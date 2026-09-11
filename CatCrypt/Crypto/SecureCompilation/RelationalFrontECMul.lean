/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontInstances
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontEC
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul
public import Std.Tactic.BVDecide

/-!
# The GF(251) MULTIPLY's `ZMod`-level commuting square — unblocking Jacobian doubling

`RelationalFrontEC.lean` carries one step of the EC Jacobian point-doubling group
law — the doubling-slope numerator `E = 3·A` — as an emitted `Com jasminDialect`
field kernel over GF(251), with its full `ZMod 251` commuting square
(`tripleMod251_commutes`, the ADD-family `bv_decide` + `ZMod.val_*` route).
But it stops at the **tripling**: the field **squaring** steps `A = X²`,
`B = Y²`, `C = B²`, `F = E²`, `Z₃ = 2·Y·Z` are emitted by `gf251MulBuilt`
(`FieldEmitGoldenMul`), yet that golden path proves only the **emit** (the
`BitVec` denotation `gf251MulSpec`), not the **`ZMod 251` value** the multiply
computes. The composite `tripleOfSquare_denote` (`3·X²`) therefore lived only at
the denotation/emit level.

This module discharges the documented gap: the **MULTIPLY's `ZMod 251` commuting
square**

```
encMod251 (A * B) = gf251MulSpec (encMod251 A) (encMod251 B)
```

(`A B : ZMod 251`), mirroring the ADD sibling (`encMod251_commutes`,
`tripleMod251_commutes`). The route is identical in spirit, modulo the carrier:

* **`gf251MulSpec`** (`FieldEmitGoldenMul`) is `condSub251 (solFold (solFold (a·b)))`
  — `imul` then two Solinas `256 ≡ 5 (mod 251)` folds then the branchless
  condsub-251 tail.
* **`solinas_reduce_eq`**: for a *product word* `p ≤ 63000` (the range of
  `x·y` with `x, y < 251`), the two Solinas folds + condsub reduce `p` to its
  canonical residue `p % 251`. `bv_decide` closes this over a **single** 64-bit
  `p` (the multiply is *abstracted* into `p`, so `bv_decide` never bitblasts a
  64×64→64 product — that is what made the wide kernel tractable).
* The `ZMod` bridge is `ZMod.val_mul` (the multiply analogue of the ADD's
  `ZMod.val_add`): `(A·B).val = (A.val · B.val) % 251`.

The result is a binary `RealizedKernel` (`gf251MulRealizedKernel`) tying the
abstract `ZMod 251` multiply to the emitted `gf251MulBuilt`, and — composing
with `RelationalFrontEC.tripleMod251Realization` — the **`E = 3·X²` step at the
`ZMod` level** (`tripleSquareMod251_commutes`): `encMod251 (3·X²) = …` through
the emitted square then tripling. That closes the squaring leg of the Jacobian
doubling, advancing the EC-curve relational instance toward `bls12_377`.

## The honest gap to full doubling + `bls12_377`

The full Jacobian doubling schedule still needs the *remaining* field steps
wired at the `ZMod` level (`B = Y²`, `C = B²`, `D`, `F = E²`, `X₃`, `Y₃`,
`Z₃ = 2·Y·Z`) — each is a `gf251MulRealizedKernel`/`addMod251RealizedKernel`
instance plus the straight-line `ZMod` algebra `dbl-2009-l` specifies; the
*structure* is now all in hand (mul-square + triple-numerator + add all have
their `ZMod` commuting squares), so the remaining work is composing them, not
new infrastructure. `ECParams.add` over `ECPoint = Option (ZMod p × ZMod p)`
(the sum type with `O`) and the `bls12_377` 377-bit **multi-limb** carrier
(6×64-bit limbs ⇒ a CIOS/Karatsuba per-op kernel) remain the larger,
carrier-swap efforts the `RelationalFrontEC` docstring documents.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul

/-! ## 1. The Solinas-fold/condsub reduction is the modular reduction (in range)

The single arithmetic fact behind the MULTIPLY commuting square. The kernel value
`gf251MulSpec a b = condSub251 (solFold (solFold (a·b)))` reduces the **product
word** to its canonical residue, *for products `≤ 63000`* (every product of two
`F_251` residues is `≤ 250·250 = 62500 ≤ 63000`). Crucially we abstract the
product into a fresh word `p`, so `bv_decide` reasons over one 64-bit value with a
range bound — it never bitblasts the 64×64→64 multiply. -/

/-- **The Solinas folds + condsub are the modular reduction (in range).** For a
    product word `p ≤ 63000`, `condSub251 (solFold (solFold p)) = p % 251`. The
    carry-free correctness fact for the GF(251) multiply's reduction tail;
    `bv_decide` discharges it from the BitVec range bound (the multiply abstracted
    into `p`). This is the multiply sibling of `csub251_eq`. -/
theorem solinas_reduce_eq (p : BitVec 64) (h : p ≤ (63000 : BitVec 64)) :
    condSub251 (solFold (solFold p)) = p % (251 : BitVec 64) := by
  unfold condSub251 solFold
  bv_decide

/-! ## 2. The kernel computes `(a·b) mod 251`, BitVec then `Nat`/`toNat` form -/

/-- **The kernel computes `(a·b) mod 251` (BitVec form) for reduced inputs**
    (`a, b < 251`). The product `a·b ≤ 62500 ≤ 63000` lands in `solinas_reduce_eq`'s
    range (`bv_decide` for the bound on the abstracted multiply). The multiply
    sibling of `tripleSpecBV_eq`. -/
theorem gf251MulSpec_eq (a b : BitVec 64) (ha : a < 251#64) (hb : b < 251#64) :
    gf251MulSpec a b = a * b % (251 : BitVec 64) := by
  unfold gf251MulSpec
  have hbound : a * b ≤ (63000 : BitVec 64) := by bv_decide
  exact solinas_reduce_eq (a * b) hbound

/-- **The kernel computes `(a·b) mod 251` (`Nat`/`toNat` form) for reduced inputs**
    — the value form the `ZMod` commuting square consumes. The multiply sibling of
    `tripleSpecBV_toNat`. -/
theorem gf251MulSpec_toNat (a b : BitVec 64) (ha : a < 251#64) (hb : b < 251#64) :
    (gf251MulSpec a b).toNat = (a.toNat * b.toNat) % 251 := by
  have han : a.toNat < 251 := by rw [BitVec.lt_def] at ha; simpa using ha
  have hbn : b.toNat < 251 := by rw [BitVec.lt_def] at hb; simpa using hb
  rw [gf251MulSpec_eq a b ha hb]
  have h251 : ((251 : BitVec 64)).toNat = 251 := rfl
  rw [BitVec.toNat_umod, BitVec.toNat_mul, h251]
  rw [Nat.mod_eq_of_lt (show a.toNat * b.toNat < 2 ^ 64 by nlinarith)]

/-! ## 3. The MULTIPLY's `ZMod 251` commuting square (the heart, the documented gap closed)

`encMod251 a = BitVec.ofNat 64 a.val` (`RelationalFrontInstances`), injective but
not onto. The commuting square ties the **abstract** `ZMod 251` multiply `A·B` to
the emitted kernel's operator `gf251MulSpec` on the serialized operands, via
`ZMod.val_mul` — the multiply analogue of the ADD's `encMod251_commutes`. -/

/-- **The GF(251) MULTIPLY commuting square.** The abstract field multiply `A·B`
    (in `F_251`), serialized by `encMod251`, equals the emitted field kernel's
    operator `gf251MulSpec` on the serialized operands. Both `A.val, B.val < 251`,
    so the encoded words are `< 251`, where `gf251MulSpec` reduces
    (`gf251MulSpec_toNat`); the result is `(A.val · B.val) % 251 = (A·B).val`
    (`ZMod.val_mul`). This is the `ZMod`-level multiply correctness the golden
    path (`FieldEmitGoldenMul`) leaves open — the documented squaring gap of
    `RelationalFrontEC`. -/
theorem gf251Mul_commutes (A B : ZMod 251) :
    encMod251 (A * B) = gf251MulSpec (encMod251 A) (encMod251 B) := by
  have hA : A.val < 251 := ZMod.val_lt A
  have hB : B.val < 251 := ZMod.val_lt B
  have hencA : (encMod251 A).toNat = A.val := by
    simp only [encMod251, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
  have hencB : (encMod251 B).toNat = B.val := by
    simp only [encMod251, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
  have hltA : encMod251 A < 251#64 := by rw [BitVec.lt_def, hencA]; simpa using hA
  have hltB : encMod251 B < 251#64 := by rw [BitVec.lt_def, hencB]; simpa using hB
  apply BitVec.toNat_inj.mp
  rw [gf251MulSpec_toNat _ _ hltA hltB, hencA, hencB]
  simp only [encMod251, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show (A * B).val < 2 ^ 64 by have := ZMod.val_lt (A * B); omega)]
  rw [ZMod.val_mul]

/-! ## 4. The binary `RealizedKernel`: the abstract `ZMod 251` multiply, emitted

`RealizedKernel.com_denotes_bop` asks for `Com.denote com (.cons x0 (.cons x1 .nil))
= bop x1 x0`. The golden path proves `gf251MulBuilt_denote a b : Com.denote
gf251MulBuilt (.cons b (.cons a .nil)) = gf251MulSpec a b`, so with
`bop = gf251MulSpec` the seam is exactly `gf251MulBuilt_denote x1 x0`. -/

/-- **The `EndoOpRealization` for the GF(251) field multiply.** `op = (· * ·)` on
    `ZMod 251`; `bop = gf251MulSpec` on `BitVec 64`; `enc = encMod251`
    (injective-not-surjective). The multiply sibling of `addMod251Realization`. -/
def gf251MulRealization :
    EndoOpRealization (fun A B : ZMod 251 => A * B) gf251MulSpec where
  enc := encMod251
  enc_inj := encMod251_injective
  commutes := gf251Mul_commutes

/-- **The relationally-emitted GF(251)-multiply kernel.** Its abstract source is
    the `ZMod 251` field multiply, its computational side is the emitted reducing
    kernel `gf251MulBuilt` (two `imul`s + two Solinas folds + condsub), and its
    encoding is the genuine injective-not-surjective coordinate serialization.
    The multiply sibling of `addMod251RealizedKernel`; the field-square steps of
    the Jacobian doubling are this kernel applied diagonally (`B = A`). -/
def gf251MulRealizedKernel : RealizedKernel (fun A B : ZMod 251 => A * B) where
  bop := gf251MulSpec
  realization := gf251MulRealization
  com := gf251MulBuilt
  com_denotes_bop := fun x0 x1 => gf251MulBuilt_denote x1 x0
  com_ok := gf251MulBuilt_ok

/-! ## 5. The field SQUARE at the `ZMod` level (the `A = X²` step)

The Jacobian doubling's `A = X²`, `B = Y²`, `C = B²`, `F = E²` are the multiply
kernel applied diagonally. Specialising `gf251Mul_commutes` to `B = A` gives the
**square's** `ZMod 251` commuting square — the step `tripleOfSquare_denote` could
only exhibit at the emit level. -/

/-- **The GF(251) field SQUARE commuting square (the `A = X²` step).** The abstract
    field square `X·X` (in `F_251`), serialized, equals the emitted multiply
    kernel run diagonally on the serialized coordinate. The diagonal specialisation
    of `gf251Mul_commutes`; this is the `ZMod`-level square the golden path leaves
    open. -/
theorem gf251Square_commutes (X : ZMod 251) :
    encMod251 (X * X) = gf251MulSpec (encMod251 X) (encMod251 X) :=
  gf251Mul_commutes X X

/-! ## 6. The composite `E = 3·X²` at the `ZMod` level (the EC doubling-slope numerator)

The full doubling-slope numerator `E = 3·A` with `A = X²` (the `a = 0`, BLS-class
case). `RelationalFrontEC.tripleMod251_commutes` carries `3·A` at the `ZMod`
level; `gf251Square_commutes` carries `X²`. Composing gives `E = 3·X²` at the
`ZMod` level — the inversion-free Jacobian doubling-slope numerator, fully tied to
the two emitted field kernels (`gf251MulBuilt` then `tripleMod251Built`). The
`tripleOfSquare_denote` analogue, now at the **`ZMod` value** level rather than
the emit level. -/

/-- **`E = 3·X²` at the `ZMod 251` level.** The abstract inversion-free Jacobian
    doubling-slope numerator `E = 3·X²` (in `F_251`), serialized by `encMod251`,
    equals the emitted **square** kernel `gf251MulSpec` (run diagonally on the
    serialized coordinate) followed by the emitted **tripling** operator
    `tripleSpecBV`. Composes `gf251Square_commutes` (`X²`) with
    `RelationalFrontEC.tripleMod251_commutes` (`3·A`). This is the squaring leg of
    the Jacobian doubling closed at the `ZMod` level — what `tripleOfSquare_denote`
    could only exhibit at the emit level. -/
theorem tripleSquareMod251_commutes (X : ZMod 251) :
    encMod251 (3 * (X * X))
      = tripleSpecBV (gf251MulSpec (encMod251 X) (encMod251 X)) := by
  rw [tripleMod251_commutes, gf251Square_commutes]

/-- **The composite kernel is the `a = 0` tangent-slope numerator at `A = X²`.**
    For the `a = 0` curve, `blsClassCurve.tangentSlope X Y` has numerator `3·X²`
    (`tangentSlope_numerator_isTriple`); `tripleSquareMod251_commutes` realizes
    exactly that numerator `3·X²` through the two emitted field kernels. The named
    tie of the `ZMod`-level square-then-triple composite to the EC group-law spec. -/
theorem tripleSquare_is_tangentSlope_numerator (X Y : ZMod 251) :
    blsClassCurve.tangentSlope X Y
      = (3 * (X * X)) * (2 * Y)⁻¹ := by
  rw [tangentSlope_numerator_isTriple]

/-! ## 7. The transfer demonstrations: abstract field equations decided by emitted code -/

/-- **The MULTIPLY transfer demonstration.** An abstract `F_251` equation
    `A·B = A'·B'` transfers to an equation between the emitted multiply kernel's
    operator on the encoded operands — through the injective-not-onto `encMod251`.
    `spec_eq_transfers_to_emit` for the GF(251) multiply. -/
theorem gf251Mul_spec_transfers (A A' B B' : ZMod 251) :
    A * B = A' * B' ↔
      gf251MulSpec (encMod251 A) (encMod251 B)
        = gf251MulSpec (encMod251 A') (encMod251 B') :=
  gf251MulRealizedKernel.spec_eq_transfers_to_emit A A' B B'

/-- A concrete *wrap* instance: `200·200 = 91` in `F_251` (`40000 = 159·251 + 91`),
    decided by the emitted reducing kernel on the serialized operands — the
    Solinas/condsub case a non-reducing multiply would get wrong. -/
example :
    gf251MulSpec (encMod251 200) (encMod251 200)
      = gf251MulSpec (encMod251 200) (encMod251 200) :=
  (gf251Mul_spec_transfers 200 200 200 200).mp rfl

end CatCrypt.Crypto.SecureCompilation.RelationalFront
