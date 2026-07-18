/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-!
# Asymmetric operation homomorphism (`OpHomOn`) and the scalar-multiply application

`ReprTransfer.BinOpHomOn` and `ReprTransferBinaryDom.BinOpHomOn2` both carry a
**single** decode map `φ : α → A` shared by both operands and the result, and a
**homogeneous** target `tgt : α → α → α` (both operands the *same* carrier). That
is the right shape for a lane combine or a same-width add/multiply. But the
register-level multi-limb kernels include genuinely **heterogeneous** binary ops
whose two operands live in *different* carriers and whose result carrier is a
third type:

* the **scalar multiply** `mulScalar a bs 0 : a · bignumVal bs` — left operand a
  single word `a : BitVec 64` (decoded by `BitVec.toNat`), right operand a
  limb-list `bs : List (BitVec 64)` (decoded by `bignumVal`), result a limb-list
  (also decoded by `bignumVal`);
* the **2-limb × 1-word** multiply `field_mul_2x1` — left a limb-pair, right one
  word, result three limbs.

`BinOpHomOn2`'s single `φ` and `tgt : α → α → α` cannot type these: the left
decode, the right decode, and the result decode are three *different* maps with
three *different* source/target types. The multi-limb-transport agent's note
flagged exactly this — `FieldMul2x1` is heterogeneous (`left = limb-pair`,
`right = one word`, output decoded `r0 + r1·2^64 + r2·2^128`).

This file adds, **additively** (it touches neither `ReprTransfer.lean` nor
`ReprTransferBinaryDom.lean`):

* `OpHomOn phiL phiR dom2 tgt phiRes src` — the **asymmetric** homomorphism, with
  *separate* operand decodes `phiL : a1 → b`, `phiR : a2 → b`, a possibly-distinct
  result decode `phiRes : RESULT → b`, a heterogeneous target
  `tgt : a1 → a2 → RESULT`, and the abstract op `src : b → b → b`. Its square is
  `phiRes (tgt x y) = src (phiL x) (phiR y)`, gated by a binary `dom2 : a1 → a2 →
  Prop`.
* `BinOpHomOn2.toOpHomOn` — the **subsumption bridge**: every joint-domain
  `BinOpHomOn2 φ dom2 tgt src` is the special case `phiL = phiR = phiRes = φ`,
  `a1 = a2 = RESULT`, `tgt = tgt`. So `OpHomOn` strictly generalises both
  `BinOpHomOn2` (hence, by the existing subsumption, `BinOpHomOn`).
* `opHomOn_strictly_more_general` — a witness that `OpHomOn`'s three decode maps
  and three carriers genuinely differ (a two-type asymmetric example no
  `BinOpHomOn2` can express).

The **application** is the scalar multiply `mulScalar`: with carry-in `0`, its
existing value-correctness lemma `mulScalar_val` is *exactly* the `OpHomOn`
square — `bignumVal (mulScalar a bs 0) = a.toNat * bignumVal bs` — on the full
domain, with no joint bound needed.

## Scope

`OpHomOn` is map-level on each operand: the three decodes (`BitVec.toNat`,
`bignumVal`, `bignumVal`) are the Trocq map₁ transport witnesses — no injectivity
on any domain, **no univalence**, and no `jasminc_preserves_ct`. The realization
is read off `.realizes`. The scalar-multiply `app_eq` reuses
`MultiLimbKernel.mulScalar_val` (the inner-loop recombination, already proved);
no schoolbook arithmetic is re-derived here. The `field_mul_2x1` reconstruction
is `Com.denote`-phrased; see the closing note for the precise (small) bridge it
would require, which is why the worked application here is `mulScalar`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ReprTransferAsym

open CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

universe u

/-! ## §1  The asymmetric homomorphism `OpHomOn` -/

/-- An **asymmetric (heterogeneous-operand) binary-operation homomorphism**. The
    two operands live in possibly-different carriers `a1`, `a2` and decode to the
    common abstract carrier `b` by *separate* maps `phiL`, `phiR`; the result
    lives in a third carrier `RESULT` and decodes by its own `phiRes`. The
    concrete heterogeneous `tgt : a1 → a2 → RESULT` pushes through these decodes
    to the abstract `src : b → b → b`, gated by a binary domain `dom2`:

    `phiRes (tgt x y) = src (phiL x) (phiR y)`  whenever  `dom2 x y`.

    This is the shape the register-level multi-limb kernels need — scalar×bignum
    and limb-pair×word multiply — where the operand and result carriers genuinely
    differ and `BinOpHomOn2`'s single `φ : α → A` with `tgt : α → α → α` cannot
    type the square. Map-level: each decode is a plain map (the Trocq map₁
    witness), no injectivity. -/
structure OpHomOn {a1 a2 RESULT b : Type u}
    (phiL : a1 → b) (phiR : a2 → b) (dom2 : a1 → a2 → Prop)
    (tgt : a1 → a2 → RESULT) (phiRes : RESULT → b) (src : b → b → b) where
  /-- The asymmetric homomorphism square, on the joint sub-domain `dom2`. -/
  app_eq : ∀ x y, dom2 x y → phiRes (tgt x y) = src (phiL x) (phiR y)

namespace OpHomOn
variable {a1 a2 RESULT b : Type u}
  {phiL : a1 → b} {phiR : a2 → b} {dom2 : a1 → a2 → Prop}
  {tgt : a1 → a2 → RESULT} {phiRes : RESULT → b} {src : b → b → b}

/-- The realization equation: on jointly-canonical heterogeneous inputs, decoding
    the concrete result equals the abstract operation on the decoded operands. The
    per-point realization is read off this — the asymmetric `transferKernel`
    analogue. -/
theorem realizes (H : OpHomOn phiL phiR dom2 tgt phiRes src)
    {x : a1} {y : a2} (hxy : dom2 x y) :
    phiRes (tgt x y) = src (phiL x) (phiR y) := H.app_eq x y hxy

end OpHomOn

/-! ## §2  Subsumption: `BinOpHomOn2` ⊆ `OpHomOn`, and strict generality -/

/-- **Subsumption bridge.** Every joint-domain, single-decode `BinOpHomOn2 φ dom2
    tgt src` is the special case of `OpHomOn` with all three decodes equal to `φ`
    (`phiL = phiR = phiRes = φ`), both operand carriers and the result carrier
    equal to `α`, and `b = A`. So `OpHomOn` subsumes `BinOpHomOn2` — and hence,
    via the existing `BinOpHomOn.toBinOpHomOn2`, also the per-operand
    `BinOpHomOn`. Nothing proved with the symmetric forms is broken. -/
def BinOpHomOn2.toOpHomOn {α A : Type u} {φ : α → A} {dom2 : α → α → Prop}
    {tgt : α → α → α} {src : A → A → A}
    (H : BinOpHomOn2 φ dom2 tgt src) :
    OpHomOn (a1 := α) (a2 := α) (RESULT := α) (b := A) φ φ dom2 tgt φ src where
  app_eq x y hxy := H.app_eq x y hxy

/-- The subsumption bridge preserves the realization equation: the realization
    read off the lifted `OpHomOn` is the same equation as the original
    `BinOpHomOn2`'s `.realizes`. -/
theorem toOpHomOn_realizes {α A : Type u} {φ : α → A} {dom2 : α → α → Prop}
    {tgt : α → α → α} {src : A → A → A}
    (H : BinOpHomOn2 φ dom2 tgt src) {x y : α} (hxy : dom2 x y) :
    (BinOpHomOn2.toOpHomOn H).realizes hxy = H.realizes hxy := rfl

/-- **Strict generality.** `OpHomOn`'s three carriers and three decode maps may
    genuinely differ, so it expresses squares no single-`φ` `BinOpHomOn2` can
    type. Witness: an honest two-type asymmetric homomorphism — left operand a
    `Bool` decoded to `ℕ` by `cond · 1 0`, right operand a `ℕ` decoded by `id`,
    result a `ℕ` decoded by `id`, target `fun p n => (cond p 1 0) * n`, abstract
    op multiplication. Here `phiL ≠ phiR` (different *types*, `Bool → ℕ` vs
    `ℕ → ℕ`), which no `BinOpHomOn2` (whose operand decodes coincide) can be. -/
theorem opHomOn_strictly_more_general :
    OpHomOn (a1 := Bool) (a2 := Nat) (RESULT := Nat) (b := Nat)
      (fun p => cond p 1 0) id (fun _ _ => True)
      (fun p n => (cond p 1 0) * n) id (· * ·) :=
  ⟨fun _ _ _ => rfl⟩

/-! ## §3  Application: the scalar × bignum multiply `mulScalar` -/

/-- The **scalar × bignum machine multiply** with carry-in `0`: the heterogeneous
    target `tgt a bs = mulScalar a bs 0`, left operand a single word
    `a : BitVec 64`, right operand the limb-list `bs : List (BitVec 64)`. This is
    the inner loop schoolbook (and Karatsuba) multiplication is built from. -/
def scalarMulOp (a : BitVec 64) (bs : List (BitVec 64)) : List (BitVec 64) :=
  mulScalar a bs 0

/-- The **abstract product** of the decoded operands: the value-level product over
    `ℕ`. (`phiL = BitVec.toNat` carries the word to its value; `phiR = bignumVal`
    carries the limb-list to its value; the abstract op is multiplication.) -/
def scalarMulAbs (av bv : Nat) : Nat := av * bv

/-- The asymmetric homomorphism square for the scalar multiply: decoding the
    machine result `mulScalar a bs 0` by `bignumVal` equals the product of the
    decoded word `a.toNat` and the decoded list `bignumVal bs`. **Cites the
    existing value-correctness lemma** `mulScalar_val` (the inner-loop
    recombination, already proved); with carry-in `0` the residual `c.toNat`
    vanishes. No schoolbook arithmetic is re-derived. The domain is *full*
    (`fun _ _ => True`): the schoolbook list grows to fit, so the product is exact
    unconditionally — no joint no-overflow bound is needed (the truncated,
    fixed-width variant with its genuine joint bound is the separate
    `TransferMultiLimbTransport`). -/
theorem decode_scalarMul (a : BitVec 64) (bs : List (BitVec 64)) :
    bignumVal (scalarMulOp a bs) = scalarMulAbs a.toNat (bignumVal bs) := by
  simp only [scalarMulOp, scalarMulAbs]
  rw [mulScalar_val a bs 0]
  simp

/-- **The asymmetric transport, packaged as an `OpHomOn`.** The scalar multiply
    `scalarMulOp` is an `OpHomOn` along the *separate* operand decodes
    `phiL = BitVec.toNat` (the word) and `phiR = bignumVal` (the limb-list), with
    result decode `phiRes = bignumVal` and abstract op `scalarMulAbs = (·*·)`, on
    the full domain. The commuting-square obligation is `decode_scalarMul`. This is
    a square `BinOpHomOn2` cannot type: the left and right decodes have different
    *source types* (`BitVec 64` vs `List (BitVec 64)`). -/
def scalarMulHom :
    OpHomOn (a1 := BitVec 64) (a2 := List (BitVec 64)) (RESULT := List (BitVec 64))
      (b := Nat) BitVec.toNat bignumVal (fun _ _ => True) scalarMulOp bignumVal scalarMulAbs where
  app_eq a bs _ := decode_scalarMul a bs

/-- **The realization, GENERATED by the asymmetric transport.** The per-point
    realization equation for the scalar × bignum multiply comes out of
    `OpHomOn.realizes` applied to the `(BitVec.toNat, bignumVal, bignumVal)`
    witness — NOT a fresh `simp`. -/
theorem scalarMul_realizes_via_transport (a : BitVec 64) (bs : List (BitVec 64)) :
    bignumVal (scalarMulOp a bs) = scalarMulAbs a.toNat (bignumVal bs) :=
  scalarMulHom.realizes (x := a) (y := bs) trivial

/-- **The engine-generated realization is `rfl`-equal to the hand proof.** Reading
    the realization off `scalarMulHom.realizes` is definitionally the same equation
    as calling `decode_scalarMul` directly: the `OpHomOn` transport adds the
    asymmetric *packaging*, not new mathematical content. (Same relation as the
    multi-limb / butterfly / Barrett pilots.) -/
theorem scalarMul_realizes_eq_handproof (a : BitVec 64) (bs : List (BitVec 64)) :
    scalarMul_realizes_via_transport a bs = decode_scalarMul a bs := rfl

/-! ## §4  Note: the `field_mul_2x1` site and the bridge it needs

The 2-limb × 1-word multiply `FieldMul2x1GoldenPath.field_mul_2x1` is the second
heterogeneous site (left a limb-pair `(BitVec 64 × BitVec 64)`, right one word,
result three limbs `r0 + r1·2^64 + r2·2^128`). It fits `OpHomOn` *type-wise*:

```
a1 := BitVec 64 × BitVec 64,  a2 := BitVec 64,  RESULT := BitVec 64 × BitVec 64 × BitVec 64,
b := Nat,  phiL ⟨a0,a1⟩ := a0.toNat + a1.toNat·2^64,  phiR b := b.toNat,
phiRes ⟨r0,r1,r2⟩ := r0.toNat + r1.toNat·2^64 + r2.toNat·2^128,  src := (·*·).
```

The obstruction is purely *plumbing*: `field_mul_2x1` is stated as a single
`theorem` whose body threads the three limbs through `let`-bound `Com.denote`
calls and proves the value equation **inline** — it does not expose a named
`tgt : (BitVec 64 × BitVec 64) → BitVec 64 → (BitVec 64 × BitVec 64 × BitVec 64)`
result, nor a `phiRes (tgt x y) = src (phiL x) (phiR y)` lemma. To feed it to
`OpHomOn.app_eq` one would: (1) factor the three emitted `Com.denote` words
(`r0, r1, r2`) into a named tuple-valued `field_mul_2x1_tgt`; (2) restate the
existing inline equation as `phiRes (field_mul_2x1_tgt ⟨a0,a1⟩ b) = …` (a `rfl`
re-association of the current `let`-form goal); then `app_eq := that lemma`. That
refactor lives in `FieldMul2x1GoldenPath.lean`, which this base file does not
import or modify. The `mulScalar` application above is the clean,
already-named-lemma site and is the genuine deliverable; `field_mul_2x1` is a
mechanical tuple-extraction away.
-/

end CatCrypt.Crypto.SecureCompilation.ReprTransferAsym
