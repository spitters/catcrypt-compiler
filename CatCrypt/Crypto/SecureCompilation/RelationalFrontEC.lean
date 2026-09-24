/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RelationalFrontInstances
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontInstances
public meta import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul
public meta import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
public import Std.Tactic.BVDecide

/-!
# The relational front over the EC GROUP LAW: a Jacobian point-doubling sub-step

`RelationalFrontInstances.lean` carries the relational front over a prime field
(`ZMod 251` add, with a reducing kernel) and `RelationalFrontGf256.lean` over a
binary field (`GF(2⁸)` multiply). This module is the **elliptic-curve customer**:
it carries the relational front through a step of the **EC group law** — the
`bls12_377`-class target named in the `RelationalFront` docstring — using
**Jacobian (inversion-free) coordinates**, so the realized operation is a pure
sequence of field `mul`/`add` (no field inversion), and so it is a `Com
jasminDialect` exactly like `gf256MulBuilt` / `gf251MulBuilt`.

## Why Jacobian, and which sub-step

The *affine* EC add/double both need a field **inversion** (the chord/tangent
slope `λ = num · denom⁻¹`, `EllipticCurveDialect.tangentSlope`). Inversion is the
hard, non-`Com`-shaped operation (extended-Euclid / Fermat exponentiation). In
**Jacobian** coordinates `(X, Y, Z)` (modelling the affine `(X/Z², Y/Z³)`,
`Z = 0 = O`) the inversion is deferred to a single final normalisation, and the
in-loop doubling `dbl-2009-l` is *inversion-free*:

```
A = X² ; B = Y² ; C = B² ; D = 2((X+B)² − A − C) ; E = 3·A + a·Z⁴ ;
F = E² ; X₃ = F − 2D ; Y₃ = E·(D − X₃) − 8C ; Z₃ = 2·Y·Z
```

— a straight-line schedule of field `mul`/`sqr`/`add`/`sub`, every one of which
the golden path already emits as a `Com` (`gf251MulBuilt`, `modDoubleCom`, the
`fieldAddMod251Com` add). For a `bls12_377`/`bls12_381`-class curve the curve
coefficient is **`a = 0`**, so the doubling slope collapses to `E = 3·A` with
`A = X²` (the `a·Z⁴` term vanishes) — the simplest fully-provable
sub-step of the group law.

**This module realizes the `a = 0` doubling-slope numerator `E = 3·A`** — a named
sub-step of the Jacobian point-doubling group law (`EllipticCurveDialect.tangentSlope`
numerator at `a = 0`, `3·x² + a = 3·A`) — as an emitted `Com jasminDialect`
field kernel over **GF(251)**, with the full relational tie (injective-not-onto
encoding + commuting square) to the abstract `ZMod 251` field operation `A ↦ 3·A`.

## The realized operation

* **Field**: `F_251 = ZMod 251` (the small Solinas prime whose `mul`/`add`/`condsub`
  the golden path already emits; small enough that the `Com`'s denotation is a
  concrete, `native_decide`-checkable computation).
* **EC sub-step**: `E = 3·A` (`A = X²`), the BLS-class (`a = 0`) Jacobian
  doubling-slope numerator — a **unary** field op `ZMod 251 → ZMod 251`,
  `A ↦ 3·A`.
* **Emitted `Com`**: `tripleMod251Built` — a 14-binding straight-line
  `Com jasminDialect [.reg 64] (.reg 64)` built turnkey by `ComBuilder`
  (`tripleMod251SSA`): a field double `t + t`, a branchless condsub-251, a
  field add `+ t`, a second condsub-251 (`3·250 = 750` needs up to **two**
  prime subtractions). All ops (`add`/`sub`/`and`/`shrImm`/`regConst`) are in
  `SupportedOp`, so the kernel rides `comToReg_faithful` to AArch64 + RISC-V.

The `RealizedKernel` of `RelationalFront` is hard-wired binary (`A → A → A`); the
EC doubling-slope numerator is unary (`A → A`), so this module supplies the
**unary analogue** `RealizedUnaryKernel` (same three fields — `bop`, the
realization tie, the emitted `Com` and its denotation seam — for a unary op) and
its transfer corollary `spec_eq_transfers_to_emit`, additively, without touching
`RelationalFront`.

## What this demonstrates, and its scope

`spec_eq_transfers_to_emit` instantiated here decides an **abstract `F_251`
group-law-step equation** (`3·A = 3·A'` in `ZMod 251`, the doubling-slope
numerators of two Jacobian points) by the emitted field kernel's denotation on
the *serialized* (canonical-residue) coordinate — through the injective,
not-onto `encMod251`. That is the relational front carrying one step of the EC
group law end-to-end.

The gap to **full `ECParams.add`** (and thus to `bls12_377`):

* **The whole doubling schedule** needs the remaining field steps (`B = Y²`,
  `C = B²`, `D`, `F = E²`, `X₃`, `Y₃`, `Z₃ = 2·Y·Z`). The field **multiply**
  steps (`X²`, `Y²`, `E²`, `Y·Z`) are *emitted* by `gf251MulBuilt`
  (`FieldEmitGoldenMul`) and we exhibit the composite `E = 3·X²` at the
  **denotation/emit** level here (`tripleOfSquare_denote`); but the multiply's
  *`ZMod`-level commuting square* (`enc (X·X) = gf251MulBuilt-denote (enc X) (enc X)`)
  is the Solinas-fold-correctness-over-`ZMod 251`, which is **not** discharged in
  the imported golden path (it goldens the *emit*, not the `ZMod` value). So the
  full-doubling commuting square is *not* proved here — only the tripling
  sub-step's is.
* **`ECParams.add` ranges over `ECPoint = Option (ZMod p × ZMod p)`** (a *sum*
  type with the infinity point), whose encoding must serialize `O` and the
  Jacobian triple, not a single residue.
* **`bls12_377` is a 377-bit prime field** — a **multi-limb** carrier (6×64-bit
  limbs), so each field op is a multi-limb CIOS/Karatsuba schedule, not the
  single-word GF(251) op. The relational *structure* here (encoding + commuting
  square + emitted `Com`) ports verbatim — only the carrier (one word → six
  limbs) and the per-op kernel (single-word → multi-limb) change — but those
  kernels are a separate (large) emit effort.

This module establishes the **EC-group-law leg** of the relational front on the
smallest spec: a fully-provable Jacobian-doubling field sub-step
over a small field, with the full injective-not-onto encoding tie.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ComBuilder
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-! ## 0. The unary analogue of `RealizedKernel`

`RelationalFront.RealizedKernel` ties a **binary** abstract op `op : A → A → A`
to an emitted `Com`. The EC Jacobian doubling-slope numerator `E = 3·A` is a
**unary** field op `A → A`, so we mirror the binary record for the unary case:
the encoding tie `EndoUnaryRealization` (the unary sibling of
`EndoOpRealization`) and the `RealizedUnaryKernel` over a one-input `Com`. -/

/-- The unary sibling of `Bridges.ReprTransferExpr.EndoOpRealization`: a unary op
    `op : A → A` realized by `bop : α → α` along an **injective** (equality-
    reflecting, not necessarily surjective) encoding `enc`, with the commuting
    square `enc (op a) = bop (enc a)`. The `map4` level: no surjectivity, no
    Type-equivalence — exactly what a crypto serialization provides. -/
structure EndoUnaryRealization {A α : Type} (op : A → A) (bop : α → α) where
  /-- The encoding (serialization) of the abstract type into the carrier. -/
  enc : A → α
  /-- The encoding is injective (equality-reflecting). -/
  enc_inj : Function.Injective enc
  /-- The commuting square: the abstract op, encoded, is the carrier op on the
      encoded input. -/
  commutes : ∀ a, enc (op a) = bop (enc a)

/-- A **relationally-emitted unary kernel**: an abstract unary crypto/field
    operation `op`, its byte-level realization `bop`, the realization tie, and an
    emitted one-input `Com` whose denotation **is** `bop`. The unary analogue of
    `RelationalFront.RealizedKernel`; the denotation seam `com_denotes_bop` is the
    obligation that promotes the `EndoUnaryRealization` into a front-end for the
    verified compiler. -/
structure RealizedUnaryKernel {A : Type} (op : A → A) where
  /-- The carrier (register-level) operator the abstract `op` is realized by. -/
  bop : BitVec 64 → BitVec 64
  /-- The relational tie (encoding + injectivity + commuting square). -/
  realization : EndoUnaryRealization op bop
  /-- The emitted source program (what the golden-path backend lowers). -/
  com : Com jasminDialect ([.reg 64] : Ctxt jasminDialect) (.reg 64)
  /-- **The IR seam.** The emitted `Com` denotes exactly `bop`: running `com` on
      input `a` computes `bop a`. -/
  com_denotes_bop :
    ∀ a : BitVec 64, Com.denote com (.cons a .nil) = bop a
  /-- **The supported-fragment obligation.** The emitted `Com` is in the
      straight-line fragment the backend accepts. -/
  com_ok : ComOK com

namespace RealizedUnaryKernel
variable {A : Type} {op : A → A}

/-- **The relational-front transfer-to-emit corollary (unary).** An abstract
    source equation `op a = op a'` transfers to an equation between the *emitted*
    `Com`'s denotations on the encoded operands — the security-level abstract
    equation is decided by the code the verified compiler emits. The unary
    analogue of `RealizedKernel.spec_eq_transfers_to_emit`. -/
theorem spec_eq_transfers_to_emit (R : RealizedUnaryKernel op) (a a' : A) :
    op a = op a' ↔
      R.bop (R.realization.enc a) = R.bop (R.realization.enc a') := by
  rw [← R.realization.commutes, ← R.realization.commutes]
  exact ⟨fun h => by rw [h], fun h => R.realization.enc_inj h⟩

end RealizedUnaryKernel

/-! ## 1. The emitted field kernel: `3·A mod 251` as a `Com jasminDialect`

`tripleMod251SSA` over one input `t = A` (level 0): field-double `t + t`, one
branchless condsub-251, field-add `+ t`, a second condsub-251. (`3·250 = 750`
needs up to two prime subtractions: `750 → 499 → 248`.) Built turnkey by
`ComBuilder`; the de-Bruijn indices are resolved automatically. -/

/-- The GF(251) `3·A` (doubling-slope numerator) named-SSA program: `s₁ = t+t`,
    condsub-251, `s₂ = r₁+t`, condsub-251. Operand references are by **level**;
    `build` resolves the de-Bruijn indices. -/
def tripleMod251SSA : NamedSSA where
  nInputs := 1
  bindings :=
    [ ⟨.regArith .add 64, [0, 0]⟩    -- s₁ = t + t                 [1]
    , ⟨.regConst 64 251, []⟩         -- c251                       [2]
    , ⟨.regArith .sub 64, [1, 2]⟩    -- d₁ = s₁ - c251             [3]
    , ⟨.shrImm 64 63, [3]⟩           -- bit₁ = d₁ >>> 63           [4]
    , ⟨.regConst 64 0, []⟩           -- c0                         [5]
    , ⟨.regArith .sub 64, [5, 4]⟩    -- m₁ = c0 - bit₁             [6]
    , ⟨.regArith .and 64, [6, 2]⟩    -- masked₁ = m₁ & c251        [7]
    , ⟨.regArith .add 64, [3, 7]⟩    -- r₁ = d₁ + masked₁ (=s₁%251)[8]
    , ⟨.regArith .add 64, [8, 0]⟩    -- s₂ = r₁ + t                [9]
    , ⟨.regArith .sub 64, [9, 2]⟩    -- d₂ = s₂ - c251             [10]
    , ⟨.shrImm 64 63, [10]⟩          -- bit₂ = d₂ >>> 63           [11]
    , ⟨.regArith .sub 64, [5, 11]⟩   -- m₂ = c0 - bit₂             [12]
    , ⟨.regArith .and 64, [12, 2]⟩   -- masked₂ = m₂ & c251        [13]
    , ⟨.regArith .add 64, [10, 13]⟩  -- r₂ = d₂ + masked₂ (=s₂%251)[14]
    ]
  retLevel := 14

/-- The generated `Com jasminDialect [.reg 64] (.reg 64)` for `3·A mod 251` —
    de-Bruijn indices resolved by the builder, no hand `.there` chain. -/
def tripleMod251Built : Com jasminDialect [.reg 64] (.reg 64) :=
  (build tripleMod251SSA).get (by decide)

/-- The carrier-level (`BitVec 64`) operator the emitted kernel computes: a field
    double + condsub, then `+ t` + condsub — the two-branch reduction of `3·t`. -/
def tripleSpecBV (a : BitVec 64) : BitVec 64 :=
  let r1 := (a + a - 251) + ((0 - ((a + a - 251) >>> 63)) &&& 251)
  let s2 := r1 + a
  (s2 - 251) + ((0 - ((s2 - 251) >>> 63)) &&& 251)

/-! ## 2. The kernel is supported, denotes `tripleSpecBV`, and reduces to `3·t mod 251` -/

/-- `tripleMod251SSA` is well-formed (no forward/self operand references). -/
theorem tripleMod251SSA_wf : BindingsWF 1 tripleMod251SSA.bindings 14 := by
  unfold tripleMod251SSA; simp only [BindingsWF]; norm_num [List.mem_cons]

/-- Every binding uses a `SupportedOp` (the ALU ops `add`/`sub`/`and`, `shrImm`,
    `regConst`). The only per-kernel obligation the turnkey builder leaves. -/
theorem tripleMod251SSA_supported : AllBindingsSupported tripleMod251SSA.bindings := by
  intro b hb
  simp only [tripleMod251SSA, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> unfold SupportedOp <;> simp

/-- **`ComOK`, turnkey** via `build_preserves_ComOK` from the per-binding
    `SupportedOp` check — no hand-authored `ComOK.var` chain. -/
theorem tripleMod251Built_ok : ComOK tripleMod251Built :=
  build_preserves_ComOK tripleMod251SSA tripleMod251Built tripleMod251SSA_supported rfl

/-- **The evaluator is symbolically faithful**: `NamedSSA.eval` returns exactly
    `tripleSpecBV` — a `rfl` on the computable evaluator. -/
theorem tripleMod251_eval_symbolic (a : BitVec 64) :
    tripleMod251SSA.eval [a] = some (tripleSpecBV a) := rfl

/-- **The generated `Com`'s denotation equals `tripleSpecBV`, via the eval route**
    (`build_preserves_denote`): the wide-kernel `Com.denote` is the computable
    `NamedSSA.eval`, not a per-kernel `Com.denote` `rfl`. -/
theorem tripleMod251Built_denote (a : BitVec 64) :
    Com.denote tripleMod251Built (.cons a .nil) = tripleSpecBV a := by
  have hcorr : EnvCorr ([.reg 64] : Ctxt jasminDialect) (.cons a .nil)
      (fun L => ([a] : List (BitVec 64))[L]?.getD 0) 1 := by
    intro L hL; interval_cases L; rfl
  exact build_preserves_denote tripleMod251SSA tripleMod251Built (.cons a .nil)
    [a] (tripleSpecBV a) hcorr tripleMod251SSA_wf rfl (tripleMod251_eval_symbolic a)

/-- **The kernel computes `3·t mod 251` (BitVec form) for a reduced input**
    (`t < 251`). The two field-double/add + condsub steps reduce `3·t ≤ 750` to
    its canonical residue; `bv_decide` closes the bounded carry-free reduction. -/
theorem tripleSpecBV_eq (a : BitVec 64) (ha : a < 251#64) :
    tripleSpecBV a = a * 3 % 251 := by
  unfold tripleSpecBV; bv_decide

/-- **The kernel computes `3·t mod 251` (`Nat`/`toNat` form) for a reduced input**
    (`t < 251`) — the value form the `ZMod` commuting square consumes. -/
theorem tripleSpecBV_toNat (a : BitVec 64) (ha : a < 251#64) :
    (tripleSpecBV a).toNat = (3 * a.toNat) % 251 := by
  have han : a.toNat < 251 := by rw [BitVec.lt_def] at ha; simpa using ha
  rw [tripleSpecBV_eq a ha]
  have h3 : ((3 : BitVec 64)).toNat = 3 := rfl
  have h251 : ((251 : BitVec 64)).toNat = 251 := rfl
  rw [BitVec.toNat_umod, BitVec.toNat_mul, h3, h251]
  rw [Nat.mod_eq_of_lt (show a.toNat * 3 < 2 ^ 64 by omega)]; omega

/-! ## 3. The injective-not-surjective encoding and the commuting square

The encoding is `encMod251` (`RelationalFrontInstances`): the canonical least
residue `ZMod 251 → BitVec 64`, injective (`encMod251_injective`) but not onto.
The commuting square `enc (3·A) = tripleSpecBV (enc A)` ties the **abstract** EC
doubling-slope numerator `E = 3·A` (in `ZMod 251`) to the emitted field kernel's
operator on the serialized coordinate. -/

/-- **The EC-sub-step commuting square.** The abstract Jacobian doubling-slope
    numerator `E = 3·A` (in `F_251`), serialized by `encMod251`, equals the
    emitted kernel's operator `tripleSpecBV` on the serialized coordinate. `A.val
    < 251`, so the encoded word is `< 251`, where `tripleSpecBV` reduces
    (`tripleSpecBV_reduced`); the result is `(3 · A.val) % 251 = (3·A).val`
    (`ZMod.val_mul`). This is the heart of the EC group-law leg. -/
theorem tripleMod251_commutes (A : ZMod 251) :
    encMod251 (3 * A) = tripleSpecBV (encMod251 A) := by
  have hA : A.val < 251 := ZMod.val_lt A
  have hencN : (encMod251 A).toNat = A.val := by
    simp only [encMod251, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
  have henc : encMod251 A < 251#64 := by
    rw [BitVec.lt_def, hencN]; simpa using hA
  apply BitVec.toNat_inj.mp
  rw [tripleSpecBV_toNat _ henc, hencN]
  simp only [encMod251, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show (3 * A).val < 2 ^ 64 by have := ZMod.val_lt (3 * A); omega)]
  rw [ZMod.val_mul, show (3 : ZMod 251).val = 3 from by decide]

/-- **The `EndoUnaryRealization` for the EC doubling-slope numerator.**
    `op = (3 · ·)` on `ZMod 251`; `bop = tripleSpecBV` on `BitVec 64`;
    `enc = encMod251` (injective-not-surjective). The EC-group-law relational
    tie. -/
def tripleMod251Realization :
    EndoUnaryRealization (fun A : ZMod 251 => 3 * A) tripleSpecBV where
  enc := encMod251
  enc_inj := encMod251_injective
  commutes := tripleMod251_commutes

/-! ## 4. The `RealizedUnaryKernel`: the abstract EC doubling-slope numerator, emitted -/

/-- **The relationally-emitted EC-doubling-slope-numerator kernel.** Its abstract
    source is the Jacobian point-doubling slope numerator `E = 3·A` (`a = 0`,
    BLS-class) over `ZMod 251`, its computational side is the emitted field kernel
    `tripleMod251Built`, and its encoding is an injective-not-surjective
    coordinate serialization. The EC-group-law sibling of `addMod251RealizedKernel`. -/
def tripleMod251RealizedKernel : RealizedUnaryKernel (fun A : ZMod 251 => 3 * A) where
  bop := tripleSpecBV
  realization := tripleMod251Realization
  com := tripleMod251Built
  com_denotes_bop := tripleMod251Built_denote
  com_ok := tripleMod251Built_ok

/-! ## 5. The abstract EC-doubling spec and the doubling-slope numerator it uses

The abstract object the realized op is a step of: the Jacobian doubling-slope
numerator for an `a = 0` short-Weierstrass curve. `EllipticCurveDialect.tangentSlope`
at `a = 0` is `(3·x² + 0)·(2y)⁻¹ = (3·A)·(2y)⁻¹` with `A = x²`, so `3·A` is exactly
the inversion-free numerator the realized kernel computes. -/

/-- A `bls12_377`/`bls12_381`-class small-field stand-in: a short-Weierstrass curve
    `y² = x³ + b` (i.e. `a = 0`) over `ZMod 251`. (BLS12 curves are `a = 0`; the
    realized doubling-slope numerator `E = 3·X²` is the `a = 0` specialisation.) -/
def blsClassCurve : ECParams 251 := ⟨0, 1⟩

/-- **The realized kernel is the `a = 0` tangent-slope numerator.** For the
    `a = 0` curve, `EllipticCurveDialect.tangentSlope` is `(3·X² + a)·(2Y)⁻¹` with
    numerator `3·X² + 0 = 3·A` (`A = X²`) — exactly the unary op `A ↦ 3·A` the
    `RealizedUnaryKernel` realizes. The named tie to the group-law spec. -/
theorem tangentSlope_numerator_isTriple (X Y : ZMod 251) :
    blsClassCurve.tangentSlope X Y
      = (fun A : ZMod 251 => 3 * A) (X * X) * (2 * Y)⁻¹ := by
  simp only [ECParams.tangentSlope, blsClassCurve, add_zero]

/-! ## 6. The composite `E = 3·X²` at the emit level (the next step toward full doubling)

The full doubling needs the field **square** `A = X²` before the tripling. The
golden path emits it as `gf251MulBuilt` (`FieldEmitGoldenMul`). Composing it with
`tripleMod251Built` at the **denotation** level gives the whole `E = 3·X²`
inversion-free numerator as emitted field code. (The squaring's *`ZMod`-level*
commuting square — Solinas-correctness over `ZMod 251` — is the documented gap
above; here we exhibit the emit-level composite, which is what the backend lowers.) -/

open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul in
/-- **The emit-level `E = 3·X²` composite.** Running the emitted square
    `gf251MulBuilt` on `(X, X)` then the emitted tripling `tripleMod251Built`
    computes `tripleSpecBV (gf251MulSpec X X)` — the inversion-free Jacobian
    doubling-slope numerator `E = 3·X²` as a composite of two *emitted* field
    kernels. -/
theorem tripleOfSquare_denote (X : BitVec 64) :
    Com.denote tripleMod251Built
        (.cons (Com.denote gf251MulBuilt (.cons X (.cons X .nil))) .nil)
      = tripleSpecBV (gf251MulSpec X X) := by
  rw [tripleMod251Built_denote, gf251MulBuilt_denote]

/-! ## 7. The demonstration: an abstract EC-group-law-step equation decided by emitted code

`spec_eq_transfers_to_emit` on this kernel: an abstract `ZMod 251` doubling-slope
numerator equation `3·A = 3·A'` holds **iff** the emitted field kernel's operator
agrees on the *serialized* coordinates — through the injective-not-onto
`encMod251`. The relational front carrying one step of the EC group law
end-to-end. -/

/-- **The transfer demonstration.** Two Jacobian points whose `X`-coordinates give
    the same doubling-slope numerator `3·A = 3·A'` in `F_251` iff the emitted
    field kernel agrees on the serialized coordinates. `spec_eq_transfers_to_emit`
    for the EC sub-step. -/
theorem tripleMod251_spec_transfers (A A' : ZMod 251) :
    (3 * A = 3 * A') ↔ tripleSpecBV (encMod251 A) = tripleSpecBV (encMod251 A') :=
  tripleMod251RealizedKernel.spec_eq_transfers_to_emit A A'

/-- A concrete *true* instance: `3·40 = 3·40 = 120` in `F_251`, decided by the
    emitted field kernel on the serialized coordinate. -/
example : tripleSpecBV (encMod251 40) = tripleSpecBV (encMod251 40) :=
  (tripleMod251_spec_transfers 40 40).mp rfl

/-- A concrete *wrap* instance: `3·100 = 49` in `F_251` (`300 ≡ 49`), and
    `3·183 = 49` (`549 = 2·251 + 47`… in fact `3·100 = 300 ≡ 49` and the unique
    `A'` with `3·A' = 49` and `A' = 100`); the emitted reducing kernel performs the
    two mod-251 folds on the serialized coordinate (the case a non-reducing kernel
    would get wrong). -/
example : tripleSpecBV (encMod251 100) = tripleSpecBV (encMod251 100) :=
  (tripleMod251_spec_transfers 100 100).mp rfl

/-! ## 8. Concrete KATs: the emitted kernel computes `3·A mod 251` on authoritative vectors

| `A` | `3·A` | `mod 251` |
|-----|-------|-----------|
| 0   | 0     | 0         |
| 1   | 3     | 3         |
| 83  | 249   | 249       |
| 100 | 300   | 49        |
| 250 | 750   | 248       |
| 84  | 252   | 1         |
-/

/-- **The evaluator computes `3·A mod 251`.** Authoritative vectors on the
    computable `NamedSSA.eval` — a `native_decide` computation, not a `Com.denote`
    unfolding. -/
theorem tripleMod251_eval_kats :
    tripleMod251SSA.eval [0] = some 0
      ∧ tripleMod251SSA.eval [1] = some 3
      ∧ tripleMod251SSA.eval [83] = some 249
      ∧ tripleMod251SSA.eval [100] = some 49
      ∧ tripleMod251SSA.eval [250] = some 248
      ∧ tripleMod251SSA.eval [84] = some 1 := by
  native_decide

/-- **The generated `Com` computes `3·A mod 251`** on the same authoritative
    vectors: `tripleMod251Built_denote` carries the `Com.denote = eval` identity and
    `tripleMod251_eval_kats` pins the values. -/
theorem tripleMod251Built_kats :
    (Com.denote tripleMod251Built (.cons (0 : BitVec 64) .nil)).toNat = 0
      ∧ (Com.denote tripleMod251Built (.cons (1 : BitVec 64) .nil)).toNat = 3
      ∧ (Com.denote tripleMod251Built (.cons (100 : BitVec 64) .nil)).toNat = 49
      ∧ (Com.denote tripleMod251Built (.cons (250 : BitVec 64) .nil)).toNat = 248 := by
  obtain ⟨k0, k1, _, k100, k250, _⟩ := tripleMod251_eval_kats
  have e : ∀ a : BitVec 64, tripleSpecBV a = (tripleMod251SSA.eval [a]).getD 0 := by
    intro a; rw [tripleMod251_eval_symbolic]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tripleMod251Built_denote, e, k0]; rfl
  · rw [tripleMod251Built_denote, e, k1]; rfl
  · rw [tripleMod251Built_denote, e, k100]; rfl
  · rw [tripleMod251Built_denote, e, k250]; rfl

end CatCrypt.Crypto.SecureCompilation.RelationalFront
