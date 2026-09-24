/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericEcEmitValue

/-!
# Discharging `EcEmitRealizes` from the generic EC group-law realization

`GenericEcEmitValue.lean` localizes the EC emit→value residual as the named
hypothesis `EcEmitRealizes leafSpec leaf lam P Q`: its `add_realizes` field says
the `<curve>_point_add` leaf, applied to the four encoded input coordinates,
produces `encP (ecAffineAdd lam P Q)` — the byte encoding of the *affine
group-sum point*.  As stated there, that residual is "the leaf computes the
**abstract affine group law**" — a wide gap, exactly as the field version's
`FieldEmitRealizes` residual is "the leaf computes the **abstract field
value**".

This module **narrows that residual** using our *proven* generic EC realization
`ec_jacAdd_realizes_affineAdd` (`EcRealizationGeneric.lean`), the EC analogue of
`FieldEmitRealizesFromCommSquare.lean`.  That theorem proves, over an abstract
`[Field F]`, the commuting identity

```
  ecJacToAffine (ecJacAddZ1 (ofAffine P) (ofAffine Q))
    = ecAffineAdd ((Q.y − P.y)·(Q.x − P.x)⁻¹) P Q
```

i.e. the inversion-free `add-2007-bl` Jacobian add (`ecJacAddZ1`), projected back
to affine by the one-inverse conversion `ecJacToAffine`, equals the affine
group law at the chord slope.  We use this identity to *discharge* `add_realizes`
**conditioned only on the narrower "leaf computes the Jacobian-add kernel" fact**
— that the leaf-call value is the encoding of
`ecJacToAffine (ecJacAddZ1 (ofAffine P) (ofAffine Q))`.  Everything *above* the
inversion-free kernel — the projective→affine inverse, the affine group-law
value content — is then supplied by `ec_jacAdd_realizes_affineAdd`, which is a
proved theorem, not an assumption.

## The encoding wiring (precisely what is tied vs. assumed)

Both the input coordinates and the output point are carried in `.TFp` slots.  We
keep:

* an input-coordinate encoding `encC : F → RustVal .TFp`; and
* an affine-point encoding `encP : ECAffPoint F → RustVal .TFp` (the output
  convention, the same `encP` the `EcEmitRealizes` consumer uses).

The bridge `EcEmitRealizes` is then discharged from **one narrow fact**:

* **(kernel-realization, the residual)** for every previous dest value `old`, the
  leaf, applied to the four encoded input coordinates, returns
  `encP (ecJacToAffine (ecJacAddZ1 (ofAffine P) (ofAffine Q)))` — the leaf-call
  value *is* the encoding of the inversion-free Jacobian-add kernel projected to
  affine.  This is a KAT / owned-emit fact about the **bytes** of the emitted
  curve kernel, strictly narrower than "leaf = abstract affine group sum": it
  pins the kernel value (the `add-2007-bl` formula's output, with the inverse
  amortized into `ecJacToAffine`), not the abstract group law.

Given that, the affine group-law value content `add_realizes` is **proved**,
*because* `ec_jacAdd_realizes_affineAdd` proves the kernel value equals
`ecAffineAdd lam P Q` (at the chord slope `lam`).  The remaining residual is
"the leaf's bytes are the inversion-free Jacobian-add kernel's bytes"
(kernel-realization), narrower than "the leaf computes the abstract affine group
sum".

## What is closed here vs. localized

* **Closed (Lean theorem):** the affine-group-law value content of
  `add_realizes`.  Given the kernel-realization hypothesis, the leaf-call value
  encodes the affine group sum — discharged by `ec_jacAdd_realizes_affineAdd`
  (our proved generic realization), *not* assumed.  This is the
  narrowing: the projective→affine inverse and the `ecAffineAdd` value come from
  a theorem.
* **Localized (narrowed residual):** the leaf-call value is
  `encP (ecJacToAffine (ecJacAddZ1 …))` — that the leaf's emitted bytes are the
  inversion-free Jacobian-add kernel's bytes.  This is the KAT fact (owned-emit
  KAT), narrower than the original `EcEmitRealizes.add_realizes` residual.

## Non-vacuity

`ecJacKernelRealizes_canonical` exhibits a concrete `LeafSpec` (a
Jacobian-add-on-the-four-coordinates realizer) under which the kernel-realization
holds, so the narrowed hypothesis is satisfiable.  `ecEmitRealizes_canonical`
threads it through to a full `EcEmitRealizes` witness, confirming the bridge
delivers an inhabitant of the `GenericEcEmitValue` hypothesis from the generic
group-law realization — and `emitEcAdd_realizes_affineAdd_of_kernel` composes it
with `emitEcAdd_realizes_affineAdd` for the end-to-end emit→value statement with
the residual narrowed to the Jacobian kernel.

## Scope

* The kernel-realization fact is **assumed** (the `EcJacKernelRealizes`
  hypothesis), not proved: it is the named trust edge at the opaque-leaf
  granularity the security proofs operate at — the same status as the limb-kernel
  fact in `FieldEmitRealizesFromCommSquare`.
* The affine group-law *value* `ecAffineAdd lam P Q` is the one
  `ec_jacAdd_realizes_affineAdd` certifies equals the inverse-free Jacobian sum,
  so this module's output value is the EC group sum (generic chart), not
  an opaque restatement.
* The chord slope is fixed to `lam = (Q.y − P.y)·(Q.x − P.x)⁻¹` (the slope of
  `ec_jacAdd_realizes_affineAdd`); vertical-line / point-at-infinity exceptional
  cases are out of scope, exactly as for `ec_jacAdd_realizes_affineAdd`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcEmitRealizesFromGroupLaw

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
open CatCrypt.Crypto.SecureCompilation.GenericEcEmitValue
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEcEmit

universe u

/-! ## §1  The chord slope of the generic realization

`ec_jacAdd_realizes_affineAdd` realizes the affine group law at the specific
chord slope `(Q.y − P.y)·(Q.x − P.x)⁻¹`.  We name it so the discharged
`EcEmitRealizes` witness is at exactly that slope. -/

/-- The chord slope `λ = (Q.y − P.y)·(Q.x − P.x)⁻¹` of the generic EC
    realization `ec_jacAdd_realizes_affineAdd`.  The discharged `EcEmitRealizes`
    witness produced below is at this slope. -/
def chordSlope {F : Type u} [Field F] (P Q : ECAffPoint F) : F :=
  (Q.y - P.y) * (Q.x - P.x)⁻¹

/-! ## §2  The narrowed residual: the leaf computes the Jacobian-add kernel

`EcJacKernelRealizes` is the *narrowed* residual the generic realization lets us
condition on: the leaf-call value, on the four encoded input coordinates, is the
encoding of the inversion-free Jacobian add projected to affine,
`ecJacToAffine (ecJacAddZ1 (ofAffine P) (ofAffine Q))`.  This is a fact about the
**bytes** of the emitted kernel — a KAT / owned-emit statement — strictly weaker
than the original `EcEmitRealizes.add_realizes`, which spoke about the abstract
affine group sum. -/

/-- **The narrowed (kernel-level) residual.**  For every previous dest value
    `old`, the leaf, applied to the four encoded input coordinates, returns the
    `encP`-encoding of the inversion-free Jacobian-add kernel projected to affine,
    `ecJacToAffine (ecJacAddZ1 (ofAffine P) (ofAffine Q))`.  This is the KAT fact
    "the leaf's bytes are the Jacobian-add kernel's bytes" — it says nothing about
    the affine group law itself, only that the leaf computes the inversion-free
    `add-2007-bl` formula (with the inverse amortized into `ecJacToAffine`).

    The encodings `encC` (input coordinate) / `encP` (output point) are the same
    conventions the discharged `EcEmitRealizes` witness exposes. -/
def EcJacKernelRealizes {F : Type u} [Field F]
    (leafSpec : LeafSpec) (leaf : String) (P Q : ECAffPoint F)
    (encC : F → RustVal .TFp) (encP : ECAffPoint F → RustVal .TFp) : Prop :=
  ∀ (old : RustVal .TFp),
    leafSpec.call leaf .TFp [.TFp, .TFp, .TFp, .TFp] old
        [⟨.TFp, encC P.x⟩, ⟨.TFp, encC P.y⟩, ⟨.TFp, encC Q.x⟩, ⟨.TFp, encC Q.y⟩]
      = encP (ecJacToAffine (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q)))

/-! ## §3  The discharge: the generic realization turns the kernel residual into
`EcEmitRealizes`

This is the payload.  Given the narrowed kernel-realization (§2) and the
generic-chart side condition `Q.x ≠ P.x`, the abstract affine-group-law
`EcEmitRealizes` follows — *because* `ec_jacAdd_realizes_affineAdd` proves
`ecJacToAffine (ecJacAddZ1 …) = ecAffineAdd lam P Q`.  The affine-group-law value
content is supplied by the proved generic realization, so the residual that
remains is just the kernel fact. -/

/-- **The generic realization discharges `EcEmitRealizes`.**

    Suppose:
    * `hkernel` — the narrowed residual: the leaf-call value is the `encP`-encoding
      of the inversion-free Jacobian-add kernel `ecJacToAffine (ecJacAddZ1 …)`
      (§2, a KAT fact); and
    * `hx` — the generic-chart side condition `Q.x − P.x ≠ 0` (distinct
      `x`-coordinates), the same hypothesis `ec_jacAdd_realizes_affineAdd` takes.

    Then `EcEmitRealizes leafSpec leaf (chordSlope P Q) P Q` holds.  The proof
    discharges `add_realizes` by rewriting the kernel value through
    `ec_jacAdd_realizes_affineAdd` — our *proved* generic EC realization — turning
    the inversion-free Jacobian-kernel value into the abstract affine group sum
    `ecAffineAdd (chordSlope P Q) P Q`.  No affine-group-law value content is
    assumed; it is discharged by the theorem. -/
def ecEmitRealizes_of_kernel {F : Type u} [Field F]
    (leafSpec : LeafSpec) (leaf : String) (P Q : ECAffPoint F)
    (encC : F → RustVal .TFp) (encP : ECAffPoint F → RustVal .TFp)
    (hkernel : EcJacKernelRealizes leafSpec leaf P Q encC encP)
    (hx : Q.x - P.x ≠ 0) :
    EcEmitRealizes leafSpec leaf (chordSlope P Q) P Q where
  encC := encC
  encP := encP
  add_realizes old := by
    -- The leaf value is the encoded Jacobian-add kernel (`hkernel`); the generic
    -- realization rewrites that kernel to the affine group sum.
    rw [hkernel old]
    -- `ec_jacAdd_realizes_affineAdd` : the projected Jacobian add = the affine
    -- group sum at the chord slope `chordSlope P Q`.
    rw [ec_jacAdd_realizes_affineAdd P Q hx]
    rfl

/-! ## §4  Non-vacuity: a canonical Jacobian-add realizer

We exhibit a concrete `LeafSpec` under which the narrowed kernel-realization (§2)
holds, and thread it through `ecEmitRealizes_of_kernel` to a full `EcEmitRealizes`
witness — confirming the bridge produces an inhabitant of the `GenericEcEmitValue`
hypothesis from the generic realization, not an over-constraint. -/

/-- The canonical `CallSpec` realizing the inversion-free Jacobian-add kernel at
    `leaf` (over fixed inputs `P Q`, the AUCurves "feval at a point" convention):
    at the target name, for a `.TFp` result, it returns the fixed encoded kernel
    value `encP (ecJacToAffine (ecJacAddZ1 (ofAffine P) (ofAffine Q)))`; off-target
    or off-type it returns `oldDest`.  The EC analogue of `klimbAddCallSpec` — the
    leaf value is the encoded inversion-free `add-2007-bl` kernel. -/
def ecJacAddCallSpec {F : Type u} [Field F]
    (P Q : ECAffPoint F) (encP : ECAffPoint F → RustVal .TFp) (leaf : String) :
    CallSpec :=
  fun fname dt _argTs oldDest _args =>
    if fname = leaf then
      if hd : dt = TowerType.TFp then
        hd ▸ encP (ecJacToAffine (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q)))
      else oldDest
    else oldDest

/-- **Non-vacuity for the narrowed residual.**  For the canonical realizer built
    from `ecJacAddCallSpec`, the kernel-realization holds — the narrowed
    hypothesis is satisfiable. -/
theorem ecJacKernelRealizes_canonical {F : Type u} [Field F]
    (P Q : ECAffPoint F) (encC : F → RustVal .TFp) (encP : ECAffPoint F → RustVal .TFp)
    (leaf : String) (limbStore : LimbStoreSpec) :
    EcJacKernelRealizes
      { call := ecJacAddCallSpec P Q encP leaf, limbStore := limbStore }
      leaf P Q encC encP := by
  intro old
  show ecJacAddCallSpec P Q encP leaf leaf .TFp [.TFp, .TFp, .TFp, .TFp] old
      [⟨.TFp, encC P.x⟩, ⟨.TFp, encC P.y⟩, ⟨.TFp, encC Q.x⟩, ⟨.TFp, encC Q.y⟩] = _
  simp only [ecJacAddCallSpec, if_true, dite_true]

/-- **Non-vacuity for the full bridge.**  Threading the canonical Jacobian-add
    realizer through `ecEmitRealizes_of_kernel` (under the generic-chart side
    condition) yields an `EcEmitRealizes` inhabitant — so the generic
    group-law realization does deliver the `GenericEcEmitValue` hypothesis. -/
def ecEmitRealizes_canonical {F : Type u} [Field F]
    (P Q : ECAffPoint F) (encC : F → RustVal .TFp) (encP : ECAffPoint F → RustVal .TFp)
    (leaf : String) (limbStore : LimbStoreSpec)
    (hx : Q.x - P.x ≠ 0) :
    EcEmitRealizes
      { call := ecJacAddCallSpec P Q encP leaf, limbStore := limbStore }
      leaf (chordSlope P Q) P Q :=
  ecEmitRealizes_of_kernel _ leaf P Q encC encP
    (ecJacKernelRealizes_canonical P Q encC encP leaf limbStore) hx

/-! ## §5  Composed payload: emit → affine group VALUE, residual = Jacobian kernel

Composing §3 with `GenericEcEmitValue.emitEcAdd_realizes_affineAdd` gives the
end-to-end statement: *running* the emitted `emitEcAdd` program reaches a state
whose two output slots hold the encoded affine group-sum point
`encP (ecAffineAdd (chordSlope P Q) P Q)` — with the *only* cross-prover residual
the narrowed Jacobian-kernel fact (§2), the affine-group-law value content
supplied by `ec_jacAdd_realizes_affineAdd`. -/

set_option maxHeartbeats 1000000 in
/-- **The emit→affine-group-VALUE bridge with the residual narrowed to the
    Jacobian kernel.**  Under the narrowed kernel-realization (§2) and the
    generic-chart side condition, running `emitEcAdd leaf rx ry x1 y1 x2 y2`
    reaches a state whose `rx`/`ry` slots both hold the encoded affine group-sum
    point.  Compared to `emitEcAdd_realizes_affineAdd`, the `EcEmitRealizes`
    premise is *discharged here* from the generic realization, so the surviving
    residual is the Jacobian-kernel KAT fact, not "leaf = abstract affine group
    sum".

    The fifteen distinctness hypotheses are the borrow-checker / two-output side
    conditions, passed through unchanged from `emitEcAdd_realizes_affineAdd`. -/
theorem emitEcAdd_realizes_affineAdd_of_kernel
    {F : Type u} [Field F]
    {leafSpec : LeafSpec} {leaf : String} {P Q : ECAffPoint F}
    {encC : F → RustVal .TFp} {encP : ECAffPoint F → RustVal .TFp}
    (hkernel : EcJacKernelRealizes leafSpec leaf P Q encC encP)
    (hx : Q.x - P.x ≠ 0)
    (N : Nat) (rx ry x1 y1 x2 y2 : String)
    (hrxy : rx ≠ ry)
    (hrx1 : rx ≠ x1) (hry1 : rx ≠ y1) (hrx2 : rx ≠ x2) (hry2 : rx ≠ y2)
    (hyx1 : ry ≠ x1) (hyy1 : ry ≠ y1) (hyx2 : ry ≠ x2) (hyy2 : ry ≠ y2)
    (h1y1 : x1 ≠ y1) (h1x2 : x1 ≠ x2) (h1y2 : x1 ≠ y2)
    (hy1x2 : y1 ≠ x2) (hy1y2 : y1 ≠ y2) (hx2y2 : x2 ≠ y2) :
    ∃ rs',
      RustExec N leafSpec (emitEcAdd leaf rx ry x1 y1 x2 y2)
        (stEcAdd (ecEmitRealizes_of_kernel leafSpec leaf P Q encC encP hkernel hx)
          rx ry x1 y1 x2 y2) rs' ∧
      locatedLookup rs' (fpLoc rx)
        = some (encP (ecAffineAdd (chordSlope P Q) P Q)) ∧
      locatedLookup rs' (fpLoc ry)
        = some (encP (ecAffineAdd (chordSlope P Q) P Q)) :=
  emitEcAdd_realizes_affineAdd
    (ecEmitRealizes_of_kernel leafSpec leaf P Q encC encP hkernel hx)
    N rx ry x1 y1 x2 y2 hrxy hrx1 hry1 hrx2 hry2 hyx1 hyy1 hyx2 hyy2
    h1y1 h1x2 h1y2 hy1x2 hy1y2 hx2y2

end CatCrypt.Crypto.SecureCompilation.EcEmitRealizesFromGroupLaw
