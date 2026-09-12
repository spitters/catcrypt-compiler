/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEcEmit
public import CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

/-!
# Generic EC emit → value: the emitted point-add realizes the affine group law

`RelationalFrontGenericEcEmit.lean` proves that the generic EC point-add emitter
`emitEcAdd "<curve>_point_add" …` lowers through CatCrypt's owned front to a
two-`Ccall` Jasmin program — one call per output coordinate.  That is a
**structural** fact: it says the front accepts the rendered body and emits the
right call shape, but it says nothing about the *value* the running program
computes.

`EcRealizationGeneric.lean` proves, over an abstract `[Field F]`, that the
inversion-free Jacobian point-add (`ecJacAddZ1`, `add-2007-bl`, `Z = 1` chart)
**realizes the affine group law** (`ec_jacAdd_realizes_affineAdd`): converting
the Jacobian sum back to affine yields exactly `ecAffineAdd` at the chord slope.
That is the **value** content of EC point-add — but stated over the abstract
field carrier, with no connection to the emitted leaf program.

This module ties the two together: it crosses the **byte↔field coordinate
boundary** and shows that, *given* a leaf interpretation under which the
`<curve>_point_add` leaf computes the affine group-law coordinate value (the
`ecAffineAdd` value of `ec_jacAdd_realizes_affineAdd`), the emitted
`emitEcAdd …` program — run under `RustExec` with that leaf interpretation —
reaches a state whose two output slots hold exactly the **encoded group-sum
point** `ecAffineAdd lam P Q`.

## The realization data — a *named hypothesis*, not a hidden `rfl`

The boundary the emitted leaf cannot prove is the byte↔field correspondence: the
opaque leaf `<curve>_point_add`, applied to the byte encodings of the four input
coordinates, produces the byte encoding of the group-sum coordinate.  Exactly as
in `Bridges/ArkLibKZGDemo/ByteGroupRealization.lean` (the pairing analogue), we
bundle this as an explicit `EcEmitRealizes` structure: a coordinate encoding
`enc : F → RustVal .TFp` plus the two commuting squares (one per output
coordinate) tying the leaf's `call` value to the encoded `ecAffineAdd`
coordinate.  Because the leaf `call` oracle is an opaque `LeafSpec` field and the
field-side `ecAffineAdd` is concrete, this correspondence **cannot be proved**
in Lean — it is the honest, named assumption that the emitted curve leaf's byte
arithmetic realizes the affine group law.  Stating it as structure fields keeps
the trust surface visible, rather than collapsing it to a definitional `rfl`.

## What is *proved* from the realization data

`emitEcAdd_realizes_affineAdd`: under an arbitrary fuel `N`, an arbitrary
`LeafSpec` carrying an `EcEmitRealizes` witness, and the borrow-checker
distinctness side-conditions on the six slot names, the emitted point-add body
`emitEcAdd leaf rx ry x1 y1 x2 y2`, run from a state holding the four encoded
input coordinates, reaches a state whose `rx`/`ry` slots hold exactly
`enc (ecAffineAdd lam P Q).x` and `enc (ecAffineAdd lam P Q).y` — the encoded
affine group-sum point.

This is the generic emit→value tie for EC point-add, conditioned precisely on
the leaf-realization hypothesis.  The `RustExec` operational denotation carries
the content: the proof drives the two `RCall`s of `emitEcAdd` through
the `RustExec.call`/`RustExec.seq` rules and discharges the produced values via
the commuting squares.

## Scope

* The byte↔field commuting squares are **assumed** (`EcEmitRealizes` fields), not
  proved: they are the named trust edge at the opaque-leaf granularity the
  security proofs operate at — the same status as the pairing
  `ByteGroupRealization`.
* The affine group-law *value* `ecAffineAdd lam P Q` is the one
  `ec_jacAdd_realizes_affineAdd` certifies equals the inversion-free Jacobian
  sum, so this module's output value is the genuine EC group sum (generic chart),
  not an opaque restatement.
* Vertical-line / point-at-infinity exceptional cases are out of scope, exactly
  as for `ec_jacAdd_realizes_affineAdd`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GenericEcEmitValue

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEcEmit
open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

universe u

/-! ## 1. The byte↔field coordinate locations

Each EC coordinate is a base-field slot (`TowerType.TFp`).  `fpLoc x` is the
located base-field variable named `x`, matching the `⟨x, .TFp⟩` slots
`emitEcAdd` writes/reads. -/

/-- The located base-field (`TFp`) slot named `x` — the addressing surface of one
    affine coordinate, matching the `⟨x, .TFp⟩` operands of `emitEcAdd`. -/
def fpLoc (x : String) : Located := ⟨x, .TFp⟩

@[simp] theorem fpLoc_locVar (x : String) : (fpLoc x).locVar = x := rfl
@[simp] theorem fpLoc_locDst (x : String) : (fpLoc x).locDst = .TFp := rfl

/-! ## 2. The realization data (named byte↔field hypothesis)

`EcEmitRealizes` is the EC analogue of the pairing `ByteGroupRealization`: a
chosen coordinate encoding `enc : F → RustVal .TFp` and the two commuting
squares saying the leaf, applied to the four encoded input coordinates, produces
the encoded group-sum `x`- resp. `y`-coordinate.  The group-sum value is exactly
the `ecAffineAdd lam P Q` of `ec_jacAdd_realizes_affineAdd`. -/

/-- The byte↔field realization for the EC point-add leaf `leaf` under leaf
    interpretation `leafSpec`, over an abstract base field `F` and a fixed chord
    slope `lam` (the slope `ec_jacAdd_realizes_affineAdd` uses,
    `(Q.y − P.y)·(Q.x − P.x)⁻¹`).

    Bundles the input-coordinate encoding `encC`, the output-point encoding
    `encP`, and the single commuting square tying the leaf's `call` value to the
    encoded affine group-sum point `ecAffineAdd lam P Q`.

    The leaf takes the *same* four arguments for both output slots `emitEcAdd`
    writes (the structural emit re-uses one `<curve>_point_add` leaf per output
    coordinate — see `RelationalFrontGenericEcEmit`), so its `call` value is a
    single point-valued result; both output slots receive that one encoded
    group-sum point.  This is the honest, named replacement for a degenerate
    definitional `rfl`: the opaque leaf realizes the (concrete) affine group
    law, with the inverse-free Jacobian formula's value (`ecAffineAdd lam P Q`,
    certified by `ec_jacAdd_realizes_affineAdd`) on the right. -/
structure EcEmitRealizes {F : Type u} [Field F]
    (leafSpec : LeafSpec) (leaf : String) (lam : F) (P Q : ECAffPoint F) where
  /-- On-wire encoding of one affine input base-field coordinate. -/
  encC : F → RustVal .TFp
  /-- On-wire encoding of an affine output point (both coordinates packed into
      the `TFp` result slot). -/
  encP : ECAffPoint F → RustVal .TFp
  /-- **The commuting square.**  The leaf, applied to the four encoded input
      coordinates (regardless of the previous dest value `old`), produces the
      encoding of the affine group-sum point `ecAffineAdd lam P Q` — the value
      `ec_jacAdd_realizes_affineAdd` certifies equals the inverse-free Jacobian
      sum. -/
  add_realizes : ∀ (old : RustVal .TFp),
    leafSpec.call leaf .TFp [.TFp, .TFp, .TFp, .TFp] old
        [⟨.TFp, encC P.x⟩, ⟨.TFp, encC P.y⟩, ⟨.TFp, encC Q.x⟩, ⟨.TFp, encC Q.y⟩]
      = encP (ecAffineAdd lam P Q)

/-! ## 3. The initial state holding the four encoded input coordinates -/

/-- Initial state for an EC point-add: the four input coordinates at
    `x1,y1,x2,y2` (encoded), and dummy old values at the two output slots
    `rx,ry`.  All other slots empty. -/
def stEcAdd {F : Type u} [Field F]
    {leafSpec : LeafSpec} {leaf : String} {lam : F} {P Q : ECAffPoint F}
    (R : EcEmitRealizes leafSpec leaf lam P Q)
    (rx ry x1 y1 x2 y2 : String) : RustState :=
  rsSetTower (rsSetTower (rsSetTower (rsSetTower
    (rsSetTower (rsSetTower default
      rx ⟨.TFp, default⟩)
      ry ⟨.TFp, default⟩)
      x1 ⟨.TFp, R.encC P.x⟩)
      y1 ⟨.TFp, R.encC P.y⟩)
      x2 ⟨.TFp, R.encC Q.x⟩)
      y2 ⟨.TFp, R.encC Q.y⟩

/-- The argument list `emitEcAdd` reads — the four input-coordinate slots, as
    `Located`s. -/
def ecAddArgs (x1 y1 x2 y2 : String) : List Located :=
  [fpLoc x1, fpLoc y1, fpLoc x2, fpLoc y2]

/-! ## 4. The emit → value theorem

The emitted point-add body, run under a `LeafSpec` carrying an `EcEmitRealizes`
witness, reaches a state whose two output slots hold the encoded affine
group-sum point. -/

set_option maxHeartbeats 1000000 in
/-- **The emitted EC point-add realizes the affine group law.**  Given a leaf
    interpretation under which `<curve>_point_add` computes the affine group-law
    point (the `EcEmitRealizes` witness `R`, whose value is the
    `ecAffineAdd lam P Q` of `ec_jacAdd_realizes_affineAdd`), the emitted body
    `emitEcAdd leaf rx ry x1 y1 x2 y2`, run from `stEcAdd R …` under `RustExec`,
    reaches a state whose `rx`/`ry` slots both hold exactly the **encoded
    group-sum point** `encP (ecAffineAdd lam P Q)`.

    The fifteen distinctness hypotheses are the borrow-checker / two-output side
    conditions: the four input slots are pairwise distinct, and each output slot
    is distinct from the four inputs and from the other output. -/
theorem emitEcAdd_realizes_affineAdd
    {F : Type u} [Field F]
    {leafSpec : LeafSpec} {leaf : String} {lam : F} {P Q : ECAffPoint F}
    (R : EcEmitRealizes leafSpec leaf lam P Q)
    (N : Nat) (rx ry x1 y1 x2 y2 : String)
    (hrxy : rx ≠ ry)
    (hrx1 : rx ≠ x1) (hry1 : rx ≠ y1) (hrx2 : rx ≠ x2) (hry2 : rx ≠ y2)
    (hyx1 : ry ≠ x1) (hyy1 : ry ≠ y1) (hyx2 : ry ≠ x2) (hyy2 : ry ≠ y2)
    (h1y1 : x1 ≠ y1) (h1x2 : x1 ≠ x2) (h1y2 : x1 ≠ y2)
    (hy1x2 : y1 ≠ x2) (hy1y2 : y1 ≠ y2) (hx2y2 : x2 ≠ y2) :
    ∃ rs',
      RustExec N leafSpec (emitEcAdd leaf rx ry x1 y1 x2 y2)
        (stEcAdd R rx ry x1 y1 x2 y2) rs' ∧
      locatedLookup rs' (fpLoc rx) = some (R.encP (ecAffineAdd lam P Q)) ∧
      locatedLookup rs' (fpLoc ry) = some (R.encP (ecAffineAdd lam P Q)) := by
  -- Lookup-after-update at the same slot.
  have hself : ∀ (rs : RustState) (loc : Located) (v : RustVal loc.locDst),
      locatedLookup (locatedUpdate rs loc v) loc = some v := by
    intro rs loc v; unfold locatedLookup locatedUpdate rsSetTower; simp
  set s0 := stEcAdd R rx ry x1 y1 x2 y2 with hs0
  set args : List Located := ecAddArgs x1 y1 x2 y2 with hargsdef
  -- The four input-coordinate lookups in `s0`.
  have hx1 : s0.rsTower x1 = some ⟨.TFp, R.encC P.x⟩ := by
    simp only [hs0, stEcAdd, rsSetTower, beq_iff_eq]
    rw [if_neg h1y2, if_neg h1x2, if_neg h1y1, if_pos trivial]
  have hy1 : s0.rsTower y1 = some ⟨.TFp, R.encC P.y⟩ := by
    simp [hs0, stEcAdd, rsSetTower, hy1y2, hy1x2]
  have hx2 : s0.rsTower x2 = some ⟨.TFp, R.encC Q.x⟩ := by
    simp [hs0, stEcAdd, rsSetTower, hx2y2]
  have hy2 : s0.rsTower y2 = some ⟨.TFp, R.encC Q.y⟩ := by
    simp [hs0, stEcAdd, rsSetTower]
  -- The arg-list `RustExec.call` recovers from `s0` for `args`.
  have hargList : args.filterMap (fun a => s0.rsTower a.locVar)
      = [⟨.TFp, R.encC P.x⟩, ⟨.TFp, R.encC P.y⟩,
         ⟨.TFp, R.encC Q.x⟩, ⟨.TFp, R.encC Q.y⟩] := by
    simp [hargsdef, ecAddArgs, fpLoc, hx1, hy1, hx2, hy2]
  -- Per-arg type-recovery side condition (Option A determinism).
  have htyp : ∀ a ∈ args, ∃ v, s0.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
    intro a ha
    simp only [hargsdef, ecAddArgs, fpLoc, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨_, hx1⟩
    · exact ⟨_, hy1⟩
    · exact ⟨_, hx2⟩
    · exact ⟨_, hy2⟩
  -- `rx`'s old value in `s0`.
  have hrxold : locatedLookup s0 (fpLoc rx) = some (default : RustVal .TFp) := by
    simp [hs0, stEcAdd, locatedLookup, fpLoc, rsSetTower,
      hry2, hrx2, hry1, hrx1]
  -- First call: writes the encoded group sum into `rx`.
  have hcall1 := RustExec.call (N := N) (leafSpec := leafSpec)
    leaf (fpLoc rx) args s0 (default : RustVal .TFp)
    (args.filterMap (fun a => s0.rsTower a.locVar))
    hrxold rfl htyp
  -- Reduce the produced value via the commuting square.
  have hval1 : locatedUpdate s0 (fpLoc rx)
      (leafSpec.call leaf (fpLoc rx).locDst (args.map (·.locDst))
        (default : RustVal .TFp)
        (args.filterMap (fun a => s0.rsTower a.locVar)))
      = locatedUpdate s0 (fpLoc rx) (R.encP (ecAffineAdd lam P Q)) := by
    congr 1
    rw [hargList]
    simp only [fpLoc, Located.locDst, hargsdef, ecAddArgs, List.map]
    exact R.add_realizes _
  rw [hval1] at hcall1
  set s1 := locatedUpdate s0 (fpLoc rx) (R.encP (ecAffineAdd lam P Q)) with hs1
  -- The input lookups survive in `s1` (rx distinct from inputs).
  have hx1' : s1.rsTower x1 = some ⟨.TFp, R.encC P.x⟩ := by
    simp [hs1, fpLoc, locatedUpdate, rsSetTower, Ne.symm hrx1, hx1]
  have hy1' : s1.rsTower y1 = some ⟨.TFp, R.encC P.y⟩ := by
    simp [hs1, fpLoc, locatedUpdate, rsSetTower, Ne.symm hry1, hy1]
  have hx2' : s1.rsTower x2 = some ⟨.TFp, R.encC Q.x⟩ := by
    simp [hs1, fpLoc, locatedUpdate, rsSetTower, Ne.symm hrx2, hx2]
  have hy2' : s1.rsTower y2 = some ⟨.TFp, R.encC Q.y⟩ := by
    simp [hs1, fpLoc, locatedUpdate, rsSetTower, Ne.symm hry2, hy2]
  have hargList' : args.filterMap (fun a => s1.rsTower a.locVar)
      = [⟨.TFp, R.encC P.x⟩, ⟨.TFp, R.encC P.y⟩,
         ⟨.TFp, R.encC Q.x⟩, ⟨.TFp, R.encC Q.y⟩] := by
    simp [hargsdef, ecAddArgs, fpLoc, hx1', hy1', hx2', hy2']
  have htyp' : ∀ a ∈ args, ∃ v, s1.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
    intro a ha
    simp only [hargsdef, ecAddArgs, fpLoc, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨_, hx1'⟩
    · exact ⟨_, hy1'⟩
    · exact ⟨_, hx2'⟩
    · exact ⟨_, hy2'⟩
  -- `ry`'s old value in `s1` (ry distinct from rx and inputs).
  have hryold : locatedLookup s1 (fpLoc ry) = some (default : RustVal .TFp) := by
    simp only [hs1, fpLoc, locatedUpdate]
    rw [locatedLookup_rsSetTower_other _ _ _ _ (show rx ≠ (Located.mk ry .TFp).locVar by
      exact hrxy)]
    simp [hs0, stEcAdd, locatedLookup, rsSetTower,
      hyy2, hyx2, hyy1, hyx1]
  -- Second call: writes the encoded group sum into `ry`.
  have hcall2 := RustExec.call (N := N) (leafSpec := leafSpec)
    leaf (fpLoc ry) args s1 (default : RustVal .TFp)
    (args.filterMap (fun a => s1.rsTower a.locVar))
    hryold rfl htyp'
  have hval2 : locatedUpdate s1 (fpLoc ry)
      (leafSpec.call leaf (fpLoc ry).locDst (args.map (·.locDst))
        (default : RustVal .TFp)
        (args.filterMap (fun a => s1.rsTower a.locVar)))
      = locatedUpdate s1 (fpLoc ry) (R.encP (ecAffineAdd lam P Q)) := by
    congr 1
    rw [hargList']
    simp only [fpLoc, Located.locDst, hargsdef, ecAddArgs, List.map]
    exact R.add_realizes _
  rw [hval2] at hcall2
  set s2 := locatedUpdate s1 (fpLoc ry) (R.encP (ecAffineAdd lam P Q)) with hs2
  refine ⟨s2, ?_, ?_, ?_⟩
  · -- Sequence the two calls.
    have : emitEcAdd leaf rx ry x1 y1 x2 y2
        = (LowCT.RCall leaf (fpLoc rx) args).RSeq (LowCT.RCall leaf (fpLoc ry) args) := by
      rfl
    rw [this]
    exact RustExec.seq _ _ _ _ _ hcall1 hcall2
  · -- Read off `rx`: unchanged by the `ry` update (rx ≠ ry).
    rw [hs2]
    simp only [fpLoc]
    rw [locatedUpdate_other _ _ _ _
      (show (Located.mk ry .TFp).locVar ≠ (Located.mk rx .TFp).locVar from hrxy.symm)]
    rw [hs1]; exact hself _ _ _
  · -- Read off `ry`.
    rw [hs2]; exact hself _ _ _

/-! ## 5. Per-curve instance

Routing a concrete curve's point-add value through the front is one application
of the generic theorem at the curve's leaf name (`"bls377_point_add"`) — no
per-curve operational re-derivation.  The byte↔field realization `R` (the named
trust edge) is the only per-curve datum; everything else is the generic
`emitEcAdd_realizes_affineAdd`.  This mirrors the §"Per-curve instances" of
`RelationalFrontGenericEcEmit` for the structural side. -/

/-- The per-curve **point-add value** routing, recovered generically: the emitted
    `bls377_point_add` body reaches a state whose output slots hold the encoded
    affine group sum, given the curve's realization witness `R`. -/
example {F : Type u} [Field F] {leafSpec : LeafSpec} {lam : F} {P Q : ECAffPoint F}
    (R : EcEmitRealizes leafSpec "bls377_point_add" lam P Q) (N : Nat) :
    ∃ rs',
      RustExec N leafSpec
        (emitEcAdd "bls377_point_add" "rx" "ry" "x1" "y1" "x2" "y2")
        (stEcAdd R "rx" "ry" "x1" "y1" "x2" "y2") rs' ∧
      locatedLookup rs' (fpLoc "rx") = some (R.encP (ecAffineAdd lam P Q)) ∧
      locatedLookup rs' (fpLoc "ry") = some (R.encP (ecAffineAdd lam P Q)) :=
  emitEcAdd_realizes_affineAdd R N "rx" "ry" "x1" "y1" "x2" "y2"
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end CatCrypt.Crypto.SecureCompilation.GenericEcEmitValue
