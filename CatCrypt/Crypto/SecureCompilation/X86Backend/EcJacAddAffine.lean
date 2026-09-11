/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The capstone: the emitted Jacobian point-add realizes the affine EC group law

`EcJacAddValue.lean` proves the **value** identity `jacAddBlock_realizes_jacAddGen`:
running the emitted straight-line block `jacAddBlock` from a frame holding
`P₁ = (X₁,Y₁,Z₁)`, `P₂ = (X₂,Y₂,Z₂)` (in the de-Montgomery `slotFieldVal`
interpretation over `ZMod N`) leaves the output slots `sX3`/`sY3`/`sZ3` holding
exactly the field coordinates of `EcProjectiveGeneric.jacAddGen`.

`EcProjectiveAddGeneric.lean` proves the **abstract group-law** tie
`jacAddGen_realizes`: over `[Field F]`, converting that raw `add-2007-bl`
Jacobian triple back to affine (`jacToAffineGen`, one inverse) equals the affine
chord-add `ecAffineAdd` of the two projected inputs at the chord slope — in the
generic chart (`Z₁, Z₂ ≠ 0`, distinct projected `x`, `H ≠ 0`).

This module chains the two over `F := ZMod N`: the emitted `jacAddBlock`'s output
slots, read as a Jacobian point via `slotFieldVal` and projected by
`jacToAffineGen`, equal the **affine elliptic-curve group sum** `ecAffineAdd lam
P Q` of the two input affine points. End-to-end this ties the emitted `runBlock`
point-add to the abstract affine group operation, modulo the carried per-op
AUCurves canonicalisation realizers (`JacAddRealized`) and the generic-chart
non-degeneracy.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddAffine

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric
open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

variable {N : Nat} [NeZero N]

/-! ## The output slots as a Jacobian point

`outX3`/`outY3`/`outZ3` read the three output slots of the final `runBlock`
state as `ZMod N` field elements (the de-Montgomery `slotFieldVal`). By
`jacAddBlock_realizes_jacAddGen` they are the three coordinates of
`jacAddGen` applied to the six input coordinates. -/

/-- The output Jacobian `X₃` of the emitted block, as a `ZMod N` field element. -/
def outX3 (N : Nat) (s0 : JState 64) (base : String) : ZMod N :=
  slotFieldVal N (runBlock s0 jacAddBlock) base sX3

/-- The output Jacobian `Y₃` of the emitted block, as a `ZMod N` field element. -/
def outY3 (N : Nat) (s0 : JState 64) (base : String) : ZMod N :=
  slotFieldVal N (runBlock s0 jacAddBlock) base sY3

/-- The output Jacobian `Z₃` of the emitted block, as a `ZMod N` field element. -/
def outZ3 (N : Nat) (s0 : JState 64) (base : String) : ZMod N :=
  slotFieldVal N (runBlock s0 jacAddBlock) base sZ3

omit [NeZero N] in
/-- The output triple of the emitted block equals `jacAddGen` of the six input
    coordinates (the value identity `jacAddBlock_realizes_jacAddGen`, repackaged
    componentwise via the named output reads). -/
theorem out_eq_jacAddGen [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0) :
    (outX3 N s0 base, outY3 N s0 base, outZ3 N s0 base)
      = jacAddGen (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base)
          (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base) :=
  jacAddBlock_realizes_jacAddGen R

omit [NeZero N] in
/-- The output `X₃` slot value equals the first coordinate of `jacAddGen`. -/
theorem outX3_eq [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0) :
    outX3 N s0 base
      = (jacAddGen (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base)
          (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base)).1 :=
  congrArg Prod.fst (out_eq_jacAddGen R)

omit [NeZero N] in
/-- The output `Y₃` slot value equals the second coordinate of `jacAddGen`. -/
theorem outY3_eq [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0) :
    outY3 N s0 base
      = (jacAddGen (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base)
          (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base)).2.1 :=
  congrArg (fun p => p.2.1) (out_eq_jacAddGen R)

omit [NeZero N] in
/-- The output `Z₃` slot value equals the third coordinate of `jacAddGen`. -/
theorem outZ3_eq [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0) :
    outZ3 N s0 base
      = (jacAddGen (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base)
          (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base)).2.2 :=
  congrArg (fun p => p.2.2) (out_eq_jacAddGen R)

/-! ## The capstone

Chaining `out_eq_jacAddGen` (emitted block → `jacAddGen` field values) with
`jacAddGen_realizes` (`jacAddGen` → affine group law) gives the affine EC group
sum of the two input affine points, read from the emitted block's output slots. -/

omit [NeZero N] in
/-- **The capstone: the emitted `jacAddBlock` realizes the affine EC group sum.**

    Instantiate `F := ZMod N` (`[Fact (Nat.Prime N)]`, as
    `jacAddBlock_realizes_jacAddGen` requires). Given:

    * the carried per-op AUCurves-canonicalised field realizers `R`
      (`JacAddRealized` — multiply via `feMulFrameAtReduced`/`AUCurvesMontReduceFaithful`,
      add/sub via the add/sub canonicalisation bridge), and
    * the generic-chart non-degeneracy of `jacAddGen_realizes` (`hZ1 : Z₁ ≠ 0`,
      `hZ2 : Z₂ ≠ 0`, `hH : X₂Z₁² − X₁Z₂² ≠ 0`),

    the emitted block's three output slots `sX3`/`sY3`/`sZ3` — read via
    `slotFieldVal` as a Jacobian point `(outX3, outY3, outZ3)` and projected to
    affine by `jacToAffineGen` — equal the **affine elliptic-curve group sum**
    `ecAffineAdd lam P Q` of the two input affine points
    `P = jacToAffineGen X₁ Y₁ Z₁`, `Q = jacToAffineGen X₂ Y₂ Z₂` at the chord
    slope `lam = (Q.y − P.y)·(Q.x − P.x)⁻¹`.

    This is `out_eq_jacAddGen` (emitted runBlock → `jacAddGen` field values)
    composed with `EcProjectiveAddGeneric.jacAddGen_realizes` (`jacAddGen` →
    affine group law), tying the emitted point-add to the abstract affine EC
    group operation end-to-end. -/
theorem jacAddBlock_realizes_affineAdd [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0)
    (hZ1 : inZ1 N s0 base ≠ 0) (hZ2 : inZ2 N s0 base ≠ 0)
    (hH : inX2 N s0 base * inZ1 N s0 base ^ 2
        - inX1 N s0 base * inZ2 N s0 base ^ 2 ≠ 0)
    (hZ3 : outZ3 N s0 base ≠ 0) :
    jacToAffineGen (outX3 N s0 base) (outY3 N s0 base) (outZ3 N s0 base) hZ3
      = ecAffineAdd
          (((jacToAffineGen (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base) hZ2).y
              - (jacToAffineGen (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base) hZ1).y)
            * ((jacToAffineGen (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base) hZ2).x
              - (jacToAffineGen (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base) hZ1).x)⁻¹)
          (jacToAffineGen (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base) hZ1)
          (jacToAffineGen (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base) hZ2) := by
  -- The output slot values are the three coordinates of `jacAddGen` of the inputs.
  have hX := outX3_eq R
  have hY := outY3_eq R
  have hZ := outZ3_eq R
  -- Rewrite the two non-dependent value arguments of `jacToAffineGen` to the
  -- `jacAddGen` coordinates.
  rw [show outX3 N s0 base = _ from hX, show outY3 N s0 base = _ from hY]
  -- The third coordinate's `Z₃ ≠ 0` proof depends on `outZ3`; revert it so
  -- rewriting `outZ3` along `hZ` transports both the value and the proof together,
  -- then reintroduce. The goal is then exactly `jacAddGen_realizes`'s LHS.
  revert hZ3
  rw [show outZ3 N s0 base = _ from hZ]
  intro hZ3
  exact @jacAddGen_realizes (ZMod N) _
    (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base)
    (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base) hZ1 hZ2 hH hZ3

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddAffine
