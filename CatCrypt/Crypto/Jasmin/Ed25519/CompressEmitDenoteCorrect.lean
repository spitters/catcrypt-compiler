/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Ed25519.CompressEmitCorrect
import CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness

/-!
# `ed25519_compress` — denote-level correctness

`CompressEmitCorrect.lean` establishes the **algebraic** correctness of
the Bernstein-chain-based compress (`compressFromChain bernsteinInvChain
xyzt = compress_spec xyzt`) and a **structural** match against the emit
(`callNames ed25519_compress_cmd = [...]`).

This file closes the missing semantic link: a **modular** denotational
correctness theorem that says, *conditional on per-leaf specifications,*
running the emitted `LowCT` via `RustExec` produces a final state whose
output slot holds the byte encoding of `compress_spec`.

## What is proved here

* `CompressLeafSpecCorrect leafSpec mathPkg : Prop` — bundle of seven
  per-leaf specifications (3 slot extractors, 1 invert, 2 muls, 1 pack).
* `compress_emit_denote_correct` — given the bundle, the `RustExec`
  derivation of `ed25519_compress_cmd` populates the `out` slot with the
  byte-array value the math layer dictates.
* Per-leaf specs and a math-package record (`CompressMathPkg`) are
  reusable for future emit-level work.

## Approach: leaf-spec hypotheses (the same modular pattern as
`montUToEdwardsBody_functional_correctness` in
`Examples/EmittedASTCorrectness.lean`).

We do **not** define `LowCT.denote` from scratch — `RustExec` already
provides a big-step semantics in `LowCT.lean` (§6).  Per-leaf
abstractions consume `RustVal` byte-arrays and produce `RustVal`
byte-arrays; the leaf-spec hypotheses state that each call delegates to
the corresponding math op.

The math layer is opaque (parameterised): the user-facing reference is
`compress_spec`, which lives over `Fp25519 := ZMod p25519`.  A concrete
instantiation that bridges to `compress_spec` would supply a coupling
between the 40-byte slot encoding (`RustVal (TBytes 40)`) and `Fp25519`;
that bridge is out of scope for this file (it lives in the dalek shim
verified empirically via byte-for-byte difftesting).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.CompressEmitDenoteCorrect

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit

/-! ## §1  Math package: abstract operations on byte-array slots

We treat the 40-byte slot encoding (`RustVal (TBytes 40)`) and the
32-byte output encoding (`RustVal (TBytes 32)`) opaquely.  The math
package bundles the abstract operations needed by the compress
decomposition. -/

/-- The runtime byte-array type for a single 40-byte field-element slot. -/
abbrev Slot40 : Type := RustVal (TowerType.TBytes 40)

/-- The runtime byte-array type for the 200-byte XYZT input bundle. -/
abbrev Slot200 : Type := RustVal (TowerType.TBytes 200)

/-- The runtime byte-array type for the 32-byte compressed output. -/
abbrev Slot32 : Type := RustVal (TowerType.TBytes 32)

/-- Math package: the seven byte-level operations that the leaf calls
    implement.  Each takes byte-array values (encoded representations)
    and returns the same.

    * `extractX`, `extractY`, `extractZ` — extract the three field
      coordinates from the 200-byte XYZT bundle.
    * `inv` — compute the multiplicative inverse (modular exponentiation
      by `p - 2`) on the 40-byte slot encoding.
    * `mul` — multiply two field elements (40-byte encoding).
    * `pack` — pack `(y_aff, x_aff)` into the 32-byte compressed
      output, OR-ing the sign bit of `x_aff` into bit 255. -/
structure CompressMathPkg where
  extractX : Slot200 → Slot40
  extractY : Slot200 → Slot40
  extractZ : Slot200 → Slot40
  inv      : Slot40 → Slot40
  mul      : Slot40 → Slot40 → Slot40
  pack     : Slot40 → Slot40 → Slot32

/-! ## §2  Per-leaf correctness predicates

Each predicate fixes the result of `leafSpec.call` for one of the seven
leaves used in `ed25519_compress_cmd`, in terms of the corresponding
math-package op.  The predicates are unary (single argument), binary
(two-argument), or ternary as appropriate.

These mirror `Fe25519UnopLeafCorrect` / `Fe25519BinopLeafCorrect` in
`Examples/EmittedASTCorrectness.lean`. -/

/-- `xyzt_slot_*` (unpack-X/Y/Z): a single-argument leaf on `(TBytes 200)`
    whose output is a `(TBytes 40)`. -/
def XyztSlotLeafCorrect (leafSpec : LeafSpec) (name : String)
    (mathOp : Slot200 → Slot40) : Prop :=
  ∀ (oldV : Slot40) (vIn : Slot200),
    leafSpec.call name (TowerType.TBytes 40) [TowerType.TBytes 200] oldV
      [⟨TowerType.TBytes 200, vIn⟩] = mathOp vIn

/-- `fe25519_invert_slot`: a single-argument unary leaf on `(TBytes 40)`. -/
def Fe25519InvertSlotLeafCorrect (leafSpec : LeafSpec)
    (mathOp : Slot40 → Slot40) : Prop :=
  ∀ (oldV vIn : Slot40),
    leafSpec.call "fe25519_invert_slot" (TowerType.TBytes 40)
      [TowerType.TBytes 40] oldV [⟨TowerType.TBytes 40, vIn⟩] = mathOp vIn

/-- `fe25519_mul_slot`: a two-argument binary leaf on `(TBytes 40)`. -/
def Fe25519MulSlotLeafCorrect (leafSpec : LeafSpec)
    (mathOp : Slot40 → Slot40 → Slot40) : Prop :=
  ∀ (oldV vA vB : Slot40),
    leafSpec.call "fe25519_mul_slot" (TowerType.TBytes 40)
      [TowerType.TBytes 40, TowerType.TBytes 40] oldV
      [⟨TowerType.TBytes 40, vA⟩, ⟨TowerType.TBytes 40, vB⟩] = mathOp vA vB

/-- `fe25519_pack_sign`: a two-argument leaf on `(TBytes 40)` whose
    output is `(TBytes 32)`. -/
def Fe25519PackSignLeafCorrect (leafSpec : LeafSpec)
    (mathOp : Slot40 → Slot40 → Slot32) : Prop :=
  ∀ (oldV : Slot32) (vY vX : Slot40),
    leafSpec.call "fe25519_pack_sign" (TowerType.TBytes 32)
      [TowerType.TBytes 40, TowerType.TBytes 40] oldV
      [⟨TowerType.TBytes 40, vY⟩, ⟨TowerType.TBytes 40, vX⟩] = mathOp vY vX

/-- Bundle of leaf-spec correctness predicates for the compress emit. -/
structure CompressLeafSpecCorrect (leafSpec : LeafSpec)
    (mathPkg : CompressMathPkg) : Prop where
  xyztSlotX : XyztSlotLeafCorrect leafSpec "xyzt_slot_x" mathPkg.extractX
  xyztSlotY : XyztSlotLeafCorrect leafSpec "xyzt_slot_y" mathPkg.extractY
  xyztSlotZ : XyztSlotLeafCorrect leafSpec "xyzt_slot_z" mathPkg.extractZ
  invertSlot : Fe25519InvertSlotLeafCorrect leafSpec mathPkg.inv
  mulSlot   : Fe25519MulSlotLeafCorrect leafSpec mathPkg.mul
  packSign  : Fe25519PackSignLeafCorrect leafSpec mathPkg.pack

/-! ## §3  Spec-level compress (byte-level)

Given a `CompressMathPkg`, the byte-level reference compress is the
straightforward composition the seven leaves implement.  Each step
exactly mirrors `compressFromChain` with the math layer abstracted into
the package. -/

/-- The byte-level reference compress: extract the three coords, invert
    Z, scale Y and X by Z⁻¹, then pack.  Faithful to the leaf-call
    sequence in `ed25519_compress_cmd`. -/
def compress_byte_spec (mathPkg : CompressMathPkg) (xyzt : Slot200) : Slot32 :=
  let xS := mathPkg.extractX xyzt
  let yS := mathPkg.extractY xyzt
  let zS := mathPkg.extractZ xyzt
  let zInv := mathPkg.inv zS
  let yAff := mathPkg.mul yS zInv
  let xAff := mathPkg.mul xS zInv
  mathPkg.pack yAff xAff

/-! ## §4  Main theorem: denote-level emit correctness

Given the leaf-spec bundle and an `RustExec` derivation of
`ed25519_compress_cmd`, the post-state's `out` slot equals
`compress_byte_spec mathPkg xyzt`. -/

/-- Names used inside `ed25519_compress_cmd`.  Pinned here as plain
    string equalities so the proof can `decide` the inequalities
    needed for `rsSetTower_other`. -/
private def names : List String :=
  ["xyzt", "out", "x_slot", "y_slot", "z_slot", "z_inv", "y_aff", "x_aff"]

/-- **Denote-level emit correctness (main theorem).**

After executing `ed25519_compress_cmd` from a state binding `xyzt` to a
200-byte value `vXYZT` and `out` to *some* 32-byte value (the call
overwrites it), and given that the leaf spec implements each of the
seven compress leaves per the math package, the final `out` slot equals
`compress_byte_spec mathPkg vXYZT`.

The proof follows the same modular pattern as
`Examples.EmittedASTCorrectness.montUToEdwardsBody_functional_correctness`:
peel the six `RLetZero` binders, peel the six `RSeq` nodes, then
dispatch each `RustExec.call` via `cases` and chain `argList` reductions
via the slot-binding hypotheses. -/
theorem compress_emit_denote_correct
    (N : Nat) (leafSpec : LeafSpec) (mathPkg : CompressMathPkg)
    (hLeaf : CompressLeafSpecCorrect leafSpec mathPkg)
    (rs rs' : RustState)
    (vXYZT : Slot200)
    (vOut0 : Slot32)
    (hXYZT : rs.rsTower "xyzt" = some ⟨TowerType.TBytes 200, vXYZT⟩)
    (hOut  : rs.rsTower "out"  = some ⟨TowerType.TBytes 32, vOut0⟩)
    (hExec : RustExec N leafSpec ed25519_compress_cmd rs rs') :
    rs'.rsTower "out" =
      some ⟨TowerType.TBytes 32, compress_byte_spec mathPkg vXYZT⟩ := by
  -- Peel the 6 letZero binders for x_slot, y_slot, z_slot, z_inv, y_aff, x_aff.
  unfold ed25519_compress_cmd at hExec
  -- Each letZero adds a default-valued slot.
  cases hExec with | letZero _ _ _ _ _ hE1 =>
  cases hE1   with | letZero _ _ _ _ _ hE2 =>
  cases hE2   with | letZero _ _ _ _ _ hE3 =>
  cases hE3   with | letZero _ _ _ _ _ hE4 =>
  cases hE4   with | letZero _ _ _ _ _ hE5 =>
  cases hE5   with | letZero _ _ _ _ _ hE6 =>
  -- After the 6 letZeros, the state is:
  --   xyzt ↦ vXYZT, out ↦ vOut0 (preserved)
  --   x_slot, y_slot, z_slot, z_inv, y_aff, x_aff ↦ default
  -- The remaining body is 6 RSeq's terminating in the final RCall.
  cases hE6 with | seq _ _ _ _ _ hC1 hR1 =>
  cases hR1 with | seq _ _ _ _ _ hC2 hR2 =>
  cases hR2 with | seq _ _ _ _ _ hC3 hR3 =>
  cases hR3 with | seq _ _ _ _ _ hC4 hR4 =>
  cases hR4 with | seq _ _ _ _ _ hC5 hR5 =>
  cases hR5 with | seq _ _ _ _ _ hC6 hC7 =>
  -- Set s := state after the 6 letZeros.
  set s0 := rsSetTower (rsSetTower (rsSetTower (rsSetTower (rsSetTower
              (rsSetTower rs "x_slot" ⟨TowerType.TBytes 40, default⟩)
              "y_slot" ⟨TowerType.TBytes 40, default⟩)
              "z_slot" ⟨TowerType.TBytes 40, default⟩)
              "z_inv" ⟨TowerType.TBytes 40, default⟩)
              "y_aff" ⟨TowerType.TBytes 40, default⟩)
              "x_aff" ⟨TowerType.TBytes 40, default⟩ with hs0_def
  -- Show xyzt is still bound to vXYZT in s0.
  have hxyzt_s0 : s0.rsTower "xyzt" = some ⟨TowerType.TBytes 200, vXYZT⟩ := by
    show (rsSetTower _ "x_aff" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "x_aff" "xyzt" _ (by decide)]
    show (rsSetTower _ "y_aff" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "y_aff" "xyzt" _ (by decide)]
    show (rsSetTower _ "z_inv" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "z_inv" "xyzt" _ (by decide)]
    show (rsSetTower _ "z_slot" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "z_slot" "xyzt" _ (by decide)]
    show (rsSetTower _ "y_slot" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "y_slot" "xyzt" _ (by decide)]
    show (rsSetTower _ "x_slot" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "x_slot" "xyzt" _ (by decide)]
    exact hXYZT
  -- Show out is still bound to vOut0 in s0.
  have hout_s0 : s0.rsTower "out" = some ⟨TowerType.TBytes 32, vOut0⟩ := by
    show (rsSetTower _ "x_aff" _).rsTower "out" = _
    rw [rsSetTower_other _ "x_aff" "out" _ (by decide)]
    show (rsSetTower _ "y_aff" _).rsTower "out" = _
    rw [rsSetTower_other _ "y_aff" "out" _ (by decide)]
    show (rsSetTower _ "z_inv" _).rsTower "out" = _
    rw [rsSetTower_other _ "z_inv" "out" _ (by decide)]
    show (rsSetTower _ "z_slot" _).rsTower "out" = _
    rw [rsSetTower_other _ "z_slot" "out" _ (by decide)]
    show (rsSetTower _ "y_slot" _).rsTower "out" = _
    rw [rsSetTower_other _ "y_slot" "out" _ (by decide)]
    show (rsSetTower _ "x_slot" _).rsTower "out" = _
    rw [rsSetTower_other _ "x_slot" "out" _ (by decide)]
    exact hOut
  -- ==================== Step 1: xyzt_slot_x (x_slot, [xyzt]) ====================
  cases hC1 with | call _ _ _ _ oldXV argList1 _hLook1 hArg1 _ =>
  have hArg1' : argList1 = [⟨TowerType.TBytes 200, vXYZT⟩] := by
    rw [hArg1]
    show ([{ locVar := "xyzt", locSrc := TowerType.TBytes 200 }] : List Located).filterMap
            (fun a => s0.rsTower a.locVar) = _
    simp only [List.filterMap, hxyzt_s0]
  set xLoc : Located := ⟨"x_slot", TowerType.TBytes 40⟩
  have hxs_call : leafSpec.call "xyzt_slot_x" (TowerType.TBytes 40)
                    [TowerType.TBytes 200] oldXV argList1 =
                  mathPkg.extractX vXYZT := by
    rw [hArg1']; exact hLeaf.xyztSlotX oldXV vXYZT
  set r1 := locatedUpdate s0 xLoc
    (leafSpec.call "xyzt_slot_x" (TowerType.TBytes 40)
      [TowerType.TBytes 200] oldXV argList1)
    with hr1
  have hxs1 : r1.rsTower "x_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractX vXYZT⟩ := by
    rw [hr1, locatedUpdate_dest, hxs_call]
  have hxyzt1 : r1.rsTower "xyzt" = some ⟨TowerType.TBytes 200, vXYZT⟩ := by
    rw [hr1]
    show (rsSetTower s0 "x_slot" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "x_slot" "xyzt" _ (by decide)]; exact hxyzt_s0
  have hout1 : r1.rsTower "out" = some ⟨TowerType.TBytes 32, vOut0⟩ := by
    rw [hr1]
    show (rsSetTower s0 "x_slot" _).rsTower "out" = _
    rw [rsSetTower_other _ "x_slot" "out" _ (by decide)]; exact hout_s0
  -- ==================== Step 2: xyzt_slot_y (y_slot, [xyzt]) ====================
  cases hC2 with | call _ _ _ _ oldYV argList2 _hLook2 hArg2 _ =>
  have hArg2' : argList2 = [⟨TowerType.TBytes 200, vXYZT⟩] := by
    rw [hArg2]
    show ([{ locVar := "xyzt", locSrc := TowerType.TBytes 200 }] : List Located).filterMap
            (fun a => r1.rsTower a.locVar) = _
    simp only [List.filterMap, hxyzt1]
  set yLoc : Located := ⟨"y_slot", TowerType.TBytes 40⟩
  have hys_call : leafSpec.call "xyzt_slot_y" (TowerType.TBytes 40)
                    [TowerType.TBytes 200] oldYV argList2 =
                  mathPkg.extractY vXYZT := by
    rw [hArg2']; exact hLeaf.xyztSlotY oldYV vXYZT
  set r2 := locatedUpdate r1 yLoc
    (leafSpec.call "xyzt_slot_y" (TowerType.TBytes 40)
      [TowerType.TBytes 200] oldYV argList2)
    with hr2
  have hys2 : r2.rsTower "y_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractY vXYZT⟩ := by
    rw [hr2, locatedUpdate_dest, hys_call]
  have hxs2 : r2.rsTower "x_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractX vXYZT⟩ := by
    rw [hr2]
    show (rsSetTower r1 "y_slot" _).rsTower "x_slot" = _
    rw [rsSetTower_other _ "y_slot" "x_slot" _ (by decide)]; exact hxs1
  have hxyzt2 : r2.rsTower "xyzt" = some ⟨TowerType.TBytes 200, vXYZT⟩ := by
    rw [hr2]
    show (rsSetTower r1 "y_slot" _).rsTower "xyzt" = _
    rw [rsSetTower_other _ "y_slot" "xyzt" _ (by decide)]; exact hxyzt1
  have hout2 : r2.rsTower "out" = some ⟨TowerType.TBytes 32, vOut0⟩ := by
    rw [hr2]
    show (rsSetTower r1 "y_slot" _).rsTower "out" = _
    rw [rsSetTower_other _ "y_slot" "out" _ (by decide)]; exact hout1
  -- ==================== Step 3: xyzt_slot_z (z_slot, [xyzt]) ====================
  cases hC3 with | call _ _ _ _ oldZV argList3 _hLook3 hArg3 _ =>
  have hArg3' : argList3 = [⟨TowerType.TBytes 200, vXYZT⟩] := by
    rw [hArg3]
    show ([{ locVar := "xyzt", locSrc := TowerType.TBytes 200 }] : List Located).filterMap
            (fun a => r2.rsTower a.locVar) = _
    simp only [List.filterMap, hxyzt2]
  set zLoc : Located := ⟨"z_slot", TowerType.TBytes 40⟩
  have hzs_call : leafSpec.call "xyzt_slot_z" (TowerType.TBytes 40)
                    [TowerType.TBytes 200] oldZV argList3 =
                  mathPkg.extractZ vXYZT := by
    rw [hArg3']; exact hLeaf.xyztSlotZ oldZV vXYZT
  set r3 := locatedUpdate r2 zLoc
    (leafSpec.call "xyzt_slot_z" (TowerType.TBytes 40)
      [TowerType.TBytes 200] oldZV argList3)
    with hr3
  have hzs3 : r3.rsTower "z_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractZ vXYZT⟩ := by
    rw [hr3, locatedUpdate_dest, hzs_call]
  have hys3 : r3.rsTower "y_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractY vXYZT⟩ := by
    rw [hr3]
    show (rsSetTower r2 "z_slot" _).rsTower "y_slot" = _
    rw [rsSetTower_other _ "z_slot" "y_slot" _ (by decide)]; exact hys2
  have hxs3 : r3.rsTower "x_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractX vXYZT⟩ := by
    rw [hr3]
    show (rsSetTower r2 "z_slot" _).rsTower "x_slot" = _
    rw [rsSetTower_other _ "z_slot" "x_slot" _ (by decide)]; exact hxs2
  have hout3 : r3.rsTower "out" = some ⟨TowerType.TBytes 32, vOut0⟩ := by
    rw [hr3]
    show (rsSetTower r2 "z_slot" _).rsTower "out" = _
    rw [rsSetTower_other _ "z_slot" "out" _ (by decide)]; exact hout2
  -- ==================== Step 4: fe25519_invert_slot (z_inv, [z_slot]) ============
  cases hC4 with | call _ _ _ _ oldIV argList4 _hLook4 hArg4 _ =>
  have hArg4' : argList4 = [⟨TowerType.TBytes 40, mathPkg.extractZ vXYZT⟩] := by
    rw [hArg4]
    show ([{ locVar := "z_slot", locSrc := TowerType.TBytes 40 }] : List Located).filterMap
            (fun a => r3.rsTower a.locVar) = _
    simp only [List.filterMap, hzs3]
  set iLoc : Located := ⟨"z_inv", TowerType.TBytes 40⟩
  have hzinv_call : leafSpec.call "fe25519_invert_slot" (TowerType.TBytes 40)
                      [TowerType.TBytes 40] oldIV argList4 =
                    mathPkg.inv (mathPkg.extractZ vXYZT) := by
    rw [hArg4']; exact hLeaf.invertSlot oldIV (mathPkg.extractZ vXYZT)
  set r4 := locatedUpdate r3 iLoc
    (leafSpec.call "fe25519_invert_slot" (TowerType.TBytes 40)
      [TowerType.TBytes 40] oldIV argList4)
    with hr4
  have hzi4 : r4.rsTower "z_inv" =
      some ⟨TowerType.TBytes 40, mathPkg.inv (mathPkg.extractZ vXYZT)⟩ := by
    rw [hr4, locatedUpdate_dest, hzinv_call]
  have hys4 : r4.rsTower "y_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractY vXYZT⟩ := by
    rw [hr4]
    show (rsSetTower r3 "z_inv" _).rsTower "y_slot" = _
    rw [rsSetTower_other _ "z_inv" "y_slot" _ (by decide)]; exact hys3
  have hxs4 : r4.rsTower "x_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractX vXYZT⟩ := by
    rw [hr4]
    show (rsSetTower r3 "z_inv" _).rsTower "x_slot" = _
    rw [rsSetTower_other _ "z_inv" "x_slot" _ (by decide)]; exact hxs3
  have hout4 : r4.rsTower "out" = some ⟨TowerType.TBytes 32, vOut0⟩ := by
    rw [hr4]
    show (rsSetTower r3 "z_inv" _).rsTower "out" = _
    rw [rsSetTower_other _ "z_inv" "out" _ (by decide)]; exact hout3
  -- ==================== Step 5: fe25519_mul_slot (y_aff, [y_slot, z_inv]) ========
  cases hC5 with | call _ _ _ _ oldYAV argList5 _hLook5 hArg5 _ =>
  have hArg5' : argList5 =
      [⟨TowerType.TBytes 40, mathPkg.extractY vXYZT⟩,
       ⟨TowerType.TBytes 40, mathPkg.inv (mathPkg.extractZ vXYZT)⟩] := by
    rw [hArg5]
    show ([{ locVar := "y_slot", locSrc := TowerType.TBytes 40 },
           { locVar := "z_inv",  locSrc := TowerType.TBytes 40 }] : List Located).filterMap
            (fun a => r4.rsTower a.locVar) = _
    simp only [List.filterMap, hys4, hzi4]
  set yaLoc : Located := ⟨"y_aff", TowerType.TBytes 40⟩
  have hya_call : leafSpec.call "fe25519_mul_slot" (TowerType.TBytes 40)
                    [TowerType.TBytes 40, TowerType.TBytes 40] oldYAV argList5 =
                  mathPkg.mul (mathPkg.extractY vXYZT)
                              (mathPkg.inv (mathPkg.extractZ vXYZT)) := by
    rw [hArg5']; exact hLeaf.mulSlot oldYAV _ _
  set r5 := locatedUpdate r4 yaLoc
    (leafSpec.call "fe25519_mul_slot" (TowerType.TBytes 40)
      [TowerType.TBytes 40, TowerType.TBytes 40] oldYAV argList5)
    with hr5
  have hya5 : r5.rsTower "y_aff" =
      some ⟨TowerType.TBytes 40,
            mathPkg.mul (mathPkg.extractY vXYZT)
                        (mathPkg.inv (mathPkg.extractZ vXYZT))⟩ := by
    rw [hr5, locatedUpdate_dest, hya_call]
  have hxs5 : r5.rsTower "x_slot" =
      some ⟨TowerType.TBytes 40, mathPkg.extractX vXYZT⟩ := by
    rw [hr5]
    show (rsSetTower r4 "y_aff" _).rsTower "x_slot" = _
    rw [rsSetTower_other _ "y_aff" "x_slot" _ (by decide)]; exact hxs4
  have hzi5 : r5.rsTower "z_inv" =
      some ⟨TowerType.TBytes 40, mathPkg.inv (mathPkg.extractZ vXYZT)⟩ := by
    rw [hr5]
    show (rsSetTower r4 "y_aff" _).rsTower "z_inv" = _
    rw [rsSetTower_other _ "y_aff" "z_inv" _ (by decide)]; exact hzi4
  have hout5 : r5.rsTower "out" = some ⟨TowerType.TBytes 32, vOut0⟩ := by
    rw [hr5]
    show (rsSetTower r4 "y_aff" _).rsTower "out" = _
    rw [rsSetTower_other _ "y_aff" "out" _ (by decide)]; exact hout4
  -- ==================== Step 6: fe25519_mul_slot (x_aff, [x_slot, z_inv]) ========
  cases hC6 with | call _ _ _ _ oldXAV argList6 _hLook6 hArg6 _ =>
  have hArg6' : argList6 =
      [⟨TowerType.TBytes 40, mathPkg.extractX vXYZT⟩,
       ⟨TowerType.TBytes 40, mathPkg.inv (mathPkg.extractZ vXYZT)⟩] := by
    rw [hArg6]
    show ([{ locVar := "x_slot", locSrc := TowerType.TBytes 40 },
           { locVar := "z_inv",  locSrc := TowerType.TBytes 40 }] : List Located).filterMap
            (fun a => r5.rsTower a.locVar) = _
    simp only [List.filterMap, hxs5, hzi5]
  set xaLoc : Located := ⟨"x_aff", TowerType.TBytes 40⟩
  have hxa_call : leafSpec.call "fe25519_mul_slot" (TowerType.TBytes 40)
                    [TowerType.TBytes 40, TowerType.TBytes 40] oldXAV argList6 =
                  mathPkg.mul (mathPkg.extractX vXYZT)
                              (mathPkg.inv (mathPkg.extractZ vXYZT)) := by
    rw [hArg6']; exact hLeaf.mulSlot oldXAV _ _
  set r6 := locatedUpdate r5 xaLoc
    (leafSpec.call "fe25519_mul_slot" (TowerType.TBytes 40)
      [TowerType.TBytes 40, TowerType.TBytes 40] oldXAV argList6)
    with hr6
  have hxa6 : r6.rsTower "x_aff" =
      some ⟨TowerType.TBytes 40,
            mathPkg.mul (mathPkg.extractX vXYZT)
                        (mathPkg.inv (mathPkg.extractZ vXYZT))⟩ := by
    rw [hr6, locatedUpdate_dest, hxa_call]
  have hya6 : r6.rsTower "y_aff" =
      some ⟨TowerType.TBytes 40,
            mathPkg.mul (mathPkg.extractY vXYZT)
                        (mathPkg.inv (mathPkg.extractZ vXYZT))⟩ := by
    rw [hr6]
    show (rsSetTower r5 "x_aff" _).rsTower "y_aff" = _
    rw [rsSetTower_other _ "x_aff" "y_aff" _ (by decide)]; exact hya5
  have hout6 : r6.rsTower "out" = some ⟨TowerType.TBytes 32, vOut0⟩ := by
    rw [hr6]
    show (rsSetTower r5 "x_aff" _).rsTower "out" = _
    rw [rsSetTower_other _ "x_aff" "out" _ (by decide)]; exact hout5
  -- ==================== Step 7: fe25519_pack_sign (out, [y_aff, x_aff]) ========
  cases hC7 with | call _ _ _ _ oldOutV argList7 _hLook7 hArg7 _ =>
  have hArg7' : argList7 =
      [⟨TowerType.TBytes 40,
        mathPkg.mul (mathPkg.extractY vXYZT)
                    (mathPkg.inv (mathPkg.extractZ vXYZT))⟩,
       ⟨TowerType.TBytes 40,
        mathPkg.mul (mathPkg.extractX vXYZT)
                    (mathPkg.inv (mathPkg.extractZ vXYZT))⟩] := by
    rw [hArg7]
    show ([{ locVar := "y_aff", locSrc := TowerType.TBytes 40 },
           { locVar := "x_aff", locSrc := TowerType.TBytes 40 }] : List Located).filterMap
            (fun a => r6.rsTower a.locVar) = _
    simp only [List.filterMap, hya6, hxa6]
  have hpack_call : leafSpec.call "fe25519_pack_sign" (TowerType.TBytes 32)
                      [TowerType.TBytes 40, TowerType.TBytes 40] oldOutV argList7 =
                    mathPkg.pack
                      (mathPkg.mul (mathPkg.extractY vXYZT)
                                   (mathPkg.inv (mathPkg.extractZ vXYZT)))
                      (mathPkg.mul (mathPkg.extractX vXYZT)
                                   (mathPkg.inv (mathPkg.extractZ vXYZT))) := by
    rw [hArg7']; exact hLeaf.packSign oldOutV _ _
  -- Final state: locatedUpdate r6 (out-loc) (leafSpec.call "fe25519_pack_sign" ...)
  -- The goal is: rs'.rsTower "out" = some ⟨TBytes 32, compress_byte_spec mathPkg vXYZT⟩.
  -- Unfold the private `L`/`ξ_*` aliases so the destination's locVar/locDst
  -- and args' locDst reduce to plain values; then `locatedUpdate_dest` applies.
  show (locatedUpdate r6
      ({ locVar := "out", locSrc := TowerType.TBytes 32 } : Located) _).rsTower _ = _
  rw [locatedUpdate_dest]
  -- Now goal: some ⟨TBytes 32, leafSpec.call "fe25519_pack_sign" ... ⟩
  --        = some ⟨TBytes 32, compress_byte_spec mathPkg vXYZT⟩.
  -- After `rfl`-reducing the args/dest projections, the call argument-types
  -- match `[TowerType.TBytes 40, TowerType.TBytes 40]` and we can apply
  -- `hpack_call`.
  show some
      (⟨TowerType.TBytes 32,
        leafSpec.call "fe25519_pack_sign" (TowerType.TBytes 32)
          [TowerType.TBytes 40, TowerType.TBytes 40] oldOutV argList7⟩ :
        Σ t : TowerType, RustVal t) =
       some ⟨TowerType.TBytes 32, compress_byte_spec mathPkg vXYZT⟩
  rw [hpack_call]
  -- Both sides are some ⟨TBytes 32, mathPkg.pack ... ⟩; unfold to close.
  simp [compress_byte_spec]

/-! ## §5  Smoke test

We verify the existence of a `CompressMathPkg` for which everything
unfolds correctly: the trivial "default" math package returns the
default byte arrays for every operation.  The leaf spec must then
return those defaults too.  This is a tiny self-consistency check that
the bundle and the byte-spec are well-formed. -/

/-- Trivial math package: every op returns `default`.  This is only
    useful as a smoke test that the spec compiles. -/
def trivialMathPkg : CompressMathPkg where
  extractX := fun _ => default
  extractY := fun _ => default
  extractZ := fun _ => default
  inv      := fun _ => default
  mul      := fun _ _ => default
  pack     := fun _ _ => default

/-- `compress_byte_spec trivialMathPkg` always returns the default
    32-byte array. -/
example (xyzt : Slot200) :
    compress_byte_spec trivialMathPkg xyzt = (default : Slot32) := rfl

/-- A `LeafSpec` whose `call` returns `default` is compress-correct for
    `trivialMathPkg`. -/
def trivialLeafSpec : LeafSpec :=
  { call := fun _ _ _ _ _ => default
    limbStore := fun _ oldV _ _ => oldV }

/-- The trivial leaf-spec satisfies the compress bundle for the trivial
    math package. -/
example : CompressLeafSpecCorrect trivialLeafSpec trivialMathPkg :=
  { xyztSlotX := fun _ _ => rfl
    xyztSlotY := fun _ _ => rfl
    xyztSlotZ := fun _ _ => rfl
    invertSlot := fun _ _ => rfl
    mulSlot := fun _ _ _ => rfl
    packSign := fun _ _ _ => rfl }

end CatCrypt.Crypto.Jasmin.Ed25519.CompressEmitDenoteCorrect
