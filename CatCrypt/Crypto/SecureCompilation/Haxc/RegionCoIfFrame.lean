/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete

@[expose] public section

set_option autoImplicit false

/-!
# The arm-end guard of a conditional frame on the export image

The then-arm of `ExportRegions.ifFrame` ends with `movImmI r 1` followed by the loop guard
`I.loopGuard r (n + 2)` of the instruction set, a conditional jump to the join label that
every run takes. At `x86Data` the three instructions are `MOV r, #1; CMP r, #0; Lcond NZ`,
which `ConstGuard.constTakenB` recognises. This module states the recognition on the export
image and its consequence for the least liveness `PLive` of the coalescing check: at the
guard, the names live are those live one past the join label, so a name that only the
else-arm reads is not live at the end of the then-arm.

## Main definitions

* `GuardsTaken`: the arm-end guard of an instruction set is recognised as constant-taken in
  every context.

## Main results

* `x86Data_guardsTaken`: the x86 arm-end guard is recognised.
* `ifFrame_constTaken`: in a code containing an `ifFrame`, the guard at the end of the
  then-arm is constant-taken.
* `pLive_constTaken`: a name `PLive` at a constant-taken guard is `PLive` one past the label
  of its jump.
* `pLive_ifFrame_guard_x86`: at the end of the then-arm of an `ifFrame` at `x86Data`, a name
  `PLive` at the guard is `PLive` one past the join label.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoIfFrame

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data x86Data_loopGuard)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete (armOf_cond)

/-! ## 1. The guard is recognised -/

/-- **The arm-end guard of the instruction set `I` is constant-taken**: in every code
    `pre ++ movImmI r 1 :: (I.loopGuard r l).map guardI ++ post`, the last instruction of the
    loop guard is a constant-taken guard. -/
def GuardsTaken (I : IsaData) : Prop :=
  ∀ (pre post : List LinstrRM) (r : String) (l : LLabel),
    constTakenB (pre ++ (movImmI r 1 :: (I.loopGuard r l).map guardI ++ post))
      (pre.length + (I.loopGuard r l).length) = true

/-- **The x86 arm-end guard is recognised**: `MOV r, #1; CMP r, #0; Lcond NZ` jumps on every
    run, since `1 ≠ 0` at 64 bits and `jne` jumps when the zero flag is clear. -/
theorem x86Data_guardsTaken : GuardsTaken x86Data := by
  intro pre post r l
  rw [x86Data_loopGuard]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [constTakenB, constGuard?]
  simp [guardMovImm?, movImmI, movI, guardI, cmpArgs?, flagCondCC?]

/-- The code of a conditional frame in context, split before the move that ends its
    then-arm. -/
theorem ifFrame_split {I : IsaData} (fn : String) (d n : Nat) (rs : List JasminTy)
    (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat) (pre post : List LinstrRM) :
    pre ++ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD I ++ post
      = (pre ++ flagWord I (regName d) (regName (d + 1)) condOp
          ++ (I.zeroTripGuard (regName d) n (n + 1)).map guardI ++ labelI n :: thnC
          ++ ifResMoves rs d (thnD + rs.length) thnOps)
        ++ (movImmI (regName (d + rs.length)) 1
          :: (I.loopGuard (regName (d + rs.length)) (n + 2)).map guardI
          ++ (labelI (n + 1) :: (elsC ++ (ifResMoves rs d (elsD + rs.length) elsOps
            ++ [labelI (n + 2)])) ++ post)) := by
  simp [ifFrame]

/-- **The arm-end guard of a conditional frame is constant-taken.** In the code
    `pre ++ ifFrame … ++ post`, the instruction ending the then-arm, at the position after
    `pre`, the widening of the condition, the zero-trip guard, the then label, the then-arm,
    its result moves and the loop guard less one, is a constant-taken guard. -/
theorem ifFrame_constTaken {I : IsaData} (hI : GuardsTaken I) (fn : String) (d n : Nat)
    (rs : List JasminTy) (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand)
    (thnD : Nat) (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (pre post : List LinstrRM) :
    constTakenB (pre ++ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD I ++ post)
      (pre.length + (flagWord I (regName d) (regName (d + 1)) condOp).length
        + (I.zeroTripGuard (regName d) n (n + 1)).length + 1 + thnC.length
        + (ifResMoves rs d (thnD + rs.length) thnOps).length
        + (I.loopGuard (regName (d + rs.length)) (n + 2)).length) = true := by
  have h := hI (pre ++ flagWord I (regName d) (regName (d + 1)) condOp
      ++ (I.zeroTripGuard (regName d) n (n + 1)).map guardI ++ labelI n :: thnC
      ++ ifResMoves rs d (thnD + rs.length) thnOps)
    (labelI (n + 1) :: (elsC ++ (ifResMoves rs d (elsD + rs.length) elsOps
      ++ [labelI (n + 2)])) ++ post)
    (regName (d + rs.length)) (n + 2)
  rw [ifFrame_split]
  convert h using 2
  simp only [List.length_append, List.length_map, List.length_cons]
  omega

/-! ## 2. Liveness across a constant-taken guard -/

/-- **A constant-taken guard passes on the names live after its label**: a name `PLive` at
    a constant-taken guard whose arm jumps to `lbl` is `PLive` one past the position of the
    label. -/
theorem pLive_constTaken {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {obs : List String} {k : Nat} {i : LinstrRM} {lbl : LLabel}
    {r : String} (hi : body[k]? = some i) (harm : armOf i = .cc lbl)
    (ht : constTakenB body k = true) (h : PLive body aa ao obs k r) :
    ∃ p, findLabelMem lbl body = some p ∧ PLive body aa ao obs (p + 1) r := by
  cases h with
  | obs _ =>
      have := (List.getElem?_eq_some_iff.mp hi).1
      omega
  | read hi' hr =>
      rw [hi] at hi'
      cases hi'
      simp [rdArr, harm, rdArrA] at hr
  | step hi' hs _ hr =>
      rw [hi] at hi'
      cases hi'
      unfold Succ at hs
      rw [harm] at hs
      rcases hs with ⟨-, hf⟩ | ⟨p, hp, rfl⟩
      · rw [ht] at hf
        cases hf
      · exact ⟨p, hp, hr⟩

/-- **The end of the then-arm at x86.** In the code `pre ++ ifFrame … x86Data ++ post`, a
    name `PLive` at the instruction ending the then-arm is `PLive` one past the join label
    `n + 2`: the fall-through into the else-arm is no edge of the liveness. -/
theorem pLive_ifFrame_guard_x86 (fn : String) (d n : Nat) (rs : List JasminTy)
    (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat) (pre post : List LinstrRM)
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {obs : List String}
    {r : String}
    (h : PLive (pre ++ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data
        ++ post) aa ao obs
      (pre.length + (flagWord x86Data (regName d) (regName (d + 1)) condOp).length
        + (x86Data.zeroTripGuard (regName d) n (n + 1)).length + 1 + thnC.length
        + (ifResMoves rs d (thnD + rs.length) thnOps).length + 2) r) :
    ∃ p, findLabelMem (n + 2)
        (pre ++ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data ++ post)
          = some p
      ∧ PLive (pre ++ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data
          ++ post) aa ao obs (p + 1) r := by
  have ht := ifFrame_constTaken x86Data_guardsTaken fn d n rs condOp thnC thnOps thnD elsC
    elsOps elsD pre post
  rw [x86Data_loopGuard] at ht
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at ht
  refine pLive_constTaken ?_ (armOf_cond (.reg "NZ") (n + 2) (.reg none)) ht h
  rw [ifFrame_split, x86Data_loopGuard]
  have e : ∀ (X Q : List LinstrRM) (m : LinstrRM) (a b : LinstrR),
      (X ++ (m :: [a, b].map guardI ++ Q))[X.length + 2]? = some (guardI b) := by
    intro X Q m a b
    simp
  convert e _ _ _ _ _ using 2
  all_goals first
    | rfl
    | (simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
       omega)

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoIfFrame
