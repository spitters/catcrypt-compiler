/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoopsJ

@[expose] public section

set_option autoImplicit false

/-!
# Lifting the carried-register loop nodes to the typed instruction list `LinstrRM`

The loop nodes `ComLJ.forLoopRegs` and `ComLJ.whileRegs` export to the untyped `Lcmd`
streams `forLoopRegsLcmd` and `whileRegsLcmd`. The flag machine `lsemFuelMemF` runs typed
`LinstrRM` lists. This module gives the typed images of the two nodes, in the shape the flag
machine's loop theorems consume, and their wire ties.

* `loopBodyWalkRM` — the typed body walk of `loopBodyWalkR`: each binding is the
  `opToLinstrR` wire paired with `memTagOfOp` of its op.
* `regsSeedsRM`, `regsFeedbackRM` — the seed moves of the carried registers and the staged
  parallel feedback, lifted with the register descriptor.
* `forLoopRegsRM` — the counted node: the carried seeds, the index and counter seeds, then
  the zero-trip guarded flag loop `guardedFlagLoopLinstrRM` over the walk, the feedback,
  the index and counter updates and the invariant touches.
* `whileRegsRM` — the do-while node: the carried seeds, then the flag loop
  `flagLoopLinstrRM` on the materialised continue-bit register over the walk, the
  feedback, the bit materialisation and the invariant touches.

## Main results

* `loopBodyWalkRM_wire` — the wire of the typed walk is the walk's instruction stream.
* `forLoopRegsRM_wire` — the wire of `forLoopRegsRM` is `forLoopRegsLcmd`.
* `whileRegsRM_wire` — the wire of `whileRegsRM` is `whileRegsLcmd`.
* `forLoopRegsBodyRM_isLopn`, `whileRegsBodyRM_isLopn` — every instruction of a looped
  segment is an `Lopn`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLiftJ

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift

/-! ## 1. The typed body walk -/

/-- The typed body walk of a carried-register loop body: the wire of `loopBodyWalkR` with
    each binding tagged by `memTagOfOp`. -/
def loopBodyWalkRM (d base nCar : Nat) (idx : Option String) (invOps : List LOperand) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    MultiReturnCom jasminDialect Γ ts → (curDepth : Nat) → List LinstrRM
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      (opToLinstrR e.op (loopReg d curDepth)
          (loopVarsR d base nCar idx invOps curDepth e.args), memTagOfOp e.op)
        :: loopBodyWalkRM d base nCar idx invOps body (curDepth + 1)

/-- **Wire tie of the typed walk.** -/
theorem loopBodyWalkRM_wire (d base nCar : Nat) (idx : Option String)
    (invOps : List LOperand) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (com : MultiReturnCom jasminDialect Γ ts) (curDepth : Nat) :
    (loopBodyWalkRM d base nCar idx invOps com curDepth).map Prod.fst
      = (loopBodyWalkR d base nCar idx invOps com curDepth).1.map Linstr.li_i := by
  induction com generalizing curDepth with
  | ret vs => rfl
  | var e body ih =>
      simp only [loopBodyWalkRM, loopBodyWalkR, List.map_cons, ih]

/-- Every instruction of the typed walk is an `Lopn`. -/
theorem loopBodyWalkRM_isLopn (d base nCar : Nat) (idx : Option String)
    (invOps : List LOperand) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (com : MultiReturnCom jasminDialect Γ ts) (curDepth : Nat) :
    ∀ i ∈ loopBodyWalkRM d base nCar idx invOps com curDepth, IsLopn i := by
  induction com generalizing curDepth with
  | ret vs => intro i hi; simp [loopBodyWalkRM] at hi
  | var e body ih =>
      intro i hi
      simp only [loopBodyWalkRM, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact opToLinstrR_isLopn _ _ _ _
      · exact ih (curDepth + 1) i hi

/-! ## 2. Seeds and feedback -/

/-- The seed moves `MOV c_j, init_j` of the carried registers, one per entry of `accs`
    (register, seed operand, returned operand). -/
def regsSeedsRM (accs : List (String × LOperand × LOperand)) : List LinstrRM :=
  accs.map fun a => (.Lopn [.reg a.1] (withWidthTag 64 "MOV") [a.2.1], MemTag.reg none)

/-- The staged parallel feedback of `regsLoopFrame` lifted with the register descriptor:
    the staging copies of `feedbackStage` followed by `feedbackMoves`. -/
def regsFeedbackRM (d tmp0 : Nat) (targets : List String) (srcs : List LOperand) :
    List LinstrRM :=
  liftLcmdRM regTag ((feedbackStage d tmp0 targets srcs 0).1
    ++ feedbackMoves targets (feedbackStage d tmp0 targets srcs 0).2)

/-- The staging copies are `MOV`s into a register. -/
theorem feedbackStage_fst_mov (d tmp0 : Nat) (targets : List String) :
    ∀ (srcs : List LOperand) (i : Nat), ∀ l ∈ (feedbackStage d tmp0 targets srcs i).1,
      ∃ r x, l.li_i = .Lopn [.reg r] (withWidthTag 64 "MOV") [.reg x]
  | [], _, l, hl => by simp [feedbackStage] at hl
  | op :: ops, i, l, hl => by
      simp only [feedbackStage] at hl
      split at hl
      · split at hl
        · rcases List.mem_cons.mp hl with rfl | hl
          · exact ⟨_, _, rfl⟩
          · exact feedbackStage_fst_mov d tmp0 targets ops (i + 1) l hl
        · exact feedbackStage_fst_mov d tmp0 targets ops (i + 1) l hl
      · exact feedbackStage_fst_mov d tmp0 targets ops (i + 1) l hl

/-- The final feedback moves are `MOV`s into a register. -/
theorem feedbackMoves_mov : ∀ (targets : List String) (srcs : List LOperand),
    ∀ l ∈ feedbackMoves targets srcs,
      ∃ r s, l.li_i = .Lopn [.reg r] (withWidthTag 64 "MOV") [s]
  | [], _, l, hl => by simp [feedbackMoves] at hl
  | _ :: _, [], l, hl => by simp [feedbackMoves] at hl
  | t :: ts, s :: ss, l, hl => by
      simp only [feedbackMoves] at hl
      split at hl
      · split at hl
        · exact feedbackMoves_mov ts ss l hl
        · rcases List.mem_cons.mp hl with rfl | hl
          · exact ⟨_, _, rfl⟩
          · exact feedbackMoves_mov ts ss l hl
      · rcases List.mem_cons.mp hl with rfl | hl
        · exact ⟨_, _, rfl⟩
        · exact feedbackMoves_mov ts ss l hl

/-- Every instruction of the lifted feedback is an `Lopn`. -/
theorem regsFeedbackRM_isLopn (d tmp0 : Nat) (targets : List String)
    (srcs : List LOperand) : ∀ i ∈ regsFeedbackRM d tmp0 targets srcs, IsLopn i := by
  intro i hi
  simp only [regsFeedbackRM, liftLcmdRM, List.mem_map, List.mem_append] at hi
  obtain ⟨l, hl, rfl⟩ := hi
  rcases hl with hl | hl
  · obtain ⟨r, x, h⟩ := feedbackStage_fst_mov d tmp0 targets srcs 0 l hl
    exact liftLinstrRM_isLopn _ _ ⟨_, _, _, h⟩
  · obtain ⟨r, s, h⟩ := feedbackMoves_mov targets _ l hl
    exact liftLinstrRM_isLopn _ _ ⟨_, _, _, h⟩

/-! ## 3. The counted node -/

/-- The carried-register entries `(register, seed, returned operand)` of a counted node at
    depth `d`, as `forLoopRegsLcmd` zips them. -/
def forAccs (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) : List (String × LOperand × LOperand) :=
  (carriedRegs d cs.length).zip (initOps.zip
    (loopBodyWalkR d d cs.length (some (loopIdx d)) invOps update
      (invTys.length + 1 + cs.length)).2.1)

/-- The first body temporary above the walk's own, at a counted node. -/
def forTmp0 (d : Nat) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) : Nat :=
  (loopBodyWalkR d d cs.length (some (loopIdx d)) invOps update
    (invTys.length + 1 + cs.length)).2.2

/-- The looped segment of a counted node: the typed walk, the feedback, the index and
    counter updates and the invariant touches. -/
def forLoopRegsBodyRM (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) : List LinstrRM :=
  loopBodyWalkRM d d cs.length (some (loopIdx d)) invOps update
      (invTys.length + 1 + cs.length)
    ++ regsFeedbackRM d (forTmp0 d update invOps)
        ((forAccs d initOps update invOps).map (·.1))
        ((forAccs d initOps update invOps).map (·.2.2))
    ++ loopAdvanceRM d
    ++ loopTouchRM d (invRegsOf invOps)

/-- The seed moves of a counted node: the carried registers, the index and the counter. -/
def forSeedsRM (d : Nat) (initOps : List LOperand) (countOp : LOperand)
    {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) : List LinstrRM :=
  regsSeedsRM (forAccs d initOps update invOps)
    ++ [ (.Lopn [.reg (loopIdx d)] (withWidthTag 64 "MOV") [.imm 0], MemTag.reg none)
       , (.Lopn [.reg (loopCtr d)] (withWidthTag 64 "MOV") [countOp], MemTag.reg none) ]

/-- **The typed image of the counted carried-register node**: the seed moves, then the
    zero-trip guarded flag loop (top label `d`, skip label `d + 0x40000000`, counter
    `Lctr<d>`) over the looped segment. -/
def forLoopRegsRM (d : Nat) (initOps : List LOperand) (countOp : LOperand)
    {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) : List LinstrRM :=
  forSeedsRM d initOps countOp update invOps
    ++ guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d)
        (forLoopRegsBodyRM d initOps update invOps)

/-- **Wire tie of the counted node.** The wire projection of `forLoopRegsRM` is the
    instruction stream of the export's `forLoopRegsLcmd`. -/
theorem forLoopRegsRM_wire (d : Nat) (initOps : List LOperand) (countOp : LOperand)
    {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) :
    (forLoopRegsRM d initOps countOp update invOps).map Prod.fst
      = (forLoopRegsLcmd d initOps countOp update invOps).map Linstr.li_i := by
  unfold forLoopRegsRM forSeedsRM forLoopRegsBodyRM guardedFlagLoopLinstrRM flagLoopLinstrRM
    flagBackedge regsSeedsRM regsFeedbackRM loopAdvanceRM loopTouchRM forLoopRegsLcmd
    regsLoopFrame forAccs forTmp0 invRegsOf
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, loopBodyWalkRM_wire,
    liftLcmdRM_wire, List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- Every instruction of the counted looped segment is an `Lopn`. -/
theorem forLoopRegsBodyRM_isLopn (d : Nat) (initOps : List LOperand)
    {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) :
    ∀ i ∈ forLoopRegsBodyRM d initOps update invOps, IsLopn i := by
  intro i hi
  simp only [forLoopRegsBodyRM, List.mem_append] at hi
  rcases hi with ((hi | hi) | hi) | hi
  · exact loopBodyWalkRM_isLopn _ _ _ _ _ _ _ i hi
  · exact regsFeedbackRM_isLopn _ _ _ _ i hi
  · simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩

/-! ## 4. The do-while node -/

/-- The body walk of a do-while node at depth `d`. -/
abbrev whileWalk (d : Nat) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : Lcmd × List LOperand × Nat :=
  loopBodyWalkR d d cs.length none invOps update (invTys.length + cs.length)

/-- The carried-register entries of a do-while node, as `whileRegsLcmd` zips them. -/
def whileAccs (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : List (String × LOperand × LOperand) :=
  (carriedRegs d cs.length).zip (initOps.zip (whileWalk d update invOps).2.1.tail)

/-- The continue-bit operand the do-while body returns. -/
def whileFlagOp (d : Nat) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : LOperand :=
  (whileWalk d update invOps).2.1.headD (.imm 0)

/-- The staging of a do-while node's feedback, with the bit staged after the tuple. -/
def whileStage (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : Lcmd × List LOperand :=
  feedbackStage d (whileWalk d update invOps).2.2
    ((whileAccs d initOps update invOps).map (·.1))
    ((whileAccs d initOps update invOps).map (·.2.2) ++ [whileFlagOp d update invOps]) 0

/-- The register holding the continue bit at the bottom test, and its materialisation. -/
def whileFlagMat (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : String × Lcmd :=
  match (whileStage d initOps update invOps).2.getD
      (whileAccs d initOps update invOps).length (whileFlagOp d update invOps) with
  | .reg r => (r, [])
  | op =>
      let r := loopReg d ((whileWalk d update invOps).2.2
        + (whileAccs d initOps update invOps).length + 1)
      (r, [⟨0, .Lopn [.reg r] (withWidthTag 64 "MOV") [op]⟩])

/-- The looped segment of a do-while node: the typed walk, the feedback, the bit
    materialisation and the invariant touches. -/
def whileRegsBodyRM (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : List LinstrRM :=
  loopBodyWalkRM d d cs.length none invOps update (invTys.length + cs.length)
    ++ liftLcmdRM regTag ((whileStage d initOps update invOps).1
        ++ feedbackMoves ((whileAccs d initOps update invOps).map (·.1))
            (whileStage d initOps update invOps).2)
    ++ liftLcmdRM regTag (whileFlagMat d initOps update invOps).2
    ++ (invRegsOf invOps).map (fun r =>
        (.Lopn [.reg (whileFlagMat d initOps update invOps).1] (withWidthTag 64 "CMP")
          [.reg (whileFlagMat d initOps update invOps).1, .reg r], MemTag.reg none))

/-- **The typed image of the do-while carried-register node**: the carried seeds, then the
    flag loop at the top label `d` on the continue-bit register over the looped segment. -/
def whileRegsRM (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : List LinstrRM :=
  regsSeedsRM (whileAccs d initOps update invOps)
    ++ flagLoopLinstrRM d (whileFlagMat d initOps update invOps).1
        (whileRegsBodyRM d initOps update invOps)

/-- **Wire tie of the do-while node.** The wire projection of `whileRegsRM` is the
    instruction stream of the export's `whileRegsLcmd`. -/
theorem whileRegsRM_wire (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) :
    (whileRegsRM d initOps update invOps).map Prod.fst
      = (whileRegsLcmd d initOps update invOps).map Linstr.li_i := by
  cases h : (whileStage d initOps update invOps).2.getD
      (whileAccs d initOps update invOps).length (whileFlagOp d update invOps) <;>
  unfold whileStage whileAccs whileFlagOp whileWalk at h <;>
  unfold whileRegsRM whileRegsBodyRM flagLoopLinstrRM flagBackedge regsSeedsRM
    whileRegsLcmd whileRegsFrame whileFlagMat whileStage whileAccs whileFlagOp whileWalk
    invRegsOf <;>
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, loopBodyWalkRM_wire,
    liftLcmdRM_wire, List.append_assoc, List.cons_append, List.nil_append, h] <;>
  rfl

/-- Every instruction of the do-while looped segment is an `Lopn`. -/
theorem whileRegsBodyRM_isLopn (d : Nat) (initOps : List LOperand)
    {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) :
    ∀ i ∈ whileRegsBodyRM d initOps update invOps, IsLopn i := by
  intro i hi
  simp only [whileRegsBodyRM, List.mem_append] at hi
  rcases hi with ((hi | hi) | hi) | hi
  · exact loopBodyWalkRM_isLopn _ _ _ _ _ _ _ i hi
  · simp only [liftLcmdRM, List.mem_map, List.mem_append] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rcases hl with hl | hl
    · obtain ⟨r, x, h⟩ := feedbackStage_fst_mov _ _ _ _ 0 l hl
      exact liftLinstrRM_isLopn _ _ ⟨_, _, _, h⟩
    · obtain ⟨r, s, h⟩ := feedbackMoves_mov _ _ l hl
      exact liftLinstrRM_isLopn _ _ ⟨_, _, _, h⟩
  · simp only [liftLcmdRM, List.mem_map] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    unfold whileFlagMat at hl
    split at hl
    · simp at hl
    · simp only [List.mem_singleton] at hl
      subst hl
      exact ⟨_, _, _, rfl⟩
  · simp only [List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLiftJ
