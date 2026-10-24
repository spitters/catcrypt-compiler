/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Loop-invariant code motion on the `Lprog` labeled semantics — milestone 1

Loop-invariant code motion (LICM) hoists a computation whose inputs do not change
across a loop out of the loop body into a preheader, so it runs once rather than
once per iteration. This module is the first milestone: hoisting a single
register/immediate `Lopn` whose destination and sources are all defined outside
the loop body (no cross-iteration dependency), over the labeled,
program-counter-indexed linear semantics `JasminLsemLabeled.lsem`.

The module reuses the optimization-pipeline foundation
(`LprogOptPipeline`): the labeled semantics `LstateP`/`lsemStep`/`lsemStraight`,
the store image `stateStore`, the operand-stability tools `evalOperand_congr` and
`lsemStraight_stateStore`, and the control-flow-graph simulation machinery
(`Sim`, `mapBodies`, `runForward`, `fuelRun`, `jumpSim`, `LabelPres`).

## Contents

* **The invariance criterion.** `instrWrites`/`operandReads` describe which
  registers a modeled instruction writes and an operand reads; `isMemOpn`
  recognises the two runtime-indexed memory opcodes; `bodyDefs` and
  `isLoopInvariant` are the syntactic criterion.
* **Operand stability (the reusable core).** `evalOperand_stable`: an operand
  whose registers are never written in a straight-line run of non-memory
  instructions evaluates identically at the run's start and end.
  `invariant_value_stable` and `invariant_value_stable_of_criterion` lift this to
  the value an invariant `Lopn` computes: it is unchanged across any such sub-run
  of the loop body.
* **The hoisting transform.** `hoistOne` inserts the invariant instruction into a
  preheader before the loop label and deletes it from the loop; `hoistOne_decomp`
  characterizes it on the loop shape, and `hoistOne_perm` shows it neither adds
  nor drops an instruction.
* **The loop shapes.** `IsHoistableLoop` and its strengthening
  `IsHoistableLoopStrong` name the do-while loop shape and the extra read-of-`d`
  soundness condition; `hoistOne_hoistable_eq`/`hoistOne_hoistable_perm` are the
  syntactic reductions on them.
* **The sound target.** `IsHoistableDoWhile` is the do-while shape whose loop
  body and surroundings are straight-line, so the function's only label is the
  loop header and its only branch is the back-edge. `LICMEntryStorePreservedGoalSL`
  is the entry-point store-preservation theorem over it (the shape of
  `mapBodies_entry_store_preserved` with `optimizeBasicBlocks` replaced by
  `hoistOne L i`), over a function body free of runtime-indexed memory ops, proved
  by the one-instruction-offset forward simulation `licm_loop`. Store
  preservation over the weaker `IsHoistableLoop` and
  `IsHoistableLoopStrong` shapes is refutable — the loop-body prefix may read `d`,
  or the body may leave the loop before `i` runs — so only the do-while shape
  carries a theorem.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLICM

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust (stateStore)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (mapBodies)

/-! ## 1. The invariance criterion at the `Linstr` / `LstateP` level -/

/-- The single destination register an instruction writes. Only the modeled
    single-register `Lopn` writes a register; every other step advances the
    program counter without touching the register map. -/
def instrWrites (i : LinstrR) (r : String) : Bool :=
  match i with
  | .Lopn [.reg d] _ _ => d == r
  | _ => false

/-- The registers an operand reads: the named register for `.reg`, the SIB index
    register for `.arrIdx`, and none for an immediate or a constant-offset array
    element (which reads memory only). -/
def operandReads : LOperand → List String
  | .reg r => [r]
  | .imm _ => []
  | .arr _ _ => []
  | .arrIdx _ idx _ => [idx]

/-- An operand is a register or an immediate (no memory operand). -/
def isRegOrImm : LOperand → Bool
  | .reg _ => true
  | .imm _ => true
  | _ => false

/-- The instruction is an `Lopn` carrying one of the two runtime-indexed memory
    opcodes, `LOADIDX` or `STOREIDX`. `lsemStep` intercepts both ahead of its
    word-op arm: `LOADIDX` reads the indexed cell into the destination register,
    and `STOREIDX` writes the value operand into that cell — it is the one
    instruction of this model that writes memory. -/
def isMemOpn (i : LinstrR) : Bool :=
  match i with
  | .Lopn _ opn _ => opn == "LOADIDX" || opn == "STOREIDX"
  | _ => false

/-- An `Lopn` that is not a runtime-indexed memory op carries an opcode distinct
    from both `LOADIDX` and `STOREIDX`, the side condition of
    `LcmdCopyPropagate.lsemStep_reg_nonmem`. -/
theorem opn_nonmem_of_isMemOpn_false {dsts srcs : List LOperand} {opn : String}
    (h : isMemOpn (.Lopn dsts opn srcs) = false) : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" := by
  simp only [isMemOpn, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  exact h

/-- Destination registers written by a body's modeled single-register `Lopn`s. -/
def bodyDefs (body : List Linstr) : List String :=
  body.filterMap (fun li => match li.li_i with | .Lopn [.reg d] _ _ => some d | _ => none)

/-- The invariance criterion: `i` is a single-register `Lopn` whose sources are
    registers or immediates (no memory, no flags in this model), whose destination
    is written exactly once inside `loopBody` (only by `i`), and whose source
    registers are not written anywhere in `loopBody` (defined outside the loop). -/
def isLoopInvariant (loopBody : List Linstr) (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg d] _ srcs =>
      srcs.all isRegOrImm &&
      (bodyDefs loopBody).count d == 1 &&
      srcs.all (fun o => (operandReads o).all (fun r => decide (r ∉ bodyDefs loopBody)))
  | _ => false

/-! ## 2. Operand stability across a straight-line run (STEP 1: the reusable core)

If none of the registers an operand reads is written anywhere in a straight-line
run, the operand's value is unchanged from the start of the run to its end. The
register/memory-preservation lemmas below are the direct route: a step of a
non-memory instruction writes only its destination register, so a run of such
instructions that avoids a register leaves it and all memory untouched. -/

/-- A step of an instruction that is not a runtime-indexed memory op never writes
    memory. -/
theorem lsemStep_lmem {w : Nat} (i : LinstrR) {s b : Lstate w}
    (hnm : isMemOpn i = false) (h : lsemStep i s = some b) : b.lmem = s.lmem := by
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => simp [lsemStep] at h
    | cons d ds =>
      cases ds with
      | cons _ _ => simp [lsemStep] at h
      | nil =>
        cases d with
        | reg dst =>
          rw [LcmdCopyPropagate.lsemStep_reg_nonmem dst opn srcs s
            (opn_nonmem_of_isMemOpn_false hnm)] at h
          cases happ : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
          | none => rw [happ] at h; simp at h
          | some v => rw [happ] at h; simp only [Option.some.injEq] at h; rw [← h]; rfl
        | imm _ => simp [lsemStep] at h
        | arr _ _ => simp [lsemStep] at h
        | arrIdx _ _ _ => simp [lsemStep] at h
  | Lalign => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Llabel k l => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Lgoto _ => simp [lsemStep] at h
  | Lcond _ _ => simp [lsemStep] at h
  | Ligoto _ => simp [lsemStep] at h
  | Lcall _ _ => simp [lsemStep] at h
  | Lret => simp [lsemStep] at h
  | LstoreLabel _ _ => simp [lsemStep] at h
  | Lsyscall _ => simp [lsemStep] at h

/-- A step of an instruction that is not a runtime-indexed memory op leaves every
    register it does not write unchanged. -/
theorem lsemStep_lvm_of_not_writes {w : Nat} (i : LinstrR) {s b : Lstate w} (r : String)
    (hnm : isMemOpn i = false)
    (h : lsemStep i s = some b) (hw : instrWrites i r = false) : b.lvm r = s.lvm r := by
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => simp [lsemStep] at h
    | cons d ds =>
      cases ds with
      | cons _ _ => simp [lsemStep] at h
      | nil =>
        cases d with
        | reg dst =>
          rw [LcmdCopyPropagate.lsemStep_reg_nonmem dst opn srcs s
            (opn_nonmem_of_isMemOpn_false hnm)] at h
          cases happ : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
          | none => rw [happ] at h; simp at h
          | some v =>
            rw [happ] at h; simp only [Option.some.injEq] at h; rw [← h]
            simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
            have hne : ¬ (r = dst) := by
              simp only [instrWrites] at hw
              intro he; subst he; simp at hw
            simp [hne]
        | imm _ => simp [lsemStep] at h
        | arr _ _ => simp [lsemStep] at h
        | arrIdx _ _ _ => simp [lsemStep] at h
  | Lalign => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Llabel k l => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Lgoto _ => simp [lsemStep] at h
  | Lcond _ _ => simp [lsemStep] at h
  | Ligoto _ => simp [lsemStep] at h
  | Lcall _ _ => simp [lsemStep] at h
  | Lret => simp [lsemStep] at h
  | LstoreLabel _ _ => simp [lsemStep] at h
  | Lsyscall _ => simp [lsemStep] at h

/-- A straight-line run of instructions that are not runtime-indexed memory ops
    never writes memory. -/
theorem lsemStraight_lmem {w : Nat} (runR : List LinstrR) {s b : Lstate w}
    (hnm : ∀ i ∈ runR, isMemOpn i = false)
    (h : lsemStraight runR s = some b) : b.lmem = s.lmem := by
  induction runR generalizing s with
  | nil => simp only [lsemStraight_nil, Option.some.injEq] at h; rw [h]
  | cons i is ih =>
    simp only [lsemStraight_cons] at h
    cases hs : lsemStep i s with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      have hnmi : isMemOpn i = false := hnm i (List.mem_cons_self ..)
      have hnms : ∀ j ∈ is, isMemOpn j = false := fun j hj => hnm j (List.mem_cons_of_mem _ hj)
      rw [ih hnms h, lsemStep_lmem i hnmi hs]

/-- A straight-line run of instructions that are not runtime-indexed memory ops
    leaves a register it never writes unchanged. -/
theorem lsemStraight_lvm_of_not_writes {w : Nat} (runR : List LinstrR) {s b : Lstate w}
    (r : String) (hnm : ∀ i ∈ runR, isMemOpn i = false)
    (h : lsemStraight runR s = some b)
    (hw : ∀ i ∈ runR, instrWrites i r = false) : b.lvm r = s.lvm r := by
  induction runR generalizing s with
  | nil => simp only [lsemStraight_nil, Option.some.injEq] at h; rw [h]
  | cons i is ih =>
    simp only [lsemStraight_cons] at h
    cases hs : lsemStep i s with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      have hnmi : isMemOpn i = false := hnm i (List.mem_cons_self ..)
      have hnms : ∀ j ∈ is, isMemOpn j = false := fun j hj => hnm j (List.mem_cons_of_mem _ hj)
      have hwi : instrWrites i r = false := hw i (List.mem_cons_self ..)
      have hws : ∀ j ∈ is, instrWrites j r = false := fun j hj => hw j (List.mem_cons_of_mem _ hj)
      rw [ih hnms h hws, lsemStep_lvm_of_not_writes i r hnmi hs hwi]

/-- **Operand stability across a straight-line run.** If the run holds no
    runtime-indexed memory op and none of the registers an operand reads is
    written anywhere in it, the operand's evaluation is unchanged from the start
    of the run to its end. -/
theorem evalOperand_stable {w : Nat} (runR : List LinstrR) {s b : Lstate w} (o : LOperand)
    (hnm : ∀ i ∈ runR, isMemOpn i = false)
    (h : lsemStraight runR s = some b)
    (hno : ∀ r ∈ operandReads o, ∀ i ∈ runR, instrWrites i r = false) :
    evalOperand b o = evalOperand s o := by
  cases o with
  | reg r =>
    have := lsemStraight_lvm_of_not_writes runR r hnm h
      (fun i hi => hno r (by simp [operandReads]) i hi)
    simp [evalOperand, this]
  | imm v => rfl
  | arr base idx => simp [evalOperand, lsemStraight_lmem runR hnm h]
  | arrIdx base idx scale =>
    have hmem := lsemStraight_lmem runR hnm h
    have hlvm := lsemStraight_lvm_of_not_writes runR idx hnm h
      (fun i hi => hno idx (by simp [operandReads]) i hi)
    simp [evalOperand, hmem, hlvm]

/-! ## 3. The invariance crux: an invariant `Lopn` recomputes the same value -/

/-- The sources of an invariant instruction evaluate identically before and after a
    run that holds no runtime-indexed memory op and writes none of their
    registers. -/
theorem srcs_map_stable {w : Nat} (runR : List LinstrR) {s b : Lstate w} (srcs : List LOperand)
    (hnm : ∀ i ∈ runR, isMemOpn i = false)
    (h : lsemStraight runR s = some b)
    (hno : ∀ o ∈ srcs, ∀ r ∈ operandReads o, ∀ j ∈ runR, instrWrites j r = false) :
    srcs.map (evalOperand b) = srcs.map (evalOperand s) := by
  apply List.map_congr_left
  intro o ho
  exact evalOperand_stable runR o hnm h (fun r hr j hj => hno o ho r hr j hj)

/-- **The invariance crux.** The value an invariant `Lopn`'s opcode computes is
    unchanged across a loop-body run that holds no runtime-indexed memory op and
    writes none of its source registers, so hoisting it out of the loop computes
    the same result. -/
theorem invariant_value_stable {w : Nat} (runR : List LinstrR) {s b : Lstate w}
    (opn : String) (srcs : List LOperand)
    (hnm : ∀ i ∈ runR, isMemOpn i = false)
    (h : lsemStraight runR s = some b)
    (hno : ∀ o ∈ srcs, ∀ r ∈ operandReads o, ∀ j ∈ runR, instrWrites j r = false) :
    applyOpn (stripWidthTag opn) (srcs.map (evalOperand b))
      = applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) := by
  rw [srcs_map_stable runR srcs hnm h hno]

/-- A register written in `loopBody` lies in `bodyDefs loopBody`. -/
theorem instrWrites_false_of_not_bodyDef (loopBody : List Linstr) (j : Linstr) (r : String)
    (hj : j ∈ loopBody) (hr : r ∉ bodyDefs loopBody) : instrWrites j.li_i r = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  apply hr
  unfold instrWrites at hc
  split at hc
  · rename_i d o s heq
    rw [beq_iff_eq] at hc
    subst hc
    rw [bodyDefs, List.mem_filterMap]
    exact ⟨j, hj, by rw [heq]⟩
  · exact absurd hc (by simp)

/-- From the syntactic criterion, every source register of `i` is unwritten by
    every instruction of `loopBody`. -/
theorem invariant_srcs_not_written (loopBody : List Linstr) (i : Linstr)
    (d opn : String) (srcs : List LOperand)
    (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant loopBody i = true) :
    ∀ o ∈ srcs, ∀ r ∈ operandReads o, ∀ j ∈ loopBody, instrWrites j.li_i r = false := by
  simp only [isLoopInvariant, hli] at hinv
  rw [Bool.and_eq_true, Bool.and_eq_true] at hinv
  obtain ⟨⟨_, _⟩, h3⟩ := hinv
  rw [List.all_eq_true] at h3
  intro o ho r hr j hj
  have h3o := h3 o ho
  rw [List.all_eq_true] at h3o
  have hnd := h3o r hr
  rw [decide_eq_true_eq] at hnd
  exact instrWrites_false_of_not_bodyDef loopBody j r hj hnd

/-- **LICM value soundness from the syntactic criterion.** If `i` passes
    `isLoopInvariant loopBody`, then executing any straight-line sub-run of the
    loop body that holds no runtime-indexed memory op recomputes `i`'s operation
    to the same word — the hoisted computation and every in-loop recomputation
    agree. -/
theorem invariant_value_stable_of_criterion
    (loopBody : List Linstr) (i : Linstr) (d opn : String) (srcs : List LOperand)
    (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant loopBody i = true)
    {w : Nat} (run : List Linstr) (hsub : ∀ j ∈ run, j ∈ loopBody)
    (hnm : ∀ j ∈ run, isMemOpn j.li_i = false)
    {s b : Lstate w} (h : lsemStraight (run.map Linstr.li_i) s = some b) :
    applyOpn (stripWidthTag opn) (srcs.map (evalOperand b))
      = applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) := by
  refine invariant_value_stable (run.map Linstr.li_i) opn srcs ?_ h ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hnm j hj
  intro o ho r hr jj hjj
  rw [List.mem_map] at hjj
  obtain ⟨j, hjrun, hjeq⟩ := hjj
  rw [← hjeq]
  exact invariant_srcs_not_written loopBody i d opn srcs hli hinv o ho r hr j (hsub j hjrun)

/-! ## 4. The hoisting transform `hoistOne` (STEP 2) -/

/-- An instruction is the loop header `Llabel _ L`. -/
def isLabelInstr (L : LLabel) (li : Linstr) : Bool :=
  match li.li_i with | .Llabel _ l => l == L | _ => false

/-- Structural equality of two hoisting candidates on the modeled single-register
    `Lopn` shape (destination, opcode, sources). -/
def matchHoist (i j : Linstr) : Bool :=
  match i.li_i, j.li_i with
  | .Lopn [.reg d1] o1 s1, .Lopn [.reg d2] o2 s2 => decide (d1 = d2 ∧ o1 = o2 ∧ s1 = s2)
  | _, _ => false

/-- Delete the first instruction matching `i` from a list. -/
def eraseFirstMatch (i : Linstr) : List Linstr → List Linstr
  | [] => []
  | j :: js => if matchHoist i j then js else j :: eraseFirstMatch i js

/-- Split a list at the first element satisfying `p`, returning the prefix, that
    element, and the suffix. -/
def splitAtFirst (p : Linstr → Bool) : List Linstr → Option (List Linstr × Linstr × List Linstr)
  | [] => none
  | x :: xs => if p x then some ([], x, xs) else (splitAtFirst p xs).map (fun t => (x :: t.1, t.2.1, t.2.2))

/-- Hoist `i` into a preheader placed immediately before the first `Llabel _ L`,
    deleting the first matching occurrence of `i` from the loop portion. If `L` is
    absent, the body is unchanged. -/
def hoistOne (L : LLabel) (i : Linstr) (body : List Linstr) : List Linstr :=
  match splitAtFirst (isLabelInstr L) body with
  | some (pre, lbl, rest) => pre ++ [i] ++ lbl :: eraseFirstMatch i rest
  | none => body

/-- `matchHoist` is reflexive on a modeled single-register `Lopn`. -/
theorem matchHoist_refl_lopn (i : Linstr) (d o : String) (s : List LOperand)
    (h : i.li_i = .Lopn [.reg d] o s) : matchHoist i i = true := by
  unfold matchHoist; rw [h]; simp

/-- `splitAtFirst` on a body whose prefix avoids `p` and whose next element
    satisfies `p` returns exactly that split. -/
theorem splitAtFirst_decomp (p : Linstr → Bool) (pre : List Linstr) (x : Linstr) (rest : List Linstr)
    (hpre : ∀ y ∈ pre, p y = false) (hx : p x = true) :
    splitAtFirst p (pre ++ x :: rest) = some (pre, x, rest) := by
  induction pre with
  | nil => simp [splitAtFirst, hx]
  | cons y ys ih =>
    have hy : p y = false := hpre y (List.mem_cons_self ..)
    have hys : ∀ z ∈ ys, p z = false := fun z hz => hpre z (List.mem_cons_of_mem _ hz)
    simp only [List.cons_append, splitAtFirst, hy, Bool.false_eq_true, ite_false, ih hys]; rfl

/-- `eraseFirstMatch` deletes exactly the `i` after a match-free prefix. -/
theorem eraseFirstMatch_decomp (i : Linstr) (before after : List Linstr)
    (hbef : ∀ y ∈ before, matchHoist i y = false) (hi : matchHoist i i = true) :
    eraseFirstMatch i (before ++ i :: after) = before ++ after := by
  induction before with
  | nil => simp [eraseFirstMatch, hi]
  | cons y ys ih =>
    have hy : matchHoist i y = false := hbef y (List.mem_cons_self ..)
    have hys : ∀ z ∈ ys, matchHoist i z = false := fun z hz => hbef z (List.mem_cons_of_mem _ hz)
    simp only [List.cons_append, eraseFirstMatch, hy, Bool.false_eq_true, ite_false, ih hys]

/-- `hoistOne` on the loop shape: the invariant instruction moves before the loop
    header and out of the loop body. -/
theorem hoistOne_decomp (L : LLabel) (i : Linstr) (pre : List Linstr) (lbl : Linstr)
    (before after : List Linstr)
    (hpre : ∀ y ∈ pre, isLabelInstr L y = false)
    (hlbl : isLabelInstr L lbl = true)
    (hbef : ∀ y ∈ before, matchHoist i y = false)
    (hi : matchHoist i i = true) :
    hoistOne L i (pre ++ lbl :: (before ++ i :: after))
      = pre ++ [i] ++ lbl :: (before ++ after) := by
  unfold hoistOne
  rw [splitAtFirst_decomp (isLabelInstr L) pre lbl (before ++ i :: after) hpre hlbl]
  dsimp only
  rw [eraseFirstMatch_decomp i before after hbef hi]

/-- Hoisting relocates the invariant instruction without adding or dropping any
    instruction: the transformed body is a permutation of the original. -/
theorem hoistOne_perm (pre : List Linstr) (i lbl : Linstr) (before after : List Linstr) :
    (pre ++ [i] ++ lbl :: (before ++ after)).Perm (pre ++ lbl :: (before ++ i :: after)) := by
  rw [List.append_assoc]
  apply List.Perm.append_left pre
  have hmid : (before ++ i :: after).Perm (i :: (before ++ after)) := List.perm_middle
  have e1 : [i] ++ lbl :: (before ++ after) = i :: lbl :: (before ++ after) := by simp
  rw [e1]
  exact (List.Perm.swap lbl i (before ++ after)).trans (List.Perm.cons lbl hmid.symm)

/-! ## 5. Milestone-1 target: entry-point store preservation (STEP 3) -/

/-- The function body has the hoistable do-while loop shape around label `L` and
    invariant instruction `i`: an entry `pre` with no `L`, the loop header `lbl`
    (a `Llabel _ L`), a loop body `before ++ i :: after` in which no instruction
    before `i` matches `i` and `i` passes `isLoopInvariant`, and a `Lcond _ L`
    back-edge, then `post`. -/
def IsHoistableLoop (L : LLabel) (i : Linstr) (fd : Lfundef) : Prop :=
  ∃ (pre before after post : List Linstr) (lbl backedge : Linstr),
    fd.lfd_body = pre ++ lbl :: (before ++ i :: (after ++ backedge :: post))
    ∧ isLabelInstr L lbl = true
    ∧ (∃ cond, backedge.li_i = .Lcond cond L)
    ∧ (∀ y ∈ pre, isLabelInstr L y = false)
    ∧ (∀ y ∈ before, matchHoist i y = false)
    ∧ (∃ d opn srcs, i.li_i = .Lopn [.reg d] opn srcs)
    ∧ isLoopInvariant (before ++ i :: after) i = true

/-- On a hoistable loop, `hoistOne` produces exactly the preheadered body:
    `i` before the header, the loop body with `i` deleted. -/
theorem hoistOne_hoistable_eq (L : LLabel) (i : Linstr) (fd : Lfundef)
    (h : IsHoistableLoop L i fd) :
    ∃ (pre before after post : List Linstr) (lbl backedge : Linstr),
      hoistOne L i fd.lfd_body
        = pre ++ [i] ++ lbl :: (before ++ (after ++ backedge :: post)) := by
  obtain ⟨pre, before, after, post, lbl, backedge, hbody, hlbl, _, hpre, hbef, ⟨d, opn, srcs, hli⟩, _⟩ := h
  refine ⟨pre, before, after, post, lbl, backedge, ?_⟩
  rw [hbody]
  exact hoistOne_decomp L i pre lbl before (after ++ backedge :: post) hpre hlbl hbef
    (matchHoist_refl_lopn i d opn srcs hli)

/-- On a hoistable loop, the hoisted body is a permutation of the source body:
    the transform neither adds nor drops an instruction. -/
theorem hoistOne_hoistable_perm (L : LLabel) (i : Linstr) (fd : Lfundef)
    (h : IsHoistableLoop L i fd) : (hoistOne L i fd.lfd_body).Perm fd.lfd_body := by
  obtain ⟨pre, before, after, post, lbl, backedge, hbody, hlbl, _, hpre, hbef, ⟨d, opn, srcs, hli⟩, _⟩ := h
  rw [hbody,
    hoistOne_decomp L i pre lbl before (after ++ backedge :: post) hpre hlbl hbef
      (matchHoist_refl_lopn i d opn srcs hli)]
  exact hoistOne_perm pre i lbl before (after ++ backedge :: post)

/-! ### Store agreement off the hoist destination

Inside a hoisted loop the source and hoisted programs do not hold equal stores:
the source recomputes the destination `d` each iteration while the hoisted
program carries the value from the preheader. They agree on every register other
than `d` and on all of memory. `AgreeExcept` is that relation, and the two
preservation lemmas carry it across a straight-line run whose instructions
neither read nor write `d`. -/

/-- The register maps of two states agree on every register other than `d`, and
    their memories are equal. -/
def AgreeExcept (d : String) {w : Nat} (s t : Lstate w) : Prop :=
  s.lmem = t.lmem ∧ ∀ r, r ≠ d → s.lvm r = t.lvm r

/-- The registers an instruction reads: the source operands' read registers of a
    modeled `Lopn`, and none for any other instruction (which does not read the
    register map in this model). -/
def instrReadRegs : LinstrR → List String
  | .Lopn _ _ srcs => srcs.flatMap operandReads
  | _ => []

/-- Full store equality is `AgreeExcept` for every `d`. -/
theorem agreeExcept_of_stateStore {w : Nat} (d : String) {s t : Lstate w}
    (h : stateStore s = stateStore t) : AgreeExcept d s t := by
  simp only [stateStore, Prod.mk.injEq] at h
  exact ⟨h.2, fun r _ => by rw [h.1]⟩

/-- An operand whose read registers avoid `d` evaluates equally on two
    `AgreeExcept d` states. -/
theorem evalOperand_agreeExcept {w : Nat} (d : String) {s t : Lstate w}
    (h : AgreeExcept d s t) (o : LOperand) (ho : ∀ r ∈ operandReads o, r ≠ d) :
    evalOperand s o = evalOperand t o := by
  obtain ⟨hm, hv⟩ := h
  cases o with
  | reg r => simp only [evalOperand]; exact hv r (ho r (by simp [operandReads]))
  | imm v => rfl
  | arr base idx => simp [evalOperand, hm]
  | arrIdx base idx scale =>
      have hidx := hv idx (ho idx (by simp [operandReads]))
      simp [evalOperand, hm, hidx]

/-- A step of an instruction that is not a runtime-indexed memory op and neither
    reads nor writes `d` maps `AgreeExcept d` states to `AgreeExcept d` states,
    succeeding on both together. -/
theorem lsemStep_agreeExcept {w : Nat} (d : String) (i : LinstrR) {s t s1 : Lstate w}
    (hnm : isMemOpn i = false)
    (h : AgreeExcept d s t) (hw : instrWrites i d = false)
    (hr : ∀ r ∈ instrReadRegs i, r ≠ d) (hs : lsemStep i s = some s1) :
    ∃ t1, lsemStep i t = some t1 ∧ AgreeExcept d s1 t1 := by
  obtain ⟨hm, hv⟩ := h
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => simp [lsemStep] at hs
    | cons dd ds =>
      cases ds with
      | cons _ _ => simp [lsemStep] at hs
      | nil =>
        cases dd with
        | reg dst =>
          have hsrceq : srcs.map (evalOperand s) = srcs.map (evalOperand t) := by
            apply List.map_congr_left
            intro o ho
            refine evalOperand_agreeExcept d ⟨hm, hv⟩ o ?_
            intro r hro
            exact hr r (by simp only [instrReadRegs, List.mem_flatMap]; exact ⟨o, ho, hro⟩)
          have hdne : dst ≠ d := by
            intro he; subst he; simp [instrWrites] at hw
          have hnm' : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" := opn_nonmem_of_isMemOpn_false hnm
          rw [LcmdCopyPropagate.lsemStep_reg_nonmem dst opn srcs s hnm'] at hs
          cases happ : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
          | none => rw [happ] at hs; simp at hs
          | some v =>
            rw [happ] at hs; simp only [Option.some.injEq] at hs
            refine ⟨(t.setReg dst v).nextPc, ?_, ?_⟩
            · rw [LcmdCopyPropagate.lsemStep_reg_nonmem dst opn srcs t hnm', ← hsrceq, happ]
            · subst hs
              refine ⟨by simp [Lstate.nextPc, Lstate.setReg, hm], ?_⟩
              intro r hrd
              simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
              by_cases hrdst : r = dst
              · simp [hrdst]
              · simp only [hrdst, ite_false]; exact hv r hrd
        | imm _ => simp [lsemStep] at hs
        | arr _ _ => simp [lsemStep] at hs
        | arrIdx _ _ _ => simp [lsemStep] at hs
  | Lalign =>
      simp only [lsemStep, Option.some.injEq] at hs; subst hs
      exact ⟨t.nextPc, rfl, by
        refine ⟨by simp [Lstate.nextPc, hm], fun r hrd => ?_⟩
        simp only [Lstate.lvm_nextPc]; exact hv r hrd⟩
  | Llabel k l =>
      simp only [lsemStep, Option.some.injEq] at hs; subst hs
      exact ⟨t.nextPc, rfl, by
        refine ⟨by simp [Lstate.nextPc, hm], fun r hrd => ?_⟩
        simp only [Lstate.lvm_nextPc]; exact hv r hrd⟩
  | Lgoto _ => simp [lsemStep] at hs
  | Lcond _ _ => simp [lsemStep] at hs
  | Ligoto _ => simp [lsemStep] at hs
  | Lcall _ _ => simp [lsemStep] at hs
  | Lret => simp [lsemStep] at hs
  | LstoreLabel _ _ => simp [lsemStep] at hs
  | Lsyscall _ => simp [lsemStep] at hs

/-- A straight-line run of instructions that are not runtime-indexed memory ops
    and neither read nor write `d` maps `AgreeExcept d` states to `AgreeExcept d`
    states, succeeding on both. -/
theorem lsemStraight_agreeExcept {w : Nat} (d : String) (runR : List LinstrR)
    {s t s1 : Lstate w}
    (hnm : ∀ i ∈ runR, isMemOpn i = false)
    (hw : ∀ i ∈ runR, instrWrites i d = false)
    (hr : ∀ i ∈ runR, ∀ r ∈ instrReadRegs i, r ≠ d)
    (h : AgreeExcept d s t) (hs : lsemStraight runR s = some s1) :
    ∃ t1, lsemStraight runR t = some t1 ∧ AgreeExcept d s1 t1 := by
  induction runR generalizing s t with
  | nil =>
    simp only [lsemStraight_nil, Option.some.injEq] at hs
    exact ⟨t, rfl, hs ▸ h⟩
  | cons j js ih =>
    simp only [lsemStraight_cons] at hs
    cases hstep : lsemStep j s with
    | none => rw [hstep] at hs; simp at hs
    | some s' =>
      rw [hstep] at hs
      obtain ⟨t', hstept, h'⟩ := lsemStep_agreeExcept d j (hnm j (List.mem_cons_self ..)) h
        (hw j (List.mem_cons_self ..)) (fun r hr' => hr j (List.mem_cons_self ..) r hr') hstep
      obtain ⟨t1, ht1, h1⟩ := ih (fun i hi => hnm i (List.mem_cons_of_mem _ hi))
        (fun i hi => hw i (List.mem_cons_of_mem _ hi))
        (fun i hi => hr i (List.mem_cons_of_mem _ hi)) h' hs
      exact ⟨t1, by simp only [lsemStraight_cons, hstept]; exact ht1, h1⟩

/-- **The hoisted-loop-body correctness core.** Running the source loop body
    `before ++ i :: after` from a state `s`, and the hoisted loop body
    `before ++ after` (with `i` deleted) from a state `t` that already holds the
    hoist destination `d` at the value `i` computes, reach fully equal stores. The
    side conditions are: the loop body holds no runtime-indexed memory op; the
    source and hoisted states agree off `d` at entry (`AgreeExcept`); no
    instruction of `before` reads or writes `d`; and `i`'s sources read neither
    `d` nor any register `before` writes. The source recomputes `d := v` at `i`;
    because `i`'s sources are unchanged by `before`, `v` equals the preloaded `d`,
    so the two stores coincide once `i` has run, and `after` runs identically on
    both. -/
theorem hoistedBody_full_agree {w : Nat} (d opn : String) (srcs : List LOperand)
    (before after : List Linstr) (i : Linstr)
    (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hnmBody : ∀ j ∈ before ++ i :: after, isMemOpn j.li_i = false)
    (hbefW : ∀ j ∈ before, instrWrites j.li_i d = false)
    (hbefR : ∀ j ∈ before, ∀ r ∈ instrReadRegs j.li_i, r ≠ d)
    (hsrcD : ∀ r ∈ srcs.flatMap operandReads, r ≠ d)
    (hsrcInv : ∀ o ∈ srcs, ∀ r ∈ operandReads o, ∀ j ∈ before, instrWrites j.li_i r = false)
    {s t s1 : Lstate w}
    (h : AgreeExcept d s t)
    (hpre : applyOpn (stripWidthTag opn) (srcs.map (evalOperand t)) = some (t.lvm d))
    (hs : lsemStraight ((before ++ i :: after).map Linstr.li_i) s = some s1) :
    ∃ t1, lsemStraight ((before ++ after).map Linstr.li_i) t = some t1 ∧
      stateStore s1 = stateStore t1 := by
  set bR := before.map Linstr.li_i with hbR
  set aR := after.map Linstr.li_i with haR
  have hmapsrc : (before ++ i :: after).map Linstr.li_i = bR ++ (i.li_i :: aR) := by
    simp [hbR, haR]
  rw [hmapsrc, lsemStraight_append] at hs
  cases hsB : lsemStraight bR s with
  | none => rw [hsB] at hs; simp at hs
  | some sB =>
    rw [hsB] at hs
    have hs' : lsemStraight (i.li_i :: aR) sB = some s1 := hs
    rw [lsemStraight_cons] at hs'
    have hbefW' : ∀ x ∈ bR, instrWrites x d = false := by
      intro x hx; rw [hbR, List.mem_map] at hx
      obtain ⟨j, hj, rfl⟩ := hx; exact hbefW j hj
    have hbefR' : ∀ x ∈ bR, ∀ r ∈ instrReadRegs x, r ≠ d := by
      intro x hx; rw [hbR, List.mem_map] at hx
      obtain ⟨j, hj, rfl⟩ := hx; exact hbefR j hj
    have hnmBef' : ∀ x ∈ bR, isMemOpn x = false := by
      intro x hx; rw [hbR, List.mem_map] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact hnmBody j (List.mem_append_left _ hj)
    obtain ⟨tB, htB, hAB⟩ := lsemStraight_agreeExcept d bR hnmBef' hbefW' hbefR' h hsB
    have htBd : tB.lvm d = t.lvm d :=
      lsemStraight_lvm_of_not_writes bR d hnmBef' htB hbefW'
    have hsrceq_sB_tB : srcs.map (evalOperand sB) = srcs.map (evalOperand tB) := by
      apply List.map_congr_left
      intro o ho
      refine evalOperand_agreeExcept d hAB o ?_
      intro r hro
      exact hsrcD r (by rw [List.mem_flatMap]; exact ⟨o, ho, hro⟩)
    have hsrceq_tB_t : srcs.map (evalOperand tB) = srcs.map (evalOperand t) := by
      apply List.map_congr_left
      intro o ho
      exact evalOperand_stable bR o hnmBef' htB (fun r hr x hx => by
        rw [hbR, List.mem_map] at hx; obtain ⟨jj, hjj, rfl⟩ := hx
        exact hsrcInv o ho r hr jj hjj)
    have hnmI : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" :=
      opn_nonmem_of_isMemOpn_false
        (hli ▸ hnmBody i (List.mem_append_right _ (List.mem_cons_self ..)))
    cases hstepi : lsemStep i.li_i sB with
    | none => rw [hstepi] at hs'; simp at hs'
    | some s' =>
      rw [hstepi] at hs'
      replace hs' : lsemStraight aR s' = some s1 := hs'
      rw [hli, LcmdCopyPropagate.lsemStep_reg_nonmem d opn srcs sB hnmI] at hstepi
      cases happ : applyOpn (stripWidthTag opn) (srcs.map (evalOperand sB)) with
      | none => rw [happ] at hstepi; simp at hstepi
      | some v =>
        rw [happ] at hstepi; simp only [Option.some.injEq] at hstepi
        have hs'eq : s' = (sB.setReg d v).nextPc := hstepi.symm
        have hvv : v = tB.lvm d := by
          have e1 : applyOpn (stripWidthTag opn) (srcs.map (evalOperand t)) = some v := by
            rw [← hsrceq_tB_t, ← hsrceq_sB_tB]; exact happ
          rw [hpre] at e1
          rw [htBd]; exact (Option.some.inj e1).symm
        have hss : stateStore s' = stateStore tB := by
          rw [hs'eq]
          simp only [stateStore, Prod.mk.injEq]
          refine ⟨?_, ?_⟩
          · funext r
            simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
            by_cases hrd : r = d
            · rw [ite_eq_left hrd, hrd, hvv]
            · rw [ite_eq_right hrd]; exact hAB.2 r hrd
          · simp only [Lstate.nextPc, Lstate.setReg]; exact hAB.1
        have hmap := LprogOptPipeline.lsemStraight_stateStore aR hss
        rw [hs'] at hmap
        simp only [Option.map_some] at hmap
        cases hAt : lsemStraight aR tB with
        | none => rw [hAt] at hmap; simp at hmap
        | some t1 =>
          rw [hAt] at hmap; simp only [Option.map_some, Option.some.injEq] at hmap
          refine ⟨t1, ?_, hmap⟩
          have hmaphoist : (before ++ after).map Linstr.li_i = bR ++ aR := by
            simp [hbR, haR]
          rw [hmaphoist, lsemStraight_append, htB]
          exact hAt

/-! ## 6. The soundness condition the criterion is missing

`isLoopInvariant loopBody i` requires `i`'s destination `d` to be written exactly
once in the loop body and `i`'s sources to be loop-invariant, but places no
condition on which registers the loop-body prefix `before` reads. Loop-invariant
code motion is sound only when `d` is not upward-exposed in the loop — no use of
`d` reaches the loop header before `i` redefines it. `IsHoistableLoopStrong` adds
exactly that condition: no instruction of `before` reads `d`. The three
consequences the loop-body correctness core `hoistedBody_full_agree` needs — `d`
unwritten and unread in `before`, and `i`'s sources reading neither `d` nor any
register `before` writes — are then available; only the read-of-`d` condition is
absent from `isLoopInvariant`. -/

/-- The hoistable do-while loop shape of `IsHoistableLoop`, strengthened with the
    loop-invariant-code-motion soundness condition: no instruction of the loop-body
    prefix `before` reads the hoist destination `d`. -/
def IsHoistableLoopStrong (L : LLabel) (i : Linstr) (fd : Lfundef) : Prop :=
  ∃ (pre before after post : List Linstr) (lbl backedge : Linstr)
    (d opn : String) (srcs : List LOperand),
    fd.lfd_body = pre ++ lbl :: (before ++ i :: (after ++ backedge :: post))
    ∧ isLabelInstr L lbl = true
    ∧ (∃ cond, backedge.li_i = .Lcond cond L)
    ∧ (∀ y ∈ pre, isLabelInstr L y = false)
    ∧ (∀ y ∈ before, matchHoist i y = false)
    ∧ i.li_i = .Lopn [.reg d] opn srcs
    ∧ isLoopInvariant (before ++ i :: after) i = true
    ∧ (∀ y ∈ before, ∀ r ∈ instrReadRegs y.li_i, r ≠ d)

/-- The strengthened shape refines the original hoistable-loop predicate. -/
theorem isHoistableLoop_of_strong (L : LLabel) (i : Linstr) (fd : Lfundef)
    (h : IsHoistableLoopStrong L i fd) : IsHoistableLoop L i fd := by
  obtain ⟨pre, before, after, post, lbl, backedge, d, opn, srcs,
    hbody, hlbl, hcond, hpre, hbef, hli, hinv, _⟩ := h
  exact ⟨pre, before, after, post, lbl, backedge, hbody, hlbl, hcond, hpre, hbef,
    ⟨d, opn, srcs, hli⟩, hinv⟩

/-- The destination of a modeled single-register `Lopn` occurring in a body lies in
    that body's `bodyDefs`. -/
theorem dest_mem_bodyDefs (loopBody : List Linstr) (i : Linstr) (d opn : String)
    (srcs : List LOperand) (hi : i ∈ loopBody) (hli : i.li_i = .Lopn [.reg d] opn srcs) :
    d ∈ bodyDefs loopBody := by
  rw [bodyDefs, List.mem_filterMap]
  exact ⟨i, hi, by rw [hli]⟩

/-- From `isLoopInvariant`, `i`'s source registers are all distinct from its
    destination `d` (`d` is a body definition, and the sources read no body
    definition). -/
theorem invariant_srcs_ne_dest (loopBody : List Linstr) (i : Linstr) (d opn : String)
    (srcs : List LOperand) (hi : i ∈ loopBody) (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant loopBody i = true) :
    ∀ r ∈ srcs.flatMap operandReads, r ≠ d := by
  have hd : d ∈ bodyDefs loopBody := dest_mem_bodyDefs loopBody i d opn srcs hi hli
  intro r hr
  rw [List.mem_flatMap] at hr
  obtain ⟨o, ho, hro⟩ := hr
  simp only [isLoopInvariant, hli, Bool.and_eq_true] at hinv
  obtain ⟨_, h3⟩ := hinv
  rw [List.all_eq_true] at h3
  have h3o := h3 o ho
  rw [List.all_eq_true] at h3o
  have hnd := h3o r hro
  rw [decide_eq_true_eq] at hnd
  intro he; subst he; exact hnd hd

/-- From `isLoopInvariant`, no instruction of the loop-body prefix `before` writes
    the hoist destination `d`: `i` already contributes the single occurrence of `d`
    in `bodyDefs`, so a second definition in `before` would push the count above
    one. -/
theorem before_notWrites_dest (before after : List Linstr) (i : Linstr) (d opn : String)
    (srcs : List LOperand) (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant (before ++ i :: after) i = true) :
    ∀ j ∈ before, instrWrites j.li_i d = false := by
  intro j hj
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have hjd : d ∈ bodyDefs before := by
    unfold instrWrites at hc
    split at hc
    · rename_i dd o s heq
      rw [beq_iff_eq] at hc; subst hc
      rw [bodyDefs, List.mem_filterMap]; exact ⟨j, hj, by rw [heq]⟩
    · exact absurd hc (by simp)
  have hid : d ∈ bodyDefs (i :: after) := by
    rw [bodyDefs, List.mem_filterMap]; exact ⟨i, List.mem_cons_self .., by rw [hli]⟩
  have hcount : (bodyDefs (before ++ i :: after)).count d = 1 := by
    simp only [isLoopInvariant, hli, Bool.and_eq_true] at hinv
    obtain ⟨⟨_, h2⟩, _⟩ := hinv
    rw [beq_iff_eq] at h2; exact h2
  rw [bodyDefs, List.filterMap_append, List.count_append] at hcount
  have h1 : 0 < (bodyDefs before).count d := List.count_pos_iff.mpr hjd
  have h2 : 0 < (bodyDefs (i :: after)).count d := List.count_pos_iff.mpr hid
  simp only [bodyDefs] at h1 h2
  omega

/-- **The loop-body correctness core wired to the strengthened criterion.** For the
    loop body `before ++ i :: after` of an `IsHoistableLoopStrong` function, and any
    hoisted state `t` already holding `d` at the value `i` computes, the source loop
    body and the hoisted loop body (with `i` deleted) reach fully equal stores from
    `AgreeExcept d`-related entry states. This is `hoistedBody_full_agree` with its
    side conditions discharged from `isLoopInvariant` and the strengthened
    read-of-`d` condition. -/
theorem hoistableStrong_body_full_agree {w : Nat} (i : Linstr)
    (before after : List Linstr) (d opn : String) (srcs : List LOperand)
    (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant (before ++ i :: after) i = true)
    (hnmBody : ∀ j ∈ before ++ i :: after, isMemOpn j.li_i = false)
    (hbefR : ∀ y ∈ before, ∀ r ∈ instrReadRegs y.li_i, r ≠ d)
    {s t s1 : Lstate w} (h : AgreeExcept d s t)
    (hstore : applyOpn (stripWidthTag opn) (srcs.map (evalOperand t)) = some (t.lvm d))
    (hs : lsemStraight ((before ++ i :: after).map Linstr.li_i) s = some s1) :
    ∃ t1, lsemStraight ((before ++ after).map Linstr.li_i) t = some t1 ∧
      stateStore s1 = stateStore t1 := by
  have hiMem : i ∈ before ++ i :: after := by
    rw [List.mem_append]; exact Or.inr (List.mem_cons_self ..)
  refine hoistedBody_full_agree d opn srcs before after i hli hnmBody
    (before_notWrites_dest before after i d opn srcs hli hinv) hbefR
    (invariant_srcs_ne_dest _ i d opn srcs hiMem hli hinv) ?_ h hstore hs
  intro o ho r hr j hj
  refine invariant_srcs_not_written (before ++ i :: after) i d opn srcs hli hinv o ho r hr j ?_
  rw [List.mem_append]; exact Or.inl hj

/-! ## 7. The do-while shape LICM is sound on

`IsHoistableLoopStrong` leaves the loop body free to transfer control out of the
loop before `i` executes, so store preservation over it is refutable: the source
never computes `d` on such a path while the hoisted preheader has already set it.
`IsHoistableDoWhile` is the do-while shape whose loop body and surrounding code
are straight-line, so the function's only label is the loop header and its only
branch is the back-edge `Lcond _ L`; loop-invariant code motion is sound on it,
and `LICMEntryStorePreservedGoalSL` is the store-preservation theorem over it. -/

/-- The do-while loop shape of `IsHoistableLoopStrong` with the additional
    condition that the entry `pre`, the loop-body pieces `before` and `after`, and
    the exit `post` are straight-line (`bodyIsStraightLine`): each holds no label
    or jump, so the function's only label is the loop header `lbl` and its only
    branch is the back-edge `Lcond _ L`. -/
def IsHoistableDoWhile (L : LLabel) (i : Linstr) (fd : Lfundef) : Prop :=
  ∃ (pre before after post : List Linstr) (lbl backedge : Linstr)
    (d opn : String) (srcs : List LOperand),
    fd.lfd_body = pre ++ lbl :: (before ++ i :: (after ++ backedge :: post))
    ∧ isLabelInstr L lbl = true
    ∧ (∃ cond, backedge.li_i = .Lcond cond L)
    ∧ (∀ y ∈ before, matchHoist i y = false)
    ∧ i.li_i = .Lopn [.reg d] opn srcs
    ∧ isLoopInvariant (before ++ i :: after) i = true
    ∧ (∀ y ∈ before, ∀ r ∈ instrReadRegs y.li_i, r ≠ d)
    ∧ LprogOptPipeline.bodyIsStraightLine pre = true
    ∧ LprogOptPipeline.bodyIsStraightLine before = true
    ∧ LprogOptPipeline.bodyIsStraightLine after = true
    ∧ LprogOptPipeline.bodyIsStraightLine post = true

/-- The strengthened do-while shape refines `IsHoistableLoopStrong`: the
    straight-line pieces yield the missing `pre`-has-no-`L` condition (a
    straight-line `pre` holds no label at all). -/
theorem isHoistableLoopStrong_of_doWhile (L : LLabel) (i : Linstr) (fd : Lfundef)
    (h : IsHoistableDoWhile L i fd) : IsHoistableLoopStrong L i fd := by
  obtain ⟨pre, before, after, post, lbl, backedge, d, opn, srcs,
    hbody, hlbl, hcond, hbef, hli, hinv, hbefR, hpreSL, _, _, _⟩ := h
  refine ⟨pre, before, after, post, lbl, backedge, d, opn, srcs,
    hbody, hlbl, hcond, ?_, hbef, hli, hinv, hbefR⟩
  intro y hy
  have h0 := LprogOptPipeline.straightLine_noLabel pre hpreSL y hy
  simp only [isLabelInstr]
  revert h0
  cases y.li_i <;> simp [LprogOptPipeline.isLbl]

/-- From `isLoopInvariant`, no instruction of `before ++ after` writes the hoist
    destination `d`: `i` contributes the single occurrence of `d` in the loop
    body's `bodyDefs`, so both `before` and `after` contribute none. -/
theorem beforeAfter_notWrites_dest (before after : List Linstr) (i : Linstr)
    (d opn : String) (srcs : List LOperand) (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant (before ++ i :: after) i = true) :
    ∀ j ∈ before ++ after, instrWrites j.li_i d = false := by
  have hcount : (bodyDefs (before ++ i :: after)).count d = 1 := by
    simp only [isLoopInvariant, hli, Bool.and_eq_true] at hinv
    obtain ⟨⟨_, h2⟩, _⟩ := hinv
    rw [beq_iff_eq] at h2; exact h2
  have hbid : bodyDefs (i :: after) = d :: bodyDefs after := by
    simp only [bodyDefs, List.filterMap_cons, hli]
  have hsplit : (bodyDefs (before ++ i :: after)).count d
      = (bodyDefs before).count d + (1 + (bodyDefs after).count d) := by
    rw [bodyDefs, List.filterMap_append, List.count_append, ← bodyDefs, ← bodyDefs,
      hbid, List.count_cons_self]
    omega
  have hzero : (bodyDefs before).count d = 0 ∧ (bodyDefs after).count d = 0 := by
    rw [hsplit] at hcount; omega
  have hnotbef : d ∉ bodyDefs before := by
    rw [← List.count_pos_iff]; omega
  have hnotaft : d ∉ bodyDefs after := by
    rw [← List.count_pos_iff]; omega
  have hnot : d ∉ bodyDefs (before ++ after) := by
    rw [bodyDefs, List.filterMap_append, List.mem_append, ← bodyDefs, ← bodyDefs]
    exact fun h => h.elim hnotbef hnotaft
  intro j hj
  exact instrWrites_false_of_not_bodyDef (before ++ after) j d hj hnot

/-- The hoisted loop body `before ++ after` holds no runtime-indexed memory op,
    does not write `d`, and does not write any register `i`'s sources read, so it
    preserves the invariant that `d` holds the value `i` computes: if `t`
    satisfies it at entry, the post-run state does. -/
theorem holdsD_hoisted (before after : List Linstr) (i : Linstr)
    (d opn : String) (srcs : List LOperand) (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant (before ++ i :: after) i = true)
    (hnmBody : ∀ j ∈ before ++ i :: after, isMemOpn j.li_i = false)
    {w : Nat} {t b : Lstate w}
    (hrun : lsemStraight ((before ++ after).map Linstr.li_i) t = some b)
    (hHolds : applyOpn (stripWidthTag opn) (srcs.map (evalOperand t)) = some (t.lvm d)) :
    applyOpn (stripWidthTag opn) (srcs.map (evalOperand b)) = some (b.lvm d) := by
  have hdW : ∀ x ∈ (before ++ after).map Linstr.li_i, instrWrites x d = false := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact beforeAfter_notWrites_dest before after i d opn srcs hli hinv j hj
  have hnm : ∀ x ∈ (before ++ after).map Linstr.li_i, isMemOpn x = false := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    refine hnmBody j ?_
    rw [List.mem_append] at hj ⊢
    exact hj.imp id (List.mem_cons_of_mem _)
  have hbd : b.lvm d = t.lvm d := lsemStraight_lvm_of_not_writes _ d hnm hrun hdW
  have hsrc : srcs.map (evalOperand b) = srcs.map (evalOperand t) := by
    refine srcs_map_stable ((before ++ after).map Linstr.li_i) srcs hnm hrun ?_
    intro o ho r hr jj hjj
    rw [List.mem_map] at hjj
    obtain ⟨j, hjmem, rfl⟩ := hjj
    have hjIn : j ∈ before ++ i :: after := by
      rw [List.mem_append] at hjmem ⊢
      rcases hjmem with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    exact invariant_srcs_not_written (before ++ i :: after) i d opn srcs hli hinv o ho r hr j hjIn
  rw [hsrc, hbd]; exact hHolds

/-- `isLabelInstr` at the `Linstr` level implies `isLabel` on the underlying
    modeled instruction: both recognise a `Llabel` of the given label. -/
theorem isLabel_of_isLabelInstr (L : LLabel) (lbl : Linstr)
    (h : isLabelInstr L lbl = true) : isLabel L lbl.li_i = true := by
  unfold isLabelInstr at h
  unfold isLabel
  revert h
  cases lbl.li_i <;> intro h <;>
    first
      | (rw [beq_iff_eq] at h ⊢; exact h.symm)
      | exact absurd h (by simp)

/-- The label `L` of a straight-line-prefixed loop header resolves to the header's
    program counter: with a straight-line `pre` (no labels) and `lbl` the header
    `Llabel _ L`, `findLabel` returns `pre.length`. -/
theorem findLabel_header (L : LLabel) (pre rest : List Linstr) (lbl : Linstr)
    (hpre : LprogOptPipeline.bodyIsStraightLine pre = true)
    (hlbl : isLabelInstr L lbl = true) :
    findLabel L ((pre ++ lbl :: rest).map Linstr.li_i) = some pre.length := by
  rw [List.map_append, List.map_cons]
  unfold findLabel
  rw [List.findIdx?_append]
  have h1 : (pre.map Linstr.li_i).findIdx? (isLabel L) = none := by
    have := LprogOptPipeline.findLabel_none_map L pre
      (LprogOptPipeline.straightLine_noLabel pre hpre)
    unfold findLabel at this; exact this
  rw [h1]
  simp only [Option.none_or]
  rw [List.findIdx?_cons, isLabel_of_isLabelInstr L lbl hlbl]
  simp [List.length_map]

/-- Value soundness of the source loop body's `Lopn`: running `before ++ i :: after`
    from `s`, the value `i`'s opcode reads at `s` is defined, because `i` itself
    steps successfully and `before`, which holds no runtime-indexed memory op,
    does not write `i`'s sources. -/
theorem srcs_isSome_of_loopbody {w : Nat} (before after : List Linstr) (i : Linstr)
    (d opn : String) (srcs : List LOperand)
    (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant (before ++ i :: after) i = true)
    (hnmBody : ∀ j ∈ before ++ i :: after, isMemOpn j.li_i = false)
    {s bS : Lstate w}
    (hs : lsemStraight ((before ++ i :: after).map Linstr.li_i) s = some bS) :
    ∃ v, applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) = some v := by
  have hmap : (before ++ i :: after).map Linstr.li_i
      = before.map Linstr.li_i ++ (i.li_i :: after.map Linstr.li_i) := by simp
  have hnmBef : ∀ x ∈ before.map Linstr.li_i, isMemOpn x = false := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hnmBody j (List.mem_append_left _ hj)
  have hnmI : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" :=
    opn_nonmem_of_isMemOpn_false
      (hli ▸ hnmBody i (List.mem_append_right _ (List.mem_cons_self ..)))
  rw [hmap, lsemStraight_append] at hs
  cases hsB : lsemStraight (before.map Linstr.li_i) s with
  | none => rw [hsB] at hs; simp at hs
  | some sB =>
    rw [hsB] at hs
    have hs' : lsemStraight (i.li_i :: after.map Linstr.li_i) sB = some bS := hs
    rw [lsemStraight_cons] at hs'
    cases hstepi : lsemStep i.li_i sB with
    | none => rw [hstepi] at hs'; simp at hs'
    | some s' =>
      rw [hli, LcmdCopyPropagate.lsemStep_reg_nonmem d opn srcs sB hnmI] at hstepi
      cases happ : applyOpn (stripWidthTag opn) (srcs.map (evalOperand sB)) with
      | none => rw [happ] at hstepi; simp at hstepi
      | some v =>
        have hstable : srcs.map (evalOperand sB) = srcs.map (evalOperand s) := by
          refine srcs_map_stable (before.map Linstr.li_i) srcs hnmBef hsB ?_
          intro o ho r hr j hj
          rw [List.mem_map] at hj
          obtain ⟨jj, hjj, rfl⟩ := hj
          refine invariant_srcs_not_written (before ++ i :: after) i d opn srcs hli hinv o ho r hr jj ?_
          rw [List.mem_append]; exact Or.inl hjj
        exact ⟨v, by rw [← hstable]; exact happ⟩

/-- **The offset forward simulation of `hoistOne L i` over one loop iteration.**
    From a source state at the loop body's first instruction (`pre.length + 1`) and
    a hoisted state at its first instruction (`pre.length + 2`, one past the hoisted
    preheader), agreeing off `d` with the hoisted `d` holding the value `i`
    computes, a halting source run is matched by a halting hoisted run reaching an
    equal store. -/
theorem licm_loop
    (P P' : Lprog) (fn : String) {w : Nat}
    (pre before after post : List Linstr) (i lbl backedge : Linstr)
    (d opn : String) (srcs : List LOperand) (cond : LOperand) (L : LLabel)
    (fdS fdH : Lfundef)
    (hgfS : getFundef P fn = some fdS)
    (hgfH : getFundef P' fn = some fdH)
    (hbodyS : fdS.lfd_body = pre ++ lbl :: (before ++ i :: (after ++ backedge :: post)))
    (hbodyH : fdH.lfd_body = pre ++ [i] ++ lbl :: (before ++ (after ++ backedge :: post)))
    (hli : i.li_i = .Lopn [.reg d] opn srcs)
    (hinv : isLoopInvariant (before ++ i :: after) i = true)
    (hnmBody : ∀ j ∈ before ++ i :: after, isMemOpn j.li_i = false)
    (hbefR : ∀ y ∈ before, ∀ r ∈ instrReadRegs y.li_i, r ≠ d)
    (hbe : backedge.li_i = .Lcond cond L)
    (hlbl : isLabelInstr L lbl = true)
    (hpreSL : LprogOptPipeline.bodyIsStraightLine pre = true)
    (hbeforeSL : LprogOptPipeline.bodyIsStraightLine before = true)
    (hafterSL : LprogOptPipeline.bodyIsStraightLine after = true)
    (hpostSL : LprogOptPipeline.bodyIsStraightLine post = true) :
    ∀ (fuel : Nat) (sS sH tS : LstateP w),
      sS.lfn = fn → sH.lfn = fn →
      sS.base.lpc = pre.length + 1 → sH.base.lpc = pre.length + 2 →
      AgreeExcept d sS.base sH.base →
      applyOpn (stripWidthTag opn) (srcs.map (evalOperand sH.base)) = some (sH.base.lvm d) →
      lsemFuel P fuel sS = some tS →
      ∃ (fuel' : Nat) (tH : LstateP w),
        lsemFuel P' fuel' sH = some tH ∧ stateStore tS.base = stateStore tH.base := by
  -- shared structural facts, independent of the fuel and the current states
  have Hfetch : ∀ (u : LstateP w), u.lfn = fn →
      findInstr P u = (fdS.lfd_body.map Linstr.li_i)[u.base.lpc]? :=
    LprogOptPipeline.findInstr_body P fn fdS hgfS
  have Hfetch' : ∀ (u : LstateP w), u.lfn = fn →
      findInstr P' u = (fdH.lfd_body.map Linstr.li_i)[u.base.lpc]? :=
    LprogOptPipeline.findInstr_body P' fn fdH hgfH
  have hbodyS_map : fdS.lfd_body.map Linstr.li_i
      = (pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i
          ++ (backedge :: post).map Linstr.li_i := by
    rw [hbodyS]; simp [List.append_assoc]
  have hbodyH_map : fdH.lfd_body.map Linstr.li_i
      = (pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i
          ++ (backedge :: post).map Linstr.li_i := by
    rw [hbodyH]; simp [List.append_assoc]
  have hlblSrc : findLabel L (fdS.lfd_body.map Linstr.li_i) = some pre.length := by
    rw [hbodyS]; exact findLabel_header L pre _ lbl hpreSL hlbl
  have hpreiSL : LprogOptPipeline.bodyIsStraightLine (pre ++ [i]) = true := by
    rw [LprogOptPipeline.bodyIsStraightLine_append, hpreSL]
    exact LprogOptPipeline.straight_singleton_of_not_ctl i (by simp [LprogOptPipeline.isCtlInstr, hli])
  have hlblHoist : findLabel L (fdH.lfd_body.map Linstr.li_i) = some (pre.length + 1) := by
    have hb' : fdH.lfd_body = (pre ++ [i]) ++ lbl :: (before ++ (after ++ backedge :: post)) := by
      rw [hbodyH]
    rw [hb']
    have := findLabel_header L (pre ++ [i]) (before ++ (after ++ backedge :: post)) lbl hpreiSL hlbl
    simpa using this
  have hnbS : ∀ x ∈ (before ++ i :: after).map Linstr.li_i, LprogOptPipeline.NotBranch x = true := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.mem_append, List.mem_cons] at hj
    rcases hj with hb | rfl | ha
    · exact LprogOptPipeline.notBranch_of_straight before hbeforeSL j.li_i (List.mem_map_of_mem hb)
    · simp [LprogOptPipeline.NotBranch, hli]
    · exact LprogOptPipeline.notBranch_of_straight after hafterSL j.li_i (List.mem_map_of_mem ha)
  have hnbH : ∀ x ∈ (before ++ after).map Linstr.li_i, LprogOptPipeline.NotBranch x = true := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.mem_append] at hj
    rcases hj with hb | ha
    · exact LprogOptPipeline.notBranch_of_straight before hbeforeSL j.li_i (List.mem_map_of_mem hb)
    · exact LprogOptPipeline.notBranch_of_straight after hafterSL j.li_i (List.mem_map_of_mem ha)
  have hss_setcpc : ∀ (x : LstateP w) (f : String) (p : Nat),
      stateStore (x.setcpc f p).base = stateStore x.base := fun _ _ _ => rfl
  -- the backedge program counter
  have hbpS_len : ((pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i).length
      = pre.length + before.length + after.length + 2 := by
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]; omega
  have hbpH_len : ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i).length
      = pre.length + before.length + after.length + 2 := by
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]; omega
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro sS sH tS hSfn hHfn hSpc hHpc hAgree hHolds hfuel
    have hss_next : ∀ (x : LstateP w), stateStore x.nextPc.base = stateStore x.base :=
      fun _ => rfl
    have hstoreLit : ∀ (b : Lstate w) (n : Nat),
        stateStore (⟨{b with lpc := n}, fn⟩ : LstateP w).base = stateStore b := fun _ _ => rfl
    have hnbPost : ∀ x ∈ post.map Linstr.li_i, LprogOptPipeline.NotBranch x = true := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact LprogOptPipeline.notBranch_of_straight post hpostSL j.li_i (List.mem_map_of_mem hj)
    -- 1. the source runs the loop body to the back-edge
    have hSpc' : sS.base.lpc = ((pre ++ [lbl]).map Linstr.li_i).length := by rw [hSpc]; simp
    obtain ⟨bS, hstrS, hleS, htailS⟩ :=
      LprogOptPipeline.fuelRun P fn (fdS.lfd_body.map Linstr.li_i) Hfetch
        ((before ++ i :: after).map Linstr.li_i) hnbS
        ((pre ++ [lbl]).map Linstr.li_i) ((backedge :: post).map Linstr.li_i)
        hbodyS_map sS hSfn hSpc' fuel tS hfuel
    set bp := pre.length + before.length + after.length + 2 with hbpdef
    have hbpS : ((pre ++ [lbl]).map Linstr.li_i).length
        + ((before ++ i :: after).map Linstr.li_i).length = bp := by
      rw [← List.length_append]; exact hbpS_len
    rw [hbpS] at htailS
    -- 2. the hoisted loop body reaches an equal store at the back-edge
    obtain ⟨bH, hstrH, hstoreBH⟩ :=
      hoistableStrong_body_full_agree i before after d opn srcs hli hinv hnmBody hbefR
        hAgree hHolds hstrS
    have hHpc' : sH.base.lpc = ((pre ++ [i, lbl]).map Linstr.li_i).length := by rw [hHpc]; simp
    have hfwdH := LprogOptPipeline.runForward P' fn (fdH.lfd_body.map Linstr.li_i) Hfetch'
      ((before ++ after).map Linstr.li_i) hnbH
      ((pre ++ [i, lbl]).map Linstr.li_i) ((backedge :: post).map Linstr.li_i)
      hbodyH_map sH hHfn hHpc' bH hstrH
    have hbpH : ((pre ++ [i, lbl]).map Linstr.li_i).length
        + ((before ++ after).map Linstr.li_i).length = bp := by
      rw [← List.length_append]; exact hbpH_len
    rw [hbpH] at hfwdH
    set sSbe : LstateP w := ⟨{bS with lpc := bp}, fn⟩ with hsSbe
    set sHbe : LstateP w := ⟨{bH with lpc := bp}, fn⟩ with hsHbe
    have hbeFetchS : (fdS.lfd_body.map Linstr.li_i)[bp]? = some backedge.li_i := by
      have hfh := LprogOptPipeline.fetch_head (fdS.lfd_body.map Linstr.li_i)
        ((pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i)
        [] (post.map Linstr.li_i) backedge.li_i (by rw [hbodyS_map]; simp)
      rw [hbpS_len] at hfh; exact hfh
    have hbeFetchH : (fdH.lfd_body.map Linstr.li_i)[bp]? = some backedge.li_i := by
      have hfh := LprogOptPipeline.fetch_head (fdH.lfd_body.map Linstr.li_i)
        ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i)
        [] (post.map Linstr.li_i) backedge.li_i (by rw [hbodyH_map]; simp)
      rw [hbpH_len] at hfh; exact hfh
    have hfiSbe : findInstr P sSbe = some (LinstrR.Lcond cond L) := by
      rw [hsSbe, Hfetch _ rfl]
      show (fdS.lfd_body.map Linstr.li_i)[bp]? = some (LinstrR.Lcond cond L)
      rw [hbeFetchS, hbe]
    have hfiSbe' : findInstr P' sHbe = some (LinstrR.Lcond cond L) := by
      rw [hsHbe, Hfetch' _ rfl]
      show (fdH.lfd_body.map Linstr.li_i)[bp]? = some (LinstrR.Lcond cond L)
      rw [hbeFetchH, hbe]
    have hstoreBe : stateStore sSbe.base = stateStore sHbe.base := by
      rw [hsSbe, hsHbe]; exact hstoreBH
    have hsSbeLfn : sSbe.lfn = fn := by rw [hsSbe]
    have hsHbeLfn : sHbe.lfn = fn := by rw [hsHbe]
    have hsSbePc : sSbe.base.lpc = bp := by rw [hsSbe]
    have hcondSH : evalOperand sSbe.base cond = evalOperand sHbe.base cond :=
      LprogOptPipeline.evalOperand_congr hstoreBe cond
    have hHoldsBH : applyOpn (stripWidthTag opn) (srcs.map (evalOperand bH)) = some (bH.lvm d) :=
      holdsD_hoisted before after i d opn srcs hli hinv hnmBody hstrH hHolds
    -- 3. the source performs the back-edge step; it takes at least one unit of fuel
    obtain ⟨m1, hm1⟩ : ∃ m1, fuel - ((before ++ i :: after).map Linstr.li_i).length = m1 + 1 := by
      cases hk : fuel - ((before ++ i :: after).map Linstr.li_i).length with
      | zero => rw [hk] at htailS; simp [lsemFuel, hfiSbe] at htailS
      | succ n => exact ⟨n, rfl⟩
    rw [hm1] at htailS
    simp only [lsemFuel, hfiSbe, evalInstrP] at htailS
    have hlenpos : 1 ≤ ((before ++ i :: after).map Linstr.li_i).length := by
      simp only [List.length_map, List.length_append, List.length_cons]; omega
    have hm1lt : m1 < fuel := by omega
    by_cases hcnd : evalOperand sSbe.base cond ≠ 0
    · -- back-edge taken: both loop again
      rw [ite_eq_left hcnd] at htailS
      simp only [hsSbeLfn, evalJump, hgfS, hlblSrc] at htailS
      have hcndH : evalOperand sHbe.base cond ≠ 0 := hcondSH ▸ hcnd
      have hstoreH2 : stateStore (sHbe.setcpc fn (pre.length + 1 + 1)).base = stateStore bH := by
        rw [hss_setcpc, hsHbe]; exact hstoreLit bH bp
      have hAgree2 : AgreeExcept d (sSbe.setcpc fn (pre.length + 1)).base
          (sHbe.setcpc fn (pre.length + 1 + 1)).base := by
        apply agreeExcept_of_stateStore
        rw [hss_setcpc, hss_setcpc]; exact hstoreBe
      have hHolds2 : applyOpn (stripWidthTag opn)
          (srcs.map (evalOperand (sHbe.setcpc fn (pre.length + 1 + 1)).base))
          = some ((sHbe.setcpc fn (pre.length + 1 + 1)).base.lvm d) := by
        have hmapeq : srcs.map (evalOperand (sHbe.setcpc fn (pre.length + 1 + 1)).base)
            = srcs.map (evalOperand bH) :=
          List.map_congr_left (fun o _ => LprogOptPipeline.evalOperand_congr hstoreH2 o)
        have h2 := hstoreH2
        simp only [stateStore, Prod.mk.injEq] at h2
        rw [hmapeq, h2.1]; exact hHoldsBH
      obtain ⟨fuelLoop, tH, hloopH, hstoreT⟩ := ih m1 hm1lt
        (sSbe.setcpc fn (pre.length + 1)) (sHbe.setcpc fn (pre.length + 1 + 1)) tS
        (by simp) (by simp) (by rfl) (by rfl) hAgree2 hHolds2 htailS
      have hstepH : lsemFuel P' (fuelLoop + 1) sHbe = some tH := by
        simp only [lsemFuel, hfiSbe', evalInstrP]
        rw [ite_eq_left hcndH]
        simp only [hsHbeLfn, evalJump, hgfH, hlblHoist]
        exact hloopH
      exact ⟨((before ++ after).map Linstr.li_i).length + (fuelLoop + 1), tH,
        by rw [hfwdH]; exact hstepH, hstoreT⟩
    · -- back-edge not taken: both fall through to the tail and halt
      rw [ite_eq_right hcnd] at htailS
      have hcndH : ¬ evalOperand sHbe.base cond ≠ 0 := hcondSH ▸ hcnd
      -- source runs the tail `post` to the end of the body
      have hnextLfnS : sSbe.nextPc.lfn = fn := hsSbeLfn
      have hpreP_lenS : ((pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i
          ++ [backedge.li_i]).length = bp + 1 := by
        rw [List.length_append, hbpS_len]; simp
      have hnextPcS : sSbe.nextPc.base.lpc
          = ((pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i
              ++ [backedge.li_i]).length := by
        rw [hpreP_lenS, LstateP.lpc_nextPc, hsSbePc]
      obtain ⟨bP, hstrP, hleP, htailP⟩ :=
        LprogOptPipeline.fuelRun P fn (fdS.lfd_body.map Linstr.li_i) Hfetch
          (post.map Linstr.li_i) hnbPost
          ((pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i
            ++ [backedge.li_i]) []
          (by rw [hbodyS_map]; simp) sSbe.nextPc hnextLfnS hnextPcS m1 tS htailS
      -- that end index is past the body, so the source has halted at `tS`
      have hlenEqS : ((pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i
          ++ [backedge.li_i]).length + (post.map Linstr.li_i).length
          = (fdS.lfd_body.map Linstr.li_i).length := by
        rw [hbodyS_map]; simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil]; omega
      have hhaltFetchS : findInstr P (⟨{bP with lpc :=
          ((pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i
            ++ [backedge.li_i]).length + (post.map Linstr.li_i).length}, fn⟩ : LstateP w) = none := by
        rw [Hfetch _ rfl]
        show (fdS.lfd_body.map Linstr.li_i)[((pre ++ [lbl]).map Linstr.li_i
          ++ (before ++ i :: after).map Linstr.li_i ++ [backedge.li_i]).length
          + (post.map Linstr.li_i).length]? = none
        rw [hlenEqS]; exact List.getElem?_eq_none (Nat.le_refl _)
      have htEqS : tS = (⟨{bP with lpc := ((pre ++ [lbl]).map Linstr.li_i
          ++ (before ++ i :: after).map Linstr.li_i ++ [backedge.li_i]).length
          + (post.map Linstr.li_i).length}, fn⟩ : LstateP w) := by
        have hhalt := lsemFuel_halt P (m1 - (post.map Linstr.li_i).length) _ hhaltFetchS
        rw [hhalt] at htailP; exact (Option.some.inj htailP).symm
      have hstoreTS : stateStore tS.base = stateStore bP := by
        rw [htEqS]; exact hstoreLit bP _
      -- the hoisted program mirrors: fall through, run `post`, halt at an equal store
      have hstoreNext : stateStore sSbe.nextPc.base = stateStore sHbe.nextPc.base := by
        rw [hss_next, hss_next]; exact hstoreBe
      obtain ⟨bP', hstrP', hstoreP'⟩ :
          ∃ bP', lsemStraight (post.map Linstr.li_i) sHbe.nextPc.base = some bP'
            ∧ stateStore bP' = stateStore bP := by
        have hmap := LprogOptPipeline.lsemStraight_stateStore (post.map Linstr.li_i) hstoreNext.symm
        rw [hstrP] at hmap
        cases hlo : lsemStraight (post.map Linstr.li_i) sHbe.nextPc.base with
        | none => rw [hlo] at hmap; simp at hmap
        | some bP' =>
          rw [hlo] at hmap; simp only [Option.map_some] at hmap
          exact ⟨bP', rfl, Option.some.inj hmap⟩
      have hnextLfnH : sHbe.nextPc.lfn = fn := hsHbeLfn
      have hsHbePc : sHbe.base.lpc = bp := by rw [hsHbe]
      have hpreP_lenH : ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i
          ++ [backedge.li_i]).length = bp + 1 := by
        rw [List.length_append, hbpH_len]; simp
      have hnextPcH : sHbe.nextPc.base.lpc
          = ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i
              ++ [backedge.li_i]).length := by
        rw [hpreP_lenH, LstateP.lpc_nextPc, hsHbePc]
      have hfwdPH := LprogOptPipeline.runForward P' fn (fdH.lfd_body.map Linstr.li_i) Hfetch'
        (post.map Linstr.li_i) hnbPost
        ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i
          ++ [backedge.li_i]) []
        (by rw [hbodyH_map]; simp) sHbe.nextPc hnextLfnH hnextPcH bP' hstrP'
      have hlenEqH : ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i
          ++ [backedge.li_i]).length + (post.map Linstr.li_i).length
          = (fdH.lfd_body.map Linstr.li_i).length := by
        rw [hbodyH_map]; simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil]; omega
      have hhaltFetchH : findInstr P' (⟨{bP' with lpc :=
          ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i
            ++ [backedge.li_i]).length + (post.map Linstr.li_i).length}, fn⟩ : LstateP w) = none := by
        rw [Hfetch' _ rfl]
        show (fdH.lfd_body.map Linstr.li_i)[((pre ++ [i, lbl]).map Linstr.li_i
          ++ (before ++ after).map Linstr.li_i ++ [backedge.li_i]).length
          + (post.map Linstr.li_i).length]? = none
        rw [hlenEqH]; exact List.getElem?_eq_none (Nat.le_refl _)
      -- assemble the hoisted run: loop body, back-edge fall-through, tail, halt
      refine ⟨((before ++ after).map Linstr.li_i).length + (1 + (post.map Linstr.li_i).length),
        ⟨{bP' with lpc := ((pre ++ [i, lbl]).map Linstr.li_i ++ (before ++ after).map Linstr.li_i
            ++ [backedge.li_i]).length + (post.map Linstr.li_i).length}, fn⟩, ?_, ?_⟩
      · rw [hfwdH]
        have hstep : lsemFuel P' (1 + (post.map Linstr.li_i).length) sHbe
            = lsemFuel P' (post.map Linstr.li_i).length sHbe.nextPc := by
          rw [Nat.add_comm]
          simp only [lsemFuel, hfiSbe', evalInstrP]
          rw [ite_eq_right hcndH]
        rw [hstep]
        have hpost0 := hfwdPH 0
        rw [Nat.add_zero] at hpost0
        rw [hpost0]
        exact lsemFuel_halt P' 0 _ hhaltFetchH
      · rw [hstoreTS, hstoreLit bP' _]; exact hstoreP'.symm

/-- The store-preservation statement for `hoistOne L i` over the do-while shape
    `IsHoistableDoWhile`: running the source program from a function entry (pc 0)
    and running the hoisted program from the same entry state reach the same store
    over the labeled, program-counter-indexed `lsem`.

    The per-iteration store step is `hoistableStrong_body_full_agree`: from states
    agreeing off `d`, one pass of the source loop body (which runs `i`) and the
    hoisted loop body (which omits `i`) reach fully equal stores, the hoisted
    program carrying `d` at the preheader value. The full statement is the offset
    forward simulation over `lsem`: a strong-fuel induction in the style of
    `LprogOptPipeline.sim_main` whose phase relation is full store equality in
    `pre` and `post`, source and hoisted at the loop header with equal store, and
    the loop body run under a one-instruction program-counter offset (the hoisted
    preheader shifts the header and `before` by one) resynchronising at the
    back-edge, where the label `L` resolves to the header in the source body and to
    one past it in the hoisted body. -/
theorem LICMEntryStorePreservedGoalSL (L : LLabel) (i : Linstr)
    (P : Lprog) {w : Nat} (s t : LstateP w) (fd : Lfundef)
    (hfd : getFundef P s.lfn = some fd) (hpc : s.base.lpc = 0)
    (hnm : ∀ j ∈ fd.lfd_body, isMemOpn j.li_i = false)
    (hdw : IsHoistableDoWhile L i fd) (hrun : lsem P s t) :
    ∃ t', lsem (mapBodies (hoistOne L i) P) s t' ∧ stateStore t.base = stateStore t'.base := by
  obtain ⟨pre, before, after, post, lbl, backedge, d, opn, srcs, hbodyS, hlbl, ⟨cond, hbe⟩,
    hbef, hli, hinv, hbefR, hpreSL, hbeforeSL, hafterSL, hpostSL⟩ := hdw
  have hnmBody : ∀ j ∈ before ++ i :: after, isMemOpn j.li_i = false := by
    intro j hj
    refine hnm j ?_
    rw [hbodyS]
    simp only [List.mem_append, List.mem_cons] at hj ⊢
    tauto
  have hnmI : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" :=
    opn_nonmem_of_isMemOpn_false
      (hli ▸ hnmBody i (List.mem_append_right _ (List.mem_cons_self ..)))
  obtain ⟨fuel, hfuel⟩ := hrun
  have hstoreLit : ∀ (b : Lstate w) (n : Nat),
      stateStore (⟨{b with lpc := n}, s.lfn⟩ : LstateP w).base = stateStore b := fun _ _ => rfl
  have hssN : ∀ (x : Lstate w), stateStore x.nextPc = stateStore x := fun _ => rfl
  have hpre0lbl : ∀ y ∈ pre, isLabelInstr L y = false := by
    intro y hy
    have h0 := LprogOptPipeline.straightLine_noLabel pre hpreSL y hy
    simp only [isLabelInstr]; revert h0; cases y.li_i <;> simp [LprogOptPipeline.isLbl]
  have hbodyH_eq : hoistOne L i fd.lfd_body
      = pre ++ [i] ++ lbl :: (before ++ (after ++ backedge :: post)) := by
    rw [hbodyS]
    exact hoistOne_decomp L i pre lbl before (after ++ backedge :: post) hpre0lbl hlbl hbef
      (matchHoist_refl_lopn i d opn srcs hli)
  have hgfH : getFundef (mapBodies (hoistOne L i) P) s.lfn
      = some { fd with lfd_body := hoistOne L i fd.lfd_body } := by
    rw [LprogOptPipeline.getFundef_mapBodies, hfd]; rfl
  have Hfetch : ∀ (u : LstateP w), u.lfn = s.lfn →
      findInstr P u = (fd.lfd_body.map Linstr.li_i)[u.base.lpc]? :=
    LprogOptPipeline.findInstr_body P s.lfn fd hfd
  have Hfetch' : ∀ (u : LstateP w), u.lfn = s.lfn →
      findInstr (mapBodies (hoistOne L i) P) u
        = (({ fd with lfd_body := hoistOne L i fd.lfd_body } : Lfundef).lfd_body.map Linstr.li_i)[u.base.lpc]? :=
    LprogOptPipeline.findInstr_body (mapBodies (hoistOne L i) P) s.lfn _ hgfH
  have hlblForm : ∃ lk ll, lbl.li_i = .Llabel lk ll := by
    revert hlbl; unfold isLabelInstr
    cases lbl.li_i <;> intro h <;> first | exact ⟨_, _, rfl⟩ | exact absurd h (by simp)
  obtain ⟨lk, ll, hlbleq⟩ := hlblForm
  have hnbPreLbl : ∀ x ∈ (pre ++ [lbl]).map Linstr.li_i, LprogOptPipeline.NotBranch x = true := by
    intro x hx
    rw [List.mem_map] at hx; obtain ⟨j, hj, rfl⟩ := hx
    rw [List.mem_append, List.mem_singleton] at hj
    rcases hj with hp | rfl
    · exact LprogOptPipeline.notBranch_of_straight pre hpreSL j.li_i (List.mem_map_of_mem hp)
    · rw [hlbleq]; rfl
  have hnbPreILbl : ∀ x ∈ (pre ++ [i, lbl]).map Linstr.li_i, LprogOptPipeline.NotBranch x = true := by
    intro x hx
    rw [List.mem_map] at hx; obtain ⟨j, hj, rfl⟩ := hx
    rw [List.mem_append] at hj
    rcases hj with hp | hil
    · exact LprogOptPipeline.notBranch_of_straight pre hpreSL j.li_i (List.mem_map_of_mem hp)
    · rw [List.mem_cons, List.mem_singleton] at hil
      rcases hil with rfl | rfl
      · simp [LprogOptPipeline.NotBranch, hli]
      · rw [hlbleq]; rfl
  have hnbBody : ∀ x ∈ (before ++ i :: after).map Linstr.li_i, LprogOptPipeline.NotBranch x = true := by
    intro x hx
    rw [List.mem_map] at hx; obtain ⟨j, hj, rfl⟩ := hx
    rw [List.mem_append, List.mem_cons] at hj
    rcases hj with hb | rfl | ha
    · exact LprogOptPipeline.notBranch_of_straight before hbeforeSL j.li_i (List.mem_map_of_mem hb)
    · simp [LprogOptPipeline.NotBranch, hli]
    · exact LprogOptPipeline.notBranch_of_straight after hafterSL j.li_i (List.mem_map_of_mem ha)
  have hbodyPre : fd.lfd_body.map Linstr.li_i
      = [] ++ (pre ++ [lbl]).map Linstr.li_i
          ++ (before ++ i :: (after ++ backedge :: post)).map Linstr.li_i := by
    rw [hbodyS]; simp
  have hbodyMid : fd.lfd_body.map Linstr.li_i
      = (pre ++ [lbl]).map Linstr.li_i ++ (before ++ i :: after).map Linstr.li_i
          ++ (backedge :: post).map Linstr.li_i := by
    rw [hbodyS]; simp [List.append_assoc]
  have hbodyPreH : ({ fd with lfd_body := hoistOne L i fd.lfd_body } : Lfundef).lfd_body.map Linstr.li_i
      = [] ++ (pre ++ [i, lbl]).map Linstr.li_i
          ++ (before ++ (after ++ backedge :: post)).map Linstr.li_i := by
    show (hoistOne L i fd.lfd_body).map Linstr.li_i = _
    rw [hbodyH_eq]; simp
  -- 1. the source runs `pre ++ [lbl]` to the loop header
  obtain ⟨bPreLbl, hstrPreLbl, hlePre, htailPre⟩ :=
    LprogOptPipeline.fuelRun P s.lfn (fd.lfd_body.map Linstr.li_i) Hfetch
      ((pre ++ [lbl]).map Linstr.li_i) hnbPreLbl []
      ((before ++ i :: (after ++ backedge :: post)).map Linstr.li_i)
      hbodyPre s rfl (by rw [hpc]; rfl) fuel t hfuel
  simp only [List.length_nil, Nat.zero_add] at htailPre
  set sLT : LstateP w := ⟨{bPreLbl with lpc := ((pre ++ [lbl]).map Linstr.li_i).length}, s.lfn⟩
    with hSLT
  -- 2. the source's first loop body run shows `i`'s opcode is defined at the header
  obtain ⟨bS, hstrS, _, _⟩ :=
    LprogOptPipeline.fuelRun P s.lfn (fd.lfd_body.map Linstr.li_i) Hfetch
      ((before ++ i :: after).map Linstr.li_i) hnbBody
      ((pre ++ [lbl]).map Linstr.li_i) ((backedge :: post).map Linstr.li_i)
      hbodyMid sLT rfl (by rw [hSLT]) (fuel - ((pre ++ [lbl]).map Linstr.li_i).length) t htailPre
  obtain ⟨v, hAppV0⟩ :=
    srcs_isSome_of_loopbody before after i d opn srcs hli hinv hnmBody hstrS
  -- 3. peel the `pre` run and the label step
  rw [show (pre ++ [lbl]).map Linstr.li_i = pre.map Linstr.li_i ++ [lbl.li_i] from by simp,
    lsemStraight_append] at hstrPreLbl
  cases hpre0 : lsemStraight (pre.map Linstr.li_i) s.base with
  | none => rw [hpre0] at hstrPreLbl; simp at hstrPreLbl
  | some bPre0 =>
    have hbindsome : ∀ (g : Lstate w → Option (Lstate w)), (some bPre0).bind g = g bPre0 :=
      fun _ => rfl
    rw [hpre0, hbindsome, lsemStraight_singleton, hlbleq] at hstrPreLbl
    simp only [lsemStep] at hstrPreLbl
    have hbPreLbl : bPreLbl = bPre0.nextPc := (Option.some.inj hstrPreLbl).symm
    have hstoreLT : stateStore sLT.base = stateStore bPre0 := by
      rw [hSLT]; show stateStore bPreLbl = stateStore bPre0; rw [hbPreLbl]; exact hssN bPre0
    have hAppV : applyOpn (stripWidthTag opn) (srcs.map (evalOperand bPre0)) = some v := by
      rw [show srcs.map (evalOperand bPre0) = srcs.map (evalOperand sLT.base) from
        List.map_congr_left (fun o _ => LprogOptPipeline.evalOperand_congr hstoreLT.symm o)]
      exact hAppV0
    -- 4. build the hoisted preheader run
    have hstrH0 : lsemStraight ((pre ++ [i, lbl]).map Linstr.li_i) s.base
        = some (((bPre0.setReg d v).nextPc).nextPc) := by
      rw [show (pre ++ [i, lbl]).map Linstr.li_i = pre.map Linstr.li_i ++ (i.li_i :: [lbl.li_i]) from by simp,
        lsemStraight_append, hpre0, hbindsome, lsemStraight_cons, hli]
      simp only [LcmdCopyPropagate.lsemStep_reg_nonmem d opn srcs bPre0 hnmI, hAppV]
      rw [lsemStraight_singleton, hlbleq]
      simp only [lsemStep]
    have hAgreeBase : AgreeExcept d bPre0 (bPre0.setReg d v) := by
      refine ⟨rfl, ?_⟩
      intro r hr
      show bPre0.lvm r = (if r = d then v else bPre0.lvm r)
      rw [ite_eq_right hr]
    -- 5. run the hoisted preheader forward
    have hfwdPreH := LprogOptPipeline.runForward (mapBodies (hoistOne L i) P) s.lfn
      (({ fd with lfd_body := hoistOne L i fd.lfd_body } : Lfundef).lfd_body.map Linstr.li_i) Hfetch'
      ((pre ++ [i, lbl]).map Linstr.li_i) hnbPreILbl []
      ((before ++ (after ++ backedge :: post)).map Linstr.li_i)
      hbodyPreH s rfl (by rw [hpc]; rfl) (((bPre0.setReg d v).nextPc).nextPc) hstrH0
    simp only [List.length_nil, Nat.zero_add] at hfwdPreH
    set hLT : LstateP w :=
      ⟨{((bPre0.setReg d v).nextPc).nextPc with lpc := ((pre ++ [i, lbl]).map Linstr.li_i).length}, s.lfn⟩
      with hHLT
    have hstoreHLT : stateStore hLT.base = stateStore (bPre0.setReg d v) := by
      rw [hHLT]; exact (hstoreLit ((bPre0.setReg d v).nextPc.nextPc) _).trans
        ((hssN _).trans (hssN _))
    have hAgree : AgreeExcept d sLT.base hLT.base := by
      have e1 := hstoreLT; have e2 := hstoreHLT
      simp only [stateStore, Prod.mk.injEq] at e1 e2
      refine ⟨?_, ?_⟩
      · rw [e1.2, e2.2]; exact hAgreeBase.1
      · intro r hr; rw [e1.1, e2.1]; exact hAgreeBase.2 r hr
    have hHolds : applyOpn (stripWidthTag opn) (srcs.map (evalOperand hLT.base))
        = some (hLT.base.lvm d) := by
      have hne : ∀ o ∈ srcs, ∀ r ∈ operandReads o, r ≠ d := by
        intro o ho r hr
        exact invariant_srcs_ne_dest (before ++ i :: after) i d opn srcs
          (by rw [List.mem_append]; exact Or.inr (List.mem_cons_self ..)) hli hinv r
          (by rw [List.mem_flatMap]; exact ⟨o, ho, hr⟩)
      have hmapeq : srcs.map (evalOperand hLT.base) = srcs.map (evalOperand bPre0) := by
        apply List.map_congr_left
        intro o ho
        rw [LprogOptPipeline.evalOperand_congr hstoreHLT o]
        exact (evalOperand_agreeExcept d hAgreeBase o (hne o ho)).symm
      have hlvmd : hLT.base.lvm d = v := by
        rw [show hLT.base.lvm = (bPre0.setReg d v).lvm from congrArg Prod.fst hstoreHLT]
        simp [Lstate.lvm_setReg]
      rw [hmapeq, hlvmd]; exact hAppV
    -- 6. apply the offset simulation over the loop
    obtain ⟨fuelLoop, tH, hloopH, hstoreT⟩ :=
      licm_loop P (mapBodies (hoistOne L i) P) s.lfn pre before after post i lbl backedge
        d opn srcs cond L fd { fd with lfd_body := hoistOne L i fd.lfd_body }
        hfd hgfH hbodyS hbodyH_eq hli hinv hnmBody hbefR hbe hlbl hpreSL hbeforeSL hafterSL
        hpostSL
        (fuel - ((pre ++ [lbl]).map Linstr.li_i).length) sLT hLT t
        rfl rfl (by rw [hSLT]; simp) (by rw [hHLT]; simp) hAgree hHolds htailPre
    -- 7. assemble the whole hoisted run
    refine ⟨tH, ⟨((pre ++ [i, lbl]).map Linstr.li_i).length + fuelLoop, ?_⟩, hstoreT⟩
    rw [hfwdPreH]; exact hloopH

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLICM
