/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-!
# The branch channel along the executed trace of a linear-IR program

`JasminLsemRobust.lsemLeak` walks an instruction *list*: it threads the state
through `lsemStep` but never follows a jump, so a `Lcond` contributes one
`LLeak.branch` wherever it sits in the list, whatever the state. This module
defines `lsemLeakP`, the leakage trace accumulated along the **executed** trace
of `JasminLsemLabeled.lsemStepP` — the pc-following program semantics, whose
`Lcond` arm reads the condition operand out of the state and jumps or falls
through. The number and position of the `LLeak.branch` events in `lsemLeakP` is
therefore a function of the state, and the branch channel carries content.

## The results

`lsemLeakP_no_branch` is the positive statement for the straight-line fragment:
a program whose every instruction is `IsStraightLine` (`Lopn`/`Llabel`/`Lalign`
— no `Lcond`, `Lgoto`, `Lcall`, `Lret`, `Ligoto`, `LstoreLabel`, `Lsyscall`)
executes no conditional branch, so the branch channel of its executed trace is
empty from every state and every fuel. `lsemLeakP_straightLine_pc_determined`
adds that for such a program the whole executed-trace leak is fixed by the
current function name and program counter, given that every fetched instruction
steps successfully. `progStraightLine_straightOps` places the linearizer-emitted
`.var`-chain `JasminLsemSimulation.straightOps` in that fragment.

`secretBranchTrace_differs` is the negative control: `secretBranchProg` is a
three-instruction program whose executed trace contains **one** branch event
when the register `"sec"` is non-zero and **two** when it is zero, so its branch
channel differs between two states that agree everywhere except on `"sec"`.

## Scope

The positive theorems are about the straight-line fragment only, and they say
"this program executes no conditional branch", not "this program is
constant-time on the branch channel" — the branch channel is empty here because
nothing branches, and the statement is worth having only as that.

The emitted counted loop (`X86Backend.LprogControlFlow.loopLcmd`, and the
executable back-edge form `JasminLsemLoop.loopLR`) is a `Lcond` back edge and is
**outside** `ProgStraightLine`. Its existing constant-time result
`JasminLsemLoop.loopLR_lsemLeak_state_independent` is over the list-walking
`lsemLeak`, which traverses the back edge once rather than once per iteration;
no theorem here or elsewhere in this tree computes the executed-trace branch
channel of that loop, which would be one branch event per iteration of the
public trip count. That is the next statement this model makes sayable.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.ControlFlowCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-! ## 1. The leakage trace along the executed trace -/

/-- `lsemLeakP P fuel s`: the leakage trace of the instructions the program `P`
    actually executes from `s`, for up to `fuel` steps. At each step the
    instruction at the current `(lfn, lpc)` is fetched with `findInstr`, its
    `linstrLeak` is emitted, and the next state is `evalInstrP` — which for a
    `Lcond` reads the condition operand out of the state and either jumps to the
    label or falls through. The trace stops at a halted state (`findInstr` is
    `none`) or at fuel exhaustion; a failed step (`evalInstrP` is `none`) emits
    the fetched instruction's leak and stops there.

    The difference from `JasminLsemRobust.lsemLeak` is the traversal: `lsemLeak`
    walks the instruction list in order, so a `Lcond` contributes one `branch`
    event at its list position regardless of the state; `lsemLeakP` follows the
    jump, so the branch events it emits depend on the state. -/
def lsemLeakP (P : Lprog) {w : Nat} : Nat → LstateP w → List LLeak
  | 0, _ => []
  | fuel + 1, s =>
      match findInstr P s with
      | none => []
      | some i =>
          match evalInstrP P i s with
          | some s' => linstrLeak i ++ lsemLeakP P fuel s'
          | none => linstrLeak i

@[simp] theorem lsemLeakP_zero (P : Lprog) {w : Nat} (s : LstateP w) :
    lsemLeakP P 0 s = [] := rfl

theorem lsemLeakP_succ (P : Lprog) {w : Nat} (fuel : Nat) (s : LstateP w) :
    lsemLeakP P (fuel + 1) s =
      match findInstr P s with
      | none => []
      | some i =>
          match evalInstrP P i s with
          | some s' => linstrLeak i ++ lsemLeakP P fuel s'
          | none => linstrLeak i := rfl

/-! ## 2. The straight-line fragment -/

/-- `ProgStraightLine P`: every instruction of every function of `P` is
    `IsStraightLine` — an `Lopn`, an `Llabel` or an `Lalign`. Such a program
    contains no `Lcond` and no `Lgoto`, hence no instruction whose `linstrLeak`
    is a `LLeak.branch`. -/
def ProgStraightLine (P : Lprog) : Prop :=
  ∀ p ∈ P.lp_funcs, ∀ li ∈ p.2.lfd_body, IsStraightLine li.li_i = true

/-- Every instruction `findInstr` fetches from a straight-line program is
    straight-line. -/
theorem isStraightLine_of_findInstr {P : Lprog} (h : ProgStraightLine P) {w : Nat}
    {s : LstateP w} {i : LinstrR} (hf : findInstr P s = some i) :
    IsStraightLine i = true := by
  rw [findInstr] at hf
  cases hg : getFundef P s.lfn with
  | none => rw [hg] at hf; exact absurd hf (by simp)
  | some fd =>
    rw [hg] at hf
    obtain ⟨li, hli, hieq⟩ := Option.map_eq_some_iff.mp hf
    rw [getFundef] at hg
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hg
    have hpmem : p ∈ P.lp_funcs := List.mem_of_find?_eq_some hp
    subst hieq
    subst hpeq
    exact h p hpmem li (List.mem_of_getElem? hli)

/-- **The straight-line fragment executes no conditional branch.** For a program
    all of whose instructions are `Lopn`/`Llabel`/`Lalign`, the branch channel of
    the executed trace is empty, from every state and every fuel. This is a
    statement about what the program contains, not a constant-time statement: the
    channel is empty because no instruction of the fragment emits a branch
    event. -/
theorem lsemLeakP_no_branch {P : Lprog} (h : ProgStraightLine P) {w : Nat} :
    ∀ (fuel : Nat) (s : LstateP w),
      (lsemLeakP P fuel s).filter LLeak.isBranch = [] := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [lsemLeakP_succ]
    cases hf : findInstr P s with
    | none => simp only; rfl
    | some i =>
      have hi : IsStraightLine i = true := isStraightLine_of_findInstr h hf
      have hhead : (linstrLeak i).filter LLeak.isBranch = [] := by
        cases i <;> simp_all [IsStraightLine, linstrLeak, LLeak.isBranch]
      cases hs : evalInstrP P i s with
      | none => simp only [hs]; exact hhead
      | some s' =>
        simp only [hs, List.filter_append, hhead, List.nil_append]
        exact ih s'

/-! ## 3. The straight-line executed trace is fixed by the program counter -/

/-- `findInstr` reads only the current function name and program counter, so two
    states agreeing on those fetch the same instruction. -/
theorem findInstr_congr (P : Lprog) {w : Nat} (s₁ s₂ : LstateP w)
    (hfn : s₁.lfn = s₂.lfn) (hpc : s₁.base.lpc = s₂.base.lpc) :
    findInstr P s₁ = findInstr P s₂ := by
  rw [findInstr, findInstr, hfn, hpc]

/-- **The executed-trace leak of a straight-line program is fixed by `(lfn, lpc)`.**
    For a program all of whose instructions are straight-line, and under the
    hypothesis that every fetched instruction steps successfully from every state,
    two states agreeing on the current function name and program counter — and
    differing arbitrarily on every register and every memory cell — produce the
    same executed-trace leakage.

    The straight-line arms advance the pc by one (`lsemStep_lpc_succ`) and leave
    the function name alone, so both runs stay in lockstep on `(lfn, lpc)` and
    fetch the same instruction at each step; `linstrLeak` reads only the
    instruction. The hypothesis `ProgStraightLine` is what rules out a `Lcond`,
    whose next pc reads a register value; §4 exhibits a program where dropping it
    makes the conclusion false. -/
theorem lsemLeakP_straightLine_pc_determined {P : Lprog} {w : Nat}
    (hsl : ProgStraightLine P)
    (hstep : ∀ (s : LstateP w) (i : LinstrR),
      findInstr P s = some i → (evalInstrP P i s).isSome) :
    ∀ (fuel : Nat) (s₁ s₂ : LstateP w), s₁.lfn = s₂.lfn →
      s₁.base.lpc = s₂.base.lpc → lsemLeakP P fuel s₁ = lsemLeakP P fuel s₂ := by
  intro fuel
  induction fuel with
  | zero => intro s₁ s₂ _ _; rfl
  | succ n ih =>
    intro s₁ s₂ hfn hpc
    have hfc : findInstr P s₁ = findInstr P s₂ := findInstr_congr P s₁ s₂ hfn hpc
    rw [lsemLeakP_succ, lsemLeakP_succ]
    cases hf : findInstr P s₂ with
    | none => simp only [hfc, hf]
    | some i =>
      have hf1 : findInstr P s₁ = some i := by rw [hfc]; exact hf
      have hi : IsStraightLine i = true := isStraightLine_of_findInstr hsl hf
      obtain ⟨t₁, ht₁⟩ := Option.isSome_iff_exists.mp (hstep s₁ i hf1)
      obtain ⟨t₂, ht₂⟩ := Option.isSome_iff_exists.mp (hstep s₂ i hf)
      -- both steps go through increment 1's `lsemStep` on the base state
      rw [evalInstrP_straightLine P i s₁ hi] at ht₁
      rw [evalInstrP_straightLine P i s₂ hi] at ht₂
      obtain ⟨b₁, hb₁, hbe₁⟩ := Option.map_eq_some_iff.mp ht₁
      obtain ⟨b₂, hb₂, hbe₂⟩ := Option.map_eq_some_iff.mp ht₂
      have hpc₁ : b₁.lpc = s₁.base.lpc + 1 := lsemStep_lpc_succ i s₁.base b₁ hi hb₁
      have hpc₂ : b₂.lpc = s₂.base.lpc + 1 := lsemStep_lpc_succ i s₂.base b₂ hi hb₂
      have ht₁' : evalInstrP P i s₁ = some t₁ := by
        rw [evalInstrP_straightLine P i s₁ hi]; exact ht₁
      have ht₂' : evalInstrP P i s₂ = some t₂ := by
        rw [evalInstrP_straightLine P i s₂ hi]; exact ht₂
      simp only [hf1, ht₁', ht₂']
      refine congrArg (linstrLeak i ++ ·) (ih t₁ t₂ ?_ ?_)
      · rw [← hbe₁, ← hbe₂]; exact hfn
      · rw [← hbe₁, ← hbe₂]; show b₁.lpc = b₂.lpc
        rw [hpc₁, hpc₂, hpc]

/-! ## 4. The linearizer's straight-line output lies in the fragment -/

/-- A one-function program is straight-line when its body is. -/
theorem progStraightLine_singletonProg (fn : String) (body : List LinstrR)
    (h : ∀ i ∈ body, IsStraightLine i = true) :
    ProgStraightLine (singletonProg fn body) := by
  intro p hp li hli
  simp only [singletonProg, List.mem_singleton] at hp
  subst hp
  simp only [List.mem_map] at hli
  obtain ⟨ir, hir, hieq⟩ := hli
  subst hieq
  exact h ir hir

/-- Every instruction of the linearizer-emitted `.var`-chain `straightOps` is an
    `Lopn` (`JasminLsemRobust.opToLinstrR_isLopn`), hence straight-line. -/
theorem straightOps_isStraightLine {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (nArgs : Nat) :
    ∀ (curDepth : Nat), ∀ i ∈ straightOps nArgs com curDepth, IsStraightLine i = true := by
  induction com with
  | ret v => intro curDepth i hi; simp [straightOps] at hi
  | var e body ih =>
    intro curDepth i hi
    simp only [straightOps, List.mem_cons] at hi
    rcases hi with rfl | hi
    · obtain ⟨opn, dsts, srcs, hop⟩ :=
        opToLinstrR_isLopn e.op (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none) e)
      rw [hop]; rfl
    · exact ih (curDepth + 1) i hi

/-- The program holding a linearizer-emitted `.var`-chain is in the straight-line
    fragment, so §2 and §3 apply to it. -/
theorem progStraightLine_straightOps {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fn : String) (com : Com jasminDialect Γ t) (nArgs curDepth : Nat) :
    ProgStraightLine (singletonProg fn (straightOps nArgs com curDepth)) :=
  progStraightLine_singletonProg fn _ (straightOps_isStraightLine com nArgs curDepth)

/-! ## 5. The negative control: a program whose branch channel reads a register

The positive theorems hold of the straight-line fragment. Dropping
`ProgStraightLine` makes them false, and the witness is a branch-channel
difference: the executed trace of `secretBranchProg` contains one branch event
from a state with `"sec" ≠ 0` and two from a state with `"sec" = 0`. -/

/-- The label the conditional jumps to. -/
def skipLabel : LLabel := 7

/-- A three-instruction body: a conditional jump on `"sec"` over a second
    conditional jump on `"zero"`, followed by the target label. From a state with
    `"sec" ≠ 0` the first jump is taken and the second conditional is never
    fetched; from a state with `"sec" = 0` both conditionals execute. -/
def secretBranchBody : List LinstrR :=
  [ .Lcond (.reg "sec") skipLabel
  , .Lcond (.reg "zero") skipLabel
  , .Llabel .internal skipLabel ]

/-- The one-function program holding `secretBranchBody`. -/
def secretBranchProg : Lprog := singletonProg "f" secretBranchBody

/-- The initial state of `secretBranchProg` with `"sec"` set to `v` and every
    other register zero. -/
def secretBranchState (v : BitVec 64) : LstateP 64 :=
  { base := { lvm := fun r => if r = "sec" then v else 0 }, lfn := "f" }

/-- `secretBranchProg` is not straight-line: its first instruction is a
    `Lcond`. -/
theorem secretBranchProg_not_straightLine : ¬ ProgStraightLine secretBranchProg := by
  intro h
  have := h ("f", { lfd_body := secretBranchBody.map (fun ir => ⟨0, ir⟩) })
    (by simp [secretBranchProg, singletonProg])
    ⟨0, .Lcond (.reg "sec") skipLabel⟩ (by simp [secretBranchBody])
  exact absurd this (by decide)

/-- From a state with `"sec" = 1` the first conditional jumps past the second, so
    the executed trace holds a single branch event. -/
theorem secretBranchTrace_one :
    lsemLeakP secretBranchProg 4 (secretBranchState 1) = [LLeak.branch] := rfl

/-- From a state with `"sec" = 0` the first conditional falls through and the
    second executes, so the executed trace holds two branch events. -/
theorem secretBranchTrace_two :
    lsemLeakP secretBranchProg 4 (secretBranchState 0) = [LLeak.branch, LLeak.branch] := rfl

/-- **The negative control.** Two states of `secretBranchProg` that agree on
    every register except `"sec"` produce executed traces whose **branch
    channels** differ: one branch event against two. The branch channel of
    `lsemLeakP` is therefore not a function of the program text, and the
    `ProgStraightLine` hypothesis of §2 and §3 is what excludes this program. -/
theorem secretBranchTrace_differs :
    (lsemLeakP secretBranchProg 4 (secretBranchState 1)).filter LLeak.isBranch
      ≠ (lsemLeakP secretBranchProg 4 (secretBranchState 0)).filter LLeak.isBranch := by
  rw [secretBranchTrace_one, secretBranchTrace_two]
  decide

/-- The whole leakage traces differ too, not only their branch channels. -/
theorem secretBranchLeak_differs :
    lsemLeakP secretBranchProg 4 (secretBranchState 1)
      ≠ lsemLeakP secretBranchProg 4 (secretBranchState 0) := by
  rw [secretBranchTrace_one, secretBranchTrace_two]
  decide

end CatCrypt.Crypto.SecureCompilation.Ascent.ControlFlowCT
