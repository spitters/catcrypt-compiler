/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage

@[expose] public section

set_option autoImplicit false

/-!
# The machine level of the instruction-set record, and constant time of decoded programs

`IsaMachine` is the machine the bytes of an instruction set run on: the decoded
instruction type `Instr`, the straight-line operation type `Op` with its effect `exec` on the
machine state `MState`, the decoder `decode`, the action `act` of the instruction at an
index (an operation, a block of operations, a branch with its outcome, a call, or `ret`),
the operation blocks `callOps` and `retOps` around a callee, and the leakage `opLeak` of one
operation.

Over the record:

* `IsaMachine.mstep` is one step of a decoded program; `Reaches`, `Halts` and `HaltsC`
  (halting through calls) are its runs.
* `IsaMachine.RunL M ok prog pc s t s'` is a halting run through calls with leakage trace
  `t` in the event type `CT.CTLeak`, each operation it executes satisfying `ok`: an
  operation emits `opLeak`, a block the concatenated leakage `blockLeak`, a branch the
  `branch` event of its outcome, and a call the leakage of `callOps`, the callee's trace and
  the leakage of `retOps`.

The x86 instance, whose machine is the address machine `RInstrAddrMem.aMachine` over
`JInstr 64`, is `X86Backend.X86Isa.x86Mach`; at that instance `RunL`, `HaltsC` and `Halts`
are those of `DecodedCT` and `RInstrSemantics`.

## Main results

* `MAct`, `IsaMachine`: the action of one decoded instruction and the record.
* `IsaMachine.mstep`, `IsaMachine.Halts`, `IsaMachine.HaltsC`, `IsaMachine.haltsC_of_halts`:
  the step and the halting runs.
* `IsaMachine.RunL`, `IsaMachine.RunL.haltsC`, `IsaMachine.haltsC_runL`,
  `IsaMachine.halts_runL`, `IsaMachine.RunL.mono`: the leakage semantics; every run with
  leakage halts, and every halting run has a leakage trace.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Next)
open CatCrypt.Crypto.SecureCompilation.CT

/-- The action of one decoded instruction in a state: run an operation, run a block of
    operations, branch to `tgt` when `taken` and fall through otherwise, call `tgt`, or
    return. -/
inductive MAct (Op : Type) : Type where
  | op (i : Op)
  | block (ops : List Op)
  | branch (taken : Bool) (tgt : Nat)
  | call (tgt : Nat)
  | ret

/-- **The machine level of an instruction set**: the decoded instruction type, the
    straight-line operations and their effect on the machine state, the decoder, the action
    of the instruction at an index, the operation blocks around a callee, and the leakage of
    one operation. -/
structure IsaMachine : Type 1 where
  /-- The decoded instruction type. -/
  Instr : Type
  /-- The straight-line operation type. -/
  Op : Type
  /-- The machine state. -/
  MState : Type
  /-- The effect of one operation. -/
  exec : MState → Op → MState
  /-- The decoder of a byte string into a program. -/
  decode : List (BitVec 8) → Option (List Instr)
  /-- The action of the instruction of `prog` at an index in a state, `none` when stuck. -/
  act : List Instr → Nat → MState → Option (MAct Op)
  /-- The operations a call runs before its callee, given the return index. -/
  callOps : Nat → List Op
  /-- The operations a return from a callee runs. -/
  retOps : List Op
  /-- The leakage of one operation in the state it runs in. -/
  opLeak : MState → Op → List CTLeak

namespace IsaMachine

variable (M : IsaMachine)

/-- The straight-line fold of `exec`. -/
def runBlock (s : M.MState) : List M.Op → M.MState
  | [] => s
  | i :: is => runBlock (M.exec s i) is

/-- The leakage of a block, the state threaded by `exec`. -/
def blockLeak (s : M.MState) : List M.Op → List CTLeak
  | [] => []
  | i :: is => M.opLeak s i ++ blockLeak (M.exec s i) is

/-- Every operation of a block satisfies `ok` in the state it runs in. -/
def BlockOk (ok : M.MState → M.Op → Prop) (s : M.MState) : List M.Op → Prop
  | [] => True
  | i :: is => ok s i ∧ BlockOk ok (M.exec s i) is

theorem blockOk_true : ∀ (ops : List M.Op) (s : M.MState), M.BlockOk (fun _ _ => True) s ops
  | [], _ => trivial
  | _ :: is, _ => ⟨trivial, blockOk_true is _⟩

/-- One step of `prog` at `pc`: an operation or block runs and advances, a branch goes to
    its target when taken and advances otherwise, `ret` halts, and a call or a stuck index
    has no step. -/
def mstep (prog : List M.Instr) (pc : Nat) (s : M.MState) : Option (Next M.MState) :=
  match M.act prog pc s with
  | none => none
  | some (.op i) => some (.go (pc + 1) (M.exec s i))
  | some (.block ops) => some (.go (pc + 1) (M.runBlock s ops))
  | some (.branch b t) => some (.go (if b then t else pc + 1) s)
  | some (.call _) => none
  | some .ret => some (.halt s)

/-- The reflexive-transitive closure of `mstep` on continuing outcomes. -/
inductive Reaches (prog : List M.Instr) : Nat → M.MState → Nat → M.MState → Prop
  | refl (pc : Nat) (s : M.MState) : Reaches prog pc s pc s
  | next {pc : Nat} {s : M.MState} {pc' : Nat} {s' : M.MState} {pc'' : Nat} {s'' : M.MState}
      (h : M.mstep prog pc s = some (.go pc' s')) (hr : Reaches prog pc' s' pc'' s'') :
      Reaches prog pc s pc'' s''

/-- The program halts from `pc` in `s'`: a path to an index whose action is `ret`. -/
def Halts (prog : List M.Instr) (pc : Nat) (s s' : M.MState) : Prop :=
  ∃ pc', M.Reaches prog pc s pc' s' ∧ M.act prog pc' s' = some .ret

/-- The program halts from `pc` in `s''`, running through calls: a `ret` that ends the run,
    a continuing `mstep`, or a call whose callee runs from its target to its own `ret` on
    the state after `callOps`, the caller continuing at the next index on the state after
    `retOps`. -/
inductive HaltsC (prog : List M.Instr) : Nat → M.MState → M.MState → Prop
  | ret {pc : Nat} {s : M.MState} (h : M.act prog pc s = some .ret) : HaltsC prog pc s s
  | go {pc : Nat} {s : M.MState} {pc' : Nat} {s' s'' : M.MState}
      (h : M.mstep prog pc s = some (.go pc' s')) (hr : HaltsC prog pc' s' s'') :
      HaltsC prog pc s s''
  | call {pc t : Nat} {s sc s'' : M.MState} (h : M.act prog pc s = some (.call t))
      (hc : HaltsC prog t (M.runBlock s (M.callOps (pc + 1))) sc)
      (hr : HaltsC prog (pc + 1) (M.runBlock sc M.retOps) s'') :
      HaltsC prog pc s s''

variable {M}

/-- A call-free halting run is a halting run through calls. -/
theorem haltsC_of_halts {prog : List M.Instr} {pc : Nat} {s s' : M.MState}
    (h : M.Halts prog pc s s') : M.HaltsC prog pc s s' := by
  obtain ⟨pc', hr, hret⟩ := h
  induction hr with
  | refl => exact .ret hret
  | next hs _ ih => exact .go hs (ih hret)

variable (M)

/-- **A halting run with leakage**: a run of `prog` from index `pc` and state `s` through
    calls, with leakage trace `t` and final state `s'`, each operation the run executes
    satisfying `ok`. -/
inductive RunL (ok : M.MState → M.Op → Prop) (prog : List M.Instr) :
    Nat → M.MState → List CTLeak → M.MState → Prop
  | ret {pc : Nat} {s : M.MState} (h : M.act prog pc s = some .ret) : RunL ok prog pc s [] s
  | op {pc : Nat} {s : M.MState} {i : M.Op} {t : List CTLeak} {s' : M.MState}
      (h : M.act prog pc s = some (.op i)) (hok : ok s i)
      (hr : RunL ok prog (pc + 1) (M.exec s i) t s') :
      RunL ok prog pc s (M.opLeak s i ++ t) s'
  | block {pc : Nat} {s : M.MState} {ops : List M.Op} {t : List CTLeak} {s' : M.MState}
      (h : M.act prog pc s = some (.block ops)) (hok : M.BlockOk ok s ops)
      (hr : RunL ok prog (pc + 1) (M.runBlock s ops) t s') :
      RunL ok prog pc s (M.blockLeak s ops ++ t) s'
  | branch {pc : Nat} {s : M.MState} {b : Bool} {tgt : Nat} {t : List CTLeak} {s' : M.MState}
      (h : M.act prog pc s = some (.branch b tgt))
      (hr : RunL ok prog (if b then tgt else pc + 1) s t s') :
      RunL ok prog pc s (.branch b :: t) s'
  | call {pc tgt : Nat} {s sc : M.MState} {tc tr : List CTLeak} {s' : M.MState}
      (h : M.act prog pc s = some (.call tgt)) (hok : M.BlockOk ok s (M.callOps (pc + 1)))
      (hc : RunL ok prog tgt (M.runBlock s (M.callOps (pc + 1))) tc sc)
      (hokr : M.BlockOk ok sc M.retOps)
      (hr : RunL ok prog (pc + 1) (M.runBlock sc M.retOps) tr s') :
      RunL ok prog pc s
        (M.blockLeak s (M.callOps (pc + 1)) ++ tc ++ M.blockLeak sc M.retOps ++ tr) s'

variable {M}

/-- A run with leakage is a halting run through calls. -/
theorem RunL.haltsC {ok : M.MState → M.Op → Prop} {prog : List M.Instr} {pc : Nat}
    {s : M.MState} {t : List CTLeak} {s' : M.MState} (h : M.RunL ok prog pc s t s') :
    M.HaltsC prog pc s s' := by
  induction h with
  | ret h => exact .ret h
  | op h _ _ ih => exact .go (by simp [mstep, h]) ih
  | block h _ _ ih => exact .go (by simp [mstep, h]) ih
  | branch h _ ih => exact .go (by simp [mstep, h]) ih
  | call h _ _ _ _ ihc ihr => exact .call h ihc ihr

/-- **Every halting run through calls has a leakage trace.** -/
theorem haltsC_runL {prog : List M.Instr} {pc : Nat} {s s' : M.MState}
    (h : M.HaltsC prog pc s s') : ∃ t, M.RunL (fun _ _ => True) prog pc s t s' := by
  induction h with
  | ret hret => exact ⟨[], .ret hret⟩
  | call h _ _ ihc ihr =>
    obtain ⟨tc, htc⟩ := ihc
    obtain ⟨tr, htr⟩ := ihr
    exact ⟨_, .call h (M.blockOk_true _ _) htc (M.blockOk_true _ _) htr⟩
  | @go pc s pc₁ s₁ s₂ hs _ ih =>
    obtain ⟨t, ht⟩ := ih
    unfold mstep at hs
    split at hs
    · exact absurd hs (by simp)
    · rename_i i hi
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨_, .op hi trivial ht⟩
    · rename_i ops hi
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨_, .block hi (M.blockOk_true _ _) ht⟩
    · rename_i b tgt hi
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨_, .branch hi ht⟩
    · simp at hs
    · simp at hs

/-- Every call-free halting run has a leakage trace. -/
theorem halts_runL {prog : List M.Instr} {pc : Nat} {s s' : M.MState}
    (h : M.Halts prog pc s s') : ∃ t, M.RunL (fun _ _ => True) prog pc s t s' :=
  haltsC_runL (haltsC_of_halts h)

/-- `RunL` under a stronger side condition is `RunL` under a weaker one. -/
theorem RunL.mono {ok ok' : M.MState → M.Op → Prop} {prog : List M.Instr}
    (hok : ∀ s i, ok s i → ok' s i) {pc : Nat} {s : M.MState} {t : List CTLeak}
    {s' : M.MState} (h : M.RunL ok prog pc s t s') : M.RunL ok' prog pc s t s' := by
  have hb : ∀ (ops : List M.Op) (s : M.MState), M.BlockOk ok s ops → M.BlockOk ok' s ops := by
    intro ops
    induction ops with
    | nil => intro _ _; trivial
    | cons i is ih => intro s h; exact ⟨hok _ _ h.1, ih _ h.2⟩
  induction h with
  | ret h => exact .ret h
  | op h ho _ ih => exact .op h (hok _ _ ho) ih
  | block h ho _ ih => exact .block h (hb _ _ ho) ih
  | branch h _ ih => exact .branch h ih
  | call h ho _ hor _ ihc ihr => exact .call h (hb _ _ ho) ihc (hb _ _ hor) ihr

end IsaMachine

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
