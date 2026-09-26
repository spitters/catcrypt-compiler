/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmRenderValidated

/-!
# The address trace of the owned `%zmm` / `%ymm` text

The leakage of a run of the machine `ZmmTextModel.run`: the program counter of each
executed instruction and the memory locations it touches (an input offset read at
`%rsi`, a data label read at `%rip`, an output offset written at `%rdi`). The pointer
arguments `%rsi` and `%rdi` are public, so the locations are given relative to them.

`ZmmTextModel.Instr` has no control transfer, so a run executes the instructions of its
list once each, in order; an instruction touches locations fixed by its operands and
never by a register value. `runT_snd` states the consequence: the leakage of a run is
`leakFrom pc prog` when every instruction can execute on the data table, and the run
fails otherwise, whatever the input region and the initial state.

## Main definitions

* `Access`, `accesses`, `addrTrace`: the locations an instruction and a program touch.
* `leakFrom`: the leakage trace of a program, a function of the instruction list.
* `stepOK`: whether an instruction can execute on a data table.
* `runT`: the run of `ZmmTextModel.run` that also records the leakage.

## Main results

* `runT_fst`: the recording run ends in the state `run` ends in.
* `leakFrom_pcs`, `leakFrom_accesses`: the executed program counters are
  `pc, pc + 1, …` and the touched locations are `addrTrace prog`.
* `run_addrTrace_constant_time`: two runs on any two input regions and initial states
  have the same leakage.
* `parse_constant_time`, `renderValidated_constant_time`,
  `renderValidatedD_constant_time`: the same for every program `parse` accepts and
  every text the validated renders return.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextLeakage

open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode CSrc Opnd Instr MState step run
  csrcVal opVal)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (parse)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmRenderValidated (renderValidated renderValidatedD
  renderValidated_sound renderValidatedD_sound)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Locations and traces -/

/-- A memory location an instruction touches: the 64 bytes read at offset `off` of the
    input region (`%rsi`), the data at label `lbl` (`%rip`), or the bytes written at
    offset `off` of the output region (`%rdi`). -/
inductive Access where
  | rdIn (off : Nat)
  | rdC (lbl : String)
  | wrOut (off : Nat)
  deriving DecidableEq

/-- The label a read-only operand reads. -/
def csrcLabel : CSrc → String
  | .full l => l
  | .bq l => l
  | .bd l => l

/-- The locations an instruction touches, fixed by its operands. -/
def accesses : Instr → List Access
  | .ldIn off _ => [.rdIn off]
  | .ldC c _ => [.rdC (csrcLabel c)]
  | .st _ off => [.wrOut off]
  | .op _ _ (.mem c) _ _ => [.rdC (csrcLabel c)]
  | _ => []

/-- The locations a program touches, in order. -/
def addrTrace (prog : List Instr) : List Access := prog.flatMap accesses

/-- The leakage trace of a program started at program counter `pc`: each instruction's
    program counter and the locations it touches. -/
def leakFrom : Nat → List Instr → List (Nat × List Access)
  | _, [] => []
  | pc, i :: is => (pc, accesses i) :: leakFrom (pc + 1) is

/-- The program counters of the leakage trace are `pc, pc + 1, …, pc + |prog| - 1`: every
    instruction executes once, in list order. -/
theorem leakFrom_pcs : ∀ (pc : Nat) (prog : List Instr),
    (leakFrom pc prog).map Prod.fst = List.range' pc prog.length
  | _, [] => rfl
  | pc, _ :: is => by
    simp [leakFrom, leakFrom_pcs (pc + 1) is, List.range'_succ]

/-- The locations of the leakage trace are the address trace of the program. -/
theorem leakFrom_accesses : ∀ (pc : Nat) (prog : List Instr),
    (leakFrom pc prog).flatMap Prod.snd = addrTrace prog
  | _, [] => rfl
  | pc, i :: is => by
    simp [leakFrom, addrTrace, leakFrom_accesses (pc + 1) is]

/-! ## 2. The recording run -/

/-- Whether instruction `i` can execute in mode `m` on data table `ro`: every data label
    it reads is present with the quadwords it needs. -/
def stepOK (m : Mode) (ro : Std.HashMap String (Array (BitVec 64))) : Instr → Bool
  | .ldC c _ => (csrcVal m ro c).isSome
  | .op _ _ (.mem c) _ _ => (csrcVal m ro c).isSome
  | _ => true

/-- A step succeeds exactly when the instruction can execute on the data table, for every
    input region and state. -/
theorem step_isSome (m : Mode) (inp : Nat → BitVec 512)
    (ro : Std.HashMap String (Array (BitVec 64))) (σ : MState) (i : Instr) :
    (step m inp ro σ i).isSome = stepOK m ro i := by
  cases i with
  | op L o s2 s1 d => cases s2 <;> simp [step, stepOK, opVal]
  | dup odd r d mask => cases mask <;> simp [step, stepOK]
  | ldC c d => simp [step, stepOK]
  | _ => simp [step, stepOK]

/-- The run of `run` from program counter `pc` that also returns its leakage trace. -/
def runT (m : Mode) (inp : Nat → BitVec 512) (ro : Std.HashMap String (Array (BitVec 64))) :
    Nat → MState → List Instr → Option (MState × List (Nat × List Access))
  | _, σ, [] => some (σ, [])
  | pc, σ, i :: is => (step m inp ro σ i).bind fun σ' =>
      (runT m inp ro (pc + 1) σ' is).map fun r => (r.1, (pc, accesses i) :: r.2)

/-- The recording run ends in the state the run ends in. -/
theorem runT_fst (m : Mode) (inp : Nat → BitVec 512)
    (ro : Std.HashMap String (Array (BitVec 64))) :
    ∀ (pc : Nat) (σ : MState) (prog : List Instr),
      (runT m inp ro pc σ prog).map Prod.fst = run m inp ro σ prog
  | _, _, [] => rfl
  | pc, σ, i :: is => by
    cases h : step m inp ro σ i with
    | none => simp [runT, run, h]
    | some σ' =>
      have ih := runT_fst m inp ro (pc + 1) σ' is
      simp only [runT, run, h, Option.bind_some, Option.map_map] at ih ⊢
      exact ih

/-- The leakage of a run is `leakFrom pc prog` when every instruction can execute on the
    data table, and the run fails otherwise; neither depends on the input region `inp`
    or the initial state `σ`. -/
theorem runT_snd (m : Mode) (inp : Nat → BitVec 512)
    (ro : Std.HashMap String (Array (BitVec 64))) :
    ∀ (pc : Nat) (σ : MState) (prog : List Instr),
      (runT m inp ro pc σ prog).map Prod.snd =
        if prog.all (stepOK m ro) then some (leakFrom pc prog) else none
  | _, _, [] => rfl
  | pc, σ, i :: is => by
    have hs := step_isSome m inp ro σ i
    cases h : step m inp ro σ i with
    | none =>
      rw [h] at hs
      simp [runT, h, List.all_cons, ← hs]
    | some σ' =>
      rw [h] at hs
      have ih := runT_snd m inp ro (pc + 1) σ' is
      simp only [runT, h, Option.bind_some, Option.map_map] at ih ⊢
      have e : (Prod.snd ∘ fun r : MState × List (Nat × List Access) =>
          (r.1, (pc, accesses i) :: r.2)) = (fun t => (pc, accesses i) :: t) ∘ Prod.snd := rfl
      rw [e, ← Option.map_map, ih]
      simp only [List.all_cons, ← hs, Option.isSome_some, Bool.true_and]
      split <;> simp [leakFrom]

/-- **Constant time of the vector text.** For every program and data table, the runs on
    any two input regions and any two initial states have the same leakage: both fail,
    or both succeed with trace `leakFrom 0 prog`, whose program counters are
    `0, 1, …, |prog| - 1` (`leakFrom_pcs`) and whose locations are `addrTrace prog`
    (`leakFrom_accesses`). -/
theorem run_addrTrace_constant_time (m : Mode) (ro : Std.HashMap String (Array (BitVec 64)))
    (prog : List Instr) (inp₁ inp₂ : Nat → BitVec 512) (σ₁ σ₂ : MState) :
    (runT m inp₁ ro 0 σ₁ prog).map Prod.snd = (runT m inp₂ ro 0 σ₂ prog).map Prod.snd := by
  rw [runT_snd, runT_snd]

/-- A successful run has leakage `leakFrom 0 prog`. -/
theorem runT_trace {m : Mode} {inp : Nat → BitVec 512}
    {ro : Std.HashMap String (Array (BitVec 64))} {σ σ' : MState} {prog : List Instr}
    {t : List (Nat × List Access)} (h : runT m inp ro 0 σ prog = some (σ', t)) :
    t = leakFrom 0 prog := by
  have e := runT_snd m inp ro 0 σ prog
  rw [h] at e
  split at e <;> simp_all

/-! ## 3. The parsed text and the validated renders -/

/-- Every program `parse` accepts, with its data table, has the same leakage on any two
    input regions and initial states. -/
theorem parse_constant_time {m : Mode} {text : String} {prog : List Instr}
    {ro : Std.HashMap String (Array (BitVec 64))} (_ : parse m text = .ok (prog, ro))
    (inp₁ inp₂ : Nat → BitVec 512) (σ₁ σ₂ : MState) :
    (runT m inp₁ ro 0 σ₁ prog).map Prod.snd = (runT m inp₂ ro 0 σ₂ prog).map Prod.snd :=
  run_addrTrace_constant_time m ro prog inp₁ inp₂ σ₁ σ₂

/-- A text `renderValidated` returns parses to a program whose leakage is the same on any
    two input regions and initial states. -/
theorem renderValidated_constant_time {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {ymm : Bool} {text : String} (h : renderValidated sym inOffset nOut c inBound ymm = .ok text) :
    ∃ prog ro, parse (if ymm then .ymm else .zmm) text = .ok (prog, ro) ∧
      ∀ (inp₁ inp₂ : Nat → BitVec 512) (σ₁ σ₂ : MState),
        (runT (if ymm then .ymm else .zmm) inp₁ ro 0 σ₁ prog).map Prod.snd =
          (runT (if ymm then .ymm else .zmm) inp₂ ro 0 σ₂ prog).map Prod.snd := by
  obtain ⟨prog, ro, hp, -⟩ := renderValidated_sound h
  exact ⟨prog, ro, hp, run_addrTrace_constant_time _ ro prog⟩

/-- A text `renderValidatedD` returns parses to a program whose leakage is the same on any
    two input regions and initial states. -/
theorem renderValidatedD_constant_time {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : renderValidatedD sym inOffset nOut c inBound = .ok text) :
    ∃ prog ro, parse .zmm text = .ok (prog, ro) ∧
      ∀ (inp₁ inp₂ : Nat → BitVec 512) (σ₁ σ₂ : MState),
        (runT .zmm inp₁ ro 0 σ₁ prog).map Prod.snd = (runT .zmm inp₂ ro 0 σ₂ prog).map Prod.snd := by
  obtain ⟨prog, ro, hp, -⟩ := renderValidatedD_sound h
  exact ⟨prog, ro, hp, run_addrTrace_constant_time _ ro prog⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextLeakage
