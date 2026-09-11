/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled

@[expose] public section

set_option autoImplicit false

/-!
# The labeled, program-indexed linear semantics over the `LstateN` N-state (mul/carry)

`JasminLsemLabeled` ported jasmin's program-indexed `lsem` (`find_instr`/`eval_instr`/
`step`/`lsemFuel`) over the single-width `Lstate`. The mul/carry fragment runs over the
width-tagged `LstateN` (`JasminLsemWidthN`) via `lsemStepMC` — and crucially over the
*same* `LinstrR` instruction type and the *same* `Lprog`/`Lfundef` program structure as
the labeled layer (only the state is richer). So the program-indexed semantics mirrors
`JasminLsemLabeled` verbatim with `Lstate ↦ LstateN`, `lsemStep ↦ lsemStepMC`.

This is the N-state counterpart of the labeled layer: `LstatePN` (the `LstateN` state +
the current function name), `findInstrN`, `evalInstrPN` (delegating the straight-line arms
to `lsemStepMC` on the base), and `lsemFuelMC` (fuel-bounded iteration). It is the target
semantics for lifting the mul/carry-fragment faithfulness (`comToLprog_faithful_mulcarry`,
stated over the body-fold `lsemStraightMC`) into the program-indexed `lsem`, the N-state
analogue of `JasminLsemLabeled.lsemFuel_straightline`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry

/-! ## The `lpc`-advancement chain: every N-state step advances the pc by one -/

/-- Every successful base N-state step advances the pc by one (each success arm ends in
    `lnext_pc`). -/
theorem lsemStepN_lpc_succ (i : LinstrR) (s s' : LstateN) (h : lsemStepN i s = some s') :
    s'.lpc = s.lpc + 1 := by
  unfold lsemStepN at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)

/-- Every successful shift-aware step advances the pc by one. -/
theorem lsemStepSh_lpc_succ (i : LinstrR) (s s' : LstateN) (h : lsemStepSh i s = some s') :
    s'.lpc = s.lpc + 1 := by
  unfold lsemStepSh at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)
      | exact lsemStepN_lpc_succ _ s s' h

/-- Every successful mul/carry-aware step advances the pc by one. -/
theorem lsemStepMC_lpc_succ (i : LinstrR) (s s' : LstateN) (h : lsemStepMC i s = some s') :
    s'.lpc = s.lpc + 1 := by
  unfold lsemStepMC at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)
      | exact lsemStepSh_lpc_succ _ s s' h

/-- The program-indexed N-state: the `LstateN` straight-line state plus the current
    function name `lfn` (indexing `lp_funcs`). The `LstateN` analogue of `LstateP`. -/
structure LstatePN where
  /-- The mul/carry straight-line state (width-tagged lvm + lpc). -/
  base : LstateN
  /-- The current function name. -/
  lfn : String

/-- Advance the base pc, keeping `lfn`. -/
def LstatePN.nextPc (s : LstatePN) : LstatePN := { s with base := s.base.nextPc }

/-- `find_instr`: the instruction at `lpc` in the current function's body (`LinstrR`,
    the same body shape the labeled layer fetches), or `none` (halted/out of range). -/
def findInstrN (P : Lprog) (s : LstatePN) : Option LinstrR :=
  match getFundef P s.lfn with
  | some fd => (fd.lfd_body[s.base.lpc]?).map Linstr.li_i
  | none => none

/-- `eval_instr` over the N-state: the straight-line arms (`Lopn`/`Llabel`/`Lalign`)
    delegate to `lsemStepMC` on the base, carrying `lfn`; control flow is out of scope
    here (the straight-line bridge target). -/
def evalInstrPN (P : Lprog) (i : LinstrR) (s : LstatePN) : Option LstatePN :=
  match i with
  | .Lopn dsts opn srcs =>
      (lsemStepMC (.Lopn dsts opn srcs) s.base).map (fun b => { s with base := b })
  | .Llabel k l => (lsemStepMC (.Llabel k l) s.base).map (fun b => { s with base := b })
  | .Lalign => (lsemStepMC .Lalign s.base).map (fun b => { s with base := b })
  | _ => none

/-- `step`: fetch and evaluate. -/
def lsemStepPN (P : Lprog) (s : LstatePN) : Option LstatePN :=
  match findInstrN P s with
  | some i => evalInstrPN P i s
  | none => none

/-- `lsemFuel` over the N-state: iterate `lsemStepPN`, halting (returning the state) when
    `findInstrN` is `none` (lpc past the body end — `lsem_final`). -/
def lsemFuelMC (P : Lprog) : Nat → LstatePN → Option LstatePN
  | 0, s => match findInstrN P s with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrN P s with
      | none => some s
      | some i =>
          match evalInstrPN P i s with
          | some s' => lsemFuelMC P fuel s'
          | none => none

/-- A halted state (`findInstrN = none`) takes no step: `lsemFuelMC` returns it unchanged
    at every fuel (`lsem_final_nostep`). -/
theorem lsemFuelMC_halt (P : Lprog) (fuel : Nat) (s : LstatePN)
    (h : findInstrN P s = none) : lsemFuelMC P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelMC, h]
  | succ n => simp [lsemFuelMC, h]

/-- **Determinism**: same fuel ⇒ same result (`lsemFuelMC` is a function). -/
theorem lsemFuelMC_deterministic (P : Lprog) (fuel : Nat) (s t1 t2 : LstatePN)
    (h1 : lsemFuelMC P fuel s = some t1) (h2 : lsemFuelMC P fuel s = some t2) : t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## The straight-line bridge: `lsemFuelMC` over a jump-free body = `lsemStraightMC` -/

/-- On a jump-free instruction, `evalInstrPN` is `lsemStepMC` lifted over the base
    (carrying `lfn`). The per-instruction tie between the program layer and the
    mul/carry body-fold. -/
theorem evalInstrPN_straightLine (P : Lprog) (i : LinstrR) (s : LstatePN)
    (hi : IsStraightLine i) :
    evalInstrPN P i s = (lsemStepMC i s.base).map (fun b => { s with base := b }) := by
  cases i <;> simp_all [IsStraightLine, evalInstrPN]

/-- `findInstrN` on a singleton program reads the `pc`-th element of `body`. -/
theorem findInstrN_singleton (fn : String) (body : List LinstrR) (s : LstatePN)
    (hfn : s.lfn = fn) :
    findInstrN (singletonProg fn body) s = body[s.base.lpc]? := by
  rw [findInstrN, hfn, getFundef_singleton]
  show Option.map Linstr.li_i (List.map (fun ir => (⟨0, ir⟩ : Linstr)) body)[s.base.lpc]?
      = body[s.base.lpc]?
  rw [List.getElem?_map, Option.map_map]
  cases body[s.base.lpc]? <;> rfl

/-- `findInstrN` past the end of a singleton body is `none` (halted). -/
theorem findInstrN_singleton_halt (fn : String) (body : List LinstrR) (s : LstatePN)
    (hfn : s.lfn = fn) (hpc : body.length ≤ s.base.lpc) :
    findInstrN (singletonProg fn body) s = none := by
  rw [findInstrN_singleton fn body s hfn]; exact List.getElem?_eq_none hpc

/-- **Straight-line consistency (suffix form).** Running an all-straight-line `suffix` of
    a singleton program's `body` via `lsemFuelMC` (from the program position
    `body.length - suffix.length`, with `suffix.length` fuel) agrees with the body-fold
    `lsemStraightMC` over that suffix on the base state. The `lpc`-lockstep invariant:
    the program's `lpc` equals the already-executed prefix length, so `findInstrN` fetches
    the next suffix instruction, and `evalInstrPN` reduces to `lsemStepMC` (advancing the
    pc by one via `lsemStepMC_lpc_succ`). -/
theorem lsemFuelMC_straightline_suffix (fn : String) (pre suffix : List LinstrR)
    (hsl : ∀ i ∈ suffix, IsStraightLine i) :
    ∀ (s : LstatePN), s.lfn = fn → s.base.lpc = pre.length →
      lsemFuelMC (singletonProg fn (pre ++ suffix)) suffix.length s
        = (lsemStraightMC suffix s.base).map (fun b => { s with base := b }) := by
  induction suffix generalizing pre with
  | nil =>
      intro s hfn hpc
      simp only [List.length_nil, lsemFuelMC, lsemStraightMC_nil, Option.map_some]
      have hhalt : findInstrN (singletonProg fn (pre ++ [])) s = none := by
        apply findInstrN_singleton_halt fn (pre ++ []) s hfn; simp [hpc]
      rw [hhalt]
  | cons i is ih =>
      intro s hfn hpc
      have hi : IsStraightLine i := hsl i (by simp)
      have his : ∀ j ∈ is, IsStraightLine j := fun j hj => hsl j (by simp [hj])
      have hfetch : findInstrN (singletonProg fn (pre ++ i :: is)) s = some i := by
        rw [findInstrN_singleton fn (pre ++ i :: is) s hfn, hpc]; simp
      rw [List.length_cons, lsemFuelMC, hfetch]
      simp only []
      rw [evalInstrPN_straightLine _ i s hi]
      cases hstep : lsemStepMC i s.base with
      | none => simp only [Option.map_none]; rw [lsemStraightMC_cons, hstep]; rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraightMC_cons, hstep]
          have hb_lpc : b.lpc = (pre ++ [i]).length := by
            rw [lsemStepMC_lpc_succ i s.base b hstep, hpc]; simp
          have htail :
              lsemFuelMC (singletonProg fn ((pre ++ [i]) ++ is)) is.length
                  { s with base := b }
                = (lsemStraightMC is b).map (fun b' => { s with base := b' }) := by
            have := ih (pre ++ [i]) his { s with base := b } hfn hb_lpc
            simpa using this
          rw [show pre ++ i :: is = (pre ++ [i]) ++ is by simp] at *
          rw [htail]

/-- **Straight-line bridge (mul/carry).** For a jump-free `body`, the program-level
    `lsemFuelMC` over the singleton program with that body, run from `lpc = 0` with
    `body.length` fuel, agrees with the body-fold `lsemStraightMC`. The N-state analogue
    of `JasminLsemLabeled.lsemFuel_straightline`: every mul/carry-fragment simulation over
    `lsemStraightMC` lifts to the program-indexed `lsem` over `LstateN`. -/
theorem lsemFuelMC_straightline (fn : String) (body : List LinstrR)
    (hsl : ∀ i ∈ body, IsStraightLine i) (s : LstatePN)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 0) :
    lsemFuelMC (singletonProg fn body) body.length s
      = (lsemStraightMC body s.base).map (fun b => { s with base := b }) := by
  have := lsemFuelMC_straightline_suffix fn [] body hsl s hfn (by simpa using hpc)
  simpa using this

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
