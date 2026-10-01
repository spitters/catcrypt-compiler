/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

@[expose] public section

set_option autoImplicit false

/-!
# The bounds-checked flag machine

The name-keyed machine `lsemFuelMemF` reads and writes an array of length `n` at the index
`idx mod n` (`stackGet`, `stackSet`), so a run that indexes past the end of an array still
halts. The machine on addresses reads and writes the memory at `base + 8 · idx`, which past
the end of the array is another region. The checked machine `lsemFuelMemFk true` takes the
step of `lsemFuelMemF` only when the indexed access of the instruction is in bounds
(`idxOkB`), and is stuck otherwise; a halting checked run therefore indexes every array
inside its length. `lsemFuelMemFk false` is `lsemFuelMemF`.

## Main results

* `idxOkB`, `evalInstrPMemFk`, `lsemFuelMemFk`: the in-bounds condition of an instruction,
  the checked step and the checked run.
* `lsemFuelMemFk_false`: the unchecked instance is `lsemFuelMemF`.
* `lsemFuelMemF_of_checked`: a halting checked run is a halting run of `lsemFuelMemF`.
* `RunIdxOk`, `lsemFuelMemFk_of_runIdxOk`, `runIdxOk_of_checked`: a halting run of
  `lsemFuelMemF` whose accesses are in bounds is a halting checked run, and conversely.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-- The index register `idx` holds, at width `64`, a value below `n`; `true` when it holds
    no value at width `64` (the step then fails in `lsemStepMem`). -/
def idxBelowB (s : LstateMF) (idx : String) (n : Nat) : Bool :=
  match s.prog.base.reg.getW idx 64 with
  | some v => decide (v.toNat < n)
  | none => true

/-- **The in-bounds condition of an instruction**: an indexed load tagged `.load w n` or an
    indexed store tagged `.store w n` reads its index below `n`; every other instruction is
    in bounds. -/
def idxOkB (i : LinstrRM) (s : LstateMF) : Bool :=
  match i.2 with
  | .load _ n =>
      match loadStruct? i.1 with
      | some (_, _, idx) => idxBelowB s idx n
      | none => true
  | .store _ n =>
      match storeStruct? i.1 with
      | some (_, _, idx, _) => idxBelowB s idx n
      | none => true
  | _ => true

/-- **The checked step**: with `ck`, the step of `evalInstrPMemF` when the instruction is in
    bounds (`idxOkB`) and none otherwise; without `ck`, the step of `evalInstrPMemF`. -/
def evalInstrPMemFk (ck : Bool) (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    Option LstateMF :=
  if ck && !idxOkB i s then none else evalInstrPMemF P i s

/-- The run of the checked step, halting when `findInstrMem` is `none`, with the recursion
    of `lsemFuelMemF`. -/
def lsemFuelMemFk (ck : Bool) (P : LprogM) : Nat → LstateMF → Option LstateMF
  | 0, s => match findInstrMem P s.prog with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some s
      | some i =>
          match evalInstrPMemFk ck P i s with
          | some s' => lsemFuelMemFk ck P fuel s'
          | none => none

@[simp] theorem evalInstrPMemFk_false (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    evalInstrPMemFk false P i s = evalInstrPMemF P i s := by
  simp [evalInstrPMemFk]

theorem evalInstrPMemFk_true (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    evalInstrPMemFk true P i s = if idxOkB i s then evalInstrPMemF P i s else none := by
  cases h : idxOkB i s <;> simp [evalInstrPMemFk, h]

/-- A checked step is a step of `evalInstrPMemF`. -/
theorem evalInstrPMemF_of_k {ck : Bool} {P : LprogM} {i : LinstrRM} {s s' : LstateMF}
    (h : evalInstrPMemFk ck P i s = some s') : evalInstrPMemF P i s = some s' := by
  unfold evalInstrPMemFk at h
  split at h
  · cases h
  · exact h

/-- A successful checked step is in bounds. -/
theorem idxOkB_of_checked {P : LprogM} {i : LinstrRM} {s s' : LstateMF}
    (h : evalInstrPMemFk true P i s = some s') : idxOkB i s = true := by
  rw [evalInstrPMemFk_true] at h
  cases hb : idxOkB i s
  · simp [hb] at h
  · rfl

/-- The unchecked instance of the checked run is `lsemFuelMemF`. -/
theorem lsemFuelMemFk_false (P : LprogM) :
    ∀ (fuel : Nat) (s : LstateMF), lsemFuelMemFk false P fuel s = lsemFuelMemF P fuel s
  | 0, s => by
      cases hf : findInstrMem P s.prog <;> simp only [lsemFuelMemFk, lsemFuelMemF, hf]
  | fuel + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf]
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf, evalInstrPMemFk_false]
          cases evalInstrPMemF P i s with
          | none => rfl
          | some s' => exact lsemFuelMemFk_false P fuel s'

theorem lsemFuelMemFk_halt (ck : Bool) (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : lsemFuelMemFk ck P fuel s = some s := by
  cases fuel <;> simp [lsemFuelMemFk, h]

theorem lsemFuelMemFk_step (ck : Bool) (P : LprogM) (fuel : Nat) (i : LinstrRM)
    (s s' : LstateMF) (hfetch : findInstrMem P s.prog = some i)
    (heval : evalInstrPMemFk ck P i s = some s') :
    lsemFuelMemFk ck P (fuel + 1) s = lsemFuelMemFk ck P fuel s' := by
  simp only [lsemFuelMemFk, hfetch, heval]

/-- **A halting checked run is a halting run of `lsemFuelMemF`**, to the same state. -/
theorem lsemFuelMemF_of_checked {ck : Bool} (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), lsemFuelMemFk ck P fuel s = some t →
      lsemFuelMemF P fuel s = some t
  | 0, s, t, h => by
      cases hf : findInstrMem P s.prog <;>
        simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢ <;> exact h
  | fuel + 1, s, t, h => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢; exact h
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢
          cases he : evalInstrPMemFk ck P i s with
          | none => simp [he] at h
          | some s' =>
              rw [he] at h
              simp only [evalInstrPMemF_of_k he]
              exact lsemFuelMemF_of_checked P fuel s' t h

/-- Every state that a run of `lsemFuelMemF` of at most `fuel` steps steps from is in bounds
    at the instruction it fetches. -/
def RunIdxOk (P : LprogM) : Nat → LstateMF → Prop
  | 0, _ => True
  | fuel + 1, s =>
      ∀ i, findInstrMem P s.prog = some i →
        idxOkB i s = true ∧ ∀ s', evalInstrPMemF P i s = some s' → RunIdxOk P fuel s'

/-- **A halting run of `lsemFuelMemF` whose accesses are in bounds is a halting checked
    run**, to the same state. -/
theorem lsemFuelMemFk_of_runIdxOk (ck : Bool) (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), lsemFuelMemF P fuel s = some t → RunIdxOk P fuel s →
      lsemFuelMemFk ck P fuel s = some t
  | 0, s, t, h, _ => by
      cases hf : findInstrMem P s.prog <;>
        simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢ <;> exact h
  | fuel + 1, s, t, h, hok => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢; exact h
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢
          obtain ⟨hi, hnext⟩ := hok i hf
          cases he : evalInstrPMemF P i s with
          | none => simp [he] at h
          | some s' =>
              rw [he] at h
              have hk : evalInstrPMemFk ck P i s = some s' := by
                simp [evalInstrPMemFk, hi, he]
              simp only [hk]
              exact lsemFuelMemFk_of_runIdxOk ck P fuel s' t h (hnext s' he)

/-- **A halting checked run is in bounds**: every state it steps from fetches an instruction
    in bounds. -/
theorem runIdxOk_of_checked (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), lsemFuelMemFk true P fuel s = some t → RunIdxOk P fuel s
  | 0, _, _, _ => trivial
  | fuel + 1, s, t, h => by
      intro i hf
      simp only [lsemFuelMemFk, hf] at h
      cases he : evalInstrPMemFk true P i s with
      | none => simp [he] at h
      | some s' =>
          rw [he] at h
          refine ⟨idxOkB_of_checked he, fun s'' he' => ?_⟩
          rw [evalInstrPMemF_of_k he] at he'
          cases he'
          exact runIdxOk_of_checked P fuel s' t h

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
