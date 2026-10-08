/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

@[expose] public section

set_option autoImplicit false

/-!
# Soundness of the register allocation checker at an explicit fuel

`OwnedLprogTVChecked.ownedCheckMC_sound` matches a halting checked run of a body `B` at fuel
`fuel` by a halting checked run of the rewritten body `B'` at some fuel. Its simulation
`SimAtCF` goes by induction on the measure `fuel * (nb + 1) + (nb - k)`, for `nb` the number of
blocks of `B` and `k` the current block, and each step of that induction runs one block of
`B'`. The steps of the rewritten run in one step of the induction, by the terminator of the
block:

* fall through: the instructions of the block from its entry;
* jump, and branch (taken or not): those instructions and the terminator;
* the end of the body: none.

Each is at most `B'.length + 1`, and the induction takes at most the measure plus one steps,
so the rewritten run halts within `checkFuel B B' fuel
= (B'.length + 1) * (fuel * (nb + 1) + nb + 1)`. The simulation with that bound (`SimAtCF`,
`sim_stepCF`), the definitions `blockCount` and `checkFuel`, and
`ownedCheckWithC_sound_at_fuel` are in the module `OwnedLprogTVChecked`, in this namespace.
This module states the soundness theorems for the checked run, in the form "the rewritten
body halts in one state at every fuel from `checkFuel B B' fuel` on", and derives the
statements of `OwnedLprogTVChecked` from them.

## Main results

* `lsemFuelMemFk_add`: a halting checked run returns the same state at every larger fuel.
* `ownedCheckMC_sound_at_fuel`, `ownedCheckMC_sound_fuel`: the rewritten body halts in one
  state at every fuel from `checkFuel B B' fuel` on, over an instruction set and at x86.
* `ownedCheckWithC_sound_at_of_fuel`, `ownedCheckMC_sound_at_of_fuel`,
  `ownedCheckMC_sound_of_fuel`: the statements of `ownedCheckWithC_sound_at`,
  `ownedCheckMC_sound_at` and `ownedCheckMC_sound`, from the forms at an explicit fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCheckFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
  (x86Isa x86Isa_lsemFuelMemF x86Isa_runL x86Isa_lsemFuelMemFk x86Isa_RunIdxOk)

/-! ## 1. Fuel monotonicity of the checked run -/

/-- A halting checked run returns the same state at every larger fuel. -/
theorem lsemFuelMemFk_add (I : Isa) (ck : Bool) (P : LprogM) :
    ∀ (n k : Nat) (s t : LstateMF), I.lsemFuelMemFk ck P n s = some t →
      I.lsemFuelMemFk ck P (n + k) s = some t := by
  intro n
  induction n with
  | zero =>
      intro k s t h
      simp only [Isa.lsemFuelMemFk] at h
      split at h
      · next hf => cases h; rw [Nat.zero_add]; exact I.lsemFuelMemFk_halt ck P k s hf
      · cases h
  | succ n ih =>
      intro k s t h
      rw [Nat.add_right_comm]
      simp only [Isa.lsemFuelMemFk] at h ⊢
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; exact h
      | some i =>
          simp only [hf] at h ⊢
          cases hs : I.evalInstrPMemFk ck P i s with
          | none => simp only [hs, reduceCtorEq] at h
          | some s' => simp only [hs] at h ⊢; exact ih k s' t h

/-! ## 2. Soundness at an explicit fuel -/

/-- **Soundness of the checker at an explicit fuel, over an instruction set.** Under the
    hypotheses of `ownedCheckMC_sound_at`, the checked run of the singleton program over `B'`
    halts in one state at every fuel from `checkFuel B B' fuel` on, and that state agrees
    with the end state of the run of `B` on the registers `outs`, the arrays and the word
    memory. -/
theorem ownedCheckMC_sound_at_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' sym dec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ t', (∀ k, checkFuel B B' fuel ≤ k →
        I.lsemFuelMemFk true (singletonProgM fn B') k s = some t') ∧ Obs outs t t' := by
  obtain ⟨f', t', hf, hr, hobs, hok⟩ := ownedCheckMC_idx_sound_at_fuel hL hS h fn s t hfn hpc
    fuel (I.lsemFuelMemF_of_checked _ fuel s t hrun) (I.runIdxOk_of_checked _ fuel s t hrun)
  refine ⟨t', fun k hk => ?_, hobs⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (hf.trans hk)
  exact lsemFuelMemFk_add I true _ f' d s t' (I.lsemFuelMemFk_of_runIdxOk true _ f' s t' hr hok)

/-- **Soundness of the checker at an explicit fuel.** Under the hypotheses of
    `ownedCheckMC_sound`, the checked run (`lsemFuelMemFk true`) of the singleton program over
    `B'` halts in one state at every fuel from `checkFuel B B' fuel` on, and that state
    agrees with the end state of the run of `B` on the registers `outs`, the arrays and the
    word memory. -/
theorem ownedCheckMC_sound_fuel {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ t', (∀ k, checkFuel B B' fuel ≤ k →
        lsemFuelMemFk true (singletonProgM fn B') k s = some t') ∧ Obs outs t t' := by
  rw [← x86Isa_lsemFuelMemFk] at hrun
  simpa only [x86Isa_lsemFuelMemFk] using
    ownedCheckMC_sound_at_fuel symLaws_x86 symSubst_x86 h fn s t hfn hpc fuel hrun

/-! ## 4. The statements with an existential fuel -/

/-- The statement of `ownedCheckWithC_sound_at`, from `ownedCheckWithC_sound_at_fuel`. -/
theorem ownedCheckWithC_sound_at_of_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' sym dec = true)
    (hob : oblCheckWith L B B' sym = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s := by
  obtain ⟨f', t', -, hrest⟩ := ownedCheckWithC_sound_at_fuel hL h hob fn s t hfn hpc fuel hrun
    hok
  exact ⟨f', t', hrest⟩

/-- The statement of `ownedCheckMC_sound_at`, from `ownedCheckMC_sound_at_fuel` at the fuel
    `checkFuel B B' fuel`. -/
theorem ownedCheckMC_sound_at_of_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' sym dec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  obtain ⟨t', hk, hobs⟩ := ownedCheckMC_sound_at_fuel hL hS h fn s t hfn hpc fuel hrun
  exact ⟨_, t', hk _ (Nat.le_refl _), hobs⟩

/-- The statement of `ownedCheckMC_sound`, from `ownedCheckMC_sound_fuel` at the fuel
    `checkFuel B B' fuel`. -/
theorem ownedCheckMC_sound_of_fuel {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  obtain ⟨t', hk, hobs⟩ := ownedCheckMC_sound_fuel h fn s t hfn hpc fuel hrun
  exact ⟨_, t', hk _ (Nat.le_refl _), hobs⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCheckFuel
