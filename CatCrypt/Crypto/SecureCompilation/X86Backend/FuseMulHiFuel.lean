/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

@[expose] public section

set_option autoImplicit false

/-!
# The `MULX` fusion at an explicit fuel

`JasminLsemFuseMulHi.fuseMulHi_lsemFuelMemF_pre` matches a halting run of `pre ++ loop` at
fuel `fuel` by a halting run of `pre ++ fuseMulHiRM loop` at some fuel `fuel' ≤ fuel * 4`.
A halting run of `lsemFuelMemF` returns the same state at every larger fuel
(`LprogIsa.Isa.lsemFuelMemF_add`), so the fused body halts in one state at every fuel from
`fuel * 4` on. This module states that form, for the fusion of a whole body and of the loop
part of a body, and derives the statements with a bounded existential fuel from it.

## Main definitions

* `fuseFuel`: the fuel `fuel * 4` of the fused body.

## Main results

* `lsemFuelMemF_le`: a halting run of `lsemFuelMemF` returns the same state at every larger
  fuel.
* `fuseMulHi_lsemFuelMemF_fuel`, `fuseMulHi_lsemFuelMemF_pre_fuel`: the fused body halts in
  one state at every fuel from `fuseFuel fuel` on.
* `fuseMulHi_lsemFuelMemF_of_fuel`, `fuseMulHi_lsemFuelMemF_pre_of_fuel`: the statements of
  `fuseMulHi_lsemFuelMemF` and `fuseMulHi_lsemFuelMemF_pre`, from the forms at an explicit
  fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-- The fuel of the fused body for a source run at fuel `fuel`. -/
def fuseFuel (fuel : Nat) : Nat := fuel * 4

/-- A halting run of `lsemFuelMemF` returns the same state at every larger fuel. -/
theorem lsemFuelMemF_le (P : LprogM) {n k : Nat} {s t : LstateMF}
    (h : lsemFuelMemF P n s = some t) (hk : n ≤ k) : lsemFuelMemF P k s = some t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [← x86Isa_lsemFuelMemF] at h ⊢
  exact x86Isa.lsemFuelMemF_add P n d s t h

/-- **The fusion of a body at an explicit fuel.** Under the hypotheses of
    `fuseMulHi_lsemFuelMemF`, the fused body halts in one state at every fuel from
    `fuseFuel fuel` on; that state agrees with the final state of the source run on every
    register and array other than `R15`, on the word memory, the flags and the function
    name. -/
theorem fuseMulHi_lsemFuelMemF_fuel {E : List String} {c : List LinstrRM}
    (h : fuseMulHiOK E c = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn c) fuel s = some t) :
    ∃ t', (∀ k, fuseFuel fuel ≤ k →
        lsemFuelMemF (singletonProgM fn (fuseMulHiRM c)) k s = some t')
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  obtain ⟨f', t', hf, hrun', hrest⟩ := fuseMulHi_lsemFuelMemF h fn s t hpc hE fuel hrun
  exact ⟨t', fun k hk => lsemFuelMemF_le _ hrun' (hf.trans hk), hrest⟩

/-- **The fusion of the loop part of a body at an explicit fuel.** Under the hypotheses of
    `fuseMulHi_lsemFuelMemF_pre`, the body `pre ++ fuseMulHiRM loop` halts in one state at
    every fuel from `fuseFuel fuel` on; that state agrees with the final state of the source
    run as in `fuseMulHi_lsemFuelMemF`. -/
theorem fuseMulHi_lsemFuelMemF_pre_fuel {E : List String} {pre loop : List LinstrRM}
    (h : fuseOKL E (fuseLoPre pre loop) (pre ++ loop) = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel s = some t) :
    ∃ t', (∀ k, fuseFuel fuel ≤ k →
        lsemFuelMemF (singletonProgM fn (pre ++ fuseMulHiRM loop)) k s = some t')
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  obtain ⟨f', t', hf, hrun', hrest⟩ := fuseMulHi_lsemFuelMemF_pre h fn s t hpc hE fuel hrun
  exact ⟨t', fun k hk => lsemFuelMemF_le _ hrun' (hf.trans hk), hrest⟩

/-- The statement of `fuseMulHi_lsemFuelMemF`, from `fuseMulHi_lsemFuelMemF_fuel` at the
    fuel `fuseFuel fuel`. -/
theorem fuseMulHi_lsemFuelMemF_of_fuel {E : List String} {c : List LinstrRM}
    (h : fuseMulHiOK E c = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn c) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ lsemFuelMemF (singletonProgM fn (fuseMulHiRM c)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  obtain ⟨t', hk, hrest⟩ := fuseMulHi_lsemFuelMemF_fuel h fn s t hpc hE fuel hrun
  exact ⟨fuseFuel fuel, t', Nat.le_refl _, hk _ (Nat.le_refl _), hrest⟩

/-- The statement of `fuseMulHi_lsemFuelMemF_pre`, from `fuseMulHi_lsemFuelMemF_pre_fuel` at
    the fuel `fuseFuel fuel`. -/
theorem fuseMulHi_lsemFuelMemF_pre_of_fuel {E : List String} {pre loop : List LinstrRM}
    (h : fuseOKL E (fuseLoPre pre loop) (pre ++ loop) = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ lsemFuelMemF (singletonProgM fn (pre ++ fuseMulHiRM loop)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  obtain ⟨t', hk, hrest⟩ := fuseMulHi_lsemFuelMemF_pre_fuel h fn s t hpc hE fuel hrun
  exact ⟨fuseFuel fuel, t', Nat.le_refl _, hk _ (Nat.le_refl _), hrest⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiFuel
