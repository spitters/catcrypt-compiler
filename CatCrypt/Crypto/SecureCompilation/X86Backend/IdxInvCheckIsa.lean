/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

@[expose] public section

set_option autoImplicit false

/-!
# The bounds-invariant check over a symbolic companion

The bounds-invariant check `IdxInvCheck.idxInvCheckB` and the checker `ownedCheckMC` at the
symbolic step and branch condition of a symbolic companion `T : IsaSym I` of an instruction
set `I`. For a lawful companion, an accepted pair relates every halting run of `I` on the
source body from a state satisfying the entry facts to a halting checked run of `I` on the
rewritten body.

## Main results

* `IsaSym.runIdxOk_of_idxInvCheckB`: every halting run of `I` on a body the check accepts
  at `T` is in bounds.
* `IsaSym.ownedCheckMC_sound_of_idxInv`: `ownedCheckMC` and the bounds-invariant check at
  `T` relate every halting run of `I` on the source to a halting checked run of the
  rewritten body.
* `x86Sym_idxInvCheckB`: the check at `x86Sym` is the check at its default arguments.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (IdxFact idxInvCheckB)

namespace IsaSym

variable {I : Isa} (T : IsaSym I)

/-- **Soundness of the bounds-invariant check at a lawful symbolic companion.** If
    `idxInvCheckB entry ann B T.symStep T.symDec` accepts, every halting run of `I` on the
    singleton program over `B` from a state at pc `0` of that function whose registers and
    arrays satisfy the entry facts is in bounds. -/
theorem runIdxOk_of_idxInvCheckB (hT : T.Lawful) {entry : List IdxFact}
    {ann : List (List IdxFact)} {B : List LinstrRM}
    (h : idxInvCheckB entry ann B T.symStep T.symDec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    I.RunIdxOk (singletonProgM fn B) fuel s :=
  (T.symLaws hT).runIdxOk_of_idxInvCheckB h fn s t hfn hpc hent fuel hrun

/-- **The checker on runs of an accepted source body, at a lawful symbolic companion.** If
    `ownedCheckMC outs B B' T.symStep T.symDec` and
    `idxInvCheckB entry ann B T.symStep T.symDec` accept, every halting run of `I` on `B`
    from a state at pc `0` whose registers and arrays satisfy the entry facts is matched by
    a halting checked run of `I` on `B'` from the same state, the end states agreeing on
    `outs`, the arrays and the word memory. -/
theorem ownedCheckMC_sound_of_idxInv (hT : T.Lawful) {outs : List String}
    {B B' : List LinstrRM} {entry : List IdxFact} {ann : List (List IdxFact)}
    (h : ownedCheckMC outs B B' T.symStep T.symDec = true)
    (hi : idxInvCheckB entry ann B T.symStep T.symDec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' :=
  (T.symLaws hT).ownedCheckMC_sound_of_idxInv (T.symSubst hT) h hi fn s t hfn hpc hent fuel
    hrun

end IsaSym

/-- The bounds-invariant check at the x86 symbolic companion is the check at its default
    symbolic step and branch condition. -/
theorem x86Sym_idxInvCheckB (entry : List IdxFact) (ann : List (List IdxFact))
    (B : List LinstrRM) :
    idxInvCheckB entry ann B x86Sym.symStep x86Sym.symDec = idxInvCheckB entry ann B :=
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
