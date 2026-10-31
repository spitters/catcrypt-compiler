/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.DeadWriteRetSound

/-!
# The dead-write elimination of the region post-pass on the functions of a program

The region post-pass `regionPostFuse` is the high-product fusion `FuseMulHi.fuseMulHiLprog`
followed by the dead-write elimination `deadWriteRet` on every function body
(`LprogOptPipeline.mapBodies deadWriteRet`). This module lifts the theorem of the elimination
on one body at the flag machine `lsemFuelMemF`, `DeadWriteRetSound.deadWriteRet_lsemFuelMemF`,
to the functions of a program, in the shape of `PrintedLprogFuel.printedLprog_lsemFuelMemF`:
every function of the source has its image function in the output, with the same result
registers and the body of the pass, and the halting runs of the typed bodies without their
trailing return correspond.

## Main results

* `mapBodies_deadWriteRet_lsemFuelMemF`: the elimination on every function of a program.
* `regionPostFuse_deadWriteRet_lsemFuelMemF`: the same for the functions of the fused program
  `fuseMulHiLprog P` and of `regionPostFuse P`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (mapBodies)
open CatCrypt.Crypto.SecureCompilation.Haxc.DeadWriteRetSound

/-- **`mapBodies_deadWriteRet_lsemFuelMemF`: the dead-write elimination on the functions of a
    program.** Every function `(fn, fd)` of `P` has the function `(fn, fd')` in
    `mapBodies deadWriteRet P`, with the same result registers and the body
    `deadWriteRet fd.lfd_body`. When every instruction of the body passes `deadWriteStepOK tg`
    and the symbolic run of the typed body without its return is inside the fragment of the
    symbolic step, every halting run of the typed body without its return from a state `s` at
    function `fn` and program counter `0` is matched by a halting run of the typed image body
    without its return from `s`, into a state that agrees with the source final state on every
    register list `outs`, on the arrays and on the word memory (`OwnedLprogTV.Obs`). -/
theorem mapBodies_deadWriteRet_lsemFuelMemF (P : Lprog) {fn : String} {fd : Lfundef}
    (hf : (fn, fd) ∈ P.lp_funcs) (tg : LinstrR → MemTag)
    (hok : ∀ i ∈ fd.lfd_body, deadWriteStepOK tg i.li_i = true)
    (hfrag : symRun (dropRet (typeBody tg fd.lfd_body)) SSt.start ≠ .unk) :
    ∃ fd', (fn, fd') ∈ (mapBodies deadWriteRet P).lp_funcs ∧ fd'.lfd_res = fd.lfd_res
      ∧ fd'.lfd_body = deadWriteRet fd.lfd_body
      ∧ ∀ (outs : List String) {fuel : Nat} {s t : LstateMF}, s.prog.lfn = fn →
        s.prog.base.reg.lpc = 0 →
        lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg fd.lfd_body))) fuel s = some t →
        ∃ fuel' t',
          lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg fd'.lfd_body))) fuel' s = some t'
          ∧ Obs outs t t' := by
  refine ⟨{ fd with lfd_body := deadWriteRet fd.lfd_body }, ?_, rfl, rfl, ?_⟩
  · simp only [mapBodies, List.mem_map]
    exact ⟨(fn, fd), hf, rfl⟩
  · intro outs fuel s t hfn hpc hrun
    exact deadWriteRet_lsemFuelMemF outs tg fd.lfd_body hok hfrag fn s t hfn hpc fuel hrun

/-- **`regionPostFuse_deadWriteRet_lsemFuelMemF`: the dead-write half of the region
    post-pass.** Every function `(fn, fd)` of the fused program
    `FuseMulHi.fuseMulHiLprog P (saveRdx := true)` has the function `(fn, fd')` in
    `regionPostFuse P`, with the conclusion of `mapBodies_deadWriteRet_lsemFuelMemF`. -/
theorem regionPostFuse_deadWriteRet_lsemFuelMemF (P : Lprog) {fn : String} {fd : Lfundef}
    (hf : (fn, fd) ∈ (X86Backend.FuseMulHi.fuseMulHiLprog P (saveRdx := true)).lp_funcs)
    (tg : LinstrR → MemTag)
    (hok : ∀ i ∈ fd.lfd_body, deadWriteStepOK tg i.li_i = true)
    (hfrag : symRun (dropRet (typeBody tg fd.lfd_body)) SSt.start ≠ .unk) :
    ∃ fd', (fn, fd') ∈ (regionPostFuse P).lp_funcs ∧ fd'.lfd_res = fd.lfd_res
      ∧ fd'.lfd_body = deadWriteRet fd.lfd_body
      ∧ ∀ (outs : List String) {fuel : Nat} {s t : LstateMF}, s.prog.lfn = fn →
        s.prog.base.reg.lpc = 0 →
        lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg fd.lfd_body))) fuel s = some t →
        ∃ fuel' t',
          lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg fd'.lfd_body))) fuel' s = some t'
          ∧ Obs outs t t' :=
  mapBodies_deadWriteRet_lsemFuelMemF _ hf tg hok hfrag

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseFuel
