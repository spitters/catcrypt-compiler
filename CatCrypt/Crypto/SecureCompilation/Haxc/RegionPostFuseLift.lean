/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseFuel
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

/-!
# The region post-pass on the functions of a program

The region post-pass `regionPostFuse P` is the high-product fusion
`FuseMulHi.fuseMulHiLprog P (saveRdx := true)` followed by the dead-write elimination
`deadWriteRet` on every function body. This module lifts the theorem of the fusion on one typed
body, `JasminLsemFuseMulHi.fuseMulHi_lsemFuelMemF`, to the functions of a program, and composes
it with the dead-write half `RegionPostFuseFuel.regionPostFuse_deadWriteRet_lsemFuelMemF`.

The fused body of the flag machine, `JasminLsemFuseMulHi.fuseMulHiRM`, reads each two-output
`MULX` of `fuseMulHiBody` at its width (`JasminLsemFuseMulHi.normMulx`); the flag machine steps
`MULX` only at that width. The composition therefore runs the dead-write half on the body read
the same way, `normMulxBody`, and states the run of the output body in that reading.

## Main definitions

* `normMulxBody`: a body with every `MULX` read at its width.

## Main results

* `fuseMulHiLprog_lsemFuelMemF`: the fusion on every function of a program.
* `regionPostFuse_lsemFuelMemF`: the region post-pass on every function of a program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
  (Agree E64 fuseMulHiOK fuseMulHiRM normMulx fuseMulHi_lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiLprog fuseMulHiBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.DeadWriteRetSound

/-- A body with every two-output `MULX` read at its width `MULX:64` (`normMulx`), every
    instruction index unchanged. -/
def normMulxBody (c : Lcmd) : Lcmd := c.map fun j => ⟨j.li_ii, normMulx j.li_i⟩

/-- **`fuseMulHiLprog_lsemFuelMemF`: the fusion on the functions of a program.** Every function
    `(fn, fd)` of `P` has the function `(fn, fd')` in `fuseMulHiLprog P (saveRdx := true)`, with
    the same result registers and the body `fuseMulHiBody fd.lfd_body true`. When the typed body
    without its return passes `fuseMulHiOK E`, every halting run of it from program counter `0`,
    from a base whose registers in `E` have width `64`, is matched by a halting run of its fusion
    `fuseMulHiRM` from the same state with at most four times the fuel; the final states agree
    outside `R15` (`JasminLsemFuseMulHi.Agree`), on the zero flag and on the function name. -/
theorem fuseMulHiLprog_lsemFuelMemF (P : Lprog) {fn : String} {fd : Lfundef}
    (hf : (fn, fd) ∈ P.lp_funcs) (tg : LinstrR → MemTag) {E : List String}
    (hok : fuseMulHiOK E (dropRet (typeBody tg fd.lfd_body)) = true) :
    ∃ fd', (fn, fd') ∈ (fuseMulHiLprog P (saveRdx := true)).lp_funcs
      ∧ fd'.lfd_res = fd.lfd_res ∧ fd'.lfd_body = fuseMulHiBody fd.lfd_body true
      ∧ ∀ {fuel : Nat} {s t : LstateMF}, s.prog.base.lpc = 0 → E64 E s.prog.base →
        lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg fd.lfd_body))) fuel s = some t →
        ∃ fuel' t', fuel' ≤ fuel * 4
          ∧ lsemFuelMemF (singletonProgM fn (fuseMulHiRM (dropRet (typeBody tg fd.lfd_body))))
              fuel' s = some t'
          ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  refine ⟨{ fd with lfd_body := fuseMulHiBody fd.lfd_body true }, ?_, rfl, rfl, ?_⟩
  · simp only [fuseMulHiLprog, List.mem_map]
    exact ⟨(fn, fd), hf, rfl⟩
  · intro fuel s t hpc hE hrun
    exact fuseMulHi_lsemFuelMemF hok fn s t hpc hE fuel hrun

/-- **`regionPostFuse_lsemFuelMemF`: the region post-pass on the functions of a program.**
    Every function `(fn, fd)` of `P` has the function `(fn, fd'')` in `regionPostFuse P`, with
    the same result registers and the body `deadWriteRet (fuseMulHiBody fd.lfd_body true)`.
    Write `F` for `normMulxBody (fuseMulHiBody fd.lfd_body true)`. The hypotheses are decided on
    the bodies: the typed body without its return passes `fuseMulHiOK E`; its fusion
    `fuseMulHiRM` is the typed `F` without its return; `F` passes the checks of the dead-write
    elimination; and the elimination commutes with `normMulxBody` on the fused body. Then every
    halting run of the typed body without its return, from program counter `0` and function
    `fn`, from a base whose registers in `E` have width `64`, ends in a state `t` such that a
    state `t1` agrees with `t` outside `R15` (`JasminLsemFuseMulHi.Agree`), on the zero flag
    and the function name, and the typed `normMulxBody fd''.lfd_body` without its return halts from
    the same start in a state `t2` with `OwnedLprogTV.Obs outs t1 t2`. -/
theorem regionPostFuse_lsemFuelMemF (P : Lprog) {fn : String} {fd : Lfundef}
    (hf : (fn, fd) ∈ P.lp_funcs) (tg : LinstrR → MemTag) {E : List String}
    (hok : fuseMulHiOK E (dropRet (typeBody tg fd.lfd_body)) = true)
    (hty : fuseMulHiRM (dropRet (typeBody tg fd.lfd_body))
      = dropRet (typeBody tg (normMulxBody (fuseMulHiBody fd.lfd_body true))))
    (hdw : ∀ i ∈ normMulxBody (fuseMulHiBody fd.lfd_body true),
      deadWriteStepOK tg i.li_i = true)
    (hfrag : symRun (dropRet (typeBody tg (normMulxBody (fuseMulHiBody fd.lfd_body true))))
      SSt.start ≠ .unk)
    (hcomm : deadWriteRet (normMulxBody (fuseMulHiBody fd.lfd_body true))
      = normMulxBody (deadWriteRet (fuseMulHiBody fd.lfd_body true))) :
    ∃ fd'', (fn, fd'') ∈ (regionPostFuse P).lp_funcs ∧ fd''.lfd_res = fd.lfd_res
      ∧ fd''.lfd_body = deadWriteRet (fuseMulHiBody fd.lfd_body true)
      ∧ ∀ (outs : List String) {fuel : Nat} {s t : LstateMF}, s.prog.lfn = fn →
        s.prog.base.reg.lpc = 0 → E64 E s.prog.base →
        lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg fd.lfd_body))) fuel s = some t →
        ∃ t1 fuel'' t2, Agree t.prog.base t1.prog.base ∧ t1.zf = t.zf
          ∧ t1.prog.lfn = t.prog.lfn
          ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg (normMulxBody fd''.lfd_body))))
              fuel'' s = some t2
          ∧ Obs outs t1 t2 := by
  obtain ⟨fd', hmem', hres', hbody', hsim⟩ := fuseMulHiLprog_lsemFuelMemF P hf tg hok
  refine ⟨{ fd' with lfd_body := deadWriteRet fd'.lfd_body }, ?_, hres', ?_, ?_⟩
  · simp only [regionPostFuse, X86Backend.LprogOptPipeline.mapBodies, List.mem_map]
    exact ⟨(fn, fd'), hmem', rfl⟩
  · simp only [hbody']
  · intro outs fuel s t hfn hpc hE hrun
    obtain ⟨f1, t1, -, hrun1, hA, hz, hl⟩ := hsim hpc hE hrun
    rw [hty] at hrun1
    obtain ⟨f2, t2, hrun2, hobs⟩ :=
      deadWriteRet_lsemFuelMemF outs tg _ hdw hfrag fn s t1 hfn hpc f1 hrun1
    refine ⟨t1, f2, t2, hA, hz, hl, ?_, hobs⟩
    simp only [hbody']
    rw [← hcomm]
    exact hrun2

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift
