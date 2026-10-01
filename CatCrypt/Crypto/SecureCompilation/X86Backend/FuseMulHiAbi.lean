/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry

@[expose] public section

set_option autoImplicit false

/-!
# The `MULX` fusion from a System V entry

`JasminLsemFuseMulHi.fuseMulHi_lsemFuelMemF` takes the registers `E` whose start values
have width `64`. At the ABI entry of an `AbiLayout` (`ExportCertEntry.AbiEntryM`), every
argument name `argName j` of a parameter holds its register's value at width `64`, so the
argument names of the layout discharge that hypothesis.

## Main results

* `abiArgNames` — the argument names of a layout's parameters.
* `e64_of_abiEntryM` — at an ABI entry the argument names hold width-`64` words.
* `fuseMulHi_lsemFuelMemF_abi`, `fuseMulHi_lsemFuelMemF_pre_abi` — the fusion theorems with
  the ABI entry in place of the width hypothesis.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiEntryM)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- The argument names of the parameters of `σ`. -/
def abiArgNames (σ : AbiLayout) : List String := (List.range σ.args.length).map argName

theorem width_of_getW {s : LstateN} {r : String} {w : Nat} {v : BitVec w}
    (h : s.getW r w = some v) : (s.lvm r).1 = w := by
  unfold LstateN.getW at h
  split at h
  · assumption
  · simp at h

/-- At the ABI entry of `σ`, every argument name holds a width-`64` word. -/
theorem e64_of_abiEntryM {σ : AbiLayout} {sa : AState} {b0 : LstateM}
    (h : AbiEntryM σ sa b0) : E64 (abiArgNames σ) b0 := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have hj' : j < σ.args.length := List.mem_range.mp hj
  exact width_of_getW (h.reg j _ (List.getElem?_eq_getElem hj'))

/-- **The fusion from an ABI entry.** For a typed body `c` that passes
    `fuseMulHiOK (abiArgNames σ) c`, every halting run of `c` from an ABI entry of `σ` is
    matched by a halting run of `fuseMulHiRM c` from the same state, as in
    `fuseMulHi_lsemFuelMemF`. -/
theorem fuseMulHi_lsemFuelMemF_abi {σ : AbiLayout} {sa : AState} {c : List LinstrRM}
    (h : fuseMulHiOK (abiArgNames σ) c = true) (fn : String) (s t : LstateMF)
    (hent : AbiEntryM σ sa s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn c) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ lsemFuelMemF (singletonProgM fn (fuseMulHiRM c)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn :=
  fuseMulHi_lsemFuelMemF h fn s t hent.pc (e64_of_abiEntryM hent) fuel hrun

/-- **The fusion of the loop part from an ABI entry.** The instance of
    `fuseMulHi_lsemFuelMemF_pre` at the argument names of `σ`. -/
theorem fuseMulHi_lsemFuelMemF_pre_abi {σ : AbiLayout} {sa : AState}
    {pre loop : List LinstrRM}
    (h : fuseOKL (abiArgNames σ) (fuseLoPre pre loop) (pre ++ loop) = true) (fn : String)
    (s t : LstateMF) (hent : AbiEntryM σ sa s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ lsemFuelMemF (singletonProgM fn (pre ++ fuseMulHiRM loop)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn :=
  fuseMulHi_lsemFuelMemF_pre h fn s t hent.pc (e64_of_abiEntryM hent) fuel hrun

end CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi
