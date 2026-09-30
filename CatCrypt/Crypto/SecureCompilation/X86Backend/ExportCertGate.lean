/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight

@[expose] public section

set_option autoImplicit false

/-!
# The Boolean export gate of the single-loop route

`ExportCertLoop.comLCertB` checks the renaming certificate of a single-loop program. The
export theorem also asks the fragment conditions `ArrMemN` and `ComExpOK` of the loop's
update. `singleLoopB` adds their decisions `arrMemNB` and `comExpOKB`, so that an accepted
program needs no hypothesis beyond the System V entry.

## Main results

* `singleLoopB`, `singleLoopB_singleLoop` — the gate on a looped program and its value on
  the single-loop program.
* `singleLoop_export_faithful_gate` — the single-loop export theorem under the gate, with the
  entry hypotheses `AbiValOf` and `AbiEntryM` only.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- **The gate of a single-loop export.** On a runtime-count loop node over an array
    accumulator followed by a return: the update passes `arrMemNB` and `comExpOKB`, and the
    program passes `loopCertB`; `false` on every other program. -/
def singleLoopB : {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → String →
    List String → List String → Bool
  | _, _, @ComL.forLoopNRt _ (.stackArr _ _) _ _ update count init invs (.ret _), outArg,
      inArgs, abiArgs =>
      arrMemNB update && comExpOKB update
        && loopCertB update count init invs outArg inArgs abiArgs
  | _, _, _, _, _, _ => false

/-- On the single-loop program, `singleLoopB` is the conjunction of the fragment checks and
    `loopCertB`. -/
theorem singleLoopB_singleLoop {Γ : Ctxt jasminDialect} {w n : Nat} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (outArg : String)
    (inArgs abiArgs : List String) :
    singleLoopB (singleLoop update count init invs) outArg inArgs abiArgs
      = (arrMemNB update && comExpOKB update
          && loopCertB update count init invs outArg inArgs abiArgs) := rfl

/-- **The gated single-loop export from the System V entry.** For the program with one
    runtime-count loop node and nothing after it that passes `singleLoopB`: the seed and
    count resolve to registers `out` and `c`; the body `ComL.toLfundefPhysAbi` allocates is
    the liveness pin, `certNode` and the return, instruction for instruction; and for every
    valuation that a layout reads off an entry state (`AbiValOf`) and every flag-machine
    ABI entry of that state (`AbiEntryM`), `certNode` halts under `lsemFuelMemF` with the
    array at `out` decoding to the program's denotation. -/
theorem singleLoop_export_faithful_gate {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (h : singleLoopB (singleLoop update count init invs) outArg inArgs abiArgs = true) :
    ∃ out c, resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out
      ∧ resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c
      ∧ (abiBody1 (singleLoop update count init invs) outArg inArgs (fun _ => none)
            abiArgs).map (·.li_i)
          = (abiLivePin abiArgs).map (·.li_i) ++ (certNode update invs out c).map Prod.fst
            ++ [.Lret]
      ∧ ∀ (σ : AbiLayout) (sa : AState) (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM)
          (zf : Bool), AbiValOf σ sa V → AbiEntryM σ sa b0 →
          ∃ (k : Nat) (t : LstateMF),
            lsemFuelMemF (singletonProgM fn (certNode update invs out c)) k
                { prog := { base := b0, lfn := fn }, zf := zf } = some t
              ∧ decodeArrM t.prog.base out w n
                  = some ((singleLoop update count init invs).denote V) := by
  rw [singleLoopB_singleLoop] at h
  simp only [Bool.and_eq_true] at h
  exact singleLoop_export_faithful_abi update count init invs outArg inArgs abiArgs
    (arrMemNB_sound update h.1.1) (comExpOKB_sound update h.1.2) h.2

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate
