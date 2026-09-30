/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieEmitted

@[expose] public section

set_option autoImplicit false

/-!
# The certified export of a runtime-count loop node realises its denotation

`JasminLsemMemSourceTieEmitted.forLoopLcmdNRtRM_export_faithful_comL` takes the loop renaming,
the node renaming and the canonicalisation certificates as hypotheses.
`JasminLsemExportCert.exportCertB_sound` produces all of them from one Boolean check at the
renamings `certSigma` and `certRho`. This module composes the two, and with
`ExportCertLoop.loopCertB_spec` states the result for the single-loop physical-ABI export:
the body `ComL.toLfundefPhysAbi` allocates is the pin, the certified node and the return, and
the certified node, run on the flag machine `lsemFuelMemF`, halts with the array at the
output register decoding to the program's denotation. No program is named; the entry-state
hypotheses (`hseed`, readable invariant base registers, the count register) and the
fragment conditions `ArrMemN` and `ComExpOK` of the update remain hypotheses.

## Main results

* `certTau` — the canonicalisation renaming `certRho ∘ certSigma` of a node.
* `forLoopLcmdNRtRM_export_faithful_cert` — a node that passes `exportCertB`, renamed by
  `certRho`, halts with the array at `out` decoding to `ComL.forLoopNRt`'s denotation.
* `singleLoop_export_faithful_cert` — for a single-loop program that passes `loopCertB`, the
  allocated virtual body is the pin, the certified node and the return, and the certified
  node halts with the array at the seed register decoding to the program's denotation.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFaithful

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (forLoopLcmdNRtRM invRegsOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon (pullM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd (ComExpOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (tripValArrMN decodeArrM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieEmitted
  (forLoopLcmdNRtRM_export_faithful_comL)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop

variable {Γ : Ctxt jasminDialect} {w n : Nat} {invTys : Ctxt jasminDialect}

/-- The canonicalisation renaming of a certified node: `certRho` over the store slots of the
    update's chain, after `certSigma`. -/
noncomputable abbrev certTau (d : Nat) (acc out : String)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invOps : List LOperand) : String → String :=
  certRho d acc out (certSlots update) ∘ certSigma d invTys.length acc (invRegsOf invOps)

/-- **A certified loop node realises `ComL.forLoopNRt`.** Let the node at loop depth `d`,
    accumulator register `acc`, output register `out`, count register `c` and invariant
    operands `invOps` pass `exportCertB`, and let the update be in the fragment `ArrMemN` with
    `ComExpOK`. The typed export node `forLoopLcmdNRtRM`, renamed by `certRho`, run by
    `lsemFuelMemF` from program counter `0` from an entry state that agrees with the trip-`0`
    valuation along `certTau` (`hseed`), reads every invariant base register at width `64`
    and holds the runtime count in `c`, halts with the array at `out` decoding to
    `ComL.forLoopNRt update count initV invsV`'s denotation. -/
theorem forLoopLcmdNRtRM_export_faithful_cert {d : Nat} {acc out c : String}
    (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : exportCertB d acc out c update invOps = true)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM (certTau d acc out update invOps) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hinv : ∀ r ∈ invRegsOf invOps, (b0.reg.getW r 64).isSome)
    (hcnt : b0.reg.getW c 64 = some (count.lookup V)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          ((forLoopLcmdNRtRM d acc (.reg out) (.reg c) update invOps (fun _ => none)).map
            (renRM (certRho d acc out (certSlots update))))) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out w n
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  have hc := exportCertB_sound hcert
  refine forLoopLcmdNRtRM_export_faithful_comL (S := (· ∈ certSlots update)) invOps update
    hupd hexp hc.loopRen hc.nodeRen hc.ret hc.canon hc.thread count initV invsV V fn
    hc.cntIdx b0 zf hpc hseed ?_ hcnt
  intro j hj
  have hmem : certSigma d invTys.length acc (invRegsOf invOps) (argName j)
      ∈ invRegsOf invOps := by
    rw [certSigma_inv hj]
    exact getD_mem_of_lt (by rw [hc.loopRen.len]; omega) _
  show (b0.reg.getW (certRho d acc out (certSlots update)
    (certSigma d invTys.length acc (invRegsOf invOps) (argName j))) 64).isSome
  rw [hc.nodeRen.invFix _ hmem]
  exact hinv _ hmem

/-- **The certified single-loop export realises its program.** For the program with one
    runtime-count loop node and nothing after it that passes `loopCertB`, whose update is in
    `ArrMemN` with `ComExpOK`: the seed and count resolve to registers `out` and `c`; the
    body `ComL.toLfundefPhysAbi` allocates is the liveness pin, `certNode` and the return,
    instruction for instruction; and `certNode`, run by `lsemFuelMemF` from program counter
    `0` from an entry state satisfying the seed agreement along `certTau`, reading every
    invariant base register and holding the runtime count in `c`, halts with the array at
    `out` decoding to the program's denotation. -/
theorem singleLoop_export_faithful_cert
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true) :
    ∃ out c, resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out
      ∧ resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c
      ∧ (abiBody1 (singleLoop update count init invs) outArg inArgs (fun _ => none)
            abiArgs).map (·.li_i)
          = (abiLivePin abiArgs).map (·.li_i) ++ (certNode update invs out c).map Prod.fst
            ++ [.Lret]
      ∧ ∀ (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM) (zf : Bool), b0.lpc = 0 →
          StoreAgreesM (invTys.length + 2) (invTys.length + 2)
            (pullM (certTau Γ.length (regName Γ.length) out update (loopInvOps invs))
              (b0.setReg (loopIdx Γ.length) (0#64)))
            (tripValArrMN (Expr.lookupArgs invs V) 0 (init.lookup V)) →
          (∀ r ∈ invRegsOf (loopInvOps invs), (b0.reg.getW r 64).isSome) →
          b0.reg.getW c 64 = some (count.lookup V) →
          ∃ (k : Nat) (t : LstateMF),
            lsemFuelMemF (singletonProgM fn (certNode update invs out c)) k
                { prog := { base := b0, lfn := fn }, zf := zf } = some t
              ∧ decodeArrM t.prog.base out w n
                  = some ((singleLoop update count init invs).denote V) := by
  obtain ⟨out, c, hi, hcn, hx, hbody⟩ := loopCertB_spec hcert
  refine ⟨out, c, hi, hcn, hbody, ?_⟩
  intro V fn b0 zf hpc hseed hinv hcnt
  exact forLoopLcmdNRtRM_export_faithful_cert (loopInvOps invs) update hupd hexp hx count init
    invs V fn b0 zf hpc hseed hinv hcnt

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFaithful
