/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape

@[expose] public section

set_option autoImplicit false

/-!
# The export certificate of the single-loop physical-ABI export

`ComL.toLfundefPhysAbi` of the program with one runtime-count loop node and nothing after it
(`PhysAbiShape.singleLoop`) allocates the virtual body `PhysAbiShape.abiBody1`: the argument
liveness pin, the loop node with the accumulator aliased onto the out-array name and the store
thread canonicalised, and the return. `loopCertB` is the check a compiler runs on such a
program: the operands the export resolves for the seed and the count are registers `out` and
`c`, the node passes `JasminLsemExportCert.exportCertB` at loop depth `Γ.length` and
accumulator register `regName Γ.length`, and the instructions of `abiBody1` are the pin, the
typed node `forLoopLcmdNRtRM` renamed by `certRho` over the computed store slots, and the
return.

## Main results

* `loopInvOps`, `certNode`, `loopCertB` — the invariant operands of the export, the
  certified typed node and the check.
* `comLCertB`, `comLCertB_singleLoop` — the check on a looped program, and its value on the
  single-loop program.
* `loopCertB_spec` — an accepted program has register seed and count operands, passes
  `exportCertB`, and its allocated virtual body is the pin, the certified node and the
  return, instruction for instruction.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (forLoopLcmdNRtRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape

variable {Γ : Ctxt jasminDialect} {w n : Nat} {invTys : Ctxt jasminDialect}

/-- The invariant operands the export resolves for the invariant seeds `invs`. -/
def loopInvOps (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) : List LOperand :=
  exprArgsHV Γ.length Γ.length argName (fun _ => none) invs

/-- The typed loop node of the certificate: `forLoopLcmdNRtRM` at loop depth `Γ.length`,
    accumulator register `regName Γ.length`, seed register `out` and count register `c`,
    renamed by `certRho` over the store slots of the update's chain. -/
def certNode (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (out c : String) : List LinstrRM :=
  (forLoopLcmdNRtRM Γ.length (regName Γ.length) (.reg out) (.reg c) update (loopInvOps invs)
      (fun _ => none)).map
    (renRM (certRho Γ.length (regName Γ.length) out (certSlots update)))

/-- **The check of a single-loop export.** The seed and the count resolve to registers `out`
    and `c`, the loop node passes `exportCertB`, and the allocated virtual body `abiBody1` is
    the liveness pin, `certNode` and the return, instruction for instruction. -/
def loopCertB (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String) : Bool :=
  match resolveVar Γ.length Γ.length argName (fun _ => none) init,
      resolveVar Γ.length Γ.length argName (fun _ => none) count with
  | .reg out, .reg c =>
      exportCertB Γ.length (regName Γ.length) out c update (loopInvOps invs)
      && (abiBody1 (singleLoop update count init invs) outArg inArgs (fun _ => none)
            abiArgs).map (·.li_i)
          == (abiLivePin abiArgs).map (·.li_i) ++ (certNode update invs out c).map Prod.fst
            ++ [.Lret]
  | _, _ => false

/-- **Soundness of the single-loop check.** An accepted program resolves its seed and count
    to registers `out` and `c`, passes `exportCertB` there, and allocates the virtual body
    whose instructions are the pin, the certified node and the return. -/
theorem loopCertB_spec {update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)}
    {count : Ctxt.Var Γ (JasminTy.reg 64)} {init : Ctxt.Var Γ (JasminTy.stackArr w n)}
    {invs : HVector (fun ty => Ctxt.Var Γ ty) invTys}
    {outArg : String} {inArgs abiArgs : List String}
    (h : loopCertB update count init invs outArg inArgs abiArgs = true) :
    ∃ out c, resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out
      ∧ resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c
      ∧ exportCertB Γ.length (regName Γ.length) out c update (loopInvOps invs) = true
      ∧ (abiBody1 (singleLoop update count init invs) outArg inArgs (fun _ => none)
            abiArgs).map (·.li_i)
          = (abiLivePin abiArgs).map (·.li_i) ++ (certNode update invs out c).map Prod.fst
            ++ [.Lret] := by
  unfold loopCertB at h
  split at h
  · next out c hi hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨out, c, hi, hc, h.1, h.2⟩
  · cases h

/-- The check on a looped program: `loopCertB` on a runtime-count loop node over an array
    accumulator followed by a return, `false` on every other program. -/
def comLCertB : {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → String → List String →
    List String → Bool
  | _, _, @ComL.forLoopNRt _ (.stackArr _ _) _ _ update count init invs (.ret _), outArg,
      inArgs, abiArgs => loopCertB update count init invs outArg inArgs abiArgs
  | _, _, _, _, _, _ => false

/-- On the single-loop program, `comLCertB` is `loopCertB`. -/
theorem comLCertB_singleLoop (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (outArg : String)
    (inArgs abiArgs : List String) :
    comLCertB (singleLoop update count init invs) outArg inArgs abiArgs
      = loopCertB update count init invs outArg inArgs abiArgs := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
