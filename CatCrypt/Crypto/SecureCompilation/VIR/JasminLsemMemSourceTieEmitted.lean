/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd

@[expose] public section

set_option autoImplicit false

/-!
# The emitted runtime-count loop node against `ComL.forLoopNRt`

`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_comL_uncond` runs the
model do-while `loopLinstrRM` over the model body on `lsemFuelMemL`; the exporter
emits `forLoopLcmdNRt` instead, whose typed lift `forLoopLcmdNRtRM`
(`JasminLsemExportLift.forLoopLcmdNRtRM_wire`) carries the zero-trip guard, the
index register `Lidx<d>`, the feedback move, the invariant touches and the flag
back-edge, and runs on the flag machine `lsemFuelMemF`. On that machine the
feedback `MOV acc, ret` copies no array
(`JasminLsemExportTransfer.forLoopLcmdNRtRM_acc_frozen`). The statement is about
the node under a renaming `ρ` that sends the accumulator and the store results to
one output name `out`: the aliased, canonicalised node `ComL.toLfundefPhysAbi`
emits
(`JasminLsemExportCanon.forLoopLcmdNRtRM_canon_wire`).

`forLoopLcmdNRtRM_export_faithful_comL` composes
`JasminLsemExportShippedAnd.forLoopLcmdNRtRM_map_eq_canonNodeRM_expand` (the
renamed node is the immediate-shift expansion of `canonNodeRM`),
`JasminLsemExportCanon.canonNodeRM_faithful` (the canonicalised node halts on the
source fold, through the guarded-skeleton run on the flag fold
`runBoundedStraightF`), `JasminLsemExportShippedAnd.lsemFuelMemF_singleton_expand`
(a halting run carries to the expansion) and
`JasminLsemMemSourceTieUncond.comL_forLoopNRt_ret_denote_acc` (the fold is the
front node's denotation).

## Main results

* `invRegs_eq_comp` — the invariant base registers are the images of the
  invariant arguments under `ρ ∘ σ`.
* `forLoopLcmdNRtRM_export_faithful_comL` — the renamed export node halts with the
  array at `out` decoding to `ComL.forLoopNRt`'s denotation, at every count.
* `AllRes`, `arrUse_ok_of_none`, `threadCert_reg`, `threadCert_store` — one-step
  constructors of `ThreadCert`, for certificates built instruction by
  instruction.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieEmitted

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd

variable {invTys : Ctxt jasminDialect}

/-! ## 1. The emitted node against the front denotation -/

/-- The invariant base registers of a loop renaming, fixed by a node renaming,
    are the images of the invariant arguments under the composite renaming. -/
theorem invRegs_eq_comp {σ ρ : String → String} {d : Nat} {acc out c : String}
    {invRegs : List String} (hσ : LoopRen σ d invTys.length acc invRegs)
    (hρ : NodeRen ρ d acc out c invRegs) :
    ∀ r ∈ invRegs, ∃ j, j < invTys.length ∧ r = (ρ ∘ σ) (argName j) := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hlen := hσ.len
  refine ⟨invTys.length - 1 - i, by omega, ?_⟩
  show _ = ρ (σ (argName (invTys.length - 1 - i)))
  rw [hσ.inv _ (by omega), show invTys.length - 1 - (invTys.length - 1 - i) = i by omega,
    List.getD_eq_getElem _ _ hi, hρ.invFix _ (List.getElem_mem hi)]

/-- **The emitted runtime-count loop node realises `ComL.forLoopNRt`.** The typed
    export node `forLoopLcmdNRtRM` (the lift of `forLoopLcmdNRt`,
    `forLoopLcmdNRtRM_wire`: seed moves, zero-trip guard, index register, body
    walk, feedback move, invariant touches, flag back-edge) of an `ArrMemN` update
    satisfying `ComExpOK`, seeded from `.reg out` with count register `c` and
    renamed by `ρ`, run by `lsemFuelMemF` from program counter `0`, halts with the
    array at `out` decoding to `ComL.forLoopNRt update count initV invsV`'s
    denotation, at every count including zero.

    The remaining hypotheses: `hσ`, the body walk is the model chain under the
    loop renaming `σ`; `hρ`, `ρ` sends the accumulator register to `out` and fixes
    `out`, the index, the counter, `c` and the invariant base registers; `hret`,
    `ρ` sends the body walk's return register to `out`; `hτ` and `hcert`, the
    canonicalisation certificates `CanonRen` and `ThreadCert` of `ρ ∘ σ`; `hseed`,
    the entry state pulled back along `ρ ∘ σ` agrees with the trip-`0` valuation;
    `hinv`, the invariant base registers read at width `64`; `hcnt`, `c` holds the
    runtime count. -/
theorem forLoopLcmdNRtRM_export_faithful_comL {Γ : Ctxt jasminDialect}
    {d w n : Nat} {σ ρ : String → String} {S : Nat → Prop} {acc out c : String}
    (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hσ : LoopRen σ d invTys.length acc (invRegsOf invOps))
    (hρ : NodeRen ρ d acc out c (invRegsOf invOps))
    (hret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out)
    (hτ : CanonRen (ρ ∘ σ) d invTys.length S out)
    (hcert : ThreadCert (ρ ∘ σ) (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM (ρ ∘ σ) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hinv : ∀ j, j < invTys.length → (b0.reg.getW ((ρ ∘ σ) (argName j)) 64).isSome)
    (hcnt : b0.reg.getW c 64 = some (count.lookup V)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          ((forLoopLcmdNRtRM d acc (.reg out) (.reg c) update invOps (fun _ => none)).map
            (renRM ρ))) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out w n
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  have hcnt' : b0.reg.getW c 64 = some (BitVec.ofNat 64 (count.lookup V).toNat) := by
    rw [hcnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨k, t, hrun, hdec⟩ := canonNodeRM_faithful update hupd hτ hcert
    ((loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 == acc) (invRegsOf invOps) (invRegs_eq_comp hσ hρ)
    (Expr.lookupArgs invsV V) fn c hc b0 zf hpc (initV.lookup V) hseed hinv
    (count.lookup V).toNat (count.lookup V).isLt hcnt'
  obtain ⟨k', t', hrun', hlarr⟩ := lsemFuelMemF_singleton_expand fn _
    (canonNodeRM_instrOK _ d out c update hexp _ _) b0 zf hpc k t hrun
  refine ⟨k', t', ?_, ?_⟩
  · rw [forLoopLcmdNRtRM_map_eq_canonNodeRM_expand invOps update
      (ComExpOK.opsPlain _ hexp) hσ hρ hret]
    exact hrun'
  · rw [decodeArrM_congr_larr _ _ hlarr, comL_forLoopNRt_ret_denote_acc]
    exact hdec

/-! ## 2. Building a thread certificate one instruction at a time -/

/-- Every name of a list is resolved at chain depth `cd` with `nArgs` arguments. -/
def AllRes (nArgs cd : Nat) : List String → Prop
  | [] => True
  | n :: l => Resolved nArgs cd n ∧ AllRes nArgs cd l

/-- `AllRes` gives `Resolved` at every member. -/
theorem AllRes.mem {nArgs cd : Nat} :
    ∀ {L : List String}, AllRes nArgs cd L → ∀ n ∈ L, Resolved nArgs cd n
  | [], _, _, hn => absurd hn List.not_mem_nil
  | _ :: _, ⟨h1, h2⟩, _, hn => by
      rcases List.mem_cons.1 hn with rfl | hn
      · exact h1
      · exact AllRes.mem h2 _ hn

theorem AllRes.cons {nArgs cd : Nat} {n : String} {l : List String}
    (h1 : Resolved nArgs cd n) (h2 : AllRes nArgs cd l) : AllRes nArgs cd (n :: l) :=
  ⟨h1, h2⟩

theorem AllRes.nil {nArgs cd : Nat} : AllRes nArgs cd [] := trivial

/-- An instruction that uses no array passes the array-use condition. -/
theorem arrUse_ok_of_none {τ : String → String} {out h : String} {i : LinstrRM}
    (hn : arrUse? i = none) : ∀ b, arrUse? i = some b → τ b = out → b = h := by
  intro b hb
  rw [hn] at hb
  cases hb

/-- One register binding of a thread certificate. -/
theorem threadCert_reg {τ : String → String} {nArgs : Nat} {S : Nat → Prop} {out : String}
    {i : LinstrRM} {is : List LinstrRM} {cd : Nat} {h hE : String}
    (hres : AllRes nArgs cd (useNames i.1))
    (harr : ∀ b, arrUse? i = some b → τ b = out → b = h)
    (hs : storeHit? i = none) (hd : defNames i.1 = [regName cd]) (hS : ¬ S cd)
    (hrest : ThreadCert τ nArgs S out is (cd + 1) h hE) :
    ThreadCert τ nArgs S out (i :: is) cd h hE :=
  ⟨hres.mem, harr, Or.inl ⟨hs, hd, hS, hrest⟩⟩

/-- One store of a thread certificate. -/
theorem threadCert_store {τ : String → String} {nArgs : Nat} {S : Nat → Prop} {out : String}
    {i : LinstrRM} {is : List LinstrRM} {cd : Nat} {h hE : String}
    (hres : AllRes nArgs cd (useNames i.1))
    (harr : ∀ b, arrUse? i = some b → τ b = out → b = h)
    (hs : storeHit? i = some (regName cd)) (hS : S cd)
    (hrest : ThreadCert τ nArgs S out is (cd + 1) (regName cd) hE) :
    ThreadCert τ nArgs S out (i :: is) cd h hE :=
  ⟨hres.mem, harr, Or.inr ⟨hs, hS, hrest⟩⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieEmitted
