/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestInline
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The inline two-level nest export, for an array-carrier accumulator

`JasminLsemMemLoopNestInline` decodes the inline two-level nest to
`JLoopBodyN.nestedDenote` for a **register** accumulator (`decodeM … accReg w`), on
top of the decoder-agnostic engine `runBoundedIBs_decodes_fold_gen`. This module
instantiates that engine at the array decoder `decodeArrM`, so a nested loop whose
accumulator is a stack-memory array (as in `mpn_mul_basecase`, whose inner update
`bcRowUpdate` returns a `.stackArr`) reaches the same `nestedDenote` conclusion.
`JLoopBodyN.nestedDenote` / `stepCNested` / `innerTripAtC` are already polymorphic
over the accumulator `JasminTy`; only the decoder changes.

## Main results

* `runBoundedIBs_decodes_nestedDenoteArr` — the array-decoder instance of the
  bounded fold: the `m`-fold decodes at the array slot to `nestedDenote`.
* `inlineNest_export_decodes_nestedDenoteArr` — the composed inline-nest export at
  the array slot: the machine run halts at a state whose accumulator array decodes
  to `nestedDenote`, with the per-outer-pass simulation as a hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrNestInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestInline

/-- **The bounded fold decodes to `JLoopBodyN.nestedDenote` (array accumulator).**
    The `decodeArrM` instance of `runBoundedIBs_decodes_fold_gen`: per outer pass the
    effect is one inner fold of `stepCNested` over the recomputed trip
    `innerTripAtC`, and the `m`-fold decodes at the array slot to the nested runtime
    fold — the source semantics of `ComL.forLoopNRtNested` for an array-carrier
    accumulator. -/
theorem runBoundedIBs_decodes_nestedDenoteArr {w n : Nat} {invTys : Ctxt jasminDialect}
    (env : LeafEnvM) (wf : Nat) (body : List IBlock) (p : Nat) (accReg : String)
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect
      (JasminTy.stackArr w n :: .reg 64 :: .reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : Ctxt.Valuation invTys) (s0 : LstateM) (acc0 : Fin n → BitVec w)
    (hinit : decodeArrM s0 accReg w n = some acc0) (m : Nat)
    (hsim : ∀ t, t < m → ∀ (bt : LstateM) (acct : Fin n → BitVec w),
      runBoundedIBs env wf body p t s0 = some bt →
      decodeArrM bt accReg w n = some acct →
      ∀ bt', runIBsL env wf body bt = some bt' →
      decodeArrM bt' accReg w n
        = some ((List.range (JLoopBodyN.innerTripAtC innerCount invs t)).foldl
            (fun a u => JLoopBodyN.stepCNested innerUpdate invs t u a) acct))
    (bfin : LstateM) (hrun : runBoundedIBs env wf body p m s0 = some bfin) :
    decodeArrM bfin accReg w n
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate m invs acc0) :=
  runBoundedIBs_decodes_fold_gen env wf body p (fun s => decodeArrM s accReg w n)
    (fun b k => decodeArrM_setLpc b k accReg w n)
    (fun t a => (List.range (JLoopBodyN.innerTripAtC innerCount invs t)).foldl
      (fun a2 u => JLoopBodyN.stepCNested innerUpdate invs t u a2) a)
    s0 acc0 hinit m hsim bfin hrun

/-- **The composed inline-nest export theorem (array-decoder form).**  For the
    emitted two-level inline nest — the whole program is one outer region whose body
    blocks recompute the inner count and run the inner region — under the
    per-outer-pass array simulation, the machine run from the encoded seed halts at a
    state whose accumulator array decodes to **`JLoopBodyN.nestedDenote`** at the trip
    count `m` read off the run. The array-carrier analog of
    `inlineNest_export_decodes_nestedDenote`. -/
theorem inlineNest_export_decodes_nestedDenoteArr {w n : Nat} {invTys : Ctxt jasminDialect}
    (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String) (body : List IBlock)
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect
      (JasminTy.stackArr w n :: .reg 64 :: .reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : Ctxt.Valuation invTys)
    (wf : Nat) (s : LstatePMC) (bfin : LstateM) (accReg : String) (acc0 : Fin n → BitVec w)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 0)
    (hok : IBlocksOK env (singletonProgM fn (flatL [IBlock.region top nReg body]))
      [IBlock.region top nReg body])
    (hres : IBlocksResolve (singletonProgM fn (flatL [IBlock.region top nReg body]))
      [IBlock.region top nReg body] 0)
    (hrun : runIBsL env wf [IBlock.region top nReg body] s.base = some bfin)
    (hinit : decodeArrM s.base accReg w n = some acc0)
    (hsim : ∀ t (bt : LstateM) (acct : Fin n → BitVec w),
      runBoundedIBs env wf body 0 t (s.base.setLpc 1) = some bt →
      decodeArrM bt accReg w n = some acct →
      ∀ bt', runIBsL env wf body bt = some bt' →
      decodeArrM bt' accReg w n
        = some ((List.range (JLoopBodyN.innerTripAtC innerCount invs t)).foldl
            (fun a u => JLoopBodyN.stepCNested innerUpdate invs t u a) acct)) :
    ∃ (nf m : Nat) (t : LstatePMC), 0 < m
      ∧ lsemFuelMemLC env (singletonProgM fn (flatL [IBlock.region top nReg body])) nf s
          = some t
      ∧ t.base = bfin
      ∧ runBoundedIBs env wf body 0 m (s.base.setLpc 1) = some (bfin.setLpc 1)
      ∧ decodeArrM t.base accReg w n
          = some (JLoopBodyN.nestedDenote innerCount innerUpdate m invs acc0) := by
  obtain ⟨nf, hn⟩ := inlineNest_closed env fn [IBlock.region top nReg body] wf s bfin
    hfn hpc hok hres hrun
  have hrunR : runRegion env nReg body 0 wf (s.base.setLpc 1) = some bfin := by
    rw [runIBsL_cons] at hrun
    cases hx : runIB env wf (IBlock.region top nReg body) s.base with
    | none => rw [hx] at hrun; simp at hrun
    | some x =>
        rw [hx, Option.bind_some, runIBsL_nil] at hrun
        obtain rfl := Option.some.inj hrun
        rw [runIB_region] at hx
        have hlpc : s.base.lpc = 0 := hpc
        rw [hlpc, Nat.zero_add] at hx
        exact hx
  obtain ⟨m, hm, hbound, _, _⟩ := runRegion_reconstructs env nReg body 0 wf _ bfin hrunR
  have hbound' : runBoundedIBs env wf body 0 m (s.base.setLpc 1)
      = some (bfin.setLpc 1) := by
    simpa using hbound
  have hinit' : decodeArrM (s.base.setLpc 1) accReg w n = some acc0 := by
    rw [decodeArrM_setLpc]; exact hinit
  have hdec := runBoundedIBs_decodes_nestedDenoteArr env wf body 0 accReg innerCount
    innerUpdate invs (s.base.setLpc 1) acc0 hinit' m
    (fun t _ => hsim t) (bfin.setLpc 1) hbound'
  rw [decodeArrM_setLpc] at hdec
  exact ⟨nf, m, { s with base := bfin }, hm, hn, rfl, hbound', hdec⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrNestInline
