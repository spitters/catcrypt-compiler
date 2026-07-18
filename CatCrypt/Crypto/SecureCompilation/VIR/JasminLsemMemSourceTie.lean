/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

set_option autoImplicit false

/-!
# The fold → source-`Com` tie for the memref export chain (B4)

The B3 export theorems (`JasminLsemMemChainBridge`) end at the **spec fold**:
the emitted control-flow form's machine run `decodeM`s to
`runBoundedLoopMem` / `runBoundedLoopMemC` / `runWhileMem` / `lsemStraightMemDN`.
This file ties those folds to the **source semantics** — `JLoopBodyN.denote` /
`JLoopBodyN.nestedDenote` / `Com.denote`, the denotations the front emits
(`ComL.forLoopNRt` / `ComL.forLoopNRtNested`) — the `LstateM` analogue of the
register template's second half (`JasminLsemLoop.general_loopBody_lsem_faithful`
via `JForProgCT.loopRun_eq`).

Structure (mirroring the register template):

1. **Per-iteration bridge** (§1): one pass of the linearizer-emitted body chain
   `straightOpsMem` under `lsemStraightMem`, from the encoded trip valuation
   `[acc, ofNat t, *invs]`, decodes at the return register to
   `JLoopBodyN.stepC update invs t acc` — the source loop's per-iteration ground
   truth. This **instantiates** the straight-line faithfulness
   `comToLprog_lsemMem` (never re-proved) at the loop-body context
   `accTy :: .reg 64 :: invTys`.
2. **Fold = source denotation** (§2): the `n`-fold of the machine body runner
   equals `JLoopBodyN.denote ⟨n, update⟩ invs init` — the `LstateM` analogue of
   `general_loopBody_lsem_faithful`.
3. **`runBoundedLoopMem` decodes to `JLoopBodyN.denote`** (§3): the fold
   induction lifting a per-trip simulation through the A1 machine-state fold:
   if each trip of the emitted body computes one `stepC` under the `decodeM`
   correspondence, the whole `m`-fold decodes to the source loop's `m`-fold
   denotation.
4. **Composed export theorems** (§4): `loopMem_export_faithful_denote` /
   `loopMem_export_faithful_comL` — the A1 export theorem's conclusion
   strengthened from the spec fold to `JLoopBodyN.denote` = the front-emitted
   `ComL.forLoopNRt`'s `ComL.denote`: **the emitted loop's machine execution
   decodes to the source `Com` denotation**. §4b clones the fold induction and
   the composed export theorem for A2 (`runBoundedLoopMemC_decodes_denote` /
   `loopCall_export_faithful_denote` — the loop whose body calls a linked
   leaf).
5. **The `Lcall` leaf tie** (§5): the depth-N export theorem at depth 0
   composed with the straight-line faithfulness — a caller `Lcall`-ing an
   emitted `ScalarMemN` leaf runs to a halt state that decodes to the leaf's
   `Com.denote`.
6. **The nested tie** (§6): the per-outer inner-count bridge + the innermost
   body bridge + the double-fold: the machine body runners realise
   `JLoopBodyN.nestedDenote` — the source side of `ComL.forLoopNRtNested`
   (the `fri_proof` / GGM shape).
7. **Validation** (§7): a concrete 2-trip emitted loop (the `straightOpsMem`
   chain of `acc := acc + acc` + accumulator writeback + counter decrement)
   run by `lsemFuelMemL` decodes to `JLoopBodyN.denote` — the composed tie is
   realised end-to-end on a real back-edge.

Honest residuals (named, not papered over):
* The per-trip simulation hypothesis `hsim` of §3/§4/§4b is discharged here
  generically at the **encoded** trip states (§1) and concretely in §7; its
  *unconditional* discharge for the emitted `chain ++ writeback` body shape
  lives in `JasminLsemMemSourceTieUncond` (via the strengthened
  `lsemStraightMem_straightOps_store` — final store agreement + write frame),
  whose `loopMem_export_faithful_denote_uncond` / `_comL_uncond` carry only
  schedule/seed/name-hygiene hypotheses. The array-carrier decode analogue
  (`decodeArrM`, array-accumulator fold/export, the fill shape) lives there too.
* The while form (A3) has no `ComL` source node in this lane (the guard-while
  front is `TranslateDialectGuardWhile`); its tie follows the same pattern once
  a source node exists.
* The inline-nested **machine** fold (B5) is the remaining first half for §6's
  source-side tie; the nested-call route (`calleeRunDN`) is covered via §5.

**0 sorries; axioms = {propext, Classical.choice, Quot.sound} + the
pre-existing `aesSboxArrayW_size` `native_decide` (inherited from the
`jasminDialect` denotation by every statement mentioning `Com.denote`, already
carried by the imported `comToLprog_lsemMem`) (+ `Lean.ofReduceBool` for the §7
concrete witness).** The `lsem→bytes` encoder + Sail tables remain the declared
trusted base.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift

/-! ## 1. The per-iteration bridge: one emitted-body pass = one `stepC`

The loop-body context of a `forLoopNRt` node is `accTy :: .reg 64 :: invTys`
(accumulator, trip index, invariants). One trip at index `t` from accumulator
`acc` denotes `JLoopBodyN.stepC update invs t acc = update.denote [acc, ofNat t,
*invs]`. The emitted body chain is `straightOpsMem` over that context; running
it under `lsemStraightMem` from the encoded trip valuation and decoding the
return register reads exactly one `stepC` — `comToLprog_lsemMem` instantiated
at the loop-body context. -/

variable {invTys : Ctxt jasminDialect}

/-- The trip valuation `[acc, ofNat t, *invs]` — the `Ctxt.Valuation` of the
    loop-body context `accTy :: .reg 64 :: invTys` at trip index `t`, scalar
    accumulator `accTy = .reg w`. Named to fix the `HVector` type at
    elaboration (`⟦.reg w⟧ = BitVec w`). -/
def tripValMN {w : Nat} (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) :
    Ctxt.Valuation (d := jasminDialect) (JasminTy.reg w :: JasminTy.reg 64 :: invTys) :=
  .cons acc (.cons (BitVec.ofNat 64 t) invs)

/-- The linearizer-emitted typed body chain of a `forLoopNRt` loop body:
    `straightOpsMem` over the loop-body context (length `invTys.length + 2`). -/
def loopBodyChainMN {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) : List LinstrRM :=
  straightOpsMem (invTys.length + 2) update (invTys.length + 2)

/-- The return register of the emitted loop body: the register the chain
    computes the next accumulator into. -/
def loopBodyRetRegMN {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) : String :=
  comRetReg (invTys.length + 2) argName update (invTys.length + 2)

/-- **The per-iteration bridge.** One pass of the emitted body chain under
    `lsemStraightMem`, from the encoded trip valuation, succeeds and decodes at
    the return register to `JLoopBodyN.stepC update invs t acc` — the source
    loop's per-iteration denotation. This is `comToLprog_lsemMem`
    (`JasminLsemMem`, the straight-line export faithfulness) instantiated at
    the loop-body context; nothing is re-proved. -/
theorem memLoopBodyN_run_stepC {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) :
    ∃ st', lsemStraightMem (loopBodyChainMN update) (encodeM (tripValMN invs t acc))
        = some st'
      ∧ decodeM st' (loopBodyRetRegMN update) w
          = some (JLoopBodyN.stepC update invs t acc) := by
  have hkey := comToLprog_lsemMem (com := update) hupd rfl (tripValMN invs t acc)
  simpa only [loopBodyChainMN, loopBodyRetRegMN, JLoopBodyN.stepC, tripValMN,
    List.length_cons] using hkey

/-- **The machine body runner** — the `LstateM` analogue of
    `JasminLsemLoop.lsemBodyRunner`: run the emitted body chain on the encoded
    trip valuation, decode the return register. Returns `stepC` for every
    `ScalarMemN` body (`lsemBodyRunnerMemN_stepC`); `acc` otherwise (never
    taken). -/
def lsemBodyRunnerMemN {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) : BitVec w :=
  match lsemStraightMem (loopBodyChainMN update) (encodeM (tripValMN invs t acc)) with
  | some st' => (decodeM st' (loopBodyRetRegMN update) w).getD acc
  | none => acc

/-- **`StepAgrees`, memref version.** The machine body runner computes
    `JLoopBodyN.stepC` at every trip index and accumulator — the per-iteration
    edge, proved (not hypothesised) through the straight-line value bridge. -/
theorem lsemBodyRunnerMemN_stepC {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) :
    lsemBodyRunnerMemN update invs t acc = JLoopBodyN.stepC update invs t acc := by
  obtain ⟨st', hrun, hdec⟩ := memLoopBodyN_run_stepC update hupd invs t acc
  simp only [lsemBodyRunnerMemN, hrun, hdec, Option.getD_some]

/-! ## 2. The fold = the source denotation (`general_loopBody_lsem_faithful`,
memref) -/

/-- The `n`-fold of a machine body runner over the trip indices `0,…,n-1` —
    the memref analogue of `JForProgCT.loopRun`. -/
def loopRunMemN {w : Nat} (runner : Nat → BitVec w → BitVec w) (n : Nat)
    (init : BitVec w) : BitVec w :=
  (List.range n).foldl (fun acc t => runner t acc) init

/-- **General-loop-body faithfulness, memref (the `n`-fold denotation).** The
    `n`-fold of the machine body runner — each iteration running the emitted
    `straightOpsMem` chain on the encoded trip valuation and decoding the
    return register — equals `JLoopBodyN.denote ⟨n, update⟩ invs init`, the
    source loop's `n`-fold denotation. The `LstateM`/multi-binder analogue of
    `JasminLsemLoop.general_loopBody_lsem_faithful`. -/
theorem general_loopBodyN_lsemMem_faithful {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (invs : Ctxt.Valuation invTys) (n : Nat)
    (init : BitVec w) :
    loopRunMemN (lsemBodyRunnerMemN update invs) n init
      = JLoopBodyN.denote ⟨n, update⟩ invs init := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [JLoopBodyN.denote_succ, ← ih]
      simp only [loopRunMemN, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      exact lsemBodyRunnerMemN_stepC update hupd invs k _

/-! ## 3. `runBoundedLoopMem` decodes to `JLoopBodyN.denote`

The A1 machine-state fold `runBoundedLoopMem` threads the raw `LstateM` across
trips. The induction below lifts a **per-trip simulation** — each trip of the
emitted body computes one `stepC` under the `decodeM` correspondence at the
accumulator register — through the whole fold: the final state decodes to the
source loop's `m`-fold denotation. The per-trip hypothesis is exactly what §1
provides at the encoded trip states (and §7 validates concretely on a real
back-edge body). -/

/-- **The fold induction.** If the start state decodes the seed accumulator
    (`hinit`) and every trip `t < m` of the emitted body computes one
    `JLoopBodyN.stepC` under the `decodeM` correspondence (`hsim`), then the
    `m`-fold `runBoundedLoopMem` decodes at the accumulator register to
    `JLoopBodyN.denote ⟨m, update⟩ invs acc0` — the spec fold **is** the source
    denotation. Induction on `m` via `runBoundedLoopMem_succ_right` (peel the
    last trip) + `JLoopBodyN.denote_succ`, the back-edge `setLpc` absorbed by
    `decodeM_setLpc`. -/
theorem runBoundedLoopMem_decodes_denote {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys) (body : List LinstrRM) (accReg : String)
    (s0 : LstateM) (acc0 : BitVec w)
    (hinit : decodeM s0 accReg w = some acc0) :
    ∀ m : Nat,
      (∀ t, t < m → ∀ (bt : LstateM) (acct : BitVec w),
        runBoundedLoopMem body t s0 = some bt →
        decodeM bt accReg w = some acct →
        ∃ bt', lsemStraightMem body bt = some bt'
          ∧ decodeM bt' accReg w = some (JLoopBodyN.stepC update invs t acct)) →
      ∀ bfin : LstateM, runBoundedLoopMem body m s0 = some bfin →
        decodeM bfin accReg w = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
  intro m
  induction m with
  | zero =>
      intro _ bfin hrun
      rw [runBoundedLoopMem_zero] at hrun
      obtain rfl := Option.some.inj hrun
      exact hinit
  | succ k ih =>
      intro hsim bfin hrun
      rw [runBoundedLoopMem_succ_right] at hrun
      cases hbk : runBoundedLoopMem body k s0 with
      | none => rw [hbk] at hrun; simp at hrun
      | some bk =>
          rw [hbk, Option.bind_some] at hrun
          have hdk := ih (fun t ht => hsim t (Nat.lt_succ_of_lt ht)) bk hbk
          obtain ⟨bt', hbt', hdec'⟩ := hsim k (Nat.lt_succ_self k) bk _ hbk hdk
          rw [hbt', Option.map_some] at hrun
          obtain rfl := Option.some.inj hrun
          rw [JLoopBodyN.denote_succ, decodeM_setLpc]
          exact hdec'

/-! ## 4. The composed export theorems: machine run decodes to `ComL.denote`

Strengthening B3's `loopMem_export_faithful` from the spec fold to the source
denotation, and reading the result as the front node `ComL.forLoopNRt`'s
denotation. -/

/-- **A1 export faithfulness, tied to the source denotation.** Under the A1
    counter schedule (as in `loopMem_export_faithful`, never re-proved) plus
    the seed decode (`hinit`) and the per-trip simulation (`hsim`, §3), the
    emitted counter loop's machine run halts at a state whose accumulator
    register decodes to **`JLoopBodyN.denote ⟨m, update⟩ invs acc0`** — the
    source loop's `m`-fold denotation, not just the spec fold. -/
theorem loopMem_export_faithful_denote {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem body bprev = some blast)
    (hbfin : runBoundedLoopMem body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMem body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (accReg : String) (acc0 : BitVec w)
    (hinit : decodeM s.base accReg w = some acc0)
    (hsim : ∀ t, t < m → ∀ (bt : LstateM) (acct : BitVec w),
      runBoundedLoopMem body t s.base = some bt →
      decodeM bt accReg w = some acct →
      ∃ bt', lsemStraightMem body bt = some bt'
        ∧ decodeM bt' accReg w = some (JLoopBodyN.stepC update invs t acct)) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (body.length + 1)) s = some t
        ∧ decodeM t.base accReg w = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
  obtain ⟨t, ht, hdec⟩ := loopMem_export_faithful fn top nReg body hlopn s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt accReg w
  exact ⟨t, ht, hdec.trans (runBoundedLoopMem_decodes_denote update invs body accReg
    s.base acc0 hinit m hsim bfin hbfin)⟩

/-- **The source node's denotation is the loop fold.** The front-emitted
    `ComL.forLoopNRt update count init invs (.ret .here)` — the runtime-trip
    loop node returning its final accumulator — denotes exactly
    `JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩` over the looked-up
    invariants and seed. The equation closing §4's conclusion onto
    `ComL.denote`. -/
theorem comL_forLoopNRt_ret_denote {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.reg w))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ) :
    (ComL.forLoopNRt update count init invs (.ret .here)).denote V
      = JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
          (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-- **A1 export faithfulness, concluded at `ComL.denote`.** The composed
    "emitted bytes execute as the source denotation" statement for the counter
    loop: under the A1 schedule + the per-trip simulation, the machine run of
    the emitted loop decodes to the front node
    `ComL.forLoopNRt update count init invsV (.ret .here)`'s `ComL.denote` —
    the source semantics of the runtime-trip loop, at trip count
    `(count.lookup V).toNat`, seed `init.lookup V`, invariants
    `Expr.lookupArgs invsV V`. -/
theorem loopMem_export_faithful_comL {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hm : 0 < (count.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem body ((count.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem body bprev = some blast)
    (hbfin : runBoundedLoopMem body (count.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (count.lookup V).toNat → ∀ bi,
      runBoundedLoopMem body i s.base = some bi → condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (accReg : String)
    (hinit : decodeM s.base accReg w = some (initV.lookup V))
    (hsim : ∀ t, t < (count.lookup V).toNat → ∀ (bt : LstateM) (acct : BitVec w),
      runBoundedLoopMem body t s.base = some bt →
      decodeM bt accReg w = some acct →
      ∃ bt', lsemStraightMem body bt = some bt'
        ∧ decodeM bt' accReg w
            = some (JLoopBodyN.stepC update (Expr.lookupArgs invsV V) t acct)) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((count.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeM t.base accReg w
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  rw [comL_forLoopNRt_ret_denote]
  exact loopMem_export_faithful_denote update (Expr.lookupArgs invsV V) fn top nReg body
    hlopn s hfn hpc _ hm bprev blast bfin hprev hlast hbfin htaken hhalt accReg _
    hinit hsim

/-! ## 4b. The A2 fold: `runBoundedLoopMemC` decodes to `JLoopBodyN.denote`

The same fold induction over the **loop-with-call** body-fold
`lsemStraightMemC env body` (A2, the loop whose body `Lcall`s a linked owned
leaf): the per-trip simulation now runs the call-resolving body-fold, and §5's
called-leaf tie is what discharges the callee's contribution to it. -/

/-- **The A2 fold induction.** As `runBoundedLoopMem_decodes_denote`, over the
    call-resolving fold `runBoundedLoopMemC`: if each trip of the emitted
    loop-with-call body computes one `JLoopBodyN.stepC` under the `decodeM`
    correspondence, the `m`-fold decodes to the source loop's `m`-fold
    denotation. -/
theorem runBoundedLoopMemC_decodes_denote {w : Nat} (env : LeafEnvM)
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys) (body : List LinstrRM) (accReg : String)
    (s0 : LstateM) (acc0 : BitVec w)
    (hinit : decodeM s0 accReg w = some acc0) :
    ∀ m : Nat,
      (∀ t, t < m → ∀ (bt : LstateM) (acct : BitVec w),
        runBoundedLoopMemC env body t s0 = some bt →
        decodeM bt accReg w = some acct →
        ∃ bt', lsemStraightMemC env body bt = some bt'
          ∧ decodeM bt' accReg w = some (JLoopBodyN.stepC update invs t acct)) →
      ∀ bfin : LstateM, runBoundedLoopMemC env body m s0 = some bfin →
        decodeM bfin accReg w = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
  intro m
  induction m with
  | zero =>
      intro _ bfin hrun
      rw [runBoundedLoopMemC_zero] at hrun
      obtain rfl := Option.some.inj hrun
      exact hinit
  | succ k ih =>
      intro hsim bfin hrun
      rw [runBoundedLoopMemC_succ_right] at hrun
      cases hbk : runBoundedLoopMemC env body k s0 with
      | none => rw [hbk] at hrun; simp at hrun
      | some bk =>
          rw [hbk, Option.bind_some] at hrun
          have hdk := ih (fun t ht => hsim t (Nat.lt_succ_of_lt ht)) bk hbk
          obtain ⟨bt', hbt', hdec'⟩ := hsim k (Nat.lt_succ_self k) bk _ hbk hdk
          rw [hbt', Option.map_some] at hrun
          obtain rfl := Option.some.inj hrun
          rw [JLoopBodyN.denote_succ, decodeM_setLpc]
          exact hdec'

/-- **A2 export faithfulness, tied to the source denotation.** Under the A2
    schedule (as `loopCall_export_faithful`, never re-proved) plus the seed
    decode and the per-trip simulation, the emitted loop-with-call's machine
    run (`lsemFuelMemLC`) halts at a state whose accumulator register decodes
    to `JLoopBodyN.denote ⟨m, update⟩ invs acc0`. -/
theorem loopCall_export_faithful_denote {w : Nat} (env : LeafEnvM)
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top : LLabel) (nReg : String) (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (loopLinstrRM top nReg body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMemC env body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMemC env body bprev = some blast)
    (hbfin : runBoundedLoopMemC env body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMemC env body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (accReg : String) (acc0 : BitVec w)
    (hinit : decodeM s.base accReg w = some acc0)
    (hsim : ∀ t, t < m → ∀ (bt : LstateM) (acct : BitVec w),
      runBoundedLoopMemC env body t s.base = some bt →
      decodeM bt accReg w = some acct →
      ∃ bt', lsemStraightMemC env body bt = some bt'
        ∧ decodeM bt' accReg w = some (JLoopBodyN.stepC update invs t acct)) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (fuelCostC env body + 1)) s = some t
        ∧ decodeM t.base accReg w = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
  obtain ⟨t, ht, hdec⟩ := loopCall_export_faithful env fn top nReg body hok s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt accReg w
  exact ⟨t, ht, hdec.trans (runBoundedLoopMemC_decodes_denote env update invs body accReg
    s.base acc0 hinit m hsim bfin hbfin)⟩

/-! ## 5. The `Lcall` leaf tie: a called emitted leaf executes as `Com.denote`

`calleeRunDN_export_faithful` (B3) at depth `0` runs a straight-line callee:
`lsemStraightMemDN env 0 = lsemStraightMem` by definition. Instantiating the
callee body with the linearizer-emitted chain of a `ScalarMemN` leaf and
composing with the straight-line faithfulness gives: **a caller `Lcall`-ing the
emitted leaf runs (under the region-call machine model) to a halt state whose
result register decodes to the leaf's `Com.denote`** — the A2-flavoured
source tie, the callee's straight-line faithfulness threaded through the call
frame. -/

/-- The linearizer-emitted typed chain of a leaf `Com` (its whole context is
    the argument list). -/
def leafChainM {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) : List LinstrRM :=
  straightOpsMem Γ.length com Γ.length

/-- `opToLinstrR` always emits an `Lopn` — every arm of the linearizer's
    per-op image is a register/memory `Lopn` form (loads/stores included, via
    the SIB `LOADIDX`/`STOREIDX` images). -/
theorem opToLinstrR_isLopn (op : JasminOp) (dst : String) (srcs : List LOperand) :
    ∃ d o s, opToLinstrR op dst srcs = LinstrR.Lopn d o s := by
  -- name the image and walk the per-op `match`/`ite` control flow **in the
  -- hypothesis** (`split at` — the `∃`-binders block splitting in the goal)
  obtain ⟨i, hi⟩ : ∃ i, opToLinstrR op dst srcs = i := ⟨_, rfl⟩
  rw [hi]
  unfold opToLinstrR at hi
  cases op <;> repeat' first | (split at hi) | (dsimp only at hi)
  all_goals exact ⟨_, _, _, hi.symm⟩

/-- `shiftLinstr` always emits an `Lopn`. -/
theorem shiftLinstr_isLopn (mn : String) (w : Nat) (dst : String) (src : LOperand)
    (n : Nat) : ∃ d o s, shiftLinstr mn w dst src n = LinstrR.Lopn d o s :=
  ⟨_, _, _, rfl⟩

/-- **Every emitted chain element is an `Lopn`.** The `straightOpsMem` chain
    contains no control-transfer instruction — the depth-0 `NestBodyOK` (and
    A1's `IsLopn` side condition) holds for every linearizer-emitted body. -/
theorem straightOpsMem_isLopn {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (nArgs : Nat) :
    ∀ curDepth, ∀ i ∈ straightOpsMem nArgs com curDepth, IsLopn i := by
  induction com with
  | ret v => intro curDepth i hi; simp [straightOpsMem] at hi
  | var e body ih =>
      intro curDepth i hi
      rw [straightOpsMem] at hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · -- the head element: every image is an `Lopn`
        split
        · exact opToLinstrR_isLopn _ _ _
        · exact opToLinstrR_isLopn _ _ _
        · exact opToLinstrR_isLopn _ _ _
        · split
          · exact shiftLinstr_isLopn _ _ _ _ _
          · exact shiftLinstr_isLopn _ _ _ _ _
          · exact shiftLinstr_isLopn _ _ _ _ _
          · exact opToLinstrR_isLopn _ _ _
      · exact ih (curDepth + 1) i hi

/-- `setLpc 0` is the identity on the encoded start state (its pc is already
    `0`). -/
theorem encodeM_setLpc_zero {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    (encodeM V).setLpc 0 = encodeM V := by
  have h : (encodeM V).reg.lpc = 0 := by
    rw [show (encodeM V).reg = encodeN V from encodeArrAuxM_reg V _]
    exact JasminLsemGeneralFaithfulMC.encodeN_lpc V
  show { encodeM V with reg := { (encodeM V).reg with lpc := 0 } } = encodeM V
  rw [← h]

/-- **The called-leaf source tie.** For a `ScalarMemN` leaf `com` linked as the
    callee `sym` (its emitted chain + trailing `Lret`), entered from a caller
    frame that halts on return: the region-call machine model `lsemFuelMemLC`
    runs the whole call chain to a halt state whose result register decodes to
    **`com.denote V`** — the leaf's source denotation. Composes B3's
    `calleeRunDN_export_faithful` (depth `0`) with the straight-line
    faithfulness `comToLprog_lsemMem`; the depth-0 body side condition is
    discharged by `straightOpsMem_isLopn`. -/
theorem calleeLeaf_export_com_denote (env : LeafEnvM) (P : LprogM)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    (hcom : ScalarMemN com) {w : Nat} (hw : t = .reg w)
    (sym callerFn : String) (retPc : Nat) (hne : sym ≠ P.lfn)
    (hsym : env sym = some (leafChainM com ++ [(LinstrR.Lret, MemTag.reg none)]))
    (V : Ctxt.Valuation Γ) (rest : List (String × Nat))
    (hcallerHalt : ∀ b, lsemStraightMem (leafChainM com) (encodeM V) = some b →
      findInstrMemC env P
        { base := b.setLpc retPc, lfn := callerFn, rstack := rest } = none) :
    ∃ tSt : LstatePMC,
      lsemFuelMemLC env P (fuelCostDN env 0 (leafChainM com) + 1)
          { base := (encodeM V).setLpc 0, lfn := sym,
            rstack := (callerFn, retPc) :: rest } = some tSt
        ∧ decodeM tSt.base (comRetReg Γ.length argName com Γ.length) w
            = some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨b, hrun, hdec⟩ := comToLprog_lsemMem hcom hw V
  have hrunDN : lsemStraightMemDN env 0 (leafChainM com) ((encodeM V).setLpc 0)
      = some b := by
    rw [encodeM_setLpc_zero]
    simpa only [lsemStraightMemDN_zero, leafChainM] using hrun
  obtain ⟨tSt, ht, hdecT⟩ := calleeRunDN_export_faithful env P 0 sym callerFn retPc
    (leafChainM com)
    (fun i hi => straightOpsMem_isLopn com Γ.length Γ.length i hi)
    hne hsym (encodeM V) b rest hrunDN
    (hcallerHalt b hrun)
    (comRetReg Γ.length argName com Γ.length) w
  exact ⟨tSt, ht, hdecT.trans hdec⟩

/-! ## 6. The nested tie: the machine runners realise `nestedDenote`

The source side of `ComL.forLoopNRtNested` (the `fri_proof`/GGM shape): the
per-outer inner-trip count is recomputed by the emitted `innerCount` chain, and
each innermost step by the emitted `innerUpdate` chain — both instantiations of
the straight-line faithfulness, folded into the double fold
`JLoopBodyN.nestedDenote`. -/

/-- The inner-count valuation `[ofNat jd, *invs]` at outer index `jd`. -/
def innerCountValMN (invs : Ctxt.Valuation invTys) (jd : Nat) :
    Ctxt.Valuation (d := jasminDialect) (JasminTy.reg 64 :: invTys) :=
  .cons (BitVec.ofNat 64 jd) invs

/-- The nested trip valuation `[acc, ofNat t, ofNat jd, *invs]` at outer index
    `jd`, inner index `t`. -/
def nestedTripValMN {w : Nat} (invs : Ctxt.Valuation invTys) (jd t : Nat)
    (acc : BitVec w) :
    Ctxt.Valuation (d := jasminDialect)
      (JasminTy.reg w :: JasminTy.reg 64 :: JasminTy.reg 64 :: invTys) :=
  .cons acc (.cons (BitVec.ofNat 64 t) (.cons (BitVec.ofNat 64 jd) invs))

/-- The machine inner-trip counter: run the emitted `innerCount` chain on the
    encoded outer index, decode at 64 bits, read off the trip count. -/
def lsemInnerTripMemN
    (innerCount : Com jasminDialect (JasminTy.reg 64 :: invTys) (JasminTy.reg 64))
    (invs : Ctxt.Valuation invTys) (jd : Nat) : Nat :=
  match lsemStraightMem (straightOpsMem (invTys.length + 1) innerCount (invTys.length + 1))
      (encodeM (innerCountValMN invs jd)) with
  | some st' =>
      ((decodeM st' (comRetReg (invTys.length + 1) argName innerCount
        (invTys.length + 1)) 64).getD 0).toNat
  | none => 0

/-- **The inner-count bridge.** The machine inner-trip counter computes the
    source's per-outer-recomputed bound `JLoopBodyN.innerTripAtC` — the emitted
    `innerCount` chain's run decodes to `innerCount.denote [ofNat jd, *invs]`,
    whose `toNat` is the source trip count. -/
theorem lsemInnerTripMemN_eq_innerTripAtC
    (innerCount : Com jasminDialect (JasminTy.reg 64 :: invTys) (JasminTy.reg 64))
    (hc : ScalarMemN innerCount) (invs : Ctxt.Valuation invTys) (jd : Nat) :
    lsemInnerTripMemN innerCount invs jd = JLoopBodyN.innerTripAtC innerCount invs jd := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemMem hc rfl (innerCountValMN invs jd)
  have h1 : lsemStraightMem
      (straightOpsMem (invTys.length + 1) innerCount (invTys.length + 1))
      (encodeM (innerCountValMN invs jd)) = some st' := hrun
  have h2 : decodeM st' (comRetReg (invTys.length + 1) argName innerCount
      (invTys.length + 1)) 64 = some (innerCount.denote (innerCountValMN invs jd)) := hdec
  simp only [lsemInnerTripMemN, h1, h2, Option.getD_some]
  rfl

/-- The machine innermost-body runner: run the emitted `innerUpdate` chain on
    the encoded nested trip valuation, decode the return register. -/
def lsemNestedBodyRunnerMemN {w : Nat}
    (innerUpdate : Com jasminDialect
      (JasminTy.reg w :: JasminTy.reg 64 :: JasminTy.reg 64 :: invTys) (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys) (jd t : Nat) (acc : BitVec w) : BitVec w :=
  match lsemStraightMem
      (straightOpsMem (invTys.length + 3) innerUpdate (invTys.length + 3))
      (encodeM (nestedTripValMN invs jd t acc)) with
  | some st' =>
      (decodeM st' (comRetReg (invTys.length + 3) argName innerUpdate
        (invTys.length + 3)) w).getD acc
  | none => acc

/-- **The innermost-step bridge.** The machine innermost-body runner computes
    `JLoopBodyN.stepCNested` at every outer/inner index pair — the straight-line
    faithfulness instantiated at the nested body context. -/
theorem lsemNestedBodyRunnerMemN_stepCNested {w : Nat}
    (innerUpdate : Com jasminDialect
      (JasminTy.reg w :: JasminTy.reg 64 :: JasminTy.reg 64 :: invTys) (JasminTy.reg w))
    (hu : ScalarMemN innerUpdate) (invs : Ctxt.Valuation invTys) (jd t : Nat)
    (acc : BitVec w) :
    lsemNestedBodyRunnerMemN innerUpdate invs jd t acc
      = JLoopBodyN.stepCNested innerUpdate invs jd t acc := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemMem hu rfl (nestedTripValMN invs jd t acc)
  have h1 : lsemStraightMem
      (straightOpsMem (invTys.length + 3) innerUpdate (invTys.length + 3))
      (encodeM (nestedTripValMN invs jd t acc)) = some st' := hrun
  have h2 : decodeM st' (comRetReg (invTys.length + 3) argName innerUpdate
      (invTys.length + 3)) w = some (innerUpdate.denote (nestedTripValMN invs jd t acc)) := hdec
  simp only [lsemNestedBodyRunnerMemN, h1, h2, Option.getD_some]
  rfl

/-- **The nested fold = `nestedDenote`.** The double fold of the machine
    runners — outer trips `0,…,outerN-1`, each recomputing the inner bound via
    the emitted `innerCount` chain and folding the emitted `innerUpdate` chain
    over the inner trips — equals `JLoopBodyN.nestedDenote`, the source
    semantics of `ComL.forLoopNRtNested`. The source-side second half of the
    nested tie (the inline-nested machine fold is the B5 residual; the
    nested-call route is §5). -/
theorem general_nestedLoopBodyN_lsemMem_faithful {w : Nat}
    (innerCount : Com jasminDialect (JasminTy.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect
      (JasminTy.reg w :: JasminTy.reg 64 :: JasminTy.reg 64 :: invTys) (JasminTy.reg w))
    (hc : ScalarMemN innerCount) (hu : ScalarMemN innerUpdate)
    (invs : Ctxt.Valuation invTys) (outerN : Nat) (init : BitVec w) :
    (List.range outerN).foldl
        (fun acc jd =>
          (List.range (lsemInnerTripMemN innerCount invs jd)).foldl
            (fun acc2 t => lsemNestedBodyRunnerMemN innerUpdate invs jd t acc2) acc)
        init
      = JLoopBodyN.nestedDenote innerCount innerUpdate outerN invs init := by
  unfold JLoopBodyN.nestedDenote
  congr 1
  funext acc jd
  rw [lsemInnerTripMemN_eq_innerTripAtC innerCount hc invs jd]
  congr 1
  funext acc2 t
  exact lsemNestedBodyRunnerMemN_stepCNested innerUpdate hu invs jd t acc2

/-- **The nested source node's denotation is the double fold.** The
    front-emitted `ComL.forLoopNRtNested … (.ret .here)` denotes exactly
    `JLoopBodyN.nestedDenote` over the looked-up outer count, invariants and
    seed. -/
theorem comL_forLoopNRtNested_ret_denote {Γ : Ctxt jasminDialect} {w : Nat}
    (innerCount : Com jasminDialect (JasminTy.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect
      (JasminTy.reg w :: JasminTy.reg 64 :: JasminTy.reg 64 :: invTys) (JasminTy.reg w))
    (outerCount : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.reg w))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ) :
    (ComL.forLoopNRtNested innerCount innerUpdate outerCount init invs
        (.ret .here)).denote V
      = JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
          (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-! ## 7. Validation: a real emitted back-edge decodes to `JLoopBodyN.denote`

A concrete 2-trip counter loop whose per-trip body is the **actual linearizer
chain** `loopBodyChainMN` of the source body `acc := acc + acc` (a `ScalarMemN`
`Com`), followed by the accumulator writeback `MOV a1 ← r2` and the counter
decrement `SUB n ← n, 1`. Run by the labeled machine model `lsemFuelMemL` from
the encoded seed `acc = 5`, the loop follows the back-edge twice and the
accumulator register decodes to `JLoopBodyN.denote ⟨2, wUpd⟩ .nil 5 = 20` — the
composed A1 source tie realised end-to-end on a real back-edge. (The source
body ignores the loop index, so the index register needs no increment here;
`htaken`/`hsim`-style schedules are exercised implicitly by the run.) -/

/-- The witness source body: `acc := acc + acc` over the loop-body context
    `[.reg 64 (acc), .reg 64 (idx)]` (invariants `[]`, index unused). -/
def wUpd : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (⟨JasminOp.regArith .add 64, rfl, .cons .here (.cons .here .nil)⟩ :
      Expr jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (JasminTy.reg 64))
    (.ret .here)

/-- The witness body is in the stack-memory fragment. -/
theorem wUpd_scalarMemN : ScalarMemN wUpd :=
  .var (bop := .add) rfl (.cons .here (.cons .here .nil)) (.ret .here)

/-- The witness emitted loop body: the linearizer chain of `wUpd` (computes
    `r2 := a1 + a1`), the accumulator writeback `ADD a1 ← r2, #0` (a register
    move via the additive identity — the wire `MOV` is immediate-only in this
    machine model), the counter decrement `SUB n ← n, 1`. -/
def wBody : List LinstrRM :=
  loopBodyChainMN (invTys := []) wUpd ++
    [ (LinstrR.Lopn [.reg "a1"] "ADD:64" [.reg "r2", .imm 0], MemTag.reg none)
    , (LinstrR.Lopn [.reg "n"] "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

/-- The witness loop program: `wBody` wrapped in the back-edge on counter `"n"`. -/
def wProg : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" wBody)

/-- The witness start state: the encoded trip-0 valuation (`acc = 5` at `a1`,
    index `0` at `a0`) with the public counter `n = 2`. -/
def wStart : LstatePM :=
  { base := (encodeM (tripValMN (invTys := []) .nil 0 (5#64))).setReg "n" (2#64)
    lfn := "f" }

/-- **Validate (the composed tie, end-to-end).** The machine run of the emitted
    2-trip loop decodes the accumulator register to the **source denotation**
    `JLoopBodyN.denote ⟨2, wUpd⟩ .nil 5#64` — the real back-edge executes the
    source loop's fold. -/
example :
    (lsemFuelMemL wProg 20 wStart).map (fun t => decodeM t.base "a1" 64)
      = some (some (JLoopBodyN.denote ⟨2, wUpd⟩ .nil (5#64))) := by
  native_decide

/-- **Validate (the source value).** The source denotation itself is `20`
    (`5 → 10 → 20`): the decoded machine result above is the honest doubling
    fold, not a stale register. -/
example : (JLoopBodyN.denote ⟨2, wUpd⟩ .nil (5#64) : BitVec 64) = 20#64 := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
