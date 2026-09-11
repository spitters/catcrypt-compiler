/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.CompilerSecurity.JasminSemTracedDeterminism
public import CatCrypt.Crypto.CompilerSecurity.UnifiedTrace


@[expose] public section
set_option autoImplicit false

/-!
# RustExecTraced: source-side trace-emitting big-step semantics

Mirror of `JasminSemTraced` for the source-side `RustExec` relation.
Each `RustExec` rule has a trace-emitting counterpart that records:
* one tag per non-trivial constructor (matching the events that
  `toJasminCmd` would emit at the Jasmin level — see
  `UnifiedTrace.LowCT.toJasminLeakTrace` for the static version),
* dynamic branch decisions for `RIfNz`/`RWhileNz`/`RFor` (encoded
  as `branchTag true`/`branchTag false`).

The trace alphabet (events) is the *same* as `JasminSemTraced` so the
two semantics are commensurable: a complete RHP-2 statement compares
RustExec's source trace against jasminSem's target trace via a
correspondence lemma (the natural next theorem after this file).

## Forgetting and promotion

* `RustExecTraced.toExec` — every traced derivation projects to
  the original `RustExec`.
* `RustExec.toTraced` — every `RustExec` derivation can be promoted
  to a `RustExecTraced` derivation by recording the dynamic events.

Both directions axiom-clean.
-/

namespace CatCrypt.Crypto.SecureCompilation.RustExecTraced

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.JasminSemTraced

/-- Trace-emitting big-step semantics for `LowCT`. Each rule mirrors
    one of `RustExec`'s with the trace contribution added. Trace events
    are tagged with the *Jasmin-side* shape (`"Cassgn"`, `"Ccall"`,
    `"Cif"`, etc.) so dynamic source traces are commensurable with
    dynamic target traces from `jasminSemTraced`. -/
inductive RustExecTraced (N : Nat) (leafSpec : LeafSpec) :
    LowCT → RustState → LeakTrace → RustState → Prop where
  | skip : ∀ rs, RustExecTraced N leafSpec .RSkip rs [] rs
  | seq : ∀ c1 c2 rs t1 r1 t2 rs',
      RustExecTraced N leafSpec c1 rs t1 r1 →
      RustExecTraced N leafSpec c2 r1 t2 rs' →
      RustExecTraced N leafSpec (.RSeq c1 c2) rs (t1 ++ t2) rs'
  | letZero : ∀ x t body rs t_body rs',
      RustExecTraced N leafSpec body
        (rsSetTower rs x ⟨t, default⟩) t_body rs' →
      RustExecTraced N leafSpec (.RLetZero x t body) rs
        (LeakEvent.pureOp "Cassgn" :: t_body) rs'
  | letU64Zero : ∀ x body rs t_body rs',
      RustExecTraced N leafSpec body (rsSetScalar rs x 0) t_body rs' →
      RustExecTraced N leafSpec (.RLetU64Zero x body) rs
        (LeakEvent.pureOp "Cassgn" :: t_body) rs'
  | scalarSet : ∀ x v rs,
      RustExecTraced N leafSpec (.RScalarSet x v) rs
        [LeakEvent.pureOp "Cassgn"] (rsSetScalar rs x v)
  | ifTrue : ∀ e ct cf rs t_branch rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExecTraced N leafSpec ct rs t_branch rs' →
      RustExecTraced N leafSpec (.RIfNz e ct cf) rs
        (LeakEvent.pureOp "Cif" :: branchTag true :: t_branch) rs'
  | ifFalse : ∀ e ct cf rs t_branch rs',
      rs.rsScalar e = 0 →
      RustExecTraced N leafSpec cf rs t_branch rs' →
      RustExecTraced N leafSpec (.RIfNz e ct cf) rs
        (LeakEvent.pureOp "Cif" :: branchTag false :: t_branch) rs'
  | whileFalse : ∀ e body rs,
      rs.rsScalar e = 0 →
      RustExecTraced N leafSpec (.RWhileNz e body) rs
        [LeakEvent.pureOp "Cwhile", branchTag false] rs
  | whileTrue : ∀ e body rs t_body r1 t_rest rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExecTraced N leafSpec body rs t_body r1 →
      RustExecTraced N leafSpec (.RWhileNz e body) r1 t_rest rs' →
      RustExecTraced N leafSpec (.RWhileNz e body) rs
        (LeakEvent.pureOp "Cwhile" :: branchTag true :: t_body ++ t_rest) rs'
  | forZero : ∀ x body rs,
      RustExecTraced N leafSpec (.RFor x 0 body) rs [] rs
  | forSucc : ∀ x n body rs t1 r1 t2 rs',
      RustExecTraced N leafSpec (.RFor x n body) rs t1 r1 →
      RustExecTraced N leafSpec body (rsSetScalar r1 x n) t2 rs' →
      -- Each iteration emits one `Cassgn` event for the loop-counter write,
      -- matching the static-unrolling lowering's per-iteration `scalarSet`.
      RustExecTraced N leafSpec (.RFor x (n+1) body) rs
        (t1 ++ LeakEvent.pureOp "Cassgn" :: t2) rs'
  -- Stage 1a (2026-07-01): runtime-bound loop delegates to the `RFor` traced
  -- derivation at the entry-state trip count `bound.evalState rs`.
  | forRuntime : ∀ x bound body rs t rs',
      RustExecTraced N leafSpec (.RFor x (bound.evalState rs) body) rs t rs' →
      RustExecTraced N leafSpec (.RForRuntime x bound body) rs t rs'
  | call : ∀ f dest args rs oldDestV argList,
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      -- Per-arg type-recovery (Option A): args[i].locDst matches the
      -- stored Sigma type at args[i].locVar. Required for determinism.
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExecTraced N leafSpec (.RCall f dest args) rs
        [LeakEvent.pureOp "Ccall"]
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  | cloneCall : ∀ cloneVar cloneTy oldDest innerF dest args
                  rs rsClone t_call rs',
      rsClone = rsSetTower rs cloneVar
                  (rs.rsTower oldDest.locVar |>.getD ⟨cloneTy, default⟩) →
      RustExecTraced N leafSpec (.RCall innerF dest args) rsClone t_call rs' →
      RustExecTraced N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
        rs (LeakEvent.pureOp "Copn" :: t_call) rs'
  /-- 2-output cswap-shape leaf.  Trace = two `Ccall` events from the
      sub-derivations on `RCall f dest1 args` then `RCall f dest2 args`.
      Mirrors the lowering in `toJasminCmd` (two sequential Ccalls). -/
  | callSwap : ∀ f dest1 dest2 args rs t1 rs1 t2 rs',
      RustExecTraced N leafSpec (.RCall f dest1 args) rs t1 rs1 →
      RustExecTraced N leafSpec (.RCall f dest2 args) rs1 t2 rs' →
      RustExecTraced N leafSpec (.RCallSwap f dest1 dest2 args) rs
        (t1 ++ t2) rs'
  | limbStore : ∀ loc idx v rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExecTraced N leafSpec (.RLimbStore loc idx v) rs
        [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  -- Phase R5 (2026-06-01): traced runtime-valued limb store. Same single
  -- `Copn` leak event as `limbStore`; the stored word is the tower-aware
  -- `e.evalState rs` truncated (#356), mirroring `RustExec.limbStoreExpr`.
  | limbStoreExpr : ∀ loc idx e rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExecTraced N leafSpec (.RLimbStoreExpr loc idx e) rs
        [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs loc
          (leafSpec.limbStore loc oldDestV idx (BitVec.ofNat 64 (e.evalState rs))))
  -- Phase F/G/H/L/M (2026-05-03): traced versions of the new constructors.
  -- Trace events match the structural `LowCT.toJasminLeakTrace` shape.
  /-- N-output leaf call, mirroring `RustExec.callN`: the argument values are
      read once from the pre-state, then each destination is written in turn,
      destination `i` receiving `leafSpec.call (callNLeafName f i)` on them.
      Lowers to a single Jasmin `Ccall`, so the recorded trace is
      `[pureOp "Ccall"]`. -/
  | callN : ∀ f dests args rs argList,
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      RustExecTraced N leafSpec (.RCallN f dests args) rs
        [LeakEvent.pureOp "Ccall"]
        (callNUpdate leafSpec f (args.map (·.locDst)) argList 0 dests rs)
  /-- Phase E2 (2026-05-29): traced destination-threaded leaf call.
      Single output, mirroring `RustExec.callDstThreaded`: reads `dst`'s
      old value, builds the argument list from `dst :: args`, and writes
      the single `leafSpec.call` result back to `dst`.  Lowers to a single
      Jasmin `Ccall`, so the recorded trace is `[pureOp "Ccall"]`. -/
  | callDstThreaded : ∀ f dst args rs oldDestV argList,
      locatedLookup rs dst = some oldDestV →
      argList = (dst :: args).filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ dst :: args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExecTraced N leafSpec (.RCallDstThreaded f dst args) rs
        [LeakEvent.pureOp "Ccall"]
        (locatedUpdate rs dst
          (leafSpec.call f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList))
  | selectFalse : ∀ dst sel src0 src1 rs (h : src0.locDst = dst.locDst) srcV,
      rs.rsScalar sel = 0 →
      locatedLookup rs src0 = some srcV →
      RustExecTraced N leafSpec (.RSelect dst sel src0 src1) rs
        [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs dst (h ▸ srcV))
  | selectTrue : ∀ dst sel src0 src1 rs (h : src1.locDst = dst.locDst) v srcV,
      rs.rsScalar sel = v → v ≠ 0 →
      locatedLookup rs src1 = some srcV →
      RustExecTraced N leafSpec (.RSelect dst sel src0 src1) rs
        [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs dst (h ▸ srcV))
  | assert : ∀ label rs,
      RustExecTraced N leafSpec (.RAssert label) rs [] rs
  | block : ∀ body rs t_body rs',
      RustExecTraced N leafSpec body rs t_body rs' →
      RustExecTraced N leafSpec (.RBlock body) rs t_body rs'
  -- Phase I.1 (2026-05-04): tuple load with real semantics.
  -- Reads dst's old value, looks up src, applies the leafSpec
  -- oracle.  Emits a single `Copn` leak event matching the
  -- byte-offset lowering shape used by `toJasminCmd`.
  | tupleLoad : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExecTraced N leafSpec (.RTupleLoad dst src idx) rs
        [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs dst (leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  -- Phase J (wave 6, 4.29): array store / array load / scalar-set-expr.
  -- Trace shape mirrors `LowCT.toJasminLeakTrace` for these
  -- ops, where each emits a single `Copn` (or `Cassgn`) event.
  | arrStore : ∀ arr idxVar src rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExecTraced N leafSpec (.RArrStore arr idxVar src) rs
        [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  | arrLoad : ∀ dst src idxVar rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExecTraced N leafSpec (.RArrLoad dst src idxVar) rs
        [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  | scalarSetExpr : ∀ x e rs,
      RustExecTraced N leafSpec (.RScalarSetExpr x e) rs
        [LeakEvent.pureOp "Cassgn"]
        (rsSetScalar rs x (e.eval rs.rsScalar))
  -- Phase DD (2026-05-28): literal-index array store/load.  Mirror of
  -- `RustExec.arrStoreLit`/`arrLoadLit` with the static-leak tag added.
  -- `toJasminCmd` emits a single `Cassgn` (a literal-index `Laset`/`Pget`)
  -- for each, so the recorded trace is `[pureOp "Cassgn"]`, matching
  -- `LowCT.toJasminLeakTrace` for the `RArrStoreLit`/`RArrLoadLit` arms.
  | arrStoreLit : ∀ arr idx src rs oldV srcV,
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExecTraced N leafSpec (.RArrStoreLit arr idx src) rs
        [LeakEvent.pureOp "Cassgn"]
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  | arrLoadLit : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExecTraced N leafSpec (.RArrLoadLit dst src idx) rs
        [LeakEvent.pureOp "Cassgn"]
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))

/-! ## Forgetting -/

/-- Forgetting the trace: every `RustExecTraced` derivation projects
    to a `RustExec` derivation (modulo the recorded trace). -/
theorem RustExecTraced.toExec {N : Nat} {leafSpec : LeafSpec}
    {c : LowCT} {rs rs' : RustState} {t : LeakTrace}
    (h : RustExecTraced N leafSpec c rs t rs') :
    RustExec N leafSpec c rs rs' := by
  induction h with
  | skip rs0 => exact RustExec.skip rs0
  | seq c1 c2 rs0 _t1 r1 _t2 rs0' _h1 _h2 ih1 ih2 =>
    exact RustExec.seq c1 c2 rs0 r1 rs0' ih1 ih2
  | letZero x t' body rs0 _t_body rs0' _h ih =>
    exact RustExec.letZero x t' body rs0 rs0' ih
  | letU64Zero x body rs0 _t_body rs0' _h ih =>
    exact RustExec.letU64Zero x body rs0 rs0' ih
  | scalarSet x v rs0 => exact RustExec.scalarSet x v rs0
  | ifTrue e ct cf rs0 _t_branch rs0' v hv hne _h ih =>
    exact RustExec.ifTrue e ct cf rs0 rs0' v hv hne ih
  | ifFalse e ct cf rs0 _t_branch rs0' h0 _h ih =>
    exact RustExec.ifFalse e ct cf rs0 rs0' h0 ih
  | whileFalse e body rs0 h0 =>
    exact RustExec.whileFalse e body rs0 h0
  | whileTrue e body rs0 _t_body r1 _t_rest rs0' v hv hne _hb _hw ihb ihw =>
    exact RustExec.whileTrue e body rs0 r1 rs0' v hv hne ihb ihw
  | forZero x body rs0 => exact RustExec.forZero x body rs0
  | forSucc x n body rs0 _t1 r1 _t2 rs0' _h1 _h2 ih1 ih2 =>
    exact RustExec.forSucc x n body rs0 r1 rs0' ih1 ih2
  | forRuntime x bound body rs0 _t rs0' _h ih =>
    exact RustExec.forRuntime x bound body rs0 rs0' ih
  | call f dest args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact RustExec.call f dest args rs0 oldDestV argList hLk hArgs hArgsTyped
  | callDstThreaded f dst args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact RustExec.callDstThreaded f dst args rs0 oldDestV argList hLk hArgs hArgsTyped
  | cloneCall cv ct oldDest innerF dest args rs0 rsClone _t_call rs0'
                hClone _hCall ihCall =>
    exact RustExec.cloneCall cv ct oldDest innerF dest args
            rs0 rsClone rs0' hClone ihCall
  | callSwap f dest1 dest2 args rs0 _t1 rs1 _t2 rs0' _h1 _h2 ih1 ih2 =>
    exact RustExec.callSwap f dest1 dest2 args rs0 rs1 rs0' ih1 ih2
  | limbStore loc idx v rs0 oldDestV hLk =>
    exact RustExec.limbStore loc idx v rs0 oldDestV hLk
  | limbStoreExpr loc idx e rs0 oldDestV hLk =>
    exact RustExec.limbStoreExpr loc idx e rs0 oldDestV hLk
  -- Phase F/G/H/L/M (2026-05-03): forget trace, project to bare RustExec.
  | callN f dests args rs0 argList hArgList hArgs hDests =>
    exact RustExec.callN f dests args rs0 argList hArgList hArgs hDests
  | selectFalse dst sel src0 src1 rs0 h srcV hSel hLk =>
    exact RustExec.selectFalse dst sel src0 src1 rs0 h srcV hSel hLk
  | selectTrue dst sel src0 src1 rs0 h v srcV hSel hne hLk =>
    exact RustExec.selectTrue dst sel src0 src1 rs0 h v srcV hSel hne hLk
  | assert label rs0 =>
    exact RustExec.assert label rs0
  | block body rs0 _t_body rs0' _h ih =>
    exact RustExec.block body rs0 rs0' ih
  -- Phase I.1:
  | tupleLoad dst src idx rs0 oldV srcV hLkDst hLkSrc =>
    exact RustExec.tupleLoad dst src idx rs0 oldV srcV hLkDst hLkSrc
  -- Phase J (wave 6, 4.29):
  | arrStore arr idxVar src rs0 idx oldV srcV hIdx hLkArr hLkSrc =>
    exact RustExec.arrStore arr idxVar src rs0 idx oldV srcV hIdx hLkArr hLkSrc
  | arrLoad dst src idxVar rs0 idx oldV srcV hIdx hLkDst hLkSrc =>
    exact RustExec.arrLoad dst src idxVar rs0 idx oldV srcV hIdx hLkDst hLkSrc
  | scalarSetExpr x e rs0 =>
    exact RustExec.scalarSetExpr x e rs0
  -- Phase DD (2026-05-28): literal-index array store/load forget to the
  -- matching `RustExec` rule.
  | arrStoreLit arr idx src rs0 oldV srcV hLkArr hLkSrc =>
    exact RustExec.arrStoreLit arr idx src rs0 oldV srcV hLkArr hLkSrc
  | arrLoadLit dst src idx rs0 oldV srcV hLkDst hLkSrc =>
    exact RustExec.arrLoadLit dst src idx rs0 oldV srcV hLkDst hLkSrc

/-! ## Promotion -/

/-- Promotion: every `RustExec` derivation has a corresponding
    `RustExecTraced` derivation with some trace. -/
theorem RustExec.toTraced {N : Nat} {leafSpec : LeafSpec}
    {c : LowCT} {rs rs' : RustState}
    (h : RustExec N leafSpec c rs rs') :
    ∃ t : LeakTrace, RustExecTraced N leafSpec c rs t rs' := by
  induction h with
  | skip rs0 => exact ⟨[], RustExecTraced.skip rs0⟩
  | seq c1 c2 rs0 r1 rs0' _h1 _h2 ih1 ih2 =>
    obtain ⟨t1, h1'⟩ := ih1
    obtain ⟨t2, h2'⟩ := ih2
    exact ⟨t1 ++ t2, RustExecTraced.seq c1 c2 rs0 t1 r1 t2 rs0' h1' h2'⟩
  | letZero x t' body rs0 rs0' _h ih =>
    obtain ⟨t_body, h'⟩ := ih
    exact ⟨_, RustExecTraced.letZero x t' body rs0 t_body rs0' h'⟩
  | letU64Zero x body rs0 rs0' _h ih =>
    obtain ⟨t_body, h'⟩ := ih
    exact ⟨_, RustExecTraced.letU64Zero x body rs0 t_body rs0' h'⟩
  | scalarSet x v rs0 => exact ⟨_, RustExecTraced.scalarSet x v rs0⟩
  | ifTrue e ct cf rs0 rs0' v hv hne _h ih =>
    obtain ⟨t_branch, h'⟩ := ih
    exact ⟨_, RustExecTraced.ifTrue e ct cf rs0 t_branch rs0' v hv hne h'⟩
  | ifFalse e ct cf rs0 rs0' h0 _h ih =>
    obtain ⟨t_branch, h'⟩ := ih
    exact ⟨_, RustExecTraced.ifFalse e ct cf rs0 t_branch rs0' h0 h'⟩
  | whileFalse e body rs0 h0 =>
    exact ⟨_, RustExecTraced.whileFalse e body rs0 h0⟩
  | whileTrue e body rs0 r1 rs0' v hv hne _hb _hw ihb ihw =>
    obtain ⟨t_body, hb'⟩ := ihb
    obtain ⟨t_rest, hw'⟩ := ihw
    exact ⟨_, RustExecTraced.whileTrue e body rs0 t_body r1 t_rest rs0'
                v hv hne hb' hw'⟩
  | forZero x body rs0 => exact ⟨_, RustExecTraced.forZero x body rs0⟩
  | forSucc x n body rs0 r1 rs0' _h1 _h2 ih1 ih2 =>
    obtain ⟨t1, h1'⟩ := ih1
    obtain ⟨t2, h2'⟩ := ih2
    exact ⟨_, RustExecTraced.forSucc x n body rs0 t1 r1 t2 rs0' h1' h2'⟩
  | forRuntime x bound body rs0 rs0' _h ih =>
    obtain ⟨t, h'⟩ := ih
    exact ⟨_, RustExecTraced.forRuntime x bound body rs0 t rs0' h'⟩
  | call f dest args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact ⟨_, RustExecTraced.call f dest args rs0 oldDestV argList hLk hArgs
                                    hArgsTyped⟩
  | callDstThreaded f dst args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact ⟨_, RustExecTraced.callDstThreaded f dst args rs0 oldDestV argList
                                    hLk hArgs hArgsTyped⟩
  | cloneCall cv ct oldDest innerF dest args
                rs0 rsClone rs0' hClone _hCall ihCall =>
    obtain ⟨t_call, hCall'⟩ := ihCall
    exact ⟨_, RustExecTraced.cloneCall cv ct oldDest innerF dest args
                rs0 rsClone t_call rs0' hClone hCall'⟩
  | callSwap f dest1 dest2 args rs0 rs1 rs0' _h1 _h2 ih1 ih2 =>
    obtain ⟨t1, h1'⟩ := ih1
    obtain ⟨t2, h2'⟩ := ih2
    exact ⟨_, RustExecTraced.callSwap f dest1 dest2 args rs0 t1 rs1 t2 rs0' h1' h2'⟩
  | limbStore loc idx v rs0 oldDestV hLk =>
    exact ⟨_, RustExecTraced.limbStore loc idx v rs0 oldDestV hLk⟩
  | limbStoreExpr loc idx e rs0 oldDestV hLk =>
    exact ⟨_, RustExecTraced.limbStoreExpr loc idx e rs0 oldDestV hLk⟩
  -- Phase F/G/H/L/M (2026-05-03): promote new RustExec cases to traced.
  | callN f dests args rs0 argList hArgList hArgs hDests =>
    exact ⟨_, RustExecTraced.callN f dests args rs0 argList hArgList hArgs hDests⟩
  | selectFalse dst sel src0 src1 rs0 h srcV hSel hLk =>
    exact ⟨_, RustExecTraced.selectFalse dst sel src0 src1 rs0 h srcV hSel hLk⟩
  | selectTrue dst sel src0 src1 rs0 h v srcV hSel hne hLk =>
    exact ⟨_, RustExecTraced.selectTrue dst sel src0 src1 rs0 h v srcV hSel hne hLk⟩
  | assert label rs0 =>
    exact ⟨_, RustExecTraced.assert label rs0⟩
  | block body rs0 rs0' _h ih =>
    obtain ⟨t_body, h'⟩ := ih
    exact ⟨_, RustExecTraced.block body rs0 t_body rs0' h'⟩
  -- Phase I: tuple load is identity-stub semantics; promote
  -- to traced via `RustExecTraced.tupleLoad`.
  | tupleLoad dst src idx rs0 oldV srcV hLkDst hLkSrc =>
    exact ⟨_, RustExecTraced.tupleLoad dst src idx rs0 oldV srcV hLkDst hLkSrc⟩
  -- Phase J (wave 6, 4.29):
  | arrStore arr idxVar src rs0 idx oldV srcV hIdx hLkArr hLkSrc =>
    exact ⟨_, RustExecTraced.arrStore arr idxVar src rs0 idx oldV srcV
                hIdx hLkArr hLkSrc⟩
  | arrLoad dst src idxVar rs0 idx oldV srcV hIdx hLkDst hLkSrc =>
    exact ⟨_, RustExecTraced.arrLoad dst src idxVar rs0 idx oldV srcV
                hIdx hLkDst hLkSrc⟩
  | scalarSetExpr x e rs0 =>
    exact ⟨_, RustExecTraced.scalarSetExpr x e rs0⟩
  -- Phase DD (2026-05-28): promote literal-index array store/load.
  | arrStoreLit arr idx src rs0 oldV srcV hLkArr hLkSrc =>
    exact ⟨_, RustExecTraced.arrStoreLit arr idx src rs0 oldV srcV hLkArr hLkSrc⟩
  | arrLoadLit dst src idx rs0 oldV srcV hLkDst hLkSrc =>
    exact ⟨_, RustExecTraced.arrLoadLit dst src idx rs0 oldV srcV hLkDst hLkSrc⟩

/-! ## Static-dynamic correspondence (straight-line subset)

For LowCTs with no `RIfNz`/`RWhileNz`/`RFor` (i.e., no dynamic branch
decisions), the dynamic trace from `RustExecTraced` equals the static
trace from `LowCT.toJasminLeakTrace`. This pins down the relationship
between the two trace producers on the well-behaved subset that the
verified-middle straight-line pipeline emits. -/

open CatCrypt.Crypto.SecureCompilation.UnifiedTrace
open CatCrypt.Crypto.SecureCompilation.UnifiedTrace.JasminSem (LowCT.toJasminLeakTrace)

/-- Predicate: this LowCT has no top-level branching constructor.
    `RCloneCall`'s inner call is opaque from the AST perspective so it
    counts as straight-line; `RWhileNz`/`RFor` bodies are *not* recursed
    into because if they execute, the dynamic trace will differ from the
    static (the static collapses both to a single tag). -/
def LowCT.straightLine : LowCT → Bool
  | .RSkip                   => true
  | .RSeq c1 c2              => LowCT.straightLine c1 && LowCT.straightLine c2
  | .RLetZero _ _ body       => LowCT.straightLine body
  | .RLetU64Zero _ body      => LowCT.straightLine body
  | .RScalarSet _ _          => true
  | .RCall _ _ _             => true
  | .RCloneCall _ _ _ _ _ _  => true
  | .RIfNz _ _ _             => false
  | .RWhileNz _ _            => false
  | .RFor _ _ _              => false
  | .RForRuntime _ _ _       => false
  | .RLimbStore _ _ _        => true
  | .RLimbStoreExpr _ _ _    => true
  -- Phase F/G/H/L/M: the new constructors are straight-line.
  | .RCallSwap _ _ _ _       => true
  | .RCallN _ _ _            => true
  | .RSelect _ _ _ _         => true
  | .RAssert _               => true
  | .RBlock body             => LowCT.straightLine body
  -- A helper definition is outside the straight-line subset: the static
  -- `toJasminLeakTrace` inlines the body's trace ahead of the
  -- continuation's.
  | .RFnDef _ _ _ _ _        => false
  | .RFnCall _ _ _           => true
  -- Phase I: tuple load has a static-dynamic trace mismatch
  -- (static `LowCT.toJasminLeakTrace` returns `[]`, dynamic
  -- `RustExecTraced.tupleLoad` emits `[Copn]`).
  -- Gate `false` so it is excluded from the straight-line subset
  -- until the static and dynamic traces are reconciled.
  | .RTupleLoad _ _ _        => false
  -- Phase J (wave 6, 4.29): array / scalar-expr constructors added
  -- to LowCT. Gate `false` until their static and dynamic traces are
  -- wired and reconciled — straight-line coverage is unaffected because
  -- callers exclude these on entry.
  | .RArrStore _ _ _         => false
  | .RArrLoad _ _ _          => false
  | .RScalarSetExpr _ _      => false
  -- Phase DD (2026-05-28): literal-index array store/load.  Static trace
  -- (`toJasminLeakTrace = [Cassgn]`) and dynamic trace
  -- (`RustExecTraced.arrStoreLit`/`arrLoadLit = [Cassgn]`) agree, so these are
  -- in the straight-line subset.
  | .RArrStoreLit _ _ _      => true
  | .RArrLoadLit _ _ _       => true
  -- Phase E2 (2026-05-29): dst-threaded leaf call.  No source-dynamic
  -- `RustExec` rule exists yet (it is only a `LowCT`/`toJasminCmd` arm), so
  -- it never appears in a `RustExecTraced` derivation; classified as
  -- straight-line (call-like) for the `LowCT`-level Bool, with the dynamic
  -- correspondence vacuous.
  | .RCallDstThreaded _ _ _  => true

/-- **Correspondence**: on the straight-line subset, every dynamic
    `RustExecTraced` trace equals the static `LowCT.toJasminLeakTrace`.
    Proof: structural induction on the derivation; each non-branching
    constructor's trace contribution matches the corresponding clause of
    `toJasminLeakTrace`. The three branching constructors are excluded
    by `straightLine`.

    Note: `whileFalse` and `forZero` are also excluded because
    `straightLine` is `false` on `RWhileNz`/`RFor`. The actual subset
    this covers is "no `RIfNz`/`RWhileNz`/`RFor` anywhere reached during
    execution" — which is precisely what `straightLine` captures
    structurally. -/
theorem RustExecTraced.straightLine_trace_eq
    {N : Nat} {leafSpec : LeafSpec}
    {c : LowCT} {rs rs' : RustState} {t : LeakTrace}
    (hSL : LowCT.straightLine c = true)
    (h : RustExecTraced N leafSpec c rs t rs') :
    t = LowCT.toJasminLeakTrace c := by
  induction h with
  | skip _ => rfl
  | seq c1 c2 _rs0 _t1 _r1 _t2 _rs0' _h1 _h2 ih1 ih2 =>
    simp only [LowCT.straightLine, Bool.and_eq_true] at hSL
    show _ ++ _ = LowCT.toJasminLeakTrace c1 ++ LowCT.toJasminLeakTrace c2
    rw [ih1 hSL.1, ih2 hSL.2]
  | letZero _ _ body _ _ _ _ ih =>
    simp only [LowCT.straightLine] at hSL
    show LeakEvent.pureOp "Cassgn" :: _ = LeakEvent.pureOp "Cassgn" :: _
    rw [ih hSL]
  | letU64Zero _ body _ _ _ _ ih =>
    simp only [LowCT.straightLine] at hSL
    show LeakEvent.pureOp "Cassgn" :: _ = LeakEvent.pureOp "Cassgn" :: _
    rw [ih hSL]
  | scalarSet _ _ _ => rfl
  | ifTrue _ _ _ _ _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | ifFalse _ _ _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | whileFalse _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | whileTrue _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | forZero _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | forSucc _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | forRuntime _ _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | call _ _ _ _ _ _ _ _ _ => rfl
  | cloneCall _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [LowCT.straightLine] at hSL
    -- The inner RCall trace from ih equals [pureOp "Ccall"], so the
    -- prepended pureOp "Copn" gives [pureOp "Copn", pureOp "Ccall"].
    show LeakEvent.pureOp "Copn" :: _ = [LeakEvent.pureOp "Copn", LeakEvent.pureOp "Ccall"]
    rw [ih (by simp [LowCT.straightLine])]
    rfl
  | callSwap _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    -- Two inner RCalls, each with trace [pureOp "Ccall"]; the appended
    -- trace gives [pureOp "Ccall", pureOp "Ccall"], matching the static
    -- `toJasminLeakTrace (.RCallSwap _ _ _ _)`.
    show _ ++ _ = [LeakEvent.pureOp "Ccall", LeakEvent.pureOp "Ccall"]
    rw [ih1 (by simp [LowCT.straightLine]),
        ih2 (by simp [LowCT.straightLine])]
    rfl
  | limbStore _ _ _ _ _ _ => rfl
  | limbStoreExpr _ _ _ _ _ _ => rfl
  -- Phase F/G/H/L/M (2026-05-03): match the structural trace.
  | callN _ _ _ _ _ _ _ _ => rfl
  | callDstThreaded _ _ _ _ _ _ _ _ _ => rfl
  | selectFalse _ _ _ _ _ _ _ _ _ => rfl
  | selectTrue _ _ _ _ _ _ _ _ _ _ _ => rfl
  | assert _ _ => rfl
  | block _ _ _ _ _ ih =>
    simp only [LowCT.straightLine] at hSL
    simp only [LowCT.toJasminLeakTrace]
    exact ih hSL
  -- Phase I: gated `false` by `straightLine` → contradictory.
  | tupleLoad _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  -- Phase J (wave 6, 4.29): gated `false` by `straightLine` → contradictory.
  | arrStore _ _ _ _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | arrLoad _ _ _ _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | scalarSetExpr _ _ _ =>
    simp [LowCT.straightLine] at hSL
  -- Phase DD (2026-05-28): both sides are the single `[Cassgn]` tag; rfl.
  | arrStoreLit _ _ _ _ _ _ _ _ => rfl
  | arrLoadLit _ _ _ _ _ _ _ _ => rfl

/-- **Cross-stage corollary**: on the straight-line subset, the source
    dynamic trace and the target structural Jasmin trace agree. Direct
    consequence of `straightLine_trace_eq` (this file) and
    `Cmd.leakTrace_toJasminCmd` (UnifiedTrace.lean A1.4). -/
theorem RustExecTraced.straightLine_traces_match_jasmin_static
    {N : Nat} {leafSpec : LeafSpec}
    {c : LowCT} {rs rs' : RustState} {t : LeakTrace}
    (hSL : LowCT.straightLine c = true)
    (h : RustExecTraced N leafSpec c rs t rs') :
    t = JasminSem.Cmd.leakTrace (toJasminCmd c) := by
  rw [RustExecTraced.straightLine_trace_eq hSL h,
      ← JasminSem.Cmd.leakTrace_toJasminCmd]

/-! ## Source-dynamic ↔ Target-dynamic on the straight-line subset (A1.15) -/

/-- `toJasminCmd` preserves the Cif-free property: a straight-line
    LowCT's translation is a Cif-free Jasmin Cmd. -/
theorem toJasminCmd_cifFree_of_straightLine (c : LowCT)
    (hSL : LowCT.straightLine c = true) :
    cmdCifFree (toJasminCmd c) = true := by
  induction c with
  | RSkip => rfl
  | RSeq c1 c2 ih1 ih2 =>
    simp only [LowCT.straightLine, Bool.and_eq_true] at hSL
    show cmdCifFree (toJasminCmd c1 ++ toJasminCmd c2) = true
    show List.all (toJasminCmd c1 ++ toJasminCmd c2) instrCifFree = true
    simp only [List.all_append]
    have h1 : List.all (toJasminCmd c1) instrCifFree = true := ih1 hSL.1
    have h2 : List.all (toJasminCmd c2) instrCifFree = true := ih2 hSL.2
    simp [h1, h2]
  | RLetZero x t body ih =>
    simp only [LowCT.straightLine] at hSL
    show cmdCifFree (_ :: toJasminCmd body) = true
    simp only [cmdCifFree_cons, instrCifFree, ih hSL, Bool.and_self]
  | RLetU64Zero x body ih =>
    simp only [LowCT.straightLine] at hSL
    show cmdCifFree (_ :: toJasminCmd body) = true
    simp only [cmdCifFree_cons, instrCifFree, ih hSL, Bool.and_self]
  | RScalarSet _ _ => rfl
  | RCall _ _ _ => rfl
  | RCloneCall _ _ _ _ _ _ => rfl
  | RIfNz _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | RWhileNz _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | RFor _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | RForRuntime _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | RLimbStore _ _ _ => rfl
  | RLimbStoreExpr _ _ _ => rfl
  -- Phase F/G/H/L/M: each lowers to one CIf-free instruction (or empty).
  | RCallSwap _ _ _ _ => rfl
  | RCallN _ _ _ => rfl
  | RSelect _ _ _ _ => rfl
  | RAssert _ => rfl
  | RBlock body ih =>
    simp only [LowCT.straightLine] at hSL
    show cmdCifFree (toJasminCmd body) = true
    exact ih hSL
  -- Phase C: gated `false` by `straightLine` → contradictory.
  | RFnDef _ _ _ _ _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | RFnCall _ _ _ => rfl
  -- Phase I: gated `false` by `straightLine` → contradictory.
  | RTupleLoad _ _ _ =>
    simp [LowCT.straightLine] at hSL
  -- Phase J (wave 6, 4.29): gated `false` by `straightLine` → contradictory.
  | RArrStore _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | RArrLoad _ _ _ =>
    simp [LowCT.straightLine] at hSL
  | RScalarSetExpr _ _ =>
    simp [LowCT.straightLine] at hSL
  -- Phase DD/E2 (2026-05-28/29): literal-index array access and dst-threaded
  -- call lower to a single Cif-free instruction (Cassgn / Ccall); rfl.
  | RArrStoreLit _ _ _ => rfl
  | RArrLoadLit _ _ _ => rfl
  | RCallDstThreaded _ _ _ => rfl

/-- **A1.15 — full source-dynamic ↔ target-dynamic correspondence on
    the straight-line subset.** On a straight-line LowCT, the source
    dynamic trace (`RustExecTraced`) equals the target dynamic trace
    (`jasminSemTraced` on the translation). -/
theorem RustExecTraced.dynamic_traces_match_on_straightLine
    {N : Nat} {leafSpec : LeafSpec}
    {c : LowCT} {rs rs' : RustState} {t_src : LeakTrace}
    {rs_t rs_t' : RustState} {t_tgt : LeakTrace}
    (hSL : LowCT.straightLine c = true)
    (h_src : RustExecTraced N leafSpec c rs t_src rs')
    (h_tgt : jasminSemTraced leafSpec (toJasminCmd c) rs_t t_tgt rs_t') :
    t_src = t_tgt := by
  rw [RustExecTraced.straightLine_traces_match_jasmin_static hSL h_src,
      jasminSemTraced.cifFree_trace_eq
        (toJasminCmd_cifFree_of_straightLine c hSL) h_tgt]

/-! ## A1.16 — Dynamic RHP-2 for branching programs (whileFree subset)

For programs with `RIfNz` (but no `RWhileNz` / `RFor`), the dynamic
correspondence still holds: source and target make the same dynamic
branch decisions on the same `RustState`, so source-dynamic = target-dynamic
on the *whole* whileFree subset (not just the straight-line one).

The cleanest theorem: `RustExecTraced` derivations lift to
`jasminSemTraced` derivations on `toJasminCmd c`, preserving both the
final state and the trace exactly. Same shape as the existing
`rustExecSoundInJasmin` from `JasminSem.lean` but for the trace-emitting
versions. -/

/-- **A1.16**: every `RustExecTraced` derivation on a `whileFree`
    program lifts to a `jasminSemTraced` derivation on the translation,
    preserving both the final state and the entire dynamic trace
    (including branch tags).

    Proof: structural induction on `h`. For each non-branching case the
    trace contribution matches the corresponding `jasminSemTraced` rule;
    for `ifTrue`/`ifFalse` the runtime branch decision (`rs.rsScalar e`)
    is the same on both sides because they share the same state. -/
theorem rustExecTraced_to_jasminSemTraced
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hWf : whileFree c = true)
    {rs rs' : RustState} {t : LeakTrace}
    (h : RustExecTraced N leafSpec c rs t rs') :
    jasminSemTraced leafSpec (toJasminCmd c) rs t rs' := by
  induction h with
  | skip rs0 =>
    show jasminSemTraced leafSpec [] rs0 [] rs0
    exact jasminSemTraced.nil rs0
  | seq c1 c2 rs0 t1 r1 t2 rs0' _h1 _h2 ih1 ih2 =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    have h_jt1 := ih1 hWf.1
    have h_jt2 := ih2 hWf.2
    show jasminSemTraced leafSpec (toJasminCmd c1 ++ toJasminCmd c2) rs0
            (t1 ++ t2) rs0'
    exact jasminSemTraced_seq_compose leafSpec _ _ rs0 r1 rs0' t1 t2 h_jt1 h_jt2
  | letZero x t' body rs0 t_body rs0' _h ih =>
    simp only [whileFree] at hWf
    have h_jt := ih hWf
    -- toJasminCmd (RLetZero x t' body) = init :: toJasminCmd body
    -- where init is the Cassgn (Parr_init) instruction.
    show jasminSemTraced leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t'.storageBytes },
                               info := { towerTag := t'.byteSize } })
                     .AT_none (.sarr t'.storageBytes)
                     (.Parr_init t'.storageBytes) :: toJasminCmd body)
            rs0 (LeakEvent.pureOp "Cassgn" :: t_body) rs0'
    exact jasminSemTraced.cons _ _ rs0 [LeakEvent.pureOp "Cassgn"]
            (rsSetTower rs0 x ⟨t', default⟩) t_body rs0'
            (jasminSemTraced.assgn_parr_init x t' rs0)
            h_jt
  | letU64Zero x body rs0 t_body rs0' _h ih =>
    simp only [whileFree] at hWf
    have h_jt := ih hWf
    show jasminSemTraced leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 },
                               info := {} }) .AT_none (.sword .U64) (.Pconst 0)
              :: toJasminCmd body)
            rs0 (LeakEvent.pureOp "Cassgn" :: t_body) rs0'
    exact jasminSemTraced.cons _ _ rs0 [LeakEvent.pureOp "Cassgn"]
            (rsSetScalar rs0 x 0) t_body rs0'
            (jasminSemTraced.assgn_u64_zero x rs0)
            h_jt
  | scalarSet x v rs0 =>
    -- toJasminCmd (RScalarSet x v) = [Cassgn (Papp1 (Oword_of_int U64) (Pconst v))]
    exact jasminSemTraced.assgn_u64_val x v rs0
  | ifTrue e ct cf rs0 t_branch rs0' v hv hne _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    have h_jt := ih hWf.1
    -- jasminSemTraced.if_true takes ct (the source `LowCT`) — but jasminSemTraced
    -- works on Jasmin Cmds, so we apply the rule with toJasminCmd ct / toJasminCmd cf.
    exact jasminSemTraced.if_true e (toJasminCmd ct) (toJasminCmd cf) rs0 rs0'
            v t_branch hv hne h_jt
  | ifFalse e ct cf rs0 t_branch rs0' h0 _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    have h_jt := ih hWf.2
    exact jasminSemTraced.if_false e (toJasminCmd ct) (toJasminCmd cf) rs0 rs0'
            t_branch h0 h_jt
  | whileFalse _ _ _ _ =>
    simp [whileFree] at hWf
  | whileTrue _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp [whileFree] at hWf
  | forZero x body rs0 =>
    -- toJasminCmd (RFor x 0 body) = unrollForJ x _ 0 = []; trace = [].
    show jasminSemTraced leafSpec (toJasminCmd (.RFor x 0 body)) rs0 [] rs0
    show jasminSemTraced leafSpec (unrollForJ x (toJasminCmd body) 0) rs0 [] rs0
    simp only [unrollForJ]
    exact jasminSemTraced.nil rs0
  | forSucc x n body rs0 t1 r1 t2 rs0' _hInner _hBody ih1 ih2 =>
    simp only [whileFree] at hWf
    have hWfInner : whileFree (.RFor x n body) = true := by simp [whileFree, hWf]
    have hJ_inner : jasminSemTraced leafSpec (toJasminCmd (.RFor x n body)) rs0 t1 r1 :=
      ih1 hWfInner
    have hJ_body : jasminSemTraced leafSpec (toJasminCmd body)
                     (rsSetScalar r1 x n) t2 rs0' := ih2 hWf
    -- The scalar-set step.
    have hJ_set : jasminSemTraced leafSpec
        [(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64)
                  (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)]
        r1 [LeakEvent.pureOp "Cassgn"] (rsSetScalar r1 x n) :=
      jasminSemTraced.assgn_u64_val x n r1
    -- Compose `[scalarSet] ++ bodyJ`.
    have hJ_post : jasminSemTraced leafSpec
        ([(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                   .AT_none (.sword .U64)
                   (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)] ++
         toJasminCmd body)
        r1 ([LeakEvent.pureOp "Cassgn"] ++ t2) rs0' :=
      jasminSemTraced_seq_compose leafSpec _ _ r1 (rsSetScalar r1 x n) rs0'
        [LeakEvent.pureOp "Cassgn"] t2 hJ_set hJ_body
    -- Compose with inner loop.
    show jasminSemTraced leafSpec (toJasminCmd (.RFor x (n+1) body)) rs0
      (t1 ++ LeakEvent.pureOp "Cassgn" :: t2) rs0'
    show jasminSemTraced leafSpec (unrollForJ x (toJasminCmd body) (n+1)) rs0
      (t1 ++ LeakEvent.pureOp "Cassgn" :: t2) rs0'
    simp only [unrollForJ]
    show jasminSemTraced leafSpec
      (unrollForJ x (toJasminCmd body) n ++
        ([(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                   .AT_none (.sword .U64)
                   (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)] ++
         toJasminCmd body))
      rs0
      (t1 ++ ([LeakEvent.pureOp "Cassgn"] ++ t2))
      rs0'
    exact jasminSemTraced_seq_compose leafSpec _ _ rs0 r1 rs0' t1 _ hJ_inner hJ_post
  | forRuntime _ _ _ _ _ _ _ _ =>
    -- Runtime loop is excluded from the whileFree fragment.
    simp [whileFree] at hWf
  | call f dest args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact jasminSemTraced.call_oracle f dest args rs0 oldDestV argList hLk hArgs
            hArgsTyped
  | cloneCall cv ct oldDest innerF dest args rs0 rsClone t_call rs0'
                hClone _hCall ihCall =>
    -- toJasminCmd (RCloneCall ..) = [CLONE_TOWER-Copn, Ccall ...]
    -- Trace = pureOp "Copn" :: t_call (where t_call is the inner Ccall trace).
    -- We need ihCall — the IH for the inner RCall.
    have hWf_inner : whileFree (.RCall innerF dest args) = true := by
      simp [whileFree]
    have h_jt_call := ihCall hWf_inner
    -- Build the cons composition: clone_tower + call_oracle.
    show jasminSemTraced leafSpec
            (_ :: [.Ccall .DoNotInline [locToLVal dest] { name := innerF }
                          (args.map locToPExpr)])
            rs0 (LeakEvent.pureOp "Copn" :: t_call) rs0'
    refine jasminSemTraced.cons _ _ rs0 [LeakEvent.pureOp "Copn"]
              rsClone t_call rs0' ?_ h_jt_call
    -- The clone step:
    rw [hClone]
    exact jasminSemTraced.clone_tower cv ct oldDest rs0
  | callSwap f dest1 dest2 args rs0 t1 rs1 t2 rs0' _h1 _h2 ih1 ih2 =>
    -- toJasminCmd (RCallSwap ..) = [Ccall(dest1), Ccall(dest2)].
    -- Trace = t1 ++ t2 (each subcall has trace [pureOp "Ccall"]).
    -- Compose via jasminSemTraced_seq_compose on the two singleton lists.
    have hWf_inner : whileFree (.RCall f dest1 args) = true := by
      simp [whileFree]
    have hWf_inner2 : whileFree (.RCall f dest2 args) = true := by
      simp [whileFree]
    have h_jt1 := ih1 hWf_inner
    have h_jt2 := ih2 hWf_inner2
    show jasminSemTraced leafSpec
            ([.Ccall .DoNotInline [locToLVal dest1] { name := f }
                      (args.map locToPExpr)] ++
             [.Ccall .DoNotInline [locToLVal dest2] { name := f }
                      (args.map locToPExpr)])
            rs0 (t1 ++ t2) rs0'
    exact jasminSemTraced_seq_compose leafSpec _ _ rs0 rs1 rs0' t1 t2 h_jt1 h_jt2
  | limbStore loc idx v rs0 oldDestV hLk =>
    exact jasminSemTraced.limb_store_oracle loc idx v rs0 oldDestV hLk
  -- Phase R5: gated `whileFree = false`, unreachable under hWf.
  | limbStoreExpr _ _ _ _ _ _ => simp [whileFree] at hWf
  -- Phase F/G/H/L/M (2026-05-03): not yet covered by simulation;
  -- gated `whileFree = false`, so each case is unreachable under hWf.
  | callN _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | callDstThreaded _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | selectFalse _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | selectTrue _ _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  -- Phase L: RAssert is `whileFree = true` and lowers to `[]`;
  -- the dynamic trace is `[]`, so the goal is `jasminSemTraced [] rs [] rs`,
  -- discharged by `jasminSemTraced.nil`.
  | assert label rs0 =>
    show jasminSemTraced leafSpec [] rs0 [] rs0
    exact jasminSemTraced.nil rs0
  -- Phase M: RBlock body is `whileFree = whileFree body`; lowers to
  -- `toJasminCmd body`.  Trace is `t_body`.  Closed via the inner IH.
  | block body rs0 t_body rs0' _hBody ih =>
    simp only [whileFree] at hWf
    exact ih hWf
  -- Phase I: gated `whileFree = false`, so each case is unreachable.
  | tupleLoad _ _ _ _ => simp [whileFree] at hWf
  -- Phase J (wave 6, 4.29): gated `whileFree = false`.
  | arrStore _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | arrLoad _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | scalarSetExpr _ _ _ => simp [whileFree] at hWf
  -- Phase DD (2026-05-28): literal-index array store/load are `whileFree =
  -- false` (not yet covered by the simulation theorem); contradiction.
  | arrStoreLit _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | arrLoadLit _ _ _ _ _ _ _ _ => simp [whileFree] at hWf

/-! ### A1.16' — Reverse compiler correctness (jasmin → rust)

The mirror of `rustExecTraced_to_jasminSemTraced`. Given a Jasmin
derivation on `toJasminCmd c` for a `whileFree c`, recover a Rust
derivation on `c` with the same trace and states.

With the **intrinsic encoding** of `Located` (single `locType` field;
`locDst := locSrc`), `locToLVal` and `locToPExpr` are injective —
they fully determine the underlying `Located`, so there is no
"`locDst` ambiguity" to resolve. -/

/-- A1.16' (reverse): every Jasmin derivation on a translated
    `whileFree` source program lifts to a Rust derivation on the
    source. Proven by structural induction on `c`, bridging via
    `toPrime` to the refactored mutual inductive for cleaner
    inversion. The intrinsic `Located` encoding (post-locDst-drop)
    makes the Located-using cases (RCall, RCloneCall, RLimbStore)
    closeable directly — no `locatedFree` restriction needed. The
    source-side tower types are recovered from the ghost
    `VarInfo.towerTag` in the inverted instruction via
    `TowerType.byteSize_inj`. -/
theorem jasminSemTraced_to_rustExecTraced
    {N : Nat} {leafSpec : LeafSpec} :
    ∀ (c : LowCT) {rs rs' : RustState} {t : LeakTrace},
    whileFree c = true →
    -- `forFree` gates out `RFor`: the forward direction's static-unrolling
    -- emits per-iteration `Cassgn` events that this reverse theorem cannot
    -- (yet) split back into iteration boundaries.  See the `RFor` case
    -- below for the contradiction.
    forFree c = true →
    jasminSemTraced leafSpec (toJasminCmd c) rs t rs' →
    RustExecTraced N leafSpec c rs t rs'
  | .RSkip, rs, rs', t, _hWf, _hFF, h => by
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    cases h'
    exact RustExecTraced.skip rs
  | .RSeq c1 c2, rs, rs', t, hWf, hFF, h => by
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [forFree, Bool.and_eq_true] at hFF
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    obtain ⟨r1, t1, t2, ht, hL1, hL2⟩ :=
      jasminSemTraced'_split leafSpec _ _ rs rs' t h'
    have hR1 := jasminSemTraced_to_rustExecTraced (N := N) c1 hWf.1 hFF.1
                  (jasminSemTraced'.toOriginal hL1)
    have hR2 := jasminSemTraced_to_rustExecTraced (N := N) c2 hWf.2 hFF.2
                  (jasminSemTraced'.toOriginal hL2)
    rw [ht]
    exact RustExecTraced.seq c1 c2 rs t1 r1 t2 rs' hR1 hR2
  | .RLetZero x t' body, rs, rs', t, hWf, hFF, h => by
    simp only [whileFree] at hWf
    simp only [forFree] at hFF
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    cases h' with
    | cons _i _is _rs t1 rs1 t2 _rs' h_single h_rest =>
      cases h_single with
      | assgn_parr_init _ tInner _ _ _ _hn htag =>
        -- Inversion yields `htag : t'.byteSize = tInner.byteSize`;
        -- `byteSize_inj` recovers `t' = tInner`.
        have ht' : t' = tInner := TowerType.byteSize_inj htag
        subst ht'
        have hR_body := jasminSemTraced_to_rustExecTraced (N := N) body hWf hFF
                          (jasminSemTraced'.toOriginal h_rest)
        show RustExecTraced N leafSpec (.RLetZero x t' body) rs
              ([LeakEvent.pureOp "Cassgn"] ++ t2) rs'
        simp only [List.singleton_append]
        exact RustExecTraced.letZero x t' body rs t2 rs' hR_body
  | .RLetU64Zero x body, rs, rs', t, hWf, hFF, h => by
    simp only [whileFree] at hWf
    simp only [forFree] at hFF
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    cases h' with
    | cons _i _is _rs t1 rs1 t2 _rs' h_single h_rest =>
      cases h_single with
      | assgn_u64_zero _ _ =>
        have hR_body := jasminSemTraced_to_rustExecTraced (N := N) body hWf hFF
                          (jasminSemTraced'.toOriginal h_rest)
        show RustExecTraced N leafSpec (.RLetU64Zero x body) rs
              ([LeakEvent.pureOp "Cassgn"] ++ t2) rs'
        simp only [List.singleton_append]
        exact RustExecTraced.letU64Zero x body rs t2 rs' hR_body
  | .RScalarSet x v, rs, rs', t, _hWf, _hFF, h => by
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    have h_single := jasminSemTraced'.singleton_inv h'
    cases h_single with
    | assgn_u64_val _ _ _ =>
      exact RustExecTraced.scalarSet x v rs
  | .RIfNz e ct cf, rs, rs', t, hWf, hFF, h => by
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [forFree, Bool.and_eq_true] at hFF
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    have h_single := jasminSemTraced'.singleton_inv h'
    cases h_single with
    | if_true _ _ _ _ _ v tInner hv hne hct =>
      have hR_ct := jasminSemTraced_to_rustExecTraced (N := N) ct hWf.1 hFF.1
                      (jasminSemTraced'.toOriginal hct)
      exact RustExecTraced.ifTrue e ct cf rs tInner rs' v hv hne hR_ct
    | if_false _ _ _ _ _ tInner h0 hcf =>
      have hR_cf := jasminSemTraced_to_rustExecTraced (N := N) cf hWf.2 hFF.2
                      (jasminSemTraced'.toOriginal hcf)
      exact RustExecTraced.ifFalse e ct cf rs tInner rs' h0 hR_cf
  | .RCall f dest args, rs, rs', t, _hWf, _hFF, h => by
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    have h_single := jasminSemTraced'.singleton_inv h'
    -- Option A (use-site): the `jasminSemTracedSingle.call_oracle`
    -- constructor's InstrR index mentions `args.map locToPExpr` directly
    -- (no free `argEs` parameter), so `cases h_single` would have to
    -- solve `args.map locToPExpr = args✝.map locToPExpr` — `List.map` is
    -- not injective in general.  Generalize the args list so the
    -- eliminator sees a free variable, then recover via the side hyps.
    -- Mirrors the technique in `JasminSemTracedDeterminism.det_call_oracle_pair`.
    generalize hArgEs : (List.map locToPExpr args) = argEs at h_single
    cases h_single with
    | call_oracle _ dest' _ _ _ args' _ oldDestV argList
                    hVar hM hTag hLk hArgs hArgsTyped =>
      -- Recover dest = dest' from the InstrR-forced equalities.  Located
      -- has only two fields (`locVar`, `locSrc`); `locDst` is an abbrev
      -- for `locSrc`.  After unification with the outer `dest` (from
      -- the RCall pattern), constructor side hyps `hVar`/`hTag` give
      -- the two needed projections, and `cases loc; cases loc'; simp_all`
      -- closes the structural equality (mirrors the `RLimbStore` case
      -- below at the `loc = loc'` step).
      have hVarEq : dest.locVar = dest'.locVar := hVar
      -- `hTag : dest.locSrc.byteSize = dest'.locSrc.byteSize` comes from the
      -- ghost `towerTag` in the instruction; `byteSize_inj` recovers the type.
      have hSrcEq : dest.locSrc = dest'.locSrc := TowerType.byteSize_inj hTag
      have hDest : dest = dest' := by cases dest; cases dest'; simp_all
      subst hDest
      -- Recover args = args' from `args.map locToPExpr = args'.map locToPExpr`.
      -- `map_locToPExpr_inj` recovers per-index `locVar` AND `locSrc` (no
      -- type-recovery needed because `Located` only has those two fields;
      -- `locDst` is an abbrev for `locSrc`).
      have hArgsMap : args.map locToPExpr = args'.map locToPExpr := hArgEs
      have hArgs' : args = args' := by
        have hSame := map_locToPExpr_inj _ _ hArgsMap
        apply List.ext_get hSame.1
        intro i hi1 hi2
        have hVarSrc := hSame.2 i hi1 hi2
        cases h_a1 : args.get ⟨i, hi1⟩
        cases h_a2 : args'.get ⟨i, hi2⟩
        rw [h_a1, h_a2] at hVarSrc
        simp_all
      subst hArgs'
      exact RustExecTraced.call f dest args rs oldDestV argList hLk hArgs hArgsTyped
  | .RCloneCall cv ct oldDest innerF dest args, rs, rs', t, _hWf, _hFF, h => by
    -- `toJasminCmd (RCloneCall ..) = [CLONE_TOWER-Copn, Ccall innerF ..]`:
    -- split via `cons`, invert the CLONE_TOWER `Copn` via `clone_tower`
    -- (the ghost `towerTag` pins `ct` through `byteSize_inj`), recurse on
    -- the inner `RCall innerF dest args` for the `Ccall` tail, and compose
    -- via `RustExecTraced.cloneCall`.
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    cases h' with
    | cons _i _is _rs t1 rs1 t2 _rs' h_single h_rest =>
      -- Expose the `locToPExpr oldDest` operand as a literal `Pvar` and
      -- generalize the `AsmOp` literal so the eliminator can invert the
      -- `Copn`-headed constructors.
      simp only [locToPExpr, locToGVar, locToVar, towerToSType] at h_single
      generalize hOp : ({ name := "CLONE_TOWER" } : AsmOp) = aop at h_single
      generalize hov : oldDest.locVar = ov at h_single
      generalize hom : oldDest.locSrc.storageBytes = om at h_single
      generalize hotag : oldDest.locSrc.byteSize = otag at h_single
      cases h_single
      case clone_tower ct' oldDest' hn hCloneTag hVar hM hOldTag =>
        -- `hCloneTag : ct.byteSize = ct'.byteSize` pins the clone type.
        obtain rfl : ct = ct' := TowerType.byteSize_inj hCloneTag
        -- Recurse on the Ccall tail.
        have h_rest_orig : jasminSemTraced leafSpec
            (toJasminCmd (.RCall innerF dest args)) _ t2 rs' :=
          jasminSemTraced'.toOriginal h_rest
        have hWf_inner : whileFree (.RCall innerF dest args) = true := by
          simp [whileFree]
        have hFF_inner : forFree (.RCall innerF dest args) = true := by
          simp [forFree]
        have hR_call := jasminSemTraced_to_rustExecTraced (N := N)
                          (.RCall innerF dest args) hWf_inner hFF_inner
                          h_rest_orig
        -- The clone step's output state mentions `oldDest'.locVar`; the
        -- instruction pins it to `oldDest.locVar`.
        rw [← hVar, ← hov] at hR_call
        exact RustExecTraced.cloneCall cv ct oldDest innerF dest args rs
                _ t2 rs' rfl hR_call
  | .RWhileNz _ _, _, _, _, hWf, _, _ => by
    simp [whileFree] at hWf
  | .RFor _ _ _, _, _, _, _, hFF, _ => by
    -- The reverse trace direction would need to split the unrolled Jasmin
    -- trace back into per-iteration boundaries; gated `forFree = false`
    -- pending that work.
    simp [forFree] at hFF
  | .RForRuntime _ _ _, _, _, _, hWf, _, _ => by
    -- Runtime loop is excluded from the whileFree fragment.
    simp [whileFree] at hWf
  | .RLimbStore loc idx v, rs, rs', t, _hWf, _hFF, h => by
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    have h_single := jasminSemTraced'.singleton_inv h'
    -- Generalize v.toNat and the AsmOp name to avoid dependent-elim
    -- failures in the cases tactic.
    generalize hVN : v.toNat = vN at h_single
    generalize hAsm : ({ name := "STORE64" } : AsmOp) = aop at h_single
    cases h_single with
    | limb_store_oracle loc' _ _ _ _ vBV _ oldDestV hVar hM hTag hLk =>
      -- Recover loc = loc' from the InstrR-forced equalities + the
      -- intrinsic Located encoding.
      have hVarEq : loc.locVar = loc'.locVar := hVar
      -- `hTag` is the ghost `towerTag` equality forced by the `Copn`
      -- index; `byteSize_inj` recovers the type.
      have hSrcEq : loc.locSrc = loc'.locSrc := TowerType.byteSize_inj hTag
      have hLoc : loc = loc' := by cases loc; cases loc'; simp_all
      subst hLoc
      have hVeq : v.toNat = vBV.toNat := hVN
      have hV : v = vBV := BitVec.eq_of_toNat_eq hVeq
      subst hV
      exact RustExecTraced.limbStore loc idx v rs oldDestV hLk
  -- Phase R5: RLimbStoreExpr is gated `whileFree = false` (its reverse-trace
  -- inversion is future work), so unreachable under hWf.
  | .RLimbStoreExpr _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  -- RCallSwap: lowers to two sequential `.Ccall` instructions.
  -- Pattern mirrors RCloneCall: split via `cons`, invert each Ccall
  -- via the `RCall` reverse case, then compose via `RustExecTraced.callSwap`.
  | .RCallSwap f dest1 dest2 args, rs, rs', t, _hWf, _hFF, h => by
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    -- Two-instruction Cmd: split into call(dest1) step + call(dest2) step.
    cases h' with
    | cons _i _is _rs t1 rs1 t2 _rs' h_single h_rest =>
      -- The first instruction is `.Ccall .DoNotInline [locToLVal dest1]
      -- { name := f } (args.map locToPExpr)`.  Recurse on the inner
      -- `.RCall f dest1 args` whose Jasmin lowering is exactly that
      -- single instruction (wrapped via `nil` at the tail).
      have hWf_inner1 : whileFree (.RCall f dest1 args) = true := by
        simp [whileFree]
      -- Repackage h_single as a singleton-cons jasminSemTraced derivation.
      have hSingle1 : jasminSemTraced leafSpec
          (toJasminCmd (.RCall f dest1 args)) rs t1 rs1 := by
        show jasminSemTraced leafSpec
            [.Ccall .DoNotInline [locToLVal dest1] { name := f }
                    (args.map locToPExpr)]
            rs t1 rs1
        -- The single-step h_single becomes a one-instruction trace via
        -- jasminSemTraced.cons with nil tail.
        have h_single_orig := jasminSemTracedSingle.toOriginal h_single
        -- h_single_orig : jasminSemTraced leafSpec [<that one instr>] rs t1 rs1
        exact h_single_orig
      have hFF_inner1 : forFree (.RCall f dest1 args) = true := by simp [forFree]
      have hR_call1 := jasminSemTraced_to_rustExecTraced (N := N)
                         (.RCall f dest1 args) hWf_inner1 hFF_inner1 hSingle1
      -- Now invert h_rest similarly.  h_rest : jasminSemTraced'
      -- [Ccall dest2 ...] rs1 t2 rs'.
      have h_rest_orig := jasminSemTraced'.toOriginal h_rest
      have hWf_inner2 : whileFree (.RCall f dest2 args) = true := by
        simp [whileFree]
      have hFF_inner2 : forFree (.RCall f dest2 args) = true := by simp [forFree]
      have hR_call2 := jasminSemTraced_to_rustExecTraced (N := N)
                         (.RCall f dest2 args) hWf_inner2 hFF_inner2 h_rest_orig
      -- Compose via callSwap.
      exact RustExecTraced.callSwap f dest1 dest2 args rs t1 rs1 t2 rs'
              hR_call1 hR_call2
  -- Phase F/G/H/L/M: RCallN/RSelect are gated `whileFree = false`,
  -- so those cases are unreachable under hWf.
  | .RCallN _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  | .RSelect _ _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  -- Phase L: RAssert lowers to `[]`; the only Jasmin derivation is `nil`,
  -- which forces `t = []` and `rs = rs'`. Reconstruct `RustExecTraced.assert`.
  | .RAssert label, rs, rs', t, _hWf, _hFF, h => by
    simp only [toJasminCmd] at h
    have h' := jasminSemTraced.toPrime h
    cases h'
    exact RustExecTraced.assert label rs
  -- Phase M: RBlock body lowers to `toJasminCmd body`; trace and states
  -- match the inner derivation.  Recurse on the body via the IH.
  | .RBlock body, rs, rs', t, hWf, hFF, h => by
    simp only [whileFree] at hWf
    simp only [forFree] at hFF
    simp only [toJasminCmd] at h
    have hR_body := jasminSemTraced_to_rustExecTraced (N := N) body hWf hFF h
    exact RustExecTraced.block body rs t rs' hR_body
  -- Phase C: RFnDef/RFnCall are gated `whileFree = false`.
  | .RFnDef _ _ _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  | .RFnCall _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  -- Phase I: RTupleLoad is gated `whileFree = false`.
  | .RTupleLoad _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  -- Phase J (wave 6, 4.29): also gated `whileFree = false`.
  | .RArrStore _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  | .RArrLoad _ _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
  | .RScalarSetExpr _ _, _, _, _, hWf, _, _ => by simp [whileFree] at hWf
termination_by c => sizeOf c
decreasing_by
  -- All recursive calls reduce structurally on `sizeOf c`.  The
  -- RCloneCall → RCall recursion drops `cv`, `ct`, `oldDest`, so
  -- `sizeOf` strictly decreases by `1 + sizeOf cv + sizeOf ct + sizeOf oldDest`.
  -- The RCallSwap → RCall(destX) recursion drops one Located plus the
  -- structural overhead of `RCallSwap`; close by case-splitting on
  -- the dropped Located so omega sees its `≥ 1` sizeOf weight.
  -- Most cases close with `simp_wf; omega`.
  all_goals simp_wf
  all_goals first
    | omega
    | (cases oldDest with | mk a b => simp; omega)
    | (-- RCallSwap → RCall recursion: inject Located.sizeOf_pos
       -- to give omega the ≥ 1 constructor weight for the dropped
       -- Located (dest2 for the first recursion, dest1 for the
       -- second).  Closes via the constructor-weight inequality
       -- exposed by the `Located.sizeOf_pos` lemma.
       have h1 := Located.sizeOf_pos dest1
       have h2 := Located.sizeOf_pos dest2
       omega)

/-! ## A1.17 — Set-based hyperproperty framework

A *hyperproperty* (Clarkson–Schneider) is a property of *sets* of
traces: `H : Set LeakTrace → Prop`. The trace set associated with a
program is the set of traces it can produce over varying inputs
(here: initial `RustState`s). This generalises the k-safety framework
of A1.11 (which quantifies over k-tuples of *programs*) to true
hyperproperties (sets of *traces from one program*).

The back-translation specialises to the syntactic correspondence: the
source trace set of a LowCT `c` is contained in the target trace set
of `toJasminCmd c` by A1.16. With the matching-determinism follow-up,
the two sets coincide and any hyperproperty preserved on one side is
preserved on the other. -/

/-- Source-side trace set: all traces producible by `RustExecTraced`
    derivations of `c` over varying initial states. -/
def RustExecTraced.tracesOf (N : Nat) (leafSpec : LeafSpec) (c : LowCT) :
    Set LeakTrace :=
  { t | ∃ rs rs', RustExecTraced N leafSpec c rs t rs' }

/-- Target-side trace set: all traces producible by `jasminSemTraced`
    derivations of `body` over varying initial states. -/
def JasminSemTracedTracesOf (leafSpec : LeafSpec)
    (body : CatCrypt.Crypto.Jasmin.Cmd) : Set LeakTrace :=
  { t | ∃ rs rs', jasminSemTraced leafSpec body rs t rs' }

/-- A hyperproperty over `LeakTrace`s. -/
abbrev Hyperproperty := Set LeakTrace → Prop

/-- Back-translation of a hyperproperty from the target (Jasmin) trace
    set to the source (LowCT) trace set. -/
def Hyperproperty.backTranslate (N : Nat) (leafSpec : LeafSpec)
    (H : Hyperproperty) (c : LowCT) : Prop :=
  H (RustExecTraced.tracesOf N leafSpec c)

/-- **A1.17 forward inclusion**: every source trace is a target trace
    (via A1.16). On the `whileFree` subset, the source trace set of
    `c` is a subset of the target trace set of `toJasminCmd c`. -/
theorem RustExecTraced.tracesOf_subset_jasmin
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hWf : whileFree c = true) :
    RustExecTraced.tracesOf N leafSpec c ⊆
      JasminSemTracedTracesOf leafSpec (toJasminCmd c) := by
  intro t ht
  obtain ⟨rs, rs', h⟩ := ht
  exact ⟨rs, rs', rustExecTraced_to_jasminSemTraced hWf h⟩

/-- **A1.17 hyperproperty preservation (forward)**: any *monotone*
    hyperproperty preserved on the target side transfers to the source
    side. ("Monotone" = closed under shrinking the trace set.)

    Concretely: many trace-set hyperproperties of interest — including
    "every trace satisfies P", "all traces are in some bounded
    language" — are monotone in this sense. For such H, target-side
    satisfaction implies source-side satisfaction by A1.17 inclusion. -/
theorem Hyperproperty.monotone_preservation
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    {H : Hyperproperty}
    (hMono : ∀ S T : Set LeakTrace, S ⊆ T → H T → H S)
    (hWf : whileFree c = true)
    (hTgt : H (JasminSemTracedTracesOf leafSpec (toJasminCmd c))) :
    Hyperproperty.backTranslate N leafSpec H c :=
  hMono _ _ (RustExecTraced.tracesOf_subset_jasmin hWf) hTgt

/-! ### Reverse inclusion (whileFree)

The reverse direction of `tracesOf_subset_jasmin`: every Jasmin trace
is also a Rust trace on the `whileFree` subset. Follows from A1.16'.
With the intrinsic Located encoding, this needs no
`locatedFree` restriction. -/

theorem JasminSemTracedTracesOf_subset_rust
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hWf : whileFree c = true) (hFF : forFree c = true) :
    JasminSemTracedTracesOf leafSpec (toJasminCmd c) ⊆
      RustExecTraced.tracesOf N leafSpec c := by
  intro t ht
  obtain ⟨rs, rs', h⟩ := ht
  exact ⟨rs, rs', jasminSemTraced_to_rustExecTraced (N := N) c hWf hFF h⟩

/-! ### Trace-set equality (whileFree subset) -/

theorem RustExecTraced.tracesOf_eq_jasmin
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hWf : whileFree c = true) (hFF : forFree c = true) :
    RustExecTraced.tracesOf N leafSpec c
      = JasminSemTracedTracesOf leafSpec (toJasminCmd c) := by
  apply Set.eq_of_subset_of_subset
  · exact RustExecTraced.tracesOf_subset_jasmin hWf
  · exact JasminSemTracedTracesOf_subset_rust hWf hFF

/-! ### Unrestricted hyperproperty preservation (whileFree subset)

For any hyperproperty H (no monotonicity needed), source and target
satisfaction agree on the `whileFree` subset. -/

theorem Hyperproperty.preservation
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    {H : Hyperproperty}
    (hWf : whileFree c = true) (hFF : forFree c = true) :
    H (JasminSemTracedTracesOf leafSpec (toJasminCmd c))
      ↔ Hyperproperty.backTranslate N leafSpec H c := by
  unfold Hyperproperty.backTranslate
  rw [RustExecTraced.tracesOf_eq_jasmin hWf hFF]

/-! ### Worked hyperproperty example: "every trace contains no Cif"

Restate `TargetCifFree` from `UnifiedTrace.lean` as a hyperproperty
("every trace in the set is Cif-free"). This is monotone (closed under
shrinking the set), so target-side satisfaction transfers to source. -/

/-- The hyperproperty: every trace in the set is Cif-free. -/
def Hyperproperty.allTracesCifFree : Hyperproperty :=
  fun S => ∀ t ∈ S, LeakEvent.pureOp "Cif" ∉ t

/-- `allTracesCifFree` is monotone (closed under set shrinking). -/
theorem Hyperproperty.allTracesCifFree_monotone
    (S T : Set LeakTrace) (hST : S ⊆ T)
    (hT : Hyperproperty.allTracesCifFree T) :
    Hyperproperty.allTracesCifFree S :=
  fun t ht => hT t (hST ht)

/-- **Worked example**: target-side "all traces Cif-free" transfers
    to source-side via the monotone preservation framework. -/
theorem Hyperproperty.cifFree_transfers
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hWf : whileFree c = true)
    (hTgt : Hyperproperty.allTracesCifFree
              (JasminSemTracedTracesOf leafSpec (toJasminCmd c))) :
    Hyperproperty.backTranslate N leafSpec
        Hyperproperty.allTracesCifFree c :=
  Hyperproperty.monotone_preservation
    Hyperproperty.allTracesCifFree_monotone hWf hTgt

/-! ### Determinism (whileFree subset) — derived via the Jasmin bridge

For the `whileFree` subset, `RustExecTraced.deterministic` follows
from `jasminSemTraced.deterministic` via the
`rustExecTraced_to_jasminSemTraced` bridge. Both source derivations
embed into the Jasmin side, where determinism applies. -/

theorem RustExecTraced.deterministic
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    {rs : RustState} {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (hWf : whileFree c = true)
    (h1 : RustExecTraced N leafSpec c rs t1 rs1)
    (h2 : RustExecTraced N leafSpec c rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  have hj1 := rustExecTraced_to_jasminSemTraced hWf h1
  have hj2 := rustExecTraced_to_jasminSemTraced hWf h2
  exact jasminSemTraced.deterministic hj1 hj2

/-- Non-traced determinism for `RustExec` (whileFree subset): via the
    traced promotion `RustExec.toTraced` + `RustExecTraced.deterministic`. -/
theorem RustExec.deterministic
    {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    {rs rs1 rs2 : RustState}
    (hWf : whileFree c = true)
    (h1 : RustExec N leafSpec c rs rs1)
    (h2 : RustExec N leafSpec c rs rs2) :
    rs1 = rs2 := by
  obtain ⟨_, h1'⟩ := RustExec.toTraced h1
  obtain ⟨_, h2'⟩ := RustExec.toTraced h2
  exact (RustExecTraced.deterministic hWf h1' h2').2

end CatCrypt.Crypto.SecureCompilation.RustExecTraced
