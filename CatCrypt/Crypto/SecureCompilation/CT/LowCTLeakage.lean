/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CT.Leakage
public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# The constant-time leakage model at `LowCT`

The source-level instance of the leakage model of `CT/Leakage.lean`, over the
same observation type `CTLeak` and the same two-run definition
`ConstantTimeRel`.

* `RustExecLeak N leafSpec M c rs t rs'` is `RustExec` with a leakage trace `t`:
  a `branch` event per guard test of `RIfNz` and `RWhileNz`, a `trip` event with
  the value of a `RForRuntime` bound, an `addr` event with the array variable and
  element index of every array access, a `vt` event for every scalar-expression
  node whose x86 mnemonic (under `M.mnem`) makes its operands observable in the
  regime `M.regime`, and the events `M.vtEvents` for a call that `M.leafVT` marks: a
  `vtCall` event with the argument bytes for a variable-time leaf, the trace of its
  lowered run for a linked callee.
* `RustExecLeak.toRustExec` and `RustExec.exists_leak` state that the trace is
  an annotation: erasing it gives `RustExec`, and every `RustExec` run has one.
* `LowCTConstantTime` is constant time for a `LevelTable` split: runs from
  states that agree on the public scalar and tower slots have equal traces.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CT

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Variable-time operand events of scalar expressions -/

/-- The x86 mnemonic of the head node of a scalar expression under the owned
    lowering: a shift by a literal count is the immediate form (`SHR`, `SHL`,
    `SAR`), a shift by a computed count the BMI2 form (`SHRX`, `SHLX`, `SARX`);
    `SLt` is a compare; the multiplies are `IMUL` and `MULX`. Leaves have none. -/
def sexprMnem : SExpr → Option X86Mnem
  | .SVar _ | .SLit _ | .SLimb _ _ => none
  | .SAdd _ _ => some .add
  | .SSub _ _ => some .sub
  | .SMul _ _ | .SMulS _ _ | .SMulHiS _ _ => some .imul
  | .SShr _ (.SLit _) => some .shr
  | .SShr _ _ => some .shrx
  | .SShl _ (.SLit _) => some .shl
  | .SShl _ _ => some .shlx
  | .SAnd _ _ => some .and
  | .SXor _ _ => some .xor
  | .SLt _ _ => some .cmp
  | .SAsr _ (.SLit _) => some .sar
  | .SAsr _ _ => some .sarx
  | .SMulHiU _ _ => some .mulx

/-- The bytes of a tower value, as natural numbers. -/
def towerBytes (v : Σ t : TowerType, RustVal t) : List Nat :=
  List.ofFn (fun j => (v.2 j).toNat)

/-- The parameters of the `LowCT` leakage: the hardware regime, the mnemonic of each
    scalar-expression node, the calls whose events the model supplies (`leafVT`), and
    those events on the argument slots of the call (`vtEvents`). A call marked by `leafVT`
    is a variable-time leaf, whose event is its argument bytes (the default of
    `vtEvents`), or a linked callee, whose events are the trace of its lowered run; an
    unmarked call has no event. -/
structure LowCTLeakModel where
  regime : DoitRegime
  mnem : SExpr → Option X86Mnem
  leafVT : String → Bool
  vtEvents : String → List (Σ t : TowerType, RustVal t) → List CTLeak :=
    fun f argList => [.vtCall f (argList.map towerBytes)]

/-- The model of the owned x86 route: DOITM, `sexprMnem`, no variable-time
    leaf. -/
def LowCTLeakModel.owned : LowCTLeakModel :=
  { regime := .doitm, mnem := sexprMnem, leafVT := fun _ => false }

/-- The operand event of a binary node `e` with operands `a` and `b`. -/
def nodeLeak (M : LowCTLeakModel) (rs : RustState) (e a b : SExpr) : List CTLeak :=
  match M.mnem e with
  | some m => if M.regime.leaksOperands m then [.vt m [a.evalState rs, b.evalState rs]] else []
  | none => []

/-- The operand events of evaluating a scalar expression in `rs`: the events of
    the operands, then the node's own event. -/
def sexprLeak (M : LowCTLeakModel) (rs : RustState) : SExpr → List CTLeak
  | .SVar _ => []
  | .SLit _ => []
  | .SLimb _ _ => []
  | .SAdd a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SAdd a b) a b
  | .SSub a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SSub a b) a b
  | .SMul a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SMul a b) a b
  | .SShr a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SShr a b) a b
  | .SShl a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SShl a b) a b
  | .SAnd a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SAnd a b) a b
  | .SXor a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SXor a b) a b
  | .SLt a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SLt a b) a b
  | .SAsr a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SAsr a b) a b
  | .SMulS a b => sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SMulS a b) a b
  | .SMulHiU a b =>
      sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SMulHiU a b) a b
  | .SMulHiS a b =>
      sexprLeak M rs a ++ sexprLeak M rs b ++ nodeLeak M rs (.SMulHiS a b) a b

/-- The events of a call: those the model supplies (`vtEvents`) for a call marked by
    `leafVT`, nothing otherwise. -/
def callLeak (M : LowCTLeakModel) (f : String) (argList : List (Σ t : TowerType, RustVal t)) :
    List CTLeak :=
  if M.leafVT f then M.vtEvents f argList else []

/-! ## 2. The traced semantics -/

/-- `RustExec` with a leakage trace. Each constructor is the `RustExec`
    constructor of the same name with the trace of the step added. -/
inductive RustExecLeak (N : Nat) (leafSpec : LeafSpec) (M : LowCTLeakModel) :
    LowCT → RustState → List CTLeak → RustState → Prop where
  | skip : ∀ rs, RustExecLeak N leafSpec M .RSkip rs [] rs
  | seq : ∀ c1 c2 rs r1 rs' t1 t2,
      RustExecLeak N leafSpec M c1 rs t1 r1 →
      RustExecLeak N leafSpec M c2 r1 t2 rs' →
      RustExecLeak N leafSpec M (.RSeq c1 c2) rs (t1 ++ t2) rs'
  | letZero : ∀ x t body rs rs' tr,
      RustExecLeak N leafSpec M body (rsSetTower rs x ⟨t, default⟩) tr rs' →
      RustExecLeak N leafSpec M (.RLetZero x t body) rs tr rs'
  | letU64Zero : ∀ x body rs rs' tr,
      RustExecLeak N leafSpec M body (rsSetScalar rs x 0) tr rs' →
      RustExecLeak N leafSpec M (.RLetU64Zero x body) rs tr rs'
  | scalarSet : ∀ x v rs,
      RustExecLeak N leafSpec M (.RScalarSet x v) rs [] (rsSetScalar rs x v)
  | ifTrue : ∀ e ct cf rs rs' v tr,
      rs.rsScalar e = v → v ≠ 0 →
      RustExecLeak N leafSpec M ct rs tr rs' →
      RustExecLeak N leafSpec M (.RIfNz e ct cf) rs (.branch true :: tr) rs'
  | ifFalse : ∀ e ct cf rs rs' tr,
      rs.rsScalar e = 0 →
      RustExecLeak N leafSpec M cf rs tr rs' →
      RustExecLeak N leafSpec M (.RIfNz e ct cf) rs (.branch false :: tr) rs'
  | whileFalse : ∀ e body rs,
      rs.rsScalar e = 0 →
      RustExecLeak N leafSpec M (.RWhileNz e body) rs [.branch false] rs
  | whileTrue : ∀ e body rs r1 rs' v t1 t2,
      rs.rsScalar e = v → v ≠ 0 →
      RustExecLeak N leafSpec M body rs t1 r1 →
      RustExecLeak N leafSpec M (.RWhileNz e body) r1 t2 rs' →
      RustExecLeak N leafSpec M (.RWhileNz e body) rs (.branch true :: (t1 ++ t2)) rs'
  | forZero : ∀ x body rs,
      RustExecLeak N leafSpec M (.RFor x 0 body) rs [] rs
  | forSucc : ∀ x n body rs r1 rs' t1 t2,
      RustExecLeak N leafSpec M (.RFor x n body) rs t1 r1 →
      RustExecLeak N leafSpec M body (rsSetScalar r1 x n) t2 rs' →
      RustExecLeak N leafSpec M (.RFor x (n+1) body) rs (t1 ++ t2) rs'
  | forRuntime : ∀ x bound body rs rs' tr,
      RustExecLeak N leafSpec M (.RFor x (bound.evalState rs) body) rs tr rs' →
      RustExecLeak N leafSpec M (.RForRuntime x bound body) rs
        (sexprLeak M rs bound ++ .trip (bound.evalState rs) :: tr) rs'
  | call : ∀ f dest args rs oldDestV argList,
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExecLeak N leafSpec M (.RCall f dest args) rs (callLeak M f argList)
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  | cloneCall : ∀ cloneVar cloneTy oldDest innerF dest args rs rsClone rs' tr,
      rsClone = rsSetTower rs cloneVar
                  (rs.rsTower oldDest.locVar |>.getD ⟨cloneTy, default⟩) →
      RustExecLeak N leafSpec M (.RCall innerF dest args) rsClone tr rs' →
      RustExecLeak N leafSpec M (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
        rs tr rs'
  | callSwap : ∀ f dest1 dest2 args rs rs1 rs' t1 t2,
      RustExecLeak N leafSpec M (.RCall f dest1 args) rs t1 rs1 →
      RustExecLeak N leafSpec M (.RCall f dest2 args) rs1 t2 rs' →
      RustExecLeak N leafSpec M (.RCallSwap f dest1 dest2 args) rs (t1 ++ t2) rs'
  | limbStore : ∀ loc idx v rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExecLeak N leafSpec M (.RLimbStore loc idx v) rs []
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  | limbStoreExpr : ∀ loc idx e rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExecLeak N leafSpec M (.RLimbStoreExpr loc idx e) rs (sexprLeak M rs e)
        (locatedUpdate rs loc
          (leafSpec.limbStore loc oldDestV idx (BitVec.ofNat 64 (e.evalState rs))))
  | callN : ∀ f dests args rs argList,
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      RustExecLeak N leafSpec M (.RCallN f dests args) rs (callLeak M f argList)
        (callNUpdate leafSpec f (args.map (·.locDst)) argList 0 dests rs)
  | selectFalse : ∀ dst sel src0 src1 rs (h : src0.locDst = dst.locDst) srcV,
      rs.rsScalar sel = 0 →
      locatedLookup rs src0 = some srcV →
      RustExecLeak N leafSpec M (.RSelect dst sel src0 src1) rs []
        (locatedUpdate rs dst (h ▸ srcV))
  | selectTrue : ∀ dst sel src0 src1 rs (h : src1.locDst = dst.locDst) v srcV,
      rs.rsScalar sel = v → v ≠ 0 →
      locatedLookup rs src1 = some srcV →
      RustExecLeak N leafSpec M (.RSelect dst sel src0 src1) rs []
        (locatedUpdate rs dst (h ▸ srcV))
  | assert : ∀ label rs, RustExecLeak N leafSpec M (.RAssert label) rs [] rs
  | block : ∀ body rs rs' tr,
      RustExecLeak N leafSpec M body rs tr rs' →
      RustExecLeak N leafSpec M (.RBlock body) rs tr rs'
  | tupleLoad : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExecLeak N leafSpec M (.RTupleLoad dst src idx) rs []
        (locatedUpdate rs dst (leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  | arrStore : ∀ arr idxVar src rs (idx : Nat) oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExecLeak N leafSpec M (.RArrStore arr idxVar src) rs [.addr arr.locVar idx]
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  | arrLoad : ∀ dst src idxVar rs (idx : Nat) oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExecLeak N leafSpec M (.RArrLoad dst src idxVar) rs [.addr src.locVar idx]
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  | arrStoreLit : ∀ arr idx src rs oldV srcV,
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExecLeak N leafSpec M (.RArrStoreLit arr idx src) rs [.addr arr.locVar idx]
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  | arrLoadLit : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExecLeak N leafSpec M (.RArrLoadLit dst src idx) rs [.addr src.locVar idx]
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  | scalarSetExpr : ∀ x e rs,
      RustExecLeak N leafSpec M (.RScalarSetExpr x e) rs (sexprLeak M rs e)
        (rsSetScalar rs x (e.evalState rs))
  | callDstThreaded : ∀ f dst args rs oldDestV argList,
      locatedLookup rs dst = some oldDestV →
      argList = (dst :: args).filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ dst :: args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExecLeak N leafSpec M (.RCallDstThreaded f dst args) rs (callLeak M f argList)
        (locatedUpdate rs dst
          (leafSpec.call f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList))
  | copy : ∀ dst src rs (h : src.locDst = dst.locDst) srcV,
      locatedLookup rs src = some srcV →
      RustExecLeak N leafSpec M (.RCopy dst src) rs [] (locatedUpdate rs dst (h ▸ srcV))

/-- Erasing the trace of a traced run gives a `RustExec` run. -/
theorem RustExecLeak.toRustExec {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {c : LowCT} {rs rs' : RustState} {t : List CTLeak}
    (h : RustExecLeak N leafSpec M c rs t rs') : RustExec N leafSpec c rs rs' := by
  induction h with
  | skip rs => exact .skip rs
  | seq c1 c2 rs r1 rs' _ _ _ _ ih1 ih2 => exact .seq c1 c2 rs r1 rs' ih1 ih2
  | letZero x t body rs rs' _ _ ih => exact .letZero x t body rs rs' ih
  | letU64Zero x body rs rs' _ _ ih => exact .letU64Zero x body rs rs' ih
  | scalarSet x v rs => exact .scalarSet x v rs
  | ifTrue e ct cf rs rs' v _ hv hv0 _ ih => exact .ifTrue e ct cf rs rs' v hv hv0 ih
  | ifFalse e ct cf rs rs' _ hv _ ih => exact .ifFalse e ct cf rs rs' hv ih
  | whileFalse e body rs hv => exact .whileFalse e body rs hv
  | whileTrue e body rs r1 rs' v _ _ hv hv0 _ _ ih1 ih2 =>
    exact .whileTrue e body rs r1 rs' v hv hv0 ih1 ih2
  | forZero x body rs => exact .forZero x body rs
  | forSucc x n body rs r1 rs' _ _ _ _ ih1 ih2 => exact .forSucc x n body rs r1 rs' ih1 ih2
  | forRuntime x bound body rs rs' _ _ ih => exact .forRuntime x bound body rs rs' ih
  | call f dest args rs oldDestV argList h1 h2 h3 =>
    exact .call f dest args rs oldDestV argList h1 h2 h3
  | cloneCall cloneVar cloneTy oldDest innerF dest args rs rsClone rs' _ h1 _ ih =>
    exact .cloneCall cloneVar cloneTy oldDest innerF dest args rs rsClone rs' h1 ih
  | callSwap f dest1 dest2 args rs rs1 rs' _ _ _ _ ih1 ih2 =>
    exact .callSwap f dest1 dest2 args rs rs1 rs' ih1 ih2
  | limbStore loc idx v rs oldDestV h1 => exact .limbStore loc idx v rs oldDestV h1
  | limbStoreExpr loc idx e rs oldDestV h1 => exact .limbStoreExpr loc idx e rs oldDestV h1
  | callN f dests args rs argList h1 h2 h3 => exact .callN f dests args rs argList h1 h2 h3
  | selectFalse dst sel src0 src1 rs h srcV h1 h2 =>
    exact .selectFalse dst sel src0 src1 rs h srcV h1 h2
  | selectTrue dst sel src0 src1 rs h v srcV h1 h2 h3 =>
    exact .selectTrue dst sel src0 src1 rs h v srcV h1 h2 h3
  | assert label rs => exact .assert label rs
  | block body rs rs' _ _ ih => exact .block body rs rs' ih
  | tupleLoad dst src idx rs oldV srcV h1 h2 => exact .tupleLoad dst src idx rs oldV srcV h1 h2
  | arrStore arr idxVar src rs idx oldV srcV h1 h2 h3 =>
    exact .arrStore arr idxVar src rs idx oldV srcV h1 h2 h3
  | arrLoad dst src idxVar rs idx oldV srcV h1 h2 h3 =>
    exact .arrLoad dst src idxVar rs idx oldV srcV h1 h2 h3
  | arrStoreLit arr idx src rs oldV srcV h1 h2 => exact .arrStoreLit arr idx src rs oldV srcV h1 h2
  | arrLoadLit dst src idx rs oldV srcV h1 h2 => exact .arrLoadLit dst src idx rs oldV srcV h1 h2
  | scalarSetExpr x e rs => exact .scalarSetExpr x e rs
  | callDstThreaded f dst args rs oldDestV argList h1 h2 h3 =>
    exact .callDstThreaded f dst args rs oldDestV argList h1 h2 h3
  | copy dst src rs h srcV h1 => exact .copy dst src rs h srcV h1

/-- Every `RustExec` run has a leakage trace. -/
theorem RustExec.exists_leak {N : Nat} {leafSpec : LeafSpec} (M : LowCTLeakModel)
    {c : LowCT} {rs rs' : RustState} (h : RustExec N leafSpec c rs rs') :
    ∃ t, RustExecLeak N leafSpec M c rs t rs' := by
  induction h with
  | skip rs => exact ⟨_, .skip rs⟩
  | seq c1 c2 rs r1 rs' _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1; obtain ⟨_, h2⟩ := ih2
    exact ⟨_, .seq c1 c2 rs r1 rs' _ _ h1 h2⟩
  | letZero x t body rs rs' _ ih =>
    obtain ⟨_, h1⟩ := ih; exact ⟨_, .letZero x t body rs rs' _ h1⟩
  | letU64Zero x body rs rs' _ ih =>
    obtain ⟨_, h1⟩ := ih; exact ⟨_, .letU64Zero x body rs rs' _ h1⟩
  | scalarSet x v rs => exact ⟨_, .scalarSet x v rs⟩
  | ifTrue e ct cf rs rs' v hv hv0 _ ih =>
    obtain ⟨_, h1⟩ := ih; exact ⟨_, .ifTrue e ct cf rs rs' v _ hv hv0 h1⟩
  | ifFalse e ct cf rs rs' hv _ ih =>
    obtain ⟨_, h1⟩ := ih; exact ⟨_, .ifFalse e ct cf rs rs' _ hv h1⟩
  | whileFalse e body rs hv => exact ⟨_, .whileFalse e body rs hv⟩
  | whileTrue e body rs r1 rs' v hv hv0 _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1; obtain ⟨_, h2⟩ := ih2
    exact ⟨_, .whileTrue e body rs r1 rs' v _ _ hv hv0 h1 h2⟩
  | forZero x body rs => exact ⟨_, .forZero x body rs⟩
  | forSucc x n body rs r1 rs' _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1; obtain ⟨_, h2⟩ := ih2
    exact ⟨_, .forSucc x n body rs r1 rs' _ _ h1 h2⟩
  | forRuntime x bound body rs rs' _ ih =>
    obtain ⟨_, h1⟩ := ih; exact ⟨_, .forRuntime x bound body rs rs' _ h1⟩
  | call f dest args rs oldDestV argList h1 h2 h3 =>
    exact ⟨_, .call f dest args rs oldDestV argList h1 h2 h3⟩
  | cloneCall cloneVar cloneTy oldDest innerF dest args rs rsClone rs' h1 _ ih =>
    obtain ⟨_, h2⟩ := ih
    exact ⟨_, .cloneCall cloneVar cloneTy oldDest innerF dest args rs rsClone rs' _ h1 h2⟩
  | callSwap f dest1 dest2 args rs rs1 rs' _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1; obtain ⟨_, h2⟩ := ih2
    exact ⟨_, .callSwap f dest1 dest2 args rs rs1 rs' _ _ h1 h2⟩
  | limbStore loc idx v rs oldDestV h1 => exact ⟨_, .limbStore loc idx v rs oldDestV h1⟩
  | limbStoreExpr loc idx e rs oldDestV h1 =>
    exact ⟨_, .limbStoreExpr loc idx e rs oldDestV h1⟩
  | callN f dests args rs argList h1 h2 h3 => exact ⟨_, .callN f dests args rs argList h1 h2 h3⟩
  | selectFalse dst sel src0 src1 rs h srcV h1 h2 =>
    exact ⟨_, .selectFalse dst sel src0 src1 rs h srcV h1 h2⟩
  | selectTrue dst sel src0 src1 rs h v srcV h1 h2 h3 =>
    exact ⟨_, .selectTrue dst sel src0 src1 rs h v srcV h1 h2 h3⟩
  | assert label rs => exact ⟨_, .assert label rs⟩
  | block body rs rs' _ ih => obtain ⟨_, h1⟩ := ih; exact ⟨_, .block body rs rs' _ h1⟩
  | tupleLoad dst src idx rs oldV srcV h1 h2 => exact ⟨_, .tupleLoad dst src idx rs oldV srcV h1 h2⟩
  | arrStore arr idxVar src rs idx oldV srcV h1 h2 h3 =>
    exact ⟨_, .arrStore arr idxVar src rs idx oldV srcV h1 h2 h3⟩
  | arrLoad dst src idxVar rs idx oldV srcV h1 h2 h3 =>
    exact ⟨_, .arrLoad dst src idxVar rs idx oldV srcV h1 h2 h3⟩
  | arrStoreLit arr idx src rs oldV srcV h1 h2 =>
    exact ⟨_, .arrStoreLit arr idx src rs oldV srcV h1 h2⟩
  | arrLoadLit dst src idx rs oldV srcV h1 h2 =>
    exact ⟨_, .arrLoadLit dst src idx rs oldV srcV h1 h2⟩
  | scalarSetExpr x e rs => exact ⟨_, .scalarSetExpr x e rs⟩
  | callDstThreaded f dst args rs oldDestV argList h1 h2 h3 =>
    exact ⟨_, .callDstThreaded f dst args rs oldDestV argList h1 h2 h3⟩
  | copy dst src rs h srcV h1 => exact ⟨_, .copy dst src rs h srcV h1⟩

/-! ## 3. Constant time at `LowCT` -/

/-- Two states agree on the public slots of `lt`: equal scalar and tower values
    at every public name. -/
def PubEqRS (lt : LevelTable) (rs₁ rs₂ : RustState) : Prop :=
  ∀ x, lt x = .Public → rs₁.rsScalar x = rs₂.rsScalar x ∧ rs₁.rsTower x = rs₂.rsTower x

/-- Constant time of a `LowCT` program for the split `lt`: two terminating runs
    from states that agree on the public slots have equal leakage traces. -/
def LowCTConstantTime (N : Nat) (leafSpec : LeafSpec) (M : LowCTLeakModel) (lt : LevelTable)
    (c : LowCT) : Prop :=
  ConstantTimeRel (PubEqRS lt) (fun rs t => ∃ rs', RustExecLeak N leafSpec M c rs t rs')

theorem skip_ct (N : Nat) (leafSpec : LeafSpec) (M : LowCTLeakModel) (lt : LevelTable) :
    LowCTConstantTime N leafSpec M lt .RSkip := by
  rintro rs₁ rs₂ t₁ t₂ - ⟨_, h₁⟩ ⟨_, h₂⟩
  cases h₁; cases h₂; rfl

/-- A conditional on a public guard whose arms are constant time is constant
    time. -/
theorem ifNz_ct_of_public {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {lt : LevelTable} {e : String} {ct cf : LowCT} (he : lt e = .Public)
    (hct : LowCTConstantTime N leafSpec M lt ct) (hcf : LowCTConstantTime N leafSpec M lt cf) :
    LowCTConstantTime N leafSpec M lt (.RIfNz e ct cf) := by
  rintro rs₁ rs₂ t₁ t₂ hp ⟨_, h₁⟩ ⟨_, h₂⟩
  have hg := (hp e he).1
  cases h₁ with
  | ifTrue _ _ _ _ _ v₁ tr₁ hv₁ hv₁0 hb₁ =>
    cases h₂ with
    | ifTrue _ _ _ _ _ v₂ tr₂ hv₂ hv₂0 hb₂ =>
      rw [hct rs₁ rs₂ tr₁ tr₂ hp ⟨_, hb₁⟩ ⟨_, hb₂⟩]
    | ifFalse _ _ _ _ _ tr₂ hv₂ hb₂ => exact absurd (hv₁ ▸ hg.trans hv₂) hv₁0
  | ifFalse _ _ _ _ _ tr₁ hv₁ hb₁ =>
    cases h₂ with
    | ifTrue _ _ _ _ _ v₂ tr₂ hv₂ hv₂0 hb₂ =>
      exact absurd (hv₂ ▸ hg.symm.trans hv₁) hv₂0
    | ifFalse _ _ _ _ _ tr₂ hv₂ hb₂ =>
      rw [hcf rs₁ rs₂ tr₁ tr₂ hp ⟨_, hb₁⟩ ⟨_, hb₂⟩]

/-! ### 3.1 Counterexamples -/

/-- The split in which the scalar `k` is secret and every other slot public. -/
def kSecret : LevelTable := fun x => if x = "k" then .Secret else .Public

/-- The default state with the scalar `x` set to `v`. -/
def scalarState (x : String) (v : Nat) : RustState := rsSetScalar default x v

theorem kSecret_pubEq (x : String) (hx : x = "k") (v₁ v₂ : Nat) :
    PubEqRS kSecret (scalarState x v₁) (scalarState x v₂) := by
  intro y hy
  have hyk : y ≠ "k" := by rintro rfl; simp [kSecret] at hy
  subst hx
  simp [scalarState, rsSetScalar, hyk]

/-- A conditional on a secret guard is not constant time. -/
theorem secretGuard_not_ct (N : Nat) (leafSpec : LeafSpec) (M : LowCTLeakModel) :
    ¬ LowCTConstantTime N leafSpec M kSecret (.RIfNz "k" .RSkip .RSkip) := by
  intro h
  have := h (scalarState "k" 0) (scalarState "k" 1) _ _ (kSecret_pubEq "k" rfl 0 1)
    ⟨_, .ifFalse _ _ _ _ _ _ (by simp [scalarState, rsSetScalar]) (.skip _)⟩
    ⟨_, .ifTrue _ _ _ _ _ 1 _ (by simp [scalarState, rsSetScalar]) (by decide) (.skip _)⟩
  simp at this

/-- An arithmetic shift by a secret count is not constant time in the owned
    model: it is a `SARX`, which the allowlist classes variable time. -/
theorem secretSarx_not_ct (N : Nat) (leafSpec : LeafSpec) :
    ¬ LowCTConstantTime N leafSpec .owned kSecret
      (.RScalarSetExpr "y" (.SAsr (.SVar "a") (.SVar "k"))) := by
  intro h
  have := h (scalarState "k" 0) (scalarState "k" 1) _ _ (kSecret_pubEq "k" rfl 0 1)
    ⟨_, .scalarSetExpr _ _ _⟩ ⟨_, .scalarSetExpr _ _ _⟩
  simp [sexprLeak, nodeLeak, LowCTLeakModel.owned, sexprMnem, DoitRegime.leaksOperands,
    X86Mnem.timing, SExpr.evalState, scalarState, rsSetScalar] at this

/-- An arithmetic shift of a secret value by a literal count is constant time
    in the owned model: it is a `SAR` by an immediate. -/
theorem secretSarImm_ct (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable) :
    LowCTConstantTime N leafSpec .owned lt
      (.RScalarSetExpr "y" (.SAsr (.SVar "k") (.SLit 32))) := by
  rintro rs₁ rs₂ t₁ t₂ - ⟨_, h₁⟩ ⟨_, h₂⟩
  cases h₁; cases h₂
  simp [sexprLeak, nodeLeak, LowCTLeakModel.owned, sexprMnem, DoitRegime.leaksOperands,
    X86Mnem.timing]

/-- A loop with a secret runtime bound is not constant time: the trip count is
    observable. -/
theorem secretBound_not_ct (N : Nat) (leafSpec : LeafSpec) (M : LowCTLeakModel) :
    ¬ LowCTConstantTime N leafSpec M kSecret (.RForRuntime "i" (.SVar "k") .RSkip) := by
  intro h
  have h0 : (SExpr.SVar "k").evalState (scalarState "k" 0) = 0 := by
    simp [SExpr.evalState, scalarState, rsSetScalar]
  have h1 : (SExpr.SVar "k").evalState (scalarState "k" 1) = 1 := by
    simp [SExpr.evalState, scalarState, rsSetScalar]
  have r0 : RustExecLeak N leafSpec M (.RFor "i" ((SExpr.SVar "k").evalState (scalarState "k" 0))
      .RSkip) (scalarState "k" 0) [] (scalarState "k" 0) := by
    rw [h0]; exact .forZero _ _ _
  have r1 : RustExecLeak N leafSpec M (.RFor "i" ((SExpr.SVar "k").evalState (scalarState "k" 1))
      .RSkip) (scalarState "k" 1) [] (rsSetScalar (scalarState "k" 1) "i" 0) := by
    rw [h1]; exact .forSucc _ 0 _ _ _ _ [] [] (.forZero _ _ _) (.skip _)
  have := h (scalarState "k" 0) (scalarState "k" 1) _ _ (kSecret_pubEq "k" rfl 0 1)
    ⟨_, .forRuntime _ _ _ _ _ _ r0⟩ ⟨_, .forRuntime _ _ _ _ _ _ r1⟩
  simp [sexprLeak, h0, h1] at this

end CatCrypt.Crypto.SecureCompilation.CT
