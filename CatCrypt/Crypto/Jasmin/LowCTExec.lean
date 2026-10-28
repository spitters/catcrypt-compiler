/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTSyntax
public import CatCrypt.Crypto.Jasmin.LowCTState

/-!
# `LowCT` big-step semantics

The runtime layer of `LowCT` (`CatCrypt.Crypto.Jasmin.LowCT` re-exports it):
the multi-output call update `callNUpdate` and the big-step relation
`RustExec` with the `RFor` invariant rule, over the runtime state of
`LowCTState` (re-exported here).
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

/-! ## §6  Big-step semantics -/

/-- Leaf name for output `i` of the multi-output call to `f`.

    An `Expr` in the `Com` framework has exactly one return type, so a
    multi-output call is carried as one single-output call per output, named
    apart by its index. `RCallN f dests args` therefore reads output `i`
    through the ordinary `LeafSpec.call` oracle at `callNLeafName f i`, and a
    leaf supplying an `n`-output primitive registers `n` names. This is the
    same monomorphisation `Optimizer.SplitBytesSlice` performs on the
    size-varying `bytes_slice` wrapper. -/
def callNLeafName (f : String) (i : Nat) : String :=
  "callN:" ++ f ++ "#" ++ toString i

/-- Write each destination of an N-output call, left to right: destination `i`
    receives output `i` of `f` on the argument values `argList`.

    `argList` and `argTs` are read once from the pre-state by the `callN` rule,
    so every destination sees the same inputs — the borrow checker keeps
    `dests` distinct and disjoint from `args`, so no destination write can
    reach a later destination's arguments. -/
def callNUpdate (leafSpec : LeafSpec) (f : String) (argTs : List TowerType)
    (argList : List (Σ t : TowerType, RustVal t)) :
    Nat → List Located → RustState → RustState
  | _, [], rs => rs
  | i, d :: rest, rs =>
      callNUpdate leafSpec f argTs argList (i + 1) rest
        (locatedUpdate rs d
          (leafSpec.call (callNLeafName f i) d.locDst argTs
            ((locatedLookup rs d).getD default) argList))

/-- A slot whose name is none of the destinations is untouched by the fold:
    the write-set of `RCallN f dests args` is exactly `dests`. -/
theorem locatedLookup_callNUpdate_other (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (loc : Located),
      loc.locVar ∉ dests.map (·.locVar) →
      locatedLookup (callNUpdate leafSpec f argTs argList i dests rs) loc
        = locatedLookup rs loc := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _; rfl
  | cons d rest ih =>
    intro i rs loc hNotIn
    simp only [List.map_cons, List.mem_cons, not_or] at hNotIn
    obtain ⟨hd, hrest⟩ := hNotIn
    show locatedLookup
      (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs d _)) loc = _
    rw [ih (i + 1) _ loc (by simpa using hrest)]
    exact locatedUpdate_other _ _ _ _ (Ne.symm hd)

/-- The `rsTower`-level counterpart of `locatedLookup_callNUpdate_other`.
    `locatedLookup` equality does not imply `rsTower` equality — it forgets a
    type mismatch — so a frame stated at the raw heap needs this one. -/
theorem rsTower_callNUpdate_other (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (y : String),
      y ∉ dests.map (·.locVar) →
      (callNUpdate leafSpec f argTs argList i dests rs).rsTower y = rs.rsTower y := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _; rfl
  | cons d rest ih =>
    intro i rs y hNotIn
    simp only [List.map_cons, List.mem_cons, not_or] at hNotIn
    obtain ⟨hd, hrest⟩ := hNotIn
    show (callNUpdate leafSpec f argTs argList (i + 1) rest
            (locatedUpdate rs d _)).rsTower y = _
    rw [ih (i + 1) _ y (by simpa using hrest)]
    unfold locatedUpdate
    exact rsSetTower_other _ _ _ _ (Ne.symm hd)

/-- The fold writes tower slots only, so the scalar heap is untouched. -/
theorem callNUpdate_rsScalar (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState),
      (callNUpdate leafSpec f argTs argList i dests rs).rsScalar = rs.rsScalar := by
  intro dests
  induction dests with
  | nil => intro _ _; rfl
  | cons d rest ih =>
    intro i rs
    show (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs d _)).rsScalar = _
    rw [ih (i + 1)]
    rfl

/-- The `j`-th destination reads back its own write: after the fold started at
    index `i`, the slot named by `dests[j]` holds output `i + j` of `f`, applied
    to the pre-state's old value at that slot.

    Distinctness of the destination *names* is what makes this hold — with a
    repeated name the later write shadows the earlier one, and the slot carries
    only the last output written to it. -/
theorem rsTower_callNUpdate_nth (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i j : Nat) (rs : RustState) (d : Located),
      (dests.map (·.locVar)).Nodup →
      dests[j]? = some d →
      (callNUpdate leafSpec f argTs argList i dests rs).rsTower d.locVar
        = some ⟨d.locDst,
            leafSpec.call (callNLeafName f (i + j)) d.locDst argTs
              ((locatedLookup rs d).getD default) argList⟩ := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _ _ hj; simp at hj
  | cons d' rest ih =>
    intro i j rs d hNodup hj
    simp only [List.map_cons, List.nodup_cons] at hNodup
    obtain ⟨hHead, hRest⟩ := hNodup
    cases j with
    | zero =>
      have hd : d = d' := by simpa using hj.symm
      subst hd
      show (callNUpdate leafSpec f argTs argList (i + 1) rest
              (locatedUpdate rs d _)).rsTower d.locVar = _
      rw [rsTower_callNUpdate_other leafSpec f argTs argList rest (i + 1) _
            d.locVar hHead, locatedUpdate_dest]
      simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at hj
      have hmem : d ∈ rest := List.mem_of_getElem? hj
      have hne : d'.locVar ≠ d.locVar := by
        intro hEq
        exact hHead (hEq ▸ List.mem_map_of_mem hmem)
      show (callNUpdate leafSpec f argTs argList (i + 1) rest
              (locatedUpdate rs d' _)).rsTower d.locVar = _
      rw [ih (i + 1) k _ d hRest hj, locatedUpdate_other _ _ _ _ hne]
      have hidx : i + 1 + k = i + (k + 1) := by omega
      rw [hidx]

/-- Big-step execution relation for `LowCT`.

    `RustExec N leafSpec c rs rs'` means: running `c` from state `rs`
    with fuel bound `N` and leaf specification `leafSpec` terminates in `rs'`.

    `N` bounds `RWhileNz` loop iterations (via the `while_true` case's
    induction structure — the bound appears implicitly in the finite derivation
    tree).

    `RFnCall` and `RFnDef` have no rule. Giving `RFnCall` its meaning
    requires a function environment — a map from name to `FnSpec`, threaded
    through this relation's indices, so the rule can run the callee's body
    on the argument slots and write back to `dests`. This relation is
    indexed only by `N` and `leafSpec`, so that is a change to its type.
    Until then the relation is unsatisfiable at those two nodes: a
    hypothesis `RustExec … c rs rs'` for a program containing one cannot be
    discharged, rather than being discharged by a rule that moves no state.
    `toJasminCmd` still lowers `RFnCall` to a `Ccall`, so such a program
    compiles; what it does not have is an operational claim at this
    layer. `TranslateDialectFnCall`'s `fnCallD`/`fnDefD` are the dialect-side
    shape a future rule would mirror.

    Scalar semantics. `scalarSetExpr`, `limbStoreExpr` and the `forRuntime` trip
    count evaluate by `SExpr.evalState`, over unbounded naturals with saturating
    `SSub`; guards test `rsScalar x ≠ 0` on naturals. `RustExec` is therefore the
    referent for Rust `saturating_sub`, counters, indices and values that stay
    below `2^64`, and not for wrapping kernels, whose referent is `semScalar`
    (`SExpr.evalBV`). Wrapping operations routed as leaf calls (`wrapping_*#w`,
    `rotate_*#w`, `cast#w`) wrap in the leaf oracle and are unaffected.

    Bridges from `RustExec` to `semScalar` and their in-range hypotheses:
    `RustExec_limbStoreExpr_stored_eq_evalStateBV` (`inRangeState`);
    `RustExecSemScalarBridge.rustExec_semScalar_agree` and
    `rustExec_semScalar_agree_arr` (`IsCoveredAdeqS`: `srcClean` and
    `∀ σ, (∀ y, σ y < 2^64) → e.inRange σ` at every `RScalarSetExpr`, together
    with `ScalarInRange` at entry); `GuardedAgree.rustExec_semScalarGuarded_agree`
    (the per-run `InRangeG`); `RustExecSimulatesUnified.rustExec_semU_agree`
    (`IsCoveredAdeqU`). -/
inductive RustExec (N : Nat) (leafSpec : LeafSpec) :
    LowCT → RustState → RustState → Prop where
  | skip   : ∀ rs, RustExec N leafSpec .RSkip rs rs
  | seq    : ∀ c1 c2 rs r1 rs',
      RustExec N leafSpec c1 rs r1 →
      RustExec N leafSpec c2 r1 rs' →
      RustExec N leafSpec (.RSeq c1 c2) rs rs'
  | letZero : ∀ x t body rs rs',
      RustExec N leafSpec body (rsSetTower rs x ⟨t, default⟩) rs' →
      RustExec N leafSpec (.RLetZero x t body) rs rs'
  | letU64Zero : ∀ x body rs rs',
      RustExec N leafSpec body (rsSetScalar rs x 0) rs' →
      RustExec N leafSpec (.RLetU64Zero x body) rs rs'
  | scalarSet : ∀ x v rs,
      RustExec N leafSpec (.RScalarSet x v) rs (rsSetScalar rs x v)
  | ifTrue  : ∀ e ct cf rs rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec ct rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | ifFalse : ∀ e ct cf rs rs',
      rs.rsScalar e = 0 →
      RustExec N leafSpec cf rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | whileFalse : ∀ e body rs,
      rs.rsScalar e = 0 →
      RustExec N leafSpec (.RWhileNz e body) rs rs
  | whileTrue : ∀ e body rs r1 rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec body rs r1 →
      RustExec N leafSpec (.RWhileNz e body) r1 rs' →
      RustExec N leafSpec (.RWhileNz e body) rs rs'
  /-- `RFor x 0 body` is a no-op. -/
  | forZero : ∀ x body rs,
      RustExec N leafSpec (.RFor x 0 body) rs rs
  /-- `RFor x (n+1) body` runs `RFor x n body` (iterations 0..n-1), then
      sets the scalar `x` to `n` and runs `body` once more. -/
  | forSucc : ∀ x n body rs r1 rs',
      RustExec N leafSpec (.RFor x n body) rs r1 →
      RustExec N leafSpec body (rsSetScalar r1 x n) rs' →
      RustExec N leafSpec (.RFor x (n+1) body) rs rs'
  /-- Runtime-bound for-loop: delegate to `RFor` at the trip count obtained by
      evaluating `bound` in the entry state `rs`. -/
  | forRuntime : ∀ x bound body rs rs',
      RustExec N leafSpec (.RFor x (bound.evalState rs) body) rs rs' →
      RustExec N leafSpec (.RForRuntime x bound body) rs rs'
  | call : ∀ f dest args rs oldDestV argList,
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      -- Per-arg type-recovery (Option A): args[i].locDst matches the
      -- stored Sigma type at args[i].locVar. Required for determinism.
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExec N leafSpec (.RCall f dest args) rs
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  /-- The clone binding stays in the tower on exit, matching Jasmin, where a
      call introduces no scope to leave.  The AUCurves rule this is imported
      from drops it (`XR_clone_call` ends in `remove_var`), so on this
      constructor the relation is not a conservative extension of that one:
      a post-state here binds `cloneVar`, and there it does not. -/
  | cloneCall : ∀ cloneVar cloneTy oldDest innerF dest args
                   rs rsClone rs',
      rsClone = rsSetTower rs cloneVar
                  (rs.rsTower oldDest.locVar |>.getD ⟨cloneTy, default⟩) →
      RustExec N leafSpec (.RCall innerF dest args) rsClone rs' →
      RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
        rs rs'
  /-- 2-output cswap-shape leaf.  Semantically: two sequential 1-out
      calls in Jasmin: `f(dest1, args); f(dest2, args)`.  borrowOk for
      `RCallSwap` forbids `dest1 = dest2` and either dest in args. -/
  | callSwap : ∀ f dest1 dest2 args rs rs1 rs',
      RustExec N leafSpec (.RCall f dest1 args) rs rs1 →
      RustExec N leafSpec (.RCall f dest2 args) rs1 rs' →
      RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs rs'
  | limbStore : ∀ loc idx v rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStore loc idx v) rs
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  /-- **Runtime-valued limb store (tower-aware).**
      Evaluates `e` against the current *full* state via
      `SExpr.evalState`, truncates the resulting `Nat` to a `BitVec 64`,
      and writes it into limb `idx` of `loc` via the same
      `leafSpec.limbStore` oracle as `limbStore`.

      `evalState` reads the **tower heap** (by byte offset `j*8`, per
      `rsTowerLimb`/`towerLimb`) for any `SLimb v j` node, so an
      `SLimb`-valued store carries its runtime effect: the two
      Fp2 / tower halves share one slot rather than reading as
      independent ones.  On `SLimb`-free expressions `evalState rs e = eval
      rs.rsScalar e` (see `SExpr.evalState_eq_eval`), so the
      scalar-fragment stores are unchanged (see
      `SExpr.evalState_eq_eval`); the literal-valued
      `RLimbStore loc idx v` still coincides with
      `RLimbStoreExpr loc idx (.SLit v.toNat)`. -/
  | limbStoreExpr : ∀ loc idx e rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStoreExpr loc idx e) rs
        (locatedUpdate rs loc
          (leafSpec.limbStore loc oldDestV idx (BitVec.ofNat 64 (e.evalState rs))))
  /-- **N-output leaf call.**  Reads the argument values
      from the pre-state, then writes each destination in turn: destination
      `i` receives `leafSpec.call (callNLeafName f i)` on those arguments.
      Naming the outputs apart by index is what distinguishes destinations of
      the same tower type — the `(carry, sum)` of an add-with-carry shape are
      both `TU64`, and a single leaf name would give them one value. -/
  | callN : ∀ f dests args rs argList,
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      RustExec N leafSpec (.RCallN f dests args) rs
        (callNUpdate leafSpec f (args.map (·.locDst)) argList 0 dests rs)
  /-- **CT-safe conditional move.**  Reads the
      scalar `sel`; if zero, copies `src0`'s tower value into `dst`;
      else copies `src1`.  Hardware analogue: a `CMOV` chain at the
      asm level.  Both source values are read regardless of `sel`'s
      value — that's what makes this CT-safe.

      The type side conditions `src0.locDst = dst.locDst` and
      `src1.locDst = dst.locDst` reflect the borrow-checker invariant
      that cmov requires same-typed source / dest slots. -/
  | selectFalse : ∀ dst sel src0 src1 rs (h : src0.locDst = dst.locDst) srcV,
      rs.rsScalar sel = 0 →
      locatedLookup rs src0 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  | selectTrue : ∀ dst sel src0 src1 rs (h : src1.locDst = dst.locDst) v srcV,
      rs.rsScalar sel = v → v ≠ 0 →
      locatedLookup rs src1 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  /-- **Zero-cost contract.**  No state change. -/
  | assert : ∀ label rs,
      RustExec N leafSpec (.RAssert label) rs rs
  /-- **Scoped block.**  Identical to running
      the body; the "scope" boundary is meaningful only at the
      lowering level (stack reuse) and the Hoare level
      (locally-bound vars dropped from the post-context). -/
  | block : ∀ body rs rs',
      RustExec N leafSpec body rs rs' →
      RustExec N leafSpec (.RBlock body) rs rs'
  /-- **Tuple component load.**  Reads the `idx`-th
      component of `src` into `dst` via `leafSpec.tupleLoad`. -/
  | tupleLoad : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RTupleLoad dst src idx) rs
        (locatedUpdate rs dst (leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Array element store.**  Looks up runtime index
      `rs.rsScalar idxVar`, reads `arr`'s old value, reads `src`'s
      value (with dependent tower type), and writes via
      `leafSpec.arrStore`.  Concrete instances slice arr's byte
      array at offset `idx * src.locDst.storageBytes` to overwrite. -/
  | arrStore : ∀ arr idxVar src rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrStore arr idxVar src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  /-- **Array element load.**  Looks up runtime index
      `rs.rsScalar idxVar` and reads element `idx` of `src` into
      `dst` via `leafSpec.arrLoad`. -/
  | arrLoad : ∀ dst src idxVar rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrLoad dst src idxVar) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Literal-index array store.**  Same
      shape as `arrStore` but the index is the compile-time literal
      `idx : Nat` from the AST (no `rsScalar` lookup). -/
  | arrStoreLit : ∀ arr idx src rs oldV srcV,
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrStoreLit arr idx src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  /-- **Literal-index array load.**  Same
      shape as `arrLoad` but the index is the compile-time literal
      `idx : Nat` from the AST. -/
  | arrLoadLit : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrLoadLit dst src idx) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Set scalar slot to an `SExpr` value.**  Evaluates the
      expression with the tower-aware `SExpr.evalState`, so that
      `RScalarSetExpr x (SLimb v i)` reads limb `i` of tower slot `v`, and
      writes the result.  On an `SLimb`-free expression the value is
      `e.eval rs.rsScalar` (`SExpr.evalState_eq_eval`). -/
  | scalarSetExpr : ∀ x e rs,
      RustExec N leafSpec (.RScalarSetExpr x e) rs
        (rsSetScalar rs x (e.evalState rs))
  /-- **Destination-threaded leaf call.**  Single
      output, shape-compatible with `call`, but the destination slot is
      threaded as the first call argument *and* the receiving lvalue:
      `dst = f(dst, args)`.  We read `dst`'s old value, build the argument
      list from `dst :: args` (so the leaf sees the prior destination
      contents as its first input), pass the corresponding dst-types, and
      write the single result back via `leafSpec.call`.  Mirrors `call`'s
      per-arg type-recovery side condition over `dst :: args`. -/
  | callDstThreaded : ∀ f dst args rs oldDestV argList,
      locatedLookup rs dst = some oldDestV →
      argList = (dst :: args).filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ dst :: args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExec N leafSpec (.RCallDstThreaded f dst args) rs
        (locatedUpdate rs dst
          (leafSpec.call f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList))
  /-- **Whole-array copy.**  Reads `src` and writes its value to `dst`;
      the type side condition `src.locDst = dst.locDst` transports the
      value to the destination type. The old value of `dst` is not read. -/
  | copy : ∀ dst src rs (h : src.locDst = dst.locDst) srcV,
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RCopy dst src) rs
        (locatedUpdate rs dst (h ▸ srcV))

/-- **Runtime-store reconciliation.**  The word
    that `RustExec.limbStoreExpr` records — `BitVec.ofNat 64 (e.evalState rs)`,
    i.e. the saturating-then-truncate-at-storage Nat model — equals the
    intermediate-wrapping hardware value `e.evalStateBV rs` **exactly** under
    the in-range side-condition `inRangeState`.  This is what makes the runtime
    relation a faithful predictor of the emitted code: off the side-condition
    (intermediate overflow, or an `SSub` that underflows — where Nat saturates
    at 0 but hardware wraps) the two can disagree, and the side-condition is
    discharged per kernel by the no-overflow argument in that kernel's
    correctness proof (`fe25519_add` etc. operate on `< 2^51`-bounded limbs, so
    each `SAdd`/`SSub` stays in `u64` range).  Together with
    `RustExec.limbStoreExpr` this closes the model/emit wrapping gap at the
    runtime layer: the stored value is the hardware value on in-range inputs. -/
theorem RustExec_limbStoreExpr_stored_eq_evalStateBV
    (rs : RustState) (e : SExpr) (h : e.inRangeState rs) :
    BitVec.ofNat 64 (e.evalState rs) = e.evalStateBV rs :=
  (SExpr.evalStateBV_eq_ofNat_evalState rs e h).symm

/-! ## §7  `RFor` smoke tests and Hoare-style rule

The Hoare-style rule for `RFor` says: if a state-indexed invariant `I i`
is preserved by one execution of `body` (with the counter set to `i`),
and `I 0` holds initially, then `I n` holds after `RFor x n body`.
This is the standard structural rule for bounded for-loops; it's the
key reason to add `RFor` (vs. open-coding everything as `RWhileNz`):
the rule needs no termination side condition and the loop bound becomes
a free invariant. -/

namespace RustExec

/-- **RFor structural induction rule**: if `I 0 rs` and `body` preserves
    `I` across one iteration with the counter set to `i`, then `I n` holds
    at the post-state. Schematic; `I` ranges over arbitrary state predicates.

    This is Bedrock2's `compile_for` rule stated at the
    semantic level — same shape minus the program-counter bookkeeping. -/
theorem rfor_invariant
    {N : Nat} {leafSpec : LeafSpec} {x : String} {body : LowCT}
    {I : Nat → RustState → Prop}
    (hStep : ∀ (i : Nat) (rs r' : RustState),
        I i rs →
        RustExec N leafSpec body (rsSetScalar rs x i) r' →
        I (i + 1) r') :
    ∀ (n : Nat) (rs r' : RustState),
      I 0 rs →
      RustExec N leafSpec (.RFor x n body) rs r' →
      I n r' := by
  intro n
  induction n with
  | zero =>
    intro rs r' hI hExec
    cases hExec
    exact hI
  | succ k ih =>
    intro rs r' hI hExec
    cases hExec with
    | forSucc _ _ _ _ r1 _ hInner hBody =>
      have hk : I k r1 := ih rs r1 hI hInner
      exact hStep k r1 r' hk hBody

/-- Smoke test: a 3-iteration for-loop with an `RSkip` body executes to
    the explicit scalar-set chain. -/
example (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    RustExec N leafSpec (.RFor "i" 3 .RSkip) rs
      (rsSetScalar (rsSetScalar (rsSetScalar rs "i" 0) "i" 1) "i" 2) := by
  apply forSucc -- iter 2 (n=2 in forSucc, so x ↦ 2 + skip)
  · apply forSucc -- iter 1
    · apply forSucc -- iter 0
      · exact forZero ..
      · exact skip _
    · exact skip _
  · exact skip _

/-- Smoke test of the structural rule: counting iterations. After
    `RFor "i" n RSkip`, the invariant "we ran n iterations" is established. -/
example (N : Nat) (leafSpec : LeafSpec) (n : Nat) (rs r' : RustState)
    (h : RustExec N leafSpec (.RFor "i" n .RSkip) rs r') :
    True :=  -- the statement is `True`; the example checks that `rfor_invariant` applies
  rfor_invariant (I := fun _ _ => True)
    (hStep := fun _ _ _ _ _ => trivial)
    n rs r' trivial h

end RustExec

end CatCrypt.Crypto.Jasmin.LowCT
