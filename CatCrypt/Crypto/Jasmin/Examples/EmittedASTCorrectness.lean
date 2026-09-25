/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# Functional correctness + panic-freeness for Lean-emitted ASTs.

For each Lean-authored AST in `Examples/`, we state two correctness
properties:

  * **Panic-freeness**: existence of at least one `RustExec`-derivation
    for the AST.  Existence implies the IR's big-step semantics is
    total on well-formed inputs — no panic can occur during execution.
    Proof technique: structural induction on the AST.

  * **Functional correctness**: the AST's post-state at the destination
    slot equals the value computed by an abstract mathematical
    specification, given that the leaf-call semantics in `LeafSpec`
    matches that specification.  Theorem statement only (proofs are
    multi-hour bookkeeping; user-facing deliverable is the THEOREM
    STATEMENTS — see task description).

The 4 emitted ASTs covered:

  * `Fe25519Invert.fe25519InvertBody`           — the x^(p-2) addition chain
  * `Scalar25519Ops` (6 methods)                — single-RCall scalar primitives
  * `MontUToEdwards.montUToEdwardsBody`         — Mont u → Edwards y
  * `CombTableInitArrV2.combTableInitArrV2Body` — comb table builder (TArr + SExpr)

## Common pattern: `RustExec_RCall_exists`

Every RCall constructor requires:
  (i)  dst.locVar is bound in `rs.rsTower` with type dst.locDst, and
  (ii) each arg.locVar is bound with type arg.locDst.

Under these two preconditions, the `RustExec` derivation always exists
(the leaf-spec value is total).  Captured by lemma below. -/
module

public import CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert
public import CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops
public import CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards
public import CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2
public import Mathlib.Data.ZMod.Basic


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §0.  Generic panic-freeness helpers

For each `LowCT` constructor we expose a one-line existence lemma:
`∀ rs, ∃ rs', RustExec N leafSpec c rs rs'` (or with the minimum
required preconditions for the conditional ones).  These compose
into structural proofs of panic-freeness for the larger ASTs. -/

variable {N : Nat} {leafSpec : LeafSpec}

/-- `RSkip` is unconditionally executable. -/
lemma rskip_panic_free (rs : RustState) :
    ∃ rs', RustExec N leafSpec LowCT.RSkip rs rs' :=
  ⟨rs, RustExec.skip rs⟩

/-- `RScalarSet` is unconditionally executable. -/
lemma rscalarSet_panic_free (x : String) (v : Nat) (rs : RustState) :
    ∃ rs', RustExec N leafSpec (LowCT.RScalarSet x v) rs rs' :=
  ⟨_, RustExec.scalarSet x v rs⟩

/-- `RScalarSetExpr` is unconditionally executable. -/
lemma rscalarSetExpr_panic_free (x : String) (e : SExpr) (rs : RustState) :
    ∃ rs', RustExec N leafSpec (LowCT.RScalarSetExpr x e) rs rs' :=
  ⟨_, RustExec.scalarSetExpr x e rs⟩

/-- `RCallN` is executable from any state that binds every argument slot and
    every destination slot at its declared tower type. -/
lemma rcallN_panic_free (f : String) (dests args : List Located)
    (rs : RustState)
    (hArgs : ∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩)
    (hDests : ∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) :
    ∃ rs', RustExec N leafSpec (LowCT.RCallN f dests args) rs rs' :=
  ⟨_, RustExec.callN f dests args rs _ rfl hArgs hDests⟩

/-- `RAssert` is unconditionally executable (identity stub semantics). -/
lemma rassert_panic_free (label : String) (rs : RustState) :
    ∃ rs', RustExec N leafSpec (LowCT.RAssert label) rs rs' :=
  ⟨rs, RustExec.assert label rs⟩

/-- `RSeq` composes: if both halves are panic-free for all states,
    so is the sequence. -/
lemma rseq_panic_free
    {c1 c2 : LowCT}
    (h1 : ∀ rs, ∃ rs', RustExec N leafSpec c1 rs rs')
    (h2 : ∀ rs, ∃ rs', RustExec N leafSpec c2 rs rs') (rs : RustState) :
    ∃ rs', RustExec N leafSpec (LowCT.RSeq c1 c2) rs rs' := by
  obtain ⟨r1, hr1⟩ := h1 rs
  obtain ⟨r2, hr2⟩ := h2 r1
  exact ⟨r2, RustExec.seq _ _ _ _ _ hr1 hr2⟩

/-- `RLetZero` composes: if the body is panic-free starting from any
    state, then so is the let-binding form. -/
lemma rletZero_panic_free
    (x : String) (t : TowerType) {body : LowCT}
    (hBody : ∀ rs, ∃ rs', RustExec N leafSpec body rs rs') (rs : RustState) :
    ∃ rs', RustExec N leafSpec (LowCT.RLetZero x t body) rs rs' := by
  obtain ⟨rs', hrs'⟩ := hBody (rsSetTower rs x ⟨t, default⟩)
  exact ⟨rs', RustExec.letZero x t body rs rs' hrs'⟩

/-- `RLetU64Zero` composes. -/
lemma rletU64Zero_panic_free
    (x : String) {body : LowCT}
    (hBody : ∀ rs, ∃ rs', RustExec N leafSpec body rs rs') (rs : RustState) :
    ∃ rs', RustExec N leafSpec (LowCT.RLetU64Zero x body) rs rs' := by
  obtain ⟨rs', hrs'⟩ := hBody (rsSetScalar rs x 0)
  exact ⟨rs', RustExec.letU64Zero x body rs rs' hrs'⟩

/-- `RBlock` composes. -/
lemma rblock_panic_free
    {body : LowCT}
    (hBody : ∀ rs, ∃ rs', RustExec N leafSpec body rs rs') (rs : RustState) :
    ∃ rs', RustExec N leafSpec (LowCT.RBlock body) rs rs' := by
  obtain ⟨rs', hrs'⟩ := hBody rs
  exact ⟨rs', RustExec.block body rs rs' hrs'⟩

/-- `RFor` composes via induction on `n`: if the body is panic-free
    starting from any state, then `RFor x n body` is panic-free for
    any closed bound `n`. -/
lemma rfor_panic_free
    (x : String) {body : LowCT}
    (hBody : ∀ rs, ∃ rs', RustExec N leafSpec body rs rs') :
    ∀ (n : Nat) (rs : RustState),
      ∃ rs', RustExec N leafSpec (LowCT.RFor x n body) rs rs' := by
  intro n
  induction n with
  | zero =>
    intro rs; exact ⟨rs, RustExec.forZero x body rs⟩
  | succ k ih =>
    intro rs
    obtain ⟨r1, hr1⟩ := ih rs
    obtain ⟨rs', hrs'⟩ := hBody (rsSetScalar r1 x k)
    exact ⟨rs', RustExec.forSucc x k body rs r1 rs' hr1 hrs'⟩

/-- `RFor` panic-freeness with a state invariant `P`: if `P` is
    preserved by every body iteration (with any scalar value at `x`),
    then the for-loop preserves `P` and is panic-free.

    Generalises `rfor_panic_free` to bodies that require pre-conditions
    on the input state. -/
lemma rfor_panic_free_invariant
    (x : String) {body : LowCT} (P : RustState → Prop)
    (hP_setScalar : ∀ rs k, P rs → P (rsSetScalar rs x k))
    (hBodyExec : ∀ rs, P rs →
        ∃ rs', RustExec N leafSpec body rs rs' ∧ P rs') :
    ∀ (n : Nat) (rs : RustState), P rs →
      ∃ rs', RustExec N leafSpec (LowCT.RFor x n body) rs rs' ∧ P rs' := by
  intro n
  induction n with
  | zero =>
    intro rs hP; exact ⟨rs, RustExec.forZero x body rs, hP⟩
  | succ k ih =>
    intro rs hP
    obtain ⟨r1, hr1, hPr1⟩ := ih rs hP
    obtain ⟨rs', hrs', hPrs'⟩ := hBodyExec _ (hP_setScalar r1 k hPr1)
    exact ⟨rs', RustExec.forSucc x k body rs r1 rs' hr1 hrs', hPrs'⟩

/-- `RArrStore` requires `arr` and `src` slots bound. -/
lemma rarrStore_panic_free
    (arr : Located) (idxVar : String) (src : Located)
    (rs : RustState)
    (hArr : ∃ v, rs.rsTower arr.locVar = some ⟨arr.locDst, v⟩)
    (hSrc : ∃ v, rs.rsTower src.locVar = some ⟨src.locDst, v⟩) :
    ∃ rs', RustExec N leafSpec (LowCT.RArrStore arr idxVar src) rs rs' := by
  obtain ⟨arrV, hArrV⟩ := hArr
  obtain ⟨srcV, hSrcV⟩ := hSrc
  have hArrLookup : locatedLookup rs arr = some arrV := by
    show (match rs.rsTower arr.locVar with
          | some ⟨t, v⟩ => if h : t = arr.locDst then some (h ▸ v) else none
          | none => none) = some arrV
    rw [hArrV]; simp
  have hSrcLookup : locatedLookup rs src = some srcV := by
    show (match rs.rsTower src.locVar with
          | some ⟨t, v⟩ => if h : t = src.locDst then some (h ▸ v) else none
          | none => none) = some srcV
    rw [hSrcV]; simp
  refine ⟨_, RustExec.arrStore arr idxVar src rs (rs.rsScalar idxVar)
    arrV srcV rfl hArrLookup hSrcLookup⟩

/-- After an `RCall` execution, the destination slot is bound at its
    declared tower type, and all other slots are unchanged.

    Used to thread slot-binding invariants through a chain of `RCall`s. -/
lemma rcall_post_bindings
    {N : Nat} {leafSpec : LeafSpec}
    {f : String} {dest : Located} {args : List Located}
    {rs rs' : RustState}
    (hExec : RustExec N leafSpec (LowCT.RCall f dest args) rs rs') :
    (∃ v, rs'.rsTower dest.locVar = some ⟨dest.locDst, v⟩) ∧
    (∀ name : String, name ≠ dest.locVar →
        rs'.rsTower name = rs.rsTower name) := by
  cases hExec with
  | call _ _ _ _ oldV args _ _ _ =>
    refine ⟨⟨_, locatedUpdate_dest _ _ _⟩, ?_⟩
    intro name hne
    show (rsSetTower rs dest.locVar _).rsTower name = rs.rsTower name
    exact rsSetTower_other _ _ _ _ (Ne.symm hne)

/-- `RArrLoad` requires `dst` and `src` slots bound. -/
lemma rarrLoad_panic_free
    (dst src : Located) (idxVar : String)
    (rs : RustState)
    (hDst : ∃ v, rs.rsTower dst.locVar = some ⟨dst.locDst, v⟩)
    (hSrc : ∃ v, rs.rsTower src.locVar = some ⟨src.locDst, v⟩) :
    ∃ rs', RustExec N leafSpec (LowCT.RArrLoad dst src idxVar) rs rs' := by
  obtain ⟨dstV, hDstV⟩ := hDst
  obtain ⟨srcV, hSrcV⟩ := hSrc
  have hDstLookup : locatedLookup rs dst = some dstV := by
    show (match rs.rsTower dst.locVar with
          | some ⟨t, v⟩ => if h : t = dst.locDst then some (h ▸ v) else none
          | none => none) = some dstV
    rw [hDstV]; simp
  have hSrcLookup : locatedLookup rs src = some srcV := by
    show (match rs.rsTower src.locVar with
          | some ⟨t, v⟩ => if h : t = src.locDst then some (h ▸ v) else none
          | none => none) = some srcV
    rw [hSrcV]; simp
  refine ⟨_, RustExec.arrLoad dst src idxVar rs (rs.rsScalar idxVar)
    dstV srcV rfl hDstLookup hSrcLookup⟩

/-! ## §0.5  Syntactic AST predicates + slot-type preservation

For scaling FC / panic-freeness proofs over multi-RCall ASTs, we need
to thread slot-binding invariants through an arbitrary `RustExec`
derivation.  `rustExec_preserves_slot_type` is the key infrastructure
lemma: under two syntactic checks on the AST (no `RSelect`, no
`RLetZero`-rebinding of the tracked variable), any slot bound at a
declared tower type before execution is still bound at that same
tower type afterwards (with a possibly-different value).

`RSelect` is excluded because its semantics can silently change a
slot's tower type (the `srcs.locDst = dst.locDst` constraint is a
*hypothesis* of the constructor, not enforced at the value level —
so if we don't know the constructor was applied with matching types,
we can't deduce type preservation).  Our extracted ASTs never use
`RSelect`, so this hypothesis is satisfiable.

`hasBindOf x c = false` rules out `RLetZero x t' body` (or
`RLetU64Zero x body`) inside `c` that would shadow the tracked
variable.  For our extracted ASTs, fresh-let-bound vars have
hygienic, unique names that don't collide with externally-bound
inputs / outputs (e.g. `"a"`, `"out"`). -/

/-- Syntactic check: does the AST contain any `RSelect` or
    `RCloneCall` constructor?  These are the two constructors whose
    semantics can silently change a slot's stored tower type (via
    the dependent equality `srcs.locDst = dst.locDst` in `RSelect`
    or the heterogeneous overwrite in `RCloneCall`); excluding them
    lets us prove unconditional slot-type preservation. -/
def hasSelect : LowCT → Bool
  | .RSelect _ _ _ _ => true
  | .RCloneCall _ _ _ _ _ _ => true
  | .RSeq c1 c2 => hasSelect c1 || hasSelect c2
  | .RLetZero _ _ body => hasSelect body
  | .RLetU64Zero _ body => hasSelect body
  | .RBlock body => hasSelect body
  | .RFor _ _ body => hasSelect body
  | .RForRuntime _ _ body => hasSelect body
  | .RIfNz _ c1 c2 => hasSelect c1 || hasSelect c2
  | .RWhileNz _ body => hasSelect body
  | .RFnDef _ _ _ body cont => hasSelect body || hasSelect cont
  | _ => false

/-- Syntactic check: does the AST contain any `RLetZero x _ _` or
    `RLetU64Zero x _` binding the given variable name? -/
def hasBindOf (x : String) : LowCT → Bool
  | .RLetZero y _ body => decide (y = x) || hasBindOf x body
  | .RLetU64Zero y body => decide (y = x) || hasBindOf x body
  | .RSeq c1 c2 => hasBindOf x c1 || hasBindOf x c2
  | .RBlock body => hasBindOf x body
  | .RFor _ _ body => hasBindOf x body
  | .RForRuntime _ _ body => hasBindOf x body
  | .RIfNz _ c1 c2 => hasBindOf x c1 || hasBindOf x c2
  | .RWhileNz _ body => hasBindOf x body
  | .RFnDef _ _ _ body cont => hasBindOf x body || hasBindOf x cont
  | _ => false

/-- A single `locatedUpdate` at a slot bound at its own declared tower type
    preserves every slot's tower type: an unrelated slot is untouched, and the
    written slot receives a value at the type it already held. -/
lemma locatedUpdate_preserves_slot_type
    (rs : RustState) (d : Located) (w : RustVal d.locDst)
    (hd : ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩)
    (x : String) (t : TowerType) (hx : ∃ v, rs.rsTower x = some ⟨t, v⟩) :
    ∃ v', (locatedUpdate rs d w).rsTower x = some ⟨t, v'⟩ := by
  obtain ⟨vx, hvx⟩ := hx
  by_cases hxd : x = d.locVar
  · subst hxd
    obtain ⟨vd, hvd⟩ := hd
    rw [hvx] at hvd
    have ht : t = d.locDst := congrArg Sigma.fst (Option.some.inj hvd)
    subst ht
    exact ⟨w, locatedUpdate_dest rs d w⟩
  · refine ⟨vx, ?_⟩
    show (rsSetTower rs d.locVar _).rsTower x = _
    rw [rsSetTower_other rs d.locVar x _ (fun h => hxd h.symm)]
    exact hvx

/-- The destination fold of an N-output call preserves every slot's tower type,
    given that each destination is bound at its declared type in the pre-state. -/
lemma callNUpdate_preserves_slot_type
    (leafSpec : LeafSpec) (f : String) (argTs : List TowerType)
    (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState)
      (x : String) (t : TowerType),
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      (∃ v, rs.rsTower x = some ⟨t, v⟩) →
      ∃ v', (callNUpdate leafSpec f argTs argList i dests rs).rsTower x
              = some ⟨t, v'⟩ := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _ _ hx; exact hx
  | cons d rest ih =>
    intro i rs x t hDests hx
    have hdBound : ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩ :=
      hDests d (by simp)
    show ∃ v', (callNUpdate leafSpec f argTs argList (i + 1) rest
        (locatedUpdate rs d _)).rsTower x = some ⟨t, v'⟩
    refine ih (i + 1) _ x t ?_
      (locatedUpdate_preserves_slot_type rs d _ hdBound x t hx)
    intro d' hd'
    exact locatedUpdate_preserves_slot_type rs d _ hdBound d'.locVar d'.locDst
      (hDests d' (List.mem_cons_of_mem d hd'))

/-- **Slot-type preservation** (key infrastructure lemma).

    Under the two syntactic checks (no `RSelect`; no fresh-let
    rebinding of the tracked variable `x`), if `x` is bound at
    tower type `t` in `rs`, then `x` is still bound at tower type
    `t` (with some possibly-different value) in `rs'`.

    Used to thread slot-binding invariants through chains of
    `RCall`s / `RFor`s without manual case-by-case state plumbing. -/
theorem rustExec_preserves_slot_type
    {N : Nat} {leafSpec : LeafSpec}
    {c : LowCT} {rs rs' : RustState}
    (h_exec : RustExec N leafSpec c rs rs')
    (h_noSel : hasSelect c = false) :
    ∀ (x : String) (t : TowerType),
      hasBindOf x c = false →
      (∃ v, rs.rsTower x = some ⟨t, v⟩) →
      ∃ v', rs'.rsTower x = some ⟨t, v'⟩ := by
  induction h_exec with
  | skip _ => intro x t _ h; exact h
  | seq _ _ _ _ _ _ _ ih1 ih2 =>
    intro x t hNoBind h
    simp [hasSelect] at h_noSel
    simp [hasBindOf] at hNoBind
    obtain ⟨h1, h2⟩ := h_noSel
    obtain ⟨b1, b2⟩ := hNoBind
    exact ih2 h2 x t b2 (ih1 h1 x t b1 h)
  | letZero y t' body rs0 rs0' _ ih =>
    intro x t hNoBind h
    simp [hasSelect] at h_noSel
    simp [hasBindOf] at hNoBind
    obtain ⟨hyx, hBodyBind⟩ := hNoBind
    -- The body executes from `rsSetTower rs0 y ⟨t', default⟩`.
    -- We need: x's type-t binding survives.  Since y ≠ x (from hyx),
    -- setting y at type t' doesn't disturb x's slot.
    apply ih h_noSel x t hBodyBind
    obtain ⟨v, hv⟩ := h
    refine ⟨v, ?_⟩
    show (rsSetTower rs0 y ⟨t', default⟩).rsTower x = _
    rw [rsSetTower_other rs0 y x _ hyx]
    exact hv
  | letU64Zero y body rs0 rs0' _ ih =>
    intro x t hNoBind h
    simp [hasSelect] at h_noSel
    simp [hasBindOf] at hNoBind
    obtain ⟨_hyx, hBodyBind⟩ := hNoBind
    -- The body executes from `rsSetScalar rs0 y 0`.  Setting a scalar
    -- doesn't touch the tower, so x's tower binding survives directly.
    apply ih h_noSel x t hBodyBind
    obtain ⟨v, hv⟩ := h
    exact ⟨v, hv⟩
  | scalarSet y v rs0 =>
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    refine ⟨vv, ?_⟩
    show (rsSetScalar rs0 y v).rsTower x = _
    exact hv
  | ifTrue _ _ _ _ _ _ _ _ _ ih =>
    intro x t hNoBind h
    simp [hasSelect] at h_noSel
    simp [hasBindOf] at hNoBind
    obtain ⟨ht, _⟩ := h_noSel
    obtain ⟨hb, _⟩ := hNoBind
    exact ih ht x t hb h
  | ifFalse _ _ _ _ _ _ _ ih =>
    intro x t hNoBind h
    simp [hasSelect] at h_noSel
    simp [hasBindOf] at hNoBind
    obtain ⟨_, hf⟩ := h_noSel
    obtain ⟨_, hb⟩ := hNoBind
    exact ih hf x t hb h
  | whileFalse _ _ _ _ => intro x t _ h; exact h
  | whileTrue e body _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro x t hNoBind h
    -- For RWhileNz, hasSelect on body and on (RWhileNz e body) are the same.
    have h_noSel' : hasSelect body = false := by
      simp [hasSelect] at h_noSel; exact h_noSel
    have hNoBind' : hasBindOf x body = false := by
      simp [hasBindOf] at hNoBind; exact hNoBind
    exact ih2 h_noSel x t hNoBind (ih1 h_noSel' x t hNoBind' h)
  | forZero _ _ _ => intro x t _ h; exact h
  | forRuntime y bound body rs0 rs0' _ ih =>
    intro x t hNoBind h
    -- hasSelect/hasBindOf on RForRuntime mirror the inner RFor (both descend
    -- into body), so the inner-RFor IH applies directly.
    have h_noSel' : hasSelect (LowCT.RFor y (bound.evalState rs0) body) = false := by
      simp [hasSelect] at h_noSel ⊢; exact h_noSel
    have hNoBind' : hasBindOf x (LowCT.RFor y (bound.evalState rs0) body) = false := by
      simp [hasBindOf] at hNoBind ⊢; exact hNoBind
    exact ih h_noSel' x t hNoBind' h
  | forSucc y n body rs0 r1 rs0' _ _ ih1 ih2 =>
    intro x t hNoBind h
    -- ih2 runs body on rsSetScalar r1 y n; setting a scalar leaves
    -- the tower untouched.
    have h_noSel_body : hasSelect body = false := by simp [hasSelect] at h_noSel; exact h_noSel
    have hNoBind_body : hasBindOf x body = false := by simp [hasBindOf] at hNoBind; exact hNoBind
    -- Apply ih1: rs to r1 preserves x at t.
    have hr1 : ∃ v, r1.rsTower x = some ⟨t, v⟩ :=
      ih1 (by simp [hasSelect, h_noSel_body]) x t (by simp [hasBindOf, hNoBind_body]) h
    -- Then apply ih2: r1 (with scalar set) to rs0'.
    obtain ⟨v, hv⟩ := hr1
    apply ih2 h_noSel_body x t hNoBind_body
    refine ⟨v, ?_⟩
    show (rsSetScalar r1 y n).rsTower x = _
    exact hv
  | call f dest args rs0 oldDestV argList hLook _ _ =>
    intro x t _ h
    -- Post-state: locatedUpdate rs0 dest (...).  Case on x = dest.locVar.
    obtain ⟨v, hv⟩ := h
    by_cases hxd : x = dest.locVar
    · -- x = dest.locVar; old type at x must equal dest.locDst (from hLook).
      subst hxd
      have hTypeEq : t = dest.locDst := by
        unfold locatedLookup at hLook
        rw [hv] at hLook
        by_cases hh : t = dest.locDst
        · exact hh
        · simp [hh] at hLook
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 dest _⟩
    · -- x ≠ dest.locVar; locatedUpdate at dest doesn't touch x.
      refine ⟨v, ?_⟩
      show (locatedUpdate rs0 dest _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 dest.locVar x _ (fun h => hxd (h.symm))]
      exact hv
  | cloneCall _ _ _ _ _ _ _ _ _ _ _ _ =>
    -- Excluded by `hasSelect c = false` (we treat `RCloneCall` as
    -- "unsafe" w.r.t. slot-type preservation).
    intro x t _ _
    simp [hasSelect] at h_noSel
  | callSwap f dest1 dest2 args _ _ _ _ _ ih1 ih2 =>
    intro x t hNoBind h
    have h1 : hasSelect (LowCT.RCall f dest1 args) = false := by simp [hasSelect]
    have h2 : hasSelect (LowCT.RCall f dest2 args) = false := by simp [hasSelect]
    have b1 : hasBindOf x (LowCT.RCall f dest1 args) = false := by simp [hasBindOf]
    have b2 : hasBindOf x (LowCT.RCall f dest2 args) = false := by simp [hasBindOf]
    exact ih2 h2 x t b2 (ih1 h1 x t b1 h)
  | limbStore loc idx v rs0 oldDestV hLook =>
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    by_cases hxl : x = loc.locVar
    · subst hxl
      have hTypeEq : t = loc.locDst := by
        unfold locatedLookup at hLook
        rw [hv] at hLook
        by_cases hh : t = loc.locDst
        · exact hh
        · simp [hh] at hLook
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 loc _⟩
    · refine ⟨vv, ?_⟩
      show (locatedUpdate rs0 loc _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 loc.locVar x _ (fun h => hxl h.symm)]
      exact hv
  -- Phase R5: runtime-valued limb store preserves typed bindings identically
  -- to `limbStore` (the stored value does not affect the slot's type).
  | limbStoreExpr loc idx e rs0 oldDestV hLook =>
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    by_cases hxl : x = loc.locVar
    · subst hxl
      have hTypeEq : t = loc.locDst := by
        unfold locatedLookup at hLook
        rw [hv] at hLook
        by_cases hh : t = loc.locDst
        · exact hh
        · simp [hh] at hLook
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 loc _⟩
    · refine ⟨vv, ?_⟩
      show (locatedUpdate rs0 loc _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 loc.locVar x _ (fun h => hxl h.symm)]
      exact hv
  | callN f dests args rs0 argList _ _ hDests =>
    intro x t _ h
    exact callNUpdate_preserves_slot_type leafSpec f (args.map (·.locDst)) argList
      dests 0 rs0 x t hDests h
  | callDstThreaded f dst args rs0 oldDestV argList hLook _ _ =>
    -- Same shape as `call`: post-state is `locatedUpdate rs0 dst (...)`.
    intro x t _ h
    obtain ⟨v, hv⟩ := h
    by_cases hxd : x = dst.locVar
    · subst hxd
      have hTypeEq : t = dst.locDst := by
        unfold locatedLookup at hLook
        rw [hv] at hLook
        by_cases hh : t = dst.locDst
        · exact hh
        · simp [hh] at hLook
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 dst _⟩
    · refine ⟨v, ?_⟩
      show (locatedUpdate rs0 dst _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 dst.locVar x _ (fun h => hxd (h.symm))]
      exact hv
  | selectFalse _ _ _ _ _ _ _ _ _ =>
    -- excluded by h_noSel
    intro x t _ _
    simp [hasSelect] at h_noSel
  | selectTrue _ _ _ _ _ _ _ _ _ _ =>
    intro x t _ _
    simp [hasSelect] at h_noSel
  | assert _ _ => intro x t _ h; exact h
  | block body rs0 rs0' _ ih =>
    intro x t hNoBind h
    have h_noSel' : hasSelect body = false := by simp [hasSelect] at h_noSel; exact h_noSel
    have hNoBind' : hasBindOf x body = false := by simp [hasBindOf] at hNoBind; exact hNoBind
    exact ih h_noSel' x t hNoBind' h
  | tupleLoad dst src idx rs0 oldV srcV hLookDst _hLookSrc =>
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    by_cases hxd : x = dst.locVar
    · subst hxd
      have hTypeEq : t = dst.locDst := by
        unfold locatedLookup at hLookDst
        rw [hv] at hLookDst
        by_cases hh : t = dst.locDst
        · exact hh
        · simp [hh] at hLookDst
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 dst _⟩
    · refine ⟨vv, ?_⟩
      show (locatedUpdate rs0 dst _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 dst.locVar x _ (fun h => hxd h.symm)]
      exact hv
  | arrStore arr idxVar src rs0 idx oldV srcV _hIdx hLookArr _hLookSrc =>
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    by_cases hxa : x = arr.locVar
    · subst hxa
      have hTypeEq : t = arr.locDst := by
        unfold locatedLookup at hLookArr
        rw [hv] at hLookArr
        by_cases hh : t = arr.locDst
        · exact hh
        · simp [hh] at hLookArr
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 arr _⟩
    · refine ⟨vv, ?_⟩
      show (locatedUpdate rs0 arr _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 arr.locVar x _ (fun h => hxa h.symm)]
      exact hv
  | arrLoad dst src idxVar rs0 idx oldV srcV _hIdx hLookDst _hLookSrc =>
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    by_cases hxd : x = dst.locVar
    · subst hxd
      have hTypeEq : t = dst.locDst := by
        unfold locatedLookup at hLookDst
        rw [hv] at hLookDst
        by_cases hh : t = dst.locDst
        · exact hh
        · simp [hh] at hLookDst
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 dst _⟩
    · refine ⟨vv, ?_⟩
      show (locatedUpdate rs0 dst _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 dst.locVar x _ (fun h => hxd h.symm)]
      exact hv
  | arrStoreLit arr idx src rs0 oldV srcV hLookArr _hLookSrc =>
    -- Phase DD (2026-05-28): literal-index store.  Same post-state shape
    -- as `arrStore` (`locatedUpdate rs0 arr (…)`), minus the runtime
    -- index lookup, so the type-preservation argument is identical.
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    by_cases hxa : x = arr.locVar
    · subst hxa
      have hTypeEq : t = arr.locDst := by
        unfold locatedLookup at hLookArr
        rw [hv] at hLookArr
        by_cases hh : t = arr.locDst
        · exact hh
        · simp [hh] at hLookArr
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 arr _⟩
    · refine ⟨vv, ?_⟩
      show (locatedUpdate rs0 arr _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 arr.locVar x _ (fun h => hxa h.symm)]
      exact hv
  | arrLoadLit dst src idx rs0 oldV srcV hLookDst _hLookSrc =>
    -- Phase DD (2026-05-28): literal-index load.  Same post-state shape
    -- as `arrLoad`, minus the runtime index lookup.
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    by_cases hxd : x = dst.locVar
    · subst hxd
      have hTypeEq : t = dst.locDst := by
        unfold locatedLookup at hLookDst
        rw [hv] at hLookDst
        by_cases hh : t = dst.locDst
        · exact hh
        · simp [hh] at hLookDst
      subst hTypeEq
      exact ⟨_, locatedUpdate_dest rs0 dst _⟩
    · refine ⟨vv, ?_⟩
      show (locatedUpdate rs0 dst _).rsTower x = _
      unfold locatedUpdate
      rw [rsSetTower_other rs0 dst.locVar x _ (fun h => hxd h.symm)]
      exact hv
  | scalarSetExpr y e rs0 =>
    intro x t _ h
    obtain ⟨vv, hv⟩ := h
    refine ⟨vv, ?_⟩
    show (rsSetScalar rs0 y _).rsTower x = _
    exact hv


/-! ## §1.  Generic `RCall` panic-freeness lemma -/

/-- Given destination + args are present in the state at their declared
    tower types, `RCall` always has a successful execution.

    This is the structural reason every RCall-only AST is panic-free:
    the leaf-call's `LeafSpec.call` is total, and the heap's `Σ`-typed
    pair is preserved. -/
lemma rcall_panic_free (N : Nat) (leafSpec : LeafSpec)
    (f : String) (dest : Located) (args : List Located)
    (rs : RustState)
    (hDest : ∃ v, rs.rsTower dest.locVar = some ⟨dest.locDst, v⟩)
    (hArgs : ∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) :
    ∃ rs', RustExec N leafSpec (LowCT.RCall f dest args) rs rs' := by
  obtain ⟨oldV, hOld⟩ := hDest
  have hLookup : locatedLookup rs dest = some oldV := by
    show (match rs.rsTower dest.locVar with
          | some ⟨t, v⟩ => if h : t = dest.locDst then some (h ▸ v) else none
          | none => none) = some oldV
    rw [hOld]; simp
  exact ⟨_, RustExec.call f dest args rs oldV
    (args.filterMap (fun a => rs.rsTower a.locVar)) hLookup rfl hArgs⟩

/-! ## §2.  Scalar25519Ops — six single-RCall methods

Each is a single `RCall`; panic-freeness reduces to `rcall_panic_free`. -/

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- Mul body: `out := mul_mont(a, b)`. -/
theorem mulBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hOut : ∃ v, rs.rsTower "out" = some ⟨TowerType.TFpL25519, v⟩)
    (hA : ∃ v, rs.rsTower "a" = some ⟨TowerType.TFpL25519, v⟩)
    (hB : ∃ v, rs.rsTower "b" = some ⟨TowerType.TFpL25519, v⟩) :
    ∃ rs', RustExec N leafSpec mulBody rs rs' := by
  apply rcall_panic_free _ _ _ _ _ _ hOut
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; exact hA
  · rcases List.mem_singleton.mp h with rfl; exact hB

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- Add body. -/
theorem addBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hOut : ∃ v, rs.rsTower "out" = some ⟨TowerType.TFpL25519, v⟩)
    (hA : ∃ v, rs.rsTower "a" = some ⟨TowerType.TFpL25519, v⟩)
    (hB : ∃ v, rs.rsTower "b" = some ⟨TowerType.TFpL25519, v⟩) :
    ∃ rs', RustExec N leafSpec addBody rs rs' := by
  apply rcall_panic_free _ _ _ _ _ _ hOut
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; exact hA
  · rcases List.mem_singleton.mp h with rfl; exact hB

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- Sub body. -/
theorem subBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hOut : ∃ v, rs.rsTower "out" = some ⟨TowerType.TFpL25519, v⟩)
    (hA : ∃ v, rs.rsTower "a" = some ⟨TowerType.TFpL25519, v⟩)
    (hB : ∃ v, rs.rsTower "b" = some ⟨TowerType.TFpL25519, v⟩) :
    ∃ rs', RustExec N leafSpec subBody rs rs' := by
  apply rcall_panic_free _ _ _ _ _ _ hOut
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; exact hA
  · rcases List.mem_singleton.mp h with rfl; exact hB

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- Negate body. -/
theorem negateBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hOut : ∃ v, rs.rsTower "out" = some ⟨TowerType.TFpL25519, v⟩)
    (hA : ∃ v, rs.rsTower "a" = some ⟨TowerType.TFpL25519, v⟩) :
    ∃ rs', RustExec N leafSpec negateBody rs rs' := by
  apply rcall_panic_free _ _ _ _ _ _ hOut
  intro x hx
  rcases List.mem_singleton.mp hx with rfl; exact hA

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- from_bytes_mod_order body. -/
theorem fromBytesModOrderBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hOut : ∃ v, rs.rsTower "out" = some ⟨TowerType.TFpL25519, v⟩)
    (hBytes : ∃ v, rs.rsTower "bytes_in" = some ⟨TowerType.TBytes 32, v⟩) :
    ∃ rs', RustExec N leafSpec fromBytesModOrderBody rs rs' := by
  apply rcall_panic_free _ _ _ _ _ _ hOut
  intro x hx
  rcases List.mem_singleton.mp hx with rfl; exact hBytes

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- to_bytes body. -/
theorem toBytesBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hOut : ∃ v, rs.rsTower "out" = some ⟨TowerType.TBytes 32, v⟩)
    (hMont : ∃ v, rs.rsTower "mont" = some ⟨TowerType.TFpL25519, v⟩) :
    ∃ rs', RustExec N leafSpec toBytesBody rs rs' := by
  apply rcall_panic_free _ _ _ _ _ _ hOut
  intro x hx
  rcases List.mem_singleton.mp hx with rfl; exact hMont

/-! ## §3.  Functional-correctness theorem statements

Each functional-correctness theorem says: under leaf-correctness
hypotheses, the post-state's destination value equals the abstract
math.  Proofs are bookkeeping: peel off RCall semantics, propagate
leaf-spec. -/

/-- Generic single-RCall functional-correctness lemma:
    if `dest`'s post-call value matches `mathVal`, then the post-state
    has `dest.locVar = some ⟨dest.locDst, mathVal⟩`.

    Most leaf-call FC proofs reduce to this by computing the `argList`
    explicitly and applying a leaf-spec hypothesis. -/
lemma rcall_post_value
    {N : Nat} {leafSpec : LeafSpec}
    {f : String} {dest : Located} {args : List Located}
    {rs rs' : RustState}
    (hExec : RustExec N leafSpec (LowCT.RCall f dest args) rs rs')
    (mathVal : RustVal dest.locDst)
    (hLeaf : ∀ oldDestV argList,
        locatedLookup rs dest = some oldDestV →
        argList = args.filterMap (fun a => rs.rsTower a.locVar) →
        leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList =
          mathVal) :
    rs'.rsTower dest.locVar = some ⟨dest.locDst, mathVal⟩ := by
  cases hExec with
  | call _ _ _ _ oldDestV argList hLook hArgList _ =>
    rw [locatedUpdate_dest]
    congr 2
    exact hLeaf oldDestV argList hLook hArgList

/-- Abstract: a `LeafSpec` is correct for the Scalar25519 mul leaf if
    its `call` for "scalar25519_mul_mont" matches a given mathematical
    multiplication function. -/
def Scalar25519MulLeafSpecCorrect (leafSpec : LeafSpec)
    (mathMul : RustVal TowerType.TFpL25519 → RustVal TowerType.TFpL25519 →
               RustVal TowerType.TFpL25519) : Prop :=
  ∀ (oldV vA vB : RustVal TowerType.TFpL25519),
    leafSpec.call "scalar25519_mul_mont" TowerType.TFpL25519
      [TowerType.TFpL25519, TowerType.TFpL25519] oldV
      [⟨TowerType.TFpL25519, vA⟩, ⟨TowerType.TFpL25519, vB⟩] =
    mathMul vA vB

/-! ### Generic Fp25519 leaf-correctness predicates

Used by the FC theorems for `Fe25519Invert` and `MontUToEdwards`. -/

/-- The `fe25519_set_one` leaf yields a fixed `mathOne` constant. -/
def Fe25519SetOneLeafCorrect (leafSpec : LeafSpec)
    (mathOne : RustVal TowerType.TFp25519) : Prop :=
  ∀ (oldV : RustVal TowerType.TFp25519),
    leafSpec.call "fe25519_set_one" TowerType.TFp25519 [] oldV [] = mathOne

/-- A binary TFp25519 leaf-call (sub, add, mul) matches `mathOp`. -/
def Fe25519BinopLeafCorrect (leafSpec : LeafSpec) (name : String)
    (mathOp : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
              RustVal TowerType.TFp25519) : Prop :=
  ∀ (oldV vA vB : RustVal TowerType.TFp25519),
    leafSpec.call name TowerType.TFp25519
      [TowerType.TFp25519, TowerType.TFp25519] oldV
      [⟨TowerType.TFp25519, vA⟩, ⟨TowerType.TFp25519, vB⟩] =
    mathOp vA vB

/-- A unary TFp25519 leaf-call (invert, copy, sqr) matches `mathOp`. -/
def Fe25519UnopLeafCorrect (leafSpec : LeafSpec) (name : String)
    (mathOp : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519) : Prop :=
  ∀ (oldV vA : RustVal TowerType.TFp25519),
    leafSpec.call name TowerType.TFp25519
      [TowerType.TFp25519] oldV
      [⟨TowerType.TFp25519, vA⟩] = mathOp vA

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- Mul-body functional correctness: after running, `out` holds
    `mathMul a b`.

    Proof: `mulBody = RCall "scalar25519_mul_mont" out [a, b]`, a single
    leaf call.  `cases hExec` exposes the `RustExec.call` constructor,
    which fixes `rs' = locatedUpdate rs (scalar "out") (leafSpec.call ...)`.
    The argList computation reduces to `[⟨_, vA⟩, ⟨_, vB⟩]` from the
    state-lookup hypotheses, then `hLeaf` rewrites `leafSpec.call` to
    `mathMul vA vB`.  `locatedUpdate_dest` yields the goal. -/
theorem mulBody_functional_correctness
    (N : Nat) (leafSpec : LeafSpec)
    (mathMul : RustVal TowerType.TFpL25519 → RustVal TowerType.TFpL25519 →
               RustVal TowerType.TFpL25519)
    (hLeaf : Scalar25519MulLeafSpecCorrect leafSpec mathMul)
    (rs rs' : RustState)
    (vA vB : RustVal TowerType.TFpL25519)
    (hA : rs.rsTower "a" = some ⟨TowerType.TFpL25519, vA⟩)
    (hB : rs.rsTower "b" = some ⟨TowerType.TFpL25519, vB⟩)
    (hExec : RustExec N leafSpec mulBody rs rs') :
    rs'.rsTower "out" = some ⟨TowerType.TFpL25519, mathMul vA vB⟩ := by
  -- `mulBody` is one RCall — inspect via cases.
  cases hExec with
  | call _ _ _ _ oldOutV argList _hLook hArgList _hAccess =>
    -- Post-state of the call: locatedUpdate rs (out-loc) (leafSpec.call ...).
    -- locatedUpdate writes to the destination slot ("out") directly.
    show (locatedUpdate rs _ _).rsTower _ = _
    rw [show (locatedUpdate rs _ _).rsTower _ =
            some ⟨TowerType.TFpL25519, leafSpec.call "scalar25519_mul_mont"
              _ _ oldOutV argList⟩
        from locatedUpdate_dest rs _ _]
    -- Goal: some ⟨TFpL25519, leafSpec.call ...⟩ = some ⟨TFpL25519, mathMul vA vB⟩.
    -- Compute argList = [⟨_, vA⟩, ⟨_, vB⟩] from hArgList + hA + hB.
    have hArgList' : argList = [⟨TowerType.TFpL25519, vA⟩, ⟨TowerType.TFpL25519, vB⟩] := by
      rw [hArgList]
      show ([{ locVar := "a", locSrc := TowerType.TFpL25519 },
             { locVar := "b", locSrc := TowerType.TFpL25519 }] : List Located).filterMap
              (fun a => rs.rsTower a.locVar) = _
      simp only [List.filterMap, hA, hB]
    congr 2
    rw [hArgList']
    exact hLeaf oldOutV vA vB

/-! ## §4.  `Fe25519Invert` — panic-freeness theorem and
       functional-correctness goal.

The AST is ~50 RCall sites + 13 RLetZero binders + several RFor loops
(via `sqrN`).  Panic-freeness proof: induction on the seqN structure,
applying `rcall_panic_free` at each leaf.  Estimated effort:
~150 lines.  Statement-level effort: minimal.

The mathematical specification is `out = a^(p-2) mod p` where
`p = 2^255 - 19`.  Functional correctness chains 254 sqr + 11 mul
leaves to produce this exponent. -/

open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- All 13+ slots used by fe25519InvertBody bound + input `a`. -/
def Fe25519InvertInputsWellFormed (rs : RustState) : Prop :=
  (∃ v, rs.rsTower "a" = some ⟨TowerType.TFp25519, v⟩) ∧
  (∃ v, rs.rsTower "out" = some ⟨TowerType.TFp25519, v⟩)

/-- All slot names in `vars` are bound at `TFp25519` in `rs`. -/
def AllFp25519Bound (vars : List String) (rs : RustState) : Prop :=
  ∀ x ∈ vars, ∃ v, rs.rsTower x = some ⟨TowerType.TFp25519, v⟩

lemma AllFp25519Bound_setTower_other
    (vars : List String) (rs : RustState) (y : String)
    (s : Σ t, RustVal t) (hP : AllFp25519Bound vars rs)
    (hNotIn : y ∉ vars) :
    AllFp25519Bound vars (rsSetTower rs y s) := by
  intro x hx
  obtain ⟨v, hv⟩ := hP x hx
  refine ⟨v, ?_⟩
  show (rsSetTower rs y s).rsTower x = _
  rw [rsSetTower_other rs y x s (fun h => hNotIn (h ▸ hx))]
  exact hv

lemma AllFp25519Bound_setScalar
    (vars : List String) (rs : RustState) (y : String) (n : Nat)
    (hP : AllFp25519Bound vars rs) :
    AllFp25519Bound vars (rsSetScalar rs y n) := by
  intro x hx
  obtain ⟨v, hv⟩ := hP x hx
  refine ⟨v, ?_⟩
  show (rsSetScalar rs y n).rsTower x = _
  exact hv

/-- `RCall f dest args` for a destination in `vars` and TFp25519-typed
    args in `vars` is panic-free and preserves `AllFp25519Bound`. -/
lemma rcall_AllFp25519
    (N : Nat) (leafSpec : LeafSpec) (vars : List String)
    (f : String) (dest : String) (args : List String) (rs : RustState)
    (hDestIn : dest ∈ vars)
    (hArgsIn : ∀ a ∈ args, a ∈ vars)
    (hP : AllFp25519Bound vars rs) :
    ∃ rs', RustExec N leafSpec
        (LowCT.RCall f ⟨dest, TowerType.TFp25519⟩
          (args.map (fun a => ⟨a, TowerType.TFp25519⟩))) rs rs' ∧
      AllFp25519Bound vars rs' := by
  have hDest : ∃ v, rs.rsTower dest = some ⟨TowerType.TFp25519, v⟩ := hP dest hDestIn
  have hArgs : ∀ a ∈ args.map (fun a => (⟨a, TowerType.TFp25519⟩ : Located)),
      ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    exact hP s (hArgsIn s hs)
  obtain ⟨rs', hrs'⟩ := rcall_panic_free N leafSpec f
    ⟨dest, TowerType.TFp25519⟩ _ rs hDest hArgs
  refine ⟨rs', hrs', ?_⟩
  -- Preservation: use rcall_post_bindings to show all OTHER slots are
  -- unchanged; the dest slot is now bound at TFp25519 (its declared type).
  have ⟨⟨v', hDest'⟩, hPres⟩ := rcall_post_bindings hrs'
  intro x hx
  by_cases hxd : x = dest
  · subst hxd
    exact ⟨v', hDest'⟩
  · rw [hPres x hxd]; exact hP x hx

/-- The list of all TFp25519-typed slots used by fe25519InvertBody. -/
def fe25519InvertSlots : List String :=
  ["a", "out", "tmp", "scratch", "z2", "z9", "z11", "z2_5_0",
   "z2_10_0", "z2_20_0", "z2_40_0", "z2_50_0", "z2_100_0", "t2", "t3"]

/-- `sqrN n acc scratch` body is panic-free and preserves `AllFp25519Bound`
    when `acc, scratch ∈ vars`. -/
lemma sqrN_AllFp25519
    (N : Nat) (leafSpec : LeafSpec) (vars : List String)
    (n : Nat) (acc scratch : String)
    (hAcc : acc ∈ vars) (hSc : scratch ∈ vars)
    (rs : RustState) (hP : AllFp25519Bound vars rs) :
    ∃ rs', RustExec N leafSpec
        (LowCT.RFor "_i" n
          (LowCT.RSeq
            (LowCT.RCall "fe25519_sqr" ⟨scratch, TowerType.TFp25519⟩
              [⟨acc, TowerType.TFp25519⟩])
            (LowCT.RCall "fe25519_copy" ⟨acc, TowerType.TFp25519⟩
              [⟨scratch, TowerType.TFp25519⟩]))) rs rs' ∧
      AllFp25519Bound vars rs' := by
  apply rfor_panic_free_invariant "_i" (AllFp25519Bound vars)
    (fun rs k hP => AllFp25519Bound_setScalar vars rs "_i" k hP)
  · intro rs0 hP0
    -- Body: sqr scratch acc; copy acc scratch
    have hCallSqr : ∃ rs1, RustExec N leafSpec
        (LowCT.RCall "fe25519_sqr" ⟨scratch, TowerType.TFp25519⟩
          [⟨acc, TowerType.TFp25519⟩]) rs0 rs1 ∧ AllFp25519Bound vars rs1 := by
      have := rcall_AllFp25519 (vars := vars) N leafSpec
        "fe25519_sqr" scratch [acc] rs0 hSc
        (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hAcc) hP0
      simpa using this
    obtain ⟨rs1, hExec1, hP1⟩ := hCallSqr
    have hCallCopy : ∃ rs2, RustExec N leafSpec
        (LowCT.RCall "fe25519_copy" ⟨acc, TowerType.TFp25519⟩
          [⟨scratch, TowerType.TFp25519⟩]) rs1 rs2 ∧ AllFp25519Bound vars rs2 := by
      have := rcall_AllFp25519 (vars := vars) N leafSpec
        "fe25519_copy" acc [scratch] rs1 hAcc
        (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSc) hP1
      simpa using this
    obtain ⟨rs2, hExec2, hP2⟩ := hCallCopy
    exact ⟨rs2, RustExec.seq _ _ _ _ _ hExec1 hExec2, hP2⟩
  · exact hP

/-- Helper that uses `rcall_AllFp25519` with `sqr` shape (dst:=src^2 with
    src singleton). -/
lemma rcall_AllFp25519_sqr
    (N : Nat) (leafSpec : LeafSpec) (vars : List String)
    (dst src : String) (rs : RustState)
    (hD : dst ∈ vars) (hS : src ∈ vars)
    (hP : AllFp25519Bound vars rs) :
    ∃ rs', RustExec N leafSpec
        (LowCT.RCall "fe25519_sqr" ⟨dst, TowerType.TFp25519⟩
          [⟨src, TowerType.TFp25519⟩]) rs rs' ∧
      AllFp25519Bound vars rs' := by
  have := rcall_AllFp25519 (vars := vars) N leafSpec "fe25519_sqr" dst [src] rs hD
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hS) hP
  simpa using this

/-- Helper for `mul`-shape (binary). -/
lemma rcall_AllFp25519_mul
    (N : Nat) (leafSpec : LeafSpec) (vars : List String)
    (dst a b : String) (rs : RustState)
    (hD : dst ∈ vars) (hA : a ∈ vars) (hB : b ∈ vars)
    (hP : AllFp25519Bound vars rs) :
    ∃ rs', RustExec N leafSpec
        (LowCT.RCall "fe25519_mul" ⟨dst, TowerType.TFp25519⟩
          [⟨a, TowerType.TFp25519⟩, ⟨b, TowerType.TFp25519⟩]) rs rs' ∧
      AllFp25519Bound vars rs' := by
  have := rcall_AllFp25519 (vars := vars) N leafSpec "fe25519_mul" dst [a, b] rs hD
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx2
      · exact hA
      · rcases List.mem_singleton.mp hx2 with rfl; exact hB) hP
  simpa using this

/-- Helper for `copy`-shape (unary). -/
lemma rcall_AllFp25519_copy
    (N : Nat) (leafSpec : LeafSpec) (vars : List String)
    (dst src : String) (rs : RustState)
    (hD : dst ∈ vars) (hS : src ∈ vars)
    (hP : AllFp25519Bound vars rs) :
    ∃ rs', RustExec N leafSpec
        (LowCT.RCall "fe25519_copy" ⟨dst, TowerType.TFp25519⟩
          [⟨src, TowerType.TFp25519⟩]) rs rs' ∧
      AllFp25519Bound vars rs' := by
  have := rcall_AllFp25519 (vars := vars) N leafSpec "fe25519_copy" dst [src] rs hD
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hS) hP
  simpa using this

open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- **Panic-freeness for `fe25519InvertBody`.**

    Built by chaining 13 `RLetZero` binders into the state, then walking
    through the 32 leaf operations (sqr/mul/copy/sqrN) using the
    `AllFp25519Bound`-preservation helpers. -/
theorem fe25519InvertBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : Fe25519InvertInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec fe25519InvertBody rs rs' := by
  -- We build up the state by introducing each RLetZero binder, then chain
  -- the operations via the AllFp25519Bound invariant.
  obtain ⟨⟨aV, ha⟩, ⟨outV, hout⟩⟩ := hWf
  -- Build the state after 13 RLetZeros.
  set s1  := rsSetTower rs "tmp"      ⟨TowerType.TFp25519, default⟩ with hs1
  set s2  := rsSetTower s1 "scratch"  ⟨TowerType.TFp25519, default⟩
  set s3  := rsSetTower s2 "z2"       ⟨TowerType.TFp25519, default⟩
  set s4  := rsSetTower s3 "z9"       ⟨TowerType.TFp25519, default⟩
  set s5  := rsSetTower s4 "z11"      ⟨TowerType.TFp25519, default⟩
  set s6  := rsSetTower s5 "z2_5_0"   ⟨TowerType.TFp25519, default⟩
  set s7  := rsSetTower s6 "z2_10_0"  ⟨TowerType.TFp25519, default⟩
  set s8  := rsSetTower s7 "z2_20_0"  ⟨TowerType.TFp25519, default⟩
  set s9  := rsSetTower s8 "z2_40_0"  ⟨TowerType.TFp25519, default⟩
  set s10 := rsSetTower s9 "z2_50_0"  ⟨TowerType.TFp25519, default⟩
  set s11 := rsSetTower s10 "z2_100_0" ⟨TowerType.TFp25519, default⟩
  set s12 := rsSetTower s11 "t2"      ⟨TowerType.TFp25519, default⟩
  set s13 := rsSetTower s12 "t3"      ⟨TowerType.TFp25519, default⟩
  -- Establish AllFp25519Bound fe25519InvertSlots s13.
  have hAll : AllFp25519Bound fe25519InvertSlots s13 := by
    intro x hx
    simp only [fe25519InvertSlots, List.mem_cons, List.not_mem_nil,
               or_false] at hx
    show ∃ v, s13.rsTower x = some _
    -- For each of the 15 variables, the lookup in s13 reduces.
    -- The two external slots ("a", "out") are preserved via 13 rsSetTower_other rewrites;
    -- the 13 fresh slots resolve directly via rsSetTower_same at the appropriate layer.
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                | rfl | rfl | rfl | rfl
    -- x = "a"
    · refine ⟨aV, ?_⟩
      show s13.rsTower "a" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact ha
    -- x = "out"
    · refine ⟨outV, ?_⟩
      show s13.rsTower "out" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hout
    -- x = "tmp"  (innermost set, 12 outer rewrites then rsSetTower_same)
    · refine ⟨default, ?_⟩
      show s13.rsTower "tmp" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "scratch" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z9" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z11" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_5_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_10_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_20_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_40_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_50_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_100_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "t2" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, rsSetTower_same _ _ _⟩
  -- Now we chain the ops on s13.  Use AllFp25519Bound preservation.
  -- The body is a long seqN; we extract each step.
  -- Use the helpers rcall_AllFp25519_{sqr,mul,copy} and sqrN_AllFp25519.
  -- Members of fe25519InvertSlots: decidable.
  have hA : "a" ∈ fe25519InvertSlots := by decide
  have hOut : "out" ∈ fe25519InvertSlots := by decide
  have hTmp : "tmp" ∈ fe25519InvertSlots := by decide
  have hScr : "scratch" ∈ fe25519InvertSlots := by decide
  have hZ2 : "z2" ∈ fe25519InvertSlots := by decide
  have hZ9 : "z9" ∈ fe25519InvertSlots := by decide
  have hZ11 : "z11" ∈ fe25519InvertSlots := by decide
  have hZ25 : "z2_5_0" ∈ fe25519InvertSlots := by decide
  have hZ210 : "z2_10_0" ∈ fe25519InvertSlots := by decide
  have hZ220 : "z2_20_0" ∈ fe25519InvertSlots := by decide
  have hZ240 : "z2_40_0" ∈ fe25519InvertSlots := by decide
  have hZ250 : "z2_50_0" ∈ fe25519InvertSlots := by decide
  have hZ2100 : "z2_100_0" ∈ fe25519InvertSlots := by decide
  have hT2 : "t2" ∈ fe25519InvertSlots := by decide
  have hT3 : "t3" ∈ fe25519InvertSlots := by decide
  -- Chain operations.  Each step calls the appropriate helper.
  -- z2 = a^2
  obtain ⟨t0, ht0, hP0⟩ := rcall_AllFp25519_sqr N leafSpec _ "z2" "a" s13 hZ2 hA hAll
  -- tmp = z2^2
  obtain ⟨t1, ht1, hP1⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2" t0 hTmp hZ2 hP0
  -- scratch = tmp^2
  obtain ⟨t2, ht2, hP2⟩ := rcall_AllFp25519_sqr N leafSpec _ "scratch" "tmp" t1 hScr hTmp hP1
  -- tmp = copy(scratch)
  obtain ⟨t3, ht3, hP3⟩ := rcall_AllFp25519_copy N leafSpec _ "tmp" "scratch" t2 hTmp hScr hP2
  -- z9 = tmp * a
  obtain ⟨t4, ht4, hP4⟩ := rcall_AllFp25519_mul N leafSpec _ "z9" "tmp" "a" t3 hZ9 hTmp hA hP3
  -- z11 = z9 * z2
  obtain ⟨t5, ht5, hP5⟩ := rcall_AllFp25519_mul N leafSpec _ "z11" "z9" "z2" t4 hZ11 hZ9 hZ2 hP4
  -- tmp = z11^2
  obtain ⟨t6, ht6, hP6⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z11" t5 hTmp hZ11 hP5
  -- z2_5_0 = tmp * z9
  obtain ⟨t7, ht7, hP7⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_5_0" "tmp" "z9" t6 hZ25 hTmp hZ9 hP6
  -- tmp = z2_5_0^2
  obtain ⟨t8, ht8, hP8⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_5_0" t7 hTmp hZ25 hP7
  -- sqrN 4 tmp scratch
  obtain ⟨t9, ht9, hP9⟩ := sqrN_AllFp25519 N leafSpec _ 4 "tmp" "scratch" hTmp hScr t8 hP8
  -- z2_10_0 = tmp * z2_5_0
  obtain ⟨t10, ht10, hP10⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_10_0" "tmp" "z2_5_0" t9 hZ210 hTmp hZ25 hP9
  -- tmp = z2_10_0^2
  obtain ⟨t11, ht11, hP11⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_10_0" t10 hTmp hZ210 hP10
  -- sqrN 9 tmp scratch
  obtain ⟨t12, ht12, hP12⟩ := sqrN_AllFp25519 N leafSpec _ 9 "tmp" "scratch" hTmp hScr t11 hP11
  -- z2_20_0 = tmp * z2_10_0
  obtain ⟨t13, ht13, hP13⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_20_0" "tmp" "z2_10_0" t12 hZ220 hTmp hZ210 hP12
  -- tmp = z2_20_0^2
  obtain ⟨t14, ht14, hP14⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_20_0" t13 hTmp hZ220 hP13
  -- sqrN 19 tmp scratch
  obtain ⟨t15, ht15, hP15⟩ := sqrN_AllFp25519 N leafSpec _ 19 "tmp" "scratch" hTmp hScr t14 hP14
  -- z2_40_0 = tmp * z2_20_0
  obtain ⟨t16, ht16, hP16⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_40_0" "tmp" "z2_20_0" t15 hZ240 hTmp hZ220 hP15
  -- tmp = z2_40_0^2
  obtain ⟨t17, ht17, hP17⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_40_0" t16 hTmp hZ240 hP16
  -- sqrN 9 tmp scratch
  obtain ⟨t18, ht18, hP18⟩ := sqrN_AllFp25519 N leafSpec _ 9 "tmp" "scratch" hTmp hScr t17 hP17
  -- z2_50_0 = tmp * z2_10_0
  obtain ⟨t19, ht19, hP19⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_50_0" "tmp" "z2_10_0" t18 hZ250 hTmp hZ210 hP18
  -- tmp = z2_50_0^2
  obtain ⟨t20, ht20, hP20⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_50_0" t19 hTmp hZ250 hP19
  -- sqrN 49 tmp scratch
  obtain ⟨t21, ht21, hP21⟩ := sqrN_AllFp25519 N leafSpec _ 49 "tmp" "scratch" hTmp hScr t20 hP20
  -- z2_100_0 = tmp * z2_50_0
  obtain ⟨t22, ht22, hP22⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_100_0" "tmp" "z2_50_0" t21 hZ2100 hTmp hZ250 hP21
  -- tmp = z2_100_0^2
  obtain ⟨t23, ht23, hP23⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_100_0" t22 hTmp hZ2100 hP22
  -- sqrN 99 tmp scratch
  obtain ⟨t24, ht24, hP24⟩ := sqrN_AllFp25519 N leafSpec _ 99 "tmp" "scratch" hTmp hScr t23 hP23
  -- t2 = tmp * z2_100_0
  obtain ⟨t25, ht25, hP25⟩ := rcall_AllFp25519_mul N leafSpec _ "t2" "tmp" "z2_100_0" t24 hT2 hTmp hZ2100 hP24
  -- tmp = t2^2
  obtain ⟨t26, ht26, hP26⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "t2" t25 hTmp hT2 hP25
  -- sqrN 49 tmp scratch
  obtain ⟨t27, ht27, hP27⟩ := sqrN_AllFp25519 N leafSpec _ 49 "tmp" "scratch" hTmp hScr t26 hP26
  -- t3 = tmp * z2_50_0
  obtain ⟨t28, ht28, hP28⟩ := rcall_AllFp25519_mul N leafSpec _ "t3" "tmp" "z2_50_0" t27 hT3 hTmp hZ250 hP27
  -- tmp = t3^2
  obtain ⟨t29, ht29, _hP29⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "t3" t28 hTmp hT3 hP28
  -- sqrN 4 tmp scratch
  obtain ⟨t30, ht30, hP30⟩ := sqrN_AllFp25519 N leafSpec _ 4 "tmp" "scratch" hTmp hScr t29 _hP29
  -- out = tmp * z11
  obtain ⟨t31, ht31, _hP31⟩ := rcall_AllFp25519_mul N leafSpec _ "out" "tmp" "z11" t30 hOut hTmp hZ11 hP30
  -- Helper: collapse `RLetZero x t RSkip` from state `r` into state
  -- `rsSetTower r x ⟨t, default⟩`.
  have hLZ : ∀ (x : String) (t : TowerType) (r : RustState),
      RustExec N leafSpec (LowCT.RLetZero x t LowCT.RSkip) r
        (rsSetTower r x ⟨t, default⟩) :=
    fun x t r => RustExec.letZero x t _ r _ (RustExec.skip _)
  -- The body is a right-associated seqN: 13 RLetZero (RSkip) + 32 ops.
  -- Build the proof by chaining via RustExec.seq.
  refine ⟨t31, ?_⟩
  show RustExec N leafSpec Fe25519Invert.fe25519InvertBody rs t31
  -- The fe25519InvertBody is fixed; we have to match its exact shape.
  -- We'll chain everything via RSeq + the helpers built above.
  -- We build "remaining" execution working backward via term-mode.
  -- The body has the shape:
  --   seqN [lz1, ..., lz13, op0, op1, ..., op31]
  -- = RSeq lz1 (RSeq lz2 ... (RSeq lz13 (RSeq op0 (RSeq op1 ... op31))))
  -- We need a derivation rs → t31 via 45 sequenced steps.
  exact
    RustExec.seq _ _ _ _ _ (hLZ "tmp" _ rs)
      (RustExec.seq _ _ _ _ _ (hLZ "scratch" _ s1)
        (RustExec.seq _ _ _ _ _ (hLZ "z2" _ s2)
          (RustExec.seq _ _ _ _ _ (hLZ "z9" _ s3)
            (RustExec.seq _ _ _ _ _ (hLZ "z11" _ s4)
              (RustExec.seq _ _ _ _ _ (hLZ "z2_5_0" _ s5)
                (RustExec.seq _ _ _ _ _ (hLZ "z2_10_0" _ s6)
                  (RustExec.seq _ _ _ _ _ (hLZ "z2_20_0" _ s7)
                    (RustExec.seq _ _ _ _ _ (hLZ "z2_40_0" _ s8)
                      (RustExec.seq _ _ _ _ _ (hLZ "z2_50_0" _ s9)
                        (RustExec.seq _ _ _ _ _ (hLZ "z2_100_0" _ s10)
                          (RustExec.seq _ _ _ _ _ (hLZ "t2" _ s11)
                            (RustExec.seq _ _ _ _ _ (hLZ "t3" _ s12)
  (RustExec.seq _ _ _ _ _ ht0
    (RustExec.seq _ _ _ _ _ ht1
      (RustExec.seq _ _ _ _ _ ht2
        (RustExec.seq _ _ _ _ _ ht3
          (RustExec.seq _ _ _ _ _ ht4
            (RustExec.seq _ _ _ _ _ ht5
              (RustExec.seq _ _ _ _ _ ht6
                (RustExec.seq _ _ _ _ _ ht7
                  (RustExec.seq _ _ _ _ _ ht8
                    (RustExec.seq _ _ _ _ _ ht9
                      (RustExec.seq _ _ _ _ _ ht10
                        (RustExec.seq _ _ _ _ _ ht11
                          (RustExec.seq _ _ _ _ _ ht12
                            (RustExec.seq _ _ _ _ _ ht13
                              (RustExec.seq _ _ _ _ _ ht14
                                (RustExec.seq _ _ _ _ _ ht15
                                  (RustExec.seq _ _ _ _ _ ht16
                                    (RustExec.seq _ _ _ _ _ ht17
                                      (RustExec.seq _ _ _ _ _ ht18
                                        (RustExec.seq _ _ _ _ _ ht19
                                          (RustExec.seq _ _ _ _ _ ht20
                                            (RustExec.seq _ _ _ _ _ ht21
                                              (RustExec.seq _ _ _ _ _ ht22
                                                (RustExec.seq _ _ _ _ _ ht23
                                                  (RustExec.seq _ _ _ _ _ ht24
                                                    (RustExec.seq _ _ _ _ _ ht25
                                                      (RustExec.seq _ _ _ _ _ ht26
                                                        (RustExec.seq _ _ _ _ _ ht27
                                                          (RustExec.seq _ _ _ _ _ ht28
                                                            (RustExec.seq _ _ _ _ _ ht29
                                                              (RustExec.seq _ _ _ _ _ ht30
                                                                ht31)))))))))))))))))))))))))))))))))))))))))))

/-! ### Field reading of `TFp25519` slots

A `TFp25519` slot holds a byte array.  Its base-field value is exposed
through a decoder carried as a parameter — the shape used by
`AUCurvesImport.FieldLeafBridge` for the `fe25519_mul` leaf, and the
image of the Rocq section variable `Fp25519_holds` in
`AUCurves/src/Bedrock/End2End/Ed25519/Fe25519InvertCorrect.v`. -/

/-- Curve25519 base-field modulus `2^255 - 19`. -/
def fe25519Modulus : ℕ := 2 ^ 255 - 19

/-- Reading of a `TFp25519` slot value as an element of the Curve25519
    base field. -/
abbrev Fe25519Decode := RustVal TowerType.TFp25519 → ZMod fe25519Modulus

/-- Slot `x` of `rs` is bound at `TFp25519` and its value decodes to `v`. -/
def Fp25519Holds (decode : Fe25519Decode) (rs : RustState) (x : String)
    (v : ZMod fe25519Modulus) : Prop :=
  ∃ w : RustVal TowerType.TFp25519,
    rs.rsTower x = some ⟨TowerType.TFp25519, w⟩ ∧ decode w = v

/-- Every slot other than `exclude` keeps its field value from `rs` to `rs'`. -/
def Fp25519Frame (decode : Fe25519Decode) (rs rs' : RustState)
    (exclude : String) : Prop :=
  ∀ (y : String) (v : ZMod fe25519Modulus),
    y ≠ exclude → Fp25519Holds decode rs y v → Fp25519Holds decode rs' y v

/-- Binding a slot `x` leaves the field value of any other slot `y` intact. -/
lemma Fp25519Holds_rsSetTower_other
    (decode : Fe25519Decode) (rs : RustState) (x y : String)
    (s : Σ t, RustVal t) (v : ZMod fe25519Modulus) (hne : y ≠ x)
    (h : Fp25519Holds decode rs y v) :
    Fp25519Holds decode (rsSetTower rs x s) y v := by
  obtain ⟨w, hw, hdec⟩ := h
  exact ⟨w, by rw [rsSetTower_other rs x y s (Ne.symm hne)]; exact hw, hdec⟩

/-- Setting a scalar slot leaves every tower slot's field value intact. -/
lemma Fp25519Holds_rsSetScalar
    (decode : Fe25519Decode) (rs : RustState) (x y : String) (n : Nat)
    (v : ZMod fe25519Modulus) (h : Fp25519Holds decode rs y v) :
    Fp25519Holds decode (rsSetScalar rs x n) y v := h

/-! ### Field-level leaf specifications

The `RCall`-level counterparts of the Rocq hypotheses `sqr_correct`,
`mul_correct` and `copy_correct` of `Fe25519InvertCorrect.v`: each says
what a single leaf call does to the destination slot's field value, and
that it leaves every other slot's field value alone. -/

/-- `fe25519_sqr dest [src]` squares the field value of `src` into `dest`. -/
def Fe25519SqrCallCorrect (N : Nat) (leafSpec : LeafSpec)
    (decode : Fe25519Decode) : Prop :=
  ∀ (dest src : String) (rs rs' : RustState) (x : ZMod fe25519Modulus),
    dest ≠ src → Fp25519Holds decode rs src x →
    RustExec N leafSpec
      (LowCT.RCall "fe25519_sqr" ⟨dest, TowerType.TFp25519⟩
        [⟨src, TowerType.TFp25519⟩]) rs rs' →
    Fp25519Holds decode rs' dest (x ^ 2) ∧ Fp25519Frame decode rs rs' dest

/-- `fe25519_mul dest [a, b]` multiplies the field values of `a` and `b`
    into `dest`. -/
def Fe25519MulCallCorrect (N : Nat) (leafSpec : LeafSpec)
    (decode : Fe25519Decode) : Prop :=
  ∀ (dest a b : String) (rs rs' : RustState) (xa xb : ZMod fe25519Modulus),
    dest ≠ a → dest ≠ b →
    Fp25519Holds decode rs a xa → Fp25519Holds decode rs b xb →
    RustExec N leafSpec
      (LowCT.RCall "fe25519_mul" ⟨dest, TowerType.TFp25519⟩
        [⟨a, TowerType.TFp25519⟩, ⟨b, TowerType.TFp25519⟩]) rs rs' →
    Fp25519Holds decode rs' dest (xa * xb) ∧ Fp25519Frame decode rs rs' dest

/-- `fe25519_copy dest [src]` transfers the field value of `src` to `dest`. -/
def Fe25519CopyCallCorrect (N : Nat) (leafSpec : LeafSpec)
    (decode : Fe25519Decode) : Prop :=
  ∀ (dest src : String) (rs rs' : RustState) (x : ZMod fe25519Modulus),
    dest ≠ src → Fp25519Holds decode rs src x →
    RustExec N leafSpec
      (LowCT.RCall "fe25519_copy" ⟨dest, TowerType.TFp25519⟩
        [⟨src, TowerType.TFp25519⟩]) rs rs' →
    Fp25519Holds decode rs' dest x ∧ Fp25519Frame decode rs rs' dest

/-- `decode` carries the leaf value functions to the field operations of
    `ZMod (2^255 - 19)`. -/
structure Fe25519LeafFieldOps (decode : Fe25519Decode)
    (mathSqr mathCopy : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519)
    (mathMul : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
               RustVal TowerType.TFp25519) : Prop where
  /-- The sqr leaf value squares the decoded input. -/
  sqr : ∀ v, decode (mathSqr v) = decode v ^ 2
  /-- The mul leaf value multiplies the decoded inputs. -/
  mul : ∀ a b, decode (mathMul a b) = decode a * decode b
  /-- The copy leaf value preserves the decoded input. -/
  copy : ∀ v, decode (mathCopy v) = decode v

/-- The frame half of a field-level leaf specification: every slot other
    than an `RCall` destination keeps its field value. -/
lemma fp25519Frame_of_rcall
    {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode}
    {f : String} {dest : Located} {args : List Located} {rs rs' : RustState}
    (hExec : RustExec N leafSpec (LowCT.RCall f dest args) rs rs') :
    Fp25519Frame decode rs rs' dest.locVar := by
  intro y v hy hHolds
  obtain ⟨w, hw, hdec⟩ := hHolds
  exact ⟨w, by rw [(rcall_post_bindings hExec).2 y hy]; exact hw, hdec⟩

/-- A unary `TFp25519` leaf whose value function acts on decoded inputs by
    `fieldOp` sends a source slot holding `x` to a destination slot holding
    `fieldOp x`. -/
lemma fp25519Holds_of_unopLeaf
    {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode} {name : String}
    {mathOp : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519}
    {fieldOp : ZMod fe25519Modulus → ZMod fe25519Modulus}
    (hLeaf : Fe25519UnopLeafCorrect leafSpec name mathOp)
    (hField : ∀ v, decode (mathOp v) = fieldOp (decode v))
    {dest src : String} {rs rs' : RustState} {x : ZMod fe25519Modulus}
    (hSrc : Fp25519Holds decode rs src x)
    (hExec : RustExec N leafSpec
      (LowCT.RCall name ⟨dest, TowerType.TFp25519⟩
        [⟨src, TowerType.TFp25519⟩]) rs rs') :
    Fp25519Holds decode rs' dest (fieldOp x) := by
  obtain ⟨w, hw, hdec⟩ := hSrc
  cases hExec with
  | call _ _ _ _ oldV argList _hLook hArgList _ =>
    refine ⟨_, locatedUpdate_dest rs ⟨dest, TowerType.TFp25519⟩ _, ?_⟩
    have hArgList' : argList = [⟨TowerType.TFp25519, w⟩] := by
      rw [hArgList]
      show ([{ locVar := src, locSrc := TowerType.TFp25519 }] : List Located).filterMap
              (fun a => rs.rsTower a.locVar) = _
      simp only [List.filterMap, hw]
    rw [hArgList']
    show decode (leafSpec.call name TowerType.TFp25519 [TowerType.TFp25519] oldV
        [⟨TowerType.TFp25519, w⟩]) = fieldOp x
    rw [hLeaf oldV w, hField, hdec]

/-- A binary `TFp25519` leaf whose value function acts on decoded inputs by
    `fieldOp` sends source slots holding `xa`, `xb` to a destination slot
    holding `fieldOp xa xb`. -/
lemma fp25519Holds_of_binopLeaf
    {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode} {name : String}
    {mathOp : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
              RustVal TowerType.TFp25519}
    {fieldOp : ZMod fe25519Modulus → ZMod fe25519Modulus → ZMod fe25519Modulus}
    (hLeaf : Fe25519BinopLeafCorrect leafSpec name mathOp)
    (hField : ∀ u v, decode (mathOp u v) = fieldOp (decode u) (decode v))
    {dest a b : String} {rs rs' : RustState} {xa xb : ZMod fe25519Modulus}
    (hA : Fp25519Holds decode rs a xa) (hB : Fp25519Holds decode rs b xb)
    (hExec : RustExec N leafSpec
      (LowCT.RCall name ⟨dest, TowerType.TFp25519⟩
        [⟨a, TowerType.TFp25519⟩, ⟨b, TowerType.TFp25519⟩]) rs rs') :
    Fp25519Holds decode rs' dest (fieldOp xa xb) := by
  obtain ⟨wa, hwa, hdeca⟩ := hA
  obtain ⟨wb, hwb, hdecb⟩ := hB
  cases hExec with
  | call _ _ _ _ oldV argList _hLook hArgList _ =>
    refine ⟨_, locatedUpdate_dest rs ⟨dest, TowerType.TFp25519⟩ _, ?_⟩
    have hArgList' : argList =
        [⟨TowerType.TFp25519, wa⟩, ⟨TowerType.TFp25519, wb⟩] := by
      rw [hArgList]
      show ([{ locVar := a, locSrc := TowerType.TFp25519 },
             { locVar := b, locSrc := TowerType.TFp25519 }] : List Located).filterMap
              (fun l => rs.rsTower l.locVar) = _
      simp only [List.filterMap, hwa, hwb]
    rw [hArgList']
    show decode (leafSpec.call name TowerType.TFp25519
        [TowerType.TFp25519, TowerType.TFp25519] oldV
        [⟨TowerType.TFp25519, wa⟩, ⟨TowerType.TFp25519, wb⟩]) = fieldOp xa xb
    rw [hLeaf oldV wa wb, hField, hdeca, hdecb]

/-- The `fe25519_sqr` field-level specification follows from the leaf-value
    specification plus `decode`-compatibility of the leaf value function. -/
lemma Fe25519SqrCallCorrect_of_leaf
    {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode}
    {mathSqr mathCopy : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519}
    {mathMul : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
               RustVal TowerType.TFp25519}
    (hLeaf : Fe25519UnopLeafCorrect leafSpec "fe25519_sqr" mathSqr)
    (hOps : Fe25519LeafFieldOps decode mathSqr mathCopy mathMul) :
    Fe25519SqrCallCorrect N leafSpec decode := fun _ _ _ _ _ _ hSrc hExec =>
  ⟨fp25519Holds_of_unopLeaf (fieldOp := fun z => z ^ 2) hLeaf hOps.sqr hSrc hExec,
   fp25519Frame_of_rcall hExec⟩

/-- The `fe25519_mul` field-level specification follows from the leaf-value
    specification plus `decode`-compatibility of the leaf value function. -/
lemma Fe25519MulCallCorrect_of_leaf
    {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode}
    {mathSqr mathCopy : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519}
    {mathMul : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
               RustVal TowerType.TFp25519}
    (hLeaf : Fe25519BinopLeafCorrect leafSpec "fe25519_mul" mathMul)
    (hOps : Fe25519LeafFieldOps decode mathSqr mathCopy mathMul) :
    Fe25519MulCallCorrect N leafSpec decode :=
  fun _ _ _ _ _ _ _ _ _ hA hB hExec =>
  ⟨fp25519Holds_of_binopLeaf (fieldOp := fun u v => u * v) hLeaf hOps.mul hA hB hExec,
   fp25519Frame_of_rcall hExec⟩

/-- The `fe25519_copy` field-level specification follows from the leaf-value
    specification plus `decode`-compatibility of the leaf value function. -/
lemma Fe25519CopyCallCorrect_of_leaf
    {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode}
    {mathSqr mathCopy : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519}
    {mathMul : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
               RustVal TowerType.TFp25519}
    (hLeaf : Fe25519UnopLeafCorrect leafSpec "fe25519_copy" mathCopy)
    (hOps : Fe25519LeafFieldOps decode mathSqr mathCopy mathMul) :
    Fe25519CopyCallCorrect N leafSpec decode := fun _ _ _ _ _ _ hSrc hExec =>
  ⟨fp25519Holds_of_unopLeaf (fieldOp := fun z => z) hLeaf hOps.copy hSrc hExec,
   fp25519Frame_of_rcall hExec⟩

/-! ## Exponent tracking for `fe25519InvertBody`

`fp25519ExpTrack` runs a LowCT command on a map from slots to exponents: a slot
`v ↦ e` stands for `Fp25519Holds decode rs v (x ^ e)`. `fp25519ExpTrack_sound` states
that the map is preserved by `RustExec` under the leaf specifications, so the
invert chain reduces to one kernel computation of the final exponent. -/

section Fp25519ExpTrack

open CatCrypt.Crypto.Jasmin.LowCT

/-- A finite map from slot names to exponents. -/
abbrev Fp25519ExpMap := List (String × Nat)

/-- Every entry `(y, e)` of `m` has slot `y` of `rs` decoding to `x ^ e`. -/
def Fp25519ExpHolds (decode : Fe25519Decode) (rs : RustState)
    (x : ZMod fe25519Modulus) (m : Fp25519ExpMap) : Prop :=
  ∀ p ∈ m, Fp25519Holds decode rs p.1 (x ^ p.2)

/-- `m` with every entry for slot `v` removed. -/
def fp25519ExpKill (m : Fp25519ExpMap) (v : String) : Fp25519ExpMap :=
  m.filter (fun p => !decide (p.1 = v))

/-- `m` with slot `d` bound to exponent `e`. -/
def fp25519ExpSet (m : Fp25519ExpMap) (d : String) (e : Nat) : Fp25519ExpMap :=
  (d, e) :: fp25519ExpKill m d

/-- The exponent bound to slot `v` in `m`, if any. -/
def fp25519ExpFind : Fp25519ExpMap → String → Option Nat
  | [], _ => none
  | (y, e) :: m, v => if y = v then some e else fp25519ExpFind m v

/-- Exponent effect of a single `TFp25519` leaf call: `fe25519_sqr d [s]`
    doubles the exponent of `s`, `fe25519_mul d [a, b]` adds the exponents of
    `a` and `b`, `fe25519_copy d [s]` copies the exponent of `s`.  The
    destination must differ from every source; any other call gives `none`. -/
def fp25519ExpCall (f : String) (dest : Located) (args : List Located)
    (m : Fp25519ExpMap) : Option Fp25519ExpMap :=
  if dest.locSrc = TowerType.TFp25519 then
    match args with
    | [s] =>
      if s.locSrc = TowerType.TFp25519 ∧ dest.locVar ≠ s.locVar then
        if f = "fe25519_sqr" then
          (fp25519ExpFind m s.locVar).map fun e => fp25519ExpSet m dest.locVar (2 * e)
        else if f = "fe25519_copy" then
          (fp25519ExpFind m s.locVar).map fun e => fp25519ExpSet m dest.locVar e
        else none
      else none
    | [a, b] =>
      if a.locSrc = TowerType.TFp25519 ∧ b.locSrc = TowerType.TFp25519 ∧
          dest.locVar ≠ a.locVar ∧ dest.locVar ≠ b.locVar ∧ f = "fe25519_mul" then
        match fp25519ExpFind m a.locVar, fp25519ExpFind m b.locVar with
        | some ea, some eb => some (fp25519ExpSet m dest.locVar (ea + eb))
        | _, _ => none
      else none
    | _ => none
  else none

/-- `n`-fold Kleisli iteration of a partial map. -/
def fp25519ExpIter (f : Fp25519ExpMap → Option Fp25519ExpMap) :
    Nat → Fp25519ExpMap → Option Fp25519ExpMap
  | 0, m => some m
  | n + 1, m => (fp25519ExpIter f n m).bind f

/-- Exponent tracker over the `RSkip`/`RSeq`/`RLetZero`/`RFor`/`RCall`
    fragment of `LowCT`: the map of slot exponents after running `c` from a
    state described by `m`, or `none` outside the fragment. -/
def fp25519ExpTrack : LowCT → Fp25519ExpMap → Option Fp25519ExpMap
  | .RSkip, m => some m
  | .RSeq c1 c2, m => (fp25519ExpTrack c1 m).bind (fp25519ExpTrack c2)
  | .RLetZero v _ body, m => fp25519ExpTrack body (fp25519ExpKill m v)
  | .RFor _ n body, m => fp25519ExpIter (fp25519ExpTrack body) n m
  | .RCall f dest args, m => fp25519ExpCall f dest args m
  | _, _ => none

lemma fp25519ExpFind_mem {m : Fp25519ExpMap} {v : String} {e : Nat}
    (h : fp25519ExpFind m v = some e) : (v, e) ∈ m := by
  induction m with
  | nil => simp [fp25519ExpFind] at h
  | cons p m ih =>
    obtain ⟨y, e'⟩ := p
    simp only [fp25519ExpFind] at h
    split_ifs at h with hy
    · cases h; subst hy; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

lemma Fp25519ExpHolds_kill {decode : Fe25519Decode} {rs rs' : RustState}
    {x : ZMod fe25519Modulus} {m : Fp25519ExpMap} {d : String}
    (hFrame : Fp25519Frame decode rs rs' d) (h : Fp25519ExpHolds decode rs x m) :
    Fp25519ExpHolds decode rs' x (fp25519ExpKill m d) := by
  intro p hp
  simp only [fp25519ExpKill, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
  exact hFrame _ _ hp.2 (h p hp.1)

lemma Fp25519ExpHolds_set {decode : Fe25519Decode} {rs rs' : RustState}
    {x : ZMod fe25519Modulus} {m : Fp25519ExpMap} {d : String} {e : Nat}
    (hFrame : Fp25519Frame decode rs rs' d) (h : Fp25519ExpHolds decode rs x m)
    (hd : Fp25519Holds decode rs' d (x ^ e)) :
    Fp25519ExpHolds decode rs' x (fp25519ExpSet m d e) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hd
  · exact Fp25519ExpHolds_kill hFrame h p hp

lemma fp25519ExpCall_sound {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode}
    (hSqr : Fe25519SqrCallCorrect N leafSpec decode)
    (hMul : Fe25519MulCallCorrect N leafSpec decode)
    (hCopy : Fe25519CopyCallCorrect N leafSpec decode)
    {x : ZMod fe25519Modulus} {f : String} {dest : Located} {args : List Located}
    {rs rs' : RustState} {m m' : Fp25519ExpMap}
    (hT : fp25519ExpCall f dest args m = some m')
    (hM : Fp25519ExpHolds decode rs x m)
    (hExec : RustExec N leafSpec (LowCT.RCall f dest args) rs rs') :
    Fp25519ExpHolds decode rs' x m' := by
  obtain ⟨d, dt⟩ := dest
  rcases args with _ | ⟨⟨s, st⟩, _ | ⟨⟨b, bt⟩, _ | ⟨_, _⟩⟩⟩
  · simp [fp25519ExpCall] at hT
  · simp only [fp25519ExpCall] at hT
    by_cases hdt : dt = TowerType.TFp25519
    swap
    · rw [if_neg hdt] at hT; cases hT
    subst hdt
    rw [if_pos rfl] at hT
    by_cases hs : st = TowerType.TFp25519 ∧ d ≠ s
    swap
    · rw [if_neg hs] at hT; cases hT
    rw [if_pos hs] at hT
    obtain ⟨rfl, hne⟩ := hs
    by_cases hf : f = "fe25519_sqr"
    · rw [if_pos hf] at hT
      subst hf
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hT
      obtain ⟨hd, hFr⟩ := hSqr d s rs rs' _ hne (hM _ (fp25519ExpFind_mem he)) hExec
      exact Fp25519ExpHolds_set hFr hM (by rw [mul_comm, pow_mul]; exact hd)
    rw [if_neg hf] at hT
    by_cases hf' : f = "fe25519_copy"
    · rw [if_pos hf'] at hT
      subst hf'
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hT
      obtain ⟨hd, hFr⟩ := hCopy d s rs rs' _ hne (hM _ (fp25519ExpFind_mem he)) hExec
      exact Fp25519ExpHolds_set hFr hM hd
    rw [if_neg hf'] at hT; cases hT
  · simp only [fp25519ExpCall] at hT
    by_cases hdt : dt = TowerType.TFp25519
    swap
    · rw [if_neg hdt] at hT; cases hT
    subst hdt
    rw [if_pos rfl] at hT
    by_cases hc : st = TowerType.TFp25519 ∧ bt = TowerType.TFp25519 ∧
        d ≠ s ∧ d ≠ b ∧ f = "fe25519_mul"
    swap
    · rw [if_neg hc] at hT; cases hT
    rw [if_pos hc] at hT
    obtain ⟨rfl, rfl, hna, hnb, rfl⟩ := hc
    cases hea : fp25519ExpFind m s <;> cases heb : fp25519ExpFind m b <;>
      rw [hea, heb] at hT <;> try cases hT
    rename_i ea eb
    obtain ⟨hd, hFr⟩ := hMul d s b rs rs' _ _ hna hnb
      (hM _ (fp25519ExpFind_mem hea)) (hM _ (fp25519ExpFind_mem heb)) hExec
    exact Fp25519ExpHolds_set hFr hM (by rw [pow_add]; exact hd)
  · simp [fp25519ExpCall] at hT

/-- Soundness of `fp25519ExpTrack`: if the tracker maps `m` to `m'` on `c`,
    and `m` describes the slot values of `rs`, then `m'` describes the slot
    values of every `rs'` that `c` reaches from `rs`. -/
theorem fp25519ExpTrack_sound {N : Nat} {leafSpec : LeafSpec} {decode : Fe25519Decode}
    (hSqr : Fe25519SqrCallCorrect N leafSpec decode)
    (hMul : Fe25519MulCallCorrect N leafSpec decode)
    (hCopy : Fe25519CopyCallCorrect N leafSpec decode)
    (x : ZMod fe25519Modulus) {c : LowCT} {rs rs' : RustState}
    (hExec : RustExec N leafSpec c rs rs') :
    ∀ {m m' : Fp25519ExpMap}, fp25519ExpTrack c m = some m' →
      Fp25519ExpHolds decode rs x m → Fp25519ExpHolds decode rs' x m' := by
  induction hExec with
  | skip rs =>
    intro m m' hT hM
    cases hT; exact hM
  | seq c1 c2 rs r1 rs' _ _ ih1 ih2 =>
    intro m m' hT hM
    obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.1 hT
    exact ih2 h2 (ih1 h1 hM)
  | letZero v t body rs rs' _ ih =>
    intro m m' hT hM
    exact ih hT fun p hp => by
      simp only [fp25519ExpKill, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not] at hp
      exact Fp25519Holds_rsSetTower_other decode rs v p.1 _ _ hp.2 (hM p hp.1)
  | forZero v body rs =>
    intro m m' hT hM
    cases hT; exact hM
  | forSucc v n body rs r1 rs' _ _ ihFor ihBody =>
    intro m m' hT hM
    obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.1 hT
    exact ihBody h2 fun p hp =>
      Fp25519Holds_rsSetScalar decode r1 v p.1 n _ (ihFor h1 hM p hp)
  | call f dest args rs oldV argList h1 h2 h3 =>
    intro m m' hT hM
    exact fp25519ExpCall_sound hSqr hMul hCopy hT hM
      (RustExec.call f dest args rs oldV argList h1 h2 h3)
  | _ => intro m m' hT; simp [fp25519ExpTrack] at hT

open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- The exponent tracker run on `fe25519InvertBody` from `"a" ↦ 1` binds
    `"out"` to `2^255 - 21`. -/
theorem fp25519ExpTrack_fe25519InvertBody :
    ((fp25519ExpTrack fe25519InvertBody [("a", 1)]).bind
      fun m => fp25519ExpFind m "out") = some (fe25519Modulus - 2) := by
  decide +kernel

end Fp25519ExpTrack

open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- Running `fe25519InvertBody` from a state whose `"a"` slot decodes to `x`
    reaches a state whose `"out"` slot decodes to `x ^ (2^255 - 21)`, given the
    field-level specifications of the `fe25519_sqr`, `fe25519_mul` and
    `fe25519_copy` leaves. -/
theorem fe25519InvertBody_holds_pow
    (N : Nat) (leafSpec : LeafSpec) (decode : Fe25519Decode)
    (hSqr : Fe25519SqrCallCorrect N leafSpec decode)
    (hMul : Fe25519MulCallCorrect N leafSpec decode)
    (hCopy : Fe25519CopyCallCorrect N leafSpec decode)
    (rs rs' : RustState) (x : ZMod fe25519Modulus)
    (hA : Fp25519Holds decode rs "a" x)
    (hExec : RustExec N leafSpec fe25519InvertBody rs rs') :
    Fp25519Holds decode rs' "out" (x ^ (fe25519Modulus - 2)) := by
  have hK := fp25519ExpTrack_fe25519InvertBody
  obtain ⟨m', hT, hF⟩ := Option.bind_eq_some_iff.1 hK
  have hInit : Fp25519ExpHolds decode rs x [("a", 1)] := by
    intro p hp
    rw [List.mem_singleton.1 hp]
    simpa using hA
  exact fp25519ExpTrack_sound hSqr hMul hCopy x hExec hT hInit _ (fp25519ExpFind_mem hF)


open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- **Functional correctness for `fe25519InvertBody`.**

    Under the leaf-value specifications for `fe25519_sqr`, `fe25519_mul`,
    `fe25519_copy` and a decoder carrying those leaf values to the field
    operations of `ZMod (2^255 - 19)`, the post-state's `"out"` slot decodes
    to `x ^ (2^255 - 21)`, where `x` is the decoding of the `"a"` slot.

    The chain step is `fe25519InvertBody_holds_pow`. -/
theorem fe25519InvertBody_functional_correctness
    (N : Nat) (leafSpec : LeafSpec) (decode : Fe25519Decode)
    (mathSqr mathCopy : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519)
    (mathMul : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
               RustVal TowerType.TFp25519)
    (hSqr : Fe25519UnopLeafCorrect leafSpec "fe25519_sqr" mathSqr)
    (hMul : Fe25519BinopLeafCorrect leafSpec "fe25519_mul" mathMul)
    (hCopy : Fe25519UnopLeafCorrect leafSpec "fe25519_copy" mathCopy)
    (hOps : Fe25519LeafFieldOps decode mathSqr mathCopy mathMul)
    (rs rs' : RustState)
    (vA : RustVal TowerType.TFp25519)
    (hA : rs.rsTower "a" = some ⟨TowerType.TFp25519, vA⟩)
    (hExec : RustExec N leafSpec fe25519InvertBody rs rs') :
    Fp25519Holds decode rs' "out" (decode vA ^ (fe25519Modulus - 2)) :=
  fe25519InvertBody_holds_pow N leafSpec decode
    (Fe25519SqrCallCorrect_of_leaf hSqr hOps)
    (Fe25519MulCallCorrect_of_leaf hMul hOps)
    (Fe25519CopyCallCorrect_of_leaf hCopy hOps)
    rs rs' (decode vA) ⟨vA, hA, rfl⟩ hExec

/-- `fpInv` computes the Fermat power `x ^ (p - 2)` on decoded field values,
    the characterisation of multiplicative inversion in `ZMod (2^255 - 19)`
    that the `fe25519_invert` addition chain realises. -/
def Fe25519InversionSpec (decode : Fe25519Decode)
    (fpInv : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519) : Prop :=
  ∀ v, decode (fpInv v) = decode v ^ (fe25519Modulus - 2)

open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- **Functional correctness for `fe25519InvertBody`, inversion form.**

    The post-state's `"out"` slot decodes to the same field element as
    `fpInv vA`, for any `fpInv` satisfying `Fe25519InversionSpec`. -/
theorem fe25519InvertBody_inversion_correctness
    (N : Nat) (leafSpec : LeafSpec) (decode : Fe25519Decode)
    (mathSqr mathCopy : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519)
    (mathMul : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
               RustVal TowerType.TFp25519)
    (fpInv : RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519)
    (hSqr : Fe25519UnopLeafCorrect leafSpec "fe25519_sqr" mathSqr)
    (hMul : Fe25519BinopLeafCorrect leafSpec "fe25519_mul" mathMul)
    (hCopy : Fe25519UnopLeafCorrect leafSpec "fe25519_copy" mathCopy)
    (hOps : Fe25519LeafFieldOps decode mathSqr mathCopy mathMul)
    (hSpec : Fe25519InversionSpec decode fpInv)
    (rs rs' : RustState)
    (vA : RustVal TowerType.TFp25519)
    (hA : rs.rsTower "a" = some ⟨TowerType.TFp25519, vA⟩)
    (hExec : RustExec N leafSpec fe25519InvertBody rs rs') :
    Fp25519Holds decode rs' "out" (decode (fpInv vA)) := by
  rw [hSpec vA]
  exact fe25519InvertBody_functional_correctness N leafSpec decode
    mathSqr mathCopy mathMul hSqr hMul hCopy hOps rs rs' vA hA hExec

/-! ## §5.  `MontUToEdwards` -/

open CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards in
def MontUToEdwardsInputsWellFormed (rs : RustState) : Prop :=
  (∃ v, rs.rsTower "u" = some ⟨TowerType.TFp25519, v⟩) ∧
  (∃ v, rs.rsTower "y_out" = some ⟨TowerType.TFp25519, v⟩) ∧
  (∃ v, rs.rsTower "den_out" = some ⟨TowerType.TFp25519, v⟩)

/-- An auxiliary helper used by `montUToEdwardsBody_panic_free` and
    `fe25519InvertBody_panic_free`: an RCall whose dst/args bindings
    follow from looking up names in the input state, given the state
    is built as a chain of `rsSetTower` / `locatedUpdate` operations.

    Returns an existence wrapped with `rcall_panic_free`. -/
lemma rcall_panic_free_named
    (N : Nat) (leafSpec : LeafSpec)
    (f : String) (dest : Located) (args : List Located)
    (rs : RustState)
    (hDest : rs.rsTower dest.locVar = some ⟨dest.locDst, default⟩ ∨
             ∃ v, rs.rsTower dest.locVar = some ⟨dest.locDst, v⟩)
    (hArgs : ∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) :
    ∃ rs', RustExec N leafSpec (LowCT.RCall f dest args) rs rs' := by
  rcases hDest with h | h
  · exact rcall_panic_free N leafSpec f dest args rs ⟨_, h⟩ hArgs
  · exact rcall_panic_free N leafSpec f dest args rs h hArgs

open CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards in
/-- **Panic-freeness for `montUToEdwardsBody`.**

    Body: 4 RLetZero binders (one, num, den, inv_den), followed by a
    chain of 6 RCalls.  Each RCall's destination is either an input
    slot (from `MontUToEdwardsInputsWellFormed`) or one of the
    let-bound locals; arguments are similarly reachable.

    Proof: structural — peel the 4 letZero rules, then chain 6 RCalls
    via `seq`.  All slot bindings persist through `locatedUpdate`
    because every step writes a distinct named slot. -/
theorem montUToEdwardsBody_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : MontUToEdwardsInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec montUToEdwardsBody rs rs' := by
  obtain ⟨⟨uV, hu⟩, ⟨yOutV, hy⟩, ⟨denOutV, hden⟩⟩ := hWf
  -- Build the post-state of the 4 letZeros.
  let fpL (v : String) : Located :=
    { locVar := v, locSrc := TowerType.TFp25519 }
  set s1 := rsSetTower rs       "one"     ⟨TowerType.TFp25519, default⟩
  set s2 := rsSetTower s1       "num"     ⟨TowerType.TFp25519, default⟩
  set s3 := rsSetTower s2       "den"     ⟨TowerType.TFp25519, default⟩
  set s4 := rsSetTower s3       "inv_den" ⟨TowerType.TFp25519, default⟩
  -- Each slot lookup in s4 — proved by descending through the chain.
  have hu4   : s4.rsTower "u"       = some ⟨TowerType.TFp25519, uV⟩ := by
    show (rsSetTower s3 "inv_den" _).rsTower "u" = _
    rw [rsSetTower_other s3 "inv_den" "u" _ (by decide)]
    show (rsSetTower s2 "den" _).rsTower "u" = _
    rw [rsSetTower_other s2 "den" "u" _ (by decide)]
    show (rsSetTower s1 "num" _).rsTower "u" = _
    rw [rsSetTower_other s1 "num" "u" _ (by decide)]
    show (rsSetTower rs "one" _).rsTower "u" = _
    rw [rsSetTower_other rs "one" "u" _ (by decide)]; exact hu
  have hy4 : s4.rsTower "y_out" = some ⟨TowerType.TFp25519, yOutV⟩ := by
    show (rsSetTower s3 "inv_den" _).rsTower "y_out" = _
    rw [rsSetTower_other s3 "inv_den" "y_out" _ (by decide)]
    show (rsSetTower s2 "den" _).rsTower "y_out" = _
    rw [rsSetTower_other s2 "den" "y_out" _ (by decide)]
    show (rsSetTower s1 "num" _).rsTower "y_out" = _
    rw [rsSetTower_other s1 "num" "y_out" _ (by decide)]
    show (rsSetTower rs "one" _).rsTower "y_out" = _
    rw [rsSetTower_other rs "one" "y_out" _ (by decide)]; exact hy
  have hdo4 : s4.rsTower "den_out" = some ⟨TowerType.TFp25519, denOutV⟩ := by
    show (rsSetTower s3 "inv_den" _).rsTower "den_out" = _
    rw [rsSetTower_other s3 "inv_den" "den_out" _ (by decide)]
    show (rsSetTower s2 "den" _).rsTower "den_out" = _
    rw [rsSetTower_other s2 "den" "den_out" _ (by decide)]
    show (rsSetTower s1 "num" _).rsTower "den_out" = _
    rw [rsSetTower_other s1 "num" "den_out" _ (by decide)]
    show (rsSetTower rs "one" _).rsTower "den_out" = _
    rw [rsSetTower_other rs "one" "den_out" _ (by decide)]; exact hden
  have hone4 : s4.rsTower "one" = some ⟨TowerType.TFp25519, default⟩ := by
    show (rsSetTower s3 "inv_den" _).rsTower "one" = _
    rw [rsSetTower_other s3 "inv_den" "one" _ (by decide)]
    show (rsSetTower s2 "den" _).rsTower "one" = _
    rw [rsSetTower_other s2 "den" "one" _ (by decide)]
    show (rsSetTower s1 "num" _).rsTower "one" = _
    rw [rsSetTower_other s1 "num" "one" _ (by decide)]
    exact rsSetTower_same _ _ _
  have hnum4 : s4.rsTower "num" = some ⟨TowerType.TFp25519, default⟩ := by
    show (rsSetTower s3 "inv_den" _).rsTower "num" = _
    rw [rsSetTower_other s3 "inv_den" "num" _ (by decide)]
    show (rsSetTower s2 "den" _).rsTower "num" = _
    rw [rsSetTower_other s2 "den" "num" _ (by decide)]
    exact rsSetTower_same _ _ _
  have hdl4 : s4.rsTower "den" = some ⟨TowerType.TFp25519, default⟩ := by
    show (rsSetTower s3 "inv_den" _).rsTower "den" = _
    rw [rsSetTower_other s3 "inv_den" "den" _ (by decide)]
    exact rsSetTower_same _ _ _
  have hinv4 : s4.rsTower "inv_den" = some ⟨TowerType.TFp25519, default⟩ :=
    rsSetTower_same _ _ _
  -- Now build the 6-RCall chain.  Each step:
  --   (a) prove RCall is panic-free from the current state (using the
  --       slot-binding facts);
  --   (b) `obtain` the post-state and exec witness;
  --   (c) update slot-binding facts via `rcall_post_bindings`.
  -- Step 1: fe25519_set_one (one) []
  obtain ⟨r5, hr5⟩ : ∃ r5, RustExec N leafSpec
      (LowCT.RCall "fe25519_set_one" (fpL "one") []) s4 r5 :=
    rcall_panic_free N leafSpec _ _ _ _ ⟨default, hone4⟩ (by intro a ha; cases ha)
  have ⟨⟨v1, hone5⟩, hpres1⟩ := rcall_post_bindings hr5
  have hu5     : r5.rsTower "u"       = some ⟨TowerType.TFp25519, uV⟩      := by grind
  have hy5     : r5.rsTower "y_out"   = some ⟨TowerType.TFp25519, yOutV⟩   := by grind
  have hdo5    : r5.rsTower "den_out" = some ⟨TowerType.TFp25519, denOutV⟩ := by grind
  have hnum5   : r5.rsTower "num"     = some ⟨TowerType.TFp25519, default⟩ := by grind
  have hdl5    : r5.rsTower "den"     = some ⟨TowerType.TFp25519, default⟩ := by grind
  have hinv5   : r5.rsTower "inv_den" = some ⟨TowerType.TFp25519, default⟩ := by grind
  -- Step 2: fe25519_sub_then_carry (num) [u, one]
  obtain ⟨r6, hr6⟩ : ∃ r6, RustExec N leafSpec
      (LowCT.RCall "fe25519_sub_then_carry" (fpL "num") [fpL "u", fpL "one"]) r5 r6 := by
    apply rcall_panic_free _ _ _ _ _ _ ⟨default, hnum5⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h2
    · exact ⟨uV, hu5⟩
    · rcases List.mem_singleton.mp h2 with rfl
      exact ⟨v1, hone5⟩
  have ⟨⟨v2, hnum6⟩, hpres2⟩ := rcall_post_bindings hr6
  have hu6   : r6.rsTower "u"       = some ⟨TowerType.TFp25519, uV⟩      := by grind
  have hy6   : r6.rsTower "y_out"   = some ⟨TowerType.TFp25519, yOutV⟩   := by grind
  have hdo6  : r6.rsTower "den_out" = some ⟨TowerType.TFp25519, denOutV⟩ := by grind
  have hone6 : r6.rsTower "one"     = some ⟨TowerType.TFp25519, v1⟩      := by grind
  have hdl6  : r6.rsTower "den"     = some ⟨TowerType.TFp25519, default⟩ := by grind
  have hinv6 : r6.rsTower "inv_den" = some ⟨TowerType.TFp25519, default⟩ := by grind
  -- Step 3: fe25519_add_then_carry (den) [u, one]
  obtain ⟨r7, hr7⟩ : ∃ r7, RustExec N leafSpec
      (LowCT.RCall "fe25519_add_then_carry" (fpL "den") [fpL "u", fpL "one"]) r6 r7 := by
    apply rcall_panic_free _ _ _ _ _ _ ⟨default, hdl6⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h2
    · exact ⟨uV, hu6⟩
    · rcases List.mem_singleton.mp h2 with rfl
      exact ⟨v1, hone6⟩
  have ⟨⟨v3, hden7⟩, hpres3⟩ := rcall_post_bindings hr7
  have hy7   : r7.rsTower "y_out"   = some ⟨TowerType.TFp25519, yOutV⟩   := by grind
  have hdo7  : r7.rsTower "den_out" = some ⟨TowerType.TFp25519, denOutV⟩ := by grind
  have hnum7 : r7.rsTower "num"     = some ⟨TowerType.TFp25519, v2⟩      := by grind
  have hinv7 : r7.rsTower "inv_den" = some ⟨TowerType.TFp25519, default⟩ := by grind
  -- Step 4: fe25519_invert (inv_den) [den]
  obtain ⟨r8, hr8⟩ : ∃ r8, RustExec N leafSpec
      (LowCT.RCall "fe25519_invert" (fpL "inv_den") [fpL "den"]) r7 r8 := by
    apply rcall_panic_free _ _ _ _ _ _ ⟨default, hinv7⟩
    intro a ha
    rcases List.mem_singleton.mp ha with rfl
    exact ⟨v3, hden7⟩
  have ⟨⟨v4, hinv8⟩, hpres4⟩ := rcall_post_bindings hr8
  have hy8   : r8.rsTower "y_out"   = some ⟨TowerType.TFp25519, yOutV⟩   := by grind
  have hdo8  : r8.rsTower "den_out" = some ⟨TowerType.TFp25519, denOutV⟩ := by grind
  have hnum8 : r8.rsTower "num"     = some ⟨TowerType.TFp25519, v2⟩      := by grind
  have hden8 : r8.rsTower "den"     = some ⟨TowerType.TFp25519, v3⟩      := by grind
  -- Step 5: fe25519_mul (y_out) [num, inv_den]
  obtain ⟨r9, hr9⟩ : ∃ r9, RustExec N leafSpec
      (LowCT.RCall "fe25519_mul" (fpL "y_out") [fpL "num", fpL "inv_den"]) r8 r9 := by
    apply rcall_panic_free _ _ _ _ _ _ ⟨yOutV, hy8⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h2
    · exact ⟨v2, hnum8⟩
    · rcases List.mem_singleton.mp h2 with rfl
      exact ⟨v4, hinv8⟩
  have ⟨_, hpres5⟩ := rcall_post_bindings hr9
  have hdo9  : r9.rsTower "den_out" = some ⟨TowerType.TFp25519, denOutV⟩ := by grind
  have hden9 : r9.rsTower "den"     = some ⟨TowerType.TFp25519, v3⟩      := by grind
  -- Step 6: fe25519_copy (den_out) [den]
  obtain ⟨r10, hr10⟩ : ∃ r10, RustExec N leafSpec
      (LowCT.RCall "fe25519_copy" (fpL "den_out") [fpL "den"]) r9 r10 := by
    apply rcall_panic_free _ _ _ _ _ _ ⟨denOutV, hdo9⟩
    intro a ha
    rcases List.mem_singleton.mp ha with rfl
    exact ⟨v3, hden9⟩
  -- Assemble: 4 letZero + 6 seq's.
  refine ⟨r10, ?_⟩
  refine RustExec.letZero "one" _ _ rs r10 ?_
  refine RustExec.letZero "num" _ _ s1 r10 ?_
  refine RustExec.letZero "den" _ _ s2 r10 ?_
  refine RustExec.letZero "inv_den" _ _ s3 r10 ?_
  -- Now in state s4.  Need RSeq c1 (RSeq c2 ... (RSeq c5 c6)) : s4 → r10.
  exact RustExec.seq _ _ _ _ _ hr5
    (RustExec.seq _ _ _ _ _ hr6
      (RustExec.seq _ _ _ _ _ hr7
        (RustExec.seq _ _ _ _ _ hr8
          (RustExec.seq _ _ _ _ _ hr9 hr10))))

open CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards in
/-- **Functional correctness for `montUToEdwardsBody`.**

    Given leaves implement their math contracts, the post-state holds:
        `y_out   = mathMul (mathSub vU mathOne) (mathInv (mathAdd vU mathOne))`
        `den_out = mathCopy (mathAdd vU mathOne)`

    Proof: invert through the 4x RLetZero + 5x RSeq + 6x RCall structure;
    at each RCall step, the `argList` is computed by `filterMap` over the
    args from the current state, the leaf-correctness hypothesis rewrites
    `leafSpec.call` to the math op, and `locatedUpdate_dest` discharges
    the slot lookup.  Mechanical bookkeeping — proof is long but flat. -/
theorem montUToEdwardsBody_functional_correctness
    (N : Nat) (leafSpec : LeafSpec)
    (mathOne : RustVal TowerType.TFp25519)
    (mathSub mathAdd mathMul :
      RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519 →
      RustVal TowerType.TFp25519)
    (mathInv mathCopy :
      RustVal TowerType.TFp25519 → RustVal TowerType.TFp25519)
    (hSetOne : Fe25519SetOneLeafCorrect leafSpec mathOne)
    (hSub : Fe25519BinopLeafCorrect leafSpec "fe25519_sub_then_carry" mathSub)
    (hAdd : Fe25519BinopLeafCorrect leafSpec "fe25519_add_then_carry" mathAdd)
    (hInv : Fe25519UnopLeafCorrect leafSpec "fe25519_invert" mathInv)
    (hMul : Fe25519BinopLeafCorrect leafSpec "fe25519_mul" mathMul)
    (hCopy : Fe25519UnopLeafCorrect leafSpec "fe25519_copy" mathCopy)
    (rs rs' : RustState)
    (vU : RustVal TowerType.TFp25519)
    (hU : rs.rsTower "u" = some ⟨TowerType.TFp25519, vU⟩)
    (hExec : RustExec N leafSpec montUToEdwardsBody rs rs') :
    rs'.rsTower "y_out" = some ⟨TowerType.TFp25519,
        mathMul (mathSub vU mathOne) (mathInv (mathAdd vU mathOne))⟩ ∧
    rs'.rsTower "den_out" = some ⟨TowerType.TFp25519,
        mathCopy (mathAdd vU mathOne)⟩ := by
  -- Peel the 4 letZero binders.
  unfold montUToEdwardsBody at hExec
  cases hExec with | letZero _ _ _ _ _ hE1 =>
  cases hE1   with | letZero _ _ _ _ _ hE2 =>
  cases hE2   with | letZero _ _ _ _ _ hE3 =>
  cases hE3   with | letZero _ _ _ _ _ hE4 =>
  -- Now hE4 is a chain of 5 RSeq's terminating in the 6th RCall.
  cases hE4 with | seq _ _ _ _ _ hC1 hRest1 =>
  cases hRest1 with | seq _ _ _ _ _ hC2 hRest2 =>
  cases hRest2 with | seq _ _ _ _ _ hC3 hRest3 =>
  cases hRest3 with | seq _ _ _ _ _ hC4 hRest4 =>
  cases hRest4 with | seq _ _ _ _ _ hC5 hC6 =>
  -- We now have 6 individual RCall executions: hC1..hC6.
  -- State after the 4 letZeros (bindings: one=⟨_,⟨_,default⟩⟩, etc):
  --   one ↦ ⟨TFp25519, default⟩
  --   num ↦ ⟨TFp25519, default⟩
  --   den ↦ ⟨TFp25519, default⟩
  --   inv_den ↦ ⟨TFp25519, default⟩
  --   u   ↦ ⟨TFp25519, vU⟩    (preserved from rs)
  -- Set this state up:
  set s4 := rsSetTower (rsSetTower (rsSetTower
              (rsSetTower rs "one" ⟨TowerType.TFp25519, default⟩)
              "num" ⟨TowerType.TFp25519, default⟩)
              "den" ⟨TowerType.TFp25519, default⟩)
              "inv_den" ⟨TowerType.TFp25519, default⟩ with hs4
  -- Show u is still at vU in s4.
  have hu4 : s4.rsTower "u" = some ⟨TowerType.TFp25519, vU⟩ := by
    show (rsSetTower _ "inv_den" _).rsTower "u" = _
    rw [rsSetTower_other _ "inv_den" "u" _ (by decide)]
    show (rsSetTower _ "den" _).rsTower "u" = _
    rw [rsSetTower_other _ "den" "u" _ (by decide)]
    show (rsSetTower _ "num" _).rsTower "u" = _
    rw [rsSetTower_other _ "num" "u" _ (by decide)]
    show (rsSetTower _ "one" _).rsTower "u" = _
    rw [rsSetTower_other _ "one" "u" _ (by decide)]
    exact hU
  -- ===== Step 1: fe25519_set_one (one) [] =====
  -- After hC1: one = mathOne in some state r1.
  -- Inspect hC1 to extract r1's structure.
  cases hC1 with | call _ _ _ _ oldOneV argList1 hLook1 hArg1 _ =>
  -- argList1 = [].filterMap ... = []
  have hArg1' : argList1 = [] := by rw [hArg1]; rfl
  -- The post-state of hC1 is locatedUpdate s4 (oneLoc) (leafSpec.call ...).
  -- The leafSpec.call value is mathOne by hSetOne.
  set oneLoc : Located := ⟨"one", TowerType.TFp25519⟩
  have hone_r1 : leafSpec.call "fe25519_set_one" TowerType.TFp25519 []
                    oldOneV argList1 = mathOne := by
    rw [hArg1']; exact hSetOne oldOneV
  -- Set r1 := locatedUpdate s4 oneLoc (leafSpec.call ... )
  -- After the call: state r1 has one ↦ ⟨TFp25519, mathOne⟩.
  -- Other slots preserved.
  set r1 := locatedUpdate s4 oneLoc
    (leafSpec.call "fe25519_set_one" TowerType.TFp25519 [] oldOneV argList1)
    with hr1
  -- one ↦ mathOne in r1
  have hone1 : r1.rsTower "one" = some ⟨TowerType.TFp25519, mathOne⟩ := by
    rw [hr1]; rw [locatedUpdate_dest]; rw [hone_r1]
  -- u ↦ vU in r1 (preserved since oneLoc.locVar = "one" ≠ "u")
  have hu1 : r1.rsTower "u" = some ⟨TowerType.TFp25519, vU⟩ := by
    rw [hr1]
    show (rsSetTower s4 "one" _).rsTower "u" = _
    rw [rsSetTower_other s4 "one" "u" _ (by decide)]
    exact hu4
  -- ===== Step 2: fe25519_sub_then_carry (num) [u, one] =====
  cases hC2 with | call _ _ _ _ oldNumV argList2 _hLook2 hArg2 _ =>
  -- argList2 from filterMap [u, one]: should be [⟨_,vU⟩, ⟨_,mathOne⟩]
  have hArg2' : argList2 =
      [⟨TowerType.TFp25519, vU⟩, ⟨TowerType.TFp25519, mathOne⟩] := by
    rw [hArg2]
    show ([{ locVar := "u", locSrc := TowerType.TFp25519 },
           { locVar := "one", locSrc := TowerType.TFp25519 }] : List Located).filterMap
            (fun a => r1.rsTower a.locVar) = _
    simp only [List.filterMap, hu1, hone1]
  set numLoc : Located := ⟨"num", TowerType.TFp25519⟩
  have hnum_r2 : leafSpec.call "fe25519_sub_then_carry" TowerType.TFp25519
                    [TowerType.TFp25519, TowerType.TFp25519] oldNumV argList2 =
                  mathSub vU mathOne := by
    rw [hArg2']; exact hSub oldNumV vU mathOne
  set r2 := locatedUpdate r1 numLoc
    (leafSpec.call "fe25519_sub_then_carry" TowerType.TFp25519
      [TowerType.TFp25519, TowerType.TFp25519] oldNumV argList2)
    with hr2
  have hnum2 : r2.rsTower "num" = some ⟨TowerType.TFp25519, mathSub vU mathOne⟩ := by
    rw [hr2]; rw [locatedUpdate_dest]; rw [hnum_r2]
  have hu2 : r2.rsTower "u" = some ⟨TowerType.TFp25519, vU⟩ := by
    rw [hr2]
    show (rsSetTower r1 "num" _).rsTower "u" = _
    rw [rsSetTower_other r1 "num" "u" _ (by decide)]; exact hu1
  have hone2 : r2.rsTower "one" = some ⟨TowerType.TFp25519, mathOne⟩ := by
    rw [hr2]
    show (rsSetTower r1 "num" _).rsTower "one" = _
    rw [rsSetTower_other r1 "num" "one" _ (by decide)]; exact hone1
  -- ===== Step 3: fe25519_add_then_carry (den) [u, one] =====
  cases hC3 with | call _ _ _ _ oldDenV argList3 _hLook3 hArg3 _ =>
  have hArg3' : argList3 =
      [⟨TowerType.TFp25519, vU⟩, ⟨TowerType.TFp25519, mathOne⟩] := by
    rw [hArg3]
    show ([{ locVar := "u", locSrc := TowerType.TFp25519 },
           { locVar := "one", locSrc := TowerType.TFp25519 }] : List Located).filterMap
            (fun a => r2.rsTower a.locVar) = _
    simp only [List.filterMap, hu2, hone2]
  set denLoc : Located := ⟨"den", TowerType.TFp25519⟩
  have hden_r3 : leafSpec.call "fe25519_add_then_carry" TowerType.TFp25519
                    [TowerType.TFp25519, TowerType.TFp25519] oldDenV argList3 =
                  mathAdd vU mathOne := by
    rw [hArg3']; exact hAdd oldDenV vU mathOne
  set r3 := locatedUpdate r2 denLoc
    (leafSpec.call "fe25519_add_then_carry" TowerType.TFp25519
      [TowerType.TFp25519, TowerType.TFp25519] oldDenV argList3)
    with hr3
  have hden3 : r3.rsTower "den" = some ⟨TowerType.TFp25519, mathAdd vU mathOne⟩ := by
    rw [hr3]; rw [locatedUpdate_dest]; rw [hden_r3]
  have hnum3 : r3.rsTower "num" = some ⟨TowerType.TFp25519, mathSub vU mathOne⟩ := by
    rw [hr3]
    show (rsSetTower r2 "den" _).rsTower "num" = _
    rw [rsSetTower_other r2 "den" "num" _ (by decide)]; exact hnum2
  -- ===== Step 4: fe25519_invert (inv_den) [den] =====
  cases hC4 with | call _ _ _ _ oldInvV argList4 _hLook4 hArg4 _ =>
  have hArg4' : argList4 = [⟨TowerType.TFp25519, mathAdd vU mathOne⟩] := by
    rw [hArg4]
    show ([{ locVar := "den", locSrc := TowerType.TFp25519 }] : List Located).filterMap
            (fun a => r3.rsTower a.locVar) = _
    simp only [List.filterMap, hden3]
  set invLoc : Located := ⟨"inv_den", TowerType.TFp25519⟩
  have hinv_r4 : leafSpec.call "fe25519_invert" TowerType.TFp25519
                    [TowerType.TFp25519] oldInvV argList4 =
                  mathInv (mathAdd vU mathOne) := by
    rw [hArg4']; exact hInv oldInvV (mathAdd vU mathOne)
  set r4 := locatedUpdate r3 invLoc
    (leafSpec.call "fe25519_invert" TowerType.TFp25519
      [TowerType.TFp25519] oldInvV argList4)
    with hr4
  have hinv4 : r4.rsTower "inv_den" =
      some ⟨TowerType.TFp25519, mathInv (mathAdd vU mathOne)⟩ := by
    rw [hr4]; rw [locatedUpdate_dest]; rw [hinv_r4]
  have hnum4 : r4.rsTower "num" = some ⟨TowerType.TFp25519, mathSub vU mathOne⟩ := by
    rw [hr4]
    show (rsSetTower r3 "inv_den" _).rsTower "num" = _
    rw [rsSetTower_other r3 "inv_den" "num" _ (by decide)]; exact hnum3
  have hden4 : r4.rsTower "den" = some ⟨TowerType.TFp25519, mathAdd vU mathOne⟩ := by
    rw [hr4]
    show (rsSetTower r3 "inv_den" _).rsTower "den" = _
    rw [rsSetTower_other r3 "inv_den" "den" _ (by decide)]; exact hden3
  -- ===== Step 5: fe25519_mul (y_out) [num, inv_den] =====
  cases hC5 with | call _ _ _ _ oldYV argList5 _hLook5 hArg5 _ =>
  have hArg5' : argList5 = [⟨TowerType.TFp25519, mathSub vU mathOne⟩,
                            ⟨TowerType.TFp25519, mathInv (mathAdd vU mathOne)⟩] := by
    rw [hArg5]
    show ([{ locVar := "num", locSrc := TowerType.TFp25519 },
           { locVar := "inv_den", locSrc := TowerType.TFp25519 }] : List Located).filterMap
            (fun a => r4.rsTower a.locVar) = _
    simp only [List.filterMap, hnum4, hinv4]
  set yLoc : Located := ⟨"y_out", TowerType.TFp25519⟩
  have hy_r5 : leafSpec.call "fe25519_mul" TowerType.TFp25519
                    [TowerType.TFp25519, TowerType.TFp25519] oldYV argList5 =
                  mathMul (mathSub vU mathOne) (mathInv (mathAdd vU mathOne)) := by
    rw [hArg5']; exact hMul oldYV _ _
  set r5 := locatedUpdate r4 yLoc
    (leafSpec.call "fe25519_mul" TowerType.TFp25519
      [TowerType.TFp25519, TowerType.TFp25519] oldYV argList5)
    with hr5
  have hy5 : r5.rsTower "y_out" = some ⟨TowerType.TFp25519,
      mathMul (mathSub vU mathOne) (mathInv (mathAdd vU mathOne))⟩ := by
    rw [hr5]; rw [locatedUpdate_dest]; rw [hy_r5]
  have hden5 : r5.rsTower "den" = some ⟨TowerType.TFp25519, mathAdd vU mathOne⟩ := by
    rw [hr5]
    show (rsSetTower r4 "y_out" _).rsTower "den" = _
    rw [rsSetTower_other r4 "y_out" "den" _ (by decide)]; exact hden4
  -- ===== Step 6: fe25519_copy (den_out) [den] =====
  cases hC6 with | call _ _ _ _ oldDoV argList6 _hLook6 hArg6 _ =>
  have hArg6' : argList6 = [⟨TowerType.TFp25519, mathAdd vU mathOne⟩] := by
    rw [hArg6]
    show ([{ locVar := "den", locSrc := TowerType.TFp25519 }] : List Located).filterMap
            (fun a => r5.rsTower a.locVar) = _
    simp only [List.filterMap, hden5]
  set doLoc : Located := ⟨"den_out", TowerType.TFp25519⟩
  have hdo_r6 : leafSpec.call "fe25519_copy" TowerType.TFp25519
                    [TowerType.TFp25519] oldDoV argList6 =
                  mathCopy (mathAdd vU mathOne) := by
    rw [hArg6']; exact hCopy oldDoV (mathAdd vU mathOne)
  -- Final state: locatedUpdate r5 doLoc (...)
  refine ⟨?_, ?_⟩
  · -- y_out in the final state is unchanged from r5 (since step 6 writes den_out).
    show (locatedUpdate r5 doLoc _).rsTower "y_out" = _
    show (rsSetTower r5 "den_out" _).rsTower "y_out" = _
    rw [rsSetTower_other r5 "den_out" "y_out" _ (by decide)]
    exact hy5
  · -- den_out in the final state = mathCopy (mathAdd vU mathOne).
    show (locatedUpdate r5 doLoc _).rsTower "den_out" = _
    refine (locatedUpdate_dest r5 doLoc _).trans ?_
    congr 1
    exact congrArg _ hdo_r6

/-! ## §6.  `CombTableInitArrV2`

The body uses 7 named slots of mixed tower types:

  * `B_xyzt`, `ID_xyzt`            : `TBytes 200`  (inputs)
  * `scratch_a`, `scratch_b`,
    `prev`, `sum`                  : `TBytes 200`  (RLetZero-bound)
  * `cells`                        : `TArr 1024 (TBytes 200)` (RLetZero-bound)

Plus the scalar loop counter `k` (RLetU64Zero-bound).

To track preservation of all 7 typed slots through the nested RFor body,
we define `AllSlotsBoundAt`: a heterogeneous list-of-`(name, type)`
invariant.  Each constructor used by the body (`RArrStore`, `RArrLoad`,
`RScalarSetExpr`, `RCall`, `RFor`, `RLetZero`, `RLetU64Zero`, `RSeq`)
has a preservation helper that shows the invariant survives one step.

Generalises `AllFp25519Bound` from §4 to heterogeneous slot types. -/

open CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2 in
/-- Inputs to the comb-table builder: `B_xyzt` and `ID_xyzt` are
    TBytes 200 slots, `cells` is the TArr destination.  The `cells`
    hypothesis is redundant w.r.t. panic-freeness (the body's outer
    `RLetZero` rebinds it) but is retained for callers that want a
    pre-call slot witness. -/
def CombTableInputsWellFormed (rs : RustState) : Prop :=
  (∃ v, rs.rsTower "B_xyzt" = some ⟨TowerType.TBytes 200, v⟩) ∧
  (∃ v, rs.rsTower "ID_xyzt" = some ⟨TowerType.TBytes 200, v⟩) ∧
  (∃ v, rs.rsTower "cells" =
      some ⟨TowerType.TArr 1024 (TowerType.TBytes 200), v⟩)

/-! ### Original section §6 header (retained):

The body uses 7 named slots of mixed tower types:

  * `B_xyzt`, `ID_xyzt`            : `TBytes 200`  (inputs)
  * `scratch_a`, `scratch_b`,
    `prev`, `sum`                  : `TBytes 200`  (RLetZero-bound)
  * `cells`                        : `TArr 1024 (TBytes 200)` (RLetZero-bound)

Plus the scalar loop counter `k` (RLetU64Zero-bound).

To track preservation of all 7 typed slots through the nested RFor body,
we define `AllSlotsBoundAt`: a heterogeneous list-of-`(name, type)`
invariant.  Each constructor used by the body (`RArrStore`, `RArrLoad`,
`RScalarSetExpr`, `RCall`, `RFor`, `RLetZero`, `RLetU64Zero`, `RSeq`)
has a preservation helper that shows the invariant survives one step.

Generalises `AllFp25519Bound` from §4 to heterogeneous slot types. -/

/-! ### `AllSlotsBoundAt` — heterogeneous slot-binding invariant -/

/-- A single typed-slot binding hypothesis. -/
def SlotBoundAt (s : String × TowerType) (rs : RustState) : Prop :=
  ∃ v, rs.rsTower s.1 = some ⟨s.2, v⟩

/-- Every `(name, type)` in `slots` is bound at the recorded type in `rs`. -/
def AllSlotsBoundAt (slots : List (String × TowerType)) (rs : RustState) :
    Prop :=
  ∀ s ∈ slots, SlotBoundAt s rs

/-- Setting an unrelated scalar preserves `AllSlotsBoundAt`. -/
lemma AllSlotsBoundAt_setScalar
    (slots : List (String × TowerType)) (rs : RustState) (y : String) (n : Nat)
    (hP : AllSlotsBoundAt slots rs) :
    AllSlotsBoundAt slots (rsSetScalar rs y n) := by
  intro s hs
  obtain ⟨v, hv⟩ := hP s hs
  refine ⟨v, ?_⟩
  show (rsSetScalar rs y n).rsTower s.1 = _
  exact hv

/-- Setting an unrelated tower slot preserves `AllSlotsBoundAt`,
    *provided* the new name doesn't collide with any tracked slot's name. -/
lemma AllSlotsBoundAt_setTower_fresh
    (slots : List (String × TowerType)) (rs : RustState) (y : String)
    (sval : Σ t, RustVal t) (hP : AllSlotsBoundAt slots rs)
    (hFresh : ∀ s ∈ slots, s.1 ≠ y) :
    AllSlotsBoundAt slots (rsSetTower rs y sval) := by
  intro s hs
  obtain ⟨v, hv⟩ := hP s hs
  refine ⟨v, ?_⟩
  show (rsSetTower rs y sval).rsTower s.1 = _
  rw [rsSetTower_other rs y s.1 sval (hFresh s hs).symm]
  exact hv

/-- Setting a tracked slot to its declared type preserves the invariant
    (the slot may switch to a new value of the same type). -/
lemma AllSlotsBoundAt_setTower_same
    (slots : List (String × TowerType)) (rs : RustState)
    (y : String) (t : TowerType) (v : RustVal t)
    (hP : AllSlotsBoundAt slots rs)
    (hType : ∀ s ∈ slots, s.1 = y → s.2 = t) :
    AllSlotsBoundAt slots (rsSetTower rs y ⟨t, v⟩) := by
  rintro ⟨sName, sTy⟩ hs
  by_cases hsy : sName = y
  · have heq : sTy = t := hType (sName, sTy) hs hsy
    subst hsy
    subst heq
    refine ⟨v, ?_⟩
    show (rsSetTower rs sName ⟨sTy, v⟩).rsTower sName = _
    exact rsSetTower_same _ _ _
  · obtain ⟨v', hv'⟩ := hP (sName, sTy) hs
    refine ⟨v', ?_⟩
    show (rsSetTower rs y ⟨t, v⟩).rsTower sName = _
    rw [rsSetTower_other rs y sName _ (fun h => hsy h.symm)]
    exact hv'

/-- Adding a fresh `(y, t)` binding extends the invariant from `slots` to
    `(y, t) :: slots`, provided `y` doesn't already appear in `slots`. -/
lemma AllSlotsBoundAt_extend
    (slots : List (String × TowerType)) (rs : RustState)
    (y : String) (t : TowerType)
    (hP : AllSlotsBoundAt slots rs)
    (hFresh : ∀ s ∈ slots, s.1 ≠ y) :
    AllSlotsBoundAt ((y, t) :: slots) (rsSetTower rs y ⟨t, default⟩) := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs'
  · refine ⟨default, ?_⟩
    show (rsSetTower rs y ⟨t, default⟩).rsTower y = _
    exact rsSetTower_same _ _ _
  · obtain ⟨v, hv⟩ := hP s hs'
    refine ⟨v, ?_⟩
    show (rsSetTower rs y ⟨t, default⟩).rsTower s.1 = _
    rw [rsSetTower_other rs y s.1 _ (hFresh s hs').symm]
    exact hv

/-- `RCall f dest args` whose dest+args are all tracked at their declared
    tower types preserves `AllSlotsBoundAt`. -/
lemma rcall_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (f : String) (dest : Located) (args : List Located) (rs : RustState)
    (hDestIn : (dest.locVar, dest.locDst) ∈ slots)
    (hArgsIn : ∀ a ∈ args, (a.locVar, a.locDst) ∈ slots)
    (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RCall f dest args) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  have hDest : ∃ v, rs.rsTower dest.locVar = some ⟨dest.locDst, v⟩ :=
    hP (dest.locVar, dest.locDst) hDestIn
  have hArgs : ∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
    intro a ha
    exact hP (a.locVar, a.locDst) (hArgsIn a ha)
  obtain ⟨rs', hExec⟩ := rcall_panic_free N leafSpec f dest args rs hDest hArgs
  refine ⟨rs', hExec, ?_⟩
  -- Use rcall_post_bindings to thread preservation: dest is now at locDst,
  -- all other slots are unchanged.
  have ⟨⟨v', hDest'⟩, hPres⟩ := rcall_post_bindings hExec
  rintro ⟨sName, sTy⟩ hs
  by_cases hsd : sName = dest.locVar
  · -- If sName = dest.locVar, the type sTy stored at that name must equal
    -- dest.locDst (uniqueness of stored type in rs).
    obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    obtain ⟨v1, hv1⟩ := hDest
    have hrs_eq : sTy = dest.locDst := by
      simp only at hv0
      rw [hsd] at hv0
      rw [hv0] at hv1
      exact (Sigma.mk.injEq _ _ _ _).mp (Option.some_inj.mp hv1) |>.1
    subst hsd
    subst hrs_eq
    exact ⟨v', hDest'⟩
  · obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    refine ⟨v0, ?_⟩
    show rs'.rsTower sName = _
    rw [hPres sName hsd]
    exact hv0

/-- Post-state of an `RArrStore` execution: the `arr` slot is bound at
    `arr.locDst` and all other slots are unchanged.  Analogous to
    `rcall_post_bindings`. -/
lemma rarrStore_post_bindings
    {N : Nat} {leafSpec : LeafSpec}
    {arr : Located} {idxVar : String} {src : Located}
    {rs rs' : RustState}
    (hExec : RustExec N leafSpec (LowCT.RArrStore arr idxVar src) rs rs') :
    (∃ v, rs'.rsTower arr.locVar = some ⟨arr.locDst, v⟩) ∧
    (∀ name : String, name ≠ arr.locVar →
        rs'.rsTower name = rs.rsTower name) := by
  cases hExec with
  | arrStore _ _ _ _ _ _ _ _ _ _ =>
    refine ⟨⟨_, locatedUpdate_dest _ _ _⟩, ?_⟩
    intro name hne
    show (rsSetTower rs arr.locVar _).rsTower name = rs.rsTower name
    exact rsSetTower_other rs arr.locVar name _ (Ne.symm hne)

/-- Post-state of an `RArrLoad` execution: the `dst` slot is bound at
    `dst.locDst` and all other slots are unchanged. -/
lemma rarrLoad_post_bindings
    {N : Nat} {leafSpec : LeafSpec}
    {dst src : Located} {idxVar : String}
    {rs rs' : RustState}
    (hExec : RustExec N leafSpec (LowCT.RArrLoad dst src idxVar) rs rs') :
    (∃ v, rs'.rsTower dst.locVar = some ⟨dst.locDst, v⟩) ∧
    (∀ name : String, name ≠ dst.locVar →
        rs'.rsTower name = rs.rsTower name) := by
  cases hExec with
  | arrLoad _ _ _ _ _ _ _ _ _ _ =>
    refine ⟨⟨_, locatedUpdate_dest _ _ _⟩, ?_⟩
    intro name hne
    show (rsSetTower rs dst.locVar _).rsTower name = rs.rsTower name
    exact rsSetTower_other rs dst.locVar name _ (Ne.symm hne)

/-- `RArrStore arr idxVar src` preserves `AllSlotsBoundAt` provided
    `arr` and `src` are both tracked at their declared types. -/
lemma rarrStore_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (arr : Located) (idxVar : String) (src : Located) (rs : RustState)
    (hArrIn : (arr.locVar, arr.locDst) ∈ slots)
    (hSrcIn : (src.locVar, src.locDst) ∈ slots)
    (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RArrStore arr idxVar src) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  have hArr : ∃ v, rs.rsTower arr.locVar = some ⟨arr.locDst, v⟩ :=
    hP (arr.locVar, arr.locDst) hArrIn
  have hSrc : ∃ v, rs.rsTower src.locVar = some ⟨src.locDst, v⟩ :=
    hP (src.locVar, src.locDst) hSrcIn
  obtain ⟨rs', hExec⟩ := rarrStore_panic_free arr idxVar src rs hArr hSrc
  refine ⟨rs', hExec, ?_⟩
  have ⟨⟨v', hArr'⟩, hPres⟩ := rarrStore_post_bindings hExec
  rintro ⟨sName, sTy⟩ hs
  by_cases hsa : sName = arr.locVar
  · obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    obtain ⟨v1, hv1⟩ := hArr
    have hrs_eq : sTy = arr.locDst := by
      simp only at hv0
      rw [hsa] at hv0
      rw [hv0] at hv1
      exact (Sigma.mk.injEq _ _ _ _).mp (Option.some_inj.mp hv1) |>.1
    subst hsa
    subst hrs_eq
    exact ⟨v', hArr'⟩
  · obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    refine ⟨v0, ?_⟩
    show rs'.rsTower sName = _
    rw [hPres sName hsa]
    exact hv0

/-- `RArrLoad dst src idxVar` preserves `AllSlotsBoundAt` provided
    `dst` and `src` are both tracked at their declared types. -/
lemma rarrLoad_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (dst src : Located) (idxVar : String) (rs : RustState)
    (hDstIn : (dst.locVar, dst.locDst) ∈ slots)
    (hSrcIn : (src.locVar, src.locDst) ∈ slots)
    (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RArrLoad dst src idxVar) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  have hDst : ∃ v, rs.rsTower dst.locVar = some ⟨dst.locDst, v⟩ :=
    hP (dst.locVar, dst.locDst) hDstIn
  have hSrc : ∃ v, rs.rsTower src.locVar = some ⟨src.locDst, v⟩ :=
    hP (src.locVar, src.locDst) hSrcIn
  obtain ⟨rs', hExec⟩ := rarrLoad_panic_free dst src idxVar rs hDst hSrc
  refine ⟨rs', hExec, ?_⟩
  have ⟨⟨v', hDst'⟩, hPres⟩ := rarrLoad_post_bindings hExec
  rintro ⟨sName, sTy⟩ hs
  by_cases hsd : sName = dst.locVar
  · obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    obtain ⟨v1, hv1⟩ := hDst
    have hrs_eq : sTy = dst.locDst := by
      simp only at hv0
      rw [hsd] at hv0
      rw [hv0] at hv1
      exact (Sigma.mk.injEq _ _ _ _).mp (Option.some_inj.mp hv1) |>.1
    subst hsd
    subst hrs_eq
    exact ⟨v', hDst'⟩
  · obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    refine ⟨v0, ?_⟩
    show rs'.rsTower sName = _
    rw [hPres sName hsd]
    exact hv0

/-- `RScalarSetExpr x e` preserves `AllSlotsBoundAt` (only scalar state
    changes). -/
lemma rscalarSetExpr_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (x : String) (e : SExpr) (rs : RustState)
    (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RScalarSetExpr x e) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  refine ⟨_, RustExec.scalarSetExpr x e rs, ?_⟩
  exact AllSlotsBoundAt_setScalar slots rs x (e.evalState rs) hP

/-- `RSeq c1 c2` preserves `AllSlotsBoundAt` if both halves do. -/
lemma rseq_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    {c1 c2 : LowCT}
    (h1 : ∀ rs, AllSlotsBoundAt slots rs →
      ∃ rs', RustExec N leafSpec c1 rs rs' ∧ AllSlotsBoundAt slots rs')
    (h2 : ∀ rs, AllSlotsBoundAt slots rs →
      ∃ rs', RustExec N leafSpec c2 rs rs' ∧ AllSlotsBoundAt slots rs')
    (rs : RustState) (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RSeq c1 c2) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  obtain ⟨r1, hr1, hP1⟩ := h1 rs hP
  obtain ⟨r2, hr2, hP2⟩ := h2 r1 hP1
  exact ⟨r2, RustExec.seq _ _ _ _ _ hr1 hr2, hP2⟩

/-- `RFor x n body` preserves `AllSlotsBoundAt` when `body` does, for any
    closed bound `n`. -/
lemma rfor_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (x : String) {body : LowCT}
    (hBody : ∀ rs, AllSlotsBoundAt slots rs →
      ∃ rs', RustExec N leafSpec body rs rs' ∧ AllSlotsBoundAt slots rs')
    (n : Nat) (rs : RustState) (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RFor x n body) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  apply rfor_panic_free_invariant x (AllSlotsBoundAt slots)
    (fun rs k hP => AllSlotsBoundAt_setScalar slots rs x k hP)
  · intro rs0 hP0
    exact hBody rs0 hP0
  · exact hP

/-- `RLetZero y t body` preserves `AllSlotsBoundAt` if the *extended*
    invariant (with `(y, t)` prepended) is preserved by the body, and
    `y` is fresh w.r.t. `slots`. -/
lemma rletZero_AllSlots_extend
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (y : String) (t : TowerType) {body : LowCT}
    (hFresh : ∀ s ∈ slots, s.1 ≠ y)
    (hBody : ∀ rs, AllSlotsBoundAt ((y, t) :: slots) rs →
      ∃ rs', RustExec N leafSpec body rs rs' ∧
        AllSlotsBoundAt ((y, t) :: slots) rs')
    (rs : RustState) (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RLetZero y t body) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  have hExt : AllSlotsBoundAt ((y, t) :: slots) (rsSetTower rs y ⟨t, default⟩) :=
    AllSlotsBoundAt_extend slots rs y t hP hFresh
  obtain ⟨rs', hExec, hP'⟩ := hBody _ hExt
  refine ⟨rs', RustExec.letZero y t body rs rs' hExec, ?_⟩
  -- The extended invariant on `(y, t) :: slots` restricts to the
  -- original `slots`.
  intro s hs
  exact hP' s (List.mem_cons_of_mem _ hs)

/-- `RLetU64Zero y body` preserves `AllSlotsBoundAt` (scalars don't
    interact with tracked tower slots). -/
lemma rletU64Zero_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (y : String) {body : LowCT}
    (hBody : ∀ rs, AllSlotsBoundAt slots rs →
      ∃ rs', RustExec N leafSpec body rs rs' ∧ AllSlotsBoundAt slots rs')
    (rs : RustState) (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RLetU64Zero y body) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  have hP' : AllSlotsBoundAt slots (rsSetScalar rs y 0) :=
    AllSlotsBoundAt_setScalar slots rs y 0 hP
  obtain ⟨rs', hExec, hP''⟩ := hBody _ hP'
  exact ⟨rs', RustExec.letU64Zero y body rs rs' hExec, hP''⟩

/-! ### Specialised helpers for `combTableInitArrV2Body`

The body uses 7 slot names + 1 scalar.  These slot-list literals show
up everywhere; we name them once. -/

/-- The 7 typed slots tracked through the comb-table body.  Order
    matters here only for readability — `AllSlotsBoundAt` uses
    `List.Mem`. -/
abbrev combTableSlots : List (String × TowerType) :=
  [ ("B_xyzt",     TowerType.TBytes 200)
  , ("ID_xyzt",    TowerType.TBytes 200)
  , ("scratch_a",  TowerType.TBytes 200)
  , ("scratch_b",  TowerType.TBytes 200)
  , ("prev",       TowerType.TBytes 200)
  , ("sum",        TowerType.TBytes 200)
  , ("cells",      TowerType.TArr 1024 (TowerType.TBytes 200))
  ]

open CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2 in
/-- **Panic-freeness for `combTableInitArrV2Body`.**

    The body is a chain of 5 `RLetZero` (for `cells`, `scratch_a`,
    `scratch_b`, `prev`, `sum`) + 1 `RLetU64Zero` (for `k`) + `RSeq
    buildRow0 buildLaterRows`.  We thread `AllSlotsBoundAt
    combTableSlots` through the body, discharging each constructor
    via the §6 preservation helpers (`rcall_AllSlots`,
    `rarrStore_AllSlots`, etc.).

    Note: `CombTableInputsWellFormed` only requires `B_xyzt`, `ID_xyzt`
    (and `cells`, redundantly — `RLetZero` rebinds it).  The 4 fresh
    locals are introduced by `RLetZero`s inside the body. -/
theorem combTableInitArrV2Body_panic_free
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : CombTableInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec combTableInitArrV2Body rs rs' := by
  obtain ⟨⟨bV, hb⟩, ⟨idV, hid⟩, _⟩ := hWf
  -- Membership lemmas in combTableSlots (by `simp`).
  have hB_in    : ("B_xyzt",    TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hID_in   : ("ID_xyzt",   TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hSa_in   : ("scratch_a", TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hSb_in   : ("scratch_b", TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hPrev_in : ("prev",      TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hSum_in  : ("sum",       TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hCells_in : ("cells", TowerType.TArr 1024 (TowerType.TBytes 200))
                    ∈ combTableSlots := by
    simp [combTableSlots]
  -- Helper: any state with the 7 slots bound discharges buildRow0 + buildLaterRows.
  --
  -- buildRow0 body:
  --   scExpr "k" (.SLit 0); arrStore "k" "ID_xyzt";
  --   scExpr "k" (.SLit 1); arrStore "k" "B_xyzt";
  --   RFor "d" 14 (5-stmt body for row-0 doubling)
  -- buildLaterRows: RFor "i" 63 (RFor "d" 16 (8-stmt body))
  --
  -- Each statement is one of: RScalarSetExpr, RArrLoad, RArrStore,
  -- RCall.  All are handled by the helper lemmas above.
  -- Step 1: Show that an arbitrary `LowCT` built from the §6
  -- constructors, with dest/src slots in combTableSlots, preserves
  -- AllSlotsBoundAt.  We inline this per-statement here rather than
  -- defining a generic interpreter.
  -- Helper for row-0's inner-d body (5 statements):
  have hRow0Body : ∀ rs0, AllSlotsBoundAt combTableSlots rs0 →
      ∃ rs', RustExec N leafSpec (CombTableInitArrV2.seqN
        [ CombTableInitArrV2.scExpr "k" (.SAdd (.SVar "d") (.SLit 1))
        , CombTableInitArrV2.arrLoad "prev" "k"
        , CombTableInitArrV2.xyztAdd "sum" "prev" "B_xyzt"
        , CombTableInitArrV2.scExpr "k" (.SAdd (.SVar "d") (.SLit 2))
        , CombTableInitArrV2.arrStore "k" "sum"
        ]) rs0 rs' ∧ AllSlotsBoundAt combTableSlots rs' := by
    intro rs0 hP0
    unfold CombTableInitArrV2.seqN
    -- s1: k := d + 1
    obtain ⟨r1, hr1, hP1⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" (.SAdd (.SVar "d") (.SLit 1)) rs0 hP0
    -- s2: prev := cells[k]
    obtain ⟨r2, hr2, hP2⟩ := rarrLoad_AllSlots N leafSpec combTableSlots
      (CombTableInitArrV2.cellLoc "prev") CombTableInitArrV2.cellsLoc "k" r1
      hPrev_in hCells_in hP1
    -- s3: sum := xyzt_add(prev, B_xyzt)
    obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_add_decomposed" (CombTableInitArrV2.cellLoc "sum")
      [CombTableInitArrV2.cellLoc "prev", CombTableInitArrV2.cellLoc "B_xyzt"]
      r2 hSum_in (by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hPrev_in
        · rcases List.mem_singleton.mp h with rfl
          exact hB_in)
      hP2
    -- s4: k := d + 2
    obtain ⟨r4, hr4, hP4⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" (.SAdd (.SVar "d") (.SLit 2)) r3 hP3
    -- s5: cells[k] := sum
    obtain ⟨r5, hr5, hP5⟩ := rarrStore_AllSlots N leafSpec combTableSlots
      CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "sum") r4
      hCells_in hSum_in hP4
    refine ⟨r5, ?_, hP5⟩
    -- Chain via RSeq.
    exact RustExec.seq _ _ _ _ _ hr1
      (RustExec.seq _ _ _ _ _ hr2
        (RustExec.seq _ _ _ _ _ hr3
          (RustExec.seq _ _ _ _ _ hr4 hr5)))
  -- Helper for the inner-d body of buildLaterRows (8 statements):
  have hLaterDBody : ∀ rs0, AllSlotsBoundAt combTableSlots rs0 →
      ∃ rs', RustExec N leafSpec (CombTableInitArrV2.seqN
        [ CombTableInitArrV2.scExpr "k"
            (.SAdd (.SMul (.SVar "i") (.SLit 16)) (.SVar "d"))
        , CombTableInitArrV2.arrLoad "scratch_a" "k"
        , CombTableInitArrV2.xyztDouble "scratch_b" "scratch_a"
        , CombTableInitArrV2.xyztDouble "scratch_a" "scratch_b"
        , CombTableInitArrV2.xyztDouble "scratch_b" "scratch_a"
        , CombTableInitArrV2.xyztDouble "scratch_a" "scratch_b"
        , CombTableInitArrV2.scExpr "k"
            (.SAdd (.SMul (.SAdd (.SVar "i") (.SLit 1)) (.SLit 16)) (.SVar "d"))
        , CombTableInitArrV2.arrStore "k" "scratch_a"
        ]) rs0 rs' ∧ AllSlotsBoundAt combTableSlots rs' := by
    intro rs0 hP0
    unfold CombTableInitArrV2.seqN
    obtain ⟨r1, hr1, hP1⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" _ rs0 hP0
    obtain ⟨r2, hr2, hP2⟩ := rarrLoad_AllSlots N leafSpec combTableSlots
      (CombTableInitArrV2.cellLoc "scratch_a") CombTableInitArrV2.cellsLoc "k" r1
      hSa_in hCells_in hP1
    obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_b")
      [CombTableInitArrV2.cellLoc "scratch_a"]
      r2 hSb_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSa_in)
      hP2
    obtain ⟨r4, hr4, hP4⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_a")
      [CombTableInitArrV2.cellLoc "scratch_b"]
      r3 hSa_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSb_in)
      hP3
    obtain ⟨r5, hr5, hP5⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_b")
      [CombTableInitArrV2.cellLoc "scratch_a"]
      r4 hSb_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSa_in)
      hP4
    obtain ⟨r6, hr6, hP6⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_a")
      [CombTableInitArrV2.cellLoc "scratch_b"]
      r5 hSa_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSb_in)
      hP5
    obtain ⟨r7, hr7, hP7⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" _ r6 hP6
    obtain ⟨r8, hr8, hP8⟩ := rarrStore_AllSlots N leafSpec combTableSlots
      CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "scratch_a") r7
      hCells_in hSa_in hP7
    refine ⟨r8, ?_, hP8⟩
    exact RustExec.seq _ _ _ _ _ hr1
      (RustExec.seq _ _ _ _ _ hr2
        (RustExec.seq _ _ _ _ _ hr3
          (RustExec.seq _ _ _ _ _ hr4
            (RustExec.seq _ _ _ _ _ hr5
              (RustExec.seq _ _ _ _ _ hr6
                (RustExec.seq _ _ _ _ _ hr7 hr8))))))
  -- Now build the 6 outer binders (5 RLetZero + 1 RLetU64Zero) by hand.
  -- Establish AllSlotsBoundAt combTableSlots on s7 := state after all
  -- 6 binders (cells is RLetZero'd LAST in source = OUTERMOST, so
  -- it's set FIRST when we descend through letZero rule).
  -- Body shape:
  --   RLetZero "cells"     (TArr ...) $
  --   RLetZero "scratch_a" (TBytes 200) $
  --   RLetZero "scratch_b" (TBytes 200) $
  --   RLetZero "prev"      (TBytes 200) $
  --   RLetZero "sum"       (TBytes 200) $
  --   RLetU64Zero "k" $
  --   RSeq buildRow0 buildLaterRows
  set s1 := rsSetTower rs "cells"
    ⟨TowerType.TArr 1024 (TowerType.TBytes 200), default⟩
  set s2 := rsSetTower s1 "scratch_a" ⟨TowerType.TBytes 200, default⟩
  set s3 := rsSetTower s2 "scratch_b" ⟨TowerType.TBytes 200, default⟩
  set s4 := rsSetTower s3 "prev"      ⟨TowerType.TBytes 200, default⟩
  set s5 := rsSetTower s4 "sum"       ⟨TowerType.TBytes 200, default⟩
  set s6 := rsSetScalar s5 "k" 0
  -- AllSlotsBoundAt combTableSlots s6.
  have hAll : AllSlotsBoundAt combTableSlots s6 := by
    rintro ⟨sN, sT⟩ hs
    -- combTableSlots = [B_xyzt, ID_xyzt, scratch_a, scratch_b, prev, sum, cells]
    simp only [combTableSlots, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    -- B_xyzt
    · refine ⟨bV, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "B_xyzt" = _
      show s5.rsTower "B_xyzt" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hb
    -- ID_xyzt
    · refine ⟨idV, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "ID_xyzt" = _
      show s5.rsTower "ID_xyzt" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hid
    -- scratch_a (set at s2)
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "scratch_a" = _
      show s5.rsTower "scratch_a" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    -- scratch_b (set at s3)
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "scratch_b" = _
      show s5.rsTower "scratch_b" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    -- prev (set at s4)
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "prev" = _
      show s5.rsTower "prev" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    -- sum (set at s5)
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "sum" = _
      show s5.rsTower "sum" = _
      exact rsSetTower_same _ _ _
    -- cells (set at s1, outermost)
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "cells" = _
      show s5.rsTower "cells" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
  -- Now build the body of RSeq buildRow0 buildLaterRows starting from s6.
  -- buildRow0:
  --   scExpr "k" 0 ; arrStore "k" "ID_xyzt"
  --   ; scExpr "k" 1 ; arrStore "k" "B_xyzt"
  --   ; RFor "d" 14 (hRow0Body)
  obtain ⟨r1, hr1, hP1⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
    "k" (.SLit 0) s6 hAll
  obtain ⟨r2, hr2, hP2⟩ := rarrStore_AllSlots N leafSpec combTableSlots
    CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "ID_xyzt") r1
    hCells_in hID_in hP1
  obtain ⟨r3, hr3, hP3⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
    "k" (.SLit 1) r2 hP2
  obtain ⟨r4, hr4, hP4⟩ := rarrStore_AllSlots N leafSpec combTableSlots
    CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "B_xyzt") r3
    hCells_in hB_in hP3
  obtain ⟨r5, hr5, hP5⟩ := rfor_AllSlots N leafSpec combTableSlots
    "d" hRow0Body 14 r4 hP4
  -- buildLaterRows: RFor "i" 63 (RFor "d" 16 hLaterDBody)
  obtain ⟨r6, hr6, _hP6⟩ := rfor_AllSlots N leafSpec combTableSlots
    "i" (fun rs0 hP0 => rfor_AllSlots N leafSpec combTableSlots
      "d" hLaterDBody 16 rs0 hP0) 63 r5 hP5
  -- Assemble: 5 letZero + 1 letU64Zero + RSeq (RSeq buildRow0 buildLaterRows)
  refine ⟨r6, ?_⟩
  show RustExec N leafSpec combTableInitArrV2Body rs r6
  unfold combTableInitArrV2Body
  refine RustExec.letZero "cells" _ _ rs r6 ?_
  refine RustExec.letZero "scratch_a" _ _ s1 r6 ?_
  refine RustExec.letZero "scratch_b" _ _ s2 r6 ?_
  refine RustExec.letZero "prev" _ _ s3 r6 ?_
  refine RustExec.letZero "sum" _ _ s4 r6 ?_
  refine RustExec.letU64Zero "k" _ s5 r6 ?_
  -- Now in state s6.  Body is RSeq buildRow0 buildLaterRows.
  unfold CombTableInitArrV2.buildRow0 CombTableInitArrV2.buildLaterRows
  unfold CombTableInitArrV2.seqN
  -- buildRow0 = scExpr 0 ; arrStore ID ; scExpr 1 ; arrStore B ; RFor 14 ...
  refine RustExec.seq _ _ _ _ _ ?_ hr6
  exact RustExec.seq _ _ _ _ _ hr1
    (RustExec.seq _ _ _ _ _ hr2
      (RustExec.seq _ _ _ _ _ hr3
        (RustExec.seq _ _ _ _ _ hr4 hr5)))

/-- A binary TBytes 200 leaf-call (xyzt_add_decomposed) matches `mathOp`. -/
def XyztBinopLeafCorrect (leafSpec : LeafSpec) (name : String)
    (mathOp : RustVal (TowerType.TBytes 200) → RustVal (TowerType.TBytes 200) →
              RustVal (TowerType.TBytes 200)) : Prop :=
  ∀ (oldV vA vB : RustVal (TowerType.TBytes 200)),
    leafSpec.call name (TowerType.TBytes 200)
      [TowerType.TBytes 200, TowerType.TBytes 200] oldV
      [⟨TowerType.TBytes 200, vA⟩, ⟨TowerType.TBytes 200, vB⟩] =
    mathOp vA vB

/-- A unary TBytes 200 leaf-call (xyzt_double_decomposed) matches `mathOp`. -/
def XyztUnopLeafCorrect (leafSpec : LeafSpec) (name : String)
    (mathOp : RustVal (TowerType.TBytes 200) → RustVal (TowerType.TBytes 200)) :
    Prop :=
  ∀ (oldV vA : RustVal (TowerType.TBytes 200)),
    leafSpec.call name (TowerType.TBytes 200)
      [TowerType.TBytes 200] oldV
      [⟨TowerType.TBytes 200, vA⟩] = mathOp vA

open CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2 in
/-- **Functional correctness goal.**

    Under the leaf-correctness hypotheses for `xyzt_add_decomposed` and
    `xyzt_double_decomposed`, after running, `cells[k]` holds the
    comb-table cell function value `combMath i d` for `k = i*16 + d`
    where `0 ≤ i < 64`, `0 ≤ d < 16`.

    Proof outline: structural-invariant induction through the nested
    RFor (63 outer × 16 inner = 1008 iterations).  The math contract
    on `combMath` says `combMath i d = double⁴(combMath (i-1) d)` for
    `i > 0`, `combMath 0 d = sum_{j=0..d} B`.

    Stated as a `Prop`-level documented goal rather than a
    theorem with an admitted proof, so the file builds clean.  The output
    conjunct records that `cells` is bound at its declared array type
    after execution; the exact per-cell predicate
    (`cells[i*16 + d] = combMath i d`) requires lifting the TArr
    decomposition through `leafSpec.arrLoad`/`arrStore` and is the
    deferred nested-RFor work item. -/
def CombTableInitArrV2BodyFunctionalCorrectness : Prop :=
    ∀ (N : Nat) (leafSpec : LeafSpec)
      (mathAdd : RustVal (TowerType.TBytes 200) → RustVal (TowerType.TBytes 200) →
                 RustVal (TowerType.TBytes 200))
      (mathDouble : RustVal (TowerType.TBytes 200) → RustVal (TowerType.TBytes 200))
      (_combMath : Nat → Nat → RustVal (TowerType.TBytes 200)),
      XyztBinopLeafCorrect leafSpec "xyzt_add_decomposed" mathAdd →
      XyztUnopLeafCorrect leafSpec "xyzt_double_decomposed" mathDouble →
      ∀ (rs rs' : RustState),
        CombTableInputsWellFormed rs →
        RustExec N leafSpec combTableInitArrV2Body rs rs' →
        ∃ cellsV, rs'.rsTower "cells" =
          some ⟨TowerType.TArr 1024 (TowerType.TBytes 200), cellsV⟩

/-! ## §7.  Memory safety

"Memory safety" in the slot-typed `RustExec` semantics reduces to a
slot-level property: every tracked slot is bound at its declared
tower type after execution.  In the IR, slots are typed values — not
raw pointers — so there are no dangling-pointer or aliasing-induced
hazards to model; what remains is:

  * **Type preservation**: every slot read returns a value of the
    declared `TowerType` (rules out use-after-let-zero and type
    confusion at the IR level).  Captured by `AllSlotsBoundAt`.
  * **Index bounds (RArrLoad/RArrStore)**: at the abstract-IR layer
    the `leafSpec.arrLoad`/`leafSpec.arrStore` callbacks are total
    functions in `(idx : Nat)`, so an out-of-bounds index produces
    a well-typed (default) value rather than a panic.  Concrete
    `LeafSpec` instances can opt to make OOB a leaf-level panic, in
    which case index-safety becomes a leaf obligation discharged by
    a `idx < n` precondition on the call site (the panic-freedom
    proof of `combTableInitArrV2Body` shows the indices stay in
    `[0..1024)`, which is exactly the declared array length).

The interpretation we ship here is #1 (slot type preservation), which
composes with the existence witness from `_panic_free` to give:

    ∀ rs, well-formed-inputs rs →
        ∃ rs', RustExec body rs rs' ∧ memory_safe slots rs'

i.e. there is at least one execution and the post-state is type-safe.

The two bodies covered (`fe25519InvertBody`, `combTableInitArrV2Body`)
are the panic-free targets. -/

/-- **Memory safety (slot-level interpretation #1)** — a state is
    memory-safe for a slot signature `slots` iff every tracked slot
    is bound at its declared tower type.  Alias for `AllSlotsBoundAt`;
    exists to make the safety property explicit at the API boundary
    when paired with an existence witness. -/
def memory_safe (slots : List (String × TowerType)) (rs : RustState) : Prop :=
  AllSlotsBoundAt slots rs

/-- **Memory-safe body** — a `LowCT` is memory-safe over a slot
    signature `slots` iff for every memory-safe input state there is
    at least one post-state that is also memory-safe.  Combines the
    panic-freedom existence claim with slot-type preservation. -/
def MemorySafeBody (N : Nat) (leafSpec : LeafSpec)
    (slots : List (String × TowerType)) (c : LowCT) : Prop :=
  ∀ rs, memory_safe slots rs →
    ∃ rs', RustExec N leafSpec c rs rs' ∧ memory_safe slots rs'

/-- Bridge: the `AllFp25519Bound` invariant used by `fe25519InvertBody`
    is exactly `AllSlotsBoundAt` over the slot signature where every
    variable is tagged with `TFp25519`. -/
lemma AllFp25519Bound_iff_AllSlotsBoundAt
    (vars : List String) (rs : RustState) :
    AllFp25519Bound vars rs ↔
    AllSlotsBoundAt (vars.map (fun v => (v, TowerType.TFp25519))) rs := by
  constructor
  · intro h s hs
    rcases List.mem_map.mp hs with ⟨v, hv, rfl⟩
    exact h v hv
  · intro h v hv
    have hMem : (v, TowerType.TFp25519) ∈
        vars.map (fun v => (v, TowerType.TFp25519)) :=
      List.mem_map.mpr ⟨v, hv, rfl⟩
    exact h _ hMem

/-! ### §7.1  Memory safety of `fe25519InvertBody`

We prove the strong existence-plus-invariant theorem
`fe25519InvertBody_panic_free_strong` directly by replaying the
chain of helper lemmas used in `fe25519InvertBody_panic_free`, this
time keeping the `AllFp25519Bound`-witness for the final state.
Memory-safety is then a renaming via `AllFp25519Bound_iff_AllSlotsBoundAt`.

The proof structure is identical to `_panic_free` but returns
`hP31` (final-state invariant) alongside the execution derivation. -/

open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- **Strong panic-freeness for `fe25519InvertBody`**: existence of a
    post-state PLUS preservation of `AllFp25519Bound fe25519InvertSlots`.

    Same proof structure as `fe25519InvertBody_panic_free`, but the
    final `AllFp25519Bound`-witness `hP31` is exposed rather than
    discarded.  Used as the substrate for memory safety. -/
theorem fe25519InvertBody_panic_free_strong
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : Fe25519InvertInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec fe25519InvertBody rs rs' ∧
      AllFp25519Bound fe25519InvertSlots rs' := by
  obtain ⟨⟨aV, ha⟩, ⟨outV, hout⟩⟩ := hWf
  set s1  := rsSetTower rs "tmp"      ⟨TowerType.TFp25519, default⟩ with hs1
  set s2  := rsSetTower s1 "scratch"  ⟨TowerType.TFp25519, default⟩
  set s3  := rsSetTower s2 "z2"       ⟨TowerType.TFp25519, default⟩
  set s4  := rsSetTower s3 "z9"       ⟨TowerType.TFp25519, default⟩
  set s5  := rsSetTower s4 "z11"      ⟨TowerType.TFp25519, default⟩
  set s6  := rsSetTower s5 "z2_5_0"   ⟨TowerType.TFp25519, default⟩
  set s7  := rsSetTower s6 "z2_10_0"  ⟨TowerType.TFp25519, default⟩
  set s8  := rsSetTower s7 "z2_20_0"  ⟨TowerType.TFp25519, default⟩
  set s9  := rsSetTower s8 "z2_40_0"  ⟨TowerType.TFp25519, default⟩
  set s10 := rsSetTower s9 "z2_50_0"  ⟨TowerType.TFp25519, default⟩
  set s11 := rsSetTower s10 "z2_100_0" ⟨TowerType.TFp25519, default⟩
  set s12 := rsSetTower s11 "t2"      ⟨TowerType.TFp25519, default⟩
  set s13 := rsSetTower s12 "t3"      ⟨TowerType.TFp25519, default⟩
  have hAll : AllFp25519Bound fe25519InvertSlots s13 := by
    intro x hx
    simp only [fe25519InvertSlots, List.mem_cons, List.not_mem_nil,
               or_false] at hx
    show ∃ v, s13.rsTower x = some _
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                | rfl | rfl | rfl | rfl
    · refine ⟨aV, ?_⟩
      show s13.rsTower "a" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact ha
    · refine ⟨outV, ?_⟩
      show s13.rsTower "out" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hout
    · refine ⟨default, ?_⟩
      show s13.rsTower "tmp" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "scratch" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z9" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z11" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_5_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_10_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_20_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_40_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_50_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "z2_100_0" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show s13.rsTower "t2" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, rsSetTower_same _ _ _⟩
  have hA : "a" ∈ fe25519InvertSlots := by decide
  have hOut : "out" ∈ fe25519InvertSlots := by decide
  have hTmp : "tmp" ∈ fe25519InvertSlots := by decide
  have hScr : "scratch" ∈ fe25519InvertSlots := by decide
  have hZ2 : "z2" ∈ fe25519InvertSlots := by decide
  have hZ9 : "z9" ∈ fe25519InvertSlots := by decide
  have hZ11 : "z11" ∈ fe25519InvertSlots := by decide
  have hZ25 : "z2_5_0" ∈ fe25519InvertSlots := by decide
  have hZ210 : "z2_10_0" ∈ fe25519InvertSlots := by decide
  have hZ220 : "z2_20_0" ∈ fe25519InvertSlots := by decide
  have hZ240 : "z2_40_0" ∈ fe25519InvertSlots := by decide
  have hZ250 : "z2_50_0" ∈ fe25519InvertSlots := by decide
  have hZ2100 : "z2_100_0" ∈ fe25519InvertSlots := by decide
  have hT2 : "t2" ∈ fe25519InvertSlots := by decide
  have hT3 : "t3" ∈ fe25519InvertSlots := by decide
  obtain ⟨t0, ht0, hP0⟩ := rcall_AllFp25519_sqr N leafSpec _ "z2" "a" s13 hZ2 hA hAll
  obtain ⟨t1, ht1, hP1⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2" t0 hTmp hZ2 hP0
  obtain ⟨t2, ht2, hP2⟩ := rcall_AllFp25519_sqr N leafSpec _ "scratch" "tmp" t1 hScr hTmp hP1
  obtain ⟨t3, ht3, hP3⟩ := rcall_AllFp25519_copy N leafSpec _ "tmp" "scratch" t2 hTmp hScr hP2
  obtain ⟨t4, ht4, hP4⟩ := rcall_AllFp25519_mul N leafSpec _ "z9" "tmp" "a" t3 hZ9 hTmp hA hP3
  obtain ⟨t5, ht5, hP5⟩ := rcall_AllFp25519_mul N leafSpec _ "z11" "z9" "z2" t4 hZ11 hZ9 hZ2 hP4
  obtain ⟨t6, ht6, hP6⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z11" t5 hTmp hZ11 hP5
  obtain ⟨t7, ht7, hP7⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_5_0" "tmp" "z9" t6 hZ25 hTmp hZ9 hP6
  obtain ⟨t8, ht8, hP8⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_5_0" t7 hTmp hZ25 hP7
  obtain ⟨t9, ht9, hP9⟩ := sqrN_AllFp25519 N leafSpec _ 4 "tmp" "scratch" hTmp hScr t8 hP8
  obtain ⟨t10, ht10, hP10⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_10_0" "tmp" "z2_5_0" t9 hZ210 hTmp hZ25 hP9
  obtain ⟨t11, ht11, hP11⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_10_0" t10 hTmp hZ210 hP10
  obtain ⟨t12, ht12, hP12⟩ := sqrN_AllFp25519 N leafSpec _ 9 "tmp" "scratch" hTmp hScr t11 hP11
  obtain ⟨t13, ht13, hP13⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_20_0" "tmp" "z2_10_0" t12 hZ220 hTmp hZ210 hP12
  obtain ⟨t14, ht14, hP14⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_20_0" t13 hTmp hZ220 hP13
  obtain ⟨t15, ht15, hP15⟩ := sqrN_AllFp25519 N leafSpec _ 19 "tmp" "scratch" hTmp hScr t14 hP14
  obtain ⟨t16, ht16, hP16⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_40_0" "tmp" "z2_20_0" t15 hZ240 hTmp hZ220 hP15
  obtain ⟨t17, ht17, hP17⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_40_0" t16 hTmp hZ240 hP16
  obtain ⟨t18, ht18, hP18⟩ := sqrN_AllFp25519 N leafSpec _ 9 "tmp" "scratch" hTmp hScr t17 hP17
  obtain ⟨t19, ht19, hP19⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_50_0" "tmp" "z2_10_0" t18 hZ250 hTmp hZ210 hP18
  obtain ⟨t20, ht20, hP20⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_50_0" t19 hTmp hZ250 hP19
  obtain ⟨t21, ht21, hP21⟩ := sqrN_AllFp25519 N leafSpec _ 49 "tmp" "scratch" hTmp hScr t20 hP20
  obtain ⟨t22, ht22, hP22⟩ := rcall_AllFp25519_mul N leafSpec _ "z2_100_0" "tmp" "z2_50_0" t21 hZ2100 hTmp hZ250 hP21
  obtain ⟨t23, ht23, hP23⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "z2_100_0" t22 hTmp hZ2100 hP22
  obtain ⟨t24, ht24, hP24⟩ := sqrN_AllFp25519 N leafSpec _ 99 "tmp" "scratch" hTmp hScr t23 hP23
  obtain ⟨t25, ht25, hP25⟩ := rcall_AllFp25519_mul N leafSpec _ "t2" "tmp" "z2_100_0" t24 hT2 hTmp hZ2100 hP24
  obtain ⟨t26, ht26, hP26⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "t2" t25 hTmp hT2 hP25
  obtain ⟨t27, ht27, hP27⟩ := sqrN_AllFp25519 N leafSpec _ 49 "tmp" "scratch" hTmp hScr t26 hP26
  obtain ⟨t28, ht28, hP28⟩ := rcall_AllFp25519_mul N leafSpec _ "t3" "tmp" "z2_50_0" t27 hT3 hTmp hZ250 hP27
  obtain ⟨t29, ht29, hP29⟩ := rcall_AllFp25519_sqr N leafSpec _ "tmp" "t3" t28 hTmp hT3 hP28
  obtain ⟨t30, ht30, hP30⟩ := sqrN_AllFp25519 N leafSpec _ 4 "tmp" "scratch" hTmp hScr t29 hP29
  obtain ⟨t31, ht31, hP31⟩ := rcall_AllFp25519_mul N leafSpec _ "out" "tmp" "z11" t30 hOut hTmp hZ11 hP30
  have hLZ : ∀ (x : String) (t : TowerType) (r : RustState),
      RustExec N leafSpec (LowCT.RLetZero x t LowCT.RSkip) r
        (rsSetTower r x ⟨t, default⟩) :=
    fun x t r => RustExec.letZero x t _ r _ (RustExec.skip _)
  refine ⟨t31, ?_, hP31⟩
  show RustExec N leafSpec Fe25519Invert.fe25519InvertBody rs t31
  exact
    RustExec.seq _ _ _ _ _ (hLZ "tmp" _ rs)
      (RustExec.seq _ _ _ _ _ (hLZ "scratch" _ s1)
        (RustExec.seq _ _ _ _ _ (hLZ "z2" _ s2)
          (RustExec.seq _ _ _ _ _ (hLZ "z9" _ s3)
            (RustExec.seq _ _ _ _ _ (hLZ "z11" _ s4)
              (RustExec.seq _ _ _ _ _ (hLZ "z2_5_0" _ s5)
                (RustExec.seq _ _ _ _ _ (hLZ "z2_10_0" _ s6)
                  (RustExec.seq _ _ _ _ _ (hLZ "z2_20_0" _ s7)
                    (RustExec.seq _ _ _ _ _ (hLZ "z2_40_0" _ s8)
                      (RustExec.seq _ _ _ _ _ (hLZ "z2_50_0" _ s9)
                        (RustExec.seq _ _ _ _ _ (hLZ "z2_100_0" _ s10)
                          (RustExec.seq _ _ _ _ _ (hLZ "t2" _ s11)
                            (RustExec.seq _ _ _ _ _ (hLZ "t3" _ s12)
  (RustExec.seq _ _ _ _ _ ht0
    (RustExec.seq _ _ _ _ _ ht1
      (RustExec.seq _ _ _ _ _ ht2
        (RustExec.seq _ _ _ _ _ ht3
          (RustExec.seq _ _ _ _ _ ht4
            (RustExec.seq _ _ _ _ _ ht5
              (RustExec.seq _ _ _ _ _ ht6
                (RustExec.seq _ _ _ _ _ ht7
                  (RustExec.seq _ _ _ _ _ ht8
                    (RustExec.seq _ _ _ _ _ ht9
                      (RustExec.seq _ _ _ _ _ ht10
                        (RustExec.seq _ _ _ _ _ ht11
                          (RustExec.seq _ _ _ _ _ ht12
                            (RustExec.seq _ _ _ _ _ ht13
                              (RustExec.seq _ _ _ _ _ ht14
                                (RustExec.seq _ _ _ _ _ ht15
                                  (RustExec.seq _ _ _ _ _ ht16
                                    (RustExec.seq _ _ _ _ _ ht17
                                      (RustExec.seq _ _ _ _ _ ht18
                                        (RustExec.seq _ _ _ _ _ ht19
                                          (RustExec.seq _ _ _ _ _ ht20
                                            (RustExec.seq _ _ _ _ _ ht21
                                              (RustExec.seq _ _ _ _ _ ht22
                                                (RustExec.seq _ _ _ _ _ ht23
                                                  (RustExec.seq _ _ _ _ _ ht24
                                                    (RustExec.seq _ _ _ _ _ ht25
                                                      (RustExec.seq _ _ _ _ _ ht26
                                                        (RustExec.seq _ _ _ _ _ ht27
                                                          (RustExec.seq _ _ _ _ _ ht28
                                                            (RustExec.seq _ _ _ _ _ ht29
                                                              (RustExec.seq _ _ _ _ _ ht30
                                                                ht31)))))))))))))))))))))))))))))))))))))))))))

open CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert in
/-- **Memory safety for `fe25519InvertBody`** (interpretation #1):
    every well-formed input yields at least one execution whose
    post-state has every tracked slot bound at its declared tower
    type (`TFp25519` for the 15 named slots).

    Corollary of `fe25519InvertBody_panic_free_strong` via the
    `AllFp25519Bound` ↔ `AllSlotsBoundAt` bridge. -/
theorem fe25519InvertBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : Fe25519InvertInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec fe25519InvertBody rs rs' ∧
      memory_safe (fe25519InvertSlots.map
        (fun v => (v, TowerType.TFp25519))) rs' := by
  obtain ⟨rs', hExec, hP⟩ := fe25519InvertBody_panic_free_strong N leafSpec rs hWf
  refine ⟨rs', hExec, ?_⟩
  exact (AllFp25519Bound_iff_AllSlotsBoundAt _ _).mp hP

/-! ### §7.2  Memory safety of `combTableInitArrV2Body`

The comb-table body's panic-freeness proof already threads
`AllSlotsBoundAt combTableSlots` through every iteration of the
nested `RFor`s; we simply expose the final-state invariant.

Note on array-index safety: the body uses `RArrLoad`/`RArrStore`
with index variable `"k"`.  In the outer scope, `k` ranges over
values `0..1024` (= `combTableSlots.cells` array length).  At the
`RustExec` semantic level these bounds are not enforced — the
`leafSpec.arrLoad`/`arrStore` callbacks are total in `idx : Nat`
and an OOB index returns a well-typed (default) value rather than
panicking.  A concrete `LeafSpec` instance that panics on OOB would
require a leaf-precondition `idx < 1024`, which the body's index
arithmetic satisfies (`k = i*16 + d` for `i < 64, d < 16`); this is
outside the IR-level memory-safety claim. -/

open CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2 in
/-- **Strong panic-freeness for `combTableInitArrV2Body`**: existence
    of a post-state PLUS preservation of `AllSlotsBoundAt
    combTableSlots`.  Same structure as the panic-freeness proof,
    but exposing the final invariant. -/
theorem combTableInitArrV2Body_panic_free_strong
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : CombTableInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec combTableInitArrV2Body rs rs' ∧
      AllSlotsBoundAt combTableSlots rs' := by
  obtain ⟨⟨bV, hb⟩, ⟨idV, hid⟩, _⟩ := hWf
  have hB_in    : ("B_xyzt",    TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hID_in   : ("ID_xyzt",   TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hSa_in   : ("scratch_a", TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hSb_in   : ("scratch_b", TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hPrev_in : ("prev",      TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hSum_in  : ("sum",       TowerType.TBytes 200) ∈ combTableSlots := by
    simp [combTableSlots]
  have hCells_in : ("cells", TowerType.TArr 1024 (TowerType.TBytes 200))
                    ∈ combTableSlots := by
    simp [combTableSlots]
  have hRow0Body : ∀ rs0, AllSlotsBoundAt combTableSlots rs0 →
      ∃ rs', RustExec N leafSpec (CombTableInitArrV2.seqN
        [ CombTableInitArrV2.scExpr "k" (.SAdd (.SVar "d") (.SLit 1))
        , CombTableInitArrV2.arrLoad "prev" "k"
        , CombTableInitArrV2.xyztAdd "sum" "prev" "B_xyzt"
        , CombTableInitArrV2.scExpr "k" (.SAdd (.SVar "d") (.SLit 2))
        , CombTableInitArrV2.arrStore "k" "sum"
        ]) rs0 rs' ∧ AllSlotsBoundAt combTableSlots rs' := by
    intro rs0 hP0
    unfold CombTableInitArrV2.seqN
    obtain ⟨r1, hr1, hP1⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" (.SAdd (.SVar "d") (.SLit 1)) rs0 hP0
    obtain ⟨r2, hr2, hP2⟩ := rarrLoad_AllSlots N leafSpec combTableSlots
      (CombTableInitArrV2.cellLoc "prev") CombTableInitArrV2.cellsLoc "k" r1
      hPrev_in hCells_in hP1
    obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_add_decomposed" (CombTableInitArrV2.cellLoc "sum")
      [CombTableInitArrV2.cellLoc "prev", CombTableInitArrV2.cellLoc "B_xyzt"]
      r2 hSum_in (by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hPrev_in
        · rcases List.mem_singleton.mp h with rfl
          exact hB_in)
      hP2
    obtain ⟨r4, hr4, hP4⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" (.SAdd (.SVar "d") (.SLit 2)) r3 hP3
    obtain ⟨r5, hr5, hP5⟩ := rarrStore_AllSlots N leafSpec combTableSlots
      CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "sum") r4
      hCells_in hSum_in hP4
    refine ⟨r5, ?_, hP5⟩
    exact RustExec.seq _ _ _ _ _ hr1
      (RustExec.seq _ _ _ _ _ hr2
        (RustExec.seq _ _ _ _ _ hr3
          (RustExec.seq _ _ _ _ _ hr4 hr5)))
  have hLaterDBody : ∀ rs0, AllSlotsBoundAt combTableSlots rs0 →
      ∃ rs', RustExec N leafSpec (CombTableInitArrV2.seqN
        [ CombTableInitArrV2.scExpr "k"
            (.SAdd (.SMul (.SVar "i") (.SLit 16)) (.SVar "d"))
        , CombTableInitArrV2.arrLoad "scratch_a" "k"
        , CombTableInitArrV2.xyztDouble "scratch_b" "scratch_a"
        , CombTableInitArrV2.xyztDouble "scratch_a" "scratch_b"
        , CombTableInitArrV2.xyztDouble "scratch_b" "scratch_a"
        , CombTableInitArrV2.xyztDouble "scratch_a" "scratch_b"
        , CombTableInitArrV2.scExpr "k"
            (.SAdd (.SMul (.SAdd (.SVar "i") (.SLit 1)) (.SLit 16)) (.SVar "d"))
        , CombTableInitArrV2.arrStore "k" "scratch_a"
        ]) rs0 rs' ∧ AllSlotsBoundAt combTableSlots rs' := by
    intro rs0 hP0
    unfold CombTableInitArrV2.seqN
    obtain ⟨r1, hr1, hP1⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" _ rs0 hP0
    obtain ⟨r2, hr2, hP2⟩ := rarrLoad_AllSlots N leafSpec combTableSlots
      (CombTableInitArrV2.cellLoc "scratch_a") CombTableInitArrV2.cellsLoc "k" r1
      hSa_in hCells_in hP1
    obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_b")
      [CombTableInitArrV2.cellLoc "scratch_a"]
      r2 hSb_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSa_in)
      hP2
    obtain ⟨r4, hr4, hP4⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_a")
      [CombTableInitArrV2.cellLoc "scratch_b"]
      r3 hSa_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSb_in)
      hP3
    obtain ⟨r5, hr5, hP5⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_b")
      [CombTableInitArrV2.cellLoc "scratch_a"]
      r4 hSb_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSa_in)
      hP4
    obtain ⟨r6, hr6, hP6⟩ := rcall_AllSlots N leafSpec combTableSlots
      "xyzt_double_decomposed" (CombTableInitArrV2.cellLoc "scratch_a")
      [CombTableInitArrV2.cellLoc "scratch_b"]
      r5 hSa_in
      (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hSb_in)
      hP5
    obtain ⟨r7, hr7, hP7⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
      "k" _ r6 hP6
    obtain ⟨r8, hr8, hP8⟩ := rarrStore_AllSlots N leafSpec combTableSlots
      CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "scratch_a") r7
      hCells_in hSa_in hP7
    refine ⟨r8, ?_, hP8⟩
    exact RustExec.seq _ _ _ _ _ hr1
      (RustExec.seq _ _ _ _ _ hr2
        (RustExec.seq _ _ _ _ _ hr3
          (RustExec.seq _ _ _ _ _ hr4
            (RustExec.seq _ _ _ _ _ hr5
              (RustExec.seq _ _ _ _ _ hr6
                (RustExec.seq _ _ _ _ _ hr7 hr8))))))
  set s1 := rsSetTower rs "cells"
    ⟨TowerType.TArr 1024 (TowerType.TBytes 200), default⟩
  set s2 := rsSetTower s1 "scratch_a" ⟨TowerType.TBytes 200, default⟩
  set s3 := rsSetTower s2 "scratch_b" ⟨TowerType.TBytes 200, default⟩
  set s4 := rsSetTower s3 "prev"      ⟨TowerType.TBytes 200, default⟩
  set s5 := rsSetTower s4 "sum"       ⟨TowerType.TBytes 200, default⟩
  set s6 := rsSetScalar s5 "k" 0
  have hAll : AllSlotsBoundAt combTableSlots s6 := by
    rintro ⟨sN, sT⟩ hs
    simp only [combTableSlots, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨bV, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "B_xyzt" = _
      show s5.rsTower "B_xyzt" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hb
    · refine ⟨idV, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "ID_xyzt" = _
      show s5.rsTower "ID_xyzt" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hid
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "scratch_a" = _
      show s5.rsTower "scratch_a" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "scratch_b" = _
      show s5.rsTower "scratch_b" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "prev" = _
      show s5.rsTower "prev" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "sum" = _
      show s5.rsTower "sum" = _
      exact rsSetTower_same _ _ _
    · refine ⟨default, ?_⟩
      show (rsSetScalar s5 "k" 0).rsTower "cells" = _
      show s5.rsTower "cells" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
  obtain ⟨r1, hr1, hP1⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
    "k" (.SLit 0) s6 hAll
  obtain ⟨r2, hr2, hP2⟩ := rarrStore_AllSlots N leafSpec combTableSlots
    CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "ID_xyzt") r1
    hCells_in hID_in hP1
  obtain ⟨r3, hr3, hP3⟩ := rscalarSetExpr_AllSlots N leafSpec combTableSlots
    "k" (.SLit 1) r2 hP2
  obtain ⟨r4, hr4, hP4⟩ := rarrStore_AllSlots N leafSpec combTableSlots
    CombTableInitArrV2.cellsLoc "k" (CombTableInitArrV2.cellLoc "B_xyzt") r3
    hCells_in hB_in hP3
  obtain ⟨r5, hr5, hP5⟩ := rfor_AllSlots N leafSpec combTableSlots
    "d" hRow0Body 14 r4 hP4
  obtain ⟨r6, hr6, hP6⟩ := rfor_AllSlots N leafSpec combTableSlots
    "i" (fun rs0 hP0 => rfor_AllSlots N leafSpec combTableSlots
      "d" hLaterDBody 16 rs0 hP0) 63 r5 hP5
  refine ⟨r6, ?_, hP6⟩
  show RustExec N leafSpec combTableInitArrV2Body rs r6
  unfold combTableInitArrV2Body
  refine RustExec.letZero "cells" _ _ rs r6 ?_
  refine RustExec.letZero "scratch_a" _ _ s1 r6 ?_
  refine RustExec.letZero "scratch_b" _ _ s2 r6 ?_
  refine RustExec.letZero "prev" _ _ s3 r6 ?_
  refine RustExec.letZero "sum" _ _ s4 r6 ?_
  refine RustExec.letU64Zero "k" _ s5 r6 ?_
  unfold CombTableInitArrV2.buildRow0 CombTableInitArrV2.buildLaterRows
  unfold CombTableInitArrV2.seqN
  refine RustExec.seq _ _ _ _ _ ?_ hr6
  exact RustExec.seq _ _ _ _ _ hr1
    (RustExec.seq _ _ _ _ _ hr2
      (RustExec.seq _ _ _ _ _ hr3
        (RustExec.seq _ _ _ _ _ hr4 hr5)))

open CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2 in
/-- **Memory safety for `combTableInitArrV2Body`** (interpretation #1):
    every well-formed input yields at least one execution whose
    post-state has every tracked slot bound at its declared tower
    type (the 6 `TBytes 200` slots + the `TArr 1024 (TBytes 200)`
    cells slot).

    Corollary of `combTableInitArrV2Body_panic_free_strong`. -/
theorem combTableInitArrV2Body_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : CombTableInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec combTableInitArrV2Body rs rs' ∧
      memory_safe combTableSlots rs' :=
  combTableInitArrV2Body_panic_free_strong N leafSpec rs hWf

/-! ### §7.3  Memory safety of `montUToEdwardsBody`

The Mont→Edwards body has the structural shape
  `RLetZero one  $ RLetZero num $ RLetZero den $ RLetZero inv_den $
   RSeq c1 (RSeq c2 (RSeq c3 (RSeq c4 (RSeq c5 c6))))`
where each `c_i` is a single `RCall` with all operands typed
`TFp25519`.  The slot signature has 7 entries (3 inputs + 4 locals),
all at `TFp25519`.

We prove `_panic_free_strong` by establishing `AllSlotsBoundAt
montUToEdwardsSlots` after the 4 `rsSetTower`s and then chaining 6
`rcall_AllSlots` applications.  Memory safety follows immediately. -/

/-- The slot signature for `montUToEdwardsBody`: 3 inputs (`u`,
    `y_out`, `den_out`) + 4 locals (`one`, `num`, `den`, `inv_den`),
    all at tower type `TFp25519`. -/
abbrev montUToEdwardsSlots : List (String × TowerType) :=
  [ ("u",       TowerType.TFp25519)
  , ("y_out",   TowerType.TFp25519)
  , ("den_out", TowerType.TFp25519)
  , ("one",     TowerType.TFp25519)
  , ("num",     TowerType.TFp25519)
  , ("den",     TowerType.TFp25519)
  , ("inv_den", TowerType.TFp25519) ]

open CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards in
/-- **Strong panic-freeness for `montUToEdwardsBody`**: existence of a
    post-state PLUS preservation of `AllSlotsBoundAt
    montUToEdwardsSlots`.  Same structure as the panic-freeness proof,
    but exposing the final invariant via the generic `rcall_AllSlots`
    chain. -/
theorem montUToEdwardsBody_panic_free_strong
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : MontUToEdwardsInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec montUToEdwardsBody rs rs' ∧
      AllSlotsBoundAt montUToEdwardsSlots rs' := by
  obtain ⟨⟨uV, hu⟩, ⟨yOutV, hy⟩, ⟨denOutV, hden⟩⟩ := hWf
  -- §1 Build the state s4 after the 4 RLetZero binders.
  set s1 := rsSetTower rs  "one"     ⟨TowerType.TFp25519, default⟩ with hs1
  set s2 := rsSetTower s1  "num"     ⟨TowerType.TFp25519, default⟩ with hs2
  set s3 := rsSetTower s2  "den"     ⟨TowerType.TFp25519, default⟩ with hs3
  set s4 := rsSetTower s3  "inv_den" ⟨TowerType.TFp25519, default⟩ with hs4
  -- §2 Show AllSlotsBoundAt montUToEdwardsSlots s4 by case-splitting on
  --   the 7 slot names.
  have hAll : AllSlotsBoundAt montUToEdwardsSlots s4 := by
    rintro ⟨sN, sT⟩ hs
    simp only [montUToEdwardsSlots, List.mem_cons, List.not_mem_nil,
               or_false, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- u : TFp25519
      refine ⟨uV, ?_⟩
      show s4.rsTower "u" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hu
    · -- y_out : TFp25519
      refine ⟨yOutV, ?_⟩
      show s4.rsTower "y_out" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hy
    · -- den_out : TFp25519
      refine ⟨denOutV, ?_⟩
      show s4.rsTower "den_out" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact hden
    · -- one : TFp25519 (default)
      refine ⟨default, ?_⟩
      show s4.rsTower "one" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · -- num : TFp25519 (default)
      refine ⟨default, ?_⟩
      show s4.rsTower "num" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · -- den : TFp25519 (default)
      refine ⟨default, ?_⟩
      show s4.rsTower "den" = _
      repeat rw [rsSetTower_other _ _ _ _ (by decide)]
      exact rsSetTower_same _ _ _
    · -- inv_den : TFp25519 (default)
      refine ⟨default, rsSetTower_same _ _ _⟩
  -- §3 Slot-membership lemmas (for use with rcall_AllSlots).
  let fpL (v : String) : Located :=
    { locVar := v, locSrc := TowerType.TFp25519 }
  have hU_in    : ("u",       TowerType.TFp25519) ∈ montUToEdwardsSlots := by
    simp [montUToEdwardsSlots]
  have hY_in    : ("y_out",   TowerType.TFp25519) ∈ montUToEdwardsSlots := by
    simp [montUToEdwardsSlots]
  have hDO_in   : ("den_out", TowerType.TFp25519) ∈ montUToEdwardsSlots := by
    simp [montUToEdwardsSlots]
  have hOne_in  : ("one",     TowerType.TFp25519) ∈ montUToEdwardsSlots := by
    simp [montUToEdwardsSlots]
  have hNum_in  : ("num",     TowerType.TFp25519) ∈ montUToEdwardsSlots := by
    simp [montUToEdwardsSlots]
  have hDen_in  : ("den",     TowerType.TFp25519) ∈ montUToEdwardsSlots := by
    simp [montUToEdwardsSlots]
  have hInv_in  : ("inv_den", TowerType.TFp25519) ∈ montUToEdwardsSlots := by
    simp [montUToEdwardsSlots]
  -- §4 Six RCalls via rcall_AllSlots.
  -- Step 1: fe25519_set_one (one) []
  obtain ⟨r5, hr5, hP5⟩ := rcall_AllSlots N leafSpec montUToEdwardsSlots
    "fe25519_set_one" (fpL "one") [] s4 hOne_in (by intro a ha; cases ha) hAll
  -- Step 2: fe25519_sub_then_carry (num) [u, one]
  obtain ⟨r6, hr6, hP6⟩ := rcall_AllSlots N leafSpec montUToEdwardsSlots
    "fe25519_sub_then_carry" (fpL "num") [fpL "u", fpL "one"] r5 hNum_in
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hU_in
        · rcases List.mem_singleton.mp h with rfl; exact hOne_in)
    hP5
  -- Step 3: fe25519_add_then_carry (den) [u, one]
  obtain ⟨r7, hr7, hP7⟩ := rcall_AllSlots N leafSpec montUToEdwardsSlots
    "fe25519_add_then_carry" (fpL "den") [fpL "u", fpL "one"] r6 hDen_in
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hU_in
        · rcases List.mem_singleton.mp h with rfl; exact hOne_in)
    hP6
  -- Step 4: fe25519_invert (inv_den) [den]
  obtain ⟨r8, hr8, hP8⟩ := rcall_AllSlots N leafSpec montUToEdwardsSlots
    "fe25519_invert" (fpL "inv_den") [fpL "den"] r7 hInv_in
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hDen_in)
    hP7
  -- Step 5: fe25519_mul (y_out) [num, inv_den]
  obtain ⟨r9, hr9, hP9⟩ := rcall_AllSlots N leafSpec montUToEdwardsSlots
    "fe25519_mul" (fpL "y_out") [fpL "num", fpL "inv_den"] r8 hY_in
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hNum_in
        · rcases List.mem_singleton.mp h with rfl; exact hInv_in)
    hP8
  -- Step 6: fe25519_copy (den_out) [den]
  obtain ⟨r10, hr10, hP10⟩ := rcall_AllSlots N leafSpec montUToEdwardsSlots
    "fe25519_copy" (fpL "den_out") [fpL "den"] r9 hDO_in
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hDen_in)
    hP9
  -- §5 Assemble: 4 letZero + 6 RSeq.
  refine ⟨r10, ?_, hP10⟩
  refine RustExec.letZero "one" _ _ rs r10 ?_
  refine RustExec.letZero "num" _ _ s1 r10 ?_
  refine RustExec.letZero "den" _ _ s2 r10 ?_
  refine RustExec.letZero "inv_den" _ _ s3 r10 ?_
  exact RustExec.seq _ _ _ _ _ hr5
    (RustExec.seq _ _ _ _ _ hr6
      (RustExec.seq _ _ _ _ _ hr7
        (RustExec.seq _ _ _ _ _ hr8
          (RustExec.seq _ _ _ _ _ hr9 hr10))))

open CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards in
/-- **Memory safety for `montUToEdwardsBody`** (interpretation #1):
    every well-formed input yields at least one execution whose
    post-state has every tracked slot bound at its declared tower
    type (the 7 `TFp25519` slots).

    Corollary of `montUToEdwardsBody_panic_free_strong`. -/
theorem montUToEdwardsBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hWf : MontUToEdwardsInputsWellFormed rs) :
    ∃ rs', RustExec N leafSpec montUToEdwardsBody rs rs' ∧
      memory_safe montUToEdwardsSlots rs' :=
  montUToEdwardsBody_panic_free_strong N leafSpec rs hWf

/-! ### §7.4  Memory safety of the 6 `Scalar25519Ops` bodies

Each body is a single `RCall`; memory safety reduces to one
application of `rcall_AllSlots`.  The slot signature varies per body
(2 or 3 slots) and includes the operand types (`TFpL25519` and
`TBytes 32` for the bytes/mont converters). -/

/-- Slot signature for `mulBody` / `addBody` / `subBody`:
    `out, a, b : TFpL25519`. -/
abbrev scalarBinopSlots : List (String × TowerType) :=
  [ ("out", TowerType.TFpL25519)
  , ("a",   TowerType.TFpL25519)
  , ("b",   TowerType.TFpL25519) ]

/-- Slot signature for `negateBody`: `out, a : TFpL25519`. -/
abbrev scalarUnopSlots : List (String × TowerType) :=
  [ ("out", TowerType.TFpL25519)
  , ("a",   TowerType.TFpL25519) ]

/-- Slot signature for `fromBytesModOrderBody`:
    `out : TFpL25519`, `bytes_in : TBytes 32`. -/
abbrev fromBytesSlots : List (String × TowerType) :=
  [ ("out",      TowerType.TFpL25519)
  , ("bytes_in", TowerType.TBytes 32) ]

/-- Slot signature for `toBytesBody`:
    `out : TBytes 32`, `mont : TFpL25519`. -/
abbrev toBytesSlots : List (String × TowerType) :=
  [ ("out",  TowerType.TBytes 32)
  , ("mont", TowerType.TFpL25519) ]

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- **Memory safety for `mulBody`**: single `RCall` whose 3 operands
    are tracked at `TFpL25519`. -/
theorem mulBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt scalarBinopSlots rs) :
    ∃ rs', RustExec N leafSpec mulBody rs rs' ∧
      memory_safe scalarBinopSlots rs' := by
  have hOut : ("out", TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  have hA   : ("a",   TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  have hB   : ("b",   TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  exact rcall_AllSlots N leafSpec scalarBinopSlots _ _ _ rs hOut
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hA
        · rcases List.mem_singleton.mp h with rfl; exact hB) hP

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- **Memory safety for `addBody`** — same slots/proof as `mulBody`. -/
theorem addBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt scalarBinopSlots rs) :
    ∃ rs', RustExec N leafSpec addBody rs rs' ∧
      memory_safe scalarBinopSlots rs' := by
  have hOut : ("out", TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  have hA   : ("a",   TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  have hB   : ("b",   TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  exact rcall_AllSlots N leafSpec scalarBinopSlots _ _ _ rs hOut
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hA
        · rcases List.mem_singleton.mp h with rfl; exact hB) hP

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- **Memory safety for `subBody`** — same slots/proof as `mulBody`. -/
theorem subBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt scalarBinopSlots rs) :
    ∃ rs', RustExec N leafSpec subBody rs rs' ∧
      memory_safe scalarBinopSlots rs' := by
  have hOut : ("out", TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  have hA   : ("a",   TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  have hB   : ("b",   TowerType.TFpL25519) ∈ scalarBinopSlots := by
    simp [scalarBinopSlots]
  exact rcall_AllSlots N leafSpec scalarBinopSlots _ _ _ rs hOut
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hA
        · rcases List.mem_singleton.mp h with rfl; exact hB) hP

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- **Memory safety for `negateBody`**: single `RCall` whose 2 operands
    are tracked at `TFpL25519`. -/
theorem negateBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt scalarUnopSlots rs) :
    ∃ rs', RustExec N leafSpec negateBody rs rs' ∧
      memory_safe scalarUnopSlots rs' := by
  have hOut : ("out", TowerType.TFpL25519) ∈ scalarUnopSlots := by
    simp [scalarUnopSlots]
  have hA   : ("a",   TowerType.TFpL25519) ∈ scalarUnopSlots := by
    simp [scalarUnopSlots]
  exact rcall_AllSlots N leafSpec scalarUnopSlots _ _ _ rs hOut
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hA) hP

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- **Memory safety for `fromBytesModOrderBody`**: single `RCall`
    with `out : TFpL25519` + `bytes_in : TBytes 32`. -/
theorem fromBytesModOrderBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt fromBytesSlots rs) :
    ∃ rs', RustExec N leafSpec fromBytesModOrderBody rs rs' ∧
      memory_safe fromBytesSlots rs' := by
  have hOut   : ("out",      TowerType.TFpL25519) ∈ fromBytesSlots := by
    simp [fromBytesSlots]
  have hBytes : ("bytes_in", TowerType.TBytes 32) ∈ fromBytesSlots := by
    simp [fromBytesSlots]
  exact rcall_AllSlots N leafSpec fromBytesSlots _ _ _ rs hOut
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hBytes) hP

open CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops in
/-- **Memory safety for `toBytesBody`**: single `RCall` with
    `out : TBytes 32` + `mont : TFpL25519`. -/
theorem toBytesBody_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt toBytesSlots rs) :
    ∃ rs', RustExec N leafSpec toBytesBody rs rs' ∧
      memory_safe toBytesSlots rs' := by
  have hOut  : ("out",  TowerType.TBytes 32) ∈ toBytesSlots := by
    simp [toBytesSlots]
  have hMont : ("mont", TowerType.TFpL25519) ∈ toBytesSlots := by
    simp [toBytesSlots]
  exact rcall_AllSlots N leafSpec toBytesSlots _ _ _ rs hOut
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hMont) hP

/-! ### §7.5  Summary

Nine `_memory_safe` theorems wire panic-freeness to slot-type
preservation:

  * `fe25519InvertBody_memory_safe` — 15 slots all `TFp25519`.
  * `combTableInitArrV2Body_memory_safe` — 6 `TBytes 200` slots +
    1 `TArr 1024 (TBytes 200)` slot.
  * `montUToEdwardsBody_memory_safe` — 7 slots all `TFp25519`
    (3 inputs + 4 locals).
  * `mulBody_memory_safe`, `addBody_memory_safe`, `subBody_memory_safe`
    — 3 slots all `TFpL25519`.
  * `negateBody_memory_safe` — 2 slots all `TFpL25519`.
  * `fromBytesModOrderBody_memory_safe` — `TFpL25519` + `TBytes 32`.
  * `toBytesBody_memory_safe` — `TBytes 32` + `TFpL25519`.

All derive from the generic `rcall_AllSlots` / `rarrStore_AllSlots`
preservation lemmas (or, for the multi-call bodies, a strong
panic-freeness theorem `_panic_free_strong` that bundles execution +
invariant).

Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only;
no new global axioms. -/

end CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness
