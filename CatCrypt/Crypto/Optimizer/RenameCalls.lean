/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# Renaming leaf calls in `LowCT`

`renameCalls σ` replaces the leaf name `f` of every leaf call (`RCall`,
`RCallSwap`, the inner call of `RCloneCall`, `RCallDstThreaded`) by `σ f` and
traverses every nested command. When the leaf specification gives `σ f` and `f`
the same result on every input (`CallsAgree leafSpec σ`), the renamed command
has the same big-step executions as the original.

The optimizer passes `BarrettReduce.barrettReduce` and
`MontgomeryReduce.montgomeryReduce` are instances of `renameCalls`. The
arithmetic of the leaves they target is proved elsewhere
(`Rewrite/BarrettReduceGeneric`, `Rewrite/MontgomeryRedcGeneric`); this module is
about the renaming only.

## Main results

* `renameCalls σ` — the call-renaming pass.
* `CallsAgree leafSpec σ` — the leaf specification agrees at `σ f` and `f`.
* `rustExec_renameCalls_iff` — under `CallsAgree leafSpec σ`, `RustExec` of
  `renameCalls σ c` holds iff `RustExec` of `c` holds.
* `rfor_spine_reverse` — reversal of an execution along the `RFor` spine.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.RenameCalls

open CatCrypt.Crypto.Jasmin.LowCT

/-- Rename the leaf name `f` of every leaf call to `σ f`. `RCall`, `RCallSwap`,
    the inner call of `RCloneCall` and `RCallDstThreaded` are renamed; every
    constructor with a nested command is traversed; every other constructor,
    including `RCallN` and `RFnCall`, is kept. -/
def renameCalls (σ : String → String) : LowCT → LowCT
  | .RSkip => .RSkip
  | .RSeq c1 c2 => .RSeq (renameCalls σ c1) (renameCalls σ c2)
  | .RLetZero x t body => .RLetZero x t (renameCalls σ body)
  | .RLetU64Zero x body => .RLetU64Zero x (renameCalls σ body)
  | .RScalarSet x v => .RScalarSet x v
  | .RCall f dst args => .RCall (σ f) dst args
  | .RCallSwap f d1 d2 args => .RCallSwap (σ f) d1 d2 args
  | .RCloneCall cv ct od inner dest args => .RCloneCall cv ct od (σ inner) dest args
  | .RIfNz cond ct cf => .RIfNz cond (renameCalls σ ct) (renameCalls σ cf)
  | .RWhileNz cond body => .RWhileNz cond (renameCalls σ body)
  | .RFor x n body => .RFor x n (renameCalls σ body)
  | .RForRuntime x b body => .RForRuntime x b (renameCalls σ body)
  | .RLimbStore loc idx v => .RLimbStore loc idx v
  | .RLimbStoreExpr loc idx e => .RLimbStoreExpr loc idx e
  | .RCallN f dests args => .RCallN f dests args
  | .RSelect dst sel s0 s1 => .RSelect dst sel s0 s1
  | .RAssert label => .RAssert label
  | .RBlock body => .RBlock (renameCalls σ body)
  | .RFnDef name params returns body cont =>
      .RFnDef name params returns (renameCalls σ body) (renameCalls σ cont)
  | .RFnCall f dests args => .RFnCall f dests args
  | .RTupleLoad dst src idx => .RTupleLoad dst src idx
  | .RArrStore arr idxVar src => .RArrStore arr idxVar src
  | .RArrLoad dst src idxVar => .RArrLoad dst src idxVar
  | .RScalarSetExpr x e => .RScalarSetExpr x e
  | .RArrStoreLit arr idx src => .RArrStoreLit arr idx src
  | .RArrLoadLit dst src idx => .RArrLoadLit dst src idx
  | .RCallDstThreaded f dst args => .RCallDstThreaded (σ f) dst args
  | .RCopy dst src => .RCopy dst src

/-- The leaf specification gives the renamed leaf `σ f` and the leaf `f` the
    same result on every input. -/
def CallsAgree (leafSpec : LeafSpec) (σ : String → String) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType)
    (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
    leafSpec.call (σ f) dt argTs oldV args = leafSpec.call f dt argTs oldV args

/-- Under `CallsAgree`, every execution of `c` is an execution of
    `renameCalls σ c`. -/
theorem rustExec_renameCalls_of_rustExec
    {σ : String → String} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : CallsAgree leafSpec σ)
    {c : LowCT} {rs rs' : RustState}
    (h : RustExec N leafSpec c rs rs') :
    RustExec N leafSpec (renameCalls σ c) rs rs' := by
  -- Each rule is re-applied at the renamed command; at a leaf call the
  -- post-state is first rewritten from `f` to `σ f` by `hAgree`. The `ifFalse`
  -- arm is listed because `constructor` commits to `ifTrue` at `RIfNz`.
  induction h <;> simp only [renameCalls] at * <;>
    first
    | (rw [← hAgree]; constructor <;> assumption)
    | (constructor <;> assumption)
    | (apply RustExec.ifFalse <;> assumption)

/-- Reversal along the `RFor` spine: when every `RustExec` of `body'` lifts to
    one of `body`, every `RustExec` of `RFor x n body'` lifts to one of
    `RFor x n body`.

    The command is carried as a variable `c0` with a defining equation so that
    the induction on the derivation has a uniform motive, and the trip count
    `n0` is quantified inside that motive so the `forSucc` step can specialise
    it to the shorter count. Every `RustExec` rule is listed: the rules other
    than `forZero`/`forSucc` are at commands whose head constructor is not
    `RFor`, so the defining equation refutes them, and listing them makes a
    change to the rule set a build error. -/
theorem rfor_spine_reverse {N : Nat} {leafSpec : LeafSpec}
    {x : String} {body body' : LowCT}
    (ih : ∀ (rs rs' : RustState),
      RustExec N leafSpec body' rs rs' → RustExec N leafSpec body rs rs') :
    ∀ (c0 : LowCT) (rs0 rs0' : RustState),
      RustExec N leafSpec c0 rs0 rs0' →
      ∀ (n0 : Nat), c0 = .RFor x n0 body' →
      RustExec N leafSpec (.RFor x n0 body) rs0 rs0' := by
  intro c0 rs0 rs0' h0
  induction h0 with
  | forZero x' b rs =>
      intro n0 hEq; cases hEq; exact RustExec.forZero x body rs
  | forSucc x' k b rs r1 rs' _ hBody ihInner _ =>
      intro n0 hEq
      cases hEq
      exact RustExec.forSucc x k body rs r1 rs' (ihInner k rfl) (ih _ _ hBody)
  | skip | seq | letZero | letU64Zero | scalarSet | ifTrue | ifFalse
  | whileFalse | whileTrue | forRuntime | call | cloneCall | callSwap
  | limbStore | limbStoreExpr | callN | selectFalse | selectTrue
  | assert | block | tupleLoad | arrStore
  | arrLoad | arrStoreLit | arrLoadLit | scalarSetExpr
  | callDstThreaded | copy => intro n0 hEq; cases hEq

/-- Under `CallsAgree`, a leaf-call execution at the renamed name `σ f` is one
    at `f`. -/
theorem rustExec_call_of_renamed
    {σ : String → String} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : CallsAgree leafSpec σ) {f : String} {dst : Located} {args : List Located}
    {rs rs' : RustState}
    (h : RustExec N leafSpec (.RCall (σ f) dst args) rs rs') :
    RustExec N leafSpec (.RCall f dst args) rs rs' := by
  cases h
  rw [hAgree]
  constructor <;> assumption

/-- Under `CallsAgree`, every execution of `renameCalls σ c` is an execution
    of `c`. -/
theorem rustExec_of_rustExec_renameCalls
    {σ : String → String} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : CallsAgree leafSpec σ) :
    ∀ {c : LowCT} {rs rs' : RustState},
      RustExec N leafSpec (renameCalls σ c) rs rs' →
      RustExec N leafSpec c rs rs' := by
  intro c
  induction c with
  | RSeq c1 c2 ih1 ih2 =>
      intro rs rs' h
      cases h with
      | seq _ _ _ r1 _ h1 h2 => exact RustExec.seq c1 c2 rs r1 rs' (ih1 h1) (ih2 h2)
  | RLetZero x t body ih =>
      intro rs rs' h
      cases h with
      | letZero _ _ _ _ _ hBody => exact RustExec.letZero x t body rs rs' (ih hBody)
  | RLetU64Zero x body ih =>
      intro rs rs' h
      cases h with
      | letU64Zero _ _ _ _ hBody => exact RustExec.letU64Zero x body rs rs' (ih hBody)
  | RCall f dst args => intro rs rs' h; exact rustExec_call_of_renamed hAgree h
  | RCallSwap f d1 d2 args =>
      intro rs rs' h
      cases h with
      | callSwap _ _ _ _ _ rs1 _ h1 h2 =>
          exact RustExec.callSwap f d1 d2 args rs rs1 rs'
            (rustExec_call_of_renamed hAgree h1) (rustExec_call_of_renamed hAgree h2)
  | RCloneCall cv ct od inner dest args =>
      intro rs rs' h
      cases h with
      | cloneCall _ _ _ _ _ _ _ rsClone _ hrs hInner =>
          exact RustExec.cloneCall cv ct od inner dest args rs rsClone rs' hrs
            (rustExec_call_of_renamed hAgree hInner)
  | RIfNz cond ct cf ihT ihF =>
      intro rs rs' h
      cases h with
      | ifTrue _ _ _ _ _ v hv hne hBody =>
          exact RustExec.ifTrue cond ct cf rs rs' v hv hne (ihT hBody)
      | ifFalse _ _ _ _ _ hv hBody =>
          exact RustExec.ifFalse cond ct cf rs rs' hv (ihF hBody)
  | RWhileNz cond body ih =>
      intro rs rs' h
      -- Induction on the derivation of the renamed loop, with the loop carried
      -- as a variable `c0` and a defining equation.
      have aux : ∀ c0 rs0 rs0',
          RustExec N leafSpec c0 rs0 rs0' →
          c0 = .RWhileNz cond (renameCalls σ body) →
          RustExec N leafSpec (.RWhileNz cond body) rs0 rs0' := by
        intro c0 rs0 rs0' h0
        induction h0 with
        | whileFalse e b rs hv =>
            intro hEq; cases hEq; exact RustExec.whileFalse cond body rs hv
        | whileTrue e b rs r1 rs' v hv hne hBody hRest ihBody ihRest =>
            intro hEq
            cases hEq
            exact RustExec.whileTrue cond body rs r1 rs' v hv hne (ih hBody) (ihRest rfl)
        -- The remaining rules are at commands whose head constructor is not
        -- `RWhileNz`, so the defining equation refutes them. They are listed
        -- rather than matched by `_` so that a change to the rule set is a
        -- build error.
        | skip | seq | letZero | letU64Zero | scalarSet | ifTrue | ifFalse
        | forZero | forSucc | forRuntime | call | cloneCall | callSwap
        | limbStore | limbStoreExpr | callN | selectFalse | selectTrue
        | assert | block | tupleLoad | arrStore
        | arrLoad | arrStoreLit | arrLoadLit | scalarSetExpr
        | callDstThreaded | copy => intro hEq; cases hEq
      exact aux _ rs rs' h rfl
  | RFor x n body ih =>
      intro rs rs' h
      exact rfor_spine_reverse (fun _ _ hb => ih hb) _ rs rs' h n rfl
  | RForRuntime x bnd body ih =>
      intro rs rs' h
      cases h with
      | forRuntime _ _ _ _ _ hInner =>
          exact RustExec.forRuntime x bnd body rs rs'
            (rfor_spine_reverse (fun _ _ hb => ih hb) _ rs rs' hInner _ rfl)
  | RBlock body ih =>
      intro rs rs' h
      cases h with
      | block _ _ _ hBody => exact RustExec.block body rs rs' (ih hBody)
  | RFnDef => intro _ _ h; cases h
  | RCallDstThreaded f dst args =>
      intro rs rs' h
      cases h
      rw [hAgree]
      constructor <;> assumption
  | RSkip | RScalarSet | RLimbStore | RLimbStoreExpr | RCallN | RSelect | RAssert
  | RFnCall | RTupleLoad | RArrStore | RArrLoad | RScalarSetExpr | RArrStoreLit
  | RArrLoadLit | RCopy => intro rs rs' h; exact h

/-- Under `CallsAgree leafSpec σ`, renaming leaf calls by `σ` preserves the
    big-step semantics: `renameCalls σ c` and `c` have the same executions. -/
theorem rustExec_renameCalls_iff
    {σ : String → String} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : CallsAgree leafSpec σ) (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (renameCalls σ c) rs rs' ↔ RustExec N leafSpec c rs rs' :=
  ⟨rustExec_of_rustExec_renameCalls hAgree, rustExec_renameCalls_of_rustExec hAgree⟩

end CatCrypt.Crypto.Optimizer.RenameCalls
