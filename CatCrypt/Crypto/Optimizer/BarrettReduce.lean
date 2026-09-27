/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# Pass 1.1 — Barrett Reduction

A pass of CatCrypt's verified optimizing compiler.  Rewrites
`RCall "mod_q" [x]` (and ML-KEM's `"reduce"` leaf) to
`RCall s!"barrett_{q}" [x]` when `q` is a statically-known modulus.

## Soundness

The pass's correctness reduces to per-leaf agreement: the `LeafSpec`'s
`s!"barrett_{q}"` and `"mod_q"` (or `"reduce"`) must produce
semantically identical results at every call site.  This is an external
assumption on the `LeafSpec` (`barrettAgreesModQ`); it is provable by
`decide` for concrete `q` once the `LeafSpec` is instantiated against
a Jasmin/libcrux implementation.

## Composition

This pass is one slot in the optimizer pipeline.
The orchestrator composes the per-pass equivalences into the global
`optimize_denote_eq` correctness theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.BarrettReduce

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Pattern recognition

A `LowCT` is a "mod-q reduction site" if it is `RCall "mod_q"` or
ML-KEM's `RCall "reduce"`.  Both have the same semantic intent and
share the same `dst`/`args` shape.  We list both names because
different protocol surfaces use different conventions:

* `"mod_q"` — the conventional name used in the abstract spec.
* `"reduce"` — ML-KEM's hand-written kernel name (see
  `CatCrypt/Crypto/MLKEM/MlkemLowCT.lean` §2.1).
-/

/-- Predicate: the call name `f` is one of the recognised
    mod-q reduction-site names. -/
def isModQName (f : String) : Bool :=
  f == "mod_q" || f == "reduce"

@[simp] theorem isModQName_mod_q : isModQName "mod_q" = true := by
  decide

@[simp] theorem isModQName_reduce : isModQName "reduce" = true := by
  decide

/-! ## §2  Rewrite pass

`barrettReduce q` walks the LowCT AST and replaces every recognised
mod-q reduction call with `s!"barrett_{q}"`.  All other constructors
are traversed compositionally; constructors with no nested `LowCT`
(scalar set, limb store, asm op, …) are identity.
-/

/-- The name of the Barrett-q leaf for a given modulus `q`. -/
@[inline] def barrettName (q : Nat) : String := s!"barrett_{q}"

/-- The Barrett-reduction rewrite pass parameterised by the modulus `q`.
    Replaces `RCall "mod_q"`/`RCall "reduce"` with
    `RCall (barrettName q)`; recurses through every constructor with a
    nested `LowCT` body.  Constructors without nested commands act
    as identity. -/
def barrettReduce (q : Nat) : LowCT → LowCT
  | .RSkip => .RSkip
  | .RSeq c1 c2 => .RSeq (barrettReduce q c1) (barrettReduce q c2)
  | .RLetZero x t body => .RLetZero x t (barrettReduce q body)
  | .RLetU64Zero x body => .RLetU64Zero x (barrettReduce q body)
  | .RScalarSet x v => .RScalarSet x v
  | .RCall f dst args =>
      if isModQName f then .RCall (barrettName q) dst args
      else .RCall f dst args
  | .RCallSwap f d1 d2 args =>
      if isModQName f then .RCallSwap (barrettName q) d1 d2 args
      else .RCallSwap f d1 d2 args
  | .RCloneCall cv ct od inner dest args =>
      if isModQName inner then .RCloneCall cv ct od (barrettName q) dest args
      else .RCloneCall cv ct od inner dest args
  | .RIfNz cond ct cf => .RIfNz cond (barrettReduce q ct) (barrettReduce q cf)
  | .RWhileNz cond body => .RWhileNz cond (barrettReduce q body)
  | .RFor x n body => .RFor x n (barrettReduce q body)
  | .RForRuntime x b body => .RForRuntime x b (barrettReduce q body)
  | .RLimbStore loc idx v => .RLimbStore loc idx v
  | .RLimbStoreExpr loc idx e => .RLimbStoreExpr loc idx e
  | .RCallN f dests args => .RCallN f dests args
  | .RSelect dst sel s0 s1 => .RSelect dst sel s0 s1
  | .RAssert label => .RAssert label
  | .RBlock body => .RBlock (barrettReduce q body)
  | .RFnDef name params returns body cont =>
      .RFnDef name params returns (barrettReduce q body) (barrettReduce q cont)
  | .RFnCall f dests args => .RFnCall f dests args
  | .RTupleLoad dst src idx => .RTupleLoad dst src idx
  | .RArrStore arr idxVar src => .RArrStore arr idxVar src
  | .RArrLoad dst src idxVar => .RArrLoad dst src idxVar
  | .RScalarSetExpr x e => .RScalarSetExpr x e
  | .RArrStoreLit arr idx src => .RArrStoreLit arr idx src
  | .RArrLoadLit dst src idx => .RArrLoadLit dst src idx
  | .RCallDstThreaded f dst args =>
      if isModQName f then .RCallDstThreaded (barrettName q) dst args
      else .RCallDstThreaded f dst args
  | .RCopy dst src => .RCopy dst src

/-! ## §3  Per-leaf agreement assumption

The pass's soundness requires that the `LeafSpec`'s Barrett-q leaf
agrees with the abstract `"mod_q"`/`"reduce"` leaf on every
invocation.  We encode this as a `Prop`-level predicate on the
`LeafSpec`, parameterised by `q`.

For concrete `LeafSpec` instances and concrete `q`, this is closable
by `decide` (since the leaf-call functions are pure and the relevant
input domain is finite once `dt` is fixed).  At the level of this
file we leave it as an externally-supplied hypothesis. -/

/-- Per-leaf agreement predicate: the `LeafSpec`'s Barrett-`q` leaf
    agrees with the abstract `"mod_q"` and `"reduce"` leaves on all
    inputs.  This is the soundness obligation for the Barrett pass. -/
def barrettAgreesModQ (leafSpec : LeafSpec) (q : Nat) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType)
    (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
    isModQName f = true →
    leafSpec.call (barrettName q) dt argTs oldV args =
      leafSpec.call f dt argTs oldV args

/-! ## §4  Correctness theorem

The pass preserves the big-step semantics: `barrettReduce q c`
produces the same final state as `c` for any starting state `rs`,
provided the agreement hypothesis holds.

Both directions are proved by induction on the `RustExec` derivation.
The interesting case is `call`, where the agreement hypothesis lets us
rewrite the post-state from `leafSpec.call f …` to
`leafSpec.call (barrettName q) …` (and back).  All other constructors
either have no `LowCT` subterms (identity-traversed by
`barrettReduce`) or recursive subterms (handled by the inductive
hypothesis).
-/

/-- Forward direction: any `RustExec` derivation lifts through the
    Barrett rewrite. -/
theorem barrettReduce_denote_forward
    {q : Nat} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : barrettAgreesModQ leafSpec q)
    {c : LowCT} {rs rs' : RustState}
    (h : RustExec N leafSpec c rs rs') :
    RustExec N leafSpec (barrettReduce q c) rs rs' := by
  induction h with
  | skip rs => simpa [barrettReduce] using RustExec.skip rs
  | seq c1 c2 rs r1 rs' _ _ ih1 ih2 =>
      simpa [barrettReduce] using
        RustExec.seq (barrettReduce q c1) (barrettReduce q c2) rs r1 rs' ih1 ih2
  | letZero x t body rs rs' _ ih =>
      simpa [barrettReduce] using RustExec.letZero x t _ rs rs' ih
  | letU64Zero x body rs rs' _ ih =>
      simpa [barrettReduce] using RustExec.letU64Zero x _ rs rs' ih
  | scalarSet x v rs =>
      simpa [barrettReduce] using RustExec.scalarSet (N := N) (leafSpec := leafSpec) x v rs
  | ifTrue e ct cf rs rs' v hv hne _ ih =>
      simpa [barrettReduce] using RustExec.ifTrue e _ _ rs rs' v hv hne ih
  | ifFalse e ct cf rs rs' hv _ ih =>
      simpa [barrettReduce] using RustExec.ifFalse e _ _ rs rs' hv ih
  | whileFalse e body rs hv =>
      simpa [barrettReduce] using RustExec.whileFalse (N := N) (leafSpec := leafSpec)
        e _ rs hv
  | whileTrue e body rs r1 rs' v hv hne _ _ ih1 ih2 =>
      -- The IH for the recursive while step is itself stated on the
      -- rewritten body's RWhileNz; `simp` normalises both sides.
      have h1 : RustExec N leafSpec (barrettReduce q body) rs r1 := ih1
      have h2 : RustExec N leafSpec (.RWhileNz e (barrettReduce q body)) r1 rs' := by
        simpa [barrettReduce] using ih2
      simpa [barrettReduce] using
        RustExec.whileTrue e (barrettReduce q body) rs r1 rs' v hv hne h1 h2
  | forZero x body rs =>
      simpa [barrettReduce] using RustExec.forZero (N := N) (leafSpec := leafSpec)
        x _ rs
  | forSucc x n body rs r1 rs' _ _ ih1 ih2 =>
      have h1 : RustExec N leafSpec (.RFor x n (barrettReduce q body)) rs r1 := by
        simpa [barrettReduce] using ih1
      have h2 : RustExec N leafSpec (barrettReduce q body) (rsSetScalar r1 x n) rs' := ih2
      simpa [barrettReduce] using
        RustExec.forSucc x n (barrettReduce q body) rs r1 rs' h1 h2
  | forRuntime x bound body rs rs' _ ih =>
      -- `barrettReduce` leaves scalars untouched, so `bound.evalState` is
      -- unchanged; delegate to the inner `RFor` IH and rewrap.
      have h1 : RustExec N leafSpec
          (.RFor x (bound.evalState rs) (barrettReduce q body)) rs rs' := by
        simpa [barrettReduce] using ih
      simpa [barrettReduce] using
        RustExec.forRuntime x bound (barrettReduce q body) rs rs' h1
  | call f dest args rs oldDestV argList hLookup hArgList hArgs =>
      -- Case split on whether `f` is recognised.
      by_cases hf : isModQName f = true
      · -- Recognised: rewrite the call to `barrettName q` and use
        -- the agreement to identify the post-states.
        have hPostEq :
            leafSpec.call (barrettName q) dest.locDst (args.map (·.locDst))
                oldDestV argList =
              leafSpec.call f dest.locDst (args.map (·.locDst))
                oldDestV argList := by
          exact hAgree f dest.locDst (args.map (·.locDst)) oldDestV argList hf
        have hExecB :
            RustExec N leafSpec (.RCall (barrettName q) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call (barrettName q) dest.locDst
                  (args.map (·.locDst)) oldDestV argList)) :=
          RustExec.call (barrettName q) dest args rs oldDestV argList
            hLookup hArgList hArgs
        -- Adjust the post-state to match what the goal expects.
        have hExecB' :
            RustExec N leafSpec (.RCall (barrettName q) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call f dest.locDst
                  (args.map (·.locDst)) oldDestV argList)) := by
          rw [← hPostEq]; exact hExecB
        -- Conclude by unfolding `barrettReduce` at the call.
        have hUnfold :
            barrettReduce q (.RCall f dest args) =
              .RCall (barrettName q) dest args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact hExecB'
      · -- Not recognised: the rewrite is identity.
        have hUnfold :
            barrettReduce q (.RCall f dest args) = .RCall f dest args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact RustExec.call f dest args rs oldDestV argList hLookup hArgList hArgs
  | cloneCall cv ct od inner dest args rs rsClone rs' hrs _ ihInner =>
      -- The IH gives a RustExec of `barrettReduce q (RCall inner …)`.
      -- Case split on whether `inner` is recognised so we can pick
      -- the correct rewritten `RCloneCall` shape.
      by_cases hf : isModQName inner = true
      · -- Recognised: the inner call is rewritten to `barrettName q`.
        have hInner' :
            RustExec N leafSpec (.RCall (barrettName q) dest args) rsClone rs' := by
          have := ihInner
          simp [barrettReduce, hf] at this
          exact this
        have hUnfold :
            barrettReduce q (.RCloneCall cv ct od inner dest args) =
              .RCloneCall cv ct od (barrettName q) dest args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact RustExec.cloneCall cv ct od (barrettName q) dest args
                rs rsClone rs' hrs hInner'
      · -- Not recognised: identity.
        have hInner' :
            RustExec N leafSpec (.RCall inner dest args) rsClone rs' := by
          have := ihInner
          simp [barrettReduce, hf] at this
          exact this
        have hUnfold :
            barrettReduce q (.RCloneCall cv ct od inner dest args) =
              .RCloneCall cv ct od inner dest args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact RustExec.cloneCall cv ct od inner dest args
                rs rsClone rs' hrs hInner'
  | callSwap f dest1 dest2 args rs rs1 rs' _ _ ih1 ih2 =>
      -- Both IHs are RustExecs of `barrettReduce q (RCall f …)`.  Case
      -- split on `f` to pick the rewritten `RCallSwap` shape.
      by_cases hf : isModQName f = true
      · have h1' : RustExec N leafSpec
            (.RCall (barrettName q) dest1 args) rs rs1 := by
          have := ih1; simp [barrettReduce, hf] at this; exact this
        have h2' : RustExec N leafSpec
            (.RCall (barrettName q) dest2 args) rs1 rs' := by
          have := ih2; simp [barrettReduce, hf] at this; exact this
        have hUnfold :
            barrettReduce q (.RCallSwap f dest1 dest2 args) =
              .RCallSwap (barrettName q) dest1 dest2 args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact RustExec.callSwap (barrettName q) dest1 dest2 args rs rs1 rs' h1' h2'
      · have h1' : RustExec N leafSpec (.RCall f dest1 args) rs rs1 := by
          have := ih1; simp [barrettReduce, hf] at this; exact this
        have h2' : RustExec N leafSpec (.RCall f dest2 args) rs1 rs' := by
          have := ih2; simp [barrettReduce, hf] at this; exact this
        have hUnfold :
            barrettReduce q (.RCallSwap f dest1 dest2 args) =
              .RCallSwap f dest1 dest2 args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact RustExec.callSwap f dest1 dest2 args rs rs1 rs' h1' h2'
  | limbStore loc idx v rs oldDestV hLookup =>
      simpa [barrettReduce] using
        RustExec.limbStore loc idx v rs oldDestV hLookup
  | limbStoreExpr loc idx e rs oldDestV hLookup =>
      simpa [barrettReduce] using
        RustExec.limbStoreExpr loc idx e rs oldDestV hLookup
  | callN f dests args rs argList hArg hArgsBound hDestsBound =>
      simpa [barrettReduce] using
        RustExec.callN (N := N) (leafSpec := leafSpec) f dests args rs argList
          hArg hArgsBound hDestsBound
  | selectFalse dst sel src0 src1 rs h srcV hsel hLookup =>
      simpa [barrettReduce] using
        RustExec.selectFalse (N := N) (leafSpec := leafSpec)
          dst sel src0 src1 rs h srcV hsel hLookup
  | selectTrue dst sel src0 src1 rs h v srcV hsel hne hLookup =>
      simpa [barrettReduce] using
        RustExec.selectTrue (N := N) (leafSpec := leafSpec)
          dst sel src0 src1 rs h v srcV hsel hne hLookup
  | assert label rs =>
      simpa [barrettReduce] using
        RustExec.assert (N := N) (leafSpec := leafSpec) label rs
  | block body rs rs' _ ih =>
      simpa [barrettReduce] using RustExec.block _ rs rs' ih
  | tupleLoad dst src idx rs oldV srcV hDst hSrc =>
      simpa [barrettReduce] using
        RustExec.tupleLoad dst src idx rs oldV srcV hDst hSrc
  | arrStore arr idxVar src rs idx oldV srcV hIdx hArr hSrc =>
      simpa [barrettReduce] using
        RustExec.arrStore arr idxVar src rs idx oldV srcV hIdx hArr hSrc
  | arrLoad dst src idxVar rs idx oldV srcV hIdx hDst hSrc =>
      simpa [barrettReduce] using
        RustExec.arrLoad dst src idxVar rs idx oldV srcV hIdx hDst hSrc
  | scalarSetExpr x e rs =>
      simpa [barrettReduce] using
        RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) x e rs
  | arrStoreLit arr idx src rs oldV srcV hArr hSrc =>
      simpa [barrettReduce] using
        RustExec.arrStoreLit arr idx src rs oldV srcV hArr hSrc
  | arrLoadLit dst src idx rs oldV srcV hDst hSrc =>
      simpa [barrettReduce] using
        RustExec.arrLoadLit dst src idx rs oldV srcV hDst hSrc
  | copy dst src rs hT srcV hSrc =>
      exact RustExec.copy dst src rs hT srcV hSrc
  | callDstThreaded f dest args rs oldDestV argList hLookup hArgList hArgs =>
      by_cases hf : isModQName f = true
      · have hPostEq :
            leafSpec.call (barrettName q) dest.locDst
                ((dest :: args).map (·.locDst)) oldDestV argList =
              leafSpec.call f dest.locDst ((dest :: args).map (·.locDst))
                oldDestV argList :=
          hAgree f dest.locDst ((dest :: args).map (·.locDst)) oldDestV argList hf
        have hExecB :
            RustExec N leafSpec (.RCallDstThreaded (barrettName q) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call (barrettName q) dest.locDst
                  ((dest :: args).map (·.locDst)) oldDestV argList)) :=
          RustExec.callDstThreaded (barrettName q) dest args rs oldDestV argList
            hLookup hArgList hArgs
        have hExecB' :
            RustExec N leafSpec (.RCallDstThreaded (barrettName q) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call f dest.locDst
                  ((dest :: args).map (·.locDst)) oldDestV argList)) := by
          rw [← hPostEq]; exact hExecB
        have hUnfold :
            barrettReduce q (.RCallDstThreaded f dest args) =
              .RCallDstThreaded (barrettName q) dest args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact hExecB'
      · have hUnfold :
            barrettReduce q (.RCallDstThreaded f dest args) =
              .RCallDstThreaded f dest args := by
          simp [barrettReduce, hf]
        rw [hUnfold]
        exact RustExec.callDstThreaded f dest args rs oldDestV argList
          hLookup hArgList hArgs

/-! ### §4.2  Reverse direction

For the reverse direction, we induct on the source command `c` and
invert the `RustExec` derivation on the rewritten side.  The rewrite
is structure-preserving up to call-name substitution; on each
constructor `cases h` exposes the same derivation shape on the
original command, modulo the per-leaf agreement at `RCall`/`RCallSwap`/
`RCloneCall`. -/

/-- Reversal along the `RFor` spine: when every `RustExec` of `body'` lifts to
    one of `body`, every `RustExec` of `RFor x n body'` lifts to one of
    `RFor x n body`.

    The command is carried as a variable `c0` with a defining equation so that
    the induction on the derivation has a uniform motive, and the trip count
    `n0` is quantified inside that motive so the `forSucc` step can specialise
    it to the shorter count.  Every `RustExec` rule is listed: the rules other
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

/-- Reverse direction: any `RustExec` of the rewritten command lifts
    to one on the source command. -/
theorem barrettReduce_denote_reverse
    {q : Nat} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : barrettAgreesModQ leafSpec q)
    : ∀ {c : LowCT} {rs rs' : RustState},
      RustExec N leafSpec (barrettReduce q c) rs rs' →
      RustExec N leafSpec c rs rs' := by
  intro c
  induction c with
  | RSkip => intro rs rs' h; simpa [barrettReduce] using h
  | RSeq c1 c2 ih1 ih2 =>
      intro rs rs' h
      simp only [barrettReduce] at h
      cases h with
      | seq _ _ _ r1 _ h1 h2 =>
          exact RustExec.seq c1 c2 rs r1 rs' (ih1 h1) (ih2 h2)
  | RLetZero x t body ih =>
      intro rs rs' h
      simp only [barrettReduce] at h
      cases h with
      | letZero _ _ _ _ _ hBody =>
          exact RustExec.letZero x t body rs rs' (ih hBody)
  | RLetU64Zero x body ih =>
      intro rs rs' h
      simp only [barrettReduce] at h
      cases h with
      | letU64Zero _ _ _ _ hBody =>
          exact RustExec.letU64Zero x body rs rs' (ih hBody)
  | RScalarSet x v => intro rs rs' h; simpa [barrettReduce] using h
  | RCall f dst args =>
      intro rs rs' h
      by_cases hf : isModQName f = true
      · -- Rewritten to `RCall (barrettName q) dst args`.  Invert and
        -- transport the post-state via `hAgree`.
        have hEq : barrettReduce q (.RCall f dst args) =
            .RCall (barrettName q) dst args := by simp [barrettReduce, hf]
        rw [hEq] at h
        cases h with
        | call _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
            have hPostEq :
                leafSpec.call (barrettName q) dst.locDst (args.map (·.locDst))
                    oldDestV argList =
                  leafSpec.call f dst.locDst (args.map (·.locDst))
                    oldDestV argList :=
              hAgree f dst.locDst (args.map (·.locDst)) oldDestV argList hf
            -- The post-state from `cases` is in terms of `barrettName q`;
            -- rewrite to `f` and re-apply the constructor.
            have hExec :
                RustExec N leafSpec (.RCall f dst args) rs
                  (locatedUpdate rs dst
                    (leafSpec.call f dst.locDst (args.map (·.locDst))
                      oldDestV argList)) :=
              RustExec.call f dst args rs oldDestV argList
                hLookup hArgList hArgs
            rw [hPostEq]; exact hExec
      · -- Identity rewrite.
        have hEq : barrettReduce q (.RCall f dst args) =
            .RCall f dst args := by simp [barrettReduce, hf]
        rw [hEq] at h; exact h
  | RCallSwap f d1 d2 args =>
      intro rs rs' h
      by_cases hf : isModQName f = true
      · have hEq : barrettReduce q (.RCallSwap f d1 d2 args) =
            .RCallSwap (barrettName q) d1 d2 args := by simp [barrettReduce, hf]
        rw [hEq] at h
        cases h with
        | callSwap _ _ _ _ _ rs1 _ h1 h2 =>
            -- Both inner calls are at name `barrettName q`; reverse each
            -- by inverting the RCall constructor and applying hAgree.
            -- Reuse the RCall reverse handling inline.
            have h1' : RustExec N leafSpec (.RCall f d1 args) rs rs1 := by
              cases h1 with
              | call _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
                  have hPostEq :=
                    hAgree f d1.locDst (args.map (·.locDst)) oldDestV argList hf
                  rw [hPostEq]
                  exact RustExec.call f d1 args rs oldDestV argList
                    hLookup hArgList hArgs
            have h2' : RustExec N leafSpec (.RCall f d2 args) rs1 rs' := by
              cases h2 with
              | call _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
                  have hPostEq :=
                    hAgree f d2.locDst (args.map (·.locDst)) oldDestV argList hf
                  rw [hPostEq]
                  exact RustExec.call f d2 args rs1 oldDestV argList
                    hLookup hArgList hArgs
            exact RustExec.callSwap f d1 d2 args rs rs1 rs' h1' h2'
      · have hEq : barrettReduce q (.RCallSwap f d1 d2 args) =
            .RCallSwap f d1 d2 args := by simp [barrettReduce, hf]
        rw [hEq] at h; exact h
  | RCloneCall cv ct od inner dest args =>
      intro rs rs' h
      by_cases hf : isModQName inner = true
      · have hEq : barrettReduce q (.RCloneCall cv ct od inner dest args) =
            .RCloneCall cv ct od (barrettName q) dest args := by
          simp [barrettReduce, hf]
        rw [hEq] at h
        cases h with
        | cloneCall _ _ _ _ _ _ _ rsClone _ hrs hInner =>
            -- Reverse the inner RCall as above.
            have hInner' :
                RustExec N leafSpec (.RCall inner dest args) rsClone rs' := by
              cases hInner with
              | call _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
                  have hPostEq :=
                    hAgree inner dest.locDst (args.map (·.locDst))
                      oldDestV argList hf
                  rw [hPostEq]
                  exact RustExec.call inner dest args rsClone oldDestV argList
                    hLookup hArgList hArgs
            exact RustExec.cloneCall cv ct od inner dest args rs rsClone rs'
                    hrs hInner'
      · have hEq : barrettReduce q (.RCloneCall cv ct od inner dest args) =
            .RCloneCall cv ct od inner dest args := by simp [barrettReduce, hf]
        rw [hEq] at h; exact h
  | RIfNz cond ct cf ihT ihF =>
      intro rs rs' h
      simp only [barrettReduce] at h
      cases h with
      | ifTrue _ _ _ _ _ v hv hne hBody =>
          exact RustExec.ifTrue cond ct cf rs rs' v hv hne (ihT hBody)
      | ifFalse _ _ _ _ _ hv hBody =>
          exact RustExec.ifFalse cond ct cf rs rs' hv (ihF hBody)
  | RWhileNz cond body ih =>
      intro rs rs' h
      -- Generalised induction on the RustExec derivation, using a
      -- carrier-of-rewritten-body invariant.
      simp only [barrettReduce] at h
      -- Strengthen with an auxiliary induction on the derivation of
      -- the rewritten while loop.
      have aux : ∀ c0 rs0 rs0',
          RustExec N leafSpec c0 rs0 rs0' →
          c0 = .RWhileNz cond (barrettReduce q body) →
          RustExec N leafSpec (.RWhileNz cond body) rs0 rs0' := by
        intro c0 rs0 rs0' h0
        induction h0 with
        | whileFalse e b rs hv =>
            intro hEq
            cases hEq
            exact RustExec.whileFalse cond body rs hv
        | whileTrue e b rs r1 rs' v hv hne hBody hRest ihBody ihRest =>
            intro hEq
            cases hEq
            exact RustExec.whileTrue cond body rs r1 rs' v hv hne
              (ih hBody) (ihRest rfl)
        -- The remaining rules are at commands whose head constructor is not
        -- `RWhileNz`, so the defining equation refutes them.  They are listed
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
      simp only [barrettReduce] at h
      exact rfor_spine_reverse (fun _ _ hb => ih hb) _ rs rs' h n rfl
  | RForRuntime x bnd body ih =>
      intro rs rs' h
      simp only [barrettReduce] at h
      -- Invert the runtime loop to its inner `RFor` at the entry trip count,
      -- reverse that along the `RFor` spine, then rewrap with `forRuntime`.
      cases h with
      | forRuntime _ _ _ _ _ hInner =>
          exact RustExec.forRuntime x bnd body rs rs'
            (rfor_spine_reverse (fun _ _ hb => ih hb) _ rs rs' hInner _ rfl)
  | RLimbStore loc idx v => intro rs rs' h; simpa [barrettReduce] using h
  | RLimbStoreExpr loc idx e => intro rs rs' h; simpa [barrettReduce] using h
  | RCallN f dests args => intro rs rs' h; simpa [barrettReduce] using h
  | RSelect dst sel s0 s1 => intro rs rs' h; simpa [barrettReduce] using h
  | RAssert label => intro rs rs' h; simpa [barrettReduce] using h
  | RBlock body ih =>
      intro rs rs' h
      simp only [barrettReduce] at h
      cases h with
      | block _ _ _ hBody => exact RustExec.block body rs rs' (ih hBody)
  | RFnDef _ _ _ _ _ _ _ =>
      intro _ _ h
      simp only [barrettReduce] at h
      cases h
  | RFnCall f dests args => intro rs rs' h; simpa [barrettReduce] using h
  | RTupleLoad dst src idx => intro rs rs' h; simpa [barrettReduce] using h
  | RArrStore arr idxVar src => intro rs rs' h; simpa [barrettReduce] using h
  | RArrLoad dst src idxVar => intro rs rs' h; simpa [barrettReduce] using h
  | RScalarSetExpr x e => intro rs rs' h; simpa [barrettReduce] using h
  | RArrStoreLit arr idx src => intro rs rs' h; simpa [barrettReduce] using h
  | RArrLoadLit dst src idx => intro rs rs' h; simpa [barrettReduce] using h
  | RCopy dst src => intro rs rs' h; simpa [barrettReduce] using h
  | RCallDstThreaded f dst args =>
      intro rs rs' h
      by_cases hf : isModQName f = true
      · have hEq : barrettReduce q (.RCallDstThreaded f dst args) =
            .RCallDstThreaded (barrettName q) dst args := by simp [barrettReduce, hf]
        rw [hEq] at h
        cases h with
        | callDstThreaded _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
            have hPostEq :
                leafSpec.call (barrettName q) dst.locDst
                    ((dst :: args).map (·.locDst)) oldDestV argList =
                  leafSpec.call f dst.locDst ((dst :: args).map (·.locDst))
                    oldDestV argList :=
              hAgree f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList hf
            have hExec :
                RustExec N leafSpec (.RCallDstThreaded f dst args) rs
                  (locatedUpdate rs dst
                    (leafSpec.call f dst.locDst ((dst :: args).map (·.locDst))
                      oldDestV argList)) :=
              RustExec.callDstThreaded f dst args rs oldDestV argList
                hLookup hArgList hArgs
            rw [hPostEq]; exact hExec
      · have hEq : barrettReduce q (.RCallDstThreaded f dst args) =
            .RCallDstThreaded f dst args := by simp [barrettReduce, hf]
        rw [hEq] at h; exact h

/-- The Barrett rewrite preserves the big-step semantics, modulo the
    per-leaf agreement assumption.  This is the **soundness anchor** for
    Pass 1.1 — combine with a concrete `LeafSpec` whose `barrettAgreesModQ`
    is closable by `decide`. -/
theorem barrettReduce_denote_eq
    (q : Nat) (N : Nat) (leafSpec : LeafSpec)
    (hAgree : barrettAgreesModQ leafSpec q)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (barrettReduce q c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  ⟨barrettReduce_denote_reverse hAgree, barrettReduce_denote_forward hAgree⟩

end CatCrypt.Crypto.Optimizer.BarrettReduce
