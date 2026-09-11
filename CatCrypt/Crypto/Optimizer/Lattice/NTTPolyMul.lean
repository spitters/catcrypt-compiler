/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Pass 3.1 — NTT-backed Polynomial Multiplication

First Tier-3 (algorithmic-rewrite) pass of CatCrypt's verified optimizing
compiler.  Rewrites `RCall "poly_mul" [a, b]` to
`RCall s!"ntt_poly_mul_{q}_{n}"` when the polynomial parameters
`(q, n)` are statically known.

## Soundness

The pass's correctness reduces to per-leaf agreement: the `LeafSpec`'s
`s!"ntt_poly_mul_{q}_{n}"` leaf must produce semantically identical
outputs to the abstract `"poly_mul"` leaf at every call site.  This is
an external assumption on the `LeafSpec` (`nttAgreesPolyMul`); it is
discharged on instantiation against a concrete NTT-backed Rust kernel.

The algebraic content backing the agreement obligation lives in
`CompPoly.Univariate.NTT.FastMul`:

* `CompPoly.CPolynomial.NTT.fastMulImpl_eq_mul`
* `CompPoly.CPolynomial.NTT.safeFastMul_eq_mul`

Under `Domain.fits D p.val q.val`, the NTT-backed implementation
`fastMulImpl D p q` equals canonical multiplication `p * q`.  The
agreement obligation is then a one-step transport along this equality
once the concrete `LeafSpec` is instantiated.

## Composition

This pass is one slot in the optimizer pipeline (orchestrator Tier 4.1,
`Optimizer/Pipeline.lean`).  Compose with `BarrettReduce` /
`MontgomeryReduce` to get coefficient-level + algorithmic rewrites in
a single pipeline application.

## Naming

The generated leaf name encodes both modulus and degree
(`ntt_poly_mul_3329_256`).  This lets a single `LeafSpec` carry
multiple NTT specialisations (e.g. ML-KEM and ML-DSA share
`n = 256` but differ in `q`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Pattern recognition

A `LowCT` is a "polynomial multiplication site" if it is
`RCall "poly_mul"` (the canonical name used by the ML-KEM hand
kernels in `MLKEM/MlkemLowCT.lean`) or `"polymul"` (alternative
spelling used by some haxpipe extractions).
-/

/-- Predicate: the call name `f` is one of the recognised
    polynomial-multiplication site names. -/
def isPolyMulName (f : String) : Bool :=
  f == "poly_mul" || f == "polymul"

@[simp] theorem isPolyMulName_poly_mul : isPolyMulName "poly_mul" = true := by
  decide

@[simp] theorem isPolyMulName_polymul : isPolyMulName "polymul" = true := by
  decide

/-! ## §2  Rewrite pass

`nttPolyMul q n` walks the LowCT AST and replaces every recognised
poly-mul call with `s!"ntt_poly_mul_{q}_{n}"`.  Structure-preserving:
all other constructors are traversed compositionally; constructors
with no nested `LowCT` act as identity.
-/

/-- The name of the NTT-backed poly-mul leaf for parameters `(q, n)`. -/
@[inline] def nttPolyMulName (q n : Nat) : String := s!"ntt_poly_mul_{q}_{n}"

/-- The NTT poly-mul rewrite pass parameterised by the modulus `q` and
    polynomial degree `n`.  Replaces `RCall "poly_mul"`/`RCall "polymul"`
    with `RCall (nttPolyMulName q n)`; recurses through every
    constructor with a nested `LowCT` body.  Constructors without
    nested commands act as identity. -/
def nttPolyMul (q n : Nat) : LowCT → LowCT
  | .RSkip => .RSkip
  | .RSeq c1 c2 => .RSeq (nttPolyMul q n c1) (nttPolyMul q n c2)
  | .RLetZero x t body => .RLetZero x t (nttPolyMul q n body)
  | .RLetU64Zero x body => .RLetU64Zero x (nttPolyMul q n body)
  | .RScalarSet x v => .RScalarSet x v
  | .RCall f dst args =>
      if isPolyMulName f then .RCall (nttPolyMulName q n) dst args
      else .RCall f dst args
  | .RCallSwap f d1 d2 args =>
      if isPolyMulName f then .RCallSwap (nttPolyMulName q n) d1 d2 args
      else .RCallSwap f d1 d2 args
  | .RCloneCall cv ct od inner dest args =>
      if isPolyMulName inner then
        .RCloneCall cv ct od (nttPolyMulName q n) dest args
      else .RCloneCall cv ct od inner dest args
  | .RIfNz cond ct cf => .RIfNz cond (nttPolyMul q n ct) (nttPolyMul q n cf)
  | .RWhileNz cond body => .RWhileNz cond (nttPolyMul q n body)
  | .RFor x k body => .RFor x k (nttPolyMul q n body)
  | .RForRuntime x b body => .RForRuntime x b (nttPolyMul q n body)
  | .RLimbStore loc idx v => .RLimbStore loc idx v
  | .RLimbStoreExpr loc idx e => .RLimbStoreExpr loc idx e
  | .RCallN f dests args => .RCallN f dests args
  | .RSelect dst sel s0 s1 => .RSelect dst sel s0 s1
  | .RAssert label => .RAssert label
  | .RBlock body => .RBlock (nttPolyMul q n body)
  | .RFnDef name params returns body cont =>
      .RFnDef name params returns (nttPolyMul q n body) (nttPolyMul q n cont)
  | .RFnCall f dests args => .RFnCall f dests args
  | .RTupleLoad dst src idx => .RTupleLoad dst src idx
  | .RArrStore arr idxVar src => .RArrStore arr idxVar src
  | .RArrLoad dst src idxVar => .RArrLoad dst src idxVar
  | .RScalarSetExpr x e => .RScalarSetExpr x e
  | .RArrStoreLit arr idx src => .RArrStoreLit arr idx src
  | .RArrLoadLit dst src idx => .RArrLoadLit dst src idx
  | .RCallDstThreaded f dst args =>
      if isPolyMulName f then .RCallDstThreaded (nttPolyMulName q n) dst args
      else .RCallDstThreaded f dst args

/-! ## §3  Per-leaf agreement assumption

The pass's soundness requires that the `LeafSpec`'s NTT poly-mul leaf
agrees with the abstract `"poly_mul"` leaf on every invocation.  We
encode this as a `Prop`-level predicate on the `LeafSpec`, parameterised
by `(q, n)`.

For a concrete `LeafSpec` whose NTT leaf is built on
`CompPoly.NTT.fastMulImpl` (and whose `"poly_mul"` leaf is canonical
polynomial multiplication followed by reduction mod `X^n + 1`), the
agreement is provable via `CompPoly.CPolynomial.NTT.fastMulImpl_eq_mul`
under the precondition `Domain.fits D p.val q.val`.

At the level of this file we leave the agreement as an externally
supplied hypothesis. -/

/-- Per-leaf agreement predicate: the `LeafSpec`'s NTT poly-mul leaf for
    parameters `(q, n)` agrees with the abstract `"poly_mul"` /
    `"polymul"` leaves on all inputs.  This is the soundness obligation
    for the NTT poly-mul pass. -/
def nttAgreesPolyMul (leafSpec : LeafSpec) (q n : Nat) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType)
    (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
    isPolyMulName f = true →
    leafSpec.call (nttPolyMulName q n) dt argTs oldV args =
      leafSpec.call f dt argTs oldV args

/-! ## §4  Correctness theorem

The pass preserves the big-step semantics: `nttPolyMul q n c` produces
the same final state as `c` for any starting state `rs`, provided the
agreement hypothesis holds.

Both directions are proved by induction.  The interesting case is
`call`, where the agreement hypothesis lets us rewrite the post-state
from `leafSpec.call f …` to `leafSpec.call (nttPolyMulName q n) …`.
All other constructors either have no `LowCT` subterms (identity-
traversed by `nttPolyMul`) or recursive subterms (handled by the
inductive hypothesis).
-/

/-- Forward direction: any `RustExec` derivation lifts through the
    NTT poly-mul rewrite. -/
theorem nttPolyMul_denote_forward
    {q n : Nat} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : nttAgreesPolyMul leafSpec q n)
    {c : LowCT} {rs rs' : RustState}
    (h : RustExec N leafSpec c rs rs') :
    RustExec N leafSpec (nttPolyMul q n c) rs rs' := by
  induction h with
  | skip rs => simpa [nttPolyMul] using RustExec.skip rs
  | seq c1 c2 rs r1 rs' _ _ ih1 ih2 =>
      simpa [nttPolyMul] using
        RustExec.seq (nttPolyMul q n c1) (nttPolyMul q n c2) rs r1 rs' ih1 ih2
  | letZero x t body rs rs' _ ih =>
      simpa [nttPolyMul] using RustExec.letZero x t _ rs rs' ih
  | letU64Zero x body rs rs' _ ih =>
      simpa [nttPolyMul] using RustExec.letU64Zero x _ rs rs' ih
  | scalarSet x v rs =>
      simpa [nttPolyMul] using
        RustExec.scalarSet (N := N) (leafSpec := leafSpec) x v rs
  | ifTrue e ct cf rs rs' v hv hne _ ih =>
      simpa [nttPolyMul] using RustExec.ifTrue e _ _ rs rs' v hv hne ih
  | ifFalse e ct cf rs rs' hv _ ih =>
      simpa [nttPolyMul] using RustExec.ifFalse e _ _ rs rs' hv ih
  | whileFalse e body rs hv =>
      simpa [nttPolyMul] using
        RustExec.whileFalse (N := N) (leafSpec := leafSpec) e _ rs hv
  | whileTrue e body rs r1 rs' v hv hne _ _ ih1 ih2 =>
      have h1 : RustExec N leafSpec (nttPolyMul q n body) rs r1 := ih1
      have h2 : RustExec N leafSpec (.RWhileNz e (nttPolyMul q n body)) r1 rs' := by
        simpa [nttPolyMul] using ih2
      simpa [nttPolyMul] using
        RustExec.whileTrue e (nttPolyMul q n body) rs r1 rs' v hv hne h1 h2
  | forZero x body rs =>
      simpa [nttPolyMul] using
        RustExec.forZero (N := N) (leafSpec := leafSpec) x _ rs
  | forSucc x k body rs r1 rs' _ _ ih1 ih2 =>
      have h1 : RustExec N leafSpec (.RFor x k (nttPolyMul q n body)) rs r1 := by
        simpa [nttPolyMul] using ih1
      have h2 : RustExec N leafSpec (nttPolyMul q n body) (rsSetScalar r1 x k) rs' :=
        ih2
      simpa [nttPolyMul] using
        RustExec.forSucc x k (nttPolyMul q n body) rs r1 rs' h1 h2
  | forRuntime x bound body rs rs' _ ih =>
      have h1 : RustExec N leafSpec
          (.RFor x (bound.evalState rs) (nttPolyMul q n body)) rs rs' := by
        simpa [nttPolyMul] using ih
      simpa [nttPolyMul] using
        RustExec.forRuntime x bound (nttPolyMul q n body) rs rs' h1
  | call f dest args rs oldDestV argList hLookup hArgList hArgs =>
      by_cases hf : isPolyMulName f = true
      · have hPostEq :
            leafSpec.call (nttPolyMulName q n) dest.locDst (args.map (·.locDst))
                oldDestV argList =
              leafSpec.call f dest.locDst (args.map (·.locDst))
                oldDestV argList :=
          hAgree f dest.locDst (args.map (·.locDst)) oldDestV argList hf
        have hExecB :
            RustExec N leafSpec (.RCall (nttPolyMulName q n) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call (nttPolyMulName q n) dest.locDst
                  (args.map (·.locDst)) oldDestV argList)) :=
          RustExec.call (nttPolyMulName q n) dest args rs oldDestV argList
            hLookup hArgList hArgs
        have hExecB' :
            RustExec N leafSpec (.RCall (nttPolyMulName q n) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call f dest.locDst
                  (args.map (·.locDst)) oldDestV argList)) := by
          rw [← hPostEq]; exact hExecB
        have hUnfold :
            nttPolyMul q n (.RCall f dest args) =
              .RCall (nttPolyMulName q n) dest args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact hExecB'
      · have hUnfold :
            nttPolyMul q n (.RCall f dest args) = .RCall f dest args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact RustExec.call f dest args rs oldDestV argList hLookup hArgList hArgs
  | cloneCall cv ct od inner dest args rs rsClone rs' hrs _ ihInner =>
      by_cases hf : isPolyMulName inner = true
      · have hInner' :
            RustExec N leafSpec (.RCall (nttPolyMulName q n) dest args) rsClone rs' := by
          have := ihInner
          simp [nttPolyMul, hf] at this
          exact this
        have hUnfold :
            nttPolyMul q n (.RCloneCall cv ct od inner dest args) =
              .RCloneCall cv ct od (nttPolyMulName q n) dest args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact RustExec.cloneCall cv ct od (nttPolyMulName q n) dest args
                rs rsClone rs' hrs hInner'
      · have hInner' :
            RustExec N leafSpec (.RCall inner dest args) rsClone rs' := by
          have := ihInner
          simp [nttPolyMul, hf] at this
          exact this
        have hUnfold :
            nttPolyMul q n (.RCloneCall cv ct od inner dest args) =
              .RCloneCall cv ct od inner dest args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact RustExec.cloneCall cv ct od inner dest args
                rs rsClone rs' hrs hInner'
  | callSwap f dest1 dest2 args rs rs1 rs' _ _ ih1 ih2 =>
      by_cases hf : isPolyMulName f = true
      · have h1' : RustExec N leafSpec
            (.RCall (nttPolyMulName q n) dest1 args) rs rs1 := by
          have := ih1; simp [nttPolyMul, hf] at this; exact this
        have h2' : RustExec N leafSpec
            (.RCall (nttPolyMulName q n) dest2 args) rs1 rs' := by
          have := ih2; simp [nttPolyMul, hf] at this; exact this
        have hUnfold :
            nttPolyMul q n (.RCallSwap f dest1 dest2 args) =
              .RCallSwap (nttPolyMulName q n) dest1 dest2 args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact RustExec.callSwap (nttPolyMulName q n) dest1 dest2 args rs rs1 rs' h1' h2'
      · have h1' : RustExec N leafSpec (.RCall f dest1 args) rs rs1 := by
          have := ih1; simp [nttPolyMul, hf] at this; exact this
        have h2' : RustExec N leafSpec (.RCall f dest2 args) rs1 rs' := by
          have := ih2; simp [nttPolyMul, hf] at this; exact this
        have hUnfold :
            nttPolyMul q n (.RCallSwap f dest1 dest2 args) =
              .RCallSwap f dest1 dest2 args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact RustExec.callSwap f dest1 dest2 args rs rs1 rs' h1' h2'
  | limbStore loc idx v rs oldDestV hLookup =>
      simpa [nttPolyMul] using
        RustExec.limbStore loc idx v rs oldDestV hLookup
  | limbStoreExpr loc idx e rs oldDestV hLookup =>
      simpa [nttPolyMul] using
        RustExec.limbStoreExpr loc idx e rs oldDestV hLookup
  | callN f dests args rs argList hArg hArgsBound hDestsBound =>
      simpa [nttPolyMul] using
        RustExec.callN (N := N) (leafSpec := leafSpec) f dests args rs argList
          hArg hArgsBound hDestsBound
  | selectFalse dst sel src0 src1 rs h srcV hsel hLookup =>
      simpa [nttPolyMul] using
        RustExec.selectFalse (N := N) (leafSpec := leafSpec)
          dst sel src0 src1 rs h srcV hsel hLookup
  | selectTrue dst sel src0 src1 rs h v srcV hsel hne hLookup =>
      simpa [nttPolyMul] using
        RustExec.selectTrue (N := N) (leafSpec := leafSpec)
          dst sel src0 src1 rs h v srcV hsel hne hLookup
  | assert label rs =>
      simpa [nttPolyMul] using
        RustExec.assert (N := N) (leafSpec := leafSpec) label rs
  | block body rs rs' _ ih =>
      simpa [nttPolyMul] using RustExec.block _ rs rs' ih
  | tupleLoad dst src idx rs oldV srcV hDst hSrc =>
      simpa [nttPolyMul] using
        RustExec.tupleLoad dst src idx rs oldV srcV hDst hSrc
  | arrStore arr idxVar src rs idx oldV srcV hIdx hArr hSrc =>
      simpa [nttPolyMul] using
        RustExec.arrStore arr idxVar src rs idx oldV srcV hIdx hArr hSrc
  | arrLoad dst src idxVar rs idx oldV srcV hIdx hDst hSrc =>
      simpa [nttPolyMul] using
        RustExec.arrLoad dst src idxVar rs idx oldV srcV hIdx hDst hSrc
  | scalarSetExpr x e rs =>
      simpa [nttPolyMul] using
        RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) x e rs
  | arrStoreLit arr idx src rs oldV srcV hArr hSrc =>
      simpa [nttPolyMul] using
        RustExec.arrStoreLit arr idx src rs oldV srcV hArr hSrc
  | arrLoadLit dst src idx rs oldV srcV hDst hSrc =>
      simpa [nttPolyMul] using
        RustExec.arrLoadLit dst src idx rs oldV srcV hDst hSrc
  | callDstThreaded f dest args rs oldDestV argList hLookup hArgList hArgs =>
      by_cases hf : isPolyMulName f = true
      · have hPostEq :
            leafSpec.call (nttPolyMulName q n) dest.locDst
                ((dest :: args).map (·.locDst)) oldDestV argList =
              leafSpec.call f dest.locDst ((dest :: args).map (·.locDst))
                oldDestV argList :=
          hAgree f dest.locDst ((dest :: args).map (·.locDst)) oldDestV argList hf
        have hExecB :
            RustExec N leafSpec (.RCallDstThreaded (nttPolyMulName q n) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call (nttPolyMulName q n) dest.locDst
                  ((dest :: args).map (·.locDst)) oldDestV argList)) :=
          RustExec.callDstThreaded (nttPolyMulName q n) dest args rs oldDestV argList
            hLookup hArgList hArgs
        have hExecB' :
            RustExec N leafSpec (.RCallDstThreaded (nttPolyMulName q n) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call f dest.locDst
                  ((dest :: args).map (·.locDst)) oldDestV argList)) := by
          rw [← hPostEq]; exact hExecB
        have hUnfold :
            nttPolyMul q n (.RCallDstThreaded f dest args) =
              .RCallDstThreaded (nttPolyMulName q n) dest args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact hExecB'
      · have hUnfold :
            nttPolyMul q n (.RCallDstThreaded f dest args) =
              .RCallDstThreaded f dest args := by
          simp [nttPolyMul, hf]
        rw [hUnfold]
        exact RustExec.callDstThreaded f dest args rs oldDestV argList
          hLookup hArgList hArgs

/-! ### §4.2  Reverse direction

For the reverse direction, we induct on the source command `c` and
invert the `RustExec` derivation on the rewritten side. -/

/-- Reversal along the `RFor` spine: when every `RustExec` of `body'` lifts to
    one of `body`, every `RustExec` of `RFor x k body'` lifts to one of
    `RFor x k body`.

    The command is carried as a variable `c0` with a defining equation so that
    the induction on the derivation has a uniform motive, and the trip count
    `k0` is quantified inside that motive so the `forSucc` step can specialise
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
      ∀ (k0 : Nat), c0 = .RFor x k0 body' →
      RustExec N leafSpec (.RFor x k0 body) rs0 rs0' := by
  intro c0 rs0 rs0' h0
  induction h0 with
  | forZero x' b rs =>
      intro k0 hEq; cases hEq; exact RustExec.forZero x body rs
  | forSucc x' k b rs r1 rs' _ hBody ihInner _ =>
      intro k0 hEq
      cases hEq
      exact RustExec.forSucc x k body rs r1 rs' (ihInner k rfl) (ih _ _ hBody)
  | skip | seq | letZero | letU64Zero | scalarSet | ifTrue | ifFalse
  | whileFalse | whileTrue | forRuntime | call | cloneCall | callSwap
  | limbStore | limbStoreExpr | callN | selectFalse | selectTrue
  | assert | block | tupleLoad | arrStore
  | arrLoad | arrStoreLit | arrLoadLit | scalarSetExpr
  | callDstThreaded => intro k0 hEq; cases hEq

/-- Reverse direction: any `RustExec` of the rewritten command lifts
    to one on the source command. -/
theorem nttPolyMul_denote_reverse
    {q n : Nat} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : nttAgreesPolyMul leafSpec q n)
    : ∀ {c : LowCT} {rs rs' : RustState},
      RustExec N leafSpec (nttPolyMul q n c) rs rs' →
      RustExec N leafSpec c rs rs' := by
  intro c
  induction c with
  | RSkip => intro rs rs' h; simpa [nttPolyMul] using h
  | RSeq c1 c2 ih1 ih2 =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      cases h with
      | seq _ _ _ r1 _ h1 h2 =>
          exact RustExec.seq c1 c2 rs r1 rs' (ih1 h1) (ih2 h2)
  | RLetZero x t body ih =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      cases h with
      | letZero _ _ _ _ _ hBody =>
          exact RustExec.letZero x t body rs rs' (ih hBody)
  | RLetU64Zero x body ih =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      cases h with
      | letU64Zero _ _ _ _ hBody =>
          exact RustExec.letU64Zero x body rs rs' (ih hBody)
  | RScalarSet x v => intro rs rs' h; simpa [nttPolyMul] using h
  | RCall f dst args =>
      intro rs rs' h
      by_cases hf : isPolyMulName f = true
      · have hEq : nttPolyMul q n (.RCall f dst args) =
            .RCall (nttPolyMulName q n) dst args := by simp [nttPolyMul, hf]
        rw [hEq] at h
        cases h with
        | call _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
            have hPostEq :
                leafSpec.call (nttPolyMulName q n) dst.locDst (args.map (·.locDst))
                    oldDestV argList =
                  leafSpec.call f dst.locDst (args.map (·.locDst))
                    oldDestV argList :=
              hAgree f dst.locDst (args.map (·.locDst)) oldDestV argList hf
            have hExec :
                RustExec N leafSpec (.RCall f dst args) rs
                  (locatedUpdate rs dst
                    (leafSpec.call f dst.locDst (args.map (·.locDst))
                      oldDestV argList)) :=
              RustExec.call f dst args rs oldDestV argList
                hLookup hArgList hArgs
            rw [hPostEq]; exact hExec
      · have hEq : nttPolyMul q n (.RCall f dst args) =
            .RCall f dst args := by simp [nttPolyMul, hf]
        rw [hEq] at h; exact h
  | RCallSwap f d1 d2 args =>
      intro rs rs' h
      by_cases hf : isPolyMulName f = true
      · have hEq : nttPolyMul q n (.RCallSwap f d1 d2 args) =
            .RCallSwap (nttPolyMulName q n) d1 d2 args := by simp [nttPolyMul, hf]
        rw [hEq] at h
        cases h with
        | callSwap _ _ _ _ _ rs1 _ h1 h2 =>
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
      · have hEq : nttPolyMul q n (.RCallSwap f d1 d2 args) =
            .RCallSwap f d1 d2 args := by simp [nttPolyMul, hf]
        rw [hEq] at h; exact h
  | RCloneCall cv ct od inner dest args =>
      intro rs rs' h
      by_cases hf : isPolyMulName inner = true
      · have hEq : nttPolyMul q n (.RCloneCall cv ct od inner dest args) =
            .RCloneCall cv ct od (nttPolyMulName q n) dest args := by
          simp [nttPolyMul, hf]
        rw [hEq] at h
        cases h with
        | cloneCall _ _ _ _ _ _ _ rsClone _ hrs hInner =>
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
      · have hEq : nttPolyMul q n (.RCloneCall cv ct od inner dest args) =
            .RCloneCall cv ct od inner dest args := by simp [nttPolyMul, hf]
        rw [hEq] at h; exact h
  | RIfNz cond ct cf ihT ihF =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      cases h with
      | ifTrue _ _ _ _ _ v hv hne hBody =>
          exact RustExec.ifTrue cond ct cf rs rs' v hv hne (ihT hBody)
      | ifFalse _ _ _ _ _ hv hBody =>
          exact RustExec.ifFalse cond ct cf rs rs' hv (ihF hBody)
  | RWhileNz cond body ih =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      have aux : ∀ c0 rs0 rs0',
          RustExec N leafSpec c0 rs0 rs0' →
          c0 = .RWhileNz cond (nttPolyMul q n body) →
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
        | callDstThreaded => intro hEq; cases hEq
      exact aux _ rs rs' h rfl
  | RFor x k body ih =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      exact rfor_spine_reverse (fun _ _ hb => ih hb) _ rs rs' h k rfl
  | RForRuntime x bnd body ih =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      cases h with
      | forRuntime _ _ _ _ _ hInner =>
          exact RustExec.forRuntime x bnd body rs rs'
            (rfor_spine_reverse (fun _ _ hb => ih hb) _ rs rs' hInner _ rfl)
  | RLimbStore loc idx v => intro rs rs' h; simpa [nttPolyMul] using h
  | RLimbStoreExpr loc idx e => intro rs rs' h; simpa [nttPolyMul] using h
  | RCallN f dests args => intro rs rs' h; simpa [nttPolyMul] using h
  | RSelect dst sel s0 s1 => intro rs rs' h; simpa [nttPolyMul] using h
  | RAssert label => intro rs rs' h; simpa [nttPolyMul] using h
  | RBlock body ih =>
      intro rs rs' h
      simp only [nttPolyMul] at h
      cases h with
      | block _ _ _ hBody => exact RustExec.block body rs rs' (ih hBody)
  | RFnDef _ _ _ _ _ _ _ =>
      intro _ _ h
      simp only [nttPolyMul] at h
      cases h
  | RFnCall f dests args => intro rs rs' h; simpa [nttPolyMul] using h
  | RTupleLoad dst src idx => intro rs rs' h; simpa [nttPolyMul] using h
  | RArrStore arr idxVar src => intro rs rs' h; simpa [nttPolyMul] using h
  | RArrLoad dst src idxVar => intro rs rs' h; simpa [nttPolyMul] using h
  | RScalarSetExpr x e => intro rs rs' h; simpa [nttPolyMul] using h
  | RArrStoreLit arr idx src => intro rs rs' h; simpa [nttPolyMul] using h
  | RArrLoadLit dst src idx => intro rs rs' h; simpa [nttPolyMul] using h
  | RCallDstThreaded f dst args =>
      intro rs rs' h
      by_cases hf : isPolyMulName f = true
      · have hEq : nttPolyMul q n (.RCallDstThreaded f dst args) =
            .RCallDstThreaded (nttPolyMulName q n) dst args := by
          simp [nttPolyMul, hf]
        rw [hEq] at h
        cases h with
        | callDstThreaded _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
            have hPostEq :
                leafSpec.call (nttPolyMulName q n) dst.locDst
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
      · have hEq : nttPolyMul q n (.RCallDstThreaded f dst args) =
            .RCallDstThreaded f dst args := by simp [nttPolyMul, hf]
        rw [hEq] at h; exact h

/-- The NTT poly-mul rewrite preserves the big-step semantics, modulo
    the per-leaf agreement assumption.  This is the **soundness anchor**
    for Pass 3.1 — combine with a concrete `LeafSpec` whose
    `nttAgreesPolyMul` is discharged via
    `CompPoly.NTT.fastMulImpl_eq_mul`. -/
theorem nttPolyMul_denote_eq
    (q n N : Nat) (leafSpec : LeafSpec)
    (hAgree : nttAgreesPolyMul leafSpec q n)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (nttPolyMul q n c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  ⟨nttPolyMul_denote_reverse hAgree, nttPolyMul_denote_forward hAgree⟩

/-! ## §5  ML-KEM / ML-DSA convenience specialisations -/

/-- ML-KEM parameters: `(q = 3329, n = 256)`. -/
@[inline] def nttPolyMulMlkem : LowCT → LowCT := nttPolyMul 3329 256

/-- ML-DSA parameters: `(q = 8380417, n = 256)`. -/
@[inline] def nttPolyMulMldsa : LowCT → LowCT := nttPolyMul 8380417 256

/-- ML-KEM specialisation of the denotational-equivalence theorem. -/
theorem nttPolyMulMlkem_denote_eq
    (N : Nat) (leafSpec : LeafSpec)
    (hAgree : nttAgreesPolyMul leafSpec 3329 256)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (nttPolyMulMlkem c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  nttPolyMul_denote_eq 3329 256 N leafSpec hAgree c rs rs'

/-- ML-DSA specialisation of the denotational-equivalence theorem. -/
theorem nttPolyMulMldsa_denote_eq
    (N : Nat) (leafSpec : LeafSpec)
    (hAgree : nttAgreesPolyMul leafSpec 8380417 256)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (nttPolyMulMldsa c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  nttPolyMul_denote_eq 8380417 256 N leafSpec hAgree c rs rs'

/-! ## Constant-time of the runtime-indexed NTT coefficient loop

The NTT operates on a coefficient array indexed by the (public) loop position.
A representative butterfly-style coefficient loop — `for i in 0..n {
tmp := coeffs[i]; coeffs[i] := tmp }` over a `TArr n (TU64)` polynomial — uses
the runtime-indexed array access this pass leaves in place (lines `RArrLoad`/
`RArrStore` above).  With a public index it is constant-time by construction
(`cmdCT`), and the access now flows through the CryptoSSA front-end without
unrolling.  The bit-level field correctness of the butterfly is the kernel
layer (`BarrettButterflyKernel`, `NttPolyVerified`); here we record the CT
guarantee of the access shape. -/

/-- The polynomial coefficient array (`n` u64 limbs). -/
def nttCoeffsLoc (n : Nat) : Located :=
  { locVar := "coeffs", locSrc := TowerType.TArr n TowerType.TU64 }

/-- A scratch coefficient. -/
def nttTmpLoc : Located := { locVar := "tmp", locSrc := TowerType.TU64 }

/-- A representative NTT coefficient loop: read/write `coeffs[i]` at the public
    loop counter `i`. -/
def nttCoeffLoop (n : Nat) : LowCT :=
  LowCT.RFor "i" n
    (LowCT.RSeq
      (LowCT.RArrLoad nttTmpLoc (nttCoeffsLoc n) "i")
      (LowCT.RArrStore (nttCoeffsLoc n) "i" nttTmpLoc))

/-- The NTT coefficient loop is constant-time by construction on a public
    index (the loop counter). -/
theorem nttCoeffLoop_isCT (n : Nat) (leafCT : LeafCTTable) :
    cmdCT (nttCoeffLoop n) (fun _ => SecretLevel.Public) leafCT = true := by
  simp only [nttCoeffLoop, nttCoeffsLoc, nttTmpLoc, cmdCT_RFor, cmdCT_RSeq,
    cmdCT_RArrLoad, cmdCT_RArrStore]
  decide

end CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
