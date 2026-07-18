/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# Pass 1.2 — Montgomery Reduction

Sibling to `BarrettReduce.lean`.  Rewrites `RCall "mul_mod_q"` (and the
ML-KEM convention `"mul_reduce"`) to `RCall s!"mont_mul_{q}_{R}"` when
both the modulus `q` and the Montgomery radix `R = 2^k` are
statically known.

Per the verified-compiler plan: Tier 1.2 (local arithmetic).  Estimated
speedup: 3-5× on lattice multiplication.

## Soundness

The pass's correctness reduces to per-leaf agreement: the `LeafSpec`'s
`s!"mont_mul_{q}_{R}"` leaf must produce semantically identical results
to the abstract `"mul_mod_q"`/`"mul_reduce"` leaf at every call site.
This is an external assumption on the `LeafSpec`
(`montAgreesMulModQ`); it is provable by `decide` for concrete `q`/`R`
once the `LeafSpec` is instantiated against a Jasmin/libcrux
implementation.

## Strategy

This pass uses **direct renaming** (analogue of Barrett's pattern):
each recognised `mul_mod_q` call site is renamed to the Montgomery leaf
`mont_mul_{q}_{R}`.  The Montgomery semantics — including any
to-Montgomery / from-Montgomery conversions — is absorbed into the
LeafSpec's implementation of `mont_mul_{q}_{R}`, mirroring the way
Barrett's `barrettName` leaf absorbs the Barrett-reduction
constant-time bit tricks.

This is the **compact** Strategy A from the verified-compiler plan: by
treating the multiplication-with-Montgomery-conversion as an atomic
leaf, the pass avoids the proof burden of fresh-name analysis at the
LowCT AST level while still exposing the Montgomery code path to the
backend code generator (which dispatches on the leaf name).

A follow-up **Strategy B** (per-variable Montgomery-form tracking, with
explicit `to_mont` / `from_mont` calls hoisted across chains of
multiplications) could amortise the conversion overhead.  That requires
a flow-sensitive analysis at the LowCT AST level and is left as a
separate pass.

## Composition

Pipeline composition: this pass is `pass_montgomery` in the optimizer
orchestrator (Tier 4.1).  Composes with `pass_barrett` via the per-pass
equivalence theorems.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.MontgomeryReduce

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Pattern recognition

A `LowCT` is a "mul-mod-q multiplication site" if it is
`RCall "mul_mod_q"` or `RCall "mul_reduce"` (ML-KEM's hand-written
fused multiply-reduce kernel).  Both have the same semantic intent
and share the same `dst`/`args` shape.
-/

/-- Predicate: the call name `f` is one of the recognised
    mul-mod-q multiplication-site names. -/
def isMulModQName (f : String) : Bool :=
  f == "mul_mod_q" || f == "mul_reduce"

@[simp] theorem isMulModQName_mul_mod_q : isMulModQName "mul_mod_q" = true := by
  decide

@[simp] theorem isMulModQName_mul_reduce : isMulModQName "mul_reduce" = true := by
  decide

/-! ## §2  Rewrite pass

`montgomeryReduce q R` walks the LowCT AST and replaces every
recognised mul-mod-q multiplication call with `s!"mont_mul_{q}_{R}"`.
All other constructors are traversed compositionally; constructors
with no nested `LowCT` (scalar set, limb store, asm op, …) are
identity.
-/

/-- The name of the Montgomery multiplication leaf for given modulus
    `q` and radix `R`. -/
@[inline] def montMulName (q R : Nat) : String := s!"mont_mul_{q}_{R}"

/-- The Montgomery-reduction rewrite pass parameterised by the modulus
    `q` and radix `R = 2^k`.  Replaces `RCall "mul_mod_q"`/
    `RCall "mul_reduce"` with `RCall (montMulName q R)`; recurses
    through every constructor with a nested `LowCT` body.
    Constructors without nested commands act as identity. -/
def montgomeryReduce (q R : Nat) : LowCT → LowCT
  | .RSkip => .RSkip
  | .RSeq c1 c2 => .RSeq (montgomeryReduce q R c1) (montgomeryReduce q R c2)
  | .RLetZero x t body => .RLetZero x t (montgomeryReduce q R body)
  | .RLetU64Zero x body => .RLetU64Zero x (montgomeryReduce q R body)
  | .RScalarSet x v => .RScalarSet x v
  | .RCall f dst args =>
      if isMulModQName f then .RCall (montMulName q R) dst args
      else .RCall f dst args
  | .RCallSwap f d1 d2 args =>
      if isMulModQName f then .RCallSwap (montMulName q R) d1 d2 args
      else .RCallSwap f d1 d2 args
  | .RCloneCall cv ct od inner dest args =>
      if isMulModQName inner then .RCloneCall cv ct od (montMulName q R) dest args
      else .RCloneCall cv ct od inner dest args
  | .RIfNz cond ct cf => .RIfNz cond (montgomeryReduce q R ct) (montgomeryReduce q R cf)
  | .RWhileNz cond body => .RWhileNz cond (montgomeryReduce q R body)
  | .RFor x n body => .RFor x n (montgomeryReduce q R body)
  | .RForRuntime x b body => .RForRuntime x b (montgomeryReduce q R body)
  | .RLimbStore loc idx v => .RLimbStore loc idx v
  | .RLimbStoreExpr loc idx e => .RLimbStoreExpr loc idx e
  | .RAsmOp name dests args => .RAsmOp name dests args
  | .RCallN f dests args => .RCallN f dests args
  | .RSelect dst sel s0 s1 => .RSelect dst sel s0 s1
  | .RAssert label => .RAssert label
  | .RBlock body => .RBlock (montgomeryReduce q R body)
  | .RFnDef name params returns body cont =>
      .RFnDef name params returns (montgomeryReduce q R body) (montgomeryReduce q R cont)
  | .RFnCall f dests args => .RFnCall f dests args
  | .RTupleStore dst idx src => .RTupleStore dst idx src
  | .RTupleLoad dst src idx => .RTupleLoad dst src idx
  | .RArrStore arr idxVar src => .RArrStore arr idxVar src
  | .RArrLoad dst src idxVar => .RArrLoad dst src idxVar
  | .RScalarSetExpr x e => .RScalarSetExpr x e
  | .RBytesSlice dst src start len => .RBytesSlice dst src start len
  | .RArrStoreLit arr idx src => .RArrStoreLit arr idx src
  | .RArrLoadLit dst src idx => .RArrLoadLit dst src idx
  | .RCallDstThreaded f dst args =>
      if isMulModQName f then .RCallDstThreaded (montMulName q R) dst args
      else .RCallDstThreaded f dst args

/-! ## §3  Per-leaf agreement assumption

The pass's soundness requires that the `LeafSpec`'s
`mont_mul_{q}_{R}` leaf agrees with the abstract
`"mul_mod_q"`/`"mul_reduce"` leaf on every invocation.  We encode
this as a `Prop`-level predicate on the `LeafSpec`, parameterised by
`q` and `R`.

For concrete `LeafSpec` instances and concrete `q`/`R`, this is
closable by `decide` (since the leaf-call functions are pure and the
relevant input domain is finite once `dt` is fixed).  At the level of
this file we leave it as an externally-supplied hypothesis.

The agreement is mathematically valid because `mont_mul(a', b')` on
Montgomery-domain inputs `a' = a·R mod q`, `b' = b·R mod q` produces
`a'·b'·R⁻¹ mod q = a·b·R mod q`, which after a `from_mont` (built
into the leaf when needed) equals `a·b mod q` — the abstract
`mul_mod_q` result. -/

/-- Per-leaf agreement predicate: the `LeafSpec`'s Montgomery
    multiplication leaf agrees with the abstract `"mul_mod_q"` and
    `"mul_reduce"` leaves on all inputs.  This is the soundness
    obligation for the Montgomery pass. -/
def montAgreesMulModQ (leafSpec : LeafSpec) (q R : Nat) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType)
    (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
    isMulModQName f = true →
    leafSpec.call (montMulName q R) dt argTs oldV args =
      leafSpec.call f dt argTs oldV args

/-! ## §4  Correctness theorem

The pass preserves the big-step semantics: `montgomeryReduce q R c`
produces the same final state as `c` for any starting state `rs`,
provided the agreement hypothesis holds.

Both directions are proved by induction on the `RustExec` derivation.
The interesting case is `call`, where the agreement hypothesis lets us
rewrite the post-state from `leafSpec.call f …` to
`leafSpec.call (montMulName q R) …` (and back).  All other constructors
either have no `LowCT` subterms (identity-traversed by
`montgomeryReduce`) or recursive subterms (handled by the inductive
hypothesis).
-/

/-- Forward direction: any `RustExec` derivation lifts through the
    Montgomery rewrite. -/
theorem montgomeryReduce_denote_forward
    {q R : Nat} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : montAgreesMulModQ leafSpec q R)
    {c : LowCT} {rs rs' : RustState}
    (h : RustExec N leafSpec c rs rs') :
    RustExec N leafSpec (montgomeryReduce q R c) rs rs' := by
  induction h with
  | skip rs => simpa [montgomeryReduce] using RustExec.skip rs
  | seq c1 c2 rs r1 rs' _ _ ih1 ih2 =>
      simpa [montgomeryReduce] using
        RustExec.seq (montgomeryReduce q R c1) (montgomeryReduce q R c2) rs r1 rs' ih1 ih2
  | letZero x t body rs rs' _ ih =>
      simpa [montgomeryReduce] using RustExec.letZero x t _ rs rs' ih
  | letU64Zero x body rs rs' _ ih =>
      simpa [montgomeryReduce] using RustExec.letU64Zero x _ rs rs' ih
  | scalarSet x v rs =>
      simpa [montgomeryReduce] using RustExec.scalarSet (N := N) (leafSpec := leafSpec) x v rs
  | ifTrue e ct cf rs rs' v hv hne _ ih =>
      simpa [montgomeryReduce] using RustExec.ifTrue e _ _ rs rs' v hv hne ih
  | ifFalse e ct cf rs rs' hv _ ih =>
      simpa [montgomeryReduce] using RustExec.ifFalse e _ _ rs rs' hv ih
  | whileFalse e body rs hv =>
      simpa [montgomeryReduce] using RustExec.whileFalse (N := N) (leafSpec := leafSpec)
        e _ rs hv
  | whileTrue e body rs r1 rs' v hv hne _ _ ih1 ih2 =>
      have h1 : RustExec N leafSpec (montgomeryReduce q R body) rs r1 := ih1
      have h2 : RustExec N leafSpec (.RWhileNz e (montgomeryReduce q R body)) r1 rs' := by
        simpa [montgomeryReduce] using ih2
      simpa [montgomeryReduce] using
        RustExec.whileTrue e (montgomeryReduce q R body) rs r1 rs' v hv hne h1 h2
  | forZero x body rs =>
      simpa [montgomeryReduce] using RustExec.forZero (N := N) (leafSpec := leafSpec)
        x _ rs
  | forSucc x n body rs r1 rs' _ _ ih1 ih2 =>
      have h1 : RustExec N leafSpec (.RFor x n (montgomeryReduce q R body)) rs r1 := by
        simpa [montgomeryReduce] using ih1
      have h2 : RustExec N leafSpec (montgomeryReduce q R body)
          (rsSetScalar r1 x n) rs' := ih2
      simpa [montgomeryReduce] using
        RustExec.forSucc x n (montgomeryReduce q R body) rs r1 rs' h1 h2
  | forRuntime x bound body rs rs' _ ih =>
      have h1 : RustExec N leafSpec
          (.RFor x (bound.evalState rs) (montgomeryReduce q R body)) rs rs' := by
        simpa [montgomeryReduce] using ih
      simpa [montgomeryReduce] using
        RustExec.forRuntime x bound (montgomeryReduce q R body) rs rs' h1
  | call f dest args rs oldDestV argList hLookup hArgList hArgs =>
      by_cases hf : isMulModQName f = true
      · have hPostEq :
            leafSpec.call (montMulName q R) dest.locDst (args.map (·.locDst))
                oldDestV argList =
              leafSpec.call f dest.locDst (args.map (·.locDst))
                oldDestV argList := by
          exact hAgree f dest.locDst (args.map (·.locDst)) oldDestV argList hf
        have hExecM :
            RustExec N leafSpec (.RCall (montMulName q R) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call (montMulName q R) dest.locDst
                  (args.map (·.locDst)) oldDestV argList)) :=
          RustExec.call (montMulName q R) dest args rs oldDestV argList
            hLookup hArgList hArgs
        have hExecM' :
            RustExec N leafSpec (.RCall (montMulName q R) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call f dest.locDst
                  (args.map (·.locDst)) oldDestV argList)) := by
          rw [← hPostEq]; exact hExecM
        have hUnfold :
            montgomeryReduce q R (.RCall f dest args) =
              .RCall (montMulName q R) dest args := by
          simp [montgomeryReduce, hf]
        rw [hUnfold]
        exact hExecM'
      · have hUnfold :
            montgomeryReduce q R (.RCall f dest args) = .RCall f dest args := by
          simp [montgomeryReduce, hf]
        rw [hUnfold]
        exact RustExec.call f dest args rs oldDestV argList hLookup hArgList hArgs
  | cloneCall cv ct od inner dest args rs rsClone rs' hrs _ ihInner =>
      by_cases hf : isMulModQName inner = true
      · have hInner' :
            RustExec N leafSpec (.RCall (montMulName q R) dest args) rsClone rs' := by
          have := ihInner
          simp [montgomeryReduce, hf] at this
          exact this
        have hUnfold :
            montgomeryReduce q R (.RCloneCall cv ct od inner dest args) =
              .RCloneCall cv ct od (montMulName q R) dest args := by
          simp [montgomeryReduce, hf]
        rw [hUnfold]
        exact RustExec.cloneCall cv ct od (montMulName q R) dest args
                rs rsClone rs' hrs hInner'
      · have hInner' :
            RustExec N leafSpec (.RCall inner dest args) rsClone rs' := by
          have := ihInner
          simp [montgomeryReduce, hf] at this
          exact this
        have hUnfold :
            montgomeryReduce q R (.RCloneCall cv ct od inner dest args) =
              .RCloneCall cv ct od inner dest args := by
          simp [montgomeryReduce, hf]
        rw [hUnfold]
        exact RustExec.cloneCall cv ct od inner dest args
                rs rsClone rs' hrs hInner'
  | callSwap f dest1 dest2 args rs rs1 rs' _ _ ih1 ih2 =>
      by_cases hf : isMulModQName f = true
      · have h1' : RustExec N leafSpec
            (.RCall (montMulName q R) dest1 args) rs rs1 := by
          have := ih1; simp [montgomeryReduce, hf] at this; exact this
        have h2' : RustExec N leafSpec
            (.RCall (montMulName q R) dest2 args) rs1 rs' := by
          have := ih2; simp [montgomeryReduce, hf] at this; exact this
        have hUnfold :
            montgomeryReduce q R (.RCallSwap f dest1 dest2 args) =
              .RCallSwap (montMulName q R) dest1 dest2 args := by
          simp [montgomeryReduce, hf]
        rw [hUnfold]
        exact RustExec.callSwap (montMulName q R) dest1 dest2 args rs rs1 rs' h1' h2'
      · have h1' : RustExec N leafSpec (.RCall f dest1 args) rs rs1 := by
          have := ih1; simp [montgomeryReduce, hf] at this; exact this
        have h2' : RustExec N leafSpec (.RCall f dest2 args) rs1 rs' := by
          have := ih2; simp [montgomeryReduce, hf] at this; exact this
        have hUnfold :
            montgomeryReduce q R (.RCallSwap f dest1 dest2 args) =
              .RCallSwap f dest1 dest2 args := by
          simp [montgomeryReduce, hf]
        rw [hUnfold]
        exact RustExec.callSwap f dest1 dest2 args rs rs1 rs' h1' h2'
  | limbStore loc idx v rs oldDestV hLookup =>
      simpa [montgomeryReduce] using
        RustExec.limbStore loc idx v rs oldDestV hLookup
  | limbStoreExpr loc idx e rs oldDestV hLookup =>
      simpa [montgomeryReduce] using
        RustExec.limbStoreExpr loc idx e rs oldDestV hLookup
  | asmOp name dests args rs =>
      simpa [montgomeryReduce] using
        RustExec.asmOp (N := N) (leafSpec := leafSpec) name dests args rs
  | callN f dests args rs =>
      simpa [montgomeryReduce] using
        RustExec.callN (N := N) (leafSpec := leafSpec) f dests args rs
  | selectFalse dst sel src0 src1 rs h srcV hsel hLookup =>
      simpa [montgomeryReduce] using
        RustExec.selectFalse (N := N) (leafSpec := leafSpec)
          dst sel src0 src1 rs h srcV hsel hLookup
  | selectTrue dst sel src0 src1 rs h v srcV hsel hne hLookup =>
      simpa [montgomeryReduce] using
        RustExec.selectTrue (N := N) (leafSpec := leafSpec)
          dst sel src0 src1 rs h v srcV hsel hne hLookup
  | assert label rs =>
      simpa [montgomeryReduce] using
        RustExec.assert (N := N) (leafSpec := leafSpec) label rs
  | block body rs rs' _ ih =>
      simpa [montgomeryReduce] using RustExec.block _ rs rs' ih
  | fnDef name params returns body cont rs rs' _ ih =>
      simpa [montgomeryReduce] using
        RustExec.fnDef name params returns (montgomeryReduce q R body) _ rs rs' ih
  | fnCall f dests args rs =>
      simpa [montgomeryReduce] using
        RustExec.fnCall (N := N) (leafSpec := leafSpec) f dests args rs
  | tupleStore dst idx src rs oldV srcV hDst hSrc =>
      simpa [montgomeryReduce] using
        RustExec.tupleStore dst idx src rs oldV srcV hDst hSrc
  | tupleLoad dst src idx rs oldV srcV hDst hSrc =>
      simpa [montgomeryReduce] using
        RustExec.tupleLoad dst src idx rs oldV srcV hDst hSrc
  | arrStore arr idxVar src rs idx oldV srcV hIdx hArr hSrc =>
      simpa [montgomeryReduce] using
        RustExec.arrStore arr idxVar src rs idx oldV srcV hIdx hArr hSrc
  | arrLoad dst src idxVar rs idx oldV srcV hIdx hDst hSrc =>
      simpa [montgomeryReduce] using
        RustExec.arrLoad dst src idxVar rs idx oldV srcV hIdx hDst hSrc
  | scalarSetExpr x e rs =>
      simpa [montgomeryReduce] using
        RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) x e rs
  | bytesSlice dst src start len rs oldV srcV hDst hSrc =>
      simpa [montgomeryReduce] using
        RustExec.bytesSlice dst src start len rs oldV srcV hDst hSrc
  | arrStoreLit arr idx src rs oldV srcV hArr hSrc =>
      simpa [montgomeryReduce] using
        RustExec.arrStoreLit arr idx src rs oldV srcV hArr hSrc
  | arrLoadLit dst src idx rs oldV srcV hDst hSrc =>
      simpa [montgomeryReduce] using
        RustExec.arrLoadLit dst src idx rs oldV srcV hDst hSrc
  | callDstThreaded f dest args rs oldDestV argList hLookup hArgList hArgs =>
      by_cases hf : isMulModQName f = true
      · have hPostEq :
            leafSpec.call (montMulName q R) dest.locDst
                ((dest :: args).map (·.locDst)) oldDestV argList =
              leafSpec.call f dest.locDst ((dest :: args).map (·.locDst))
                oldDestV argList :=
          hAgree f dest.locDst ((dest :: args).map (·.locDst)) oldDestV argList hf
        have hExecB :
            RustExec N leafSpec (.RCallDstThreaded (montMulName q R) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call (montMulName q R) dest.locDst
                  ((dest :: args).map (·.locDst)) oldDestV argList)) :=
          RustExec.callDstThreaded (montMulName q R) dest args rs oldDestV argList
            hLookup hArgList hArgs
        have hExecB' :
            RustExec N leafSpec (.RCallDstThreaded (montMulName q R) dest args) rs
              (locatedUpdate rs dest
                (leafSpec.call f dest.locDst
                  ((dest :: args).map (·.locDst)) oldDestV argList)) := by
          rw [← hPostEq]; exact hExecB
        have hUnfold :
            montgomeryReduce q R (.RCallDstThreaded f dest args) =
              .RCallDstThreaded (montMulName q R) dest args := by
          simp [montgomeryReduce, hf]
        rw [hUnfold]
        exact hExecB'
      · have hUnfold :
            montgomeryReduce q R (.RCallDstThreaded f dest args) =
              .RCallDstThreaded f dest args := by
          simp [montgomeryReduce, hf]
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

/-- Reverse direction: any `RustExec` of the rewritten command lifts
    to one on the source command. -/
theorem montgomeryReduce_denote_reverse
    {q R : Nat} {N : Nat} {leafSpec : LeafSpec}
    (hAgree : montAgreesMulModQ leafSpec q R)
    : ∀ {c : LowCT} {rs rs' : RustState},
      RustExec N leafSpec (montgomeryReduce q R c) rs rs' →
      RustExec N leafSpec c rs rs' := by
  intro c
  induction c with
  | RSkip => intro rs rs' h; simpa [montgomeryReduce] using h
  | RSeq c1 c2 ih1 ih2 =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      cases h with
      | seq _ _ _ r1 _ h1 h2 =>
          exact RustExec.seq c1 c2 rs r1 rs' (ih1 h1) (ih2 h2)
  | RLetZero x t body ih =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      cases h with
      | letZero _ _ _ _ _ hBody =>
          exact RustExec.letZero x t body rs rs' (ih hBody)
  | RLetU64Zero x body ih =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      cases h with
      | letU64Zero _ _ _ _ hBody =>
          exact RustExec.letU64Zero x body rs rs' (ih hBody)
  | RScalarSet x v => intro rs rs' h; simpa [montgomeryReduce] using h
  | RCall f dst args =>
      intro rs rs' h
      by_cases hf : isMulModQName f = true
      · have hEq : montgomeryReduce q R (.RCall f dst args) =
            .RCall (montMulName q R) dst args := by simp [montgomeryReduce, hf]
        rw [hEq] at h
        cases h with
        | call _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
            have hPostEq :
                leafSpec.call (montMulName q R) dst.locDst (args.map (·.locDst))
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
      · have hEq : montgomeryReduce q R (.RCall f dst args) =
            .RCall f dst args := by simp [montgomeryReduce, hf]
        rw [hEq] at h; exact h
  | RCallSwap f d1 d2 args =>
      intro rs rs' h
      by_cases hf : isMulModQName f = true
      · have hEq : montgomeryReduce q R (.RCallSwap f d1 d2 args) =
            .RCallSwap (montMulName q R) d1 d2 args := by simp [montgomeryReduce, hf]
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
      · have hEq : montgomeryReduce q R (.RCallSwap f d1 d2 args) =
            .RCallSwap f d1 d2 args := by simp [montgomeryReduce, hf]
        rw [hEq] at h; exact h
  | RCloneCall cv ct od inner dest args =>
      intro rs rs' h
      by_cases hf : isMulModQName inner = true
      · have hEq : montgomeryReduce q R (.RCloneCall cv ct od inner dest args) =
            .RCloneCall cv ct od (montMulName q R) dest args := by
          simp [montgomeryReduce, hf]
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
      · have hEq : montgomeryReduce q R (.RCloneCall cv ct od inner dest args) =
            .RCloneCall cv ct od inner dest args := by simp [montgomeryReduce, hf]
        rw [hEq] at h; exact h
  | RIfNz cond ct cf ihT ihF =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      cases h with
      | ifTrue _ _ _ _ _ v hv hne hBody =>
          exact RustExec.ifTrue cond ct cf rs rs' v hv hne (ihT hBody)
      | ifFalse _ _ _ _ _ hv hBody =>
          exact RustExec.ifFalse cond ct cf rs rs' hv (ihF hBody)
  | RWhileNz cond body ih =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      have aux : ∀ c0 rs0 rs0',
          RustExec N leafSpec c0 rs0 rs0' →
          c0 = .RWhileNz cond (montgomeryReduce q R body) →
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
        | _ => intro hEq; cases hEq
      exact aux _ rs rs' h rfl
  | RFor x n body ih =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      -- Strengthen the auxiliary so that the loop count `n0` is
      -- universally quantified *inside* the induction motive (not
      -- introduced before), so the recursive `forSucc` IH can be
      -- specialised to the shorter count `k`.
      have aux : ∀ (c0 : LowCT) (rs0 rs0' : RustState),
          RustExec N leafSpec c0 rs0 rs0' →
          ∀ (n0 : Nat), c0 = .RFor x n0 (montgomeryReduce q R body) →
          RustExec N leafSpec (.RFor x n0 body) rs0 rs0' := by
        intro c0 rs0 rs0' h0
        induction h0 with
        | forZero x' b rs =>
            intro n0 hEq; cases hEq; exact RustExec.forZero x body rs
        | forSucc x' k b rs r1 rs' hInner hBody ihInner _ =>
            intro n0 hEq
            cases hEq
            -- Outer match forces `n0 = k+1`, `x' = x`, `b = montgomeryReduce q R body`.
            -- Inner IH `ihInner` is applied at count `k`.
            exact RustExec.forSucc x k body rs r1 rs'
              (ihInner k rfl) (ih hBody)
        | _ => intro n0 hEq; cases hEq
      exact aux _ rs rs' h n rfl
  | RForRuntime x bnd body ih =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      cases h with
      | forRuntime _ _ _ _ _ hInner =>
          have aux : ∀ (c0 : LowCT) (rs0 rs0' : RustState),
              RustExec N leafSpec c0 rs0 rs0' →
              ∀ (n0 : Nat), c0 = .RFor x n0 (montgomeryReduce q R body) →
              RustExec N leafSpec (.RFor x n0 body) rs0 rs0' := by
            intro c0 rs0 rs0' h0
            induction h0 with
            | forZero x' b rs => intro n0 hEq; cases hEq; exact RustExec.forZero x body rs
            | forSucc x' k b rs r1 rs' hInner2 hBody ihInner _ =>
                intro n0 hEq; cases hEq
                exact RustExec.forSucc x k body rs r1 rs' (ihInner k rfl) (ih hBody)
            | _ => intro n0 hEq; cases hEq
          exact RustExec.forRuntime x bnd body rs rs' (aux _ rs rs' hInner _ rfl)
  | RLimbStore loc idx v => intro rs rs' h; simpa [montgomeryReduce] using h
  | RLimbStoreExpr loc idx e => intro rs rs' h; simpa [montgomeryReduce] using h
  | RAsmOp name dests args => intro rs rs' h; simpa [montgomeryReduce] using h
  | RCallN f dests args => intro rs rs' h; simpa [montgomeryReduce] using h
  | RSelect dst sel s0 s1 => intro rs rs' h; simpa [montgomeryReduce] using h
  | RAssert label => intro rs rs' h; simpa [montgomeryReduce] using h
  | RBlock body ih =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      cases h with
      | block _ _ _ hBody => exact RustExec.block body rs rs' (ih hBody)
  | RFnDef name params returns body cont ihBody ihCont =>
      intro rs rs' h
      simp only [montgomeryReduce] at h
      cases h with
      | fnDef _ _ _ _ _ _ _ hCont =>
          exact RustExec.fnDef name params returns body cont rs rs' (ihCont hCont)
  | RFnCall f dests args => intro rs rs' h; simpa [montgomeryReduce] using h
  | RTupleStore dst idx src => intro rs rs' h; simpa [montgomeryReduce] using h
  | RTupleLoad dst src idx => intro rs rs' h; simpa [montgomeryReduce] using h
  | RArrStore arr idxVar src => intro rs rs' h; simpa [montgomeryReduce] using h
  | RArrLoad dst src idxVar => intro rs rs' h; simpa [montgomeryReduce] using h
  | RScalarSetExpr x e => intro rs rs' h; simpa [montgomeryReduce] using h
  | RBytesSlice dst src start len => intro rs rs' h; simpa [montgomeryReduce] using h
  | RArrStoreLit arr idx src => intro rs rs' h; simpa [montgomeryReduce] using h
  | RArrLoadLit dst src idx => intro rs rs' h; simpa [montgomeryReduce] using h
  | RCallDstThreaded f dst args =>
      intro rs rs' h
      by_cases hf : isMulModQName f = true
      · have hEq : montgomeryReduce q R (.RCallDstThreaded f dst args) =
            .RCallDstThreaded (montMulName q R) dst args := by
          simp [montgomeryReduce, hf]
        rw [hEq] at h
        cases h with
        | callDstThreaded _ _ _ _ oldDestV argList hLookup hArgList hArgs =>
            have hPostEq :
                leafSpec.call (montMulName q R) dst.locDst
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
      · have hEq : montgomeryReduce q R (.RCallDstThreaded f dst args) =
            .RCallDstThreaded f dst args := by simp [montgomeryReduce, hf]
        rw [hEq] at h; exact h

/-- The Montgomery rewrite preserves the big-step semantics, modulo
    the per-leaf agreement assumption.  This is the **soundness anchor**
    for Pass 1.2 — combine with a concrete `LeafSpec` whose
    `montAgreesMulModQ` is closable by `decide`. -/
theorem montgomeryReduce_denote_eq
    (q R : Nat) (N : Nat) (leafSpec : LeafSpec)
    (hAgree : montAgreesMulModQ leafSpec q R)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (montgomeryReduce q R c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  ⟨montgomeryReduce_denote_reverse hAgree, montgomeryReduce_denote_forward hAgree⟩

/-! ## §5  ML-KEM specialisation

ML-KEM operates over the polynomial ring `Z_q[X] / (X^256 + 1)` with
`q = 3329` and uses Montgomery arithmetic with radix `R = 2^16 = 65536`
(matching the `i16` limb width chosen by the reference and formosa
implementations).
-/

/-- ML-KEM modulus. -/
abbrev mlkem_q : Nat := 3329

/-- ML-KEM Montgomery radix: `2^16` matching the `i16` representation
    used by both the reference C implementation and the formosa-MLKEM
    Jasmin port. -/
abbrev mlkem_R : Nat := 65536

/-- Montgomery rewrite pre-specialised for ML-KEM. -/
abbrev montgomeryReduceMlkem : LowCT → LowCT :=
  montgomeryReduce mlkem_q mlkem_R

/-- ML-KEM specialisation of `montgomeryReduce_denote_eq`. -/
theorem montgomeryReduceMlkem_denote_eq
    (N : Nat) (leafSpec : LeafSpec)
    (hAgree : montAgreesMulModQ leafSpec mlkem_q mlkem_R)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (montgomeryReduceMlkem c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  montgomeryReduce_denote_eq mlkem_q mlkem_R N leafSpec hAgree c rs rs'

end CatCrypt.Crypto.Optimizer.MontgomeryReduce
