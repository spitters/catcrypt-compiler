/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole
public import CatCrypt.Crypto.SecureCompilation.Ascent.EgraphBlockEquality
public import CatCrypt.Crypto.Optimizer.Rewrite.ComGVN

/-!
# `Com jasminDialect` rewrite pipeline: peephole then equality-saturation

The two verified algebraic `Com → Com` passes over the typed VIR
`jasminDialect` —

* the bounded equality-saturation engine `Egraph.saturateCom` (algebraic
  identity/annihilator collapses under a known-constant environment), and
* the local syntactic peephole `Peephole.peepCom` (`sub a a ↦ xor a a`
  zeroing idiom, `and a a ↦ or a a` idempotent canonicalisation) —

are composed here into the canonical `Com`-level optimisation sequence.

## Ordering

The pipeline runs **peephole first, then equality-saturation**:

1. `peepCom` canonicalises the local two-address / zeroing idioms (it is
   purely syntactic — no constant analysis), exposing more `or a a` /
   `and a a` idempotent shapes;
2. `saturateCom` then fires the algebraic identity/annihilator rules
   (`x + 0 ↦ x`, `x * 0 ↦ 0`, `x * 1 ↦ x`, …) under the known-constant
   environment, to a fuel-bounded fixed point.

This is the *algebraic-canonicalisation* stage of the dual-IR optimiser.
The complementary *instruction-scheduling* stage runs one IR down, on the
`LowCT` block representation (`Optimizer.Pipeline.scheduleThenPipeline`,
which wires in the ILP list scheduler): the VIR `Com jasminDialect`
is canonicalised here, and the lowered `LowCT` block is scheduled there.

## What is proved

* `comAlgebraicPipeline_denote` — end-to-end denotation preservation of
  the composed (peephole then saturate) `Com → Com` transform, under a
  known-constant environment consistent with the valuation.  Chains
  `Peephole.peepCom_denote` with `Egraph.saturateCom_denote`.  **Not**
  `rfl` — the peephole and the saturation engine rewrite the
  `Com` term.
* `comAlgebraicPipeline_ctSafe` — end-to-end constant-time preservation.
  `jasminDialect` is branch-free, so the composed transform produces only
  straight-line ops; `ctSafeComJ` is preserved.
* `comAlgebraicPipeline_cost_le` — the composed transform is
  cost-non-increasing (the "extraction is no worse than the input" half of
  the equality-saturation contract, composed with the peephole's own
  cost-non-increase).
* `optCom`, `optCom_denote` — the composed transform under `KEnv.unknown`, followed by
  global value numbering (`ComGVN.gvnCom`), a `Com → Com` stage whose denotation
  equality holds at every valuation; `optCom_ctSafe`, `optCom_cost_le` carry the CT
  predicate and the cost bound through both parts.
* `comAlgebraicPipeline_ctLeak`, `optCom_constantTime` — under a leakage model whose
  `regArith` operations are quiet, the composed transform keeps the leakage of a program
  at every valuation, and the stage keeps constant time for every relation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## §1  The composed algebraic-canonicalisation transform

Peephole first (syntactic local cleanups), then the fuel-bounded
equality-saturation engine (algebraic identity/annihilator collapses). -/

/-- The composed `Com → Com` algebraic-canonicalisation transform:
    peephole, then `fuel`-bounded equality saturation under the
    known-constant environment `k`. -/
def comAlgebraicPipeline {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    Com jasminDialect Γ t :=
  saturateCom fuel (peepCom c) k

/-! ## §2  End-to-end denotation preservation -/

/-- **Composed denotation preservation.**  Running the peephole then the
    equality-saturation engine preserves the denotation of the `Com`, for
    any known-constant environment `k` consistent with the valuation `V`.
    Chains `peepCom_denote` with `saturateCom_denote`.  This is exactly
    `Peephole.peep_then_saturate_denote`, re-exported as the headline
    pipeline theorem. -/
theorem comAlgebraicPipeline_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (comAlgebraicPipeline fuel c k).denote V = c.denote V := by
  unfold comAlgebraicPipeline
  rw [saturateCom_denote fuel (peepCom c) k V hk, peepCom_denote c V]

/-! ## §3  End-to-end constant-time preservation -/

/-- **Composed CT preservation.**  `jasminDialect` is branch-free, so both
    passes produce only straight-line ops; the composed transform
    preserves the structural CT predicate `ctSafeComJ`.  This is exactly
    `Peephole.peep_then_saturate_ctSafe`, re-exported as the headline
    pipeline theorem. -/
theorem comAlgebraicPipeline_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    ctSafeComJ (comAlgebraicPipeline fuel c k) = ctSafeComJ c := by
  unfold comAlgebraicPipeline
  rw [saturateCom_ctSafe fuel (peepCom c) k, peepCom_ctSafe c]

/-! ## §4  Cost non-increase -/

/-- **The composed transform is cost-non-increasing.**  The peephole is
    cost-non-increasing (`peepCom_cost_le`) and so is the saturation engine
    (`saturate_cost_le`); transitivity gives the composed bound. -/
theorem comAlgebraicPipeline_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    comCost (comAlgebraicPipeline fuel c k) ≤ comCost c := by
  unfold comAlgebraicPipeline
  exact Nat.le_trans (saturate_cost_le fuel (peepCom c) k) (peepCom_cost_le c)

/-! ## §5  The unconditional stage

With the environment `KEnv.unknown`, which claims no constant for any input, the
composed transform needs no hypothesis on the valuation: the constants it uses are
those the program binds itself with `regConst`, which `extendK` records as the
engine descends. One saturation pass reaches the fixed point of the rule set
(`saturateCom`), so the fuel is `1`. Global value numbering (`ComGVN.gvnCom`) runs last,
so it also merges the bindings the rewrites make equal. -/

/-- **The `Com` optimisation stage**: the peephole, then one pass of the saturation
    engine under `KEnv.unknown`, then global value numbering. -/
def optCom {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  ComGVN.gvnCom
    (comAlgebraicPipeline 1 c (CatCrypt.Crypto.SecureCompilation.Ascent.KEnv.unknown Γ))

/-- **Denotation of the stage.** `optCom c` denotes the same function as `c`, at every
    valuation. -/
theorem optCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : (optCom c).denote = c.denote := by
  rw [optCom, ComGVN.gvnCom_denote]
  exact funext fun V => comAlgebraicPipeline_denote 1 c _ V
    (CatCrypt.Crypto.SecureCompilation.Ascent.KEnv.unknown_consistent V)

/-- The stage preserves the structural CT predicate `ctSafeComJ`. -/
theorem optCom_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : ctSafeComJ (optCom c) = ctSafeComJ c := by
  rw [optCom, ComGVN.gvnCom_ctSafe]
  exact comAlgebraicPipeline_ctSafe 1 c _

/-- The stage does not increase `comCost`. -/
theorem optCom_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : comCost (optCom c) ≤ comCost c :=
  Nat.le_trans (ComGVN.gvnCom_cost_le _) (comAlgebraicPipeline_cost_le 1 c _)

/-! ## §5a  Leakage of the stage

The peephole and the saturation engine replace a binary `regArith` binding by another binary
`regArith` binding over the same width and leave every other binding unchanged. Under a
leakage model whose `regArith` operations emit no event, both passes keep the leakage of a
program at every valuation. Without that hypothesis the statement fails: a model for which
`add` is quiet and `or` is not distinguishes `x + 0` from its rewrite `x ||| x`. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)

/-- An expression whose operation is a `regArith` emits no event under a leakage model whose
    `regArith` operations are quiet. -/
theorem expr_ctLeak_regArith (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) {bop : JasminBinOp} {w : Nat}
    (h : e.op = .regArith bop w) (V : Ctxt.Valuation Γ) : Expr.ctLeak L e V = [] := by
  unfold Expr.ctLeak opLeak
  split <;> rename_i heq <;> rw [h, hq] at heq <;> first | rfl | cases heq

/-- A result of `binE` is a `regArith` expression. -/
theorem binE_op {Γ : Ctxt jasminDialect} {w : Nat} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg w)) : (binE op a b).op = .regArith op w := rfl

/-- Leakage of one rewritten expression of the saturation engine. -/
theorem rewriteExpr_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ) :
    Expr.ctLeak L (rewriteExpr e k) V = Expr.ctLeak L e V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [rewriteExpr, HVector.head, HVector.tail]
      rw [expr_ctLeak_regArith L hq ⟨.regArith bop w, rfl, .cons a (.cons b .nil)⟩ rfl V]
      rcases hr : rewriteBin bop a b (KEnv.lookup b k) with _ | e'
      · exact expr_ctLeak_regArith L hq _ rfl V
      · have hop' : ∃ bop', e'.op = .regArith bop' w := by
          unfold rewriteBin at hr
          split at hr <;> first | (cases hr; exact ⟨_, binE_op _ _ _⟩) | cases hr
        obtain ⟨bop', hop'⟩ := hop'
        exact expr_ctLeak_regArith L hq e' hop' V
  all_goals rfl

/-- Leakage of one rewritten expression of the peephole. -/
theorem peepExpr_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    Expr.ctLeak L (peepExpr e) V = Expr.ctLeak L e V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [peepExpr, HVector.head, HVector.tail]
      rw [expr_ctLeak_regArith L hq ⟨.regArith bop w, rfl, .cons a (.cons b .nil)⟩ rfl V]
      rcases hr : peepBin bop a b with _ | e'
      · exact expr_ctLeak_regArith L hq _ rfl V
      · have hop' : ∃ bop', e'.op = .regArith bop' w := by
          unfold peepBin at hr
          split at hr
          · split at hr <;> first | (cases hr; exact ⟨_, binE_op _ _ _⟩) | cases hr
          · cases hr
        obtain ⟨bop', hop'⟩ := hop'
        exact expr_ctLeak_regArith L hq e' hop' V
  all_goals rfl

/-- Leakage of one pass of the saturation engine, from an environment consistent with the
    valuation. -/
theorem rewriteCom_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ),
      KEnv.Consistent k V → Com.ctLeak L (rewriteCom c k) V = Com.ctLeak L c V
  | .ret _, _, _, _ => rfl
  | .var e body, k, V, hk => by
      simp only [rewriteCom, Com.ctLeak]
      rw [rewriteExpr_ctLeak L hq e k V, rewriteExpr_denote e k V hk,
        rewriteCom_ctLeak L hq body (extendK e k) (V.extend (e.denote V))
          (extendK_consistent e k V hk)]

/-- Leakage of the bounded saturation engine, from an environment consistent with the
    valuation. -/
theorem saturateCom_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} :
    ∀ (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ),
      KEnv.Consistent k V → Com.ctLeak L (saturateCom fuel c k) V = Com.ctLeak L c V
  | 0, _, _, _, _ => rfl
  | fuel + 1, c, k, V, hk => by
      simp only [saturateCom]
      rw [saturateCom_ctLeak L hq fuel (rewriteCom c k) k V hk, rewriteCom_ctLeak L hq c k V hk]

/-- Leakage of the peephole pass. -/
theorem peepCom_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      Com.ctLeak L (peepCom c) V = Com.ctLeak L c V
  | .ret _, _ => rfl
  | .var e body, V => by
      simp only [peepCom, Com.ctLeak]
      rw [peepExpr_ctLeak L hq e V, peepExpr_denote e V, peepCom_ctLeak L hq body]

/-- **Leakage of the composed transform.** Under a leakage model whose `regArith`
    operations are quiet, `comAlgebraicPipeline fuel c k` has the leakage of `c` at every
    valuation consistent with `k`. -/
theorem comAlgebraicPipeline_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    Com.ctLeak L (comAlgebraicPipeline fuel c k) V = Com.ctLeak L c V := by
  unfold comAlgebraicPipeline
  rw [saturateCom_ctLeak L hq fuel (peepCom c) k V hk, peepCom_ctLeak L hq c V]

/-- **Constant time of the stage.** Under a leakage model whose `regArith` operations are
    quiet, if `c` is constant time for the relation `R`, so is `optCom c`. -/
theorem optCom_constantTime (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (optCom c)) := by
  unfold optCom
  refine ComGVN.gvnCom_constantTime L _ R fun V₁ V₂ hR => ?_
  rw [comAlgebraicPipeline_ctLeak L hq 1 c _ V₁
      (CatCrypt.Crypto.SecureCompilation.Ascent.KEnv.unknown_consistent V₁),
    comAlgebraicPipeline_ctLeak L hq 1 c _ V₂
      (CatCrypt.Crypto.SecureCompilation.Ascent.KEnv.unknown_consistent V₂)]
  exact h V₁ V₂ hR

end Leak

/-! ## §6  Self-contained validation

`Egraph.demoMulZero` is `x ↦ x * 0` via an explicit `regConst 0` binder.
The composed pipeline (peephole then saturation) preserves its denotation
(both map `x` to `0`) and is cost-non-increasing.  The peephole half does
not fire on this kernel (no `sub a a` / `and a a`), and the saturation
half collapses the `mul`-by-zero to `b &&& b`; the composition therefore
realises the same denotation-preserving rewrite as the saturation engine
alone, through the canonical two-pass entry point. -/

/-- The composed pipeline (fuel 4) preserves the demo's denotation. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoMulZero demoK).denote V = demoMulZero.denote V :=
  comAlgebraicPipeline_denote 4 demoMulZero demoK V (demoK_consistent V)

/-- The composed pipeline preserves CT on the demo. -/
example : ctSafeComJ (comAlgebraicPipeline 4 demoMulZero demoK)
        = ctSafeComJ demoMulZero :=
  comAlgebraicPipeline_ctSafe 4 demoMulZero demoK

/-- The composed pipeline is cost-non-increasing on the demo. -/
example : comCost (comAlgebraicPipeline 4 demoMulZero demoK) ≤ comCost demoMulZero :=
  comAlgebraicPipeline_cost_le 4 demoMulZero demoK

/-- The composed pipeline on the peephole demo (`x ↦ x - x`): the peephole
    half fires (`sub x x ↦ xor x x`), the saturation half leaves it
    (no known constant), and denotation is preserved (both map `x` to `0`). -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoSelfSub demoK).denote V = demoSelfSub.denote V :=
  comAlgebraicPipeline_denote 4 demoSelfSub demoK V (demoK_consistent V)

end CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
