/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalf
public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontLeakNF

/-!
# Constant time through the `Com` optimisation stage of a route program

The optimisation stage `RouteProg.opt` rewrites a straight-line program by
`ComPipeline.optCom` and every straight-line piece of a looped program by `optComL`. Under a
leakage model whose `regArith` operations are quiet, the stage maps equal leakage at two
valuations to equal leakage at the same valuations (`RouteProg.opt_ctLeak_eq`), so it
preserves constant time for every relation on valuations (`RouteCT_opt`).

On a straight-line program this is `ComPipeline.optCom_ctLeak_eq`. On a looped program the
leakage is a concatenation over bindings and iterations, which an equality of two traces does
not split by itself. The split comes from the shape of the traces: a binding emits a number of
events fixed by its operation, a straight-line program a number fixed by the program
(`Com.ctLeak_length_eq`), and a loop node first emits the trip count of the iterations that
follow. Two traces of the same looped program of which one extended equals the other extended
are therefore equal, and the traces of the optimised program at the same two valuations are
equal (`optComL_ctLeak_prefix`). The iterations are carried by `iterLeak_prefix`; the
accumulators of the optimised loop are those of the original one, since the stage keeps the
denotation of every piece (`ComPipeline.optCom_denote`, `optComL_denote`).

## Main results

* `Com.ctLeak_length_eq` — a straight-line program emits the same number of events at every
  valuation.
* `iterLeak_prefix` — the iteration traces of two loops whose single iterations split, split.
* `optCom_ctLeak_prefix`, `optComL_ctLeak_prefix`, `optComL_ctLeak_eq` — the stage on
  straight-line and looped programs maps equal leakage to equal leakage.
* `RouteProg.opt_ctLeak_eq`, `RouteCT_opt` — the same on a route program, and constant time.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak (CatLeakParams catLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnv impToNF hax64SigOf tableOf)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (optCom optCom_denote)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open _root_.Hax (TExpr)

/-! ## The shape of the traces -/

/-- A straight-line program emits the same number of events at every valuation. -/
theorem Com.ctLeak_length_eq (M : LeakModel jasminDialect) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
      (V₁ V₂ : Ctxt.Valuation Γ) → (Com.ctLeak M c V₁).length = (Com.ctLeak M c V₂).length
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, V₁, V₂ => by
      simp only [Com.ctLeak, List.length_append, Dialects.NFLeak.Expr.ctLeak_length]
      rw [Com.ctLeak_length_eq M body _ (V₂.extend (e.denote V₂))]

/-- **Splitting iteration traces.** If a single iteration of the first loop and one of the
    second split off any continuation, with equal traces of the iterations `leak₁'`,
    `leak₂'` at the same accumulators, then the iteration traces over `ts` split off any
    continuation, with equal traces of the iterations `leak₁'`, `leak₂'`. -/
theorem iterLeak_prefix {α : Type} (leak₁ leak₂ leak₁' leak₂' : Nat → α → List CTLeak)
    (step₁ step₂ : Nat → α → α)
    (hb : ∀ (t : Nat) (a₁ a₂ : α) (l₁ l₂ : List CTLeak),
      leak₁ t a₁ ++ l₁ = leak₂ t a₂ ++ l₂ → leak₁ t a₁ = leak₂ t a₂ ∧ leak₁' t a₁ = leak₂' t a₂) :
    ∀ (ts : List Nat) (a₁ a₂ : α) (l₁ l₂ : List CTLeak),
      iterLeak leak₁ step₁ ts a₁ ++ l₁ = iterLeak leak₂ step₂ ts a₂ ++ l₂ →
      iterLeak leak₁ step₁ ts a₁ = iterLeak leak₂ step₂ ts a₂ ∧
        iterLeak leak₁' step₁ ts a₁ = iterLeak leak₂' step₂ ts a₂
  | [], _, _, _, _, _ => ⟨rfl, rfl⟩
  | t :: ts, a₁, a₂, l₁, l₂, h => by
      simp only [iterLeak, List.append_assoc] at h ⊢
      obtain ⟨e1, m1⟩ := hb _ _ _ _ _ h
      rw [e1, List.append_cancel_left_eq] at h
      obtain ⟨e2, m2⟩ := iterLeak_prefix leak₁ leak₂ leak₁' leak₂' step₁ step₂ hb ts _ _ _ _ h
      exact ⟨by rw [e1, e2], by rw [m1, m2]⟩

/-- An iteration trace followed by a continuation `X` splits off any further continuation
    when the iterations and `X` do; the iteration traces `leak₁'`, `leak₂'` followed by the
    continuations `Y₁`, `Y₂` are then equal. -/
theorem iterLeak_cont_prefix {α : Type} {leak₁ leak₂ leak₁' leak₂' : Nat → α → List CTLeak}
    {step₁ step₂ : Nat → α → α} {ts : List Nat} {a₁ a₂ : α}
    {X₁ X₂ Y₁ Y₂ l₁ l₂ : List CTLeak}
    (hb : ∀ (t : Nat) (b₁ b₂ : α) (k₁ k₂ : List CTLeak),
      leak₁ t b₁ ++ k₁ = leak₂ t b₂ ++ k₂ → leak₁ t b₁ = leak₂ t b₂ ∧ leak₁' t b₁ = leak₂' t b₂)
    (hc : X₁ ++ l₁ = X₂ ++ l₂ → X₁ = X₂ ∧ Y₁ = Y₂)
    (h : iterLeak leak₁ step₁ ts a₁ ++ (X₁ ++ l₁) = iterLeak leak₂ step₂ ts a₂ ++ (X₂ ++ l₂)) :
    iterLeak leak₁ step₁ ts a₁ ++ X₁ = iterLeak leak₂ step₂ ts a₂ ++ X₂ ∧
      iterLeak leak₁' step₁ ts a₁ ++ Y₁ = iterLeak leak₂' step₂ ts a₂ ++ Y₂ := by
  obtain ⟨e1, m1⟩ := iterLeak_prefix leak₁ leak₂ leak₁' leak₂' step₁ step₂ hb ts a₁ a₂ _ _ h
  rw [e1, List.append_cancel_left_eq] at h
  obtain ⟨e2, m2⟩ := hc h
  exact ⟨by rw [e1, e2], by rw [m1, m2]⟩

/-! ## The stage maps equal leakage to equal leakage -/

section Stage

variable {M : LeakModel jasminDialect}

/-- **The stage on a straight-line program.** Two traces of `c` of which one extended equals
    the other extended are equal, and so are the traces of `optCom c` at the same
    valuations. -/
theorem optCom_ctLeak_prefix (hq : ∀ bop w, M.kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V₁ V₂ : Ctxt.Valuation Γ) (l₁ l₂ : List CTLeak)
    (h : Com.ctLeak M c V₁ ++ l₁ = Com.ctLeak M c V₂ ++ l₂) :
    Com.ctLeak M c V₁ = Com.ctLeak M c V₂ ∧
      Com.ctLeak M (optCom c) V₁ = Com.ctLeak M (optCom c) V₂ := by
  have he := (List.append_inj h (Com.ctLeak_length_eq M c V₁ V₂)).1
  exact ⟨he, Optimizer.Rewrite.ComPipeline.optCom_ctLeak_eq M hq c V₁ V₂ he⟩

/-- **The stage on a looped program.** Two traces of `c` of which one extended equals the
    other extended are equal, and so are the traces of `optComL c` at the same valuations. -/
theorem optComL_ctLeak_prefix (hq : ∀ bop w, M.kind (.regArith bop w) = .quiet) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : ComL Γ t) →
      (V₁ V₂ : Ctxt.Valuation Γ) → (l₁ l₂ : List CTLeak) →
      ComL.ctLeak M c V₁ ++ l₁ = ComL.ctLeak M c V₂ ++ l₂ →
      ComL.ctLeak M c V₁ = ComL.ctLeak M c V₂ ∧
        ComL.ctLeak M (optComL c) V₁ = ComL.ctLeak M (optComL c) V₂
  | _, _, .ret _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | _, _, .var e body, V₁, V₂, l₁, l₂, h => by
      simp only [optComL, ComL.ctLeak, List.append_assoc] at h ⊢
      obtain ⟨he, h⟩ := List.append_inj h (by simp only [Dialects.NFLeak.Expr.ctLeak_length])
      obtain ⟨e2, m2⟩ := optComL_ctLeak_prefix hq body _ _ _ _ h
      exact ⟨by rw [he, e2], by rw [he, m2]⟩
  | _, _, .forLoop loop init body, V₁, V₂, l₁, l₂, h => by
      simp only [optComL, ComL.ctLeak, JLoopBody.denote, JLoopBody.stepC, optCom_denote,
        List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h ⊢
      exact iterLeak_cont_prefix
        (fun _ _ _ k₁ k₂ hk => optCom_ctLeak_prefix hq loop.update _ _ k₁ k₂ hk)
        (optComL_ctLeak_prefix hq body _ _ _ _) h
  | _, _, .forLoopN loop init invs body, V₁, V₂, l₁, l₂, h => by
      simp only [optComL, ComL.ctLeak, JLoopBodyN.denote, JLoopBodyN.stepC, optCom_denote,
        List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h ⊢
      exact iterLeak_cont_prefix
        (fun _ _ _ k₁ k₂ hk => optCom_ctLeak_prefix hq loop.update _ _ k₁ k₂ hk)
        (optComL_ctLeak_prefix hq body _ _ _ _) h
  | _, _, .forLoopNRt update count init invs body, V₁, V₂, l₁, l₂, h => by
      simp only [optComL, ComL.ctLeak, JLoopBodyN.stepC, optCom_denote,
        List.cons_append, List.cons.injEq, CTLeak.trip.injEq, List.append_assoc] at h ⊢
      obtain ⟨hn, h⟩ := h
      rw [hn] at h ⊢
      simp only [true_and]
      exact iterLeak_cont_prefix
        (fun _ _ _ k₁ k₂ hk => optCom_ctLeak_prefix hq update _ _ k₁ k₂ hk)
        (optComL_ctLeak_prefix hq body _ _ _ _) h
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body,
      V₁, V₂, l₁, l₂, h => by
      simp only [optComL, ComL.ctLeak, JLoopBodyN.nestedDenote, JLoopBodyN.innerTripAtC,
        JLoopBodyN.stepCNested, optCom_denote,
        List.cons_append, List.cons.injEq, CTLeak.trip.injEq, List.append_assoc] at h ⊢
      obtain ⟨hn, h⟩ := h
      rw [hn] at h ⊢
      simp only [true_and]
      refine iterLeak_cont_prefix (fun jd b₁ b₂ k₁ k₂ hk => ?_)
        (optComL_ctLeak_prefix hq body _ _ _ _) h
      simp only [List.append_assoc, List.cons_append] at hk ⊢
      obtain ⟨e1, m1⟩ := optCom_ctLeak_prefix hq innerCount _ _ _ _ hk
      rw [e1, List.append_cancel_left_eq, List.cons.injEq, CTLeak.trip.injEq] at hk
      obtain ⟨hk', hk⟩ := hk
      rw [e1, m1, hk'] at *
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and]
      exact iterLeak_prefix _ _ _ _ _ _
        (fun _ _ _ k₁ k₂ hk => optCom_ctLeak_prefix hq innerUpdate _ _ k₁ k₂ hk) _ _ _ _ _ hk
  | _, _, .whileNz update guard init invs body, V₁, V₂, l₁, l₂, h => by
      simp only [optComL, ComL.ctLeak, JLoopBodyN.stepC, optCom_denote,
        List.cons_append, List.cons.injEq, CTLeak.trip.injEq, List.append_assoc] at h ⊢
      obtain ⟨hn, h⟩ := h
      rw [hn] at h ⊢
      simp only [true_and]
      exact iterLeak_cont_prefix
        (fun _ _ _ k₁ k₂ hk => optCom_ctLeak_prefix hq update _ _ k₁ k₂ hk)
        (optComL_ctLeak_prefix hq body _ _ _ _) h
  | _, _, .forLoopBlock loopBody count init invs body, V₁, V₂, l₁, l₂, h => by
      simp only [optComL, ComL.ctLeak, optComL_denote,
        List.cons_append, List.cons.injEq, CTLeak.trip.injEq, List.append_assoc] at h ⊢
      obtain ⟨hn, h⟩ := h
      rw [hn] at h ⊢
      simp only [true_and]
      exact iterLeak_cont_prefix
        (fun _ _ _ k₁ k₂ hk => optComL_ctLeak_prefix hq loopBody _ _ k₁ k₂ hk)
        (optComL_ctLeak_prefix hq body _ _ _ _) h

/-- **Leakage of the stage on a looped program.** Equal leakage of `c` at two valuations
    gives equal leakage of `optComL c` there. -/
theorem optComL_ctLeak_eq (hq : ∀ bop w, M.kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : ComL.ctLeak M c V₁ = ComL.ctLeak M c V₂) :
    ComL.ctLeak M (optComL c) V₁ = ComL.ctLeak M (optComL c) V₂ :=
  (optComL_ctLeak_prefix hq c V₁ V₂ [] [] (by rw [h])).2

end Stage

/-! ## The stage on a route program -/

/-- **Leakage of the stage on a route program.** Under parameters whose `regArith`
    operations are quiet, equal leakage of `p` at two valuations gives equal leakage of
    `p.opt` there. -/
theorem RouteProg.opt_ctLeak_eq {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : RouteProg Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : RouteProg.ctLeak Pj p V₁ = RouteProg.ctLeak Pj p V₂) :
    RouteProg.ctLeak Pj p.opt V₁ = RouteProg.ctLeak Pj p.opt V₂ := by
  cases p using RouteProg.cases_straight_loop with
  | straight c =>
      rw [RouteProg.ctLeak_straight, RouteProg.ctLeak_straight] at h
      rw [RouteProg.opt_straight, RouteProg.ctLeak_straight, RouteProg.ctLeak_straight]
      exact Optimizer.Rewrite.ComPipeline.optCom_ctLeak_eq _ hq c V₁ V₂ h
  | loop c hc =>
      rw [RouteProg.ctLeak_loop, RouteProg.ctLeak_loop] at h
      rw [RouteProg.opt_loop c hc, RouteProg.ctLeak_loop, RouteProg.ctLeak_loop]
      exact optComL_ctLeak_eq hq c V₁ V₂ h

/-- **Constant time of the stage on a route program.** Under parameters whose `regArith`
    operations are quiet, if `p` is constant time for the labels `L`, so is `p.opt`. -/
theorem RouteCT_opt {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (L : Labels Γ) (p : RouteProg Γ t)
    (h : RouteCT Pj L p) : RouteCT Pj L p.opt :=
  fun V₁ V₂ hR => RouteProg.opt_ctLeak_eq hq p V₁ V₂ (h V₁ V₂ hR)

end CatCrypt.Crypto.SecureCompilation.Haxc
