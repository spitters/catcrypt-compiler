/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakM
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgDCE

/-!
# The leakage transformer of dead-binding elimination

`NFProg.dce` removes a binding whose continuation does not read it, so the events of the
removed operation are absent from the run of the pruned program. The leakage transformer is
the erasure `NFProg.dceErase M fuel p`: a function of the trace of `p` alone, which reads the
trace along the structure of `p` (an operation emits one event or none according to its
class, a counted loop emits `trip n` and then `n` runs of its body, a branch emits `branch b`
and then the arm `b` selects, an exit-flag loop emits a run of its body followed by
`branch b` per iteration), and drops the events of the bindings `dce` removes. It returns the
kept events and the rest of the trace.

A renamed program emits the events of the source (`NFProg.leakRunM_rename?`). A run of `p`
that succeeds is matched by a run of `dce p` to the same results, whose events are the
erasure of the events of `p` (`NFProg.leakRunM_dce`). Since the erasure is a function of
the trace, constant time of `p` relative to its successful runs gives the equality of the
events of `dce p` on the same pairs of valuations (`NFProg.dce_ctRel`).

## Main definitions

* `evCount`, `iterErase`, `whileErase`, `NFProg.dceErase`

## Main results

* `NFProg.leakRunM_rename?` — renaming keeps the events.
* `NFProg.leakRunM_dce` — the leakage transformer of `dce` is the erasure.
* `NFProg.dce_ctRel` — equal source events give equal events after `dce`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## The erasure -/

/-- The number of events an operation of a class emits: none for a quiet operation, one
    otherwise. -/
def evCount : LeakKind → Nat
  | .quiet => 0
  | _ => 1

/-- The reading of `n` runs of a loop body by `er`: the kept events of the runs and the rest
    of the trace. -/
def iterErase (er : List CTLeak → List CTLeak × List CTLeak) :
    Nat → List CTLeak → List CTLeak × List CTLeak
  | 0, tr => ([], tr)
  | n + 1, tr =>
      ((er tr).1 ++ (iterErase er n (er tr).2).1, (iterErase er n (er tr).2).2)

/-- The reading of an exit-flag loop by `er` within `fuel` iterations: each run of the body
    is followed by the event `branch b` of its flag; `branch true` continues. -/
def whileErase (er : List CTLeak → List CTLeak × List CTLeak) :
    Nat → List CTLeak → List CTLeak × List CTLeak
  | 0, tr => ([], tr)
  | n + 1, tr =>
      match (er tr).2 with
      | .branch true :: r =>
          ((er tr).1 ++ .branch true :: (whileErase er n r).1, (whileErase er n r).2)
      | .branch false :: r => ((er tr).1 ++ [.branch false], r)
      | r => ((er tr).1, r)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **The erasure of dead-binding elimination**: the reading of a trace along the structure of
    `p`, keeping the events of the bindings `dce` keeps. It returns the kept events and the
    rest of the trace. -/
def NFProg.dceErase (M : LeakModel d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → List CTLeak →
    List CTLeak × List CTLeak
  | _, _, .ret _, tr => ([], tr)
  | _, _, .var e k, tr =>
      if (NFProg.rename? PRen.drop (NFProg.dce k)).isSome then
        NFProg.dceErase M fuel k (tr.drop (evCount (M.kind e.op)))
      else
        (tr.take (evCount (M.kind e.op)) ++
            (NFProg.dceErase M fuel k (tr.drop (evCount (M.kind e.op)))).1,
          (NFProg.dceErase M fuel k (tr.drop (evCount (M.kind e.op)))).2)
  | _, _, .forLoop _ _ body k, tr =>
      match tr with
      | .trip n :: tr' =>
          (.trip n :: ((iterErase (NFProg.dceErase M fuel body) n tr').1 ++
              (NFProg.dceErase M fuel k (iterErase (NFProg.dceErase M fuel body) n tr').2).1),
            (NFProg.dceErase M fuel k (iterErase (NFProg.dceErase M fuel body) n tr').2).2)
      | _ => ([], tr)
  | _, _, .ifThenElse _ thn els k, tr =>
      match tr with
      | .branch b :: tr' =>
          (.branch b :: ((if b then NFProg.dceErase M fuel thn tr'
              else NFProg.dceErase M fuel els tr').1 ++
              (NFProg.dceErase M fuel k (if b then NFProg.dceErase M fuel thn tr'
                else NFProg.dceErase M fuel els tr').2).1),
            (NFProg.dceErase M fuel k (if b then NFProg.dceErase M fuel thn tr'
              else NFProg.dceErase M fuel els tr').2).2)
      | _ => ([], tr)
  | _, _, .whileLoop _ body k, tr =>
      ((whileErase (NFProg.dceErase M fuel body) fuel tr).1 ++
          (NFProg.dceErase M fuel k (whileErase (NFProg.dceErase M fuel body) fuel tr).2).1,
        (NFProg.dceErase M fuel k (whileErase (NFProg.dceErase M fuel body) fuel tr).2).2)
  | _, _, .call .., tr => ([], tr)

/-! ## Renaming keeps the events -/

omit [HasWord64 d] [HasBoolBit d] in
/-- A renamed expression emits in `W` the events of the source in `V`. -/
theorem Expr.ctLeak_rename? (M : LeakModel d) {Γ Δ : Ctxt d} {t : d.Ty} {f : PRen Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : PRen.Agrees f V W) (e : Expr d Γ t)
    {e' : Expr d Δ t} (he : Expr.rename? f e = some e') :
    Expr.ctLeak M e' W = Expr.ctLeak M e V := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  unfold Expr.ctLeak
  rw [PRen.lookupArgs_vars? h e.args hargs]

variable [DialectDenoteM d Option]

/-- **A renamed program emits the events of the source.** When `rename? f p = some p'` and
    `f` relates `V` to `W`, the leakage run of `p'` at `W` is that of `p` at `V`. -/
theorem NFProg.leakRunM_rename? (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {p' : NFProg d Δ ts} {V : Valuation Γ}
      {W : Valuation Δ}, NFProg.rename? f p = some p' → PRen.Agrees f V W →
      NFProg.leakRunM M fuel p' W = NFProg.leakRunM M fuel p V := by
  induction p with
  | ret vs =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.map_eq_some_iff] at hp
      obtain ⟨ws, hws, rfl⟩ := hp
      simp only [NFProg.leakRunM, PRen.lookupArgs_vars? h vs hws]
  | var e k ih =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨e', he, k', hk, rfl⟩ := hp
      simp only [NFProg.leakRunM, Expr.denoteM_rename? h e he, Expr.ctLeak_rename? M h e he]
      congr 1
      funext x
      rw [ih hk (PRen.agrees_lift h x)]
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨c', hc, i', hi, b', hb, k', hk, rfl⟩ := hp
      simp only [NFProg.leakRunM, h count c' hc, PRen.lookupArgs_vars? h inits hi]
      have hbody : (fun i acc => NFProg.leakRunM M fuel b'
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) W))) =
          (fun i acc => NFProg.leakRunM M fuel body
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) V))) := by
        funext i acc
        exact ihb hb (PRen.agrees_liftApp (PRen.agrees_lift h _) _ acc)
      rw [hbody]
      congr 1
      funext acc
      rw [ihk hk (PRen.agrees_liftApp h _ acc.1)]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨c', hc, t', ht, e', he, k', hk, rfl⟩ := hp
      simp only [NFProg.leakRunM, h cond c' hc, iht ht h, ihe he h]
      congr 1
      funext r
      rw [ihk hk (PRen.agrees_liftApp h _ r.1)]
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨i', hi, b', hb, k', hk, rfl⟩ := hp
      simp only [NFProg.leakRunM, PRen.lookupArgs_vars? h inits hi]
      have hbody : (fun acc => NFProg.leakRunM M fuel b' (hvAppend acc W)) =
          (fun acc => NFProg.leakRunM M fuel body (hvAppend acc V)) := by
        funext acc
        exact ihb hb (PRen.agrees_liftApp h _ acc)
      rw [hbody]
      congr 1
      funext acc
      rw [ihk hk (PRen.agrees_liftApp h _ acc.1)]
  | call fn args k ih =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a', ha, k', hk, rfl⟩ := hp
      rfl

/-! ## The leakage transformer of `dce` -/

omit [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] in
/-- An expression emits as many events as its class counts. -/
theorem Expr.ctLeak_length (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (V : Valuation Γ) : (Expr.ctLeak M e V).length = evCount (M.kind e.op) := by
  unfold Expr.ctLeak opLeak
  split <;> simp_all [evCount]

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] in
/-- Iterations whose steps are matched, with erased events, by the steps of a second loop are
    matched by the iterations of the second loop, with the events `iterErase` keeps. -/
theorem forIterLeak_erase {cs : List d.Ty}
    (step stepD : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (er : List CTLeak → List CTLeak × List CTLeak)
    (hs : ∀ i X r, step i X = some r → ∃ E, stepD i X = some (r.1, E) ∧
      ∀ rest, er (r.2 ++ rest) = (E, rest)) :
    ∀ (is : List Nat) (X : Valuation cs) (q : Valuation cs × List CTLeak),
      forIterLeak step is X = some q → ∃ E, forIterLeak stepD is X = some (q.1, E) ∧
        ∀ rest, iterErase er is.length (q.2 ++ rest) = (E, rest)
  | [], X, q, h => by
      simp only [forIterLeak, Option.some.injEq] at h
      subst h
      exact ⟨[], rfl, fun rest => rfl⟩
  | i :: is, X, q, h => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, q', hq', rfl⟩ := h
      obtain ⟨E₁, h₁, e₁⟩ := hs i X r hr
      obtain ⟨E₂, h₂, e₂⟩ := forIterLeak_erase step stepD er hs is r.1 q' hq'
      refine ⟨E₁ ++ E₂, ?_, fun rest => ?_⟩
      · simp only [forIterLeak, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [List.length_cons, iterErase, List.append_assoc, e₁, e₂]

omit [DialectSignature d] [HasWord64 d] [DialectDenoteM d Option] in
/-- Exit-flag iterations whose body runs are matched, with erased events, by the body runs of
    a second loop are matched by the iterations of the second loop, with the events
    `whileErase` keeps. -/
theorem whileIterLeak_erase {cs : List d.Ty}
    (step stepD : Valuation cs →
      Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (er : List CTLeak → List CTLeak × List CTLeak)
    (hs : ∀ X r, step X = some r → ∃ E, stepD X = some (r.1, E) ∧
      ∀ rest, er (r.2 ++ rest) = (E, rest)) :
    ∀ (n : Nat) (X : Valuation cs) (q : Valuation cs × List CTLeak),
      whileIterLeak step n X = some q → ∃ E, whileIterLeak stepD n X = some (q.1, E) ∧
        ∀ rest, whileErase er n (q.2 ++ rest) = (E, rest)
  | 0, _, _, h => by simp [whileIterLeak] at h
  | n + 1, X, q, h => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, h⟩ := h
      obtain ⟨E₁, h₁, e₁⟩ := hs X r hr
      split at h
      · rename_i hb
        obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨E₂, h₂, e₂⟩ := whileIterLeak_erase step stepD er hs n _ q' hq'
        refine ⟨E₁ ++ .branch true :: E₂, ?_, fun rest => ?_⟩
        · simp only [whileIterLeak, h₁, Option.bind_some, if_pos hb, h₂, Option.map_some]
        · simp only [List.append_assoc, List.cons_append, whileErase, e₁, e₂]
      · rename_i hb
        cases h
        refine ⟨E₁ ++ [.branch false], ?_, fun rest => ?_⟩
        · simp only [whileIterLeak, h₁, Option.bind_some, if_neg hb]
        · simp only [List.append_assoc, List.cons_append, List.nil_append, whileErase, e₁]

/-- **The leakage transformer of dead-binding elimination.** A leakage run of `p` that
    succeeds is matched by a leakage run of `dce p` to the same results, whose events are the
    events `dceErase` keeps from the trace of `p`. -/
theorem NFProg.leakRunM_dce (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) :
    ∀ (V : Valuation Γ) (r : Valuation ts × List CTLeak), NFProg.leakRunM M fuel p V = some r →
      ∃ E, NFProg.leakRunM M fuel (NFProg.dce p) V = some (r.1, E) ∧
        ∀ rest, NFProg.dceErase M fuel p (r.2 ++ rest) = (E, rest) := by
  induction p with
  | ret vs =>
      intro V r h
      simp only [NFProg.leakRunM, Option.some.injEq] at h
      subst h
      exact ⟨[], rfl, fun rest => rfl⟩
  | var e k ih =>
      intro V r h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, q, hq, rfl⟩ := h
      obtain ⟨E, hE, eE⟩ := ih _ q hq
      have hlen := Expr.ctLeak_length M e V
      have htake : ∀ rest, (Expr.ctLeak M e V ++ (q.2 ++ rest)).take
          (evCount (M.kind e.op)) = Expr.ctLeak M e V := by
        intro rest; rw [← hlen, List.take_left]
      have hdrop : ∀ rest, (Expr.ctLeak M e V ++ (q.2 ++ rest)).drop
          (evCount (M.kind e.op)) = q.2 ++ rest := by
        intro rest; rw [← hlen, List.drop_left]
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        refine ⟨E, ?_, fun rest => ?_⟩
        · rw [NFProg.leakRunM_rename? M fuel _ hr (PRen.agrees_drop V x), hE]
        · simp only [NFProg.dceErase, hr, Option.isSome_some, if_true, List.append_assoc,
            hdrop, eE]
      · rename_i hr
        refine ⟨Expr.ctLeak M e V ++ E, ?_, fun rest => ?_⟩
        · simp only [NFProg.leakRunM, hx, Option.bind_some, hE, Option.map_some]
        · have hn : (NFProg.rename? PRen.drop (NFProg.dce k)).isSome = false := by
            rw [hr]; rfl
          simp only [NFProg.dceErase, hn, Bool.false_eq_true, if_false, List.append_assoc,
            htake, hdrop, eE]
  | forLoop count inits body k ihb ihk =>
      intro V r h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨E₁, h₁, e₁⟩ := forIterLeak_erase _ _ (NFProg.dceErase M fuel body)
        (fun i X r hr => ihb _ r hr) _ _ a ha
      obtain ⟨E₂, h₂, e₂⟩ := ihk _ q hq
      refine ⟨.trip (HasWord64.toNat (d := d) (count.lookup V)) :: (E₁ ++ E₂), ?_,
        fun rest => ?_⟩
      · simp only [NFProg.dce, NFProg.leakRunM, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [List.length_range] at e₁
        simp only [NFProg.dceErase, List.cons_append, List.append_assoc, e₁, e₂]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro V r h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨E₂, h₂, e₂⟩ := ihk _ q hq
      have harm : ∃ E₁, (if HasBoolBit.toBool (d := d) (cond.lookup V) then
            NFProg.leakRunM M fuel (NFProg.dce thn) V
          else NFProg.leakRunM M fuel (NFProg.dce els) V) = some (a.1, E₁) ∧
          ∀ rest, (if HasBoolBit.toBool (d := d) (cond.lookup V) then
            NFProg.dceErase M fuel thn (a.2 ++ rest)
          else NFProg.dceErase M fuel els (a.2 ++ rest)) = (E₁, rest) := by
        split at ha
        · rename_i hb
          obtain ⟨E₁, h₁, e₁⟩ := iht V a ha
          exact ⟨E₁, by rw [if_pos hb]; exact h₁, fun rest => by rw [if_pos hb]; exact e₁ rest⟩
        · rename_i hb
          obtain ⟨E₁, h₁, e₁⟩ := ihe V a ha
          exact ⟨E₁, by rw [if_neg hb]; exact h₁, fun rest => by rw [if_neg hb]; exact e₁ rest⟩
      obtain ⟨E₁, h₁, e₁⟩ := harm
      refine ⟨.branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (E₁ ++ E₂), ?_,
        fun rest => ?_⟩
      · simp only [NFProg.dce, NFProg.leakRunM, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [NFProg.dceErase, List.cons_append, List.append_assoc, e₁, e₂]
  | whileLoop inits body k ihb ihk =>
      intro V r h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨E₁, h₁, e₁⟩ := whileIterLeak_erase _ _ (NFProg.dceErase M fuel body)
        (fun X r hr => ihb _ r hr) _ _ a ha
      obtain ⟨E₂, h₂, e₂⟩ := ihk _ q hq
      refine ⟨E₁ ++ E₂, ?_, fun rest => ?_⟩
      · simp only [NFProg.dce, NFProg.leakRunM, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [NFProg.dceErase, List.append_assoc, e₁, e₂]
  | call => intro V r h; simp [NFProg.leakRunM] at h

/-- **Constant time through `dce`, relative to source runs.** Two runs of `p` that succeed
    with equal events give two runs of `dce p` that succeed with equal events. -/
theorem NFProg.dce_ctRel (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation ts × List CTLeak)
    (h₁ : NFProg.leakRunM M fuel p V₁ = some r₁) (h₂ : NFProg.leakRunM M fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRunM M fuel (NFProg.dce p) V₁ = some s₁ ∧
      NFProg.leakRunM M fuel (NFProg.dce p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      s₁.2 = s₂.2 := by
  obtain ⟨E₁, k₁, e₁⟩ := NFProg.leakRunM_dce M fuel p V₁ r₁ h₁
  obtain ⟨E₂, k₂, e₂⟩ := NFProg.leakRunM_dce M fuel p V₂ r₂ h₂
  refine ⟨_, _, k₁, k₂, rfl, rfl, ?_⟩
  have h1 := e₁ []
  have h2 := e₂ []
  rw [he] at h1
  rw [h1] at h2
  exact (Prod.mk.inj h2).1

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
