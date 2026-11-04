/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFDceLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFAbortElim

/-!
# The leakage transformer of the elimination of aborting branches

`NFProg.abortElim ab` replaces a branch without result whose first arm aborts first and whose
second arm returns at once by its continuation. On a run that succeeds the branch took its
second arm, so it emitted `branch false` followed by the events of that arm, and the run of
the eliminated program emits neither. The leakage transformer is the erasure
`NFProg.abortErase ab M fuel p`, a function of the trace of `p` alone that reads the trace
along the structure of `p` as `NFProg.dceErase` does and drops, at each eliminated branch, the
event of the branch and the events of the arm it took. It returns the kept events and the
rest of the trace.

Since the erasure is a function of the trace, constant time of `p` relative to its successful
runs gives the equality of the events of `abortElim ab p` on the same pairs of valuations.
The statements take the hypothesis that every operation `ab` marks denotes no value, the
hypothesis of `NFProg.denote_abortElim`.

## Main definitions

* `NFProg.abortErase` — the erasure.

## Main results

* `NFProg.leakRunM_abortElim` — a successful run of `p` is matched by a run of
  `abortElim ab p` to the same results, whose events are the erasure of the events of `p`.
* `NFProg.abortElim_ctRel` — equal source events give equal events after the elimination.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] (ab : d.Op → Bool)

/-- The test of `NFProg.iteElim` on the eliminated arms: a branch without result is replaced
    by its continuation when its first arm aborts first and its second arm returns at once. -/
def iteElimB {Γ : Ctxt d} {rs : List d.Ty} (thn els : NFProg d Γ rs) : Bool :=
  rs.isEmpty && NFProg.abortsFirst ab thn && NFProg.isRetNil els

/-- **The erasure of the elimination of aborting branches**: the reading of a trace along the
    structure of `p` that drops, at each branch `abortElim` replaces by its continuation, the
    event of the branch and the events of the arm it took. It returns the kept events and the
    rest of the trace. -/
def NFProg.abortErase (M : LeakModel d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → List CTLeak →
    List CTLeak × List CTLeak
  | _, _, .ret _, tr => ([], tr)
  | _, _, .var e k, tr =>
      (tr.take (evCount (M.kind e.op)) ++
          (NFProg.abortErase M fuel k (tr.drop (evCount (M.kind e.op)))).1,
        (NFProg.abortErase M fuel k (tr.drop (evCount (M.kind e.op)))).2)
  | _, _, .forLoop _ _ body k, tr =>
      match tr with
      | .trip n :: tr' =>
          (.trip n :: ((iterErase (NFProg.abortErase M fuel body) n tr').1 ++
              (NFProg.abortErase M fuel k
                (iterErase (NFProg.abortErase M fuel body) n tr').2).1),
            (NFProg.abortErase M fuel k (iterErase (NFProg.abortErase M fuel body) n tr').2).2)
      | _ => ([], tr)
  | _, _, .ifThenElse _ thn els k, tr =>
      match tr with
      | .branch b :: tr' =>
          if iteElimB ab (NFProg.abortElim ab thn) (NFProg.abortElim ab els) then
            NFProg.abortErase M fuel k (if b then NFProg.abortErase M fuel thn tr'
              else NFProg.abortErase M fuel els tr').2
          else
            (.branch b :: ((if b then NFProg.abortErase M fuel thn tr'
                else NFProg.abortErase M fuel els tr').1 ++
                (NFProg.abortErase M fuel k (if b then NFProg.abortErase M fuel thn tr'
                  else NFProg.abortErase M fuel els tr').2).1),
              (NFProg.abortErase M fuel k (if b then NFProg.abortErase M fuel thn tr'
                else NFProg.abortErase M fuel els tr').2).2)
      | _ => ([], tr)
  | _, _, .whileLoop _ body k, tr =>
      ((whileErase (NFProg.abortErase M fuel body) fuel tr).1 ++
          (NFProg.abortErase M fuel k (whileErase (NFProg.abortErase M fuel body) fuel tr).2).1,
        (NFProg.abortErase M fuel k (whileErase (NFProg.abortErase M fuel body) fuel tr).2).2)
  | _, _, .call .., tr => ([], tr)

omit [HasWord64 d] [HasBoolBit d] in
/-- `NFProg.iteElim` at a branch without result is the continuation exactly when the test
    `iteElimB` holds. -/
theorem iteElim_nil_of_iteElimB {Γ : Ctxt d} {ts : List d.Ty} [HasWord64 d] [HasBoolBit d]
    (c : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ [])
    (k : NFProg d ([] ++ Γ) ts) (h : iteElimB ab thn els = true) :
    NFProg.iteElim ab c thn els k = k := by
  simp only [iteElimB, List.isEmpty_nil, Bool.true_and] at h
  rw [NFProg.iteElim, ite_eq_left h]

variable [DialectDenoteM d Option]

/-- A program that aborts first has no leakage run, when every operation `ab` marks denotes no
    value. -/
theorem NFProg.leakRunM_of_abortsFirst
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → e.denoteM V = none)
    (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : NFProg.abortsFirst ab p = true) (V : Valuation Γ) :
    NFProg.leakRunM M fuel p V = none := by
  cases p with
  | var e k =>
      simp only [NFProg.abortsFirst] at hp
      simp only [NFProg.leakRunM, hab e V hp, Option.bind_none]
  | _ => simp [NFProg.abortsFirst] at hp

/-- **The leakage transformer of the elimination of aborting branches.** When every operation
    `ab` marks denotes no value, a leakage run of `p` that succeeds is matched by a leakage
    run of `abortElim ab p` to the same results, whose events are the events `abortErase`
    keeps from the trace of `p`. -/
theorem NFProg.leakRunM_abortElim
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → e.denoteM V = none)
    (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ (V : Valuation Γ) (r : Valuation ts × List CTLeak), NFProg.leakRunM M fuel p V = some r →
      ∃ E, NFProg.leakRunM M fuel (NFProg.abortElim ab p) V = some (r.1, E) ∧
        ∀ rest, NFProg.abortErase ab M fuel p (r.2 ++ rest) = (E, rest) := by
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
      refine ⟨Expr.ctLeak M e V ++ E, ?_, fun rest => ?_⟩
      · simp only [NFProg.abortElim, NFProg.leakRunM, hx, Option.bind_some, hE,
          Option.map_some]
      · simp only [NFProg.abortErase, List.append_assoc, ← hlen, List.take_left,
          List.drop_left, eE]
  | forLoop count inits body k ihb ihk =>
      intro V r h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨E₁, h₁, e₁⟩ := forIterLeak_erase _ _ (NFProg.abortErase ab M fuel body)
        (fun i X r hr => ihb _ r hr) _ _ a ha
      obtain ⟨E₂, h₂, e₂⟩ := ihk _ q hq
      refine ⟨.trip (HasWord64.toNat (d := d) (count.lookup V)) :: (E₁ ++ E₂), ?_,
        fun rest => ?_⟩
      · simp only [NFProg.abortElim, NFProg.leakRunM, h₁, Option.bind_some, h₂,
          Option.map_some]
      · simp only [List.length_range] at e₁
        simp only [NFProg.abortErase, List.cons_append, List.append_assoc, e₁, e₂]
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      intro V r h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨E₂, h₂, e₂⟩ := ihk _ q hq
      have harm : ∃ E₁, (if HasBoolBit.toBool (d := d) (cond.lookup V) then
            NFProg.leakRunM M fuel (NFProg.abortElim ab thn) V
          else NFProg.leakRunM M fuel (NFProg.abortElim ab els) V) = some (a.1, E₁) ∧
          ∀ rest, (if HasBoolBit.toBool (d := d) (cond.lookup V) then
            NFProg.abortErase ab M fuel thn (a.2 ++ rest)
          else NFProg.abortErase ab M fuel els (a.2 ++ rest)) = (E₁, rest) := by
        split at ha
        · rename_i hb
          obtain ⟨E₁, h₁, e₁⟩ := iht V a ha
          exact ⟨E₁, by rw [ite_eq_left hb]; exact h₁,
            fun rest => by rw [ite_eq_left hb]; exact e₁ rest⟩
        · rename_i hb
          obtain ⟨E₁, h₁, e₁⟩ := ihe V a ha
          exact ⟨E₁, by rw [ite_eq_right hb]; exact h₁,
            fun rest => by rw [ite_eq_right hb]; exact e₁ rest⟩
      obtain ⟨E₁, h₁, e₁⟩ := harm
      by_cases hc : iteElimB ab (NFProg.abortElim ab thn) (NFProg.abortElim ab els) = true
      · -- the branch is eliminated: the run took the second arm, which returns at once
        cases rs with
        | cons _ _ => simp [iteElimB] at hc
        | nil =>
          have hc' := hc
          simp only [iteElimB, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true] at hc'
          have hb : HasBoolBit.toBool (d := d) (cond.lookup V) = false := by
            cases hb : HasBoolBit.toBool (d := d) (cond.lookup V)
            · rfl
            · rw [hb, ite_eq_left rfl,
                NFProg.leakRunM_of_abortsFirst ab hab M fuel _ hc'.1] at h₁
              cases h₁
          rw [hb] at h₁ e₁
          simp only [Bool.false_eq_true, ↓reduceIte] at h₁ e₁
          have hret : ∀ (p : NFProg d Γ []), NFProg.isRetNil p = true →
              NFProg.leakRunM M fuel p V = some (a.1, E₁) → a.1 = .nil ∧ E₁ = [] := by
            intro p hp hl
            cases p with
            | ret vs =>
                simp only [NFProg.leakRunM, Option.some.injEq, Prod.mk.injEq] at hl
                cases a.1
                exact ⟨rfl, hl.2.symm⟩
            | _ => simp [NFProg.isRetNil] at hp
          obtain ⟨ha1, hE₁⟩ := hret _ hc'.2 h₁
          subst hE₁
          have hV : hvAppend a.1 V = V := by rw [ha1]; rfl
          rw [hV] at h₂
          refine ⟨E₂, ?_, fun rest => ?_⟩
          · rw [NFProg.abortElim, iteElim_nil_of_iteElimB ab cond _ _ _ hc]
            exact h₂
          · simp only [NFProg.abortErase, List.cons_append, List.append_assoc, hc,
              hb, Bool.false_eq_true, ↓reduceIte]
            rw [e₁ (q.2 ++ rest)]
            exact e₂ rest
      · have hite : NFProg.abortElim ab (NFProg.ifThenElse cond thn els k) =
            .ifThenElse cond (NFProg.abortElim ab thn) (NFProg.abortElim ab els)
              (NFProg.abortElim ab k) := by
          rw [NFProg.abortElim]
          cases rs with
          | cons _ _ => rfl
          | nil =>
              simp only [iteElimB, List.isEmpty_nil, Bool.true_and] at hc
              rw [NFProg.iteElim, ite_eq_right hc]
        refine ⟨.branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (E₁ ++ E₂), ?_,
          fun rest => ?_⟩
        · rw [hite]
          simp only [NFProg.leakRunM, h₁, Option.bind_some, h₂, Option.map_some]
        · simp only [NFProg.abortErase, List.cons_append, List.append_assoc, hc,
            Bool.false_eq_true, ↓reduceIte, e₁, e₂]
  | whileLoop inits body k ihb ihk =>
      intro V r h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨E₁, h₁, e₁⟩ := whileIterLeak_erase _ _ (NFProg.abortErase ab M fuel body)
        (fun X r hr => ihb _ r hr) _ _ a ha
      obtain ⟨E₂, h₂, e₂⟩ := ihk _ q hq
      refine ⟨E₁ ++ E₂, ?_, fun rest => ?_⟩
      · simp only [NFProg.abortElim, NFProg.leakRunM, h₁, Option.bind_some, h₂,
          Option.map_some]
      · simp only [NFProg.abortErase, List.append_assoc, e₁, e₂]
  | call => intro V r h; simp [NFProg.leakRunM] at h

/-- **Constant time through the elimination of aborting branches, relative to source runs.**
    When every operation `ab` marks denotes no value, two runs of `p` that succeed with equal
    events give two runs of `abortElim ab p` that succeed, to the same results, with equal
    events. -/
theorem NFProg.abortElim_ctRel
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → e.denoteM V = none)
    (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation ts × List CTLeak)
    (h₁ : NFProg.leakRunM M fuel p V₁ = some r₁) (h₂ : NFProg.leakRunM M fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRunM M fuel (NFProg.abortElim ab p) V₁ = some s₁ ∧
      NFProg.leakRunM M fuel (NFProg.abortElim ab p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧
      s₂.1 = r₂.1 ∧ s₁.2 = s₂.2 := by
  obtain ⟨E₁, k₁, e₁⟩ := NFProg.leakRunM_abortElim ab hab M fuel p V₁ r₁ h₁
  obtain ⟨E₂, k₂, e₂⟩ := NFProg.leakRunM_abortElim ab hab M fuel p V₂ r₂ h₂
  refine ⟨_, _, k₁, k₂, rfl, rfl, ?_⟩
  have h1 := e₁ []
  have h2 := e₂ []
  rw [he] at h1
  rw [h1] at h2
  exact (Prod.mk.inj h2).1

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
