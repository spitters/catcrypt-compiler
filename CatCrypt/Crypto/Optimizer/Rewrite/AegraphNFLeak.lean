/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
public import CatCrypt.Crypto.Optimizer.Rewrite.Aegraph
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFDceLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect

/-!
# Constant time of the acyclic e-graph over structured programs

`aegraphOptNF R` emits, for each let-binding, the binding itself (renamed and hash-consed)
or a rule alternative, and keeps the region constructors. When the events of every rule
alternative do not depend on the valuation (`RulesIndep`), two runs of a program with equal
events give two runs of the optimised program with equal events
(`aegraphOptNF_ctRel`), and the pass keeps `NFCT` (`aegraphOptNF_nfCT`).

The proof is one induction along `nfGo`. A region's events are split into the events of its
iterations or arm and those of its continuation by the prefix property of leakage traces
(`NFProg.leakRun_prefix`): for a fixed program, a trace is never a proper prefix of
another trace, since a binding emits a number of events fixed by its operation, a counted
loop emits its trip count first, a branch its decision first, and each exit-flag iteration
its flag. The prefix property is read off the erasure parser `NFProg.dceErase` of
dead-binding elimination.

The pass creates no branch, so it keeps a program branch-free (`ifFree_nfGo`,
`ifFree_aegraphOptNF`).

## Main results

* `NFProg.leakRun_prefix` — the prefix property of leakage traces.
* `forIterLeak_ctRel`, `whileIterLeak_ctRel` — loops whose steps are related two-run.
* `nfGo_ctRel`, `aegraphOptNF_ctRel` — equal events in give equal events out.
* `aegraphOptNF_nfCT` — the pass keeps `NFCT`.
* `aegraphOptNF_catRules_nfCT`, `aegraphOptNF_jasminRules_nfCT` — the instances at the two
  rule sets; the jasmin one under quiet `regArith` operations.
* `ifFree_nfGo`, `ifFree_aegraphOptNF` — the pass keeps a program branch-free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel LeakKind Expr.ctLeak Labels)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-! ## 1. The prefix property of leakage traces -/

section Prefix

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- **The prefix property of leakage traces.** Two runs of a program whose traces, each
    followed by a list, are equal have equal traces. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak.NFProg.leakRun_prefix
    (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (V₁ V₂ : Ctxt.Valuation Γ) (r₁ r₂ : Ctxt.Valuation ts × List CTLeak)
    (x y : List CTLeak) (h₁ : NFProg.leakRun M fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRun M fuel p V₂ = some r₂) (he : r₁.2 ++ x = r₂.2 ++ y) :
    r₁.2 = r₂.2 := by
  rw [← NFProg.leakRunM_eq_leakRun] at h₁ h₂
  obtain ⟨E₁, _, e₁⟩ := NFProg.leakRunM_dce M fuel p V₁ r₁ h₁
  obtain ⟨E₂, _, e₂⟩ := NFProg.leakRunM_dce M fuel p V₂ r₂ h₂
  have h := e₁ x
  rw [he, e₂ y] at h
  have hxy : y = x := (Prod.mk.inj h).2
  subst hxy
  exact List.append_cancel_right he

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- The iterations of two counted-loop runs over the same indices, whose steps have the
    prefix property, have the prefix property. -/
theorem forIterLeak_prefix {cs : List d.Ty}
    (a₁ a₂ : Nat → Ctxt.Valuation cs → Option (Ctxt.Valuation cs × List CTLeak))
    (hpf : ∀ i X Y (r r' : Ctxt.Valuation cs × List CTLeak) (x y : List CTLeak),
      a₁ i X = some r → a₂ i Y = some r' → r.2 ++ x = r'.2 ++ y → r.2 = r'.2) :
    ∀ (l : List Nat) (X Y : Ctxt.Valuation cs) (r r' : Ctxt.Valuation cs × List CTLeak)
      (x y : List CTLeak), forIterLeak a₁ l X = some r → forIterLeak a₂ l Y = some r' →
      r.2 ++ x = r'.2 ++ y → r.2 = r'.2
  | [], X, Y, r, r', x, y, h₁, h₂, _ => by
      simp only [forIterLeak, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      rfl
  | i :: l, X, Y, r, r', x, y, h₁, h₂, he => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨u₁, hu₁, q₁, hq₁, rfl⟩ := h₁
      obtain ⟨u₂, hu₂, q₂, hq₂, rfl⟩ := h₂
      simp only [List.append_assoc] at he
      have hu := hpf i X Y u₁ u₂ _ _ hu₁ hu₂ he
      rw [hu] at he
      have hq := forIterLeak_prefix a₁ a₂ hpf l _ _ q₁ q₂ x y hq₁ hq₂
        (List.append_cancel_left he)
      show u₁.2 ++ q₁.2 = u₂.2 ++ q₂.2
      rw [hu, hq]

omit [DialectSignature d] [HasWord64 d] [DialectDenote d] in
/-- The iterations of two exit-flag loop runs at the same fuel, whose bodies have the prefix
    property, have the prefix property. -/
theorem whileIterLeak_prefix {cs : List d.Ty}
    (a₁ a₂ : Ctxt.Valuation cs →
      Option (Ctxt.Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (hpf : ∀ X Y (r r' : Ctxt.Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak)
      (x y : List CTLeak), a₁ X = some r → a₂ Y = some r' → r.2 ++ x = r'.2 ++ y →
      r.2 = r'.2) :
    ∀ (n : Nat) (X Y : Ctxt.Valuation cs) (r r' : Ctxt.Valuation cs × List CTLeak)
      (x y : List CTLeak), whileIterLeak a₁ n X = some r → whileIterLeak a₂ n Y = some r' →
      r.2 ++ x = r'.2 ++ y → r.2 = r'.2
  | 0, _, _, _, _, _, _, h₁, _, _ => by simp [whileIterLeak] at h₁
  | n + 1, X, Y, r, r', x, y, h₁, h₂, he => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨u₁, hu₁, h₁⟩ := h₁
      obtain ⟨u₂, hu₂, h₂⟩ := h₂
      by_cases c₁ : HasBoolBit.toBool (d := d) u₁.1.head = true <;>
        by_cases c₂ : HasBoolBit.toBool (d := d) u₂.1.head = true <;>
        simp only [c₁, c₂, if_true, if_false, Bool.false_eq_true, Option.map_eq_some_iff,
          Option.some.injEq] at h₁ h₂
      · obtain ⟨q₁, hq₁, rfl⟩ := h₁
        obtain ⟨q₂, hq₂, rfl⟩ := h₂
        simp only [List.append_assoc, List.cons_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        rw [hu] at he
        have he' := (List.cons.inj (List.append_cancel_left he)).2
        have hq := whileIterLeak_prefix a₁ a₂ hpf n _ _ q₁ q₂ x y hq₁ hq₂ he'
        show u₁.2 ++ .branch true :: q₁.2 = u₂.2 ++ .branch true :: q₂.2
        rw [hu, hq]
      · obtain ⟨q₁, hq₁, rfl⟩ := h₁
        subst h₂
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        rw [hu] at he
        simp at he
      · obtain ⟨q₂, hq₂, rfl⟩ := h₂
        subst h₁
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        rw [hu] at he
        simp at he
      · subst h₁ h₂
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        show u₁.2 ++ [.branch false] = u₂.2 ++ [.branch false]
        rw [hu]

/-- **The prefix property of leakage traces at a call environment.** Two runs at `E` of a
    program whose traces, each followed by a list, are equal have equal traces; a call node
    emits no event. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak.NFProg.leakRunMC_prefix
    (M : LeakModel d) (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) :
    ∀ (V₁ V₂ : Ctxt.Valuation Γ) (r₁ r₂ : Ctxt.Valuation ts × List CTLeak)
      (x y : List CTLeak), NFProg.leakRunMC M E fuel p V₁ = some r₁ →
      NFProg.leakRunMC M E fuel p V₂ = some r₂ → r₁.2 ++ x = r₂.2 ++ y → r₁.2 = r₂.2 := by
  induction p with
  | ret vs =>
      intro V₁ V₂ r₁ r₂ x y h₁ h₂ _
      simp only [NFProg.leakRunMC, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      rfl
  | var e k ih =>
      intro V₁ V₂ r₁ r₂ x y h₁ h₂ he
      simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      simp only [List.append_assoc] at he
      obtain ⟨hE, hB⟩ := List.append_inj he (opLeak_length M e.op _ _)
      show Expr.ctLeak M e V₁ ++ u₁.2 = Expr.ctLeak M e V₂ ++ u₂.2
      rw [hE, ih _ _ u₁ u₂ x y hu₁ hu₂ hB]
  | forLoop count inits body k ihb ihk =>
      intro V₁ V₂ r₁ r₂ x y h₁ h₂ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      simp only [List.cons_append, List.append_assoc] at he
      obtain ⟨hn, he'⟩ := List.cons.inj he
      injection hn with hn
      rw [← hn] at hi₂
      have hi := forIterLeak_prefix _ _
        (fun i X Y r r' x y h h' hxy => ihb _ _ r r' x y h h' hxy) _ _ _ i₁ i₂ _ _ hi₁ hi₂ he'
      rw [hi] at he'
      have hq := ihk _ _ q₁ q₂ x y hq₁ hq₂ (List.append_cancel_left he')
      show _ :: (i₁.2 ++ q₁.2) = _ :: (i₂.2 ++ q₂.2)
      rw [hi, hq, hn]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro V₁ V₂ r₁ r₂ x y h₁ h₂ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      simp only [List.cons_append, List.append_assoc] at he
      obtain ⟨hc, he'⟩ := List.cons.inj he
      injection hc with hc
      rw [← hc] at ha₂
      have ha : a₁.2 = a₂.2 := by
        split at ha₁
        · rw [if_pos (by assumption)] at ha₂
          exact iht _ _ a₁ a₂ _ _ ha₁ ha₂ he'
        · rw [if_neg (by assumption)] at ha₂
          exact ihe _ _ a₁ a₂ _ _ ha₁ ha₂ he'
      rw [ha] at he'
      have hq := ihk _ _ q₁ q₂ x y hq₁ hq₂ (List.append_cancel_left he')
      show _ :: (a₁.2 ++ q₁.2) = _ :: (a₂.2 ++ q₂.2)
      rw [ha, hq, hc]
  | whileLoop inits body k ihb ihk =>
      intro V₁ V₂ r₁ r₂ x y h₁ h₂ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      simp only [List.append_assoc] at he
      have hi := whileIterLeak_prefix _ _
        (fun X Y r r' x y h h' hxy => ihb _ _ r r' x y h h' hxy) _ _ _ i₁ i₂ _ _ hi₁ hi₂ he
      rw [hi] at he
      have hq := ihk _ _ q₁ q₂ x y hq₁ hq₂ (List.append_cancel_left he)
      show i₁.2 ++ q₁.2 = i₂.2 ++ q₂.2
      rw [hi, hq]
  | call f args k ih =>
      intro V₁ V₂ r₁ r₂ x y h₁ h₂ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      obtain ⟨a₁, -, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨a₂, -, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      exact ih _ _ r₁ r₂ x y h₁ h₂ he

end Prefix

/-! ## 2. Loops related two-run -/

section Loops

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] in
/-- **Counted loops related two-run.** Let `a₁`, `a₂` be the steps of two runs of a loop
    and `b₁`, `b₂` those of two runs of a second loop with the results of `a₁`, `a₂`.
    If the traces of `a₁` and `a₂` have the prefix property and equal traces of `a₁`, `a₂`
    give equal traces of `b₁`, `b₂`, then iterations of `a₁`, `a₂` whose traces, each
    followed by a list, are equal have equal traces, and the iterations of `b₁`, `b₂` have
    equal traces and the results of `a₁`, `a₂`. -/
theorem forIterLeak_ctRel {cs : List d.Ty}
    (a₁ a₂ b₁ b₂ : Nat → Ctxt.Valuation cs → Option (Ctxt.Valuation cs × List CTLeak))
    (hf₁ : ∀ i X, (b₁ i X).map Prod.fst = (a₁ i X).map Prod.fst)
    (hf₂ : ∀ i X, (b₂ i X).map Prod.fst = (a₂ i X).map Prod.fst)
    (hpf : ∀ i X Y (r r' : Ctxt.Valuation cs × List CTLeak) (x y : List CTLeak),
      a₁ i X = some r → a₂ i Y = some r' → r.2 ++ x = r'.2 ++ y → r.2 = r'.2)
    (hrel : ∀ i X Y (r r' s s' : Ctxt.Valuation cs × List CTLeak), a₁ i X = some r →
      a₂ i Y = some r' → b₁ i X = some s → b₂ i Y = some s' → r.2 = r'.2 → s.2 = s'.2) :
    ∀ (l : List Nat) (X Y : Ctxt.Valuation cs) (r r' s s' : Ctxt.Valuation cs × List CTLeak)
      (x y : List CTLeak),
      forIterLeak a₁ l X = some r → forIterLeak a₂ l Y = some r' →
      forIterLeak b₁ l X = some s → forIterLeak b₂ l Y = some s' →
      r.2 ++ x = r'.2 ++ y → r.2 = r'.2 ∧ s.2 = s'.2 ∧ s.1 = r.1 ∧ s'.1 = r'.1
  | [], X, Y, r, r', s, s', x, y, h₁, h₂, h₃, h₄, _ => by
      simp only [forIterLeak, Option.some.injEq] at h₁ h₂ h₃ h₄
      subst h₁ h₂ h₃ h₄
      exact ⟨rfl, rfl, rfl, rfl⟩
  | i :: l, X, Y, r, r', s, s', x, y, h₁, h₂, h₃, h₄, he => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂ h₃ h₄
      obtain ⟨u₁, hu₁, q₁, hq₁, rfl⟩ := h₁
      obtain ⟨u₂, hu₂, q₂, hq₂, rfl⟩ := h₂
      obtain ⟨v₁, hv₁, w₁, hw₁, rfl⟩ := h₃
      obtain ⟨v₂, hv₂, w₂, hw₂, rfl⟩ := h₄
      have e₁ : v₁.1 = u₁.1 := by
        have := hf₁ i X
        rw [hv₁, hu₁] at this
        exact Option.some.inj this
      have e₂ : v₂.1 = u₂.1 := by
        have := hf₂ i Y
        rw [hv₂, hu₂] at this
        exact Option.some.inj this
      rw [e₁] at hw₁
      rw [e₂] at hw₂
      simp only [List.append_assoc] at he
      have hu := hpf i X Y u₁ u₂ _ _ hu₁ hu₂ he
      rw [hu] at he
      obtain ⟨hq, hw, hs₁, hs₂⟩ := forIterLeak_ctRel a₁ a₂ b₁ b₂ hf₁ hf₂ hpf hrel l _ _ q₁ q₂
        w₁ w₂ x y hq₁ hq₂ hw₁ hw₂ (List.append_cancel_left he)
      refine ⟨?_, ?_, hs₁, hs₂⟩
      · show u₁.2 ++ q₁.2 = u₂.2 ++ q₂.2
        rw [hu, hq]
      · show v₁.2 ++ w₁.2 = v₂.2 ++ w₂.2
        rw [hrel i X Y u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hu, hw]

omit [DialectSignature d] [HasWord64 d] in
/-- **Exit-flag loops related two-run.** The counterpart of `forIterLeak_ctRel` for the
    iterations `whileIterLeak` of an exit-flag loop. -/
theorem whileIterLeak_ctRel {cs : List d.Ty}
    (a₁ a₂ b₁ b₂ : Ctxt.Valuation cs →
      Option (Ctxt.Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (hf₁ : ∀ X, (b₁ X).map Prod.fst = (a₁ X).map Prod.fst)
    (hf₂ : ∀ X, (b₂ X).map Prod.fst = (a₂ X).map Prod.fst)
    (hpf : ∀ X Y (r r' : Ctxt.Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak)
      (x y : List CTLeak), a₁ X = some r → a₂ Y = some r' → r.2 ++ x = r'.2 ++ y →
      r.2 = r'.2)
    (hrel : ∀ X Y (r r' s s' : Ctxt.Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak),
      a₁ X = some r → a₂ Y = some r' → b₁ X = some s → b₂ Y = some s' → r.2 = r'.2 →
      s.2 = s'.2) :
    ∀ (n : Nat) (X Y : Ctxt.Valuation cs) (r r' s s' : Ctxt.Valuation cs × List CTLeak)
      (x y : List CTLeak),
      whileIterLeak a₁ n X = some r → whileIterLeak a₂ n Y = some r' →
      whileIterLeak b₁ n X = some s → whileIterLeak b₂ n Y = some s' →
      r.2 ++ x = r'.2 ++ y → r.2 = r'.2 ∧ s.2 = s'.2 ∧ s.1 = r.1 ∧ s'.1 = r'.1
  | 0, _, _, _, _, _, _, _, _, h₁, _, _, _, _ => by simp [whileIterLeak] at h₁
  | n + 1, X, Y, r, r', s, s', x, y, h₁, h₂, h₃, h₄, he => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁ h₂ h₃ h₄
      obtain ⟨u₁, hu₁, h₁⟩ := h₁
      obtain ⟨u₂, hu₂, h₂⟩ := h₂
      obtain ⟨v₁, hv₁, h₃⟩ := h₃
      obtain ⟨v₂, hv₂, h₄⟩ := h₄
      have e₁ : v₁.1 = u₁.1 := by
        have := hf₁ X
        rw [hv₁, hu₁] at this
        exact Option.some.inj this
      have e₂ : v₂.1 = u₂.1 := by
        have := hf₂ Y
        rw [hv₂, hu₂] at this
        exact Option.some.inj this
      rw [e₁] at h₃
      rw [e₂] at h₄
      have hrv := hrel X Y u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂
      by_cases c₁ : HasBoolBit.toBool (d := d) u₁.1.head = true <;>
        by_cases c₂ : HasBoolBit.toBool (d := d) u₂.1.head = true <;>
        simp only [c₁, c₂, if_true, if_false, Bool.false_eq_true, Option.map_eq_some_iff,
          Option.some.injEq] at h₁ h₂ h₃ h₄
      · obtain ⟨q₁, hq₁, rfl⟩ := h₁
        obtain ⟨q₂, hq₂, rfl⟩ := h₂
        obtain ⟨w₁, hw₁, rfl⟩ := h₃
        obtain ⟨w₂, hw₂, rfl⟩ := h₄
        simp only [List.append_assoc, List.cons_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        rw [hu] at he
        have he' := (List.cons.inj (List.append_cancel_left he)).2
        obtain ⟨hq, hw, hs₁, hs₂⟩ := whileIterLeak_ctRel a₁ a₂ b₁ b₂ hf₁ hf₂ hpf hrel n _ _
          q₁ q₂ w₁ w₂ x y hq₁ hq₂ hw₁ hw₂ he'
        refine ⟨?_, ?_, hs₁, hs₂⟩
        · show u₁.2 ++ .branch true :: q₁.2 = u₂.2 ++ .branch true :: q₂.2
          rw [hu, hq]
        · show v₁.2 ++ .branch true :: w₁.2 = v₂.2 ++ .branch true :: w₂.2
          rw [hrv hu, hw]
      · obtain ⟨q₁, hq₁, rfl⟩ := h₁
        subst h₂
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        rw [hu] at he
        simp at he
      · obtain ⟨q₂, hq₂, rfl⟩ := h₂
        subst h₁
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        rw [hu] at he
        simp at he
      · subst h₁ h₂ h₃ h₄
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hu₁ hu₂ he
        refine ⟨?_, ?_, ?_, ?_⟩
        · show u₁.2 ++ [.branch false] = u₂.2 ++ [.branch false]
          rw [hu]
        · show v₁.2 ++ [.branch false] = v₂.2 ++ [.branch false]
          rw [hrv hu]
        · rfl
        · rfl

end Loops

/-! ## 3. The traversal -/

section Traversal

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]

/-- The results of the leakage run of the traversal are those of the source at the
    pulled-back valuation. -/
theorem nfGo_leakRun_fst (R : RuleSet d) (M : LeakModel d) (fuel : Nat) {Γ Δ : Ctxt d}
    {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d) (p : NFProg d Γ ts)
    (V : Ctxt.Valuation Δ) (hS : StSound V S) :
    (NFProg.leakRun M fuel (nfGo R ρ S p) V).map Prod.fst =
      (NFProg.leakRun M fuel p (V.comap ρ)).map Prod.fst := by
  rw [NFProg.leakRun_fst, NFProg.leakRun_fst]
  let _ : CallDenote d := ⟨CallEnv.empty⟩
  exact nfGo_denote R fuel ρ S p V hS

/-- A run of the traversal and a run of the source at the pulled-back valuation have the
    same results. -/
theorem nfGo_fst_eq (R : RuleSet d) (M : LeakModel d) (fuel : Nat) {Γ Δ : Ctxt d}
    {ts : List d.Ty} {ρ : Ctxt.Hom Γ Δ} {S : Tbl d × Defs d} {p : NFProg d Γ ts}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) {r s : Ctxt.Valuation ts × List CTLeak}
    (h : NFProg.leakRun M fuel p (V.comap ρ) = some r)
    (h' : NFProg.leakRun M fuel (nfGo R ρ S p) V = some s) : s.1 = r.1 := by
  have := nfGo_leakRun_fst R M fuel ρ S p V hS
  rw [h, h'] at this
  exact Option.some.inj this

omit [DecidableEq d.Ty] [DialectSignature d] [DialectDenote d] [DecidableEq d.Op]
  [HasWord64 d] [HasBoolBit d] in
/-- The renaming of a loop body, lifted through the carried tuple and the trip index, pulls
    a prefixed valuation back to the same prefix in front of the pulled-back valuation. -/
theorem comap_homLiftApp_cons (cs : List d.Ty) {Γ Δ : Ctxt d} (ρ : Ctxt.Hom Γ Δ)
    (X : Ctxt.Valuation cs) {s : d.Ty} (x : ⟦s⟧) (V : Ctxt.Valuation Δ) :
    Ctxt.Valuation.comap (homLiftApp cs (Ctxt.Hom.lift ρ))
        (hvAppend X (.cons x V) : Ctxt.Valuation (cs ++ s :: Δ)) =
      hvAppend X (.cons x (V.comap ρ)) := by
  rw [comap_homLiftApp]
  exact congrArg (hvAppend X) (Ctxt.Valuation.extend_comap_lift ρ V x)

variable {L : LeakModel d}

/-- **Leakage of the traversal, two-run.** Under states sound for `V₁` and `V₂`, two runs
    of the source at the pulled-back valuations with equal events give, for any two runs
    of the output at `V₁` and `V₂`, equal events. -/
theorem nfGo_ctRel (R : RuleSet d) (hI : RulesIndep L R) (fuel : Nat) :
    ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (p : NFProg d Γ ts) (V₁ V₂ : Ctxt.Valuation Δ), StSound V₁ S → StSound V₂ S →
      ∀ (r₁ r₂ s₁ s₂ : Ctxt.Valuation ts × List CTLeak),
      NFProg.leakRun L fuel p (V₁.comap ρ) = some r₁ →
      NFProg.leakRun L fuel p (V₂.comap ρ) = some r₂ →
      NFProg.leakRun L fuel (nfGo R ρ S p) V₁ = some s₁ →
      NFProg.leakRun L fuel (nfGo R ρ S p) V₂ = some s₂ → r₁.2 = r₂.2 → s₁.2 = s₂.2
  | _, _, _, ρ, _, .ret vs, V₁, V₂, _, _, r₁, r₂, s₁, s₂, _, _, h₃, h₄, _ => by
      simp only [nfGo, NFProg.leakRun, Option.some.injEq] at h₃ h₄
      subst h₃ h₄
      rfl
  | _, Δ, _, ρ, S, .var e k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨hE, hB⟩ := List.append_inj he (opLeak_length L e.op _ _)
      rw [← Expr.ctLeak_rename, ← Expr.ctLeak_rename] at hE
      have hP := choose_leak R hI S (e.rename ρ)
      simp only [nfGo] at h₃ h₄
      cases hc : choose R S (e.rename ρ) with
      | var w =>
          simp only [hc] at h₃ h₄
          obtain ⟨hS₁', hw₁⟩ := stVar_sound R hS₁ _ hc
          obtain ⟨hS₂', hw₂⟩ := stVar_sound R hS₂ _ hc
          refine nfGo_ctRel R hI fuel _ _ k V₁ V₂ hS₁' hS₂' u₁ u₂ s₁ s₂ ?_ ?_ h₃ h₄ hB
          · rw [comap_consHom, hw₁, Expr.denote_rename]
            exact hu₁
          · rw [comap_consHom, hw₂, Expr.denote_rename]
            exact hu₂
      | one e2 =>
          simp only [hc, NFProg.leakRun] at h₃ h₄
          obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
          obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
          obtain ⟨hS₁', hw₁⟩ := stOne_sound R hS₁ _ hc
          obtain ⟨hS₂', hw₂⟩ := stOne_sound R hS₂ _ hc
          have hE2 : Expr.ctLeak L e2 V₁ = Expr.ctLeak L e2 V₂ := by
            rw [hc] at hP
            rcases hP with h' | h'
            · injection h' with h''
              subst h''
              exact hE
            · exact h' V₁ V₂
          show Expr.ctLeak L e2 V₁ ++ t₁.2 = Expr.ctLeak L e2 V₂ ++ t₂.2
          rw [hE2]
          congr 1
          refine nfGo_ctRel R hI fuel _ _ k _ _ hS₁' hS₂' u₁ u₂ t₁ t₂ ?_ ?_ ht₁ ht₂ hB
          · rw [Ctxt.Valuation.extend_comap_lift, hw₁, Expr.denote_rename]
            exact hu₁
          · rw [Ctxt.Valuation.extend_comap_lift, hw₂, Expr.denote_rename]
            exact hu₂
      | two e1 e2 =>
          simp only [hc, NFProg.leakRun, Option.map_map] at h₃ h₄
          obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
          obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
          obtain ⟨hS₁', hw₁⟩ := stTwo_sound R hS₁ _ hc
          obtain ⟨hS₂', hw₂⟩ := stTwo_sound R hS₂ _ hc
          have hI2 : (Alt.two e1 e2).Indep L := by
            rw [hc] at hP
            rcases hP with h' | h'
            · cases h'
            · exact h'
          show Expr.ctLeak L e1 V₁ ++ (Expr.ctLeak L e2 (V₁.extend (e1.denote V₁)) ++ t₁.2) =
            Expr.ctLeak L e1 V₂ ++ (Expr.ctLeak L e2 (V₂.extend (e1.denote V₂)) ++ t₂.2)
          rw [hI2.1 V₁ V₂, hI2.2 _ (V₂.extend (e1.denote V₂))]
          congr 2
          refine nfGo_ctRel R hI fuel _ _ k _ _ hS₁' hS₂' u₁ u₂ t₁ t₂ ?_ ?_ ht₁ ht₂ hB
          · rw [comap_consHom, comap_wk2]
            show NFProg.leakRun L fuel k
              ((V₁.comap ρ).extend (e2.denote (V₁.extend (e1.denote V₁)))) = some u₁
            rw [hw₁, Expr.denote_rename]
            exact hu₁
          · rw [comap_consHom, comap_wk2]
            show NFProg.leakRun L fuel k
              ((V₂.comap ρ).extend (e2.denote (V₂.extend (e1.denote V₂)))) = some u₂
            rw [hw₂, Expr.denote_rename]
            exact hu₂
  | _, Δ, _, ρ, S, .forLoop (cs := cs) count inits body k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun, Ctxt.Valuation.lookup_comap] at h₁ h₂
      simp only [nfGo, NFProg.leakRun, Expr.lookupArgs_renameVars] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hn, he'⟩ := List.cons.inj he
      injection hn with hn
      rw [← hn] at hi₂ hj₂
      have hb : ∀ (V : Ctxt.Valuation Δ) (X : Ctxt.Valuation cs) (i : Nat),
          StSound V S → StSound (Γ := cs ++ _ :: _)
            (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V)) S := fun V X i hS =>
        stSound_append X (stSound_extend (HasWord64.ofNat (d := d) i) hS)
      obtain ⟨hi, hj, hji₁, hji₂⟩ := forIterLeak_ctRel
        (fun i X => NFProg.leakRun L fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) (V₁.comap ρ))))
        (fun i X => NFProg.leakRun L fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) (V₂.comap ρ))))
        (fun i X => NFProg.leakRun L fuel (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₁)))
        (fun i X => NFProg.leakRun L fuel (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₂)))
        (fun i X => by
          rw [nfGo_leakRun_fst R L fuel _ S body _ (hb V₁ X i hS₁), comap_homLiftApp_cons])
        (fun i X => by
          rw [nfGo_leakRun_fst R L fuel _ S body _ (hb V₂ X i hS₂), comap_homLiftApp_cons])
        (fun i X Y r r' x y h h' hxy =>
          NFProg.leakRun_prefix L fuel body _ _ r r' x y h h' hxy)
        (fun i X Y r r' s s' h h' g g' hr =>
          nfGo_ctRel R hI fuel _ S body _ _ (hb V₁ X i hS₁) (hb V₂ Y i hS₂) r r' s s'
            (by rw [comap_homLiftApp_cons]; exact h)
            (by rw [comap_homLiftApp_cons]; exact h') g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he'
      rw [hi] at he'
      have hq := List.append_cancel_left he'
      have hk := nfGo_ctRel R hI fuel _ S k _ _ (stSound_append j₁.1 hS₁)
        (stSound_append j₂.1 hS₂) q₁ q₂ t₁ t₂
        (by rw [comap_homLiftApp, hji₁]; exact hq₁)
        (by rw [comap_homLiftApp, hji₂]; exact hq₂) ht₁ ht₂ hq
      show _ :: (j₁.2 ++ t₁.2) = _ :: (j₂.2 ++ t₂.2)
      rw [hj, hk, hn]
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun, Ctxt.Valuation.lookup_comap] at h₁ h₂
      simp only [nfGo, NFProg.leakRun] at h₃ h₄
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hc, he'⟩ := List.cons.inj he
      injection hc with hc
      rw [← hc] at ha₂ hb₂
      have harm : a₁.2 = a₂.2 ∧ b₁.2 = b₂.2 ∧ b₁.1 = a₁.1 ∧ b₂.1 = a₂.1 := by
        cases hcb : HasBoolBit.toBool (d := d) ((ρ cond).lookup V₁) <;>
          simp only [hcb, if_true, if_false, Bool.false_eq_true] at ha₁ ha₂ hb₁ hb₂
        · have ha := NFProg.leakRun_prefix L fuel els _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, nfGo_ctRel R hI fuel ρ S els V₁ V₂ hS₁ hS₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha,
            nfGo_fst_eq R L fuel hS₁ ha₁ hb₁, nfGo_fst_eq R L fuel hS₂ ha₂ hb₂⟩
        · have ha := NFProg.leakRun_prefix L fuel thn _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, nfGo_ctRel R hI fuel ρ S thn V₁ V₂ hS₁ hS₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha,
            nfGo_fst_eq R L fuel hS₁ ha₁ hb₁, nfGo_fst_eq R L fuel hS₂ ha₂ hb₂⟩
      obtain ⟨ha, hb, hba₁, hba₂⟩ := harm
      rw [ha] at he'
      have hq := List.append_cancel_left he'
      have hk := nfGo_ctRel R hI fuel _ S k _ _ (stSound_append b₁.1 hS₁)
        (stSound_append b₂.1 hS₂) q₁ q₂ t₁ t₂
        (by rw [comap_homLiftApp, hba₁]; exact hq₁)
        (by rw [comap_homLiftApp, hba₂]; exact hq₂) ht₁ ht₂ hq
      show _ :: (b₁.2 ++ t₁.2) = _ :: (b₂.2 ++ t₂.2)
      rw [hb, hk, hc]
  | _, Δ, _, ρ, S, .whileLoop (cs := cs) inits body k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [nfGo, NFProg.leakRun, Expr.lookupArgs_renameVars] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hb : ∀ (V : Ctxt.Valuation Δ) (X : Ctxt.Valuation cs), StSound V S →
          StSound (Γ := cs ++ _) (hvAppend X V) S := fun V X hS => stSound_append X hS
      obtain ⟨hi, hj, hji₁, hji₂⟩ := whileIterLeak_ctRel
        (fun X => NFProg.leakRun L fuel body (hvAppend X (V₁.comap ρ)))
        (fun X => NFProg.leakRun L fuel body (hvAppend X (V₂.comap ρ)))
        (fun X => NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S body) (hvAppend X V₁))
        (fun X => NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S body) (hvAppend X V₂))
        (fun X => by
          rw [nfGo_leakRun_fst R L fuel _ S body _ (hb V₁ X hS₁), comap_homLiftApp])
        (fun X => by
          rw [nfGo_leakRun_fst R L fuel _ S body _ (hb V₂ X hS₂), comap_homLiftApp])
        (fun X Y r r' x y h h' hxy =>
          NFProg.leakRun_prefix L fuel body _ _ r r' x y h h' hxy)
        (fun X Y r r' s s' h h' g g' hr =>
          nfGo_ctRel R hI fuel _ S body _ _ (hb V₁ X hS₁) (hb V₂ Y hS₂) r r' s s'
            (by rw [comap_homLiftApp]; exact h)
            (by rw [comap_homLiftApp]; exact h') g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he
      rw [hi] at he
      have hq := List.append_cancel_left he
      have hk := nfGo_ctRel R hI fuel _ S k _ _ (stSound_append j₁.1 hS₁)
        (stSound_append j₂.1 hS₂) q₁ q₂ t₁ t₂
        (by rw [comap_homLiftApp, hji₁]; exact hq₁)
        (by rw [comap_homLiftApp, hji₂]; exact hq₂) ht₁ ht₂ hq
      show j₁.2 ++ t₁.2 = j₂.2 ++ t₂.2
      rw [hj, hk]
  | _, _, _, _, _, .call .., _, _, _, _, _, _, _, _, h₁, _, _, _, _ => by
      simp [NFProg.leakRun] at h₁

/-- **Leakage of the pass, two-run.** For a rule set whose alternatives have events
    independent of the valuation, two runs of `p` that succeed with equal events give two
    runs of `aegraphOptNF R p` that succeed, with the same results and equal events. -/
theorem aegraphOptNF_ctRel (R : RuleSet d) (hI : RulesIndep L R) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (V₁ V₂ : Ctxt.Valuation Γ)
    (r₁ r₂ : Ctxt.Valuation ts × List CTLeak) (h₁ : NFProg.leakRun L fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRun L fuel p V₂ = some r₂) (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRun L fuel (aegraphOptNF R p) V₁ = some s₁ ∧
      NFProg.leakRun L fuel (aegraphOptNF R p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      s₁.2 = s₂.2 := by
  have hc : ∀ V : Ctxt.Valuation Γ, V.comap (Ctxt.Hom.id Γ) = V := Ctxt.Valuation.comap_id
  have f₁ := nfGo_leakRun_fst R L fuel (Ctxt.Hom.id Γ) (∅, ∅) p V₁ (stSound_empty V₁)
  have f₂ := nfGo_leakRun_fst R L fuel (Ctxt.Hom.id Γ) (∅, ∅) p V₂ (stSound_empty V₂)
  rw [hc, h₁, Option.map_some] at f₁
  rw [hc, h₂, Option.map_some] at f₂
  obtain ⟨s₁, hs₁, e₁⟩ := Option.map_eq_some_iff.mp f₁
  obtain ⟨s₂, hs₂, e₂⟩ := Option.map_eq_some_iff.mp f₂
  refine ⟨s₁, s₂, hs₁, hs₂, e₁, e₂, ?_⟩
  exact nfGo_ctRel R hI fuel _ _ p V₁ V₂ (stSound_empty V₁) (stSound_empty V₂) r₁ r₂ s₁ s₂
    (by rw [hc]; exact h₁) (by rw [hc]; exact h₂) hs₁ hs₂ he

/-- **Constant time of the pass.** For a rule set whose alternatives have events
    independent of the valuation, if `p` is constant time for the labels `Lb`, so is
    `aegraphOptNF R p`. -/
theorem aegraphOptNF_nfCT (R : RuleSet d) (hI : RulesIndep L R) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (Lb : Labels Γ) (p : NFProg d Γ ts) (hct : NFCT L Lb fuel p) :
    NFCT L Lb fuel (aegraphOptNF R p) := by
  intro V₁ V₂ hV
  have hc : ∀ V : Ctxt.Valuation Γ, V.comap (Ctxt.Hom.id Γ) = V := Ctxt.Valuation.comap_id
  have f₁ := nfGo_leakRun_fst R L fuel (Ctxt.Hom.id Γ) (∅, ∅) p V₁ (stSound_empty V₁)
  have f₂ := nfGo_leakRun_fst R L fuel (Ctxt.Hom.id Γ) (∅, ∅) p V₂ (stSound_empty V₂)
  rw [hc] at f₁ f₂
  have hp := hct V₁ V₂ hV
  change (NFProg.leakRun L fuel (nfGo R _ _ p) V₁).map Prod.snd =
    (NFProg.leakRun L fuel (nfGo R _ _ p) V₂).map Prod.snd
  rcases hr₁ : NFProg.leakRun L fuel p V₁ with _ | r₁ <;>
    rcases hr₂ : NFProg.leakRun L fuel p V₂ with _ | r₂ <;>
    rw [hr₁] at f₁ hp <;> rw [hr₂] at f₂ hp
  · rw [Option.map_eq_none_iff.mp f₁, Option.map_eq_none_iff.mp f₂]
  · cases hp
  · cases hp
  · obtain ⟨s₁, hs₁, _⟩ := Option.map_eq_some_iff.mp f₁
    obtain ⟨s₂, hs₂, _⟩ := Option.map_eq_some_iff.mp f₂
    rw [hs₁, hs₂, Option.map_some, Option.map_some,
      nfGo_ctRel R hI fuel _ _ p V₁ V₂ (stSound_empty V₁) (stSound_empty V₂) r₁ r₂ s₁ s₂
        (by rw [hc]; exact hr₁) (by rw [hc]; exact hr₂) hs₁ hs₂
        (Option.some.inj hp)]

/-! ### At a call environment -/

/-- The results of the leakage run at `E` of the traversal are those of the source at the
    pulled-back valuation. -/
theorem nfGo_leakRunMC_fst (R : RuleSet d) (M : LeakModel d) (E : CallEnv d) (fuel : Nat)
    {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d) (p : NFProg d Γ ts)
    (V : Ctxt.Valuation Δ) (hS : StSound V S) :
    (NFProg.leakRunMC M E fuel (nfGo R ρ S p) V).map Prod.fst =
      (NFProg.leakRunMC M E fuel p (V.comap ρ)).map Prod.fst := by
  rw [NFProg.leakRunMC_fst, NFProg.leakRunMC_fst]
  let _ : CallDenote d := ⟨E⟩
  exact nfGo_denote R fuel ρ S p V hS

/-- A run at `E` of the traversal and a run at `E` of the source at the pulled-back
    valuation have the same results. -/
theorem nfGo_fst_eqC (R : RuleSet d) (M : LeakModel d) (E : CallEnv d) (fuel : Nat)
    {Γ Δ : Ctxt d} {ts : List d.Ty} {ρ : Ctxt.Hom Γ Δ} {S : Tbl d × Defs d}
    {p : NFProg d Γ ts} {V : Ctxt.Valuation Δ} (hS : StSound V S)
    {r s : Ctxt.Valuation ts × List CTLeak}
    (h : NFProg.leakRunMC M E fuel p (V.comap ρ) = some r)
    (h' : NFProg.leakRunMC M E fuel (nfGo R ρ S p) V = some s) : s.1 = r.1 := by
  have := nfGo_leakRunMC_fst R M E fuel ρ S p V hS
  rw [h, h'] at this
  exact Option.some.inj this

/-- **Leakage of the traversal at a call environment, two-run.** The statement `nfGo_ctRel`
    for the runs `NFProg.leakRunMC` at `E`, in which a call node emits no event. -/
theorem nfGo_ctRelC (R : RuleSet d) (hI : RulesIndep L R) (E : CallEnv d) (fuel : Nat) :
    ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (p : NFProg d Γ ts) (V₁ V₂ : Ctxt.Valuation Δ), StSound V₁ S → StSound V₂ S →
      ∀ (r₁ r₂ s₁ s₂ : Ctxt.Valuation ts × List CTLeak),
      NFProg.leakRunMC L E fuel p (V₁.comap ρ) = some r₁ →
      NFProg.leakRunMC L E fuel p (V₂.comap ρ) = some r₂ →
      NFProg.leakRunMC L E fuel (nfGo R ρ S p) V₁ = some s₁ →
      NFProg.leakRunMC L E fuel (nfGo R ρ S p) V₂ = some s₂ → r₁.2 = r₂.2 → s₁.2 = s₂.2
  | _, _, _, ρ, _, .ret vs, V₁, V₂, _, _, r₁, r₂, s₁, s₂, _, _, h₃, h₄, _ => by
      simp only [nfGo, NFProg.leakRunMC, Option.some.injEq] at h₃ h₄
      subst h₃ h₄
      rfl
  | _, Δ, _, ρ, S, .var e k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨hE, hB⟩ := List.append_inj he (opLeak_length L e.op _ _)
      rw [← Expr.ctLeak_rename, ← Expr.ctLeak_rename] at hE
      have hP := choose_leak R hI S (e.rename ρ)
      simp only [nfGo] at h₃ h₄
      cases hc : choose R S (e.rename ρ) with
      | var w =>
          simp only [hc] at h₃ h₄
          obtain ⟨hS₁', hw₁⟩ := stVar_sound R hS₁ _ hc
          obtain ⟨hS₂', hw₂⟩ := stVar_sound R hS₂ _ hc
          refine nfGo_ctRelC R hI E fuel _ _ k V₁ V₂ hS₁' hS₂' u₁ u₂ s₁ s₂ ?_ ?_ h₃ h₄ hB
          · rw [comap_consHom, hw₁, Expr.denote_rename]
            exact hu₁
          · rw [comap_consHom, hw₂, Expr.denote_rename]
            exact hu₂
      | one e2 =>
          simp only [hc, NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some]
            at h₃ h₄
          obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
          obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
          obtain ⟨hS₁', hw₁⟩ := stOne_sound R hS₁ _ hc
          obtain ⟨hS₂', hw₂⟩ := stOne_sound R hS₂ _ hc
          have hE2 : Expr.ctLeak L e2 V₁ = Expr.ctLeak L e2 V₂ := by
            rw [hc] at hP
            rcases hP with h' | h'
            · injection h' with h''
              subst h''
              exact hE
            · exact h' V₁ V₂
          show Expr.ctLeak L e2 V₁ ++ t₁.2 = Expr.ctLeak L e2 V₂ ++ t₂.2
          rw [hE2]
          congr 1
          refine nfGo_ctRelC R hI E fuel _ _ k _ _ hS₁' hS₂' u₁ u₂ t₁ t₂ ?_ ?_ ht₁ ht₂ hB
          · rw [Ctxt.Valuation.extend_comap_lift, hw₁, Expr.denote_rename]
            exact hu₁
          · rw [Ctxt.Valuation.extend_comap_lift, hw₂, Expr.denote_rename]
            exact hu₂
      | two e1 e2 =>
          simp only [hc, NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
            Option.map_map] at h₃ h₄
          obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
          obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
          obtain ⟨hS₁', hw₁⟩ := stTwo_sound R hS₁ _ hc
          obtain ⟨hS₂', hw₂⟩ := stTwo_sound R hS₂ _ hc
          have hI2 : (Alt.two e1 e2).Indep L := by
            rw [hc] at hP
            rcases hP with h' | h'
            · cases h'
            · exact h'
          show Expr.ctLeak L e1 V₁ ++ (Expr.ctLeak L e2 (V₁.extend (e1.denote V₁)) ++ t₁.2) =
            Expr.ctLeak L e1 V₂ ++ (Expr.ctLeak L e2 (V₂.extend (e1.denote V₂)) ++ t₂.2)
          rw [hI2.1 V₁ V₂, hI2.2 _ (V₂.extend (e1.denote V₂))]
          congr 2
          refine nfGo_ctRelC R hI E fuel _ _ k _ _ hS₁' hS₂' u₁ u₂ t₁ t₂ ?_ ?_ ht₁ ht₂ hB
          · rw [comap_consHom, comap_wk2]
            show NFProg.leakRunMC L E fuel k
              ((V₁.comap ρ).extend (e2.denote (V₁.extend (e1.denote V₁)))) = some u₁
            rw [hw₁, Expr.denote_rename]
            exact hu₁
          · rw [comap_consHom, comap_wk2]
            show NFProg.leakRunMC L E fuel k
              ((V₂.comap ρ).extend (e2.denote (V₂.extend (e1.denote V₂)))) = some u₂
            rw [hw₂, Expr.denote_rename]
            exact hu₂
  | _, Δ, _, ρ, S, .forLoop (cs := cs) count inits body k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC, Ctxt.Valuation.lookup_comap] at h₁ h₂
      simp only [nfGo, NFProg.leakRunMC, Expr.lookupArgs_renameVars] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hn, he'⟩ := List.cons.inj he
      injection hn with hn
      rw [← hn] at hi₂ hj₂
      have hb : ∀ (V : Ctxt.Valuation Δ) (X : Ctxt.Valuation cs) (i : Nat),
          StSound V S → StSound (Γ := cs ++ _ :: _)
            (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V)) S := fun V X i hS =>
        stSound_append X (stSound_extend (HasWord64.ofNat (d := d) i) hS)
      obtain ⟨hi, hj, hji₁, hji₂⟩ := forIterLeak_ctRel
        (fun i X => NFProg.leakRunMC L E fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) (V₁.comap ρ))))
        (fun i X => NFProg.leakRunMC L E fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) (V₂.comap ρ))))
        (fun i X => NFProg.leakRunMC L E fuel
          (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₁)))
        (fun i X => NFProg.leakRunMC L E fuel
          (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₂)))
        (fun i X => by
          rw [nfGo_leakRunMC_fst R L E fuel _ S body _ (hb V₁ X i hS₁),
            comap_homLiftApp_cons])
        (fun i X => by
          rw [nfGo_leakRunMC_fst R L E fuel _ S body _ (hb V₂ X i hS₂),
            comap_homLiftApp_cons])
        (fun i X Y r r' x y h h' hxy =>
          NFProg.leakRunMC_prefix L E fuel body _ _ r r' x y h h' hxy)
        (fun i X Y r r' s s' h h' g g' hr =>
          nfGo_ctRelC R hI E fuel _ S body _ _ (hb V₁ X i hS₁) (hb V₂ Y i hS₂) r r' s s'
            (by rw [comap_homLiftApp_cons]; exact h)
            (by rw [comap_homLiftApp_cons]; exact h') g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he'
      rw [hi] at he'
      have hq := List.append_cancel_left he'
      have hk := nfGo_ctRelC R hI E fuel _ S k _ _ (stSound_append j₁.1 hS₁)
        (stSound_append j₂.1 hS₂) q₁ q₂ t₁ t₂
        (by rw [comap_homLiftApp, hji₁]; exact hq₁)
        (by rw [comap_homLiftApp, hji₂]; exact hq₂) ht₁ ht₂ hq
      show _ :: (j₁.2 ++ t₁.2) = _ :: (j₂.2 ++ t₂.2)
      rw [hj, hk, hn]
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC, Ctxt.Valuation.lookup_comap] at h₁ h₂
      simp only [nfGo, NFProg.leakRunMC] at h₃ h₄
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hc, he'⟩ := List.cons.inj he
      injection hc with hc
      rw [← hc] at ha₂ hb₂
      have harm : a₁.2 = a₂.2 ∧ b₁.2 = b₂.2 ∧ b₁.1 = a₁.1 ∧ b₂.1 = a₂.1 := by
        cases hcb : HasBoolBit.toBool (d := d) ((ρ cond).lookup V₁) <;>
          simp only [hcb, if_true, if_false, Bool.false_eq_true] at ha₁ ha₂ hb₁ hb₂
        · have ha := NFProg.leakRunMC_prefix L E fuel els _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, nfGo_ctRelC R hI E fuel ρ S els V₁ V₂ hS₁ hS₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂
            ha, nfGo_fst_eqC R L E fuel hS₁ ha₁ hb₁, nfGo_fst_eqC R L E fuel hS₂ ha₂ hb₂⟩
        · have ha := NFProg.leakRunMC_prefix L E fuel thn _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, nfGo_ctRelC R hI E fuel ρ S thn V₁ V₂ hS₁ hS₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂
            ha, nfGo_fst_eqC R L E fuel hS₁ ha₁ hb₁, nfGo_fst_eqC R L E fuel hS₂ ha₂ hb₂⟩
      obtain ⟨ha, hb, hba₁, hba₂⟩ := harm
      rw [ha] at he'
      have hq := List.append_cancel_left he'
      have hk := nfGo_ctRelC R hI E fuel _ S k _ _ (stSound_append b₁.1 hS₁)
        (stSound_append b₂.1 hS₂) q₁ q₂ t₁ t₂
        (by rw [comap_homLiftApp, hba₁]; exact hq₁)
        (by rw [comap_homLiftApp, hba₂]; exact hq₂) ht₁ ht₂ hq
      show _ :: (b₁.2 ++ t₁.2) = _ :: (b₂.2 ++ t₂.2)
      rw [hb, hk, hc]
  | _, Δ, _, ρ, S, .whileLoop (cs := cs) inits body k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [nfGo, NFProg.leakRunMC, Expr.lookupArgs_renameVars] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hb : ∀ (V : Ctxt.Valuation Δ) (X : Ctxt.Valuation cs), StSound V S →
          StSound (Γ := cs ++ _) (hvAppend X V) S := fun V X hS => stSound_append X hS
      obtain ⟨hi, hj, hji₁, hji₂⟩ := whileIterLeak_ctRel
        (fun X => NFProg.leakRunMC L E fuel body (hvAppend X (V₁.comap ρ)))
        (fun X => NFProg.leakRunMC L E fuel body (hvAppend X (V₂.comap ρ)))
        (fun X => NFProg.leakRunMC L E fuel (nfGo R (homLiftApp cs ρ) S body) (hvAppend X V₁))
        (fun X => NFProg.leakRunMC L E fuel (nfGo R (homLiftApp cs ρ) S body) (hvAppend X V₂))
        (fun X => by
          rw [nfGo_leakRunMC_fst R L E fuel _ S body _ (hb V₁ X hS₁), comap_homLiftApp])
        (fun X => by
          rw [nfGo_leakRunMC_fst R L E fuel _ S body _ (hb V₂ X hS₂), comap_homLiftApp])
        (fun X Y r r' x y h h' hxy =>
          NFProg.leakRunMC_prefix L E fuel body _ _ r r' x y h h' hxy)
        (fun X Y r r' s s' h h' g g' hr =>
          nfGo_ctRelC R hI E fuel _ S body _ _ (hb V₁ X hS₁) (hb V₂ Y hS₂) r r' s s'
            (by rw [comap_homLiftApp]; exact h)
            (by rw [comap_homLiftApp]; exact h') g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he
      rw [hi] at he
      have hq := List.append_cancel_left he
      have hk := nfGo_ctRelC R hI E fuel _ S k _ _ (stSound_append j₁.1 hS₁)
        (stSound_append j₂.1 hS₂) q₁ q₂ t₁ t₂
        (by rw [comap_homLiftApp, hji₁]; exact hq₁)
        (by rw [comap_homLiftApp, hji₂]; exact hq₂) ht₁ ht₂ hq
      show j₁.2 ++ t₁.2 = j₂.2 ++ t₂.2
      rw [hj, hk]
  | _, Δ, _, ρ, S, .call (rs := rs) f args k, V₁, V₂, hS₁, hS₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [nfGo, NFProg.leakRunMC, Expr.lookupArgs_renameVars] at h₃ h₄
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      rw [ha₁, Option.some.injEq] at hb₁
      rw [ha₂, Option.some.injEq] at hb₂
      subst hb₁ hb₂
      exact nfGo_ctRelC R hI E fuel _ S k _ _ (stSound_append a₁ hS₁) (stSound_append a₂ hS₂)
        r₁ r₂ s₁ s₂ (by rw [comap_homLiftApp]; exact h₁) (by rw [comap_homLiftApp]; exact h₂)
        h₃ h₄ he

/-- **Leakage of the pass at a call environment, two-run.** The statement
    `aegraphOptNF_ctRel` for the runs `NFProg.leakRunMC` at `E`. -/
theorem aegraphOptNF_ctRelC (R : RuleSet d) (hI : RulesIndep L R) (E : CallEnv d)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V₁ V₂ : Ctxt.Valuation Γ)
    (r₁ r₂ : Ctxt.Valuation ts × List CTLeak) (h₁ : NFProg.leakRunMC L E fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRunMC L E fuel p V₂ = some r₂) (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRunMC L E fuel (aegraphOptNF R p) V₁ = some s₁ ∧
      NFProg.leakRunMC L E fuel (aegraphOptNF R p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧
      s₂.1 = r₂.1 ∧ s₁.2 = s₂.2 := by
  have hc : ∀ V : Ctxt.Valuation Γ, V.comap (Ctxt.Hom.id Γ) = V := Ctxt.Valuation.comap_id
  have f₁ := nfGo_leakRunMC_fst R L E fuel (Ctxt.Hom.id Γ) (∅, ∅) p V₁ (stSound_empty V₁)
  have f₂ := nfGo_leakRunMC_fst R L E fuel (Ctxt.Hom.id Γ) (∅, ∅) p V₂ (stSound_empty V₂)
  rw [hc, h₁, Option.map_some] at f₁
  rw [hc, h₂, Option.map_some] at f₂
  obtain ⟨s₁, hs₁, e₁⟩ := Option.map_eq_some_iff.mp f₁
  obtain ⟨s₂, hs₂, e₂⟩ := Option.map_eq_some_iff.mp f₂
  refine ⟨s₁, s₂, hs₁, hs₂, e₁, e₂, ?_⟩
  exact nfGo_ctRelC R hI E fuel _ _ p V₁ V₂ (stSound_empty V₁) (stSound_empty V₂) r₁ r₂ s₁ s₂
    (by rw [hc]; exact h₁) (by rw [hc]; exact h₂) hs₁ hs₂ he

end Traversal

/-! ## 4. The two rule sets -/

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-- **Constant time of the pass at the catCrypt rule set**, for every leakage model. -/
theorem aegraphOptNF_catRules_nfCT {L : LeakModel catCryptDialect} (fuel : Nat)
    {Γ : Ctxt catCryptDialect} {ts : List _} (Lb : Labels Γ)
    (p : NFProg catCryptDialect Γ ts) (hct : NFCT L Lb fuel p) :
    NFCT L Lb fuel (aegraphOptNF AegraphCat.catRules p) :=
  aegraphOptNF_nfCT AegraphCat.catRules AegraphCat.catRules_indep fuel Lb p hct

/-- **Constant time of the pass at the jasmin rule set**, for a leakage model whose
    `regArith` operations are quiet. -/
theorem aegraphOptNF_jasminRules_nfCT {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List _} (Lb : Labels Γ)
    (p : NFProg jasminDialect Γ ts) (hct : NFCT L Lb fuel p) :
    NFCT L Lb fuel (aegraphOptNF Aegraph.jasminRules p) :=
  aegraphOptNF_nfCT Aegraph.jasminRules (Aegraph.jasminRules_indep hq) fuel Lb p hct

/-! ## 5. The pass keeps a program branch-free -/

section IfFree

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]

/-- **The traversal keeps a program branch-free.** -/
theorem ifFree_nfGo (R : RuleSet d) : ∀ {Γ Δ : Ctxt d} {ts : List d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d) (p : NFProg d Γ ts),
    NFProg.ifFree p = true → NFProg.ifFree (nfGo R ρ S p) = true
  | _, _, _, _, _, .ret _, _ => rfl
  | _, _, _, ρ, S, .var e k, hp => by
      have hk : NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using hp
      simp only [nfGo]
      split
      · exact ifFree_nfGo R _ _ k hk
      · simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using
          ifFree_nfGo R _ _ k hk
      · simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using
          ifFree_nfGo R _ _ k hk
  | _, _, _, ρ, S, .forLoop _ _ body k, hp => by
      have hbk : NFProg.ifFree body = true ∧ NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true] using hp
      simp only [nfGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true]
      exact ⟨ifFree_nfGo R _ _ body hbk.1, ifFree_nfGo R _ _ k hbk.2⟩
  | _, _, _, _, _, .ifThenElse .., hp => by
      simp [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] at hp
  | _, _, _, ρ, S, .whileLoop _ body k, hp => by
      have hbk : NFProg.ifFree body = true ∧ NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true] using hp
      simp only [nfGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true]
      exact ⟨ifFree_nfGo R _ _ body hbk.1, ifFree_nfGo R _ _ k hbk.2⟩
  | _, _, _, ρ, S, .call _ _ k, hp => by
      have hk : NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] using hp
      simpa only [nfGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] using
        ifFree_nfGo R _ _ k hk

/-- **The pass keeps a program branch-free.** -/
theorem ifFree_aegraphOptNF (R : RuleSet d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : NFProg.ifFree p = true) :
    NFProg.ifFree (aegraphOptNF R p) = true :=
  ifFree_nfGo R _ _ p hp

end IfFree

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
