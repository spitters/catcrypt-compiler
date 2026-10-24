/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-!
# Relational congruence of the region operators of `NFProg`

A region of `NFProg` denotes a Kleisli arrow of `Option`, and the three region operators
are the fold `List.foldlM` over the trip indices, the fuel-bounded exit-flag iteration
`NFProg.whileIter`, and the branch. This module states their congruence under a relation
`R` between two carriers of possibly different types: two runs whose steps preserve `R`
end in results related by `R`. The carriers, the step functions and the dialects may differ
between the two sides; the index list and the fuel are shared.

Each rule has two forms.

* The bisimulation form relates the two `Option` results by `Option.Rel R`: both fail or
  both succeed with related values. At the graph `R a a' := T a = a'` of a function `T`
  it is the equation `g (T a) = (f a).map T` (`rel_graph_iff`).
* The forward form (suffix `_fwd`) relates a successful left run to a successful right
  run: `f a = some b → ∃ b', g a' = some b' ∧ R b b'`.

The leak writer `Option (· × List CTLeak)` of `Dialects/NFLeak.lean` has the same rules
for `forIterLeak` and `whileIterLeak`, with the events of the two runs equal. The branch
rule `ite_rel` is stated over any `Option` type and serves both denotations.

This is the loop rule of a relational Hoare logic (pRHL's `rHoare_foldM`) at the effect
`Option`, with heterogeneous carriers.

## Main results

* `NFProg.rel_graph_iff`, `NFProg.bind_rel`, `NFProg.bind_rel_fwd` — the graph of a
  function and the bind rule.
* `NFProg.foldlM_rel_graded_list`, `NFProg.foldlM_rel_graded` and their `_fwd` forms — the
  counted loop under a relation family indexed by the trip index;
  `NFProg.foldlM_add_bounded_rel` is an instance with the bound `a ≤ B * j`.
* `NFProg.foldlM_rel`, `NFProg.foldlM_rel_fwd` — the counted loop, the constant family.
* `NFProg.whileIter_rel`, `NFProg.whileIter_rel_fwd`, `NFProg.whileIter_rel_graded`,
  `NFProg.whileIter_fwd_le` — the exit-flag loop.
* `NFProg.ite_rel`, `NFProg.ite_rel_fwd` — the branch.
* `NFProg.forIterLeak_rel_bisim`, `NFProg.forIterLeak_rel_fwd`,
  `NFProg.whileIterLeak_rel_bisim`, `NFProg.whileIterLeak_rel_fwd` — the two loops of the
  leak writer.
* `NFProg.forIterLeak_pure` — a counted loop of the leak writer whose steps are the image
  of a pure step under an embedding `E` of carriers.
* `NFProg.denote_forLoop_rel`, `NFProg.denote_ifThenElse_rel`,
  `NFProg.denote_whileLoop_rel` and their `_fwd` forms — the program-level congruence of
  each region constructor, with the graded forms `NFProg.denote_forLoop_rel_graded` and
  `NFProg.denote_forLoop_rel_graded_fwd`: two programs of the same constructor, over possibly different
  dialects and contexts, whose components are related, denote related results on related
  valuations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (forIterLeak whileIterLeak)

namespace NFProg

/-! ## 1. `Option`: graph and bind -/

section Generic

universe u v w

/-- `Option.Rel` at the graph of `T` is the equation `o.map T = o'`. -/
theorem rel_graph_iff {α : Type u} {β : Type v} {T : α → β} {o : Option α}
    {o' : Option β} : Option.Rel (fun a b => T a = b) o o' ↔ o.map T = o' := by
  constructor
  · rintro (⟨h⟩ | _) <;> simp [*]
  · rintro rfl
    cases o
    · exact .none
    · exact .some rfl

/-- `Option.Rel` at the graph of `T` on the first component and the equality on the second
    is the equation `o.map (fun r => (T r.1, r.2)) = o'`. -/
theorem rel_graph_prod_iff {α : Type u} {β : Type v} {γ : Type w} {T : α → β}
    {o : Option (α × γ)} {o' : Option (β × γ)} :
    Option.Rel (fun r r' => T r.1 = r'.1 ∧ r.2 = r'.2) o o' ↔
      o.map (fun r => (T r.1, r.2)) = o' := by
  have hR : (fun (r : α × γ) (r' : β × γ) => T r.1 = r'.1 ∧ r.2 = r'.2) =
      fun r r' => (T r.1, r.2) = r' := by
    funext r r'
    simp only [Prod.ext_iff]
  rw [hR]
  exact rel_graph_iff

/-- A computation and its image under `F` are `Option.Rel S`-related when `F` sends every
    value to an `S`-related one. -/
theorem rel_map_of {α : Type u} {β : Type v} {S : α → β → Prop} {F : α → β}
    (hF : ∀ a, S a (F a)) (o : Option α) : Option.Rel S o (o.map F) := by
  cases o
  · exact .none
  · exact .some (hF _)

/-- The bind rule, bisimulation form: related computations followed by continuations that
    send related values to `S`-related computations give `S`-related computations. -/
theorem bind_rel {α α' β β' : Type u}
    {R : α → α' → Prop} {S : β → β' → Prop} {o : Option α} {o' : Option α'}
    {k : α → Option β} {k' : α' → Option β'} (ho : Option.Rel R o o')
    (hk : ∀ a a', R a a' → Option.Rel S (k a) (k' a')) : Option.Rel S (o >>= k) (o' >>= k') := by
  cases ho with
  | none => exact .none
  | some h => exact hk _ _ h

/-- The bind rule, forward form. -/
theorem bind_rel_fwd {α α' β β' : Type u}
    {R : α → α' → Prop} {S : β → β' → Prop} {o : Option α} {o' : Option α'}
    {k : α → Option β} {k' : α' → Option β'}
    (ho : ∀ a, o = some a → ∃ a', o' = some a' ∧ R a a')
    (hk : ∀ a a' b, R a a' → k a = some b → ∃ b', k' a' = some b' ∧ S b b') :
    ∀ b, (o >>= k) = some b → ∃ b', (o' >>= k') = some b' ∧ S b b' := by
  intro b h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨a, ha, hb⟩ := h
  obtain ⟨a', ha', hr⟩ := ho a ha
  obtain ⟨b', hb', hs⟩ := hk a a' b hr hb
  exact ⟨b', ⟨a', ha', hb'⟩, hs⟩

/-! ## 2. The counted loop -/

/-- **The counted loop over a list, graded bisimulation form.** The relation is a family
    `R : ℕ → α → α' → Prop` indexed by the step count from the grade `k`: two `Option` folds
    over the same list whose step at position `j` sends `R (k + j)`-related carriers to
    `Option.Rel (R (k + j + 1))`-related results send `R k`-related initial carriers to
    `Option.Rel (R (k + l.length))`-related results. -/
theorem foldlM_rel_graded_list {α : Type u} {α' : Type v} {β : Type w}
    {R : ℕ → α → α' → Prop} {f : α → β → Option α} {g : α' → β → Option α'} :
    ∀ (l : List β) (k : ℕ), (∀ (j : ℕ) (hj : j < l.length), ∀ a a', R (k + j) a a' →
        Option.Rel (R (k + j + 1)) (f a l[j]) (g a' l[j])) →
      ∀ a a', R k a a' → Option.Rel (R (k + l.length)) (l.foldlM f a) (l.foldlM g a')
  | [], _, _, _, _, h => .some h
  | i :: l, k, h, a, a', hr => by
      simp only [List.foldlM_cons]
      have hi : Option.Rel (R (k + 1)) (f a i) (g a' i) := h 0 (by simp) a a' hr
      revert hi
      rcases f a i with _ | b <;> rcases g a' i with _ | b' <;> intro hb <;> cases hb
      · exact .none
      · have e : k + 1 + l.length = k + (i :: l).length := by simp only [List.length_cons]; omega
        rw [← e]
        refine foldlM_rel_graded_list l (k + 1) (fun j hj c c' hc => ?_) _ _ ‹_›
        have e' : k + 1 + j = k + (j + 1) := by omega
        rw [e'] at hc ⊢
        exact h (j + 1) (by simp only [List.length_cons]; omega) c c' hc

/-- **The counted loop over a list, graded forward form.** -/
theorem foldlM_rel_graded_list_fwd {α : Type u} {α' : Type v} {β : Type w}
    {R : ℕ → α → α' → Prop} {f : α → β → Option α} {g : α' → β → Option α'} :
    ∀ (l : List β) (k : ℕ), (∀ (j : ℕ) (hj : j < l.length), ∀ a a' b, R (k + j) a a' →
        f a l[j] = some b → ∃ b', g a' l[j] = some b' ∧ R (k + j + 1) b b') →
      ∀ a a' b, R k a a' → l.foldlM f a = some b →
        ∃ b', l.foldlM g a' = some b' ∧ R (k + l.length) b b'
  | [], _, _, _, a', _, hr, h => by cases h; exact ⟨a', rfl, hr⟩
  | i :: l, k, h, a, a', b, hr, hf => by
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hf ⊢
      obtain ⟨c, hc, hf⟩ := hf
      obtain ⟨c', hc', hr'⟩ := h 0 (by simp) a a' c hr hc
      have e : k + 1 + l.length = k + (i :: l).length := by simp only [List.length_cons]; omega
      rw [← e]
      obtain ⟨b', hb', hrb⟩ := foldlM_rel_graded_list_fwd l (k + 1) (fun j hj d d' e hd he => by
        have e' : k + 1 + j = k + (j + 1) := by omega
        rw [e'] at hd ⊢
        exact h (j + 1) (by simp only [List.length_cons]; omega) d d' e hd he) c c' b hr' hf
      exact ⟨b', ⟨c', hc', hb'⟩, hrb⟩

/-- **The counted loop, graded bisimulation form.** Two `Option` folds over the trip
    indices `s, …, s + n - 1` whose step at index `i` sends `R i`-related carriers to
    `Option.Rel (R (i + 1))`-related results send `R s`-related initial carriers to
    `Option.Rel (R (s + n))`-related results. The family `R` carries invariants whose
    bound depends on the trip index, such as `|acc| ≤ B * i`. -/
theorem foldlM_rel_graded {α : Type u} {α' : Type v} {R : ℕ → α → α' → Prop}
    {f : α → ℕ → Option α} {g : α' → ℕ → Option α'} (s n : ℕ)
    (h : ∀ i, s ≤ i → i < s + n → ∀ a a', R i a a' →
      Option.Rel (R (i + 1)) (f a i) (g a' i)) :
    ∀ a a', R s a a' →
      Option.Rel (R (s + n)) ((List.range' s n).foldlM f a) ((List.range' s n).foldlM g a') := by
  intro a a' hr
  have := foldlM_rel_graded_list (R := R) (f := f) (g := g) (List.range' s n) s
    (fun j hj => by
      rw [List.length_range'] at hj
      rw [List.getElem_range', Nat.one_mul]
      exact h (s + j) (by omega) (by omega)) a a' hr
  rwa [List.length_range'] at this

/-- **The counted loop, graded forward form.** -/
theorem foldlM_rel_graded_fwd {α : Type u} {α' : Type v} {R : ℕ → α → α' → Prop}
    {f : α → ℕ → Option α} {g : α' → ℕ → Option α'} (s n : ℕ)
    (h : ∀ i, s ≤ i → i < s + n → ∀ a a' b, R i a a' → f a i = some b →
      ∃ b', g a' i = some b' ∧ R (i + 1) b b') :
    ∀ a a' b, R s a a' → (List.range' s n).foldlM f a = some b →
      ∃ b', (List.range' s n).foldlM g a' = some b' ∧ R (s + n) b b' := by
  intro a a' b hr hb
  have := foldlM_rel_graded_list_fwd (R := R) (f := f) (g := g) (List.range' s n) s
    (fun j hj => by
      rw [List.length_range'] at hj
      rw [List.getElem_range', Nat.one_mul]
      exact h (s + j) (by omega) (by omega)) a a' b hr hb
  rwa [List.length_range'] at this

/-- A fold that adds a term bounded by `B` at each of `n` steps is related to itself under
    the graded relation `R j a w := w = a ∧ a ≤ B * j`; the result is bounded by `B * n`. -/
theorem foldlM_add_bounded_rel (t : ℕ → ℕ) (B n : ℕ) (ht : ∀ i, t i ≤ B) :
    Option.Rel (fun a w => w = a ∧ a ≤ B * n)
      ((List.range n).foldlM (fun a i => some (a + t i)) 0)
      ((List.range n).foldlM (fun a i => some (a + t i)) 0) := by
  rw [List.range_eq_range']
  have := foldlM_rel_graded (R := fun j a w => w = a ∧ a ≤ B * j)
    (f := fun a i => some (a + t i)) (g := fun a i => some (a + t i)) 0 n
    (fun i _ _ a a' ⟨he, hle⟩ => .some ⟨by rw [he], by
      rw [Nat.mul_succ]; have := ht i; omega⟩) 0 0 ⟨rfl, Nat.zero_le _⟩
  rwa [Nat.zero_add] at this

/-- **The counted loop, bisimulation form.** Two `Option` folds over the same list whose
    steps send `R`-related carriers to `Option.Rel R`-related results, at every index of
    the list, send `R`-related initial carriers to `Option.Rel R`-related results. -/
theorem foldlM_rel {α : Type u} {α' : Type v} {β : Type w} {R : α → α' → Prop}
    {f : α → β → Option α} {g : α' → β → Option α'} :
    ∀ (l : List β), (∀ i ∈ l, ∀ a a', R a a' → Option.Rel R (f a i) (g a' i)) →
      ∀ a a', R a a' → Option.Rel R (l.foldlM f a) (l.foldlM g a') := fun l h =>
  foldlM_rel_graded_list (R := fun _ => R) l 0 fun _ hj => h _ (List.getElem_mem hj)

/-- **The counted loop, forward form.** Two `Option` folds over the same list, where each
    successful left step from an `R`-related carrier has a successful right step to an
    `R`-related carrier, at every index of the list: a successful left fold from
    `R`-related initial carriers has a successful right fold to an `R`-related result. -/
theorem foldlM_rel_fwd {α : Type u} {α' : Type v} {β : Type w} {R : α → α' → Prop}
    {f : α → β → Option α} {g : α' → β → Option α'} :
    ∀ (l : List β),
      (∀ i ∈ l, ∀ a a' b, R a a' → f a i = some b → ∃ b', g a' i = some b' ∧ R b b') →
      ∀ a a' b, R a a' → l.foldlM f a = some b → ∃ b', l.foldlM g a' = some b' ∧ R b b' :=
  fun l h => foldlM_rel_graded_list_fwd (R := fun _ => R) l 0 fun _ hj => h _ (List.getElem_mem hj)

/-! ## 3. The branch -/

/-- **The branch, bisimulation form.** Equal conditions and related arms give related
    results. -/
theorem ite_rel {α : Type u} {β : Type v} {S : α → β → Prop} {c c' : Bool} (hc : c = c')
    {x y : Option α} {x' y' : Option β} (ht : Option.Rel S x x') (he : Option.Rel S y y') :
    Option.Rel S (if c then x else y) (if c' then x' else y') := by
  subst hc
  cases c
  · exact he
  · exact ht

/-- **The branch, forward form.** -/
theorem ite_rel_fwd {α : Type u} {β : Type v} {S : α → β → Prop} {c c' : Bool}
    (hc : c = c') {x y : Option α} {x' y' : Option β}
    (ht : ∀ b, x = some b → ∃ b', x' = some b' ∧ S b b')
    (he : ∀ b, y = some b → ∃ b', y' = some b' ∧ S b b') :
    ∀ b, (if c then x else y) = some b → ∃ b', (if c' then x' else y') = some b' ∧ S b b' := by
  subst hc
  cases c
  · exact he
  · exact ht

end Generic

/-! ## 4. The exit-flag loop -/

section While

variable {d d' : Dialect.{0, 0}} [TyDenote d.Ty] [HasBoolBit d] [TyDenote d'.Ty]
  [HasBoolBit d']

/-- **The exit-flag loop, bisimulation form.** Two exit-flag iterations whose bodies send
    `R`-related carriers to results that both fail, or both succeed with flags reading as
    the same `Bool` and `R`-related next carriers, send `R`-related carriers to
    `Option.Rel R`-related results at every fuel. -/
theorem whileIter_rel {cs : List d.Ty} {cs' : List d'.Ty}
    {R : Valuation cs → Valuation cs' → Prop}
    {step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs))}
    {step' : Valuation cs' → Option (Valuation (HasBitType.bit (d := d') :: cs'))}
    (hs : ∀ a a', R a a' → Option.Rel (fun r r' => R r.tail r'.tail ∧
      HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head)
      (step a) (step' a')) :
    ∀ (n : Nat) (a : Valuation cs) (a' : Valuation cs'), R a a' →
      Option.Rel R (whileIter step n a) (whileIter step' n a')
  | 0, _, _, _ => .none
  | n + 1, a, a', hr => by
      simp only [whileIter]
      refine bind_rel (hs a a' hr) fun r r' ⟨ht, hb⟩ => ?_
      rw [hb]
      exact ite_rel rfl (whileIter_rel hs n _ _ ht) (.some ht)

/-- **The exit-flag loop, graded bisimulation form.** The relation is a family
    `R : ℕ → …` indexed by the iteration count. Two exit-flag iterations whose bodies send
    `R j`-related carriers to results that both fail, or both succeed with flags reading as
    the same `Bool` and `R (j + 1)`-related next carriers, send `R j`-related carriers at
    fuel `n` to results related by `R m` for some exit grade `m` with `j < m ≤ j + n`. -/
theorem whileIter_rel_graded {cs : List d.Ty} {cs' : List d'.Ty}
    {R : ℕ → Valuation cs → Valuation cs' → Prop}
    {step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs))}
    {step' : Valuation cs' → Option (Valuation (HasBitType.bit (d := d') :: cs'))}
    (hs : ∀ j a a', R j a a' → Option.Rel (fun r r' => R (j + 1) r.tail r'.tail ∧
      HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head)
      (step a) (step' a')) :
    ∀ (n j : Nat) (a : Valuation cs) (a' : Valuation cs'), R j a a' →
      Option.Rel (fun b b' => ∃ m, j < m ∧ m ≤ j + n ∧ R m b b')
        (whileIter step n a) (whileIter step' n a')
  | 0, _, _, _, _ => .none
  | n + 1, j, a, a', hr => by
      simp only [whileIter]
      refine bind_rel (hs j a a' hr) fun r r' ⟨ht, hb⟩ => ?_
      rw [hb]
      refine ite_rel rfl ?_ (.some ⟨j + 1, by omega, by omega, ht⟩)
      have hw := whileIter_rel_graded hs n (j + 1) _ _ ht
      revert hw
      generalize whileIter step n r.tail = o
      generalize whileIter step' n r'.tail = o'
      intro hw
      cases hw with
      | none => exact .none
      | some h =>
        obtain ⟨m, h1, h2, h3⟩ := h
        exact .some ⟨m, by omega, by omega, h3⟩

/-- **The exit-flag loop, forward form.** -/
theorem whileIter_rel_fwd {cs : List d.Ty} {cs' : List d'.Ty}
    {R : Valuation cs → Valuation cs' → Prop}
    {step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs))}
    {step' : Valuation cs' → Option (Valuation (HasBitType.bit (d := d') :: cs'))}
    (hs : ∀ a a' r, R a a' → step a = some r → ∃ r', step' a' = some r' ∧ R r.tail r'.tail ∧
      HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head) :
    ∀ (n : Nat) (a : Valuation cs) (a' : Valuation cs') (b : Valuation cs), R a a' →
      whileIter step n a = some b → ∃ b', whileIter step' n a' = some b' ∧ R b b'
  | 0, _, _, _, _, h => by cases h
  | n + 1, a, a', b, hr, h => by
      simp only [whileIter] at h ⊢
      refine bind_rel_fwd (R := fun r r' => R r.tail r'.tail ∧
        HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head)
        (fun r hr' => hs a a' r hr hr') (fun r r' c ⟨ht, hb⟩ => ?_) b h
      rw [hb]
      exact ite_rel_fwd rfl (fun b => whileIter_rel_fwd hs n _ _ b ht)
        (fun b hb => by obtain rfl := Option.some.inj hb; exact ⟨_, rfl, ht⟩) c

/-- **The exit-flag loop, forward form from a fuel to a larger one.** -/
theorem whileIter_fwd_le {cs : List d.Ty} {cs' : List d'.Ty}
    {R : Valuation cs → Valuation cs' → Prop}
    {step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs))}
    {step' : Valuation cs' → Option (Valuation (HasBitType.bit (d := d') :: cs'))}
    (hs : ∀ a a' r, R a a' → step a = some r → ∃ r', step' a' = some r' ∧ R r.tail r'.tail ∧
      HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head) :
    ∀ (n m : Nat), n ≤ m → ∀ (a : Valuation cs) (a' : Valuation cs') (b : Valuation cs),
      R a a' → whileIter step n a = some b → ∃ b', whileIter step' m a' = some b' ∧ R b b'
  | 0, _, _, _, _, _, _, h => by cases h
  | n + 1, 0, hle, _, _, _, _, _ => by omega
  | n + 1, m + 1, hle, a, a', b, hr, h => by
      simp only [whileIter] at h ⊢
      refine bind_rel_fwd (R := fun r r' => R r.tail r'.tail ∧
        HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head)
        (fun r hr' => hs a a' r hr hr') (fun r r' c ⟨ht, hb⟩ => ?_) b h
      rw [hb]
      exact ite_rel_fwd rfl (fun b => whileIter_fwd_le hs n m (by omega) _ _ b ht)
        (fun b hb => by obtain rfl := Option.some.inj hb; exact ⟨_, rfl, ht⟩) c

end While

/-! ## 5. The leak writer -/

section Leak

variable {d d' : Dialect.{0, 0}} [TyDenote d.Ty] [TyDenote d'.Ty]

/-- **The counted loop of the leak writer, bisimulation form.** Two runs `forIterLeak` over
    the same indices whose steps send `R`-related carriers to results that both fail, or
    both succeed with `R`-related carriers and equal events, do the same from `R`-related
    initial carriers. -/
theorem forIterLeak_rel_bisim {cs : List d.Ty} {cs' : List d'.Ty}
    {R : Valuation cs → Valuation cs' → Prop}
    {step : Nat → Valuation cs → Option (Valuation cs × List CTLeak)}
    {step' : Nat → Valuation cs' → Option (Valuation cs' × List CTLeak)} :
    ∀ (l : List Nat), (∀ i ∈ l, ∀ a a', R a a' →
      Option.Rel (fun r r' => R r.1 r'.1 ∧ r.2 = r'.2) (step i a) (step' i a')) →
      ∀ a a', R a a' → Option.Rel (fun r r' => R r.1 r'.1 ∧ r.2 = r'.2)
        (forIterLeak step l a) (forIterLeak step' l a')
  | [], _, _, _, h => .some ⟨h, rfl⟩
  | i :: l, h, a, a', hr => by
      simp only [forIterLeak]
      have hi := h i (List.mem_cons_self ..) a a' hr
      revert hi
      rcases step i a with _ | r <;> rcases step' i a' with _ | r' <;> intro hb <;> cases hb
      · exact .none
      · rename_i hrr
        have ih := forIterLeak_rel_bisim l (fun j hj => h j (List.mem_cons_of_mem _ hj))
          r.1 r'.1 hrr.1
        revert ih
        simp only [Option.bind_some]
        rcases forIterLeak step l r.1 with _ | q <;> rcases forIterLeak step' l r'.1 with _ | q'
          <;> intro hq <;> cases hq
        · exact .none
        · rename_i hqq
          exact .some ⟨hqq.1, by simp only [hrr.2, hqq.2]⟩

/-- **The counted loop of the leak writer, forward form.** -/
theorem forIterLeak_rel_fwd {cs : List d.Ty} {cs' : List d'.Ty}
    {R : Valuation cs → Valuation cs' → Prop}
    {step : Nat → Valuation cs → Option (Valuation cs × List CTLeak)}
    {step' : Nat → Valuation cs' → Option (Valuation cs' × List CTLeak)} :
    ∀ (l : List Nat), (∀ i ∈ l, ∀ a a' r, R a a' → step i a = some r →
      ∃ r', step' i a' = some r' ∧ R r.1 r'.1 ∧ r.2 = r'.2) →
      ∀ a a' r, R a a' → forIterLeak step l a = some r →
        ∃ r', forIterLeak step' l a' = some r' ∧ R r.1 r'.1 ∧ r.2 = r'.2
  | [], _, _, a', _, hr, h => by cases h; exact ⟨_, rfl, hr, rfl⟩
  | i :: l, h, a, a', r, hr, hf => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf ⊢
      obtain ⟨c, hc, q, hq, rfl⟩ := hf
      obtain ⟨c', hc', hr', he⟩ := h i (List.mem_cons_self ..) a a' c hr hc
      obtain ⟨q', hq', hrq, heq⟩ :=
        forIterLeak_rel_fwd l (fun j hj => h j (List.mem_cons_of_mem _ hj)) c.1 c'.1 q hr' hq
      exact ⟨_, ⟨c', hc', q', hq', rfl⟩, hrq, by simp only [he, heq]⟩

/-- **A counted loop of the leak writer over a pure step.** When each step sends the
    embedding `E a` of a carrier to `E (g i a)` with the events `lk i a`, the run from
    `E a` ends in the embedding of the pure fold, with the events `L l a` of any `L` that
    unfolds as `lk` followed by `L` of the next carrier. -/
theorem forIterLeak_pure {cs : List d.Ty} {α : Type} (E : α → Valuation cs)
    (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (g : Nat → α → α) (lk : Nat → α → List CTLeak) (L : List Nat → α → List CTLeak)
    (hL0 : ∀ a, L [] a = []) (hL : ∀ i l a, L (i :: l) a = lk i a ++ L l (g i a))
    (hf : ∀ i a, step i (E a) = some (E (g i a), lk i a)) :
    ∀ (l : List Nat) (a : α),
      forIterLeak step l (E a) = some (E (l.foldl (fun x i => g i x) a), L l a)
  | [], a => by rw [hL0]; rfl
  | i :: l, a => by
      simp only [forIterLeak, hf, Option.bind_some, forIterLeak_pure E step g lk L hL0 hL hf l,
        Option.map_some, List.foldl_cons, hL]

variable [HasBoolBit d] [HasBoolBit d']

/-- **The exit-flag loop of the leak writer, bisimulation form.** -/
theorem whileIterLeak_rel_bisim {cs : List d.Ty} {cs' : List d'.Ty}
    {R : Valuation cs → Valuation cs' → Prop}
    {step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak)}
    {step' : Valuation cs' →
      Option (Valuation (HasBitType.bit (d := d') :: cs') × List CTLeak)}
    (hs : ∀ a a', R a a' → Option.Rel (fun r r' => R r.1.tail r'.1.tail ∧
      HasBoolBit.toBool (d := d) r.1.head = HasBoolBit.toBool (d := d') r'.1.head ∧
      r.2 = r'.2) (step a) (step' a')) :
    ∀ (n : Nat) (a : Valuation cs) (a' : Valuation cs'), R a a' →
      Option.Rel (fun r r' => R r.1 r'.1 ∧ r.2 = r'.2)
        (whileIterLeak step n a) (whileIterLeak step' n a')
  | 0, _, _, _ => .none
  | n + 1, a, a', hr => by
      simp only [whileIterLeak]
      have hi := hs a a' hr
      revert hi
      rcases step a with _ | r <;> rcases step' a' with _ | r' <;> intro hb <;> cases hb
      · exact .none
      · rename_i hrr
        obtain ⟨ht, hb, he⟩ := hrr
        simp only [Option.bind_some, hb, he]
        split
        · have ih := whileIterLeak_rel_bisim hs n _ _ ht
          revert ih
          rcases whileIterLeak step n r.1.tail with _ | q <;>
            rcases whileIterLeak step' n r'.1.tail with _ | q' <;> intro hq <;> cases hq
          · exact .none
          · rename_i hqq
            exact .some ⟨hqq.1, by simp only [hqq.2]⟩
        · exact .some ⟨ht, rfl⟩

/-- **The exit-flag loop of the leak writer, forward form.** -/
theorem whileIterLeak_rel_fwd {cs : List d.Ty} {cs' : List d'.Ty}
    {R : Valuation cs → Valuation cs' → Prop}
    {step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak)}
    {step' : Valuation cs' →
      Option (Valuation (HasBitType.bit (d := d') :: cs') × List CTLeak)}
    (hs : ∀ a a' r, R a a' → step a = some r → ∃ r', step' a' = some r' ∧
      R r.1.tail r'.1.tail ∧
      HasBoolBit.toBool (d := d) r.1.head = HasBoolBit.toBool (d := d') r'.1.head ∧
      r.2 = r'.2) :
    ∀ (n : Nat) (a : Valuation cs) (a' : Valuation cs') r, R a a' →
      whileIterLeak step n a = some r →
        ∃ r', whileIterLeak step' n a' = some r' ∧ R r.1 r'.1 ∧ r.2 = r'.2
  | 0, _, _, _, _, h => by cases h
  | n + 1, a, a', r, hr, h => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      obtain ⟨c', hc', ht, hb, he⟩ := hs a a' c hr hc
      simp only [whileIterLeak, hc', Option.bind_some]
      rw [← hb, ← he]
      split at h
      · rw [ite_eq_left ‹_›]
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hrq, heq⟩ := whileIterLeak_rel_fwd hs n _ _ q ht hq
        exact ⟨(q'.1, c.2 ++ .branch true :: q'.2), by rw [hq', Option.map_some], hrq,
          by simp only [heq]⟩
      · rw [ite_eq_right ‹_›]
        cases h
        exact ⟨_, rfl, ht, rfl⟩

end Leak

/-! ## 6. The program-level congruence of the region constructors -/

section Program

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option] [CallDenote d] [DialectSignature d']
  [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d'] [DialectDenoteM d' Option] [CallDenote d']

/-- **The counted-loop constructor, graded bisimulation form.** The relation of carried
    tuples is a family `Rc : ℕ → …` indexed by the trip index. Two counted loops over
    related valuations, with equal trip counts `n`, `Rc 0`-related initial tuples, bodies
    that send `Rc i`-related tuples to `Option.Rel (Rc (i + 1))`-related results at every
    trip index `i < n`, and continuations that send `Rc n`-related tuples to `S`-related
    results, denote `S`-related results. The fuels of the two sides may differ. -/
theorem denote_forLoop_rel_graded {Γ : Ctxt d} {cs ts : List d.Ty} {Γ' : Ctxt d'}
    {cs' ts' : List d'.Ty} (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rc : ℕ → Valuation cs → Valuation cs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (count' : Var Γ' (HasWord64.word (d := d'))) (inits' : HVector (fun t => Var Γ' t) cs')
    (body' : NFProg d' (cs' ++ HasWord64.word (d := d') :: Γ') cs')
    (k' : NFProg d' (cs' ++ Γ') ts')
    (hcount : ∀ V V', RΓ V V' →
      HasWord64.toNat (d := d) (count.lookup V) = HasWord64.toNat (d := d') (count'.lookup V'))
    (hinits : ∀ V V', RΓ V V' → Rc 0 (Expr.lookupArgs inits V) (Expr.lookupArgs inits' V'))
    (hbody : ∀ V V', RΓ V V' → ∀ (i : Nat), i < HasWord64.toNat (d := d) (count.lookup V) →
      ∀ a a', Rc i a a' → Option.Rel (Rc (i + 1))
        (body.denote fuel (hvAppend a (.cons (HasWord64.ofNat (d := d) i) V)))
        (body'.denote fuel' (hvAppend a' (.cons (HasWord64.ofNat (d := d') i) V'))))
    (hk : ∀ V V', RΓ V V' → ∀ a a', Rc (HasWord64.toNat (d := d) (count.lookup V)) a a' →
      Option.Rel S (k.denote fuel (hvAppend a V)) (k'.denote fuel' (hvAppend a' V')))
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') :
    Option.Rel S ((NFProg.forLoop count inits body k).denote fuel V)
      ((NFProg.forLoop count' inits' body' k').denote fuel' V') := by
  rw [denote_forLoop, denote_forLoop, ← hcount V V' hV, List.range_eq_range']
  refine bind_rel (foldlM_rel_graded 0 _ (fun i _ hi => hbody V V' hV i (by omega)) _ _
    (hinits V V' hV)) fun a a' h => hk V V' hV a a' ?_
  rwa [Nat.zero_add] at h

/-- **The counted-loop constructor, graded forward form.** -/
theorem denote_forLoop_rel_graded_fwd {Γ : Ctxt d} {cs ts : List d.Ty} {Γ' : Ctxt d'}
    {cs' ts' : List d'.Ty} (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rc : ℕ → Valuation cs → Valuation cs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (count' : Var Γ' (HasWord64.word (d := d'))) (inits' : HVector (fun t => Var Γ' t) cs')
    (body' : NFProg d' (cs' ++ HasWord64.word (d := d') :: Γ') cs')
    (k' : NFProg d' (cs' ++ Γ') ts')
    (hcount : ∀ V V', RΓ V V' →
      HasWord64.toNat (d := d) (count.lookup V) = HasWord64.toNat (d := d') (count'.lookup V'))
    (hinits : ∀ V V', RΓ V V' → Rc 0 (Expr.lookupArgs inits V) (Expr.lookupArgs inits' V'))
    (hbody : ∀ V V', RΓ V V' → ∀ (i : Nat), i < HasWord64.toNat (d := d) (count.lookup V) →
      ∀ a a' b, Rc i a a' →
      body.denote fuel (hvAppend a (.cons (HasWord64.ofNat (d := d) i) V)) = some b →
      ∃ b', body'.denote fuel' (hvAppend a' (.cons (HasWord64.ofNat (d := d') i) V')) =
        some b' ∧ Rc (i + 1) b b')
    (hk : ∀ V V', RΓ V V' → ∀ a a' b, Rc (HasWord64.toNat (d := d) (count.lookup V)) a a' →
      k.denote fuel (hvAppend a V) = some b →
      ∃ b', k'.denote fuel' (hvAppend a' V') = some b' ∧ S b b')
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') (out : Valuation ts)
    (h : (NFProg.forLoop count inits body k).denote fuel V = some out) :
    ∃ out', (NFProg.forLoop count' inits' body' k').denote fuel' V' = some out' ∧
      S out out' := by
  rw [denote_forLoop, List.range_eq_range'] at h
  rw [denote_forLoop, ← hcount V V' hV, List.range_eq_range']
  refine bind_rel_fwd (fun a ha => foldlM_rel_graded_fwd 0 _
    (fun i _ hi => hbody V V' hV i (by omega)) _ _ a (hinits V V' hV) ha)
    (fun a a' b hr => hk V V' hV a a' b ?_) out h
  rwa [Nat.zero_add] at hr

/-- **The counted-loop constructor, bisimulation form.** Two counted loops over related
    valuations, with equal trip counts, related initial tuples, bodies that preserve the
    relation `Rc` of carried tuples at every trip index, and continuations that send
    `Rc`-related tuples to `S`-related results, denote `S`-related results. The fuels of the
    two sides may differ. -/
theorem denote_forLoop_rel {Γ : Ctxt d} {cs ts : List d.Ty} {Γ' : Ctxt d'}
    {cs' ts' : List d'.Ty} (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rc : Valuation cs → Valuation cs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (count' : Var Γ' (HasWord64.word (d := d'))) (inits' : HVector (fun t => Var Γ' t) cs')
    (body' : NFProg d' (cs' ++ HasWord64.word (d := d') :: Γ') cs')
    (k' : NFProg d' (cs' ++ Γ') ts')
    (hcount : ∀ V V', RΓ V V' →
      HasWord64.toNat (d := d) (count.lookup V) = HasWord64.toNat (d := d') (count'.lookup V'))
    (hinits : ∀ V V', RΓ V V' → Rc (Expr.lookupArgs inits V) (Expr.lookupArgs inits' V'))
    (hbody : ∀ V V', RΓ V V' → ∀ (i : Nat) a a', Rc a a' → Option.Rel Rc
      (body.denote fuel (hvAppend a (.cons (HasWord64.ofNat (d := d) i) V)))
      (body'.denote fuel' (hvAppend a' (.cons (HasWord64.ofNat (d := d') i) V'))))
    (hk : ∀ V V', RΓ V V' → ∀ a a', Rc a a' →
      Option.Rel S (k.denote fuel (hvAppend a V)) (k'.denote fuel' (hvAppend a' V')))
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') :
    Option.Rel S ((NFProg.forLoop count inits body k).denote fuel V)
      ((NFProg.forLoop count' inits' body' k').denote fuel' V') :=
  denote_forLoop_rel_graded (Rc := fun _ => Rc) fuel fuel' count inits body k count' inits'
    body' k' hcount hinits (fun V V' hV i _ => hbody V V' hV i) hk V V' hV

/-- **The counted-loop constructor, forward form.** -/
theorem denote_forLoop_rel_fwd {Γ : Ctxt d} {cs ts : List d.Ty} {Γ' : Ctxt d'}
    {cs' ts' : List d'.Ty}
    (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rc : Valuation cs → Valuation cs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (count' : Var Γ' (HasWord64.word (d := d'))) (inits' : HVector (fun t => Var Γ' t) cs')
    (body' : NFProg d' (cs' ++ HasWord64.word (d := d') :: Γ') cs')
    (k' : NFProg d' (cs' ++ Γ') ts')
    (hcount : ∀ V V', RΓ V V' →
      HasWord64.toNat (d := d) (count.lookup V) = HasWord64.toNat (d := d') (count'.lookup V'))
    (hinits : ∀ V V', RΓ V V' → Rc (Expr.lookupArgs inits V) (Expr.lookupArgs inits' V'))
    (hbody : ∀ V V', RΓ V V' → ∀ (i : Nat) a a' b, Rc a a' →
      body.denote fuel (hvAppend a (.cons (HasWord64.ofNat (d := d) i) V)) = some b →
      ∃ b', body'.denote fuel' (hvAppend a' (.cons (HasWord64.ofNat (d := d') i) V')) =
        some b' ∧ Rc b b')
    (hk : ∀ V V', RΓ V V' → ∀ a a' b, Rc a a' → k.denote fuel (hvAppend a V) = some b →
      ∃ b', k'.denote fuel' (hvAppend a' V') = some b' ∧ S b b')
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') (out : Valuation ts)
    (h : (NFProg.forLoop count inits body k).denote fuel V = some out) :
    ∃ out', (NFProg.forLoop count' inits' body' k').denote fuel' V' = some out' ∧
      S out out' :=
  denote_forLoop_rel_graded_fwd (Rc := fun _ => Rc) fuel fuel' count inits body k count'
    inits' body' k' hcount hinits (fun V V' hV i _ => hbody V V' hV i) hk V V' hV out h

/-- **The branch constructor, bisimulation form.** Two branches over related valuations,
    with conditions reading as the same `Bool`, arms with `Rr`-related results and
    continuations that send `Rr`-related results to `S`-related results, denote
    `S`-related results. -/
theorem denote_ifThenElse_rel {Γ : Ctxt d} {rs ts : List d.Ty} {Γ' : Ctxt d'}
    {rs' ts' : List d'.Ty}
    (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rr : Valuation rs → Valuation rs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts)
    (cond' : Var Γ' (HasBitType.bit (d := d'))) (thn' els' : NFProg d' Γ' rs')
    (k' : NFProg d' (rs' ++ Γ') ts')
    (hcond : ∀ V V', RΓ V V' →
      HasBoolBit.toBool (d := d) (cond.lookup V) = HasBoolBit.toBool (d := d') (cond'.lookup V'))
    (hthn : ∀ V V', RΓ V V' → Option.Rel Rr (thn.denote fuel V) (thn'.denote fuel' V'))
    (hels : ∀ V V', RΓ V V' → Option.Rel Rr (els.denote fuel V) (els'.denote fuel' V'))
    (hk : ∀ V V', RΓ V V' → ∀ a a', Rr a a' →
      Option.Rel S (k.denote fuel (hvAppend a V)) (k'.denote fuel' (hvAppend a' V')))
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') :
    Option.Rel S ((NFProg.ifThenElse cond thn els k).denote fuel V)
      ((NFProg.ifThenElse cond' thn' els' k').denote fuel' V') := by
  rw [denote_ifThenElse, denote_ifThenElse]
  exact bind_rel (ite_rel (hcond V V' hV) (hthn V V' hV) (hels V V' hV)) (hk V V' hV)

/-- **The branch constructor, forward form.** -/
theorem denote_ifThenElse_rel_fwd {Γ : Ctxt d} {rs ts : List d.Ty} {Γ' : Ctxt d'}
    {rs' ts' : List d'.Ty}
    (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rr : Valuation rs → Valuation rs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts)
    (cond' : Var Γ' (HasBitType.bit (d := d'))) (thn' els' : NFProg d' Γ' rs')
    (k' : NFProg d' (rs' ++ Γ') ts')
    (hcond : ∀ V V', RΓ V V' →
      HasBoolBit.toBool (d := d) (cond.lookup V) = HasBoolBit.toBool (d := d') (cond'.lookup V'))
    (hthn : ∀ V V', RΓ V V' → ∀ b, thn.denote fuel V = some b →
      ∃ b', thn'.denote fuel' V' = some b' ∧ Rr b b')
    (hels : ∀ V V', RΓ V V' → ∀ b, els.denote fuel V = some b →
      ∃ b', els'.denote fuel' V' = some b' ∧ Rr b b')
    (hk : ∀ V V', RΓ V V' → ∀ a a' b, Rr a a' → k.denote fuel (hvAppend a V) = some b →
      ∃ b', k'.denote fuel' (hvAppend a' V') = some b' ∧ S b b')
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') (out : Valuation ts)
    (h : (NFProg.ifThenElse cond thn els k).denote fuel V = some out) :
    ∃ out', (NFProg.ifThenElse cond' thn' els' k').denote fuel' V' = some out' ∧
      S out out' := by
  rw [denote_ifThenElse] at h
  rw [denote_ifThenElse]
  exact bind_rel_fwd (ite_rel_fwd (hcond V V' hV) (hthn V V' hV) (hels V V' hV))
    (hk V V' hV) out h

/-- **The exit-flag-loop constructor, bisimulation form.** Two exit-flag loops over related
    valuations, at the same fuel, with related initial tuples, bodies that send
    `Rc`-related tuples to results with flags reading as the same `Bool` and `Rc`-related
    next tuples, and continuations that send `Rc`-related tuples to `S`-related results,
    denote `S`-related results. -/
theorem denote_whileLoop_rel {Γ : Ctxt d} {cs ts : List d.Ty} {Γ' : Ctxt d'}
    {cs' ts' : List d'.Ty} (fuel : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rc : Valuation cs → Valuation cs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts)
    (inits' : HVector (fun t => Var Γ' t) cs')
    (body' : NFProg d' (cs' ++ Γ') (HasBitType.bit (d := d') :: cs'))
    (k' : NFProg d' (cs' ++ Γ') ts')
    (hinits : ∀ V V', RΓ V V' → Rc (Expr.lookupArgs inits V) (Expr.lookupArgs inits' V'))
    (hbody : ∀ V V', RΓ V V' → ∀ a a', Rc a a' → Option.Rel (fun r r' => Rc r.tail r'.tail ∧
      HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head)
      (body.denote fuel (hvAppend a V)) (body'.denote fuel (hvAppend a' V')))
    (hk : ∀ V V', RΓ V V' → ∀ a a', Rc a a' →
      Option.Rel S (k.denote fuel (hvAppend a V)) (k'.denote fuel (hvAppend a' V')))
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') :
    Option.Rel S ((NFProg.whileLoop inits body k).denote fuel V)
      ((NFProg.whileLoop inits' body' k').denote fuel V') := by
  rw [denote_whileLoop, denote_whileLoop]
  exact bind_rel (whileIter_rel (hbody V V' hV) fuel _ _ (hinits V V' hV)) (hk V V' hV)

/-- **The exit-flag-loop constructor, forward form.** -/
theorem denote_whileLoop_rel_fwd {Γ : Ctxt d} {cs ts : List d.Ty} {Γ' : Ctxt d'}
    {cs' ts' : List d'.Ty}
    (fuel : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Rc : Valuation cs → Valuation cs' → Prop}
    {S : Valuation ts → Valuation ts' → Prop}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts)
    (inits' : HVector (fun t => Var Γ' t) cs')
    (body' : NFProg d' (cs' ++ Γ') (HasBitType.bit (d := d') :: cs'))
    (k' : NFProg d' (cs' ++ Γ') ts')
    (hinits : ∀ V V', RΓ V V' → Rc (Expr.lookupArgs inits V) (Expr.lookupArgs inits' V'))
    (hbody : ∀ V V', RΓ V V' → ∀ a a' r, Rc a a' → body.denote fuel (hvAppend a V) = some r →
      ∃ r', body'.denote fuel (hvAppend a' V') = some r' ∧ Rc r.tail r'.tail ∧
        HasBoolBit.toBool (d := d) r.head = HasBoolBit.toBool (d := d') r'.head)
    (hk : ∀ V V', RΓ V V' → ∀ a a' b, Rc a a' → k.denote fuel (hvAppend a V) = some b →
      ∃ b', k'.denote fuel (hvAppend a' V') = some b' ∧ S b b')
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') (out : Valuation ts)
    (h : (NFProg.whileLoop inits body k).denote fuel V = some out) :
    ∃ out', (NFProg.whileLoop inits' body' k').denote fuel V' = some out' ∧ S out out' := by
  rw [denote_whileLoop] at h
  rw [denote_whileLoop]
  exact bind_rel_fwd (fun a ha => whileIter_rel_fwd (hbody V V' hV) fuel _ _ a
    (hinits V V' hV) ha) (hk V V' hV) out h

end Program

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
