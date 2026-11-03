/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

@[expose] public section

set_option autoImplicit false

/-!
# The obligation check on affine indices

The index check `IdxInvCheck.idxInvCheckB` discharges an index obligation of a block by
`oblsOk`, which reads, among others, the affine form `affOf` of the index with the upper
bound `affHi` of its atoms. This module proves that the obligation check is complete on
indices whose affine form is a combination with non-negative coefficients of bounded atoms:
when the upper bound `hiOf` of every atom `x` is at most `u x` and the combination of these
bounds with the constant of the form is below the length of the array, `oblsOk` accepts the
obligation. An atom is bounded by a single-term fact, or by a sum fact less the lower bounds
of the other terms, which gives the bound of a trip index `x` from `x + c ≤ b` and `c ≥ 1`
for the counter `c` of a counted loop.

## Main results

* `hiOf_le_of_mem`, `hiOf_le_of_single`, `lbOf_ge_of_mem`: a sum fact bounds `hiOf` of each
  of its terms by its bound less the lower bounds of the others; a lower-bound fact bounds
  `lbOf`.
* `hiOf_le_of_pair`: the loop-counter bound, `x + c ≤ b` and `c ≥ k` give `hiOf x ≤ b - k`.
* `affHi_le_of_bounds`: on a form with non-negative coefficients whose atoms are bounded,
  `affHi` is at most the combination of the bounds.
* `affLe_of_bounds`, `oblsOk_of_bounds`, `oblsOk_of_facts`: the affine check and the
  obligation check accept such an index.
* `ubOf_le_of_mem`, `ubOf_mem`, `ubOf_mono`, `ubSum_mono`: `ubOf` is the least bound of the
  single-term facts on a term, so it is at most the bound of the first such fact (the value
  `ubOf` read before it took the minimum) and does not grow when facts are added.
* `lbOf_cases`, `lbOf_mono`, `lbSum_mono`, `widOk_mono`: the lower bounds and the width test
  are monotone in the fact list.

* `linOf_mem_linAlts`, `sumLin_mem_sumAlts`, `splitAdds_mem_splitsAlts`, `affOf_mem_affAlts`:
  the greedy forms are among the forms the readers try.
* `hiOf_mono`, `termHi_mono`, `hiNe_mono`, `lbNe_mono`, `linAlts_mono`, `affAlts_mono`: the
  bounds and the lists of forms are monotone in the fact list.
* `entails_mono`, `oblsOk_mono`, `succOk_mono`: entailment, the obligation check and the
  successor check are monotone in the fact list.
* `idxInvCheckB_of_G`: `idxInvCheckB` accepts every entry, annotation and body that the check
  with the greedy forms (`idxInvCheckBG`) accepts.

* `entails_le_of_sub`, `entails_le_of_mem`, `entails_le_of_hiOf`, `entails_ge_of_mem`,
  `entails_ne_of_mem`, `entails_w64_of_mem`, `entails_ale_of_mem`: entailment is complete on
  the facts of the list, on sub-sums of a fact over atoms, and on sums of terms bounded by
  facts containing them.
* `IdxFact.toS_setR`, `succOk_setR`: a successor fact read through a register move is its
  renaming read through the state before the move.
* `annWork_contains`, `idxAnnot_contains`: the annotation by restriction contains every
  annotation of candidates whose block-`0` facts follow from the entry facts and whose
  successor facts follow along every edge (a post-fixed point of the restriction).

With the monotonicity of `entails`, `oblsOk` and `succOk`, `idxAnnot_contains` is the half of
a greatest-fixed-point argument for the completeness of the annotation that bounds it from
below; the other half, that the worklist `annWork` stops at a fixed point within its fuel, is
not proved here.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-! ## The forms of the greedy readers among the alternatives -/

/-- **The form of `linOf` is a linear form.** -/
theorem linOf_mem_linAlts (F : List SFact) (t : STerm) : linOf F t ∈ linAlts F t := by
  fun_induction linOf F t with
  | case6 m x w k =>
      rw [linAlts]
      split_ifs <;> simp_all
  | case8 m x y hy h =>
      rw [linAlts, ite_eq_right h]
      · exact List.mem_singleton_self _
      · exact hy
  | _ => simp_all [linAlts]

/-- **The form of `sumLin` is a linear form of the sum.** -/
theorem sumLin_mem_sumAlts (F : List SFact) : ∀ ts : List STerm, sumLin F ts ∈ sumAlts F ts
  | [] => by simp [sumLin, sumAlts]
  | t :: ts => mem_altsAdd.mpr ⟨_, linOf_mem_linAlts F t, _, sumLin_mem_sumAlts F ts, rfl⟩

/-- **The form of `splitAdd` is a splitting.** -/
theorem splitAdd_mem_splitAlts (F : List SFact) (t : STerm) : splitAdd F t ∈ splitAlts F t := by
  unfold splitAdd splitAlts
  split
  · split
    · exact List.mem_cons_of_mem _
        (mem_altsAdd.mpr ⟨_, linOf_mem_linAlts F _, _, linOf_mem_linAlts F _, rfl⟩)
    · exact List.mem_cons_self
  · exact List.mem_cons_self

/-- **The form of `splitAdds` is a splitting of the list.** -/
theorem splitAdds_mem_splitsAlts (F : List SFact) :
    ∀ ts : List STerm, splitAdds F ts ∈ splitsAlts F ts
  | [] => by simp [splitAdds, splitsAlts]
  | t :: ts =>
      mem_altsAdd.mpr ⟨_, splitAdd_mem_splitAlts F t, _, splitAdds_mem_splitsAlts F ts, rfl⟩

/-- The bound of `affOf` on a product implies the bound of `affComb`. -/
theorem max_mul_max_lt {a b : Int} (h : a * b < 2 ^ 64) : max 0 a * max 0 b < 2 ^ 64 := by
  rcases le_total 0 a with ha | ha
  · rcases le_total 0 b with hb | hb
    · rwa [max_eq_right ha, max_eq_right hb]
    · rw [max_eq_left hb, mul_zero]
      norm_num
  · rw [max_eq_left ha, zero_mul]
    norm_num

/-- **The form of `affOf` is an affine form.** -/
theorem affOf_mem_affAlts (F : List SFact) (t : STerm) : affOf F t ∈ affAlts F t := by
  fun_induction affOf F t with
  | case3 m x y hw h ihx ihy =>
      obtain ⟨rfl, hlt⟩ := h
      rw [affAlts, ite_eq_left hw]
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, ihx, List.mem_filterMap.mpr
        ⟨_, ihy, ?_⟩⟩)
      simpa [affComb] using hlt
  | case4 m x y hw hn h ihx ihy =>
      obtain ⟨rfl, hle⟩ := h
      rw [affAlts, ite_eq_left hw]
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, ihx, List.mem_filterMap.mpr
        ⟨_, ihy, ?_⟩⟩)
      simp [affComb, hle]
  | case5 m x y hw _ _ h hy ihx ihy =>
      obtain ⟨rfl, hlt⟩ := h
      rw [affAlts, ite_eq_left hw]
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, ihx, List.mem_filterMap.mpr
        ⟨_, ihy, ?_⟩⟩)
      simpa [affComb, hy] using max_mul_max_lt hlt
  | case6 m x y hw _ _ h hy hx ihx ihy =>
      obtain ⟨rfl, hlt⟩ := h
      rw [affAlts, ite_eq_left hw]
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, ihx, List.mem_filterMap.mpr
        ⟨_, ihy, ?_⟩⟩)
      simpa [affComb, hy, hx] using max_mul_max_lt hlt
  | _ =>
      simp_all [affAlts]
      try split <;> simp

/-- **A sum fact bounds `hiOf`**: a fact `.le ts b` of `G` with `t ∈ ts` bounds the upper
    bound `hiOf` of `t` by `b` less the lower bounds of the other terms. -/
theorem hiOf_le_of_mem (F : List SFact) :
    ∀ {G : List SFact} {ts : List STerm} {t : STerm} {b : Nat}, SFact.le ts b ∈ G → t ∈ ts →
      hiOf F G t ≤ b - lbSum F (ts.erase t)
  | [], _, _, _, h, _ => by cases h
  | .le ts' b' :: G, ts, t, b, h, ht => by
      simp only [hiOf]
      rcases List.mem_cons.mp h with h | h
      · cases h
        rw [ite_eq_left ht]
        exact min_le_left _ _
      · have ih := hiOf_le_of_mem F h ht
        split
        · exact (min_le_right _ _).trans ih
        · exact ih
  | .ge _ _ :: G, _, _, _, h, ht => by
      simp only [hiOf]
      exact hiOf_le_of_mem F (List.mem_of_ne_of_mem (by simp) h) ht
  | .w64 _ :: G, _, _, _, h, ht => by
      simp only [hiOf]
      exact hiOf_le_of_mem F (List.mem_of_ne_of_mem (by simp) h) ht
  | .ne _ _ :: G, _, _, _, h, ht => by
      simp only [hiOf]
      exact hiOf_le_of_mem F (List.mem_of_ne_of_mem (by simp) h) ht
  | .ale a b' :: G, ts, t, b, h, ht => by
      have ih := hiOf_le_of_mem F (List.mem_of_ne_of_mem (by simp) h) ht
      simp only [hiOf]
      split
      · exact (min_le_right _ _).trans ih
      · exact ih

/-- **A single-term upper-bound fact bounds `hiOf`.** -/
theorem hiOf_le_of_single (F : List SFact) {G : List SFact} {t : STerm} {b : Nat}
    (h : SFact.le [t] b ∈ G) : hiOf F G t ≤ b := by
  have := hiOf_le_of_mem F h List.mem_cons_self
  simpa [lbSum] using this

/-- **A lower-bound fact bounds `lbOf`.** -/
theorem lbOf_ge_of_mem : ∀ {F : List SFact} {t : STerm} {k : Nat}, SFact.ge t k ∈ F →
    k ≤ lbOf F t
  | [], _, _, h => by cases h
  | .ge t' k' :: F, t, k, h => by
      simp only [lbOf]
      rcases List.mem_cons.mp h with h | h
      · cases h
        rw [ite_eq_left rfl]
        exact le_max_left _ _
      · have ih := lbOf_ge_of_mem h
        split
        · exact ih.trans (le_max_right _ _)
        · exact ih
  | .le _ _ :: F, _, _, h => by
      simp only [lbOf]
      exact lbOf_ge_of_mem (List.mem_of_ne_of_mem (by simp) h)
  | .w64 _ :: F, _, _, h => by
      simp only [lbOf]
      exact lbOf_ge_of_mem (List.mem_of_ne_of_mem (by simp) h)
  | .ne _ _ :: F, _, _, h => by
      simp only [lbOf]
      exact lbOf_ge_of_mem (List.mem_of_ne_of_mem (by simp) h)
  | .ale _ _ :: F, _, _, h => by
      simp only [lbOf]
      exact lbOf_ge_of_mem (List.mem_of_ne_of_mem (by simp) h)

/-- **The loop-counter bound**: a fact `.le [x, c] b` and a fact `.ge c k` bound the upper
    bound `hiOf` of `x` by `b - k`; for a trip index `x` and a counter `c` with `x + c` at most
    the trip count `b` and `c ≥ 1` inside the loop, `x ≤ b - 1`. -/
theorem hiOf_le_of_pair (F : List SFact) {x c : STerm} {b k : Nat}
    (hle : SFact.le [x, c] b ∈ F) (hge : SFact.ge c k ∈ F) : hiOf F F x ≤ b - k := by
  have h1 := hiOf_le_of_mem F hle List.mem_cons_self
  have h2 := lbOf_ge_of_mem hge
  simp only [List.erase_cons_head, lbSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at h1
  omega

/-- **The upper bound of a non-negative affine form with bounded atoms**: when every atom
    `p.1` of `L` has a non-negative coefficient and an upper bound `hiOf F F p.1 ≤ u p.1`,
    `affHi` is at most the combination of the bounds `u`. -/
theorem affHi_le_of_bounds (F : List SFact) (u : STerm → Nat) :
    ∀ {L : List (STerm × Int)}, (∀ p ∈ L, 0 ≤ p.2 ∧ hiOf F F p.1 ≤ u p.1) →
      affHi F L ≤ (L.map fun p => p.2 * (u p.1 : Int)).sum
  | [], _ => by simp [affHi]
  | p :: L, h => by
      have ih := affHi_le_of_bounds F u fun q hq => h q (List.mem_cons_of_mem _ hq)
      obtain ⟨hc, hm⟩ := h p List.mem_cons_self
      have hb : ((hiOf F F p.1 : Nat) : Int) ≤ (u p.1 : Int) := Int.ofNat_le.mpr hm
      simp only [affHi, List.map_cons, List.sum_cons, ite_eq_left hc]
      have := Int.mul_le_mul_of_nonneg_left hb hc
      omega

/-- **The affine check accepts an index whose affine form is bounded**: every atom of
    `affOf F t` has a non-negative coefficient and an upper bound `hiOf F F x ≤ u x`, and the
    combination of the bounds with the constant of the form is at most `b'`. -/
theorem affLe_of_bounds {F : List SFact} {t : STerm} {b' : Nat} (u : STerm → Nat)
    (h : ∀ p ∈ (affOf F t).1, 0 ≤ p.2 ∧ hiOf F F p.1 ≤ u p.1)
    (hb : ((affOf F t).1.map fun p => p.2 * (u p.1 : Int)).sum + (affOf F t).2 ≤ b') :
    affLe F t b' = true := by
  have := affHi_le_of_bounds F u h
  simp only [affLe, List.any_eq_true, decide_eq_true_eq]
  exact ⟨_, affOf_mem_affAlts F t, by omega⟩

/-! ## Monotonicity of the bounds in the fact list -/

/-- **`ubOf` is at most every single-term bound**: a fact `.le [t] b` of `F` gives `ubOf F t`
    a value at most `b`. In particular the value is at most the bound of the first such fact,
    so a check that reads `ubOf` as an upper bound compared by `≤` accepts whatever it
    accepted when `ubOf` read the first fact. -/
theorem ubOf_le_of_mem : ∀ {F : List SFact} {t : STerm} {b : Nat}, SFact.le [t] b ∈ F →
    ∃ u, ubOf F t = some u ∧ u ≤ b
  | [], _, _, h => by cases h
  | f :: F, t, b, h => by
      rcases List.mem_cons.mp h with rfl | h
      · refine ⟨min b ((ubOf F t).getD b), by simp [ubOf], min_le_left _ _⟩
      · obtain ⟨u, hu, hb⟩ := ubOf_le_of_mem h
        match f with
        | .le [t'] b' =>
            simp only [ubOf]
            split
            · rename_i he
              subst he
              exact ⟨_, rfl, (min_le_right _ _).trans (by simp [hu, hb])⟩
            · exact ⟨u, hu, hb⟩
        | .le [] _ | .le (_ :: _ :: _) _ | .ge _ _ | .w64 _ | .ne _ _ | .ale _ _ =>
            exact ⟨u, by simpa [ubOf] using hu, hb⟩

/-- **`ubOf` is attained**: its value is the bound of a single-term fact of `F` on `t`. -/
theorem ubOf_mem : ∀ {F : List SFact} {t : STerm} {u : Nat}, ubOf F t = some u →
    SFact.le [t] u ∈ F
  | [], _, _, h => by cases h
  | f :: F, t, u, h => by
      match f with
      | .le [t'] b' =>
          simp only [ubOf] at h
          split at h
          · rename_i he
            subst he
            cases h
            cases hu : ubOf F t' with
            | none => simp
            | some v =>
                have hv := ubOf_mem hu
                simp only [Option.getD_some]
                rcases min_choice b' v with he | he <;> rw [he]
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ hv
          · exact List.mem_cons_of_mem _ (ubOf_mem h)
      | .le [] _ | .le (_ :: _ :: _) _ | .ge _ _ | .w64 _ | .ne _ _ | .ale _ _ =>
          exact List.mem_cons_of_mem _ (ubOf_mem (by simpa [ubOf] using h))

/-- **`ubOf` does not grow when facts are added.** -/
theorem ubOf_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {t : STerm} {u : Nat}
    (h : ubOf F t = some u) : ∃ u', ubOf F' t = some u' ∧ u' ≤ u :=
  ubOf_le_of_mem (hF _ (ubOf_mem h))

/-- **`ubSum` does not grow when facts are added.** -/
theorem ubSum_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') :
    ∀ {ts : List STerm} {u : Nat}, ubSum F ts = some u → ∃ u', ubSum F' ts = some u' ∧ u' ≤ u
  | [], u, h => ⟨0, rfl, by simp only [ubSum, Option.some.injEq] at h; omega⟩
  | t :: ts, u, h => by
      simp only [ubSum] at h
      split at h
      · rename_i a b ha hb
        cases h
        obtain ⟨a', ha', hle⟩ := ubOf_mono hF ha
        obtain ⟨b', hb', hle'⟩ := ubSum_mono hF hb
        exact ⟨a' + b', by simp [ubSum, ha', hb'], by omega⟩
      · cases h

/-- **`lbOf` is at least its immediate bound.** -/
theorem immLb_le_lbOf : ∀ (F : List SFact) (t : STerm), immLb t ≤ lbOf F t
  | [], _ => le_rfl
  | .ge t' k :: F, t => by
      simp only [lbOf]
      split
      · exact (immLb_le_lbOf F t).trans (le_max_right _ _)
      · exact immLb_le_lbOf F t
  | .le _ _ :: F, t | .w64 _ :: F, t | .ne _ _ :: F, t | .ale _ _ :: F, t =>
      immLb_le_lbOf F t

/-- **`lbOf` is attained**: it is the immediate bound of `t` or the bound of a lower-bound fact
    of `F` on `t`. -/
theorem lbOf_cases : ∀ (F : List SFact) (t : STerm),
    lbOf F t = immLb t ∨ SFact.ge t (lbOf F t) ∈ F
  | [], _ => Or.inl rfl
  | .ge t' k :: F, t => by
      simp only [lbOf]
      split
      · rename_i he
        subst he
        rcases max_choice k (lbOf F t') with he | he <;> rw [he]
        · exact Or.inr List.mem_cons_self
        · rcases lbOf_cases F t' with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases lbOf_cases F t with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
  | .le _ _ :: F, t | .w64 _ :: F, t | .ne _ _ :: F, t | .ale _ _ :: F, t => by
      rcases lbOf_cases F t with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **`lbOf` does not decrease when facts are added.** -/
theorem lbOf_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (t : STerm) :
    lbOf F t ≤ lbOf F' t := by
  rcases lbOf_cases F t with h | h
  · rw [h]
    exact immLb_le_lbOf F' t
  · exact lbOf_ge_of_mem (hF _ h)

/-- **`lbSum` does not decrease when facts are added.** -/
theorem lbSum_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') :
    ∀ ts : List STerm, lbSum F ts ≤ lbSum F' ts
  | [] => le_rfl
  | t :: ts => by
      have h1 := lbOf_mono hF t
      have h2 := lbSum_mono hF ts
      simp only [lbSum, List.map_cons, List.sum_cons] at h2 ⊢
      omega

/-- **`widOk` holds after facts are added.** -/
theorem widOk_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {t : STerm}
    (h : widOk F t = true) : widOk F' t = true := by
  simp only [widOk, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  exact h.imp id (hF _)

/-- **`hiOf` is at most the bound of the structure of the term.** -/
theorem hiOf_le_immHi (F : List SFact) : ∀ (G : List SFact) (t : STerm), hiOf F G t ≤ immHi t
  | [], _ => le_rfl
  | .le ts b :: G, t => by
      simp only [hiOf]
      split
      · exact (min_le_right _ _).trans (hiOf_le_immHi F G t)
      · exact hiOf_le_immHi F G t
  | .ale a b :: G, t => by
      simp only [hiOf]
      split
      · exact (min_le_right _ _).trans (hiOf_le_immHi F G t)
      · exact hiOf_le_immHi F G t
  | .ge _ _ :: G, t | .w64 _ :: G, t | .ne _ _ :: G, t => hiOf_le_immHi F G t

/-- **An element-bound fact bounds `hiOf` of a load from its array.** -/
theorem hiOf_le_of_ale (F : List SFact) :
    ∀ {G : List SFact} {a : SArr} {t : STerm} {b : Nat}, SFact.ale a b ∈ G →
      loadArr t = some a → hiOf F G t ≤ b
  | [], _, _, _, h, _ => by cases h
  | .ale a' b' :: G, a, t, b, h, ht => by
      simp only [hiOf]
      rcases List.mem_cons.mp h with h | h
      · cases h
        rw [ite_eq_left ht]
        exact min_le_left _ _
      · have ih := hiOf_le_of_ale F h ht
        split
        · exact (min_le_right _ _).trans ih
        · exact ih
  | .le ts' b' :: G, _, t, _, h, ht => by
      have ih := hiOf_le_of_ale F (List.mem_of_ne_of_mem (by simp) h) ht
      simp only [hiOf]
      split
      · exact (min_le_right _ _).trans ih
      · exact ih
  | .ge _ _ :: G, _, _, _, h, ht => by
      simp only [hiOf]
      exact hiOf_le_of_ale F (List.mem_of_ne_of_mem (by simp) h) ht
  | .w64 _ :: G, _, _, _, h, ht => by
      simp only [hiOf]
      exact hiOf_le_of_ale F (List.mem_of_ne_of_mem (by simp) h) ht
  | .ne _ _ :: G, _, _, _, h, ht => by
      simp only [hiOf]
      exact hiOf_le_of_ale F (List.mem_of_ne_of_mem (by simp) h) ht

/-- **`hiOf` does not grow when facts are added**, to the lower bounds `F` and to the bounding
    facts `G`. -/
theorem hiOf_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {G' : List SFact} (t : STerm) :
    ∀ (G : List SFact), (∀ f ∈ G, f ∈ G') → hiOf F' G' t ≤ hiOf F G t
  | [], _ => hiOf_le_immHi F' G' t
  | .le ts b :: G, hG => by
      have ih := hiOf_mono hF t G fun f hf => hG f (List.mem_cons_of_mem _ hf)
      simp only [hiOf]
      split
      · rename_i ht
        have h1 := hiOf_le_of_mem F' (hG _ List.mem_cons_self) ht
        have h2 := lbSum_mono hF (ts.erase t)
        exact le_min (h1.trans (by omega)) ih
      · exact ih
  | .ale a b :: G, hG => by
      have ih := hiOf_mono hF t G fun f hf => hG f (List.mem_cons_of_mem _ hf)
      simp only [hiOf]
      split
      · rename_i ht
        exact le_min (hiOf_le_of_ale F' (hG _ List.mem_cons_self) ht) ih
      · exact ih
  | .ge _ _ :: G, hG | .w64 _ :: G, hG | .ne _ _ :: G, hG =>
      hiOf_mono hF t G fun f hf => hG f (List.mem_cons_of_mem _ hf)

/-- **The alternatives of a sum keep their members** when those of both summands do. -/
theorem altsAdd_mono {P P' Q Q' : List (List STerm × Int)} (hP : ∀ p ∈ P, p ∈ P')
    (hQ : ∀ q ∈ Q, q ∈ Q') {r : List STerm × Int} (h : r ∈ altsAdd P Q) : r ∈ altsAdd P' Q' := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_altsAdd.mp h
  exact mem_altsAdd.mpr ⟨p, hP p hp, q, hQ q hq, rfl⟩

/-- **`linAlts` does not lose a form when facts are added.** -/
theorem linAlts_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (t : STerm) :
    ∀ p ∈ linAlts F t, p ∈ linAlts F' t := by
  fun_induction linAlts F t with
  | case3 m x w k h ih =>
      intro p hp
      rw [linAlts, ite_eq_left h]
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact List.mem_map.mpr ⟨q, ih q hq, rfl⟩
  | case4 m x w k h1 h hk ih =>
      intro p hp
      rw [linAlts, ite_eq_right h1, ite_eq_left h, ite_eq_left (hk.trans (lbOf_mono hF x))]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, ih q hq, rfl⟩)
  | case5 m x w k h1 h hk =>
      intro p hp
      rw [linAlts, ite_eq_right h1, ite_eq_left h]
      split
      · rcases List.mem_singleton.mp hp with rfl
        exact List.mem_cons_self
      · exact hp
  | case6 x w k h1 h2 ih =>
      intro p hp
      rw [linAlts, ite_eq_right h1, ite_eq_right h2, ite_eq_left rfl]
      exact ih p hp
  | case8 m x y _ h ih =>
      intro p hp
      have e : linAlts F' (.bin m x y) = linAlts F' x := by
        rwa [linAlts, ite_eq_left h]
      rw [e]
      exact ih p hp
  | _ =>
      intro p hp
      simp_all [linAlts]
      try split_ifs <;> simp_all

/-- **`sumAlts` does not lose a form when facts are added.** -/
theorem sumAlts_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') :
    ∀ (ts : List STerm), ∀ p ∈ sumAlts F ts, p ∈ sumAlts F' ts
  | [], _, hp => hp
  | t :: ts, _, hp => altsAdd_mono (linAlts_mono hF t) (sumAlts_mono hF ts) hp

/-- **`splitAlts` does not lose a splitting when facts are added.** -/
theorem splitAlts_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (t : STerm) :
    ∀ p ∈ splitAlts F t, p ∈ splitAlts F' t := by
  intro p hp
  cases t with
  | bin m x y =>
      simp only [splitAlts] at hp ⊢
      split at hp
      · rename_i h
        rw [ite_eq_left ⟨h.1, widOk_mono hF h.2⟩]
        rcases List.mem_cons.mp hp with rfl | hp
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _
            (altsAdd_mono (linAlts_mono hF x) (linAlts_mono hF y) hp)
      · rcases List.mem_singleton.mp hp with rfl
        split <;> exact List.mem_cons_self
  | _ => simpa [splitAlts] using hp

/-- **`splitsAlts` does not lose a splitting when facts are added.** -/
theorem splitsAlts_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') :
    ∀ (ts : List STerm), ∀ p ∈ splitsAlts F ts, p ∈ splitsAlts F' ts
  | [], _, hp => hp
  | t :: ts, _, hp => altsAdd_mono (splitAlts_mono hF t) (splitsAlts_mono hF ts) hp

/-- **`leBy` holds after facts are added.** -/
theorem leBy_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {as : List STerm} {K : Int}
    {b' : Nat} {f : SFact} (h : leBy F as K b' f = true) : leBy F' as K b' f = true := by
  cases f with
  | le ts b =>
      simp only [leBy] at h ⊢
      split at h
      · rename_i R hR
        simp only [decide_eq_true_eq] at h ⊢
        have := lbSum_mono hF R
        omega
      · cases h
  | _ => simp [leBy] at h

/-- **`leForm` holds after facts are added.** -/
theorem leForm_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {b' : Nat}
    {p : List STerm × Int} (h : leForm F b' p = true) : leForm F' b' p = true := by
  simp only [leForm, Bool.or_eq_true, List.any_eq_true] at h ⊢
  exact h.imp id fun ⟨f, hf, hl⟩ => ⟨f, hF f hf, leBy_mono hF hl⟩

/-- **`leLin` holds after facts are added.** -/
theorem leLin_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {ts : List STerm} {b' : Nat}
    (h : leLin F ts b' = true) : leLin F' ts b' = true := by
  simp only [leLin, List.any_eq_true] at h ⊢
  obtain ⟨p, hp, hl⟩ := h
  exact ⟨p, sumAlts_mono hF ts p hp, leForm_mono hF hl⟩

/-- **`mulParts` keeps its value when facts are added.** -/
theorem mulParts_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {a : STerm} {r : Nat × STerm}
    (h : mulParts F a = some r) : mulParts F' a = some r := by
  unfold mulParts at h ⊢
  split at h
  · rename_i m x y
    split at h
    · rename_i hm
      rw [ite_eq_left hm]
      split at h
      · exact h
      · split at h
        · split at h
          · rename_i hc
            rw [ite_eq_left ⟨hc.1, widOk_mono hF hc.2⟩]
            exact h
          · cases h
        · cases h
    · cases h
  · cases h

/-- **`mulForm` holds after facts are added.** -/
theorem mulForm_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {b' : Nat}
    {p : List STerm × Int} (h : mulForm F b' p = true) : mulForm F' b' p = true := by
  unfold mulForm at h ⊢
  split at h
  · rename_i a ha
    split at h
    · rename_i c x hp
      rw [mulParts_mono hF hp]
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, leLin_mono hF h.2⟩
    · cases h
  · cases h

/-- **`mulLe` holds after facts are added.** -/
theorem mulLe_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {ts : List STerm} {b' : Nat}
    (h : mulLe F ts b' = true) : mulLe F' ts b' = true := by
  simp only [mulLe, List.any_eq_true] at h ⊢
  obtain ⟨p, hp, hl⟩ := h
  exact ⟨p, sumAlts_mono hF ts p hp, mulForm_mono hF hl⟩

/-- **`formHi` does not grow when facts are added.** -/
theorem formHi_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (p : List STerm × Int) :
    formHi F' p ≤ formHi F p := by
  have key : ∀ ts : List STerm, (ts.map (hiOf F' F')).sum ≤ (ts.map (hiOf F F)).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
        have := hiOf_mono hF t F hF
        simp only [List.map_cons, List.sum_cons]
        omega
  have := key p.1
  unfold formHi
  omega

/-- The least of a base and the values of a list is at most each value and the base, and is
    the base or one of the values. -/
theorem foldr_min_cases {α : Type} (f : α → Nat) (b : Nat) :
    ∀ P : List α, P.foldr (fun p u => min (f p) u) b = b ∨
      ∃ p ∈ P, P.foldr (fun p u => min (f p) u) b = f p
  | [] => Or.inl rfl
  | p :: P => by
      simp only [List.foldr_cons]
      rcases min_choice (f p) (P.foldr (fun p u => min (f p) u) b) with h | h <;> rw [h]
      · exact Or.inr ⟨p, List.mem_cons_self, rfl⟩
      · rcases foldr_min_cases f b P with h | ⟨q, hq, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h⟩

theorem foldr_min_le_base {α : Type} (f : α → Nat) (b : Nat) :
    ∀ P : List α, P.foldr (fun p u => min (f p) u) b ≤ b
  | [] => le_rfl
  | _ :: P => (min_le_right _ _).trans (foldr_min_le_base f b P)

theorem foldr_min_le_mem {α : Type} (f : α → Nat) (b : Nat) :
    ∀ {P : List α} {p : α}, p ∈ P → P.foldr (fun p u => min (f p) u) b ≤ f p
  | q :: P, p, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (foldr_min_le_mem f b h)

/-- **`termHi` is at most the bound of each linear form.** -/
theorem termHi_le_form {F : List SFact} {t : STerm} {p : List STerm × Int}
    (hp : p ∈ linAlts F t) : termHi F t ≤ formHi F p :=
  foldr_min_le_mem _ _ hp

/-- **`termHi` is at most the bound `hiOf` of the term.** -/
theorem termHi_le_hiOf (F : List SFact) (t : STerm) : termHi F t ≤ hiOf F F t :=
  foldr_min_le_base _ _ _

/-- **`termHi` does not grow when facts are added.** -/
theorem termHi_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (t : STerm) :
    termHi F' t ≤ termHi F t := by
  rcases foldr_min_cases (formHi F) (hiOf F F t) (linAlts F t) with h | ⟨p, hp, h⟩
  · have e : termHi F t = hiOf F F t := h
    have := hiOf_mono hF t F hF
    have := termHi_le_hiOf F' t
    omega
  · have e : termHi F t = formHi F p := h
    have := termHi_le_form (linAlts_mono hF t p hp)
    have := formHi_mono hF p
    omega

/-- **`hiNe` does not grow when facts are added.** -/
theorem hiNe_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (t : STerm) :
    hiNe F' t ≤ hiNe F t := by
  have h1 := termHi_mono hF t
  have hle : hiNe F' t ≤ termHi F' t := by unfold hiNe; split <;> omega
  have hge : termHi F t - 1 ≤ hiNe F t := by unfold hiNe; split <;> omega
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · omega
  · unfold hiNe
    rw [h]
    by_cases hm : SFact.ne t (termHi F t) ∈ F
    · rw [ite_eq_left (hF _ hm), ite_eq_left hm]
    · rw [ite_eq_right hm]
      split <;> omega

/-- **`lbNe` does not decrease when facts are added.** -/
theorem lbNe_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (t : STerm) :
    lbNe F t ≤ lbNe F' t := by
  have h1 := lbOf_mono hF t
  have hge : lbOf F' t ≤ lbNe F' t := by unfold lbNe; split <;> omega
  have hle : lbNe F t ≤ lbOf F t + 1 := by unfold lbNe; split <;> omega
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · omega
  · unfold lbNe
    rw [← h]
    by_cases hm : SFact.ne t (lbOf F t) ∈ F
    · rw [ite_eq_left (hF _ hm), ite_eq_left hm]
    · rw [ite_eq_right hm]
      split <;> omega

/-- **`hiLe` holds after facts are added.** -/
theorem hiLe_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {ts : List STerm} {b' : Nat}
    (h : hiLe F ts b' = true) : hiLe F' ts b' = true := by
  have key : ∀ ts : List STerm, (ts.map (hiNe F')).sum ≤ (ts.map (hiNe F)).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
        have := hiNe_mono hF t
        simp only [List.map_cons, List.sum_cons]
        omega
  simp only [hiLe, decide_eq_true_eq] at h ⊢
  exact (key ts).trans h

/-- **`arrIn` holds after facts are added.** -/
theorem arrIn_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {a : SArr} {b : Nat}
    (h : arrIn F a b = true) : arrIn F' a b = true := by
  simp only [arrIn, List.any_eq_true] at h ⊢
  obtain ⟨f, hf, hl⟩ := h
  exact ⟨f, hF f hf, hl⟩

/-- **`arrOk` holds after facts are added.** -/
theorem arrOk_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {b : Nat} :
    ∀ (a : SArr), arrOk F b a = true → arrOk F' b a = true
  | .cell r, h => arrIn_mono hF h
  | .zero _ _, _ => rfl
  | .aset a w n i v, h => by
      simp only [arrOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact h.imp (arrIn_mono hF) fun h => ⟨arrOk_mono hF a h.1, (hiNe_mono hF v).trans h.2⟩

/-- **Entailment is monotone in the fact list**: a fact `F` entails is entailed by every list
    containing the facts of `F`. -/
theorem entails_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') :
    ∀ g : SFact, entails F g = true → entails F' g = true
  | .le ts b', h => by
      simp only [entails, Bool.or_eq_true] at h ⊢
      exact h.imp (Or.imp (leLin_mono hF) (mulLe_mono hF)) (hiLe_mono hF)
  | .ge t k, h => by
      simp only [entails, decide_eq_true_eq] at h ⊢
      exact h.trans (lbNe_mono hF t)
  | .w64 t, h => widOk_mono hF h
  | .ne t c, h => by
      simp only [entails, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      exact h.imp (Or.imp (fun h => lt_of_lt_of_le h (lbOf_mono hF t))
        (fun h => lt_of_le_of_lt (hiNe_mono hF t) h)) (hF _)
  | .ale a b, h => arrOk_mono hF a h

/-- **`leMixBy` holds after facts are added.** -/
theorem leMixBy_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {as : List STerm} {K : Int}
    {b' : Nat} {f : SFact} (h : leMixBy F as K b' f = true) : leMixBy F' as K b' f = true := by
  cases f with
  | le ts b =>
      simp only [leMixBy] at h ⊢
      split at h
      · rename_i u hu
        obtain ⟨u', hu', hle⟩ := ubSum_mono hF hu
        rw [hu']
        simp only [decide_eq_true_eq] at h ⊢
        have := lbSum_mono hF (peel ts as).1
        omega
      · cases h
  | _ => simp [leMixBy] at h

/-- **`leMix` holds after facts are added.** -/
theorem leMix_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {ts : List STerm} {b' : Nat}
    (h : leMix F ts b' = true) : leMix F' ts b' = true := by
  simp only [leMix, List.any_eq_true] at h ⊢
  obtain ⟨p, hp, q, hq, f, hf, hl⟩ := h
  exact ⟨p, sumAlts_mono hF ts p hp, q, splitsAlts_mono hF p.1 q hq, f, hF f hf,
    leMixBy_mono hF hl⟩

/-- **`affHi` does not grow when facts are added.** -/
theorem affHi_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') :
    ∀ L : List (STerm × Int), affHi F' L ≤ affHi F L
  | [] => le_rfl
  | p :: L => by
      have ih := affHi_mono hF L
      have hh : ((hiOf F' F' p.1 : Nat) : Int) ≤ (hiOf F F p.1 : Int) :=
        Int.ofNat_le.mpr (hiOf_mono hF p.1 F hF)
      have hl : ((lbOf F p.1 : Nat) : Int) ≤ (lbOf F' p.1 : Int) :=
        Int.ofNat_le.mpr (lbOf_mono hF p.1)
      simp only [affHi]
      split
      · rename_i hc
        have := Int.mul_le_mul_of_nonneg_left hh hc
        omega
      · rename_i hc
        have := Int.mul_le_mul_of_nonpos_left (by omega : p.2 ≤ 0) hl
        omega

/-- **`affLo` does not decrease when facts are added.** -/
theorem affLo_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') :
    ∀ L : List (STerm × Int), affLo F L ≤ affLo F' L
  | [] => le_rfl
  | p :: L => by
      have ih := affLo_mono hF L
      have hh : ((hiOf F' F' p.1 : Nat) : Int) ≤ (hiOf F F p.1 : Int) :=
        Int.ofNat_le.mpr (hiOf_mono hF p.1 F hF)
      have hl : ((lbOf F p.1 : Nat) : Int) ≤ (lbOf F' p.1 : Int) :=
        Int.ofNat_le.mpr (lbOf_mono hF p.1)
      simp only [affLo]
      split
      · rename_i hc
        have := Int.mul_le_mul_of_nonneg_left hl hc
        omega
      · rename_i hc
        have := Int.mul_le_mul_of_nonpos_left (by omega : p.2 ≤ 0) hh
        omega

/-- **`affComb` keeps its value when facts are added.** -/
theorem affComb_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {m : String}
    {L M r : List (STerm × Int) × Int} (h : affComb F m L M = some r) :
    affComb F' m L M = some r := by
  have hL := affHi_mono hF L.1
  have hM := affHi_mono hF M.1
  unfold affComb at h ⊢
  split at h
  · rename_i hm
    rw [ite_eq_left hm]
    split at h
    · rename_i hlt
      rw [ite_eq_left (by omega)]
      exact h
    · cases h
  · rename_i hm
    rw [ite_eq_right hm]
    split at h
    · rename_i hs
      rw [ite_eq_left hs]
      split at h
      · rename_i hle
        have := affLo_mono hF (affAdd L.1 (affScale (-1) M.1))
        rw [ite_eq_left (by omega)]
        exact h
      · cases h
    · rename_i hs
      rw [ite_eq_right hs]
      split at h
      · rename_i hu
        rw [ite_eq_left hu]
        split at h
        · rename_i hlt
          have h1 : max 0 (affHi F' L.1 + L.2) ≤ max 0 (affHi F L.1 + L.2) :=
            max_le_max le_rfl (by omega)
          have h2 : max 0 (affHi F' M.1 + M.2) ≤ max 0 (affHi F M.1 + M.2) :=
            max_le_max le_rfl (by omega)
          have h3 := Int.mul_le_mul h1 h2 (le_max_left _ _) (le_max_left _ _)
          rw [ite_eq_left (lt_of_le_of_lt h3 hlt)]
          exact h
        · cases h
      · cases h

/-- **`affAlts` does not lose a form when facts are added.** -/
theorem affAlts_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') (t : STerm) :
    ∀ p ∈ affAlts F t, p ∈ affAlts F' t := by
  fun_induction affAlts F t with
  | case3 m x y hw ihy ihx =>
      intro r hr
      rw [affAlts, ite_eq_left ⟨widOk_mono hF hw.1, widOk_mono hF hw.2⟩]
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · simp only [List.mem_flatMap, List.mem_filterMap] at hr
        obtain ⟨L, hL, M, hM, hc⟩ := hr
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨L, ihx L hL,
          List.mem_filterMap.mpr ⟨M, ihy M hM, affComb_mono hF hc⟩⟩)
  | case4 m x y hw =>
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      rw [affAlts]
      split <;> exact List.mem_cons_self
  | _ => intro p hp; simp_all [affAlts]

/-- **`affLe` holds after facts are added.** -/
theorem affLe_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {t : STerm} {b' : Nat}
    (h : affLe F t b' = true) : affLe F' t b' = true := by
  simp only [affLe, List.any_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨p, hp, hl⟩ := h
  have := affHi_mono hF p.1
  exact ⟨p, affAlts_mono hF t p hp, by omega⟩

/-- **The obligation check is monotone in the fact list.** -/
theorem oblsOk_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {os : List SObl}
    (h : oblsOk F os = true) : oblsOk F' os = true := by
  simp only [oblsOk, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  intro o ho
  obtain ⟨h0, h1⟩ := h o ho
  exact ⟨h0, h1.imp (Or.imp (entails_mono hF _) (leMix_mono hF)) (affLe_mono hF)⟩

/-- **The successor check is monotone in the fact list.** -/
theorem succOk_mono {F F' : List SFact} (hF : ∀ f ∈ F, f ∈ F') {ss : SSt} {fs : List IdxFact}
    (h : succOk F ss fs = true) : succOk F' ss fs = true := by
  simp only [succOk, List.all_eq_true] at h ⊢
  exact fun f hf => entails_mono hF _ (h f hf)

/-- **The obligation check accepts an index of a non-empty array whose affine form is
    bounded** below the length `n`. -/
theorem oblsOk_of_bounds {F : List SFact} {t : STerm} {n : Nat} (hn : 0 < n)
    (u : STerm → Nat) (h : ∀ p ∈ (affOf F t).1, 0 ≤ p.2 ∧ hiOf F F p.1 ≤ u p.1)
    (hb : ((affOf F t).1.map fun p => p.2 * (u p.1 : Int)).sum + (affOf F t).2 ≤ (n - 1 : Nat)) :
    oblsOk F [(t, n)] = true := by
  simp only [oblsOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true]
  exact ⟨hn, Or.inr (affLe_of_bounds u h hb)⟩

/-- **The obligation check on an affine index with single-term bound facts**: every atom `x`
    of the affine form has a non-negative coefficient and a fact `.le [x] (u x)` of `F`. -/
theorem oblsOk_of_facts {F : List SFact} {t : STerm} {n : Nat} (hn : 0 < n) (u : STerm → Nat)
    (h : ∀ p ∈ (affOf F t).1, 0 ≤ p.2 ∧ SFact.le [p.1] (u p.1) ∈ F)
    (hb : ((affOf F t).1.map fun p => p.2 * (u p.1 : Int)).sum + (affOf F t).2 ≤ (n - 1 : Nat)) :
    oblsOk F [(t, n)] = true :=
  oblsOk_of_bounds hn u (fun p hp => ⟨(h p hp).1, hiOf_le_of_single F (h p hp).2⟩) hb

/-! ## Completeness of entailment on the facts and their sub-sums -/

/-- A register is its own linear form. -/
theorem reg_mem_linAlts (F : List SFact) (r : String) :
    ([STerm.reg r], 0) ∈ linAlts F (.reg r) := by
  simp [linAlts]

/-- **A sum of atoms is its own linear form.** -/
theorem self_mem_sumAlts {F : List SFact} :
    ∀ {as : List STerm}, (∀ t ∈ as, ([t], 0) ∈ linAlts F t) → (as, 0) ∈ sumAlts F as
  | [], _ => by simp [sumAlts]
  | t :: as, h =>
      mem_altsAdd.mpr ⟨_, h t List.mem_cons_self, _,
        self_mem_sumAlts fun u hu => h u (List.mem_cons_of_mem _ hu), by simp⟩

theorem eraseAll_self : ∀ ts : List STerm, eraseAll ts ts = some []
  | [] => rfl
  | t :: ts => by
      simp only [eraseAll, List.mem_cons_self, ite_true, List.erase_cons_head]
      exact eraseAll_self ts

/-- **Entailment of a sub-sum of a fact**: the sum of atoms `as` that one fact `.le ts b`
    contains is at most `b` less the lower bounds of the remaining terms. -/
theorem entails_le_of_sub {F : List SFact} {ts as R : List STerm} {b b' : Nat}
    (hf : SFact.le ts b ∈ F) (hR : eraseAll ts as = some R)
    (hat : ∀ t ∈ as, ([t], 0) ∈ linAlts F t) (hb : (b : Int) - lbSum F R ≤ b') :
    entails F (.le as b') = true := by
  have hl : leLin F as b' = true := by
    simp only [leLin, List.any_eq_true]
    refine ⟨_, self_mem_sumAlts hat, ?_⟩
    simp only [leForm, Bool.or_eq_true, List.any_eq_true]
    refine Or.inr ⟨_, hf, ?_⟩
    simp only [leBy, hR, decide_eq_true_eq]
    omega
  simp [entails, hl]

/-- **Entailment of a fact of the list** on atoms. -/
theorem entails_le_of_mem {F : List SFact} {ts : List STerm} {b : Nat}
    (hf : SFact.le ts b ∈ F) (hat : ∀ t ∈ ts, ([t], 0) ∈ linAlts F t) :
    entails F (.le ts b) = true :=
  entails_le_of_sub hf (eraseAll_self ts) hat (by simp [lbSum])

/-- **Entailment of a sum by the bounds of its terms**: a sum whose terms have upper bounds
    `hiOf` (each from a fact containing it) summing to at most `b'`. -/
theorem entails_le_of_hiOf {F : List SFact} {ts : List STerm} {b' : Nat}
    (h : (ts.map (hiOf F F)).sum ≤ b') : entails F (.le ts b') = true := by
  have key : ∀ ts : List STerm, (ts.map (hiNe F)).sum ≤ (ts.map (hiOf F F)).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
        have h1 : hiNe F t ≤ termHi F t := by unfold hiNe; split <;> omega
        have h2 := termHi_le_hiOf F t
        simp only [List.map_cons, List.sum_cons]
        omega
  have hl : hiLe F ts b' = true := by
    simp only [hiLe, decide_eq_true_eq]
    exact (key ts).trans h
  simp [entails, hl]

/-- **Entailment of a single-term fact of the list.** -/
theorem entails_single_of_mem {F : List SFact} {t : STerm} {b : Nat}
    (hf : SFact.le [t] b ∈ F) : entails F (.le [t] b) = true :=
  entails_le_of_hiOf (by simpa using hiOf_le_of_single F hf)

/-- **Entailment of a lower-bound fact of the list.** -/
theorem entails_ge_of_mem {F : List SFact} {t : STerm} {k : Nat} (hf : SFact.ge t k ∈ F) :
    entails F (.ge t k) = true := by
  have h1 := lbOf_ge_of_mem hf
  have h2 : lbOf F t ≤ lbNe F t := by unfold lbNe; split <;> omega
  simp only [entails, decide_eq_true_eq]
  omega

/-- **Entailment of an excluded value of the list.** -/
theorem entails_ne_of_mem {F : List SFact} {t : STerm} {c : Nat} (hf : SFact.ne t c ∈ F) :
    entails F (.ne t c) = true := by
  simp [entails, hf]

/-- **Entailment of a width fact of the list** on a term that is its own width base. -/
theorem entails_w64_of_mem {F : List SFact} {t : STerm} (hf : SFact.w64 t ∈ F)
    (ht : t.wbase = t) : entails F (.w64 t) = true := by
  simp [entails, widOk, ht, hf]

/-- **Entailment of an element bound of the list.** -/
theorem entails_ale_of_mem {F : List SFact} {a : SArr} {b : Nat} (hf : SFact.ale a b ∈ F) :
    entails F (.ale a b) = true := by
  have h : arrIn F a b = true := by
    simp only [arrIn, List.any_eq_true]
    exact ⟨_, hf, by simp⟩
  cases a with
  | cell r => exact h
  | zero _ _ => rfl
  | aset a w n i v => simp [entails, arrOk, h]

/-! ## Facts through register moves -/

/-- The fact `f` with the register `d` replaced by `s`. -/
def IdxFact.rename (d s : String) : IdxFact → IdxFact
  | .le rs b => .le (rs.map fun r => if r = d then s else r) b
  | .ge r k => .ge (if r = d then s else r) k
  | .ale a b => .ale a b
  | .w64 r => .w64 (if r = d then s else r)

/-- **A fact passes through a register move**: read through the state after the move
    `d := s` (the symbolic step of `movRegArgs?`), a fact is its renaming read through the
    state before. -/
theorem IdxFact.toS_setR (ss : SSt) (d s : String) (f : IdxFact) :
    f.toS (ss.setR d (ss.regs s)).regs (ss.setR d (ss.regs s)).arrs =
      (f.rename d s).toS ss.regs ss.arrs := by
  have e : (ss.setR d (ss.regs s)).regs = fun r => ss.regs (if r = d then s else r) := by
    funext r
    rw [SSt.setR_regs]
    split <;> rfl
  have ea : (ss.setR d (ss.regs s)).arrs = ss.arrs := rfl
  cases f <;> simp only [IdxFact.toS, IdxFact.rename, e, ea, List.map_map, Function.comp_def]

/-- **The successor check through a register move**: the facts of a successor follow through
    the state after the move `d := s` exactly when their renamings follow through the state
    before. -/
theorem succOk_setR (F : List SFact) (ss : SSt) (d s : String) (fs : List IdxFact) :
    succOk F (ss.setR d (ss.regs s)) fs = succOk F ss (fs.map (IdxFact.rename d s)) := by
  simp only [succOk, List.all_map, Function.comp_def, IdxFact.toS_setR]

/-! ## The annotation keeps every post-fixed annotation below the candidates -/

/-- An element of a list of an array stays in it when the list at another index is set, and
    when the list at its index is set to one containing it. -/
theorem mem_getD_set! {a : Array (List IdxFact)} {k j : Nat} {v : List IdxFact} {f : IdxFact}
    (h : f ∈ a.getD j []) (hv : j = k → f ∈ v) : f ∈ (a.set! k v).getD j [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds] at h ⊢
  split
  · rename_i hk
    subst hk
    split
    · simp [hv rfl]
    · rw [Array.getElem?_eq_none (by omega)] at h
      simp at h
  · exact h

/-- **A restriction step keeps a post-fixed annotation**: when the facts `P j` of every
    successor `j` follow from `F` and the condition of the edge, the step keeps them. -/
theorem annVisit_contains {P : Nat → List IdxFact} {F : List SFact} :
    ∀ (es : List (Nat × List SFact × SSt)) (a : Array (List IdxFact)) (pend : Array Bool)
      (q : Std.Queue Nat), (∀ j, ∀ f ∈ P j, f ∈ a.getD j []) →
      (∀ e ∈ es, ∀ f ∈ P e.1, entails (F ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true) →
      ∀ j, ∀ f ∈ P j, f ∈ (annVisit F es (a, pend, q)).1.getD j []
  | [], _, _, _, hinv, _ => hinv
  | (k, ex, ss) :: es, a, pend, q, hinv, hpost => by
      have hpost' : ∀ e ∈ es, ∀ f ∈ P e.1,
          entails (F ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true :=
        fun e he => hpost e (List.mem_cons_of_mem _ he)
      have hset : ∀ j, ∀ f ∈ P j, f ∈ (a.set! k ((a.getD k []).filter fun f =>
          entails (F ++ ex) (f.toS ss.regs ss.arrs))).getD j [] := by
        intro j f hf
        refine mem_getD_set! (hinv j f hf) fun hj => ?_
        subst hj
        exact List.mem_filter.mpr ⟨hinv j f hf, hpost _ List.mem_cons_self f hf⟩
      unfold annVisit
      rw [List.foldl_cons]
      dsimp only
      split
      · split
        · exact annVisit_contains es _ _ _ hset hpost'
        · exact annVisit_contains es _ _ _ hset hpost'
      · exact annVisit_contains es _ _ _ hinv hpost'


/-- `startF` keeps inclusion. -/
theorem startF_sub {fs gs : List IdxFact} (h : ∀ f ∈ fs, f ∈ gs) :
    ∀ g ∈ startF fs, g ∈ startF gs := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  exact List.mem_map.mpr ⟨f, h f hf, rfl⟩

/-- **The worklist keeps a post-fixed annotation**: when the facts `P j` of every successor
    `j` of every block `k` follow from the facts `P k` and the condition of the edge, every
    fact of `P` present at the start is present at the end. -/
theorem annWork_contains {P : Nat → List IdxFact} {E : Array (List (Nat × List SFact × SSt))}
    (hpost : ∀ k, ∀ e ∈ E.getD k [], ∀ f ∈ P e.1,
      entails (startF (P k) ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true) :
    ∀ (fuel : Nat) (st : Array (List IdxFact) × Array Bool × Std.Queue Nat),
      (∀ j, ∀ f ∈ P j, f ∈ st.1.getD j []) → ∀ j, ∀ f ∈ P j, f ∈ (annWork E fuel st).getD j []
  | 0, (_, _, _), hinv => hinv
  | fuel + 1, (a, pend, q), hinv => by
      unfold annWork
      split
      · exact hinv
      · rename_i k q' _
        refine annWork_contains hpost fuel _ (annVisit_contains _ _ _ _ hinv ?_)
        intro e he f hf
        refine entails_mono ?_ _ (hpost k e he f hf)
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact List.mem_append_left _ (startF_sub (hinv k) g hg)
        · exact List.mem_append_right _ hg

/-- **The annotation contains every post-fixed annotation below the candidates**: an
    annotation `P` of candidates whose block-`0` facts follow from the entry facts and whose
    successor facts follow along every edge `annEdges` is contained in `idxAnnot`. -/
theorem idxAnnot_contains {entry : List IdxFact} {B : List LinstrRM} {G : CFG}
    (hG : cfgOf (B.map Prod.fst) = some G) {P : Nat → List IdxFact}
    (hcand : ∀ j < G.blocks.size, ∀ f ∈ P j, f ∈ idxCands entry B G)
    (h0 : ∀ f ∈ P 0, entails (startF entry) (f.toS STerm.reg SArr.cell) = true)
    (hpost : ∀ k < G.blocks.size, ∀ e ∈ annEdges B G k, e.1 < G.blocks.size → ∀ f ∈ P e.1,
      entails (startF (P k) ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true) :
    ∀ j < G.blocks.size, ∀ f ∈ P j, f ∈ annAt (idxAnnot entry B) j := by
  intro j hj f hf
  let P' : Nat → List IdxFact := fun j => if j < G.blocks.size then P j else []
  have hP' : ∀ {j f}, f ∈ P' j → j < G.blocks.size ∧ f ∈ P j := by
    intro j f h
    simp only [P'] at h
    split at h
    · exact ⟨by assumption, h⟩
    · simp at h
  have key := annWork_contains (P := P')
    (E := (Array.range G.blocks.size).map (annEdges B G)) ?_ (G.blocks.size *
      ((idxCands entry B G).length + 1) + 1)
    ((Array.range G.blocks.size).map fun k =>
        if k = 0 then (idxCands entry B G).filter fun f =>
          entails (startF entry) (f.toS STerm.reg SArr.cell)
        else idxCands entry B G,
      Array.replicate G.blocks.size true,
      (List.range G.blocks.size).foldl (fun q k => q.enqueue k) Std.Queue.empty) ?_ j f
      (by simp only [P', hj, ite_true]; exact hf)
  · simp only [annAt, idxAnnot]
    rw [hG]
    simpa [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD] using key
  · intro k e he f hf
    obtain ⟨hk1, hf1⟩ := hP' hf
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range] at he
    split at he
    · rename_i hk
      have hsub : ∀ g ∈ startF (P k) ++ e.2.1, g ∈ startF (P' k) ++ e.2.1 := by
        simp only [P', hk, ite_true]
        exact fun g hg => hg
      exact entails_mono hsub _ (hpost k hk e (by simpa using he) hk1 f hf1)
    · simp at he
  · intro j f hf
    obtain ⟨hj, hf1⟩ := hP' hf
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hj,
      ite_true, Option.map_some, Option.getD_some]
    split
    · rename_i h0j
      subst h0j
      exact List.mem_filter.mpr ⟨hcand 0 hj f hf1, h0 f hf1⟩
    · exact hcand j hj f hf1

/-! ## The check with the greedy forms

`idxInvCheckBG` is `idxInvCheckB` with each reader of a form replaced by the reader of the
single greedy form `sumLin`, `splitAdds`, `affOf` (and the product bound of `affOf`). It is the
check of compiler commit 4bd6693e; `idxInvCheckB_of_G` proves that `idxInvCheckB` accepts every
triple of entry facts, annotation and body it accepts. -/

section Greedy

/-- The sum of `ts` is at most `b'` by the greedy linear form `sumLin`. -/
def leLinG (F : List SFact) (ts : List STerm) (b' : Nat) : Bool := leForm F b' (sumLin F ts)

/-- The sum of `ts` is at most `b'` by a product read off the greedy linear form `sumLin`. -/
def mulLeG (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  match (sumLin F ts).1 with
  | [a] =>
      match mulParts F a with
      | some (c, x) =>
          decide ((sumLin F ts).2 ≤ b') &&
            leLinG F [x] (((b' : Int) - (sumLin F ts).2).toNat / c)
      | none => false
  | _ => false

/-- The upper bound of `t` from `hiOf` and the greedy linear form `linOf`. -/
def termHiG (F : List SFact) (t : STerm) : Nat := min (hiOf F F t) (formHi F (linOf F t))

/-- The upper bound `termHiG` of `t`, less one when a fact of `F` excludes the bound. -/
def hiNeG (F : List SFact) (t : STerm) : Nat :=
  if SFact.ne t (termHiG F t) ∈ F then termHiG F t - 1 else termHiG F t

/-- The sum of `ts` is at most `b'` by the sum of the upper bounds `hiNeG` of its terms. -/
def hiLeG (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  decide ((ts.map (hiNeG F)).sum ≤ b')

/-- `arrOk` with the upper bound `hiNeG`. -/
def arrOkG (F : List SFact) (b : Nat) : SArr → Bool
  | .cell r => arrIn F (.cell r) b
  | .zero _ _ => true
  | .aset a w n i v => arrIn F (.aset a w n i v) b || (arrOkG F b a && decide (hiNeG F v ≤ b))

/-- Entailment with the greedy readers. -/
def entailsG (F : List SFact) : SFact → Bool
  | .le ts b' => leLinG F ts b' || mulLeG F ts b' || hiLeG F ts b'
  | .ge t k => decide (k ≤ lbNe F t)
  | .w64 t => widOk F t
  | .ne t c => decide (c < lbOf F t) || decide (hiNeG F t < c) || decide (SFact.ne t c ∈ F)
  | .ale a b => arrOkG F b a

/-- `leMix` with the greedy forms `sumLin` and `splitAdds`. -/
def leMixG (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  F.any (leMixBy F (splitAdds F (sumLin F ts).1).1
    ((sumLin F ts).2 + (splitAdds F (sumLin F ts).1).2) b')

/-- `affLe` with the greedy affine form `affOf`. -/
def affLeG (F : List SFact) (t : STerm) (b' : Nat) : Bool :=
  decide (affHi F (affOf F t).1 + (affOf F t).2 ≤ b')

/-- The obligation check with the greedy readers. -/
def oblsOkG (F : List SFact) (os : List SObl) : Bool :=
  os.all fun o => decide (0 < o.2) &&
    (entailsG F (.le [o.1] (o.2 - 1)) || leMixG F [o.1] (o.2 - 1) || affLeG F o.1 (o.2 - 1))

/-- The successor check with the greedy readers. -/
def succOkG (F : List SFact) (ss : SSt) (fs : List IdxFact) : Bool :=
  fs.all fun f => entailsG F (f.toS ss.regs ss.arrs)

/-- `termInvOk` with the greedy readers. -/
def termInvOkG (ann : List (List IdxFact)) (F : List SFact) (ss : SSt) (T : Term)
    (z : Option LinstrRM) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match T with
  | .fall (some j) => succOkG F ss (annAt ann j)
  | .fall none => true
  | .goto tg => succOkG F ss (annAt ann tg)
  | .cond tg nx =>
      match z with
      | some (.Lcond c _, _) =>
          succOkG (F ++ edgeFacts (dec ss c) true) ss (annAt ann tg) &&
            match nx with
            | some j => succOkG (F ++ edgeFacts (dec ss c) false) ss (annAt ann j)
            | none => true
      | _ => false
  | .ret => true

/-- `blockInvOk` with the greedy readers. -/
def blockInvOkG (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG) (k : Nat)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) :
    Bool :=
  match (G.blk k).term with
  | .ret => true
  | T =>
      match symRun (bodyAt B (G.blk k) T) SSt.start sym with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          oblsOkG (startF (annAt ann k) ++ gs.flatMap guardW64)
              (symObl (bodyAt B (G.blk k) T) SSt.start sym) &&
            termInvOkG ann (startF (annAt ann k)) ss T B[(G.blk k).stop - 1]? dec

/-- **The bounds-invariant check with the greedy readers.** -/
def idxInvCheckBG (entry : List IdxFact) (ann : List (List IdxFact)) (B : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) :
    Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      (List.range G.blocks.size).all (fun k => blockInvOkG ann B G k sym dec) &&
        (annAt ann 0).all fun f => entailsG (startF entry) (f.toS STerm.reg SArr.cell)
  | none => false

variable {F : List SFact}

theorem leLin_of_G {ts : List STerm} {b' : Nat} (h : leLinG F ts b' = true) :
    leLin F ts b' = true := by
  simp only [leLin, List.any_eq_true]
  exact ⟨_, sumLin_mem_sumAlts F ts, h⟩

theorem mulLe_of_G {ts : List STerm} {b' : Nat} (h : mulLeG F ts b' = true) :
    mulLe F ts b' = true := by
  simp only [mulLe, List.any_eq_true]
  refine ⟨_, sumLin_mem_sumAlts F ts, ?_⟩
  unfold mulLeG at h
  unfold mulForm
  split at h
  · rename_i a ha
    rw [ha]
    split at h
    · rename_i c x hp
      simp only [hp]
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, leLin_of_G h.2⟩
    · cases h
  · cases h

theorem termHi_le_G (t : STerm) : termHi F t ≤ termHiG F t :=
  le_min (termHi_le_hiOf F t) (termHi_le_form (linOf_mem_linAlts F t))

theorem hiNe_le_G (t : STerm) : hiNe F t ≤ hiNeG F t := by
  have h1 := termHi_le_G (F := F) t
  have hle : hiNe F t ≤ termHi F t := by unfold hiNe; split <;> omega
  have hge : termHiG F t - 1 ≤ hiNeG F t := by unfold hiNeG; split <;> omega
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · omega
  · unfold hiNe hiNeG
    rw [h]

theorem hiLe_of_G {ts : List STerm} {b' : Nat} (h : hiLeG F ts b' = true) :
    hiLe F ts b' = true := by
  have key : ∀ ts : List STerm, (ts.map (hiNe F)).sum ≤ (ts.map (hiNeG F)).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
        have := hiNe_le_G (F := F) t
        simp only [List.map_cons, List.sum_cons]
        omega
  simp only [hiLe, hiLeG, decide_eq_true_eq] at h ⊢
  exact (key ts).trans h

theorem arrOk_of_G {b : Nat} : ∀ (a : SArr), arrOkG F b a = true → arrOk F b a = true
  | .cell _, h => h
  | .zero _ _, _ => rfl
  | .aset a w n i v, h => by
      simp only [arrOk, arrOkG, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact h.imp id fun h => ⟨arrOk_of_G a h.1, (hiNe_le_G v).trans h.2⟩

theorem entails_of_G : ∀ g : SFact, entailsG F g = true → entails F g = true
  | .le ts b', h => by
      simp only [entails, entailsG, Bool.or_eq_true] at h ⊢
      exact h.imp (Or.imp leLin_of_G mulLe_of_G) hiLe_of_G
  | .ge _ _, h => h
  | .w64 _, h => h
  | .ne t c, h => by
      simp only [entails, entailsG, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      exact h.imp (Or.imp id fun h => lt_of_le_of_lt (hiNe_le_G t) h) id
  | .ale a _, h => arrOk_of_G a h

theorem leMix_of_G {ts : List STerm} {b' : Nat} (h : leMixG F ts b' = true) :
    leMix F ts b' = true := by
  simp only [leMix, leMixG, List.any_eq_true] at h ⊢
  obtain ⟨f, hf, hl⟩ := h
  exact ⟨_, sumLin_mem_sumAlts F ts, _, splitAdds_mem_splitsAlts F _, f, hf, hl⟩

theorem affLe_of_G {t : STerm} {b' : Nat} (h : affLeG F t b' = true) : affLe F t b' = true := by
  simp only [affLe, affLeG, List.any_eq_true] at h ⊢
  exact ⟨_, affOf_mem_affAlts F t, h⟩

theorem oblsOk_of_G {os : List SObl} (h : oblsOkG F os = true) : oblsOk F os = true := by
  simp only [oblsOk, oblsOkG, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  intro o ho
  obtain ⟨h0, h1⟩ := h o ho
  exact ⟨h0, h1.imp (Or.imp (entails_of_G _) leMix_of_G) affLe_of_G⟩

theorem succOk_of_G {ss : SSt} {fs : List IdxFact} (h : succOkG F ss fs = true) :
    succOk F ss fs = true := by
  simp only [succOk, succOkG, List.all_eq_true] at h ⊢
  exact fun f hf => entails_of_G _ (h f hf)

theorem termInvOk_of_G {ann : List (List IdxFact)} {ss : SSt} {T : Term}
    {z : Option LinstrRM} {dec : SSt → LOperand → SDec}
    (h : termInvOkG ann F ss T z dec = true) : termInvOk ann F ss T z dec = true := by
  unfold termInvOkG at h
  unfold termInvOk
  split at h
  · exact succOk_of_G h
  · rfl
  · exact succOk_of_G h
  · split at h
    · simp only [Bool.and_eq_true] at h ⊢
      refine ⟨succOk_of_G h.1, ?_⟩
      have h2 := h.2
      split at h2
      · exact succOk_of_G h2
      · rfl
    · cases h
  · rfl

theorem blockInvOk_of_G {ann : List (List IdxFact)} {B : List LinstrRM} {G : CFG} {k : Nat}
    {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (h : blockInvOkG ann B G k sym dec = true) : blockInvOk ann B G k sym dec = true := by
  unfold blockInvOkG at h
  unfold blockInvOk
  cases hT : (G.blk k).term <;> rw [hT] at h <;> dsimp only at h ⊢
  all_goals
    split at h <;> rename_i hr <;> rw [hr]
    · cases h
    · simp only [Bool.and_eq_true] at h ⊢
      exact ⟨oblsOk_of_G h.1, termInvOk_of_G h.2⟩

/-- **The check does not lose a body**: `idxInvCheckB` accepts every entry, annotation and
    body that the check with the greedy forms `idxInvCheckBG` accepts. -/
theorem idxInvCheckB_of_G {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (h : idxInvCheckBG entry ann B sym dec = true) : idxInvCheckB entry ann B sym dec = true := by
  unfold idxInvCheckBG at h
  unfold idxInvCheckB
  split at h
  · rename_i G hG
    rw [hG]
    simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨fun k hk => blockInvOk_of_G (h.1 k hk), fun f hf => entails_of_G _ (h.2 f hf)⟩
  · cases h

end Greedy

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
