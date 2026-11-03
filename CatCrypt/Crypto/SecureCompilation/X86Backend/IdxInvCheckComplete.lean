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
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

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
  simp only [affLe, decide_eq_true_eq]
  omega

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

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
