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
* `entails_mono`, `oblsOk_mono`, `succOk_mono`: entailment, the obligation check and the
  successor check are monotone in the list of facts read as a set (`F ⊆ F'`), through
  `lbOf_mono`, `hiOf_anti`, `ubSum_mono`, `termHi_anti` and the monotonicity of the forms
  (`linForms_mono`, `splitForms_mono`, `affForms_mono`).
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
  exact affLe_of_affOf (by omega)

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

/-! ## Monotonicity in the facts

Every bound and test of the check is monotone in the list of facts, read as a set: a list
`F'` that contains every fact of `F` gives lower bounds at least, upper bounds at most, and
accepts every entailment and obligation that `F` accepts. -/

section Mono

variable {F F' : List SFact}

theorem immLb_le_lbOf (t : STerm) : ∀ F : List SFact, immLb t ≤ lbOf F t
  | [] => le_rfl
  | .ge t' k :: F => by
      simp only [lbOf]
      split
      · exact (immLb_le_lbOf t F).trans (le_max_right _ _)
      · exact immLb_le_lbOf t F
  | .le _ _ :: F => immLb_le_lbOf t F
  | .w64 _ :: F => immLb_le_lbOf t F
  | .ne _ _ :: F => immLb_le_lbOf t F
  | .ale _ _ :: F => immLb_le_lbOf t F

theorem lbOf_mono (h : F ⊆ F') (t : STerm) : lbOf F t ≤ lbOf F' t := by
  induction F with
  | nil => exact immLb_le_lbOf t F'
  | cons f F ih =>
      have ih := ih (fun g hg => h (List.mem_cons_of_mem _ hg))
      cases f with
      | ge t' k =>
          simp only [lbOf]
          split
          · rename_i he
            subst he
            exact max_le (lbOf_ge_of_mem (h List.mem_cons_self)) ih
          · exact ih
      | le _ _ => exact ih
      | w64 _ => exact ih
      | ne _ _ => exact ih
      | ale _ _ => exact ih

theorem lbSum_mono (h : F ⊆ F') (ts : List STerm) : lbSum F ts ≤ lbSum F' ts := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
      have := lbOf_mono h t
      simp only [lbSum, List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem hiOf_le_immHi (F : List SFact) (t : STerm) : ∀ G : List SFact, hiOf F G t ≤ immHi t
  | [] => le_rfl
  | .le ts b :: G => by
      simp only [hiOf]
      split
      · exact (min_le_right _ _).trans (hiOf_le_immHi F t G)
      · exact hiOf_le_immHi F t G
  | .ale a b :: G => by
      simp only [hiOf]
      split
      · exact (min_le_right _ _).trans (hiOf_le_immHi F t G)
      · exact hiOf_le_immHi F t G
  | .ge _ _ :: G => hiOf_le_immHi F t G
  | .w64 _ :: G => hiOf_le_immHi F t G
  | .ne _ _ :: G => hiOf_le_immHi F t G

/-- **An element-bound fact bounds `hiOf` of a load from its array.** -/
theorem hiOf_le_of_ale (F : List SFact) {t : STerm} {a : SArr} {b : Nat}
    (ha : loadArr t = some a) : ∀ {G : List SFact}, SFact.ale a b ∈ G → hiOf F G t ≤ b
  | [], h => by cases h
  | g :: G, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [hiOf, ha, ite_true]
        exact min_le_left _ _
      · have ih := hiOf_le_of_ale F ha h
        cases g with
        | le ts b' =>
            simp only [hiOf]
            split
            · exact (min_le_right _ _).trans ih
            · exact ih
        | ale a' b' =>
            simp only [hiOf]
            split
            · exact (min_le_right _ _).trans ih
            · exact ih
        | ge _ _ => exact ih
        | w64 _ => exact ih
        | ne _ _ => exact ih

theorem hiOf_anti {G G' : List SFact} (hF : F ⊆ F') (hG : G ⊆ G') (t : STerm) :
    hiOf F' G' t ≤ hiOf F G t := by
  induction G with
  | nil => exact hiOf_le_immHi F' t G'
  | cons g G ih =>
      have ih := ih (fun x hx => hG (List.mem_cons_of_mem _ hx))
      have hg := hG List.mem_cons_self
      cases g with
      | le ts b =>
          simp only [hiOf]
          split
          · rename_i ht
            have h1 := hiOf_le_of_mem F' hg ht
            have h2 := lbSum_mono hF (ts.erase t)
            exact le_min (h1.trans (by omega)) ih
          · exact ih
      | ale a b =>
          simp only [hiOf]
          split
          · rename_i ha
            exact le_min (hiOf_le_of_ale F' ha hg) ih
          · exact ih
      | ge _ _ => exact ih
      | w64 _ => exact ih
      | ne _ _ => exact ih

theorem widOk_mono (h : F ⊆ F') {t : STerm} (hw : widOk F t = true) : widOk F' t = true := by
  simp only [widOk, Bool.or_eq_true, decide_eq_true_eq] at hw ⊢
  exact hw.imp id (fun hm => h hm)

theorem linForms_mono (h : F ⊆ F') (t : STerm) : linForms F t ⊆ linForms F' t := by
  fun_induction linOf F t with
  | case3 m x w k hc ih =>
      obtain ⟨rfl, rfl⟩ := hc
      intro p hp
      simp only [linForms, and_self, ite_true, List.mem_map] at hp ⊢
      obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨q, ih hq, rfl⟩
  | case4 m x w k _ hc ih =>
      obtain ⟨rfl, rfl, hk⟩ := hc
      intro p hp
      simp only [linForms, show ("SUB" = "ADD") = False by decide, and_false, ite_false,
        and_self, ite_true, hk, (hk.trans (lbOf_mono h x)), List.mem_append, List.mem_map,
        List.mem_singleton] at hp ⊢
      rcases hp with ⟨q, hq, rfl⟩ | rfl
      · exact Or.inl ⟨q, ih hq, rfl⟩
      · exact Or.inr rfl
  | case5 x w k _ _ ih =>
      intro p hp
      simp only [linForms, show ("AND" = "ADD") = False by decide,
        show ("AND" = "SUB") = False by decide, and_false, ite_false, ite_true] at hp ⊢
      exact ih hp
  | case7 m x y _ hc ih =>
      intro p hp
      simp only [linForms, hc, ite_true] at hp ⊢
      exact ih hp
  | _ =>
      intro p hp
      simp_all only [linForms]
      try (split_ifs at hp ⊢ <;> simp_all)

theorem sumForms_mono (h : F ⊆ F') : ∀ ts : List STerm, sumForms F ts ⊆ sumForms F' ts
  | [] => fun _ hp => hp
  | t :: ts => by
      intro p hp
      obtain ⟨p1, hp1, hm⟩ := List.mem_flatMap.mp hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      exact List.mem_flatMap.mpr ⟨p1, linForms_mono h t hp1,
        List.mem_map.mpr ⟨q, sumForms_mono h ts hq, rfl⟩⟩

theorem splitForms_mono (h : F ⊆ F') (t : STerm) : splitForms F t ⊆ splitForms F' t := by
  intro p hp
  cases t with
  | bin m x y =>
      simp only [splitForms, List.mem_append, List.mem_singleton] at hp ⊢
      rcases hp with hp | rfl
      · split_ifs at hp with hc
        · obtain ⟨rfl, hw⟩ := hc
          left
          rw [ite_eq_left ⟨rfl, widOk_mono h hw⟩]
          obtain ⟨p1, hp1, hm⟩ := List.mem_flatMap.mp hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          exact List.mem_flatMap.mpr ⟨p1, linForms_mono h x hp1,
            List.mem_map.mpr ⟨q, linForms_mono h y hq, rfl⟩⟩
        · simp at hp
      · exact Or.inr rfl
  | _ => simpa [splitForms] using hp

theorem splitsForms_mono (h : F ⊆ F') : ∀ ts : List STerm, splitsForms F ts ⊆ splitsForms F' ts
  | [] => fun _ hp => hp
  | t :: ts => by
      intro p hp
      obtain ⟨p1, hp1, hm⟩ := List.mem_flatMap.mp hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      exact List.mem_flatMap.mpr ⟨p1, splitForms_mono h t hp1,
        List.mem_map.mpr ⟨q, splitsForms_mono h ts hq, rfl⟩⟩

theorem affHi_anti (h : F ⊆ F') : ∀ L : List (STerm × Int), affHi F' L ≤ affHi F L
  | [] => le_rfl
  | p :: L => by
      have ih := affHi_anti h L
      have hh : ((hiOf F' F' p.1 : Nat) : Int) ≤ (hiOf F F p.1 : Int) :=
        Int.ofNat_le.mpr (hiOf_anti h h p.1)
      have hl : ((lbOf F p.1 : Nat) : Int) ≤ (lbOf F' p.1 : Int) :=
        Int.ofNat_le.mpr (lbOf_mono h p.1)
      simp only [affHi]
      split
      · rename_i hc
        have := Int.mul_le_mul_of_nonneg_left hh hc
        omega
      · rename_i hc
        have := Int.mul_le_mul_of_nonpos_left (by omega : p.2 ≤ 0) hl
        omega

theorem affLo_mono (h : F ⊆ F') : ∀ L : List (STerm × Int), affLo F L ≤ affLo F' L
  | [] => le_rfl
  | p :: L => by
      have ih := affLo_mono h L
      have hh : ((hiOf F' F' p.1 : Nat) : Int) ≤ (hiOf F F p.1 : Int) :=
        Int.ofNat_le.mpr (hiOf_anti h h p.1)
      have hl : ((lbOf F p.1 : Nat) : Int) ≤ (lbOf F' p.1 : Int) :=
        Int.ofNat_le.mpr (lbOf_mono h p.1)
      simp only [affLo]
      split
      · rename_i hc
        have := Int.mul_le_mul_of_nonneg_left hl hc
        omega
      · rename_i hc
        have := Int.mul_le_mul_of_nonpos_left (by omega : p.2 ≤ 0) hh
        omega

theorem affComb_mono (h : F ⊆ F') {m : String} {fx fy r : List (STerm × Int) × Int}
    (hc : affComb F m fx fy = some r) : affComb F' m fx fy = some r := by
  have hx := affHi_anti h fx.1
  have hy := affHi_anti h fy.1
  have hl := affLo_mono h (affAdd fx.1 (affScale (-1) fy.1))
  have hm : max (affHi F' fx.1 + fx.2) 0 * max (affHi F' fy.1 + fy.2) 0 ≤
      max (affHi F fx.1 + fx.2) 0 * max (affHi F fy.1 + fy.2) 0 :=
    mul_le_mul (max_le_max (by omega) le_rfl) (max_le_max (by omega) le_rfl)
      (le_max_right _ _) (le_max_right _ _)
  unfold affComb at hc ⊢
  split_ifs at hc ⊢ <;> first | exact hc | grind

theorem affForms_mono (h : F ⊆ F') : ∀ t : STerm, affForms F t ⊆ affForms F' t
  | .immW _ _ => fun _ hp => by simpa [affForms] using hp
  | .bin m x y => by
      intro p hp
      simp only [affForms] at hp ⊢
      split_ifs at hp with hw
      · rw [ite_eq_left ⟨widOk_mono h hw.1, widOk_mono h hw.2⟩]
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨fx, hfx, hm⟩ := List.mem_flatMap.mp hp
          obtain ⟨fy, hfy, hc⟩ := List.mem_filterMap.mp hm
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨fx, affForms_mono h x hfx,
            List.mem_filterMap.mpr ⟨fy, affForms_mono h y hfy, affComb_mono h hc⟩⟩)
        · exact List.mem_append_right _ hp
      · simp only [List.mem_singleton] at hp
        subst hp
        split_ifs <;> simp
  | .reg _ => fun _ hp => by simpa [affForms] using hp
  | .immAt _ _ => fun _ hp => by simpa [affForms] using hp
  | .un _ _ => fun _ hp => by simpa [affForms] using hp
  | .shImm _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .aget _ _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .cin _ => fun _ hp => by simpa [affForms] using hp
  | .aluF _ _ _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .carryW _ _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .carryF _ _ _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .mulx _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .cout _ _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .sel _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .setcc _ _ _ => fun _ hp => by simpa [affForms] using hp
  | .ref _ => fun _ hp => by simpa [affForms] using hp

theorem leBy_mono (h : F ⊆ F') {as : List STerm} {K : Int} {b' : Nat} {f : SFact}
    (hb : leBy F as K b' f = true) : leBy F' as K b' f = true := by
  cases f with
  | le ts b =>
      simp only [leBy] at hb ⊢
      split at hb
      · rename_i R hR
        have := lbSum_mono h R
        simp only [decide_eq_true_eq] at hb ⊢
        omega
      · cases hb
  | _ => simp [leBy] at hb

theorem leLin_mono (h : F ⊆ F') {ts : List STerm} {b' : Nat} (hl : leLin F ts b' = true) :
    leLin F' ts b' = true := by
  obtain ⟨p, hp, hl⟩ := List.any_eq_true.mp hl
  refine List.any_eq_true.mpr ⟨p, sumForms_mono h ts hp, ?_⟩
  simp only [Bool.or_eq_true, List.any_eq_true] at hl ⊢
  exact hl.imp id fun ⟨f, hf, hb⟩ => ⟨f, h hf, leBy_mono h hb⟩

theorem mulParts_mono (h : F ⊆ F') {a : STerm} {r : Nat × STerm}
    (hm : mulParts F a = some r) : mulParts F' a = some r := by
  unfold mulParts at hm ⊢
  split at hm
  · split_ifs at hm ⊢
    split at hm
    · exact hm
    · split at hm
      · split_ifs at hm with hc
        rw [ite_eq_left ⟨hc.1, widOk_mono h hc.2⟩]
        exact hm
      · cases hm
  · cases hm

theorem mulLe_mono (h : F ⊆ F') {ts : List STerm} {b' : Nat} (hl : mulLe F ts b' = true) :
    mulLe F' ts b' = true := by
  obtain ⟨p, hp, hl⟩ := List.any_eq_true.mp hl
  refine List.any_eq_true.mpr ⟨p, sumForms_mono h ts hp, ?_⟩
  split at hl
  · rename_i a ha
    split at hl
    · rename_i c x hc
      simp only [Bool.and_eq_true] at hl
      simp only [mulParts_mono h hc, hl.1, leLin_mono h hl.2, Bool.and_self]
    · cases hl
  · cases hl

theorem termHi_anti (h : F ⊆ F') (t : STerm) : termHi F' t ≤ termHi F t := by
  refine le_foldr_min ((foldr_min_le).trans (hiOf_anti h h t)) fun v hv => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  refine (foldr_min_le_of_mem (List.mem_map.mpr ⟨p, linForms_mono h t hp, rfl⟩)).trans ?_
  have : (p.1.map (hiOf F' F')).sum ≤ (p.1.map (hiOf F F)).sum :=
    List.sum_le_sum fun x _ => hiOf_anti h h x
  omega

theorem hiNe_anti (h : F ⊆ F') (t : STerm) : hiNe F' t ≤ hiNe F t := by
  have ht := termHi_anti h t
  unfold hiNe
  split_ifs with h1 h2 h2 <;> try omega
  rcases Nat.lt_or_ge (termHi F' t) (termHi F t) with hlt | hge
  · omega
  · have he : termHi F' t = termHi F t := le_antisymm ht hge
    exact absurd (he ▸ h h2) h1

theorem lbNe_mono (h : F ⊆ F') (t : STerm) : lbNe F t ≤ lbNe F' t := by
  have ht := lbOf_mono h t
  unfold lbNe
  split_ifs with h1 h2 h2 <;> try omega
  rcases Nat.lt_or_ge (lbOf F t) (lbOf F' t) with hlt | hge
  · omega
  · have he : lbOf F' t = lbOf F t := le_antisymm hge ht
    exact absurd (he ▸ h h1) h2

theorem hiLe_mono (h : F ⊆ F') {ts : List STerm} {b' : Nat} (hl : hiLe F ts b' = true) :
    hiLe F' ts b' = true := by
  simp only [hiLe, decide_eq_true_eq] at hl ⊢
  exact (List.sum_le_sum fun t _ => hiNe_anti h t).trans hl

theorem arrIn_mono (h : F ⊆ F') {a : SArr} {b : Nat} (hl : arrIn F a b = true) :
    arrIn F' a b = true := by
  obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp hl
  exact List.any_eq_true.mpr ⟨g, h hg, hb⟩

theorem arrOk_mono (h : F ⊆ F') {b : Nat} : ∀ {a : SArr}, arrOk F b a = true → arrOk F' b a = true
  | .cell _, hl => arrIn_mono h hl
  | .zero _ _, _ => rfl
  | .aset a w n i v, hl => by
      simp only [arrOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl ⊢
      exact hl.imp (arrIn_mono h) fun ⟨ha, hv⟩ => ⟨arrOk_mono h ha, (hiNe_anti h v).trans hv⟩

/-- **Entailment is monotone in the facts.** -/
theorem entails_mono (h : F ⊆ F') {g : SFact} (he : entails F g = true) :
    entails F' g = true := by
  cases g with
  | le ts b' =>
      simp only [entails, Bool.or_eq_true] at he ⊢
      exact he.imp (Or.imp (leLin_mono h) (mulLe_mono h)) (hiLe_mono h)
  | ge t k =>
      simp only [entails, decide_eq_true_eq] at he ⊢
      exact he.trans (lbNe_mono h t)
  | w64 t => exact widOk_mono h he
  | ne t c =>
      have h1 := lbOf_mono h t
      have h2 := hiNe_anti h t
      simp only [entails, Bool.or_eq_true, decide_eq_true_eq] at he ⊢
      rcases he with (he | he) | he
      · exact Or.inl (Or.inl (by omega))
      · exact Or.inl (Or.inr (by omega))
      · exact Or.inr (h he)
  | ale a b => exact arrOk_mono h he

/-- The bound `ubOf` is the bound of a single-term fact of `F`. -/
theorem ubOf_mem : ∀ {F : List SFact} {t : STerm} {u : Nat}, ubOf F t = some u →
    SFact.le [t] u ∈ F
  | [], _, _, hu => by cases hu
  | .le [t'] b :: F, t, u, hu => by
      simp only [ubOf] at hu
      split at hu
      · rename_i he
        subst he
        cases hu
        cases hv : ubOf F t' with
        | none => exact List.mem_cons_self
        | some v =>
            simp only [Option.elim]
            rcases min_choice b v with hm | hm <;> rw [hm]
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ubOf_mem hv)
      · exact List.mem_cons_of_mem _ (ubOf_mem hu)
  | .le [] _ :: F, _, _, hu => List.mem_cons_of_mem _ (ubOf_mem hu)
  | .le (_ :: _ :: _) _ :: F, _, _, hu => List.mem_cons_of_mem _ (ubOf_mem hu)
  | .ge _ _ :: F, _, _, hu => List.mem_cons_of_mem _ (ubOf_mem hu)
  | .w64 _ :: F, _, _, hu => List.mem_cons_of_mem _ (ubOf_mem hu)
  | .ne _ _ :: F, _, _, hu => List.mem_cons_of_mem _ (ubOf_mem hu)
  | .ale _ _ :: F, _, _, hu => List.mem_cons_of_mem _ (ubOf_mem hu)

/-- **`ubOf` is at most the bound of every single-term fact on its term**, in particular of the
    first one. -/
theorem ubOf_le_of_mem : ∀ {F : List SFact} {t : STerm} {b : Nat}, SFact.le [t] b ∈ F →
    ∃ u, ubOf F t = some u ∧ u ≤ b
  | [], _, _, hb => by cases hb
  | f :: F, t, b, hb => by
      have key : ∀ {t' : STerm} {b' : Nat}, (∃ u, ubOf F t = some u ∧ u ≤ b) →
          ∃ u, ubOf (.le [t'] b' :: F) t = some u ∧ u ≤ b := by
        intro t' b' ⟨u, hu, hle⟩
        simp only [ubOf]
        split
        · rename_i he
          subst he
          rw [hu]
          exact ⟨_, rfl, (min_le_right _ _).trans hle⟩
        · exact ⟨u, hu, hle⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · simp only [ubOf, ite_true]
        exact ⟨_, rfl, by cases ubOf F t <;> simp [Option.elim]⟩
      · have ih := ubOf_le_of_mem hb
        cases f with
        | le ts b' =>
            match ts, ih with
            | [t'], ih => exact key ih
            | [], ih => exact ih
            | _ :: _ :: _, ih => exact ih
        | ge _ _ => exact ih
        | w64 _ => exact ih
        | ne _ _ => exact ih
        | ale _ _ => exact ih

theorem ubSum_mono (h : F ⊆ F') : ∀ {ts : List STerm} {u : Nat}, ubSum F ts = some u →
    ∃ u', ubSum F' ts = some u' ∧ u' ≤ u
  | [], u, hu => ⟨0, rfl, by simp only [ubSum, Option.some.injEq] at hu; omega⟩
  | t :: ts, u, hu => by
      simp only [ubSum] at hu
      split at hu
      · rename_i a c ha hc
        cases hu
        obtain ⟨a', ha', hle⟩ := ubOf_le_of_mem (h (ubOf_mem ha))
        obtain ⟨c', hc', hle'⟩ := ubSum_mono h hc
        refine ⟨a' + c', ?_, by omega⟩
        simp only [ubSum, ha', hc']
      · cases hu

theorem leMixBy_mono (h : F ⊆ F') {as : List STerm} {K : Int} {b' : Nat} {f : SFact}
    (hb : leMixBy F as K b' f = true) : leMixBy F' as K b' f = true := by
  cases f with
  | le ts b =>
      simp only [leMixBy] at hb ⊢
      split at hb
      · rename_i u hu
        obtain ⟨u', hu', hle⟩ := ubSum_mono h hu
        rw [hu']
        have := lbSum_mono h (peel ts as).1
        simp only [decide_eq_true_eq] at hb ⊢
        omega
      · cases hb
  | _ => simp [leMixBy] at hb

theorem leMix_mono (h : F ⊆ F') {ts : List STerm} {b' : Nat} (hl : leMix F ts b' = true) :
    leMix F' ts b' = true := by
  obtain ⟨p, hp, hl⟩ := List.any_eq_true.mp hl
  obtain ⟨q, hq, hl⟩ := List.any_eq_true.mp hl
  obtain ⟨f, hf, hb⟩ := List.any_eq_true.mp hl
  exact List.any_eq_true.mpr ⟨p, sumForms_mono h ts hp, List.any_eq_true.mpr
    ⟨q, splitsForms_mono h p.1 hq, List.any_eq_true.mpr ⟨f, h hf, leMixBy_mono h hb⟩⟩⟩

theorem affLe_mono (h : F ⊆ F') {t : STerm} {b' : Nat} (hl : affLe F t b' = true) :
    affLe F' t b' = true := by
  obtain ⟨p, hp, hl⟩ := List.any_eq_true.mp hl
  refine List.any_eq_true.mpr ⟨p, affForms_mono h t hp, ?_⟩
  have := affHi_anti h p.1
  simp only [decide_eq_true_eq] at hl ⊢
  omega

/-- **The obligation check is monotone in the facts.** -/
theorem oblsOk_mono (h : F ⊆ F') {os : List SObl} (ho : oblsOk F os = true) :
    oblsOk F' os = true := by
  simp only [oblsOk, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true] at ho ⊢
  intro o hmem
  obtain ⟨hn, he⟩ := ho o hmem
  exact ⟨hn, he.imp (Or.imp (entails_mono h) (leMix_mono h)) (affLe_mono h)⟩

/-- **The successor check is monotone in the facts.** -/
theorem succOk_mono (h : F ⊆ F') {ss : SSt} {fs : List IdxFact} (ho : succOk F ss fs = true) :
    succOk F' ss fs = true := by
  simp only [succOk, List.all_eq_true] at ho ⊢
  exact fun f hf => entails_mono h (ho f hf)

end Mono

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
