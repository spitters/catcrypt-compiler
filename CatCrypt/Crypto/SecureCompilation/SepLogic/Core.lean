/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.ByteMem
public import Lean

/-!
# Separation logic with footprints over total states

An assertion `SAssert σ L` over a total state `σ` carries a footprint `fp : Set L` of
locations, a predicate `holds`, and a support proof `supp`: two states that agree on the
footprint (`Footprinted.AgreeOn`) satisfy the assertion together. The separating conjunction
`P ∗ Q` takes the union of the footprints and adds their disjointness as a pure conjunct;
entailment `P ⊢ₛ Q` says that every state satisfying `P` satisfies `Q` and that the footprint
of `Q` is then contained in that of `P`. The logic is affine: `P ∗ Q ⊢ₛ P`.

A state transformer `f` writes in `W` (`WritesIn f W`) when `f s` agrees with `s` outside
`W s`. `Triple P f Q` is the total, deterministic Hoare triple. The frame rule
`Triple.frame` follows from `WritesIn` and the support of the frame.

Chains of `∗` are represented as lists, `bigSep : List (SAssert σ L) → SAssert σ L`. The
tactic `sep_cancel` proves entailments `bigSep hs ⊢ₛ bigSep gs` between list literals: it
flattens nested `∗`, `bigSep` and `emp` atoms, moves pure hypotheses into the local context,
cancels each goal atom against a hypothesis atom that is equal up to reducible definitional
equality (or that has the same head and whose argument equalities close by `rfl`,
`assumption`, `bv_omega` or `omega`), drops the remaining hypothesis atoms, and leaves
unproved pure facts and unmatched atoms as goals. Each step applies one lemma whose list
side conditions are closed by `rfl` on list literals; there is no rewriting on a tree of `∗`.

The byte-memory instance: `MemW A` is footprinted over `BitVec A`; `ptsLE n a v` is the
little-endian points-to assertion on the range `⟨a, n⟩`.

## Main definitions

* `Footprinted`, `SAssert`, `SAssert.Entails` (`⊢ₛ`), `SAssert.sep` (`∗`), `SAssert.pure`
  (`⌜φ⌝`), `SAssert.emp`, `SAssert.own`, `SAssert.sexists`, `SAssert.bigSep`.
* `WritesIn`, `iterWrites`, `whileFuel`, `Triple`.
* `ptsLE`: the points-to assertion of `MemW A`.
* `sep_cancel`: the entailment tactic.

## Main results

* `SAssert.sep_comm`, `SAssert.sep_assoc`, `SAssert.sep_mono`,
  `SAssert.sep_disj`, `SAssert.sep_elim_left`, `SAssert.sep_elim_right`.
* `SAssert.holds_bigSep`, `SAssert.bigSep_perm`, `SAssert.bigSep_append`: the big separating
  conjunction, its permutation invariance, and split/merge along `++`.
* `WritesIn.comp`, `WritesIn.iterate`, `WritesIn.whileFuel`: write sets of sequencing and
  of fuel-bounded iteration.
* `Triple.frame`: the frame rule.
* `writesIn_writeLE`, `triple_writeLE`, `ptsLE_disj`: the byte-memory write writes in its
  range and establishes its points-to assertion; separated points-to ranges are disjoint.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

universe u v w

/-- A state type `σ` whose states can be compared on sets of locations `L`. `AgreeOn S s t`
    says that `s` and `t` agree on every location of `S`; it is an equivalence relation for
    each `S` and antitone in `S`. -/
class Footprinted (σ : Type u) (L : outParam (Type v)) where
  /-- The states agree on every location of the set. -/
  AgreeOn : Set L → σ → σ → Prop
  agreeOn_refl : ∀ (S : Set L) (s : σ), AgreeOn S s s
  agreeOn_symm : ∀ {S : Set L} {s t : σ}, AgreeOn S s t → AgreeOn S t s
  agreeOn_trans : ∀ {S : Set L} {s t r : σ}, AgreeOn S s t → AgreeOn S t r → AgreeOn S s r
  agreeOn_anti : ∀ {S T : Set L} {s t : σ}, S ⊆ T → AgreeOn T s t → AgreeOn S s t

open Footprinted

/-- Functions agree on a set of arguments when they agree pointwise on it. -/
instance instFootprintedFun (α : Type u) (β : Type v) : Footprinted (α → β) α where
  AgreeOn S f g := ∀ x ∈ S, f x = g x
  agreeOn_refl _ _ _ _ := rfl
  agreeOn_symm h x hx := (h x hx).symm
  agreeOn_trans h h' x hx := (h x hx).trans (h' x hx)
  agreeOn_anti hST h x hx := h x (hST hx)

/-- An assertion over states `σ` with footprint `fp`: `holds` is determined by the
    locations of `fp`. -/
structure SAssert (σ : Type u) (L : Type v) [Footprinted σ L] where
  /-- The footprint. -/
  fp : Set L
  /-- The predicate on states. -/
  holds : σ → Prop
  /-- States that agree on the footprint satisfy the assertion together. -/
  supp : ∀ s t, AgreeOn fp s t → holds s → holds t

namespace SAssert

variable {σ : Type u} {L : Type v} [Footprinted σ L]

/-- Entailment: every state satisfying `P` satisfies `Q`, and the footprint of `Q` is then
    contained in that of `P`. -/
def Entails (P Q : SAssert σ L) : Prop := ∀ s, P.holds s → Q.holds s ∧ Q.fp ⊆ P.fp

@[inherit_doc] scoped infix:25 " ⊢ₛ " => Entails

/-- Mutual entailment. -/
def Equiv (P Q : SAssert σ L) : Prop := (P ⊢ₛ Q) ∧ (Q ⊢ₛ P)

@[inherit_doc] scoped infix:25 " ⊣⊢ₛ " => Equiv

theorem Entails.refl (P : SAssert σ L) : P ⊢ₛ P := fun _ h => ⟨h, subset_rfl⟩

theorem Entails.trans {P Q R : SAssert σ L} (h₁ : P ⊢ₛ Q) (h₂ : Q ⊢ₛ R) : P ⊢ₛ R :=
  fun s h => ⟨(h₂ s (h₁ s h).1).1, (h₂ s (h₁ s h).1).2.trans (h₁ s h).2⟩

/-- The separating conjunction: union of the footprints, which must be disjoint. -/
def sep (P Q : SAssert σ L) : SAssert σ L where
  fp := P.fp ∪ Q.fp
  holds s := Disjoint P.fp Q.fp ∧ P.holds s ∧ Q.holds s
  supp s t h := fun ⟨hd, hp, hq⟩ =>
    ⟨hd, P.supp s t (agreeOn_anti Set.subset_union_left h) hp,
      Q.supp s t (agreeOn_anti Set.subset_union_right h) hq⟩

@[inherit_doc] scoped infixr:70 " ∗ " => sep

/-- A pure assertion: empty footprint. -/
def pure (φ : Prop) : SAssert σ L where
  fp := ∅
  holds _ := φ
  supp _ _ _ h := h

@[inherit_doc] scoped notation "⌜" φ "⌝" => pure φ

/-- The empty assertion. -/
def emp : SAssert σ L := pure True

/-- Ownership of the locations `S`, with no constraint on their contents. -/
def own (S : Set L) : SAssert σ L where
  fp := S
  holds _ := True
  supp _ _ _ h := h

/-- The existential over a family of assertions with one fixed footprint `F`. -/
def sexists {α : Sort w} (F : Set L) (P : α → SAssert σ L) (hP : ∀ x, (P x).fp = F) :
    SAssert σ L where
  fp := F
  holds s := ∃ x, (P x).holds s
  supp s t h := fun ⟨x, hx⟩ => ⟨x, (P x).supp s t (by rw [hP]; exact h) hx⟩

/-- The big separating conjunction of a list. -/
def bigSep : List (SAssert σ L) → SAssert σ L
  | [] => emp
  | P :: l => P ∗ bigSep l

@[simp] theorem fp_sep (P Q : SAssert σ L) : (P ∗ Q).fp = P.fp ∪ Q.fp := rfl
@[simp] theorem holds_sep (P Q : SAssert σ L) (s : σ) :
    (P ∗ Q).holds s ↔ Disjoint P.fp Q.fp ∧ P.holds s ∧ Q.holds s := Iff.rfl
@[simp] theorem fp_pure (φ : Prop) : (⌜φ⌝ : SAssert σ L).fp = ∅ := rfl
@[simp] theorem holds_pure (φ : Prop) (s : σ) : (⌜φ⌝ : SAssert σ L).holds s ↔ φ := Iff.rfl
@[simp] theorem fp_emp : (emp : SAssert σ L).fp = ∅ := rfl
@[simp] theorem holds_emp (s : σ) : (emp : SAssert σ L).holds s := trivial
@[simp] theorem fp_own (S : Set L) : (own S : SAssert σ L).fp = S := rfl
@[simp] theorem holds_own (S : Set L) (s : σ) : (own S : SAssert σ L).holds s := trivial
@[simp] theorem bigSep_nil : bigSep ([] : List (SAssert σ L)) = emp := rfl
@[simp] theorem bigSep_cons (P : SAssert σ L) (l : List (SAssert σ L)) :
    bigSep (P :: l) = P ∗ bigSep l := rfl

/-! ## Laws of the separating conjunction -/

theorem sep_comm (P Q : SAssert σ L) : P ∗ Q ⊢ₛ Q ∗ P :=
  fun _ ⟨hd, hp, hq⟩ => ⟨⟨hd.symm, hq, hp⟩, (Set.union_comm _ _).le⟩

theorem sep_assoc (P Q R : SAssert σ L) : (P ∗ Q) ∗ R ⊣⊢ₛ P ∗ (Q ∗ R) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨hd, ⟨hd', hp, hq⟩, hr⟩
    replace hd := Set.disjoint_union_left.1 hd
    exact ⟨⟨Set.disjoint_union_right.2 ⟨hd', hd.1⟩, hp, hd.2, hq, hr⟩,
      (Set.union_assoc _ _ _).ge⟩
  · rintro _ ⟨hd, hp, hd', hq, hr⟩
    replace hd := Set.disjoint_union_right.1 hd
    exact ⟨⟨Set.disjoint_union_left.2 ⟨hd.2, hd'⟩, ⟨hd.1, hp, hq⟩, hr⟩,
      (Set.union_assoc _ _ _).le⟩

theorem sep_mono {P P' Q Q' : SAssert σ L} (hP : P ⊢ₛ P') (hQ : Q ⊢ₛ Q') : P ∗ Q ⊢ₛ P' ∗ Q' :=
  fun s ⟨hd, hp, hq⟩ =>
    ⟨⟨hd.mono (hP s hp).2 (hQ s hq).2, (hP s hp).1, (hQ s hq).1⟩,
      Set.union_subset_union (hP s hp).2 (hQ s hq).2⟩

/-- The footprints of the two sides of a satisfied separating conjunction are disjoint. -/
theorem sep_disj {P Q : SAssert σ L} {s : σ} (h : (P ∗ Q).holds s) : Disjoint P.fp Q.fp := h.1

theorem sep_elim_left (P Q : SAssert σ L) : P ∗ Q ⊢ₛ P :=
  fun _ h => ⟨h.2.1, Set.subset_union_left⟩

theorem sep_elim_right (P Q : SAssert σ L) : P ∗ Q ⊢ₛ Q :=
  fun _ h => ⟨h.2.2, Set.subset_union_right⟩

theorem emp_sep (P : SAssert σ L) : P ⊢ₛ emp ∗ P :=
  fun _ h => ⟨⟨Set.empty_disjoint _, trivial, h⟩, by simp⟩

theorem sep_emp (P : SAssert σ L) : P ⊢ₛ P ∗ emp :=
  fun _ h => ⟨⟨Set.disjoint_empty _, h, trivial⟩, by simp⟩

/-- Ownership of `S` entails ownership of a subset of `S`. -/
theorem own_mono {S S' : Set L} (h : S' ⊆ S) : (own S : SAssert σ L) ⊢ₛ own S' :=
  fun _ _ => ⟨trivial, h⟩

theorem entails_sexists {α : Sort w} {F : Set L} {P : α → SAssert σ L}
    {hP : ∀ x, (P x).fp = F} (x : α) : P x ⊢ₛ sexists F P hP :=
  fun _ h => ⟨⟨x, h⟩, (hP x).symm.le⟩

theorem sexists_entails {α : Sort w} {F : Set L} {P : α → SAssert σ L}
    {hP : ∀ x, (P x).fp = F} {Q : SAssert σ L} (h : ∀ x, P x ⊢ₛ Q) : sexists F P hP ⊢ₛ Q :=
  fun s ⟨x, hx⟩ => ⟨(h x s hx).1, (hP x) ▸ (h x s hx).2⟩

/-! ## The big separating conjunction -/

theorem mem_fp_bigSep {l : List (SAssert σ L)} {x : L} :
    x ∈ (bigSep l).fp ↔ ∃ P ∈ l, x ∈ P.fp := by
  induction l with
  | nil => simp
  | cons P l ih => simp [ih]

theorem disjoint_fp_bigSep {X : Set L} {l : List (SAssert σ L)} :
    Disjoint X (bigSep l).fp ↔ ∀ P ∈ l, Disjoint X P.fp := by
  induction l with
  | nil => simp
  | cons P l ih => simp [Set.disjoint_union_right, ih]

/-- A list satisfies the big separating conjunction when its footprints are pairwise
    disjoint and each member holds. -/
theorem holds_bigSep {l : List (SAssert σ L)} {s : σ} :
    (bigSep l).holds s ↔
      l.Pairwise (fun P Q => Disjoint P.fp Q.fp) ∧ ∀ P ∈ l, P.holds s := by
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [bigSep_cons, holds_sep, ih, disjoint_fp_bigSep, List.pairwise_cons,
      List.forall_mem_cons]
    tauto

/-- The big separating conjunction is invariant under permutation. -/
theorem bigSep_perm {l l' : List (SAssert σ L)} (p : l.Perm l') : bigSep l ⊢ₛ bigSep l' := by
  intro s h
  rw [holds_bigSep] at h ⊢
  refine ⟨⟨(p.pairwise_iff fun h => Disjoint.symm h).1 h.1, fun P hP => h.2 P (p.mem_iff.2 hP)⟩,
    fun x hx => ?_⟩
  obtain ⟨P, hP, hx⟩ := mem_fp_bigSep.1 hx
  exact mem_fp_bigSep.2 ⟨P, p.mem_iff.2 hP, hx⟩

/-- The big separating conjunction of `l₁ ++ l₂` splits into, and merges from, the two
    big separating conjunctions. -/
theorem bigSep_append (l₁ l₂ : List (SAssert σ L)) :
    bigSep (l₁ ++ l₂) ⊣⊢ₛ bigSep l₁ ∗ bigSep l₂ := by
  refine ⟨fun s h => ?_, ?_⟩
  swap
  · rintro s ⟨hd, h₁, h₂⟩
    rw [holds_bigSep] at h₁ h₂
    refine ⟨holds_bigSep.2 ⟨List.pairwise_append.2 ⟨h₁.1, h₂.1, fun P hP Q hQ => ?_⟩,
      fun P hP => (List.mem_append.1 hP).elim (h₁.2 P) (h₂.2 P)⟩, fun x hx => ?_⟩
    · have := (disjoint_fp_bigSep.1 hd) Q hQ
      rw [disjoint_comm] at this
      exact ((disjoint_fp_bigSep.1 this) P hP).symm
    · obtain ⟨P, hP, hx⟩ := mem_fp_bigSep.1 hx
      rcases List.mem_append.1 hP with hP | hP
      · exact Or.inl (mem_fp_bigSep.2 ⟨P, hP, hx⟩)
      · exact Or.inr (mem_fp_bigSep.2 ⟨P, hP, hx⟩)
  · rw [holds_bigSep, List.pairwise_append] at h
    refine ⟨⟨?_, holds_bigSep.2 ⟨h.1.1, fun P hP => h.2 P (List.mem_append_left _ hP)⟩,
      holds_bigSep.2 ⟨h.1.2.1, fun P hP => h.2 P (List.mem_append_right _ hP)⟩⟩, ?_⟩
    · refine disjoint_fp_bigSep.2 fun Q hQ => ?_
      rw [disjoint_comm]
      exact disjoint_fp_bigSep.2 fun P hP => (h.1.2.2 P hP Q hQ).symm
    · intro x hx
      rcases hx with hx | hx <;> obtain ⟨P, hP, hx⟩ := mem_fp_bigSep.1 hx <;>
        exact mem_fp_bigSep.2 ⟨P, by simp [hP], hx⟩

theorem sep_entails_bigSep (P Q : SAssert σ L) : P ∗ Q ⊢ₛ bigSep [P, Q] :=
  sep_mono (Entails.refl P) (sep_emp Q)

theorem bigSep_entails_sep (P Q : SAssert σ L) : bigSep [P, Q] ⊢ₛ P ∗ Q :=
  sep_mono (Entails.refl P) (sep_elim_left Q emp)

/-- Replacing a member `X` of a big separating conjunction by a list `Y` that `X` entails. -/
theorem bigSep_congr_at (l₁ l₂ : List (SAssert σ L)) (X : SAssert σ L)
    (Y : List (SAssert σ L)) (h : X ⊢ₛ bigSep Y) :
    bigSep (l₁ ++ X :: l₂) ⊢ₛ bigSep (l₁ ++ Y ++ l₂) :=
  (bigSep_perm List.perm_middle).trans <|
    (sep_mono h (Entails.refl _)).trans <| (bigSep_append _ _).2.trans <|
      bigSep_perm (by
        simpa [List.append_assoc] using List.perm_append_comm_assoc Y l₁ l₂)

/-- Replacing a sublist `Y` of a big separating conjunction by an assertion `X` that it
    entails. -/
theorem bigSep_collapse_at (l₁ l₂ : List (SAssert σ L)) (X : SAssert σ L)
    (Y : List (SAssert σ L)) (h : bigSep Y ⊢ₛ X) :
    bigSep (l₁ ++ Y ++ l₂) ⊢ₛ bigSep (l₁ ++ X :: l₂) :=
  (bigSep_perm (by
        simpa [List.append_assoc] using List.perm_append_comm_assoc l₁ Y l₂)).trans <|
    (bigSep_append _ _).1.trans <| (sep_mono h (Entails.refl _)).trans <|
      bigSep_perm List.perm_middle.symm

/-! ## Steps of the cancellation procedure

Each lemma takes the list literals it produces as explicit arguments and relates them to the
goal's lists by equations that `sep_cancel` closes by `rfl`. -/

theorem cancel_at (l₁ l₂ gs rest : List (SAssert σ L)) (h : SAssert σ L)
    {hs : List (SAssert σ L)} (e₁ : hs = l₁ ++ h :: l₂) (e₂ : rest = l₁ ++ l₂)
    (k : bigSep rest ⊢ₛ bigSep gs) : bigSep hs ⊢ₛ bigSep (h :: gs) := by
  subst e₁ e₂
  exact (bigSep_perm List.perm_middle).trans (sep_mono (Entails.refl h) k)

theorem cancel_eq_at (l₁ l₂ gs rest : List (SAssert σ L)) (h g : SAssert σ L)
    {hs : List (SAssert σ L)} (e₁ : hs = l₁ ++ h :: l₂) (e₂ : rest = l₁ ++ l₂)
    (hg : h = g) (k : bigSep rest ⊢ₛ bigSep gs) : bigSep hs ⊢ₛ bigSep (g :: gs) :=
  hg ▸ cancel_at l₁ l₂ gs rest h e₁ e₂ k

theorem pure_left_at (l₁ l₂ rest : List (SAssert σ L)) (φ : Prop)
    {hs : List (SAssert σ L)} {G : SAssert σ L} (e₁ : hs = l₁ ++ ⌜φ⌝ :: l₂)
    (e₂ : rest = l₁ ++ l₂) (k : φ → bigSep rest ⊢ₛ G) : bigSep hs ⊢ₛ G := by
  subst e₁ e₂
  intro s h
  have h₁ := bigSep_perm List.perm_middle s h
  obtain ⟨hG, hfp⟩ := k h₁.1.2.1 s h₁.1.2.2
  exact ⟨hG, hfp.trans (Set.subset_union_right.trans h₁.2)⟩

theorem pure_right (φ : Prop) (gs : List (SAssert σ L)) {hs : List (SAssert σ L)}
    (hφ : φ) (k : bigSep hs ⊢ₛ bigSep gs) : bigSep hs ⊢ₛ bigSep (⌜φ⌝ :: gs) :=
  fun s h => ⟨⟨Set.empty_disjoint _, hφ, (k s h).1⟩,
    Set.union_subset (Set.empty_subset _) (k s h).2⟩

theorem flatten_left_at (l₁ l₂ rest : List (SAssert σ L)) (X : SAssert σ L)
    (Y : List (SAssert σ L)) (hX : X ⊢ₛ bigSep Y) {hs : List (SAssert σ L)}
    {G : SAssert σ L} (e₁ : hs = l₁ ++ X :: l₂) (e₂ : rest = l₁ ++ Y ++ l₂)
    (k : bigSep rest ⊢ₛ G) : bigSep hs ⊢ₛ G := by
  subst e₁ e₂
  exact (bigSep_congr_at l₁ l₂ X Y hX).trans k

theorem flatten_right_at (l₁ l₂ rest : List (SAssert σ L)) (X : SAssert σ L)
    (Y : List (SAssert σ L)) (hX : bigSep Y ⊢ₛ X) {hs gs : List (SAssert σ L)}
    (e₁ : gs = l₁ ++ X :: l₂) (e₂ : rest = l₁ ++ Y ++ l₂)
    (k : bigSep hs ⊢ₛ bigSep rest) : bigSep hs ⊢ₛ bigSep gs := by
  subst e₁ e₂
  exact k.trans (bigSep_collapse_at l₁ l₂ X Y hX)

theorem rot_right (gs rest : List (SAssert σ L)) (g : SAssert σ L) {hs : List (SAssert σ L)}
    (e : rest = gs ++ [g]) (k : bigSep hs ⊢ₛ bigSep rest) : bigSep hs ⊢ₛ bigSep (g :: gs) := by
  subst e
  exact k.trans (bigSep_perm (List.perm_append_singleton g gs))

theorem entails_nil_right {hs : List (SAssert σ L)} :
    bigSep hs ⊢ₛ bigSep ([] : List (SAssert σ L)) :=
  fun _ _ => ⟨trivial, Set.empty_subset _⟩

theorem entails_of_bigSep_single {P Q : SAssert σ L} (h : bigSep [P] ⊢ₛ bigSep [Q]) :
    P ⊢ₛ Q :=
  (sep_emp P).trans <| h.trans (sep_elim_left Q emp)

theorem entails_of_bigSep_left {P : SAssert σ L} {gs : List (SAssert σ L)}
    (h : bigSep [P] ⊢ₛ bigSep gs) : P ⊢ₛ bigSep gs :=
  (sep_emp P).trans h

theorem entails_of_bigSep_right {hs : List (SAssert σ L)} {Q : SAssert σ L}
    (h : bigSep hs ⊢ₛ bigSep [Q]) : bigSep hs ⊢ₛ Q :=
  h.trans (sep_elim_left Q emp)

end SAssert

/-! ## Write sets and triples -/

section Triples

variable {σ : Type u} {L : Type v} [Footprinted σ L]

open SAssert

/-- `f` writes in the state-dependent set `W`: `f s` agrees with `s` outside `W s`. -/
def WritesIn (f : σ → σ) (W : σ → Set L) : Prop := ∀ s, AgreeOn (W s)ᶜ s (f s)

theorem WritesIn.mono {f : σ → σ} {W W' : σ → Set L} (h : WritesIn f W)
    (hW : ∀ s, W s ⊆ W' s) : WritesIn f W' :=
  fun s => agreeOn_anti (Set.compl_subset_compl.2 (hW s)) (h s)

theorem WritesIn.id : WritesIn (id : σ → σ) (fun _ => (∅ : Set L)) :=
  fun s => agreeOn_refl _ s

/-- Sequencing: `g ∘ f` writes in the writes of `f` at `s` and of `g` at `f s`. -/
theorem WritesIn.comp {f g : σ → σ} {W V : σ → Set L} (hf : WritesIn f W)
    (hg : WritesIn g V) : WritesIn (g ∘ f) (fun s => W s ∪ V (f s)) := fun s =>
  agreeOn_trans (agreeOn_anti (Set.compl_subset_compl.2 Set.subset_union_left) (hf s))
    (agreeOn_anti (Set.compl_subset_compl.2 Set.subset_union_right) (hg (f s)))

/-- The writes of the first `n` iterations of `f` from `s`. -/
def iterWrites (f : σ → σ) (W : σ → Set L) : Nat → σ → Set L
  | 0, _ => ∅
  | n + 1, s => W s ∪ iterWrites f W n (f s)

/-- `n` iterations of `f` write in `iterWrites f W n`. -/
theorem WritesIn.iterate {f : σ → σ} {W : σ → Set L} (hf : WritesIn f W) (n : Nat) :
    WritesIn (f^[n]) (iterWrites f W n) := by
  induction n with
  | zero => exact fun s => agreeOn_refl _ s
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    exact WritesIn.comp hf ih s

/-- The loop `while c do f` with at most `n` iterations. -/
def whileFuel (c : σ → Bool) (f : σ → σ) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => if c s then whileFuel c f n (f s) else s

/-- A fuel-bounded loop writes in the writes of the first `n` iterations of its body. -/
theorem WritesIn.whileFuel {c : σ → Bool} {f : σ → σ} {W : σ → Set L} (hf : WritesIn f W)
    (n : Nat) : WritesIn (SepLogic.whileFuel c f n) (iterWrites f W n) := by
  induction n with
  | zero => exact fun s => agreeOn_refl _ s
  | succ n ih =>
    intro s
    simp only [SepLogic.whileFuel]
    split
    · exact WritesIn.comp hf ih s
    · exact agreeOn_refl _ s

/-- The total, deterministic Hoare triple. -/
def Triple (P : SAssert σ L) (f : σ → σ) (Q : SAssert σ L) : Prop :=
  ∀ s, P.holds s → Q.holds (f s)

theorem Triple.conseq {P P' Q Q' : SAssert σ L} {f : σ → σ} (hP : P' ⊢ₛ P)
    (h : Triple P f Q) (hQ : Q ⊢ₛ Q') : Triple P' f Q' :=
  fun s hs => (hQ _ (h s (hP s hs).1)).1

theorem Triple.comp {P Q R : SAssert σ L} {f g : σ → σ} (hf : Triple P f Q)
    (hg : Triple Q g R) : Triple P (g ∘ f) R :=
  fun s hs => hg _ (hf s hs)

/-- The frame rule: if `f` writes only inside the footprint of `P` and the footprint of `Q`
    lies in that of `P`, a frame `R` separated from `P` is preserved. -/
theorem Triple.frame {P Q : SAssert σ L} {f : σ → σ} {W : σ → Set L} (R : SAssert σ L)
    (h : Triple P f Q) (hW : WritesIn f W) (hWP : ∀ s, P.holds s → W s ⊆ P.fp)
    (hQ : Q.fp ⊆ P.fp) : Triple (P ∗ R) f (Q ∗ R) := by
  rintro s ⟨hd, hp, hr⟩
  refine ⟨hd.mono_left hQ, h s hp, R.supp s (f s) (agreeOn_anti ?_ (hW s)) hr⟩
  exact fun x hx hxW => Set.disjoint_left.1 hd (hWP s hp hxW) hx

end Triples

/-! ## Byte memory -/

section ByteMem

open SAssert

variable {A : Nat}

/-- The little-endian points-to assertion: the `n` bytes at `a` hold `v`. -/
def ptsLE (n : Nat) (a : BitVec A) (v : BitVec (8 * n)) : SAssert (MemW A) (BitVec A) where
  fp := (⟨a, n⟩ : Rng A).toSet
  holds m := readLE n m a = v
  supp _ _ h hm := (readLE_congr n a h).symm.trans hm

@[simp] theorem fp_ptsLE (n : Nat) (a : BitVec A) (v : BitVec (8 * n)) :
    (ptsLE n a v).fp = (⟨a, n⟩ : Rng A).toSet := rfl

@[simp] theorem holds_ptsLE (n : Nat) (a : BitVec A) (v : BitVec (8 * n)) (m : MemW A) :
    (ptsLE n a v).holds m ↔ readLE n m a = v := Iff.rfl

/-- The write of `n` bytes at `a` writes in the range `⟨a, n⟩`. -/
theorem writesIn_writeLE (n : Nat) (a : BitVec A) (v : BitVec (8 * n)) :
    WritesIn (fun m : MemW A => writeLE n m a v) (fun _ => (⟨a, n⟩ : Rng A).toSet) :=
  fun m _ hx => (writeLE_outside n m a v hx).symm

/-- The write of `n ≤ 2^A` bytes at `a` turns `a ↦ x` into `a ↦ v`. -/
theorem triple_writeLE (n : Nat) (a : BitVec A) (x v : BitVec (8 * n)) (hn : n ≤ 2 ^ A) :
    Triple (ptsLE n a x) (fun m : MemW A => writeLE n m a v) (ptsLE n a v) :=
  fun m _ => readLE_writeLE_same n m a v hn

/-- Separated nonempty points-to assertions have disjoint ranges. -/
theorem ptsLE_disj {n k : Nat} {a b : BitVec A} {v : BitVec (8 * n)} {w : BitVec (8 * k)}
    {m : MemW A} (h : (ptsLE n a v ∗ ptsLE k b w).holds m) (hn : 0 < n) (hk : 0 < k) :
    (⟨a, n⟩ : Rng A).Disj ⟨b, k⟩ :=
  Rng.disj_of_disjoint hn hk h.1

end ByteMem

/-! ## The tactic `sep_cancel` -/

namespace SepCancel

open Lean Meta Elab Tactic

/-- The elements of a list literal built from `List.cons` and `List.nil`. -/
meta partial def listLit? (e : Expr) : MetaM (Option (List Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``List.nil 1 then
    return some []
  else if e.isAppOfArity ``List.cons 3 then
    match ← listLit? e.appArg! with
    | some t => return some (e.appFn!.appArg! :: t)
    | none => return none
  else
    return none

/-- The two lists of a goal `bigSep hs ⊢ₛ bigSep gs`, with the element type. -/
meta def goalLists (g : MVarId) : MetaM (Expr × List Expr × List Expr) := do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SAssert.Entails 5 do
    throwError "sep_cancel: the goal is not an entailment `_ ⊢ₛ _`{indentExpr t}"
  let P := t.appFn!.appArg!
  let Q := t.appArg!
  unless P.isAppOfArity ``SAssert.bigSep 4 && Q.isAppOfArity ``SAssert.bigSep 4 do
    throwError "sep_cancel: both sides must be `bigSep` of a list{indentExpr t}"
  let some hs ← listLit? P.appArg! | throwError "sep_cancel: not a list literal{indentExpr P}"
  let some gs ← listLit? Q.appArg! | throwError "sep_cancel: not a list literal{indentExpr Q}"
  let lty ← whnfR (← inferType P.appArg!)
  return (lty.appArg!, hs, gs)

/-- The proposition of a pure atom `⌜φ⌝`. -/
meta def pureArg? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``SAssert.pure 4 then some e.appArg! else none

/-- A flattening of an atom: the list `Y` replacing it and the two entailments between the
    atom and `bigSep Y`. -/
meta def flatten? (x : Expr) : MetaM (Option (List Expr × Expr × Expr)) := do
  if x.isAppOfArity ``SAssert.sep 5 then
    let P := x.appFn!.appArg!
    let Q := x.appArg!
    return some ([P, Q], ← mkAppM ``SAssert.sep_entails_bigSep #[P, Q],
      ← mkAppM ``SAssert.bigSep_entails_sep #[P, Q])
  else if x.isAppOfArity ``SAssert.bigSep 4 then
    match ← listLit? x.appArg! with
    | some m =>
      let r ← mkAppM ``SAssert.Entails.refl #[x]
      return some (m, r, r)
    | none => return none
  else if x.isAppOfArity ``SAssert.emp 3 then
    let r ← mkAppM ``SAssert.Entails.refl #[x]
    return some ([], r, r)
  else
    return none

/-- Apply `e` to `g`, close the list equations among the new goals by `rfl`, and return the
    other new goals. -/
meta def applyStep (g : MVarId) (e : Expr) : MetaM (List MVarId) := do
  let gs ← g.apply e
  let mut rest := []
  for h in gs do
    if ← h.isAssigned then continue
    let ty ← instantiateMVars (← h.getType)
    let isListEq ← if ty.isAppOfArity ``Eq 3 then
        pure ((← whnfR ty.appFn!.appFn!.appArg!).isAppOf ``List)
      else
        pure false
    if isListEq then
      h.refl
    else
      rest := rest ++ [h]
  return rest

/-- The closing tactic for side goals: equalities of atoms and pure facts. -/
meta def closeSide (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| first
      | assumption | exact True.intro | (show _ = _; rfl) | bv_omega | omega
      | (show _ = _; congr 1 <;> first | assumption | (show _ = _; rfl) | bv_omega | omega)))
    if (← getUnsolvedGoals).isEmpty then
      return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Flatten the hypothesis list: pure atoms go to the context, nested atoms are spliced. -/
meta partial def flattenLeft (g : MVarId) : TacticM MVarId := do
  let (T, hs, _) ← goalLists g
  for i in [0:hs.length] do
    let x := hs[i]!
    let l₁ ← mkListLit T (hs.take i)
    let l₂ ← mkListLit T (hs.drop (i + 1))
    if let some φ := pureArg? x then
      let rest ← mkListLit T (hs.eraseIdx i)
      let [k] ← applyStep g (← mkAppM ``SAssert.pure_left_at #[l₁, l₂, rest, φ])
        | throwError "sep_cancel: unexpected goals after `pure_left_at`"
      let (_, k) ← k.intro1
      return ← flattenLeft k
    if let some (Y, hX, _) ← flatten? x then
      let rest ← mkListLit T (hs.take i ++ Y ++ hs.drop (i + 1))
      let [k] ← applyStep g
          (← mkAppM ``SAssert.flatten_left_at #[l₁, l₂, rest, x, ← mkListLit T Y, hX])
        | throwError "sep_cancel: unexpected goals after `flatten_left_at`"
      return ← flattenLeft k
  return g

/-- Flatten the goal list: nested atoms are spliced. -/
meta partial def flattenRight (g : MVarId) : TacticM MVarId := do
  let (T, _, gs) ← goalLists g
  for i in [0:gs.length] do
    let x := gs[i]!
    if let some (Y, _, hX) ← flatten? x then
      let l₁ ← mkListLit T (gs.take i)
      let l₂ ← mkListLit T (gs.drop (i + 1))
      let rest ← mkListLit T (gs.take i ++ Y ++ gs.drop (i + 1))
      let [k] ← applyStep g
          (← mkAppM ``SAssert.flatten_right_at #[l₁, l₂, rest, x, ← mkListLit T Y, hX])
        | throwError "sep_cancel: unexpected goals after `flatten_right_at`"
      return ← flattenRight k
  return g

/-- Two atoms with the same head constant and the same number of arguments. -/
meta def sameHead (a b : Expr) : Bool :=
  a.getAppFn.isConst && a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs

/-! ### Registered rules

A rule is a theorem whose conclusion is an entailment `X ⊢ₛ R` or an equivalence `X ⊣⊢ₛ R`
(used forwards) with `X` an application of a constant. When a goal atom matches no hypothesis
atom, `sep_cancel` looks for a hypothesis atom `h` with the head of `X` and a rule whose `X`
unifies with `h` and one of whose atoms of `R` (through `∗` and `bigSep` literals) unifies with
the goal atom, both up to reducible unfolding. The hypothesis atom is then replaced by `R`;
the rule's remaining hypotheses are closed by the side-goal closer or left as goals. -/

/-- A rule registered with `@[sep_cancel_rule]`: the declaration, the head constant of the
    left side of its conclusion, and whether the conclusion is an equivalence. -/
structure Rule where
  /-- The registered theorem. -/
  decl : Name
  /-- The head constant of the left side `X` of the conclusion. -/
  head : Name
  /-- The conclusion is `X ⊣⊢ₛ R` (otherwise `X ⊢ₛ R`). -/
  equiv : Bool
  deriving Inhabited

/-- The rules registered with `@[sep_cancel_rule]`. -/
meta initialize ruleExt : SimpleScopedEnvExtension Rule (Array Rule) ←
  registerSimpleScopedEnvExtension { addEntry := Array.push, initial := #[] }

/-- Read a theorem as a rule, or fail with the accepted shapes. -/
meta def classifyRule (decl : Name) : MetaM Rule := do
  let info ← getConstInfo decl
  forallTelescope info.type fun _ concl => do
    let concl ← instantiateMVars concl
    let equiv ←
      if concl.isAppOfArity ``SAssert.Entails 5 then pure false
      else if concl.isAppOfArity ``SAssert.Equiv 5 then pure true
      else throwError "sep_cancel_rule: the conclusion of `{decl}` is not `_ ⊢ₛ _` or `_ ⊣⊢ₛ _`"
    let .const head _ := concl.appFn!.appArg!.getAppFn
      | throwError "sep_cancel_rule: the left side of `{decl}` is not an application of a \
          constant"
    return { decl, head, equiv }

/-- `@[sep_cancel_rule]` registers an entailment `X ⊢ₛ R` or an equivalence `X ⊣⊢ₛ R` for
    `sep_cancel`, which replaces a hypothesis atom `X` by `R` when an atom of `R` matches a
    goal atom. -/
meta initialize registerBuiltinAttribute {
  name := `sep_cancel_rule
  descr := "Register an entailment `X ⊢ₛ R` for `sep_cancel`"
  add := fun decl _ kind => MetaM.run' do
    ruleExt.add (← classifyRule decl) kind
  applicationTime := .afterTypeChecking
}

/-- The registered rules. The registry is initialized when this module is imported; in this
    module itself the rule set is empty. -/
meta def registeredRules : CoreM (Array Rule) := do
  let env ← getEnv
  if (env.getModuleIdxFor? ``ruleExt).isNone then
    return #[]
  return ruleExt.getState env

/-- The atoms of an assertion through `∗` and `bigSep` list literals. -/
meta partial def sepAtoms (e : Expr) : MetaM (List Expr) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``SAssert.sep 5 then
    return (← sepAtoms e.appFn!.appArg!) ++ (← sepAtoms e.appArg!)
  if e.isAppOfArity ``SAssert.bigSep 4 then
    if let some l ← listLit? e.appArg! then
      let mut out := []
      for y in l do
        out := out ++ (← sepAtoms y)
      return out
  return [e]

/-- Instantiate the rule `r` at the hypothesis atom `h` so that an atom of its right side is the
    goal atom `x`. Returns a proof of `h ⊢ₛ R`, the right side `R`, and the hypotheses of the
    rule that unification left open; fails (restoring the state) when a non-proposition
    argument stays open. -/
meta def instRule (r : Rule) (h x : Expr) : MetaM (Option (Expr × Expr × List MVarId)) := do
  let s ← saveState
  let c ← mkConstWithFreshMVarLevels r.decl
  let (mvs, _, ty) ← forallMetaTelescope (← inferType c)
  let ty ← instantiateMVars ty
  unless ← withReducible (isDefEq ty.appFn!.appArg! h) do
    s.restore
    return none
  let mut found := false
  for y in ← sepAtoms ty.appArg! do
    if ← commitWhen (withReducible (isDefEq y x)) then
      found := true
      break
  unless found do
    s.restore
    return none
  let mut open_ := []
  for m in mvs do
    let m := m.mvarId!
    if ← m.isAssigned then continue
    unless ← isProp (← m.getType) do
      s.restore
      return none
    open_ := open_ ++ [m]
  let pf := mkAppN c mvs
  let pf ← if r.equiv then mkAppM ``And.left #[pf] else pure pf
  return some (← instantiateMVars pf, ← instantiateMVars ty.appArg!, open_)

/-- Cancel the goal atoms one by one; `skipped` counts the unmatched atoms rotated to the end
    of the goal list. Returns the residual entailment, if any, followed by the side goals. -/
meta partial def cancelLoop (g : MVarId) (skipped : Nat) (side : Array MVarId) :
    TacticM (List MVarId) := do
  let (T, hs, gs) ← goalLists g
  if gs.length ≤ skipped then
    if gs.isEmpty then
      let _ ← g.apply (← mkConstWithFreshMVarLevels ``SAssert.entails_nil_right)
      return side.toList
    return g :: side.toList
  let x := gs.head!
  let gsT ← mkListLit T gs.tail!
  if let some φ := pureArg? x then
    let [hφ, k] ← applyStep g (← mkAppM ``SAssert.pure_right #[φ, gsT])
      | throwError "sep_cancel: unexpected goals after `pure_right`"
    let side := if ← closeSide hφ then side else side.push hφ
    return ← cancelLoop k skipped side
  for i in [0:hs.length] do
    if ← commitWhen (withReducible (isDefEq hs[i]! x)) then
      let l₁ ← mkListLit T (hs.take i)
      let l₂ ← mkListLit T (hs.drop (i + 1))
      let rest ← mkListLit T (hs.eraseIdx i)
      let [k] ← applyStep g (← mkAppM ``SAssert.cancel_at #[l₁, l₂, gsT, rest, hs[i]!])
        | throwError "sep_cancel: unexpected goals after `cancel_at`"
      return ← cancelLoop k skipped side
  for i in [0:hs.length] do
    if sameHead hs[i]! x && (pureArg? hs[i]!).isNone then
      let s ← saveState
      let l₁ ← mkListLit T (hs.take i)
      let l₂ ← mkListLit T (hs.drop (i + 1))
      let rest ← mkListLit T (hs.eraseIdx i)
      let [hg, k] ← applyStep g
          (← mkAppM ``SAssert.cancel_eq_at #[l₁, l₂, gsT, rest, hs[i]!, x])
        | throwError "sep_cancel: unexpected goals after `cancel_eq_at`"
      if ← closeSide hg then
        return ← cancelLoop k skipped side
      s.restore
  let rules ← registeredRules
  for i in [0:hs.length] do
    let hi := hs[i]!
    let .const hd _ := hi.getAppFn | continue
    for r in rules do
      if r.head != hd then continue
      let some (pf, R, opens) ← instRule r hi x | continue
      let hX ← mkAppM ``SAssert.Entails.trans #[pf, ← mkAppM ``SAssert.sep_emp #[R]]
      let l₁ ← mkListLit T (hs.take i)
      let l₂ ← mkListLit T (hs.drop (i + 1))
      let rest ← mkListLit T (hs.take i ++ R :: hs.drop (i + 1))
      let mut side := side
      for m in opens do
        unless ← m.isAssigned do
          unless ← closeSide m do
            side := side.push m
      let ks ← applyStep g
          (← mkAppM ``SAssert.flatten_left_at #[l₁, l₂, rest, hi, ← mkListLit T [R], hX])
      let [k] := ks.filter fun k => !opens.contains k
        | throwError "sep_cancel: unexpected goals after `flatten_left_at`"
      return ← cancelLoop (← flattenLeft k) skipped side
  let rest ← mkListLit T (gs.tail! ++ [x])
  let [k] ← applyStep g (← mkAppM ``SAssert.rot_right #[gsT, rest, x])
    | throwError "sep_cancel: unexpected goals after `rot_right`"
  cancelLoop k (skipped + 1) side

/-- Bring a goal `P ⊢ₛ Q` into the form `bigSep hs ⊢ₛ bigSep gs`. -/
meta def normalizeGoal (g : MVarId) : MetaM MVarId := do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SAssert.Entails 5 do
    throwError "sep_cancel: the goal is not an entailment `_ ⊢ₛ _`{indentExpr t}"
  let lBig := t.appFn!.appArg!.isAppOfArity ``SAssert.bigSep 4
  let rBig := t.appArg!.isAppOfArity ``SAssert.bigSep 4
  let lem :=
    if lBig && rBig then none
    else if lBig then some ``SAssert.entails_of_bigSep_right
    else if rBig then some ``SAssert.entails_of_bigSep_left
    else some ``SAssert.entails_of_bigSep_single
  match lem with
  | none => return g
  | some n =>
    let [k] ← g.apply (← mkConstWithFreshMVarLevels n)
      | throwError "sep_cancel: unexpected goals after `{n}`"
    return k

end SepCancel

open Lean Elab Tactic in
/-- `sep_cancel` proves an entailment between separating conjunctions. The two sides are
    `bigSep` list literals or single assertions. Nested `∗`, `bigSep` and `emp` atoms are
    flattened, pure hypotheses are introduced, each goal atom is cancelled against a
    hypothesis atom equal to it up to reducible unfolding, or with the same head and argument
    equalities closed by `rfl`, `assumption`, `bv_omega` or `omega`, or, failing both, against
    an atom of the right side of a `@[sep_cancel_rule]` rule instantiated at a hypothesis
    atom; leftover hypothesis atoms are dropped. Unproved pure facts, unproved hypotheses of
    rules and the entailment of unmatched goal atoms remain as goals. -/
elab "sep_cancel" : tactic => do
  let g :: others ← getGoals | throwError "sep_cancel: no goals"
  let g ← SepCancel.normalizeGoal g
  let g ← SepCancel.flattenLeft g
  let g ← SepCancel.flattenRight g
  let res ← SepCancel.cancelLoop g 0 #[]
  setGoals (res ++ others)

/-! ## Examples at `A = 64` -/

section Examples

open SAssert

example (S T : Set ℕ) (P : SAssert (ℕ → ℕ) ℕ) :
    own S ∗ (P ∗ own T) ⊢ₛ (own T ∗ ⌜1 + 1 = 2⌝) ∗ emp ∗ own S := by
  sep_cancel

example (S T U : Set ℕ) (n : ℕ) (h : n = 3) (hUS : U ⊆ S) :
    bigSep [own S, (own T : SAssert (ℕ → ℕ) ℕ)] ⊢ₛ bigSep [own U, ⌜n + 1 = 4⌝, own T] := by
  sep_cancel
  exact sep_mono (own_mono hUS) (Entails.refl _)

example (a b : BitVec 64) (x y : BitVec 64) (S : Set (BitVec 64)) :
    bigSep [ptsLE 8 a x, ptsLE 8 b y, own S] ⊢ₛ bigSep [ptsLE 8 b y, ptsLE 8 a x] := by
  sep_cancel

example (a b c : BitVec 64) (x y z : BitVec 64) :
    ptsLE 8 a x ∗ (ptsLE 8 b y ∗ ptsLE 8 c z) ⊢ₛ (ptsLE 8 c z ∗ ptsLE 8 a x) ∗ ptsLE 8 b y := by
  sep_cancel

example (a : BitVec 64) (x y : BitVec 64) :
    bigSep [ptsLE 8 (a + 8 + 8) x, ptsLE 8 a y] ⊢ₛ bigSep [ptsLE 8 a y, ptsLE 8 (a + 16) x] := by
  sep_cancel

example (a b : BitVec 64) (x y : BitVec 64) :
    bigSep [⌜a ≠ b⌝, ptsLE 8 a x, emp, ptsLE 8 b y] ⊢ₛ
      bigSep [ptsLE 8 b y, ⌜a ≠ b⌝, ptsLE 8 a x] := by
  sep_cancel

example (a b : BitVec 64) (x : BitVec 64) (y : BitVec 32) :
    bigSep [ptsLE 8 a x, ptsLE 4 b y] ⊢ₛ bigSep [ptsLE 4 b y, ⌜x = x + 0⌝] := by
  sep_cancel

example (a b : BitVec 64) (x y : BitVec 64) (m : MemW 64)
    (h : (ptsLE 8 a x ∗ ptsLE 8 b y).holds m) : (⟨a, 8⟩ : Rng 64).Disj ⟨b, 8⟩ :=
  ptsLE_disj h (by decide) (by decide)

example (a b : BitVec 64) (x y v : BitVec 64) :
    Triple (ptsLE 8 a x ∗ ptsLE 8 b y) (fun m : MemW 64 => writeLE 8 m a v)
      (ptsLE 8 a v ∗ ptsLE 8 b y) :=
  Triple.frame _ (triple_writeLE 8 a x v (by decide)) (writesIn_writeLE 8 a v)
    (fun _ _ => subset_rfl) subset_rfl

end Examples

end CatCrypt.Crypto.SecureCompilation.SepLogic
