/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Rust.WP

/-!
# The correspondence square over a `RustM` program

`CorresM P G p V Q` relates a state-passing `RustM` program `p : C → RustM (A × C)` to a
shallow description over an abstract state `σ : S`:

* `P c σ` — the entry relation between the concrete state and the abstract state;
* `G σ` — the guard under which the correspondence is claimed;
* `V σ` — the value the program returns;
* `Q c' σ` — the exit relation between the final concrete state and the abstract state.

The three outcomes of `RustM` enter as follows. `.ok (V σ, c')` is the only outcome the
judgment admits: under `P c σ` and `G σ` the program is `.ok` with first component `V σ`
and a second component related to `σ` by `Q`. `.fail e` and `.div` are therefore outside
the guard — `corresM_ne_fail` and `corresM_ne_div` read that off — so the square says
that under `G` the computation succeeds and its value is the one the abstract state
stands for. `RustM` reports divergence as an outcome, so the judgment needs no fuel
parameter.

The program is state-passing because a square has two vertical sides: a bare `RustM A`
carries no exit state for `Q` to constrain. `C` is the concrete state, `A` the Rust
return type.

## Vertical direction

`corresM_conseq` strengthens the entry relation and the guard and weakens the exit
relation. `VMapM` bundles its four hypotheses into one arrow between the boundary data
`(P, G, V, Q)` of a square and `(P', G', V', Q')`; `VMapM.id` and `VMapM.comp` are a
strict category (`vmapM_id_comp`, `vmapM_comp_id`, `vmapM_comp_assoc`, all `rfl`), and
`vsquareM_act` is its action on a square, with the two functor laws holding by proof
irrelevance. `corresM_reindex` moves a square along a map `k : S' → S` of abstract states,
reading every side at `k σ'`; the judgment holds the abstract state fixed, so a
continuation whose abstract state is a shift of the caller's reaches its square through
this reindexing rather than through `corresM_conseq`.

## Horizontal direction

`kseq p f` is the Kleisli composition of two state-passing programs and `pureK v` returns
`v` leaving the state alone. `kseq_pure_left`, `kseq_pure_right` and `kseq_assoc` hold as
equalities of programs, so the unit and associativity laws of the horizontal direction are
equalities of `CorresM` statements (`corresM_kseq_pure_left_eq`,
`corresM_kseq_pure_right_eq`, `corresM_kseq_assoc_eq`) rather than mere inter-derivability.

`corresM_bind` composes two squares over `kseq`: the continuation's square is demanded at
every value `a`, with its entry relation restricted to the abstract states whose value is
`a`, so only the value the first leg produces is constrained. `RustM`'s bind propagates
`.fail` and `.div` without running the continuation, which is why the first leg's square —
excluding both — is what lets the composite reach the continuation at all.

## The `Std.Do` reading

`corresM_iff_triple` states the square as a `Std.Do` triple over `RustM`'s `WP` instance:
the square holds exactly when, from every entry state, there is an exit state related by
`Q` for which `p c` satisfies the total postcondition `r = (V σ, c')`. The two forms are
equivalent, so the triple form carries the same exclusion of `.fail` and `.div` as
`corresM_ne_fail` and `corresM_ne_div` state for the definition.

## Main definitions

* `CorresM` — the square over a state-passing `RustM` program
* `kseq`, `pureK` — the horizontal composition and its unit
* `VMapM`, `VMapM.id`, `VMapM.comp`, `vsquareM_act` — the vertical category and its action
* `corresM_reindex` — a square along a map of abstract states
* `corresM_bind` — horizontal composition of squares
* `corresM_iff_triple` — the square as a `Std.Do` triple

A worked instance of all of these on a two-step program is
`Ascent/RustMSquareDemo.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent.RustM

open Aeneas.Std
open Std.Do

variable {C S A B : Type}

/-! ## The judgment -/

/-- **The correspondence judgment over `RustM`.** From a concrete state `c` related to
    `σ` by `P` with the guard `G σ`, the program is `.ok (V σ, c')` for a `c'` related to
    `σ` by `Q`. -/
def CorresM (P : C → S → Prop) (G : S → Prop) (p : C → Aeneas.Std.RustM (A × C))
    (V : S → A) (Q : C → S → Prop) : Prop :=
  ∀ c σ, P c σ → G σ → ∃ c', p c = .ok (V σ, c') ∧ Q c' σ

/-- Under the guard the program is not a failure. -/
theorem corresM_ne_fail {P : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V : S → A} {Q : C → S → Prop}
    (h : CorresM P G p V Q) {c : C} {σ : S} (hP : P c σ) (hG : G σ) (e : Aeneas.Std.Error) :
    p c ≠ .fail e := by
  obtain ⟨c', hc, _⟩ := h c σ hP hG
  rw [hc]; intro hcon; cases hcon

/-- Under the guard the program does not diverge. -/
theorem corresM_ne_div {P : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V : S → A} {Q : C → S → Prop}
    (h : CorresM P G p V Q) {c : C} {σ : S} (hP : P c σ) (hG : G σ) :
    p c ≠ .div := by
  obtain ⟨c', hc, _⟩ := h c σ hP hG
  rw [hc]; intro hcon; cases hcon

/-! ## Vertical direction -/

/-- **Consequence.** Strengthen the entry relation and the guard, weaken the exit
    relation, and replace the value by one equal to it under the guard. -/
theorem corresM_conseq {P P' : C → S → Prop} {G G' : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V V' : S → A} {Q Q' : C → S → Prop}
    (h : CorresM P G p V Q)
    (hP : ∀ c σ, P' c σ → G' σ → P c σ) (hG : ∀ σ, G' σ → G σ)
    (hV : ∀ σ, G' σ → V σ = V' σ) (hQ : ∀ c σ, G' σ → Q c σ → Q' c σ) :
    CorresM P' G' p V' Q' := by
  intro c σ hP' hG'
  obtain ⟨c', hc, hQ₀⟩ := h c σ (hP c σ hP' hG') (hG σ hG')
  exact ⟨c', by rw [hc, hV σ hG'], hQ c' σ hG' hQ₀⟩

/-- **Reindexing the abstract state.** A square over `S` gives a square over `S'` along
    any `k : S' → S`, with every side read at `k σ'`. -/
theorem corresM_reindex {S' : Type} {P : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V : S → A} {Q : C → S → Prop}
    (k : S' → S) (h : CorresM P G p V Q) :
    CorresM (fun c σ' => P c (k σ')) (fun σ' => G (k σ')) p (fun σ' => V (k σ'))
      (fun c σ' => Q c (k σ')) :=
  fun c σ' hP hG => h c (k σ') hP hG

/-- A vertical arrow: the four hypotheses of `corresM_conseq` as one arrow between the
    boundary data of two squares. -/
structure VMapM (P P' : C → S → Prop) (G G' : S → Prop) (V V' : S → A)
    (Q Q' : C → S → Prop) : Prop where
  /-- The entry relation weakens. -/
  hP : ∀ c σ, P' c σ → G' σ → P c σ
  /-- The guard weakens. -/
  hG : ∀ σ, G' σ → G σ
  /-- The value is unchanged under the new guard. -/
  hV : ∀ σ, G' σ → V σ = V' σ
  /-- The exit relation strengthens. -/
  hQ : ∀ c σ, G' σ → Q c σ → Q' c σ

/-- The vertical identity. -/
theorem VMapM.id (P : C → S → Prop) (G : S → Prop) (V : S → A) (Q : C → S → Prop) :
    VMapM P P G G V V Q Q where
  hP := fun _ _ h _ => h
  hG := fun _ h => h
  hV := fun _ _ => rfl
  hQ := fun _ _ _ h => h

/-- Vertical composition through the shared middle boundary. -/
theorem VMapM.comp {P P' P'' : C → S → Prop} {G G' G'' : S → Prop} {V V' V'' : S → A}
    {Q Q' Q'' : C → S → Prop} (m : VMapM P P' G G' V V' Q Q')
    (m' : VMapM P' P'' G' G'' V' V'' Q' Q'') : VMapM P P'' G G'' V V'' Q Q'' where
  hP := fun c σ h hG'' => m.hP c σ (m'.hP c σ h hG'') (m'.hG σ hG'')
  hG := fun σ h => m.hG σ (m'.hG σ h)
  hV := fun σ h => (m.hV σ (m'.hG σ h)).trans (m'.hV σ h)
  hQ := fun c σ h hQ => m'.hQ c σ h (m.hQ c σ (m'.hG σ h) hQ)

/-- Left unit for vertical composition, on the nose. -/
theorem vmapM_id_comp {P P' : C → S → Prop} {G G' : S → Prop} {V V' : S → A}
    {Q Q' : C → S → Prop} (m : VMapM P P' G G' V V' Q Q') :
    (VMapM.id P G V Q).comp m = m := rfl

/-- Right unit for vertical composition, on the nose. -/
theorem vmapM_comp_id {P P' : C → S → Prop} {G G' : S → Prop} {V V' : S → A}
    {Q Q' : C → S → Prop} (m : VMapM P P' G G' V V' Q Q') :
    m.comp (VMapM.id P' G' V' Q') = m := rfl

/-- Associativity of vertical composition, on the nose. -/
theorem vmapM_comp_assoc {P₀ P₁ P₂ P₃ : C → S → Prop} {G₀ G₁ G₂ G₃ : S → Prop}
    {V₀ V₁ V₂ V₃ : S → A} {Q₀ Q₁ Q₂ Q₃ : C → S → Prop}
    (m₁ : VMapM P₀ P₁ G₀ G₁ V₀ V₁ Q₀ Q₁) (m₂ : VMapM P₁ P₂ G₁ G₂ V₁ V₂ Q₁ Q₂)
    (m₃ : VMapM P₂ P₃ G₂ G₃ V₂ V₃ Q₂ Q₃) :
    (m₁.comp m₂).comp m₃ = m₁.comp (m₂.comp m₃) := rfl

/-- **The action of a vertical arrow on a square.** -/
theorem vsquareM_act {P P' : C → S → Prop} {G G' : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V V' : S → A} {Q Q' : C → S → Prop}
    (h : CorresM P G p V Q) (m : VMapM P P' G G' V V' Q Q') : CorresM P' G' p V' Q' :=
  corresM_conseq h m.hP m.hG m.hV m.hQ

/-- Acting by the vertical identity changes nothing: both sides prove the same `Prop`. -/
theorem vsquareM_act_id {P : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V : S → A} {Q : C → S → Prop}
    (h : CorresM P G p V Q) : vsquareM_act h (VMapM.id P G V Q) = h := rfl

/-- Acting by a vertical composite is acting by the two arrows in turn. -/
theorem vsquareM_act_comp {P P' P'' : C → S → Prop} {G G' G'' : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V V' V'' : S → A} {Q Q' Q'' : C → S → Prop}
    (h : CorresM P G p V Q) (m : VMapM P P' G G' V V' Q Q')
    (m' : VMapM P' P'' G' G'' V' V'' Q' Q'') :
    vsquareM_act h (m.comp m') = vsquareM_act (vsquareM_act h m) m' := rfl

/-! ## Horizontal direction -/

/-- The Kleisli composition of two state-passing `RustM` programs: the first program's
    value is handed to the continuation together with its exit state. -/
def kseq (p : C → Aeneas.Std.RustM (A × C)) (f : A → C → Aeneas.Std.RustM (B × C)) :
    C → Aeneas.Std.RustM (B × C) :=
  fun c => (p c) >>= fun r => f r.1 r.2

/-- The program that returns `v` and leaves the state alone. -/
def pureK (v : A) : C → Aeneas.Std.RustM (A × C) := fun c => .ok (v, c)

/-- `pureK` is a left unit for `kseq`. -/
theorem kseq_pure_left (v : A) (f : A → C → Aeneas.Std.RustM (B × C)) :
    kseq (pureK v) f = f v := rfl

/-- `pureK` is a right unit for `kseq`. -/
theorem kseq_pure_right (p : C → Aeneas.Std.RustM (A × C)) :
    kseq p (fun a c => pureK a c) = p := by
  funext c
  simp only [kseq, pureK]
  cases p c <;> rfl

/-- `kseq` is associative. -/
theorem kseq_assoc {D : Type} (p : C → Aeneas.Std.RustM (A × C))
    (f : A → C → Aeneas.Std.RustM (B × C)) (g : B → C → Aeneas.Std.RustM (D × C)) :
    kseq (kseq p f) g = kseq p (fun a c => kseq (f a) g c) := by
  funext c
  simp only [kseq]
  cases p c <;> rfl

/-- A program returning a constant, with the state untouched. -/
theorem corresM_pureK (P : C → S → Prop) (G : S → Prop) (v : A) :
    CorresM P G (pureK v) (fun _ => v) P :=
  fun c _ hP _ => ⟨c, rfl, hP⟩

/-- **Horizontal composition.** From a square for `p` and, at every value `a`, a square
    for the continuation at `a` whose entry relation is the first square's exit relation
    restricted to the abstract states with value `a`, a square for `kseq p f`. -/
theorem corresM_bind {P Q R : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {f : A → C → Aeneas.Std.RustM (B × C)}
    {V : S → A} {W : S → B}
    (h₁ : CorresM P G p V Q)
    (h₂ : ∀ a, CorresM (fun c σ => Q c σ ∧ V σ = a) G (f a) W R) :
    CorresM P G (kseq p f) W R := by
  intro c σ hP hG
  obtain ⟨c₁, h₁c, hQ⟩ := h₁ c σ hP hG
  obtain ⟨c₂, h₂c, hR⟩ := h₂ (V σ) c₁ σ ⟨hQ, rfl⟩ hG
  exact ⟨c₂, by simp only [kseq, h₁c, Aeneas.Std.bind_tc_ok]; exact h₂c, hR⟩

/-- The left unit law of `kseq` as an equality of square statements. -/
theorem corresM_kseq_pure_left_eq {P R : C → S → Prop} {G : S → Prop} {W : S → B}
    (v : A) (f : A → C → Aeneas.Std.RustM (B × C)) :
    CorresM P G (kseq (pureK v) f) W R = CorresM P G (f v) W R := by
  rw [kseq_pure_left]

/-- The right unit law of `kseq` as an equality of square statements. -/
theorem corresM_kseq_pure_right_eq {P R : C → S → Prop} {G : S → Prop} {V : S → A}
    (p : C → Aeneas.Std.RustM (A × C)) :
    CorresM P G (kseq p (fun a c => pureK a c)) V R = CorresM P G p V R := by
  rw [kseq_pure_right]

/-- Associativity of `kseq` as an equality of square statements. -/
theorem corresM_kseq_assoc_eq {D : Type} {P R : C → S → Prop} {G : S → Prop} {W : S → D}
    (p : C → Aeneas.Std.RustM (A × C)) (f : A → C → Aeneas.Std.RustM (B × C))
    (g : B → C → Aeneas.Std.RustM (D × C)) :
    CorresM P G (kseq (kseq p f) g) W R
      = CorresM P G (kseq p (fun a c => kseq (f a) g c)) W R := by
  rw [kseq_assoc]

/-! ## The `Std.Do` reading -/

/-- The square as a `Std.Do` triple over `RustM`'s `WP` instance, with a total
    postcondition pinning the returned pair. -/
theorem corresM_iff_triple {P Q : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V : S → A} :
    CorresM P G p V Q ↔
      ∀ c σ, P c σ → G σ →
        ∃ c', Q c' σ ∧ (⦃⌜True⌝⦄ p c ⦃⇓ r => ⌜r = (V σ, c')⌝⦄) := by
  constructor
  · intro h c σ hP hG
    obtain ⟨c', hc, hQ⟩ := h c σ hP hG
    exact ⟨c', hQ, Aeneas.Std.WP.triple_post_eq_iff_eq.mpr hc⟩
  · intro h c σ hP hG
    obtain ⟨c', hQ, ht⟩ := h c σ hP hG
    exact ⟨c', Aeneas.Std.WP.triple_post_eq_iff_eq.mp ht, hQ⟩

end Hax.Ascent.RustM
