/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.Corres

/-!
# The correspondence squares as a double-category fragment

`Corres bi P G e V Q` is a square: the vertical sides are the entry/exit relations
`P, Q : Env → S → Prop` between the concrete environment and the abstract state, the
top horizontal side is the program `e`, and the bottom horizontal side is the pair
`(G, V)` reporting the guard and the value the abstract state stands for. This file
gives the two composition directions their categorical structure.

## Vertical direction: `VMap`

`VMap` bundles the four hypotheses of `corres_conseq` (`hP`, `hG`, `hV`, `hQ`) into one
arrow between the boundary data `(P, G, V, Q)` of a square and `(P', G', V', Q')`.
`VMap.id` and `VMap.comp` make these a category (`vmap_id_comp`, `vmap_comp_id`,
`vmap_comp_assoc`), and `corres_conseq` is its action on a square (`vsquare_act`,
`vsquare_act_id`, `vsquare_act_comp`). The unit and associativity laws for the action
hold by proof irrelevance: `Corres bi P' G' e V' Q'` is a `Prop`, so any two proofs of
it are equal, and both sides of each law are such proofs. The vertical category itself
is a strict category, distinct from a preorder up to the corres_conseq action: `VMap`
carries the four functions as data, but composing and identity are associative and
unital on the nose (`rfl`), since composition is plain function composition.

## Horizontal direction: composed programs

A horizontal arrow from `P` to `Q` at a fixed `bi`, `G` is a program together with a
value function and a proof `Corres bi P G e V Q`; `HArrow` bundles this. `hcomp` is
`corres_seq` repackaged as composition of `HArrow`s and `hid` is `corres_unitVal`
repackaged as an arrow. `.seq (.seq e1 e2) e3` and `.seq e1 (.seq e2 e3)` are different
`ImpExpr` values, so `hcomp` cannot be associative on the nose; `corres_seq_assoc`
records instead that the same three leg proofs build a square over *either* bracketing
directly, with no re-derivation, and `seq_assoc_run` identifies the two programs'
`denote'` runs at the semantic level. `corres_seq_unitVal_left_iff` shows `hid` is a
**left** identity for `hcomp` up to `Iff` of the resulting `Corres` statement
(the run of `.seq .unitVal e` equals the run of `e` outright, at every fuel). `hid` is
**not** a right identity: `hcomp h1 _ (hid bi Q G)` produces the program `.seq e1
.unitVal`, whose value is `fun _ => .unit`, discarding `h1`'s own value — recovering a
right identity needs `corres_letBind` (binding the value, then a trailing `.var x` to
read it back), not `corres_seq`. **The horizontal structure is a category on the leg
data one already has (`corres_seq_assoc`), with a proved left unit and no proved right
unit under `corres_seq`; it is not a symmetric bicategory.**

## Interchange

`vmap_hcomp_interchange` is the double-category interchange law: weakening the two ends of
a horizontal composite by a `VMap` acting on the *shared middle* relation is the same
proof as composing the two separately-weakened squares, because both sides are proofs
of `Corres bi P' G' (.seq e1 e2) V' Q'` — the same program on the nose, so no associator
is needed and the law is `rfl` by proof irrelevance once the two constructions are seen
to target the same statement.

## Where the existing judgments sit

* `Corres`, `CorresArgs` are literally instances: a square's data.
* `CorresX` (`Ascent/EarlyExit.lean`) is *definitionally* `Corres` at
  `V := fun σ => excVal (R σ)` — the same square, not a parallel one.
* `FnCorres` (`fnCorres_of_corres`) is the square specialised at the vertical arrow
  `P := fun env a => env = entry a` (a functional entry side, stronger than a general
  relation)
  and `Q := fun _ _ => True`; it is a corollary of a square, not itself stored as one,
  because its defining `∃ fuel₀, …` drops the exit relation `Q` entirely. The same is
  true of `FnCorresX` and `CorresB`, read off `fnCorres_of_corresB` in `GenRules.lean`.

## Automation

`weld` (`macro_rules`) tries `corres_seq`, `corres_letBind` and `corres_conseq` in turn
at each step of a linear leg chain, closing each step without naming which combinator
glues that particular pair; see the rewritten `Demo.body_corres` proof.

## Main definitions

* `VMap`, `VMap.id`, `VMap.comp` — the vertical category of boundary weakenings
* `vsquare_act`, `vsquare_act_id`, `vsquare_act_comp` — its action on a square, and the
  two functor laws
* `HArrow`, `hid`, `hcomp` — the horizontal arrows of programs between vertical
  relations
* `corres_seq_assoc` — both bracketings of a three-leg chain, from the same data
* `seq_assoc_run`, `seq_unitVal_left_run`, `seq_unitVal_right_run` — the `denote'`-level
  content behind reassociation and the left unit
* `corres_seq_unitVal_left_iff` — `hid` is a left identity for `hcomp`, up to `Iff`
* `vmap_hcomp_interchange` — the double-category interchange law
* `weld` — the composition tactic
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {S : Type} (bi : Builtins)

/-! ## The vertical category of boundary weakenings -/

/-- A vertical arrow of the correspondence double category: the four hypotheses
    `corres_conseq` needs to turn a square with boundary `(P, G, V, Q)` into one with
    boundary `(P', G', V', Q')`. -/
structure VMap (P P' : Env → S → Prop) (G G' : S → Prop) (V V' : S → Value)
    (Q Q' : Env → S → Prop) : Prop where
  /-- The entry relation weakens. -/
  hP : ∀ env σ, P' env σ → G' σ → P env σ
  /-- The guard weakens. -/
  hG : ∀ σ, G' σ → G σ
  /-- The value is unchanged under the new guard. -/
  hV : ∀ σ, G' σ → V σ = V' σ
  /-- The exit relation strengthens. -/
  hQ : ∀ env σ, G' σ → Q env σ → Q' env σ

/-- The vertical identity: every field of `VMap` at its trivial witness. -/
theorem VMap.id (P : Env → S → Prop) (G : S → Prop) (V : S → Value) (Q : Env → S → Prop) :
    VMap P P G G V V Q Q where
  hP := fun _ _ h _ => h
  hG := fun _ h => h
  hV := fun _ _ => rfl
  hQ := fun _ _ _ h => h

/-- Vertical composition: chase both `VMap`s through the shared middle boundary. -/
theorem VMap.comp {P P' P'' : Env → S → Prop} {G G' G'' : S → Prop} {V V' V'' : S → Value}
    {Q Q' Q'' : Env → S → Prop} (m : VMap P P' G G' V V' Q Q')
    (m' : VMap P' P'' G' G'' V' V'' Q' Q'') : VMap P P'' G G'' V V'' Q Q'' where
  hP := fun env σ h hG'' => m.hP env σ (m'.hP env σ h hG'') (m'.hG σ hG'')
  hG := fun σ h => m.hG σ (m'.hG σ h)
  hV := fun σ h => (m.hV σ (m'.hG σ h)).trans (m'.hV σ h)
  hQ := fun env σ h hQ => m'.hQ env σ h (m.hQ env σ (m'.hG σ h) hQ)

/-- Left unit for vertical composition, on the nose. -/
theorem vmap_id_comp {P P' : Env → S → Prop} {G G' : S → Prop} {V V' : S → Value}
    {Q Q' : Env → S → Prop} (m : VMap P P' G G' V V' Q Q') :
    (VMap.id P G V Q).comp m = m := rfl

/-- Right unit for vertical composition, on the nose. -/
theorem vmap_comp_id {P P' : Env → S → Prop} {G G' : S → Prop} {V V' : S → Value}
    {Q Q' : Env → S → Prop} (m : VMap P P' G G' V V' Q Q') :
    m.comp (VMap.id P' G' V' Q') = m := rfl

/-- Associativity of vertical composition, on the nose. -/
theorem vmap_comp_assoc {P₀ P₁ P₂ P₃ : Env → S → Prop} {G₀ G₁ G₂ G₃ : S → Prop}
    {V₀ V₁ V₂ V₃ : S → Value} {Q₀ Q₁ Q₂ Q₃ : Env → S → Prop}
    (m₁ : VMap P₀ P₁ G₀ G₁ V₀ V₁ Q₀ Q₁) (m₂ : VMap P₁ P₂ G₁ G₂ V₁ V₂ Q₁ Q₂)
    (m₃ : VMap P₂ P₃ G₂ G₃ V₂ V₃ Q₂ Q₃) :
    (m₁.comp m₂).comp m₃ = m₁.comp (m₂.comp m₃) := rfl

variable {bi}

/-- **The action of a vertical arrow on a square.** `corres_conseq` under the `VMap`
    packaging. -/
theorem vsquare_act {P P' : Env → S → Prop} {G G' : S → Prop} {V V' : S → Value}
    {Q Q' : Env → S → Prop} {e : ImpExpr} (h : Corres bi P G e V Q)
    (m : VMap P P' G G' V V' Q Q') : Corres bi P' G' e V' Q' :=
  corres_conseq h m.hP m.hG m.hV m.hQ

/-- **Unit law of the action.** Acting by the vertical identity changes nothing —
    both sides prove the same `Prop`, so this holds by proof irrelevance. -/
theorem vsquare_act_id {P : Env → S → Prop} {G : S → Prop} {V : S → Value}
    {Q : Env → S → Prop} {e : ImpExpr} (h : Corres bi P G e V Q) :
    vsquare_act h (VMap.id P G V Q) = h := rfl

/-- **Functoriality of the action.** Acting by a vertical composite is acting by the
    two arrows in turn — again a proof-irrelevance identity between two proofs of
    `Corres bi P'' G'' e V'' Q''`. -/
theorem vsquare_act_comp {P P' P'' : Env → S → Prop} {G G' G'' : S → Prop}
    {V V' V'' : S → Value} {Q Q' Q'' : Env → S → Prop} {e : ImpExpr}
    (h : Corres bi P G e V Q) (m : VMap P P' G G' V V' Q Q')
    (m' : VMap P' P'' G' G'' V' V'' Q' Q'') :
    vsquare_act h (m.comp m') = vsquare_act (vsquare_act h m) m' := rfl

/-! ## The horizontal bicategory of programs -/

/-- A horizontal arrow from the entry relation `P` to the exit relation `Q` at guard
    `G`: a program `e`, the value it stands for, and the square relating them. -/
structure HArrow (bi : Builtins) (P : Env → S → Prop) (G : S → Prop) (Q : Env → S → Prop)
    where
  /-- The program. -/
  e : ImpExpr
  /-- The value the abstract state produces. -/
  V : S → Value
  /-- The square. -/
  hCorres : Corres bi P G e V Q

/-- The horizontal identity at `P`: `.unitVal`, returning `.unit` and leaving the
    relation unchanged (`corres_unitVal`). -/
def hid (bi : Builtins) (P : Env → S → Prop) (G : S → Prop) : HArrow bi P G P where
  e := .unitVal
  V := fun _ => .unit
  hCorres := corres_unitVal P G

/-- Horizontal composition: run the first arrow's program, then the second's
    (`corres_seq`), provided the first's value is never a control-flow value under the
    guard. -/
def hcomp {bi : Builtins} {P Q R : Env → S → Prop} {G : S → Prop} (h1 : HArrow bi P G Q)
    (hplain : ∀ σ, G σ → (h1.V σ).isControlFlow = false) (h2 : HArrow bi Q G R) :
    HArrow bi P G R where
  e := .seq h1.e h2.e
  V := h2.V
  hCorres := corres_seq h1.hCorres hplain h2.hCorres

/-! ## The `denote'` identities behind the horizontal associator and unitors -/

/-- `.unitVal` on the left of a `.seq` is transparent to the run of the right side, from
    any state, at any fuel: both sides run `e` from the same environment. This is the
    left-unitor content, stated once and for all rather than per `e`. -/
theorem seq_unitVal_left_run (fuel : Nat) (e : ImpExpr) (env : Env) :
    denote' bi fuel (.seq .unitVal e) env = denote' bi fuel e env := by
  rw [denote'_seq bi fuel (denote'_unitVal bi fuel env) (by rfl)]

/-- The right-unitor content: `.seq e .unitVal` runs `e`, then discards its value for
    `.unit`, at the exit environment of `e`'s run. Given `e`'s run at `fuel`, this
    identifies the run of `.seq e .unitVal` explicitly (it is *not* the run of `e`
    itself, since the returned value changes from `e`'s to `.unit`). -/
theorem seq_unitVal_right_run {fuel : Nat} {e : ImpExpr} {env s : Env} {v : Value}
    (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.seq e .unitVal) env = (.val .unit, s) := by
  rw [denote'_seq bi fuel h hv, denote'_unitVal]

/-- The associator content: from a run of `e1` landing at `s1` with a plain value, and
    of `e2` from `s1` landing at `s2` with a plain value, both nestings of `.seq` run to
    the same run of `e3` from `s2` — i.e. `.seq (.seq e1 e2) e3` and
    `.seq e1 (.seq e2 e3)` agree at every state either is defined at this fuel. -/
theorem seq_assoc_run {fuel : Nat} {e1 e2 e3 : ImpExpr} {env s1 s2 : Env} {v1 v2 : Value}
    (h1 : denote' bi fuel e1 env = (.val v1, s1)) (hv1 : v1.isControlFlow = false)
    (h2 : denote' bi fuel e2 s1 = (.val v2, s2)) (hv2 : v2.isControlFlow = false) :
    denote' bi fuel (.seq (.seq e1 e2) e3) env = denote' bi fuel (.seq e1 (.seq e2 e3)) env := by
  have hleft : denote' bi fuel (.seq e1 e2) env = (.val v2, s2) := by
    rw [denote'_seq bi fuel h1 hv1]; exact h2
  rw [denote'_seq bi fuel hleft hv2, denote'_seq bi fuel h1 hv1, denote'_seq bi fuel h2 hv2]

/-- **`hid` is a left identity for `hcomp`, up to `Iff`.** The run of `.seq .unitVal e`
    is the run of `e` at every fuel (`seq_unitVal_left_run`), so the two `Corres`
    statements — one over each program — are logically equivalent, not just each
    separately derivable. -/
theorem corres_seq_unitVal_left_iff {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} :
    Corres bi P G (.seq .unitVal e) V Q ↔ Corres bi P G e V Q := by
  constructor
  · intro h env σ hP hG
    obtain ⟨f₀, env', hQ, hrun⟩ := h env σ hP hG
    exact ⟨f₀, env', hQ, fun fuel hf => by
      rw [← seq_unitVal_left_run fuel e env]; exact hrun fuel hf⟩
  · intro h env σ hP hG
    obtain ⟨f₀, env', hQ, hrun⟩ := h env σ hP hG
    exact ⟨f₀, env', hQ, fun fuel hf => by
      rw [seq_unitVal_left_run fuel e env]; exact hrun fuel hf⟩

/-- **Reassociation from the same data.** The three leg proofs `h1`, `h2`, `h3` build a
    square over *either* bracketing of `.seq (.seq e1 e2) e3`, with no extra work and no
    choice of which bracketing to commit to first — the plainness side condition at each
    join is exactly the value of the leg feeding it (`hplain1` at the first join,
    `hplain2` at the second, in both bracketings). -/
theorem corres_seq_assoc {P Q1 Q2 Q : Env → S → Prop} {G : S → Prop} {e1 e2 e3 : ImpExpr}
    {V1 V2 V3 : S → Value} (h1 : Corres bi P G e1 V1 Q1)
    (hplain1 : ∀ σ, G σ → (V1 σ).isControlFlow = false) (h2 : Corres bi Q1 G e2 V2 Q2)
    (hplain2 : ∀ σ, G σ → (V2 σ).isControlFlow = false) (h3 : Corres bi Q2 G e3 V3 Q) :
    Corres bi P G (.seq (.seq e1 e2) e3) V3 Q ∧ Corres bi P G (.seq e1 (.seq e2 e3)) V3 Q :=
  ⟨corres_seq (corres_seq h1 hplain1 h2) hplain2 h3,
    corres_seq h1 hplain1 (corres_seq h2 hplain2 h3)⟩

/-- **The interchange law.** Weakening `h1` by `mIn` and `h2` by `mOut` and then
    composing horizontally is the same proof as composing horizontally and then
    weakening by the combined vertical arrow `mIn.hP`/`mIn.hG`/`mOut.hV`/`mOut.hQ` —
    both sides are proofs of `Corres bi P' G' (.seq e1 e2) V2' Q'`, the *same* program
    (no associator is involved, unlike `corres_seq_assoc`), so the law is `rfl` by
    `Corres`'s being a `Prop`. -/
theorem vmap_hcomp_interchange {P P' Q1 Q1' Q Q' : Env → S → Prop} {G G' : S → Prop}
    {V1 V1' V2 V2' : S → Value} {e1 e2 : ImpExpr} (h1 : Corres bi P G e1 V1 Q1)
    (hplain : ∀ σ, G σ → (V1 σ).isControlFlow = false) (h2 : Corres bi Q1 G e2 V2 Q)
    (mIn : VMap P P' G G' V1 V1' Q1 Q1') (mOut : VMap Q1 Q1' G G' V2 V2' Q Q') :
    corres_seq (vsquare_act h1 mIn)
        (fun σ hG' => by rw [← mIn.hV σ hG']; exact hplain σ (mIn.hG σ hG'))
        (vsquare_act h2 mOut)
      = vsquare_act (corres_seq h1 hplain h2)
          { hP := mIn.hP, hG := mIn.hG, hV := mOut.hV, hQ := mOut.hQ } :=
  rfl

/-! ## Automation -/

/-- Tries each combinator that glues one leg to the next: `corres_seq` for a plain
    sequence, `corres_letBind` when the composite binds the first value into the
    environment, `corres_conseq` to adjust the boundary along a `VMap`-shaped
    entailment. Repeating it walks a linear chain of leg proofs down to leaf goals,
    without naming which combinator joins each pair. -/
macro "weld" : tactic =>
  `(tactic| first
    | apply corres_seq
    | apply corres_letBind
    | apply corres_conseq)

end Hax.Ascent
