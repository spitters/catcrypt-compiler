/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Wp
public import HaxAscent.Ascent.Encode
public import HaxAscent.Ascent.Refines
public import Std.Do

/-!
# Correspondence of `denote'` with shallow functions

`Corres bi P G e V Q` relates the post-pipeline program `e`, run by `denote' bi`, to a
shallow description over an abstract state `σ : S`:

* `P env σ` — the entry relation between the environment and the abstract state;
* `G σ` — the guard under which the correspondence is claimed;
* `V σ` — the value the run returns;
* `Q env' σ` — the exit relation between the final environment and the abstract state.

From `P env σ` and `G σ` there are a fuel `fuel₀` and an environment `env'` with
`Q env' σ` such that at every `fuel ≥ fuel₀` the run is `(.val (V σ), env')`. `letBind`
extends the environment without restoring it, so the exit relation is part of the
judgment. The value is a `Value`; a shallow function of surface type `β` reads through
`fun σ => enc (F σ)` (`HaxAscent/Ascent/Encode.lean`). The judgment and the one-step
equations of `denote'` are defined in `HaxAscent/Ascent/CorresCore.lean`.

## Rules

Each rule is proved from the corresponding rule of the weakest precondition
(`HaxAscent/Ascent/Wp.lean`) through `corres_iff_wp` and `corresArgs_iff_wpArgs`; the
counted loop `corres_forFoldE` is proved from `wp_forFold`.

`corres_conseq`, `corres_lit`, `corres_unitVal`, `corres_var`, `corres_letBind`,
`corres_seq`, `corres_ifThenElse`, `corres_tuple`, `corres_proj`,
`corres_typeAscription`, `corres_borrow`, `corres_deref`, `corres_app`, `corres_cfBreak`,
`corres_cfContinue`; `CorresArgs` for argument lists with `corresArgs_nil`,
`corresArgs_cons`; the counted loop `corres_forFold` against `foldFrom` and
`corres_forFoldE`, whose body may leave through `cfBreak`, against `foldFromE`.

`foldFrom f n i a` and `foldFromE f n i a` are the recursion equations of the runtime's
`Hax.foldRange.go` and `Hax.forFold.go` (`ControlFlow.Break b` is `.error b`,
`ControlFlow.Continue a` is `.ok a`), stated here without importing the runtime.

## Functions

`FnCorres bi e entry G f` is the top-level form: for every argument `a` with `G a`, the
run from `entry a` returns `enc (f a)` from some fuel on. `haxEval bi e env` is the
eventual value of the run, and `fnCorres_refinesO` and `fnCorres_absProg` read a
`FnCorres` as `RefinesO` and as the `Option`-level `AbsProg` refinement of
`optGuard G f`. `FnPartial` is the partial-correctness form (a value the run returns at
any fuel is `enc (f a)`), implied by `FnCorres` (`fnPartial_of_fnCorres`), and
`fnCorres_iff_triple` states `FnCorres` as a `Std.Do` triple over the `Option` program
`optGuard G f a`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## The rules of the judgment -/

section Judgment

variable {S : Type} {bi : Builtins}

/-- **Consequence.** Strengthen the entry relation and the guard, weaken the exit
    relation, and replace the value by one equal to it under the guard. -/
theorem corres_conseq {P P' : Env → S → Prop} {G G' : S → Prop} {e : ImpExpr}
    {V V' : S → Value} {Q Q' : Env → S → Prop} (h : Corres bi P G e V Q)
    (hP : ∀ env σ, P' env σ → G' σ → P env σ) (hG : ∀ σ, G' σ → G σ)
    (hV : ∀ σ, G' σ → V σ = V' σ) (hQ : ∀ env σ, G' σ → Q env σ → Q' env σ) :
    Corres bi P' G' e V' Q' := by
  rw [corres_iff_wp] at h ⊢
  intro σ hG' env hP'
  refine wp_mono (h σ (hG σ hG') env (hP env σ hP' hG')) ?_ ?_ <;>
    exact fun _ s _ ⟨hv, hq⟩ => ⟨hv.trans (hV σ hG'), hQ s σ hG' hq⟩

theorem corres_lit (P : Env → S → Prop) (G : S → Prop) (l : ImpLit) :
    Corres bi P G (.lit l) (fun _ => Value.ofLit l) P :=
  corres_iff_wp.mpr fun _ _ _ hP => wp_lit.mpr (wpPost_self.mpr ⟨rfl, hP⟩)

theorem corres_unitVal (P : Env → S → Prop) (G : S → Prop) :
    Corres bi P G .unitVal (fun _ => .unit) P :=
  corres_iff_wp.mpr fun _ _ _ hP => wp_unitVal.mpr ⟨rfl, hP⟩

/-- A variable read returns the value the entry relation places at the name. -/
theorem corres_var {P : Env → S → Prop} {G : S → Prop} {x : String} {V : S → Value}
    (h : ∀ env σ, P env σ → G σ → env x = some (V σ)) :
    Corres bi P G (.var x) V P :=
  corres_iff_wp.mpr fun σ hG env hP =>
    wp_var.mpr ⟨_, h env σ hP hG, wpPost_self.mpr ⟨rfl, hP⟩⟩

/-- **`let`.** The bound value is not a control-flow value; the body runs from the exit
    environment of the bound expression extended at the name, related by `P₂`. -/
theorem corres_letBind {P Q₁ P₂ Q : Env → S → Prop} {G : S → Prop} {x : String}
    {val body : ImpExpr} {V₁ V : S → Value}
    (hval : Corres bi P G val V₁ Q₁) (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false)
    (hlink : ∀ env σ, Q₁ env σ → G σ → P₂ (env.extend x (V₁ σ)) σ)
    (hbody : Corres bi P₂ G body V Q) :
    Corres bi P G (.letBind x val body) V Q := by
  rw [corres_iff_wp] at hval hbody ⊢
  intro σ hG env hP
  rw [wp_letBind]
  refine wp_mono (hval σ hG env hP) ?_ ?_
  · rintro v s _ ⟨rfl, hQ₁⟩
    exact hbody σ hG _ (hlink s σ hQ₁ hG)
  · rintro v s hc ⟨rfl, -⟩
    rw [hplain σ hG] at hc
    cases hc

/-- **Sequence.** The first expression returns a value that is not a control-flow value;
    the second runs from its exit relation. -/
theorem corres_seq {P Q₁ Q : Env → S → Prop} {G : S → Prop} {e1 e2 : ImpExpr}
    {V₁ V : S → Value}
    (h1 : Corres bi P G e1 V₁ Q₁) (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false)
    (h2 : Corres bi Q₁ G e2 V Q) :
    Corres bi P G (.seq e1 e2) V Q := by
  rw [corres_iff_wp] at h1 h2 ⊢
  intro σ hG env hP
  rw [wp_seq]
  refine wp_mono (h1 σ hG env hP) (fun v s _ ⟨_, hQ₁⟩ => h2 σ hG s hQ₁) ?_
  rintro v s hc ⟨rfl, -⟩
  rw [hplain σ hG] at hc
  cases hc

/-- **Conditional.** The condition returns `.bool (C σ)`; each branch runs under the
    guard extended by the value of the condition. -/
theorem corres_ifThenElse {P Q₁ Q : Env → S → Prop} {G : S → Prop} {c t e : ImpExpr}
    {C : S → Bool} {V : S → Value}
    (hc : Corres bi P G c (fun σ => .bool (C σ)) Q₁)
    (ht : Corres bi Q₁ (fun σ => G σ ∧ C σ = true) t V Q)
    (he : Corres bi Q₁ (fun σ => G σ ∧ C σ = false) e V Q) :
    Corres bi P G (.ifThenElse c t e) V Q := by
  rw [corres_iff_wp] at hc ht he ⊢
  intro σ hG env hP
  rw [wp_ifThenElse]
  refine wp_mono (hc σ hG env hP) ?_ ?_
  · rintro v s _ ⟨rfl, hQ₁⟩
    cases hC : C σ
    · exact Or.inr ⟨rfl, he σ ⟨hG, hC⟩ s hQ₁⟩
    · exact Or.inl ⟨rfl, ht σ ⟨hG, hC⟩ s hQ₁⟩
  · rintro v s hcf ⟨rfl, -⟩
    cases hcf

theorem corresArgs_nil (P : Env → S → Prop) (G : S → Prop) :
    CorresArgs bi P G [] (fun _ => []) P :=
  corresArgs_iff_wpArgs.mpr fun _ _ _ hP => wpArgs_nil.mpr ⟨rfl, hP⟩

theorem corresArgs_cons {P Q₁ Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {es : List ImpExpr} {V₁ : S → Value} {Vs : S → List Value}
    (he : Corres bi P G e V₁ Q₁) (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false)
    (hes : CorresArgs bi Q₁ G es Vs Q) :
    CorresArgs bi P G (e :: es) (fun σ => V₁ σ :: Vs σ) Q := by
  rw [corres_iff_wp] at he
  rw [corresArgs_iff_wpArgs] at hes ⊢
  intro σ hG env hP
  rw [wpArgs_cons]
  refine wp_mono (he σ hG env hP) ?_ ?_
  · rintro v s _ ⟨rfl, hQ₁⟩
    obtain ⟨vs, s', hE, rfl, hQ⟩ := hes σ hG s hQ₁
    exact ⟨_, s', hE, rfl, hQ⟩
  · rintro v s hc ⟨rfl, -⟩
    rw [hplain σ hG] at hc
    cases hc

/-- **Leaf call.** The arguments return `Vs σ` and the builtin table maps them to
    `V σ`. -/
theorem corres_app {P Q : Env → S → Prop} {G : S → Prop} {f : String} {args : List ImpExpr}
    {Vs : S → List Value} {V : S → Value}
    (hargs : CorresArgs bi P G args Vs Q) (hbi : ∀ σ, G σ → bi f (Vs σ) = some (V σ)) :
    Corres bi P G (.app f args) V Q :=
  corres_iff_wp.mpr fun σ hG env hP => by
    obtain ⟨vs, s, hE, rfl, hQ⟩ := corresArgs_iff_wpArgs.mp hargs σ hG env hP
    exact wp_app.mpr ⟨_, s, hE, V σ, hbi σ hG, wpPost_self.mpr ⟨rfl, hQ⟩⟩

theorem corres_tuple {P Q : Env → S → Prop} {G : S → Prop} {es : List ImpExpr}
    {Vs : S → List Value} (h : CorresArgs bi P G es Vs Q) :
    Corres bi P G (.tuple es) (fun σ => .tuple (Vs σ)) Q :=
  corres_iff_wp.mpr fun σ hG env hP => by
    obtain ⟨vs, s, hE, rfl, hQ⟩ := corresArgs_iff_wpArgs.mp h σ hG env hP
    exact wp_tuple.mpr ⟨_, s, hE, rfl, hQ⟩

/-- **Projection.** Index `i` of the value, read by `Value.projIdx`. -/
theorem corres_proj {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr} {i : Nat}
    {W V : S → Value} (h : Corres bi P G e W Q)
    (hplain : ∀ σ, G σ → (W σ).isControlFlow = false)
    (hp : ∀ σ, G σ → (W σ).projIdx i = some (V σ)) :
    Corres bi P G (.proj e i) V Q := by
  rw [corres_iff_wp] at h ⊢
  intro σ hG env hP
  rw [wp_proj]
  refine wp_mono (h σ hG env hP) ?_ ?_
  · rintro v s _ ⟨rfl, hQ⟩
    exact ⟨V σ, hp σ hG, wpPost_self.mpr ⟨rfl, hQ⟩⟩
  · rintro v s hc ⟨rfl, -⟩
    rw [hplain σ hG] at hc
    cases hc

theorem corres_typeAscription {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (ty : String) (h : Corres bi P G e V Q) :
    Corres bi P G (.typeAscription e ty) V Q :=
  corres_iff_wp.mpr fun σ hG env hP => wp_typeAscription.mpr (corres_iff_wp.mp h σ hG env hP)

theorem corres_borrow {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q) :
    Corres bi P G (.borrow e) V Q :=
  corres_iff_wp.mpr fun σ hG env hP => wp_borrow.mpr (corres_iff_wp.mp h σ hG env hP)

theorem corres_deref {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q) :
    Corres bi P G (.deref e) V Q :=
  corres_iff_wp.mpr fun σ hG env hP => wp_deref.mpr (corres_iff_wp.mp h σ hG env hP)

/-- **`break`.** The value is tagged `controlFlow true`. -/
theorem corres_cfBreak {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q)
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    Corres bi P G (.cfBreak e) (fun σ => .controlFlow true (V σ)) Q := by
  rw [corres_iff_wp] at h ⊢
  intro σ hG env hP
  rw [wp_cfBreak]
  refine wp_mono (h σ hG env hP) (fun _ _ _ ⟨hv, hQ⟩ => ⟨hv ▸ rfl, hQ⟩) ?_
  rintro v s hc ⟨rfl, -⟩
  rw [hplain σ hG] at hc
  cases hc

/-- **`continue`.** The value is tagged `controlFlow false`. -/
theorem corres_cfContinue {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q)
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    Corres bi P G (.cfContinue e) (fun σ => .controlFlow false (V σ)) Q := by
  rw [corres_iff_wp] at h ⊢
  intro σ hG env hP
  rw [wp_cfContinue]
  refine wp_mono (h σ hG env hP) (fun _ _ _ ⟨hv, hQ⟩ => ⟨hv ▸ rfl, hQ⟩) ?_
  rintro v s hc ⟨rfl, -⟩
  rw [hplain σ hG] at hc
  cases hc

end Judgment

/-! ## Counted loops -/

section Loops

/-- The fold over `n` indices from `i`: the recursion equation of the runtime's
    `Hax.foldRange.go`. -/
def foldFrom {A : Type} (f : Int → A → A) : Nat → Int → A → A
  | 0, _, a => a
  | n + 1, i, a => foldFrom f n (i + 1) (f i a)

/-- The fold over `n` indices from `i` whose step may stop with `.error b`: the recursion
    equation of the runtime's `Hax.forFold.go`, with `ControlFlow.Break b` as `.error b`
    and `ControlFlow.Continue a` as `.ok a`. -/
def foldFromE {A B : Type} (f : Int → A → Except B A) : Nat → Int → A → Except B A
  | 0, _, a => .ok a
  | n + 1, i, a =>
    match f i a with
    | .error b => .error b
    | .ok a' => foldFromE f n (i + 1) a'

/-- The fold over `[lo, hi)`: `Hax.foldRange lo hi a f`. -/
def foldRangeSpec {A : Type} (lo hi : Int) (a : A) (f : Int → A → A) : A :=
  foldFrom f (hi - lo).toNat lo a

/-- The stopping fold over `[lo, hi)`: `Hax.forFold lo hi a f` read through `Except`. -/
def foldRangeE {A B : Type} (lo hi : Int) (a : A) (f : Int → A → Except B A) : Except B A :=
  foldFromE f (hi - lo).toNat lo a

theorem foldFromE_ok {A B : Type} (f : Int → A → A) :
    ∀ (n : Nat) (i : Int) (a : A),
      foldFromE (B := B) (fun i a => .ok (f i a)) n i a = .ok (foldFrom f n i a)
  | 0, _, _ => rfl
  | n + 1, i, a => foldFromE_ok f n (i + 1) (f i a)

/-- The value a counted loop returns: `.unit` when it runs to the end, the break value
    otherwise. -/
def loopVal {S A B : Type} (W : S → B → Value) (σ : S) : Except B A → Value
  | .ok _ => .unit
  | .error b => W σ b

/-- The exit relation of a counted loop: the invariant at the upper bound when it runs to
    the end, the break relation otherwise. -/
def loopExit {S A B : Type} (Inv : Env → S → Int → A → Prop) (Brk : Env → S → B → Prop)
    (σ : S) (hi : Int) : Except B A → Env → Prop
  | .ok a => fun env => Inv env σ hi a
  | .error b => fun env => Brk env σ b

variable {S A B : Type} {bi : Builtins}

/-- The body correspondence of a counted loop with loop variable `var`, invariant `Inv`,
    step `f` and break relation `Brk`: from an environment satisfying the invariant at
    index `i` and accumulator `a` with `var` bound to `i`, under `G σ` and
    `loF σ ≤ i < hiF σ`, the body ends in the invariant at `i + 1` when the step continues
    and in `Brk` when it stops. -/
def LoopBody (bi : Builtins) (var : String) (body : ImpExpr) (G : S → Prop)
    (loF hiF : S → Int) (f : S → Int → A → Except B A) (Inv : Env → S → Int → A → Prop)
    (Brk : Env → S → B → Prop) (Vb : S × Int × A → Value) : Prop :=
  Corres bi (fun env t => Inv env t.1 t.2.1 t.2.2 ∧ env var = some (.int t.2.1))
    (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Vb
    (fun env t => match f t.1 t.2.1 t.2.2 with
      | .ok a' => Inv env t.1 (t.2.1 + 1) a'
      | .error b => Brk env t.1 b)

/-- **Counted loop with an exit.** `forFold var lo hi body` over the bounds `loF σ ≤ hiF σ`
    corresponds to the stopping fold `foldRangeE (loF σ) (hiF σ) (a₀ σ) (f σ)`: the loop
    returns `.unit` and ends in the invariant at `hiF σ` when every step continues, and
    returns `W σ b` and ends in `Brk` when a step stops with `b`. The accumulator is
    carried by the environment through `Inv`; `hext` states that binding the loop
    variable preserves the invariant. -/
theorem corres_forFoldE {P Q₁ Q₂ : Env → S → Prop} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {f : S → Int → A → Except B A} {Inv : Env → S → Int → A → Prop}
    {Brk : Env → S → B → Prop} {Vb : S × Int × A → Value} {W : S → B → Value}
    (hlo : Corres bi P G lo (fun σ => .int (loF σ)) Q₁)
    (hhi : Corres bi Q₁ G hi (fun σ => .int (hiF σ)) Q₂)
    (hinit : ∀ env σ, Q₂ env σ → G σ → Inv env σ (loF σ) (a₀ σ))
    (hle : ∀ σ, G σ → loF σ ≤ hiF σ)
    (hbody : LoopBody bi var body G loF hiF f Inv Brk Vb)
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      match f t.1 t.2.1 t.2.2 with
      | .ok _ => ∀ w, Vb t ≠ .controlFlow true w
      | .error b => Vb t = .controlFlow true (W t.1 b))
    (hext : ∀ env σ i a, Inv env σ i a → Inv (env.extend var (.int i)) σ i a) :
    Corres bi P G (.forFold var lo hi body)
      (fun σ => loopVal W σ (foldRangeE (loF σ) (hiF σ) (a₀ σ) (f σ)))
      (fun env σ => loopExit Inv Brk σ (hiF σ) (foldRangeE (loF σ) (hiF σ) (a₀ σ) (f σ)) env) := by
  rw [corres_iff_wp] at hlo hhi ⊢
  intro σ hG env hP
  refine wp_forFold (a := loF σ) (b := hiF σ) (fun i s => loF σ ≤ i ∧ ∃ a, Inv s σ i a ∧
    foldFromE (f σ) (hiF σ - i).toNat i a = foldRangeE (loF σ) (hiF σ) (a₀ σ) (f σ)) ?_ ?_ ?_
  · refine wp_mono (hlo σ hG env hP) (fun _ s₁ _ ⟨hv, hQ₁⟩ => ⟨hv, ?_⟩) ?_
    · refine wp_mono (hhi σ hG s₁ hQ₁) (fun _ s₂ _ ⟨hv, hQ₂⟩ =>
        ⟨hv, Int.le_refl _, a₀ σ, hinit s₂ σ hQ₂ hG, rfl⟩) ?_
      rintro v s hc ⟨rfl, -⟩; cases hc
    · rintro v s hc ⟨rfl, -⟩; cases hc
  · rintro i s hli hib ⟨-, a, hI, hR⟩
    have hb := corres_iff_wp.mp hbody (σ, i, a) ⟨hG, hli, hib⟩ (s.extend var (.int i))
      ⟨hext s σ i a hI, Env.extend_same _ _ _⟩
    have hVt := hV (σ, i, a) hG hli hib
    have hn : (hiF σ - i).toNat = (hiF σ - (i + 1)).toNat + 1 := by omega
    rw [hn] at hR
    simp only [foldFromE] at hR
    simp only at hb hVt
    cases hf : f σ i a with
    | error b =>
      simp only [hf] at hb hVt hR
      refine wp_mono hb ?_ fun _ s' _ ⟨hv, hBrk⟩ =>
        Or.inl ⟨_, hv.trans hVt, wpPost_self.mpr ⟨by rw [← hR]; rfl, by rw [← hR]; exact hBrk⟩⟩
      rintro v s' hc ⟨rfl, -⟩
      rw [hVt] at hc
      cases hc
    | ok a' =>
      simp only [hf] at hb hVt hR
      refine wp_mono hb (fun _ s' _ ⟨_, hQ⟩ => ⟨by omega, a', hQ, hR⟩) ?_
      rintro v s' hc ⟨rfl, hQ⟩
      obtain ⟨c, w, hw⟩ : ∃ c w, Vb (σ, i, a) = .controlFlow c w := by
        cases h' : Vb (σ, i, a) <;> rw [h'] at hc <;> first | exact ⟨_, _, rfl⟩ | cases hc
      cases c
      · exact Or.inr ⟨w, hw, by omega, a', hQ, hR⟩
      · exact absurd hw (hVt w)
  · rintro s ⟨-, a, hI, hR⟩
    rw [Int.max_eq_right (hle σ hG)] at hI hR
    rw [show (hiF σ - hiF σ).toNat = 0 by omega] at hR
    exact ⟨by rw [← hR]; rfl, by rw [← hR]; exact hI⟩

/-- **Counted loop.** `forFold var lo hi body` whose body never breaks corresponds to the
    fold `foldRangeSpec (loF σ) (hiF σ) (a₀ σ) (g σ)`: it returns `.unit` and ends in the
    invariant at `hiF σ`. -/
theorem corres_forFold {P Q₁ Q₂ : Env → S → Prop} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {g : S → Int → A → A} {Inv : Env → S → Int → A → Prop} {Vb : S × Int × A → Value}
    (hlo : Corres bi P G lo (fun σ => .int (loF σ)) Q₁)
    (hhi : Corres bi Q₁ G hi (fun σ => .int (hiF σ)) Q₂)
    (hinit : ∀ env σ, Q₂ env σ → G σ → Inv env σ (loF σ) (a₀ σ))
    (hle : ∀ σ, G σ → loF σ ≤ hiF σ)
    (hbody : Corres bi (fun env t => Inv env t.1 t.2.1 t.2.2 ∧ env var = some (.int t.2.1))
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Vb
      (fun env t => Inv env t.1 (t.2.1 + 1) (g t.1 t.2.1 t.2.2)))
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      ∀ w, Vb t ≠ .controlFlow true w)
    (hext : ∀ env σ i a, Inv env σ i a → Inv (env.extend var (.int i)) σ i a) :
    Corres bi P G (.forFold var lo hi body) (fun _ => .unit)
      (fun env σ => Inv env σ (hiF σ) (foldRangeSpec (loF σ) (hiF σ) (a₀ σ) (g σ))) := by
  have h := corres_forFoldE (B := Empty) (f := fun σ i a => .ok (g σ i a))
    (Brk := fun _ _ _ => False) (W := fun _ b => nomatch b) hlo hhi hinit hle hbody
    (fun t hG hlo hlt => hV t hG hlo hlt) hext
  refine corres_conseq h (fun _ _ hP _ => hP) (fun _ hG => hG) (fun σ _ => ?_)
    (fun env σ _ hQ => ?_)
  · simp only [foldRangeE, foldFromE_ok, loopVal]
  · simpa only [foldRangeE, foldFromE_ok, loopExit, foldRangeSpec] using hQ

end Loops

/-! ## A single terminating run, and functions -/

section Functions

open Std.Do

variable {S : Type} {bi : Builtins}

/-- One value run at some fuel gives the correspondence: the run is the eventual run
    (`Eval.of_run`). -/
theorem corres_of_run {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr} {V : S → Value}
    (h : ∀ env σ, P env σ → G σ → ∃ fuel env', Q env' σ ∧ denote' bi fuel e env = (.val (V σ), env')) :
    Corres bi P G e V Q :=
  corres_iff_wp.mpr fun σ hG env hP => by
    obtain ⟨_, env', hQ, hrun⟩ := h env σ hP hG
    exact ⟨V σ, env', Eval.of_run hrun, wpPost_self.mpr ⟨rfl, hQ⟩⟩

/-- The environment binding the parameters of a function: the head of the list is bound
    last and shadows the rest. -/
def bindParams : List (String × Value) → Env
  | [] => Env.empty
  | (x, v) :: ps => (bindParams ps).extend x v

/-- **The top-level form for a function.** For every argument `a` with `G a`, the run of
    the body `e` from the entry environment `entry a` returns `enc (f a)` from some fuel
    on. -/
def FnCorres (bi : Builtins) {A β : Type} [HaxEnc β] (e : ImpExpr) (entry : A → Env)
    (G : A → Prop) (f : A → β) : Prop :=
  ∀ a, G a → ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → (denote' bi fuel e (entry a)).1 = .val (enc (f a))

theorem fnCorres_of_corres {A β : Type} [HaxEnc β] {e : ImpExpr} {entry : A → Env}
    {G : A → Prop} {f : A → β} {Q : Env → A → Prop}
    (h : Corres bi (fun env a => env = entry a) G e (fun a => enc (f a)) Q) :
    FnCorres bi e entry G f := by
  intro a hG
  obtain ⟨fuel₀, env', _, hrun⟩ := h (entry a) a rfl hG
  exact ⟨fuel₀, fun fuel hf => by rw [hrun fuel hf]⟩

/-- A function correspondence is the `Option`-level refinement of `optGuard G f` by the
    eventual value `haxEval bi e`, with the entry relation `env = entry a` and the output
    relation `v = enc b`. -/
theorem fnCorres_refinesO {A β : Type} [HaxEnc β] {e : ImpExpr} {entry : A → Env}
    {G : A → Prop} [DecidablePred G] {f : A → β} (h : FnCorres bi e entry G f) :
    RefinesO (haxEval bi e) (fun env a => env = entry a) (fun v b => v = enc b) (optGuard G f) := by
  intro env a b hentry hf
  subst hentry
  unfold optGuard at hf
  by_cases hG : G a
  · rw [if_pos hG, Option.some.injEq] at hf
    subst hf
    obtain ⟨fuel₀, hrun⟩ := h a hG
    exact ⟨_, haxEval_eq hrun, rfl⟩
  · rw [if_neg hG] at hf
    exact absurd hf (by simp)

/-- A function correspondence as the `AbsProg` refinement of the `Option` program
    `optGuard G f`. -/
theorem fnCorres_absProg {A β ε : Type} [HaxEnc β] {e : ImpExpr} {entry : A → Env}
    {G : A → Prop} [DecidablePred G] {f : A → β} (h : FnCorres bi e entry G f) :
    (AbsProg.option (ε := ε) (optGuard G f)).Refines (haxEval bi e)
      (fun env a => env = entry a) (liftOk (fun v b => v = enc b)) :=
  fnCorres_refinesO h

/-- **The partial-correctness form for a function.** For every argument `a` with `G a`,
    whenever the run of `e` from `entry a` returns a value at some fuel, that value is
    `enc (f a)`. -/
def FnPartial (bi : Builtins) {A β : Type} [HaxEnc β] (e : ImpExpr) (entry : A → Env)
    (G : A → Prop) (f : A → β) : Prop :=
  ∀ a, G a → ∀ fuel v, (denote' bi fuel e (entry a)).1 = .val v → v = enc (f a)

/-- The adequacy form gives the partial-correctness form. -/
theorem fnPartial_of_fnCorres {A β : Type} [HaxEnc β] {e : ImpExpr} {entry : A → Env}
    {G : A → Prop} {f : A → β} (h : FnCorres bi e entry G f) :
    FnPartial bi e entry G f := by
  intro a hG fuel v hv
  obtain ⟨fuel₀, hrun⟩ := h a hG
  have hm := denote'_val_mono bi hv (Nat.le_max_left fuel fuel₀)
  have e₁ := hrun (max fuel fuel₀) (Nat.le_max_right _ _)
  rw [hm, hv] at e₁
  exact Outcome.val.inj e₁

/-- A `Std.Do` triple over `Option` with a trivial failure postcondition states the
    postcondition of every `some` result. -/
theorem triple_option_iff {B : Type} (x : Option B) (R : B → Prop) :
    ⦃⌜True⌝⦄ x ⦃post⟨fun b => ⌜R b⌝, fun _ => ⌜True⌝⟩⦄ ↔ ∀ b, x = some b → R b := by
  rw [Std.Do.Triple.iff]
  cases x with
  | none =>
    simp only [reduceCtorEq, false_imp_iff, implies_true, iff_true]
    intro _
    trivial
  | some b =>
    simp only [Option.some.injEq, forall_eq']
    show _ ⊢ₛ wp⟦(pure b : Option B)⟧ _ ↔ R b
    rw [WP.pure]
    simp

/-- **The adequacy form as a `Std.Do` triple.** A function correspondence is, for every
    argument, the triple over the `Option` program `optGuard G f a` whose postcondition on a
    result `b` is that the run returns `enc b` from some fuel on. -/
theorem fnCorres_iff_triple {A β : Type} [HaxEnc β] {e : ImpExpr} {entry : A → Env}
    {G : A → Prop} [DecidablePred G] {f : A → β} :
    FnCorres bi e entry G f ↔ ∀ a,
      ⦃⌜True⌝⦄ optGuard G f a
      ⦃post⟨fun b => ⌜∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
          (denote' bi fuel e (entry a)).1 = .val (enc b)⌝, fun _ => ⌜True⌝⟩⦄ := by
  simp only [triple_option_iff]
  constructor
  · intro h a b hb
    unfold optGuard at hb
    by_cases hG : G a
    · rw [if_pos hG, Option.some.injEq] at hb
      subst hb
      exact h a hG
    · rw [if_neg hG] at hb
      exact absurd hb (by simp)
  · intro h a hG
    exact h a (f a) (by simp [optGuard, hG])

end Functions

end Hax.Ascent
