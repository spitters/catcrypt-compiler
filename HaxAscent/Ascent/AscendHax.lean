/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Corres
public import HaxAscent.Ascent.Wp
public import Lean
public meta import Lean

/-!
# A `SymM` generator for the `denote'` correspondence

`hax_corres` closes a goal `Corres bi P G e V Q` whose program `e` is an `ImpExpr`
literal by applying one rule per constructor.

## Binding lists

The rules are stated over `CorresB bi Γ G e V Γ'`, the correspondence whose entry and exit
relations are `Binds env (Γ σ)` and `Binds env (Γ' σ)`: the environment binds every name
of the binding list `Γ σ : List (String × Value)` to its value there (`bindLookup`, the head
shadowing the tail). A `let` extends the list, so the entry relation of every
subexpression is a concrete list, and a variable read is a lookup in it. In each rule the
value `V` and the exit list `Γ'` of the conclusion are either pattern variables or lambda
terms over the pattern variables of the premises, and every other constraint is a premise.

## The generator

`hax_corres` follows `CorresSymEngine`: the goal is hash-consed, the rules are compiled
once per call into `Sym.BackwardRule`s, indexed by the `ImpExpr` constructor, and applied
by pattern unification in a worklist over goals.

* The goal is first rewritten by `corres_of_corresB` into a `CorresB` goal whose value and
  exit list are fresh metavariables, with three consequence side conditions (entry,
  value, exit). The entry bindings are given as `hax_corres (env := Γ₀)` or read off an
  entry relation `fun env σ => env = E σ` whose `E σ` unfolds to `bindParams l`.
* A `CorresB` goal whose value is not an open metavariable is first rewritten by
  `corresB_castV`, so a rule conclusion with a lambda value always meets a metavariable,
  which pattern unification assigns (a Miller pattern).
* A counted loop `forFold` takes the next specification `(Λ, a₀, g)` of
  `loops [...]` (invariant bindings, initial accumulator, step) and is applied by
  `corresB_forFold` in `MetaM`.
* A program that is a constant is unfolded; a constructor without a rule is an error.
* Every other premise is a side condition. Side conditions are collected in creation
  order and tried after the structural phase by `hax_corres_side`: `rfl` (which assigns a
  value metavariable), the entry lemma `binds_bindParams`, and `simp` with the binding
  lemmas, the `String` equality simprocs, the lemmas given in brackets and `omega` as
  discharger. A side condition that is not closed is returned as a goal.

## Main results

* `bindLookup`, `Binds`, `binds_extend`, `binds_bindParams`, `BindsSub`, `binds_of_sub`
* `CorresB`, `CorresArgsB`, `corres_of_corresB`, `corresB_castV`, and the rules
  `corresB_lit`, `corresB_unitVal`, `corresB_var`, `corresB_letBind`, `corresB_seq`,
  `corresB_ifThenElse`, `corresArgsB_nil`, `corresArgsB_cons`, `corresB_app`,
  `corresB_tuple`, `corresB_proj`, `corresB_typeAscription`, `corresB_borrow`,
  `corresB_deref`, `corresB_cfBreak`, `corresB_cfContinue`, `corresB_forFold`
* `corresB_iff_wp` — `CorresB` as a weakest precondition
* the tactics `hax_corres` and `hax_corres_side`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## Binding lists -/

section Binds

/-- The value bound to `x` by a binding list; the head shadows the tail. -/
def bindLookup : List (String × Value) → String → Option Value
  | [], _ => none
  | (k, v) :: l, x => if x = k then some v else bindLookup l x

@[simp] theorem bindLookup_nil (x : String) : bindLookup [] x = none := rfl

@[simp] theorem bindLookup_cons (k : String) (v : Value) (l : List (String × Value))
    (x : String) : bindLookup ((k, v) :: l) x = if x = k then some v else bindLookup l x := rfl

theorem bindLookup_ite (c : Prop) [Decidable c] (l₁ l₂ : List (String × Value)) (x : String) :
    bindLookup (if c then l₁ else l₂) x = if c then bindLookup l₁ x else bindLookup l₂ x := by
  split <;> rfl

theorem ite_some_some {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  split <;> rfl

theorem ite_value_bool (c : Prop) [Decidable c] (a b : Bool) :
    (if c then Value.bool a else Value.bool b) = Value.bool (if c then a else b) := by
  split <;> rfl

theorem ite_value_int (c : Prop) [Decidable c] (a b : Int) :
    (if c then Value.int a else Value.int b) = Value.int (if c then a else b) := by
  split <;> rfl

/-- The environment binds every name of `Γ` to its value in `Γ`. -/
def Binds (env : Env) (Γ : List (String × Value)) : Prop :=
  ∀ x v, bindLookup Γ x = some v → env x = some v

theorem Binds.lookup {env : Env} {Γ : List (String × Value)} {x : String} {v : Value}
    (h : Binds env Γ) (hx : bindLookup Γ x = some v) : env x = some v :=
  h x v hx

theorem binds_extend {env : Env} {Γ : List (String × Value)} (h : Binds env Γ) (x : String)
    (v : Value) : Binds (env.extend x v) ((x, v) :: Γ) := by
  intro y w hy
  rw [bindLookup_cons] at hy
  by_cases hyx : y = x
  · subst hyx
    rw [ite_eq_left rfl] at hy
    cases hy
    exact Env.extend_same _ _ _
  · rw [ite_eq_right hyx] at hy
    rw [Env.extend_other _ _ _ _ hyx]
    exact h y w hy

theorem binds_extend_fresh {env : Env} {Γ : List (String × Value)} {x : String}
    (h : Binds env Γ) (hx : bindLookup Γ x = none) (w : Value) : Binds (env.extend x w) Γ := by
  intro y v hy
  by_cases hyx : y = x
  · subst hyx; rw [hx] at hy; cases hy
  · rw [Env.extend_other _ _ _ _ hyx]; exact h y v hy

theorem binds_cons_of {env : Env} {Γ : List (String × Value)} {x : String} {v : Value}
    (hx : env x = some v) (h : Binds env Γ) : Binds env ((x, v) :: Γ) := by
  intro y w hy
  rw [bindLookup_cons] at hy
  by_cases hyx : y = x
  · subst hyx; rw [ite_eq_left rfl] at hy; cases hy; exact hx
  · rw [ite_eq_right hyx] at hy; exact h y w hy

theorem bindParams_apply (ps : List (String × Value)) (x : String) :
    bindParams ps x = bindLookup ps x := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    by_cases hx : x = k
    · subst hx
      simp only [bindParams, bindLookup_cons]
      exact Env.extend_same _ _ _
    · simp only [bindParams, bindLookup_cons, ite_eq_right hx]
      rw [Env.extend_other _ _ _ _ hx, ih]

theorem binds_bindParams (ps : List (String × Value)) : Binds (bindParams ps) ps :=
  fun x v h => by rw [bindParams_apply]; exact h

/-- A sufficient condition for `Binds env Γ → Binds env Γ'`: each binding of `Γ'` is the
    binding of its name in `Γ`. -/
def BindsSub (Γ : List (String × Value)) : List (String × Value) → Prop
  | [] => True
  | (x, v) :: Γ' => bindLookup Γ x = some v ∧ BindsSub Γ Γ'

@[simp] theorem bindsSub_nil (Γ : List (String × Value)) : BindsSub Γ [] = True := rfl

@[simp] theorem bindsSub_cons (Γ Γ' : List (String × Value)) (x : String) (v : Value) :
    BindsSub Γ ((x, v) :: Γ') = (bindLookup Γ x = some v ∧ BindsSub Γ Γ') := rfl

theorem binds_of_sub {env : Env} {Γ : List (String × Value)} (h : Binds env Γ) :
    ∀ {Γ' : List (String × Value)}, BindsSub Γ Γ' → Binds env Γ'
  | [], _ => fun x v hx => by simp at hx
  | (_, _) :: _, ⟨hk, hs⟩ => binds_cons_of (h.lookup hk) (binds_of_sub h hs)

end Binds

/-! ## The judgment over binding lists -/

section CorresB

variable {S : Type} {bi : Builtins}

/-- `Corres` whose entry and exit relations bind the names of the binding lists `Γ σ` and
    `Γ' σ`. -/
def CorresB (bi : Builtins) (Γ : S → List (String × Value)) (G : S → Prop) (e : ImpExpr)
    (V : S → Value) (Γ' : S → List (String × Value)) : Prop :=
  Corres bi (fun env σ => Binds env (Γ σ)) G e V (fun env σ => Binds env (Γ' σ))

/-- `CorresArgs` over binding lists. -/
def CorresArgsB (bi : Builtins) (Γ : S → List (String × Value)) (G : S → Prop)
    (es : List ImpExpr) (Vs : S → List Value) (Γ' : S → List (String × Value)) : Prop :=
  CorresArgs bi (fun env σ => Binds env (Γ σ)) G es Vs (fun env σ => Binds env (Γ' σ))

/-- **`CorresB` as a weakest precondition.** The postcondition is the value `V σ` with the
    exit bindings `Γ' σ`, at plain and control-flow outcomes alike. -/
theorem corresB_iff_wp {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} :
    CorresB bi Γ G e V Γ' ↔ ∀ σ, G σ → ∀ env, Binds env (Γ σ) →
      wp bi e (fun v s => v = V σ ∧ Binds s (Γ' σ)) (fun v s => v = V σ ∧ Binds s (Γ' σ)) env :=
  corres_iff_wp

/-- **Entry and exit of a binding-list derivation.** A `CorresB` from the bindings `Γ₀`
    gives the correspondence from any entry relation that implies them, with the value
    and the exit relation weakened. -/
theorem corres_of_corresB {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (Γ₀ : S → List (String × Value)) {V' : S → Value}
    {Γ' : S → List (String × Value)} (h : CorresB bi Γ₀ G e V' Γ')
    (hP : ∀ env σ, P env σ → G σ → Binds env (Γ₀ σ))
    (hV : ∀ σ, G σ → V' σ = V σ)
    (hQ : ∀ env σ, G σ → Binds env (Γ' σ) → Q env σ) :
    Corres bi P G e V Q :=
  corres_conseq h hP (fun _ h => h) hV hQ

theorem corresB_castV {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {V V' : S → Value} (h : CorresB bi Γ G e V' Γ') (hV : ∀ σ, G σ → V' σ = V σ) :
    CorresB bi Γ G e V Γ' :=
  corres_conseq h (fun _ _ h _ => h) (fun _ h => h) hV (fun _ _ _ h => h)

theorem corresB_lit (Γ : S → List (String × Value)) (G : S → Prop) (l : ImpLit) :
    CorresB bi Γ G (.lit l) (fun _ => Value.ofLit l) Γ :=
  corres_lit _ _ l

theorem corresB_unitVal (Γ : S → List (String × Value)) (G : S → Prop) :
    CorresB bi Γ G .unitVal (fun _ => .unit) Γ :=
  corres_unitVal _ _

theorem corresB_var {Γ : S → List (String × Value)} {G : S → Prop} {x : String}
    {V : S → Value} (h : ∀ σ, G σ → bindLookup (Γ σ) x = some (V σ)) :
    CorresB bi Γ G (.var x) V Γ :=
  corres_var fun _ σ hP hG => hP.lookup (h σ hG)

theorem corresB_letBind {Γ Γ₁ Γ' : S → List (String × Value)} {G : S → Prop} {x : String}
    {val body : ImpExpr} {V₁ V : S → Value} (hval : CorresB bi Γ G val V₁ Γ₁)
    (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false)
    (hbody : CorresB bi (fun σ => (x, V₁ σ) :: Γ₁ σ) G body V Γ') :
    CorresB bi Γ G (.letBind x val body) V Γ' :=
  corres_letBind hval hplain (fun _ _ h _ => binds_extend h _ _) hbody

theorem corresB_seq {Γ Γ₁ Γ' : S → List (String × Value)} {G : S → Prop} {e1 e2 : ImpExpr}
    {V₁ V : S → Value} (h1 : CorresB bi Γ G e1 V₁ Γ₁)
    (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false) (h2 : CorresB bi Γ₁ G e2 V Γ') :
    CorresB bi Γ G (.seq e1 e2) V Γ' :=
  corres_seq h1 hplain h2

theorem corresB_ifThenElse {Γ Γ₁ Γt Γe : S → List (String × Value)} {G : S → Prop}
    {c t e : ImpExpr} {C : S → Bool} {Vt Ve : S → Value}
    (hc : CorresB bi Γ G c (fun σ => .bool (C σ)) Γ₁)
    (ht : CorresB bi Γ₁ (fun σ => G σ ∧ C σ = true) t Vt Γt)
    (he : CorresB bi Γ₁ (fun σ => G σ ∧ C σ = false) e Ve Γe) :
    CorresB bi Γ G (.ifThenElse c t e) (fun σ => if C σ = true then Vt σ else Ve σ)
      (fun σ => if C σ = true then Γt σ else Γe σ) := by
  refine corres_ifThenElse hc ?_ ?_
  · refine corres_conseq ht (fun _ _ h _ => h) (fun _ h => h) (fun σ hG => ?_) (fun env σ hG h => ?_)
    · simp only [hG.2, ite_true]
    · simp only [hG.2, ite_true]; exact h
  · refine corres_conseq he (fun _ _ h _ => h) (fun _ h => h) (fun σ hG => ?_) (fun env σ hG h => ?_)
    · simp only [hG.2]; rfl
    · simp only [hG.2]; exact h

theorem corresArgsB_nil (Γ : S → List (String × Value)) (G : S → Prop) :
    CorresArgsB bi Γ G [] (fun _ => []) Γ :=
  corresArgs_nil _ _

theorem corresArgsB_cons {Γ Γ₁ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {es : List ImpExpr} {V₁ : S → Value} {Vs : S → List Value}
    (he : CorresB bi Γ G e V₁ Γ₁) (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false)
    (hes : CorresArgsB bi Γ₁ G es Vs Γ') :
    CorresArgsB bi Γ G (e :: es) (fun σ => V₁ σ :: Vs σ) Γ' :=
  corresArgs_cons he hplain hes

theorem corresB_app {Γ Γ' : S → List (String × Value)} {G : S → Prop} {f : String}
    {args : List ImpExpr} {Vs : S → List Value} {V : S → Value}
    (hargs : CorresArgsB bi Γ G args Vs Γ') (hbi : ∀ σ, G σ → bi f (Vs σ) = some (V σ)) :
    CorresB bi Γ G (.app f args) V Γ' :=
  corres_app hargs hbi

theorem corresB_tuple {Γ Γ' : S → List (String × Value)} {G : S → Prop} {es : List ImpExpr}
    {Vs : S → List Value} (h : CorresArgsB bi Γ G es Vs Γ') :
    CorresB bi Γ G (.tuple es) (fun σ => .tuple (Vs σ)) Γ' :=
  corres_tuple h

theorem corresB_proj {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {i : Nat} {W V : S → Value} (h : CorresB bi Γ G e W Γ')
    (hplain : ∀ σ, G σ → (W σ).isControlFlow = false)
    (hp : ∀ σ, G σ → (W σ).projIdx i = some (V σ)) :
    CorresB bi Γ G (.proj e i) V Γ' :=
  corres_proj h hplain hp

theorem corresB_typeAscription {Γ Γ' : S → List (String × Value)} {G : S → Prop}
    {e : ImpExpr} {V : S → Value} (ty : String) (h : CorresB bi Γ G e V Γ') :
    CorresB bi Γ G (.typeAscription e ty) V Γ' :=
  corres_typeAscription ty h

theorem corresB_borrow {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : CorresB bi Γ G e V Γ') : CorresB bi Γ G (.borrow e) V Γ' :=
  corres_borrow h

theorem corresB_deref {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : CorresB bi Γ G e V Γ') : CorresB bi Γ G (.deref e) V Γ' :=
  corres_deref h

theorem corresB_cfBreak {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : CorresB bi Γ G e V Γ')
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    CorresB bi Γ G (.cfBreak e) (fun σ => .controlFlow true (V σ)) Γ' :=
  corres_cfBreak h hplain

theorem corresB_cfContinue {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : CorresB bi Γ G e V Γ')
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    CorresB bi Γ G (.cfContinue e) (fun σ => .controlFlow false (V σ)) Γ' :=
  corres_cfContinue h hplain

/-- **Counted loop over binding lists.** The invariant binds the names of
    `Λ σ i a`, which do not include the loop variable; the body runs from the invariant
    extended by the loop variable, and its exit bindings contain the invariant at the next
    index and the stepped accumulator. -/
theorem corresB_forFold {A : Type} {Γ Γ₁ Γ₂ : S → List (String × Value)} {G : S → Prop}
    {var : String} {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {g : S → Int → A → A} {Λ : S → Int → A → List (String × Value)}
    {Vb : S × Int × A → Value} {Γb : S × Int × A → List (String × Value)}
    (hlo : CorresB bi Γ G lo (fun σ => .int (loF σ)) Γ₁)
    (hhi : CorresB bi Γ₁ G hi (fun σ => .int (hiF σ)) Γ₂)
    (hinit : ∀ σ, G σ → BindsSub (Γ₂ σ) (Λ σ (loF σ) (a₀ σ)))
    (hle : ∀ σ, G σ → loF σ ≤ hiF σ)
    (hfresh : ∀ t : S × Int × A, bindLookup (Λ t.1 t.2.1 t.2.2) var = none)
    (hbody : CorresB bi (fun t : S × Int × A => (var, .int t.2.1) :: Λ t.1 t.2.1 t.2.2)
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Vb Γb)
    (hV : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 →
      (Vb t).isControlFlow = false)
    (hstep : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 →
      BindsSub (Γb t) (Λ t.1 (t.2.1 + 1) (g t.1 t.2.1 t.2.2))) :
    CorresB bi Γ G (.forFold var lo hi body) (fun _ => .unit)
      (fun σ => Λ σ (hiF σ) (foldRangeSpec (loF σ) (hiF σ) (a₀ σ) (g σ))) := by
  refine corres_forFold (Inv := fun env σ i a => Binds env (Λ σ i a)) (Vb := Vb) hlo hhi
    (fun env σ h hG => binds_of_sub h (hinit σ hG)) hle ?_ ?_ ?_
  · refine corres_conseq hbody (fun env t h _ => ?_) (fun _ h => h) (fun _ _ => rfl)
      (fun env t hG h => binds_of_sub h (hstep t hG))
    exact binds_cons_of h.2 h.1
  · intro t hG hlo hlt w hw
    have := hV t ⟨hG, hlo, hlt⟩
    rw [hw] at this
    cases this
  · intro env σ i a h
    exact binds_extend_fresh h (hfresh (σ, i, a)) _

end CorresB

/-! ## The generator -/

namespace AscendHax

/-- The side-condition closer of `hax_corres`: after introducing the binders, `rfl`, the
    entry lemma `binds_bindParams`, `simp` with the binding lemmas and the given lemmas
    (discharger `omega`) followed by `rfl` or `omega`, and the lookups of a `Binds`
    hypothesis for a conjunction of variable bindings. -/
syntax (name := haxCorresSide) "hax_corres_side" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| hax_corres_side $[[$ts,*]]?) => do
    let ts : Array (Lean.TSyntax `term) := match ts with
      | some ts => ts.getElems
      | none => #[]
    let ts : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) ←
      ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      intros
      first
      | done
      | rfl
      | (subst_vars; exact binds_bindParams _)
      | (try simp only [$ts,*] at *
         try simp (disch := omega) only [bindLookup_cons, bindLookup_nil, bindLookup_ite,
          bindsSub_cons, bindsSub_nil, Value.isControlFlow, Value.ofLit, ↓reduceIte,
          String.reduceEq, Option.some.injEq, Value.int.injEq, Value.bool.injEq, and_true,
          true_and, ite_self, and_self, ite_some_some, ite_value_bool, ite_value_int, enc_int,
          enc_bool, $ts,*]
         first | done | rfl | omega)
      | (rename_i hb
         try simp only [$ts,*]
         and_intros <;> exact Binds.lookup hb (by
          simp only [bindLookup_cons, bindLookup_nil, ↓reduceIte, String.reduceEq, $ts,*]))))

meta section

open Lean Meta Elab Tactic Sym

/-- The specification of one counted loop: the invariant bindings, the initial
    accumulator, the step. -/
structure LoopSpec where
  /-- `Λ : S → Int → A → List (String × Value)`. -/
  inv : Expr
  /-- `a₀ : S → A`. -/
  init : Expr
  /-- `g : S → Int → A → A`. -/
  step : Expr

/-- The generator state. -/
structure State where
  /-- Compiled backward rules by declaration name. -/
  rules : Std.HashMap Name BackwardRule := {}
  /-- Side conditions, in the order of their creation. -/
  side : Array MVarId := #[]
  /-- Data metavariables created by the rules. -/
  data : Array MVarId := #[]
  /-- The loop specifications not yet used. -/
  loops : List LoopSpec := []

/-- The generator monad. -/
abbrev M := StateRefT State SymM

/-- The backward rule of `name`, compiled on first use. -/
def ruleOf (name : Name) : M BackwardRule := do
  if let some r := (← get).rules[name]? then return r
  let r ← mkBackwardRuleFromDecl name
  modify fun s => { s with rules := s.rules.insert name r }
  return r

/-- The rule for an `ImpExpr` constructor. -/
def ctorRule : Name → Option Name
  | ``ImpExpr.lit => some ``corresB_lit
  | ``ImpExpr.unitVal => some ``corresB_unitVal
  | ``ImpExpr.var => some ``corresB_var
  | ``ImpExpr.letBind => some ``corresB_letBind
  | ``ImpExpr.seq => some ``corresB_seq
  | ``ImpExpr.ifThenElse => some ``corresB_ifThenElse
  | ``ImpExpr.app => some ``corresB_app
  | ``ImpExpr.tuple => some ``corresB_tuple
  | ``ImpExpr.proj => some ``corresB_proj
  | ``ImpExpr.typeAscription => some ``corresB_typeAscription
  | ``ImpExpr.borrow => some ``corresB_borrow
  | ``ImpExpr.deref => some ``corresB_deref
  | ``ImpExpr.cfBreak => some ``corresB_cfBreak
  | ``ImpExpr.cfContinue => some ``corresB_cfContinue
  | _ => none

/-- Apply the rule `name`, failing with an error when it does not apply. -/
def applyRule (goal : MVarId) (name : Name) : M (List MVarId) := do
  let .goals gs ← (← ruleOf name).apply goal
    | throwError "hax_corres: {name} does not apply to{indentExpr (← goal.getType)}"
  return gs

/-- Replace the argument `i` of the judgment target of `goal` by its unfolding. -/
def unfoldArg (goal : MVarId) (target : Expr) (i : Nat) (what : String) : M (List MVarId) := do
  let arg := target.getAppArgs[i]!
  let some arg' ← unfoldDefinition? arg
    | throwError "hax_corres: the {what} is not a literal{indentExpr arg}"
  let target' ← shareCommonInc (mkAppN target.getAppFn (target.getAppArgs.set! i arg'))
  return [← goal.replaceTargetDefEq target']

/-- The binder names of a `∀` telescope. -/
partial def binderNames : Expr → Array Name
  | .forallE n _ b _ => #[n] ++ binderNames b
  | _ => #[]

/-- Apply `corresB_forFold` with the next loop specification. -/
def applyForFold (goal : MVarId) (target : Expr) : M (List MVarId) := do
  let spec :: rest := (← get).loops
    | throwError "hax_corres: no loop specification for{indentExpr target}"
  modify fun s => { s with loops := rest }
  let c ← mkConstWithFreshMVarLevels ``corresB_forFold
  let cty ← Meta.inferType c
  let names := binderNames cty
  let (mvs, _, concl) ← forallMetaTelescope cty
  let pick (n : Name) : M Expr := do
    let some i := names.findIdx? (· == n) | throwError "hax_corres: no binder {n}"
    return mvs[i]!
  for (n, v) in [(`Λ, spec.inv), (`a₀, spec.init), (`g, spec.step)] do
    unless ← isDefEq (← pick n) v do
      throwError "hax_corres: the loop specification {n} does not fit{indentExpr v}"
  unless ← isDefEq concl target do
    throwError "hax_corres: corresB_forFold does not apply to{indentExpr target}"
  goal.assign (mkAppN c mvs)
  let premises := [`hlo, `hhi, `hinit, `hle, `hfresh, `hbody, `hV, `hstep]
  let mut out := []
  for n in premises.reverse do
    let m ← pick n
    let g := m.mvarId!
    let ty ← shareCommonInc (← instantiateMVars (← g.getType))
    out := (← g.replaceTargetDefEq ty) :: out
  return out

/-- Whether `e` is an unassigned metavariable after instantiation. -/
def isOpen (e : Expr) : M Bool := do
  return (← instantiateMVars e).isMVar

/-- One worklist step. -/
def step (goal : MVarId) : M (List MVarId) := goal.withContext do
  if ← goal.isAssigned then return []
  let target ← instantiateMVarsIfMVarApp (← goal.getType)
  if target.isAppOfArity ``CorresB 7 then
    let args := target.getAppArgs
    unless ← isOpen args[5]! do
      return ← applyRule goal ``corresB_castV
    let e ← instantiateMVars args[4]!
    let .const c _ := e.getAppFn | return ← unfoldArg goal target 4 "expression"
    if c == ``ImpExpr.forFold then return ← applyForFold goal target
    match ctorRule c with
    | some r => applyRule goal r
    | none =>
      if (← getConstInfo c).isCtor then
        throwError "hax_corres: no rule for the constructor {c}"
      unfoldArg goal target 4 "expression"
  else if target.isAppOfArity ``CorresArgsB 7 then
    let es ← instantiateMVars target.getAppArgs[4]!
    if es.isAppOfArity ``List.cons 3 then applyRule goal ``corresArgsB_cons
    else if es.isAppOfArity ``List.nil 1 then applyRule goal ``corresArgsB_nil
    else unfoldArg goal target 4 "argument list"
  else if ← isProp target then
    modify fun s => { s with side := s.side.push goal }
    return []
  else
    modify fun s => { s with data := s.data.push goal }
    return []

/-- Run the worklist from `goal`. -/
def work (goal : MVarId) : M Unit := do
  let mut stack := #[goal]
  while let some g := stack.back? do
    stack := stack.pop
    let gs ← step g
    stack := stack ++ gs.toArray.reverse

/-- The binding list of an entry relation `fun env σ => env = E σ` whose `E σ` unfolds to
    `bindParams l`: `fun σ => l`. -/
def entryBindings? (P : Expr) : MetaM (Option Expr) := do
  let P ← instantiateMVars P
  let .lam _ envTy b1 _ := P | return none
  let .lam nσ σTy _ _ := b1 | return none
  withLocalDeclD `env envTy fun env => withLocalDeclD nσ σTy fun σ => do
    let body ← whnfR (mkApp2 P env σ)
    let_expr Eq _ lhs rhs := body | return none
    unless lhs == env do return none
    let mut r := rhs
    for _ in [0:32] do
      if r.isAppOfArity ``bindParams 1 then
        return some (← mkLambdaFVars #[σ] r.appArg!)
      let some r' ← unfoldDefinition? r | return none
      r := r'
    return none

/-- Open the goal `Corres bi P G e V Q` into a `CorresB` goal with open value and exit
    bindings; returns it with the three consequence side conditions. -/
def prepare (goal : MVarId) (Γ₀? : Option Expr) : MetaM (MVarId × List MVarId) :=
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``Corres 7 do
    throwError "hax_corres: the goal is not a Corres judgment{indentExpr target}"
  let P := target.getAppArgs[2]!
  let Γ₀ ← match Γ₀? with
    | some g => pure g
    | none =>
      match ← entryBindings? P with
      | some g => pure g
      | none => throwError "hax_corres: give the entry bindings with `hax_corres (env := Γ₀)`"
  let c ← mkConstWithFreshMVarLevels ``corres_of_corresB
  let cty ← Meta.inferType c
  let (mvs, _, concl) ← forallMetaTelescope cty
  let names := binderNames cty
  let some iΓ := names.findIdx? (· == `Γ₀) | throwError "hax_corres: internal"
  unless ← isDefEq mvs[iΓ]! Γ₀ do throwError "hax_corres: the entry bindings do not fit"
  unless ← isDefEq concl target do throwError "hax_corres: internal: conclusion mismatch"
  goal.assign (mkAppN c mvs)
  let get (n : Name) : MetaM MVarId := do
    let some i := names.findIdx? (· == n) | throwError "hax_corres: internal"
    return mvs[i]!.mvarId!
  return (← get `h, [← get `hP, ← get `hV, ← get `hQ])

/-- Run the structural phase on `goal`; returns the side conditions in creation order and
    the data metavariables. -/
def structural (goal : MVarId) (loops : List LoopSpec) : MetaM (Array MVarId × Array MVarId) := do
  SymM.run do
    let goal ← preprocessMVar goal
    let go : M (Array MVarId × Array MVarId) := do
      work goal
      let s ← get
      return (s.side, s.data)
    go.run' { loops }


/-- The generator on the main goal. -/
def run (Γ₀? : Option Expr) (loops : List LoopSpec) (simps : Array (TSyntax `term)) :
    TacticM Unit := do
  let goal :: rest ← getUnsolvedGoals | throwNoGoalsToBeSolved
  let (g, cons) ← prepare goal Γ₀?
  let (side, data) ← structural g loops
  let mut residual := #[]
  for s in side ++ cons.toArray do
    if ← s.isAssigned then continue
    setGoals [s]
    let saved ← saveState
    try
      withoutRecover <| evalTactic (← `(tactic| hax_corres_side [$simps,*]))
    catch _ =>
      saved.restore
      setGoals [s]
    for r in ← getGoals do
      unless ← r.isAssigned do residual := residual.push r
  for d in data do
    unless ← d.isAssigned do residual := residual.push d
  setGoals (residual.toList ++ rest)

end

/-- One loop specification `(Λ, a₀, g)`: the invariant bindings
    `Λ : S → Int → A → List (String × Value)`, the initial accumulator `a₀ : S → A` and the
    step `g : S → Int → A → A`. -/
syntax haxLoopSpec := "(" term ", " term ", " term ")"

/-- **`hax_corres`.** Close `Corres bi P G e V Q` for an `ImpExpr` literal `e` by the
    per-constructor rules over binding lists. The entry bindings are `env := Γ₀` or read
    off `P = fun env σ => env = E σ` with `E σ` unfolding to `bindParams l`; each counted
    loop takes the next specification of `loops`; side conditions are tried by
    `hax_corres_side` with the lemmas in brackets, and those not closed are returned as
    goals. -/
syntax (name := haxCorres) "hax_corres" (" (" &"env" " := " term ")")?
  (" [" term,* "]")? (&" loops " "[" haxLoopSpec,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| hax_corres $[(env := $env?)]? $[[$simps?,*]]? $[loops [$specs?,*]]?) => do
    let Γ₀? ← env?.mapM fun t => Term.elabTerm t none
    let specs := (specs?.map (·.getElems)).getD #[]
    let mut specList := []
    for sp in specs.reverse do
      match sp with
      | `(haxLoopSpec| ($i, $a, $s)) =>
        let i ← Term.elabTerm i none
        let a ← Term.elabTerm a none
        let s ← Term.elabTerm s none
        specList := { inv := i, init := a, step := s } :: specList
      | _ => throwUnsupportedSyntax
    Term.synthesizeSyntheticMVarsNoPostponing
    let simps := (simps?.map (·.getElems)).getD #[]
    run Γ₀? specList simps

end AscendHax

end Hax.Ascent
