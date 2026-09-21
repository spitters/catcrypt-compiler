/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.Square

/-!
# The sequencing normal form and the Kleisli horizontal composition

`Hax/Ascent/Square.lean` composes squares horizontally with `corres_seq`. This module
puts two variants of that horizontal direction beside it: the free-monoid presentation
of `.seq`, and a composition built from `corres_letBind` and `corres_var`.

## The free-monoid presentation of `.seq`

`seqFlatten e` is the list of the non-`.seq` leaves of `e` in evaluation order and
`seqOfList` rebuilds a right-nested sequence from a list. `seqFlatten` is a monoid map:
`seqFlatten (.seq e₁ e₂) = seqFlatten e₁ ++ seqFlatten e₂`, so the two bracketings of a
three-leg chain have the same normal form (`seqFlatten_assoc`). `seqOfList` is a section
of it up to the run: `denote'_seqOfList_seqFlatten` identifies the run of the normal form
with the run of `e` at every fuel and environment, so expressions with the same normal
form have the same run (`denote'_of_seqFlatten_eq`) and the same `Corres` squares
(`corres_of_seqFlatten_eq`). The round trip `seqOfList (seqFlatten e) = e` holds for an
`e` that is not a `.seq` (`seqOfList_seqFlatten_of_not_seq`) and fails in general, since
`seqFlatten` reassociates; `seqFlatten_seqOfList` and `seqFlatten_idem` are the
idempotence of the normal form.

The `denote'` clause for `.seq` propagates a control-flow value and an error without
running the second leg, which makes `denote'_seq_assoc` hold with no hypothesis on the
legs: `Square.seq_assoc_run` is its special case where both legs return a plain value
with known exit environments. `corres_seq_assoc_iff` is the resulting equivalence of the
two bracketings' `Corres` statements, which strengthens `Square.corres_seq_assoc` from
"both are derivable from the same leg data" to "each follows from the other".

## The Kleisli horizontal composition

`HArrowK` is a horizontal arrow carrying, besides the program, the value function and
the square, the plainness of its value under the guard. `hcompK` composes with
`corres_letBind` at a name `x`, binding the first arrow's value; `hidK` is `corres_var`
reading that name back. `corres_letBind`'s two side conditions behave differently:
`hplain` is the `plain` field of the first arrow, and `hlink` is discharged outright by
taking the second arrow's entry relation to be `extendRel x V Q`, the image of the first
arrow's exit relation under binding `x`.

* Associativity. `denote'_letBind_assoc` holds with no hypothesis, for the same reason
  as `.seq`, so the two bracketings of a three-arrow chain are equivalent as `Corres`
  statements (`corres_letBind_assoc_iff`), agree as runs (`hcompK_assoc_run`) and carry
  the same value function (`hcompK_assoc_value`). The two bracketings are composable
  with the same leg data: the entry relation `hcompK` demands of its second argument is
  the same in both.
* Left unit. Under `hread` — the entry relation places `V σ` at `x` — the entry
  relation is its own extension (`extendRel_eq_self`) and the composite's run is the
  run of the second leg, so the two `Corres` statements are equivalent
  (`corres_letBind_var_left_iff`).
* Right unit. The composite's value function is the *first* leg's
  (`hcompK_hidK_value`), which is what `corres_seq` discards. The composite is still not
  the first leg: its run binds `x` in the exit environment (`letBind_var_exit_extends`,
  and `letBind_var_run_ne_of_unbound` exhibits an environment where the two runs
  differ). Under `hread` for the exit relation the law holds in the direction
  composition needs, over the unchanged boundary `(P, G, V, Q)`
  (`corres_letBind_var_right`), and it holds in that direction only:
  `corres_letBind_var_right_not_iff` exhibits an arrow, with both boundary relations
  reading `x` at its value, whose composite square holds while its own does not.

  The failure is located: the composite's run *does* determine the first leg's
  (`letBind_var_run_inv`), so the composite's square gives the first leg's square at the
  exit relation pulled back along the binding (`corres_letBind_var_right_pullback`), and
  the one missing step is `Q env σ` from `Q (env.extend x (V σ)) σ` at `env` the first
  leg's own exit environment. That step cannot be assumed: a relation closed under that
  lowering and satisfying `hread` is empty under the guard
  (`not_exit_of_read_of_lower`), since removing `x` from an environment it holds at
  produces an environment it must also hold at and cannot read `x` in.

## Which structure each of the three algebras is

* The `corres_seq` algebra of `Square.lean`: a strict category vertically; horizontally
  associative and left-unital up to the equality of `denote'` runs (`corres_seq_assoc`,
  `corres_seq_assoc_iff`, `corres_seq_unitVal_left_iff`) with no right unit, since the
  composite's value function is the second leg's. A double semicategory, with a left
  unit but no two-sided one.
* The `hcompK` algebra of this module: a double semicategory whose horizontal
  composition is associative up to the equality of runs, with a left unit at the entry
  relations that read `x` and a right unit in one direction at the exit relations that
  read `x`. Not a category, and not one on the relations that read `x` either: `hidK`
  exists at exactly those relations, and `corres_letBind_var_right_not_iff` refutes the
  right unit there, so the sub-algebra they span is again a double semicategory with a
  one-sided unit.
* The machine-side algebra of `Ascent/SquareStrict.lean`: a strict double category. All
  three horizontal laws are equalities of programs (`List.append_assoc`,
  `List.nil_append`, `List.append_nil`) and of proofs, and the interchange law is `rfl`.

## Main definitions

* `seqFlatten`, `seqOfList` — the normal form of `.seq` and its section
* `denote'_seqOfList_seqFlatten`, `denote'_of_seqFlatten_eq`, `corres_of_seqFlatten_eq` —
  the run and the square are invariant under normalisation
* `seqOfList_seqFlatten_of_not_seq`, `seqFlatten_seqOfList`, `seqFlatten_idem` — the
  round trip on normal forms
* `denote'_seq_assoc`, `corres_seq_assoc_iff` — hypothesis-free associativity of `.seq`
* `extendRel`, `HArrowK`, `hcompK`, `hidK` — the Kleisli horizontal arrows
* `denote'_letBind_assoc`, `corres_letBind_assoc_iff`, `hcompK_assoc_run`,
  `hcompK_assoc_value` — associativity
* `corres_letBind_var_left_iff` — the left unit
* `corres_letBind_var_right`, `hcompK_hidK_value`, `letBind_var_exit_extends`,
  `letBind_var_run_ne_of_unbound` — the right unit
* `letBind_var_run_inv`, `corres_letBind_var_right_pullback`,
  `corres_letBind_var_right_not_iff`, `not_exit_of_read_of_lower` — the failure of the
  right unit as an equivalence, and where it fails
* `denote'_assign_tuple_nil` — the run of an assignment of the empty tuple
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {S : Type} {bi : Builtins}

/-! ## The free-monoid presentation of `.seq` -/

/-- The list of the non-`.seq` leaves of an expression, in evaluation order. -/
def seqFlatten : ImpExpr → List ImpExpr
  | .seq e₁ e₂ => seqFlatten e₁ ++ seqFlatten e₂
  | e => [e]

/-- The right-nested sequence of a list of expressions; the empty list is `.unitVal`. -/
def seqOfList : List ImpExpr → ImpExpr
  | [] => .unitVal
  | [e] => e
  | e :: es => .seq e (seqOfList es)

/-- `seqFlatten` takes `.seq` to `++`. -/
theorem seqFlatten_seq (e₁ e₂ : ImpExpr) :
    seqFlatten (.seq e₁ e₂) = seqFlatten e₁ ++ seqFlatten e₂ := rfl

/-- Every expression has at least one leaf. -/
theorem seqFlatten_ne_nil (e : ImpExpr) : seqFlatten e ≠ [] := by
  induction e using ImpExpr.ind <;> simp_all [seqFlatten]

theorem seqOfList_singleton (e : ImpExpr) : seqOfList [e] = e := rfl

theorem seqOfList_cons (e : ImpExpr) {es : List ImpExpr} (h : es ≠ []) :
    seqOfList (e :: es) = .seq e (seqOfList es) := by
  cases es with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- The two bracketings of a three-leg chain have the same normal form. -/
theorem seqFlatten_assoc (e₁ e₂ e₃ : ImpExpr) :
    seqFlatten (.seq (.seq e₁ e₂) e₃) = seqFlatten (.seq e₁ (.seq e₂ e₃)) := by
  simp only [seqFlatten_seq, List.append_assoc]

/-! ## Runs of `.seq` -/

/-- **Associativity of `.seq` on runs, with no hypothesis on the legs.** The `.seq`
    clause of `denote'` returns a control-flow value or an error without running its
    second argument, so both bracketings run the legs in the same order and stop at the
    same point. `Square.seq_assoc_run` is the case where the first two legs return plain
    values at known exit environments. -/
theorem denote'_seq_assoc (fuel : Nat) (e₁ e₂ e₃ : ImpExpr) (env : Env) :
    denote' bi fuel (.seq (.seq e₁ e₂) e₃) env
      = denote' bi fuel (.seq e₁ (.seq e₂ e₃)) env := by
  simp only [denote', stateM_bind_apply]
  rcases h : denote' bi fuel e₁ env with ⟨r, s⟩
  cases r with
  | val v => cases v <;> rfl
  | _ => rfl

/-- Runs that agree on each leg agree on the sequence. -/
theorem denote'_seq_congr (fuel : Nat) {a a' b b' : ImpExpr}
    (ha : ∀ env, denote' bi fuel a env = denote' bi fuel a' env)
    (hb : ∀ env, denote' bi fuel b env = denote' bi fuel b' env) (env : Env) :
    denote' bi fuel (.seq a b) env = denote' bi fuel (.seq a' b') env := by
  simp only [denote', stateM_bind_apply, ha env]
  rcases h : denote' bi fuel a' env with ⟨r, s⟩
  cases r with
  | val v => cases v <;> first | exact hb s | rfl
  | _ => rfl

/-- Rebuilding a concatenation is sequencing the two rebuilt halves, on runs. -/
theorem denote'_seqOfList_append (fuel : Nat) (l₁ l₂ : List ImpExpr)
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (env : Env) :
    denote' bi fuel (seqOfList (l₁ ++ l₂)) env
      = denote' bi fuel (.seq (seqOfList l₁) (seqOfList l₂)) env := by
  induction l₁ generalizing env with
  | nil => exact absurd rfl h₁
  | cons x xs ih =>
    cases xs with
    | nil => rw [List.singleton_append, seqOfList_cons x h₂, seqOfList_singleton]
    | cons y ys =>
      have hne : (y :: ys) ++ l₂ ≠ [] := by simp
      have hxs' : (y :: ys) ≠ [] := by simp
      rw [List.cons_append, seqOfList_cons x hne, seqOfList_cons x hxs',
        denote'_seq_assoc]
      exact denote'_seq_congr fuel (fun _ => rfl) (fun e => ih hxs' e) env

/-- **The run is invariant under normalisation.** Rebuilding an expression from its
    leaves changes the bracketing of `.seq` and nothing else. -/
theorem denote'_seqOfList_seqFlatten (fuel : Nat) (e : ImpExpr) (env : Env) :
    denote' bi fuel (seqOfList (seqFlatten e)) env = denote' bi fuel e env := by
  induction e using ImpExpr.ind generalizing env with
  | seq e₁ e₂ ih₁ ih₂ =>
    rw [seqFlatten_seq,
      denote'_seqOfList_append fuel _ _ (seqFlatten_ne_nil e₁) (seqFlatten_ne_nil e₂)]
    exact denote'_seq_congr fuel (fun env => ih₁ env) (fun env => ih₂ env) env
  | _ => rfl

/-- Expressions with the same normal form have the same run. -/
theorem denote'_of_seqFlatten_eq (fuel : Nat) {e e' : ImpExpr}
    (h : seqFlatten e = seqFlatten e') (env : Env) :
    denote' bi fuel e env = denote' bi fuel e' env := by
  rw [← denote'_seqOfList_seqFlatten (bi := bi) fuel e env,
    ← denote'_seqOfList_seqFlatten (bi := bi) fuel e' env, h]

/-- Programs with the same runs at every fuel and environment carry the same squares. -/
theorem corres_congr_run {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    {e e' : ImpExpr} (h : ∀ fuel env, denote' bi fuel e env = denote' bi fuel e' env) :
    Corres bi P G e V Q ↔ Corres bi P G e' V Q := by
  constructor
  · intro hc env σ hP hG
    obtain ⟨f₀, env', hQ, hrun⟩ := hc env σ hP hG
    exact ⟨f₀, env', hQ, fun fuel hf => by rw [← h fuel env]; exact hrun fuel hf⟩
  · intro hc env σ hP hG
    obtain ⟨f₀, env', hQ, hrun⟩ := hc env σ hP hG
    exact ⟨f₀, env', hQ, fun fuel hf => by rw [h fuel env]; exact hrun fuel hf⟩

/-- **Squares are invariant under normalisation of `.seq`.** -/
theorem corres_of_seqFlatten_eq {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    {e e' : ImpExpr} (h : seqFlatten e = seqFlatten e') :
    Corres bi P G e V Q ↔ Corres bi P G e' V Q :=
  corres_congr_run (fun fuel env => denote'_of_seqFlatten_eq fuel h env)

/-- **The two bracketings of a three-leg chain state equivalent squares.** -/
theorem corres_seq_assoc_iff {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    {e₁ e₂ e₃ : ImpExpr} :
    Corres bi P G (.seq (.seq e₁ e₂) e₃) V Q ↔ Corres bi P G (.seq e₁ (.seq e₂ e₃)) V Q :=
  corres_of_seqFlatten_eq (seqFlatten_assoc e₁ e₂ e₃)

/-! ## Normal forms of `seqOfList` -/

/-- An expression that is not a `.seq` is its own single leaf. -/
theorem seqFlatten_of_not_seq {e : ImpExpr} (h : ∀ a b, e ≠ .seq a b) :
    seqFlatten e = [e] := by
  cases e <;> first | rfl | exact absurd rfl (h _ _)

/-- An expression that is not a `.seq` is the rebuilding of its own flattening. -/
theorem seqOfList_seqFlatten_of_not_seq {e : ImpExpr} (h : ∀ a b, e ≠ .seq a b) :
    seqOfList (seqFlatten e) = e := by
  rw [seqFlatten_of_not_seq h, seqOfList_singleton]

/-- Rebuilding a list of non-`.seq` expressions and flattening again returns the list. -/
theorem seqFlatten_seqOfList : ∀ (l : List ImpExpr), l ≠ [] →
    (∀ e ∈ l, ∀ a b, e ≠ .seq a b) → seqFlatten (seqOfList l) = l
  | [], h, _ => absurd rfl h
  | [e], _, hl => by
    rw [seqOfList_singleton, seqFlatten_of_not_seq (hl e (by simp))]
  | e :: f :: l, _, hl => by
    have hne : (f :: l) ≠ [] := by simp
    rw [seqOfList_cons e hne, seqFlatten_seq,
      seqFlatten_of_not_seq (hl e (by simp)),
      seqFlatten_seqOfList (f :: l) hne (fun a ha => hl a (by simp [ha]))]
    rfl

/-- Every leaf of a flattening is a leaf. -/
theorem seqFlatten_mem_not_seq (e : ImpExpr) :
    ∀ f ∈ seqFlatten e, ∀ a b, f ≠ .seq a b := by
  induction e using ImpExpr.ind with
  | seq e₁ e₂ ih₁ ih₂ =>
    intro f hf
    rw [seqFlatten_seq, List.mem_append] at hf
    exact hf.elim (ih₁ f) (ih₂ f)
  | _ => intro f hf; simp only [seqFlatten, List.mem_singleton] at hf; subst hf; simp

/-- Normalisation is idempotent. -/
theorem seqFlatten_idem (e : ImpExpr) :
    seqFlatten (seqOfList (seqFlatten e)) = seqFlatten e :=
  seqFlatten_seqOfList (seqFlatten e) (seqFlatten_ne_nil e) (seqFlatten_mem_not_seq e)

/-! ## The Kleisli horizontal arrows -/

/-- Extending an environment at a name with the value it already holds is the
    identity. `Env.extend_self` of `hax-lean` is the same statement and carries the
    proof. -/
theorem extend_of_read {env : Env} {x : String} {v : Value} (h : env x = some v) :
    env.extend x v = env := Env.extend_self env x v h

/-- The image of an exit relation under binding `x` to the value `V σ`: the entry
    relation of the body of a `.letBind` that binds `x`. -/
def extendRel (x : String) (V : S → Value) (Q : Env → S → Prop) : Env → S → Prop :=
  fun env σ => ∃ env₀, Q env₀ σ ∧ env = env₀.extend x (V σ)

/-- A relation that places `V σ` at `x` under the guard is its own extension at `x`. -/
theorem extendRel_eq_self {x : String} {V : S → Value} {Q : Env → S → Prop}
    {G : S → Prop} (hread : ∀ env σ, Q env σ → G σ → env x = some (V σ))
    {env : Env} {σ : S} (hG : G σ) : extendRel x V Q env σ ↔ Q env σ := by
  constructor
  · rintro ⟨env₀, hQ, rfl⟩
    rwa [extend_of_read (hread env₀ σ hQ hG)]
  · intro hQ
    exact ⟨env, hQ, (extend_of_read (hread env σ hQ hG)).symm⟩

/-- A horizontal arrow of the Kleisli composition: a program, the value it stands for,
    the plainness of that value under the guard, and the square. -/
structure HArrowK (bi : Builtins) (P : Env → S → Prop) (G : S → Prop)
    (Q : Env → S → Prop) where
  /-- The program. -/
  e : ImpExpr
  /-- The value the abstract state produces. -/
  V : S → Value
  /-- The value is never a control-flow value under the guard. -/
  plain : ∀ σ, G σ → (V σ).isControlFlow = false
  /-- The square. -/
  hCorres : Corres bi P G e V Q

/-- **Kleisli composition at the name `x`.** `corres_letBind`: the first arrow's value
    is bound at `x` and the second runs from the extended environment. Both side
    conditions of `corres_letBind` are discharged — `hplain` by the first arrow's
    `plain` field, `hlink` by the second arrow's entry relation being `extendRel`. -/
def hcompK (x : String) {P Q R : Env → S → Prop} {G : S → Prop}
    (h₁ : HArrowK bi P G Q) (h₂ : HArrowK bi (extendRel x h₁.V Q) G R) :
    HArrowK bi P G R where
  e := .letBind x h₁.e h₂.e
  V := h₂.V
  plain := h₂.plain
  hCorres :=
    corres_letBind h₁.hCorres h₁.plain (fun env _σ hQ _ => ⟨env, hQ, rfl⟩) h₂.hCorres

/-- **The Kleisli identity at `x`.** `corres_var`: reading back the name, at a relation
    that places a plain value there. -/
def hidK (x : String) {P : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hread : ∀ env σ, P env σ → G σ → env x = some (V σ))
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    HArrowK bi P G P where
  e := .var x
  V := V
  plain := hplain
  hCorres := corres_var hread

/-! ## Associativity -/

/-- **Associativity of `.letBind` on runs, at one name, with no hypothesis.** Both
    bracketings run the legs in the same order and extend the environment at `x` with
    the same values; a control-flow value or an error stops both at the same leg. -/
theorem denote'_letBind_assoc (fuel : Nat) (x : String) (e₁ e₂ e₃ : ImpExpr) (env : Env) :
    denote' bi fuel (.letBind x (.letBind x e₁ e₂) e₃) env
      = denote' bi fuel (.letBind x e₁ (.letBind x e₂ e₃)) env := by
  simp only [denote', stateM_bind_apply]
  rcases h : denote' bi fuel e₁ env with ⟨r, s⟩
  cases r with
  | val v => cases v <;> rfl
  | _ => rfl

/-- **The two bracketings of a three-arrow Kleisli chain state equivalent squares.** -/
theorem corres_letBind_assoc_iff {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    {x : String} {e₁ e₂ e₃ : ImpExpr} :
    Corres bi P G (.letBind x (.letBind x e₁ e₂) e₃) V Q
      ↔ Corres bi P G (.letBind x e₁ (.letBind x e₂ e₃)) V Q :=
  corres_congr_run (fun fuel env => denote'_letBind_assoc fuel x e₁ e₂ e₃ env)

/-- The two bracketings of a three-arrow chain have the same runs. -/
theorem hcompK_assoc_run (x : String) {P Q R T : Env → S → Prop} {G : S → Prop}
    (h₁ : HArrowK bi P G Q) (h₂ : HArrowK bi (extendRel x h₁.V Q) G R)
    (h₃ : HArrowK bi (extendRel x h₂.V R) G T) (fuel : Nat) (env : Env) :
    denote' bi fuel (hcompK x (hcompK x h₁ h₂) h₃).e env
      = denote' bi fuel (hcompK x h₁ (hcompK x h₂ h₃)).e env :=
  denote'_letBind_assoc fuel x h₁.e h₂.e h₃.e env

/-- The two bracketings carry the same value function. -/
theorem hcompK_assoc_value (x : String) {P Q R T : Env → S → Prop} {G : S → Prop}
    (h₁ : HArrowK bi P G Q) (h₂ : HArrowK bi (extendRel x h₁.V Q) G R)
    (h₃ : HArrowK bi (extendRel x h₂.V R) G T) :
    (hcompK x (hcompK x h₁ h₂) h₃).V = (hcompK x h₁ (hcompK x h₂ h₃)).V := rfl

/-! ## The left unit -/

/-- **The left unit, up to equivalence of the squares.** At an entry relation that
    places the plain value `V₀ σ` at `x`, binding `x` to the value read from `x` and
    then running `e` is the run of `e`. -/
theorem corres_letBind_var_left_iff {P Q : Env → S → Prop} {G : S → Prop}
    {V V₀ : S → Value} {x : String} {e : ImpExpr}
    (hread : ∀ env σ, P env σ → G σ → env x = some (V₀ σ))
    (hplain : ∀ σ, G σ → (V₀ σ).isControlFlow = false) :
    Corres bi P G (.letBind x (.var x) e) V Q ↔ Corres bi P G e V Q := by
  have key : ∀ (fuel : Nat) (env : Env) (σ : S), P env σ → G σ →
      denote' bi fuel (.letBind x (.var x) e) env = denote' bi fuel e env := by
    intro fuel env σ hP hG
    have hx : env x = some (V₀ σ) := hread env σ hP hG
    rw [denote'_letBind bi fuel (denote'_var bi fuel hx) (hplain σ hG),
      extend_of_read hx]
  constructor
  · intro hc env σ hP hG
    obtain ⟨f₀, env', hQ, hrun⟩ := hc env σ hP hG
    exact ⟨f₀, env', hQ, fun fuel hf => by
      rw [← key fuel env σ hP hG]; exact hrun fuel hf⟩
  · intro hc env σ hP hG
    obtain ⟨f₀, env', hQ, hrun⟩ := hc env σ hP hG
    exact ⟨f₀, env', hQ, fun fuel hf => by
      rw [key fuel env σ hP hG]; exact hrun fuel hf⟩

/-! ## The right unit -/

/-- The value function of a composite with the identity on the right is the first
    arrow's, which is what `Square.hcomp` with `Square.hid` discards. -/
theorem hcompK_hidK_value (x : String) {P Q : Env → S → Prop} {G : S → Prop}
    (h₁ : HArrowK bi P G Q)
    (hread : ∀ env σ, extendRel x h₁.V Q env σ → G σ → env x = some (h₁.V σ)) :
    (hcompK x h₁ (hidK (bi := bi) x hread h₁.plain)).V = h₁.V := rfl

/-- The run of `.letBind x e (.var x)` returns the value of `e` at the exit environment
    of `e` extended at `x` with that value. -/
theorem letBind_var_exit_extends (fuel : Nat) {x : String} {e : ImpExpr} {env s : Env}
    {v : Value} (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.letBind x e (.var x)) env = (.val v, s.extend x v) := by
  rw [denote'_letBind bi fuel h hv]
  exact denote'_var bi fuel (Env.extend_same s x v)

/-- **The composite's run determines the first leg's run.** A run of
    `.letBind x e (.var x)` returning a plain value comes from a run of `e` returning
    that value, at an exit environment the composite's extends at `x`. -/
theorem letBind_var_run_inv (fuel : Nat) {x : String} {e : ImpExpr} {env env'' : Env}
    {v : Value} (hv : v.isControlFlow = false)
    (h : denote' bi fuel (.letBind x e (.var x)) env = (.val v, env'')) :
    ∃ s, denote' bi fuel e env = (.val v, s) ∧ env'' = s.extend x v := by
  rcases hr : denote' bi fuel e env with ⟨r, s⟩
  cases r with
  | val w =>
    cases w with
    | controlFlow b u =>
      rw [show denote' bi fuel (.letBind x e (.var x)) env
          = (Outcome.val (.controlFlow b u), s) from by
        simp only [denote', stateM_bind_apply, hr]; rfl] at h
      injection h with h1 _
      injection h1 with h2
      exact absurd hv (by rw [← h2]; simp)
    | _ =>
      rw [letBind_var_exit_extends fuel hr rfl] at h
      injection h with h1 h2
      injection h1 with h3
      subst h3
      exact ⟨s, rfl, h2.symm⟩
  | _ =>
    rw [show denote' bi fuel (.letBind x e (.var x)) env = (_, s) from by
      simp only [denote', stateM_bind_apply, hr]; rfl] at h
    cases h

/-- The extra binding is observable: at an environment where `x` is unbound, the run of
    `.letBind x .unitVal (.var x)` and the run of `.unitVal` differ. -/
theorem letBind_var_run_ne_of_unbound (fuel : Nat) (x : String) :
    denote' bi fuel (.letBind x .unitVal (.var x)) Env.empty
      ≠ denote' bi fuel .unitVal Env.empty := by
  rw [letBind_var_exit_extends fuel (denote'_unitVal bi fuel Env.empty) rfl,
    denote'_unitVal]
  intro h
  have hs : Env.empty.extend x Value.unit = Env.empty := congrArg Prod.snd h
  have hx : (Env.empty.extend x Value.unit) x = Env.empty x := by rw [hs]
  simp [Env.extend_same, Env.empty] at hx

/-- **The right unit, in the direction composition needs.** At an exit relation that
    places the arrow's plain value at `x`, composing with `hidK` on the right keeps the
    boundary `(P, G, V, Q)`: the value function is unchanged and the exit relation is
    re-established at the extended environment. -/
theorem corres_letBind_var_right {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    {x : String} {e : ImpExpr}
    (hread : ∀ env σ, Q env σ → G σ → env x = some (V σ))
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) (h : Corres bi P G e V Q) :
    Corres bi P G (.letBind x e (.var x)) V Q := by
  intro env σ hP hG
  obtain ⟨f₀, env', hQ, hrun⟩ := h env σ hP hG
  refine ⟨f₀, env', hQ, fun fuel hf => ?_⟩
  rw [letBind_var_exit_extends fuel (hrun fuel hf) (hplain σ hG),
    extend_of_read (hread env' σ hQ hG)]

/-- **What the composite's square does determine.** The square over
    `.letBind x e (.var x)` gives the square over `e` at the exit relation pulled back
    along the binding, with no hypothesis on the exit relation. -/
theorem corres_letBind_var_right_pullback {P Q : Env → S → Prop} {G : S → Prop}
    {V : S → Value} {x : String} {e : ImpExpr}
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false)
    (h : Corres bi P G (.letBind x e (.var x)) V Q) :
    Corres bi P G e V (fun env σ => Q (env.extend x (V σ)) σ) := by
  intro env σ hP hG
  obtain ⟨f₀, env'', hQ, hrun⟩ := h env σ hP hG
  obtain ⟨s, hs, hext⟩ := letBind_var_run_inv f₀ (hplain σ hG) (hrun f₀ (Nat.le_refl f₀))
  refine ⟨f₀, s, ?_, fun fuel hf => ?_⟩
  · show Q (s.extend x (V σ)) σ
    exact hext ▸ hQ
  · rw [denote'_val_mono bi (by rw [hs]) hf]; exact hs

/-- The run of an assignment of the empty tuple. -/
theorem denote'_assign_tuple_nil (fuel : Nat) (x : String) (env : Env) :
    denote' bi fuel (.assign x (.tuple [])) env
      = (.val .unit, env.extend x (.tuple [])) :=
  denote'_assign bi fuel (denote'_tuple bi fuel (denoteArgs'_nil bi fuel env)) rfl

/-- **The right unit is not an equivalence, and restricting to the relations that read
    `x` does not make it one.** Both boundary relations read `x` at the arrow's value
    `.unit`, so `hidK` exists at each; the arrow assigns another value to `x`. The
    square over `.letBind x e (.var x)` holds, because the trailing read rebinds `x` to
    the returned value, and the square over `e` does not, because `e`'s own exit
    environment holds the assigned value at `x`. -/
theorem corres_letBind_var_right_not_iff (x : String) :
    ∃ (P Q : Env → Unit → Prop) (G : Unit → Prop) (V : Unit → Value) (e : ImpExpr),
      (∀ env σ, P env σ → G σ → env x = some (V σ)) ∧
      (∀ env σ, Q env σ → G σ → env x = some (V σ)) ∧
      (∀ σ, G σ → (V σ).isControlFlow = false) ∧
      Corres bi P G (.letBind x e (.var x)) V Q ∧ ¬ Corres bi P G e V Q := by
  refine ⟨fun env _ => env x = some Value.unit, fun env _ => env x = some Value.unit,
    fun _ => True, fun _ => Value.unit, .assign x (.tuple []),
    fun _ _ h _ => h, fun _ _ h _ => h, fun _ _ => rfl, ?_, ?_⟩
  · intro env _ _ _
    exact ⟨0, (env.extend x (Value.tuple [])).extend x Value.unit,
      Env.extend_same _ x Value.unit,
      fun fuel _ => letBind_var_exit_extends fuel (denote'_assign_tuple_nil fuel x env) rfl⟩
  · intro hc
    obtain ⟨f₀, env', hQ, hrun⟩ :=
      hc (Env.empty.extend x Value.unit) () (Env.extend_same _ x Value.unit) trivial
    have h := hrun f₀ (Nat.le_refl f₀)
    rw [denote'_assign_tuple_nil] at h
    have hEnv : (Env.empty.extend x Value.unit).extend x (Value.tuple []) = env' :=
      congrArg Prod.snd h
    rw [← hEnv, Env.extend_same] at hQ
    simp at hQ

/-- **An exit relation cannot both read `x` and be closed downward under the binding at
    `x`.** The converse of `corres_letBind_var_right` needs `Q env σ` where only
    `Q (env.extend x (V σ)) σ` is available; a relation satisfying both that lowering
    property and `hread` is empty under the guard, so no hypothesis of that shape closes
    the converse at a satisfiable exit relation. -/
theorem not_exit_of_read_of_lower {x : String} {V : S → Value} {Q : Env → S → Prop}
    {G : S → Prop} (hread : ∀ env σ, Q env σ → G σ → env x = some (V σ))
    (hlower : ∀ env σ, G σ → Q (env.extend x (V σ)) σ → Q env σ)
    {env : Env} {σ : S} (hG : G σ) : ¬ Q env σ := by
  intro hQ
  have hx : env x = some (V σ) := hread env σ hQ hG
  have hre : (Env.remove env x).extend x (V σ) = env := by
    funext y
    by_cases hy : y = x
    · subst hy; simp [Env.extend, hx]
    · simp [Env.extend, Env.remove, hy]
  have hQ₀ : Q (Env.remove env x) σ := hlower _ σ hG (by rw [hre]; exact hQ)
  have hnone : (Env.remove env x) x = some (V σ) := hread _ σ hQ₀ hG
  simp [Env.remove] at hnone

end Hax.Ascent
