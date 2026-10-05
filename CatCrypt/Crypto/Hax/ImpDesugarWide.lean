/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AnfLowCT

/-!
# The `128`-bit widening patterns as word calls

Rust code on `u64` words reaches a `128`-bit intermediate in two ways that hax extracts as
fixed chains of calls:

* the high word of a product, `((a as u128) * (b as u128) >> 64) as u64`, the chain
  `cast#64 (Shr#128 (Mul (cast#128 a) (cast#128 b)) 64)`;
* a modular product, `((a as u128) * (b as u128) % (n as u128)) as u64`, the chain
  `cast#64 (Rem (Mul (cast#128 a) (cast#128 b)) (cast#128 n))`, inline or with the product
  bound to a local `x` first: `let x = Mul (cast#128 a) (cast#128 b); cast#64 (Rem x
  (cast#128 n))`.

`desugarWide e` replaces the first chain by the word call `mulhi#64 a b` and the second by
the word call `mulmod#64 a b n`, when `a`, `b` and `n` are literals or variables (`atom`).
The pass descends through `letBind` and `seq`. The inline chains are replaced as a bound
expression, as a statement of a sequence and as the result; the bound form is replaced
where it is the result (along bodies of `letBind` and second parts of `seq`), and its local
`x` is then unbound in the final environment (`wideLocal`). Every other expression is
unchanged, so a `128`-bit call outside the chains stays in place.

The denotation lemmas are stated over a builtin table `bi` with a hypothesis on the value
of the chains: `WideSpec bi` (the chain and the word call agree where both are defined)
for two successful runs, and `WideTotal bi` (the word call is defined with the value of
the chain where the chain is defined) for the run of the result from the run of the
source.

## Main definitions

* `atom`, `atomOff` — the literals and variables, and those that are not a given variable.
* `mulHiOf`, `mulModOf`, `mulModLetOf` — the operands of an expression that is one of the
  three chains.
* `desugarLeaf`, `desugarAt`, `desugarWide` — the pass at one expression, the pass with a
  flag for the result position, and the pass.
* `wideLocal` — the local of the bound form the pass removes at the result.
* `mulWideVal`, `mulHiVal`, `mulModVal` — the values of the product and of the two chains
  under a table.
* `WideSpec`, `WideTotal` — the hypotheses on the builtins.
* `wideName`, `wideFree`, `wideFreeL` — the `128`-bit call names, and the expressions of
  the constructors `lit`, `var`, `unitVal`, `app`, `tuple`, `letBind`, `seq`, `assign`,
  `typeAscription`, `ifThenElse` and `forFold` that call none of them.
* `wideOK` — the expressions whose pieces the pass visits are chains or `wideFree`.

## Main results

* `mulHiOf_eq_some`, `mulModOf_eq_some`, `mulModLetOf_eq_some` — a recognised expression
  is the chain on atoms.
* `desugarLeaf_denote`, `desugarAt_denote`, `desugarWide_denote` — under `WideSpec`, two
  successful runs of the source and of the result have the same value, and the same final
  environment off `wideLocal`.
* `desugarLeaf_run`, `desugarAt_run`, `desugarWide_run` — under `WideTotal`, a successful
  run of the source gives a run of the result to the same value.
* `desugarLeaf_of_none` — an expression that is no chain is unchanged.
* `desugarWide_wideFree` — on a `wideOK` expression the result of the pass is `wideFree`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpDesugarWide

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote' denoteApp' denoteArgs')

/-! ## 1. The chains and the pass -/

/-- The name of the word call for the high word of a product. -/
def mulHiName : String := "mulhi#64"

/-- The name of the word call for a product modulo a third word. -/
def mulModName : String := "mulmod#64"

/-- A literal or a variable. -/
def atom : ImpExpr → Bool
  | .lit _ | .var _ => true
  | _ => false

/-- A literal, or a variable other than `x`. -/
def atomOff (x : String) : ImpExpr → Bool
  | .lit _ => true
  | .var y => y != x
  | _ => false

/-- The operands of an expression that is the chain
    `cast#64 (Shr#128 (Mul (cast#128 a) (cast#128 b)) 64)` on atoms. -/
def mulHiOf (e : ImpExpr) : Option (ImpExpr × ImpExpr) :=
  match e with
  | .app f [.app g [.app m [.app c₁ [a], .app c₂ [b]], .lit (.int k)]] =>
      if f = "cast#64" ∧ g = "Shr#128" ∧ m = "Mul" ∧ c₁ = "cast#128" ∧ c₂ = "cast#128" ∧
          k = 64 ∧ atom a = true ∧ atom b = true
      then some (a, b) else none
  | _ => none

/-- The operands of an expression that is the chain
    `cast#64 (Rem (Mul (cast#128 a) (cast#128 b)) (cast#128 n))` on atoms. -/
def mulModOf (e : ImpExpr) : Option (ImpExpr × ImpExpr × ImpExpr) :=
  match e with
  | .app f [.app g [.app m [.app c₁ [a], .app c₂ [b]], .app c₃ [n]]] =>
      if f = "cast#64" ∧ g = "Rem" ∧ m = "Mul" ∧ c₁ = "cast#128" ∧ c₂ = "cast#128" ∧
          c₃ = "cast#128" ∧ atom a = true ∧ atom b = true ∧ atom n = true
      then some (a, b, n) else none
  | _ => none

/-- The operands of an expression that is the bound form
    `let x = Mul (cast#128 a) (cast#128 b); cast#64 (Rem x (cast#128 n))` on atoms, the
    modulus `n` not the variable `x`. -/
def mulModLetOf (e : ImpExpr) : Option (ImpExpr × ImpExpr × ImpExpr) :=
  match e with
  | .letBind x (.app m [.app c₁ [a], .app c₂ [b]]) (.app f [.app g [.var y, .app c₃ [n]]]) =>
      if f = "cast#64" ∧ g = "Rem" ∧ m = "Mul" ∧ c₁ = "cast#128" ∧ c₂ = "cast#128" ∧
          c₃ = "cast#128" ∧ y = x ∧ atom a = true ∧ atom b = true ∧ atomOff x n = true
      then some (a, b, n) else none
  | _ => none

/-- The pass at one expression: an inline chain is the word call on its operands, and
    every other expression is unchanged. -/
def desugarLeaf (e : ImpExpr) : ImpExpr :=
  match mulHiOf e with
  | some (a, b) => .app mulHiName [a, b]
  | none =>
      match mulModOf e with
      | some (a, b, n) => .app mulModName [a, b, n]
      | none => e

/-- The pass with a flag for the result position: through `letBind` and `seq`, an inline
    chain is replaced everywhere, and the bound form of the modular product where the
    flag holds. -/
def desugarAt (t : Bool) : ImpExpr → ImpExpr
  | .letBind x v b =>
      match (if t then mulModLetOf (.letBind x v b) else none) with
      | some (a, b', n) => .app mulModName [a, b', n]
      | none => .letBind x (desugarAt false v) (desugarAt t b)
  | .seq a b => .seq (desugarAt false a) (desugarAt t b)
  | e => desugarLeaf e

/-- The pass: `desugarAt` at the result position. -/
def desugarWide (e : ImpExpr) : ImpExpr := desugarAt true e

/-- The local of the bound form that `desugarWide` removes at the result of `e`. -/
def wideLocal : ImpExpr → Option String
  | .letBind x v b =>
      match mulModLetOf (.letBind x v b) with
      | some _ => some x
      | none => wideLocal b
  | .seq _ b => wideLocal b
  | _ => none

theorem mulHiOf_eq_some {e a b : ImpExpr} (h : mulHiOf e = some (a, b)) :
    e = .app "cast#64" [.app "Shr#128" [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]],
      .lit (.int 64)]] ∧ atom a = true ∧ atom b = true := by
  unfold mulHiOf at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, ha, hb⟩ := hc
      cases h
      exact ⟨rfl, ha, hb⟩
    · cases h
  · cases h

theorem mulModOf_eq_some {e a b n : ImpExpr} (h : mulModOf e = some (a, b, n)) :
    e = .app "cast#64" [.app "Rem" [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]],
      .app "cast#128" [n]]] ∧ atom a = true ∧ atom b = true ∧ atom n = true := by
  unfold mulModOf at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, ha, hb, hn⟩ := hc
      cases h
      exact ⟨rfl, ha, hb, hn⟩
    · cases h
  · cases h

theorem mulModLetOf_eq_some {x : String} {v body a b n : ImpExpr}
    (h : mulModLetOf (.letBind x v body) = some (a, b, n)) :
    v = .app "Mul" [.app "cast#128" [a], .app "cast#128" [b]] ∧
      body = .app "cast#64" [.app "Rem" [.var x, .app "cast#128" [n]]] ∧
      atom a = true ∧ atom b = true ∧ atomOff x n = true := by
  unfold mulModLetOf at h
  split at h
  · rename_i heq
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ha, hb, hn⟩ := hc
      cases h
      cases heq
      exact ⟨rfl, rfl, ha, hb, hn⟩
    · cases h
  · cases h

/-- An expression that is no inline chain is unchanged by `desugarLeaf`. -/
theorem desugarLeaf_of_none {e : ImpExpr} (h₁ : mulHiOf e = none) (h₂ : mulModOf e = none) :
    desugarLeaf e = e := by
  simp only [desugarLeaf, h₁, h₂]

/-! ## 2. The hypotheses on the builtins -/

/-- A value that is not a control-flow value. -/
def Plain (v : Value) : Prop := ∀ k p, v ≠ .controlFlow k p

/-- The value of `Mul (cast#128 a) (cast#128 b)` under `bi` on the values of `a`, `b`. -/
def mulWideVal (bi : Builtins) (va vb : Value) : Option Value :=
  (bi "cast#128" [va]).bind fun p => (bi "cast#128" [vb]).bind fun q => bi "Mul" [p, q]

/-- The value of the high-word chain under `bi` on the values of its operands. -/
def mulHiVal (bi : Builtins) (va vb : Value) : Option Value :=
  (mulWideVal bi va vb).bind fun s =>
    (bi "Shr#128" [s, .int 64]).bind fun r => bi "cast#64" [r]

/-- The value of the modular-product chain under `bi` on the values of its operands. -/
def mulModVal (bi : Builtins) (va vb vn : Value) : Option Value :=
  (mulWideVal bi va vb).bind fun s =>
    (bi "cast#128" [vn]).bind fun n => (bi "Rem" [s, n]).bind fun r => bi "cast#64" [r]

/-- Each chain agrees with its word call on the operands where both are defined. -/
structure WideSpec (bi : Builtins) : Prop where
  /-- The high-word chain and `mulhi#64`. -/
  mulhi : ∀ va vb r w, mulHiVal bi va vb = some r → bi mulHiName [va, vb] = some w → r = w
  /-- The modular-product chain and `mulmod#64`. -/
  mulmod : ∀ va vb vn r w, mulModVal bi va vb vn = some r →
    bi mulModName [va, vb, vn] = some w → r = w

/-- Each word call is defined, with the value of its chain, on the operands where the
    chain is defined. -/
structure WideTotal (bi : Builtins) : Prop where
  /-- The high-word chain and `mulhi#64`. -/
  mulhi : ∀ va vb r, mulHiVal bi va vb = some r → bi mulHiName [va, vb] = some r
  /-- The modular-product chain and `mulmod#64`. -/
  mulmod : ∀ va vb vn r, mulModVal bi va vb vn = some r →
    bi mulModName [va, vb, vn] = some r

theorem WideTotal.spec {bi : Builtins} (h : WideTotal bi) : WideSpec bi where
  mulhi va vb r w hr hw := by
    rw [h.mulhi va vb r hr] at hw
    exact Option.some.inj hw
  mulmod va vb vn r w hr hw := by
    rw [h.mulmod va vb vn r hr] at hw
    exact Option.some.inj hw

/-! ## 3. Runs of calls on atoms -/

section Runs

variable {bi : Builtins} {fuel : Nat}

/-- One-step unfolding of `denote'` at a call. -/
theorem denote'_app_run (f : String) (args : List ImpExpr) (env : Env) :
    denote' bi fuel (.app f args) env =
      match denoteArgs' bi fuel args env with
      | (some vals, e1) =>
          match bi f vals with
          | some v => (.val v, e1)
          | none => (.err s!"unknown function or bad args: {f}", e1)
      | (none, e1) => (.err "non-value in function arguments", e1) := by
  simp only [denote', denoteApp', bind, StateT.bind, pure]
  rcases denoteArgs' bi fuel args env with ⟨o, e1⟩
  rcases o with _ | vals
  · rfl
  · cases h : bi f vals <;> simp only [h] <;> rfl

/-- One-step unfolding of `denoteArgs'` at a nonempty list. -/
theorem denoteArgs'_cons_run (e : ImpExpr) (es : List ImpExpr) (env : Env) :
    denoteArgs' bi fuel (e :: es) env =
      match denote' bi fuel e env with
      | (.val (.controlFlow _ _), e1) => (none, e1)
      | (.val v, e1) =>
          ((denoteArgs' bi fuel es e1).1.map (v :: ·), (denoteArgs' bi fuel es e1).2)
      | (_, e1) => (none, e1) := by
  simp only [denoteArgs', bind, StateT.bind, pure]
  rcases denote' bi fuel e env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

/-- `denoteArgs'` at the empty list. -/
theorem denoteArgs'_nil_run (env : Env) : denoteArgs' bi fuel [] env = (some [], env) := by
  simp only [denoteArgs']; rfl

/-- `denoteArgs'` at a list whose head runs to a value that is not a control-flow value. -/
theorem denoteArgs'_cons_val {e : ImpExpr} {es : List ImpExpr} {env x : Env} {u : Value}
    (h : denote' bi fuel e env = (.val u, x)) (hu : Plain u) :
    denoteArgs' bi fuel (e :: es) env =
      ((denoteArgs' bi fuel es x).1.map (u :: ·), (denoteArgs' bi fuel es x).2) := by
  rw [denoteArgs'_cons_run, h]
  cases u
  case controlFlow k p => exact absurd rfl (hu k p)
  all_goals rfl

/-- A call that runs to a value: its arguments run to values and the builtin is defined
    on them. -/
theorem denote'_app_val {f : String} {args : List ImpExpr} {env e₁ : Env} {v : Value}
    (h : denote' bi fuel (.app f args) env = (.val v, e₁)) :
    ∃ vals, denoteArgs' bi fuel args env = (some vals, e₁) ∧ bi f vals = some v := by
  rw [denote'_app_run] at h
  rcases hd : denoteArgs' bi fuel args env with ⟨o, e1⟩
  rw [hd] at h
  rcases o with _ | vals
  · cases h
  · dsimp only at h
    rcases hb : bi f vals with _ | u
    · rw [hb] at h; cases h
    · rw [hb] at h; cases h; exact ⟨vals, rfl, hb⟩

/-- A nonempty list of arguments that runs to values: the head runs to a value that is
    not a control-flow value, and the tail runs to values from the environment the head
    leaves. -/
theorem denoteArgs'_cons_some {e : ImpExpr} {es : List ImpExpr} {env e₁ : Env}
    {vs : List Value} (h : denoteArgs' bi fuel (e :: es) env = (some vs, e₁)) :
    ∃ u x vs0, denote' bi fuel e env = (.val u, x) ∧ Plain u ∧
      denoteArgs' bi fuel es x = (some vs0, e₁) ∧ vs = u :: vs0 := by
  rw [denoteArgs'_cons_run] at h
  rcases hd : denote' bi fuel e env with ⟨o, x⟩
  rw [hd] at h
  have key : ∀ u : Value, Plain u →
      ((denoteArgs' bi fuel es x).1.map (u :: ·), (denoteArgs' bi fuel es x).2) =
        (some vs, e₁) →
      ∃ u' x' vs0, (Outcome.val u, x) = (Outcome.val u', x') ∧ Plain u' ∧
        denoteArgs' bi fuel es x' = (some vs0, e₁) ∧ vs = u' :: vs0 := by
    intro u hu h'
    have h1 := congrArg Prod.fst h'
    have h2 := congrArg Prod.snd h'
    rcases hr : denoteArgs' bi fuel es x with ⟨o', x'⟩
    rw [hr] at h1 h2
    dsimp only at h1 h2
    rcases o' with _ | vs0
    · cases h1
    · cases h1; cases h2; exact ⟨u, x, vs0, rfl, hu, hr, rfl⟩
  rcases o with u | _ | _ | _ | _
  · cases u
    case controlFlow k p => dsimp only at h; cases h
    all_goals exact key _ (by intro k p hh; cases hh) h
  all_goals (dsimp only at h; cases h)

/-- A `letBind` that runs to a value that is not a control-flow value: its bound
    expression runs to such a value and its body runs to the value from the extended
    environment. -/
theorem denote'_letBind_val {n : String} {a b : ImpExpr} {env e₁ : Env} {v : Value}
    (h : denote' bi fuel (.letBind n a b) env = (.val v, e₁)) (hv : Plain v) :
    ∃ u x, denote' bi fuel a env = (.val u, x) ∧ Plain u ∧
      denote' bi fuel b (Hax.Env.extend x n u) = (.val v, e₁) := by
  rw [Hax.denote'_letBind_run] at h
  rcases hd : denote' bi fuel a env with ⟨o, x⟩
  rw [hd] at h
  rcases o with u | _ | _ | _ | _
  · cases u
    case controlFlow k p => dsimp only at h; cases h; exact absurd rfl (hv _ _)
    all_goals exact ⟨_, x, rfl, (by intro k p hh; cases hh), h⟩
  all_goals (dsimp only at h; cases h)

/-- A `seq` that runs to a value that is not a control-flow value: its first expression
    runs to such a value and its second runs to the value from the environment the first
    leaves. -/
theorem denote'_seq_val {a b : ImpExpr} {env e₁ : Env} {v : Value}
    (h : denote' bi fuel (.seq a b) env = (.val v, e₁)) (hv : Plain v) :
    ∃ u x, denote' bi fuel a env = (.val u, x) ∧ Plain u ∧
      denote' bi fuel b x = (.val v, e₁) := by
  rw [Hax.denote'_seq_run] at h
  rcases hd : denote' bi fuel a env with ⟨o, x⟩
  rw [hd] at h
  rcases o with u | _ | _ | _ | _
  · cases u
    case controlFlow k p => dsimp only at h; cases h; exact absurd rfl (hv _ _)
    all_goals exact ⟨_, x, rfl, (by intro k p hh; cases hh), h⟩
  all_goals (dsimp only at h; cases h)

/-- A `letBind` whose bound expression runs to a value that is not a control-flow value
    runs as its body from the extended environment. -/
theorem denote'_letBind_of_val {n : String} {a b : ImpExpr} {env x : Env} {u : Value}
    (h : denote' bi fuel a env = (.val u, x)) (hu : Plain u) :
    denote' bi fuel (.letBind n a b) env = denote' bi fuel b (Hax.Env.extend x n u) := by
  rw [Hax.denote'_letBind_run, h]
  cases u
  case controlFlow k p => exact absurd rfl (hu k p)
  all_goals rfl

/-- A `seq` whose first expression runs to a value that is not a control-flow value runs
    as its second from the environment the first leaves. -/
theorem denote'_seq_of_val {a b : ImpExpr} {env x : Env} {u : Value}
    (h : denote' bi fuel a env = (.val u, x)) (hu : Plain u) :
    denote' bi fuel (.seq a b) env = denote' bi fuel b x := by
  rw [Hax.denote'_seq_run, h]
  cases u
  case controlFlow k p => exact absurd rfl (hu k p)
  all_goals rfl

/-- An atom that runs to a value leaves the environment unchanged. -/
theorem atom_env {e : ImpExpr} {env x : Env} {u : Value} (ha : atom e = true)
    (h : denote' bi fuel e env = (.val u, x)) : x = env := by
  cases e
  case lit l => rw [Hax.denote'_lit_run] at h; cases h; rfl
  case var y =>
    rw [Hax.denote'_var_run] at h
    cases hy : env y <;> rw [hy] at h <;> cases h
    rfl
  all_goals simp only [atom, Bool.false_eq_true] at ha

/-- An atom that is not the variable `x` runs from an environment extended at `x` as
    from the environment. -/
theorem atomOff_extend {e : ImpExpr} {env y : Env} {x : String} {s u : Value}
    (ha : atomOff x e = true)
    (h : denote' bi fuel e (Hax.Env.extend env x s) = (.val u, y)) :
    denote' bi fuel e env = (.val u, env) ∧ y = Hax.Env.extend env x s := by
  cases e
  case lit l =>
    rw [Hax.denote'_lit_run] at h
    cases h
    exact ⟨Hax.denote'_lit_run _ _ _ _, rfl⟩
  case var z =>
    simp only [atomOff, bne_iff_ne, ne_eq] at ha
    rw [Hax.denote'_var_run] at h
    have hz : Hax.Env.extend env x s z = env z := by
      simp [Hax.Env.extend, ha]
    rw [hz] at h
    rw [Hax.denote'_var_run]
    cases hy : env z <;> rw [hy] at h <;> cases h
    exact ⟨rfl, rfl⟩
  all_goals simp only [atomOff, Bool.false_eq_true] at ha

theorem atomOff_atom {e : ImpExpr} {x : String} (ha : atomOff x e = true) : atom e = true := by
  cases e <;> first | rfl | simp only [atomOff, Bool.false_eq_true] at ha

/-- A call on one atom that runs to a value. -/
theorem app1_val {f : String} {a : ImpExpr} {env e₁ : Env} {v : Value} (ha : atom a = true)
    (h : denote' bi fuel (.app f [a]) env = (.val v, e₁)) :
    e₁ = env ∧ ∃ u, denote' bi fuel a env = (.val u, env) ∧ Plain u ∧ bi f [u] = some v := by
  obtain ⟨vals, hargs, hb⟩ := denote'_app_val h
  obtain ⟨u, x, vs0, h1, hu, h2, rfl⟩ := denoteArgs'_cons_some hargs
  obtain rfl := atom_env ha h1
  rw [denoteArgs'_nil_run] at h2
  cases h2
  exact ⟨rfl, u, h1, hu, hb⟩

/-- A call on two expressions that runs to a value. -/
theorem app2_val {f : String} {a b : ImpExpr} {env e₁ : Env} {v : Value}
    (h : denote' bi fuel (.app f [a, b]) env = (.val v, e₁)) :
    ∃ ua x ub, denote' bi fuel a env = (.val ua, x) ∧ Plain ua ∧
      denote' bi fuel b x = (.val ub, e₁) ∧ Plain ub ∧ bi f [ua, ub] = some v := by
  obtain ⟨vals, hargs, hb⟩ := denote'_app_val h
  obtain ⟨ua, x, vs0, h1, hua, h2, rfl⟩ := denoteArgs'_cons_some hargs
  obtain ⟨ub, y, vs1, h3, hub, h4, rfl⟩ := denoteArgs'_cons_some h2
  rw [denoteArgs'_nil_run] at h4
  cases h4
  exact ⟨ua, x, ub, h1, hua, h3, hub, hb⟩

/-- A call on three atoms that runs to a value. -/
theorem app3_val {f : String} {a b n : ImpExpr} {env e₁ : Env} {v : Value}
    (ha : atom a = true) (hb : atom b = true) (hn : atom n = true)
    (h : denote' bi fuel (.app f [a, b, n]) env = (.val v, e₁)) :
    e₁ = env ∧ ∃ ua ub un, denote' bi fuel a env = (.val ua, env) ∧
      denote' bi fuel b env = (.val ub, env) ∧ denote' bi fuel n env = (.val un, env) ∧
      bi f [ua, ub, un] = some v := by
  obtain ⟨vals, hargs, hbi⟩ := denote'_app_val h
  obtain ⟨ua, x, vs0, h1, _, h2, rfl⟩ := denoteArgs'_cons_some hargs
  obtain rfl := atom_env ha h1
  obtain ⟨ub, y, vs1, h3, _, h4, rfl⟩ := denoteArgs'_cons_some h2
  obtain rfl := atom_env hb h3
  obtain ⟨un, z, vs2, h5, _, h6, rfl⟩ := denoteArgs'_cons_some h4
  obtain rfl := atom_env hn h5
  rw [denoteArgs'_nil_run] at h6
  cases h6
  exact ⟨rfl, ua, ub, un, h1, h3, h5, hbi⟩

/-- A call on expressions that run to values that are not control-flow values, each
    leaving the environment unchanged, runs to the value of the builtin. -/
theorem app2_run {f : String} {a b : ImpExpr} {env : Env} {ua ub v : Value}
    (h1 : denote' bi fuel a env = (.val ua, env)) (hua : Plain ua)
    (h2 : denote' bi fuel b env = (.val ub, env)) (hub : Plain ub)
    (hb : bi f [ua, ub] = some v) :
    denote' bi fuel (.app f [a, b]) env = (.val v, env) := by
  rw [denote'_app_run, denoteArgs'_cons_val h1 hua, denoteArgs'_cons_val h2 hub,
    denoteArgs'_nil_run]
  simp only [Option.map_some, hb]

/-- The call on three such expressions. -/
theorem app3_run {f : String} {a b n : ImpExpr} {env : Env} {ua ub un v : Value}
    (h1 : denote' bi fuel a env = (.val ua, env)) (hua : Plain ua)
    (h2 : denote' bi fuel b env = (.val ub, env)) (hub : Plain ub)
    (h3 : denote' bi fuel n env = (.val un, env)) (hun : Plain un)
    (hb : bi f [ua, ub, un] = some v) :
    denote' bi fuel (.app f [a, b, n]) env = (.val v, env) := by
  rw [denote'_app_run, denoteArgs'_cons_val h1 hua, denoteArgs'_cons_val h2 hub,
    denoteArgs'_cons_val h3 hun, denoteArgs'_nil_run]
  simp only [Option.map_some, hb]

/-- The product `Mul (cast#128 a) (cast#128 b)` on atoms that runs to a value: the atoms
    run to values, and the value is `mulWideVal` on them. -/
theorem mulWide_val {a b : ImpExpr} {env e₁ : Env} {s : Value}
    (ha : atom a = true) (hb : atom b = true)
    (h : denote' bi fuel (.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]]) env =
      (.val s, e₁)) :
    e₁ = env ∧ ∃ ua ub, denote' bi fuel a env = (.val ua, env) ∧ Plain ua ∧
      denote' bi fuel b env = (.val ub, env) ∧ Plain ub ∧ mulWideVal bi ua ub = some s := by
  obtain ⟨p, x, q, h1, _, h2, _, hm⟩ := app2_val h
  obtain ⟨rfl, ua, h1a, hua, hp⟩ := app1_val ha h1
  obtain ⟨rfl, ub, h2b, hub, hq⟩ := app1_val hb h2
  refine ⟨rfl, ua, ub, h1a, hua, h2b, hub, ?_⟩
  simp only [mulWideVal, hp, hq, Option.bind_some, hm]

/-- The high-word chain on atoms that runs to a value. -/
theorem mulHi_val {a b : ImpExpr} {env e₁ : Env} {v : Value}
    (ha : atom a = true) (hb : atom b = true)
    (h : denote' bi fuel (.app "cast#64" [.app "Shr#128"
      [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]], .lit (.int 64)]]) env =
      (.val v, e₁)) :
    e₁ = env ∧ ∃ ua ub, denote' bi fuel a env = (.val ua, env) ∧ Plain ua ∧
      denote' bi fuel b env = (.val ub, env) ∧ Plain ub ∧ mulHiVal bi ua ub = some v := by
  obtain ⟨vals, hargs, hc⟩ := denote'_app_val h
  obtain ⟨r, x, vs0, h1, _, h2, rfl⟩ := denoteArgs'_cons_some hargs
  rw [denoteArgs'_nil_run] at h2
  cases h2
  obtain ⟨s, y, k, h3, _, h4, _, hsh⟩ := app2_val h1
  obtain ⟨rfl, ua, ub, h1a, hua, h2b, hub, hw⟩ := mulWide_val ha hb h3
  rw [Hax.denote'_lit_run] at h4
  cases h4
  refine ⟨rfl, ua, ub, h1a, hua, h2b, hub, ?_⟩
  simp only [mulHiVal, hw, Option.bind_some]
  have hsh' : bi "Shr#128" [s, .int 64] = some r := hsh
  simp only [hsh', Option.bind_some, hc]

/-- The modular-product chain on atoms that runs to a value. -/
theorem mulMod_val {a b n : ImpExpr} {env e₁ : Env} {v : Value}
    (ha : atom a = true) (hb : atom b = true) (hn : atom n = true)
    (h : denote' bi fuel (.app "cast#64" [.app "Rem"
      [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]], .app "cast#128" [n]]]) env =
      (.val v, e₁)) :
    e₁ = env ∧ ∃ ua ub un, denote' bi fuel a env = (.val ua, env) ∧ Plain ua ∧
      denote' bi fuel b env = (.val ub, env) ∧ Plain ub ∧
      denote' bi fuel n env = (.val un, env) ∧ Plain un ∧
      mulModVal bi ua ub un = some v := by
  obtain ⟨vals, hargs, hc⟩ := denote'_app_val h
  obtain ⟨r, x, vs0, h1, _, h2, rfl⟩ := denoteArgs'_cons_some hargs
  rw [denoteArgs'_nil_run] at h2
  cases h2
  obtain ⟨s, y, k, h3, _, h4, _, hrem⟩ := app2_val h1
  obtain ⟨rfl, ua, ub, h1a, hua, h2b, hub, hw⟩ := mulWide_val ha hb h3
  obtain ⟨rfl, un, h3n, hun, hk⟩ := app1_val hn h4
  refine ⟨rfl, ua, ub, un, h1a, hua, h2b, hub, h3n, hun, ?_⟩
  simp only [mulModVal, hw, hk, hrem, Option.bind_some, hc]

/-- The bound form of the modular product on atoms that runs to a value that is not a
    control-flow value: the atoms run to values from the initial environment, the final
    environment is the initial one extended at the local, and the value is `mulModVal`. -/
theorem mulModLet_val {x : String} {a b n : ImpExpr} {env e₁ : Env} {v : Value}
    (ha : atom a = true) (hb : atom b = true) (hn : atomOff x n = true)
    (h : denote' bi fuel (.letBind x (.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]])
      (.app "cast#64" [.app "Rem" [.var x, .app "cast#128" [n]]])) env = (.val v, e₁))
    (hv : Plain v) :
    ∃ s ua ub un, e₁ = Hax.Env.extend env x s ∧
      denote' bi fuel a env = (.val ua, env) ∧ Plain ua ∧
      denote' bi fuel b env = (.val ub, env) ∧ Plain ub ∧
      denote' bi fuel n env = (.val un, env) ∧ Plain un ∧
      mulModVal bi ua ub un = some v := by
  obtain ⟨s, y, h1, _, h2⟩ := denote'_letBind_val h hv
  obtain ⟨rfl, ua, ub, h1a, hua, h2b, hub, hw⟩ := mulWide_val ha hb h1
  obtain ⟨vals, hargs, hc⟩ := denote'_app_val h2
  obtain ⟨r, z, vs0, h3, _, h4, rfl⟩ := denoteArgs'_cons_some hargs
  rw [denoteArgs'_nil_run] at h4
  cases h4
  obtain ⟨s', z', k, h5, _, h6, _, hrem⟩ := app2_val h3
  rw [Hax.denote'_var_run, Hax.Env.extend_same] at h5
  cases h5
  obtain ⟨vals', hargs', hk⟩ := denote'_app_val h6
  obtain ⟨un, z'', vs1, h7, hun, h8, rfl⟩ := denoteArgs'_cons_some hargs'
  rw [denoteArgs'_nil_run] at h8
  cases h8
  obtain ⟨h3n, rfl⟩ := atomOff_extend hn h7
  refine ⟨s, ua, ub, un, rfl, h1a, hua, h2b, hub, h3n, hun, ?_⟩
  simp only [mulModVal, hw, hk, hrem, Option.bind_some, hc]

/-! ## 4. The pass -/

/-- **The pass at one expression, two runs.** Under `WideSpec bi`, a run of `e` and a run
    of `desugarLeaf e` to values end in the same value and the same environment. -/
theorem desugarLeaf_denote (hsp : WideSpec bi) {e : ImpExpr} {env e₁ e₂ : Env} {v w : Value}
    (hs : denote' bi fuel e env = (.val v, e₁))
    (ht : denote' bi fuel (desugarLeaf e) env = (.val w, e₂)) : v = w ∧ e₁ = e₂ := by
  unfold desugarLeaf at ht
  rcases hh : mulHiOf e with _ | ⟨a, b⟩
  · rw [hh] at ht
    dsimp only at ht
    rcases hm : mulModOf e with _ | ⟨a, b, n⟩
    · rw [hm] at ht
      dsimp only at ht
      rw [hs] at ht
      cases ht
      exact ⟨rfl, rfl⟩
    · rw [hm] at ht
      dsimp only at ht
      obtain ⟨rfl, ha, hb, hn⟩ := mulModOf_eq_some hm
      obtain ⟨rfl, ua, ub, un, h1, _, h2, _, h3, _, hval⟩ := mulMod_val ha hb hn hs
      obtain ⟨rfl, ua', ub', un', h1', h2', h3', hbi⟩ := app3_val ha hb hn ht
      rw [h1] at h1'
      rw [h2] at h2'
      rw [h3] at h3'
      cases h1'
      cases h2'
      cases h3'
      exact ⟨hsp.mulmod _ _ _ _ _ hval hbi, rfl⟩
  · rw [hh] at ht
    dsimp only at ht
    obtain ⟨rfl, ha, hb⟩ := mulHiOf_eq_some hh
    obtain ⟨rfl, ua, ub, h1, _, h2, _, hval⟩ := mulHi_val ha hb hs
    obtain ⟨ua', x, ub', h1', _, h2', _, hbi⟩ := app2_val ht
    obtain rfl := atom_env ha h1'
    obtain rfl := atom_env hb h2'
    rw [h1] at h1'
    rw [h2] at h2'
    cases h1'
    cases h2'
    exact ⟨hsp.mulhi _ _ _ _ hval hbi, rfl⟩

/-- **The pass at one expression, the run of the result.** Under `WideTotal bi`, a run of
    `e` to a value is a run of `desugarLeaf e` to that value and that environment. -/
theorem desugarLeaf_run (htot : WideTotal bi) {e : ImpExpr} {env e₁ : Env} {v : Value}
    (hs : denote' bi fuel e env = (.val v, e₁)) :
    denote' bi fuel (desugarLeaf e) env = (.val v, e₁) := by
  unfold desugarLeaf
  rcases hh : mulHiOf e with _ | ⟨a, b⟩
  · dsimp only
    rcases hm : mulModOf e with _ | ⟨a, b, n⟩
    · exact hs
    · dsimp only
      obtain ⟨rfl, ha, hb, hn⟩ := mulModOf_eq_some hm
      obtain ⟨rfl, ua, ub, un, h1, hua, h2, hub, h3, hun, hval⟩ := mulMod_val ha hb hn hs
      exact app3_run h1 hua h2 hub h3 hun (htot.mulmod _ _ _ _ hval)
  · dsimp only
    obtain ⟨rfl, ha, hb⟩ := mulHiOf_eq_some hh
    obtain ⟨rfl, ua, ub, h1, hua, h2, hub, hval⟩ := mulHi_val ha hb hs
    exact app2_run h1 hua h2 hub (htot.mulhi _ _ _ hval)

theorem extend_off {env : Env} {x y : String} {s : Value} (h : some x ≠ some y) :
    Hax.Env.extend env x s y = env y := by
  have hne : y ≠ x := fun hh => h (by rw [hh])
  simp [Hax.Env.extend, hne]

/-- **The pass preserves the value, two runs.** Under `WideSpec bi`, when the source runs
    to a value that is not a control-flow value and the result of the pass runs to such a
    value, the two values are equal, and the two final environments are equal off the
    local `wideLocal e`; they are equal when the flag is `false`. -/
theorem desugarAt_denote (hsp : WideSpec bi) :
    ∀ (t : Bool) (e : ImpExpr) (env e₁ e₂ : Env) (v w : Value),
      denote' bi fuel e env = (.val v, e₁) → Plain v →
      denote' bi fuel (desugarAt t e) env = (.val w, e₂) → Plain w →
      v = w ∧ (t = false → e₁ = e₂) ∧ ∀ y, wideLocal e ≠ some y → e₁ y = e₂ y
  | t, .letBind x a b, env, e₁, e₂, v, w, hs, hv, ht, hw => by
      have step : denote' bi fuel (.letBind x (desugarAt false a) (desugarAt t b)) env =
          (.val w, e₂) →
          v = w ∧ (t = false → e₁ = e₂) ∧ ∀ y, wideLocal b ≠ some y → e₁ y = e₂ y := by
        intro ht'
        obtain ⟨u, z, h1, hu, h2⟩ := denote'_letBind_val hs hv
        obtain ⟨u', z', h1', hu', h2'⟩ := denote'_letBind_val ht' hw
        obtain ⟨rfl, hz, _⟩ := desugarAt_denote hsp false a _ _ _ _ _ h1 hu h1' hu'
        obtain rfl := hz rfl
        exact desugarAt_denote hsp t b _ _ _ _ _ h2 hv h2' hw
      cases t
      · simp only [desugarAt, Bool.false_eq_true, if_false] at ht
        obtain ⟨hvw, he, _⟩ := step ht
        obtain rfl := he rfl
        exact ⟨hvw, fun _ => rfl, fun _ _ => rfl⟩
      · rcases hl : mulModLetOf (.letBind x a b) with _ | ⟨a', b', n⟩
        · simp only [desugarAt, if_true, hl] at ht
          obtain ⟨hvw, _, hy⟩ := step ht
          refine ⟨hvw, Bool.noConfusion, fun y hne => hy y ?_⟩
          simpa only [wideLocal, hl] using hne
        · simp only [desugarAt, if_true, hl] at ht
          obtain ⟨rfl, rfl, ha, hb, hn⟩ := mulModLetOf_eq_some hl
          obtain ⟨s, ua, ub, un, rfl, h1, _, h2, _, h3, _, hval⟩ :=
            mulModLet_val ha hb hn hs hv
          obtain ⟨rfl, ua', ub', un', h1', h2', h3', hbi⟩ :=
            app3_val ha hb (atomOff_atom hn) ht
          rw [h1] at h1'
          rw [h2] at h2'
          rw [h3] at h3'
          cases h1'
          cases h2'
          cases h3'
          refine ⟨hsp.mulmod _ _ _ _ _ hval hbi, Bool.noConfusion, fun y hne => ?_⟩
          simp only [wideLocal, hl] at hne
          exact extend_off hne
  | t, .seq a b, env, e₁, e₂, v, w, hs, hv, ht, hw => by
      simp only [desugarAt] at ht
      obtain ⟨u, z, h1, hu, h2⟩ := denote'_seq_val hs hv
      obtain ⟨u', z', h1', hu', h2'⟩ := denote'_seq_val ht hw
      obtain ⟨_, hz, _⟩ := desugarAt_denote hsp false a _ _ _ _ _ h1 hu h1' hu'
      obtain rfl := hz rfl
      exact desugarAt_denote hsp t b _ _ _ _ _ h2 hv h2' hw
  | _, .lit .., _, _, _, _, _, hs, _, ht, _ | _, .var .., _, _, _, _, _, hs, _, ht, _
  | _, .app .., _, _, _, _, _, hs, _, ht, _ | _, .ifThenElse .., _, _, _, _, _, hs, _, ht, _
  | _, .lam .., _, _, _, _, _, hs, _, ht, _
  | _, .tuple .., _, _, _, _, _, hs, _, ht, _ | _, .proj .., _, _, _, _, _, hs, _, ht, _
  | _, .match_ .., _, _, _, _, _, hs, _, ht, _ | _, .unitVal, _, _, _, _, _, hs, _, ht, _
  | _, .borrow .., _, _, _, _, _, hs, _, ht, _
  | _, .deref .., _, _, _, _, _, hs, _, ht, _ | _, .assign .., _, _, _, _, _, hs, _, ht, _
  | _, .forLoop .., _, _, _, _, _, hs, _, ht, _
  | _, .forLoopRev .., _, _, _, _, _, hs, _, ht, _
  | _, .whileLoop .., _, _, _, _, _, hs, _, ht, _ | _, .break_ .., _, _, _, _, _, hs, _, ht, _
  | _, .continue_, _, _, _, _, _, hs, _, ht, _
  | _, .earlyReturn .., _, _, _, _, _, hs, _, ht, _
  | _, .questionMark .., _, _, _, _, _, hs, _, ht, _
  | _, .forFold .., _, _, _, _, _, hs, _, ht, _
  | _, .forFoldRev .., _, _, _, _, _, hs, _, ht, _
  | _, .whileFold .., _, _, _, _, _, hs, _, ht, _
  | _, .forFoldReturn .., _, _, _, _, _, hs, _, ht, _
  | _, .forFoldRevReturn .., _, _, _, _, _, hs, _, ht, _
  | _, .whileFoldReturn .., _, _, _, _, _, hs, _, ht, _
  | _, .cfBreak .., _, _, _, _, _, hs, _, ht, _ | _, .cfContinue .., _, _, _, _, _, hs, _, ht, _
  | _, .cfBreakContinue .., _, _, _, _, _, hs, _, ht, _
  | _, .typeAscription .., _, _, _, _, _, hs, _, ht, _ => by
      simp only [desugarAt] at ht
      obtain ⟨hvw, rfl⟩ := desugarLeaf_denote hsp hs ht
      exact ⟨hvw, fun _ => rfl, fun _ _ => rfl⟩

/-- **The pass preserves the value.** `desugarAt_denote` at the result position. -/
theorem desugarWide_denote (hsp : WideSpec bi) {e : ImpExpr} {env e₁ e₂ : Env} {v w : Value}
    (hs : denote' bi fuel e env = (.val v, e₁)) (hv : Plain v)
    (ht : denote' bi fuel (desugarWide e) env = (.val w, e₂)) (hw : Plain w) :
    v = w ∧ ∀ y, wideLocal e ≠ some y → e₁ y = e₂ y :=
  let ⟨h, _, hy⟩ := desugarAt_denote hsp true e env e₁ e₂ v w hs hv ht hw
  ⟨h, hy⟩

/-- **The run of the result.** Under `WideTotal bi`, when the source runs to a value that
    is not a control-flow value, the result of the pass runs to that value, and the two
    final environments are equal off the local `wideLocal e`; they are equal when the flag
    is `false`. -/
theorem desugarAt_run (htot : WideTotal bi) :
    ∀ (t : Bool) (e : ImpExpr) (env e₁ : Env) (v : Value),
      denote' bi fuel e env = (.val v, e₁) → Plain v →
      ∃ e₂, denote' bi fuel (desugarAt t e) env = (.val v, e₂) ∧ (t = false → e₁ = e₂) ∧
        ∀ y, wideLocal e ≠ some y → e₁ y = e₂ y
  | t, .letBind x a b, env, e₁, v, hs, hv => by
      have step : ∃ e₂, denote' bi fuel (.letBind x (desugarAt false a) (desugarAt t b)) env =
          (.val v, e₂) ∧ (t = false → e₁ = e₂) ∧ ∀ y, wideLocal b ≠ some y → e₁ y = e₂ y := by
        obtain ⟨u, z, h1, hu, h2⟩ := denote'_letBind_val hs hv
        obtain ⟨z', h1', hz, _⟩ := desugarAt_run htot false a _ _ _ h1 hu
        obtain rfl := hz rfl
        obtain ⟨e₂, h2', hrest⟩ := desugarAt_run htot t b _ _ _ h2 hv
        exact ⟨e₂, by rw [denote'_letBind_of_val h1' hu]; exact h2', hrest⟩
      cases t
      · simp only [desugarAt, Bool.false_eq_true, if_false]
        obtain ⟨e₂, h, he, _⟩ := step
        obtain rfl := he rfl
        exact ⟨e₁, h, fun _ => rfl, fun _ _ => rfl⟩
      · rcases hl : mulModLetOf (.letBind x a b) with _ | ⟨a', b', n⟩
        · simp only [desugarAt, if_true, hl]
          obtain ⟨e₂, h, _, hy⟩ := step
          refine ⟨e₂, h, Bool.noConfusion, fun y hne => hy y ?_⟩
          simpa only [wideLocal, hl] using hne
        · simp only [desugarAt, if_true, hl]
          obtain ⟨rfl, rfl, ha, hb, hn⟩ := mulModLetOf_eq_some hl
          obtain ⟨s, ua, ub, un, rfl, h1, hua, h2, hub, h3, hun, hval⟩ :=
            mulModLet_val ha hb hn hs hv
          refine ⟨env, app3_run h1 hua h2 hub h3 hun (htot.mulmod _ _ _ _ hval),
            Bool.noConfusion, fun y hne => ?_⟩
          simp only [wideLocal, hl] at hne
          exact extend_off hne
  | t, .seq a b, env, e₁, v, hs, hv => by
      simp only [desugarAt]
      obtain ⟨u, z, h1, hu, h2⟩ := denote'_seq_val hs hv
      obtain ⟨z', h1', hz, _⟩ := desugarAt_run htot false a _ _ _ h1 hu
      obtain rfl := hz rfl
      obtain ⟨e₂, h2', hrest⟩ := desugarAt_run htot t b _ _ _ h2 hv
      exact ⟨e₂, by rw [denote'_seq_of_val h1' hu]; exact h2', hrest⟩
  | _, .lit .., _, _, _, hs, _ | _, .var .., _, _, _, hs, _
  | _, .app .., _, _, _, hs, _ | _, .ifThenElse .., _, _, _, hs, _
  | _, .lam .., _, _, _, hs, _
  | _, .tuple .., _, _, _, hs, _ | _, .proj .., _, _, _, hs, _
  | _, .match_ .., _, _, _, hs, _ | _, .unitVal, _, _, _, hs, _
  | _, .borrow .., _, _, _, hs, _
  | _, .deref .., _, _, _, hs, _ | _, .assign .., _, _, _, hs, _
  | _, .forLoop .., _, _, _, hs, _ | _, .forLoopRev .., _, _, _, hs, _
  | _, .whileLoop .., _, _, _, hs, _ | _, .break_ .., _, _, _, hs, _
  | _, .continue_, _, _, _, hs, _ | _, .earlyReturn .., _, _, _, hs, _
  | _, .questionMark .., _, _, _, hs, _ | _, .forFold .., _, _, _, hs, _
  | _, .forFoldRev .., _, _, _, hs, _ | _, .whileFold .., _, _, _, hs, _
  | _, .forFoldReturn .., _, _, _, hs, _
  | _, .forFoldRevReturn .., _, _, _, hs, _
  | _, .whileFoldReturn .., _, _, _, hs, _
  | _, .cfBreak .., _, _, _, hs, _ | _, .cfContinue .., _, _, _, hs, _
  | _, .cfBreakContinue .., _, _, _, hs, _
  | _, .typeAscription .., _, _, _, hs, _ => by
      simp only [desugarAt]
      exact ⟨_, desugarLeaf_run htot hs, fun _ => rfl, fun _ _ => rfl⟩

/-- **The run of the result.** `desugarAt_run` at the result position. -/
theorem desugarWide_run (htot : WideTotal bi) {e : ImpExpr} {env e₁ : Env} {v : Value}
    (hs : denote' bi fuel e env = (.val v, e₁)) (hv : Plain v) :
    ∃ e₂, denote' bi fuel (desugarWide e) env = (.val v, e₂) ∧
      ∀ y, wideLocal e ≠ some y → e₁ y = e₂ y :=
  let ⟨e₂, h, _, hy⟩ := desugarAt_run htot true e env e₁ v hs hv
  ⟨e₂, h, hy⟩

end Runs

/-! ## 5. The result calls no `128`-bit name -/

/-- The call names that occur only at `128` bits: `cast#128` and `Shr#128`. -/
def wideName (f : String) : Bool := f == "cast#128" || f == "Shr#128"

mutual
/-- An expression built of the constructors `lit`, `var`, `unitVal`, `app`, `tuple`,
    `letBind`, `seq`, `assign`, `typeAscription`, `ifThenElse` and `forFold` in which no
    call has a `wideName`. -/
def wideFree : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal => true
  | .app f args => !wideName f && wideFreeL args
  | .tuple es => wideFreeL es
  | .letBind _ v b => wideFree v && wideFree b
  | .seq a b => wideFree a && wideFree b
  | .assign _ r => wideFree r
  | .typeAscription e _ => wideFree e
  | .ifThenElse c a b => wideFree c && wideFree a && wideFree b
  | .forFold _ lo hi body => wideFree lo && wideFree hi && wideFree body
  | _ => false
/-- A list of `wideFree` expressions. -/
def wideFreeL : List ImpExpr → Bool
  | [] => true
  | e :: es => wideFree e && wideFreeL es
end

/-- An expression `desugarLeaf` leaves `wideFree`: an inline chain, or a `wideFree`
    expression. -/
def leafOK (e : ImpExpr) : Bool :=
  (mulHiOf e).isSome || (mulModOf e).isSome || wideFree e

/-- An expression whose pieces visited by `desugarAt t` are the bound form at the result,
    inline chains, or `wideFree` expressions. -/
def wideOK (t : Bool) : ImpExpr → Bool
  | .letBind x v b =>
      (t && (mulModLetOf (.letBind x v b)).isSome) || (wideOK false v && wideOK t b)
  | .seq a b => wideOK false a && wideOK t b
  | e => leafOK e

theorem atom_wideFree {e : ImpExpr} (h : atom e = true) : wideFree e = true := by
  cases e <;> first | rfl | simp only [atom, Bool.false_eq_true] at h

/-- On a `leafOK` expression the result of `desugarLeaf` is `wideFree`. -/
theorem desugarLeaf_wideFree {e : ImpExpr} (h : leafOK e = true) :
    wideFree (desugarLeaf e) = true := by
  unfold desugarLeaf
  rcases hh : mulHiOf e with _ | ⟨a, b⟩
  · dsimp only
    rcases hm : mulModOf e with _ | ⟨a, b, n⟩
    · simpa [leafOK, hh, hm] using h
    · obtain ⟨_, ha, hb, hn⟩ := mulModOf_eq_some hm
      simp [wideFree, wideFreeL, wideName, mulModName, atom_wideFree ha, atom_wideFree hb,
        atom_wideFree hn]
  · obtain ⟨_, ha, hb⟩ := mulHiOf_eq_some hh
    simp [wideFree, wideFreeL, wideName, mulHiName, atom_wideFree ha, atom_wideFree hb]

/-- **The result calls no `128`-bit name.** On a `wideOK` expression the result of
    `desugarAt` is `wideFree`. -/
theorem desugarAt_wideFree (t : Bool) (e : ImpExpr) (h : wideOK t e = true) :
    wideFree (desugarAt t e) = true := by
  fun_induction desugarAt t e
  case case1 t x v b a b' n hl =>
    cases t
    · simp only [Bool.false_eq_true, if_false] at hl
      cases hl
    · simp only [if_true] at hl
      obtain ⟨_, _, ha, hb, hn⟩ := mulModLetOf_eq_some hl
      simp [wideFree, wideFreeL, wideName, mulModName, atom_wideFree ha, atom_wideFree hb,
        atom_wideFree (atomOff_atom hn)]
  case case2 t x v b hl ihv ihb =>
    have hvb : wideOK false v = true ∧ wideOK t b = true := by
      cases t
      · simpa [wideOK] using h
      · simp only [if_true] at hl
        simpa [wideOK, hl] using h
    simp [wideFree, ihv hvb.1, ihb hvb.2]
  case case3 t a b iha ihb =>
    simp only [wideOK, Bool.and_eq_true] at h
    simp [wideFree, iha h.1, ihb h.2]
  case case4 t e hlet hseq =>
    have hk : wideOK t e = leafOK e := by
      cases e
      case letBind x v b => exact (hlet x v b rfl).elim
      case seq a b => exact (hseq a b rfl).elim
      all_goals simp only [wideOK]
    exact desugarLeaf_wideFree (hk ▸ h)

/-- On a `wideOK` expression the result of `desugarWide` is `wideFree`. -/
theorem desugarWide_wideFree {e : ImpExpr} (h : wideOK true e = true) :
    wideFree (desugarWide e) = true :=
  desugarAt_wideFree true e h

end CatCrypt.Crypto.Hax.ImpDesugarWide
