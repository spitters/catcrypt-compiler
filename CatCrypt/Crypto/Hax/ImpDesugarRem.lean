/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpDesugarIte
public import CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

/-!
# Remainder by a constant modulus as a Barrett reduction

`desugarRem κ e` replaces a call `Rem(x, m)` of `e` whose modulus `m` is a constant `p`
with `1 < p < 2^64` by a sequence of `u64` operations without division:

```
r = wrapping_sub#64(x, wrapping_mul#64(mulhi#64(x, ⌊2^64 / p⌋), p))
select(Lt(r, p), r, wrapping_sub#64(r, p))
```

The modulus is constant when it is an integer literal or a variable that the table `κ`
maps to its value. The pass extends `κ` at a `letBind` of a variable to a non-negative
integer literal, and empties it after an expression that is not `pureForm`, which may
assign. The constant `⌊2^64 / p⌋` is computed by the pass.

The pass descends through `letBind` and `seq`, and through the arguments of calls in a
`pureForm` expression. A `Rem` whose modulus is not a constant in range is unchanged.

The sequence is defined on operands below `2^64`, while the builtin `Rem` may accept a
wider operand. The denotation lemmas therefore relate two successful runs, as those of
`ImpDesugarIte` do: when the source runs to a value and the result of the pass runs to a
value, the two values and the two environments are equal.

One conditional subtraction suffices for every operand below `2^64` and every modulus
`0 < p ≤ 2^64` (`BarrettReduceGeneric.barrettCondsub_eq_mod`).

## Main definitions

* `modulusOf` — the constant modulus of an expression along a table of constants.
* `barrettExpr`, `remForm` — the Barrett estimate of the remainder and the sequence with
  its conditional subtraction.
* `barrettRem`, `barrettWord` — the values of `barrettExpr` and of `remForm` on a word.
* `remSite`, `remExpr`, `remArgs` — the rewriting of a `pureForm` expression.
* `bindConst`, `desugarRem` — the table after a `letBind`, and the pass.
* `Known` — the environments that hold the constants of a table.
* `WordSpec` — the hypotheses on the builtins `mulhi#64`, `wrapping_mul#64`,
  `wrapping_sub#64`, `Lt` and `Rem`.
* `divFree`, `divFreeL` — the expressions built of literals, variables and calls of
  names other than `Rem` and `Div`.

## Main results

* `barrettWord_eq_mod` — the value of the sequence on a word is the remainder.
* `remForm_run` — a run of the sequence reads a word and returns `barrettWord`.
* `remExpr_denote`, `desugarRem_denote` — the rewriting and the pass preserve the value;
  the pass preserves the final environment.
* `remForm_divFree` — the sequence on a `divFree` operand is `divFree`.
* `wordSpec_hax64WordOps` — the table `hax64WordOps` satisfies `WordSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpDesugarRem

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote' denoteApp' denoteArgs')
open CatCrypt.Crypto.Hax.ImpDesugarIte
open CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric (barrettCondsub
  barrettCondsub_eq_mod barrett barrettQuot barrettQuot_le mu)

/-! ## 1. The arithmetic -/

/-- The value of `barrettExpr p` on the word `a`: `a - ⌊a·⌊2^64/p⌋ / 2^64⌋·p` in wrapping
    `u64` arithmetic. -/
def barrettRem (p a : Nat) : Nat :=
  (a + 2 ^ 64 - (a * (2 ^ 64 / p) / 2 ^ 64 * p) % 2 ^ 64) % 2 ^ 64

/-- The value of `remForm p` on the word `a`: `barrettRem p a` after one conditional
    subtraction of `p`. -/
def barrettWord (p a : Nat) : Nat :=
  if barrettRem p a < p then barrettRem p a else (barrettRem p a + 2 ^ 64 - p) % 2 ^ 64

/-- **The sequence computes the remainder.** For a modulus `0 < p < 2^64` and a word
    `a < 2^64`, one conditional subtraction after the Barrett estimate gives `a % p`. -/
theorem barrettWord_eq_mod {p a : Nat} (hp0 : 0 < p) (hp : p < 2 ^ 64) (ha : a < 2 ^ 64) :
    barrettWord p a = a % p := by
  have h := barrettCondsub_eq_mod p 64 hp0 (by omega) a ha
  have hle := barrettQuot_le p 64 hp0 (by omega) a
  simp only [barrettCondsub, barrett, barrettQuot, mu] at h hle
  have hqp : a * (2 ^ 64 / p) / 2 ^ 64 * p ≤ a :=
    (Nat.mul_le_mul_right p hle).trans (Nat.div_mul_le_self a p)
  have hmod : a % p < p := Nat.mod_lt _ hp0
  have aux : ∀ t : Nat, t ≤ a → (if p ≤ a - t then a - t - p else a - t) = a % p →
      (if (a + 2 ^ 64 - t % 2 ^ 64) % 2 ^ 64 < p then (a + 2 ^ 64 - t % 2 ^ 64) % 2 ^ 64
        else ((a + 2 ^ 64 - t % 2 ^ 64) % 2 ^ 64 + 2 ^ 64 - p) % 2 ^ 64) = a % p := by
    intro t ht h'
    split at h' <;> split <;> omega
  exact aux _ hqp h

/-! ## 2. The pass -/

/-- The constant modulus of an expression: an integer literal `p`, or a variable the
    table `κ` maps to `p`, with `1 < p < 2^64`. -/
def modulusOf (κ : String → Option Nat) : ImpExpr → Option Nat
  | .lit (.int p) => if 1 < p ∧ p < 2 ^ 64 then some p.toNat else none
  | .var x => (κ x).bind fun p => if 1 < p ∧ p < 2 ^ 64 then some p else none
  | _ => none

/-- The Barrett estimate of `x % p`: `x - mulhi(x, ⌊2^64/p⌋) · p` in wrapping `u64`
    arithmetic. -/
def barrettExpr (p : Nat) (x : ImpExpr) : ImpExpr :=
  .app "wrapping_sub#64" [x, .app "wrapping_mul#64"
    [.app "mulhi#64" [x, .lit (.int ((2 ^ 64 / p : Nat) : Int))], .lit (.int (p : Int))]]

/-- The sequence for `x % p`: the Barrett estimate `r`, then `select(r < p, r, r - p)`. -/
def remForm (p : Nat) (x : ImpExpr) : ImpExpr :=
  .app selectName [.app "Lt" [barrettExpr p x, .lit (.int (p : Int))], barrettExpr p x,
    .app "wrapping_sub#64" [barrettExpr p x, .lit (.int (p : Int))]]

/-- The modulus of a call the pass rewrites: the call is `Rem(x, m)` and `m` is a
    constant modulus. -/
def remSite (κ : String → Option Nat) (f : String) : List ImpExpr → Option Nat
  | [_, m] => if f = "Rem" then modulusOf κ m else none
  | _ => none

mutual
/-- The rewriting of a `pureForm` expression: a call `Rem(x, m)` with a constant modulus
    `p` is `remForm p` on the rewriting of `x`; every other call is the call on the
    rewritings of its arguments; every other expression is unchanged. -/
def remExpr (κ : String → Option Nat) : ImpExpr → ImpExpr
  | .app f args =>
      match remSite κ f args, remArgs κ args with
      | some p, x' :: _ => remForm p x'
      | _, as => .app f as
  | e => e
/-- The rewritings of a list of arguments. -/
def remArgs (κ : String → Option Nat) : List ImpExpr → List ImpExpr
  | [] => []
  | e :: es => remExpr κ e :: remArgs κ es
end

/-- The non-negative integer literal an expression is, if any. -/
def constOf : ImpExpr → Option Nat
  | .lit (.int p) => if 0 ≤ p then some p.toNat else none
  | _ => none

/-- The table of constants after `let x = v`: `x` holds the literal `v` is, and every
    other entry is kept when `v` is `pureForm` and dropped otherwise. -/
def bindConst (κ : String → Option Nat) (x : String) (v : ImpExpr) : String → Option Nat :=
  fun y => if y = x then constOf v else if pureForm v then κ y else none

/-- The table of constants after an expression in sequence: kept when the expression is
    `pureForm` and empty otherwise. -/
def seqConst (κ : String → Option Nat) (a : ImpExpr) : String → Option Nat :=
  fun y => if pureForm a then κ y else none

/-- The pass: the rewriting `remExpr` on the `pureForm` expressions reached through
    `letBind` and `seq`, along the table of constants. Every other expression is
    unchanged. -/
def desugarRem : (String → Option Nat) → ImpExpr → ImpExpr
  | κ, .letBind x v b => .letBind x (desugarRem κ v) (desugarRem (bindConst κ x v) b)
  | κ, .seq a b => .seq (desugarRem κ a) (desugarRem (seqConst κ a) b)
  | κ, e => if pureForm e then remExpr κ e else e

/-! ## 3. The hypotheses -/

/-- The environment holds every constant of the table. -/
def Known (κ : String → Option Nat) (env : Env) : Prop :=
  ∀ x p, κ x = some p → env x = some (.int (p : Int))

/-- The builtins the sequence calls, and `Rem` on a word:
    * `mulhi#64`, `wrapping_mul#64` and `wrapping_sub#64` are defined on two words below
      `2^64` only, with the high half of the product, the product modulo `2^64` and the
      difference modulo `2^64`;
    * `Lt` compares two integers;
    * `Rem`, where defined on a word below `2^64` and a positive modulus below `2^64`,
      is the remainder. -/
structure WordSpec (bi : Builtins) : Prop where
  mulhi : ∀ vals v, bi "mulhi#64" vals = some v → ∃ a b : Nat, a < 2 ^ 64 ∧ b < 2 ^ 64 ∧
    vals = [.int (a : Int), .int (b : Int)] ∧ v = .int ((a * b / 2 ^ 64 : Nat) : Int)
  wmul : ∀ vals v, bi "wrapping_mul#64" vals = some v → ∃ a b : Nat, a < 2 ^ 64 ∧
    b < 2 ^ 64 ∧ vals = [.int (a : Int), .int (b : Int)] ∧
    v = .int ((a * b % 2 ^ 64 : Nat) : Int)
  wsub : ∀ vals v, bi "wrapping_sub#64" vals = some v → ∃ a b : Nat, a < 2 ^ 64 ∧
    b < 2 ^ 64 ∧ vals = [.int (a : Int), .int (b : Int)] ∧
    v = .int (((a + 2 ^ 64 - b) % 2 ^ 64 : Nat) : Int)
  lt : ∀ (a b : Nat) v, bi "Lt" [.int (a : Int), .int (b : Int)] = some v →
    v = .bool (decide (a < b))
  rem : ∀ (a p : Nat) v, a < 2 ^ 64 → 0 < p → p < 2 ^ 64 →
    bi "Rem" [.int (a : Int), .int (p : Int)] = some v → v = .int ((a % p : Nat) : Int)

/-- On two integers, one of them outside `[0, 2^64)`, `u64BinOp` is undefined; where it
    is defined both are words and the value is that of the operation. -/
theorem u64BinOp_some {a b : Int} {g : Nat → Nat → Option Nat} {v : Value}
    (h : Hax.u64BinOp a b g = some v) :
    ∃ x y r : Nat, x < 2 ^ 64 ∧ y < 2 ^ 64 ∧ a = (x : Int) ∧ b = (y : Int) ∧
      g x y = some r ∧ v = .int (r : Int) := by
  unfold Hax.u64BinOp at h
  split at h
  · rename_i hr
    rcases hg : g a.toNat b.toNat with _ | r
    · rw [hg] at h; cases h
    · rw [hg] at h
      cases h
      exact ⟨a.toNat, b.toNat, r, by omega, by omega, by omega, by omega, hg, rfl⟩
  · cases h

/-- The table `hax64WordOps` satisfies `WordSpec`. -/
theorem wordSpec_hax64WordOps : WordSpec Hax.hax64WordOps where
  mulhi := by
    intro vals v h
    rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;>
      first
        | cases (h.symm.trans (rfl : _ = none))
        | (cases x <;> first
            | cases (h.symm.trans (rfl : _ = none))
            | (cases y <;> first | cases (h.symm.trans (rfl : _ = none)) | skip))
    rw [Hax.hax64WordOps_mulhi] at h
    obtain ⟨x, y, r, hx, hy, rfl, rfl, hg, rfl⟩ := u64BinOp_some h
    cases hg
    exact ⟨x, y, hx, hy, rfl, by rw [Nat.shiftRight_eq_div_pow]⟩
  wmul := by
    intro vals v h
    rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;>
      first
        | cases (h.symm.trans (rfl : _ = none))
        | (cases x <;> first
            | cases (h.symm.trans (rfl : _ = none))
            | (cases y <;> first | cases (h.symm.trans (rfl : _ = none)) | skip))
    rw [Hax.hax64WordOps_wrapping_mul] at h
    obtain ⟨x, y, r, hx, hy, rfl, rfl, hg, rfl⟩ := u64BinOp_some h
    cases hg
    exact ⟨x, y, hx, hy, rfl, rfl⟩
  wsub := by
    intro vals v h
    rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;>
      first
        | cases (h.symm.trans (rfl : _ = none))
        | (cases x <;> first
            | cases (h.symm.trans (rfl : _ = none))
            | (cases y <;> first | cases (h.symm.trans (rfl : _ = none)) | skip))
    rw [Hax.hax64WordOps_wrapping_sub] at h
    obtain ⟨x, y, r, hx, hy, rfl, rfl, hg, rfl⟩ := u64BinOp_some h
    cases hg
    exact ⟨x, y, hx, hy, rfl, by rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]⟩
  lt := by
    intro a b v h
    have h0 : Hax.hax64WordOps "Lt" [.int (a : Int), .int (b : Int)] =
        some (.bool (decide ((a : Int) < (b : Int)))) := rfl
    rw [h0] at h
    cases h
    simp
  rem := by
    intro a p v ha hp0 hp h
    rw [Hax.hax64WordOps_rem] at h
    split at h
    · cases h
      simp
    · cases h

/-! ## 4. Runs of calls on `pureForm` arguments -/

/-- A call on two `pureForm` arguments that runs to a value: both arguments run to
    values in the starting environment, which the call leaves unchanged. -/
theorem app2_val {bi : Builtins} {fuel : Nat} {f : String} {a b : ImpExpr} {env e₁ : Env}
    {v : Value} (ha : pureForm a = true) (hb : pureForm b = true)
    (h : denote' bi fuel (.app f [a, b]) env = (.val v, e₁)) :
    ∃ u₁ u₂, denote' bi fuel a env = (.val u₁, env) ∧
      denote' bi fuel b env = (.val u₂, env) ∧ bi f [u₁, u₂] = some v ∧ e₁ = env := by
  obtain ⟨vals, hd, hbi⟩ := denote'_app_val h
  obtain ⟨u₁, x₁, r₁, h1, _, hr1, rfl⟩ := denoteArgs'_cons_some hd
  obtain ⟨u₂, x₂, r₂, h2, _, hr2, rfl⟩ := denoteArgs'_cons_some hr1
  have ex1 : x₁ = env := env_of_pureForm ha h1
  have ex2 : x₂ = x₁ := env_of_pureForm hb h2
  have he : e₁ = x₂ := by rw [denoteArgs'_nil_run] at hr2; cases hr2; rfl
  have hr : r₂ = [] := by rw [denoteArgs'_nil_run] at hr2; cases hr2; rfl
  subst he; subst ex2; subst ex1; subst hr
  exact ⟨u₁, u₂, h1, h2, hbi, rfl⟩

/-- A call on three `pureForm` arguments that runs to a value: the three arguments run
    to values in the starting environment, which the call leaves unchanged. -/
theorem app3_val {bi : Builtins} {fuel : Nat} {f : String} {a b c : ImpExpr}
    {env e₁ : Env} {v : Value} (ha : pureForm a = true) (hb : pureForm b = true)
    (hc : pureForm c = true)
    (h : denote' bi fuel (.app f [a, b, c]) env = (.val v, e₁)) :
    ∃ u₁ u₂ u₃, denote' bi fuel a env = (.val u₁, env) ∧
      denote' bi fuel b env = (.val u₂, env) ∧ denote' bi fuel c env = (.val u₃, env) ∧
      bi f [u₁, u₂, u₃] = some v ∧ e₁ = env := by
  obtain ⟨vals, hd, hbi⟩ := denote'_app_val h
  obtain ⟨u₁, x₁, r₁, h1, _, hr1, rfl⟩ := denoteArgs'_cons_some hd
  obtain ⟨u₂, x₂, r₂, h2, _, hr2, rfl⟩ := denoteArgs'_cons_some hr1
  obtain ⟨u₃, x₃, r₃, h3, _, hr3, rfl⟩ := denoteArgs'_cons_some hr2
  have ex1 : x₁ = env := env_of_pureForm ha h1
  have ex2 : x₂ = x₁ := env_of_pureForm hb h2
  have ex3 : x₃ = x₂ := env_of_pureForm hc h3
  have he : e₁ = x₃ := by rw [denoteArgs'_nil_run] at hr3; cases hr3; rfl
  have hr : r₃ = [] := by rw [denoteArgs'_nil_run] at hr3; cases hr3; rfl
  subst he; subst ex3; subst ex2; subst ex1; subst hr
  exact ⟨u₁, u₂, u₃, h1, h2, h3, hbi, rfl⟩

/-- An integer literal runs to its value. -/
theorem lit_int_run (bi : Builtins) (fuel : Nat) (n : Int) (env : Env) :
    denote' bi fuel (.lit (.int n)) env = (.val (.int n), env) := by
  rw [Hax.denote'_lit_run]; rfl

/-! ## 5. The sequence -/

/-- `barrettExpr` on a `pureForm` operand is `pureForm`. -/
theorem barrettExpr_pureForm {p : Nat} {x : ImpExpr} (hx : pureForm x = true) :
    pureForm (barrettExpr p x) = true := by
  simp [barrettExpr, pureForm, pureForms, hx]

/-- `remForm` on a `pureForm` operand is `pureForm`. -/
theorem remForm_pureForm {p : Nat} {x : ImpExpr} (hx : pureForm x = true) :
    pureForm (remForm p x) = true := by
  simp [remForm, pureForm, pureForms, barrettExpr_pureForm hx]

/-- A run of the Barrett estimate: the operand runs to a word `a` below `2^64`, the
    modulus is below `2^64`, and the value is `barrettRem p a`. -/
theorem barrettExpr_run {bi : Builtins} {fuel : Nat} (hw : WordSpec bi) {p : Nat}
    {x : ImpExpr} {env e₁ : Env} {u : Value} (hx : pureForm x = true)
    (h : denote' bi fuel (barrettExpr p x) env = (.val u, e₁)) :
    ∃ a : Nat, a < 2 ^ 64 ∧ p < 2 ^ 64 ∧
      denote' bi fuel x env = (.val (.int (a : Int)), env) ∧
      u = .int ((barrettRem p a : Nat) : Int) := by
  have hpl : ∀ n : Int, pureForm (.lit (.int n)) = true := fun _ => rfl
  have hmh : pureForm (.app "mulhi#64" [x, .lit (.int ((2 ^ 64 / p : Nat) : Int))]) = true := by
    simp [pureForm, pureForms, hx]
  have hml : pureForm (.app "wrapping_mul#64"
      [.app "mulhi#64" [x, .lit (.int ((2 ^ 64 / p : Nat) : Int))],
        .lit (.int (p : Int))]) = true := by
    simp [pureForm, pureForms, hx]
  obtain ⟨u₁, u₂, h1, h2, hb, _⟩ := app2_val hx hml h
  obtain ⟨t₁, t₂, h3, h4, hb2, _⟩ := app2_val hmh (hpl _) h2
  obtain ⟨s₁, s₂, h5, h6, hb3, _⟩ := app2_val hx (hpl _) h3
  rw [lit_int_run] at h4 h6
  cases h4
  cases h6
  rw [h1] at h5
  cases h5
  obtain ⟨a, b, ha, _, e1, rfl⟩ := hw.wsub _ _ hb
  obtain ⟨c, d, _, hd, e2, e2'⟩ := hw.wmul _ _ hb2
  obtain ⟨g, k, _, _, e3, e3'⟩ := hw.mulhi _ _ hb3
  simp only [List.cons.injEq, and_true] at e1 e2 e3
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, e2p⟩ := e2
  obtain ⟨e3a, e3k⟩ := e3
  have hga : g = a := by exact_mod_cast (Value.int.inj e3a).symm
  have hkm : k = 2 ^ 64 / p := by exact_mod_cast (Value.int.inj e3k).symm
  have hdp : d = p := by exact_mod_cast (Value.int.inj e2p).symm
  subst hga hkm hdp
  have hc : c = g * (2 ^ 64 / d) / 2 ^ 64 := by exact_mod_cast Value.int.inj e3'
  have hb' : b = c * d % 2 ^ 64 := by exact_mod_cast Value.int.inj e2'
  subst hc hb'
  exact ⟨g, ha, hd, h1, rfl⟩

/-- **A run of the sequence.** The operand runs to a word `a` below `2^64`, and the value
    is `barrettWord p a`; the environment is unchanged. -/
theorem remForm_run {bi : Builtins} {fuel : Nat} (hsel : SelectSpec bi) (hw : WordSpec bi)
    {p : Nat} {x : ImpExpr} {env e₁ : Env} {w : Value} (hx : pureForm x = true)
    (h : denote' bi fuel (remForm p x) env = (.val w, e₁)) :
    ∃ a : Nat, a < 2 ^ 64 ∧ p < 2 ^ 64 ∧
      denote' bi fuel x env = (.val (.int (a : Int)), env) ∧
      w = .int ((barrettWord p a : Nat) : Int) ∧ e₁ = env := by
  have hpl : ∀ n : Int, pureForm (.lit (.int n)) = true := fun _ => rfl
  have hR := barrettExpr_pureForm (p := p) hx
  have hlt : pureForm (.app "Lt" [barrettExpr p x, .lit (.int (p : Int))]) = true := by
    simp [pureForm, pureForms, hR]
  have hsb : pureForm (.app "wrapping_sub#64" [barrettExpr p x, .lit (.int (p : Int))]) =
      true := by
    simp [pureForm, pureForms, hR]
  obtain ⟨c, r, s, hc, hr, hs, hb, he⟩ := app3_val hlt hR hsb h
  obtain ⟨a, ha, hp, hxa, rfl⟩ := barrettExpr_run hw hx hr
  obtain ⟨c₁, c₂, hc1, hc2, hbc, _⟩ := app2_val hR (hpl _) hc
  obtain ⟨s₁, s₂, hs1, hs2, hbs, _⟩ := app2_val hR (hpl _) hs
  rw [lit_int_run] at hc2 hs2
  cases hc2
  cases hs2
  rw [hr] at hc1 hs1
  cases hc1
  cases hs1
  have hcv := hw.lt _ _ _ hbc
  subst hcv
  obtain ⟨a', b', _, _, e1, rfl⟩ := hw.wsub _ _ hbs
  simp only [List.cons.injEq, and_true] at e1
  obtain ⟨e1a, e1b⟩ := e1
  have ha' : a' = barrettRem p a := by exact_mod_cast (Value.int.inj e1a).symm
  have hb' : b' = p := by exact_mod_cast (Value.int.inj e1b).symm
  subst ha' hb'
  rw [hsel] at hb
  cases hb
  refine ⟨a, ha, hp, hxa, ?_, he⟩
  unfold barrettWord
  by_cases hlt' : barrettRem b' a < b' <;> simp [hlt']

/-! ## 6. The rewriting of a `pureForm` expression -/

/-- A constant modulus runs to its value in an environment that holds the constants. -/
theorem modulusOf_run {κ : String → Option Nat} {m : ImpExpr} {p : Nat}
    (h : modulusOf κ m = some p) (bi : Builtins) (fuel : Nat) {env : Env}
    (hk : Known κ env) :
    denote' bi fuel m env = (.val (.int (p : Int)), env) ∧ 1 < p ∧ p < 2 ^ 64 ∧
      pureForm m = true := by
  cases m
  case lit l =>
    cases l
    case int n =>
      simp only [modulusOf] at h
      split at h
      · rename_i hn
        cases h
        refine ⟨?_, by omega, by omega, rfl⟩
        rw [lit_int_run, Int.toNat_of_nonneg (by omega)]
      · cases h
    all_goals simp [modulusOf] at h
  case var x =>
    simp only [modulusOf] at h
    rcases hx : κ x with _ | q
    · rw [hx] at h; cases h
    · rw [hx] at h
      simp only [Option.bind] at h
      split at h
      · rename_i hn
        cases h
        refine ⟨?_, hn.1, hn.2, rfl⟩
        rw [Hax.denote'_var_run, hk x _ hx]
      · cases h
  all_goals simp [modulusOf] at h

/-- A rewritten call is `Rem` on two arguments, the second a constant modulus. -/
theorem remSite_some {κ : String → Option Nat} {f : String} {args : List ImpExpr} {p : Nat}
    (h : remSite κ f args = some p) :
    ∃ x m, args = [x, m] ∧ f = "Rem" ∧ modulusOf κ m = some p := by
  unfold remSite at h
  split at h
  · rename_i x m
    split at h
    · rename_i hf
      exact ⟨x, m, rfl, hf, h⟩
    · cases h
  · cases h

/-- `remExpr` at a call. -/
theorem remExpr_app (κ : String → Option Nat) (f : String) (args : List ImpExpr) :
    remExpr κ (.app f args) =
      match remSite κ f args, remArgs κ args with
      | some p, x' :: _ => remForm p x'
      | _, as => .app f as := by
  rw [remExpr]

mutual
/-- The rewriting of a `pureForm` expression is `pureForm`. -/
theorem remExpr_pureForm (κ : String → Option Nat) :
    ∀ e : ImpExpr, pureForm e = true → pureForm (remExpr κ e) = true
  | .app f args, h => by
      have ih := remArgs_pureForms κ args (by simpa [pureForm] using h)
      rw [remExpr_app]
      rcases hs : remSite κ f args with _ | p
      · simpa [pureForm] using ih
      · obtain ⟨x, m, rfl, _, _⟩ := remSite_some hs
        simp only [remArgs, pureForms, Bool.and_eq_true] at ih ⊢
        exact remForm_pureForm ih.1
  | .lit _, h | .var _, h | .ifThenElse .., h => by simpa [remExpr] using h
  | .letBind .., h | .lam .., h | .tuple .., h | .proj .., h
  | .match_ .., h | .unitVal, h | .seq .., h | .borrow .., h | .deref .., h
  | .assign .., h | .forLoop .., h | .forLoopRev .., h | .whileLoop .., h
  | .break_ .., h | .continue_, h | .earlyReturn .., h | .questionMark .., h
  | .forFold .., h | .forFoldRev .., h | .whileFold .., h
  | .forFoldReturn .., h | .forFoldRevReturn .., h | .whileFoldReturn .., h
  | .cfBreak .., h | .cfContinue .., h | .cfBreakContinue .., h
  | .typeAscription .., h => by simp [pureForm] at h
/-- The list counterpart of `remExpr_pureForm`. -/
theorem remArgs_pureForms (κ : String → Option Nat) :
    ∀ es : List ImpExpr, pureForms es = true → pureForms (remArgs κ es) = true
  | [], _ => by simp [remArgs, pureForms]
  | e :: es, h => by
      simp only [pureForms, Bool.and_eq_true] at h
      simp [remArgs, pureForms, remExpr_pureForm κ e h.1, remArgs_pureForms κ es h.2]
end

mutual
/-- **The rewriting preserves the value.** When a `pureForm` expression runs to a value
    in an environment that holds the constants and its rewriting runs to a value, the
    two values are equal. -/
theorem remExpr_denote {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    (hsel : SelectSpec bi) (hw : WordSpec bi) :
    ∀ (e : ImpExpr) (env e₁ e₂ : Env) (v w : Value), pureForm e = true → Known κ env →
      denote' bi fuel e env = (.val v, e₁) →
      denote' bi fuel (remExpr κ e) env = (.val w, e₂) → v = w
  | .app f args, env, e₁, e₂, v, w, hp, hk, hs, ht => by
      have hpa : pureForms args = true := by simpa [pureForm] using hp
      rw [remExpr_app] at ht
      obtain ⟨vals, hd, hb⟩ := denote'_app_val hs
      rcases hsite : remSite κ f args with _ | p
      · rw [hsite] at ht
        obtain ⟨vals', hd', hb'⟩ := denote'_app_val ht
        have := remArgs_denote hsel hw args env e₁ e₂ vals vals' hpa hk hd hd'
        subst this
        rw [hb] at hb'
        cases hb'
        rfl
      · rw [hsite] at ht
        obtain ⟨x, m, rfl, rfl, hm⟩ := remSite_some hsite
        simp only [remArgs] at ht
        simp only [pureForms, Bool.and_eq_true] at hpa
        obtain ⟨hmr, hp1, hp64, _⟩ := modulusOf_run hm bi fuel hk
        obtain ⟨a, ha, _, hxa, rfl, _⟩ :=
          remForm_run hsel hw (remExpr_pureForm κ x hpa.1) ht
        obtain ⟨u₁, x₁, r₁, h1, _, hr1, rfl⟩ := denoteArgs'_cons_some hd
        obtain ⟨u₂, x₂, r₂, h2, _, hr2, rfl⟩ := denoteArgs'_cons_some hr1
        rw [denoteArgs'_nil_run] at hr2
        cases hr2
        have ex1 : x₁ = env := env_of_pureForm hpa.1 h1
        subst ex1
        rw [hmr] at h2
        cases h2
        have hu : u₁ = .int (a : Int) :=
          remExpr_denote hsel hw x _ _ _ _ _ hpa.1 hk h1 hxa
        subst hu
        rw [hw.rem a p v ha (by omega) hp64 hb, barrettWord_eq_mod (by omega) hp64 ha]
  | .lit _, _, _, _, _, _, _, _, hs, ht | .var _, _, _, _, _, _, _, _, hs, ht
  | .ifThenElse .., _, _, _, _, _, _, _, hs, ht => by
      simp only [remExpr] at ht
      rw [hs] at ht
      cases ht
      rfl
  | .letBind .., _, _, _, _, _, h, _, _, _ | .lam .., _, _, _, _, _, h, _, _, _
  | .tuple .., _, _, _, _, _, h, _, _, _ | .proj .., _, _, _, _, _, h, _, _, _
  | .match_ .., _, _, _, _, _, h, _, _, _ | .unitVal, _, _, _, _, _, h, _, _, _
  | .seq .., _, _, _, _, _, h, _, _, _ | .borrow .., _, _, _, _, _, h, _, _, _
  | .deref .., _, _, _, _, _, h, _, _, _ | .assign .., _, _, _, _, _, h, _, _, _
  | .forLoop .., _, _, _, _, _, h, _, _, _ | .forLoopRev .., _, _, _, _, _, h, _, _, _
  | .whileLoop .., _, _, _, _, _, h, _, _, _ | .break_ .., _, _, _, _, _, h, _, _, _
  | .continue_, _, _, _, _, _, h, _, _, _ | .earlyReturn .., _, _, _, _, _, h, _, _, _
  | .questionMark .., _, _, _, _, _, h, _, _, _ | .forFold .., _, _, _, _, _, h, _, _, _
  | .forFoldRev .., _, _, _, _, _, h, _, _, _ | .whileFold .., _, _, _, _, _, h, _, _, _
  | .forFoldReturn .., _, _, _, _, _, h, _, _, _
  | .forFoldRevReturn .., _, _, _, _, _, h, _, _, _
  | .whileFoldReturn .., _, _, _, _, _, h, _, _, _
  | .cfBreak .., _, _, _, _, _, h, _, _, _ | .cfContinue .., _, _, _, _, _, h, _, _, _
  | .cfBreakContinue .., _, _, _, _, _, h, _, _, _
  | .typeAscription .., _, _, _, _, _, h, _, _, _ => by simp [pureForm] at h
/-- The list counterpart of `remExpr_denote`. -/
theorem remArgs_denote {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    (hsel : SelectSpec bi) (hw : WordSpec bi) :
    ∀ (es : List ImpExpr) (env e₁ e₂ : Env) (vs ws : List Value), pureForms es = true →
      Known κ env → denoteArgs' bi fuel es env = (some vs, e₁) →
      denoteArgs' bi fuel (remArgs κ es) env = (some ws, e₂) → vs = ws
  | [], env, e₁, e₂, vs, ws, _, _, hs, ht => by
      simp only [remArgs] at ht
      rw [denoteArgs'_nil_run] at hs ht
      cases hs
      cases ht
      rfl
  | e :: es, env, e₁, e₂, vs, ws, hp, hk, hs, ht => by
      simp only [remArgs] at ht
      simp only [pureForms, Bool.and_eq_true] at hp
      obtain ⟨u, x, vs0, hu1, _, hr, rfl⟩ := denoteArgs'_cons_some hs
      obtain ⟨u', x', ws0, hu1', _, hr', rfl⟩ := denoteArgs'_cons_some ht
      have ex : x = env := env_of_pureForm hp.1 hu1
      have ex' : x' = env := env_of_pureForm (remExpr_pureForm κ e hp.1) hu1'
      subst ex
      subst ex'
      have h1 : u = u' := remExpr_denote hsel hw e _ _ _ _ _ hp.1 hk hu1 hu1'
      have h2 : vs0 = ws0 := remArgs_denote hsel hw es _ _ _ _ _ hp.2 hk hr hr'
      rw [h1, h2]
end

/-! ## 7. The pass -/

/-- The table after `let x = v` is held by the environment the binding leaves. -/
theorem known_bindConst {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    {n : String} {a : ImpExpr} {env x : Env} {u : Value} (hk : Known κ env)
    (h : denote' bi fuel a env = (.val u, x)) :
    Known (bindConst κ n a) (Hax.Env.extend x n u) := by
  intro y p hy
  unfold bindConst at hy
  by_cases hyn : y = n
  · subst hyn
    rw [if_pos rfl] at hy
    cases a
    case lit l =>
      cases l
      case int k =>
        simp only [constOf] at hy
        split at hy
        · rename_i hk0
          cases hy
          rw [lit_int_run] at h
          cases h
          rw [Hax.Env.extend_same, Int.toNat_of_nonneg hk0]
        · cases hy
      all_goals simp [constOf] at hy
    all_goals simp [constOf] at hy
  · rw [if_neg hyn] at hy
    split at hy
    · rename_i hpure
      have ex : x = env := env_of_pureForm hpure h
      subst ex
      rw [Hax.Env.extend_other _ _ _ _ hyn]
      exact hk y p hy
    · cases hy

/-- The table after an expression in sequence is held by the environment it leaves. -/
theorem known_seqConst {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    {a : ImpExpr} {env x : Env} {u : Value} (hk : Known κ env)
    (h : denote' bi fuel a env = (.val u, x)) : Known (seqConst κ a) x := by
  intro y p hy
  unfold seqConst at hy
  split at hy
  · rename_i hpure
    have ex : x = env := env_of_pureForm hpure h
    subst ex
    exact hk y p hy
  · cases hy

/-- The pass at an expression that is neither a `letBind` nor a `seq`: the rewriting of a
    `pureForm` expression preserves the value and the environment, and every other
    expression is unchanged. -/
theorem desugarRem_leaf {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    (hsel : SelectSpec bi) (hw : WordSpec bi) {e : ImpExpr} {env e₁ e₂ : Env}
    {v w : Value} (hk : Known κ env) (hs : denote' bi fuel e env = (.val v, e₁))
    (ht : denote' bi fuel (if pureForm e then remExpr κ e else e) env = (.val w, e₂)) :
    v = w ∧ e₁ = e₂ := by
  by_cases hp : pureForm e = true
  · rw [if_pos hp] at ht
    exact ⟨remExpr_denote hsel hw e _ _ _ _ _ hp hk hs ht,
      (env_of_pureForm hp hs).trans (env_of_pureForm (remExpr_pureForm κ e hp) ht).symm⟩
  · rw [if_neg hp, hs] at ht
    cases ht
    exact ⟨rfl, rfl⟩

/-- **The pass preserves the value and the final environment.** When the source runs to
    a value that is not a control-flow value from an environment that holds the
    constants, and the result of the pass runs to such a value, the two values and the
    two final environments are equal. -/
theorem desugarRem_denote {bi : Builtins} {fuel : Nat} (hsel : SelectSpec bi)
    (hw : WordSpec bi) :
    ∀ (e : ImpExpr) (κ : String → Option Nat) (env e₁ e₂ : Env) (v w : Value),
      Known κ env → denote' bi fuel e env = (.val v, e₁) → Plain v →
      denote' bi fuel (desugarRem κ e) env = (.val w, e₂) → Plain w → v = w ∧ e₁ = e₂
  | .letBind n a b, κ, env, e₁, e₂, v, w, hk, hs, hv, ht, hw' => by
      simp only [desugarRem] at ht
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_letBind_val hs hv
      obtain ⟨u', x', h1', hu', h2'⟩ := denote'_letBind_val ht hw'
      obtain ⟨rfl, rfl⟩ := desugarRem_denote hsel hw a κ _ _ _ _ _ hk h1 hu h1' hu'
      exact desugarRem_denote hsel hw b _ _ _ _ _ _ (known_bindConst hk h1) h2 hv h2' hw'
  | .seq a b, κ, env, e₁, e₂, v, w, hk, hs, hv, ht, hw' => by
      simp only [desugarRem] at ht
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_seq_val hs hv
      obtain ⟨u', x', h1', hu', h2'⟩ := denote'_seq_val ht hw'
      obtain ⟨_, rfl⟩ := desugarRem_denote hsel hw a κ _ _ _ _ _ hk h1 hu h1' hu'
      exact desugarRem_denote hsel hw b _ _ _ _ _ _ (known_seqConst hk h1) h2 hv h2' hw'
  | .lit .., _, _, _, _, _, _, hk, hs, _, ht, _ | .var .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .app .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .ifThenElse .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .lam .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .tuple .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .proj .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .match_ .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .unitVal, _, _, _, _, _, _, hk, hs, _, ht, _
  | .borrow .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .deref .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .assign .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .forLoop .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .forLoopRev .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .whileLoop .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .break_ .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .continue_, _, _, _, _, _, _, hk, hs, _, ht, _
  | .earlyReturn .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .questionMark .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .forFold .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .forFoldRev .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .whileFold .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .forFoldReturn .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .forFoldRevReturn .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .whileFoldReturn .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .cfBreak .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .cfContinue .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .cfBreakContinue .., _, _, _, _, _, _, hk, hs, _, ht, _
  | .typeAscription .., _, _, _, _, _, _, hk, hs, _, ht, _ => by
      simp only [desugarRem] at ht
      exact desugarRem_leaf hsel hw hk hs ht

/-! ## 8. Absence of division and of conditionals -/

mutual
/-- An expression built of literals, variables and calls of names other than `Rem` and
    `Div`. No such expression has a division, a remainder or a conditional. -/
def divFree : ImpExpr → Bool
  | .lit _ | .var _ => true
  | .app f args => f != "Rem" && f != "Div" && divFreeL args
  | _ => false
/-- A list of `divFree` expressions. -/
def divFreeL : List ImpExpr → Bool
  | [] => true
  | e :: es => divFree e && divFreeL es
end

/-- The sequence on a `divFree` operand is `divFree`. -/
theorem remForm_divFree {p : Nat} {x : ImpExpr} (hx : divFree x = true) :
    divFree (remForm p x) = true := by
  simp [remForm, barrettExpr, divFree, divFreeL, hx, selectName]

/-- The rewriting of `Rem(x, m)` at a constant modulus, on a literal or variable
    operand, is `divFree`. -/
theorem remExpr_rem_divFree {κ : String → Option Nat} {x m : ImpExpr} {p : Nat}
    (hm : modulusOf κ m = some p) (hx : divFree (remExpr κ x) = true) :
    divFree (remExpr κ (.app "Rem" [x, m])) = true := by
  rw [remExpr_app]
  simp only [remSite, if_true, hm, remArgs]
  exact remForm_divFree hx

end CatCrypt.Crypto.Hax.ImpDesugarRem
