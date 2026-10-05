/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.RustSemantics.ToRustMS
public import CatCrypt.Hax.RustSemantics.ToRustM
public import CatCrypt.Hax.Ascent.Demo

/-!
# Termination of the state-passing `RustM` reading with conditionals and counted loops

`toRustMS_total_kind` states that the reading `toRustMS app e ρ` returns a value on every
literal to which the kind checker `kindOf sig Γ e` assigns a kind. The kinds `Kd κ` are
the integer literals, the Booleans, the unit value, the loop indices `idx lo hi` (the
`usize` words `ctr i` with `lo ≤ i < hi`) and the kinds `base k` of a user type `κ`, whose
values are given by a predicate `H : κ → AVal → Prop`. The fragment is:

* integer and Boolean literals, the unit value, variables bound in `Γ`;
* `letBind x v b`, where a name already bound in `Γ` is rebound only at its kind, and
  `seq`, `typeAscription`;
* calls `.app f args` of arity one to three, whose name and argument kinds have the result
  kind `k` in the signature list `sig`;
* `ifThenElse c t e` with `c` of kind `bool` and `t`, `e` of one kind;
* `forFold var lo hi body` whose bounds are integer literals or expressions of an index kind
  `idx l h` with `h ≤ 2 ^ 32`; with `[a, _]` the static range of `lo` and `[_, b]` that of
  `hi` (`boundRange`), `0 ≤ a`, `b ≤ 2 ^ 32` and the body in the fragment under `var` at
  the static kind `idx a b`. With literal bounds `lo`, `hi` the index kind is `idx lo hi`.

The hypotheses are an environment binding each name of `Γ` to a value of its kind
(`EnvTy`) and a reading of the calls that returns, on arguments of the kinds of a signature
of `sig`, a value of its result kind (`AppTyped`). A checked word operation enters the
fragment through its signature: `appTyped_add` states `AppTyped` for the checked `Add` of
`appRt` on the bounded words `WB ty B`, under the no-overflow condition `B₁ + B₂ ≤ 2 ^ w`
on each signature. On the word ranges `WI ty L U` (the words `x` of width `ty` with
`L ≤ x < U`) the checked `Add`, `Sub`, `Mul`, `Div` and `Rem` of `appRt` are typed under
the conditions that make each total: `U₁ + U₂ ≤ 2 ^ w` for `Add`, `U₂ ≤ L₁ + 1` (the
subtrahend at most the minuend) for `Sub`, `U₁ * U₂ ≤ 2 ^ w` for `Mul`, and `1 ≤ L₂` (a
non-zero divisor) for `Div` and `Rem`; `AppTyped.append` joins signature lists.

The tagged shifts `Shl#t` and `Shr#t` read the shift amount as a word of the shifted width;
on an amount in `[Lₐ, Uₐ)` with `Uₐ ≤ w` they are total, `Shl#t` under
`U * 2 ^ (Uₐ - 1) ≤ 2 ^ w` with result in `[L * 2 ^ Lₐ, U * 2 ^ (Uₐ - 1))` and `Shr#t` with
result in `[L / 2 ^ (Uₐ - 1), U)`. The untagged `Shl` and `Shr` are not routed by `appRt` and
fail. `AVal` has no signed word, so checked signed arithmetic over `IScalar` has no kind; the
untagged arithmetic on two integer literals is the unbounded integer operation and is total
at the kind `int` (`appTyped_intArith`), without the overflow failure of Rust's signed
operations.

`fnCorres_toRustMS_triple_of_kindOf` combines the termination theorem with
`fnCorres_toRustMS`: a function correspondence, `AppOk`, `AppTyped` and `EnvTy` give the
total `Std.Do` triple of the reading.

`kindOfL sig ki` is the checker with integer literals at a kind `ki`, and `kindOf` is its
instance at `int`. `toRustMS_total_kindL` and `fnCorres_toRustMS_triple_of_kindOfL` hold
under the hypothesis that every integer literal is a value of the kind `ki`; with `ki` a
base kind, a name of that kind can be rebound to an integer literal. The straight-line
termination theorem `toRustMS_total` of `ToRustMSTotal` is the instance at one base kind.

## The instance on `keyEqLit`

`keyEqLit` compares the first 32 entries of two arrays by a `forFold` over `[0, 32)` whose
body is a conditional. `keyEqApp` reads `Ne` and `index` on bytes and byte arrays,
`keyEqLit_kind` is the kind assignment of the literal, and `keyEqLit_triple` is the total
triple of the reading from two Aeneas byte arrays of length at least 32, from the
correspondence `keyEq_fnCorres`.

## The instance with a variable bound

`varLoopLit` is the loop `for i in 0..n { step(i) }` with `n` of the kind `idx 0 (2 ^ 32)`;
`varLoopLit_kind` is its kind assignment and `varLoopLit_total` the termination of its
reading.

## Main definitions

* `Kd`, `Kd.Has`, `EnvTy`, `AppTyped`, `sigFind`, `fits`, `boundRange`, `kindOfL`, `kindOf`,
  `WB`, `WI`

## Main results

* `boundRange_toInt`, `loopS_total`, `toRustMS_total_kindL`, `toRustMS_total_kind`
* `fnCorres_toRustMS_triple_of_kindOfL`, `fnCorres_toRustMS_triple_of_kindOf`
* `appRt_add_total`, `appTyped_add`
* `AppTyped.append`, `appRt_addI_total`, `appRt_sub_total`, `appRt_mul_total`,
  `appRt_div_total`, `appRt_rem_total`
* `appTyped_addI`, `appTyped_sub`, `appTyped_mul`, `appTyped_div`, `appTyped_rem`
* `appTyped_intArith`, `appRt_Shl_undef`, `appRt_Shr_undef`, `appRt_shl_total`,
  `appRt_shr_total`, `appTyped_shl`, `appTyped_shr`
* `keyEqLit_kind`, `keyEqLit_triple`, `varLoopLit_kind`, `varLoopLit_total`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Aeneas.Std.WP Std.Do

/-! ## Kinds -/

/-- The kinds of the fragment: integer literals, Booleans, the unit value, the loop indices
    of a range, and the kinds of a user type `κ`. -/
inductive Kd (κ : Type) where
  /-- An integer literal. -/
  | int
  /-- A Boolean. -/
  | bool
  /-- The unit value. -/
  | unit
  /-- A loop index `ctr i` with `lo ≤ i < hi`. -/
  | idx (lo hi : Int)
  /-- A kind of the user type. -/
  | base (k : κ)
  deriving DecidableEq

/-- The values of a kind, the values of `base k` given by `H k`. -/
def Kd.Has {κ : Type} (H : κ → AVal → Prop) : Kd κ → AVal → Prop
  | .int, v => ∃ n, v = .int n
  | .bool, v => ∃ b, v = .bool b
  | .unit, v => v = .unit
  | .idx lo hi, v => ∃ i : Nat, lo ≤ i ∧ (i : Int) < hi ∧ v = RustSemantics.ctr i
  | .base k, v => H k v

/-- The environment `ρ` binds each name of `Γ` to a value of its kind. -/
def EnvTy {κ : Type} (H : κ → AVal → Prop) (Γ : List (String × Kd κ)) (ρ : AEnv) : Prop :=
  ∀ x k, Γ.lookup x = some k → ∃ v, ρ x = some v ∧ Kd.Has H k v

/-- The reading of the calls `app` returns, at each signature `(f, ks, k)` of `sig` and on
    arguments of the kinds `ks`, a value of the kind `k`. -/
def AppTyped {κ : Type} (H : κ → AVal → Prop) (sig : List (String × List (Kd κ) × Kd κ))
    (app : String → List AVal → RustM AVal) : Prop :=
  ∀ f ks k vs, (f, ks, k) ∈ sig → List.Forall₂ (Kd.Has H) ks vs →
    ∃ r, app f vs = .ok r ∧ Kd.Has H k r

/-- The result kind of the first signature of `sig` for the name `f` and the argument
    kinds `ks`. -/
def sigFind {κ : Type} [DecidableEq κ] (sig : List (String × List (Kd κ) × Kd κ))
    (f : String) (ks : List (Kd κ)) : Option (Kd κ) :=
  (sig.find? fun s => decide (s.1 = f ∧ s.2.1 = ks)).map fun s => s.2.2

/-- Binding `x` at the kind `k` keeps the kinds of `Γ`: `x` is not in `Γ` or has kind `k`. -/
def fits {κ : Type} [DecidableEq κ] (Γ : List (String × Kd κ)) (x : String) (k : Kd κ) :
    Bool :=
  (Γ.lookup x).all fun k0 => decide (k0 = k)

/-- The static range `[L, U]` of the integer `AVal.toInt?` gives on the value of a loop bound
    `e` of kind `k`: `[n, n]` for an integer literal `n`, and `[l, h - 1]` for a bound of an
    index kind `idx l h` with `h ≤ 2 ^ 32`. -/
def boundRange {κ : Type} : Hax.ImpExpr → Kd κ → Option (Int × Int)
  | .lit (.int n), _ => some (n, n)
  | _, .idx l h => if h ≤ 2 ^ 32 then some (l, h - 1) else none
  | _, _ => none

/-- **The kind checker of the fragment with integer literals at the kind `ki`.** The kind
    of the value the reading returns, when the literal is in the fragment. A counted loop
    `forFold var lo hi body` is accepted when each bound is an integer literal or an
    expression of an index kind `idx l h` with `h ≤ 2 ^ 32`; with `[a, _]` the range of `lo`
    and `[_, b]` the range of `hi` (`boundRange`), the check is `0 ≤ a` and `b ≤ 2 ^ 32`, and
    the body is checked with `var` at the static kind `idx a b`, which contains every index
    `[a', b')` of a run with `a ≤ a'` and `b' ≤ b`. -/
def kindOfL {κ : Type} [DecidableEq κ] (sig : List (String × List (Kd κ) × Kd κ))
    (ki : Kd κ) : List (String × Kd κ) → Hax.ImpExpr → Option (Kd κ)
  | _, .lit (.int _) => some ki
  | _, .lit (.bool _) => some .bool
  | Γ, .var x => Γ.lookup x
  | _, .unitVal => some .unit
  | Γ, .letBind x v b =>
    match kindOfL sig ki Γ v with
    | some k => if fits Γ x k then kindOfL sig ki ((x, k) :: Γ) b else none
    | none => none
  | Γ, .seq a b =>
    match kindOfL sig ki Γ a with
    | some _ => kindOfL sig ki Γ b
    | none => none
  | Γ, .typeAscription e _ => kindOfL sig ki Γ e
  | Γ, .app f [a] =>
    match kindOfL sig ki Γ a with
    | some k1 => sigFind sig f [k1]
    | none => none
  | Γ, .app f [a, b] =>
    match kindOfL sig ki Γ a, kindOfL sig ki Γ b with
    | some k1, some k2 => sigFind sig f [k1, k2]
    | _, _ => none
  | Γ, .app f [a, b, c] =>
    match kindOfL sig ki Γ a, kindOfL sig ki Γ b, kindOfL sig ki Γ c with
    | some k1, some k2, some k3 => sigFind sig f [k1, k2, k3]
    | _, _, _ => none
  | Γ, .ifThenElse c t e =>
    match kindOfL sig ki Γ c, kindOfL sig ki Γ t, kindOfL sig ki Γ e with
    | some .bool, some k1, some k2 => if k1 = k2 then some k1 else none
    | _, _, _ => none
  | Γ, .forFold var lo hi body =>
    match kindOfL sig ki Γ lo, kindOfL sig ki Γ hi with
    | some k1, some k2 =>
      match boundRange lo k1, boundRange hi k2 with
      | some (a, _), some (_, b) =>
        if 0 ≤ a ∧ b ≤ 2 ^ 32 ∧ fits Γ var (.idx a b) then
          match kindOfL sig ki ((var, .idx a b) :: Γ) body with
          | some _ => some .unit
          | none => none
        else none
      | _, _ => none
    | _, _ => none
  | _, _ => none

/-- **The kind checker of the fragment**, with integer literals at the kind `int`. -/
def kindOf {κ : Type} [DecidableEq κ] (sig : List (String × List (Kd κ) × Kd κ))
    (Γ : List (String × Kd κ)) (e : Hax.ImpExpr) : Option (Kd κ) :=
  kindOfL sig .int Γ e

/-! ## Lemmas on the hypotheses -/

theorem sigFind_mem {κ : Type} [DecidableEq κ] {sig : List (String × List (Kd κ) × Kd κ)}
    {f : String} {ks : List (Kd κ)} {k : Kd κ} (h : sigFind sig f ks = some k) :
    (f, ks, k) ∈ sig := by
  unfold sigFind at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hs
  simp only [decide_eq_true_eq] at hp
  obtain ⟨h1, h2⟩ := hp
  have hm := List.mem_of_find?_eq_some hs
  obtain ⟨s1, s2, s3⟩ := s
  simp only at h1 h2
  subst h1 h2
  exact hm

theorem EnvTy.upd {κ : Type} {H : κ → AVal → Prop} {Γ : List (String × Kd κ)} {ρ : AEnv}
    (h : EnvTy H Γ ρ) (x : String) {k : Kd κ} {v : AVal} (hv : Kd.Has H k v) :
    EnvTy H ((x, k) :: Γ) (ρ.upd x v) := by
  intro y k' hy
  unfold AEnv.upd
  by_cases hyx : y = x
  · subst hyx
    simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hy
    subst hy
    exact ⟨v, by simp, hv⟩
  · have hb : (y == x) = false := by simpa using hyx
    simp only [List.lookup_cons, hb] at hy
    rw [if_neg (by simpa using hyx)]
    exact h y k' hy

theorem EnvTy.of_cons {κ : Type} [DecidableEq κ] {H : κ → AVal → Prop}
    {Γ : List (String × Kd κ)} {ρ : AEnv} {x : String} {k : Kd κ}
    (h : EnvTy H ((x, k) :: Γ) ρ) (hfit : fits Γ x k = true) : EnvTy H Γ ρ := by
  intro y k' hy
  by_cases hyx : y = x
  · subst hyx
    unfold fits at hfit
    rw [hy] at hfit
    simp only [Option.all_some, decide_eq_true_eq] at hfit
    subst hfit
    exact h y k' (by simp)
  · have hb : (y == x) = false := by simpa using hyx
    exact h y k' (by simp only [List.lookup_cons, hb]; exact hy)

theorem two_pow_32_le_usize : (2 : Int) ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

/-- A value of kind `k` that the reading returns on a loop bound `e` with range `[L, U]`
    (`boundRange`) is an integer in `[L, U]` under `AVal.toInt?`. -/
theorem boundRange_toInt {κ : Type} {H : κ → AVal → Prop}
    {app : String → List AVal → RustM AVal} {e : Hax.ImpExpr} {k : Kd κ} {L U : Int}
    (hb : boundRange e k = some (L, U)) {ρ ρ' : AEnv} {v : AVal}
    (he : toRustMS app e ρ = .ok (v, ρ')) (hv : Kd.Has H k v) :
    ∃ a, v.toInt? = some a ∧ L ≤ a ∧ a ≤ U := by
  unfold boundRange at hb
  split at hb
  · cases hb
    simp only [toRustMS] at he
    cases he
    exact ⟨_, rfl, le_rfl, le_rfl⟩
  · split_ifs at hb with hh
    cases hb
    obtain ⟨i, hl, hi, rfl⟩ := hv
    have hlt : i < 2 ^ UScalarTy.Usize.numBits := by
      have := two_pow_32_le_usize
      have h2 : ((2 ^ UScalarTy.Usize.numBits : Nat) : Int) = 2 ^ UScalarTy.Usize.numBits := by
        push_cast; rfl
      omega
    refine ⟨i, ?_, hl, by omega⟩
    simp only [AVal.toInt?, ctr, UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · cases hb

/-! ## Termination -/

/-- `loopS` returns a value when each step from an index in `[lo, hi)` and a state in `Q`
    returns a state in `Q`. -/
theorem loopS_total {Q : AEnv → Prop} {step : Nat → AEnv → RustM AEnv} {lo hi : Nat}
    (hstep : ∀ i ρ, lo ≤ i → i < hi → Q ρ → ∃ ρ', step i ρ = .ok ρ' ∧ Q ρ') :
    ∀ (n i : Nat) (ρ : AEnv), lo ≤ i → i + n ≤ hi → Q ρ →
      ∃ ρ', loopS step n i ρ = .ok ρ' ∧ Q ρ'
  | 0, _, ρ, _, _, hρ => ⟨ρ, rfl, hρ⟩
  | n + 1, i, ρ, hi, hn, hρ => by
    obtain ⟨ρ1, h1, hρ1⟩ := hstep i ρ hi (by omega) hρ
    obtain ⟨ρ2, h2, hρ2⟩ := loopS_total hstep n (i + 1) ρ1 (by omega) (by omega) hρ1
    exact ⟨ρ2, by simp [loopS, h1, h2], hρ2⟩

/-- **The reading returns a value on the fragment with integer literals at the kind `ki`.**
    When every integer literal has the kind `ki`, from an environment binding each name of
    `Γ` to a value of its kind, the reading of a literal of kind `k` under a reading of the
    calls typed by `sig` returns a value of kind `k`, and its final environment again binds
    each name of `Γ` to a value of its kind. -/
theorem toRustMS_total_kindL {κ : Type} [DecidableEq κ] {H : κ → AVal → Prop}
    {sig : List (String × List (Kd κ) × Kd κ)} {ki : Kd κ} (hlit : ∀ n, Kd.Has H ki (.int n))
    {app : String → List AVal → RustM AVal}
    (happ : AppTyped H sig app) (Γ : List (String × Kd κ)) (e : Hax.ImpExpr) :
    ∀ k, kindOfL sig ki Γ e = some k → ∀ ρ, EnvTy H Γ ρ →
      ∃ v ρ', toRustMS app e ρ = .ok (v, ρ') ∧ Kd.Has H k v ∧ EnvTy H Γ ρ' := by
  fun_induction kindOfL sig ki Γ e
  all_goals intro k hk ρ hρ
  all_goals try (cases hk; done)
  case case1 =>
    cases hk
    exact ⟨.int _, ρ, rfl, hlit _, hρ⟩
  case case2 =>
    cases hk
    exact ⟨.bool _, ρ, rfl, ⟨_, rfl⟩, hρ⟩
  case case3 Γ x =>
    obtain ⟨v, hv, hH⟩ := hρ x k hk
    exact ⟨v, ρ, by simp [toRustMS, hv], hH, hρ⟩
  case case4 =>
    cases hk
    exact ⟨.unit, ρ, rfl, rfl, hρ⟩
  case case5 Γ x v b kv hv hfit ihv ihb =>
    obtain ⟨a, ρ1, h1, ha, hρ1⟩ := ihv _ hv ρ hρ
    obtain ⟨r, ρ2, h2, hr, hρ2⟩ := ihb k hk _ (hρ1.upd x ha)
    exact ⟨r, ρ2, by simp [toRustMS, h1, h2], hr, hρ2.of_cons hfit⟩
  case case8 Γ a b ka hka iha ihb =>
    obtain ⟨u, ρ1, h1, -, hρ1⟩ := iha _ hka ρ hρ
    obtain ⟨r, ρ2, h2, hr, hρ2⟩ := ihb k hk ρ1 hρ1
    exact ⟨r, ρ2, by simp [toRustMS, h1, h2], hr, hρ2⟩
  case case10 Γ e ty ih =>
    obtain ⟨r, ρ1, h1, hr, hρ1⟩ := ih k hk ρ hρ
    exact ⟨r, ρ1, by simp [toRustMS, h1], hr, hρ1⟩
  case case11 Γ f a k1 ha iha =>
    obtain ⟨u, ρ1, h1, hu, hρ1⟩ := iha _ ha ρ hρ
    obtain ⟨r, hr, hk'⟩ := happ f [k1] k [u] (sigFind_mem hk) (.cons hu .nil)
    exact ⟨r, ρ1, by simp [toRustMS, h1, hr], hk', hρ1⟩
  case case13 Γ f a b k1 k2 hb ha iha ihb =>
    obtain ⟨u, ρ1, h1, hu, hρ1⟩ := iha _ ha ρ hρ
    obtain ⟨w, ρ2, h2, hw, hρ2⟩ := ihb _ hb ρ1 hρ1
    obtain ⟨r, hr, hk'⟩ := happ f [k1, k2] k [u, w] (sigFind_mem hk)
      (.cons hu (.cons hw .nil))
    exact ⟨r, ρ2, by simp [toRustMS, h1, h2, hr], hk', hρ2⟩
  case case15 Γ f a b c k1 k2 k3 hc hb ha iha ihb ihc =>
    obtain ⟨u, ρ1, h1, hu, hρ1⟩ := iha _ ha ρ hρ
    obtain ⟨w, ρ2, h2, hw, hρ2⟩ := ihb _ hb ρ1 hρ1
    obtain ⟨z, ρ3, h3, hz, hρ3⟩ := ihc _ hc ρ2 hρ2
    obtain ⟨r, hr, hk'⟩ := happ f [k1, k2, k3] k [u, w, z] (sigFind_mem hk)
      (.cons hu (.cons hw (.cons hz .nil)))
    exact ⟨r, ρ3, by simp [toRustMS, h1, h2, h3, hr], hk', hρ3⟩
  case case17 Γ c t e k2 he hc ht ihc iht ihe =>
    cases hk
    obtain ⟨cv, ρ1, h1, hcv, hρ1⟩ := ihc _ hc ρ hρ
    obtain ⟨b, rfl⟩ := hcv
    cases b
    · obtain ⟨r, ρ2, h2, hr, hρ2⟩ := ihe _ he ρ1 hρ1
      exact ⟨r, ρ2, by simp [toRustMS, h1, h2], hr, hρ2⟩
    · obtain ⟨r, ρ2, h2, hr, hρ2⟩ := iht _ ht ρ1 hρ1
      exact ⟨r, ρ2, by simp [toRustMS, h1, h2], hr, hρ2⟩
  case case20 Γ var lo hi body k1 k2 hk2 hk1 a _ _ b hb2 hb1 hcond kb hbody ihlo ihhi ih =>
    cases hk
    obtain ⟨hlo, hhi, hfit⟩ := hcond
    obtain ⟨p, ρ1, h1, hp, hρ1⟩ := ihlo _ hk1 ρ hρ
    obtain ⟨q, ρ2, h2, hq, hρ2⟩ := ihhi _ hk2 ρ1 hρ1
    obtain ⟨a', ha', hla, -⟩ := boundRange_toInt hb1 h1 hp
    obtain ⟨b', hb', -, hub⟩ := boundRange_toInt hb2 h2 hq
    have hstep : ∀ i ρ0, a'.toNat ≤ i → i < a'.toNat + (b' - a').toNat → EnvTy H Γ ρ0 →
        ∃ ρ', (toRustMS app body (ρ0.upd var (ctr i)) >>= fun s => RustM.ok s.2) = .ok ρ' ∧
          EnvTy H Γ ρ' := by
      intro i ρ0 hi1 hi2 hρ0
      obtain ⟨w, ρ', hw, -, hρ'⟩ := ih _ hbody _
        (hρ0.upd var (k := .idx a b) ⟨i, by omega, by omega, rfl⟩)
      exact ⟨ρ', by simp [hw], hρ'.of_cons hfit⟩
    obtain ⟨ρ3, h3, hρ3⟩ := loopS_total
      (step := fun i ρ0 => toRustMS app body (ρ0.upd var (ctr i)) >>= fun s => RustM.ok s.2)
      hstep (b' - a').toNat a'.toNat ρ2 le_rfl (by omega) hρ2
    refine ⟨.unit, ρ3, ?_, rfl, hρ3⟩
    have hb : b' ≤ 2 ^ System.Platform.numBits :=
      le_trans (le_trans hub hhi) two_pow_32_le_usize
    have ha0 : 0 ≤ a' := le_trans hlo hla
    simp [toRustMS, h1, h2, ha', hb', ha0, hb, h3]

/-- **The reading returns a value on the fragment.** From an environment binding each name
    of `Γ` to a value of its kind, the reading of a literal of kind `k` under a reading of
    the calls typed by `sig` returns a value of kind `k`, and its final environment again
    binds each name of `Γ` to a value of its kind. -/
theorem toRustMS_total_kind {κ : Type} [DecidableEq κ] {H : κ → AVal → Prop}
    {sig : List (String × List (Kd κ) × Kd κ)} {app : String → List AVal → RustM AVal}
    (happ : AppTyped H sig app) (Γ : List (String × Kd κ)) (e : Hax.ImpExpr) :
    ∀ k, kindOf sig Γ e = some k → ∀ ρ, EnvTy H Γ ρ →
      ∃ v ρ', toRustMS app e ρ = .ok (v, ρ') ∧ Kd.Has H k v ∧ EnvTy H Γ ρ' :=
  toRustMS_total_kindL (ki := .int) (fun n => ⟨n, rfl⟩) happ Γ e

/-! ## The total specification from a function correspondence -/

/-- **The total triple of the reading on the fragment with integer literals at the kind
    `ki`.** A function correspondence, `AppOk`, a kind `ki` of every integer literal, a
    reading of the calls typed by `sig`, and an environment binding the names of `Γ` to
    values of their kinds give the total `Std.Do` triple of the reading of a literal of the
    fragment; the postcondition is fixed by `a`. -/
theorem fnCorres_toRustMS_triple_of_kindOfL {bi : Hax.Builtins} {A β : Type}
    [Hax.Ascent.HaxEnc β] {e : Hax.ImpExpr} {entry : A → Hax.Env} {G : A → Prop} {f : A → β}
    {app : String → List AVal → RustM AVal} {κ : Type} [DecidableEq κ]
    {H : κ → AVal → Prop} {sig : List (String × List (Kd κ) × Kd κ)} {ki : Kd κ}
    {Γ : List (String × Kd κ)} {k : Kd κ}
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app)
    (hlit : ∀ n, Kd.Has H ki (.int n))
    (htot : AppTyped H sig app) (he : kindOfL sig ki Γ e = some k) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) (hΓ : EnvTy H Γ ρ) :
    ⦃⌜True⌝⦄ toRustMS app e ρ ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄ := by
  obtain ⟨v, ρ', h, -⟩ := toRustMS_total_kindL hlit htot Γ e k he ρ hΓ
  apply spec_to_mvcgen
  rw [h]
  exact (spec_ok _).2 (fnCorres_toRustMS hF happ a hG ρ hρ v ρ' h)

/-- **The total triple of the reading on the fragment.** A function correspondence, `AppOk`,
    a reading of the calls typed by `sig`, and an environment binding the names of `Γ` to
    values of their kinds give the total `Std.Do` triple of the reading of a literal of the
    fragment; the postcondition is fixed by `a`. -/
theorem fnCorres_toRustMS_triple_of_kindOf {bi : Hax.Builtins} {A β : Type}
    [Hax.Ascent.HaxEnc β] {e : Hax.ImpExpr} {entry : A → Hax.Env} {G : A → Prop} {f : A → β}
    {app : String → List AVal → RustM AVal} {κ : Type} [DecidableEq κ]
    {H : κ → AVal → Prop} {sig : List (String × List (Kd κ) × Kd κ)}
    {Γ : List (String × Kd κ)} {k : Kd κ}
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app)
    (htot : AppTyped H sig app) (he : kindOf sig Γ e = some k) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) (hΓ : EnvTy H Γ ρ) :
    ⦃⌜True⌝⦄ toRustMS app e ρ ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄ :=
  fnCorres_toRustMS_triple_of_kindOfL (ki := .int) hF happ (fun n => ⟨n, rfl⟩) htot he a hG
    ρ hρ hΓ

/-! ## Checked addition under a no-overflow condition -/

/-- The words of width `ty` below `B`. -/
def WB (ty : UScalarTy) (B : Nat) (v : AVal) : Prop :=
  ∃ x : UScalar ty, v = .w ty x ∧ x.val < B

theorem appRt_Add (a b : AVal) : appRt "Add" [a, b] = appArith .add a b := by
  rfl

/-- The checked `Add` of `appRt` returns a word below `B₁ + B₂` on words below `B₁` and
    `B₂` when `B₁ + B₂ ≤ 2 ^ w`. -/
theorem appRt_add_total {ty : UScalarTy} {B1 B2 : Nat} (hB : B1 + B2 ≤ 2 ^ ty.numBits)
    {u w : AVal} (hu : WB ty B1 u) (hw : WB ty B2 w) :
    ∃ r, appRt "Add" [u, w] = .ok r ∧ WB ty (B1 + B2) r := by
  obtain ⟨x, rfl, hx⟩ := hu
  obtain ⟨y, rfl, hy⟩ := hw
  have h := UScalar.add_equiv x y
  rw [appRt_Add]
  rcases hxy : x + y with z | e | _ <;> rw [hxy] at h
  · obtain ⟨-, hz, -⟩ := h
    refine ⟨.w ty z, ?_, z, rfl, by omega⟩
    simp [appArith, AVal.asW, AOp.aen, hxy]
  · simp [UScalar.inBounds] at h
    omega
  · exact h.elim

/-- **Checked addition in the fragment.** `appRt` is typed by every signature list of
    checked additions `Add : WB ty B₁ → WB ty B₂ → WB ty (B₁ + B₂)` whose bounds satisfy the
    no-overflow condition `B₁ + B₂ ≤ 2 ^ w`. -/
theorem appTyped_add {sig : List (String × List (Kd (UScalarTy × Nat)) × Kd (UScalarTy × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty B1 B2, s = ("Add", [.base (ty, B1), .base (ty, B2)],
      .base (ty, B1 + B2)) ∧ B1 + B2 ≤ 2 ^ ty.numBits) :
    AppTyped (fun p => WB p.1 p.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, B1, B2, hseq, hB⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_add_total hB hu hw

/-! ## Checked arithmetic on word ranges -/

/-- The words of width `ty` in the range `[L, U)`. -/
def WI (ty : UScalarTy) (L U : Nat) (v : AVal) : Prop :=
  ∃ x : UScalar ty, v = .w ty x ∧ L ≤ x.val ∧ x.val < U

/-- The signature lists of two typed readings of the calls type the reading on their
    concatenation. -/
theorem AppTyped.append {κ : Type} {H : κ → AVal → Prop}
    {s1 s2 : List (String × List (Kd κ) × Kd κ)} {app : String → List AVal → RustM AVal}
    (h1 : AppTyped H s1 app) (h2 : AppTyped H s2 app) : AppTyped H (s1 ++ s2) app := by
  intro f ks k vs hs hvs
  rcases List.mem_append.mp hs with h | h
  exacts [h1 f ks k vs h hvs, h2 f ks k vs h hvs]

theorem appRt_Sub (a b : AVal) : appRt "Sub" [a, b] = appArith .sub a b := by
  rfl

theorem appRt_Mul (a b : AVal) : appRt "Mul" [a, b] = appArith .mul a b := by
  rfl

theorem appRt_Div (a b : AVal) : appRt "Div" [a, b] = appArith .div a b := by
  rfl

theorem appRt_Rem (a b : AVal) : appRt "Rem" [a, b] = appArith .rem a b := by
  rfl

/-- `appArith` on two words of one width returns the word the Aeneas operation returns. -/
theorem appArith_w_ok {o : AOp} {ty : UScalarTy} {x y z : UScalar ty} (h : o.aen x y = .ok z) :
    appArith o (.w ty x) (.w ty y) = .ok (.w ty z) := by
  simp [appArith, AVal.asW, h]

/-- The checked `Add` of `appRt` on the ranges `[L₁, U₁)` and `[L₂, U₂)` returns a word in
    `[L₁ + L₂, U₁ + U₂)` when `U₁ + U₂ ≤ 2 ^ w`. -/
theorem appRt_addI_total {ty : UScalarTy} {L1 U1 L2 U2 : Nat}
    (hB : U1 + U2 ≤ 2 ^ ty.numBits) {u w : AVal} (hu : WI ty L1 U1 u) (hw : WI ty L2 U2 w) :
    ∃ r, appRt "Add" [u, w] = .ok r ∧ WI ty (L1 + L2) (U1 + U2) r := by
  obtain ⟨x, rfl, hx1, hx2⟩ := hu
  obtain ⟨y, rfl, hy1, hy2⟩ := hw
  have h := UScalar.add_equiv x y
  rcases hxy : x + y with z | e | _ <;> rw [hxy] at h
  · obtain ⟨-, hz, -⟩ := h
    exact ⟨.w ty z, by rw [appRt_Add]; exact appArith_w_ok (o := .add) hxy, z, rfl,
      by omega, by omega⟩
  · simp [UScalar.inBounds] at h
    omega
  · exact h.elim

/-- The checked `Sub` of `appRt` on the ranges `[L₁, U₁)` and `[L₂, U₂)` returns a word in
    `[L₁ + 1 - U₂, U₁ - L₂)` when `U₂ ≤ L₁ + 1`, which orders the operands. -/
theorem appRt_sub_total {ty : UScalarTy} {L1 U1 L2 U2 : Nat} (hB : U2 ≤ L1 + 1)
    {u w : AVal} (hu : WI ty L1 U1 u) (hw : WI ty L2 U2 w) :
    ∃ r, appRt "Sub" [u, w] = .ok r ∧ WI ty (L1 + 1 - U2) (U1 - L2) r := by
  obtain ⟨x, rfl, hx1, hx2⟩ := hu
  obtain ⟨y, rfl, hy1, hy2⟩ := hw
  have h := UScalar.sub_equiv x y
  rcases hxy : x - y with z | e | _ <;> rw [hxy] at h
  · obtain ⟨-, hz, -⟩ := h
    exact ⟨.w ty z, by rw [appRt_Sub]; exact appArith_w_ok (o := .sub) hxy, z, rfl,
      by omega, by omega⟩
  · omega
  · exact h.elim

/-- The checked `Mul` of `appRt` on the ranges `[L₁, U₁)` and `[L₂, U₂)` returns a word in
    `[L₁ * L₂, U₁ * U₂)` when `U₁ * U₂ ≤ 2 ^ w`. -/
theorem appRt_mul_total {ty : UScalarTy} {L1 U1 L2 U2 : Nat}
    (hB : U1 * U2 ≤ 2 ^ ty.numBits) {u w : AVal} (hu : WI ty L1 U1 u) (hw : WI ty L2 U2 w) :
    ∃ r, appRt "Mul" [u, w] = .ok r ∧ WI ty (L1 * L2) (U1 * U2) r := by
  obtain ⟨x, rfl, hx1, hx2⟩ := hu
  obtain ⟨y, rfl, hy1, hy2⟩ := hw
  have hlt : x.val * y.val < U1 * U2 := Nat.mul_lt_mul'' hx2 hy2
  have h := UScalar.mul_equiv x y
  have hm : x * y = x.mul y := rfl
  rcases hxy : x.mul y with z | e | _ <;> rw [hxy] at h
  · obtain ⟨-, hz, -⟩ := h
    refine ⟨.w ty z, by rw [appRt_Mul]; exact appArith_w_ok (o := .mul) (hm.trans hxy), z, rfl,
      ?_, ?_⟩
    · rw [hz]
      exact Nat.mul_le_mul hx1 hy1
    · rw [hz]
      exact hlt
  · have hmax := UScalar.max.eq_1 ty
    omega
  · exact h.elim

/-- The checked `Div` of `appRt` on the ranges `[L₁, U₁)` and `[L₂, U₂)` returns a word in
    `[0, U₁)` when `1 ≤ L₂`, which excludes the divisor zero. -/
theorem appRt_div_total {ty : UScalarTy} {L1 U1 L2 U2 : Nat} (hB : 1 ≤ L2)
    {u w : AVal} (hu : WI ty L1 U1 u) (hw : WI ty L2 U2 w) :
    ∃ r, appRt "Div" [u, w] = .ok r ∧ WI ty 0 U1 r := by
  obtain ⟨x, rfl, hx1, hx2⟩ := hu
  obtain ⟨y, rfl, hy1, hy2⟩ := hw
  obtain ⟨z, hz, hzv⟩ := UScalar.div_spec x (y := y) (by omega)
  refine ⟨.w ty z, by rw [appRt_Div]; exact appArith_w_ok (o := .div) hz, z, rfl,
    Nat.zero_le _, ?_⟩
  rw [hzv]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) hx2

/-- The checked `Rem` of `appRt` on the ranges `[L₁, U₁)` and `[L₂, U₂)` returns a word in
    `[0, U₂)` when `1 ≤ L₂`, which excludes the divisor zero. -/
theorem appRt_rem_total {ty : UScalarTy} {L1 U1 L2 U2 : Nat} (hB : 1 ≤ L2)
    {u w : AVal} (hu : WI ty L1 U1 u) (hw : WI ty L2 U2 w) :
    ∃ r, appRt "Rem" [u, w] = .ok r ∧ WI ty 0 U2 r := by
  obtain ⟨x, rfl, hx1, hx2⟩ := hu
  obtain ⟨y, rfl, hy1, hy2⟩ := hw
  obtain ⟨z, hz, hzv⟩ := spec_imp_exists (UScalar.rem_spec x (y := y) (by omega))
  refine ⟨.w ty z, by rw [appRt_Rem]; exact appArith_w_ok (o := .rem) hz, z, rfl,
    Nat.zero_le _, ?_⟩
  rw [hzv]
  exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)

/-- **Checked addition on word ranges.** `appRt` is typed by every signature list of
    checked additions `Add : WI ty L₁ U₁ → WI ty L₂ U₂ → WI ty (L₁ + L₂) (U₁ + U₂)` with
    `U₁ + U₂ ≤ 2 ^ w`. -/
theorem appTyped_addI
    {sig : List (String × List (Kd (UScalarTy × Nat × Nat)) × Kd (UScalarTy × Nat × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty L1 U1 L2 U2, s = ("Add", [.base (ty, L1, U1), .base (ty, L2, U2)],
      .base (ty, L1 + L2, U1 + U2)) ∧ U1 + U2 ≤ 2 ^ ty.numBits) :
    AppTyped (fun p => WI p.1 p.2.1 p.2.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, L1, U1, L2, U2, hseq, hB⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_addI_total hB hu hw

/-- **Checked subtraction on word ranges.** `appRt` is typed by every signature list of
    checked subtractions `Sub : WI ty L₁ U₁ → WI ty L₂ U₂ → WI ty (L₁ + 1 - U₂) (U₁ - L₂)`
    with `U₂ ≤ L₁ + 1`: every subtrahend is at most every minuend. -/
theorem appTyped_sub
    {sig : List (String × List (Kd (UScalarTy × Nat × Nat)) × Kd (UScalarTy × Nat × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty L1 U1 L2 U2, s = ("Sub", [.base (ty, L1, U1), .base (ty, L2, U2)],
      .base (ty, L1 + 1 - U2, U1 - L2)) ∧ U2 ≤ L1 + 1) :
    AppTyped (fun p => WI p.1 p.2.1 p.2.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, L1, U1, L2, U2, hseq, hB⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_sub_total hB hu hw

/-- **Checked multiplication on word ranges.** `appRt` is typed by every signature list of
    checked multiplications `Mul : WI ty L₁ U₁ → WI ty L₂ U₂ → WI ty (L₁ * L₂) (U₁ * U₂)`
    with `U₁ * U₂ ≤ 2 ^ w`. -/
theorem appTyped_mul
    {sig : List (String × List (Kd (UScalarTy × Nat × Nat)) × Kd (UScalarTy × Nat × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty L1 U1 L2 U2, s = ("Mul", [.base (ty, L1, U1), .base (ty, L2, U2)],
      .base (ty, L1 * L2, U1 * U2)) ∧ U1 * U2 ≤ 2 ^ ty.numBits) :
    AppTyped (fun p => WI p.1 p.2.1 p.2.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, L1, U1, L2, U2, hseq, hB⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_mul_total hB hu hw

/-- **Checked division on word ranges.** `appRt` is typed by every signature list of
    checked divisions `Div : WI ty L₁ U₁ → WI ty L₂ U₂ → WI ty 0 U₁` with `1 ≤ L₂`: the
    divisor is non-zero. -/
theorem appTyped_div
    {sig : List (String × List (Kd (UScalarTy × Nat × Nat)) × Kd (UScalarTy × Nat × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty L1 U1 L2 U2, s = ("Div", [.base (ty, L1, U1), .base (ty, L2, U2)],
      .base (ty, 0, U1)) ∧ 1 ≤ L2) :
    AppTyped (fun p => WI p.1 p.2.1 p.2.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, L1, U1, L2, U2, hseq, hB⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_div_total hB hu hw

/-- **Checked remainder on word ranges.** `appRt` is typed by every signature list of
    checked remainders `Rem : WI ty L₁ U₁ → WI ty L₂ U₂ → WI ty 0 U₂` with `1 ≤ L₂`: the
    divisor is non-zero. -/
theorem appTyped_rem
    {sig : List (String × List (Kd (UScalarTy × Nat × Nat)) × Kd (UScalarTy × Nat × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty L1 U1 L2 U2, s = ("Rem", [.base (ty, L1, U1), .base (ty, L2, U2)],
      .base (ty, 0, U2)) ∧ 1 ≤ L2) :
    AppTyped (fun p => WI p.1 p.2.1 p.2.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, L1, U1, L2, U2, hseq, hB⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_rem_total hB hu hw

/-! ## Arithmetic on integer literals

`AVal` has no signed word: the reading `appRt` routes `Add`, `Sub`, `Mul`, `Div` and `Rem`
to `appArith`, which reads a word operand only at an unsigned width (`AVal.asW`) and computes
on two integer literals the unbounded integer operation `AOp.rt`. Checked signed arithmetic
over `IScalar` therefore has no kind in this fragment; the literal arithmetic below is total
without a width condition, so it does not model the overflow failure of Rust's checked
signed operations. -/

/-- **Literal arithmetic in the fragment.** `appRt` is typed by every signature list of
    untagged arithmetic operations `f : int → int → int` with `f` one of `Add`, `Sub`, `Mul`,
    `Div`, `Rem`; the result is the unbounded integer operation of the runtime. -/
theorem appTyped_intArith {κ : Type} {H : κ → AVal → Prop}
    {sig : List (String × List (Kd κ) × Kd κ)}
    (hsig : ∀ s ∈ sig, ∃ f, s = (f, [.int, .int], .int) ∧
      f ∈ ["Add", "Sub", "Mul", "Div", "Rem"]) :
    AppTyped H sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨g, hseq, hg⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons ⟨n, hn⟩ (.cons ⟨m, hm⟩ .nil) =>
    subst hn hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [appRt_Add]; rfl, _, rfl⟩
    · exact ⟨_, by rw [appRt_Sub]; rfl, _, rfl⟩
    · exact ⟨_, by rw [appRt_Mul]; rfl, _, rfl⟩
    · exact ⟨_, by rw [appRt_Div]; rfl, _, rfl⟩
    · exact ⟨_, by rw [appRt_Rem]; rfl, _, rfl⟩

/-! ## Shifts on word ranges

`appRt` routes a shift only by its width-tagged name `Shl#t` or `Shr#t` (`wordOpAt?`), to
`appWord`, which reads both operands at the width of the tag: the shift amount is a word of
the shifted width (a loop index `idx` only at `usize`). The untagged names `Shl` and `Shr`
are not routed and fail on every argument pair (`appRt_Shl_undef`, `appRt_Shr_undef`), so
they have no total kind. -/

theorem appRt_Shl_undef (a b : AVal) : appRt "Shl" [a, b] = .fail .undef := by
  rfl

theorem appRt_Shr_undef (a b : AVal) : appRt "Shr" [a, b] = .fail .undef := by
  rfl

theorem appRt_Shl_tag (ty : UScalarTy) (a b : AVal) :
    appRt ("Shl#" ++ uTag ty) [a, b] = appWord ty .shl a b := by
  cases ty <;> rfl

theorem appRt_Shr_tag (ty : UScalarTy) (a b : AVal) :
    appRt ("Shr#" ++ uTag ty) [a, b] = appWord ty .shr a b := by
  cases ty <;> rfl

/-- The tagged `Shl#t` of `appRt` on a word in `[L, U)` and an amount in `[Lₐ, Uₐ)` with
    `Uₐ ≤ w` returns a word in `[L * 2 ^ Lₐ, U * 2 ^ (Uₐ - 1))` when
    `U * 2 ^ (Uₐ - 1) ≤ 2 ^ w`, under which the shift does not wrap. -/
theorem appRt_shl_total {ty : UScalarTy} {L U La Ua : Nat} (hA : Ua ≤ ty.numBits)
    (hB : U * 2 ^ (Ua - 1) ≤ 2 ^ ty.numBits) {u w : AVal} (hu : WI ty L U u)
    (hw : WI ty La Ua w) :
    ∃ r, appRt ("Shl#" ++ uTag ty) [u, w] = .ok r ∧
      WI ty (L * 2 ^ La) (U * 2 ^ (Ua - 1)) r := by
  obtain ⟨x, rfl, hx1, hx2⟩ := hu
  obtain ⟨y, rfl, hy1, hy2⟩ := hw
  have hs : y.val < ty.numBits := by omega
  have hp : 2 ^ y.val ≤ 2 ^ (Ua - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : x.val * 2 ^ y.val < U * 2 ^ (Ua - 1) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx2 (Nat.two_pow_pos _))
      (Nat.mul_le_mul_left _ hp)
  let z : UScalar ty := ⟨x.bv.shiftLeft y.val⟩
  have hz : z.val = x.val * 2 ^ y.val := by
    show (x.bv <<< y.val).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le hlt hB)
  refine ⟨.w ty z, ?_, z, rfl, ?_, ?_⟩
  · rw [appRt_Shl_tag]
    have hsh : x <<< y = RustM.ok z := by
      show UScalar.shiftLeft_UScalar x y = _
      unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
      rw [if_pos hs]
    simp [appWord, AVal.asW, WordOp.aen, hsh]
  · rw [hz]
    exact Nat.mul_le_mul hx1 (Nat.pow_le_pow_right (by omega) hy1)
  · rw [hz]
    exact hlt

/-- The tagged `Shr#t` of `appRt` on a word in `[L, U)` and an amount in `[Lₐ, Uₐ)` with
    `Uₐ ≤ w` returns a word in `[L / 2 ^ (Uₐ - 1), U)`. -/
theorem appRt_shr_total {ty : UScalarTy} {L U La Ua : Nat} (hA : Ua ≤ ty.numBits)
    {u w : AVal} (hu : WI ty L U u) (hw : WI ty La Ua w) :
    ∃ r, appRt ("Shr#" ++ uTag ty) [u, w] = .ok r ∧ WI ty (L / 2 ^ (Ua - 1)) U r := by
  obtain ⟨x, rfl, hx1, hx2⟩ := hu
  obtain ⟨y, rfl, hy1, hy2⟩ := hw
  have hs : y.val < ty.numBits := by omega
  let z : UScalar ty := ⟨x.bv.ushiftRight y.val⟩
  have hz : z.val = x.val / 2 ^ y.val := by
    show (x.bv >>> y.val).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  refine ⟨.w ty z, ?_, z, rfl, ?_, ?_⟩
  · rw [appRt_Shr_tag]
    have hsh : x >>> y = RustM.ok z := by
      show UScalar.shiftRight_UScalar x y = _
      unfold UScalar.shiftRight_UScalar UScalar.shiftRight
      rw [if_pos hs]
    simp [appWord, AVal.asW, WordOp.aen, hsh]
  · rw [hz]
    exact Nat.div_le_div hx1 (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.two_pow_pos _).ne'
  · rw [hz]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hx2

/-- **Left shifts on word ranges.** `appRt` is typed by every signature list of tagged
    left shifts `Shl#t : WI ty L U → WI ty Lₐ Uₐ → WI ty (L * 2 ^ Lₐ) (U * 2 ^ (Uₐ - 1))`,
    with `t` the tag of `ty`, `Uₐ ≤ w` and `U * 2 ^ (Uₐ - 1) ≤ 2 ^ w`. -/
theorem appTyped_shl
    {sig : List (String × List (Kd (UScalarTy × Nat × Nat)) × Kd (UScalarTy × Nat × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty L U La Ua, s = ("Shl#" ++ uTag ty,
      [.base (ty, L, U), .base (ty, La, Ua)], .base (ty, L * 2 ^ La, U * 2 ^ (Ua - 1))) ∧
      Ua ≤ ty.numBits ∧ U * 2 ^ (Ua - 1) ≤ 2 ^ ty.numBits) :
    AppTyped (fun p => WI p.1 p.2.1 p.2.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, L, U, La, Ua, hseq, hA, hB⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_shl_total hA hB hu hw

/-- **Right shifts on word ranges.** `appRt` is typed by every signature list of tagged
    right shifts `Shr#t : WI ty L U → WI ty Lₐ Uₐ → WI ty (L / 2 ^ (Uₐ - 1)) U`, with `t`
    the tag of `ty` and `Uₐ ≤ w`. -/
theorem appTyped_shr
    {sig : List (String × List (Kd (UScalarTy × Nat × Nat)) × Kd (UScalarTy × Nat × Nat))}
    (hsig : ∀ s ∈ sig, ∃ ty L U La Ua, s = ("Shr#" ++ uTag ty,
      [.base (ty, L, U), .base (ty, La, Ua)], .base (ty, L / 2 ^ (Ua - 1), U)) ∧
      Ua ≤ ty.numBits) :
    AppTyped (fun p => WI p.1 p.2.1 p.2.2) sig appRt := by
  intro f ks k vs hs hvs
  obtain ⟨ty, L, U, La, Ua, hseq, hA⟩ := hsig _ hs
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨rfl, rfl, rfl⟩ := hseq
  match vs, hvs with
  | [u, w], .cons hu (.cons hw .nil) => exact appRt_shr_total hA hu hw

/-! ## The instance on `keyEqLit` -/

section KeyEq

open Hax.Ascent Hax.Ascent.Demo

/-- The kinds of the instance: byte arrays of length at least 32, and bytes. -/
inductive KeyK where
  /-- A byte array of length at least 32. -/
  | arr
  /-- A byte. -/
  | byte
  deriving DecidableEq

/-- The values of the kinds of the instance. -/
def KeyK.Has : KeyK → AVal → Prop
  | .arr, v => ∃ (n : Usize) (x : Aeneas.Std.Array (UScalar .U8) n), 32 ≤ n.val ∧
      v = .arr .U8 n x
  | .byte, v => ∃ x : UScalar .U8, v = .w .U8 x

/-- The signatures of `keyEqLit`: `index` of a byte array at an index below 32, and `Ne` of
    two bytes. -/
def keyEqSig : List (String × List (Kd KeyK) × Kd KeyK) :=
  [("index", [.base .arr, .idx 0 32], .base .byte), ("Ne", [.base .byte, .base .byte], .bool)]

/-- The kinds of the parameters of `keyEqLit`. -/
def keyEqΓ : List (String × Kd KeyK) := [("a", .base .arr), ("b", .base .arr)]

/-- `Ne` on two words. -/
def appNe : AVal → AVal → RustM AVal
  | .w _ x, .w _ y => .ok (.bool ((x.val : Int) != (y.val : Int)))
  | _, _ => .fail .undef

/-- The reading of the calls of `demoBuiltins`: `Ne` on words and `index` on arrays. -/
def keyEqApp (f : String) (vs : List AVal) : RustM AVal :=
  match f, vs with
  | "Ne", [a, b] => appNe a b
  | "index", [a, i] => appIndex a i
  | _, _ => .fail .undef

/-- `keyEqLit` has the kind `bool` over its two array parameters. -/
theorem keyEqLit_kind : kindOf keyEqSig keyEqΓ keyEqLit = some .bool := by
  decide

theorem keyEqApp_ok : AppOk demoBuiltins keyEqApp := by
  intro f vs r h
  unfold keyEqApp at h
  split at h
  · unfold appNe at h
    split at h
    · cases h
      rfl
    · cases h
  · rename_i a i
    cases a with
    | arr ty n arr =>
      simp only [appIndex] at h
      obtain ⟨j, hj, h⟩ := rustM_bind_ok h
      obtain ⟨x, hx, h⟩ := rustM_bind_ok h
      cases h
      have hi := AVal.asW_ok hj
      unfold Aeneas.Std.Array.index_usize at hx
      rw [Aeneas.Std.Array.getElem?_Usize_eq] at hx
      split at hx
      · cases hx
      · rename_i y hy
        cases hx
        simp [AVal.toValues, AVal.toValue, hi, demoBuiltins, enc_uscalar, hy]
    | _ => simp [appIndex] at h
  · cases h

theorem keyEqApp_typed : AppTyped KeyK.Has keyEqSig keyEqApp := by
  intro f ks k vs hs hvs
  simp only [keyEqSig, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · match vs, hvs with
    | [u, w], .cons hu (.cons hw .nil) =>
      obtain ⟨n, x, hn, rfl⟩ := hu
      obtain ⟨i, -, hi, rfl⟩ := hw
      have hlt : i < x.val.length := by
        have := x.property
        omega
      have hv : (⟨BitVec.ofNat UScalarTy.Usize.numBits i⟩ : UScalar .Usize).val = i := by
        simp only [UScalar.val, BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega
      refine ⟨.w .U8 (x.val[i]'hlt), ?_, _, rfl⟩
      simp [keyEqApp, appIndex, ctr, AVal.asW, Aeneas.Std.Array.index_usize, hv, hlt]
  · match vs, hvs with
    | [u, w], .cons hu (.cons hw .nil) =>
      obtain ⟨x, rfl⟩ := hu
      obtain ⟨y, rfl⟩ := hw
      exact ⟨_, rfl, _, rfl⟩

/-- The integer array of the entries of an Aeneas byte array. -/
def keyArr {n : Usize} (x : Aeneas.Std.Array (UScalar .U8) n) : Array Int :=
  (x.val.map fun w => (w.val : Int)).toArray

/-- The environment binding the parameters of `keyEqLit` to two Aeneas byte arrays. -/
def keyEqEnvA {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n) : AEnv :=
  bindA [("a", .arr .U8 n x), ("b", .arr .U8 n y)]

theorem keyEqEnvA_ty {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n) (hn : 32 ≤ n.val) :
    EnvTy KeyK.Has keyEqΓ (keyEqEnvA x y) := by
  intro z k hz
  simp only [keyEqΓ, List.lookup] at hz
  by_cases ha : z = "a"
  · subst ha
    cases hz
    exact ⟨.arr .U8 n x, by simp [keyEqEnvA, bindA, AEnv.upd], n, x, hn, rfl⟩
  · by_cases hb : z = "b"
    · subst hb
      cases hz
      exact ⟨.arr .U8 n y, by simp [keyEqEnvA, bindA, AEnv.upd], n, y, hn, rfl⟩
    · have h1 : (z == "a") = false := by simpa using ha
      have h2 : (z == "b") = false := by simpa using hb
      simp [h1, h2] at hz

theorem keyEqEntry_keyArr {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n) :
    keyEqEntry (keyArr x, keyArr y) = encEnv (keyEqEnvA x y) := by
  rw [keyEqEnvA, encEnv_bindA]
  simp [keyEqEntry, keyArr, AVal.toValue, HaxEnc.enc]
  rfl

theorem keyEqGuard_keyArr {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n)
    (hn : 32 ≤ n.val) : keyEqGuard (keyArr x, keyArr y) := by
  have hx := x.property
  have hy := y.property
  simp only [keyEqGuard, keyArr, List.size_toArray, List.length_map]
  omega

/-- **The total triple of the reading of `keyEqLit`** on two Aeneas byte arrays of length
    at least 32, from the correspondence `keyEq_fnCorres` and the kind assignment
    `keyEqLit_kind`: the reading returns a value, and the value encodes the comparison
    `keyEq` of the two arrays. -/
theorem keyEqLit_triple {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n)
    (hn : 32 ≤ n.val) :
    ⦃⌜True⌝⦄ toRustMS keyEqApp keyEqLit (keyEqEnvA x y)
    ⦃⇓ r => ⌜r.1.toValue = HaxEnc.enc (keyEq (keyArr x) (keyArr y))⌝⦄ :=
  fnCorres_toRustMS_triple_of_kindOf keyEq_fnCorres keyEqApp_ok keyEqApp_typed keyEqLit_kind
    (keyArr x, keyArr y) (keyEqGuard_keyArr x y hn) (keyEqEnvA x y) (keyEqEntry_keyArr x y)
    (keyEqEnvA_ty x y hn)

end KeyEq

/-! ## An instance with a variable loop bound -/

section VarLoop

/-- The loop `for i in 0..n { step(i) }` with the upper bound a parameter `n`. -/
def varLoopLit : Hax.ImpExpr :=
  .forFold "i" (.lit (.int 0)) (.var "n") (.seq (.app "step" [.var "i"]) .unitVal)

/-- The signature of `varLoopLit`: `step` on an index below `2 ^ 32 - 1`. -/
def varLoopSig : List (String × List (Kd Unit) × Kd Unit) :=
  [("step", [.idx 0 (2 ^ 32 - 1)], .unit)]

/-- The kind of the parameter of `varLoopLit`: an index below `2 ^ 32`. -/
def varLoopΓ : List (String × Kd Unit) := [("n", .idx 0 (2 ^ 32))]

/-- `varLoopLit` has the kind `unit`; its index has the static kind `idx 0 (2 ^ 32 - 1)`. -/
theorem varLoopLit_kind : kindOf varLoopSig varLoopΓ varLoopLit = some .unit := by
  decide

/-- **The reading of `varLoopLit` returns a value** from every environment binding `n` to a
    `usize` index below `2 ^ 32`, under every reading of `step` typed by `varLoopSig`. -/
theorem varLoopLit_total {H : Unit → AVal → Prop} {app : String → List AVal → RustM AVal}
    (happ : AppTyped H varLoopSig app) {ρ : AEnv} {i : Nat} (hi : i < 2 ^ 32)
    (hn : ρ "n" = some (ctr i)) :
    ∃ v ρ', toRustMS app varLoopLit ρ = .ok (v, ρ') := by
  have hρ : EnvTy H varLoopΓ ρ := by
    intro x k hx
    by_cases hxn : x = "n"
    · subst hxn
      cases hx
      exact ⟨ctr i, hn, i, by omega, by omega, rfl⟩
    · have hb : (x == "n") = false := by simpa using hxn
      simp [varLoopΓ, List.lookup_cons, hb] at hx
  obtain ⟨v, ρ', h, -⟩ := toRustMS_total_kind happ varLoopΓ varLoopLit _ varLoopLit_kind ρ hρ
  exact ⟨v, ρ', h⟩

end VarLoop

end CatCrypt.Hax.RustSemantics
