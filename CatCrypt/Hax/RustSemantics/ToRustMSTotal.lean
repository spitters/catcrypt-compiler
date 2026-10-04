/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.RustSemantics.ToRustMS
public import CatCrypt.Hax.RustSemantics.ToRustM
public import CatCrypt.Hax.RustSemantics.ToRustMSSpecDemo

/-!
# Termination of the state-passing `RustM` reading on straight-line literals

`toRustMS_total` states that the reading `toRustMS app e ρ` returns a value on the
straight-line fragment `straightOk names bound e`: integer literals, variables in `bound` or
bound by an enclosing `let`, `let`, sequencing, type ascriptions and calls of arity one to
three to the names of `names`. The hypotheses are a class of values `P` containing the
integer literals, a reading of the calls total on `P` at the names and arities of `names`
(`AppTotalOn`), and an environment binding every name of `bound` to a value in `P`
(`EnvOk`). The returned value is in `P` and the final environment again satisfies
`EnvOk P bound`.

`fnCorres_toRustMS_triple_of_straightOk` combines the termination theorem with
`fnCorres_toRustMS`: a function correspondence, `AppOk`, and the three hypotheses above
give the total `Std.Do` triple of the reading, with no hypothesis that the reading returns
a value. The triple has the statement of `fnCorres_toRustMS_triple` of
`CatCrypt/Hax/RustSemantics/ToRustMSSpec.lean`, of which it is the instance at
`toRustMS_total`; it belongs beside that theorem.

## The instance on `lineLit`

`IsInt` is the class of integer literals; the reading of the calls `SpecDemo.addApp` of
`ToRustMSSpecDemo` reads `Add` by `appArith` and is total on `IsInt` (`addApp_total`).
`lineLit_straightOk` is decided by the kernel, and `lineLitI_triple` is the total triple of
the reading of `lineLit` from an environment binding the parameter to an integer literal.

## Relation to the kinded fragment

The kind checker `kindOf` of `ToRustMSTotalCtl` does not contain this fragment. It gives
integer literals the kind `int`, and it rebinds a name already bound only at the kind of
that binding (`fits`), since the reading of `letBind` keeps the new binding in the final
environment. `.letBind "a" (.lit (.int 0)) (.var "a")` passes `straightOk [] ["a"]`, while
`kindOf` returns `none` on it under every kind of `"a"` other than `int`. `toRustMS_total`
is therefore proved by its own induction.

## Main definitions

* `AppTotalOn`, `EnvOk`, `straightOk`

## Main results

* `toRustMS_total`, `toRustMS_isOk_of_straightOk`
* `fnCorres_toRustMS_spec_of_straightOk`, `fnCorres_toRustMS_triple_of_straightOk`
* `addApp_total`, `lineLitI_ok`, `lineLitI_triple`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Aeneas.Std.WP Std.Do

/-! ## The fragment and its hypotheses -/

/-- The reading of the calls `app` returns, at each name and arity of `names`, a value in
    `P` on every list of arguments in `P`. -/
def AppTotalOn (P : AVal → Prop) (names : List (String × Nat))
    (app : String → List AVal → RustM AVal) : Prop :=
  ∀ f vs, (f, vs.length) ∈ names → (∀ v ∈ vs, P v) → ∃ r, app f vs = .ok r ∧ P r

/-- The environment `ρ` binds every name of `bound` to a value in `P`. -/
def EnvOk (P : AVal → Prop) (bound : List String) (ρ : AEnv) : Prop :=
  ∀ x ∈ bound, ∃ v, ρ x = some v ∧ P v

/-- The straight-line fragment: integer literals, variables in `bound` or bound by an
    enclosing `let`, `let`, sequencing, type ascriptions, and calls of arity one to three
    whose name and arity are in `names`. -/
def straightOk (names : List (String × Nat)) : List String → Hax.ImpExpr → Bool
  | _, .lit (.int _) => true
  | bound, .var x => bound.contains x
  | bound, .letBind x v b => straightOk names bound v && straightOk names (x :: bound) b
  | bound, .seq a b => straightOk names bound a && straightOk names bound b
  | bound, .typeAscription e _ => straightOk names bound e
  | bound, .app f [a] => names.contains (f, 1) && straightOk names bound a
  | bound, .app f [a, b] =>
    names.contains (f, 2) && straightOk names bound a && straightOk names bound b
  | bound, .app f [a, b, c] =>
    names.contains (f, 3) && straightOk names bound a && straightOk names bound b &&
      straightOk names bound c
  | _, _ => false

theorem EnvOk.upd {P : AVal → Prop} {bound : List String} {ρ : AEnv} (h : EnvOk P bound ρ)
    (x : String) {v : AVal} (hv : P v) : EnvOk P (x :: bound) (ρ.upd x v) := by
  intro y hy
  unfold AEnv.upd
  by_cases hyx : y = x
  · subst hyx
    exact ⟨v, by simp, hv⟩
  · rw [if_neg (by simpa using hyx)]
    exact h y (by simpa [hyx] using hy)

theorem EnvOk.of_cons {P : AVal → Prop} {bound : List String} {ρ : AEnv} {x : String}
    (h : EnvOk P (x :: bound) ρ) : EnvOk P bound ρ :=
  fun y hy => h y (List.mem_cons_of_mem x hy)

/-! ## Termination -/

/-- **The reading returns a value on the straight-line fragment.** From an environment
    binding every name of `bound` to a value in `P`, the reading of a literal passing
    `straightOk names bound` under a reading of the calls total on `P` returns a value in
    `P`, and its final environment binds every name of `bound` to a value in `P`. -/
theorem toRustMS_total {P : AVal → Prop} (hint : ∀ n, P (.int n))
    {names : List (String × Nat)} {app : String → List AVal → RustM AVal}
    (happ : AppTotalOn P names app) (bound : List String) (e : Hax.ImpExpr) :
    straightOk names bound e = true → ∀ ρ, EnvOk P bound ρ →
      ∃ v ρ', toRustMS app e ρ = .ok (v, ρ') ∧ P v ∧ EnvOk P bound ρ' := by
  fun_induction straightOk names bound e with
  | case1 bound n =>
    intro _ ρ hρ
    exact ⟨_, ρ, rfl, hint n, hρ⟩
  | case2 bound x =>
    intro h ρ hρ
    obtain ⟨v, hv, hP⟩ := hρ x (by simpa using h)
    exact ⟨v, ρ, by simp [toRustMS, hv], hP, hρ⟩
  | case3 bound x v b ihv ihb =>
    intro h ρ hρ
    simp only [Bool.and_eq_true] at h
    obtain ⟨a, ρ1, h1, ha, hρ1⟩ := ihv h.1 ρ hρ
    obtain ⟨r, ρ2, h2, hr, hρ2⟩ := ihb h.2 _ (hρ1.upd x ha)
    exact ⟨r, ρ2, by simp [toRustMS, h1, h2], hr, hρ2.of_cons⟩
  | case4 bound a b iha ihb =>
    intro h ρ hρ
    simp only [Bool.and_eq_true] at h
    obtain ⟨u, ρ1, h1, _, hρ1⟩ := iha h.1 ρ hρ
    obtain ⟨r, ρ2, h2, hr, hρ2⟩ := ihb h.2 ρ1 hρ1
    exact ⟨r, ρ2, by simp [toRustMS, h1, h2], hr, hρ2⟩
  | case5 bound e ty ih =>
    intro h ρ hρ
    obtain ⟨r, ρ1, h1, hr, hρ1⟩ := ih h ρ hρ
    exact ⟨r, ρ1, by simp [toRustMS, h1], hr, hρ1⟩
  | case6 bound f a iha =>
    intro h ρ hρ
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨u, ρ1, h1, hu, hρ1⟩ := iha h.2 ρ hρ
    obtain ⟨r, hr, hP⟩ := happ f [u] h.1 (by simpa using hu)
    exact ⟨r, ρ1, by simp [toRustMS, h1, hr], hP, hρ1⟩
  | case7 bound f a b iha ihb =>
    intro h ρ hρ
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨u, ρ1, h1, hu, hρ1⟩ := iha h.1.2 ρ hρ
    obtain ⟨w, ρ2, h2, hw, hρ2⟩ := ihb h.2 ρ1 hρ1
    obtain ⟨r, hr, hP⟩ := happ f [u, w] h.1.1 (by simp [hu, hw])
    exact ⟨r, ρ2, by simp [toRustMS, h1, h2, hr], hP, hρ2⟩
  | case8 bound f a b c iha ihb ihc =>
    intro h ρ hρ
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨u, ρ1, h1, hu, hρ1⟩ := iha h.1.1.2 ρ hρ
    obtain ⟨w, ρ2, h2, hw, hρ2⟩ := ihb h.1.2 ρ1 hρ1
    obtain ⟨z, ρ3, h3, hz, hρ3⟩ := ihc h.2 ρ2 hρ2
    obtain ⟨r, hr, hP⟩ := happ f [u, w, z] h.1.1.1 (by simp [hu, hw, hz])
    exact ⟨r, ρ3, by simp [toRustMS, h1, h2, h3, hr], hP, hρ3⟩
  | case9 =>
    intro h
    simp at h

/-- The reading returns a value on the straight-line fragment, in the form of the
    hypothesis of the total specifications of `ToRustMSSpec`. -/
theorem toRustMS_isOk_of_straightOk {P : AVal → Prop} (hint : ∀ n, P (.int n))
    {names : List (String × Nat)} {app : String → List AVal → RustM AVal}
    (happ : AppTotalOn P names app) {bound : List String} {e : Hax.ImpExpr}
    (he : straightOk names bound e = true) {ρ : AEnv} (hρ : EnvOk P bound ρ) :
    ∃ r, toRustMS app e ρ = .ok r := by
  obtain ⟨v, ρ', h, -⟩ := toRustMS_total hint happ bound e he ρ hρ
  exact ⟨(v, ρ'), h⟩

/-! ## The total specification from a function correspondence -/

section Spec

variable {bi : Hax.Builtins} {A β : Type} [Hax.Ascent.HaxEnc β]
  {e : Hax.ImpExpr} {entry : A → Hax.Env} {G : A → Prop} {f : A → β}
  {app : String → List AVal → RustM AVal} {P : AVal → Prop} {names : List (String × Nat)}
  {bound : List String}

/-- **The total specification of the reading on the straight-line fragment**: the reading
    returns a value, and the value encodes `f a`. -/
theorem fnCorres_toRustMS_spec_of_straightOk
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app)
    (hint : ∀ n, P (.int n)) (htot : AppTotalOn P names app)
    (he : straightOk names bound e = true) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) (hρP : EnvOk P bound ρ) :
    spec (toRustMS app e ρ) (fun r => r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)) := by
  obtain ⟨r, hr⟩ := toRustMS_isOk_of_straightOk hint htot he hρP
  rw [hr]
  exact (spec_ok r).2 (fnCorres_toRustMS hF happ a hG ρ hρ r.1 r.2 hr)

/-- **The total triple of the reading on the straight-line fragment.** A function
    correspondence, `AppOk`, a reading of the calls total on `P`, and an environment binding
    the free names of the literal to values in `P` give the total `Std.Do` triple; the
    postcondition is fixed by `a`. -/
theorem fnCorres_toRustMS_triple_of_straightOk
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app)
    (hint : ∀ n, P (.int n)) (htot : AppTotalOn P names app)
    (he : straightOk names bound e = true) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) (hρP : EnvOk P bound ρ) :
    ⦃⌜True⌝⦄ toRustMS app e ρ ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄ :=
  spec_to_mvcgen
    (fnCorres_toRustMS_spec_of_straightOk hF happ hint htot he a hG ρ hρ hρP)

end Spec

/-! ## The instance on `lineLit` -/

section Line

open Hax.Ascent Hax.Ascent.Demo

/-- The class of integer literals. -/
def IsInt (v : AVal) : Prop := ∃ n, v = .int n

/-- `SpecDemo.addApp` is total on integer literals at `Add` of arity two. -/
theorem addApp_total : AppTotalOn IsInt [("Add", 2)] SpecDemo.addApp := by
  intro f vs hf hvs
  simp only [List.mem_singleton, Prod.mk.injEq] at hf
  obtain ⟨rfl, hlen⟩ := hf
  match vs, hlen, hvs with
  | [u, w], _, hvs =>
    obtain ⟨n, rfl⟩ := hvs u (by simp)
    obtain ⟨m, rfl⟩ := hvs w (by simp)
    exact ⟨.int (AOp.rt .add n m), rfl, _, rfl⟩

/-- `lineLit` is in the straight-line fragment over the parameter `a`. -/
theorem lineLit_straightOk : straightOk [("Add", 2)] ["a"] lineLit = true := by
  decide

/-- The environment binding the parameter of `lineLit` to an integer literal. -/
def lineLitEnvI (n : Int) : AEnv := bindA [("a", .int n)]

theorem lineLitEnvI_ok (n : Int) : EnvOk IsInt ["a"] (lineLitEnvI n) := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨.int n, by simp [lineLitEnvI, bindA, AEnv.upd], n, rfl⟩

/-- The reading of `lineLit` on an integer argument returns a value, by `toRustMS_total`. -/
theorem lineLitI_ok (n : Int) :
    ∃ r, toRustMS SpecDemo.addApp lineLit (lineLitEnvI n) = .ok r :=
  toRustMS_isOk_of_straightOk (fun k => ⟨k, rfl⟩) addApp_total lineLit_straightOk
    (lineLitEnvI_ok n)

/-- **The total triple of the reading of `lineLit` on an integer argument**, from the
    function correspondence `line_corres_gen` and the straight-line fragment: the returned
    value encodes `n + 210`. -/
theorem lineLitI_triple (n : Int) :
    ⦃⌜True⌝⦄ toRustMS SpecDemo.addApp lineLit (lineLitEnvI n)
    ⦃⇓ r => ⌜r.1.toValue = .int (n + 210)⌝⦄ :=
  fnCorres_toRustMS_triple_of_straightOk SpecDemo.line_fnCorres SpecDemo.addApp_ok
    (fun k => ⟨k, rfl⟩) addApp_total lineLit_straightOk n trivial (lineLitEnvI n)
    (by rw [lineLitEnvI, encEnv_bindA]; rfl) (lineLitEnvI_ok n)

end Line

end CatCrypt.Hax.RustSemantics
