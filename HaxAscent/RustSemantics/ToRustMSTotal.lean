/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMS
public import HaxAscent.RustSemantics.ToRustM
public import HaxAscent.RustSemantics.ToRustMSSpecDemo
public import HaxAscent.RustSemantics.ToRustMSTotalCtl

/-!
# Termination of the state-passing `RustM` reading on straight-line literals

`toRustMS_total` states that the reading `toRustMS app e ρ` returns a value on the
straight-line fragment `straightOk names bound e`: integer literals, variables in `bound` or
bound by an enclosing `let`, `let`, sequencing, type ascriptions and calls of every arity
to the names of `names`. The hypotheses are a class of values `P` containing the
integer literals, a reading of the calls total on `P` at the names and arities of `names`
(`AppTotalOn`), and an environment binding every name of `bound` to a value in `P`
(`EnvOk`). The returned value is in `P` and the final environment again satisfies
`EnvOk P bound`.

`fnCorres_toRustMS_triple_of_straightOk` combines the termination theorem with
`fnCorres_toRustMS`: a function correspondence, `AppOk`, and the three hypotheses above
give the total `Std.Do` triple of the reading, with no hypothesis that the reading returns
a value. The triple has the statement of `fnCorres_toRustMS_triple` of
`HaxAscent/RustSemantics/ToRustMSSpec.lean`, of which it is the instance at
`toRustMS_total`; it belongs beside that theorem.

## The instance on `lineLit`

`IsInt` is the class of integer literals; the reading of the calls `SpecDemo.addApp` of
`ToRustMSSpecDemo` reads `Add` on two literals as the addition of integers and is total on
`IsInt` (`addApp_total`).
`lineLit_straightOk` is decided by the kernel, and `lineLitI_triple` is the total triple of
the reading of `lineLit` from an environment binding the parameter to an integer literal.

## Relation to the kinded fragment

The straight-line fragment is the instance of the kinded fragment of `ToRustMSTotalCtl` at
one base kind, whose values are `P`, with integer literals at that base kind
(`kindOfL sig (.base ())`). `kindOfL_of_straightOk` states that a literal passing
`straightOk names bound` has the base kind under the signatures `straightSig names` and the
names `straightΓ bound`; `AppTotalOn.appTyped` and `envTy_straightΓ_iff` translate the
hypotheses. `toRustMS_total` and `fnCorres_toRustMS_triple_of_straightOk` are the
instances of `toRustMS_total_kindL` and `fnCorres_toRustMS_triple_of_kindOfL`.

## Main definitions

* `AppTotalOn`, `EnvOk`, `straightOk`, `straightSig`, `straightΓ`
* `StraightKindOk`, `StraightArgsKindOk`

## Main results

* `kindOfL_of_straightOk`, `AppTotalOn.appTyped`, `envTy_straightΓ_iff`
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
    enclosing `let`, `let`, sequencing, type ascriptions, and calls of every arity whose
    name and arity are in `names` and whose arguments are in the fragment. -/
def straightOk (names : List (String × Nat)) : List String → Hax.ImpExpr → Bool
  | _, .lit (.int _) => true
  | bound, .var x => bound.contains x
  | bound, .letBind x v b => straightOk names bound v && straightOk names (x :: bound) b
  | bound, .seq a b => straightOk names bound a && straightOk names bound b
  | bound, .typeAscription e _ => straightOk names bound e
  | bound, .app f args =>
    names.contains (f, args.length) && straightOk.list names bound args
  | _, _ => false
where
  /-- Every argument of a call is in the straight-line fragment under `bound`. -/
  list (names : List (String × Nat)) (bound : List String) : List Hax.ImpExpr → Bool
    | [] => true
    | a :: as => straightOk names bound a && list names bound as

/-! ## The fragment as an instance of the kinded fragment -/

/-- The signatures of the straight-line fragment over one base kind: a name of arity `n` of
    `names` takes `n` arguments of the base kind to the base kind. -/
def straightSig (names : List (String × Nat)) : List (String × List (Kd Unit) × Kd Unit) :=
  names.map fun p => (p.1, List.replicate p.2 (.base ()), .base ())

/-- The names of `bound`, each at the base kind. -/
def straightΓ (bound : List String) : List (String × Kd Unit) :=
  bound.map fun x => (x, .base ())

theorem lookup_straightΓ (bound : List String) (x : String) :
    (straightΓ bound).lookup x = if x ∈ bound then some (.base ()) else none := by
  induction bound with
  | nil => simp [straightΓ]
  | cons y bound ih =>
    by_cases h : x = y
    · subst h
      simp [straightΓ]
    · have hb : (x == y) = false := by simpa using h
      simp only [straightΓ, List.map_cons, List.lookup_cons, hb] at ih ⊢
      simp [ih, h]

theorem sigFind_straightSig {names : List (String × Nat)} {f : String} {n : Nat}
    (h : (f, n) ∈ names) :
    sigFind (straightSig names) f (List.replicate n (.base ())) = some (.base ()) := by
  unfold sigFind
  cases hs : (straightSig names).find?
      (fun s => decide (s.1 = f ∧ s.2.1 = List.replicate n (.base ()))) with
  | none =>
    rw [List.find?_eq_none] at hs
    exact absurd (by simp) (hs _ (List.mem_map.mpr ⟨_, h, rfl⟩))
  | some s =>
    have hm := List.mem_of_find?_eq_some hs
    simp only [straightSig, List.mem_map] at hm
    obtain ⟨p, -, rfl⟩ := hm
    rfl

/-- A reading of the calls total on `P` at the names of `names` is typed by the signatures
    `straightSig names` at the one base kind of values `P`. -/
theorem AppTotalOn.appTyped {P : AVal → Prop} {names : List (String × Nat)}
    {app : String → List AVal → RustM AVal} (h : AppTotalOn P names app) :
    AppTyped (fun _ => P) (straightSig names) app := by
  have hall : ∀ {ks : List (Kd Unit)} {vs : List AVal}, (∀ k ∈ ks, k = .base ()) →
      List.Forall₂ (Kd.Has fun _ => P) ks vs → ∀ v ∈ vs, P v := by
    intro ks vs hks hf
    induction hf with
    | nil => simp
    | cons hkv _ ih =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hks _ List.mem_cons_self] at hkv
        exact hkv
      · exact ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) v hv
  intro f ks k vs hs hvs
  simp only [straightSig, List.mem_map, Prod.mk.injEq] at hs
  obtain ⟨⟨g, n⟩, hgn, rfl, rfl, rfl⟩ := hs
  have hlen := forall₂_length_eq hvs
  simp only [List.length_replicate] at hlen
  exact h g vs (hlen ▸ hgn) (hall (fun k hk => (List.eq_of_mem_replicate hk)) hvs)

theorem envTy_straightΓ_iff {P : AVal → Prop} {bound : List String} {ρ : AEnv} :
    EnvTy (fun _ => P) (straightΓ bound) ρ ↔ EnvOk P bound ρ := by
  constructor
  · intro h x hx
    exact h x (.base ()) (by simp [lookup_straightΓ, hx])
  · intro h x k hk
    rw [lookup_straightΓ] at hk
    split at hk
    · rename_i hx
      cases hk
      exact h x hx
    · cases hk

/-- When `r` is `true`, the literal `e` has the base kind under `straightSig names` and
    `straightΓ bound`; `r` is instantiated at `straightOk names bound e`. -/
def StraightKindOk (names : List (String × Nat)) (bound : List String) (e : Hax.ImpExpr)
    (r : Bool) : Prop :=
  r = true → kindOfL (straightSig names) (.base ()) (straightΓ bound) e = some (.base ())

/-- When `r` is `true`, each argument of `args` has the base kind under `straightSig names`
    and `straightΓ bound`; `r` is instantiated at `straightOk.list names bound args`. -/
def StraightArgsKindOk (names : List (String × Nat)) (bound : List String)
    (args : List Hax.ImpExpr) (r : Bool) : Prop :=
  r = true → kindOfL.argsK (straightSig names) (.base ()) (straightΓ bound) args =
    some (List.replicate args.length (.base ()))

/-- A literal of the straight-line fragment has the base kind under the kind checker with
    integer literals at the base kind, the signatures `straightSig names` and the names of
    `bound` at the base kind. -/
theorem kindOfL_of_straightOk {names : List (String × Nat)} (bound : List String)
    (e : Hax.ImpExpr) : straightOk names bound e = true →
      kindOfL (straightSig names) (.base ()) (straightΓ bound) e = some (.base ()) := by
  suffices HS : ∀ bound e, StraightKindOk names bound e (straightOk names bound e) from
    HS bound e
  apply straightOk.induct_unfolding names (StraightArgsKindOk names) (StraightKindOk names)
  all_goals intros
  all_goals intro h
  all_goals try (simp at h; done)
  case case1 => rfl
  case case2 bound x =>
    simp only [List.contains_iff_mem] at h
    simp [kindOfL, lookup_straightΓ, h]
  case case3 bound x v b ihv ihb =>
    simp only [Bool.and_eq_true] at h
    have hfit : fits (straightΓ bound) x (.base ()) = true := by
      unfold fits
      rw [lookup_straightΓ]
      split <;> simp
    simp only [kindOfL, ihv h.1, hfit, ite_true]
    exact ihb h.2
  case case4 bound a b iha ihb =>
    simp only [Bool.and_eq_true] at h
    simp only [kindOfL, iha h.1]
    exact ihb h.2
  case case5 bound e ty ih =>
    simp only [kindOfL]
    exact ih h
  case case6 bound f args ih =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [kindOfL, ih h.2]
    exact sigFind_straightSig h.1
  case case8 bound => rfl
  case case9 bound a as iha ihas =>
    simp only [Bool.and_eq_true] at h
    simp only [kindOfL.argsK, iha h.1, ihas h.2, List.length_cons, List.replicate_succ]

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
  intro he ρ hρ
  obtain ⟨v, ρ', h, hv, hρ'⟩ := toRustMS_total_kindL (H := fun _ : Unit => P) (ki := .base ())
    hint happ.appTyped (straightΓ bound) e _ (kindOfL_of_straightOk bound e he) ρ
    (envTy_straightΓ_iff.mpr hρ)
  exact ⟨v, ρ', h, hv, envTy_straightΓ_iff.mp hρ'⟩

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
  fnCorres_toRustMS_triple_of_kindOfL (H := fun _ : Unit => P) (ki := .base ()) hF happ hint
    htot.appTyped (kindOfL_of_straightOk bound e he) a hG ρ hρ (envTy_straightΓ_iff.mpr hρP)

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
    exact ⟨.int (n + m), rfl, _, rfl⟩

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
