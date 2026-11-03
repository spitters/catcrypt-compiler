/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.Hax64Bridge
public import CatCrypt.Hax.TExprTypingSpine
public import CatCrypt.Crypto.Mpn.Extraction.Mpn_haxpipe
public meta import CatCrypt.Crypto.Hax.Hax64Bridge
public meta import CatCrypt.Crypto.Mpn.Extraction.Mpn_haxpipe
public import CatCryptCore.Tactics.KatGuard

/-!
# Result types of the `u64` table with array constructors

The instance of the result-type soundness of `denoteSpine`
(`CatCrypt.Hax.TExprTypingSpine.SpTy.spine_result`) at the builtin table `hax64WExit`.

`Hax64Ty` interprets a type the way `u64` code represents it: every scalar type (an integer
type, `bool`, `unit`) by the scalar values (`Value.int`, `Value.uint`, `Value.sint`,
`Value.bool`, `Value.unit`), since the table represents words by `Value.int` and returns
comparisons as `Value.bool`; an array type `array t n` by arrays of `n` values of type `t`;
slices and tuples pointwise. `Hax64Sig` gives `index` and `array_update` a signature at every
array type and scalar index type, `array_lit` one at every element type and length, and every
call other than `array_lit` and `repeat` the signatures from scalar types to a scalar type.
`hax64WExit_respect` proves that `hax64WExit` respects `Hax64Sig`, for a call name given as a
variable, from the lemmas of `Hax64Table` on the table's branches.

A function body typed at `array t n` with the early returns of `retEsc` therefore returns an
array or an early return carrying one, never a scalar: `valueToScalar` is `none` on its value
and a bridge `hax64WBridge (.TArr m e)` at a word element tower `e` holds only through its
array disjunct `hax64WArrRel`.

## Main definitions

* `scalarTyB`, `scalarVB` — scalar types and scalar values
* `Hax64Ty` — the value interpretation of the `u64` table
* `Hax64Sig` — the relational signature of `hax64WExit`
* `andTyEnv`, `andEnv` — the parameter types of `mpn_and_n` and an environment of that type

## Main results

* `hax64Ty_noCF` — no value of `Hax64Ty` is a control-flow value
* `hax64WExit_respect` — `hax64WExit` respects `Hax64Sig`
* `valueToScalar_of_arrayRes`, `hax64WBridge_arr_of_arrayRes` — the value of a function of
  array result type has no scalar decoding, and a bridge relating it is the array disjunct
* `texpr_spine_arrayRes` — a typed extraction with declared result type `array t n`, run by
  `denoteSpine hax64WExit`, returns an array of `n` values of type `t` after its early-return
  tag is removed, with no scalar decoding and only the array disjunct of the bridge
* `mpn_and_n_spTy` — `mpn_and_n`'s extraction has its declared result type
  `array (uint w64) 4` under `andTyEnv`
* `mpn_and_n_arrayRes` — the instance on `mpn_and_n` from every environment typed by
  `andTyEnv`; `andEnv_typed` and a `#kat` on the run from `andEnv` show its hypotheses
  satisfiable
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ResultType

open _root_.Hax (ImpExpr ImpType Value Env Outcome Builtins hax64Builtins hax64WordOps
  widthArrayOps TExpr IntWidth)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Hax.TExprTyping (TyEnv TyEnv.extend TyEnv.Le)
open CatCrypt.Hax.TExprTypingSpine
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## The value interpretation -/

/-- A scalar type: an integer type, `bool` or `unit`. -/
def scalarTyB : ImpType → Bool
  | .int => true
  | .uint _ => true
  | .sint _ => true
  | .bool => true
  | .unit => true
  | _ => false

/-- A scalar value: an integer, an unsigned or signed word, a Boolean or the unit. -/
def scalarVB : Value → Bool
  | .int _ => true
  | .uint _ _ => true
  | .sint _ _ => true
  | .bool _ => true
  | .unit => true
  | _ => false

/-- **The value interpretation of the `u64` table.**  A scalar type holds the scalar values;
    `array t n` holds arrays of `n` values of type `t`; `slice t` arrays of values of type
    `t`; a tuple type tuples of values of its component types. -/
inductive Hax64Ty : ImpType → Value → Prop where
  | scalar {τ : ImpType} {v : Value} : scalarTyB τ = true → scalarVB v = true → Hax64Ty τ v
  | array {t : ImpType} {n : Nat} {vs : List Value} :
      (∀ x ∈ vs, Hax64Ty t x) → vs.length = n → Hax64Ty (.array t n) (.array vs)
  | slice {t : ImpType} {vs : List Value} :
      (∀ x ∈ vs, Hax64Ty t x) → Hax64Ty (.slice t) (.array vs)
  | tuple {ts : List ImpType} {vs : List Value} (hl : vs.length = ts.length) :
      (∀ i (h : i < vs.length), Hax64Ty ts[i] vs[i]) → Hax64Ty (.tuple ts) (.tuple vs)

theorem hax64Ty_noCF : NoCF Hax64Ty := by
  intro τ v h
  cases h with
  | scalar _ hv => cases v <;> first | rfl | simp [scalarVB] at hv
  | array _ _ => rfl
  | slice _ => rfl
  | tuple _ _ => rfl

theorem Hax64Ty.scalarVB_of {τ : ImpType} {v : Value} (h : Hax64Ty τ v)
    (hτ : scalarTyB τ = true) : scalarVB v = true := by
  cases h with
  | scalar _ hv => exact hv
  | array _ _ => simp [scalarTyB] at hτ
  | slice _ => simp [scalarTyB] at hτ
  | tuple _ _ => simp [scalarTyB] at hτ

theorem Hax64Ty.array_inv {t : ImpType} {n : Nat} {v : Value} (h : Hax64Ty (.array t n) v) :
    ∃ vs, v = .array vs ∧ vs.length = n ∧ ∀ x ∈ vs, Hax64Ty t x := by
  cases h with
  | scalar hτ _ => simp [scalarTyB] at hτ
  | array hx hl => exact ⟨_, rfl, hl, hx⟩

theorem listW_scalar : {ts : List ImpType} → {vs : List Value} → ListW Hax64Ty ts vs →
    (∀ τ ∈ ts, scalarTyB τ = true) → ∀ x ∈ vs, scalarVB x = true
  | [], [], _, _, x, hx => by simp at hx
  | t :: ts, v :: vs, ⟨hv, hvs⟩, hts, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv.scalarVB_of (hts t (List.mem_cons_self ..))
      · exact listW_scalar hvs (fun τ hτ => hts τ (List.mem_cons_of_mem _ hτ)) x hx
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

theorem listW_replicate {t : ImpType} : (k : Nat) → {vs : List Value} →
    ListW Hax64Ty (List.replicate k t) vs → vs.length = k ∧ ∀ x ∈ vs, Hax64Ty t x
  | 0, [], _ => ⟨rfl, fun _ hx => by simp at hx⟩
  | 0, _ :: _, h => h.elim
  | k + 1, [], h => h.elim
  | k + 1, v :: vs, h => by
      obtain ⟨hv, hvs⟩ := h
      obtain ⟨hl, hx⟩ := listW_replicate k hvs
      refine ⟨by simp [hl], fun x hx' => ?_⟩
      rcases List.mem_cons.mp hx' with rfl | hx'
      · exact hv
      · exact hx x hx'

/-! ## The signature of `hax64WExit` -/

/-- **The relational signature of `hax64WExit`.**  `index` on an array of `t` and a scalar
    index gives a `t`; `array_update` on an array of `t`, a scalar index and a `t` gives the
    array type; `array_lit` of `k` values of `t` gives `array t k`; every call other than
    `array_lit` and `repeat` takes scalars to a scalar. -/
inductive Hax64Sig : String → List ImpType → ImpType → Prop where
  | index {t τi : ImpType} {n : Nat} :
      scalarTyB τi = true → Hax64Sig "index" [.array t n, τi] t
  | update {t τi : ImpType} {n : Nat} :
      scalarTyB τi = true → Hax64Sig "array_update" [.array t n, τi, t] (.array t n)
  | arrayLit (t : ImpType) (k : Nat) : Hax64Sig "array_lit" (List.replicate k t) (.array t k)
  | scalar {f : String} {ts : List ImpType} {r : ImpType} :
      f ≠ "array_lit" → f ≠ "repeat" → (∀ τ ∈ ts, scalarTyB τ = true) → scalarTyB r = true →
      Hax64Sig f ts r

theorem mem_of_getElem?_bind {xs : List Value} {k : Nat} {g : Value → Option Value}
    {v : Value} (hg : ∀ x, g x = some v → x = v) (h : xs[k]?.bind g = some v) : v ∈ xs := by
  rcases hx : xs[k]? with _ | x
  · rw [hx] at h; cases h
  · rw [hx] at h
    have hxv := hg x h
    subst hxv
    exact List.mem_of_getElem? hx

theorem hax64Builtins_index_mem {xs : List Value} {i v : Value}
    (h : hax64Builtins "index" [.array xs, i] = some v) : v ∈ xs := by
  have hg : ∀ x, (fun
      | .controlFlow _ _ => none
      | w => some w : Value → Option Value) x = some v → x = v := by
    intro x hx
    cases x <;> first | exact Option.some.inj hx | cases hx
  cases i with
  | int k =>
    rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_index _ _),
      _root_.Hax.widthArrayOps_index_int] at h
    by_cases hk : 0 ≤ k
    · rw [ite_eq_left hk] at h; exact mem_of_getElem?_bind hg h
    · rw [ite_eq_right hk] at h; cases h
  | uint w k =>
    have he : hax64Builtins "index" [.array xs, .uint w k] = xs[k]?.bind (fun
        | .controlFlow _ _ => none
        | w => some w) := rfl
    rw [he] at h
    exact mem_of_getElem?_bind hg h
  | _ => cases h

theorem hax64Builtins_update {xs : List Value} {i u v : Value}
    (h : hax64Builtins "array_update" [.array xs, i, u] = some v) :
    ∃ ys, v = .array ys ∧ ys.length = xs.length ∧ ∀ y ∈ ys, y ∈ xs ∨ y = u := by
  cases i with
  | int k =>
    rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_array_update _ _ _),
      _root_.Hax.widthArrayOps_array_update_int] at h
    by_cases hk : (0 ≤ k && k.toNat < xs.length) = true
    · rw [ite_eq_left hk] at h
      cases h
      exact ⟨_, rfl, List.length_set .., fun y hy => List.mem_or_eq_of_mem_set hy⟩
    · rw [ite_eq_right hk] at h
      cases h
  | uint w k =>
    have he : hax64Builtins "array_update" [.array xs, .uint w k, u] =
        if k < xs.length then some (.array (xs.set k u)) else none := rfl
    rw [he] at h
    by_cases hk : k < xs.length
    · rw [ite_eq_left hk] at h
      cases h
      exact ⟨_, rfl, List.length_set .., fun y hy => List.mem_or_eq_of_mem_set hy⟩
    · rw [ite_eq_right hk] at h
      cases h
  | _ => cases h

theorem hax64ArrShape_head {f : String} {vals : List Value}
    (h : hax64ArrShape f vals = true) : ∃ a rest, vals = .array a :: rest := by
  unfold hax64ArrShape at h
  split at h <;> first | exact ⟨_, _, rfl⟩ | cases h

/-- **`hax64WExit` respects `Hax64Sig`**, for a call name given as a variable. -/
theorem hax64WExit_respect : RespectW Hax64Ty Hax64Sig hax64WExit := by
  intro f ts r hS vs hvs v hv
  cases hS with
  | @index _ _ n _ =>
    match vs, hvs, hv with
    | [a, _], hvs, hv =>
      have ha : Hax64Ty (.array r n) a := hvs.1
      obtain ⟨xs, rfl, -, hxs⟩ := ha.array_inv
      exact hxs v (hax64Builtins_index_mem (hax64WExit_sub hv))
    | [], h, _ => exact h.elim
    | [_], h, _ => exact h.2.elim
    | _ :: _ :: _ :: _, h, _ => exact h.2.2.elim
  | @update t _ n _ =>
    match vs, hvs, hv with
    | [a, _, u], hvs, hv =>
      have ha : Hax64Ty (.array t n) a := hvs.1
      have hu : Hax64Ty t u := hvs.2.2.1
      obtain ⟨xs, rfl, hl, hxs⟩ := ha.array_inv
      obtain ⟨ys, rfl, hyl, hys⟩ := hax64Builtins_update (hax64WExit_sub hv)
      refine .array (fun y hy => ?_) (hyl.trans hl)
      rcases hys y hy with hy | rfl
      · exact hxs y hy
      · exact hu
    | [], h, _ => exact h.elim
    | [_], h, _ => exact h.2.elim
    | [_, _], h, _ => exact h.2.2.elim
    | _ :: _ :: _ :: _ :: _, h, _ => exact h.2.2.2.elim
  | arrayLit t k =>
    obtain ⟨-, rfl⟩ := hax64WExit_arrayLit hv
    obtain ⟨hl, hx⟩ := listW_replicate k hvs
    exact .array hx hl
  | scalar hne1 hne2 hts hr =>
    have hsc := listW_scalar hvs hts
    refine .scalar hr ?_
    by_cases heq : f = "eq#arr" ∨ f = "ne#arr"
    · obtain ⟨a, b, rfl, -⟩ := hax64WExit_eqArr heq hv
      have := hsc (.array a) (List.mem_cons_self ..)
      simp [scalarVB] at this
    · have h1 : f ≠ "eq#arr" := fun h => heq (Or.inl h)
      have h2 : f ≠ "ne#arr" := fun h => heq (Or.inr h)
      by_cases hw : hax64WideHead f
      · rw [hax64WExit_wide hw] at hv
        obtain ⟨⟨a, rest, rfl⟩, -⟩ := hax64Builtins_wideHead hw hv
        have := hsc (.array a) (List.mem_cons_self ..)
        simp [scalarVB] at this
      by_cases hs : f = "select"
      · subst hs
        obtain ⟨k, x, y, rfl, -, -, rfl⟩ := hax64WExit_select_some hv
        split <;> exact hsc _ (by simp)
      rw [hax64WExit_of_ne hne1 hne2 h1 h2 hw hs] at hv
      obtain ⟨-, -, hsh⟩ := hax64Exit_some hv
      rcases hsh with hA | hA
      · obtain ⟨a, rest, rfl⟩ := hax64ArrShape_head hA
        have := hsc (.array a) (List.mem_cons_self ..)
        simp [scalarVB] at this
      · unfold hax64ScalarAdmit at hA
        simp only [Bool.and_eq_true] at hA
        have hv' := hA.2
        cases v <;> simp_all [scalarValNB, scalarVB]

/-! ## Functions of array result type -/

/-- The value of a function of result type `array t n`: an array of that type or an early
    return carrying one. -/
def ArrayRes (t : ImpType) (n : Nat) (v : Value) : Prop :=
  Hax64Ty (.array t n) v ∨ ∃ u, v = .controlFlow true u ∧ Hax64Ty (.array t n) u

theorem valueToScalar_of_arrayRes {t : ImpType} {n : Nat} {v : Value} (h : ArrayRes t n v) :
    valueToScalar v = none := by
  rcases h with h | ⟨u, rfl, -⟩
  · obtain ⟨vs, rfl, -⟩ := h.array_inv
    rfl
  · rfl

theorem not_scalarValN_of_arrayRes {t : ImpType} {n : Nat} {v : Value} (h : ArrayRes t n v) :
    ¬ ScalarValN v := by
  rcases h with h | ⟨u, rfl, -⟩
  · obtain ⟨vs, rfl, -⟩ := h.array_inv
    exact fun h => h
  · exact fun h => h

/-- **The bridge at a function of array result type.**  At a tower `.TArr m e` of word
    elements, a bridge relating the value of a function of result type `array t n` is its
    array disjunct `hax64WArrRel`. -/
theorem hax64WBridge_arr_of_arrayRes {t : ImpType} {n m : Nat} {e : TowerType}
    (hw : exitWordTower e = true) {v : Value} (h : ArrayRes t n v) {r : RustVal (.TArr m e)}
    (hb : hax64WBridge (.TArr m e) v r) : hax64WArrRel (.TArr m e) v r := by
  rcases hb with hs | ha | ⟨hwf, -⟩
  · exact absurd hs.1 (not_scalarValN_of_arrayRes h)
  · exact ha
  · rw [hw] at hwf; cases hwf

/-- **Result type of a typed extraction of array result type.**  A typed extraction `te`
    whose declared result type is `array t n`, typed at it with the early returns of
    `retEsc`, run by `denoteSpine hax64WExit` from an environment typed by `Γ` to a value
    `v`, returns an array of `n` values of type `t` after its early-return tag is removed;
    `valueToScalar v` is `none`, and at a tower `.TArr m e` of word elements a bridge relating
    `v` is its array disjunct. -/
theorem texpr_spine_arrayRes {Γ : TyEnv} {te : TExpr} {t : ImpType} {n : Nat}
    (hty : te.ty = .array t n)
    (h : SpTy Hax64Ty Hax64Sig Γ (retEsc Hax64Ty te.ty) te.erase te.ty)
    {fuel : Nat} {env env' : Env} {v : Value} (henv : EnvW Hax64Ty Γ env)
    (hrun : (denoteSpine hax64WExit fuel te.erase).run env = (.val v, env')) :
    (∃ vs, stripRet v = .array vs ∧ vs.length = n ∧ ∀ x ∈ vs, Hax64Ty t x) ∧
      valueToScalar v = none ∧
      ∀ {m : Nat} {e : TowerType}, exitWordTower e = true → ∀ r : RustVal (.TArr m e),
        hax64WBridge (.TArr m e) v r → hax64WArrRel (.TArr m e) v r := by
  rw [hty] at h
  have hres : ArrayRes t n v :=
    (SpTy.spine_result hax64Ty_noCF hax64WExit_respect h henv hrun).1
  refine ⟨(SpTy.spine_stripRet hax64Ty_noCF hax64WExit_respect h henv hrun).array_inv,
    valueToScalar_of_arrayRes hres, fun hw r hb => hax64WBridge_arr_of_arrayRes hw hres hb⟩

/-! ## `mpn_and_n` -/

/-- The parameter types of `mpn_and_n`: the arrays `rp`, `up`, `vp` of four `u64` words and
    the count `n : usize`. -/
def andTyEnv : TyEnv :=
  TyEnv.extend (TyEnv.extend (TyEnv.extend (TyEnv.extend (fun _ => none) "rp" Mpn.ty_1)
    "up" Mpn.ty_1) "vp" Mpn.ty_1) "n" Mpn.ty_8

theorem scalar_ty7 (v : Value) (hv : scalarVB v = true) : Hax64Ty Mpn.ty_7 v :=
  .scalar rfl hv

theorem scalar_ty8 (v : Value) (hv : scalarVB v = true) : Hax64Ty Mpn.ty_8 v :=
  .scalar rfl hv

theorem le_extend_new {Γ : TyEnv} {x : String} {τ : ImpType} (h : Γ x = none) :
    TyEnv.Le Γ (Γ.extend x τ) :=
  TyEnv.le_extend fun τ' h' => by rw [h] at h'; cases h'

theorem le_extend_same {Γ : TyEnv} {x : String} {τ : ImpType} (h : Γ x = some τ) :
    TyEnv.Le Γ (Γ.extend x τ) :=
  TyEnv.le_extend fun τ' h' => by rw [h] at h'; cases h'; rfl

/-- **`mpn_and_n` has its declared result type.**  The extraction of `mpn_and_n` is typed
    at its declared result type `array (uint w64) 4` under `andTyEnv`, with the early returns
    of `retEsc`. -/
theorem mpn_and_n_spTy :
    SpTy Hax64Ty Hax64Sig andTyEnv (retEsc Hax64Ty Mpn.mpn_and_n_texpr.ty)
      Mpn.mpn_and_n_texpr.erase Mpn.mpn_and_n_texpr.ty := by
  show SpTy Hax64Ty Hax64Sig andTyEnv (retEsc Hax64Ty Mpn.ty_1) Mpn.mpn_and_n_impExpr Mpn.ty_1
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .seq (σ := .unit) ?_ (.var rfl)
  refine .forFold (σ₁ := Mpn.ty_8) (σ₂ := Mpn.ty_8) (τi := Mpn.ty_8) (σb := .unit)
    (.lit (scalar_ty8 _ rfl)) (.var rfl) (fun k => scalar_ty8 _ rfl) (le_extend_new rfl) ?_
    (.scalar rfl rfl)
  refine .letBind (τ₁ := Mpn.ty_7)
    (.app (.index (n := 4) rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
    (le_extend_new rfl) ?_
  refine .letBind (τ₁ := Mpn.ty_7)
    (.app (.index (n := 4) rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
    (le_extend_new rfl) ?_
  refine .seq (σ := .unit) (.seq (σ := Mpn.ty_1) ?_ (.unitVal (.scalar rfl rfl)))
    (.unitVal (.scalar rfl rfl))
  refine .letBind (τ₁ := Mpn.ty_1) ?_ (le_extend_same rfl) (.var rfl)
  refine .app (.update (n := 4) (τi := Mpn.ty_8) rfl)
    (.cons (.var rfl) (.cons (.var rfl) (.cons ?_ .nil)))
  refine .app (ts := [Mpn.ty_7, Mpn.ty_7]) (.scalar (by decide) (by decide) ?_ rfl)
    (.cons (.var rfl) (.cons (.var rfl) .nil))
  intro τ hτ
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hτ
  subst hτ
  rfl

/-- **`mpn_and_n` returns an array.**  From every environment typed by `andTyEnv`, a run of
    `denoteSpine hax64WExit` on `mpn_and_n`'s extraction to a value `v` returns an array of
    four words after its early-return tag is removed; `valueToScalar v` is `none`, and at a
    tower `.TArr m e` of word elements a bridge relating `v` is its array disjunct. -/
theorem mpn_and_n_arrayRes {fuel : Nat} {env env' : Env} {v : Value}
    (henv : EnvW Hax64Ty andTyEnv env)
    (hrun : (denoteSpine hax64WExit fuel Mpn.mpn_and_n_texpr.erase).run env = (.val v, env')) :
    (∃ vs, stripRet v = .array vs ∧ vs.length = 4 ∧ ∀ x ∈ vs, Hax64Ty Mpn.ty_7 x) ∧
      valueToScalar v = none ∧
      ∀ {m : Nat} {e : TowerType}, exitWordTower e = true → ∀ r : RustVal (.TArr m e),
        hax64WBridge (.TArr m e) v r → hax64WArrRel (.TArr m e) v r :=
  texpr_spine_arrayRes rfl mpn_and_n_spTy henv hrun

/-- An environment of `mpn_and_n`'s parameter types: `rp` zero, `up` and `vp` two arrays of
    four words, `n = 4`. -/
def andEnv : Env := fun x =>
  if x = "rp" then some (.array [.int 0, .int 0, .int 0, .int 0])
  else if x = "up" then some (.array [.int 0xF0, .int 0x0F, .int 0xFF, .int 5])
  else if x = "vp" then some (.array [.int 0xFF, .int 0xFF, .int 0x0F, .int 3])
  else if x = "n" then some (.int 4)
  else none

theorem andEnv_typed : EnvW Hax64Ty andTyEnv andEnv := by
  intro x τ hx
  simp only [andTyEnv, TyEnv.extend, beq_iff_eq] at hx
  unfold andEnv
  by_cases hn : x = "n"
  · subst hn
    rw [ite_eq_left rfl] at hx
    cases hx
    exact ⟨_, rfl, scalar_ty8 _ rfl⟩
  · rw [ite_eq_right hn] at hx
    by_cases hv : x = "vp"
    · subst hv
      rw [ite_eq_left rfl] at hx
      cases hx
      exact ⟨_, rfl, .array (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> exact scalar_ty7 _ rfl) rfl⟩
    · rw [ite_eq_right hv] at hx
      by_cases hu : x = "up"
      · subst hu
        rw [ite_eq_left rfl] at hx
        cases hx
        exact ⟨_, rfl, .array (fun y hy => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl <;> exact scalar_ty7 _ rfl) rfl⟩
      · rw [ite_eq_right hu] at hx
        by_cases hr : x = "rp"
        · subst hr
          rw [ite_eq_left rfl] at hx
          cases hx
          exact ⟨_, rfl, .array (fun y hy => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl | rfl <;> exact scalar_ty7 _ rfl) rfl⟩
        · rw [ite_eq_right hr] at hx
          cases hx

end CatCrypt.Crypto.Hax.ResultType
