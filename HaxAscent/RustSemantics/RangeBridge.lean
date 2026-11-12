/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMSBreak
public import HaxLean.Range.Sound
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Data.DTreeMap.Internal.Operations

/-!
# From a value of the guarded run to a value of the `RustM` reading

`toRustMSB_sim` (`HaxAscent/RustSemantics/ToRustMSBreak.lean`) runs from the reading to the
runtime: a value of the `RustM` reading `toRustMSB app e ρ` is the value of `Hax.denote'`
from `encEnv ρ`. This module proves the converse on a syntactic fragment: a value of the
run of `e` under a table `bi` is a value of the reading, provided the reading of the calls
returns a value wherever `bi` does (`AppComplete`). At the table
`Range.guardBi Range.rustGuard bi`, which has no value where a Rust guard fails, the
hypothesis states that the reading of the calls fails only where Rust panics.

The fragment `RevFrag k e` contains the constructs the reading interprets as `Hax.denote'`
does: integer literals within the loop bound, Booleans, variables, `let`, sequencing, the
unit value, type ascriptions, tuples, conditionals, calls, `cfBreak` (only where
`k = true`) and counted loops `forFold` whose bounds do not break. The values of the reading
are small (`AVal.Small`): an integer or a word is at most the bound `2 ^ usize`, so that
the bounds of a counted loop are in the range the reading accepts.

## Main definitions

* `AVal.Small`, `BOut.Small`, `EnvSmall`: integers and words at most `2 ^ usize`.
* `AppComplete`: the reading of the calls returns a small value encoding the value of the
  table, on small arguments.
* `RevFrag`: the fragment.
* `aParamEnv`: the reading's environment binding parameters.

## Main results

* `toRustMSB_complete`: a value of `Hax.denote'` from `encEnv ρ` is the encoding of the
  outcome of `toRustMSB app e ρ`, which returns a value.
* `encEnv_aParamEnv`: `encEnv (aParamEnv ps vs)` is `Range.paramEnv ps` of the encodings.
* `toRustMSB_paramEnv`: the converse at the parameter environment of a function body.
* `toRustMSB_ok_of_noPanicOn`: from a theorem of the form `f_noPanicOn` (the guarded run
  is the unguarded one from every environment in the summary's precondition) and a value of
  the unguarded run, the reading returns that value.
* `toRustMSB_spec_of_noPanicOn`: from `f_noPanicOn` and a function correspondence
  `FnCorres bi e entry G f_pure`, the reading returns the encoding of `f_pure a`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RangeRustM

open CatCrypt CatCrypt.Hax CatCrypt.Hax.RustSemantics HaxAscent.RustSemantics Aeneas.Std
open Hax.Ascent (stateM_bind_apply bindCF_eq_val)

/-! ## Small values -/

/-- An integer literal in `[0, 2 ^ usize]`, a word at most `2 ^ usize`, or any other value. -/
def _root_.CatCrypt.Hax.RustSemantics.AVal.Small : AVal → Prop
  | .int n => 0 ≤ n ∧ n ≤ 2 ^ UScalarTy.Usize.numBits
  | .w _ x => (x.val : Int) ≤ 2 ^ UScalarTy.Usize.numBits
  | _ => True

/-- The value of an outcome is small. -/
def _root_.HaxAscent.RustSemantics.BOut.Small : BOut → Prop
  | .val v => v.Small
  | .brk v => v.Small

/-- Every value the environment binds is small. -/
def EnvSmall (ρ : AEnv) : Prop :=
  ∀ x v, ρ x = some v → v.Small

/-- The loop index is small. -/
theorem ctr_small (i : Nat) : (ctr i).Small := by
  simp only [ctr, AVal.Small]
  exact Int.le_of_lt (by exact_mod_cast (BitVec.ofNat UScalarTy.Usize.numBits i).isLt)

/-- Binding a small value keeps an environment small. -/
theorem EnvSmall.upd {ρ : AEnv} (h : EnvSmall ρ) (x : String) {v : AVal} (hv : v.Small) :
    EnvSmall (ρ.upd x v) := by
  intro y w hy
  simp only [AEnv.upd] at hy
  split at hy
  · cases hy; exact hv
  · exact h y w hy

/-! ## Completeness of the reading of the calls -/

/-- On small arguments, wherever the table `bi` returns a value, the reading of the calls
    `app` returns a small value encoding it. -/
def AppComplete (bi : _root_.Hax.Builtins) (app : String → List AVal → RustM AVal) : Prop :=
  ∀ f vs w, (∀ v ∈ vs, v.Small) → bi f (AVal.toValues vs) = some w →
    ∃ r, app f vs = .ok r ∧ r.toValue = w ∧ r.Small

/-! ## The fragment -/

/-- The fragment of the converse. `RevFrag k e`: `e` is built from integer literals in
    `[0, 2 ^ usize]`, Booleans, variables, `let`, sequencing, the unit value, type
    ascriptions, tuples, conditionals, calls, counted loops `forFold` whose bounds are in
    `RevFrag false`, and, where `k = true`, `cfBreak`. -/
inductive RevFrag : Bool → _root_.Hax.ImpExpr → Prop where
  /-- An integer literal in `[0, 2 ^ usize]`. -/
  | litInt {k : Bool} {n : Int} : 0 ≤ n → n ≤ 2 ^ UScalarTy.Usize.numBits →
      RevFrag k (.lit (.int n))
  /-- A Boolean literal. -/
  | litBool {k : Bool} (b : Bool) : RevFrag k (.lit (.bool b))
  /-- A variable. -/
  | var {k : Bool} (x : String) : RevFrag k (.var x)
  /-- A `let`. -/
  | letBind {k : Bool} {x : String} {v b : _root_.Hax.ImpExpr} :
      RevFrag k v → RevFrag k b → RevFrag k (.letBind x v b)
  /-- The unit value. -/
  | unitVal {k : Bool} : RevFrag k .unitVal
  /-- Sequencing. -/
  | seq {k : Bool} {a b : _root_.Hax.ImpExpr} : RevFrag k a → RevFrag k b → RevFrag k (.seq a b)
  /-- A type ascription. -/
  | typeAscription {k : Bool} {e : _root_.Hax.ImpExpr} (ty : String) :
      RevFrag k e → RevFrag k (.typeAscription e ty)
  /-- A tuple. -/
  | tuple {k : Bool} {es : List _root_.Hax.ImpExpr} :
      (∀ e ∈ es, RevFrag k e) → RevFrag k (.tuple es)
  /-- A conditional. -/
  | ifThenElse {k : Bool} {c t e : _root_.Hax.ImpExpr} :
      RevFrag k c → RevFrag k t → RevFrag k e → RevFrag k (.ifThenElse c t e)
  /-- A `break` with a value, inside a loop body. -/
  | cfBreak {e : _root_.Hax.ImpExpr} : RevFrag true e → RevFrag true (.cfBreak e)
  /-- A counted loop whose bounds do not break. -/
  | forFold {k : Bool} {var : String} {lo hi body : _root_.Hax.ImpExpr} :
      RevFrag false lo → RevFrag false hi → RevFrag true body →
      RevFrag k (.forFold var lo hi body)
  /-- A call. -/
  | app {k : Bool} {f : String} {args : List _root_.Hax.ImpExpr} :
      (∀ a ∈ args, RevFrag k a) → RevFrag k (.app f args)

/-- The converse for one expression: a value of the run from `encEnv ρ` is the encoding of
    the small outcome of the reading from `ρ`, which ends in a small environment encoding the
    final one; the outcome is a value when `k = false`. -/
def Complete (bi : _root_.Hax.Builtins) (app : String → List AVal → RustM AVal) (k : Bool)
    (e : _root_.Hax.ImpExpr) : Prop :=
  ∀ fuel ρ w σ, EnvSmall ρ → _root_.Hax.denote' bi fuel e (encEnv ρ) = (.val w, σ) →
    ∃ r ρ', toRustMSB app e ρ = .ok (r, ρ') ∧ r.toValue = w ∧ encEnv ρ' = σ ∧ r.Small ∧
      EnvSmall ρ' ∧ (k = false → r.brk? = none)

/-- A breaking outcome encodes a control-flow value. -/
theorem BOut.toValue_isControlFlow (r : BOut) : r.toValue.isControlFlow = r.brk?.isSome := by
  cases r with
  | val v => simp only [BOut.toValue, BOut.brk?, AVal.toValue_isControlFlow, Option.isSome_none]
  | brk v => rfl

/-! ## Argument lists -/

/-- The converse for the arguments of a call or the components of a tuple. -/
theorem argsSB_complete {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    {k : Bool} : ∀ {es : List _root_.Hax.ImpExpr}, (∀ e ∈ es, Complete bi app k e) →
    ∀ fuel ρ vals σ, EnvSmall ρ →
      _root_.Hax.denoteArgs' bi fuel es (encEnv ρ) = (some vals, σ) →
      ∃ vs ρ', toRustMSB.argsSB app es ρ = .ok (vs, ρ') ∧ AVal.toValues vs = vals ∧
        encEnv ρ' = σ ∧ (∀ v ∈ vs, v.Small) ∧ EnvSmall ρ'
  | [], _, fuel, ρ, vals, σ, hρ, h => by
    rw [Hax.Ascent.denoteArgs'_nil] at h
    cases h
    exact ⟨[], ρ, rfl, rfl, rfl, by simp, hρ⟩
  | e :: es, ih, fuel, ρ, vals, σ, hρ, h => by
    obtain ⟨w, s, ws, h1, hcf, h2, rfl⟩ := (Hax.Ascent.denoteArgs'_cons_eq bi fuel).mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s, -⟩ := ih e List.mem_cons_self fuel ρ w s hρ h1
    cases r with
    | brk a =>
      subst hrw
      simp [BOut.toValue] at hcf
    | val a =>
      subst hρ1
      obtain ⟨vs, ρ2, hvs, hvv, hρ2, hvsS, hρ2s⟩ :=
        argsSB_complete (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) fuel ρ1 ws σ hρ1s h2
      refine ⟨a :: vs, ρ2, ?_, ?_, hρ2, ?_, hρ2s⟩
      · simp only [toRustMSB.argsSB, hr]
        simp [hvs]
      · simp only [AVal.toValues, hvv]
        simp only [BOut.toValue] at hrw
        rw [hrw]
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hrs
        · exact hvsS v hv

/-! ## Counted loops -/

/-- A value of a counted loop with at least one step comes from a value of the body at a
    nonzero fuel. -/
theorem denoteForLoop'_body_val {bi : _root_.Hax.Builtins} {fuel : Nat} {var : String}
    {a b : Int} {body : _root_.Hax.ImpExpr} {env σ : _root_.Hax.Env} {w : _root_.Hax.Value}
    (hab : a < b) (h : _root_.Hax.denoteForLoop' bi fuel var a b body env = (.val w, σ)) :
    fuel ≠ 0 ∧ ∃ w1 s1,
      _root_.Hax.denote' bi fuel body (env.extend var (.int a)) = (.val w1, s1) := by
  rw [_root_.Hax.denoteForLoop'] at h
  split at h
  · omega
  split at h
  · cases h
  rename_i hf
  refine ⟨hf, ?_⟩
  simp only [Hax.Ascent.stateM_bind_apply, Hax.Ascent.stateM_modify_apply] at h
  rcases hb : _root_.Hax.denote' bi fuel body (env.extend var (.int a)) with ⟨o, s⟩
  rw [hb] at h
  rcases o with (w1|_|_|_|_)
  · exact ⟨w1, s, rfl⟩
  all_goals cases h

/-- A value of a counted loop `forFold` comes from value runs of its bounds; when neither
    bound is a control-flow value, both are integers or unsigned words. -/
theorem denote'_forFold_inv {bi : _root_.Hax.Builtins} {fuel : Nat} {var : String}
    {lo hi body : _root_.Hax.ImpExpr} {env σ : _root_.Hax.Env} {w : _root_.Hax.Value}
    (h : _root_.Hax.denote' bi fuel (.forFold var lo hi body) env = (.val w, σ)) :
    ∃ wl s1, _root_.Hax.denote' bi fuel lo env = (.val wl, s1) ∧
      (wl.isControlFlow = true ∨ ∃ wu s2, _root_.Hax.denote' bi fuel hi s1 = (.val wu, s2) ∧
        (wu.isControlFlow = true ∨
          ((∃ a, wl = .int a) ∨ ∃ t a, wl = .uint t a) ∧
          ((∃ b, wu = .int b) ∨ ∃ t b, wu = .uint t b))) := by
  simp only [_root_.Hax.denote', Hax.Ascent.stateM_bind_apply] at h
  rcases hlo : _root_.Hax.denote' bi fuel lo env with ⟨o1, s1⟩
  rw [hlo] at h
  rcases o1 with (wl|_|_|_|_)
  · refine ⟨wl, s1, rfl, ?_⟩
    cases hcl : wl.isControlFlow
    · right
      rcases hhi : _root_.Hax.denote' bi fuel hi s1 with ⟨o2, s2⟩
      rcases o2 with (wu|_|_|_|_) <;> cases wl <;> simp at hcl <;> (try cases wu) <;>
        simp_all [Hax.Ascent.stateM_bind_apply] <;> (try cases h) <;>
        exact ⟨_, ⟨_, rfl⟩, by simp [Hax.Value.isControlFlow]⟩
    · exact Or.inl rfl
  all_goals cases h

/-- The converse for the counted loop: a value of `denoteForLoop'` from index `i` to `b` is
    the value of `k = (b - i).toNat` steps of `loopBS` on the reading of the body. -/
theorem loopBS_complete {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    {var : String} {body : _root_.Hax.ImpExpr} (ih : Complete bi app true body) :
    ∀ (k i : Nat) (b : Int) (fuel : Nat) (ρ : AEnv) (w : _root_.Hax.Value)
      (σ : _root_.Hax.Env), (b - i).toNat = k → b ≤ 2 ^ UScalarTy.Usize.numBits → EnvSmall ρ →
      _root_.Hax.denoteForLoop' bi fuel var i b body (encEnv ρ) = (.val w, σ) →
      ∃ o ρ', loopBS (fun i ρ => toRustMSB app body (ρ.upd var (ctr i)) >>= fun s =>
          .ok (s.1.brk?, s.2)) k i ρ = .ok (o, ρ') ∧ (o.getD .unit).toValue = w ∧
        encEnv ρ' = σ ∧ (o.getD .unit).Small ∧ EnvSmall ρ'
  | 0, i, b, fuel, ρ, w, σ, hk, _, hρ, h => by
    rw [Hax.Ascent.denoteForLoop'_done bi fuel var body _ (by omega)] at h
    cases h
    exact ⟨none, ρ, rfl, rfl, rfl, trivial, hρ⟩
  | k + 1, i, b, fuel, ρ, w, σ, hk, hb, hρ, h => by
    have hib : (i : Int) < b := by omega
    have hi : i < 2 ^ UScalarTy.Usize.numBits := by
      have : (i : Int) < 2 ^ UScalarTy.Usize.numBits := by omega
      exact_mod_cast this
    obtain ⟨hf, w1, s1, h1⟩ := denoteForLoop'_body_val hib h
    have henv : (encEnv ρ).extend var (.int i) = encEnv (ρ.upd var (ctr i)) := by
      rw [encEnv_upd, ctr_toValue hi]
    rw [henv] at h1
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s, -⟩ :=
      ih fuel (ρ.upd var (ctr i)) w1 s1 (hρ.upd var (ctr_small i)) h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rw [← henv] at h1
      rw [Hax.Ascent.denoteForLoop'_break bi fuel var hib hf h1] at h
      cases h
      refine ⟨some a, ρ1, ?_, rfl, rfl, hrs, hρ1s⟩
      simp only [loopBS, hr]
      rfl
    | val a =>
      rw [← henv] at h1
      rw [Hax.Ascent.denoteForLoop'_next bi fuel var hib hf h1
        (AVal.toValue_ne_break a)] at h
      have h' : _root_.Hax.denoteForLoop' bi (fuel - 1) var ((i + 1 : Nat) : Int) b body
          (encEnv ρ1) = (.val w, σ) := by
        rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by push_cast; rfl]
        exact h
      obtain ⟨o, ρ2, ho, how, hρ2, hos, hρ2s⟩ :=
        loopBS_complete ih k (i + 1) b (fuel - 1) ρ1 w σ (by omega) hb hρ1s h'
      refine ⟨o, ρ2, ?_, how, hρ2, hos, hρ2s⟩
      simp only [loopBS, hr]
      exact ho

/-! ## The converse -/

/-- **The converse of `toRustMSB_sim`.** On the fragment `RevFrag k`, when the reading of the
    calls is complete for `bi`, a value `w` of the run of `e` under `bi` from `encEnv ρ` is
    the encoding of the outcome of the reading `toRustMSB app e ρ`, which returns a value. -/
theorem toRustMSB_complete {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    (hc : AppComplete bi app) {k : Bool} {e : _root_.Hax.ImpExpr} (hf : RevFrag k e) :
    Complete bi app k e := by
  induction hf with
  | litInt h0 h1 =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_lit] at h
    cases h
    exact ⟨.val (.int _), ρ, rfl, rfl, rfl, ⟨h0, h1⟩, hρ, fun _ => rfl⟩
  | litBool b =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_lit] at h
    cases h
    exact ⟨.val (.bool b), ρ, rfl, rfl, rfl, trivial, hρ, fun _ => rfl⟩
  | var x =>
    intro fuel ρ w σ hρ h
    obtain ⟨hx, rfl⟩ := (Hax.Ascent.denote'_var_eq bi fuel).mp h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨.val v, ρ, by simp only [toRustMSB, hv], rfl, rfl, hρ x v hv, hρ, fun _ => rfl⟩
  | letBind _ _ ihv ihb =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_letBind_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s, hk⟩ := ihv fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s, hk⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · rw [BOut.toValue, ← encEnv_upd] at h2
        obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩ :=
          ihb fuel (ρ1.upd _ a) w σ (hρ1s.upd _ hrs) h2
        exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩
  | unitVal =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_unitVal] at h
    cases h
    exact ⟨.val .unit, ρ, rfl, rfl, rfl, trivial, hρ, fun _ => rfl⟩
  | seq _ _ iha ihb =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_seq_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s, hk⟩ := iha fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s, hk⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩ := ihb fuel ρ1 w σ hρ1s h2
        exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩
  | typeAscription ty _ ih =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_typeAscription] at h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s, hk⟩ := ih fuel ρ w σ hρ h
    exact ⟨r, ρ1, by simp only [toRustMSB]; exact hr, hrw, hρ1, hrs, hρ1s, hk⟩
  | tuple _ ih =>
    intro fuel ρ w σ hρ h
    obtain ⟨vals, h1, rfl⟩ := (Hax.Ascent.denote'_tuple_eq bi fuel).mp h
    obtain ⟨vs, ρ1, hvs, hvv, hρ1, -, hρ1s⟩ := argsSB_complete ih fuel ρ vals σ hρ h1
    refine ⟨.val (.tup vs), ρ1, ?_, ?_, hρ1, trivial, hρ1s, fun _ => rfl⟩
    · simp only [toRustMSB, hvs]
      rfl
    · simp only [BOut.toValue, AVal.toValue, hvv]
  | ifThenElse _ _ _ ihc iht ihe =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_ifThenElse_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s, hk⟩ := ihc fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s, hk⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · cases a with
        | bool b =>
          simp only [BOut.toValue, AVal.toValue] at h2
          cases b with
          | true =>
            obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩ := iht fuel ρ1 w σ hρ1s h2
            exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩
          | false =>
            obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩ := ihe fuel ρ1 w σ hρ1s h2
            exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩
        | _ => simp [BOut.toValue, AVal.toValue] at h2
  | cfBreak _ ih =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_cfBreak_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s, -⟩ := ih fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s,
          fun h => nomatch h⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · cases h2
        exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s,
          fun h => nomatch h⟩
  | @forFold k var lo hi body _ _ _ ihlo ihhi ihbody =>
    intro fuel ρ w σ hρ h
    obtain ⟨wl, s1, h1, hcase⟩ := denote'_forFold_inv h
    obtain ⟨r1, ρ1, hr1, hrw1, hρ1, hrs1, hρ1s, hk1⟩ := ihlo fuel ρ wl s1 hρ h1
    subst hρ1 hrw1
    cases r1 with
    | brk _ => exact absurd (hk1 rfl) (by simp [BOut.brk?])
    | val l =>
    rcases hcase with hcf | ⟨wu, s2, h2, hcase2⟩
    · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
    obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s, hk2⟩ := ihhi fuel ρ1 wu s2 hρ1s h2
    subst hρ2 hrw2
    cases r2 with
    | brk _ => exact absurd (hk2 rfl) (by simp [BOut.brk?])
    | val u =>
    rcases hcase2 with hcf | ⟨hl, hu⟩
    · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
    have hla : ∃ a, l.toInt? = some a ∧ l.toValue = .int a ∧ 0 ≤ a ∧
        a ≤ 2 ^ UScalarTy.Usize.numBits := by
      rcases hl with ⟨a, ha⟩ | ⟨t, a, ha⟩ <;> cases l <;>
        simp_all [BOut.toValue, BOut.Small, AVal.toValue, AVal.toInt?, AVal.Small] <;> omega
    have hub : ∃ b, u.toInt? = some b ∧ u.toValue = .int b ∧ b ≤ 2 ^ UScalarTy.Usize.numBits := by
      rcases hu with ⟨b, hb⟩ | ⟨t, b, hb⟩ <;> cases u <;>
        simp_all [BOut.toValue, BOut.Small, AVal.toValue, AVal.toInt?, AVal.Small]
    obtain ⟨a, hla, hla', ha0, -⟩ := hla
    obtain ⟨b, hub, hub', hb⟩ := hub
    rw [BOut.toValue, hla'] at h1
    rw [BOut.toValue, hub'] at h2
    rw [Hax.Ascent.denote'_forFold bi fuel h1 h2] at h
    rw [← Int.toNat_of_nonneg ha0] at h
    obtain ⟨o, ρ3, ho, how, hρ3, hos, hρ3s⟩ :=
      loopBS_complete ihbody _ a.toNat b fuel ρ2 w σ rfl hb hρ2s h
    refine ⟨.val (o.getD .unit), ρ3, ?_, how, hρ3, hos, hρ3s, fun _ => rfl⟩
    rw [Int.toNat_of_nonneg ha0] at ho
    have hb' : b ≤ 2 ^ System.Platform.numBits := hb
    simp [toRustMSB, hr1, hr2, hla, hub, ha0, hb', ho]
  | app _ ih =>
    intro fuel ρ w σ hρ h
    obtain ⟨vals, h1, hb⟩ := (Hax.Ascent.denote'_app_eq bi fuel).mp h
    obtain ⟨vs, ρ1, hvs, hvv, hρ1, hvsS, hρ1s⟩ := argsSB_complete ih fuel ρ vals σ hρ h1
    subst hvv
    obtain ⟨r, hr, hrw, hrs⟩ := hc _ vs w hvsS hb
    refine ⟨.val r, ρ1, ?_, hrw, hρ1, hrs, hρ1s, fun _ => rfl⟩
    simp only [toRustMSB, hvs]
    simp [hr]

/-! ## Function bodies -/

/-- The reading's environment binding the parameters `ps` to the values `vs`, a parameter
    repeated in the list taking the value of its first position (as `Range.paramEnv`). -/
def aParamEnv : List String → List AVal → AEnv
  | p :: ps, v :: vs => (aParamEnv ps vs).upd p v
  | _, _ => fun _ => none

/-- The encoding of the reading's parameter environment is the parameter environment of the
    encoded values. -/
theorem encEnv_aParamEnv : ∀ (ps : List String) (vs : List AVal),
    encEnv (aParamEnv ps vs) = _root_.Hax.Range.paramEnv ps (vs.map AVal.toValue)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, v :: vs => by
    rw [aParamEnv, encEnv_upd, encEnv_aParamEnv ps vs]
    rfl

/-- Small arguments give a small parameter environment. -/
theorem aParamEnv_small : ∀ (ps : List String) (vs : List AVal), (∀ v ∈ vs, v.Small) →
    EnvSmall (aParamEnv ps vs)
  | [], _, _ => fun _ _ h => nomatch h
  | _ :: _, [], _ => fun _ _ h => nomatch h
  | p :: ps, v :: vs, hv => by
    rw [aParamEnv]
    exact (aParamEnv_small ps vs fun w hw => hv w (List.mem_cons_of_mem _ hw)).upd p
      (hv v List.mem_cons_self)

/-- **The converse at a function body.** A value of the run of `e` from the parameter
    environment of small arguments is the encoding of the outcome of the reading from the
    reading's parameter environment. -/
theorem toRustMSB_paramEnv {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    (hc : AppComplete bi app) {k : Bool} {e : _root_.Hax.ImpExpr} (hf : RevFrag k e)
    {ps : List String} {vs : List AVal} (hvs : ∀ v ∈ vs, v.Small) {fuel : Nat}
    {w : _root_.Hax.Value} {σ : _root_.Hax.Env}
    (h : _root_.Hax.denote' bi fuel e (_root_.Hax.Range.paramEnv ps (vs.map AVal.toValue)) =
      (.val w, σ)) :
    ∃ r ρ', toRustMSB app e (aParamEnv ps vs) = .ok (r, ρ') ∧ r.toValue = w := by
  rw [← encEnv_aParamEnv] at h
  obtain ⟨r, ρ', h1, h2, -⟩ :=
    toRustMSB_complete hc hf fuel (aParamEnv ps vs) w σ (aParamEnv_small ps vs hvs) h
  exact ⟨r, ρ', h1, h2⟩

/-! ## From `f_noPanicOn` to a value of the reading -/

/-- **The reading returns the value of the unguarded run.** `hnp` is the statement of the
    theorem `f_noPanicOn` (or `f_noPanic`) of `--emit-monadic`: from every environment in the
    abstract environment `entry` without control-flow values, the run under the guarded table
    `Range.guardBi g bi` is the run under `bi`. When the reading of the calls is complete for
    the guarded table, a value of the run under `bi` from `encEnv ρ` in `entry` is the
    encoding of the outcome of the reading from `ρ`. -/
theorem toRustMSB_ok_of_noPanicOn {g : String → List _root_.Hax.Value → Bool}
    {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    {entry : _root_.Hax.Range.AEnv} {e : _root_.Hax.ImpExpr}
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g bi) fuel e env =
        _root_.Hax.denote' bi fuel e env)
    (hc : AppComplete (_root_.Hax.Range.guardBi g bi) app) {k : Bool} (hf : RevFrag k e)
    {ρ : AEnv} (hρ : EnvSmall ρ) (hΓ : _root_.Hax.Range.Sat entry (encEnv ρ))
    (hN : _root_.Hax.Env.NoControlFlow (encEnv ρ)) {fuel : Nat} {v : _root_.Hax.Value}
    {σ : _root_.Hax.Env} (hrun : _root_.Hax.denote' bi fuel e (encEnv ρ) = (.val v, σ)) :
    ∃ r ρ', toRustMSB app e ρ = .ok (r, ρ') ∧ r.toValue = v := by
  obtain ⟨r, ρ', h1, h2, -⟩ :=
    toRustMSB_complete hc hf fuel ρ v σ hρ ((hnp fuel _ hΓ hN).trans hrun)
  exact ⟨r, ρ', h1, h2⟩

/-- **The specification of the reading from `f_noPanicOn` and `f_pure`.** With `hnp` the
    statement of `f_noPanicOn` and `hF` a function correspondence of the body with the total
    surface `f_pure` from the environments `encEnv (entryOf a)`, the reading from
    `entryOf a` returns the encoding of `f_pure a` for every argument `a` with `G a` whose
    environment is small and lies in the precondition `entry`. -/
theorem toRustMSB_spec_of_noPanicOn {g : String → List _root_.Hax.Value → Bool}
    {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    {entry : _root_.Hax.Range.AEnv} {e : _root_.Hax.ImpExpr} {A β : Type}
    [Hax.Ascent.HaxEnc β] {G : A → Prop} {f_pure : A → β} {entryOf : A → AEnv}
    (hF : Hax.Ascent.FnCorres bi e (fun a => encEnv (entryOf a)) G f_pure)
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g bi) fuel e env =
        _root_.Hax.denote' bi fuel e env)
    (hc : AppComplete (_root_.Hax.Range.guardBi g bi) app) {k : Bool} (hf : RevFrag k e)
    (a : A) (hG : G a) (hρ : EnvSmall (entryOf a))
    (hΓ : _root_.Hax.Range.Sat entry (encEnv (entryOf a)))
    (hN : _root_.Hax.Env.NoControlFlow (encEnv (entryOf a))) :
    ∃ r ρ', toRustMSB app e (entryOf a) = .ok (r, ρ') ∧
      r.toValue = Hax.Ascent.HaxEnc.enc (f_pure a) := by
  obtain ⟨F, hF'⟩ := hF a hG
  have hrun : _root_.Hax.denote' bi F e (encEnv (entryOf a)) =
      (.val (Hax.Ascent.HaxEnc.enc (f_pure a)), (_root_.Hax.denote' bi F e
        (encEnv (entryOf a))).2) :=
    Prod.ext (hF' F (Nat.le_refl F)) rfl
  exact toRustMSB_ok_of_noPanicOn hnp hc hf hρ hΓ hN hrun

end CatCrypt.Hax.RangeRustM
