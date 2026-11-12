/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.RangeBridge
public import HaxAscent.RustSemantics.ToRustMSTotalCtl
public import HaxLean.Range.Heads
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Data.DTreeMap.Internal.Balancing

/-!
# The converse of the `RustM` reading on kinded literals

`toRustMSB_complete` (`HaxAscent/RustSemantics/RangeBridge.lean`) states that a value of the run
of a literal under a table `bi` is a value of the reading `toRustMSB app`, from small
environments and under a reading of the calls complete for `bi` on all small arguments
(`AppComplete`). This module states the converse under kinds (`Kd`, `ToRustMSTotalCtl`): the
environment binds each name of a context `Γ` to a value of its kind (`EnvTy H Γ`), and the
reading of the calls is complete for `bi` only on arguments of the kinds of a signature of a
list `sig`, returning a value of the result kind (`AppCompleteK`). The runtime call table
`appRt` satisfies `AppCompleteK` at the guarded table `guardBi g (runtimeBuiltins base)` for
every signature list that types it (`AppTyped`), in particular the checked arithmetic on the
word ranges `WI ty L U`.

The fragment is the kind judgment `KTy sig ki b Γ e k`: the rules of the kind checker
`kindOfL sig ki` (literals, variables, `let`, sequencing, ascriptions, calls at a signature,
conditionals, counted loops whose bounds have a static range) and `cfBreak e` with `e` of
kind `unit`, allowed where `b = true` (inside a loop body). Every kind `kindOfL` assigns is a
kind of the judgment (`kTy_of_kindOfL`).

The summaries of the range checker give kinds: an interval of naturals `[l, u]` of an
abstract value is the word range `WI ty l (u + 1)` at a width `ty` (`avKind`), and an
environment binding the names of a summary at these kinds satisfies the summary
(`sat_of_envTy`).

## Main definitions

* `OutK`, `AppCompleteK`, `KTy`, `CompleteK`
* `WK`, `WIH`, `avKind`, `avCtx`

## Main results

* `AppCompleteK.of_appTyped`, `AppCompleteK.guard`: completeness from typing and agreement,
  and its transfer to a guarded table.
* `toRustMSB_completeK`: the converse on the judgment.
* `toRustMSB_ok_of_noPanicOnK`, `toRustMSB_spec_of_noPanicOnK`: the converse and the
  specification of the reading from `f_noPanicOn` under kinds.
* `toRustMSB_spec_of_noPanicOn_appRt`: the specification at `appRt` and the guarded runtime
  table, from a signature list typing `appRt`.
* `kTy_of_kindOfL`: the judgment contains the kind checker.
* `sat_of_envTy`: range summaries from word-range kinds.
* `addBrkLit_completeK`: the converse at `appRt` on a literal with a loop, a break and a
  checked addition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RangeRustM

open CatCrypt CatCrypt.Hax CatCrypt.Hax.RustSemantics HaxAscent.RustSemantics Aeneas.Std
open Hax.Ascent (stateM_bind_apply bindCF_eq_val)

variable {κ : Type}

/-! ## Kinded outcomes and completeness of the calls -/

/-- A value of the outcome has kind `k`; a break, allowed only where `b = true`, carries the
    unit value. -/
def OutK (H : κ → AVal → Prop) (k : Kd κ) (b : Bool) : BOut → Prop
  | .val v => Kd.Has H k v
  | .brk v => b = true ∧ v = .unit

/-- At each signature `(f, ks, k)` of `sig` and on arguments of the kinds `ks`, wherever the
    table `bi` returns a value, the reading of the calls `app` returns a value of kind `k`
    encoding it. -/
def AppCompleteK (H : κ → AVal → Prop) (sig : List (String × List (Kd κ) × Kd κ))
    (bi : _root_.Hax.Builtins) (app : String → List AVal → RustM AVal) : Prop :=
  ∀ f ks k vs w, (f, ks, k) ∈ sig → List.Forall₂ (Kd.Has H) ks vs →
    bi f (AVal.toValues vs) = some w → ∃ r, app f vs = .ok r ∧ r.toValue = w ∧ Kd.Has H k r

/-- A reading of the calls typed by `sig` that agrees with `bi` is complete for `bi` on the
    signatures of `sig`. -/
theorem AppCompleteK.of_appTyped {H : κ → AVal → Prop}
    {sig : List (String × List (Kd κ) × Kd κ)} {bi : _root_.Hax.Builtins}
    {app : String → List AVal → RustM AVal} (ht : AppTyped H sig app) (hok : AppOk bi app) :
    AppCompleteK H sig bi app := by
  intro f ks k vs w hs hvs hw
  obtain ⟨r, hr, hk⟩ := ht f ks k vs hs hvs
  have h := hok f vs r hr
  rw [hw] at h
  exact ⟨r, hr, (Option.some.inj h).symm, hk⟩

/-- Completeness for `bi` gives completeness for the guarded table `guardBi g bi`, which
    returns a value only where `bi` does. -/
theorem AppCompleteK.guard {H : κ → AVal → Prop} {sig : List (String × List (Kd κ) × Kd κ)}
    {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    (h : AppCompleteK H sig bi app) (g : String → List _root_.Hax.Value → Bool) :
    AppCompleteK H sig (_root_.Hax.Range.guardBi g bi) app := by
  intro f ks k vs w hs hvs hw
  unfold _root_.Hax.Range.guardBi at hw
  split at hw
  · exact h f ks k vs w hs hvs hw
  · cases hw

/-! ## The kind judgment -/

/-- **The kinded fragment.** `KTy sig ki b Γ e k`: under the context `Γ`, `e` has kind `k`,
    with integer literals at the kind `ki`, calls at the signatures of `sig`, and `cfBreak`
    of a unit value only where `b = true`. A counted loop has bounds without breaks, each an
    integer literal or of an index kind (`boundRange`), and a body checked with breaks
    allowed and the index at the static kind `idx a c`. -/
inductive KTy [DecidableEq κ] (sig : List (String × List (Kd κ) × Kd κ)) (ki : Kd κ) :
    Bool → List (String × Kd κ) → _root_.Hax.ImpExpr → Kd κ → Prop where
  /-- An integer literal. -/
  | litInt {b : Bool} {Γ : List (String × Kd κ)} (n : Int) : KTy sig ki b Γ (.lit (.int n)) ki
  /-- A Boolean literal. -/
  | litBool {b : Bool} {Γ : List (String × Kd κ)} (c : Bool) :
      KTy sig ki b Γ (.lit (.bool c)) .bool
  /-- A variable of the context. -/
  | var {b : Bool} {Γ : List (String × Kd κ)} {x : String} {k : Kd κ} :
      Γ.lookup x = some k → KTy sig ki b Γ (.var x) k
  /-- The unit value. -/
  | unitVal {b : Bool} {Γ : List (String × Kd κ)} : KTy sig ki b Γ .unitVal .unit
  /-- A `let`, rebinding a name of the context only at its kind. -/
  | letBind {b : Bool} {Γ : List (String × Kd κ)} {x : String} {v e : _root_.Hax.ImpExpr}
      {kv k : Kd κ} :
      KTy sig ki b Γ v kv → fits Γ x kv = true → KTy sig ki b ((x, kv) :: Γ) e k →
      KTy sig ki b Γ (.letBind x v e) k
  /-- Sequencing. -/
  | seq {b : Bool} {Γ : List (String × Kd κ)} {a e : _root_.Hax.ImpExpr} {ka k : Kd κ} :
      KTy sig ki b Γ a ka → KTy sig ki b Γ e k → KTy sig ki b Γ (.seq a e) k
  /-- A type ascription. -/
  | typeAscription {b : Bool} {Γ : List (String × Kd κ)} {e : _root_.Hax.ImpExpr} {k : Kd κ}
      (ty : String) : KTy sig ki b Γ e k → KTy sig ki b Γ (.typeAscription e ty) k
  /-- A call at a signature of `sig`. -/
  | app {b : Bool} {Γ : List (String × Kd κ)} {f : String} {args : List _root_.Hax.ImpExpr}
      {ks : List (Kd κ)} {k : Kd κ} :
      (f, ks, k) ∈ sig → args.length = ks.length →
      (∀ p ∈ args.zip ks, KTy sig ki b Γ p.1 p.2) → KTy sig ki b Γ (.app f args) k
  /-- A conditional. -/
  | ifThenElse {b : Bool} {Γ : List (String × Kd κ)} {c t e : _root_.Hax.ImpExpr} {k : Kd κ} :
      KTy sig ki b Γ c .bool → KTy sig ki b Γ t k → KTy sig ki b Γ e k →
      KTy sig ki b Γ (.ifThenElse c t e) k
  /-- A `break` of a unit value, inside a loop body. -/
  | cfBreak {Γ : List (String × Kd κ)} {e : _root_.Hax.ImpExpr} {k : Kd κ} :
      KTy sig ki true Γ e .unit → KTy sig ki true Γ (.cfBreak e) k
  /-- A counted loop. -/
  | forFold {b : Bool} {Γ : List (String × Kd κ)} {var : String}
      {lo hi body : _root_.Hax.ImpExpr} {k1 k2 kb : Kd κ} {a a' b' c : Int} :
      KTy sig ki false Γ lo k1 → KTy sig ki false Γ hi k2 →
      boundRange lo k1 = some (a, a') → boundRange hi k2 = some (b', c) → 0 ≤ a →
      c ≤ 2 ^ 32 → fits Γ var (.idx a c) = true →
      KTy sig ki true ((var, .idx a c) :: Γ) body kb →
      KTy sig ki b Γ (.forFold var lo hi body) .unit

/-- The converse for one expression: a value of the run from `encEnv ρ`, with `ρ` binding
    each name of `Γ` to a value of its kind, is the encoding of an outcome of the reading
    from `ρ` of kind `k`, which ends in an environment again binding each name of `Γ` to a
    value of its kind and encoding the final one. -/
def CompleteK (H : κ → AVal → Prop) (bi : _root_.Hax.Builtins)
    (app : String → List AVal → RustM AVal) (b : Bool) (Γ : List (String × Kd κ))
    (e : _root_.Hax.ImpExpr) (k : Kd κ) : Prop :=
  ∀ fuel ρ w σ, EnvTy H Γ ρ → _root_.Hax.denote' bi fuel e (encEnv ρ) = (.val w, σ) →
    ∃ r ρ', toRustMSB app e ρ = .ok (r, ρ') ∧ r.toValue = w ∧ encEnv ρ' = σ ∧ OutK H k b r ∧
      EnvTy H Γ ρ'

/-! ## Argument lists, loop bounds and counted loops -/

/-- The converse for the arguments of a call, at a list of kinds. -/
theorem argsSB_completeK {H : κ → AVal → Prop} {bi : _root_.Hax.Builtins}
    {app : String → List AVal → RustM AVal} {b : Bool} {Γ : List (String × Kd κ)} :
    ∀ {es : List _root_.Hax.ImpExpr} {ks : List (Kd κ)}, es.length = ks.length →
    (∀ p ∈ es.zip ks, CompleteK H bi app b Γ p.1 p.2) →
    ∀ fuel ρ vals σ, EnvTy H Γ ρ →
      _root_.Hax.denoteArgs' bi fuel es (encEnv ρ) = (some vals, σ) →
      ∃ vs ρ', toRustMSB.argsSB app es ρ = .ok (vs, ρ') ∧ AVal.toValues vs = vals ∧
        encEnv ρ' = σ ∧ List.Forall₂ (Kd.Has H) ks vs ∧ EnvTy H Γ ρ'
  | [], [], _, _, fuel, ρ, vals, σ, hρ, h => by
    rw [Hax.Ascent.denoteArgs'_nil] at h
    cases h
    exact ⟨[], ρ, rfl, rfl, rfl, .nil, hρ⟩
  | e :: es, k :: ks, hlen, ih, fuel, ρ, vals, σ, hρ, h => by
    obtain ⟨w, s, ws, h1, hcf, h2, rfl⟩ := (Hax.Ascent.denoteArgs'_cons_eq bi fuel).mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrk, hρ1s⟩ := ih (e, k) List.mem_cons_self fuel ρ w s hρ h1
    cases r with
    | brk a =>
      subst hrw
      simp [BOut.toValue] at hcf
    | val a =>
      subst hρ1
      obtain ⟨vs, ρ2, hvs, hvv, hρ2, hvsK, hρ2s⟩ :=
        argsSB_completeK (es := es) (ks := ks) (by simpa using hlen)
          (fun p hp => ih p (List.mem_cons_of_mem _ hp)) fuel ρ1 ws σ hρ1s h2
      refine ⟨a :: vs, ρ2, ?_, ?_, hρ2, .cons hrk hvsK, hρ2s⟩
      · simp only [toRustMSB.argsSB, hr]
        simp [hvs]
      · simp only [AVal.toValues, hvv]
        simp only [BOut.toValue] at hrw
        rw [hrw]
  | [], _ :: _, hlen, _, _, _, _, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _, _, _, _, _ => by simp at hlen

/-- A value of kind `k` that the reading returns on a loop bound `e` with range `[L, U]`
    (`boundRange`) is an integer in `[L, U]` under `AVal.toInt?`, encoded as that integer. -/
theorem boundRange_toIntB {H : κ → AVal → Prop} {app : String → List AVal → RustM AVal}
    {e : _root_.Hax.ImpExpr} {k : Kd κ} {L U : Int} (hb : boundRange e k = some (L, U))
    {ρ ρ' : AEnv} {v : AVal} (he : toRustMSB app e ρ = .ok (.val v, ρ'))
    (hv : Kd.Has H k v) :
    ∃ a, v.toInt? = some a ∧ v.toValue = .int a ∧ L ≤ a ∧ a ≤ U := by
  unfold boundRange at hb
  split at hb
  · cases hb
    simp only [toRustMSB] at he
    cases he
    exact ⟨_, rfl, rfl, Int.le_refl _, Int.le_refl _⟩
  · split at hb
    case isFalse => cases hb
    cases hb
    obtain ⟨i, hl, hi, rfl⟩ := hv
    have hlt : i < 2 ^ UScalarTy.Usize.numBits := by
      have := two_pow_32_le_usize
      have h2 : ((2 ^ UScalarTy.Usize.numBits : Nat) : Int) = 2 ^ UScalarTy.Usize.numBits := by
        push_cast; rfl
      omega
    refine ⟨i, ?_, ctr_toValue hlt, hl, by omega⟩
    simp only [AVal.toInt?, ctr, UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · cases hb

/-- The converse for the counted loop under an invariant `Q` of the environments: a value of
    `denoteForLoop'` from index `i` to `b ≤ hi` is the value of `(b - i).toNat` steps of
    `loopBS` on the reading of the body, when the body is complete at each index of
    `[lo, hi)` from `Q`, keeps `Q`, and breaks only with the unit value. -/
theorem loopBS_completeQ {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    {var : String} {body : _root_.Hax.ImpExpr} {Q : AEnv → Prop} {lo hi : Nat}
    (hhi : (hi : Int) ≤ 2 ^ UScalarTy.Usize.numBits)
    (ih : ∀ i, lo ≤ i → i < hi → ∀ fuel ρ w σ, Q ρ →
      _root_.Hax.denote' bi fuel body (encEnv (ρ.upd var (ctr i))) = (.val w, σ) →
      ∃ r ρ', toRustMSB app body (ρ.upd var (ctr i)) = .ok (r, ρ') ∧ r.toValue = w ∧
        encEnv ρ' = σ ∧ (∀ v, r.brk? = some v → v = .unit) ∧ Q ρ') :
    ∀ (k i : Nat) (b : Int) (fuel : Nat) (ρ : AEnv) (w : _root_.Hax.Value)
      (σ : _root_.Hax.Env), lo ≤ i → (b - i).toNat = k → b ≤ hi → Q ρ →
      _root_.Hax.denoteForLoop' bi fuel var i b body (encEnv ρ) = (.val w, σ) →
      ∃ o ρ', loopBS (fun i ρ => toRustMSB app body (ρ.upd var (ctr i)) >>= fun s =>
          .ok (s.1.brk?, s.2)) k i ρ = .ok (o, ρ') ∧ (o.getD .unit).toValue = w ∧
        encEnv ρ' = σ ∧ o.getD .unit = .unit ∧ Q ρ'
  | 0, i, b, fuel, ρ, w, σ, _, hk, _, hρ, h => by
    rw [Hax.Ascent.denoteForLoop'_done bi fuel var body _ (by omega)] at h
    cases h
    exact ⟨none, ρ, rfl, rfl, rfl, rfl, hρ⟩
  | k + 1, i, b, fuel, ρ, w, σ, hli, hk, hb, hρ, h => by
    have hib : (i : Int) < b := by omega
    have hih : i < hi := by omega
    have hi : i < 2 ^ UScalarTy.Usize.numBits := by
      have : (i : Int) < 2 ^ UScalarTy.Usize.numBits := by omega
      exact_mod_cast this
    obtain ⟨hf, w1, s1, h1⟩ := denoteForLoop'_body_val hib h
    have henv : (encEnv ρ).extend var (.int i) = encEnv (ρ.upd var (ctr i)) := by
      rw [encEnv_upd, ctr_toValue hi]
    rw [henv] at h1
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrb, hρ1s⟩ := ih i hli hih fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rw [← henv] at h1
      rw [Hax.Ascent.denoteForLoop'_break bi fuel var hib hf h1] at h
      cases h
      refine ⟨some a, ρ1, ?_, rfl, rfl, hrb a rfl, hρ1s⟩
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
      obtain ⟨o, ρ2, ho, how, hρ2, hou, hρ2s⟩ :=
        loopBS_completeQ hhi ih k (i + 1) b (fuel - 1) ρ1 w σ (by omega) (by omega) hb hρ1s h'
      refine ⟨o, ρ2, ?_, how, hρ2, hou, hρ2s⟩
      simp only [loopBS, hr]
      exact ho

/-! ## The converse -/

/-- **The converse of `toRustMSB_sim` on the kinded fragment.** When every integer literal
    has the kind `ki` and the reading of the calls is complete for `bi` on the signatures of
    `sig`, a value of the run under `bi` of a literal of kind `k` from `encEnv ρ`, with `ρ`
    binding each name of `Γ` to a value of its kind, is the encoding of an outcome of kind
    `k` of the reading `toRustMSB app e ρ`. -/
theorem toRustMSB_completeK [DecidableEq κ] {H : κ → AVal → Prop} {sig : List (String × List (Kd κ) × Kd κ)}
    {ki : Kd κ} {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    (hc : AppCompleteK H sig bi app) (hlit : ∀ n, Kd.Has H ki (.int n)) {b : Bool}
    {Γ : List (String × Kd κ)} {e : _root_.Hax.ImpExpr} {k : Kd κ} (hk : KTy sig ki b Γ e k) :
    CompleteK H bi app b Γ e k := by
  induction hk with
  | litInt n =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_lit] at h
    cases h
    exact ⟨.val (.int n), ρ, rfl, rfl, rfl, hlit n, hρ⟩
  | litBool c =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_lit] at h
    cases h
    exact ⟨.val (.bool c), ρ, rfl, rfl, rfl, ⟨c, rfl⟩, hρ⟩
  | var hx =>
    intro fuel ρ w σ hρ h
    obtain ⟨hx', rfl⟩ := (Hax.Ascent.denote'_var_eq bi fuel).mp h
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hx'
    obtain ⟨v, hv, hvk⟩ := hρ _ _ hx
    rw [hv] at hv'
    cases hv'
    exact ⟨.val v', ρ, by simp only [toRustMSB, hv], rfl, rfl, hvk, hρ⟩
  | unitVal =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_unitVal] at h
    cases h
    exact ⟨.val .unit, ρ, rfl, rfl, rfl, rfl, hρ⟩
  | letBind _ hfit _ ihv ihb =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_letBind_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s⟩ := ihv fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · rw [BOut.toValue, ← encEnv_upd] at h2
        obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s⟩ :=
          ihb fuel (ρ1.upd _ a) w σ (hρ1s.upd _ hrs) h2
        exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2,
          hρ2s.of_cons hfit⟩
  | seq _ _ iha ihb =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_seq_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s⟩ := iha fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s⟩ := ihb fuel ρ1 w σ hρ1s h2
        exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2, hρ2s⟩
  | typeAscription ty _ ih =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_typeAscription] at h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s⟩ := ih fuel ρ w σ hρ h
    exact ⟨r, ρ1, by simp only [toRustMSB]; exact hr, hrw, hρ1, hrs, hρ1s⟩
  | app hs hlen _ ih =>
    intro fuel ρ w σ hρ h
    obtain ⟨vals, h1, hb⟩ := (Hax.Ascent.denote'_app_eq bi fuel).mp h
    obtain ⟨vs, ρ1, hvs, hvv, hρ1, hvsK, hρ1s⟩ := argsSB_completeK hlen ih fuel ρ vals σ hρ h1
    subst hvv
    obtain ⟨r, hr, hrw, hrk⟩ := hc _ _ _ vs w hs hvsK hb
    refine ⟨.val r, ρ1, ?_, hrw, hρ1, hrk, hρ1s⟩
    simp only [toRustMSB, hvs]
    simp [hr]
  | ifThenElse _ _ _ ihc iht ihe =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_ifThenElse_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s⟩ := ihc fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · obtain ⟨c, rfl⟩ := hrs
        simp only [BOut.toValue, AVal.toValue] at h2
        cases c with
        | true =>
          obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s⟩ := iht fuel ρ1 w σ hρ1s h2
          exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2, hρ2s⟩
        | false =>
          obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s⟩ := ihe fuel ρ1 w σ hρ1s h2
          exact ⟨r2, ρ2, by simp only [toRustMSB, hr]; exact hr2, hrw2, hρ2, hrs2, hρ2s⟩
  | cfBreak _ ih =>
    intro fuel ρ w σ hρ h
    rw [Hax.Ascent.denote'_cfBreak_bindCF] at h
    obtain ⟨w1, s1, h1, hcase⟩ := bindCF_eq_val.mp h
    obtain ⟨r, ρ1, hr, hrw, hρ1, hrs, hρ1s⟩ := ih fuel ρ w1 s1 hρ h1
    subst hρ1 hrw
    cases r with
    | brk a =>
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hcf, -⟩
      · exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, hrs, hρ1s⟩
      · simp [BOut.toValue] at hcf
    | val a =>
      rcases hcase with ⟨hcf, -⟩ | ⟨-, h2⟩
      · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
      · cases h2
        exact ⟨.brk a, ρ1, by simp only [toRustMSB, hr]; rfl, rfl, rfl, ⟨rfl, hrs⟩, hρ1s⟩
  | @forFold b Γ var lo hi body k1 k2 kb a a' b' c _ _ hb1 hb2 ha0 hc32 hfit _ ihlo ihhi
      ihbody =>
    intro fuel ρ w σ hρ h
    obtain ⟨wl, s1, h1, hcase⟩ := denote'_forFold_inv h
    obtain ⟨r1, ρ1, hr1, hrw1, hρ1, hrs1, hρ1s⟩ := ihlo fuel ρ wl s1 hρ h1
    subst hρ1 hrw1
    cases r1 with
    | brk _ => exact absurd hrs1.1 (by simp)
    | val l =>
    rcases hcase with hcf | ⟨wu, s2, h2, -⟩
    · simp [BOut.toValue, AVal.toValue_isControlFlow] at hcf
    obtain ⟨r2, ρ2, hr2, hrw2, hρ2, hrs2, hρ2s⟩ := ihhi fuel ρ1 wu s2 hρ1s h2
    subst hρ2 hrw2
    cases r2 with
    | brk _ => exact absurd hrs2.1 (by simp)
    | val u =>
    obtain ⟨x, hlx, hlx', hax, -⟩ := boundRange_toIntB hb1 hr1 hrs1
    obtain ⟨y, huy, huy', -, hyc⟩ := boundRange_toIntB hb2 hr2 hrs2
    rw [BOut.toValue, hlx'] at h1
    rw [BOut.toValue, huy'] at h2
    rw [Hax.Ascent.denote'_forFold bi fuel h1 h2] at h
    have hx0 : 0 ≤ x := Int.le_trans ha0 hax
    rw [← Int.toNat_of_nonneg hx0] at h
    have hcU : ((c.toNat : Nat) : Int) ≤ 2 ^ UScalarTy.Usize.numBits := by
      have := two_pow_32_le_usize
      omega
    obtain ⟨o, ρ3, ho, how, hρ3, hou, hρ3s⟩ :=
      loopBS_completeQ (Q := EnvTy H Γ) (lo := x.toNat) hcU
        (fun i hi1 hi2 fuel' ρ0 w1 s1' hρ0 hb0 => by
          obtain ⟨r, ρ', hr, hrw, hρ', hro, hρ's⟩ := ihbody fuel' (ρ0.upd var (ctr i)) w1 s1'
            (hρ0.upd var (k := .idx a c) ⟨i, by omega, by omega, rfl⟩) hb0
          refine ⟨r, ρ', hr, hrw, hρ', ?_, hρ's.of_cons hfit⟩
          intro v hv
          cases r with
          | val _ => cases hv
          | brk v' =>
            cases hv
            exact hro.2)
        _ x.toNat y fuel ρ2 w σ (Nat.le_refl _) rfl (by omega) hρ2s h
    refine ⟨.val (o.getD .unit), ρ3, ?_, how, hρ3, hou, hρ3s⟩
    rw [Int.toNat_of_nonneg hx0] at ho
    have hb' : y ≤ 2 ^ System.Platform.numBits :=
      Int.le_trans (Int.le_trans hyc hc32) two_pow_32_le_usize
    simp [toRustMSB, hr1, hr2, hlx, huy, hx0, hb', ho]

/-! ## From `f_noPanicOn` to a value of the reading -/

/-- **The reading returns the value of the unguarded run, under kinds.** `hnp` is the
    statement of `f_noPanicOn`. When the reading of the calls is complete for the guarded
    table on the signatures of `sig`, a value of the run under `bi` of a literal of the
    kinded fragment from `encEnv ρ`, with `ρ` binding each name of `Γ` to a value of its
    kind and `encEnv ρ` in `entry`, is the encoding of the outcome of the reading from
    `ρ`. -/
theorem toRustMSB_ok_of_noPanicOnK [DecidableEq κ] {g : String → List _root_.Hax.Value → Bool}
    {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    {entry : _root_.Hax.Range.AEnv} {e : _root_.Hax.ImpExpr} {H : κ → AVal → Prop}
    {sig : List (String × List (Kd κ) × Kd κ)} {ki : Kd κ} {b : Bool}
    {Γ : List (String × Kd κ)} {k : Kd κ}
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g bi) fuel e env =
        _root_.Hax.denote' bi fuel e env)
    (hc : AppCompleteK H sig (_root_.Hax.Range.guardBi g bi) app)
    (hlit : ∀ n, Kd.Has H ki (.int n)) (hk : KTy sig ki b Γ e k)
    {ρ : AEnv} (hρ : EnvTy H Γ ρ) (hΓ : _root_.Hax.Range.Sat entry (encEnv ρ))
    (hN : _root_.Hax.Env.NoControlFlow (encEnv ρ)) {fuel : Nat} {v : _root_.Hax.Value}
    {σ : _root_.Hax.Env} (hrun : _root_.Hax.denote' bi fuel e (encEnv ρ) = (.val v, σ)) :
    ∃ r ρ', toRustMSB app e ρ = .ok (r, ρ') ∧ r.toValue = v := by
  obtain ⟨r, ρ', h1, h2, -⟩ :=
    toRustMSB_completeK hc hlit hk fuel ρ v σ hρ ((hnp fuel _ hΓ hN).trans hrun)
  exact ⟨r, ρ', h1, h2⟩

/-- **The specification of the reading from `f_noPanicOn` and `f_pure`, under kinds.** With
    `hnp` the statement of `f_noPanicOn` and `hF` a function correspondence of the body with
    the total surface `f_pure`, the reading from `entryOf a` returns the encoding of
    `f_pure a` for every argument `a` with `G a` whose environment binds each name of `Γ` to
    a value of its kind and lies in the precondition `entry`. -/
theorem toRustMSB_spec_of_noPanicOnK [DecidableEq κ] {g : String → List _root_.Hax.Value → Bool}
    {bi : _root_.Hax.Builtins} {app : String → List AVal → RustM AVal}
    {entry : _root_.Hax.Range.AEnv} {e : _root_.Hax.ImpExpr} {A β : Type}
    [Hax.Ascent.HaxEnc β] {G : A → Prop} {f_pure : A → β} {entryOf : A → AEnv}
    {H : κ → AVal → Prop} {sig : List (String × List (Kd κ) × Kd κ)} {ki : Kd κ} {b : Bool}
    {Γ : List (String × Kd κ)} {k : Kd κ}
    (hF : Hax.Ascent.FnCorres bi e (fun a => encEnv (entryOf a)) G f_pure)
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g bi) fuel e env =
        _root_.Hax.denote' bi fuel e env)
    (hc : AppCompleteK H sig (_root_.Hax.Range.guardBi g bi) app)
    (hlit : ∀ n, Kd.Has H ki (.int n)) (hk : KTy sig ki b Γ e k)
    (a : A) (hG : G a) (hρ : EnvTy H Γ (entryOf a))
    (hΓ : _root_.Hax.Range.Sat entry (encEnv (entryOf a)))
    (hN : _root_.Hax.Env.NoControlFlow (encEnv (entryOf a))) :
    ∃ r ρ', toRustMSB app e (entryOf a) = .ok (r, ρ') ∧
      r.toValue = Hax.Ascent.HaxEnc.enc (f_pure a) := by
  obtain ⟨F, hF'⟩ := hF a hG
  have hrun : _root_.Hax.denote' bi F e (encEnv (entryOf a)) =
      (.val (Hax.Ascent.HaxEnc.enc (f_pure a)), (_root_.Hax.denote' bi F e
        (encEnv (entryOf a))).2) :=
    Prod.ext (hF' F (Nat.le_refl F)) rfl
  exact toRustMSB_ok_of_noPanicOnK hnp hc hlit hk hρ hΓ hN hrun

/-- **The specification at the runtime call table.** For the guarded runtime table
    `guardBi g (runtimeBuiltins base)` and a signature list `sig` typing `appRt`, the
    reading `toRustMSB appRt` of a literal of the kinded fragment returns the encoding of
    `f_pure a`, from `f_noPanicOn` and a function correspondence. -/
theorem toRustMSB_spec_of_noPanicOn_appRt [DecidableEq κ] {g : String → List _root_.Hax.Value → Bool}
    {base : _root_.Hax.Builtins} {entry : _root_.Hax.Range.AEnv} {e : _root_.Hax.ImpExpr}
    {A β : Type} [Hax.Ascent.HaxEnc β] {G : A → Prop} {f_pure : A → β} {entryOf : A → AEnv}
    {H : κ → AVal → Prop} {sig : List (String × List (Kd κ) × Kd κ)} {ki : Kd κ} {b : Bool}
    {Γ : List (String × Kd κ)} {k : Kd κ}
    (hF : Hax.Ascent.FnCorres (Hax.Ascent.runtimeBuiltins base) e
      (fun a => encEnv (entryOf a)) G f_pure)
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g (Hax.Ascent.runtimeBuiltins base)) fuel
        e env = _root_.Hax.denote' (Hax.Ascent.runtimeBuiltins base) fuel e env)
    (ht : AppTyped H sig appRt) (hlit : ∀ n, Kd.Has H ki (.int n)) (hk : KTy sig ki b Γ e k)
    (a : A) (hG : G a) (hρ : EnvTy H Γ (entryOf a))
    (hΓ : _root_.Hax.Range.Sat entry (encEnv (entryOf a)))
    (hN : _root_.Hax.Env.NoControlFlow (encEnv (entryOf a))) :
    ∃ r ρ', toRustMSB appRt e (entryOf a) = .ok (r, ρ') ∧
      r.toValue = Hax.Ascent.HaxEnc.enc (f_pure a) :=
  toRustMSB_spec_of_noPanicOnK hF hnp ((AppCompleteK.of_appTyped ht (appRt_ok base)).guard g)
    hlit hk a hG hρ hΓ hN

/-! ## The judgment contains the kind checker -/

/-- **Every kind `kindOfL` assigns is a kind of the judgment**, with or without breaks. -/
theorem kTy_of_kindOfL [DecidableEq κ] {sig : List (String × List (Kd κ) × Kd κ)}
    {ki : Kd κ} (Γ : List (String × Kd κ)) (e : _root_.Hax.ImpExpr) (k : Kd κ)
    (h : kindOfL sig ki Γ e = some k) (b : Bool) : KTy sig ki b Γ e k := by
  suffices HT : ∀ Γ e, ∀ k, kindOfL sig ki Γ e = some k → ∀ b, KTy sig ki b Γ e k from
    HT Γ e k h b
  apply kindOfL.induct_unfolding sig ki
    (fun Γ args r => ∀ ks, r = some ks → args.length = ks.length ∧
      ∀ b, ∀ p ∈ args.zip ks, KTy sig ki b Γ p.1 p.2)
    (fun Γ e r => ∀ k, r = some k → ∀ b, KTy sig ki b Γ e k)
  all_goals intros
  all_goals try (rename_i hk _; cases hk; done)
  all_goals try (rename_i hk; cases hk; done)
  case case1 => rename_i hk _; cases hk; exact .litInt _
  case case2 => rename_i hk _; cases hk; exact .litBool _
  case case3 => rename_i hk _; exact .var hk
  case case4 => rename_i hk _; cases hk; exact .unitVal
  case case5 Γ x v e kv hv hfit ihv ihe k hk b =>
    exact .letBind (ihv kv hv b) hfit (ihe k hk b)
  case case8 Γ a e ka ha iha ihe k hk b => exact .seq (iha ka ha b) (ihe k hk b)
  case case10 Γ e ty ih k hk b => exact .typeAscription ty (ih k hk b)
  case case11 Γ f args ks hks ih k hk b =>
    obtain ⟨hlen, hargs⟩ := ih ks hks
    exact .app (sigFind_mem hk) hlen (hargs b)
  case case13 Γ c t e k2 he hc ht ihc iht ihe k hk b =>
    cases hk
    exact .ifThenElse (ihc _ hc b) (iht _ ht b) (ihe _ he b)
  case case16 Γ var lo hi body k1 k2 hk2 hk1 a _ _ c hb2 hb1 hcond kb hbody ihlo ihhi ih
      k hk b =>
    cases hk
    obtain ⟨ha, hc, hfit⟩ := hcond
    exact .forFold (ihlo _ hk1 false) (ihhi _ hk2 false) hb1 hb2 ha hc hfit (ih _ hbody true)
  case case22 Γ ks hks =>
    cases hks
    exact ⟨rfl, fun _ p hp => by cases hp⟩
  case case23 Γ a as k ks' hks' hk iha ihas ks hks =>
    cases hks
    obtain ⟨hlen, hargs⟩ := ihas ks' hks'
    refine ⟨by simp [hlen], fun b p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact iha k hk b
    · exact hargs b p hp

/-! ## Range summaries as word-range kinds -/

/-- The word-range kinds: a width, a lower bound and a strict upper bound. -/
abbrev WK := UScalarTy × Nat × Nat

/-- The values of a word-range kind `(ty, L, U)`: the words `WI ty L U`. -/
abbrev WIH : WK → AVal → Prop := fun p => WI p.1 p.2.1 p.2.2

/-- The word-range kind at the width `ty` of an abstract value of the range checker: an
    interval `[l, u]` with `0 ≤ l`, or an index in `[lo, hi]` with `0 ≤ lo` and no facts,
    is the range `WI ty l (u + 1)`. -/
def avKind (ty : UScalarTy) : _root_.Hax.Range.AV → Option (Kd WK)
  | .num i => if 0 ≤ i.1 then some (.base (ty, i.1.toNat, (i.2 + 1).toNat)) else none
  | .idx lo (some hi) [] =>
    if 0 ≤ lo then some (.base (ty, lo.toNat, (hi + 1).toNat)) else none
  | _ => none

/-- A value of the word-range kind of an abstract value lies in the abstract value. -/
theorem avKind_mem {ty : UScalarTy} {a : _root_.Hax.Range.AV} {k : Kd WK}
    (h : avKind ty a = some k) {v : AVal} (hv : Kd.Has WIH k v) (env : _root_.Hax.Env) :
    a.Mem v.toValue ∧ a.RelIn env v.toValue := by
  unfold avKind at h
  split at h
  · split at h
    · cases h
      obtain ⟨x, rfl, h1, h2⟩ := hv
      simp only at h1 h2
      refine ⟨⟨(x.val : Int), rfl, by omega, by omega⟩, fun p hp => ?_⟩
      simp [_root_.Hax.Range.AV.rels] at hp
    · cases h
  · split at h
    · cases h
      obtain ⟨x, rfl, h1, h2⟩ := hv
      simp only at h1 h2
      refine ⟨⟨(x.val : Int), rfl, by omega, fun h hh => by cases hh; omega⟩, fun p hp => ?_⟩
      simp [_root_.Hax.Range.AV.rels] at hp
    · cases h
  · cases h

/-- The context of word-range kinds of a range summary, at the width `tyOf x` of each
    name `x`; `none` when an abstract value of the summary has no word-range kind. -/
def avCtx (tyOf : String → UScalarTy) : _root_.Hax.Range.AEnv → Option (List (String × Kd WK))
  | [] => some []
  | (x, a) :: rest =>
    match avKind (tyOf x) a, avCtx tyOf rest with
    | some k, some Γ => some ((x, k) :: Γ)
    | _, _ => none

/-- Each name of the summary has, in the context, the word-range kind of its abstract
    value. -/
theorem avCtx_lookup {tyOf : String → UScalarTy} :
    ∀ {entry : _root_.Hax.Range.AEnv} {Γ : List (String × Kd WK)}, avCtx tyOf entry = some Γ →
    ∀ {x : String} {a : _root_.Hax.Range.AV}, entry.lookup x = some a →
      ∃ k, Γ.lookup x = some k ∧ avKind (tyOf x) a = some k
  | [], _, _, _, _, hx => by cases hx
  | (y, a0) :: rest, Γ, h, x, a, hx => by
    simp only [avCtx] at h
    split at h
    · rename_i k Γ' hk hΓ'
      cases h
      by_cases hxy : x = y
      · subst hxy
        simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hx
        subst hx
        exact ⟨k, by simp, hk⟩
      · have hb : (x == y) = false := by simpa using hxy
        simp only [List.lookup_cons, hb] at hx ⊢
        exact avCtx_lookup hΓ' hx
    · cases h

/-- **Range summaries from word-range kinds.** An environment binding each name of the
    context of a summary to a value of its word-range kind satisfies the summary. -/
theorem sat_of_envTy {tyOf : String → UScalarTy} {entry : _root_.Hax.Range.AEnv}
    {Γ : List (String × Kd WK)} (h : avCtx tyOf entry = some Γ) {ρ : AEnv}
    (hρ : EnvTy WIH Γ ρ) : _root_.Hax.Range.Sat entry (encEnv ρ) := by
  intro x a hx
  obtain ⟨k, hk, hak⟩ := avCtx_lookup h hx
  obtain ⟨v, hv, hvk⟩ := hρ x k hk
  exact ⟨v.toValue, by simp [encEnv, hv], avKind_mem hak hvk _⟩

/-! ## An instance at the runtime call table -/

/-- The signature of the checked `u8` addition on `[0, 100)`. -/
def addBrkSig : List (String × List (Kd WK) × Kd WK) :=
  [("Add", [.base (.U8, 0, 100), .base (.U8, 0, 100)], .base (.U8, 0, 200))]

/-- The context binding `x` and `y` to `u8` words in `[0, 100)`. -/
def addBrkΓ : List (String × Kd WK) := [("x", .base (.U8, 0, 100)), ("y", .base (.U8, 0, 100))]

/-- A loop over `[0, 4)` whose body breaks, followed by the checked addition `x + y`. -/
def addBrkLit : _root_.Hax.ImpExpr :=
  .seq (.forFold "i" (.lit (.int 0)) (.lit (.int 4)) (.cfBreak .unitVal))
    (.app "Add" [.var "x", .var "y"])

/-- `appRt` is typed by `addBrkSig`. -/
theorem addBrkSig_appTyped : AppTyped WIH addBrkSig appRt :=
  appTyped_addI fun s hs => by
    simp only [addBrkSig, List.mem_singleton] at hs
    subst hs
    exact ⟨.U8, 0, 100, 0, 100, rfl, by decide⟩

/-- The kind of `addBrkLit`. -/
theorem addBrkLit_kTy : KTy addBrkSig .int false addBrkΓ addBrkLit (.base (.U8, 0, 200)) := by
  refine .seq (.forFold (kb := .unit) (.litInt 0) (.litInt 4) rfl rfl (by decide) (by decide)
    (by decide) (.cfBreak .unitVal)) (.app List.mem_cons_self rfl ?_)
  intro p hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl <;> exact .var rfl

/-- **The converse at `appRt`.** A value of the run of `addBrkLit` under the guarded runtime
    table, from an environment binding `x` and `y` to `u8` words in `[0, 100)`, is the
    encoding of a value of the reading `toRustMSB appRt`, a word in `[0, 200)`. -/
theorem addBrkLit_completeK (base : _root_.Hax.Builtins) :
    CompleteK WIH (_root_.Hax.Range.guardBi _root_.Hax.Range.rustGuard
      (Hax.Ascent.runtimeBuiltins base)) appRt false addBrkΓ addBrkLit (.base (.U8, 0, 200)) :=
  toRustMSB_completeK (ki := .int) ((AppCompleteK.of_appTyped addBrkSig_appTyped (appRt_ok base)).guard _)
    (fun n => ⟨n, rfl⟩) addBrkLit_kTy

end CatCrypt.Hax.RangeRustM
