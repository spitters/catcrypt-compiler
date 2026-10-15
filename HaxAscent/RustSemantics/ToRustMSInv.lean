/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMSSpec
public import HaxAscent.Ascent.TableCongr

/-!
# The state-passing reading under two readings of the calls that agree on invariant values

`toRustMS_congr` compares two readings of the calls that are the same function at every
called name. The comparison here depends on the values of the arguments. Let `Inv` be a
predicate on the values of the reading. `AppInv Inv ok app app'` states that at every name
accepted by `ok`, on arguments that satisfy `Inv`, a value `app` returns is the value `app'`
returns, and satisfies `Inv`. The reading of an expression whose calls are to accepted names,
from an environment whose values satisfy `Inv`, then returns under `app'` the value it
returns under `app`, and the returned value and environment satisfy `Inv`.

The predicate must hold of the values the reading itself makes (`ValInv`): the integer
literals, the Booleans, the unit value, a tuple of values that satisfy it, and the loop
index `ctr i`, and pass from a tuple to each of its components. The comparison is one-directional: a failure or a divergence of the reading
under `app` gives no statement on the reading under `app'`.

## Main definitions

* `ValInv`: a predicate on values that holds of the values the reading makes
* `EnvInv`: every value an environment binds satisfies the predicate
* `AppInv`: a value of the first reading of the calls on invariant arguments is the value of
  the second and is invariant

## Main results

* `loopS_ok_of_inv`: the comparison for the counted loop
* `toRustMS_ok_of_inv`: a value of the reading under `app` from an invariant environment is
  its value under `app'`, and the returned value and environment are invariant
* `toRustMS_triple_of_inv`: a total triple of the reading under `app` from an invariant
  environment is the triple of the reading under `app'`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Aeneas.Std.WP Std.Do Hax.Ascent

/-- A predicate on values that holds of the values the reading makes without a call: the
    integer literals, the Booleans, the unit value, a tuple of values that satisfy it, and
    the loop index; it holds of each component of a tuple that satisfies it. -/
structure ValInv (Inv : AVal → Prop) : Prop where
  /-- Every integer literal satisfies the predicate. -/
  int : ∀ n, Inv (.int n)
  /-- Every Boolean satisfies the predicate. -/
  bool : ∀ b, Inv (.bool b)
  /-- The unit value satisfies the predicate. -/
  unit : Inv .unit
  /-- A tuple of values that satisfy the predicate satisfies it. -/
  tup : ∀ vs, (∀ v ∈ vs, Inv v) → Inv (.tup vs)
  /-- Every component of a tuple that satisfies the predicate satisfies it. -/
  proj : ∀ vs v, Inv (.tup vs) → v ∈ vs → Inv v
  /-- Every loop index satisfies the predicate. -/
  ctr : ∀ i, Inv (ctr i)

/-- Every value the environment `ρ` binds satisfies `Inv`. -/
def EnvInv (Inv : AVal → Prop) (ρ : AEnv) : Prop :=
  ∀ x v, ρ x = some v → Inv v

/-- Binding a name to a value that satisfies `Inv` keeps `EnvInv`. -/
theorem EnvInv.upd {Inv : AVal → Prop} {ρ : AEnv} (h : EnvInv Inv ρ) (x : String) {v : AVal}
    (hv : Inv v) : EnvInv Inv (ρ.upd x v) := by
  intro y w hy
  simp only [AEnv.upd] at hy
  split at hy
  · cases hy
    exact hv
  · exact h y w hy

/-- At every name accepted by `ok`, on arguments that satisfy `Inv`, a value the reading
    `app` of the calls returns is the value `app'` returns, and it satisfies `Inv`. -/
def AppInv (Inv : AVal → Prop) (ok : String → Bool)
    (app app' : String → List AVal → RustM AVal) : Prop :=
  ∀ f, ok f = true → ∀ vs r, (∀ v ∈ vs, Inv v) → app f vs = .ok r →
    app' f vs = .ok r ∧ Inv r

/-- A program that returns `a`, followed by `f`, is `f a`. -/
theorem rustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    (RustM.ok a >>= f) = f a := rfl

/-- **The counted loop under two steps that agree on invariant environments.** If a value
    of `step` from an environment satisfying `EnvInv Inv` is the value of `step'` and
    satisfies `EnvInv Inv`, the same holds for `k` steps from the index `i`. -/
theorem loopS_ok_of_inv {Inv : AVal → Prop} {step step' : Nat → AEnv → RustM AEnv}
    (hstep : ∀ i ρ ρ', EnvInv Inv ρ → step i ρ = .ok ρ' →
      step' i ρ = .ok ρ' ∧ EnvInv Inv ρ') :
    ∀ (k i : Nat) (ρ ρ' : AEnv), EnvInv Inv ρ → loopS step k i ρ = .ok ρ' →
      loopS step' k i ρ = .ok ρ' ∧ EnvInv Inv ρ'
  | 0, _, ρ, ρ', hρ, h => by
    cases h
    exact ⟨rfl, hρ⟩
  | k + 1, i, ρ, ρ', hρ, h => by
    obtain ⟨ρ1, h1, h2⟩ := rustM_bind_ok h
    obtain ⟨h1', hρ1⟩ := hstep i ρ ρ1 hρ h1
    obtain ⟨h2', hρ'⟩ := loopS_ok_of_inv hstep k (i + 1) ρ1 ρ' hρ1 h2
    refine ⟨?_, hρ'⟩
    show (step' i ρ >>= loopS step' k (i + 1)) = _
    rw [h1', rustM_ok_bind]
    exact h2'

/-- **The reverse counted loop under two steps that agree on invariant environments.** The
    statement of `loopS_ok_of_inv` for `loopRevS`. -/
theorem loopRevS_ok_of_inv {Inv : AVal → Prop} {step step' : Nat → AEnv → RustM AEnv}
    (hstep : ∀ i ρ ρ', EnvInv Inv ρ → step i ρ = .ok ρ' →
      step' i ρ = .ok ρ' ∧ EnvInv Inv ρ') :
    ∀ (k i : Nat) (ρ ρ' : AEnv), EnvInv Inv ρ → loopRevS step k i ρ = .ok ρ' →
      loopRevS step' k i ρ = .ok ρ' ∧ EnvInv Inv ρ'
  | 0, _, ρ, ρ', hρ, h => by
    cases h
    exact ⟨rfl, hρ⟩
  | k + 1, i, ρ, ρ', hρ, h => by
    obtain ⟨ρ1, h1, h2⟩ := rustM_bind_ok h
    obtain ⟨h1', hρ1⟩ := hstep (i + k) ρ ρ1 hρ h1
    obtain ⟨h2', hρ'⟩ := loopRevS_ok_of_inv hstep k i ρ1 ρ' hρ1 h2
    refine ⟨?_, hρ'⟩
    show (step' (i + k) ρ >>= loopRevS step' k i) = _
    rw [h1', rustM_ok_bind]
    exact h2'

/-- The conclusion of `toRustMS_ok_of_inv` for a computation `r` that reads `e` from `ρ`. -/
private def InvOk (Inv : AVal → Prop) (ok : String → Bool)
    (app' : String → List AVal → RustM AVal) (e : Hax.ImpExpr) (ρ : AEnv)
    (r : RustM (AVal × AEnv)) : Prop :=
  ∀ res, callsOK ok e = true → EnvInv Inv ρ → r = .ok res →
    toRustMS app' e ρ = .ok res ∧ Inv res.1 ∧ EnvInv Inv res.2

/-- The conclusion of `toRustMS_ok_of_inv` for a computation `r` that reads the arguments
    `args` from `ρ`. -/
private def InvArgsOk (Inv : AVal → Prop) (ok : String → Bool)
    (app' : String → List AVal → RustM AVal) (args : List Hax.ImpExpr) (ρ : AEnv)
    (r : RustM (List AVal × AEnv)) : Prop :=
  ∀ res, callsOK.callsOKList ok args = true → EnvInv Inv ρ → r = .ok res →
    toRustMS.argsS app' args ρ = .ok res ∧ (∀ v ∈ res.1, Inv v) ∧ EnvInv Inv res.2

/-- **Congruence of the reading along invariant values.** Let `Inv` hold of the values the
    reading makes, let a value of `app` on arguments satisfying `Inv` be the value of `app'`
    and satisfy `Inv` at every name accepted by `ok`, and let every call of `e` be to such
    a name. If the reading of `e` under `app` returns `r` from an environment whose values
    satisfy `Inv`, the reading under `app'` returns `r`, and the value and the environment
    of `r` satisfy `Inv`. -/
theorem toRustMS_ok_of_inv {Inv : AVal → Prop} (hI : ValInv Inv)
    {app app' : String → List AVal → RustM AVal} {ok : String → Bool}
    (hag : AppInv Inv ok app app') (e : Hax.ImpExpr) (ρ : AEnv) :
    ∀ r, callsOK ok e = true → EnvInv Inv ρ → toRustMS app e ρ = .ok r →
      toRustMS app' e ρ = .ok r ∧ Inv r.1 ∧ EnvInv Inv r.2 := by
  suffices H : ∀ e ρ, InvOk Inv ok app' e ρ (toRustMS app e ρ) from H e ρ
  apply toRustMS.induct_unfolding app (InvArgsOk Inv ok app') (InvOk Inv ok app')
  all_goals intros
  case case1 n ρ =>
    intro r hc hρ h
    cases h
    exact ⟨by simp only [toRustMS], hI.int _, hρ⟩
  case case2 b ρ =>
    intro r hc hρ h
    cases h
    exact ⟨by simp only [toRustMS], hI.bool _, hρ⟩
  case case3 x ρ w hx =>
    intro r hc hρ h
    cases h
    exact ⟨by simp only [toRustMS, hx], hρ x w hx, hρ⟩
  case case4 =>
    intro r hc hρ h
    cases h
  case case5 x a b ρ ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, Bool.and_eq_true] at hc
    obtain ⟨p, hp, hb⟩ := rustM_bind_ok h
    obtain ⟨hp', hp1, hp2⟩ := ih2 p hc.1 hρ hp
    obtain ⟨hb', hr1, hr2⟩ := ih1 p r hc.2 (hp2.upd x hp1) hb
    refine ⟨?_, hr1, hr2⟩
    simp only [toRustMS, hp', rustM_ok_bind]
    exact hb'
  case case6 ρ =>
    intro r hc hρ h
    cases h
    exact ⟨by simp only [toRustMS], hI.unit, hρ⟩
  case case7 a b ρ ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, Bool.and_eq_true] at hc
    obtain ⟨p, hp, hb⟩ := rustM_bind_ok h
    obtain ⟨hp', -, hp2⟩ := ih2 p hc.1 hρ hp
    obtain ⟨hb', hr1, hr2⟩ := ih1 p r hc.2 hp2 hb
    refine ⟨?_, hr1, hr2⟩
    simp only [toRustMS, hp', rustM_ok_bind]
    exact hb'
  case case8 a s ρ ih1 =>
    intro r hc hρ h
    simp only [callsOK] at hc
    obtain ⟨h', hr1, hr2⟩ := ih1 r hc hρ h
    exact ⟨by simp only [toRustMS]; exact h', hr1, hr2⟩
  case case9 f a ρ ih1 =>
    intro r hc hρ h
    simp only [callsOK, callsOK.callsOKList, Bool.and_eq_true, Bool.and_true] at hc
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨v, hv, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨hp', hp1, hp2⟩ := ih1 p hc.2 hρ hp
    obtain ⟨hv', hv1⟩ := hag f hc.1 [p.1] v (by simpa using hp1) hv
    refine ⟨?_, hv1, hp2⟩
    simp only [toRustMS, hp', hv', rustM_ok_bind]
  case case10 f a b ρ ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, callsOK.callsOKList, Bool.and_eq_true, Bool.and_true] at hc
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨v, hv, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨hp', hp1, hp2⟩ := ih2 p hc.2.1 hρ hp
    obtain ⟨hq', hq1, hq2⟩ := ih1 p q hc.2.2 hp2 hq
    obtain ⟨hv', hv1⟩ := hag f hc.1 [p.1, q.1] v (by simp [hp1, hq1]) hv
    refine ⟨?_, hv1, hq2⟩
    simp only [toRustMS, hp', hq', hv', rustM_ok_bind]
  case case11 f a b c ρ ih3 ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, callsOK.callsOKList, Bool.and_eq_true, Bool.and_true] at hc
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨s, hs, h⟩ := rustM_bind_ok h
    obtain ⟨v, hv, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨hp', hp1, hp2⟩ := ih3 p hc.2.1 hρ hp
    obtain ⟨hq', hq1, hq2⟩ := ih2 p q hc.2.2.1 hp2 hq
    obtain ⟨hs', hs1, hs2⟩ := ih1 q s hc.2.2.2 hq2 hs
    obtain ⟨hv', hv1⟩ := hag f hc.1 [p.1, q.1, s.1] v (by simp [hp1, hq1, hs1]) hv
    refine ⟨?_, hv1, hs2⟩
    simp only [toRustMS, hp', hq', hs', hv', rustM_ok_bind]
  case case12 a b ρ ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, callsOK.callsOKList, Bool.and_eq_true, Bool.and_true] at hc
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨hp', hp1, hp2⟩ := ih2 p hc.1 hρ hp
    obtain ⟨hq', hq1, hq2⟩ := ih1 p q hc.2 hp2 hq
    refine ⟨?_, hI.tup _ (by simp [hp1, hq1]), hq2⟩
    simp only [toRustMS, hp', hq', rustM_ok_bind]
  case case13 a b c ρ ih3 ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, callsOK.callsOKList, Bool.and_eq_true, Bool.and_true] at hc
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨s, hs, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨hp', hp1, hp2⟩ := ih3 p hc.1 hρ hp
    obtain ⟨hq', hq1, hq2⟩ := ih2 p q hc.2.1 hp2 hq
    obtain ⟨hs', hs1, hs2⟩ := ih1 q s hc.2.2 hq2 hs
    refine ⟨?_, hI.tup _ (by simp [hp1, hq1, hs1]), hs2⟩
    simp only [toRustMS, hp', hq', hs', rustM_ok_bind]
  case case14 c t e ρ ih3 ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, Bool.and_eq_true] at hc
    obtain ⟨⟨cv, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨hp', -, hp2⟩ := ih3 (cv, ρ1) hc.1.1 hρ hp
    cases cv with
    | bool b =>
      cases b with
      | true =>
        obtain ⟨h', hr1, hr2⟩ := ih2 (.bool true, ρ1) r hc.1.2 hp2 h
        refine ⟨?_, hr1, hr2⟩
        simp only [toRustMS, hp', rustM_ok_bind]
        exact h'
      | false =>
        obtain ⟨h', hr1, hr2⟩ := ih1 (.bool false, ρ1) r hc.2 hp2 h
        refine ⟨?_, hr1, hr2⟩
        simp only [toRustMS, hp', rustM_ok_bind]
        exact h'
    | _ => cases h
  case case15 var lo hi body ρ ih3 ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, Bool.and_eq_true] at hc
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    obtain ⟨hp', -, hρ1⟩ := ih3 (l, ρ1) hc.1.1 hρ hp
    obtain ⟨hq', -, hρ2⟩ := ih2 (l, ρ1) (u, ρ2) hc.1.2 hρ1 hq
    cases hl : l.toInt? with
    | none => simp only [hl] at h; cases h
    | some a =>
      cases hu : u.toInt? with
      | none => simp only [hl, hu] at h; cases h
      | some b =>
        simp only [hl, hu] at h
        by_cases hab : 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits
        case neg => rw [if_neg hab] at h; cases h
        rw [if_pos hab] at h
        obtain ⟨ρ3, hloop, h⟩ := rustM_bind_ok h
        cases h
        have hstep : ∀ (i : Nat) (ρ ρ' : AEnv), EnvInv Inv ρ →
            (toRustMS app body (ρ.upd var (ctr i)) >>= fun s => RustM.ok s.2) = .ok ρ' →
            (toRustMS app' body (ρ.upd var (ctr i)) >>= fun s => RustM.ok s.2) = .ok ρ' ∧
              EnvInv Inv ρ' := by
          intro i ρ ρ'' hρi hs
          obtain ⟨s, hs', hfin⟩ := rustM_bind_ok hs
          cases hfin
          obtain ⟨h1, -, h2⟩ := ih1 i ρ s hc.2 (hρi.upd var (hI.ctr i)) hs'
          exact ⟨by rw [h1, rustM_ok_bind], h2⟩
        obtain ⟨hloop', hρ3⟩ := loopS_ok_of_inv hstep _ _ ρ2 ρ3 hρ2 hloop
        refine ⟨?_, hI.unit, hρ3⟩
        simp only [toRustMS, hp', hq', hl, hu, if_pos hab, hloop', rustM_ok_bind]
  case case16 var lo hi body ρ ih3 ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK, Bool.and_eq_true] at hc
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    obtain ⟨hp', -, hρ1⟩ := ih3 (l, ρ1) hc.1.1 hρ hp
    obtain ⟨hq', -, hρ2⟩ := ih2 (l, ρ1) (u, ρ2) hc.1.2 hρ1 hq
    cases hl : l.toInt? with
    | none => simp only [hl] at h; cases h
    | some a =>
      cases hu : u.toInt? with
      | none => simp only [hl, hu] at h; cases h
      | some b =>
        simp only [hl, hu] at h
        by_cases hab : 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits
        case neg => rw [if_neg hab] at h; cases h
        rw [if_pos hab] at h
        obtain ⟨ρ3, hloop, h⟩ := rustM_bind_ok h
        cases h
        have hstep : ∀ (i : Nat) (ρ ρ' : AEnv), EnvInv Inv ρ →
            (toRustMS app body (ρ.upd var (ctr i)) >>= fun s => RustM.ok s.2) = .ok ρ' →
            (toRustMS app' body (ρ.upd var (ctr i)) >>= fun s => RustM.ok s.2) = .ok ρ' ∧
              EnvInv Inv ρ' := by
          intro i ρ ρ'' hρi hs
          obtain ⟨s, hs', hfin⟩ := rustM_bind_ok hs
          cases hfin
          obtain ⟨h1, -, h2⟩ := ih1 i ρ s hc.2 (hρi.upd var (hI.ctr i)) hs'
          exact ⟨by rw [h1, rustM_ok_bind], h2⟩
        obtain ⟨hloop', hρ3⟩ := loopRevS_ok_of_inv hstep _ _ ρ2 ρ3 hρ2 hloop
        refine ⟨?_, hI.unit, hρ3⟩
        simp only [toRustMS, hp', hq', hl, hu, if_pos hab, hloop', rustM_ok_bind]
  case case17 e i ρ ih1 =>
    intro r hc hρ h
    simp only [callsOK] at hc
    obtain ⟨⟨t, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨hp', ht, hρ1⟩ := ih1 (t, ρ1) hc hρ hp
    cases t with
    | tup vs =>
      cases hvi : vs[i]? with
      | none => simp only [hvi] at h; cases h
      | some w =>
        simp only [hvi] at h
        cases h
        refine ⟨?_, hI.proj vs w ht (List.mem_of_getElem? hvi), hρ1⟩
        simp only [toRustMS, hp', rustM_ok_bind, hvi]
    | _ => cases h
  case case18 f args ρ _ _ _ ih =>
    intro r hc hρ h
    simp only [callsOK, Bool.and_eq_true] at hc
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨v, hv, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨hp', hp1, hp2⟩ := ih p hc.2 hρ hp
    obtain ⟨hv', hv1⟩ := hag f hc.1 p.1 v hp1 hv
    refine ⟨?_, hv1, hp2⟩
    rw [toRustMS_app_eq, hp', rustM_ok_bind, hv', rustM_ok_bind]
  case case19 =>
    intro r hc hρ h
    cases h
  case case20 ρ =>
    intro r hc hρ h
    cases h
    exact ⟨by simp only [toRustMS.argsS], by simp, hρ⟩
  case case21 a as ρ ih2 ih1 =>
    intro r hc hρ h
    simp only [callsOK.callsOKList, Bool.and_eq_true] at hc
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨hp', hp1, hp2⟩ := ih2 p hc.1 hρ hp
    obtain ⟨hq', hq1, hq2⟩ := ih1 p q hc.2 hp2 hq
    refine ⟨?_, ?_, hq2⟩
    · simp only [toRustMS.argsS, hp', hq', rustM_ok_bind]
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hp1
      · exact hq1 v hv

/-- **A total triple of the reading along invariant values.** Under the hypotheses of
    `toRustMS_ok_of_inv`, a total triple of the reading of `e` under `app` from an
    environment whose values satisfy `Inv` is the triple of the reading under `app'`. -/
theorem toRustMS_triple_of_inv {Inv : AVal → Prop} (hI : ValInv Inv)
    {app app' : String → List AVal → RustM AVal} {ok : String → Bool}
    (hag : AppInv Inv ok app app') {e : Hax.ImpExpr} (hc : callsOK ok e = true) {ρ : AEnv}
    (hρ : EnvInv Inv ρ) {Q : AVal × AEnv → Prop}
    (h : ⦃⌜True⌝⦄ toRustMS app e ρ ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃⌜True⌝⦄ toRustMS app' e ρ ⦃⇓ r => ⌜Q r⌝⦄ := by
  obtain ⟨r, hr, hQ⟩ := triple_iff_exists_ok.1 h
  exact (triple_iff_post_of_eq_ok (toRustMS_ok_of_inv hI hag e ρ r hc hρ hr).1).2 hQ

end CatCrypt.Hax.RustSemantics
