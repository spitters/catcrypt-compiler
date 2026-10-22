/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMS
public import HaxLean.AeneasBackendPrelude

/-!
# Counted loops with `break` in the state-passing `RustM` reading

`toRustMSB app e ρ` reads the literal `e` as `toRustMS` does and in addition reads the
control-flow constructor `.cfBreak e` of a loop body. A run returns an outcome `BOut`: a
value `.val v`, or a break `.brk v` carrying the value `v` of the `break`. A break passes
through `letBind`, `seq`, the condition of `ifThenElse`, a projection and a further
`.cfBreak`, as in `Hax.denote'`; an argument of a call or a tuple component that breaks
makes the reading fail. A counted loop `forFold` runs its body by `loopBS`, which stops at
the first break and returns its value, the value of the loop; a loop that runs to its end
returns the unit value. A downward loop `forFoldRev` is read by `loopRevS`, with a body
that does not break. Calls and tuples of every arity are read through `toRustMSB.argsSB`.

`BOut.toValue` encodes an outcome as a `Hax.Value`: a break by `.controlFlow true`, the
value of `Hax.denote'` for a `.cfBreak`.

## Main results

* `toRustMSB_sim`: when the reading returns `(r, ρ')` from `ρ`, the run of the literal from
  `encEnv ρ` returns `(.val r.toValue, encEnv ρ')` at every fuel from some fuel on.
* `toRustMSB_of_toRustMS`: on every literal that `toRustMS` reads, `toRustMSB` returns the
  same value as `.val`.
* `loopBS_sim`: the loop square of `loopBS` against `Hax.denoteForLoop'`.
* `loop_range_break`: the Aeneas `loop` over a `usize` range whose body returns
  `ControlFlow.done` at a break is `loopBS`.

## Main definitions

* `BOut`, `BOut.toValue`, `BOut.brk?`, `loopBS`, `toRustMSB`, `SimB`
-/

@[expose] public section

set_option autoImplicit false

namespace HaxAscent.RustSemantics

open CatCrypt CatCrypt.Hax CatCrypt.Hax.RustSemantics Aeneas.Std

/-! ## Outcomes -/

/-- The outcome of a run of the reading: a value, or a break with its value. -/
inductive BOut where
  /-- A value. -/
  | val (v : AVal)
  /-- A `break` carrying the value `v`. -/
  | brk (v : AVal)

/-- The runtime value encoding an outcome: a break by `.controlFlow true`. -/
def BOut.toValue : BOut → Hax.Value
  | .val v => v.toValue
  | .brk v => .controlFlow true v.toValue

/-- The value of a break, `none` at a value. -/
def BOut.brk? : BOut → Option AVal
  | .val _ => none
  | .brk v => some v

/-! ## The reading -/

/-- `step` run on at most `k` successive indices from `i`, stopping at the first step that
    returns `some b`, the value of the run; a run of all `k` steps returns `none`. -/
def loopBS {α β : Type} (step : Nat → α → RustM (Option β × α)) :
    Nat → Nat → α → RustM (Option β × α)
  | 0, _, a => .ok (none, a)
  | k + 1, i, a => step i a >>= fun p => match p.1 with
    | some b => .ok (some b, p.2)
    | none => loopBS step k (i + 1) p.2

/-- **The state-passing `RustM` reading of a literal with breaks.** -/
def toRustMSB (app : String → List AVal → RustM AVal) :
    Hax.ImpExpr → AEnv → RustM (BOut × AEnv)
  | .lit (.int n), ρ => .ok (.val (.int n), ρ)
  | .lit (.bool b), ρ => .ok (.val (.bool b), ρ)
  | .var x, ρ => match ρ x with
    | some v => .ok (.val v, ρ)
    | none => .fail .undef
  | .letBind x v b, ρ =>
    toRustMSB app v ρ >>= fun p => match p.1 with
      | .val w => toRustMSB app b (p.2.upd x w)
      | .brk w => .ok (.brk w, p.2)
  | .unitVal, ρ => .ok (.val .unit, ρ)
  | .seq a b, ρ =>
    toRustMSB app a ρ >>= fun p => match p.1 with
      | .val _ => toRustMSB app b p.2
      | .brk w => .ok (.brk w, p.2)
  | .typeAscription e _, ρ => toRustMSB app e ρ
  | .tuple es, ρ => toRustMSB.argsSB app es ρ >>= fun p => .ok (.val (.tup p.1), p.2)
  | .ifThenElse c t e, ρ =>
    toRustMSB app c ρ >>= fun p => match p.1 with
      | .val (.bool true) => toRustMSB app t p.2
      | .val (.bool false) => toRustMSB app e p.2
      | .brk w => .ok (.brk w, p.2)
      | _ => .fail .undef
  | .cfBreak e, ρ =>
    toRustMSB app e ρ >>= fun p => match p.1 with
      | .val w => .ok (.brk w, p.2)
      | .brk w => .ok (.brk w, p.2)
  | .forFold var lo hi body, ρ =>
    toRustMSB app lo ρ >>= fun p => toRustMSB app hi p.2 >>= fun q =>
      match p.1, q.1 with
      | .val l, .val u =>
        match l.toInt?, u.toInt? with
        | some a, some b =>
          if 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits then
            loopBS (fun i ρ => toRustMSB app body (ρ.upd var (ctr i)) >>= fun s =>
                .ok (s.1.brk?, s.2))
              (b - a).toNat a.toNat q.2 >>= fun r => .ok (.val (r.1.getD .unit), r.2)
          else .fail .undef
        | _, _ => .fail .undef
      | _, _ => .fail .undef
  | .forFoldRev var lo hi body, ρ =>
    toRustMSB app lo ρ >>= fun p => toRustMSB app hi p.2 >>= fun q =>
      match p.1, q.1 with
      | .val l, .val u =>
        match l.toInt?, u.toInt? with
        | some a, some b =>
          if 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits then
            loopRevS (fun i ρ => toRustMSB app body (ρ.upd var (ctr i)) >>= fun s =>
                match s.1 with
                | .val _ => .ok s.2
                | .brk _ => .fail .undef)
              (b - a).toNat a.toNat q.2 >>= fun ρ3 => .ok (.val .unit, ρ3)
          else .fail .undef
        | _, _ => .fail .undef
      | _, _ => .fail .undef
  | .proj e i, ρ =>
    toRustMSB app e ρ >>= fun p => match p.1 with
      | .val (.tup vs) => match vs[i]? with
        | some v => .ok (.val v, p.2)
        | none => .fail .undef
      | .brk w => .ok (.brk w, p.2)
      | _ => .fail .undef
  | .app f args, ρ =>
    toRustMSB.argsSB app args ρ >>= fun p => app f p.1 >>= fun r => .ok (.val r, p.2)
  | _, _ => .fail .undef
where
  /-- The arguments of a call or the components of a tuple read left to right: their
      values and the environment after the last of them. A break fails. -/
  argsSB (app : String → List AVal → RustM AVal) :
      List Hax.ImpExpr → AEnv → RustM (List AVal × AEnv)
    | [], ρ => .ok ([], ρ)
    | a :: as, ρ => toRustMSB app a ρ >>= fun p => match p.1 with
      | .val v => argsSB app as p.2 >>= fun q => .ok (v :: q.1, q.2)
      | .brk _ => .fail .undef

/-! ## Control-flow steps of `Hax.denote'` -/

section Steps

variable (bi : Hax.Builtins) (fuel : Nat)

theorem denote'_ifThenElse_cf {c t e : Hax.ImpExpr} {env s : Hax.Env} {b : Bool}
    {w : Hax.Value} (h : Hax.denote' bi fuel c env = (.val (.controlFlow b w), s)) :
    Hax.denote' bi fuel (.ifThenElse c t e) env = (.val (.controlFlow b w), s) := by
  simp only [Hax.denote', Hax.Ascent.stateM_bind_apply, h]
  rfl

theorem denote'_proj_cf {e : Hax.ImpExpr} {i : Nat} {env s : Hax.Env} {b : Bool}
    {w : Hax.Value} (h : Hax.denote' bi fuel e env = (.val (.controlFlow b w), s)) :
    Hax.denote' bi fuel (.proj e i) env = (.val (.controlFlow b w), s) := by
  simp only [Hax.denote', Hax.Ascent.stateM_bind_apply, h]
  rfl

theorem denote'_cfBreak_cf {e : Hax.ImpExpr} {env s : Hax.Env} {b : Bool}
    {w : Hax.Value} (h : Hax.denote' bi fuel e env = (.val (.controlFlow b w), s)) :
    Hax.denote' bi fuel (.cfBreak e) env = (.val (.controlFlow b w), s) := by
  simp only [Hax.denote', Hax.Ascent.stateM_bind_apply, h]
  rfl

end Steps

/-! ## Pasting -/

/-- The run of `e` from the encoding of `ρ` returns the encoding of the outcome `r` and
    ends in the encoding of `ρ'`, at every fuel from some fuel on. -/
def SimB (bi : Hax.Builtins) (e : Hax.ImpExpr) (ρ ρ' : AEnv) (r : BOut) : Prop :=
  ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
    Hax.denote' bi fuel e (encEnv ρ) = (.val r.toValue, encEnv ρ')

/-- Every outcome and environment that the computation `r` returns are simulated by the run
    of `e` from `ρ`. -/
def SimBOk (bi : Hax.Builtins) (e : Hax.ImpExpr) (ρ : AEnv) (r : RustM (BOut × AEnv)) :
    Prop :=
  ∀ o ρ', r = .ok (o, ρ') → SimB bi e ρ ρ' o

/-- **The loop square with breaks.** At most `k` steps of the reading from the index `i`,
    each a run of the body from the environment with the index bound, stopping at the first
    break, are the counted loop of the runtime from `i` to `b`; its value is the value of
    the break, or the unit value. -/
theorem loopBS_sim {bi : Hax.Builtins} {var : String} {body : Hax.ImpExpr}
    {step : Nat → AEnv → RustM (Option AVal × AEnv)}
    (hstep : ∀ i ρ o ρ', step i ρ = .ok (o, ρ') →
      ∃ r : BOut, r.brk? = o ∧ SimB bi body (ρ.upd var (ctr i)) ρ' r) :
    ∀ (k i : Nat) (b : Int) (ρ : AEnv) (o : Option AVal) (ρ' : AEnv), (b - i).toNat = k →
      b ≤ 2 ^ UScalarTy.Usize.numBits → loopBS step k i ρ = .ok (o, ρ') →
      ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
        Hax.denoteForLoop' bi fuel var i b body (encEnv ρ) =
          (.val (o.getD .unit).toValue, encEnv ρ')
  | 0, i, b, ρ, o, ρ', hk, _, h => by
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denoteForLoop'_done bi fuel var body _ (by omega)⟩
  | k + 1, i, b, ρ, o, ρ', hk, hb, h => by
    obtain ⟨⟨o1, ρ1⟩, h1, h2⟩ := rustM_bind_ok h
    obtain ⟨r, hr, F1, hF1⟩ := hstep i ρ o1 ρ1 h1
    have hi' : (i : Int) < 2 ^ UScalarTy.Usize.numBits := by omega
    have hi : i < 2 ^ UScalarTy.Usize.numBits := by exact_mod_cast hi'
    cases o1 with
    | some v =>
      cases h2
      cases r with
      | val _ => cases hr
      | brk w =>
        cases hr
        refine ⟨max F1 1, fun fuel hf => ?_⟩
        have hbody := hF1 fuel (by omega)
        rw [encEnv_upd, ctr_toValue hi] at hbody
        exact Hax.Ascent.denoteForLoop'_break bi fuel var (by omega) (by omega) hbody
    | none =>
      cases r with
      | brk _ => cases hr
      | val w =>
        obtain ⟨F2, hF2⟩ := loopBS_sim hstep k (i + 1) b ρ1 o ρ' (by omega) hb h2
        refine ⟨max F1 (F2 + 1), fun fuel hf => ?_⟩
        have hbody := hF1 fuel (by omega)
        rw [encEnv_upd, ctr_toValue hi] at hbody
        rw [Hax.Ascent.denoteForLoop'_next bi fuel var (by omega) (by omega) hbody
          (AVal.toValue_ne_break w)]
        have h3 := hF2 (fuel - 1) (by omega)
        rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by push_cast; rfl] at h3
        exact h3

theorem toRustMSB_sim {bi : Hax.Builtins} {app : String → List AVal → RustM AVal}
    (hok : AppOk bi app) {e : Hax.ImpExpr} {ρ : AEnv} {r : BOut} {ρ' : AEnv}
    (h : toRustMSB app e ρ = .ok (r, ρ')) :
    ∃ N, ∀ fuel, N ≤ fuel → Hax.denote' bi fuel e (encEnv ρ) = (.val r.toValue, encEnv ρ') := by
  suffices H : ∀ e ρ, SimBOk bi e ρ (toRustMSB app e ρ) from H e ρ r ρ' h
  clear h
  apply toRustMSB.induct_unfolding app (SimArgsOk bi) (SimBOk bi)
  all_goals intros
  case case1 n ρ =>
    intro o ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denote'_lit bi fuel _ _⟩
  case case2 b ρ =>
    intro o ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denote'_lit bi fuel _ _⟩
  case case3 x ρ w hx =>
    intro o ρ' h
    cases h
    refine ⟨0, fun fuel _ => Hax.Ascent.denote'_var bi fuel ?_⟩
    show (ρ x).map AVal.toValue = _
    rw [hx]
    rfl
  case case4 =>
    intro o ρ' h
    cases h
  case case5 x a b ρ ih2 ih1 =>
    intro o ρ' h
    obtain ⟨⟨r1, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih2 r1 ρ1 hp
    cases r1 with
    | val w =>
      obtain ⟨F2, h2⟩ := ih1 (.val w, ρ1) w o ρ' h
      refine ⟨max F1 F2, fun fuel hf => ?_⟩
      rw [Hax.Ascent.denote'_letBind bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _),
        BOut.toValue, ← encEnv_upd]
      exact h2 fuel (by omega)
    | brk w =>
      cases h
      exact ⟨F1, fun fuel hf => Hax.Ascent.denote'_letBind_cf bi fuel (h1 fuel hf)⟩
  case case6 ρ =>
    intro o ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denote'_unitVal bi fuel _⟩
  case case7 a b ρ ih2 ih1 =>
    intro o ρ' h
    obtain ⟨⟨r1, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih2 r1 ρ1 hp
    cases r1 with
    | val w =>
      obtain ⟨F2, h2⟩ := ih1 (.val w, ρ1) o ρ' h
      refine ⟨max F1 F2, fun fuel hf => ?_⟩
      rw [Hax.Ascent.denote'_seq bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _)]
      exact h2 fuel (by omega)
    | brk w =>
      cases h
      exact ⟨F1, fun fuel hf => Hax.Ascent.denote'_seq_cf bi fuel (h1 fuel hf)⟩
  case case8 a s ρ ih1 =>
    intro o ρ' h
    obtain ⟨F1, h1⟩ := ih1 o ρ' h
    exact ⟨F1, fun fuel hf => by
      rw [Hax.Ascent.denote'_typeAscription]; exact h1 fuel hf⟩
  case case9 es ρ ih1 =>
    intro o ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F, hF⟩ := ih1 p.1 p.2 hp
    exact ⟨F, fun fuel hf => Hax.Ascent.denote'_tuple bi fuel (hF fuel hf)⟩
  case case10 c t e ρ ih3 ih2 ih1 =>
    intro o ρ' h
    obtain ⟨⟨cv, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih3 cv ρ1 hp
    cases cv with
    | val cv =>
      cases cv with
      | bool b =>
        cases b with
        | true =>
          obtain ⟨F2, h2⟩ := ih2 (.val (.bool true), ρ1) o ρ' h
          refine ⟨max F1 F2, fun fuel hf => ?_⟩
          rw [Hax.Ascent.denote'_ifThenElse bi fuel (h1 fuel (by omega))]
          exact h2 fuel (by omega)
        | false =>
          obtain ⟨F2, h2⟩ := ih1 (.val (.bool false), ρ1) o ρ' h
          refine ⟨max F1 F2, fun fuel hf => ?_⟩
          rw [Hax.Ascent.denote'_ifThenElse bi fuel (h1 fuel (by omega))]
          exact h2 fuel (by omega)
      | _ => cases h
    | brk w =>
      cases h
      exact ⟨F1, fun fuel hf => denote'_ifThenElse_cf bi fuel (h1 fuel hf)⟩
  case case11 e ρ ih1 =>
    intro o ρ' h
    obtain ⟨⟨r1, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih1 r1 ρ1 hp
    cases r1 with
    | val w =>
      cases h
      exact ⟨F1, fun fuel hf =>
        Hax.Ascent.denote'_cfBreak bi fuel (h1 fuel hf) (AVal.toValue_isControlFlow _)⟩
    | brk w =>
      cases h
      exact ⟨F1, fun fuel hf => denote'_cfBreak_cf bi fuel (h1 fuel hf)⟩
  case case12 var lo hi body ρ ih3 ih2 ih1 =>
    intro o ρ' h
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih3 l ρ1 hp
    obtain ⟨F2, h2⟩ := ih2 (l, ρ1) u ρ2 hq
    cases l with
    | brk _ => cases h
    | val l =>
    cases u with
    | brk _ => cases h
    | val u =>
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
        obtain ⟨⟨o3, ρ3⟩, hloop, h⟩ := rustM_bind_ok h
        cases h
        have hstep : ∀ (i : Nat) (ρ : AEnv) (o : Option AVal) (ρ'' : AEnv),
            (toRustMSB app body (ρ.upd var (ctr i)) >>= fun s => RustM.ok (s.1.brk?, s.2)) =
              .ok (o, ρ'') → ∃ r : BOut, r.brk? = o ∧ SimB bi body (ρ.upd var (ctr i)) ρ'' r := by
          intro i ρ o ρ'' hs
          obtain ⟨s, hs', hfin⟩ := rustM_bind_ok hs
          cases hfin
          exact ⟨s.1, rfl, ih1 i ρ s.1 s.2 hs'⟩
        obtain ⟨F3, h3⟩ := loopBS_sim hstep (b - a).toNat a.toNat b ρ2 o3 ρ3
          (by rw [Int.toNat_of_nonneg hab.1]) hab.2 hloop
        refine ⟨max F1 (max F2 F3), fun fuel hf => ?_⟩
        have hlo := h1 fuel (by omega)
        have hhi := h2 fuel (by omega)
        rw [BOut.toValue, AVal.toValue_of_toInt? hl] at hlo
        rw [BOut.toValue, AVal.toValue_of_toInt? hu] at hhi
        rw [Hax.Ascent.denote'_forFold bi fuel hlo hhi]
        have h4 := h3 fuel (by omega)
        rw [Int.toNat_of_nonneg hab.1] at h4
        exact h4
  case case13 var lo hi body ρ ih3 ih2 ih1 =>
    intro o ρ' h
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih3 l ρ1 hp
    obtain ⟨F2, h2⟩ := ih2 (l, ρ1) u ρ2 hq
    cases l with
    | brk _ => cases h
    | val l =>
    cases u with
    | brk _ => cases h
    | val u =>
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
        have hstep : ∀ (i : Nat) (ρ ρ'' : AEnv),
            (toRustMSB app body (ρ.upd var (ctr i)) >>= fun s => match s.1 with
              | .val _ => RustM.ok s.2
              | .brk _ => RustM.fail .undef) = .ok ρ'' →
              ∃ w, Sim bi body (ρ.upd var (ctr i)) ρ'' w := by
          intro i ρ ρ'' hs
          obtain ⟨⟨r, ρs⟩, hs', hfin⟩ := rustM_bind_ok hs
          cases r with
          | val w =>
            cases hfin
            exact ⟨w, ih1 i ρ (.val w) ρs hs'⟩
          | brk _ => cases hfin
        obtain ⟨F3, h3⟩ := loopRevS_sim hstep (b - a).toNat a.toNat b ρ2 _
          (by rw [Int.toNat_of_nonneg hab.1]) hab.2 hloop
        refine ⟨max F1 (max F2 F3), fun fuel hf => ?_⟩
        have hlo := h1 fuel (by omega)
        have hhi := h2 fuel (by omega)
        rw [BOut.toValue, AVal.toValue_of_toInt? hl] at hlo
        rw [BOut.toValue, AVal.toValue_of_toInt? hu] at hhi
        rw [denote'_forFoldRev bi fuel hlo hhi]
        have h4 := h3 fuel (by omega)
        rw [Int.toNat_of_nonneg hab.1] at h4
        exact h4
  case case14 e i ρ ih1 =>
    intro o ρ' h
    obtain ⟨⟨t, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih1 t ρ1 hp
    cases t with
    | val t =>
      cases t with
      | tup vs =>
        cases hvi : vs[i]? with
        | none => simp only [hvi] at h; cases h
        | some w =>
          simp only [hvi] at h
          cases h
          refine ⟨F1, fun fuel hf => ?_⟩
          refine Hax.Ascent.denote'_proj bi fuel (h1 fuel hf) (AVal.toValue_isControlFlow _) ?_
          simp only [BOut.toValue, AVal.toValue, Hax.Value.projIdx, AVal.toValues_eq_map,
            List.getElem?_map,
            hvi, Option.map_some]
      | _ => cases h
    | brk w =>
      cases h
      exact ⟨F1, fun fuel hf => denote'_proj_cf bi fuel (h1 fuel hf)⟩
  case case15 f args ρ ih =>
    intro o ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F, hF⟩ := ih p.1 p.2 hp
    exact ⟨F, fun fuel hf => Hax.Ascent.denote'_app bi fuel (hF fuel hf) (hok f p.1 _ hr)⟩
  case case16 =>
    intro o ρ' h
    cases h
  case case17 ρ =>
    intro vs ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denoteArgs'_nil bi fuel _⟩
  case case18 a as ρ ih2 ih1 =>
    intro vs ρ' h
    obtain ⟨⟨r1, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    cases r1 with
    | brk _ => cases h
    | val v =>
      obtain ⟨q, hq, h⟩ := rustM_bind_ok h
      cases h
      obtain ⟨F1, h1⟩ := ih2 (.val v) ρ1 hp
      obtain ⟨F2, h2⟩ := ih1 (.val v, ρ1) q.1 q.2 hq
      exact ⟨max F1 F2, fun fuel hf => Hax.Ascent.denoteArgs'_cons bi fuel (h1 fuel (by omega))
        (AVal.toValue_isControlFlow _) (h2 fuel (by omega))⟩

/-! ## Agreement with `toRustMS` -/

theorem loopBS_of_loopS {step : Nat → AEnv → RustM AEnv}
    {step' : Nat → AEnv → RustM (Option AVal × AEnv)}
    (hs : ∀ i ρ ρ', step i ρ = .ok ρ' → step' i ρ = .ok (none, ρ')) :
    ∀ (k i : Nat) (ρ ρ' : AEnv), loopS step k i ρ = .ok ρ' →
      loopBS step' k i ρ = .ok (none, ρ')
  | 0, _, _, _, h => by cases h; rfl
  | k + 1, i, ρ, ρ', h => by
    obtain ⟨ρ1, h1, h2⟩ := rustM_bind_ok h
    simp only [loopBS, hs i ρ ρ1 h1, bind_tc_ok]
    exact loopBS_of_loopS hs k (i + 1) ρ1 ρ' h2

theorem loopRevS_of_loopRevS {step step' : Nat → AEnv → RustM AEnv}
    (hs : ∀ i ρ ρ', step i ρ = .ok ρ' → step' i ρ = .ok ρ') :
    ∀ (k i : Nat) (ρ ρ' : AEnv), loopRevS step k i ρ = .ok ρ' → loopRevS step' k i ρ = .ok ρ'
  | 0, _, _, _, h => h
  | k + 1, i, ρ, ρ', h => by
    obtain ⟨ρ1, h1, h2⟩ := rustM_bind_ok h
    simp only [loopRevS, hs (i + k) ρ ρ1 h1, bind_tc_ok]
    exact loopRevS_of_loopRevS hs k i ρ1 ρ' h2

/-- Every value and environment that `r` returns, `toRustMSB` returns on `e` from `ρ`. -/
private def AgreeB (app : String → List AVal → RustM AVal) (e : Hax.ImpExpr) (ρ : AEnv)
    (r : RustM (AVal × AEnv)) : Prop :=
  ∀ v ρ', r = .ok (v, ρ') → toRustMSB app e ρ = .ok (.val v, ρ')

/-- Every list of values and environment that `r` returns, `toRustMSB.argsSB` returns on
    `args` from `ρ`. -/
private def AgreeArgsB (app : String → List AVal → RustM AVal) (args : List Hax.ImpExpr)
    (ρ : AEnv) (r : RustM (List AVal × AEnv)) : Prop :=
  ∀ vs ρ', r = .ok (vs, ρ') → toRustMSB.argsSB app args ρ = .ok (vs, ρ')

theorem toRustMSB_of_toRustMS {app : String → List AVal → RustM AVal} {e : Hax.ImpExpr}
    {ρ : AEnv} {v : AVal} {ρ' : AEnv} (h : toRustMS app e ρ = .ok (v, ρ')) :
    toRustMSB app e ρ = .ok (.val v, ρ') := by
  suffices H : ∀ e ρ, AgreeB app e ρ (toRustMS app e ρ) from H e ρ v ρ' h
  clear h
  apply toRustMS.induct_unfolding app (AgreeArgsB app) (AgreeB app)
  all_goals intros
  case case1 n ρ =>
    intro v ρ' h
    cases h
    simp only [toRustMSB]
  case case2 b ρ =>
    intro v ρ' h
    cases h
    simp only [toRustMSB]
  case case3 x ρ w hx =>
    intro v ρ' h
    cases h
    simp only [toRustMSB, hx]
  case case4 =>
    intro v ρ' h
    cases h
  case case5 x a b ρ ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, hb⟩ := rustM_bind_ok h
    simp only [toRustMSB, ih2 p.1 p.2 hp, bind_tc_ok]
    exact ih1 p v ρ' hb
  case case6 ρ =>
    intro v ρ' h
    cases h
    simp only [toRustMSB]
  case case7 a b ρ ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, hb⟩ := rustM_bind_ok h
    simp only [toRustMSB, ih2 p.1 p.2 hp, bind_tc_ok]
    exact ih1 p v ρ' hb
  case case8 a s ρ ih1 =>
    intro v ρ' h
    simp only [toRustMSB]
    exact ih1 v ρ' h
  case case9 f a ρ ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    simp only [toRustMSB, toRustMSB.argsSB, ih1 p.1 p.2 hp, bind_tc_ok, hr]
  case case10 f a b ρ ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    simp only [toRustMSB, toRustMSB.argsSB, ih2 p.1 p.2 hp, ih1 p q.1 q.2 hq, bind_tc_ok, hr]
  case case11 f a b c ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨s, hs, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    simp only [toRustMSB, toRustMSB.argsSB, ih3 p.1 p.2 hp, ih2 p q.1 q.2 hq, ih1 q s.1 s.2 hs,
      bind_tc_ok, hr]
  case case12 es ρ ih =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    cases h
    simp only [toRustMSB, ih p.1 p.2 hp, bind_tc_ok]
  case case13 c t e ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨⟨cv, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    have hc := ih3 cv ρ1 hp
    cases cv with
    | bool b =>
      cases b with
      | true =>
        simp only [toRustMSB, hc, bind_tc_ok]
        exact ih2 (.bool true, ρ1) v ρ' h
      | false =>
        simp only [toRustMSB, hc, bind_tc_ok]
        exact ih1 (.bool false, ρ1) v ρ' h
    | _ => cases h
  case case14 var lo hi body ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    simp only [toRustMSB, ih3 l ρ1 hp, ih2 (l, ρ1) u ρ2 hq, bind_tc_ok]
    cases hl : l.toInt? with
    | none => simp only [hl] at h; cases h
    | some a =>
      cases hu : u.toInt? with
      | none => simp only [hl, hu] at h; cases h
      | some b =>
        simp only [hl, hu] at h ⊢
        by_cases hab : 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits
        case neg => rw [if_neg hab] at h; cases h
        rw [if_pos hab] at h ⊢
        obtain ⟨ρ3, hloop, h⟩ := rustM_bind_ok h
        cases h
        rw [loopBS_of_loopS (step' := fun i ρ => toRustMSB app body (ρ.upd var (ctr i)) >>=
            fun s => .ok (s.1.brk?, s.2)) (fun i ρ ρ'' hs => by
              obtain ⟨s, hs', hfin⟩ := rustM_bind_ok hs
              cases hfin
              simp only [ih1 i ρ s.1 s.2 hs', bind_tc_ok, BOut.brk?]) _ _ _ _ hloop]
        rfl
  case case15 var lo hi body ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    simp only [toRustMSB, ih3 l ρ1 hp, ih2 (l, ρ1) u ρ2 hq, bind_tc_ok]
    cases hl : l.toInt? with
    | none => simp only [hl] at h; cases h
    | some a =>
      cases hu : u.toInt? with
      | none => simp only [hl, hu] at h; cases h
      | some b =>
        simp only [hl, hu] at h ⊢
        by_cases hab : 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits
        case neg => rw [if_neg hab] at h; cases h
        rw [if_pos hab] at h ⊢
        obtain ⟨ρ3, hloop, h⟩ := rustM_bind_ok h
        cases h
        rw [loopRevS_of_loopRevS (step' := fun i ρ => toRustMSB app body (ρ.upd var (ctr i)) >>=
            fun s => match s.1 with
              | .val _ => .ok s.2
              | .brk _ => .fail .undef) (fun i ρ ρ'' hs => by
              obtain ⟨s, hs', hfin⟩ := rustM_bind_ok hs
              cases hfin
              simp only [ih1 i ρ s.1 s.2 hs', bind_tc_ok]) _ _ _ _ hloop]
        rfl
  case case16 e i ρ ih1 =>
    intro v ρ' h
    obtain ⟨⟨t, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    have ht := ih1 t ρ1 hp
    cases t with
    | tup vs =>
      cases hvi : vs[i]? with
      | none => simp only [hvi] at h; cases h
      | some w =>
        simp only [hvi] at h
        cases h
        simp only [toRustMSB, ht, bind_tc_ok, hvi]
    | _ => cases h
  case case17 f args ρ _ _ _ ih =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    simp only [toRustMSB, ih p.1 p.2 hp, bind_tc_ok, hr]
  case case18 =>
    intro v ρ' h
    cases h
  case case19 ρ =>
    intro vs ρ' h
    cases h
    simp only [toRustMSB.argsSB]
  case case20 a as ρ ih2 ih1 =>
    intro vs ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    cases h
    simp only [toRustMSB.argsSB, ih2 p.1 p.2 hp, ih1 p q.1 q.2 hq, bind_tc_ok]

/-! ## The Aeneas backend's loop with breaks -/

/-- **The Aeneas backend's loop over a `usize` range with breaks.** For a body that steps
    the range, runs `f` on the current index and returns `ControlFlow.done` at a break
    (`some b`) or at the end of the range (`none`), the loop is `loopBS`. -/
theorem loop_range_break {α β : Type}
    (body : core.ops.range.Range Usize × α →
      RustM (Aeneas.Std.ControlFlow (core.ops.range.Range Usize × α) (Option β × α)))
    (f : α → Usize → RustM (Option β × α)) (n : Usize)
    (hbody : ∀ (s : Usize) (acc : α), body ({ start := s, «end» := n }, acc) =
      if s.val < n.val then
        f acc s >>= fun p => match p.1 with
          | some b => .ok (.done (some b, p.2))
          | none => .ok (.cont ({ start := ⟨BitVec.ofNat _ (s.val + 1)⟩, «end» := n }, p.2))
      else .ok (.done (none, acc))) :
    ∀ (k : Nat) (s : Usize) (acc : α), k = n.val - s.val →
      loop body ({ start := s, «end» := n }, acc) =
        loopBS (fun i a => f a ⟨BitVec.ofNat _ i⟩) k s.val acc
  | 0, s, acc, hk => by
    rw [loop.eq_1, hbody, if_neg (by omega)]
    rfl
  | k + 1, s, acc, hk => by
    have hlt : s.val < n.val := by omega
    have e : (⟨BitVec.ofNat _ s.val⟩ : Usize) = s := by
      cases s
      simp [UScalar.val]
    rw [loop.eq_1, hbody, if_pos hlt]
    simp only [loopBS, e]
    cases hf : f acc s with
    | ok p =>
      obtain ⟨o, acc'⟩ := p
      cases o with
      | some b => simp only [bind_tc_ok]
      | none =>
        simp only [bind_tc_ok]
        have hs : (⟨BitVec.ofNat _ (s.val + 1)⟩ : Usize).val = s.val + 1 := by
          have hn := n.bv.isLt
          simp only [UScalar.val, BitVec.toNat_ofNat] at hlt hn ⊢
          exact Nat.mod_eq_of_lt (by omega)
        have := loop_range_break body f n hbody k ⟨BitVec.ofNat _ (s.val + 1)⟩ acc' (by omega)
        rw [hs] at this
        exact this
    | fail e => rfl
    | div => rfl

/-- The loop `for i in 0..3 { break i }` is read: it stops at its first iteration and
    returns the index `0`. -/
example : toRustMSB appRt
    (.forFold "i" (.lit (.int 0)) (.lit (.int 3)) (.cfBreak (.var "i"))) (fun _ => none) =
      .ok (.val (ctr 0), AEnv.upd (fun _ => none) "i" (ctr 0)) := by
  have h3 : (3 : Int) ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  simp [toRustMSB, AVal.toInt?, loopBS, BOut.brk?, h3, AEnv.upd]

end HaxAscent.RustSemantics
