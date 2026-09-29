/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxExitCT

/-!
# Constant time of the exit-flag loops over an agreement relation

The loop lemmas of `HaxExitCT.lean` stated for any relation `Ag` between environments
and states, in place of `envAgreesOff`. The lowered loop body `bC` of a source body
`body` enters through two hypotheses:

* `BodyRunAg Ag body bC`: a traced run of `bC` from a state agreeing with an environment,
  with the exit flag `0`, whose source counterpart ends in a value `w`, ends with the
  exit flag `1` when `w` is an exit, and otherwise with the flag `0`, `w` not a
  control-flow value, and a state agreeing with the final environment;
* `BodyCTAg Ag body bC`: two such runs from environments with equal source leakage have
  equal traces and agree on whether they exit.

`AgReserved Ag` states that writing a reserved scalar slot keeps the agreement. The
loops are then proved once per target shape as in `HaxExitCT.lean`: `genLoopCT` and
`genLoopWrapCT` for `RWhileNz`, `genTripsCT` for the guarded trips of a counted loop
(`genTripsCTAg` when the counter expression reads more than the trip slot), and `genForCT`,
`genForRevCT`, `genForLoopCT`, `genForLoopRtCT`, `genForLoopVCT` for the counted loops.

## Main definitions

* `AgReserved`, `BodyRunAg`, `BodyCTAg`

## Main results

* `bodyStepAg` — two runs of a loop body: equal traces, and both exit or both continue
* `genLoopCT`, `genLoopWrapCT`, `genTripsCT`, `genTripsCTAg`, `genForCT`, `genForRevCT`,
  `genForLoopCT`, `genForLoopRtCT`, `genForLoopVCT`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak LowCTLeakModel sexprLeak RustExecLeak)

section Generic

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (Ag : Env → RustState → Prop)

/-- Writing a reserved scalar slot keeps the agreement. -/
def AgReserved : Prop :=
  ∀ (x : String) (k : Nat) (env : Env) (rs : RustState), exitReserved x = true →
    Ag env rs → Ag env (rsSetScalar rs x k)

/-- A traced run of `bC` from a state agreeing with `env` with the exit flag `0`, whose
    source run of `body` ends in the value `w`: at an exit the flag ends `1`; otherwise `w`
    is not a control-flow value, the flag ends `0` and the final state agrees with the
    final environment. -/
def BodyRunAg (body : ImpExpr) (bC : LowCT) : Prop :=
  ∀ (fuel : Nat) (env env' : Env) (w : Value) (rs r : RustState) (t : List CTLeak),
    Ag env rs → rs.rsScalar exitRetName = 0 →
    (denote' bi fuel body).run env = (.val w, env') →
    RustExecLeak N leafSpec M bC rs t r →
    (exitOf (.val w) = true → r.rsScalar exitRetName = 1) ∧
    (exitOf (.val w) = false →
      w.isControlFlow = false ∧ r.rsScalar exitRetName = 0 ∧ Ag env' r)

/-- Two traced runs of `bC` from states agreeing with environments with equal source
    leakage of `body`, whose source runs end in values, have equal traces and agree on
    whether they exit. -/
def BodyCTAg (body : ImpExpr) (bC : LowCT) : Prop :=
  ∀ (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (w₁ w₂ : Value) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak),
    Ag env₁ rs₁ → rs₁.rsScalar exitRetName = 0 → Ag env₂ rs₂ → rs₂.rsScalar exitRetName = 0 →
    (denote' bi fuel body).run env₁ = (.val w₁, env₁') →
    (denote' bi fuel body).run env₂ = (.val w₂, env₂') →
    srcLeak M bi body fuel env₁ = srcLeak M bi body fuel env₂ →
    RustExecLeak N leafSpec M bC rs₁ t₁ r₁ → RustExecLeak N leafSpec M bC rs₂ t₂ r₂ →
    t₁ = t₂ ∧ exitOf (.val w₁) = exitOf (.val w₂)

variable {M bi N leafSpec Ag}

/-- Two runs of a loop body: equal traces, and either both exit with the flag `1`, or
    both continue with the flag `0` from agreeing states. -/
theorem bodyStepAg {body : ImpExpr} {bC : LowCT} (hR : BodyRunAg M bi N leafSpec Ag body bC)
    (hC : BodyCTAg M bi N leafSpec Ag body bC) {fuel : Nat} {env₁ env₂ e₁ e₂ : Env}
    {w₁ w₂ : Value} {rs₁ rs₂ q₁ q₂ : RustState} {t₁ t₂ : List CTLeak}
    (hag₁ : Ag env₁ rs₁) (hret₁ : rs₁.rsScalar exitRetName = 0)
    (hag₂ : Ag env₂ rs₂) (hret₂ : rs₂.rsScalar exitRetName = 0)
    (hr₁ : (denote' bi fuel body).run env₁ = (.val w₁, e₁))
    (hr₂ : (denote' bi fuel body).run env₂ = (.val w₂, e₂))
    (hL : srcLeak M bi body fuel env₁ = srcLeak M bi body fuel env₂)
    (h₁ : RustExecLeak N leafSpec M bC rs₁ t₁ q₁) (h₂ : RustExecLeak N leafSpec M bC rs₂ t₂ q₂) :
    t₁ = t₂ ∧
      ((exitOf (.val w₁) = true ∧ exitOf (.val w₂) = true ∧
          q₁.rsScalar exitRetName = 1 ∧ q₂.rsScalar exitRetName = 1) ∨
        (w₁.isControlFlow = false ∧ w₂.isControlFlow = false ∧
          q₁.rsScalar exitRetName = 0 ∧ Ag e₁ q₁ ∧ q₂.rsScalar exitRetName = 0 ∧ Ag e₂ q₂)) := by
  obtain ⟨ht, hx⟩ := hC fuel env₁ env₂ e₁ e₂ w₁ w₂ rs₁ rs₂ q₁ q₂ t₁ t₂ hag₁ hret₁ hag₂ hret₂
    hr₁ hr₂ hL h₁ h₂
  have s₁ := hR fuel env₁ e₁ w₁ rs₁ q₁ t₁ hag₁ hret₁ hr₁ h₁
  have s₂ := hR fuel env₂ e₂ w₂ rs₂ q₂ t₂ hag₂ hret₂ hr₂ h₂
  refine ⟨ht, ?_⟩
  cases hx₁ : exitOf (.val w₁) with
  | true =>
    have hx₂ : exitOf (.val w₂) = true := hx.symm.trans hx₁
    exact Or.inl ⟨rfl, hx₂, s₁.1 hx₁, s₂.1 hx₂⟩
  | false =>
    obtain ⟨c₁, f₁, a₁⟩ := s₁.2 hx₁
    obtain ⟨c₂, f₂, a₂⟩ := s₂.2 (hx.symm.trans hx₁)
    exact Or.inr ⟨c₁, c₂, f₁, a₁, f₂, a₂⟩

/-- **The lowered `RWhileNz` loop** over the agreement `Ag`, by induction on fuel:
    `exitLoopCT` with the body entering through `BodyRunAg` and `BodyCTAg`. -/
theorem genLoopCT (hres : AgReserved Ag) (L : Nat → Env → Outcome × Env) (run c : String)
    (body : ImpExpr) (bC : LowCT)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hc : exitReserved c = false)
    (hg : ∀ env rs b, Ag env rs → env c = some (.bool b) → rs.rsScalar c = if b then 1 else 0)
    (hL0 : ∀ env v, (L 0 env).1 ≠ .val v)
    (hLb : ∀ n env rs v, Ag env rs → (∀ b, env c ≠ some (.bool b)) →
      (L (n + 1) env).1 ≠ .val v)
    (hLo : ∀ n env o e2, env c = some (.bool true) →
      (denote' bi (n + 1) body).run env = (o, e2) → (∀ v, o ≠ .val v) → L (n + 1) env = (o, e2))
    (hLi : ∀ n env w e2, env c = some (.bool true) →
      (denote' bi (n + 1) body).run env = (.val w, e2) → w.isControlFlow = false →
      L (n + 1) env = L n e2) :
    ∀ (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
      (t₁ t₂ : List CTLeak),
      L fuel env₁ = (o₁, env₁') → (∃ v, o₁ = .val v) →
      L fuel env₂ = (o₂, env₂') → (∃ v, o₂ = .val v) →
      Ag env₁ rs₁ → rs₁.rsScalar exitRetName = 0 → rs₁.rsScalar run = rs₁.rsScalar c →
      Ag env₂ rs₂ → rs₂.rsScalar exitRetName = 0 → rs₂.rsScalar run = rs₂.rsScalar c →
      whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₁ =
        whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₂ →
      RustExecLeak N leafSpec M (.RWhileNz run (.RSeq bC (loopTail run c))) rs₁ t₁ r₁ →
      RustExecLeak N leafSpec M (.RWhileNz run (.RSeq bC (loopTail run c))) rs₂ t₂ r₂ →
      t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hcr : c ≠ run := ne_of_reserved hc (exitReserved_of_runSlot hslot)
  have hresv := exitReserved_of_runSlot hslot
  have hcv : ∀ {n : Nat} {env : Env} {b : Bool}, env c = some (.bool b) →
      (denote' bi n (.var c)).run env = (.val (.bool b), env) := fun h => by
    rw [denote'_var_run, h]
  intro fuel
  induction fuel with
  | zero =>
    intro env₁ _ _ _ o₁ _ _ _ _ _ _ _ hrun₁ hval₁
    obtain ⟨v, rfl⟩ := hval₁
    exact absurd (by rw [hrun₁]) (hL0 env₁ v)
  | succ n IH =>
    intro env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hret₁
      hrc₁ hag₂ hret₂ hrc₂ hL h₁ h₂
    have hgd : ∀ {env env' : Env} {o : Outcome} {rs : RustState}, L (n + 1) env = (o, env') →
        (∃ v, o = .val v) → Ag env rs →
        ∃ b, env c = some (.bool b) ∧ rs.rsScalar c = if b then 1 else 0 := by
      intro env env' o rs hrun hval hag
      by_cases hb : ∃ b, env c = some (.bool b)
      · obtain ⟨b, hb⟩ := hb
        exact ⟨b, hb, hg env rs b hag hb⟩
      · obtain ⟨v, rfl⟩ := hval
        exact absurd (by rw [hrun]) (hLb n env rs v hag (fun b h => hb ⟨b, h⟩))
    obtain ⟨b₁, hb₁, hd₁⟩ := hgd hrun₁ hval₁ hag₁
    obtain ⟨b₂, hb₂, hd₂⟩ := hgd hrun₂ hval₂ hag₂
    simp only [whileLeak, srcLeak, hcv hb₁, hcv hb₂] at hL
    cases b₁ <;> cases b₂ <;> simp only [SrcLeak.cat.injEq, reduceCtorEq, and_false,
      true_and] at hL
    · -- both guards false
      simp only [Bool.false_eq_true, if_false] at hd₁ hd₂
      have hw : ∀ {rs r : RustState} {t : List CTLeak}, rs.rsScalar run = 0 →
          RustExecLeak N leafSpec M (.RWhileNz run (.RSeq bC (loopTail run c))) rs t r →
          t = [.branch false] ∧ r = rs := by
        intro rs r t h0 h
        cases h with
        | whileFalse => exact ⟨rfl, rfl⟩
        | whileTrue _ _ _ _ _ _ _ _ hv hv0 _ _ => exact absurd (hv ▸ h0) hv0
      obtain ⟨rfl, rfl⟩ := hw (hrc₁.trans hd₁) h₁
      obtain ⟨rfl, rfl⟩ := hw (hrc₂.trans hd₂) h₂
      exact ⟨rfl, hret₁.trans hret₂.symm⟩
    · -- both guards true
      simp only [if_true] at hd₁ hd₂
      rcases hbr₁ : (denote' bi (n + 1) body).run env₁ with ⟨ob₁, e2₁⟩
      rcases hbr₂ : (denote' bi (n + 1) body).run env₂ with ⟨ob₂, e2₂⟩
      have hvb : ∀ {env env' e2 : Env} {o ob : Outcome}, env c = some (.bool true) →
          (denote' bi (n + 1) body).run env = (ob, e2) → L (n + 1) env = (o, env') →
          (∃ v, o = .val v) → ∃ w, ob = .val w := by
        intro env env' e2 o ob hb hbr hrun hval
        cases ob with
        | val w => exact ⟨w, rfl⟩
        | _ =>
          rw [hLo n env _ e2 hb hbr (fun v h => by cases h)] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          obtain ⟨_, h⟩ := hval; cases h
      obtain ⟨w₁, rfl⟩ := hvb hb₁ hbr₁ hrun₁ hval₁
      obtain ⟨w₂, rfl⟩ := hvb hb₂ hbr₂ hrun₂ hval₂
      rw [hbr₁, hbr₂] at hL
      obtain ⟨hLbody, hLrest⟩ := hL
      cases h₁ with
      | whileFalse _ _ _ h0 => rw [hrc₁, hd₁] at h0; simp at h0
      | whileTrue _ _ _ m₁ _ _ tt₁ tl₁ _ _ hbody₁ hloop₁ =>
      cases h₂ with
      | whileFalse _ _ _ h0 => rw [hrc₂, hd₂] at h0; simp at h0
      | whileTrue _ _ _ m₂ _ _ tt₂ tl₂ _ _ hbody₂ hloop₂ =>
      cases hbody₁ with
      | seq _ _ _ q₁ _ tb₁ tq₁ hB₁ hT₁ =>
      cases hbody₂ with
      | seq _ _ _ q₂ _ tb₂ tq₂ hB₂ hT₂ =>
      obtain ⟨htb, hst⟩ := bodyStepAg hR hC hag₁ hret₁ hag₂ hret₂ hbr₁ hbr₂ hLbody hB₁ hB₂
      rcases hst with ⟨-, -, hf₁, hf₂⟩ | ⟨hcf₁, hcf₂, h01, hagq₁, h02, hagq₂⟩
      · have hdone : ∀ {q m r : RustState} {tq tl : List CTLeak}, q.rsScalar exitRetName = 1 →
            RustExecLeak N leafSpec M (loopTail run c) q tq m →
            RustExecLeak N leafSpec M (.RWhileNz run (.RSeq bC (loopTail run c))) m tl r →
            tq = [.branch true] ∧ tl = [.branch false] ∧ r.rsScalar exitRetName = 1 := by
          intro q m r tq tl hq hT hl
          cases hT with
          | ifFalse _ _ _ _ _ _ h0 _ => rw [hq] at h0; simp at h0
          | ifTrue _ _ _ _ _ _ _ _ _ hs =>
            cases hs
            cases hl with
            | whileFalse =>
              refine ⟨rfl, rfl, ?_⟩
              rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hq]
            | whileTrue _ _ _ _ _ _ _ _ hv hv0 _ _ => simp at hv; exact absurd hv.symm hv0
        obtain ⟨rfl, rfl, hr₁⟩ := hdone hf₁ hT₁ hloop₁
        obtain ⟨rfl, rfl, hr₂⟩ := hdone hf₂ hT₂ hloop₂
        exact ⟨by rw [htb], hr₁.trans hr₂.symm⟩
      · rw [tripCont_val hcf₁, tripCont_val hcf₂] at hLrest
        rw [hLi n env₁ w₁ e2₁ hb₁ hbr₁ hcf₁] at hrun₁
        rw [hLi n env₂ w₂ e2₂ hb₂ hbr₂ hcf₂] at hrun₂
        have hnext : ∀ {q m : RustState} {tq : List CTLeak} {e : Env},
            Ag e q → q.rsScalar exitRetName = 0 →
            RustExecLeak N leafSpec M (loopTail run c) q tq m →
            tq = [.branch false] ∧ Ag e m ∧ m.rsScalar exitRetName = 0 ∧
              m.rsScalar run = m.rsScalar c := by
          intro q m tq e hag hq hT
          cases hT with
          | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ hq) hv0
          | ifFalse _ _ _ _ _ _ _ hs =>
            cases hs
            refine ⟨rfl, hres _ _ _ _ hresv hag, ?_, ?_⟩
            · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hq]
            · simp [rsScalar_rsSetScalar, hcr, SExpr.evalState]
        obtain ⟨rfl, hagm₁, hretm₁, hrcm₁⟩ := hnext hagq₁ h01 hT₁
        obtain ⟨rfl, hagm₂, hretm₂, hrcm₂⟩ := hnext hagq₂ h02 hT₂
        obtain ⟨htl, hr⟩ := IH e2₁ e2₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ tl₁ tl₂ hrun₁ hval₁ hrun₂ hval₂
          hagm₁ hretm₁ hrcm₁ hagm₂ hretm₂ hrcm₂ hLrest hloop₁ hloop₂
        exact ⟨by rw [htb, htl], hr⟩

/-- `genLoopCT` with the loop entry of `exitLoop`: the flag, payload and loop slots are
    zeroed and the guard is copied into the loop slot. -/
theorem genLoopWrapCT (hres : AgReserved Ag) (L : Nat → Env → Outcome × Env) (run c : String)
    (body : ImpExpr) (bC : LowCT)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hc : exitReserved c = false)
    (hg : ∀ env rs b, Ag env rs → env c = some (.bool b) → rs.rsScalar c = if b then 1 else 0)
    (hL0 : ∀ env v, (L 0 env).1 ≠ .val v)
    (hLb : ∀ n env rs v, Ag env rs → (∀ b, env c ≠ some (.bool b)) →
      (L (n + 1) env).1 ≠ .val v)
    (hLo : ∀ n env o e2, env c = some (.bool true) →
      (denote' bi (n + 1) body).run env = (o, e2) → (∀ v, o ≠ .val v) → L (n + 1) env = (o, e2))
    (hLi : ∀ n env w e2, env c = some (.bool true) →
      (denote' bi (n + 1) body).run env = (.val w, e2) → w.isControlFlow = false →
      L (n + 1) env = L n e2)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : L fuel env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : L fuel env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : Ag env₁ rs₁) (hag₂ : Ag env₂ rs₂)
    (hL : whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₁ =
        whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₂)
    (h₁ : RustExecLeak N leafSpec M (exitLoop run c bC) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (exitLoop run c bC) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hresv := exitReserved_of_runSlot hslot
  have hcr : c ≠ run := ne_of_reserved hc hresv
  have hentry : ∀ {env : Env} {rs r : RustState} {t : List CTLeak}, Ag env rs →
      RustExecLeak N leafSpec M (exitLoop run c bC) rs t r →
      ∃ rs1, Ag env rs1 ∧ rs1.rsScalar exitRetName = 0 ∧
        rs1.rsScalar run = rs1.rsScalar c ∧
        RustExecLeak N leafSpec M (.RWhileNz run (.RSeq bC (loopTail run c))) rs1 t r := by
    intro env rs r t hag h
    cases h with
    | letU64Zero _ _ _ _ _ h =>
    cases h with
    | letU64Zero _ _ _ _ _ h =>
    cases h with
    | letU64Zero _ _ _ _ _ h =>
    cases h with
    | seq _ _ _ _ _ _ _ hs hl =>
    cases hs
    refine ⟨_, hres _ _ _ _ hresv (hres _ _ _ _ hresv (hres _ _ _ _ exitReserved_val
      (hres _ _ _ _ exitReserved_ret hag))), ?_, ?_, hl⟩
    · simp [rsScalar_rsSetScalar, (runSlot_ne_ret hslot).symm, exitRetName_ne_val]
    · simp [rsScalar_rsSetScalar, hcr, SExpr.evalState]
  obtain ⟨q₁, hq₁, hr₁, hc₁, hl₁⟩ := hentry hag₁ h₁
  obtain ⟨q₂, hq₂, hr₂, hc₂, hl₂⟩ := hentry hag₂ h₂
  exact genLoopCT hres L run c body bC hR hC hslot hc hg hL0 hLb hLo hLi
    fuel env₁ env₂ env₁' env₂' o₁ o₂ q₁ q₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hq₁ hr₁ hc₁ hq₂
    hr₂ hc₂ hL hl₁ hl₂

/-- **The trips of a lowered counted loop** over the agreement `Ag`, by induction on the
    trips left: `exitTripsCT` with the body entering through `BodyRunAg` and `BodyCTAg`,
    and the binding of the counter through `hext`. -/
theorem genTripsCT (hres : AgReserved Ag) (run i : String) (body : ImpExpr) (bC : LowCT)
    (ce : SExpr) (cnt : Nat → Nat) (D : Nat) (L : Nat → Nat → Env → Outcome × Env)
    (T : Nat → Nat → Env → SrcLeak)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false)
    (hext : ∀ env rs j, j < D → Ag env rs →
      Ag (env.extend i (.int (cnt j))) (rsSetScalar rs i (cnt j)))
    (hce : sexprReadsOnly (fun x => x = run) ce)
    (hcev : ∀ (j : Nat) (s : RustState), s.rsScalar run = j → ce.evalState s = cnt j)
    (hL0 : ∀ j env v, j < D → (L 0 j env).1 ≠ .val v)
    (hLo : ∀ n j env o e2, j < D →
      (denote' bi (n + 1) body).run (env.extend i (.int (cnt j))) = (o, e2) →
      (∀ v, o ≠ .val v) → L (n + 1) j env = (o, e2))
    (hLi : ∀ n j env w e2, j < D →
      (denote' bi (n + 1) body).run (env.extend i (.int (cnt j))) = (.val w, e2) →
      w.isControlFlow = false → L (n + 1) j env = L n (j + 1) e2)
    (hT : ∀ n j env, j < D → T (n + 1) j env =
      .cat (srcLeak M bi body (n + 1) (env.extend i (.int (cnt j))))
        (tripCont ((denote' bi (n + 1) body).run (env.extend i (.int (cnt j)))) fun e2 =>
          T n (j + 1) e2)) :
    ∀ (d j fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome)
      (rs₁ rs₂ r₁ r₂ : RustState) (t₁ t₂ : List CTLeak), j + d = D →
      L fuel j env₁ = (o₁, env₁') → (∃ v, o₁ = .val v) →
      L fuel j env₂ = (o₂, env₂') → (∃ v, o₂ = .val v) →
      Ag env₁ rs₁ → rs₁.rsScalar exitRetName = 0 →
      Ag env₂ rs₂ → rs₂.rsScalar exitRetName = 0 →
      T fuel j env₁ = T fuel j env₂ →
      TripsL M N leafSpec run (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
        j d rs₁ t₁ r₁ →
      TripsL M N leafSpec run (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
        j d rs₂ t₂ r₂ →
      t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ _ _ _ _ _ _ hret₁ _ hret₂ _ h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, hret₁.trans hret₂.symm⟩
  | succ d IH =>
    intro j fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hj hrun₁ hval₁ hrun₂ hval₂
      hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
    have hjD : j < D := by omega
    cases fuel with
    | zero =>
      obtain ⟨v, rfl⟩ := hval₁
      exact absurd (by rw [hrun₁]) (hL0 j env₁ v hjD)
    | succ n =>
    have hent : ∀ {env : Env} {rs m : RustState} {tt : List CTLeak},
        Ag env rs → rs.rsScalar exitRetName = 0 →
        RustExecLeak N leafSpec M (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
          (rsSetScalar rs run j) tt m →
        ∃ tb, tt = .branch false ::
            (sexprLeak M (rsSetScalar (rsSetScalar rs run j) i 0) ce ++ tb) ∧
          RustExecLeak N leafSpec M bC (rsSetScalar (rsSetScalar rs run j) i (cnt j)) tb m ∧
          Ag (env.extend i (.int (cnt j))) (rsSetScalar (rsSetScalar rs run j) i (cnt j)) ∧
          (rsSetScalar (rsSetScalar rs run j) i (cnt j)).rsScalar exitRetName = 0 := by
      intro env rs m tt hag hret h
      have hr0 : (rsSetScalar rs run j).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret]
      cases h with
      | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ hr0) hv0
      | ifFalse _ _ _ _ _ _ _ h =>
      cases h with
      | letU64Zero _ _ _ _ _ h =>
      cases h with
      | seq _ _ _ _ _ _ tb hs hb =>
      cases hs
      have hv : ce.evalState (rsSetScalar (rsSetScalar rs run j) i 0) = cnt j :=
        hcev j _ (by simp [rsScalar_rsSetScalar, hir.symm])
      rw [hv, rsSetScalar_rsSetScalar] at hb
      refine ⟨tb, rfl, hb, hext _ _ j hjD (hres _ _ _ _ hresv hag), ?_⟩
      rw [rsScalar_rsSetScalar, if_neg hiret.symm, hr0]
    obtain ⟨m₁, tt₁, tr₁, hB₁, hR₁, rfl⟩ := h₁
    obtain ⟨m₂, tt₂, tr₂, hB₂, hR₂, rfl⟩ := h₂
    obtain ⟨tb₁, rfl, hb₁, hagT₁, hretT₁⟩ := hent hag₁ hret₁ hB₁
    obtain ⟨tb₂, rfl, hb₂, hagT₂, hretT₂⟩ := hent hag₂ hret₂ hB₂
    have hce_eq : sexprLeak M (rsSetScalar (rsSetScalar rs₁ run j) i 0) ce =
        sexprLeak M (rsSetScalar (rsSetScalar rs₂ run j) i 0) ce :=
      sexprLeak_congr M (fun x hx => by subst hx; simp [rsScalar_rsSetScalar, hir.symm]) ce hce
    rcases hbr₁ : (denote' bi (n + 1) body).run (env₁.extend i (.int (cnt j))) with ⟨ob₁, e2₁⟩
    rcases hbr₂ : (denote' bi (n + 1) body).run (env₂.extend i (.int (cnt j))) with ⟨ob₂, e2₂⟩
    have hvb : ∀ {env env' e2 : Env} {o ob : Outcome},
        (denote' bi (n + 1) body).run (env.extend i (.int (cnt j))) = (ob, e2) →
        L (n + 1) j env = (o, env') → (∃ v, o = .val v) → ∃ w, ob = .val w := by
      intro env env' e2 o ob hbr hrun hval
      cases ob with
      | val w => exact ⟨w, rfl⟩
      | _ =>
        rw [hLo n j env _ e2 hjD hbr (fun v h => by cases h)] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        obtain ⟨_, h⟩ := hval; cases h
    obtain ⟨w₁, rfl⟩ := hvb hbr₁ hrun₁ hval₁
    obtain ⟨w₂, rfl⟩ := hvb hbr₂ hrun₂ hval₂
    rw [hT n j env₁ hjD, hT n j env₂ hjD, hbr₁, hbr₂] at hL
    injection hL with hLbody hLrest
    obtain ⟨htb, hst⟩ := bodyStepAg hR hC hagT₁ hretT₁ hagT₂ hretT₂ hbr₁ hbr₂ hLbody hb₁ hb₂
    rcases hst with ⟨-, -, hf₁, hf₂⟩ | ⟨hcf₁, hcf₂, h01, hagq₁, h02, hagq₂⟩
    · obtain ⟨rfl, hr₁⟩ := exitedTripsL M N leafSpec run _ hslot d (j + 1) m₁ r₁ tr₁ hf₁ hR₁
      obtain ⟨rfl, hr₂⟩ := exitedTripsL M N leafSpec run _ hslot d (j + 1) m₂ r₂ tr₂ hf₂ hR₂
      exact ⟨by rw [hce_eq, htb], hr₁.trans hr₂.symm⟩
    · rw [tripCont_val hcf₁, tripCont_val hcf₂] at hLrest
      rw [hLi n j env₁ w₁ e2₁ hjD hbr₁ hcf₁] at hrun₁
      rw [hLi n j env₂ w₂ e2₂ hjD hbr₂ hcf₂] at hrun₂
      obtain ⟨htr, hr⟩ := IH (j + 1) n e2₁ e2₂ env₁' env₂' o₁ o₂ m₁ m₂ r₁ r₂ tr₁ tr₂ (by omega)
        hrun₁ hval₁ hrun₂ hval₂ hagq₁ h01 hagq₂ h02 hLrest hR₁ hR₂
      exact ⟨by rw [hce_eq, htb, htr], hr⟩

/-- **The lowered upward counted loop** `RFor run (hi - lo) (exitForTrip run i lo bC)` over
    the agreement `Ag`, for a source loop `Lf` that unfolds as `denoteForLoop'Return` and
    `denoteForLoop'` do. -/
theorem genForCT (hres : AgReserved Ag) (Lf : Nat → Int → Env → Outcome × Env) (run i : String)
    (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hext : ∀ env rs (k : Nat), k < 2 ^ 64 → Ag env rs →
      Ag (env.extend i (.int k)) (rsSetScalar rs i k))
    (hL0 : ∀ (k : Int) env v, k < hi → (Lf 0 k env).1 ≠ .val v)
    (hLo : ∀ n (k : Int) env o e2, k < hi →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (o, e2) →
      (∀ v, o ≠ .val v) → Lf (n + 1) k env = (o, e2))
    (hLi : ∀ n (k : Int) env w e2, k < hi →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (.val w, e2) →
      w.isControlFlow = false → Lf (n + 1) k env = Lf n (k + 1) e2)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : Lf fuel lo env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : Lf fuel lo env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : Ag env₁ rs₁) (hret₁ : rs₁.rsScalar exitRetName = 0)
    (hag₂ : Ag env₂ rs₂) (hret₂ : rs₂.rsScalar exitRetName = 0)
    (hL : forLeak bi i body (srcLeak M bi body) fuel lo hi env₁ =
      forLeak bi i body (srcLeak M bi body) fuel lo hi env₂)
    (h₁ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTrip run i lo bC)) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTrip run i lo bC)) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hcast : ∀ j : Nat, ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 := by
    intro j; push_cast; ring
  refine genTripsCT hres run i body bC (.SAdd (.SVar run) (.SLit lo))
    (fun j => lo + j) (hi - lo) (fun n j env => Lf n ((lo + j : Nat) : Int) env)
    (fun n j env => forLeak bi i body (srcLeak M bi body) n ((lo + j : Nat) : Int) hi env)
    hR hC hslot hi_ (fun env rs j hj hag => hext env rs _ (by omega) hag) ⟨rfl, trivial⟩
    (fun j s hs => by simp [SExpr.evalState, hs, Nat.add_comm])
    (fun j env v hj => hL0 _ env v (by omega))
    (fun n j env o e2 hj hbr ho => hLo n _ env o e2 (by omega) hbr ho)
    (fun n j env w e2 hj hbr hw => by
      rw [hLi n _ env w e2 (by omega) hbr hw, hcast])
    (fun n j env hj => by
      rw [forLeak, if_neg (by omega), hcast])
    (hi - lo) 0 fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ (by omega)
    (by simpa using hrun₁) hval₁ (by simpa using hrun₂) hval₂ hag₁ hret₁ hag₂ hret₂
    (by simpa using hL) (rFor_tripsL M N leafSpec _ _ _ rs₁ r₁ t₁ h₁)
    (rFor_tripsL M N leafSpec _ _ _ rs₂ r₂ t₂ h₂)

/-- **The lowered downward counted loop** `RFor run (hi - lo) (exitForTripRev run i hi bC)`
    over the agreement `Ag`, for the source loop `denoteForLoopRev'Return`. -/
theorem genForRevCT (hres : AgReserved Ag) (run i : String) (lo hi : Nat)
    (body : ImpExpr) (bC : LowCT)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hext : ∀ env rs (k : Nat), k < 2 ^ 64 → Ag env rs →
      Ag (env.extend i (.int k)) (rsSetScalar rs i k))
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : (_root_.Hax.denoteForLoopRev'Return bi fuel i lo hi body).run env₁ = (o₁, env₁'))
    (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : (_root_.Hax.denoteForLoopRev'Return bi fuel i lo hi body).run env₂ = (o₂, env₂'))
    (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : Ag env₁ rs₁) (hret₁ : rs₁.rsScalar exitRetName = 0)
    (hag₂ : Ag env₂ rs₂) (hret₂ : rs₂.rsScalar exitRetName = 0)
    (hL : forRevLeak bi i body (srcLeak M bi body) fuel lo hi env₁ =
      forRevLeak bi i body (srcLeak M bi body) fuel lo hi env₂)
    (h₁ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTripRev run i hi bC)) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTripRev run i hi bC)) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hcast : ∀ j : Nat, j < hi - lo → ((hi - j : Nat) : Int) - 1 = ((hi - 1 - j : Nat) : Int) := by
    intro j hj; omega
  have hcast' : ∀ j : Nat, j < hi - lo →
      ((hi - (j + 1) : Nat) : Int) = ((hi - j : Nat) : Int) - 1 := by
    intro j hj; omega
  refine genTripsCT hres run i body bC (.SSub (.SLit (hi - 1)) (.SVar run))
    (fun j => hi - 1 - j) (hi - lo)
    (fun n j env =>
      (_root_.Hax.denoteForLoopRev'Return bi n i lo ((hi - j : Nat) : Int) body).run env)
    (fun n j env => forRevLeak bi i body (srcLeak M bi body) n lo ((hi - j : Nat) : Int) env)
    hR hC hslot hi_ (fun env rs j hj hag => hext env rs _ (by omega) hag) ⟨trivial, rfl⟩
    (fun j s hs => by simp [SExpr.evalState, hs])
    (fun j env v hj => by
      rw [denoteForLoopRev'Return_zero_run bi i _ _ body env (by omega)]; simp)
    (fun n j env o e2 hj hbr ho => by
      refine denoteForLoopRev'Return_succ_nonval bi n i _ _ body env e2 o (by omega) ?_ ho
      rw [hcast j hj]; exact hbr)
    (fun n j env w e2 hj hbr hw => by
      rw [denoteForLoopRev'Return_succ_iterate bi n i _ _ body env e2 w (by omega)
        (by rw [hcast j hj]; exact hbr) hw, hcast' j hj])
    (fun n j env hj => by
      rw [forRevLeak, if_neg (by omega), hcast j hj, hcast' j hj, hcast j hj])
    (hi - lo) 0 fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ (by omega)
    (by simpa using hrun₁) hval₁ (by simpa using hrun₂) hval₂ hag₁ hret₁ hag₂ hret₂
    (by simpa using hL) (rFor_tripsL M N leafSpec _ _ _ rs₁ r₁ t₁ h₁)
    (rFor_tripsL M N leafSpec _ _ _ rs₂ r₂ t₂ h₂)

/-- The entry of a lowered counted loop: zeroing the flag and payload slots keeps the
    agreement and sets the flag to `0`. -/
theorem genForEntry (hres : AgReserved Ag) {env : Env} {rs : RustState} (hag : Ag env rs) :
    Ag env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) ∧
      (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar exitRetName = 0 :=
  ⟨hres _ _ _ _ exitReserved_val (hres _ _ _ _ exitReserved_ret hag),
    by rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]⟩

/-- `genForCT` with the loop entry of `exitForLoop`. -/
theorem genForLoopCT (hres : AgReserved Ag) (Lf : Nat → Int → Env → Outcome × Env)
    (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hext : ∀ env rs (k : Nat), k < 2 ^ 64 → Ag env rs →
      Ag (env.extend i (.int k)) (rsSetScalar rs i k))
    (hL0 : ∀ (k : Int) env v, k < hi → (Lf 0 k env).1 ≠ .val v)
    (hLo : ∀ n (k : Int) env o e2, k < hi →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (o, e2) →
      (∀ v, o ≠ .val v) → Lf (n + 1) k env = (o, e2))
    (hLi : ∀ n (k : Int) env w e2, k < hi →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (.val w, e2) →
      w.isControlFlow = false → Lf (n + 1) k env = Lf n (k + 1) e2)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : Lf fuel lo env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : Lf fuel lo env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : Ag env₁ rs₁) (hag₂ : Ag env₂ rs₂)
    (hL : forLeak bi i body (srcLeak M bi body) fuel lo hi env₁ =
      forLeak bi i body (srcLeak M bi body) fuel lo hi env₂)
    (h₁ : RustExecLeak N leafSpec M (exitForLoop run i lo hi bC) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (exitForLoop run i lo hi bC) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  obtain ⟨hag₁', hret₁'⟩ := genForEntry hres hag₁
  obtain ⟨hag₂', hret₂'⟩ := genForEntry hres hag₂
  exact genForCT hres Lf run i lo hi body bC hR hC hslot hi_ hhi hext hL0 hLo hLi fuel
    env₁ env₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂
    hag₁' hret₁' hag₂' hret₂' hL h₁ h₂

/-- **The trips of a lowered counted loop whose counter expression reads the agreement**:
    `genTripsCT` with the value and the events of the counter expression `ce` given at the
    start of each trip from states agreeing with an environment (`hcev`, `hceq`), in place
    of reading the trip slot alone. -/
theorem genTripsCTAg (hres : AgReserved Ag) (run i : String) (body : ImpExpr) (bC : LowCT)
    (ce : SExpr) (cnt : Nat → Nat) (D : Nat) (L : Nat → Nat → Env → Outcome × Env)
    (T : Nat → Nat → Env → SrcLeak)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false)
    (hext : ∀ env rs j, j < D → Ag env rs →
      Ag (env.extend i (.int (cnt j))) (rsSetScalar rs i (cnt j)))
    (hcev : ∀ env rs j, j < D → Ag env rs →
      ce.evalState (rsSetScalar (rsSetScalar rs run j) i 0) = cnt j)
    (hceq : ∀ env₁ rs₁ env₂ rs₂ j, j < D → Ag env₁ rs₁ → Ag env₂ rs₂ →
      sexprLeak M (rsSetScalar (rsSetScalar rs₁ run j) i 0) ce =
        sexprLeak M (rsSetScalar (rsSetScalar rs₂ run j) i 0) ce)
    (hL0 : ∀ j env v, j < D → (L 0 j env).1 ≠ .val v)
    (hLo : ∀ n j env o e2, j < D →
      (denote' bi (n + 1) body).run (env.extend i (.int (cnt j))) = (o, e2) →
      (∀ v, o ≠ .val v) → L (n + 1) j env = (o, e2))
    (hLi : ∀ n j env w e2, j < D →
      (denote' bi (n + 1) body).run (env.extend i (.int (cnt j))) = (.val w, e2) →
      w.isControlFlow = false → L (n + 1) j env = L n (j + 1) e2)
    (hT : ∀ n j env, j < D → T (n + 1) j env =
      .cat (srcLeak M bi body (n + 1) (env.extend i (.int (cnt j))))
        (tripCont ((denote' bi (n + 1) body).run (env.extend i (.int (cnt j)))) fun e2 =>
          T n (j + 1) e2)) :
    ∀ (d j fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome)
      (rs₁ rs₂ r₁ r₂ : RustState) (t₁ t₂ : List CTLeak), j + d = D →
      L fuel j env₁ = (o₁, env₁') → (∃ v, o₁ = .val v) →
      L fuel j env₂ = (o₂, env₂') → (∃ v, o₂ = .val v) →
      Ag env₁ rs₁ → rs₁.rsScalar exitRetName = 0 →
      Ag env₂ rs₂ → rs₂.rsScalar exitRetName = 0 →
      T fuel j env₁ = T fuel j env₂ →
      TripsL M N leafSpec run (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
        j d rs₁ t₁ r₁ →
      TripsL M N leafSpec run (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
        j d rs₂ t₂ r₂ →
      t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hresv := exitReserved_of_runSlot hslot
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ _ _ _ _ _ _ hret₁ _ hret₂ _ h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, hret₁.trans hret₂.symm⟩
  | succ d IH =>
    intro j fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hj hrun₁ hval₁ hrun₂ hval₂
      hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
    have hjD : j < D := by omega
    cases fuel with
    | zero =>
      obtain ⟨v, rfl⟩ := hval₁
      exact absurd (by rw [hrun₁]) (hL0 j env₁ v hjD)
    | succ n =>
    have hent : ∀ {env : Env} {rs m : RustState} {tt : List CTLeak},
        Ag env rs → rs.rsScalar exitRetName = 0 →
        RustExecLeak N leafSpec M (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
          (rsSetScalar rs run j) tt m →
        ∃ tb, tt = .branch false ::
            (sexprLeak M (rsSetScalar (rsSetScalar rs run j) i 0) ce ++ tb) ∧
          RustExecLeak N leafSpec M bC (rsSetScalar (rsSetScalar rs run j) i (cnt j)) tb m ∧
          Ag (env.extend i (.int (cnt j))) (rsSetScalar (rsSetScalar rs run j) i (cnt j)) ∧
          (rsSetScalar (rsSetScalar rs run j) i (cnt j)).rsScalar exitRetName = 0 := by
      intro env rs m tt hag hret h
      have hr0 : (rsSetScalar rs run j).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret]
      cases h with
      | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ hr0) hv0
      | ifFalse _ _ _ _ _ _ _ h =>
      cases h with
      | letU64Zero _ _ _ _ _ h =>
      cases h with
      | seq _ _ _ _ _ _ tb hs hb =>
      cases hs
      have hv : ce.evalState (rsSetScalar (rsSetScalar rs run j) i 0) = cnt j :=
        hcev env rs j hjD hag
      rw [hv, rsSetScalar_rsSetScalar] at hb
      refine ⟨tb, rfl, hb, hext _ _ j hjD (hres _ _ _ _ hresv hag), ?_⟩
      rw [rsScalar_rsSetScalar, if_neg hiret.symm, hr0]
    obtain ⟨m₁, tt₁, tr₁, hB₁, hR₁, rfl⟩ := h₁
    obtain ⟨m₂, tt₂, tr₂, hB₂, hR₂, rfl⟩ := h₂
    obtain ⟨tb₁, rfl, hb₁, hagT₁, hretT₁⟩ := hent hag₁ hret₁ hB₁
    obtain ⟨tb₂, rfl, hb₂, hagT₂, hretT₂⟩ := hent hag₂ hret₂ hB₂
    have hce_eq := hceq env₁ rs₁ env₂ rs₂ j hjD hag₁ hag₂
    rcases hbr₁ : (denote' bi (n + 1) body).run (env₁.extend i (.int (cnt j))) with ⟨ob₁, e2₁⟩
    rcases hbr₂ : (denote' bi (n + 1) body).run (env₂.extend i (.int (cnt j))) with ⟨ob₂, e2₂⟩
    have hvb : ∀ {env env' e2 : Env} {o ob : Outcome},
        (denote' bi (n + 1) body).run (env.extend i (.int (cnt j))) = (ob, e2) →
        L (n + 1) j env = (o, env') → (∃ v, o = .val v) → ∃ w, ob = .val w := by
      intro env env' e2 o ob hbr hrun hval
      cases ob with
      | val w => exact ⟨w, rfl⟩
      | _ =>
        rw [hLo n j env _ e2 hjD hbr (fun v h => by cases h)] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        obtain ⟨_, h⟩ := hval; cases h
    obtain ⟨w₁, rfl⟩ := hvb hbr₁ hrun₁ hval₁
    obtain ⟨w₂, rfl⟩ := hvb hbr₂ hrun₂ hval₂
    rw [hT n j env₁ hjD, hT n j env₂ hjD, hbr₁, hbr₂] at hL
    injection hL with hLbody hLrest
    obtain ⟨htb, hst⟩ := bodyStepAg hR hC hagT₁ hretT₁ hagT₂ hretT₂ hbr₁ hbr₂ hLbody hb₁ hb₂
    rcases hst with ⟨-, -, hf₁, hf₂⟩ | ⟨hcf₁, hcf₂, h01, hagq₁, h02, hagq₂⟩
    · obtain ⟨rfl, hr₁⟩ := exitedTripsL M N leafSpec run _ hslot d (j + 1) m₁ r₁ tr₁ hf₁ hR₁
      obtain ⟨rfl, hr₂⟩ := exitedTripsL M N leafSpec run _ hslot d (j + 1) m₂ r₂ tr₂ hf₂ hR₂
      exact ⟨by rw [hce_eq, htb], hr₁.trans hr₂.symm⟩
    · rw [tripCont_val hcf₁, tripCont_val hcf₂] at hLrest
      rw [hLi n j env₁ w₁ e2₁ hjD hbr₁ hcf₁] at hrun₁
      rw [hLi n j env₂ w₂ e2₂ hjD hbr₂ hcf₂] at hrun₂
      obtain ⟨htr, hr⟩ := IH (j + 1) n e2₁ e2₂ env₁' env₂' o₁ o₂ m₁ m₂ r₁ r₂ tr₁ tr₂ (by omega)
        hrun₁ hval₁ hrun₂ hval₂ hagq₁ h01 hagq₂ h02 hLrest hR₁ hR₂
      exact ⟨by rw [hce_eq, htb, htr], hr⟩

/-- `genForCT` with the loop entry of `exitForLoopRt`: the trip count is read from the
    slot `hv`, which holds `H` in both runs. -/
theorem genForLoopRtCT (hres : AgReserved Ag) (Lf : Nat → Int → Env → Outcome × Env)
    (run i : String) (lo : Nat) (hv : String) (H : Nat) (body : ImpExpr) (bC : LowCT)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false)
    (hh_ : exitReserved hv = false) (hH : H < 2 ^ 64)
    (hext : ∀ env rs (k : Nat), k < 2 ^ 64 → Ag env rs →
      Ag (env.extend i (.int k)) (rsSetScalar rs i k))
    (hL0 : ∀ (k : Int) env v, k < H → (Lf 0 k env).1 ≠ .val v)
    (hLo : ∀ n (k : Int) env o e2, k < H →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (o, e2) →
      (∀ v, o ≠ .val v) → Lf (n + 1) k env = (o, e2))
    (hLi : ∀ n (k : Int) env w e2, k < H →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (.val w, e2) →
      w.isControlFlow = false → Lf (n + 1) k env = Lf n (k + 1) e2)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : Lf fuel lo env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : Lf fuel lo env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : Ag env₁ rs₁) (hag₂ : Ag env₂ rs₂)
    (hd₁ : rs₁.rsScalar hv = H) (hd₂ : rs₂.rsScalar hv = H)
    (hL : forLeak bi i body (srcLeak M bi body) fuel lo H env₁ =
      forLeak bi i body (srcLeak M bi body) fuel lo H env₂)
    (h₁ : RustExecLeak N leafSpec M (exitForLoopRt run i lo hv bC) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (exitForLoopRt run i lo hv bC) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hent : ∀ {rs : RustState}, rs.rsScalar hv = H →
      (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar hv = H := by
    intro rs h
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hh_ exitReserved_val), rsScalar_rsSetScalar,
      if_neg (ne_of_reserved hh_ exitReserved_ret), h]
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₁ with
  | forRuntime _ _ _ _ _ tr₁ h₁ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  cases h₂ with
  | forRuntime _ _ _ _ _ tr₂ h₂ =>
  have he₁ := hent hd₁
  have he₂ := hent hd₂
  have hb₁ : (SExpr.SSub (.SVar hv) (.SLit lo)).evalState
      (rsSetScalar (rsSetScalar rs₁ exitRetName 0) exitValName 0) = H - lo := by
    simp only [SExpr.evalState, he₁]
  have hb₂ : (SExpr.SSub (.SVar hv) (.SLit lo)).evalState
      (rsSetScalar (rsSetScalar rs₂ exitRetName 0) exitValName 0) = H - lo := by
    simp only [SExpr.evalState, he₂]
  rw [hb₁] at h₁ ⊢
  rw [hb₂] at h₂ ⊢
  obtain ⟨hag₁', hret₁'⟩ := genForEntry hres hag₁
  obtain ⟨hag₂', hret₂'⟩ := genForEntry hres hag₂
  obtain ⟨ht, hr⟩ := genForCT hres Lf run i lo H body bC hR hC hslot hi_ hH.le hext hL0 hLo hLi
    fuel env₁ env₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ tr₁ tr₂ hrun₁ hval₁ hrun₂ hval₂ hag₁' hret₁'
    hag₂' hret₂' hL h₁ h₂
  refine ⟨?_, hr⟩
  rw [ht, sexprLeak_congr M (S := fun x => x = hv)
    (fun x hx => by subst hx; exact he₁.trans he₂.symm) (.SSub (.SVar hv) (.SLit lo))
    ⟨rfl, trivial⟩]

/-- **The lowered upward counted loop with bounds read at run time**: the loop entry zeroes
    the flag and payload slots, reads the trip count `hiE - loE`, which is `H - lo` in both
    runs with equal events (`hb₁`, `hb₂`, `hbl`), and runs the trips binding the counter to
    `run + loE`, where `loE` reads `lo` with equal events from states agreeing with an
    environment (`hlo`, `hloq`). -/
theorem genForLoopVCT (hres : AgReserved Ag) (Lf : Nat → Int → Env → Outcome × Env)
    (run i : String) (loE hiE : SExpr) (lo H : Nat) (body : ImpExpr) (bC : LowCT)
    (hR : BodyRunAg M bi N leafSpec Ag body bC) (hC : BodyCTAg M bi N leafSpec Ag body bC)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false)
    (hext : ∀ env rs (k : Nat), k < 2 ^ 64 → Ag env rs →
      Ag (env.extend i (.int k)) (rsSetScalar rs i k))
    (hlo : ∀ env rs j, Ag env rs → loE.evalState (rsSetScalar (rsSetScalar rs run j) i 0) = lo)
    (hloq : ∀ env₁ rs₁ env₂ rs₂ j, Ag env₁ rs₁ → Ag env₂ rs₂ →
      sexprLeak M (rsSetScalar (rsSetScalar rs₁ run j) i 0) loE =
        sexprLeak M (rsSetScalar (rsSetScalar rs₂ run j) i 0) loE)
    (hH : H < 2 ^ 64)
    (hL0 : ∀ (k : Int) env v, k < H → (Lf 0 k env).1 ≠ .val v)
    (hLo : ∀ n (k : Int) env o e2, k < H →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (o, e2) →
      (∀ v, o ≠ .val v) → Lf (n + 1) k env = (o, e2))
    (hLi : ∀ n (k : Int) env w e2, k < H →
      (denote' bi (n + 1) body).run (env.extend i (.int k)) = (.val w, e2) →
      w.isControlFlow = false → Lf (n + 1) k env = Lf n (k + 1) e2)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : Lf fuel lo env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : Lf fuel lo env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : Ag env₁ rs₁) (hag₂ : Ag env₂ rs₂)
    (hb₁ : (SExpr.SSub hiE loE).evalState
      (rsSetScalar (rsSetScalar rs₁ exitRetName 0) exitValName 0) = H - lo)
    (hb₂ : (SExpr.SSub hiE loE).evalState
      (rsSetScalar (rsSetScalar rs₂ exitRetName 0) exitValName 0) = H - lo)
    (hbl : sexprLeak M (rsSetScalar (rsSetScalar rs₁ exitRetName 0) exitValName 0)
        (.SSub hiE loE) =
      sexprLeak M (rsSetScalar (rsSetScalar rs₂ exitRetName 0) exitValName 0) (.SSub hiE loE))
    (hL : forLeak bi i body (srcLeak M bi body) fuel lo H env₁ =
      forLeak bi i body (srcLeak M bi body) fuel lo H env₂)
    (h₁ : RustExecLeak N leafSpec M (.RLetU64Zero exitRetName (.RLetU64Zero exitValName
      (.RForRuntime run (.SSub hiE loE)
        (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i (.SAdd (.SVar run) loE)) bC))))))
      rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (.RLetU64Zero exitRetName (.RLetU64Zero exitValName
      (.RForRuntime run (.SSub hiE loE)
        (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i (.SAdd (.SVar run) loE)) bC))))))
      rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hcast : ∀ j : Nat, ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 := by
    intro j; push_cast; ring
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₁ with
  | forRuntime _ _ _ _ _ tr₁ h₁ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  cases h₂ with
  | forRuntime _ _ _ _ _ tr₂ h₂ =>
  rw [hb₁] at h₁
  rw [hb₂] at h₂
  obtain ⟨hag₁', hret₁'⟩ := genForEntry hres hag₁
  obtain ⟨hag₂', hret₂'⟩ := genForEntry hres hag₂
  have hev : ∀ env rs j, Ag env rs →
      (SExpr.SAdd (.SVar run) loE).evalState (rsSetScalar (rsSetScalar rs run j) i 0) =
        lo + j := by
    intro env rs j hag
    simp only [SExpr.evalState, hlo env rs j hag, rsScalar_rsSetScalar, if_neg hir.symm,
      if_true]
    omega
  obtain ⟨ht, hr⟩ := genTripsCTAg hres run i body bC (.SAdd (.SVar run) loE)
    (fun j => lo + j) (H - lo) (fun n j env => Lf n ((lo + j : Nat) : Int) env)
    (fun n j env => forLeak bi i body (srcLeak M bi body) n ((lo + j : Nat) : Int) H env)
    hR hC hslot hi_ (fun env rs j hj hag => hext env rs _ (by omega) hag)
    (fun env rs j _ hag => hev env rs j hag)
    (fun env₁ rs₁ env₂ rs₂ j _ hag₁ hag₂ => by
      simp only [sexprLeak, hloq env₁ rs₁ env₂ rs₂ j hag₁ hag₂]
      unfold CatCrypt.Crypto.SecureCompilation.CT.nodeLeak
      simp only [SExpr.evalState, hlo env₁ rs₁ j hag₁, hlo env₂ rs₂ j hag₂,
        rsScalar_rsSetScalar, if_neg hir.symm, if_true])
    (fun j env v hj => hL0 _ env v (by omega))
    (fun n j env o e2 hj hbr ho => hLo n _ env o e2 (by omega) hbr ho)
    (fun n j env w e2 hj hbr hw => by
      rw [hLi n _ env w e2 (by omega) hbr hw, hcast])
    (fun n j env hj => by
      rw [forLeak, if_neg (by omega), hcast])
    (H - lo) 0 fuel env₁ env₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ tr₁ tr₂ (by omega)
    (by simpa using hrun₁) hval₁ (by simpa using hrun₂) hval₂ hag₁' hret₁' hag₂' hret₂'
    (by simpa using hL) (rFor_tripsL M N leafSpec _ _ _ _ r₁ tr₁ h₁)
    (rFor_tripsL M N leafSpec _ _ _ _ r₂ tr₂ h₂)
  exact ⟨by rw [ht, hbl, hb₁, hb₂], hr⟩

end Generic

end CatCrypt.Crypto.Hax
