/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxSourceLeak
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit -- deprecated_module: ignore

/-!
# The exit-flag lowering preserves constant time

For an expression of the fragment `exitSimOk`, two runs of `denote'` that end in a value,
from environments whose source leakages (`srcLeak`) are equal, are matched by runs of the
lowered program `haxToLowCTK true` with equal `RustExecLeak` traces. With `SourceCT`, two
runs from environments agreeing on the public variables have equal target traces.

`ExitCT e` is that statement for `e`, from states agreeing with the environments off the
reserved names (`envAgreesOff`) with the exit flag `0`. Its conclusion also states that
the two source runs agree on whether they end in an exit (`exitOf`), which the enclosing
`seq` and loops read. The states the target runs reach after a part are those of the
simulation `haxToLowCTK_simulates` (by determinism of `RustExecLeak`), so each arm reads
the agreement it needs from the simulation and only follows the traces.

Loops are proved once per target shape: `exitLoopCT` for the `RWhileNz` of
`whileFoldReturn` and of a breaking `whileFold`, by induction on fuel; `exitTripsCT` for
the guarded trips of a counted loop, by induction on the trips left, with the traced
trips `TripsL` of `RFor` (`rFor_tripsL`). Each is stated for any source loop that
unfolds as `denote'`'s loops do, and instantiated at `denoteWhile'Return`,
`denoteWhile'`, `denoteForLoop'Return`, `denoteForLoop'` and
`denoteForLoopRev'Return`. After an exit the remaining trips of a counted loop each
leave one `branch true` event (`exitedTripsL`), the same number in both runs.

The statement covers target runs whose source counterparts end in a value; it says
nothing about a target run from a state that agrees with no such source run.

## Main definitions

* `exitOf` — whether an outcome is an exit, `val (controlFlow true _)`
* `ExitCT` — the two-run trace equality of the lowering of an expression
* `TripsL` — traced trips of a counted loop

## Main results

* `envAgreesExit_flag` — the exit flag after a simulated run is `1` exactly at an exit
* the arms `exitCT_var`, `exitCT_unitVal`, `exitCT_lit`, `exitCT_cfBreak`,
  `exitCT_letBind_lit`, `exitCT_letBind_var`, `exitCT_letBind_app`, `exitCT_seq`,
  `exitCT_ifThenElse`, `exitCT_whileFoldReturn`, `exitCT_whileFold`,
  `exitCT_forFoldReturn`, `exitCT_forFoldRevReturn`, `exitCT_forFold`
* `haxToLowCTK_ct` — every expression satisfies `ExitCT`
* `haxToLowCTFn_leak_eq`, `haxToLowCTFn_ct` — the lowered function: equal source
  leakage, and source constant time, give equal traces
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak LowCTLeakModel sexprLeak RustExecLeak)

/-! ## Exits and the exit flag -/

/-- Whether an outcome is an exit: a value `controlFlow true _`. -/
def exitOf : Outcome → Bool
  | .val (.controlFlow true _) => true
  | _ => false

/-- After a run agreeing with an outcome, the exit flag is `1` at an exit and `0`
    otherwise. -/
theorem envAgreesExit_flag {tl : Bool} {o : Outcome} {env : Env} {rs : RustState}
    (h : envAgreesExit tl o env rs) :
    rs.rsScalar exitRetName = if exitOf o then 1 else 0 := by
  cases o with
  | val v =>
    cases v with
    | controlFlow b w =>
      cases b with
      | false => exact h.elim
      | true => exact h.1
    | _ => exact h.1
  | _ => exact h.elim

/-- Two agreeing runs whose final exit flags are equal agree on the exit. -/
theorem exitOf_eq_of_flag {tl₁ tl₂ : Bool} {o₁ o₂ : Outcome} {env₁ env₂ : Env}
    {r₁ r₂ : RustState} (h₁ : envAgreesExit tl₁ o₁ env₁ r₁) (h₂ : envAgreesExit tl₂ o₂ env₂ r₂)
    (h : r₁.rsScalar exitRetName = r₂.rsScalar exitRetName) : exitOf o₁ = exitOf o₂ := by
  rw [envAgreesExit_flag h₁, envAgreesExit_flag h₂] at h
  revert h
  cases exitOf o₁ <;> cases exitOf o₂ <;> simp

theorem contLeak_val {w : Value} (hw : w.isControlFlow = false) (e1 : Env)
    (k : Value → Env → SrcLeak) : contLeak (.val w, e1) k = k w e1 := by
  cases w <;> first | rfl | simp at hw

/-! ## The statement -/

section Stmt

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)

/-- **Constant-time preservation of the lowering of `e`.** Two runs of `e` ending in a
    value, from environments with equal source leakage, and two runs of the lowered
    program from states agreeing with them with the exit flag `0`, have equal traces,
    and the source runs agree on whether they exit. -/
def ExitCT (e : ImpExpr) : Prop :=
  ∀ (tl : Bool) (fl : Option String) (fuel : Nat) (env₁ env₂ env₁' env₂' : Env)
    (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState) (c : LowCT) (x : Bool)
    (t₁ t₂ : List CTLeak),
    exitSimOk tl fl.isSome e = true → RunCtx fl →
    haxToLowCTK true tl fl e = some (c, x) →
    (denote' bi fuel e).run env₁ = (o₁, env₁') → (∃ v, o₁ = .val v) →
    (denote' bi fuel e).run env₂ = (o₂, env₂') → (∃ v, o₂ = .val v) →
    envAgreesOff env₁ rs₁ → rs₁.rsScalar exitRetName = 0 →
    envAgreesOff env₂ rs₂ → rs₂.rsScalar exitRetName = 0 →
    srcLeak M bi e fuel env₁ = srcLeak M bi e fuel env₂ →
    RustExecLeak N leafSpec M c rs₁ t₁ r₁ → RustExecLeak N leafSpec M c rs₂ t₂ r₂ →
    t₁ = t₂ ∧ exitOf o₁ = exitOf o₂

/-- The state a traced run of a simulated expression reaches agrees with the source
    outcome. -/
theorem exitSim_final {e : ImpExpr} (hsim : ExitSim bi N leafSpec e) {tl : Bool}
    {fl : Option String} {fuel : Nat} {env env' : Env} {o : Outcome} {rs r : RustState}
    {c : LowCT} {x : Bool} {t : List CTLeak}
    (hok : exitSimOk tl fl.isSome e = true) (hfl : RunCtx fl)
    (hK : haxToLowCTK true tl fl e = some (c, x))
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesOff env rs) (hret : rs.rsScalar exitRetName = 0)
    (h : RustExecLeak N leafSpec M c rs t r) :
    envAgreesExit tl o env' r ∧ (x = false → r.rsScalar exitRetName = 0) := by
  obtain ⟨rs', hex, hagE, hx⟩ := hsim tl fl fuel env env' o rs c x hok hfl hK hrun hval hag hret
  obtain rfl := rustExecLeak_state_eq h hex
  exact ⟨hagE, hx⟩

/-- An expression whose lowering cannot exit: the source runs do not exit. -/
theorem exitOf_false_of_x {e : ImpExpr} (hsim : ExitSim bi N leafSpec e) {tl : Bool}
    {fl : Option String} {fuel : Nat} {env env' : Env} {o : Outcome} {rs r : RustState}
    {c : LowCT} {t : List CTLeak}
    (hok : exitSimOk tl fl.isSome e = true) (hfl : RunCtx fl)
    (hK : haxToLowCTK true tl fl e = some (c, false))
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesOff env rs) (hret : rs.rsScalar exitRetName = 0)
    (h : RustExecLeak N leafSpec M c rs t r) : exitOf o = false := by
  obtain ⟨hE, hx⟩ := exitSim_final M bi N leafSpec hsim hok hfl hK hrun hval hag hret h
  have h0 := hx rfl
  rw [envAgreesExit_flag hE] at h0
  cases hc : exitOf o
  · rfl
  · rw [hc] at h0; simp at h0

end Stmt

/-! ## The arms -/

section Arms

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (hsim : ∀ e, ExitSim bi N leafSpec e)
include hsim

theorem exitCT_var (x : String) : ExitCT M bi N leafSpec (.var x) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ _ h₁ h₂
  have hx : haxToLowCTK true tl fl (.var x) =
      some (if tl then .RScalarSetExpr exitResName (.SVar x) else .RSkip, false) := by
    cases tl <;> cases fl <;> rfl
  rw [hx] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  refine ⟨?_, by
    rw [exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hx hrun₁ hval₁ hag₁ hret₁ h₁,
      exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hx hrun₂ hval₂ hag₂ hret₂ h₂]⟩
  cases tl
  · cases h₁; cases h₂; rfl
  · cases h₁; cases h₂; rfl

theorem exitCT_unitVal : ExitCT M bi N leafSpec .unitVal := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ _ h₁ h₂
  have hx : haxToLowCTK true tl fl .unitVal =
      some (if tl then .RScalarSet exitResName 0 else .RSkip, false) := by
    cases tl <;> cases fl <;> rfl
  rw [hx] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  refine ⟨?_, by
    rw [exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hx hrun₁ hval₁ hag₁ hret₁ h₁,
      exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hx hrun₂ hval₂ hag₂ hret₂ h₂]⟩
  cases tl
  · cases h₁; cases h₂; rfl
  · cases h₁; cases h₂; rfl

theorem exitCT_lit (l : ImpLit) : ExitCT M bi N leafSpec (.lit l) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ _ h₁ h₂
  cases tl with
  | false => cases fl <;> simp [exitSimOk] at hok
  | true =>
    cases l with
    | uintLit w k =>
      cases w <;> try (cases fl <;> simp [exitSimOk] at hok; done)
      have hx : haxToLowCTK true true fl (.lit (.uintLit .w64 k)) =
          some (.RScalarSet exitResName (k % IntWidth.w64.modulus), false) := by
        cases fl <;> rfl
      rw [hx] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      refine ⟨by cases h₁; cases h₂; rfl, ?_⟩
      rw [exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hx hrun₁ hval₁ hag₁ hret₁ h₁,
        exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hx hrun₂ hval₂ hag₂ hret₂ h₂]
    | _ => cases fl <;> simp [exitSimOk] at hok

theorem exitCT_cfBreak (e : ImpExpr) : ExitCT M bi N leafSpec (.cfBreak e) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ _ h₁ h₂
  cases fl with
  | none => cases tl <;> simp [exitSimOk] at hok
  | some r =>
    obtain ⟨hE₁, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
    obtain ⟨hE₂, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
    obtain ⟨s, hs, rfl⟩ : ∃ s, storeScalar exitValName e = some s ∧
        c = .RSeq s (.RScalarSet exitRetName 1) := by
      cases tl <;>
      · simp only [haxToLowCTK, exitStore, Option.map_eq_some_iff, Prod.mk.injEq] at hK
        obtain ⟨_, ⟨s, hs, rfl⟩, rfl, -⟩ := hK
        exact ⟨s, hs, rfl⟩
    have hnil : ∀ {rs r : RustState} {t : List CTLeak}, RustExecLeak N leafSpec M
        (.RSeq s (.RScalarSet exitRetName 1)) rs t r → t = [] ∧ r.rsScalar exitRetName = 1 := by
      intro rs r t h
      cases h with
      | seq _ _ _ r1 _ ta tb ha hb =>
        cases hb
        refine ⟨?_, by simp⟩
        cases e with
        | var y => simp only [storeScalar, Option.some.injEq] at hs; subst hs; cases ha; rfl
        | lit l =>
          cases l <;> simp only [storeScalar, Option.some.injEq] at hs <;>
            (try split at hs) <;> (try simp only [Option.some.injEq] at hs) <;>
            (try cases hs) <;> cases ha <;> rfl
        | unitVal => simp only [storeScalar, Option.some.injEq] at hs; subst hs; cases ha; rfl
        | _ => simp [storeScalar] at hs
    obtain ⟨ht₁, hf₁⟩ := hnil h₁
    obtain ⟨ht₂, hf₂⟩ := hnil h₂
    exact ⟨ht₁.trans ht₂.symm, exitOf_eq_of_flag hE₁ hE₂ (hf₁.trans hf₂.symm)⟩

omit hsim in
theorem exitCT_letBind_lit (n : String) (l : ImpLit) (body : ImpExpr)
    (ihb : ExitCT M bi N leafSpec body) : ExitCT M bi N leafSpec (.letBind n (.lit l) body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  obtain ⟨v, k, hv, hsv, hk, hhead, hn, hokB⟩ :
      ∃ v k, Value.ofLit l = v ∧ ScalarVal v ∧ valueToScalar v = some k ∧
        letHeadK true n (.lit l) =
          some (fun bC => .RLetU64Zero n (.RSeq (.RScalarSet n k) bC)) ∧
        exitReserved n = false ∧ exitSimOk tl fl.isSome body = true := by
    cases l with
    | uintLit w k =>
      cases w <;> try (cases tl <;> cases fl <;> simp [exitSimOk] at hok; done)
      have hh : exitReserved n = false ∧ exitSimOk tl fl.isSome body = true := by
        cases tl <;> cases fl <;>
          simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] using hok
      exact ⟨_, k % IntWidth.w64.modulus, rfl, Nat.mod_lt _ (by decide), rfl, rfl, hh⟩
    | bool b =>
      have hh : exitReserved n = false ∧ exitSimOk tl fl.isSome body = true := by
        cases tl <;> cases fl <;>
          simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] using hok
      exact ⟨_, if b then 1 else 0, rfl, trivial, valueToScalar_bool b, rfl, hh⟩
    | int k =>
      have hh : (0 ≤ k ∧ k < 2 ^ 64) ∧ exitReserved n = false ∧
          exitSimOk tl fl.isSome body = true := by
        cases tl <;> cases fl <;>
          simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
            and_assoc] using hok
      obtain ⟨⟨h0, h1⟩, hh⟩ := hh
      refine ⟨_, k.toNat, rfl, ⟨h0, h1⟩, by simp [valueToScalar, Value.ofLit, h0], ?_, hh⟩
      simp [letHeadK, letHead, h0]
    | _ => cases tl <;> cases fl <;> simp [exitSimOk] at hok
  have hrv : ∀ env, (denote' bi fuel (.lit l)).run env = (.val v, env) := fun env => by
    rw [denote'_lit_run, hv]
  rw [denote'_letBind_run_val bi fuel n _ body env₁ env₁ v (hrv env₁) hsv.not_cf] at hrun₁
  rw [denote'_letBind_run_val bi fuel n _ body env₂ env₂ v (hrv env₂) hsv.not_cf] at hrun₂
  simp only [srcLeak, hrv, contLeak_val hsv.not_cf] at hL
  injection hL with _ hLb
  rw [haxToLowCTK_letBind_eq, hhead] at hK
  rcases hB : haxToLowCTK true tl fl body with _ | ⟨bC, x⟩
  · rw [hB] at hK; cases hK
  rw [hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  have hret' : ∀ rs : RustState, rs.rsScalar exitRetName = 0 →
      (rsSetScalar rs n k).rsScalar exitRetName = 0 := fun rs h => by
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn exitReserved_ret).symm, h]
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
    cases h₁ with
    | seq _ _ _ _ _ _ tb₁ hs₁ hb₁ =>
      cases hs₁
      cases h₂ with
      | letU64Zero _ _ _ _ _ h₂ =>
        cases h₂ with
        | seq _ _ _ _ _ _ tb₂ hs₂ hb₂ =>
          cases hs₂
          rw [rsSetScalar_rsSetScalar] at hb₁ hb₂
          obtain ⟨ht, hx⟩ := ihb tl fl fuel _ _ env₁' env₂' o₁ o₂ _ _ r₁ r₂ bC x tb₁ tb₂ hokB hfl
            hB hrun₁ hval₁ hrun₂ hval₂ (envAgreesOff_extend hn hsv hk hag₁) (hret' _ hret₁)
            (envAgreesOff_extend hn hsv hk hag₂) (hret' _ hret₂) hLb hb₁ hb₂
          exact ⟨by rw [ht], hx⟩

omit hsim in
theorem exitCT_letBind_var (n s : String) (body : ImpExpr)
    (ihb : ExitCT M bi N leafSpec body) : ExitCT M bi N leafSpec (.letBind n (.var s) body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  have hh : exitReserved n = false ∧ exitReserved s = false ∧
      exitSimOk tl fl.isSome body = true := by
    cases tl <;> cases fl <;>
      simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using hok
  obtain ⟨hn, hs, hokB⟩ := hh
  have hget : ∀ {env env' : Env} {o : Outcome},
      (denote' bi fuel (.letBind n (.var s) body)).run env = (o, env') → (∃ v, o = .val v) →
      ∃ w, env s = some w := by
    intro env env' o hrun hval
    cases hw : env s with
    | none =>
      rw [denote'_letBind_run_nonval bi fuel n _ body env env _
        (by rw [denote'_var_run, hw]) (fun _ h => by cases h)] at hrun
      obtain ⟨v, rfl⟩ := hval
      cases hrun
    | some w => exact ⟨w, rfl⟩
  obtain ⟨w₁, hw₁⟩ := hget hrun₁ hval₁
  obtain ⟨w₂, hw₂⟩ := hget hrun₂ hval₂
  obtain ⟨hsv₁, hk₁⟩ := hag₁ s w₁ hs hw₁
  obtain ⟨hsv₂, hk₂⟩ := hag₂ s w₂ hs hw₂
  have hr₁ : (denote' bi fuel (.var s)).run env₁ = (.val w₁, env₁) := by
    rw [denote'_var_run, hw₁]
  have hr₂ : (denote' bi fuel (.var s)).run env₂ = (.val w₂, env₂) := by
    rw [denote'_var_run, hw₂]
  rw [denote'_letBind_run_val bi fuel n _ body env₁ env₁ w₁ hr₁ hsv₁.not_cf] at hrun₁
  rw [denote'_letBind_run_val bi fuel n _ body env₂ env₂ w₂ hr₂ hsv₂.not_cf] at hrun₂
  simp only [srcLeak, hr₁, hr₂, contLeak_val hsv₁.not_cf, contLeak_val hsv₂.not_cf] at hL
  injection hL with _ hLb
  rw [haxToLowCTK_letBind_eq] at hK
  rcases hB : haxToLowCTK true tl fl body with _ | ⟨bC, x⟩
  · rw [hB] at hK
    rcases letHeadK true n (.var s) with _ | k <;> simp at hK
  rw [hB] at hK
  by_cases hns : n = s
  · subst hns
    simp only [letHeadK, letHead, if_true, id, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [Env.extend_self env₁ n w₁ hw₁] at hrun₁ hLb
    rw [Env.extend_self env₂ n w₂ hw₂] at hrun₂ hLb
    exact ihb tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ bC x t₁ t₂ hokB hfl hB
      hrun₁ hval₁ hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hLb h₁ h₂
  · simp only [letHeadK, letHead, hns, if_false, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    have hmid : ∀ rs : RustState, rsSetScalar (rsSetScalar rs n 0) n
        ((SExpr.SVar s).evalState (rsSetScalar rs n 0)) = rsSetScalar rs n (rs.rsScalar s) := by
      intro rs
      rw [rsSetScalar_rsSetScalar]
      simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg (Ne.symm hns)]
    have hret' : ∀ rs : RustState, rs.rsScalar exitRetName = 0 →
        (rsSetScalar rs n (rs.rsScalar s)).rsScalar exitRetName = 0 := fun rs h => by
      rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn exitReserved_ret).symm, h]
    cases h₁ with
    | letU64Zero _ _ _ _ _ h₁ =>
      cases h₁ with
      | seq _ _ _ _ _ _ tb₁ hs₁ hb₁ =>
        cases hs₁
        cases h₂ with
        | letU64Zero _ _ _ _ _ h₂ =>
          cases h₂ with
          | seq _ _ _ _ _ _ tb₂ hs₂ hb₂ =>
            cases hs₂
            rw [hmid] at hb₁ hb₂
            obtain ⟨ht, hx⟩ := ihb tl fl fuel _ _ env₁' env₂' o₁ o₂ _ _ r₁ r₂ bC x tb₁ tb₂ hokB
              hfl hB hrun₁ hval₁ hrun₂ hval₂ (envAgreesOff_extend hn hsv₁ hk₁ hag₁)
              (hret' _ hret₁) (envAgreesOff_extend hn hsv₂ hk₂ hag₂) (hret' _ hret₂) hLb hb₁ hb₂
            exact ⟨by simp only [sexprLeak, List.nil_append, ht], hx⟩

omit hsim in
theorem exitCT_letBind_app (hs : ScalarOpsSound bi) (n op a b : String) (body : ImpExpr)
    (ihb : ExitCT M bi N leafSpec body) :
    ExitCT M bi N leafSpec (.letBind n (.app op [.var a, .var b]) body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  have hok' : (scalarOpExpr op (.SVar a) (.SVar b)).isSome = true ∧ exitReserved n = false ∧
      exitReserved a = false ∧ exitReserved b = false ∧
      exitSimOk tl fl.isSome body = true := by
    cases tl <;> cases fl <;>
      (simp only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1.1, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩)
  obtain ⟨hop, hn, ha', hb', hokB⟩ := hok'
  obtain ⟨se, hse⟩ := Option.isSome_iff_exists.mp hop
  -- one run: the operation's value, the body's run and the head's leakage
  have side : ∀ {env env' : Env} {o : Outcome} {rs : RustState},
      (denote' bi fuel (.letBind n (.app op [.var a, .var b]) body)).run env = (o, env') →
      (∃ v, o = .val v) → envAgreesOff env rs →
      ∃ r, ScalarVal r ∧ valueToScalar r = some (se.evalState rs) ∧
        (denote' bi fuel body).run (env.extend n r) = (o, env') ∧
        srcLeak M bi (.letBind n (.app op [.var a, .var b]) body) fuel env =
          .cat (.ev (.op (sexprLeak M rs se))) (srcLeak M bi body fuel (env.extend n r)) := by
    intro env env' o rs hrun hval hag
    have herr : ∀ msg e1,
        (denote' bi fuel (.app op [.var a, .var b])).run env = (.err msg, e1) → False := by
      intro msg e1 h
      rw [denote'_letBind_run_nonval bi fuel n _ body env e1 _ h (fun v hv => by cases hv)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    cases hva : env a with
    | none =>
      obtain ⟨msg, h⟩ := denote'_app2_run_none_left bi fuel op a b env hva
      exact (herr msg env h).elim
    | some va =>
      obtain ⟨hsa, hda⟩ := hag a va ha' hva
      cases hvb : env b with
      | none =>
        obtain ⟨msg, h⟩ := denote'_app2_run_none_right bi fuel op a b env va hva hsa.not_cf hvb
        exact (herr msg env h).elim
      | some vb =>
        obtain ⟨hsb, hdb⟩ := hag b vb hb' hvb
        have happ := denote'_app2_run bi fuel op a b env va vb hva hvb hsa.not_cf hsb.not_cf
        cases hbi : bi op [va, vb] with
        | none => rw [hbi] at happ; exact (herr _ env happ).elim
        | some r =>
          rw [hbi] at happ
          have hop' := hop
          rw [scalarOpExpr_isSome_vars op a b "a" "b"] at hop'
          obtain ⟨hsr, hdr⟩ := hs op va vb r _ _ hop' hsa hsb hda hdb hbi
          rw [denote'_letBind_run_val bi fuel n _ body env env r happ hsr.not_cf] at hrun
          refine ⟨r, hsr, ?_, hrun, ?_⟩
          · rw [scalarOpExpr_evalState op a b se rs hse, scalarOpExpr_eval op a b se _ hse]
            exact hdr
          · have hS : ∀ x, (x = a ∨ x = b) →
                rs.rsScalar x = (envScalarState env).rsScalar x := by
              rintro x (rfl | rfl)
              · simp only [envScalarState, hva, Option.bind_some, hda, Option.getD_some]
              · simp only [envScalarState, hvb, Option.bind_some, hdb, Option.getD_some]
            simp only [srcLeak, opLeak, hse, happ, contLeak_val hsr.not_cf,
              sexprLeak_congr M hS se (scalarOpExpr_readsOnly hse)]
  obtain ⟨w₁, hsv₁, hk₁, hrun₁, hL₁⟩ := side hrun₁ hval₁ hag₁
  obtain ⟨w₂, hsv₂, hk₂, hrun₂, hL₂⟩ := side hrun₂ hval₂ hag₂
  rw [hL₁, hL₂] at hL
  injection hL with hLa hLb
  injection hLa with hLa
  injection hLa with hLa
  have hhead : letHeadK true n (.app op [.var a, .var b]) =
      some (fun bC => .RSeq (.RScalarSetExpr n se) bC) := by
    simp only [letHeadK, hse]
  rw [haxToLowCTK_letBind_eq, hhead] at hK
  rcases hB : haxToLowCTK true tl fl body with _ | ⟨bC, x⟩
  · rw [hB] at hK; cases hK
  rw [hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  have hret' : ∀ rs : RustState, rs.rsScalar exitRetName = 0 →
      (rsSetScalar rs n (se.evalState rs)).rsScalar exitRetName = 0 := fun rs h => by
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn exitReserved_ret).symm, h]
  cases h₁ with
  | seq _ _ _ _ _ _ tb₁ hs₁ hb₁ =>
    cases hs₁
    cases h₂ with
    | seq _ _ _ _ _ _ tb₂ hs₂ hb₂ =>
      cases hs₂
      obtain ⟨ht, hx⟩ := ihb tl fl fuel _ _ env₁' env₂' o₁ o₂ _ _ r₁ r₂ bC x tb₁ tb₂ hokB
        hfl hB hrun₁ hval₁ hrun₂ hval₂ (envAgreesOff_extend hn hsv₁ hk₁ hag₁)
        (hret' _ hret₁) (envAgreesOff_extend hn hsv₂ hk₂ hag₂) (hret' _ hret₂) hLb hb₁ hb₂
      exact ⟨by rw [hLa, ht], hx⟩

omit hsim in
/-- An exit outcome is a value `controlFlow true w`. -/
theorem exitOf_val_true {v : Value} (h : exitOf (.val v) = true) : ∃ w, v = .controlFlow true w := by
  cases v with
  | controlFlow b w => cases b with
    | true => exact ⟨w, rfl⟩
    | false => simp [exitOf] at h
  | _ => simp [exitOf] at h

omit hsim in
/-- An agreeing value that is not an exit is not a control-flow value. -/
theorem notCF_of_agree {tl : Bool} {v : Value} {env : Env} {rs : RustState}
    (h : envAgreesExit tl (.val v) env rs) (hx : exitOf (.val v) = false) :
    v.isControlFlow = false := by
  cases v with
  | controlFlow b w => cases b with
    | true => simp [exitOf] at hx
    | false => exact h.elim
  | _ => rfl

theorem exitCT_seq (a b : ImpExpr) (iha : ExitCT M bi N leafSpec a)
    (ihb : ExitCT M bi N leafSpec b) : ExitCT M bi N leafSpec (.seq a b) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  have hok' : exitSimOk false fl.isSome a = true ∧ exitSimOk tl fl.isSome b = true := by
    cases tl <;> cases fl <;> simpa only [exitSimOk, Bool.and_eq_true] using hok
  rw [haxToLowCTK_seq_eq] at hK
  rcases hA : haxToLowCTK true false fl a with _ | ⟨aC, xa⟩
  · rw [hA] at hK; cases hK
  rcases hB : haxToLowCTK true tl fl b with _ | ⟨bC, xb'⟩
  · rw [hA, hB] at hK; cases hK
  rw [hA, hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  have hav : ∀ {env env' : Env} {o : Outcome}, (denote' bi fuel (.seq a b)).run env = (o, env') →
      (∃ v, o = .val v) → ∃ va e1, (denote' bi fuel a).run env = (.val va, e1) := by
    intro env env' o hrun hval
    rcases hra : (denote' bi fuel a).run env with ⟨oa, e1⟩
    cases oa with
    | val va => exact ⟨va, e1, rfl⟩
    | _ =>
      rw [denote'_seq_run_nonval bi fuel a b env e1 _ hra (fun v h => by cases h)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
  obtain ⟨va₁, e1₁, hra₁⟩ := hav hrun₁ hval₁
  obtain ⟨va₂, e1₂, hra₂⟩ := hav hrun₂ hval₂
  simp only [srcLeak, hra₁, hra₂] at hL
  injection hL with hLa hLb
  obtain ⟨bC', hbc, rfl⟩ : ∃ bC', (if xa then LowCT.RSeq aC (exitGuard bC) else .RSeq aC bC) =
      .RSeq aC bC' ∧ bC' = (if xa then exitGuard bC else bC) := ⟨_, by cases xa <;> rfl, rfl⟩
  rw [hbc] at h₁ h₂
  cases h₁ with
  | seq _ _ _ m₁ _ ta₁ tb₁ hA₁ hB₁ =>
  cases h₂ with
  | seq _ _ _ m₂ _ ta₂ tb₂ hA₂ hB₂ =>
  obtain ⟨hta, hxa⟩ := iha false fl fuel env₁ env₂ e1₁ e1₂ _ _ rs₁ rs₂ m₁ m₂ aC xa ta₁ ta₂
    hok'.1 hfl hA hra₁ ⟨_, rfl⟩ hra₂ ⟨_, rfl⟩ hag₁ hret₁ hag₂ hret₂ hLa hA₁ hA₂
  obtain ⟨hE₁, hx₁⟩ := exitSim_final M bi N leafSpec (hsim a) hok'.1 hfl hA hra₁ ⟨_, rfl⟩
    hag₁ hret₁ hA₁
  obtain ⟨hE₂, hx₂⟩ := exitSim_final M bi N leafSpec (hsim a) hok'.1 hfl hA hra₂ ⟨_, rfl⟩
    hag₂ hret₂ hA₂
  have hf₁ := envAgreesExit_flag hE₁
  have hf₂ := envAgreesExit_flag hE₂
  cases hex₁ : exitOf (.val va₁) with
  | true =>
    have hex₂ : exitOf (.val va₂) = true := hxa ▸ hex₁
    obtain ⟨w₁, rfl⟩ := exitOf_val_true hex₁
    obtain ⟨w₂, rfl⟩ := exitOf_val_true hex₂
    rw [denote'_seq_run_cf bi fuel a b env₁ e1₁ true w₁ hra₁] at hrun₁
    rw [denote'_seq_run_cf bi fuel a b env₂ e1₂ true w₂ hra₂] at hrun₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun₂
    rw [hex₁] at hf₁
    rw [hex₂] at hf₂
    cases xa with
    | false => have h0 := hx₁ rfl; rw [hf₁] at h0; simp at h0
    | true =>
      simp only [if_true] at hB₁ hB₂
      have htb : ∀ {m r : RustState} {tb : List CTLeak}, m.rsScalar exitRetName = 1 →
          RustExecLeak N leafSpec M (exitGuard bC) m tb r → tb = [.branch true] := by
        intro m r tb hm h
        cases h with
        | ifTrue _ _ _ _ _ _ _ _ _ h => cases h; rfl
        | ifFalse _ _ _ _ _ _ h0 _ => rw [hm] at h0; simp at h0
      rw [htb (by simpa using hf₁) hB₁, htb (by simpa using hf₂) hB₂, hta]
      exact ⟨rfl, rfl⟩
  | false =>
    have hex₂ : exitOf (.val va₂) = false := hxa ▸ hex₁
    have hcf₁ := notCF_of_agree hE₁ hex₁
    have hcf₂ := notCF_of_agree hE₂ hex₂
    obtain ⟨h01, hagm₁, -⟩ := (envAgreesExit_val hcf₁).mp hE₁
    obtain ⟨h02, hagm₂, -⟩ := (envAgreesExit_val hcf₂).mp hE₂
    rw [denote'_seq_run_val bi fuel a b env₁ e1₁ va₁ hra₁ hcf₁] at hrun₁
    rw [denote'_seq_run_val bi fuel a b env₂ e1₂ va₂ hra₂ hcf₂] at hrun₂
    rw [contLeak_val hcf₁, contLeak_val hcf₂] at hLb
    cases xa with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hB₁ hB₂
      obtain ⟨htb, hxb⟩ := ihb tl fl fuel e1₁ e1₂ env₁' env₂' o₁ o₂ m₁ m₂ r₁ r₂ bC xb' tb₁ tb₂
        hok'.2 hfl hB hrun₁ hval₁ hrun₂ hval₂ hagm₁ h01 hagm₂ h02 hLb hB₁ hB₂
      exact ⟨by rw [hta, htb], hxb⟩
    | true =>
      simp only [if_true] at hB₁ hB₂
      cases hB₁ with
      | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ h01) hv0
      | ifFalse _ _ _ _ _ tb₁ _ hB₁ =>
      cases hB₂ with
      | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ h02) hv0
      | ifFalse _ _ _ _ _ tb₂ _ hB₂ =>
      obtain ⟨htb, hxb⟩ := ihb tl fl fuel e1₁ e1₂ env₁' env₂' o₁ o₂ m₁ m₂ r₁ r₂ bC xb' tb₁ tb₂
        hok'.2 hfl hB hrun₁ hval₁ hrun₂ hval₂ hagm₁ h01 hagm₂ h02 hLb hB₁ hB₂
      exact ⟨by rw [hta, htb], hxb⟩

omit hsim in
theorem exitCT_ifThenElse (v : String) (t e : ImpExpr) (iht : ExitCT M bi N leafSpec t)
    (ihe : ExitCT M bi N leafSpec e) : ExitCT M bi N leafSpec (.ifThenElse (.var v) t e) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  have hok' : exitReserved v = false ∧ exitSimOk tl fl.isSome t = true ∧
      exitSimOk tl fl.isSome e = true := by
    cases tl <;> cases fl <;>
      (simp only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1, hok.1.2, hok.2⟩)
  rw [haxToLowCTK_ifThenElse_eq] at hK
  rcases hT' : haxToLowCTK true tl fl t with _ | ⟨tC, xt⟩
  · rw [hT'] at hK; cases hK
  rcases hE : haxToLowCTK true tl fl e with _ | ⟨eC, xe⟩
  · rw [hT', hE] at hK; cases hK
  rw [hT', hE] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  have hb : ∀ {env env' : Env} {o : Outcome} {rs : RustState},
      (denote' bi fuel (.ifThenElse (.var v) t e)).run env = (o, env') → (∃ w, o = .val w) →
      envAgreesOff env rs →
      ∃ b, env v = some (.bool b) ∧ rs.rsScalar v = (if b then 1 else 0) := by
    intro env env' o rs hrun hval hag
    cases hvv : env v with
    | none =>
      rw [denote'_ifThenElse_var_run_none bi fuel v t e env hvv] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some w =>
      obtain ⟨hsw, hdw⟩ := hag v w hok'.1 hvv
      rcases hsw.cases with ⟨k, rfl, _⟩ | ⟨bb, rfl⟩ | ⟨k, rfl, _⟩
      · rw [denote'_ifThenElse_var_run_uint bi fuel v t e env _ k hvv] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        obtain ⟨_, h⟩ := hval; cases h
      · rw [valueToScalar_bool, Option.some.injEq] at hdw
        exact ⟨bb, rfl, hdw.symm⟩
      · rw [denote'_ifThenElse_var_run_int bi fuel v t e env k hvv] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        obtain ⟨_, h⟩ := hval; cases h
  obtain ⟨b₁, hb₁, hr₁⟩ := hb hrun₁ hval₁ hag₁
  obtain ⟨b₂, hb₂, hr₂⟩ := hb hrun₂ hval₂ hag₂
  have hc : ∀ {env : Env} {b : Bool}, env v = some (.bool b) →
      (denote' bi fuel (.var v)).run env = (.val (.bool b), env) := fun h => by
    rw [denote'_var_run, h]
  rw [denote'_ifThenElse_var_run_bool bi fuel v t e env₁ b₁ hb₁] at hrun₁
  rw [denote'_ifThenElse_var_run_bool bi fuel v t e env₂ b₂ hb₂] at hrun₂
  simp only [srcLeak, hc hb₁, hc hb₂] at hL
  cases b₁ <;> cases b₂ <;> simp only [SrcLeak.cat.injEq, SrcLeak.ev.injEq, SrcEv.branch.injEq,
    Bool.false_eq_true, Bool.true_eq_false, false_and, and_false, true_and] at hL
  · simp only [Bool.false_eq_true, if_false] at hrun₁ hrun₂ hr₁ hr₂
    cases h₁ with
    | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ hr₁) hv0
    | ifFalse _ _ _ _ _ tr₁ _ h₁ =>
    cases h₂ with
    | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ hr₂) hv0
    | ifFalse _ _ _ _ _ tr₂ _ h₂ =>
    obtain ⟨ht, hx⟩ := ihe tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ eC xe tr₁ tr₂
      hok'.2.2 hfl hE hrun₁ hval₁ hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
    exact ⟨by rw [ht], hx⟩
  · simp only [if_true] at hrun₁ hrun₂ hr₁ hr₂
    cases h₁ with
    | ifFalse _ _ _ _ _ _ h0 _ => rw [hr₁] at h0; simp at h0
    | ifTrue _ _ _ _ _ _ tr₁ _ _ h₁ =>
    cases h₂ with
    | ifFalse _ _ _ _ _ _ h0 _ => rw [hr₂] at h0; simp at h0
    | ifTrue _ _ _ _ _ _ tr₂ _ _ h₂ =>
    obtain ⟨ht, hx⟩ := iht tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ tC xt tr₁ tr₂
      hok'.2.1 hfl hT' hrun₁ hval₁ hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
    exact ⟨by rw [ht], hx⟩

/-- **The lowered `RWhileNz` loop**, by induction on fuel, for a source loop `L` that
    unfolds as `denoteWhile'Return` and `denoteWhile'` do on a `true` guard: two runs
    ending in a value, with equal `whileLeak`, from states holding the guard in the loop
    slot, have equal traces and end with the same exit flag. -/
theorem exitLoopCT (L : Nat → Env → Outcome × Env) (run c : String) (body : ImpExpr)
    (bC : LowCT) (xb : Bool) (ihb : ExitCT M bi N leafSpec body)
    (hslot : exitRunSlot run = true) (hc : exitReserved c = false)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb))
    (hL0 : ∀ env v, (L 0 env).1 ≠ .val v)
    (hLb : ∀ n env v, (∀ w, env c = some w → ScalarVal w) → (∀ b, env c ≠ some (.bool b)) →
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
      envAgreesOff env₁ rs₁ → rs₁.rsScalar exitRetName = 0 → rs₁.rsScalar run = rs₁.rsScalar c →
      envAgreesOff env₂ rs₂ → rs₂.rsScalar exitRetName = 0 → rs₂.rsScalar run = rs₂.rsScalar c →
      whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₁ =
        whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₂ →
      RustExecLeak N leafSpec M (.RWhileNz run (.RSeq bC (loopTail run c))) rs₁ t₁ r₁ →
      RustExecLeak N leafSpec M (.RWhileNz run (.RSeq bC (loopTail run c))) rs₂ t₂ r₂ →
      t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
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
    have hg : ∀ {env env' : Env} {o : Outcome} {rs : RustState}, L (n + 1) env = (o, env') →
        (∃ v, o = .val v) → envAgreesOff env rs →
        ∃ b, env c = some (.bool b) ∧ rs.rsScalar c = if b then 1 else 0 := by
      intro env env' o rs hrun hval hag
      by_cases hb : ∃ b, env c = some (.bool b)
      · obtain ⟨b, hb⟩ := hb
        obtain ⟨_, hd⟩ := hag c _ hc hb
        rw [valueToScalar_bool, Option.some.injEq] at hd
        exact ⟨b, hb, hd.symm⟩
      · obtain ⟨v, rfl⟩ := hval
        exact absurd (by rw [hrun])
          (hLb n env v (fun w hw => (hag c w hc hw).1) (fun b h => hb ⟨b, h⟩))
    obtain ⟨b₁, hb₁, hd₁⟩ := hg hrun₁ hval₁ hag₁
    obtain ⟨b₂, hb₂, hd₂⟩ := hg hrun₂ hval₂ hag₂
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
      obtain ⟨htb, hxw⟩ := ihb false (some run) (n + 1) env₁ env₂ e2₁ e2₂ _ _ rs₁ rs₂ q₁ q₂ bC xb
        tb₁ tb₂ hokB hctx hKB hbr₁ ⟨_, rfl⟩ hbr₂ ⟨_, rfl⟩ hag₁ hret₁ hag₂ hret₂ hLbody hB₁ hB₂
      obtain ⟨hE₁, -⟩ := exitSim_final M bi N leafSpec (hsim body) hokB hctx hKB hbr₁ ⟨_, rfl⟩
        hag₁ hret₁ hB₁
      obtain ⟨hE₂, -⟩ := exitSim_final M bi N leafSpec (hsim body) hokB hctx hKB hbr₂ ⟨_, rfl⟩
        hag₂ hret₂ hB₂
      have hf₁ := envAgreesExit_flag hE₁
      have hf₂ := envAgreesExit_flag hE₂
      cases hex₁ : exitOf (.val w₁) with
      | true =>
        have hex₂ : exitOf (.val w₂) = true := hxw ▸ hex₁
        rw [hex₁] at hf₁
        rw [hex₂] at hf₂
        simp only [if_true] at hf₁ hf₂
        have hdone : ∀ {q m r : RustState} {tq tl : List CTLeak}, q.rsScalar exitRetName = 1 →
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
      | false =>
        have hex₂ : exitOf (.val w₂) = false := hxw ▸ hex₁
        have hcf₁ := notCF_of_agree hE₁ hex₁
        have hcf₂ := notCF_of_agree hE₂ hex₂
        obtain ⟨h01, hagq₁, -⟩ := (envAgreesExit_val hcf₁).mp hE₁
        obtain ⟨h02, hagq₂, -⟩ := (envAgreesExit_val hcf₂).mp hE₂
        rw [tripCont_val hcf₁, tripCont_val hcf₂] at hLrest
        rw [hLi n env₁ w₁ e2₁ hb₁ hbr₁ hcf₁] at hrun₁
        rw [hLi n env₂ w₂ e2₂ hb₂ hbr₂ hcf₂] at hrun₂
        have hnext : ∀ {q m : RustState} {tq : List CTLeak} {e : Env},
            envAgreesOff e q → q.rsScalar exitRetName = 0 →
            RustExecLeak N leafSpec M (loopTail run c) q tq m →
            tq = [.branch false] ∧ envAgreesOff e m ∧ m.rsScalar exitRetName = 0 ∧
              m.rsScalar run = m.rsScalar c := by
          intro q m tq e hag hq hT
          cases hT with
          | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ hq) hv0
          | ifFalse _ _ _ _ _ _ _ hs =>
            cases hs
            refine ⟨rfl, envAgreesOff_set_reserved _ hresv hag, ?_, ?_⟩
            · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hq]
            · simp [rsScalar_rsSetScalar, hcr, SExpr.evalState]
        obtain ⟨rfl, hagm₁, hretm₁, hrcm₁⟩ := hnext hagq₁ h01 hT₁
        obtain ⟨rfl, hagm₂, hretm₂, hrcm₂⟩ := hnext hagq₂ h02 hT₂
        obtain ⟨htl, hr⟩ := IH e2₁ e2₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ tl₁ tl₂ hrun₁ hval₁ hrun₂ hval₂
          hagm₁ hretm₁ hrcm₁ hagm₂ hretm₂ hrcm₂ hLrest hloop₁ hloop₂
        exact ⟨by rw [htb, htl], hr⟩

/-- `exitLoopCT` with the loop entry of `exitLoop`: the flag, payload and loop slots
    are zeroed and the guard is copied into the loop slot. -/
theorem exitLoopWrapCT (L : Nat → Env → Outcome × Env) (run c : String) (body : ImpExpr)
    (bC : LowCT) (xb : Bool) (ihb : ExitCT M bi N leafSpec body)
    (hslot : exitRunSlot run = true) (hc : exitReserved c = false)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb))
    (hL0 : ∀ env v, (L 0 env).1 ≠ .val v)
    (hLb : ∀ n env v, (∀ w, env c = some w → ScalarVal w) → (∀ b, env c ≠ some (.bool b)) →
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
    (hag₁ : envAgreesOff env₁ rs₁) (hag₂ : envAgreesOff env₂ rs₂)
    (hL : whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₁ =
        whileLeak bi (.var c) body (srcLeak M bi (.var c)) (srcLeak M bi body) fuel env₂)
    (h₁ : RustExecLeak N leafSpec M (exitLoop run c bC) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (exitLoop run c bC) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hresv := exitReserved_of_runSlot hslot
  have hcr : c ≠ run := ne_of_reserved hc hresv
  have hentry : ∀ {env : Env} {rs r : RustState} {t : List CTLeak}, envAgreesOff env rs →
      RustExecLeak N leafSpec M (exitLoop run c bC) rs t r →
      ∃ rs1, envAgreesOff env rs1 ∧ rs1.rsScalar exitRetName = 0 ∧
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
    refine ⟨_, envAgreesOff_set_reserved _ hresv (envAgreesOff_set_reserved _ hresv
      (envAgreesOff_set_reserved _ exitReserved_val
        (envAgreesOff_set_reserved _ exitReserved_ret hag))), ?_, ?_, hl⟩
    · simp [rsScalar_rsSetScalar, (runSlot_ne_ret hslot).symm, exitRetName_ne_val]
    · simp [rsScalar_rsSetScalar, hcr, SExpr.evalState]
  obtain ⟨q₁, hq₁, hr₁, hc₁, hl₁⟩ := hentry hag₁ h₁
  obtain ⟨q₂, hq₂, hr₂, hc₂, hl₂⟩ := hentry hag₂ h₂
  exact exitLoopCT M bi N leafSpec hsim L run c body bC xb ihb hslot hc hokB hKB hL0 hLb hLo hLi
    fuel env₁ env₂ env₁' env₂' o₁ o₂ q₁ q₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hq₁ hr₁ hc₁ hq₂
    hr₂ hc₂ hL hl₁ hl₂

theorem exitCT_whileFoldReturn (c : String) (body : ImpExpr) (ihb : ExitCT M bi N leafSpec body) :
    ExitCT M bi N leafSpec (.whileFoldReturn (.var c) body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  obtain ⟨hE₁, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
  obtain ⟨hE₂, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    have hok' : exitReserved c = false ∧ exitSimOk false true body = true := by
      cases fl <;> simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] using hok
    rw [haxToLowCTK_whileFoldReturn_eq] at hK
    rcases hB : haxToLowCTK true false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK; cases hK
    rw [hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_whileFoldReturn_run] at hrun₁ hrun₂
    simp only [srcLeak] at hL
    have hslot := runSlot_exitRunName hfl
    obtain ⟨ht, hr⟩ := exitLoopWrapCT M bi N leafSpec hsim
      (fun n env => (_root_.Hax.denoteWhile'Return bi n (.var c) body).run env)
      (exitRunName fl) c body bC x ihb hslot hok'.1 hok'.2 hB
      (fun env v => by simp [denoteWhile'Return_zero_run])
      (fun n env v hsv hnb => by
        cases hvc : env c with
        | none =>
          obtain ⟨msg, h⟩ := denoteWhile'Return_succ_none bi n c body env hvc
          simp [h]
        | some w =>
          rcases (hsv w hvc).cases with ⟨k, rfl, _⟩ | ⟨b, rfl⟩ | ⟨k, rfl, _⟩
          · simp [denoteWhile'Return_succ_uint bi n c body env _ k hvc]
          · exact absurd hvc (hnb b)
          · simp [denoteWhile'Return_succ_int bi n c body env k hvc])
      (fun n env o e2 hb hbr ho => denoteWhile'Return_succ_nonval bi n c body env e2 o hb hbr ho)
      (fun n env w e2 hb hbr hw => denoteWhile'Return_succ_iterate bi n c body env e2 w hb hbr hw)
      fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂ hL
      h₁ h₂
    exact ⟨ht, exitOf_eq_of_flag hE₁ hE₂ hr⟩

theorem exitCT_whileFold (c : String) (body : ImpExpr) (ihb : ExitCT M bi N leafSpec body) :
    ExitCT M bi N leafSpec (.whileFold (.var c) body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOk] at hok
    | some r =>
      have hok' : exitReserved c = false ∧ hasBreak body = true ∧
          exitSimOk false true body = true := by
        simpa only [exitSimOk, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have hK0 := hK
      rw [haxToLowCTK_whileFold_some_eq, if_pos hok'.2.1] at hK
      rcases hB : haxToLowCTK true false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK; cases hK
      rw [hB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      have hx₁ := exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hK0 hrun₁ hval₁ hag₁ hret₁ h₁
      have hx₂ := exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hK0 hrun₂ hval₂ hag₂ hret₂ h₂
      rw [denote'_whileFold_run] at hrun₁ hrun₂
      simp only [srcLeak] at hL
      have hslot := runSlot_exitRunName hfl
      cases h₁ with
      | seq _ _ _ _ _ tl₁ tz₁ hl₁ hz₁ =>
      cases h₂ with
      | seq _ _ _ _ _ tl₂ tz₂ hl₂ hz₂ =>
      cases hz₁
      cases hz₂
      obtain ⟨ht, -⟩ := exitLoopWrapCT M bi N leafSpec hsim
        (fun n env => (_root_.Hax.denoteWhile' bi n (.var c) body).run env)
        (exitRunName (some r)) c body bC x ihb hslot hok'.1 hok'.2.2 hB
        (fun env v => by simp [denoteWhile'_zero_run])
        (fun n env v hsv hnb => by
          cases hvc : env c with
          | none =>
            obtain ⟨msg, h⟩ := denoteWhile'_succ_none bi n c body env hvc
            simp [h]
          | some w =>
            rcases (hsv w hvc).cases with ⟨k, rfl, _⟩ | ⟨b, rfl⟩ | ⟨k, rfl, _⟩
            · simp [denoteWhile'_succ_uint bi n c body env _ k hvc]
            · exact absurd hvc (hnb b)
            · simp [denoteWhile'_succ_int bi n c body env k hvc])
        (fun n env o e2 hb hbr ho => denoteWhile'_succ_nonval bi n c body env e2 o hb hbr ho)
        (fun n env w e2 hb hbr hw => denoteWhile'_succ_iterate bi n c body env e2 w hb hbr hw)
        fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ _ _ tl₁ tl₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂ hL
        hl₁ hl₂
      exact ⟨by rw [ht], hx₁.trans hx₂.symm⟩

end Arms

/-! ## Counted loops -/

section Trips

variable (M : LowCTLeakModel) (N : Nat) (leafSpec : LeafSpec)

/-- `d` traced trips of `B` with the trip counter `x` from `k`: the traces of the trips
    in order. -/
def TripsL (x : String) (B : LowCT) : Nat → Nat → RustState → List CTLeak → RustState → Prop
  | _, 0, rs, t, r => t = [] ∧ r = rs
  | k, d + 1, rs, t, r => ∃ m t1 t2, RustExecLeak N leafSpec M B (rsSetScalar rs x k) t1 m ∧
      TripsL x B (k + 1) d m t2 r ∧ t = t1 ++ t2

theorem tripsL_snoc (x : String) (B : LowCT) :
    ∀ (d k : Nat) (rs m r : RustState) (t t' : List CTLeak), TripsL M N leafSpec x B k d rs t m →
      RustExecLeak N leafSpec M B (rsSetScalar m x (k + d)) t' r →
      TripsL M N leafSpec x B k (d + 1) rs (t ++ t') r := by
  intro d
  induction d with
  | zero =>
    intro k rs m r t t' h h'
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨r, t', [], by simpa using h', ⟨rfl, rfl⟩, by simp⟩
  | succ d ih =>
    intro k rs m r t t' h h'
    obtain ⟨m1, t1, t2, hB, hT, rfl⟩ := h
    exact ⟨m1, t1, t2 ++ t', hB,
      ih (k + 1) m1 m r t2 t' hT (by rwa [show k + 1 + d = k + (d + 1) by omega]), by simp⟩

/-- A traced run of `RFor x n B` is `n` traced trips from `0`. -/
theorem rFor_tripsL (x : String) (B : LowCT) :
    ∀ (n : Nat) (rs r : RustState) (t : List CTLeak),
      RustExecLeak N leafSpec M (.RFor x n B) rs t r → TripsL M N leafSpec x B 0 n rs t r := by
  intro n
  induction n with
  | zero => intro rs r t h; cases h; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro rs r t h
    cases h with
    | forSucc _ _ _ _ r1 _ t1 t2 h1 h2 =>
      exact tripsL_snoc M N leafSpec x B n 0 rs r1 r t1 t2 (ih rs r1 t1 h1)
        (by rwa [Nat.zero_add])

/-- After an exit, each guarded trip leaves the branch event of its guard and keeps the
    exit flag. -/
theorem exitedTripsL (run : String) (B : LowCT) (hslot : exitRunSlot run = true) :
    ∀ (d k : Nat) (q r : RustState) (t : List CTLeak), q.rsScalar exitRetName = 1 →
      TripsL M N leafSpec run (exitGuard B) k d q t r →
      t = List.replicate d (.branch true) ∧ r.rsScalar exitRetName = 1 := by
  intro d
  induction d with
  | zero => intro k q r t hq h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
  | succ d ih =>
    intro k q r t hq h
    obtain ⟨m, t1, t2, hB, hT, rfl⟩ := h
    have hq' : (rsSetScalar q run k).rsScalar exitRetName = 1 := by
      rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hq]
    cases hB with
    | ifFalse _ _ _ _ _ _ h0 _ => rw [hq'] at h0; simp at h0
    | ifTrue _ _ _ _ _ _ _ _ _ hs =>
      cases hs
      obtain ⟨rfl, hr⟩ := ih (k + 1) _ r t2 hq' hT
      exact ⟨by simp [List.replicate_succ], hr⟩

variable (bi : Builtins) (hsim : ∀ e, ExitSim bi N leafSpec e)
include hsim

/-- **The trips of a lowered counted loop**, by induction on the trips left. The trip
    `j` binds the counter `i` to `cnt j` through the expression `ce` of the loop slot;
    the source loop `L` and its leakage `T` unfold as the counted loops of `denote'` do.
    Two runs ending in a value, with equal leakage, from states with the exit flag `0`,
    have equal traces and end with the same exit flag. -/
theorem exitTripsCT (run i : String) (body : ImpExpr) (bC : LowCT) (xb : Bool) (ce : SExpr)
    (cnt : Nat → Nat) (D : Nat) (L : Nat → Nat → Env → Outcome × Env)
    (T : Nat → Nat → Env → SrcLeak)
    (ihb : ExitCT M bi N leafSpec body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb))
    (hce : sexprReadsOnly (fun x => x = run) ce)
    (hcev : ∀ (j : Nat) (s : RustState), s.rsScalar run = j → ce.evalState s = cnt j)
    (hcnt : ∀ j, j < D → cnt j < 2 ^ 64)
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
      envAgreesOff env₁ rs₁ → rs₁.rsScalar exitRetName = 0 →
      envAgreesOff env₂ rs₂ → rs₂.rsScalar exitRetName = 0 →
      T fuel j env₁ = T fuel j env₂ →
      TripsL M N leafSpec run (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
        j d rs₁ t₁ r₁ →
      TripsL M N leafSpec run (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
        j d rs₂ t₂ r₂ →
      t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
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
    -- the trip's entry: the counter slot holds `cnt j`
    have hent : ∀ {env : Env} {rs m : RustState} {tt : List CTLeak},
        envAgreesOff env rs → rs.rsScalar exitRetName = 0 →
        RustExecLeak N leafSpec M (exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i ce) bC)))
          (rsSetScalar rs run j) tt m →
        ∃ tb, tt = .branch false :: (sexprLeak M (rsSetScalar (rsSetScalar rs run j) i 0) ce ++ tb) ∧
          RustExecLeak N leafSpec M bC (rsSetScalar (rsSetScalar rs run j) i (cnt j)) tb m ∧
          envAgreesOff (env.extend i (.int (cnt j))) (rsSetScalar (rsSetScalar rs run j) i (cnt j)) ∧
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
      refine ⟨tb, rfl, hb, ?_, ?_⟩
      · exact envAgreesOff_extend hi_ ⟨by omega, by have := hcnt j hjD; omega⟩
          (valueToScalar_int _) (envAgreesOff_set_reserved _ hresv hag)
      · rw [rsScalar_rsSetScalar, if_neg hiret.symm, hr0]
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
    obtain ⟨htb, hxw⟩ := ihb false (some run) (n + 1) _ _ e2₁ e2₂ _ _ _ _ m₁ m₂ bC xb tb₁ tb₂
      hokB hctx hKB hbr₁ ⟨_, rfl⟩ hbr₂ ⟨_, rfl⟩ hagT₁ hretT₁ hagT₂ hretT₂ hLbody hb₁ hb₂
    obtain ⟨hE₁, -⟩ := exitSim_final M bi N leafSpec (hsim body) hokB hctx hKB hbr₁ ⟨_, rfl⟩
      hagT₁ hretT₁ hb₁
    obtain ⟨hE₂, -⟩ := exitSim_final M bi N leafSpec (hsim body) hokB hctx hKB hbr₂ ⟨_, rfl⟩
      hagT₂ hretT₂ hb₂
    have hf₁ := envAgreesExit_flag hE₁
    have hf₂ := envAgreesExit_flag hE₂
    cases hex₁ : exitOf (.val w₁) with
    | true =>
      have hex₂ : exitOf (.val w₂) = true := hxw ▸ hex₁
      rw [hex₁] at hf₁
      rw [hex₂] at hf₂
      simp only [if_true] at hf₁ hf₂
      obtain ⟨rfl, hr₁⟩ := exitedTripsL M N leafSpec run _ hslot d (j + 1) m₁ r₁ tr₁ hf₁ hR₁
      obtain ⟨rfl, hr₂⟩ := exitedTripsL M N leafSpec run _ hslot d (j + 1) m₂ r₂ tr₂ hf₂ hR₂
      exact ⟨by rw [hce_eq, htb], hr₁.trans hr₂.symm⟩
    | false =>
      have hex₂ : exitOf (.val w₂) = false := hxw ▸ hex₁
      have hcf₁ := notCF_of_agree hE₁ hex₁
      have hcf₂ := notCF_of_agree hE₂ hex₂
      obtain ⟨h01, hagq₁, -⟩ := (envAgreesExit_val hcf₁).mp hE₁
      obtain ⟨h02, hagq₂, -⟩ := (envAgreesExit_val hcf₂).mp hE₂
      rw [tripCont_val hcf₁, tripCont_val hcf₂] at hLrest
      rw [hLi n j env₁ w₁ e2₁ hjD hbr₁ hcf₁] at hrun₁
      rw [hLi n j env₂ w₂ e2₂ hjD hbr₂ hcf₂] at hrun₂
      obtain ⟨htr, hr⟩ := IH (j + 1) n e2₁ e2₂ env₁' env₂' o₁ o₂ m₁ m₂ r₁ r₂ tr₁ tr₂ (by omega)
        hrun₁ hval₁ hrun₂ hval₂ hagq₁ h01 hagq₂ h02 hLrest hR₁ hR₂
      exact ⟨by rw [hce_eq, htb, htr], hr⟩

/-- **The lowered upward counted loop** `RFor run (hi - lo) (exitForTrip run i lo bC)`, for
    a source loop `Lf` that unfolds as `denoteForLoop'Return` and `denoteForLoop'` do. -/
theorem exitForCT (Lf : Nat → Int → Env → Outcome × Env) (run i : String) (lo hi : Nat)
    (body : ImpExpr) (bC : LowCT) (xb : Bool) (ihb : ExitCT M bi N leafSpec body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb))
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
    (hag₁ : envAgreesOff env₁ rs₁) (hret₁ : rs₁.rsScalar exitRetName = 0)
    (hag₂ : envAgreesOff env₂ rs₂) (hret₂ : rs₂.rsScalar exitRetName = 0)
    (hL : forLeak bi i body (srcLeak M bi body) fuel lo hi env₁ =
      forLeak bi i body (srcLeak M bi body) fuel lo hi env₂)
    (h₁ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTrip run i lo bC)) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTrip run i lo bC)) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hcast : ∀ j : Nat, ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 := by
    intro j; push_cast; ring
  refine exitTripsCT M N leafSpec bi hsim run i body bC xb (.SAdd (.SVar run) (.SLit lo))
    (fun j => lo + j) (hi - lo) (fun n j env => Lf n ((lo + j : Nat) : Int) env)
    (fun n j env => forLeak bi i body (srcLeak M bi body) n ((lo + j : Nat) : Int) hi env)
    ihb hslot hi_ hokB hKB ⟨rfl, trivial⟩
    (fun j s hs => by simp [SExpr.evalState, hs, Nat.add_comm])
    (fun j hj => by omega)
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

/-- **The lowered downward counted loop** `RFor run (hi - lo) (exitForTripRev run i hi bC)`,
    for the source loop `denoteForLoopRev'Return`. -/
theorem exitForRevCT (run i : String) (lo hi : Nat)
    (body : ImpExpr) (bC : LowCT) (xb : Bool) (ihb : ExitCT M bi N leafSpec body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb))
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : (_root_.Hax.denoteForLoopRev'Return bi fuel i lo hi body).run env₁ = (o₁, env₁'))
    (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : (_root_.Hax.denoteForLoopRev'Return bi fuel i lo hi body).run env₂ = (o₂, env₂'))
    (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : envAgreesOff env₁ rs₁) (hret₁ : rs₁.rsScalar exitRetName = 0)
    (hag₂ : envAgreesOff env₂ rs₂) (hret₂ : rs₂.rsScalar exitRetName = 0)
    (hL : forRevLeak bi i body (srcLeak M bi body) fuel lo hi env₁ =
      forRevLeak bi i body (srcLeak M bi body) fuel lo hi env₂)
    (h₁ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTripRev run i hi bC)) rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec M (.RFor run (hi - lo) (exitForTripRev run i hi bC)) rs₂ t₂ r₂) :
    t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName := by
  have hcast : ∀ j : Nat, j < hi - lo → ((hi - j : Nat) : Int) - 1 = ((hi - 1 - j : Nat) : Int) := by
    intro j hj; omega
  have hcast' : ∀ j : Nat, j < hi - lo → ((hi - (j + 1) : Nat) : Int) = ((hi - j : Nat) : Int) - 1 := by
    intro j hj; omega
  refine exitTripsCT M N leafSpec bi hsim run i body bC xb (.SSub (.SLit (hi - 1)) (.SVar run))
    (fun j => hi - 1 - j) (hi - lo)
    (fun n j env => (_root_.Hax.denoteForLoopRev'Return bi n i lo ((hi - j : Nat) : Int) body).run env)
    (fun n j env => forRevLeak bi i body (srcLeak M bi body) n lo ((hi - j : Nat) : Int) env)
    ihb hslot hi_ hokB hKB ⟨trivial, rfl⟩
    (fun j s hs => by simp [SExpr.evalState, hs])
    (fun j hj => by omega)
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

omit hsim in
/-- The entry of a lowered counted loop: zeroing the flag and payload slots keeps the
    agreement and sets the flag to `0`. -/
theorem forEntry {env : Env} {rs : RustState} (hag : envAgreesOff env rs) :
    envAgreesOff env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) ∧
      (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar exitRetName = 0 :=
  ⟨envAgreesOff_set_reserved _ exitReserved_val (envAgreesOff_set_reserved _ exitReserved_ret hag),
    by rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]⟩

/-- `exitForCT` with the loop entry of `exitForLoop`. -/
theorem exitForLoopCT (Lf : Nat → Int → Env → Outcome × Env) (run i : String) (lo hi : Nat)
    (body : ImpExpr) (bC : LowCT) (xb : Bool) (ihb : ExitCT M bi N leafSpec body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb))
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
    (hag₁ : envAgreesOff env₁ rs₁) (hag₂ : envAgreesOff env₂ rs₂)
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
  obtain ⟨hag₁', hret₁'⟩ := forEntry hag₁
  obtain ⟨hag₂', hret₂'⟩ := forEntry hag₂
  exact exitForCT M N leafSpec bi hsim Lf run i lo hi body bC xb ihb hslot hi_ hhi hokB hKB
    hL0 hLo hLi fuel env₁ env₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂
    hag₁' hret₁' hag₂' hret₂' hL h₁ h₂

/-- `exitForCT` with the loop entry of `exitForLoopRt`: the trip count is read from the
    slot `hv`, which holds `H` in both runs. -/
theorem exitForLoopRtCT (Lf : Nat → Int → Env → Outcome × Env) (run i : String) (lo : Nat)
    (hv : String) (H : Nat) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitCT M bi N leafSpec body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false)
    (hh_ : exitReserved hv = false) (hH : H < 2 ^ 64)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb))
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
    (hag₁ : envAgreesOff env₁ rs₁) (hag₂ : envAgreesOff env₂ rs₂)
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
  obtain ⟨hag₁', hret₁'⟩ := forEntry hag₁
  obtain ⟨hag₂', hret₂'⟩ := forEntry hag₂
  obtain ⟨ht, hr⟩ := exitForCT M N leafSpec bi hsim Lf run i lo H body bC xb ihb hslot hi_
    hH.le hokB hKB hL0 hLo hLi fuel env₁ env₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ tr₁ tr₂ hrun₁ hval₁
    hrun₂ hval₂ hag₁' hret₁' hag₂' hret₂' hL h₁ h₂
  refine ⟨?_, hr⟩
  rw [ht, sexprLeak_congr M (S := fun x => x = hv)
    (fun x hx => by subst hx; exact he₁.trans he₂.symm) (.SSub (.SVar hv) (.SLit lo))
    ⟨rfl, trivial⟩]

end Trips

/-! ## The counted-loop arms -/

section LoopArms

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (hsim : ∀ e, ExitSim bi N leafSpec e)

theorem boundInt_int (n : Int) : boundInt (.int n) = some n := rfl

/-- The upper bound of a counted loop run to a value from a scalar variable: its value
    denotes the trip bound `H` as an integer. -/
theorem boundInt_of_scalar_run {v : Value} {H : Nat} (hs : ScalarVal v)
    (hd : valueToScalar v = some H) (hnb : ∀ b, v ≠ .bool b) : boundInt v = some (H : Int) := by
  rcases hs.cases with ⟨k, rfl, _⟩ | ⟨b, rfl⟩ | ⟨k, rfl, h0, _⟩
  · simp only [valueToScalar, Option.some.injEq] at hd; subst hd; rfl
  · exact absurd rfl (hnb b)
  · simp only [valueToScalar, h0, if_true, Option.some.injEq] at hd
    subst hd
    simp [boundInt, Int.toNat_of_nonneg h0]

theorem forFoldReturn_var_not_bool (fuel : Nat) (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome) (b : Bool) (hh : env h = some (.bool b))
    (hrun : (denote' bi fuel (.forFoldReturn i (.lit (.int lo)) (.var h) body)).run env =
      (o, env')) (hval : ∃ v, o = .val v) : False := by
  obtain ⟨u, rfl⟩ := hval
  simp only [denote'] at hrun
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, hh, Value.ofLit] at hrun
  cases (Prod.mk.inj hrun).1

theorem forFold_var_not_bool (fuel : Nat) (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome) (b : Bool) (hh : env h = some (.bool b))
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.var h) body)).run env =
      (o, env')) (hval : ∃ v, o = .val v) : False := by
  obtain ⟨u, rfl⟩ := hval
  simp only [denote'] at hrun
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, hh, Value.ofLit] at hrun
  cases (Prod.mk.inj hrun).1

/-- The leakage of a counted loop with literal bounds. -/
theorem boundsLeak_lit (fuel : Nat) (l h : Int) (trips : Int → Int → Env → SrcLeak)
    (env : Env) :
    boundsLeak bi (.lit (.int l)) (.lit (.int h)) (fun _ => .nil) (fun _ => .nil) fuel trips env =
      .cat .nil (.cat .nil (.cat (.ev (.bound l h)) (trips l h env))) := by
  simp [boundsLeak, denote'_lit_run, Value.ofLit, boundInt]

/-- The leakage of a counted loop from a literal to a variable holding `v`. -/
theorem boundsLeak_var (fuel : Nat) (l : Int) (h : String) (trips : Int → Int → Env → SrcLeak)
    (env : Env) (v : Value) (H : Int) (hh : env h = some v) (hb : boundInt v = some H) :
    boundsLeak bi (.lit (.int l)) (.var h) (fun _ => .nil) (fun _ => .nil) fuel trips env =
      .cat .nil (.cat .nil (.cat (.ev (.bound l H)) (trips l H env))) := by
  simp [boundsLeak, denote'_lit_run, denote'_var_run, hh, Value.ofLit, boundInt_int, hb]

include hsim

theorem exitCT_forFoldReturn (i : String) (lo hi body : ImpExpr)
    (ihb : ExitCT M bi N leafSpec body) :
    ExitCT M bi N leafSpec (.forFoldReturn i lo hi body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  obtain ⟨hE₁, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
  obtain ⟨hE₂, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
  suffices H : t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName from
    ⟨H.1, exitOf_eq_of_flag hE₁ hE₂ H.2⟩
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    have hok' : ((forBounds lo hi).isSome || forBoundsRtOk lo hi) = true ∧
        exitReserved i = false ∧ exitSimOk false true body = true := by
      cases fl <;> simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have hslot := runSlot_exitRunName hfl
    rw [haxToLowCTK_forFoldReturn_eq] at hK
    rcases hB : haxToLowCTK true false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
        rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
    rw [hB] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
      · rw [hFB, hRt] at hK; cases hK
      rw [hFB, hRt] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      have hh_ : exitReserved h = false := by
        have h1 := hok'.1
        simp only [hFB, forBoundsRtOk, hRt, Option.isSome_none, Bool.false_or,
          Bool.not_eq_true'] at h1
        exact h1
      obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
      obtain ⟨v₁, H₁, hv₁, hd₁, hH₁, hrun₁'⟩ := denote'_forFoldReturn_var_scalar bi fuel i h l body
        env₁ env₁' o₁ hrun₁ hval₁ (fun v hv => (hag₁ h v hh_ hv).1)
      obtain ⟨v₂, H₂, hv₂, hd₂, hH₂, hrun₂'⟩ := denote'_forFoldReturn_var_scalar bi fuel i h l body
        env₂ env₂' o₂ hrun₂ hval₂ (fun v hv => (hag₂ h v hh_ hv).1)
      have hbI₁ := boundInt_of_scalar_run (hag₁ h v₁ hh_ hv₁).1 hd₁ (fun b hb =>
        forFoldReturn_var_not_bool bi fuel i h l body env₁ env₁' o₁ b (hb ▸ hv₁) hrun₁ hval₁)
      have hbI₂ := boundInt_of_scalar_run (hag₂ h v₂ hh_ hv₂).1 hd₂ (fun b hb =>
        forFoldReturn_var_not_bool bi fuel i h l body env₂ env₂' o₂ b (hb ▸ hv₂) hrun₂ hval₂)
      simp only [srcLeak] at hL
      rw [boundsLeak_var bi fuel l h _ env₁ v₁ H₁ hv₁ hbI₁,
        boundsLeak_var bi fuel l h _ env₂ v₂ H₂ hv₂ hbI₂] at hL
      simp only [SrcLeak.cat.injEq, SrcLeak.ev.injEq, SrcEv.bound.injEq, true_and,
        Nat.cast_inj] at hL
      obtain ⟨rfl, hL⟩ := hL
      have hdec₁ : rs₁.rsScalar h = H₁ := by
        have := (hag₁ h v₁ hh_ hv₁).2; rw [hd₁] at this; exact (Option.some.inj this).symm
      have hdec₂ : rs₂.rsScalar h = H₁ := by
        have := (hag₂ h v₂ hh_ hv₂).2; rw [hd₂] at this; exact (Option.some.inj this).symm
      exact exitForLoopRtCT M N leafSpec bi hsim
        (fun n k env => (_root_.Hax.denoteForLoop'Return bi n i k H₁ body).run env)
        (exitRunName fl) i l h H₁ body bC x ihb hslot hok'.2.1 hh_ hH₁ hok'.2.2 hB
        (fun k env v hk => by rw [denoteForLoop'Return_zero_run bi i k _ body env hk]; simp)
        (fun n k env o e2 hk hbr ho =>
          denoteForLoop'Return_succ_nonval bi n i k _ body env e2 o hk hbr ho)
        (fun n k env w e2 hk hbr hw =>
          denoteForLoop'Return_succ_iterate bi n i k _ body env e2 w hk hbr hw)
        fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁' hval₁ hrun₂' hval₂ hag₁ hag₂
        hdec₁ hdec₂ hL h₁ h₂
    rw [hFB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rw [denote'_forFoldReturn_lit_run] at hrun₁ hrun₂
    simp only [srcLeak] at hL
    rw [boundsLeak_lit, boundsLeak_lit] at hL
    simp only [SrcLeak.cat.injEq, true_and] at hL
    exact exitForLoopCT M N leafSpec bi hsim
      (fun n k env => (_root_.Hax.denoteForLoop'Return bi n i k h body).run env)
      (exitRunName fl) i l h body bC x ihb hslot hok'.2.1 hh hok'.2.2 hB
      (fun k env v hk => by rw [denoteForLoop'Return_zero_run bi i k _ body env hk]; simp)
      (fun n k env o e2 hk hbr ho =>
        denoteForLoop'Return_succ_nonval bi n i k _ body env e2 o hk hbr ho)
      (fun n k env w e2 hk hbr hw =>
        denoteForLoop'Return_succ_iterate bi n i k _ body env e2 w hk hbr hw)
      fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂
      hL h₁ h₂

theorem exitCT_forFoldRevReturn (i : String) (lo hi body : ImpExpr)
    (ihb : ExitCT M bi N leafSpec body) :
    ExitCT M bi N leafSpec (.forFoldRevReturn i lo hi body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  obtain ⟨hE₁, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
  obtain ⟨hE₂, -⟩ := exitSim_final M bi N leafSpec (hsim _) hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
  suffices H : t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName from
    ⟨H.1, exitOf_eq_of_flag hE₁ hE₂ H.2⟩
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
        exitSimOk false true body = true := by
      cases fl <;> simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    rw [haxToLowCTK_forFoldRevReturn_eq] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rw [hFB] at hok'; cases hok'.1
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rcases hB : haxToLowCTK true false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hFB, hB] at hK; cases hK
    rw [hFB, hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_forFoldRevReturn_lit_run] at hrun₁ hrun₂
    simp only [srcLeak] at hL
    rw [boundsLeak_lit, boundsLeak_lit] at hL
    simp only [SrcLeak.cat.injEq, true_and] at hL
    have hslot := runSlot_exitRunName hfl
    cases h₁ with
    | letU64Zero _ _ _ _ _ h₁ =>
    cases h₁ with
    | letU64Zero _ _ _ _ _ h₁ =>
    cases h₂ with
    | letU64Zero _ _ _ _ _ h₂ =>
    cases h₂ with
    | letU64Zero _ _ _ _ _ h₂ =>
    obtain ⟨hag₁', hret₁'⟩ := forEntry hag₁
    obtain ⟨hag₂', hret₂'⟩ := forEntry hag₂
    exact exitForRevCT M N leafSpec bi hsim (exitRunName fl) i l h body bC x ihb hslot hok'.2.1
      hh hok'.2.2 hB fuel env₁ env₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂
      hag₁' hret₁' hag₂' hret₂' hL h₁ h₂

theorem exitCT_forFold (i : String) (lo hi body : ImpExpr)
    (ihb : ExitCT M bi N leafSpec body) :
    ExitCT M bi N leafSpec (.forFold i lo hi body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOk] at hok
    | some r =>
      have hok' : ((forBounds lo hi).isSome || forBoundsRtOk lo hi) = true ∧
          exitReserved i = false ∧ hasBreak body = true ∧ exitSimOk false true body = true := by
        simpa only [exitSimOk, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have hK0 := hK
      have hslot := runSlot_exitRunName hfl
      rw [haxToLowCTK_forFold_some_eq, if_pos hok'.2.2.1] at hK
      rcases hB : haxToLowCTK true false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK
        rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
          rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
      rw [hB] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
      · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
        · rw [hFB, hRt] at hK; cases hK
        rw [hFB, hRt] at hK
        simp only [Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        refine ⟨?_, (exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hK0 hrun₁ hval₁ hag₁
          hret₁ h₁).trans (exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hK0 hrun₂ hval₂
          hag₂ hret₂ h₂).symm⟩
        have hh_ : exitReserved h = false := by
          have h1 := hok'.1
          simp only [hFB, forBoundsRtOk, hRt, Option.isSome_none, Bool.false_or,
            Bool.not_eq_true'] at h1
          exact h1
        obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
        obtain ⟨v₁, H₁, hv₁, hd₁, hH₁, hrun₁'⟩ := denote'_forFold_var_scalar bi fuel i h l body
          env₁ env₁' o₁ hrun₁ hval₁ (fun v hv => (hag₁ h v hh_ hv).1)
        obtain ⟨v₂, H₂, hv₂, hd₂, hH₂, hrun₂'⟩ := denote'_forFold_var_scalar bi fuel i h l body
          env₂ env₂' o₂ hrun₂ hval₂ (fun v hv => (hag₂ h v hh_ hv).1)
        have hbI₁ := boundInt_of_scalar_run (hag₁ h v₁ hh_ hv₁).1 hd₁ (fun b hb =>
          forFold_var_not_bool bi fuel i h l body env₁ env₁' o₁ b (hb ▸ hv₁) hrun₁ hval₁)
        have hbI₂ := boundInt_of_scalar_run (hag₂ h v₂ hh_ hv₂).1 hd₂ (fun b hb =>
          forFold_var_not_bool bi fuel i h l body env₂ env₂' o₂ b (hb ▸ hv₂) hrun₂ hval₂)
        simp only [srcLeak] at hL
        rw [boundsLeak_var bi fuel l h _ env₁ v₁ H₁ hv₁ hbI₁,
          boundsLeak_var bi fuel l h _ env₂ v₂ H₂ hv₂ hbI₂] at hL
        simp only [SrcLeak.cat.injEq, SrcLeak.ev.injEq, SrcEv.bound.injEq, true_and,
          Nat.cast_inj] at hL
        obtain ⟨rfl, hL⟩ := hL
        have hdec₁ : rs₁.rsScalar h = H₁ := by
          have := (hag₁ h v₁ hh_ hv₁).2; rw [hd₁] at this; exact (Option.some.inj this).symm
        have hdec₂ : rs₂.rsScalar h = H₁ := by
          have := (hag₂ h v₂ hh_ hv₂).2; rw [hd₂] at this; exact (Option.some.inj this).symm
        cases h₁ with
        | seq _ _ _ _ _ tl₁ tz₁ hl₁ hz₁ =>
        cases h₂ with
        | seq _ _ _ _ _ tl₂ tz₂ hl₂ hz₂ =>
        cases hz₁
        cases hz₂
        obtain ⟨ht, -⟩ := exitForLoopRtCT M N leafSpec bi hsim
          (fun n k env => (_root_.Hax.denoteForLoop' bi n i k H₁ body).run env)
          (exitRunName (some r)) i l h H₁ body bC x ihb hslot hok'.2.1 hh_ hH₁ hok'.2.2.2 hB
          (fun k env v hk => by rw [denoteForLoop'_zero_run bi i k _ body env hk]; simp)
          (fun n k env o e2 hk hbr ho =>
            denoteForLoop'_succ_nonval bi n i k _ body env e2 o hk hbr ho)
          (fun n k env w e2 hk hbr hw =>
            denoteForLoop'_succ_iterate bi n i k _ body env e2 w hk hbr hw)
          fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ _ _ tl₁ tl₂ hrun₁' hval₁ hrun₂' hval₂ hag₁
          hag₂ hdec₁ hdec₂ hL hl₁ hl₂
        rw [ht]
      rw [hFB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      refine ⟨?_, (exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hK0 hrun₁ hval₁ hag₁
        hret₁ h₁).trans (exitOf_false_of_x M bi N leafSpec (hsim _) hok hfl hK0 hrun₂ hval₂
        hag₂ hret₂ h₂).symm⟩
      obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
      rw [denote'_forFold_lit_run] at hrun₁ hrun₂
      simp only [srcLeak] at hL
      rw [boundsLeak_lit, boundsLeak_lit] at hL
      simp only [SrcLeak.cat.injEq, true_and] at hL
      cases h₁ with
      | seq _ _ _ _ _ tl₁ tz₁ hl₁ hz₁ =>
      cases h₂ with
      | seq _ _ _ _ _ tl₂ tz₂ hl₂ hz₂ =>
      cases hz₁
      cases hz₂
      obtain ⟨ht, -⟩ := exitForLoopCT M N leafSpec bi hsim
        (fun n k env => (_root_.Hax.denoteForLoop' bi n i k h body).run env)
        (exitRunName (some r)) i l h body bC x ihb hslot hok'.2.1 hh hok'.2.2.2 hB
        (fun k env v hk => by rw [denoteForLoop'_zero_run bi i k _ body env hk]; simp)
        (fun n k env o e2 hk hbr ho =>
          denoteForLoop'_succ_nonval bi n i k _ body env e2 o hk hbr ho)
        (fun n k env w e2 hk hbr hw =>
          denoteForLoop'_succ_iterate bi n i k _ body env e2 w hk hbr hw)
        fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ _ _ tl₁ tl₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂
        hL hl₁ hl₂
      rw [ht]

end LoopArms

/-! ## Every expression of the fragment, and the function frame -/

section Assembly

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)

/-- An expression outside the fragment satisfies `ExitCT` vacuously. -/
theorem exitCT_of_not_ok (e : ImpExpr) (h : ∀ tl il, exitSimOk tl il e = false) :
    ExitCT M bi N leafSpec e := by
  intro tl fl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hok
  rw [h] at hok; cases hok

/-- **The exit-flag lowering preserves constant time.** For a builtin table computing
    the scalar operations soundly, every expression satisfies `ExitCT`. -/
theorem haxToLowCTK_ct (hs : ScalarOpsSound bi) (e : ImpExpr) : ExitCT M bi N leafSpec e := by
  have hsim := haxToLowCTK_simulates bi N leafSpec hs
  have nok : ∀ e : ImpExpr, (∀ tl il, exitSimOk tl il e = false) → ExitCT M bi N leafSpec e :=
    exitCT_of_not_ok M bi N leafSpec
  induction e using ImpExpr.ind with
  | lit l => exact exitCT_lit M bi N leafSpec hsim l
  | var x => exact exitCT_var M bi N leafSpec hsim x
  | unitVal => exact exitCT_unitVal M bi N leafSpec hsim
  | letBind n val body _ ihb =>
    cases val with
    | lit l => exact exitCT_letBind_lit M bi N leafSpec n l body ihb
    | var s => exact exitCT_letBind_var M bi N leafSpec n s body ihb
    | app op args =>
      rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩
      · exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
      · exact nok _ (fun tl il => by cases tl <;> cases il <;> cases a1 <;> rfl)
      · cases a1 with
        | var a =>
          cases a2 with
          | var b => exact exitCT_letBind_app M bi N leafSpec hs n op a b body ihb
          | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
        | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
      · exact nok _ (fun tl il => by
          cases tl <;> cases il <;> cases a1 <;> (try cases a2) <;> rfl)
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | seq a b iha ihb => exact exitCT_seq M bi N leafSpec hsim a b iha ihb
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v => exact exitCT_ifThenElse M bi N leafSpec v t e iht ihe
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | whileFoldReturn c body _ ihb =>
    cases c with
    | var v => exact exitCT_whileFoldReturn M bi N leafSpec hsim v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | forFoldReturn i lo hi body _ _ ihb =>
    exact exitCT_forFoldReturn M bi N leafSpec hsim i lo hi body ihb
  | forFoldRevReturn i lo hi body _ _ ihb =>
    exact exitCT_forFoldRevReturn M bi N leafSpec hsim i lo hi body ihb
  | forFold i lo hi body _ _ ihb => exact exitCT_forFold M bi N leafSpec hsim i lo hi body ihb
  | whileFold c body _ ihb =>
    cases c with
    | var v => exact exitCT_whileFold M bi N leafSpec hsim v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | cfBreak e _ => exact exitCT_cfBreak M bi N leafSpec hsim e
  | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)

/-- **The lowered function preserves the leakage.** For a function body of the fragment
    with exits at function level, two runs ending in a value from environments with
    equal source leakage, and two runs of `haxToLowCTFn e` from states agreeing with them
    off the reserved names, have equal traces. -/
theorem haxToLowCTFn_leak_eq (hs : ScalarOpsSound bi) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOk true true e = true) (hK : haxToLowCTFn e = some c)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : (denote' bi fuel e).run env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : (denote' bi fuel e).run env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : envAgreesOff env₁ rs₁) (hag₂ : envAgreesOff env₂ rs₂)
    (hL : srcLeak M bi e fuel env₁ = srcLeak M bi e fuel env₂)
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂) :
    t₁ = t₂ := by
  have hsim := haxToLowCTK_simulates bi N leafSpec hs
  unfold haxToLowCTFn at hK
  rcases hK0 : haxToLowCTK true true (some exitFnSlot) e with _ | ⟨c0, x⟩
  · rw [hK0] at hK; cases hK
  rw [hK0] at hK
  simp only [Option.map_some, Option.some.injEq] at hK
  subst hK
  have hctx : RunCtx (some exitFnSlot) := fun r h => Or.inr (Option.some.inj h).symm
  have hentry : ∀ {env : Env} {rs : RustState}, envAgreesOff env rs →
      envAgreesOff env (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0) ∧
        (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0).rsScalar exitRetName = 0 :=
    fun hag => ⟨envAgreesOff_set_reserved _ exitReserved_res
      (envAgreesOff_set_reserved _ exitReserved_ret hag), by simp [rsScalar_rsSetScalar]⟩
  obtain ⟨hag₁', hret₁'⟩ := hentry hag₁
  obtain ⟨hag₂', hret₂'⟩ := hentry hag₂
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₁ with
  | letU64Zero _ _ _ _ _ h₁ =>
  cases h₁ with
  | seq _ _ _ m₁ _ t0₁ tf₁ hc₁ hf₁ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  cases h₂ with
  | letU64Zero _ _ _ _ _ h₂ =>
  cases h₂ with
  | seq _ _ _ m₂ _ t0₂ tf₂ hc₂ hf₂ =>
  obtain ⟨ht, hx⟩ := haxToLowCTK_ct M bi N leafSpec hs e true (some exitFnSlot) fuel env₁ env₂
    env₁' env₂' o₁ o₂ _ _ m₁ m₂ c0 x t0₁ t0₂ hok hctx hK0 hrun₁ hval₁ hrun₂ hval₂ hag₁' hret₁'
    hag₂' hret₂' hL hc₁ hc₂
  obtain ⟨hE₁, -⟩ := exitSim_final M bi N leafSpec (hsim e) hok hctx hK0 hrun₁ hval₁ hag₁'
    hret₁' hc₁
  obtain ⟨hE₂, -⟩ := exitSim_final M bi N leafSpec (hsim e) hok hctx hK0 hrun₂ hval₂ hag₂'
    hret₂' hc₂
  have hf : m₁.rsScalar exitRetName = m₂.rsScalar exitRetName := by
    rw [envAgreesExit_flag hE₁, envAgreesExit_flag hE₂, hx]
  have htail : ∀ {m r : RustState} {tf : List CTLeak}, RustExecLeak N leafSpec M
      (.RIfNz exitRetName (.RScalarSetExpr exitResName (.SVar exitValName)) .RSkip) m tf r →
      tf = [.branch (m.rsScalar exitRetName != 0)] := by
    intro m r tf h
    cases h with
    | ifTrue _ _ _ _ _ _ _ hv hv0 hs => cases hs; subst hv; simp [hv0, sexprLeak]
    | ifFalse _ _ _ _ _ _ h0 hs => cases hs; simp [h0]
  rw [ht, htail hf₁, htail hf₂, hf]

/-- **Source constant time implies constant time of the lowered function**, for runs
    whose source counterparts end in a value: for a function body of the fragment, two
    runs of `haxToLowCTFn e` from states agreeing off the reserved names with
    environments that agree on the public variables of `lt` and from which the body runs
    to a value, have equal traces. -/
theorem haxToLowCTFn_ct (hs : ScalarOpsSound bi) (lt : LevelTable) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOk true true e = true) (hK : haxToLowCTFn e = some c)
    (hsrc : SourceCT M bi lt e)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak) (hpub : PubEqEnv lt env₁ env₂)
    (hrun₁ : (denote' bi fuel e).run env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : (denote' bi fuel e).run env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : envAgreesOff env₁ rs₁) (hag₂ : envAgreesOff env₂ rs₂)
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂) :
    t₁ = t₂ :=
  haxToLowCTFn_leak_eq M bi N leafSpec hs e c hok hK fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂
    r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂
    (hsrc fuel env₁ env₂ env₁' env₂' o₁ o₂ hpub hrun₁ hval₁ hrun₂ hval₂) h₁ h₂

end Assembly

end CatCrypt.Crypto.Hax
