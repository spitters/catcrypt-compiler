/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxExitLoopCT
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTyped

/-!
# The typed exit-flag lowering preserves constant time

For an expression of the fragment `exitSimOkT A R`, two runs of `denote'` that end in a
value, from environments whose source leakages (`srcLeak`) are equal, are matched by runs
of the typed lowering `haxToLowCTKT A` with equal `RustExecLeak` traces, from states
agreeing with the environments under the placement `A` (`envAgreesT`). With
`SourceCT`, two runs of the lowered function `haxToLowCTFnT A e` from states agreeing
with environments that agree on the public variables have equal traces.

`ExitCTT e` is that statement for `e`; as `ExitCT` of `HaxExitCT.lean` its conclusion
also states that the two source runs agree on whether they exit. The states the target
runs reach after a part are those of the simulation `haxToLowCTKT_simulates`, by
determinism of `RustExecLeak`. The loops are the agreement-generic lemmas of
`HaxExitLoopCT.lean` at `envAgreesT br A`.

A `letBind` head `k` runs as a prefix of the lowered body (`HeadPrefix`). The events of
the heads are: none for literals, copies and calls (`Silent`, for a leakage model
classing no leaf variable time); the operand events of a scalar operation, equal by the
source event `op`, or, for an operation outside `scalarOpExpr`, by the equal
environments of the source event `opaque`; the address event of an element load or
store, whose index is equal by the `opaque` event of `index` and `array_update`.

The statement covers target runs whose source counterparts end in a value.

## Main definitions

* `Silent`, `HeadPrefix`, `ExitCTT`

## Main results

* `haxToLowCTKT_ct` — every expression satisfies `ExitCTT`
* `haxToLowCTFnT_leak_eq`, `haxToLowCTFnT_ct`, `haxToLowCTFnI_ct` — the lowered function:
  equal source leakage, and source constant time, give equal traces
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak LowCTLeakModel sexprLeak RustExecLeak
  callLeak)

/-! ## Programs without events -/

section Silent

variable (M : LowCTLeakModel) (N : Nat) (leafSpec : LeafSpec)

/-- Every traced run of `c` has the empty trace. -/
def Silent (c : LowCT) : Prop :=
  ∀ rs t r, RustExecLeak N leafSpec M c rs t r → t = []

variable {M N leafSpec}

theorem silent_skip : Silent M N leafSpec .RSkip := by
  intro rs t r h; cases h; rfl

theorem silent_scalarSet (x : String) (k : Nat) : Silent M N leafSpec (.RScalarSet x k) := by
  intro rs t r h; cases h; rfl

theorem silent_setVar (x y : String) : Silent M N leafSpec (.RScalarSetExpr x (.SVar y)) := by
  intro rs t r h; cases h; rfl

theorem silent_setLimb (x y : String) (i : Nat) :
    Silent M N leafSpec (.RScalarSetExpr x (.SLimb y i)) := by
  intro rs t r h; cases h; rfl

theorem silent_copy (d s : Located) : Silent M N leafSpec (.RCopy d s) := by
  intro rs t r h; cases h; rfl

theorem silent_limbLit (loc : Located) (i k : Nat) :
    Silent M N leafSpec (.RLimbStoreExpr loc i (.SLit k)) := by
  intro rs t r h; cases h; rfl

theorem silent_seq {a b : LowCT} (ha : Silent M N leafSpec a) (hb : Silent M N leafSpec b) :
    Silent M N leafSpec (.RSeq a b) := by
  intro rs t r h
  cases h with
  | seq _ _ _ _ _ _ _ h1 h2 => rw [ha _ _ _ h1, hb _ _ _ h2]; rfl

theorem silent_letZero (x : String) (ty : TowerType) {b : LowCT} (hb : Silent M N leafSpec b) :
    Silent M N leafSpec (.RLetZero x ty b) := by
  intro rs t r h
  cases h with
  | letZero _ _ _ _ _ _ h => exact hb _ _ _ h

theorem silent_letU64Zero (x : String) {b : LowCT} (hb : Silent M N leafSpec b) :
    Silent M N leafSpec (.RLetU64Zero x b) := by
  intro rs t r h
  cases h with
  | letU64Zero _ _ _ _ _ h => exact hb _ _ _ h

/-- A leaf call has no event in a model classing no leaf variable time. -/
theorem silent_call (hvt : ∀ f, M.leafVT f = false) (f : String) (d : Located)
    (ls : List Located) : Silent M N leafSpec (.RCall f d ls) := by
  intro rs t r h
  cases h
  simp [callLeak, hvt]

theorem silent_storeScalar {slot : String} {e : ImpExpr} {s : LowCT}
    (h : storeScalar slot e = some s) : Silent M N leafSpec s := by
  cases e with
  | var x =>
    simp only [storeScalar, Option.some.injEq] at h
    subst h; exact silent_setVar _ _
  | lit l =>
    cases l <;> simp only [storeScalar, Option.some.injEq, reduceCtorEq] at h <;>
      (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
      (try subst h) <;> first | exact silent_scalarSet _ _ | cases h
  | unitVal =>
    simp only [storeScalar, Option.some.injEq] at h
    subst h; exact silent_scalarSet _ _
  | _ => simp [storeScalar] at h

theorem silent_tupleStoreT (A : ExitTowers) :
    ∀ (es : List ImpExpr) (i : Nat) (s : LowCT), tupleStoreT A i es = some s →
      Silent M N leafSpec s := by
  intro es
  induction es with
  | nil =>
    intro i s h
    simp only [tupleStoreT, Option.some.injEq] at h
    subst h; exact silent_skip
  | cons e es ih =>
    intro i s h
    cases e with
    | var x =>
      simp only [tupleStoreT, Option.map_eq_some_iff] at h
      obtain ⟨rest, hr, rfl⟩ := h
      have hs := ih (i + 1) rest hr
      split
      · exact silent_seq (silent_setVar _ _) hs
      · exact silent_seq (silent_copy _ _) hs
    | _ => simp [tupleStoreT] at h

theorem silent_resultStoreT {A : ExitTowers} {e : ImpExpr} {s : LowCT}
    (h : resultStoreT A e = some s) : Silent M N leafSpec s := by
  cases e with
  | var x =>
    simp only [resultStoreT] at h
    rcases hx : A.lookup x with _ | t <;> rw [hx] at h
    · exact silent_storeScalar h
    · simp only [Option.some.injEq] at h
      subst h; exact silent_copy _ _
  | tuple es => exact silent_tupleStoreT A es 0 s h
  | _ =>
    simp only [resultStoreT, resultStore] at h
    exact silent_storeScalar h

/-- A run of the marshalling context of `callMarshal` has the events of the run of the
    command it wraps, from a state with the same scalar heap. -/
theorem callMarshal_leak (A : ExitTowers) (dt : TowerType) :
    ∀ (args : List ImpExpr) (ctx : LowCT → LowCT) (ls : List Located),
      callMarshal A dt args = some (ctx, ls) →
      ∀ c rs t r, RustExecLeak N leafSpec M (ctx c) rs t r →
        ∃ rs0 : RustState, rs0.rsScalar = rs.rsScalar ∧ RustExecLeak N leafSpec M c rs0 t r := by
  intro args
  induction args with
  | nil =>
    intro ctx ls h
    simp only [callMarshal, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro c rs t r h
    exact ⟨rs, rfl, h⟩
  | cons a as ih =>
    intro ctx ls h
    cases a with
    | var x =>
      rcases hr : callMarshal A dt as with _ | ⟨ctx', ls'⟩
      · simp [callMarshal, hr] at h
      rcases hx : A.lookup x with _ | t
      · simp only [callMarshal, hr, hx] at h
        split_ifs at h with hmo
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro c rs tr r h
        cases h with
        | letZero _ _ _ _ _ _ h =>
        cases h with
        | seq _ _ _ _ _ t1 t2 h1 h2 =>
        cases h1 with
        | limbStoreExpr =>
        obtain ⟨rs0, hs0, h0⟩ := ih ctx' ls' hr c _ t2 r h2
        exact ⟨rs0, hs0, by simpa only [sexprLeak, List.nil_append] using h0⟩
      · simp only [callMarshal, hr, hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ih ctx' ls' hr
    | _ => simp [callMarshal] at h

theorem silent_ctx {A : ExitTowers} {dt : TowerType} {args : List ImpExpr}
    {ctx : LowCT → LowCT} {ls : List Located} (hm : callMarshal A dt args = some (ctx, ls))
    {c : LowCT} (hc : Silent M N leafSpec c) : Silent M N leafSpec (ctx c) := by
  intro rs t r h
  obtain ⟨rs0, -, h0⟩ := callMarshal_leak A dt args ctx ls hm c rs t r h
  exact hc _ _ _ h0

end Silent

/-! ## Heads as prefixes -/

section Prefix

variable (M : LowCTLeakModel) (N : Nat) (leafSpec : LeafSpec)

/-- A run of `k bC` is a run of `k .RSkip` followed by a run of `bC`. -/
def HeadPrefix (k : LowCT → LowCT) : Prop :=
  ∀ bC rs t r, RustExecLeak N leafSpec M (k bC) rs t r →
    ∃ q th tb, RustExecLeak N leafSpec M (k .RSkip) rs th q ∧
      RustExecLeak N leafSpec M bC q tb r ∧ t = th ++ tb

variable {M N leafSpec}

theorem headPrefix_id : HeadPrefix M N leafSpec (fun b => b) :=
  fun _ rs t _ h => ⟨rs, [], t, RustExecLeak.skip rs, h, rfl⟩

theorem headPrefix_seq (H : LowCT) {k : LowCT → LowCT} (hk : HeadPrefix M N leafSpec k) :
    HeadPrefix M N leafSpec (fun b => .RSeq H (k b)) := by
  intro bC rs t r h
  cases h with
  | seq _ _ _ m _ t1 t2 h1 h2 =>
    obtain ⟨q, th, tb, hk', hb, rfl⟩ := hk bC m t2 r h2
    exact ⟨q, t1 ++ th, tb, RustExecLeak.seq _ _ _ _ _ _ _ h1 hk', hb, by simp⟩

theorem headPrefix_letZero (x : String) (ty : TowerType) {k : LowCT → LowCT}
    (hk : HeadPrefix M N leafSpec k) : HeadPrefix M N leafSpec (fun b => .RLetZero x ty (k b)) := by
  intro bC rs t r h
  cases h with
  | letZero _ _ _ _ _ _ h =>
    obtain ⟨q, th, tb, hk', hb, rfl⟩ := hk bC _ t r h
    exact ⟨q, th, tb, RustExecLeak.letZero _ _ _ _ _ _ hk', hb, rfl⟩

theorem headPrefix_letU64Zero (x : String) {k : LowCT → LowCT}
    (hk : HeadPrefix M N leafSpec k) : HeadPrefix M N leafSpec (fun b => .RLetU64Zero x (k b)) := by
  intro bC rs t r h
  cases h with
  | letU64Zero _ _ _ _ _ h =>
    obtain ⟨q, th, tb, hk', hb, rfl⟩ := hk bC _ t r h
    exact ⟨q, th, tb, RustExecLeak.letU64Zero _ _ _ _ _ hk', hb, rfl⟩

/-- Every head of `letHeadT` runs as a prefix. -/
theorem letHeadT_prefix {A : ExitTowers} {n : String} {val : ImpExpr} {k : LowCT → LowCT}
    (hk : letHeadT A n val = some k) : HeadPrefix M N leafSpec k := by
  cases val with
  | lit l =>
    simp only [letHeadT] at hk
    rcases hA : A.lookup n with _ | t <;> rw [hA] at hk
    · cases l <;> simp only [letHead, Option.some.injEq, reduceCtorEq] at hk <;>
        (try split at hk) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hk) <;>
        (try subst hk) <;>
        first
          | exact headPrefix_letU64Zero _ (headPrefix_seq _ headPrefix_id)
          | cases hk
    · simp only at hk
      split_ifs at hk
      obtain ⟨kk, -, rfl⟩ := Option.map_eq_some_iff.mp hk
      exact headPrefix_letZero _ _ (headPrefix_seq _ headPrefix_id)
  | var s =>
    simp only [letHeadT] at hk
    split at hk
    · simp only [letHead] at hk
      split at hk <;> simp only [Option.some.injEq] at hk <;> subst hk
      · exact headPrefix_id
      · exact headPrefix_letU64Zero _ (headPrefix_seq _ headPrefix_id)
    · split at hk
      · split at hk <;> simp only [Option.some.injEq] at hk <;> subst hk
        · exact headPrefix_id
        · exact headPrefix_seq _ headPrefix_id
      · cases hk
    · cases hk
  | app f args =>
    have hk' : appHeadT A n f args = some k := hk
    unfold appHeadT at hk'
    rcases hso : scalarOpHeadT A n f args with _ | se
    · rw [hso] at hk'
      simp only at hk'
      have hcallP : ∀ {dt dr : TowerType}, callHeadAt A n f dt dr args = some k →
          HeadPrefix M N leafSpec k := fun hc => by
        obtain ⟨_, _, _, h⟩ := callHeadAt_some A hc
        rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          exact headPrefix_seq _ (headPrefix_seq _ headPrefix_id)
      split_ifs at hk' with hfi hfu hfl hfr
      · obtain ⟨_, _, _, _, _, _, h⟩ := indexHeadT_some A hk'
        rcases h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
          exact headPrefix_letZero _ _ (headPrefix_seq _ (headPrefix_seq _ headPrefix_id))
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := updateHeadT_some A hk'
        exact headPrefix_seq _ headPrefix_id
      · subst hfl
        obtain ⟨_, _, _, hc⟩ := arrLitHeadN_some A hk'
        exact hcallP hc
      · obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := repeatHeadT_some A hk'
        obtain ⟨_, _, _, h⟩ := callHeadAt_some A hc
        rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          exact headPrefix_seq _ (headPrefix_seq _ headPrefix_id)
      · obtain ⟨_, _, hc, -⟩ := callHeadT_some A hk'
        exact hcallP hc
    · rw [hso] at hk'
      simp only [Option.some.injEq] at hk'
      subst hk'
      exact headPrefix_seq _ headPrefix_id
  | _ => simp [letHeadT] at hk

end Prefix

/-! ## The statement -/

section Stmt

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)

/-- **Constant-time preservation of the typed lowering of `e`.** Two runs of `e` ending
    in a value, from environments with equal source leakage, and two runs of the lowered
    program from states agreeing with them under `A` with the exit flag `0`, have equal
    traces, and the source runs agree on whether they exit. -/
def ExitCTT (e : ImpExpr) : Prop :=
  ∀ (tl : Bool) (fl : Option String) (fuel : Nat) (env₁ env₂ env₁' env₂' : Env)
    (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState) (c : LowCT) (x : Bool)
    (t₁ t₂ : List CTLeak),
    exitSimOkT A R tl fl.isSome e = true → RunCtx fl →
    haxToLowCTKT A tl fl e = some (c, x) →
    (denote' bi fuel e).run env₁ = (o₁, env₁') → (∃ v, o₁ = .val v) →
    (denote' bi fuel e).run env₂ = (o₂, env₂') → (∃ v, o₂ = .val v) →
    envAgreesT br A env₁ rs₁ → rs₁.rsScalar exitRetName = 0 →
    envAgreesT br A env₂ rs₂ → rs₂.rsScalar exitRetName = 0 →
    srcLeak M bi e fuel env₁ = srcLeak M bi e fuel env₂ →
    RustExecLeak N leafSpec M c rs₁ t₁ r₁ → RustExecLeak N leafSpec M c rs₂ t₂ r₂ →
    t₁ = t₂ ∧ exitOf o₁ = exitOf o₂

end Stmt

section Helpers

variable {M : LowCTLeakModel} {bi : Builtins} {N : Nat} {leafSpec : LeafSpec}
  {br : ValueTowerBridge} {A : ExitTowers} {R : ExitRes}

/-- After a run agreeing with an outcome under `A`, the exit flag is `1` at an exit and
    `0` otherwise. -/
theorem envAgreesExitT_flag {tl : Bool} {o : Outcome} {env : Env} {rs : RustState}
    (h : envAgreesExitT br A R tl o env rs) :
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

theorem exitOf_eq_of_flagT {tl₁ tl₂ : Bool} {o₁ o₂ : Outcome} {env₁ env₂ : Env}
    {r₁ r₂ : RustState} (h₁ : envAgreesExitT br A R tl₁ o₁ env₁ r₁)
    (h₂ : envAgreesExitT br A R tl₂ o₂ env₂ r₂)
    (h : r₁.rsScalar exitRetName = r₂.rsScalar exitRetName) : exitOf o₁ = exitOf o₂ := by
  rw [envAgreesExitT_flag h₁, envAgreesExitT_flag h₂] at h
  revert h
  cases exitOf o₁ <;> cases exitOf o₂ <;> simp

theorem notCF_of_agreeT {tl : Bool} {v : Value} {env : Env} {rs : RustState}
    (h : envAgreesExitT br A R tl (.val v) env rs) (hx : exitOf (.val v) = false) :
    v.isControlFlow = false := by
  cases v with
  | controlFlow b w => cases b with
    | true => simp [exitOf] at hx
    | false => exact h.elim
  | _ => rfl

/-- The state a traced run of the typed lowering reaches agrees with the source
    outcome. -/
theorem exitSimT_final (hL : ExitLeaves bi leafSpec br (exitCallTys A)) {e : ImpExpr} {tl : Bool}
    {fl : Option String} {fuel : Nat} {env env' : Env} {o : Outcome} {rs r : RustState}
    {c : LowCT} {x : Bool} {t : List CTLeak}
    (hok : exitSimOkT A R tl fl.isSome e = true) (hfl : RunCtx fl)
    (hK : haxToLowCTKT A tl fl e = some (c, x))
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesT br A env rs) (hret : rs.rsScalar exitRetName = 0)
    (h : RustExecLeak N leafSpec M c rs t r) :
    envAgreesExitT br A R tl o env' r ∧ (x = false → r.rsScalar exitRetName = 0) := by
  obtain ⟨rs', hex, hagE, hx⟩ := haxToLowCTKT_simulates bi N leafSpec br A R hL e tl fl fuel
    env env' o rs c x hok hfl hK hrun hval hag hret
  obtain rfl := rustExecLeak_state_eq h hex
  exact ⟨hagE, hx⟩

/-- A typed lowering that cannot exit: the source run does not exit. -/
theorem exitOf_false_of_xT (hL : ExitLeaves bi leafSpec br (exitCallTys A)) {e : ImpExpr}
    {tl : Bool}
    {fl : Option String} {fuel : Nat} {env env' : Env} {o : Outcome} {rs r : RustState}
    {c : LowCT} {t : List CTLeak}
    (hok : exitSimOkT A R tl fl.isSome e = true) (hfl : RunCtx fl)
    (hK : haxToLowCTKT A tl fl e = some (c, false))
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesT br A env rs) (hret : rs.rsScalar exitRetName = 0)
    (h : RustExecLeak N leafSpec M c rs t r) : exitOf o = false := by
  obtain ⟨hE, hx⟩ := exitSimT_final hL hok hfl hK hrun hval hag hret h
  have h0 := hx rfl
  rw [envAgreesExitT_flag hE] at h0
  cases hc : exitOf o
  · rfl
  · rw [hc] at h0; simp at h0

/-- Writing a reserved scalar slot keeps `envAgreesT`. -/
theorem agResT : AgReserved (envAgreesT br A) :=
  fun _ k _ _ hx h => envAgreesT_set_reserved k hx h

/-- Binding a scalar loop counter to a word keeps `envAgreesT`. -/
theorem agExtT {i : String} (hi : exitReserved i = false) (his : A.lookup i = none) :
    ∀ (env : Env) (rs : RustState) (k : Nat), k < 2 ^ 64 → envAgreesT br A env rs →
      envAgreesT br A (env.extend i (.int k)) (rsSetScalar rs i k) :=
  fun _ _ k hk h => envAgreesT_extend hi his
    (show (0 : Int) ≤ (k : Int) ∧ (k : Int) < 2 ^ 64 from ⟨Int.natCast_nonneg k, by exact_mod_cast hk⟩)
    (valueToScalar_int k) h

/-- A scalar guard holding a bool decodes to `1` or `0`. -/
theorem agGuardT {c : String} (hc : exitReserved c = false) (hcs : A.lookup c = none) :
    ∀ (env : Env) (rs : RustState) (b : Bool), envAgreesT br A env rs →
      env c = some (.bool b) → rs.rsScalar c = if b then 1 else 0 := by
  intro env rs b h hb
  have hd := (envAgreesT_scalar h hc hcs hb).2
  rw [valueToScalar_bool, Option.some.injEq] at hd
  exact hd.symm

/-- The body of a typed loop satisfies `BodyRunAg` at `envAgreesT`. -/
theorem bodyRunT (hL : ExitLeaves bi leafSpec br (exitCallTys A)) {body : ImpExpr} {bC : LowCT}
    {run : String}
    {x : Bool} (hokB : exitSimOkT A R false true body = true) (hslot : exitRunSlot run = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, x)) :
    BodyRunAg M bi N leafSpec (envAgreesT br A) body bC := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  intro fuel env env' w rs r t hag hret hr h
  obtain ⟨hE, -⟩ := exitSimT_final hL hokB hctx hKB hr ⟨_, rfl⟩ hag hret h
  have hf := envAgreesExitT_flag hE
  refine ⟨fun hx => by simp [hf, hx], fun hx => ?_⟩
  have hcf := notCF_of_agreeT hE hx
  obtain ⟨h0, ha, -⟩ := (envAgreesExitT_val hcf).mp hE
  exact ⟨hcf, h0, ha⟩

/-- The body of a typed loop satisfies `BodyCTAg` at `envAgreesT`. -/
theorem bodyCTT {body : ImpExpr} {bC : LowCT} {run : String} {x : Bool}
    (ihb : ExitCTT M bi N leafSpec br A R body)
    (hokB : exitSimOkT A R false true body = true) (hslot : exitRunSlot run = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, x)) :
    BodyCTAg M bi N leafSpec (envAgreesT br A) body bC := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  intro fuel env₁ env₂ env₁' env₂' w₁ w₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hag₁ hret₁ hag₂ hret₂ hr₁ hr₂
    hL h₁ h₂
  exact ihb false (some run) fuel env₁ env₂ env₁' env₂' _ _ rs₁ rs₂ r₁ r₂ bC x t₁ t₂ hokB hctx
    hKB hr₁ ⟨_, rfl⟩ hr₂ ⟨_, rfl⟩ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂

end Helpers

/-! ## The heads of a `letBind` -/

section Heads

variable {M : LowCTLeakModel} {bi : Builtins} {N : Nat} {leafSpec : LeafSpec}
  {br : ValueTowerBridge} {A : ExitTowers} {R : ExitRes}

/-- The `SExpr` of a scalar operation of `scalarOpExpr` is that of `scalarOpExprT`. -/
theorem scalarOpExprT_of_scalarOpExpr {op : String} {a b se : SExpr}
    (h : scalarOpExpr op a b = some se) : scalarOpExprT op a b = some se := by
  unfold scalarOpExpr at h
  split at h <;> simp_all [scalarOpExprT]

/-- The `SExpr` of a scalar operation of `scalarOpExprT` on the variables `a` and `b`
    reads only `a` and `b`. -/
theorem scalarOpExprT_readsOnly {op a b : String} {se : SExpr}
    (h : scalarOpExprT op (.SVar a) (.SVar b) = some se) :
    sexprReadsOnly (fun x => x = a ∨ x = b) se := by
  unfold scalarOpExprT at h
  split at h
  all_goals first
    | (cases h; simp [sexprReadsOnly, orExprN])
    | skip
  obtain ⟨⟨w, o⟩, -, rfl⟩ := Option.map_eq_some_iff.mp h
  cases o <;> simp [WidthOp.sexpr, widthMask, orExprN, widthAmt, sexprReadsOnly]

/-- A run of `let n = f(args); body` ending in a value: the call runs to the builtin's
    value `r` without changing the environment, and the body runs from the environment
    extended by `n ↦ r`. -/
theorem app_run_inv (hplain : _root_.Hax.ContinueFlag.BuiltinsPlain bi) (fuel : Nat)
    (n f : String) (args : List ImpExpr) (body : ImpExpr) (hargs : exitArgsOk args = true)
    (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.letBind n (.app f args) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    ∃ vals r, List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) args vals ∧
      bi f vals = some r ∧ (denote' bi fuel (.app f args)).run env = (.val r, env) ∧
      (denote' bi fuel body).run (env.extend n r) = (o, env') := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel args).run env with ⟨oa, e1⟩
  obtain ⟨rfl, hF⟩ := denoteArgs'_vars_inv bi fuel args hargs env e1 oa hA
  have happ := denote'_app_run bi fuel f args e1
  rw [hA] at happ
  rcases oa with _ | vals
  · rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  · cases hbi : bi f vals with
    | none =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_val bi fuel n _ body e1 e1 r happ (hplain f vals r hbi)] at hrun
      exact ⟨vals, r, hF vals rfl, hbi, happ, hrun⟩

/-- A run of `let n = repeat(v, l); body` with a literal count ending in a value: the call
    runs to the builtin's value `r` on the value of `v` and the value of `l` without changing
    the environment, and the body runs from the environment extended by `n ↦ r`. -/
theorem repeat_run_inv (hplain : _root_.Hax.ContinueFlag.BuiltinsPlain bi) (fuel : Nat)
    (n v : String) (l : ImpLit) (body : ImpExpr) (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.letBind n (.app "repeat" [.var v, .lit l]) body)).run env =
      (o, env'))
    (hval : ∃ w, o = .val w) :
    ∃ vv r, env v = some vv ∧ bi "repeat" [vv, Value.ofLit l] = some r ∧
      (denote' bi fuel (.app "repeat" [.var v, .lit l])).run env = (.val r, env) ∧
      (denote' bi fuel body).run (env.extend n r) = (o, env') := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel [.var v, .lit l]).run env with ⟨oa, e1⟩
  obtain ⟨rfl, hF⟩ := denoteArgs'_varLit_inv bi fuel v l env e1 oa hA
  have happ := denote'_app_run bi fuel "repeat" [.var v, .lit l] e1
  rw [hA] at happ
  rcases oa with _ | vals
  · rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  · obtain ⟨vv, hvv, rfl⟩ := hF _ rfl
    cases hbi : bi "repeat" [vv, Value.ofLit l] with
    | none =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_val bi fuel n _ body e1 e1 r happ (hplain _ _ r hbi)] at hrun
      exact ⟨vv, r, hvv, hbi, happ, hrun⟩

/-- The head of `let n = l`: `HeadResT` at the literal's value. -/
theorem headResT_lit (hmar : ExitMarshal br leafSpec) {n : String} {l : ImpLit} {k : LowCT → LowCT} {env : Env} {rs : RustState}
    (hl : exitLitOk l = true) (hn : exitReserved n = false) (hk : letHeadT A n (.lit l) = some k)
    (hag : envAgreesT br A env rs) (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n (Value.ofLit l) k := by
  have hsv := exitLitOk_scalarValN hl
  rcases hsc' : A.lookup n with _ | t
  · have hk' : letHead n (.lit l) = some k := by simpa [letHeadT, hsc'] using hk
    obtain ⟨kk, hkk, hdk⟩ : ∃ kk, k = (fun bC => .RLetU64Zero n (.RSeq (.RScalarSet n kk) bC)) ∧
        valueToScalar (Value.ofLit l) = some kk := by
      cases l with
      | uintLit w m =>
        simp only [letHead, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, rfl⟩
      | int z =>
        simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
        simp only [letHead, ge_iff_le, hl.1, if_true, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, by simp [valueToScalar, Value.ofLit, hl.1]⟩
      | bool b =>
        simp only [letHead, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, valueToScalar_bool b⟩
      | unit => simp [letHead] at hk'
      | _ => simp [exitLitOk] at hl
    subst hkk
    exact ⟨_, envAgreesT_extend hn hsc' hsv hdk hag, ret_setScalar hn _ hret,
      fun bC rs' h => exec_letU64_set N leafSpec n kk bC rs rs' h⟩
  · simp only [letHeadT, hsc'] at hk
    split_ifs at hk with hmo
    obtain ⟨kk, hdk, rfl⟩ := Option.map_eq_some_iff.mp hk
    have h8 : 8 ≤ t.storageBytes := by simpa [exitMarshalOk] using hmo
    refine ⟨rsSetTower rs n ⟨t, leafSpec.limbStore ⟨n, t⟩ default 0 (BitVec.ofNat 64 kk)⟩,
      envAgreesT_extend_tower hn hsc' hsv.not_cf (hmar ⟨n, t⟩ _ kk h8 hsv hdk) hag, hret,
      fun bC rs' h => ?_⟩
    refine RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _
      (RustExec.limbStoreExpr _ _ _ _ default ?_) ?_)
    · exact locatedLookup_of_rsTower _ _ t default
        (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _)
    · simpa only [locatedUpdate, SExpr.evalState, rsSetTower_rsSetTower] using h

/-- The head of `let n = s`: `HeadResT` at the value of `s`. -/
theorem headResT_var {n s : String} {k : LowCT → LowCT} {env : Env} {rs : RustState}
    {w : Value} (hn : exitReserved n = false) (hs : exitReserved s = false)
    (hns : A.lookup n = A.lookup s) (hw : env s = some w)
    (hk : letHeadT A n (.var s) = some k)
    (hag : envAgreesT br A env rs) (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n w k := by
  have hcf := envAgreesT_not_cf hag hs hw
  rcases hA : A.lookup s with _ | t
  · rw [hA] at hns
    simp only [letHeadT, hns, hA, letHead] at hk
    obtain ⟨hsv, hdv⟩ := envAgreesT_scalar hag hs hA hw
    by_cases hsn : n = s
    · subst hsn
      simp only [if_true, Option.some.injEq] at hk
      subst hk
      refine ⟨rs, ?_, hret, fun bC rs' h => h⟩
      rw [Env.extend_self env n w hw]
      exact hag
    · simp only [hsn, if_false, Option.some.injEq] at hk
      subst hk
      exact ⟨_, envAgreesT_extend hn hns hsv hdv hag, ret_setScalar hn _ hret,
        fun bC rs' h => rustExec_letBind_copy N leafSpec n s bC rs rs' hsn h⟩
  · rw [hA] at hns
    simp only [letHeadT, hns, hA, if_true] at hk
    obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hag hs hA hw
    by_cases hsn : n = s
    · subst hsn
      simp only [if_true, Option.some.injEq] at hk
      subst hk
      refine ⟨rs, ?_, hret, fun bC rs' h => h⟩
      rw [Env.extend_self env n w hw]
      exact hag
    · simp only [hsn, if_false, Option.some.injEq] at hk
      subst hk
      refine ⟨rsSetTower rs n ⟨t, val⟩, envAgreesT_extend_tower hn hns hcf hbr hag, hret,
        fun bC rs' h => ?_⟩
      exact RustExec.seq _ _ _ _ _
        (RustExec.copy ⟨n, t⟩ ⟨s, t⟩ rs rfl val (locatedLookup_of_rsTower rs s t val hval')) h

/-- The head of `let n = f(args)`: `HeadResT` at the builtin's value. -/
theorem headResT_app (hL : ExitLeaves bi leafSpec br (exitCallTys A)) {n f : String}
    {args : List ImpExpr}
    {k : LowCT → LowCT} {env : Env} {rs : RustState} {vals : List Value} {r : Value}
    (hk : appHeadT A n f args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k :=
  headT_app hL hk hn hargs hF hbi hag hret

/-- The state a traced run of a head reaches is the state of `HeadResT`. -/
theorem headResT_state {env : Env} {rs q : RustState} {n : String} {w : Value}
    {k : LowCT → LowCT} {th : List CTLeak} (hr : HeadResT N leafSpec br A env rs n w k)
    (h : RustExecLeak N leafSpec M (k .RSkip) rs th q) :
    envAgreesT br A (env.extend n w) q ∧ q.rsScalar exitRetName = 0 := by
  obtain ⟨rs1, ha, hret, hex⟩ := hr
  obtain rfl := rustExecLeak_state_eq h (hex .RSkip rs1 (RustExec.skip rs1))
  exact ⟨ha, hret⟩

/-- The events of the head of a call, element load or element store, from states
    agreeing with environments whose source leakage of the call is equal. -/
theorem headTrace_app (hvt : ∀ f, M.leafVT f = false) {n f : String} {args : List ImpExpr}
    {k : LowCT → LowCT} (hk : appHeadT A n f args = some k) (hargs : exitArgsOk args = true)
    {fuel : Nat} {env₁ env₂ : Env} {rs₁ rs₂ q₁ q₂ : RustState} {th₁ th₂ : List CTLeak}
    {vals₁ vals₂ : List Value}
    (hF₁ : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env₁ x = some v) args vals₁)
    (hF₂ : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env₂ x = some v) args vals₂)
    (hag₁ : envAgreesT br A env₁ rs₁) (hag₂ : envAgreesT br A env₂ rs₂)
    (hL : srcLeak M bi (.app f args) fuel env₁ = srcLeak M bi (.app f args) fuel env₂)
    (h₁ : RustExecLeak N leafSpec M (k .RSkip) rs₁ th₁ q₁)
    (h₂ : RustExecLeak N leafSpec M (k .RSkip) rs₂ th₂ q₂) : th₁ = th₂ := by
  unfold appHeadT at hk
  rcases hso : scalarOpHeadT A n f args with _ | se
  · rw [hso] at hk
    simp only at hk
    have hcallS : ∀ {dt dr : TowerType}, callHeadAt A n f dt dr args = some k →
        Silent M N leafSpec (k .RSkip) := fun hc => by
      obtain ⟨ctx, ls, hm, hcase⟩ := callHeadAt_some A hc
      rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact silent_seq (silent_letZero _ _ (silent_ctx hm (silent_call hvt _ _ _)))
          (silent_seq (silent_setLimb _ _ _) silent_skip)
      · exact silent_seq (silent_letZero _ _ (silent_ctx hm (silent_call hvt _ _ _)))
          (silent_seq (silent_copy _ _) silent_skip)
    split_ifs at hk with hfi hfu hfl hfr
    · -- the element load
      subst hfi
      obtain ⟨arr, idx, t, rfl, hat, hid, hcase⟩ := indexHeadT_some A hk
      simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
      obtain ⟨va, vi, rfl, hva, hvi⟩ := forall₂_var2 hF₁
      obtain ⟨va', vi', rfl, hva', hvi'⟩ := forall₂_var2 hF₂
      have hnone : scalarOpExpr "index" (.SVar arr) (.SVar idx) = none := by
        first | rfl | decide | simp [scalarOpExpr]
      have henv : env₁ = env₂ := by
        simp only [srcLeak, opLeak, hnone, SrcLeak.ev.injEq, SrcEv.opaque.injEq] at hL
        first | exact hL.1 | exact hL
      subst henv
      rw [hvi] at hvi'
      cases hvi'
      have hi : rs₁.rsScalar idx = rs₂.rsScalar idx := by
        have d₁ := (envAgreesT_scalar hag₁ hargs.2.1 hid hvi).2
        have d₂ := (envAgreesT_scalar hag₂ hargs.2.1 hid hvi).2
        rw [d₁] at d₂
        exact Option.some.inj d₂
      have htr : ∀ {rs q : RustState} {th : List CTLeak}, RustExecLeak N leafSpec M
          (k .RSkip) rs th q → th = [.addr arr (rs.rsScalar idx)] := by
        intro rs q th h
        rcases hcase with ⟨-, -, rfl⟩ | ⟨t', -, -, rfl⟩
        · cases h with
          | letZero _ _ _ _ _ _ h =>
          cases h with
          | seq _ _ _ _ _ _ _ h1 h2 =>
          cases h1 with
          | arrLoad _ _ _ _ _ _ _ hidx _ _ =>
          cases h2 with
          | seq _ _ _ _ _ _ _ h3 h4 =>
          cases h3
          cases h4
          subst hidx
          rfl
        · cases h with
          | letZero _ _ _ _ _ _ h =>
          cases h with
          | seq _ _ _ _ _ _ _ h1 h2 =>
          cases h1 with
          | arrLoad _ _ _ _ _ _ _ hidx _ _ =>
          cases h2 with
          | seq _ _ _ _ _ _ _ h3 h4 =>
          cases h3
          cases h4
          subst hidx
          rfl
      rw [htr h₁, htr h₂, hi]
    · -- the element store
      subst hfu
      obtain ⟨arr, idx, src, t, ctx, srcLoc, rfl, rfl, hat, hid, -, hm, -, rfl⟩ :=
        updateHeadT_some A hk
      simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
      obtain ⟨va, vi, vs, rfl, hva, hvi, hvs⟩ := forall₂_var3 hF₁
      obtain ⟨va', vi', vs', rfl, hva', hvi', hvs'⟩ := forall₂_var3 hF₂
      have henv : env₁ = env₂ := by
        simp only [srcLeak, SrcLeak.ev.injEq, SrcEv.opaque.injEq] at hL
        first | exact hL.1 | exact hL
      subst henv
      rw [hvi] at hvi'
      cases hvi'
      have hi : rs₁.rsScalar idx = rs₂.rsScalar idx := by
        have d₁ := (envAgreesT_scalar hag₁ hargs.2.1 hid hvi).2
        have d₂ := (envAgreesT_scalar hag₂ hargs.2.1 hid hvi).2
        rw [d₁] at d₂
        exact Option.some.inj d₂
      have htr : ∀ {rs q : RustState} {th : List CTLeak}, RustExecLeak N leafSpec M
          (.RSeq (ctx (.RArrStore ⟨n, t⟩ idx srcLoc)) .RSkip) rs th q →
          th = [.addr n (rs.rsScalar idx)] := by
        intro rs q th h
        cases h with
        | seq _ _ _ _ _ _ _ h1 h2 =>
        cases h2
        obtain ⟨rs0, hs0, h0⟩ := callMarshal_leak A (exitElem t) _ ctx [srcLoc] hm _ _ _ _ h1
        cases h0 with
        | arrStore _ _ _ _ _ _ _ hidx _ _ =>
        subst hidx
        rw [hs0]
        rfl
      rw [htr h₁, htr h₂, hi]
    · -- an array literal: a call
      subst hfl
      obtain ⟨_, _, _, hc⟩ := arrLitHeadN_some A hk
      have hsil : Silent M N leafSpec (k .RSkip) := hcallS hc
      rw [hsil _ _ _ h₁, hsil _ _ _ h₂]
    · -- a `repeat` with a literal count: a call
      obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := repeatHeadT_some A hk
      have hsil : Silent M N leafSpec (k .RSkip) := by
        obtain ⟨ctx, ls, hm, hcase⟩ := callHeadAt_some A hc
        rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact silent_seq (silent_letZero _ _ (silent_ctx hm (silent_call hvt _ _ _)))
            (silent_seq (silent_setLimb _ _ _) silent_skip)
        · exact silent_seq (silent_letZero _ _ (silent_ctx hm (silent_call hvt _ _ _)))
            (silent_seq (silent_copy _ _) silent_skip)
      rw [hsil _ _ _ h₁, hsil _ _ _ h₂]
    · -- a call
      obtain ⟨_, _, hc, -⟩ := callHeadT_some A hk
      have hsil : Silent M N leafSpec (k .RSkip) := hcallS hc
      rw [hsil _ _ _ h₁, hsil _ _ _ h₂]
  · -- a scalar operation
    rw [hso] at hk
    simp only [Option.some.injEq] at hk
    subst hk
    obtain ⟨a, b, rfl, hnA, haA, hbA, hse⟩ := scalarOpHeadT_some A hso
    simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
    have htr : ∀ {rs q : RustState} {th : List CTLeak}, RustExecLeak N leafSpec M
        (.RSeq (.RScalarSetExpr n se) .RSkip) rs th q → th = sexprLeak M rs se := by
      intro rs q th h
      cases h with
      | seq _ _ _ _ _ _ _ h1 h2 => cases h1; cases h2; simp
    have hcong : ∀ {env : Env} {rs : RustState} {vals : List Value},
        List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v)
          [.var a, .var b] vals → envAgreesT br A env rs →
        sexprLeak M rs se = sexprLeak M (envScalarState env) se := by
      intro env rs vals hF hag
      obtain ⟨va, vb, rfl, hva, hvb⟩ := forall₂_var2 hF
      have hda := (envAgreesT_scalar hag hargs.1 haA hva).2
      have hdb := (envAgreesT_scalar hag hargs.2.1 hbA hvb).2
      have hS : ∀ x, (x = a ∨ x = b) → rs.rsScalar x = (envScalarState env).rsScalar x := by
        rintro x (rfl | rfl)
        · simp only [envScalarState, hva, Option.bind_some, hda, Option.getD_some]
        · simp only [envScalarState, hvb, Option.bind_some, hdb, Option.getD_some]
      exact sexprLeak_congr M hS se (scalarOpExprT_readsOnly hse)
    rw [htr h₁, htr h₂, hcong hF₁ hag₁, hcong hF₂ hag₂]
    simp only [srcLeak, opLeak] at hL
    rcases hso' : scalarOpExpr f (.SVar a) (.SVar b) with _ | se'
    · rw [hso'] at hL
      simp only [SrcLeak.ev.injEq, SrcEv.opaque.injEq] at hL
      rw [hL.1]
    · rw [hso'] at hL
      have hee : se' = se := by
        rw [scalarOpExprT_of_scalarOpExpr hso'] at hse
        exact Option.some.inj hse
      subst hee
      simpa only [SrcLeak.ev.injEq, SrcEv.op.injEq] using hL

end Heads

/-! ## The arms without a loop -/

section Arms

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)

/-- The head of a literal binding has no event. -/
theorem litHead_silent {n : String} {l : ImpLit} {k : LowCT → LowCT}
    (hk : letHeadT A n (.lit l) = some k) : Silent M N leafSpec (k .RSkip) := by
  simp only [letHeadT] at hk
  rcases hA : A.lookup n with _ | t <;> rw [hA] at hk
  · cases l <;> simp only [letHead, Option.some.injEq, reduceCtorEq] at hk <;>
      (try split at hk) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hk) <;>
      (try subst hk) <;>
      first
        | exact silent_letU64Zero _ (silent_seq (silent_scalarSet _ _) silent_skip)
        | cases hk
  · simp only at hk
    split_ifs at hk
    obtain ⟨kk, -, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact silent_letZero _ _ (silent_seq (silent_limbLit _ _ _) silent_skip)

/-- The head of a copy has no event. -/
theorem varHead_silent {n s : String} {k : LowCT → LowCT}
    (hk : letHeadT A n (.var s) = some k) : Silent M N leafSpec (k .RSkip) := by
  simp only [letHeadT] at hk
  split at hk
  · simp only [letHead] at hk
    split at hk <;> simp only [Option.some.injEq] at hk <;> subst hk
    · exact silent_skip
    · exact silent_letU64Zero _ (silent_seq (silent_setVar _ _) silent_skip)
  · split at hk
    · split at hk <;> simp only [Option.some.injEq] at hk <;> subst hk
      · exact silent_skip
      · exact silent_seq (silent_copy _ _) silent_skip
    · cases hk
  · cases hk

theorem exitCTT_letBind (hvt : ∀ f, M.leafVT f = false)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A))
    (n : String) (val body : ImpExpr) (ihb : ExitCTT M bi N leafSpec br A R body) :
    ExitCTT M bi N leafSpec br A R (.letBind n val body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hLk h₁ h₂
  rw [haxToLowCTKT_letBind_eq] at hK
  rcases hk : letHeadT A n val with _ | k
  · rw [hk] at hK; cases hK
  rcases hB : haxToLowCTKT A tl fl body with _ | ⟨bC, x⟩
  · rw [hk, hB] at hK; cases hK
  rw [hk, hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  have hokB := exitSimOkT_letBind_body A R _ _ n val body hok
  obtain ⟨q₁, th₁, tb₁, hk₁, hb₁, rfl⟩ := letHeadT_prefix hk bC rs₁ t₁ r₁ h₁
  obtain ⟨q₂, th₂, tb₂, hk₂, hb₂, rfl⟩ := letHeadT_prefix hk bC rs₂ t₂ r₂ h₂
  suffices H : (srcLeak M bi val fuel env₁ = srcLeak M bi val fuel env₂ → th₁ = th₂) ∧
      ∃ w₁ w₂, (denote' bi fuel val).run env₁ = (.val w₁, env₁) ∧
        (denote' bi fuel val).run env₂ = (.val w₂, env₂) ∧
        w₁.isControlFlow = false ∧ w₂.isControlFlow = false ∧
        (denote' bi fuel body).run (env₁.extend n w₁) = (o₁, env₁') ∧
        (denote' bi fuel body).run (env₂.extend n w₂) = (o₂, env₂') ∧
        HeadResT N leafSpec br A env₁ rs₁ n w₁ k ∧ HeadResT N leafSpec br A env₂ rs₂ n w₂ k by
    obtain ⟨hth, w₁, w₂, hv₁, hv₂, hcf₁, hcf₂, hr₁, hr₂, hR₁, hR₂⟩ := H
    obtain ⟨ha₁, hq₁⟩ := headResT_state hR₁ hk₁
    obtain ⟨ha₂, hq₂⟩ := headResT_state hR₂ hk₂
    simp only [srcLeak, hv₁, hv₂, contLeak_val hcf₁, contLeak_val hcf₂] at hLk
    injection hLk with hLa hLb
    obtain ⟨ht, hx⟩ := ihb tl fl fuel _ _ env₁' env₂' o₁ o₂ q₁ q₂ r₁ r₂ bC x tb₁ tb₂ hokB hfl hB
      hr₁ hval₁ hr₂ hval₂ ha₁ hq₁ ha₂ hq₂ hLb hb₁ hb₂
    exact ⟨by rw [hth hLa, ht], hx⟩
  cases val with
  | lit l =>
    have hh : exitLitOk l = true ∧ exitReserved n = false := by
      cases tl <;> cases fl <;>
        (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
         exact ⟨hok.1.1, hok.1.2⟩)
    have hsv := exitLitOk_scalarValN hh.1
    have hv : ∀ env, (denote' bi fuel (.lit l)).run env = (.val (Value.ofLit l), env) :=
      fun env => denote'_lit_run bi fuel l env
    rw [denote'_letBind_run_val bi fuel n _ body env₁ env₁ _ (hv env₁) hsv.not_cf] at hrun₁
    rw [denote'_letBind_run_val bi fuel n _ body env₂ env₂ _ (hv env₂) hsv.not_cf] at hrun₂
    have hsil := litHead_silent M N leafSpec A hk
    exact ⟨fun _ => (hsil _ _ _ hk₁).trans (hsil _ _ _ hk₂).symm, _, _, hv env₁, hv env₂,
      hsv.not_cf, hsv.not_cf, hrun₁, hrun₂, headResT_lit hL.marshal hh.1 hh.2 hk hag₁ hret₁,
      headResT_lit hL.marshal hh.1 hh.2 hk hag₂ hret₂⟩
  | var s =>
    have hh : exitReserved n = false ∧ exitReserved s = false ∧ A.lookup n = A.lookup s := by
      cases tl <;> cases fl <;>
        (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
         exact ⟨hok.1.1.1, hok.1.1.2, hok.1.2⟩)
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
    have hcf₁ := envAgreesT_not_cf hag₁ hh.2.1 hw₁
    have hcf₂ := envAgreesT_not_cf hag₂ hh.2.1 hw₂
    have hr₁ : (denote' bi fuel (.var s)).run env₁ = (.val w₁, env₁) := by
      rw [denote'_var_run, hw₁]
    have hr₂ : (denote' bi fuel (.var s)).run env₂ = (.val w₂, env₂) := by
      rw [denote'_var_run, hw₂]
    rw [denote'_letBind_run_val bi fuel n _ body env₁ env₁ w₁ hr₁ hcf₁] at hrun₁
    rw [denote'_letBind_run_val bi fuel n _ body env₂ env₂ w₂ hr₂ hcf₂] at hrun₂
    have hsil := varHead_silent M N leafSpec A hk
    exact ⟨fun _ => (hsil _ _ _ hk₁).trans (hsil _ _ _ hk₂).symm, w₁, w₂, hr₁, hr₂, hcf₁,
      hcf₂, hrun₁, hrun₂, headResT_var hh.1 hh.2.1 hh.2.2 hw₁ hk hag₁ hret₁,
      headResT_var hh.1 hh.2.1 hh.2.2 hw₂ hk hag₂ hret₂⟩
  | app f args =>
    have hh : exitReserved n = false ∧ exitArgsOkT f args = true := by
      cases tl <;> cases fl <;>
        (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
         exact ⟨hok.1.1.1, hok.1.1.2⟩)
    have hk' : appHeadT A n f args = some k := hk
    by_cases hargs : exitArgsOk args = true
    · obtain ⟨vals₁, w₁, hF₁, hbi₁, hv₁, hrun₁'⟩ :=
        app_run_inv hL.plain fuel n f args body hargs env₁ env₁' o₁ hrun₁ hval₁
      obtain ⟨vals₂, w₂, hF₂, hbi₂, hv₂, hrun₂'⟩ :=
        app_run_inv hL.plain fuel n f args body hargs env₂ env₂' o₂ hrun₂ hval₂
      exact ⟨fun hLa => headTrace_app hvt hk' hargs hF₁ hF₂ hag₁ hag₂ hLa hk₁ hk₂, w₁, w₂, hv₁,
        hv₂, hL.plain _ _ _ hbi₁, hL.plain _ _ _ hbi₂, hrun₁', hrun₂',
        headResT_app hL hk' hh.1 hargs hF₁ hbi₁ hag₁ hret₁,
        headResT_app hL hk' hh.1 hargs hF₂ hbi₂ hag₂ hret₂⟩
    · have hrep : f = "repeat" ∧ exitRepeatArgsOk args = true := by
        simpa [exitArgsOkT, hargs] using hh.2
      obtain ⟨rfl, hra⟩ := hrep
      match args, hra with
      | [.var v, .lit l], hra =>
        simp only [exitRepeatArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hra
        have hkr : repeatHeadT A n [.var v, .lit l] = some k := by
          simpa [appHeadT, scalarOpHeadT] using hk'
        obtain ⟨vv₁, w₁, hx₁, hbi₁, hv₁, hrun₁'⟩ :=
          repeat_run_inv hL.plain fuel n v l body env₁ env₁' o₁ hrun₁ hval₁
        obtain ⟨vv₂, w₂, hx₂, hbi₂, hv₂, hrun₂'⟩ :=
          repeat_run_inv hL.plain fuel n v l body env₂ env₂' o₂ hrun₂ hval₂
        have hsil : Silent M N leafSpec (k .RSkip) := by
          obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := repeatHeadT_some A hkr
          obtain ⟨ctx, ls, hm, hcase⟩ := callHeadAt_some A hc
          rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact silent_seq (silent_letZero _ _ (silent_ctx hm (silent_call hvt _ _ _)))
              (silent_seq (silent_setLimb _ _ _) silent_skip)
          · exact silent_seq (silent_letZero _ _ (silent_ctx hm (silent_call hvt _ _ _)))
              (silent_seq (silent_copy _ _) silent_skip)
        exact ⟨fun _ => (hsil _ _ _ hk₁).trans (hsil _ _ _ hk₂).symm, w₁, w₂, hv₁, hv₂,
          hL.plain _ _ _ hbi₁, hL.plain _ _ _ hbi₂, hrun₁', hrun₂',
          headT_repeat hL hkr hh.1 hra.1 hx₁ hbi₁ hag₁ hret₁,
          headT_repeat hL hkr hh.1 hra.1 hx₂ hbi₂ hag₂ hret₂⟩
  | _ => simp [letHeadT] at hk

/-- An expression whose lowerings cannot exit and have no event. -/
theorem exitCTT_of_silent (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (e : ImpExpr)
    (hS : ∀ tl fl c x, exitSimOkT A R tl (Option.isSome fl) e = true →
      haxToLowCTKT A tl fl e = some (c, x) → x = false ∧ Silent M N leafSpec c) :
    ExitCTT M bi N leafSpec br A R e := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ _ h₁ h₂
  obtain ⟨rfl, hs⟩ := hS tl fl c xb hok hK
  refine ⟨(hs _ _ _ h₁).trans (hs _ _ _ h₂).symm, ?_⟩
  rw [exitOf_false_of_xT hL hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁,
    exitOf_false_of_xT hL hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂]

theorem exitCTT_var (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (x : String) :
    ExitCTT M bi N leafSpec br A R (.var x) :=
  exitCTT_of_silent M bi N leafSpec br A R hL _ fun tl fl c xb _ hK => by
    cases tl with
    | false =>
      have hK' : haxToLowCTKT A false fl (.var x) = some (.RSkip, false) := by cases fl <;> rfl
      rw [hK'] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      exact ⟨rfl, silent_skip⟩
    | true =>
      have hK' : haxToLowCTKT A true fl (.var x) =
          (resultStoreT A (.var x)).map fun s => (s, false) := by cases fl <;> rfl
      rw [hK'] at hK
      obtain ⟨s, hs, hsx⟩ := Option.map_eq_some_iff.mp hK
      simp only [Prod.mk.injEq] at hsx
      obtain ⟨rfl, rfl⟩ := hsx
      exact ⟨rfl, silent_resultStoreT hs⟩

theorem exitCTT_unitVal (hL : ExitLeaves bi leafSpec br (exitCallTys A)) :
    ExitCTT M bi N leafSpec br A R .unitVal :=
  exitCTT_of_silent M bi N leafSpec br A R hL _ fun tl fl c xb _ hK => by
    cases tl with
    | false =>
      have hK' : haxToLowCTKT A false fl .unitVal = some (.RSkip, false) := by cases fl <;> rfl
      rw [hK'] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      exact ⟨rfl, silent_skip⟩
    | true =>
      have hK' : haxToLowCTKT A true fl .unitVal =
          (resultStoreT A .unitVal).map fun s => (s, false) := by cases fl <;> rfl
      rw [hK'] at hK
      obtain ⟨s, hs, hsx⟩ := Option.map_eq_some_iff.mp hK
      simp only [Prod.mk.injEq] at hsx
      obtain ⟨rfl, rfl⟩ := hsx
      exact ⟨rfl, silent_resultStoreT hs⟩

theorem exitCTT_lit (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (l : ImpLit) :
    ExitCTT M bi N leafSpec br A R (.lit l) :=
  exitCTT_of_silent M bi N leafSpec br A R hL _ fun tl fl c xb hok hK => by
    cases tl with
    | false => cases fl <;> simp [exitSimOkT] at hok
    | true =>
      have hK' : haxToLowCTKT A true fl (.lit l) =
          (resultStoreT A (.lit l)).map fun s => (s, false) := by cases fl <;> rfl
      rw [hK'] at hK
      obtain ⟨s, hs, hsx⟩ := Option.map_eq_some_iff.mp hK
      simp only [Prod.mk.injEq] at hsx
      obtain ⟨rfl, rfl⟩ := hsx
      exact ⟨rfl, silent_resultStoreT hs⟩

theorem exitCTT_tuple (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (es : List ImpExpr) :
    ExitCTT M bi N leafSpec br A R (.tuple es) :=
  exitCTT_of_silent M bi N leafSpec br A R hL _ fun tl fl c xb hok hK => by
    cases tl with
    | false => cases fl <;> simp [exitSimOkT] at hok
    | true =>
      have hK' : haxToLowCTKT A true fl (.tuple es) =
          (resultStoreT A (.tuple es)).map fun s => (s, false) := by cases fl <;> rfl
      rw [hK'] at hK
      obtain ⟨s, hs, hsx⟩ := Option.map_eq_some_iff.mp hK
      simp only [Prod.mk.injEq] at hsx
      obtain ⟨rfl, rfl⟩ := hsx
      exact ⟨rfl, silent_resultStoreT hs⟩

theorem exitCTT_cfBreak (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (p : ImpExpr) :
    ExitCTT M bi N leafSpec br A R (.cfBreak p) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ _ h₁ h₂
  obtain ⟨hE₁, -⟩ := exitSimT_final hL hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
  obtain ⟨hE₂, -⟩ := exitSimT_final hL hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
  cases fl with
  | none => cases tl <;> simp [exitSimOkT] at hok
  | some r =>
    have hK' : haxToLowCTKT A tl (some r) (.cfBreak p) = (exitStore p).map fun s => (s, true) := by
      cases tl <;> rfl
    rw [hK'] at hK
    obtain ⟨s', hs', hsx⟩ := Option.map_eq_some_iff.mp hK
    simp only [Prod.mk.injEq] at hsx
    obtain ⟨rfl, rfl⟩ := hsx
    unfold exitStore at hs'
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hs'
    have hsil : Silent M N leafSpec (.RSeq s (.RScalarSet exitRetName 1)) :=
      silent_seq (silent_storeScalar hs) (silent_scalarSet _ _)
    have hfin : ∀ {rs r : RustState} {t : List CTLeak},
        RustExecLeak N leafSpec M (.RSeq s (.RScalarSet exitRetName 1)) rs t r →
        r.rsScalar exitRetName = 1 := by
      intro rs r t h
      cases h with
      | seq _ _ _ _ _ _ _ _ hb => cases hb; simp
    exact ⟨(hsil _ _ _ h₁).trans (hsil _ _ _ h₂).symm,
      exitOf_eq_of_flagT hE₁ hE₂ ((hfin h₁).trans (hfin h₂).symm)⟩

theorem exitCTT_typeAscription (e : ImpExpr) (ty : String)
    (ih : ExitCTT M bi N leafSpec br A R e) :
    ExitCTT M bi N leafSpec br A R (.typeAscription e ty) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hLk h₁ h₂
  have hok' : exitSimOkT A R tl fl.isSome e = true := by
    cases tl <;> cases fl <;> simpa only [exitSimOkT] using hok
  rw [haxToLowCTKT_typeAscription_eq] at hK
  have hr : ∀ {env env' : Env} {o : Outcome},
      (denote' bi fuel (.typeAscription e ty)).run env = (o, env') →
      (denote' bi fuel e).run env = (o, env') := fun h => by
    rw [← h]; simp only [StateT.run, denote']
  exact ih tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok' hfl hK
    (hr hrun₁) hval₁ (hr hrun₂) hval₂ hag₁ hret₁ hag₂ hret₂ (by simpa only [srcLeak] using hLk)
    h₁ h₂

theorem exitCTT_seq (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (a b : ImpExpr)
    (iha : ExitCTT M bi N leafSpec br A R a) (ihb : ExitCTT M bi N leafSpec br A R b) :
    ExitCTT M bi N leafSpec br A R (.seq a b) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL' h₁ h₂
  have hok' : exitSimOkT A R false fl.isSome a = true ∧ exitSimOkT A R tl fl.isSome b = true := by
    cases tl <;> cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true] using hok
  rw [haxToLowCTKT_seq_eq] at hK
  rcases hA : haxToLowCTKT A false fl a with _ | ⟨aC, xa⟩
  · rw [hA] at hK; cases hK
  rcases hB : haxToLowCTKT A tl fl b with _ | ⟨bC, xb'⟩
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
  simp only [srcLeak, hra₁, hra₂] at hL'
  injection hL' with hLa hLb
  obtain ⟨bC', hbc, rfl⟩ : ∃ bC', (if xa then LowCT.RSeq aC (exitGuard bC) else .RSeq aC bC) =
      .RSeq aC bC' ∧ bC' = (if xa then exitGuard bC else bC) := ⟨_, by cases xa <;> rfl, rfl⟩
  rw [hbc] at h₁ h₂
  cases h₁ with
  | seq _ _ _ m₁ _ ta₁ tb₁ hA₁ hB₁ =>
  cases h₂ with
  | seq _ _ _ m₂ _ ta₂ tb₂ hA₂ hB₂ =>
  obtain ⟨hta, hxa⟩ := iha false fl fuel env₁ env₂ e1₁ e1₂ _ _ rs₁ rs₂ m₁ m₂ aC xa ta₁ ta₂
    hok'.1 hfl hA hra₁ ⟨_, rfl⟩ hra₂ ⟨_, rfl⟩ hag₁ hret₁ hag₂ hret₂ hLa hA₁ hA₂
  obtain ⟨hE₁, hx₁⟩ := exitSimT_final hL hok'.1 hfl hA hra₁ ⟨_, rfl⟩ hag₁ hret₁ hA₁
  obtain ⟨hE₂, hx₂⟩ := exitSimT_final hL hok'.1 hfl hA hra₂ ⟨_, rfl⟩ hag₂ hret₂ hA₂
  have hf₁ := envAgreesExitT_flag hE₁
  have hf₂ := envAgreesExitT_flag hE₂
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
    have hcf₁ := notCF_of_agreeT hE₁ hex₁
    have hcf₂ := notCF_of_agreeT hE₂ hex₂
    obtain ⟨h01, hagm₁, -⟩ := (envAgreesExitT_val hcf₁).mp hE₁
    obtain ⟨h02, hagm₂, -⟩ := (envAgreesExitT_val hcf₂).mp hE₂
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

theorem exitCTT_ifThenElse (v : String) (t e : ImpExpr)
    (iht : ExitCTT M bi N leafSpec br A R t) (ihe : ExitCTT M bi N leafSpec br A R e) :
    ExitCTT M bi N leafSpec br A R (.ifThenElse (.var v) t e) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ c xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
  have hok' : exitReserved v = false ∧ exitSc A v = true ∧ exitSimOkT A R tl fl.isSome t = true ∧
      exitSimOkT A R tl fl.isSome e = true := by
    cases tl <;> cases fl <;>
      simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using hok
  have hvs : A.lookup v = none := by simpa [exitSc] using hok'.2.1
  rw [haxToLowCTKT_ifThenElse_eq] at hK
  rcases hT' : haxToLowCTKT A tl fl t with _ | ⟨tC, xt⟩
  · rw [hT'] at hK; cases hK
  rcases hE : haxToLowCTKT A tl fl e with _ | ⟨eC, xe⟩
  · rw [hT', hE] at hK; cases hK
  rw [hT', hE] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  have hb : ∀ {env env' : Env} {o : Outcome} {rs : RustState},
      (denote' bi fuel (.ifThenElse (.var v) t e)).run env = (o, env') → (∃ w, o = .val w) →
      envAgreesT br A env rs →
      ∃ b, env v = some (.bool b) ∧ rs.rsScalar v = (if b then 1 else 0) := by
    intro env env' o rs hrun hval hag
    cases hvv : env v with
    | none =>
      rw [denote'_ifThenElse_var_run_none bi fuel v t e env hvv] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some w =>
      obtain ⟨hsw, hdw⟩ := envAgreesT_scalar hag hok'.1 hvs hvv
      rcases hsw.bool_or with ⟨bb, rfl⟩ | ⟨hnb, hcf⟩
      · rw [valueToScalar_bool, Option.some.injEq] at hdw
        exact ⟨bb, rfl, hdw.symm⟩
      · rw [denote'_ifThenElse_var_run_nonbool bi fuel v t e env w hvv hnb hcf] at hrun
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
      hok'.2.2.2 hfl hE hrun₁ hval₁ hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
    exact ⟨by rw [ht], hx⟩
  · simp only [if_true] at hrun₁ hrun₂ hr₁ hr₂
    cases h₁ with
    | ifFalse _ _ _ _ _ _ h0 _ => rw [hr₁] at h0; simp at h0
    | ifTrue _ _ _ _ _ _ tr₁ _ _ h₁ =>
    cases h₂ with
    | ifFalse _ _ _ _ _ _ h0 _ => rw [hr₂] at h0; simp at h0
    | ifTrue _ _ _ _ _ _ tr₂ _ _ h₂ =>
    obtain ⟨ht, hx⟩ := iht tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ tC xt tr₁ tr₂
      hok'.2.2.1 hfl hT' hrun₁ hval₁ hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL h₁ h₂
    exact ⟨by rw [ht], hx⟩

end Arms

/-! ## The loop arms -/

section LoopArms

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)

theorem forFoldReturn_var_not_unit (fuel : Nat) (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome) (hh : env h = some .unit)
    (hrun : (denote' bi fuel (.forFoldReturn i (.lit (.int lo)) (.var h) body)).run env =
      (o, env')) (hval : ∃ v, o = .val v) : False := by
  obtain ⟨u, rfl⟩ := hval
  simp only [denote'] at hrun
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, hh, Value.ofLit] at hrun
  cases (Prod.mk.inj hrun).1

theorem forFold_var_not_unit (fuel : Nat) (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome) (hh : env h = some .unit)
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.var h) body)).run env =
      (o, env')) (hval : ∃ v, o = .val v) : False := by
  obtain ⟨u, rfl⟩ := hval
  simp only [denote'] at hrun
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, hh, Value.ofLit] at hrun
  cases (Prod.mk.inj hrun).1

/-- A scalar word that is neither a bool nor the unit denotes its decoding as a bound. -/
theorem boundIntN_of_scalar {v : Value} {H : Nat} (hs : ScalarValN v)
    (hd : valueToScalar v = some H) (hnb : ∀ b, v ≠ .bool b) (hnu : v ≠ .unit) :
    boundInt v = some (H : Int) := by
  rcases hs.cases with ⟨w, k, rfl, _⟩ | ⟨b, rfl⟩ | ⟨k, rfl, h0, _⟩ | rfl
  · rw [valueToScalar_uint] at hd
    cases hd
    rfl
  · exact absurd rfl (hnb b)
  · simp only [valueToScalar, h0, if_true, Option.some.injEq] at hd
    subst hd
    simp [boundInt, Int.toNat_of_nonneg h0]
  · exact absurd rfl hnu

theorem exitCTT_whileFoldReturn (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (c : String)
    (body : ImpExpr)
    (ihb : ExitCTT M bi N leafSpec br A R body) :
    ExitCTT M bi N leafSpec br A R (.whileFoldReturn (.var c) body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hLk h₁ h₂
  obtain ⟨hE₁, -⟩ := exitSimT_final hL hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
  obtain ⟨hE₂, -⟩ := exitSimT_final hL hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : exitReserved c = false ∧ exitSc A c = true ∧
        exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have hcs : A.lookup c = none := by simpa [exitSc] using hok'.2.1
    rw [haxToLowCTKT_whileFoldReturn_eq] at hK
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK; cases hK
    rw [hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_whileFoldReturn_run] at hrun₁ hrun₂
    simp only [srcLeak] at hLk
    have hslot := runSlot_exitRunName hfl
    obtain ⟨ht, hr⟩ := genLoopWrapCT agResT
      (fun n env => (_root_.Hax.denoteWhile'Return bi n (.var c) body).run env)
      (exitRunName fl) c body bC (bodyRunT hL hok'.2.2 hslot hB)
      (bodyCTT ihb hok'.2.2 hslot hB) hslot hok'.1 (agGuardT hok'.1 hcs)
      (fun env v => by simp [denoteWhile'Return_zero_run])
      (fun n env rs v hag hnb => by
        cases hvc : env c with
        | none =>
          obtain ⟨msg, h⟩ := denoteWhile'Return_succ_none bi n c body env hvc
          simp [h]
        | some w =>
          obtain ⟨hsw, -⟩ := envAgreesT_scalar hag hok'.1 hcs hvc
          rcases hsw.bool_or with ⟨b, rfl⟩ | ⟨hnb', hcf⟩
          · exact absurd hvc (hnb b)
          · simp [denoteWhile'Return_succ_nonbool bi n c body env w hvc hnb' hcf])
      (fun n env o e2 hb hbr ho => denoteWhile'Return_succ_nonval bi n c body env e2 o hb hbr ho)
      (fun n env w e2 hb hbr hw => denoteWhile'Return_succ_iterate bi n c body env e2 w hb hbr hw)
      fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂ hLk
      h₁ h₂
    exact ⟨ht, exitOf_eq_of_flagT hE₁ hE₂ hr⟩

theorem exitCTT_whileFold (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (c : String)
    (body : ImpExpr)
    (ihb : ExitCTT M bi N leafSpec br A R body) :
    ExitCTT M bi N leafSpec br A R (.whileFold (.var c) body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hLk h₁ h₂
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOkT] at hok
    | some r =>
      have hok' : exitReserved c = false ∧ exitSc A c = true ∧
          exitSimOkT A R false true body = true := by
        simpa only [exitSimOkT, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have hcs : A.lookup c = none := by simpa [exitSc] using hok'.2.1
      have hK0 := hK
      rw [haxToLowCTKT_whileFold_some_eq] at hK
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK; cases hK
      rw [hB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      have hx₁ := exitOf_false_of_xT hL hok hfl hK0 hrun₁ hval₁ hag₁ hret₁ h₁
      have hx₂ := exitOf_false_of_xT hL hok hfl hK0 hrun₂ hval₂ hag₂ hret₂ h₂
      rw [denote'_whileFold_run] at hrun₁ hrun₂
      simp only [srcLeak] at hLk
      have hslot := runSlot_exitRunName hfl
      cases h₁ with
      | seq _ _ _ _ _ tl₁ tz₁ hl₁ hz₁ =>
      cases h₂ with
      | seq _ _ _ _ _ tl₂ tz₂ hl₂ hz₂ =>
      cases hz₁
      cases hz₂
      obtain ⟨ht, -⟩ := genLoopWrapCT agResT
        (fun n env => (_root_.Hax.denoteWhile' bi n (.var c) body).run env)
        (exitRunName (some r)) c body bC (bodyRunT hL hok'.2.2 hslot hB)
        (bodyCTT ihb hok'.2.2 hslot hB) hslot hok'.1 (agGuardT hok'.1 hcs)
        (fun env v => by simp [denoteWhile'_zero_run])
        (fun n env rs v hag hnb => by
          cases hvc : env c with
          | none =>
            obtain ⟨msg, h⟩ := denoteWhile'_succ_none bi n c body env hvc
            simp [h]
          | some w =>
            obtain ⟨hsw, -⟩ := envAgreesT_scalar hag hok'.1 hcs hvc
            rcases hsw.bool_or with ⟨b, rfl⟩ | ⟨hnb', hcf⟩
            · exact absurd hvc (hnb b)
            · simp [denoteWhile'_succ_nonbool bi n c body env w hvc hnb' hcf])
        (fun n env o e2 hb hbr ho => denoteWhile'_succ_nonval bi n c body env e2 o hb hbr ho)
        (fun n env w e2 hb hbr hw => denoteWhile'_succ_iterate bi n c body env e2 w hb hbr hw)
        fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ _ _ tl₁ tl₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂
        hLk hl₁ hl₂
      exact ⟨by rw [ht], hx₁.trans hx₂.symm⟩

theorem exitCTT_forFoldReturn (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (i : String)
    (lo hi body : ImpExpr)
    (ihb : ExitCTT M bi N leafSpec br A R body) :
    ExitCTT M bi N leafSpec br A R (.forFoldReturn i lo hi body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL' h₁ h₂
  obtain ⟨hE₁, -⟩ := exitSimT_final hL hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
  obtain ⟨hE₂, -⟩ := exitSimT_final hL hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
  suffices H : t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName from
    ⟨H.1, exitOf_eq_of_flagT hE₁ hE₂ H.2⟩
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) = true ∧
        exitReserved i = false ∧ exitSc A i = true ∧ exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
    have hslot := runSlot_exitRunName hfl
    rw [haxToLowCTKT_forFoldReturn_eq] at hK
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
        rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
    rw [hB] at hK
    have hR := bodyRunT (M := M) (N := N) hL hok'.2.2.2 hslot hB
    have hC := bodyCTT ihb hok'.2.2.2 hslot hB
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
      · rw [hFB, hRt] at hK; cases hK
      rw [hFB, hRt] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      have hh : exitReserved h = false ∧ exitSc A h = true := by
        have h1 := hok'.1
        simpa only [hFB, forBoundsRtOkT, hRt, Option.isSome_none, Bool.false_or,
          Bool.and_eq_true, Bool.not_eq_true'] using h1
      have hhs : A.lookup h = none := by simpa [exitSc] using hh.2
      obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
      obtain ⟨v₁, H₁, hv₁, hd₁, hH₁, hrun₁'⟩ := denote'_forFoldReturn_var_scalarN bi fuel i h l
        body env₁ env₁' o₁ hrun₁ hval₁ (fun v hv => (envAgreesT_scalar hag₁ hh.1 hhs hv).1)
      obtain ⟨v₂, H₂, hv₂, hd₂, hH₂, hrun₂'⟩ := denote'_forFoldReturn_var_scalarN bi fuel i h l
        body env₂ env₂' o₂ hrun₂ hval₂ (fun v hv => (envAgreesT_scalar hag₂ hh.1 hhs hv).1)
      have hbI₁ := boundIntN_of_scalar (envAgreesT_scalar hag₁ hh.1 hhs hv₁).1 hd₁
        (fun b hb => forFoldReturn_var_not_bool bi fuel i h l body env₁ env₁' o₁ b (hb ▸ hv₁)
          hrun₁ hval₁)
        (fun hb => forFoldReturn_var_not_unit bi fuel i h l body env₁ env₁' o₁ (hb ▸ hv₁)
          hrun₁ hval₁)
      have hbI₂ := boundIntN_of_scalar (envAgreesT_scalar hag₂ hh.1 hhs hv₂).1 hd₂
        (fun b hb => forFoldReturn_var_not_bool bi fuel i h l body env₂ env₂' o₂ b (hb ▸ hv₂)
          hrun₂ hval₂)
        (fun hb => forFoldReturn_var_not_unit bi fuel i h l body env₂ env₂' o₂ (hb ▸ hv₂)
          hrun₂ hval₂)
      simp only [srcLeak] at hL'
      rw [boundsLeak_var bi fuel l h _ env₁ v₁ H₁ hv₁ hbI₁,
        boundsLeak_var bi fuel l h _ env₂ v₂ H₂ hv₂ hbI₂] at hL'
      simp only [SrcLeak.cat.injEq, SrcLeak.ev.injEq, SrcEv.bound.injEq, true_and,
        Nat.cast_inj] at hL'
      obtain ⟨rfl, hL'⟩ := hL'
      have hdec₁ : rs₁.rsScalar h = H₁ := by
        have := (envAgreesT_scalar hag₁ hh.1 hhs hv₁).2
        rw [hd₁] at this; exact (Option.some.inj this).symm
      have hdec₂ : rs₂.rsScalar h = H₁ := by
        have := (envAgreesT_scalar hag₂ hh.1 hhs hv₂).2
        rw [hd₂] at this; exact (Option.some.inj this).symm
      exact genForLoopRtCT agResT
        (fun n k env => (_root_.Hax.denoteForLoop'Return bi n i k H₁ body).run env)
        (exitRunName fl) i l h H₁ body bC hR hC hslot hok'.2.1 hh.1 hH₁ (agExtT hok'.2.1 his)
        (fun k env v hk => by rw [denoteForLoop'Return_zero_run bi i k _ body env hk]; simp)
        (fun n k env o e2 hk hbr ho =>
          denoteForLoop'Return_succ_nonval bi n i k _ body env e2 o hk hbr ho)
        (fun n k env w e2 hk hbr hw =>
          denoteForLoop'Return_succ_iterate bi n i k _ body env e2 w hk hbr hw)
        fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁' hval₁ hrun₂' hval₂ hag₁ hag₂
        hdec₁ hdec₂ hL' h₁ h₂
    rw [hFB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rw [denote'_forFoldReturn_lit_run] at hrun₁ hrun₂
    simp only [srcLeak] at hL'
    rw [boundsLeak_lit, boundsLeak_lit] at hL'
    simp only [SrcLeak.cat.injEq, true_and] at hL'
    exact genForLoopCT agResT
      (fun n k env => (_root_.Hax.denoteForLoop'Return bi n i k h body).run env)
      (exitRunName fl) i l h body bC hR hC hslot hok'.2.1 hh (agExtT hok'.2.1 his)
      (fun k env v hk => by rw [denoteForLoop'Return_zero_run bi i k _ body env hk]; simp)
      (fun n k env o e2 hk hbr ho =>
        denoteForLoop'Return_succ_nonval bi n i k _ body env e2 o hk hbr ho)
      (fun n k env w e2 hk hbr hw =>
        denoteForLoop'Return_succ_iterate bi n i k _ body env e2 w hk hbr hw)
      fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂
      hL' h₁ h₂

theorem exitCTT_forFoldRevReturn (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (i : String)
    (lo hi body : ImpExpr) (ihb : ExitCTT M bi N leafSpec br A R body) :
    ExitCTT M bi N leafSpec br A R (.forFoldRevReturn i lo hi body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL' h₁ h₂
  obtain ⟨hE₁, -⟩ := exitSimT_final hL hok hfl hK hrun₁ hval₁ hag₁ hret₁ h₁
  obtain ⟨hE₂, -⟩ := exitSimT_final hL hok hfl hK hrun₂ hval₂ hag₂ hret₂ h₂
  suffices H : t₁ = t₂ ∧ r₁.rsScalar exitRetName = r₂.rsScalar exitRetName from
    ⟨H.1, exitOf_eq_of_flagT hE₁ hE₂ H.2⟩
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
        exitSc A i = true ∧ exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
    rw [haxToLowCTKT_forFoldRevReturn_eq] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rw [hFB] at hok'; cases hok'.1
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hFB, hB] at hK; cases hK
    rw [hFB, hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_forFoldRevReturn_lit_run] at hrun₁ hrun₂
    simp only [srcLeak] at hL'
    rw [boundsLeak_lit, boundsLeak_lit] at hL'
    simp only [SrcLeak.cat.injEq, true_and] at hL'
    have hslot := runSlot_exitRunName hfl
    cases h₁ with
    | letU64Zero _ _ _ _ _ h₁ =>
    cases h₁ with
    | letU64Zero _ _ _ _ _ h₁ =>
    cases h₂ with
    | letU64Zero _ _ _ _ _ h₂ =>
    cases h₂ with
    | letU64Zero _ _ _ _ _ h₂ =>
    obtain ⟨hag₁', hret₁'⟩ := genForEntry agResT hag₁
    obtain ⟨hag₂', hret₂'⟩ := genForEntry agResT hag₂
    exact genForRevCT agResT (exitRunName fl) i l h body bC
      (bodyRunT (M := M) (N := N) hL hok'.2.2.2 hslot hB) (bodyCTT ihb hok'.2.2.2 hslot hB)
      hslot hok'.2.1 hh (agExtT hok'.2.1 his) fuel env₁ env₂ env₁' env₂' o₁ o₂ _ _ r₁ r₂ t₁ t₂
      hrun₁ hval₁ hrun₂ hval₂ hag₁' hret₁' hag₂' hret₂' hL' h₁ h₂

theorem exitCTT_forFold (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (i : String)
    (lo hi body : ImpExpr)
    (ihb : ExitCTT M bi N leafSpec br A R body) :
    ExitCTT M bi N leafSpec br A R (.forFold i lo hi body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL' h₁ h₂
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOkT] at hok
    | some r =>
      have hok' : ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) = true ∧
          exitReserved i = false ∧ exitSc A i = true ∧
          exitSimOkT A R false true body = true := by
        simpa only [exitSimOkT, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
      have hK0 := hK
      have hslot := runSlot_exitRunName hfl
      have hxo : xb = false → exitOf o₁ = exitOf o₂ := fun hxb => by
        subst hxb
        exact (exitOf_false_of_xT hL hok hfl hK0 hrun₁ hval₁ hag₁ hret₁ h₁).trans
          (exitOf_false_of_xT hL hok hfl hK0 hrun₂ hval₂ hag₂ hret₂ h₂).symm
      rw [haxToLowCTKT_forFold_some_eq] at hK
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK
        rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
          rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
      rw [hB] at hK
      have hR := bodyRunT (M := M) (N := N) hL hok'.2.2.2 hslot hB
      have hC := bodyCTT ihb hok'.2.2.2 hslot hB
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
      · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
        · rw [hFB, hRt] at hK; cases hK
        rw [hFB, hRt] at hK
        simp only [Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        refine ⟨?_, hxo rfl⟩
        have hh : exitReserved h = false ∧ exitSc A h = true := by
          have h1 := hok'.1
          simpa only [hFB, forBoundsRtOkT, hRt, Option.isSome_none, Bool.false_or,
            Bool.and_eq_true, Bool.not_eq_true'] using h1
        have hhs : A.lookup h = none := by simpa [exitSc] using hh.2
        obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
        obtain ⟨v₁, H₁, hv₁, hd₁, hH₁, hrun₁'⟩ := denote'_forFold_var_scalarN bi fuel i h l
          body env₁ env₁' o₁ hrun₁ hval₁ (fun v hv => (envAgreesT_scalar hag₁ hh.1 hhs hv).1)
        obtain ⟨v₂, H₂, hv₂, hd₂, hH₂, hrun₂'⟩ := denote'_forFold_var_scalarN bi fuel i h l
          body env₂ env₂' o₂ hrun₂ hval₂ (fun v hv => (envAgreesT_scalar hag₂ hh.1 hhs hv).1)
        have hbI₁ := boundIntN_of_scalar (envAgreesT_scalar hag₁ hh.1 hhs hv₁).1 hd₁
          (fun b hb => forFold_var_not_bool bi fuel i h l body env₁ env₁' o₁ b (hb ▸ hv₁)
            hrun₁ hval₁)
          (fun hb => forFold_var_not_unit bi fuel i h l body env₁ env₁' o₁ (hb ▸ hv₁)
            hrun₁ hval₁)
        have hbI₂ := boundIntN_of_scalar (envAgreesT_scalar hag₂ hh.1 hhs hv₂).1 hd₂
          (fun b hb => forFold_var_not_bool bi fuel i h l body env₂ env₂' o₂ b (hb ▸ hv₂)
            hrun₂ hval₂)
          (fun hb => forFold_var_not_unit bi fuel i h l body env₂ env₂' o₂ (hb ▸ hv₂)
            hrun₂ hval₂)
        simp only [srcLeak] at hL'
        rw [boundsLeak_var bi fuel l h _ env₁ v₁ H₁ hv₁ hbI₁,
          boundsLeak_var bi fuel l h _ env₂ v₂ H₂ hv₂ hbI₂] at hL'
        simp only [SrcLeak.cat.injEq, SrcLeak.ev.injEq, SrcEv.bound.injEq, true_and,
          Nat.cast_inj] at hL'
        obtain ⟨rfl, hL'⟩ := hL'
        have hdec₁ : rs₁.rsScalar h = H₁ := by
          have := (envAgreesT_scalar hag₁ hh.1 hhs hv₁).2
          rw [hd₁] at this; exact (Option.some.inj this).symm
        have hdec₂ : rs₂.rsScalar h = H₁ := by
          have := (envAgreesT_scalar hag₂ hh.1 hhs hv₂).2
          rw [hd₂] at this; exact (Option.some.inj this).symm
        cases h₁ with
        | seq _ _ _ _ _ tl₁ tz₁ hl₁ hz₁ =>
        cases h₂ with
        | seq _ _ _ _ _ tl₂ tz₂ hl₂ hz₂ =>
        cases hz₁
        cases hz₂
        obtain ⟨ht, -⟩ := genForLoopRtCT agResT
          (fun n k env => (_root_.Hax.denoteForLoop' bi n i k H₁ body).run env)
          (exitRunName (some r)) i l h H₁ body bC hR hC hslot hok'.2.1 hh.1 hH₁
          (agExtT hok'.2.1 his)
          (fun k env v hk => by rw [denoteForLoop'_zero_run bi i k _ body env hk]; simp)
          (fun n k env o e2 hk hbr ho =>
            denoteForLoop'_succ_nonval bi n i k _ body env e2 o hk hbr ho)
          (fun n k env w e2 hk hbr hw =>
            denoteForLoop'_succ_iterate bi n i k _ body env e2 w hk hbr hw)
          fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ _ _ tl₁ tl₂ hrun₁' hval₁ hrun₂' hval₂ hag₁
          hag₂ hdec₁ hdec₂ hL' hl₁ hl₂
        rw [ht]
      rw [hFB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      refine ⟨?_, hxo rfl⟩
      obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
      rw [denote'_forFold_lit_run] at hrun₁ hrun₂
      simp only [srcLeak] at hL'
      rw [boundsLeak_lit, boundsLeak_lit] at hL'
      simp only [SrcLeak.cat.injEq, true_and] at hL'
      cases h₁ with
      | seq _ _ _ _ _ tl₁ tz₁ hl₁ hz₁ =>
      cases h₂ with
      | seq _ _ _ _ _ tl₂ tz₂ hl₂ hz₂ =>
      cases hz₁
      cases hz₂
      obtain ⟨ht, -⟩ := genForLoopCT agResT
        (fun n k env => (_root_.Hax.denoteForLoop' bi n i k h body).run env)
        (exitRunName (some r)) i l h body bC hR hC hslot hok'.2.1 hh (agExtT hok'.2.1 his)
        (fun k env v hk => by rw [denoteForLoop'_zero_run bi i k _ body env hk]; simp)
        (fun n k env o e2 hk hbr ho =>
          denoteForLoop'_succ_nonval bi n i k _ body env e2 o hk hbr ho)
        (fun n k env w e2 hk hbr hw =>
          denoteForLoop'_succ_iterate bi n i k _ body env e2 w hk hbr hw)
        fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ _ _ tl₁ tl₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂
        hL' hl₁ hl₂
      rw [ht]

/-- A downward counted loop that may break: its source event is `opaque`, so equal source
    leakage gives equal environments, and the trips are those of `genTripsCT` over
    `denoteForLoopRev'` counting down from `hi - 1`. -/
theorem exitCTT_forFoldRev (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (i : String)
    (lo hi body : ImpExpr)
    (ihb : ExitCTT M bi N leafSpec br A R body) :
    ExitCTT M bi N leafSpec br A R (.forFoldRev i lo hi body) := by
  intro tl fl fuel env₁ env₂ env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ cc xb t₁ t₂ hok hfl hK hrun₁ hval₁
    hrun₂ hval₂ hag₁ hret₁ hag₂ hret₂ hL' h₁ h₂
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOkT] at hok
    | some r =>
      have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
          exitSc A i = true ∧ exitSimOkT A R false true body = true := by
        simpa only [exitSimOkT, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
      have hK0 := hK
      have hslot := runSlot_exitRunName hfl
      have hxo : xb = false → exitOf o₁ = exitOf o₂ := fun hxb => by
        subst hxb
        exact (exitOf_false_of_xT hL hok hfl hK0 hrun₁ hval₁ hag₁ hret₁ h₁).trans
          (exitOf_false_of_xT hL hok hfl hK0 hrun₂ hval₂ hag₂ hret₂ h₂).symm
      rw [haxToLowCTKT_forFoldRev_some_eq] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
      · rw [hFB] at hok'; cases hok'.1
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hFB, hB] at hK; cases hK
      rw [hFB, hB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      refine ⟨?_, hxo rfl⟩
      obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
      have hR := bodyRunT (M := M) (N := N) hL hok'.2.2.2 hslot hB
      have hC := bodyCTT ihb hok'.2.2.2 hslot hB
      have henv : env₁ = env₂ := by
        simp only [srcLeak, SrcLeak.ev.injEq, SrcEv.opaque.injEq] at hL'
        first | exact hL'.1 | exact hL'
      subst henv
      rw [denote'_forFoldRev_lit_run] at hrun₁ hrun₂
      have hcast : ∀ j : Nat, j < h - l →
          ((h - j : Nat) : Int) - 1 = ((h - 1 - j : Nat) : Int) := by
        intro j hj; omega
      have hcast' : ∀ j : Nat, j < h - l →
          ((h - (j + 1) : Nat) : Int) = ((h - j : Nat) : Int) - 1 := by
        intro j hj; omega
      cases h₁ with
      | seq _ _ _ _ _ tl₁ tz₁ hl₁ hz₁ =>
      cases h₂ with
      | seq _ _ _ _ _ tl₂ tz₂ hl₂ hz₂ =>
      cases hz₁
      cases hz₂
      cases hl₁ with
      | letU64Zero _ _ _ _ _ hl₁ =>
      cases hl₁ with
      | letU64Zero _ _ _ _ _ hl₁ =>
      cases hl₂ with
      | letU64Zero _ _ _ _ _ hl₂ =>
      cases hl₂ with
      | letU64Zero _ _ _ _ _ hl₂ =>
      obtain ⟨hag₁', hret₁'⟩ := genForEntry agResT hag₁
      obtain ⟨hag₂', hret₂'⟩ := genForEntry agResT hag₂
      obtain ⟨ht, -⟩ := genTripsCT agResT (exitRunName (some r)) i body bC
        (.SSub (.SLit (h - 1)) (.SVar (exitRunName (some r))))
        (fun j => h - 1 - j) (h - l)
        (fun n j env =>
          (_root_.Hax.denoteForLoopRev' bi n i l ((h - j : Nat) : Int) body).run env)
        (fun n j env => forRevLeak bi i body (srcLeak M bi body) n l ((h - j : Nat) : Int) env)
        hR hC hslot hok'.2.1
        (fun env rs j hj hag => agExtT hok'.2.1 his env rs _ (by omega) hag) ⟨trivial, rfl⟩
        (fun j s hs => by simp [SExpr.evalState, hs])
        (fun j env v hj => by
          rw [denoteForLoopRev'_zero_run bi i _ _ body env (by omega)]; simp)
        (fun n j env o e2 hj hbr ho => by
          refine denoteForLoopRev'_succ_nonval bi n i _ _ body env e2 o (by omega) ?_ ho
          rw [hcast j hj]; exact hbr)
        (fun n j env w e2 hj hbr hw => by
          rw [denoteForLoopRev'_succ_iterate bi n i _ _ body env e2 w (by omega)
            (by rw [hcast j hj]; exact hbr) hw, hcast' j hj])
        (fun n j env hj => by
          rw [forRevLeak, if_neg (by omega), hcast j hj, hcast' j hj, hcast j hj])
        (h - l) 0 fuel env₁ env₁ env₁' env₂' o₁ o₂ _ _ _ _ _ _ (by omega)
        (by simpa using hrun₁) hval₁ (by simpa using hrun₂) hval₂ hag₁' hret₁' hag₂' hret₂'
        rfl (rFor_tripsL M N leafSpec _ _ _ _ _ _ hl₁) (rFor_tripsL M N leafSpec _ _ _ _ _ _ hl₂)
      rw [ht]

end LoopArms

/-! ## Every expression of the fragment, and the function frame -/

section Assembly

variable (M : LowCTLeakModel) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (br : ValueTowerBridge)

/-- An expression outside the fragment satisfies `ExitCTT` vacuously. -/
theorem exitCTT_of_not_ok (A : ExitTowers) (R : ExitRes) (e : ImpExpr)
    (h : ∀ tl il, exitSimOkT A R tl il e = false) : ExitCTT M bi N leafSpec br A R e := by
  intro tl fl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hok
  rw [h] at hok; cases hok

/-- **The typed exit-flag lowering preserves constant time.** For leaf conditions
    `ExitLeaves` and a leakage model classing no leaf variable time (`M.leafVT f = false`
    for every `f`, as for `LowCTLeakModel.owned`), every expression satisfies `ExitCTT`.
    The condition on `M` is used at the calls: the bridge `br` is a relation, so the tower
    arguments of a call are not determined by the environment. -/
theorem haxToLowCTKT_ct (hvt : ∀ f, M.leafVT f = false) (A : ExitTowers)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (R : ExitRes) (e : ImpExpr) :
    ExitCTT M bi N leafSpec br A R e := by
  have nok : ∀ e : ImpExpr, (∀ tl il, exitSimOkT A R tl il e = false) →
      ExitCTT M bi N leafSpec br A R e :=
    exitCTT_of_not_ok M bi N leafSpec br A R
  induction e using ImpExpr.ind with
  | lit l => exact exitCTT_lit M bi N leafSpec br A R hL l
  | var x => exact exitCTT_var M bi N leafSpec br A R hL x
  | unitVal => exact exitCTT_unitVal M bi N leafSpec br A R hL
  | letBind n val body _ ihb => exact exitCTT_letBind M bi N leafSpec br A R hvt hL n val body ihb
  | seq a b iha ihb => exact exitCTT_seq M bi N leafSpec br A R hL a b iha ihb
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v => exact exitCTT_ifThenElse M bi N leafSpec br A R v t e iht ihe
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | typeAscription e ty ih => exact exitCTT_typeAscription M bi N leafSpec br A R e ty ih
  | whileFoldReturn c body _ ihb =>
    cases c with
    | var v => exact exitCTT_whileFoldReturn M bi N leafSpec br A R hL v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | forFoldReturn i lo hi body _ _ ihb =>
    exact exitCTT_forFoldReturn M bi N leafSpec br A R hL i lo hi body ihb
  | forFoldRevReturn i lo hi body _ _ ihb =>
    exact exitCTT_forFoldRevReturn M bi N leafSpec br A R hL i lo hi body ihb
  | forFold i lo hi body _ _ ihb => exact exitCTT_forFold M bi N leafSpec br A R hL i lo hi body ihb
  | forFoldRev i lo hi body _ _ ihb =>
    exact exitCTT_forFoldRev M bi N leafSpec br A R hL i lo hi body ihb
  | whileFold c body _ ihb =>
    cases c with
    | var v => exact exitCTT_whileFold M bi N leafSpec br A R hL v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | cfBreak p _ => exact exitCTT_cfBreak M bi N leafSpec br A R hL p
  | tuple es _ => exact exitCTT_tuple M bi N leafSpec br A R hL es
  | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)

/-- **The typed lowered function preserves the leakage.** For a function body of the
    fragment `exitSimOkT A R` with exits at function level, two runs ending in a value
    from environments with equal source leakage, and two runs of `haxToLowCTFnT A e` from
    states agreeing with them under `A`, have equal traces. -/
theorem haxToLowCTFnT_leak_eq (hvt : ∀ f, M.leafVT f = false) (A : ExitTowers)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (R : ExitRes) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOkT A R true true e = true) (hK : haxToLowCTFnT A e = some c)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak)
    (hrun₁ : (denote' bi fuel e).run env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : (denote' bi fuel e).run env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : envAgreesT br A env₁ rs₁) (hag₂ : envAgreesT br A env₂ rs₂)
    (hL' : srcLeak M bi e fuel env₁ = srcLeak M bi e fuel env₂)
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂) :
    t₁ = t₂ := by
  unfold haxToLowCTFnT at hK
  rcases hK0 : haxToLowCTKT A true (some exitFnSlot) e with _ | ⟨c0, x⟩
  · rw [hK0] at hK; cases hK
  rw [hK0] at hK
  simp only [Option.map_some, Option.some.injEq] at hK
  subst hK
  have hctx : RunCtx (some exitFnSlot) := fun r h => Or.inr (Option.some.inj h).symm
  have hentry : ∀ {env : Env} {rs : RustState}, envAgreesT br A env rs →
      envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0) ∧
        (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0).rsScalar exitRetName = 0 :=
    fun hag => ⟨envAgreesT_set_reserved _ exitReserved_res
      (envAgreesT_set_reserved _ exitReserved_ret hag), by simp [rsScalar_rsSetScalar]⟩
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
  obtain ⟨ht, hx⟩ := haxToLowCTKT_ct M bi N leafSpec br hvt A hL R e true (some exitFnSlot) fuel
    env₁ env₂ env₁' env₂' o₁ o₂ _ _ m₁ m₂ c0 x t0₁ t0₂ hok hctx hK0 hrun₁ hval₁ hrun₂ hval₂
    hag₁' hret₁' hag₂' hret₂' hL' hc₁ hc₂
  obtain ⟨hE₁, -⟩ := exitSimT_final hL hok hctx hK0 hrun₁ hval₁ hag₁' hret₁' hc₁
  obtain ⟨hE₂, -⟩ := exitSimT_final hL hok hctx hK0 hrun₂ hval₂ hag₂' hret₂' hc₂
  have hf : m₁.rsScalar exitRetName = m₂.rsScalar exitRetName := by
    rw [envAgreesExitT_flag hE₁, envAgreesExitT_flag hE₂, hx]
  have htail : ∀ {m r : RustState} {tf : List CTLeak}, RustExecLeak N leafSpec M
      (.RIfNz exitRetName (.RScalarSetExpr exitResName (.SVar exitValName)) .RSkip) m tf r →
      tf = [.branch (m.rsScalar exitRetName != 0)] := by
    intro m r tf h
    cases h with
    | ifTrue _ _ _ _ _ _ _ hv hv0 hs => cases hs; subst hv; simp [hv0, sexprLeak]
    | ifFalse _ _ _ _ _ _ h0 hs => cases hs; simp [h0]
  rw [ht, htail hf₁, htail hf₂, hf]

/-- **Source constant time implies constant time of the typed lowered function**, for
    runs whose source counterparts end in a value: two runs of `haxToLowCTFnT A e` from
    states agreeing under `A` with environments that agree on the public variables of
    `lt` and from which the body runs to a value have equal traces. -/
theorem haxToLowCTFnT_ct (hvt : ∀ f, M.leafVT f = false) (A : ExitTowers)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A)) (R : ExitRes) (lt : LevelTable) (e : ImpExpr)
    (c : LowCT)
    (hok : exitSimOkT A R true true e = true) (hK : haxToLowCTFnT A e = some c)
    (hsrc : SourceCT M bi lt e)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak) (hpub : PubEqEnv lt env₁ env₂)
    (hrun₁ : (denote' bi fuel e).run env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : (denote' bi fuel e).run env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : envAgreesT br A env₁ rs₁) (hag₂ : envAgreesT br A env₂ rs₂)
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂) :
    t₁ = t₂ :=
  haxToLowCTFnT_leak_eq M bi N leafSpec br hvt A hL R e c hok hK fuel env₁ env₂ env₁' env₂' o₁ o₂
    rs₁ rs₂ r₁ r₂ t₁ t₂ hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂
    (hsrc fuel env₁ env₂ env₁' env₂' o₁ o₂ hpub hrun₁ hval₁ hrun₂ hval₂) h₁ h₂

/-- `haxToLowCTFnT_ct` for the function lowering `haxToLowCTFnI` under the inferred
    placement `exitTowers e` and result placement `exitResultPlace (exitTowers e) e`. -/
theorem haxToLowCTFnI_ct (hvt : ∀ f, M.leafVT f = false) (hL : ExitLeaves bi leafSpec br)
    (lt : LevelTable) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOkT (exitTowers e) (exitResultPlace (exitTowers e) e) true true e = true)
    (hK : haxToLowCTFnI e = some c) (hsrc : SourceCT M bi lt e)
    (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome) (rs₁ rs₂ r₁ r₂ : RustState)
    (t₁ t₂ : List CTLeak) (hpub : PubEqEnv lt env₁ env₂)
    (hrun₁ : (denote' bi fuel e).run env₁ = (o₁, env₁')) (hval₁ : ∃ v, o₁ = .val v)
    (hrun₂ : (denote' bi fuel e).run env₂ = (o₂, env₂')) (hval₂ : ∃ v, o₂ = .val v)
    (hag₁ : envAgreesT br (exitTowers e) env₁ rs₁) (hag₂ : envAgreesT br (exitTowers e) env₂ rs₂)
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂) :
    t₁ = t₂ :=
  haxToLowCTFnT_ct M bi N leafSpec br hvt (exitTowers e) (hL.atExitTowers e) _ lt e c hok hK
    hsrc fuel env₁ env₂
    env₁' env₂' o₁ o₂ rs₁ rs₂ r₁ r₂ t₁ t₂ hpub hrun₁ hval₁ hrun₂ hval₂ hag₁ hag₂ h₁ h₂

end Assembly

end CatCrypt.Crypto.Hax
