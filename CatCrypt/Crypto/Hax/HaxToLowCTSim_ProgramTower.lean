/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Program

/-!
# Program-level simulation with scalar-valued call results

`haxToLowCT` lowers every call to an `RCall` that writes the tower heap, while
the scalar agreement `envAgreesRust` asks every environment binding that decodes
to a scalar to be held in the scalar heap.  `haxToLowCT_simulates_program`
therefore requires `FullSimPreconds.leafScalar`: no builtin returns a value that
decodes to a scalar.  Hax arithmetic and bitwise builtins return `int`, `uint`
and `bool` values, so no builtin table that implements them satisfies it.

This module restates the program-level simulation for such tables:

* `envAgreesRustT bridge env rs` asks scalar agreement only at names without a
  tower binding, and tower agreement (through `bridge`) at names with one.  It
  follows from `envAgreesRustFull` (`envAgreesRustT_of_full`).
* `LeafCallAgreesArgs bi leafSpec f dt bridge` is the leaf condition with the
  arguments in its premise: when every argument value is related by `bridge` to
  the tower slot the call reads, the builtin's result is related to the leaf
  output.  A builtin table that does not implement `f` satisfies it
  (`leafCallAgreesArgs_of_unmatched`).
* `condsScalar S e` asks that the condition of every `ifThenElse` and
  `whileLoop` be a scalar-binding name, which is where `RIfNz` and `RWhileNz`
  read it.
* `ProgSimT` is the simulation predicate; `haxToLowCT_simulates_programT` proves
  it for every program, from the leaf conditions, the tuple-load agreement, and
  the absence of `array_update` and `index` from the builtin table.

## Main results

* `haxToLowCT_simulates_programT`
* `envAgreesRustT_extend_tower`, `envAgreesRustT_extend_scalar_fresh`
* `argsAgree_of_envAgrees` — the argument premise of `LeafCallAgreesArgs` holds
  at every translated call.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Builtins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  Agreement -/

/-- Scalar agreement at the names without a tower binding. -/
def envAgreesScalarOff (env : Env) (rs : RustState) : Prop :=
  ∀ name v n, env name = some v → rs.rsTower name = none →
    valueToScalar v = some n → rs.rsScalar name = n

/-- Agreement of an environment with a state: scalar agreement at names without
    a tower binding, and `bridge` agreement at names with one. -/
def envAgreesRustT (bridge : ValueTowerBridge) (env : Env) (rs : RustState) : Prop :=
  envAgreesScalarOff env rs ∧ envAgreesRustTower bridge env rs

theorem envAgreesRustT_of_full (bridge : ValueTowerBridge) (env : Env) (rs : RustState)
    (h : envAgreesRustFull bridge env rs) : envAgreesRustT bridge env rs :=
  ⟨fun name v n hv _ hn => h.1 name v hv n hn, h.2⟩

/-- Binding a name in the environment and at the tower preserves agreement when
    the bound values are related by `bridge`. -/
theorem envAgreesRustT_extend_tower (bridge : ValueTowerBridge) (env : Env) (rs : RustState)
    (name : String) (v : Value) (dt : TowerType) (val : RustVal dt)
    (hAgree : envAgreesRustT bridge env rs) (hBridge : bridge dt v val) :
    envAgreesRustT bridge (env.extend name v) (rsSetTower rs name ⟨dt, val⟩) := by
  refine ⟨?_, envAgreesRustTower_extend_tower bridge env rs name v dt val hAgree.2 hBridge⟩
  intro m w n hw hT hn
  by_cases hm : m = name
  · subst hm
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same] at hT
    cases hT
  · have hEnv : env.extend name v m = env m := by simp [Hax.Env.extend, hm]
    rw [hEnv] at hw
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs name m _ (Ne.symm hm)] at hT
    exact hAgree.1 m w n hw hT hn

/-- Binding a name without a tower binding in the environment and in the scalar
    heap preserves agreement when the scalar is the value's decoding. -/
theorem envAgreesRustT_extend_scalar_fresh (bridge : ValueTowerBridge) (env : Env)
    (rs : RustState) (name : String) (v : Value) (n : Nat)
    (hFresh : TowerFresh rs name) (hDecode : valueToScalar v = some n)
    (hAgree : envAgreesRustT bridge env rs) :
    envAgreesRustT bridge (env.extend name v) (rsSetScalar rs name n) := by
  refine ⟨?_, envAgreesRustTower_extend_scalar_fresh bridge env rs name v n hFresh hAgree.2⟩
  intro m w k hw hT hk
  by_cases hm : m = name
  · subst hm
    simp only [Hax.Env.extend, beq_self_eq_true, if_true, Option.some.injEq] at hw
    subst hw
    rw [hDecode, Option.some.injEq] at hk
    subst hk
    simp [rsSetScalar]
  · have hEnv : env.extend name v m = env m := by simp [Hax.Env.extend, hm]
    rw [hEnv] at hw
    have hS : (rsSetScalar rs name n).rsScalar m = rs.rsScalar m := by
      simp [rsSetScalar, hm]
    rw [hS]
    exact hAgree.1 m w k hw hT hk

/-- The copy of `src` into `name`, both without a tower binding, preserves
    agreement. -/
theorem envAgreesRustT_extend_copy (bridge : ValueTowerBridge) (env : Env) (rs : RustState)
    (name src : String) (w : Value) (hFresh : TowerFresh rs name)
    (hSrcFresh : TowerFresh rs src) (hsrc : env src = some w)
    (hAgree : envAgreesRustT bridge env rs) :
    envAgreesRustT bridge (env.extend name w) (rsSetScalar rs name (rs.rsScalar src)) := by
  refine ⟨?_, envAgreesRustTower_extend_scalar_fresh bridge env rs name w _ hFresh hAgree.2⟩
  intro m w' k hw hT hk
  by_cases hm : m = name
  · subst hm
    simp only [Hax.Env.extend, beq_self_eq_true, if_true, Option.some.injEq] at hw
    subst hw
    simpa [rsSetScalar] using hAgree.1 src w k hsrc hSrcFresh hk
  · have hEnv : env.extend name w m = env m := by simp [Hax.Env.extend, hm]
    rw [hEnv] at hw
    have hS : (rsSetScalar rs name (rs.rsScalar src)).rsScalar m = rs.rsScalar m := by
      simp [rsSetScalar, hm]
    rw [hS]
    exact hAgree.1 m w' k hw hT hk

/-- A boolean condition without a tower binding is held in the scalar heap as
    `0` or `1`. -/
theorem envAgreesRustT_bool_to_scalar (bridge : ValueTowerBridge) (env : Env) (rs : RustState)
    (cond : String) (b : Bool) (hAgree : envAgreesRustT bridge env rs)
    (hT : rs.rsTower cond = none) (hEnv : env cond = some (.bool b)) :
    rs.rsScalar cond = if b then 1 else 0 := by
  cases b with
  | true => exact hAgree.1 cond _ 1 hEnv hT rfl
  | false => exact hAgree.1 cond _ 0 hEnv hT rfl

/-! ## §2  The leaf condition with argument agreement -/

/-- The leaf `f` at destination type `dt` agrees with the builtin table: when the
    argument values are related by `bridge` to the tower slots read by the call,
    in order, the builtin's result is related to the leaf output. -/
def LeafCallAgreesArgs (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (bridge : ValueTowerBridge) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => bridge p.1 v p.2) vals argList →
    bridge dt vRes (leafSpec.call f dt (args.map (·.locDst)) oldV argList)

/-- A builtin table that does not implement `f` satisfies the leaf condition. -/
theorem leafCallAgreesArgs_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (f : String)
    (dt : TowerType) (bridge : ValueTowerBridge) (h : ∀ vals, bi f vals = none) :
    LeafCallAgreesArgs bi leafSpec f dt bridge := by
  intro _ vals _ _ _ hBi
  rw [h vals] at hBi
  cases hBi

/-! ## §3  Argument agreement at a translated call -/

/-- At a translated call with variable arguments bound in the environment and at
    the tower, the argument values are related by `bridge` to the tower slots the
    call reads. -/
theorem argsAgree_of_envAgrees (bridge : ValueTowerBridge) (env : Env) (rs : RustState)
    (dt : TowerType) (hT : envAgreesRustTower bridge env rs) :
    ∀ (args : List ImpExpr) (args' : List Located) (vals : List Value),
      haxArgsToLocated dt args = some args' →
      _root_.CatCrypt.Crypto.Hax.AllVars env args vals →
      ArgsTowerBound rs args' →
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => bridge p.1 v p.2) vals
        (args'.filterMap (fun a => rs.rsTower a.locVar)) := by
  intro args
  induction args with
  | nil =>
    intro args' vals hL hAV _
    simp only [haxArgsToLocated, Option.some.injEq] at hL
    subst hL
    cases hAV
    exact List.Forall₂.nil
  | cons a as ih =>
    intro args' vals hL hAV hB
    cases hAV with
    | cons n w as' ws hw hRest =>
      simp only [haxArgsToLocated, haxArgToLocated] at hL
      rcases hR : haxArgsToLocated dt as with _ | rest
      · rw [hR] at hL; cases hL
      · rw [hR] at hL
        simp only [Option.some.injEq] at hL
        subst hL
        obtain ⟨vv, hvv⟩ := hB _ (List.mem_cons_self ..)
        have hB' : ArgsTowerBound rs rest := fun b hb => hB b (List.mem_cons_of_mem _ hb)
        simp only [List.filterMap_cons]
        simp only at hvv
        rw [hvv]
        exact List.Forall₂.cons (hT n w hw _ vv hvv) (ih rest ws hR hRest hB')

/-! ## §4  The simulation predicate -/

/-- Every `ifThenElse` and `whileLoop` condition on the statement path of `e` is
    a variable in `S`. -/
def condsScalar (S : List String) : ImpExpr → Bool
  | .letBind _ _ body => condsScalar S body
  | .seq a b => condsScalar S a && condsScalar S b
  | .ifThenElse (.var c) t e => S.contains c && condsScalar S t && condsScalar S e
  | .whileLoop (.var c) body => S.contains c && condsScalar S body
  | .typeAscription e _ => condsScalar S e
  | _ => true

/-- Simulation of `e` under the checker's side conditions, with the agreement
    `envAgreesRustT`.  The conclusion re-establishes `ScopeBound` at the exit
    scope and `NamesFresh`. -/
def ProgSimT (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S : List String) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (Γ Γ' : TowerScope) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    simScope S Γ e = some Γ' → condsScalar S e = true →
    ScopeBound rs Γ → NamesFresh rs S →
    haxToLowCT e = some c →
    evalImp bi fuel e env = some (v, env') →
    envAgreesRustT bridge env rs →
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRustT bridge env' rs' ∧
      ScopeBound rs' Γ' ∧ NamesFresh rs' S

section ArmsT

variable (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (S : List String)

theorem progSimT_of_simScope_none (e : ImpExpr) (h : ∀ Γ, simScope S Γ e = none) :
    ProgSimT bridge bi N leafSpec S e := by
  intro fuel Γ Γ' c env env' rs v hScope
  rw [h Γ] at hScope
  cases hScope

theorem progSimT_var (name : String) : ProgSimT bridge bi N leafSpec S (.var name) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScope, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_var_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_var_inv bi fuel name env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSimT_unitVal : ProgSimT bridge bi N leafSpec S .unitVal := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScope, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_unitVal_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_unitVal_inv bi fuel env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSimT_tuple (es : List ImpExpr) : ProgSimT bridge bi N leafSpec S (.tuple es) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hAll
    rw [Option.some.injEq] at hScope
    subst hScope
    rw [haxToLowCT_tuple_of_vars es hAll] at hHax
    cases hHax
    have henv := evalImp_tuple_vars_inv bi fuel es env v env' hAll hEval
    subst henv
    exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩
  · cases hScope

theorem progSimT_seq (a b : ImpExpr)
    (iha : ProgSimT bridge bi N leafSpec S a) (ihb : ProgSimT bridge bi N leafSpec S b) :
    ProgSimT bridge bi N leafSpec S (.seq a b) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  simp only [simScope] at hScope
  rcases hA : simScope S Γ a with _ | Γ₁
  · rw [hA] at hScope; cases hScope
  rw [hA] at hScope
  obtain ⟨aC, bC, hAtrans, hBtrans, hC⟩ := haxToLowCT_seq_some a b c hHax
  subst hC
  obtain ⟨vA, env_mid, hAeval, hBeval⟩ := evalImp_seq_inv bi fuel a b env v env' hEval
  obtain ⟨rs_mid, hAexec, hAgreeMid, hSBmid, hSFmid⟩ :=
    iha fuel Γ Γ₁ aC env env_mid rs vA hA hConds.1 hSB hSF hAtrans hAeval hAgree
  obtain ⟨rs', hBexec, hAgree', hSB', hSF'⟩ :=
    ihb fuel Γ₁ Γ' bC env_mid env' rs_mid v hScope hConds.2 hSBmid hSFmid hBtrans hBeval
      hAgreeMid
  exact ⟨rs', rustExec_RSeq_chain N leafSpec aC bC rs rs_mid rs' hAexec hBexec,
         hAgree', hSB', hSF'⟩

theorem progSimT_ifThenElse (cond : String) (t e : ImpExpr)
    (iht : ProgSimT bridge bi N leafSpec S t) (ihe : ProgSimT bridge bi N leafSpec S e) :
    ProgSimT bridge bi N leafSpec S (.ifThenElse (.var cond) t e) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  obtain ⟨⟨hCondS, hCt⟩, hCe⟩ := hConds
  have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
  simp only [simScope] at hScope
  rcases hT : simScope S Γ t with _ | Γt
  · rw [hT] at hScope; cases hScope
  rcases hE : simScope S Γ e with _ | Γe
  · rw [hT, hE] at hScope; cases hScope
  rw [hT, hE] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ := haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  rcases evalImp_ifThenElse_var_inv bi fuel cond t e env v env' hEval with
    ⟨hCond, hTeval⟩ | ⟨hCond, hEeval⟩
  · obtain ⟨rs', hTexec, hAgree', hSB', hSF'⟩ :=
      iht fuel Γ Γt tC env env' rs v hT hCt hSB hSF hTtrans hTeval hAgree
    have hScalar : rs.rsScalar cond = 1 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_true N leafSpec cond tC eC rs rs' 1 hScalar
      (by decide) hTexec, hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γt (simScope_lookup_mono S t Γ Γt hT) hSB'
  · obtain ⟨rs', hEexec, hAgree', hSB', hSF'⟩ :=
      ihe fuel Γ Γe eC env env' rs v hE hCe hSB hSF hEtrans hEeval hAgree
    have hScalar : rs.rsScalar cond = 0 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond false hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_false N leafSpec cond tC eC rs rs' hScalar hEexec,
      hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γe (simScope_lookup_mono S e Γ Γe hE) hSB'

theorem progSimT_whileLoop (cond : String) (body : ImpExpr)
    (ihBody : ProgSimT bridge bi N leafSpec S body) :
    ProgSimT bridge bi N leafSpec S (.whileLoop (.var cond) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  obtain ⟨hCondS, hCb⟩ := hConds
  simp only [simScope] at hScope
  rcases hB : simScope S Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bC, hBtrans, hC⟩ := haxToLowCT_whileLoop_var_some cond body c hHax
  subst hC
  have hMono := simScope_lookup_mono S body Γ Γb hB
  induction fuel generalizing env env' rs v with
  | zero =>
    exact absurd hEval (fun h => evalImp_whileLoop_var_fuel_zero_inv bi cond body env v env' h)
  | succ n IH =>
    have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
    rcases evalImp_whileLoop_var_step_inv bi n cond body env v env' hEval
        (denote_val_or_err_of_haxToLowCT bi (n+1) body bC hBtrans env) with
      ⟨hCondF, hv, henv⟩ | ⟨vB, env_mid, hCondTrue, hBodyEval, hLoopRec⟩
    · subst hv
      subst henv
      have hScalar : rs.rsScalar cond = 0 :=
        envAgreesRustT_bool_to_scalar bridge _ rs cond false hAgree hCondT hCondF
      exact ⟨rs, RustExec.whileFalse cond bC rs hScalar, hAgree, hSB, hSF⟩
    · have hScalar : rs.rsScalar cond = 1 :=
        envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCondTrue
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid⟩ :=
        ihBody (n+1) Γ Γb bC env env_mid rs vB hB hCb hSB hSF hBtrans hBodyEval hAgree
      have hSBmid' : ScopeBound rs_mid Γ := ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid
      obtain ⟨rs', hLoopExec, hAgree', hSB', hSF'⟩ :=
        IH env_mid env' rs_mid v hSBmid' hSFmid hLoopRec hAgreeMid
      exact ⟨rs', RustExec.whileTrue cond bC rs rs_mid rs' 1 hScalar (by decide)
               hBodyExec hLoopExec, hAgree', hSB', hSF'⟩

theorem progSimT_letBind_lit (name : String) (l : ImpLit) (body : ImpExpr)
    (ihBody : ProgSimT bridge bi N leafSpec S body) :
    ProgSimT bridge bi N leafSpec S (.letBind name (.lit l) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScope] at hScope
  split at hScope
  · rename_i hIn
    obtain ⟨bodyC, n, hBodyTrans, hDecode, hC⟩ :=
      haxToLowCT_letBind_lit_some name l body c hHax
    subst hC
    have hBodyEval := evalImp_letBind_lit_inv bi fuel name l body env v env' hEval
    have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
    have hAgreeExt : envAgreesRustT bridge (env.extend name (Value.ofLit l))
                      (rsSetScalar rs name n) :=
      envAgreesRustT_extend_scalar_fresh bridge env rs name (Value.ofLit l) n hFresh hDecode
        hAgree
    obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
      ihBody fuel Γ Γ' bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name n) v
        hScope hConds hSB hSF hBodyTrans hBodyEval hAgreeExt
    exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name n bodyC rs rs' hBodyExec,
           hAgree', hSB', hSF'⟩
  · cases hScope

theorem progSimT_letBind_var (name src : String) (body : ImpExpr)
    (ihBody : ProgSimT bridge bi N leafSpec S body) :
    ProgSimT bridge bi N leafSpec S (.letBind name (.var src) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScope] at hScope
  split at hScope
  · rename_i hc
    obtain ⟨w, hw, hBodyEval⟩ := evalImp_letBind_var_inv bi fuel _ _ body env v env' hEval
    by_cases hEq : name = src
    · subst hEq
      rw [haxToLowCT_letBind_var_self] at hHax
      rw [Env.extend_self env _ w hw] at hBodyEval
      exact ihBody fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hBodyEval hAgree
    · have hIn : S.contains name = true ∧ S.contains src = true := by simp_all
      obtain ⟨bodyC, hBodyT, rfl⟩ := haxToLowCT_letBind_var_ne_some name src body c hEq hHax
      obtain ⟨rs', hExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel Γ Γ' bodyC (env.extend name w) env' (rsSetScalar rs name (rs.rsScalar src))
          v hScope hConds hSB hSF hBodyT hBodyEval
          (envAgreesRustT_extend_copy bridge env rs name src w
            (hSF name (mem_of_contains S name hIn.1)) (hSF src (mem_of_contains S src hIn.2))
            hw hAgree)
      exact ⟨rs', rustExec_letBind_copy N leafSpec name src bodyC rs rs' hEq hExec,
        hAgree', hSB', hSF'⟩
  · cases hScope

/-- A tower update at a name no argument reads leaves the slots the call reads
    unchanged. -/
theorem filterMap_rsSetTower_avoid (rs : RustState) (name : String)
    (x : Σ t : TowerType, RustVal t) (args' : List Located)
    (hAF : ∀ a ∈ args', a.locVar ≠ name) :
    args'.filterMap (fun a => (rsSetTower rs name x).rsTower a.locVar)
      = args'.filterMap (fun a => rs.rsTower a.locVar) := by
  apply List.filterMap_congr
  intro a ha
  exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs name a.locVar x (Ne.symm (hAF a ha))

theorem progSimT_letBind_app (name f : String) (args : List ImpExpr) (body : ImpExpr)
    (hLeaf : LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hf_arr : f ≠ "array_update") (hf_idx : f ≠ "index")
    (ihBody : ProgSimT bridge bi N leafSpec S body) :
    ProgSimT bridge bi N leafSpec S (.letBind name (.app f args) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScope, if_neg hf_arr, if_neg hf_idx] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hNotSc, hArgsIn⟩, hAvoid⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
      haxToLowCT_letBind_app_some name f args body c hf_arr hf_idx (by simpa using hNotSc) hHax
    subst hC
    have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f args body env v env'
      (argsInScope_allVars Γ _ args hArgsIn) hEval
    obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
      evalImp_letBind_app_vars_inv bi fuel name f args body env v env' hArgsEnv hEval
    have hAB : ArgsTowerBound rs args' := argsInScope_bound Γ _ rs hSB args args' hArgsIn hArgsT
    have hAF : ∀ a ∈ args', a.locVar ≠ name := argsAvoid_fresh name _ args args' hAvoid hArgsT
    set dt := towerOfCallName f with hdt_def
    set dest : Located := { locVar := name, locSrc := dt } with hdest_def
    set rs_init := rsSetTower rs name ⟨dt, default⟩ with hrs_init_def
    have hABinit : ArgsTowerBound rs_init args' :=
      ArgsTowerBound_preserved_extend rs args' name ⟨dt, default⟩ hAF hAB
    have hLookup : locatedLookup rs_init dest = some default := locatedLookup_letZero rs name dt
    set argList := args'.filterMap (fun a => rs_init.rsTower a.locVar) with hargList_def
    set newVal := leafSpec.call f dt (args'.map (·.locDst)) default argList with hnewVal_def
    set rs_mid := locatedUpdate rs_init dest newVal with hrs_mid_def
    have hCallArgs : ∀ a ∈ args', ∃ vv, rs_init.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
      hABinit
    have hCall : RustExec N leafSpec (.RCall f dest args') rs_init rs_mid :=
      RustExec.call (N := N) (leafSpec := leafSpec)
        f dest args' rs_init default argList hLookup rfl hCallArgs
    have hArgsAgree :
        List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => bridge p.1 v p.2) vals argList := by
      rw [hargList_def, hrs_init_def, filterMap_rsSetTower_avoid rs name _ args' hAF]
      exact argsAgree_of_envAgrees bridge env rs dt hAgree.2 args args' vals hArgsT hAV hAB
    have hBridgeAgr : bridge dt vRes newVal := hLeaf args' vals argList default vRes hBi hArgsAgree
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨dt, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨dt, default⟩) name ⟨dt, newVal⟩
           = rsSetTower rs name ⟨dt, newVal⟩
      exact rsSetTower_collapse rs name ⟨dt, default⟩ ⟨dt, newVal⟩
    have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustT_extend_tower bridge env rs name vRes dt newVal hAgree hBridgeAgr
    have hSBmid : ScopeBound rs_mid ((name, dt) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name dt newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, dt) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
        hScope hConds hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name dt _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hCall hBodyExec
  · cases hScope

/-- The tuple-component load agrees with `Value.projIdx` under `bridge`. -/
def TupleLoadAgrees (bridge : ValueTowerBridge) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (i : Nat) (vTup vi : Value) (srcV : RustVal .TFp),
    bridge .TFp vTup srcV → vTup.projIdx i = some vi →
    bridge .TFp vi
      (leafSpec.tupleLoad { locVar := name, locSrc := .TFp } (default : RustVal .TFp)
        ⟨.TFp, srcV⟩ i)

theorem progSimT_letBind_proj (name t : String) (i : Nat) (body : ImpExpr)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (ihBody : ProgSimT bridge bi N leafSpec S body) :
    ProgSimT bridge bi N leafSpec S (.letBind name (.proj (.var t) i) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScope] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hLk, hNe⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_proj_some name t i body c hHax
    subst hC
    obtain ⟨vTup, vi, hEnvT, hProjI, hBodyEval⟩ :=
      evalImp_letBind_proj_inv bi fuel name t i body env v env' hEval
    obtain ⟨srcV, hRawT⟩ := hSB t .TFp hLk
    have hSrcLook : locatedLookup rs { locVar := t, locSrc := .TFp } = some srcV :=
      locatedLookup_of_rsTower rs t .TFp srcV hRawT
    set dst : Located := { locVar := name, locSrc := .TFp } with hdst
    set src : Located := { locVar := t, locSrc := .TFp } with hsrc
    set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
    have hDstLook : locatedLookup rs_init dst = some default :=
      locatedLookup_letZero rs name .TFp
    have hSrcLook' : locatedLookup rs_init src = some srcV := by
      rw [hrs_init,
          CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
            rs name ⟨.TFp, default⟩ src (Ne.symm hNe)]
      exact hSrcLook
    set newVal := leafSpec.tupleLoad dst default ⟨src.locDst, srcV⟩ i with hnewVal
    set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
    have hLoad : RustExec N leafSpec (.RTupleLoad dst src i) rs_init rs_mid :=
      RustExec.tupleLoad dst src i rs_init default srcV hDstLook hSrcLook'
    have hTupBridge : bridge .TFp vTup srcV := hAgree.2 t vTup hEnvT .TFp srcV hRawT
    have hCompBridge : bridge .TFp vi newVal := hProj name i vTup vi srcV hTupBridge hProjI
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
          = rsSetTower rs name ⟨.TFp, newVal⟩
      exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
    have hAgreeMid : envAgreesRustT bridge (env.extend name vi) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustT_extend_tower bridge env rs name vi .TFp newVal hAgree hCompBridge
    have hSBmid : ScopeBound rs_mid ((name, .TFp) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vi) env' rs_mid v
        hScope hConds hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name .TFp _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hLoad hBodyExec
  · cases hScope

theorem progSimT_assign_lit (name : String) (l : ImpLit) :
    ProgSimT bridge bi N leafSpec S (.assign name (.lit l)) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hIn
    rw [Option.some.injEq] at hScope
    subst hScope
    have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
    obtain ⟨m, hC⟩ := haxToLowCT_assign_lit_shape name l c hHax
    subst hC
    obtain ⟨_, henv⟩ := evalImp_assign_lit_inv bi fuel name l env v env' hEval
    subst henv
    have hDecode : valueToScalar (Value.ofLit l) = some m := by
      cases l with
      | uintLit w n =>
        rw [haxToLowCT_assign_lit_uintLit_some, Option.some.injEq] at hHax
        cases hHax; rfl
      | bool b =>
        rw [haxToLowCT_assign_lit_bool_some, Option.some.injEq] at hHax
        cases hHax; cases b <;> rfl
      | int n =>
        by_cases hn : 0 ≤ n
        · rw [haxToLowCT_assign_lit_int_some_of_nonneg name n hn, Option.some.injEq] at hHax
          cases hHax
          simp [Value.ofLit, valueToScalar, hn]
        · simp [haxToLowCT, hn] at hHax
      | unit => simp [haxToLowCT] at hHax
      | sintLit _ _ => simp [haxToLowCT] at hHax
    exact ⟨_, RustExec.scalarSet name m rs,
      envAgreesRustT_extend_scalar_fresh bridge env rs name _ m hFresh hDecode hAgree, hSB,
      fun k hk => by
        show (rsSetScalar rs name m).rsTower k = none
        exact hSF k hk⟩
  · cases hScope

theorem progSimT_assign_app (name f : String) (args : List ImpExpr) (hf : f ≠ "array_update")
    (hLeaf : LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge) :
    ProgSimT bridge bi N leafSpec S (.assign name (.app f args)) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScope, if_neg hf] at hScope
  split at hScope
  · rename_i hc
    rw [Option.some.injEq] at hScope
    subst hScope
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hArgsIn, hLk⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', hArgsT, hC⟩ := haxToLowCT_assign_app_some name f args c hf hHax
    subst hC
    have hArgsEnv := evalImp_assign_app_argsDefined bi fuel name f args env v env'
      (argsInScope_allVars Γ _ args hArgsIn) hEval
    obtain ⟨vals, vRes, hAV, hBi, henvEq, hvEq⟩ :=
      evalImp_assign_app_vars_inv bi fuel name f args env v env' hArgsEnv hEval
    subst henvEq
    subst hvEq
    have hAB : ArgsTowerBound rs args' := argsInScope_bound Γ _ rs hSB args args' hArgsIn hArgsT
    set dt := towerOfCallName f with hdt_def
    obtain ⟨oldV, hOld⟩ := hSB name dt hLk
    set dest : Located := { locVar := name, locSrc := dt } with hdest_def
    have hLookup : locatedLookup rs dest = some oldV := locatedLookup_of_rsTower rs name _ oldV hOld
    set argList := args'.filterMap (fun a => rs.rsTower a.locVar) with hargList_def
    set newVal := leafSpec.call f dt (args'.map (·.locDst)) oldV argList with hnewVal_def
    have hCall : RustExec N leafSpec (.RCall f dest args') rs (locatedUpdate rs dest newVal) :=
      RustExec.call (N := N) (leafSpec := leafSpec) f dest args' rs oldV argList hLookup rfl hAB
    have hArgsAgree :
        List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => bridge p.1 v p.2) vals argList :=
      argsAgree_of_envAgrees bridge env rs dt hAgree.2 args args' vals hArgsT hAV hAB
    have hBridgeAgr : bridge dt vRes newVal := hLeaf args' vals argList oldV vRes hBi hArgsAgree
    have hRsEq : locatedUpdate rs dest newVal = rsSetTower rs name ⟨dt, newVal⟩ := rfl
    refine ⟨_, hCall, ?_, ?_, ?_⟩
    · rw [hRsEq]
      exact envAgreesRustT_extend_tower bridge env rs name vRes dt newVal hAgree hBridgeAgr
    · rw [hRsEq]
      exact ScopeBound_rsSetTower_same rs Γ name _ newVal hLk hSB
    · rw [hRsEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
  · cases hScope

end ArmsT

/-! ## §5  The program-level theorem -/

/-- **Program-level simulation with scalar-valued call results.**  Every source
    program simulates under `envAgreesRustT`, when every call name satisfies
    `LeafCallAgreesArgs`, tuple loads agree with `Value.projIdx`, and the builtin
    table implements neither `array_update` nor `index`. -/
theorem haxToLowCT_simulates_programT
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S : List String)
    (hLeaf : ∀ f, LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hArr : ∀ vals, bi "array_update" vals = none)
    (hIdx : ∀ vals, bi "index" vals = none)
    (e : ImpExpr) : ProgSimT bridge bi N leafSpec S e := by
  induction e using ImpExpr.ind with
  | var name => exact progSimT_var bridge bi N leafSpec S name
  | unitVal => exact progSimT_unitVal bridge bi N leafSpec S
  | seq a b iha ihb => exact progSimT_seq bridge bi N leafSpec S a b iha ihb
  | tuple es _ => exact progSimT_tuple bridge bi N leafSpec S es
  | letBind name val body _ ihBody =>
    cases val with
    | lit l => exact progSimT_letBind_lit bridge bi N leafSpec S name l body ihBody
    | app f args =>
      by_cases hf_arr : f = "array_update"
      · subst hf_arr
        intro fuel _ _ _ env env' _ v _ _ _ _ _ hEval _
        exact absurd hEval (fun h =>
          evalImp_letBind_app_vacuous bi fuel name "array_update" args body env v env' hArr h)
      by_cases hf_idx : f = "index"
      · subst hf_idx
        intro fuel _ _ _ env env' _ v _ _ _ _ _ hEval _
        exact absurd hEval (fun h =>
          evalImp_letBind_app_vacuous bi fuel name "index" args body env v env' hIdx h)
      exact progSimT_letBind_app bridge bi N leafSpec S name f args body (hLeaf f)
        hf_arr hf_idx ihBody
    | var src => exact progSimT_letBind_var bridge bi N leafSpec S name src body ihBody
    | proj pe i =>
      cases pe with
      | var t => exact progSimT_letBind_proj bridge bi N leafSpec S name t i body hProj ihBody
      | _ => exact progSimT_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
    | _ => exact progSimT_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | ifThenElse cond t e _ iht ihe =>
    cases cond with
    | var v_cond => exact progSimT_ifThenElse bridge bi N leafSpec S v_cond t e iht ihe
    | _ => exact progSimT_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | whileLoop cond body _ ihBody =>
    cases cond with
    | var v_cond => exact progSimT_whileLoop bridge bi N leafSpec S v_cond body ihBody
    | _ => exact progSimT_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | assign name rhs _ =>
    cases rhs with
    | lit l => exact progSimT_assign_lit bridge bi N leafSpec S name l
    | app f args =>
      by_cases hf : f = "array_update"
      · exact progSimT_of_simScope_none bridge bi N leafSpec S _
          (fun Γ => by simp only [simScope, if_pos hf])
      · exact progSimT_assign_app bridge bi N leafSpec S name f args hf (hLeaf f)
    | _ => exact progSimT_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | typeAscription e _ ih =>
    intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
    simp only [simScope] at hScope
    simp only [condsScalar] at hConds
    rw [haxToLowCT_typeAscription_eq] at hHax
    rw [evalImp_typeAscription] at hEval
    exact ih fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  | _ => exact progSimT_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])

end CatCrypt.Crypto.Hax
