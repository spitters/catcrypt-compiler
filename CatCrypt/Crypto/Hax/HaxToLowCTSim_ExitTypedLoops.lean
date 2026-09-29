/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTypedSteps

/-!
# The exit-flag lowering with one heap per name: arms and loops

The third of four parts of the typed exit-flag lowering; the overview is the docstring of
`HaxToLowCTSim_ExitTyped.lean`.  This part holds §13–§14: the simulation of the arms
without a loop, and of the loops, among them the counted loops with bounds read at run
time (`exitForLoopVT_sim`, `breakForLoopVT_sim`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT Located SExpr RustState RustExec LeafSpec rsSetScalar)

open CatCrypt.Crypto.Jasmin.LowCT (rsSetTower locatedLookup locatedUpdate RustVal towerLimb
  rsTowerLimb)

/-! ## §13  The arms without a loop -/

section Arms

variable (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
  (A : ExitTowers) (R : ExitRes)

theorem exitSimTy_var (x : String) : ExitSimTy bi N leafSpec br A R (.var x) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hx : exitReserved x = false ∧ (tl = true → ExitRes.ofPlace (A.lookup x) = R) := by
    cases tl <;> cases fl <;> simp_all [exitSimOkT]
  rw [denote'_var_run] at hrun
  cases hv : env x with
  | none =>
    rw [hv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  | some v =>
    rw [hv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    have hcf := envAgreesT_not_cf hag hx.1 hv
    cases tl with
    | false =>
      have hK' : haxToLowCTKT A false fl (.var x) = some (.RSkip, false) := by
        cases fl <;> rfl
      rw [hK'] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      exact ⟨rs, RustExec.skip rs,
        (envAgreesExitT_val hcf).mpr ⟨hret, hag, fun h => by cases h⟩, fun _ => hret⟩
    | true =>
      have hR := hx.2 rfl
      have hK' : haxToLowCTKT A true fl (.var x) =
          (resultStoreT A (.var x)).map fun s => (s, false) := by
        cases fl <;> rfl
      rw [hK'] at hK
      rcases hA : A.lookup x with _ | t
      · rw [hA] at hR
        subst hR
        simp only [resultStoreT, hA, resultStore, storeScalar, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨-, hdec⟩ := envAgreesT_scalar hag hx.1 hA hv
        obtain ⟨h0, hag', hres⟩ := res_writeT rs (rs.rsScalar x) hret hag
        exact ⟨_, RustExec.scalarSetExpr _ _ rs,
          (envAgreesExitT_val hcf).mpr ⟨h0, hag', fun _ => by
            show valueToScalar v = some _
            rw [hdec]; exact congrArg some hres.symm⟩,
          fun _ => h0⟩
      · rw [hA] at hR
        subst hR
        simp only [resultStoreT, hA, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hag hx.1 hA hv
        refine ⟨rsSetTower rs exitResName ⟨t, val⟩,
          RustExec.copy ⟨exitResName, t⟩ ⟨x, t⟩ rs rfl val (locatedLookup_of_rsTower rs x t val hval'),
          (envAgreesExitT_val hcf).mpr ⟨hret, envAgreesT_setTower_reserved _ exitReserved_res hag,
            fun _ => ⟨val, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _, hbr⟩⟩,
          fun _ => hret⟩

theorem exitSimTy_unitVal : ExitSimTy bi N leafSpec br A R .unitVal := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [denote'_unitVal_run] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases tl with
  | false =>
    have hK' : haxToLowCTKT A false fl .unitVal = some (.RSkip, false) := by cases fl <;> rfl
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    exact ⟨rs, RustExec.skip rs,
      (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩, fun _ => hret⟩
  | true =>
    have hR : R = .scalar := by
      cases fl <;> simpa [exitSimOkT, eq_comm] using hok
    subst hR
    have hK' : haxToLowCTKT A true fl .unitVal = some (.RScalarSet exitResName 0, false) := by
      cases fl <;> rfl
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨h0, hag', hres⟩ := res_writeT rs 0 hret hag
    exact ⟨_, RustExec.scalarSet _ _ rs,
      (envAgreesExitT_val rfl).mpr ⟨h0, hag', fun _ => by
        show valueToScalar Value.unit = some _
        rw [hres]; rfl⟩, fun _ => h0⟩

/-- The value and word of a literal of `exitLitOk` that `storeScalar` stores. -/
theorem storeScalar_lit {slot : String} {l : ImpLit} {s : LowCT} (hl : exitLitOk l = true)
    (hs : storeScalar slot (.lit l) = some s) :
    ∃ k, ScalarValN (Value.ofLit l) ∧ valueToScalar (Value.ofLit l) = some k ∧
      ∀ N leafSpec (rs : RustState), RustExec N leafSpec s rs (rsSetScalar rs slot k) := by
  cases l with
  | uintLit w m =>
    simp only [storeScalar, Option.some.injEq] at hs
    subst hs
    refine ⟨_, ?_, rfl, fun N leafSpec rs => RustExec.scalarSet _ _ _⟩
    show m % w.modulus < 2 ^ 64
    cases w <;> simp only [IntWidth.modulus, IntWidth.bits] <;> first
      | omega | (simp only [exitLitOk] at hl; exact absurd hl (by decide))
  | int z =>
    simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [storeScalar, hl.1, if_true, Option.some.injEq] at hs
    subst hs
    exact ⟨_, hl, by simp [valueToScalar, Value.ofLit, hl.1],
      fun N leafSpec rs => RustExec.scalarSet _ _ _⟩
  | bool b =>
    simp only [storeScalar, Option.some.injEq] at hs
    subst hs
    exact ⟨_, trivial, valueToScalar_bool b, fun N leafSpec rs => RustExec.scalarSet _ _ _⟩
  | _ => simp [storeScalar] at hs

theorem exitSimTy_lit (l : ImpLit) : ExitSimTy bi N leafSpec br A R (.lit l) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [denote'_lit_run] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases tl with
  | false => cases fl <;> simp [exitSimOkT] at hok
  | true =>
    have hh : exitLitOk l = true ∧ R = .scalar := by
      cases fl <;> simpa [exitSimOkT] using hok
    obtain ⟨hl, rfl⟩ := hh
    have hK' : haxToLowCTKT A true fl (.lit l) =
        (resultStore (.lit l)).map fun s => (s, false) := by
      cases fl <;> rfl
    rw [hK'] at hK
    rcases hs : resultStore (.lit l) with _ | s
    · rw [hs] at hK; cases hK
    rw [hs] at hK
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨k, hsv, hk, hex⟩ := storeScalar_lit hl hs
    obtain ⟨h0, hag', hres⟩ := res_writeT rs k hret hag
    exact ⟨_, hex N leafSpec rs, (envAgreesExitT_val hsv.not_cf).mpr ⟨h0, hag', fun _ => by
      show valueToScalar _ = some _
      rw [hres]; exact hk⟩, fun _ => h0⟩

theorem exitReserved_resComp (i : Nat) : exitReserved (exitResCompName i) = true := by
  show "__exit_".toList.isPrefixOf (exitResCompName i).toList = true
  simp [exitResCompName]

theorem exitResCompName_inj {i j : Nat} (h : exitResCompName i = exitResCompName j) : i = j := by
  have := congrArg String.length h
  simpa [exitResCompName, String.length_append] using this

theorem exitResCompName_ne_ret (i : Nat) : exitResCompName i ≠ exitRetName := by
  have hp : "__exit_rc".toList.isPrefixOf exitRetName.toList = false := by decide
  rintro h
  rw [← h] at hp
  simp [exitResCompName] at hp

/-- A run of a tuple ends in a value only when its components evaluate to values: the
    value is the tuple of the component values, in the environment the components end in. -/
theorem denote'_tuple_inv (fuel : Nat) (es : List ImpExpr) (env env' : Env) (o : Outcome)
    (h : (denote' bi fuel (.tuple es)).run env = (o, env')) (hval : ∃ v, o = .val v) :
    ∃ vals, (_root_.Hax.denoteArgs' bi fuel es).run env = (some vals, env') ∧
      o = .val (.tuple vals) := by
  simp only [denote', StateT.run, bind, Bind.bind, StateT.bind] at h
  rcases hA : _root_.Hax.denoteArgs' bi fuel es env with ⟨_ | vals, e1⟩
  · rw [hA] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    obtain ⟨_, h'⟩ := hval; cases h'
  · rw [hA] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨vals, hA, rfl⟩

/-- The component stores `tupleStoreT A i es` of a tuple of variables bound to `vals`:
    from a state agreeing with the environment, they run to a state agreeing with it, with
    the exit flag and the slots of the components before `i` unchanged, where component
    `j` of `vals` agrees with the slot `exitResCompName (i + j)`. -/
theorem tupleStoreT_sim {env : Env} :
    ∀ (es : List ImpExpr) (vals : List Value),
      List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) es vals →
      exitArgsOk es = true →
      ∀ (i : Nat) (s : LowCT) (rs : RustState), tupleStoreT A i es = some s →
        envAgreesT br A env rs →
        ∃ rs', RustExec N leafSpec s rs rs' ∧ envAgreesT br A env rs' ∧
          rs'.rsScalar exitRetName = rs.rsScalar exitRetName ∧
          (∀ (j : Nat) (w : Value), vals[j]? = some w →
            compAgreesT br (exitResCompName (i + j)) w rs') ∧
          (∀ k, k < i → rs'.rsScalar (exitResCompName k) = rs.rsScalar (exitResCompName k) ∧
            rs'.rsTower (exitResCompName k) = rs.rsTower (exitResCompName k))
  | [], vals, hF, _, i, s, rs, hs, hag => by
    cases hF
    simp only [tupleStoreT, Option.some.injEq] at hs
    subst hs
    exact ⟨rs, RustExec.skip rs, hag, rfl, fun j w h => by simp at h, fun _ _ => ⟨rfl, rfl⟩⟩
  | a :: es, vals, hF, hargs, i, s, rs, hs, hag => by
    rcases hF with _ | ⟨⟨x, rfl, hv⟩, hF⟩
    rename_i v vals
    simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
    simp only [tupleStoreT] at hs
    rcases hr : tupleStoreT A (i + 1) es with _ | rest
    · rw [hr] at hs; cases hs
    rw [hr] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    have hne : ∀ k, k < i → exitResCompName k ≠ exitResCompName i := fun k hk h =>
      absurd (exitResCompName_inj h) (Nat.ne_of_lt hk)
    rcases hA : A.lookup x with _ | t
    · rw [hA] at hs
      subst hs
      obtain ⟨hsv, hdec⟩ := envAgreesT_scalar hag hargs.1 hA hv
      let rs1 := rsSetScalar rs (exitResCompName i) (rs.rsScalar x)
      have hag1 : envAgreesT br A env rs1 :=
        envAgreesT_set_reserved _ (exitReserved_resComp i) hag
      obtain ⟨rs', hex, hag', hret', hcomp, hframe⟩ :=
        tupleStoreT_sim es vals hF hargs.2 (i + 1) rest rs1 hr hag1
      refine ⟨rs', RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ rs) hex, hag', ?_, ?_, ?_⟩
      · rw [hret']
        simp [rs1, rsScalar_rsSetScalar, Ne.symm (exitResCompName_ne_ret i)]
      · intro j w hw
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
          subst hw
          refine Or.inl ⟨hsv, ?_⟩
          rw [Nat.add_zero, (hframe i (Nat.lt_succ_self i)).1]
          simp [rs1, rsScalar_rsSetScalar, hdec]
        | succ j =>
          simp only [List.getElem?_cons_succ] at hw
          have := hcomp j w hw
          rwa [show i + 1 + j = i + (j + 1) by omega] at this
      · intro k hk
        obtain ⟨h1, h2⟩ := hframe k (Nat.lt_succ_of_lt hk)
        refine ⟨?_, h2⟩
        rw [h1]
        simp [rs1, rsScalar_rsSetScalar, hne k hk]
    · rw [hA] at hs
      subst hs
      obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hag hargs.1 hA hv
      let rs1 := rsSetTower rs (exitResCompName i) ⟨t, val⟩
      have hag1 : envAgreesT br A env rs1 :=
        envAgreesT_setTower_reserved _ (exitReserved_resComp i) hag
      obtain ⟨rs', hex, hag', hret', hcomp, hframe⟩ :=
        tupleStoreT_sim es vals hF hargs.2 (i + 1) rest rs1 hr hag1
      refine ⟨rs', RustExec.seq _ _ _ _ _
        (RustExec.copy ⟨exitResCompName i, t⟩ ⟨x, t⟩ rs rfl val
          (locatedLookup_of_rsTower rs x t val hval')) hex, hag', hret', ?_, ?_⟩
      · intro j w hw
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
          subst hw
          refine Or.inr ⟨t, val, ?_, hbr⟩
          rw [Nat.add_zero, (hframe i (Nat.lt_succ_self i)).2]
          exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
        | succ j =>
          simp only [List.getElem?_cons_succ] at hw
          have := hcomp j w hw
          rwa [show i + 1 + j = i + (j + 1) by omega] at this
      · intro k hk
        obtain ⟨h1, h2⟩ := hframe k (Nat.lt_succ_of_lt hk)
        refine ⟨h1, ?_⟩
        rw [h2]
        exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ (hne k hk).symm

theorem exitSimOkT_app_inv {tl il : Bool} {f : String} {args : List ImpExpr}
    (h : exitSimOkT A R tl il (.app f args) = true) :
    tl = true ∧ ((f = "None" ∧ args = [] ∧ R.isOption = true) ∨
      ∃ x, f = "Some" ∧ args = [.var x] ∧ exitReserved x = false ∧ R = .option (A.lookup x)) := by
  unfold exitSimOkT at h
  split at h <;> simp_all

theorem exitResCompName_ne_res (i : Nat) : exitResCompName i ≠ exitResName := by
  have hp : "__exit_rc".toList.isPrefixOf exitResName.toList = false := by decide
  rintro h
  rw [← h] at hp
  simp [exitResCompName] at hp

/-- **The `Option` tails** `None()` and `Some(x)`: the tag `0` or `1` is stored into the
    scalar result slot and the payload of `Some(x)` into the slot `exitResCompName 0`. -/
theorem exitSimTy_app (hC : OptCtors bi) (f : String) (args : List ImpExpr) :
    ExitSimTy bi N leafSpec br A R (.app f args) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  obtain ⟨rfl, hcase⟩ := exitSimOkT_app_inv A R hok
  have hK' : haxToLowCTKT A true fl (.app f args) =
      (resultStoreT A (.app f args)).map fun s => (s, false) := by
    cases fl <;> rfl
  rw [hK'] at hK
  rw [denote'_app_run] at hrun
  rcases hcase with ⟨rfl, rfl, hR⟩ | ⟨x, rfl, rfl, hx, rfl⟩
  · simp only [resultStoreT, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denoteArgs'_nil_run] at hrun
    cases hbi : bi "None" [] with
    | none =>
      simp only [hbi] at hrun
      obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨-, rfl⟩ := hC.1 [] r hbi
      obtain ⟨h0, hag', hres⟩ := res_writeT rs 0 hret hag
      obtain ⟨p, rfl⟩ : ∃ p, R = .option p := by
        cases R <;> simp_all [ExitRes.isOption]
      exact ⟨_, RustExec.scalarSet _ _ rs,
        (envAgreesExitT_val rfl).mpr ⟨h0, hag', fun _ => Or.inl ⟨rfl, hres⟩⟩, fun _ => h0⟩
  · have hargs : exitArgsOk [.var x] = true := by simp [exitArgsOk, hx]
    rcases hA : (_root_.Hax.denoteArgs' bi fuel [.var x]).run env with ⟨oa, e1⟩
    obtain ⟨he1, hF⟩ := denoteArgs'_vars_inv bi fuel [.var x] hargs env e1 oa hA
    subst e1
    rw [hA] at hrun
    rcases oa with _ | vals
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    obtain ⟨v, rfl, hv⟩ : ∃ v, vals = [v] ∧ env x = some v := by
      rcases hF vals rfl with _ | ⟨⟨y, hy, hyv⟩, hrest⟩
      cases hrest
      cases hy
      exact ⟨_, rfl, hyv⟩
    cases hbi : bi "Some" [v] with
    | none =>
      simp only [hbi] at hrun
      obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨v', hv', rfl⟩ := hC.2 [v] r hbi
      cases hv'
      have hne0 : exitResCompName 0 ≠ exitResName := exitResCompName_ne_res 0
      rcases hAx : A.lookup x with _ | t
      · simp only [resultStoreT, hAx, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨hsv, hdv⟩ := envAgreesT_scalar hag hx hAx hv
        let rs1 := rsSetScalar rs (exitResCompName 0) (rs.rsScalar x)
        have hag1 : envAgreesT br A env rs1 := envAgreesT_set_reserved _ (exitReserved_resComp 0) hag
        have hret1 : rs1.rsScalar exitRetName = 0 := by
          simp only [rs1, rsScalar_rsSetScalar, if_neg (exitResCompName_ne_ret 0).symm]; exact hret
        obtain ⟨h0, hag2, hres⟩ := res_writeT rs1 1 hret1 hag1
        refine ⟨rsSetScalar rs1 exitResName 1,
          RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ rs) (RustExec.scalarSet _ _ _),
          (envAgreesExitT_val rfl).mpr ⟨h0, hag2, fun _ => Or.inr ⟨v, rfl, hres, hsv, ?_⟩⟩,
          fun _ => h0⟩
        rw [hdv]
        simp [rs1, rsScalar_rsSetScalar, hne0]
      · simp only [resultStoreT, hAx, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨hvcf, val, hval', hbr⟩ := envAgreesT_tower hag hx hAx hv
        let rs1 := rsSetTower rs (exitResCompName 0) ⟨t, val⟩
        have hag1 : envAgreesT br A env rs1 :=
          envAgreesT_setTower_reserved _ (exitReserved_resComp 0) hag
        have hret1 : rs1.rsScalar exitRetName = 0 := hret
        obtain ⟨h0, hag2, hres⟩ := res_writeT rs1 1 hret1 hag1
        refine ⟨rsSetScalar rs1 exitResName 1, RustExec.seq _ _ _ _ _
            (RustExec.copy ⟨exitResCompName 0, t⟩ ⟨x, t⟩ rs rfl val
              (locatedLookup_of_rsTower rs x t val hval')) (RustExec.scalarSet _ _ _),
          (envAgreesExitT_val rfl).mpr ⟨h0, hag2, fun _ => Or.inr ⟨v, rfl, hres, val,
            (show rs1.rsTower (exitResCompName 0) = some ⟨t, val⟩ from
              CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _), hbr⟩⟩,
          fun _ => h0⟩

theorem exitSimTy_tuple (es : List ImpExpr) : ExitSimTy bi N leafSpec br A R (.tuple es) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  cases tl with
  | false => cases fl <;> simp [exitSimOkT] at hok
  | true =>
    have hh : R = .tuple ∧ exitArgsOk es = true := by
      cases fl <;> simpa [exitSimOkT] using hok
    obtain ⟨rfl, hargs⟩ := hh
    obtain ⟨vals, hA, rfl⟩ := denote'_tuple_inv bi fuel es env env' o hrun hval
    obtain ⟨rfl, hF⟩ := denoteArgs'_vars_inv bi fuel es hargs env env' (some vals) hA
    have hK' : haxToLowCTKT A true fl (.tuple es) =
        (tupleStoreT A 0 es).map fun s => (s, false) := by
      cases fl <;> rfl
    rw [hK'] at hK
    rcases hs : tupleStoreT A 0 es with _ | s
    · rw [hs] at hK; cases hK
    rw [hs] at hK
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨rs', hex, hag', hret', hcomp, -⟩ :=
      tupleStoreT_sim N leafSpec br A es vals (hF vals rfl) hargs 0 s rs hs hag
    refine ⟨rs', hex, (envAgreesExitT_val rfl).mpr ⟨hret'.trans hret, hag', fun _ =>
      ⟨vals, rfl, fun j w hw => by simpa using hcomp j w hw⟩⟩, fun _ => hret'.trans hret⟩

theorem exitSimTy_cfBreak (p : ImpExpr) : ExitSimTy bi N leafSpec br A R (.cfBreak p) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  cases fl with
  | none => cases tl <;> simp [exitSimOkT] at hok
  | some r =>
    have hp : exitPayloadOk A p = true := by cases tl <;> simpa [exitSimOkT] using hok
    rw [denote'_cfBreak_run'] at hrun
    obtain ⟨v, k, s, hpay, hsv, hk, hs, hsexec⟩ :
        ∃ v k s, (denote' bi fuel p).run env = (.val v, env) ∧ ScalarValN v ∧
          valueToScalar v = some k ∧ storeScalar exitValName p = some s ∧
          RustExec N leafSpec s rs (rsSetScalar rs exitValName k) := by
      cases p with
      | var x =>
        simp only [exitPayloadOk, Bool.and_eq_true, Bool.not_eq_true'] at hp
        have hsc : A.lookup x = none := by simpa [exitSc] using hp.2
        rw [denote'_var_run] at hrun ⊢
        cases hv : env x with
        | none =>
          rw [hv] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          obtain ⟨_, h⟩ := hval; cases h
        | some v =>
          obtain ⟨hsv, hdec⟩ := envAgreesT_scalar hag hp.1 hsc hv
          exact ⟨v, rs.rsScalar x, _, rfl, hsv, hdec, rfl, RustExec.scalarSetExpr _ _ rs⟩
      | lit l =>
        simp only [exitPayloadOk] at hp
        rcases hs : storeScalar exitValName (.lit l) with _ | s
        · have hK' : haxToLowCTKT A tl (some r) (.cfBreak (.lit l)) = none := by
            rw [haxToLowCTKT_cfBreak_eq _ _ _ _ rfl]; simp [exitStore, hs]
          rw [hK'] at hK; cases hK
        obtain ⟨k, hsv, hk, hex⟩ := storeScalar_lit hp hs
        exact ⟨_, k, s, denote'_lit_run bi fuel l env, hsv, hk, rfl, hex N leafSpec rs⟩
      | unitVal =>
        exact ⟨.unit, 0, _, denote'_unitVal_run bi fuel env, trivial, rfl, rfl,
          RustExec.scalarSet _ _ rs⟩
      | _ => simp [exitPayloadOk] at hp
    rw [hpay] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (Outcome.val (.controlFlow true v), env) = (o, env') by
      rw [← hrun]
      rcases hsv.cases with ⟨_, _, rfl, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ | rfl <;> rfl)
    have hK' : haxToLowCTKT A tl (some r) (.cfBreak p) =
        some (.RSeq s (.RScalarSet exitRetName 1), true) := by
      rw [haxToLowCTKT_cfBreak_eq _ _ _ _ (exitScE_of_payloadOk hp)]; simp [exitStore, hs]
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    refine ⟨_, RustExec.seq _ _ _ _ _ hsexec (RustExec.scalarSet _ _ _), ?_, fun h => by cases h⟩
    refine ⟨by simp, ?_, ?_⟩
    · rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val.symm, rsScalar_rsSetScalar, if_pos rfl]
      exact hk
    · exact envAgreesT_set_reserved 1 exitReserved_ret
        (envAgreesT_set_reserved k exitReserved_val hag)

theorem exitSimTy_seq (a b : ImpExpr) (iha : ExitSimTy bi N leafSpec br A R a)
    (ihb : ExitSimTy bi N leafSpec br A R b) : ExitSimTy bi N leafSpec br A R (.seq a b) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
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
  rcases hra : (denote' bi fuel a).run env with ⟨oa, e1⟩
  cases oa with
  | val va =>
    obtain ⟨rs1, hexA, hagA, hxA⟩ :=
      iha false fl fuel env e1 (.val va) rs aC xa hok'.1 hfl hA hra ⟨va, rfl⟩ hag hret
    cases hcf : va.isControlFlow with
    | false =>
      obtain ⟨h1, hag1, -⟩ := (envAgreesExitT_val hcf).mp hagA
      rw [denote'_seq_run_val bi fuel a b env e1 va hra hcf] at hrun
      obtain ⟨rs', hexB, hagB, hxB⟩ :=
        ihb tl fl fuel e1 env' o rs1 bC xb' hok'.2 hfl hB hrun hval hag1 h1
      refine ⟨rs', ?_, hagB, fun h => hxB (by simp at h; exact h.2)⟩
      cases xa
      · exact RustExec.seq _ _ _ _ _ hexA hexB
      · exact RustExec.seq _ _ _ _ _ hexA (exitGuard_running _ _ _ _ _ h1 hexB)
    | true =>
      cases va with
      | controlFlow k w =>
        cases k with
        | false => exact (show False from hagA).elim
        | true =>
          obtain ⟨h1, hw, hag1⟩ := hagA
          rw [denote'_seq_run_cf bi fuel a b env e1 true w hra] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          cases xa with
          | false => have h0 := hxA rfl; rw [h1] at h0; cases h0
          | true =>
            exact ⟨rs1, RustExec.seq _ _ _ _ _ hexA (exitGuard_exited _ _ _ _ h1),
              ⟨h1, hw, hag1⟩, fun h => by simp at h⟩
      | _ => simp at hcf
  | _ =>
    rw [denote'_seq_run_nonval bi fuel a b env e1 _ hra (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h

theorem exitSimTy_ifThenElse (v : String) (t e : ImpExpr)
    (iht : ExitSimTy bi N leafSpec br A R t) (ihe : ExitSimTy bi N leafSpec br A R e) :
    ExitSimTy bi N leafSpec br A R (.ifThenElse (.var v) t e) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : exitReserved v = false ∧ exitSc A v = true ∧
      exitSimOkT A R tl fl.isSome t = true ∧ exitSimOkT A R tl fl.isSome e = true := by
    cases tl <;> cases fl <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1, hok.1.1.2, hok.1.2, hok.2⟩)
  have hvsc : A.lookup v = none := by simpa [exitSc] using hok'.2.1
  rw [haxToLowCTKT_ifThenElse_eq _ _ _ _ _ _ hok'.2.1] at hK
  rcases hT' : haxToLowCTKT A tl fl t with _ | ⟨tC, xt⟩
  · rw [hT'] at hK; cases hK
  rcases hE : haxToLowCTKT A tl fl e with _ | ⟨eC, xe⟩
  · rw [hT', hE] at hK; cases hK
  rw [hT', hE] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  cases hvv : env v with
  | none =>
    rw [denote'_ifThenElse_var_run_none bi fuel v t e env hvv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  | some w =>
    obtain ⟨hsw, hdw⟩ := envAgreesT_scalar hag hok'.1 hvsc hvv
    rcases hsw.bool_or with ⟨bb, rfl⟩ | ⟨hnb, hwcf⟩
    · rw [denote'_ifThenElse_var_run_bool bi fuel v t e env bb hvv] at hrun
      rw [valueToScalar_bool, Option.some.injEq] at hdw
      cases bb with
      | true =>
        simp only [if_true] at hrun hdw
        obtain ⟨rs', hex, hag', hx⟩ := iht tl fl fuel env env' o rs tC xt hok'.2.2.1 hfl hT' hrun
          hval hag hret
        exact ⟨rs', RustExec.ifTrue _ _ _ _ _ 1 hdw.symm (by decide) hex, hag',
          fun h => hx (by simp at h; exact h.1)⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at hrun hdw
        obtain ⟨rs', hex, hag', hx⟩ := ihe tl fl fuel env env' o rs eC xe hok'.2.2.2 hfl hE hrun
          hval hag hret
        exact ⟨rs', RustExec.ifFalse _ _ _ _ _ hdw.symm hex, hag',
          fun h => hx (by simp at h; exact h.2)⟩
    · rw [denote'_ifThenElse_var_run_nonbool bi fuel v t e env w hvv hnb hwcf] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h

/-- The scrutinee of a `match` `M` that runs to a value: when a call `f(args)` on argument
    variables that does not run to a value makes `M` end in the same outcome, a run of `M`
    ending in a value has the call on the values `vals` of the arguments return `vRes`,
    leaving the environment unchanged. -/
theorem optMatch_app_inv {M : ImpExpr} {f : String} {args : List ImpExpr} {fuel : Nat}
    {env env' : Env} {o : Outcome} (hargs : exitArgsOk args = true)
    (hnonval : ∀ env1 o, denote' bi fuel (.app f args) env = (o, env1) →
      (∀ v, o ≠ .val v) → denote' bi fuel M env = (o, env1))
    (hrun : denote' bi fuel M env = (o, env')) (hval : ∃ v, o = .val v) :
    ∃ vals vRes, List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals ∧
      bi f vals = some vRes ∧ denote' bi fuel (.app f args) env = (.val vRes, env) := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel args).run env with ⟨oa, e1⟩
  obtain ⟨he1, hF⟩ := denoteArgs'_vars_inv bi fuel args hargs env e1 oa hA
  subst e1
  have happ := denote'_app_run bi fuel f args env
  rw [hA] at happ
  have hbad : ∀ (m : String), denote' bi fuel (.app f args) env = (.err m, env) → False :=
    fun m h => by
      rw [hnonval env _ h (fun v hv => by cases hv)] at hrun
      obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h'⟩ := hval; cases h'
  rcases oa with _ | vals
  · exact (hbad _ happ).elim
  cases hbi : bi f vals with
  | none =>
    simp only [hbi] at happ
    exact (hbad _ happ).elim
  | some vRes =>
    simp only [hbi] at happ
    exact ⟨vals, vRes, hF vals rfl, hbi, happ⟩

/-- The payload binding `bindP` of `optHeadT`: from a state holding in the slot
    `exitOptPayName` an output related to the payload `w` by `optPayloadRel`, it runs to a
    state agreeing with the environment extended by `p ↦ w`, with the exit flag `0`. -/
theorem optBind_sim {env : Env} {rs2 : RustState} {p : String} {tty : TowerType}
    {bindP : LowCT} {w : Value} {payOut : RustVal tty} (hpn : exitReserved p = false)
    (hbind : (A.lookup p = none ∧ tty = .TU64 ∧
        bindP = .RScalarSetExpr p (.SLimb exitOptPayName 0)) ∨
      (A.lookup p = some tty ∧ tty ≠ .TU64 ∧ bindP = .RCopy ⟨p, tty⟩ ⟨exitOptPayName, tty⟩))
    (hwcf : w.isControlFlow = false)
    (hpay2 : rs2.rsTower exitOptPayName = some ⟨tty, payOut⟩)
    (hrel : optPayloadRel br tty w payOut) (hag2 : envAgreesT br A env rs2)
    (hret2 : rs2.rsScalar exitRetName = 0) :
    ∃ rs3, RustExec N leafSpec bindP rs2 rs3 ∧
      envAgreesT br A (env.extend p w) rs3 ∧ rs3.rsScalar exitRetName = 0 := by
  rcases hbind with ⟨hpA, rfl, rfl⟩ | ⟨hpA, htu, rfl⟩
  · simp only [optPayloadRel, if_true] at hrel
    have hev : (SExpr.SLimb exitOptPayName 0).evalState rs2 = towerLimb payOut 0 := by
      simp only [SExpr.evalState, CatCrypt.Crypto.Jasmin.LowCT.rsTowerLimb, hpay2]
    have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) p
      (.SLimb exitOptPayName 0) rs2
    rw [hev] at hset
    exact ⟨_, hset, envAgreesT_extend hpn hpA hrel.1 hrel.2 hag2, ret_setScalar hpn _ hret2⟩
  · simp only [optPayloadRel, if_neg htu] at hrel
    exact ⟨rsSetTower rs2 p ⟨tty, payOut⟩,
      RustExec.copy ⟨p, tty⟩ ⟨exitOptPayName, tty⟩ rs2 rfl payOut
        (locatedLookup_of_rsTower rs2 exitOptPayName tty payOut hpay2),
      envAgreesT_extend_tower hpn hpA hwcf hrel hag2, hret2⟩

/-- **A `match` on the `Option` returned by a call**, for either order of its two arms `M`:
    the call of `optHeadT`, then the `Some` arm with the payload bound or the `None` arm by
    the tag. -/
theorem exitSimTy_optMatch (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    (M : ImpExpr) (f : String) (args : List ImpExpr) (p : String) (t e : ImpExpr)
    (hOk : ∀ tl il, exitSimOkT A R tl il M = (!exitReserved p && exitArgsOk args &&
      (optHeadT A f args p).isSome && exitSimOkT A R tl il t && exitSimOkT A R tl il e))
    (hKM : ∀ tl fl, haxToLowCTKT A tl fl M =
      match optHeadT A f args p, haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (callC, bindP), some (tC, xt), some (eC, xe) =>
          some (.RSeq callC (.RIfNz exitOptTagS (.RSeq bindP tC) eC), xt || xe)
      | _, _, _ => none)
    (hsome : ∀ fuel env env1 w, denote' bi fuel (.app f args) env = (.val (.option (some w)), env1) →
      denote' bi fuel M env = denote' bi fuel t (env1.extend p w))
    (hnone : ∀ fuel env env1, denote' bi fuel (.app f args) env = (.val (.option none), env1) →
      denote' bi fuel M env = denote' bi fuel e env1)
    (hnonval : ∀ fuel env env1 o, denote' bi fuel (.app f args) env = (o, env1) →
      (∀ v, o ≠ .val v) → denote' bi fuel M env = (o, env1))
    (iht : ExitSimTy bi N leafSpec br A R t) (ihe : ExitSimTy bi N leafSpec br A R e) :
    ExitSimTy bi N leafSpec br A R M := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  change denote' bi fuel M env = (o, env') at hrun
  rw [hOk] at hok
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hpn, hargs⟩, -⟩, hokt⟩, hoke⟩ := hok
  rw [hKM] at hK
  rcases hk : optHeadT A f args p with _ | ⟨callC, bindP⟩
  · rw [hk] at hK; cases hK
  rcases hT' : haxToLowCTKT A tl fl t with _ | ⟨tC, xt⟩
  · rw [hk, hT'] at hK; cases hK
  rcases hE : haxToLowCTKT A tl fl e with _ | ⟨eC, xe⟩
  · rw [hk, hT', hE] at hK; cases hK
  rw [hk, hT', hE] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  obtain ⟨tty, ctx, ls, hsf, hfi, hfu, hfl', hfr, hDO, hm, rfl, hbind⟩ := optHeadT_some A hk
  obtain ⟨vals, vRes, hF, hbi, happ⟩ :=
    optMatch_app_inv bi hargs (hnonval fuel env) hrun hval
  obtain ⟨o', rs2, rfl, hexC, hag2, hret2, htagS, hpay⟩ :=
    optCall_sim hL hm (hL.optD f tty hDO hsf hfi hfu hfl' hfr) hargs hF hbi hag
  rw [hret] at hret2
  rcases o' with _ | w
  · rw [hnone fuel env env happ] at hrun
    obtain ⟨rs', hex, hagE, hx⟩ := ihe tl fl fuel env env' o rs2 eC xe hoke hfl hE hrun hval
      hag2 hret2
    exact ⟨rs', RustExec.seq _ _ _ _ _ hexC (RustExec.ifFalse _ _ _ _ _ (by simpa using htagS)
      hex), hagE, fun h => hx (by simp at h; exact h.2)⟩
  · rw [hsome fuel env env w happ] at hrun
    obtain ⟨hwcf, payOut, hpay2, hrel⟩ := hpay w rfl
    obtain ⟨rs3, hexB, hag3, hret3⟩ :=
      optBind_sim N leafSpec br A hpn hbind hwcf hpay2 hrel hag2 hret2
    obtain ⟨rs', hex, hagE, hx⟩ := iht tl fl fuel _ env' o rs3 tC xt hokt hfl hT' hrun hval
      hag3 hret3
    exact ⟨rs', RustExec.seq _ _ _ _ _ hexC (RustExec.ifTrue _ _ _ _ _ 1 (by simpa using htagS)
      (by decide) (RustExec.seq _ _ _ _ _ hexB hex)), hagE,
      fun h => hx (by simp at h; exact h.1)⟩

theorem exitSimTy_typeAscription (e : ImpExpr) (ty : String)
    (ih : ExitSimTy bi N leafSpec br A R e) :
    ExitSimTy bi N leafSpec br A R (.typeAscription e ty) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : exitSimOkT A R tl fl.isSome e = true := by
    cases tl <;> cases fl <;> simpa only [exitSimOkT] using hok
  rw [haxToLowCTKT_typeAscription_eq] at hK
  have hrun' : (denote' bi fuel e).run env = (o, env') := by
    rw [← hrun]; simp only [StateT.run, denote']
  exact ih tl fl fuel env env' o rs c xb hok' hfl hK hrun' hval hag hret

/-- An expression outside the fragment simulates vacuously. -/
theorem exitSimTy_of_not_ok (e : ImpExpr) (h : ∀ tl il, exitSimOkT A R tl il e = false) :
    ExitSimTy bi N leafSpec br A R e := by
  intro tl fl _ _ _ _ _ _ _ hok
  rw [h] at hok; cases hok

/-! ## §14  The loops -/

/-- **The `whileFoldReturn` loop**, by induction on fuel, as `exitLoop_sim` under the
    placement `A`: the guard is a scalar name. -/
theorem exitLoopT_sim (run c : String) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hc : exitReserved c = false) (hcs : A.lookup c = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      (_root_.Hax.denoteWhile'Return bi fuel (.var c) body).run env = (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      rs.rsScalar run = rs.rsScalar c →
      ∃ rs', RustExec N leafSpec (.RWhileNz run (.RSeq bC (loopTail run c))) rs rs' ∧
        envAgreesExitT br A R false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hcr : c ≠ run := ne_of_reserved hc (exitReserved_of_runSlot hslot)
  have hresv := exitReserved_of_runSlot hslot
  intro fuel
  induction fuel with
  | zero =>
    intro env env' o rs h hval _ _ _
    rw [denoteWhile'Return_zero_run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨_, h⟩ := hval; cases h
  | succ n IH =>
    intro env env' o rs h hval hag hret hrc
    cases hvc : env c with
    | none =>
      obtain ⟨msg, h'⟩ := denoteWhile'Return_succ_none bi n c body env hvc
      rw [h'] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | some w =>
      obtain ⟨hsw, hdw⟩ := envAgreesT_scalar hag hc hcs hvc
      rcases hsw.bool_or with ⟨bb, rfl⟩ | ⟨hnb, hwcf⟩
      swap
      · rw [denoteWhile'Return_succ_nonbool bi n c body env w hvc hnb hwcf] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h
      rw [valueToScalar_bool, Option.some.injEq] at hdw
      cases bb with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hdw
        rw [denoteWhile'Return_succ_false bi n c body env hvc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨rs, RustExec.whileFalse _ _ _ (by rw [hrc, ← hdw]),
          (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
      | true =>
        simp only [if_true] at hdw
        have hrun1 : rs.rsScalar run = 1 := by rw [hrc, ← hdw]
        rcases hb : (denote' bi (n + 1) body).run env with ⟨ob, e2⟩
        cases ob with
        | val vb =>
          obtain ⟨rs1, hex1, hag1, -⟩ :=
            ihb false (some run) (n + 1) env e2 (.val vb) rs bC xb hokB hctx hKB hb
              ⟨vb, rfl⟩ hag hret
          cases hcf : vb.isControlFlow with
          | false =>
            obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
            rw [denoteWhile'Return_succ_iterate bi n c body env e2 vb hvc hb hcf] at h
            have htail : RustExec N leafSpec (loopTail run c) rs1
                (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              RustExec.ifFalse _ _ _ _ _ h1 (RustExec.scalarSetExpr _ _ _)
            have hag2 : envAgreesT br A e2 (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              envAgreesT_set_reserved _ hresv hagE
            have hret2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar exitRetName = 0 := by
              rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
            have hrc2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar run =
                (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar c := by
              simp [rsScalar_rsSetScalar, hcr]
            obtain ⟨rs', hexL, hagL⟩ := IH e2 env' o _ h hval hag2 hret2 hrc2
            exact ⟨rs', RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
              (RustExec.seq _ _ _ _ _ hex1 htail) hexL, hagL⟩
          | true =>
            cases vb with
            | controlFlow kk ww =>
              cases kk with
              | false => exact (show False from hag1).elim
              | true =>
                obtain ⟨h1, hw, hagE⟩ := hag1
                have hwcf : ww.isControlFlow = false := by
                  cases ww <;> first | rfl | simp [valueToScalar] at hw
                rw [denoteWhile'Return_succ_exit bi n c body env e2 ww hvc hb hwcf] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                refine ⟨rsSetScalar rs1 run 0,
                  RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
                    (RustExec.seq _ _ _ _ _ hex1
                      (RustExec.ifTrue _ _ _ _ _ 1 h1 (by decide) (RustExec.scalarSet _ _ _)))
                    (RustExec.whileFalse _ _ _ (by simp)), ?_, ?_, ?_⟩
                · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
                · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_val hslot).symm]; exact hw
                · exact envAgreesT_set_reserved _ hresv hagE
            | _ => simp at hcf
        | _ =>
          rw [denoteWhile'Return_succ_nonval bi n c body env e2 _ hvc hb
            (fun v h => by cases h)] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          obtain ⟨_, h⟩ := hval; cases h

theorem exitSimTy_whileFoldReturn (c : String) (body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.whileFoldReturn (.var c) body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : exitReserved c = false ∧ exitSc A c = true ∧
        exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have hcs : A.lookup c = none := by simpa [exitSc] using hok'.2.1
    rw [haxToLowCTKT_whileFoldReturn_eq _ _ _ _ hok'.2.1] at hK
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK; cases hK
    rw [hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_whileFoldReturn_run] at hrun
    have hslot := runSlot_exitRunName hfl
    have hresv := exitReserved_of_runSlot hslot
    have hcr : c ≠ exitRunName fl := ne_of_reserved hok'.1 hresv
    let rs0 := rsSetScalar (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0)
      (exitRunName fl) 0
    let rs1 := rsSetScalar rs0 (exitRunName fl) (rs0.rsScalar c)
    have hag1 : envAgreesT br A env rs1 :=
      envAgreesT_set_reserved _ hresv (envAgreesT_set_reserved _ hresv
        (envAgreesT_set_reserved _ exitReserved_val
          (envAgreesT_set_reserved _ exitReserved_ret hag)))
    have hret1 : rs1.rsScalar exitRetName = 0 := by
      simp [rs1, rs0, rsScalar_rsSetScalar, (runSlot_ne_ret hslot).symm, exitRetName_ne_val]
    have hrc1 : rs1.rsScalar (exitRunName fl) = rs1.rsScalar c := by
      simp [rs1, rsScalar_rsSetScalar, hcr]
    obtain ⟨rs', hexL, hagL⟩ :=
      exitLoopT_sim bi N leafSpec br A R (exitRunName fl) c body bC x ihb hslot hok'.1 hcs
        hok'.2.2 hB fuel env env' o rs1 hrun hval hag1 hret1 hrc1
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
      (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) hexL))),
      hagL, fun h => by cases h⟩

/-- After an exit, the guarded trips preserve the exit agreement. -/
theorem exitedTripsT (run : String) (B : LowCT) (hslot : exitRunSlot run = true) :
    ∀ (d k : Nat) (rs : RustState) (w : Value) (env : Env),
      envAgreesExitT br A R false (.val (.controlFlow true w)) env rs →
      ∃ rs', TripsFrom N leafSpec run (exitGuard B) k d rs rs' ∧
        envAgreesExitT br A R false (.val (.controlFlow true w)) env rs' := by
  intro d
  induction d with
  | zero => intro k rs w env hag; exact ⟨rs, rfl, hag⟩
  | succ d IH =>
    intro k rs w env hag
    obtain ⟨h1, hw, hagO⟩ := hag
    have h1' : (rsSetScalar rs run k).rsScalar exitRetName = 1 := by
      rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm]; exact h1
    have hag' : envAgreesExitT br A R false (.val (.controlFlow true w)) env
        (rsSetScalar rs run k) :=
      ⟨h1', by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_val hslot).symm]; exact hw,
        envAgreesT_set_reserved _ (exitReserved_of_runSlot hslot) hagO⟩
    obtain ⟨rs', hT, hagL⟩ := IH (k + 1) (rsSetScalar rs run k) w env hag'
    exact ⟨rs', ⟨rsSetScalar rs run k, exitGuard_exited N leafSpec B _ h1', hT⟩, hagL⟩

/-- The state at the start of trip `j` of a counted loop from `lo`: the trip counter
    `run` holds `j` and the counter `i` holds `lo + j`. -/
theorem tripStart_agree {env : Env} {rs : RustState} {run i : String}
    (hresv : exitReserved run = true) (hi_ : exitReserved i = false) (his : A.lookup i = none)
    (j c : Nat) (hc : c < 2 ^ 64) (hag : envAgreesT br A env rs) :
    envAgreesT br A (env.extend i (.int (c : Int))) (rsSetScalar (rsSetScalar rs run j) i c) :=
  envAgreesT_extend hi_ his ⟨by omega, by omega⟩ (valueToScalar_int _)
    (envAgreesT_set_reserved _ hresv hag)

/-- **The `forFoldReturn` trips**, as `exitForTrips_sim` under the placement `A`. -/
theorem exitForTripsT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoop'Return bi fuel i ((lo + j : Nat) : Int) hi body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTrip run i lo bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoop'Return_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : ((lo + j : Nat) : Int) < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop'Return_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT := tripStart_agree A (br := br) hresv hi_ his j (lo + j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (lo + j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (lo + j)) r →
          RustExec N leafSpec (exitForTrip run i lo bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SAdd (.SVar run) (.SLit lo)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (lo + j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
          rw [Nat.add_comm]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int ((lo + j : Nat) : Int)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoop'Return_succ_iterate bi n i _ hi body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoop'Return bi n i ((lo + (j + 1) : Nat) : Int) hi
              body).run e2 = (o, env') := by
            rw [show ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 by push_cast; ring]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoop'Return_succ_exit bi n i _ hi body env e2 ww hlt hb hwcf] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoop'Return_succ_nonval bi n i _ hi body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

/-- The `forFoldReturn` loop with a variable upper bound, as `exitForLoopRt_sim`. -/
theorem exitForLoopRtT_sim (run i h : String) (lo : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hh_ : exitReserved h = false)
    (hhs : A.lookup h = none) (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFoldReturn i (.lit (.int lo)) (.var h) body)).run env =
      (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (exitForLoopRt run i lo h bC) rs rs' ∧
      envAgreesExitT br A R false o env' rs' := by
  obtain ⟨v, H, hhv, hvs, hH, hrun⟩ :=
    denote'_forFoldReturn_var_scalarN bi fuel i h lo body env env' o hrun hval
      (fun v hv => (envAgreesT_scalar hag hh_ hhs hv).1)
  have hdec : H = rs.rsScalar h := by
    have hd := (envAgreesT_scalar hag hh_ hhs hhv).2
    rw [hvs] at hd
    exact Option.some.inj hd
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hH0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar h = H := by
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hh_ exitReserved_val), rsScalar_rsSetScalar,
      if_neg (ne_of_reserved hh_ exitReserved_ret), hdec]
  have hrun0 : (_root_.Hax.denoteForLoop'Return bi fuel i ((lo + 0 : Nat) : Int) H body).run env =
      (o, env') := by
    rw [Nat.add_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    exitForTripsT_sim bi N leafSpec br A R run i lo H body bC xb ihb hslot hi_ his (by omega)
      hokB hKB (H - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (H - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  refine ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
    (RustExec.forRuntime _ _ _ _ _ ?_)), hagL⟩
  simpa only [SExpr.evalState, hH0] using hFor

/-- **The `forFoldReturn` trips with a lower bound read at run time**: as
    `exitForTripsT_sim`, over the trip `exitForTripV` whose lower bound `loE` reads `lo` from
    every state agreeing with an environment of the invariant `Keep`, which each trip of the
    body keeps. -/
theorem exitForTripsVT_sim (run i : String) (loE : SExpr) (lo hi : Nat) (body : ImpExpr)
    (bC : LowCT) (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (his : A.lookup i = none)
    (hhi : hi ≤ 2 ^ 64) (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) (Keep : Env → Prop)
    (hkeep : ∀ fuel env e2 w (k : Int), Keep env →
      (denote' bi fuel body).run (env.extend i (.int k)) = (.val w, e2) → Keep e2)
    (hloE : ∀ env rs j, Keep env → envAgreesT br A env rs →
      loE.evalState (rsSetScalar (rsSetScalar rs run j) i 0) = lo) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoop'Return bi fuel i ((lo + j : Nat) : Int) hi body).run env =
        (o, env') →
      (∃ v, o = .val v) → Keep env → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTripV run i loE bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval _ hag hret
    rw [denoteForLoop'Return_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hK hag hret
    have hlt : ((lo + j : Nat) : Int) < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop'Return_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT := tripStart_agree A (br := br) hresv hi_ his j (lo + j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (lo + j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (lo + j)) r →
          RustExec N leafSpec (exitForTripV run i loE bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SAdd (.SVar run) loE).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (lo + j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, hloE env rs j hK hag, rsScalar_rsSetScalar, if_neg hir.symm,
            if_true]
          rw [Nat.add_comm]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int ((lo + j : Nat) : Int)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        have hK2 := hkeep (n + 1) env e2 vb _ hK hb
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoop'Return_succ_iterate bi n i _ hi body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoop'Return bi n i ((lo + (j + 1) : Nat) : Int) hi
              body).run e2 = (o, env') := by
            rw [show ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 by push_cast; ring]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hK2 hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoop'Return_succ_exit bi n i _ hi body env e2 ww hlt hb hwcf] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoop'Return_succ_nonval bi n i _ hi body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

/-- **The `forFoldReturn` loop with bounds read at run time** (`exitForLoopV`, bounds of
    `forBoundsV`): the entry state agrees with the environment, the trip count is the
    difference of the decoded bounds, and a variable lower bound keeps its value over the
    trips. -/
theorem exitForLoopVT_sim (run i : String) (lo hi body : ImpExpr) (loE hiE : SExpr)
    (bC : LowCT) (xb : Bool) (hS : ScalarOpsSoundT bi) (ihb : ExitSimTy bi N leafSpec br A R body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (his : A.lookup i = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (hlo : loBoundSE A i body lo = some loE) (hhi : boundSE A hi = some hiE)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFoldReturn i lo hi body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (exitForLoopV run i loE hiE bC) rs rs' ∧
      envAgreesExitT br A R false o env' rs' := by
  let rs0 := rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0
  have hag0 : envAgreesT br A env rs0 :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : rs0.rsScalar exitRetName = 0 := by
    simp only [rs0]
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hloS := fun {o : Outcome} {e : Env} (h : (denote' bi fuel lo).run env = (o, e)) =>
    boundSE_sim hS hag0 fuel lo (loBoundSE_boundSE hlo) h
  have hhiS := fun {o : Outcome} {e : Env} (h : (denote' bi fuel hi).run env = (o, e)) =>
    boundSE_sim hS hag0 fuel hi hhi h
  obtain ⟨hrunL, hH, vlo, -, hvlo, -⟩ := denote'_forFoldReturn_pure_bounds hloS hhiS hrun hval
  obtain ⟨-, hvl⟩ := hloS hvlo
  obtain ⟨-, hdl⟩ := hvl vlo rfl
  have hvx : ∀ x, lo = .var x → env x = some vlo := by
    intro x hx
    subst hx
    rw [_root_.Hax.ContinueFlag.var_run] at hvlo
    cases hex : env x with
    | none => rw [hex] at hvlo; cases hvlo
    | some w => rw [hex] at hvlo; cases hvlo; rfl
  have hLit : ∀ k, loE = .SLit k → k = loE.evalState rs0 := by
    intro k hk; subst hk; rfl
  have hrun0 : (_root_.Hax.denoteForLoop'Return bi fuel i
      ((loE.evalState rs0 + 0 : Nat) : Int) (hiE.evalState rs0) body).run env = (o, env') := by
    rw [Nat.add_zero]; exact hrunL
  obtain ⟨rs', hT, hagL⟩ :=
    exitForTripsVT_sim bi N leafSpec br A R run i loE (loE.evalState rs0) (hiE.evalState rs0) body
      bC xb ihb hslot hi_ his hH.le hokB hKB (fun e => ∀ x, loE = .SVar x → e x = env x)
      (fun fuel e1 e2 w k hK hb => loBound_keep hlo env fuel e1 e2 w k hK hb)
      (loBound_read hlo hslot hvx hdl hLit)
      (hiE.evalState rs0 - loE.evalState rs0) 0 fuel env env' o rs0 (by omega) hrun0 hval
      (fun _ _ => rfl) hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ _ 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
    (RustExec.forRuntime _ _ _ _ _ (by simpa only [SExpr.evalState] using hFor))), hagL⟩

theorem exitSimTy_forFoldReturn (hS : ScalarOpsSoundT bi) (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFoldReturn i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : forBoundsOkT A i body lo hi = true ∧
        exitReserved i = false ∧ exitSc A i = true ∧ exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
    have hslot := runSlot_exitRunName hfl
    rw [haxToLowCTKT_forFoldReturn_eq _ _ _ _ _ _
      (by simp only [hok'.2.2.1, exitScRt_of_okT hok'.1, Bool.and_self])] at hK
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
        rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
    rw [hB] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
      · rw [hFB, hRt] at hK
        obtain ⟨⟨loE, hiE⟩, hV, hKe⟩ := Option.map_eq_some_iff.mp hK
        simp only [Prod.mk.injEq] at hKe
        obtain ⟨rfl, rfl⟩ := hKe
        obtain ⟨hlo, hhi⟩ := forBoundsV_some hV
        obtain ⟨rs', hex, hagL⟩ :=
          exitForLoopVT_sim bi N leafSpec br A R (exitRunName fl) i lo hi body loE hiE bC x hS ihb
            hslot hok'.2.1 his hok'.2.2.2 hB hlo hhi fuel env env' o rs hrun hval hag
        exact ⟨rs', hex, hagL, fun h => by cases h⟩
      rw [hFB, hRt] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      have hh : exitReserved h = false ∧ exitSc A h = true := forBoundsOkT_rt hok'.1 hRt
      have hhs : A.lookup h = none := by simpa [exitSc] using hh.2
      obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
      obtain ⟨rs', hex, hagL⟩ :=
        exitForLoopRtT_sim bi N leafSpec br A R (exitRunName fl) i h l body bC x ihb hslot
          hok'.2.1 his hh.1 hhs hok'.2.2.2 hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun h => by cases h⟩
    rw [hFB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rw [denote'_forFoldReturn_lit_run] at hrun
    have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
      envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
    have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
        exitRetName = 0 := by
      rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
    have hrun0 : (_root_.Hax.denoteForLoop'Return bi fuel i ((l + 0 : Nat) : Int) h body).run env =
        (o, env') := by
      rw [Nat.add_zero]; exact hrun
    obtain ⟨rs', hT, hagL⟩ :=
      exitForTripsT_sim bi N leafSpec br A R (exitRunName fl) i l h body bC x ihb hslot
        hok'.2.1 his hh hok'.2.2.2 hB (h - l) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
    have hFor := rustExec_rFor_of_tripsFrom N leafSpec (exitRunName fl) _ (h - l) 0 _ _ rs'
      (RustExec.forZero _ _ _) hT
    rw [Nat.zero_add] at hFor
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor), hagL,
      fun h => by cases h⟩

/-- **The `forFoldRevReturn` trips**, as `exitForTripsRev_sim` under the placement `A`. -/
theorem exitForTripsRevT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoopRev'Return bi fuel i lo ((hi - j : Nat) : Int) body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTripRev run i hi bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoopRev'Return_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : (lo : Int) < ((hi - j : Nat) : Int) := by omega
    have hc : ((hi - j : Nat) : Int) - 1 = ((hi - 1 - j : Nat) : Int) := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoopRev'Return_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT : envAgreesT br A (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
          (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) := by
        rw [hc]
        exact tripStart_agree br A hresv hi_ his j (hi - 1 - j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) r →
          RustExec N leafSpec (exitForTripRev run i hi bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SSub (.SLit (hi - 1)) (.SVar run)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoopRev'Return_succ_iterate bi n i lo _ body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoopRev'Return bi n i lo ((hi - (j + 1) : Nat) : Int)
              body).run e2 = (o, env') := by
            rw [show ((hi - (j + 1) : Nat) : Int) = ((hi - j : Nat) : Int) - 1 by omega]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoopRev'Return_succ_exit bi n i lo _ body env e2 ww hlt hb hwcf] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoopRev'Return_succ_nonval bi n i lo _ body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem exitSimTy_forFoldRevReturn (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFoldRevReturn i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
        exitSc A i = true ∧ exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
    rw [haxToLowCTKT_forFoldRevReturn_eq _ _ _ _ _ _ hok'.2.2.1] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rw [hFB] at hok'; cases hok'.1
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hFB, hB] at hK; cases hK
    rw [hFB, hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_forFoldRevReturn_lit_run] at hrun
    have hslot := runSlot_exitRunName hfl
    have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
      envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
    have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
        exitRetName = 0 := by
      rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
    have hrun0 : (_root_.Hax.denoteForLoopRev'Return bi fuel i l ((h - 0 : Nat) : Int) body).run
        env = (o, env') := by
      rw [Nat.sub_zero]; exact hrun
    obtain ⟨rs', hT, hagL⟩ :=
      exitForTripsRevT_sim bi N leafSpec br A R (exitRunName fl) i l h body bC x ihb hslot
        hok'.2.1 his hh hok'.2.2.2 hB (h - l) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
    have hFor := rustExec_rFor_of_tripsFrom N leafSpec (exitRunName fl) _ (h - l) 0 _ _ rs'
      (RustExec.forZero _ _ _) hT
    rw [Nat.zero_add] at hFor
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor), hagL,
      fun h => by cases h⟩

/-- **The `forFold` trips of a loop that may break**, as `breakForTrips_sim` under the
    placement `A`. -/
theorem breakForTripsT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoop' bi fuel i ((lo + j : Nat) : Int) hi body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTrip run i lo bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' (rsSetScalar rs' exitRetName 0) := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoop'_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, envAgreesExitT_reset hag rfl⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : ((lo + j : Nat) : Int) < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop'_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT := tripStart_agree br A hresv hi_ his j (lo + j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (lo + j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (lo + j)) r →
          RustExec N leafSpec (exitForTrip run i lo bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SAdd (.SVar run) (.SLit lo)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (lo + j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
          rw [Nat.add_comm]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int ((lo + j : Nat) : Int)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoop'_succ_iterate bi n i _ hi body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoop' bi n i ((lo + (j + 1) : Nat) : Int) hi
              body).run e2 = (o, env') := by
            rw [show ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 by push_cast; ring]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoop'_succ_break bi n i _ hi body env e2 ww hlt hb] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, envAgreesExitT_reset hagL.2.2 hwcf⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoop'_succ_nonval bi n i _ hi body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem breakForLoopT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitForLoop run i lo hi bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  rw [denote'_forFold_lit_run] at hrun
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hrun0 : (_root_.Hax.denoteForLoop' bi fuel i ((lo + 0 : Nat) : Int) hi body).run env =
      (o, env') := by
    rw [Nat.add_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    breakForTripsT_sim bi N leafSpec br A R run i lo hi body bC xb ihb hslot hi_ his hhi hokB hKB
      (hi - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (hi - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  exact ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor))
    (RustExec.scalarSet _ _ _), hagL, by simp [rsScalar_rsSetScalar]⟩

theorem breakForLoopRtT_sim (run i h : String) (lo : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hh_ : exitReserved h = false)
    (hhs : A.lookup h = none) (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.var h) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitForLoopRt run i lo h bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  obtain ⟨v, H, hhv, hvs, hH, hrun⟩ :=
    denote'_forFold_var_scalarN bi fuel i h lo body env env' o hrun hval
      (fun v hv => (envAgreesT_scalar hag hh_ hhs hv).1)
  have hdec : H = rs.rsScalar h := by
    have hd := (envAgreesT_scalar hag hh_ hhs hhv).2
    rw [hvs] at hd
    exact Option.some.inj hd
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hH0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar h = H := by
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hh_ exitReserved_val), rsScalar_rsSetScalar,
      if_neg (ne_of_reserved hh_ exitReserved_ret), hdec]
  have hrun0 : (_root_.Hax.denoteForLoop' bi fuel i ((lo + 0 : Nat) : Int) H body).run env =
      (o, env') := by
    rw [Nat.add_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    breakForTripsT_sim bi N leafSpec br A R run i lo H body bC xb ihb hslot hi_ his (by omega)
      hokB hKB (H - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (H - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  refine ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
    (RustExec.forRuntime _ _ _ _ _ ?_))) (RustExec.scalarSet _ _ _), hagL,
    by simp [rsScalar_rsSetScalar]⟩
  simpa only [SExpr.evalState, hH0] using hFor

/-- **The `forFold` trips of a loop that may break, with a lower bound read at run time**:
    as `breakForTripsT_sim`, over the trip `exitForTripV` under the invariant `Keep` of
    `exitForTripsVT_sim`. -/
theorem breakForTripsVT_sim (run i : String) (loE : SExpr) (lo hi : Nat) (body : ImpExpr)
    (bC : LowCT) (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (his : A.lookup i = none)
    (hhi : hi ≤ 2 ^ 64) (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) (Keep : Env → Prop)
    (hkeep : ∀ fuel env e2 w (k : Int), Keep env →
      (denote' bi fuel body).run (env.extend i (.int k)) = (.val w, e2) → Keep e2)
    (hloE : ∀ env rs j, Keep env → envAgreesT br A env rs →
      loE.evalState (rsSetScalar (rsSetScalar rs run j) i 0) = lo) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoop' bi fuel i ((lo + j : Nat) : Int) hi body).run env =
        (o, env') →
      (∃ v, o = .val v) → Keep env → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTripV run i loE bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' (rsSetScalar rs' exitRetName 0) := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval _ hag hret
    rw [denoteForLoop'_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, envAgreesExitT_reset hag rfl⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hK hag hret
    have hlt : ((lo + j : Nat) : Int) < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop'_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT := tripStart_agree br A hresv hi_ his j (lo + j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (lo + j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (lo + j)) r →
          RustExec N leafSpec (exitForTripV run i loE bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SAdd (.SVar run) loE).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (lo + j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, hloE env rs j hK hag, rsScalar_rsSetScalar, if_neg hir.symm,
            if_true]
          rw [Nat.add_comm]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int ((lo + j : Nat) : Int)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        have hK2 := hkeep (n + 1) env e2 vb _ hK hb
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoop'_succ_iterate bi n i _ hi body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoop' bi n i ((lo + (j + 1) : Nat) : Int) hi
              body).run e2 = (o, env') := by
            rw [show ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 by push_cast; ring]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hK2 hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoop'_succ_break bi n i _ hi body env e2 ww hlt hb] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, envAgreesExitT_reset hagL.2.2 hwcf⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoop'_succ_nonval bi n i _ hi body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

/-- **The `forFold` loop that may break, with bounds read at run time**
    (`breakLoop (exitForLoopV …)`), as `exitForLoopVT_sim`. -/
theorem breakForLoopVT_sim (run i : String) (lo hi body : ImpExpr) (loE hiE : SExpr)
    (bC : LowCT) (xb : Bool) (hS : ScalarOpsSoundT bi) (ihb : ExitSimTy bi N leafSpec br A R body)
    (hslot : exitRunSlot run = true) (hi_ : exitReserved i = false) (his : A.lookup i = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (hlo : loBoundSE A i body lo = some loE) (hhi : boundSE A hi = some hiE)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFold i lo hi body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitForLoopV run i loE hiE bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  let rs0 := rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0
  have hag0 : envAgreesT br A env rs0 :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : rs0.rsScalar exitRetName = 0 := by
    simp only [rs0]
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hloS := fun {o : Outcome} {e : Env} (h : (denote' bi fuel lo).run env = (o, e)) =>
    boundSE_sim hS hag0 fuel lo (loBoundSE_boundSE hlo) h
  have hhiS := fun {o : Outcome} {e : Env} (h : (denote' bi fuel hi).run env = (o, e)) =>
    boundSE_sim hS hag0 fuel hi hhi h
  obtain ⟨hrunL, hH, vlo, -, hvlo, -⟩ := denote'_forFold_pure_bounds hloS hhiS hrun hval
  obtain ⟨-, hvl⟩ := hloS hvlo
  obtain ⟨-, hdl⟩ := hvl vlo rfl
  have hvx : ∀ x, lo = .var x → env x = some vlo := by
    intro x hx
    subst hx
    rw [_root_.Hax.ContinueFlag.var_run] at hvlo
    cases hex : env x with
    | none => rw [hex] at hvlo; cases hvlo
    | some w => rw [hex] at hvlo; cases hvlo; rfl
  have hLit : ∀ k, loE = .SLit k → k = loE.evalState rs0 := by
    intro k hk; subst hk; rfl
  have hrun0 : (_root_.Hax.denoteForLoop' bi fuel i
      ((loE.evalState rs0 + 0 : Nat) : Int) (hiE.evalState rs0) body).run env = (o, env') := by
    rw [Nat.add_zero]; exact hrunL
  obtain ⟨rs', hT, hagL⟩ :=
    breakForTripsVT_sim bi N leafSpec br A R run i loE (loE.evalState rs0) (hiE.evalState rs0)
      body bC xb ihb hslot hi_ his hH.le hokB hKB (fun e => ∀ x, loE = .SVar x → e x = env x)
      (fun fuel e1 e2 w k hK hb => loBound_keep hlo env fuel e1 e2 w k hK hb)
      (loBound_read hlo hslot hvx hdl hLit)
      (hiE.evalState rs0 - loE.evalState rs0) 0 fuel env env' o rs0 (by omega) hrun0 hval
      (fun _ _ => rfl) hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ _ 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  refine ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
    (RustExec.forRuntime _ _ _ _ _ ?_))) (RustExec.scalarSet _ _ _), hagL,
    by simp [rsScalar_rsSetScalar]⟩
  simpa only [SExpr.evalState] using hFor

/-- **The `whileFold` trips of a loop that may break**, as `breakWhileTrips_sim` under the
    placement `A`. -/
theorem breakWhileTripsT_sim (run c : String) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hc : exitReserved c = false) (hcs : A.lookup c = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      (_root_.Hax.denoteWhile' bi fuel (.var c) body).run env = (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      rs.rsScalar run = rs.rsScalar c →
      ∃ rs', RustExec N leafSpec (.RWhileNz run (.RSeq bC (loopTail run c))) rs rs' ∧
        envAgreesExitT br A R false o env' (rsSetScalar rs' exitRetName 0) := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hcr : c ≠ run := ne_of_reserved hc (exitReserved_of_runSlot hslot)
  have hresv := exitReserved_of_runSlot hslot
  intro fuel
  induction fuel with
  | zero =>
    intro env env' o rs h hval _ _ _
    rw [denoteWhile'_zero_run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨_, h⟩ := hval; cases h
  | succ n IH =>
    intro env env' o rs h hval hag hret hrc
    cases hvc : env c with
    | none =>
      obtain ⟨msg, h'⟩ := denoteWhile'_succ_none bi n c body env hvc
      rw [h'] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | some w =>
      obtain ⟨hsw, hdw⟩ := envAgreesT_scalar hag hc hcs hvc
      rcases hsw.bool_or with ⟨bb, rfl⟩ | ⟨hnb, hwcf⟩
      swap
      · rw [denoteWhile'_succ_nonbool bi n c body env w hvc hnb hwcf] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h
      rw [valueToScalar_bool, Option.some.injEq] at hdw
      cases bb with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hdw
        rw [denoteWhile'_succ_false bi n c body env hvc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨rs, RustExec.whileFalse _ _ _ (by rw [hrc, ← hdw]), envAgreesExitT_reset hag rfl⟩
      | true =>
        simp only [if_true] at hdw
        have hrun1 : rs.rsScalar run = 1 := by rw [hrc, ← hdw]
        rcases hb : (denote' bi (n + 1) body).run env with ⟨ob, e2⟩
        cases ob with
        | val vb =>
          obtain ⟨rs1, hex1, hag1, -⟩ :=
            ihb false (some run) (n + 1) env e2 (.val vb) rs bC xb hokB hctx hKB hb
              ⟨vb, rfl⟩ hag hret
          cases hcf : vb.isControlFlow with
          | false =>
            obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
            rw [denoteWhile'_succ_iterate bi n c body env e2 vb hvc hb hcf] at h
            have htail : RustExec N leafSpec (loopTail run c) rs1
                (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              RustExec.ifFalse _ _ _ _ _ h1 (RustExec.scalarSetExpr _ _ _)
            have hag2 : envAgreesT br A e2 (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              envAgreesT_set_reserved _ hresv hagE
            have hret2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar exitRetName = 0 := by
              rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
            have hrc2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar run =
                (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar c := by
              simp [rsScalar_rsSetScalar, hcr]
            obtain ⟨rs', hexL, hagL⟩ := IH e2 env' o _ h hval hag2 hret2 hrc2
            exact ⟨rs', RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
              (RustExec.seq _ _ _ _ _ hex1 htail) hexL, hagL⟩
          | true =>
            cases vb with
            | controlFlow kk ww =>
              cases kk with
              | false => exact (show False from hag1).elim
              | true =>
                obtain ⟨h1, hw, hagE⟩ := hag1
                have hwcf : ww.isControlFlow = false := by
                  cases ww <;> first | rfl | simp [valueToScalar] at hw
                rw [denoteWhile'_succ_break bi n c body env e2 ww hvc hb] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                exact ⟨rsSetScalar rs1 run 0,
                  RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
                    (RustExec.seq _ _ _ _ _ hex1
                      (RustExec.ifTrue _ _ _ _ _ 1 h1 (by decide) (RustExec.scalarSet _ _ _)))
                    (RustExec.whileFalse _ _ _ (by simp)),
                  envAgreesExitT_reset (envAgreesT_set_reserved _ hresv hagE) hwcf⟩
            | _ => simp at hcf
        | _ =>
          rw [denoteWhile'_succ_nonval bi n c body env e2 _ hvc hb
            (fun v h => by cases h)] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          obtain ⟨_, h⟩ := hval; cases h

theorem breakWhileLoopT_sim (run c : String) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hc : exitReserved c = false) (hcs : A.lookup c = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.whileFold (.var c) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitLoop run c bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  rw [denote'_whileFold_run] at hrun
  have hresv := exitReserved_of_runSlot hslot
  have hcr : c ≠ run := ne_of_reserved hc hresv
  let rs0 := rsSetScalar (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) run 0
  let rs1 := rsSetScalar rs0 run (rs0.rsScalar c)
  have hag1 : envAgreesT br A env rs1 :=
    envAgreesT_set_reserved _ hresv (envAgreesT_set_reserved _ hresv
      (envAgreesT_set_reserved _ exitReserved_val
        (envAgreesT_set_reserved _ exitReserved_ret hag)))
  have hret1 : rs1.rsScalar exitRetName = 0 := by
    simp [rs1, rs0, rsScalar_rsSetScalar, (runSlot_ne_ret hslot).symm, exitRetName_ne_val]
  have hrc1 : rs1.rsScalar run = rs1.rsScalar c := by
    simp [rs1, rsScalar_rsSetScalar, hcr]
  obtain ⟨rs', hexL, hagL⟩ :=
    breakWhileTripsT_sim bi N leafSpec br A R run c body bC xb ihb hslot hc hcs hokB hKB
      fuel env env' o rs1 hrun hval hag1 hret1 hrc1
  exact ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
      (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) hexL))))
    (RustExec.scalarSet _ _ _), hagL, by simp [rsScalar_rsSetScalar]⟩

theorem exitSimTy_forFold (hS : ScalarOpsSoundT bi) (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFold i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOkT] at hok
    | some r =>
      have hok' : forBoundsOkT A i body lo hi = true ∧
          exitReserved i = false ∧ exitSc A i = true ∧
          exitSimOkT A R false true body = true := by
        simpa only [exitSimOkT, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
      have hokB := hok'.2.2.2
      have hslot := runSlot_exitRunName hfl
      rw [haxToLowCTKT_forFold_some_eq _ _ _ _ _ _
        (by simp only [hok'.2.2.1, exitScRt_of_okT hok'.1, Bool.and_self])] at hK
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK
        rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
          rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
      rw [hB] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
      · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
        · rw [hFB, hRt] at hK
          obtain ⟨⟨loE, hiE⟩, hV, hKe⟩ := Option.map_eq_some_iff.mp hK
          simp only [Prod.mk.injEq] at hKe
          obtain ⟨rfl, rfl⟩ := hKe
          obtain ⟨hlo, hhi⟩ := forBoundsV_some hV
          obtain ⟨rs', hex, hagL, h0⟩ :=
            breakForLoopVT_sim bi N leafSpec br A R (exitRunName (some r)) i lo hi body loE hiE
              bC x hS ihb hslot hok'.2.1 his hokB hB hlo hhi fuel env env' o rs hrun hval hag
          exact ⟨rs', hex, hagL, fun _ => h0⟩
        rw [hFB, hRt] at hK
        simp only [Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        have hh : exitReserved h = false ∧ exitSc A h = true := forBoundsOkT_rt hok'.1 hRt
        have hhs : A.lookup h = none := by simpa [exitSc] using hh.2
        obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
        obtain ⟨rs', hex, hagL, h0⟩ :=
          breakForLoopRtT_sim bi N leafSpec br A R (exitRunName (some r)) i h l body bC x ihb
            hslot hok'.2.1 his hh.1 hhs hokB hB fuel env env' o rs hrun hval hag
        exact ⟨rs', hex, hagL, fun _ => h0⟩
      rw [hFB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
      obtain ⟨rs', hex, hagL, h0⟩ :=
        breakForLoopT_sim bi N leafSpec br A R (exitRunName (some r)) i l h body bC x ihb hslot
          hok'.2.1 his hh hokB hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun _ => h0⟩

/-- **The `forFoldRev` trips of a loop that may break**: as `breakForTripsT_sim`, with the
    counter of trip `j` bound to `hi - 1 - j` (`exitForTripRev`). -/
theorem breakForTripsRevT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoopRev' bi fuel i lo ((hi - j : Nat) : Int) body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTripRev run i hi bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' (rsSetScalar rs' exitRetName 0) := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoopRev'_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, envAgreesExitT_reset hag rfl⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : (lo : Int) < ((hi - j : Nat) : Int) := by omega
    have hc : ((hi - j : Nat) : Int) - 1 = ((hi - 1 - j : Nat) : Int) := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoopRev'_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT : envAgreesT br A (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
          (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) := by
        rw [hc]
        exact tripStart_agree br A hresv hi_ his j (hi - 1 - j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) r →
          RustExec N leafSpec (exitForTripRev run i hi bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SSub (.SLit (hi - 1)) (.SVar run)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoopRev'_succ_iterate bi n i lo _ body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoopRev' bi n i lo ((hi - (j + 1) : Nat) : Int)
              body).run e2 = (o, env') := by
            rw [show ((hi - (j + 1) : Nat) : Int) = ((hi - j : Nat) : Int) - 1 by omega]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoopRev'_succ_break bi n i lo _ body env e2 ww hlt hb] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, envAgreesExitT_reset hagL.2.2 hwcf⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoopRev'_succ_nonval bi n i lo _ body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem breakForLoopRevT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitForLoopRev run i lo hi bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  rw [denote'_forFoldRev_lit_run] at hrun
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hrun0 : (_root_.Hax.denoteForLoopRev' bi fuel i lo ((hi - 0 : Nat) : Int) body).run env =
      (o, env') := by
    rw [Nat.sub_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    breakForTripsRevT_sim bi N leafSpec br A R run i lo hi body bC xb ihb hslot hi_ his hhi hokB
      hKB (hi - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (hi - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  exact ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor))
    (RustExec.scalarSet _ _ _), hagL, by simp [rsScalar_rsSetScalar]⟩

theorem exitSimTy_forFoldRev (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFoldRev i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
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
      have hslot := runSlot_exitRunName hfl
      rw [haxToLowCTKT_forFoldRev_some_eq _ _ _ _ _ _ hok'.2.2.1] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
      · rw [hFB] at hok'; cases hok'.1
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hFB, hB] at hK; cases hK
      rw [hFB, hB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
      obtain ⟨rs', hex, hagL, h0⟩ :=
        breakForLoopRevT_sim bi N leafSpec br A R (exitRunName (some r)) i l h body bC x ihb
          hslot hok'.2.1 his hh hok'.2.2.2 hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun _ => h0⟩

theorem exitSimTy_whileFold (c : String) (body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.whileFold (.var c) body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
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
      have hslot := runSlot_exitRunName hfl
      rw [haxToLowCTKT_whileFold_some_eq _ _ _ _ hok'.2.1] at hK
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK; cases hK
      rw [hB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨rs', hex, hagL, h0⟩ :=
        breakWhileLoopT_sim bi N leafSpec br A R (exitRunName (some r)) c body bC x ihb hslot
          hok'.1 hcs hok'.2.2 hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun _ => h0⟩

end Arms

end CatCrypt.Crypto.Hax
