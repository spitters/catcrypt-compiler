/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramTower

/-!
# Program-level simulation with literal call arguments

`haxToLowCT` lowers `let x = n` for an integer literal `n` to a scalar slot, and
a call reads its arguments from tower slots, so `simScope` rejects a program
that passes a literal-bound name to a call.  A-normal forms do so whenever a
source call has a literal argument (`rotate_right#32(x, 7)`).

`litTower T` is a pass over the lowered program that stores each literal bound
to a name of `T` into a fresh `.TFp` tower slot: it replaces
`RLetU64Zero x (RSeq (RScalarSet x m) body)` by
`RLetZero x .TFp (RSeq (RLimbStore x 0 m) body)` for `x ∈ T`.  It uses only
existing `LowCT` commands.

* `simScopeL S T Γ e` is the scope checker of `simScope` in which a literal
  `letBind` of a name of `T` binds that name at `.TFp` in the tower scope; the
  literal must be an integer in `[0, 2^64)`.
* `LitStoreAgrees bridge leafSpec` is the leaf condition for the literal store:
  the limb-0 store of `n` into a zero `.TFp` slot is related to `.int n`.
* `ProgSimL` is the simulation predicate for `litTower T (haxToLowCT e)`.

## Main results

* `haxToLowCT_simulates_programL` — every program simulates under
  `envAgreesRustT`, from the hypotheses of `haxToLowCT_simulates_programT` and
  `LitStoreAgrees`.
* `simScopeL_nil` — with `T = []` the checker is `simScope`.
* `litTower_nil` — with `T = []` the pass is the identity on the image of
  `haxToLowCT`.
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Builtins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  The pass and the checker -/

/-- Store every literal bound to a name of `T` in a `.TFp` tower slot. -/
def litTower (T : List String) : LowCT → LowCT
  | .RSeq a b => .RSeq (litTower T a) (litTower T b)
  | .RLetZero x t b => .RLetZero x t (litTower T b)
  | .RLetU64Zero x (.RSeq (.RScalarSet y m) b) =>
      if T.contains x then
        .RLetZero x .TFp
          (.RSeq (.RLimbStore { locVar := x, locSrc := .TFp } 0 (BitVec.ofNat 64 m))
            (litTower T b))
      else .RLetU64Zero x (.RSeq (.RScalarSet y m) (litTower T b))
  | .RLetU64Zero x b => .RLetU64Zero x (litTower T b)
  | .RIfNz v t e => .RIfNz v (litTower T t) (litTower T e)
  | .RWhileNz v b => .RWhileNz v (litTower T b)
  | .RFor x n b => .RFor x n (litTower T b)
  | .RForRuntime x bound b => .RForRuntime x bound (litTower T b)
  | c => c

theorem litTower_seq (T : List String) (a b : LowCT) :
    litTower T (.RSeq a b) = .RSeq (litTower T a) (litTower T b) := by
  simp [litTower]

theorem litTower_letZero (T : List String) (x : String) (t : TowerType) (b : LowCT) :
    litTower T (.RLetZero x t b) = .RLetZero x t (litTower T b) := by
  simp [litTower]

theorem litTower_lit_mem (T : List String) (x : String) (m : Nat) (b : LowCT)
    (h : T.contains x = true) :
    litTower T (.RLetU64Zero x (.RSeq (.RScalarSet x m) b)) =
      .RLetZero x .TFp
        (.RSeq (.RLimbStore { locVar := x, locSrc := .TFp } 0 (BitVec.ofNat 64 m))
          (litTower T b)) := by
  simp only [litTower, h, if_true]

theorem litTower_lit_not_mem (T : List String) (x : String) (m : Nat) (b : LowCT)
    (h : T.contains x = false) :
    litTower T (.RLetU64Zero x (.RSeq (.RScalarSet x m) b)) =
      .RLetU64Zero x (.RSeq (.RScalarSet x m) (litTower T b)) := by
  simp only [litTower, h, Bool.false_eq_true, if_false]

theorem litTower_letBind_copy (T : List String) (x src : String) (b : LowCT) :
    litTower T (.RLetU64Zero x (.RSeq (.RScalarSetExpr x (.SVar src)) b)) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (.SVar src)) (litTower T b)) := by
  simp [litTower]

theorem litTower_ifNz (T : List String) (v : String) (t e : LowCT) :
    litTower T (.RIfNz v t e) = .RIfNz v (litTower T t) (litTower T e) := by
  simp [litTower]

theorem litTower_whileNz (T : List String) (v : String) (b : LowCT) :
    litTower T (.RWhileNz v b) = .RWhileNz v (litTower T b) := by
  simp [litTower]

theorem litTower_for (T : List String) (x : String) (n : Nat) (b : LowCT) :
    litTower T (.RFor x n b) = .RFor x n (litTower T b) := by
  simp [litTower]

theorem litTower_forRuntime (T : List String) (x : String)
    (bound : CatCrypt.Crypto.Jasmin.LowCT.SExpr) (b : LowCT) :
    litTower T (.RForRuntime x bound b) = .RForRuntime x bound (litTower T b) := by
  simp [litTower]

/-- With no tower literals, `litTower` is the identity. -/
theorem litTower_nil (c : LowCT) : litTower [] c = c := by
  induction c with
  | RSeq a b iha ihb => rw [litTower_seq, iha, ihb]
  | RLetZero x t b ih => rw [litTower_letZero, ih]
  | RLetU64Zero x b ih =>
    cases b with
    | RSeq a b' =>
      cases a with
      | RScalarSet y m =>
        rw [litTower_seq] at ih
        simp only [litTower, List.contains_nil, Bool.false_eq_true, if_false]
        simp only [LowCT.RSeq.injEq] at ih
        rw [ih.2]
      | _ => simp only [litTower] at ih ⊢; rw [ih]
    | _ => simp only [litTower] at ih ⊢ <;> rw [ih]
  | RIfNz v t e iht ihe => rw [litTower_ifNz, iht, ihe]
  | RWhileNz v b ih => rw [litTower_whileNz, ih]
  | RFor x n b ih => rw [litTower_for, ih]
  | RForRuntime x bound b ih => rw [litTower_forRuntime, ih]
  | _ => simp [litTower]

/-- An integer literal in `[0, 2^64)`. -/
def litWord : ImpLit → Bool
  | .int n => decide (0 ≤ n) && decide (n < 2 ^ 64)
  | _ => false

/-- The scope checker of `simScope`, in which a literal `letBind` of a name of
    `T` binds that name at `.TFp`. -/
def simScopeL (S T : List String) (Γ : TowerScope) : ImpExpr → Option TowerScope
  | .letBind name (.app f args) body =>
      if f = "array_update" then
        if args.all isVar then simScopeL S T Γ body else none
      else if f = "index" then
        if args.all isVar && scopeCompat Γ name .TFp && !S.contains name then
          simScopeL S T ((name, .TFp) :: Γ) body
        else none
      else
        let dt := towerOfCallName f
        if !scalarCallName f && argsInScope Γ dt args && argsAvoid name args
            && scopeCompat Γ name dt && !S.contains name then
          simScopeL S T ((name, dt) :: Γ) body
        else none
  | .letBind name (.lit l) body =>
      if T.contains name then
        if litWord l && scopeCompat Γ name .TFp && !S.contains name then
          simScopeL S T ((name, .TFp) :: Γ) body
        else none
      else if S.contains name then simScopeL S T Γ body else none
  | .letBind name (.var src) body =>
      if decide (name = src) || (S.contains name && S.contains src) then simScopeL S T Γ body
      else none
  | .letBind name (.proj (.var t) _) body =>
      if decide (List.lookup t Γ = some .TFp) && decide (t ≠ name)
          && scopeCompat Γ name .TFp && !S.contains name then
        simScopeL S T ((name, .TFp) :: Γ) body
      else none
  | .var _ => some Γ
  | .unitVal => some Γ
  | .seq a b =>
      match simScopeL S T Γ a with
      | some Γ₁ => simScopeL S T Γ₁ b
      | none => none
  | .ifThenElse (.var _) t e =>
      match simScopeL S T Γ t, simScopeL S T Γ e with
      | some _, some _ => some Γ
      | _, _ => none
  | .whileLoop (.var _) body =>
      match simScopeL S T Γ body with
      | some _ => some Γ
      | none => none
  | .assign name (.lit _) => if S.contains name then some Γ else none
  | .assign name (.app f args) =>
      if f = "array_update" then none
      else
        let dt := towerOfCallName f
        if argsInScope Γ dt args && decide (List.lookup name Γ = some dt)
            && !S.contains name then some Γ else none
  | .tuple es => if es.all isVar then some Γ else none
  | .typeAscription e _ => simScopeL S T Γ e
  | _ => none

/-- With no tower literals, `simScopeL` is `simScope`. -/
theorem simScopeL_nil (S : List String) (e : ImpExpr) :
    ∀ Γ, simScopeL S [] Γ e = simScope S Γ e := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro Γ
    cases val with
    | app f args => simp only [simScopeL, simScope, ihBody]
    | lit l => simp only [simScopeL, simScope, ihBody, List.contains_nil, Bool.false_eq_true,
        if_false]
    | var src => simp only [simScopeL, simScope, ihBody]
    | proj pe i => cases pe <;> simp only [simScopeL, simScope, ihBody]
    | _ => simp only [simScopeL, simScope]
  | seq a b iha ihb =>
    intro Γ; simp only [simScopeL, simScope, iha, ihb] <;> cases simScope S Γ a <;> rfl
  | ifThenElse c t e _ iht ihe =>
    intro Γ
    cases c <;> simp only [simScopeL, simScope, iht, ihe] <;>
      cases simScope S Γ t <;> cases simScope S Γ e <;> rfl
  | whileLoop c body _ ih =>
    intro Γ
    cases c <;> simp only [simScopeL, simScope, ih] <;> cases simScope S Γ body <;> rfl
  | typeAscription e _ ih => intro Γ; simp only [simScopeL, simScope, ih]
  | assign name rhs _ => intro Γ; cases rhs <;> simp only [simScopeL, simScope]
  | _ => intro Γ; rfl

/-- The exit scope of `simScopeL` extends the entry scope. -/
theorem simScopeL_lookup_mono (S T : List String) (e : ImpExpr) :
    ∀ (Γ Γ' : TowerScope), simScopeL S T Γ e = some Γ' →
      ∀ m dt, List.lookup m Γ = some dt → List.lookup m Γ' = some dt := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro Γ Γ' h m dt hm
    cases val with
    | app f args =>
      simp only [simScopeL] at h
      by_cases hArr : f = "array_update"
      · rw [if_pos hArr] at h
        by_cases hAll : args.all isVar = true
        · rw [if_pos hAll] at h
          exact ihBody Γ Γ' h m dt hm
        · rw [if_neg hAll] at h; cases h
      · rw [if_neg hArr] at h
        by_cases hIdx : f = "index"
        · rw [if_pos hIdx] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            exact ihBody _ Γ' h m dt
              (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
          · cases h
        · rw [if_neg hIdx] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            exact ihBody _ Γ' h m dt
              (lookup_cons_of_scopeCompat Γ name (towerOfCallName f) hc.1.2 m dt hm)
          · cases h
    | lit l =>
      simp only [simScopeL] at h
      split at h
      · split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      · split at h
        · exact ihBody Γ Γ' h m dt hm
        · cases h
    | var src =>
      simp only [simScopeL] at h
      split at h
      · exact ihBody Γ Γ' h m dt hm
      · cases h
    | proj pe i =>
      cases pe with
      | var t =>
        simp only [simScopeL] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      | _ => simp [simScopeL] at h
    | _ => simp [simScopeL] at h
  | var _ => intro Γ Γ' h m dt hm; simp only [simScopeL, Option.some.injEq] at h; subst h; exact hm
  | unitVal => intro Γ Γ' h m dt hm; simp only [simScopeL, Option.some.injEq] at h; subst h; exact hm
  | seq a b iha ihb =>
    intro Γ Γ' h m dt hm
    simp only [simScopeL] at h
    rcases hA : simScopeL S T Γ a with _ | Γ₁
    · rw [hA] at h; cases h
    · rw [hA] at h
      exact ihb Γ₁ Γ' h m dt (iha Γ Γ₁ hA m dt hm)
  | ifThenElse c t e _ _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeL] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | _ => simp [simScopeL] at h
  | whileLoop c body _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeL] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | _ => simp [simScopeL] at h
  | assign name rhs _ =>
    intro Γ Γ' h m dt hm
    cases rhs with
    | lit _ =>
      simp only [simScopeL] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | app f args =>
      simp only [simScopeL] at h
      split at h
      · cases h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
    | _ => simp [simScopeL] at h
  | tuple es _ =>
    intro Γ Γ' h m dt hm
    simp only [simScopeL] at h
    split at h
    · rw [Option.some.injEq] at h; subst h; exact hm
    · cases h
  | typeAscription e _ ih =>
    intro Γ Γ' h
    simp only [simScopeL] at h
    exact ih Γ Γ' h
  | _ => intro Γ Γ' h; simp [simScopeL] at h

/-! ## §2  The simulation predicate -/

/-- The limb-0 store of `n < 2^64` into a zero `.TFp` slot is related by
    `bridge` to the integer value `n`. -/
def LitStoreAgrees (bridge : ValueTowerBridge) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (n : Nat), n < 2 ^ 64 →
    bridge .TFp (.int (n : Int))
      (leafSpec.limbStore { locVar := name, locSrc := .TFp } (default : RustVal .TFp) 0
        (BitVec.ofNat 64 n))

/-- Simulation of `e` by `litTower T` of its lowering, under the side conditions
    of `simScopeL`. -/
def ProgSimL (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (Γ Γ' : TowerScope) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    simScopeL S T Γ e = some Γ' → condsScalar S e = true →
    ScopeBound rs Γ → NamesFresh rs S →
    haxToLowCT e = some c →
    evalImp bi fuel e env = some (v, env') →
    envAgreesRustT bridge env rs →
    ∃ rs', RustExec N leafSpec (litTower T c) rs rs' ∧ envAgreesRustT bridge env' rs' ∧
      ScopeBound rs' Γ' ∧ NamesFresh rs' S

section ArmsL

variable (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (S T : List String)

theorem progSimL_of_simScopeL_none (e : ImpExpr) (h : ∀ Γ, simScopeL S T Γ e = none) :
    ProgSimL bridge bi N leafSpec S T e := by
  intro fuel Γ Γ' c env env' rs v hScope
  rw [h Γ] at hScope
  cases hScope

theorem progSimL_var (name : String) : ProgSimL bridge bi N leafSpec S T (.var name) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScopeL, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_var_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_var_inv bi fuel name env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSimL_unitVal : ProgSimL bridge bi N leafSpec S T .unitVal := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScopeL, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_unitVal_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_unitVal_inv bi fuel env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSimL_tuple (es : List ImpExpr) : ProgSimL bridge bi N leafSpec S T (.tuple es) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScopeL] at hScope
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

theorem progSimL_seq (a b : ImpExpr)
    (iha : ProgSimL bridge bi N leafSpec S T a) (ihb : ProgSimL bridge bi N leafSpec S T b) :
    ProgSimL bridge bi N leafSpec S T (.seq a b) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  simp only [simScopeL] at hScope
  rcases hA : simScopeL S T Γ a with _ | Γ₁
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
  rw [litTower_seq]
  exact ⟨rs', rustExec_RSeq_chain N leafSpec _ _ rs rs_mid rs' hAexec hBexec,
         hAgree', hSB', hSF'⟩

theorem progSimL_ifThenElse (cond : String) (t e : ImpExpr)
    (iht : ProgSimL bridge bi N leafSpec S T t) (ihe : ProgSimL bridge bi N leafSpec S T e) :
    ProgSimL bridge bi N leafSpec S T (.ifThenElse (.var cond) t e) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  obtain ⟨⟨hCondS, hCt⟩, hCe⟩ := hConds
  have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
  simp only [simScopeL] at hScope
  rcases hT : simScopeL S T Γ t with _ | Γt
  · rw [hT] at hScope; cases hScope
  rcases hE : simScopeL S T Γ e with _ | Γe
  · rw [hT, hE] at hScope; cases hScope
  rw [hT, hE] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ := haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  rw [litTower_ifNz]
  rcases evalImp_ifThenElse_var_inv bi fuel cond t e env v env' hEval with
    ⟨hCond, hTeval⟩ | ⟨hCond, hEeval⟩
  · obtain ⟨rs', hTexec, hAgree', hSB', hSF'⟩ :=
      iht fuel Γ Γt tC env env' rs v hT hCt hSB hSF hTtrans hTeval hAgree
    have hScalar : rs.rsScalar cond = 1 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_true N leafSpec cond _ _ rs rs' 1 hScalar
      (by decide) hTexec, hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γt (simScopeL_lookup_mono S T t Γ Γt hT) hSB'
  · obtain ⟨rs', hEexec, hAgree', hSB', hSF'⟩ :=
      ihe fuel Γ Γe eC env env' rs v hE hCe hSB hSF hEtrans hEeval hAgree
    have hScalar : rs.rsScalar cond = 0 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond false hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_false N leafSpec cond _ _ rs rs' hScalar hEexec,
      hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γe (simScopeL_lookup_mono S T e Γ Γe hE) hSB'

theorem progSimL_whileLoop (cond : String) (body : ImpExpr)
    (ihBody : ProgSimL bridge bi N leafSpec S T body) :
    ProgSimL bridge bi N leafSpec S T (.whileLoop (.var cond) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  obtain ⟨hCondS, hCb⟩ := hConds
  simp only [simScopeL] at hScope
  rcases hB : simScopeL S T Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bC, hBtrans, hC⟩ := haxToLowCT_whileLoop_var_some cond body c hHax
  subst hC
  rw [litTower_whileNz]
  have hMono := simScopeL_lookup_mono S T body Γ Γb hB
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
      exact ⟨rs, RustExec.whileFalse cond _ rs hScalar, hAgree, hSB, hSF⟩
    · have hScalar : rs.rsScalar cond = 1 :=
        envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCondTrue
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid⟩ :=
        ihBody (n+1) Γ Γb bC env env_mid rs vB hB hCb hSB hSF hBtrans hBodyEval hAgree
      have hSBmid' : ScopeBound rs_mid Γ := ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid
      obtain ⟨rs', hLoopExec, hAgree', hSB', hSF'⟩ :=
        IH env_mid env' rs_mid v hSBmid' hSFmid hLoopRec hAgreeMid
      exact ⟨rs', RustExec.whileTrue cond _ rs rs_mid rs' 1 hScalar (by decide)
               hBodyExec hLoopExec, hAgree', hSB', hSF'⟩

theorem progSimL_letBind_lit (name : String) (l : ImpLit) (body : ImpExpr)
    (hLit : LitStoreAgrees bridge leafSpec)
    (ihBody : ProgSimL bridge bi N leafSpec S T body) :
    ProgSimL bridge bi N leafSpec S T (.letBind name (.lit l) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeL] at hScope
  obtain ⟨bodyC, m, hBodyTrans, hDecode, hC⟩ := haxToLowCT_letBind_lit_some name l body c hHax
  subst hC
  have hBodyEval := evalImp_letBind_lit_inv bi fuel name l body env v env' hEval
  by_cases hTm : T.contains name = true
  · rw [if_pos hTm] at hScope
    split at hScope
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hW, hCompat⟩, hNotS⟩ := hc
      have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
      obtain ⟨k, hk, hl, hm⟩ : ∃ k : Nat, k < 2 ^ 64 ∧ Value.ofLit l = .int (k : Int) ∧ k = m := by
        cases l with
        | int n =>
          simp only [litWord, Bool.and_eq_true, decide_eq_true_eq] at hW
          obtain ⟨h0, h1⟩ := hW
          refine ⟨n.toNat, by omega, by simp [Value.ofLit, Int.toNat_of_nonneg h0], ?_⟩
          simp only [Value.ofLit, valueToScalar, if_pos h0, Option.some.injEq] at hDecode
          exact hDecode
        | _ => simp [litWord] at hW
      subst hm
      rw [litTower_lit_mem T name k bodyC hTm]
      set loc : Located := { locVar := name, locSrc := .TFp } with hloc
      set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
      have hLookup : locatedLookup rs_init loc = some default := locatedLookup_letZero rs name .TFp
      set newVal := leafSpec.limbStore loc (default : RustVal .TFp) 0 (BitVec.ofNat 64 k)
        with hnewVal
      have hStore : RustExec N leafSpec (.RLimbStore loc 0 (BitVec.ofNat 64 k)) rs_init
          (locatedUpdate rs_init loc newVal) :=
        RustExec.limbStore loc 0 _ rs_init default hLookup
      have hRsMidEq : locatedUpdate rs_init loc newVal = rsSetTower rs name ⟨.TFp, newVal⟩ := by
        show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
            = rsSetTower rs name ⟨.TFp, newVal⟩
        exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
      have hBridge : bridge .TFp (Value.ofLit l) newVal := by
        rw [hl]; exact hLit name k hk
      have hAgreeMid : envAgreesRustT bridge (env.extend name (Value.ofLit l))
          (locatedUpdate rs_init loc newVal) := by
        rw [hRsMidEq]
        exact envAgreesRustT_extend_tower bridge env rs name _ .TFp newVal hAgree hBridge
      have hSBmid : ScopeBound (locatedUpdate rs_init loc newVal) ((name, .TFp) :: Γ) := by
        rw [hRsMidEq]
        exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
      have hSFmid : NamesFresh (locatedUpdate rs_init loc newVal) S := by
        rw [hRsMidEq]
        exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC _ env' _ v hScope hConds hSBmid hSFmid
          hBodyTrans hBodyEval hAgreeMid
      exact ⟨rs', RustExec.letZero name .TFp _ rs rs'
        (RustExec.seq _ _ _ _ _ hStore hBodyExec), hAgree', hSB', hSF'⟩
    · cases hScope
  · rw [if_neg hTm] at hScope
    split at hScope
    · rename_i hIn
      rw [litTower_lit_not_mem T name m bodyC (by simpa using hTm)]
      have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
      have hAgreeExt : envAgreesRustT bridge (env.extend name (Value.ofLit l))
                        (rsSetScalar rs name m) :=
        envAgreesRustT_extend_scalar_fresh bridge env rs name (Value.ofLit l) m hFresh hDecode
          hAgree
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel Γ Γ' bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name m) v
          hScope hConds hSB hSF hBodyTrans hBodyEval hAgreeExt
      exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name m _ rs rs' hBodyExec,
             hAgree', hSB', hSF'⟩
    · cases hScope

theorem progSimL_letBind_var (name src : String) (body : ImpExpr)
    (ihBody : ProgSimL bridge bi N leafSpec S T body) :
    ProgSimL bridge bi N leafSpec S T (.letBind name (.var src) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeL] at hScope
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
      rw [litTower_letBind_copy]
      exact ⟨rs', rustExec_letBind_copy N leafSpec name src _ rs rs' hEq hExec,
        hAgree', hSB', hSF'⟩
  · cases hScope

theorem progSimL_letBind_app (name f : String) (args : List ImpExpr) (body : ImpExpr)
    (hLeaf : LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hf_arr : f ≠ "array_update") (hf_idx : f ≠ "index")
    (ihBody : ProgSimL bridge bi N leafSpec S T body) :
    ProgSimL bridge bi N leafSpec S T (.letBind name (.app f args) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeL, if_neg hf_arr, if_neg hf_idx] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hNotSc, hArgsIn⟩, hAvoid⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
      haxToLowCT_letBind_app_some name f args body c hf_arr hf_idx (by simpa using hNotSc) hHax
    subst hC
    rw [litTower_letZero, litTower_seq]
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

theorem progSimL_letBind_proj (name t : String) (i : Nat) (body : ImpExpr)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (ihBody : ProgSimL bridge bi N leafSpec S T body) :
    ProgSimL bridge bi N leafSpec S T (.letBind name (.proj (.var t) i) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeL] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hLk, hNe⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_proj_some name t i body c hHax
    subst hC
    rw [litTower_letZero, litTower_seq]
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

/-- On a program `simScopeL` accepts, `litTower` fixes the lowering of an
    assignment. -/
theorem progSimL_of_progSimT_assign (e : ImpExpr)
    (hScopeEq : ∀ Γ, simScopeL S T Γ e = simScope S Γ e)
    (hFix : ∀ c, haxToLowCT e = some c → litTower T c = c)
    (h : ProgSimT bridge bi N leafSpec S e) : ProgSimL bridge bi N leafSpec S T e := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  rw [hScopeEq] at hScope
  rw [hFix c hHax]
  exact h fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree

end ArmsL

/-! ## §3  The program-level theorem -/

/-- **Program-level simulation with literal call arguments.**  Every source
    program simulates by `litTower T` of its lowering under `envAgreesRustT`,
    when every call name satisfies `LeafCallAgreesArgs`, tuple loads agree with
    `Value.projIdx`, literal stores agree with `LitStoreAgrees`, and the builtin
    table implements neither `array_update` nor `index`. -/
theorem haxToLowCT_simulates_programL
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String)
    (hLeaf : ∀ f, LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hArr : ∀ vals, bi "array_update" vals = none)
    (hIdx : ∀ vals, bi "index" vals = none)
    (e : ImpExpr) : ProgSimL bridge bi N leafSpec S T e := by
  have noneArm := progSimL_of_simScopeL_none bridge bi N leafSpec S T
  induction e using ImpExpr.ind with
  | var name => exact progSimL_var bridge bi N leafSpec S T name
  | unitVal => exact progSimL_unitVal bridge bi N leafSpec S T
  | seq a b iha ihb => exact progSimL_seq bridge bi N leafSpec S T a b iha ihb
  | tuple es _ => exact progSimL_tuple bridge bi N leafSpec S T es
  | letBind name val body _ ihBody =>
    cases val with
    | lit l => exact progSimL_letBind_lit bridge bi N leafSpec S T name l body hLit ihBody
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
      exact progSimL_letBind_app bridge bi N leafSpec S T name f args body (hLeaf f)
        hf_arr hf_idx ihBody
    | var src => exact progSimL_letBind_var bridge bi N leafSpec S T name src body ihBody
    | proj pe i =>
      cases pe with
      | var t =>
        exact progSimL_letBind_proj bridge bi N leafSpec S T name t i body hProj ihBody
      | _ => exact noneArm _ fun Γ => by simp [simScopeL]
    | _ => exact noneArm _ fun Γ => by simp [simScopeL]
  | ifThenElse cond t e _ iht ihe =>
    cases cond with
    | var v_cond => exact progSimL_ifThenElse bridge bi N leafSpec S T v_cond t e iht ihe
    | _ => exact noneArm _ fun Γ => by simp [simScopeL]
  | whileLoop cond body _ ihBody =>
    cases cond with
    | var v_cond => exact progSimL_whileLoop bridge bi N leafSpec S T v_cond body ihBody
    | _ => exact noneArm _ fun Γ => by simp [simScopeL]
  | assign name rhs _ =>
    cases rhs with
    | lit l =>
      refine progSimL_of_progSimT_assign bridge bi N leafSpec S T _ (fun Γ => rfl) ?_
        (progSimT_assign_lit bridge bi N leafSpec S name l)
      intro c hc
      obtain ⟨m, rfl⟩ := haxToLowCT_assign_lit_shape name l c hc
      rfl
    | app f args =>
      by_cases hf : f = "array_update"
      · exact noneArm _ fun Γ => by simp only [simScopeL, if_pos hf]
      refine progSimL_of_progSimT_assign bridge bi N leafSpec S T _ (fun Γ => rfl) ?_
        (progSimT_assign_app bridge bi N leafSpec S name f args hf (hLeaf f))
      intro c hc
      obtain ⟨_, _, rfl⟩ := haxToLowCT_assign_app_some name f args c hf hc
      rfl
    | _ => exact noneArm _ fun Γ => by simp [simScopeL]
  | typeAscription e _ ih =>
    intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
    simp only [simScopeL] at hScope
    simp only [condsScalar] at hConds
    rw [haxToLowCT_typeAscription_eq] at hHax
    rw [evalImp_typeAscription] at hEval
    exact ih fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  | _ => exact noneArm _ fun Γ => by simp [simScopeL]

end CatCrypt.Crypto.Hax
