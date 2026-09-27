/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramFor
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_RuntimeLoop

/-!
# Program-level simulation with runtime-bound, reverse and data-dependent loops

`haxToLowCT` lowers a hax `forFold i lo n body` from a non-negative integer
literal `lo` to a variable bound `n` to `RForRuntime i (n - lo) body'`, a
`forFoldRev i lo hi body` with non-negative integer literal bounds to
`RFor i (hi - lo) body'` whose body first maps the trip counter `j` to
`hi - 1 - j` (`revShift`), and a `whileFold (var c) body` to `RWhileNz c body'`.
The source semantics is `denote` of `forToLoop e`, which reads every `forFold`,
`forFoldRev` and `whileFold` as the `forLoop`, `forLoopRev` and `whileLoop` with
the same range, guard and body.

* `simScopeW tow D S T A Γ e` is the checker of `simScopeF` with the three loop
  arms: the runtime bound is a name of `S` and of `D`; the counters and the
  guard are names of `S`.
* `ScalarInv D S env` is the environment invariant the runtime arm needs: every
  name of `D` is bound and every integer held by a name of `S` is non-negative.
  `denote` runs zero trips of a `forLoop` whose bound is a negative integer while
  `RForRuntime` reads the scalar heap, and it returns the start of a `forLoop`
  whose bound is unbound; the invariant excludes both.
* `ProgSimW` is the simulation predicate, with `ScalarInv` as a hypothesis on the
  entry environment and a conclusion on the exit environment.
* A binding `let x = f(a, b)` of a call name `f` computed in the scalar heap
  (`scalarCallName`) lowers to `RScalarSetExpr`; `simScopeW` accepts it when `x`,
  `a` and `b` are names of `S` and `a`, `b` differ from `x`, and
  `ScalarCallsAgree` is the condition it places on the builtin table
  (`progSimW_letBind_scalar`).
* A binding `let x = index(v, i)` at a non-negative integer literal `i` lowers to
  `RScalarSetExpr x (SLimb v i)`; `simScopeW` accepts it when `x` is a name of
  `S` and `v` is in scope at a type that is not a container (`t.elemType = t`),
  and `LimbReadAgrees` is the condition it places on the builtin table
  (`progSimW_letBind_limb`).
* An assignment `arr = array_update(arr, idx, src)` on three variables lowers to
  `RArrStore arr idx src`; `simScopeW` accepts it under the side conditions of the
  `letBind` form, and `ArrUpdateAgrees` is the condition it places on the builtin
  table (`progSimW_assign_arrUpdate`).

## Main results

* `haxToLowCT_simulates_programW` — every program simulates, from the
  hypotheses of `haxToLowCT_simulates_programA`.
* `progSimW_forFold_var`, `progSimW_forFoldRev`, `progSimW_whileFold` — the
  three loop arms; `tripsFrom_of_forLoop` and `tripsFrom_of_forLoopRev` are the
  trip inductions shared with the literal-bound arm `progSimW_forFold`.
* `haxToLowCT_simulates_forFold`, `haxToLowCT_simulates_forFoldRev`,
  `haxToLowCT_simulates_whileFold` — the closed forms of the loop arms from the
  leaf hypotheses.
* `simScopeW_lookup_mono`, `simScopeW_eq_tow` — the exit scope extends the entry
  scope, and the checker depends on the tower dispatch only at the call names
  `scopeCallNamesW` collects.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat Value Env Outcome Builtins denote denoteForLoop
  denoteForLoopRev denoteArgs)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal SExpr
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  Unpackers of the loop arms of `haxToLowCT` -/

/-- The lowering of a `forFoldRev` with non-negative integer literal bounds. -/
theorem haxToLowCT_forFoldRev_lit_some (i : String) (lo hi : Int) (body : ImpExpr) (c : LowCT)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (h : haxToLowCT (.forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body) = some c) :
    ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = .RFor i (hi.toNat - lo.toNat)
        (.RSeq (.RScalarSetExpr i (.SSub (.SLit (hi.toNat - 1)) (.SVar i))) bodyC) := by
  cases hB : haxToLowCT body with
  | none => simp [haxToLowCT, hB, impLitNat, hlo, hhi] at h
  | some bodyC =>
    refine ⟨bodyC, rfl, ?_⟩
    simp [haxToLowCT, hB, impLitNat, hlo, hhi] at h
    exact h.symm

/-- The lowering of a `forFold` from a non-negative integer literal to a
    variable bound: `RForRuntime` over the bound less the start, with the
    counter shifted by the start when it is not zero. -/
theorem haxToLowCT_forFold_var_some (i : String) (lo : Int) (n : String) (body : ImpExpr)
    (c : LowCT) (hlo : 0 ≤ lo)
    (h : haxToLowCT (.forFold i (.lit (.int lo)) (.var n) body) = some c) :
    ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = (if lo.toNat = 0 then .RForRuntime i (.SVar n) bodyC
           else .RForRuntime i (.SSub (.SVar n) (.SLit lo.toNat))
             (.RSeq (.RScalarSetExpr i (.SAdd (.SVar i) (.SLit lo.toNat))) bodyC)) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hlo
  cases hB : haxToLowCT body with
  | none =>
    cases a with
    | zero => simp [haxToLowCT, hB, impBoundToSExpr] at h
    | succ a =>
      rw [show ((a + 1 : Nat) : Int) = Int.ofNat (a + 1) from rfl] at h
      simp only [haxToLowCT, hB, impLitNat, impBoundToSExpr] at h
      simp_all
  | some bodyC =>
    refine ⟨bodyC, rfl, ?_⟩
    cases a with
    | zero => simp [haxToLowCT, hB, impBoundToSExpr] at h; simp [h]
    | succ a =>
      rw [show ((a + 1 : Nat) : Int) = Int.ofNat (a + 1) from rfl] at h
      simp only [haxToLowCT, hB, impLitNat, impBoundToSExpr] at h
      simp_all

/-- The lowering of a `whileFold` on a variable guard. -/
theorem haxToLowCT_whileFold_var_some (cond : String) (body : ImpExpr) (c : LowCT)
    (h : haxToLowCT (.whileFold (.var cond) body) = some c) :
    ∃ bC, haxToLowCT body = some bC ∧ c = .RWhileNz cond bC := by
  cases hB : haxToLowCT body with
  | none => simp [haxToLowCT, hB] at h
  | some bC =>
    refine ⟨bC, rfl, ?_⟩
    simp [haxToLowCT, hB] at h
    exact h.symm

/-! ## §2  Scalar names hold non-negative integers -/

/-- Every name of `D` is bound in the environment, and every integer held by a
    name of `S` is non-negative. -/
def ScalarInv (D S : List String) (env : Env) : Prop :=
  (∀ x ∈ D, ∃ v, env x = some v) ∧ ∀ x ∈ S, ∀ k : Int, env x = some (.int k) → 0 ≤ k

theorem ScalarInv.extend_defined {D S : List String} {env : Env} (h : ScalarInv D S env)
    (x : String) (v : Value) : ∀ y ∈ D, ∃ w, (env.extend x v) y = some w := by
  intro y hy
  simp only [Env.extend]
  split
  · exact ⟨v, rfl⟩
  · exact h.1 y hy

theorem ScalarInv.extend_of_not_mem {D S : List String} {env : Env}
    (h : ScalarInv D S env) {x : String} (hx : x ∉ S) (v : Value) :
    ScalarInv D S (env.extend x v) := by
  refine ⟨h.extend_defined x v, ?_⟩
  intro y hy k hk
  simp only [Env.extend] at hk
  split at hk
  · rename_i heq
    simp only [beq_iff_eq] at heq
    subst heq
    exact absurd hy hx
  · exact h.2 y hy k hk

theorem ScalarInv.extend_of_nonneg {D S : List String} {env : Env}
    (h : ScalarInv D S env) (x : String) {v : Value} (hv : ∀ k : Int, v = .int k → 0 ≤ k) :
    ScalarInv D S (env.extend x v) := by
  refine ⟨h.extend_defined x v, ?_⟩
  intro y hy k hk
  simp only [Env.extend] at hk
  split at hk
  · exact hv k (Option.some.inj hk)
  · exact h.2 y hy k hk

/-- A value with a scalar reading is a non-negative integer if it is an integer. -/
theorem nonneg_of_valueToScalar {v : Value} {m : Nat} (h : valueToScalar v = some m) :
    ∀ k : Int, v = .int k → 0 ≤ k := by
  intro k hk
  subst hk
  simp only [valueToScalar] at h
  split at h <;> simp_all

/-- A literal assignment `haxToLowCT` accepts assigns a non-negative integer if
    it assigns an integer. -/
theorem assign_lit_nonneg (name : String) (l : ImpLit) (c : LowCT)
    (h : haxToLowCT (.assign name (.lit l)) = some c) :
    ∀ k : Int, Value.ofLit l = .int k → 0 ≤ k := by
  intro k hk
  cases l with
  | int n =>
    simp only [Value.ofLit, Value.int.injEq] at hk
    subst hk
    simp only [haxToLowCT] at h
    split at h <;> simp_all
  | _ => simp [Value.ofLit] at hk

theorem ScalarInv_of_eq {D S : List String} {env env' : Env} (h : ScalarInv D S env)
    (he : env' = env) : ScalarInv D S env' := he ▸ h

/-! ## §3  The checker -/

/-- The scope checker of `simScopeF` extended to a `forFold` from a non-negative
    integer literal to a scalar variable bound, a `forFoldRev` with non-negative
    integer literal bounds and a `whileFold` on a scalar guard; the exit scope of
    every loop is its entry scope.  A limb read `let x = index(v, i)` at a
    non-negative integer literal `i` requires `x` to be a name of `S` and `v` to
    be in scope at a type that is not a container, and leaves the scope
    unchanged.  An assignment `arr = array_update(arr, idx, src)` on three
    variables has the side conditions of the `letBind` form: `arr` is recorded in
    `A` and in scope at that type, `src` is in scope at the element type and `idx`
    is a name of `S`. -/
def simScopeW (tow : String → TowerType) (D S T : List String) (A Γ : TowerScope) :
    ImpExpr → Option TowerScope
  | .letBind name (.app f args) body =>
      if f = "array_update" then
        match args with
        | [.var arr, .var idx, .var src] =>
            match List.lookup arr A with
            | some t =>
                if decide (name = arr) && decide (List.lookup arr Γ = some t)
                    && decide (List.lookup src Γ = some t.elemType) && S.contains idx then
                  simScopeW tow D S T A Γ body
                else none
            | none => none
        | _ => none
      else if f = "index" then
        match args with
        | [.var arr, .var idx] =>
            match List.lookup arr A with
            | some t =>
                if decide (List.lookup arr Γ = some t) && decide (arr ≠ name) && S.contains idx
                    && scopeCompat Γ name .TFp && !S.contains name then
                  simScopeW tow D S T A ((name, .TFp) :: Γ) body
                else none
            | none => none
        | [.var arr, .lit (.int i)] =>
            match List.lookup arr Γ with
            | some t =>
                if decide (t.elemType = t) && decide (0 ≤ i) && S.contains name then
                  simScopeW tow D S T A Γ body
                else none
            | none => none
        | _ => none
      else if scalarCallName f then
        match args with
        | [.var a, .var b] =>
            if S.contains name && S.contains a && S.contains b && decide (a ≠ name)
                && decide (b ≠ name) then
              simScopeW tow D S T A Γ body
            else none
        | _ => none
      else
        let dt := tow f
        if argsInScope Γ dt args && argsAvoid name args && scopeCompat Γ name dt
            && !S.contains name then
          simScopeW tow D S T A ((name, dt) :: Γ) body
        else none
  | .letBind name (.lit l) body =>
      if T.contains name then
        if litWord l && scopeCompat Γ name .TFp && !S.contains name then
          simScopeW tow D S T A ((name, .TFp) :: Γ) body
        else none
      else if S.contains name then simScopeW tow D S T A Γ body else none
  | .letBind name (.var src) body =>
      if name = src then simScopeW tow D S T A Γ body else none
  | .letBind name (.proj (.var t) _) body =>
      if decide (List.lookup t Γ = some .TFp) && decide (t ≠ name)
          && scopeCompat Γ name .TFp && !S.contains name then
        simScopeW tow D S T A ((name, .TFp) :: Γ) body
      else none
  | .var _ => some Γ
  | .unitVal => some Γ
  | .seq a b =>
      match simScopeW tow D S T A Γ a with
      | some Γ₁ => simScopeW tow D S T A Γ₁ b
      | none => none
  | .ifThenElse (.var c) t e =>
      if S.contains c then
        match simScopeW tow D S T A Γ t, simScopeW tow D S T A Γ e with
        | some _, some _ => some Γ
        | _, _ => none
      else none
  | .whileLoop (.var c) body =>
      if S.contains c then
        match simScopeW tow D S T A Γ body with
        | some _ => some Γ
        | none => none
      else none
  | .forFold i (.lit (.int lo)) (.lit (.int hi)) body =>
      if decide (0 ≤ lo) && decide (0 ≤ hi) && S.contains i then
        match simScopeW tow D S T A Γ body with
        | some _ => some Γ
        | none => none
      else none
  | .forFold i (.lit (.int lo)) (.var n) body =>
      if decide (0 ≤ lo) && S.contains i && S.contains n && D.contains n then
        match simScopeW tow D S T A Γ body with
        | some _ => some Γ
        | none => none
      else none
  | .forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body =>
      if decide (0 ≤ lo) && decide (0 ≤ hi) && S.contains i then
        match simScopeW tow D S T A Γ body with
        | some _ => some Γ
        | none => none
      else none
  | .whileFold (.var c) body =>
      if S.contains c then
        match simScopeW tow D S T A Γ body with
        | some _ => some Γ
        | none => none
      else none
  | .assign name (.lit _) => if S.contains name then some Γ else none
  | .assign name (.app f args) =>
      if f = "array_update" then
        match args with
        | [.var arr, .var idx, .var src] =>
            match List.lookup arr A with
            | some t =>
                if decide (name = arr) && decide (List.lookup arr Γ = some t)
                    && decide (List.lookup src Γ = some t.elemType) && S.contains idx then some Γ
                else none
            | none => none
        | _ => none
      else if f = "index" then none
      else
        let dt := tow f
        if !scalarCallName f && argsInScope Γ dt args && decide (List.lookup name Γ = some dt)
            && !S.contains name then some Γ else none
  | .tuple es => if es.all isVar then some Γ else none
  | .typeAscription e _ => simScopeW tow D S T A Γ e
  | _ => none

/-- `simScopeW` rejects a `forFold` whose start is not an integer literal or whose
    bound is neither an integer literal nor a variable. -/
theorem simScopeW_forFold_none (tow : String → TowerType) (D S T : List String) (A Γ : TowerScope)
    (i : String) (lo hi body : ImpExpr)
    (hs : ¬ ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b))
    (hv : ¬ ∃ (a : Int) (n : String), lo = .lit (.int a) ∧ hi = .var n) :
    simScopeW tow D S T A Γ (.forFold i lo hi body) = none := by
  unfold simScopeW
  split <;> simp_all

/-- `simScopeW` rejects a `forFoldRev` whose bounds are not both integer literals. -/
theorem simScopeW_forFoldRev_none (tow : String → TowerType) (D S T : List String) (A Γ : TowerScope)
    (i : String) (lo hi body : ImpExpr)
    (hs : ¬ ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)) :
    simScopeW tow D S T A Γ (.forFoldRev i lo hi body) = none := by
  unfold simScopeW
  split <;> simp_all

/-- The exit scope of `simScopeW` extends the entry scope. -/
theorem simScopeW_lookup_mono (tow : String → TowerType) (D S T : List String) (A : TowerScope)
    (e : ImpExpr) :
    ∀ (Γ Γ' : TowerScope), simScopeW tow D S T A Γ e = some Γ' →
      ∀ m dt, List.lookup m Γ = some dt → List.lookup m Γ' = some dt := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro Γ Γ' h m dt hm
    cases val with
    | app f args =>
      simp only [simScopeW] at h
      split at h
      · split at h
        · split at h
          · split at h
            · exact ihBody Γ Γ' h m dt hm
            · cases h
          · cases h
        · cases h
      · split at h
        · split at h
          · split at h
            · split at h
              · rename_i hc
                simp only [Bool.and_eq_true] at hc
                exact ihBody _ Γ' h m dt
                  (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
              · cases h
            · cases h
          · split at h
            · split at h
              · exact ihBody Γ Γ' h m dt hm
              · cases h
            · cases h
          · cases h
        · split at h
          · split at h
            · split at h
              · exact ihBody Γ Γ' h m dt hm
              · cases h
            · cases h
          · split at h
            · rename_i hc
              simp only [Bool.and_eq_true] at hc
              exact ihBody _ Γ' h m dt
                (lookup_cons_of_scopeCompat Γ name (tow f) hc.1.2 m dt hm)
            · cases h
    | lit l =>
      simp only [simScopeW] at h
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
      simp only [simScopeW] at h
      split at h
      · exact ihBody Γ Γ' h m dt hm
      · cases h
    | proj pe i =>
      cases pe with
      | var t =>
        simp only [simScopeW] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      | _ => simp [simScopeW] at h
    | _ => simp [simScopeW] at h
  | var _ => intro Γ Γ' h m dt hm; simp only [simScopeW, Option.some.injEq] at h; subst h; exact hm
  | unitVal => intro Γ Γ' h m dt hm; simp only [simScopeW, Option.some.injEq] at h; subst h; exact hm
  | seq a b iha ihb =>
    intro Γ Γ' h m dt hm
    simp only [simScopeW] at h
    rcases hA : simScopeW tow D S T A Γ a with _ | Γ₁
    · rw [hA] at h; cases h
    · rw [hA] at h
      exact ihb Γ₁ Γ' h m dt (iha Γ Γ₁ hA m dt hm)
  | ifThenElse c t e _ _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeW] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    | _ => simp [simScopeW] at h
  | whileLoop c body _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeW] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    | _ => simp [simScopeW] at h
  | whileFold c body _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeW] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    | _ => simp [simScopeW] at h
  | forFold i lo hi body _ _ _ =>
    intro Γ Γ' h m dt hm
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      simp only [simScopeW] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    · by_cases hv : ∃ (a : Int) (n : String), lo = .lit (.int a) ∧ hi = .var n
      · obtain ⟨a, n, rfl, rfl⟩ := hv
        simp only [simScopeW] at h
        split at h
        · split at h
          · rw [Option.some.injEq] at h; subst h; exact hm
          · cases h
        · cases h
      · rw [simScopeW_forFold_none tow D S T A Γ i lo hi body hs hv] at h
        cases h
  | forFoldRev i lo hi body _ _ _ =>
    intro Γ Γ' h m dt hm
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      simp only [simScopeW] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    · rw [simScopeW_forFoldRev_none tow D S T A Γ i lo hi body hs] at h
      cases h
  | assign name rhs _ =>
    intro Γ Γ' h m dt hm
    cases rhs with
    | lit _ =>
      simp only [simScopeW] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | app f args =>
      simp only [simScopeW] at h
      repeat' split at h
      all_goals first
        | (rw [Option.some.injEq] at h; subst h; exact hm)
        | cases h
    | _ => simp [simScopeW] at h
  | tuple es _ =>
    intro Γ Γ' h m dt hm
    simp only [simScopeW] at h
    split at h
    · rw [Option.some.injEq] at h; subst h; exact hm
    · cases h
  | typeAscription e _ ih =>
    intro Γ Γ' h
    simp only [simScopeW] at h
    exact ih Γ Γ' h
  | _ => intro Γ Γ' h; simp [simScopeW] at h

/-! ## §4  The simulation predicate -/

/-- Simulation of `e` by `arrTower A (litTower T c)` for its lowering `c`, under
    the side conditions of `simScopeW towerOfCallName`, with the source run of
    `forToLoop e` from an environment whose scalar names hold non-negative
    integers. -/
def ProgSimW (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (D S T : List String) (A : TowerScope) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (Γ Γ' : TowerScope) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    simScopeW towerOfCallName D S T A Γ e = some Γ' →
    ScopeBound rs Γ → NamesFresh rs S →
    haxToLowCT e = some c →
    evalImp bi fuel (forToLoop e) env = some (v, env') →
    envAgreesRustT bridge env rs → ScalarInv D S env →
    ∃ rs', RustExec N leafSpec (arrTower A (litTower T c)) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S ∧
      ScalarInv D S env'

/-- The loop body `haxToLowCT` produces for a `forFoldRev` with bound `hi`: the
    lowered body after the trip counter `j` is mapped to `hi - 1 - j`. -/
def revShift (i : String) (hi : Nat) (bodyC : LowCT) : LowCT :=
  .RSeq (.RScalarSetExpr i (.SSub (.SLit (hi - 1)) (.SVar i))) bodyC

/-- A trip of the lowered reverse loop body: from the counter set to `j`, the
    shifted body runs as the body from the counter set to `hi - 1 - j`. -/
theorem revShift_exec (N : Nat) (leafSpec : LeafSpec) (T : List String) (A : TowerScope)
    (i : String) (hi j : Nat) (bodyC : LowCT) (rs r : RustState)
    (h : RustExec N leafSpec (arrTower A (litTower T bodyC)) (rsSetScalar rs i (hi - 1 - j)) r) :
    RustExec N leafSpec (arrTower A (litTower T (revShift i hi bodyC))) (rsSetScalar rs i j) r := by
  unfold revShift
  rw [litTower_seq, arrTower_seq, litTower_scalarSetExpr, arrTower_scalarSetExpr]
  refine RustExec.seq _ _ _ (rsSetScalar rs i (hi - 1 - j)) _ ?_ h
  have hS := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) i
    (.SSub (.SLit (hi - 1)) (.SVar i)) (rsSetScalar rs i j)
  have hv : (SExpr.SSub (.SLit (hi - 1)) (.SVar i)).evalState (rsSetScalar rs i j) =
      hi - 1 - j := by
    simp [SExpr.evalState, rsSetScalar]
  rw [hv, rsSetScalar_collapse] at hS
  exact hS

section ArmsW

variable (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (D S T : List String) (A : TowerScope)

theorem progSimW_of_simScopeW_none (e : ImpExpr)
    (h : ∀ Γ, simScopeW towerOfCallName D S T A Γ e = none) :
    ProgSimW bridge bi N leafSpec D S T A e := by
  intro fuel Γ Γ' c env env' rs v hScope
  rw [h Γ] at hScope
  cases hScope

/-- On a program without subprograms that `simScopeW` accepts as `simScopeA` does,
    whose conditions are trivially scalar, which `forToLoop` fixes and whose runs
    keep the scalar names non-negative, the simulation of `ProgSimA` gives that of
    `ProgSimW`. -/
theorem progSimW_of_progSimA (e : ImpExpr)
    (hScopeEq : ∀ Γ, simScopeW towerOfCallName D S T A Γ e = simScopeA towerOfCallName S T A Γ e)
    (hConds : condsScalar S e = true)
    (hLoop : ∀ Γ Γ', simScopeW towerOfCallName D S T A Γ e = some Γ' → forToLoop e = e)
    (hInv : ∀ Γ Γ' c fuel env env' v, simScopeW towerOfCallName D S T A Γ e = some Γ' →
      haxToLowCT e = some c → evalImp bi fuel e env = some (v, env') →
      ScalarInv D S env → ScalarInv D S env')
    (h : ProgSimA bridge bi N leafSpec S T A e) : ProgSimW bridge bi N leafSpec D S T A e := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  rw [hLoop Γ Γ' hScope] at hEval
  have hNN' := hInv Γ Γ' c fuel env env' v hScope hHax hEval hNN
  rw [hScopeEq] at hScope
  obtain ⟨rs', hExec, hAgree', hSB', hSF'⟩ :=
    h fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  exact ⟨rs', hExec, hAgree', hSB', hSF', hNN'⟩

/-- `progSimW_of_progSimA` with the simulation of `ProgSimA` over a second builtin
    table `bi'` whose runs of `e` agree with those of `bi` when `simScopeW`
    accepts `e`. -/
theorem progSimW_of_progSimA_tables (bi' : Builtins) (e : ImpExpr)
    (hScopeEq : ∀ Γ, simScopeW towerOfCallName D S T A Γ e = simScopeA towerOfCallName S T A Γ e)
    (hConds : condsScalar S e = true)
    (hLoop : ∀ Γ Γ', simScopeW towerOfCallName D S T A Γ e = some Γ' → forToLoop e = e)
    (hInv : ∀ Γ Γ' c fuel env env' v, simScopeW towerOfCallName D S T A Γ e = some Γ' →
      haxToLowCT e = some c → evalImp bi fuel e env = some (v, env') →
      ScalarInv D S env → ScalarInv D S env')
    (heq : ∀ Γ Γ', simScopeW towerOfCallName D S T A Γ e = some Γ' →
      ∀ fuel env, evalImp bi fuel e env = evalImp bi' fuel e env)
    (h : ProgSimA bridge bi' N leafSpec S T A e) : ProgSimW bridge bi N leafSpec D S T A e := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  rw [hLoop Γ Γ' hScope] at hEval
  have hNN' := hInv Γ Γ' c fuel env env' v hScope hHax hEval hNN
  rw [heq Γ Γ' hScope] at hEval
  have hScopeA := hScope
  rw [hScopeEq] at hScopeA
  obtain ⟨rs', hExec, hAgree', hSB', hSF'⟩ :=
    h fuel Γ Γ' c env env' rs v hScopeA hConds hSB hSF hHax hEval hAgree
  exact ⟨rs', hExec, hAgree', hSB', hSF', hNN'⟩

theorem progSimW_seq (a b : ImpExpr)
    (iha : ProgSimW bridge bi N leafSpec D S T A a) (ihb : ProgSimW bridge bi N leafSpec D S T A b) :
    ProgSimW bridge bi N leafSpec D S T A (.seq a b) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  rcases hA : simScopeW towerOfCallName D S T A Γ a with _ | Γ₁
  · rw [hA] at hScope; cases hScope
  rw [hA] at hScope
  obtain ⟨aC, bC, hAtrans, hBtrans, hC⟩ := haxToLowCT_seq_some a b c hHax
  subst hC
  simp only [forToLoop] at hEval
  obtain ⟨vA, env_mid, hAeval, hBeval⟩ := evalImp_seq_inv bi fuel _ _ env v env' hEval
  obtain ⟨rs_mid, hAexec, hAgreeMid, hSBmid, hSFmid, hNNmid⟩ :=
    iha fuel Γ Γ₁ aC env env_mid rs vA hA hSB hSF hAtrans hAeval hAgree hNN
  obtain ⟨rs', hBexec, hAgree', hSB', hSF', hNN'⟩ :=
    ihb fuel Γ₁ Γ' bC env_mid env' rs_mid v hScope hSBmid hSFmid hBtrans hBeval hAgreeMid hNNmid
  rw [litTower_seq, arrTower_seq]
  exact ⟨rs', rustExec_RSeq_chain N leafSpec _ _ rs rs_mid rs' hAexec hBexec,
         hAgree', hSB', hSF', hNN'⟩

theorem progSimW_ifThenElse (cond : String) (t e : ImpExpr)
    (iht : ProgSimW bridge bi N leafSpec D S T A t) (ihe : ProgSimW bridge bi N leafSpec D S T A e) :
    ProgSimW bridge bi N leafSpec D S T A (.ifThenElse (.var cond) t e) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hCondS
  have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
  rcases hT : simScopeW towerOfCallName D S T A Γ t with _ | Γt
  · rw [hT] at hScope; cases hScope
  rcases hE : simScopeW towerOfCallName D S T A Γ e with _ | Γe
  · rw [hT, hE] at hScope; cases hScope
  rw [hT, hE] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ := haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  rw [litTower_ifNz, arrTower_ifNz]
  simp only [forToLoop] at hEval
  rcases evalImp_ifThenElse_var_inv bi fuel cond _ _ env v env' hEval with
    ⟨hCond, hTeval⟩ | ⟨hCond, hEeval⟩
  · obtain ⟨rs', hTexec, hAgree', hSB', hSF', hNN'⟩ :=
      iht fuel Γ Γt tC env env' rs v hT hSB hSF hTtrans hTeval hAgree hNN
    have hScalar : rs.rsScalar cond = 1 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_true N leafSpec cond _ _ rs rs' 1 hScalar
      (by decide) hTexec, hAgree', ?_, hSF', hNN'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γt
      (simScopeW_lookup_mono towerOfCallName D S T A t Γ Γt hT) hSB'
  · obtain ⟨rs', hEexec, hAgree', hSB', hSF', hNN'⟩ :=
      ihe fuel Γ Γe eC env env' rs v hE hSB hSF hEtrans hEeval hAgree hNN
    have hScalar : rs.rsScalar cond = 0 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond false hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_false N leafSpec cond _ _ rs rs' hScalar hEexec,
      hAgree', ?_, hSF', hNN'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γe
      (simScopeW_lookup_mono towerOfCallName D S T A e Γ Γe hE) hSB'

/-- The data-dependent loop arm, shared by `whileLoop (var cond)` and
    `whileFold (var cond)`: by induction on the fuel, each trip tests the scalar
    guard and runs the body's simulation. -/
theorem progSimW_whileNz (cond : String) (body : ImpExpr) (bC : LowCT) (Γ Γb : TowerScope)
    (hCondS : S.contains cond = true)
    (hB : simScopeW towerOfCallName D S T A Γ body = some Γb)
    (hBtrans : haxToLowCT body = some bC)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ∀ (fuel : Nat) (env env' : Env) (rs : RustState) (v : Value),
      ScopeBound rs Γ → NamesFresh rs S →
      evalImp bi fuel (.whileLoop (.var cond) (forToLoop body)) env = some (v, env') →
      envAgreesRustT bridge env rs → ScalarInv D S env →
      ∃ rs', RustExec N leafSpec (.RWhileNz cond (arrTower A (litTower T bC))) rs rs' ∧
        envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ ∧ NamesFresh rs' S ∧
        ScalarInv D S env' := by
  intro fuel
  have hAnf : AnfShaped body = true := (haxToLowCT_isSome_iff_anf body).mp (by rw [hBtrans]; rfl)
  have hMono := simScopeW_lookup_mono towerOfCallName D S T A body Γ Γb hB
  induction fuel with
  | zero =>
    intro env env' rs v _ _ hEval
    exact absurd hEval (fun h => evalImp_whileLoop_var_fuel_zero_inv bi cond _ env v env' h)
  | succ n IH =>
    intro env env' rs v hSB hSF hEval hAgree hNN
    have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
    rcases evalImp_whileLoop_var_step_inv bi n cond _ env v env' hEval
        (anfShaped_forToLoop_val_or_err bi body hAnf (n+1) env) with
      ⟨hCondF, hv, henv⟩ | ⟨vB, env_mid, hCondTrue, hBodyEval, hLoopRec⟩
    · subst hv
      subst henv
      have hScalar : rs.rsScalar cond = 0 :=
        envAgreesRustT_bool_to_scalar bridge _ rs cond false hAgree hCondT hCondF
      exact ⟨rs, RustExec.whileFalse cond _ rs hScalar, hAgree, hSB, hSF, hNN⟩
    · have hScalar : rs.rsScalar cond = 1 :=
        envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCondTrue
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid, hNNmid⟩ :=
        ihBody (n+1) Γ Γb bC env env_mid rs vB hB hSB hSF hBtrans hBodyEval hAgree hNN
      have hSBmid' : ScopeBound rs_mid Γ := ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid
      obtain ⟨rs', hLoopExec, hAgree', hSB', hSF', hNN'⟩ :=
        IH env_mid env' rs_mid v hSBmid' hSFmid hLoopRec hAgreeMid hNNmid
      exact ⟨rs', RustExec.whileTrue cond _ rs rs_mid rs' 1 hScalar (by decide)
               hBodyExec hLoopExec, hAgree', hSB', hSF', hNN'⟩

theorem progSimW_whileLoop (cond : String) (body : ImpExpr)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.whileLoop (.var cond) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hCondS
  rcases hB : simScopeW towerOfCallName D S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bC, hBtrans, hC⟩ := haxToLowCT_whileLoop_var_some cond body c hHax
  subst hC
  rw [litTower_whileNz, arrTower_whileNz]
  simp only [forToLoop] at hEval
  exact progSimW_whileNz bridge bi N leafSpec D S T A cond body bC Γ Γb hCondS hB hBtrans ihBody
    fuel env env' rs v hSB hSF hEval hAgree hNN

/-- The `whileFold` arm: a `whileFold` on a scalar guard is read as the
    `whileLoop` with the same guard and body and lowered to `RWhileNz`. -/
theorem progSimW_whileFold (cond : String) (body : ImpExpr)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.whileFold (.var cond) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hCondS
  rcases hB : simScopeW towerOfCallName D S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bC, hBtrans, hC⟩ := haxToLowCT_whileFold_var_some cond body c hHax
  subst hC
  rw [litTower_whileNz, arrTower_whileNz]
  simp only [forToLoop] at hEval
  exact progSimW_whileNz bridge bi N leafSpec D S T A cond body bC Γ Γb hCondS hB hBtrans ihBody
    fuel env env' rs v hSB hSF hEval hAgree hNN

/-- The trips of a counted loop: by induction on the number of trips left, each
    trip binds the counter to its value in the environment and in the scalar
    heap and runs the body's simulation, whose exit scope extends the loop's
    scope. -/
theorem tripsFrom_of_forLoop (i : String) (lo hi : Int) (body : ImpExpr) (bodyC : LowCT)
    (Γ Γb : TowerScope) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hiS : S.contains i = true)
    (hB : simScopeW towerOfCallName D S T A Γ body = some Γb)
    (hBtrans : haxToLowCT body = some bodyC)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ∀ (d j fuel : Nat) (env env'' : Env) (rs : RustState) (w : Value),
      j + d = hi.toNat - lo.toNat → ScopeBound rs Γ → NamesFresh rs S →
      envAgreesRustT bridge env rs → ScalarInv D S env →
      (denoteForLoop bi fuel i (lo + j) hi (forToLoop body)).run env = (.val w, env'') →
      ∃ rs', TripsFrom N leafSpec i (arrTower A (litTower T (forShift i lo.toNat bodyC))) j d rs rs' ∧
        envAgreesRustT bridge env'' rs' ∧ ScopeBound rs' Γ ∧ NamesFresh rs' S ∧
        ScalarInv D S env'' := by
  have hAnf : AnfShaped body = true := (haxToLowCT_isSome_iff_anf body).mp (by rw [hBtrans]; rfl)
  have hMono := simScopeW_lookup_mono towerOfCallName D S T A body Γ Γb hB
  have hloN := Int.toNat_of_nonneg hlo
  have hhiN := Int.toNat_of_nonneg hhi
  intro d
  induction d with
  | zero =>
    intro j fuel env env'' rs w hj hSB hSF hAgree hNN hRun
    rw [denoteForLoop_ge_run bi fuel i (lo + j) hi _ env (by omega)] at hRun
    injection hRun with _ h2
    subst h2
    exact ⟨rs, rfl, hAgree, hSB, hSF, hNN⟩
  | succ d ih =>
    intro j fuel env env'' rs w hj hSB hSF hAgree hNN hRun
    have hlt : lo + j < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop_zero_run bi i (lo + j) hi _ env hlt] at hRun
      injection hRun with h1
      cases h1
    | succ m =>
      rw [denoteForLoop_succ_run bi m i (lo + j) hi _ env hlt] at hRun
      rcases anfShaped_forToLoop_val_or_err bi body hAnf (m + 1)
          (env.extend i (.int (lo + j))) with ⟨vB, envB, hb⟩ | ⟨msg, envB, hb⟩
      swap
      · rw [hb] at hRun
        injection hRun with h1
        cases h1
      rw [hb] at hRun
      have hTi : rs.rsTower i = none := hSF i (mem_of_contains S i hiS)
      have hAgree1 : envAgreesRustT bridge (env.extend i (.int (lo + j)))
          (rsSetScalar rs i (lo.toNat + j)) :=
        envAgreesRustT_extend_scalar_fresh bridge env rs i _ _ hTi
          (by simp only [valueToScalar]; rw [if_pos (by omega)]; congr 1; omega) hAgree
      have hNN1 : ScalarInv D S (env.extend i (.int (lo + j))) :=
        hNN.extend_of_nonneg i (fun k hk => by
          simp only [Value.int.injEq] at hk; omega)
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid, hNNmid⟩ :=
        ihBody (m + 1) Γ Γb bodyC _ envB (rsSetScalar rs i (lo.toNat + j)) vB hB hSB hSF hBtrans
          (by unfold evalImp; rw [hb]) hAgree1 hNN1
      have hStep := forShift_exec N leafSpec T A i lo.toNat j bodyC rs rs_mid hBodyExec
      have hRun' : (denoteForLoop bi m i (lo + ((j + 1 : Nat) : Int)) hi (forToLoop body)).run envB =
          (.val w, env'') := by
        rw [show lo + ((j + 1 : Nat) : Int) = lo + j + 1 by push_cast; ring]
        exact hRun
      obtain ⟨rs', hTrips, hA', hSB', hSF', hNN'⟩ :=
        ih (j + 1) m envB env'' rs_mid w (by omega)
          (ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid) hSFmid hAgreeMid hNNmid hRun'
      exact ⟨rs', ⟨rs_mid, hStep, hTrips⟩, hA', hSB', hSF', hNN'⟩

/-- The trips of a reverse counted loop: as `tripsFrom_of_forLoop`, with the
    counter bound to `hi - 1 - j` at trip `j`. -/
theorem tripsFrom_of_forLoopRev (i : String) (lo hi : Int) (body : ImpExpr) (bodyC : LowCT)
    (Γ Γb : TowerScope) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hiS : S.contains i = true)
    (hB : simScopeW towerOfCallName D S T A Γ body = some Γb)
    (hBtrans : haxToLowCT body = some bodyC)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ∀ (d j fuel : Nat) (env env'' : Env) (rs : RustState) (w : Value),
      j + d = hi.toNat - lo.toNat → ScopeBound rs Γ → NamesFresh rs S →
      envAgreesRustT bridge env rs → ScalarInv D S env →
      (denoteForLoopRev bi fuel i lo (hi - j) (forToLoop body)).run env = (.val w, env'') →
      ∃ rs', TripsFrom N leafSpec i (arrTower A (litTower T (revShift i hi.toNat bodyC))) j d rs rs' ∧
        envAgreesRustT bridge env'' rs' ∧ ScopeBound rs' Γ ∧ NamesFresh rs' S ∧
        ScalarInv D S env'' := by
  have hAnf : AnfShaped body = true := (haxToLowCT_isSome_iff_anf body).mp (by rw [hBtrans]; rfl)
  have hMono := simScopeW_lookup_mono towerOfCallName D S T A body Γ Γb hB
  have hloN := Int.toNat_of_nonneg hlo
  have hhiN := Int.toNat_of_nonneg hhi
  intro d
  induction d with
  | zero =>
    intro j fuel env env'' rs w hj hSB hSF hAgree hNN hRun
    rw [denoteForLoopRev_ge_run bi fuel i lo (hi - j) _ env (by omega)] at hRun
    injection hRun with _ h2
    subst h2
    exact ⟨rs, rfl, hAgree, hSB, hSF, hNN⟩
  | succ d ih =>
    intro j fuel env env'' rs w hj hSB hSF hAgree hNN hRun
    have hlt : lo < hi - j := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoopRev_zero_run bi i lo (hi - j) _ env hlt] at hRun
      injection hRun with h1
      cases h1
    | succ m =>
      rw [denoteForLoopRev_succ_run bi m i lo (hi - j) _ env hlt] at hRun
      rcases anfShaped_forToLoop_val_or_err bi body hAnf (m + 1)
          (env.extend i (.int (hi - j - 1))) with ⟨vB, envB, hb⟩ | ⟨msg, envB, hb⟩
      swap
      · rw [hb] at hRun
        injection hRun with h1
        cases h1
      rw [hb] at hRun
      have hTi : rs.rsTower i = none := hSF i (mem_of_contains S i hiS)
      have hAgree1 : envAgreesRustT bridge (env.extend i (.int (hi - j - 1)))
          (rsSetScalar rs i (hi.toNat - 1 - j)) :=
        envAgreesRustT_extend_scalar_fresh bridge env rs i _ _ hTi
          (by simp only [valueToScalar]; rw [if_pos (by omega)]; congr 1; omega) hAgree
      have hNN1 : ScalarInv D S (env.extend i (.int (hi - j - 1))) :=
        hNN.extend_of_nonneg i (fun k hk => by
          simp only [Value.int.injEq] at hk; omega)
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid, hNNmid⟩ :=
        ihBody (m + 1) Γ Γb bodyC _ envB (rsSetScalar rs i (hi.toNat - 1 - j)) vB hB hSB hSF hBtrans
          (by unfold evalImp; rw [hb]) hAgree1 hNN1
      have hStep := revShift_exec N leafSpec T A i hi.toNat j bodyC rs rs_mid hBodyExec
      have hRun' : (denoteForLoopRev bi m i lo (hi - ((j + 1 : Nat) : Int)) (forToLoop body)).run
          envB = (.val w, env'') := by
        rw [show hi - ((j + 1 : Nat) : Int) = hi - j - 1 by push_cast; ring]
        exact hRun
      obtain ⟨rs', hTrips, hA', hSB', hSF', hNN'⟩ :=
        ih (j + 1) m envB env'' rs_mid w (by omega)
          (ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid) hSFmid hAgreeMid hNNmid hRun'
      exact ⟨rs', ⟨rs_mid, hStep, hTrips⟩, hA', hSB', hSF', hNN'⟩

/-- The counted-loop arm with literal bounds. -/
theorem progSimW_forFold (i : String) (lo hi : Int) (body : ImpExpr)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.forFold i (.lit (.int lo)) (.lit (.int hi)) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hlo, hhi⟩, hiS⟩ := hc
  rcases hB : simScopeW towerOfCallName D S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bodyC, hBtrans, rfl⟩ := haxToLowCT_forFold_lit_some i lo hi body c hlo hhi hHax
  rw [litTower_for, arrTower_for]
  have hRun : (denoteForLoop bi fuel i lo hi (forToLoop body)).run env = (.val v, env') := by
    simp only [forToLoop] at hEval
    unfold evalImp at hEval
    rw [denote_forLoop_lit_run] at hEval
    split at hEval
    · rename_i w e1 hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hw
    · cases hEval
  obtain ⟨rs', hTrips, hA', hSB', hSF', hNN'⟩ :=
    tripsFrom_of_forLoop bridge bi N leafSpec D S T A i lo hi body bodyC Γ Γb hlo hhi hiS hB hBtrans
      ihBody (hi.toNat - lo.toNat) 0 fuel env env' rs v (by omega) hSB hSF hAgree hNN
      (by simpa using hRun)
  have hExec := rustExec_rFor_of_tripsFrom N leafSpec i _ (hi.toNat - lo.toNat) 0 rs rs rs'
    (RustExec.forZero i _ rs) hTrips
  rw [Nat.zero_add] at hExec
  exact ⟨rs', hExec, hA', hSB', hSF', hNN'⟩

/-- A `forLoop` from an integer literal to a variable bound holding a value
    that is not an integer runs to an error. -/
theorem denote_forLoop_lit_var_nonint (fuel : Nat) (v : String) (lo : Int) (n : String)
    (body : ImpExpr) (env : Env) (w : Value) (hw : env n = some w)
    (hk : ∀ k : Int, w ≠ .int k) :
    (denote bi fuel (.forLoop v (.lit (.int lo)) (.var n) body)).run env =
      (.err "for loop bounds must be integers", env) := by
  cases w with
  | int k => exact absurd rfl (hk k)
  | _ =>
    simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure,
      Value.ofLit, get, getThe, MonadStateOf.get, StateT.get, hw]

/-- The counted-loop arm with a variable bound: the bound holds a non-negative
    integer, which is the scalar `RForRuntime` evaluates. -/
theorem progSimW_forFold_var (i : String) (lo : Int) (n : String) (body : ImpExpr)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.forFold i (.lit (.int lo)) (.var n) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hlo, hiS⟩, hnS⟩, hnD⟩ := hc
  rcases hB : simScopeW towerOfCallName D S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bodyC, hBtrans, rfl⟩ := haxToLowCT_forFold_var_some i lo n body c hlo hHax
  simp only [forToLoop] at hEval
  unfold evalImp at hEval
  -- The bound holds a non-negative integer `k`.
  obtain ⟨w, hw⟩ := hNN.1 n (mem_of_contains D n hnD)
  obtain ⟨k, hk⟩ : ∃ k : Int, env n = some (.int k) := by
    by_contra hne
    push_neg at hne
    rw [denote_forLoop_lit_var_nonint bi fuel i lo n (forToLoop body) env w hw
      (fun k hk => hne k (hk ▸ hw))] at hEval
    cases hEval
  have hk0 : 0 ≤ k := hNN.2 n (mem_of_contains S n hnS) k hk
  have hTn : rs.rsTower n = none := hSF n (mem_of_contains S n hnS)
  have hScalar : rs.rsScalar n = k.toNat :=
    hAgree.1 n (.int k) k.toNat hk hTn (by simp [valueToScalar, hk0])
  rw [denote_forLoop_lit_var_run bi fuel i lo n k _ env hk] at hEval
  have hRun : (denoteForLoop bi fuel i lo k (forToLoop body)).run env = (.val v, env') := by
    split at hEval
    · rename_i w e1 hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hw
    · cases hEval
  obtain ⟨rs', hTrips, hA', hSB', hSF', hNN'⟩ :=
    tripsFrom_of_forLoop bridge bi N leafSpec D S T A i lo k body bodyC Γ Γb hlo hk0 hiS hB hBtrans
      ihBody (k.toNat - lo.toNat) 0 fuel env env' rs v (by omega) hSB hSF hAgree hNN
      (by simpa using hRun)
  have hExec := rustExec_rFor_of_tripsFrom N leafSpec i _ (k.toNat - lo.toNat) 0 rs rs rs'
    (RustExec.forZero i _ rs) hTrips
  rw [Nat.zero_add] at hExec
  refine ⟨rs', ?_, hA', hSB', hSF', hNN'⟩
  split
  · rename_i h0
    rw [forShift, if_pos h0] at hExec
    rw [litTower_forRuntime, arrTower_forRuntime]
    refine RustExec.forRuntime i _ _ rs rs' ?_
    have hE : (SExpr.SVar n).evalState rs = k.toNat - lo.toNat := by
      simp [SExpr.evalState, hScalar, h0]
    rw [hE]
    exact hExec
  · rename_i h0
    rw [forShift, if_neg h0] at hExec
    rw [litTower_forRuntime, arrTower_forRuntime]
    refine RustExec.forRuntime i _ _ rs rs' ?_
    have hE : (SExpr.SSub (.SVar n) (.SLit lo.toNat)).evalState rs = k.toNat - lo.toNat := by
      simp [SExpr.evalState, hScalar]
    rw [hE]
    exact hExec

/-- The reverse counted-loop arm with literal bounds. -/
theorem progSimW_forFoldRev (i : String) (lo hi : Int) (body : ImpExpr)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hlo, hhi⟩, hiS⟩ := hc
  rcases hB : simScopeW towerOfCallName D S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bodyC, hBtrans, rfl⟩ := haxToLowCT_forFoldRev_lit_some i lo hi body c hlo hhi hHax
  rw [litTower_for, arrTower_for]
  have hRun : (denoteForLoopRev bi fuel i lo hi (forToLoop body)).run env = (.val v, env') := by
    simp only [forToLoop] at hEval
    unfold evalImp at hEval
    rw [denote_forLoopRev_lit_run] at hEval
    split at hEval
    · rename_i w e1 hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hw
    · cases hEval
  obtain ⟨rs', hTrips, hA', hSB', hSF', hNN'⟩ :=
    tripsFrom_of_forLoopRev bridge bi N leafSpec D S T A i lo hi body bodyC Γ Γb hlo hhi hiS hB
      hBtrans ihBody (hi.toNat - lo.toNat) 0 fuel env env' rs v (by omega) hSB hSF hAgree hNN
      (by simpa using hRun)
  have hExec := rustExec_rFor_of_tripsFrom N leafSpec i _ (hi.toNat - lo.toNat) 0 rs rs rs'
    (RustExec.forZero i _ rs) hTrips
  rw [Nat.zero_add] at hExec
  exact ⟨rs', hExec, hA', hSB', hSF', hNN'⟩

theorem progSimW_letBind_lit (name : String) (l : ImpLit) (body : ImpExpr)
    (hLit : LitStoreAgrees bridge leafSpec)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.letBind name (.lit l) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  obtain ⟨bodyC, m, hBodyTrans, hDecode, hC⟩ := haxToLowCT_letBind_lit_some name l body c hHax
  subst hC
  simp only [forToLoop] at hEval
  have hBodyEval := evalImp_letBind_lit_inv bi fuel name l _ env v env' hEval
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
      rw [litTower_lit_mem T name k bodyC hTm, arrTower_letZero, arrTower_seq, arrTower_limbStore]
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
      have hNNmid : ScalarInv D S (env.extend name (Value.ofLit l)) :=
        hNN.extend_of_not_mem hNotMem _
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF', hNN'⟩ :=
        ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC _ env' _ v hScope hSBmid hSFmid
          hBodyTrans hBodyEval hAgreeMid hNNmid
      exact ⟨rs', RustExec.letZero name .TFp _ rs rs'
        (RustExec.seq _ _ _ _ _ hStore hBodyExec), hAgree', hSB', hSF', hNN'⟩
    · cases hScope
  · rw [if_neg hTm] at hScope
    split at hScope
    · rename_i hIn
      rw [litTower_lit_not_mem T name m bodyC (by simpa using hTm), arrTower_letU64Zero,
        arrTower_seq, arrTower_scalarSet]
      have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
      have hAgreeExt : envAgreesRustT bridge (env.extend name (Value.ofLit l))
                        (rsSetScalar rs name m) :=
        envAgreesRustT_extend_scalar_fresh bridge env rs name (Value.ofLit l) m hFresh hDecode
          hAgree
      have hNNmid : ScalarInv D S (env.extend name (Value.ofLit l)) :=
        hNN.extend_of_nonneg name (nonneg_of_valueToScalar hDecode)
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF', hNN'⟩ :=
        ihBody fuel Γ Γ' bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name m) v
          hScope hSB hSF hBodyTrans hBodyEval hAgreeExt hNNmid
      exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name m _ rs rs' hBodyExec,
             hAgree', hSB', hSF', hNN'⟩
    · cases hScope

theorem progSimW_letBind_var (name src : String) (body : ImpExpr)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.letBind name (.var src) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  · rename_i hEq
    subst hEq
    have hHax' : haxToLowCT body = some c := by
      simp only [haxToLowCT] at hHax
      exact hHax
    simp only [forToLoop] at hEval
    obtain ⟨w, hw, hBodyEval⟩ := evalImp_letBind_var_inv bi fuel _ _ _ env v env' hEval
    rw [Env.extend_self env _ w hw] at hBodyEval
    exact ihBody fuel Γ Γ' c env env' rs v hScope hSB hSF hHax' hBodyEval hAgree hNN
  · cases hScope

theorem progSimW_letBind_app (name f : String) (args : List ImpExpr) (body : ImpExpr)
    (hLeaf : LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hf_arr : f ≠ "array_update") (hf_idx : f ≠ "index") (hf_sc : scalarCallName f = false)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.letBind name (.app f args) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW, if_neg hf_arr, if_neg hf_idx, hf_sc, Bool.false_eq_true, if_false] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hArgsIn, hAvoid⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
      haxToLowCT_letBind_app_some name f args body c hf_arr hf_idx hf_sc hHax
    subst hC
    rw [litTower_letZero, litTower_seq, litTower_call, arrTower_letZero, arrTower_seq, arrTower_call]
    have hAllVar := argsInScope_allVars Γ _ args hArgsIn
    simp only [forToLoop] at hEval
    rw [forToLoopArgs_of_vars args hAllVar] at hEval
    have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f args _ env v env'
      hAllVar hEval
    obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
      evalImp_letBind_app_vars_inv bi fuel name f args _ env v env' hArgsEnv hEval
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
    have hNNmid : ScalarInv D S (env.extend name vRes) := hNN.extend_of_not_mem hNotMem _
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF', hNN'⟩ :=
      ihBody fuel ((name, dt) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
        hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid hNNmid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF', hNN'⟩
    refine RustExec.letZero name dt _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hCall hBodyExec
  · cases hScope

/-- The natural-number operation of a call computed in the scalar heap. -/
def scalarCallNat (f : String) : Option (Nat → Nat → Nat) :=
  match f with
  | "scalar#Add" => some (· + ·)
  | "scalar#Sub" => some (· - ·)
  | "scalar#Mul" => some (· * ·)
  | "scalar#BitAnd" => some (· &&& ·)
  | "scalar#BitXor" => some (· ^^^ ·)
  | "scalar#Shr" => some (· >>> ·)
  | "scalar#Shl" => some (· <<< ·)
  | "scalar#Lt" => some fun a b => if a < b then 1 else 0
  | "scalar#Gt" => some fun a b => if b < a then 1 else 0
  | "scalar#Le" => some fun a b => if a ≤ b then 1 else 0
  | "scalar#Ge" => some fun a b => if b ≤ a then 1 else 0
  | "scalar#Eq" => some fun a b => if a = b then 1 else 0
  | "scalar#Ne" => some fun a b => if a = b then 0 else 1
  | _ => none

theorem scalarCallNat_of_sexpr {f : String} {a b se : SExpr}
    (h : scalarCallSExpr f a b = some se) : ∃ k, scalarCallNat f = some k := by
  unfold scalarCallSExpr at h
  unfold scalarCallNat
  split at h <;> first | exact ⟨_, rfl⟩ | cases h

/-- The scalar expression of a call evaluates to its natural-number operation on
    the values of the operands. -/
theorem scalarCallSExpr_eval {f : String} {ea eb se : SExpr} {k : Nat → Nat → Nat}
    (hk : scalarCallNat f = some k) (hse : scalarCallSExpr f ea eb = some se)
    (σ : String → Nat) : se.eval σ = k (ea.eval σ) (eb.eval σ) := by
  unfold scalarCallSExpr at hse
  unfold scalarCallNat at hk
  split at hse <;> cases hse <;> cases hk <;> simp only [SExpr.eval] <;> split_ifs <;> omega

/-- The scalar expression of a call on two `limbFree` operands is `limbFree`. -/
theorem scalarCallSExpr_limbFree {f : String} {ea eb se : SExpr}
    (hse : scalarCallSExpr f ea eb = some se) (ha : ea.limbFree) (hb : eb.limbFree) :
    se.limbFree := by
  unfold scalarCallSExpr at hse
  split at hse <;> cases hse <;> simp [SExpr.limbFree, ha, hb]

/-- The builtin table agrees with the calls computed in the scalar heap: such a
    call succeeds only on two values with scalar readings, and its result reads
    as the natural-number operation on them.

    `scalarCallNat` reads `scalar#Add`, `scalar#Mul` and `scalar#Shl` as unbounded
    `+`, `*` and `<<<` and `scalar#Sub` as saturating subtraction. Rust `u64` `<<`
    truncates and `+`/`*` wrap or panic, so a table faithful to Rust satisfies this
    condition only by refusing every call whose result is at least the word bound
    `2^64`. Every theorem that takes `ScalarCallsAgree` as a hypothesis (including
    `lowCTToImp_simulates`, `lowCTToImp_simulates_frontNF` and
    `roundTrip_hax_simulates`) therefore holds only on runs
    whose intermediate values stay below the word bound; on a wrapping run the
    hypothesis fails and the theorem says nothing. -/
def ScalarCallsAgree (bi : Builtins) : Prop :=
  ∀ (f : String) (k : Nat → Nat → Nat) (va vb r : Value), scalarCallNat f = some k →
    bi f [va, vb] = some r →
    ∃ n m, valueToScalar va = some n ∧ valueToScalar vb = some m ∧
      valueToScalar r = some (k n m)

theorem evalImp_letBind_app2_inv (bi : Builtins) (fuel : Nat) (name f a b : String)
    (body : ImpExpr) (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.letBind name (.app f [.var a, .var b]) body) env = some (v, env')) :
    ∃ va vb r, env a = some va ∧ env b = some vb ∧ bi f [va, vb] = some r ∧
      evalImp bi fuel body (env.extend name r) = some (v, env') := by
  unfold evalImp at h ⊢
  have hNil : (denoteArgs bi fuel ([] : List ImpExpr)).run env = (some [], env) := by
    unfold denoteArgs; rfl
  rw [denote_letBind_run_eq, denote_app_run_eq, denoteArgs_cons_run_eq, denote_var_run_eq] at h
  cases ha : env a with
  | none => rw [ha] at h; simp at h
  | some va =>
    rw [ha] at h
    simp only at h
    rw [denoteArgs_cons_run_eq, denote_var_run_eq] at h
    cases hb : env b with
    | none => rw [hb] at h; simp at h
    | some vb =>
      rw [hb] at h
      simp only at h
      rw [hNil] at h
      simp only [Option.map_some] at h
      cases hbi : bi f [va, vb] with
      | none => rw [hbi] at h; simp at h
      | some r =>
        rw [hbi] at h
        exact ⟨va, vb, r, rfl, rfl, hbi, h⟩

theorem litTower_letU64Zero_scalarSetExpr (T : List String) (x y : String) (e : SExpr)
    (b : LowCT) :
    litTower T (.RLetU64Zero x (.RSeq (.RScalarSetExpr y e) b)) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr y e) (litTower T b)) := by
  simp [litTower]

/-- The arm of a call computed in the scalar heap: `let name = f(a, b)` with
    `name`, `a` and `b` scalar names and `a`, `b` distinct from `name` runs
    `RScalarSetExpr name e` for the scalar expression `e` of `f`, and the body
    from the extended scalar heap. -/
theorem progSimW_letBind_scalar (name f a b : String) (body : ImpExpr)
    (hSc : ScalarCallsAgree bi) (hf_sc : scalarCallName f = true)
    (hf_arr : f ≠ "array_update") (hf_idx : f ≠ "index")
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.letBind name (.app f [.var a, .var b]) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW, if_neg hf_arr, if_neg hf_idx, hf_sc, ↓reduceIte] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨⟨hName, ha⟩, hb⟩, hna⟩, hnb⟩ := hS
  obtain ⟨se, hse⟩ : ∃ se, scalarCallSExpr f (.SVar a) (.SVar b) = some se :=
    Option.isSome_iff_exists.mp (by rw [scalarCallSExpr_isSome]; exact hf_sc)
  have hHax' : ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = .RLetU64Zero name (.RSeq (.RScalarSetExpr name se) bodyC) := by
    simp only [haxToLowCT, haxArgsToLocated, haxArgToLocated] at hHax
    cases hB : haxToLowCT body with
    | none => simp [hB] at hHax
    | some bodyC =>
      simp only [hB, if_neg hf_arr, if_neg hf_idx, hf_sc, ↓reduceIte, hse,
        Option.some.injEq] at hHax
      exact ⟨bodyC, rfl, hHax.symm⟩
  obtain ⟨bodyC, hB, rfl⟩ := hHax'
  simp only [forToLoop, forToLoopArgs] at hEval
  obtain ⟨va, vb, r, hva, hvb, hbi, hBodyEval⟩ :=
    evalImp_letBind_app2_inv bi fuel name f a b _ env v env' hEval
  obtain ⟨k, hk⟩ := scalarCallNat_of_sexpr hse
  obtain ⟨n, m, hn, hm, hr⟩ := hSc f k va vb r hk hbi
  have hTa : rs.rsTower a = none := hSF a (mem_of_contains S a ha)
  have hTb : rs.rsTower b = none := hSF b (mem_of_contains S b hb)
  have hsa : rs.rsScalar a = n := hAgree.1 a va n hva hTa hn
  have hsb : rs.rsScalar b = m := hAgree.1 b vb m hvb hTb hm
  have hEvalSe : se.evalState (rsSetScalar rs name 0) = k n m := by
    rw [SExpr.evalState_eq_eval _ se
      (scalarCallSExpr_limbFree hse (by simp [SExpr.limbFree]) (by simp [SExpr.limbFree])),
      scalarCallSExpr_eval hk hse]
    simp [SExpr.eval, rsSetScalar, hna, hnb, hsa, hsb]
  have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hName)
  have hAgree' :=
    envAgreesRustT_extend_scalar_fresh bridge env rs name r (k n m) hFresh hr hAgree
  have hNN' : ScalarInv D S (env.extend name r) :=
    hNN.extend_of_nonneg name (nonneg_of_valueToScalar hr)
  obtain ⟨rs', hBodyExec, hAgreeF, hSB', hSF', hNNF⟩ :=
    ihBody fuel Γ Γ' bodyC (env.extend name r) env' (rsSetScalar rs name (k n m)) v hScope hSB
      hSF hB hBodyEval hAgree' hNN'
  refine ⟨rs', ?_, hAgreeF, hSB', hSF', hNNF⟩
  rw [litTower_letU64Zero_scalarSetExpr, arrTower_letU64Zero, arrTower_seq, arrTower_scalarSetExpr]
  refine RustExec.letU64Zero name _ rs rs' ?_
  refine RustExec.seq _ _ _ (rsSetScalar rs name (k n m)) _ ?_ hBodyExec
  have hS := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) name se (rsSetScalar rs name 0)
  rw [hEvalSe, rsSetScalar_collapse] at hS
  exact hS

theorem progSimW_letBind_proj (name t : String) (i : Nat) (body : ImpExpr)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.letBind name (.proj (.var t) i) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hLk, hNe⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_proj_some name t i body c hHax
    subst hC
    rw [litTower_letZero, litTower_seq, litTower_tupleLoad, arrTower_letZero, arrTower_seq,
      arrTower_tupleLoad]
    simp only [forToLoop] at hEval
    obtain ⟨vTup, vi, hEnvT, hProjI, hBodyEval⟩ :=
      evalImp_letBind_proj_inv bi fuel name t i _ env v env' hEval
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
    have hNNmid : ScalarInv D S (env.extend name vi) := hNN.extend_of_not_mem hNotMem _
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF', hNN'⟩ :=
      ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vi) env' rs_mid v
        hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid hNNmid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF', hNN'⟩
    refine RustExec.letZero name .TFp _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hLoad hBodyExec
  · cases hScope

theorem progSimW_letBind_index (name f arr idx : String) (body : ImpExpr)
    (hf_arr : f ≠ "array_update") (hf_idx : f = "index")
    (hIdx : IndexAgrees bridge bi leafSpec)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A (.letBind name (.app f [.var arr, .var idx]) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW, if_neg hf_arr, if_pos hf_idx] at hScope
  rcases hA : List.lookup arr A with _ | t
  · rw [hA] at hScope; cases hScope
  simp only [hA] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hLk, hNe⟩, hIdxS'⟩, hCompat⟩, hNotS⟩ := hc
  have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
  have hIdxS : idx ∈ S := mem_of_contains S idx hIdxS'
  obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_index_some name f arr idx body c hf_arr hf_idx hHax
  subst hC
  rw [litTower_letZero, litTower_seq, litTower_arrLoad, arrTower_letZero, arrTower_seq,
    arrTower_arrLoad A _ { locVar := arr, locSrc := .TFp } idx t hA]
  simp only [forToLoop, forToLoopArgs] at hEval
  have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f [.var arr, .var idx] _ env v
    env' (by simp) hEval
  obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
    evalImp_letBind_app_vars_inv bi fuel name f _ _ env v env' hArgsEnv hEval
  obtain ⟨vArr, vIdx, rfl, hvArr, hvIdx⟩ := allVars_two hAV
  subst hf_idx
  obtain ⟨arrV, hRawArr⟩ := hSB arr t hLk
  have hTIdx : rs.rsTower idx = none := hSF idx hIdxS
  have hk : ∀ n, valueToScalar vIdx = some n → n = rs.rsScalar idx :=
    fun n hn => (hAgree.1 idx vIdx n hvIdx hTIdx hn).symm
  set dst : Located := { locVar := name, locSrc := .TFp } with hdst
  set src : Located := { locVar := arr, locSrc := t } with hsrc
  set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
  have hDstLook : locatedLookup rs_init dst = some default := locatedLookup_letZero rs name .TFp
  have hSrcLook : locatedLookup rs_init src = some arrV := by
    rw [hrs_init, CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
      rs name ⟨.TFp, default⟩ src (Ne.symm hNe)]
    exact locatedLookup_of_rsTower rs arr t arrV hRawArr
  set newVal := leafSpec.arrLoad dst default ⟨t, arrV⟩ (rs.rsScalar idx) with hnewVal
  set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
  have hLoad : RustExec N leafSpec (.RArrLoad dst src idx) rs_init rs_mid :=
    RustExec.arrLoad dst src idx rs_init (rs.rsScalar idx) default arrV rfl hDstLook hSrcLook
  have hB : bridge .TFp vRes newVal :=
    hIdx name t vArr vIdx vRes arrV (rs.rsScalar idx) (hAgree.2 arr vArr hvArr t arrV hRawArr)
      hk hBi
  have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
    show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
        = rsSetTower rs name ⟨.TFp, newVal⟩
    exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
  have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) rs_mid := by
    rw [hRsMidEq]
    exact envAgreesRustT_extend_tower bridge env rs name vRes .TFp newVal hAgree hB
  have hSBmid : ScopeBound rs_mid ((name, .TFp) :: Γ) := by
    rw [hRsMidEq]
    exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
  have hSFmid : NamesFresh rs_mid S := by
    rw [hRsMidEq]
    exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
  have hNNmid : ScalarInv D S (env.extend name vRes) := hNN.extend_of_not_mem hNotMem _
  obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF', hNN'⟩ :=
    ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
      hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid hNNmid
  refine ⟨rs', ?_, hAgreeFinal, hSB', hSF', hNN'⟩
  refine RustExec.letZero name .TFp _ rs rs' ?_
  exact RustExec.seq _ _ _ _ _ hLoad hBodyExec

/-- The arm of a limb read: `let name = index(v, k)` at a non-negative integer
    literal `k`, with `name` a scalar name and `v` in scope at a type that is not
    a container, runs `RScalarSetExpr name (SLimb v k)`, and the body from the
    extended scalar heap. -/
theorem progSimW_letBind_limb (name f v : String) (k : Int) (body : ImpExpr)
    (hf_arr : f ≠ "array_update") (hf_idx : f = "index")
    (hLimb : LimbReadAgrees bridge bi)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A
      (.letBind name (.app f [.var v, .lit (.int k)]) body) := by
  intro fuel Γ Γ' c env env' rs w hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW, if_neg hf_arr, if_pos hf_idx] at hScope
  subst hf_idx
  rcases hL : List.lookup v Γ with _ | t
  · rw [hL] at hScope; cases hScope
  simp only [hL] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨ht, hk⟩, hName⟩ := hc
  obtain ⟨bodyC, hB, rfl⟩ := haxToLowCT_letBind_limb_some name v k hk body c hHax
  obtain ⟨arrV, hT⟩ := hSB v t hL
  simp only [forToLoop, forToLoopArgs] at hEval
  rw [litTower_letU64Zero_scalarSetExpr, arrTower_letU64Zero, arrTower_seq, arrTower_scalarSetExpr]
  have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hName)
  refine limbRead_sim bridge bi N leafSpec hLimb name v k hk _ _ fuel env env' rs w t arrV ht hT
    hFresh hEval hAgree
    (fun rs' => envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S ∧
      ScalarInv D S env') ?_
  intro r n hr hBodyEval hAgree'
  exact ihBody fuel Γ Γ' bodyC (env.extend name r) env' (rsSetScalar rs name n) w hScope hSB hSF hB
    hBodyEval hAgree' (hNN.extend_of_nonneg name (nonneg_of_valueToScalar hr))

theorem progSimW_letBind_arrUpdate (name f arr idx src : String) (body : ImpExpr)
    (hf_arr : f = "array_update")
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (ihBody : ProgSimW bridge bi N leafSpec D S T A body) :
    ProgSimW bridge bi N leafSpec D S T A
      (.letBind name (.app f [.var arr, .var idx, .var src]) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW, if_pos hf_arr] at hScope
  rcases hA : List.lookup arr A with _ | t
  · rw [hA] at hScope; cases hScope
  simp only [hA] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hName, hLk⟩, hLkSrc⟩, hIdxS'⟩ := hc
  have hIdxS : idx ∈ S := mem_of_contains S idx hIdxS'
  subst hName
  obtain ⟨bodyC, hBodyT, hC⟩ :=
    haxToLowCT_letBind_arrUpdate_some name f name idx src body c hf_arr hHax
  subst hC
  rw [litTower_seq, litTower_arrStore, arrTower_seq,
    arrTower_arrStore A { locVar := name, locSrc := .TBytes 0 } { locVar := src, locSrc := .TBytes 0 }
      idx t hA]
  simp only [forToLoop, forToLoopArgs] at hEval
  have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f
    [.var name, .var idx, .var src] _ env v env' (by simp) hEval
  obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
    evalImp_letBind_app_vars_inv bi fuel name f _ _ env v env' hArgsEnv hEval
  obtain ⟨vArr, vIdx, vSrc, rfl, hvArr, hvIdx, hvSrc⟩ := allVars_three hAV
  subst hf_arr
  obtain ⟨arrV, hRawArr⟩ := hSB name t hLk
  obtain ⟨srcV, hRawSrc⟩ := hSB src t.elemType hLkSrc
  have hTIdx : rs.rsTower idx = none := hSF idx hIdxS
  have hk : ∀ n, valueToScalar vIdx = some n → n = rs.rsScalar idx :=
    fun n hn => (hAgree.1 idx vIdx n hvIdx hTIdx hn).symm
  have hNotMem : name ∉ S := by
    intro hm
    rw [hSF name hm] at hRawArr
    cases hRawArr
  set arrL : Located := { locVar := name, locSrc := t } with harrL
  set srcL : Located := { locVar := src, locSrc := t.elemType } with hsrcL
  have hArrLook : locatedLookup rs arrL = some arrV := locatedLookup_of_rsTower rs name t arrV hRawArr
  have hSrcLook : locatedLookup rs srcL = some srcV :=
    locatedLookup_of_rsTower rs src t.elemType srcV hRawSrc
  set newVal := leafSpec.arrStore arrL arrV (rs.rsScalar idx) ⟨t.elemType, srcV⟩ with hnewVal
  have hStore : RustExec N leafSpec (.RArrStore arrL idx srcL) rs (rsSetTower rs name ⟨t, newVal⟩) :=
    RustExec.arrStore arrL idx srcL rs (rs.rsScalar idx) arrV srcV rfl hArrLook hSrcLook
  have hB : bridge t vRes newVal :=
    hUpd name t vArr vIdx vSrc vRes arrV srcV (rs.rsScalar idx)
      (hAgree.2 name vArr hvArr t arrV hRawArr) hk (hAgree.2 src vSrc hvSrc _ srcV hRawSrc) hBi
  have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) (rsSetTower rs name ⟨t, newVal⟩) :=
    envAgreesRustT_extend_tower bridge env rs name vRes t newVal hAgree hB
  have hSBmid : ScopeBound (rsSetTower rs name ⟨t, newVal⟩) Γ :=
    ScopeBound_rsSetTower_same rs Γ name t newVal hLk hSB
  have hSFmid : NamesFresh (rsSetTower rs name ⟨t, newVal⟩) S :=
    NamesFresh_rsSetTower rs S name _ hNotMem hSF
  have hNNmid : ScalarInv D S (env.extend name vRes) := hNN.extend_of_not_mem hNotMem _
  obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF', hNN'⟩ :=
    ihBody fuel Γ Γ' bodyC (env.extend name vRes) env' _ v
      hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid hNNmid
  exact ⟨rs', RustExec.seq _ _ _ _ _ hStore hBodyExec, hAgreeFinal, hSB', hSF', hNN'⟩

/-- The array-store arm of an assignment: `arr = array_update(arr, idx, src)` on
    three variables simulates by `RArrStore` under `ArrUpdateAgrees`. -/
theorem progSimW_assign_arrUpdate (name f arr idx src : String)
    (hf_arr : f = "array_update")
    (hUpd : ArrUpdateAgrees bridge bi leafSpec) :
    ProgSimW bridge bi N leafSpec D S T A
      (.assign name (.app f [.var arr, .var idx, .var src])) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  simp only [simScopeW, if_pos hf_arr] at hScope
  rcases hA : List.lookup arr A with _ | t
  · rw [hA] at hScope; cases hScope
  simp only [hA] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  rw [Option.some.injEq] at hScope
  subst hScope
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hName, hLk⟩, hLkSrc⟩, hIdxS'⟩ := hc
  have hIdxS : idx ∈ S := mem_of_contains S idx hIdxS'
  subst hName
  have hC := haxToLowCT_assign_arrUpdate_some name f name idx src c hf_arr hHax
  subst hC
  rw [litTower_arrStore,
    arrTower_arrStore A { locVar := name, locSrc := .TBytes 0 } { locVar := src, locSrc := .TBytes 0 }
      idx t hA]
  simp only [forToLoop, forToLoopArgs] at hEval
  have hArgsEnv := evalImp_assign_app_argsDefined bi fuel name f
    [.var name, .var idx, .var src] env v env' (by simp) hEval
  obtain ⟨vals, vRes, hAV, hBi, henv', _⟩ :=
    evalImp_assign_app_vars_inv bi fuel name f _ env v env' hArgsEnv hEval
  obtain ⟨vArr, vIdx, vSrc, rfl, hvArr, hvIdx, hvSrc⟩ := allVars_three hAV
  subst hf_arr
  subst henv'
  obtain ⟨arrV, hRawArr⟩ := hSB name t hLk
  obtain ⟨srcV, hRawSrc⟩ := hSB src t.elemType hLkSrc
  have hTIdx : rs.rsTower idx = none := hSF idx hIdxS
  have hk : ∀ n, valueToScalar vIdx = some n → n = rs.rsScalar idx :=
    fun n hn => (hAgree.1 idx vIdx n hvIdx hTIdx hn).symm
  have hNotMem : name ∉ S := by
    intro hm
    rw [hSF name hm] at hRawArr
    cases hRawArr
  set arrL : Located := { locVar := name, locSrc := t } with harrL
  set srcL : Located := { locVar := src, locSrc := t.elemType } with hsrcL
  have hArrLook : locatedLookup rs arrL = some arrV := locatedLookup_of_rsTower rs name t arrV hRawArr
  have hSrcLook : locatedLookup rs srcL = some srcV :=
    locatedLookup_of_rsTower rs src t.elemType srcV hRawSrc
  set newVal := leafSpec.arrStore arrL arrV (rs.rsScalar idx) ⟨t.elemType, srcV⟩ with hnewVal
  have hStore : RustExec N leafSpec (.RArrStore arrL idx srcL) rs (rsSetTower rs name ⟨t, newVal⟩) :=
    RustExec.arrStore arrL idx srcL rs (rs.rsScalar idx) arrV srcV rfl hArrLook hSrcLook
  have hB : bridge t vRes newVal :=
    hUpd name t vArr vIdx vSrc vRes arrV srcV (rs.rsScalar idx)
      (hAgree.2 name vArr hvArr t arrV hRawArr) hk (hAgree.2 src vSrc hvSrc _ srcV hRawSrc) hBi
  exact ⟨_, hStore, envAgreesRustT_extend_tower bridge env rs name vRes t newVal hAgree hB,
    ScopeBound_rsSetTower_same rs Γ name t newVal hLk hSB,
    NamesFresh_rsSetTower rs S name _ hNotMem hSF, hNN.extend_of_not_mem hNotMem _⟩

end ArmsW

/-! ## §5  The checker at a given tower dispatch -/

/-- The call names `simScopeW` reads the tower dispatch of: those of `letBind`s
    and `assign`s on the statement path, including loop bodies. -/
def scopeCallNamesW : ImpExpr → List String
  | .letBind _ (.app f _) body => f :: scopeCallNamesW body
  | .letBind _ _ body => scopeCallNamesW body
  | .seq a b => scopeCallNamesW a ++ scopeCallNamesW b
  | .ifThenElse _ t e => scopeCallNamesW t ++ scopeCallNamesW e
  | .whileLoop _ body => scopeCallNamesW body
  | .whileFold _ body => scopeCallNamesW body
  | .forFold _ _ _ body => scopeCallNamesW body
  | .forFoldRev _ _ _ body => scopeCallNamesW body
  | .assign _ (.app f _) => [f]
  | .typeAscription e _ => scopeCallNamesW e
  | _ => []

/-- `simScopeW` at two tower dispatches that agree on the call names it reads
    coincide. -/
theorem simScopeW_eq_tow (tow tow' : String → TowerType) (D S T : List String) (A : TowerScope)
    (e : ImpExpr) :
    (∀ f ∈ scopeCallNamesW e, tow f = tow' f) →
      ∀ Γ, simScopeW tow D S T A Γ e = simScopeW tow' D S T A Γ e := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro h Γ
    cases val with
    | app f args =>
      simp only [scopeCallNamesW, List.mem_cons] at h
      have hf := h f (Or.inl rfl)
      have hb := ihBody fun g hg => h g (Or.inr hg)
      simp only [simScopeW, hf, hb]
    | lit l =>
      simp only [scopeCallNamesW] at h
      simp only [simScopeW, ihBody h]
    | var src =>
      simp only [scopeCallNamesW] at h
      simp only [simScopeW, ihBody h]
    | proj pe i =>
      simp only [scopeCallNamesW] at h
      cases pe <;> simp only [simScopeW, ihBody h]
    | _ => simp only [simScopeW]
  | seq a b iha ihb =>
    intro h Γ
    simp only [scopeCallNamesW, List.mem_append] at h
    have ha := iha fun g hg => h g (Or.inl hg)
    have hb := ihb fun g hg => h g (Or.inr hg)
    simp only [simScopeW, ha, hb]
  | ifThenElse c t e _ iht ihe =>
    intro h Γ
    simp only [scopeCallNamesW, List.mem_append] at h
    have ht := iht fun g hg => h g (Or.inl hg)
    have he := ihe fun g hg => h g (Or.inr hg)
    cases c <;> simp only [simScopeW, ht, he]
  | whileLoop c body _ ih =>
    intro h Γ
    simp only [scopeCallNamesW] at h
    cases c <;> simp only [simScopeW, ih h]
  | whileFold c body _ ih =>
    intro h Γ
    simp only [scopeCallNamesW] at h
    cases c <;> simp only [simScopeW, ih h]
  | forFold i lo hi body _ _ ih =>
    intro h Γ
    simp only [scopeCallNamesW] at h
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      simp only [simScopeW, ih h]
    · by_cases hv : ∃ (a : Int) (n : String), lo = .lit (.int a) ∧ hi = .var n
      · obtain ⟨a, n, rfl, rfl⟩ := hv
        simp only [simScopeW, ih h]
      · rw [simScopeW_forFold_none _ D S T A Γ i lo hi body hs hv,
          simScopeW_forFold_none _ D S T A Γ i lo hi body hs hv]
  | forFoldRev i lo hi body _ _ ih =>
    intro h Γ
    simp only [scopeCallNamesW] at h
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      simp only [simScopeW, ih h]
    · rw [simScopeW_forFoldRev_none _ D S T A Γ i lo hi body hs,
        simScopeW_forFoldRev_none _ D S T A Γ i lo hi body hs]
  | typeAscription e _ ih =>
    intro h Γ
    simp only [scopeCallNamesW] at h
    simp only [simScopeW, ih h]
  | assign name rhs _ =>
    intro h Γ
    cases rhs with
    | app f args =>
      simp only [scopeCallNamesW, List.mem_singleton] at h
      simp only [simScopeW, h f rfl]
    | _ => simp only [simScopeW]
  | _ => intro _ Γ; rfl

/-! ## §6  The program-level theorem -/

/-- The builtin table `bi` with every call computed in the scalar heap undefined. -/
def scalarCallFree (bi : Builtins) : Builtins := fun f vals =>
  if scalarCallName f then none else bi f vals

theorem scalarCallFree_of_false {bi : Builtins} {f : String} (h : scalarCallName f = false)
    (vals : List Value) : scalarCallFree bi f vals = bi f vals := by
  simp only [scalarCallFree, h, Bool.false_eq_true, if_false]

theorem scalarCallFree_leaf (bridge : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" → scalarCallName f = false →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge) :
    ∀ f, f ≠ "array_update" → f ≠ "index" →
      LeafCallAgreesArgs (scalarCallFree bi) leafSpec f (towerOfCallName f) bridge := by
  intro f h1 h2 args vals argList oldV vRes hBi hF
  cases hc : scalarCallName f with
  | true => simp only [scalarCallFree, hc, if_true] at hBi; cases hBi
  | false =>
    rw [scalarCallFree_of_false hc] at hBi
    exact hLeaf f h1 h2 hc args vals argList oldV vRes hBi hF

theorem scalarCallFree_index (bridge : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec)
    (h : IndexAgrees bridge bi leafSpec) : IndexAgrees bridge (scalarCallFree bi) leafSpec := by
  intro name t vArr vIdx vRes arrV k hB hk hBi
  rw [scalarCallFree_of_false (by decide)] at hBi
  exact h name t vArr vIdx vRes arrV k hB hk hBi

theorem scalarCallFree_arrUpdate (bridge : ValueTowerBridge) (bi : Builtins)
    (leafSpec : LeafSpec) (h : ArrUpdateAgrees bridge bi leafSpec) :
    ArrUpdateAgrees bridge (scalarCallFree bi) leafSpec := by
  intro arr t vArr vIdx vSrc vRes arrV srcV k hB hk hS hBi
  rw [scalarCallFree_of_false (by decide)] at hBi
  exact h arr t vArr vIdx vSrc vRes arrV srcV k hB hk hS hBi

/-- The run of a list of variables does not read the builtin table. -/
theorem denoteArgs_allVar_eq_tables (bi bi' : Builtins) (fuel : Nat) :
    ∀ (args : List ImpExpr), args.all isVar = true →
      denoteArgs bi fuel args = denoteArgs bi' fuel args
  | [], _ => by
    unfold denoteArgs
    rfl
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨n, rfl⟩ : ∃ n, a = .var n := by
      cases a <;> simp_all [isVar]
    have ih := denoteArgs_allVar_eq_tables bi bi' fuel as h.2
    have hv : denote bi fuel (.var n) = denote bi' fuel (.var n) := by
      unfold denote
      rfl
    unfold denoteArgs
    rw [hv]
    refine congrArg (fun k => denote bi' fuel (.var n) >>= k) ?_
    funext r
    cases r <;> first | rfl | rw [ih]

theorem evalImp_var_eq_tables (bi bi' : Builtins) (fuel : Nat) (n : String) (env : Env) :
    evalImp bi fuel (.var n) env = evalImp bi' fuel (.var n) env := by
  unfold evalImp denote
  rfl

theorem evalImp_unitVal_eq_tables (bi bi' : Builtins) (fuel : Nat) (env : Env) :
    evalImp bi fuel .unitVal env = evalImp bi' fuel .unitVal env := by
  unfold evalImp denote
  rfl

theorem evalImp_assign_lit_eq_tables (bi bi' : Builtins) (fuel : Nat) (n : String) (l : ImpLit)
    (env : Env) :
    evalImp bi fuel (.assign n (.lit l)) env = evalImp bi' fuel (.assign n (.lit l)) env := by
  unfold evalImp
  rw [denote_assign_run_eq, denote_assign_run_eq, denote_lit_eq, denote_lit_eq]

theorem evalImp_tuple_eq_tables (bi bi' : Builtins) (fuel : Nat) (es : List ImpExpr)
    (h : es.all isVar = true) (env : Env) :
    evalImp bi fuel (.tuple es) env = evalImp bi' fuel (.tuple es) env := by
  unfold evalImp
  rw [denote_tuple_run_eq, denote_tuple_run_eq, denoteArgs_allVar_eq_tables bi bi' fuel es h]

theorem evalImp_assign_app_eq_tables (bi bi' : Builtins) (fuel : Nat) (n f : String)
    (args : List ImpExpr) (hv : args.all isVar = true) (hf : ∀ vals, bi f vals = bi' f vals)
    (env : Env) :
    evalImp bi fuel (.assign n (.app f args)) env =
      evalImp bi' fuel (.assign n (.app f args)) env := by
  unfold evalImp
  rw [denote_assign_run_eq, denote_assign_run_eq, denote_app_run_eq, denote_app_run_eq,
    denoteArgs_allVar_eq_tables bi bi' fuel args hv]
  rcases (denoteArgs bi' fuel args).run env with ⟨mvals, env_a⟩
  cases mvals with
  | none => rfl
  | some vals => simp only [hf]

theorem allVar_of_argsInScope (Γ : TowerScope) (dt : TowerType) (args : List ImpExpr)
    (h : argsInScope Γ dt args = true) : args.all isVar = true := by
  refine List.all_eq_true.mpr fun a ha => ?_
  obtain ⟨n, rfl⟩ := argsInScope_allVars Γ dt args h a ha
  rfl

/-- **Program-level simulation with counted, reverse, runtime-bound and
    data-dependent loops.**  Every source program simulates by
    `arrTower A (litTower T c)` for its lowering `c` under `envAgreesRustT`, with
    its loops read back by `forToLoop`, from an environment whose names of `D`
    are bound and whose names of `S` hold non-negative integers, from the
    hypotheses of `haxToLowCT_simulates_programA` with the leaf condition on the
    call names not computed in the scalar heap, `ScalarCallsAgree` and
    `LimbReadAgrees`. -/
theorem haxToLowCT_simulates_programW
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (D S T : List String) (A : TowerScope)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" → scalarCallName f = false →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (hSc : ScalarCallsAgree bi)
    (hLimb : LimbReadAgrees bridge bi)
    (e : ImpExpr) : ProgSimW bridge bi N leafSpec D S T A e := by
  have noneArm := progSimW_of_simScopeW_none bridge bi N leafSpec D S T A
  have hA := haxToLowCT_simulates_programA bridge (scalarCallFree bi) N leafSpec S T A
    (scalarCallFree_leaf bridge bi leafSpec hLeaf) hProj hLit (scalarCallFree_index bridge bi leafSpec hIdx)
    (scalarCallFree_arrUpdate bridge bi leafSpec hUpd)
  induction e using ImpExpr.ind with
  | var name =>
    refine progSimW_of_progSimA_tables bridge bi N leafSpec D S T A (scalarCallFree bi) _
      (fun _ => rfl) rfl (fun _ _ _ => rfl) ?_
      (fun _ _ _ fuel env => evalImp_var_eq_tables bi _ fuel name env) (hA _)
    intro Γ Γ' c fuel env env' v _ _ hEval hNN
    exact ScalarInv_of_eq hNN (evalImp_var_inv bi fuel name env v env' hEval).2
  | unitVal =>
    refine progSimW_of_progSimA_tables bridge bi N leafSpec D S T A (scalarCallFree bi) _
      (fun _ => rfl) rfl (fun _ _ _ => rfl) ?_
      (fun _ _ _ fuel env => evalImp_unitVal_eq_tables bi _ fuel env) (hA _)
    intro Γ Γ' c fuel env env' v _ _ hEval hNN
    exact ScalarInv_of_eq hNN (evalImp_unitVal_inv bi fuel env v env' hEval).2
  | tuple es _ =>
    refine progSimW_of_progSimA_tables bridge bi N leafSpec D S T A (scalarCallFree bi) _
      (fun _ => rfl) rfl ?_ ?_ ?_ (hA _)
    · intro Γ Γ' h
      simp only [simScopeW] at h
      split at h
      · rename_i hAll
        simp only [forToLoop, forToLoopArgs_of_allVar es hAll]
      · cases h
    · intro Γ Γ' c fuel env env' v hScope _ hEval hNN
      simp only [simScopeW] at hScope
      split at hScope
      · rename_i hAll
        exact ScalarInv_of_eq hNN (evalImp_tuple_vars_inv bi fuel es env v env' hAll hEval)
      · cases hScope
    · intro Γ Γ' h fuel env
      simp only [simScopeW] at h
      split at h
      · rename_i hAll
        exact evalImp_tuple_eq_tables bi _ fuel es hAll env
      · cases h
  | seq a b iha ihb => exact progSimW_seq bridge bi N leafSpec D S T A a b iha ihb
  | letBind name val body _ ihBody =>
    cases val with
    | lit l => exact progSimW_letBind_lit bridge bi N leafSpec D S T A name l body hLit ihBody
    | app f args =>
      by_cases hf_arr : f = "array_update"
      · rcases hSh : varArgs3 args with _ | ⟨arr, idx, src⟩
        · refine noneArm _ fun Γ => ?_
          simp only [simScopeW, if_pos hf_arr]
          split
          · simp [varArgs3] at hSh
          · rfl
        · rw [varArgs3_some hSh]
          exact progSimW_letBind_arrUpdate bridge bi N leafSpec D S T A name f arr idx src body
            hf_arr hUpd ihBody
      by_cases hf_idx : f = "index"
      · rcases hSh : varArgs2 args with _ | ⟨arr, idx⟩
        · by_cases hl : ∃ (v : String) (k : Int), args = [.var v, .lit (.int k)]
          · obtain ⟨v, k, rfl⟩ := hl
            exact progSimW_letBind_limb bridge bi N leafSpec D S T A name f v k body hf_arr
              hf_idx hLimb ihBody
          · refine noneArm _ fun Γ => ?_
            simp only [simScopeW, if_neg hf_arr, if_pos hf_idx]
            split
            · simp [varArgs2] at hSh
            · exact absurd ⟨_, _, rfl⟩ hl
            · rfl
        · rw [varArgs2_some hSh]
          exact progSimW_letBind_index bridge bi N leafSpec D S T A name f arr idx body hf_arr
            hf_idx hIdx ihBody
      by_cases hsc : scalarCallName f = true
      · rcases hSh : varArgs2 args with _ | ⟨a, b⟩
        · refine noneArm _ fun Γ => ?_
          simp only [simScopeW, if_neg hf_arr, if_neg hf_idx, hsc, ↓reduceIte]
          split
          · simp [varArgs2] at hSh
          · rfl
        · rw [varArgs2_some hSh]
          exact progSimW_letBind_scalar bridge bi N leafSpec D S T A name f a b body hSc hsc
            hf_arr hf_idx ihBody
      have hsc' : scalarCallName f = false := by simpa using hsc
      exact progSimW_letBind_app bridge bi N leafSpec D S T A name f args body
        (hLeaf f hf_arr hf_idx hsc') hf_arr hf_idx hsc' ihBody
    | var src => exact progSimW_letBind_var bridge bi N leafSpec D S T A name src body ihBody
    | proj pe i =>
      cases pe with
      | var t =>
        exact progSimW_letBind_proj bridge bi N leafSpec D S T A name t i body hProj ihBody
      | _ => exact noneArm _ fun Γ => by simp [simScopeW]
    | _ => exact noneArm _ fun Γ => by simp [simScopeW]
  | ifThenElse cond t e _ iht ihe =>
    cases cond with
    | var v_cond => exact progSimW_ifThenElse bridge bi N leafSpec D S T A v_cond t e iht ihe
    | _ => exact noneArm _ fun Γ => by simp [simScopeW]
  | whileLoop cond body _ ihBody =>
    cases cond with
    | var v_cond => exact progSimW_whileLoop bridge bi N leafSpec D S T A v_cond body ihBody
    | _ => exact noneArm _ fun Γ => by simp [simScopeW]
  | whileFold cond body _ ihBody =>
    cases cond with
    | var v_cond => exact progSimW_whileFold bridge bi N leafSpec D S T A v_cond body ihBody
    | _ => exact noneArm _ fun Γ => by simp [simScopeW]
  | forFold i lo hi body _ _ ihBody =>
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      exact progSimW_forFold bridge bi N leafSpec D S T A i a b body ihBody
    · by_cases hv : ∃ (a : Int) (n : String), lo = .lit (.int a) ∧ hi = .var n
      · obtain ⟨a, n, rfl, rfl⟩ := hv
        exact progSimW_forFold_var bridge bi N leafSpec D S T A i a n body ihBody
      · exact noneArm _ fun Γ => simScopeW_forFold_none _ D S T A Γ i lo hi body hs hv
  | forFoldRev i lo hi body _ _ ihBody =>
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      exact progSimW_forFoldRev bridge bi N leafSpec D S T A i a b body ihBody
    · exact noneArm _ fun Γ => simScopeW_forFoldRev_none _ D S T A Γ i lo hi body hs
  | assign name rhs _ =>
    cases rhs with
    | lit l =>
      refine progSimW_of_progSimA_tables bridge bi N leafSpec D S T A (scalarCallFree bi) _
        (fun _ => rfl) rfl (fun _ _ _ => rfl) ?_
        (fun _ _ _ fuel env => evalImp_assign_lit_eq_tables bi _ fuel name l env) (hA _)
      intro Γ Γ' c fuel env env' v _ hHax hEval hNN
      rw [(evalImp_assign_lit_inv bi fuel name l env v env' hEval).2]
      exact hNN.extend_of_nonneg name (assign_lit_nonneg name l c hHax)
    | app f args =>
      by_cases hf_arr : f = "array_update"
      · rcases hSh : varArgs3 args with _ | ⟨arr, idx, src⟩
        · refine noneArm _ fun Γ => ?_
          simp only [simScopeW, if_pos hf_arr]
          split
          · simp [varArgs3] at hSh
          · rfl
        · rw [varArgs3_some hSh]
          exact progSimW_assign_arrUpdate bridge bi N leafSpec D S T A name f arr idx src hf_arr
            hUpd
      by_cases hf_idx : f = "index"
      · exact noneArm _ fun Γ => by simp only [simScopeW, if_neg hf_arr, if_pos hf_idx]
      have hf : ¬ (f = "array_update" ∨ f = "index") := not_or.mpr ⟨hf_arr, hf_idx⟩
      by_cases hsc : scalarCallName f = true
      · exact noneArm _ fun Γ => by
          simp only [simScopeW, if_neg hf_arr, if_neg hf_idx, hsc, Bool.not_true, Bool.false_and,
            Bool.false_eq_true, if_false]
      have hsc' : scalarCallName f = false := by simpa using hsc
      refine progSimW_of_progSimA_tables bridge bi N leafSpec D S T A (scalarCallFree bi) _
        (fun _ => by
          simp only [simScopeW, simScopeA, if_neg hf_arr, if_neg hf_idx, if_neg hf, hsc',
            Bool.not_false, Bool.true_and]) rfl
        ?_ ?_ ?_ (hA _)
      · intro Γ Γ' h
        simp only [simScopeW, if_neg hf_arr, if_neg hf_idx, hsc', Bool.not_false, Bool.true_and] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          simp only [forToLoop, forToLoopArgs_of_vars args (argsInScope_allVars Γ _ args hc.1.1)]
        · cases h
      · intro Γ Γ' c fuel env env' v hScope _ hEval hNN
        simp only [simScopeW, if_neg hf_arr, if_neg hf_idx, hsc', Bool.not_false, Bool.true_and]
          at hScope
        split at hScope
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          obtain ⟨vRhs, env_mid, hRhs, _, henv⟩ := evalImp_assign_inv bi fuel name _ env v env' hEval
          have hAllVar := argsInScope_allVars Γ _ args hc.1.1
          have hArgsEnv := evalImp_assign_app_argsDefined bi fuel name f args env v env'
            hAllVar hEval
          obtain ⟨_, _, _, _, henv', _⟩ :=
            evalImp_assign_app_vars_inv bi fuel name f args env v env' hArgsEnv hEval
          rw [henv']
          exact hNN.extend_of_not_mem (not_mem_of_not_contains S name hc.2) _
        · cases hScope
      · intro Γ Γ' h fuel env
        simp only [simScopeW, if_neg hf_arr, if_neg hf_idx, hsc', Bool.not_false, Bool.true_and] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact evalImp_assign_app_eq_tables bi _ fuel name f args
            (allVar_of_argsInScope Γ _ args hc.1.1)
            (fun vals => (scalarCallFree_of_false hsc' vals).symm) env
        · cases h
    | _ => exact noneArm _ fun Γ => by simp [simScopeW]
  | typeAscription e _ ih =>
    intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
    simp only [simScopeW] at hScope
    rw [haxToLowCT_typeAscription_eq] at hHax
    simp only [forToLoop] at hEval
    rw [evalImp_typeAscription] at hEval
    exact ih fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hNN
  | _ => exact noneArm _ fun Γ => by simp [simScopeW]

section ClosedForms

variable (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (D S T : List String) (A : TowerScope)
  (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" → scalarCallName f = false →
    LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
  (hProj : TupleLoadAgrees bridge leafSpec)
  (hLit : LitStoreAgrees bridge leafSpec)
  (hIdx : IndexAgrees bridge bi leafSpec)
  (hUpd : ArrUpdateAgrees bridge bi leafSpec)
  (hSc : ScalarCallsAgree bi)
  (hLimb : LimbReadAgrees bridge bi)

include hLeaf hProj hLit hIdx hUpd hSc hLimb

/-- A counted loop with non-negative integer literal bounds simulates, with the
    source run of the `forLoop` it is read as. -/
theorem haxToLowCT_simulates_forFold (i : String) (lo hi : Int) (body : ImpExpr) :
    ProgSimW bridge bi N leafSpec D S T A (.forFold i (.lit (.int lo)) (.lit (.int hi)) body) :=
  progSimW_forFold bridge bi N leafSpec D S T A i lo hi body
    (haxToLowCT_simulates_programW bridge bi N leafSpec D S T A hLeaf hProj hLit hIdx hUpd hSc hLimb
      body)

/-- A reverse counted loop with non-negative integer literal bounds simulates,
    with the source run of the `forLoopRev` it is read as. -/
theorem haxToLowCT_simulates_forFoldRev (i : String) (lo hi : Int) (body : ImpExpr) :
    ProgSimW bridge bi N leafSpec D S T A (.forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body) :=
  progSimW_forFoldRev bridge bi N leafSpec D S T A i lo hi body
    (haxToLowCT_simulates_programW bridge bi N leafSpec D S T A hLeaf hProj hLit hIdx hUpd hSc hLimb
      body)

/-- A data-dependent loop on a scalar guard simulates, with the source run of
    the `whileLoop` it is read as. -/
theorem haxToLowCT_simulates_whileFold (cond : String) (body : ImpExpr) :
    ProgSimW bridge bi N leafSpec D S T A (.whileFold (.var cond) body) :=
  progSimW_whileFold bridge bi N leafSpec D S T A cond body
    (haxToLowCT_simulates_programW bridge bi N leafSpec D S T A hLeaf hProj hLit hIdx hUpd hSc hLimb
      body)

end ClosedForms

end CatCrypt.Crypto.Hax
