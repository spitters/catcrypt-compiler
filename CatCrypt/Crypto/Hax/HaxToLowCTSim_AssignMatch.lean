/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Hax.HaxToLowCTSimulates

/-!
# H3.tertia: assign-lit and match-tuple-destructure simulation cases

* `assign name (lit l)` → `RScalarSet name n` (when literal decodes)
* `match_ (app f args) [(tuplePat [varPat n1, varPat n2], body)]` →
  `RLetZero n1 dt (RLetZero n2 dt (RSeq (RCallSwap f d1 d2 args') bodyC))`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Source-side decomposition: `assign` -/

/-- Inverse: if `evalImp` on `.assign name rhs` succeeds, then `rhs` produces
    some value `vRhs` with mid-env `env_mid`, the result is `.unit`, and the
    final env is `env_mid` extended at `name`. -/
theorem evalImp_assign_inv (bi : Builtins) (fuel : Nat) (name : String)
    (rhs : ImpExpr) (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.assign name rhs) env = some (v, env')) :
    ∃ vRhs env_mid, evalImp bi fuel rhs env = some (vRhs, env_mid) ∧
                    v = .unit ∧ env' = Env.extend env_mid name vRhs := by
  unfold evalImp at h ⊢
  -- Unfold the .assign case of denote
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure, modify, modifyGet, MonadStateOf.modifyGet] at h
  -- Case-split on what `denote bi fuel rhs env` returns
  cases hR : denote bi fuel rhs env with
  | mk oR emR =>
    rw [hR] at h
    cases oR with
    | val vR =>
      -- After `rw [hR]`, the modify+pure for the val branch must reduce.
      simp only [StateT.modifyGet, StateT.pure, StateT.bind, bind,
                 Bind.bind, pure, Pure.pure] at h
      refine ⟨vR, emR, ?_, ?_, ?_⟩
      · show (match denote bi fuel rhs env with
                | (Outcome.val v, env') => some (v, env')
                | _ => none) = some (vR, emR)
        rw [hR]
      · -- h now has shape `some (.unit, emR.extend name vR) = some (v, env')`
        rw [Option.some.injEq, Prod.mk.injEq] at h
        exact h.1.symm
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm
    | earlyRet w =>
      simp only [StateT.pure] at h
      cases h
    | broke w =>
      simp only [StateT.pure] at h
      cases h
    | continued =>
      simp only [StateT.pure] at h
      cases h
    | err msg =>
      simp only [StateT.pure] at h
      cases h

/-! ## §2  Source-side decomposition: `assign` of a literal RHS

Specialisation of `evalImp_assign_inv` to `rhs = .lit l`.  The RHS
evaluation is `pure (.val (Value.ofLit l))` with no env change, so the
inverse simplifies: `v = .unit` and `env' = env.extend name (Value.ofLit l)`. -/

theorem evalImp_assign_lit_inv (bi : Builtins) (fuel : Nat) (name : String)
    (l : ImpLit) (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.assign name (.lit l)) env = some (v, env')) :
    v = .unit ∧ env' = Env.extend env name (Value.ofLit l) := by
  obtain ⟨vRhs, env_mid, hRhs, hv, henv⟩ :=
    evalImp_assign_inv bi fuel name (.lit l) env v env' h
  -- The lit RHS pins down vRhs and env_mid.
  unfold evalImp at hRhs
  simp only [denote, pure, Pure.pure, StateT.pure, StateT.run] at hRhs
  rw [Option.some.injEq, Prod.mk.injEq] at hRhs
  obtain ⟨hvRhs, hEnvMid⟩ := hRhs
  refine ⟨hv, ?_⟩
  rw [henv, ← hEnvMid, ← hvRhs]

/-! ## §3  Agreement-extension lemma (local copy)

This duplicates `envAgreesRust_extend_scalar` from
`HaxToLowCTSim_Agreement.lean` to avoid creating a cross-file
dependency.  Once that file lands stable, this local copy can be
deleted and the import added. -/

private theorem envAgreesRust_extend_scalar_local
    (env : Env) (rs : RustState) (name : String) (n : Nat)
    (hAgree : envAgreesRust env rs) :
    envAgreesRust (env.extend name (.int n)) (rsSetScalar rs name n) := by
  intro x v hxv m hm
  by_cases hx : x = name
  · -- x = name: lookup pins v = .int n, rsScalar agrees with n.toNat = n.
    subst hx
    rw [Env.extend_same] at hxv
    rw [Option.some.injEq] at hxv
    subst hxv
    -- valueToScalar (.int n) = some n (since n : Nat ≥ 0)
    have hVS : valueToScalar (.int (n : Int)) = some n := by
      simp [valueToScalar]
    rw [hVS] at hm
    rw [Option.some.injEq] at hm
    subst hm
    -- rsSetScalar same: lookup returns n
    simp [rsSetScalar]
  · -- x ≠ name: extension and rsSetScalar are no-ops at x.
    rw [Env.extend_other _ _ _ _ hx] at hxv
    have hScalar : (rsSetScalar rs name n).rsScalar x = rs.rsScalar x := by
      unfold rsSetScalar; simp only []
      have : (x == name) = false := beq_eq_false_iff_ne.mpr hx
      simp [this]
    rw [hScalar]
    exact hAgree x v hxv m hm

/-! ## §4  Simulation instance: `assign _ (.lit (.uintLit _ _))` -/

/-- `haxToLowCT` reduces the assign-uintLit arm to `RScalarSet`. -/
theorem haxToLowCT_assign_lit_uintLit_some
    (name : String) (w : IntWidth) (n : Nat) :
    haxToLowCT (.assign name (.lit (.uintLit w n))) = some (.RScalarSet name n) := by
  unfold haxToLowCT; rfl

/-- Simulation: assign-uintLit lowers to `RScalarSet` which sets the
    Rust scalar to the literal value.  Agreement extends via the
    local agreement lemma. -/
theorem haxToLowCT_simulates_assign_lit_uintLit
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (w : IntWidth) (n : Nat) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec
      (.assign name (.lit (.uintLit w n))) c env env' rs v := by
  intro hHax hEval hAgree
  -- Unpack the syntactic translation: c = .RScalarSet name n
  rw [haxToLowCT_assign_lit_uintLit_some] at hHax
  cases hHax
  -- Unpack the source-side evaluation
  obtain ⟨hv, henv⟩ := evalImp_assign_lit_inv bi fuel name (.uintLit w n) env v env' hEval
  -- Value.ofLit (.uintLit w n) = .int n
  have hOfLit : Value.ofLit (.uintLit w n) = .int n := rfl
  rw [hOfLit] at henv
  -- Choose rs' = rsSetScalar rs name n
  refine ⟨rsSetScalar rs name n,
          RustExec.scalarSet (N := N) (leafSpec := leafSpec) name n rs, ?_⟩
  -- Agreement preservation
  rw [henv]
  exact envAgreesRust_extend_scalar_local env rs name n hAgree

/-! ## §4bis  Simulation instance: `assign _ (.lit (.bool b))`

Bools are 0/1 scalars (consistent with `RIfNz` / `RWhileNz` reading
nonzero as true), so the bool arm mirrors the uintLit case with
`n = if b then 1 else 0`. -/

private theorem envAgreesRust_extend_scalar_bool_local
    (env : Env) (rs : RustState) (name : String) (b : Bool)
    (hAgree : envAgreesRust env rs) :
    envAgreesRust (env.extend name (.bool b))
      (rsSetScalar rs name (if b then 1 else 0)) := by
  intro x v hxv m hm
  by_cases hx : x = name
  · subst hx
    rw [Env.extend_same] at hxv
    rw [Option.some.injEq] at hxv
    subst hxv
    have hVS : valueToScalar (.bool b) = some (if b then 1 else 0) := by
      cases b <;> rfl
    rw [hVS] at hm
    rw [Option.some.injEq] at hm
    subst hm
    simp [rsSetScalar]
  · rw [Env.extend_other _ _ _ _ hx] at hxv
    have hScalar : (rsSetScalar rs name (if b then 1 else 0)).rsScalar x
        = rs.rsScalar x := by
      unfold rsSetScalar; simp only []
      have : (x == name) = false := beq_eq_false_iff_ne.mpr hx
      simp [this]
    rw [hScalar]
    exact hAgree x v hxv m hm

/-- `haxToLowCT` reduces the assign-bool arm to `RScalarSet` with the
    0/1 encoding. -/
theorem haxToLowCT_assign_lit_bool_some (name : String) (b : Bool) :
    haxToLowCT (.assign name (.lit (.bool b)))
      = some (.RScalarSet name (if b then 1 else 0)) := by
  unfold haxToLowCT; rfl

/-- Simulation: assign-bool lowers to `RScalarSet` which sets the Rust
    scalar to the 0/1 encoding of the literal. -/
theorem haxToLowCT_simulates_assign_lit_bool
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (b : Bool) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec
      (.assign name (.lit (.bool b))) c env env' rs v := by
  intro hHax hEval hAgree
  rw [haxToLowCT_assign_lit_bool_some] at hHax
  cases hHax
  obtain ⟨hv, henv⟩ := evalImp_assign_lit_inv bi fuel name (.bool b) env v env' hEval
  have hOfLit : Value.ofLit (.bool b) = .bool b := rfl
  rw [hOfLit] at henv
  refine ⟨rsSetScalar rs name (if b then 1 else 0),
          RustExec.scalarSet (N := N) (leafSpec := leafSpec)
            name (if b then 1 else 0) rs, ?_⟩
  rw [henv]
  exact envAgreesRust_extend_scalar_bool_local env rs name b hAgree

/-! ## §5  Simulation instance: `assign _ (.lit (.int n))` with `n ≥ 0`

The signed-int literal arm of `haxToLowCT` rewrites to `RScalarSet`
when `n ≥ 0`.  Lit decode is the same (`Value.ofLit (.int n) = .int n`),
so the proof follows the uintLit case structurally. -/

theorem haxToLowCT_assign_lit_int_some_of_nonneg
    (name : String) (n : Int) (hn : n ≥ 0) :
    haxToLowCT (.assign name (.lit (.int n))) = some (.RScalarSet name n.toNat) := by
  unfold haxToLowCT
  simp [hn]

theorem haxToLowCT_simulates_assign_lit_int
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (n : Int) (hn : n ≥ 0) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec
      (.assign name (.lit (.int n))) c env env' rs v := by
  intro hHax hEval hAgree
  rw [haxToLowCT_assign_lit_int_some_of_nonneg name n hn] at hHax
  cases hHax
  obtain ⟨hv, henv⟩ := evalImp_assign_lit_inv bi fuel name (.int n) env v env' hEval
  -- Value.ofLit (.int n) = .int n
  have hOfLit : Value.ofLit (.int n) = .int n := rfl
  rw [hOfLit] at henv
  refine ⟨rsSetScalar rs name n.toNat,
          RustExec.scalarSet (N := N) (leafSpec := leafSpec) name n.toNat rs, ?_⟩
  -- Agreement.  The decoded Nat is n.toNat; need to show
  -- envAgreesRust (env.extend name (.int n)) (rsSetScalar rs name n.toNat).
  -- Use the agreement lemma after rewriting .int n to .int (n.toNat : Int)
  -- via the n ≥ 0 hypothesis.
  rw [henv]
  have hCoerce : (n : Int) = ((n.toNat : Nat) : Int) := (Int.toNat_of_nonneg hn).symm
  -- Rewrite the env extension's Value: .int n = .int (n.toNat : Int).
  have hVal : (Value.int n) = Value.int ((n.toNat : Nat) : Int) := by rw [← hCoerce]
  rw [hVal]
  exact envAgreesRust_extend_scalar_local env rs name n.toNat hAgree

/-! ## §6  TODO: match-tuple-destructure of an app

The case `.match_ (.app f args) [(.tuplePat [.varPat n1, .varPat n2], body)]`
lowers to `RLetZero n1 dt (RLetZero n2 dt (RSeq (RCallSwap f d1 d2 args') bodyC))`.
The simulation obligation requires:

* a source-side inverse for `match_` on the singleton arm `tuplePat
  [varPat n1, varPat n2]`, decomposing `denote bi fuel (app f args) env`
  into argument denotations + the builtin call;
* a `LeafCallAgrees` predicate relating the source builtin call to
  `leafSpec.call f dt [...]` on the Rust side;
* tower-typed agreement (`bindingOK`-style) — currently the agreement
  predicate `envAgreesRust` only covers scalars.

All three are H3.quarta (tower / byte leaf calls) territory.  The full
proof is blocked on the H3.quarta agreement extension; this file
intentionally leaves the match-tuple case as a stub to track.

```
/- TODO: haxToLowCT_simulates_match_tuple_app -/
```
-/

end CatCrypt.Crypto.Hax
