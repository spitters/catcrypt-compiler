/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates

/-!
# H3.sexta: ifThenElse simulation case

Handles `.ifThenElse (.var cond) t e` arm of `haxToLowCT`, which
produces `RIfNz cond tC eC` on the LowCT side.  The agreement
predicate aligns Hax's `.bool` condition with LowCT's scalar
nonzero-test.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Syntactic unpacker for the `ifThenElse (.var cond) t e` arm -/

/-- `haxToLowCT` reduces on `.ifThenElse (.var cond) t e` to `some c` iff
    both sub-translations succeed and `c = .RIfNz cond tC eC`. -/
theorem haxToLowCT_ifThenElse_var_some
    (cond : String) (t e : ImpExpr) (c : LowCT)
    (h : haxToLowCT (.ifThenElse (.var cond) t e) = some c) :
    ∃ tC eC, haxToLowCT t = some tC ∧ haxToLowCT e = some eC
           ∧ c = .RIfNz cond tC eC := by
  unfold haxToLowCT at h
  cases hT : haxToLowCT t with
  | none => rw [hT] at h; simp at h
  | some tC =>
    cases hE : haxToLowCT e with
    | none => rw [hT, hE] at h; simp at h
    | some eC =>
      rw [hT, hE] at h
      simp at h
      exact ⟨tC, eC, rfl, rfl, h.symm⟩

/-! ## §2  Source-side decomposition: `ifThenElse (.var cond) t e`

For `.ifThenElse (.var cond) t e`, the Hax-side first reads `env cond`
(which must be `some (.bool _)`), then dispatches to `t` or `e`.  The
inverse therefore splits into two sub-cases. -/

theorem evalImp_ifThenElse_var_inv (bi : Builtins) (fuel : Nat)
    (cond : String) (t e : ImpExpr) (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.ifThenElse (.var cond) t e) env = some (v, env')) :
    (env cond = some (.bool true) ∧ evalImp bi fuel t env = some (v, env'))
  ∨ (env cond = some (.bool false) ∧ evalImp bi fuel e env = some (v, env')) := by
  unfold evalImp at h ⊢
  -- Unfold the `.ifThenElse` arm of `denote` and the inner `.var cond` lookup.
  simp only [denote, bind, Bind.bind, StateT.bind, get, getThe,
             MonadStateOf.get, StateT.get, pure, Pure.pure,
             StateT.run] at h
  -- Case-split on `env cond`.
  cases hen : env cond with
  | none =>
    rw [hen] at h
    -- The lookup returns `Outcome.err`, propagated to outer; contradiction.
    simp only [StateT.pure] at h
    cases h
  | some w =>
    rw [hen] at h
    -- Now case-split on the value: only `.bool true` / `.bool false` succeed.
    cases w with
    | bool b =>
      cases b with
      | true =>
        left
        exact ⟨rfl, h⟩
      | false =>
        right
        exact ⟨rfl, h⟩
    | int _ => simp only [StateT.pure] at h; cases h
    | uint _ _ => simp only [StateT.pure] at h; cases h
    | sint _ _ => simp only [StateT.pure] at h; cases h
    | array _ => simp only [StateT.pure] at h; cases h
    | unit => simp only [StateT.pure] at h; cases h
    | tuple _ => simp only [StateT.pure] at h; cases h
    | option _ => simp only [StateT.pure] at h; cases h
    | result _ _ => simp only [StateT.pure] at h; cases h
    | controlFlow _ _ => simp only [StateT.pure] at h; cases h

/-! ## §3  Full `ifThenElse (.var cond) t e` simulation

Combine the syntactic unpacker, the source-side inverse, and the
appropriate RIfNz dispatcher.  The agreement on `cond` translates the
Hax-side `.bool` value to the LowCT-side scalar (1 for true, 0 for
false), which selects the matching branch on each side. -/

theorem haxToLowCT_simulates_ifThenElse_var
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (cond : String) (t e : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (ihT : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulates bi fuel N leafSpec t c' env_a env_b rs_a v_a)
    (ihE : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulates bi fuel N leafSpec e c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulates bi fuel N leafSpec
      (.ifThenElse (.var cond) t e) c env env' rs v := by
  intro hHax hEval hAgree
  -- Unpack syntactic translation.
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ :=
    haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  -- Split into the true / false branches via the source-side inverse.
  rcases evalImp_ifThenElse_var_inv bi fuel cond t e env v env' hEval with
    ⟨hCondTrue, hTeval⟩ | ⟨hCondFalse, hEeval⟩
  · -- True branch.  Agreement gives `rs.rsScalar cond = 1`.
    have hScalar : rs.rsScalar cond = 1 := by
      have := hAgree cond (.bool true) hCondTrue 1
      simpa [valueToScalar] using this
    -- Apply IH on the THEN branch.
    obtain ⟨rs', hTexec, hAgree'⟩ :=
      ihT tC env env' rs v hTtrans hTeval hAgree
    -- Dispatch RIfNz on the true side.
    exact ⟨rs',
      rustExec_RIfNz_dispatch_true N leafSpec cond tC eC rs rs' 1
        hScalar (by decide) hTexec,
      hAgree'⟩
  · -- False branch.  Agreement gives `rs.rsScalar cond = 0`.
    have hScalar : rs.rsScalar cond = 0 := by
      have := hAgree cond (.bool false) hCondFalse 0
      simpa [valueToScalar] using this
    -- Apply IH on the ELSE branch.
    obtain ⟨rs', hEexec, hAgree'⟩ :=
      ihE eC env env' rs v hEtrans hEeval hAgree
    -- Dispatch RIfNz on the false side.
    exact ⟨rs',
      rustExec_RIfNz_dispatch_false N leafSpec cond tC eC rs rs'
        hScalar hEexec,
      hAgree'⟩

end CatCrypt.Crypto.Hax
