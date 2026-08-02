/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Hax.HaxToLowCTSimulates

/-!
# H3.bis-final: agreement-extension + letBind lit simulation

Extends the H3 simulation theorem with the agreement-extension lemma
`envAgreesRust_extend_scalar` and the productive letBind-lit simulation
instance `haxToLowCT_simulates_letBind_lit`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Agreement-extension lemma for scalar bindings

When a Hax env is extended at `name` with a value `v` that decodes
to a scalar `n`, and the RustState's scalar slot at `name` is set to
`n`, scalar-agreement is preserved.  This is the missing piece for
the letBind-lit simulation instance. -/

theorem envAgreesRust_extend_scalar
    (env : Env) (rs : RustState) (name : String) (v : Value) (n : Nat)
    (hAgree : envAgreesRust env rs)
    (hDecode : valueToScalar v = some n) :
    envAgreesRust (Env.extend env name v) (rsSetScalar rs name n) := by
  intro m
  unfold nameAgreesScalar
  intro w hLookup k hDecK
  by_cases hm : m = name
  · subst hm
    -- Env.extend env name v m = some v, so w = v
    rw [Env.extend_same] at hLookup
    have hwv : w = v := (Option.some.inj hLookup).symm
    subst hwv
    -- valueToScalar w = some k and = some n ⇒ k = n
    have : k = n := by
      rw [hDecode] at hDecK
      exact (Option.some.inj hDecK).symm
    subst this
    -- (rsSetScalar rs m n).rsScalar m = n
    simp [rsSetScalar]
  · rw [Env.extend_other env name v m hm] at hLookup
    have hRs : (rsSetScalar rs name n).rsScalar m = rs.rsScalar m := by
      simp [rsSetScalar, hm]
    rw [hRs]
    exact hAgree m w hLookup k hDecK

/-! ## §2  `letBind lit` simulation instance

For `.letBind name (.lit l) body`, the translation produces
`RLetU64Zero name (RSeq (RScalarSet name n) bodyC)` where `n` is the
decoded scalar value from the literal and `bodyC = haxToLowCT body`.
This holds for three productive arms of `haxToLowCT`:

* `l = .uintLit w n` (Nat literal), with `n = n` (direct)
* `l = .int n` with `n ≥ 0`, with `n = n.toNat`
* `l = .bool b`, with `n = if b then 1 else 0` (bools are 0/1 scalars)

In each case `valueToScalar (Value.ofLit l) = some n`. -/

/-- Unpack the syntactic translation for the `letBind lit` arm.
    Extracts the body translation `bodyC`, the scalar value `n`, and
    the proof that `Value.ofLit l` decodes to `n`. -/
theorem haxToLowCT_letBind_lit_some
    (name : String) (l : ImpLit) (body : ImpExpr) (c : LowCT)
    (h : haxToLowCT (.letBind name (.lit l) body) = some c) :
    ∃ bodyC n,
      haxToLowCT body = some bodyC ∧
      valueToScalar (Value.ofLit l) = some n ∧
      c = .RLetU64Zero name (.RSeq (.RScalarSet name n) bodyC) := by
  cases l with
  | bool b =>
    simp [haxToLowCT] at h
    cases hBody : haxToLowCT body with
    | none => rw [hBody] at h; simp at h
    | some bodyC =>
      rw [hBody] at h
      simp at h
      refine ⟨bodyC, if b then 1 else 0, rfl, ?_, ?_⟩
      · cases b <;> rfl
      · cases b <;> simp_all
  | int n =>
    by_cases hn : n ≥ 0
    · simp [haxToLowCT, hn] at h
      cases hBody : haxToLowCT body with
      | none => rw [hBody] at h; simp at h
      | some bodyC =>
        rw [hBody] at h
        simp at h
        refine ⟨bodyC, n.toNat, rfl, ?_, h.symm⟩
        simp [valueToScalar, Value.ofLit, hn]
    · simp [haxToLowCT, hn] at h
  | unit =>
    simp [haxToLowCT] at h
  | uintLit w n =>
    simp [haxToLowCT] at h
    cases hBody : haxToLowCT body with
    | none => rw [hBody] at h; simp at h
    | some bodyC =>
      rw [hBody] at h
      simp at h
      refine ⟨bodyC, n, rfl, ?_, h.symm⟩
      simp [valueToScalar, Value.ofLit]
  | sintLit w n =>
    simp [haxToLowCT] at h

theorem haxToLowCT_simulates_letBind_lit
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (l : ImpLit) (body : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (ihBody : ∀ c' env_a env_b rs_a v_a,
                HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulates bi fuel N leafSpec
      (.letBind name (.lit l) body) c env env' rs v := by
  intro hHax hEval hAgree
  -- Unpack the syntactic translation
  obtain ⟨bodyC, n, hBodyTrans, hDecode, hC⟩ :=
    haxToLowCT_letBind_lit_some name l body c hHax
  subst hC
  -- Reduce source-side evaluation to body in extended env
  have hBodyEval := evalImp_letBind_lit_inv bi fuel name l body env v env' hEval
  -- Build the extended-agreement
  have hAgreeExt : envAgreesRust (env.extend name (Value.ofLit l))
                    (rsSetScalar rs name n) :=
    envAgreesRust_extend_scalar env rs name (Value.ofLit l) n hAgree hDecode
  -- Apply IH on body
  obtain ⟨rs', hBodyExec, hAgree'⟩ :=
    ihBody bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name n) v
           hBodyTrans hBodyEval hAgreeExt
  -- Combine via RLetU64Zero + RScalarSet
  exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name n bodyC rs rs' hBodyExec,
         hAgree'⟩

end CatCrypt.Crypto.Hax
