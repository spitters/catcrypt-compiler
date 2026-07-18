/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.JasminMonoSem

/-!
# Dead-code elimination on the Jasmin SSA subset

Liveness-directed dead-code elimination over the monomorphic Jasmin SSA
fragment, with a proved preservation theorem for the pure reference
evaluator `pureEvalMonoCmd`.

The Jasmin → SSA *translation* with its semantics-preservation proof now
targets `catCryptDialect` directly (the MLIR-aligned `Com` dialect):

* `CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialect`
  (`translateMonoCmdD` / `translateMonoExprD` / `translateBinOpD`), and
* `CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialectNative`
  (`translateMonoCmdD_denoteSP_native` — the reference-semantics
  correctness, proved directly by induction, sorry-free).

This module keeps the translator-independent liveness analysis used by the
ports and case studies:

* `monoExprVars` / `monoCmdLiveVars` — variables read by an expression /
  live across a command;
* `pureEvalMonoExpr_irrelevant` / `pureEvalMonoCmd_irrelevant` — agreement
  on the live variables determines the pure evaluation;
* `simpleDCE` / `simpleDCE_correct` — liveness-directed DCE preserves
  `pureEvalMonoCmd`.

The covered fragment is the SSA `Cassgn` spine plus the `ADD_64` / `ADC_64`
carry intrinsics. The remaining `Copn` catch-all in
`pureEvalMonoCmd_irrelevant` / `simpleDCE_correct` is a documented
structural gap (Lean's `match` compiler drops the negative shape
information in the no-op wildcard arm).
-/

namespace CatCrypt.Crypto.Jasmin.ToSSA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

set_option autoImplicit false

/-! ## Live-variable analysis -/

/-- Variables read by an expression in the monomorphic fragment. -/
def monoExprVars : PExpr → List Var
  | .Pvar gv => [gv.gv.var]
  | .Papp2 _ (.Pvar x) (.Pvar y) => [x.gv.var, y.gv.var]
  | .Papp2 _ (.Pvar x) (.Pconst _) => [x.gv.var]
  | .Papp1 _ (.Pvar x) => [x.gv.var]
  | _ => []

/-- Variables that matter for computing `pureEvalMonoCmd`: variables read
    by instructions or the return variable itself. Computed backwards
    from the return. Handles the `ADD_64` / `ADC_64` `Copn` shapes:
    subtract lvals (cf, r), add reads (a, b, [cin]). -/
def monoCmdLiveVars (retVar : Var) : List InstrR → List Var
  | [] => [retVar]
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    let liveRest := monoCmdLiveVars retVar rest
    if x.var ∈ liveRest then
      (liveRest.filter (fun v => !decide (v = x.var))) ++ monoExprVars e
    else
      liveRest
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADD_64"⟩) [.Pvar av, .Pvar bv] :: rest =>
    let liveRest := monoCmdLiveVars retVar rest
    (liveRest.filter (fun v => !decide (v = cfv.var) && !decide (v = rv.var)))
      ++ [av.gv.var, bv.gv.var]
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADC_64"⟩) [.Pvar av, .Pvar bv, .Pvar cinv] :: rest =>
    let liveRest := monoCmdLiveVars retVar rest
    (liveRest.filter (fun v => !decide (v = cfv.var) && !decide (v = rv.var)))
      ++ [av.gv.var, bv.gv.var, cinv.gv.var]
  | _ :: rest => monoCmdLiveVars retVar rest

/-- If two environments agree on the variables read by an expression,
    `pureEvalMonoExpr` gives the same result. -/
theorem pureEvalMonoExpr_irrelevant {n : Nat}
    (env₁ env₂ : Var → BitVec n) (e : PExpr)
    (h : ∀ w ∈ monoExprVars e, env₁ w = env₂ w) :
    pureEvalMonoExpr n env₁ e = pureEvalMonoExpr n env₂ e := by
  cases e with
  | Pvar gv =>
    simp [pureEvalMonoExpr, monoExprVars] at h ⊢; exact h
  | Papp2 op e1 e2 =>
    cases e1 with
    | Pvar x =>
      cases e2 with
      | Pvar y =>
        simp [monoExprVars] at h
        obtain ⟨hx, hy⟩ := h
        cases op <;> simp [pureEvalMonoExpr, hx, hy]
      | Pconst k =>
        simp [monoExprVars] at h
        cases op <;> simp [pureEvalMonoExpr, h]
      | _ => simp [pureEvalMonoExpr]
    | _ => simp [pureEvalMonoExpr]
  | Papp1 op arg =>
    cases arg with
    | Pvar x =>
      simp [monoExprVars] at h
      cases op <;> simp [pureEvalMonoExpr, h]
    | _ => simp [pureEvalMonoExpr]
  | _ => simp [pureEvalMonoExpr]

/-- If two environments agree on the live variables of a command,
    `pureEvalMonoCmd` gives the same result. -/
theorem pureEvalMonoCmd_irrelevant {n : Nat}
    (env₁ env₂ : Var → BitVec n) (retVar : Var) (cmd : List InstrR)
    (h : ∀ w ∈ monoCmdLiveVars retVar cmd, env₁ w = env₂ w) :
    pureEvalMonoCmd n env₁ retVar cmd = pureEvalMonoCmd n env₂ retVar cmd := by
  induction cmd generalizing env₁ env₂ with
  | nil =>
    simp [pureEvalMonoCmd, monoCmdLiveVars] at h ⊢
    exact h
  | cons instr rest ih =>
    cases instr with
    | Cassgn lv tag ty e =>
      cases lv with
      | Lvar x =>
        simp only [pureEvalMonoCmd]
        apply ih
        intro w hw
        simp only [monoCmdLiveVars] at h
        by_cases hx_live : x.var ∈ monoCmdLiveVars retVar rest
        · simp [hx_live] at h
          by_cases hw_eq : w = x.var
          · subst hw_eq; simp
            apply pureEvalMonoExpr_irrelevant
            intro v hv; exact h v (Or.inr hv)
          · simp [hw_eq]
            exact h w (Or.inl ⟨hw, hw_eq⟩)
        · simp [hx_live] at h
          by_cases hw_eq : w = x.var
          · subst hw_eq; exact absurd hw hx_live
          · simp [hw_eq]; exact h w hw
      | _ => simp only [pureEvalMonoCmd]; exact ih _ _ (by simp [monoCmdLiveVars] at h ⊢; exact h)
    | Copn _ _ _ _ =>
      -- For ADD_64/ADC_64 shapes, env₁ and env₂ updates depend on
      -- argument variables (a, b, [cin]) which are now in
      -- `monoCmdLiveVars`. For other Copn shapes, it's a no-op.
      -- **Open (same wildcard-match obstacle as the `Copn` cases of
      -- `simpleDCE_correct`).** Both `pureEvalMonoCmd` *and*
      -- `monoCmdLiveVars` need to unfold on an abstract `Copn lvs op es`,
      -- but Lean's `match` compiler discards the "not the ADD_64/ADC_64
      -- shape" negation in the no-op arm, so neither `simp only
      -- [pureEvalMonoCmd, monoCmdLiveVars]` (no progress) nor `rw`
      -- (unprovable abstract-shape side goals) discharges it. The
      -- ADD_64/ADC_64 arms are tractable; only the no-op catch-all is
      -- blocked, and closing it honestly needs a full LVal/SOpn/PExpr
      -- head-shape enumeration. Out of scope; documented structural gap.
      sorry
    | Cif _ _ _ | Cfor _ _ _ | Cwhile _ _ _ | Ccall _ _ _ _ =>
      simp only [pureEvalMonoCmd]
      exact ih _ _ (by simp [monoCmdLiveVars] at h ⊢; exact h)

/-- A dead assignment (to a variable not live in the rest) can be removed. -/
theorem pureEvalMonoCmd_dead_elim {n : Nat}
    (env : Var → BitVec n) (retVar : Var) (x : VarI) (tag : AssgnTag)
    (ty : SType) (e : PExpr) (rest : List InstrR)
    (h_dead : x.var ∉ monoCmdLiveVars retVar rest) :
    pureEvalMonoCmd n env retVar (.Cassgn (.Lvar x) tag ty e :: rest) =
    pureEvalMonoCmd n env retVar rest := by
  simp only [pureEvalMonoCmd]
  apply pureEvalMonoCmd_irrelevant
  intro w hw
  by_cases hw_eq : w = x.var
  · subst hw_eq; exact absurd hw h_dead
  · simp [hw_eq]

/-- Simple dead code elimination: remove assignments to variables not read later.
    Checks liveness against the original (pre-DCE) rest for straightforward correctness. -/
def simpleDCE (retVar : Var) : List InstrR → List InstrR
  | [] => []
  | .Cassgn (.Lvar x) tag ty e :: rest =>
    if x.var ∈ monoCmdLiveVars retVar rest then
      .Cassgn (.Lvar x) tag ty e :: simpleDCE retVar rest
    else
      simpleDCE retVar rest
  | instr :: rest => instr :: simpleDCE retVar rest

/-- **DCE correctness**: `simpleDCE` preserves `pureEvalMonoCmd`. -/
theorem simpleDCE_correct {n : Nat}
    (env : Var → BitVec n) (retVar : Var) (cmd : List InstrR) :
    pureEvalMonoCmd n env retVar (simpleDCE retVar cmd) =
    pureEvalMonoCmd n env retVar cmd := by
  induction cmd generalizing env with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | Cassgn lv tag ty e =>
      cases lv with
      | Lvar x =>
        simp only [simpleDCE]
        by_cases h_live : x.var ∈ monoCmdLiveVars retVar rest
        · simp [h_live, pureEvalMonoCmd, ih]
        · simp [h_live]
          rw [ih]
          exact (pureEvalMonoCmd_dead_elim env retVar x tag ty e _ h_live).symm
      | _ => simp [simpleDCE, pureEvalMonoCmd, ih]
    | Copn lvs tag op es =>
      -- `simpleDCE` is a no-op on the `.Copn` head, so the goal is
      -- `pureEvalMonoCmd … (Copn lvs tag op es :: simpleDCE rest) =
      --  pureEvalMonoCmd … (Copn lvs tag op es :: rest)`. Drive the match
      -- on the `Copn` head ourselves (rcases on the ADD_64/ADC_64 shape vs
      -- the no-op catch-all); each leaf reduces `pureEvalMonoCmd` to a
      -- recursion on `simpleDCE rest` / `rest` under the *same* env, closed
      -- by `ih`.
      simp only [simpleDCE]
      match lvs, op, es with
      | [.Lnone _ _, .Lvar _, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar _],
        .Oasm ⟨"ADD_64"⟩, [.Pvar _, .Pvar _] =>
        simp only [pureEvalMonoCmd]; exact ih _
      | [.Lnone _ _, .Lvar _, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar _],
        .Oasm ⟨"ADC_64"⟩, [.Pvar _, .Pvar _, .Pvar _] =>
        simp only [pureEvalMonoCmd]; exact ih _
      | _, _, _ =>
        -- No-op catch-all. Open goal: even after driving the head-shape
        -- match ourselves, the proof-`match` wildcard re-binds
        -- `lvs/op/es` generically, so `pureEvalMonoCmd` cannot reduce to
        -- its `| _ :: rest` arm — `simp only [pureEvalMonoCmd]` makes no
        -- progress and the `ih`-form is not defeq. Lean's `match` compiler
        -- drops the "not the ADD_64/ADC_64 shape" negation in the wildcard,
        -- so closing it honestly needs a full `List LVal`/`SOpn`/`List
        -- PExpr` head-shape enumeration or a `rest`-independent refactor of
        -- `pureEvalMonoCmd`'s `Copn`-head env-update. Out of scope; the two
        -- ADD_64/ADC_64 shapes above are fully closed.
        sorry
    | Cif _ _ _ | Cfor _ _ _ | Cwhile _ _ _ | Ccall _ _ _ _ =>
      simp [simpleDCE, pureEvalMonoCmd, ih]

end CatCrypt.Crypto.Jasmin.ToSSA
