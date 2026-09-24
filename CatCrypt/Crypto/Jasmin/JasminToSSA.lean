/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JasminMonoSem

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
  correctness, proved directly by induction, fully proved).

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

@[expose] public section

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

/-- `monoCmdLiveVars` on a single `Copn`, characterized through `copnCarry?`. -/
theorem monoCmdLiveVars_Copn (retVar : Var) (lvs : List LVal) (tag : AssgnTag)
    (op : SOpn) (es : List PExpr) (rest : List InstrR) :
    monoCmdLiveVars retVar (InstrR.Copn lvs tag op es :: rest) =
      match copnCarry? lvs op es with
      | some (cf, r, a, b, cin) =>
          ((monoCmdLiveVars retVar rest).filter (fun v => !decide (v = cf) && !decide (v = r)))
            ++ (a :: b :: cin.elim [] (fun cv => [cv]))
      | none => monoCmdLiveVars retVar rest := by
  fun_cases copnCarry? lvs op es <;>
    first
    | (simp [monoCmdLiveVars]; done)
    | (rw [monoCmdLiveVars] <;> grind [monoCmdLiveVars])

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
    | Copn lvs tag op es =>
      -- The head's env-effect is tail-independent, so `pureEvalMonoCmd_append`
      -- on the singleton prefix reduces the goal to `ih` applied to the two
      -- post-`Copn` environments; the remaining obligation is that the single
      -- `Copn` step preserves agreement on the live variables of `rest`.
      have e0 : (InstrR.Copn lvs tag op es :: rest) = [InstrR.Copn lvs tag op es] ++ rest := rfl
      rw [e0, pureEvalMonoCmd_append, pureEvalMonoCmd_append]
      apply ih
      intro w hw
      rw [monoCmdLiveVars_Copn] at h
      rw [pureEvalFinalEnv_Copn, pureEvalFinalEnv_Copn]
      cases hc : copnCarry? lvs op es with
      | none => simp only [hc] at h ⊢; exact h w hw
      | some val =>
        obtain ⟨cf, r, a, b, cin⟩ := val
        simp only [hc] at h ⊢
        have ha : env₁ a = env₂ a := h a (by simp)
        have hb : env₁ b = env₂ b := h b (by simp)
        have hcin : (cin.elim false fun cv => decide ((env₁ cv).toNat ≠ 0))
            = (cin.elim false fun cv => decide ((env₂ cv).toNat ≠ 0)) := by
          cases cin with
          | none => rfl
          | some cv => simp only [Option.elim, h cv (by simp)]
        by_cases hwr : w = r
        · subst hwr; simp only [↓reduceIte, ha, hb, hcin]
        · by_cases hwcf : w = cf
          · subst hwcf; simp only [if_neg hwr, ↓reduceIte, ha, hb, hcin]
          · simp only [if_neg hwr, if_neg hwcf]
            exact h w (by simp_all [List.mem_append, List.mem_filter, hwr, hwcf])
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
      --  pureEvalMonoCmd … (Copn lvs tag op es :: rest)`. The head's env
      -- effect is tail-independent, so `pureEvalMonoCmd_head_congr` closes it
      -- for any `Copn` shape at once (no ADD_64/ADC_64 vs no-op split needed).
      simp only [simpleDCE]
      exact pureEvalMonoCmd_head_congr n env retVar (.Copn lvs tag op es) _ _ ih
    | Cif _ _ _ | Cfor _ _ _ | Cwhile _ _ _ | Ccall _ _ _ _ =>
      simp [simpleDCE, pureEvalMonoCmd, ih]

end CatCrypt.Crypto.Jasmin.ToSSA
