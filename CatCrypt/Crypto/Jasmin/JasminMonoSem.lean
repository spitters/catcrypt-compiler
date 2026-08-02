/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CryptoSSA
import CatCrypt.Crypto.Jasmin.JasminAST

/-!
# `CProg`-free reference semantics for the monomorphic Jasmin fragment

This module holds the `CExpr` / `CProg`-**free** reference-semantics core that
both the `CProg`-targeting translator (`JasminToSSA.lean`) and the
dialect-targeting translators (`JasminToSSADialect.lean` /
`JasminToSSADialectNative.lean`) share:

* `MonoVarMap` — the monomorphic Jasmin `Var` → de Bruijn `CVar` map (plus its
  `empty` / `extend` / `extend2` builders);
* `monoAgrees` — the simulation invariant (tracked variable values agree),
  preserved under `extend` (`monoAgrees_extend`) and `extend2`
  (`monoAgrees_extend2`);
* `pureEvalMonoExpr` / `pureEvalMonoCmd` — the pure Jasmin reference evaluator
  on the word fragment (plus the `boolToBVaux` carry-bit packer).

None of these mention the `CryptoSSA` `CExpr` / `CProg` inductives (the
de Bruijn machinery `CVar` / `HVec` / `Ctx` lives in `CryptoSSA` and is reused
unchanged). Extracting them here de-couples the dialect-translator correctness
layer from `CProg`, a prerequisite for retiring the `CExpr` / `CProg`
inductives.
-/

namespace CatCrypt.Crypto.Jasmin.ToSSA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-! ## Section 1: Monomorphic Variable Maps -/

/-- Monomorphic variable map: maps Jasmin `Var` to CryptoSSA De Bruijn indices. -/
def MonoVarMap (Γ : Ctx) (n : Nat) := Var → Option (CVar Γ (.sword n))

def MonoVarMap.empty {n : Nat} : MonoVarMap ([] : Ctx) n := fun _ => none

/-- Extend with a new binding at `.here`; shift existing bindings. -/
def MonoVarMap.extend {Γ : Ctx} {n : Nat} (m : MonoVarMap Γ n) (v : Var) :
    MonoVarMap (CryptoTy.sword n :: Γ) n :=
  fun w => if w = v then some .here else (m w).map .there

/-- Extend a map with two fresh sword-`n` bindings: the innermost
    (most recently bound, at `.here`) goes to `lastVar`, and the one
    below it (at `.there .here`) goes to `secondVar`. Existing map
    entries get shifted three places (for pair, fst, snd bindings).
    Used for pair-destructuring `Copn` intrinsics: we bind the pair,
    then `fst` (carry), then `snd` (sum). -/
def MonoVarMap.extend2 {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (secondVar lastVar : Var) :
    MonoVarMap (.sword n :: .sword n :: .pair (.sword n) (.sword n) :: Γ) n :=
  fun w =>
    if w = lastVar then some .here
    else if w = secondVar then some (.there .here)
    else ((m w).map .there |>.map .there |>.map .there)

/-! ## Section 2: Agreement Relation -/

/-- The simulation invariant: tracked variable values agree. -/
def monoAgrees {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (V : HVec Γ) (env : Var → BitVec n) : Prop :=
  ∀ (v : Var) (cv : CVar Γ (.sword n)),
    m v = some cv → cv.lookup V = env v

/-- Agreement is preserved when extending with a new variable. -/
theorem monoAgrees_extend {Γ : Ctx} {n : Nat}
    {m : MonoVarMap Γ n} {V : HVec Γ} {env : Var → BitVec n}
    (h : monoAgrees m V env) (v : Var) (val : BitVec n) :
    monoAgrees (m.extend v) (HVec.cons val V)
      (fun w => if w = v then val else env w) := by
  intro w cv h_lookup
  simp only [MonoVarMap.extend] at h_lookup
  split at h_lookup
  · rename_i h_eq; subst h_eq
    cases h_lookup; simp [CVar.lookup]
  · rename_i h_neq
    simp only [Option.map] at h_lookup
    split at h_lookup
    · rename_i cv' h_eq; cases h_lookup
      simp [CVar.lookup, h_neq, h w cv' h_eq]
    · exact absurd h_lookup (by simp)

/-- **`extend2` agreement preservation**: when the new pair binding holds
    `pval = (cfVal, rVal)` and we track `secondVar ↦ cf, lastVar ↦ r`,
    agreement is preserved. -/
theorem monoAgrees_extend2 {Γ : Ctx} {n : Nat}
    {m : MonoVarMap Γ n} {V : HVec Γ} {env : Var → BitVec n}
    (h : monoAgrees m V env) (secondVar lastVar : Var)
    (pval : BitVec n × BitVec n) (cfVal rVal : BitVec n)
    (_h_cf : cfVal = pval.fst) (_h_r : rVal = pval.snd) :
    monoAgrees (m.extend2 secondVar lastVar)
      (HVec.cons rVal (HVec.cons cfVal (HVec.cons pval V)))
      (fun w => if w = lastVar then rVal
                else if w = secondVar then cfVal
                else env w) := by
  intro w cv h_lookup
  simp only [MonoVarMap.extend2] at h_lookup
  by_cases h1 : w = lastVar
  · subst h1; simp at h_lookup; cases h_lookup
    simp [CVar.lookup]
  · simp [h1] at h_lookup
    by_cases h2 : w = secondVar
    · subst h2; simp at h_lookup; cases h_lookup
      simp [CVar.lookup, h1]
    · simp [h2] at h_lookup
      obtain ⟨cv₀, hm, hcv⟩ := h_lookup
      subst hcv
      simp [CVar.lookup, h1, h2]
      exact h w cv₀ hm

/-! ## Section 3: Pure Evaluation (Reference Semantics) -/

/-- Pure evaluation of a Jasmin expression in the word fragment. -/
def pureEvalMonoExpr (n : Nat) (env : Var → BitVec n) : PExpr → BitVec n
  | .Pvar gv => env gv.gv.var
  | .Pconst z => BitVec.ofInt n z
  | .Papp2 (.Olxor _) (.Pvar x) (.Pvar y) => env x.gv.var ^^^ env y.gv.var
  | .Papp2 (.Oland _) (.Pvar x) (.Pvar y) => env x.gv.var &&& env y.gv.var
  | .Papp2 (.Olor _) (.Pvar x) (.Pvar y) => env x.gv.var ||| env y.gv.var
  | .Papp2 (.Oadd _) (.Pvar x) (.Pvar y) => env x.gv.var + env y.gv.var
  | .Papp2 (.Osub _) (.Pvar x) (.Pvar y) => env x.gv.var - env y.gv.var
  | .Papp2 (.Omul _) (.Pvar x) (.Pvar y) => env x.gv.var * env y.gv.var
  | .Papp1 (.Olnot _) (.Pvar x) => ~~~(env x.gv.var)
  | .Papp2 (.Olsl _) (.Pvar x) (.Pconst k) => env x.gv.var <<< k.toNat
  | .Papp2 (.Olsr _) (.Pvar x) (.Pconst k) => BitVec.ushiftRight (env x.gv.var) k.toNat
  | _ => 0

/-- Pack a `Bool` into a `BitVec n`: `true ↦ 1`, `false ↦ 0`. -/
def boolToBVaux (n : Nat) : Bool → BitVec n
  | true => 1
  | false => 0

/-- Pure evaluation of an SSA-compatible command sequence. Handles
    `Cassgn` directly, plus the `ADD_64` / `ADC_64` multi-output
    intrinsics (mirrors `JasminCT.pureEvalMonoCmdExt` for these two
    cases). All other instructions are treated as no-ops. -/
def pureEvalMonoCmd (n : Nat) (env : Var → BitVec n) (retVar : Var) :
    List InstrR → BitVec n
  | [] => env retVar
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    pureEvalMonoCmd n
      (fun w => if w = x.var then pureEvalMonoExpr n env e else env w)
      retVar rest
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADD_64"⟩) [.Pvar av, .Pvar bv] :: rest =>
    let a := env av.gv.var
    let b := env bv.gv.var
    let p := BitVec.adc a b false
    pureEvalMonoCmd n
      (fun w =>
        if w = rv.var then p.snd
        else if w = cfv.var then boolToBVaux n p.fst
        else env w)
      retVar rest
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADC_64"⟩) [.Pvar av, .Pvar bv, .Pvar cinv] :: rest =>
    let a := env av.gv.var
    let b := env bv.gv.var
    let cinBool := (env cinv.gv.var).toNat ≠ 0
    let p := BitVec.adc a b cinBool
    pureEvalMonoCmd n
      (fun w =>
        if w = rv.var then p.snd
        else if w = cfv.var then boolToBVaux n p.fst
        else env w)
      retVar rest
  | _ :: rest => pureEvalMonoCmd n env retVar rest

/-- Final environment after processing a list of commands. Mirrors the arm
    structure of `pureEvalMonoCmd`, including the `Copn ADD_64`/`ADC_64` arms
    (written inline, no `let`, so `fun_induction`/`simp` normalize identically
    to `pureEvalMonoCmd`'s unfolded arms). -/
def pureEvalFinalEnv (n : Nat) (env : Var → BitVec n) : List InstrR → Var → BitVec n
  | [] => env
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    pureEvalFinalEnv n
      (fun w => if w = x.var then pureEvalMonoExpr n env e else env w)
      rest
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADD_64"⟩) [.Pvar av, .Pvar bv] :: rest =>
    pureEvalFinalEnv n
      (fun w =>
        if w = rv.var then (BitVec.adc (env av.gv.var) (env bv.gv.var) false).snd
        else if w = cfv.var then boolToBVaux n (BitVec.adc (env av.gv.var) (env bv.gv.var) false).fst
        else env w)
      rest
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADC_64"⟩) [.Pvar av, .Pvar bv, .Pvar cinv] :: rest =>
    pureEvalFinalEnv n
      (fun w =>
        if w = rv.var then
          (BitVec.adc (env av.gv.var) (env bv.gv.var) ((env cinv.gv.var).toNat ≠ 0)).snd
        else if w = cfv.var then
          boolToBVaux n (BitVec.adc (env av.gv.var) (env bv.gv.var) ((env cinv.gv.var).toNat ≠ 0)).fst
        else env w)
      rest
  | _ :: rest => pureEvalFinalEnv n env rest

/-- Classifier for the two carry-`Copn` intrinsics. Returns the relevant
    variables — (carry-flag out, result out, addend a, addend b, carry-in?) —
    for a recognized `ADD_64`/`ADC_64` shape, `none` otherwise. Its match arms
    mirror the `Copn` arms of `pureEvalMonoCmd` / `pureEvalFinalEnv` /
    `monoCmdLiveVars`, so `split`ing it supplies the negative shape information
    that a bare `Copn` head-match discards. -/
def copnCarry? : List LVal → SOpn → List PExpr → Option (Var × Var × Var × Var × Option Var)
  | [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv],
    .Oasm ⟨"ADD_64"⟩, [.Pvar av, .Pvar bv] =>
    some (cfv.var, rv.var, av.gv.var, bv.gv.var, none)
  | [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv],
    .Oasm ⟨"ADC_64"⟩, [.Pvar av, .Pvar bv, .Pvar cinv] =>
    some (cfv.var, rv.var, av.gv.var, bv.gv.var, some cinv.gv.var)
  | _, _, _ => none

/-- `pureEvalFinalEnv` on a single `Copn`, characterized through `copnCarry?`. -/
theorem pureEvalFinalEnv_Copn (n : Nat) (env : Var → BitVec n)
    (lvs : List LVal) (tag : AssgnTag) (op : SOpn) (es : List PExpr) :
    pureEvalFinalEnv n env [InstrR.Copn lvs tag op es] =
      match copnCarry? lvs op es with
      | some (cf, r, a, b, cin) =>
          let p := BitVec.adc (env a) (env b) (cin.elim false (fun cv => (env cv).toNat ≠ 0))
          (fun w => if w = r then p.snd else if w = cf then boolToBVaux n p.fst else env w)
      | none => env := by
  fun_cases copnCarry? lvs op es <;>
    first
    | (simp [pureEvalFinalEnv]; done)
    | (rw [pureEvalFinalEnv] <;> grind [pureEvalFinalEnv])

/-- **Composition lemma**: `pureEvalMonoCmd` over concatenated commands equals
    evaluating the first commands to get a final environment, then evaluating
    the second commands in that environment. -/
theorem pureEvalMonoCmd_append (n : Nat) (env : Var → BitVec n) (retVar : Var)
    (cmds1 cmds2 : List InstrR) :
    pureEvalMonoCmd n env retVar (cmds1 ++ cmds2) =
    pureEvalMonoCmd n (pureEvalFinalEnv n env cmds1) retVar cmds2 := by
  fun_induction pureEvalFinalEnv n env cmds1 <;>
    simp_all [pureEvalMonoCmd, List.cons_append]

/-- Head congruence: the head instruction's env-effect is tail-independent, so
    if two tails agree under every environment, prepending the same instruction
    keeps them equal. Follows from `pureEvalMonoCmd_append` on the singleton
    prefix, sidestepping any per-`Copn`-shape case analysis. -/
theorem pureEvalMonoCmd_head_congr (n : Nat) (env : Var → BitVec n) (retVar : Var)
    (c : InstrR) (L1 L2 : List InstrR)
    (h : ∀ e, pureEvalMonoCmd n e retVar L1 = pureEvalMonoCmd n e retVar L2) :
    pureEvalMonoCmd n env retVar (c :: L1) = pureEvalMonoCmd n env retVar (c :: L2) := by
  have e1 : c :: L1 = [c] ++ L1 := rfl
  have e2 : c :: L2 = [c] ++ L2 := rfl
  rw [e1, e2, pureEvalMonoCmd_append, pureEvalMonoCmd_append, h]

end

end CatCrypt.Crypto.Jasmin.ToSSA
