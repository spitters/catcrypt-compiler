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

end

end CatCrypt.Crypto.Jasmin.ToSSA
