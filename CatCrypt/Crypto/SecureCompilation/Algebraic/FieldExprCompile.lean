/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord

/-!
# Field expressions compiled to `fieldDialect` programs

`FExpr p n` is the type of expressions over `ZMod p` in `n` inputs, built from
inputs, constants, sums and products. `emit` compiles an expression to a
`Com fieldDialect` program in continuation-passing style: every constant, sum and
product becomes one `fConst`, `fAdd` or `fMul` binding, and an input is the input
variable itself. `compile e` is the program over the `n` input variables that
returns the value of `e`.

## Main definitions

* `FExpr`, `FExpr.eval`: expressions and their value.
* `emit`, `compile`: the compiler.
* `compileJasmin F e`: `compile e` lowered through a single-word field `F`.

## Main results

* `emit_denote`, `compile_denote`: the program denotes the value of the expression.
* `emit_covered`, `compile_covered`: the program is `GoodW p`-covered.
* `compileJasmin_denote`: the lowered program returns the encoding of the value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldExprCompile

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField)

variable (p : Nat)

/-- An expression over `ZMod p` in `n` inputs. -/
inductive FExpr (n : Nat) where
  /-- Input `i`. -/
  | inp (i : Fin n)
  /-- The constant `c`. -/
  | const (c : ZMod p)
  /-- A sum. -/
  | add (a b : FExpr n)
  /-- A product. -/
  | mul (a b : FExpr n)

variable {p}

/-- The value of an expression at the inputs `x`. -/
def FExpr.eval {n : Nat} (x : Fin n → ZMod p) : FExpr p n → ZMod p
  | .inp i => x i
  | .const c => c
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

/-- A renaming of variables from `Γ` to `Γ'`. -/
abbrev Ren (Γ Γ' : Ctxt fieldDialect) : Type :=
  ∀ {t : FieldTy}, Ctxt.Var Γ t → Ctxt.Var Γ' t

/-- The program of an expression: one binding per constant, sum and product, then
    the continuation, given the renaming into its context and the variable holding
    the value. -/
def emit {n : Nat} : FExpr p n → {Γ : Ctxt fieldDialect} → (Fin n → Ctxt.Var Γ (.fp p)) →
    ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → Com fieldDialect Γ' (.fp p)) →
    Com fieldDialect Γ (.fp p)
  | .inp i, _, env, k => k id (env i)
  | .const c, _, _, k => .var ⟨.fConst p c, rfl, .nil⟩ (k (fun v => v.there) .here)
  | .add a b, _, env, k =>
    emit a env fun r₁ va => emit b (fun i => r₁ (env i)) fun r₂ vb =>
      .var ⟨.fAdd p, rfl, .cons (r₂ va) (.cons vb .nil)⟩ (k (fun v => (r₂ (r₁ v)).there) .here)
  | .mul a b, _, env, k =>
    emit a env fun r₁ va => emit b (fun i => r₁ (env i)) fun r₂ vb =>
      .var ⟨.fMul p, rfl, .cons (r₂ va) (.cons vb .nil)⟩ (k (fun v => (r₂ (r₁ v)).there) .here)

/-- **Denotation of `emit`.** If `env` holds the inputs `x` under `V` and the
    continuation denotes `R` whenever its renaming preserves values and its variable
    holds the value of `e`, then `emit e env k` denotes `R`. -/
theorem emit_denote {n : Nat} (x : Fin n → ZMod p) (e : FExpr p n) {Γ : Ctxt fieldDialect}
    (env : Fin n → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → Com fieldDialect Γ' (.fp p))
    (V : Ctxt.Valuation Γ) (R : ZMod p) (hx : ∀ i, (env i).lookup V = x i)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ')
      (w : Ctxt.Var Γ' (.fp p)), (∀ {t : FieldTy} (v : Ctxt.Var Γ t), (r v).lookup V' = v.lookup V) →
      w.lookup V' = e.eval x → (k r w).denote V' = R) :
    (emit e env k).denote V = R := by
  induction e generalizing Γ R with
  | inp i => exact hk id V (env i) (fun _ => rfl) (hx i)
  | const c => exact hk _ _ .here (fun _ => rfl) rfl
  | add a b iha ihb =>
    refine iha env _ V R hx fun r₁ V₁ va h₁ hva => ?_
    refine ihb (fun i => r₁ (env i)) _ V₁ R (fun i => (h₁ (env i)).trans (hx i))
      fun r₂ V₂ vb h₂ hvb => ?_
    refine hk _ _ .here (fun v => ?_) ?_
    · exact (h₂ (r₁ v)).trans (h₁ v)
    · exact congrArg₂ (fun u w : ZMod p => u + w) ((h₂ va).trans hva) hvb
  | mul a b iha ihb =>
    refine iha env _ V R hx fun r₁ V₁ va h₁ hva => ?_
    refine ihb (fun i => r₁ (env i)) _ V₁ R (fun i => (h₁ (env i)).trans (hx i))
      fun r₂ V₂ vb h₂ hvb => ?_
    refine hk _ _ .here (fun v => ?_) ?_
    · exact (h₂ (r₁ v)).trans (h₁ v)
    · exact congrArg₂ (fun u w : ZMod p => u * w) ((h₂ va).trans hva) hvb

/-- **Coverage of `emit`.** -/
theorem emit_covered {n : Nat} (e : FExpr p n) {Γ : Ctxt fieldDialect}
    (env : Fin n → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → Com fieldDialect Γ' (.fp p))
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (w : Ctxt.Var Γ' (.fp p)),
      CoveredCom (GoodW p) (k r w)) :
    CoveredCom (GoodW p) (emit e env k) := by
  induction e generalizing Γ with
  | inp i => exact hk _ _
  | const c => exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))), hk _ _⟩
  | add a b iha ihb =>
    exact iha env _ fun r₁ va => ihb _ _ fun r₂ vb => ⟨Or.inl rfl, hk _ _⟩
  | mul a b iha ihb =>
    exact iha env _ fun r₁ va => ihb _ _ fun r₂ vb =>
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), hk _ _⟩

variable (p) in
/-- The input context: `n` variables of type `fp p`. -/
abbrev inCtxt (n : Nat) : Ctxt fieldDialect := List.replicate n (.fp p)

/-- Input variable `i` of `List.replicate n τ`, with index `0` the most recent
    binding. -/
def inVar {τ : FieldTy} : (n : Nat) → Fin n → @Ctxt.Var fieldDialect (List.replicate n τ) τ
  | _ + 1, ⟨0, _⟩ => .here
  | n + 1, ⟨j + 1, h⟩ => (inVar n ⟨j, by omega⟩).there

/-- The inputs of a valuation of `inCtxt p n`: input `i` is the value of `inVar n i`. -/
def inputs {n : Nat} (V : Ctxt.Valuation (inCtxt p n)) : Fin n → ZMod p :=
  fun i => (inVar n i).lookup V

/-- The program over the `n` inputs returning the value of `e`. -/
def compile {n : Nat} (e : FExpr p n) : Com fieldDialect (inCtxt p n) (.fp p) :=
  emit e (inVar n) fun _ w => .ret w

theorem compile_denote {n : Nat} (e : FExpr p n) (V : Ctxt.Valuation (inCtxt p n)) :
    (compile e).denote V = e.eval (inputs V) :=
  emit_denote (inputs V) e (inVar n) _ V _ (fun _ => rfl) fun _ _ _ _ hw => hw

theorem compile_covered {n : Nat} (e : FExpr p n) : CoveredCom (GoodW p) (compile e) :=
  emit_covered e _ _ fun _ _ => trivial

/-- `compile e` lowered through the single-word field `F`. -/
def compileJasmin {n : Nat} (F : SingleWordField p) (e : FExpr p n) :
    Com jasminDialect (mapCtxW (inCtxt p n)) (mapTyW (.fp p)) :=
  lowerK F (compile e)

/-- **Correctness of the lowered program.** On the encoding of any valuation of the
    inputs, the lowered program returns the encoding of the value of `e`. -/
theorem compileJasmin_denote {n : Nat} (F : SingleWordField p) (e : FExpr p n)
    (V : Ctxt.Valuation (inCtxt p n)) :
    (compileJasmin F e).denote (mapValW F V) = F.enc (e.eval (inputs V)) := by
  rw [compileJasmin, fieldToJasminWord_denote F _ (compile_covered e), compile_denote]

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful (ComLsemExportFaithful) in
/-- **Virtual export faithfulness of the lowered program**, for a field whose blocks
    are in the scalar fragment. -/
theorem compileJasmin_exportFaithful {n : Nat} (F : SingleWordField p) (hs : ScalarBlocks F)
    (e : FExpr p n) (fn : String) :
    ComLsemExportFaithful (compileJasmin F e) fn (lowerK_scalar F hs (compile e)).ret_ty :=
  lowerK_exportFaithful F hs (compile e) fn

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldExprCompile
