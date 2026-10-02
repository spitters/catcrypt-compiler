/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
public import CatCrypt.Crypto.Optimizer.CopyProp
public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-!
# Global value numbering of `Com jasminDialect` by hash-consing

The instance at `jasminDialect` of the value numbering `AegraphGeneric.gvnGo`, which is
stated for every dialect. The pass walks the let-chain once and carries a renaming
`ρ : Ctxt.Hom Γ Δ` from the context of the input program to the context of the output
program, and a node table `Tbl` from the argument levels of a binding to the pairs
(operation, result level) of the output bindings with those arguments. At a binding
`let x = op(args)` whose operation is pure (`gvnPure`), the renamed expression is looked
up by its key (operation, argument levels); on a hit the binding is dropped and `x` is
mapped to the output variable of the earlier node.

Purity is decided from the operation alone: stack loads and stores, external and
multi-result calls, and the operations of the instruction pairs of the x86 lowering
(`pairedOp`: the multiply and the high multiply, the carry-chain add and its carry-out)
are never merged.

The level machinery (`varLvl`, `getLvl`, `evalKey`, `Sound`, ...) is that of
`AegraphGeneric`, exported under this namespace.

## Main results

* `gvnGo_denote`: under a table sound for the valuation, the output of the traversal
  denotes the input at the pulled-back valuation.
* `gvnCom`, `gvnCom_denote`: the pass from the empty table; it denotes the same function
  as its input.
* `gvnCom_cost_le`: the pass does not increase `comCost`.
* `gvnGo_ctLeak`, `gvnCom_ctLeak_eq`, `gvnCom_constantTime`: for every leakage model
  (`ComLevelCheck.LeakModel`), equal leakage of the input at two valuations gives equal
  leakage of the output, so the pass preserves constant time for every public-equality
  relation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.ComGVN

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph (opCost comCost)
open CatCrypt.Crypto.Optimizer.CopyProp (pullV pullV_id)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (comCostOf)

/-! ## 1. Purity -/

/-- The low halves of the instruction pairs of the x86 lowering: the multiply
    `regArith .mul w`, whose `MUL` the `MULX` fusion pairs with the `MULXHI` of `mulhi w`
    on the same sources, and the carry-chain add `addCarryLo w`, whose `ADCX` sets the
    carry flag that the `setc` of the paired `addCarryHi w` reads. -/
def pairLowOp : JasminOp → Bool
  | .regArith .mul _ | .addCarryLo _ => true
  | _ => false

/-- The operations of the instruction pairs of the x86 lowering: the low halves
    (`pairLowOp`) and the high halves `mulhi w` and `addCarryHi w`. -/
def pairedOp : JasminOp → Bool
  | .mulhi _ | .addCarryHi _ => true
  | op => pairLowOp op

/-- The operations whose bindings the pass may merge: every operation other than a stack
    load or store, an external call, a multi-result call and an operation of an
    instruction pair of the x86 lowering (`pairedOp`). -/
def gvnPure : JasminOp → Bool
  | .stackLoad _ _ | .stackStore _ _ | .extCall _ _ _ | .callN _ _ _ => false
  | op => !pairedOp op

/-! ## 2. Levels and the node table -/

export CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
  (varLvl argLvls getDepth getLvl castTo? gatherArgs evalKey varOfDepth? varOfLvl?
    getDepth_var getLvl_var getLvl_extend_some getLvl_extend_top castTo?_mk
    gatherArgs_extend_some evalKey_extend_some gatherArgs_argLvls evalKey_expr
    varOfDepth?_lookup varOfLvl?_lookup Sound sound_empty sound_extend)

/-- The node table at `jasminDialect`. -/
abbrev Tbl := AegraphGeneric.Tbl jasminDialect

/-- The output variable of type `s` of a recorded node with operation `op` and argument
    levels `lv`, when `op` is pure. -/
def findVar (Δ : Ctxt jasminDialect) (s : JasminTy) (M : Tbl) (op : JasminOp)
    (lv : List Nat) : Option (Ctxt.Var Δ s) :=
  AegraphGeneric.findVar gvnPure Δ s M op lv

theorem findVar_sound {Δ : Ctxt jasminDialect} {s : JasminTy} {M : Tbl} {op : JasminOp}
    {lv : List Nat} {w : Ctxt.Var Δ s} {V : Ctxt.Valuation Δ} (hM : Sound V M)
    (h : findVar Δ s M op lv = some w) : evalKey V op lv = some ⟨s, w.lookup V⟩ :=
  AegraphGeneric.findVar_sound hM h

/-- The table with the node (`op`, `lv`) of result level `n` entered, when `op` is pure. -/
def insertT (M : Tbl) (op : JasminOp) (lv : List Nat) (n : Nat) : Tbl :=
  AegraphGeneric.insertT gvnPure M op lv n

theorem sound_insertT {Δ : Ctxt jasminDialect} {s : JasminTy} {V : Ctxt.Valuation Δ}
    {M : Tbl} (hM : Sound V M) (e : Expr jasminDialect Δ s) :
    Sound (Γ := s :: Δ) (V.extend (e.denote V))
      (insertT M e.op (argLvls e.args) Δ.length) :=
  AegraphGeneric.sound_insertT hM e

/-! ## 3. The pass -/

/-- The pullback of a valuation along a renaming is its `comap`. -/
theorem pullV_eq_comap {Γ Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom Γ Δ)
    (V : Ctxt.Valuation Δ) : pullV ρ V = V.comap ρ :=
  Ctxt.Valuation.ext _ _ fun _ v => by
    rw [← CopyProp.Ctxt.Var.lookup_rename, Ctxt.Valuation.lookup_comap]

/-- Global value numbering under the renaming `ρ` and the node table `M`: the instance of
    `AegraphGeneric.gvnGo` at `gvnPure`. -/
def gvnGo {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (M : Tbl)
    (c : Com jasminDialect Γ t) : Com jasminDialect Δ t :=
  AegraphGeneric.gvnGo gvnPure ρ M c

/-- **Denotation of the traversal.** Under a table sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`. -/
theorem gvnGo_denote : ∀ {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (M : Tbl) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Δ),
    Sound V M → (gvnGo ρ M c).denote V = c.denote (pullV ρ V) := by
  intro Γ Δ t ρ M c V hM
  rw [pullV_eq_comap]
  exact AegraphGeneric.gvnGo_denote gvnPure ρ M c V hM

/-- **Global value numbering**: the traversal from the identity renaming and the empty
    table. -/
def gvnCom {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  gvnGo (Ctxt.Hom.id Γ) ∅ c

/-- **Denotation of the pass.** `gvnCom c` denotes the same function as `c`. -/
theorem gvnCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : (gvnCom c).denote = c.denote :=
  funext fun V => by rw [gvnCom, gvnGo_denote _ _ c V (sound_empty V), pullV_id]

/-! ## 4. Cost and constant time -/

/-- `comCost` is the cost of the generic passes at `opCost`. -/
theorem comCost_eq_comCostOf : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t), comCost c = comCostOf opCost c
  | _, _, .ret _ => rfl
  | _, _, .var _ body => by simp only [comCost, comCostOf, comCost_eq_comCostOf body]

theorem gvnGo_cost_le {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (M : Tbl) (c : Com jasminDialect Γ t) :
    comCost (gvnGo ρ M c) ≤ comCost c := by
  rw [comCost_eq_comCostOf, comCost_eq_comCostOf]
  exact AegraphGeneric.gvnGo_cost_le opCost gvnPure ρ M c

/-- The pass does not increase `comCost`. -/
theorem gvnCom_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : comCost (gvnCom c) ≤ comCost c :=
  gvnGo_cost_le _ _ c

/-! ## 5. Constant time under a leakage model -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime)

/-- The number of events of an operation does not depend on its argument values. -/
theorem opLeak_length (L : LeakModel jasminDialect) (op : JasminOp)
    (a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    (opLeak L op a).length = (opLeak L op b).length :=
  AegraphGeneric.opLeak_length L op a b

/-- The events of a renamed expression are those of the expression at the pulled-back
    valuation. -/
theorem Expr.ctLeak_rename (L : LeakModel jasminDialect) {Γ Δ : Ctxt jasminDialect}
    {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (e : Expr jasminDialect Γ t) (V : Ctxt.Valuation Δ) :
    Expr.ctLeak L (e.rename ρ) V = Expr.ctLeak L e (pullV ρ V) := by
  rw [pullV_eq_comap]
  exact AegraphGeneric.Expr.ctLeak_rename L ρ e V

/-- **Leakage of the traversal.** Under tables sound for `V₁` and `V₂`, equal leakage of
    the input at the pulled-back valuations gives equal leakage of the output. -/
theorem gvnGo_ctLeak (L : LeakModel jasminDialect) : ∀ {Γ Δ : Ctxt jasminDialect}
    {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (M : Tbl) (c : Com jasminDialect Γ t)
    (V₁ V₂ : Ctxt.Valuation Δ), Sound V₁ M → Sound V₂ M →
    Com.ctLeak L c (pullV ρ V₁) = Com.ctLeak L c (pullV ρ V₂) →
    Com.ctLeak L (gvnGo ρ M c) V₁ = Com.ctLeak L (gvnGo ρ M c) V₂ := by
  intro Γ Δ t ρ M c V₁ V₂ h₁ h₂ h
  rw [pullV_eq_comap, pullV_eq_comap] at h
  exact AegraphGeneric.gvnGo_ctLeak L gvnPure ρ M c V₁ V₂ h₁ h₂ h

/-- **Leakage of the pass.** Equal leakage of `c` at two valuations gives equal leakage of
    `gvnCom c` there. -/
theorem gvnCom_ctLeak_eq (L : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (gvnCom c) V₁ = Com.ctLeak L (gvnCom c) V₂ :=
  gvnGo_ctLeak L _ _ c V₁ V₂ (sound_empty V₁) (sound_empty V₂)
    (by rw [pullV_id, pullV_id]; exact h)

/-- **Constant time of the pass.** If `c` is constant time for the public-equality
    relation `R`, so is `gvnCom c`. -/
theorem gvnCom_constantTime (L : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (gvnCom c)) :=
  fun V₁ V₂ hR => gvnCom_ctLeak_eq L c V₁ V₂ (h V₁ V₂ hR)

end Leak

end CatCrypt.Crypto.Optimizer.Rewrite.ComGVN
