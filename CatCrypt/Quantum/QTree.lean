/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Instrument
public import CatCrypt.Tactics.LeOfSum

/-!
# QTree: Syntactic Computation Trees for QComp

This file defines `QTree d α`, a syntactic representation of quantum
computations. Unlike `QComp d α` (which is a family of CP linear maps),
`QTree` preserves the sequential structure of instrument applications,
enabling structural cost analysis.

## Main definitions

* `QTree` — syntactic quantum computation tree (ret, op, fail)
* `QTree.compile` — CP map semantics (→ QComp)
* `QTree.queryCost` — instrument count (structural recursion)
* `QTree.bind` — monadic composition (substitution at leaves)

## Main results

* `compile_bind` — compilation commutes with bind
* `queryCost_bind` — cost of bind ≤ cost of tree + bound on continuation

## Sorry status

`compile_bind` depends on QComp monad laws (`qpure_qbind`, `qbind_assoc`,
`qbind_fail`), which have pre-existing sorries in `Instrument.lean`.
No new sorries are introduced by QTree itself.
-/

@[expose] public section

noncomputable section

namespace CatCrypt.Quantum

/-! ## QTree Definition -/

/-- Syntactic computation tree for quantum programs on `d`-dimensional systems. -/
inductive QTree (d : ℕ) : Type → Type 1 where
  | ret {α : Type} : α → QTree d α
  | op {α : Type} (β : Type) (finβ : Fintype β) :
      QComp d β → (β → QTree d α) → QTree d α
  | fail {α : Type} : QTree d α

namespace QTree

variable {d : ℕ} {α β γ : Type}

/-! ## Compilation to QComp -/

/-- Compile a syntax tree to its CP map semantics. -/
def compile : QTree d α → QComp d α
  | .ret a => QComp.qpure a
  | .op β finβ I k => letI := finβ;
    QComp.qbind I (fun b => (k b).compile)
  | .fail => QComp.qfail

/-! ## Query Cost -/

/-- Instrument count on the worst-case execution path. -/
def queryCost : QTree d α → ℕ
  | .ret _ => 0
  | .op β finβ _ k => letI := finβ;
    1 + Finset.univ.sup (fun b => (k b).queryCost)
  | .fail => 0

/-! ## Monadic Bind -/

/-- Monadic bind: substitute `f` at every `ret` leaf. -/
def bind : QTree d α → (α → QTree d β) → QTree d β
  | .ret a, f => f a
  | .op γ finγ I k, f => .op γ finγ I (fun c => (k c).bind f)
  | .fail, _ => .fail

/-! ## Simp Lemmas -/

@[simp] theorem compile_ret (a : α) :
    (QTree.ret a : QTree d α).compile = QComp.qpure a := rfl

@[simp] theorem compile_fail :
    (QTree.fail : QTree d α).compile = QComp.qfail := rfl

@[simp] theorem queryCost_ret (a : α) :
    (QTree.ret a : QTree d α).queryCost = 0 := rfl

@[simp] theorem queryCost_fail :
    (QTree.fail : QTree d α).queryCost = 0 := rfl

@[simp] theorem bind_ret_val (a : α) (f : α → QTree d β) :
    (QTree.ret a).bind f = f a := rfl

@[simp] theorem bind_fail (f : α → QTree d β) :
    (QTree.fail : QTree d α).bind f = .fail := rfl

/-! ## Compile-Bind Correctness -/

/-- Compilation commutes with monadic bind.
    Depends on pre-existing QComp monad law sorries. -/
theorem compile_bind (s : QTree d α) (f : α → QTree d β) :
    (s.bind f).compile = QComp.qbind s.compile (fun a => (f a).compile) := by
  induction s with
  | ret a => exact (QComp.qpure_qbind a (fun a => (f a).compile)).symm
  | op γ finγ I k ih =>
    simp only [bind, compile]; rw [QComp.qbind_assoc]; congr_funext
  | fail =>
    simp only [bind, compile]
    exact (QComp.qfail_qbind (fun a => (f a).compile)).symm

/-! ## Query Cost Bound for Bind -/

/-- Cost of bind ≤ cost of tree + uniform bound on continuation. -/
theorem queryCost_bind (s : QTree d α) (f : α → QTree d β) (bound : ℕ)
    (hf : ∀ a, (f a).queryCost ≤ bound) :
    (s.bind f).queryCost ≤ s.queryCost + bound := by
  induction s with
  | ret a => simp only [bind, queryCost, Nat.zero_add]; exact hf a
  | op γ finγ I k ih =>
    simp only [bind, queryCost]
    have : Finset.univ.sup (fun c => ((k c).bind f).queryCost) ≤
        Finset.univ.sup (fun c => (k c).queryCost) + bound := by
      apply Finset.sup_le; intro c _
      calc ((k c).bind f).queryCost
          ≤ (k c).queryCost + bound := ih c
        _ ≤ Finset.univ.sup (fun c => (k c).queryCost) + bound := by
          gcongr; exact Finset.le_sup (f := fun c => (k c).queryCost) (Finset.mem_univ c)
    omega
  | fail => simp [bind, queryCost]

/-! ## Monad Laws -/

theorem ret_bind (a : α) (f : α → QTree d β) :
    (QTree.ret a).bind f = f a := rfl

theorem bind_ret (s : QTree d α) : s.bind QTree.ret = s := by
  induction s with
  | ret a => simp [bind]
  | op γ finγ I k ih => simp only [bind]; congr_funext
  | fail => rfl

theorem bind_assoc (s : QTree d α) (f : α → QTree d β) (g : β → QTree d γ) :
    (s.bind f).bind g = s.bind (fun a => (f a).bind g) := by
  induction s with
  | ret a => simp [bind]
  | op δ finδ I k ih => simp only [bind]; congr_funext
  | fail => rfl


end QTree

end CatCrypt.Quantum
