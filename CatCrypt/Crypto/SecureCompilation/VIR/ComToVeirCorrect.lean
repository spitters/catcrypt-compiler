/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Veir.IR.Basic
public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir

/-!
# Structural correctness of `Com → Veir.IRContext` lowering

Scaffold for the correctness story of `ComToVeir.lean`. The goal of
this file is to accumulate structural lemmas about the lowering that
do *not* depend on Veir's pointer-graph semantics: shape facts about
the emitted op list, length / parent / chain invariants, and (later)
preservation of `Com.denote` under interpretation.

Stage 1 (this file): purely arithmetic / list-shape facts. Each
theorem here is `True := trivial`-free and has no open goals and uses no `axiom`.

Out of scope (future files):

* Pointer-graph well-formedness: every emitted op's prev/next/parent
  satisfies the Veir `InBounds` predicates after `lowerComToBlockRegion`
  completes.
* Semantic preservation: an interpretation of the lowered Veir
  `IRContext` that agrees with `Com.denote` under `ToVeirOp`'s op
  semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)

variable {d : Dialect.{0, 0}} [DialectSignature d]

/-! ## 1. `Com.size` — a structural measure -/

/-- Number of `Com.var` binders in a program. For a dialect without
    expansions it is the length of `lowerCom`'s emitted op-list. -/
def Com.size {Γ : Ctxt d} {t : d.Ty} : Com d Γ t → Nat
  | .ret _ => 0
  | .var _ body => body.size + 1

@[simp] theorem Com.size_ret {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) :
    (Com.ret (d := d) v).size = 0 := rfl

@[simp] theorem Com.size_var {Γ : Ctxt d} {t s : d.Ty}
    (e : Expr d Γ t) (body : Com d (t :: Γ) s) :
    (Com.var e body).size = body.size + 1 := rfl

/-! ## 2. `lowerCom` op-list length

The list of `OperationPtr`s returned by `lowerCom` has length
`Com.veirOpCount`: each binder contributes the number of operations of its
expansion (`ToVeirOp.expand?`), or one. Without expansions this is `Com.size`.
This is the structural fact used by `lowerComToBlockRegion`'s chain-wiring. -/

section Count

variable [ToVeirOp d]

/-- The number of operations the lowering emits for the op `o`: the length of its
    expansion, or one. -/
def opVeirCount (o : d.Op) : Nat :=
  match ToVeirOp.expand? (d := d) o with
  | some x => x.steps.length
  | none => 1

/-- The number of operations the lowering emits for a program. -/
def Com.veirOpCount {Γ : Ctxt d} {t : d.Ty} : Com d Γ t → Nat
  | .ret _ => 0
  | .var e body => opVeirCount (d := d) e.op + body.veirOpCount

/-- Without expansions, the lowering emits one operation per binder. -/
theorem Com.veirOpCount_eq_size
    (hNo : ∀ o : d.Op, ToVeirOp.expand? (d := d) o = none) {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t) : com.veirOpCount = com.size := by
  induction com with
  | ret v => rfl
  | var e body ih =>
      simp only [Com.veirOpCount, Com.size, opVeirCount, hNo, ih]
      omega

end Count

section Lowering

variable [ToVeirOp d] [ToVeirTy d]

/-! ### Equational forms of `lowerCom`

These are direct definitional rewrites — useful as `simp` lemmas
when reasoning about `lowerCom`'s state-monadic shape without
unfolding it by hand each time. -/

/-- `lowerCom vm (.ret v) ctx = ((vm _ v, []), ctx)` — the return
    case neither emits an op nor mutates context. -/
@[simp] theorem lowerCom_ret {Γ : Ctxt d} {t : d.Ty}
    (vm : VarMap Γ) (v : Var Γ t)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    (lowerCom vm (Com.ret (d := d) v)).run ctx = ((vm _ v, []), ctx) := by
  simp [lowerCom, StateT.run, pure, StateT.pure]

/-- `lowerCom vm (.var e body) ctx` destructures into a `lowerExpr`
    step followed by `lowerCom` on the body in the VarMap extended by the
    binding's value, with the operations of `lowerExpr` prepended to the
    resulting list. -/
theorem lowerCom_var {Γ : Ctxt d} {t s : d.Ty}
    (vm : VarMap Γ) (e : Expr d Γ t) (body : Com d (t :: Γ) s)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    (lowerCom vm (Com.var e body)).run ctx =
      let ((ops, val), s1) := (lowerExpr vm e).run ctx
      let ((final, rest), s2) := (lowerCom (vm.extend val) body).run s1
      ((final, ops ++ rest), s2) := rfl

/-! ### Structural facts about the emitted op list -/

omit [ToVeirTy d] in
/-- `runSteps` emits one operation per step. -/
theorem runSteps_length (args : List Veir.ValuePtr) (resTy : Veir.TypeAttr) :
    (steps : List (VeirExpandStep (ToVeirOp.Op (d := d)))) →
    (done : List (List Veir.OpResultPtr)) → (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) →
    ((runSteps (d := d) args resTy steps done).run ctx).1.1.length = steps.length
  | [], _, _ => rfl
  | s :: rest, done, ctx => by
      simp only [runSteps, StateT.run, bind, StateT.bind, pure, StateT.pure]
      generalize emitStep (d := d) args resTy done s ctx = r1
      rcases r1 with ⟨⟨op, rs⟩, s1⟩
      have ih := runSteps_length args resTy rest (done ++ [rs]) s1
      simp only [StateT.run] at ih
      dsimp only
      generalize runSteps (d := d) args resTy rest (done ++ [rs]) s1 = r2 at ih ⊢
      rcases r2 with ⟨⟨ops, done'⟩, s2⟩
      simp only [List.length_cons] at ih ⊢
      omega

/-- `lowerExpr e` emits `opVeirCount e.op` operations: the steps of the op's
    expansion, or one. -/
theorem lowerExpr_ops_length {Γ : Ctxt d} {t : d.Ty} (vm : VarMap Γ) (e : Expr d Γ t)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    ((lowerExpr vm e).run ctx).1.1.length = opVeirCount (d := d) e.op := by
  unfold lowerExpr opVeirCount
  cases hx : ToVeirOp.expand? (d := d) e.op with
  | some x =>
    simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
    have h := runSteps_length (d := d) (argPtrs vm e.args) (ToVeirTy.toTy (d := d) t)
      x.steps [] ctx
    simp only [StateT.run] at h
    generalize runSteps (d := d) (argPtrs vm e.args) (ToVeirTy.toTy (d := d) t) x.steps [] ctx
      = r at h ⊢
    rcases r with ⟨⟨ops, done⟩, s1⟩
    dsimp only at h ⊢
    exact h
  | none =>
    simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
    generalize lowerExprSingle vm e ctx = r
    rcases r with ⟨⟨op, res⟩, s1⟩
    rfl

/-- When the op of `e` has the expansion `x`, the binding denotes the operand
    `x.value`, resolved against the results of the expansion's operations. -/
theorem lowerExpr_value_of_expand {Γ : Ctxt d} {t : d.Ty} (vm : VarMap Γ) (e : Expr d Γ t)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (x : VeirExpansion (ToVeirOp.Op (d := d)))
    (hx : ToVeirOp.expand? (d := d) e.op = some x) :
    ((lowerExpr vm e).run ctx).1.2 =
      x.value.resolve (argPtrs vm e.args)
        ((runSteps (d := d) (argPtrs vm e.args) (ToVeirTy.toTy (d := d) t) x.steps []).run
          ctx).1.2 := by
  unfold lowerExpr
  rw [hx]
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
  generalize runSteps (d := d) (argPtrs vm e.args) (ToVeirTy.toTy (d := d) t) x.steps [] ctx
    = r
  rcases r with ⟨⟨ops, done⟩, s1⟩
  rfl

/-- `lowerCom` emits exactly `com.veirOpCount` operation pointers. -/
theorem lowerCom_ops_length_eq_veirOpCount {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t) (vm : VarMap Γ)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    ((lowerCom vm com).run ctx).1.2.length = com.veirOpCount := by
  induction com generalizing ctx with
  | ret v =>
      simp [lowerCom, Com.veirOpCount, StateT.run, pure, StateT.pure]
  | var e body ih =>
      simp only [lowerCom, Com.veirOpCount, StateT.run, bind, StateT.bind,
                 pure, StateT.pure]
      have hE := lowerExpr_ops_length vm e ctx
      simp only [StateT.run] at hE
      generalize lowerExpr vm e ctx = exprRes at hE ⊢
      rcases exprRes with ⟨⟨ops, val⟩, s1⟩
      have := ih (vm := vm.extend val) (ctx := s1)
      simp only [StateT.run] at this
      dsimp only
      generalize lowerCom (vm.extend val) body s1 = bodyRes at this ⊢
      rcases bodyRes with ⟨⟨final, rest⟩, s2⟩
      simp only [List.length_append] at this hE ⊢
      omega

/-- Without expansions, `lowerCom` emits exactly `com.size` operation pointers. -/
theorem lowerCom_ops_length_eq_size
    (hNo : ∀ o : d.Op, ToVeirOp.expand? (d := d) o = none) {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t) (vm : VarMap Γ)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    ((lowerCom vm com).run ctx).1.2.length = com.size := by
  rw [lowerCom_ops_length_eq_veirOpCount, Com.veirOpCount_eq_size hNo]

/-- On a `Com.var e body` whose binding emits an operation, the *first* op in
    the emitted list is the first one emitted by `lowerExpr e`. Useful for
    `block.firstOp` / chain-head reasoning downstream. -/
theorem lowerCom_var_head_op {Γ : Ctxt d} {t s : d.Ty}
    (vm : VarMap Γ) (e : Expr d Γ t) (body : Com d (t :: Γ) s)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (h : ((lowerExpr vm e).run ctx).1.1 ≠ []) :
    ((lowerCom vm (Com.var e body)).run ctx).1.2.head? =
      ((lowerExpr vm e).run ctx).1.1.head? := by
  rw [lowerCom_var]
  revert h
  generalize (lowerExpr vm e).run ctx = exprRes
  rcases exprRes with ⟨⟨ops, val⟩, s1⟩
  intro h
  dsimp only
  generalize (lowerCom (vm.extend val) body).run s1 = bodyRes
  rcases bodyRes with ⟨⟨final, rest⟩, s2⟩
  cases ops with
  | nil => exact absurd rfl h
  | cons o os => rfl

/-- A program whose lowering counts at least one operation emits a non-empty
    op list. -/
theorem lowerCom_ops_nonempty_of_veirOpCount_pos {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t) (vm : VarMap Γ)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    com.veirOpCount > 0 → ((lowerCom vm com).run ctx).1.2 ≠ [] := by
  intro hpos hempty
  have hlen := lowerCom_ops_length_eq_veirOpCount com vm ctx
  rw [hempty] at hlen
  simp at hlen
  omega

/-- Without expansions, a program with a binder emits a non-empty op list. -/
theorem lowerCom_ops_nonempty_of_size_pos
    (hNo : ∀ o : d.Op, ToVeirOp.expand? (d := d) o = none) {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t) (vm : VarMap Γ)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    com.size > 0 → ((lowerCom vm com).run ctx).1.2 ≠ [] := by
  rw [← Com.veirOpCount_eq_size hNo]
  exact lowerCom_ops_nonempty_of_veirOpCount_pos com vm ctx

/-! ### Structural facts about `chainOpsInBlock`

`chainOpsInBlock blk ops` walks a list of operation pointers and
threads `prev`/`next`/`parent` mutations through the `IRContext`.
Below are its definitional shapes; deeper Veir-side invariants
(e.g. `(after-chain)[op_i].next = some op_{i+1}`) require lemmas
about Veir's `HashMap.get!_insert` interaction and live in a
follow-up file. -/

omit [ToVeirTy d] in
/-- `chainOpsInBlock` on the empty list is a no-op. -/
@[simp] theorem chainOpsInBlock_nil
    (blk : Veir.BlockPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    (chainOpsInBlock (d := d) blk []).run ctx = ((), ctx) := rfl

omit [ToVeirTy d] in
/-- `chainOpsInBlock` on a singleton sets only the parent pointer. -/
theorem chainOpsInBlock_singleton
    (blk : Veir.BlockPtr) (op : Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    (chainOpsInBlock (d := d) blk [op]).run ctx =
      ((), op.setParent! ctx (some blk)) := rfl

omit [ToVeirTy d] in
/-- On two-or-more, `chainOpsInBlock` first sets the head op's `next`
    pointer to the second op, then the second op's `prev` pointer to
    the head, then the head's parent, then recurses on the tail. -/
theorem chainOpsInBlock_cons_cons
    (blk : Veir.BlockPtr) (op op' : Veir.OperationPtr)
    (rest : List Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d))) :
    (chainOpsInBlock (d := d) blk (op :: op' :: rest)).run ctx =
      let ctx1 := op.setNextOp! ctx (some op')
      let ctx2 := op'.setPrevOp! ctx1 (some op)
      let ctx3 := op.setParent! ctx2 (some blk)
      (chainOpsInBlock blk (op' :: rest)).run ctx3 := rfl

end Lowering

/-! ## 3. Lawful instances for `Veir.OperationPtr`

`Std.HashMap.getElem!_insert` requires `LawfulHashable` and `EquivBEq`.
`Veir.OperationPtr := { id : Nat }` derives `DecidableEq` (and hence
`BEq`) and has a manual `Hashable` instance forwarding to `Nat`'s.
Both lawful instances follow by reducing to the `Nat` ones. -/

instance : LawfulBEq Veir.OperationPtr where
  eq_of_beq {a b} h := by
    rcases a with ⟨ai⟩
    rcases b with ⟨bi⟩
    simp only [BEq.beq, decide_eq_true_eq] at h
    exact h
  rfl {a} := by
    rcases a with ⟨ai⟩
    simp [BEq.beq]

-- `LawfulHashable` is derived from `LawfulBEq` via
-- `instLawfulHashableOfLawfulBEq` — no explicit instance needed.

/-! ## 4. Chain semantic invariant

The two-op case of `chainOpsInBlock` — first real semantic invariant
about Veir state: after running `chainOpsInBlock blk [op1, op2]`,
looking up `op1` in the resulting `IRContext` yields an operation
whose `next` field is `some op2`. Larger lists follow by induction
(future work). -/

section ChainInvariant

variable [ToVeirOp d]

/-- `OperationPtr.get!` after `setNextOp!` on the SAME pointer
    yields the updated operation. Direct unfolding + HashMap. -/
theorem get!_setNextOp!_self
    (op : Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (new : Option Veir.OperationPtr) :
    op.get! (op.setNextOp! ctx new) =
      { op.get! ctx with next := new } := by
  simp [Veir.OperationPtr.setNextOp!, Veir.OperationPtr.set,
        Veir.OperationPtr.get!]

/-- `OperationPtr.get!` after `setNextOp!` on a DIFFERENT pointer
    is unchanged. -/
theorem get!_setNextOp!_other
    (op op' : Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (new : Option Veir.OperationPtr) (h : op ≠ op') :
    op.get! (op'.setNextOp! ctx new) = op.get! ctx := by
  simp [Veir.OperationPtr.setNextOp!, Veir.OperationPtr.set,
        Veir.OperationPtr.get!,
        Std.HashMap.getElem!_insert,
        show ¬ (op' = op) from fun he => h he.symm]

/-- Same for `setPrevOp!` on a different pointer. -/
theorem get!_setPrevOp!_other
    (op op' : Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (new : Option Veir.OperationPtr) (h : op ≠ op') :
    op.get! (op'.setPrevOp! ctx new) = op.get! ctx := by
  simp [Veir.OperationPtr.setPrevOp!, Veir.OperationPtr.set,
        Veir.OperationPtr.get!,
        Std.HashMap.getElem!_insert,
        show ¬ (op' = op) from fun he => h he.symm]

/-- `setParent!` on the same pointer preserves `next`. -/
theorem next_get!_setParent!_self
    (op : Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (new : Option Veir.BlockPtr) :
    (op.get! (op.setParent! ctx new)).next = (op.get! ctx).next := by
  simp [Veir.OperationPtr.setParent!, Veir.OperationPtr.set,
        Veir.OperationPtr.get!]

/-- `setParent!` on a different pointer is fully transparent. -/
theorem get!_setParent!_other
    (op op' : Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (new : Option Veir.BlockPtr) (h : op ≠ op') :
    op.get! (op'.setParent! ctx new) = op.get! ctx := by
  simp [Veir.OperationPtr.setParent!, Veir.OperationPtr.set,
        Veir.OperationPtr.get!,
        Std.HashMap.getElem!_insert,
        show ¬ (op' = op) from fun he => h he.symm]

/-- **Chain semantic invariant (two-op case).** After running
    `chainOpsInBlock blk [op1, op2]`, the operation at `op1` has its
    `next` field set to `some op2`. -/
theorem chainOpsInBlock_pair_next
    (blk : Veir.BlockPtr) (op1 op2 : Veir.OperationPtr)
    (ctx : Veir.IRContext (ToVeirOp.Op (d := d)))
    (hne : op1 ≠ op2) :
    (op1.get! (((chainOpsInBlock (d := d) blk [op1, op2]).run ctx).2)).next =
      some op2 := by
  -- Reduce chainOpsInBlock to the four `modify` ops.
  rw [chainOpsInBlock_cons_cons, chainOpsInBlock_singleton]
  -- Walk get! across the four sets in order:
  --   setNextOp! op1  (sets op1.next := some op2)
  --   setPrevOp! op2  (different key — preserved)
  --   setParent! op1  (same key, but only changes parent)
  --   setParent! op2  (different key — preserved)
  simp only []
  rw [get!_setParent!_other op1 op2 _ _ hne]
  rw [next_get!_setParent!_self op1]
  rw [get!_setPrevOp!_other op1 op2 _ _ hne]
  rw [get!_setNextOp!_self]

end ChainInvariant

end CatCrypt.Crypto.SecureCompilation.VIR
