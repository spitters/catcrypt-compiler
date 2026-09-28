/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Veir.IR.Basic
public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir

/-!
# Structural facts about the `Com → Veir.WfIRContext` lowering

Shape facts about the lowering of `ComToVeir.lean` that do not depend on Veir's
semantics: the number of operations the builder emits, and lemmas about Veir's
pointer-graph setters. Well-formedness of the built context holds by construction
(`lowerClosedComToModuleWithExterns_wellFormed`); what VeIR's interpreter computes on
it is proved for `jasminDialect` in `ComToVeirWf.lean`.

* `Com.size`, `Com.veirOpCount`: the number of binders of a program and the number of
  operations the lowering emits for it.
* `emitStepsWf_length`, `lowerComWfWith_ops_length_eq_veirOpCount`: when the builder
  succeeds, it emits one operation per expansion step, `com.veirOpCount` in all.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)

variable {d : Dialect.{0, 0}} [DialectSignature d]

/-! ## 1. `Com.size` — a structural measure -/

/-- Number of `Com.var` binders in a program. For a dialect without
    expansions it is the number of operations `lowerComWfWith` emits. -/
def Com.size {Γ : Ctxt d} {t : d.Ty} : Com d Γ t → Nat
  | .ret _ => 0
  | .var _ body => body.size + 1

@[simp] theorem Com.size_ret {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) :
    (Com.ret (d := d) v).size = 0 := rfl

@[simp] theorem Com.size_var {Γ : Ctxt d} {t s : d.Ty}
    (e : Expr d Γ t) (body : Com d (t :: Γ) s) :
    (Com.var e body).size = body.size + 1 := rfl

/-! ## 2. The number of operations the builder emits

The operations returned by `lowerComWfWith veirExpansionOf` number
`Com.veirOpCount`: each binder contributes the number of operations of its
expansion (`ToVeirOp.expand?`), or one. Without expansions this is `Com.size`. -/

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

/-- The expansion `veirExpansionOf o n` has `opVeirCount o` steps. -/
theorem veirExpansionOf_steps_length (o : d.Op) (n : Nat) :
    (veirExpansionOf (d := d) o n).steps.length = opVeirCount (d := d) o := by
  unfold veirExpansionOf opVeirCount
  cases ToVeirOp.expand? (d := d) o <;> rfl

end Count

/-- `emitStepsWf` emits one operation per step. -/
theorem emitStepsWf_length {O : Type} [Veir.HasOpInfo O] (blk : Veir.BlockPtr)
    (args : List Veir.ValuePtr) (resTy : Veir.TypeAttr) :
    ∀ {steps : List (VeirExpandStep O)} {done : List (List Veir.OpResultPtr)}
      {ctx ctx' : Veir.WfIRContext O} {ops : List Veir.OperationPtr}
      {done' : List (List Veir.OpResultPtr)},
    emitStepsWf blk args resTy steps done ctx = some (ctx', ops, done') →
    ops.length = steps.length
  | [], _, _, _, _, _, h => by
    simp only [emitStepsWf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    rfl
  | _ :: _, _, _, _, _, _, h => by
    simp only [emitStepsWf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨ctx₁, o⟩, _, ⟨ctx₂, ops₂, done₂⟩, h₂, hret⟩ := h
    simp only [Prod.mk.injEq] at hret
    obtain ⟨_, rfl, _⟩ := hret
    simp [emitStepsWf_length blk args resTy h₂]

section Lowering

variable [ToVeirOp d]

/-- `lowerComWfWith bx toTy blk vm (.ret v) ctx = some (ctx, [], vm _ v)`: the return
    case neither emits an operation nor changes the context. -/
@[simp] theorem lowerComWfWith_ret {O : Type} [Veir.HasOpInfo O]
    (bx : d.Op → Nat → VeirExpansion O) (toTy : d.Ty → Veir.TypeAttr) (blk : Veir.BlockPtr)
    {Γ : Ctxt d} {t : d.Ty} (vm : VarMap Γ) (v : Var Γ t) (ctx : Veir.WfIRContext O) :
    lowerComWfWith bx toTy blk vm (Com.ret (d := d) v) ctx = some (ctx, [], vm _ v) := rfl

/-- When `lowerComWfWith veirExpansionOf` succeeds, it emits exactly `com.veirOpCount`
    operations. -/
theorem lowerComWfWith_ops_length_eq_veirOpCount (toTy : d.Ty → Veir.TypeAttr)
    (blk : Veir.BlockPtr) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (com : Com d Γ t) {vm : VarMap Γ}
      {ctx ctx' : Veir.WfIRContext (ToVeirOp.Op (d := d))} {ops : List Veir.OperationPtr}
      {final : Veir.ValuePtr},
    lowerComWfWith (veirExpansionOf (d := d)) toTy blk vm com ctx = some (ctx', ops, final) →
    ops.length = com.veirOpCount
  | _, _, .ret _, _, _, _, _, _, h => by
    simp only [lowerComWfWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    rfl
  | _, _, .var e body, _, _, _, _, _, h => by
    simp only [lowerComWfWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ctx₁, ops₁, done⟩, h₁, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨⟨ctx₂, ops₂, final₂⟩, h₂, hret⟩ := h
      simp only [Prod.mk.injEq] at hret
      obtain ⟨_, rfl, _⟩ := hret
      rw [List.length_append, emitStepsWf_length _ _ _ h₁, veirExpansionOf_steps_length,
        lowerComWfWith_ops_length_eq_veirOpCount toTy blk body h₂]
      rfl
    · simp at h

/-- Without expansions, when `lowerComWfWith veirExpansionOf` succeeds, it emits
    exactly `com.size` operations. -/
theorem lowerComWfWith_ops_length_eq_size
    (hNo : ∀ o : d.Op, ToVeirOp.expand? (d := d) o = none) (toTy : d.Ty → Veir.TypeAttr)
    (blk : Veir.BlockPtr) {Γ : Ctxt d} {t : d.Ty} (com : Com d Γ t) {vm : VarMap Γ}
    {ctx ctx' : Veir.WfIRContext (ToVeirOp.Op (d := d))} {ops : List Veir.OperationPtr}
    {final : Veir.ValuePtr}
    (h : lowerComWfWith (veirExpansionOf (d := d)) toTy blk vm com ctx =
      some (ctx', ops, final)) :
    ops.length = com.size := by
  rw [lowerComWfWith_ops_length_eq_veirOpCount toTy blk com h, Com.veirOpCount_eq_size hNo]

/-- A program whose lowering counts at least one operation emits a non-empty
    operation list when the builder succeeds. -/
theorem lowerComWfWith_ops_nonempty_of_veirOpCount_pos (toTy : d.Ty → Veir.TypeAttr)
    (blk : Veir.BlockPtr) {Γ : Ctxt d} {t : d.Ty} (com : Com d Γ t) {vm : VarMap Γ}
    {ctx ctx' : Veir.WfIRContext (ToVeirOp.Op (d := d))} {ops : List Veir.OperationPtr}
    {final : Veir.ValuePtr}
    (h : lowerComWfWith (veirExpansionOf (d := d)) toTy blk vm com ctx =
      some (ctx', ops, final)) :
    com.veirOpCount > 0 → ops ≠ [] := by
  intro hpos hempty
  have hlen := lowerComWfWith_ops_length_eq_veirOpCount toTy blk com h
  rw [hempty] at hlen
  simp at hlen
  omega

/-- Without expansions, a program with a binder emits a non-empty operation list when
    the builder succeeds. -/
theorem lowerComWfWith_ops_nonempty_of_size_pos
    (hNo : ∀ o : d.Op, ToVeirOp.expand? (d := d) o = none) (toTy : d.Ty → Veir.TypeAttr)
    (blk : Veir.BlockPtr) {Γ : Ctxt d} {t : d.Ty} (com : Com d Γ t) {vm : VarMap Γ}
    {ctx ctx' : Veir.WfIRContext (ToVeirOp.Op (d := d))} {ops : List Veir.OperationPtr}
    {final : Veir.ValuePtr}
    (h : lowerComWfWith (veirExpansionOf (d := d)) toTy blk vm com ctx =
      some (ctx', ops, final)) :
    com.size > 0 → ops ≠ [] := by
  rw [← Com.veirOpCount_eq_size hNo]
  exact lowerComWfWith_ops_nonempty_of_veirOpCount_pos toTy blk com h

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

/-! ## 4. Veir's operation setters

`OperationPtr.get!` after `setNextOp!`, `setPrevOp!` and `setParent!`, on the same
pointer or a different one. -/

section Setters

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

end Setters

end CatCrypt.Crypto.SecureCompilation.VIR
