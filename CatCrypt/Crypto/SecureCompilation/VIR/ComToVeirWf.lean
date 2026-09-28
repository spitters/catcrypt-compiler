/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeirSemantics
public import Veir.Rewriter.WfRewriter
public import Veir.Interpreter.Lemmas
import all Veir.Interpreter.Basic
import all Veir.Data.LLVM.Int.Basic
import all Veir.IR.Attribute
import all Veir.RuntimeValue.Conforms
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic
import all Veir.IR.Basic
import all Veir.Rewriter.LinkedList.Basic
import all Veir.IR.WellFormed
import all Veir.Rewriter.InsertPoint
import all Veir.Interfaces.FunctionInterfaces

/-!
# Well-formed `Com → Veir` lowering of `jasminDialect`, run by `interpretBlock`

A lowering of `Com jasminDialect Γ t` into a VeIR block built through VeIR's
well-formedness-preserving builder `WfRewriter`, so that the result is a
`WfIRContext` and VeIR's own block interpreter `interpretBlock` applies to it.

The operations are those of `lowerExpr` for the `ToVeirOp jasminDialect`
instance: per binding, the steps of `JasminOp.expandVeir?` or the one operation
with op-code `toMlirOpCode o`, properties `propsOfOp o`, one operand per argument
and `max n 1` results of the binding's type (`bindingExpansion`). They are
appended to one block whose arguments are the context `Γ` (argument `i` is the
variable of De Bruijn depth `i`, as in `varMapOfBlockArgs`), followed by a
`func.return` of the program's value. Discardable attributes are not set; the
interpreter does not read them.

* `lowerComWf_spec`, `emitStepsWf_spec`: the built context holds the block's
  operations as a chain (`Chain`) and each operation has the op-code, properties,
  result types and operands of its step (`StepsIn`, `ComIn`), owning no value that
  is live when it is created.
* `steps_sim`, `com_sim`: `interpretOpList` on those operations follows
  `veirRunStepsC`, the op-by-op run by `Veir.interpretOp'` in which every step's
  results conform to its result types.
* `interpretBlock_lowerComToBlockWf`: on the `arith` fragment over a context of
  integer types, `interpretBlock` on the built block, with the arguments set to the
  encoded valuation, returns the encoded denotation through the `func.return`;
  `interpretBlock_lowerComToBlockWf_eq_veirRunCom` states it as agreement with
  `veirRunCom`.

* `lowerComToBlockWf_isSome`: the builder returns a context for every program.
  Each `createAtEnd` allocates the operation `⟨nextID⟩`, which is fresh because
  every operation in bounds has a smaller identifier (`OpsBelow`), and every operand
  of every expansion step is an argument or a result of an earlier step
  (`bindingExpansion_inScope`). `exists_interpretBlock_lowerComToBlockWf` and
  `exists_interpretBlock_lowerComToBlockWf_eq_veirRunCom` state the two
  `interpretBlock` theorems without the hypothesis that the builder succeeds.

* `lowerComToFuncWf`: the same block as the body of a `func.func` inside a
  `builtin.module`, all built through `WfRewriter` (`createRegionOp`, `createBlockIn`).
  `interpretFunction_lowerComToFuncWf` and `_eq_veirRunCom`: on the `arith` fragment,
  VeIR's function-level interpreter `interpretFunction` on that `func.func` returns the
  encoded denotation, equal to what `veirRunCom` computes, and leaves the memory
  unchanged. `lowerComToFuncWf_isSome` (every allocation is fresh because every
  operation, block and region has an identifier below `nextID`, `IdsBelow`) gives
  `exists_interpretFunction_lowerComToFuncWf` and its `_eq_veirRunCom` form without the
  hypothesis that the builder succeeds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

open Veir Veir.Data
open CatCrypt.Crypto.SecureCompilation.VIR (Com Expr Ctxt TyDenote DialectSignature VarMap
  VeirSrc VeirExpandStep VeirExpansion argPtrs varMapOfBlockArgs)
open Ctxt (Var Valuation)

/-! ## The builder -/

/-- Create an operation with op-code `op`, properties `props`, result types `resTys`
and operands `operands` at the end of the block `blk`, through
`WfRewriter.createOp`; `none` when an operand or the block is not in bounds. -/
def createAtEnd (ctx : WfIRContext OpCode) (blk : BlockPtr) (op : OpCode)
    (props : propertiesOf op) (resTys : Array TypeAttr) (operands : Array ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  if hoper : ∀ v ∈ operands, v.InBounds ctx.raw then
    if hblk : blk.InBounds ctx.raw then
      WfRewriter.createOp ctx op resTys operands #[] #[] props (some (.atEnd blk)) hoper
        (by simp) (by simp) (by simpa [Option.maybe_some] using hblk)
    else none
  else none

/-- The operations the lowering emits for a binding with op `o` and `nargs`
arguments: the expansion `JasminOp.expandVeir? o`, or the one operation of
`lowerExprSingle` (op-code `toMlirOpCode o`, properties `propsOfOp o`, the
arguments as operands, `max n 1` results of the binding's type) whose value is the
result in the slot `resultSlotOfOp o` names. -/
def bindingExpansion (o : JasminOp) (nargs : Nat) : VeirExpansion OpCode :=
  match JasminOp.expandVeir? o with
  | some x => x
  | none =>
      { steps := [{ op := JasminOp.toMlirOpCode o, props := JasminOp.propsOfOp o,
                    operands := (List.range nargs).map VeirSrc.arg,
                    results := List.replicate (max (JasminOp.resultSlotOfOp o).1 1) none }],
        value := .res 0 (JasminOp.resultSlotOfOp o).2 }

/-- The result types of the step `s`, with `none` read as `resTy`. -/
def stepResTys (resTy : TypeAttr) (s : VeirExpandStep OpCode) : Array TypeAttr :=
  (s.results.map (·.getD resTy)).toArray

/-- The result pointers of `op` with indices below `n`. -/
def resultPtrs (op : OperationPtr) (n : Nat) : List OpResultPtr :=
  (List.range n).map op.getResult

/-- Emit the steps of an expansion at the end of `blk`, in order, each reading its
operands through `VeirSrc.resolve`; returns the context, the operations and the
results of every operation emitted so far. -/
def emitStepsWf (blk : BlockPtr) (args : List ValuePtr) (resTy : TypeAttr) :
    List (VeirExpandStep OpCode) → List (List OpResultPtr) → WfIRContext OpCode →
    Option (WfIRContext OpCode × List OperationPtr × List (List OpResultPtr))
  | [], done, ctx => some (ctx, [], done)
  | s :: rest, done, ctx => do
      let (ctx', op) ← createAtEnd ctx blk s.op s.props (stepResTys resTy s)
        (s.operands.map (VeirSrc.resolve args done)).toArray
      let (ctx'', ops, done') ←
        emitStepsWf blk args resTy rest (done ++ [resultPtrs op (stepResTys resTy s).size]) ctx'
      pure (ctx'', op :: ops, done')

/-- Lower a `Com` at the end of `blk`: each binding emits the steps of its
`bindingExpansion` and binds the value of the expansion, which must be in bounds.
Returns the context, the operations in order, and the value of the program. -/
def lowerComWf (blk : BlockPtr) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    VarMap Γ → Com jasminDialect Γ t → WfIRContext OpCode →
    Option (WfIRContext OpCode × List OperationPtr × ValuePtr)
  | _, _, vm, .ret v, ctx => some (ctx, [], vm _ v)
  | _, _, vm, .var (t := tEx) e body, ctx => do
      let args := argPtrs vm e.args
      let x := bindingExpansion e.op args.length
      let (ctx1, ops1, done) ← emitStepsWf blk args (JasminTy.toVeirTy tEx) x.steps [] ctx
      let val := x.value.resolve args done
      if val.InBounds ctx1.raw then
        let (ctx2, ops2, final) ← lowerComWf blk (vm.extend (t := tEx) val) body ctx1
        pure (ctx2, ops1 ++ ops2, final)
      else none

/-- Lower a `Com jasminDialect Γ t` into a fresh well-formed context: a block with
one argument per entry of `Γ` (types `toVeirTy`), the operations of `lowerComWf`
and a final `func.return` of the program's value. Returns the context, the block
and its operations in order. -/
def lowerComToBlockWf {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Option (WfIRContext OpCode × BlockPtr × List OperationPtr) := do
  let (ctx1, blk) ← WfRewriter.createBlock (default : WfIRContext OpCode)
    (Γ.map JasminTy.toVeirTy).toArray none (by simp [Option.maybe_none])
  let (ctx2, ops, final) ← lowerComWf blk (varMapOfBlockArgs blk) c ctx1
  let (ctx3, ret) ← createAtEnd ctx2 blk (.func .return) default #[] #[final]
  pure (ctx3, blk, ops ++ [ret])

/-! ## Facts about one `createAtEnd` -/

section CreateAtEnd

variable {ctx ctx' : WfIRContext OpCode} {blk : BlockPtr} {oc : OpCode} {p : propertiesOf oc}
  {rt : Array TypeAttr} {xs : Array ValuePtr} {op' : OperationPtr}

theorem createAtEnd_spec (h : createAtEnd ctx blk oc p rt xs = some (ctx', op')) :
    blk.InBounds ctx.raw ∧ ∃ h₁ h₂ h₃ h₄,
      WfRewriter.createOp ctx oc rt xs #[] #[] p (some (.atEnd blk)) h₁ h₂ h₃ h₄ =
        some (ctx', op') := by
  unfold createAtEnd at h
  split at h
  · split at h
    · exact ⟨by assumption, _, _, _, _, h⟩
    · simp at h
  · simp at h

theorem createAtEnd_new_not_inBounds (h : createAtEnd ctx blk oc p rt xs = some (ctx', op')) :
    ¬ op'.InBounds ctx.raw := by
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  exact WfRewriter.createOp_new_not_inBounds _ h

theorem createAtEnd_new_inBounds (h : createAtEnd ctx blk oc p rt xs = some (ctx', op')) :
    op'.InBounds ctx'.raw := by
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  exact WfRewriter.createOp_new_inBounds _ h

theorem createAtEnd_operands_inBounds (h : createAtEnd ctx blk oc p rt xs = some (ctx', op')) :
    ∀ v ∈ xs, v.InBounds ctx.raw := by
  obtain ⟨_, h₁, _, _, _, _⟩ := createAtEnd_spec h
  exact h₁

theorem createAtEnd_op_inBounds_mono (h : createAtEnd ctx blk oc p rt xs = some (ctx', op'))
    {o : OperationPtr} (ho : o.InBounds ctx.raw) : o.InBounds ctx'.raw := by
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  grind

theorem createAtEnd_value_inBounds_mono (h : createAtEnd ctx blk oc p rt xs = some (ctx', op'))
    {v : ValuePtr} (hv : v.InBounds ctx.raw) : v.InBounds ctx'.raw := by
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  grind

theorem createAtEnd_block_inBounds_mono (h : createAtEnd ctx blk oc p rt xs = some (ctx', op'))
    {b : BlockPtr} (hb : b.InBounds ctx.raw) : b.InBounds ctx'.raw := by
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  grind

/-- The operation `o` is in bounds in `ctx` with op-code `oc`, properties `p`, result
types `rt`, operands `xs` and no successors. -/
structure OpIs (ctx : WfIRContext OpCode) (o : OperationPtr) (oc : OpCode) (p : propertiesOf oc)
    (rt : Array TypeAttr) (xs : Array ValuePtr) : Prop where
  inBounds : o.InBounds ctx.raw
  opType : o.getOpType! ctx.raw = oc
  props : o.getProperties! ctx.raw oc = p
  resTys : o.getResultTypes! ctx.raw = rt
  operands : o.getOperands! ctx.raw = xs
  succs : o.getSuccessors! ctx.raw = #[]

theorem createAtEnd_opIs_new (h : createAtEnd ctx blk oc p rt xs = some (ctx', op')) :
    OpIs ctx' op' oc p rt xs := by
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  refine ⟨WfRewriter.createOp_new_inBounds _ h, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OperationPtr.getOpType!_WfRewriter_createOp h]; simp [ofDialect_hasDialectRefl]
  · rw [OperationPtr.getProperties!_WfRewriter_createOp h]; simp
  · rw [OperationPtr.getResultTypes!_WfRewriter_createOp h]; simp
  · rw [OperationPtr.getOperands!_WfRewriter_createOp h]; simp
  · rw [OperationPtr.getSuccessors!_WfRewriter_createOp h]; simp

theorem OpIs.createAtEnd {o : OperationPtr} {oc₀ : OpCode} {p₀ : propertiesOf oc₀}
    {rt₀ : Array TypeAttr} {xs₀ : Array ValuePtr} (ho : OpIs ctx o oc₀ p₀ rt₀ xs₀)
    (h : createAtEnd ctx blk oc p rt xs = some (ctx', op')) :
    OpIs ctx' o oc₀ p₀ rt₀ xs₀ := by
  have hne : o ≠ op' := fun he => createAtEnd_new_not_inBounds h (he ▸ ho.inBounds)
  have hin := createAtEnd_op_inBounds_mono h ho.inBounds
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  refine ⟨hin, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_neg hne, ho.opType]
  · rw [OperationPtr.getProperties!_WfRewriter_createOp h, if_neg hne, ho.props]
  · rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_neg hne, ho.resTys]
  · rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_neg hne, ho.operands]
  · rw [OperationPtr.getSuccessors!_WfRewriter_createOp h, if_neg hne, ho.succs]

/-- The block `blk` of `ctx` holds exactly the operations `L`, in order: its first and
last operations are the head and the last element of `L`, and the successor of each
element is the next element. -/
structure Chain (ctx : WfIRContext OpCode) (blk : BlockPtr) (L : List OperationPtr) : Prop where
  blkIn : blk.InBounds ctx.raw
  first : (blk.get! ctx.raw).firstOp = L.head?
  last : (blk.get! ctx.raw).lastOp = L.getLast?
  next : ∀ (i : Nat) (h : i < L.length), (L[i].get! ctx.raw).next = L[i + 1]?
  inBounds : ∀ o ∈ L, o.InBounds ctx.raw
  nodup : L.Nodup

theorem Chain.createAtEnd {L : List OperationPtr} (hc : Chain ctx blk L)
    (h : createAtEnd ctx blk oc p rt xs = some (ctx', op')) : Chain ctx' blk (L ++ [op']) := by
  have hnew := createAtEnd_new_not_inBounds h
  have hnewIn := createAtEnd_new_inBounds h
  have hblk := createAtEnd_block_inBounds_mono h hc.blkIn
  have hmono : ∀ o ∈ L, o.InBounds ctx'.raw := fun o ho =>
    createAtEnd_op_inBounds_mono h (hc.inBounds o ho)
  have hnotin : op' ∉ L := fun hm => hnew (hc.inBounds _ hm)
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  refine ⟨hblk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BlockPtr.firstOp!_WfRewriter_createOp h]
    simp only [InsertPoint.block!_atEnd_eq, InsertPoint.prev_atEnd_eq, hc.last, hc.first]
    cases L <;> simp
  · rw [BlockPtr.lastOp!_WfRewriter_createOp h]
    simp [InsertPoint.block!_atEnd_eq, InsertPoint.next_atEnd_eq]
  · intro i hi
    rw [OperationPtr.next!_WfRewriter_createOp h]
    simp only [InsertPoint.next_atEnd_eq, InsertPoint.prev_atEnd_eq, hc.last]
    have hlen : i < L.length ∨ i = L.length := by simp at hi; omega
    rcases hlen with hlt | rfl
    · rw [List.getElem_append_left hlt]
      have hne : L[i] ≠ op' := fun e => hnotin (e ▸ List.getElem_mem hlt)
      rw [if_neg hne]
      by_cases hl : i + 1 = L.length
      · have hlast : some L[i] = L.getLast? := by
          rw [List.getLast?_eq_getElem?]; simp [← hl]
        rw [if_pos hlast, List.getElem?_append_right (by omega)]
        simp [hl]
      · have hne2 : some L[i] ≠ L.getLast? := by
          rw [List.getLast?_eq_getElem?]
          intro e
          have hlt' : L.length - 1 < L.length := by omega
          rw [List.getElem?_eq_getElem hlt'] at e
          exact absurd (List.getElem_inj hc.nodup |>.1 (Option.some.inj e)) (by omega)
        rw [if_neg hne2, hc.next i hlt, List.getElem?_append_left (by omega)]
    · simp
  · intro o ho
    simp only [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hmono o ho
    · exact hnewIn
  · rw [List.nodup_append]
    refine ⟨hc.nodup, by simp, ?_⟩
    simp only [List.mem_singleton]
    rintro a ha b rfl rfl
    exact hnotin ha

theorem createAtEnd_result_inBounds (h : createAtEnd ctx blk oc p rt xs = some (ctx', op'))
    {i : Nat} (hi : i < rt.size) : (ValuePtr.opResult (op'.getResult i)).InBounds ctx'.raw := by
  obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
  have := OperationPtr.getNumResults!_WfRewriter_createOp (operation := op') h
  grind

end CreateAtEnd

/-- The operation whose result the value is, if any. -/
def valueOwner : ValuePtr → Option OperationPtr
  | .opResult r => some r.op
  | .blockArgument _ => none

theorem valueOwner_inBounds {ctx : WfIRContext OpCode} {v : ValuePtr} {o : OperationPtr}
    (hv : v.InBounds ctx.raw) (h : valueOwner v = some o) : o.InBounds ctx.raw := by
  cases v with
  | opResult r =>
    simp only [valueOwner, Option.some.injEq] at h
    subst h
    grind
  | blockArgument _ => simp [valueOwner] at h

/-- `ctx'` is reached from `ctx` by `createAtEnd` steps. -/
inductive Reach : WfIRContext OpCode → WfIRContext OpCode → Prop
  | refl (ctx) : Reach ctx ctx
  | step {ctx ctx' ctx'' : WfIRContext OpCode} {blk : BlockPtr} {oc : OpCode}
      {p : propertiesOf oc} {rt : Array TypeAttr} {xs : Array ValuePtr} {o : OperationPtr} :
      createAtEnd ctx blk oc p rt xs = some (ctx', o) → Reach ctx' ctx'' → Reach ctx ctx''

theorem Reach.trans {a b c : WfIRContext OpCode} (h₁ : Reach a b) (h₂ : Reach b c) :
    Reach a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem Reach.op_inBounds {a b : WfIRContext OpCode} (h : Reach a b) {o : OperationPtr}
    (ho : o.InBounds a.raw) : o.InBounds b.raw := by
  induction h with
  | refl => exact ho
  | step h _ ih => exact ih (createAtEnd_op_inBounds_mono h ho)

theorem Reach.value_inBounds {a b : WfIRContext OpCode} (h : Reach a b) {v : ValuePtr}
    (hv : v.InBounds a.raw) : v.InBounds b.raw := by
  induction h with
  | refl => exact hv
  | step h _ ih => exact ih (createAtEnd_value_inBounds_mono h hv)

theorem Reach.opIs {a b : WfIRContext OpCode} (h : Reach a b) {o : OperationPtr} {oc : OpCode}
    {p : propertiesOf oc} {rt : Array TypeAttr} {xs : Array ValuePtr} (ho : OpIs a o oc p rt xs) :
    OpIs b o oc p rt xs := by
  induction h with
  | refl => exact ho
  | step h _ ih => exact ih (ho.createAtEnd h)

/-! ## The operations of an expansion, read in a context -/

/-- In `C`, the operations `ops` are the steps `steps` of an expansion with arguments
`args`, emitted after the results `done`, ending with the results `done'`: each
operation has the op-code, properties, result types and resolved operands of its
step, owns no argument and no earlier result. -/
def StepsIn (C : WfIRContext OpCode) (args : List ValuePtr) (resTy : TypeAttr) :
    List (VeirExpandStep OpCode) → List (List OpResultPtr) → List OperationPtr →
    List (List OpResultPtr) → Prop
  | [], done, ops, done' => ops = [] ∧ done' = done
  | s :: rest, done, ops, done' => ∃ o ops', ops = o :: ops' ∧
      OpIs C o s.op s.props (stepResTys resTy s)
        (s.operands.map (VeirSrc.resolve args done)).toArray ∧
      (∀ a ∈ args, valueOwner a ≠ some o) ∧ (∀ l ∈ done, ∀ r ∈ l, r.op ≠ o) ∧
      StepsIn C args resTy rest (done ++ [resultPtrs o (stepResTys resTy s).size]) ops' done'

theorem StepsIn.reach {a b : WfIRContext OpCode} (h : Reach a b) {args : List ValuePtr}
    {resTy : TypeAttr} : ∀ {steps : List (VeirExpandStep OpCode)} {done : List (List OpResultPtr)}
    {ops : List OperationPtr} {done' : List (List OpResultPtr)},
    StepsIn a args resTy steps done ops done' → StepsIn b args resTy steps done ops done'
  | [], _, _, _, hs => hs
  | _ :: _, _, _, _, ⟨o, ops', hops, ho, ha, hd, hr⟩ =>
      ⟨o, ops', hops, h.opIs ho, ha, hd, StepsIn.reach h hr⟩

theorem emitStepsWf_spec {blk : BlockPtr} {args : List ValuePtr} {resTy : TypeAttr} :
    ∀ {steps : List (VeirExpandStep OpCode)} {done : List (List OpResultPtr)}
      {ctx ctx' : WfIRContext OpCode} {ops : List OperationPtr}
      {done' : List (List OpResultPtr)} {L : List OperationPtr},
    emitStepsWf blk args resTy steps done ctx = some (ctx', ops, done') →
    Chain ctx blk L → (∀ a ∈ args, a.InBounds ctx.raw) →
    (∀ l ∈ done, ∀ r ∈ l, (ValuePtr.opResult r).InBounds ctx.raw) →
    Chain ctx' blk (L ++ ops) ∧ StepsIn ctx' args resTy steps done ops done' ∧
      (∀ o ∈ ops, ¬ o.InBounds ctx.raw) ∧
      (∀ l ∈ done', ∀ r ∈ l, (ValuePtr.opResult r).InBounds ctx'.raw) ∧ Reach ctx ctx'
  | [], done, ctx, ctx', ops, done', L, h, hc, _, hd => by
    simp only [emitStepsWf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨by simpa using hc, ⟨rfl, rfl⟩, by simp, hd, .refl _⟩
  | s :: rest, done, ctx, ctx', ops, done', L, h, hc, ha, hd => by
    simp only [emitStepsWf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨ctx₁, o⟩, h₁, ⟨ctx₂, ops₂, done₂⟩, h₂, hret⟩ := h
    simp only [Prod.mk.injEq] at hret
    obtain ⟨rfl, rfl, rfl⟩ := hret
    have hoNot := createAtEnd_new_not_inBounds h₁
    have hc₁ := hc.createAtEnd h₁
    have ha₁ : ∀ a ∈ args, a.InBounds ctx₁.raw := fun a hm =>
      createAtEnd_value_inBounds_mono h₁ (ha a hm)
    have hd₁ : ∀ l ∈ done ++ [resultPtrs o (stepResTys resTy s).size], ∀ r ∈ l,
        (ValuePtr.opResult r).InBounds ctx₁.raw := by
      intro l hl r hr
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact createAtEnd_value_inBounds_mono h₁ (hd l hl r hr)
      · simp only [resultPtrs, List.mem_map, List.mem_range] at hr
        obtain ⟨i, hi, rfl⟩ := hr
        exact createAtEnd_result_inBounds h₁ hi
    obtain ⟨hc₂, hs₂, hn₂, hd₂, hr₂⟩ := emitStepsWf_spec h₂ hc₁ ha₁ hd₁
    refine ⟨by simpa using hc₂,
      ⟨o, ops₂, rfl, hr₂.opIs (createAtEnd_opIs_new h₁), ?_, ?_, hs₂⟩,
      ?_, hd₂, .step h₁ hr₂⟩
    · intro a hm he
      exact hoNot (valueOwner_inBounds (ha a hm) he)
    · intro l hl r hr he
      apply hoNot
      have := hd l hl r hr
      rw [← he]
      exact valueOwner_inBounds (v := .opResult r) this rfl
    · intro o' hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hoNot
      · exact fun hin => hn₂ o' hm (createAtEnd_op_inBounds_mono h₁ hin)

/-! ## The operations of a program, read in a context -/

theorem mem_argPtrs {Γ : Ctxt jasminDialect} (vm : VarMap Γ) :
    ∀ {tys : List JasminTy} (xs : HVector (fun ty => Var Γ ty) tys) {a : ValuePtr},
    a ∈ argPtrs vm xs → ∃ (s : JasminTy) (v : Var Γ s), a = vm s v
  | [], .nil, _, h => by simp [argPtrs] at h
  | _ :: _, .cons x rest, _, h => by
    have h' : _ ∈ vm _ x :: argPtrs vm rest := h
    rcases List.mem_cons.1 h' with he | h''
    · exact ⟨_, x, he⟩
    · exact mem_argPtrs vm rest h''

/-- In `C`, the operations `ops` are the lowering of the program `c` under the
variable map `vm`, with value `final`: each binding is the `StepsIn` of its
`bindingExpansion`, whose operations own no value of `vm`. -/
def ComIn (C : WfIRContext OpCode) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    VarMap Γ → Com jasminDialect Γ t → List OperationPtr → ValuePtr → Prop
  | _, _, vm, .ret v, ops, final => ops = [] ∧ final = vm _ v
  | Γ, _, vm, .var (t := tEx) e body, ops, final =>
      ∃ ops₁ done ops₂, ops = ops₁ ++ ops₂ ∧
        StepsIn C (argPtrs vm e.args) (JasminTy.toVeirTy tEx)
          (bindingExpansion e.op (argPtrs vm e.args).length).steps [] ops₁ done ∧
        (∀ (s : JasminTy) (v : Var Γ s), ∀ o ∈ ops₁, valueOwner (vm s v) ≠ some o) ∧
        ComIn C (vm.extend (t := tEx)
          ((bindingExpansion e.op (argPtrs vm e.args).length).value.resolve
            (argPtrs vm e.args) done)) body ops₂ final

theorem ComIn.reach {a b : WfIRContext OpCode} (h : Reach a b) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {vm : VarMap Γ} {c : Com jasminDialect Γ t}
      {ops : List OperationPtr} {final : ValuePtr},
    ComIn a vm c ops final → ComIn b vm c ops final
  | _, _, _, .ret _, _, _, hc => by simp only [ComIn] at hc ⊢; exact hc
  | _, _, _, .var _ _, _, _, hc => by
    simp only [ComIn] at hc ⊢
    obtain ⟨ops₁, done, ops₂, hops, hs, hf, hb⟩ := hc
    exact ⟨ops₁, done, ops₂, hops, hs.reach h, hf, ComIn.reach h hb⟩

theorem lowerComWf_spec {blk : BlockPtr} :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {vm : VarMap Γ} {c : Com jasminDialect Γ t}
      {ctx ctx' : WfIRContext OpCode} {ops : List OperationPtr} {final : ValuePtr}
      {L : List OperationPtr},
    lowerComWf blk vm c ctx = some (ctx', ops, final) →
    Chain ctx blk L → (∀ (s : JasminTy) (v : Var Γ s), (vm s v).InBounds ctx.raw) →
    Chain ctx' blk (L ++ ops) ∧ ComIn ctx' vm c ops final ∧
      (∀ o ∈ ops, ¬ o.InBounds ctx.raw) ∧
      final.InBounds ctx'.raw ∧ Reach ctx ctx'
  | _, _, vm, .ret v, ctx, ctx', ops, final, L, h, hc, hvm => by
    simp only [lowerComWf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨by simpa using hc, ⟨rfl, rfl⟩, by simp, hvm _ v, .refl _⟩
  | _, _, vm, .var (t := tEx) e body, ctx, ctx', ops, final, L, h, hc, hvm => by
    simp only [lowerComWf, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ctx₁, ops₁, done⟩, h₁, h⟩ := h
    split at h
    · rename_i hval
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨⟨ctx₂, ops₂, final₂⟩, h₂, hret⟩ := h
      simp only [Prod.mk.injEq] at hret
      obtain ⟨rfl, rfl, rfl⟩ := hret
      have ha : ∀ a ∈ argPtrs vm e.args, a.InBounds ctx.raw := fun a hm => by
        obtain ⟨s, v, rfl⟩ := mem_argPtrs vm e.args hm
        exact hvm s v
      obtain ⟨hc₁, hs₁, hn₁, _, hr₁⟩ := emitStepsWf_spec h₁ hc ha (by simp)
      have hvm₁ : ∀ (s : JasminTy) (v : Var (tEx :: _) s),
          ((vm.extend (t := tEx) _) s v).InBounds ctx₁.raw := fun s v => by
        cases v with
        | here => exact hval
        | there v' => exact hr₁.value_inBounds (hvm _ v')
      obtain ⟨hc₂, hb₂, hn₂, hf₂, hr₂⟩ := lowerComWf_spec h₂ hc₁ hvm₁
      refine ⟨by simpa using hc₂,
        ⟨ops₁, done, ops₂, rfl, hs₁.reach hr₂, ?_, hb₂⟩, ?_, hf₂,
        hr₁.trans hr₂⟩
      · intro s v o hm he
        exact hn₁ o hm (valueOwner_inBounds (hvm s v) he)
      · intro o hm
        simp only [List.mem_append] at hm
        rcases hm with hm | hm
        · exact hn₁ o hm
        · exact fun hin => hn₂ o hm (hr₁.op_inBounds hin)
    · simp at h


/-! ## Running one operation -/

/-- An operation that `OpIs` with op-code `oc`, properties `p` and result types `rt`,
whose operands hold `vs`, runs under `interpretOp` to the results and control-flow
action of `interpretOp' oc p rt vs`, when the results conform to `rt`; the new state
binds its results and leaves every other value unchanged. -/
theorem interpretOp_of_opIs {C : WfIRContext OpCode} {o : OperationPtr} {oc : OpCode}
    {p : propertiesOf oc} {rt : Array TypeAttr} {xs : Array ValuePtr}
    (ho : OpIs C o oc p rt xs) (S : InterpreterState C) {vs res : Array RuntimeValue}
    {mem' : MemoryState} {cf : Option ControlFlowAction}
    (hvs : S.variables.getOperandValues o = some vs)
    (hi : interpretOp' oc p rt vs #[] S.memory = .ok (res, mem', cf))
    (hconf : RuntimeValue.ArrayConforms res rt) :
    ∃ S', interpretOp o S ho.inBounds = .ok (S', cf) ∧ S'.memory = mem' ∧
      ∀ v : ValuePtr, S'.variables.getVar? v =
        match v with
        | .opResult r => if r.op = o ∧ r.index < rt.size then some res[r.index]!
            else S.variables.getVar? v
        | .blockArgument _ => S.variables.getVar? v := by
  have hint : o.interpret C.raw vs S.memory = .ok (res, mem', cf) := by
    unfold OperationPtr.interpret
    rw [ho.opType, ho.props, ho.resTys, ho.succs]
    exact hi
  obtain ⟨vars', hset⟩ := (VariableState.setResultValues?_isSome_iff_conforms S.variables
    ho.inBounds).mp (by rw [ho.resTys]; exact hconf)
  have hS' : interpretOp o S ho.inBounds = .ok (⟨vars', mem'⟩, cf) :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hvs).2 ⟨res, hint, hset⟩
  refine ⟨⟨vars', mem'⟩, hS', rfl, fun v => ?_⟩
  have hn : o.getNumResults! C.raw = rt.size := by
    rw [VariableState.setResultValues?.getNumRseults!_eq_size hset]
    exact hconf.1
  rw [VariableState.getVar?_setResultValues? hset, hn]
  rcases v with ⟨o', i⟩ | _ <;> rfl

/-! ## Running the steps of an expansion -/

/-- Every value of `vals` conforms to the type of the same index in `rt`, and the
two arrays have one size. -/
def conformsB (vals : Array RuntimeValue) (rt : Array TypeAttr) : Bool :=
  vals.size == rt.size && (List.range vals.size).all fun i => decide (vals[i]!.Conforms rt[i]!)

theorem arrayConforms_of_conformsB {vals : Array RuntimeValue} {rt : Array TypeAttr}
    (h : conformsB vals rt = true) : RuntimeValue.ArrayConforms vals rt := by
  simp only [conformsB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1, fun i hi => h.2 i hi⟩

/-- The steps of an expansion run by `Veir.interpretOp'`, as `veirRunSteps`, where
each step must take no control-flow action and return results conforming to its
result types. -/
def veirRunStepsC (args : List RuntimeValue) (resTy : TypeAttr) :
    List (VeirExpandStep OpCode) → List (Array RuntimeValue) → MemoryState →
    Option (List (Array RuntimeValue) × MemoryState)
  | [], done, mem => some (done, mem)
  | s :: rest, done, mem =>
    match s.operands.mapM (VeirSrc.resolveVal args done) with
    | none => none
    | some ops =>
      match Veir.interpretOp' s.op s.props (stepResTys resTy s) ops.toArray #[] mem with
      | .ok (vals, mem', none) =>
          if conformsB vals (stepResTys resTy s) then
            veirRunStepsC args resTy rest (done ++ [vals]) mem'
          else none
      | _ => none

/-- In the variable state `S`, the argument pointers `args` hold the values `argV`. -/
def ArgRel {C : WfIRContext OpCode} (S : VariableState C) (args : List ValuePtr)
    (argV : List RuntimeValue) : Prop :=
  args.length = argV.length ∧ ∀ (i : Nat) (h : i < args.length), S.getVar? args[i] = argV[i]?

/-- In the variable state `S`, the result pointers `doneP` hold the result values
`doneV`. -/
def DoneRel {C : WfIRContext OpCode} (S : VariableState C) (doneP : List (List OpResultPtr))
    (doneV : List (Array RuntimeValue)) : Prop :=
  doneP.length = doneV.length ∧ ∀ (j : Nat) (hj : j < doneP.length) (hj' : j < doneV.length),
    doneP[j].length = doneV[j].size ∧
      ∀ (k : Nat) (hk : k < doneP[j].length), S.getVar? (.opResult doneP[j][k]) = doneV[j][k]?

theorem resolve_getVar {C : WfIRContext OpCode} {S : VariableState C} {args : List ValuePtr}
    {argV : List RuntimeValue} {doneP : List (List OpResultPtr)}
    {doneV : List (Array RuntimeValue)} (ha : ArgRel S args argV) (hd : DoneRel S doneP doneV)
    (src : VeirSrc) {v : RuntimeValue} (h : VeirSrc.resolveVal argV doneV src = some v) :
    S.getVar? (VeirSrc.resolve args doneP src) = some v := by
  cases src with
  | arg i =>
    simp only [VeirSrc.resolveVal] at h
    have hi : i < argV.length := by
      rcases Nat.lt_or_ge i argV.length with hi | hi
      · exact hi
      · simp [List.getElem?_eq_none hi] at h
    have hi' : i < args.length := ha.1 ▸ hi
    simp only [VeirSrc.resolve, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
      Option.getD_some]
    rw [ha.2 i hi', h]
  | res j slot =>
    simp only [VeirSrc.resolveVal, Option.bind_eq_some_iff] at h
    obtain ⟨lv, hlv, hv⟩ := h
    have hj' : j < doneV.length := by
      rcases Nat.lt_or_ge j doneV.length with hj | hj
      · exact hj
      · simp [List.getElem?_eq_none hj] at hlv
    have hj : j < doneP.length := hd.1 ▸ hj'
    rw [List.getElem?_eq_getElem hj', Option.some.injEq] at hlv
    subst hlv
    obtain ⟨hlen, hget⟩ := hd.2 j hj hj'
    have hk : slot < doneP[j].length := by
      rcases Nat.lt_or_ge slot doneV[j].size with hk | hk
      · omega
      · simp [Array.getElem?_eq_none hk] at hv
    simp only [VeirSrc.resolve, List.getElem?_eq_getElem hj, Option.bind_some,
      List.getElem?_eq_getElem hk]
    rw [hget slot hk, hv]

theorem mapM_resolve_getVar {C : WfIRContext OpCode} {S : VariableState C}
    {args : List ValuePtr} {argV : List RuntimeValue} {doneP : List (List OpResultPtr)}
    {doneV : List (Array RuntimeValue)} (ha : ArgRel S args argV) (hd : DoneRel S doneP doneV) :
    ∀ (l : List VeirSrc) (vs : List RuntimeValue),
    l.mapM (VeirSrc.resolveVal argV doneV) = some vs →
    (l.map (VeirSrc.resolve args doneP)).mapM S.getVar? = some vs
  | [], vs, h => by simpa using h
  | src :: l, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    simp only [List.map_cons, List.mapM_cons, resolve_getVar ha hd src hv,
      mapM_resolve_getVar ha hd l vs' hvs', Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]

theorem getVar_of_owner_ne {C : WfIRContext OpCode} {S S' : InterpreterState C}
    {o : OperationPtr} {rt : Array TypeAttr} {res : Array RuntimeValue}
    (hget : ∀ v : ValuePtr, S'.variables.getVar? v =
        match v with
        | .opResult r => if r.op = o ∧ r.index < rt.size then some res[r.index]!
            else S.variables.getVar? v
        | .blockArgument _ => S.variables.getVar? v)
    (v : ValuePtr) (hv : valueOwner v ≠ some o) :
    S'.variables.getVar? v = S.variables.getVar? v := by
  rw [hget v]
  cases v with
  | opResult r =>
    have : r.op ≠ o := fun he => hv (by simp [valueOwner, he])
    simp [this]
  | blockArgument _ => rfl

theorem resultPtrs_getElem {o : OperationPtr} {n k : Nat} (hk : k < (resultPtrs o n).length) :
    (resultPtrs o n)[k] = ⟨o, k⟩ := by
  simp [resultPtrs, OperationPtr.getResult_def]

/-- The operations of `StepsIn`, run by `interpretOpList` from a state whose argument
and earlier result pointers hold the values of `veirRunStepsC`, end with no
control-flow action, the memory of `veirRunStepsC`, all result pointers holding its
result values, and every value no operation owns unchanged. -/
theorem steps_sim {C : WfIRContext OpCode} {args : List ValuePtr} {argV : List RuntimeValue}
    {resTy : TypeAttr} :
    ∀ {steps : List (VeirExpandStep OpCode)} {doneP : List (List OpResultPtr)}
      {doneV : List (Array RuntimeValue)} {ops : List OperationPtr}
      {doneP' : List (List OpResultPtr)} {doneV' : List (Array RuntimeValue)}
      {S : InterpreterState C} {mem' : MemoryState},
    StepsIn C args resTy steps doneP ops doneP' →
    ArgRel S.variables args argV → DoneRel S.variables doneP doneV →
    veirRunStepsC argV resTy steps doneV S.memory = some (doneV', mem') →
    ∀ (hin : ∀ o ∈ ops, o.InBounds C.raw),
    ∃ S', interpretOpList ops S hin = .ok (S', none) ∧
      S'.memory = mem' ∧ DoneRel S'.variables doneP' doneV' ∧
      ∀ v, (∀ o ∈ ops, valueOwner v ≠ some o) →
        S'.variables.getVar? v = S.variables.getVar? v
  | [], doneP, doneV, ops, doneP', doneV', S, mem', hs, ha, hd, hr, hin => by
    obtain ⟨rfl, rfl⟩ := hs
    simp only [veirRunStepsC, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨S, by simp, rfl, hd, fun _ _ => rfl⟩
  | s :: rest, doneP, doneV, ops, doneP', doneV', S, mem', hs, ha, hd, hr, hin => by
    obtain ⟨o, ops', rfl, ho, hao, hdo, hrest⟩ := hs
    simp only [veirRunStepsC] at hr
    split at hr
    · simp at hr
    rename_i vs hvs
    split at hr
    rotate_left
    · simp at hr
    rename_i vals mem₁ hi
    split at hr
    rotate_left
    · simp at hr
    rename_i hcb
    have hconf := arrayConforms_of_conformsB hcb
    have hvs' : S.variables.getOperandValues o = some vs.toArray := by
      simp only [VariableState.getOperandValues, ho.operands]
      rw [List.mapM_toArray, mapM_resolve_getVar ha hd _ vs hvs]
      rfl
    obtain ⟨S₁, hS₁, hmem₁, hget⟩ := interpretOp_of_opIs ho S hvs' hi hconf
    have hne := getVar_of_owner_ne hget
    have ha₁ : ArgRel S₁.variables args argV := by
      refine ⟨ha.1, fun i hi => ?_⟩
      rw [hne _ (hao _ (List.getElem_mem hi)), ha.2 i hi]
    have hd₁ : DoneRel S₁.variables (doneP ++ [resultPtrs o (stepResTys resTy s).size])
        (doneV ++ [vals]) := by
      refine ⟨by simp [hd.1], fun j hj hj' => ?_⟩
      have hj2 : j < doneP.length + 1 := by simpa using hj
      rcases Nat.lt_or_ge j doneP.length with hlt | hge
      · have hlt' : j < doneV.length := hd.1 ▸ hlt
        rw [List.getElem_append_left hlt, List.getElem_append_left hlt']
        obtain ⟨hl, hg⟩ := hd.2 j hlt hlt'
        refine ⟨hl, fun k hk => ?_⟩
        rw [hne _ (by
          simp only [valueOwner, ne_eq, Option.some.injEq]
          exact hdo _ (List.getElem_mem hlt) _ (List.getElem_mem hk)), hg k hk]
      · have hj0 : j = doneP.length := by omega
        subst hj0
        have hlen := hd.1
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, hd.1, List.getElem_cons_zero]
        have hsz : (resultPtrs o (stepResTys resTy s).size).length = vals.size := by
          simp [resultPtrs, hconf.1]
        refine ⟨hsz, fun k hk => ?_⟩
        rw [hget, resultPtrs_getElem hk]
        have hk' : k < vals.size := hsz ▸ hk
        simp [hconf.1 ▸ hk', Array.getElem?_eq_getElem hk', getElem!_pos vals k hk']
    have hr' : veirRunStepsC argV resTy rest (doneV ++ [vals]) S₁.memory =
        some (doneV', mem') := by
      rw [hmem₁]; exact hr
    obtain ⟨S₂, hS₂, hmem₂, hd₂, hkeep⟩ := steps_sim hrest ha₁ hd₁ hr' (fun o' hm =>
      hin o' (List.mem_cons_of_mem _ hm))
    refine ⟨S₂, ?_, hmem₂, hd₂, fun v hv => ?_⟩
    · rw [interpretOpList_cons]
      simp only [hS₁]
      exact hS₂
    · rw [hkeep v (fun o' hm => hv o' (List.mem_cons_of_mem _ hm)),
        hne v (hv o List.mem_cons_self)]

/-! ## The expansions of the `arith` fragment -/

theorem conforms_int_integerType {w : Nat} (v : LLVM.Int w) (h) :
    (RuntimeValue.int w v).Conforms ((Attribute.integerType ⟨w⟩).asType h) := by
  simp [Attribute.asType, RuntimeValue.Conforms]

theorem veirRunStepsC_shift (bop : JasminBinOp) (hb : bop.IsShift) (w : Nat) (x y : LLVM.Int w)
    (mem : MemoryState) :
    ∃ doneV, veirRunStepsC [.int w x, .int w y] (JasminTy.toVeirTy (.reg w))
        (JasminOp.shiftSelectExpansion bop w).steps [] mem = some (doneV, mem) ∧
      VeirSrc.resolveVal [.int w x, .int w y] doneV (JasminOp.shiftSelectExpansion bop w).value =
        some (.int w (veirShiftSel bop x y)) := by
  cases bop <;> simp only [JasminBinOp.IsShift] at hb
  all_goals
    simp [veirRunStepsC, JasminOp.shiftSelectExpansion, VeirSrc.resolveVal, stepResTys,
      conformsB, interpretOp', Arith.interpretOp', JasminOp.toMlirOpCode,
      JasminBinOp.toArithOpCode, JasminTy.toVeirTy]
    exact ⟨⟨conforms_int_integerType _ _, conforms_int_integerType _ _,
      conforms_int_integerType _ _, conforms_int_integerType _ _,
      conforms_int_integerType _ _⟩, rfl⟩

theorem argPtrs_length {Γ : Ctxt jasminDialect} (vm : VarMap Γ) (ρ : VEnv Γ) :
    ∀ {tys : List JasminTy} (xs : HVector (fun ty => Var Γ ty) tys),
    (argPtrs vm xs).length = (argVals ρ xs).length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (· + 1) (argPtrs_length vm ρ rest)

/-- The `jasminDialect` types whose values are integers: `reg w` and `bool`. -/
def JasminTy.IsScalar : JasminTy → Prop
  | .reg _ => True
  | .bool => True
  | _ => False

theorem encodeVal_conforms {t : JasminTy} (ht : t.IsScalar) (a : TyDenote.denote t) :
    (encodeVal t a).Conforms (JasminTy.toVeirTy t) := by
  cases t <;> simp only [JasminTy.IsScalar] at ht
  · exact conforms_int_integerType _ _
  · exact conforms_int_integerType _ _

theorem isScalar_of_inArith {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (hc : JasminOp.InArith e.op) : t.IsScalar := by
  obtain ⟨op, hret, _⟩ := e
  cases op <;> simp only [JasminOp.InArith] at hc <;> (subst hret; trivial)

theorem mapM_range_arg (args : List RuntimeValue) (done : List (Array RuntimeValue)) :
    ∀ k, k ≤ args.length →
    ((List.range k).map VeirSrc.arg).mapM (VeirSrc.resolveVal args done) = some (args.take k)
  | 0, _ => by simp
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.mapM_append, mapM_range_arg args done k (by omega)]
    simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, VeirSrc.resolveVal,
      List.getElem?_eq_getElem (by omega : k < args.length), Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, List.take_add_one]
    rfl

/-- The one step of `bindingExpansion` of an op without an expansion and with one
result, run by `veirRunStepsC`, is the operation `veirRunOp`. -/
theorem veirRunStepsC_single (o : JasminOp) (t : JasminTy) (args : List RuntimeValue)
    (mem : MemoryState) (r : RuntimeValue) (hx : JasminOp.expandVeir? o = none)
    (hslot : JasminOp.resultSlotOfOp o = (1, 0))
    (hop : veirRunOp o t args mem = .ok (#[r], mem, none))
    (hconf : r.Conforms (JasminTy.toVeirTy t)) :
    ∃ doneV, veirRunStepsC args (JasminTy.toVeirTy t) (bindingExpansion o args.length).steps []
        mem = some (doneV, mem) ∧
      VeirSrc.resolveVal args doneV (bindingExpansion o args.length).value = some r := by
  have hops := mapM_range_arg args [] args.length le_rfl
  rw [List.take_length] at hops
  simp only [veirRunOp, hslot] at hop
  refine ⟨[#[r]], ?_, by simp [bindingExpansion, hx, hslot, VeirSrc.resolveVal]⟩
  simp only [bindingExpansion, hx, hslot, veirRunStepsC, hops, stepResTys]
  have hty : (List.map (fun x => x.getD (JasminTy.toVeirTy t))
      (List.replicate (max 1 1) (none : Option TypeAttr))).toArray =
      Array.replicate (max 1 1) (JasminTy.toVeirTy t) := by simp
  simp only [hty, hop]
  simp [conformsB, hconf]

/-- The steps of `bindingExpansion` of a binding of the `arith` fragment, run by
`veirRunStepsC` on operands read from the encoded valuation, leave memory unchanged
and give the expansion the encoded denotation of the binding as its value. -/
theorem bindingExpansion_run {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : JasminOp.InArith e.op)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) :
    ∃ doneV, veirRunStepsC (argVals ρ e.args) (JasminTy.toVeirTy t)
        (bindingExpansion e.op (argVals ρ e.args).length).steps [] mem = some (doneV, mem) ∧
      VeirSrc.resolveVal (argVals ρ e.args) doneV
        (bindingExpansion e.op (argVals ρ e.args).length).value =
        some (encodeVal t (e.denote V)) := by
  by_cases hsh : ∃ bop w, e.op = .regArith bop w ∧ bop.IsShift
  swap
  · have hx := JasminOp.expandVeir?_eq_none e.op hsh
    obtain ⟨hop, hslot⟩ := veirRunOp_expr_eq e V ρ mem hc
      (JasminOp.shiftSafe_of_not_shift e.op _ hsh) hρ
    have hslot' : JasminOp.resultSlotOfOp e.op = (1, 0) := by
      obtain ⟨op, _, _⟩ := e
      cases op <;> simp only [JasminOp.InArith] at hc <;> rfl
    exact veirRunStepsC_single e.op t _ mem _ hx hslot' hop
      (encodeVal_conforms (isScalar_of_inArith e hc) _)
  obtain ⟨bop, w, hop, hsh⟩ := hsh
  obtain ⟨op, hret, args⟩ := e
  simp only at hop
  subst hop
  subst hret
  cases args with
  | cons x rest =>
    cases rest with
    | cons y rest' =>
      cases rest'
      simp only
      rw [argVals_two, hρ, hρ]
      have hx : bindingExpansion (.regArith bop w) 2 = JasminOp.shiftSelectExpansion bop w := by
        cases bop <;> simp only [JasminBinOp.IsShift] at hsh <;> rfl
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, hx]
      obtain ⟨doneV, h₁, h₂⟩ := veirRunStepsC_shift bop hsh w
        (.val (x.lookup V)) (.val (y.lookup V)) mem
      exact ⟨doneV, h₁, h₂.trans (by rw [veirShiftSel_val bop hsh]; rfl)⟩

/-! ## The block -/

theorem createBlock_raw {types : Array TypeAttr} {c₀ c : WfIRContext OpCode} {blk : BlockPtr}
    {ip : Option BlockInsertPoint} {hip : Option.maybe BlockInsertPoint.InBounds ip c₀.raw}
    (h : WfRewriter.createBlock c₀ types ip hip = some (c, blk)) :
    ∃ hx, Rewriter.createBlock c₀.raw types ip hx hip = some (c.raw, blk) := by
  simp only [WfRewriter.createBlock] at h
  split at h
  · simp at h
  · rename_i ctx' blk' heq
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, heq⟩

/-- The block `WfRewriter.createBlock` creates without an insertion point holds no
operation and has one argument per type of `types`, with that type. -/
theorem createBlock_spec {types : Array TypeAttr} {c₀ c : WfIRContext OpCode} {blk : BlockPtr}
    {hip : Option.maybe BlockInsertPoint.InBounds none c₀.raw}
    (h : WfRewriter.createBlock c₀ types none hip = some (c, blk)) :
    Chain c blk [] ∧ blk.getNumArguments! c.raw = types.size ∧
      ∀ (i : Nat) (hi : i < types.size),
        (ValuePtr.blockArgument (blk.getArgument i)).getType! c.raw = types[i] ∧
        (ValuePtr.blockArgument (blk.getArgument i)).InBounds c.raw := by
  obtain ⟨hx, h⟩ := createBlock_raw h
  have hchain := BlockPtr.opChain_rewriter_createBlock_new h
  refine ⟨⟨hchain.blockInBounds, by simpa using hchain.first, by simpa using hchain.last,
    fun i hi => absurd hi (by simp), fun o ho => absurd ho (by simp), List.nodup_nil⟩, ?_⟩
  simp only [Rewriter.createBlock] at h
  split at h
  · simp at h
  rename_i ctx₁ blk₁ halloc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hc, rfl⟩ := h
  rw [← hc]
  have h0 := BlockPtr.getNumArguments!_BlockPtr_allocEmpty (block := blk₁) halloc
  simp only [if_true] at h0
  refine ⟨?_, fun i hi => ⟨?_, ?_⟩⟩
  · rw [BlockPtr.getNumArguments!_initBlockArguments, h0]; simp
  · rw [ValuePtr.getType!_initBlockArguments]; simp [h0, BlockPtr.getArgument_def, hi]
  · grind

/-- The block `WfRewriter.createBlock` creates at the end of the region `reg` holds no
operation and has one argument per type of `types`, with that type; the regions of
every operation are unchanged, and when `reg` held no block the new block is its first. -/
theorem createBlock_atEnd_spec {types : Array TypeAttr} {c₀ c : WfIRContext OpCode}
    {blk : BlockPtr} {reg : RegionPtr}
    {hip : Option.maybe BlockInsertPoint.InBounds (some (.atEnd reg)) c₀.raw}
    (h : WfRewriter.createBlock c₀ types (some (.atEnd reg)) hip = some (c, blk)) :
    (Chain c blk [] ∧ blk.getNumArguments! c.raw = types.size ∧
      ∀ (i : Nat) (hi : i < types.size),
        (ValuePtr.blockArgument (blk.getArgument i)).getType! c.raw = types[i] ∧
        (ValuePtr.blockArgument (blk.getArgument i)).InBounds c.raw) ∧
    (∀ o : OperationPtr, o.getNumRegions! c.raw = o.getNumRegions! c₀.raw) ∧
    (∀ (o : OperationPtr) (i : Nat), o.getRegion! c.raw i = o.getRegion! c₀.raw i) ∧
    ((reg.get! c₀.raw).lastBlock = none → (reg.get! c.raw).firstBlock = some blk) := by
  obtain ⟨hx, h⟩ := createBlock_raw h
  have hchain := BlockPtr.opChain_rewriter_createBlock_new h
  have hin := fun (p : GenericPtr) => Rewriter.createBlock_inBounds p h
  simp only [Rewriter.createBlock] at h
  split at h
  · simp at h
  rename_i ctx₁ blk₁ halloc
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨ctx₂, hins, hc, rfl⟩ := h
  have h0 := BlockPtr.getNumArguments!_BlockPtr_allocEmpty (block := blk₁) halloc
  simp only [if_true] at h0
  refine ⟨⟨⟨hchain.blockInBounds, by simpa using hchain.first, by simpa using hchain.last,
    fun i hi => absurd hi (by simp), fun o ho => absurd ho (by simp), List.nodup_nil⟩,
    ?_, fun i hi => ⟨?_, ?_⟩⟩, fun o => ?_, fun o i => ?_, fun hl => ?_⟩
  · rw [← hc, BlockPtr.getNumArguments!_insertBlock hins,
      BlockPtr.getNumArguments!_initBlockArguments, h0]; simp
  · rw [← hc, ValuePtr.getType!_insertBlock hins, ValuePtr.getType!_initBlockArguments]
    simp [h0, BlockPtr.getArgument_def, hi]
  · exact (hin (.value (.blockArgument _))).2 (by simp [BlockPtr.getArgument_def, hi])
  · rw [← hc, OperationPtr.getNumRegions!_insertBlock hins,
      OperationPtr.getNumRegions!_initBlockArguments,
      OperationPtr.getNumRegions!_BlockPtr_allocEmpty halloc]
  · rw [← hc, OperationPtr.getRegion!_insertBlock hins,
      OperationPtr.getRegion!_initBlockArguments,
      OperationPtr.getRegion!_BlockPtr_allocEmpty halloc]
  · rw [← hc, RegionPtr.firstBlock!_insertBlock hins]
    simp [RegionPtr.get!_initBlockArguments, RegionPtr.get!_BlockPtr_allocEmpty halloc, hl]

/-! ## Running the operations of a program -/

theorem argRel_of_env {C : WfIRContext OpCode} {Γ : Ctxt jasminDialect} (S : VariableState C)
    (vm : VarMap Γ) (ρ : VEnv Γ)
    (h : ∀ (s : JasminTy) (v : Var Γ s), S.getVar? (vm s v) = some (ρ s v)) :
    ∀ {tys : List JasminTy} (xs : HVector (fun ty => Var Γ ty) tys),
    ArgRel S (argPtrs vm xs) (argVals ρ xs)
  | [], .nil => ⟨rfl, fun i hi => absurd hi (by simp [argPtrs])⟩
  | _ :: _, .cons x rest => by
    obtain ⟨hl, hr⟩ := argRel_of_env S vm ρ h rest
    refine ⟨congrArg (· + 1) hl, fun i hi => ?_⟩
    cases i with
    | zero => exact h _ x
    | succ i =>
      have hlen : (argPtrs vm (HVector.cons x rest)).length = (argPtrs vm rest).length + 1 := rfl
      exact hr i (by omega)

/-- The operations of `ComIn`, run by `interpretOpList` from a state in which every
value of the variable map holds the encoded valuation `V`, end with no control-flow
action, memory unchanged, and the program's value holding the encoded denotation. -/
theorem com_sim {C : WfIRContext OpCode} :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {vm : VarMap Γ} {c : Com jasminDialect Γ t}
      {ops : List OperationPtr} {final : ValuePtr} (V : Valuation Γ) (S : InterpreterState C),
    ComIn C vm c ops final → ComInArith c →
    (∀ (s : JasminTy) (v : Var Γ s),
      S.variables.getVar? (vm s v) = some (encodeVal s (v.lookup V))) →
    ∀ (hin : ∀ o ∈ ops, o.InBounds C.raw),
    ∃ S', interpretOpList ops S hin = .ok (S', none) ∧
      S'.memory = S.memory ∧ S'.variables.getVar? final = some (encodeVal t (c.denote V))
  | _, _, vm, .ret v, ops, final, V, S, hc, _, hS, hin => by
    simp only [ComIn] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨S, by simp, rfl, hS _ v⟩
  | Γ, _, vm, .var (t := tEx) e body, ops, final, V, S, hc, harith, hS, hin => by
    simp only [ComIn] at hc
    obtain ⟨ops₁, done, ops₂, rfl, hs, hfresh, hb⟩ := hc
    let ρ : VEnv Γ := fun s v => encodeVal s (v.lookup V)
    have ha := argRel_of_env S.variables vm ρ hS e.args
    obtain ⟨doneV, hrun, hval⟩ := bindingExpansion_run e V ρ S.memory harith.1 (fun _ _ => rfl)
    rw [← argPtrs_length vm ρ e.args] at hrun hval
    obtain ⟨S₁, hS₁, hmem₁, hd₁, hkeep⟩ :=
      steps_sim hs ha ⟨rfl, fun j hj => by simp at hj⟩ hrun
      (fun o hm => hin o (List.mem_append_left _ hm))
    have hkeepVm : ∀ (s : JasminTy) (v : Var Γ s),
        S₁.variables.getVar? (vm s v) = S.variables.getVar? (vm s v) :=
      fun s v => hkeep _ (hfresh s v)
    have ha₁ : ArgRel S₁.variables (argPtrs vm e.args) (argVals ρ e.args) := by
      refine ⟨ha.1, fun i hi => ?_⟩
      obtain ⟨s, v, hv⟩ := mem_argPtrs vm e.args (List.getElem_mem hi)
      rw [hv, hkeepVm, ← hv, ha.2 i hi]
    have hv₁ := resolve_getVar ha₁ hd₁ _ hval
    have hS₁' : ∀ (s : JasminTy) (v : Var (tEx :: Γ) s),
        S₁.variables.getVar? ((vm.extend (t := tEx) (VeirSrc.resolve (argPtrs vm e.args) done
          (bindingExpansion e.op (argPtrs vm e.args).length).value)) s v) =
          some (encodeVal s (v.lookup (Ctxt.Valuation.extend V (e.denote V)))) := by
      intro s v
      cases v with
      | here => exact hv₁
      | there v' => exact (hkeepVm _ v').trans (hS _ v')
    obtain ⟨S₂, hS₂, hmem₂, hf₂⟩ := com_sim _ S₁ hb harith.2 hS₁'
      (fun o hm => hin o (List.mem_append_right _ hm))
    refine ⟨S₂, ?_, hmem₂.trans hmem₁, hf₂⟩
    rw [interpretOpList_append]
    simp only [hS₁]
    exact hS₂

/-! ## Block arguments and the block's operation chain -/

/-- The runtime values of a valuation, in De Bruijn order: entry `i` is the encoded
value of the variable of depth `i`. -/
def encodeArgs : {Γ : Ctxt jasminDialect} → Valuation Γ → List RuntimeValue
  | [], .nil => []
  | s :: _, .cons a V => encodeVal s a :: encodeArgs V

theorem encodeArgs_length : ∀ {Γ : Ctxt jasminDialect} (V : Valuation Γ),
    (encodeArgs V).length = Γ.length
  | [], .nil => rfl
  | _ :: _, .cons _ V => congrArg (· + 1) (encodeArgs_length V)

theorem encodeArgs_getElem? : ∀ {Γ : Ctxt jasminDialect} {s : JasminTy} (V : Valuation Γ)
    (v : Var Γ s), (encodeArgs V)[CatCrypt.Crypto.SecureCompilation.VIR.varDepth v]? =
      some (encodeVal s (v.lookup V))
  | _ :: _, _, .cons _ _, .here => rfl
  | _ :: _, _, .cons _ V, .there v => encodeArgs_getElem? V v

theorem encodeArgs_conforms : ∀ {Γ : Ctxt jasminDialect} (V : Valuation Γ),
    (∀ s ∈ Γ, JasminTy.IsScalar s) → ∀ (j : Nat), j < Γ.length →
    ((encodeArgs V).toArray[j]!).Conforms ((Γ.map JasminTy.toVeirTy).toArray[j]!)
  | [], .nil, _, j, hj => absurd hj (by simp)
  | s :: Γ, .cons a V, hΓ, j, hj => by
    have e : encodeArgs (HVector.cons a V) = encodeVal s a :: encodeArgs V := rfl
    cases j with
    | zero =>
      simpa [e] using encodeVal_conforms (hΓ s List.mem_cons_self) a
    | succ j =>
      have := encodeArgs_conforms V (fun s' hs' => hΓ s' (List.mem_cons_of_mem _ hs')) j
        (by simpa using hj)
      simpa [e] using this

theorem Reach.numArgs {a b : WfIRContext OpCode} (h : Reach a b) (blk : BlockPtr) :
    blk.getNumArguments! b.raw = blk.getNumArguments! a.raw := by
  induction h with
  | refl => rfl
  | step h _ ih =>
    obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
    rw [ih, BlockPtr.getNumArguments!_WfRewriter_createOp h]

theorem Reach.argType {a b : WfIRContext OpCode} (h : Reach a b) (arg : BlockArgumentPtr) :
    (ValuePtr.blockArgument arg).getType! b.raw = (ValuePtr.blockArgument arg).getType! a.raw := by
  induction h with
  | refl => rfl
  | step h _ ih =>
    obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
    rw [ih, ValuePtr.getType!_WfRewriter_createOp h]

/-- On a chain `o :: L` of a block, `interpretOpChain` from `o` is
`interpretTerminatedOpList` of the chain. -/
theorem interpretOpChain_of_chain {C : WfIRContext OpCode} :
    ∀ (L : List OperationPtr) (o : OperationPtr) (S : InterpreterState C),
      (∀ (i : Nat) (h : i < (o :: L).length),
        ((o :: L)[i].get! C.raw).next = (o :: L)[i + 1]?) →
      ∀ (hin : o.InBounds C.raw) (hin' : ∀ o' ∈ o :: L, o'.InBounds C.raw),
    interpretOpChain o S hin = interpretTerminatedOpList (o :: L) S hin'
  | [], o, S, hnext, hin, hin' => by
    have hn : (o.get! C.raw).next = none := hnext 0 (by simp)
    rw [interpretOpChain_of_next!_eq_none hn, interpretTerminatedOpList_cons]
    rcases interpretOp o S hin with _ | _ | ⟨S', _ | cf⟩ <;> simp
  | o₂ :: L, o, S, hnext, hin, hin' => by
    have hn : (o.get! C.raw).next = some o₂ := hnext 0 (by simp)
    rw [interpretOpChain_of_next!_eq_some hn, interpretTerminatedOpList_cons]
    rcases interpretOp o S hin with _ | _ | ⟨S', _ | cf⟩ <;> simp only
    exact interpretOpChain_of_chain L o₂ S' (fun i hi => hnext (i + 1) (by simpa using hi)) _ _

theorem interpretOpChain_of_chain' {C : WfIRContext OpCode} (L : List OperationPtr)
    (o : OperationPtr) (S : InterpreterState C) (hL : L.head? = some o)
    (hnext : ∀ (i : Nat) (h : i < L.length), (L[i].get! C.raw).next = L[i + 1]?)
    (hin : o.InBounds C.raw) (hin' : ∀ o' ∈ L, o'.InBounds C.raw) :
    interpretOpChain o S hin = interpretTerminatedOpList L S hin' := by
  cases L with
  | nil => simp at hL
  | cons o' L =>
    simp only [List.head?_cons, Option.some.injEq] at hL
    subst hL
    exact interpretOpChain_of_chain L o' S hnext hin hin'

/-! ## The block, run by `interpretBlock` -/

/-- A program of the `arith` fragment over a context of integer types, lowered by
`lowerComWf` into a block `blk₁` of `ctx₁` that holds no operation and has one argument
of type `toVeirTy s` per entry `s` of `Γ`, followed by a `func.return` of its value, run
by VeIR's `interpretBlock` from any state `S₀` with the block arguments set to the
encoded valuation `V`, returns the encoded denotation of the program through the
`func.return` and leaves the memory unchanged. -/
theorem interpretBlock_of_lowerComWf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (hc : ComInArith c)
    (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s)
    {ctx₁ ctx₂ ctx₃ : WfIRContext OpCode} {blk₁ : BlockPtr} {ops₂ : List OperationPtr}
    {final : ValuePtr} {ret : OperationPtr}
    (hblk : Chain ctx₁ blk₁ [] ∧
      blk₁.getNumArguments! ctx₁.raw = (Γ.map JasminTy.toVeirTy).toArray.size ∧
      ∀ (i : Nat) (hi : i < (Γ.map JasminTy.toVeirTy).toArray.size),
        (ValuePtr.blockArgument (blk₁.getArgument i)).getType! ctx₁.raw =
          (Γ.map JasminTy.toVeirTy).toArray[i] ∧
        (ValuePtr.blockArgument (blk₁.getArgument i)).InBounds ctx₁.raw)
    (h₂ : lowerComWf blk₁ (varMapOfBlockArgs blk₁) c ctx₁ = some (ctx₂, ops₂, final))
    (h₃ : createAtEnd ctx₂ blk₁ (.func .return) default #[] #[final] = some (ctx₃, ret))
    (S₀ : InterpreterState ctx₃) :
    ∃ (hb : blk₁.InBounds ctx₃.raw) (S : InterpreterState ctx₃), S.memory = S₀.memory ∧
      interpretBlock blk₁ (encodeArgs V).toArray S₀ hb =
        .ok (S, .return #[encodeVal t (c.denote V)]) := by
  obtain ⟨hchain₀, hnum, htypes⟩ := hblk
  have hvm : ∀ (s : JasminTy) (v : Var Γ s),
      (varMapOfBlockArgs blk₁ (Γ := Γ) s v).InBounds ctx₁.raw :=
    fun s v => (htypes _ (by simpa using CatCrypt.Crypto.SecureCompilation.VIR.varDepth_lt v)).2
  obtain ⟨hc₂, hcom, _, hfinal, hr₂⟩ := lowerComWf_spec h₂ hchain₀ hvm
  have hc₃ := hc₂.createAtEnd h₃
  have hr₃ : Reach ctx₂ ctx₃ := .step h₃ (.refl _)
  have hcom₃ := hcom.reach hr₃
  have hret := createAtEnd_opIs_new h₃
  have hr : Reach ctx₁ ctx₃ := hr₂.trans hr₃
  refine ⟨hc₃.blkIn, ?_⟩
  -- the block arguments
  have hnum₃ : blk₁.getNumArguments! ctx₃.raw = Γ.length := by
    rw [hr.numArgs, hnum]; simp
  obtain ⟨vars₁, hset⟩ := (VariableState.setArgumentValues?_isSome_iff_conforms
    S₀.variables (block := blk₁) (values := (encodeArgs V).toArray)
    (blockInBounds := hc₃.blkIn)).mp (by
      intro j hj
      rw [hnum₃] at hj
      rw [hr.argType, (htypes j (by simpa using hj)).1]
      have := encodeArgs_conforms V hΓ j hj
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj] using this)
  obtain ⟨o₀, rest, hol⟩ : ∃ o₀ rest, ops₂ ++ [ret] = o₀ :: rest := by
    cases ops₂ <;> simp
  have hfirst : (blk₁.get ctx₃.raw hc₃.blkIn).firstOp = some o₀ := by
    rw [← BlockPtr.get!_eq_get hc₃.blkIn, hc₃.first]
    simp [hol]
  unfold interpretBlock
  simp only [hset, liftM, monadLift, MonadLift.monadLift, Interp.bind_ok]
  split
  · rename_i hn; rw [hfirst] at hn; simp at hn
  rename_i o₁ ho₁
  rw [hfirst, Option.some.injEq] at ho₁
  subst ho₁
  simp only [List.nil_append] at hc₃ hcom₃ hret
  -- the environment of the block arguments
  have henv : ∀ (s : JasminTy) (v : Var Γ s),
      vars₁.getVar? (varMapOfBlockArgs blk₁ (Γ := Γ) s v) =
        some (encodeVal s (v.lookup V)) := by
    intro s v
    have hd := CatCrypt.Crypto.SecureCompilation.VIR.varDepth_lt v
    have hg := VariableState.getVar?_getArgument_of_setArgumentValues?
      (i := CatCrypt.Crypto.SecureCompilation.VIR.varDepth v) (by rw [hnum₃]; exact hd) hset
    refine hg.trans ?_
    have he := encodeArgs_getElem? V v
    simp [he]
  let S₁ : InterpreterState ctx₃ := ⟨vars₁, S₀.memory⟩
  rw [interpretOpChain_of_chain' (ops₂ ++ [ret]) _ S₁ (by rw [hol]; rfl) hc₃.next _
    hc₃.inBounds, interpretTerminatedOpList_append]
  obtain ⟨S₂, hS₂, hm₂, hf₂⟩ := com_sim V S₁ hcom₃ hc henv
    (fun o hm => hc₃.inBounds o (List.mem_append_left _ hm))
  simp only [hS₂]
  have hvs : S₂.variables.getOperandValues ret = some #[encodeVal t (c.denote V)] := by
    simp only [VariableState.getOperandValues, hret.operands]
    rw [List.mapM_toArray] at *
    simp [hf₂]
  obtain ⟨S₃, hS₃, hm₃, _⟩ := interpretOp_of_opIs hret S₂ hvs rfl ⟨rfl, by simp⟩
  refine ⟨S₃, hm₃.trans hm₂, ?_⟩
  rw [interpretTerminatedOpList_cons]
  simp only [hS₃]

/-- The lowering `lowerComToBlockWf` of a program of the `arith` fragment over a
context of integer types, run by VeIR's `interpretBlock` on the well-formed context it
builds, with the block arguments set to the encoded valuation `V`, returns the encoded
denotation of the program through the block's `func.return`. -/
theorem interpretBlock_lowerComToBlockWf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (hc : ComInArith c)
    (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s)
    {C : WfIRContext OpCode} {blk : BlockPtr} {ops : List OperationPtr}
    (h : lowerComToBlockWf c = some (C, blk, ops)) :
    ∃ (hb : blk.InBounds C.raw) (S : InterpreterState C),
      interpretBlock blk (encodeArgs V).toArray (InterpreterState.empty C) hb =
        .ok (S, .return #[encodeVal t (c.denote V)]) := by
  simp only [lowerComToBlockWf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨⟨ctx₁, blk₁⟩, h₁, ⟨ctx₂, ops₂, final⟩, h₂, ⟨ctx₃, ret⟩, h₃, hret⟩
    := h
  simp only [Prod.mk.injEq] at hret
  obtain ⟨rfl, rfl, rfl⟩ := hret
  obtain ⟨hb, S, _, hS⟩ := interpretBlock_of_lowerComWf c V hc hΓ (createBlock_spec h₁) h₂ h₃
    (InterpreterState.empty _)
  exact ⟨hb, S, hS⟩

/-- On the `arith` fragment over a context of integer types, VeIR's `interpretBlock`
on the block `lowerComToBlockWf` builds returns the value `veirRunCom` computes from
the encoded valuation. -/
theorem interpretBlock_lowerComToBlockWf_eq_veirRunCom {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V : Valuation Γ) (mem : MemoryState)
    (hc : ComInArith c) (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s)
    {C : WfIRContext OpCode} {blk : BlockPtr} {ops : List OperationPtr}
    (h : lowerComToBlockWf c = some (C, blk, ops)) :
    ∃ (hb : blk.InBounds C.raw) (S : InterpreterState C) (r : RuntimeValue),
      veirRunCom c (fun s v => encodeVal s (v.lookup V)) mem = .ok r ∧
      interpretBlock blk (encodeArgs V).toArray (InterpreterState.empty C) hb =
        .ok (S, .return #[r]) := by
  obtain ⟨hb, S, hS⟩ := interpretBlock_lowerComToBlockWf c V hc hΓ h
  exact ⟨hb, S, _, veirRunCom_eq_denote c V _ mem hc (fun _ _ => rfl), hS⟩

/-! ## Totality of the builder

`Rewriter.createOp` allocates the operation `⟨ctx.nextID⟩`; it returns a context
exactly when that pointer is not yet in bounds and the new operation can be linked
at its insertion point. `OpsBelow` (every operation has an identifier below
`nextID`) holds of the empty context and is preserved by each `createAtEnd`, so
every call of the builder succeeds on every program (`lowerComToBlockWf_isSome`). -/

section Fresh

variable {O : Type} [HasOpInfo O] {ctx : IRContext O}

theorem createEmptyOp_eq_some {Dialect : Type} [HasOpInfo Dialect] [HasDialect O Dialect]
    {oc : Dialect} {p : propertiesOf oc} {c : IRContext O} {o : OperationPtr}
    (h : Rewriter.createEmptyOp ctx oc p = some (c, o)) :
    o = ⟨ctx.nextID⟩ ∧ c.nextID = ctx.nextID + 1 := by
  unfold Rewriter.createEmptyOp OperationPtr.allocEmpty at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem initOpResults_nextID {op : OperationPtr} {rt : Array TypeAttr} {i : Nat} {h₁ h₂} :
    (Rewriter.initOpResults ctx op rt i h₁ h₂).nextID = ctx.nextID := by
  fun_induction Rewriter.initOpResults
  · rfl
  · rename_i ih; rw [ih]; rfl

theorem initOpRegions_empty {op : OperationPtr} {i : Nat} {h₁ h₂ h₃ h₄} :
    Rewriter.initOpRegions ctx op #[] i h₁ h₂ h₃ h₄ = some ctx := by
  unfold Rewriter.initOpRegions
  simp

theorem ValuePtr.setFirstUse_nextID (v : ValuePtr) (x) (h) :
    (v.setFirstUse ctx x h).nextID = ctx.nextID := by
  cases v <;> rfl

theorem pushOperand_nextID (op : OperationPtr) (v : ValuePtr) (h₁ h₂ h₃) :
    (Rewriter.pushOperand ctx op v h₁ h₂ h₃).nextID = ctx.nextID := by
  unfold Rewriter.pushOperand OpOperandPtr.insertIntoCurrent
  dsimp only
  split <;> exact ValuePtr.setFirstUse_nextID _ _ _

theorem initOpOperands_nextID {op : OperationPtr} {xs : Array ValuePtr} {n : Nat}
    {h₁ h₂ h₃ hn} :
    (Rewriter.initOpOperands ctx op h₁ xs h₂ h₃ n hn).nextID = ctx.nextID := by
  induction n generalizing ctx with
  | zero => unfold Rewriter.initOpOperands; rfl
  | succ n ih =>
    unfold Rewriter.initOpOperands
    dsimp only
    rw [ih, pushOperand_nextID]

theorem initBlockOperands_empty {op : OperationPtr} {h₁ h₂ h₃ hn} :
    Rewriter.initBlockOperands ctx op (#[] : Array BlockPtr) (#[] : Array BlockPtr).size
      h₁ h₂ h₃ hn = ctx := by
  unfold Rewriter.initBlockOperands; rfl

theorem OperationPtr.linkBetween_nextID (o : OperationPtr) (p n) (h₁ h₂ h₃) :
    (o.linkBetween ctx p n h₁ h₂ h₃).nextID = ctx.nextID := by
  unfold OperationPtr.linkBetween
  dsimp only
  split <;> split <;> rfl

/-- Inserting an operation without a parent at the end of a block succeeds and keeps
`nextID`. -/
theorem insertOp_atEnd_exists {op : OperationPtr} {blk : BlockPtr} {h₁ h₂ h₃}
    (hpar : (op.get! ctx).parent = none) :
    ∃ c, Rewriter.insertOp ctx op (.atEnd blk) h₁ h₂ h₃ = some c ∧ c.nextID = ctx.nextID := by
  unfold Rewriter.insertOp OperationPtr.linkBetweenWithParent
  split
  · rename_i h; simp [InsertPoint.block] at h
  rename_i parent hb
  dsimp only
  split
  · rename_i h
    exfalso
    unfold OperationPtr.setParentWithCheck at h
    split at h
    · rename_i p hp
      rw [← OperationPtr.get!_eq_get] at hp
      grind
    · simp at h
  rename_i c₂ h₂
  have hc₂ : c₂.nextID = ctx.nextID := by
    unfold OperationPtr.setParentWithCheck at h₂
    split at h₂
    · simp at h₂
    · cases h₂; exact OperationPtr.linkBetween_nextID op _ _ _ _ _
  split <;> split <;> exact ⟨_, rfl, hc₂⟩

theorem insertOp_atEnd_ne_none {op : OperationPtr} {blk : BlockPtr} {h₁ h₂ h₃}
    (hpar : (op.get! ctx).parent = none) :
    Rewriter.insertOp ctx op (.atEnd blk) h₁ h₂ h₃ ≠ none := by
  obtain ⟨c, hc, _⟩ := insertOp_atEnd_exists (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hpar
  simp [hc]

theorem insertOp_atEnd_nextID {op : OperationPtr} {blk : BlockPtr} {h₁ h₂ h₃}
    {c' : IRContext O} (hpar : (op.get! ctx).parent = none)
    (h : Rewriter.insertOp ctx op (.atEnd blk) h₁ h₂ h₃ = some c') :
    c'.nextID = ctx.nextID := by
  obtain ⟨c, hc, hn⟩ := insertOp_atEnd_exists (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hpar
  rw [hc] at h; cases h; exact hn

/-- `Rewriter.createOp` with no successors and no regions, inserting at the end of a
block, returns the operation `⟨ctx.nextID⟩` and increments `nextID` whenever that
pointer is not in bounds. -/
theorem createOp_atEnd_exists {Dialect : Type} [HasOpInfo Dialect] [HasDialect O Dialect]
    {oc : Dialect} {p : propertiesOf oc} {rt : Array TypeAttr} {xs : Array ValuePtr}
    {blk : BlockPtr} (h₁ h₂ h₃ h₄ h₅)
    (hfresh : ¬ (OperationPtr.mk ctx.nextID).InBounds ctx) :
    ∃ c', Rewriter.createOp ctx oc rt xs #[] #[] p (some (.atEnd blk)) h₁ h₂ h₃ h₄ h₅ =
      some (c', ⟨ctx.nextID⟩) ∧ c'.nextID = ctx.nextID + 1 := by
  unfold Rewriter.createOp
  split
  · rename_i heq
    unfold Rewriter.createEmptyOp OperationPtr.allocEmpty at heq
    grind [OperationPtr.InBounds]
  rename_i c₁ o₁ he
  obtain ⟨rfl, hn₁⟩ := createEmptyOp_eq_some he
  dsimp only
  split
  · rename_i h; rw [initOpRegions_empty] at h; simp at h
  rename_i c₂ h₂
  rw [initOpRegions_empty] at h₂
  cases h₂
  have hpar : ∀ {h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉},
      ((OperationPtr.mk ctx.nextID).get! (Rewriter.initBlockOperands
        (Rewriter.initOpOperands (Rewriter.initOpResults c₁ ⟨ctx.nextID⟩ rt 0 h₁ h₂)
          ⟨ctx.nextID⟩ h₃ xs h₄ h₅ xs.size h₆) ⟨ctx.nextID⟩ (#[] : Array BlockPtr)
          (#[] : Array BlockPtr).size h₇ h₈ h₉ (by simp))).parent = none := by
    intros
    rw [OperationPtr.parent!_initBlockOperands, OperationPtr.parent!_initOpOperands,
      OperationPtr.parent!_initOpResults, OperationPtr.parent!_createEmptyOp he]
    simp
  split
  · rename_i h
    exact absurd h (insertOp_atEnd_ne_none hpar)
  · rename_i c₅ h₅'
    refine ⟨c₅, rfl, ?_⟩
    rw [insertOp_atEnd_nextID hpar h₅', initBlockOperands_empty, initOpOperands_nextID,
      initOpResults_nextID, hn₁]

/-- `Rewriter.createOp` with no successors, no regions and no insertion point returns
the operation `⟨ctx.nextID⟩` and increments `nextID` whenever that pointer is not in
bounds. -/
theorem createOp_none_exists {Dialect : Type} [HasOpInfo Dialect] [HasDialect O Dialect]
    {oc : Dialect} {p : propertiesOf oc} {rt : Array TypeAttr} {xs : Array ValuePtr}
    (h₁ h₂ h₃ h₄ h₅)
    (hfresh : ¬ (OperationPtr.mk ctx.nextID).InBounds ctx) :
    ∃ c', Rewriter.createOp ctx oc rt xs #[] #[] p none h₁ h₂ h₃ h₄ h₅ =
      some (c', ⟨ctx.nextID⟩) ∧ c'.nextID = ctx.nextID + 1 := by
  unfold Rewriter.createOp
  split
  · rename_i heq
    unfold Rewriter.createEmptyOp OperationPtr.allocEmpty at heq
    grind [OperationPtr.InBounds]
  rename_i c₁ o₁ he
  obtain ⟨rfl, hn₁⟩ := createEmptyOp_eq_some he
  dsimp only
  split
  · rename_i h; rw [initOpRegions_empty] at h; simp at h
  rename_i c₂ h₂
  rw [initOpRegions_empty] at h₂
  cases h₂
  refine ⟨_, rfl, ?_⟩
  rw [initBlockOperands_empty, initOpOperands_nextID, initOpResults_nextID, hn₁]

end Fresh

/-- Every operation in bounds in `ctx` has an identifier below `ctx.nextID`. -/
def OpsBelow (ctx : IRContext OpCode) : Prop :=
  ∀ o : OperationPtr, o.InBounds ctx → o.id < ctx.nextID

theorem opsBelow_default : OpsBelow (default : WfIRContext OpCode).raw := by
  intro o ho
  simp [OperationPtr.InBounds, default, IRContext.empty] at ho

theorem OpsBelow.createOp_atEnd {c c' : IRContext OpCode} {oc : OpCode} {p : propertiesOf oc}
    {rt : Array TypeAttr} {xs : Array ValuePtr} {blk : BlockPtr} {o : OperationPtr}
    {h₁ h₂ h₃ h₄ h₅} (hf : OpsBelow c)
    (h : Rewriter.createOp c oc rt xs #[] #[] p (some (.atEnd blk)) h₁ h₂ h₃ h₄ h₅ =
      some (c', o)) : OpsBelow c' := by
  have hfresh : ¬ (OperationPtr.mk c.nextID).InBounds c := fun hin =>
    Nat.lt_irrefl _ (hf _ hin)
  obtain ⟨c'', hc, hn⟩ := createOp_atEnd_exists (Dialect := OpCode) h₁ h₂ h₃ h₄ h₅ hfresh
  rw [hc] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  intro q hq
  have := (Rewriter.createOp_inBounds (.operation q) hc).1 (by simpa using hq)
  simp only [GenericPtr.operation.injEq] at this
  rw [hn]
  rcases this with hq' | rfl
  · have := hf q (by simpa using hq'); omega
  · simp

theorem createAtEnd_exists {ctx : WfIRContext OpCode} {blk : BlockPtr} {oc : OpCode}
    {p : propertiesOf oc} {rt : Array TypeAttr} {xs : Array ValuePtr}
    (hx : ∀ v ∈ xs, v.InBounds ctx.raw) (hb : blk.InBounds ctx.raw) (hf : OpsBelow ctx.raw) :
    ∃ ctx' op', createAtEnd ctx blk oc p rt xs = some (ctx', op') ∧ OpsBelow ctx'.raw := by
  have hfresh : ¬ (OperationPtr.mk ctx.raw.nextID).InBounds ctx.raw := fun hin =>
    Nat.lt_irrefl _ (hf _ hin)
  unfold createAtEnd
  rw [dif_pos hx, dif_pos hb]
  unfold WfRewriter.createOp
  split
  · rename_i h
    obtain ⟨c, hc, _⟩ := createOp_atEnd_exists (Dialect := OpCode) (oc := oc) (p := p) (rt := rt) (blk := blk)
      hx (by simp) (by simp) (by simpa [Option.maybe_some] using hb) (by grind) hfresh
    rw [hc] at h; simp at h
  · rename_i c o h
    exact ⟨_, _, rfl, hf.createOp_atEnd h⟩

/-- The operand `src` of an expansion step reads an argument below `nargs`, or a
result of an earlier step, the steps so far having `sizes` results. -/
def SrcInScope (nargs : Nat) (sizes : List Nat) : VeirSrc → Prop
  | .arg i => i < nargs
  | .res j slot => ∃ n, sizes[j]? = some n ∧ slot < n

/-- Every operand of every step reads an argument below `nargs` or a result of an
earlier step, the steps before the first having `sizes` results. -/
def StepsInScope (nargs : Nat) : List (VeirExpandStep OpCode) → List Nat → Prop
  | [], _ => True
  | s :: rest, sizes => (∀ src ∈ s.operands, SrcInScope nargs sizes src) ∧
      StepsInScope nargs rest (sizes ++ [s.results.length])

/-- The steps and the value of the expansion `x` read only arguments below `nargs`
and results of earlier steps. -/
def ExpansionInScope (x : VeirExpansion OpCode) (nargs : Nat) : Prop :=
  StepsInScope nargs x.steps [] ∧ SrcInScope nargs (x.steps.map (·.results.length)) x.value

theorem resolve_inBounds {C : IRContext OpCode} {args : List ValuePtr}
    {done : List (List OpResultPtr)} {src : VeirSrc}
    (ha : ∀ a ∈ args, a.InBounds C) (hd : ∀ l ∈ done, ∀ r ∈ l, (ValuePtr.opResult r).InBounds C)
    (hs : SrcInScope args.length (done.map List.length) src) :
    (src.resolve args done).InBounds C := by
  cases src with
  | arg i =>
    simp only [SrcInScope] at hs
    simp only [VeirSrc.resolve, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs,
      Option.getD_some]
    exact ha _ (List.getElem_mem hs)
  | res j slot =>
    obtain ⟨n, hn, hlt⟩ := hs
    rw [List.getElem?_map] at hn
    cases hj : done[j]? with
    | none => simp [hj] at hn
    | some l =>
      simp only [hj, Option.map_some, Option.some.injEq] at hn
      subst hn
      have hl : l ∈ done := List.mem_of_getElem? hj
      simp only [VeirSrc.resolve, hj, Option.bind_some, List.getElem?_eq_getElem hlt]
      exact hd l hl _ (List.getElem_mem hlt)

theorem resultPtrs_length (o : OperationPtr) (n : Nat) : (resultPtrs o n).length = n := by
  simp [resultPtrs]

theorem emitStepsWf_exists {blk : BlockPtr} {args : List ValuePtr} {resTy : TypeAttr} :
    ∀ {steps : List (VeirExpandStep OpCode)} {done : List (List OpResultPtr)}
      {ctx : WfIRContext OpCode},
    StepsInScope args.length steps (done.map List.length) → OpsBelow ctx.raw →
    blk.InBounds ctx.raw → (∀ a ∈ args, a.InBounds ctx.raw) →
    (∀ l ∈ done, ∀ r ∈ l, (ValuePtr.opResult r).InBounds ctx.raw) →
    ∃ ctx' ops done', emitStepsWf blk args resTy steps done ctx = some (ctx', ops, done') ∧
      OpsBelow ctx'.raw ∧
      done'.map List.length = done.map List.length ++ steps.map (·.results.length)
  | [], done, ctx, _, hf, _, _, _ => ⟨ctx, [], done, rfl, hf, by simp⟩
  | s :: rest, done, ctx, hs, hf, hb, ha, hd => by
    have hx : ∀ v ∈ (s.operands.map (VeirSrc.resolve args done)).toArray,
        v.InBounds ctx.raw := by
      intro v hv
      simp only [List.mem_toArray, List.mem_map] at hv
      obtain ⟨src, hsrc, rfl⟩ := hv
      exact resolve_inBounds ha hd (hs.1 src hsrc)
    obtain ⟨ctx₁, o, h₁, hf₁⟩ := createAtEnd_exists (oc := s.op) (p := s.props)
      (rt := stepResTys resTy s) hx hb hf
    have hd₁ : ∀ l ∈ done ++ [resultPtrs o (stepResTys resTy s).size], ∀ r ∈ l,
        (ValuePtr.opResult r).InBounds ctx₁.raw := by
      intro l hl r hr
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact createAtEnd_value_inBounds_mono h₁ (hd l hl r hr)
      · simp only [resultPtrs, List.mem_map, List.mem_range] at hr
        obtain ⟨i, hi, rfl⟩ := hr
        exact createAtEnd_result_inBounds h₁ hi
    have hsz : (stepResTys resTy s).size = s.results.length := by simp [stepResTys]
    have hs₁ : StepsInScope args.length rest
        ((done ++ [resultPtrs o (stepResTys resTy s).size]).map List.length) := by
      simpa [resultPtrs_length, hsz] using hs.2
    obtain ⟨ctx₂, ops₂, done₂, h₂, hf₂, hl₂⟩ := emitStepsWf_exists (resTy := resTy) hs₁ hf₁
      (createAtEnd_block_inBounds_mono h₁ hb)
      (fun a hm => createAtEnd_value_inBounds_mono h₁ (ha a hm)) hd₁
    refine ⟨ctx₂, o :: ops₂, done₂, ?_, hf₂, ?_⟩
    · simp only [emitStepsWf, h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · rw [hl₂]; simp [resultPtrs_length, hsz]

theorem argPtrs_length_eq {Γ : Ctxt jasminDialect} (vm : VarMap Γ) :
    ∀ {tys : List JasminTy} (xs : HVector (fun ty => Var Γ ty) tys),
    (argPtrs vm xs).length = tys.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (· + 1) (argPtrs_length_eq vm rest)

/-- The expansion of every op of `jasminDialect`, with one argument per entry of its
signature, reads only its arguments and results of earlier steps. -/
theorem bindingExpansion_inScope (o : JasminOp) :
    ExpansionInScope (bindingExpansion o (DialectSignature.sig (d := jasminDialect) o).length)
      (DialectSignature.sig (d := jasminDialect) o).length := by
  unfold bindingExpansion
  cases h : JasminOp.expandVeir? o with
  | some x =>
    cases o <;> simp [JasminOp.expandVeir?] at h
    rename_i bop w
    have hl : (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)).length = 2 :=
      rfl
    rw [hl]
    cases bop <;> simp at h <;> subst h <;>
      simp [ExpansionInScope, StepsInScope, SrcInScope, JasminOp.shiftSelectExpansion]
  | none =>
    refine ⟨⟨?_, trivial⟩, ?_⟩
    · intro src hsrc
      simp only [List.mem_map, List.mem_range] at hsrc
      obtain ⟨i, hi, rfl⟩ := hsrc
      exact hi
    · show SrcInScope _ [(List.replicate (max (JasminOp.resultSlotOfOp o).1 1) none).length]
        (.res 0 (JasminOp.resultSlotOfOp o).2)
      refine ⟨_, rfl, ?_⟩
      rw [List.length_replicate]
      unfold JasminOp.resultSlotOfOp
      split <;> decide

theorem lowerComWf_exists {blk : BlockPtr} :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {vm : VarMap Γ} (c : Com jasminDialect Γ t)
      {ctx : WfIRContext OpCode} {L : List OperationPtr},
    OpsBelow ctx.raw → Chain ctx blk L → (∀ (s : JasminTy) (v : Var Γ s), (vm s v).InBounds ctx.raw) →
    ∃ ctx' ops final, lowerComWf blk vm c ctx = some (ctx', ops, final) ∧ OpsBelow ctx'.raw
  | _, _, vm, .ret v, ctx, _, hf, _, _ => ⟨ctx, [], vm _ v, rfl, hf⟩
  | _, _, vm, .var (t := tEx) e body, ctx, L, hf, hc, hvm => by
    have ha : ∀ a ∈ argPtrs vm e.args, a.InBounds ctx.raw := fun a hm => by
      obtain ⟨s, v, rfl⟩ := mem_argPtrs vm e.args hm
      exact hvm s v
    have hlen := argPtrs_length_eq vm e.args
    have hsc := bindingExpansion_inScope e.op
    rw [← hlen] at hsc
    obtain ⟨ctx₁, ops₁, done, h₁, hf₁, hl₁⟩ := emitStepsWf_exists (blk := blk)
      (resTy := JasminTy.toVeirTy tEx) (done := []) hsc.1 hf hc.blkIn ha (by simp)
    obtain ⟨hc₁, _, _, hd₁, hr₁⟩ := emitStepsWf_spec h₁ hc ha (by simp)
    have hval : ((bindingExpansion e.op (argPtrs vm e.args).length).value.resolve
        (argPtrs vm e.args) done).InBounds ctx₁.raw :=
      resolve_inBounds (fun a hm => hr₁.value_inBounds (ha a hm)) hd₁
        (by rw [hl₁]; simpa using hsc.2)
    have hvm₁ : ∀ (s : JasminTy) (v : Var (tEx :: _) s),
        ((vm.extend (t := tEx) _) s v).InBounds ctx₁.raw := fun s v => by
      cases v with
      | here => exact hval
      | there v' => exact hr₁.value_inBounds (hvm _ v')
    obtain ⟨ctx₂, ops₂, final, h₂, hf₂⟩ := lowerComWf_exists (vm := vm.extend (t := tEx)
      ((bindingExpansion e.op (argPtrs vm e.args).length).value.resolve (argPtrs vm e.args) done))
      body hf₁ hc₁ hvm₁
    refine ⟨ctx₂, ops₁ ++ ops₂, final, ?_, hf₂⟩
    simp only [lowerComWf, h₁, Option.bind_eq_bind, Option.bind_some, if_pos hval, h₂,
      Option.pure_def]

/-- `lowerComToBlockWf` returns a context for every program of `jasminDialect`. -/
theorem lowerComToBlockWf_isSome {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) :
    ∃ C blk ops, lowerComToBlockWf c = some (C, blk, ops) := by
  obtain ⟨ctx₁, blk, h₁⟩ : ∃ ctx₁ blk, WfRewriter.createBlock (default : WfIRContext OpCode)
      (Γ.map JasminTy.toVeirTy).toArray none (by simp [Option.maybe_none]) =
        some (ctx₁, blk) := by
    unfold WfRewriter.createBlock
    split
    · rename_i h
      unfold Rewriter.createBlock BlockPtr.allocEmpty at h
      simp only [default, IRContext.empty] at h
      split at h <;> simp_all
    · exact ⟨_, _, rfl⟩
  have hf₁ : OpsBelow ctx₁.raw := by
    obtain ⟨_, hr⟩ := createBlock_raw h₁
    intro o ho
    have := (Rewriter.createBlock_inBounds (.operation o) hr).1 (by simpa using ho)
    simp [OperationPtr.InBounds, default, IRContext.empty] at this
  obtain ⟨hchain₀, _, htypes⟩ := createBlock_spec h₁
  have hvm : ∀ (s : JasminTy) (v : Var Γ s),
      (varMapOfBlockArgs blk (Γ := Γ) s v).InBounds ctx₁.raw :=
    fun s v => (htypes _ (by simpa using CatCrypt.Crypto.SecureCompilation.VIR.varDepth_lt v)).2
  obtain ⟨ctx₂, ops, final, h₂, hf₂⟩ := lowerComWf_exists c hf₁ hchain₀ hvm
  obtain ⟨hc₂, _, _, hfinal, _⟩ := lowerComWf_spec h₂ hchain₀ hvm
  obtain ⟨ctx₃, ret, h₃, _⟩ := createAtEnd_exists (oc := .func .return) (p := default)
    (rt := #[]) (xs := #[final]) (by simpa using hfinal) hc₂.blkIn hf₂
  refine ⟨ctx₃, blk, ops ++ [ret], ?_⟩
  simp only [lowerComToBlockWf, h₁, h₂, h₃, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

/-- On the `arith` fragment over a context of integer types, `lowerComToBlockWf`
returns a well-formed context, and VeIR's `interpretBlock` on its block, with the
arguments set to the encoded valuation `V`, returns the encoded denotation of the
program. -/
theorem exists_interpretBlock_lowerComToBlockWf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (hc : ComInArith c)
    (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s) :
    ∃ C blk ops, lowerComToBlockWf c = some (C, blk, ops) ∧
      ∃ (hb : blk.InBounds C.raw) (S : InterpreterState C),
        interpretBlock blk (encodeArgs V).toArray (InterpreterState.empty C) hb =
          .ok (S, .return #[encodeVal t (c.denote V)]) := by
  obtain ⟨C, blk, ops, h⟩ := lowerComToBlockWf_isSome c
  exact ⟨C, blk, ops, h, interpretBlock_lowerComToBlockWf c V hc hΓ h⟩

/-- On the `arith` fragment over a context of integer types, `lowerComToBlockWf`
returns a well-formed context, and VeIR's `interpretBlock` on its block returns the
value `veirRunCom` computes from the encoded valuation. -/
theorem exists_interpretBlock_lowerComToBlockWf_eq_veirRunCom {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V : Valuation Γ) (mem : MemoryState)
    (hc : ComInArith c) (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s) :
    ∃ C blk ops, lowerComToBlockWf c = some (C, blk, ops) ∧
      ∃ (hb : blk.InBounds C.raw) (S : InterpreterState C) (r : RuntimeValue),
        veirRunCom c (fun s v => encodeVal s (v.lookup V)) mem = .ok r ∧
        interpretBlock blk (encodeArgs V).toArray (InterpreterState.empty C) hb =
          .ok (S, .return #[r]) := by
  obtain ⟨C, blk, ops, h⟩ := lowerComToBlockWf_isSome c
  exact ⟨C, blk, ops, h, interpretBlock_lowerComToBlockWf_eq_veirRunCom c V mem hc hΓ h⟩

/-! ## The program as a `func.func` inside a `builtin.module`

`lowerComToFuncWf` builds, through VeIR's `WfIRContext.create` and `WfRewriter`, a
`builtin.module` whose block holds one `func.func`, whose one region holds the block of
the lowering: the arguments of `Γ`, the operations of `lowerComWf` and a `func.return`.
`interpretFunction_lowerComToFuncWf` runs that `func.func` with VeIR's function-level
interpreter `interpretFunction`. -/

/-- The properties of the `func.func` named `name` of a program over `Γ` returning `t`:
the symbol name, the function type with inputs `toVeirTy s` for the entries `s` of `Γ`
and the output `toVeirTy t`, and no further attributes. -/
def funcPropsWf (Γ : Ctxt jasminDialect) (t : JasminTy) (name : String) :
    propertiesOf (OpCode.func .func) :=
  CatCrypt.Crypto.SecureCompilation.VIR.VeirPrinterShim.funcFuncProps name
    { inputs := (Γ.map fun s => (JasminTy.toVeirTy s).val).toArray,
      outputs := #[(JasminTy.toVeirTy t).val] } default

/-- Create an operation with op-code `oc`, properties `p` and no operands, results,
successors or regions, through `WfRewriter.createOp`: at the end of the block `mb` for
`some mb` (`createAtEnd`), detached for `none`. -/
def createOpAt (ctx : WfIRContext OpCode) (oc : OpCode) (p : propertiesOf oc) :
    Option BlockPtr → Option (WfIRContext OpCode × OperationPtr)
  | none => WfRewriter.createOp ctx oc #[] #[] #[] #[] p none (by simp) (by simp) (by simp)
      (by simp [Option.maybe_none])
  | some mb => createAtEnd ctx mb oc p #[] #[]

/-- Create a region and an operation with op-code `oc`, properties `p` and no operands,
results, successors or regions, through `WfRewriter`, and push the region onto the
operation (`WfRewriter.pushRegion`); the operation is inserted at the end of the block
`mb?` when it is `some`, and left detached when it is `none`. Returns the context, the
operation and the region. -/
def createRegionOp (ctx : WfIRContext OpCode) (oc : OpCode) (p : propertiesOf oc)
    (mb? : Option BlockPtr) : Option (WfIRContext OpCode × OperationPtr × RegionPtr) := do
  let (ctx₁, reg) ← WfRewriter.createRegion ctx
  let (ctx₂, o) ← createOpAt ctx₁ oc p mb?
  if h : o.InBounds ctx₂.raw ∧ reg.InBounds ctx₂.raw ∧ (reg.get! ctx₂.raw).parent = none then
    pure (WfRewriter.pushRegion ctx₂ o reg h.1 h.2.1 h.2.2, o, reg)
  else none

/-- Create a block with arguments of types `types` at the end of the region `reg`,
through `WfRewriter.createBlock`; `none` when `reg` is not in bounds. -/
def createBlockIn (ctx : WfIRContext OpCode) (types : Array TypeAttr) (reg : RegionPtr) :
    Option (WfIRContext OpCode × BlockPtr) :=
  if hreg : reg.InBounds ctx.raw then
    WfRewriter.createBlock ctx types (some (.atEnd reg))
      (by simpa [Option.maybe_some, BlockInsertPoint.inBounds_atEnd] using hreg)
  else none

/-- Lower a `Com jasminDialect Γ t` into a `func.func` named `name` inside a fresh
`builtin.module`: a `builtin.module` whose one region holds one empty block `mb` (the
steps of `IRContext.create`), a `func.func` at the end of `mb` with properties
`funcPropsWf Γ t name` and one region `reg`, and a block at the end of `reg` with one
argument per entry of `Γ`, the operations of `lowerComWf` and a `func.return` of the
program's value. Returns the context, the module, the `func.func`, the block and its
operations in order. -/
def lowerComToFuncWf {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (name : String) :
    Option (WfIRContext OpCode × OperationPtr × OperationPtr × BlockPtr ×
      List OperationPtr) := do
  let (ctxM, modOp, mreg) ← createRegionOp default (.builtin .module) default none
  let (ctx₀, mb) ← createBlockIn ctxM #[] mreg
  let (ctx₁, fn, reg) ← createRegionOp ctx₀ (.func .func) (funcPropsWf Γ t name) (some mb)
  let (ctx₂, blk) ← createBlockIn ctx₁ (Γ.map JasminTy.toVeirTy).toArray reg
  let (ctx₃, ops, final) ← lowerComWf blk (varMapOfBlockArgs blk) c ctx₂
  let (ctx₄, ret) ← createAtEnd ctx₃ blk (.func .return) default #[] #[final]
  pure (ctx₄, modOp, fn, blk, ops ++ [ret])

/-- The region `WfRewriter.createRegion` creates holds no block, and every pointer in
bounds before is in bounds after. -/
theorem createRegion_spec {c₀ c : WfIRContext OpCode} {reg : RegionPtr}
    (h : WfRewriter.createRegion c₀ = some (c, reg)) :
    (reg.get! c.raw).lastBlock = none ∧ reg.InBounds c.raw ∧
      ∀ p : GenericPtr, p.InBounds c₀.raw → p.InBounds c.raw := by
  refine ⟨?_, WfRewriter.createRegion_new_inBounds h,
    fun p hp => (WfRewriter.createRegion_genericPtr_mono (ptr := p) h).2 (.inl hp)⟩
  simp only [WfRewriter.createRegion] at h
  split at h
  · simp at h
  · rename_i ctx' reg' heq
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [RegionPtr.lastBlock!_createRegion heq]

/-- `createOpAt` is one `WfRewriter.createOp` with no insertion point or an insertion
at the end of a block. -/
theorem createOpAt_spec {ctx ctx' : WfIRContext OpCode} {oc : OpCode} {p : propertiesOf oc}
    {mb? : Option BlockPtr} {o : OperationPtr} (h : createOpAt ctx oc p mb? = some (ctx', o)) :
    ∃ ip, (ip = none ∨ ∃ mb, ip = some (InsertPoint.atEnd mb)) ∧ ∃ h₁ h₂ h₃ h₄,
      WfRewriter.createOp ctx oc #[] #[] #[] #[] p ip h₁ h₂ h₃ h₄ = some (ctx', o) := by
  cases mb? with
  | none => exact ⟨_, .inl rfl, _, _, _, _, h⟩
  | some mb =>
    obtain ⟨_, _, _, _, _, hc⟩ := createAtEnd_spec (h : createAtEnd _ _ _ _ _ _ = _)
    exact ⟨_, .inr ⟨mb, rfl⟩, _, _, _, _, hc⟩

/-- The operation `createRegionOp` creates is in bounds, has one region, the region it
returns, which is in bounds and holds no block; every pointer in bounds before is in
bounds after. -/
theorem createRegionOp_spec {ctx ctx' : WfIRContext OpCode} {oc : OpCode}
    {p : propertiesOf oc} {mb? : Option BlockPtr} {o : OperationPtr} {r : RegionPtr}
    (h : createRegionOp ctx oc p mb? = some (ctx', o, r)) :
    o.InBounds ctx'.raw ∧ o.getNumRegions! ctx'.raw = 1 ∧ o.getRegion! ctx'.raw 0 = r ∧
      (r.get! ctx'.raw).lastBlock = none ∧ r.InBounds ctx'.raw ∧
      ∀ q : GenericPtr, q.InBounds ctx.raw → q.InBounds ctx'.raw := by
  unfold createRegionOp at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ctx₁, reg⟩, h₁, ⟨ctx₂, o₂⟩, h₂, h⟩ := h
  obtain ⟨hl₁, hr₁, hm₁⟩ := createRegion_spec h₁
  have key : o₂.getNumRegions! ctx₂.raw = 0 ∧ (reg.get! ctx₂.raw).lastBlock = none ∧
      ∀ q : GenericPtr, q.InBounds ctx₁.raw → q.InBounds ctx₂.raw := by
    obtain ⟨ip, _, _, _, _, _, hc⟩ := createOpAt_spec h₂
    refine ⟨?_, ?_, fun q hq => WfRewriter.createOp_inBounds_mono hc hq⟩
    · rw [OperationPtr.getNumRegions!_WfRewriter_createOp hc]; simp
    · rw [RegionPtr.lastBlock!_WfRewriter_createOp hc]; exact hl₁
  split at h
  next hin =>
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hn0, hl₂, hm₂⟩ := key
    refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · exact (Rewriter.pushRegion_inBounds_mono (h₁ := hin.1) (h₂ := hin.2.1) (h₃ := hin.2.2)
        (.operation o₂)).2 hin.1
    · simp [WfRewriter.pushRegion, OperationPtr.getNumRegions!_pushRegion, hn0]
    · simp [WfRewriter.pushRegion, OperationPtr.getRegion!_pushRegion, hn0]
    · simp [WfRewriter.pushRegion, hl₂]
    · exact (Rewriter.pushRegion_inBounds_mono (h₁ := hin.1) (h₂ := hin.2.1) (h₃ := hin.2.2)
        (.region reg)).2 hin.2.1
    · simpa [WfRewriter.pushRegion] using hm₂ q (hm₁ q hq)
  next => simp at h

/-- The block `createBlockIn` creates satisfies `createBlock_atEnd_spec`, and every
operation in bounds before is in bounds after. -/
theorem createBlockIn_spec {ctx ctx' : WfIRContext OpCode} {types : Array TypeAttr}
    {reg : RegionPtr} {blk : BlockPtr} (h : createBlockIn ctx types reg = some (ctx', blk)) :
    ((Chain ctx' blk [] ∧ blk.getNumArguments! ctx'.raw = types.size ∧
      ∀ (i : Nat) (hi : i < types.size),
        (ValuePtr.blockArgument (blk.getArgument i)).getType! ctx'.raw = types[i] ∧
        (ValuePtr.blockArgument (blk.getArgument i)).InBounds ctx'.raw) ∧
    (∀ o : OperationPtr, o.getNumRegions! ctx'.raw = o.getNumRegions! ctx.raw) ∧
    (∀ (o : OperationPtr) (i : Nat), o.getRegion! ctx'.raw i = o.getRegion! ctx.raw i) ∧
    ((reg.get! ctx.raw).lastBlock = none → (reg.get! ctx'.raw).firstBlock = some blk)) ∧
    ∀ o : OperationPtr, o.InBounds ctx.raw → o.InBounds ctx'.raw := by
  unfold createBlockIn at h
  split at h
  next =>
    refine ⟨createBlock_atEnd_spec h, fun o ho => ?_⟩
    have := WfRewriter.createBlock_inBounds_mono (ptr := .operation o) h
    simpa using this ho
  next => simp at h

theorem Reach.numRegions {a b : WfIRContext OpCode} (h : Reach a b) {q : OperationPtr}
    (ho : q.InBounds a.raw) : q.getNumRegions! b.raw = q.getNumRegions! a.raw := by
  induction h with
  | refl => rfl
  | @step _ _ _ _ _ _ _ _ o' h _ ih =>
    have hne : q ≠ o' := fun he => createAtEnd_new_not_inBounds h (he ▸ ho)
    have ho' := createAtEnd_op_inBounds_mono h ho
    obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
    rw [ih ho', OperationPtr.getNumRegions!_WfRewriter_createOp h, if_neg hne]

theorem Reach.region {a b : WfIRContext OpCode} (h : Reach a b) (o : OperationPtr) (i : Nat) :
    o.getRegion! b.raw i = o.getRegion! a.raw i := by
  induction h with
  | refl => rfl
  | step h _ ih =>
    obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
    rw [ih, OperationPtr.getRegion!_WfRewriter_createOp h]
    simp

theorem Reach.firstBlock {a b : WfIRContext OpCode} (h : Reach a b) (r : RegionPtr) :
    (r.get! b.raw).firstBlock = (r.get! a.raw).firstBlock := by
  induction h with
  | refl => rfl
  | step h _ ih =>
    obtain ⟨_, _, _, _, _, h⟩ := createAtEnd_spec h
    rw [ih, RegionPtr.firstBlock!_WfRewriter_createOp h]

/-- An operation with one region `reg` whose first block is `blk`, run by
`interpretFunction` with arguments `vals` and memory `mem`, returns what
`interpretBlock` returns through a `return` action on `blk` from the empty variable
state with memory `mem`. -/
theorem interpretFunction_of_interpretBlock {C : WfIRContext OpCode} {fn : OperationPtr}
    {reg : RegionPtr} {blk : BlockPtr} (hf : fn.InBounds C.raw)
    (hn : fn.getNumRegions! C.raw = 1) (hr : fn.getRegion! C.raw 0 = reg)
    (hfb : (reg.get! C.raw).firstBlock = some blk) (hb : blk.InBounds C.raw)
    (vals : Array RuntimeValue) (mem : MemoryState) {S : InterpreterState C}
    {res : Array RuntimeValue}
    (hblock : interpretBlock blk vals ⟨.empty C, mem⟩ hb = .ok (S, .return res)) :
    interpretFunction fn vals mem hf = .ok (S.memory, res) := by
  have hn' : fn.getNumRegions C.raw hf = 1 := by
    rw [← OperationPtr.getNumRegions!_eq_getNumRegions hf]; exact hn
  unfold interpretFunction
  rw [dif_neg (by simp [hn'])]
  have key : ∀ (r : RegionPtr) (hri : r.InBounds C.raw), r = reg →
      interpretRegion r vals ⟨.empty C, mem⟩ hri = .ok (S, res) := by
    rintro r hri rfl
    have hfb' : (r.get C.raw hri).firstBlock = some blk := by
      rw [← RegionPtr.get!_eq_get hri]; exact hfb
    unfold interpretRegion
    split
    · rename_i hn; rw [hfb'] at hn; simp at hn
    rename_i b hb'
    rw [hfb', Option.some.injEq] at hb'
    subst hb'
    rw [interpretBlockCFG, hblock]
  simp only
  rw [key _ _ (by
    rw [← FunctionOpInterface.getFunctionBody!_eq_getFunctionBody]
    simpa [FunctionOpInterface.getFunctionBody!] using hr)]
  rfl

/-- The `func.func` that `lowerComToFuncWf` builds for a program of the `arith` fragment
over a context of integer types, run by VeIR's function-level interpreter
`interpretFunction` with the encoded valuation `V` as arguments and any memory `mem`,
returns the encoded denotation of the program and leaves the memory unchanged. -/
theorem interpretFunction_lowerComToFuncWf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (name : String) (V : Valuation Γ) (mem : MemoryState)
    (hc : ComInArith c) (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s)
    {C : WfIRContext OpCode} {modOp fn : OperationPtr} {blk : BlockPtr}
    {ops : List OperationPtr}
    (h : lowerComToFuncWf c name = some (C, modOp, fn, blk, ops)) :
    ∃ hf : fn.InBounds C.raw,
      interpretFunction fn (encodeArgs V).toArray mem hf =
        .ok (mem, #[encodeVal t (c.denote V)]) := by
  simp only [lowerComToFuncWf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨ctxM, modOp₀, mreg⟩, _, ⟨ctx₀, mb⟩, _, ⟨ctx₁, fn₁, reg⟩, h₁, ⟨ctx₂, blk₂⟩, h₂,
    ⟨ctx₃, ops₃, final⟩, h₃, ⟨ctx₄, ret⟩, h₄, rfl, rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨hf₁, hn₁, hreg₁, hlast₁, _, _⟩ := createRegionOp_spec h₁
  obtain ⟨⟨hblk, hnr, hrg, hfb⟩, hmono⟩ := createBlockIn_spec h₂
  have hf₂ := hmono _ hf₁
  have hvm : ∀ (s : JasminTy) (v : Var Γ s),
      (varMapOfBlockArgs blk₂ (Γ := Γ) s v).InBounds ctx₂.raw :=
    fun s v => (hblk.2.2 _
      (by simpa using CatCrypt.Crypto.SecureCompilation.VIR.varDepth_lt v)).2
  obtain ⟨_, _, _, _, hr₃⟩ := lowerComWf_spec h₃ hblk.1 hvm
  have hr : Reach ctx₂ ctx₄ := hr₃.trans (.step h₄ (.refl _))
  obtain ⟨hb, S, hmem, hS⟩ := interpretBlock_of_lowerComWf c V hc hΓ hblk h₃ h₄
    ⟨.empty _, mem⟩
  have := interpretFunction_of_interpretBlock (hr.op_inBounds hf₂)
    ((hr.numRegions hf₂).trans ((hnr fn₁).trans hn₁))
    ((hr.region fn₁ 0).trans ((hrg fn₁ 0).trans hreg₁))
    ((hr.firstBlock reg).trans (hfb hlast₁)) hb _ mem hS
  rw [hmem] at this
  exact ⟨_, this⟩

/-- On the `arith` fragment over a context of integer types, VeIR's
`interpretFunction` on the `func.func` that `lowerComToFuncWf` builds returns the value
`veirRunCom` computes from the encoded valuation, and leaves the memory unchanged. -/
theorem interpretFunction_lowerComToFuncWf_eq_veirRunCom {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (name : String) (V : Valuation Γ)
    (mem : MemoryState) (hc : ComInArith c) (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s)
    {C : WfIRContext OpCode} {modOp fn : OperationPtr} {blk : BlockPtr}
    {ops : List OperationPtr}
    (h : lowerComToFuncWf c name = some (C, modOp, fn, blk, ops)) :
    ∃ (hf : fn.InBounds C.raw) (r : RuntimeValue),
      veirRunCom c (fun s v => encodeVal s (v.lookup V)) mem = .ok r ∧
      interpretFunction fn (encodeArgs V).toArray mem hf = .ok (mem, #[r]) := by
  obtain ⟨hf, hS⟩ := interpretFunction_lowerComToFuncWf c name V mem hc hΓ h
  exact ⟨hf, _, veirRunCom_eq_denote c V _ mem hc (fun _ _ => rfl), hS⟩

/-! ## Totality of `lowerComToFuncWf`

Each allocation of VeIR (`OperationPtr.allocEmpty`, `BlockPtr.allocEmpty`,
`RegionPtr.allocEmpty`) takes the identifier `nextID` and fails when that pointer is
already in bounds. `IdsBelow` (every operation, block and region in bounds has an
identifier below `nextID`) holds of the empty context and is preserved by every step of
`lowerComToFuncWf` before the operations of the program, so every step succeeds. -/

/-- Every operation, block and region in bounds in `ctx` has an identifier below
`ctx.nextID`. -/
def IdsBelow (ctx : IRContext OpCode) : Prop :=
  OpsBelow ctx ∧ (∀ b : BlockPtr, b.InBounds ctx → b.id < ctx.nextID) ∧
    ∀ r : RegionPtr, r.InBounds ctx → r.id < ctx.nextID

theorem idsBelow_default : IdsBelow (default : WfIRContext OpCode).raw := by
  refine ⟨opsBelow_default, fun b hb => ?_, fun r hr => ?_⟩
  · simp [BlockPtr.InBounds, default, IRContext.empty] at hb
  · simp [RegionPtr.InBounds, default, IRContext.empty] at hr

theorem IdsBelow.of_step {c c' : IRContext OpCode} (hf : IdsBelow c)
    (hn : c.nextID ≤ c'.nextID)
    (hop : ∀ o : OperationPtr, o.InBounds c' → o.InBounds c ∨ o.id < c'.nextID)
    (hbl : ∀ b : BlockPtr, b.InBounds c' → b.InBounds c ∨ b.id < c'.nextID)
    (hrg : ∀ r : RegionPtr, r.InBounds c' → r.InBounds c ∨ r.id < c'.nextID) :
    IdsBelow c' := by
  refine ⟨fun o ho => ?_, fun b hb => ?_, fun r hr => ?_⟩
  · rcases hop o ho with h | h
    · exact Nat.lt_of_lt_of_le (hf.1 o h) hn
    · exact h
  · rcases hbl b hb with h | h
    · exact Nat.lt_of_lt_of_le (hf.2.1 b h) hn
    · exact h
  · rcases hrg r hr with h | h
    · exact Nat.lt_of_lt_of_le (hf.2.2 r h) hn
    · exact h

theorem createRegion_exists {c : WfIRContext OpCode} (hf : IdsBelow c.raw) :
    ∃ c' r, WfRewriter.createRegion c = some (c', r) ∧ IdsBelow c'.raw := by
  unfold WfRewriter.createRegion
  split
  · rename_i h
    exfalso
    unfold Rewriter.createRegion RegionPtr.allocEmpty at h
    have := hf.2.2 ⟨c.raw.nextID⟩
    grind [RegionPtr.InBounds]
  · rename_i c' r heq
    refine ⟨_, _, rfl, ?_⟩
    have hn : c'.nextID = c.raw.nextID + 1 ∧ r = ⟨c.raw.nextID⟩ := by
      unfold Rewriter.createRegion RegionPtr.allocEmpty at heq
      dsimp only at heq
      split at heq
      · simp at heq
      · simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨rfl, rfl⟩
    have hm := fun p => Rewriter.createRegion_genericPtr_mono p heq
    refine hf.of_step (show c.raw.nextID ≤ c'.nextID by omega) (fun o ho => .inl ?_)
      (fun b hb => .inl ?_) (fun q hq => ?_)
    · simpa using (hm (.operation o)).1 ho
    · simpa using (hm (.block b)).1 hb
    · rcases (hm (.region q)).1 hq with h | h
      · exact .inl h
      · simp only [GenericPtr.region.injEq] at h
        subst h; right; rw [hn.1, hn.2]; simp

theorem createOpAt_exists {ctx : WfIRContext OpCode} {oc : OpCode} {p : propertiesOf oc}
    {mb? : Option BlockPtr} (hf : IdsBelow ctx.raw)
    (hmb : ∀ mb, mb? = some mb → mb.InBounds ctx.raw) :
    ∃ ctx' o, createOpAt ctx oc p mb? = some (ctx', o) ∧ IdsBelow ctx'.raw := by
  have hfresh : ¬ (OperationPtr.mk ctx.raw.nextID).InBounds ctx.raw := fun hin =>
    Nat.lt_irrefl _ (hf.1 _ hin)
  have hraw : ∀ {ip : Option InsertPoint} {h₁ h₂ h₃ h₄ h₅} {c' : IRContext OpCode},
      Rewriter.createOp ctx.raw oc #[] #[] #[] #[] p ip h₁ h₂ h₃ h₄ h₅ =
        some (c', ⟨ctx.raw.nextID⟩) → c'.nextID = ctx.raw.nextID + 1 → IdsBelow c' := by
    intro ip _ _ _ _ _ c' hc hn
    refine hf.of_step (by omega) (fun q hq => ?_) (fun b hb => .inl ?_) (fun r hr => .inl ?_)
    · have := (Rewriter.createOp_inBounds (.operation q) hc).1 (by simpa using hq)
      simp only [GenericPtr.operation.injEq] at this
      rcases this with h | rfl
      · exact .inl (by simpa using h)
      · right; simp [hn]
    · simpa using (Rewriter.createOp_inBounds (.block b) hc).1 (by simpa using hb)
    · simpa using (Rewriter.createOp_inBounds (.region r) hc).1 (by simpa using hr)
  have hwf : ∀ {ip : Option InsertPoint} {h₁ h₂ h₃ h₄},
      (ip = none ∨ ∃ b, ip = some (InsertPoint.atEnd b)) →
      ∃ ctx', WfRewriter.createOp ctx oc #[] #[] #[] #[] p ip h₁ h₂ h₃ h₄ =
        some (ctx', ⟨ctx.raw.nextID⟩) ∧ IdsBelow ctx'.raw := by
    intro ip h₁ h₂ h₃ h₄ hip
    obtain ⟨c', hc, hn⟩ : ∃ c', Rewriter.createOp ctx.raw oc #[] #[] #[] #[] p ip h₁ h₂ h₃ h₄
        (by grind) = some (c', ⟨ctx.raw.nextID⟩) ∧ c'.nextID = ctx.raw.nextID + 1 := by
      rcases hip with rfl | ⟨b, rfl⟩
      · exact createOp_none_exists (Dialect := OpCode) _ _ _ _ _ hfresh
      · exact createOp_atEnd_exists (Dialect := OpCode) _ _ _ _ _ hfresh
    unfold WfRewriter.createOp
    split
    · rename_i h; rw [hc] at h; simp at h
    · rename_i c o h
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hraw hc hn⟩
  cases mb? with
  | none =>
    obtain ⟨ctx', hc, hi⟩ := hwf (ip := none) (h₁ := by simp) (h₂ := by simp) (h₃ := by simp)
      (h₄ := by simp [Option.maybe_none]) (.inl rfl)
    exact ⟨ctx', _, hc, hi⟩
  | some mb =>
    have hb := hmb mb rfl
    unfold createOpAt createAtEnd
    dsimp only
    rw [dif_pos (fun v hv => by simp at hv), dif_pos hb]
    obtain ⟨ctx', hc, hi⟩ := hwf (.inr ⟨mb, rfl⟩)
    exact ⟨ctx', _, hc, hi⟩

theorem createRegion_parent {c₀ c : WfIRContext OpCode} {reg : RegionPtr}
    (h : WfRewriter.createRegion c₀ = some (c, reg)) : (reg.get! c.raw).parent = none := by
  simp only [WfRewriter.createRegion] at h
  split at h
  · simp at h
  · rename_i ctx' reg' heq
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [RegionPtr.parent!_createRegion heq]

theorem createRegionOp_exists {ctx : WfIRContext OpCode} {oc : OpCode} {p : propertiesOf oc}
    {mb? : Option BlockPtr} (hf : IdsBelow ctx.raw)
    (hmb : ∀ mb, mb? = some mb → mb.InBounds ctx.raw) :
    ∃ ctx' o r, createRegionOp ctx oc p mb? = some (ctx', o, r) ∧ IdsBelow ctx'.raw := by
  obtain ⟨ctx₁, reg, h₁, hf₁⟩ := createRegion_exists hf
  obtain ⟨_, hr₁, hm₁⟩ := createRegion_spec h₁
  obtain ⟨ctx₂, o, h₂, hf₂⟩ := createOpAt_exists (oc := oc) (p := p) (mb? := mb?) hf₁
    (fun mb hm => hm₁ (.block mb) (hmb mb hm))
  obtain ⟨ip, _, _, _, _, _, hc⟩ := createOpAt_spec h₂
  have hin : o.InBounds ctx₂.raw ∧ reg.InBounds ctx₂.raw ∧
      (reg.get! ctx₂.raw).parent = none := by
    refine ⟨WfRewriter.createOp_new_inBounds _ hc,
      WfRewriter.createOp_inBounds_mono (ptr := .region reg) hc hr₁, ?_⟩
    rw [RegionPtr.parent!_WfRewriter_createOp hc]
    simpa using createRegion_parent h₁
  refine ⟨WfRewriter.pushRegion ctx₂ o reg hin.1 hin.2.1 hin.2.2, o, reg, ?_, ?_⟩
  · simp only [createRegionOp, h₁, h₂, Option.bind_eq_bind, Option.bind_some, dif_pos hin,
      Option.pure_def]
  · have hn : (Rewriter.pushRegion ctx₂.raw o reg hin.1 hin.2.1 hin.2.2).nextID =
        ctx₂.raw.nextID := rfl
    have hm := fun q => Rewriter.pushRegion_inBounds_mono (h₁ := hin.1) (h₂ := hin.2.1)
      (h₃ := hin.2.2) q
    refine hf₂.of_step (show _ ≤ (Rewriter.pushRegion ctx₂.raw o reg _ _ _).nextID by omega)
      (fun q hq => .inl ((hm (.operation q)).1 hq)) (fun b hb => .inl ((hm (.block b)).1 hb))
      (fun r hr => .inl ((hm (.region r)).1 hr))

theorem initBlockArguments_nextID {c : IRContext OpCode} {blk : BlockPtr}
    {types : Array TypeAttr} {i : Nat} {h₁ h₂} :
    (Rewriter.initBlockArguments c blk types i h₁ h₂).nextID = c.nextID := by
  fun_induction Rewriter.initBlockArguments
  · rfl
  · rename_i ih
    rw [ih]
    show (Rewriter.pushBlockArgument _ _ _ _).nextID = _
    unfold Rewriter.pushBlockArgument BlockPtr.pushArgument BlockPtr.setArguments
    rfl

theorem BlockPtr.linkBetween_nextID {c : IRContext OpCode} (b : BlockPtr) (p n) (h₁ h₂ h₃) :
    (b.linkBetween c p n h₁ h₂ h₃).nextID = c.nextID := by
  unfold BlockPtr.linkBetween
  dsimp only
  split <;> split <;> rfl

/-- Inserting a block without a parent at the end of a region succeeds and keeps
`nextID`. -/
theorem insertBlock_atEnd_exists {c : IRContext OpCode} {blk : BlockPtr} {reg : RegionPtr}
    {h₁ h₂ h₃} (hpar : (blk.get! c).parent = none) :
    ∃ c', Rewriter.insertBlock c blk (.atEnd reg) h₁ h₂ h₃ = some c' ∧
      c'.nextID = c.nextID := by
  unfold Rewriter.insertBlock BlockPtr.linkBetweenWithParent
  split
  · rename_i h; simp [BlockInsertPoint.region] at h
  rename_i parent hb
  dsimp only
  split
  · rename_i h
    exfalso
    unfold BlockPtr.setParentWithCheck at h
    split at h
    · rename_i p hp
      rw [← BlockPtr.get!_eq_get] at hp
      grind
    · simp at h
  rename_i c₂ h₂
  have hc₂ : c₂.nextID = c.nextID := by
    unfold BlockPtr.setParentWithCheck at h₂
    split at h₂
    · simp at h₂
    · cases h₂
      exact BlockPtr.linkBetween_nextID blk _ _ _ _ _
  split <;> split <;> exact ⟨_, rfl, hc₂⟩

theorem blockAllocEmpty_eq {c c' : IRContext OpCode} {b : BlockPtr}
    (h : BlockPtr.allocEmpty c = some (c', b)) :
    b = ⟨c.nextID⟩ ∧ c'.nextID = c.nextID + 1 := by
  unfold BlockPtr.allocEmpty at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem createBlockIn_exists {ctx : WfIRContext OpCode} {types : Array TypeAttr}
    {reg : RegionPtr} (hf : IdsBelow ctx.raw) (hr : reg.InBounds ctx.raw) :
    ∃ ctx' blk, createBlockIn ctx types reg = some (ctx', blk) ∧ IdsBelow ctx'.raw := by
  have hraw : ∀ {hx hip}, ∃ c' b, Rewriter.createBlock ctx.raw types (some (.atEnd reg)) hx hip =
      some (c', b) ∧ c'.nextID = ctx.raw.nextID + 1 ∧ b = ⟨ctx.raw.nextID⟩ := by
    intro hx hip
    unfold Rewriter.createBlock
    split
    · rename_i h
      exfalso
      unfold BlockPtr.allocEmpty at h
      have := hf.2.1 ⟨ctx.raw.nextID⟩
      grind [BlockPtr.InBounds]
    rename_i c₁ b₁ halloc
    dsimp only
    have hpar : (b₁.get! (Rewriter.initBlockArguments c₁ b₁ types 0 (by grind) (by grind))).parent
        = none := by
      rw [BlockPtr.parent!_initBlockArguments, BlockPtr.get!_BlockPtr_allocEmpty halloc]
      simp [Block.empty]
    obtain ⟨c₂, hc₂, hn₂⟩ := insertBlock_atEnd_exists (reg := reg) (h₁ := by grind)
      (h₂ := by grind) (h₃ := by grind) hpar
    obtain ⟨hb₁, hn₁⟩ := blockAllocEmpty_eq halloc
    refine ⟨c₂, b₁, by simp [hc₂], ?_, hb₁⟩
    rw [hn₂, initBlockArguments_nextID, hn₁]
  unfold createBlockIn
  rw [dif_pos hr]
  unfold WfRewriter.createBlock
  split
  · rename_i h
    obtain ⟨c', b, hc, _⟩ := hraw (hx := by grind)
      (hip := by simpa [Option.maybe_some, BlockInsertPoint.inBounds_atEnd] using hr)
    rw [hc] at h; simp at h
  · rename_i c b h
    obtain ⟨c', b', hc, hn, hb'⟩ := hraw (hx := by grind)
      (hip := by simpa [Option.maybe_some, BlockInsertPoint.inBounds_atEnd] using hr)
    rw [hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, _, rfl, hf.of_step (show _ ≤ c'.nextID by omega) (fun q hq => .inl ?_)
      (fun q hq => ?_) (fun q hq => .inl ?_)⟩
    · simpa using (Rewriter.createBlock_inBounds (.operation q) hc).1 hq
    · have := (Rewriter.createBlock_inBounds (.block q) hc).1 hq
      simp only [GenericPtr.block.injEq, reduceCtorEq, or_false] at this
      rcases this with h | rfl
      · exact .inl h
      · right; show q.id < c'.nextID; simp [hb', hn]
    · simpa using (Rewriter.createBlock_inBounds (.region q) hc).1 hq

/-- `lowerComToFuncWf` returns a context for every program of `jasminDialect`. -/
theorem lowerComToFuncWf_isSome {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (name : String) :
    ∃ C modOp fn blk ops, lowerComToFuncWf c name = some (C, modOp, fn, blk, ops) := by
  obtain ⟨ctxM, modOp, mreg, hM, hfM⟩ := createRegionOp_exists (oc := .builtin .module)
    (p := default) (mb? := none) idsBelow_default (by simp)
  obtain ⟨_, _, _, _, hmreg, _⟩ := createRegionOp_spec hM
  obtain ⟨ctx₀, mb, h₀, hf₀⟩ := createBlockIn_exists (types := #[]) hfM hmreg
  have hmb : mb.InBounds ctx₀.raw := (createBlockIn_spec h₀).1.1.1.blkIn
  obtain ⟨ctx₁, fn, reg, h₁, hf₁⟩ := createRegionOp_exists (oc := .func .func)
    (p := funcPropsWf Γ t name) (mb? := some mb) hf₀
    (fun mb' hm => by simp only [Option.some.injEq] at hm; exact hm ▸ hmb)
  obtain ⟨_, _, _, _, hreg, _⟩ := createRegionOp_spec h₁
  obtain ⟨ctx₂, blk, h₂, hf₂⟩ := createBlockIn_exists
    (types := (Γ.map JasminTy.toVeirTy).toArray) hf₁ hreg
  obtain ⟨⟨hchain, _, htypes⟩, _⟩ := (createBlockIn_spec h₂).1
  have hvm : ∀ (s : JasminTy) (v : Var Γ s),
      (varMapOfBlockArgs blk (Γ := Γ) s v).InBounds ctx₂.raw :=
    fun s v => (htypes _ (by simpa using CatCrypt.Crypto.SecureCompilation.VIR.varDepth_lt v)).2
  obtain ⟨ctx₃, ops, final, h₃, hf₃⟩ := lowerComWf_exists c hf₂.1 hchain hvm
  obtain ⟨hc₃, _, _, hfinal, _⟩ := lowerComWf_spec h₃ hchain hvm
  obtain ⟨ctx₄, ret, h₄, _⟩ := createAtEnd_exists (oc := .func .return) (p := default)
    (rt := #[]) (xs := #[final]) (by simpa using hfinal) hc₃.blkIn hf₃
  exact ⟨ctx₄, modOp, fn, blk, ops ++ [ret], by
    simp only [lowerComToFuncWf, hM, h₀, h₁, h₂, h₃, h₄, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]⟩

/-- On the `arith` fragment over a context of integer types, `lowerComToFuncWf` returns
a well-formed context, and VeIR's `interpretFunction` on its `func.func`, with the
encoded valuation `V` as arguments and any memory `mem`, returns the encoded
denotation of the program and leaves the memory unchanged. -/
theorem exists_interpretFunction_lowerComToFuncWf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (name : String) (V : Valuation Γ) (mem : MemoryState)
    (hc : ComInArith c) (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s) :
    ∃ C modOp fn blk ops, lowerComToFuncWf c name = some (C, modOp, fn, blk, ops) ∧
      ∃ hf : fn.InBounds C.raw,
        interpretFunction fn (encodeArgs V).toArray mem hf =
          .ok (mem, #[encodeVal t (c.denote V)]) := by
  obtain ⟨C, modOp, fn, blk, ops, h⟩ := lowerComToFuncWf_isSome c name
  exact ⟨C, modOp, fn, blk, ops, h, interpretFunction_lowerComToFuncWf c name V mem hc hΓ h⟩

/-- On the `arith` fragment over a context of integer types, `lowerComToFuncWf` returns
a well-formed context, and VeIR's `interpretFunction` on its `func.func` returns the
value `veirRunCom` computes from the encoded valuation and leaves the memory
unchanged. -/
theorem exists_interpretFunction_lowerComToFuncWf_eq_veirRunCom {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (name : String) (V : Valuation Γ)
    (mem : MemoryState) (hc : ComInArith c) (hΓ : ∀ s ∈ Γ, JasminTy.IsScalar s) :
    ∃ C modOp fn blk ops, lowerComToFuncWf c name = some (C, modOp, fn, blk, ops) ∧
      ∃ (hf : fn.InBounds C.raw) (r : RuntimeValue),
        veirRunCom c (fun s v => encodeVal s (v.lookup V)) mem = .ok r ∧
        interpretFunction fn (encodeArgs V).toArray mem hf = .ok (mem, #[r]) := by
  obtain ⟨C, modOp, fn, blk, ops, h⟩ := lowerComToFuncWf_isSome c name
  exact ⟨C, modOp, fn, blk, ops, h,
    interpretFunction_lowerComToFuncWf_eq_veirRunCom c name V mem hc hΓ h⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
