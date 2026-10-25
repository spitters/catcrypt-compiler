/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComVarDepth
public import CatCrypt.Crypto.SecureCompilation.VIR.ComVarDepth
public import Veir.IR.Basic
public import Veir.IR.OpInfo
public import Veir.IR.Attribute
public import Veir.Rewriter.WfRewriter

/-!
# Path (b): `Com → Veir.WfIRContext` lowering

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A lowering from CatCrypt's typed-SSA VIR (`Com d Γ t`) to Veir's pointer graph,
built through VeIR's well-formedness-preserving builder `WfRewriter`, so every
context it produces is a `Veir.WfIRContext`.

## Approach

The lowering is parameterised by two typeclasses:

* `ToVeirOp d` maps each VIR op (`d.Op`) to a Veir op-code of the op-info type
  `ToVeirOp.Op` with its properties, discardable attributes (`attrsOf`) and result
  slot, or, through `expand?`, to a sequence of operations (`VeirExpansion`).
* `ToVeirTy d` maps each VIR type (`d.Ty`) to a Veir `TypeAttr`.

The builder:

* `createAtEnd`, `emitStepsWf`: create operations at the end of a block through
  `WfRewriter.createOp`.
* `lowerComWfWith bx toTy`: the operations of a program, per binding the steps of the
  expansion `bx o nargs`; `veirExpansionOf` is the expansion a `ToVeirOp` instance
  gives.
* `setAttrsWf`: sets the discardable attributes of the operations through
  `WfRewriter.setAttributes`.
* `lowerComToFuncAtWf`, `lowerComToModuleWf`: a `func.func` whose one block holds the
  context `Γ` as block arguments, the operations of the program and a return
  terminator, inside a `builtin.module` that first holds one private `func.func`
  declaration per extern.

The entry points `lowerClosedCom`, `lowerClosedComToFunc` and
`lowerClosedComToModuleWithExterns` return the raw context of the builder's output;
`lowerClosedComToModuleWithExterns_wellFormed` and its siblings state that it is well
formed. `ComToVeirWf.lean` proves, for `jasminDialect`, what VeIR's interpreter
computes on the built `func.func`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)

/-! ## 1. Variable map -/

-- We work with `Type 0` dialects because Veir's `IRContext`, `OpResultPtr`,
-- etc., live in `Type 0`. All real CatCrypt dialects (`CatCryptOp`, `CryptoTy`)
-- are in `Type 0` already, so this is no restriction in practice.

variable {d : Dialect.{0, 0}} [DialectSignature d]

/-- A Veir op-info bundle: an op-code with its `HasOpInfo` instance. The
    instance is bundled rather than passed as a separate parameter so it
    can ride along with the choice of `O` from a `ToVeirOp` lookup. -/
structure VeirOpInfoBundle where
  /-- The Veir op-code type. -/
  O : Type
  /-- The `HasOpInfo` instance for `O`. -/
  [hasOpInfo : Veir.HasOpInfo O]

attribute [instance] VeirOpInfoBundle.hasOpInfo

/--
A map from VIR variables (typed De Bruijn indices) to Veir
SSA-value pointers (`ValuePtr`).

`ValuePtr` is the right level: a variable can be either an
operation result (the common case — bound by `Com.var`) or a block
argument (when the enclosing context `Γ` is materialised as block
arguments of a `func.func`-style entry block; see
`varMapOfBlockArgs`).
-/
abbrev VarMap (Γ : Ctxt d) : Type :=
  ∀ (t : d.Ty), Var Γ t → Veir.ValuePtr

namespace VarMap

/-- Empty variable map (for `Γ = []`). The body is vacuous because
    `Var [] t` has no inhabitants. -/
def empty : VarMap (d := d) [] :=
  fun _ v => by cases v

/-- Extend a variable map with a new binding `here ↦ ptr`, shifting
    all existing entries by `.there`. -/
def extend {Γ : Ctxt d} {t : d.Ty} (vm : VarMap Γ) (ptr : Veir.ValuePtr) :
    VarMap (t :: Γ) :=
  fun s v => by
    cases v with
    | here => exact ptr
    | there v' => exact vm s v'

end VarMap

/-! ## 2. Op-code and type mapping (typeclasses) -/

/-- An operand of one operation of an expansion: argument `i` of the binding, or
    result `slot` of the earlier operation `j` of the same expansion. -/
inductive VeirSrc where
  /-- Argument `i` of the binding. -/
  | arg (i : Nat)
  /-- Result `slot` of operation `j` of the expansion. -/
  | res (j slot : Nat)
  deriving Inhabited, Repr, DecidableEq

/-- One operation of an expansion: its op-code and properties, its discardable
    attributes, its operands, and its result types (`none` is the binding's type). -/
structure VeirExpandStep (O : Type) [Veir.HasOpInfo O] where
  /-- The op-code. -/
  op : O
  /-- The properties of the op-code. -/
  props : Veir.propertiesOf op
  /-- The discardable attributes. -/
  attrs : Array (ByteArray × Veir.Attribute) := #[]
  /-- The operands, in order. -/
  operands : List VeirSrc
  /-- The result types, in order; `none` is the type of the binding. -/
  results : List (Option Veir.TypeAttr)

/-- The lowering of one binding as the operations `steps`, emitted in order, and
    the operand `value` that the binding denotes. With no steps and
    `value = .arg 0` the binding is an alias of its first argument. -/
structure VeirExpansion (O : Type) [Veir.HasOpInfo O] where
  /-- The operations, in emission order. -/
  steps : List (VeirExpandStep O)
  /-- The value of the binding. -/
  value : VeirSrc

/-- A mapping from a VIR dialect to a Veir op-info enum. Each VIR op
    becomes a Veir op-code with its default properties, or, when `expand?`
    gives an expansion, the operations of that expansion.

    Optionally an op can carry a per-instance attribute dictionary
    (e.g. `callee = @fp_add` for an external-call op). The default
    `attrsOf` returns `#[]`. -/
class ToVeirOp (d : Dialect) [DialectSignature d] where
  /-- The Veir op-info type for this dialect. -/
  Op : Type
  /-- The `HasOpInfo` instance for `Op`. -/
  hasOpInfo : Veir.HasOpInfo Op
  /-- Map a VIR op to a Veir op-code. -/
  toOp : d.Op → Op
  /-- Default properties for a given Veir op-code. Implementations
      typically just return `default` (since `propertiesOf` is
      `Inhabited` for any concrete dialect). -/
  defaultProps (o : d.Op) :
    @Veir.propertiesOf Op hasOpInfo.toIsOpCode (toOp o)
  /-- Per-op attribute payload (key → attribute). Default: no attrs. -/
  attrsOf (o : d.Op) : Array (ByteArray × Veir.Attribute) := #[]
  /-- The number of results of the op's Veir operation, all of the binding's type,
      and the index of the result that carries the binding's value. Default: one
      result. -/
  resultSlot (o : d.Op) : Nat × Nat := (1, 0)
  /-- The lowering of the op as a sequence of operations, when it is not one
      operation. Default: every op is one operation. -/
  expand? (o : d.Op) : Option (@VeirExpansion Op hasOpInfo) := none

attribute [reducible, instance] ToVeirOp.hasOpInfo

/-- A mapping from VIR types to Veir `TypeAttr`. Used to populate the
    `type` field of `OpResult`s and `BlockArgument`s. -/
class ToVeirTy (d : Dialect) where
  /-- Map a VIR type to a Veir `TypeAttr`. -/
  toTy : d.Ty → Veir.TypeAttr

/-- Default trivial mapping: every VIR type lowers to `default :
    TypeAttr`. Useful as a starting point; a real dialect should
    override with an `instance` that returns appropriate Veir types
    (e.g. `IntegerType`, `FunctionType`). -/
@[reducible] def ToVeirTy.trivial (d : Dialect) : ToVeirTy d where
  toTy _ := default

/-! ## 3. Operands, block arguments and expansions -/

/-- The value pointers of the arguments of a binding, in order. -/
def argPtrs {Γ : Ctxt d} (vm : VarMap Γ) :
    {tys : List d.Ty} → HVector (fun ty => Var Γ ty) tys → List Veir.ValuePtr
  | [], .nil => []
  | _ :: _, .cons v rest => vm _ v :: argPtrs vm rest

/-- The value pointer an operand of an expansion denotes, given the binding's
    arguments `args` and the results `done` of the operations emitted so far. -/
def VeirSrc.resolve (args : List Veir.ValuePtr) (done : List (List Veir.OpResultPtr)) :
    VeirSrc → Veir.ValuePtr
  | .arg i => args.getD i default
  | .res j slot =>
      match done[j]?.bind (·[slot]?) with
      | some r => .opResult r
      | none => default

/-- Resolve a De Bruijn `Var Γ t` to a Veir `BlockArgumentPtr`. The
    convention matches CatCrypt's in-tree printer
    (`Print.printModuleArgs` + `PrintEnv.get`): block-arg index =
    De Bruijn depth, i.e. `.here ↦ arg 0`, `.there .here ↦ arg 1`,
    `.there (.there .here) ↦ arg 2`, … . The block arguments are the
    entries of `Γ` head first (so the head of `Γ` is arg 0). -/
def varToBlockArg (blk : Veir.BlockPtr) {Γ : Ctxt d} {t : d.Ty}
    (v : Var Γ t) : Veir.BlockArgumentPtr :=
  blk.getArgument (varDepth v)

/-- Build a `VarMap` whose entries are the block arguments of `blk`,
    indexed by De Bruijn depth (`.here ↦ arg 0`). -/
def varMapOfBlockArgs {Γ : Ctxt d} (blk : Veir.BlockPtr) :
    VarMap Γ :=
  fun _ v => Veir.ValuePtr.blockArgument (varToBlockArg blk v)

/-- The operations the lowering emits for a binding with op `o` and `nargs`
    arguments under a `ToVeirOp` instance: the expansion `ToVeirOp.expand? o`, or one
    operation with op-code `toOp o`, properties `defaultProps o`, attributes
    `attrsOf o`, the arguments as operands and `max n 1` results of the binding's
    type, whose value is the result in the slot `resultSlot o` names. -/
def veirExpansionOf [ToVeirOp d] (o : d.Op) (nargs : Nat) :
    VeirExpansion (ToVeirOp.Op (d := d)) :=
  match ToVeirOp.expand? (d := d) o with
  | some x => x
  | none =>
      { steps := [{ op := ToVeirOp.toOp o, props := ToVeirOp.defaultProps o,
                    attrs := ToVeirOp.attrsOf o,
                    operands := (List.range nargs).map VeirSrc.arg,
                    results := List.replicate (max (ToVeirOp.resultSlot o).1 1) none }],
        value := .res 0 (ToVeirOp.resultSlot o).2 }

/-! ## 4. The well-formed builder -/

section WfBuilder

variable {O : Type} [Veir.HasOpInfo O]

/-- Create an operation with op-code `op`, properties `props`, result types `resTys`
and operands `operands` at the end of the block `blk`, through
`WfRewriter.createOp`; `none` when an operand or the block is not in bounds. -/
def createAtEnd (ctx : Veir.WfIRContext O) (blk : Veir.BlockPtr) (op : O)
    (props : Veir.propertiesOf op) (resTys : Array Veir.TypeAttr)
    (operands : Array Veir.ValuePtr) : Option (Veir.WfIRContext O × Veir.OperationPtr) :=
  if hoper : ∀ v ∈ operands, v.InBounds ctx.raw then
    if hblk : blk.InBounds ctx.raw then
      Veir.WfRewriter.createOp ctx op resTys operands #[] #[] props (some (.atEnd blk)) hoper
        (by simp) (by simp) (by simpa [Option.maybe_some] using hblk)
    else none
  else none

/-- The result types of the step `s`, with `none` read as `resTy`. -/
def stepResTys (resTy : Veir.TypeAttr) (s : VeirExpandStep O) : Array Veir.TypeAttr :=
  (s.results.map (·.getD resTy)).toArray

/-- The result pointers of `op` with indices below `n`. -/
def resultPtrs (op : Veir.OperationPtr) (n : Nat) : List Veir.OpResultPtr :=
  (List.range n).map op.getResult

/-- Emit the steps of an expansion at the end of `blk`, in order, each reading its
operands through `VeirSrc.resolve`; returns the context, the operations and the
results of every operation emitted so far. -/
def emitStepsWf (blk : Veir.BlockPtr) (args : List Veir.ValuePtr) (resTy : Veir.TypeAttr) :
    List (VeirExpandStep O) → List (List Veir.OpResultPtr) → Veir.WfIRContext O →
    Option (Veir.WfIRContext O × List Veir.OperationPtr × List (List Veir.OpResultPtr))
  | [], done, ctx => some (ctx, [], done)
  | s :: rest, done, ctx => do
      let (ctx', op) ← createAtEnd ctx blk s.op s.props (stepResTys resTy s)
        (s.operands.map (VeirSrc.resolve args done)).toArray
      let (ctx'', ops, done') ←
        emitStepsWf blk args resTy rest (done ++ [resultPtrs op (stepResTys resTy s).size]) ctx'
      pure (ctx'', op :: ops, done')

/-- Lower a `Com` at the end of `blk`: each binding with op `o` and `n` arguments emits
the steps of the expansion `bx o n` (result types defaulting to `toTy` of the binding's
type) and binds the value of the expansion, which must be in bounds. Returns the
context, the operations in order, and the value of the program. -/
def lowerComWfWith (bx : d.Op → Nat → VeirExpansion O) (toTy : d.Ty → Veir.TypeAttr)
    (blk : Veir.BlockPtr) : {Γ : Ctxt d} → {t : d.Ty} →
    VarMap Γ → Com d Γ t → Veir.WfIRContext O →
    Option (Veir.WfIRContext O × List Veir.OperationPtr × Veir.ValuePtr)
  | _, _, vm, .ret v, ctx => some (ctx, [], vm _ v)
  | _, _, vm, .var (t := tEx) e body, ctx => do
      let args := argPtrs vm e.args
      let x := bx e.op args.length
      let (ctx1, ops1, done) ← emitStepsWf blk args (toTy tEx) x.steps [] ctx
      let val := x.value.resolve args done
      if val.InBounds ctx1.raw then
        let (ctx2, ops2, final) ← lowerComWfWith bx toTy blk (vm.extend (t := tEx) val) body ctx1
        pure (ctx2, ops1 ++ ops2, final)
      else none

/-- The discardable attributes of the operations `lowerComWfWith bx` emits for a
program, in emission order. -/
def Com.veirStepAttrs (bx : d.Op → Nat → VeirExpansion O) :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → List (Array (ByteArray × Veir.Attribute))
  | _, _, .ret _ => []
  | _, _, .var e body =>
      (bx e.op (DialectSignature.sig e.op).length).steps.map (·.attrs) ++
        Com.veirStepAttrs bx body

/-- Set the discardable attributes of each listed operation whose attribute array is
not empty, through `WfRewriter.setAttributes`; an operation out of bounds is skipped. -/
def setAttrsWf :
    List (Veir.OperationPtr × Array (ByteArray × Veir.Attribute)) →
    Veir.WfIRContext O → Veir.WfIRContext O
  | [], ctx => ctx
  | (op, attrs) :: rest, ctx =>
      if h : attrs.isEmpty = false ∧ op.InBounds ctx.raw then
        setAttrsWf rest
          (Veir.WfRewriter.setAttributes ctx op (Veir.DictionaryAttr.fromArray attrs) h.2)
      else setAttrsWf rest ctx

/-- Create an operation with op-code `oc`, properties `p` and no operands, results,
successors or regions, through `WfRewriter.createOp`: at the end of the block `mb` for
`some mb` (`createAtEnd`), detached for `none`. -/
def createOpAt (ctx : Veir.WfIRContext O) (oc : O) (p : Veir.propertiesOf oc) :
    Option Veir.BlockPtr → Option (Veir.WfIRContext O × Veir.OperationPtr)
  | none => Veir.WfRewriter.createOp ctx oc #[] #[] #[] #[] p none (by simp) (by simp)
      (by simp) (by simp [Option.maybe_none])
  | some mb => createAtEnd ctx mb oc p #[] #[]

/-- Create a region and an operation with op-code `oc`, properties `p` and no operands,
results, successors or regions, through `WfRewriter`, and push the region onto the
operation (`WfRewriter.pushRegion`); the operation is inserted at the end of the block
`mb?` when it is `some`, and left detached when it is `none`. Returns the context, the
operation and the region. -/
def createRegionOp (ctx : Veir.WfIRContext O) (oc : O) (p : Veir.propertiesOf oc)
    (mb? : Option Veir.BlockPtr) :
    Option (Veir.WfIRContext O × Veir.OperationPtr × Veir.RegionPtr) := do
  let (ctx₁, reg) ← Veir.WfRewriter.createRegion ctx
  let (ctx₂, o) ← createOpAt ctx₁ oc p mb?
  if h : o.InBounds ctx₂.raw ∧ reg.InBounds ctx₂.raw ∧ reg.getParent! ctx₂.raw = none then
    pure (Veir.WfRewriter.pushRegion ctx₂ o reg h.1 h.2.1 h.2.2, o, reg)
  else none

/-- Create a block with arguments of types `types` at the end of the region `reg`,
through `WfRewriter.createBlock`; `none` when `reg` is not in bounds. -/
def createBlockIn (ctx : Veir.WfIRContext O) (types : Array Veir.TypeAttr)
    (reg : Veir.RegionPtr) : Option (Veir.WfIRContext O × Veir.BlockPtr) :=
  if hreg : reg.InBounds ctx.raw then
    Veir.WfRewriter.createBlock ctx types (some (.atEnd reg))
      (by simpa [Option.maybe_some, Veir.BlockInsertPoint.inBounds_atEnd] using hreg)
  else none

/-- The function type with inputs `toTy s` for the entries `s` of `argTys` and the
output `toTy retTy`. -/
def funcTypeWith (toTy : d.Ty → Veir.TypeAttr) (argTys : List d.Ty) (retTy : d.Ty) :
    Veir.FunctionType :=
  { inputs := (argTys.map fun s => (toTy s).val).toArray, outputs := #[(toTy retTy).val] }

/-- The inherent attributes `{sym_visibility = "private"}` of an extern declaration. -/
def externVisibility : Veir.DictionaryAttr :=
  Veir.DictionaryAttr.fromArray
    #[("sym_visibility".toUTF8, Veir.Attribute.stringAttr ⟨"private".toUTF8⟩)]

/-- Create, at the end of the block `mb` and in order, one `func.func` declaration with
an empty body region per extern `(name, argTys, retTy)`, with the properties
`mkFuncProps name (funcTypeWith toTy argTys retTy) externVisibility`. -/
def createExternsWf (funcOp : O)
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (toTy : d.Ty → Veir.TypeAttr) (mb : Veir.BlockPtr) :
    List (String × List d.Ty × d.Ty) → Veir.WfIRContext O → Option (Veir.WfIRContext O)
  | [], ctx => some ctx
  | (name, argTys, retTy) :: rest, ctx => do
      let (ctx', _, _) ← createRegionOp ctx funcOp
        (mkFuncProps name (funcTypeWith toTy argTys retTy) externVisibility) (some mb)
      createExternsWf funcOp mkFuncProps toTy mb rest ctx'

/-- Lower a `Com d Γ t` into a `func.func` named `name` created in `ctx` (at the end of
the block `mb?` when it is `some`, detached when it is `none`): a `func.func` with
properties `mkFuncProps name (funcTypeWith toTy Γ t) default` and one region holding
one block, whose arguments are the entries of `Γ` (argument `i` is the variable of De
Bruijn depth `i`), followed by the operations of `lowerComWfWith bx toTy` and a return
terminator `returnOp` of the program's value; the attributes of the operations are
then set by `setAttrsWf`. Returns the context, the `func.func`, the block, its
operations in order and the value of the program. -/
def lowerComToFuncAtWf (bx : d.Op → Nat → VeirExpansion O) (toTy : d.Ty → Veir.TypeAttr)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (funcOp : O)
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (returnOp : O) (returnProps : Veir.propertiesOf returnOp) (name : String)
    (ctx : Veir.WfIRContext O) (mb? : Option Veir.BlockPtr) :
    Option (Veir.WfIRContext O × Veir.OperationPtr × Veir.BlockPtr ×
      List Veir.OperationPtr × Veir.ValuePtr) := do
  let (ctx₁, fn, reg) ← createRegionOp ctx funcOp
    (mkFuncProps name (funcTypeWith toTy Γ t) default) mb?
  let (ctx₂, blk) ← createBlockIn ctx₁ (Γ.map toTy).toArray reg
  let (ctx₃, ops, final) ← lowerComWfWith bx toTy blk (varMapOfBlockArgs blk) c ctx₂
  let (ctx₄, ret) ← createAtEnd ctx₃ blk returnOp returnProps #[] #[final]
  pure (setAttrsWf (ops.zip (c.veirStepAttrs bx)) ctx₄, fn, blk, ops ++ [ret], final)

/-- Lower a `Com d Γ t` into a fresh `builtin.module` (op-code `moduleOp`) whose one
region holds one block `mb`, holding in order the extern declarations of
`createExternsWf` and the `func.func` of `lowerComToFuncAtWf` at the end of `mb`.
Returns the context, the module, the `func.func`, its block, the block's operations in
order and the value of the program. -/
def lowerComToModuleWf (bx : d.Op → Nat → VeirExpansion O) (toTy : d.Ty → Veir.TypeAttr)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (externs : List (String × List d.Ty × d.Ty))
    (moduleOp : O) (moduleProps : Veir.propertiesOf moduleOp) (funcOp : O)
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (returnOp : O) (returnProps : Veir.propertiesOf returnOp) (name : String) :
    Option (Veir.WfIRContext O × Veir.OperationPtr × Veir.OperationPtr × Veir.BlockPtr ×
      List Veir.OperationPtr × Veir.ValuePtr) := do
  let (ctxM, modOp, mreg) ← createRegionOp default moduleOp moduleProps none
  let (ctx₀, mb) ← createBlockIn ctxM #[] mreg
  let ctxE ← createExternsWf funcOp mkFuncProps toTy mb externs ctx₀
  let (C, fn, blk, ops, final) ← lowerComToFuncAtWf bx toTy c funcOp mkFuncProps
    returnOp returnProps name ctxE (some mb)
  pure (C, modOp, fn, blk, ops, final)

/-- Lower a `Com d Γ t` into a fresh detached region holding one block, whose arguments
are the entries of `Γ`, followed by the operations of `lowerComWfWith bx toTy`, with
their attributes set by `setAttrsWf`. Returns the context, the block, the region, the
operations in order and the value of the program. -/
def lowerComToRegionWf (bx : d.Op → Nat → VeirExpansion O) (toTy : d.Ty → Veir.TypeAttr)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    Option (Veir.WfIRContext O × Veir.BlockPtr × Veir.RegionPtr ×
      List Veir.OperationPtr × Veir.ValuePtr) := do
  let (ctx₀, reg) ← Veir.WfRewriter.createRegion (default : Veir.WfIRContext O)
  let (ctx₁, blk) ← createBlockIn ctx₀ (Γ.map toTy).toArray reg
  let (ctx₂, ops, final) ← lowerComWfWith bx toTy blk (varMapOfBlockArgs blk) c ctx₁
  pure (setAttrsWf (ops.zip (c.veirStepAttrs bx)) ctx₂, blk, reg, ops, final)

end WfBuilder

/-! ## 5. Entry points

Each entry point runs the builder with the expansion `veirExpansionOf` and the types
`ToVeirTy.toTy` of the dialect's instances, and returns the raw context of its output;
when the builder fails it returns the empty context `(default : WfIRContext _).raw`.
Either way the context is well formed. -/

section Entry

variable [ToVeirOp d] [ToVeirTy d]

/--
Lower a closed `Com d [] t` to a fresh context: a detached region holding one block
with the operations of the program (`lowerComToRegionWf`). Returns
`(ctx, blk, reg, finalResult)`.
-/
def lowerClosedCom {t : d.Ty} (com : Com d [] t) :
    Veir.IRContext (ToVeirOp.Op (d := d))
      × Veir.BlockPtr × Veir.RegionPtr × Veir.ValuePtr :=
  match lowerComToRegionWf (veirExpansionOf (d := d)) (ToVeirTy.toTy (d := d)) com with
  | some (C, blk, reg, _, final) => (C.raw, blk, reg, final)
  | none => ((default : Veir.WfIRContext (ToVeirOp.Op (d := d))).raw, default, default, default)

/--
Lower a possibly-open `Com d Γ t` into a detached `func.func` (`lowerComToFuncAtWf`)
in a fresh context. Returns the context, the `func.func` and the value of the program.
-/
def lowerClosedComToFunc {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t)
    (funcOp : ToVeirOp.Op (d := d))
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (returnOp : ToVeirOp.Op (d := d))
    (returnProps : Veir.propertiesOf returnOp)
    (funcName : String) :
    Veir.IRContext (ToVeirOp.Op (d := d))
      × Veir.OperationPtr × Veir.ValuePtr :=
  match lowerComToFuncAtWf (veirExpansionOf (d := d)) (ToVeirTy.toTy (d := d)) com funcOp
      mkFuncProps returnOp returnProps funcName default none with
  | some (C, fn, _, _, final) => (C.raw, fn, final)
  | none => ((default : Veir.WfIRContext (ToVeirOp.Op (d := d))).raw, default, default)

/--
Lower a `Com d Γ t` to a complete `builtin.module` containing
private extern declarations for each callee + the main function
(`lowerComToModuleWf`).

* `externs` — list of `(name, argTys, retTy)` triples; the caller
  is responsible for collecting these from the `com` (e.g., via a
  dialect-specific `externNames` traversal).
* `moduleOp`, `funcOp`, `returnOp` — Veir opcodes (typically
  `.builtin .module`, `.func .func`, `.func .return`).
* `mkFuncProps` — the `funcOp` properties built from a symbol name, a
  function type and the remaining inherent attributes.
* `funcName` — symbol name for the main function.

Returns the `IRContext` and the wrapping `builtin.module`
`OperationPtr` (which is what to hand to `Veir.Printer.printModule`). -/
def lowerClosedComToModuleWithExterns {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t)
    (externs : List (String × List d.Ty × d.Ty))
    (moduleOp : ToVeirOp.Op (d := d))
    (moduleProps : Veir.propertiesOf moduleOp)
    (funcOp : ToVeirOp.Op (d := d))
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (returnOp : ToVeirOp.Op (d := d))
    (returnProps : Veir.propertiesOf returnOp)
    (funcName : String) :
    Veir.IRContext (ToVeirOp.Op (d := d)) × Veir.OperationPtr :=
  match lowerComToModuleWf (veirExpansionOf (d := d)) (ToVeirTy.toTy (d := d)) com externs
      moduleOp moduleProps funcOp mkFuncProps returnOp returnProps funcName with
  | some (C, modOp, _, _, _, _) => (C.raw, modOp)
  | none => ((default : Veir.WfIRContext (ToVeirOp.Op (d := d))).raw, default)

/-- The context `lowerClosedCom` returns is well formed. -/
theorem lowerClosedCom_wellFormed {t : d.Ty} (com : Com d [] t) :
    (lowerClosedCom com).1.WellFormed := by
  unfold lowerClosedCom
  split
  · exact Veir.WfIRContext.wellFormed _
  · exact (default : Veir.WfIRContext (ToVeirOp.Op (d := d))).wellFormed

/-- The context `lowerClosedComToFunc` returns is well formed. -/
theorem lowerClosedComToFunc_wellFormed {Γ : Ctxt d} {t : d.Ty} (com : Com d Γ t)
    (funcOp : ToVeirOp.Op (d := d))
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (returnOp : ToVeirOp.Op (d := d)) (returnProps : Veir.propertiesOf returnOp)
    (funcName : String) :
    (lowerClosedComToFunc com funcOp mkFuncProps returnOp returnProps
      funcName).1.WellFormed := by
  unfold lowerClosedComToFunc
  split
  · exact Veir.WfIRContext.wellFormed _
  · exact (default : Veir.WfIRContext (ToVeirOp.Op (d := d))).wellFormed

/-- The context `lowerClosedComToModuleWithExterns` returns is well formed. -/
theorem lowerClosedComToModuleWithExterns_wellFormed {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t) (externs : List (String × List d.Ty × d.Ty))
    (moduleOp : ToVeirOp.Op (d := d)) (moduleProps : Veir.propertiesOf moduleOp)
    (funcOp : ToVeirOp.Op (d := d))
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (returnOp : ToVeirOp.Op (d := d)) (returnProps : Veir.propertiesOf returnOp)
    (funcName : String) :
    (lowerClosedComToModuleWithExterns com externs moduleOp moduleProps funcOp mkFuncProps
      returnOp returnProps funcName).1.WellFormed := by
  unfold lowerClosedComToModuleWithExterns
  split
  · exact Veir.WfIRContext.wellFormed _
  · exact (default : Veir.WfIRContext (ToVeirOp.Op (d := d))).wellFormed

end Entry

/-! ## Smoke test (EXAMPLE-ONLY)

The `SmokeTest` section below defines a throwaway one-op/one-type dialect
(`smokeDialect`) purely to exercise `lowerClosedCom` end-to-end inside this
module. It is **example-only**: not on any emit/lowering path, used nowhere
outside this section, and exists solely as a type-check smoke signal for the
`Com → Veir` lowering. It is not a backend dialect. -/

namespace SmokeTest

/-- A trivial **example-only** dialect: one op `cst`, one type `nat`. Used solely
    to smoke-test `lowerClosedCom` in this section; not a real backend dialect. -/
def smokeOp : Type := Unit
def smokeTy : Type := Unit

/-- EXAMPLE-ONLY smoke-test dialect (see the section banner above): a throwaway
    one-op/one-type dialect to type-check the `Com → Veir` lowering end-to-end.
    Not on any emit path; no consumer outside `SmokeTest`. -/
@[reducible] def smokeDialect : Dialect :=
  { Op := smokeOp, Ty := smokeTy }

instance : TyDenote smokeTy where
  denote _ := Unit

instance : DialectSignature smokeDialect where
  sig _ := []
  ret _ := ()

/-- A trivial Veir op-info enum with one constructor. -/
inductive SmokeVeirOp where | const
  deriving Inhabited, Hashable, DecidableEq, Repr

instance : Veir.HasOpInfo SmokeVeirOp where
  fromName _ := some .const
  name _ := "smoke.const".toUTF8
  propertiesOf _ := Unit
  fromAttrDict _ _ := .ok ()
  toAttrDict _ _ := Std.HashMap.emptyWithCapacity 0
  propertiesHash := ⟨fun _ => 0⟩
  propertiesDefault := ⟨()⟩
  propertiesRepr := ⟨fun _ _ => "()"⟩
  propertiesDecideEq := fun _ _ => isTrue rfl
  decideEq := inferInstance
  hasSSADominance _ _ := true

instance : ToVeirOp smokeDialect where
  Op := SmokeVeirOp
  hasOpInfo := inferInstance
  toOp _ := .const
  defaultProps _ := ()

instance : ToVeirTy smokeDialect where
  toTy _ := default

/-- A one-`var` `Com`: bind a `cst`, return the binding. -/
def exampleCom : Com smokeDialect [] () :=
  .var (Expr.mk (op := ()) (retTy_eq := rfl) (args := .nil)) (.ret .here)

/-- Smoke test: the lowering type-checks end-to-end and produces a
    concrete `IRContext × BlockPtr × RegionPtr × ValuePtr` value.
    We deliberately use `#check` rather than `#eval` or a `decide` on
    a size predicate because Veir's `HashMap`-backed `IRContext`
    doesn't reduce via Lean's kernel for `decide`; the type-check
    itself is the smoke signal. -/
example : Veir.IRContext SmokeVeirOp × Veir.BlockPtr × Veir.RegionPtr ×
    Veir.ValuePtr :=
  lowerClosedCom (d := smokeDialect) exampleCom

end SmokeTest

end CatCrypt.Crypto.SecureCompilation.VIR
