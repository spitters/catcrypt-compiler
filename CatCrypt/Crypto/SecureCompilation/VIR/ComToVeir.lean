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

/-!
# Path (b): `Com → Veir.IRContext` lowering

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A hand-written lowering from CatCrypt's typed-SSA VIR (`Com d Γ t`) to
Veir's imperative pointer-graph (`Veir.IRContext`).

## Why this exists

Upstream lean-mlir is planned (per opencompl roadmap) to migrate its
typed-SSA layer to be Veir-backed. Until that lands, CatCrypt
maintains this hand-written lowering so we can use Veir as a
code-generation / serialization backend NOW, without waiting for an
upstream lean-mlir Veir-backed release.

Once upstream lean-mlir is Veir-backed and 4.29-released, this file
becomes obsolete — replace with imports from upstream.

## Approach

The lowering is parameterised by two typeclasses:

* `ToVeirOp d O` — maps each VIR op (`d.Op`) to a Veir op-code
  (`O : Type` with `HasOpInfo O`) together with its (default)
  properties. The codomain is left abstract because Veir uses
  per-dialect `OpInfo` enums whereas the in-tree VIR dialect
  (`CatCryptOp`) is structurally different. A separate file will
  provide the `ToVeirOp catCryptDialect VeirCatCryptOpInfo` instance
  once Veir gains a CatCrypt op-info enum.

* `ToVeirTy d` — maps each VIR type (`d.Ty`) to a Veir `TypeAttr`.
  Defaults to `default : TypeAttr` when not refined.

We use Veir's `!`-suffixed (partial) primitives (`pushOperand!`,
`pushResult!`, `setFirstOp!`, …) and rely on the fact that we only
ever push into operations we just allocated. Each operand is linked into
the use list of its value (`pushFreshOperand`). That the built graph is
`IRContext.WellFormed` is not proved here; `ComToVeirWf.lean` builds the
same operations of `jasminDialect` through VeIR's `WfRewriter`, whose
contexts are well formed by construction.

## Status

Scaffold + `Expr` lowering + `Com` lowering + smoke test compile
clean. No open goals, no `axiom`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)

/-! ## 1. State monad and variable map -/

-- We work with `Type 0` dialects because Veir's `IRContext`, `OpResultPtr`,
-- etc., live in `Type 0`, and `StateM` needs its state and result both in
-- the same universe. All real CatCrypt dialects (`CatCryptOp`, `CryptoTy`)
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
A per-protocol bundle of all the Veir state we operate on. We pin
`O` and its `HasOpInfo` here so we can keep `IRContext O` consistent
throughout the lowering.
-/
abbrev ComToVeirM (O : Type) [Veir.HasOpInfo O] (α : Type) : Type :=
  StateM (Veir.IRContext O) α

/--
A map from VIR variables (typed De Bruijn indices) to Veir
SSA-value pointers (`ValuePtr`).

`ValuePtr` is the right level: a variable can be either an
operation result (the common case — bound by `Com.var`) or a block
argument (when the enclosing context `Γ` is materialised as block
arguments of a `func.func`-style entry block; see
`lowerClosedComToFunc`).
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

/-! ## 3. Lowering an `Expr` -/

section Lowering

variable [ToVeirOp d] [ToVeirTy d]

/--
Allocate a fresh `OpResultPtr` on the operation `op`, recording the
result's `TypeAttr`. Returns the new result pointer.

This mirrors Veir's allocation pattern: a freshly-allocated
`Operation` starts with `results := #[]`; each subsequent
`pushResult!` extends that array. The returned `OpResultPtr` is
`{op := op, index := <old length>}`, which is exactly what
`OperationPtr.getResult` would return.
-/
def pushFreshResult (op : Veir.OperationPtr) (ty : Veir.TypeAttr) :
    ComToVeirM (ToVeirOp.Op (d := d)) Veir.OpResultPtr := do
  let ctx ← get
  let idx := op.getNumResults! ctx
  let res : Veir.OpResult :=
    { type := ty
      firstUse := none
      index := idx
      owner := op }
  set (op.pushResult! ctx res)
  return ⟨op, idx⟩

/--
Append an operand reading `value` to the operation `op` and link it at the head of
the use list of `value`, in the steps of VeIR's `Rewriter.pushOperand`
(`OperationPtr.pushOperand` followed by `OpOperandPtr.insertIntoCurrent`): the new
use points back to the first-use slot of `value` and forward to its previous first
use, whose back pointer becomes the new use's next-use slot, and `value`'s first
use becomes the new use.
-/
def pushFreshOperand (op : Veir.OperationPtr) (value : Veir.ValuePtr) :
    ComToVeirM (ToVeirOp.Op (d := d)) Unit := do
  let ctx ← get
  let use : Veir.OpOperandPtr := ⟨op, op.getNumOperands! ctx⟩
  let operand : Veir.OpOperand :=
    { nextUse := none
      back := Veir.OpOperandPtrPtr.valueFirstUse value
      owner := op
      value := value }
  let ctx := op.pushOperand! ctx operand
  let ctx := use.setBack! ctx (Veir.OpOperandPtrPtr.valueFirstUse value)
  let next := value.getFirstUse! ctx
  let ctx := use.setNextUse! ctx next
  let ctx := value.setFirstUse! ctx (some use)
  set (match next with
    | none => ctx
    | some n => n.setBack! ctx (Veir.OpOperandPtrPtr.operandNextUse use))

/-- Allocate a fresh operation for a VIR op-tag, returning its
    `OperationPtr`. The operation starts empty (no operands, no
    results) but immediately receives the op's static attribute
    dictionary (from `ToVeirOp.attrsOf`). The caller is responsible
    for pushing operands and results. -/
def allocOp (vop : d.Op) :
    ComToVeirM (ToVeirOp.Op (d := d)) Veir.OperationPtr := do
  let ctx ← get
  let veop := ToVeirOp.toOp (d := d) vop
  let props := ToVeirOp.defaultProps (d := d) vop
  match Veir.OperationPtr.allocEmpty ctx veop props with
  | some (ctx', ptr) =>
      let attrs := Veir.DictionaryAttr.fromArray (ToVeirOp.attrsOf (d := d) vop)
      let ctx'' := if attrs.entries.isEmpty then ctx' else ptr.setAttributes! ctx' attrs
      set ctx''
      return ptr
  | none =>
      -- `allocEmpty` only returns `none` if the pointer collides,
      -- which by construction (we use `nextID`, monotonically
      -- increasing) cannot happen. Returning `default` here is a
      -- safe fallback that never gets exercised; the smoke test
      -- below exhibits this.
      return default

/--
Push all the operand-arguments from an `HVector` of variables. Iterates
over the argument list, looking up each `Var` in the `VarMap` and
emitting one `pushFreshOperand` per argument.

Defined by recursion on the type-list `tys` so it doesn't need
well-founded reasoning.
-/
def pushAllOperands {Γ : Ctxt d} (vm : VarMap Γ)
    (op : Veir.OperationPtr) :
    {tys : List d.Ty} → HVector (fun ty => Var Γ ty) tys →
    ComToVeirM (ToVeirOp.Op (d := d)) Unit
  | [], .nil => pure ()
  | _ :: _, .cons v rest => do
      pushFreshOperand op (vm _ v)
      pushAllOperands vm op rest

/-- Append `n` fresh results of type `ty` to the operation `op`, returning their
    pointers in order. -/
def pushFreshResults (op : Veir.OperationPtr) (ty : Veir.TypeAttr) :
    Nat → ComToVeirM (ToVeirOp.Op (d := d)) (List Veir.OpResultPtr)
  | 0 => pure []
  | n + 1 => do
      let r ← pushFreshResult (d := d) op ty
      let rs ← pushFreshResults op ty n
      return r :: rs

/--
Lower a single `Expr d Γ t` to one Veir operation.

Builds an op of kind `e.op`, attaches one operand per argument
(resolved against `vm`), and attaches the results given by
`ToVeirOp.resultSlot` (at least one), each of type `ToVeirTy.toTy t`.
Returns the pair `(opPtr, resPtr)`: the `OperationPtr` of the allocated op
(needed for chaining) and the `OpResultPtr` of the result that carries the
binding's value (needed for the `VarMap`).
-/
def lowerExprSingle {Γ : Ctxt d} {t : d.Ty} (vm : VarMap Γ) (e : Expr d Γ t) :
    ComToVeirM (ToVeirOp.Op (d := d))
      (Veir.OperationPtr × Veir.OpResultPtr) := do
  let op ← allocOp e.op
  pushAllOperands vm op e.args
  let (n, k) := ToVeirOp.resultSlot (d := d) e.op
  let rs ← pushFreshResults (d := d) op (ToVeirTy.toTy (d := d) t) (max n 1)
  match rs[k]? with
  | some res => return (op, res)
  | none =>
      match rs with
      | res :: _ => return (op, res)
      | [] => return (op, ⟨op, 0⟩)

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

/-- Append the operands `vs` to the operation `op`, in order. -/
def pushOperandList (op : Veir.OperationPtr) :
    List Veir.ValuePtr → ComToVeirM (ToVeirOp.Op (d := d)) Unit
  | [] => pure ()
  | v :: vs => do
      pushFreshOperand (d := d) op v
      pushOperandList op vs

/-- Append one result per type of `tys` to the operation `op`, returning their
    pointers in order. -/
def pushResultsOfTypes (op : Veir.OperationPtr) :
    List Veir.TypeAttr → ComToVeirM (ToVeirOp.Op (d := d)) (List Veir.OpResultPtr)
  | [] => pure []
  | ty :: tys => do
      let r ← pushFreshResult (d := d) op ty
      let rs ← pushResultsOfTypes op tys
      return r :: rs

/-- Emit one operation of an expansion, whose result types default to `resTy`,
    returning its pointer and its results. -/
def emitStep (args : List Veir.ValuePtr) (resTy : Veir.TypeAttr)
    (done : List (List Veir.OpResultPtr)) (s : VeirExpandStep (ToVeirOp.Op (d := d))) :
    ComToVeirM (ToVeirOp.Op (d := d)) (Veir.OperationPtr × List Veir.OpResultPtr) := do
  let ctx ← get
  let ptr ←
    match Veir.OperationPtr.allocEmpty ctx s.op s.props with
    | some (ctx', ptr) =>
        let attrs := Veir.DictionaryAttr.fromArray s.attrs
        set (if attrs.entries.isEmpty then ctx' else ptr.setAttributes! ctx' attrs)
        pure ptr
    | none => pure default
  pushOperandList (d := d) ptr (s.operands.map (·.resolve args done))
  let rs ← pushResultsOfTypes (d := d) ptr (s.results.map (·.getD resTy))
  return (ptr, rs)

/-- Emit the operations of an expansion in order, returning their pointers and the
    results of every operation emitted so far. -/
def runSteps (args : List Veir.ValuePtr) (resTy : Veir.TypeAttr) :
    List (VeirExpandStep (ToVeirOp.Op (d := d))) → List (List Veir.OpResultPtr) →
    ComToVeirM (ToVeirOp.Op (d := d))
      (List Veir.OperationPtr × List (List Veir.OpResultPtr))
  | [], done => pure ([], done)
  | s :: rest, done => do
      let (op, rs) ← emitStep (d := d) args resTy done s
      let (ops, done') ← runSteps args resTy rest (done ++ [rs])
      return (op :: ops, done')

/--
Lower a single `Expr d Γ t` to Veir operations: the operations of
`ToVeirOp.expand? e.op` when the op has an expansion, else the one operation of
`lowerExprSingle`. Returns the emitted operations, in order, and the value the
binding denotes.
-/
def lowerExpr {Γ : Ctxt d} {t : d.Ty} (vm : VarMap Γ) (e : Expr d Γ t) :
    ComToVeirM (ToVeirOp.Op (d := d)) (List Veir.OperationPtr × Veir.ValuePtr) :=
  match ToVeirOp.expand? (d := d) e.op with
  | some x => do
      let args := argPtrs vm e.args
      let (ops, done) ← runSteps (d := d) args (ToVeirTy.toTy (d := d) t) x.steps []
      return (ops, x.value.resolve args done)
  | none => do
      let (op, res) ← lowerExprSingle vm e
      return ([op], .opResult res)

/-! ## 4. Lowering a `Com` -/

/--
Lower a `Com d Γ t` to a sequence of Veir operations.

Returns the pair `(finalOpRes, opChain)`:

* `finalOpRes : OpResultPtr` — the value the program "computes" (the
  lowering of the `Com.ret`). On `.ret v`, this is `vm v`; otherwise
  it's the result pointer of the last `lowerExpr` invocation.
* `opChain : List OperationPtr` — every `OperationPtr` emitted during
  this lowering, in emission order. The caller chains them via
  `setNextOp!`/`setPrevOp!` and pins `block.firstOp`/`lastOp`.

The semantics:

* `Com.ret v` — looks up `v` in `vm`. No new operation is emitted.
* `Com.var e body` — lowers `e` to its operations, extends the `VarMap`
  with the value of the binding, then recurses on `body`. The operations
  are prepended to the eventual `opChain`.

Chain assembly (parent / prev / next wiring) is left to the caller —
keeping `lowerCom` itself chain-free makes the recursion clean.
-/
def lowerCom {Γ : Ctxt d} {t : d.Ty} :
    VarMap Γ → Com d Γ t →
    ComToVeirM (ToVeirOp.Op (d := d))
      (Veir.ValuePtr × List Veir.OperationPtr)
  | vm, .ret v => pure (vm _ v, [])
  | vm, .var (t := tEx) e body => do
      let (ops, val) ← lowerExpr vm e
      let (final, rest) ← lowerCom (vm.extend (t := tEx) val) body
      return (final, ops ++ rest)

/-- Chain a list of `OperationPtr`s via `setNextOp!`/`setPrevOp!` and
    set each op's parent to `blk`. The first/last pointers of `blk`
    are NOT set here; the caller does that.

    Public so structural reasoning in `ComToVeirCorrect.lean` can
    reference it. -/
def chainOpsInBlock (blk : Veir.BlockPtr) :
    List Veir.OperationPtr →
      ComToVeirM (ToVeirOp.Op (d := d)) Unit
  | [] => pure ()
  | [op] => modify (op.setParent! · (some blk))
  | op :: op' :: rest => do
      modify (op.setNextOp! · (some op'))
      modify (op'.setPrevOp! · (some op))
      modify (op.setParent! · (some blk))
      chainOpsInBlock blk (op' :: rest)

/--
Run `lowerCom` and additionally:

1. Allocate a fresh `BlockPtr` (via `BlockPtr.allocEmpty`).
2. Allocate a fresh `RegionPtr` and link the block as its sole block.
3. Chain the operations emitted by `lowerCom` via `setNextOp!` /
   `setPrevOp!`, set each op's `parent` to the block, and pin
   `block.firstOp` to the first emitted op and `block.lastOp` to the
   last.

Returns the `(BlockPtr, RegionPtr, OpResultPtr)` triple. The
`OpResultPtr` is the value the block "computes" (the lowering of the
`Com.ret`). If the body was a bare `Com.ret v` with no `var`s, no ops
are chained and `block.firstOp` / `block.lastOp` are left as `none`.
-/
def lowerComToBlockRegion {Γ : Ctxt d} {t : d.Ty}
    (vm : VarMap Γ) (com : Com d Γ t) :
    ComToVeirM (ToVeirOp.Op (d := d))
      (Veir.BlockPtr × Veir.RegionPtr × Veir.ValuePtr) := do
  -- Allocate block.
  let ctx ← get
  let (ctx', blk) ←
    match Veir.BlockPtr.allocEmpty ctx with
    | some (ctx', blk) => pure (ctx', blk)
    | none => pure (ctx, default)
  set ctx'
  -- Allocate region.
  let ctx ← get
  let (ctx', reg) ←
    match Veir.RegionPtr.allocEmpty ctx with
    | some (ctx', reg) => pure (ctx', reg)
    | none => pure (ctx, default)
  set ctx'
  -- Lower the Com, collecting the emitted op list.
  let (final, ops) ← lowerCom vm com
  -- Chain ops and set parents.
  chainOpsInBlock blk ops
  -- Wire region → block, block → first/last op, block → parent region.
  let ctx ← get
  let ctx := reg.setFirstBlock! ctx (some blk)
  let ctx := reg.setLastBlock! ctx (some blk)
  let ctx :=
    match ops with
    | [] => ctx
    | first :: tail =>
      let last := (first :: tail).getLast (List.cons_ne_nil _ _)
      blk.setLastOp! (blk.setFirstOp! ctx (some first)) (some last)
  let ctx := blk.setParent! ctx (some reg)
  set ctx
  return (blk, reg, final)

/-! ## 5. Top-level entry point -/

/--
Top-level: lower a closed `Com d [] t` to a freshly-allocated
`IRContext`. Returns `(ctx, blk, reg, finalResult)`.

Closed = no free variables, i.e. `Γ = []`. For an open `Com d Γ t`,
the caller is expected to first emit one block argument per type in
`Γ`, build a `VarMap` from them, then call `lowerComToBlockRegion`.
-/
def lowerClosedCom {t : d.Ty} (com : Com d [] t) :
    Veir.IRContext (ToVeirOp.Op (d := d))
      × Veir.BlockPtr × Veir.RegionPtr × Veir.ValuePtr :=
  let action : ComToVeirM (ToVeirOp.Op (d := d))
      (Veir.BlockPtr × Veir.RegionPtr × Veir.ValuePtr) :=
    lowerComToBlockRegion VarMap.empty com
  let (result, ctx) := action.run default
  (ctx, result.1, result.2.1, result.2.2)

/--
Wrap `lowerClosedCom`'s result in a synthetic `builtin_module`-style
op whose sole region is the lowered region. Returns the wrapping
`OperationPtr` and the updated context — this op is what to hand to
`Veir.Printer.printModule` so that it walks the full op chain rather
than just the producing op.

The wrapping op is allocated against the supplied
`(moduleOp, moduleProps)` pair: callers use their dialect's "module"
op-code (e.g. `Veir.OpCode.builtin .module`) with whatever properties
that op-code expects.
-/
def lowerClosedComToModule {t : d.Ty} (com : Com d [] t)
    (moduleOp : ToVeirOp.Op (d := d))
    (moduleProps : Veir.propertiesOf moduleOp) :
    Veir.IRContext (ToVeirOp.Op (d := d))
      × Veir.OperationPtr × Veir.ValuePtr :=
  let (ctx, _blk, reg, final) := lowerClosedCom com
  match Veir.OperationPtr.allocEmpty ctx moduleOp moduleProps with
  | some (ctx', modPtr) =>
      let ctx'' := modPtr.pushRegion! ctx' reg
      let ctx''' := reg.setParent! ctx'' modPtr
      (ctx''', modPtr, final)
  | none => (ctx, default, final)

/-! ## 6. Func-shaped lowering (path b's "func.func" wrapper)

`lowerClosedComToFunc` lowers a possibly-open `Com d Γ t` into a
`func.func`-shaped operation: the context `Γ` is materialised as
block arguments, the lowered ops live inside the entry block, and a
return-terminator op is appended carrying the final value. -/

section FuncShape

variable [ToVeirOp d] [ToVeirTy d]

/-- Resolve a De Bruijn `Var Γ t` to a Veir `BlockArgumentPtr`. The
    convention matches CatCrypt's in-tree printer
    (`Print.printModuleArgs` + `PrintEnv.get`): block-arg index =
    De Bruijn depth, i.e. `.here ↦ arg 0`, `.there .here ↦ arg 1`,
    `.there (.there .here) ↦ arg 2`, … . This is consistent with
    `pushBlockArgs` pushing `Γ` head-first (so the head of `Γ` becomes
    arg 0). -/
def varToBlockArg (blk : Veir.BlockPtr) {Γ : Ctxt d} {t : d.Ty}
    (v : Var Γ t) : Veir.BlockArgumentPtr :=
  blk.getArgument (varDepth v)

/-- Build a `VarMap` whose entries are the block arguments of `blk`,
    indexed by De Bruijn depth (`.here ↦ arg 0`). -/
def varMapOfBlockArgs {Γ : Ctxt d} (blk : Veir.BlockPtr) :
    VarMap Γ :=
  fun _ v => Veir.ValuePtr.blockArgument (varToBlockArg blk v)

/-- Push one fresh `BlockArgument` for each type in `tys` (in source
    order: `tys.head` ⇒ arg 0). -/
def pushBlockArgs (blk : Veir.BlockPtr) :
    (tys : List d.Ty) →
    ComToVeirM (ToVeirOp.Op (d := d)) Unit
  | [] => pure ()
  | t :: rest => do
      let ctx ← get
      let arg : Veir.BlockArgument :=
        { type := ToVeirTy.toTy (d := d) t
          firstUse := none
          index := blk.getNumArguments! ctx
          loc := default
          owner := blk }
      set (blk.pushArgument! ctx arg)
      pushBlockArgs blk rest

/-- StateM-builder helper: build a `func.func` op from a `Com d Γ t`.
    Allocates an entry block + region, materialises `Γ` as block
    arguments, lowers the body, appends a return-terminator op,
    wires the chain, and finally allocates the wrapping func.func op
    with the properties `mkFuncProps funcName funcType extra`, where
    `mkFuncProps` builds the op-code's properties from the symbol name, the
    function type and the remaining inherent attributes (`extra`).

    Returns the `OperationPtr` of the func.func — usable as a top-level
    op inside a wrapping `builtin.module` block, or as a printer root. -/
def buildFuncFromCom {Γ : Ctxt d} {t : d.Ty}
    (com : Com d Γ t)
    (funcOp : ToVeirOp.Op (d := d))
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (returnOp : ToVeirOp.Op (d := d))
    (returnProps : Veir.propertiesOf returnOp)
    (funcName : String) :
    ComToVeirM (ToVeirOp.Op (d := d)) Veir.OperationPtr := do
  -- Allocate entry block + body region.
  let ctx ← get
  let (ctx', blk) ←
    match Veir.BlockPtr.allocEmpty ctx with
    | some (ctx', blk) => pure (ctx', blk)
    | none => pure (ctx, default)
  set ctx'
  let ctx ← get
  let (ctx', reg) ←
    match Veir.RegionPtr.allocEmpty ctx with
    | some (ctx', reg) => pure (ctx', reg)
    | none => pure (ctx, default)
  set ctx'
  pushBlockArgs blk Γ
  let vm : VarMap Γ := varMapOfBlockArgs blk
  let (final, bodyOps) ← lowerCom vm com
  -- Return-terminator op.
  let ctxR ← get
  let retOpPtr ←
    match Veir.OperationPtr.allocEmpty ctxR returnOp returnProps with
    | some (ctxR', p) => set ctxR'; pure p
    | none => pure default
  pushFreshOperand retOpPtr final
  let allOps := bodyOps ++ [retOpPtr]
  chainOpsInBlock blk allOps
  let ctx ← get
  let ctx := reg.setFirstBlock! ctx (some blk)
  let ctx := reg.setLastBlock! ctx (some blk)
  let ctx :=
    match allOps with
    | [] => ctx
    | first :: tail =>
      let last := (first :: tail).getLast (List.cons_ne_nil _ _)
      blk.setLastOp! (blk.setFirstOp! ctx (some first)) (some last)
  let ctx := blk.setParent! ctx (some reg)
  set ctx
  -- Allocate the func wrapper and wire region in.
  let inputs : Array Veir.Attribute :=
    (Γ.map (fun ty => ((ToVeirTy.toTy (d := d) ty).val))).toArray
  let outputs : Array Veir.Attribute :=
    #[(ToVeirTy.toTy (d := d) t).val]
  let funcType : Veir.FunctionType := { inputs := inputs, outputs := outputs }
  let ctx ← get
  let funcOpPtr ←
    match Veir.OperationPtr.allocEmpty ctx funcOp
        (mkFuncProps funcName funcType default) with
    | some (ctx', p) => set ctx'; pure p
    | none => pure default
  modify (funcOpPtr.pushRegion! · reg)
  modify (reg.setParent! · funcOpPtr)
  return funcOpPtr

/--
Lower a possibly-open `Com d Γ t` into a `func.func`-shaped wrapper.
Convenience entry: runs `buildFuncFromCom` over a fresh `IRContext`
and unpacks. -/
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
  let action := buildFuncFromCom com funcOp mkFuncProps returnOp returnProps funcName
  let (funcPtr, ctx) := action.run default
  -- The final value isn't recoverable from this entry point (caller
  -- gets only the wrapping func op + ctx). Return `default` as the
  -- ValuePtr slot — kept for legacy API shape.
  (ctx, funcPtr, default)

/-! ## 7. Module-with-externs wrapping (mlir-opt-roundtrippable)

`lowerClosedComToModuleWithExterns` builds a complete top-level
`builtin.module` containing:

* A private `func.func` declaration (empty body region) for each
  callee referenced by a `func.call`-shaped op in `com`.
* The main `func.func` lowered from `com`.

This is the shape `mlir-opt` accepts and re-emits in sugared form. -/

/-- Build an extern `func.func` declaration — a func with an empty
    body region, whose properties `mkFuncProps name funcType extra` carry the
    symbol name, the function type and `extra = {sym_visibility = "private"}`.
    Returns the `OperationPtr`. -/
def buildExternFunc
    (funcOp : ToVeirOp.Op (d := d))
    (mkFuncProps : String → Veir.FunctionType → Veir.DictionaryAttr →
      Veir.propertiesOf funcOp)
    (name : String) (argTys : List d.Ty) (retTy : d.Ty) :
    ComToVeirM (ToVeirOp.Op (d := d)) Veir.OperationPtr := do
  -- An empty body region (no blocks).
  let ctx ← get
  let (ctx', reg) ←
    match Veir.RegionPtr.allocEmpty ctx with
    | some (ctx', reg) => pure (ctx', reg)
    | none => pure (ctx, default)
  set ctx'
  -- The func.func op.
  let inputs : Array Veir.Attribute :=
    (argTys.map (fun ty => ((ToVeirTy.toTy (d := d) ty).val))).toArray
  let outputs : Array Veir.Attribute :=
    #[(ToVeirTy.toTy (d := d) retTy).val]
  let funcType : Veir.FunctionType := { inputs := inputs, outputs := outputs }
  let extra := Veir.DictionaryAttr.fromArray
    #[("sym_visibility".toUTF8, Veir.Attribute.stringAttr ⟨"private".toUTF8⟩)]
  let ctx ← get
  let funcOpPtr ←
    match Veir.OperationPtr.allocEmpty ctx funcOp (mkFuncProps name funcType extra) with
    | some (ctx', p) => set ctx'; pure p
    | none => pure default
  modify (funcOpPtr.pushRegion! · reg)
  modify (reg.setParent! · funcOpPtr)
  return funcOpPtr

/--
Lower a closed `Com d Γ t` to a complete `builtin.module` containing
private extern declarations for each callee + the main function.

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
  let action : ComToVeirM (ToVeirOp.Op (d := d)) Veir.OperationPtr := do
    -- Build the extern func.func decls.
    let externOps ← externs.mapM
      (fun ext => buildExternFunc funcOp mkFuncProps ext.1 ext.2.1 ext.2.2)
    -- Build the main func.
    let mainOp ← buildFuncFromCom com funcOp mkFuncProps returnOp returnProps
                                  funcName
    -- Allocate the module wrapper + region + entry block.
    let ctx ← get
    let modOpPtr ←
      match Veir.OperationPtr.allocEmpty ctx moduleOp moduleProps with
      | some (ctx', p) => set ctx'; pure p
      | none => pure default
    let ctx ← get
    let (ctx', modBlk) ←
      match Veir.BlockPtr.allocEmpty ctx with
      | some (ctx', blk) => pure (ctx', blk)
      | none => pure (ctx, default)
    set ctx'
    let ctx ← get
    let (ctx', modReg) ←
      match Veir.RegionPtr.allocEmpty ctx with
      | some (ctx', reg) => pure (ctx', reg)
      | none => pure (ctx, default)
    set ctx'
    let allTopOps := externOps ++ [mainOp]
    chainOpsInBlock modBlk allTopOps
    -- Wire module → region → block, set firstBlock/lastBlock and
    -- firstOp/lastOp.
    modify (modReg.setFirstBlock! · (some modBlk))
    modify (modReg.setLastBlock! · (some modBlk))
    modify (modReg.setParent! · modOpPtr)
    modify (modBlk.setParent! · (some modReg))
    let ctx ← get
    let ctx :=
      match allTopOps with
      | [] => ctx
      | first :: tail =>
        let last := (first :: tail).getLast (List.cons_ne_nil _ _)
        modBlk.setLastOp! (modBlk.setFirstOp! ctx (some first)) (some last)
    let ctx := modOpPtr.pushRegion! ctx modReg
    set ctx
    return modOpPtr
  let (modPtr, ctx) := action.run default
  (ctx, modPtr)

end FuncShape

end Lowering

/-! ## 6. Smoke test

Build a tiny dialect with one op (a nullary "constant"), lower a
single-`ret` `Com`, and verify that the lowering type-checks and
runs.
-/

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
    concrete `IRContext × BlockPtr × RegionPtr × OpResultPtr` value.
    We deliberately use `#check` rather than `#eval` or a `decide` on
    a size predicate because Veir's `HashMap`-backed `IRContext`
    doesn't reduce via Lean's kernel for `decide`; the type-check
    itself is the smoke signal. -/
example : Veir.IRContext SmokeVeirOp × Veir.BlockPtr × Veir.RegionPtr ×
    Veir.ValuePtr :=
  lowerClosedCom (d := smokeDialect) exampleCom

end SmokeTest

end CatCrypt.Crypto.SecureCompilation.VIR
