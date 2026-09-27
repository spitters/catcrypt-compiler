/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTSyntax

/-!
# Direct `LowCT → MLIR text` emitter (DEBUG-ONLY shortcut)

Walks a `LowCT` tree and produces textual MLIR in generic-op syntax
compatible with the existing `catcrypt-bench/src/x25519_*.mlir`
pipeline. Bypasses the `Com` / VIR layer.

This emitter answers one concrete question: *does the DSL source produce
the same runtime performance as the hand-authored VIR path?* The emitter
itself is not verified — it is a text formatter over the `LowCT` AST.

The verified chain `LowCT → Com catCryptDialect → Veir/MLIR` threads a leaf
`extCall` end-to-end (see
`CatCrypt/Crypto/SecureCompilation/VIR/ExtCallVeirSmoke.lean`), so this
module is a **redundant, debug-only** text formatter: prefer the verified
chain (`CryptoToVIR` → `ComToVeir` / `CatCryptPrint`) for any emission whose
correctness matters.

## Scope

Supports the subset of `LowCT` that X25519-style benchmark code
uses:
- `RSkip` (no-op)
- `RSeq` (statement sequencing)
- `RCall f dest args` (emits `%N = "func.call"(%args){callee=@f}...`)
- `RLetZero`, `RLetU64Zero` (treated as "local dummy" — ignored for
  MLIR emission; the benchmark harness threads initial values as
  function arguments, not via explicit zero-alloc).

Does NOT support:
- `RIfNz`, `RWhileNz` (structured control flow — not used in the
  unrolled ladder).
- `RLimbStore`, `RCloneCall`, `RScalarSet` (not used in X25519 step).
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTToMLIR

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## MLIR type rendering -/

/-- Render a `TowerType` as an MLIR type string. -/
def towerTypeToMLIR : TowerType → String
  | .TFp      => "memref<6xi64>"
  | .TFp2     => "memref<12xi64>"
  | .TFp6     => "memref<36xi64>"
  | .TFp12    => "memref<72xi64>"
  | .TU64     => "i64"
  | .TU8      => "i8"
  | .TU32     => "i32"
  | .TFp25519 => "memref<5xi64>"
  | .TFp25519_64 => "memref<4xi64>"
  | .TFpL25519 => "memref<4xi64>"
  | .TFpP256 => "memref<4xi64>"
  | .TFp25519_4Bounded _ => "memref<4xi64>"
  | .TFpGen _ n => s!"memref<{n}xi8>"
  | .TFp2Gen _ n => s!"memref<{n}xi8>"
  | .TTuple _ _ => "memref<?xi8>"  -- tuple lowered as raw byte array
  | .TBytes n => s!"memref<{n}xi8>"
  -- Runtime-indexed array type, as a flat byte memref
  -- (the X25519 benchmark path doesn't exercise TArr).
  | .TArr n _ => s!"memref<{n}xi8>"
  -- Polynomial-mod-q types lowered as flat memref byte arrays.
  | .TPolyMod _ n => s!"memref<{n}xi64>"
  | .TPolyVec _ n k => s!"memref<{k * n}xi64>"
  | .TPolyMat _ n k m => s!"memref<{k * m * n}xi64>"

/-! ## Emit state

A symbol table maps LowCT variable names (strings) to the MLIR SSA
identifier that currently holds their value (e.g. `"%arg0"`, `"%3"`).
Each `RCall` allocates a fresh `%N` for its result and updates the
table. -/

/-- Emission state. -/
structure State where
  /-- Map from LowCT variable name → current MLIR SSA identifier. -/
  names : List (String × String)
  /-- Counter for fresh `%N` SSA identifiers. -/
  counter : Nat
  /-- Accumulated MLIR body lines. -/
  lines : List String
  deriving Inhabited

/-- Look up a variable's current SSA id. Fails with a sentinel string
    if the name is not bound (shouldn't happen for well-formed input). -/
def State.lookup (s : State) (name : String) : String :=
  match s.names.find? (fun p => p.1 == name) with
  | some p => p.2
  | none   => "%UNBOUND_" ++ name

/-- Bind a name to a fresh SSA id. -/
def State.bind (s : State) (name : String) (ssa : String) : State :=
  { s with names := (name, ssa) :: s.names.filter (fun p => p.1 != name) }

/-- Fresh SSA identifier, incrementing the counter. -/
def State.fresh (s : State) : String × State :=
  (s!"%{s.counter}", { s with counter := s.counter + 1 })

/-- Append a line to the body. -/
def State.emit (s : State) (line : String) : State :=
  { s with lines := line :: s.lines }

/-! ## Per-constructor emission -/

/-- Emit a single `RCall`. -/
def emitCall (f : String) (dest : Located) (args : List Located)
    (s : State) : State :=
  let argSSAs := args.map (fun a => s.lookup a.locVar)
  let argTys  := args.map (fun a => towerTypeToMLIR a.locSrc)
  let retTy   := towerTypeToMLIR dest.locDst
  let (newSSA, s') := s.fresh
  let argCSV := String.intercalate ", " argSSAs
  let tysCSV := String.intercalate ", " argTys
  -- Splitting string concatenation to avoid s! interpreting `{callee}`.
  let line :=
    "  " ++ newSSA ++ " = \"func.call\"(" ++ argCSV ++ ") "
      ++ "{callee = @" ++ f ++ "} : (" ++ tysCSV ++ ") -> " ++ retTy
  (s'.emit line).bind dest.locVar newSSA

/-- Emit a whole-array `RCopy dst src`: a fresh buffer of the destination
    type (`memref.alloc`), a `memref.copy` of `src` into it, and a binding
    of `dst` to the fresh buffer. -/
def emitCopy (dst src : Located) (s : State) : State :=
  let srcSSA := s.lookup src.locVar
  let ty := towerTypeToMLIR dst.locDst
  let (newSSA, s') := s.fresh
  let allocLine := "  " ++ newSSA ++ " = \"memref.alloc\"() : () -> " ++ ty
  let copyLine :=
    "  \"memref.copy\"(" ++ srcSSA ++ ", " ++ newSSA ++ ") : ("
      ++ ty ++ ", " ++ ty ++ ") -> ()"
  ((s'.emit allocLine).emit copyLine).bind dst.locVar newSSA

/-- Walk a `LowCT` tree in execution order, accumulating MLIR lines. -/
partial def emitCmd (c : LowCT) (s : State) : State :=
  match c with
  | .RSkip            => s
  | .RSeq a b         => emitCmd b (emitCmd a s)
  | .RCall f d args   => emitCall f d args s
  -- `RLetZero`/`RLetU64Zero`: no MLIR emission — locals are implicit
  -- in SSA. Later `RCall` that writes this name creates the value.
  | .RLetZero _ _ body    => emitCmd body s
  | .RLetU64Zero _ body   => emitCmd body s
  -- Unsupported for the benchmark subset — emit a placeholder comment.
  | .RScalarSet _ _       => s.emit "  // <RScalarSet: not emitted>"
  | .RLimbStore _ _ _     => s.emit "  // <RLimbStore: not emitted>"
  | .RLimbStoreExpr _ _ _ => s.emit "  // <RLimbStoreExpr: not emitted>"
  | .RCloneCall _ _ _ _ _ _ => s.emit "  // <RCloneCall: not emitted>"
  | .RIfNz _ _ _          => s.emit "  // <RIfNz: not emitted>"
  | .RWhileNz _ _         => s.emit "  // <RWhileNz: not emitted>"
  | .RFor _ _ _           => s.emit "  // <RFor: not emitted>"
  | .RForRuntime _ _ _    => s.emit "  // <RForRuntime: not emitted>"
  | .RCallSwap _ _ _ _    => s.emit "  // <RCallSwap: not emitted>"
  | .RCallN _ _ _         => s.emit "  // <RCallN: not emitted>"
  | .RSelect _ _ _ _      => s.emit "  // <RSelect: not emitted>"
  | .RAssert _            => s.emit "  // <RAssert: not emitted>"
  | .RBlock body          => emitCmd body s
  | .RFnDef _ _ _ body cont => emitCmd cont (emitCmd body s)
  | .RFnCall _ _ _        => s.emit "  // <RFnCall: not emitted>"
  | .RTupleLoad _ _ _     => s.emit "  // <RTupleLoad: not emitted>"
  -- Not used in the X25519 benchmark.
  | .RArrStore _ _ _      => s.emit "  // <RArrStore: not emitted>"
  | .RArrLoad _ _ _       => s.emit "  // <RArrLoad: not emitted>"
  | .RScalarSetExpr _ _   => s.emit "  // <RScalarSetExpr: not emitted>"
  -- Literal-index array ops + dst-threaded
  -- leaf call.  Not used in the X25519 benchmark subset this emitter
  -- targets; emit the same placeholder comment as the other
  -- unsupported shapes.
  | .RArrStoreLit _ _ _     => s.emit "  // <RArrStoreLit: not emitted>"
  | .RArrLoadLit _ _ _      => s.emit "  // <RArrLoadLit: not emitted>"
  | .RCallDstThreaded _ _ _ => s.emit "  // <RCallDstThreaded: not emitted>"
  | .RCopy dst src          => emitCopy dst src s

/-! ## Top-level `func.func` emission -/

/-- Emit a full MLIR `func.func @name(%arg0 : Ty, …) -> retTy { … }`
    from a `LowCT` body, a list of (argName, argType) pairs, and a
    (retName, retType). The `retName` must be bound in the body by one
    of the `RCall`s. -/
def emitFunc (name : String) (args : List (String × TowerType))
    (retName : String) (retTy : TowerType) (body : LowCT) : String :=
  let initState : State :=
    { names   := (args.zipIdx.map (fun p => (p.1.1, s!"%arg{p.2}")))
      counter := 0
      lines   := [] }
  let final := emitCmd body initState
  let bodyLines := (final.lines.reverse).foldl (· ++ "\n" ++ ·) ""
  let argSig := String.intercalate ", "
    (args.zipIdx.map (fun p =>
      s!"%arg{p.2} : {towerTypeToMLIR p.1.2}"))
  let retSSA := final.lookup retName
  s!"func.func @{name}({argSig}) -> {towerTypeToMLIR retTy} \{"
    ++ bodyLines ++ "\n"
    ++ s!"  return {retSSA} : {towerTypeToMLIR retTy}\n"
    ++ "}"

/-- Emit the external declarations for a list of leaf calls. Each
    entry is `(name, arity, input-type, output-type)` — we assume all
    field ops use a single tower type for both inputs and outputs.
    For heterogeneous-arity signatures (e.g. `fp_sqr` is arity 1),
    pass the arity explicitly. -/
def emitExterns (externs : List (String × Nat × TowerType × TowerType))
    : String :=
  externs.foldl (fun acc ⟨name, arity, argTy, retTy⟩ =>
    let argTys := String.intercalate ", "
      ((List.replicate arity (towerTypeToMLIR argTy)))
    acc ++ s!"func.func private @{name}({argTys}) -> {towerTypeToMLIR retTy}\n"
  ) ""

/-- Emit a complete MLIR module: externs followed by one `func.func`. -/
def emitModule (name : String) (args : List (String × TowerType))
    (retName : String) (retTy : TowerType) (body : LowCT)
    (externs : List (String × Nat × TowerType × TowerType)) : String :=
  emitExterns externs ++ "\n" ++ emitFunc name args retName retTy body

/-! ## Out-param calling convention

Standard MLIR out-param emission: each `RCall` allocates a stack buffer
via `memref.alloca`, passes it as the first argument to the callee, and
the callee returns `()` after writing to `%out`. At the top level, the
function itself takes `%out` as its first argument and the last `RCall`
writes directly to it (no extra copy).

This matches the fiat-crypto C ABI `void fiat_25519_add(out, a, b)`, so
emitted MLIR links directly against `curve25519_64.c` without a shim
pool — eliminating the pool-slot indirection that prevents LLVM from
inlining through the bench loop. Expected speedup: ~3× vs the pool
convention, based on the inlined-C baseline. -/

/-- Emit a single `RCall` as stack-allocated out-param: alloca + call. -/
def emitCallOutParam (f : String) (dest : Located) (args : List Located)
    (retSlot : Option String) (s : State) : State :=
  let argSSAs := args.map (fun a => s.lookup a.locVar)
  let argTy   := towerTypeToMLIR (args.headD dest).locDst
  let retTy   := towerTypeToMLIR dest.locDst
  -- If this RCall writes to the top-level return slot, use %out directly;
  -- otherwise alloca a fresh buffer.
  let (outSSA, s') :=
    match retSlot with
    | some slot => if slot == dest.locVar then ("%out", s) else s.fresh
    | none => s.fresh
  let allocaLine :=
    if outSSA == "%out" then none
    else some ("  " ++ outSSA ++ " = \"memref.alloca\"() "
               ++ "<{alignment = 8 : i64, operandSegmentSizes = array<i32: 0, 0>}> "
               ++ ": () -> " ++ retTy)
  let argCSV := String.intercalate ", " (outSSA :: argSSAs)
  let allTys := String.intercalate ", "
    (retTy :: args.map (fun a => towerTypeToMLIR a.locSrc))
  let callLine :=
    "  \"func.call\"(" ++ argCSV ++ ") "
      ++ "{callee = @" ++ f ++ "} : (" ++ allTys ++ ") -> ()"
  let s'' := match allocaLine with
    | some l => s'.emit l
    | none => s'
  let _ := argTy
  (s''.emit callLine).bind dest.locVar outSSA

/-- Walk `LowCT` emitting out-param calls. -/
partial def emitCmdOutParam (c : LowCT) (retSlot : Option String) (s : State) : State :=
  match c with
  | .RSkip              => s
  | .RSeq a b           => emitCmdOutParam b retSlot (emitCmdOutParam a retSlot s)
  | .RCall f d args     => emitCallOutParam f d args retSlot s
  | .RLetZero _ _ body  => emitCmdOutParam body retSlot s
  | .RLetU64Zero _ body => emitCmdOutParam body retSlot s
  | _                   => s.emit "  // <unsupported constructor>"

/-- Emit a full out-param MLIR function. Signature:
    `func.func @name(%out : retTy, %arg0, …, %argN) -> ()`
    where the body's last `RCall` writes directly to `%out`. -/
def emitFuncOutParam (name : String) (args : List (String × TowerType))
    (retName : String) (retTy : TowerType) (body : LowCT) : String :=
  let initState : State :=
    { names   := args.zipIdx.map (fun p => (p.1.1, s!"%arg{p.2}"))
      counter := 0
      lines   := [] }
  let final := emitCmdOutParam body (some retName) initState
  let bodyLines := (final.lines.reverse).foldl (· ++ "\n" ++ ·) ""
  let argSig := String.intercalate ", "
    (("%out : " ++ towerTypeToMLIR retTy) ::
      args.zipIdx.map (fun p => s!"%arg{p.2} : {towerTypeToMLIR p.1.2}"))
  "func.func @" ++ name ++ "(" ++ argSig ++ ") {" ++
    bodyLines ++ "\n  return\n}"

/-- Externs for out-param ABI: each leaf takes out as first arg, returns `()`.
    `(name, arity, argTy, retTy)` — retTy placed at arg 0, argTy for the rest. -/
def emitExternsOutParam (externs : List (String × Nat × TowerType × TowerType))
    : String :=
  externs.foldl (fun acc ⟨name, arity, argTy, retTy⟩ =>
    let argTys := String.intercalate ", "
      (towerTypeToMLIR retTy :: List.replicate arity (towerTypeToMLIR argTy))
    acc ++ s!"func.func private @{name}({argTys})\n"
  ) ""

end CatCrypt.Crypto.Jasmin.LowCTToMLIR
