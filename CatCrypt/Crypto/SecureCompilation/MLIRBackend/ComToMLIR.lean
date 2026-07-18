/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIRBackend.Smoke
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
import CatCrypt.Crypto.Optimizer.ComCanonical

/-!
# MLIR backend — Stage 2 scalar translation skeleton (task #183)

`Com → lean-mlir.Module` for the *scalar* subset of Jasmin's `Cmd` /
`InstrR` / `PExpr`. The output is MLIR text in the registered `arith` /
`func` dialects.

## Scope (this stage)

| Source                   | Target                                      |
|--------------------------|---------------------------------------------|
| `Cassgn lv _ ty e`       | `%v = <expr-translation> : <ty>`            |
| `Pconst z`               | `arith.constant z : <ty>`                   |
| `Pvar gv`                | (operand lookup — reuse existing SSA name)  |
| `Papp2 (Oadd ws) e1 e2`  | `arith.addi`                                |
| `Papp2 (Osub ws) e1 e2`  | `arith.subi`                                |
| `Papp2 (Omul ws) e1 e2`  | `arith.muli`                                |
| `Papp2 (Oland ws) e1 e2` | `arith.andi`                                |
| `Papp2 (Olor ws) e1 e2`  | `arith.ori`                                 |
| `Papp2 (Olxor ws) e1 e2` | `arith.xori`                                |
| `Papp2 (Olsl ws) e1 e2`  | `arith.shli`                                |
| `Papp2 (Olsr ws) e1 e2`  | `arith.shrui`                               |
| Anything else            | `catcrypt.opaque` (escape hatch)            |

`Cif`, `Cfor`, `Cwhile` now lower into the `scf` dialect (Phase 5) —
they recurse into their nested `Cmd` bodies via mutual recursion with
`emitCmd`. `Ccall`, `Copn` are still deferred to Phase 6 / 8 and lower
as `catcrypt.opaque` for now so the emitter is total.

## Trust scope

This file produces **MLIR text**. The text is consumed by `mlir-opt`
downstream — there is no proof at this layer that the text matches the
`Cmd`'s denotation. `Denote.lean` (Stage 4) provides the
`denoteCmd_eq_denoteMlirEmit` proof obligation; this file is the
*emitter*, not the *equivalence*.

We deliberately stay text-based (rather than building a `Veir.IRContext`)
so the Stage-2 lowering is straightforward to read and audit. A future
stage may swap to a proper `IRContext` construction; the existing
`VIR/ComToVeir.lean` is the template.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIRBackend

open CatCrypt.Crypto.Jasmin

/-! ## §1. MLIR type rendering

Jasmin `SType` → MLIR type string. -/

/-- Render a Jasmin `WSize` as the corresponding MLIR integer type. -/
def renderWSize : WSize → String
  | .U8   => "i8"
  | .U16  => "i16"
  | .U32  => "i32"
  | .U64  => "i64"
  | .U128 => "i128"
  | .U256 => "i256"
  | .U512 => "i512"

/-- Render a Jasmin `SType` as an MLIR type string. Boolean → `i1`,
    integer → `index`, word → `iN`, array → `memref<n × i8>`. -/
def renderSType : SType → String
  | .sbool   => "i1"
  | .sint    => "index"
  | .sword w => renderWSize w
  | .sarr n  => s!"memref<{n}xi8>"

example : renderSType (.sword .U32) = "i32" := rfl
example : renderSType (.sword .U64) = "i64" := rfl
example : renderSType .sbool = "i1" := rfl
example : renderSType (.sarr 16) = "memref<16xi8>" := rfl

/-! ## §2. Emit state

A symbol table maps Jasmin variable names to current MLIR SSA identifiers,
plus a counter for fresh `%N` ids and an accumulator for emitted lines.

This is intentionally the same shape as `LowCTToMLIR.State` so the two
emitters can share `mlir-opt` downstream tooling. -/

/-- Stage-2 emit state. -/
structure EmitState where
  /-- Mapping from Jasmin var name → current MLIR SSA id (e.g. `"%3"`). -/
  names : List (String × String)
  /-- Counter for fresh `%N` SSA identifiers. -/
  counter : Nat
  /-- Accumulated MLIR body lines (reversed — head is most-recent). -/
  lines : List String
  deriving Inhabited

namespace EmitState

/-- Lookup a variable's current SSA id. Falls back to a sentinel for
    unbound names so emission is total. -/
def lookup (s : EmitState) (name : String) : String :=
  match s.names.find? (fun p => p.1 == name) with
  | some p => p.2
  | none   => "%UNBOUND_" ++ name

/-- Bind a Jasmin variable name to a fresh SSA id. Existing bindings for
    the same name are shadowed (SSA-style — the old id is unreachable). -/
def bind (s : EmitState) (name : String) (ssa : String) : EmitState :=
  { s with names := (name, ssa) :: s.names.filter (fun p => p.1 != name) }

/-- Allocate a fresh `%N` SSA identifier and bump the counter. -/
def fresh (s : EmitState) : String × EmitState :=
  (s!"%{s.counter}", { s with counter := s.counter + 1 })

/-- Append a line to the body. Stored in reverse order; flush via `getLines`. -/
def emit (s : EmitState) (line : String) : EmitState :=
  { s with lines := line :: s.lines }

/-- Return the body in source order. -/
def getLines (s : EmitState) : List String := s.lines.reverse

/-- The empty initial state. -/
def init : EmitState := { names := [], counter := 0, lines := [] }

end EmitState

/-! ## §3. Binary-op translation table

`SOp2 → arith.*` for the eight scalar binary ops we support. Other `SOp2`
constructors return `none` (caller emits an opaque marker). -/

/-- Translate a Jasmin `SOp2` to an `arith.*` mnemonic, if it is one of
    the eight scalar binops Stage 2 supports. Returns `none` for ops that
    are outside the scalar arith subset (comparison, vector ops, etc.). -/
def sOp2ToArithMnemonic : SOp2 → Option String
  | .Oadd _  => some "arith.addi"
  | .Osub _  => some "arith.subi"
  | .Omul _  => some "arith.muli"
  | .Oland _ => some "arith.andi"
  | .Olor _  => some "arith.ori"
  | .Olxor _ => some "arith.xori"
  | .Olsl _  => some "arith.shli"
  | .Olsr _  => some "arith.shrui"
  | _        => none

example : sOp2ToArithMnemonic (.Oadd .U32) = some "arith.addi" := rfl
example : sOp2ToArithMnemonic (.Olxor .U64) = some "arith.xori" := rfl
example : sOp2ToArithMnemonic .Obeq = none := rfl

/-! ### Stage-3 vector arith subset

Vector arith in MLIR is just `arith.*i` lifted to `vector<n × iM>` types
— there is no separate `vector.addi` op. So we share the mnemonic table
with the scalar case and only widen the type the op is emitted at.

The Stage-3 lowering target for x86 is reached via `mlir-opt
--convert-vector-to-llvm` (or the more aggressive
`--convert-vector-to-x86vector` pass once we wire it). The
`vector.broadcast` / `vector.shuffle` / `vector.fma` / `vector.load` /
`vector.store` ops that the `VectorDialect/` pre-#183 directory models
abstractly route through that same lowering. -/

/-- Translate a vector-shaped `SOp2` to the `arith.*` mnemonic it
    becomes when lifted to `vector<n × iM>`. Returns `none` for
    non-vector binops. -/
def sOp2ToVectorArithMnemonic : SOp2 → Option String
  | .Ovadd _ _ => some "arith.addi"
  | .Ovsub _ _ => some "arith.subi"
  | .Ovmul _ _ => some "arith.muli"
  | .Ovlsr _ _ => some "arith.shrui"
  | .Ovlsl _ _ => some "arith.shli"
  | .Ovasr _ _ => some "arith.shrsi"
  | _          => none

example : sOp2ToVectorArithMnemonic (.Ovadd .U16 .U256) = some "arith.addi" := rfl
example : sOp2ToVectorArithMnemonic (.Ovmul .U32 .U256) = some "arith.muli" := rfl
example : sOp2ToVectorArithMnemonic (.Oadd .U64) = none := rfl

/-- The MLIR vector type for an `Ov*` op with element-width `ve` and
    total-width `ws`. E.g. `Ovadd U16 U256 → vector<16xi16>`. -/
def renderVectorType (ve ws : WSize) : String :=
  let lanes := ws.bits / ve.bits
  s!"vector<{lanes}x{renderWSize ve}>"

example : renderVectorType .U16 .U256 = "vector<16xi16>" := rfl
example : renderVectorType .U32 .U256 = "vector<8xi32>" := rfl
example : renderVectorType .U64 .U256 = "vector<4xi64>" := rfl
example : renderVectorType .U8 .U128  = "vector<16xi8>" := rfl

/-- Extract `(ve, ws)` from an `Ov*` op for vector-type rendering. -/
def sOp2VectorWidths : SOp2 → Option (WSize × WSize)
  | .Ovadd ve ws | .Ovsub ve ws | .Ovmul ve ws
  | .Ovlsr ve ws | .Ovlsl ve ws | .Ovasr ve ws => some (ve, ws)
  | _ => none

/-- Extract the result `WSize` from an arith-shape `SOp2`. Returns `.U64`
    as a default when the op carries no width (boolean comparisons etc.). -/
def sOp2ResultWSize : SOp2 → WSize
  | .Oadd w | .Osub w | .Omul w
  | .Oland w | .Olor w | .Olxor w
  | .Olsl w | .Olsr w | .Oasr w | .Oeq w | .Oneq w => w
  | .Odiv _ w | .Omod _ w | .Olt _ w | .Ole _ w | .Ogt _ w | .Oge _ w => w
  | .Ovadd _ w | .Ovsub _ w | .Ovmul _ w
  | .Ovlsr _ w | .Ovlsl _ w | .Ovasr _ w => w
  | _ => .U64

/-! ## §4. Expression translation

`PExpr → (EmitState → String × EmitState)`. The string is the SSA id (or
literal value) representing the expression's result. Side effects on the
state cover fresh-id allocation and line emission.

We only handle the scalar subset; everything else emits an opaque marker
with a fresh result id. -/

/-- Combine two already-emitted operand SSA ids with a binary op into a
    single MLIR line. Non-recursive helper used by `emitPExpr` for the
    `Papp2` case. Stage-2 scalar arith first; then Stage-3 vector arith;
    otherwise an opaque marker. -/
def emitPapp2Combine (op : SOp2) (id1 id2 : String) (s : EmitState) :
    String × EmitState :=
  match sOp2ToArithMnemonic op with
  | some mnemonic =>
    let ty := renderWSize (sOp2ResultWSize op)
    let (id, s) := s.fresh
    let line := s!"  {id} = {mnemonic} {id1}, {id2} : {ty}"
    (id, s.emit line)
  | none =>
    -- Try Stage-3 vector arith.
    match sOp2ToVectorArithMnemonic op, sOp2VectorWidths op with
    | some mnemonic, some (ve, ws) =>
      let ty := renderVectorType ve ws
      let (id, s) := s.fresh
      let line := s!"  {id} = {mnemonic} {id1}, {id2} : {ty}"
      (id, s.emit line)
    | _, _ =>
      -- Out-of-subset binary op: escape hatch.
      let (id, s) := s.fresh
      let line := s!"  {id} = \"catcrypt.opaque\"({id1}, {id2}) : (i64, i64) -> i64  // out-of-subset SOp2"
      (id, s.emit line)

/-- Translate a `PExpr` to (result SSA id, updated emit state).
    Structurally recursive on `PExpr`: each recursive call descends into
    a sub-expression, so termination is automatic. -/
def emitPExpr (e : PExpr) (s : EmitState) : String × EmitState :=
  match e with
  | .Pconst z =>
    -- arith.constant with width-64 default. Future: derive width from context.
    let (id, s) := s.fresh
    let line := s!"  {id} = arith.constant {z} : i64"
    (id, s.emit line)
  | .Pbool b =>
    let (id, s) := s.fresh
    let lit := if b then "1" else "0"
    let line := s!"  {id} = arith.constant {lit} : i1"
    (id, s.emit line)
  | .Pvar gv =>
    (s.lookup gv.gv.var.vname, s)
  | .Papp2 op e1 e2 =>
    let (id1, s) := emitPExpr e1 s
    let (id2, s) := emitPExpr e2 s
    emitPapp2Combine op id1 id2 s
  | e =>
    -- Escape hatch: emit an opaque marker with a fresh result.
    let (id, s) := s.fresh
    let line := s!"  {id} = \"catcrypt.opaque\"() : () -> i64  // {repr e}"
    (id, s.emit line)

/-- Translate a binary application. Stage-2 scalar arith first; if the
    op is a vector binop (Stage-3 pilot), emit the `arith.*` mnemonic at
    a `vector<n × iM>` type; otherwise emit an opaque marker.

    Defined in terms of `emitPExpr` + `emitPapp2Combine`; this preserves
    the original public API of the file (Stage 2 / 3 callers, examples). -/
def emitPapp2 (op : SOp2) (e1 e2 : PExpr) (s : EmitState) :
    String × EmitState :=
  let (id1, s) := emitPExpr e1 s
  let (id2, s) := emitPExpr e2 s
  emitPapp2Combine op id1 id2 s

/-! ## §5. Instruction / command translation

`InstrR → EmitState → EmitState`. Stage-2 handles `Cassgn` (with `Lvar`
or `Lnone`); Phase 5 adds the `scf` dialect for `Cif` / `Cfor` /
`Cwhile`. Mutually recursive with `emitCmd` because the control-flow
constructors carry nested `List InstrR` bodies that need recursive
emission.

For each control-flow op we:

* Allocate a child `EmitState` whose `lines` buffer starts empty (the
  outer state's accumulated lines are *not* visible inside the nested
  region) but inheriting `names` and `counter` so SSA ids stay fresh.
* Run `emitCmd` on the body in the child state.
* Reconstruct the region as a bracketed block of indented body lines,
  prepended/wrapped in the `scf.<op>` op header/trailer.
* Append the resulting block onto the outer state with the outer's
  `lines` preserved (we *do* keep all body lines visible in the linear
  output — the `{ ... }` braces delimit them to MLIR, not to our
  emitter, which is text-level).

This keeps the emitter total and structural — termination is automatic
because each recursive call descends into a sub-`Cmd` that is a strict
component of the outer `InstrR`. -/

mutual

/-- Translate a single instruction. Mutually recursive with `emitCmd`
    via the nested `Cmd` bodies of `Cif` / `Cfor` / `Cwhile`. -/
def emitInstrR (i : InstrR) (s : EmitState) : EmitState :=
  match i with
  | .Cassgn (.Lvar x) _ _ e =>
    let (rhsId, s) := emitPExpr e s
    s.bind x.var.vname rhsId
  | .Cassgn (.Lnone _ _) _ _ e =>
    -- A "discard" — still emit the RHS for its effect (we have none in
    -- this scalar subset, but downstream stages may rely on side effects).
    let (_, s) := emitPExpr e s
    s
  | .Cif cond cthen celse =>
    -- Emit the condition; then open an `scf.if %c -> () { then } else { else }`.
    let (condId, s) := emitPExpr cond s
    let outerLines := s.lines
    -- Recurse into THEN branch with an empty lines accumulator.
    let sThen := emitCmd cthen { s with lines := [] }
    let thenLines := sThen.getLines
    -- Recurse into ELSE branch with the THEN state (inherits counter/names).
    let sElse := emitCmd celse { sThen with lines := [] }
    let elseLines := sElse.getLines
    -- Reassemble: outer lines + scf.if header + indented bodies + trailer.
    let header := s!"  scf.if {condId} \{"
    let elseHdr := s!"  } else \{"
    let trailer := "  }"
    let indentedThen := thenLines.map (fun ln => "  " ++ ln)
    let indentedElse := elseLines.map (fun ln => "  " ++ ln)
    let newLines :=
      trailer :: (indentedElse.reverse ++ (elseHdr :: (indentedThen.reverse ++ (header :: outerLines))))
    { sElse with lines := newLines }
  | .Cfor v range body =>
    -- Emit `scf.for %ivar = %lo to %hi step %1 { body }`.
    -- For Stage 5 we ignore loop direction (UpTo only; DownTo would need
    -- explicit `step -1`) and don't model iter_args (carried state).
    let outerLines := s.lines
    -- Allocate three fresh SSA ids: %lo, %hi, %step.
    let (loId, s) := s.fresh
    let s := s.emit s!"  {loId} = arith.constant {range.lo} : index"
    let (hiId, s) := s.fresh
    let s := s.emit s!"  {hiId} = arith.constant {range.hi} : index"
    let (stepId, s) := s.fresh
    let s := s.emit s!"  {stepId} = arith.constant 1 : index"
    -- Allocate the loop-variable SSA id and bind it in the symbol table.
    let (ivarId, s) := s.fresh
    let sBody0 := s.bind v.var.vname ivarId
    -- Recurse into body with empty lines accumulator.
    let sBody := emitCmd body { sBody0 with lines := [] }
    let bodyLines := sBody.getLines
    -- The three pre-loop constants and the scf.for header / trailer.
    let preLines := s.lines.take (s.lines.length - outerLines.length)
    let preLinesReversed := preLines
    let header := s!"  scf.for {ivarId} = {loId} to {hiId} step {stepId} \{"
    let trailer := "  }"
    let indentedBody := bodyLines.map (fun ln => "  " ++ ln)
    let newLines :=
      trailer :: (indentedBody.reverse ++ (header :: (preLinesReversed ++ outerLines)))
    { sBody with lines := newLines }
  | .Cwhile cbefore cond cafter =>
    -- Emit `scf.while () : () -> () { ... ; scf.condition(%c) } do { ... ; scf.yield }`.
    -- We do not model loop-carried values; the two regions just thread
    -- side effects (textually).
    let outerLines := s.lines
    -- Before-region (computes the condition).
    let sBefore0 := emitCmd cbefore { s with lines := [] }
    let (condId, sBefore) := emitPExpr cond sBefore0
    let beforeLines := sBefore.getLines ++ [s!"  scf.condition({condId})"]
    -- After-region (loop body).
    let sAfter := emitCmd cafter { sBefore with lines := [] }
    let afterLines := sAfter.getLines ++ ["  scf.yield"]
    -- Reassemble.
    let header := "  scf.while : () -> () {"
    let midHdr := "  } do {"
    let trailer := "  }"
    let indentedBefore := beforeLines.map (fun ln => "  " ++ ln)
    let indentedAfter := afterLines.map (fun ln => "  " ++ ln)
    let newLines :=
      trailer :: (indentedAfter.reverse ++ (midHdr :: (indentedBefore.reverse ++ (header :: outerLines))))
    { sAfter with lines := newLines }
  | _ =>
    -- Catch-all: opaque marker for arrays / calls / ops.
    s.emit s!"  \"catcrypt.opaque\"() : () -> ()  // unsupported InstrR"

/-- Translate a sequence of instructions (a `Cmd`). Mutually recursive
    with `emitInstrR` because the latter recurses into nested `Cmd`s
    inside control-flow constructors. -/
def emitCmd (cmd : Cmd) (s : EmitState) : EmitState :=
  match cmd with
  | [] => s
  | i :: rest => emitCmd rest (emitInstrR i s)

end

/-! ## §6. Function-shaped wrapper

Wrap a `Cmd` body inside a `func.func @<name>(...) -> i64 { ... func.return ... }`
shell, with each parameter pre-bound to a `%argN`-style SSA name.

The function returns a single `i64` whose value is bound to the first
result variable, if any. Multi-return is deferred — the existing #145
`MultiReturnCom.lean` is the future target. -/

/-- Bind a list of parameter names to `%arg0`, `%arg1`, ... in the
    starting state. Returns the rendered MLIR parameter list and the
    updated state. -/
def bindParams (params : List String) (s : EmitState) :
    String × EmitState :=
  let f : Nat × List String × EmitState → String → Nat × List String × EmitState :=
    fun (idx, accStrs, st) name =>
      let arg := s!"%arg{idx}"
      let st := st.bind name arg
      let renderedArg := s!"{arg} : i64"
      (idx + 1, renderedArg :: accStrs, st)
  let (_, revArgs, s) := params.foldl f (0, [], s)
  let argsStr := String.intercalate ", " revArgs.reverse
  (argsStr, s)

/-- Emit a function `@name(params) -> i64` with body `cmd` and returning
    the SSA id currently bound to `retVar` (or `0` if unbound). -/
def emitFunc (name : String) (params : List String) (cmd : Cmd)
    (retVar : String) : String :=
  let s := EmitState.init
  let (argsStr, s) := bindParams params s
  let s := emitCmd cmd s
  let retId := s.lookup retVar
  let body := String.intercalate "\n" s.getLines
  s!"func.func @{name}({argsStr}) -> i64 \{
{body}
  func.return {retId} : i64
}"

/-! ## §7. Sanity tests / examples

A two-instruction `Cmd` that adds two parameters and binds the result, to
check the Stage-2 emitter produces well-shaped MLIR. -/

/-- Sample Jasmin variable. -/
private def mkVar (name : String) : VarI :=
  { var := { vname := name, vtype := .sword .U64 }, info := {} }

/-- Sample global-variable reference. -/
private def mkGV (name : String) : GVar :=
  { gv := mkVar name, gs := false }

/-- Example: `c := a + b`, where `a`, `b` are function parameters. -/
def example_add_cmd : Cmd :=
  [ .Cassgn (.Lvar (mkVar "c")) .AT_none (.sword .U64)
            (.Papp2 (.Oadd .U64) (.Pvar (mkGV "a")) (.Pvar (mkGV "b"))) ]

/-- Emit the example function. -/
def exampleAddFuncMLIR : String :=
  emitFunc "add" ["a", "b"] example_add_cmd "c"

#eval exampleAddFuncMLIR

/-- A second example: `c := (a + b) * a` — chains two arith ops. -/
def example_addmul_cmd : Cmd :=
  [ .Cassgn (.Lvar (mkVar "t")) .AT_none (.sword .U64)
            (.Papp2 (.Oadd .U64) (.Pvar (mkGV "a")) (.Pvar (mkGV "b")))
  , .Cassgn (.Lvar (mkVar "c")) .AT_none (.sword .U64)
            (.Papp2 (.Omul .U64) (.Pvar (mkGV "t")) (.Pvar (mkGV "a"))) ]

/-- The chained-arith example. -/
def exampleAddMulFuncMLIR : String :=
  emitFunc "addmul" ["a", "b"] example_addmul_cmd "c"

#eval exampleAddMulFuncMLIR

/-! ### Stage-3 vector example: 16xi16 lane-wise add

A single `Ovadd U16 U256` over two 256-bit registers, modelled as
`vector<16xi16>` SIMD add. This is the canonical Stage-3 pilot: the same
op shape used by every 16-lane SIMD primitive (ChaCha20 quarter-round
lane-wise add, ML-KEM polynomial coefficient add, lattice-arith
coefficient add, etc.).

### End-to-end validation (2026-05-28)

The vector body is taken end-to-end through the MLIR toolchain at
`mlir-opt-20` / `llc-18` (system LLVM 20 / 18 respectively):

```
arith.addi %a, %b : vector<16xi16>      -- Stage-3 emit
  ↓  mlir-opt-20 --convert-vector-to-llvm --convert-arith-to-llvm
                 --convert-func-to-llvm --reconcile-unrealized-casts
llvm.add %a, %b : vector<16xi16>        -- LLVM dialect
  ↓  mlir-translate-20 --mlir-to-llvmir
%3 = add <16 x i16> %0, %1              -- LLVM IR
  ↓  llc-18 -O3 -mattr=+avx2
vpaddw %ymm1, %ymm0, %ymm0              -- AVX2 asm
```

That matches the instruction the existing jasmin path emits as
`#VPADDW_16u16_256` (256-bit, 16 × i16 lane-wise add via `vpaddw` on
`ymm` registers). The fndsa emit elsewhere in the bench tree
(`bench/fndsa_compare/gen/fndsa_512_verify.s`) uses the 8 × i16 / `xmm`
variant of the same instruction family.

**Bit-for-bit comparison with jasmin output**: the existing jasmin chain
emits `vpaddw` inside a larger context (register-allocation slot
decisions, load/store wrapping). Comparing the *instruction* is the
right granularity here: both pipelines produce `vpaddw ymm, ymm, ymm`
for 16xi16 lane-wise add. Diff in scheduling / regalloc is downstream
of the MLIR pipeline (`llc` decides slot assignment, jasmin uses its
own RA). -/

/-- Example: `c := a + b` where `a`, `b`, `c` are 256-bit registers
    interpreted as `16 × i16` SIMD lanes. -/
def example_vadd16x16_cmd : Cmd :=
  [ .Cassgn (.Lvar (mkVar "c")) .AT_none (.sword .U256)
            (.Papp2 (.Ovadd .U16 .U256) (.Pvar (mkGV "a")) (.Pvar (mkGV "b"))) ]

/-- Emit the 16-lane vector add. -/
def exampleVadd16x16MLIR : String :=
  emitFunc "vadd16x16" ["a", "b"] example_vadd16x16_cmd "c"

#eval exampleVadd16x16MLIR

/-- A chained vector example: `t := a + b; c := t * a` — two lane-wise
    arith ops at `vector<8xi32>` (a common ML-KEM / lattice shape). -/
def example_vmuladd8x32_cmd : Cmd :=
  [ .Cassgn (.Lvar (mkVar "t")) .AT_none (.sword .U256)
            (.Papp2 (.Ovadd .U32 .U256) (.Pvar (mkGV "a")) (.Pvar (mkGV "b")))
  , .Cassgn (.Lvar (mkVar "c")) .AT_none (.sword .U256)
            (.Papp2 (.Ovmul .U32 .U256) (.Pvar (mkGV "t")) (.Pvar (mkGV "a"))) ]

/-- The chained-vector-arith example. -/
def exampleVmuladd8x32MLIR : String :=
  emitFunc "vmuladd8x32" ["a", "b"] example_vmuladd8x32_cmd "c"

#eval exampleVmuladd8x32MLIR

/-! ### Phase-5 control-flow example: `scf.for` over a four-element vector add

A canonical pre-vectoriser shape: a length-4 loop that updates a single
output variable. Emits an `scf.for` with three preamble constants
(`%lo`, `%hi`, `%step`) and a single-line body. The example exercises
`Cfor` plus a nested `Cassgn`; downstream of `mlir-opt
--convert-scf-to-cf --convert-arith-to-llvm` this lowers to a `cf.br` /
`cf.cond_br` loop that LLVM `llc` then jumps to unroll/vectorise. -/

/-- Example: `for i in 0..4 { x := a + b }` — a four-iteration loop that
    overwrites `x` each round. Single-instruction body so the emit table
    is easy to eyeball. -/
def example_for_cmd : Cmd :=
  [ .Cfor (mkVar "i") { dir := .UpTo, lo := 0, hi := 4 }
      [ .Cassgn (.Lvar (mkVar "x")) .AT_none (.sword .U64)
                (.Papp2 (.Oadd .U64) (.Pvar (mkGV "a")) (.Pvar (mkGV "b"))) ] ]

/-- The control-flow example function. -/
def exampleForFuncMLIR : String :=
  emitFunc "for_loop" ["a", "b"] example_for_cmd "x"

#eval exampleForFuncMLIR

/-- Example: `if cond then x := a + b else x := a - b` — a two-branch
    selector with non-trivial bodies (so each branch emits one arith
    line). -/
def example_if_cmd : Cmd :=
  [ .Cassgn (.Lvar (mkVar "cond")) .AT_none (.sword .U64)
            (.Pvar (mkGV "a"))
  , .Cif (.Pvar (mkGV "cond"))
      [ .Cassgn (.Lvar (mkVar "x")) .AT_none (.sword .U64)
                (.Papp2 (.Oadd .U64) (.Pvar (mkGV "a")) (.Pvar (mkGV "b"))) ]
      [ .Cassgn (.Lvar (mkVar "x")) .AT_none (.sword .U64)
                (.Papp2 (.Osub .U64) (.Pvar (mkGV "a")) (.Pvar (mkGV "b"))) ] ]

/-- The if-then-else example function. -/
def exampleIfFuncMLIR : String :=
  emitFunc "if_branch" ["a", "b"] example_if_cmd "x"

#eval exampleIfFuncMLIR

/-- Example: `while (cond) { x := a + b }` — a single-condition,
    single-body loop. Emits an `scf.while` with the condition computed
    in the `before` region and the body in the `after` region. -/
def example_while_cmd : Cmd :=
  [ .Cwhile
      [ .Cassgn (.Lvar (mkVar "cond")) .AT_none (.sword .U64) (.Pvar (mkGV "a")) ]
      (.Pvar (mkGV "cond"))
      [ .Cassgn (.Lvar (mkVar "x")) .AT_none (.sword .U64)
                (.Papp2 (.Oadd .U64) (.Pvar (mkGV "a")) (.Pvar (mkGV "b"))) ] ]

/-- The while-loop example function. -/
def exampleWhileFuncMLIR : String :=
  emitFunc "while_loop" ["a", "b"] example_while_cmd "x"

#eval exampleWhileFuncMLIR

/-! ## §8. Translation coverage summary

| Source constructor      | Stage 2 handling                  |
|-------------------------|-----------------------------------|
| `Cmd = List InstrR`     | sequential fold via `emitCmd`     |
| `Cassgn (Lvar _) _ _ e` | translate `e`, bind RHS to LHS    |
| `Cassgn (Lnone _) _ _ e`| translate `e` for effect          |
| `Cassgn _ _ _ _` other  | opaque marker                     |
| `Pconst z`              | `arith.constant z : i64`          |
| `Pbool b`               | `arith.constant 0/1 : i1`         |
| `Pvar gv`               | symbol-table lookup               |
| `Papp2 (Oadd w) _ _`    | `arith.addi`                      |
| `Papp2 (Osub w) _ _`    | `arith.subi`                      |
| `Papp2 (Omul w) _ _`    | `arith.muli`                      |
| `Papp2 (Oland w) _ _`   | `arith.andi`                      |
| `Papp2 (Olor w) _ _`    | `arith.ori`                       |
| `Papp2 (Olxor w) _ _`   | `arith.xori`                      |
| `Papp2 (Olsl w) _ _`    | `arith.shli`                      |
| `Papp2 (Olsr w) _ _`    | `arith.shrui`                     |
| `Papp2 (Ovadd ve ws)`   | `arith.addi` at `vector<n×iM>`    |
| `Papp2 (Ovsub ve ws)`   | `arith.subi` at `vector<n×iM>`    |
| `Papp2 (Ovmul ve ws)`   | `arith.muli` at `vector<n×iM>`    |
| `Papp2 (Ovlsr ve ws)`   | `arith.shrui` at `vector<n×iM>`   |
| `Papp2 (Ovlsl ve ws)`   | `arith.shli` at `vector<n×iM>`    |
| `Papp2 (Ovasr ve ws)`   | `arith.shrsi` at `vector<n×iM>`   |
| `Papp2 _ _ _` other     | opaque marker                     |
| `Cif cond cthen celse`  | `scf.if %cond { ... } else { ... }` (Phase 5) |
| `Cfor v range body`     | `scf.for %v = %lo to %hi step %1 { ... }` (Phase 5) |
| `Cwhile cb cond ca`     | `scf.while { ... cb ; scf.condition(cond) } do { ... ca ; scf.yield }` (Phase 5) |
| `Copn / Ccall`          | opaque marker (deferred Stage 3+) |
| `Papp1 / PappN`         | opaque marker (deferred)          |
| `Pget / Psub / Pload`   | opaque marker (deferred Stage 3+) |

Eight `Papp2` constructors and three `PExpr` head shapes map to
registered `arith.*` ops. Everything else routes to `catcrypt.opaque`,
which `mlir-opt --allow-unregistered-dialect` accepts.
-/

/-! ## §9. Canonicalising emit entry (round-out canonicalize wired into emit)

`emitFunc` (§6) lowers a `Cmd` to MLIR text with **no** `Com`-level
canonicalisation pass run first. The verified, denotation-preserving
algebraic-canonicalisation transform lives one IR up, on the typed VIR
`Com jasminDialect`: `Optimizer.Rewrite.ComPipeline.comAlgebraicPipeline`
(peephole, then fuel-bounded equality saturation), whose end-to-end
denotation preservation is `comAlgebraicPipeline_denote`.

This section wires that pass *in front of* the MLIR emit. The canonical
optimisation lives on the typed `Com jasminDialect Γ t`; the §6 emitter
consumes the concrete Jasmin `Cmd` (`List InstrR`). They are distinct IRs,
so `emitFuncCanon` is parametric over the caller-supplied
`Com jasminDialect Γ t → Cmd` lowering `lower` (the project's
`Com[jasminDialect] → LowCT → toJasminCmd` path; no single combined lowering
function exists in this module, hence it is passed in rather than fixed).
The flow is:

```
Com jasminDialect Γ t
  ──comAlgebraicPipeline fuel · k──▶  Com jasminDialect Γ t   (canonicalised)
  ──lower──▶                          Cmd
  ──emitFunc──▶                       MLIR text
```

The accompanying lemma `emitFuncCanon_denote_eq` carries
`comAlgebraicPipeline_denote`: under a known-constant environment `k`
consistent with the valuation, the canonicalised `Com` fed to `lower`
denotes exactly the source `Com`. This is the denotation guarantee that the
canonicalise step did not change program meaning before emission. -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.ComCanonical

/-- Canonicalising MLIR emit entry. Runs the verified general optimizer
    `comCanonical fuel k ·` — algebraic canonicalisation (peephole + equality
    saturation) followed by the fold/CSE/uncompute/DCE clean-up stack — on the
    typed `Com jasminDialect` *before* lowering (`lower`) it to a concrete
    `Cmd` and emitting via `emitFunc`. Identical output shape to `emitFunc`;
    only the `Com` it lowers has been optimized first. Every emitted kernel
    flows through this pass. -/
def emitFuncCanon {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (com : Com jasminDialect Γ t) (k : KEnv Γ)
    (lower : Com jasminDialect Γ t → Cmd)
    (name : String) (params : List String) (retVar : String) : String :=
  emitFunc name params (lower (comCanonical fuel k com)) retVar

/-- **The general optimizer is denotation-preserving before emit.** The `Com`
    that `emitFuncCanon` lowers — `comCanonical fuel k com` — denotes exactly
    the source `com`, for any known-constant environment `k` consistent with
    the valuation `V`. This is `comCanonical_denote` re-exported at the emit
    entry: the verified guarantee that wiring the full optimizer in front of
    `emitFunc` does not change program meaning. -/
theorem emitFuncCanon_denote_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (com : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (comCanonical fuel k com).denote V = com.denote V :=
  comCanonical_denote fuel k com V hk

/-- **The general optimizer preserves constant-time-safety before emit.** The
    optimized `Com` is CT-safe exactly when the source is — the optimizer never
    introduces a secret-dependent branch (`comCanonical_ctSafe`). -/
theorem emitFuncCanon_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (com : Com jasminDialect Γ t) (k : KEnv Γ) :
    ctSafeComJ (comCanonical fuel k com) = ctSafeComJ com :=
  comCanonical_ctSafe fuel k com

end CatCrypt.Crypto.SecureCompilation.MLIRBackend
