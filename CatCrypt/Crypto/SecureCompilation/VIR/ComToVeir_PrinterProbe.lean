/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# Veir printer status (probe only)

## Finding

Veir ships an `IRContext OpCode → OperationPtr → IO Unit` printer family
(in `Veir/Printer.lean`), not an `IRContext → String` (or
`... → m String`) function. All public printer entries are `IO Unit` and
write to the current `stdout` via `IO.print` / `IO.println`. There is no
pure (or `m`-polymorphic) MLIR-text serializer over the pointer-graph IR.
The closest thing to a "capture" path is `Veir/Passes/PrintIR.lean`,
which redirects stdout to stderr using `IO.withStdout`; it does not
return a `String`. Consequently, path (b) (emit MLIR text from a
`Com`/`IRContext`) cannot just call an existing Veir function — a thin
`String`-producing wrapper has to be written on top of the same
pointer-graph traversal.

## Available functions (if any)

Public printer entrypoints in
`/.lake/packages/Veir/Veir/Printer.lean` (namespace `Veir.Printer`):

* `printValue            : IRContext OpCode → ValuePtr → IO Unit`  (Printer.lean:29)
* `printOpResult         : IRContext OpCode → OpResultPtr → IO Unit` (Printer.lean:42)
* `printOpResults        : IRContext OpCode → OperationPtr → IO Unit` (Printer.lean:45)
* `printOpOperands       : IRContext OpCode → OperationPtr → IO Unit` (Printer.lean:55)
* `printOperationType    : IRContext OpCode → OperationPtr → IO Unit` (Printer.lean:64)
* `printBlockOperands    : IRContext OpCode → OperationPtr → IO Unit` (Printer.lean:93)
* `printAttrDictEntry    : String → Attribute → IO Unit`            (Printer.lean:101)
* `printOpAttrDict       : IRContext OpCode → OperationPtr → IO Unit` (Printer.lean:107)
* `printOpProperties     : IRContext OpCode → OperationPtr → IO Unit` (Printer.lean:113)
* `printOpList`, `printBlock`, `printBlockList`, `printRegion`,
  `printRegions`, `printOperation` — all `IO Unit`           (Printer.lean:122–189)
* `printModule           : IRContext OpCode → OperationPtr → IO Unit` (Printer.lean:192)
* `opName                : Nat → String`                              (Printer.lean:10)

Auxiliary `toString` instances on attribute types (NOT on IR
operations / modules) live in
`/.lake/packages/Veir/Veir/IR/Attribute.lean`:

* `ArrayAttr.toString`                 (Attribute.lean:302)
* `DictionaryAttr.toString`            (Attribute.lean:318)
* `FunctionType.toString`              (Attribute.lean:327)
* `Attribute.toString`                 (Attribute.lean:352)

These cover attribute values only; they do not serialize operations,
blocks, regions, or modules.

The PrintIR pass (`Veir/Passes/PrintIR.lean:6`) uses
`IO.withStdout stdErr (Printer.printModule ctx.val op)` to redirect to
stderr but still returns `IO Unit`, not `String`.

## Gaps

What path (b) needs that Veir does not currently expose:

1. A pure (or `StateM String` / `IO String`) variant of `printModule`
   returning the MLIR text instead of effecting `IO.print`.
2. Equivalent String-returning variants of the helper printers
   (`printOperation`, `printRegion`, `printBlock`, `printOpResults`,
   `printOpOperands`, `printOperationType`, `printOpAttrDict`,
   `printOpProperties`, `printBlockOperands`, `printValue`).
3. (Optional) A `Com → IRContext × OperationPtr` lowering — assumed
   already in scope for path (b); not part of this probe.

The pointer-graph traversal logic itself is already factored: each
`print*` is a thin pass over `IRContext OpCode` accessors
(`getNumOperands!`, `getOperand!`, `getResult`, `getRegion!`, etc.).
A string-producing version is a mechanical re-spelling — substitute
`IO.print s` with appending to a `String` accumulator and thread it.

## Estimated effort if gap exists

Approximately **150–220 LoC** of new Lean code:

* `Printer.lean` is ~195 LoC of `IO Unit` traversal. A `StateM String`
  (or `String → String`-difference-list) mirror should land in a
  similar size; possibly a touch smaller because the indent/format
  helpers compose more cleanly without `IO`.
* No new proofs required — the traversal is structural and the
  pointer-graph well-formedness invariants are already discharged at
  the Veir level. The wrapper is a definition only.
* Bound assumption: reuse the existing `partial def` discipline (Veir's
  printers are all `partial`); no termination proofs needed.

If a `StateM` variant is undesirable, an even cheaper option is a
~30-line `captureIOString : IO Unit → IO String` shim using
`IO.FS.withTempFile` + `IO.withStdout` (analogous to PrintIR's
`withStdout` trick); this trades purity for one extra `IO` and reuses
`Printer.printModule` verbatim. Estimated 25–40 LoC.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

/-- Placeholder marker — this file is documentation only. -/
theorem printerProbe_compiles : True := trivial

end CatCrypt.Crypto.SecureCompilation.VIR
