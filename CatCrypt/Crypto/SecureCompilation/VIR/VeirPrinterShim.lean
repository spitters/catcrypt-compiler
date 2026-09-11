/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Veir.Printer

/-!
# Veir Printer Shim — `IO Unit` → `IO String`

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

Veir's `Veir.Printer.printModule` (Printer.lean:192) emits MLIR text
via `IO.print` / `IO.println` (side-effects on stdout).  It has no
pure `IRContext → String` form.

This shim wraps `printModule` to **capture stdout output to a
String**, giving us an `IO String` interface for code-generation use.

## Usage

```lean
open CatCrypt.Crypto.SecureCompilation.VIR.VeirPrinterShim
example (ctx : Veir.IRContext Veir.OpCode) (op : Veir.OperationPtr) :
    IO Unit := do
  let mlirText ← printModuleToString ctx op
  IO.println s!"Emitted MLIR:\n{mlirText}"
```

## Implementation

Lean 4's `IO.FS.withTempFile` (or its `IO.withStdout`/`IO.print` pair)
lets us redirect stdout to a file handle, run the side-effecting
printer, then read the captured text back.

We use the simplest reliable approach: redirect stdout to a temp
file, run `printModule`, restore stdout, read the file as a String.

## When to use vs a pure mirror

This shim costs one tempfile alloc + read per call.  Fine for
end-of-pipeline emission (write `.mlir` file, hand to `mlir-opt` /
`mlir-translate`).

If you need MLIR text **inside a proof** (e.g. proving a property of
the emitted output), the IO monad isn't usable — you'd need the
~150-220 LoC pure mirror of `Veir.Printer` documented in
`ComToVeir_PrinterProbe.lean`.

## Path-(b) integration

Combine with `lowerClosedCom` from `ComToVeir.lean`:

```lean
def lowerComToMLIRText {d : Dialect} (com : Com d ... t)
    [ToVeirOp d O] [ToVeirTy d] [Veir.HasOpInfo O] : IO String := do
  let (rootOp, ctx) := (lowerClosedCom com).run Veir.IRContext.empty
  printModuleToString ctx rootOp
```

(`lowerComToMLIRText` itself isn't defined here — depends on
`ComToVeir_CatCryptDialect.lean` which is currently blocked on the
Veir-Mathlib import wall.  Wire it in once that wall is lifted.)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VeirPrinterShim

/-- Capture stdout output of an `IO Unit` action into a `String`.

    Uses a tempfile + stdout redirection.  On any exception, the
    tempfile is removed and the exception is re-raised. -/
def captureStdout (action : IO Unit) : IO String := do
  let tmpDir ← IO.currentDir
  let tmpPath := tmpDir / s!"veir-print-{← IO.rand 0 (2^31 - 1)}.tmp"
  let handle ← IO.FS.Handle.mk tmpPath .write
  let savedStdout ← IO.setStdout (IO.FS.Stream.ofHandle handle)
  try
    action
    handle.flush
    let _ ← IO.setStdout savedStdout
    let content ← IO.FS.readFile tmpPath
    IO.FS.removeFile tmpPath
    return content
  catch e =>
    let _ ← IO.setStdout savedStdout
    -- Best-effort cleanup; ignore failure to remove.
    try IO.FS.removeFile tmpPath catch _ => pure ()
    throw e

/-- Run `Veir.Printer.printModule` and capture its output as a String. -/
def printModuleToString
    (ctx : Veir.IRContext Veir.OpCode) (op : Veir.OperationPtr) :
    IO String :=
  captureStdout (Veir.Printer.printModule ctx op)

/-- Convenience: print to a file path directly without going through
    String. Useful when the next pipeline step takes a file path
    (`mlir-opt`/`mlir-translate`). -/
def printModuleToFile
    (ctx : Veir.IRContext Veir.OpCode) (op : Veir.OperationPtr)
    (path : System.FilePath) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .write
  let savedStdout ← IO.setStdout (IO.FS.Stream.ofHandle handle)
  try
    Veir.Printer.printModule ctx op
    handle.flush
    let _ ← IO.setStdout savedStdout
  catch e =>
    let _ ← IO.setStdout savedStdout
    throw e

end CatCrypt.Crypto.SecureCompilation.VIR.VeirPrinterShim
