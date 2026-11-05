/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject
import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Compiled

set_option autoImplicit false
set_option compiler.extract_closed false

/-!
# The rows of the linked-kernel emitters and their command line

A row of an emitter names an object file, its global symbol and a call that returns the frame
size of the code, the bytes and the read-only flag, or `none` when the compiler refuses the
program. `runRow` evaluates the call and writes the bytes as an ELF64 relocatable object
(`ElfObject.buildElfObject`) with one global symbol; `runCli` is the command line of an emitter
over its rows and its frame programs. The executable `linked-kernel-emit`
(`LinkedKernelEmitMain`) is one such emitter.

The command line:

* `--list`: the row names, one per line.
* `--only <row>`: the row named `row` alone; one row per process is the intended use.
  Without `--only` every row runs.
* `--stage <s> <row>`: for a frame row, the node count of the program after a prefix of the
  narrow-word stages (`src`, `widen`, `mask`, `dce`) and the wall time in milliseconds; it
  measures the stages one process at a time.

A row prints one tab-separated line: the row name, `yes` or `no`, the frame size of the code,
the byte count, the read-only flag of `frameCompile` (`-` for a compiler row), and the wall
time of the call in milliseconds. A refused row prints `refused` and the process exits with code 3.

## Main definitions

* `Row`: a row, with its name, symbol, object path and call.
* `rowFrameCompile`, `aeneasBytes`: the calls of a frame row and of a row of the Aeneas front.
* `runRow`: run one row and write its bytes as an ELF object.
* `FrameProg`, `stageNodes`: a straight-line program of a frame row and its node count after
  the narrow-word stages.
* `runCli`: the command line of an emitter.
-/

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.LinkedKernelEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject (buildElfObject)
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords (widenJ maskElim)

/-- The result of a row: the frame size of the code, the bytes, and the read-only flag, the
    first and the last as printed. -/
abbrev Out := Option (String × List (BitVec 8) × String)

/-- One row: its name, the symbol and the path of its object, and the call. -/
structure Row where
  /-- The row name. -/
  name : String
  /-- The global symbol of the object. -/
  sym : String
  /-- The path of the object, relative to the repository root. -/
  path : System.FilePath
  /-- The call of the back half. -/
  call : Unit → Out

/-- `frameCompile` without its printed program. -/
def rowFrameCompile (σ : AbiLayout) (fname : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : Out :=
  (frameCompile σ (nfAbiNames fname σ) p).map fun (F, _, bs, ro) => (toString F, bs, toString ro)

/-- The bytes of the compiler of the Aeneas front on a source under a layout. -/
def aeneasBytes (s : AeneasFront.AeSrc) (σ : AbiLayout) (fname : String) : Out :=
  (AeneasFront.aeneasEntry.compileR s σ fname).map fun (_, bs) => ("-", bs, "-")

/-- The bytes as a byte array. -/
def objectByteArray (bs : List (BitVec 8)) : ByteArray :=
  ByteArray.mk (bs.map fun b => b.toNat.toUInt8).toArray

/-- Runs the row `r`: prints its line, and writes its object when the call is accepted;
    `false` when the call is refused. -/
def runRow (r : Row) : IO Bool := do
  let t0 ← IO.monoMsNow
  let res ← IO.lazyPure fun _ => r.call ()
  let t1 ← IO.monoMsNow
  let out ← IO.getStdout
  match res with
  | some (F, bs, ro) =>
      out.putStrLn ("\t".intercalate
        [r.name, "yes", F, toString bs.length, ro, toString (t1 - t0)])
      (← IO.getStdout).flush
      if let some d := r.path.parent then IO.FS.createDirAll d
      IO.FS.writeBinFile r.path (objectByteArray (buildElfObject r.sym bs))
      return true
  | none =>
      out.putStrLn ("\t".intercalate [r.name, "no", "refused", toString (t1 - t0)])
      (← IO.getStdout).flush
      return false

/-- A straight-line program of a frame row, with its context and result type. -/
structure FrameProg where
  /-- The context. -/
  Γ : Ctxt jasminDialect
  /-- The result type. -/
  t : JasminTy
  /-- The program. -/
  p : NFProg jasminDialect Γ [t]

/-- The number of bindings, regions and returns of a program. -/
def nodes {Γ : Ctxt jasminDialect} {ts : List JasminTy} : NFProg jasminDialect Γ ts → Nat
  | .ret _ => 1
  | .var _ k => nodes k + 1
  | .forLoop _ _ b k => nodes b + nodes k + 1
  | .ifThenElse _ a b k => nodes a + nodes b + nodes k + 1
  | .whileLoop _ b k => nodes b + nodes k + 1
  | .call _ _ k => nodes k + 1

/-- The node count after a prefix of the narrow-word stages: `widen` (`widenJ`), `mask`
    (then `maskElim`), `dce` (then `NFProg.dce`); `src` counts the source. -/
def stageNodes (st : String) (fp : FrameProg) : Option Nat :=
  match st with
  | "src" => some (nodes fp.p)
  | "widen" => (widenJ fp.p).map nodes
  | "mask" => (widenJ fp.p).map fun q => nodes (maskElim q)
  | "dce" => (widenJ fp.p).map fun q => nodes (NFProg.dce (maskElim q))
  | _ => none

/-- The command line of the emitter `exe` over the rows `rows` and the frame programs
    `frameProgs` (module docstring). -/
def runCli (exe : String) (rows : List Row)
    (frameProgs : List (String × (Unit → Option FrameProg))) (args : List String) :
    IO UInt32 := do
  match args with
  | ["--list"] =>
      for r in rows do IO.println r.name
      return 0
  | ["--only", nm] =>
      match rows.find? (·.name == nm) with
      | some r => return if (← runRow r) then 0 else 3
      | none => throw (IO.userError s!"{exe}: no row named {nm}")
  | [] =>
      let mut ok := true
      for r in rows do
        ok := (← runRow r) && ok
      return if ok then 0 else 3
  | ["--stage", st, nm] =>
      match frameProgs.find? (·.1 == nm) with
      | some (_, mk) =>
          let t0 ← IO.monoMsNow
          let res ← IO.lazyPure fun _ => (mk ()).bind (stageNodes st)
          let t1 ← IO.monoMsNow
          IO.println ("\t".intercalate [nm, st, toString res, toString (t1 - t0)])
          return if res.isSome then 0 else 3
      | none => throw (IO.userError s!"{exe}: no frame row named {nm}")
  | _ => throw (IO.userError
      s!"{exe}: usage: [--list | --only <row> | --stage <src|widen|mask|dce> <row>]")

end CatCrypt.Crypto.SecureCompilation.HashTemplate.LinkedKernelEmit
