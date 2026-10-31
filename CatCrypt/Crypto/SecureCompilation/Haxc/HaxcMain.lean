/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.CensusCore
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import HaxLean.CertifiedTExprs

set_option autoImplicit false
set_option compiler.extract_closed false

/-!
# `haxc`: the hax compiler on a hax frontend export

The root of `lake exe haxc`, imported by no module. The program reads a hax frontend export
(`hax_frontend_export.json`, written by `cargo hax json`) at run time, computes the typed
extraction of every function of the crate, and runs `compileA` (`Haxc/ComposeV1.lean`) on
one function of it:

```
haxc <hax_frontend_export.json> [--fn NAME] [--name CRATE]
```

## Main definitions

* `exportCrate`: the crate of the extracted functions, as the census takes it.
* `refusalReport`: the first refusing stage of `compileA` and its construct.
* `main`: the command line.

## The typed extraction

The functions of the export are `Hax.certifiedTExprs` (`HaxLean/CertifiedTExprs.lean`) of
the export text under the options of `scripts/reextract.sh` (no `--emit-classes`, no
`--emit-contracts`, no `--nominal-crates`, no function filter): the terms
`haxpipeT --hax --emit-certified` prints as the `f_texpr` literals of an extraction module,
computed by the definitions `haxpipeT` and `toLeanCertifiedFileTyped` run. An export with a
call through `&mut` outside the write-back rewrite has no extraction, as for `haxpipeT`.

## The compilation

The crate (`exportCrate`) has as constants, declarations and functions all the extracted
functions; the module of the function is `crateModule` of that crate and the layout is
`deriveAbi` with the literal constants of the crate bound, as `censusRow` computes them for
a function of the census. On a result of `compileA` the program prints the AT&T assembly of
the returned `Lprog` (`renderLprogAtt`) on standard output and the length of the machine
code on standard error, and exits `0`. On a refusal it prints the first refusing stage and
its construct as the census reports them (`censusRow`, `pipeRun`) and exits `2`. The
target is x86-64 only.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.HaxcCli

open CatCrypt.Crypto.SecureCompilation.Haxc.Census

/-- The crate of an extraction: every extracted function is a constant (a literal one is
    bound by `deriveAbi` and `crateModule`), a declaration and a function of the crate. -/
def exportCrate (name : String) (fs : List (String × _root_.Hax.TExpr)) : Crate where
  name := name
  consts := fs
  defs := fs.map (·.1)
  fns := fs

/-- The options of the command line: the export, the function, the crate name. -/
structure Opts where
  export? : Option String := none
  fn? : Option String := none
  name : String := "crate"

/-- The options of a command line. -/
def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--fn" :: f :: rest, o => parseOpts rest { o with fn? := some f }
  | "--name" :: n :: rest, o => parseOpts rest { o with name := n }
  | a :: rest, o =>
      if a.startsWith "-" then .error s!"unknown option {a}"
      else parseOpts rest { o with export? := some a }

/-- The usage line. -/
def usage : String :=
  "usage: haxc <hax_frontend_export.json> [--fn NAME] [--name CRATE]\n" ++
  "Runs compileA on the function NAME (default: the last extracted function) and prints\n" ++
  "its x86-64 AT&T assembly; exit 2 when compileA refuses it."

/-- The report of a refusal of `compileA` on the function `fname` of the crate `c`: the first
    refusing stage and its construct (`censusRow`), the stage under the widened layout when
    the layout is refused, and the reason `regionWhy` when there is one. -/
def refusalReport (c : Crate) (fname : String) (te : _root_.Hax.TExpr) : List String :=
  let r := censusRow c fname te
  [s!"haxc: {fname}: refused at stage {r.stage}: {r.construct}"] ++
    (if r.stage == "ABI" then
      [s!"haxc: {fname}: under the widened layout: {r.wideStage}: {r.wideConstruct}"]
    else []) ++
    (match r.run with
      | some run => if run.regionWhy.isEmpty then [] else [s!"haxc: {fname}: {run.regionWhy}"]
      | none => [])

end CatCrypt.Crypto.SecureCompilation.Haxc.HaxcCli

open CatCrypt.Crypto.SecureCompilation.Haxc.HaxcCli
  CatCrypt.Crypto.SecureCompilation.Haxc.Census in
/-- Compile one function of a hax frontend export with `compileA`: the assembly on standard
    output and exit `0`, or the refusing stage on standard error and exit `2`; exit `1` on a
    usage error or an export without extraction. -/
def main (args : List String) : IO UInt32 := do
  match parseOpts args {} with
  | .error e =>
      IO.eprintln s!"haxc: {e}\n{usage}"
      return 1
  | .ok o =>
      let some path := o.export? | do
        IO.eprintln usage
        return 1
      let input ← IO.FS.readFile path
      match _root_.Hax.certifiedTExprs input with
      | .error e =>
          IO.eprintln s!"haxc: {e}"
          return 1
      | .ok fs =>
          let names := fs.map (·.1)
          let listed := " ".intercalate names
          let some fname := o.fn? <|> names.getLast? | do
            IO.eprintln "haxc: the export has no extracted function"
            return 1
          if o.fn?.isNone then
            IO.eprintln s!"haxc: no --fn given; compiling '{fname}'. Functions: {listed}"
          let some te := fs.lookup fname | do
            IO.eprintln s!"haxc: no function '{fname}'. Functions: {listed}"
            return 1
          let c := exportCrate o.name fs
          let res : Option (CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog ×
              List (BitVec 8)) :=
            match deriveAbi false c.consts te with
            | .ok σ =>
                match crateModule c te with
                | .ok m => CatCrypt.Crypto.SecureCompilation.Haxc.compileA m σ fname
                | .error _ => none
            | .error _ => none
          match res with
          | some (P, bytes) =>
              IO.println
                (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt P)
              IO.eprintln s!"haxc: {fname}: {bytes.length} bytes of x86-64 machine code"
              return 0
          | none =>
              for l in refusalReport c fname te do IO.eprintln l
              return 2
