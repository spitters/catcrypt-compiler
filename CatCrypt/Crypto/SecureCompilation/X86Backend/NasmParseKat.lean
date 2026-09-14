/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock

/-!
# Round-trip and coverage check of the NASM parser on CryptOpt assembly

A program over two CryptOpt Curve25519 kernels, run from the package root:

```
lake exe nasm-parse-kat
```

* `bench/cryptopt/fiat_curve25519_solinas_square.asm` and
  `bench/cryptopt/fiat_curve25519_carry_mul.asm`, every instruction of which has a
  `JInstr` constructor: each whole file must parse, print back to its canonical
  text, and equal its expected block.

For every instruction line of a file it compares `printInstr (toJInstr line)`
with the canonical text of the line, lists the lines whose instruction has no
`JInstr` constructor with the reason, and prints per-mnemonic counts of mapped
and unmapped lines. A final `ret` is counted as the terminator `parseNasm`
accepts. It then runs `parseNasm` on the whole file and, when that succeeds,
compares `printNasm` of the result with `canonicalNasm` of the file. For a file
with an expected block, the parsed list must also equal that block: the solinas
square file must parse to `SolinasSquareBlock.solinasSquareBlock` and the carry_mul
file to `CarryMulBlock.carryMulBlock`, the literals the proofs about the kernels
unfold. The comparison is on the `repr` of both
lists, since `JInstr` derives `Repr` and its `DecidableEq` instance lives in a
module this program does not import.

Exit status: `0` when every file meets its expectation; `1` when the lexical
layer accepts every file and every mapped line prints back to its canonical
text, but a file expected to parse completely has an instruction with no
`JInstr` constructor; `2` when a file cannot be read or lexed, a mapped line
prints back to a different text, `printNasm (parseNasm file)` differs from
`canonicalNasm file`, or the parsed list differs from the expected block.

## Main definitions

* `Target`, `targets`: the input files, relative to the package root, with
  whether each must parse completely and the block it must parse to, if any.
* `LineResult`, `checkLine`: the per-line outcome.
* `checkFile`: the checks on one file, returning its exit status.
* `main`: runs `checkFile` on every target and reports.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParseKat

open CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock (solinasSquareBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock (carryMulBlock)

/-- An input file, relative to the package root, whether every instruction of it
    must have a `JInstr` constructor, and the block `parseNasm` must return on
    it, if any. -/
structure Target where
  path : System.FilePath
  complete : Bool
  expected : Option (List (JInstr 64)) := none

/-- The input files. -/
def targets : List Target :=
  [ { path := "bench/cryptopt/fiat_curve25519_solinas_square.asm", complete := true,
      expected := some solinasSquareBlock },
    { path := "bench/cryptopt/fiat_curve25519_carry_mul.asm", complete := true,
      expected := some carryMulBlock } ]

/-- The outcome of one source line: no instruction, the final `ret`, a mapped
    instruction whose printed text agrees or disagrees with the canonical text,
    or an instruction with no `JInstr` constructor. -/
inductive LineResult where
  | noInstr
  | terminator
  | roundTrip (mn : String)
  | mismatch (mn canonical printed : String)
  | unmapped (mn canonical reason : String)
  | lexError (reason : String)

/-- Classify one source line. -/
def checkLine (ln : String) : LineResult :=
  match lexLine ln with
  | .error e => .lexError e
  | .ok (.instr mn ops) =>
      if isRet mn ops then .terminator else
      let canon := printInstrSyntax mn ops
      match toJInstr mn ops with
      | .error e => .unmapped mn canon e
      | .ok i =>
          match printInstr i with
          | .ok p => if p == canon then .roundTrip mn else .mismatch mn canon p
          | .error e => .mismatch mn canon s!"<print error: {e}>"
  | .ok _ => .noInstr

/-- Increment the mapped or unmapped count of a mnemonic in an association list
    of `(mnemonic, mapped, unmapped)`. -/
def bump (acc : List (String × Nat × Nat)) (mn : String) (mapped : Bool) :
    List (String × Nat × Nat) :=
  if acc.any (·.1 == mn) then
    acc.map fun (m, a, b) =>
      if m == mn then (if mapped then (m, a + 1, b) else (m, a, b + 1)) else (m, a, b)
  else acc ++ [(mn, if mapped then 1 else 0, if mapped then 0 else 1)]

/-- Run the per-line round-trip and coverage check and the whole-file parse on
    one target, returning its exit status as described in the module
    docstring. -/
def checkFile (t : Target) : IO UInt32 := do
  let src ← try IO.FS.readFile t.path catch e => do
    IO.eprintln s!"nasm-parse-kat: cannot read {t.path}: {e}"
    return 2
  IO.println s!"{t.path}:"
  let mut counts : List (String × Nat × Nat) := []
  let mut bad := false
  let mut total := 0
  let mut unmappedCount := 0
  for (n, ln) in numberedLines src do
    match checkLine ln with
    | .noInstr => pure ()
    | .terminator => IO.println s!"  line {n}: ret: block terminator"
    | .roundTrip mn =>
        total := total + 1
        counts := bump counts mn true
    | .mismatch mn canon p =>
        total := total + 1
        counts := bump counts mn true
        bad := true
        IO.eprintln s!"nasm-parse-kat: {t.path}: line {n}: MISMATCH\n  canonical: {canon}\n  printed:   {p}"
    | .unmapped mn canon e =>
        total := total + 1
        unmappedCount := unmappedCount + 1
        counts := bump counts mn false
        IO.println s!"  line {n}: {canon}: {e}"
    | .lexError e =>
        bad := true
        IO.eprintln s!"nasm-parse-kat: {t.path}: line {n}: lexical error: {e}"
  IO.println s!"  instructions: {total}"
  for (mn, a, b) in counts do
    IO.println s!"    {mn}: {a} mapped, {b} without a JInstr constructor"
  if bad then return 2
  match parseNasm src, canonicalNasm src with
  | .ok is, .ok canon =>
      match printNasm is with
      | .ok p =>
          if p == canon then
            IO.println s!"  {is.length} instructions parse and print back to the canonical text"
            match t.expected with
            | none => return 0
            | some blk =>
                if reprStr is == reprStr blk then
                  IO.println s!"  the parsed list equals the expected {blk.length}-instruction block"
                  return 0
                else
                  IO.eprintln s!"nasm-parse-kat: {t.path}: the parsed list differs from the expected block"
                  return 2
          else
            IO.eprintln s!"nasm-parse-kat: {t.path}: printNasm (parseNasm file) differs from canonicalNasm file"
            return 2
      | .error e =>
          IO.eprintln s!"nasm-parse-kat: {t.path}: printNasm failed: {e}"
          return 2
  | .error e, .ok _ =>
      IO.println s!"  parseNasm: {e}"
      if t.complete then return 1
      else
        IO.println s!"  {unmappedCount} instructions without a JInstr constructor"
        return 0
  | _, .error e =>
      IO.eprintln s!"nasm-parse-kat: {t.path}: canonicalNasm: {e}"
      return 2

end CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParseKat

open CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParseKat in
/-- Run `checkFile` on every target; the exit status is the largest of theirs. -/
def main : IO UInt32 := do
  let mut status : UInt32 := 0
  for t in targets do
    let s ← checkFile t
    if s > status then status := s
  return status
