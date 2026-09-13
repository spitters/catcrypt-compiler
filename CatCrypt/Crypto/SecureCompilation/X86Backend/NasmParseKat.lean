/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse

/-!
# Round-trip and coverage check of the NASM parser on the CryptOpt `carry_mul`

A program over `bench/cryptopt/fiat_curve25519_carry_mul.asm`, run from the
package root:

```
lake exe nasm-parse-kat
```

For every instruction line it compares `printInstr (toJInstr line)` with the
canonical text of the line, lists the lines whose instruction has no `JInstr`
constructor with the reason, and prints per-mnemonic counts of mapped and
unmapped lines. It then runs `parseNasm` on the whole file and, when that
succeeds, compares `printNasm` of the result with `canonicalNasm` of the file.

Exit status: `0` when the whole file parses and prints back to its canonical
text; `1` when the lexical layer accepts the file and every mapped line prints
back to its canonical text, but some instruction has no `JInstr` constructor;
`2` when the file cannot be read or lexed, or a mapped line prints back to a
different text.

## Main definitions

* `asmPath`: the input file, relative to the package root.
* `LineResult`, `checkLine`: the per-line outcome.
* `main`: runs the checks and reports.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParseKat

open CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse

/-- The input file, relative to the package root. -/
def asmPath : System.FilePath := "bench/cryptopt/fiat_curve25519_carry_mul.asm"

/-- The outcome of one source line: no instruction, a mapped instruction whose
    printed text agrees or disagrees with the canonical text, or an instruction
    with no `JInstr` constructor. -/
inductive LineResult where
  | noInstr
  | roundTrip (mn : String)
  | mismatch (mn canonical printed : String)
  | unmapped (mn canonical reason : String)
  | lexError (reason : String)

/-- Classify one source line. -/
def checkLine (ln : String) : LineResult :=
  match lexLine ln with
  | .error e => .lexError e
  | .ok (.instr mn ops) =>
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParseKat

open CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse
open CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParseKat in
/-- Run the per-line round-trip and coverage check and the whole-file parse. -/
def main : IO UInt32 := do
  let src ← try IO.FS.readFile asmPath catch e => do
    IO.eprintln s!"nasm-parse-kat: cannot read {asmPath}: {e}"
    return 2
  let mut counts : List (String × Nat × Nat) := []
  let mut bad := false
  let mut total := 0
  for (n, ln) in numberedLines src do
    match checkLine ln with
    | .noInstr => pure ()
    | .roundTrip mn =>
        total := total + 1
        counts := bump counts mn true
    | .mismatch mn canon p =>
        total := total + 1
        counts := bump counts mn true
        bad := true
        IO.eprintln s!"nasm-parse-kat: line {n}: MISMATCH\n  canonical: {canon}\n  printed:   {p}"
    | .unmapped mn canon e =>
        total := total + 1
        counts := bump counts mn false
        IO.println s!"line {n}: {canon}: {e}"
    | .lexError e =>
        bad := true
        IO.eprintln s!"nasm-parse-kat: line {n}: lexical error: {e}"
  IO.println s!"instructions: {total}"
  for (mn, a, b) in counts do
    IO.println s!"  {mn}: {a} mapped, {b} without a JInstr constructor"
  if bad then return 2
  match parseNasm src, canonicalNasm src with
  | .ok is, .ok canon =>
      match printNasm is with
      | .ok p =>
          if p == canon then
            IO.println s!"nasm-parse-kat: {is.length} instructions parse and print back to the canonical text"
            return 0
          else
            IO.eprintln "nasm-parse-kat: printNasm (parseNasm file) differs from canonicalNasm file"
            return 2
      | .error e =>
          IO.eprintln s!"nasm-parse-kat: printNasm failed: {e}"
          return 2
  | .error e, _ =>
      IO.println s!"nasm-parse-kat: parseNasm: {e}"
      return 1
  | _, .error e =>
      IO.eprintln s!"nasm-parse-kat: canonicalNasm: {e}"
      return 2
