/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.MldsaJincImport
public meta import CatCrypt.Crypto.Jasmin.JincToLowCT
public import CatCrypt.Crypto.Jasmin.JincToLowCT

/-!
# Import-path checks on the ML-DSA `.jinc` leaves, as a program

Named Boolean checks on the `.jinc` leaves of `MldsaJincImport`: their parse,
their elaboration to a `Com jasminDialect`, and their AT&T rendering. They evaluate
`partial def`s (`JincToCom.tokenize`, `JincElab.elabStmts`) that the kernel cannot
unfold, so they are checks of the compiled program rather than theorems, and they
run as a program rather than at elaboration:

```
lake exe mldsa-jinc-import-kat
```

## Main definitions

* `importChecks`: the checks, each paired with its name.
* `instrLineCount`: the number of instruction lines of a rendered AT&T text.
* `main`: evaluates `importChecks`, exiting non-zero at the first failing check and
  naming it, then writes the `ExpandMask` rendering to
  `bench/mldsa_compare/gen_com/mldsa_expand_mask_owned.s`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.MldsaJincImportKat

open CatCrypt.Crypto.Jasmin.JincToCom
open CatCrypt.Crypto.Jasmin.JincElab
open CatCrypt.Crypto.Jasmin.MldsaJincImport

/-- An instruction line of an AT&T rendering: a tab-indented line that is neither
    an assembler directive (`.text`, `.globl`) nor a comment. -/
def isInstrLine (l : String) : Bool :=
  l.startsWith "\t" && !l.startsWith "\t." && !l.startsWith "\t#"

/-- The number of instruction lines of a rendered AT&T text. -/
def instrLineCount (asm : String) : Nat :=
  ((asm.splitOn "\n").filter isInstrLine).length

/-- The import-path checks. The Montgomery leaf parses to a function with one
    parameter, three declarations and seven statements returning `reg u64`; it
    elaborates to a one-argument `Com` returning `reg 64`; and its rendering
    carries no parse or elaboration failure and exactly one
    `mldsa_montgomery_reduce:` label. The `ExpandMask` leaf elaborates to a
    two-argument `Com` returning `stackArr 32 256`; its rendered text is checked
    where the artifact is consumed, by the bench Makefile and the C harness. -/
def importChecks (_ : Unit) : List (String × Bool) :=
  let parsed := (parseJincFun mldsaMontRedSrc).toOption
  let asm := mldsaMontRedAsm
  [ ("parse shape (1 param, 3 decls, 7 stmts)",
      parsed.map (fun f => (f.params.length, f.decls.length, f.body.length)) == some (1, 3, 7))
  , ("parsed return type reg u64", parsed.map (fun f => f.retTy) == some (JTy.reg 64))
  , ("elaborates to Com [reg 64] (reg 64)", mldsaMontRedCom?.isSome)
  , ("render has no parse error", (asm.splitOn "; parse error").length == 1)
  , ("render has no elaboration failure", (asm.splitOn "elaboration failed").length == 1)
  , ("render has one export label", (asm.splitOn "mldsa_montgomery_reduce:").length == 2)
  , ("expand_mask elaborates to Com [stackArr 32 640, stackArr 32 256] (stackArr 32 256)",
      expandMaskCom?.isSome) ]

/-- The path the `ExpandMask` rendering is written to, relative to the workspace
    root the executable runs from. -/
def expandMaskOutDir : String := "bench/mldsa_compare/gen_com"

/-- The file name of the `ExpandMask` rendering. -/
def expandMaskOutFile : String := "mldsa_expand_mask_owned.s"

end CatCrypt.Crypto.Jasmin.MldsaJincImportKat

open CatCrypt.Crypto.Jasmin.MldsaJincImport in
open CatCrypt.Crypto.Jasmin.MldsaJincImportKat in
/-- Evaluates `importChecks`, exiting non-zero at the first failing check, then
    writes the `ExpandMask` rendering and prints its instruction-line count. -/
def main : IO UInt32 := do
  let checks := importChecks ()
  for (nm, ok) in checks do
    unless ok do
      IO.eprintln s!"mldsa-jinc-import-kat: check FAILED: {nm}"
      return 1
  IO.println s!"mldsa-jinc-import-kat: {checks.length} import-path checks hold"
  let asm := expandMaskAsm
  IO.FS.createDirAll expandMaskOutDir
  let path : System.FilePath := System.FilePath.mk expandMaskOutDir / expandMaskOutFile
  IO.FS.writeFile path asm
  IO.println s!"mldsa-jinc-import-kat: wrote {path} ({instrLineCount asm} instruction lines)"
  match (CatCrypt.Crypto.Jasmin.JincToCom.parseJincFun
        CatCrypt.Crypto.Jasmin.JincToCom.mldsaExpandMaskSrc).toOption.bind
      (CatCrypt.Crypto.Jasmin.JincToLowCT.renderJFunLeaf "mldsa_expand_mask_real") with
  | some rolled =>
      let pathR : System.FilePath :=
        System.FilePath.mk expandMaskOutDir / "mldsa_expand_mask_rolled.s"
      IO.FS.writeFile pathR rolled
      IO.println s!"mldsa-jinc-import-kat: wrote {pathR} ({instrLineCount rolled} instruction lines)"
  | none => IO.println "mldsa-jinc-import-kat: the LowCT route declined the ExpandMask leaf"
  return 0
