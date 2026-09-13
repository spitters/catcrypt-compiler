/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.MldsaJincImport

/-!
# Import-path checks on the ML-DSA Montgomery-reduction leaf, as a program

Named Boolean checks on the `.jinc` leaf of `MldsaJincImport`: its parse, its
elaboration to a `Com jasminDialect`, and its AT&T rendering. They evaluate
`partial def`s (`JincToCom.tokenize`, `JincElab.elabStmts`) that the kernel cannot
unfold, so they are checks of the compiled program rather than theorems, and they
run as a program rather than at elaboration:

```
lake exe mldsa-jinc-import-kat
```

## Main definitions

* `importChecks`: the checks, each paired with its name.
* `main`: evaluates `importChecks`, exiting non-zero at the first failing check and
  naming it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.MldsaJincImportKat

open CatCrypt.Crypto.Jasmin.JincToCom
open CatCrypt.Crypto.Jasmin.JincElab
open CatCrypt.Crypto.Jasmin.MldsaJincImport

/-- The import-path checks: the leaf parses to a function with one parameter,
    three declarations and seven statements returning `reg u64`; it elaborates to
    a one-argument `Com` returning `reg 64`; and its rendering carries no parse or
    elaboration failure and exactly one `mldsa_montgomery_reduce:` label. -/
def importChecks (_ : Unit) : List (String × Bool) :=
  let parsed := (parseJincFun mldsaMontRedSrc).toOption
  let asm := mldsaMontRedAsm
  [ ("parse shape (1 param, 3 decls, 7 stmts)",
      parsed.map (fun f => (f.params.length, f.decls.length, f.body.length)) == some (1, 3, 7))
  , ("parsed return type reg u64", parsed.map (fun f => f.retTy) == some (JTy.reg 64))
  , ("elaborates to Com [reg 64] (reg 64)", mldsaMontRedCom?.isSome)
  , ("render has no parse error", (asm.splitOn "; parse error").length == 1)
  , ("render has no elaboration failure", (asm.splitOn "elaboration failed").length == 1)
  , ("render has one export label", (asm.splitOn "mldsa_montgomery_reduce:").length == 2) ]

end CatCrypt.Crypto.Jasmin.MldsaJincImportKat

open CatCrypt.Crypto.Jasmin.MldsaJincImportKat in
/-- Evaluates `importChecks`, exiting non-zero at the first failing check. -/
def main : IO UInt32 := do
  let checks := importChecks ()
  for (nm, ok) in checks do
    unless ok do
      IO.eprintln s!"mldsa-jinc-import-kat: check FAILED: {nm}"
      return 1
  IO.println s!"mldsa-jinc-import-kat: {checks.length} import-path checks hold"
  return 0
