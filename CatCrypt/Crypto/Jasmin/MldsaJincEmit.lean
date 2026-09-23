/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JincToLowCT

/-!
# Emit the imported ML-DSA leaves

Writes the owned AT&T text of the Jasmin leaves the importer translates, into
`bench/mldsa_compare/gen_com/`. `JincToCom` parses the source, `JincToLowCT`
translates it to `LowCT`, and the rolled-loop front renders it, so a source
loop stays a loop.

The artifact is the output; nothing here compares values. The rendered text is
checked where it is consumed: the bench Makefile greps it and the C harness
compares every coefficient against the reference.

```
lake exe mldsa-jinc-emit
```

## Main definitions

* `emitLeaf`: write one leaf, reporting its instruction-line count.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.MldsaJincEmit

open CatCrypt.Crypto.Jasmin.JincToCom
open CatCrypt.Crypto.Jasmin.JincToLowCT

/-- The directory the renders are written to, relative to the workspace root the
    executable runs from. -/
def outDir : String := "bench/mldsa_compare/gen_com"

/-- An instruction line: indented and not a directive. -/
def isInstrLine (l : String) : Bool :=
  l.startsWith "\t" && !((l.drop 1).startsWith ".")

/-- Parse `src`, render it under `sym`, and write it to `outDir/<file>`. -/
def emitLeaf (src sym file : String) : IO Unit := do
  match (parseJincFun src).toOption.bind (renderJFunLeaf sym) with
  | some asm =>
      IO.FS.createDirAll outDir
      let path : System.FilePath := System.FilePath.mk outDir / file
      IO.FS.writeFile path asm
      let n := ((asm.splitOn "\n").filter isInstrLine).length
      IO.println s!"mldsa-jinc-emit: wrote {path} ({n} instruction lines)"
  | none =>
      throw (IO.userError s!"mldsa-jinc-emit: the LowCT route declined {sym}")

end CatCrypt.Crypto.Jasmin.MldsaJincEmit

open CatCrypt.Crypto.Jasmin.JincToCom in
open CatCrypt.Crypto.Jasmin.MldsaJincEmit in
/-- Write the imported leaves. -/
def main : IO UInt32 := do
  emitLeaf mldsaExpandMaskSrc "mldsa_expand_mask_real" "mldsa_expand_mask_rolled.s"
  return 0
