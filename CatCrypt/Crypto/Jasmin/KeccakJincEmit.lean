/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.KeccakJincImport

/-!
# Emit the imported Keccak-f[1600]

Writes the owned AT&T text of `keccak_f1600` imported from the formosa-keccak
Jasmin source (`KeccakJincImport`) to
`bench/keccak_compare/gen_com/keccak_f1600_jinc_ref.s`, relative to the workspace
root the executable runs from. The artifact is the output; its values are checked
where it is consumed, by `bench/keccak_compare` (`make keccak-kat-jinc`) and
`bench/symcrust_compare`.

```
lake exe keccak-jinc-emit
```
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.KeccakJincEmit

/-- The directory the rendering is written to. -/
def outDir : String := "bench/keccak_compare/gen_com"

/-- The file name of the rendering. -/
def outFile : String := "keccak_f1600_jinc_ref.s"

/-- An instruction line: tab-indented and neither a directive nor a comment. -/
def isInstrLine (l : String) : Bool :=
  l.startsWith "\t" && !l.startsWith "\t." && !l.startsWith "\t#"

end CatCrypt.Crypto.Jasmin.KeccakJincEmit

open CatCrypt.Crypto.Jasmin in
/-- Imports `keccak_f1600`, renders it through the owned backend and writes the
    text, exiting non-zero when the import or the elaboration fails. -/
def main : IO UInt32 := do
  match KeccakJincImport.keccakF1600JFun with
  | .error e =>
      IO.eprintln s!"keccak-jinc-emit: import failed: {e}"
      return 1
  | .ok f =>
      IO.println s!"keccak-jinc-emit: imported {f.body.length} statements"
      let asm := JincElab.emitJFunAsm f KeccakJincImport.keccakF1600Sym
      if asm.startsWith ";" then
        IO.eprintln s!"keccak-jinc-emit: {asm}"
        return 1
      IO.FS.createDirAll KeccakJincEmit.outDir
      let path : System.FilePath :=
        System.FilePath.mk KeccakJincEmit.outDir / KeccakJincEmit.outFile
      IO.FS.writeFile path asm
      let n := ((asm.splitOn "\n").filter KeccakJincEmit.isInstrLine).length
      IO.println s!"keccak-jinc-emit: wrote {path} ({n} instruction lines)"
      return 0
