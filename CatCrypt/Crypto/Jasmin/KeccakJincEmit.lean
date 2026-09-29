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

The round loop is kept rolled (`KeccakJincImport.keccakF1600RolledAsm`);
`--unrolled` writes the fully unrolled rendering (`keccakF1600Asm`) instead.

```
lake exe keccak-jinc-emit [--unrolled]
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
/-- Imports `keccak_f1600` with its round loop kept rolled
    (`KeccakJincImport.keccakF1600Rolled`), or fully unrolled under `--unrolled`,
    renders it through the owned backend and writes the text, exiting non-zero
    when the import or the elaboration fails. -/
def main (args : List String) : IO UInt32 := do
  let imported : Except String (JincToCom.JFun × String) :=
    if args.contains "--unrolled" then
      KeccakJincImport.keccakF1600JFun.map fun f =>
        (f, JincElab.emitJFunAsm f KeccakJincImport.keccakF1600Sym)
    else
      KeccakJincImport.keccakF1600Rolled.map fun r =>
        (r.fn, JincElab.emitJFunRolledAsm r.fn r.tables KeccakJincImport.keccakF1600Sym)
  match imported with
  | .error e =>
      IO.eprintln s!"keccak-jinc-emit: import failed: {e}"
      return 1
  | .ok (f, asm) =>
      IO.println s!"keccak-jinc-emit: imported {f.body.length} statements"
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
