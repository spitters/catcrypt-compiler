/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Where the example modules write their generated MLIR

The MLIR the `Jasmin/Examples/` modules emit at elaboration is consumed by the
`catcrypt-bench` checkout, which is a sibling of this repository rather than
part of it. The destination is `$CATCRYPT_BENCH_SRC` when that variable is set
and `../BLS/catcrypt-bench/src` otherwise, and writing is skipped when the
directory is absent, so the modules elaborate in a clone that has no sibling.

## Main definitions

* `benchSrcRoot` — the destination directory.
* `writeBench` — write one named file under it.
* `writeBenchWith` — hand the resolved path to a writer that takes one.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Examples.BenchOut

/-- The directory the generated MLIR is written to. -/
def benchSrcRoot : IO System.FilePath := do
  pure (((← IO.getEnv "CATCRYPT_BENCH_SRC").getD "../BLS/catcrypt-bench/src") : System.FilePath)

/-- Write `contents` to `name` under `benchSrcRoot`, or do nothing when that
    directory does not exist. -/
def writeBench (name : String) (contents : String) : IO Unit := do
  let root ← benchSrcRoot
  if ← System.FilePath.pathExists root then
    IO.FS.writeFile (root / name) contents

/-- Call `write` on the full path of `name` under `benchSrcRoot`, or do nothing
    when that directory does not exist. For emitters that take the path rather
    than returning the contents. -/
def writeBenchWith (name : String) (write : String → IO Unit) : IO Unit := do
  let root ← benchSrcRoot
  if ← System.FilePath.pathExists root then
    write (root / name).toString

end CatCrypt.Crypto.Jasmin.Examples.BenchOut
