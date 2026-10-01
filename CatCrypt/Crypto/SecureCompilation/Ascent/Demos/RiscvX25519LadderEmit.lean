/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Object

/-!
# Emit the RV64 X25519 objects

Writes `RiscvX25519LadderObject.ladderObject`, the ELF64 object whose `.text` is the
verified encoding of the ladder program, to `bench/riscv_x25519/gen/x25519_ladder.o`, and
`RiscvX25519Object.x25519Object`, the one holding the whole X25519 function, to
`bench/riscv_x25519/gen/x25519.o`. Run from the package root:

```
lake exe riscv-x25519-emit
```

The values are checked where the objects are consumed: `bench/riscv_x25519/run.sh` links them
into C drivers and compares their outputs with the RFC 7748 vectors under qemu.

## Scope

The objects carry functional-correctness theorems (`x25519LadderObject_correct`,
`x25519Object_correct`) and no constant-time or leakage theorem: nothing here shows that
their control flow and memory addresses are independent of the secret scalar. This module
is listed in `scripts/ct-obligation-baseline.txt` for that reason.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject (ladderObject)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Object (x25519Object)

/-- Write `obj` to `dir / name`. -/
def writeObj (dir : System.FilePath) (name : String) (obj : List (BitVec 8)) : IO Unit := do
  let path := dir / name
  IO.FS.writeBinFile path (ByteArray.mk (obj.map fun b => b.toNat.toUInt8).toArray)
  IO.println s!"wrote {path} ({obj.length} bytes)"

/-- Write the objects. -/
def main : IO UInt32 := do
  let dir : System.FilePath := "bench/riscv_x25519/gen"
  IO.FS.createDirAll dir
  writeObj dir "x25519_ladder.o" ladderObject
  writeObj dir "x25519.o" x25519Object
  return 0
