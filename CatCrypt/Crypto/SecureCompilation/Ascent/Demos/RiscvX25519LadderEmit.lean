/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject

/-!
# Emit the RV64 X25519 ladder object

Writes `RiscvX25519LadderObject.ladderObject`, the ELF64 object whose `.text` is the
verified encoding of the ladder program, to `bench/riscv_x25519/gen/x25519_ladder.o`.
Run from the package root:

```
lake exe riscv-x25519-emit
```

The values are checked where the object is consumed: `bench/riscv_x25519/run.sh` links it
into a C driver and compares the ladder output with the RFC 7748 vectors under qemu.

## Scope

The object carries a functional-correctness theorem (`x25519LadderObject_correct`) and no
constant-time or leakage theorem: nothing here shows that its control flow and memory
addresses are independent of the secret scalar. This module is listed in
`scripts/ct-obligation-baseline.txt` for that reason.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject

/-- Write the object. -/
def main : IO UInt32 := do
  let dir : System.FilePath := "bench/riscv_x25519/gen"
  IO.FS.createDirAll dir
  let path := dir / "x25519_ladder.o"
  IO.FS.writeBinFile path (ByteArray.mk (ladderObject.map fun b => b.toNat.toUInt8).toArray)
  IO.println s!"wrote {path} ({ladderObject.length} bytes)"
  return 0
