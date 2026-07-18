/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# The whole ChaCha20 block (FULL pointer ABI) through the OWNED x86 backend (NO jasminc)

`Chacha20BlockFullMemrefEmit.lean` lowers the whole ChaCha20 block — over the
two-memref-pointer context `(out, in)` — from the high `catCryptDialect` to
`Com jasminDialect` (`chacha20BlockFullMemrefJasmin`, with the input reads as
`stackLoad` and the output stores as `stackStore`), and emits it through the
*testing/comparison* path (`emitJazz` → jasminc). This file emits the **same**
lowered `Com jasminDialect` through the **owned** x86 backend:

```
Com jasminDialect  --Com.toLprogPhysAbi-->  Lprog  --renderLprogAtt-->  AT&T `.s`
```

assembled by `cc`/`as` directly, no jasminc.

## ABI (2-pointer SysV, `f(out = RDI, in = RSI)`)

The whole-block program is the wide one the register-argument version could not
take: its 32-register-word predecessor blew the x86-64 SysV 6-register limit. The
full-memref version's lowered jasmin context is exactly the two pointer-array
params `[stackArr 64 16, stackArr 64 16]` (proved by
`chacha20BlockFullMemref_param_ctx`) — `out` and `in`. The block reads its sixteen
input words from `in` and writes its sixteen output words to `out` **internally**
(the body's `stackLoad`/`stackStore` SIB-address the param pointer registers), so
the owned ABI needs no per-word `inLoadMap`/`outStoreMap` splice: the two memref
params map directly onto the two SysV pointer arguments `RDI`/`RSI`. There is no
6-register-arg limit on the owned pointer ABI, so the wide state passes fine.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 0. Substring helper -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-! ## 1. The owned `Lprog` + AT&T `.s`

The two memref params `(out, in)` map onto the SysV pointer args `RDI`/`RSI`
(`chacha20_block(out = RDI, in = RSI)`). The body addresses memory itself
(`stackLoad in[i]` reads / `stackStore out[i]` writes), so the ABI splice carries
NO per-word load/store maps — the defaults (`inLoadMap = none`, `outStoreMap = []`).
`abiTyin = [64, 64]` declares the two pointer arguments.

### `abiArgs` order: the de-Bruijn → arg-slot reversal

`comToBody`/`resolveVar` resolve a De-Bruijn var to the body arg name
`slot = curDepth - 1 - deBruijn`, which **reverses** the source dialect-context
order. The full-memref `Com`'s context is `[out, in]` (`out = .here`, `in =
.there .here`), so the body's two argument names come out reversed:

* `a0` is the **input** memref var — the SIB base of all sixteen `LOADIDX` reads;
* `a1` is the **output** memref var — the SIB base of the first `STOREIDX` write
  (subsequent stores thread the functionally-updated array through fresh SSA).

`buildArgPtrMaterialize` zips `abiArgs` positionally with the body arg slots
(`abiArgs[j]` materialized into `aj`'s RA register). The SysV C ABI is
`chacha20_block(out, in)` ⇒ `RDI = out`, `RSI = in`. To make the input reads
(`a0`) read from `in = RSI` and the output stores (`a1`) write to `out = RDI`,
`abiArgs` must therefore be **`["RSI", "RDI"]`** (`a0 ← RSI = in`, `a1 ← RDI =
out`), NOT `["RDI", "RSI"]`. With `["RDI", "RSI"]` the reads would read from
`out` and the stores write to `in` — both buffers swapped, the in/out aliasing
bug (a store clobbers a not-yet-loaded input). The two materialized pointer
registers are `RSI ≠ RDI`, so `MemrefPtrsDistinct` holds and
`toLprogPhysAbi_lsem` applies. -/

/-- The whole ChaCha20 block as a 2-pointer-ABI physical-register `Lprog`
    (symbol `chacha20_block_owned`), built from the *same* lowered
    `chacha20BlockFullMemrefJasmin` the jasminc path uses. The two memref params
    `(out, in)` are the SysV pointer args `RDI`/`RSI`; the sixteen input reads and
    sixteen output writes are the body's own `stackLoad`/`stackStore`. Because the
    De-Bruijn → arg-slot resolution reverses the source context order, the body's
    input-read base is `a0` and its output-store base is `a1`; the ABI list is
    therefore `["RSI", "RDI"]` (`a0 = in ← RSI`, `a1 = out ← RDI`) so reads hit
    `in` and stores hit `out`. -/
def chachaOwnedLprog : Lprog :=
  Com.toLprogPhysAbi chacha20BlockFullMemrefJasmin "chacha20_block_owned"
    (fun _ => none) (fun _ => none) (fun _ => none) []
    (abiArgs := ["RSI", "RDI"]) (abiTyin := [64, 64])

/-- The owned-backend AT&T `.s` text of the whole ChaCha20 block
    (symbol `chacha20_block_owned`), rendered straight from the `Lprog` by the
    verified printer — no jasminc. -/
def chachaOwnedAtt : String := renderLprogAtt chachaOwnedLprog

/-! ## 1a. Front provenance

`chacha20BlockFullMemrefJasmin` is the FRONT pipeline's output: the high
`catCryptDialect` whole-block program `chacha20BlockFullMemrefCom` lowered
through the seam `DialectToJasminCom.cryptoDialectToJasminCom` in
`Chacha20BlockFullMemrefEmit`. The theorem pins that provenance in checkable
form — the deployed `Com` IS the seam's output, so the owned render below
carries no hand-authored `Com` anywhere on its emit path. -/

/-- The deployed whole-block `Com` is the front pipeline's output for the
    high-dialect `chacha20BlockFullMemrefCom`. -/
theorem chachaCom_from_front :
    DialectToJasminCom.cryptoDialectToJasminCom chacha20BlockFullMemrefCom
      = some chacha20BlockFullMemrefJasmin :=
  (Option.some_get chacha20BlockFullMemref_jasmin_isSome).symm

/-! ## 2. Printer shape lemmas: the export label is present, no unhandled op -/

theorem chacha_owned_has_leaf :
    hasSub chachaOwnedAtt "chacha20_block_owned" = true := by native_decide

theorem chacha_owned_no_unhandled :
    hasSub chachaOwnedAtt "UNHANDLED" = false := by native_decide

/-! ## 3. Emit driver -/

/-- Emit driver: write the owned-backend whole-block ChaCha20 `.s` (rendered
    straight from the lowered `Com jasminDialect`, NO jasminc; the wide state
    flows through the two memref pointers, so there is no 6-register-arg limit) to
    the bench gen-from-Com directory under the symbol `chacha20_block_owned`. -/
def emit : IO Unit := do
  let dir := "bench/chacha_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/chacha20_block_owned.s") chachaOwnedAtt
  IO.println "WROTE bench/chacha_compare/gen_com/chacha20_block_owned.s"
  IO.println "  owned x86 backend (toLprogPhysAbi -> renderLprogAtt), 2-pointer ABI, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefOwnedEmit
