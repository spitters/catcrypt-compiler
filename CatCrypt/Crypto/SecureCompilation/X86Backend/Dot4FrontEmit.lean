/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit

/-!
# `dot4` (fixed-width unsigned inner product, `w = 64`) through the OWNED x86 backend

The Substrate FRONT-lane pilot scalar crypto fn `dot4` — the fixed-width
unsigned inner product / schoolbook MAC step

    dot4(a, b) = Σ_{i<4} a[i] * b[i]        (wrapping u64)

routed onto the OWNED x86 backend instead of through jasminc. Rather than rebuild
the program at the `Com thirDialect` level, we reuse the front's **own** lowered
`Com jasminDialect` (`dot4Com`, the output of the verified `thirToJasmin`), which
already carries the connecting theorem `dot4_FrontValueAgrees` (the lowered Com
denotes the same `BitVec 64` as the THIR `dot4`). We feed `dot4Com` straight into
the owned ABI export:

    dot4Com : Com jasminDialect ctxt4 (.reg 64)   -- the FRONT's own lowering
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

`dot4`'s body is four `MUL` (the per-lane products) and three `ADD` (the wrapping
accumulation) over u64 registers — all printer-recognised two-address ALU forms
(`MUL → imul`, `ADD → add`), so the emit needs no shift/rotate legalisation pass
and carries no unhandled-op sentinel.

## ABI (2-pointer SysV)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out,
`RSI` = inp); the eight u64 inputs are loaded from `[RSI + 8*i]` and the single
output stored to `out[0]`, matching the `dot4` C extern (and the existing
`bench/thir_front_pilot/dot4_front_kat.c` harness):

```c
extern void dot4(uint64_t *out, const uint64_t *inp);
//   inp[0..3] = a[0..3], inp[4..7] = b[0..3]
//   out[0] receives sum_{i<4} a[i]*b[i]   (wrapping u64)
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `dot4`'s context `ctxt4`
is 8 u64 inputs in input order `[inp0, …, inp7]`, so input index `i` is `inp[i]`
at byte offset `8*i`, and arg slot `s ↦ input index (8 - 1 - s) = 7 - s`:

    inLoadMap s = ("RSI", 8 * (7 - s))

i.e. slot `7 ↦ inp[0]` (offset 0), …, slot `0 ↦ inp[7]` (offset 56). The single
output (the last accumulation binding) is stored to `out[0]`
(`outStoreMap = [("RDI", 0)]`).

## What is verified vs trusted

* **Verified (value, the front's own theorem)**: `dot4_FrontValueAgrees`
  (re-exported here as `dot4Front_value`) — the lowered `Com jasminDialect`
  `dot4Com` denotes the same `BitVec 64` as the THIR `dot4`.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `dot4(a, b) == Σ a[i]·b[i]` is the external `as`/`cc` KAT in
`bench/thir_front_pilot/` (no jasminc).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Dot4FrontEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (dot4Com dot4 dot4_FrontValueAgrees ctxt4 inputValuation)

/-! ## 1. The front's value theorem (re-exported)

The owned emit reuses the front's **own** lowered Com `dot4Com`; its value
correctness is exactly the front's `dot4_FrontValueAgrees` (the lowered Com
denotes the same `BitVec 64` as the THIR `dot4`). -/

/-- The front's lowered `dot4Com` denotes the same `BitVec 64` as the THIR `dot4`
    on any input vector `I`, given the front's own lowering witness `hc`. This is
    a direct re-export of the front's `dot4_FrontValueAgrees`; the lowering does
    succeed (`dot4_lowers`), so a witness `hc` always exists. -/
theorem dot4Front_value (I : Fin 8 → BitVec 64)
    {c : Com jasminDialect ctxt4 (.reg 64)}
    (hc : ThirToComFront.thirToJasmin [] (ThirToComFront.initFState 64 8) dot4 = some c) :
    dot4.denote I (ThirToComFront.LEnv.empty 64)
      = some (c.denote (inputValuation 64 8 I)) :=
  dot4_FrontValueAgrees I c hc

/-! ## 2. ABI maps for the 8-in / 1-out width-64 `dot4` leaf -/

/-- Input-load map: arg slot `s ↦ ("RSI", 8 * (7 - s))` (input index `7 - s` is
    `inp[7 - s]`, byte offset `8 * (7 - s)`). Slot `7 ↦ inp[0]` (offset 0), …,
    slot `0 ↦ inp[7]` (offset 56). Slots `≥ 8` are absent (8 inputs). -/
def dot4InLoadMap : InLoadMap := fun s =>
  if s < 8 then some ("RSI", 8 * (7 - s)) else none

/-- Output-store map: the single result word (the last accumulation binding) is
    stored to `out[0]` (`[RDI + 0]`). -/
def dot4OutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The front's `dot4Com` exported to a physical, two-address SysV `Lprog`. No
    shift/rotate legalisation is needed (the body is `MUL`/`ADD` only). `fname`
    `"dot4"` becomes the emitted asm label (matching the C extern). -/
def dot4Lprog (_ : Unit) : Lprog :=
  Com.toLprogPhysAbi (dot4Com ()) "dot4"
    (fun _ => none)                       -- shiftImm oracle (unused)
    (fun _ => none)                       -- immSlotMap (no input immediates)
    dot4InLoadMap                         -- inLoadMap
    dot4OutStoreMap                       -- outStoreMap
    ["RDI", "RSI"]                        -- abiArgs (out, inp)
    [64, 64, 64, 64, 64, 64, 64, 64]      -- abiTyin (8 u64 inputs)

/-- The rendered owned-backend AT&T `.s` for `dot4` (no jasminc). -/
def dot4Asm (_ : Unit) : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (dot4Lprog ())

/-! ## 4. Rendered asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `dot4` into the `bench/thir_front_pilot/gen`
    harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_pilot/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/dot4_owned.s") (dot4Asm ())
  IO.println "WROTE bench/thir_front_pilot/gen/dot4_owned.s"
  IO.println "  (dot4 inner product, the front's own dot4Com through"
  IO.println "   Com.toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend,"
  IO.println "   NO jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Dot4FrontEmit
