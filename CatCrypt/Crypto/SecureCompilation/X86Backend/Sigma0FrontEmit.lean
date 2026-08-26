/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# SHA-256 `small_sigma0` (`w = 32`) through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §4.1.2 lowercase-`σ₀` message-schedule function, the pilot ARX
leaf of `bench/thir_front_sigma0/` (#605 Phase 1, Step 4), routed onto the OWNED
x86 backend instead of through jasminc:

    small_sigma0(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)        (FIPS 180-4 §4.1.2)

This is the σ₀ companion of `bench/thir_front_sha256_sigma1_owned/`'s σ₁ leaf
(`ROTR¹⁷ ⊕ ROTR¹⁹ ⊕ SHR¹⁰`). Rather than build a fresh `Com thirDialect` σ₀
program, we reuse the front's **own** lowered `Com jasminDialect` (`sigma0Com`,
the output of the verified width-parameterized `thirToJasmin`), which already
carries the connecting theorem `sigma0_FrontValueAgrees` (the lowered Com denotes
the same `BitVec 32` as the THIR `sigma0Thir`) and `sigma0Thir_denote` (the THIR
meaning equals the FIPS reference). We feed `sigma0Com` straight into the owned
ABI export (`Com.toLprogPhysAbi`), then shift/rotate-immediate-legalise it:

    sigma0Com : Com jasminDialect ctxtSigma0 (.reg 32)   -- the FRONT's lowering
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --legalizeShiftImmLprog-> rotates/shift expanded to GP shift-or idioms
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out,
`RSI` = inp); the single input is loaded from `[RSI + 0]` and the single output
stored to `[RDI + 0]`, matching the `small_sigma0` C extern (and the existing
`bench/thir_front_sigma0/sigma0_front_kat.c` harness):

```c
extern void small_sigma0(uint32_t *out, const uint32_t *inp);  // inp = [x]
//   out[0] receives ROTR7(x) ^ ROTR18(x) ^ (x >> 3)
```

The lone arg slot `0 ↦ ("RSI", 0)` (`sigma0InLoadMap`); the single output (the
final xor binding) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The two rotates + one shift (immediate legalisation)

`σ₀`'s `ROTR⁷`/`ROTR¹⁸` lower to rotate-immediate `Lopn` forms and the `SHR³` to
a unary shift-immediate; `legalizeShiftImmLprog` (shared from
`Sha256Sigma1ThirEmit`) expands each into the printer-recognised GP shift /
shift-or idiom over the reserved scratch `R15`. So the emitted `.s` carries no
unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value, the front's own theorem)**: `sigma0_FrontValueAgrees`
  (re-exported here as `sigma0Front_value`) — the lowered `Com jasminDialect`
  `sigma0Com` denotes the same `BitVec 32` as the THIR `sigma0Thir`, and
  `sigma0Thir_denote` ties that to the FIPS `sigma0Spec`.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `small_sigma0(x) == σ₀(x)` is the external `as`/`cc` KAT in
`bench/thir_front_sigma0/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sigma0FrontEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (sigma0Com sigma0Thir sigma0Spec sigma0_FrontValueAgrees sigma0Thir_denote
   ctxtSigma0 inputValuation)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
  (legalizeShiftImmLprog)

/-! ## 1. The front's value theorem (re-exported)

The owned emit reuses the front's **own** lowered Com `sigma0Com`; its value
correctness is exactly the front's `sigma0_FrontValueAgrees` (the lowered Com
denotes the same `BitVec 32` as the THIR `sigma0Thir`) combined with
`sigma0Thir_denote` (the THIR meaning is the FIPS `sigma0Spec`). -/

/-- The front's lowered `sigma0Com` denotes the FIPS `σ₀` reference on any
    single-word input, given the front's own lowering witness `hc`: combines
    `sigma0_FrontValueAgrees` (Com = THIR) with `sigma0Thir_denote`
    (THIR = `sigma0Spec`). The lowering does succeed (`sigma0_lowers`), so a
    witness `hc` always exists. -/
theorem sigma0Front_value (I : Fin 1 → BitVec 32)
    {c : Com jasminDialect ctxtSigma0 (.reg 32)}
    (hc : ThirToComFront.thirToJasmin [] (ThirToComFront.initFState 32 1) sigma0Thir = some c) :
    some (c.denote (inputValuation 32 1 I)) = some (sigma0Spec (I 0)) := by
  rw [← sigma0Thir_denote I]
  exact (sigma0_FrontValueAgrees I c hc).symm

/-! ## 2. ABI maps for the 1-in / 1-out width-32 σ₀ leaf -/

/-- Input-load map: the single arg slot `0 ↦ ("RSI", 0)` (input `x = inp[0]`).
    Slots `≥ 1` are absent (σ₀ has exactly one input). -/
def sigma0InLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 0) else none

/-- Output-store map: the single result word (the final xor binding) is stored to
    `out[0]` (`[RDI + 0]`). -/
def sigma0OutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The front's `sigma0Com` exported to a physical, two-address SysV `Lprog`,
    then shift/rotate-immediate-legalised so the owned printer renders the two
    rotates and the shift. `fname` `"small_sigma0"` becomes the emitted asm label
    (matching the C extern). -/
def sigma0Lprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi sigma0Com "small_sigma0"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      sigma0InLoadMap                       -- inLoadMap
      sigma0OutStoreMap                     -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32])                                 -- abiTyin (1 u32 input)

/-- The rendered owned-backend AT&T `.s` for `small_sigma0` (no jasminc). -/
def sigma0Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned sigma0Lprog

/-! ## 4. Shape checks on the emitted asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `small_sigma0` into the
    `bench/thir_front_sigma0/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sigma0/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/small_sigma0_owned.s") sigma0Asm
  IO.println "WROTE bench/thir_front_sigma0/gen/small_sigma0_owned.s"
  IO.println "  (SHA-256 message-schedule small_sigma0, the front's own sigma0Com"
  IO.println "   through Com.toLprogPhysAbi -> renderLprogAtt onto the OWNED x86"
  IO.println "   backend, NO jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sigma0FrontEmit
