/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull

/-!
# `compileComToElfJInstrFull6` — the byte-safe re-point entry for ALL GoldenPath kernels

`CompileComToElfJInstrFull.compileComToElfJInstrFull` byte-matches `compileComToElf`
on the ALU/shift fragment via `gatherJBlock5`/`encodeJBlock`, but the immediate-form
peepholes (imm32-sign-extended `MOV:64`, shift-by-1 `D1`, nil-`MULXHI`) live in
`GatherImmForms.gatherJBlock6`/`encodeJBlock6`. This module wires THOSE into the same
`compileComToElf`-shaped ELF entry, so the WHOLE surveyed GoldenPath kernel set (all
29 sampled, 16 already-matching + 10 imm-form-blocked) byte-matches `compileComToElf`.

It is byte-for-byte the `…Full` entry with `jBodyBytes6` (the `gatherJBlock6` +
`encodeJBlock6` body bytes) substituted for `jBodyBytes`. The framing wrapper
(`wrapFundefBytes`) and the ELF stitch (`buildElfObjectMulti` + `bytesToByteArray`)
are the SAME functions `compileComToElf`/`…Full` use, so the whole ELF object is
byte-identical whenever the body bytes agree — and `GatherImmForms.imm_forms_byte_match`
+ the step-5..8 per-op agreements establish the body agreement across the op set.

## Honest status

The whole-ELF byte identity on each kernel is an `#eval` certificate (the body
agreement runs through `parseShiftMnem`'s `String.startsWith`, which does not
kernel-reduce in Lean 4.29); the conditional whole-ELF theorem
`CompileComToElfJInstrFull.jElf_eq_lprogElf` discharges everything above the body
agreement. So a GoldenPath `_x86_elf` def re-pointed to `compileComToElfJInstrFull6`
emits identical bytes — KAT-preserving — the precondition for retiring `encodeLprog`
from the GoldenPath emit path.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6 encodeJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
  (wrapFundefBytes physBodyOf)

/-- The full-body JInstr bytes via the immediate-form-correct gather/encoder
    (`gatherJBlock6` + `encodeJBlock6`): the body bytes that byte-match `encodeLcmd`
    across the whole surveyed GoldenPath kernel set (incl. the imm32-`MOV`,
    shift-by-1, and nil-`MULXHI` forms). -/
def jBodyBytes6 (body : List Linstr) : List (BitVec 8) :=
  ((gatherJBlock6 body).map (encodeJBlock6 physAlloc)).getD []

/-- The JInstr full-body ELF entry over a physical body, immediate-form-correct:
    the same framing wrap + ELF stitch as `…Full.jElf`, with `jBodyBytes6` in the
    body slot. -/
def jElf6 (body : List Linstr) (fname : String) : ByteArray :=
  bytesToByteArray
    (ElfObject.buildElfObjectMulti
      [{ name := fname, text := wrapFundefBytes body (jBodyBytes6 body) }])

/-- **The full-body JInstr owned-emit ELF entry covering all GoldenPath kernels —
    the byte-safe drop-in for `compileComToElf`.** Lower the `Com` to its physical
    body the SAME way `compileComToElf` does, then build the ELF object through the
    immediate-form-correct full-body gather. Byte-identical to `compileComToElf` on
    every surveyed GoldenPath kernel, so a kernel's `_x86_elf` def re-points to this
    KAT-preservingly. -/
def compileComToElfJInstrFull6 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : ByteArray :=
  let body := physBodyOf com fname
  -- Totally byte-safe re-point: when the physical body is `gatherJBlock6`-coverable
  -- (every surveyed GoldenPath kernel is), emit the proven-byte-equal JInstr ELF;
  -- otherwise FALL BACK to the `Lprog` `compileComToElf` (the reference encoder we
  -- keep). So a kernel's `_x86_elf` re-pointed to this entry NEVER changes its bytes.
  if (gatherJBlock6 body).isSome then jElf6 body fname
  else CompileComToElf.compileComToElf com fname

-- The smoke-check `#eval` confirming `Full6` byte-matches `compileComToElf` on the
-- real kernel `asconSigma0` is re-homed in `GoldenPathByteIdentityDemo` (which sits
-- above both this entry and the GoldenPath kernels) so this entry file is
-- GoldenPath-free and the GoldenPath kernels can import it without a cycle.

end CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
