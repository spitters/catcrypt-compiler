/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# BabyBear Montgomery multiply through the OWNED x86 backend (no jasminc)

The first field-arithmetic primitive driven through the `compile-from-hax`
front (`Com thirDialect`) onto the OWNED x86 backend — NO jasminc anywhere. The
companion of `bench/thir_front_treehash_owned/` (a control-flow demo chain), but
for the lazy BabyBear Montgomery REDC (`ThirToComFront.montMulThir`):

    babybear_montmul(a, b) = REDC(a · b)   over BabyBear `p = 0x78000001`, `R = 2^32`

The pipeline mirrors `VIR.Sha256LinearMain.emitOne`:

    montMulThir : Com thirDialect [.reg 64, .reg 64] (.reg 64)
      --lowerThir-->            Com jasminDialect [.reg 64, .reg 64] (.reg 64)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the inputs are loaded from `[RSI + off]` and the single output stored to
`[RDI + off]`. So the emitted symbol matches the existing `.jazz` export's ABI
(`ThirToComFront.montMulJazz`: `reg ptr u64[1] out, reg const ptr u64[2] inp`):

```c
extern void babybear_montmul(uint64_t *out, const uint64_t *inp);
//   inp = [ a, b ]   (two u64 words holding u32 Montgomery representatives)
//   out[0] receives REDC(a · b)
```

The argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `j`
(program-root order) is context entry `nArgs - 1 - j`. `montMulThir`'s context is
`[a, b]` (a = `.here`, b = `.there .here`), so input index `a = 0`, `b = 1`, and
arg slot `s ↦ input index (nArgs - 1 - s)`. With C-side `inp = [a, b]`:

* slot `1` → input `a` (`inp[0]`, byte offset 0)
* slot `0` → input `b` (`inp[1]`, byte offset 8)

i.e. `inLoadMap s = ("RSI", 8 * (1 - s))`. The single output (the last binding
`r = s >> 32`) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## In-body constants (no `immSlotMap` needed)

The REDC's `0xffffffff` low-word mask, the Montgomery inverse `minv`, and the
prime `p` are `thConst` ops, lowered to in-body `regConst` bindings, which
`opToLinstrR` renders as `MOV[:w] dst, #n` (a `movabs` for the wide values).
These are NOT inputs, so no `immSlotMap` entry is required — the body
materialises them directly.

## The `>> 32` reduction (shift-immediate legalisation)

The final reduction `r = s >> 32` is a `thShrImm 64 32`, lowered to the
single-source `Lopn [d] "SHR:32:64" [s]`. The owned printer's `renderLopn`
recognises the two-source shift form `[d] SHR:64 [d, #n]` (the form
`physBodyWithStores` produces for *register*-count shifts via the `shiftImm`
oracle), but NOT the unary `shrImm` mnemonic that carries the count in the
mnemonic (`SHR:<n>`). `legalizeShiftImmBody` is a thin, byte-faithful post-pass
over the already-allocated `Lprog` body that rewrites each unary
`Lopn [d] "SHR:<n>[:64]" [s]` / `"SHL:<n>[:64]"` into the printer's two-source
operand form (`[d] SHR[:64] [d, #n]`, prefixed by a `MOV` when `d ≠ s`), exactly
mirroring `JasminLprogExport.lowerTwoAddrShiftImm`. The rewrite is purely
syntactic (a shift by a compile-time constant) and leaves every other `Lopn`
untouched.

## What is verified vs trusted (same surface as `Sha256LinearMain` / `MpnAdxLprog`)

* **Verified (value)**: `montMulThir.denote = montMulSpec64` and
  `montMul_via_thirDialect` (the lowered `Com jasminDialect` denotes the width-64
  REDC) — both in `ThirToComFront`. The lowering `lowerThir` is denotation-proved
  (`lowerThir_denote`).
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame — the
  same surface every owned backend trusts.

The byte-identity `babybear_montmul(inp) == REDC(inp[0]·inp[1])` is the external
`as`/`cc` KAT in `bench/thir_front_montmul_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MontMulThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (montMulThir)

/-! ## 1. ABI maps for the 2-in / 1-out width-64 REDC -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (1 - s))`. Slot `1` is input `a`
    (`inp[0]`, offset 0); slot `0` is input `b` (`inp[1]`, offset 8). Slots `≥ 2`
    are absent (the REDC has exactly two inputs). -/
def montInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 8)        -- slot 0 = input b = inp[1]
  else if s = 1 then some ("RSI", 0)   -- slot 1 = input a = inp[0]
  else none

/-- Output-store map: the single result word (the last binding `r = s >> 32`) is
    stored to `out[0]` (`[RDI + 0]`). -/
def montOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 2. Shift-immediate legalisation post-pass

The owned printer renders the two-source shift form `[d] SHR[:64] [d, #n]` but
not the unary `shrImm` mnemonic `SHR:<n>[:64]` (count carried in the mnemonic).
This pass rewrites each such unary shift into the operand form, byte-faithfully
mirroring `JasminLprogExport.lowerTwoAddrShiftImm` for the register-destination
case (the REDC body's `>> 32` lands in a GP register, never a spill). -/

export CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
  (parseShiftImm legalizeBody legalizeLprog opnMnemonics)

/-- Rewrite one already-allocated `Linstr`: a unary shift-immediate
    `Lopn [d] "SHR:<n>[:64]" [s]` becomes the printer's two-source operand form
    `[d] SHR[:64] [d, #n]` (prefixed by a `MOV[:64] d, s` when `d ≠ s`); every
    other instruction passes through unchanged. The `MOV` width tracks the shift
    width (`MOV:64` for a `:64` shift). -/
def legalizeShiftImmInstr (i : Linstr) : List Linstr :=
  match i.li_i with
  | .Lopn [d] opn [s] =>
      match parseShiftImm opn with
      | some (baseMnem, n) =>
          let movMnem := if baseMnem.endsWith ":64" then "MOV:64" else "MOV"
          if d = s then
            [⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
          else
            [⟨i.li_ii, .Lopn [d] movMnem [s]⟩,
             ⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
      | none => [i]
  | _ => [i]

/-- Apply `legalizeShiftImmInstr` across a whole body. -/
def legalizeShiftImmBody : Lcmd → Lcmd :=
  legalizeBody legalizeShiftImmInstr

/-- Apply the shift-immediate legalisation to every function body of an `Lprog`. -/
def legalizeShiftImmLprog : Lprog → Lprog :=
  legalizeLprog legalizeShiftImmInstr

/-! A 64-bit shift with distinct source and destination expands to a
width-matched `MOV` and the two-source shift; with a common source and
destination the `MOV` is absent; a rotate is not rewritten. -/

#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:32:64" [.reg "RCX"]⟩)
    == ["MOV:64", "SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:32:64" [.reg "RAX"]⟩)
    == ["SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "ROR:16:64" [.reg "RCX"]⟩)
    == ["ROR:16:64"]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The REDC lowered through the thirDialect spine and exported to a physical,
    two-address SysV `Lprog`, then shift-immediate-legalised so the owned printer
    renders the `>> 32` reduction. The `fname` `"babybear_montmul"` becomes the
    emitted asm label (matching the C extern). -/
def montMulLprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir montMulThir) "babybear_montmul"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (constants are in-body regConst)
      montInLoadMap                         -- inLoadMap
      montOutStoreMap                       -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64])                             -- abiTyin

/-- The rendered owned-backend AT&T `.s` for `babybear_montmul` (no jasminc). -/
def montMulOwnedAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned montMulLprog

/-! ## 4. Rendered asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `babybear_montmul` into the
    `bench/thir_front_montmul_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_montmul_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/babybear_montmul_owned.s") montMulOwnedAsm
  IO.println "WROTE bench/thir_front_montmul_owned/gen/babybear_montmul_owned.s"
  IO.println "  (BabyBear Montgomery REDC montMulThir through Com[thir] -> lowerThir ->"
  IO.println "   toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc)"

/-! ## 6. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MontMulThirEmit
