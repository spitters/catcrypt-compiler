/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512SigmaThirEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# SHA-512 message-schedule WORD (64-bit) through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §6.4.2 SHA-512 message-schedule recurrence word `W_t` driven
through the `compile-from-hax` front (`Com thirDialect`) onto the OWNED x86
backend — NO jasminc anywhere. The width-64 sibling of
`Sha256MsgScheduleThirEmit.lean` (the width-32 SHA-256 message-schedule
word): it inlines both σ₀ and σ₁ (each a rotate/rotate/shift-xor triple) and
combines them with a three-add wrapping accumulation, width-64, 4-input:

    W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}     (mod 2⁶⁴, wrapping)

where (FIPS 180-4 §4.1.3, width 64)

    σ₀(x) = ROTR¹(x)  ⊕ ROTR⁸(x)  ⊕ SHR⁷(x)
    σ₁(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)

The sum is taken **left-to-right** (matching `sha512MsgWSpec`):
`((σ₁(w2) + w7) + σ₀(w15)) + w16`. This leaf exercises BOTH the width-64 rotate
legalisation (four `ROTR`) AND the width-64 shift legalisation (two `SHR`) AND
the wrapping-add chain (three `add`) in a single multi-input width-64 program.

The pipeline mirrors `Sha256MsgScheduleThirEmit` / `Sha512SigmaThirEmit`:

    sha512MsgWThir : Com thirDialect [.reg 64 × 4] (.reg 64)
      --lowerThir-->            Com jasminDialect [...] (.reg 64)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the four u64 inputs are loaded from `[RSI + off]` and the single output
stored to `[RDI + 0]`:

```c
extern void sha512_msg_w(uint64_t *out, const uint64_t *inp);
//   inp = [w2, w7, w15, w16]   (8-byte-strided u64 slots)
//   out[0] receives W_t = sigma1(w2) + w7 + sigma0(w15) + w16
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `sha512MsgWThir`'s
context is `[w2, w7, w15, w16]` (w2 = `.here`, …, w16 = `.there³ .here`), so
input index `w2 = 0, …, w16 = 3`, and arg slot `s ↦ input index (4 - 1 - s) =
3 - s`. The slot stride is **8 bytes** (`8 * (3 - s)`), the natural u64 stride.
So:

* slot `3` → input `w2`  (`inp[0]`, byte offset 0)
* slot `2` → input `w7`  (`inp[1]`, byte offset 8)
* slot `1` → input `w15` (`inp[2]`, byte offset 16)
* slot `0` → input `w16` (`inp[3]`, byte offset 24)

i.e. `inLoadMap s = ("RSI", 8 * (3 - s))`. The single output (the last binding,
`W_t`) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The four rotates + two shifts (width-64 immediate legalisation)

σ₁'s `ROTR¹⁹`/`ROTR⁶¹` and σ₀'s `ROTR¹`/`ROTR⁸` lower (via `thRor 64`) to
rotate-immediate `Lopn` forms; σ₁'s `SHR⁶` and σ₀'s `SHR⁷` lower (via
`thShrImm 64`) to unary shift-immediates. `legalizeShiftImmLprog` (shared from
`Sha256Sigma1ThirEmit`, width-generic `:64`-tagged path) rewrites each
unary shift-immediate into the two-source `[d] SHR:64 [d, #n]` form and each
rotate into the shift-or idiom over the reserved scratch `R15`. The three
`thBin .add 64` lower to printer-recognised two-source ALU forms directly. So
the emitted `.s` carries no unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha512MsgWThir_denote` (the leaf denotes `W_t` =
  `sha512MsgWSpec`) and `msgW_via_thirDialect` (the lowered `Com jasminDialect`
  denotes the same) — both by `rfl`.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha512_msg_w(...) == W_t` is the external `as`/`cc` KAT in
`bench/thir_front_sha512_msgw_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512MsgScheduleThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512SigmaThirEmit
  (sha512SmallSigma0Spec sha512SmallSigma1Spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
  (legalizeShiftImmLprog)

/-! ## 0. The FIPS 180-4 §6.4.2 SHA-512 message-schedule reference (width 64)

No bundled width-64 message-schedule spec exists in `ThirToComFront`, so we
define `sha512MsgWSpec` locally in terms of the width-64 σ specs already proved
in `Sha512SigmaThirEmit` (`sha512SmallSigma0Spec`/`sha512SmallSigma1Spec`).
The sum is left-to-right wrapping u64. -/

/-- FIPS 180-4 §6.4.2 message-schedule word
    `W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}` over the four
    influencing words, summed left-to-right (wrapping u64). σ₀/σ₁ are the
    width-64 specs from `Sha512SigmaThirEmit`. -/
def sha512MsgWSpec (w2 w7 w15 w16 : BitVec 64) : BitVec 64 :=
  sha512SmallSigma1Spec w2 + w7 + sha512SmallSigma0Spec w15 + w16

/-! ## 1. The SHA-512 message-schedule program as a `Com thirDialect` leaf

Built directly at the THIR-dialect level (`thRor 64`/`thShrImm 64`/`thBin 64`),
inlining σ₁(w2), σ₀(w15) and the three wrapping adds. Inputs (de-Bruijn,
program-root order): `[w2, w7, w15, w16]` — `w2 = .here`, …, `w16 = .there³ .here`.

SSA bindings (each `.var` prepends a fresh head binding; depth of original input
`i` after `k` bindings is `k + i`):

    -- σ₁(w2)   (ROTR¹⁹ ⊕ ROTR⁶¹ ⊕ SHR⁶)
    s1a  = ror 19 w2          s1b  = ror 61 w2          s1s  = shr 6 w2
    s1x  = s1a ^ s1b          sig1 = s1x ^ s1s          (= σ₁(w2))
    -- σ₀(w15)  (ROTR¹ ⊕ ROTR⁸ ⊕ SHR⁷)
    s0a  = ror  1 w15         s0b  = ror  8 w15         s0s  = shr  7 w15
    s0x  = s0a ^ s0b          sig0 = s0x ^ s0s          (= σ₀(w15))
    -- wrapping accumulation, left-to-right
    a1   = sig1 + w7          a2   = a1 + sig0          a3   = a2 + w16
    ret a3 -/
def sha512MsgWThir :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- b0: s1a = ror 19 w2   (w2 at depth 0)
  .var (.mk (.thRor 64 19) rfl (.cons .here .nil))
  -- b1: s1b = ror 61 w2   (w2 at depth 1)
  (.var (.mk (.thRor 64 61) rfl (.cons (.there .here) .nil))
  -- b2: s1s = shr 6 w2   (w2 at depth 2)
  (.var (.mk (.thShrImm 64 6) rfl (.cons (.there (.there .here)) .nil))
  -- b3: s1x = s1a ^ s1b   (s1a depth 2, s1b depth 1)
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b4: sig1 = s1x ^ s1s   (s1x depth 0, s1s depth 1)   (= σ₁(w2))
  (.var (.mk (.thBin .xor 64) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b5: s0a = ror 1 w15   (w15 at depth 7)
  (.var (.mk (.thRor 64 1) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))
  -- b6: s0b = ror 8 w15  (w15 at depth 8)
  (.var (.mk (.thRor 64 8) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))
  -- b7: s0s = shr 7 w15   (w15 at depth 9)
  (.var (.mk (.thShrImm 64 7) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there .here))))))))) .nil))
  -- b8: s0x = s0a ^ s0b   (s0a depth 2, s0b depth 1)
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b9: sig0 = s0x ^ s0s   (s0x depth 0, s0s depth 1)   (= σ₀(w15))
  (.var (.mk (.thBin .xor 64) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b10: a1 = sig1 + w7   (sig1 = b4 at depth 5, w7 at depth 11)
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there .here))))))))))) .nil)))
  -- b11: a2 = a1 + sig0   (a1 depth 0, sig0 = b9 at depth 1)
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b12: a3 = a2 + w16   (a2 depth 0, w16 at depth 15)
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)))
  (.ret .here)))))))))))))

/-- The THIR-dialect message-schedule leaf denotes the FIPS `W_t` word on any
    input valuation `[w2, w7, w15, w16]`. A direct check of the `thirDialect`
    semantics against `sha512MsgWSpec`. -/
theorem sha512MsgWThir_denote (w2 w7 w15 w16 : BitVec 64) :
    sha512MsgWThir.denote
        (.cons w2 (.cons w7 (.cons w15 (.cons w16 .nil))))
      = sha512MsgWSpec w2 w7 w15 w16 := by
  rfl

/-- **Message-schedule word re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` for `W_t` denotes the same `BitVec 64` as the
    FIPS reference, obtained through `Com[thir] →lowerThir→ Com[jasmin]`. Combines
    `lowerThir_denote` (the generic, proved dialect lowering) with
    `sha512MsgWThir_denote`. -/
theorem msgW_via_thirDialect (w2 w7 w15 w16 : BitVec 64) :
    (lowerThir sha512MsgWThir).denote
        (.cons w2 (.cons w7 (.cons w15 (.cons w16 .nil))))
      = sha512MsgWSpec w2 w7 w15 w16 := by
  rw [lowerThir_denote sha512MsgWThir
      (.cons w2 (.cons w7 (.cons w15 (.cons w16 .nil)))),
    sha512MsgWThir_denote]

/-! ## 2. ABI maps for the 4-in / 1-out width-64 message-schedule leaf -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (3 - s))` (8-byte u64 slot
    stride). Slot `3` is input `w2` (`inp[0]`, offset 0); slot `2` is `w7`
    (`inp[1]`, offset 8); slot `1` is `w15` (`inp[2]`, offset 16); slot `0` is
    `w16` (`inp[3]`, offset 24). Slots `≥ 4` are absent (4 inputs). -/
def msgWInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 24)       -- slot 0 = input w16 = inp[3]
  else if s = 1 then some ("RSI", 16)  -- slot 1 = input w15 = inp[2]
  else if s = 2 then some ("RSI", 8)   -- slot 2 = input w7  = inp[1]
  else if s = 3 then some ("RSI", 0)   -- slot 3 = input w2  = inp[0]
  else none

/-- Output-store map: the single result word (the last binding, `W_t`) is stored
    to `out[0]` (`[RDI + 0]`). -/
def msgWOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The message-schedule leaf lowered through the thirDialect spine and exported
    to a physical, two-address SysV `Lprog`, then shift/rotate-immediate-legalised
    so the owned printer renders the four rotates and two shifts. `fname`
    `"sha512_msg_w"` becomes the emitted asm label (matching the C extern). -/
def msgWLprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha512MsgWThir) "sha512_msg_w"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      msgWInLoadMap                         -- inLoadMap
      msgWOutStoreMap                       -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64, 64, 64])                     -- abiTyin (4 u64 inputs)

/-- The rendered owned-backend AT&T `.s` for `sha512_msg_w` (no jasminc). -/
def msgWAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned msgWLprog

/-! ## 4. Shape checks on the emitted asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `sha512_msg_w` into the
    `bench/thir_front_sha512_msgw_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha512_msgw_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha512_msgw_owned.s") msgWAsm
  IO.println "WROTE bench/thir_front_sha512_msgw_owned/gen/sha512_msgw_owned.s"
  IO.println "  (SHA-512 message-schedule word sha512MsgWThir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

/-! ## 6. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512MsgScheduleThirEmit
