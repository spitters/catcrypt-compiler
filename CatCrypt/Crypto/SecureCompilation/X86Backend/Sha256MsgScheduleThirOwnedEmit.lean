/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirOwnedEmit

/-!
# SHA-256 message-schedule WORD through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §6.2.2 SHA-256 message-schedule recurrence word `W_t` driven
through the `compile-from-hax` front (`Com thirDialect`) onto the OWNED x86
backend — NO jasminc anywhere. This is the **first COMPOSITE compile-from-hax
leaf**: it inlines both σ₀ and σ₁ (each a rotate/rotate/shift-xor triple) and
combines them with a three-add wrapping accumulation, width-32, 4-input:

    W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}     (mod 2³², wrapping)

where (FIPS 180-4 §4.1.2, width 32)

    σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)
    σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)

The sum is taken **left-to-right** (matching the bundled `msgSchedSpec`):
`((σ₁(w2) + w7) + σ₀(w15)) + w16`. Unlike `sha256Sigma1Thir` (a single σ leaf)
or `sha512{Ch,Maj}Thir` (multi-input boolean components, no rotate/shift), this
leaf exercises BOTH the rotate legalisation (four `ROTR`) AND the shift
legalisation (two `SHR`) AND the wrapping-add chain (three `add`) in a single
multi-input width-32 program.

The pipeline mirrors `Sha256Sigma1ThirOwnedEmit` / `Sha256RoundThirOwnedEmit`:

    sha256MsgWThir : Com thirDialect [.reg 32 × 4] (.reg 32)
      --lowerThir-->            Com jasminDialect [...] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the four inputs are loaded from `[RSI + off]` and the single output stored
to `[RDI + 0]`:

```c
extern void sha256_msg_w(uint32_t *out, const uint64_t *inp);
//   inp = [w2, w7, w15, w16]   (8-byte-strided slots, low 32 bits used)
//   out[0] receives W_t = sigma1(w2) + w7 + sigma0(w15) + w16
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `sha256MsgWThir`'s
context is `[w2, w7, w15, w16]` (w2 = `.here`, …, w16 = `.there³ .here`), so
input index `w2 = 0, …, w16 = 3`, and arg slot `s ↦ input index (4 - 1 - s) =
3 - s`. The slot stride is **8 bytes** (`8 * (3 - s)`), modelled exactly on the
round-`e` u32 ABI precedent (`roundEInLoadMap = ("RSI", 8 * (6 - s))`, with
C-side `inp` typed `const uint64_t *`, low 32 bits used). So:

* slot `3` → input `w2`  (`inp[0]`, byte offset 0)
* slot `2` → input `w7`  (`inp[1]`, byte offset 8)
* slot `1` → input `w15` (`inp[2]`, byte offset 16)
* slot `0` → input `w16` (`inp[3]`, byte offset 24)

i.e. `inLoadMap s = ("RSI", 8 * (3 - s))`. The single output (the last binding,
`W_t`) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The four rotates + two shifts (immediate legalisation)

σ₁'s `ROTR¹⁷`/`ROTR¹⁹` and σ₀'s `ROTR⁷`/`ROTR¹⁸` lower (via `thRor`) to
rotate-immediate `Lopn` forms; σ₁'s `SHR¹⁰` and σ₀'s `SHR³` lower (via
`thShrImm`) to unary shift-immediates. `legalizeShiftImmLprog` (shared from
`Sha256Sigma1ThirOwnedEmit`) rewrites each unary shift-immediate into the
two-source `[d] SHR [d, #n]` form and each rotate into the shift-or idiom over
the reserved scratch `R15`. The three `thBin .add 32` lower to printer-recognised
two-source ALU forms directly. So the emitted `.s` carries no unhandled-op
sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha256MsgWThir_denote` (the leaf denotes `W_t` =
  `msgSchedSpec`) and `msgW_via_thirDialect` (the lowered `Com jasminDialect`
  denotes the same) — both by `rfl`.
* **Verified (printer)**: the shape lemma below pins that the emitted `.s`
  carries the SysV leaf label and has no unhandled-op sentinel.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha256_msg_w(...) == W_t` is the external `as`/`cc` KAT in
`bench/thir_front_sha256_msgw_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256MsgScheduleThirOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (smallSigma1Spec sigma0Spec msgSchedSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirOwnedEmit
  (legalizeShiftImmLprog hasSub)

/-! ## 0. The FIPS message-schedule reference

The bundled `msgSchedSpec` is `σ₁(w2) + w7 + σ₀(w15) + w16` (left-to-right
wrapping u32). We provide `sha256MsgWSpec` as a transparent alias so the leaf's
denotation statement names the message-schedule word directly. -/

/-- FIPS 180-4 §6.2.2 message-schedule word
    `W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}` over the four
    influencing words, summed left-to-right (wrapping u32). Defeq to the bundled
    `msgSchedSpec`. -/
def sha256MsgWSpec (w2 w7 w15 w16 : BitVec 32) : BitVec 32 :=
  msgSchedSpec w2 w7 w15 w16

/-! ## 1. The SHA-256 message-schedule program as a `Com thirDialect` leaf

Built directly at the THIR-dialect level (`thRor`/`thShrImm`/`thBin`), inlining
σ₁(w2), σ₀(w15) and the three wrapping adds. Inputs (de-Bruijn, program-root
order): `[w2, w7, w15, w16]` — `w2 = .here`, …, `w16 = .there³ .here`.

SSA bindings (each `.var` prepends a fresh head binding; depth of original input
`i` after `k` bindings is `k + i`):

    -- σ₁(w2)
    s1a  = ror 17 w2          s1b  = ror 19 w2          s1s  = shr 10 w2
    s1x  = s1a ^ s1b          sig1 = s1x ^ s1s          (= σ₁(w2))
    -- σ₀(w15)
    s0a  = ror  7 w15         s0b  = ror 18 w15         s0s  = shr  3 w15
    s0x  = s0a ^ s0b          sig0 = s0x ^ s0s          (= σ₀(w15))
    -- wrapping accumulation, left-to-right
    a1   = sig1 + w7          a2   = a1 + sig0          a3   = a2 + w16
    ret a3 -/
def sha256MsgWThir :
    Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  -- b0: s1a = ror 17 w2   (w2 at depth 0)
  .var (.mk (.thRor 32 17) rfl (.cons .here .nil))
  -- b1: s1b = ror 19 w2   (w2 at depth 1)
  (.var (.mk (.thRor 32 19) rfl (.cons (.there .here) .nil))
  -- b2: s1s = shr 10 w2   (w2 at depth 2)
  (.var (.mk (.thShrImm 32 10) rfl (.cons (.there (.there .here)) .nil))
  -- b3: s1x = s1a ^ s1b   (s1a depth 2, s1b depth 1)
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b4: sig1 = s1x ^ s1s   (s1x depth 0, s1s depth 1)   (= σ₁(w2))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b5: s0a = ror 7 w15   (w15 at depth 7)
  (.var (.mk (.thRor 32 7) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))
  -- b6: s0b = ror 18 w15  (w15 at depth 8)
  (.var (.mk (.thRor 32 18) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))
  -- b7: s0s = shr 3 w15   (w15 at depth 9)
  (.var (.mk (.thShrImm 32 3) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there .here))))))))) .nil))
  -- b8: s0x = s0a ^ s0b   (s0a depth 2, s0b depth 1)
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b9: sig0 = s0x ^ s0s   (s0x depth 0, s0s depth 1)   (= σ₀(w15))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b10: a1 = sig1 + w7   (sig1 depth 5, w7 at depth 11)
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there .here))))))))))) .nil)))
  -- b11: a2 = a1 + sig0   (a1 depth 0, sig0 = b9 at depth 1)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b12: a3 = a2 + w16   (a2 depth 0, w16 at depth 15)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)))
  (.ret .here)))))))))))))

/-- The THIR-dialect message-schedule leaf denotes the FIPS `W_t` word on any
    input valuation `[w2, w7, w15, w16]`. A direct check of the `thirDialect`
    semantics against `sha256MsgWSpec` (= `msgSchedSpec`). -/
theorem sha256MsgWThir_denote (w2 w7 w15 w16 : BitVec 32) :
    sha256MsgWThir.denote
        (.cons w2 (.cons w7 (.cons w15 (.cons w16 .nil))))
      = sha256MsgWSpec w2 w7 w15 w16 := by
  rfl

/-- **Message-schedule word re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` for `W_t` denotes the same `BitVec 32` as the
    FIPS reference, obtained through `Com[thir] →lowerThir→ Com[jasmin]`. Combines
    `lowerThir_denote` (the generic, proved dialect lowering) with
    `sha256MsgWThir_denote`. -/
theorem msgW_via_thirDialect (w2 w7 w15 w16 : BitVec 32) :
    (lowerThir sha256MsgWThir).denote
        (.cons w2 (.cons w7 (.cons w15 (.cons w16 .nil))))
      = sha256MsgWSpec w2 w7 w15 w16 := by
  rw [lowerThir_denote sha256MsgWThir
      (.cons w2 (.cons w7 (.cons w15 (.cons w16 .nil)))),
    sha256MsgWThir_denote]

/-! ## 2. ABI maps for the 4-in / 1-out width-32 message-schedule leaf -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (3 - s))`, mirroring the
    round-`e` u32 ABI precedent (8-byte slot stride, low 32 bits used). Slot `3`
    is input `w2` (`inp[0]`, offset 0); slot `2` is `w7` (`inp[1]`, offset 8);
    slot `1` is `w15` (`inp[2]`, offset 16); slot `0` is `w16` (`inp[3]`,
    offset 24). Slots `≥ 4` are absent (4 inputs). -/
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
    `"sha256_msg_w"` becomes the emitted asm label (matching the C extern). -/
def msgWOwnedLprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha256MsgWThir) "sha256_msg_w"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      msgWInLoadMap                         -- inLoadMap
      msgWOutStoreMap                       -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32, 32, 32, 32])                     -- abiTyin (4 u32 inputs)

/-- The rendered owned-backend AT&T `.s` for `sha256_msg_w` (no jasminc). -/
def msgWOwnedAsm : String := renderLprogAtt msgWOwnedLprog

/-! ## 4. Shape checks on the emitted asm -/

/-- The emitted `.s` carries the SysV leaf label and has no unhandled-op
    sentinel. (Rotate/shift/add mnemonics are not asserted — the legalisation
    lands the rotates and shifts in GP-register shift forms whose exact printed
    mnemonic is left to the printer.) -/
theorem msgWOwnedAsm_shape :
    hasSub msgWOwnedAsm "sha256_msg_w"
      ∧ hasSub msgWOwnedAsm "UNHANDLED" = false := by native_decide

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `sha256_msg_w` into the
    `bench/thir_front_sha256_msgw_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha256_msgw_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha256_msgw_owned.s") msgWOwnedAsm
  IO.println "WROTE bench/thir_front_sha256_msgw_owned/gen/sha256_msgw_owned.s"
  IO.println "  (SHA-256 message-schedule word sha256MsgWThir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256MsgScheduleThirOwnedEmit
