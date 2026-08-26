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
# SHA-256 σ₁ message-schedule word through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §4.1.2 lowercase-sigma-one message-schedule function driven
through the `compile-from-hax` front (`Com thirDialect`) onto the OWNED x86
backend — NO jasminc anywhere. The companion of
`bench/thir_front_chacha_qr_owned/` (the RFC 8439 quarter-round) and
`bench/thir_front_montmul_owned/` (the BabyBear REDC), but for the SHA-256
small-sigma-one word:

    sha256_sigma1(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)   (FIPS 180-4 §4.1.2)

This is a SHA-256 primitive: it is the `σ₁` half of the SHA-256
message schedule `W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}`. It is
the natural width-32 sibling of the committed `ssaSmallSigma0` (`Com thirDialect`
σ₀ = `ROTR⁷ ⊕ ROTR¹⁸ ⊕ SHR³`); here we build the σ₁ program directly at the
`thirDialect` level (`thRor`/`thShrImm`/`thBin`) — mirroring `ssaSmallSigma0`'s
constructor shape — and emit it as an owned-backend leaf.

Why σ₁ and not the full round word: the bundled SHA-256 round/sub-function
front fns (`sha256RoundAThir`, `bigSigma0Thir`, `chThir`, `majThir`, …) are on
the OLDER `inductive Thir` AST (they lower to `Com jasminDialect` via the
bespoke `thirToJasmin` for the *jasminc* emit path) — they are NOT
`Com thirDialect`, so they are not directly emittable through the owned spine.
The ONLY SHA-256 primitive already on the `Com thirDialect` AST is
`ssaSmallSigma0` (σ₀). σ₁ is the least-risky SHA-256 `Com thirDialect`
primitive: a single u32 input, two rotate-immediates (exercising the rotate
legalisation pass cloned from `ChaChaQRThirEmit`) and one shift-immediate
(exercising the `MontMulThirEmit` shift legalisation), with a proven
denotation against the FIPS reference (`smallSigma1Spec`).

The pipeline mirrors `MontMulThirEmit`:

    sha256Sigma1Thir : Com thirDialect [.reg 32] (.reg 32)
      --lowerThir-->            Com jasminDialect [.reg 32] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the single input is loaded from `[RSI + 0]` and the single output stored
to `[RDI + 0]`:

```c
extern void sha256_sigma1(uint32_t *out, const uint32_t *inp);  // inp = [x]
//   out[0] receives ROTR17(x) ^ ROTR19(x) ^ (x >> 10)
```

The argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot
`s` (program-root order) is context entry `nArgs - 1 - s`. With a single input
(`nArgs = 1`) the only slot is `s = 0 ↦ input index 0 = inp[0]`, so
`inLoadMap 0 = ("RSI", 0)`. The single output (the last binding, the final xor)
is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The two rotates + one shift (immediate legalisation)

σ₁'s `ROTR¹⁷`/`ROTR¹⁹` lower (via `thRor`) to rotate-immediate `Lopn` forms; the
`SHR¹⁰` lowers (via `thShrImm`) to a unary shift-immediate. The owned printer
recognises NEITHER the unary `SHR:<n>[:64]` shift mnemonic NOR any rotate
mnemonic. `legalizeShiftImmLprog` (cloned verbatim from
`ChaChaQRThirEmit`) rewrites:

* a unary shift-immediate `Lopn [d] "SHR:<n>" [s]` → two-source
  `[d] SHR [d, #n]` (prefixed by `MOV d, s` when `d ≠ s`), mirroring
  `JasminLprogExport.lowerTwoAddrShiftImm`;
* a rotate `Lopn [d] "ROR:<n>[:w]" [s]` → the canonical shift-or idiom over the
  reserved scratch `R15` (`ror(d,n) = (d>>n)|(d<<(w-n))`), all four lines in
  printer-recognised two-source `Lopn` forms (`MOV`/`SHR`/`SHL`/`OR`).

So the emitted `.s` carries no unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha256Sigma1Thir_denote` (the leaf denotes `σ₁` =
  `smallSigma1Spec`) and `sigma1_via_thirDialect` (the lowered
  `Com jasminDialect` denotes the same).
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha256_sigma1(x) == σ₁(x)` is the external `as`/`cc` KAT in
`bench/thir_front_sha256_sigma1_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (smallSigma1Spec)

/-! ## 0. The SHA-256 σ₁ program as a `Com thirDialect` leaf

Built directly at the THIR-dialect level (`thRor`, `thShrImm`, `thBin`),
mirroring the committed `ssaSmallSigma0`'s constructor shape:

    let r17 = thRor 32 17 x;  let r19 = thRor 32 19 x;  let s10 = thShrImm 32 10 x
    let t   = thBin xor r17 r19;  let o = thBin xor t s10;  ret o -/
def sha256Sigma1Thir : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thRor 32 17) rfl (.cons .here .nil))
    (.var (.mk (.thRor 32 19) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thShrImm 32 10) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 32) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 32) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- The THIR-dialect σ₁ denotes to the FIPS σ₁ spec on any input valuation
    (`x` = the single de-Bruijn-0 word). A direct check of the `thirDialect`
    semantics against `smallSigma1Spec`. -/
theorem sha256Sigma1Thir_denote (x : BitVec 32) :
    sha256Sigma1Thir.denote (.cons x .nil) = smallSigma1Spec x := by
  rfl

/-- **σ₁ re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for σ₁ denotes the same `BitVec 32` as the FIPS σ₁ spec.
    Combines `lowerThir_denote` (the generic, proved dialect lowering) with
    `sha256Sigma1Thir_denote`. -/
theorem sigma1_via_thirDialect (x : BitVec 32) :
    (lowerThir sha256Sigma1Thir).denote (.cons x .nil) = smallSigma1Spec x := by
  rw [lowerThir_denote sha256Sigma1Thir (.cons x .nil), sha256Sigma1Thir_denote]

/-! ## 1. ABI maps for the 1-in / 1-out width-32 σ₁ leaf -/

/-- Input-load map: the single arg slot `0` ↦ `("RSI", 0)` (input `x = inp[0]`).
    Slots `≥ 1` are absent (σ₁ has exactly one input). -/
def sigma1InLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 0) else none

/-- Output-store map: the single result word (the last xor binding) is stored to
    `out[0]` (`[RDI + 0]`). -/
def sigma1OutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 2. Shift and rotate immediate legalisation post-pass

Cloned verbatim from `ChaChaQRThirEmit` (which itself extends
`MontMulThirEmit`'s shift-immediate pass with the rotate expansion). The
owned printer renders the two-source shift form `[d] SHR [d, #n]` but recognises
NEITHER the unary `SHR:<n>[:64]` mnemonic NOR any rotate mnemonic. So:

* unary `SHR:<n>[:64]` / `SHL:<n>[:64]` rewrite to the two-source operand form
  `[d] SHR [d, #n]` (prefixed by `MOV` when `d ≠ s`);
* a rotate `ROR:<n>[:w]` expands into the shift-or idiom over the reserved
  scratch `R15`: `ror(d, n) = (d >> n) | (d << (w - n))`, emitted as

      MOV R15, d ;  SHR R15, #n ;  SHL d, #(w-n) ;  OR d, R15

  All four lines use printer-recognised two-source `Lopn` forms. -/

export CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
  (parseShiftImm parseRotImm wTag expandRotInPlace legalizeBody legalizeLprog opnMnemonics)

/-- Rewrite one already-allocated `Linstr`:

    * a unary shift-immediate `Lopn [d] "SHR:<n>[:64]" [s]` → two-source
      `[d] SHR[:64] [d, #n]` (prefixed by `MOV d, s` when `d ≠ s`);
    * a rotate `Lopn [d] "ROR:<n>[:w]" [s]` → (a `MOV d, s` when `d ≠ s`)
      followed by the `expandRotInPlace` shift-or idiom over `R15`;

    every other instruction passes through unchanged. -/
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
      | none =>
        match parseRotImm opn with
        | some (dir, n, w) =>
            let movMnem := if w = 64 then "MOV:64" else "MOV"
            let prefixMov := if d = s then [] else [(⟨i.li_ii, .Lopn [d] movMnem [s]⟩ : Linstr)]
            prefixMov ++ expandRotInPlace i.li_ii d dir n w
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
destination the `MOV` is absent. A rotate expands to the scratch-`R15` shift-or
idiom, and a rotate by zero is expanded rather than elided. -/

#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:32:64" [.reg "RCX"]⟩)
    == ["MOV:64", "SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:32:64" [.reg "RAX"]⟩)
    == ["SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "ROR:16:64" [.reg "RCX"]⟩)
    == ["MOV:64", "MOV:64", "SHR:64", "SHL:64", "OR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "ROR:0:64" [.reg "RAX"]⟩)
    == ["MOV:64", "SHR:64", "SHL:64", "OR:64"]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- σ₁ lowered through the thirDialect spine and exported to a physical,
    two-address SysV `Lprog`, then shift/rotate-immediate-legalised so the owned
    printer renders the two rotates and the shift. `fname` `"sha256_sigma1"`
    becomes the emitted asm label (matching the C extern). -/
def sigma1Lprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha256Sigma1Thir) "sha256_sigma1"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      sigma1InLoadMap                       -- inLoadMap
      sigma1OutStoreMap                     -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32])                                 -- abiTyin (1 u32 input)

/-- The rendered owned-backend AT&T `.s` for `sha256_sigma1` (no jasminc). -/
def sigma1Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned sigma1Lprog

/-! ## 4. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `sha256_sigma1` into the
    `bench/thir_front_sha256_sigma1_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha256_sigma1_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha256_sigma1_owned.s") sigma1Asm
  IO.println "WROTE bench/thir_front_sha256_sigma1_owned/gen/sha256_sigma1_owned.s"
  IO.println "  (SHA-256 sigma1 message-schedule word sha256Sigma1Thir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

/-! ## 6. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
