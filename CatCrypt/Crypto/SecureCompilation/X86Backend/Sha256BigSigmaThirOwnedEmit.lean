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
# SHA-256 Σ₀ and Σ₁ (big-Sigma, width 32) through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §4.1.2 uppercase-Sigma round sub-functions driven through the
`compile-from-hax` front (`Com thirDialect`) onto the OWNED x86 backend — NO
jasminc anywhere. The width-32 sibling of `Sha256Sigma1ThirOwnedEmit` (the σ₁
message-schedule word), but for the two big-Sigma functions used in the SHA-256
round:

    Σ₀(x) = ROTR²(x)  ⊕ ROTR¹³(x) ⊕ ROTR²²(x)   (FIPS 180-4 §4.1.2)
    Σ₁(x) = ROTR⁶(x)  ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)

These are genuinely-SHA-256 primitives: `Σ₀` feeds `T₂ = Σ₀(a) + Maj(a,b,c)`
and `Σ₁` feeds `T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ`. They are PURE rotates —
no shift — so simpler than σ₁ (which also has a `SHR¹⁰`): each is three
rotate-immediates xored together (`thRor`/`thBin`, no `thShrImm`). We build each
program directly at the `thirDialect` level — mirroring `ssaSmallSigma0`'s and
`sha256Sigma1Thir`'s constructor shape — and emit both as owned-backend leaves
combined into one `.s`.

The pipeline mirrors `Sha256Sigma1ThirOwnedEmit`:

    sha256BigSigma{0,1}Thir : Com thirDialect [.reg 32] (.reg 32)
      --lowerThir-->            Com jasminDialect [.reg 32] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the single input is loaded from `[RSI + 0]` and the single output stored
to `[RDI + 0]`:

```c
extern void sha256_bigsigma0(uint32_t *out, const uint32_t *inp);  // inp = [a]
extern void sha256_bigsigma1(uint32_t *out, const uint32_t *inp);  // inp = [e]
//   out[0] receives ROTR2(a) ^ ROTR13(a) ^ ROTR22(a)   (Σ₀)
//   out[0] receives ROTR6(e) ^ ROTR11(e) ^ ROTR25(e)   (Σ₁)
```

With a single input (`nArgs = 1`) the only slot is `s = 0 ↦ input index 0 =
inp[0]`, so `inLoadMap 0 = ("RSI", 0)` and `outStoreMap = [("RDI", 0)]` (reused
from `Sha256Sigma1ThirOwnedEmit.sigma1InLoadMap` / `sigma1OutStoreMap`).

## The three rotates (immediate legalisation)

Each big-Sigma is three `ROTR` rotate-immediates xored together; they lower (via
`thRor`) to rotate-immediate `Lopn` forms. The owned printer recognises no
rotate mnemonic, so `legalizeShiftImmLprog` (reused from
`Sha256Sigma1ThirOwnedEmit`) expands each rotate into the shift-or idiom over
the reserved scratch `R15` (`ror(d,n) = (d>>n)|(d<<(w-n))`), all four lines in
printer-recognised two-source `Lopn` forms (`MOV`/`SHR`/`SHL`/`OR`). There is no
`SHR:<n>` unary shift to legalise here (these are pure rotates). So the emitted
`.s` carries no unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha256BigSigma0Thir_denote` / `sha256BigSigma1Thir_denote`
  (each leaf denotes the FIPS big-Sigma = `bigSigma0Spec` / `bigSigma1Spec`) and
  `bigSigma{0,1}_via_thirDialect` (the lowered `Com jasminDialect` denotes the
  same).
* **Verified (printer)**: the shape lemma below pins that the emitted combined
  `.s` carries both SysV leaf labels and has no unhandled-op sentinel.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity to the FIPS reference is the external `as`/`cc` KAT in
`bench/thir_front_sha256_bigsigma_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256BigSigmaThirOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (bigSigma0Spec bigSigma1Spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirOwnedEmit
  (sigma1InLoadMap sigma1OutStoreMap legalizeShiftImmLprog)

/-! ## 0. The SHA-256 big-Sigma programs as `Com thirDialect` leaves

Built directly at the THIR-dialect level (`thRor`, `thBin`), mirroring the
committed `ssaSmallSigma0` / `sha256Sigma1Thir` constructor shape but with three
PURE rotates (no `thShrImm`):

    let rA = thRor 32 a x;  let rB = thRor 32 b x;  let rC = thRor 32 c x
    let t  = thBin xor rA rB;  let o = thBin xor t rC;  ret o

The de-Bruijn discipline (each `.var` prepends one binding):
`[x]` → `[rA,x]` → `[rB,rA,x]` → `[rC,rB,rA,x]`; the first xor reads
`rA` (`there (there here)`) and `rB` (`there here`) giving `[t,rC,rB,rA,x]`; the
second xor reads `t` (`here`) and `rC` (`there here`), so the result is
`(rA ⊕ rB) ⊕ rC`. -/

/-- SHA-256 Σ₀ = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x), as a `Com thirDialect`. -/
def sha256BigSigma0Thir : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thRor 32 2) rfl (.cons .here .nil))
    (.var (.mk (.thRor 32 13) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thRor 32 22) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 32) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 32) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- SHA-256 Σ₁ = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x), as a `Com thirDialect`. -/
def sha256BigSigma1Thir : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thRor 32 6) rfl (.cons .here .nil))
    (.var (.mk (.thRor 32 11) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thRor 32 25) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 32) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 32) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- The THIR-dialect Σ₀ denotes to the FIPS Σ₀ spec on any input valuation. -/
theorem sha256BigSigma0Thir_denote (x : BitVec 32) :
    sha256BigSigma0Thir.denote (.cons x .nil) = bigSigma0Spec x := by
  rfl

/-- The THIR-dialect Σ₁ denotes to the FIPS Σ₁ spec on any input valuation. -/
theorem sha256BigSigma1Thir_denote (x : BitVec 32) :
    sha256BigSigma1Thir.denote (.cons x .nil) = bigSigma1Spec x := by
  rfl

/-- **Σ₀ re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for Σ₀ denotes the same `BitVec 32` as the FIPS Σ₀
    spec. -/
theorem bigSigma0_via_thirDialect (x : BitVec 32) :
    (lowerThir sha256BigSigma0Thir).denote (.cons x .nil) = bigSigma0Spec x := by
  rw [lowerThir_denote sha256BigSigma0Thir (.cons x .nil), sha256BigSigma0Thir_denote]

/-- **Σ₁ re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for Σ₁ denotes the same `BitVec 32` as the FIPS Σ₁
    spec. -/
theorem bigSigma1_via_thirDialect (x : BitVec 32) :
    (lowerThir sha256BigSigma1Thir).denote (.cons x .nil) = bigSigma1Spec x := by
  rw [lowerThir_denote sha256BigSigma1Thir (.cons x .nil), sha256BigSigma1Thir_denote]

/-! ## 1. The owned `Lprog`s and combined AT&T emission (no jasminc)

Each big-Sigma is exported to a physical, two-address SysV `Lprog` and
rotate-legalised (reusing `Sha256Sigma1ThirOwnedEmit.legalizeShiftImmLprog`, the
ABI maps, and the 2-pointer SysV signature). The two single-func `Lprog`s are
then merged into one `Lprog` so a single `.s` carries both leaves
(`sha256_bigsigma0` and `sha256_bigsigma1`). -/

/-- Σ₀ lowered through the thirDialect spine, exported to a physical SysV
    `Lprog`, then rotate-immediate-legalised. `fname` `"sha256_bigsigma0"`
    becomes the emitted asm label (matching the C extern). -/
def bigSigma0OwnedLprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha256BigSigma0Thir) "sha256_bigsigma0"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      sigma1InLoadMap                       -- inLoadMap (single arg ↦ RSI[0])
      sigma1OutStoreMap                     -- outStoreMap (result ↦ RDI[0])
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32])                                 -- abiTyin (1 u32 input)

/-- Σ₁ lowered through the thirDialect spine, exported to a physical SysV
    `Lprog`, then rotate-immediate-legalised. `fname` `"sha256_bigsigma1"`
    becomes the emitted asm label (matching the C extern). -/
def bigSigma1OwnedLprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha256BigSigma1Thir) "sha256_bigsigma1"
      (fun _ => none)
      (fun _ => none)
      sigma1InLoadMap
      sigma1OutStoreMap
      ["RDI", "RSI"]
      [32])

/-- The two big-Sigma leaves merged into ONE `Lprog`, so a single rendered `.s`
    exports both `sha256_bigsigma0` and `sha256_bigsigma1`. -/
def bigSigmaOwnedLprog : Lprog :=
  { bigSigma0OwnedLprog with
    lp_funcs := bigSigma0OwnedLprog.lp_funcs ++ bigSigma1OwnedLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for both big-Sigmas (no jasminc). -/
def bigSigmaOwnedAsm : String := renderLprogAtt bigSigmaOwnedLprog

/-! ## 2. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The emitted combined `.s` carries BOTH SysV leaf labels and has no
    unhandled-op sentinel. (Rotate mnemonics are not asserted — the legalisation
    lands the rotates in GP-register shift forms whose exact printed mnemonic is
    left to the printer.) -/
theorem bigSigmaOwnedAsm_shape :
    hasSub bigSigmaOwnedAsm "sha256_bigsigma0"
      ∧ hasSub bigSigmaOwnedAsm "sha256_bigsigma1"
      ∧ hasSub bigSigmaOwnedAsm "UNHANDLED" = false := by native_decide

/-! ## 3. Emit driver -/

/-- Write the owned-backend `.s` for both big-Sigmas into the
    `bench/thir_front_sha256_bigsigma_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha256_bigsigma_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha256_bigsigma_owned.s") bigSigmaOwnedAsm
  IO.println "WROTE bench/thir_front_sha256_bigsigma_owned/gen/sha256_bigsigma_owned.s"
  IO.println "  (SHA-256 big-Sigma round sub-functions sha256BigSigma0Thir /"
  IO.println "   sha256BigSigma1Thir through Com[thir] -> lowerThir ->"
  IO.println "   toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend,"
  IO.println "   NO jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256BigSigmaThirOwnedEmit
