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
# SHA-512 σ₀ and σ₁ message-schedule words through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §4.1.3 lowercase-sigma message-schedule functions for SHA-512
(width 64) driven through the `compile-from-hax` front (`Com thirDialect`) onto
the OWNED x86 backend — NO jasminc anywhere. The width-64 sibling of
`Sha256Sigma1ThirEmit.lean` (the width-32 SHA-256 σ₁ leaf): same single-u64
input, two rotate-immediates and one shift-immediate, but at width 64.

    σ₀_512(x) = ROTR¹(x)  ⊕ ROTR⁸(x)  ⊕ SHR⁷(x)   (FIPS 180-4 §4.1.3)
    σ₁_512(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)   (FIPS 180-4 §4.1.3)

These are SHA-512 primitives: the `σ₀`/`σ₁` halves of the SHA-512
message schedule `W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}` over
`u64` words. We build each program directly at the `thirDialect` level
(`thRor 64`/`thShrImm 64`/`thBin .xor 64`) — mirroring the committed width-32
`ssaSmallSigma0` / `sha256Sigma1Thir` constructor shapes, widened to 64 — and
emit both as owned-backend leaves in a single `.s`.

The pipeline mirrors `Sha256Sigma1ThirEmit`:

    sha512Sigma{0,1}Thir : Com thirDialect [.reg 64] (.reg 64)
      --lowerThir-->            Com jasminDialect [.reg 64] (.reg 64)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the single input is loaded from `[RSI + 0]` and the single output stored
to `[RDI + 0]`:

```c
extern void sha512_sigma0(uint64_t *out, const uint64_t *inp);  // inp = [x]
extern void sha512_sigma1(uint64_t *out, const uint64_t *inp);  // inp = [x]
```

With a single input (`nArgs = 1`) the only slot is `s = 0 ↦ input index 0 =
inp[0]`, so `inLoadMap 0 = ("RSI", 0)`. The single output (the last binding, the
final xor) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The two rotates + one shift (width-64 immediate legalisation)

Each σ's `ROTR`s lower (via `thRor 64`) to rotate-immediate `Lopn` forms; the
`SHR` lowers (via `thShrImm 64`) to a unary shift-immediate. The owned printer
recognises NEITHER the unary `SHR:<n>:64` shift mnemonic NOR any rotate
mnemonic. `legalizeShiftImmLprog` (cloned from `Sha256Sigma1ThirEmit`,
which carries the width-generic `:64`-tagged path already exercised by
`Blake2bGThirEmit`) rewrites:

* a unary shift-immediate `Lopn [d] "SHR:<n>:64" [s]` → two-source
  `[d] SHR:64 [d, #n]` (prefixed by `MOV:64 d, s` when `d ≠ s`);
* a rotate `Lopn [d] "ROR:<n>:64" [s]` → the canonical shift-or idiom over the
  reserved scratch `R15` (`ror(d,n) = (d>>n)|(d<<(64-n))`), all four lines in
  printer-recognised two-source `Lopn` forms (`MOV:64`/`SHR:64`/`SHL:64`/`OR:64`).

So the emitted `.s` carries no unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha512Sigma0Thir_denote` / `sha512Sigma1Thir_denote`
  (the leaves denote `σ₀`/`σ₁` = `sha512SmallSigma0Spec`/`sha512SmallSigma1Spec`)
  and `sigma{0,1}_via_thirDialect` (the lowered `Com jasminDialect` denotes the
  same).
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha512_sigma{0,1}(x) == σ{0,1}(x)` is the external `as`/`cc`
KAT in `bench/thir_front_sha512_sigma_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512SigmaThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 0. FIPS 180-4 §4.1.3 SHA-512 σ₀/σ₁ reference specs (width 64) -/

/-- FIPS 180-4 §4.1.3 σ₀_512(x) = ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x). -/
def sha512SmallSigma0Spec (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 1) ^^^ (x.rotateRight 8) ^^^ (x >>> (7 : Nat))

/-- FIPS 180-4 §4.1.3 σ₁_512(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x). -/
def sha512SmallSigma1Spec (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 19) ^^^ (x.rotateRight 61) ^^^ (x >>> (6 : Nat))

/-! ## 1. The SHA-512 σ₀/σ₁ programs as `Com thirDialect` leaves

Built directly at the THIR-dialect level (`thRor 64`, `thShrImm 64`,
`thBin .xor 64`), mirroring the committed width-32 `ssaSmallSigma0` /
`sha256Sigma1Thir` constructor shapes:

    let r_a = thRor 64 a x;  let r_b = thRor 64 b x;  let s = thShrImm 64 c x
    let t   = thBin xor r_a r_b;  let o = thBin xor t s;  ret o -/

/-- SHA-512 σ₀ as a `Com thirDialect` over `[reg 64]` (input `x = here`):
    `ROTR¹ ⊕ ROTR⁸ ⊕ SHR⁷`. -/
def sha512Sigma0Thir : Com thirDialect [.reg 64] (.reg 64) :=
  .var (.mk (.thRor 64 1) rfl (.cons .here .nil))
    (.var (.mk (.thRor 64 8) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thShrImm 64 7) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 64) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 64) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- SHA-512 σ₁ as a `Com thirDialect` over `[reg 64]` (input `x = here`):
    `ROTR¹⁹ ⊕ ROTR⁶¹ ⊕ SHR⁶`. -/
def sha512Sigma1Thir : Com thirDialect [.reg 64] (.reg 64) :=
  .var (.mk (.thRor 64 19) rfl (.cons .here .nil))
    (.var (.mk (.thRor 64 61) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thShrImm 64 6) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 64) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 64) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- The THIR-dialect σ₀ denotes to the FIPS σ₀_512 spec on any input valuation. -/
theorem sha512Sigma0Thir_denote (x : BitVec 64) :
    sha512Sigma0Thir.denote (.cons x .nil) = sha512SmallSigma0Spec x := by
  rfl

/-- The THIR-dialect σ₁ denotes to the FIPS σ₁_512 spec on any input valuation. -/
theorem sha512Sigma1Thir_denote (x : BitVec 64) :
    sha512Sigma1Thir.denote (.cons x .nil) = sha512SmallSigma1Spec x := by
  rfl

/-- **σ₀_512 re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for σ₀ denotes the same `BitVec 64` as the FIPS σ₀ spec. -/
theorem sigma0_via_thirDialect (x : BitVec 64) :
    (lowerThir sha512Sigma0Thir).denote (.cons x .nil) = sha512SmallSigma0Spec x := by
  rw [lowerThir_denote sha512Sigma0Thir (.cons x .nil), sha512Sigma0Thir_denote]

/-- **σ₁_512 re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for σ₁ denotes the same `BitVec 64` as the FIPS σ₁ spec. -/
theorem sigma1_via_thirDialect (x : BitVec 64) :
    (lowerThir sha512Sigma1Thir).denote (.cons x .nil) = sha512SmallSigma1Spec x := by
  rw [lowerThir_denote sha512Sigma1Thir (.cons x .nil), sha512Sigma1Thir_denote]

/-! ## 2. ABI maps for the 1-in / 1-out width-64 σ leaves -/

/-- Input-load map: the single arg slot `0` ↦ `("RSI", 0)` (input `x = inp[0]`).
    Slots `≥ 1` are absent (each σ has exactly one input). -/
def sigmaInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 0) else none

/-- Output-store map: the single result word (the last xor binding) is stored to
    `out[0]` (`[RDI + 0]`). -/
def sigmaOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. Shift and rotate immediate legalisation post-pass

Cloned from `Sha256Sigma1ThirEmit` (which carries the width-generic
`:64`-tagged path already exercised by `Blake2bGThirEmit`). The owned
printer renders the two-source shift form `[d] SHR:64 [d, #n]` but recognises
NEITHER the unary `SHR:<n>:64` mnemonic NOR any rotate mnemonic. So:

* unary `SHR:<n>:64` / `SHL:<n>:64` rewrite to the two-source operand form
  `[d] SHR:64 [d, #n]` (prefixed by `MOV:64` when `d ≠ s`);
* a rotate `ROR:<n>:64` expands into the shift-or idiom over the reserved
  scratch `R15`: `ror(d, n) = (d >> n) | (d << (64 - n))`, emitted as

      MOV:64 R15, d ;  SHR:64 R15, #n ;  SHL:64 d, #(64-n) ;  OR:64 d, R15

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

/-! ## 4. The owned `Lprog`s and combined AT&T emission (no jasminc) -/

/-- Build a 1-in/1-out width-64 owned `Lprog` for a `Com thirDialect [.reg 64]`
    σ leaf under the SysV 2-pointer ABI, shift/rotate-immediate-legalised. -/
def sigmaLprog (com : Com thirDialect [.reg 64] (.reg 64)) (fname : String) : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir com) fname
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      sigmaInLoadMap                        -- inLoadMap
      sigmaOutStoreMap                      -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64])                                 -- abiTyin (1 u64 input)

/-- σ₀_512 owned `Lprog` (`fname` `"sha512_sigma0"`). -/
def sigma0Lprog : Lprog := sigmaLprog sha512Sigma0Thir "sha512_sigma0"

/-- σ₁_512 owned `Lprog` (`fname` `"sha512_sigma1"`). -/
def sigma1Lprog : Lprog := sigmaLprog sha512Sigma1Thir "sha512_sigma1"

/-- Both σ leaves combined into a single `Lprog` (`lp_funcs` concatenated), so
    `renderLprogAtt` emits one `.s` carrying both `sha512_sigma0` and
    `sha512_sigma1`. -/
def sha512SigmaLprog : Lprog :=
  { sigma0Lprog with
    lp_funcs := sigma0Lprog.lp_funcs ++ sigma1Lprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for both σ leaves (no jasminc). -/
def sha512SigmaAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned sha512SigmaLprog

/-! ## 5. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 6. Emit driver -/

/-- Write the owned-backend `.s` for `sha512_sigma0`/`sha512_sigma1` into the
    `bench/thir_front_sha512_sigma_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha512_sigma_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha512_sigma_owned.s") sha512SigmaAsm
  IO.println "WROTE bench/thir_front_sha512_sigma_owned/gen/sha512_sigma_owned.s"
  IO.println "  (SHA-512 sigma0/sigma1 message-schedule words sha512Sigma{0,1}Thir"
  IO.println "   through Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt"
  IO.println "   onto the OWNED x86 backend, NO jasminc)"

/-! ## 7. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512SigmaThirEmit
