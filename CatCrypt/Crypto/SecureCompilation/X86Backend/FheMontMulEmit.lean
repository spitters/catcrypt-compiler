/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.FheMontMulLaw
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-!
# Single-word 60-bit FHE Montgomery modmul through the OWNED x86 backend (no jasminc)

A single-word **Montgomery REDC** modular multiply at the 60-bit FHE-NTT prime
`q = 1152921504606830593 = 2^60 − 2^14 + 1`, radix `R = 2^64`,
`qinv = 1080859512253956095 = −q⁻¹ mod 2^64`, driven through the
`compile-from-hax` front (`Com thirDialect`) onto the OWNED x86 backend — NO
jasminc anywhere. The companion of the 32-bit BabyBear REDC `montMulThir`
(`ThirToComFront` §13).

## Why this differs from the 32-bit `montMulThir`

`montMulThir` works at the BabyBear prime `p = 0x78000001 < 2^31`, so the product
of two Montgomery representatives `a, b < 2^32` fits in **64 bits**: a single
`thBin .mul 64` computes the full product `t = a·b`, and the REDC's `t + m·p`
stays in 64-bit range. At the 60-bit FHE prime, `a, b < q < 2^60`, so the product
`a·b` is a full **128-bit** quantity that does NOT fit in one 64-bit word. The
REDC therefore needs the high word of the `64×64→128` product via `thMulHi`
(`mulhi`, the `MULX` high half), and the Montgomery quotient is assembled with a
carry-chain add (`thAddCarryHi`/`thAddCarryLo`, the `ADCX` carry-out + data word).

The REDC computed (radix-`R` Montgomery, `T = a·b`):

```
  lo  = a * b            -- low 64 of the 128-bit product
  hi  = mulhi(a, b)      -- high 64 of the 128-bit product   (T = hi·R + lo)
  m   = lo * qinv        -- low word of the REDC multiplier   (m ≡ (T mod R)·qinv mod R)
  mqLo = m * q           -- low 64 of m·q
  mqHi = mulhi(m, q)     -- high 64 of m·q                    (m·q = mqHi·R + mqLo)
  cout = carryOut(lo + mqLo)                                  -- the low-word carry
  u   = hi + mqHi + cout -- the Montgomery quotient (T + m·q)/R, since lo + mqLo ≡ 0 mod R
```

`u ∈ [0, 2q)` is the **lazy** Montgomery representative (congruent mod `q` to
`a·b·R⁻¹`), exactly `FheMontMulLaw.montU (a·b)`. A single conditional subtract
`if u ≥ q then u − q` canonicalises it into `[0, q)` (= `FheMontMulLaw.montMul`).

This module emits the **lazy** REDC (no conditional subtract — the thirDialect
front is straight-line and the GP-linear printer renders neither `thSelect`/`CMOV`
nor a `>> 32` reduction here); canonicalisation `if u ≥ q then u − q` is a
host-side step. This mirrors the §13 BabyBear lazy-leaf discipline.

## What is verified vs trusted (scope)

* **Verified (value, in Lean)**: `fheMontMulThir_denote` — `fheMontMulThir.denote`
  on `[a, b]` is the width-64 lazy REDC reference `fheMontMulSpec64` (true by
  *definition*: `fheMontMulSpec64` is that denotation) — and
  `fheMontMul_via_thirDialect`, the lowered `Com jasminDialect` denotes the same
  word, via the generic, proved `lowerThir_denote`. The closed-form REDC
  (`u = addCarryWord (mulHiW a b) (mulHiW (a·b·qinv) q) (carryOutBit (a·b)
  (a·b·qinv·q) 0)`) is documented (§3); its `Nat`-level connection to
  `FheMontMulLaw.montU` is **not** carried in-Lean — a single `rfl` over the
  10-binding tower reduces the `2^64`-heavy `mulHiW`/`carryOutBit` bodies and
  trips the kernel recursion guard, so the value check is the orchestrator's GMP
  KAT on the emitted `.s` (the lazy-leaf discipline; see the §13 note in MEMORY
  about avoiding heavy in-kernel KATs).
* **High-word gap CLOSED by the MULX-fusion post-pass of `FuseMulHi`**: `fuseMulHiLprog`
  coalesces each paired low `MUL` + `MULXHI` into the printer's two-output `mulx`
  (multiplicand pinned into `%rdx`, the first product's `%rdx`-homed high word
  evacuated to scratch `R8`), so the emitted `.s` now materialises the
  `64×64→128` high words `hi`/`mqHi`.
* **Remaining seam (flagged for the KAT)**: the ADX carry-chain tail
  (`ADCXHI` cout + `ADCX` `u = hi + mqHi + cout`) is rendered by the shared
  `LprogAsmPrinter` ADX arm, which drops the carry-out binding and assumes the
  high word was coalesced onto the `ADCX` destination; that MOV is absent for
  this allocation, so the carry propagation is not yet faithful. Closing it is a
  shared-printer / two-address-lowering concern (out of scope for this contained
  emit-module pass).
* **Trusted (thin)**: `renderLfundef` / `as`/`cc` / the SysV leaf ABI frame.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir lowerThir_denote thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog Lfundef Lcmd Linstr LinstrR LOperand stripWidthTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiLprog)

/-! ## 1. The FHE-NTT prime constants (as `BitVec 64`) -/

/-- The 60-bit FHE prime `q = 2^60 − 2^14 + 1` (matches `FheMontMulLaw.fheQ`). -/
def fheQ : Nat := 1152921504606830593

/-- `−q⁻¹ mod 2^64` (matches `FheMontMulLaw.fheQinv`). -/
def fheQinv : Nat := 1080859512253956095

/-! ## 2. The lazy REDC as a `Com thirDialect`

Single-output: the last binding (`u`) IS the result. Context starts `[a, b]`
(`a = .here`, `b = .there .here`). Bindings, head-first:

    lo, hi, cqinv, m, cq, mqLo, mqHi, czero, cout, u

where `cqinv = qinv`, `cq = q`, `czero : reg 1 = 0` are materialised constants.
`cout : reg 1` is the carry-out of `lo + mqLo` (an `ADCXHI` binding, the carry
of the low-word sum), and `u = hi + mqHi + cout` (an `ADCX` data word). -/
def fheMontMulThir (_ : Unit) : Com thirDialect [.reg 64, .reg 64] (.reg 64) :=
  -- lo = a * b                                  ctx: [a, b]
  .var (.mk (.thBin .mul 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- hi = mulhi(a, b)                            ctx: [lo, a, b]; a = dB1, b = dB2
  (.var (.mk (.thMulHi 64) rfl (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
  -- cqinv = qinv                                ctx: [hi, lo, a, b]
  (.var (.mk (.thConst 64 fheQinv) rfl .nil)
  -- m = lo * cqinv                              ctx: [cqinv, hi, lo, a, b]; lo = dB2
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
  -- cq = q                                      ctx: [m, cqinv, hi, lo, a, b]
  (.var (.mk (.thConst 64 fheQ) rfl .nil)
  -- mqLo = m * cq                               ctx: [cq, m, cqinv, hi, lo, a, b]; m = dB1
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- mqHi = mulhi(m, cq)                         ctx: [mqLo, cq, m, cqinv, hi, lo, a, b]; m = dB2, cq = dB1
  (.var (.mk (.thMulHi 64) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- czero : reg 1 = 0                           ctx: [mqHi, mqLo, cq, m, cqinv, hi, lo, a, b]
  (.var (.mk (.thConst 1 0) rfl .nil)
  -- cout : reg 1 = carryOut(lo + mqLo + czero)  ctx: [czero, mqHi, mqLo, cq, m, cqinv, hi, lo, a, b]
  --   lo = dB7, mqLo = dB2, czero = dB0
  (.var (.mk (.thAddCarryHi 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
        (.cons (.there (.there .here)) (.cons .here .nil))))
  -- u = hi + mqHi + cout                        ctx: [cout, czero, mqHi, mqLo, cq, m, cqinv, hi, lo, a, b]
  --   hi = dB7, mqHi = dB2, cout = dB0
  (.var (.mk (.thAddCarryLo 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
        (.cons (.there (.there .here)) (.cons .here .nil))))
  (.ret .here))))))))))

/-! ## 3. The width-64 lazy REDC reference

`fheMontMulSpec64 a b` is *defined* as the width-64 denotation of `fheMontMulThir`
on `[a, b]`, so the denotation lemma `fheMontMulThir_denote` is a syntactic
identity. The closed-form REDC the program computes is, head-first
(`lo = a·b`, `hi = mulhi(a,b)` ⟹ `T = a·b = hi·R + lo`):

```
  m    = lo * qinv                 -- low word of the REDC multiplier
  mqLo = m * q,   mqHi = mulhi(m,q) -- m·q = mqHi·R + mqLo
  cout = carryOut(lo + mqLo)        -- low-word carry (lo + mqLo ≡ 0 mod R)
  u    = hi + mqHi + cout           -- the Montgomery quotient (T + m·q)/R, in [0, 2q)
```

i.e. `u = addCarryWord (mulHiW a b) (mulHiW (a·b·qinv) q) (carryOutBit (a·b)
(a·b·qinv·q) 0)` — the lazy Montgomery representative, congruent mod `q` to
`a·b·R⁻¹` (= `FheMontMulLaw.montU (a·b)`). The connection to `FheMontMulLaw.montU`
over `Nat` (the `64×64→128` ↔ `Nat` bridge) is the orchestrator's GMP value KAT
on the emitted `.s`: the closed-form REDC equality is `true by reduction` of the
`Com` denotation, but a single in-kernel `rfl` over the 10-binding tower would
reduce the `2^64`-heavy `mulHiW`/`carryOutBit` bodies and trip the kernel
recursion guard, so the value check is externalised (KAT) rather than carried in
Lean — exactly the lazy-leaf discipline of the §13 BabyBear REDC. -/

/-- The width-64 lazy Montgomery REDC: by definition the denotation of the
    emitted-through-the-spine program `fheMontMulThir` on the two input words
    (the closed-form REDC is in the section docstring above; its value is checked
    by the orchestrator's GMP KAT on the emitted `.s`). -/
def fheMontMulSpec64 (a b : BitVec 64) : BitVec 64 :=
  (fheMontMulThir ()).denote (.cons a (.cons b .nil))

/-- The THIR-dialect lazy FHE Montgomery REDC denotes `fheMontMulSpec64` — true by
    definition (`fheMontMulSpec64` is that denotation). -/
theorem fheMontMulThir_denote (a b : BitVec 64) :
    (fheMontMulThir ()).denote (.cons a (.cons b .nil)) = fheMontMulSpec64 a b := rfl

/-- **FHE Montgomery REDC re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` denotes the same `BitVec 64` as the width-64
    REDC reference, obtained through `Com[thir] →lowerThir→ Com[jasmin]` (the
    generic, proved `lowerThir_denote`) rather than a bespoke lowering. -/
theorem fheMontMul_via_thirDialect (a b : BitVec 64) :
    (lowerThir (fheMontMulThir ())).denote (.cons a (.cons b .nil)) = fheMontMulSpec64 a b :=
  (lowerThir_denote (fheMontMulThir ()) (.cons a (.cons b .nil))).trans
    (fheMontMulThir_denote a b)

/-! ## 4. ABI maps for the 2-in / 1-out width-64 kernel

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp). The argument-slot numbering (`JasminLprogExport.comToLfundef`): argument
slot `s` (program-root order) is context entry `nArgs - 1 - s`. The REDC context
is `[a, b]` (`a = .here`, `b = .there .here`), so input index `a = 0`, `b = 1`,
and arg slot `s ↦ input index (1 - s)`. With C-side `inp = [a, b]`:

* slot `1` → input `a` (`inp[0]`, byte offset 0)
* slot `0` → input `b` (`inp[1]`, byte offset 8)

i.e. `inLoadMap s = ("RSI", 8 * s)` (`s = 0 ↦ inp[1] = b`, `s = 1 ↦ inp[0] = a`).
The single output (the last binding `u`) is stored to `out[0]`. -/

/-- Input-load map: slot `0` is input `b` (`inp[1]`, offset 8); slot `1` is input
    `a` (`inp[0]`, offset 0). Slots `≥ 2` are absent. -/
def fheMontMulInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 8)        -- slot 0 = input b = inp[1]
  else if s = 1 then some ("RSI", 0)   -- slot 1 = input a = inp[0]
  else none

/-- Output-store map: the single result word `u` is stored to `out[0]`. -/
def fheMontMulOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 5. The owned `Lprog` and AT&T emission (no jasminc)

The single-output REDC is lowered through the thirDialect spine
(`lowerThir fheMontMulThir`) and exported to a physical, two-address SysV
`Lprog`, then the MULX-fusion post-pass `FuseMulHi.fuseMulHiLprog` coalesces each paired low `MUL` +
`MULXHI` into a real two-output `mulx`, and the result is rendered to AT&T. No
shift-immediate legalisation pass is needed: the REDC has no `thShrImm`/`thRor`
(the carry-chain `ADCX` replaces the `>> 32`-shift reduction used by the 32-bit
lazy REDC); its ops are `MUL` (`thBin .mul`), `MULXHI` (`thMulHi`),
`ADCX`/`ADCXHI` (`thAddCarryLo`/`thAddCarryHi`) and `regConst`. After the
fusion the high words `hi`/`mqHi` ARE materialised (two `mulx` lines); the
remaining un-closed seam is the ADX carry-chain rendering. -/

/-- The FHE Montgomery REDC lowered through the thirDialect spine and exported to
    a physical, two-address SysV `Lprog`. The `fname` `"fhe_montmul"` becomes the
    emitted asm label (matching the C extern). -/
def fheMontMulLprog (_ : Unit) : Lprog :=
  fuseMulHiLprog
    (Com.toLprogPhysAbi (lowerThir (fheMontMulThir ())) "fhe_montmul"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (constants are in-body regConst)
      fheMontMulInLoadMap                   -- inLoadMap
      fheMontMulOutStoreMap                 -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64])                             -- abiTyin (a, b)

/-- The rendered owned-backend AT&T `.s` for `fhe_montmul` (no jasminc). -/
def fheMontMulAsm (_ : Unit) : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (fheMontMulLprog ())

/-! ## 6. Substring helper -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

-- Rendered-asm correctness is the external C KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 7. Emit driver -/

/-- Write the owned-backend `.s` for the 60-bit FHE Montgomery multiply
    (`fhe_montmul`) into the `bench/fhe_ntt_compare/gen` harness directory (no
    jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/fhe_ntt_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/fhe_montmul.s") (fheMontMulAsm ())
  IO.println "WROTE bench/fhe_ntt_compare/gen/fhe_montmul.s"
  IO.println "  (60-bit FHE-NTT Montgomery REDC fheMontMulThir through Com[thir] -> lowerThir ->"
  IO.println "   toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc;"
  IO.println "   q = 1152921504606830593, qinv = 1080859512253956095, R = 2^64)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit
