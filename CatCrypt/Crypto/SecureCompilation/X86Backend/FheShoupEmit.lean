/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.FheShoupMulLaw
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-!
# Single-word 60-bit FHE **Shoup** modmul through the OWNED x86 backend (no jasminc)

A single-word **Shoup** (Barrett-with-precomputed-quotient) modular multiply at
the 60-bit FHE-NTT prime `q = 1152921504606830593`, radix `R = 2^64`, driven
through the `compile-from-hax` front (`Com thirDialect`) onto the OWNED x86
backend — NO jasminc anywhere. The Shoup companion of the Montgomery REDC
`fheMontMulThir` (`FheMontMulEmit.lean`).

## Why Shoup avoids the Montgomery ADX carry-chain gap

The Montgomery owned-emit (`FheMontMulEmit`) hit an ADX carry-chain seam at
the 128-bit reduce add (`u = hi + mqHi + cout`, the `ADCX`/`ADCXHI` tail the
shared printer does not yet render faithfully). The **Shoup** kernel avoids that
add entirely. With a fixed twiddle `b`, the precomputed Shoup constant is
`b' = ⌊b·R/q⌋` (`FheShoupMulLaw.fheShoupConst b`, supplied by the caller — in an
NTT it is a baked twiddle constant; for the KAT the harness computes it). The
emitted sequence is, on inputs `(a, b, b')`:

```
  qhat = mulhi(a, b')      -- high word of a·b' = q̂ = ⌊a·b'/R⌋  (Shoup quotient)
  lo1  = a * b             -- low 64 of a·b
  cq   = q                 -- materialised constant
  lo2  = qhat * q          -- low 64 of q̂·q
  t    = lo1 − lo2         -- a·b − q̂·q   (the LAZY value, in [0, 2q))
```

The crucial point: the **true** value `a·b − q̂·q` lies in `[0, 2q) ⊂ [0, 2^64)`
(`FheShoupMulLaw.shoup_q_mul_q_le` / `shoup_lt`), so the high words of `a·b` and
`q̂·q` cancel and the difference is a **single 64-bit subtraction** — there is NO
128-bit add, NO ADCX/ADCXHI carry chain, and NO `thAddCarry*` op anywhere in the
kernel. The final canonicalisation `if t ≥ q then t − q else t`
(`FheShoupMulLaw.shoupMul`) is the LAZY-LEAF host-side step (the caller's csub),
exactly like the Montgomery emit leaves its `if u ≥ q then u − q` to the host —
no `thSelect`/`CMOV` in the emitted kernel.

This is also the faster NTT butterfly kernel (one precomputed quotient multiply
instead of the REDC's `qinv` multiply + reduce).

## The standalone `mulhi` and how `fuseMulHiLprog` is reused (no scaffold edit)

`fuseMulHiLprog` (from `FuseMulHi`) fuses a low `MUL` immediately
followed by a `MULXHI` that shares the low op's second source `s2` into the
printer's two-output `mulx`. In the Montgomery REDC every `mulhi` was paired with
a low `mul` over the same operands, so fusion fired. The Shoup `qhat = mulhi a b'`
is a **standalone** high word — `a·b'` has no low word used by the kernel.

Rather than extend the shared `fuseMulHiLprog` to special-case a paired-less
`MULXHI`, this module feeds the existing fusion: it emits a **discarded** low
`loQ = a · b'` binding (the `thBin .mul` over the SAME sources `a`, `b'`)
immediately before `qhat = mulhi(a, b')`. After physical/two-address lowering
this is exactly the `MUL`+`MULXHI` pair `fuseMulHiAux` keys on (shared second
source `b'`), so the unmodified pass coalesces them into one `mulx`, and the low
word lands in `loQ`'s slot where it is never read (discarded — the `t` binding
reads `lo1 = a·b` and `lo2 = qhat·q`, not `loQ`). This keeps
`FuseMulHi.fuseMulHiLprog` byte-for-byte untouched (the cleaner of the
two options the task allows).

## What is verified vs trusted (scope)

* **Verified (value, in Lean)**: `fheShoupThir_denote` — `fheShoupThir.denote` on
  `[a, b, b']` is the width-64 lazy Shoup reference `fheShoupSpec64` (true by
  *definition*: `fheShoupSpec64` is that denotation, mirroring
  `FheMontMulEmit.fheMontMulSpec64`). The closed-form
  `t = (a*b) − mulHiW a b' * q` is documented in §3; its `Nat`-level connection to
  `FheShoupMulLaw.shoupMul` *without* the final csub (the
  `mulHiW`/`BitVec → Nat` bridge) is the orchestrator's GMP KAT on the emitted
  `.s` — a single `rfl` over the binding tower reduces the `2^64`-heavy `mulHiW`
  body and trips the kernel recursion guard, so the value check is externalised
  (the §13 lazy-leaf discipline). `fheShoup_via_thirDialect` re-derives the same
  word through the generic, proved `lowerThir_denote`.
* **No carry chain at all**: the kernel has NO `thAddCarry*` op, so there is no
  ADX `ADCX`/`ADCXHI` tail and hence none of the Montgomery emit's carry-chain
  seam. `t` is a single `SUB`. (Flagged for the KAT: the only register risk is
  the `mulx` rdx-pin / `R8` evacuation inherited from `fuseMulHiLprog`, and the
  SUB operand order `lo1 − lo2`.)
* **Trusted (thin)**: `renderLfundef` / `as`/`cc` / the SysV leaf ABI frame.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FheShoupEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir lowerThir_denote thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiLprog)

/-! ## 1. The FHE-NTT prime constant (as `Nat`, matching `FheShoupMulLaw.fheQ`) -/

/-- The 60-bit FHE prime `q = 2^60 − 2^14 + 1` (matches `FheShoupMulLaw.fheQ`). -/
def fheQ : Nat := 1152921504606830593

/-! ## 2. The lazy Shoup modmul as a `Com thirDialect`

Single-output: the last binding (`t`) IS the result. Context starts
`[a, b, bprime]` (`a = .here`, `b = .there .here`, `bprime = .there (.there .here)`),
where `bprime = ⌊b·R/q⌋` is the precomputed Shoup twiddle constant (caller-supplied).
Bindings, head-first:

    loQ, qhat, lo1, cq, lo2, t

where `loQ = a·bprime` is a **discarded** low word emitted ONLY to feed
`fuseMulHiLprog` (it shares its second source `bprime` with the next `qhat`
`MULXHI`, so the unmodified fusion pass coalesces the pair into one `mulx`; `loQ`
is never read). `qhat = mulhi(a, bprime) = q̂`; `lo1 = a·b`; `cq = q`;
`lo2 = qhat·q`; `t = lo1 − lo2 = a·b − q̂·q` (the lazy value in `[0, 2q)`). NO
add-with-carry, NO conditional subtract — the caller applies the final csub. -/
def fheShoupThir : Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- loQ = a * bprime  (DISCARDED low word; pairs with the next mulhi for fusion)
  --   ctx: [a, b, bprime]; a = dB0, bprime = dB2
  .var (.mk (.thBin .mul 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
  -- qhat = mulhi(a, bprime) = q̂   ctx: [loQ, a, b, bprime]; a = dB1, bprime = dB3
  (.var (.mk (.thMulHi 64) rfl (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
  -- lo1 = a * b                    ctx: [qhat, loQ, a, b, bprime]; a = dB2, b = dB3
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))
  -- cq = q                         ctx: [lo1, qhat, loQ, a, b, bprime]
  (.var (.mk (.thConst 64 fheQ) rfl .nil)
  -- lo2 = qhat * cq                ctx: [cq, lo1, qhat, loQ, a, b, bprime]; qhat = dB2, cq = dB0
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
  -- t = lo1 − lo2                  ctx: [lo2, cq, lo1, qhat, loQ, a, b, bprime]; lo1 = dB2, lo2 = dB0
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
  (.ret .here))))))

/-! ## 3. The width-64 lazy Shoup reference

`fheShoupSpec64 a b bprime` is *defined* as the width-64 denotation of
`fheShoupThir` on `[a, b, bprime]`, so the denotation lemma `fheShoupThir_denote`
is a syntactic identity (mirroring `FheMontMulEmit.fheMontMulSpec64`). The
closed-form value the program computes is

```
  t = (a * b) − mulHiW a bprime * q          -- a·b − q̂·q, the lazy value in [0, 2q)
```

with `q̂ = mulHiW a bprime = ⌊a·bprime/R⌋` and `bprime = ⌊b·R/q⌋`. Over `Nat`
this is `FheShoupMulLaw.shoupMul a b` WITHOUT the final conditional subtract
(`shoupMul = if t ≥ q then t − q else t`; the lazy value is the `t` itself). The
`BitVec 64 ↔ Nat` connection (the `mulHiW`/`%2^64` bridge) is the orchestrator's
GMP value KAT on the emitted `.s`: a single in-kernel `rfl` over the binding
tower would reduce the `2^64`-heavy `mulHiW` body and trip the kernel recursion
guard, so the value check is externalised (KAT), exactly the §13 lazy-leaf
discipline. -/

/-- The width-64 lazy Shoup modmul: by definition the denotation of the
    emitted-through-the-spine program `fheShoupThir` on the three input words
    `(a, b, bprime)` (the closed-form is `(a*b) − mulHiW a bprime * q`; its value
    is checked by the orchestrator's GMP KAT on the emitted `.s`). -/
def fheShoupSpec64 (a b bprime : BitVec 64) : BitVec 64 :=
  fheShoupThir.denote (.cons a (.cons b (.cons bprime .nil)))

/-- The THIR-dialect lazy FHE Shoup modmul denotes `fheShoupSpec64` — true by
    definition (`fheShoupSpec64` is that denotation; mirrors
    `FheMontMulEmit.fheMontMulThir_denote`). -/
theorem fheShoupThir_denote (a b bprime : BitVec 64) :
    fheShoupThir.denote (.cons a (.cons b (.cons bprime .nil))) = fheShoupSpec64 a b bprime := rfl

/-- **FHE Shoup modmul re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` denotes the same `BitVec 64` as the width-64
    Shoup reference, obtained through `Com[thir] →lowerThir→ Com[jasmin]` (the
    generic, proved `lowerThir_denote`) rather than a bespoke lowering. -/
theorem fheShoup_via_thirDialect (a b bprime : BitVec 64) :
    (lowerThir fheShoupThir).denote (.cons a (.cons b (.cons bprime .nil)))
      = fheShoupSpec64 a b bprime :=
  (lowerThir_denote fheShoupThir (.cons a (.cons b (.cons bprime .nil)))).trans
    (fheShoupThir_denote a b bprime)

/-! ## 4. ABI maps for the 3-in / 1-out width-64 kernel

`comToLfundefPhysAbi` emits the 2-pointer SysV signature
(`extern void fhe_shoup_modmul(uint64_t* out, const uint64_t* inp)`, `RDI` = out,
`RSI` = inp). Argument-slot numbering (`JasminLprogExport.comToLfundef`):
argument slot `s` (program-root order) is context entry `nArgs - 1 - s`. The
Shoup context is `[a, b, bprime]` (`a = 0`, `b = 1`, `bprime = 2`), so arg slot
`s ↦ input index (2 - s)`. With C-side `inp = [a, b, bprime]`:

* slot `2` → input `a`      (`inp[0]`, byte offset 0)
* slot `1` → input `b`      (`inp[1]`, byte offset 8)
* slot `0` → input `bprime` (`inp[2]`, byte offset 16)

i.e. `inLoadMap s = ("RSI", 8 * (2 - s))`. The single output (the last binding
`t`) is stored to `out[0]`. -/

/-- Input-load map: slot `0` → `bprime` (`inp[2]`, offset 16); slot `1` → `b`
    (`inp[1]`, offset 8); slot `2` → `a` (`inp[0]`, offset 0). Slots `≥ 3` absent. -/
def fheShoupInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 16)       -- slot 0 = bprime = inp[2]
  else if s = 1 then some ("RSI", 8)   -- slot 1 = b = inp[1]
  else if s = 2 then some ("RSI", 0)   -- slot 2 = a = inp[0]
  else none

/-- Output-store map: the single result word `t` is stored to `out[0]`. -/
def fheShoupOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 5. The owned `Lprog` and AT&T emission (no jasminc)

The single-output Shoup modmul is lowered through the thirDialect spine
(`lowerThir fheShoupThir`), exported to a physical, two-address SysV `Lprog`
(3-pointer-load `inp`, 1-store `out`), then the §"standalone mulhi" trick lets the
**unmodified** `FuseMulHi.fuseMulHiLprog` coalesce the discarded low
`loQ = a·bprime` + `qhat = mulhi(a,bprime)` pair into the printer's two-output
`mulx`, and the result is rendered to AT&T. No shift-immediate legalisation pass
is needed (no `thShrImm`/`thRor`), and — crucially — there is no carry-chain to
render: the kernel has no `thAddCarry*` op, so the difference `t = lo1 − lo2` is
one plain `SUB`. -/

/-- The FHE Shoup modmul lowered through the thirDialect spine and exported to a
    physical, two-address SysV `Lprog`. The `fname` `"fhe_shoup_modmul"` becomes
    the emitted asm label (matching the C extern). -/
def fheShoupLprog : Lprog :=
  fuseMulHiLprog
    (Com.toLprogPhysAbi (lowerThir fheShoupThir) "fhe_shoup_modmul"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (constants are in-body regConst)
      fheShoupInLoadMap                     -- inLoadMap (3 inputs)
      fheShoupOutStoreMap                   -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64, 64])                         -- abiTyin (a, b, bprime)

/-- The rendered owned-backend AT&T `.s` for `fhe_shoup_modmul` (no jasminc). -/
def fheShoupAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned fheShoupLprog

/-! ## 6. Rendered asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 7. Emit driver -/

/-- Write the owned-backend `.s` for the 60-bit FHE Shoup multiply
    (`fhe_shoup_modmul`) into the `bench/fhe_ntt_compare/gen` harness directory
    (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/fhe_ntt_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/fhe_shoup_modmul.s") fheShoupAsm
  IO.println "WROTE bench/fhe_ntt_compare/gen/fhe_shoup_modmul.s"
  IO.println "  (60-bit FHE-NTT Shoup modmul fheShoupThir through Com[thir] -> lowerThir ->"
  IO.println "   toLprogPhysAbi -> fuseMulHiLprog -> renderLprogAtt onto the OWNED x86 backend,"
  IO.println "   NO jasminc; inputs (a, b, bprime=floor(b*R/q)), out[0] = a*b - qhat*q in [0,2q);"
  IO.println "   q = 1152921504606830593, R = 2^64; final csub is host-side)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.FheShoupEmit
