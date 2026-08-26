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
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# SHA-256 round value `T₁` (width 32) through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §6.2.2 SHA-256 round value `T₁` driven through the
`compile-from-hax` front (`Com thirDialect`) onto the OWNED x86 backend — NO
jasminc anywhere. This is the widest COMPOSITE compile-from-hax leaf so far: a
**6-input** width-32 program inlining the big-Sigma `Σ₁(e)`, the boolean
`Ch(e,f,g)`, and a four-add wrapping accumulation:

    T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ     (mod 2³², wrapping, left-to-right)

where (FIPS 180-4 §4.1.2 / §4.1.3, width 32)

    Σ₁(e)     = ROTR⁶(e) ⊕ ROTR¹¹(e) ⊕ ROTR²⁵(e)
    Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)        (¬e = e ⊕ 0xffffffff)

The sum is taken **left-to-right** (matching the bundled `t1Spec`):
`((((h + Σ₁(e)) + Ch(e,f,g)) + Kₜ) + Wₜ)`. This leaf exercises in one width-32
multi-input program: the rotate legalisation (three `ROTR` in `Σ₁`), the
NOT-via-`xor`-literal idiom (`thBinLit .xor 32 0xffffffff` in `Ch`), the
boolean `and`/`xor` surface, and the four-`add` wrapping chain.

The pipeline mirrors `Sha256MsgScheduleThirEmit` / `Sha256BigSigmaThirEmit`:

    sha256T1Thir : Com thirDialect [.reg 32 × 6] (.reg 32)
      --lowerThir-->            Com jasminDialect [...] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the six inputs are loaded from `[RSI + off]` and the single output stored
to `out[0]`:

```c
extern void sha256_t1(uint32_t *out, const uint64_t *inp);
//   inp = [e, f, g, h, kt, wt]   (8-byte-strided slots, low 32 bits used)
//   out[0] receives T1 = h + Sigma1(e) + Ch(e,f,g) + kt + wt
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `sha256T1Thir`'s context
is `[e, f, g, h, kt, wt]` (e = `.here`, …, wt = `.there⁵ .here`), so input index
`e = 0, …, wt = 5`, and arg slot `s ↦ input index (6 - 1 - s) = 5 - s`. The slot
stride is **8 bytes** (`8 * (5 - s)`), modelled on the round-`e` u32 ABI
precedent (`8 * (nArgs - 1 - s)`, C-side `inp` typed `const uint64_t *`, low 32
bits used). So:

* slot `5` → input `e`  (`inp[0]`, byte offset 0)
* slot `4` → input `f`  (`inp[1]`, byte offset 8)
* slot `3` → input `g`  (`inp[2]`, byte offset 16)
* slot `2` → input `h`  (`inp[3]`, byte offset 24)
* slot `1` → input `kt` (`inp[4]`, byte offset 32)
* slot `0` → input `wt` (`inp[5]`, byte offset 40)

i.e. `inLoadMap s = ("RSI", 8 * (5 - s))`. The single output (the last binding,
`T₁`) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The three rotates + NOT-via-xor (immediate legalisation)

`Σ₁`'s `ROTR⁶`/`ROTR¹¹`/`ROTR²⁵` lower (via `thRor`) to rotate-immediate `Lopn`
forms; `legalizeShiftImmLprog` (shared from `Sha256Sigma1ThirEmit`) expands
each into the shift-or idiom over the reserved scratch `R15`. The `Ch` NOT is
the expanding `thBinLit .xor 32 0xffffffff`, lowered to an `xor`-with-literal
two-source ALU form. The boolean `and`/`xor` and the four `thBin .add 32` lower
to printer-recognised two-source ALU forms directly. So the emitted `.s` carries
no unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha256T1Thir_denote` (the leaf denotes `T₁` = `t1Spec`)
  and `t1_via_thirDialect` (the lowered `Com jasminDialect` denotes the same) —
  both by `rfl`.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha256_t1(...) == T₁` is the external `as`/`cc` KAT in
`bench/thir_front_sha256_t1_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256RoundT1ThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (bigSigma1Spec chSpec t1Spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
  (legalizeShiftImmLprog)

/-! ## 0. The FIPS round-value reference

The bundled `t1Spec e f g h kt wt = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ`
(left-to-right wrapping u32). We provide `sha256T1Spec` as a transparent alias so
the leaf's denotation statement names the round value directly. -/

/-- FIPS 180-4 §6.2.2 round value
    `T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ`, summed left-to-right (wrapping u32).
    Defeq to the bundled `t1Spec`. -/
def sha256T1Spec (e f g h kt wt : BitVec 32) : BitVec 32 :=
  t1Spec e f g h kt wt

/-! ## 1. The SHA-256 `T₁` program as a `Com thirDialect` leaf

Built directly at the THIR-dialect level (`thRor`/`thBin`/`thBinLit`), inlining
`Σ₁(e)`, `Ch(e,f,g)` and the four wrapping adds. Inputs (de-Bruijn, program-root
order): `[e, f, g, h, kt, wt]` — `e = .here`, …, `wt = .there⁵ .here`.

SSA bindings (each `.var` prepends a fresh head binding; depth of original input
`i` after `k` bindings is `k + i`):

    -- Σ₁(e)
    e6  = ror 6 e             e11 = ror 11 e            e25 = ror 25 e
    ex  = e6 ^ e11            S1  = ex ^ e25            (= Σ₁(e))
    -- Ch(e,f,g)
    ef  = e & f              ne  = e ^ 0xffffffff   (¬e)
    neg = ne & g             Ch  = ef ^ neg            (= Ch(e,f,g))
    -- wrapping accumulation, left-to-right
    a1  = h + S1             a2  = a1 + Ch
    a3  = a2 + kt            a4  = a3 + wt
    ret a4 -/
def sha256T1Thir :
    Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  -- b0: e6 = ror 6 e   (e at depth 0)
  .var (.mk (.thRor 32 6) rfl (.cons .here .nil))
  -- b1: e11 = ror 11 e   (e at depth 1)
  (.var (.mk (.thRor 32 11) rfl (.cons (.there .here) .nil))
  -- b2: e25 = ror 25 e   (e at depth 2)
  (.var (.mk (.thRor 32 25) rfl (.cons (.there (.there .here)) .nil))
  -- b3: ex = e6 ^ e11   (e6 depth 2, e11 depth 1)
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b4: S1 = ex ^ e25   (ex depth 0, e25 depth 1)   (= Σ₁(e))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b5: ef = e & f   (e at depth 5, f at depth 6)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- b6: ne = e ^ 0xffffffff   (¬e)   (e at depth 6)
  (.var (.mk (.thBinLit .xor 32 0xffffffff) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))
  -- b7: neg = ne & g   (ne depth 0, g at depth 9)
  (.var (.mk (.thBin .and 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there .here))))))))) .nil)))
  -- b8: Ch = ef ^ neg   (ef depth 2, neg depth 0)   (= Ch(e,f,g))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons .here .nil)))
  -- b9: a1 = h + S1   (h at depth 12, S1 depth 4)
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there .here))))))))))))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- b10: a2 = a1 + Ch   (a1 depth 0, Ch depth 1)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b11: a3 = a2 + kt   (a2 depth 0, kt at depth 15)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) ) .nil)))
  -- b12: a4 = a3 + wt   (a3 depth 0, wt at depth 17)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            (.there .here))))))))))))))))) .nil)))
  (.ret .here)))))))))))))

/-- The THIR-dialect `T₁` leaf denotes the FIPS `T₁` round value on any input
    valuation `[e, f, g, h, kt, wt]`. A direct check of the `thirDialect`
    semantics against `sha256T1Spec` (= `t1Spec`). -/
theorem sha256T1Thir_denote (e f g h kt wt : BitVec 32) :
    sha256T1Thir.denote
        (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil))))))
      = sha256T1Spec e f g h kt wt := by
  rfl

/-- **Round value `T₁` re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` for `T₁` denotes the same `BitVec 32` as the
    FIPS reference, obtained through `Com[thir] →lowerThir→ Com[jasmin]`. Combines
    `lowerThir_denote` (the generic, proved dialect lowering) with
    `sha256T1Thir_denote`. -/
theorem t1_via_thirDialect (e f g h kt wt : BitVec 32) :
    (lowerThir sha256T1Thir).denote
        (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil))))))
      = sha256T1Spec e f g h kt wt := by
  rw [lowerThir_denote sha256T1Thir
      (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil)))))),
    sha256T1Thir_denote]

/-! ## 2. ABI maps for the 6-in / 1-out width-32 `T₁` leaf -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (5 - s))`, mirroring the
    round-`e` u32 ABI precedent (8-byte slot stride, low 32 bits used). Slot `5`
    is input `e` (`inp[0]`, offset 0); … slot `0` is input `wt` (`inp[5]`,
    offset 40). Slots `≥ 6` are absent (6 inputs). -/
def t1InLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 40)       -- slot 0 = input wt = inp[5]
  else if s = 1 then some ("RSI", 32)  -- slot 1 = input kt = inp[4]
  else if s = 2 then some ("RSI", 24)  -- slot 2 = input h  = inp[3]
  else if s = 3 then some ("RSI", 16)  -- slot 3 = input g  = inp[2]
  else if s = 4 then some ("RSI", 8)   -- slot 4 = input f  = inp[1]
  else if s = 5 then some ("RSI", 0)   -- slot 5 = input e  = inp[0]
  else none

/-- Output-store map: the single result word (the last binding, `T₁`) is stored
    to `out[0]` (`[RDI + 0]`). -/
def t1OutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The `T₁` leaf lowered through the thirDialect spine and exported to a
    physical, two-address SysV `Lprog`, then shift/rotate-immediate-legalised so
    the owned printer renders the three rotates and the NOT-via-xor. `fname`
    `"sha256_t1"` becomes the emitted asm label (matching the C extern). -/
def t1Lprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha256T1Thir) "sha256_t1"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      t1InLoadMap                           -- inLoadMap
      t1OutStoreMap                         -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32, 32, 32, 32, 32, 32])             -- abiTyin (6 u32 inputs)

/-- The rendered owned-backend AT&T `.s` for `sha256_t1` (no jasminc). -/
def t1Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned t1Lprog

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `sha256_t1` into the
    `bench/thir_front_sha256_t1_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha256_t1_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha256_t1_owned.s") t1Asm
  IO.println "WROTE bench/thir_front_sha256_t1_owned/gen/sha256_t1_owned.s"
  IO.println "  (SHA-256 round value sha256T1Thir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

/-! ## 6. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256RoundT1ThirEmit
