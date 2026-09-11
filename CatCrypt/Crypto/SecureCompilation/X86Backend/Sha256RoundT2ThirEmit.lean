/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256BigSigmaThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256BigSigmaThirEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# SHA-256 round value `T₂` (width 32) through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §6.2.2 SHA-256 round value `T₂` driven through the
`compile-from-hax` front (`Com thirDialect`) onto the OWNED x86 backend — NO
jasminc anywhere. This completes the SHA-256 round-component set: it is the
**3-input** width-32 sibling of `Sha256RoundT1ThirEmit`, inlining the
big-Sigma `Σ₀(a)`, the boolean `Maj(a,b,c)`, and one wrapping `add`:

    T₂ = Σ₀(a) + Maj(a,b,c)     (mod 2³², wrapping)

where (FIPS 180-4 §4.1.2 / §4.1.3, width 32)

    Σ₀(a)       = ROTR²(a) ⊕ ROTR¹³(a) ⊕ ROTR²²(a)
    Maj(a,b,c)  = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)

This leaf exercises in one width-32 multi-input program: the rotate
legalisation (three `ROTR` in `Σ₀`), the boolean `and`/`xor` surface (`Maj`),
and a single `thBin .add 32` wrapping combine.

The pipeline mirrors `Sha256RoundT1ThirEmit` / `Sha256BigSigmaThirEmit`:

    sha256T2Thir : Com thirDialect [.reg 32, .reg 32, .reg 32] (.reg 32)
      --lowerThir-->            Com jasminDialect [...] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the three inputs are loaded from `[RSI + off]` and the single output
stored to `out[0]`:

```c
extern void sha256_t2(uint32_t *out, const uint32_t *inp);
//   inp = [a, b, c]   (8-byte-strided slots, low 32 bits used)
//   out[0] receives T2 = Sigma0(a) + Maj(a,b,c)
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `sha256T2Thir`'s context
is `[a, b, c]` (a = `.here`, b = `.there .here`, c = `.there² .here`), so input
index `a = 0, b = 1, c = 2`, and arg slot `s ↦ input index (3 - 1 - s) = 2 - s`.
The slot stride is **8 bytes** (`8 * (2 - s)`), modelled on the round-`e` /
`T₁` u32 ABI precedent (C-side `inp` low 32 bits used). So:

* slot `2` → input `a` (`inp[0]`, byte offset 0)
* slot `1` → input `b` (`inp[1]`, byte offset 8)
* slot `0` → input `c` (`inp[2]`, byte offset 16)

i.e. `inLoadMap s = ("RSI", 8 * (2 - s))`. The single output (the last binding,
`T₂`) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The three rotates (immediate legalisation)

`Σ₀`'s `ROTR²`/`ROTR¹³`/`ROTR²²` lower (via `thRor`) to rotate-immediate `Lopn`
forms; `legalizeShiftImmLprog` (shared from `Sha256Sigma1ThirEmit`) expands
each into the shift-or idiom over the reserved scratch `R15`. The boolean
`and`/`xor` and the single `thBin .add 32` lower to printer-recognised
two-source ALU forms directly. So the emitted `.s` carries no unhandled-op
sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha256T2Thir_denote` (the leaf denotes `T₂` = `t2Spec`)
  and `t2_via_thirDialect` (the lowered `Com jasminDialect` denotes the same) —
  both by `rfl`.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha256_t2(...) == T₂` is the external `as`/`cc` KAT in
`bench/thir_front_sha256_t2_owned/` (no jasminc).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256RoundT2ThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (bigSigma0Spec majSpec t2Spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
  (legalizeShiftImmLprog)

/-! ## 0. The FIPS round-value reference

The bundled `t2Spec a b c = Σ₀(a) + Maj(a,b,c)` (wrapping u32). We provide
`sha256T2Spec` as a transparent alias so the leaf's denotation statement names
the round value directly. -/

/-- FIPS 180-4 §6.2.2 round value `T₂ = Σ₀(a) + Maj(a,b,c)` (wrapping u32).
    Defeq to the bundled `t2Spec`. -/
def sha256T2Spec (a b c : BitVec 32) : BitVec 32 :=
  t2Spec a b c

/-! ## 1. The SHA-256 `T₂` program as a `Com thirDialect` leaf

Built directly at the THIR-dialect level (`thRor`/`thBin`), inlining `Σ₀(a)`,
`Maj(a,b,c)` and the wrapping add. Inputs (de-Bruijn, program-root order):
`[a, b, c]` — `a = .here`, `b = .there .here`, `c = .there² .here`.

SSA bindings (each `.var` prepends a fresh head binding; the operand of binding
`bk` is read in the context `b(k-1),…,b0,a,b,c`, so `bj` is at depth `k-1-j` and
input `a/b/c` is at depth `k+0`/`k+1`/`k+2`):

    -- Σ₀(a)
    r2  = ror 2 a            r13 = ror 13 a           r22 = ror 22 a
    ex  = r2 ^ r13           S0  = ex ^ r22           (= Σ₀(a))
    -- Maj(a,b,c)
    ab  = a & b              ac  = a & c              bc  = b & c
    m1  = ab ^ ac            Maj = m1 ^ bc            (= Maj(a,b,c))
    -- wrapping combine
    t2  = S0 + Maj
    ret t2 -/
def sha256T2Thir :
    Com thirDialect [.reg 32, .reg 32, .reg 32] (.reg 32) :=
  -- b0: r2 = ror 2 a   (a depth 0)
  .var (.mk (.thRor 32 2) rfl (.cons .here .nil))
  -- b1: r13 = ror 13 a   (a depth 1)
  (.var (.mk (.thRor 32 13) rfl (.cons (.there .here) .nil))
  -- b2: r22 = ror 22 a   (a depth 2)
  (.var (.mk (.thRor 32 22) rfl (.cons (.there (.there .here)) .nil))
  -- b3: ex = r2 ^ r13   (r2 depth 2, r13 depth 1)
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b4: S0 = ex ^ r22   (ex depth 0, r22 depth 1)   (= Σ₀(a))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b5: ab = a & b   (a depth 5, b depth 6)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- b6: ac = a & c   (a depth 6, c depth 8)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there
          (.there .here)))))))) .nil)))
  -- b7: bc = b & c   (b depth 8, c depth 9)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there
          (.there .here))))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there
          (.there (.there .here))))))))) .nil)))
  -- b8: m1 = ab ^ ac   (ab depth 2, ac depth 1)
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b9: Maj = m1 ^ bc   (m1 depth 0, bc depth 1)   (= Maj(a,b,c))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b10: t2 = S0 + Maj   (S0 depth 5, Maj depth 0)
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  (.ret .here)))))))))))

/-- The THIR-dialect `T₂` leaf denotes the FIPS `T₂` round value on any input
    valuation `[a, b, c]`. A direct check of the `thirDialect` semantics against
    `sha256T2Spec` (= `t2Spec`). -/
theorem sha256T2Thir_denote (a b c : BitVec 32) :
    sha256T2Thir.denote (.cons a (.cons b (.cons c .nil)))
      = sha256T2Spec a b c := by
  rfl

/-- **Round value `T₂` re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` for `T₂` denotes the same `BitVec 32` as the
    FIPS reference, obtained through `Com[thir] →lowerThir→ Com[jasmin]`.
    Combines `lowerThir_denote` (the generic, proved dialect lowering) with
    `sha256T2Thir_denote`. -/
theorem t2_via_thirDialect (a b c : BitVec 32) :
    (lowerThir sha256T2Thir).denote (.cons a (.cons b (.cons c .nil)))
      = sha256T2Spec a b c := by
  rw [lowerThir_denote sha256T2Thir (.cons a (.cons b (.cons c .nil))),
    sha256T2Thir_denote]

/-! ## 2. ABI maps for the 3-in / 1-out width-32 `T₂` leaf -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (2 - s))`, mirroring the
    round-`e` / `T₁` u32 ABI precedent (8-byte slot stride, low 32 bits used).
    Slot `2` is input `a` (`inp[0]`, offset 0); slot `1` is input `b` (`inp[1]`,
    offset 8); slot `0` is input `c` (`inp[2]`, offset 16). Slots `≥ 3` are
    absent (3 inputs). -/
def t2InLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 16)       -- slot 0 = input c = inp[2]
  else if s = 1 then some ("RSI", 8)   -- slot 1 = input b = inp[1]
  else if s = 2 then some ("RSI", 0)   -- slot 2 = input a = inp[0]
  else none

/-- Output-store map: the single result word (the last binding, `T₂`) is stored
    to `out[0]` (`[RDI + 0]`). -/
def t2OutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The `T₂` leaf lowered through the thirDialect spine and exported to a
    physical, two-address SysV `Lprog`, then shift/rotate-immediate-legalised so
    the owned printer renders the three rotates. `fname` `"sha256_t2"` becomes
    the emitted asm label (matching the C extern). -/
def t2Lprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha256T2Thir) "sha256_t2"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      t2InLoadMap                           -- inLoadMap
      t2OutStoreMap                         -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32, 32, 32])                         -- abiTyin (3 u32 inputs)

/-- The rendered owned-backend AT&T `.s` for `sha256_t2` (no jasminc). -/
def t2Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned t2Lprog

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `sha256_t2` into the
    `bench/thir_front_sha256_t2_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha256_t2_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha256_t2_owned.s") t2Asm
  IO.println "WROTE bench/thir_front_sha256_t2_owned/gen/sha256_t2_owned.s"
  IO.println "  (SHA-256 round value sha256T2Thir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

/-! ## 6. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256RoundT2ThirEmit
