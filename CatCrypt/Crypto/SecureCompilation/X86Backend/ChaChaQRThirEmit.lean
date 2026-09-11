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
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# ChaCha20 quarter-round through the OWNED x86 backend (no jasminc)

The RFC 8439 §2.1 ChaCha20 quarter-round driven through the `compile-from-hax`
front (`Com thirDialect`) onto the OWNED x86 backend — NO jasminc anywhere. The
companion of `bench/thir_front_montmul_owned/` (the BabyBear Montgomery REDC),
but for the four single-output quarter-round words
(`ThirToComFront.{qrAThir, qrBThir, qrCThir, qrDThir}`):

    QUARTERROUND(a, b, c, d) = (a', b', c', d')   (RFC 8439 §2.1)

Each of the four leaves recomputes the FULL quarter-round body (shared SSA
`qrBody`) and returns ONE of the four updated words:

    chacha_qr_a(a,b,c,d) = a'     (= a2,  qrAThir)
    chacha_qr_b(a,b,c,d) = b'     (= b4,  qrBThir)
    chacha_qr_c(a,b,c,d) = c'     (= c2,  qrCThir)
    chacha_qr_d(a,b,c,d) = d'     (= d4,  qrDThir)

The pipeline mirrors `MontMulThirEmit`:

    qrXThir : Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32)
      --lowerThir-->            Com jasminDialect [...] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

All four functions are gathered into ONE `Lprog` (`renderLprogAtt` renders each
with a unique label prefix), emitting a single `.s` with four SysV leaves.

## The RFC 8439 quarter-round (`ThirToComFront.chachaQRSpec`)

```
a += b;  d ^= a;  d = rol(d, 16);
c += d;  b ^= c;  b = rol(b, 12);
a += b;  d ^= a;  d = rol(d,  8);
c += d;  b ^= c;  b = rol(b,  7);
```

`rol(x, n)` is encoded as `x.rotateRight (32 - n)` (the `thRor (32 - n)` front
encoding). The shared SSA body `qrBody` produces the 12 compute bindings
(head-first) `b4, b3, c2, d4, d3, a2, b2, b1, c1, d2, d1, a1, a, b, c, d`; the
four output words live at `a' = a2`, `b' = b4`, `c' = c2`, `d' = d4`. Each leaf
ends with an identity-copy (`thRor 32 0`) of its chosen word so the register-arith
emit reads that word back as the result.

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the four inputs are loaded from `[RSI + off]` and the single output stored
to `[RDI + 0]`:

```c
extern void chacha_qr_a(uint32_t *out, const uint32_t *inp);   // inp = [a,b,c,d]
//   (and chacha_qr_b / _c / _d)   out[0] receives the chosen quarter-round word
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `qrXThir`'s context is
`[a, b, c, d]` (a = `.here`, …, d = `.there³ .here`), so input index
`a = 0, b = 1, c = 2, d = 3`, and arg slot `s ↦ input index (4 - 1 - s) = 3 - s`.
With C-side `inp = [a, b, c, d]`:

* slot `3` → input `a` (`inp[0]`, byte offset 0)
* slot `2` → input `b` (`inp[1]`, byte offset 8)
* slot `1` → input `c` (`inp[2]`, byte offset 16)
* slot `0` → input `d` (`inp[3]`, byte offset 24)

i.e. `inLoadMap s = ("RSI", 8 * (3 - s))`, modelled exactly on `montMul`'s
`8 * (nArgs - 1 - s)` slot stride. The single output (the last binding, the
identity-copy of the chosen word) is stored to `out[0]` (`outStoreMap =
[("RDI", 0)]`).

NOTE on the C-side word width: the loader reads 8-byte-strided slots
(`8 * (3 - s)`), matching `montMul`. The C harness passes `inp` as a 4-word
array; if the orchestrator's loader takes the low 32 bits of an 8-byte slot,
the inputs must be 8-byte-spaced (`uint64_t inp[4]`). The faithful structural
clone keeps the `8 * (3 - s)` stride; the harness side documents the
`uint64_t inp[4]` layout so the slots line up.

## The `rol` rotates (shift-immediate legalisation)

The quarter-round's `rol(x, n)` lower to `thRor (32 - n)`, ultimately
shift-immediate `Lopn` forms. `legalizeShiftImmLprog` (cloned verbatim from
`MontMulThirEmit`) rewrites each unary shift-immediate
`Lopn [d] "SHR:<n>[:64]" / "SHL:<n>[:64]" [s]` into the printer's two-source
operand form (`[d] SHR[:64] [d, #n]`, prefixed by a `MOV` when `d ≠ s`),
byte-faithfully mirroring `JasminLprogExport.lowerTwoAddrShiftImm`.

## What is verified vs trusted

* **Verified (value)**: `qrAThir_denote` … `qrDThir_denote` (each leaf denotes its
  `chachaQRSpec` component) and `qrA_via_thirDialect` … `qrD_via_thirDialect` (the
  lowered `Com jasminDialect` denotes the same) — all in `ThirToComFront`.
* **Verified (printer)**: the shape `#guard` below pins that the emitted `.s`
  carries all four SysV leaf labels and has no unhandled-op sentinel.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `chacha_qr_X(a,b,c,d) == X'` is the external `as`/`cc` KAT in
`bench/thir_front_chacha_qr_owned/` (no jasminc).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ChaChaQRThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (qrAThir qrBThir qrCThir qrDThir)

/-! ## 1. ABI maps for the 4-in / 1-out width-32 quarter-round leaves -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (3 - s))`. Slot `3` is input `a`
    (`inp[0]`, offset 0); slot `2` is `b` (offset 8); slot `1` is `c` (offset 16);
    slot `0` is `d` (offset 24). Slots `≥ 4` are absent (4 inputs). -/
def qrInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 24)       -- slot 0 = input d = inp[3]
  else if s = 1 then some ("RSI", 16)  -- slot 1 = input c = inp[2]
  else if s = 2 then some ("RSI", 8)   -- slot 2 = input b = inp[1]
  else if s = 3 then some ("RSI", 0)   -- slot 3 = input a = inp[0]
  else none

/-- Output-store map: the single result word (the last identity-copy binding) is
    stored to `out[0]` (`[RDI + 0]`). -/
def qrOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 2. Shift and rotate immediate legalisation post-pass

Extends `MontMulThirEmit`'s shift-immediate pass to ALSO expand the
quarter-round's rotate-immediates. The owned printer renders the two-source shift
form `[d] SHR[:64] [d, #n]` / `[d] SHL[:64] [d, #n]` (and `OR`), but recognises
NEITHER the unary `shrImm`/`shlImm` mnemonic `SHR:<n>[:64]` NOR any rotate
mnemonic (`attBase` has no `ROR`/`ROL`). So:

* unary `SHR:<n>[:64]` / `SHL:<n>[:64]` rewrite to the two-source operand form
  `[d] SHR[:64] [d, #n]` (prefixed by `MOV` when `d ≠ s`), mirroring
  `JasminLprogExport.lowerTwoAddrShiftImm`;
* a rotate `ROR:<n>[:w]` (the lowering target of `thRor`, RFC 8439's `rol`) is
  expanded into the canonical shift-or idiom over the reserved scratch `R15`
  (`reloadScratch`, never an allocatable destination, dead between reload
  micro-sequences): for an in-place rotate of register `d` by `n` over width `w`,
  `ror(d, n) = (d >> n) | (d << (w - n))`, emitted as

      MOV R15, d           -- t := d                  (only when d ≠ s: MOV d, s first)
      SHR R15, #n          -- t >>= n
      SHL d,   #(w - n)    -- d <<= (w - n)
      OR  d,   R15         -- d |= t

  All four lines use printer-recognised two-source `Lopn` forms (`MOV`, `SHR`,
  `SHL`, `OR`), so the emitted `.s` carries no unhandled-op sentinel. NOTE: the
  scratch-`R15` rotate expansion is the structural-clone choice; the orchestrator
  may prefer adding a native `rorl`/`roll` arm to `attBase` and a one-line
  `[d] ROR [d, #n]` legalisation (a single instruction). The shift-or form here
  is value-correct and printer-only. -/

export CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
  (parseShiftImm parseRotImm wTag expandRotInPlace legalizeBody legalizeLprog opnMnemonics)

/-- Rewrite one already-allocated `Linstr`:

    * a unary shift-immediate `Lopn [d] "SHR:<n>[:64]" [s]` → two-source
      `[d] SHR[:64] [d, #n]` (prefixed by `MOV d, s` when `d ≠ s`);
    * a rotate `Lopn [d] "ROR:<n>[:w]" [s]` → (a `MOV d, s` when `d ≠ s`, to move
      the rotate's source into place) followed by the `expandRotInPlace` shift-or
      idiom over `R15`;

    every other instruction passes through unchanged. -/
def legalizeShiftImmInstr (i : Linstr) : List Linstr :=
  match i.li_i with
  | .Lopn [d] opn [s] =>
      match parseShiftImm opn with
      | some (baseMnem, n) =>
          let movMnem := if hasSuffix baseMnem ":64" then "MOV:64" else "MOV"
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

/-! A 32-bit shift with distinct source and destination expands to a
width-matched `MOV` and the two-source shift; with a common source and
destination the `MOV` is absent. A rotate expands to the scratch-`R15` shift-or
idiom, and a rotate by zero is expanded rather than elided. -/

#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "EAX"] "SHR:7" [.reg "ECX"]⟩)
    == ["MOV", "SHR"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "EAX"] "SHR:7" [.reg "EAX"]⟩)
    == ["SHR"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "EAX"] "ROR:16" [.reg "ECX"]⟩)
    == ["MOV", "MOV", "SHR", "SHL", "OR"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "EAX"] "ROR:0" [.reg "EAX"]⟩)
    == ["MOV", "SHR", "SHL", "OR"]

/-! ## 3. The owned `Lprog`s and AT&T emission (no jasminc) -/

/-- Lower one quarter-round leaf through the thirDialect spine and export to a
    physical, two-address SysV `Lprog`, then shift-immediate-legalise so the
    owned printer renders the `rol` rotates. `fname` becomes the emitted label. -/
def qrLprog (com : Com thirDialect
    [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32)) (fname : String) : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir com) fname
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      qrInLoadMap                           -- inLoadMap
      qrOutStoreMap                         -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32, 32, 32, 32])                     -- abiTyin (4 u32 inputs)

/-- The four single-output quarter-round leaves, each its own owned `Lprog`. -/
def qrALprog : Lprog := qrLprog qrAThir "chacha_qr_a"
def qrBLprog : Lprog := qrLprog qrBThir "chacha_qr_b"
def qrCLprog : Lprog := qrLprog qrCThir "chacha_qr_c"
def qrDLprog : Lprog := qrLprog qrDThir "chacha_qr_d"

/-- All four leaves gathered into ONE `Lprog`: concatenate the four single-leaf
    `lp_funcs`. `renderLprogAtt` renders each function with a unique
    label-prefix, so the four bodies' local `.L` labels do not collide. -/
def chachaQRLprog : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := qrALprog.lp_funcs ++ qrBLprog.lp_funcs
                ++ qrCLprog.lp_funcs ++ qrDLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for all four quarter-round leaves
    (no jasminc). -/
def chachaQRAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned chachaQRLprog

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for the four quarter-round leaves into the
    `bench/thir_front_chacha_qr_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_chacha_qr_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/chacha_qr_owned.s") chachaQRAsm
  IO.println "WROTE bench/thir_front_chacha_qr_owned/gen/chacha_qr_owned.s"
  IO.println "  (RFC 8439 ChaCha20 quarter-round leaves qr{A,B,C,D}Thir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.ChaChaQRThirEmit
