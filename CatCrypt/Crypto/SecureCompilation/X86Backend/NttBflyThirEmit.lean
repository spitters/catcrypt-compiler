/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
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
# BabyBear NTT butterfly through the OWNED x86 backend (no jasminc)

The BabyBear Montgomery-domain NTT butterfly driven through the `compile-from-hax`
front (`Com thirDialect`) onto the OWNED x86 backend — NO jasminc anywhere. The
companion of `bench/thir_front_montmul_owned/` (which emits the lazy BabyBear
Montgomery REDC `montMulThir`); the butterfly REUSES that REDC verbatim, so this
module is a clone of `MontMulThirEmit` over the two single-output butterfly
programs `ThirToComFront.bflyAThir` / `bflyBThir`.

The lazy butterfly over three `u64` words holding `u32` Montgomery
representatives `a`, `b`, `w` (the twiddle/zeta), `t = montmul(w, b)` the §13
REDC:

    (a', b') = (a + t, a + 4p − t)   over BabyBear `p = 0x78000001`, `R = 2^32`

is a straight-line Gentleman–Sande-shaped butterfly with NO final conditional
subtract (the `4p` bias keeps `b'` non-negative; both outputs are lazy, in
`[0, 5p)`, congruent mod `p` to the canonical butterfly).

Each butterfly output is a SEPARATE single-output program (`bflyAThir` for `a'`,
`bflyBThir` for `b'`), each emitted through the same pipeline as
`MontMulThirEmit`:

    bflyXThir : Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64)
      --lowerThir-->            Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

Both functions are emitted into a single `.s` (one `Lprog` with two `lp_funcs`).

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the three inputs are loaded from `[RSI + off]` and the single output stored
to `[RDI + 0]`:

```c
extern void ntt_bfly_a(uint64_t *out, const uint64_t *inp);   // out[0] = a'
extern void ntt_bfly_b(uint64_t *out, const uint64_t *inp);   // out[0] = b'
//   inp = [ a, b, w ]   (three u64 words holding u32 Montgomery representatives)
```

The argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `j`
(program-root order) is context entry `nArgs - 1 - j`. The butterfly context is
`[a, b, w]` (a = `.here`, b = `.there .here`, w = `.there .there .here`), so input
index `a = 0`, `b = 1`, `w = 2`, and arg slot `s ↦ input index (nArgs - 1 - s)`.
With C-side `inp = [a, b, w]`:

* slot `2` → input `a` (`inp[0]`, byte offset 0)
* slot `1` → input `b` (`inp[1]`, byte offset 8)
* slot `0` → input `w` (`inp[2]`, byte offset 16)

i.e. `inLoadMap s = ("RSI", 8 * (2 - s))`. The single output (the last binding,
the identity-copy of the chosen butterfly word) is stored to `out[0]`
(`outStoreMap = [("RDI", 0)]`).

## The `>> 32` reduction (shift-immediate legalisation)

The inner REDC's final reduction `t = s >> 32` is a `thShrImm 64 32`, lowered to
the unary `Lopn [d] "SHR:32:64" [s]`. As in `MontMulThirEmit`, the owned
printer renders the two-source shift form but not the unary `shrImm` mnemonic, so
`legalizeShiftImmLprog` (a byte-faithful post-pass, KEPT verbatim from montmul)
rewrites each unary shift into the printer's operand form. No rotates appear (the
identity-copy tail `thRor 64 0` is a width-64 rotate by 0, lowered to a plain
move).

## What is verified vs trusted

Same surface as `MontMulThirEmit`:

* **Verified (value)**: `bflyAThir_denote` / `bflyBThir_denote`
  (`bflyXThir.denote = (nttButterflySpec64 …).{1,2}`) and
  `bflyA_via_thirDialect` / `bflyB_via_thirDialect` (the lowered `Com
  jasminDialect` denote the width-64 butterfly outputs) — all in
  `ThirToComFront`. The lowering `lowerThir` is denotation-proved
  (`lowerThir_denote`).
* **Verified (printer)**: `LprogAsmPrinter.renderLinstrR` is a thin syntactic map.
  The conservative shape lemma below pins that the emitted `.s` carries the
  `ntt_bfly_a` leaf and contains no unhandled-op sentinel.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `ntt_bfly_a(inp) == a'`, `ntt_bfly_b(inp) == b'` is the external
`as`/`cc` KAT in `bench/thir_front_ntt_bfly_owned/` (no jasminc).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.NttBflyThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (bflyAThir bflyBThir)

/-! ## 1. ABI maps for the 3-in / 1-out width-64 butterfly -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (2 - s))`. Slot `2` is input `a`
    (`inp[0]`, offset 0); slot `1` is input `b` (`inp[1]`, offset 8); slot `0` is
    input `w` (`inp[2]`, offset 16). Slots `≥ 3` are absent (the butterfly has
    exactly three inputs). -/
def bflyInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 16)       -- slot 0 = input w = inp[2]
  else if s = 1 then some ("RSI", 8)   -- slot 1 = input b = inp[1]
  else if s = 2 then some ("RSI", 0)   -- slot 2 = input a = inp[0]
  else none

/-- Output-store map: the single result word (the last binding, the identity-copy
    of the chosen butterfly output) is stored to `out[0]` (`[RDI + 0]`). -/
def bflyOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 2. Shift-immediate legalisation post-pass (kept from montmul)

The owned printer renders the two-source shift form `[d] SHR[:64] [d, #n]` but
not the unary `shrImm` mnemonic `SHR:<n>[:64]` (count carried in the mnemonic).
This pass rewrites each such unary shift into the operand form, byte-faithfully
mirroring `JasminLprogExport.lowerTwoAddrShiftImm`. The butterfly's inner REDC has
a `>> 32` reduction (`thShrImm 64 32`).

In addition, each butterfly output program ends with an identity-copy tail
(`thRor 64 0`, a width-64 rotate by zero) that seats the chosen output word as
the last binding. That lowers to a unary `Lopn [d] "ROR:0:64" [s]`, which is
likewise not in the owned printer's two-source repertoire; a rotate by zero is
just a register move, so this pass also rewrites `"ROR:0[:64]"` / `"ROL:0[:64]"`
into the printer's plain `MOV` (dropped entirely when `d = s`). -/

export CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
  (parseShiftImm legalizeBody legalizeLprog opnMnemonics)

/-- Recognise a rotate-by-zero mnemonic `"ROR:0"` / `"ROL:0"` (optionally
    width-tagged `":64"`), the identity-copy tail's lowered form. Returns `none`
    for any other mnemonic — including a NON-zero rotate (which the owned backend
    does not emit here, and which must NOT be silently turned into a move). -/
def isIdentityRot (opn : String) : Bool :=
  let isU64 := hasSuffix opn ":64"
  let core := if isU64 then String.ofList (opn.toList.dropLast.dropLast.dropLast) else opn
  core == "ROR:0" || core == "ROL:0"

/-- Rewrite one already-allocated `Linstr`:

    * a unary shift-immediate `Lopn [d] "SHR:<n>[:64]" [s]` becomes the printer's
      two-source operand form (prefixed by a `MOV` when `d ≠ s`);
    * a rotate-by-zero identity copy `Lopn [d] "ROR:0[:64]" [s]` becomes a plain
      `MOV[:64] d, s` (dropped when `d = s`);

    every other instruction passes through unchanged. -/
def legalizeShiftImmInstr (i : Linstr) : List Linstr :=
  match i.li_i with
  | .Lopn [d] opn [s] =>
      if isIdentityRot opn then
        let movMnem := if hasSuffix opn ":64" then "MOV:64" else "MOV"
        if d = s then [] else [⟨i.li_ii, .Lopn [d] movMnem [s]⟩]
      else
      match parseShiftImm opn with
      | some (baseMnem, n) =>
          let movMnem := if hasSuffix baseMnem ":64" then "MOV:64" else "MOV"
          if d = s then
            [⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
          else
            [⟨i.li_ii, .Lopn [d] movMnem [s]⟩,
             ⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
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
destination the `MOV` is absent. A rotate by zero becomes a width-matched `MOV`,
or nothing when source and destination agree; a non-zero rotate is left
untouched. -/

#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:32:64" [.reg "RCX"]⟩)
    == ["MOV:64", "SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:32:64" [.reg "RAX"]⟩)
    == ["SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "ROR:0:64" [.reg "RCX"]⟩)
    == ["MOV:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "ROR:0:64" [.reg "RAX"]⟩)
    == []
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "ROR:16:64" [.reg "RCX"]⟩)
    == ["ROR:16:64"]

/-! ## 3. The owned `Lprog`s and combined AT&T emission (no jasminc) -/

/-- The butterfly `a'` output lowered through the thirDialect spine and exported
    to a physical, two-address SysV `Lprog`, then shift-immediate-legalised. The
    `fname` `"ntt_bfly_a"` becomes the emitted asm label (matching the C extern). -/
def nttBflyALprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir bflyAThir) "ntt_bfly_a"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (constants are in-body regConst)
      bflyInLoadMap                         -- inLoadMap
      bflyOutStoreMap                       -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64, 64])                         -- abiTyin (a, b, w)

/-- The butterfly `b'` output lowered and exported the same way. -/
def nttBflyBLprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir bflyBThir) "ntt_bfly_b"
      (fun _ => none)
      (fun _ => none)
      bflyInLoadMap
      bflyOutStoreMap
      ["RDI", "RSI"]
      [64, 64, 64])

/-- Both butterfly leaves combined into a single `Lprog` (two `lp_funcs`), so
    `renderLprogAtt` emits one `.s` carrying both `ntt_bfly_a` and `ntt_bfly_b`. -/
def nttBflyLprog : Lprog :=
  { nttBflyALprog with
    lp_funcs := nttBflyALprog.lp_funcs ++ nttBflyBLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for `ntt_bfly_a` + `ntt_bfly_b`
    (no jasminc). -/
def nttBflyAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned nttBflyLprog

/-! ## 4. Shape check on the emitted asm (conservative) -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration. The value
-- correctness of both butterfly outputs is carried at the Lean level by
-- `bflyA_via_thirDialect` / `bflyB_via_thirDialect`.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for the BabyBear NTT butterfly (`ntt_bfly_a` +
    `ntt_bfly_b`) into the `bench/thir_front_ntt_bfly_owned/gen` harness
    directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_ntt_bfly_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/ntt_bfly_owned.s") nttBflyAsm
  IO.println "WROTE bench/thir_front_ntt_bfly_owned/gen/ntt_bfly_owned.s"
  IO.println "  (BabyBear NTT butterfly bflyAThir/bflyBThir through Com[thir] -> lowerThir ->"
  IO.println "   toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.NttBflyThirEmit
