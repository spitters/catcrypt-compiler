/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToCom_Sha256Round
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# SHA-256 compression-ROUND `e'` word through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §6.2 SHA-256 round-update for the working word `e'` driven
through the `compile-from-hax` front (`Com thirDialect`) onto the OWNED x86
backend — NO jasminc anywhere. The real-primitive milestone for the front: a
*whole SHA-256 round component* (not just a sub-function) on the `Com thirDialect`
AST, emitted through the owned spine.

    e' = d + Σ₁(e) + Ch(e,f,g) + K_t + W_t + h     (FIPS 180-4 §6.2.2)

(`sha256RoundEComThir`, proven `= sha256RoundESpec7` in
`ThirToCom_Sha256Round.lean`). Companion of `Sha256Sigma1ThirOwnedEmit` (the σ₁
word) and `ChaChaQRThirOwnedEmit` (the ChaCha quarter-round), but for the full
round-`e'` word — exercising the rotate legalisation (three `ROTR` in `Σ₁`), the
`thBinLit` mask expansion (`¬e` in `Ch`) and the wrapping-add chain.

The pipeline mirrors `Sha256Sigma1ThirOwnedEmit`:

    sha256RoundEComThir : Com thirDialect [.reg 32 × 7] (.reg 32)
      --lowerThir-->            Com jasminDialect [...] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the seven inputs are loaded from `[RSI + off]` and the single output stored
to `[RDI + 0]`:

```c
extern void sha256_round_e(uint32_t *out, const uint64_t *inp);
//   inp = [d, e, f, g, h, kt, wt]   (8-byte-strided slots, low 32 bits used)
//   out[0] receives e' = d + h + Sigma1(e) + Ch(e,f,g) + kt + wt
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `sha256RoundEComThir`'s
context is `[d, e, f, g, h, kt, wt]` (d = `.here`, …, wt = `.there⁶ .here`), so
input index `d = 0, …, wt = 6`, and arg slot `s ↦ input index (7 - 1 - s) =
6 - s`. With C-side `inp = [d, e, f, g, h, kt, wt]`:

* slot `6` → input `d` (`inp[0]`, byte offset 0)
* slot `5` → input `e` (`inp[1]`, byte offset 8)
* …
* slot `0` → input `wt` (`inp[6]`, byte offset 48)

i.e. `inLoadMap s = ("RSI", 8 * (6 - s))`, modelled exactly on `montMul`'s
`8 * (nArgs - 1 - s)` slot stride (and `qrInLoadMap`). The single output (the
last binding, `e'`) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The three rotates + one mask (immediate legalisation)

`Σ₁`'s `ROTR⁶`/`ROTR¹¹`/`ROTR²⁵` lower (via `thRor`) to rotate-immediate `Lopn`
forms; the `Ch` `¬e` mask lowers (via `thBinLit .xor`) to a `regConst` + `regArith`
pair (no shift). `legalizeShiftImmLprog` (cloned verbatim from
`ChaChaQRThirOwnedEmit`) rewrites each rotate `Lopn [d] "ROR:<n>[:w]" [s]` into the
canonical shift-or idiom over the reserved scratch `R15`
(`ror(d,n) = (d>>n)|(d<<(w-n))`), all four lines in printer-recognised two-source
`Lopn` forms (`MOV`/`SHR`/`SHL`/`OR`). The `thBinLit` mask and the add-chain lower
to printer-recognised forms directly. So the emitted `.s` carries no
unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha256RoundEComThir_denote` (the leaf denotes the FIPS
  `e'` word = `sha256RoundESpec7`) and `roundE_via_thirDialect` (the lowered
  `Com jasminDialect` denotes the same) — both in `ThirToCom_Sha256Round`.
* **Verified (printer)**: the shape lemma below pins that the emitted `.s`
  carries the SysV leaf label and has no unhandled-op sentinel.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha256_round_e(...) == e'` is the external `as`/`cc` KAT in
`bench/thir_front_sha256_round_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256RoundThirOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (sha256RoundEComThir)

/-! ## 1. ABI maps for the 7-in / 1-out width-32 round-`e'` leaf -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (6 - s))`. Slot `6` is input `d`
    (`inp[0]`, offset 0); … slot `0` is `wt` (`inp[6]`, offset 48). Slots `≥ 7`
    are absent (7 inputs). -/
def roundEInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 48)       -- slot 0 = input wt = inp[6]
  else if s = 1 then some ("RSI", 40)  -- slot 1 = input kt = inp[5]
  else if s = 2 then some ("RSI", 32)  -- slot 2 = input h  = inp[4]
  else if s = 3 then some ("RSI", 24)  -- slot 3 = input g  = inp[3]
  else if s = 4 then some ("RSI", 16)  -- slot 4 = input f  = inp[2]
  else if s = 5 then some ("RSI", 8)   -- slot 5 = input e  = inp[1]
  else if s = 6 then some ("RSI", 0)   -- slot 6 = input d  = inp[0]
  else none

/-- Output-store map: the single result word (the last binding, `e'`) is stored
    to `out[0]` (`[RDI + 0]`). -/
def roundEOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 2. Shift and rotate immediate legalisation post-pass

Cloned verbatim from `ChaChaQRThirOwnedEmit` (which itself extends
`MontMulThirOwnedEmit`'s shift-immediate pass with the rotate expansion). The
owned printer renders the two-source shift form `[d] SHR [d, #n]` but recognises
NEITHER the unary `SHR:<n>[:64]` mnemonic NOR any rotate mnemonic. So:

* unary `SHR:<n>[:64]` / `SHL:<n>[:64]` rewrite to the two-source operand form
  `[d] SHR [d, #n]` (prefixed by `MOV` when `d ≠ s`);
* a rotate `ROR:<n>[:w]` expands into the shift-or idiom over the reserved
  scratch `R15`: `ror(d, n) = (d >> n) | (d << (w - n))`, emitted as

      MOV R15, d ;  SHR R15, #n ;  SHL d, #(w-n) ;  OR d, R15

  All four lines use printer-recognised two-source `Lopn` forms. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (reloadScratch)

/-- Parse a unary shift-immediate mnemonic `"SHR:<n>"` / `"SHL:<n>"` (optionally
    width-tagged `":64"`) into `(baseMnem, count)`. Returns `none` for any other
    mnemonic (so every non-shift-imm `Lopn` is left untouched). -/
def parseShiftImm (opn : String) : Option (String × Nat) :=
  let isU64 := opn.endsWith ":64"
  let core := if isU64 then String.ofList (opn.toList.dropLast.dropLast.dropLast) else opn
  match core.splitOn ":" with
  | [base, cnt] =>
      if base = "SHR" || base = "SHL" then
        match cnt.toNat? with
        | some n => some ((if isU64 then base ++ ":64" else base), n)
        | none => none
      else none
  | _ => none

/-- Parse a rotate-immediate mnemonic `"ROR:<n>"` / `"ROL:<n>"` (optionally
    width-tagged `":64"`) into `(baseDir, count, width)` where `baseDir` is
    `"ROR"` or `"ROL"` and `width` is `64` for a `:64`-tagged op else `32`.
    Returns `none` for any other mnemonic. -/
def parseRotImm (opn : String) : Option (String × Nat × Nat) :=
  let isU64 := opn.endsWith ":64"
  let core := if isU64 then String.ofList (opn.toList.dropLast.dropLast.dropLast) else opn
  match core.splitOn ":" with
  | [base, cnt] =>
      if base = "ROR" || base = "ROL" then
        match cnt.toNat? with
        | some n => some (base, n, if isU64 then 64 else 32)
        | none => none
      else none
  | _ => none

/-- Width-tag suffix (`":64"` for 64-bit, empty for 32-bit). -/
def wTag (w : Nat) : String := if w = 64 then ":64" else ""

/-- Expand an in-place rotate of register `d` by `n` (width `w`) into the
    shift-or idiom over scratch `R15`. `ror(d,n) = (d>>n)|(d<<(w-n))`;
    `rol(d,n) = ror(d, w-n)`. All four lines are printer-recognised two-source
    forms. `ii` is the carried instruction info. -/
def expandRotInPlace (ii : Nat) (d : LOperand) (dir : String)
    (n w : Nat) : List Linstr :=
  let rn := if dir = "ROL" then (w - n) % w else n % w
  let ln := (w - rn) % w
  let sh := wTag w
  let mv := if w = 64 then "MOV:64" else "MOV"
  [⟨ii, .Lopn [.reg reloadScratch] mv [d]⟩,
   ⟨ii, .Lopn [.reg reloadScratch] ("SHR" ++ sh) [.reg reloadScratch, .imm rn]⟩,
   ⟨ii, .Lopn [d] ("SHL" ++ sh) [d, .imm ln]⟩,
   ⟨ii, .Lopn [d] ("OR" ++ sh) [d, .reg reloadScratch]⟩]

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
def legalizeShiftImmBody (body : Lcmd) : Lcmd :=
  body.flatMap legalizeShiftImmInstr

/-- Apply the shift-immediate legalisation to every function body of an `Lprog`. -/
def legalizeShiftImmLprog (p : Lprog) : Lprog :=
  { p with
    lp_funcs := p.lp_funcs.map (fun (n, f) =>
      (n, { f with lfd_body := legalizeShiftImmBody f.lfd_body })) }

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The round-`e'` leaf lowered through the thirDialect spine and exported to a
    physical, two-address SysV `Lprog`, then shift/rotate-immediate-legalised so
    the owned printer renders the three rotates. `fname` `"sha256_round_e"`
    becomes the emitted asm label (matching the C extern). -/
def roundEOwnedLprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha256RoundEComThir) "sha256_round_e"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      roundEInLoadMap                       -- inLoadMap
      roundEOutStoreMap                     -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32, 32, 32, 32, 32, 32, 32])         -- abiTyin (7 u32 inputs)

/-- The rendered owned-backend AT&T `.s` for `sha256_round_e` (no jasminc). -/
def roundEOwnedAsm : String := renderLprogAtt roundEOwnedLprog

/-! ## 4. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The emitted `.s` carries the SysV leaf label and has no unhandled-op
    sentinel. (Rotate/shift mnemonics are not asserted — the legalisation lands
    the rotates in GP-register shift forms whose exact printed mnemonic is left
    to the printer.) -/
theorem roundEOwnedAsm_shape :
    hasSub roundEOwnedAsm "sha256_round_e"
      ∧ hasSub roundEOwnedAsm "UNHANDLED" = false := by native_decide

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `sha256_round_e` into the
    `bench/thir_front_sha256_round_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha256_round_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha256_round_e_owned.s") roundEOwnedAsm
  IO.println "WROTE bench/thir_front_sha256_round_owned/gen/sha256_round_e_owned.s"
  IO.println "  (SHA-256 compression-round e' word sha256RoundEComThir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256RoundThirOwnedEmit
