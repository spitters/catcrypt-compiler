/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# BLAKE2b G mixing function through the OWNED x86 backend (no jasminc)

The RFC 7693 §3.1 BLAKE2b `G` mixing function driven through the
`compile-from-hax` front (`Com thirDialect`) onto the OWNED x86 backend — NO
jasminc anywhere. The width-64 companion of `ChaChaQRThirOwnedEmit` (the RFC
8439 width-32 quarter-round): `G` has the same shape (add / xor / rotate body,
one output word per leaf) but is **6-in / 1-out u64** instead of 4-in / 1-out
u32, and its rotates are width-64 (`ror64` by 32/24/16/63).

`G` takes the four state words `a, b, c, d` plus the two message words `x, y`
(RFC 7693 §3.1) and produces four updated words `(a', b', c', d')`. Each of the
four leaves (`ThirToComFront.{gAThir, gBThir, gCThir, gDThir}`) recomputes the
FULL `G` body (shared SSA `gBody`) and returns ONE of the four updated words:

    blake2b_g_a(a,b,c,d,x,y) = a'     (= a4,  gAThir)
    blake2b_g_b(a,b,c,d,x,y) = b'     (= b4,  gBThir)
    blake2b_g_c(a,b,c,d,x,y) = c'     (= c2,  gCThir)
    blake2b_g_d(a,b,c,d,x,y) = d'     (= d4,  gDThir)

The pipeline mirrors `ChaChaQRThirOwnedEmit`:

    gXThir : Com thirDialect [.reg 64, …, .reg 64] (.reg 64)   (6 inputs)
      --lowerThir-->            Com jasminDialect [...] (.reg 64)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

All four functions are gathered into ONE `Lprog` (`renderLprogAtt` renders each
with a unique label prefix), emitting a single `.s` with four SysV leaves.

## The RFC 7693 G mixing function (`ThirToComFront.blake2bGSpec`)

```
a = a + b + x;  d = ror64(d ^ a, 32);
c = c + d;      b = ror64(b ^ c, 24);
a = a + b + y;  d = ror64(d ^ a, 16);
c = c + d;      b = ror64(b ^ c, 63);
```

`ror64(z, n)` is `z.rotateRight n` (`thRor 64 n`). The shared SSA body `gBody`
produces the 14 compute bindings (head-first)
`a1, a2, d1, d2, c1, b1, b2, a3, a4, d3, d4, c2, b3, b4`; the four output words
live at `a' = a4`, `b' = b4`, `c' = c2`, `d' = d4`. Each leaf ends with an
identity-copy (`thRor 64 0`) of its chosen word so the register-arith emit reads
that word back as the result.

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the six inputs are loaded from `[RSI + off]` and the single output stored
to `[RDI + 0]`:

```c
extern void blake2b_g_a(uint64_t *out, const uint64_t *inp);   // inp=[a,b,c,d,x,y]
//   (and blake2b_g_b / _c / _d)   out[0] receives the chosen G output word
```

Argument-slot numbering (`JasminLprogExport.comToLfundef`): argument slot `s`
(program-root order) is context entry `nArgs - 1 - s`. `gXThir`'s context is
`[a, b, c, d, x, y]` (a = `.here`, …, y = `.there⁵ .here`), so input index
`a = 0, b = 1, …, y = 5`, and arg slot `s ↦ input index (6 - 1 - s) = 5 - s`.
With C-side `inp = [a, b, c, d, x, y]`:

* slot `5` → input `a` (`inp[0]`, byte offset 0)
* slot `4` → input `b` (`inp[1]`, byte offset 8)
* slot `3` → input `c` (`inp[2]`, byte offset 16)
* slot `2` → input `d` (`inp[3]`, byte offset 24)
* slot `1` → input `x` (`inp[4]`, byte offset 32)
* slot `0` → input `y` (`inp[5]`, byte offset 40)

i.e. `gInLoadMap s = ("RSI", 8 * (5 - s))` — the width-64 6-input analogue of
ChaCha's `8 * (3 - s)`. The single output (the last binding, the identity-copy
of the chosen word) is stored to `out[0]` (`gOutStoreMap = [("RDI", 0)]`). The
8-byte slot stride matches the natural u64 layout `uint64_t inp[6]`.

## The `ror64` rotates (shift-immediate legalisation)

`G`'s `ror64(z, n)` lower to `thRor 64 n`, ultimately width-tagged
shift/rotate-immediate `Lopn` forms (`SHR:<n>:64` / `SHL:<n>:64` /
`ROR:<n>:64`). `legalizeShiftImmLprog` (cloned from `ChaChaQRThirOwnedEmit`,
which already handles the `:64` width tag) rewrites:

* unary `SHR:<n>:64` / `SHL:<n>:64` into the printer's two-source operand form
  `[d] SHR:64 [d, #n]` (prefixed by `MOV:64` when `d ≠ s`), mirroring
  `JasminLprogExport.lowerTwoAddrShiftImm`;
* a rotate `ROR:<n>:64` into the canonical shift-or idiom over the reserved
  scratch `R15`: `ror(d, n) = (d >> n) | (d << (64 - n))`, emitted as four
  printer-recognised two-source forms (`MOV:64`, `SHR:64`, `SHL:64`, `OR:64`).

So the emitted `.s` carries no unhandled-op sentinel. NOTE: the scratch-`R15`
rotate expansion is the structural-clone choice; the orchestrator may prefer
adding a native `rorq`/`rolq` arm to `attBase` and a one-line `[d] ROR [d, #n]`
legalisation. The shift-or form here is value-correct and printer-only.

## What is verified vs trusted

* **Verified (value)**: `gAThir_denote` … `gDThir_denote` (each leaf denotes its
  `blake2bGSpec` component) and `gA_via_thirDialect` … `gD_via_thirDialect` (the
  lowered `Com jasminDialect` denotes the same) — all in `ThirToComFront`.
* **Verified (printer)**: the shape lemma below pins that the emitted `.s`
  carries the `blake2b_g_a` SysV leaf label and has no unhandled-op sentinel.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `blake2b_g_X(a,b,c,d,x,y) == X'` is the external `as`/`cc` KAT
in `bench/thir_front_blake2b_g_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2bGThirOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (gAThir gBThir gCThir gDThir)

/-! ## 1. ABI maps for the 6-in / 1-out width-64 BLAKE2b G leaves -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (5 - s))`. Slot `5` is input `a`
    (`inp[0]`, offset 0); slot `4` is `b` (offset 8); …; slot `0` is `y`
    (offset 40). Slots `≥ 6` are absent (6 inputs). -/
def gInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 40)       -- slot 0 = input y = inp[5]
  else if s = 1 then some ("RSI", 32)  -- slot 1 = input x = inp[4]
  else if s = 2 then some ("RSI", 24)  -- slot 2 = input d = inp[3]
  else if s = 3 then some ("RSI", 16)  -- slot 3 = input c = inp[2]
  else if s = 4 then some ("RSI", 8)   -- slot 4 = input b = inp[1]
  else if s = 5 then some ("RSI", 0)   -- slot 5 = input a = inp[0]
  else none

/-- Output-store map: the single result word (the last identity-copy binding) is
    stored to `out[0]` (`[RDI + 0]`). -/
def gOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 2. Shift and rotate immediate legalisation post-pass

Cloned from `ChaChaQRThirOwnedEmit` (which already handles the `:64` width tag).
The owned printer renders the two-source shift form `[d] SHR:64 [d, #n]` /
`[d] SHL:64 [d, #n]` (and `OR:64`), but recognises NEITHER the unary
`shrImm`/`shlImm` mnemonic `SHR:<n>:64` NOR any rotate mnemonic (`attBase` has
no `ROR`/`ROL`). So:

* unary `SHR:<n>:64` / `SHL:<n>:64` rewrite to the two-source operand form
  `[d] SHR:64 [d, #n]` (prefixed by `MOV:64` when `d ≠ s`), mirroring
  `JasminLprogExport.lowerTwoAddrShiftImm`;
* a rotate `ROR:<n>:64` (the lowering target of `thRor 64 n`, RFC 7693's
  `ror64`) is expanded into the canonical shift-or idiom over the reserved
  scratch `R15` (`reloadScratch`, never an allocatable destination, dead between
  reload micro-sequences): for an in-place rotate of register `d` by `n` over
  width `64`, `ror(d, n) = (d >> n) | (d << (64 - n))`, emitted as

      MOV:64 R15, d           -- t := d                  (only when d ≠ s: MOV d, s first)
      SHR:64 R15, #n          -- t >>= n
      SHL:64 d,   #(64 - n)   -- d <<= (64 - n)
      OR:64  d,   R15         -- d |= t

  All four lines use printer-recognised two-source `Lopn` forms (`MOV:64`,
  `SHR:64`, `SHL:64`, `OR:64`), so the emitted `.s` carries no unhandled-op
  sentinel. -/

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

/-- Width-tag suffix (`":64"` for 64-bit, empty for 32-bit) for a legalised
    two-source mnemonic at width `w`. -/
def wTag (w : Nat) : String := if w = 64 then ":64" else ""

/-- Expand an in-place rotate of register `d` by `n` (width `w`) into the
    shift-or idiom over scratch `R15`. `ror(d,n) = (d>>n)|(d<<(w-n))`;
    `rol(d,n) = ror(d, w-n)`. All four lines are printer-recognised two-source
    forms. `ii` is the carried instruction info. -/
def expandRotInPlace (ii : Nat) (d : LOperand) (dir : String)
    (n w : Nat) : List Linstr :=
  -- left-rotate by n == right-rotate by (w - n)
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
    * a rotate `Lopn [d] "ROR:<n>[:w]" [s]` → (a `MOV d, s` when `d ≠ s`, to move
      the rotate's source into place) followed by the `expandRotInPlace` shift-or
      idiom over `R15`;

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

/-! ## 3. The owned `Lprog`s and AT&T emission (no jasminc) -/

/-- Lower one BLAKE2b G leaf through the thirDialect spine and export to a
    physical, two-address SysV `Lprog`, then shift-immediate-legalise so the
    owned printer renders the `ror64` rotates. `fname` becomes the emitted
    label. -/
def gOwnedLprog (com : Com thirDialect
    [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64] (.reg 64))
    (fname : String) : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir com) fname
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      gInLoadMap                            -- inLoadMap
      gOutStoreMap                          -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64, 64, 64, 64, 64])             -- abiTyin (6 u64 inputs)

/-- The four single-output BLAKE2b G leaves, each its own owned `Lprog`. -/
def gAOwnedLprog : Lprog := gOwnedLprog gAThir "blake2b_g_a"
def gBOwnedLprog : Lprog := gOwnedLprog gBThir "blake2b_g_b"
def gCOwnedLprog : Lprog := gOwnedLprog gCThir "blake2b_g_c"
def gDOwnedLprog : Lprog := gOwnedLprog gDThir "blake2b_g_d"

/-- All four leaves gathered into ONE `Lprog`: concatenate the four single-leaf
    `lp_funcs`. `renderLprogAtt` renders each function with a unique
    label-prefix, so the four bodies' local `.L` labels do not collide. -/
def blake2bGOwnedLprog : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := gAOwnedLprog.lp_funcs ++ gBOwnedLprog.lp_funcs
                ++ gCOwnedLprog.lp_funcs ++ gDOwnedLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for all four BLAKE2b G leaves
    (no jasminc). -/
def blake2bGOwnedAsm : String := renderLprogAtt blake2bGOwnedLprog

/-! ## 4. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The emitted `.s` carries the `blake2b_g_a` SysV leaf label and no
    unhandled-op sentinel. (Rotate mnemonics are not asserted — the legalisation
    lands the `ror64` rotates in GP-register shift forms whose exact printed
    mnemonic is left to the printer.) -/
theorem blake2bGOwnedAsm_shape :
    hasSub blake2bGOwnedAsm "blake2b_g_a"
      ∧ hasSub blake2bGOwnedAsm "UNHANDLED" = false := by native_decide

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for the four BLAKE2b G leaves into the
    `bench/thir_front_blake2b_g_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_blake2b_g_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/blake2b_g_owned.s") blake2bGOwnedAsm
  IO.println "WROTE bench/thir_front_blake2b_g_owned/gen/blake2b_g_owned.s"
  IO.println "  (RFC 7693 BLAKE2b G mixing leaves g{A,B,C,D}Thir through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2bGThirOwnedEmit
