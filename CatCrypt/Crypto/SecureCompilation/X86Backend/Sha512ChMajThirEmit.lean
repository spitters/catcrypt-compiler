/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ThirToCom_Sha512ChMaj
public import CatCrypt.Crypto.SecureCompilation.ThirToCom_Sha512ChMaj
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512SigmaThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512SigmaThirEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# SHA-512 `Ch` and `Maj` (width 64) through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §4.1.3 multi-input boolean round components `Ch`/`Maj` of SHA-512
(width 64) driven through the `compile-from-hax` front (`Com thirDialect`) onto
the OWNED x86 backend — NO jasminc anywhere. The 3-in/1-out width-64 sibling of
`Sha512SigmaThirEmit.lean` (the 1-in σ leaves): both leaves carry only
`and`/`xor`/`xor-with-literal` ops (no rotate, no shift), so the shift/rotate
immediate legalisation pass is a harmless pass-through here (kept for shape
uniformity with the σ emitter).

    Ch(e,f,g)  = (e ∧ f) ⊕ (¬e ∧ g)             (FIPS 180-4 §4.1.3)
    Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)    (FIPS 180-4 §4.1.3)

The leaves `sha512ChThir` / `sha512MajThir` (`Com thirDialect`, built from
`thBin .and 64` / `thBin .xor 64` / `thBinLit .xor 64 0xffffffffffffffff`) are
lowered through the unified `thirDialect` spine (`lowerThir`) and routed through
the OWNED backend, emitting both as leaves in a single `.s`.

The pipeline mirrors `Sha512SigmaThirEmit`:

    sha512{Ch,Maj}Thir : Com thirDialect [.reg 64,.reg 64,.reg 64] (.reg 64)
      --lowerThir-->            Com jasminDialect [.reg 64,…] (.reg 64)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the three inputs are loaded from `[RSI + off]` and the single output stored
to `out[0]`:

```c
extern void sha512_ch(uint64_t *out, const uint64_t *inp);   // inp = [e, f, g]
extern void sha512_maj(uint64_t *out, const uint64_t *inp);  // inp = [a, b, c]
```

With three inputs (`nArgs = 3`) the slot stride is
`inLoadMap s = ("RSI", 8 * (2 - s))`, modelled exactly on the round-`e`
`8 * (nArgs - 1 - s)` slot stride: slot `2` = first arg (`e`/`a`) = `inp[0]`,
slot `1` = second arg (`f`/`b`) = `inp[1]`, slot `0` = third arg (`g`/`c`) =
`inp[2]`. The single output (the last binding, `Ch`/`Maj`) is stored to `out[0]`
(`outStoreMap = [("RDI", 0)]`).

## What is verified vs trusted

* **Verified (value)**: `sha512ChThir_denote` / `sha512MajThir_denote`
  (the leaves denote `Ch`/`Maj` = `sha512ChSpec`/`sha512MajSpec`) and
  `ch64_via_thirDialect` / `maj64_via_thirDialect` (the lowered `Com jasminDialect`
  denotes the same).
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha512_ch(e,f,g) == Ch(e,f,g)` and
`sha512_maj(a,b,c) == Maj(a,b,c)` is the external `as`/`cc` KAT in
`bench/thir_front_sha512_chmaj_owned/` (no jasminc).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512ChMajThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (sha512ChThir sha512MajThir)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512SigmaThirEmit
  (legalizeShiftImmLprog)

/-! ## 1. ABI maps for the 3-in / 1-out width-64 `Ch`/`Maj` leaves -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (2 - s))`. Slot `2` is the
    first arg (`e`/`a`) = `inp[0]`, slot `1` the second (`f`/`b`) = `inp[1]`,
    slot `0` the third (`g`/`c`) = `inp[2]`. Slots `≥ 3` are absent. -/
def chMajInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 16)       -- slot 0 = third arg = inp[2]
  else if s = 1 then some ("RSI", 8)   -- slot 1 = second arg = inp[1]
  else if s = 2 then some ("RSI", 0)   -- slot 2 = first arg  = inp[0]
  else none

/-- Output-store map: the single result word (the last binding) is stored to
    `out[0]` (`[RDI + 0]`). -/
def chMajOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 2. The owned `Lprog`s and combined AT&T emission (no jasminc)

The shift/rotate-immediate legalisation pass (`legalizeShiftImmLprog`, shared
from `Sha512SigmaThirEmit`) is retained for shape uniformity; `Ch`/`Maj`
emit no rotate/shift ops, so it is a harmless pass-through here. -/

/-- Build a 3-in/1-out width-64 owned `Lprog` for a `Com thirDialect`
    `Ch`/`Maj` leaf under the SysV 2-pointer ABI. -/
def chMajLprog
    (com : Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64))
    (fname : String) : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir com) fname
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      chMajInLoadMap                        -- inLoadMap
      chMajOutStoreMap                      -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64, 64])                         -- abiTyin (3 u64 inputs)

/-- `Ch` owned `Lprog` (`fname` `"sha512_ch"`). -/
def chLprog : Lprog := chMajLprog sha512ChThir "sha512_ch"

/-- `Maj` owned `Lprog` (`fname` `"sha512_maj"`). -/
def majLprog : Lprog := chMajLprog sha512MajThir "sha512_maj"

/-- Both leaves combined into a single `Lprog` (`lp_funcs` concatenated), so
    `renderLprogAtt` emits one `.s` carrying both `sha512_ch` and
    `sha512_maj`. -/
def sha512ChMajLprog : Lprog :=
  { chLprog with
    lp_funcs := chLprog.lp_funcs ++ majLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for both leaves (no jasminc). -/
def sha512ChMajAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned sha512ChMajLprog

/-! ## 3. Shape checks on the emitted asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 4. Emit driver -/

/-- Write the owned-backend `.s` for `sha512_ch`/`sha512_maj` into the
    `bench/thir_front_sha512_chmaj_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha512_chmaj_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha512_chmaj_owned.s") sha512ChMajAsm
  IO.println "WROTE bench/thir_front_sha512_chmaj_owned/gen/sha512_chmaj_owned.s"
  IO.println "  (SHA-512 Ch/Maj round components sha512{Ch,Maj}Thir"
  IO.println "   through Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt"
  IO.println "   onto the OWNED x86 backend, NO jasminc)"

/-! ## 5. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512ChMajThirEmit
