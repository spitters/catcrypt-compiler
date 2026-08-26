/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MayoUovGf256CatCryptEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# The MAYO / UOV GF(2⁸) MAC step through the OWNED x86 backend (NO jasminc)

`MayoUovGf256CatCryptEmit.lean` lowers the GF(2⁸) bit-serial MAC step
(`gf256StepAccCom 0`) from the high `catCryptDialect` down to a
`Com jasminDialect` (`gf256MacStepJasmin`) and emits it through the
*testing/comparison* path (`emitJazz` → jasminc). This file emits the **same**
lowered `Com jasminDialect` through the **owned** x86 backend instead:

```
Com jasminDialect  --Com.toLprogPhysAbi-->  Lprog  --renderLprogAtt-->  AT&T `.s`
```

assembled by `cc`/`as` directly, with no jasminc dependency.

## ABI (2-pointer SysV, `f(out = RDI, inp = RSI)`)

The lowered step's input context is `mapCtx stepΓ` = six machine words
`[acc, a, b, c1, c0, c1b]`. The first three are runtime inputs (read from the
`inp`/RSI buffer at word offsets `0,1,2`); the last three are the GF(2⁸) step's
materialised constants `c1 = 1`, `c0 = 0`, `c1b = 0x1b` (baked as immediates, so
the caller's `inp` buffer need only hold `acc,a,b`). The single output word
(`acc' = acc ^ (a & (0 - ((b>>0)&1)))`) is stored to `out[0]` on RDI.

`abiMaps` builds the `(immSlotMap, inLoadMap)` pair from the per-input-word
constant oracle below; argument slot `s` corresponds to input word
`nInputs - 1 - s` (the De Bruijn reversal in `comToLfundef`), exactly as in
`Plonky3LdeColumnEmit`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MayoUovGf256Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.MayoUovGf256CatCryptEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 0. Shared helpers (substring + ABI maps, mirrors `Plonky3LdeColumnEmit`) -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The standard `out[0..nOut-1]` store map: output word `j` to `[RDI + 8j]`. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- Build the `(immSlotMap, inLoadMap)` pair from a per-input-word constant
    oracle `constAt : idx → Option Nat` over an `nIn`-word context. A word with a
    constant becomes an immediate; every other word is loaded from `[RSI+8·idx]`.
    Argument slot `s` corresponds to input word `nIn - 1 - s`. -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

/-! ## 1. The MAC-step constant oracle

The six-word input context `stepΓ = [acc, a, b, c1, c0, c1b]`. Words `0,1,2`
(`acc, a, b`) are runtime `RSI` loads; words `3,4,5` are the GF(2⁸) step's
materialised constants `c1 = 1`, `c0 = 0`, `c1b = 0x1b` (baked as immediates). -/

/-- The number of input words of one bit-serial GF(2⁸) MAC step. -/
def nInputs : Nat := 6

/-- The GF(2⁸) step constants at input words `3,4,5` (`c1=1`, `c0=0`, `c1b=0x1b`);
    `acc,a,b` at `0,1,2` are runtime loads. -/
def macConstAt (idx : Nat) : Option Nat :=
  if idx = 3 then some 1
  else if idx = 4 then some 0
  else if idx = 5 then some 0x1b
  else none

/-! ## 2. The owned `Lprog` + AT&T `.s` -/

/-- The GF(2⁸) MAC step as a 2-pointer-ABI physical-register `Lprog`
    (symbol `mayo_gf256_mac_owned`), built from the *same* lowered
    `gf256MacStepJasmin` the jasminc path uses. -/
def macStepLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs macConstAt
  Com.toLprogPhysAbi gf256MacStepJasmin "mayo_gf256_mac_owned"
    (fun _ => none) imm inl (stdOutStore 1)

/-- The owned-backend AT&T `.s` text of the GF(2⁸) MAC step
    (symbol `mayo_gf256_mac_owned`), rendered straight from the `Lprog` by the
    verified printer — no jasminc. -/
def macStepAtt : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned macStepLprog

/-! ## 2a. Front provenance

`gf256MacStepJasmin` is the FRONT pipeline's output: the high `catCryptDialect`
bit-serial MAC step `gf256StepAccCom 0` lowered through the seam
`DialectToJasminCom.cryptoDialectToJasminCom` in `MayoUovGf256CatCryptEmit`. The
theorem pins that provenance in checkable form — the deployed `Com` IS the
seam's output, so the owned render above carries no hand-authored `Com`
anywhere on its emit path. -/

/-- The deployed MAC-step `Com` is the front pipeline's output for the
    high-dialect `gf256StepAccCom 0`. -/
theorem macStepCom_from_front :
    DialectToJasminCom.cryptoDialectToJasminCom (gf256StepAccCom 0)
      = some gf256MacStepJasmin :=
  (Option.some_get gf256StepAccCom_lowers).symm

/-! ## 3. Printer shape lemmas: the export label is present, no unhandled op -/

#guard (hasSub macStepAtt "mayo_gf256_mac_owned")

#guard !(hasSub macStepAtt "UNHANDLED")

/-! ## 4. Emit driver -/

/-- Emit driver: write the owned-backend GF(2⁸) MAC step `.s` (rendered straight
    from the lowered `Com jasminDialect`, NO jasminc) to the bench gen-from-Com
    directory under the symbol `mayo_gf256_mac_owned`. -/
def emit : IO Unit := do
  let dir := "bench/uov_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/mayo_gf256_mac_owned.s") macStepAtt
  IO.println "WROTE bench/uov_compare/gen_com/mayo_gf256_mac_owned.s"
  IO.println "  owned x86 backend (toLprogPhysAbi -> renderLprogAtt), NO jasminc"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emit

end CatCrypt.Crypto.SecureCompilation.VIR.MayoUovGf256Emit
