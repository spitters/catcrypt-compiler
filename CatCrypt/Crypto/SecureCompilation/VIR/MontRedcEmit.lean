/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.MontRedcCatCryptEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.MontRedcCatCryptEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# The single-word Montgomery REDC step through the OWNED x86 backend (NO jasminc)

`MontRedcCatCryptEmit.lean` lowers the single-word Montgomery REDC step from the
high `catCryptDialect` to `Com jasminDialect` (`montRedcWordJasmin`) and emits it
through the *testing/comparison* path (`emitJazz` → jasminc). That step uses the
split-word ops `bvMul`/`bvMulHi`/`bvAddCarryLo`/`bvAddCarryHi`, i.e. x86
`MUL`/`MULX`/`ADCX` — and jasminc rejected the `MULXHI` form. The **owned** x86
backend emits real `MULX`, so the same lowered `Com jasminDialect` renders fine:

```
Com jasminDialect  --Com.toLprogPhysAbi-->  Lprog  --renderLprogAtt-->  AT&T `.s`
```

assembled by `cc`/`as` directly, no jasminc.

## ABI (2-pointer SysV, `f(out = RDI, inp = RSI)`)

The lowered step's input context is `mapCtx Γᵣ` = four machine words
`[Tlo, Thi, q, qp]` (input low/high limbs, modulus, Montgomery constant). All
four are runtime inputs — there are no baked immediates — so each is read from
the `inp`/RSI buffer at its word offset, and the single reduced word
`t = T_hi + mqHi + c` is stored to `out[0]` on RDI.

`abiMaps` builds the `(immSlotMap, inLoadMap)` pair with an empty constant oracle
(every word is a runtime load); argument slot `s` corresponds to input word
`nInputs - 1 - s` (the De Bruijn reversal in `comToLfundef`), as in
`Plonky3LdeColumnEmit`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MontRedcEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.MontRedcCatCryptEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiLprog)

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

/-! ## 1. The REDC-step input context

`Γᵣ = [Tlo, Thi, q, qp]` — four words, all runtime `RSI` loads, no immediates. -/

/-- The number of input words of the single-word Montgomery REDC step. -/
def nInputs : Nat := 4

/-- The REDC step has no baked immediates: every input word `Tlo,Thi,q,qp` is a
    runtime load. -/
def montConstAt (_idx : Nat) : Option Nat := none

/-! ## 2. The owned `Lprog` + AT&T `.s` -/

/-- The single-word Montgomery REDC step as a 2-pointer-ABI physical-register
    `Lprog` (symbol `mont_redc_step_owned`), built from the *same* lowered
    `montRedcWordJasmin` the jasminc path uses. The owned backend emits real
    `MULX` (the `bvMulHi` op jasminc rejected). -/
def montRedcLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs montConstAt
  fuseMulHiLprog
    (Com.toLprogPhysAbi montRedcWordJasmin "mont_redc_step_owned"
      (fun _ => none) imm inl (stdOutStore 1))

/-- The owned-backend AT&T `.s` text of the Montgomery REDC step
    (symbol `mont_redc_step_owned`), rendered straight from the `Lprog` by the
    verified printer — no jasminc. -/
def montRedcAtt : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned montRedcLprog

/-! ## 3. Printer shape lemmas: the export label is present, no unhandled op -/

#guard (hasSub montRedcAtt "mont_redc_step_owned")

#guard !(hasSub montRedcAtt "UNHANDLED")

/-! ## 4. Emit driver -/

/-- Emit driver: write the owned-backend Montgomery REDC step `.s` (rendered
    straight from the lowered `Com jasminDialect`, NO jasminc — the owned backend
    emits the real `MULX` jasminc declined) to the bench gen-from-Com directory
    under the symbol `mont_redc_step_owned`. -/
def emit : IO Unit := do
  let dir := "bench/bls12381_fieldmul_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/mont_redc_step_owned.s") montRedcAtt
  IO.println "WROTE bench/bls12381_fieldmul_compare/gen_com/mont_redc_step_owned.s"
  IO.println "  owned x86 backend (toLprogPhysAbi -> renderLprogAtt), real MULX, NO jasminc"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emit

end CatCrypt.Crypto.SecureCompilation.VIR.MontRedcEmit
