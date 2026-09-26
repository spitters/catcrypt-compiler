/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Goldilocks
public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2KoalaBearEmit
public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Mersenne31
public import CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonBN254Emit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

/-!
# Owned x86-64 rendering of the Goldilocks, Poseidon2 and BN254 Poseidon kernels

`lake exe zkfieldsowned [DIR]` renders seven kernels through `Com.toLprogPhysAbi`
and the owned printer to AT&T `.s` files in `DIR` (default
`../catcrypt-compiler/bench/zk_fields_owned/gen`, relative to the dev root it is run
from), and exits with status `1` when any rendered text contains an `UNHANDLED`
marker or any kernel fails the `lcmdDirect` hypothesis of the constant-time theorem
(`directChecks`).

| file                   | symbol              | source program                               |
|------------------------|---------------------|----------------------------------------------|
| `gl_add.s`             | `gl_add`            | `Goldilocks.glAddBlk` on a two-word context  |
| `gl_sub.s`             | `gl_sub`            | `Goldilocks.glSubBlk` on a two-word context  |
| `gl_mul.s`             | `gl_mul`            | `Goldilocks.glMulBlk` on a two-word context  |
| `gl_neg.s`             | `gl_neg`            | `Goldilocks.glNegBlk` on a one-word context  |
| `poseidon2_kb.s`       | `poseidon2_kb`      | `Poseidon2KoalaBear.permAsm`                 |
| `poseidon2_m31.s`      | `poseidon2_m31`     | `Poseidon2Mersenne31.permJasminAt 15`        |
| `poseidon_bn254_t3.s`  | `poseidon_bn254_t3` | `PoseidonBN254.permAsm`                      |

## ABI

Every function is `void f(uint64_t *out, const uint64_t *in)`. Context entry `i`
(entry `0` the most recent binding) is argument slot `n - 1 - i` of an `n`-word
context and is loaded from `8 i(%rsi)`; the last `m` bindings of the body are stored
to `8 j(%rdi)`, `j < m`.

* Goldilocks: `in[0] = x`, `in[1] = y` (canonical, `< P`), `out[0]` the canonical
  result of `x + y`, `x - y`, `x * y` or `-x`.
* Poseidon2 (KoalaBear, Mersenne-31): `in[0..15]` the canonical lanes, `out[0..15]`
  the permuted lanes.
* BN254 Poseidon: `in[0..11]` and `out[0..11]` hold three lanes of four
  little-endian limbs of `x · 2²⁵⁶ mod r`.

## What is proved and what is not

The value theorems are those of the source programs: `Goldilocks.glAddBlk_value`
and its siblings, `Poseidon2KoalaBear.permJasminAt_spec`,
`Poseidon2Mersenne31.permJasminAt_spec` and `PoseidonBN254Lower.permJasminAt_denote`.
The physical export, the passes of `renderOwned` and `renderOwnedZeroized`, and the
printer are not proved to preserve them; the known-answer harnesses of
`bench/zk_fields_owned` test the assembled output.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.ZkFieldsEmitMain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (renderOwned)

/-! ## Goldilocks field operations -/

namespace Goldilocks

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (w64)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Goldilocks

/-- The two-word input context: entry `0` is `x`, entry `1` is `y`. -/
abbrev binCtxt : Ctxt jasminDialect := [w64, w64]

/-- The one-word input context of negation. -/
abbrev unCtxt : Ctxt jasminDialect := [w64]

/-- The input-load map of an `n`-word context: argument slot `s` holds context entry
    `n - 1 - s`, read from `8 (n - 1 - s)(%rsi)`. -/
def inLoad (n : Nat) : InLoadMap := fun slot =>
  if slot < n then some ("RSI", (n - 1 - slot) * 8) else none

/-- The output-store map: the last binding, written to `0(%rdi)`. -/
def outStore : OutStoreMap := [("RDI", 0)]

/-- `x + y`. -/
def addCom : Com jasminDialect binCtxt w64 := glAddBlk .here Ctxt.Var.here.there
/-- `x - y`. -/
def subCom : Com jasminDialect binCtxt w64 := glSubBlk .here Ctxt.Var.here.there
/-- `x * y`. -/
def mulCom : Com jasminDialect binCtxt w64 := glMulBlk .here Ctxt.Var.here.there
/-- `-x`. -/
def negCom : Com jasminDialect unCtxt w64 := glNegBlk .here

/-- The exported two-input program `c` as the function `fname`. -/
def binLprog (c : Com jasminDialect binCtxt w64) (fname : String) : Lprog :=
  Com.toLprogPhysAbi c fname (fun _ => none) (fun _ => none) (inLoad 2) outStore

/-- The AT&T text of `gl_add`. -/
def addAsm (_ : Unit) : String := renderOwned (binLprog addCom "gl_add")
/-- The AT&T text of `gl_sub`. -/
def subAsm (_ : Unit) : String := renderOwned (binLprog subCom "gl_sub")
/-- The AT&T text of `gl_mul`. -/
def mulAsm (_ : Unit) : String := renderOwned (binLprog mulCom "gl_mul")
/-- The AT&T text of `gl_neg`. -/
def negAsm (_ : Unit) : String :=
  renderOwned (Com.toLprogPhysAbi negCom "gl_neg" (fun _ => none) (fun _ => none)
    (inLoad 1) outStore)

end Goldilocks

/-! ## Poseidon2 over Mersenne-31 -/

/-- The exported Mersenne-31 Poseidon2 permutation: `permJasminAt 15` as the function
    `poseidon2_m31`, with the width-16 Poseidon2 ABI maps. -/
def m31Lprog (_ : Unit) : Lprog :=
  Com.toLprogPhysAbi (Poseidon2Mersenne31.permJasminAt 15) "poseidon2_m31" (fun _ => none)
    poseidon2ImmSlots poseidon2InLoadMap poseidon2OutStoreMap

/-- The AT&T text of `poseidon2_m31`. -/
def m31Asm (_ : Unit) : String := renderOwned (m31Lprog ())

/-! ## Driver -/

/-- The default output directory, relative to the dev root. -/
def defaultDir : String := "../catcrypt-compiler/bench/zk_fields_owned/gen"

/-- The rendered kernels: file name and a thunk producing the AT&T text. -/
def kernels : List (String × (Unit → String)) :=
  [ ("gl_add.s", Goldilocks.addAsm),
    ("gl_sub.s", Goldilocks.subAsm),
    ("gl_mul.s", Goldilocks.mulAsm),
    ("gl_neg.s", Goldilocks.negAsm),
    ("poseidon2_kb.s", Poseidon2KoalaBear.permAsm),
    ("poseidon2_m31.s", m31Asm),
    ("poseidon_bn254_t3.s", PoseidonBN254.permAsm) ]

open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation (lcmdDirect) in
/-- Per kernel, the hypothesis `lcmdDirect (comToLfundef com imm).lfd_body` of
    `AllocCTPreservation.toLprogPhysAbi_gather_constant_time`: no instruction of the
    allocated body addresses memory through an index register. When it holds, the
    gathered machine block of the exported function has a leakage trace independent
    of the initial state. The BN254 kernel is rendered after `fuseMulHiLprog`, a
    pass that theorem does not cover. -/
def directChecks : List (String × (Unit → Bool)) :=
  [ ("gl_add", fun _ => lcmdDirect (comToLfundef Goldilocks.addCom (fun _ => none)).lfd_body),
    ("gl_sub", fun _ => lcmdDirect (comToLfundef Goldilocks.subCom (fun _ => none)).lfd_body),
    ("gl_mul", fun _ => lcmdDirect (comToLfundef Goldilocks.mulCom (fun _ => none)).lfd_body),
    ("gl_neg", fun _ => lcmdDirect (comToLfundef Goldilocks.negCom (fun _ => none)).lfd_body),
    ("poseidon2_kb", fun _ => lcmdDirect
      (comToLfundef (Poseidon2KoalaBear.permJasminAt 15) poseidon2ImmSlots).lfd_body),
    ("poseidon2_m31", fun _ => lcmdDirect
      (comToLfundef (Poseidon2Mersenne31.permJasminAt 15) poseidon2ImmSlots).lfd_body),
    ("poseidon_bn254_t3", fun _ => lcmdDirect
      (comToLfundef PoseidonBN254.permCom PoseidonBN254.permImmSlots).lfd_body) ]

/-- Check and write the kernels whose names (without `.s`) are in `only`, or every
    kernel when `only` is empty, to `dir`; the number of kernels whose
    `directChecks` entry is `false` or whose text contains an `UNHANDLED` marker. -/
def emitAll (dir : String) (only : List String) : IO Nat := do
  IO.FS.createDirAll dir
  let mut bad := 0
  for ((file, asm), (name, ok)) in kernels.zip directChecks do
    if only.isEmpty || only.contains name then
      if ok () then
        IO.println s!"lcmdDirect {name}: true"
      else
        IO.eprintln s!"lcmdDirect {name}: false"
        bad := bad + 1
      let text := asm ()
      let path := dir ++ "/" ++ file
      IO.FS.writeFile path text
      if PoseidonBN254.hasUnhandled text then
        IO.eprintln s!"UNHANDLED marker in {path}"
        bad := bad + 1
      else
        IO.println s!"wrote {path}"
  return bad

end CatCrypt.Crypto.SecureCompilation.Algebraic.ZkFieldsEmitMain

/-- Entry point of `lake exe zkfieldsowned [DIR [NAME ...]]`; the names select kernels
    (e.g. `gl_mul poseidon2_kb`), so that each heavy kernel runs in its own process. -/
def main (args : List String) : IO UInt32 := do
  let dir := args.headD CatCrypt.Crypto.SecureCompilation.Algebraic.ZkFieldsEmitMain.defaultDir
  let bad ← CatCrypt.Crypto.SecureCompilation.Algebraic.ZkFieldsEmitMain.emitAll dir args.tail
  return if bad = 0 then 0 else 1
