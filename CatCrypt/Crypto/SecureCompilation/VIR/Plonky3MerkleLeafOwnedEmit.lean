/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HashLeafEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3CompressEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Plonky3 FRI surrogate-hash leaves through the OWNED x86 backend (no jasminc)

The plonky3 FRI proof-object prover builds its per-layer Merkle commitments and
authentication paths out of a **small 4-lane wrapping-multiply + xor mixer** —
a deliberately-simple, carry-free surrogate hash, NOT the 8-lane Poseidon2 used
for the trace commitment. The two leaves are
`bench/plonky3_compare/include/plonky3_merkle_leaves.jinc`:

```
_p3_hleaf_u64(v) -> o[4]          // 8-byte field elem -> 32-byte digest
  for i in 0..4: t = (prev * GOLDEN + i) * SPLIT;  o[i] = t;  prev = t
  prev = o[0]; for i in 1..4: prev *= 0xA3; o[i] += prev; prev = o[i]

_p3_compress_u64(l[4], r[4]) -> o[4]    // two-to-one compress
  for i in 0..4: t = (l[i]+r[i])*0x9E + i ^ (l[i]*0x6D) ^ r[i];  o[i] = t
  prev = o[0]; for i in 1..4: prev *= 0xC5; o[i] ^= prev; prev = o[i]
```

with `GOLDEN = 0x9E3779B97F4A7C15`, `SPLIT = 0xBF58476D1CE4E5B9`. All arithmetic
is plain wrapping `u64`, with NO field reduction (a random-oracle surrogate,
not BabyBear arithmetic).

This is the owned-backend render of those two leaves. The mixer math is
**exactly** the front-compiled `Plonky3HashLeafEmit.hashLeafCom` /
`Plonky3CompressEmit.compressComFinal` bodies (same GOLDEN/SPLIT lane chain +
`0xA3` additive diffusion; same `0x9E/0x6D/0xC5` xor mixer), so this module
authors NO `Com` of its own — it renders the two FRONT-GENERATED `Com`s
(`hashBody`/`compressBody` LowCT `--translateDialectControl-->`
`catCryptDialect` `--cryptoDialectToJasminCom-->` `Com jasminDialect`) under
the `_p3_hleaf_u64` / `_p3_compress_u64` export symbols:

    Com jasminDialect  --Com.toLprogPhysAbi-->  Lprog (physical-register, SysV ABI)
                       --renderLprogAtt-->       AT&T `.s`  (assembled by `cc`, no jasminc)

## ABI

Both leaves export the `(out : RDI, inp : RSI)` two-pointer SysV ABI with
`outStoreMap = stdOutStore 4` (four `u64` digest lanes to `[RDI + 8j]`, the
last four bindings — the source modules' `*_last_four_bindings_are_copies`).
Inputs are read from `[RSI + 8·idx]`:

* `_p3_hleaf_u64` (8-word context): `inp[0] = v`, `inp[1] = GOLDEN`,
  `inp[2] = SPLIT` (the two 64-bit multipliers stay runtime words, exactly the
  KAT's calling convention); the mix constant `0xA3` and the lane indices
  `0..3` (context words `3..7`) are immediates.
* `_p3_compress_u64` (15-word context): `inp[0..3] = l`, `inp[4..7] = r`; the
  constants `0x9E, 0x6D, 0xC5, 0, 1, 2, 3` (context words `8..14`) are
  immediates.

## What is verified vs trusted

* **Verified (value)**: each `Com` is front-generated and denote-gated against
  the independent C-reference transcription in its source module
  (`Plonky3HashLeafEmit.hash_denote_spec` /
  `Plonky3CompressEmit.compress_denote_spec`), and is pure scalar arith
  (`hash_is_purearith_only` / `compress_is_purearith_only`); the owned render
  is a syntactic map of that same `Com` (`hleaf_from_front` /
  `compress_from_front` below pin the provenance).
* **Verified (printer)**: the shape lemmas pin that the emitted `.s` carries
  each export label and contains no `# UNHANDLED-OP`.
* **Trusted (thin)**: `renderLfundef` / `cc` / the SysV leaf ABI frame.

The byte identity owned-`.s` == reference is the external `cc` KAT
(`bench/plonky3_compare/merkle_leaves_owned_kat.c`, an independent C reference
of the mixer), relinked against the owned `.s` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleLeafOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 0. Shared helpers (substring + ABI maps) -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The standard `out[0..nOut-1]` store map: output word `j` to `[RDI + 8j]`. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- Build the `(immSlotMap, inLoadMap)` pair from a per-input-word constant
    oracle `constAt : idx → Option Nat` over an `nIn`-word context.  A word with
    a constant becomes an immediate; every other word is loaded from
    `[RSI+8·idx]`.  Argument slot `s` corresponds to input word `nIn - 1 - s`
    (the De Bruijn reversal in `comToLfundef`). -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

/-! ## 1. Front provenance

The two `Com`s are the FRONT-GENERATED lowerings from the sibling emit modules
— `hashBody` / `compressBody` (LowCT) through `translateDialectControl` and
`DialectToJasminCom.cryptoDialectToJasminCom`. The theorems below pin that
provenance in checkable form: each deployed `Com` IS the front pipeline's
output. -/

/-- `Plonky3HashLeafEmit.hashLeafCom` is the front pipeline's output for
    `hashBody` capped at the last output copy `q3`. -/
theorem hleaf_from_front :
    (Plonky3HashLeafEmit.frontComAt (Plonky3HashLeafEmit.qN 3)).bind
        DialectToJasminCom.cryptoDialectToJasminCom
      = some Plonky3HashLeafEmit.hashLeafCom :=
  (Option.some_get Plonky3HashLeafEmit.hashLowered_isSome).symm

/-- `Plonky3CompressEmit.compressComFinal` is the front pipeline's output for
    `compressBody` capped at the last output copy `q3`. -/
theorem compress_from_front :
    (Plonky3CompressEmit.frontComAt (Plonky3CompressEmit.qN 3)).bind
        DialectToJasminCom.cryptoDialectToJasminCom
      = some Plonky3CompressEmit.compressComFinal :=
  (Option.some_get Plonky3CompressEmit.compressLowered_isSome).symm

/-! ## 2. Per-leaf constant oracles

`_p3_hleaf_u64` over the 8-word `Plonky3HashLeafEmit` context: `v`, `GOLDEN`,
`SPLIT` (words `0..2`) stay runtime pointer loads (the KAT passes GOLDEN/SPLIT
in `inp[1..2]`); the mix constant `0xA3` and lane indices (words `3..7`) are
immediates. `_p3_compress_u64` over the 15-word `Plonky3CompressEmit` context:
`l`/`r` (words `0..7`) runtime, the 7 mix constants (words `8..14`)
immediates. -/

/-- leaf-hash constant oracle: words `3..7` (`0xA3, 0, 1, 2, 3`) are immediates;
    `v`, `GOLDEN`, `SPLIT` (words `0..2`) are runtime. -/
def hleafConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 3 ∧ idx ≤ 7 then some (Plonky3HashLeafEmit.constNat (idx - 1)) else none

/-- compress constant oracle: words `8..14` (`0x9E, 0x6D, 0xC5, 0, 1, 2, 3`)
    are immediates; `l`/`r` (words `0..7`) are runtime. -/
def compressConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 8 ∧ idx ≤ 14 then some (Plonky3CompressEmit.constNat (idx - 8)) else none

/-! ## 3. The two owned leaves -/

/-- leaf-hash leaf (`_p3_hleaf_u64`): 1 value + 2 multipliers in, 4 lanes out.
    Renders the FRONT-GENERATED `Plonky3HashLeafEmit.hashLeafCom`. -/
def hleafOwnedLprog : Lprog :=
  let (imm, inl) := abiMaps 8 hleafConstAt
  Com.toLprogPhysAbi Plonky3HashLeafEmit.hashLeafCom
    "_p3_hleaf_u64" (fun _ => none) imm inl (stdOutStore 4)

/-- compress leaf (`_p3_compress_u64`): 8 words in, 4 lanes out.
    Renders the FRONT-GENERATED `Plonky3CompressEmit.compressComFinal`. -/
def compressOwnedLprog : Lprog :=
  let (imm, inl) := abiMaps 15 compressConstAt
  Com.toLprogPhysAbi Plonky3CompressEmit.compressComFinal
    "_p3_compress_u64" (fun _ => none) imm inl (stdOutStore 4)

/-- Both surrogate-hash leaves combined into one `.s`. -/
def merkleLeavesOwnedLprog : Lprog :=
  { hleafOwnedLprog with
    lp_funcs := hleafOwnedLprog.lp_funcs ++ compressOwnedLprog.lp_funcs }

def hleafOwnedAsm : String := renderLprogAtt hleafOwnedLprog
def compressOwnedAsm : String := renderLprogAtt compressOwnedLprog
def merkleLeavesOwnedAsm : String := renderLprogAtt merkleLeavesOwnedLprog

/-! ## 4. Structural gates

The output-store map is in range: both `Com`s end in (at least) four bindings —
the source modules' `*_last_four_bindings_are_copies` pin that the last four
are exactly the digest-lane copies. -/

/-- Binding count of a `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

theorem hleaf_bindings_ge :
    4 ≤ comBindings Plonky3HashLeafEmit.hashLeafCom := by native_decide
theorem compress_bindings_ge :
    4 ≤ comBindings Plonky3CompressEmit.compressComFinal := by native_decide

/-! ## 5. Conservative printer shape lemmas -/

theorem hleaf_owned_has_leaf :
    hasSub hleafOwnedAsm "_p3_hleaf_u64" = true := by native_decide
theorem hleaf_owned_no_unhandled :
    hasSub hleafOwnedAsm "UNHANDLED" = false := by native_decide
theorem compress_owned_has_leaf :
    hasSub compressOwnedAsm "_p3_compress_u64" = true := by native_decide
theorem compress_owned_no_unhandled :
    hasSub compressOwnedAsm "UNHANDLED" = false := by native_decide

/-- The combined `.s` carries both leaf labels (structural: its `lp_funcs` is the
    concatenation of the two single-leaf programs). -/
theorem merkleLeaves_owned_funcs_len :
    merkleLeavesOwnedLprog.lp_funcs.length = 2 := by native_decide

/-! ## 6. Emit driver -/

/-- Write the owned-backend `.s` carrying both FRI surrogate-hash leaves into the
    `bench/plonky3_compare/gen_com` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/merkle_leaves_owned.s") merkleLeavesOwnedAsm
  IO.println "WROTE plonky3 owned FRI surrogate-hash leaves .s (_p3_hleaf_u64 / _p3_compress_u64)"
  IO.println "  FRONT-GENERATED Com (translateDialectControl + cryptoDialectToJasminCom) -> toLprogPhysAbi -> renderLprogAtt, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleLeafOwnedEmit

/-- Top-level entry point. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleLeafOwnedEmit.emitMain
  return 0
