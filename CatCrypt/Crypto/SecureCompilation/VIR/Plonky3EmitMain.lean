/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3CompressEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HashLeafEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldFrontEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFieldEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Plonky3 BabyBear regArith kernels through the OWNED x86 backend (no jasminc)

This is the owned-backend twin of the `.jazz`-then-jasminc emit modules
`Plonky3{Compress,HashLeaf,NttLayer,FriFold}Emit`. Each of those modules builds
a `Com jasminDialect` that is **entirely `regArith add/sub/mul/and/xor/shr`**
(`*_is_regarith_only`, proved there), then renders it to `.jazz` text via
`JasminAbiEmit.emitAbiOrchReg` for jasminc to lower. This module renders the
**same `Com`** straight to AT&T `.s` through the owned linear-jasmin backend:

    Com jasminDialect  --Com.toLprogPhysAbi-->  Lprog (physical-register, SysV ABI)
                       --renderLprogAtt-->       AT&T `.s`  (assembled by `cc`, no jasminc)

— the `Poseidon2LinearMain` / `KeccakLinearMain` owned path (#504/#537), now
applied to the Plonky3 regArith leaves (#656 jasmin-tail migration).

## ABI: constants are immediates (`immSlotMap`), runtime words are pointer loads

The `.jazz` path's `*InName` map resolves each input word to either a literal
immediate (the BabyBear Barrett constants `MU,p,30,32,63`, the mixing constants,
…) or a pointer read `inp[i]`. The owned `toLprogPhysAbi` path reproduces this
split with **two producer-side maps** — *no printer change*:

* `immSlotMap : argSlot → Option Nat` materializes each constant input word as a
  `.imm` operand at producer time (exactly the `inName` immediate decisions);
* `inLoadMap : argSlot → (base, off)` loads each remaining (runtime) input word
  from the `RSI` input pointer.

The argument-slot model is `comToLfundef`'s De Bruijn reversal: input word `idx`
of an `nIn`-word context is argument slot `nIn - 1 - idx`. The `outStoreMap`
stores the `nOut` output words to `out[0..]` via `RDI`.

Because the constants are materialized as immediates (not read from memory), the
owned `.s` has the **same C ABI** as the existing KAT harnesses — those harnesses
already pass the runtime words at the same offsets — so each owned `.s` relinks
into the existing `*_kat.c` byte-identically (re-KAT, no harness change).

## What is verified vs trusted

* **Verified (value)**: each `Com` is `*_is_regarith_only` (proved in its emit
  module), so its denotation is the exact BabyBear word arithmetic; the owned
  render is a syntactic map of that same `Com`.
* **Verified (printer)**: the conservative `*_owned_no_unhandled` shape lemmas
  below pin that each emitted `.s` carries its export label and contains no
  `# UNHANDLED-OP` sentinel.
* **Trusted (thin)**: `renderLfundef` / `cc` / the SysV leaf ABI frame.

The byte identity owned-`.s` == reference is the external `cc` KAT in
`bench/plonky3_compare/` (`compress_from_rustcmd_kat.c`, etc.), relinked against
the owned `.s` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3EmitMain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 0. Shared helpers -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The standard `out[0..nOut-1]` store map: output word `j` to `[RDI + 8j]`. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- Build the `(immSlotMap, inLoadMap)` pair from a per-input-word constant
    oracle `constAt : idx → Option Nat` over an `nIn`-word context. A word with
    a constant becomes an immediate; every other word is loaded from `[RSI+8·idx]`.
    Argument slot `s` corresponds to input word `nIn - 1 - s`. -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

/-! ## 1. Merkle 2-to-1 compress (`plonky3_merkle_compress_rc`)

15 inputs: words `0..7` = the two 4-limb digests (runtime), words `8..14` = the
7 constants `0x9E,0x6D,0xC5,0,1,2,3` (immediates). 4 output words. -/

/-- Constant oracle for compress: words `8..14` are the 7 mixing constants. -/
def compressConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 8 ∧ idx ≤ 14 then some (Plonky3CompressEmit.constNat (idx - 8)) else none

def compressLprog : Lprog :=
  let (imm, inl) := abiMaps 15 compressConstAt
  Com.toLprogPhysAbi Plonky3CompressEmit.compressComFinal
    "plonky3_merkle_compress_rc" (fun _ => none) imm inl (stdOutStore 4)

def compressAsm : String := renderLprogAtt compressLprog

#guard (hasSub compressAsm "plonky3_merkle_compress_rc")
#guard !(hasSub compressAsm "UNHANDLED")

/-! ## 2. Merkle leaf-hash (`plonky3_merkle_hash_leaf_rc`)

8 inputs: word `0` = the field word `v` (runtime), words `1..7` = the 7
constants `G1,G2,0xA3,0,1,2,3` (immediates). 4 output words. -/

def hashLeafConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 1 ∧ idx ≤ 7 then some (Plonky3HashLeafEmit.constNat (idx - 1)) else none

def hashLeafLprog : Lprog :=
  let (imm, inl) := abiMaps 8 hashLeafConstAt
  Com.toLprogPhysAbi Plonky3HashLeafEmit.hashLeafCom
    "plonky3_merkle_hash_leaf_rc" (fun _ => none) imm inl (stdOutStore 4)

def hashLeafAsm : String := renderLprogAtt hashLeafLprog

#guard (hasSub hashLeafAsm "plonky3_merkle_hash_leaf_rc")
#guard !(hasSub hashLeafAsm "UNHANDLED")

/-! ## 3. NTT layer n=8 (`plonky3_ntt_layer8_rc`)

18 inputs: words `0..7` = the eight values (runtime), words `8..11` = the four
twiddles (runtime), words `12..17` = the six Barrett constants `MU,p,0,30,32,63`
(immediates). 8 output words. -/

def nttLayerConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 12 ∧ idx ≤ 17 then some (Plonky3NttLayerEmit.constNat (idx - 12)) else none

def nttLayerLprog : Lprog :=
  let (imm, inl) := abiMaps 18 nttLayerConstAt
  Com.toLprogPhysAbi Plonky3NttLayerEmit.layerCom
    "plonky3_ntt_layer8_rc" (fun _ => none) imm inl (stdOutStore 8)

def nttLayerAsm : String := renderLprogAtt nttLayerLprog

#guard (hasSub nttLayerAsm "plonky3_ntt_layer8_rc")
#guard !(hasSub nttLayerAsm "UNHANDLED")

/-! ## 4. FRI fold-layer + bbInv (`fri_fold_rc`, `bb_inv_rc`)

16-word context. `fri_fold_rc` runtime words `0..3`
(eval_pos,eval_neg,x,alpha); `bb_inv_rc` runtime word `0` (`a`). Both share the
constant words `4..12` = `invTwo,2,1,MU,p,0,30,32,63` (immediates; `bb_inv`
additionally treats word `4`/`5` as constants — its `bbInvInName` resolves the
same `4..12` to immediates and reads only `inp[0]`). 1 output word each. -/

def friConstAt (idx : Nat) : Option Nat :=
  if idx = 4 then some 1006632961
  else if idx = 5 then some 2
  else if idx = 6 then some 1
  else if idx = 7 then some 2290649223
  else if idx = 8 then some 2013265921
  else if idx = 9 then some 0
  else if idx = 10 then some 30
  else if idx = 11 then some 32
  else if idx = 12 then some 63
  else none

/-- `fri_fold_rc`: the four fold args `inp[0..3]` are runtime. -/
def friFoldConstAt (idx : Nat) : Option Nat := friConstAt idx

/-- `bb_inv_rc`: only `inp[0]` (`a`) is runtime; words `1..3` are unused by the
    body but `bbInvInName` resolves `1`(=invTwo no — `iOne=6`) — we mark every
    non-`0`, non-`4..12` slot as a runtime load (harmless; the body never reads
    them). To match `bbInvInName` exactly we ALSO keep `4..12` as immediates. -/
def bbInvConstAt (idx : Nat) : Option Nat := friConstAt idx

def friFoldLprog : Lprog :=
  let (imm, inl) := abiMaps 16 friFoldConstAt
  Com.toLprogPhysAbi Plonky3FriFoldEmit.friFoldCom
    "fri_fold_rc" (fun _ => none) imm inl (stdOutStore 1)

def bbInvLprog : Lprog :=
  let (imm, inl) := abiMaps 16 bbInvConstAt
  Com.toLprogPhysAbi Plonky3FriFoldEmit.bbInvCom
    "bb_inv_rc" (fun _ => none) imm inl (stdOutStore 1)

/-- Both FRI leaves combined into one `Lprog` (two `lp_funcs`), so one `.s`
    carries both `fri_fold_rc` and `bb_inv_rc`. -/
def friLprog : Lprog :=
  { friFoldLprog with
    lp_funcs := friFoldLprog.lp_funcs ++ bbInvLprog.lp_funcs }

def friAsm : String := renderLprogAtt friLprog

#guard (hasSub friAsm "fri_fold_rc")
#guard (hasSub friAsm "bb_inv_rc")
#guard !(hasSub friAsm "UNHANDLED")

/-! ## 4b. Degree-4 extension-field FRI kernels (`ext4_mul_c{0..3}_rc`, `ext4_scale_rc`)

The deg-4 binomial-extension (`x^4 = 11`) multiply coordinates and the base-field
scale (`Plonky3ExtFieldEmit`). 16-word context: the Barrett constants are at
`7..12` (immediates), `W = 11` is at word `15` (immediate), and the coords
`a0..a3, b0..b3` are runtime words `0,1,2,3,4,5,13,14`. The scale leaf uses words
`0` (x) and `1` (s) as runtime. -/

/-- Ext-field constant oracle: Barrett constants at `7..12`, `W = 11` at `15`. -/
def extConstAt (idx : Nat) : Option Nat :=
  if idx = 7 then some 2290649223
  else if idx = 8 then some 2013265921
  else if idx = 9 then some 0
  else if idx = 10 then some 30
  else if idx = 11 then some 32
  else if idx = 12 then some 63
  else if idx = 15 then some 11
  else none

def ext4MulC0Lprog : Lprog :=
  let (imm, inl) := abiMaps 16 extConstAt
  Com.toLprogPhysAbi Plonky3ExtFieldEmit.ext4MulC0Com
    "ext4_mul_c0_rc" (fun _ => none) imm inl (stdOutStore 1)
def ext4MulC1Lprog : Lprog :=
  let (imm, inl) := abiMaps 16 extConstAt
  Com.toLprogPhysAbi Plonky3ExtFieldEmit.ext4MulC1Com
    "ext4_mul_c1_rc" (fun _ => none) imm inl (stdOutStore 1)
def ext4MulC2Lprog : Lprog :=
  let (imm, inl) := abiMaps 16 extConstAt
  Com.toLprogPhysAbi Plonky3ExtFieldEmit.ext4MulC2Com
    "ext4_mul_c2_rc" (fun _ => none) imm inl (stdOutStore 1)
def ext4MulC3Lprog : Lprog :=
  let (imm, inl) := abiMaps 16 extConstAt
  Com.toLprogPhysAbi Plonky3ExtFieldEmit.ext4MulC3Com
    "ext4_mul_c3_rc" (fun _ => none) imm inl (stdOutStore 1)
def ext4ScaleLprog : Lprog :=
  let (imm, inl) := abiMaps 16 extConstAt
  Com.toLprogPhysAbi Plonky3ExtFieldEmit.ext4ScaleCom
    "ext4_scale_rc" (fun _ => none) imm inl (stdOutStore 1)

/-- Per-coordinate ext add (`eadd` coordinate): `bbAdd x y`, `x` at word `0`, `y`
    at word `1`. Needed by the `ExtensionMmcs` fold and the barycentric OOD/DEEP. -/
def ext4AddLprog : Lprog :=
  let (imm, inl) := abiMaps 16 extConstAt
  Com.toLprogPhysAbi Plonky3ExtFieldEmit.ext4AddCom
    "ext4_add_rc" (fun _ => none) imm inl (stdOutStore 1)
/-- Per-coordinate ext sub (`esub` coordinate): `bbSub x y`. -/
def ext4SubLprog : Lprog :=
  let (imm, inl) := abiMaps 16 extConstAt
  Com.toLprogPhysAbi Plonky3ExtFieldEmit.ext4SubCom
    "ext4_sub_rc" (fun _ => none) imm inl (stdOutStore 1)

/-- All seven ext-field leaves combined into one `.s` (`lp_funcs` concatenated):
    the four mul coords, scale, add, sub. -/
def extFieldLprog : Lprog :=
  { ext4MulC0Lprog with
    lp_funcs :=
      ext4MulC0Lprog.lp_funcs ++ ext4MulC1Lprog.lp_funcs
        ++ ext4MulC2Lprog.lp_funcs ++ ext4MulC3Lprog.lp_funcs
        ++ ext4ScaleLprog.lp_funcs ++ ext4AddLprog.lp_funcs
        ++ ext4SubLprog.lp_funcs }

def extFieldAsm : String := renderLprogAtt extFieldLprog

#guard (hasSub extFieldAsm "ext4_mul_c0_rc")
#guard (hasSub extFieldAsm "ext4_mul_c3_rc")
#guard (hasSub extFieldAsm "ext4_scale_rc")
theorem extField_owned_has_add :
    hasSub extFieldAsm "ext4_add_rc" = true := by native_decide
theorem extField_owned_has_sub :
    hasSub extFieldAsm "ext4_sub_rc" = true := by native_decide
#guard !(hasSub extFieldAsm "UNHANDLED")

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` files for the Plonky3 regArith kernels into the
    `bench/plonky3_compare/gen_com` harness directory (no jasminc). Each `.s`
    relinks into the existing `*_kat.c` byte-identically. -/
def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/compress_from_rustcmd_owned.s") compressAsm
  IO.FS.writeFile (dir ++ "/hash_leaf_from_rustcmd_owned.s") hashLeafAsm
  IO.FS.writeFile (dir ++ "/ntt_layer_from_rustcmd_owned.s") nttLayerAsm
  -- fri_fold_rc / bb_inv_rc: DEPLOYED front-sourced (Plonky3FriFoldFrontEmit —
  -- the field arithmetic re-sourced through translateDialectControl +
  -- cryptoDialectToJasminCom, then this same owned toLprogPhysAbi backend).
  -- The hand-Com `friAsm` above is retained only for the whole-prover /
  -- orch-loops composites that still consume `Plonky3FriFoldEmit.friFoldCom`.
  IO.FS.writeFile (dir ++ "/fri_fold_from_rustcmd_owned.s")
    Plonky3FriFoldFrontEmit.friFrontAsm
  IO.FS.writeFile (dir ++ "/ext4_from_rustcmd_owned.s") extFieldAsm
  IO.println "WROTE plonky3 owned .s (compress / hash_leaf / ntt_layer / fri_fold + bb_inv / ext4 mul+scale)"
  IO.println "  Com[jasmin] regArith -> toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3EmitMain

/-- Top-level entry point for `lake exe plonky3owned`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3EmitMain.emitMain
  return 0
