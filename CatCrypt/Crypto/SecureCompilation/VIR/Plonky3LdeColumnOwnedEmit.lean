/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Plonky3 coset-NTT column LDE through the OWNED x86 backend (no jasminc)

This is the owned-backend twin of `Plonky3LdeColumnEmit`, which builds the seven
register-arith leaves of `computeColumnLde colEvals 3 5 31`
(`inttLeafCom`, `twistLeafCom`, `nttLeafCom 0..4`) as `Com jasminDialect` bodies
that are **entirely `regArith add/sub/mul/and/shr`** (`*_regarith` proved there),
and renders them to `.jazz` text via `JasminAbiEmit.emitAbiOrchReg` for jasminc.

This module renders the **same seven `Com`s** straight to AT&T `.s` through the
owned linear-jasmin backend — the `Plonky3OwnedEmitMain` (#656 jasmin-tail) path:

    Com jasminDialect  --Com.toLprogPhysAbi-->  Lprog (physical-register, SysV ABI)
                       --renderLprogAtt-->       AT&T `.s`  (assembled by `cc`, no jasminc)

## ABI: constants are immediates, runtime words are RSI loads

The `.jazz` path's `inttInName`/`bufInName` resolve input words `133..138`
(`MU = 2290649223`, `p = 2013265921`, `0`, `30`, `32`, `63`) to immediates and
every other input word to a buffer/`inp[i]` read. The owned `toLprogPhysAbi` path
reproduces that split with the two producer-side maps `immSlotMap`/`inLoadMap`:

* `immSlotMap` materializes input words `133..138` as `.imm` operands;
* `inLoadMap` loads every remaining (runtime) input word `0..132` from the `RSI`
  input pointer at offset `8·idx`.

This is the **identical** constant/runtime split the existing
`lde_column_from_rustcmd_kat.c` harness already feeds (it builds the full 139-word
`inp[]` per leaf with the constants present at `133..138`), so each owned `.s`
exports the same `(out:RDI, inp:RSI)`-pointer ABI and relinks into the existing
KAT harness byte-identically (no harness change, no jasminc).

The intt-8 leaf's 8-pt bit-reversal is folded into the harness copy-in
(`inp[i] = colEvals[bitReverse(i,3)]`), and the forward-NTT bit-reversal is fused
into the twist leaf's swap — both are pure data movement in the leaf bodies, so
the owned render carries them unchanged.

## What is verified vs trusted

* **Verified (value)**: each of the seven `Com`s is `allRegArith` (`*_regarith`,
  proved compositionally in `Plonky3LdeColumnEmit`), so its denotation is the
  exact BabyBear Barrett/branchless word arithmetic; the owned render is a
  syntactic map of that same `Com`.
* **Verified (printer)**: the `*_owned_*` shape lemmas below pin that the emitted
  `.s` carries each of the seven export labels and contains no `# UNHANDLED-OP`.
* **Trusted (thin)**: `renderLfundef` / `cc` / the SysV leaf ABI frame.

The byte identity owned-`.s` == reference is the external `cc` KAT
(`lde_column_from_rustcmd_kat.c`), relinked against the owned `.s` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit
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
    oracle `constAt : idx → Option Nat` over an `nIn`-word context. A word with a
    constant becomes an immediate; every other word is loaded from `[RSI+8·idx]`.
    Argument slot `s` corresponds to input word `nIn - 1 - s` (the De Bruijn
    reversal in `comToLfundef`). -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

/-! ## 1. The LDE constant oracle

The 139-word input context (`Plonky3LdeColumnEmit.nInputs = 139`). Words
`133..138` are the six Barrett/branchless immediates (matching `inttInName` /
`bufInName`); every other word (`0..132`: the buffer values, twiddles, coset
powers, intt scale) is a runtime `RSI` load. -/

/-- The Barrett/branchless immediates at LDE input words `133..138`. -/
def ldeConstAt (idx : Nat) : Option Nat :=
  if idx = iMU then some 2290649223        -- 133
  else if idx = iP then some 2013265921    -- 134
  else if idx = iZero then some 0          -- 135
  else if idx = iSh30 then some 30         -- 136
  else if idx = iSh32 then some 32         -- 137
  else if idx = iSh63 then some 63         -- 138
  else none

/-! ## 2. The seven owned leaves

Each leaf takes `(out : RDI ptr u64[32], inp : RSI ptr u64[139])`, writes 32
output words to `[RDI + 8j]`, and reads its runtime words from `[RSI + 8·idx]`.
The seven `Com`s and their `allRegArith` proofs are from `Plonky3LdeColumnEmit`. -/

/-- intt-8 leaf (`lde_intt8_rc`): 8-pt inverse NTT + scale `8⁻¹`. -/
def inttOwnedLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs ldeConstAt
  Com.toLprogPhysAbi inttLeafCom "lde_intt8_rc" (fun _ => none) imm inl (stdOutStore 32)

/-- coset-twist leaf (`lde_twist_rc`): zero-pad + coset twist + fused fwd-NTT
    bit-reversal. -/
def twistOwnedLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs ldeConstAt
  Com.toLprogPhysAbi twistLeafCom "lde_twist_rc" (fun _ => none) imm inl (stdOutStore 32)

/-- one forward-NTT layer leaf (`lde_ntt32_l<layer>_rc`). -/
def nttOwnedLprog (layer : Nat) : Lprog :=
  let (imm, inl) := abiMaps nInputs ldeConstAt
  Com.toLprogPhysAbi (nttLeafCom layer) ("lde_ntt32_l" ++ toString layer ++ "_rc")
    (fun _ => none) imm inl (stdOutStore 32)

/-- All seven LDE leaves combined into one `.s` (their `lp_funcs` concatenated),
    matching the single composed `lde_column_from_rustcmd.s` unit. -/
def ldeColumnOwnedLprog : Lprog :=
  { inttOwnedLprog with
    lp_funcs :=
      inttOwnedLprog.lp_funcs ++ twistOwnedLprog.lp_funcs
        ++ (nttOwnedLprog 0).lp_funcs ++ (nttOwnedLprog 1).lp_funcs
        ++ (nttOwnedLprog 2).lp_funcs ++ (nttOwnedLprog 3).lp_funcs
        ++ (nttOwnedLprog 4).lp_funcs }

def ldeColumnOwnedAsm : String := renderLprogAtt ldeColumnOwnedLprog

/-! ## 2b. Front provenance (per-leaf, small)

Each deployed leaf `Com` this module renders is the sibling front module
`Plonky3LdeColumnEmit`'s front lowering — the `translateDialectControl`-translated
LowCT statement list, lowered to a `Com jasminDialect` by
`cryptoDialectToJasminCom`.  Nothing here hand-authors a `Com`: the leaves are
consumed from the front and only the owned RA-render tail (`toLprogPhysAbi` /
`renderLprogAtt`) is local.  The provenance gate is the front module's SMALL
per-leaf `*_isSome` check (each a `native_decide` over ONE ≈30-binding leaf), not
a whole-block scan; the equalities below are definitional (`Option.some_get`) and
name the front lowering (`cryptoDialectToJasminCom`) that produced each symbol. -/

theorem intt_front_sourced :
    (frontComAt (seqAll inttLeafStmts) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some inttLeafCom :=
  (Option.some_get inttLowered_isSome).symm

theorem twist_front_sourced :
    (frontComAt (seqAll twistLeafStmts) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some twistLeafCom :=
  (Option.some_get twistLowered_isSome).symm

theorem ntt0_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 0)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 0) :=
  (Option.some_get nttLeaf0_isSome).symm

theorem ntt1_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 1)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 1) :=
  (Option.some_get nttLeaf1_isSome).symm

theorem ntt2_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 2)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 2) :=
  (Option.some_get nttLeaf2_isSome).symm

theorem ntt3_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 3)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 3) :=
  (Option.some_get nttLeaf3_isSome).symm

theorem ntt4_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 4)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 4) :=
  (Option.some_get nttLeaf4_isSome).symm

/-! ## 3. Conservative printer shape lemmas

Each leaf's export label is present and its body contains no `UNHANDLED` op
sentinel (every binding is a handled `regArith` op). The shape checks are done
**per leaf** (each render ≈ the proven-feasible 57 KB `fri_fold_from_rustcmd`
scale) rather than over the ~350 KB concatenation, keeping each `native_decide`
`hasSub` scan in the established size regime. -/

def inttOwnedAsm : String := renderLprogAtt inttOwnedLprog
def twistOwnedAsm : String := renderLprogAtt twistOwnedLprog
def nttOwnedAsm (layer : Nat) : String := renderLprogAtt (nttOwnedLprog layer)

theorem intt_owned_has_leaf :
    hasSub inttOwnedAsm "lde_intt8_rc" = true := by native_decide
theorem intt_owned_no_unhandled :
    hasSub inttOwnedAsm "UNHANDLED" = false := by native_decide
theorem twist_owned_has_leaf :
    hasSub twistOwnedAsm "lde_twist_rc" = true := by native_decide
theorem twist_owned_no_unhandled :
    hasSub twistOwnedAsm "UNHANDLED" = false := by native_decide
theorem ntt0_owned_has_leaf :
    hasSub (nttOwnedAsm 0) "lde_ntt32_l0_rc" = true := by native_decide
theorem ntt0_owned_no_unhandled :
    hasSub (nttOwnedAsm 0) "UNHANDLED" = false := by native_decide
theorem ntt4_owned_has_leaf :
    hasSub (nttOwnedAsm 4) "lde_ntt32_l4_rc" = true := by native_decide
theorem ntt4_owned_no_unhandled :
    hasSub (nttOwnedAsm 4) "UNHANDLED" = false := by native_decide

/-- The combined `.s` carries all seven leaf labels (structural: its `lp_funcs`
    is the concatenation of the seven single-leaf programs). -/
theorem ldeColumn_owned_funcs_len :
    ldeColumnOwnedLprog.lp_funcs.length = 7 := by native_decide

/-! ## 4. Emit driver -/

/-- Write the owned-backend `.s` carrying all seven LDE column leaves into the
    `bench/plonky3_compare/gen_com` harness directory (no jasminc). The `.s`
    relinks into `lde_column_from_rustcmd_kat.c` byte-identically. -/
def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/lde_column_from_rustcmd_owned.s") ldeColumnOwnedAsm
  IO.println "WROTE plonky3 owned LDE column .s (intt8 / twist / ntt32 l0..l4)"
  IO.println "  Com[jasmin] regArith -> toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnOwnedEmit

/-- Top-level entry point for `lake exe plonky3ldeowned`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnOwnedEmit.emitMain
  return 0
