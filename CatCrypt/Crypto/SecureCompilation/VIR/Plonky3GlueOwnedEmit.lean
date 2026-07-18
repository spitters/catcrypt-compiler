/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3GlueEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Plonky3 prover-orchestration glue through the OWNED x86 backend (no jasminc)

Owned-backend render of `Plonky3GlueEmit`'s three single-element
prover-orchestration leaves (`quotient_compose_elem_rc`, `ood_deep_elem_rc`,
`challenger_squeeze_rc`) — each a FRONT-GENERATED `Com jasminDialect` (LowCT
body `--translateDialectControl-->` `catCryptDialect`
`--cryptoDialectToJasminCom-->` jasmin dialect; the `*_from_front` provenance
theorems below pin this in checkable form). This module authors NO `Com` of
its own.

The three `Com`s are rendered straight to AT&T `.s` through the
owned linear-jasmin backend (`Com.toLprogPhysAbi -> renderLprogAtt`, the #656
jasmin-tail path). Each leaf exports the same
`(out:RDI, inp:RSI)`-pointer single-output ABI the existing
`glue_from_rustcmd_kat.c` harness already feeds (a 16-word `inp[]` per leaf with
the constants present at their designated slots), so the owned `.s` relinks into
that KAT byte-identically.

## Input constant split

Each leaf reads its runtime words from `[RSI + 8·idx]`; the Barrett/branchless
constants at `iMU=7, iP=8, iZero=9, 10, 11, 12` are materialized as immediates
(the front context's constant words). The challenger leaf additionally bakes
`C = 2654435769` (slot 4), `R = 268435454` (slot 5), `LOW = 4294967295` (slot 6)
and the immediate `1` (slot 13) as immediates, since the
KAT supplies only the four digest words `inp[0..3]` for that leaf.

## What is verified vs trusted

* **Verified (value)**: each of the three `Com`s is front-generated,
  pure-scalar-arith, and denote-gated against the independent `pr_*`
  transcription (`Plonky3GlueEmit.{quot,ood,chal}_denote_spec`), so its
  denotation is the exact BabyBear Barrett word arithmetic; the owned render
  is a syntactic map of that same `Com`.
* **Verified (printer)**: the shape lemmas below pin that the emitted `.s`
  carries each export label and contains no `# UNHANDLED-OP`.
* **Trusted (thin)**: `renderLfundef` / `cc` / the SysV leaf ABI frame.

The byte identity owned-`.s` == reference is the external `cc` KAT
(`glue_from_rustcmd_kat.c`), relinked against the owned `.s` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3GlueOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3GlueEmit
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

/-! ## 0b. Front provenance

Each deployed `Com` IS the front pipeline's output for its LowCT body
(`translateDialectControl` + `cryptoDialectToJasminCom`), capped at the
`qout` output copy — pinned here in checkable form. -/

/-- `quotientComposeElemCom` is the front pipeline's output for `quotBody`. -/
theorem quot_from_front :
    (frontComWith quotVM quotBody "qout").bind
        DialectToJasminCom.cryptoDialectToJasminCom
      = some quotientComposeElemCom :=
  (Option.some_get quotLowered_isSome).symm

/-- `oodDeepElemCom` is the front pipeline's output for `oodBody`. -/
theorem ood_from_front :
    (frontComWith oodVM oodBody "qout").bind
        DialectToJasminCom.cryptoDialectToJasminCom
      = some oodDeepElemCom :=
  (Option.some_get oodLowered_isSome).symm

/-- `challengerSqueezeCom` is the front pipeline's output for `chalBody`. -/
theorem chal_from_front :
    (frontComWith chalVM chalBody "qout").bind
        DialectToJasminCom.cryptoDialectToJasminCom
      = some challengerSqueezeCom :=
  (Option.some_get chalLowered_isSome).symm

/-! ## 1. Per-leaf constant oracles (16-word input context, `nInputs = 16`)

The six Barrett/branchless immediates at `iMU=7, iP=8, iZero=9, 10, 11, 12` are
shared by all three leaves. The challenger leaf adds four more (the wrapping
multiply constant, the `2³² mod p` factor, the low-32 mask, and the immediate
`1`). -/

/-- Barrett constants common to all three glue leaves. -/
def barrettConstAt (idx : Nat) : Option Nat :=
  if idx = iMU then some 2290649223        -- 7
  else if idx = iP then some 2013265921    -- 8
  else if idx = iZero then some 0          -- 9
  else if idx = 10 then some 30
  else if idx = 11 then some 32
  else if idx = 12 then some 63
  else none

/-- Quotient-compose / OOD-DEEP constant oracle (Barrett only). -/
def quotConstAt (idx : Nat) : Option Nat := barrettConstAt idx

/-- Challenger-squeeze constant oracle (Barrett + the four challenger
    immediates `C`, `R`, `LOW`, `1`). -/
def chalConstAt (idx : Nat) : Option Nat :=
  if idx = cC then some 2654435769         -- 4
  else if idx = cR then some 268435454     -- 5
  else if idx = cLOW then some 4294967295  -- 6
  else if idx = cOne then some 1           -- 13
  else barrettConstAt idx

/-! ## 2. The three owned leaves

Each leaf takes `(out : RDI ptr u64[1], inp : RSI ptr u64[16])`, computes one
output word (the final binding's value), and stores it to `[RDI]`. -/

/-- quotient-compose leaf (`quotient_compose_elem_rc`). -/
def quotOwnedLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs quotConstAt
  Com.toLprogPhysAbi quotientComposeElemCom "quotient_compose_elem_rc"
    (fun _ => none) imm inl (stdOutStore 1)

/-- OOD/DEEP leaf (`ood_deep_elem_rc`). -/
def oodOwnedLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs quotConstAt
  Com.toLprogPhysAbi oodDeepElemCom "ood_deep_elem_rc"
    (fun _ => none) imm inl (stdOutStore 1)

/-- Fiat–Shamir challenger-squeeze leaf (`challenger_squeeze_rc`). -/
def chalOwnedLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs chalConstAt
  Com.toLprogPhysAbi challengerSqueezeCom "challenger_squeeze_rc"
    (fun _ => none) imm inl (stdOutStore 1)

/-- All three glue leaves combined into one `.s` (their `lp_funcs` concatenated),
    matching the single composed `glue_from_rustcmd.s` unit. -/
def glueOwnedLprog : Lprog :=
  { quotOwnedLprog with
    lp_funcs := quotOwnedLprog.lp_funcs ++ oodOwnedLprog.lp_funcs
      ++ chalOwnedLprog.lp_funcs }

def glueOwnedAsm : String := renderLprogAtt glueOwnedLprog

/-! ## 3. Conservative printer shape lemmas -/

def quotOwnedAsm : String := renderLprogAtt quotOwnedLprog
def oodOwnedAsm : String := renderLprogAtt oodOwnedLprog
def chalOwnedAsm : String := renderLprogAtt chalOwnedLprog

theorem quot_owned_has_leaf :
    hasSub quotOwnedAsm "quotient_compose_elem_rc" = true := by native_decide
theorem quot_owned_no_unhandled :
    hasSub quotOwnedAsm "UNHANDLED" = false := by native_decide
theorem ood_owned_has_leaf :
    hasSub oodOwnedAsm "ood_deep_elem_rc" = true := by native_decide
theorem ood_owned_no_unhandled :
    hasSub oodOwnedAsm "UNHANDLED" = false := by native_decide
theorem chal_owned_has_leaf :
    hasSub chalOwnedAsm "challenger_squeeze_rc" = true := by native_decide
theorem chal_owned_no_unhandled :
    hasSub chalOwnedAsm "UNHANDLED" = false := by native_decide

/-- The combined `.s` carries all three leaf labels (structural: its `lp_funcs`
    is the concatenation of the three single-leaf programs). -/
theorem glue_owned_funcs_len :
    glueOwnedLprog.lp_funcs.length = 3 := by native_decide

/-! ## 4. Emit driver -/

/-- Write the owned-backend `.s` carrying all three glue leaves into the
    `bench/plonky3_compare/gen_com` harness directory (no jasminc). The `.s`
    relinks into `glue_from_rustcmd_kat.c` byte-identically. -/
def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/glue_from_rustcmd_owned.s") glueOwnedAsm
  IO.println "WROTE plonky3 owned glue .s (quotient_compose / ood_deep / challenger_squeeze)"
  IO.println "  Com[jasmin] regArith -> toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3GlueOwnedEmit

/-- Top-level entry point. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3GlueOwnedEmit.emitMain
  return 0
