/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

@[expose] public section

set_option autoImplicit false

/-!
# Scalar-accumulator looped ABI export (`ComL.toLfundefPhysAbiScalarAcc`)

The committed looped 2-pointer-ABI export `ComL.toLfundefPhysAbi` structurally
assumes the loop's `init` accumulator IS the output array: it derives the
out-array base name from `resolveVar init` (`ComL.loopArgBaseNames`), aliases
the accumulator register onto that name, and keys the SIB-base qsave-reload map
as `(init, invs)` = `(out, ins)` zipped positionally onto `abiArgs`.

The GMP mpn carry family (`mpn_add_n`/`mpn_sub_n`, task #20) breaks that
assumption: the loop-carried accumulator is a **scalar** (the carry/borrow bit,
riding a `.reg 64` — the half-add-split prototype
`X86Backend/MpnAddCarryFrontPrototype.lean`), and the output array is a loop
**invariant** written through `RArrStore`/`STOREIDX`. Fed to `toLfundefPhysAbi`,
the scalar seed would be treated as the out-array base (aliased, mapped to
`RDI`) and the real out array would be zipped one register too far — wrong
bytes by construction.

This module adds the **additive** scalar-accumulator variant. Deltas versus
`ComL.toLfundefPhysAbi` (everything else — prologue, argument materialization,
per-access SIB-base qsave reload, callee-saved restore — is shared verbatim):

1. **No accumulator alias.** The accumulator stays the scalar loop-carried
   register (`regName nArgs`); the linear-scan RA homes it like any loop
   temporary (the `loopSmokeRtProg`/`loopSmokeRt3Prog` scalar-acc smoke path).
2. **Positional reload map.** The memref-base qsave-reload map is keyed
   positionally over ALL `abiArgs` (`argName j ↦ qsave(abiArgs[j])`, the
   `comToLfundefPhysAbi` convention) instead of being derived from
   `(init, invs)`. The caller therefore lays out `Γ` so that program-root arg
   slot `j` is the `j`-th SysV argument (the natural GMP order:
   `a0 = rp → RDI, a1 = ap → RSI, a2 = bp → RDX, a3 = n → RCX`). Entries for
   scalar arguments are inert (a scalar name never appears as a SIB base;
   the LIVEPIN keeps its physical register distinct from the array bases).
3. **Scalar return in `RAX`.** The accumulator's final physical home is moved
   into the SysV return register before the callee-saved restore
   (`MOVQ RAX, phys(acc)`), so the kernel returns the carry/borrow limb —
   GMP's `__gmpn_add_n`/`__gmpn_sub_n` return-value ABI.

**Carry-in seed plumbing (documented choice: MOV-0 prologue, no 5th argument).**
GMP's `mpn_add_n(rp, ap, bp, n)` has no carry-in argument. Rather than extend
the ABI with a trailing `cy0` register (which a 4-argument C caller would leave
as garbage), the accumulator seed variable is placed at an arg slot BEYOND
`abiArgs` (slot 4 of a 4-register signature) and covered by the export's
`immSlotMap` (`4 ↦ 0`), so `resolveVar` renders the seed as `.imm 0` and the
loop prologue is `MOV acc, #0` — no fifth SysV register is ever read. A
carry-propagation caller that DOES want a live carry-in can instead pass a
5-register `abiArgs` (`… ++ ["R8"]`) and omit the `immSlotMap` entry.

The variant is strictly additive: `ComL.toLfundefPhysAbi` and every deployed
kernel through it are untouched.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The scalar-accumulator looped physical ABI export: a `ComL` whose loop node
    carries a **scalar** accumulator (`init : .reg 64` — a carry/borrow bit, a
    fold value) while the output array (if any) is a loop **invariant** written
    via `STOREIDX`. Argument layout contract: program-root arg slot `j` is the
    `j`-th entry of `abiArgs` (`argName j ↦ abiArgs[j]`); arg slots `≥
    abiArgs.length` must be immediate-substituted via `immSlotMap` (the MOV-imm
    accumulator seed). The accumulator's final value is returned in `RAX`.
    See the module docstring for the delta versus `ComL.toLfundefPhysAbi`. -/
def ComL.toLfundefPhysAbiScalarAcc {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI", "RDX", "RCX"])
    (abiTyin : List Nat := [64, 64, 64, 64]) :
    Lfundef :=
  let virt0 := ComL.toLfundef c immSlotMap
  -- Argument-liveness pin (same rationale as `comToLfundefPhysAbi`, ≥3-argument
  -- signatures): the scalar count/seed args are read once, early, so without
  -- the pin the RA can coalesce a scalar arg onto an array base's register,
  -- making the register-keyed positional reload map ambiguous. Pins only the
  -- `abiArgs`-covered slots (an imm-substituted seed slot has no register).
  let livePin : Lcmd :=
    if abiArgs.length ≥ 3 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  -- NO accumulator alias (delta 1): the accumulator is a scalar fold value, not
  -- an array pointer. `canonicalizeMemrefThread` still collapses any
  -- `STOREIDX`-result thread onto its SIB base (identity when nothing reads the
  -- store result).
  let body1 := livePin ++ canonicalizeMemrefThread virt0.lfd_body
  let virt := { virt0 with lfd_body := body1 }
  let tbl := physTableOut virt.lfd_body []
  -- Extra qsave slots for the 3rd+ SysV registers (RDX/RCX/R8/R9), as in the
  -- array-accumulator looped export.
  let extraInputSaves : Lcmd :=
    (abiArgs.drop 2).filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none)
  let prologue := buildPrologue virt tbl (fun _ => none) ++ extraInputSaves
  let argMat := buildArgPtrMaterialize virt tbl abiArgs (fun _ => none)
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  -- Positional SIB-base reload map (delta 2): each ABI argument `j` maps its
  -- RA-assigned physical register to its own qsave slot. Scalar-argument
  -- entries are inert (never a SIB base; LIVEPIN keeps registers distinct).
  let memrefBaseReload : String → Option String :=
    let pairs : List (String × String) :=
      (abiArgs.zipIdx).filterMap (fun ⟨abiReg, j⟩ =>
        match abiSaveOfExt abiReg with
        | some saveName =>
            some (physNameForBody virt.lfd_body tbl (argName j), saveName)
        | none => none)
    fun base => (pairs.find? (fun p => p.1 == base)).map Prod.snd
  let bodyWithReload := (physBodyWithStores shiftImm' virt.lfd_body
    (fun _ => none) reloadScratch2 [] reloadScratch2 0 memrefBaseReload).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  -- Scalar return materialization (delta 3): move the accumulator's final
  -- physical home into `RAX` before the callee-saved restore. `virt.lfd_res`
  -- is `[comLRetReg …]` = the loop accumulator register for a
  -- `forLoopNRt … (.ret .here)` program. MOVQ (64-bit): the carry limb is a
  -- full word (an untagged MOV would render `movl` and truncate).
  let retMat : Lcmd :=
    match virt.lfd_res.head? with
    | some rn =>
        let phys := physNameForBody virt.lfd_body tbl rn
        if phys == sysvRetReg then []
        else [⟨0, .Lopn [.reg sysvRetReg] "MOVQ" [.reg phys]⟩]
    | none => []
  let bodyWithRestore := insertEpilogue bodyWithReload (retMat ++ calleeSaveRestoreEpilogue)
  { virt with
    lfd_body := prologue ++ argMat ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := [sysvRetReg]
    lfd_tyout := [64] }

/-- Export a scalar-accumulator looped `ComL` to a physical `Lprog` (the GMP
    `mpn_add_n`/`mpn_sub_n` shape). See `ComL.toLfundefPhysAbiScalarAcc`. -/
def ComL.toLprogPhysAbiScalarAcc {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI", "RDX", "RCX"])
    (abiTyin : List Nat := [64, 64, 64, 64]) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, ComL.toLfundefPhysAbiScalarAcc c shiftImm immSlotMap
                 abiArgs abiTyin)] }

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
