/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi

/-!
# The post-allocation lowering of one instruction, split into its stages

The register-allocated expansion of one virtual instruction (`PhysAbiShape.physExpand`) is
the composition of four maps:

* `immOf`: the immediate the lowering reads from the virtual instruction, before renaming:
  the shift count of a two-address `SHL`/`SHR` binop, or the index constant of a store;
* `renameOps`: the operand renaming of the allocation;
* `withBaseReload`: the reload of a memory base from its red-zone slot into `R14` in front of
  a store or a load, with the address rewritten onto `R14`;
* `lowerCore`: the lowering of the allocated, base-reloaded instruction to the x86 forms: the
  two-address binop, the legalised store, load and one-source instruction, the native shift,
  and the select and comparison with spilled operands.

`JasminLprogExport.physBodyWithStores` and `JasminLprogExport.physPositionEmit` carry inline
copies of the same expansion; `PhysAbiShape.physPositionEmit_eq_physExpand` states their
agreement with `physExpand` at a position without argument loads, output stores and calls.

## Main definitions

* `immOf`, `renameOps`, `withBaseReload`, `lowerCore`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowerCore

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The immediate the lowering of the virtual instruction `w` reads before renaming: for a
    two-address `SHL`/`SHR` binop, its count (an immediate second source, or the constant the
    oracle gives for a register second source); for a store `[d] opn [addr, val]` that is
    no two-address binop, the index constant `idxConst shiftImm addr`; `none` otherwise. -/
def immOf (shiftImm : ShiftImmOracle) (w : LinstrR) : Option Nat :=
  match w with
  | .Lopn (_ :: _) opn (_ :: s1 :: _) =>
      if isTwoAddrBinop opn then
        if stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR" then
          match s1 with
          | .imm v => some v
          | .reg n => shiftImm n
          | _ => none
        else none
      else
        match w with
        | .Lopn [_] opn' [addr, _] => if isMemStore opn' then idxConst shiftImm addr else none
        | _ => none
  | _ => none

/-- The operand renaming `rmap` of an `Lopn`; every other instruction is kept. -/
def renameOps (rmap : LOperand → LOperand) : LinstrR → LinstrR
  | .Lopn dsts opn srcs => .Lopn (dsts.map rmap) opn (srcs.map rmap)
  | other => other

/-- The base reload of an allocated instruction: for a store `[d] opn [addr, val]` that is no
    two-address binop, and for a load `[d] opn [s]` that is no native shift or rotate, the
    reload `reloadMemrefBase mbr` of the address and the instruction with the reloaded
    address; no instruction and the instruction itself otherwise. -/
def withBaseReload (mbr : String → Option String) (w : LinstrR) : List LinstrR × LinstrR :=
  match w with
  | .Lopn [d] opn [addr, val] =>
      if !isTwoAddrBinop opn && isMemStore opn then
        let (pre, addr') := reloadMemrefBase mbr addr
        (pre, .Lopn [d] opn [addr', val])
      else ([], w)
  | .Lopn [d] opn [s] =>
      if !isNativeShiftRotate opn && isMemLoad opn then
        let (pre, s') := reloadMemrefBase mbr s
        (pre, .Lopn [d] opn [s'])
      else ([], w)
  | _ => ([], w)

/-- The lowering of an allocated, base-reloaded instruction under the immediate `imm`
    (`immOf`) and the 8-byte-slot flag `u64`: the two-address lowering of a binop (by an
    immediate count when `imm` is one), the legalised store at index constant `imm`, the
    select and comparison with spilled operands (`legalizeSpillDst`), the native shift or
    rotate, the legalised load and one-source instruction; every other instruction is
    kept. -/
def lowerCore (imm : Option Nat) (u64 : Bool) (w : LinstrR) : List LinstrR :=
  match w with
  | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
      if isTwoAddrBinop opn then
        match imm with
        | some v =>
            lowerTwoAddrShiftImm d s0 v opn (if hasSuffix opn ":64" then "MOV:64" else "MOV")
        | none =>
            lowerTwoAddr d s0 s1 opn (if hasSuffix opn ":64" then "MOV:64" else "MOV")
      else
        match w with
        | .Lopn [d'] opn' [addr, val] =>
            if isMemStore opn' then
              legalizeMemStoreK imm d' addr val opn'
                (if hasSuffix opn' ":64" then "MOV:64" else "MOV")
            else legalizeSpillDst [d'] opn' [addr, val]
        | .Lopn dsts opn srcs => legalizeSpillDst dsts opn srcs
        | other => [other]
  | .Lopn [d] opn [s] =>
      if isNativeShiftRotate opn then
        lowerNativeShiftRotate d s opn (if hasSuffix opn ":64" then "MOV:64" else "MOV")
      else if isMemLoad opn then
        legalizeMemLoad d s opn (if hasSuffix opn ":64" then "MOV:64" else "MOV")
      else legalizeOneSrc u64 opn d s
  | .Lopn dsts opn srcs => [.Lopn dsts opn srcs]
  | other => [other]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowerCore
