/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

@[expose] public section

set_option autoImplicit false

/-!
# Gate pins for indexed moves through `%rbp` and `%r13`

The SIB encoding of a base register whose low three bits are `5` (`%rbp`, `%r13`) carries a
zero `disp8`. `DecodeGen.decodeLinstr_loadIdx8_sib` and `decodeLinstr_storeIdx8_sib` decode
that form, so the gate `DecodePrintedAddrW.instrOKWB` and the shape computation
`DecodeGen.shapeOf` accept indexed loads and stores at every general-purpose base. This
module pins both on a load through `RBP` and a store through `R13`.

## Main results

* `#kat` pins: `instrOKWB` accepts `LOADIDX RAX ← [RBP + RCX·8]` and
  `STOREIDX [R13 + RCX·8] ← RAX`, and `shapeOf` computes a shape for each.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxBaseGateKats

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LinstrR LOperand Lcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen (shapeOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (instrOKWB)

/-- The body parameters of the pins: a `128`-byte frame, `64`-bit spill cells, the
    eight-cell save block. -/
def idxPinP : Params := { frame := 128, spillW := 64, qsaveB := 64, tbl := [] }

/-- The indexed load `LOADIDX RAX ← [RBP + RCX·8]`. -/
def ldxRbp : LinstrR := .Lopn [.reg "RAX"] "LOADIDX" [.arrIdx "RBP" "RCX" 8]

/-- The indexed store `STOREIDX [R13 + RCX·8] ← RAX` into the array `out`. -/
def stxR13 : LinstrR := .Lopn [.reg "out"] "STOREIDX" [.arrIdx "R13" "RCX" 8, .reg "RAX"]

-- the gate accepts both indexed moves
#kat instrOKWB ([] : Lcmd) idxPinP ldxRbp && instrOKWB ([] : Lcmd) idxPinP stxR13

-- the shape computation splits the bytes of both into decoded pieces
#kat (shapeOf idxPinP ldxRbp).isSome && (shapeOf idxPinP stxR13).isSome

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxBaseGateKats
