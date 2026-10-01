/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarry
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LfundefBridge
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarry
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LfundefBridge
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode

@[expose] public section

set_option autoImplicit false

/-!
# The carry check on the decoded bytes of the Curve25519 field multiplication

`DecodeCarry.bodyOKC` is the Boolean condition under which `DecodeCarry.decSim_of_bodyOKC`
relates a flag-machine body to its machine instructions. This module evaluates it on the
field multiplication `Fe25519MulKernel.feMulBlock`: the flag-machine side is the lifted body
`Fe25519LfundefBridge.jinstrBlockToLcmd` that the byte encoder consumes, the machine side is
the decode by `LprogBytesDecode.decodeLprog` of the encoded bytes
`Fe25519LfundefBridge.feMulEncodedBytes`, and the register map is the printer's
`LprogAsmPrinter.gpReg64`. The checked block is the fold of the reduction: the flag reset
`XOR`, four register `MULX` against the decoded VEX `mulx` with the implicit source `%rdx`,
the interleaved `ADCX`/`ADOX` chains, and the closing `ADC` that reads the carry flag of the
`ADCX` chain across the flag-quiet `MULX`. The schoolbook product is checked by
`DecodeCarry.bodyOKCK` with the eight input words as cells: the `LOAD` of a multiplier word
against the decoded `mov off(%rcx), %rdx`, and `MULXMEM` against the decoded memory-source
`mulx off(%rsi)`. The checks are `#kat`s evaluated by the compiled evaluator.

## Main definitions

* `feMulOps`, `feMulDecoded` — the lifted body and the decoded machine instructions.
* `gpNames` — the sixteen general-purpose register names of the lifted body.
* `foldOps`, `foldJs` — the fold block on both sides.
* `quotOps`, `quotJs` — the head of the quotient estimate on both sides.
* `feMulCells`, `schoolOps`, `schoolJs` — the input cells and the schoolbook product on both
  sides.

## Main results

* `bodyOKC` accepts the fold block and the head of the quotient estimate, and rejects the fold
  without its flag reset and a `MULX` with exchanged destinations (`#kat` pins).
* `bodyOKCK` accepts the schoolbook product (instructions `0` to `55`) and rejects a
  memory-source `mulx` at the wrong offset (`#kat` pins).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarryKats

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (gpReg64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LfundefBridge
  (jinstrBlockToLcmd feMulEncodedBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim (injB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarry (bodyOKC bodyOKCK)

/-- The lifted body of the field multiplication, each instruction with the register tag. -/
def feMulOps : List LinstrRM :=
  (jinstrBlockToLcmd Fe25519MulKernel.feMulAlloc Fe25519MulKernel.feMulBlock).map
    fun li => (li.li_i, MemTag.reg none)

/-- The straight-line machine instructions decoded from the encoded body. -/
def feMulDecoded : List (JInstr 64) :=
  ((decodeLprog feMulEncodedBytes).getD []).filterMap fun
    | .op i => some i
    | _ => none

/-- The sixteen general-purpose register names of the lifted body. -/
def gpNames : List String :=
  ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP",
    "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"]

/-- The fold block of the lifted body: instructions `67` to `79`. -/
def foldOps : List LinstrRM := (feMulOps.drop 67).take 13

/-- The fold block of the decoded instructions, one machine instruction per instruction. -/
def foldJs : List (List (JInstr 64)) := ((feMulDecoded.drop 67).take 13).map ([·])

/-- The head of the quotient estimate in the lifted body: instructions `56` to `60`
    (`MOV` of `38`, `MULX`, `ADD`, `ADC`, a two-source register `MOV`). -/
def quotOps : List LinstrRM := (feMulOps.drop 56).take 5

/-- The head of the quotient estimate in the decoded instructions. -/
def quotJs : List (List (JInstr 64)) := ((feMulDecoded.drop 56).take 5).map ([·])

/-- The cells of the field multiplication: the four words of the multiplicand at `%rsi` and
    of the multiplier at `%rcx`, under their lifted names `mem.<B>.<off>`. -/
def feMulCells : List (String × String × Int) :=
  [("mem.RSI.0", "%rsi", 0), ("mem.RSI.8", "%rsi", 8), ("mem.RSI.16", "%rsi", 16),
    ("mem.RSI.24", "%rsi", 24), ("mem.RCX.0", "%rcx", 0), ("mem.RCX.8", "%rcx", 8),
    ("mem.RCX.16", "%rcx", 16), ("mem.RCX.24", "%rcx", 24)]

/-- The schoolbook product in the lifted body: instructions `0` to `55`. -/
def schoolOps : List LinstrRM := feMulOps.take 56

/-- The schoolbook product in the decoded instructions. -/
def schoolJs : List (List (JInstr 64)) := (feMulDecoded.take 56).map ([·])

-- the encoded body decodes, one machine instruction per lifted instruction
#kat (decodeLprog feMulEncodedBytes).isSome && feMulDecoded.length == 95

-- the register map is injective on the register names
#kat injB gpReg64 gpNames

-- the fold block is accepted from no live flag
#kat bodyOKC gpReg64 gpNames (false, false) foldOps foldJs

-- without the flag reset, the first `ADOX` reads an overflow flag that is not live
#kat !bodyOKC gpReg64 gpNames (false, false) (foldOps.drop 1) (foldJs.drop 1)

-- a decoded `mulx` with its two destinations exchanged is rejected
#kat !bodyOKC gpReg64 gpNames (false, false) foldOps
  (foldJs.set 2 [.mulx "%r11" "%r12" (.reg "%rdx") (.reg "%rbx")])

-- the head of the quotient estimate: the immediate and register two-source copies, a
-- `MULX`, and an `ADD`, `ADC` carry chain
#kat bodyOKC gpReg64 gpNames (false, false) quotOps quotJs

-- the schoolbook product: cell loads of the multiplier, memory-source `MULX` on the
-- multiplicand cells, and the `ADCX`/`ADOX` chains, from no live flag
#kat bodyOKCK gpReg64 (gpNames ++ feMulCells.map (·.1)) feMulCells (false, false)
  schoolOps schoolJs

-- the cell names have distinct registers
#kat injB gpReg64 (gpNames ++ feMulCells.map (·.1))

-- a memory-source `mulx` reading a word that is not the cell's is rejected
#kat !bodyOKCK gpReg64 (gpNames ++ feMulCells.map (·.1)) feMulCells (false, false)
  schoolOps (schoolJs.set 3 [.mulxMem "%r8" "%r9" (.reg "%rdx") "%rsi" 8])

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarryKats
