/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImgGateOfLegal
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ImgGateOfLegal
public import CatCryptCore.Tactics.KatGuard

@[expose] public section

set_option autoImplicit false

/-!
# The legal forms the printed-class gate refuses, by origin and by the support they lack

## The table

For each family of legal forms of `GateOfLegal` that the printed-class gate `instrOKWB`
refuses, and for three families `instrOKWB` accepts that `ImgGateOfLegal.ImgForm` does not
list, the columns are:

* (a) whether the region route emits it, with the source construct;
* (b) whether the decoder reads its bytes (`DecodeGen.shapeOf` at the parameters of its
  one-instruction body is defined) and whether the address machine steps it (`fstepA` from a
  state with every name at the instruction's width, or `stepA` for a control transfer);
* (c) the extension it takes and its estimated size in plan units.

Rows are ordered by (a), then by (c).

| family | (a) region route | decoder | step | (c) extension |
|---|---|---|---|---|
| `SAR:64 D, [D, #k]` | yes: `sarImm 64 k` (`straightOpsMem` prints it by `shiftLinstr`) | yes | yes | local: a classify arm, its ok predicate, pieces and one simulation case beside the `SHL:64`/`SHR:64` immediate arm; 0.25 |
| `SETE:64 D, [A, #v]`, `CASTW_<w>_<w'>` | yes: `cmpImm .eq 64 v`, `castW w w'` | yes | yes | none at either gate: `instrOKWB` and `instrGateBW` accept both; `ImgForm` lacks the two constructors; 0.1 |
| `LEA:64 R14, (B, R15, 8)` | yes: `legalizeMemStore` on a store whose index and value are both spilled, followed by `MOV:64 mem.R14.0, R15` | yes | yes | local: a classify arm for the indexed address and the cell store under `MOV:64` (`refused_movToCell`); 0.5 |
| indexed access with base `RBP` | yes: `RBP` is in the allocation pool `gpRegNames`, so an array base may be placed in it | no | yes | decoder: the base `RBP` takes the `mod = 01`, `disp8 = 0` encoding, which the decoder does not read; then the existing indexed-access case; 0.5-1 |
| strides other than `8` | yes: `stackLoad w n` and `stackStore w n` at `w < 64` give the stride `w / 8` | no | steps, at the wrong width | decoder and semantics: `tagA` tags every `LOADIDX`/`STOREIDX` at width `64`, so `fstepA` reads eight bytes at stride `4`; the tag, the narrow read and write, the decoder arms and the simulation case are new; 1-1.5 |
| 32-bit forms (`ADD`, `MOV`, `SETE`, ... untagged) | yes: every general-purpose operation of `opMemB` at a width other than `64` (`withWidthTag`) | no | yes, at width `32` | decoder and simulation: the decoder reads no operand-size-32 form; `ACorrW` relates 32-bit names (`NarrowCell`), so the simulation cases follow the cast arm; 1.5-2 |
| `SHR:k:64`, `SHL:k:64` | no: `straightOpsMem` prints `shrImm`/`shlImm` by `shiftLinstr` (count as an operand) | yes | yes | none at either gate; `ImgForm` lacks the constructor; 0.1 |
| `MULX:64 [L, H], [S]` | no: the fusion `fuseMulHiLprog` prints the untagged `MULX` | yes | yes | local: `normA` already reads `MULX` as `MULX:64`; an alias in `classifyA`; 0.1 |
| `SAR:k:64` | no: as for `SHR:k:64` | yes | yes | local: the `tagShift` arm at base `SAR`; 0.25 |
| `NEG:64` | no: no operation of `opMemB` prints `NEG` | yes | yes | local; 0.25 |
| `RSP` as a data operand | no: `RSP` is outside `gpRegNames` | yes | yes | not local: `ACorrW` pins `RSP` to the frame base `rsp`, so reading it as data needs an invariant on its value; 0.5 |
| `ADOXHI:64` | no: `addCarryHi` prints `ADCXHI` and no operation prints `ADOX`/`ADOXHI` | no | no | decoder and semantics: the overflow-flag chain; 1 |
| `Lgoto` | no: `exportR` emits no `gotoI` (the frame of `ifThenElse` jumps by a constant and the loop guard) | no | no | decoder (`jmp`), a `stepA` arm and a simulation case; 1 |
| `Lcall` | no on a call-free body; a calling body is checked by `calleeCtB`, outside `printedAddrWB` | yes | no | semantics of a call on the address machine; 2 or more |

Columns "decoder" and "step" and the values of both gates are evaluated below. Column (a) is evaluated
for the emitting constructs; the "no" entries of column (a) are read off the definitions
`opMemB`, `straightOpsMem`, `exportR`, `physPositionEmit` and `fuseMulHiLprog`, not proved
over the lowering image.

## Main definitions

* `stW w` — the address state with every name at width `w` holding `5`.
* `probeK w i` — the decoder shape of `i` and its address step from `stW w`, checked by
  kernel reduction.
* `probe w i` — `probeK w i` with `instrOKWB` and `instrGateBW` on `i` in its
  one-instruction body, checked by `#kat` (the kernel does not reduce `instrGateBW` on
  these instructions).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GateWExtDiag

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (shiftLinstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (instrOKWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (instrGateBW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal (wb)

/-- The address state with every name at width `w` holding `5`, and the zero memory. -/
def stW (w : Nat) : LstateA :=
  { reg := { lvm := fun _ => ⟨w, BitVec.ofNat w 5⟩ }, mem := fun _ => 0 }

/-- The decoder shape of `i` at the parameters of its one-instruction body, the address step
    of `i` at its tag from `stW w`, and the gates `instrOKWB` and `instrGateBW` on `i` in that
    body. -/
def probe (w : Nat) (i : LinstrR) : Bool × Bool × Bool × Bool :=
  ((DecodeGen.shapeOf (Params.ofBody (wb i)) i).isSome,
   (fstepA (fun _ => none) (normA i, tagA i) (stW w) false).isSome,
   instrOKWB (wb i) (Params.ofBody (wb i)) i,
   instrGateBW (fun _ => none) (fun _ => none) (wb i) 0 i)

/-- The decoder shape of `i` at the parameters of its one-instruction body and the address
    step of `i` at its tag from `stW w`. -/
def probeK (w : Nat) (i : LinstrR) : Bool × Bool :=
  ((DecodeGen.shapeOf (Params.ofBody (wb i)) i).isSome,
   (fstepA (fun _ => none) (normA i, tagA i) (stW w) false).isSome)

/-! ## Column (a): the emitting constructs -/

example : opMemB (.sarImm 64 3) = true ∧
    shiftLinstr "SAR" 64 "D" (.reg "A") 3 = .Lopn [.reg "D"] "SAR:64" [.reg "A", .imm 3] :=
  ⟨rfl, rfl⟩

example : opMemB (.cmpImm .eq 64 5) = true ∧
    opToLinstrR (.cmpImm .eq 64 5) "D" [.reg "A"] = .Lopn [.reg "D"] "SETE:64" [.reg "A", .imm 5] :=
  ⟨rfl, rfl⟩

example : opMemB (.castW 64 32) = true ∧
    opToLinstrR (.castW 64 32) "D" [.reg "A"] = .Lopn [.reg "D"] "CASTW_64_32" [.reg "A"] :=
  ⟨rfl, rfl⟩

#kat legalizeMemStore (.reg "D") (.arrIdx "RBX" "k.1" 8) (.reg "k.2") "STOREIDX" "MOV:64"
  == [.Lopn [.reg "R15"] "MOV:64" [.reg "k.1"],
      .Lopn [.reg "R14"] "LEA:64" [.arrIdx "RBX" "R15" 8],
      .Lopn [.reg "R15"] "MOV:64" [.reg "k.2"],
      .Lopn [.reg "mem.R14.0"] "MOV:64" [.reg "R15"]]

example : "RBP" ∈ gpRegNames := by decide

example : opMemB (.stackLoad 32 4) = true ∧
    opToLinstrR (.stackLoad 32 4) "D" [.reg "A", .reg "I"]
      = .Lopn [.reg "D"] "LOADIDX" [.arrIdx "A" "I" 4] :=
  ⟨rfl, rfl⟩

example : opMemB (.regArith .add 32) = true ∧
    opToLinstrR (.regArith .add 32) "D" [.reg "A", .reg "B"]
      = .Lopn [.reg "D"] "ADD" [.reg "A", .reg "B"] :=
  ⟨rfl, rfl⟩

example : "RSP" ∉ gpRegNames := by decide

/-! ## Column (b): the decoder and the address step -/

example : probeK 64 (.Lopn [.reg "RAX"] "SAR:64" [.reg "RAX", .imm 3]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "SETE:64" [.reg "RCX", .imm 5]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "CASTW_64_32" [.reg "RCX"]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "LEA:64" [.arrIdx "RBX" "RCX" 8]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "LOADIDX" [.arrIdx "RBP" "RCX" 8]) = (false, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "LOADIDX" [.arrIdx "RBX" "RCX" 4]) = (false, true) := by
  decide +kernel

example : probeK 32 (.Lopn [.reg "RAX"] "ADD" [.reg "RAX", .reg "RCX"]) = (false, true) := by
  decide +kernel

example : probeK 32 (.Lopn [.reg "RAX"] "MOV" [.reg "RCX"]) = (false, true) := by
  decide +kernel

example : probeK 32 (.Lopn [.reg "RAX"] "SETE" [.reg "RCX", .reg "RDX"]) = (false, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "SHR:5:64" [.reg "RCX"]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX", .reg "RCX"] "MULX:64" [.reg "RDX"]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "SAR:7:64" [.reg "RCX"]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "NEG:64" [.reg "RCX"]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RSP"]) = (true, true) := by
  decide +kernel

example : probeK 64 (.Lopn [.reg "RAX"] "ADOXHI:64" [.reg "RAX", .reg "RCX", .reg "RDX"])
    = (false, false) := by
  decide +kernel

/-! ## The values of the gates

`instrOKWB` refuses every family below except `SETE:64` by an immediate, the cast and
`SHR:k:64`, which both gates accept; `instrGateBW` refuses the base `RBP`, the stride `4` and
`ADOXHI:64`. -/

#kat probe 64 (.Lopn [.reg "RAX"] "SAR:64" [.reg "RAX", .imm 3]) == (true, true, false, true)
#kat probe 64 (.Lopn [.reg "RAX"] "SETE:64" [.reg "RCX", .imm 5]) == (true, true, true, true)
#kat probe 64 (.Lopn [.reg "RAX"] "CASTW_64_32" [.reg "RCX"]) == (true, true, true, true)
#kat probe 64 (.Lopn [.reg "RAX"] "LEA:64" [.arrIdx "RBX" "RCX" 8]) == (true, true, false, true)
#kat probe 64 (.Lopn [.reg "RAX"] "LOADIDX" [.arrIdx "RBP" "RCX" 8]) == (false, true, false, false)
#kat probe 64 (.Lopn [.reg "RAX"] "LOADIDX" [.arrIdx "RBX" "RCX" 4]) == (false, true, false, false)
#kat probe 32 (.Lopn [.reg "RAX"] "ADD" [.reg "RAX", .reg "RCX"]) == (false, true, false, true)
#kat probe 32 (.Lopn [.reg "RAX"] "MOV" [.reg "RCX"]) == (false, true, false, true)
#kat probe 32 (.Lopn [.reg "RAX"] "SETE" [.reg "RCX", .reg "RDX"]) == (false, true, false, true)
#kat probe 64 (.Lopn [.reg "RAX"] "SHR:5:64" [.reg "RCX"]) == (true, true, true, true)
#kat probe 64 (.Lopn [.reg "RAX", .reg "RCX"] "MULX:64" [.reg "RDX"]) == (true, true, false, true)
#kat probe 64 (.Lopn [.reg "RAX"] "SAR:7:64" [.reg "RCX"]) == (true, true, false, true)
#kat probe 64 (.Lopn [.reg "RAX"] "NEG:64" [.reg "RCX"]) == (true, true, false, true)
#kat probe 64 (.Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RSP"]) == (true, true, false, true)
#kat probe 64 (.Lopn [.reg "RAX"] "ADOXHI:64" [.reg "RAX", .reg "RCX", .reg "RDX"])
  == (false, false, false, false)

/-! ## The control transfers -/

example : (DecodeGen.shapeOf (Params.ofBody (wb (.Lgoto ("", 1)))) (.Lgoto ("", 1))).isSome = false ∧
    (stepA (fun _ => none) (wb (.Lgoto ("", 1))) (stW 64) false).isSome = false := by
  decide +kernel

example : (DecodeGen.shapeOf (Params.ofBody (wb (.Lcall none ("f", 1)))) (.Lcall none ("f", 1))).isSome
      = true ∧
    (stepA (fun _ => none) (wb (.Lcall none ("f", 1))) (stW 64) false).isSome = false := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.GateWExtDiag
