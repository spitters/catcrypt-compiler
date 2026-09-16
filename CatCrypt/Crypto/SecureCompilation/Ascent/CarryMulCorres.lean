/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Mem
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock

/-!
# The CryptOpt `carry_mul` kernel refines its abstract run

`X86Backend/CarryMulBlock.lean` splits the parsed kernel into segments at the
instructions that write a register used as a memory base. Within a segment no base
register of the tracked cells is written, so `SRmem` over a fixed cell list is
preserved, and `corres_sym` closes each segment against `absRunMem`:

* `carryMulMid` (instructions 5–146) reads and writes the input limbs `[rsi + 8i]`,
  `[rax + 8i]` and the seventeen frame slots `[rsp - 0x80]` … `[rsp + 0]`
  (`carryMulMidCells`);
* `carryMulTail` (instructions 148–166) writes the output limbs `[r10 + 8i]` and reads
  the six saved registers back from `[rsp - 0x80]` … `[rsp - 0x58]`
  (`carryMulTailCells`).

The remaining instructions, `carryMulPre` (`sub rsp`, the two memory-source
multiplies through `rdx`, `xchg rdx, rax`), `carryMulLoadOut` (`mov r10, [rsp - 0x50]`)
and `carryMulPost` (`add rsp`), each write a base register of the cells around them;
`CarryMulCorrect.lean` steps them on the machine state directly.

## Main results

* `carryMulMidCells`, `carryMulTailCells`: the two layouts.
* `srmem_carryMulMid_satisfiable`, `srmem_carryMulTail_satisfiable`: both layouts
  have a witness.
* `carryMulMid1_corres` … `carryMulMid5_corres`, `carryMulMid_corres`: the middle
  segment refines `absRunMem carryMulMid` over `SRmem carryMulMidCells`.
* `carryMulTail_corres`: the tail refines `absRunMem carryMulTail` over
  `SRmem carryMulTailCells`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock

/-- The cells of instructions 5–146: the input limbs `[rsi + 8i]` and `[rax + 8i]`, and
    the frame slots `[rsp - 8k]`, `k ≤ 16`. -/
def carryMulMidCells : List (String × Int) :=
  [("%rsi", 0), ("%rsi", 8), ("%rsi", 16), ("%rsi", 24), ("%rsi", 32),
   ("%rax", 0), ("%rax", 8), ("%rax", 16), ("%rax", 24), ("%rax", 32),
   ("%rsp", -128), ("%rsp", -120), ("%rsp", -112), ("%rsp", -104), ("%rsp", -96),
   ("%rsp", -88), ("%rsp", -80), ("%rsp", -72), ("%rsp", -64), ("%rsp", -56),
   ("%rsp", -48), ("%rsp", -40), ("%rsp", -32), ("%rsp", -24), ("%rsp", -16),
   ("%rsp", -8), ("%rsp", 0)]

/-- The cells of instructions 148–166: the output limbs `[r10 + 8i]` and the saved
    registers `[rsp - 0x80]` … `[rsp - 0x58]`. -/
def carryMulTailCells : List (String × Int) :=
  [("%r10", 0), ("%r10", 8), ("%r10", 16), ("%r10", 24), ("%r10", 32),
   ("%rsp", -128), ("%rsp", -120), ("%rsp", -112), ("%rsp", -104), ("%rsp", -96),
   ("%rsp", -88)]

/-- The register valuation used to witness the layouts: the two input arrays at
    `0x10000` and `0x20000`, the output array at `0x30000`, the stack pointer at
    `0x40000`. -/
def carryMulWitnessRegs (r : String) : BitVec 64 :=
  if r = "%rsi" then 0x10000 else if r = "%rax" then 0x20000
  else if r = "%r10" then 0x30000 else if r = "%rsp" then 0x40000 else 0

/-- The layout of instructions 5–146 is satisfiable. -/
theorem srmem_carryMulMid_satisfiable : ∃ st a, SRmem carryMulMidCells st a := by
  let a : AMemX := ⟨⟨carryMulWitnessRegs, false, false⟩, fun _ => 0⟩
  refine ⟨witnessState a, a, srmem_witnessState _ a ?_⟩
  unfold CellsSeparated
  decide

/-- The layout of instructions 148–166 is satisfiable. -/
theorem srmem_carryMulTail_satisfiable : ∃ st a, SRmem carryMulTailCells st a := by
  let a : AMemX := ⟨⟨carryMulWitnessRegs, false, false⟩, fun _ => 0⟩
  refine ⟨witnessState a, a, srmem_witnessState _ a ?_⟩
  unfold CellsSeparated
  decide

/-- Instructions 5–33 refine their abstract run over `SRmem carryMulMidCells`. -/
theorem carryMulMid1_corres :
    CorresJ (SRmem carryMulMidCells) (fun _ => True) (absRunMem carryMulMid1) carryMulMid1 := by
  corres_sym

/-- Instructions 34–63 refine their abstract run over `SRmem carryMulMidCells`. -/
theorem carryMulMid2_corres :
    CorresJ (SRmem carryMulMidCells) (fun _ => True) (absRunMem carryMulMid2) carryMulMid2 := by
  corres_sym

/-- Instructions 64–92 refine their abstract run over `SRmem carryMulMidCells`. -/
theorem carryMulMid3_corres :
    CorresJ (SRmem carryMulMidCells) (fun _ => True) (absRunMem carryMulMid3) carryMulMid3 := by
  corres_sym

/-- Instructions 93–120 refine their abstract run over `SRmem carryMulMidCells`. -/
theorem carryMulMid4_corres :
    CorresJ (SRmem carryMulMidCells) (fun _ => True) (absRunMem carryMulMid4) carryMulMid4 := by
  corres_sym

/-- Instructions 121–146 refine their abstract run over `SRmem carryMulMidCells`. -/
theorem carryMulMid5_corres :
    CorresJ (SRmem carryMulMidCells) (fun _ => True) (absRunMem carryMulMid5) carryMulMid5 := by
  corres_sym

/-- Instructions 5–146 refine their abstract run over `SRmem carryMulMidCells`. -/
theorem carryMulMid_corres :
    CorresJ (SRmem carryMulMidCells) (fun _ => True) (absRunMem carryMulMid) carryMulMid :=
  corresJ_absRunMem_append _
    (corresJ_absRunMem_append _
      (corresJ_absRunMem_append _
        (corresJ_absRunMem_append _ carryMulMid1_corres carryMulMid2_corres)
        carryMulMid3_corres)
      carryMulMid4_corres)
    carryMulMid5_corres

/-- Instructions 148–166 refine their abstract run over `SRmem carryMulTailCells`. -/
theorem carryMulTail_corres :
    CorresJ (SRmem carryMulTailCells) (fun _ => True) (absRunMem carryMulTail) carryMulTail := by
  corres_sym

end CatCrypt.Crypto.SecureCompilation.Ascent
