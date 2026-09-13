/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresAttr
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Solver
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock
public import Lean

/-!
# Memory-operand leaves of the x86 ascent over an address-keyed abstract memory

The machine memory of `JState 64` is keyed by the base register's *name* and a
displacement: `evalInstr` reads `[b + o]` as `s.mem b o` and writes it with
`JState.store b o`. A hand-written kernel addresses memory by *value*: the cell
`[b + o]` is the address `regs b + o`. This module relates the two. The abstract
state `AMemX` carries the dual-carry state `ACarry2` (registers, `CF`, `OF`) and an
address-keyed memory `BitVec 64 → BitVec 64`; the relation `SRmem cells` fixes a
finite list `cells` of `(base, displacement)` pairs and states

* `SRcarry2` on the registers and the two carry flags,
* for every tracked cell `(b, o)`, `st.mem b o = a.mem (a.regs b + o)`,
* `CellsSeparated`: distinct tracked cells have distinct addresses.

Under these conditions the name-keyed machine memory and the address-keyed abstract
memory agree on the tracked cells, and they stay in agreement across a step that
writes no base register of a tracked cell (the side condition `d ∉ baseRegs cells`
of the leaves) and that reads or writes memory only at tracked cells (the side
condition `(b, o) ∈ cells`).

The flag-and-register leaves of `SRcarry2` lift to `SRmem` through
`corresJ_liftCarry2`; the memory-operand instructions `loadMem`, `storeMem` and
`mulxMem` have direct leaves. `corres_solve_mem` runs the `corres_solve` fold and
discharges the side conditions by `decide`.

The layouts of CryptOpt's Curve25519 `carry_mul`
(`fiat_curve25519_carry_mul/seed1667947554054692_ratio13465.asm`) are
`carryMulEntryCells` (the five limbs at `[rsi + 8i]`, `[rdx + 8i]`, `[rdi + 8i]` and
the seventeen spill slots `[rsp - 8k]`, `k ≤ 16`) and `carryMulBodyCells` (the same
with the second input array at `rax`, the base after `xchg rdx, rax`); both are
satisfiable (`srmem_carryMulEntry_satisfiable`, `srmem_carryMulBody_satisfiable`).

The leaves cover every instruction of CryptOpt's Curve25519 `solinas_square`
(`bench/cryptopt/fiat_curve25519_solinas_square.asm`, as `NasmParse.toJInstr` maps it).
`ACarry2` tracks `CF` and `OF` and no other flag; the kernel reads no other flag, and
`setcc`/`cmovcc` have leaves exactly at the conditions `carryConds` that read only
`CF` and `OF`. `absStepMem` is the abstract step of each covered instruction and
`absRunMem` its fold over a block; the layout `solinasCells` (input limbs
`[rsi + 8i]`, output limbs `[rdi + 8i]`, six spill slots `[rsp - 0x80]` …
`[rsp - 0x58]`) is satisfiable (`srmem_solinas_satisfiable`), and the 99-instruction
body refines `absRunMem` over `SRmem solinasCells` (`solinasBody_corres`), composed
from four segments closed by `corres_solve_mem`.

## Main results

* `SRmem`, `CellsSeparated`, `cellAddr`, `baseRegs`: the relation and its parts.
* `corresJ_liftCarry2`: an `SRcarry2` leaf that writes no memory and no base register
  is an `SRmem` leaf.
* `corresJ_mov2`, `corresJ_add2`, `corresJ_xor2`, `corresJ_imul2`: `SRcarry2` leaves
  for `mov`, `add`, `xor` and two-operand `imul` with a register or immediate source.
* `corresJ_loadMemM`, `corresJ_storeMemM`, `corresJ_mulxMemM`: the memory-operand
  leaves.
* `corresJ_movM`, `corresJ_addM`, `corresJ_xorM`, `corresJ_imulM`, `corresJ_mulxM`,
  `corresJ_adcxM`, `corresJ_adoxM`: the lifted register leaves.
* `corresJ_memSrcM`, `corresJ_addMemM`, `corresJ_imulMemM`, `corresJ_imulriMemM`,
  `corresJ_adcxMemM`, `corresJ_adoxMemM`: the leaves of the memory-source arithmetic,
  each an `SRcarry2` leaf at the loaded word.
* `runBlock_imulMemImm`: the block `loadMem d b o; imul d k` has the effect of the
  three-operand `imul d, [b + o], k` on registers, flags and memory.
* `corres_solve_mem`: the solver over `SRmem`.
* `carryMul_lines8to16_corres`, `carryMul_imul_corres`, `carryMul_addAdcx_corres`:
  instruction sequences of the `carry_mul` file closed by `corres_solve_mem`.
* `corresJ_inc2`, `corresJ_clc2`, `corresJ_testN2`, `corresJ_test2`, `corresJ_adc2`,
  `corresJ_lea2`, `corresJ_movzx2`, `corresJ_setcc2`, `corresJ_cmovcc2`: `SRcarry2`
  leaves for `inc`, `clc`, `test`, `adc`, `lea`, `movzx`, and `setcc`/`cmovcc` at a
  condition of `carryConds`.
* `corresJ_incM`, `corresJ_clcM`, `corresJ_testNM`, `corresJ_testM`, `corresJ_adcM`,
  `corresJ_leaM`, `corresJ_movzxM`, `corresJ_setccM`, `corresJ_cmovccM`: their lifts
  to `SRmem`.
* `wordExtendMerge_setcc`, `x86_MOVZX_eq_mod`, `condB_eq_condStep2`: the byte merge of
  `SETcc`, zero extension as a residue, and the carry conditions on `ACarry2`.
* `absStepMem`, `absRunMem`, `corresJ_absRunMem_append`: the abstract run and its
  sequencing rule.
* `solinasCells`, `srmem_solinas_satisfiable`: the `solinas_square` layout.
* `solinasSeg1_corres` … `solinasSeg4_corres`, `solinasBody_corres`,
  `solinasSquareBlock_corres`: the four segments
  and the whole body of `solinas_square` refine their abstract runs (the segment
  literals and `solinasBody_eq_block` are in `X86Backend/SolinasSquareBlock.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock

/-! ## The abstract state and the relation -/

/-- The abstract state of a kernel with memory operands: the dual-carry state
    (registers, `CF`, `OF`) and a memory keyed by 64-bit address. -/
structure AMemX where
  /-- Registers and the two carry flags. -/
  c : ACarry2
  /-- Address-keyed memory. -/
  mem : BitVec 64 → BitVec 64

/-- The address of the cell `[b + o]` under the register valuation `regs`. -/
def cellAddr (regs : String → BitVec 64) (c : String × Int) : BitVec 64 :=
  regs c.1 + BitVec.ofInt 64 c.2

/-- The base registers of a cell list. -/
def baseRegs (cells : List (String × Int)) : List String := cells.map Prod.fst

/-- Distinct tracked cells have distinct addresses under `regs`. -/
def CellsSeparated (cells : List (String × Int)) (regs : String → BitVec 64) : Prop :=
  ∀ c ∈ cells, ∀ c' ∈ cells, cellAddr regs c = cellAddr regs c' → c = c'

/-- `SRmem cells`: registers and the two carry flags agree (`SRcarry2`), every
    tracked cell `(b, o)` of the machine memory holds the abstract memory word at
    address `regs b + o`, and the tracked cells are separated. -/
def SRmem (cells : List (String × Int)) (st : JState 64) (a : AMemX) : Prop :=
  SRcarry2 st a.c ∧ (∀ c ∈ cells, st.mem c.1 c.2 = a.mem (cellAddr a.c.regs c)) ∧
    CellsSeparated cells a.c.regs

/-- Cell addresses depend only on the base registers. -/
theorem cellAddr_frame (cells : List (String × Int)) (regs regs' : String → BitVec 64)
    (h : ∀ r ∈ baseRegs cells, regs' r = regs r) :
    ∀ c ∈ cells, cellAddr regs' c = cellAddr regs c := by
  intro c hc
  simp only [cellAddr, h c.1 (List.mem_map_of_mem hc)]

/-- Separation depends only on the base registers. -/
theorem cellsSeparated_frame (cells : List (String × Int)) (regs regs' : String → BitVec 64)
    (h : ∀ r ∈ baseRegs cells, regs' r = regs r) (hs : CellsSeparated cells regs) :
    CellsSeparated cells regs' := by
  intro c hc c' hc' he
  rw [cellAddr_frame cells regs regs' h c hc, cellAddr_frame cells regs regs' h c' hc'] at he
  exact hs c hc c' hc' he

/-- A single-register write at `d ∉ baseRegs cells` leaves the base registers. -/
theorem base_of_write (cells : List (String × Int)) (d : String)
    (hd : d ∉ baseRegs cells) (v : BitVec 64) (regs : String → BitVec 64) :
    ∀ r ∈ baseRegs cells, (if r = d then v else regs r) = regs r := by
  intro r hr
  have : r ≠ d := fun h => hd (h ▸ hr)
  simp [this]

/-! ## Lifting `SRcarry2` leaves -/

/-- An `SRcarry2` leaf for an instruction that writes no memory, whose abstract step
    leaves the base registers of `cells`, is an `SRmem cells` leaf with the abstract
    memory unchanged. -/
theorem corresJ_liftCarry2 (cells : List (String × Int)) {f : ACarry2 → ACarry2}
    {i : JInstr 64} (h : CorresJ SRcarry2 (fun _ => True) f [i])
    (hmem : ∀ s : JState 64, (evalInstr s i).mem = s.mem)
    (hbase : ∀ x : ACarry2, ∀ r ∈ baseRegs cells, (f x).regs r = x.regs r) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨f a.c, a.mem⟩) [i] := by
  intro s a ⟨h2, hm, hsep⟩ _
  refine ⟨h s a.c h2 trivial, ?_, cellsSeparated_frame cells _ _ (hbase a.c) hsep⟩
  intro c hc
  simp only [runBlock_cons, runBlock_nil, hmem]
  rw [cellAddr_frame cells a.c.regs (f a.c).regs (hbase a.c) c hc]
  exact hm c hc

/-! ## `SRcarry2` leaves for `mov`, `add`, `xor`, `imul` -/

/-- `mov d o` over `ACarry2`: `d := o`, flags unchanged. -/
def movStep2 (d : String) (o : JOperand) (a : ACarry2) : ACarry2 :=
  { a with regs := fun r => if r = d then evalX a.regs o else a.regs r }

/-- `add d o` over `ACarry2`: `d := d + o`; `CF` is the unsigned overflow
    `2^64 ≤ d + o` and `OF` the signed overflow of the sum. -/
def addStep2 (d : String) (o : JOperand) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = d then a.regs d + evalX a.regs o else a.regs r
    cf := decide (2 ^ 64 ≤ (a.regs d).toNat + (evalX a.regs o).toNat)
    of := decide ((a.regs d + evalX a.regs o).toInt ≠
      (a.regs d).toInt + (evalX a.regs o).toInt) }

/-- `xor d o` over `ACarry2`: `d := d ^^^ o`; `CF` and `OF` cleared. -/
def xorStep2 (d : String) (o : JOperand) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = d then a.regs d ^^^ evalX a.regs o else a.regs r
    cf := false
    of := false }

/-- The signed-overflow bit of the 64-bit product `x * y`: the product of the signed
    values lies outside `[-2^63, 2^63 - 1]`. -/
def imulOverflow (x y : BitVec 64) : Bool :=
  decide (x.toInt * y.toInt < -(2 ^ 63 : Int) ∨ x.toInt * y.toInt > (2 ^ 63 : Int) - 1)

/-- `imul d o` over `ACarry2`: `d :=` the low word of `d * o`; `CF` and `OF` are the
    signed-overflow bit. -/
def imulStep2 (d : String) (o : JOperand) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = d then a.regs d * evalX a.regs o else a.regs r
    cf := imulOverflow (a.regs d) (evalX a.regs o)
    of := imulOverflow (a.regs d) (evalX a.regs o) }

/-- `mov` refines `movStep2`. -/
theorem corresJ_mov2 (d : String) (o : JOperand) :
    CorresJ SRcarry2 (fun _ => True) (movStep2 d o) [.mov d o] := by
  intro s a ⟨hreg, hcf, hof⟩ _
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, x86_MOV, movStep2,
      evalX_eq s a.regs hreg]
    split <;> simp [hreg r]
  · exact hcf
  · exact hof

/-- `add` refines `addStep2`. -/
theorem corresJ_add2 (d : String) (o : JOperand) :
    CorresJ SRcarry2 (fun _ => True) (addStep2 d o) [.add d o] := by
  intro s a ⟨hreg, _, _⟩ _
  have ho := evalX_eq s a.regs hreg o
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, x86_ADD,
      rflags_of_aluop, addStep2, JState.get, ho, hreg d]
    split <;> simp [hreg r]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_ADD, rflags_of_aluop, Option.getD_some, addStep2, JState.get, wunsigned, ho, hreg d]
    rw [decide_eq_decide, BitVec.toNat_add]
    have := (a.regs d).isLt
    have := (evalX a.regs o).isLt
    omega
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_ADD, rflags_of_aluop, Option.getD_some, addStep2, JState.get, wsigned, ho, hreg d]

/-- `xor` refines `xorStep2`. -/
theorem corresJ_xor2 (d : String) (o : JOperand) :
    CorresJ SRcarry2 (fun _ => True) (xorStep2 d o) [.xor_ d o] := by
  intro s a ⟨hreg, _, _⟩ _
  have ho := evalX_eq s a.regs hreg o
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, x86_XOR,
      rflags_of_bwop, xorStep2, JState.get, ho, hreg d]
    split <;> simp [hreg r]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_XOR, rflags_of_bwop, Option.getD_some, xorStep2]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_XOR, rflags_of_bwop, Option.getD_some, xorStep2]

/-- `imul` refines `imulStep2`. -/
theorem corresJ_imul2 (d : String) (o : JOperand) :
    CorresJ SRcarry2 (fun _ => True) (imulStep2 d o) [.imul d o] := by
  intro s a ⟨hreg, _, _⟩ _
  have ho := evalX_eq s a.regs hreg o
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, x86_IMULt,
      rflags_of_mul, imulStep2, JState.get, ho, hreg d]
    split <;> simp [hreg r]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_IMULt, rflags_of_mul, Option.getD_some, imulStep2, imulOverflow, wsigned,
      JState.get, ho, hreg d]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_IMULt, rflags_of_mul, Option.getD_some, imulStep2, imulOverflow, wsigned,
      JState.get, ho, hreg d]

/-! ## The memory-operand leaves -/

/-- `loadMem d b o` over `AMemX`: `d :=` the memory word at address `regs b + o`. -/
def loadStepM (d b : String) (o : Int) (a : AMemX) : AMemX :=
  ⟨{ a.c with regs := fun r => if r = d then a.mem (cellAddr a.c.regs (b, o)) else a.c.regs r },
    a.mem⟩

/-- `storeMem b o src` over `AMemX`: the memory word at address `regs b + o` becomes
    `src`; registers and flags unchanged. -/
def storeStepM (b : String) (o : Int) (src : JOperand) (a : AMemX) : AMemX :=
  ⟨a.c, fun p => if p = cellAddr a.c.regs (b, o) then evalX a.c.regs src else a.mem p⟩

/-- `mulxMem dHi dLo x b o` over `AMemX`: the low and high words of the 128-bit product
    of `x` and the memory word at `regs b + o` go to `dLo` and `dHi` (the high write
    last); flags unchanged. -/
def mulxMemStepM (dHi dLo : String) (x : JOperand) (b : String) (o : Int) (a : AMemX) :
    AMemX :=
  { c := { regs := fun r =>
             if r = dHi then BitVec.ofNat 64
               ((evalX a.c.regs x).toNat * (a.mem (cellAddr a.c.regs (b, o))).toNat / 2 ^ 64)
             else if r = dLo then BitVec.ofNat 64
               ((evalX a.c.regs x).toNat * (a.mem (cellAddr a.c.regs (b, o))).toNat)
             else a.c.regs r
           cf := a.c.cf
           of := a.c.of }
    mem := a.mem }

/-- `loadMem` from a tracked cell into a register that is not a base refines
    `loadStepM`. -/
theorem corresJ_loadMemM (cells : List (String × Int)) (d b : String) (o : Int)
    (hc : (b, o) ∈ cells) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (loadStepM d b o) [.loadMem d b o] := by
  intro s a ⟨⟨hreg, hcf, hof⟩, hm, hsep⟩ _
  have hbase := base_of_write cells d hd (a.mem (cellAddr a.c.regs (b, o))) a.c.regs
  refine ⟨⟨?_, hcf, hof⟩, ?_, cellsSeparated_frame cells _ _ hbase hsep⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, x86_MOV, JState.load,
      loadStepM]
    split
    · exact hm (b, o) hc
    · exact hreg r
  · intro c hc'
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, loadStepM]
    rw [cellAddr_frame cells a.c.regs _ hbase c hc']
    exact hm c hc'

/-- `storeMem` to a tracked cell refines `storeStepM`. -/
theorem corresJ_storeMemM (cells : List (String × Int)) (b : String) (o : Int)
    (src : JOperand) (hc : (b, o) ∈ cells) :
    CorresJ (SRmem cells) (fun _ => True) (storeStepM b o src) [.storeMem b o src] := by
  intro s a ⟨⟨hreg, hcf, hof⟩, hm, hsep⟩ _
  refine ⟨⟨hreg, hcf, hof⟩, ?_, hsep⟩
  intro c hc'
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.store, x86_MOV, storeStepM]
  by_cases hcb : c = (b, o)
  · subst hcb
    simp only [and_self, if_true]
    exact evalX_eq s a.c.regs hreg src
  · have hne : ¬ (c.1 = b ∧ c.2 = o) := fun ⟨h1, h2⟩ => hcb (Prod.ext h1 h2)
    have hadr : cellAddr a.c.regs c ≠ cellAddr a.c.regs (b, o) :=
      fun he => hcb (hsep c hc' (b, o) hc he)
    rw [if_neg hne, if_neg hadr]
    exact hm c hc'

/-- `mulxMem` with a tracked memory source, writing two registers that are not bases,
    refines `mulxMemStepM`. -/
theorem corresJ_mulxMemM (cells : List (String × Int)) (dHi dLo : String) (x : JOperand)
    (b : String) (o : Int) (hc : (b, o) ∈ cells) (hHi : dHi ∉ baseRegs cells)
    (hLo : dLo ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (mulxMemStepM dHi dLo x b o)
      [.mulxMem dHi dLo x b o] := by
  intro s a ⟨⟨hreg, hcf, hof⟩, hm, hsep⟩ _
  have hbase : ∀ r ∈ baseRegs cells, (mulxMemStepM dHi dLo x b o a).c.regs r = a.c.regs r := by
    intro r hr
    have h1 : r ≠ dHi := fun h => hHi (h ▸ hr)
    have h2 : r ≠ dLo := fun h => hLo (h ▸ hr)
    simp [mulxMemStepM, h1, h2]
  refine ⟨⟨?_, hcf, hof⟩, ?_, cellsSeparated_frame cells _ _ hbase hsep⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, high_bits,
      JState.setReg, JState.load, mulxMemStepM, evalX_eq s a.c.regs hreg, hm (b, o) hc]
    by_cases h1 : r = dHi
    · simp [h1]
    · by_cases h2 : r = dLo
      · simp [h2]
      · simp [h1, h2, hreg r]
  · intro c hc'
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, JState.setReg]
    rw [cellAddr_frame cells a.c.regs _ hbase c hc']
    exact hm c hc'

/-! ## The lifted register leaves -/

/-- `mov` to a register that is not a base, over `SRmem`. -/
theorem corresJ_movM (cells : List (String × Int)) (d : String) (o : JOperand)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨movStep2 d o a.c, a.mem⟩) [.mov d o] :=
  corresJ_liftCarry2 cells (corresJ_mov2 d o) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- `add` to a register that is not a base, over `SRmem`. -/
theorem corresJ_addM (cells : List (String × Int)) (d : String) (o : JOperand)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨addStep2 d o a.c, a.mem⟩) [.add d o] :=
  corresJ_liftCarry2 cells (corresJ_add2 d o) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- `xor` to a register that is not a base, over `SRmem`. -/
theorem corresJ_xorM (cells : List (String × Int)) (d : String) (o : JOperand)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨xorStep2 d o a.c, a.mem⟩) [.xor_ d o] :=
  corresJ_liftCarry2 cells (corresJ_xor2 d o) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- Two-operand `imul` to a register that is not a base, over `SRmem`. -/
theorem corresJ_imulM (cells : List (String × Int)) (d : String) (o : JOperand)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨imulStep2 d o a.c, a.mem⟩) [.imul d o] :=
  corresJ_liftCarry2 cells (corresJ_imul2 d o) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- Register-operand `mulx` writing two registers that are not bases, over `SRmem`. -/
theorem corresJ_mulxM (cells : List (String × Int)) (dHi dLo ra rb : String)
    (hHi : dHi ∉ baseRegs cells) (hLo : dLo ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨mulxStep2 dHi dLo ra rb a.c, a.mem⟩)
      [.mulx dHi dLo (.reg ra) (.reg rb)] :=
  corresJ_liftCarry2 cells (corresJ_mulx2 dHi dLo ra rb) (fun _ => rfl)
    (fun x r hr => by
      have h1 : r ≠ dHi := fun h => hHi (h ▸ hr)
      have h2 : r ≠ dLo := fun h => hLo (h ▸ hr)
      simp [mulxStep2, h1, h2])

/-- Register-operand `adcx` to a register that is not a base, over `SRmem`. -/
theorem corresJ_adcxM (cells : List (String × Int)) (d src : String)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨adcxStep2 d src a.c, a.mem⟩)
      [.adcx d (.reg src)] :=
  corresJ_liftCarry2 cells (corresJ_adcx2 d src) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- Register-operand `adox` to a register that is not a base, over `SRmem`. -/
theorem corresJ_adoxM (cells : List (String × Int)) (d src : String)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨adoxStep2 d src a.c, a.mem⟩)
      [.adox d (.reg src)] :=
  corresJ_liftCarry2 cells (corresJ_adox2 d src) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-! ## Three-operand `imul` with a memory source -/

/-- The block `loadMem d b o; imul d k` has the effect of `imul d, [b + o], k`: the
    destination receives `x86_IMULt` of the memory word and the immediate, all five
    flags are written from that product, and memory is unchanged. -/
theorem runBlock_imulMemImm (s : JState 64) (d b : String) (o : Int) (k : Nat) :
    runBlock s [.loadMem d b o, .imul d (.imm k)] =
      s.writeB5W d (x86_IMULt (s.load b o) (BitVec.ofNat 64 k)) := by
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JState.writeB5W,
    JState.get, JOperand.eval, x86_MOV, if_pos]
  congr 1
  funext r
  split <;> simp_all

/-! ## The memory-source arithmetic leaves

`addMem`, `imulMem`, `imulriMem`, `adcxMem` and `adoxMem` read one tracked cell and
write one register. Each has the effect of its register form with the cell's word in
place of the register operand, so each leaf is an `SRcarry2` leaf at an immediate
source equal to the word, lifted through `corresJ_memSrcM`. -/

/-- A memory-source instruction `i` reading the tracked cell `(b, o)` refines the
    `SRcarry2` leaf of a block `gs v` that takes the cell's word as the immediate `v`:
    `i` runs as `gs` at the loaded word, `gs` writes no memory, and its abstract step
    leaves the base registers. -/
theorem corresJ_memSrcM (cells : List (String × Int)) {i : JInstr 64}
    (gs : Nat → List (JInstr 64)) (f : Nat → ACarry2 → ACarry2) (b : String) (o : Int)
    (hc : (b, o) ∈ cells)
    (hleaf : ∀ v, CorresJ SRcarry2 (fun _ => True) (f v) (gs v))
    (heq : ∀ s : JState 64, runBlock s [i] = runBlock s (gs (s.load b o).toNat))
    (hmem : ∀ v (s : JState 64), (runBlock s (gs v)).mem = s.mem)
    (hbase : ∀ v (x : ACarry2), ∀ r ∈ baseRegs cells, (f v x).regs r = x.regs r) :
    CorresJ (SRmem cells) (fun _ => True)
      (fun a => ⟨f (a.mem (cellAddr a.c.regs (b, o))).toNat a.c, a.mem⟩) [i] := by
  intro s a ⟨h2, hm, hsep⟩ _
  have hv : s.load b o = a.mem (cellAddr a.c.regs (b, o)) := hm (b, o) hc
  rw [heq s, hv]
  refine ⟨hleaf _ s a.c h2 trivial, ?_, cellsSeparated_frame cells _ _ (hbase _ a.c) hsep⟩
  intro c hc'
  rw [hmem, cellAddr_frame cells a.c.regs _ (hbase _ a.c) c hc']
  exact hm c hc'

/-- `adcx d, $v` over `ACarry2`: `adcxStep2` with the immediate word `v` as source. -/
def adcxImmStep2 (dst : String) (v : Nat) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = dst then
      add_carry (a.regs dst) (BitVec.ofNat 64 v) (if a.cf then 1 else 0) else a.regs r
    cf := decide (2 ^ 64 ≤ (a.regs dst).toNat + (BitVec.ofNat 64 v).toNat +
      (if a.cf then 1 else 0))
    of := a.of }

/-- `adox d, $v` over `ACarry2`: `adoxStep2` with the immediate word `v` as source. -/
def adoxImmStep2 (dst : String) (v : Nat) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = dst then
      add_carry (a.regs dst) (BitVec.ofNat 64 v) (if a.of then 1 else 0) else a.regs r
    cf := a.cf
    of := decide (2 ^ 64 ≤ (a.regs dst).toNat + (BitVec.ofNat 64 v).toNat +
      (if a.of then 1 else 0)) }

/-- The `adcx` evaluation at an immediate source refines `adcxImmStep2`. -/
theorem corresJ_adcxImm2 (dst : String) (v : Nat) :
    CorresJ SRcarry2 (fun _ => True) (adcxImmStep2 dst v) [.adcx dst (.imm v)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf, hof⟩ := hSR
  have hcf' : Option.getD st.flags.cf false = a.cf := by simpa [JState.flagB] using hcf
  have hof' : Option.getD st.flags.of false = a.of := by simpa [JState.flagB] using hof
  refine ⟨?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = dst
    · subst hr
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        add_carry, adcxImmStep2, JState.get, JOperand.eval, hcf, hreg]
    · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        adcxImmStep2, JState.get, JOperand.eval, hcf, hreg, if_neg hr]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, Option.getD_some, adcxImmStep2, JState.get, JOperand.eval, hcf', hreg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, adcxImmStep2]
    exact hof'

/-- The `adox` evaluation at an immediate source refines `adoxImmStep2`. -/
theorem corresJ_adoxImm2 (dst : String) (v : Nat) :
    CorresJ SRcarry2 (fun _ => True) (adoxImmStep2 dst v) [.adox dst (.imm v)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf, hof⟩ := hSR
  have hcf' : Option.getD st.flags.cf false = a.cf := by simpa [JState.flagB] using hcf
  have hof' : Option.getD st.flags.of false = a.of := by simpa [JState.flagB] using hof
  refine ⟨?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = dst
    · subst hr
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        add_carry, adoxImmStep2, JState.get, JOperand.eval, hof, hreg]
    · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        adoxImmStep2, JState.get, JOperand.eval, hof, hreg, if_neg hr]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, adoxImmStep2]
    exact hcf'
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, Option.getD_some, adoxImmStep2, JState.get, JOperand.eval, hof', hreg]

/-- `add d, [b + o]` over `AMemX`: `addStep2` with the cell's word as source. -/
def addMemStepM (d b : String) (o : Int) (a : AMemX) : AMemX :=
  ⟨addStep2 d (.imm (a.mem (cellAddr a.c.regs (b, o))).toNat) a.c, a.mem⟩

/-- `imul d, [b + o]` over `AMemX`: `imulStep2` with the cell's word as source. -/
def imulMemStepM (d b : String) (o : Int) (a : AMemX) : AMemX :=
  ⟨imulStep2 d (.imm (a.mem (cellAddr a.c.regs (b, o))).toNat) a.c, a.mem⟩

/-- `imul d, [b + o], k` over `AMemX`: `d` receives the cell's word, then `imulStep2`
    multiplies it by `k`. -/
def imulriMemStepM (d b : String) (o : Int) (k : Nat) (a : AMemX) : AMemX :=
  ⟨imulStep2 d (.imm k) (movStep2 d (.imm (a.mem (cellAddr a.c.regs (b, o))).toNat) a.c),
    a.mem⟩

/-- `adcx d, [b + o]` over `AMemX`: `adcxImmStep2` at the cell's word. -/
def adcxMemStepM (d b : String) (o : Int) (a : AMemX) : AMemX :=
  ⟨adcxImmStep2 d (a.mem (cellAddr a.c.regs (b, o))).toNat a.c, a.mem⟩

/-- `adox d, [b + o]` over `AMemX`: `adoxImmStep2` at the cell's word. -/
def adoxMemStepM (d b : String) (o : Int) (a : AMemX) : AMemX :=
  ⟨adoxImmStep2 d (a.mem (cellAddr a.c.regs (b, o))).toNat a.c, a.mem⟩

/-- `add` with a tracked memory source into a register that is not a base refines
    `addMemStepM`. -/
theorem corresJ_addMemM (cells : List (String × Int)) (d b : String) (o : Int)
    (hc : (b, o) ∈ cells) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (addMemStepM d b o) [.addMem d b o] :=
  corresJ_memSrcM cells (fun v => [.add d (.imm v)]) (fun v => addStep2 d (.imm v)) b o hc
    (fun v => corresJ_add2 d (.imm v))
    (fun s => by simp [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval])
    (fun _ _ => rfl) (fun _ x => base_of_write cells d hd _ x.regs)

/-- Two-operand `imul` with a tracked memory source into a register that is not a base
    refines `imulMemStepM`. -/
theorem corresJ_imulMemM (cells : List (String × Int)) (d b : String) (o : Int)
    (hc : (b, o) ∈ cells) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (imulMemStepM d b o) [.imulMem d b o] :=
  corresJ_memSrcM cells (fun v => [.imul d (.imm v)]) (fun v => imulStep2 d (.imm v)) b o hc
    (fun v => corresJ_imul2 d (.imm v))
    (fun s => by simp [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval])
    (fun _ _ => rfl) (fun _ x => base_of_write cells d hd _ x.regs)

/-- Three-operand `imul` with a tracked memory source into a register that is not a
    base refines `imulriMemStepM`. -/
theorem corresJ_imulriMemM (cells : List (String × Int)) (d b : String) (o : Int) (k : Nat)
    (hc : (b, o) ∈ cells) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (imulriMemStepM d b o k) [.imulriMem d b o k] :=
  corresJ_memSrcM cells (fun v => [.mov d (.imm v), .imul d (.imm k)])
    (fun v c => imulStep2 d (.imm k) (movStep2 d (.imm v) c)) b o hc
    (fun v => corresJ_cons SRcarry2 (corresJ_mov2 d (.imm v)) (corresJ_imul2 d (.imm k))
      (fun _ _ => trivial))
    (fun s => by
      simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JState.writeB5W,
        JState.get, JOperand.eval, x86_MOV, if_pos, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      congr 1
      funext r
      split <;> simp_all)
    (fun _ _ => rfl)
    (fun _ x r hr => by
      have hne : r ≠ d := fun h => hd (h ▸ hr)
      simp [imulStep2, movStep2, hne])

/-- `adcx` with a tracked memory source into a register that is not a base refines
    `adcxMemStepM`. -/
theorem corresJ_adcxMemM (cells : List (String × Int)) (d b : String) (o : Int)
    (hc : (b, o) ∈ cells) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (adcxMemStepM d b o) [.adcxMem d b o] :=
  corresJ_memSrcM cells (fun v => [.adcx d (.imm v)]) (fun v => adcxImmStep2 d v) b o hc
    (fun v => corresJ_adcxImm2 d v)
    (fun s => by simp [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval])
    (fun _ _ => rfl) (fun _ x => base_of_write cells d hd _ x.regs)

/-- `adox` with a tracked memory source into a register that is not a base refines
    `adoxMemStepM`. -/
theorem corresJ_adoxMemM (cells : List (String × Int)) (d b : String) (o : Int)
    (hc : (b, o) ∈ cells) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (adoxMemStepM d b o) [.adoxMem d b o] :=
  corresJ_memSrcM cells (fun v => [.adox d (.imm v)]) (fun v => adoxImmStep2 d v) b o hc
    (fun v => corresJ_adoxImm2 d v)
    (fun s => by simp [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval])
    (fun _ _ => rfl) (fun _ x => base_of_write cells d hd _ x.regs)

/-! ## `SRcarry2` leaves for `inc`, `clc`, `test`, `adc`, `lea`, `movzx`, `setcc`, `cmovcc`

`ACarry2` tracks the registers, `CF` and `OF`. `ZF`, `SF` and `PF` are not tracked, so
a leaf exists for an instruction that reads no flag or reads only `CF` and `OF`:
`setcc` and `cmovcc` have leaves at the conditions `carryConds` (`o`, `no`, `b`,
`nb`), and no leaf at a condition that reads `ZF`, `SF` or `PF`. -/

/-- `inc d` over `ACarry2`: `d := d + 1`; `OF` is the signed overflow of the
    increment; `CF` unchanged. -/
def incStep2 (d : String) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = d then a.regs d + 1 else a.regs r
    cf := a.cf
    of := decide ((a.regs d + 1).toInt ≠ (a.regs d).toInt + 1) }

/-- `clc` over `ACarry2`: `CF` cleared. -/
def clcStep2 (a : ACarry2) : ACarry2 := { a with cf := false }

/-- `test` at any operand size over `ACarry2`: `CF` and `OF` cleared, registers
    unchanged. -/
def testStep2 (a : ACarry2) : ACarry2 := { a with cf := false, of := false }

/-- `adc d o` over `ACarry2`: `d := d + o + CF`; `CF` is the unsigned overflow and
    `OF` the signed overflow of the three-term sum. -/
def adcStep2 (d : String) (o : JOperand) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = d then
      add_carry (a.regs d) (evalX a.regs o) (if a.cf then 1 else 0) else a.regs r
    cf := decide (2 ^ 64 ≤ (a.regs d).toNat + (evalX a.regs o).toNat + (if a.cf then 1 else 0))
    of := decide ((add_carry (a.regs d) (evalX a.regs o) (if a.cf then 1 else 0)).toInt ≠
      (a.regs d).toInt + (evalX a.regs o).toInt + ((if a.cf then 1 else 0 : Nat) : Int)) }

/-- `lea d, [b + i * sc + off]` over `ACarry2`: `d :=` the address; flags unchanged. -/
def leaStep2 (d b i : String) (sc : Nat) (off : Int) (a : ACarry2) : ACarry2 :=
  { a with regs := fun r => if r = d then
      a.regs b + a.regs i * BitVec.ofNat 64 sc + BitVec.ofInt 64 off else a.regs r }

/-- `movzx d, src` from the low `sz` bits over `ACarry2`: `d := src mod 2^sz`; flags
    unchanged. -/
def movzxStep2 (d : String) (sz : Nat) (src : String) (a : ACarry2) : ACarry2 :=
  { a with regs := fun r => if r = d then
      BitVec.ofNat 64 ((a.regs src).toNat % 2 ^ sz) else a.regs r }

/-- The conditions that read only `CF` and `OF`. -/
def carryConds : List Condt := [.o, .no, .b, .nb]

/-- The value of a condition of `carryConds` on the two carry bits (`false` at the
    other conditions, which have no leaf). -/
def condStep2 (a : ACarry2) : Condt → Bool
  | .o => a.of
  | .no => !a.of
  | .b => a.cf
  | .nb => !a.cf
  | _ => false

/-- `setcc c d` over `ACarry2`: the low byte of `d` becomes `1` or `0` by the
    condition, bits 8 and above of `d` are kept; flags unchanged. -/
def setccStep2 (c : Condt) (d : String) (a : ACarry2) : ACarry2 :=
  { a with regs := fun r => if r = d then
      (a.regs d &&& ~~~(0xFF : BitVec 64)) ||| (if condStep2 a c then 1 else 0) else a.regs r }

/-- `cmovcc c d o` over `ACarry2`: `d := o` when the condition holds; flags
    unchanged. -/
def cmovccStep2 (c : Condt) (d : String) (o : JOperand) (a : ACarry2) : ACarry2 :=
  { a with regs := fun r => if r = d then
      (if condStep2 a c then evalX a.regs o else a.regs d) else a.regs r }

/-- On a condition of `carryConds`, the machine condition equals `condStep2` of the
    abstract carry bits. -/
theorem condB_eq_condStep2 (s : JState 64) (a : ACarry2) (hcf : s.flagB (·.cf) = a.cf)
    (hof : s.flagB (·.of) = a.of) (c : Condt) (hc : c ∈ carryConds) :
    s.condB c = condStep2 a c := by
  cases c <;> simp [carryConds] at hc <;>
    simp [JState.condB, x86_eval_cond, condStep2, hcf, hof]

/-- The `MSB_MERGE` write of the `SETcc` byte of `b` keeps bits 8 and above and sets
    the low byte to `1` or `0`. -/
theorem wordExtendMerge_setcc (old : BitVec 64) (b : Bool) :
    wordExtendMerge old (x86_SETcc b) = (old &&& ~~~(0xFF : BitVec 64)) ||| (if b then 1 else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases b
  · simp [wordExtendMerge, wshl, x86_SETcc]
  · simp [wordExtendMerge, wshl, x86_SETcc]
    grind

/-- Zero extension of the low `sz` bits is the residue modulo `2^sz`. -/
theorem x86_MOVZX_eq_mod (sz : Nat) (v : BitVec 64) :
    x86_MOVZX sz v = BitVec.ofNat 64 (v.toNat % 2 ^ sz) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [x86_MOVZX, BitVec.getLsbD_ofNat, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Nat.testBit_mod_two_pow]
  by_cases h : i < sz <;> simp [h, hi, BitVec.testBit_toNat] <;> omega

/-- `inc` refines `incStep2`. -/
theorem corresJ_inc2 (d : String) :
    CorresJ SRcarry2 (fun _ => True) (incStep2 d) [.inc d] := by
  intro s a ⟨hreg, hcf, _⟩ _
  refine ⟨?_, hcf, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB4W, x86_INC,
      rflags_of_aluop_nocf, incStep2, JState.get, hreg d]
    split <;> simp [hreg r]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB4W, JState.flagB, x86_INC,
      rflags_of_aluop_nocf, Option.getD_some, incStep2, wsigned, JState.get, hreg d]

/-- `clc` refines `clcStep2`. -/
theorem corresJ_clc2 : CorresJ SRcarry2 (fun _ => True) clcStep2 [.clc] := by
  intro s a ⟨hreg, _, hof⟩ _
  exact ⟨hreg, rfl, hof⟩

/-- `test` at operand size `sz` refines `testStep2`. -/
theorem corresJ_testN2 (sz : Nat) (x : String) (o : JOperand) :
    CorresJ SRcarry2 (fun _ => True) testStep2 [.testN sz x o] := by
  intro s a ⟨hreg, _, _⟩ _
  exact ⟨hreg, rfl, rfl⟩

/-- `test` at the register width refines `testStep2`. -/
theorem corresJ_test2 (x : String) (o : JOperand) :
    CorresJ SRcarry2 (fun _ => True) testStep2 [.test x o] := by
  intro s a ⟨hreg, _, _⟩ _
  exact ⟨hreg, rfl, rfl⟩

/-- `adc` refines `adcStep2`. -/
theorem corresJ_adc2 (d : String) (o : JOperand) :
    CorresJ SRcarry2 (fun _ => True) (adcStep2 d o) [.adc d o] := by
  intro s a ⟨hreg, hcf, _⟩ _
  have ho := evalX_eq s a.regs hreg o
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, x86_ADC,
      rflags_of_aluop, adcStep2, JState.get, ho, hreg d, hcf]
    split <;> simp [hreg r]
  · have hcf' : Option.getD s.flags.cf false = a.cf := hcf
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_ADC, rflags_of_aluop, Option.getD_some, adcStep2, JState.get, wunsigned, ho, hreg d,
      hcf']
    exact add_carry_eq _ _ _
  · have hcf' : Option.getD s.flags.cf false = a.cf := hcf
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.writeB5W_flags,
      x86_ADC, rflags_of_aluop, Option.getD_some, adcStep2, JState.get, wsigned, ho, hreg d,
      hcf']

/-- `lea` refines `leaStep2`. -/
theorem corresJ_lea2 (d b i : String) (sc : Nat) (off : Int) :
    CorresJ SRcarry2 (fun _ => True) (leaStep2 d b i sc off) [.lea d b i sc off] := by
  intro s a ⟨hreg, hcf, hof⟩ _
  refine ⟨?_, hcf, hof⟩
  intro r
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, x86_LEA, leaStep2,
    JState.get, hreg b, hreg i]
  split <;> simp [hreg r]

/-- `movzx` refines `movzxStep2`. -/
theorem corresJ_movzx2 (d : String) (sz : Nat) (src : String) :
    CorresJ SRcarry2 (fun _ => True) (movzxStep2 d sz src) [.movzx d sz src] := by
  intro s a ⟨hreg, hcf, hof⟩ _
  refine ⟨?_, hcf, hof⟩
  intro r
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, x86_MOVZX_eq_mod,
    movzxStep2, JState.get, hreg src]
  split <;> simp [hreg r]

/-- `setcc` at a condition of `carryConds` refines `setccStep2`. -/
theorem corresJ_setcc2 (c : Condt) (d : String) (hc : c ∈ carryConds) :
    CorresJ SRcarry2 (fun _ => True) (setccStep2 c d) [.setcc c d] := by
  intro s a ⟨hreg, hcf, hof⟩ _
  refine ⟨?_, hcf, hof⟩
  intro r
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setRegMerge, JState.setReg,
    wordExtendMerge_setcc, condB_eq_condStep2 s a hcf hof c hc, setccStep2, JState.get, hreg d]
  split <;> simp [hreg r]

/-- `cmovcc` at a condition of `carryConds` refines `cmovccStep2`. -/
theorem corresJ_cmovcc2 (c : Condt) (d : String) (o : JOperand) (hc : c ∈ carryConds) :
    CorresJ SRcarry2 (fun _ => True) (cmovccStep2 c d o) [.cmovcc c d o] := by
  intro s a ⟨hreg, hcf, hof⟩ _
  refine ⟨?_, hcf, hof⟩
  intro r
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, x86_CMOVcc,
    condB_eq_condStep2 s a hcf hof c hc, cmovccStep2, JState.get, hreg d,
    evalX_eq s a.regs hreg o]
  split <;> simp [hreg r]

/-! ## The lifted leaves of the `solinas_square` repertoire -/

/-- `inc` of a register that is not a base, over `SRmem`. -/
theorem corresJ_incM (cells : List (String × Int)) (d : String) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨incStep2 d a.c, a.mem⟩) [.inc d] :=
  corresJ_liftCarry2 cells (corresJ_inc2 d) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- `clc` over `SRmem`. -/
theorem corresJ_clcM (cells : List (String × Int)) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨clcStep2 a.c, a.mem⟩) [.clc] :=
  corresJ_liftCarry2 cells corresJ_clc2 (fun _ => rfl) (fun _ _ _ => rfl)

/-- `test` at operand size `sz` over `SRmem`. -/
theorem corresJ_testNM (cells : List (String × Int)) (sz : Nat) (x : String) (o : JOperand) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨testStep2 a.c, a.mem⟩) [.testN sz x o] :=
  corresJ_liftCarry2 cells (corresJ_testN2 sz x o) (fun _ => rfl) (fun _ _ _ => rfl)

/-- `test` at the register width over `SRmem`. -/
theorem corresJ_testM (cells : List (String × Int)) (x : String) (o : JOperand) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨testStep2 a.c, a.mem⟩) [.test x o] :=
  corresJ_liftCarry2 cells (corresJ_test2 x o) (fun _ => rfl) (fun _ _ _ => rfl)

/-- `adc` to a register that is not a base, over `SRmem`. -/
theorem corresJ_adcM (cells : List (String × Int)) (d : String) (o : JOperand)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨adcStep2 d o a.c, a.mem⟩) [.adc d o] :=
  corresJ_liftCarry2 cells (corresJ_adc2 d o) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- `lea` to a register that is not a base, over `SRmem`. -/
theorem corresJ_leaM (cells : List (String × Int)) (d b i : String) (sc : Nat) (off : Int)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨leaStep2 d b i sc off a.c, a.mem⟩)
      [.lea d b i sc off] :=
  corresJ_liftCarry2 cells (corresJ_lea2 d b i sc off) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- `movzx` to a register that is not a base, over `SRmem`. -/
theorem corresJ_movzxM (cells : List (String × Int)) (d : String) (sz : Nat) (src : String)
    (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨movzxStep2 d sz src a.c, a.mem⟩)
      [.movzx d sz src] :=
  corresJ_liftCarry2 cells (corresJ_movzx2 d sz src) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- `setcc` at a condition of `carryConds` to a register that is not a base, over
    `SRmem`. -/
theorem corresJ_setccM (cells : List (String × Int)) (c : Condt) (d : String)
    (hc : c ∈ carryConds) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨setccStep2 c d a.c, a.mem⟩) [.setcc c d] :=
  corresJ_liftCarry2 cells (corresJ_setcc2 c d hc) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-- `cmovcc` at a condition of `carryConds` to a register that is not a base, over
    `SRmem`. -/
theorem corresJ_cmovccM (cells : List (String × Int)) (c : Condt) (d : String) (o : JOperand)
    (hc : c ∈ carryConds) (hd : d ∉ baseRegs cells) :
    CorresJ (SRmem cells) (fun _ => True) (fun a => ⟨cmovccStep2 c d o a.c, a.mem⟩)
      [.cmovcc c d o] :=
  corresJ_liftCarry2 cells (corresJ_cmovcc2 c d o hc) (fun _ => rfl)
    (fun x => base_of_write cells d hd _ x.regs)

/-! ## `@[corres]` registrations and the solver -/

attribute [corres] corresJ_mov2 corresJ_add2 corresJ_xor2 corresJ_imul2
  corresJ_loadMemM corresJ_storeMemM corresJ_mulxMemM
  corresJ_movM corresJ_addM corresJ_xorM corresJ_imulM corresJ_mulxM
  corresJ_adcxM corresJ_adoxM
  corresJ_inc2 corresJ_clc2 corresJ_testN2 corresJ_test2 corresJ_adc2 corresJ_lea2
  corresJ_movzx2
  corresJ_incM corresJ_clcM corresJ_testNM corresJ_testM corresJ_adcM corresJ_leaM
  corresJ_movzxM corresJ_setccM corresJ_cmovccM
  corresJ_addMemM corresJ_imulMemM corresJ_imulriMemM corresJ_adcxMemM corresJ_adoxMemM

/-- Apply a `@[corres]` leaf to a single-instruction goal and discharge its side
    conditions (cell membership, base-register non-membership) by `decide`. -/
syntax "corres_leaf_mem" : tactic
macro_rules
  | `(tactic| corres_leaf_mem) => `(tactic| (corres_leaf <;> decide))

/-- The fold of `corres_chain` with `corres_leaf_mem` at each instruction. -/
syntax "corres_chain_mem" : tactic
macro_rules
  | `(tactic| corres_chain_mem) =>
    `(tactic|
      first
      | corres_leaf_mem
      | (apply corresJ_cons
         · corres_leaf_mem
         · corres_chain_mem
         · exact fun _ _ => trivial))

/-- Refine a `CorresJ (SRmem cells)` over a straight-line block by composing the
    `@[corres]` leaves, with the side conditions of the memory leaves decided on the
    concrete cell list; the synthesized fold is matched against the goal's transition
    by `rfl`. -/
syntax "corres_solve_mem" : tactic
macro_rules
  | `(tactic| corres_solve_mem) =>
    `(tactic|
      (apply corresJ_castFa
       · corres_chain_mem
       · rfl))

/-! ## The `carry_mul` layouts -/

/-- The five limb cells `[b + 8i]`, `i < 5`. -/
def limbCells (b : String) : List (String × Int) :=
  [(b, 0), (b, 8), (b, 16), (b, 24), (b, 32)]

/-- The seventeen spill slots `[rsp - 8k]`, `k ≤ 16`. -/
def spillCells : List (String × Int) :=
  (List.range 17).map fun k => ("rsp", -((8 * k : Nat) : Int))

/-- The entry layout of `carry_mul`: the input arrays at `rsi` and `rdx`, the output
    array at `rdi`, the spill slots below `rsp`. -/
def carryMulEntryCells : List (String × Int) :=
  limbCells "rsi" ++ limbCells "rdx" ++ limbCells "rdi" ++ spillCells

/-- The layout of `carry_mul` after `xchg rdx, rax`: the second input array at `rax`. -/
def carryMulBodyCells : List (String × Int) :=
  limbCells "rsi" ++ limbCells "rax" ++ limbCells "rdi" ++ spillCells

/-- The register valuation used to witness the layouts: the three arrays at
    `0x10000`, `0x20000`, `0x30000`, the stack pointer at `0x40000`. -/
def witnessRegs (second : String) (r : String) : BitVec 64 :=
  if r = "rsi" then 0x10000 else if r = second then 0x20000
  else if r = "rdi" then 0x30000 else if r = "rsp" then 0x40000 else 0

/-- The machine state whose registers, flags and memory are read off an abstract
    state along `cells`. -/
def witnessState (a : AMemX) : JState 64 :=
  { regs := a.c.regs
    flags := { cf := some a.c.cf, of := some a.c.of }
    mem := fun b o => a.mem (cellAddr a.c.regs (b, o)) }

/-- `SRmem cells` holds between `witnessState a` and `a` whenever the tracked cells are
    separated under `a`'s registers. -/
theorem srmem_witnessState (cells : List (String × Int)) (a : AMemX)
    (hs : CellsSeparated cells a.c.regs) : SRmem cells (witnessState a) a :=
  ⟨⟨fun _ => rfl, rfl, rfl⟩, fun _ _ => rfl, hs⟩

/-- The entry layout of `carry_mul` is satisfiable. -/
theorem srmem_carryMulEntry_satisfiable :
    ∃ st a, SRmem carryMulEntryCells st a := by
  let a : AMemX := ⟨⟨witnessRegs "rdx", false, false⟩, fun _ => 0⟩
  refine ⟨witnessState a, a, srmem_witnessState _ a ?_⟩
  unfold CellsSeparated
  decide

/-- The body layout of `carry_mul` is satisfiable. -/
theorem srmem_carryMulBody_satisfiable :
    ∃ st a, SRmem carryMulBodyCells st a := by
  let a : AMemX := ⟨⟨witnessRegs "rax", false, false⟩, fun _ => 0⟩
  refine ⟨witnessState a, a, srmem_witnessState _ a ?_⟩
  unfold CellsSeparated
  decide

/-! ## Instruction sequences of `carry_mul` -/

/-- Lines 8–16 of `carry_mul`: three memory-source `mulx`, a register `mov`, two loads
    and three spills. -/
theorem carryMul_lines8to16_corres :
    CorresJ (SRmem carryMulBodyCells) (fun _ => True)
      (fun a =>
        mulxMemStepM "r12" "rbp" (.reg "rdx") "rsi" 0
          (storeStepM "rsp" (-0x70) (.reg "r12")
          (storeStepM "rsp" (-0x78) (.reg "rbp")
          (loadStepM "rdx" "rax" 8
          (mulxMemStepM "rbx" "r9" (.reg "rdx") "rax" 0x20
          (storeStepM "rsp" (-0x80) (.reg "rbx")
          (loadStepM "rdx" "rsi" 0
          (⟨movStep2 "r8" (.reg "rdx")
            (mulxMemStepM "rcx" "r11" (.reg "rdx") "rsi" 0x18 a).c,
            (mulxMemStepM "rcx" "r11" (.reg "rdx") "rsi" 0x18 a).mem⟩))))))))
      [.mulxMem "rcx" "r11" (.reg "rdx") "rsi" 0x18,
       .mov "r8" (.reg "rdx"),
       .loadMem "rdx" "rsi" 0,
       .storeMem "rsp" (-0x80) (.reg "rbx"),
       .mulxMem "rbx" "r9" (.reg "rdx") "rax" 0x20,
       .loadMem "rdx" "rax" 8,
       .storeMem "rsp" (-0x78) (.reg "rbp"),
       .storeMem "rsp" (-0x70) (.reg "r12"),
       .mulxMem "r12" "rbp" (.reg "rdx") "rsi" 0] := by
  corres_solve_mem

/-- Line 25 of `carry_mul`, `imul rdx, [rax + 0x8], 0x13`, as `loadMem; imul`
    (`runBlock_imulMemImm`), followed by the spill of line 26. -/
theorem carryMul_imul_corres :
    CorresJ (SRmem carryMulBodyCells) (fun _ => True)
      (fun a =>
        storeStepM "rsp" (-0x48) (.reg "rbx")
          (⟨imulStep2 "rdx" (.imm 0x13) (loadStepM "rdx" "rax" 8 a).c,
            (loadStepM "rdx" "rax" 8 a).mem⟩))
      [.loadMem "rdx" "rax" 8, .imul "rdx" (.imm 0x13),
       .storeMem "rsp" (-0x48) (.reg "rbx")] := by
  corres_solve_mem

/-- Lines 37–40 of `carry_mul`: two `add`/`adcx` pairs. -/
theorem carryMul_addAdcx_corres :
    CorresJ (SRmem carryMulBodyCells) (fun _ => True)
      (fun a =>
        ⟨adcxStep2 "rcx" "r12" (addStep2 "r10" (.reg "r11")
          (adcxStep2 "r15" "r9" (addStep2 "rbx" (.reg "rdi") a.c))), a.mem⟩)
      [.add "rbx" (.reg "rdi"), .adcx "r15" (.reg "r9"),
       .add "r10" (.reg "r11"), .adcx "rcx" (.reg "r12")] := by
  corres_solve_mem

/-! ## The abstract run over `AMemX` -/

/-- The abstract step of one instruction over `AMemX`: the step function of its
    `SRmem` leaf. Instructions and operand forms without a leaf map to the identity;
    a `CorresJ` stated with `absRunMem` holds only over blocks whose every instruction
    has a leaf. -/
def absStepMem : JInstr 64 → AMemX → AMemX
  | .mov d o => fun a => ⟨movStep2 d o a.c, a.mem⟩
  | .add d o => fun a => ⟨addStep2 d o a.c, a.mem⟩
  | .xor_ d o => fun a => ⟨xorStep2 d o a.c, a.mem⟩
  | .imul d o => fun a => ⟨imulStep2 d o a.c, a.mem⟩
  | .mulx dHi dLo (.reg ra) (.reg rb) => fun a => ⟨mulxStep2 dHi dLo ra rb a.c, a.mem⟩
  | .adcx d (.reg src) => fun a => ⟨adcxStep2 d src a.c, a.mem⟩
  | .adox d (.reg src) => fun a => ⟨adoxStep2 d src a.c, a.mem⟩
  | .adc d o => fun a => ⟨adcStep2 d o a.c, a.mem⟩
  | .inc d => fun a => ⟨incStep2 d a.c, a.mem⟩
  | .clc => fun a => ⟨clcStep2 a.c, a.mem⟩
  | .testN _ _ _ => fun a => ⟨testStep2 a.c, a.mem⟩
  | .test _ _ => fun a => ⟨testStep2 a.c, a.mem⟩
  | .lea d b i sc off => fun a => ⟨leaStep2 d b i sc off a.c, a.mem⟩
  | .movzx d sz src => fun a => ⟨movzxStep2 d sz src a.c, a.mem⟩
  | .setcc c d => fun a => ⟨setccStep2 c d a.c, a.mem⟩
  | .cmovcc c d o => fun a => ⟨cmovccStep2 c d o a.c, a.mem⟩
  | .loadMem d b o => loadStepM d b o
  | .storeMem b o src => storeStepM b o src
  | .mulxMem dHi dLo x b o => mulxMemStepM dHi dLo x b o
  | .addMem d b o => addMemStepM d b o
  | .imulMem d b o => imulMemStepM d b o
  | .imulriMem d b o k => imulriMemStepM d b o k
  | .adcxMem d b o => adcxMemStepM d b o
  | .adoxMem d b o => adoxMemStepM d b o
  | _ => id

/-- The abstract run of a block over `AMemX`: `absStepMem` folded left to right. -/
def absRunMem (c : List (JInstr 64)) (a : AMemX) : AMemX :=
  match c with
  | [] => a
  | i :: is => absRunMem is (absStepMem i a)

/-- The abstract run of a concatenation runs the second block after the first. -/
theorem absRunMem_append (c₁ c₂ : List (JInstr 64)) :
    absRunMem (c₁ ++ c₂) = fun a => absRunMem c₂ (absRunMem c₁ a) := by
  funext a
  induction c₁ generalizing a with
  | nil => rfl
  | cons i is ih => exact ih (absStepMem i a)

/-- Two blocks refining their abstract runs over `SRmem cells` compose into their
    concatenation. -/
theorem corresJ_absRunMem_append (cells : List (String × Int)) {c₁ c₂ : List (JInstr 64)}
    (h₁ : CorresJ (SRmem cells) (fun _ => True) (absRunMem c₁) c₁)
    (h₂ : CorresJ (SRmem cells) (fun _ => True) (absRunMem c₂) c₂) :
    CorresJ (SRmem cells) (fun _ => True) (absRunMem (c₁ ++ c₂)) (c₁ ++ c₂) := by
  rw [absRunMem_append]
  exact corresJ_append (SRmem cells) h₁ h₂ (fun _ _ => trivial)

/-! ## The `solinas_square` layout

`bench/cryptopt/fiat_curve25519_solinas_square.asm` reads the four input limbs at
`[rsi + 8i]`, writes the four output limbs at `[rdi + 8i]`, and spills the six
callee-saved registers `rbx`, `rbp`, `r12`–`r15` to `[rsp - 0x80]` … `[rsp - 0x58]`.
Register names are those of `NasmParse.toJInstr` (`%`-prefixed). -/

/-- The cells of `solinas_square`: input limbs, output limbs, spill slots. -/
def solinasCells : List (String × Int) :=
  [("%rsi", 0), ("%rsi", 8), ("%rsi", 16), ("%rsi", 24),
   ("%rdi", 0), ("%rdi", 8), ("%rdi", 16), ("%rdi", 24),
   ("%rsp", -0x80), ("%rsp", -0x78), ("%rsp", -0x70), ("%rsp", -0x68),
   ("%rsp", -0x60), ("%rsp", -0x58)]

/-- The register valuation used to witness the layout: the input array at `0x10000`,
    the output array at `0x30000`, the stack pointer at `0x40000`. -/
def solinasWitnessRegs (r : String) : BitVec 64 :=
  if r = "%rsi" then 0x10000 else if r = "%rdi" then 0x30000
  else if r = "%rsp" then 0x40000 else 0

/-- The `solinas_square` layout is satisfiable. -/
theorem srmem_solinas_satisfiable : ∃ st a, SRmem solinasCells st a := by
  let a : AMemX := ⟨⟨solinasWitnessRegs, false, false⟩, fun _ => 0⟩
  refine ⟨witnessState a, a, srmem_witnessState _ a ?_⟩
  unfold CellsSeparated
  decide


/-- Instructions 1–33 refine their abstract run over `SRmem solinasCells`. -/
theorem solinasSeg1_corres :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg1) solinasSeg1 := by
  unfold solinasSeg1
  corres_solve_mem

/-- Instructions 34–65 refine their abstract run over `SRmem solinasCells`. -/
theorem solinasSeg2_corres :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg2) solinasSeg2 := by
  unfold solinasSeg2
  corres_solve_mem

/-- Instructions 66–93 refine their abstract run over `SRmem solinasCells`. -/
theorem solinasSeg3_corres :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg3) solinasSeg3 := by
  unfold solinasSeg3
  corres_solve_mem

/-- Instructions 94–99 refine their abstract run over `SRmem solinasCells`. -/
theorem solinasSeg4_corres :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg4) solinasSeg4 := by
  unfold solinasSeg4
  corres_solve_mem

/-- The whole body of `solinas_square` refines its abstract run over
    `SRmem solinasCells`. -/
theorem solinasBody_corres :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasBody) solinasBody :=
  corresJ_absRunMem_append _
    (corresJ_absRunMem_append _
      (corresJ_absRunMem_append _ solinasSeg1_corres solinasSeg2_corres) solinasSeg3_corres)
    solinasSeg4_corres

/-- The parsed `solinas_square` kernel refines its abstract run over
    `SRmem solinasCells`. -/
theorem solinasSquareBlock_corres :
    CorresJ (SRmem solinasCells) (fun _ => True)
      (absRunMem X86Backend.SolinasSquareBlock.solinasSquareBlock)
      X86Backend.SolinasSquareBlock.solinasSquareBlock :=
  solinasBody_eq_block ▸ solinasBody_corres

end CatCrypt.Crypto.SecureCompilation.Ascent
