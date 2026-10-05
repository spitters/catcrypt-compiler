/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import CatCrypt.Crypto.SecureCompilation.MachineMem64

/-!
# A Lean RV64 64-bit bignum/field machine model

`RiscvModel.lean` is the owned RV64 machine layer for the scalar 32-bit-word
GP-ALU subset a ChaCha20 quarter-round needs (`addw`/`xor`/`slliw`/`srliw`/`or`).
This module is its **64-bit bignum/field** sibling — the RISC-V analogue of
`ARMBackend/ArmModel.lean`'s `BState` layer and `X86Backend`'s ADX
carry-chain layer — at the `X`-register width the s2n-bignum-class kernels
(256-bit add-mod-p, 4×64 Montgomery multiply) run on.

## The key difference from ARM/x86: RV64 has **no carry flag**

AArch64 exposes the multi-precision carry chain as real NZCV flags (`ADDS`/`ADCS`
read/write `C`); x86 has `CF`/`OF` and the ADX `ADCX`/`ADOX`. **RV64 has neither.**
The base ISA has only `ADD`/`SUB` (no flag output) and the `SLTU` *set-less-than-
unsigned* comparator. So a carry/borrow is **synthesized**, not read from a flag:

* the carry out of `t := a + b` is `SLTU cout, t, a` — `cout = (t <ᵘ a) = 1` iff
  `a + b` wrapped (RISC-V manual, "Integer Computational Instructions", the
  canonical add-carry idiom);
* the borrow out of `t := a - b` is `SLTU borrow, a, b` — `borrow = (a <ᵘ b)`.

This makes a RISC-V bignum carry chain **instruction-heavier** than ARM/x86: each
`ADCS` (one A64 instruction) becomes `add ; sltu ; add ; sltu ; or` (five RV64
instructions) in the general add-with-carry-in case, and each `SBCS` likewise.
And RV64 has **no conditional-select** (`CSEL`); the constant-time
conditional-subtract reduce is a **branch-free mask select**
`mask := 0 - cond ; z := (x_sub &&& mask) ||| (x &&& ~~~mask)`. We document this
cost — the RISC-V `bignum_add_p256` lowers to materially more
instructions than the A64 one — and this is exactly the price of the missing
flag register, not a backend inefficiency.

## The 64-bit RV64 ops we model (the bignum/field subset)

| mnemonic | shape          | op (64-bit view)                              |
|----------|----------------|-----------------------------------------------|
| `ADD`    | `rd, rs1, rs2` | `rd := rs1 + rs2`  (wrapping 64-bit)          |
| `SUB`    | `rd, rs1, rs2` | `rd := rs1 - rs2`  (wrapping 64-bit)          |
| `SLTU`   | `rd, rs1, rs2` | `rd := if rs1 <ᵘ rs2 then 1 else 0` (carry)   |
| `MUL`    | `rd, rs1, rs2` | `rd := (rs1 * rs2) mod 2⁶⁴`  (low half)       |
| `MULHU`  | `rd, rs1, rs2` | `rd := (rs1 * rs2) >>> 64`   (high half, u×u) |
| `AND`    | `rd, rs1, rs2` | `rd := rs1 &&& rs2`                           |
| `OR`     | `rd, rs1, rs2` | `rd := rs1 ||| rs2`                           |
| `XOR`    | `rd, rs1, rs2` | `rd := rs1 ^^^ rs2`                           |
| `LI`     | `rd, #imm`     | `rd := imm`  (pseudo: `lui`+`addi`)           |
| `MV`     | `rd, rs`       | `rd := rs`                                     |

`x0` (`zero`) is hard-wired to `0`. `MUL`/`MULHU` are the RV64 M-extension widening
product (the low/high halves of the 64×64 product; the low half is signedness-
independent, so `MUL` is the low limb and `MULHU` the unsigned high limb the bignum
multiply needs). `LI` is the assembler `li` pseudo-op (materialises a 64-bit
constant); modelled as a direct register write. Loads/stores at the function
boundary of the straight-line kernels are ABI scaffolding rendered by the printer.

Section 4 adds the memory-and-branch fragment `RMInst64` (`ADDI`, `LD`, `SD`, `BNE`) over
the state `RMState64`, which carries a byte-addressed memory (`MachineMem64`) and the
program counter.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. The 64-bit RV64 register state

A 64-bit `X` register value is a `BitVec 64`; the file is a `String → BitVec 64`
function keyed by register name. An absent name (and `zero`/`x0`) reads as `0`.
There is **no carry flag** in the state — the only structural difference from the
A64 `BState`, and the reason carries are synthesized with `SLTU`. -/

/-- A 64-bit RV64 `X` register value. -/
abbrev X64R : Type := BitVec 64

/-- The RV64 64-bit GP register file: a name → `X64R` function. An absent name
    (e.g. an uninitialised temporary) and the zero register `zero`/`x0` read as
    `0`. There is no carry flag (RV64 has none). -/
structure RState64 where
  /-- The 64-bit integer register file (`x0 … x31` / ABI names, by string). -/
  regs : String → X64R

namespace RState64

/-- Read a 64-bit register. The zero register `zero`/`x0` and any absent name
    read as `0`. -/
@[simp] def get (s : RState64) (r : String) : X64R :=
  if r = "zero" ∨ r = "x0" then 0 else s.regs r

/-- Write a 64-bit register, leaving the others unchanged. Writes to `zero`/`x0`
    are discarded (the RISC-V zero register is hard-wired to 0). -/
def set (s : RState64) (r : String) (v : X64R) : RState64 :=
  if r = "zero" ∨ r = "x0" then s
  else { regs := fun r' => if r' = r then v else s.regs r' }

@[simp] theorem get_set_same (s : RState64) (r : String) (v : X64R)
    (h : ¬ (r = "zero" ∨ r = "x0")) : (s.set r v).get r = v := by
  simp [set, get, h]

@[simp] theorem get_set_other (s : RState64) (r r' : String) (v : X64R)
    (h : r' ≠ r) : (s.set r v).get r' = s.get r' := by
  by_cases hz : r' = "zero" ∨ r' = "x0"
  · simp [get, hz]
  · simp only [get, hz, if_false, set]
    by_cases hr : r = "zero" ∨ r = "x0"
    · simp [hr]
    · simp [hr, h]

end RState64

/-! ## 2. Per-op 64-bit RV64 ALU semantics

Each op is the obvious 64-bit integer op over `BitVec 64`, auditable against the
RISC-V ISA manual by eye. `opSltu` is the *set-less-than-unsigned* comparator
that synthesizes carries/borrows; `opMul64`/`opMulhu` are the M-extension
widening-product halves. -/

/-- `ADD` op: wrapping 64-bit add. -/
@[simp] def opAdd64 (a b : X64R) : X64R := a + b

/-- `SUB` op: wrapping 64-bit subtract. -/
@[simp] def opSub64 (a b : X64R) : X64R := a - b

/-- `SLTU` op: set-less-than-unsigned — `1` if `a <ᵘ b`, else `0`. This is the
    carry/borrow-synthesis primitive: the carry out of `a + b` is
    `opSltu (a + b) a`, and the borrow out of `a - b` is `opSltu a b`. -/
@[simp] def opSltu (a b : X64R) : X64R := if a.toNat < b.toNat then 1 else 0

/-- `AND`/`OR`/`XOR` 64-bit. -/
@[simp] def opAnd64 (a b : X64R) : X64R := a &&& b
@[simp] def opOr64  (a b : X64R) : X64R := a ||| b
@[simp] def opXor64 (a b : X64R) : X64R := a ^^^ b

/-- `MUL` op: the low 64 bits of the 64×64 product (signedness-independent). -/
@[simp] def opMul64 (a b : X64R) : X64R := a * b

/-- `MULHU` op: the high 64 bits of the *unsigned* 64×64 product. -/
@[simp] def opMulhu (a b : X64R) : X64R :=
  BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)

/-! ### Carry-synthesis correctness witnesses

The SLTU idiom is the verified-by-`native_decide` source of carry/borrow bits. -/

/-- **The add-carry idiom is correct.** The carry out of `t := a + b` is exactly
    `SLTU t, a` (`t <ᵘ a`): `t` wraps below `a` iff the true sum `≥ 2⁶⁴`. -/
theorem sltu_add_carry (a b : X64R) :
    (opSltu (opAdd64 a b) a).toNat = (if a.toNat + b.toNat ≥ 2 ^ 64 then 1 else 0) := by
  simp only [opSltu, opAdd64, BitVec.add_def, BitVec.toNat_ofNat]
  by_cases h : a.toNat + b.toNat ≥ 2 ^ 64
  · have hb : b.toNat < 2 ^ 64 := b.isLt
    have ha : a.toNat < 2 ^ 64 := a.isLt
    rw [if_pos h]
    have : (a.toNat + b.toNat) % 2 ^ 64 = a.toNat + b.toNat - 2 ^ 64 := by omega
    rw [this, if_pos (by omega)]; rfl
  · have ha : a.toNat < 2 ^ 64 := a.isLt
    rw [if_neg h]
    have : (a.toNat + b.toNat) % 2 ^ 64 = a.toNat + b.toNat := Nat.mod_eq_of_lt (by omega)
    rw [this, if_neg (by omega)]; rfl

/-- **The sub-borrow idiom is correct.** The borrow out of `a - b` is exactly
    `SLTU a, b` (`a <ᵘ b`). -/
theorem sltu_sub_borrow (a b : X64R) :
    opSltu a b = (if a.toNat < b.toNat then 1 else 0) := rfl

/-! ## 3. The 64-bit RV64 bignum instruction set

The machine-level analogue of `ARMBackend.BInst`, but **flagless** — there is no
`*S` flag-setting form and no `CSEL`; carries are produced by explicit `SLTU`
instructions, and the conditional select is a branch-free mask. -/

/-- A single 64-bit RV64 bignum/field instruction over named registers. -/
inductive RInst64 where
  /-- `ADD rd, rs1, rs2` — 64-bit add. -/
  | add (d a b : String)
  /-- `SUB rd, rs1, rs2` — 64-bit subtract. -/
  | sub (d a b : String)
  /-- `SLTU rd, rs1, rs2` — set-less-than-unsigned (carry/borrow synthesis). -/
  | sltu (d a b : String)
  /-- `AND rd, rs1, rs2`. -/
  | and (d a b : String)
  /-- `OR  rd, rs1, rs2`. -/
  | or  (d a b : String)
  /-- `XOR rd, rs1, rs2`. -/
  | xor (d a b : String)
  /-- `MUL rd, rs1, rs2` — low 64 of the product. -/
  | mul (d a b : String)
  /-- `MULHU rd, rs1, rs2` — high 64 of the unsigned product. -/
  | mulhu (d a b : String)
  /-- `LI rd, #imm` — load a 64-bit immediate (assembler pseudo-op). -/
  | li (d : String) (imm : Nat)
  /-- `MV rd, rs` — register move (pseudo for `ADDI rd, rs, 0`). -/
  | mv (d s : String)
  /-- `SRLI rd, rs, #sh` — logical shift right by an immediate below 64. -/
  | srli (d a : String) (sh : Fin 64)
  /-- `SLLI rd, rs, #sh` — logical shift left by an immediate below 64. -/
  | slli (d a : String) (sh : Fin 64)
  deriving Repr, DecidableEq

/-- The semantics of one 64-bit RV64 instruction. -/
def evalRInst64 (s : RState64) : RInst64 → RState64
  | .add  d a b => s.set d (opAdd64 (s.get a) (s.get b))
  | .sub  d a b => s.set d (opSub64 (s.get a) (s.get b))
  | .sltu d a b => s.set d (opSltu (s.get a) (s.get b))
  | .and  d a b => s.set d (opAnd64 (s.get a) (s.get b))
  | .or   d a b => s.set d (opOr64  (s.get a) (s.get b))
  | .xor  d a b => s.set d (opXor64 (s.get a) (s.get b))
  | .mul  d a b => s.set d (opMul64 (s.get a) (s.get b))
  | .mulhu d a b => s.set d (opMulhu (s.get a) (s.get b))
  | .li   d imm => s.set d (BitVec.ofNat 64 imm)
  | .mv   d a   => s.set d (s.get a)
  | .srli d a sh => s.set d (s.get a >>> sh.val)
  | .slli d a sh => s.set d (s.get a <<< sh.val)

/-- `runRBlock64`: a straight-line fold of `evalRInst64`. -/
def runRBlock64 (s : RState64) : List RInst64 → RState64
  | [] => s
  | i :: is => runRBlock64 (evalRInst64 s i) is

@[simp] theorem runRBlock64_nil (s : RState64) : runRBlock64 s [] = s := rfl

@[simp] theorem runRBlock64_cons (s : RState64) (i : RInst64) (is : List RInst64) :
    runRBlock64 s (i :: is) = runRBlock64 (evalRInst64 s i) is := rfl

theorem runRBlock64_append (xs ys : List RInst64) (s : RState64) :
    runRBlock64 s (xs ++ ys) = runRBlock64 (runRBlock64 s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runRBlock64_cons]; exact ih _

/-! ## 4. Memory and branches

`RMInst64` extends `RInst64` by the RV64I instructions a word-array loop needs: `ADDI` with a
non-zero immediate (pointer and counter steps), the doubleword load `LD rd, off(rs1)` and
store `SD rs2, off(rs1)` with base+offset addressing, and the conditional branch
`BNE rs1, rs2, off`. `RMState64` adds to the register file the byte-addressed data memory
`MachineMem64.Mem64` and the program counter. The offsets are the signed byte displacements
of the instruction formats: 12-bit for `ADDI`, `LD`, `SD`, 13-bit and even for `BNE`. -/

/-- An RV64 instruction of the memory-and-branch fragment: a register instruction of
    `RInst64`, `ADDI`, `LD`, `SD` or `BNE`. -/
inductive RMInst64 where
  /-- A register instruction of `RInst64`. -/
  | alu (i : RInst64)
  /-- `ADDI rd, rs1, imm` — add a sign-extended 12-bit immediate. -/
  | addi (d a : String) (imm : Int)
  /-- `LD rd, off(rs1)` — load the doubleword at `rs1 + off`. -/
  | ld (d base : String) (off : Int)
  /-- `SD rs2, off(rs1)` — store `rs2` as the doubleword at `rs1 + off`. -/
  | sd (src base : String) (off : Int)
  /-- `BNE rs1, rs2, off` — branch by the byte offset `off` when `rs1 ≠ rs2`. -/
  | bne (a b : String) (off : Int)
  deriving Repr, DecidableEq

/-- The RV64 machine state of the memory-and-branch fragment: the register file, the data
    memory and the program counter (a byte address). -/
structure RMState64 where
  /-- The integer register file. -/
  regs : RState64
  /-- The byte-addressed data memory. -/
  mem : MachineMem64.Mem64
  /-- The program counter. -/
  pc : BitVec 64

/-- The effective address `rs1 + off` of a load or store. -/
def rvAddr (s : RState64) (base : String) (off : Int) : BitVec 64 :=
  s.get base + BitVec.ofInt 64 off

/-- **The step of one instruction of the memory-and-branch fragment.** A register
    instruction runs `evalRInst64`; `LD` reads `MachineMem64.read64` at the effective address,
    `SD` writes `MachineMem64.write64` there; `BNE` adds its offset to the program counter when
    its registers differ. Every other instruction advances the program counter by 4. -/
def evalRMInst64 (s : RMState64) : RMInst64 → RMState64
  | .alu i => { s with regs := evalRInst64 s.regs i, pc := s.pc + 4 }
  | .addi d a imm =>
      { s with regs := s.regs.set d (s.regs.get a + BitVec.ofInt 64 imm), pc := s.pc + 4 }
  | .ld d base off =>
      { s with regs := s.regs.set d (MachineMem64.read64 s.mem (rvAddr s.regs base off)),
               pc := s.pc + 4 }
  | .sd src base off =>
      { s with mem := MachineMem64.write64 s.mem (rvAddr s.regs base off) (s.regs.get src),
               pc := s.pc + 4 }
  | .bne a b off =>
      { s with pc := if s.regs.get a ≠ s.regs.get b then s.pc + BitVec.ofInt 64 off
                     else s.pc + 4 }

/-- A straight-line fold of `evalRMInst64`. -/
def runRMBlock64 (s : RMState64) : List RMInst64 → RMState64
  | [] => s
  | i :: is => runRMBlock64 (evalRMInst64 s i) is

@[simp] theorem runRMBlock64_nil (s : RMState64) : runRMBlock64 s [] = s := rfl

@[simp] theorem runRMBlock64_cons (s : RMState64) (i : RMInst64) (is : List RMInst64) :
    runRMBlock64 s (i :: is) = runRMBlock64 (evalRMInst64 s i) is := rfl

theorem runRMBlock64_append (xs ys : List RMInst64) (s : RMState64) :
    runRMBlock64 s (xs ++ ys) = runRMBlock64 (runRMBlock64 s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runRMBlock64_cons]; exact ih _

/-- On the registers, a register instruction of the fragment is the `RInst64` step. -/
theorem evalRMInst64_alu_regs (s : RMState64) (i : RInst64) :
    (evalRMInst64 s (.alu i)).regs = evalRInst64 s.regs i := rfl

/-! ## 5. Differential-validation pins (the 64-bit RV64 anchor)

Unit-level witnesses for the new ops; the integration witness is the
`bignum_add_p256` KAT (`RiscvBignumKernel.addp256_kat`) and the real
qemu-riscv64 run-KAT in `bench/riscv_compare/`. -/

/-- `MUL`/`MULHU` pin: `(2⁶⁴-1)² = 0xfffffffffffffffe_0000000000000001`, so
    `MUL = 1` (low), `MULHU = 0xfffffffffffffffe` (high). -/
example : opMul64 (BitVec.allOnes 64) (BitVec.allOnes 64) = 1
    ∧ opMulhu (BitVec.allOnes 64) (BitVec.allOnes 64)
        = BitVec.ofNat 64 0xfffffffffffffffe := by native_decide

/-- `SLTU` carry pin: `(2⁶⁴-1) + 1` wraps to `0`, and `SLTU 0, (2⁶⁴-1) = 1` —
    the carry was synthesized. -/
example : opSltu (opAdd64 (BitVec.allOnes 64) 1) (BitVec.allOnes 64) = 1 := by
  native_decide

/-- `SLTU` no-carry pin: `1 + 2 = 3`, `SLTU 3, 1 = 0` (no wrap). -/
example : opSltu (opAdd64 1 2) 1 = 0 := by native_decide

/-- `SLTU` borrow pin: `0 - 1` borrows, `SLTU 0, 1 = 1`. -/
example : opSltu (0 : X64R) 1 = 1 := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend
