/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel64
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.BitVec
public import Mathlib.Algebra.Group.Basic

/-!
# Sail refinement for the 64-bit RV64 model (`RiscvModel64`)

This connects our **trusted hand-written effect semantics** `evalRInst64` (the
RV64 64-bit bignum/field ALU + carry-synthesis model) to an in-file excerpt of
the model generated from the `riscv/sail-riscv` Sail spec by the
[Sail `-lean` backend](https://github.com/opencompl/sail-riscv-lean) (commit
`9eba3f07`; upstream not vendored — see the provenance section below).

Unlike `RiscvModel.lean` (the 32-bit `*W`-word view, which needs a low-32
simulation relation to bridge to Sail's sign-extending 64-bit registers),
`RiscvModel64`'s `X64R = BitVec 64` registers line up with Sail's `xlenbits`
directly — so the connection is width-clean.

## What is real vs. transcribed vs. simplified

* **Real / tested:** `opAdd64`, `opSub64`, `opSltu`, `opAnd64`, `opOr64`,
  `opXor64` are the *real* `RiscvModel64` ops (imported above), unchanged.
* **Transcribed (in-file excerpt):** `execute_RTYPE` is a hand-pasted excerpt of
  the generated `opencompl/sail-riscv-lean` `LeanRV64D/InstsEnd.lean` (commit
  `9eba3f07`); the BitVec primitives are the one-line wrappers from
  `rems-project/lean-sail`. Per project decision, pasting the generated text
  in-file (rather than `require`-ing the 170k-line monolith) is the accepted
  integration shape — so **upstream is not vendored**: the
  `sail-riscv-lean`/`lean-sail` sources are neither vendored nor `require`d in
  this repo, only the individual clauses below are in-tree, and the
  transcription's fidelity to the generated file is not machine-checked in-tree;
  it rests on the manual copy having been done correctly at the time.
* **Simplified (accepted, low-risk):** `SailM` is a thin `StateM` over a flat
  `BitVec 5 → BitVec 64` register file rather than lean-sail's
  `PreSailM`/`SequentialState`; the `xreg_write_callback` (`:= ()`, register
  preserving) is dropped. On this exception-free GP subset both are observably
  equal — the only cost of the real monad is `ExtDHashMap` plumbing.

## Result

For each core RV64 ALU / carry-synthesis op, the value the transcribed Sail
`execute_RTYPE` clause writes to `rd` equals our `RiscvModel64` op applied to the
operands — i.e. our hand-written effect semantics matches the in-file excerpt of
the sail-riscv-lean generated output (commit `9eba3f07`; upstream not vendored).

`MUL`/`MULHU` route through Sail's `mult_to_bits_half` / `to_bits_truncate`
helper chain; the 128-bit-product BitVec lemmas `mulhu_value` (L1) and `mul_value`
(L2) connect them to `opMulhu` / `opMul64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Ref

/-! ## Sail runtime primitives (verbatim one-liners from `rems-project/lean-sail`) -/

namespace Sail.BitVec
def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) := x.extractLsb hi lo
end Sail.BitVec

def shift_bits_left {n m : Nat} (bv : BitVec n) (sh : BitVec m) : BitVec n := bv <<< sh
def shift_bits_right {n m : Nat} (bv : BitVec n) (sh : BitVec m) : BitVec n := bv >>> sh
def shift_bits_right_arith {n m : Nat} (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  BitVec.sshiftRight bv sh.toNat
def zero_extend {m k_n : Nat} (v : BitVec k_n) : BitVec m := v.zeroExtend m
def bool_to_bit (b : Bool) : BitVec 1 := if b then 1 else 0
def zopz0zI_s {n : Nat} (x y : BitVec n) : Bool := x.slt y
def zopz0zI_u {n : Nat} (x y : BitVec n) : Bool := x.ult y
abbrev log2_xlen : Nat := 6

/-! ## Transcribed types (in-file excerpts from generated `LeanRV64D/Defs.lean`) -/

inductive regidx where | Regidx (_ : BitVec 5)
inductive rop where | ADD | SLT | SLTU | AND | OR | XOR | SLL | SRL | SUB | SRA
inductive ExecutionResult where | Retire_Success (_ : Unit) | Illegal_Instruction (_ : Unit)
abbrev RETIRE_SUCCESS : ExecutionResult := .Retire_Success ()

/-! ## Thin faithful state monad + register accessors (fold of generated `Regs.lean`) -/

abbrev RegFile := BitVec 5 → BitVec 64
abbrev SailM := StateM RegFile

def upd (s : RegFile) (i : BitVec 5) (v : BitVec 64) : RegFile := fun j => if j = i then v else s j

/-- x0 hardwired to 0 (generated `rX`). -/
def rX_bits (i : regidx) : SailM (BitVec 64) := do
  let .Regidx b := i
  if b.toNat = 0 then pure 0 else pure ((← get) b)

/-- write to x0 ignored (generated `wX`); callback dropped (register preserving). -/
def wX_bits (i : regidx) (data : BitVec 64) : SailM Unit := do
  let .Regidx b := i
  if b.toNat = 0 then pure () else modify (upd · b data)

/-! ## Generated execute clause — VERBATIM from `LeanRV64D/InstsEnd.lean:67736` -/

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | .SLT =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .SLTU =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | .OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | .XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | .SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen - 1) 0)))
      | .SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen - 1) 0)))
      | .SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | .SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen - 1) 0)))))
  (pure RETIRE_SUCCESS)

/-! ## Transcribed M-extension + shift + ITYPE machinery (in-file excerpts from generated `LeanRV64D`) -/

def BitVec.toNatInt {w : Nat} (x : BitVec w) : Int := (x.toNat : Int)
def sign_extend {m k_n : Nat} (v : BitVec k_n) : BitVec m := v.signExtend m

inductive Signedness where | Signed | Unsigned
inductive VectorHalf where | High | Low
structure mul_op where
  result_part : VectorHalf
  signed_rs1 : Signedness
  signed_rs2 : Signedness
inductive iop where | ADDI | SLTI | SLTIU | XORI | ORI | ANDI
inductive sop where | SLLI | SRLI | SRAI

/-- `lean-sail` `Sail/Sail.lean:238`. -/
def get_slice_int (len : Nat) (n : Int) (lo : Nat) : BitVec len :=
  BitVec.extractLsb' lo len (BitVec.ofInt (lo + len + 1) n)
/-- generated `Prelude.lean:334`. -/
def to_bits_truncate {l : Nat} (n : Int) : BitVec l := get_slice_int l n 0
/-- generated `Arithmetic.lean:258`, specialized to `l = xlen = 64` (the only width we emit). -/
def mult_to_bits_half (sign1 sign2 : Signedness) (rs1_bits rs2_bits : BitVec 64)
    (result_part : VectorHalf) : BitVec 64 :=
  let rs1_int : Int := match sign1 with | .Signed => rs1_bits.toInt | .Unsigned => BitVec.toNatInt rs1_bits
  let rs2_int : Int := match sign2 with | .Signed => rs2_bits.toInt | .Unsigned => BitVec.toNatInt rs2_bits
  let result_wide : BitVec 128 := to_bits_truncate (rs1_int * rs2_int)
  match result_part with
  | .High => Sail.BitVec.extractLsb result_wide 127 64
  | .Low => Sail.BitVec.extractLsb result_wide 63 0

/-- generated `InstsEnd.lean:68825`. -/
def execute_MUL (rs2 rs1 rd : regidx) (mop : mul_op) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (mult_to_bits_half mop.signed_rs1 mop.signed_rs2 rs1_bits rs2_bits mop.result_part))
  (pure RETIRE_SUCCESS)

/-- generated `InstsEnd.lean:67574`. -/
def execute_SHIFTIOP (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen - 1) 0)
  (wX_bits rd
    (← do
      match op with
      | .SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | .SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | .SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)

/-- generated `InstsEnd.lean:69227`. -/
def execute_ITYPE (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : BitVec 64 := (sign_extend (m := 64) imm)
  (wX_bits rd
    (← do
      match op with
      | .ADDI => (pure ((← (rX_bits rs1)) + immext))
      | .ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | .ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | .XORI => (pure ((← (rX_bits rs1)) ^^^ immext))
      | .SLTI => (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) immext))))
      | .SLTIU => (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) immext))))))
  (pure RETIRE_SUCCESS)

/-! ## The BitVec lemmas (L1, L2): Sail product halves = our M-ext ops -/

/-- L1: Sail `MULHU` value = `opMulhu` (high 64 of the 128-bit unsigned product). -/
theorem mulhu_value (x y : BitVec 64) :
    mult_to_bits_half .Unsigned .Unsigned x y .High = opMulhu x y := by
  simp only [mult_to_bits_half, to_bits_truncate, get_slice_int, Sail.BitVec.extractLsb,
    BitVec.toNatInt, opMulhu]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hy : y.toNat < 2 ^ 64 := y.isLt
  have hP : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 128 := by norm_num
  have hcast : BitVec.ofInt 129 ((x.toNat : Int) * (y.toNat : Int))
      = BitVec.ofNat 129 (x.toNat * y.toNat) := by
    rw [← Nat.cast_mul, BitVec.ofInt_natCast]
  rw [hcast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  norm_num
  omega

/-- L2: Sail `MUL` value = `opMul64` (low 64 of the product; signedness-independent). -/
theorem mul_value (x y : BitVec 64) :
    mult_to_bits_half .Signed .Signed x y .Low = opMul64 x y := by
  simp only [mult_to_bits_half, to_bits_truncate, get_slice_int, Sail.BitVec.extractLsb, opMul64]
  rw [show x * y = BitVec.ofInt 64 (x.toInt * y.toInt) from by
        rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  norm_num
  omega

/-! ## Refinement: the Sail clause's written value = the real `RiscvModel64` op -/

/-- x0-aware read, matching the Sail runtime and `RState64.get`. -/
def rget (s : RegFile) (i : BitVec 5) : BitVec 64 := if i.toNat = 0 then 0 else s i

/-- Run a clause and read register `rd`'s final value. -/
def runRd (m : SailM ExecutionResult) (s : RegFile) (rd : BitVec 5) : BitVec 64 := (m.run s).2 rd

/-- The verbatim Sail `ADD` writes our `opAdd64`. -/
theorem rtype_add (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .ADD) s rd = opAdd64 (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opAdd64, h1, h2, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

theorem rtype_sub (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .SUB) s rd = opSub64 (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opSub64, h1, h2, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

theorem rtype_and (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .AND) s rd = opAnd64 (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opAnd64, h1, h2, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

theorem rtype_or (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .OR) s rd = opOr64 (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opOr64, h1, h2, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

theorem rtype_xor (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .XOR) s rd = opXor64 (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opXor64, h1, h2, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- The carry-synthesis primitive: Sail `SLTU` writes our `opSltu`. -/
theorem rtype_sltu (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .SLTU) s rd = opSltu (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opSltu, zero_extend, bool_to_bit,
      zopz0zI_u, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.zero_mod,
      h1, h2, hrd, bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe,
      MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet] <;>
    (try split) <;> simp_all

/-- Sail `MUL` (low) writes our `opMul64`. -/
theorem rtype_mul (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_MUL ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ ⟨.Low, .Signed, .Signed⟩) s rd
      = opMul64 (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_MUL, rX_bits, wX_bits, rget, upd, mul_value, h1, h2, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- Sail `MULHU` writes our `opMulhu` (the bignum high-word primitive). -/
theorem rtype_mulhu (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_MUL ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ ⟨.High, .Unsigned, .Unsigned⟩) s rd
      = opMulhu (rget s rs1) (rget s rs2) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_MUL, rX_bits, wX_bits, rget, upd, mulhu_value, h1, h2, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- Sail `ADDI rd, rs, 0` (the `MV` pseudo-op) writes `rget s rs1`. -/
theorem itype_mv (s : RegFile) (rs1 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    runRd (execute_ITYPE 0 ⟨rs1⟩ ⟨rd⟩ .ADDI) s rd = rget s rs1 := by
  by_cases h1 : rs1.toNat = 0 <;>
    simp [runRd, execute_ITYPE, rX_bits, wX_bits, rget, upd, sign_extend, h1, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- L5 shift bridge: the `BitVec 6` shift amount of value `sh < 64` has `toNat = sh`
    (added to the SLLI/SRLI `simp` sets, which normalize a BitVec-shift to a `.toNat` shift). -/
theorem shamt6_toNat (sh : Nat) (hsh : sh < 64) :
    (Sail.BitVec.extractLsb (BitVec.ofNat 6 sh) 5 0).toNat = sh := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat]
  norm_num
  omega

/-- Sail `SLLI` writes our `slli` value `rget s rs1 <<< sh`. -/
theorem shiftiop_slli (s : RegFile) (rs1 rd : BitVec 5) (sh : Nat) (hsh : sh < 64)
    (hrd : rd.toNat ≠ 0) :
    runRd (execute_SHIFTIOP (BitVec.ofNat 6 sh) ⟨rs1⟩ ⟨rd⟩ .SLLI) s rd = (rget s rs1) <<< sh := by
  by_cases h1 : rs1.toNat = 0 <;>
    simp [runRd, execute_SHIFTIOP, rX_bits, wX_bits, rget, upd, shift_bits_left,
      BitVec.shiftLeft_eq', shamt6_toNat sh hsh, h1, hrd, bind, StateT.bind, StateT.run,
      pure, StateT.pure, get, getThe, MonadStateOf.get, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- Sail `SRLI` writes our `srli` value `rget s rs1 >>> sh`. -/
theorem shiftiop_srli (s : RegFile) (rs1 rd : BitVec 5) (sh : Nat) (hsh : sh < 64)
    (hrd : rd.toNat ≠ 0) :
    runRd (execute_SHIFTIOP (BitVec.ofNat 6 sh) ⟨rs1⟩ ⟨rd⟩ .SRLI) s rd = (rget s rs1) >>> sh := by
  by_cases h1 : rs1.toNat = 0 <;>
    simp [runRd, execute_SHIFTIOP, rX_bits, wX_bits, rget, upd, shift_bits_right,
      BitVec.ushiftRight_eq', shamt6_toNat sh hsh, h1, hrd, bind, StateT.bind, StateT.run,
      pure, StateT.pure, get, getThe, MonadStateOf.get, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-! `li rd, imm` is an RV assembler pseudo-op (`LUI`+`ADDI`, or `ADDI x0`), with no single Sail
clause, so it is not given a per-clause equivalence here — it is a `RiscvModel64` convenience
expanded by the lowering, not a machine instruction. -/

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Ref
