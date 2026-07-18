/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel
import Mathlib.Tactic.NormNum
import Mathlib.Data.BitVec
import Mathlib.Algebra.Group.Basic

/-!
# Sail refinement for the 32-bit `*W`-word RV64 model (`RiscvModel`)

`SailRiscv64Refinement.lean` connected `RiscvModel64` (64-bit X registers) to Sail directly,
because its widths match Sail's `xlenbits`. `RiscvModel` is the **32-bit `*W`-word** view
(ChaCha20 / SHA-256): its registers are `R32 = BitVec 32`, while the RV64 Sail model holds
64-bit registers and the `*W` instructions sign-extend their 32-bit result.

We connect it the **same way** (vendoring the verbatim Sail clauses), with the equivalence
stated at the **low 32 bits**: the low 32 bits of what the Sail clause writes equal our
`R32` op applied to the low 32 bits of the operands. This is exactly the soundness of the
32-bit-word abstraction `RiscvModel` currently *trusts* (the docstring's "auditable by eye"):
here it is *proven* against the golden 64-bit Sail model.

Genuine lemmas (vs plumbing): `lo32_signExtend` (truncation undoes `*W` sign-extension),
`lo32_eq_setWidth` + `BitVec.setWidth_{and,or,xor}` (low-32 distributes over the 64-bit logical
ops our model treats as 32-bit), and `rotateRight_eq_shift_or` (L3, the rotate = shift-or fact
behind `RORIW`). Provenance/simplifications as in the 64-bit file (verbatim clauses from
`opencompl/sail-riscv-lean` commit `9eba3f07`; thin `StateM`; `xreg_write_callback` dropped).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv32Ref

/-! ## Sail runtime primitives + vendored types -/

namespace Sail.BitVec
def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) := x.extractLsb hi lo
end Sail.BitVec

def BitVec.toNatInt {w : Nat} (x : BitVec w) : Int := (x.toNat : Int)
def sign_extend {m k_n : Nat} (v : BitVec k_n) : BitVec m := BitVec.signExtend m v
def shift_bits_left {n m : Nat} (bv : BitVec n) (sh : BitVec m) : BitVec n := bv <<< sh
def shift_bits_right {n m : Nat} (bv : BitVec n) (sh : BitVec m) : BitVec n := bv >>> sh
def shift_bits_right_arith {n m : Nat} (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  BitVec.sshiftRight bv sh.toNat
def rotater {n : Nat} (v : BitVec n) (k : Int) : BitVec n := v.rotateRight k.toNat
def rotate_bits_right {km kn : Nat} (value : BitVec km) (shift : BitVec kn) : BitVec km :=
  rotater value (BitVec.toNatInt shift)

inductive regidx where | Regidx (_ : BitVec 5)
inductive rop  where | ADD | SLT | SLTU | AND | OR | XOR | SLL | SRL | SUB | SRA
inductive ropw where | ADDW | SUBW | SLLW | SRLW | SRAW
inductive sopw where | SLLIW | SRLIW | SRAIW
inductive ExecutionResult where | Retire_Success (_ : Unit) | Illegal_Instruction (_ : Unit)
abbrev RETIRE_SUCCESS : ExecutionResult := .Retire_Success ()

/-! ## Thin state monad + register accessors -/

abbrev RegFile := BitVec 5 → BitVec 64
abbrev SailM := StateM RegFile

def upd (s : RegFile) (i : BitVec 5) (v : BitVec 64) : RegFile := fun j => if j = i then v else s j
def rX_bits (i : regidx) : SailM (BitVec 64) := do
  let .Regidx b := i
  if b.toNat = 0 then pure 0 else pure ((← get) b)
def wX_bits (i : regidx) (data : BitVec 64) : SailM Unit := do
  let .Regidx b := i
  if b.toNat = 0 then pure () else modify (upd · b data)
def rget (s : RegFile) (i : BitVec 5) : BitVec 64 := if i.toNat = 0 then 0 else s i
def runRd (m : SailM ExecutionResult) (s : RegFile) (rd : BitVec 5) : BitVec 64 := (m.run s).2 rd

/-! ## Generated execute clauses — VERBATIM from `LeanRV64D/InstsEnd.lean` -/

/-- `:67723`. -/
def execute_RTYPEW (rs2 rs1 rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .ADDW => (rs1_val + rs2_val)
    | .SUBW => (rs1_val - rs2_val)
    | .SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

/-- `:67736` (logical ops have no `*W` form; emitted as the 64-bit `RTYPE`). -/
def execute_RTYPE (rs2 rs1 rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | .OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | .XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | _ => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))))
  (pure RETIRE_SUCCESS)

/-- `:67564`. -/
def execute_SHIFTIWOP (shamt : BitVec 5) (rs1 rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .SLLIW => (shift_bits_left rs1_val shamt)
    | .SRLIW => (shift_bits_right rs1_val shamt)
    | .SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

/-- `:67762` (Zbb single-instruction rotate). -/
def execute_RORIW (shamt : BitVec 5) (rs1 rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd
    (sign_extend (m := 64)
      (rotate_bits_right (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0) shamt)))
  (pure RETIRE_SUCCESS)

/-! ## The genuine BitVec lemmas -/

/-- Low 32 bits of a 64-bit value = `setWidth 32` (definitional via `toNat`). -/
theorem lo32_eq_setWidth (x : BitVec 64) : x.extractLsb 31 0 = x.setWidth 32 :=
  BitVec.eq_of_toNat_eq rfl

/-- Truncating a `*W` sign-extended result back to 32 bits recovers it. -/
theorem lo32_signExtend (v : BitVec 32) : (BitVec.signExtend 64 v).extractLsb 31 0 = v := by
  rw [lo32_eq_setWidth]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_signExtend]
  rcases v.msb <;> simp <;> omega

/-- L3: `rotateRight` = the shift-or rotate idiom, on `BitVec 32`, count `< 32`. -/
theorem rotateRight_eq_shift_or (v : BitVec 32) (n : Nat) (hn : n < 32) :
    v.rotateRight n = (v >>> n) ||| (v <<< (32 - n)) := by
  rw [BitVec.rotateRight, Nat.mod_eq_of_lt hn, BitVec.rotateRightAux]

/-- L5 shift bridge: a `BitVec 5` shift amount of value `m < 32` has `toNat = m`. -/
theorem shamt5_toNat (m : Nat) (hm : m < 32) : (BitVec.ofNat 5 m).toNat = m := by
  simp only [BitVec.toNat_ofNat]; norm_num; omega

/-- `rotate_bits_right` by a 5-bit count `m < 32` = our `opRoriw`. -/
theorem roriw_value (v : BitVec 32) (m : Nat) (hm : m < 32) :
    rotate_bits_right v (BitVec.ofNat 5 m) = opRoriw v m := by
  simp only [rotate_bits_right, rotater, BitVec.toNatInt, opRoriw]
  rw [show ((BitVec.ofNat 5 m).toNat : Int).toNat = m by rw [Int.toNat_natCast, shamt5_toNat m hm]]
  exact rotateRight_eq_shift_or v m hm

/-! ## Refinement: low 32 bits of the Sail write = our `R32` op -/

theorem addw_lo32 (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_RTYPEW ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .ADDW) s rd).extractLsb 31 0
      = opAddw ((rget s rs1).extractLsb 31 0) ((rget s rs2).extractLsb 31 0) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp only [runRd, execute_RTYPEW, rX_bits, wX_bits, rget, upd, opAddw, sign_extend,
      Sail.BitVec.extractLsb, h1, h2, hrd, if_true, if_false, bind, StateT.bind, StateT.run,
      pure, StateT.pure, get, getThe, MonadStateOf.get, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.get, StateT.modifyGet] <;>
    rw [lo32_signExtend]

theorem subw_lo32 (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_RTYPEW ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .SUBW) s rd).extractLsb 31 0
      = opSubw ((rget s rs1).extractLsb 31 0) ((rget s rs2).extractLsb 31 0) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp only [runRd, execute_RTYPEW, rX_bits, wX_bits, rget, upd, opSubw, sign_extend,
      Sail.BitVec.extractLsb, h1, h2, hrd, if_true, if_false, bind, StateT.bind, StateT.run,
      pure, StateT.pure, get, getThe, MonadStateOf.get, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.get, StateT.modifyGet] <;>
    rw [lo32_signExtend]

theorem and_lo32 (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .AND) s rd).extractLsb 31 0
      = opAnd ((rget s rs1).extractLsb 31 0) ((rget s rs2).extractLsb 31 0) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opAnd, lo32_eq_setWidth,
      BitVec.setWidth_and, h1, h2, hrd, bind, StateT.bind, StateT.run, pure, StateT.pure,
      get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.get, StateT.modifyGet]

theorem or_lo32 (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .OR) s rd).extractLsb 31 0
      = opOr ((rget s rs1).extractLsb 31 0) ((rget s rs2).extractLsb 31 0) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opOr, lo32_eq_setWidth,
      BitVec.setWidth_or, h1, h2, hrd, bind, StateT.bind, StateT.run, pure, StateT.pure,
      get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.get, StateT.modifyGet]

theorem xor_lo32 (s : RegFile) (rs1 rs2 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ .XOR) s rd).extractLsb 31 0
      = opXor ((rget s rs1).extractLsb 31 0) ((rget s rs2).extractLsb 31 0) := by
  by_cases h1 : rs1.toNat = 0 <;> by_cases h2 : rs2.toNat = 0 <;>
    simp [runRd, execute_RTYPE, rX_bits, wX_bits, rget, upd, opXor, lo32_eq_setWidth,
      BitVec.setWidth_xor, h1, h2, hrd, bind, StateT.bind, StateT.run, pure, StateT.pure,
      get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.get, StateT.modifyGet]

theorem slliw_lo32 (s : RegFile) (rs1 rd : BitVec 5) (m : Nat) (hm : m < 32) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_SHIFTIWOP (BitVec.ofNat 5 m) ⟨rs1⟩ ⟨rd⟩ .SLLIW) s rd).extractLsb 31 0
      = opSlliw ((rget s rs1).extractLsb 31 0) m := by
  by_cases h1 : rs1.toNat = 0 <;>
    simp only [runRd, execute_SHIFTIWOP, rX_bits, wX_bits, rget, upd, opSlliw, sign_extend,
      shift_bits_left, Sail.BitVec.extractLsb, BitVec.shiftLeft_eq', shamt5_toNat m hm,
      h1, hrd, if_true, if_false, bind, StateT.bind, StateT.run, pure, StateT.pure,
      get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.get, StateT.modifyGet] <;>
    rw [lo32_signExtend]

theorem srliw_lo32 (s : RegFile) (rs1 rd : BitVec 5) (m : Nat) (hm : m < 32) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_SHIFTIWOP (BitVec.ofNat 5 m) ⟨rs1⟩ ⟨rd⟩ .SRLIW) s rd).extractLsb 31 0
      = opSrliw ((rget s rs1).extractLsb 31 0) m := by
  by_cases h1 : rs1.toNat = 0 <;>
    simp only [runRd, execute_SHIFTIWOP, rX_bits, wX_bits, rget, upd, opSrliw, sign_extend,
      shift_bits_right, Sail.BitVec.extractLsb, BitVec.ushiftRight_eq', shamt5_toNat m hm,
      h1, hrd, if_true, if_false, bind, StateT.bind, StateT.run, pure, StateT.pure,
      get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.get, StateT.modifyGet] <;>
    rw [lo32_signExtend]

/-- Zbb `RORIW` (the SHA-256 production rotate): low 32 bits = our `opRoriw`. -/
theorem roriw_lo32 (s : RegFile) (rs1 rd : BitVec 5) (m : Nat) (hm : m < 32) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_RORIW (BitVec.ofNat 5 m) ⟨rs1⟩ ⟨rd⟩) s rd).extractLsb 31 0
      = opRoriw ((rget s rs1).extractLsb 31 0) m := by
  by_cases h1 : rs1.toNat = 0 <;>
    simp only [runRd, execute_RORIW, rX_bits, wX_bits, rget, upd, sign_extend,
      roriw_value _ m hm, Sail.BitVec.extractLsb, h1, hrd, if_true, if_false, bind, StateT.bind,
      StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.get, StateT.modifyGet] <;>
    rw [lo32_signExtend]

/-- Sail `ADDI rd, rs, 0` (the `MV` pseudo-op): low 32 bits = our `mv` value `rget s rs1 [31:0]`. -/
def zero_extend {m k_n : Nat} (v : BitVec k_n) : BitVec m := v.zeroExtend m
def bool_to_bit (b : Bool) : BitVec 1 := if b then 1 else 0
def zopz0zI_s {n : Nat} (x y : BitVec n) : Bool := x.slt y
def zopz0zI_u {n : Nat} (x y : BitVec n) : Bool := x.ult y
inductive iop where | ADDI | SLTI | SLTIU | XORI | ORI | ANDI

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

theorem mv_lo32 (s : RegFile) (rs1 rd : BitVec 5) (hrd : rd.toNat ≠ 0) :
    (runRd (execute_ITYPE 0 ⟨rs1⟩ ⟨rd⟩ .ADDI) s rd).extractLsb 31 0 = (rget s rs1).extractLsb 31 0 := by
  by_cases h1 : rs1.toNat = 0 <;>
    simp [runRd, execute_ITYPE, rX_bits, wX_bits, rget, upd, sign_extend, h1, hrd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv32Ref
