/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Refinement

/-!
# Sail refinement for RV64 programs (`RiscvPc64`)

`SailRiscv64Refinement` compares the value each register clause of the Sail model writes with
`evalRInst64`, one instruction at a time. This module runs whole programs. It adds the Sail
clauses for `ld`, `sd`, `bne`, `jal` and `jalr` over a state with a byte memory, `PC` and
`nextPC`. It shows that one Sail step of each instruction `RiscvPc64` executes refines
`RiscvPc64.step`, and composes the steps over runs and functions.

## What is transcribed, and what is simplified

* **Reused:** `execute_RTYPE`, `execute_ITYPE`, `execute_SHIFTIOP` and `execute_MUL` are the
  in-file excerpts of `SailRiscv64Refinement`, run on the register file by `liftR`.
* **Transcribed:** `execute_LOAD`, `execute_STORE`, `execute_BTYPE`, `execute_JAL`,
  `execute_JALR` and `jump_to` follow the `riscv-zkvm` extraction of `riscv/sail-riscv`
  0.13.1 (rev `27224ccb`, Sail compiler 0.20.2; generated `InstsEnd.lean` and
  `BaseInsts.lean`, line numbers in the docstrings). `access` and `update` are the
  `lean-sail` one-liners, and `zopz0zKzJ_s`/`zopz0zKzJ_u` are the generated comparisons.
* **Specialized:** loads and stores are at `width = 8`, the only width the programs use.
  `Zca` is enabled, as in the extraction's configuration, and `Zicfilp` and the
  control-address extension are taken as off, so `update_elp_state` writes nothing and
  `ext_control_check_pc` is `none`.
* **Simplified:** `vmem_read8` and `vmem_write8` read and write the flat little-endian
  memory of `Memory64` at `rX rs + offset`. Sail's address translation, PMP checks and
  misaligned-access handling are not modelled; this holds for machine mode with no
  translation, no PMP regions and the configured misaligned behaviour. A failed `jump_to`
  assertion is the result `Assertion_Failure`.
* **Glue:** `sailStep` sets `nextPC := PC + 4`, executes, and on success sets `PC := nextPC`,
  as the Sail step loop does. Instructions are fetched as `PInst64` and mapped by `toInstr`;
  the word decoder is `RiscvPc64.decodeP64`, not Sail's `encdec`.

## Main results

* `sailStep_refines`: from related states at a word-aligned `pc`, the Sail step of an
  instruction with a word retires and lands in a state related to the successor that
  `RiscvPc64.step` computes.
* `sailRun_refines`: every run of `RiscvPc64.steps` of a program whose instructions all have
  words, on a word-aligned base, is matched by a Sail run of the same length.
* `fnSpec_sail`: a function meeting `FnSpec` has a Sail run that returns to `ra` in a state
  its effect allows.

`Rel` relates the registers of `memRegs64` (read through `rget`, so `x0` reads 0) and the
memory; registers outside `memRegs64` are unconstrained.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvPc64Ref

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscv64Ref

/-! ## 1. The register clauses as state transformers -/

/-- The register file after writing `v` to `i`; writes to `x0` are dropped. -/
def wr (s : RegFile) (i : BitVec 5) (v : BitVec 64) : RegFile :=
  if i.toNat = 0 then s else upd s i v

theorem rX_run (s : RegFile) (i : BitVec 5) : (rX_bits ⟨i⟩).run s = (rget s i, s) := by
  by_cases h : i.toNat = 0 <;>
    simp [rX_bits, rget, h, bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe,
      MonadStateOf.get, StateT.get]

theorem wX_run (s : RegFile) (i : BitVec 5) (v : BitVec 64) :
    (wX_bits ⟨i⟩ v).run s = ((), wr s i v) := by
  by_cases h : i.toNat = 0 <;>
    simp [wX_bits, wr, h, StateT.run, pure, StateT.pure, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet]

theorem rtype_run (s : RegFile) (rs2 rs1 rd : BitVec 5) (op : rop) :
    (execute_RTYPE ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ op).run s = (RETIRE_SUCCESS, wr s rd (match op with
      | .ADD => rget s rs1 + rget s rs2
      | .SLT => zero_extend (m := 64) (bool_to_bit (zopz0zI_s (rget s rs1) (rget s rs2)))
      | .SLTU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u (rget s rs1) (rget s rs2)))
      | .AND => rget s rs1 &&& rget s rs2
      | .OR => rget s rs1 ||| rget s rs2
      | .XOR => rget s rs1 ^^^ rget s rs2
      | .SLL => shift_bits_left (rget s rs1) (Sail.BitVec.extractLsb (rget s rs2) (log2_xlen - 1) 0)
      | .SRL => shift_bits_right (rget s rs1) (Sail.BitVec.extractLsb (rget s rs2) (log2_xlen - 1) 0)
      | .SUB => rget s rs1 - rget s rs2
      | .SRA => shift_bits_right_arith (rget s rs1)
          (Sail.BitVec.extractLsb (rget s rs2) (log2_xlen - 1) 0))) := by
  cases op <;> simp [execute_RTYPE, StateT.run, bind, StateT.bind, pure, StateT.pure,
    show ∀ i, rX_bits ⟨i⟩ = fun s => (rget s i, s) from fun i => funext fun s => rX_run s i,
    show ∀ i v, wX_bits ⟨i⟩ v = fun s => ((), wr s i v) from fun i v => funext fun s => wX_run s i v]

theorem itype_run (s : RegFile) (imm : BitVec 12) (rs1 rd : BitVec 5) :
    (execute_ITYPE imm ⟨rs1⟩ ⟨rd⟩ .ADDI).run s
      = (RETIRE_SUCCESS, wr s rd (rget s rs1 + imm.signExtend 64)) := by
  simp [execute_ITYPE, StateT.run, bind, StateT.bind, pure, StateT.pure, sign_extend,
    show ∀ i, rX_bits ⟨i⟩ = fun s => (rget s i, s) from fun i => funext fun s => rX_run s i,
    show ∀ i v, wX_bits ⟨i⟩ v = fun s => ((), wr s i v) from fun i v => funext fun s => wX_run s i v]

theorem shiftiop_run (s : RegFile) (shamt : BitVec 6) (rs1 rd : BitVec 5) (op : sop) :
    (execute_SHIFTIOP shamt ⟨rs1⟩ ⟨rd⟩ op).run s = (RETIRE_SUCCESS, wr s rd (match op with
      | .SLLI => shift_bits_left (rget s rs1) (Sail.BitVec.extractLsb shamt (log2_xlen - 1) 0)
      | .SRLI => shift_bits_right (rget s rs1) (Sail.BitVec.extractLsb shamt (log2_xlen - 1) 0)
      | .SRAI => shift_bits_right_arith (rget s rs1)
          (Sail.BitVec.extractLsb shamt (log2_xlen - 1) 0))) := by
  cases op <;> simp [execute_SHIFTIOP, StateT.run, bind, StateT.bind, pure, StateT.pure,
    show ∀ i, rX_bits ⟨i⟩ = fun s => (rget s i, s) from fun i => funext fun s => rX_run s i,
    show ∀ i v, wX_bits ⟨i⟩ v = fun s => ((), wr s i v) from fun i v => funext fun s => wX_run s i v]

theorem mul_run (s : RegFile) (rs2 rs1 rd : BitVec 5) (mop : mul_op) :
    (execute_MUL ⟨rs2⟩ ⟨rs1⟩ ⟨rd⟩ mop).run s = (RETIRE_SUCCESS, wr s rd
      (mult_to_bits_half mop.signed_rs1 mop.signed_rs2 (rget s rs1) (rget s rs2) mop.result_part)) := by
  simp [execute_MUL, StateT.run, bind, StateT.bind, pure, StateT.pure,
    show ∀ i, rX_bits ⟨i⟩ = fun s => (rget s i, s) from fun i => funext fun s => rX_run s i,
    show ∀ i v, wX_bits ⟨i⟩ v = fun s => ((), wr s i v) from fun i v => funext fun s => wX_run s i v]

/-! ## 2. The machine with memory and a program counter -/

open CatCrypt.Crypto.SecureCompilation.Memory64 (AMem read64 write64)
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder (reg5)
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64 (emittedRegs64)

/-- The Sail state of the clauses below: the register file, a flat byte memory, `PC` and
    `nextPC`. -/
structure SailSt where
  regs : RegFile
  mem : AMem
  PC : BitVec 64
  nextPC : BitVec 64

/-- The state monad of the clauses below. -/
abbrev SailPM := StateM SailSt

/-- An execution result: success, or the failures the clauses below can raise. -/
inductive Result where
  | Retire_Success (_ : Unit)
  | Illegal_Instruction (_ : Unit)
  | Assertion_Failure (_ : Unit)
  | Memory_Exception (_ : BitVec 64)

/-- A result of the register-file clauses. -/
def Result.ofReg : ExecutionResult → Result
  | .Retire_Success () => .Retire_Success ()
  | .Illegal_Instruction () => .Illegal_Instruction ()

/-- Run a clause of `SailRiscv64Ref` on the register file. -/
def liftR {α : Type} (m : SailRiscv64Ref.SailM α) : SailPM α := fun s =>
  let r := m.run s.regs
  (r.1, { s with regs := r.2 })

def rX (i : regidx) : SailPM (BitVec 64) := liftR (rX_bits i)
def wX (i : regidx) (data : BitVec 64) : SailPM Unit := liftR (wX_bits i data)
def readPC : SailPM (BitVec 64) := fun s => (s.PC, s)
def get_next_pc (_ : Unit) : SailPM (BitVec 64) := fun s => (s.nextPC, s)
def set_next_pc (pc : BitVec 64) : SailPM Unit := fun s => ((), { s with nextPC := pc })

/-- `Zca` is supported in the configuration of the extraction (`rv64d_v256_e64.json`). -/
def zcaEnabled : Bool := true

/-- `lean-sail` `Sail/Sail.lean:78`. -/
def access {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 := BitVec.ofBool x[i]!

/-- `lean-sail` `Sail/Sail.lean:49`. -/
def updateSubrange' {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len) : BitVec w :=
  let mask := ~~~(((BitVec.allOnes len).zeroExtend w) <<< start)
  let y' := ((y.zeroExtend w) <<< start)
  (mask &&& x) ||| y'

/-- `lean-sail` `Sail/Sail.lean:106`. -/
def update {m : Nat} (x : BitVec m) (n : Nat) (b : BitVec 1) : BitVec m := updateSubrange' x n _ b

/-- Generated `BaseInsts.lean:236`, with no control-address extension
    (`ext_control_check_pc` is `none`); the assertion fails as `Assertion_Failure`. -/
def jump_to (target : BitVec 64) : SailPM Result := do
  if access target 0 != 0#1 then pure (.Assertion_Failure ())
  else if (access target 1 == 1#1) && (not zcaEnabled) then pure (.Memory_Exception target)
  else
    (do
      (set_next_pc target)
      (pure (.Retire_Success ())))

/-- The doubleword load at `rX rs + offset`, over the flat little-endian memory. -/
def vmem_read8 (rs : regidx) (offset : BitVec 64) : SailPM (BitVec 64) := do
  let vaddr := (← rX rs) + offset
  pure (read64 (← get).mem vaddr)

/-- The doubleword store at `rX rs + offset`, over the flat little-endian memory. -/
def vmem_write8 (rs : regidx) (offset : BitVec 64) (data : BitVec 64) : SailPM Unit := do
  let vaddr := (← rX rs) + offset
  modify fun s => { s with mem := write64 s.mem vaddr data }

inductive bop where | BEQ | BNE | BLT | BGE | BLTU | BGEU

/-- Generated `Prelude.lean:366`. -/
def zopz0zKzJ_s {k_n : Nat} (x y : BitVec k_n) : Bool := decide (x.toInt ≥ y.toInt)
/-- Generated `Prelude.lean:382`. -/
def zopz0zKzJ_u {k_n : Nat} (x y : BitVec k_n) : Bool := decide (x.toNat ≥ y.toNat)

/-- Generated `InstsEnd.lean:4480`, at `width = 8` (`extend_value` is the identity). -/
def execute_LOAD (imm : BitVec 12) (rs1 rd : regidx) : SailPM Result := do
  let offset : BitVec 64 := (sign_extend (m := 64) imm)
  let data ← vmem_read8 rs1 offset
  (wX rd data)
  (pure (.Retire_Success ()))

/-- Generated `InstsEnd.lean:4228`, at `width = 8`. -/
def execute_STORE (imm : BitVec 12) (rs2 rs1 : regidx) : SailPM Result := do
  let offset : BitVec 64 := (sign_extend (m := 64) imm)
  let data ← do (pure (Sail.BitVec.extractLsb (← (rX rs2)) (8 * 8 - 1) 0))
  (vmem_write8 rs1 offset data)
  (pure (.Retire_Success ()))

/-- Generated `InstsEnd.lean:4626`. -/
def execute_BTYPE (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) : SailPM Result := do
  let taken ← (( do
    match op with
    | .BEQ => (pure ((← (rX rs1)) == (← (rX rs2))))
    | .BNE => (pure ((← (rX rs1)) != (← (rX rs2))))
    | .BLT => (pure (zopz0zI_s (← (rX rs1)) (← (rX rs2))))
    | .BGE => (pure (zopz0zKzJ_s (← (rX rs1)) (← (rX rs2))))
    | .BLTU => (pure (zopz0zI_u (← (rX rs1)) (← (rX rs2))))
    | .BGEU => (pure (zopz0zKzJ_u (← (rX rs1)) (← (rX rs2)))) ) : SailPM Bool)
  if (taken : Bool)
  then (jump_to ((← readPC) + (sign_extend (m := 64) imm)))
  else (pure (.Retire_Success ()))

/-- Generated `InstsEnd.lean:4501`. -/
def execute_JAL (imm : BitVec 21) (rd : regidx) : SailPM Result := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readPC) + (sign_extend (m := 64) imm)))) with
  | .Retire_Success () =>
    (do
      (wX rd link_address)
      (pure (.Retire_Success ())))
  | failure => (pure failure)

/-- Generated `InstsEnd.lean:4490`, with `Zicfilp` disabled (`update_elp_state` writes
    nothing). -/
def execute_JALR (imm : BitVec 12) (rs1 rd : regidx) : SailPM Result := do
  let link_address ← do (get_next_pc ())
  let target ← do (pure ((← (rX rs1)) + (sign_extend (m := 64) imm)))
  match (← (jump_to (update target 0 0#1))) with
  | .Retire_Success () =>
    (do
      (wX rd link_address)
      (pure (.Retire_Success ())))
  | failure => (pure failure)

/-- The instructions of the clauses above. -/
inductive Instr where
  | RTYPE (rs2 rs1 rd : regidx) (op : rop)
  | ITYPE (imm : BitVec 12) (rs1 rd : regidx) (op : iop)
  | SHIFTIOP (shamt : BitVec 6) (rs1 rd : regidx) (op : sop)
  | MUL (rs2 rs1 rd : regidx) (mop : mul_op)
  | LOAD (imm : BitVec 12) (rs1 rd : regidx)
  | STORE (imm : BitVec 12) (rs2 rs1 : regidx)
  | BTYPE (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
  | JAL (imm : BitVec 21) (rd : regidx)
  | JALR (imm : BitVec 12) (rs1 rd : regidx)

/-- The dispatch of generated `execute`, on these instructions. -/
def execute : Instr → SailPM Result
  | .RTYPE rs2 rs1 rd op => Result.ofReg <$> liftR (execute_RTYPE rs2 rs1 rd op)
  | .ITYPE imm rs1 rd op => Result.ofReg <$> liftR (execute_ITYPE imm rs1 rd op)
  | .SHIFTIOP shamt rs1 rd op => Result.ofReg <$> liftR (execute_SHIFTIOP shamt rs1 rd op)
  | .MUL rs2 rs1 rd mop => Result.ofReg <$> liftR (execute_MUL rs2 rs1 rd mop)
  | .LOAD imm rs1 rd => execute_LOAD imm rs1 rd
  | .STORE imm rs2 rs1 => execute_STORE imm rs2 rs1
  | .BTYPE imm rs2 rs1 op => execute_BTYPE imm rs2 rs1 op
  | .JAL imm rd => execute_JAL imm rd
  | .JALR imm rs1 rd => execute_JALR imm rs1 rd

/-- One instruction: `nextPC := PC + 4`, execute, and on success `PC := nextPC`. -/
def sailStep (i : Instr) : SailPM Result := do
  set_next_pc ((← readPC) + 4)
  match (← execute i) with
  | .Retire_Success () =>
    (do
      modify fun s => { s with PC := s.nextPC }
      (pure (.Retire_Success ())))
  | failure => (pure failure)

/-! ## 3. The instructions of `RiscvPc64` as Sail instructions -/

/-- The register index of a name. -/
def rIdx (r : String) : regidx := .Regidx (reg5 r)

/-- The Sail instruction of a program instruction (`none` for `li`, which has no word). -/
def toInstr : PInst64 → Option Instr
  | .x (.m (.base (.add d a b))) => some (.RTYPE (rIdx b) (rIdx a) (rIdx d) .ADD)
  | .x (.m (.base (.sub d a b))) => some (.RTYPE (rIdx b) (rIdx a) (rIdx d) .SUB)
  | .x (.m (.base (.sltu d a b))) => some (.RTYPE (rIdx b) (rIdx a) (rIdx d) .SLTU)
  | .x (.m (.base (.and d a b))) => some (.RTYPE (rIdx b) (rIdx a) (rIdx d) .AND)
  | .x (.m (.base (.or d a b))) => some (.RTYPE (rIdx b) (rIdx a) (rIdx d) .OR)
  | .x (.m (.base (.xor d a b))) => some (.RTYPE (rIdx b) (rIdx a) (rIdx d) .XOR)
  | .x (.m (.base (.mul d a b))) => some (.MUL (rIdx b) (rIdx a) (rIdx d) ⟨.Low, .Signed, .Signed⟩)
  | .x (.m (.base (.mulhu d a b))) =>
    some (.MUL (rIdx b) (rIdx a) (rIdx d) ⟨.High, .Unsigned, .Unsigned⟩)
  | .x (.m (.base (.li _ _))) => none
  | .x (.m (.base (.mv d a))) => some (.ITYPE 0 (rIdx a) (rIdx d) .ADDI)
  | .x (.m (.base (.srli d a sh))) => some (.SHIFTIOP (BitVec.ofNat 6 sh) (rIdx a) (rIdx d) .SRLI)
  | .x (.m (.base (.slli d a sh))) => some (.SHIFTIOP (BitVec.ofNat 6 sh) (rIdx a) (rIdx d) .SLLI)
  | .x (.m (.addi d a imm)) => some (.ITYPE imm (rIdx a) (rIdx d) .ADDI)
  | .x (.ld d b off) => some (.LOAD off (rIdx b) (rIdx d))
  | .x (.sd v b off) => some (.STORE off (rIdx v) (rIdx b))
  | .bne a b off => some (.BTYPE off (rIdx b) (rIdx a) .BNE)
  | .jal d off => some (.JAL off (rIdx d))
  | .jalr d b off => some (.JALR off (rIdx b) (rIdx d))

/-- The registers named by `memRegs64` read the same, and the memories are equal. -/
def Rel (st : MState64) (σ : SailSt) : Prop :=
  (∀ r ∈ memRegs64, rget σ.regs (reg5 r) = st.regs.get r) ∧ σ.mem = st.mem

theorem reg5_zero : ∀ r ∈ memRegs64, ((reg5 r).toNat = 0 ↔ r = "zero") := by decide

theorem reg5_inj : ∀ r ∈ memRegs64, ∀ q ∈ memRegs64, reg5 r = reg5 q → r = q := by decide

theorem x0_not_mem : "x0" ∉ memRegs64 := by decide

theorem rget_wr_same (s : RegFile) (i : BitVec 5) (v : BitVec 64) (h : i.toNat ≠ 0) :
    rget (wr s i v) i = v := by
  simp [rget, wr, upd, h]

theorem rget_wr_other (s : RegFile) (i j : BitVec 5) (v : BitVec 64) (h : j ≠ i) :
    rget (wr s i v) j = rget s j := by
  unfold wr; split
  · rfl
  · simp [rget, upd, h]

theorem rel_write (R : RState64) (s : RegFile) (d : String) (v : BitVec 64) (hd : d ∈ memRegs64)
    (h : ∀ r ∈ memRegs64, rget s (reg5 r) = R.get r) :
    ∀ r ∈ memRegs64, rget (wr s (reg5 d) v) (reg5 r) = (R.set d v).get r := by
  intro r hr
  by_cases hrd : r = d
  · subst hrd
    by_cases hz : r = "zero"
    · subst hz
      have : (reg5 "zero").toNat = 0 := (reg5_zero _ hr).2 rfl
      simp [this, rget, RState64.get]
    · have h0 : (reg5 r).toNat ≠ 0 := fun h' => hz ((reg5_zero _ hr).1 h')
      rw [rget_wr_same _ _ _ h0, RState64.get_set_same _ _ _ (by
        rintro (h' | h')
        · exact hz h'
        · exact x0_not_mem (h' ▸ hr))]
  · rw [rget_wr_other _ _ _ _ (fun h' => hrd (reg5_inj _ hr _ hd h')),
      RState64.get_set_other _ _ _ _ hrd]
    exact h r hr

/-! ## 4. The values -/

theorem sltu_val (x y : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)) = opSltu x y := by
  by_cases h : x.toNat < y.toNat <;>
    simp [zero_extend, bool_to_bit, zopz0zI_u, BitVec.ult, opSltu, h]

theorem srli_val (x : BitVec 64) (sh : Nat) (h : sh < 64) :
    shift_bits_right x (Sail.BitVec.extractLsb (BitVec.ofNat 6 sh) (log2_xlen - 1) 0) = x >>> sh := by
  simp only [shift_bits_right, Sail.BitVec.extractLsb, log2_xlen]
  rw [BitVec.ushiftRight_eq']
  congr 1
  simp [BitVec.extractLsb, Nat.mod_eq_of_lt h]

theorem slli_val (x : BitVec 64) (sh : Nat) (h : sh < 64) :
    shift_bits_left x (Sail.BitVec.extractLsb (BitVec.ofNat 6 sh) (log2_xlen - 1) 0) = x <<< sh := by
  simp only [shift_bits_left, Sail.BitVec.extractLsb, log2_xlen]
  rw [BitVec.shiftLeft_eq']
  congr 1
  simp [BitVec.extractLsb, Nat.mod_eq_of_lt h]

theorem slice64 (x : BitVec 64) : Sail.BitVec.extractLsb x (8 * 8 - 1) 0 = x := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb]

theorem update_zero (x : BitVec 64) : update x 0 0#1 = x &&& ~~~1 := by
  simp only [update, updateSubrange']
  rw [show (BitVec.allOnes 1).zeroExtend 64 = (1 : BitVec 64) by decide,
    show (0#1).zeroExtend 64 = (0 : BitVec 64) by decide]
  simp [BitVec.and_comm]

theorem access_zero (x : BitVec 64) (h : x.toNat % 2 = 0) : access x 0 = 0#1 := by
  have : x.getLsbD 0 = false := by
    rw [BitVec.getLsbD, Nat.testBit_zero]; simp [h]
  rw [access, show x[0]! = x.getLsbD 0 from rfl, this]; rfl

theorem access_clear (x : BitVec 64) : access (x &&& ~~~1) 0 = 0#1 := by
  simp [access]

theorem access_clear' (x : BitVec 64) : access (x &&& 18446744073709551614#64) 0 = 0#1 :=
  access_clear x

/-! ## 5. One step of each kind -/

theorem rX_app (s : RegFile) (i : BitVec 5) : rX_bits ⟨i⟩ s = (rget s i, s) := rX_run s i

theorem wX_app (s : RegFile) (i : BitVec 5) (v : BitVec 64) : wX_bits ⟨i⟩ v s = ((), wr s i v) :=
  wX_run s i v

theorem slice63 (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x := slice64 x

theorem rX_run' (σ : SailSt) (i : BitVec 5) : (rX ⟨i⟩).run σ = (rget σ.regs i, σ) := by
  simp only [rX, liftR, StateT.run, rX_app]

theorem wX_run' (σ : SailSt) (i : BitVec 5) (v : BitVec 64) :
    (wX ⟨i⟩ v).run σ = ((), { σ with regs := wr σ.regs i v }) := by
  simp only [wX, liftR, StateT.run, wX_app]

theorem step_lift (σ : SailSt) (i : Instr) (m : SailRiscv64Ref.SailM ExecutionResult)
    (hi : execute i = Result.ofReg <$> liftR m) (r' : RegFile)
    (h : m.run σ.regs = (RETIRE_SUCCESS, r')) :
    (sailStep i).run σ
      = (.Retire_Success (), { σ with regs := r', nextPC := σ.PC + 4, PC := σ.PC + 4 }) := by
  simp only [StateT.run] at h
  simp [sailStep, hi, liftR, h, readPC, set_next_pc, bind, StateT.bind, StateT.run, Functor.map,
    StateT.map, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure,
    Result.ofReg, RETIRE_SUCCESS]

theorem step_load (σ : SailSt) (imm : BitVec 12) (rs1 rd : BitVec 5) :
    (sailStep (.LOAD imm ⟨rs1⟩ ⟨rd⟩)).run σ = (.Retire_Success (), { σ with
      regs := wr σ.regs rd (read64 σ.mem (rget σ.regs rs1 + imm.signExtend 64)),
      nextPC := σ.PC + 4, PC := σ.PC + 4 }) := by
  simp [sailStep, execute, execute_LOAD, vmem_read8, rX, wX, liftR, rX_app, wX_app, readPC,
    set_next_pc, sign_extend, bind, StateT.bind, StateT.run, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get]

theorem step_store (σ : SailSt) (imm : BitVec 12) (rs2 rs1 : BitVec 5) :
    (sailStep (.STORE imm ⟨rs2⟩ ⟨rs1⟩)).run σ = (.Retire_Success (), { σ with
      mem := write64 σ.mem (rget σ.regs rs1 + imm.signExtend 64) (rget σ.regs rs2),
      nextPC := σ.PC + 4, PC := σ.PC + 4 }) := by
  simp [sailStep, execute, execute_STORE, vmem_write8, rX, liftR, rX_app, readPC, slice63,
    set_next_pc, sign_extend, bind, StateT.bind, StateT.run, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure]

theorem jump_ok (σ : SailSt) (t : BitVec 64) (h : access t 0 = 0#1) :
    (jump_to t).run σ = (.Retire_Success (), { σ with nextPC := t }) := by
  simp [jump_to, h, zcaEnabled, set_next_pc, bind, StateT.bind, StateT.run, pure, StateT.pure]

theorem step_bne (σ : SailSt) (imm : BitVec 13) (rs2 rs1 : BitVec 5)
    (h : rget σ.regs rs1 ≠ rget σ.regs rs2 → access (σ.PC + imm.signExtend 64) 0 = 0#1) :
    (sailStep (.BTYPE imm ⟨rs2⟩ ⟨rs1⟩ .BNE)).run σ = (.Retire_Success (), { σ with
      nextPC := if rget σ.regs rs1 = rget σ.regs rs2 then σ.PC + 4 else σ.PC + imm.signExtend 64,
      PC := if rget σ.regs rs1 = rget σ.regs rs2 then σ.PC + 4 else σ.PC + imm.signExtend 64 }) := by
  by_cases he : rget σ.regs rs1 = rget σ.regs rs2
  · simp [sailStep, execute, execute_BTYPE, rX, liftR, rX_app, readPC, set_next_pc, he,
      bind, StateT.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      pure, StateT.pure]
  · have hj := h he
    simp [sailStep, execute, execute_BTYPE, rX, liftR, rX_app, readPC, set_next_pc, he,
      jump_to, hj, zcaEnabled, sign_extend, bind, StateT.bind, StateT.run, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure]

theorem step_jal (σ : SailSt) (imm : BitVec 21) (rd : BitVec 5)
    (h : access (σ.PC + imm.signExtend 64) 0 = 0#1) :
    (sailStep (.JAL imm ⟨rd⟩)).run σ = (.Retire_Success (), { σ with
      regs := wr σ.regs rd (σ.PC + 4), nextPC := σ.PC + imm.signExtend 64,
      PC := σ.PC + imm.signExtend 64 }) := by
  simp [sailStep, execute, execute_JAL, wX, liftR, wX_app, readPC, get_next_pc, set_next_pc,
    jump_to, h, zcaEnabled, sign_extend, bind, StateT.bind, StateT.run, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure]

theorem step_jalr (σ : SailSt) (imm : BitVec 12) (rs1 rd : BitVec 5) :
    (sailStep (.JALR imm ⟨rs1⟩ ⟨rd⟩)).run σ = (.Retire_Success (), { σ with
      regs := wr σ.regs rd (σ.PC + 4),
      nextPC := (rget σ.regs rs1 + imm.signExtend 64) &&& ~~~1,
      PC := (rget σ.regs rs1 + imm.signExtend 64) &&& ~~~1 }) := by
  simp [sailStep, execute, execute_JALR, rX, wX, liftR, rX_app, wX_app, readPC, get_next_pc,
    set_next_pc, jump_to, update_zero, access_clear', zcaEnabled, sign_extend, bind, StateT.bind,
    StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure]

/-! ## 6. One step refines -/

/-- The successor state of `RiscvPc64.step` after fetching `i`. -/
def pexec (s : PState64) : PInst64 → PState64
  | .x i => ⟨s.pc + 4, evalX s.st i⟩
  | .bne a b off =>
    ⟨if s.st.regs.get a = s.st.regs.get b then s.pc + 4 else s.pc + off.signExtend 64, s.st⟩
  | .jal d off => ⟨s.pc + off.signExtend 64, ⟨s.st.regs.set d (s.pc + 4), s.st.mem⟩⟩
  | .jalr d b off =>
    ⟨(s.st.regs.get b + off.signExtend 64) &&& ~~~1, ⟨s.st.regs.set d (s.pc + 4), s.st.mem⟩⟩

theorem step_of_fetch (prog : List PInst64) (base : BitVec 64) (s : PState64) (i : PInst64)
    (h : fetch prog base s.pc = some i) : step prog base s = some (pexec s i) := by
  cases i <;> simp [step, h, pexec]

theorem em {r : String} (h : r ∈ emittedRegs64) : r ∈ memRegs64 := by
  simp only [memRegs64, List.mem_append]; exact Or.inl h

theorem even_target (pc : BitVec 64) (k : Nat) (off : BitVec k) (h4 : pc.toNat % 4 = 0)
    (ho : (off.signExtend 64).toNat % 2 = 0) : (pc + off.signExtend 64).toNat % 2 = 0 := by
  simp only [BitVec.toNat_add]; omega

theorem sext_even13 (off : BitVec 13) (h : off &&& 0x1ffe = off) :
    (off.signExtend 64).toNat % 2 = 0 := by
  have h0 : off.getLsbD 0 = false := by
    have := congrArg (fun x => x.getLsbD 0) h
    simp only [BitVec.getLsbD_and] at this
    rw [show (0x1ffe : BitVec 13).getLsbD 0 = false by decide, Bool.and_false] at this
    exact this.symm
  have : (off.signExtend 64).getLsbD 0 = false := by
    rw [BitVec.getLsbD_signExtend]; simp_all
  rw [BitVec.getLsbD, Nat.testBit_zero] at this
  simpa using this

theorem sext_even21 (off : BitVec 21) (h : off &&& 0x1ffffe = off) :
    (off.signExtend 64).toNat % 2 = 0 := by
  have h0 : off.getLsbD 0 = false := by
    have := congrArg (fun x => x.getLsbD 0) h
    simp only [BitVec.getLsbD_and] at this
    rw [show (0x1ffffe : BitVec 21).getLsbD 0 = false by decide, Bool.and_false] at this
    exact this.symm
  have : (off.signExtend 64).getLsbD 0 = false := by
    rw [BitVec.getLsbD_signExtend]; simp_all
  rw [BitVec.getLsbD, Nat.testBit_zero] at this
  simpa using this

/-- **One step refines.** For an instruction with a word, from related states at a word-aligned
    `pc`, the Sail step succeeds and lands in a state related to the successor of
    `RiscvPc64.step`, at its `pc`. -/
theorem sailStep_refines (i : PInst64) (hok : PInstOKb i = true) (s : PState64) (σ : SailSt)
    (hR : Rel s.st σ) (hpc : σ.PC = s.pc) (h4 : s.pc.toNat % 4 = 0) :
    ∃ a σ', toInstr i = some a ∧ (sailStep a).run σ = (.Retire_Success (), σ') ∧
      Rel (pexec s i).st σ' ∧ σ'.PC = (pexec s i).pc := by
  cases i with
  | x xi =>
    cases xi with
    | m mi =>
      cases mi with
      | base ri =>
        cases ri with
        | add d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (rtype_run _ _ _ _ .ADD), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show rget σ.regs (reg5 a) + rget σ.regs (reg5 b) = opAdd64 (s.st.regs.get a) (s.st.regs.get b) from by rw [hR.1 a (em ha), hR.1 b (em hb)]; simp]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | sub d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (rtype_run _ _ _ _ .SUB), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show rget σ.regs (reg5 a) - rget σ.regs (reg5 b) = opSub64 (s.st.regs.get a) (s.st.regs.get b) from by rw [hR.1 a (em ha), hR.1 b (em hb)]; simp]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | sltu d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (rtype_run _ _ _ _ .SLTU), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show zero_extend (m := 64) (bool_to_bit (zopz0zI_u (rget σ.regs (reg5 a)) (rget σ.regs (reg5 b)))) = opSltu (s.st.regs.get a) (s.st.regs.get b) from by rw [hR.1 a (em ha), hR.1 b (em hb)]; simp [sltu_val]]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | and d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (rtype_run _ _ _ _ .AND), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show (rget σ.regs (reg5 a) &&& rget σ.regs (reg5 b)) = opAnd64 (s.st.regs.get a) (s.st.regs.get b) from by rw [hR.1 a (em ha), hR.1 b (em hb)]; simp]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | or d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (rtype_run _ _ _ _ .OR), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show (rget σ.regs (reg5 a) ||| rget σ.regs (reg5 b)) = opOr64 (s.st.regs.get a) (s.st.regs.get b) from by rw [hR.1 a (em ha), hR.1 b (em hb)]; simp]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | xor d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (rtype_run _ _ _ _ .XOR), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show (rget σ.regs (reg5 a) ^^^ rget σ.regs (reg5 b)) = opXor64 (s.st.regs.get a) (s.st.regs.get b) from by rw [hR.1 a (em ha), hR.1 b (em hb)]; simp]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | mul d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (mul_run _ _ _ _ _), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show mult_to_bits_half .Signed .Signed (rget σ.regs (reg5 a)) (rget σ.regs (reg5 b)) .Low
              = opMul64 (s.st.regs.get a) (s.st.regs.get b) from by
            rw [hR.1 a (em ha), hR.1 b (em hb)]; exact mul_value _ _]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | mulhu d a b =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha, hb⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (mul_run _ _ _ _ _), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show mult_to_bits_half .Unsigned .Unsigned (rget σ.regs (reg5 a)) (rget σ.regs (reg5 b))
              .High = opMulhu (s.st.regs.get a) (s.st.regs.get b) from by
            rw [hR.1 a (em ha), hR.1 b (em hb)]; exact mulhu_value _ _]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | li d imm => simp [PInstOKb, XInstOKb, MInstOKb] at hok
        | mv d a =>
          simp only [PInstOKb, XInstOKb, MInstOKb, rinst64DstSrcs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨hd, ha⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (itype_run _ _ _ _), ?_, by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [show rget σ.regs (reg5 a) + (0 : BitVec 12).signExtend 64 = s.st.regs.get a from by
            rw [hR.1 a (em ha)]; simp]
          exact rel_write _ _ _ _ (em (of_decide_eq_true hd)) hR.1
        | srli d a sh =>
          simp only [PInstOKb, XInstOKb, MInstOKb, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨hd, ha⟩, hsh⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (shiftiop_run _ _ _ _ .SRLI), ?_,
            by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [srli_val _ _ hsh, hR.1 a (em ha)]
          exact rel_write _ _ _ _ (em hd) hR.1
        | slli d a sh =>
          simp only [PInstOKb, XInstOKb, MInstOKb, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨hd, ha⟩, hsh⟩ := hok
          refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (shiftiop_run _ _ _ _ .SLLI), ?_,
            by simp [pexec, hpc]⟩
          refine ⟨?_, hR.2⟩
          simp only [pexec, evalX, evalMInst64, evalRInst64]
          rw [slli_val _ _ hsh, hR.1 a (em ha)]
          exact rel_write _ _ _ _ (em hd) hR.1
      | addi d a imm =>
        simp only [PInstOKb, XInstOKb, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨hd, ha⟩, -⟩ := hok
        refine ⟨_, _, rfl, step_lift σ _ _ rfl _ (itype_run _ _ _ _), ?_, by simp [pexec, hpc]⟩
        refine ⟨?_, hR.2⟩
        simp only [pexec, evalX, evalMInst64]
        rw [hR.1 a ha]
        exact rel_write _ _ _ _ hd hR.1
    | ld d b off =>
      simp only [PInstOKb, XInstOKb, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hd, hb⟩ := hok
      refine ⟨_, _, rfl, step_load σ _ _ _, ?_, by simp [pexec, hpc]⟩
      refine ⟨?_, hR.2⟩
      simp only [pexec, evalX, addr]
      rw [hR.1 b hb, hR.2]
      exact rel_write _ _ _ _ hd hR.1
    | sd v b off =>
      simp only [PInstOKb, XInstOKb, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hv, hb⟩ := hok
      refine ⟨_, _, rfl, step_store σ _ _ _, ⟨hR.1, ?_⟩, by simp [pexec, hpc]⟩
      simp only [pexec, evalX, addr]
      rw [hR.1 b hb, hR.1 v hv, hR.2]
  | bne a b off =>
    simp only [PInstOKb, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨ha, hb⟩, hoff⟩ := hok
    refine ⟨_, _, rfl, step_bne σ _ _ _ (fun _ => access_zero _ (by
      rw [hpc]; exact even_target _ _ _ h4 (sext_even13 _ hoff))), ⟨hR.1, hR.2⟩, ?_⟩
    simp only [pexec, hR.1 a ha, hR.1 b hb, hpc]
  | jal d off =>
    simp only [PInstOKb, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨hd, hoff⟩ := hok
    refine ⟨_, _, rfl, step_jal σ _ _ (access_zero _ (by
      rw [hpc]; exact even_target _ _ _ h4 (sext_even21 _ hoff))), ?_, by simp [pexec, hpc]⟩
    refine ⟨?_, hR.2⟩
    simp only [pexec, hpc]
    exact rel_write _ _ _ _ hd hR.1
  | jalr d b off =>
    simp only [PInstOKb, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hd, hb⟩ := hok
    refine ⟨_, _, rfl, step_jalr σ _ _ _, ?_, by simp [pexec, hR.1 b hb]⟩
    refine ⟨?_, hR.2⟩
    simp only [pexec, hpc]
    exact rel_write _ _ _ _ hd hR.1

/-! ## 7. Runs -/

/-- Run `n` Sail steps on the instructions of `prog` loaded at `base`, fetched at `PC`; `none`
    if the fetch fails, the instruction has no word, or a step does not retire. -/
def sailRun (prog : List PInst64) (base : BitVec 64) : Nat → SailSt → Option SailSt
  | 0, σ => some σ
  | n + 1, σ =>
    match fetch prog base σ.PC with
    | none => none
    | some i =>
      match toInstr i with
      | none => none
      | some a =>
        match (sailStep a).run σ with
        | (.Retire_Success (), σ') => sailRun prog base n σ'
        | _ => none

theorem fetch_mem (prog : List PInst64) (base pc : BitVec 64) (i : PInst64)
    (h : fetch prog base pc = some i) : i ∈ prog := by
  unfold fetch at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

theorem fetch_aligned (prog : List PInst64) (base pc : BitVec 64) (i : PInst64)
    (hb : base &&& 3 = 0) (h : fetch prog base pc = some i) : pc.toNat % 4 = 0 := by
  unfold fetch at h
  split at h
  · rename_i h4
    have hb4 : base.toNat % 4 = 0 := by
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_and, show (3 : BitVec 64).toNat = 2 ^ 2 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at this
      simpa using this
    have e : pc = base + (pc - base) := by simp
    rw [e, BitVec.toNat_add]
    have := base.isLt; have := (pc - base).isLt
    omega
  · cases h

/-- **Runs refine.** On a word-aligned base, for a program whose instructions all have words,
    every run of `RiscvPc64.steps` from a state related to a Sail state at the same `pc` is
    matched by a Sail run of the same length, which ends related, at the same `pc`. -/
theorem sailRun_refines (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0)
    (hok : prog.all PInstOKb = true) :
    ∀ (n : Nat) (s s' : PState64) (σ : SailSt), Rel s.st σ → σ.PC = s.pc →
      steps prog base n s = some s' →
      ∃ σ', sailRun prog base n σ = some σ' ∧ Rel s'.st σ' ∧ σ'.PC = s'.pc := by
  intro n
  induction n with
  | zero =>
    intro s s' σ hR hpc h
    simp only [steps, Option.some.injEq] at h
    subst h
    exact ⟨σ, rfl, hR, hpc⟩
  | succ n ih =>
    intro s s' σ hR hpc h
    simp only [steps] at h
    cases hf : fetch prog base s.pc with
    | none => simp [step, hf] at h
    | some i =>
      rw [step_of_fetch prog base s i hf, Option.bind_some] at h
      obtain ⟨a, σ1, ha, hrun, hR1, hpc1⟩ := sailStep_refines i
        (List.all_eq_true.1 hok i (fetch_mem _ _ _ _ hf)) s σ hR hpc
        (fetch_aligned _ _ _ _ hb hf)
      obtain ⟨σ', h', hR', hpc'⟩ := ih _ _ σ1 hR1 hpc1 h
      refine ⟨σ', ?_, hR', hpc'⟩
      simp only [sailRun, hpc, hf, ha, hrun]
      exact h'

/-- **A function, in Sail.** A function meeting `FnSpec`, entered from a Sail state related to a
    state satisfying its precondition, has a Sail run that returns to the address in `ra`
    (bit 0 cleared) in a state related to one its effect allows. -/
theorem fnSpec_sail (prog : List PInst64) (base f : BitVec 64) (hb : base &&& 3 = 0)
    (hok : prog.all PInstOKb = true) {P : MState64 → Prop} {Q : MState64 → MState64 → Prop}
    (h : FnSpec prog base f P Q) (st : MState64) (σ : SailSt) (hR : Rel st σ) (hpc : σ.PC = f)
    (hP : P st) :
    ∃ n σ' st', sailRun prog base n σ = some σ' ∧ σ'.PC = st.regs.get "ra" &&& ~~~1 ∧
      Rel st' σ' ∧ Q st st' := by
  obtain ⟨n, st', hrun, hq⟩ := h st hP
  obtain ⟨σ', h', hR', hpc'⟩ := sailRun_refines prog base hb hok n ⟨f, st⟩ _ σ hR hpc hrun
  exact ⟨n, σ', st', h', hpc', hR', hq⟩

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvPc64Ref
