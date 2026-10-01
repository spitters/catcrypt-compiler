/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
public import CatCrypt.Crypto.SecureCompilation.Memory64

/-!
# RV64 doubleword loads and stores over a byte memory

`RiscvBytes64.MInst64` and `runM64` act on registers only. This module adds a byte memory
as a layer on top: `MState64` pairs an `RState64` with `Memory64.AMem`, and `XInst64` is a
machine instruction, a doubleword load `ld d, off(b)` or a doubleword store
`sd v, off(b)`. Addresses are `b + signExtend off`; the eight bytes are read and written
little-endian (`Memory64.read64`, `Memory64.write64`). A register-only block runs on
`MState64` as on `RState64` and leaves the memory unchanged (`runX_lift`), so every
`runM64` result carries over.

The encoding follows the RISC-V I-type (`ld`: opcode `0x03`, `funct3 = 3`) and S-type
(`sd`: opcode `0x23`, `funct3 = 3`) formats. `ADDI` is admitted on `sp` and `ra` as well
as on the allocator's registers, so a stack adjustment decodes.

## Main definitions

* `MState64`, `XInst64`, `evalX`, `runX`.
* `encodeXWord64`, `encodeXBlock64`, `decodeX64`, `decodeXStream64`, `XInstOK`, `XInstOKb`.

## Main results

* `runX_lift`: a block of `MInst64` runs on `MState64` as `runM64`, memory unchanged.
* `decodeX64_encode`, `decodeXStream64_encode_b`: the decode round trip, per instruction
  and per block.
* `runM64_frame`: a register-only block leaves every register it does not write.

## Alignment

`runX` reads and writes any address: it has no misaligned-access trap. An RV64 processor
may trap a misaligned `ld` or `sd`, or emulate it slowly. The function contracts built on
this layer therefore require `Aligned 16` of `sp` (the psABI's alignment at a call) and
`Aligned 8` of each buffer pointer. Every `ld` and `sd` the RV64 functions in
`Ascent/Demos` execute is at an offset that is a multiple of 8 from such a register, and
their stack frames are multiples of 16 bytes. That the accesses are aligned is read off
the code, not proved.

* `Aligned n a`: `a` is a multiple of `n`; `Aligned.add_ofNat`, `Aligned.add_ofInt_neg`
  and `Aligned.of_dvd` carry it through the offsets of a call.

That `runX` agrees with an RV64 processor (misaligned-access traps, the memory model of a
multi-hart system) is not proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.Memory64 (AMem read64 write64)

/-! ## 1. The machine -/

/-- A machine state: the register file and a byte memory. -/
structure MState64 where
  regs : RState64
  mem : AMem

/-- A machine instruction, a doubleword load, or a doubleword store. -/
inductive XInst64 where
  | m (i : MInst64)
  | ld (d b : String) (off : BitVec 12)
  | sd (v b : String) (off : BitVec 12)

/-- The address `b + signExtend off`. -/
def addr (s : RState64) (b : String) (off : BitVec 12) : BitVec 64 :=
  s.get b + off.signExtend 64

/-- Execute one instruction. -/
def evalX (s : MState64) : XInst64 → MState64
  | .m i => { s with regs := evalMInst64 s.regs i }
  | .ld d b off => { s with regs := s.regs.set d (read64 s.mem (addr s.regs b off)) }
  | .sd v b off => { s with mem := write64 s.mem (addr s.regs b off) (s.regs.get v) }

/-- Execute a block, left to right. -/
def runX (s : MState64) : List XInst64 → MState64
  | [] => s
  | i :: is => runX (evalX s i) is

@[simp] theorem runX_nil (s : MState64) : runX s [] = s := rfl

@[simp] theorem runX_cons (s : MState64) (i : XInst64) (is : List XInst64) :
    runX s (i :: is) = runX (evalX s i) is := rfl

theorem runX_append (s : MState64) (xs ys : List XInst64) :
    runX s (xs ++ ys) = runX (runX s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

/-- **A register-only block runs as `runM64` and leaves the memory.** -/
theorem runX_lift (s : MState64) (b : List MInst64) :
    runX s (b.map .m) = { regs := runM64 s.regs b, mem := s.mem } := by
  induction b generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

/-- The destination of a machine instruction. -/
def mDst : MInst64 → String
  | .base i => (rinst64DstSrcs i).1
  | .addi d _ _ => d

/-- The destinations of a block of machine instructions. -/
def mWrites (b : List MInst64) : List String := b.map mDst

theorem evalMInst64_get_other (s : RState64) (i : MInst64) (r : String) (h : r ≠ mDst i) :
    (evalMInst64 s i).get r = s.get r := by
  cases i with
  | base i =>
    simp only [evalMInst64]
    rw [evalRInst64_eq_set]
    exact RState64.get_set_other _ _ _ _ h
  | addi d a imm => exact RState64.get_set_other _ _ _ _ h

/-- **A register-only block leaves every register it does not write.** -/
theorem runM64_frame (b : List MInst64) (s : RState64) (r : String) (h : r ∉ mWrites b) :
    (runM64 s b).get r = s.get r := by
  induction b generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [mWrites, List.map_cons, List.mem_cons, not_or] at h
    simp only [runM64]
    rw [ih _ h.2, evalMInst64_get_other _ _ _ h.1]

/-! ## 2. Encoding -/

/-- An S-type word: `imm[11:5] @ rs2 @ rs1 @ funct3 @ imm[4:0] @ opcode`. -/
def encS (imm : BitVec 12) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3) (opcode : BitVec 7) :
    BitVec 32 :=
  (imm.extractLsb' 5 7 ++ rs2 ++ rs1 ++ funct3 ++ imm.extractLsb' 0 5 ++ opcode).cast rfl

/-- The S-type immediate of a word: bits `31:25` above bits `11:7`. -/
def sImmS (w : BitVec 32) : BitVec 12 := (w.extractLsb' 25 7 ++ w.extractLsb' 7 5).cast rfl

theorem encS_slices (imm : BitVec 12) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opcode : BitVec 7) :
    sOpcode (encS imm rs2 rs1 funct3 opcode) = opcode ∧
    sFunct3 (encS imm rs2 rs1 funct3 opcode) = funct3 ∧
    sRs1 (encS imm rs2 rs1 funct3 opcode) = rs1 ∧
    sRs2 (encS imm rs2 rs1 funct3 opcode) = rs2 ∧
    sImmS (encS imm rs2 rs1 funct3 opcode) = imm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sOpcode, sFunct3, sRs1, sRs2, sImmS, encS] <;> bv_decide

/-- The word of an instruction (`none` for `li`). -/
def encodeXWord64 : XInst64 → Option (BitVec 32)
  | .m i => encodeMWord64 i
  | .ld d b off => some (encI off (reg5 b) 0b011 (reg5 d) 0x03)
  | .sd v b off => some (encS off (reg5 v) (reg5 b) 0b011 0x23)

/-- The little-endian bytes of a block. -/
def encodeXBlock64 (b : List XInst64) : List (BitVec 8) :=
  b.flatMap fun i => match encodeXWord64 i with
    | some w => wordLE w
    | none => []

/-- Decode one word: `decodeM64`, and otherwise `ld` or `sd`. -/
def decodeX64 (w : BitVec 32) : Option XInst64 :=
  match decodeM64 w with
  | some i => some (.m i)
  | none =>
    if fOpcode w = 0x03 ∧ fFunct3 w = 3 then
      some (.ld (regName (fRd w)) (regName (fRs1 w)) (sImm12 w))
    else if fOpcode w = 0x23 ∧ fFunct3 w = 3 then
      some (.sd (regName (fRs2 w)) (regName (fRs1 w)) (sImmS w))
    else none

/-- The registers a load, a store or a stack `ADDI` may name: `emittedRegs64`, `sp` and
    `ra`. -/
def memRegs64 : List String := emittedRegs64 ++ ["sp", "ra"]

theorem regName_reg5_mem (r : String) (h : r ∈ memRegs64) : regName (reg5 r).toNat = r := by
  simp only [memRegs64, emittedRegs64, emittedRegs, List.cons_append, List.nil_append] at h
  fin_cases h <;> rfl

/-- The side conditions of the round trip. -/
def XInstOK : XInst64 → Prop
  | .m (.addi d a imm) => d ∈ memRegs64 ∧ a ∈ memRegs64 ∧ imm ≠ 0
  | .m i => MInstOK i
  | .ld d b _ => d ∈ memRegs64 ∧ b ∈ memRegs64
  | .sd v b _ => v ∈ memRegs64 ∧ b ∈ memRegs64

/-- `XInstOK` as a `Bool`. -/
def XInstOKb : XInst64 → Bool
  | .m (.addi d a imm) => decide (d ∈ memRegs64) && decide (a ∈ memRegs64) && imm != 0
  | .m i => MInstOKb i
  | .ld d b _ => decide (d ∈ memRegs64) && decide (b ∈ memRegs64)
  | .sd v b _ => decide (v ∈ memRegs64) && decide (b ∈ memRegs64)

theorem XInstOK_of_b (i : XInst64) (h : XInstOKb i = true) : XInstOK i := by
  cases i with
  | m i =>
    cases i with
    | base i => exact MInstOK_of_b _ h
    | addi d a imm => simp_all [XInstOKb, XInstOK, decide_eq_true_eq]
  | ld d b off => simp_all [XInstOKb, XInstOK, decide_eq_true_eq]
  | sd v b off => simp_all [XInstOKb, XInstOK, decide_eq_true_eq]

theorem decodeM64_ld (d b : String) (off : BitVec 12) :
    decodeM64 (encI off (reg5 b) 0b011 (reg5 d) 0x03) = none := by
  have D := decConsts64
  simp only [decodeM64, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fImm12, fFunct7,
    (encI_slices ..).1, (encI_slices ..).2.2.1]
  simp

theorem decodeM64_sd (v b : String) (off : BitVec 12) :
    decodeM64 (encS off (reg5 v) (reg5 b) 0b011 0x23) = none := by
  simp only [decodeM64, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fImm12, fFunct7,
    (encS_slices ..).1, (encS_slices ..).2.1]
  simp

theorem decodeM64_addi_mem (d a : String) (imm : BitVec 12) (hd : d ∈ memRegs64)
    (ha : a ∈ memRegs64) (hi : imm ≠ 0) :
    decodeM64 (encI imm (reg5 a) 0b000 (reg5 d) 0x13) = some (.addi d a imm) := by
  have D := decConsts64
  simp only [decodeM64, riscvDecode64_addi d a imm hi, fOpcode, fRd, fRs1, fFunct3, fImm12,
    (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
    (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2, D.2.1, D.2.2.2.2.2.1,
    regName_reg5_mem d hd, regName_reg5_mem a ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp

/-- **One instruction decodes from its word.** -/
theorem decodeX64_encode (i : XInst64) (h : XInstOK i) :
    ∃ w, encodeXWord64 i = some w ∧ decodeX64 w = some i := by
  cases i with
  | m i =>
    cases i with
    | base i =>
      obtain ⟨w, hw, hd⟩ := decodeM64_encode (.base i) h
      exact ⟨w, hw, by simp [decodeX64, hd]⟩
    | addi d a imm =>
      obtain ⟨hd, ha, hi⟩ := h
      refine ⟨_, rfl, ?_⟩
      unfold decodeX64
      rw [decodeM64_addi_mem d a imm hd ha hi]
  | ld d b off =>
    obtain ⟨hd, hb⟩ := h
    refine ⟨_, rfl, ?_⟩
    simp only [decodeX64, decodeM64_ld, fOpcode, fFunct3, fRd, fRs1,
      (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
      (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
      regName_reg5_mem d hd, regName_reg5_mem b hb]
    simp
  | sd v b off =>
    obtain ⟨hv, hb⟩ := h
    refine ⟨_, rfl, ?_⟩
    simp only [decodeX64, decodeM64_sd, fOpcode, fFunct3, fRs2, fRs1,
      (encS_slices ..).1, (encS_slices ..).2.1, (encS_slices ..).2.2.1,
      (encS_slices ..).2.2.2.1, (encS_slices ..).2.2.2.2,
      regName_reg5_mem v hv, regName_reg5_mem b hb]
    simp

/-! ## 3. The byte stream -/

/-- Decode `n` instructions from `bs`, which must be used up exactly. -/
def decodeXStream64 : Nat → List (BitVec 8) → Option (List XInst64)
  | 0, bs => if bs.isEmpty then some [] else none
  | n + 1, b0 :: b1 :: b2 :: b3 :: rest =>
    match decodeX64 (leWord b0 b1 b2 b3) with
    | some i => (decodeXStream64 n rest).map (i :: ·)
    | none => none
  | _ + 1, _ => none

/-- **A block decodes from its bytes.** -/
theorem decodeXStream64_encode (b : List XInst64) (h : ∀ i ∈ b, XInstOK i) :
    decodeXStream64 b.length (encodeXBlock64 b) = some b := by
  induction b with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨w, hw, hd⟩ := decodeX64_encode i (h i (by simp))
    obtain ⟨b0, b1, b2, b3, hle, hlw⟩ := wordLE_leWord w
    have ih' := ih fun j hj => h j (by simp [hj])
    simp only [encodeXBlock64, List.flatMap_cons, hw, hle, List.length_cons] at ih' ⊢
    simp only [List.cons_append, List.nil_append, decodeXStream64, hlw, hd, ih',
      Option.map_some]

theorem decodeXStream64_encode_b (b : List XInst64) (h : b.all XInstOKb = true) :
    decodeXStream64 b.length (encodeXBlock64 b) = some b :=
  decodeXStream64_encode b fun i hi => XInstOK_of_b i (List.all_eq_true.1 h i hi)

/-! ## Alignment -/

/-- `a` is a multiple of `n`, as an unsigned 64-bit value. -/
def Aligned (n : Nat) (a : BitVec 64) : Prop := a.toNat % n = 0

theorem Aligned.add_ofNat {n : Nat} (hn : n ∣ 2 ^ 64) {a : BitVec 64} (h : Aligned n a)
    {k : Nat} (hk : n ∣ k) : Aligned n (a + BitVec.ofNat 64 k) := by
  unfold Aligned at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hn, Nat.add_mod, h,
    Nat.mod_mod_of_dvd _ hn, Nat.mod_eq_zero_of_dvd hk, Nat.zero_add, Nat.zero_mod]

theorem ofInt_neg_eq (k : Nat) :
    BitVec.ofInt 64 (-(k : Int)) = BitVec.ofNat 64 (2 ^ 64 - k % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem Aligned.add_ofInt_neg {n : Nat} (hn : n ∣ 2 ^ 64) {a : BitVec 64} (h : Aligned n a)
    {k : Nat} (hk : n ∣ k) : Aligned n (a + BitVec.ofInt 64 (-(k : Int))) := by
  rw [ofInt_neg_eq]
  exact h.add_ofNat hn (Nat.dvd_sub hn ((Nat.dvd_mod_iff hn).2 hk))

theorem Aligned.of_dvd {m n : Nat} {a : BitVec 64} (h : Aligned n a) (hmn : m ∣ n) :
    Aligned m a :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hmn (Nat.dvd_of_mod_eq_zero h))

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
