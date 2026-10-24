/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder

/-!
# sail-riscv decoder round-trip for the 64-bit bignum subset: `decode (encode i) ≡ i`

`SailRiscvDecoder.lean` proves `riscvDecode (encodeWord i) = some i` for the
scalar 32-bit-word `RInst` subset. This module is its **64-bit bignum**
counterpart: a decoder `riscvDecode64` that recovers the
`(funct7, rs2, rs1, funct3, rd, opcode)` fields and reconstructs the `RInst64`,
transcribed from the official sail-riscv `encdec` clauses
(`model/extensions/I/base_insts.sail` for `RTYPE`/`ITYPE`,
`model/extensions/M/mext_insts.sail` for `MUL`/`MULHU`), and the round-trip

```
riscvDecode64 (encodeWord64 i) = some i   -- for every non-LI RInst64 the backend emits
```

It reuses the sail `@`⁻¹ field-slice lemmas (`SailRiscvDecoder.encR_slices` /
`encI_slices`) and the register-name inverse (`regName_reg5`). The `MUL` arm adds
the M-extension funct7 `0b0000001 = 0x01` dispatch.

## Scope

Every **fixed-width** `RInst64` arm round-trips here: `ADD`/`SUB`/`SLTU`/`AND`/
`OR`/`XOR` (RTYPE), `MUL`/`MULHU` (M-extension RTYPE), `MV` (= `ADDI rd,rs,0`,
ITYPE) and `SLLI`/`SRLI` (SHIFTIOP, ITYPE). The single exception is `LI` — the
assembler pseudo-op `as` expands to a *variable-length* `lui`+`addi`(+…)
sequence; it has no single 32-bit word, so `encodeWord64 (.li ..) = none` and it
is **not** round-trip-proved (it is the trusted constant-materialisation
scaffolding, the RV64 analogue of the prologue). The capstone
`roundtrip_RInst64` quantifies over all non-`LI` `RInst64` with the
`SailRiscvDecoder.emittedRegs` register-name well-formedness side-condition; the
`SLLI`/`SRLI` shift count is a `Fin 64`, the RV64 6-bit `shamt` field.

Section 4 decodes the memory-and-branch fragment `RMInst64` (`LD`, `SD`, `BNE`, `ADDI` with a
non-zero immediate) with `riscvDecodeM64` and proves its round trip `roundtrip_RMInst64`
for immediates within their fields.

**Register ceiling:** `emittedRegs = {zero, a0..a7, t0..t6}` (16 names). The
64-bit backend's own allocator pool, `RiscvAsmPrinter64.gpPool64`, is wider — it
also allocates the callee-saved `s2..s11` (25 names total, since the bignum body
has a larger live set than the ChaCha QR). So `roundtrip_RInst64`'s round-trip
is proved only for the `emittedRegs` register names; an `RInst64` whose operand
is allocated from `s2..s11` satisfies the capstone's hypothesis only if that
name is separately shown to be in `emittedRegs` (it is not) — the full `gpPool64` range is
outside the round-trip's scope.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder

/-! ## 1. The 64-bit decoder

Dispatches on `(opcode, funct3, funct7)` per the sail `encdec` clauses for the
RTYPE / M-extension / ITYPE subset. -/

/-- Decode a 32-bit RV64 instruction word back to an `RInst64`, per the sail-riscv
    `encdec` clauses for the emitted 64-bit bignum subset. Returns `none` for a
    word outside the subset. -/
def riscvDecode64 (w : BitVec 32) : Option RInst64 :=
  let rd := fRd w; let rs1 := fRs1 w; let rs2 := fRs2 w
  let f3 := fFunct3 w; let f7 := fFunct7 w
  match fOpcode w, f3, f7 with
  -- RTYPE (opcode 0x33), funct7 0: ADD (f3=0), SLTU (f3=3), XOR (f3=4), OR (f3=6), AND (f3=7)
  | 0x33, 0b000, 0x00 => some (.add  (regName rd) (regName rs1) (regName rs2))
  | 0x33, 0b011, 0x00 => some (.sltu (regName rd) (regName rs1) (regName rs2))
  | 0x33, 0b100, 0x00 => some (.xor  (regName rd) (regName rs1) (regName rs2))
  | 0x33, 0b110, 0x00 => some (.or   (regName rd) (regName rs1) (regName rs2))
  | 0x33, 0b111, 0x00 => some (.and  (regName rd) (regName rs1) (regName rs2))
  -- RTYPE (opcode 0x33), funct7 0x20: SUB (f3=0)
  | 0x33, 0b000, 0x20 => some (.sub  (regName rd) (regName rs1) (regName rs2))
  -- M-extension (opcode 0x33), funct7 0x01: MUL (f3=0), MULHU (f3=3)
  | 0x33, 0b000, 0x01 => some (.mul   (regName rd) (regName rs1) (regName rs2))
  | 0x33, 0b011, 0x01 => some (.mulhu (regName rd) (regName rs1) (regName rs2))
  -- ITYPE ADDI (opcode 0x13, f3=0): MV pseudo when imm = 0
  | 0x13, 0b000, _ =>
      if fImm12 w = 0 then some (.mv (regName rd) (regName rs1)) else none
  -- SHIFTIOP (opcode 0x13): SLLI (f3=1), SRLI (f3=5). On RV64 the shift amount is
  -- the 6-bit `shamt = imm[5:0]` and `funct6 = imm[11:6]` is `0b000000`; the two
  -- conditions together are `imm12 < 64`, which also separates SRLI from SRAI
  -- (`funct6 = 0b010000`, so `imm12 ≥ 1024`).
  | 0x13, 0b001, _ =>
      if h : fImm12 w < 64 then some (.slli (regName rd) (regName rs1) ⟨fImm12 w, h⟩) else none
  | 0x13, 0b101, _ =>
      if h : fImm12 w < 64 then some (.srli (regName rd) (regName rs1) ⟨fImm12 w, h⟩) else none
  | _, _, _ => none

/-! ## 2. The dispatch-constant reductions (the funct7/funct3/opcode literals) -/

/-- The sail dispatch constants the decode matches on, reduced to Nat literals. -/
theorem decConsts64 :
    ((51 : BitVec 7).toNat = 51) ∧ ((19 : BitVec 7).toNat = 19) ∧
    ((0 : BitVec 7).toNat = 0) ∧ ((32 : BitVec 7).toNat = 32) ∧
    ((1 : BitVec 7).toNat = 1) ∧
    ((0 : BitVec 3).toNat = 0) ∧ ((3 : BitVec 3).toNat = 3) ∧
    ((4 : BitVec 3).toNat = 4) ∧ ((6 : BitVec 3).toNat = 6) ∧
    ((7 : BitVec 3).toNat = 7) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. The per-instruction and capstone round-trip

Each emitted non-`LI` arm decodes back to itself, via the sail `@`⁻¹ slice lemmas
and `regName_reg5`. -/

/-- **The capstone round-trip `decode (encode i) = i` for the full emitted 64-bit
    bignum subset** (every fixed-width arm; `LI` excluded as the variable-length
    pseudo-op). For every non-`LI` `RInst64` whose register names are in the
    backend's emitted pool, decoding its encoder word recovers the original
    instruction — against the sail-riscv `encdec` discipline. The `SRLI`/`SLLI`
    shift count is a `Fin 64`, the RV64 6-bit `shamt`, so the statement carries no
    range condition on it. -/
theorem roundtrip_RInst64 (i : RInst64)
    (hnotli : ∀ d imm, i ≠ .li d imm)
    (hregs : (rinst64DstSrcs i).1 ∈ emittedRegs ∧
             ∀ r ∈ (rinst64DstSrcs i).2, r ∈ emittedRegs) :
    riscvDecode64 (encodeWord64 i).get! = some i := by
  obtain ⟨hdst, hsrc⟩ := hregs
  have D := decConsts64
  have S := @encR_slices
  cases i with
  | add d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.1, D.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | sub d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.2.1, D.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | sltu d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.1, D.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | and d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.1, D.2.2.2.2.2.2.2.2.2]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | or d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.1, D.2.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | xor d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.1, D.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | mul d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]; rfl
  | mulhu d a b =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); have hb := hsrc b (by simp [rinst64DstSrcs])
      simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (S ..).1, (S ..).2.1, (S ..).2.2.1, (S ..).2.2.2.1, (S ..).2.2.2.2.1, (S ..).2.2.2.2.2,
        D.1, D.2.2.2.2.1, D.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | li d imm => exact absurd rfl (hnotli d imm)
  | srli d a sh =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); simp only [rinst64DstSrcs] at hdst
      have hlt : sh.val < 64 := sh.isLt
      have h5 : ((5 : BitVec 3).toNat) = 5 := rfl
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fFunct3, fImm12,
        (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
        (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
        D.2.1, h5]
      rw [regName_reg5 d hdst, regName_reg5 a ha]
      simp [Nat.mod_eq_of_lt (show sh.val < 4096 by omega), hlt]
  | slli d a sh =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); simp only [rinst64DstSrcs] at hdst
      have hlt : sh.val < 64 := sh.isLt
      have h1 : ((1 : BitVec 3).toNat) = 1 := rfl
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fFunct3, fImm12,
        (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
        (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
        D.2.1, h1]
      rw [regName_reg5 d hdst, regName_reg5 a ha]
      simp [Nat.mod_eq_of_lt (show sh.val < 4096 by omega), hlt]
  | mv d s =>
      have hs := hsrc s (by simp [rinst64DstSrcs]); simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fFunct3, fImm12,
        (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
        (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
        D.2.1, D.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 s hs]
      simp

/-! ## 4. The memory-and-branch fragment

`riscvDecodeM64` decodes the `RMInst64` words: `LD` (opcode `0x03`, funct3 `0b011`), `SD`
(opcode `0x23`, funct3 `0b011`), `BNE` (opcode `0x63`, funct3 `0b001`), `ADDI` with a non-zero
immediate (opcode `0x13`, funct3 `0`), and every other word through `riscvDecode64` as a
register instruction. The immediates are read sign-extended (`BitVec.toInt`), as the sail
clauses `sign_extend(imm)` do. -/

/-- The 12-bit S-type immediate `imm[11:5] @ imm[4:0]` of a word. -/
def sImmS (w : BitVec 32) : BitVec 12 :=
  (w.extractLsb' 25 7 ++ w.extractLsb' 7 5).cast rfl

/-- The S-type slices of `encStype` recover opcode, funct3, rs1, rs2 and the immediate. -/
theorem encStype_slices (imm : BitVec 12) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opcode : BitVec 7) :
    sOpcode (encStype imm rs2 rs1 funct3 opcode) = opcode ∧
    sFunct3 (encStype imm rs2 rs1 funct3 opcode) = funct3 ∧
    sRs1    (encStype imm rs2 rs1 funct3 opcode) = rs1 ∧
    sRs2    (encStype imm rs2 rs1 funct3 opcode) = rs2 ∧
    sImmS   (encStype imm rs2 rs1 funct3 opcode) = imm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sOpcode, sFunct3, sRs1, sRs2, sImmS, encStype] <;> bv_decide

/-- Decode a 32-bit RV64 word to an `RMInst64`, per the sail-riscv `encdec` clauses of
    `LOAD`, `STORE`, `BTYPE` and `ITYPE`, and `riscvDecode64` otherwise. -/
def riscvDecodeM64 (w : BitVec 32) : Option RMInst64 :=
  if fOpcode w = 0x03 then
    if fFunct3 w = 0b011 then some (.ld (regName (fRd w)) (regName (fRs1 w)) (sImm12 w).toInt)
    else none
  else if fOpcode w = 0x23 then
    if fFunct3 w = 0b011 then some (.sd (regName (fRs2 w)) (regName (fRs1 w)) (sImmS w).toInt)
    else none
  else if fOpcode w = 0x63 then
    if fFunct3 w = 0b001 then some (.bne (regName (fRs1 w)) (regName (fRs2 w)) (sImmB w).toInt)
    else none
  else if fOpcode w = 0x13 ∧ fFunct3 w = 0 ∧ fImm12 w ≠ 0 then
    some (.addi (regName (fRd w)) (regName (fRs1 w)) (sImm12 w).toInt)
  else (riscvDecode64 w).map .alu

/-- A word `riscvDecode64` decodes is decoded by `riscvDecodeM64` as the same register
    instruction. -/
theorem riscvDecodeM64_of_decode64 {w : BitVec 32} {i : RInst64}
    (h : riscvDecode64 w = some i) : riscvDecodeM64 w = some (.alu i) := by
  unfold riscvDecodeM64
  by_cases h3 : fOpcode w = 0x03
  · simp [riscvDecode64, h3] at h
  by_cases h23 : fOpcode w = 0x23
  · simp [riscvDecode64, h23] at h
  by_cases h63 : fOpcode w = 0x63
  · simp [riscvDecode64, h63] at h
  rw [ite_eq_right h3, ite_eq_right h23, ite_eq_right h63]
  by_cases hA : fOpcode w = 0x13 ∧ fFunct3 w = 0 ∧ fImm12 w ≠ 0
  · obtain ⟨h13, hf, hi⟩ := hA
    simp [riscvDecode64, h13, hf, hi] at h
  · rw [ite_eq_right hA, h]; rfl

/-- The sign-extended 12-bit immediate of an in-range integer is the integer. -/
theorem toInt_ofInt12 {i : Int} (h1 : -2048 ≤ i) (h2 : i < 2048) :
    (BitVec.ofInt 12 i).toInt = i := by
  rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le h1 h2

/-- The B-type immediate field keeps an even 13-bit offset. -/
theorem ofInt13_and_even {i : Int} (he : i % 2 = 0) :
    (BitVec.ofInt 13 i) &&& 0x1ffe = BitVec.ofInt 13 i := by
  have key : ∀ x : BitVec 13, x &&& 1 = 0 → x &&& 0x1ffe = x := by intro x; bv_decide
  apply key
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofInt, show (1 : BitVec 13).toNat = 1 from rfl,
    Nat.and_one_is_mod, show (0 : BitVec 13).toNat = 0 from rfl]
  omega

/-- The immediate-range side condition of the round trip: 12-bit signed for `ADDI` (and
    non-zero, `ADDI rd, rs, 0` being `MV`), `LD`, `SD`; 13-bit signed and even for `BNE`. -/
def RMImmOK : RMInst64 → Prop
  | .alu _ => True
  | .addi _ _ imm => -2048 ≤ imm ∧ imm < 2048 ∧ imm ≠ 0
  | .ld _ _ off => -2048 ≤ off ∧ off < 2048
  | .sd _ _ off => -2048 ≤ off ∧ off < 2048
  | .bne _ _ off => -4096 ≤ off ∧ off < 4096 ∧ off % 2 = 0

/-- The registers an `RMInst64` names. -/
def rminst64Regs : RMInst64 → List String
  | .alu i => (rinst64DstSrcs i).1 :: (rinst64DstSrcs i).2
  | .addi d a _ => [d, a]
  | .ld d base _ => [d, base]
  | .sd src base _ => [src, base]
  | .bne a b _ => [a, b]

/-- **The round trip of the memory-and-branch fragment**: for an `RMInst64` with its
    registers in `emittedRegs`, its immediates in range, and a register instruction under
    the side conditions of `roundtrip_RInst64`, decoding the encoder word with
    `riscvDecodeM64` recovers the instruction. -/
theorem roundtrip_RMInst64 (i : RMInst64)
    (hregs : ∀ r ∈ rminst64Regs i, r ∈ emittedRegs) (himm : RMImmOK i)
    (halu : ∀ j, i = .alu j → ∀ d imm, j ≠ .li d imm) :
    riscvDecodeM64 (encodeMWord64 i).get! = some i := by
  cases i with
  | alu j =>
      have hnl := halu j rfl
      exact riscvDecodeM64_of_decode64 (roundtrip_RInst64 j hnl
        ⟨hregs _ (by simp [rminst64Regs]), fun r hr => hregs r (by simp [rminst64Regs, hr])⟩)
  | addi d a imm =>
      obtain ⟨h1, h2, h0⟩ := himm
      have hd := hregs d (by simp [rminst64Regs]); have ha := hregs a (by simp [rminst64Regs])
      obtain ⟨ho, hrd, hf, hrs, hi⟩ := encI_slices (BitVec.ofInt 12 imm) (reg5 a) 0b000 (reg5 d) 0x13
      have hne : (BitVec.ofInt 12 imm).toNat ≠ 0 := by
        intro hz
        apply h0
        rw [← toInt_ofInt12 h1 h2, BitVec.toInt_eq_toNat_cond, hz]; simp
      simp only [encodeMWord64, Option.get!, riscvDecodeM64, fOpcode, fFunct3, fRd, fRs1, fImm12,
        ho, hrd, hf, hrs, hi, regName_reg5 d hd, regName_reg5 a ha, toInt_ofInt12 h1 h2]
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left ⟨by decide, by decide, hne⟩]
  | ld d base off =>
      obtain ⟨h1, h2⟩ := himm
      have hd := hregs d (by simp [rminst64Regs]); have hb := hregs base (by simp [rminst64Regs])
      obtain ⟨ho, hrd, hf, hrs, hi⟩ :=
        encI_slices (BitVec.ofInt 12 off) (reg5 base) 0b011 (reg5 d) 0x03
      simp only [encodeMWord64, Option.get!, riscvDecodeM64, fOpcode, fFunct3, fRd, fRs1,
        ho, hrd, hf, hrs, hi, regName_reg5 d hd, regName_reg5 base hb, toInt_ofInt12 h1 h2]
      rfl
  | sd src base off =>
      obtain ⟨h1, h2⟩ := himm
      have hs := hregs src (by simp [rminst64Regs]); have hb := hregs base (by simp [rminst64Regs])
      obtain ⟨ho, hf, hrs1, hrs2, hi⟩ :=
        encStype_slices (BitVec.ofInt 12 off) (reg5 src) (reg5 base) 0b011 0x23
      simp only [encodeMWord64, Option.get!, riscvDecodeM64, fOpcode, fFunct3, fRs1, fRs2,
        ho, hf, hrs1, hrs2, hi, regName_reg5 src hs, regName_reg5 base hb, toInt_ofInt12 h1 h2]
      rfl
  | bne a b off =>
      obtain ⟨h1, h2, he⟩ := himm
      have ha := hregs a (by simp [rminst64Regs]); have hb := hregs b (by simp [rminst64Regs])
      obtain ⟨ho, hf, hrs1, hrs2, hi⟩ :=
        encB_slices (BitVec.ofInt 13 off) (reg5 b) (reg5 a) 0b001 0x63
      have hti : (BitVec.ofInt 13 off).toInt = off := by
        rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le h1 h2
      simp only [encodeMWord64, Option.get!, riscvDecodeM64, fOpcode, fFunct3, fRs1, fRs2,
        ho, hf, hrs1, hrs2, hi, ofInt13_and_even he, hti, regName_reg5 a ha, regName_reg5 b hb]
      rfl

/-- Doc-anchor pilot: the `SLTU` carry comparator round-trips (the instruction
    that makes RISC-V's flagless carry chain work). -/
theorem trust_edge_pilot64 :
    riscvDecode64 (encodeWord64 (.sltu "a3" "a0" "a1")).get! = some (.sltu "a3" "a0" "a1") :=
  roundtrip_RInst64 (.sltu "a3" "a0" "a1") (by simp) (by decide)

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
