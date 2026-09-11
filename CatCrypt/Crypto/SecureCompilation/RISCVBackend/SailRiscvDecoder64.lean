/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder

/-!
# sail-riscv decoder round-trip for the 64-bit bignum subset: `decode (encode i) ≡ i` (#549)

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
`SailRiscvDecoder.emittedRegs` register-name well-formedness side-condition and,
for `SLLI`/`SRLI`, a shift count within the RV64 6-bit `shamt` field
(`sh < 64`).

**Register ceiling:** `emittedRegs = {zero, a0..a7, t0..t6}` (16 names). The
64-bit backend's own allocator pool, `RiscvAsmPrinter64.gpPool64`, is wider — it
also allocates the callee-saved `s2..s11` (25 names total, since the bignum body
has a larger live set than the ChaCha QR). So `roundtrip_RInst64`'s round-trip
is proved only for the `emittedRegs` register names; an `RInst64` whose operand
is allocated from `s2..s11` satisfies the capstone's hypothesis only if that
name is separately shown to be in `emittedRegs` (it is not) — the round-trip is
not yet extended to the full `gpPool64` range.
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
      if fImm12 w < 64 then some (.slli (regName rd) (regName rs1) (fImm12 w)) else none
  | 0x13, 0b101, _ =>
      if fImm12 w < 64 then some (.srli (regName rd) (regName rs1) (fImm12 w)) else none
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
    backend's emitted pool and whose `SRLI`/`SLLI` shift count fits the RV64 6-bit
    `shamt` (`sh < 64`), decoding its encoder word recovers the original
    instruction — against the sail-riscv `encdec` discipline. -/
theorem roundtrip_RInst64 (i : RInst64)
    (hnotli : ∀ d imm, i ≠ .li d imm)
    (hregs : (rinst64DstSrcs i).1 ∈ emittedRegs ∧
             ∀ r ∈ (rinst64DstSrcs i).2, r ∈ emittedRegs)
    (hsh : ∀ d a sh, i = .srli d a sh ∨ i = .slli d a sh → sh < 64) :
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
      have hlt : sh < 64 := hsh d a sh (Or.inl rfl)
      have h5 : ((5 : BitVec 3).toNat) = 5 := rfl
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fFunct3, fImm12,
        (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
        (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
        D.2.1, h5]
      rw [regName_reg5 d hdst, regName_reg5 a ha]
      simp [Nat.mod_eq_of_lt (show sh < 4096 by omega), hlt]
  | slli d a sh =>
      have ha := hsrc a (by simp [rinst64DstSrcs]); simp only [rinst64DstSrcs] at hdst
      have hlt : sh < 64 := hsh d a sh (Or.inr rfl)
      have h1 : ((1 : BitVec 3).toNat) = 1 := rfl
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fFunct3, fImm12,
        (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
        (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
        D.2.1, h1]
      rw [regName_reg5 d hdst, regName_reg5 a ha]
      simp [Nat.mod_eq_of_lt (show sh < 4096 by omega), hlt]
  | mv d s =>
      have hs := hsrc s (by simp [rinst64DstSrcs]); simp only [rinst64DstSrcs] at hdst
      simp only [encodeWord64, Option.get!, riscvDecode64, fOpcode, fRd, fRs1, fFunct3, fImm12,
        (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
        (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
        D.2.1, D.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 s hs]
      simp

/-- Doc-anchor pilot: the `SLTU` carry comparator round-trips (the instruction
    that makes RISC-V's flagless carry chain work). -/
theorem trust_edge_pilot64 :
    riscvDecode64 (encodeWord64 (.sltu "a3" "a0" "a1")).get! = some (.sltu "a3" "a0" "a1") :=
  roundtrip_RInst64 (.sltu "a3" "a0" "a1") (by simp) (by decide)
    (by intro d a sh h; rcases h with h | h <;> cases h)

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
