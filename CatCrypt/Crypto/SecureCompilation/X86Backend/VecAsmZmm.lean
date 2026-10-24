/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmByteEncoder

/-!
# The x86 encoding table of the vector instructions in `%zmm` mode

`zmmAsm P` is a table `VecImage.VecAsm`: the x86-64 machine encoding of each vector
instruction `VecMach.VInstr` that has one at vector length 512, and none for the others.
`P` is the read-only data: a constant pool that places each read-only vector at an absolute
address.

Every instruction but two is an EVEX instruction `62 P0 P1 P2 op ModRM [SIB] [disp] [imm]`
(Intel SDM Vol. 2, §2.7): the payload bytes are those of `ZmmByteEncoder.evexP0`,
`evexP1` and `evexP2` with vector length `L'L = 10`, no zeroing and no broadcast. The
operand forms are
* register-direct (`ModRM.mod = 11`), as in `ZmmByteEncoder.encEvexRR`;
* a memory operand `[base + index·scale + disp]`, always through a SIB byte (`ModRM.rm =
  100`): no displacement when it is zero and the base is not `rbp`/`r13`, the compressed
  displacement `disp8·N` with `N = 64` (SDM §2.7.5, full-vector memory operand) when the
  displacement is a multiple of 64 in range, and `disp32` otherwise;
* an absolute address `[disp32]` (`ModRM.mod = 00`, `SIB.base = 101`, no index), for the
  read-only vectors of `P`.
The two others are the two-byte VEX instructions `vzeroupper` (`C5 F8 77`) and
`kmovw %eax, %kN` (`C5 F8 92 /r`, `VEX.L0.0F.W0 92`).

An instruction has no encoding when its operation has no instruction at its lane width,
its immediate exceeds a byte, its displacement exceeds 32 bits, a base or index name is no
64-bit register, the index is `%rsp`, its scale is not 1, 2, 4 or 8, its mask register is
`%k0`, or its read-only vector is outside the pool.

`zmmAsm_lawful` proves that the table meets `VecImage.VecAsm.Lawful`. The proof decodes:
`decF` reads the fields of an EVEX instruction back from its bytes (`decF_encF`), and
`ofF` reads the instruction back from the fields (`ofF_toF`).

## Main definitions

* `Pool`: the addresses of the read-only vectors, with their inverse.
* `EvexF`, `encF`, `decF`: the fields of an EVEX instruction, its bytes, and the decoder.
* `opTab`: the opcode map, opcode byte and `EVEX.W` of a lane-wise operation.
* `toF`, `ofF`: the fields of an EVEX-encoded vector instruction and their inverse.
* `zmmEnc`, `zmmAsm`: the table.

## Main results

* `decF_encF`: the decoder inverts the encoder on valid fields.
* `ofF_toF`, `toF_valid`: the instruction is read back from its fields, which are valid.
* `zmmAsm_lawful`: the table is lawful.
* `zmmEnc_op64_eq_pack`: on the 64-bit lane-wise operations the table is
  `ZmmByteEncoder.encodeZmmPackInst`, whose bytes are pinned against GNU as
  (`ZmmByteEncoder.encodeZmmPack_map0F_eq_gas`, `encodeZmmPack_map0F38_eq_gas`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecAsmZmm

open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach (VInstr VAddr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmByteEncoder (evexP0 evexP1 evexP2 encEvexRR
  encEvex512W1 encodeZmmPackInst zmmPackOpcode zmmRegsOk)
open CatCrypt.Crypto.SecureCompilation.VIR.YmmByteEncoder (ymmBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt (bit cbit modRMReg)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (LOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (gpNum?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (regName)

/-! ## 1. Bit fields -/

theorem land1 (n : Nat) : n &&& 1 = n % 2 := Nat.and_two_pow_sub_one_eq_mod n 1
theorem land3 (n : Nat) : n &&& 3 = n % 4 := Nat.and_two_pow_sub_one_eq_mod n 2
theorem land7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem land15 (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4

theorem bit_eq (n i : Nat) : bit n i = n / 2 ^ i % 2 := by
  simp [bit, Nat.shiftRight_eq_div_pow]

/-- The four little-endian bytes of the two's-complement value of `d` modulo `2 ^ 32`. -/
def le32 (d : Int) : List Nat :=
  let u : Nat := (d % 2 ^ 32).toNat
  [u % 256, u / 256 % 256, u / 65536 % 256, u / 16777216 % 256]

/-- The signed value of four little-endian bytes. -/
def sext32 (b0 b1 b2 b3 : Nat) : Int :=
  let u : Nat := b0 % 256 + 256 * (b1 % 256) + 65536 * (b2 % 256) + 16777216 * (b3 % 256)
  if u < 2 ^ 31 then (u : Int) else (u : Int) - 2 ^ 32

/-- The byte of the two's-complement value of `k` modulo `256`. -/
def le8 (k : Int) : Nat := (k % 256).toNat

/-- The signed value of a byte. -/
def sext8 (b : Nat) : Int := if b % 256 < 128 then ((b % 256 : Nat) : Int) else
  ((b % 256 : Nat) : Int) - 256

/-- A displacement that fits a sign-extended 32-bit field. -/
def Fits32 (d : Int) : Prop := -2 ^ 31 ≤ d ∧ d < 2 ^ 31

instance (d : Int) : Decidable (Fits32 d) := inferInstanceAs (Decidable (_ ∧ _))

/-- A displacement that has the compressed form `disp8·64`. -/
def Disp8 (d : Int) : Prop := d % 64 = 0 ∧ -128 ≤ d / 64 ∧ d / 64 ≤ 127

instance (d : Int) : Decidable (Disp8 d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## 2. The fields of an EVEX instruction -/

/-- A memory operand. -/
inductive MemF where
  /-- `[base + index · 2 ^ scale + disp]`; the index is absent or a register number with a
      scale code. -/
  | sib (base : Nat) (idx : Option (Nat × Nat)) (disp : Int)
  /-- The absolute address `[disp32]`. -/
  | abs (a : Int)
  deriving DecidableEq

/-- The operand of `ModRM.rm`: a vector register or a memory operand. -/
inductive RmF where
  /-- A vector register. -/
  | reg (r : Nat)
  /-- A memory operand. -/
  | mem (m : MemF)
  deriving DecidableEq

/-- The fields of an EVEX instruction at vector length 512 without zeroing or broadcast:
    opcode map `mm`, implied prefix `pp`, `EVEX.W`, opmask `aaa`, opcode byte, the
    `ModRM.reg` operand (a register or an opcode extension), the `vvvv` register, the
    `ModRM.rm` operand and an optional immediate byte. -/
structure EvexF where
  /-- The opcode map. -/
  mm : Nat
  /-- The implied prefix. -/
  pp : Nat
  /-- `EVEX.W`. -/
  w : Nat
  /-- The opmask register. -/
  aaa : Nat
  /-- The opcode byte. -/
  op : Nat
  /-- The `ModRM.reg` operand. -/
  reg : Nat
  /-- The `vvvv` register. -/
  vvvv : Nat
  /-- The `ModRM.rm` operand. -/
  rm : RmF
  /-- The immediate byte. -/
  imm : Option Nat
  deriving DecidableEq

/-- The register number whose bits 4 and 3 are `EVEX.X` and `EVEX.B`: the register itself
    for a register operand, the bit 3 of the index and of the base for a memory operand. -/
def RmF.xb : RmF → Nat
  | .reg r => r
  | .mem (.abs _) => 0
  | .mem (.sib b idx _) => (match idx with | none => 0 | some (x, _) => x / 8 % 2) * 16
      + b / 8 % 2 * 8

/-- The SIB byte of a memory operand with base `b` and index `idx`; index `100` is no
    index. -/
def sibByte (b : Nat) (idx : Option (Nat × Nat)) : Nat :=
  (match idx with | none => 32 | some (x, s) => s * 64 + x % 8 * 8) + b % 8

/-- The `ModRM`, SIB and displacement bytes of the operand `rm` with `ModRM.reg = reg`. -/
def rmBytes (reg : Nat) : RmF → List Nat
  | .reg r => [modRMReg reg r]
  | .mem (.abs a) => [reg % 8 * 8 + 4, 0x25] ++ le32 a
  | .mem (.sib b idx d) =>
      if d = 0 ∧ b % 8 ≠ 5 then [reg % 8 * 8 + 4, sibByte b idx]
      else if Disp8 d then [64 + reg % 8 * 8 + 4, sibByte b idx, le8 (d / 64)]
      else [128 + reg % 8 * 8 + 4, sibByte b idx] ++ le32 d

/-- An immediate byte follows the instructions of map `0F3A` and the shifts and rotates
    `66 0F 72` and `66 0F 73`. -/
def hasImm (mm op : Nat) : Bool := mm == 3 || (mm == 1 && (op == 0x72 || op == 0x73))

/-- The bytes of an EVEX instruction (vector length 512, `z = 0`, `b = 0`). -/
def encF (f : EvexF) : List (BitVec 8) :=
  ([0x62, evexP0 f.reg f.rm.xb f.mm, evexP1 f.w f.vvvv f.pp, evexP2 0 2 0 f.vvvv f.aaa, f.op]
    ++ rmBytes f.reg f.rm ++ f.imm.toList).map (BitVec.ofNat 8)

/-- The fields of an operand that the encoding represents. -/
def RmF.Valid : RmF → Prop
  | .reg r => r < 32
  | .mem (.abs a) => Fits32 a
  | .mem (.sib b idx d) =>
      b < 16 ∧ (∀ x s, idx = some (x, s) → x < 16 ∧ x ≠ 4 ∧ s < 4) ∧ Fits32 d

/-- The fields that the encoding represents. -/
structure EvexF.Valid (f : EvexF) : Prop where
  mm : f.mm < 4
  pp : f.pp < 4
  w : f.w < 2
  aaa : f.aaa < 8
  op : f.op < 256
  reg : f.reg < 32
  vvvv : f.vvvv < 32
  rm : f.rm.Valid
  imm : ∀ i, f.imm = some i → i < 256
  hasImm : f.imm.isSome = hasImm f.mm f.op

/-! ## 3. The decoder of EVEX fields -/

/-- Read the `ModRM.rm` operand, given the `ModRM` byte and the bits `X` and `B`. -/
def decRm (m X B : Nat) (rest : List (BitVec 8)) : Option (RmF × List (BitVec 8)) :=
  if m / 64 = 3 then some (.reg (X * 16 + B * 8 + m % 8), rest)
  else
    match rest with
    | s :: rest =>
      let base := B * 8 + s.toNat % 8
      let ix := X * 8 + s.toNat / 8 % 8
      let idx := if ix = 4 then none else some (ix, s.toNat / 64)
      if m / 64 = 0 then
        if s.toNat % 8 = 5 then
          match rest with
          | d0 :: d1 :: d2 :: d3 :: r =>
              some (.mem (.abs (sext32 d0.toNat d1.toNat d2.toNat d3.toNat)), r)
          | _ => none
        else some (.mem (.sib base idx 0), rest)
      else if m / 64 = 1 then
        match rest with
        | d :: r => some (.mem (.sib base idx (64 * sext8 d.toNat)), r)
        | [] => none
      else
        match rest with
        | d0 :: d1 :: d2 :: d3 :: r =>
            some (.mem (.sib base idx (sext32 d0.toNat d1.toNat d2.toNat d3.toNat)), r)
        | _ => none
    | [] => none

/-- **The decoder of EVEX fields**: the fields of the EVEX instruction at the front of a
    stream, with the bytes that follow. -/
def decF : List (BitVec 8) → Option (EvexF × List (BitVec 8))
  | b0 :: p0 :: p1 :: p2 :: op :: modrm :: rest =>
    if b0.toNat = 0x62 then
      let R := 1 - p0.toNat / 128 % 2
      let X := 1 - p0.toNat / 64 % 2
      let B := 1 - p0.toNat / 32 % 2
      let R' := 1 - p0.toNat / 16 % 2
      let mm := p0.toNat % 8
      let reg := R' * 16 + R * 8 + modrm.toNat / 8 % 8
      let vvvv := (1 - p2.toNat / 8 % 2) * 16 + (15 - p1.toNat / 8 % 16)
      (decRm modrm.toNat X B rest).bind fun q =>
        if hasImm mm op.toNat then
          match q.2 with
          | i :: r => some (⟨mm, p1.toNat % 4, p1.toNat / 128, p2.toNat % 8, op.toNat, reg,
              vvvv, q.1, some i.toNat⟩, r)
          | [] => none
        else some (⟨mm, p1.toNat % 4, p1.toNat / 128, p2.toNat % 8, op.toNat, reg, vvvv, q.1,
          none⟩, q.2)
    else none
  | _ => none

theorem decRm_reg (m X B : Nat) (rest : List (BitVec 8)) (h : m / 64 = 3) :
    decRm m X B rest = some (.reg (X * 16 + B * 8 + m % 8), rest) := by
  simp [decRm, h]

theorem decF_cons (p0 p1 p2 op modrm : Nat) (rest : List (BitVec 8)) :
    decF ((([0x62, p0, p1, p2, op, modrm] : List Nat).map (BitVec.ofNat 8)) ++ rest) =
      (decRm (modrm % 256) (1 - p0 % 256 / 64 % 2) (1 - p0 % 256 / 32 % 2) rest).bind fun q =>
        if hasImm (p0 % 256 % 8) (op % 256) then
          match q.2 with
          | i :: r => some (⟨p0 % 256 % 8, p1 % 256 % 4, p1 % 256 / 128, p2 % 256 % 8, op % 256,
              (1 - p0 % 256 / 16 % 2) * 16 + (1 - p0 % 256 / 128 % 2) * 8 + modrm % 256 / 8 % 8,
              (1 - p2 % 256 / 8 % 2) * 16 + (15 - p1 % 256 / 8 % 16), q.1, some i.toNat⟩, r)
          | [] => none
        else some (⟨p0 % 256 % 8, p1 % 256 % 4, p1 % 256 / 128, p2 % 256 % 8, op % 256,
              (1 - p0 % 256 / 16 % 2) * 16 + (1 - p0 % 256 / 128 % 2) * 8 + modrm % 256 / 8 % 8,
              (1 - p2 % 256 / 8 % 2) * 16 + (15 - p1 % 256 / 8 % 16), q.1, none⟩, q.2) := by
  simp [decF]

theorem evexP0_val (r x mm : Nat) : evexP0 r x mm =
    (1 - r / 8 % 2) * 128 + (1 - x / 16 % 2) * 64 + (1 - x / 8 % 2) * 32 + (1 - r / 16 % 2) * 16
      + mm % 8 := by
  simp [evexP0, land7, Nat.shiftRight_eq_div_pow]

theorem evexP1_val (w v pp : Nat) : evexP1 w v pp = w % 2 * 128 + (15 - v % 16) * 8 + 4 + pp % 4 := by
  simp [evexP1, land3, land15]

theorem evexP2_val (v aaa : Nat) : evexP2 0 2 0 v aaa = 64 + (1 - v / 16 % 2) * 8 + aaa % 8 := by
  simp [evexP2, land3, land7, Nat.shiftRight_eq_div_pow]

theorem modRMReg_val (reg rm : Nat) : modRMReg reg rm = 192 + reg % 8 * 8 + rm % 8 := by
  simp [modRMReg, land7]

/-- The bit fields of a byte with bits 7 to 4 `A`, `B`, `C`, `D` and low nibble `E`. -/
theorem byteBits (A B C D E : Nat) (hA : A < 2) (hB : B < 2) (hC : C < 2) (hD : D < 2)
    (hE : E < 16) :
    (A * 128 + B * 64 + C * 32 + D * 16 + E) % 256 / 128 % 2 = A ∧
    (A * 128 + B * 64 + C * 32 + D * 16 + E) % 256 / 64 % 2 = B ∧
    (A * 128 + B * 64 + C * 32 + D * 16 + E) % 256 / 32 % 2 = C ∧
    (A * 128 + B * 64 + C * 32 + D * 16 + E) % 256 / 16 % 2 = D ∧
    (A * 128 + B * 64 + C * 32 + D * 16 + E) % 256 % 16 = E := by
  omega

/-- The decoder on the four payload bytes and the `ModRM` byte of valid fields. -/
theorem decF_head {mm pp w aaa op reg vvvv x m : Nat} (hmm : mm < 4) (hpp : pp < 4) (hw : w < 2)
    (haaa : aaa < 8) (hop : op < 256) (hreg : reg < 32) (hv : vvvv < 32)
    (hm : m < 256) (hmr : m / 8 % 8 = reg % 8) (rest : List (BitVec 8)) :
    decF ((([0x62, evexP0 reg x mm, evexP1 w vvvv pp, evexP2 0 2 0 vvvv aaa, op, m] :
        List Nat).map (BitVec.ofNat 8)) ++ rest) =
      (decRm m (x / 16 % 2) (x / 8 % 2) rest).bind fun q =>
        if hasImm mm op then
          match q.2 with
          | i :: r => some (⟨mm, pp, w, aaa, op, reg, vvvv, q.1, some i.toNat⟩, r)
          | [] => none
        else some (⟨mm, pp, w, aaa, op, reg, vvvv, q.1, none⟩, q.2) := by
  rw [decF_cons]
  have e0 := evexP0_val reg x mm
  have e1 := evexP1_val w vvvv pp
  have e2 := evexP2_val vvvv aaa
  have h1 : 1 - evexP0 reg x mm % 256 / 64 % 2 = x / 16 % 2 := by omega
  have h2 : 1 - evexP0 reg x mm % 256 / 32 % 2 = x / 8 % 2 := by omega
  have h3 : evexP0 reg x mm % 256 % 8 = mm := by omega
  have h4 : evexP1 w vvvv pp % 256 % 4 = pp := by omega
  have h5 : evexP1 w vvvv pp % 256 / 128 = w := by omega
  have h6 : evexP2 0 2 0 vvvv aaa % 256 % 8 = aaa := by omega
  have hb := byteBits (1 - reg / 8 % 2) (1 - x / 16 % 2) (1 - x / 8 % 2) (1 - reg / 16 % 2)
    (mm % 8) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [← evexP0_val] at hb
  have a1 : evexP0 reg x mm % 256 / 16 % 2 = 1 - reg / 16 % 2 := hb.2.2.2.1
  have a2 : evexP0 reg x mm % 256 / 128 % 2 = 1 - reg / 8 % 2 := hb.1
  have h7 : (1 - evexP0 reg x mm % 256 / 16 % 2) * 16 + (1 - evexP0 reg x mm % 256 / 128 % 2) * 8
      + m % 256 / 8 % 8 = reg := by
    rw [a1, a2, Nat.mod_eq_of_lt hm]
    omega
  have h8 : (1 - evexP2 0 2 0 vvvv aaa % 256 / 8 % 2) * 16 + (15 - evexP1 w vvvv pp % 256 / 8 % 16)
      = vvvv := by omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hm]

/-- The bytes after the operand: the immediate, when the opcode has one, and the
    continuation. -/
theorem decF_tail (mm pp w aaa op reg vvvv : Nat) (rmf : RmF) (imm : Option Nat)
    (himm : ∀ i, imm = some i → i < 256) (hhas : imm.isSome = hasImm mm op)
    (r : List (BitVec 8)) :
    (some (rmf, imm.toList.map (BitVec.ofNat 8) ++ r) : Option (RmF × List (BitVec 8))).bind
      (fun q =>
        if hasImm mm op then
          match q.2 with
          | i :: r => some (EvexF.mk mm pp w aaa op reg vvvv q.1 (some i.toNat), r)
          | [] => none
        else some (EvexF.mk mm pp w aaa op reg vvvv q.1 none, q.2)) =
      some (EvexF.mk mm pp w aaa op reg vvvv rmf imm, r) := by
  cases imm with
  | none =>
    simp only [Option.isSome_none] at hhas
    simp [← hhas]
  | some i =>
    simp only [Option.isSome_some] at hhas
    have hi := himm i rfl
    simp [← hhas, Nat.mod_eq_of_lt hi]

theorem le32_bytes (d : Int) (rest : List (BitVec 8)) :
    ∃ d0 d1 d2 d3, (le32 d).map (BitVec.ofNat 8) ++ rest
      = d0 :: d1 :: d2 :: d3 :: rest ∧
      (Fits32 d → sext32 d0.toNat d1.toNat d2.toNat d3.toNat = d) := by
  refine ⟨_, _, _, _, rfl, fun hd => ?_⟩
  obtain ⟨h1, h2⟩ := hd
  simp only [sext32, BitVec.toNat_ofNat]
  split <;> omega

/-- The compressed displacement byte decodes to the displacement. -/
theorem disp8_dec {d : Int} (h : Disp8 d) :
    64 * sext8 ((le8 (d / 64)) % 256) = d := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [sext8, le8]
  split_ifs <;> omega

/-- The SIB byte and the bits `X` and `B` of a valid memory operand decode to its base and
    index. -/
theorem sib_fields (b : Nat) (idx : Option (Nat × Nat)) (d : Int) (hb : b < 16)
    (hidx : ∀ x s, idx = some (x, s) → x < 16 ∧ x ≠ 4 ∧ s < 4) :
    sibByte b idx < 256 ∧ RmF.xb (.mem (.sib b idx d)) < 32 ∧
    RmF.xb (.mem (.sib b idx d)) / 8 % 2 * 8 + sibByte b idx % 8 = b ∧
    (if RmF.xb (.mem (.sib b idx d)) / 16 % 2 * 8 + sibByte b idx / 8 % 8 = 4 then none
      else some (RmF.xb (.mem (.sib b idx d)) / 16 % 2 * 8 + sibByte b idx / 8 % 8,
        sibByte b idx / 64)) = idx := by
  cases idx with
  | none =>
    have h4 : RmF.xb (.mem (.sib b none d)) / 16 % 2 * 8 + sibByte b none / 8 % 8 = 4 := by
      simp only [sibByte, RmF.xb]; omega
    rw [ite_eq_left h4]
    simp only [sibByte, RmF.xb]
    exact ⟨by omega, by omega, by omega, trivial⟩
  | some p =>
    obtain ⟨x, s⟩ := p
    obtain ⟨hx, hx4, hs⟩ := hidx x s rfl
    have h4 : RmF.xb (.mem (.sib b (some (x, s)) d)) / 16 % 2 * 8
        + sibByte b (some (x, s)) / 8 % 8 = x := by
      simp only [sibByte, RmF.xb]; omega
    have h5 : sibByte b (some (x, s)) / 64 = s := by simp only [sibByte]; omega
    rw [h4, ite_eq_right hx4, h5]
    simp only [sibByte, RmF.xb]
    exact ⟨by omega, by omega, by omega, trivial⟩

/-- **The decoder inverts the encoder** on valid fields. -/
theorem decF_encF {f : EvexF} (hf : f.Valid) (r : List (BitVec 8)) :
    decF (encF f ++ r) = some (f, r) := by
  obtain ⟨mm, pp, w, aaa, op, reg, vvvv, rm, imm⟩ := f
  obtain ⟨hmm, hpp, hw, haaa, hop, hreg, hv, hrm, himm, hhas⟩ := hf
  simp only at hmm hpp hw haaa hop hreg hv hrm himm hhas
  cases rm with
  | reg x =>
    simp only [RmF.Valid] at hrm
    have hm := modRMReg_val reg x
    have e : encF ⟨mm, pp, w, aaa, op, reg, vvvv, .reg x, imm⟩ ++ r =
        (([0x62, evexP0 reg x mm, evexP1 w vvvv pp, evexP2 0 2 0 vvvv aaa, op,
          modRMReg reg x] : List Nat).map (BitVec.ofNat 8)) ++
          (imm.toList.map (BitVec.ofNat 8) ++ r) := by
      simp [encF, rmBytes, RmF.xb]
    rw [e, decF_head (x := x) (m := modRMReg reg x) hmm hpp hw haaa hop hreg hv (by omega)
      (by omega),
      decRm_reg _ _ _ _ (by omega)]
    have hx : x / 16 % 2 * 16 + x / 8 % 2 * 8 + modRMReg reg x % 8 = x := by omega
    rw [hx]
    exact decF_tail _ _ _ _ _ _ _ _ _ himm hhas r
  | mem mf =>
    cases mf with
    | abs a =>
      simp only [RmF.Valid] at hrm
      obtain ⟨d0, d1, d2, d3, hd, hs⟩ := le32_bytes a (imm.toList.map (BitVec.ofNat 8) ++ r)
      have e : encF ⟨mm, pp, w, aaa, op, reg, vvvv, .mem (.abs a), imm⟩ ++ r =
          (([0x62, evexP0 reg 0 mm, evexP1 w vvvv pp, evexP2 0 2 0 vvvv aaa, op,
            reg % 8 * 8 + 4] : List Nat).map (BitVec.ofNat 8)) ++
            (BitVec.ofNat 8 0x25 :: (d0 :: d1 :: d2 :: d3 ::
              (imm.toList.map (BitVec.ofNat 8) ++ r))) := by
        rw [← hd]
        simp [encF, rmBytes, RmF.xb]
      rw [e, decF_head (x := 0) (m := reg % 8 * 8 + 4) hmm hpp hw haaa hop hreg hv
        (by omega) (by omega)]
      have hdr : decRm (reg % 8 * 8 + 4) (0 / 16 % 2) (0 / 8 % 2)
          (BitVec.ofNat 8 0x25 :: d0 :: d1 :: d2 :: d3 :: (imm.toList.map (BitVec.ofNat 8) ++ r))
          = some (.mem (.abs a), imm.toList.map (BitVec.ofNat 8) ++ r) := by
        simp only [decRm]
        rw [ite_eq_right (by omega)]
        simp only [BitVec.toNat_ofNat]
        rw [ite_eq_left (show (reg % 8 * 8 + 4) / 64 = 0 by omega), ite_eq_left trivial, hs hrm]
      rw [hdr]
      exact decF_tail _ _ _ _ _ _ _ _ _ himm hhas r
    | sib b idx d =>
      obtain ⟨hb, hidx, hd⟩ := hrm
      obtain ⟨hs256, -, hbase, hix⟩ := sib_fields b idx d hb hidx
      by_cases h0 : d = 0 ∧ b % 8 ≠ 5
      · have e : encF ⟨mm, pp, w, aaa, op, reg, vvvv, .mem (.sib b idx d), imm⟩ ++ r =
            (([0x62, evexP0 reg (RmF.xb (.mem (.sib b idx d))) mm, evexP1 w vvvv pp,
              evexP2 0 2 0 vvvv aaa, op, reg % 8 * 8 + 4] : List Nat).map (BitVec.ofNat 8)) ++
              (BitVec.ofNat 8 (sibByte b idx) :: (imm.toList.map (BitVec.ofNat 8) ++ r)) := by
          simp [encF, rmBytes, h0]
        rw [e, decF_head (x := RmF.xb (.mem (.sib b idx d))) (m := reg % 8 * 8 + 4) hmm hpp hw
          haaa hop hreg hv (by omega) (by omega)]
        have hdr : decRm (reg % 8 * 8 + 4) (RmF.xb (.mem (.sib b idx d)) / 16 % 2)
            (RmF.xb (.mem (.sib b idx d)) / 8 % 2)
            (BitVec.ofNat 8 (sibByte b idx) :: (imm.toList.map (BitVec.ofNat 8) ++ r))
            = some (.mem (.sib b idx d), imm.toList.map (BitVec.ofNat 8) ++ r) := by
          simp only [decRm, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt hs256]
          rw [ite_eq_right (by omega), ite_eq_left (show (reg % 8 * 8 + 4) / 64 = 0 by omega),
            ite_eq_right (by omega), hbase, hix, h0.1]
        rw [hdr]
        exact decF_tail _ _ _ _ _ _ _ _ _ himm hhas r
      · by_cases h8 : Disp8 d
        · have e : encF ⟨mm, pp, w, aaa, op, reg, vvvv, .mem (.sib b idx d), imm⟩ ++ r =
              (([0x62, evexP0 reg (RmF.xb (.mem (.sib b idx d))) mm, evexP1 w vvvv pp,
                evexP2 0 2 0 vvvv aaa, op, 64 + reg % 8 * 8 + 4] : List Nat).map
                  (BitVec.ofNat 8)) ++
                (BitVec.ofNat 8 (sibByte b idx) :: BitVec.ofNat 8 (le8 (d / 64)) ::
                  (imm.toList.map (BitVec.ofNat 8) ++ r)) := by
            simp [encF, rmBytes, h0, h8]
          rw [e, decF_head (x := RmF.xb (.mem (.sib b idx d))) (m := 64 + reg % 8 * 8 + 4) hmm hpp
            hw haaa hop hreg hv (by omega) (by omega)]
          have hdr : decRm (64 + reg % 8 * 8 + 4) (RmF.xb (.mem (.sib b idx d)) / 16 % 2)
              (RmF.xb (.mem (.sib b idx d)) / 8 % 2)
              (BitVec.ofNat 8 (sibByte b idx) :: BitVec.ofNat 8 (le8 (d / 64)) ::
                (imm.toList.map (BitVec.ofNat 8) ++ r))
              = some (.mem (.sib b idx d), imm.toList.map (BitVec.ofNat 8) ++ r) := by
            simp only [decRm, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt hs256]
            rw [ite_eq_right (by omega), ite_eq_right (show ¬ (64 + reg % 8 * 8 + 4) / 64 = 0 by omega),
              ite_eq_left (show (64 + reg % 8 * 8 + 4) / 64 = 1 by omega), hbase, hix, disp8_dec h8]
          rw [hdr]
          exact decF_tail _ _ _ _ _ _ _ _ _ himm hhas r
        · obtain ⟨d0, d1, d2, d3, hdl, hs⟩ := le32_bytes d (imm.toList.map (BitVec.ofNat 8) ++ r)
          have e : encF ⟨mm, pp, w, aaa, op, reg, vvvv, .mem (.sib b idx d), imm⟩ ++ r =
              (([0x62, evexP0 reg (RmF.xb (.mem (.sib b idx d))) mm, evexP1 w vvvv pp,
                evexP2 0 2 0 vvvv aaa, op, 128 + reg % 8 * 8 + 4] : List Nat).map
                  (BitVec.ofNat 8)) ++
                (BitVec.ofNat 8 (sibByte b idx) :: d0 :: d1 :: d2 :: d3 ::
                  (imm.toList.map (BitVec.ofNat 8) ++ r)) := by
            rw [← hdl]
            simp [encF, rmBytes, h0, h8]
          rw [e, decF_head (x := RmF.xb (.mem (.sib b idx d))) (m := 128 + reg % 8 * 8 + 4) hmm
            hpp hw haaa hop hreg hv (by omega) (by omega)]
          have hdr : decRm (128 + reg % 8 * 8 + 4) (RmF.xb (.mem (.sib b idx d)) / 16 % 2)
              (RmF.xb (.mem (.sib b idx d)) / 8 % 2)
              (BitVec.ofNat 8 (sibByte b idx) :: d0 :: d1 :: d2 :: d3 ::
                (imm.toList.map (BitVec.ofNat 8) ++ r))
              = some (.mem (.sib b idx d), imm.toList.map (BitVec.ofNat 8) ++ r) := by
            simp only [decRm, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt hs256]
            rw [ite_eq_right (by omega), ite_eq_right (show ¬ (128 + reg % 8 * 8 + 4) / 64 = 0 by omega),
              ite_eq_right (show ¬ (128 + reg % 8 * 8 + 4) / 64 = 1 by omega), hbase, hix, hs hd]
          rw [hdr]
          exact decF_tail _ _ _ _ _ _ _ _ _ himm hhas r

/-- An encoding of valid fields begins with `0x62`. -/
theorem encF_head (f : EvexF) : ∃ t, encF f = evexEscape :: t := ⟨_, rfl⟩

/-! ## 4. The read-only data and the operand tables -/

/-- **The constant pool**: the absolute address of each read-only vector it holds, and the
    vector at an address. Every address fits a sign-extended 32-bit displacement. -/
structure Pool where
  /-- The address of a read-only vector. -/
  addr : BitVec 512 → Option Int
  /-- The read-only vector at an address. -/
  val : Int → Option (BitVec 512)
  /-- The vector at the address of `x` is `x`. -/
  val_addr : ∀ x a, addr x = some a → val a = some x
  /-- Every address fits a sign-extended 32-bit displacement. -/
  addr_fits : ∀ x a, addr x = some a → Fits32 a

/-- The opcode map, opcode byte and `EVEX.W` of the lane-wise operation `o` at lane width
    `L` (Intel SDM Vol. 2: `vpaddq` `EVEX.66.0F.W1 D4`, `vpaddd` `EVEX.66.0F.W0 FE`, `vpsubq`
    `W1 FB`, `vpsubd` `W0 FA`, `vpmullq`/`vpmulld` `EVEX.66.0F38 40` with `W1`/`W0`,
    `vpmuludq` `EVEX.66.0F.W1 F4`, `vpandq`/`vpandd` `DB`, `vporq`/`vpord` `EB`,
    `vpxorq`/`vpxord` `EF`, `vpandnq`/`vpandnd` `DF`, `vpsllvq`/`vpsllvd` `EVEX.66.0F38 47`,
    `vpsrlvq`/`vpsrlvd` `EVEX.66.0F38 45`, `vpminuq`/`vpminud` `EVEX.66.0F38 3B`). These are the
    mnemonics `ZmmTextValidate` reads for the operations. -/
def opTab : Nat → LOp → Option (Nat × Nat × Nat)
  | 64, .bin .add => some (1, 0xd4, 1)
  | 32, .bin .add => some (1, 0xfe, 0)
  | 64, .bin .sub => some (1, 0xfb, 1)
  | 32, .bin .sub => some (1, 0xfa, 0)
  | 64, .bin .mul => some (2, 0x40, 1)
  | 32, .bin .mul => some (2, 0x40, 0)
  | 64, .muludq => some (1, 0xf4, 1)
  | 64, .bin .and => some (1, 0xdb, 1)
  | 32, .bin .and => some (1, 0xdb, 0)
  | 64, .bin .or => some (1, 0xeb, 1)
  | 32, .bin .or => some (1, 0xeb, 0)
  | 64, .bin .xor => some (1, 0xef, 1)
  | 32, .bin .xor => some (1, 0xef, 0)
  | 64, .bin .andn => some (1, 0xdf, 1)
  | 32, .bin .andn => some (1, 0xdf, 0)
  | 64, .bin .shl => some (2, 0x47, 1)
  | 32, .bin .shl => some (2, 0x47, 0)
  | 64, .bin .shr => some (2, 0x45, 1)
  | 32, .bin .shr => some (2, 0x45, 0)
  | 64, .minu => some (2, 0x3b, 1)
  | 32, .minu => some (2, 0x3b, 0)
  | _, _ => none

/-- The lane width and operation of an opcode map, opcode byte and `EVEX.W`: the inverse of
    `opTab`. -/
def opInv : Nat → Nat → Nat → Option (Nat × LOp)
  | 1, 0xd4, 1 => some (64, .bin .add)
  | 1, 0xfe, 0 => some (32, .bin .add)
  | 1, 0xfb, 1 => some (64, .bin .sub)
  | 1, 0xfa, 0 => some (32, .bin .sub)
  | 2, 0x40, 1 => some (64, .bin .mul)
  | 2, 0x40, 0 => some (32, .bin .mul)
  | 1, 0xf4, 1 => some (64, .muludq)
  | 1, 0xdb, 1 => some (64, .bin .and)
  | 1, 0xdb, 0 => some (32, .bin .and)
  | 1, 0xeb, 1 => some (64, .bin .or)
  | 1, 0xeb, 0 => some (32, .bin .or)
  | 1, 0xef, 1 => some (64, .bin .xor)
  | 1, 0xef, 0 => some (32, .bin .xor)
  | 1, 0xdf, 1 => some (64, .bin .andn)
  | 1, 0xdf, 0 => some (32, .bin .andn)
  | 2, 0x47, 1 => some (64, .bin .shl)
  | 2, 0x47, 0 => some (32, .bin .shl)
  | 2, 0x45, 1 => some (64, .bin .shr)
  | 2, 0x45, 0 => some (32, .bin .shr)
  | 2, 0x3b, 1 => some (64, .minu)
  | 2, 0x3b, 0 => some (32, .minu)
  | _, _, _ => none

theorem opInv_opTab {L : Nat} {o : LOp} {k : Nat × Nat × Nat} (h : opTab L o = some k) :
    opInv k.1 k.2.1 k.2.2 = some (L, o) ∧ (k.1 = 1 ∨ k.1 = 2) ∧ k.2.1 < 256 ∧ k.2.2 < 2 ∧
      k.2.1 ≠ 0x6f ∧ k.2.1 ≠ 0x7f ∧ k.2.1 ≠ 0x72 ∧ k.2.1 ≠ 0x73 ∧ k.2.1 ≠ 0x36 ∧
      k.2.1 ≠ 0x64 ∧ k.2.1 ≠ 0x16 ∧ k.2.1 ≠ 0x12 := by
  unfold opTab at h
  split at h <;> first | (cases h; decide) | simp at h

/-- The `EVEX.W` bit of the lane width of a shift, rotate or ternary logic instruction. -/
def wTab : Nat → Option Nat
  | 64 => some 1
  | 32 => some 0
  | _ => none

theorem wTab_spec {L w : Nat} (h : wTab L = some w) : w < 2 ∧ L = (if w = 1 then 64 else 32) := by
  unfold wTab at h
  split at h <;> first | (cases h; decide) | simp at h

/-- The scale code of an index scale. -/
def scaleCode : Nat → Option Nat
  | 1 => some 0
  | 2 => some 1
  | 4 => some 2
  | 8 => some 3
  | _ => none

theorem scaleCode_spec {sc s : Nat} (h : scaleCode sc = some s) : s < 4 ∧ 2 ^ s = sc := by
  unfold scaleCode at h
  split at h <;> first | (cases h; decide) | simp at h

theorem gpNum?_spec {r : String} {n : Nat} (h : gpNum? r = some n) : n < 16 ∧ regName n = r := by
  unfold gpNum? at h
  split at h <;> simp_all <;> subst h <;> decide

/-- The memory operand of an address: the base and index names are 64-bit registers, the
    index is not `%rsp`, the scale is 1, 2, 4 or 8 and the displacement fits 32 bits. -/
def memF (a : VAddr) : Option MemF :=
  (gpNum? a.base).bind fun b =>
    (match a.idx with
      | none => some none
      | some (x, sc) =>
          (gpNum? x).bind fun xn =>
            if xn = 4 then none else (scaleCode sc).map fun s => some (xn, s)).bind fun idx =>
      if Fits32 a.disp then some (.sib b idx a.disp) else none

/-- The address of a memory operand. -/
def memInv : MemF → Option VAddr
  | .sib b idx d => some ⟨regName b, idx.map fun p => (regName p.1, 2 ^ p.2), d⟩
  | .abs _ => none

theorem memF_spec {a : VAddr} {m : MemF} (h : memF a = some m) :
    memInv m = some a ∧ RmF.Valid (.mem m) ∧ ∃ b idx d, m = .sib b idx d := by
  obtain ⟨base, idx, disp⟩ := a
  simp only [memF, Option.bind_eq_some_iff] at h
  obtain ⟨b, hb, ix, hix, hm⟩ := h
  split at hm
  · rename_i hfit
    simp only [Option.some.injEq] at hm
    subst hm
    obtain ⟨hb16, hbn⟩ := gpNum?_spec hb
    cases idx with
    | none =>
      simp only [Option.some.injEq] at hix
      subst hix
      refine ⟨by simp [memInv, hbn], ⟨hb16, by simp, hfit⟩, _, _, _, rfl⟩
    | some p =>
      obtain ⟨x, sc⟩ := p
      simp only [Option.bind_eq_some_iff] at hix
      obtain ⟨xn, hxn, hix⟩ := hix
      split at hix
      · simp at hix
      · rename_i hx4
        simp only [Option.map_eq_some_iff] at hix
        obtain ⟨s, hs, rfl⟩ := hix
        obtain ⟨hx16, hxn'⟩ := gpNum?_spec hxn
        obtain ⟨hs4, hsc⟩ := scaleCode_spec hs
        refine ⟨by simp [memInv, hbn, hxn', hsc], ⟨hb16, ?_, hfit⟩, _, _, _, rfl⟩
        intro x' s' he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hx16, hx4, hs4⟩
  · simp at hm

/-! ## 5. The fields of a vector instruction -/

/-- The register `n` when it is below 32. -/
def fin32 (n : Nat) : Option (Fin 32) := if h : n < 32 then some ⟨n, h⟩ else none

/-- The mask register `n` when it is below 8. -/
def fin8 (n : Nat) : Option (Fin 8) := if h : n < 8 then some ⟨n, h⟩ else none

@[simp] theorem fin32_val (r : Fin 32) : fin32 r.val = some r := by simp [fin32, r.isLt]

@[simp] theorem fin8_val (k : Fin 8) : fin8 k.val = some k := by simp [fin8, k.isLt]

/-- The `aaa` field of a merge mask: `0` for no mask, none for `%k0`, which encodes no
    mask. -/
def maskF : Option (Fin 8) → Option Nat
  | none => some 0
  | some k => if k.val = 0 then none else some k.val

theorem maskF_spec {mask : Option (Fin 8)} {aaa : Nat} (h : maskF mask = some aaa) :
    aaa < 8 ∧ (if aaa = 0 then some none else (fin8 aaa).map some) = some mask := by
  cases mask with
  | none => simp only [maskF, Option.some.injEq] at h; subst h; simp
  | some k =>
    simp only [maskF] at h
    split at h
    · cases h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      simp [hk, k.isLt]

/-- **The EVEX fields of a vector instruction** at vector length 512, none for an
    instruction without an EVEX encoding. The register operands of the AT&T line
    `mnem src2, src1, dst` are `ModRM.rm`, `vvvv` and `ModRM.reg`; a shift or rotate by an
    immediate puts its destination in `vvvv` and its opcode extension in `ModRM.reg`
    (Intel SDM Vol. 2: `vpsllq`/`vpsrlq` `EVEX.66.0F.W1 73 /6 ib` and `/2 ib`,
    `vpslld`/`vpsrld` `EVEX.66.0F.W0 72 /6 ib` and `/2 ib`, `vprolq`/`vprold`
    `EVEX.66.0F 72 /1 ib` with `W1`/`W0`); `vmovdqu64` is `EVEX.F3.0F.W1 6F /r` (load) and
    `7F /r` (store), `vmovdqa64` is `EVEX.66.0F.W1 6F /r`, `vmovshdup`/`vmovsldup` are
    `EVEX.F3.0F.W0 16 /r` and `12 /r` with the merge mask in `aaa`, `vpermd` is
    `EVEX.66.0F38.W0 36 /r`, `vpblendmd` is `EVEX.66.0F38.W0 64 /r` with its mask in `aaa`,
    and `vpternlogq`/`vpternlogd` are `EVEX.66.0F3A 25 /r ib` with `W1`/`W0`. -/
def toF (P : Pool) : VInstr → Option EvexF
  | .ld a d => (memF a).map fun m => ⟨1, 2, 1, 0, 0x6f, d.val, 0, .mem m, none⟩
  | .st s a => (memF a).map fun m => ⟨1, 2, 1, 0, 0x7f, s.val, 0, .mem m, none⟩
  | .op L o s2 s1 d =>
      (opTab L o).map fun k => ⟨k.1, 1, k.2.2, 0, k.2.1, d.val, s1.val, .reg s2.val, none⟩
  | .shi L left imm s d =>
      if imm < 256 then
        (wTab L).map fun w => ⟨1, 1, w, 0, if w = 1 then 0x73 else 0x72, if left then 6 else 2,
          d.val, .reg s.val, some imm⟩
      else none
  | .dup odd s d mask =>
      (maskF mask).map fun aaa =>
        ⟨1, 2, 0, aaa, if odd then 0x16 else 0x12, d.val, 0, .reg s.val, none⟩
  | .mova s d => some ⟨1, 1, 1, 0, 0x6f, d.val, 0, .reg s.val, none⟩
  | .perm x i d => some ⟨2, 1, 0, 0, 0x36, d.val, i.val, .reg x.val, none⟩
  | .blend k a b d =>
      if k.val = 0 then none else some ⟨2, 1, 0, k.val, 0x64, d.val, b.val, .reg a.val, none⟩
  | .rol L imm s d =>
      if imm < 256 then
        (wTab L).map fun w => ⟨1, 1, w, 0, 0x72, 1, d.val, .reg s.val, some imm⟩
      else none
  | .tern L imm s3 s2 d =>
      (wTab L).map fun w => ⟨3, 1, w, 0, 0x25, d.val, s2.val, .reg s3.val, some imm.toNat⟩
  | .ldK x d => (P.addr x).map fun a => ⟨1, 2, 1, 0, 0x6f, d.val, 0, .mem (.abs a), none⟩
  | .opK L o x s1 d =>
      (opTab L o).bind fun k => (P.addr x).map fun a =>
        ⟨k.1, 1, k.2.2, 0, k.2.1, d.val, s1.val, .mem (.abs a), none⟩
  | .kmov _ => none
  | .zeroUpper => none

/-- The vector instruction of EVEX fields: the inverse of `toF`. -/
def ofF (P : Pool) (f : EvexF) : Option VInstr :=
  match f.rm, f.imm with
  | .reg r, none =>
      if f.pp = 1 ∧ f.mm = 1 ∧ f.op = 0x6f then
        (fin32 r).bind fun s => (fin32 f.reg).map fun d => .mova s d
      else if f.pp = 1 ∧ f.mm = 2 ∧ f.op = 0x36 then
        (fin32 r).bind fun s => (fin32 f.vvvv).bind fun i => (fin32 f.reg).map fun d =>
          .perm s i d
      else if f.pp = 1 ∧ f.mm = 2 ∧ f.op = 0x64 then
        (fin8 f.aaa).bind fun k => (fin32 r).bind fun a => (fin32 f.vvvv).bind fun b =>
          (fin32 f.reg).map fun d => .blend k a b d
      else if f.pp = 2 then
        (fin32 r).bind fun s => (fin32 f.reg).bind fun d =>
          (if f.aaa = 0 then some none else (fin8 f.aaa).map some).map fun mask =>
            .dup (decide (f.op = 0x16)) s d mask
      else
        (opInv f.mm f.op f.w).bind fun lo => (fin32 r).bind fun s2 =>
          (fin32 f.vvvv).bind fun s1 => (fin32 f.reg).map fun d => .op lo.1 lo.2 s2 s1 d
  | .reg r, some i =>
      if f.mm = 3 then
        (fin32 r).bind fun s3 => (fin32 f.vvvv).bind fun s2 => (fin32 f.reg).map fun d =>
          .tern (if f.w = 1 then 64 else 32) (BitVec.ofNat 8 i) s3 s2 d
      else if f.op = 0x72 ∧ f.reg = 1 then
        (fin32 r).bind fun s => (fin32 f.vvvv).map fun d =>
          .rol (if f.w = 1 then 64 else 32) i s d
      else
        (fin32 r).bind fun s => (fin32 f.vvvv).map fun d =>
          .shi (if f.w = 1 then 64 else 32) (decide (f.reg = 6)) i s d
  | .mem (.abs a), none =>
      if f.pp = 2 then
        (P.val a).bind fun x => (fin32 f.reg).map fun d => .ldK x d
      else
        (opInv f.mm f.op f.w).bind fun lo => (P.val a).bind fun x =>
          (fin32 f.vvvv).bind fun s1 => (fin32 f.reg).map fun d => .opK lo.1 lo.2 x s1 d
  | .mem m, none =>
      if f.op = 0x6f then
        (memInv m).bind fun a => (fin32 f.reg).map fun d => .ld a d
      else
        (memInv m).bind fun a => (fin32 f.reg).map fun s => .st s a
  | .mem _, some _ => none

/-- **The instruction is read back from its fields.** -/
theorem ofF_toF (P : Pool) {v : VInstr} {f : EvexF} (h : toF P v = some f) :
    ofF P f = some v := by
  cases v with
  | ld a d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    obtain ⟨hinv, -, b, idx, dd, rfl⟩ := memF_spec hm
    simp [ofF, hinv]
  | st s a =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    obtain ⟨hinv, -, b, idx, dd, rfl⟩ := memF_spec hm
    simp [ofF, hinv]
  | op L o s2 s1 d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hinv, hmm, -, -, h6f, -, -, -, h36, h64, -, -⟩ := opInv_opTab hk
    rcases hmm with hmm | hmm <;> rw [hmm] at hinv <;> simp [ofF, hinv, hmm, h6f, h36, h64]
  | shi L left imm s d =>
    simp only [toF] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      obtain ⟨hw2, rfl⟩ := wTab_spec hw
      cases left <;> (rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl) <;> simp [ofF]
    · cases h
  | dup odd s d mask =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨aaa, ha, rfl⟩ := h
    obtain ⟨-, hm⟩ := maskF_spec ha
    cases odd <;> simp [ofF, hm]
  | mova s d => simp only [toF, Option.some.injEq] at h; subst h; simp [ofF]
  | perm x i d => simp only [toF, Option.some.injEq] at h; subst h; simp [ofF]
  | blend k a b d =>
    simp only [toF] at h
    split at h
    · cases h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      simp [ofF]
  | rol L imm s d =>
    simp only [toF] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      obtain ⟨hw2, rfl⟩ := wTab_spec hw
      simp [ofF]
    · cases h
  | tern L imm s3 s2 d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    obtain ⟨hw2, rfl⟩ := wTab_spec hw
    simp [ofF]
  | ldK x d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [ofF, P.val_addr x a ha]
  | opK L o x s1 d =>
    simp only [toF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, a, ha, rfl⟩ := h
    obtain ⟨hinv, -, -, -, -, -, -, -, -, -, -, -⟩ := opInv_opTab hk
    simp [ofF, hinv, P.val_addr x a ha]
  | kmov k => simp [toF] at h
  | zeroUpper => simp [toF] at h

/-- **The fields of a vector instruction are valid.** -/
theorem toF_valid (P : Pool) {v : VInstr} {f : EvexF} (h : toF P v = some f) : f.Valid := by
  cases v with
  | ld a d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    obtain ⟨-, hv, -⟩ := memF_spec hm
    exact ⟨by simp, by simp, by simp, by simp, by simp, d.isLt, by simp, hv,
      by simp, rfl⟩
  | st s a =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    obtain ⟨-, hv, -⟩ := memF_spec hm
    exact ⟨by simp, by simp, by simp, by simp, by simp, s.isLt, by simp, hv,
      by simp, rfl⟩
  | op L o s2 s1 d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨-, hmm, hop, hw, -, -, h72, h73, -⟩ := opInv_opTab hk
    refine ⟨by dsimp only; omega, by simp, hw, by simp, hop, d.isLt, s1.isLt, s2.isLt, by simp,
      ?_⟩
    rcases hmm with hmm | hmm <;> simp [hasImm, hmm, h72, h73]
  | shi L left imm s d =>
    simp only [toF] at h
    split at h
    · rename_i himm
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      obtain ⟨hw2, -⟩ := wTab_spec hw
      refine ⟨by simp, by simp, hw2, by simp, by dsimp only; split <;> simp, by dsimp only; split <;> simp,
        d.isLt, s.isLt, by simpa using himm, ?_⟩
      split <;> rfl
    · cases h
  | dup odd s d mask =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨aaa, ha, rfl⟩ := h
    have h8 : aaa < 8 := (maskF_spec ha).1
    refine ⟨by simp, by simp, by simp, h8, by dsimp only; split <;> simp, d.isLt, by simp,
      s.isLt, by simp, ?_⟩
    split <;> rfl
  | mova s d =>
    simp only [toF, Option.some.injEq] at h; subst h
    exact ⟨by simp, by simp, by simp, by simp, by simp, d.isLt, by simp, s.isLt,
      by simp, rfl⟩
  | perm x i d =>
    simp only [toF, Option.some.injEq] at h; subst h
    exact ⟨by simp, by simp, by simp, by simp, by simp, d.isLt, i.isLt, x.isLt,
      by simp, rfl⟩
  | blend k a b d =>
    simp only [toF] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨by simp, by simp, by simp, k.isLt, by simp, d.isLt, b.isLt, a.isLt,
        by simp, rfl⟩
  | rol L imm s d =>
    simp only [toF] at h
    split at h
    · rename_i himm
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      obtain ⟨hw2, -⟩ := wTab_spec hw
      exact ⟨by simp, by simp, hw2, by simp, by simp, by simp, d.isLt, s.isLt,
        by simpa using himm, rfl⟩
    · cases h
  | tern L imm s3 s2 d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    obtain ⟨hw2, -⟩ := wTab_spec hw
    exact ⟨by simp, by simp, hw2, by simp, by simp, d.isLt, s2.isLt, s3.isLt,
      by simpa using imm.isLt, rfl⟩
  | ldK x d =>
    simp only [toF, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact ⟨by simp, by simp, by simp, by simp, by simp, d.isLt, by simp,
      P.addr_fits x a ha, by simp, rfl⟩
  | opK L o x s1 d =>
    simp only [toF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, a, ha, rfl⟩ := h
    obtain ⟨-, hmm, hop, hw, -, -, h72, h73, -⟩ := opInv_opTab hk
    refine ⟨by dsimp only; omega, by simp, hw, by simp, hop, d.isLt, s1.isLt, P.addr_fits x a ha,
      by simp, ?_⟩
    rcases hmm with hmm | hmm <;> simp [hasImm, hmm, h72, h73]
  | kmov k => simp [toF] at h
  | zeroUpper => simp [toF] at h

/-! ## 6. The table -/

/-- The bytes of `vzeroupper`, `VEX.128.0F.WIG 77` (Intel SDM Vol. 2). -/
def vzeroupperBytes : List (BitVec 8) := ymmBytes [0xc5, 0xf8, 0x77]

/-- The bytes of `kmovw %eax, %kN`, `VEX.L0.0F.W0 92 /r` with `ModRM.reg = N` and
    `ModRM.rm = eax` (Intel SDM Vol. 2). -/
def kmovwBytes (k : Fin 8) : List (BitVec 8) := ymmBytes [0xc5, 0xf8, 0x92, 0xc0 + 8 * k.val]

/-- **The encoding of a vector instruction** at vector length 512: the two VEX
    instructions, and the EVEX instruction of the fields `toF` for every other. -/
def zmmEnc (P : Pool) (v : VInstr) : Option (List (BitVec 8)) :=
  match v with
  | .zeroUpper => some vzeroupperBytes
  | .kmov k => some (kmovwBytes k)
  | v => (toF P v).map encF

/-- **The x86 encoding table of the vector instructions in `%zmm` mode**, with the
    read-only vectors at the addresses of the pool `P`. Each entry is one instruction of
    the instruction set, and its Intel SDM semantics on 512-bit registers is `VecMach.vexec`
    in `Mode.zmm` on a state whose memory holds each vector of `P` at its address (a load of
    a read-only vector reads it there). `VecImage.VecAsm.Faithful (zmmAsm P) r .zmm cpu` is
    therefore the hypothesis that the processor implements these instructions, for a
    relation `cpu` whose states hold the pool. -/
def zmmAsm (P : Pool) : VecAsm := ⟨zmmEnc P⟩

/-- An entry is a VEX instruction or the EVEX instruction of valid fields. -/
theorem zmmEnc_cases (P : Pool) {v : VInstr} {bs : List (BitVec 8)}
    (h : zmmEnc P v = some bs) :
    (v = .zeroUpper ∧ bs = vzeroupperBytes) ∨ (∃ k, v = .kmov k ∧ bs = kmovwBytes k) ∨
      (∃ f, toF P v = some f ∧ bs = encF f) := by
  cases v with
  | zeroUpper => simp only [zmmEnc, Option.some.injEq] at h; exact .inl ⟨rfl, h.symm⟩
  | kmov k => simp only [zmmEnc, Option.some.injEq] at h; exact .inr (.inl ⟨k, rfl, h.symm⟩)
  | _ =>
    simp only [zmmEnc, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, rfl⟩ := h
    exact .inr (.inr ⟨f, hf, rfl⟩)

theorem kmovwBytes_inj {k k' : Fin 8} (h : kmovwBytes k = kmovwBytes k') : k = k' := by
  simp only [kmovwBytes, ymmBytes, List.map_cons, List.map_nil, List.cons.injEq,
    true_and, and_true] at h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  exact Fin.ext (by omega)

/-- **The table is lawful**: every entry begins with `0x62` or `0xC5`, and no entry is a
    proper prefix of another. -/
theorem zmmAsm_lawful (P : Pool) : (zmmAsm P).Lawful where
  escape v bs h := by
    rcases zmmEnc_cases P h with ⟨-, rfl⟩ | ⟨k, -, rfl⟩ | ⟨f, -, rfl⟩
    · exact ⟨_, .inr rfl⟩
    · exact ⟨_, .inr rfl⟩
    · exact ⟨_, .inl rfl⟩
  prefixFree v w bv bw hv hw hp := by
    obtain ⟨s, hs⟩ := hp
    rcases zmmEnc_cases P hv with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨f, hf, rfl⟩ <;>
      rcases zmmEnc_cases P hw with ⟨rfl, rfl⟩ | ⟨k', rfl, rfl⟩ | ⟨g, hg, rfl⟩
    · rfl
    · simp [vzeroupperBytes, kmovwBytes, ymmBytes] at hs
    · obtain ⟨t, ht⟩ := encF_head g
      rw [ht] at hs
      simp [vzeroupperBytes, ymmBytes, evexEscape] at hs
    · have := congrArg List.length hs
      simp [vzeroupperBytes, kmovwBytes, ymmBytes] at this
    · have hl := congrArg List.length hs
      simp only [kmovwBytes, ymmBytes, List.length_append, List.length_map,
        List.length_cons, List.length_nil] at hl
      have hs0 : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hs0
      rw [List.append_nil] at hs
      rw [kmovwBytes_inj hs]
    · obtain ⟨t, ht⟩ := encF_head g
      rw [ht] at hs
      simp [kmovwBytes, ymmBytes, evexEscape] at hs
    · obtain ⟨t, ht⟩ := encF_head f
      rw [ht] at hs
      simp [vzeroupperBytes, ymmBytes, evexEscape] at hs
    · obtain ⟨t, ht⟩ := encF_head f
      rw [ht] at hs
      simp [kmovwBytes, ymmBytes, evexEscape] at hs
    · have h1 := decF_encF (toF_valid P hf) s
      have h2 := decF_encF (toF_valid P hg) []
      rw [List.append_nil, ← hs, h1] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      have := (ofF_toF P hf).symm.trans (ofF_toF P hg)
      simpa using this

/-! ## 7. Evidence -/

/-- **On the 64-bit lane-wise operations the table is `ZmmByteEncoder.encodeZmmPackInst`**,
    whose bytes are pinned against GNU as 2.42 by `encodeZmmPack_map0F_eq_gas` and
    `encodeZmmPack_map0F38_eq_gas`. -/
theorem zmmEnc_op64_eq_pack (P : Pool) (b : JasminBinOp) (s2 s1 d : Fin 32) :
    zmmEnc P (.op 64 (.bin b) s2 s1 d) = some (encodeZmmPackInst b d.val s1.val s2.val) := by
  have hok : zmmRegsOk d.val s1.val s2.val = true := by
    simp [zmmRegsOk, d.isLt, s1.isLt, s2.isLt]
  cases b <;> simp [zmmEnc, toF, opTab, encF, rmBytes, RmF.xb, encodeZmmPackInst, hok,
    encEvex512W1, encEvexRR, zmmPackOpcode]

/-- `vzeroupper` and `kmovw %eax, %k1` against their SDM encodings: `C5 F8 77` and
    `C5 F8 92 C8`. -/
theorem zmmEnc_vex_eq (P : Pool) :
    zmmEnc P .zeroUpper = some (ymmBytes [0xc5, 0xf8, 0x77]) ∧
    zmmEnc P (.kmov 1) = some (ymmBytes [0xc5, 0xf8, 0x92, 0xc8]) := by
  constructor <;> rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecAsmZmm
