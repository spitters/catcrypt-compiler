/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import Mathlib.Tactic.IntervalCases

/-!
# x86-64 instruction-byte field extraction (the Sail-x86 decode discipline)

The REX-prefix and ModRM field splits an x86 decoder applies to an instruction
byte stream, and their behaviour on the bytes `ScalarEncoder` emits.

These transcribe the field splits of the Sail-x86 model
([`rems-project/sail-x86-from-acl2`](https://github.com/rems-project/sail-x86-from-acl2),
`model/prefix_modrm_sib_decoding.sail`): the REX prefix (`prefixes` bitfield and
the SDM `0x40 | W<<3 | R<<2 | X<<1 | B` layout, Intel SDM Vol. 2 §2.2.1), the
ModRM byte (`modr_m` bitfield `mod[7:6] / reg[5:3] / r/m[2:0]`, the accessors
`modr_m[mod]`, `modr_m[reg]`, `modr_m[r_m]`), and the SIB-presence rule
`x86_decode_sib_p`.

The second half records what each field reads back off the encoder's own byte
builders: `modRMReg`/`modRMMem` land the operands in the fields the decoder
reads them from, and a `REX.W` byte carries its `R` and `B` bits where the
decoder looks for them. `SailX86Decoder` and `SailX86BlockRoundtrip` build their
round-trips on these.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-! ## 1. REX / ModRM field extraction -/

/-- Is `b` a REX prefix byte (`0x40..0x4F`)? (`prefixes` legacy-prefix detection,
    Sail `get_one_byte_prefix_array_code` group; REX is the `0x4_` block.) -/
def isRex (b : BitVec 8) : Bool := 0x40 ≤ b.toNat ∧ b.toNat ≤ 0x4f

/-- REX.W bit (operand-size = 64). -/
def rexW (b : BitVec 8) : Nat := (b.toNat >>> 3) &&& 1
/-- REX.R bit (extends ModRM.reg). -/
def rexR (b : BitVec 8) : Nat := (b.toNat >>> 2) &&& 1
/-- REX.X bit (extends SIB.index). -/
def rexX (b : BitVec 8) : Nat := (b.toNat >>> 1) &&& 1
/-- REX.B bit (extends ModRM.rm / SIB.base). -/
def rexB (b : BitVec 8) : Nat := b.toNat &&& 1

/-- ModRM `mod` field (`modr_m[mod]`, bits 7:6). -/
def modField (b : BitVec 8) : Nat := (b.toNat >>> 6) &&& 3
/-- ModRM `reg` field (`modr_m[reg]`, bits 5:3). -/
def regField (b : BitVec 8) : Nat := (b.toNat >>> 3) &&& 7
/-- ModRM `r/m` field (`modr_m[r_m]`, bits 2:0). -/
def rmField (b : BitVec 8) : Nat := b.toNat &&& 7

/-- Sail `x86_decode_sib_p modr_m false` (64-bit mode): a SIB byte follows iff
    `r/m = 0b100 ∧ mod ≠ 0b11`. -/
def sibFollows (modrm : BitVec 8) : Bool :=
  rmField modrm = 4 ∧ modField modrm ≠ 3

/-- The GP register name (`%rN`) for a SDM register number `0..15`, the inverse of
    `gpNum` on the canonical names. -/
def regName : Nat → String
  | 0 => "%rax" | 1 => "%rcx" | 2 => "%rdx" | 3 => "%rbx"
  | 4 => "%rsp" | 5 => "%rbp" | 6 => "%rsi" | 7 => "%rdi"
  | 8 => "%r8"  | 9 => "%r9"  | 10 => "%r10" | 11 => "%r11"
  | 12 => "%r12" | 13 => "%r13" | 14 => "%r14" | _ => "%r15"

/-- `regName` inverts `gpNum` on the sixteen canonical `%rN` names. -/
theorem regName_gpNum (r : String) (h : r ∈ gpNames) : regName (gpNum r) = r := by
  simp only [gpNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-! ## 2. The register-number split -/

/-- For `n < 16`, `(n >>> 3 &&& 1) * 8 + (n &&& 7) = n` — the REX-bit/ModRM-field
    split is the identity on a 4-bit register number. -/
theorem regsplit_id (n : Nat) (h : n < 16) :
    ((n >>> 3) &&& 1) * 8 + (n &&& 7) = n := by
  interval_cases n
  all_goals decide

/-- `gpNum` always lands in the GP range `0..15` (it is a 16-way table with a `0`
    fallback) — so every register operand the encoder emits decodes back into the
    `< 16` range the round-trip lemmas require. -/
theorem gpNum_lt_16 (r : String) : gpNum r < 16 := by
  unfold gpNum
  split <;> omega

/-- A `bit` value is `0` or `1`. -/
theorem bit_le_one (n i : Nat) : bit n i ≤ 1 := by
  have h : (n >>> i) &&& 1 = (n >>> i) % 2 := Nat.and_two_pow_sub_one_eq_mod _ 1
  simp only [bit, h]
  omega

/-! ## 3. Little-endian immediate recomposition -/

/-- The little-endian 32-bit recomposition the decoder applies is the inverse of
    `imm32LE` on values `< 2^32`: `b0 + b1·256 + b2·256² + b3·256³ = v`. The four
    `BitVec 8` bytes' `.toNat` are `(v >>> 8i) &&& 0xff` reduced mod `256`. -/
theorem imm32LE_recompose (v : Nat) (hv : v < 2 ^ 32) :
    (BitVec.ofNat 8 (v &&& 0xff)).toNat
      + (BitVec.ofNat 8 ((v >>> 8) &&& 0xff)).toNat * 0x100
      + (BitVec.ofNat 8 ((v >>> 16) &&& 0xff)).toNat * 0x10000
      + (BitVec.ofNat 8 ((v >>> 24) &&& 0xff)).toNat * 0x1000000 = v := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The little-endian 64-bit recomposition the `B8+r io` decoder applies is the
    inverse of `imm64LE` on values `< 2^64`. The eight `BitVec 8` bytes' `.toNat`
    are `(v >>> 8i) &&& 0xff` reduced mod `256`. -/
theorem imm64LE_recompose (v : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 8 (v &&& 0xff)).toNat
      + (BitVec.ofNat 8 ((v >>> 8) &&& 0xff)).toNat * 0x100
      + (BitVec.ofNat 8 ((v >>> 16) &&& 0xff)).toNat * 0x10000
      + (BitVec.ofNat 8 ((v >>> 24) &&& 0xff)).toNat * 0x1000000
      + (BitVec.ofNat 8 ((v >>> 32) &&& 0xff)).toNat * 0x100000000
      + (BitVec.ofNat 8 ((v >>> 40) &&& 0xff)).toNat * 0x10000000000
      + (BitVec.ofNat 8 ((v >>> 48) &&& 0xff)).toNat * 0x1000000000000
      + (BitVec.ofNat 8 ((v >>> 56) &&& 0xff)).toNat * 0x100000000000000 = v := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## 4. The fields of the encoder's ModRM and REX bytes -/

/-- `rmField (modRMMem m reg b) = b &&& 7` — the ModRM `r/m` field is the base low-3. -/
theorem rmField_modRMMem (m reg b : Nat) :
    rmField (BitVec.ofNat 8 (modRMMem m reg b)) = b &&& 7 := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (b &&& 7) = b % 8 := Nat.and_two_pow_sub_one_eq_mod b 3
  rw [rmField, Nat.and_two_pow_sub_one_eq_mod _ 3, BitVec.toNat_ofNat, eb]
  unfold modRMMem; rw [er, eb]; omega

/-- `modField (modRMMem m reg b) = m` for a valid `mod` (`m < 4`). -/
theorem modField_modRMMem (m reg b : Nat) (hm : m < 4) :
    modField (BitVec.ofNat 8 (modRMMem m reg b)) = m := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (b &&& 7) = b % 8 := Nat.and_two_pow_sub_one_eq_mod b 3
  rw [modField, Nat.and_two_pow_sub_one_eq_mod _ 2, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  unfold modRMMem; rw [er, eb]; omega

/-- `regField (modRMMem m reg b) = reg &&& 7` — the other operand rides the ModRM
    `reg` field. -/
theorem regField_modRMMem (m reg b : Nat) :
    regField (BitVec.ofNat 8 (modRMMem m reg b)) = reg &&& 7 := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (b &&& 7) = b % 8 := Nat.and_two_pow_sub_one_eq_mod b 3
  rw [regField, Nat.and_two_pow_sub_one_eq_mod _ 3, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, er]
  unfold modRMMem; rw [er, eb]; omega

/-- `modRMReg` sets `mod = 0b11` (register-direct). -/
theorem modField_modRMReg (reg rm : Nat) :
    modField (BitVec.ofNat 8 (modRMReg reg rm)) = 3 := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (rm &&& 7) = rm % 8 := Nat.and_two_pow_sub_one_eq_mod rm 3
  rw [modField, Nat.and_two_pow_sub_one_eq_mod _ 2, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  unfold modRMReg; rw [er, eb]; omega

/-- `regField (modRMReg reg rm) = reg &&& 7`. -/
theorem regField_modRMReg (reg rm : Nat) :
    regField (BitVec.ofNat 8 (modRMReg reg rm)) = reg &&& 7 := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (rm &&& 7) = rm % 8 := Nat.and_two_pow_sub_one_eq_mod rm 3
  rw [regField, Nat.and_two_pow_sub_one_eq_mod _ 3, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, er]
  unfold modRMReg; rw [er, eb]; omega

/-- `rmField (modRMReg reg rm) = rm &&& 7`. -/
theorem rmField_modRMReg (reg rm : Nat) :
    rmField (BitVec.ofNat 8 (modRMReg reg rm)) = rm &&& 7 := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (rm &&& 7) = rm % 8 := Nat.and_two_pow_sub_one_eq_mod rm 3
  rw [rmField, Nat.and_two_pow_sub_one_eq_mod _ 3, BitVec.toNat_ofNat, eb]
  unfold modRMReg; rw [er, eb]; omega

/-- A `REX.W` prefix byte lies in the `0x40..0x4F` block. -/
theorem isRex_rex (r x b : Nat) (hr : r ≤ 1) (hx : x ≤ 1) (hb : b ≤ 1) :
    isRex (BitVec.ofNat 8 (rex 1 r x b)) = true := by
  simp only [isRex, BitVec.toNat_ofNat, rex, decide_eq_true_eq]
  omega

/-- `REX.R` of a `REX.W` prefix byte is the bit the encoder put there. -/
theorem rexR_rex (r x b : Nat) (hr : r ≤ 1) (hx : x ≤ 1) (hb : b ≤ 1) :
    rexR (BitVec.ofNat 8 (rex 1 r x b)) = r := by
  rw [rexR, Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  unfold rex; omega

/-- `REX.B` of a `REX.W` prefix byte is the bit the encoder put there. -/
theorem rexB_rex (r x b : Nat) (hb : b ≤ 1) :
    rexB (BitVec.ofNat 8 (rex 1 r x b)) = b := by
  rw [rexB, Nat.and_two_pow_sub_one_eq_mod _ 1, BitVec.toNat_ofNat]
  unfold rex; omega

/-! ## 5. The one-byte ALU opcode tables -/

/-- The one-byte ALU/MOV opcode → mnemonic constructor map, inverting the opcode
    bytes `encodeJInstr` emits for the reg-reg arms (`ADD 01`, `OR 09`, `ADC 11`,
    `SBB 19`, `AND 21`, `SUB 29`, `XOR 31`, `MOV 89`). Returns the `JInstr`
    constructor expecting `(dst, src)`. -/
def aluMnemonic : Nat → Option (String → JOperand → JInstr 64)
  | 0x01 => some JInstr.add
  | 0x09 => some JInstr.or_
  | 0x11 => some JInstr.adc
  | 0x19 => some JInstr.sbb
  | 0x21 => some JInstr.and_
  | 0x29 => some JInstr.sub
  | 0x31 => some JInstr.xor_
  | 0x89 => some JInstr.mov
  | _    => none

/-- The `81 /digit id` group-1 opcode-extension digit → mnemonic constructor map,
    inverting the digits `encodeJInstr` emits for the `imm32`-source ALU arms
    (`ADD /0`, `OR /1`, `ADC /2`, `SBB /3`, `AND /4`, `SUB /5`, `XOR /6`). -/
def aluImmMnemonic : Nat → Option (String → JOperand → JInstr 64)
  | 0 => some JInstr.add
  | 1 => some JInstr.or_
  | 2 => some JInstr.adc
  | 3 => some JInstr.sbb
  | 4 => some JInstr.and_
  | 5 => some JInstr.sub
  | 6 => some JInstr.xor_
  | _ => none

end CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
