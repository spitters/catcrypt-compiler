/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms

/-!
# Byte-stream round trip for the shipped encoder `encodeJBlock6`

`GatherImmForms.encodeJInstr6` is `ScalarEncoder.encodeJInstr` except on two
immediate forms:

* `.mov d (.imm v)` takes the `REX.W C7 /0 id` form whenever `v` sign-extends
  from 32 bits (`v < 2 ^ 31` or `2 ^ 64 - 2 ^ 31 ≤ v`), and the `REX.W B8+r io`
  form otherwise;
* `.shl`/`.shr d (.imm 1)` take the `REX.W D1 /4` resp. `D1 /5` shift-by-one form.

`SailX86Decoder.decodeJ1` has no `D1` arm, reads the `C7 /0 id` immediate
zero-extended, which is the 64-bit value of the instruction only below `2 ^ 31`,
and has no arm for the compares `REX.W 39 /r` and `REX.W 81 /7 id` (the loop exit
test `XLoop.cmpInstr` is `cmp ctr (.imm 0)`). `decodeJ1_6` extends it: it runs
`decodeJ1`, sign-extends the immediate of a decoded `REX.W C7` move
(`sextMovC7`), and on a stream `decodeJ1` rejects tries the `D1` shift-by-one
forms (`decodeShift1`) and then the compares (`decodeCmp`, whose `imm32` field is
read sign-extended, the value the CPU compares against).

The indexed memory moves `loadMemIdx`/`storeMemIdx` are inverted by `decodeJ1`
itself (`SailX86Decoder.roundtrip_loadMemIdx`, `roundtrip_storeMemIdx`); their
side condition — the index register is not allocated to `%rsp` — is a fact of
the allocation, so it enters the covered set here, through `newCovered6`, rather
than through `blockCovered`.

## Main results

* `sext32`, `sextMovC7`, `decodeShift1`, `decodeCmp`, `decodeJ1_6`,
  `decodeJStream6`: the extended decoder and its stream version.
* `sext32_imm32`: sign-extending the low 32 bits of a 64-bit value that fits a
  signed 32-bit immediate recovers the value, in both ranges.
* `decodeJ1_6_of_decodeJ1`: wherever `decodeJ1` succeeds, `decodeJ1_6` succeeds
  with the same remaining bytes and the same instruction up to `sextMovC7`.
* `roundtrip_movImm6`, `roundtrip_shl1`, `roundtrip_shr1`: the three arms where
  `encodeJInstr6` differs from `encodeJInstr` decode back to themselves.
* `roundtrip_cmpRR`, `roundtrip_cmpImm`, `roundtrip_cmpInstr`,
  `roundtrip_loadMemIdx6`, `roundtrip_storeMemIdx6`: the forms outside
  `blockCovered` decode back to themselves.
* `blockCovered6`: `blockCovered`, or one of the `newCovered6` forms: an indexed
  load or register store whose index register is not `%rsp` and whose stride is
  in `{1, 2, 4, 8}`, a register compare, or an immediate compare whose value is
  below `2 ^ 64` and sign-extends from 32 bits.
* `roundtrip_decodeJ1_6`: one covered instruction decodes off the front of its
  `encodeJInstr6` bytes.
* `roundtrip_block6`: `decodeJStream6 block.length (encodeJBlock6 alloc block)
  = some (block.map (renameJ alloc))` under `blockCovered6` and `mulxRdxOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encMovImmw encShift1 rexOpt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (encodeJInstr6 encodeJBlock6)

/-! ## 1. The extended decoder -/

/-- The 64-bit value a 32-bit immediate field `u < 2 ^ 32` denotes under sign
    extension: `u` below `2 ^ 31`, else `u + (2 ^ 64 - 2 ^ 32)`. -/
def sext32 (u : Nat) : Nat := if u < 2 ^ 31 then u else u + (2 ^ 64 - 2 ^ 32)

/-- The instruction `decodeJ1_6` returns for a `decodeJ1` result `i` read off the
    bytes `bs`: when `bs` starts with a `REX.W` byte followed by `C7` and `i` is a
    `mov` of an immediate, the immediate is sign-extended by `sext32`; every other
    instruction is unchanged. -/
def sextMovC7 (bs : List (BitVec 8)) : JInstr 64 → JInstr 64
  | .mov d (.imm u) =>
      match bs with
      | r :: op :: _ =>
          if rexW r = 1 ∧ op.toNat = 0xc7 then .mov d (.imm (sext32 u)) else .mov d (.imm u)
      | _ => .mov d (.imm u)
  | i => i

/-- The `REX.W D1 /4` (`shl $1`) and `REX.W D1 /5` (`shr $1`) register-direct
    shift-by-one forms. -/
def decodeShift1 : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | r :: op :: modrm :: rest =>
      if isRex r ∧ rexW r = 1 ∧ op.toNat = 0xd1 ∧ modField modrm = 3 then
        let dst := regName (rexB r * 8 + rmField modrm)
        if regField modrm = 4 then some (.shl dst (.imm 1), rest)
        else if regField modrm = 5 then some (.shr dst (.imm 1), rest)
        else none
      else none
  | _ => none

/-- The register-direct compares `REX.W 39 /r` (`cmp %reg, %rm`, computing
    `rm - reg`) and `REX.W 81 /7 id` (`cmp $imm32, %rm`, the immediate
    sign-extended to 64 bits). -/
def decodeCmp : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | r :: op :: modrm :: rest =>
      if isRex r ∧ rexW r = 1 ∧ modField modrm = 3 then
        let a := regName (rexB r * 8 + rmField modrm)
        if op.toNat = 0x39 then
          some (.cmp a (.reg (regName (rexR r * 8 + regField modrm))), rest)
        else if op.toNat = 0x81 ∧ regField modrm = 7 then
          match rest with
          | j0 :: j1 :: j2 :: j3 :: rest1 =>
              some (.cmp a (.imm (sext32 (j0.toNat + j1.toNat * 0x100
                + j2.toNat * 0x10000 + j3.toNat * 0x1000000))), rest1)
          | _ => none
        else none
      else none
  | _ => none

/-- Decode one instruction off the front of a byte stream: `decodeJ1` with the
    `REX.W C7 /0 id` immediate sign-extended, and on the streams `decodeJ1`
    rejects, the `D1` shift-by-one forms and then the compares. -/
def decodeJ1_6 (bs : List (BitVec 8)) : Option (JInstr 64 × List (BitVec 8)) :=
  match decodeJ1 bs with
  | some (i, rest) => some (sextMovC7 bs i, rest)
  | none => (decodeShift1 bs).or (decodeCmp bs)

/-- Decode a byte stream into `n` instructions with `decodeJ1_6`, requiring the
    stream to be consumed exactly. -/
def decodeJStream6 : Nat → List (BitVec 8) → Option (List (JInstr 64))
  | 0, bs => if bs.isEmpty then some [] else none
  | n + 1, bs =>
      match decodeJ1_6 bs with
      | some (i, rest) => (decodeJStream6 n rest).map (i :: ·)
      | none => none

/-! ## 2. Relation to `decodeJ1` -/

/-- Wherever `decodeJ1` succeeds, `decodeJ1_6` succeeds with the same remaining
    bytes, and returns the `decodeJ1` instruction passed through `sextMovC7`. -/
theorem decodeJ1_6_of_decodeJ1 (bs rest : List (BitVec 8)) (i : JInstr 64)
    (h : decodeJ1 bs = some (i, rest)) :
    decodeJ1_6 bs = some (sextMovC7 bs i, rest) := by
  simp only [decodeJ1_6, h]

/-- On a stream `decodeJ1` rejects, `decodeJ1_6` is `decodeShift1`, then
    `decodeCmp`. -/
theorem decodeJ1_6_of_none (bs : List (BitVec 8)) (h : decodeJ1 bs = none) :
    decodeJ1_6 bs = (decodeShift1 bs).or (decodeCmp bs) := by
  simp only [decodeJ1_6, h]

/-! ## 3. Sign extension of the `imm32` field -/

/-- The little-endian 32-bit recomposition of the `imm32LE` bytes of any `v` is
    `v % 2 ^ 32`. -/
theorem imm32_recompose_mod_any (v : Nat) :
    (v &&& 0xff) % 2 ^ 8 + ((v >>> 8) &&& 0xff) % 2 ^ 8 * 0x100
      + ((v >>> 16) &&& 0xff) % 2 ^ 8 * 0x10000
      + ((v >>> 24) &&& 0xff) % 2 ^ 8 * 0x1000000 = v % 2 ^ 32 := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  omega

/-- Sign-extending the low 32 bits of a 64-bit value that fits a signed 32-bit
    immediate recovers the value: below `2 ^ 31` the low bits are the value, and
    for `2 ^ 64 - 2 ^ 31 ≤ v < 2 ^ 64` they are `v - (2 ^ 64 - 2 ^ 32)`, which is at
    least `2 ^ 31`. -/
theorem sext32_imm32 (v : Nat) (hv : v < 2 ^ 64)
    (hf : X86Backend.GatherImmForms.fitsImm32S v = true) : sext32 (v % 2 ^ 32) = v := by
  simp only [X86Backend.GatherImmForms.fitsImm32S, Bool.or_eq_true, decide_eq_true_eq] at hf
  unfold sext32
  split <;> omega

/-! ## 4. Prefix-byte facts -/

/-- `REX.W` of a `rex 1 r x b` byte is `1`. -/
theorem rexW_rex (r x b : Nat) (hr : r ≤ 1) (hx : x ≤ 1) (hb : b ≤ 1) :
    rexW (BitVec.ofNat 8 (rex 1 r x b)) = 1 := by
  rw [rexW, Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  unfold rex; omega

/-- A `REX.W` prefix with no `R`/`X` bit is the one byte `rexOpt 1 0 0 b` emits. -/
theorem rexOpt_one (b : Nat) : rexOpt 1 0 0 b = [BitVec.ofNat 8 (rex 1 0 0 b)] := by
  simp [rexOpt]

/-- `encMovImmw 1` is the `encMovImm` byte string. -/
theorem encMovImmw_one_eq (d v : Nat) : encMovImmw 1 d v = encMovImm d v := by
  simp [encMovImmw, encMovImm, rexOpt]

/-! ## 5. The shift-by-one forms -/

/-- `decodeJ1` rejects a `REX.W D1` register-direct stream: `D1` is none of the
    opcodes `decodeRex` dispatches on and has no entry in `aluMnemonic`. -/
theorem decodeJ1_shift1 (ext d : Nat) (rest : List (BitVec 8)) :
    decodeJ1 (encShift1 1 ext d ++ rest) = none := by
  simp only [encShift1, rexOpt_one, List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0xd1 : Nat) % 2 ^ 8 ∧ (0xd1 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0x8b) by decide),
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0x89) by decide),
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0x81) by decide),
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0xc7) by decide),
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0x69) by decide),
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0xc1) by decide),
    if_neg (show ¬((0xd1 : Nat) % 2 ^ 8 = 0xf7) by decide),
    modField_modRMReg, ne_eq, not_true_eq_false, if_false]
  rfl

/-- `decodeShift1` inverts `encShift1 1 ext` at the digits `4` (`shl`) and `5`
    (`shr`). -/
theorem decodeShift1_encShift1 (alloc : GpAlloc) (ext : Nat) (d : String)
    (rest : List (BitVec 8)) (he : ext = 4 ∨ ext = 5) :
    decodeShift1 (encShift1 1 ext (gpNum (regOf alloc d)) ++ rest)
      = some ((if ext = 4 then JInstr.shl (nameOf alloc d) (.imm 1)
          else JInstr.shr (nameOf alloc d) (.imm 1)), rest) := by
  have he7 : ext &&& 7 = ext := by
    rcases he with rfl | rfl <;> decide
  rcases he with rfl | rfl <;>
  simp only [encShift1, rexOpt_one, List.cons_append, List.nil_append, decodeShift1,
    isRex_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    rexW_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), BitVec.toNat_ofNat,
    modField_modRMReg, regField_modRMReg, rmField_modRMReg, he7, regName_split,
    show (0xd1 : Nat) % 2 ^ 8 = 0xd1 from rfl, and_self, if_true,
    if_neg (show ¬((5 : Nat) = 4) by decide)]

/-- `SHL $1, %dst` (`REX.W D1 /4`) decodes back to itself. -/
theorem roundtrip_shl1 (alloc : GpAlloc) (d : String) (rest : List (BitVec 8)) :
    decodeJ1_6 (encodeJInstr6 alloc (.shl d (.imm 1)) ++ rest)
      = some (renameJ alloc (.shl d (.imm 1)), rest) := by
  simp only [encodeJInstr6, if_true]
  rw [decodeJ1_6_of_none _ (decodeJ1_shift1 _ _ _),
    decodeShift1_encShift1 alloc 4 d rest (Or.inl rfl)]
  simp [renameJ, operandOf]

/-- `SHR $1, %dst` (`REX.W D1 /5`) decodes back to itself. -/
theorem roundtrip_shr1 (alloc : GpAlloc) (d : String) (rest : List (BitVec 8)) :
    decodeJ1_6 (encodeJInstr6 alloc (.shr d (.imm 1)) ++ rest)
      = some (renameJ alloc (.shr d (.imm 1)), rest) := by
  simp only [encodeJInstr6, if_true]
  rw [decodeJ1_6_of_none _ (decodeJ1_shift1 _ _ _),
    decodeShift1_encShift1 alloc 5 d rest (Or.inr rfl)]
  simp [renameJ, operandOf]

/-! ## 6. The immediate `MOV` -/

/-- `decodeJ1` reads a `REX.W C7 /0 id` stream as a `mov` of the zero-extended
    `imm32` field, `v % 2 ^ 32`. -/
theorem decodeJ1_encMovImm (alloc : GpAlloc) (d : String) (v : Nat)
    (rest : List (BitVec 8)) :
    decodeJ1 (encMovImm (gpNum (regOf alloc d)) v ++ rest)
      = some (.mov (nameOf alloc d) (.imm (v % 2 ^ 32)), rest) := by
  simp only [encMovImm, imm32LE, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0xc7 : Nat) % 2 ^ 8 ∧ (0xc7 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x8b) by decide),
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x89) by decide),
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x81) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    if_false, if_true, show (0 : Nat) &&& 7 = 0 by decide,
    imm32_recompose_mod_any v]

/-- `MOV $imm, %dst` decodes back to itself from its `encodeJInstr6` bytes for any
    immediate a 64-bit register holds: the `REX.W C7 /0 id` form over the whole
    sign-extendable range, including `2 ^ 64 - 2 ^ 31 ≤ v`, and the `REX.W B8+r io`
    form elsewhere. -/
theorem roundtrip_movImm6 (alloc : GpAlloc) (d : String) (v : Nat)
    (rest : List (BitVec 8)) (hv : v < 2 ^ 64) :
    decodeJ1_6 (encodeJInstr6 alloc (.mov d (.imm v)) ++ rest)
      = some (renameJ alloc (.mov d (.imm v)), rest) := by
  by_cases hf : X86Backend.GatherImmForms.fitsImm32S v = true
  · simp only [encodeJInstr6, if_pos hf, encMovImmw_one_eq]
    rw [decodeJ1_6_of_decodeJ1 _ _ _ (decodeJ1_encMovImm alloc d v rest)]
    simp only [encMovImm, List.map_cons, List.cons_append, sextMovC7,
      rexW_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
      BitVec.toNat_ofNat, show (0xc7 : Nat) % 2 ^ 8 = 0xc7 from rfl, and_self, if_true,
      sext32_imm32 v hv hf, renameJ, operandOf]
  · have h31 : ¬ v < 2 ^ 31 := by
      simp only [X86Backend.GatherImmForms.fitsImm32S, Bool.or_eq_true, decide_eq_true_eq,
        not_or] at hf
      exact hf.1
    have henc : encodeJInstr6 alloc (.mov d (.imm v)) = encodeJInstr alloc (.mov d (.imm v)) := by
      simp only [encodeJInstr6, if_neg hf, encodeJInstr, if_neg h31]
    rw [henc, decodeJ1_6_of_decodeJ1 _ _ _ (roundtrip_movImm alloc d v rest hv)]
    have hlow : gpNum (regOf alloc d) &&& 7 < 8 := by
      rw [Nat.and_two_pow_sub_one_eq_mod _ 3]; omega
    have hop : ¬ ((0xb8 + (gpNum (regOf alloc d) &&& 7)) % 2 ^ 8 = 0xc7) := by omega
    simp only [encodeJInstr, if_neg h31, encMovImm64, List.map_cons, List.cons_append,
      renameJ, operandOf, sextMovC7, BitVec.toNat_ofNat, hop, and_false, if_false]

/-! ## 7. The compares -/

/-- `decodeJ1` rejects a `REX.W 39 /r` stream: `39` is none of the opcodes
    `decodeRex` dispatches on and has no entry in `aluMnemonic`. -/
theorem decodeJ1_cmpRR (a s : Nat) (rest : List (BitVec 8)) :
    decodeJ1 (encAluRR 0x39 a s ++ rest) = none := by
  simp only [encAluRR, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0x39 : Nat) % 2 ^ 8 ∧ (0x39 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0x8b) by decide),
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0x89) by decide),
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0x81) by decide),
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0xc7) by decide),
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0x69) by decide),
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0xc1) by decide),
    if_neg (show ¬((0x39 : Nat) % 2 ^ 8 = 0xf7) by decide),
    modField_modRMReg, ne_eq, not_true_eq_false, if_false]
  rfl

/-- `decodeJ1` rejects a `REX.W 81 /7 id` stream: `aluImmMnemonic` has no entry for
    the digit `7`. -/
theorem decodeJ1_cmpImm (a v : Nat) (rest : List (BitVec 8)) :
    decodeJ1 (encAluImm 7 a v ++ rest) = none := by
  simp only [encAluImm, imm32LE, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0x81 : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0x81 : Nat) % 2 ^ 8 ∧ (0x81 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0x81 : Nat) % 2 ^ 8 = 0x8b) by decide),
    if_neg (show ¬((0x81 : Nat) % 2 ^ 8 = 0x89) by decide),
    modField_modRMReg, regField_modRMReg, show (7 : Nat) &&& 7 = 7 by decide,
    ne_eq, not_true_eq_false, if_false, if_true]
  rfl

/-- `decodeShift1` rejects a `REX.W 39 /r` stream. -/
theorem decodeShift1_cmpRR (a s : Nat) (rest : List (BitVec 8)) :
    decodeShift1 (encAluRR 0x39 a s ++ rest) = none := by
  simp [encAluRR, decodeShift1]

/-- `decodeShift1` rejects a `REX.W 81 /7 id` stream. -/
theorem decodeShift1_cmpImm (a v : Nat) (rest : List (BitVec 8)) :
    decodeShift1 (encAluImm 7 a v ++ rest) = none := by
  simp [encAluImm, decodeShift1]

/-- `decodeCmp` inverts `encAluRR 0x39`: the `rm` field is the first operand and the
    `reg` field the second. -/
theorem decodeCmp_cmpRR (a s : Nat) (rest : List (BitVec 8)) :
    decodeCmp (encAluRR 0x39 a s ++ rest)
      = some (.cmp (regName (bit a 3 * 8 + (a &&& 7)))
          (.reg (regName (bit s 3 * 8 + (s &&& 7)))), rest) := by
  simp only [encAluRR, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeCmp, isRex_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexW_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), BitVec.toNat_ofNat,
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    show (0x39 : Nat) % 2 ^ 8 = 0x39 from rfl, and_self, if_true]

/-- `decodeCmp` inverts `encAluImm 7`, reading the `imm32` field sign-extended. -/
theorem decodeCmp_cmpImm (a v : Nat) (rest : List (BitVec 8)) :
    decodeCmp (encAluImm 7 a v ++ rest)
      = some (.cmp (regName (bit a 3 * 8 + (a &&& 7))) (.imm (sext32 (v % 2 ^ 32))), rest) := by
  simp only [encAluImm, imm32LE, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, decodeCmp,
    isRex_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    rexW_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), BitVec.toNat_ofNat,
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    show (7 : Nat) &&& 7 = 7 by decide,
    show (0x81 : Nat) % 2 ^ 8 = 0x81 from rfl, and_self, if_true,
    imm32_recompose_mod_any v, if_neg (show ¬ ((0x81 : Nat) = 0x39) by decide)]

/-- `CMP %src, %dst` (`REX.W 39 /r`) decodes back to itself. -/
theorem roundtrip_cmpRR (alloc : GpAlloc) (a s : String) (rest : List (BitVec 8)) :
    decodeJ1_6 (encodeJInstr6 alloc (.cmp a (.reg s)) ++ rest)
      = some (renameJ alloc (.cmp a (.reg s)), rest) := by
  simp only [encodeJInstr6, encodeJInstr]
  rw [decodeJ1_6_of_none _ (decodeJ1_cmpRR _ _ rest), decodeShift1_cmpRR, Option.none_or,
    decodeCmp_cmpRR]
  simp only [regName_split, renameJ, operandOf]

/-- `CMP $imm32, %dst` (`REX.W 81 /7 id`) decodes back to itself for every
    immediate below `2 ^ 64` that sign-extends from 32 bits. -/
theorem roundtrip_cmpImm (alloc : GpAlloc) (a : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1_6 (encodeJInstr6 alloc (.cmp a (.imm v)) ++ rest)
      = some (renameJ alloc (.cmp a (.imm v)), rest) := by
  simp only [encodeJInstr6, encodeJInstr]
  rw [decodeJ1_6_of_none _ (decodeJ1_cmpImm _ _ rest), decodeShift1_cmpImm, Option.none_or,
    decodeCmp_cmpImm, sext32_imm32 v hv hf]
  simp only [regName_split, renameJ, operandOf]

/-- The loop exit test `XLoop.cmpInstr`, `cmp ctr $0`, decodes back to itself. -/
theorem roundtrip_cmpInstr (alloc : GpAlloc) (l : X86Backend.LprogControlFlow.XLoop 64)
    (rest : List (BitVec 8)) :
    decodeJ1_6 (encodeJInstr6 alloc l.cmpInstr ++ rest)
      = some (renameJ alloc l.cmpInstr, rest) :=
  roundtrip_cmpImm alloc l.ctr 0 rest (by decide) (by decide)

/-! ## 8. The forms `decodeJ1` inverts -/

/-- An instruction on which `encodeJInstr6` agrees with `encodeJInstr`, whose
    renamed form `sextMovC7` leaves unchanged, and which `decodeJ1` reads back
    off its `encodeJInstr` bytes, decodes back to itself through `decodeJ1_6`. -/
theorem roundtrip_of_decodeJ1 (alloc : GpAlloc) (i : JInstr 64) (rest : List (BitVec 8))
    (henc : encodeJInstr6 alloc i = encodeJInstr alloc i)
    (hs : ∀ bs, sextMovC7 bs (renameJ alloc i) = renameJ alloc i)
    (h : decodeJ1 (encodeJInstr alloc i ++ rest) = some (renameJ alloc i, rest)) :
    decodeJ1_6 (encodeJInstr6 alloc i ++ rest) = some (renameJ alloc i, rest) := by
  rw [henc, decodeJ1_6_of_decodeJ1 _ _ _ h, hs]

/-- A covered instruction on which `encodeJInstr6` agrees with `encodeJInstr` and
    whose renamed form `sextMovC7` leaves unchanged decodes back to itself. -/
theorem roundtrip_of_encodeJInstr (alloc : GpAlloc) (i : JInstr 64) (rest : List (BitVec 8))
    (henc : encodeJInstr6 alloc i = encodeJInstr alloc i)
    (hs : ∀ bs, sextMovC7 bs (renameJ alloc i) = renameJ alloc i)
    (hc : blockCovered i = true) (hr : mulxRdxOk alloc i = true) :
    decodeJ1_6 (encodeJInstr6 alloc i ++ rest) = some (renameJ alloc i, rest) :=
  roundtrip_of_decodeJ1 alloc i rest henc hs (roundtrip_decodeJ1 alloc i rest hc hr)

/-- `MOV (%base,%idx,scale), %dst` decodes back to itself through `decodeJ1_6`
    when the index register is not `%rsp` and the stride is `1`, `2`, `4` or `8`. -/
theorem roundtrip_loadMemIdx6 (alloc : GpAlloc) (d base idx : String) (scale : Nat)
    (rest : List (BitVec 8)) (hx4 : gpNum (regOf alloc idx) ≠ 4)
    (hs : scaleOk scale = true) :
    decodeJ1_6 (encodeJInstr6 alloc (.loadMemIdx d base idx scale) ++ rest)
      = some (renameJ alloc (.loadMemIdx d base idx scale), rest) :=
  roundtrip_of_decodeJ1 alloc _ rest rfl (fun _ => rfl)
    (roundtrip_loadMemIdx alloc d base idx scale rest hx4 hs)

/-- `MOV %src, (%base,%idx,scale)` decodes back to itself through `decodeJ1_6`
    when the index register is not `%rsp` and the stride is `1`, `2`, `4` or `8`. -/
theorem roundtrip_storeMemIdx6 (alloc : GpAlloc) (base idx : String) (scale : Nat)
    (s : String) (rest : List (BitVec 8)) (hx4 : gpNum (regOf alloc idx) ≠ 4)
    (hs : scaleOk scale = true) :
    decodeJ1_6 (encodeJInstr6 alloc (.storeMemIdx base idx scale (.reg s)) ++ rest)
      = some (renameJ alloc (.storeMemIdx base idx scale (.reg s)), rest) :=
  roundtrip_of_decodeJ1 alloc _ rest rfl (fun _ => rfl)
    (roundtrip_storeMemIdx alloc base idx scale s rest hx4 hs)

/-- One instruction of `blockCovered` decodes off the front of its `encodeJInstr6`
    bytes, leaving whatever follows untouched. -/
theorem roundtrip_decodeJ1_6_covered (alloc : GpAlloc) (i : JInstr 64) (rest : List (BitVec 8))
    (hc : blockCovered i = true) (hr : mulxRdxOk alloc i = true) :
    decodeJ1_6 (encodeJInstr6 alloc i ++ rest) = some (renameJ alloc i, rest) := by
  cases i with
  | mov d s =>
      cases s with
      | reg r => exact roundtrip_of_encodeJInstr alloc _ rest rfl (fun _ => rfl) hc hr
      | imm v => exact roundtrip_movImm6 alloc d v rest (of_decide_eq_true hc)
  | shl d s =>
      cases s with
      | reg r => exact roundtrip_of_encodeJInstr alloc _ rest rfl (fun _ => rfl) hc hr
      | imm v =>
          by_cases h1 : v = 1
          · subst h1; exact roundtrip_shl1 alloc d rest
          · exact roundtrip_of_encodeJInstr alloc _ rest
              (by simp only [encodeJInstr6, if_neg h1, encodeJInstr]) (fun _ => rfl) hc hr
  | shr d s =>
      cases s with
      | reg r => exact roundtrip_of_encodeJInstr alloc _ rest rfl (fun _ => rfl) hc hr
      | imm v =>
          by_cases h1 : v = 1
          · subst h1; exact roundtrip_shr1 alloc d rest
          · exact roundtrip_of_encodeJInstr alloc _ rest
              (by simp only [encodeJInstr6, if_neg h1, encodeJInstr]) (fun _ => rfl) hc hr
  | _ => exact roundtrip_of_encodeJInstr alloc _ rest rfl (fun _ => rfl) hc hr

/-! ## 9. The covered set -/

/-- The forms outside `blockCovered` that `decodeJ1_6` inverts, with the operand
    side conditions their encodings need: an indexed load, or an indexed store of a
    register, whose index register the allocation does not place on `%rsp`
    (`SIB.index = 100` without `REX.X` names no index) and whose stride is `1`, `2`,
    `4` or `8` (`sibScale` encodes any other stride as `1`); a register compare; an
    immediate compare whose value is below `2 ^ 64` and sign-extends from 32 bits. -/
def newCovered6 (alloc : GpAlloc) : JInstr 64 → Bool
  | .loadMemIdx _ _ idx scale => gpNum (regOf alloc idx) != 4 && scaleOk scale
  | .storeMemIdx _ idx scale (.reg _) => gpNum (regOf alloc idx) != 4 && scaleOk scale
  | .cmp _ (.reg _) => true
  | .cmp _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | _ => false

/-- The instruction forms a block may contain for the round trip through
    `decodeJ1_6`: the `blockCovered` forms, and the `newCovered6` forms. -/
def blockCovered6 (alloc : GpAlloc) (i : JInstr 64) : Bool :=
  blockCovered i || newCovered6 alloc i

/-! ## 10. One instruction and a whole block -/

/-- One instruction of the covered set decodes off the front of its `encodeJInstr6`
    bytes, leaving whatever follows untouched. -/
theorem roundtrip_decodeJ1_6 (alloc : GpAlloc) (i : JInstr 64) (rest : List (BitVec 8))
    (hc : blockCovered6 alloc i = true) (hr : mulxRdxOk alloc i = true) :
    decodeJ1_6 (encodeJInstr6 alloc i ++ rest) = some (renameJ alloc i, rest) := by
  simp only [blockCovered6, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact roundtrip_decodeJ1_6_covered alloc i rest hc hr
  · cases i with
    | loadMemIdx d b x s =>
        simp only [newCovered6, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        exact roundtrip_loadMemIdx6 alloc d b x s rest hc.1 hc.2
    | storeMemIdx b x s v =>
        cases v with
        | reg v =>
            simp only [newCovered6, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
            exact roundtrip_storeMemIdx6 alloc b x s v rest hc.1 hc.2
        | imm _ => simp [newCovered6] at hc
    | cmp a v =>
        cases v with
        | reg s => exact roundtrip_cmpRR alloc a s rest
        | imm v =>
            simp only [newCovered6, Bool.and_eq_true, decide_eq_true_eq] at hc
            exact roundtrip_cmpImm alloc a v rest hc.1 hc.2
    | _ => simp [newCovered6] at hc

/-- A block built from the covered forms decodes back from its shipped
    `encodeJBlock6` bytes, instruction by instruction, with no bytes left over. -/
theorem roundtrip_block6 (alloc : GpAlloc) (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered6 alloc i = true)
    (hr : ∀ i ∈ block, mulxRdxOk alloc i = true) :
    decodeJStream6 block.length (encodeJBlock6 alloc block)
      = some (block.map (renameJ alloc)) := by
  induction block with
  | nil => rfl
  | cons i is ih =>
      have hrest := ih (fun j hj => hc j (by simp [hj])) (fun j hj => hr j (by simp [hj]))
      simp only [encodeJBlock6] at hrest ⊢
      simp only [List.length_cons, List.flatMap_cons, decodeJStream6,
        roundtrip_decodeJ1_6 alloc i _ (hc i (by simp)) (hr i (by simp)),
        hrest, Option.map_some, List.map_cons]

end CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip
