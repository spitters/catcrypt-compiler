/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
import all CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip

/-!
# A decoder for the `LprogBytes` encoder, and the round trip of the logical loops

`LprogBytes.encodeLprogChecked` produces the objects the `catcrypt-mpn` crate
links. This module decodes the function bytes of such an object back to a
program and proves the round trip for the runtime-length logical loops
`mpn_and_n_loop_owned`, `mpn_xor_n_loop_owned` and `mpn_ior_n_loop_owned`.

## The decoder

`decodeLinstr` decodes one instruction off the front of a byte stream to a
`DInstr`: a `JInstr 64` over the canonical `%rN` names, a conditional branch
with its displacement, or `ret`. It calls `SailX86Decoder.decodeJ1` first and
adds the arms that decoder lacks: `ret`, `jcc rel8`, `jcc rel32`, the reg-reg
compare `39 /r`, the sign-extended-`imm8` group-1 form `83 /digit ib`, and the
register-indexed `MOV` with a SIB byte. `decodeLinstr_of_decodeJ1` and
`decodeAt_of_decodeJStream` state the agreement with `decodeJ1` and
`decodeJStream`. `decodeLprog` decodes a whole stream and replaces each branch
displacement by the index of the instruction at the target offset.

## Round trips

Each shape has a theorem `decodeLinstr (enc ++ rest) = some (x, rest)` for every
continuation `rest` (§2, §3). That form is prefix-freeness
(`decodeLinstr_prefix_free`) and makes the stream result compositional: an
`Item` list whose positions each satisfy `ItemOK` decodes to its layout
(`decodeAt_items`), and under `branchOK` to the program it denotes
(`decodeLprog_items`). `branchOK` is the well-formedness of branches: the target
label is defined, an instruction follows the definition, and the displacement
lands on the definition's byte offset. Label definitions need not be unique;
the first one is taken, as `LprogBytes.lookupLabel` does. §4 and §6b connect
item lists to `encodeLcmd`; `decodeLprog_fundef` is the statement for
`encodeLfundefBytes`.

## What the kernel evaluates

`frameSize` and `tagShiftCount` go through `String.isPrefixOf` and
`String.toNat?`, which do not reduce in the kernel. The kernel theorems of §7
take the frame size of the body and the count of the `"SHL:0"` tag as
hypotheses, transport the encoding to the body with `MOV:64` in place of the
count-0 shift (`EncEq`, `encodeFrom_congr`, `labelOffsets_congr`), and evaluate
the closed remainder with `decide +kernel`: the byte equality between the
encoder output and the item list, and `branchOK`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## 1. The decoded instruction and the one-instruction decoder -/

/-- A decoded instruction: a straight-line `JInstr 64` over the canonical `%rN`
    names, a conditional branch carrying its SDM condition nibble and the signed
    displacement from the end of the branch, or `ret`. -/
inductive DInstr where
  | op (i : JInstr 64)
  | jcc (cc : Nat) (disp : Int)
  | ret

/-- The 64-bit value an `imm8` sign-extends to. -/
def signExt8 (b : BitVec 8) : Nat := (b.signExtend 64).toNat

/-- The group-1 `/digit` of the `83 /digit ib` form: `aluImmMnemonic` extended by
    `CMP = /7`. -/
def aluImm8Mnemonic (digit : Nat) : Option (String → JOperand → JInstr 64) :=
  if digit = 7 then some JInstr.cmp else aluImmMnemonic digit

/-- The `REX`-prefixed forms `decodeRex` has no arm for: the reg-reg compare
    `39 /r`, the sign-extended-`imm8` group-1 form `83 /digit ib`, and the
    register-indexed `MOV` `8B`/`89` against `[base + index*scale]` at `mod = 00`.
    An index field of `100` without `REX.X` names no index register and a base
    field of `101` at `mod = 00` names no base register; both are rejected. -/
def decodeRexExt (r : BitVec 8) :
    List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | op :: modrm :: rest =>
      let reg := regName (rexR r * 8 + regField modrm)
      if modField modrm = 3 then
        let rm := regName (rexB r * 8 + rmField modrm)
        if op.toNat = 0x39 then some (.cmp rm (.reg reg), rest)
        else if op.toNat = 0x83 then
          match rest with
          | ib :: rest1 =>
              (aluImm8Mnemonic (regField modrm)).map
                fun mk => (mk rm (.imm (signExt8 ib)), rest1)
          | [] => none
        else none
      else if modField modrm = 0 ∧ rmField modrm = 4 then
        match rest with
        | sib :: rest1 =>
            let idx := rexX r * 8 + regField sib
            let base := rexB r * 8 + rmField sib
            let scale := 2 ^ modField sib
            if idx = 4 ∨ rmField sib = 5 then none
            else if op.toNat = 0x8b then
              some (.loadMemIdx reg (regName base) (regName idx) scale, rest1)
            else if op.toNat = 0x89 then
              some (.storeMemIdx (regName base) (regName idx) scale (.reg reg), rest1)
            else none
        | [] => none
      else none
  | _ => none

/-- Decode one instruction off the front of a byte stream. `decodeJ1` is tried
    first, so the two decoders agree wherever `decodeJ1` succeeds; the remaining
    arms are `ret` (`C3`), `jcc rel8` (`70+cc cb`), `jcc rel32` (`0F 80+cc cd`)
    and the `REX`-prefixed forms of `decodeRexExt`. -/
def decodeLinstr : List (BitVec 8) → Option (DInstr × List (BitVec 8))
  | [] => none
  | b0 :: rest =>
      match decodeJ1 (b0 :: rest) with
      | some (i, r) => some (.op i, r)
      | none =>
        if b0.toNat = 0xc3 then some (.ret, rest)
        else if 0x70 ≤ b0.toNat ∧ b0.toNat ≤ 0x7f then
          match rest with
          | d :: r => some (.jcc (b0.toNat - 0x70) (sdisp8 d), r)
          | [] => none
        else if b0.toNat = 0x0f then
          match rest with
          | o :: d0 :: d1 :: d2 :: d3 :: r =>
              if 0x80 ≤ o.toNat ∧ o.toNat ≤ 0x8f then
                some (.jcc (o.toNat - 0x80) (sdisp32 d0 d1 d2 d3), r)
              else none
          | _ => none
        else if isRex b0 then
          (decodeRexExt b0 rest).map fun p => (.op p.1, p.2)
        else none

/-- `decodeLinstr` extends `decodeJ1`: on a stream `decodeJ1` decodes, it returns the
    same instruction and the same remaining bytes. -/
theorem decodeLinstr_of_decodeJ1 {bs rest : List (BitVec 8)} {i : JInstr 64}
    (h : decodeJ1 bs = some (i, rest)) : decodeLinstr bs = some (.op i, rest) := by
  cases bs with
  | nil => simp [decodeJ1] at h
  | cons b0 t => simp only [decodeLinstr, h]

/-! ## 2. Round trips of the shapes `decodeJ1` covers, over register numbers -/

/-- The `REX.B`/`ModRM` split of a register number below 16 recomposes to it. -/
theorem bitsplit (n : Nat) (h : n < 16) : bit n 3 * 8 + (n &&& 7) = n := by
  rw [bit]; exact regsplit_id n h

/-- At `REX.W = 1` the prefix is never elided. -/
theorem rexOpt_w1 (r x b : Nat) : rexOpt 1 r x b = [BitVec.ofNat 8 (rex 1 r x b)] := rfl

/-- A reg-reg legacy ALU/`MOV` form at `REX.W = 1` decodes to the mnemonic
    `aluMnemonic` names, with `rm` the destination and `reg` the source. -/
theorem decodeLinstr_aluRR (op : Nat) (mk : String → JOperand → JInstr 64) (d s : Nat)
    (rest : List (BitVec 8)) (hd : d < 16) (hs : s < 16)
    (hop : aluTableOp op = true) (halu : aluMnemonic op = some mk) :
    decodeLinstr (encAluRRw 1 op d s ++ rest)
      = some (.op (mk (regName d) (.reg (regName s))), rest) := by
  apply decodeLinstr_of_decodeJ1
  simp only [aluTableOp, decide_eq_true_eq] at hop
  obtain ⟨hlt, h0f, hb8, h8b, h89, h81, hc7, h69, hc1, hf7⟩ := hop
  have hm : op % 2 ^ 8 = op := Nat.mod_eq_of_lt hlt
  simp only [encAluRRw, rexOpt_w1,List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, hm, if_neg h0f, if_neg hb8, if_neg h8b, if_neg h89,
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), bitsplit _ hd, bitsplit _ hs, ne_eq,
    not_true_eq_false, if_false, if_neg h81, if_neg hc7, if_neg h69, if_neg hc1,
    if_neg hf7, halu]

/-- `MOV %s, %d` (`REX.W 89 /r`, register-direct) decodes to `mov d s`. -/
theorem decodeLinstr_movRR (d s : Nat) (rest : List (BitVec 8)) (hd : d < 16) (hs : s < 16) :
    decodeLinstr (encAluRRw 1 0x89 d s ++ rest)
      = some (.op (.mov (regName d) (.reg (regName s))), rest) := by
  apply decodeLinstr_of_decodeJ1
  simp only [encAluRRw, rexOpt_w1, List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0x89 : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0x89 : Nat) % 2 ^ 8 ∧ (0x89 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0x89 : Nat) % 2 ^ 8 = 0x8b) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), bitsplit _ hd, bitsplit _ hs, if_true]

/-- `encRspMem` is the `[base + disp]` encoder at base `%rsp`. -/
theorem encRspMem_eq_memTail (op r : Nat) (off : Int) :
    encRspMem 1 op r off
      = BitVec.ofNat 8 (rex 1 (bit r 3) 0 0) :: BitVec.ofNat 8 op :: memTail r 4 off := by
  simp only [encRspMem, rexOpt_w1, memTail]
  split_ifs <;> simp_all

/-- `MOV off(%rsp), %r` decodes to a `loadMem` off `%rsp`. -/
theorem decodeLinstr_rspLoad (r : Nat) (off : Int) (rest : List (BitVec 8))
    (hr : r < 16) (h : dispOk32 off = true) :
    decodeLinstr (encRspMem 1 0x8b r off ++ rest)
      = some (.op (.loadMem (regName r) "%rsp" off), rest) := by
  apply decodeLinstr_of_decodeJ1
  simp only [encRspMem_eq_memTail, List.cons_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (Nat.zero_le 1),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0x8b : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0x8b : Nat) % 2 ^ 8 ∧ (0x8b : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    decodeMemTail_memTail32 _ _ _ _ h,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (Nat.zero_le 1),
    rexB_rex _ _ _ (Nat.zero_le 1), bitsplit _ hr, if_true]
  rfl

/-- `MOV %r, off(%rsp)` decodes to a `storeMem` off `%rsp`. -/
theorem decodeLinstr_rspStore (r : Nat) (off : Int) (rest : List (BitVec 8))
    (hr : r < 16) (h : dispOk32 off = true) :
    decodeLinstr (encRspMem 1 0x89 r off ++ rest)
      = some (.op (.storeMem "%rsp" off (.reg (regName r))), rest) := by
  apply decodeLinstr_of_decodeJ1
  obtain ⟨m, ts, hm, hmod⟩ := memTail_head r 4 off
  have hdec := decodeMemTail_memTail32 r 4 off rest h
  rw [hm, List.cons_append] at hdec
  simp only [encRspMem_eq_memTail, List.cons_append, hm,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (Nat.zero_le 1),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0x89 : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0x89 : Nat) % 2 ^ 8 ∧ (0x89 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0x89 : Nat) % 2 ^ 8 = 0x8b) by decide),
    if_neg hmod, hdec,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (Nat.zero_le 1),
    rexB_rex _ _ _ (Nat.zero_le 1), bitsplit _ hr, if_true]
  rfl

/-- The frame `leaq disp(%rsp), %rsp` is the `[base + disp]` `LEA` at base and
    destination `%rsp`, for a nonzero displacement. -/
theorem encLeaRspFrame_eq_memTail (disp : Int) (h0 : disp ≠ 0) :
    encLeaRspFrame disp
      = BitVec.ofNat 8 (rex 1 (bit 4 3) 0 (bit 4 3)) :: BitVec.ofNat 8 0x8d
          :: memTail 4 4 disp := by
  simp only [encLeaRspFrame, memTail]
  split_ifs <;> simp_all <;> decide

/-- The frame `leaq disp(%rsp), %rsp` decodes to the index-free `lea` on `%rsp`. -/
theorem decodeLinstr_leaRsp (disp : Int) (rest : List (BitVec 8))
    (h0 : disp ≠ 0) (h : dispOk32 disp = true) :
    decodeLinstr (encLeaRspFrame disp ++ rest)
      = some (.op (.lea "%rsp" "%rsp" "%rsp" 0 disp), rest) := by
  apply decodeLinstr_of_decodeJ1
  obtain ⟨m, ts, hm, hmod⟩ := memTail_head 4 4 disp
  have hdec := decodeMemTail_memTail32 4 4 disp rest h
  rw [hm, List.cons_append] at hdec
  simp only [encLeaRspFrame_eq_memTail disp h0, List.cons_append, hm,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0x8d : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0x8d : Nat) % 2 ^ 8 ∧ (0x8d : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0x8d : Nat) % 2 ^ 8 = 0x8b) by decide),
    if_neg (show ¬((0x8d : Nat) % 2 ^ 8 = 0x89) by decide),
    ne_eq, hmod, not_false_eq_true, if_pos, hdec,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _)]
  rfl

/-- `MOV $imm32, %d` (`REX.W C7 /0 id`) decodes to a `mov` of the immediate. -/
theorem decodeLinstr_movImm (d v : Nat) (rest : List (BitVec 8))
    (hd : d < 16) (hv : v < 2 ^ 32) :
    decodeLinstr (encMovImmw 1 d v ++ rest)
      = some (.op (.mov (regName d) (.imm v)), rest) := by
  apply decodeLinstr_of_decodeJ1
  simp only [encMovImmw, if_neg (show ¬((1 : Nat) = 0) by decide),
    rexOpt_w1, imm32LE, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x0f) by decide),
    if_neg (show ¬(0xb8 ≤ (0xc7 : Nat) % 2 ^ 8 ∧ (0xc7 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x8b) by decide),
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x89) by decide),
    if_neg (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x81) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), bitsplit _ hd, ne_eq, not_true_eq_false,
    if_false, if_true, show (0 : Nat) &&& 7 = 0 by decide,
    imm32_recompose_mod v hv]

/-! ## 3. Round trips of the shapes outside `decodeJ1` -/

/-- A `REX.W` stream `decodeRex` rejects is routed to `decodeRexExt`. -/
theorem decodeLinstr_rex_of_none (r x b : Nat) (hr : r ≤ 1) (hx : x ≤ 1) (hb : b ≤ 1)
    (rest : List (BitVec 8))
    (hnone : decodeRex (BitVec.ofNat 8 (rex 1 r x b)) rest = none) :
    decodeLinstr (BitVec.ofNat 8 (rex 1 r x b) :: rest)
      = (decodeRexExt (BitVec.ofNat 8 (rex 1 r x b)) rest).map fun p => (.op p.1, p.2) := by
  have hc3 : ¬ ((BitVec.ofNat 8 (rex 1 r x b)).toNat = 0xc3) := by
    rw [BitVec.toNat_ofNat]; unfold rex; omega
  have h7 : ¬ (0x70 ≤ (BitVec.ofNat 8 (rex 1 r x b)).toNat
      ∧ (BitVec.ofNat 8 (rex 1 r x b)).toNat ≤ 0x7f) := by
    rw [BitVec.toNat_ofNat]; unfold rex; omega
  have h0f : ¬ ((BitVec.ofNat 8 (rex 1 r x b)).toNat = 0x0f) := by
    rw [BitVec.toNat_ofNat]; unfold rex; omega
  simp only [decodeLinstr, decodeJ1_rex _ _ _ hr hx hb, hnone, if_neg hc3, if_neg h7,
    if_neg h0f, isRex_rex _ _ _ hr hx hb, if_true]

/-- The reg-reg compare `CMP %s, %d` (`REX.W 39 /r`) decodes to `cmp d s`. -/
theorem decodeLinstr_cmpRR (d s : Nat) (rest : List (BitVec 8)) (hd : d < 16) (hs : s < 16) :
    decodeLinstr (encAluRRw 1 0x39 d s ++ rest)
      = some (.op (.cmp (regName d) (.reg (regName s))), rest) := by
  have hnone : decodeRex (BitVec.ofNat 8 (rex 1 (bit s 3) 0 (bit d 3)))
      (BitVec.ofNat 8 0x39 :: BitVec.ofNat 8 (modRMReg s d) :: rest) = none := by
    simp [decodeRex, modField_modRMReg, aluMnemonic]
  simp only [encAluRRw, rexOpt_w1, List.cons_append, List.nil_append,
    decodeLinstr_rex_of_none _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _) _ hnone,
    decodeRexExt, modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    BitVec.toNat_ofNat,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), bitsplit _ hd, bitsplit _ hs, if_true]
  rfl

/-- Sign-extending the `imm8` byte of a value the short group-1 form admits at
    `REX.W = 1` recovers the value. -/
theorem signExt8_imm8 (v : Nat) (h : fitsImm8S 1 v = true) :
    signExt8 (BitVec.ofNat 8 (v &&& 0xff)) = v := by
  simp only [fitsImm8S, if_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [signExt8, BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.msb_eq_decide, decide_eq_true_eq, show (0xff : Nat) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  rcases h with h | h <;> split <;> omega

/-- The sign-extended-`imm8` group-1 form `op $imm8, %d` (`REX.W 83 /digit ib`)
    decodes to the mnemonic its digit names, with the immediate sign-extended to
    64 bits. -/
theorem decodeLinstr_aluImm8 (digit : Nat) (mk : String → JOperand → JInstr 64) (d v : Nat)
    (rest : List (BitVec 8)) (hdig : digit < 8) (hd : d < 16)
    (hv : fitsImm8S 1 v = true) (halu : aluImm8Mnemonic digit = some mk) :
    decodeLinstr (encAluImm8 1 digit d v ++ rest)
      = some (.op (mk (regName d) (.imm v)), rest) := by
  have hd7 : digit &&& 7 = digit := by
    rw [Nat.and_two_pow_sub_one_eq_mod digit 3]; omega
  have hnone : decodeRex (BitVec.ofNat 8 (rex 1 0 0 (bit d 3)))
      (BitVec.ofNat 8 0x83 :: BitVec.ofNat 8 (modRMReg digit d)
        :: BitVec.ofNat 8 (v &&& 0xff) :: rest) = none := by
    simp [decodeRex, modField_modRMReg, aluMnemonic]
  simp only [encAluImm8, rexOpt_w1, List.cons_append, List.nil_append,
    decodeLinstr_rex_of_none _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _) _ hnone,
    decodeRexExt, modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    BitVec.toNat_ofNat, hd7, halu,
    rexB_rex _ _ _ (bit_le_one _ _), bitsplit _ hd, if_true, signExt8_imm8 v hv]
  rfl

/-- `REX.X` of a `REX.W` prefix. -/
theorem rexX_rex (r x b : Nat) (hr : r ≤ 1) (hx : x ≤ 1) (hb : b ≤ 1) :
    rexX (BitVec.ofNat 8 (rex 1 r x b)) = x := by
  interval_cases r <;> interval_cases x <;> interval_cases b <;> rfl

/-- The scale-8 SIB byte has the layout of a `mod = 11` ModRM byte. -/
theorem sibByte8_eq (idx base : Nat) : sibByte 8 idx base = modRMMem 3 idx base := rfl

/-- The `mod = 00`, `r/m = 100` ModRM byte of a SIB operand. -/
theorem sibModRM_eq (r : Nat) : 0 * 64 + ((r &&& 7) * 8) + 4 = modRMMem 0 r 4 := rfl

/-- The scale-8 SIB byte is not the index-free `%rsp` SIB `0x24`. -/
theorem sibByte8_ne_0x24 (idx base : Nat) : ¬ (modRMMem 3 idx base % 256 = 36) := by
  have hi : idx &&& 7 ≤ 7 := Nat.and_le_right
  have hb : base &&& 7 ≤ 7 := Nat.and_le_right
  unfold modRMMem; omega

/-- The stride-8 register-indexed load `MOV (%base,%idx,8), %r` (`REX.W 8B /r`
    with a SIB byte) decodes to `loadMemIdx`. -/
theorem decodeLinstr_loadIdx8 (r base idx : Nat) (rest : List (BitVec 8))
    (hr : r < 16) (hbase : base < 16) (hidx : idx < 16)
    (hb5 : base &&& 7 ≠ 5) (hi4 : idx ≠ 4) :
    decodeLinstr (encMemMovSibw 1 0x8b r base idx 8 ++ rest)
      = some (.op (.loadMemIdx (regName r) (regName base) (regName idx) 8), rest) := by
  have hnone : decodeRex (BitVec.ofNat 8 (rex 1 (bit r 3) (bit idx 3) (bit base 3)))
      (BitVec.ofNat 8 0x8b :: BitVec.ofNat 8 (modRMMem 0 r 4)
        :: BitVec.ofNat 8 (modRMMem 3 idx base) :: rest) = none := by
    simp [decodeRex, decodeMemTail, modField_modRMMem, rmField_modRMMem,
      sibByte8_ne_0x24]
  simp only [encMemMovSibw, sibTail, rexOpt_w1, sibByte8_eq, sibModRM_eq,
    List.cons_append, List.nil_append, ite_false,
    decodeLinstr_rex_of_none _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _) _ hnone,
    decodeRexExt, modField_modRMMem _ _ _ (by decide : 0 < 4),
    modField_modRMMem _ _ _ (by decide : 3 < 4), regField_modRMMem, rmField_modRMMem,
    BitVec.toNat_ofNat,
    rexR_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
    rexX_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), bitsplit _ hr, bitsplit _ hbase, bitsplit _ hidx,
    hb5, hi4, or_self, if_true]
  rfl

/-- The stride-8 register-indexed store `MOV %r, (%base,%idx,8)` (`REX.W 89 /r`
    with a SIB byte) decodes to `storeMemIdx`. -/
theorem decodeLinstr_storeIdx8 (r base idx : Nat) (rest : List (BitVec 8))
    (hr : r < 16) (hbase : base < 16) (hidx : idx < 16)
    (hb5 : base &&& 7 ≠ 5) (hi4 : idx ≠ 4) :
    decodeLinstr (encMemMovSibw 1 0x89 r base idx 8 ++ rest)
      = some (.op (.storeMemIdx (regName base) (regName idx) 8 (.reg (regName r))), rest) := by
  have hnone : decodeRex (BitVec.ofNat 8 (rex 1 (bit r 3) (bit idx 3) (bit base 3)))
      (BitVec.ofNat 8 0x89 :: BitVec.ofNat 8 (modRMMem 0 r 4)
        :: BitVec.ofNat 8 (modRMMem 3 idx base) :: rest) = none := by
    simp [decodeRex, decodeMemTail, modField_modRMMem, rmField_modRMMem,
      sibByte8_ne_0x24]
  simp only [encMemMovSibw, sibTail, rexOpt_w1, sibByte8_eq, sibModRM_eq,
    List.cons_append, List.nil_append, ite_false,
    decodeLinstr_rex_of_none _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _) _ hnone,
    decodeRexExt, modField_modRMMem _ _ _ (by decide : 0 < 4),
    modField_modRMMem _ _ _ (by decide : 3 < 4), regField_modRMMem, rmField_modRMMem,
    BitVec.toNat_ofNat,
    rexR_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
    rexX_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), bitsplit _ hr, bitsplit _ hbase, bitsplit _ hidx,
    hb5, hi4, or_self, if_true]
  rfl

/-- The condition nibble a condition-code name encodes to. -/
def ccNibble (cc : String) : Nat := jccOpcode cc - 0x80

theorem ccNibble_le (cc : String) : ccNibble cc ≤ 15 := by
  have := jccOpcode_range cc; unfold ccNibble; omega

/-- `jcc rel8` (`70+cc cb`) decodes to the branch with its condition nibble and
    displacement. -/
theorem decodeLinstr_jcc8 (cc : String) (d : Int) (rest : List (BitVec 8))
    (h : dispOk d = true) :
    decodeLinstr (encJcc8 cc d ++ rest) = some (.jcc (ccNibble cc) d, rest) := by
  have hk := ccNibble_le cc
  have hb : (BitVec.ofNat 8 (0x70 + (jccOpcode cc - 0x80))).toNat = 0x70 + ccNibble cc := by
    rw [BitVec.toNat_ofNat]; unfold ccNibble at *; omega
  simp only [encJcc8, List.cons_append, List.nil_append, decodeLinstr, decodeJ1, isRex, hb,
    sdisp8_disp8 d h]
  have e1 : ¬ (0x70 + ccNibble cc = 0x66) := by omega
  have e2 : ¬ (0x70 + ccNibble cc = 0xf3) := by omega
  have e3 : ¬ (0x70 + ccNibble cc = 0xc4) := by omega
  have e4 : ¬ (0x70 + ccNibble cc = 0xc3) := by omega
  have e5 : (0x70 ≤ 0x70 + ccNibble cc ∧ 0x70 + ccNibble cc ≤ 0x7f) := by omega
  have e6 : ¬ (0x40 ≤ 0x70 + ccNibble cc ∧ 0x70 + ccNibble cc ≤ 0x4f) := by omega
  have e7 : ¬ (0x70 + ccNibble cc = 0x0f) := by omega
  simp [e1, e2, e3, e4, e5, e6, e7]

/-- The `0F` escape followed by five bytes, the second of which is not the `SETB`
    opcode `92`, is read as a `jcc rel32`. -/
theorem decodeLinstr_0f (o d0 d1 d2 d3 : BitVec 8) (r : List (BitVec 8)) (ho : o.toNat ≠ 0x92) :
    decodeLinstr (BitVec.ofNat 8 0x0f :: o :: d0 :: d1 :: d2 :: d3 :: r)
      = if 0x80 ≤ o.toNat ∧ o.toNat ≤ 0x8f then
          some (.jcc (o.toNat - 0x80) (sdisp32 d0 d1 d2 d3), r)
        else none := by
  have h : decodeJ1 (BitVec.ofNat 8 0x0f :: o :: d0 :: d1 :: d2 :: d3 :: r) = none := by
    show decodeSetcBare (o :: d0 :: d1 :: d2 :: d3 :: r) = none
    simp [decodeSetcBare, ho]
  simp only [decodeLinstr, h]
  all_goals rfl

/-- The value a `rel32` field carries for a displacement: its signed 32-bit
    wrap, the displacement itself in range. -/
def wrap32 (d : Int) : Int := (BitVec.ofInt 32 d).toInt

theorem wrap32_of_dispOk32 (d : Int) (h : dispOk32 d = true) : wrap32 d = d := by
  simp only [dispOk32, decide_eq_true_eq] at h
  simp only [wrap32, BitVec.toInt_ofInt, Int.bmod_def]
  split <;> omega

/-- The four little-endian bytes of a 32-bit value read back as its signed value. -/
theorem sdisp32_imm32LE (v : Nat) (hv : v < 2 ^ 32) :
    sdisp32 (BitVec.ofNat 8 (v &&& 0xff)) (BitVec.ofNat 8 ((v >>> 8) &&& 0xff))
        (BitVec.ofNat 8 ((v >>> 16) &&& 0xff)) (BitVec.ofNat 8 ((v >>> 24) &&& 0xff))
      = (BitVec.ofNat 32 v).toInt := by
  simp only [sdisp32, BitVec.toNat_ofNat, imm32_recompose_mod v hv]

/-- `jcc rel32` (`0F 80+cc cd`) decodes to the branch with its condition nibble
    and the 32-bit wrap of its displacement. -/
theorem decodeLinstr_jcc32_wrap (cc : String) (d : Int) (rest : List (BitVec 8)) :
    decodeLinstr (encJcc32 cc d ++ rest) = some (.jcc (ccNibble cc) (wrap32 d), rest) := by
  have hr := jccOpcode_range cc
  have hb : (BitVec.ofNat 8 (jccOpcode cc)).toNat = jccOpcode cc := by
    rw [BitVec.toNat_ofNat]; omega
  simp only [encJcc32, disp32LE, imm32LE, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  rw [decodeLinstr_0f _ _ _ _ _ _ (by rw [hb]; omega), hb, if_pos hr, sdisp32_imm32LE _ (BitVec.isLt (BitVec.ofInt 32 d)),
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `jcc rel32` decodes to the branch with its displacement, in range. -/
theorem decodeLinstr_jcc32 (cc : String) (d : Int) (rest : List (BitVec 8))
    (h : dispOk32 d = true) :
    decodeLinstr (encJcc32 cc d ++ rest) = some (.jcc (ccNibble cc) d, rest) := by
  rw [decodeLinstr_jcc32_wrap, wrap32_of_dispOk32 d h]

/-- `ret` (`C3`) decodes to `ret`. -/
theorem decodeLinstr_ret (rest : List (BitVec 8)) :
    decodeLinstr (LeafBytes.encRet ++ rest) = some (.ret, rest) := by
  rfl

/-! ## 4. The body encoder as a recursion -/

/-- The parameters `encodeLcmd` fixes for a whole body: frame size, body-uniform
    spill width, qsave block size, and the relaxed label-offset table. -/
structure Params where
  frame : Nat
  spillW : Nat
  qsaveB : Nat
  tbl : List (LLabel × Nat)

/-- The parameters `encodeLcmd` computes from a body. -/
def Params.ofBody (body : Lcmd) : Params :=
  let frame := frameSize body
  let spillW := if bodyIsU64 body then 64 else 32
  let qsaveB := qsaveBytesFor body
  { frame := frame, spillW := spillW, qsaveB := qsaveB,
    tbl := labelOffsets frame spillW body qsaveB }

/-- The byte length `encodeLcmd` assigns the instruction at offset `off`. -/
def Params.lenAt (P : Params) (off : Nat) (i : LinstrR) : Nat :=
  instrLenAt P.frame P.spillW
    (fun l => Int.ofNat (lookupLabel P.tbl l)
      - Int.ofNat (off + instrLenAt P.frame P.spillW (fun _ => 0) i P.qsaveB)) i P.qsaveB

/-- The displacement resolver `encodeLcmd` uses for the instruction at offset
    `off`: label offset minus the end of the instruction. -/
def Params.dispAt (P : Params) (off : Nat) (i : LinstrR) : LLabel → Int :=
  fun l => Int.ofNat (lookupLabel P.tbl l) - Int.ofNat (off + P.lenAt off i)

/-- The bytes of the instruction at offset `off`. -/
def Params.encAt (P : Params) (off : Nat) (i : LinstrR) : List (BitVec 8) :=
  encodeLinstrR P.frame P.spillW (P.dispAt off i) i P.qsaveB

/-- `encodeLcmd`'s fold as a recursion from a starting offset. -/
def encodeFrom (P : Params) : Nat → Lcmd → List (BitVec 8)
  | _, [] => []
  | off, instr :: rest =>
      P.encAt off instr.li_i ++ encodeFrom P (off + P.lenAt off instr.li_i) rest

theorem encodeLcmd_fold_eq (P : Params) :
    ∀ (body : Lcmd) (off : Nat) (acc : List (BitVec 8)),
      ((body.foldl (fun (a : Nat × List (BitVec 8)) instr =>
          let (off, bytes) := a
          let i := instr.li_i
          let dispLong : LLabel → Int := fun l =>
            Int.ofNat (lookupLabel P.tbl l)
              - Int.ofNat (off + instrLenAt P.frame P.spillW (fun _ => 0) i P.qsaveB)
          let len := instrLenAt P.frame P.spillW dispLong i P.qsaveB
          let instrEnd := off + len
          let dispOf : LLabel → Int := fun l =>
            Int.ofNat (lookupLabel P.tbl l) - Int.ofNat instrEnd
          (instrEnd, bytes ++ encodeLinstrR P.frame P.spillW dispOf i P.qsaveB))
            (off, acc)).2) = acc ++ encodeFrom P off body := by
  intro body
  induction body with
  | nil => intro off acc; simp [encodeFrom]
  | cons instr rest ih =>
    intro off acc
    rw [List.foldl_cons, ih, encodeFrom, List.append_assoc]
    rfl

/-- `encodeLcmd` is `encodeFrom` at offset `0` under the body's own parameters. -/
theorem encodeLcmd_eq_encodeFrom (body : Lcmd) :
    encodeLcmd body = encodeFrom (Params.ofBody body) 0 body := by
  have h := encodeLcmd_fold_eq (Params.ofBody body) body 0 []
  simpa [encodeLcmd, Params.ofBody] using h

/-! ## 5. Assembled items and the stream decoder

An `Item` is one position of an assembled program: its bytes, the instruction
they decode to (none for a position that carries no bytes), the label the
position defines, and the label a branch at the position targets. Offsets are
prefix sums of the items' byte lengths, so the results of this section do not
depend on how the encoder chose its displacements. -/

/-- One position of an assembled program. -/
structure Item where
  bytes : List (BitVec 8)
  dec : Option DInstr
  label : Option LLabel := none
  target : Option LLabel := none

/-- A position without bytes decodes to nothing; a position with bytes decodes,
    in front of any continuation, to its instruction and that continuation. -/
def ItemOK (it : Item) : Prop :=
  match it.dec with
  | none => it.bytes = []
  | some x => it.bytes ≠ [] ∧ ∀ rest, decodeLinstr (it.bytes ++ rest) = some (x, rest)

/-- A position whose bytes decode to its instruction carries bytes. -/
theorem ItemOK_of_decode {bytes : List (BitVec 8)} {x : DInstr}
    {l t : Option LLabel}
    (h : ∀ rest, decodeLinstr (bytes ++ rest) = some (x, rest)) :
    ItemOK ⟨bytes, some x, l, t⟩ := by
  refine ⟨fun hb => ?_, h⟩
  have h0 := h []
  simp only [show bytes = [] from hb, List.append_nil] at h0
  exact absurd h0 (by simp [decodeLinstr])

/-- The byte stream of an item list. -/
def itemBytes (items : List Item) : List (BitVec 8) := items.flatMap (·.bytes)

/-- The decoded instructions of an item list with their start and end offsets. -/
def layoutAt : Nat → List Item → List (Nat × Nat × DInstr)
  | _, [] => []
  | off, it :: rest =>
      match it.dec with
      | none => layoutAt (off + it.bytes.length) rest
      | some x => (off, off + it.bytes.length, x) :: layoutAt (off + it.bytes.length) rest

/-- Decode a whole stream into instructions tagged with their start and end
    offsets; the fuel bounds the instruction count. -/
def decodeAt : Nat → Nat → List (BitVec 8) → Option (List (Nat × Nat × DInstr))
  | 0, _, bs => if bs.isEmpty then some [] else none
  | n + 1, off, bs =>
      if bs.isEmpty then some []
      else
        match decodeLinstr bs with
        | some (x, r) =>
            (decodeAt n (off + (bs.length - r.length)) r).map
              ((off, off + (bs.length - r.length), x) :: ·)
        | none => none

/-- **Prefix-freeness.** Two byte strings that each decode, in front of every
    continuation, to one instruction and that continuation are equal as soon as
    one is a prefix of the other's stream; the instructions and continuations
    agree too. -/
theorem decodeLinstr_prefix_free {e₁ e₂ r₁ r₂ : List (BitVec 8)} {x₁ x₂ : DInstr}
    (h₁ : ∀ rest, decodeLinstr (e₁ ++ rest) = some (x₁, rest))
    (h₂ : ∀ rest, decodeLinstr (e₂ ++ rest) = some (x₂, rest))
    (h : e₁ ++ r₁ = e₂ ++ r₂) : e₁ = e₂ ∧ x₁ = x₂ ∧ r₁ = r₂ := by
  have h3 := h₁ r₁
  rw [h, h₂ r₂] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨hx, hr⟩ := h3
  subst hr
  exact ⟨List.append_cancel_right h, hx.symm, rfl⟩

theorem decodeAt_nil (n off : Nat) : decodeAt n off [] = some [] := by
  cases n <;> rfl

/-- The stream of an item list decodes to its layout. -/
theorem decodeAt_items (items : List Item) (hok : ∀ it ∈ items, ItemOK it) :
    ∀ n off, (layoutAt off items).length ≤ n →
      decodeAt n off (itemBytes items) = some (layoutAt off items) := by
  induction items with
  | nil => intro n off _; exact decodeAt_nil n off
  | cons it rest ih =>
    intro n off hn
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold ItemOK at hit
    cases hdec : it.dec with
    | none =>
      rw [hdec] at hit
      simp only [layoutAt, hdec, hit, List.length_nil, Nat.add_zero] at hn ⊢
      simpa [itemBytes, hit] using ih' n off hn
    | some x =>
      rw [hdec] at hit
      obtain ⟨hne, hdecode⟩ := hit
      simp only [layoutAt, hdec, List.length_cons] at hn ⊢
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hbs : itemBytes (it :: rest) = it.bytes ++ itemBytes rest := by
        simp [itemBytes]
      have hemp : (it.bytes ++ itemBytes rest).isEmpty = false := by
        cases hb : it.bytes with
        | nil => exact absurd hb hne
        | cons b t => rfl
      have hlen : (it.bytes ++ itemBytes rest).length - (itemBytes rest).length
          = it.bytes.length := by
        rw [List.length_append]; omega
      rw [hbs, decodeAt, hemp]
      simp only [Bool.false_eq_true, if_false, hdecode, hlen]
      rw [ih' m (off + it.bytes.length) (by omega)]
      rfl

/-- **Agreement with the straight-line decoder.** A stream `decodeJStream`
    decodes is decoded by `decodeAt` to the same instructions. -/
theorem decodeAt_of_decodeJStream :
    ∀ (n off : Nat) (bs : List (BitVec 8)) (c : List (JInstr 64)),
      decodeJStream n bs = some c →
        (decodeAt n off bs).map (List.map (·.2.2)) = some (c.map DInstr.op) := by
  intro n
  induction n with
  | zero =>
    intro off bs c h
    simp only [decodeJStream] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      simp [decodeAt, he]
    · exact absurd h (by simp)
  | succ n ih =>
    intro off bs c h
    simp only [decodeJStream] at h
    cases hj : decodeJ1 bs with
    | none => rw [hj] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨i, rest⟩ := p
      simp only [hj] at h
      cases hr : decodeJStream n rest with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some c' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have hne : bs.isEmpty = false := by
          cases bs with
          | nil => simp [decodeJ1] at hj
          | cons b t => rfl
        have ih' := ih (off + (bs.length - rest.length)) rest c' hr
        cases hd : decodeAt n (off + (bs.length - rest.length)) rest with
        | none => rw [hd] at ih'; exact absurd ih' (by simp)
        | some xs =>
          rw [hd] at ih'
          simp only [Option.map_some, Option.some.injEq] at ih'
          simp [decodeAt, hne, decodeLinstr_of_decodeJ1 hj, hd, ih']

/-! ## 6. Branch resolution -/

/-- A decoded program instruction: a branch carries the index of its target
    instruction. -/
inductive RInstr where
  | op (i : JInstr 64)
  | jcc (cc : Nat) (target : Nat)
  | ret

/-- Replace each branch displacement by the index of the instruction that
    starts at the target offset. -/
def resolveAll (xs : List (Nat × Nat × DInstr)) :
    List (Nat × Nat × DInstr) → Option (List RInstr)
  | [] => some []
  | (_, e, x) :: rest =>
      match x with
      | .op i => (resolveAll xs rest).map (.op i :: ·)
      | .ret => (resolveAll xs rest).map (.ret :: ·)
      | .jcc cc d =>
          match xs.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) with
          | some j => (resolveAll xs rest).map (.jcc cc j :: ·)
          | none => none

/-- Decode a byte stream to a program with index-resolved branches. -/
def decodeLprog (bs : List (BitVec 8)) : Option (List RInstr) :=
  (decodeAt bs.length 0 bs).bind fun xs => resolveAll xs xs

/-- The number of decoded instructions of an item list. -/
def decCount : List Item → Nat
  | [] => 0
  | it :: rest => (if it.dec.isSome then 1 else 0) + decCount rest

/-- The position of the first definition of label `l`: the index of the next
    decoded instruction and the byte offset, counted from `j` and `off`. -/
def labelPos (l : LLabel) : Nat → Nat → List Item → Option (Nat × Nat)
  | _, _, [] => none
  | j, off, it :: rest =>
      if it.label = some l then some (j, off)
      else labelPos l (if it.dec.isSome then j + 1 else j) (off + it.bytes.length) rest

/-- The program an item list denotes: each branch carries the index of the
    instruction following its target label's definition. -/
def expectedFrom (all : List Item) : List Item → Option (List RInstr)
  | [] => some []
  | it :: rest =>
      match it.dec with
      | none => expectedFrom all rest
      | some (.op i) => (expectedFrom all rest).map (.op i :: ·)
      | some .ret => (expectedFrom all rest).map (.ret :: ·)
      | some (.jcc cc _) =>
          match it.target.bind (fun l => labelPos l 0 0 all) with
          | some (j, _) => (expectedFrom all rest).map (.jcc cc j :: ·)
          | none => none

/-- Well-formedness of the branches of `items`, laid out from offset `off` inside
    `all`: every branch names a label that `all` defines, an instruction follows
    that definition, and the branch displacement added to the end of the branch
    is the byte offset of the definition. -/
def branchOK (all : List Item) : Nat → List Item → Bool
  | _, [] => true
  | off, it :: rest =>
      (match it.dec with
        | some (.jcc _ d) =>
            match it.target.bind (fun l => labelPos l 0 0 all) with
            | some (j, t) =>
                decide ((t : Int) = ((off + it.bytes.length : Nat) : Int) + d)
                  && decide (j < decCount all)
            | none => false
        | _ => true)
      && branchOK all (off + it.bytes.length) rest

theorem layoutAt_length (items : List Item) :
    ∀ off, (layoutAt off items).length = decCount items := by
  induction items with
  | nil => intro off; rfl
  | cons it rest ih =>
    intro off
    cases hdec : it.dec with
    | none => simp [layoutAt, decCount, hdec, ih]
    | some x => simp [layoutAt, decCount, hdec, ih]; omega

theorem layoutAt_start_ge (items : List Item) :
    ∀ off y, y ∈ layoutAt off items → off ≤ y.1 := by
  induction items with
  | nil => intro off y hy; simp [layoutAt] at hy
  | cons it rest ih =>
    intro off y hy
    cases hdec : it.dec with
    | none =>
      simp only [layoutAt, hdec] at hy
      have := ih _ y hy; omega
    | some x =>
      simp only [layoutAt, hdec, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_refl _
      · have := ih _ y hy; omega

theorem layoutAt_pairwise (items : List Item) (hok : ∀ it ∈ items, ItemOK it) :
    ∀ off, (layoutAt off items).Pairwise (fun a b => a.1 < b.1) := by
  induction items with
  | nil => intro off; simp [layoutAt]
  | cons it rest ih =>
    intro off
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold ItemOK at hit
    cases hdec : it.dec with
    | none => simpa [layoutAt, hdec] using ih' _
    | some x =>
      rw [hdec] at hit
      have hpos : 0 < it.bytes.length := List.length_pos_iff.mpr hit.1
      simp only [layoutAt, hdec, List.pairwise_cons]
      refine ⟨fun y hy => ?_, ih' _⟩
      have := layoutAt_start_ge rest _ y hy
      show off < y.1
      omega

theorem layoutAt_head_start (items : List Item) (hok : ∀ it ∈ items, ItemOK it) :
    ∀ off y, (layoutAt off items)[0]? = some y → y.1 = off := by
  induction items with
  | nil => intro off y hy; simp [layoutAt] at hy
  | cons it rest ih =>
    intro off y hy
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold ItemOK at hit
    cases hdec : it.dec with
    | none =>
      rw [hdec] at hit
      simp only [layoutAt, hdec, hit, List.length_nil, Nat.add_zero] at hy
      exact ih' off y hy
    | some x =>
      simp only [layoutAt, hdec, List.getElem?_cons_zero, Option.some.injEq] at hy
      rw [← hy]

theorem layoutAt_labelPos (l : LLabel) (items : List Item)
    (hok : ∀ it ∈ items, ItemOK it) :
    ∀ j0 off0 j t, labelPos l j0 off0 items = some (j, t) →
      j0 ≤ j ∧ ∀ y, (layoutAt off0 items)[j - j0]? = some y → y.1 = t := by
  induction items with
  | nil => intro j0 off0 j t h; simp [labelPos] at h
  | cons it rest ih =>
    intro j0 off0 j t h
    have hit := hok it List.mem_cons_self
    have hrest : ∀ j ∈ rest, ItemOK j := fun j hj => hok j (List.mem_cons_of_mem _ hj)
    have ih' := ih hrest
    simp only [labelPos] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Nat.le_refl _, fun y hy => ?_⟩
      rw [Nat.sub_self] at hy
      exact layoutAt_head_start (it :: rest) hok _ y hy
    · unfold ItemOK at hit
      cases hdec : it.dec with
      | none =>
        rw [hdec] at hit
        simp only [hdec, Option.isSome_none, Bool.false_eq_true, if_false, hit,
          List.length_nil, Nat.add_zero] at h
        obtain ⟨hle, hy⟩ := ih' j0 off0 j t h
        refine ⟨hle, fun y hyy => hy y ?_⟩
        simpa [layoutAt, hdec, hit] using hyy
      | some x =>
        simp only [hdec, Option.isSome_some, if_true] at h
        obtain ⟨hle, hy⟩ := ih' (j0 + 1) _ j t h
        refine ⟨by omega, fun y hyy => hy y ?_⟩
        have hj : j - j0 = (j - (j0 + 1)) + 1 := by omega
        simpa [layoutAt, hdec, hj] using hyy

theorem findIdx?_of_pairwise (xs : List (Nat × Nat × DInstr))
    (hp : xs.Pairwise (fun a b => a.1 < b.1)) :
    ∀ k y, xs[k]? = some y →
      xs.findIdx? (fun z => decide ((z.1 : Int) = (y.1 : Int))) = some k := by
  induction xs with
  | nil => intro k y h; simp at h
  | cons a t ih =>
    intro k y h
    rw [List.pairwise_cons] at hp
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [List.findIdx?_cons]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hmem : y ∈ t := List.mem_of_getElem? h
      have hlt := hp.1 y hmem
      have hne : ¬ ((a.1 : Int) = (y.1 : Int)) := by omega
      rw [List.findIdx?_cons]
      simp only [hne, decide_false, Bool.false_eq_true, if_false, ih hp.2 k y h,
        Option.map_some]

/-- Resolving the layout of `items` inside `all` yields the program `items`
    denotes. -/
theorem resolveAll_layout (all : List Item) (hok : ∀ it ∈ all, ItemOK it) :
    ∀ items off, branchOK all off items = true →
      resolveAll (layoutAt 0 all) (layoutAt off items) = expectedFrom all items := by
  intro items
  induction items with
  | nil => intro off _; rfl
  | cons it rest ih =>
    intro off hbr
    simp only [branchOK, Bool.and_eq_true] at hbr
    obtain ⟨hhead, htail⟩ := hbr
    have ih' := ih _ htail
    cases hdec : it.dec with
    | none => simpa [layoutAt, expectedFrom, hdec] using ih'
    | some x =>
      cases x with
      | op i => simp [layoutAt, expectedFrom, hdec, resolveAll, ih']
      | ret => simp [layoutAt, expectedFrom, hdec, resolveAll, ih']
      | jcc cc d =>
        rw [hdec] at hhead
        simp only at hhead
        cases htgt : it.target.bind (fun l => labelPos l 0 0 all) with
        | none => rw [htgt] at hhead; simp at hhead
        | some p =>
          obtain ⟨j, t⟩ := p
          rw [htgt] at hhead
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hhead
          obtain ⟨ht, hj⟩ := hhead
          obtain ⟨l, _, hl⟩ :
              ∃ l, it.target = some l ∧ labelPos l 0 0 all = some (j, t) := by
            cases htg : it.target with
            | none => rw [htg] at htgt; simp at htgt
            | some l => exact ⟨l, rfl, by simpa [htg] using htgt⟩
          have hlen := layoutAt_length all 0
          obtain ⟨y, hy⟩ : ∃ y, (layoutAt 0 all)[j]? = some y := by
            have : j < (layoutAt 0 all).length := by omega
            exact ⟨_, List.getElem?_eq_getElem this⟩
          have hy1 : y.1 = t := (layoutAt_labelPos l all hok 0 0 j t hl).2 y (by simpa using hy)
          have hfind := findIdx?_of_pairwise _ (layoutAt_pairwise all hok 0) j y hy
          rw [hy1, ht] at hfind
          simp only [layoutAt, expectedFrom, hdec, resolveAll, htgt, hfind, ih']

theorem decCount_le_bytes (items : List Item) (hok : ∀ it ∈ items, ItemOK it) :
    decCount items ≤ (itemBytes items).length := by
  induction items with
  | nil => simp [decCount]
  | cons it rest ih =>
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold ItemOK at hit
    have hbs : itemBytes (it :: rest) = it.bytes ++ itemBytes rest := by simp [itemBytes]
    rw [hbs, List.length_append]
    cases hdec : it.dec with
    | none => simp [decCount, hdec]; omega
    | some x =>
      rw [hdec] at hit
      have hpos : 0 < it.bytes.length := List.length_pos_iff.mpr hit.1
      simp [decCount, hdec]; omega

/-- **Program round trip.** The byte stream of a well-formed item list decodes
    to the program the list denotes. -/
theorem decodeLprog_items (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (hbr : branchOK items 0 items = true) :
    decodeLprog (itemBytes items) = expectedFrom items items := by
  have hfuel : (layoutAt 0 items).length ≤ (itemBytes items).length := by
    rw [layoutAt_length]; exact decCount_le_bytes items hok
  rw [decodeLprog, decodeAt_items items hok _ 0 hfuel]
  exact resolveAll_layout items hok items 0 hbr

/-! ## 6b. Bodies built from decodable shapes

A `Shape` says what one `LinstrR` decodes to: nothing, a straight-line
instruction, or a branch to a label. A body whose instructions each have a
shape is an item list, and the program round trip applies to `encodeLcmd`. -/

/-- What one body instruction decodes to. -/
inductive Shape where
  | skip
  | op (i : JInstr 64)
  | jcc (cc : Nat) (l : LLabel)

/-- The decoded instruction of a shape under a displacement resolver. -/
def Shape.dec : Shape → (LLabel → Int) → Option DInstr
  | .skip, _ => none
  | .op i, _ => some (.op i)
  | .jcc cc l, d => some (.jcc cc (wrap32 (d l)))

/-- The label a shape branches to. -/
def Shape.target : Shape → Option LLabel
  | .jcc _ l => some l
  | _ => none

/-- The label an instruction defines. -/
def labelOf : LinstrR → Option LLabel
  | .Llabel _ l => some l
  | _ => none

/-- Under every resolver the instruction's bytes decode to the shape. -/
def ShapeOK (P : Params) (i : LinstrR) (sh : Shape) : Prop :=
  ∀ d : LLabel → Int,
    ItemOK ⟨encodeLinstrR P.frame P.spillW d i P.qsaveB, sh.dec d, none, none⟩

/-- The item list of a body laid out from offset `off`. -/
def itemsFrom (P : Params) : Nat → Lcmd → List Shape → List Item
  | off, instr :: body, sh :: shs =>
      { bytes := P.encAt off instr.li_i, dec := sh.dec (P.dispAt off instr.li_i),
        label := labelOf instr.li_i, target := sh.target }
        :: itemsFrom P (off + P.lenAt off instr.li_i) body shs
  | _, _, _ => []

theorem itemBytes_itemsFrom (P : Params) {body : Lcmd} {shs : List Shape}
    (h : List.Forall₂ (fun instr sh => ShapeOK P instr.li_i sh) body shs) :
    ∀ off, itemBytes (itemsFrom P off body shs) = encodeFrom P off body := by
  induction h with
  | nil => intro off; rfl
  | cons _ _ ih =>
    intro off
    simp only [itemsFrom, encodeFrom, itemBytes, List.flatMap_cons]
    exact congrArg _ (ih _)

theorem itemsFrom_ok (P : Params) {body : Lcmd} {shs : List Shape}
    (h : List.Forall₂ (fun instr sh => ShapeOK P instr.li_i sh) body shs) :
    ∀ off, ∀ it ∈ itemsFrom P off body shs, ItemOK it := by
  induction h with
  | nil => intro off it hit; cases hit
  | cons hab _ ih =>
    intro off it hit
    simp only [itemsFrom, List.mem_cons] at hit
    rcases hit with rfl | hit
    · exact hab _
    · exact ih _ it hit

/-- **Body round trip.** A body whose instructions all have shapes, with
    well-formed branches, decodes to the program its item list denotes. -/
theorem decodeLprog_encodeLcmd (body : Lcmd) (shs : List Shape)
    (h : List.Forall₂ (fun instr sh => ShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hbr : branchOK (itemsFrom (Params.ofBody body) 0 body shs) 0
      (itemsFrom (Params.ofBody body) 0 body shs) = true) :
    decodeLprog (encodeLcmd body)
      = expectedFrom (itemsFrom (Params.ofBody body) 0 body shs)
          (itemsFrom (Params.ofBody body) 0 body shs) := by
  rw [encodeLcmd_eq_encodeFrom, ← itemBytes_itemsFrom _ h 0]
  exact decodeLprog_items _ (itemsFrom_ok _ h 0) hbr

/-- A label definition carries no bytes. -/
theorem shapeOK_label (P : Params) (k : LabelKind) (l : LLabel) :
    ShapeOK P (.Llabel k l) .skip := fun _ => rfl

/-- The body's `Lret` carries no bytes; the function wrapper lays down `ret`. -/
theorem shapeOK_ret (P : Params) : ShapeOK P .Lret .skip := fun _ => rfl

/-- A conditional branch decodes to a branch to its label, in either the `rel8`
    or the `rel32` form. -/
theorem shapeOK_cond (P : Params) (cc : String) (l : LLabel) :
    ShapeOK P (.Lcond (.reg cc) l) (.jcc (ccNibble cc) l) := by
  intro d
  refine ItemOK_of_decode fun rest => ?_
  simp only [encodeLinstrR]
  split
  · rename_i h8
    have hok : dispOk (d l) = true := by simpa [fitsRel8, dispOk] using h8
    rw [decodeLinstr_jcc8 cc (d l) rest hok,
      wrap32_of_dispOk32 _ (dispOk32_of_dispOk _ hok)]
  · exact decodeLinstr_jcc32_wrap cc (d l) rest

/-- A straight-line `Lopn` whose bytes are those of a decodable item has that
    item's shape. -/
theorem shapeOK_lopn (P : Params) (ds : List LOperand) (o : String) (ss : List LOperand)
    (bytes : List (BitVec 8)) (x : JInstr 64)
    (hb : encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB = bytes)
    (hok : ItemOK ⟨bytes, some (.op x), none, none⟩) :
    ShapeOK P (.Lopn ds o ss) (.op x) := by
  intro d
  have : encodeLinstrR P.frame P.spillW d (.Lopn ds o ss) P.qsaveB = bytes := hb
  rw [this]; exact hok

/-! ## 7. The binary logical loop kernels -/

/-- The limb operation of `mpn_and_n_loop_owned` (`opn = "AND:64"`) and
    `mpn_xor_n_loop_owned` (`opn = "XOR:64"`), through the store of the result. -/
def andMid (opn cpy : String) : List LinstrR :=
  [ .Lopn [.reg "R9"] "MOV:64" [.reg "RBP"]
  , .Lopn [.reg "R9"] opn [.reg "R9", .reg "R8"]
  , .Lopn [.reg "RBP"] cpy [.reg "R9"]
  , .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"]
  , .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "RBP"] ]

/-- The limb operation of `mpn_ior_n_loop_owned`, `(a ^ b) ^ (a & b)`, through
    the store of the result. -/
def iorMid (cpy : String) : List LinstrR :=
  [ .Lopn [.reg "R9"] "MOV:64" [.reg "RBP"]
  , .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R8"]
  , .Lopn [.reg "R10"] "MOV:64" [.reg "RBP"]
  , .Lopn [.reg "R10"] "AND:64" [.reg "R10", .reg "R8"]
  , .Lopn [.reg "RBP"] "MOV:64" [.reg "R9"]
  , .Lopn [.reg "RBP"] "XOR:64" [.reg "RBP", .reg "R10"]
  , .Lopn [.reg "R8"] cpy [.reg "RBP"]
  , .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"]
  , .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "R8"] ]

/-- The `Lcmd` of a runtime-length binary logical loop around the limb operation
    `mid`. The mnemonic `cpy` of the index copy is a parameter: the export writes
    that copy, and the one inside `mid`, as the count-0 shift `"SHL:0:64"`. -/
def binLoopBody (mid : List LinstrR) (cpy : String) : Lcmd :=
  ([ .Lopn [.reg "qsave.RDI"] "MOVQ" [.reg "RDI"]
   , .Lopn [.reg "qsave.RSI"] "MOVQ" [.reg "RSI"]
   , .Lopn [.reg "qsave.RBX"] "MOVQ" [.reg "RBX"]
   , .Lopn [.reg "qsave.RBP"] "MOVQ" [.reg "RBP"]
   , .Lopn [.reg "qsave.R12"] "MOVQ" [.reg "R12"]
   , .Lopn [.reg "qsave.R13"] "MOVQ" [.reg "R13"]
   , .Lopn [.reg "qsave.R14"] "MOVQ" [.reg "R14"]
   , .Lopn [.reg "qsave.R15"] "MOVQ" [.reg "R15"]
   , .Lopn [.reg "R14"] "MOVQ" [.reg "RSI"]
   , .Lopn [.reg "qsave.RDX"] "MOVQ" [.reg "RDX"]
   , .Lopn [.reg "qsave.RCX"] "MOVQ" [.reg "RCX"]
   , .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RDI"]
   , .Lopn [.reg "RCX"] "MOVQ" [.reg "qsave.RSI"]
   , .Lopn [.reg "RSI"] "MOVQ" [.reg "qsave.RCX"]
   , .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"]
   , .Lopn [.reg "RAX"] "MOV:64" [.imm 0]
   , .Lopn [.reg "RDI"] "MOV:64" [.reg "RSI"]
   , .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0]
   , .Lcond (.reg "Z") 1073741828
   , .Llabel .internal 4
   , .Lopn [.reg "RSI"] cpy [.reg "RAX"]
   , .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"]
   , .Lopn [.reg "RBP"] "LOADIDX" [.arrIdx "R14" "RSI" 8]
   , .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDX"]
   , .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RSI" 8] ] ++ mid ++
   [ .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"]
   , .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]
   , .Lopn [.reg "RDI"] "SUB:64" [.reg "RDI", .imm 1]
   , .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RCX"]
   , .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RDX"]
   , .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0]
   , .Lcond (.reg "NZ") 4
   , .Llabel .internal 1073741828
   , .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"]
   , .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"]
   , .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"]
   , .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"]
   , .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"]
   , .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"]
   , .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

/-! ### Items of the shapes the kernels use -/

/-- `MOV %r, off(%rsp)`. -/
def mkStore (r : Nat) (off : Int) : Item :=
  ⟨encRspMem 1 0x89 r off, some (.op (.storeMem "%rsp" off (.reg (regName r)))), none, none⟩
/-- `MOV off(%rsp), %r`. -/
def mkLoad (r : Nat) (off : Int) : Item :=
  ⟨encRspMem 1 0x8b r off, some (.op (.loadMem (regName r) "%rsp" off)), none, none⟩
/-- A reg-reg legacy ALU/`MOV` op `op %s, %d`. -/
def mkAlu (op : Nat) (mk : String → JOperand → JInstr 64) (d s : Nat) : Item :=
  ⟨encAluRRw 1 op d s, some (.op (mk (regName d) (.reg (regName s)))), none, none⟩
/-- `MOV %s, %d`. -/
def mkMov (d s : Nat) : Item :=
  ⟨encAluRRw 1 0x89 d s, some (.op (.mov (regName d) (.reg (regName s)))), none, none⟩
/-- `CMP %s, %d`. -/
def mkCmp (d s : Nat) : Item :=
  ⟨encAluRRw 1 0x39 d s, some (.op (.cmp (regName d) (.reg (regName s)))), none, none⟩
/-- `MOV $v, %d`. -/
def mkMovImm (d v : Nat) : Item :=
  ⟨encMovImmw 1 d v, some (.op (.mov (regName d) (.imm v))), none, none⟩
/-- A group-1 op with a sign-extended `imm8`. -/
def mkImm8 (digit : Nat) (mk : String → JOperand → JInstr 64) (d v : Nat) : Item :=
  ⟨encAluImm8 1 digit d v, some (.op (mk (regName d) (.imm v))), none, none⟩
/-- `MOV (%base,%idx,8), %r`. -/
def mkLoadIdx (r base idx : Nat) : Item :=
  ⟨encMemMovSibw 1 0x8b r base idx 8,
    some (.op (.loadMemIdx (regName r) (regName base) (regName idx) 8)), none, none⟩
/-- `MOV %r, (%base,%idx,8)`. -/
def mkStoreIdx (r base idx : Nat) : Item :=
  ⟨encMemMovSibw 1 0x89 r base idx 8,
    some (.op (.storeMemIdx (regName base) (regName idx) 8 (.reg (regName r)))), none, none⟩
/-- `jcc rel8` to label `l`. -/
def mkJcc8 (cc : String) (d : Int) (l : LLabel) : Item :=
  ⟨encJcc8 cc d, some (.jcc (ccNibble cc) d), none, some l⟩
/-- The definition of label `l`. -/
def mkLabel (l : LLabel) : Item := ⟨[], none, some l, none⟩
/-- The frame `leaq disp(%rsp), %rsp`. -/
def mkLea (disp : Int) : Item :=
  ⟨encLeaRspFrame disp, some (.op (.lea "%rsp" "%rsp" "%rsp" 0 disp)), none, none⟩
/-- `ret`. -/
def mkRet : Item := ⟨LeafBytes.encRet, some .ret, none, none⟩

theorem mkStore_ok (r : Nat) (off : Int) (hr : r < 16) (h : dispOk32 off = true) :
    ItemOK (mkStore r off) :=
  ItemOK_of_decode fun rest => decodeLinstr_rspStore r off rest hr h
theorem mkLoad_ok (r : Nat) (off : Int) (hr : r < 16) (h : dispOk32 off = true) :
    ItemOK (mkLoad r off) :=
  ItemOK_of_decode fun rest => decodeLinstr_rspLoad r off rest hr h
theorem mkAlu_ok (op : Nat) (mk : String → JOperand → JInstr 64) (d s : Nat)
    (hd : d < 16) (hs : s < 16) (hop : aluTableOp op = true)
    (halu : aluMnemonic op = some mk) : ItemOK (mkAlu op mk d s) :=
  ItemOK_of_decode fun rest => decodeLinstr_aluRR op mk d s rest hd hs hop halu
theorem mkMov_ok (d s : Nat) (hd : d < 16) (hs : s < 16) : ItemOK (mkMov d s) :=
  ItemOK_of_decode fun rest => decodeLinstr_movRR d s rest hd hs
theorem mkCmp_ok (d s : Nat) (hd : d < 16) (hs : s < 16) : ItemOK (mkCmp d s) :=
  ItemOK_of_decode fun rest => decodeLinstr_cmpRR d s rest hd hs
theorem mkMovImm_ok (d v : Nat) (hd : d < 16) (hv : v < 2 ^ 32) : ItemOK (mkMovImm d v) :=
  ItemOK_of_decode fun rest => decodeLinstr_movImm d v rest hd hv
theorem mkImm8_ok (digit : Nat) (mk : String → JOperand → JInstr 64) (d v : Nat)
    (hdig : digit < 8) (hd : d < 16) (hv : fitsImm8S 1 v = true)
    (halu : aluImm8Mnemonic digit = some mk) : ItemOK (mkImm8 digit mk d v) :=
  ItemOK_of_decode fun rest => decodeLinstr_aluImm8 digit mk d v rest hdig hd hv halu
theorem mkLoadIdx_ok (r base idx : Nat) (hr : r < 16) (hbase : base < 16)
    (hidx : idx < 16) (hb5 : base &&& 7 ≠ 5) (hi4 : idx ≠ 4) :
    ItemOK (mkLoadIdx r base idx) :=
  ItemOK_of_decode fun rest => decodeLinstr_loadIdx8 r base idx rest hr hbase hidx hb5 hi4
theorem mkStoreIdx_ok (r base idx : Nat) (hr : r < 16) (hbase : base < 16)
    (hidx : idx < 16) (hb5 : base &&& 7 ≠ 5) (hi4 : idx ≠ 4) :
    ItemOK (mkStoreIdx r base idx) :=
  ItemOK_of_decode fun rest => decodeLinstr_storeIdx8 r base idx rest hr hbase hidx hb5 hi4
theorem mkJcc8_ok (cc : String) (d : Int) (l : LLabel) (h : dispOk d = true) :
    ItemOK (mkJcc8 cc d l) :=
  ItemOK_of_decode fun rest => decodeLinstr_jcc8 cc d rest h
theorem mkLabel_ok (l : LLabel) : ItemOK (mkLabel l) := rfl
theorem mkLea_ok (disp : Int) (h0 : disp ≠ 0) (h : dispOk32 disp = true) :
    ItemOK (mkLea disp) :=
  ItemOK_of_decode fun rest => decodeLinstr_leaRsp disp rest h0 h
theorem mkRet_ok : ItemOK mkRet := ItemOK_of_decode decodeLinstr_ret

/-! ### The function as an item list -/

/-- The items of the limb operation `andMid`, at ALU opcode `op`. -/
def andMidItems (op : Nat) (mk : String → JOperand → JInstr 64) : List Item :=
  [ mkMov 9 5, mkAlu op mk 9 8, mkMov 5 9, mkLoad 14 56,
    mkStoreIdx 5 14 6 ]

/-- The items of the limb operation `iorMid`. -/
def iorMidItems : List Item :=
  [ mkMov 9 5, mkAlu 0x31 .xor_ 9 8, mkMov 10 5,
    mkAlu 0x21 .and_ 10 8, mkMov 5 9, mkAlu 0x31 .xor_ 5 10,
    mkMov 8 5, mkLoad 14 56, mkStoreIdx 8 14 6 ]

/-- The whole function of a binary logical loop as an item list: the frame
    `leaq`, the body around the limb items `mid`, the closing `leaq` and `ret`.
    `dz` is the displacement of the zero-trip guard and `dnz` of the back-edge. -/
def binItems (mid : List Item) (dz dnz : Int) : List Item :=
  [ mkLea (-64)
  , mkStore 7 56, mkStore 6 48, mkStore 3 40, mkStore 5 32, mkStore 12 24
  , mkStore 13 16, mkStore 14 8, mkStore 15 0
  , mkMov 14 6
  , mkStore 2 (-8), mkStore 1 (-16)
  , mkLoad 3 56, mkLoad 1 48, mkLoad 6 (-16)
  , mkMov 3 3, mkMovImm 0 0, mkMov 7 6, mkImm8 7 .cmp 7 0
  , mkJcc8 "Z" dz 1073741828
  , mkLabel 4
  , mkMov 6 0, mkLoad 14 48, mkLoadIdx 5 14 6, mkLoad 14 (-8)
  , mkLoadIdx 8 14 6 ] ++ mid ++
  [ mkMov 3 3, mkImm8 0 .add 0 1, mkImm8 5 .sub 7 1, mkCmp 7 1, mkCmp 7 2
  , mkImm8 7 .cmp 7 0
  , mkJcc8 "NZ" dnz 4
  , mkLabel 1073741828
  , mkLoad 3 40, mkLoad 5 32, mkLoad 12 24, mkLoad 13 16, mkLoad 14 8, mkLoad 15 0
  , mkLea 64, mkRet ]

/-- Discharge `ItemOK` for an item built by one of the `mk*` constructors over
    literal operands. -/
macro "item_ok" : tactic =>
  `(tactic| first
    | exact mkLabel_ok _
    | exact mkRet_ok
    | (refine mkStore_ok _ _ ?_ ?_ <;> decide)
    | (refine mkLoad_ok _ _ ?_ ?_ <;> decide)
    | (refine mkAlu_ok _ _ _ _ ?_ ?_ ?_ ?_ <;> first | assumption | decide | rfl)
    | (refine mkMov_ok _ _ ?_ ?_ <;> decide)
    | (refine mkCmp_ok _ _ ?_ ?_ <;> decide)
    | (refine mkMovImm_ok _ _ ?_ ?_ <;> decide)
    | (refine mkImm8_ok _ _ _ _ ?_ ?_ ?_ ?_ <;> first | decide | rfl)
    | (refine mkLoadIdx_ok _ _ _ ?_ ?_ ?_ ?_ ?_ <;> decide)
    | (refine mkStoreIdx_ok _ _ _ ?_ ?_ ?_ ?_ ?_ <;> decide)
    | (refine mkJcc8_ok _ _ _ ?_ <;> first | assumption | decide)
    | (refine mkLea_ok _ ?_ ?_ <;> decide))

theorem ok_nil : ∀ it ∈ ([] : List Item), ItemOK it := by
  intro it h; cases h

theorem ok_cons {a : Item} {l : List Item} (ha : ItemOK a) (hl : ∀ it ∈ l, ItemOK it) :
    ∀ it ∈ a :: l, ItemOK it := by
  intro it h
  rcases List.mem_cons.mp h with rfl | h
  · exact ha
  · exact hl it h

theorem ok_append {l₁ l₂ : List Item} (h₁ : ∀ it ∈ l₁, ItemOK it)
    (h₂ : ∀ it ∈ l₂, ItemOK it) : ∀ it ∈ l₁ ++ l₂, ItemOK it := by
  intro it h
  rcases List.mem_append.mp h with h | h
  · exact h₁ it h
  · exact h₂ it h

/-- Discharge `ItemOK` over a literal list of `mk*` items. -/
macro "items_ok" : tactic =>
  `(tactic| repeat' (first | exact ok_nil | refine ok_cons ?_ ?_ | item_ok))

section
attribute [local irreducible] mkStore mkLoad mkAlu mkMov mkCmp mkMovImm mkImm8 mkLoadIdx
  mkStoreIdx mkJcc8 mkLabel mkLea mkRet

theorem andMidItems_ok (op : Nat) (mk : String → JOperand → JInstr 64)
    (hop : aluTableOp op = true) (halu : aluMnemonic op = some mk) :
    ∀ it ∈ andMidItems op mk, ItemOK it := by
  unfold andMidItems
  items_ok

theorem iorMidItems_ok : ∀ it ∈ iorMidItems, ItemOK it := by
  unfold iorMidItems
  items_ok

theorem binItems_ok (mid : List Item) (dz dnz : Int) (hmid : ∀ it ∈ mid, ItemOK it)
    (hz : dispOk dz = true) (hnz : dispOk dnz = true) :
    ∀ it ∈ binItems mid dz dnz, ItemOK it := by
  unfold binItems
  refine ok_append (ok_append ?_ hmid) ?_ <;> items_ok

end

/-! ### Instructions the body encoder cannot tell apart

`tagShiftCount` reads the count of a count-in-tag shift with `String.toNat?`,
which does not reduce in the kernel. The count-0 shift between two distinct
registers encodes as the copy `MOV:64`; the results below transport an encoding
along such a replacement, so the closed evaluations run on the `MOV:64` form. -/

/-- The count-0 shift between distinct general-purpose registers encodes as the
    register copy. -/
theorem encodeLopn_shl0 (f w q : Nat) (dn sn : String)
    (h0 : tagShiftCount "SHL:0" = 0)
    (hd : isGpName dn = true) (hs : isGpName sn = true) (hne : (dn == sn) = false) :
    encodeLopn f w (.Lopn [.reg dn] "SHL:0:64" [.reg sn]) q
      = encAluRRw 1 0x89 (gpNumU dn) (gpNumU sn) := by
  have hbind : (isCarryOutBinding "SHL:0:64" || isMulHiBinding "SHL:0:64") = false := by
    decide +kernel
  have hstrip : stripWidthTag "SHL:0:64" = "SHL:0" := by decide +kernel
  have hw : LprogBytes.rexW (mnemWidth "SHL:0:64") = 1 := by decide +kernel
  have hmulx : ("SHL:0" == "MULX") = false := by decide +kernel
  have hmulxmem : ("SHL:0" == "MULXMEM") = false := by decide +kernel
  have hadx : adxPrefix "SHL:0" = none := by decide +kernel
  have htag : tagShiftExt "SHL:0" = some 4 := by decide +kernel
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx, htag, hd, hs, hne, h0,
    Bool.false_eq_true, if_false, Bool.and_self, if_true]

/-- Two instructions with the same encoding under every resolver: equal, or two
    `Lopn`s with the same bytes. -/
def EncEq (f w q : Nat) (a b : Linstr) : Prop :=
  a.li_i = b.li_i ∨
    ∃ ds o ss ds' o' ss', a.li_i = .Lopn ds o ss ∧ b.li_i = .Lopn ds' o' ss' ∧
      encodeLopn f w (.Lopn ds o ss) q = encodeLopn f w (.Lopn ds' o' ss') q

theorem EncEq.enc {f w q : Nat} {a b : Linstr} (h : EncEq f w q a b) (d : LLabel → Int) :
    encodeLinstrR f w d a.li_i q = encodeLinstrR f w d b.li_i q := by
  rcases h with h | ⟨ds, o, ss, ds', o', ss', ha, hb, he⟩
  · rw [h]
  · rw [ha, hb]; exact he

theorem EncEq.len {f w q : Nat} {a b : Linstr} (h : EncEq f w q a b) (d : LLabel → Int) :
    instrLenAt f w d a.li_i q = instrLenAt f w d b.li_i q := by
  unfold instrLenAt; rw [h.enc]

/-- One step of `relaxPass`. -/
def relaxStep (f w q : Nat) (tbl : List (LLabel × Nat))
    (acc : Nat × List (LLabel × Nat)) (instr : Linstr) : Nat × List (LLabel × Nat) :=
  let (off, out) := acc
  match instr.li_i with
  | .Llabel _ l => (off, out ++ [(l, off)])
  | i =>
      let dispOf : LLabel → Int := fun t =>
        Int.ofNat (lookupLabel tbl t) - Int.ofNat (off + instrLenAt f w (fun _ => 0) i q)
      (off + instrLenAt f w dispOf i q, out)

theorem relaxPass_eq_foldl (f w q : Nat) (tbl : List (LLabel × Nat)) (body : Lcmd) :
    relaxPass f w tbl body q = (body.foldl (relaxStep f w q tbl) (0, [])).2 := rfl

theorem relaxStep_congr {f w q : Nat} {a b : Linstr} (h : EncEq f w q a b)
    (tbl : List (LLabel × Nat)) (acc : Nat × List (LLabel × Nat)) :
    relaxStep f w q tbl acc a = relaxStep f w q tbl acc b := by
  rcases h with h | ⟨ds, o, ss, ds', o', ss', ha, hb, he⟩
  · unfold relaxStep; rw [h]
  · have hl : ∀ d : LLabel → Int,
        instrLenAt f w d (.Lopn ds o ss) q = instrLenAt f w d (.Lopn ds' o' ss') q := by
      intro d; unfold instrLenAt; exact congrArg List.length he
    unfold relaxStep
    rw [ha, hb]
    simp only [hl]

theorem relaxPass_congr {f w q : Nat} {body body' : Lcmd}
    (h : List.Forall₂ (EncEq f w q) body body') (tbl : List (LLabel × Nat)) :
    relaxPass f w tbl body q = relaxPass f w tbl body' q := by
  rw [relaxPass_eq_foldl, relaxPass_eq_foldl]
  suffices hk : ∀ acc, body.foldl (relaxStep f w q tbl) acc
      = body'.foldl (relaxStep f w q tbl) acc by rw [hk]
  induction h with
  | nil => intro acc; rfl
  | cons hab _ ih =>
    intro acc
    rw [List.foldl_cons, List.foldl_cons, relaxStep_congr hab, ih]

theorem relaxFix_congr {f w q : Nat} {body body' : Lcmd}
    (h : List.Forall₂ (EncEq f w q) body body') :
    ∀ (fuel : Nat) (tbl : List (LLabel × Nat)),
      relaxFix f w q fuel tbl body = relaxFix f w q fuel tbl body' := by
  intro fuel
  induction fuel with
  | zero => intro tbl; rfl
  | succ n ih =>
    intro tbl
    simp only [relaxFix, relaxPass_congr h, ih]

theorem labelOffsets_congr {f w q : Nat} {body body' : Lcmd}
    (h : List.Forall₂ (EncEq f w q) body body') :
    labelOffsets f w body q = labelOffsets f w body' q := by
  unfold labelOffsets
  rw [h.length_eq, relaxPass_congr h, relaxFix_congr h]

theorem encodeFrom_congr (P : Params) {body body' : Lcmd}
    (h : List.Forall₂ (EncEq P.frame P.spillW P.qsaveB) body body') :
    ∀ off, encodeFrom P off body = encodeFrom P off body' := by
  induction h with
  | nil => intro off; rfl
  | @cons a b _ _ hab _ ih =>
    intro off
    have hlen : ∀ o, P.lenAt o a.li_i = P.lenAt o b.li_i := fun o => by
      unfold Params.lenAt; rw [hab.len (fun _ => 0), hab.len]
    have henc : ∀ o, P.encAt o a.li_i = P.encAt o b.li_i := fun o => by
      unfold Params.encAt Params.dispAt; rw [hlen o, hab.enc]
    simp only [encodeFrom, hlen, henc, ih]

/-! ### The function bytes -/

/-- The `.text` bytes of a function that saves no register by `push`: the frame
    `leaq`, the body, the closing `leaq`, `ret`. -/
def fundefBytes (P : Params) (body : Lcmd) : List (BitVec 8) :=
  encLeaRspFrame (-(Int.ofNat P.frame)) ++ encodeFrom P 0 body
    ++ encLeaRspFrame (Int.ofNat P.frame) ++ LeafBytes.encRet

theorem encodeLfundefBytes_eq (body : Lcmd) (hsaves : calleeSavedToSave body = []) :
    encodeLfundefBytes body = fundefBytes (Params.ofBody body) body := by
  simp [encodeLfundefBytes, fundefBytes, hsaves, encodeLcmd_eq_encodeFrom, Params.ofBody]

/-- **Function round trip.** A U64 body that saves no register by `push`, whose
    frame is `F` and qsave block `Q`, and that the encoder cannot tell apart from
    `body'`, decodes to the program of any well-formed item list carrying the
    function bytes of `body'`. -/
theorem decodeLprog_fundef (body body' : Lcmd) (F Q : Nat) (items : List Item)
    (hsaves : calleeSavedToSave body = [])
    (hframe : frameSize body = F) (hU64 : bodyIsU64 body = true)
    (hq : qsaveBytesFor body = Q)
    (hcong : List.Forall₂ (EncEq F 64 Q) body body')
    (hbytes : fundefBytes
        { frame := F, spillW := 64, qsaveB := Q, tbl := labelOffsets F 64 body' Q } body'
      = itemBytes items)
    (hok : ∀ it ∈ items, ItemOK it) (hbr : branchOK items 0 items = true) :
    decodeLprog (encodeLfundefBytes body) = expectedFrom items items := by
  have hP : Params.ofBody body
      = { frame := F, spillW := 64, qsaveB := Q, tbl := labelOffsets F 64 body' Q } := by
    simp only [Params.ofBody, hframe, hU64, hq, if_true, labelOffsets_congr hcong]
  have hfrom := encodeFrom_congr
    { frame := F, spillW := 64, qsaveB := Q, tbl := labelOffsets F 64 body' Q } hcong 0
  rw [encodeLfundefBytes_eq body hsaves, hP, fundefBytes, hfrom]
  rw [fundefBytes] at hbytes
  rw [hbytes]
  exact decodeLprog_items items hok hbr

/-- The count-0 shift and the register copy are the same instruction to the
    body encoder. -/
theorem encEq_shl0 (f w q : Nat) (dn sn : String) (h0 : tagShiftCount "SHL:0" = 0)
    (hd : isGpName dn = true) (hs : isGpName sn = true) (hne : (dn == sn) = false)
    (hmov : encodeLopn f w (.Lopn [.reg dn] "MOV:64" [.reg sn]) q
      = encAluRRw 1 0x89 (gpNumU dn) (gpNumU sn)) :
    EncEq f w q ⟨0, .Lopn [.reg dn] "SHL:0:64" [.reg sn]⟩
      ⟨0, .Lopn [.reg dn] "MOV:64" [.reg sn]⟩ :=
  Or.inr ⟨_, _, _, _, _, _, rfl, rfl,
    (encodeLopn_shl0 f w q dn sn h0 hd hs hne).trans hmov.symm⟩

/-- Relate two literal bodies that differ in count-0 shifts only. -/
macro "body_congr" h0:term : tactic =>
  `(tactic| repeat' (first
    | exact List.Forall₂.nil
    | refine List.Forall₂.cons ?_ ?_
    | exact Or.inl rfl
    | exact encEq_shl0 _ _ _ _ _ $h0 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel)))

/-- The program the binary logical loops decode to, around the decoded limb
    operation `mid`: branch targets are instruction indices, `20` the loop head
    and `32 + mid.length` the first instruction after the loop. -/
def binDecoded (mid : List RInstr) : List RInstr :=
  [ .op (.lea "%rsp" "%rsp" "%rsp" 0 (-64))
  , .op (.storeMem "%rsp" 56 (.reg "%rdi")), .op (.storeMem "%rsp" 48 (.reg "%rsi"))
  , .op (.storeMem "%rsp" 40 (.reg "%rbx")), .op (.storeMem "%rsp" 32 (.reg "%rbp"))
  , .op (.storeMem "%rsp" 24 (.reg "%r12")), .op (.storeMem "%rsp" 16 (.reg "%r13"))
  , .op (.storeMem "%rsp" 8 (.reg "%r14")), .op (.storeMem "%rsp" 0 (.reg "%r15"))
  , .op (.mov "%r14" (.reg "%rsi"))
  , .op (.storeMem "%rsp" (-8) (.reg "%rdx")), .op (.storeMem "%rsp" (-16) (.reg "%rcx"))
  , .op (.loadMem "%rbx" "%rsp" 56), .op (.loadMem "%rcx" "%rsp" 48)
  , .op (.loadMem "%rsi" "%rsp" (-16))
  , .op (.mov "%rbx" (.reg "%rbx")), .op (.mov "%rax" (.imm 0))
  , .op (.mov "%rdi" (.reg "%rsi")), .op (.cmp "%rdi" (.imm 0))
  , .jcc 4 (32 + mid.length)
  , .op (.mov "%rsi" (.reg "%rax")), .op (.loadMem "%r14" "%rsp" 48)
  , .op (.loadMemIdx "%rbp" "%r14" "%rsi" 8), .op (.loadMem "%r14" "%rsp" (-8))
  , .op (.loadMemIdx "%r8" "%r14" "%rsi" 8) ] ++ mid ++
  [ .op (.mov "%rbx" (.reg "%rbx")), .op (.add "%rax" (.imm 1)), .op (.sub "%rdi" (.imm 1))
  , .op (.cmp "%rdi" (.reg "%rcx")), .op (.cmp "%rdi" (.reg "%rdx"))
  , .op (.cmp "%rdi" (.imm 0))
  , .jcc 5 20
  , .op (.loadMem "%rbx" "%rsp" 40), .op (.loadMem "%rbp" "%rsp" 32)
  , .op (.loadMem "%r12" "%rsp" 24), .op (.loadMem "%r13" "%rsp" 16)
  , .op (.loadMem "%r14" "%rsp" 8), .op (.loadMem "%r15" "%rsp" 0)
  , .op (.lea "%rsp" "%rsp" "%rsp" 0 64), .ret ]

/-- The decoded limb operation of the `and`/`xor` loops. -/
def andMidDecoded (mk : String → JOperand → JInstr 64) : List RInstr :=
  [ .op (.mov "%r9" (.reg "%rbp")), .op (mk "%r9" (.reg "%r8"))
  , .op (.mov "%rbp" (.reg "%r9")), .op (.loadMem "%r14" "%rsp" 56)
  , .op (.storeMemIdx "%r14" "%rsi" 8 (.reg "%rbp")) ]

/-- The decoded limb operation of the `ior` loop. -/
def iorMidDecoded : List RInstr :=
  [ .op (.mov "%r9" (.reg "%rbp")), .op (.xor_ "%r9" (.reg "%r8"))
  , .op (.mov "%r10" (.reg "%rbp")), .op (.and_ "%r10" (.reg "%r8"))
  , .op (.mov "%rbp" (.reg "%r9")), .op (.xor_ "%rbp" (.reg "%r10"))
  , .op (.mov "%r8" (.reg "%rbp")), .op (.loadMem "%r14" "%rsp" 56)
  , .op (.storeMemIdx "%r14" "%rsi" 8 (.reg "%r8")) ]

/-- **`mpn_and_n_loop_owned`.** The function bytes the encoder lays down for the
    `and` loop decode to `binDecoded`, given the frame size of the body and the
    count of the `"SHL:0"` tag, the two facts the kernel cannot evaluate. -/
theorem and_n_roundtrip
    (hframe : frameSize (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64") = 64)
    (h0 : tagShiftCount "SHL:0" = 0) :
    decodeLprog (encodeLfundefBytes (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64"))
      = some (binDecoded (andMidDecoded .and_)) := by
  have hmid := andMidItems_ok 0x21 .and_ (by decide) rfl
  rw [decodeLprog_fundef _ (binLoopBody (andMid "AND:64" "MOV:64") "MOV:64") 64 64
    (binItems (andMidItems 0x21 .and_) 62 (-62))
    (by decide +kernel) hframe (by decide +kernel) (by decide +kernel)
    (by simp only [binLoopBody, andMid, List.cons_append, List.nil_append,
          List.map_cons, List.map_nil]
        body_congr h0)
    (by decide +kernel)
    (binItems_ok _ _ _ hmid (by decide) (by decide)) (by decide +kernel)]
  rfl

/-- **`mpn_xor_n_loop_owned`.** As `and_n_roundtrip`, at the `XOR:64` limb
    operation. -/
theorem xor_n_roundtrip
    (hframe : frameSize (binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64") = 64)
    (h0 : tagShiftCount "SHL:0" = 0) :
    decodeLprog (encodeLfundefBytes (binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64"))
      = some (binDecoded (andMidDecoded .xor_)) := by
  have hmid := andMidItems_ok 0x31 .xor_ (by decide) rfl
  rw [decodeLprog_fundef _ (binLoopBody (andMid "XOR:64" "MOV:64") "MOV:64") 64 64
    (binItems (andMidItems 0x31 .xor_) 62 (-62))
    (by decide +kernel) hframe (by decide +kernel) (by decide +kernel)
    (by simp only [binLoopBody, andMid, List.cons_append, List.nil_append,
          List.map_cons, List.map_nil]
        body_congr h0)
    (by decide +kernel)
    (binItems_ok _ _ _ hmid (by decide) (by decide)) (by decide +kernel)]
  rfl

/-- **`mpn_ior_n_loop_owned`.** As `and_n_roundtrip`, at the nine-instruction
    limb operation `iorMid`. -/
theorem ior_n_roundtrip
    (hframe : frameSize (binLoopBody (iorMid "SHL:0:64") "SHL:0:64") = 64)
    (h0 : tagShiftCount "SHL:0" = 0) :
    decodeLprog (encodeLfundefBytes (binLoopBody (iorMid "SHL:0:64") "SHL:0:64"))
      = some (binDecoded iorMidDecoded) := by
  rw [decodeLprog_fundef _ (binLoopBody (iorMid "MOV:64") "MOV:64") 64 64
    (binItems iorMidItems 74 (-74))
    (by decide +kernel) hframe (by decide +kernel) (by decide +kernel)
    (by simp only [binLoopBody, iorMid, List.cons_append, List.nil_append,
          List.map_cons, List.map_nil]
        body_congr h0)
    (by decide +kernel)
    (binItems_ok _ _ _ iorMidItems_ok (by decide) (by decide)) (by decide +kernel)]
  rfl

/-- The object `encodeLprogChecked` returns for a one-function program is the
    ELF wrapping of that function's `encodeLfundefBytes`, the byte string the
    round trips above decode. -/
theorem encodeLprogChecked_single {p : Lprog} {name : String} {f : Lfundef}
    {bs : List (BitVec 8)} (hp : p.lp_funcs = [(name, f)])
    (h : encodeLprogChecked p = some bs) :
    bs = ElfObject.buildElfObjectMulti
      [{ name := name, text := encodeLfundefBytes f.lfd_body }] := by
  rw [encodeLprogChecked_eq h, encodeLprog, hp]
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
