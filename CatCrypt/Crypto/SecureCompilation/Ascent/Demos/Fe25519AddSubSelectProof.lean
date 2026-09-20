/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Proof
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

/-!
# Correctness of the Curve25519 field add/sub blocks and the comb table select

This module proves the functional correctness of three families of x86 blocks under
`runBlock`: `Fe25519OpsKernel.feAddBlock` and `Fe25519OpsKernel.feSubBlock` (addition and
subtraction modulo `p25519 = 2^255 - 19` on four 64-bit limbs), and
`CombSelectKernel.combSelectBlock`, `combSelect5Block`, `combSelect6Block` (the 16-, 32- and
64-entry table selects). The constant-time statements for these blocks are in the kernel
modules; the results here are about values.

## Memory and calling convention

`JState.mem` is keyed by the base register's name. The field blocks read `x` and `y` from
the banks `"x"` and `"y"` and write `z` to the bank `"z"`; the select blocks read the table
from the bank `"tbl"`, the index from register `d`, and write to the bank `"z"`. Distinct
names are distinct banks, so an output buffer aliasing an input buffer is outside the model.

## Input ranges

* `feAddBlock` forms `d = x + y` and `c = d + 19`, drops the carry out of both chains, and
  returns `c` with bit 255 cleared when bit 255 of `c` is set, `d` otherwise. The carries
  are zero and the result is `(x + y) mod p25519` exactly when `x + y < 2 · p25519`, which
  holds for reduced inputs.
* `feSubBlock` forms `d = x - y` with borrow `b`, subtracts `19 · b`, drops that borrow, and
  clears bit 255. The result is `(x + p25519 - y) mod p25519` when `x < y + p25519` and
  `y ≤ x + p25519`, which holds for `x < p25519`, `y ≤ p25519`.
* The select blocks need the index below the number of entries; the output is then the
  entry at the index. For a larger index the accumulators stay zero.

## Proof structure

* Transport lemmas for the instruction forms the blocks use beyond those of
  `S2nMontmulP384Proof` (`run_add_op`, `run_sub_imm`, `run_and_op`, `run_xor_op`,
  `run_neg`, `run_shr63`, `run_cmove`), over the same state description `Desc`.
* `mask_sel`, `and_mask63`, `sbb_mask19`: the word identities of the branchless selects.
* `add_arith`, `sub_arith`: the carry equations closed over `Nat`; `add_spec`, `sub_spec`:
  the symbolic runs.
* The select blocks are `selBlock n` (`combSelectBlock_eq` and its two siblings, by `rfl`).
  `selEntry_corresJ` advances the scan invariant `SelInv` by one entry, and `selScan_inv`
  composes the entries with `runBlock_append`.

## Main results

* `feAddBlock_correct`: for `x + y < 2 · p25519`, the output is `(x + y) mod p25519`, below
  `p25519`, equal to `x + y` in `ZMod p25519`, and no memory outside `z` changes.
* `feSubBlock_correct`: for `x < y + p25519` and `y ≤ x + p25519`, the output is
  `(x + p25519 - y) mod p25519`, below `p25519`, equal to `x - y` in `ZMod p25519`, and no
  memory outside `z` changes.
* `feAddBlock_corresJ`, `feSubBlock_corresJ`: the same results as `CorresJ` steps over the
  abstract state `AFe`.
* `selBlock_correct`: for an index `D < n`, the `n`-entry select stores the four words at
  `[tbl + 32·D + 8·k]` at `[z + 8·k]`.
* `combSelectBlock_correct`, `combSelect5Block_correct`, `combSelect6Block_correct`: the
  instances `n = 16, 32, 64`.
* `combSelectBlock_initState`, `combSelect5Block_initState`, `combSelect6Block_initState`:
  from the kernels' `initState tab didx`, the output limbs are `tab didx`.

Provenance class: `@proved-hand-kernel theorems: feAddBlock_correct, feSubBlock_correct, combSelectBlock_correct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
  (cb cb_le_one upd opv Desc Desc.eval Reach reach_nil cb_false run_mov run_loadMem
    run_adc run_add run_sub run_sbb run_storeMem desc_self)

/-! ## Transport lemmas for the bitwise and immediate instruction forms -/

section Transport

variable {Q : JState 64 → Prop} {rest : List (JInstr 64)} {R : String → BitVec 64}
  {cf of zf : Bool} {M : JMem 64} {s : JState 64}

theorem run_add_op (d : String) (o : JOperand) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool),
      w.toNat + 2 ^ 64 * cb c = (R d).toNat + (opv R o).toNat → cb c ≤ 1 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.add d o :: rest)) := by
  rw [runBlock_cons]
  have hx := (R d).isLt
  have hy := (opv R o).isLt
  refine h (BitVec.ofNat 64 ((R d).toNat + (opv R o).toNat))
    (decide (2 ^ 64 ≤ (R d).toNat + (opv R o).toNat)) _ _ ?_ (cb_le_one _) _
    ⟨?_, hs.mem, ?_, rfl, rfl⟩
  · simp only [BitVec.toNat_ofNat, cb]
    split <;> simp_all; omega
  · funext r
    simp only [evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop, JState.get, hs.eval,
      upd, hs.regs]
    split <;> simp [BitVec.ofNat_add]
  · simp only [evalInstr, hs.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_ADD, rflags_of_aluop, wunsigned,
      BitVec.toNat_add, Option.getD_some]
    apply decide_eq_decide.mpr
    constructor <;> intro <;> omega

theorem run_sub_imm (d : String) (k : Nat) (hs : Desc R cf of zf M s)
    (h : ∀ (c o' : Bool) t,
      Desc (upd R d (R d - BitVec.ofNat 64 k)) c o' (decide (R d = BitVec.ofNat 64 k)) M t →
      Q (runBlock t rest)) :
    Q (runBlock s (.sub d (.imm k) :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ _ ⟨?_, hs.mem, rfl, rfl, ?_⟩
  · funext r
    simp only [evalInstr, JState.writeB5W, x86_SUB, JState.get, JOperand.eval, upd, hs.regs]
  · simp only [evalInstr, JOperand.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_SUB, ZF_of_word, Option.getD_some]
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> bv_omega

theorem run_and_op (d : String) (o : JOperand) (hs : Desc R cf of zf M s)
    (h : ∀ (c o' z : Bool) t, Desc (upd R d (R d &&& opv R o)) c o' z M t →
      Q (runBlock t rest)) :
    Q (runBlock s (.and_ d o :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ _ _ ⟨?_, hs.mem, rfl, rfl, rfl⟩
  funext r
  simp only [evalInstr, JState.writeB5W, x86_AND, rflags_of_bwop, JState.get, hs.eval, upd,
    hs.regs]

theorem run_xor_op (d : String) (o : JOperand) (hs : Desc R cf of zf M s)
    (h : ∀ (c o' z : Bool) t, Desc (upd R d (R d ^^^ opv R o)) c o' z M t →
      Q (runBlock t rest)) :
    Q (runBlock s (.xor_ d o :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ _ _ ⟨?_, hs.mem, rfl, rfl, rfl⟩
  funext r
  simp only [evalInstr, JState.writeB5W, x86_XOR, rflags_of_bwop, JState.get, hs.eval, upd,
    hs.regs]

theorem run_neg (d : String) (hs : Desc R cf of zf M s)
    (h : ∀ (c o' z : Bool) t, Desc (upd R d ((0 : BitVec 64) - R d)) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.neg d :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ _ _ ⟨?_, hs.mem, rfl, rfl, rfl⟩
  funext r
  simp only [evalInstr, JState.writeB5W, x86_NEG, JState.get, upd, hs.regs]

theorem run_shr63 (d : String) (hs : Desc R cf of zf M s)
    (h : ∀ (c o' z : Bool) t, Desc (upd R d (R d >>> 63)) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.shr d (.imm 63) :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ _ _ ⟨?_, hs.mem, rfl, rfl, rfl⟩
  funext r
  simp [evalInstr, JState.writeB5W, x86_SHR, shiftCount, rflags_OF, wshr, upd, hs.regs]

theorem run_cmove (d src : String) (hs : Desc R cf of zf M s)
    (h : ∀ t, Desc (upd R d (if zf then R src else R d)) cf of zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.cmove d (.reg src) :: rest)) := by
  rw [runBlock_cons]
  refine h _ ⟨?_, hs.mem, hs.hcf, hs.hof, hs.hzf⟩
  funext r
  simp only [evalInstr, JState.setReg, x86_CMOVcc, JOperand.eval, JState.get, hs.hzf, upd,
    hs.regs]

end Transport

/-! ## Word lemmas for the branchless select -/

theorem shr63_toNat (t : BitVec 64) : (t >>> 63).toNat = t.toNat / 2 ^ 63 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The sign-mask select `d ⊕ ((c ⊕ d) ∧ (0 - (t >> 63)))` picks `c` when bit 63 of `t`
    is set and `d` otherwise. -/
theorem mask_sel (c d t : BitVec 64) :
    d ^^^ ((c ^^^ d) &&& ((0 : BitVec 64) - (t >>> 63)))
      = if 2 ^ 63 ≤ t.toNat then c else d := by
  have ht := t.isLt
  by_cases h : 2 ^ 63 ≤ t.toNat
  · have h1 : t >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq; rw [shr63_toNat]; simp; omega
    rw [if_pos h, h1]
    have h2 : (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 := by decide
    simp only [h2, BitVec.and_allOnes]
    rw [BitVec.xor_comm c d, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · have h1 : t >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [shr63_toNat]; simp; omega
    rw [if_neg h, h1]
    simp

theorem and_mask63 (t : BitVec 64) :
    (t &&& 9223372036854775807#64).toNat = t.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_and]
  have : (9223372036854775807#64).toNat = 2 ^ 63 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-! ## Field addition -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (p25519 limbsNat outNat)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel (feAddBlock feSubBlock)

/-- The four words at `[b + 0], …, [b + 24]`, read little-endian. -/
def mem4 (M : JMem 64) (b : String) : Nat := limbsNat (M b 0) (M b 8) (M b 16) (M b 24)

/-- The carry equations of `feAddBlock`: the chain `e0 … e3` forms `d = x + y`, the chain
    `f0 … f3` forms `c = d + 19`, and the output is `c` with bit 255 cleared when bit 255
    of `c` is set, `d` otherwise. For `x + y < 2 · p25519` both chains have no carry out
    and the output is `(x + y) mod p25519`. -/
theorem add_arith (x0 x1 x2 x3 y0 y1 y2 y3 : Nat)
    (hxy : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3
      + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) < 2 * p25519)
    (D0 D1 D2 D3 C0 C1 C2 C3 c0 c1 c2 c3 g0 g1 g2 g3 : Nat)
    (hC0 : C0 < 2 ^ 64) (hC1 : C1 < 2 ^ 64) (hC2 : C2 < 2 ^ 64) (hC3 : C3 < 2 ^ 64)
    (e0 : D0 + 2 ^ 64 * c0 = x0 + y0)
    (e1 : D1 + 2 ^ 64 * c1 = x1 + y1 + c0)
    (e2 : D2 + 2 ^ 64 * c2 = x2 + y2 + c1)
    (e3 : D3 + 2 ^ 64 * c3 = x3 + y3 + c2)
    (f0 : C0 + 2 ^ 64 * g0 = D0 + 19)
    (f1 : C1 + 2 ^ 64 * g1 = D1 + 0 + g0)
    (f2 : C2 + 2 ^ 64 * g2 = D2 + 0 + g1)
    (f3 : C3 + 2 ^ 64 * g3 = D3 + 0 + g2) :
    (if 2 ^ 63 ≤ C3 then C0 + 2 ^ 64 * C1 + 2 ^ 128 * C2 + 2 ^ 192 * (C3 % 2 ^ 63)
      else D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3)
    = (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3
      + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3)) % p25519 := by
  unfold p25519 at *
  have hD : D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3 + 2 ^ 256 * c3
      = x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3
        + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    clear * - e0 e1 e2 e3; omega
  have hc3 : c3 = 0 := by clear * - hD hxy; omega
  subst hc3
  have hC : C0 + 2 ^ 64 * C1 + 2 ^ 128 * C2 + 2 ^ 192 * C3 + 2 ^ 256 * g3
      = D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3 + 19 := by
    clear * - f0 f1 f2 f3; omega
  have hg3 : g3 = 0 := by clear * - hC hD hxy; omega
  subst hg3
  clear e0 e1 e2 e3 f0 f1 f2 f3
  generalize x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3
    + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) = S at hD hxy ⊢
  split
  · have hm : C3 % 2 ^ 63 = C3 - 2 ^ 63 := by omega
    rw [hm, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The specification of `feAddBlock`: for `x + y < 2 · p25519` it stores
    `(x + y) mod p25519` at `z` and writes no other memory. -/
def AddSpec : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s → mem4 M "x" + mem4 M "y" < 2 * p25519 →
    Reach (fun _ M' => (∀ b o, b ≠ "z" → M' b o = M b o) ∧
      mem4 M' "z" = (mem4 M "x" + mem4 M "y") % p25519) (runBlock s feAddBlock)

theorem add_spec : AddSpec := by
  intro R cf of zf M s hs hxy
  simp only [feAddBlock]
  refine run_loadMem _ _ _ hs ?_; intro t0 hs0
  refine run_loadMem _ _ _ hs0 ?_; intro t1 hs1
  refine run_add _ _ hs1 ?_; intro D0 c0 q0 q1 e0 bc0 t2 hs2
  refine run_loadMem _ _ _ hs2 ?_; intro t3 hs3
  refine run_loadMem _ _ _ hs3 ?_; intro t4 hs4
  refine run_adc _ _ hs4 ?_; intro D1 c1 q2 q3 e1 bc1 hz1 t5 hs5
  refine run_loadMem _ _ _ hs5 ?_; intro t6 hs6
  refine run_loadMem _ _ _ hs6 ?_; intro t7 hs7
  refine run_adc _ _ hs7 ?_; intro D2 c2 q4 q5 e2 bc2 hz2 t8 hs8
  refine run_loadMem _ _ _ hs8 ?_; intro t9 hs9
  refine run_loadMem _ _ _ hs9 ?_; intro t10 hs10
  refine run_adc _ _ hs10 ?_; intro D3 c3 q6 q7 e3 bc3 hz3 t11 hs11
  refine run_mov _ _ hs11 ?_; intro t12 hs12
  refine run_add_op _ _ hs12 ?_; intro C0 g0 q8 q9 f0 bg0 t13 hs13
  refine run_mov _ _ hs13 ?_; intro t14 hs14
  refine run_adc _ _ hs14 ?_; intro C1 g1 q10 q11 f1 bg1 hz5 t15 hs15
  refine run_mov _ _ hs15 ?_; intro t16 hs16
  refine run_adc _ _ hs16 ?_; intro C2 g2 q12 q13 f2 bg2 hz6 t17 hs17
  refine run_mov _ _ hs17 ?_; intro t18 hs18
  refine run_adc _ _ hs18 ?_; intro C3 g3 q14 q15 f3 bg3 hz7 t19 hs19
  refine run_mov _ _ hs19 ?_; intro t20 hs20
  refine run_shr63 _ hs20 ?_; intro q16 q17 q18 t21 hs21
  refine run_neg _ hs21 ?_; intro q19 q20 q21 t22 hs22
  refine run_mov _ _ hs22 ?_; intro t23 hs23
  refine run_and_op _ _ hs23 ?_; intro q22 q23 q24 t24 hs24
  refine run_mov _ _ hs24 ?_; intro t25 hs25
  refine run_xor_op _ _ hs25 ?_; intro q25 q26 q27 t26 hs26
  refine run_and_op _ _ hs26 ?_; intro q28 q29 q30 t27 hs27
  refine run_xor_op _ _ hs27 ?_; intro q31 q32 q33 t28 hs28
  refine run_mov _ _ hs28 ?_; intro t29 hs29
  refine run_xor_op _ _ hs29 ?_; intro q34 q35 q36 t30 hs30
  refine run_and_op _ _ hs30 ?_; intro q37 q38 q39 t31 hs31
  refine run_xor_op _ _ hs31 ?_; intro q40 q41 q42 t32 hs32
  refine run_mov _ _ hs32 ?_; intro t33 hs33
  refine run_xor_op _ _ hs33 ?_; intro q43 q44 q45 t34 hs34
  refine run_and_op _ _ hs34 ?_; intro q46 q47 q48 t35 hs35
  refine run_xor_op _ _ hs35 ?_; intro q49 q50 q51 t36 hs36
  refine run_mov _ _ hs36 ?_; intro t37 hs37
  refine run_xor_op _ _ hs37 ?_; intro q52 q53 q54 t38 hs38
  refine run_and_op _ _ hs38 ?_; intro q55 q56 q57 t39 hs39
  refine run_xor_op _ _ hs39 ?_; intro q58 q59 q60 t40 hs40
  refine run_storeMem _ _ _ hs40 ?_; intro t41 hs41
  refine run_storeMem _ _ _ hs41 ?_; intro t42 hs42
  refine run_storeMem _ _ _ hs42 ?_; intro t43 hs43
  refine run_storeMem _ _ _ hs43 ?_; intro t44 hs44
  refine reach_nil hs44 ⟨fun b o hb => by simp [hb], ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Nat.zero_mod] at e0 e1 e2 e3 f0 f1 f2 f3
  simp only [mem4, limbsNat] at hxy
  have key := add_arith _ _ _ _ _ _ _ _ hxy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    C0.isLt C1.isLt C2.isLt C3.isLt e0 e1 e2 e3 f0 f1 f2 f3
  simp only [mem4, limbsNat, upd, opv, ↓reduceIte, String.reduceEq, and_self, mask_sel,
    Int.reduceEq, and_false]
  rw [← key]
  by_cases h : 2 ^ 63 ≤ C3.toNat
  · simp only [h, ↓reduceIte, and_mask63]
  · simp only [h, ↓reduceIte]

/-! ## Field subtraction -/

/-- `sbb c, 0` on `c = 0` followed by `and c, 19` leaves `19` times the incoming borrow. -/
theorem sbb_mask19 (W : BitVec 64) (a b : Bool) (h : 2 ^ 64 * cb a = W.toNat + cb b) :
    (W &&& 19#64).toNat = 19 * cb b := by
  have hW := W.isLt
  cases b <;> cases a <;> simp only [cb, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
    try omega
  · have : W = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this; decide
  · have : W = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this; decide

/-- The carry equations of `feSubBlock`: the borrow chain `e0 … e3` forms `d = x - y`
    with borrow `b3`, the chain `g0 … g3` subtracts `k = 19 · b3`, and the output clears
    bit 255. For `x < y + p25519` and `y ≤ x + p25519` the output is
    `(x + p25519 - y) mod p25519`. -/
theorem sub_arith (x0 x1 x2 x3 y0 y1 y2 y3 : Nat)
    (hx1 : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3
      < y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 + p25519)
    (hx2 : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3
      ≤ x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + p25519)
    (D0 D1 D2 D3 E0 E1 E2 E3 b0 b1 b2 b3 h0 h1 h2 h3 K : Nat)
    (hD0 : D0 < 2 ^ 64) (hD1 : D1 < 2 ^ 64) (hD2 : D2 < 2 ^ 64) (hD3 : D3 < 2 ^ 64)
    (hE0 : E0 < 2 ^ 64) (hE1 : E1 < 2 ^ 64) (hE2 : E2 < 2 ^ 64) (hE3 : E3 < 2 ^ 64)
    (bb3 : b3 ≤ 1) (hK : K = 19 * b3)
    (e0 : x0 + 2 ^ 64 * b0 = D0 + y0)
    (e1 : x1 + 2 ^ 64 * b1 = D1 + y1 + b0)
    (e2 : x2 + 2 ^ 64 * b2 = D2 + y2 + b1)
    (e3 : x3 + 2 ^ 64 * b3 = D3 + y3 + b2)
    (g0 : D0 + 2 ^ 64 * h0 = E0 + K)
    (g1 : D1 + 2 ^ 64 * h1 = E1 + 0 + h0)
    (g2 : D2 + 2 ^ 64 * h2 = E2 + 0 + h1)
    (g3 : D3 + 2 ^ 64 * h3 = E3 + 0 + h2) :
    E0 + 2 ^ 64 * E1 + 2 ^ 128 * E2 + 2 ^ 192 * (E3 % 2 ^ 63)
    = (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + p25519
      - (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3)) % p25519 := by
  unfold p25519 at *
  have hD : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * b3
      = D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3
        + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    clear * - e0 e1 e2 e3; omega
  have hE : D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3 + 2 ^ 256 * h3
      = E0 + 2 ^ 64 * E1 + 2 ^ 128 * E2 + 2 ^ 192 * E3 + K := by
    clear * - g0 g1 g2 g3; omega
  clear e0 e1 e2 e3 g0 g1 g2 g3
  generalize x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 = X at hD hx1 hx2 ⊢
  generalize y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = Y at hD hx1 hx2 ⊢
  subst hK
  have hEb : E0 + 2 ^ 64 * E1 + 2 ^ 128 * E2 < 2 ^ 192 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bb3 with rfl | rfl
  · have hh3 : h3 = 0 := by omega
    subst hh3
    have hm : E3 % 2 ^ 63 = E3 := Nat.mod_eq_of_lt (by omega)
    rw [hm, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · have hh3 : h3 = 0 := by omega
    subst hh3
    have hm : E3 % 2 ^ 63 = E3 - 2 ^ 63 := by omega
    rw [hm, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The specification of `feSubBlock`: for `x < y + p25519` and `y ≤ x + p25519` it stores
    `(x + p25519 - y) mod p25519` at `z` and writes no other memory. -/
def SubSpec : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s →
    mem4 M "x" < mem4 M "y" + p25519 → mem4 M "y" ≤ mem4 M "x" + p25519 →
    Reach (fun _ M' => (∀ b o, b ≠ "z" → M' b o = M b o) ∧
      mem4 M' "z" = (mem4 M "x" + p25519 - mem4 M "y") % p25519) (runBlock s feSubBlock)

theorem sub_spec : SubSpec := by
  intro R cf of zf M s hs hx1 hx2
  simp only [feSubBlock]
  refine run_loadMem _ _ _ hs ?_; intro t0 hs0
  refine run_loadMem _ _ _ hs0 ?_; intro t1 hs1
  refine run_sub _ _ hs1 ?_; intro D0 b0 q0 q1 e0 bb0 t2 hs2
  refine run_loadMem _ _ _ hs2 ?_; intro t3 hs3
  refine run_loadMem _ _ _ hs3 ?_; intro t4 hs4
  refine run_sbb _ _ hs4 ?_; intro D1 b1 q2 q3 e1 bb1 t5 hs5
  refine run_loadMem _ _ _ hs5 ?_; intro t6 hs6
  refine run_loadMem _ _ _ hs6 ?_; intro t7 hs7
  refine run_sbb _ _ hs7 ?_; intro D2 b2 q4 q5 e2 bb2 t8 hs8
  refine run_loadMem _ _ _ hs8 ?_; intro t9 hs9
  refine run_loadMem _ _ _ hs9 ?_; intro t10 hs10
  refine run_sbb _ _ hs10 ?_; intro D3 b3 q6 q7 e3 bb3 t11 hs11
  refine run_mov _ _ hs11 ?_; intro t12 hs12
  refine run_sbb _ _ hs12 ?_; intro W a q8 q9 eW ba t13 hs13
  refine run_and_op _ _ hs13 ?_; intro q10 q11 q12 t14 hs14
  refine run_mov _ _ hs14 ?_; intro t15 hs15
  refine run_sub _ _ hs15 ?_; intro E0 h0 q13 q14 g0 bh0 t16 hs16
  refine run_sbb _ _ hs16 ?_; intro E1 h1 q15 q16 g1 bh1 t17 hs17
  refine run_sbb _ _ hs17 ?_; intro E2 h2 q17 q18 g2 bh2 t18 hs18
  refine run_sbb _ _ hs18 ?_; intro E3 h3 q19 q20 g3 bh3 t19 hs19
  refine run_mov _ _ hs19 ?_; intro t20 hs20
  refine run_and_op _ _ hs20 ?_; intro q21 q22 q23 t21 hs21
  refine run_storeMem _ _ _ hs21 ?_; intro t22 hs22
  refine run_storeMem _ _ _ hs22 ?_; intro t23 hs23
  refine run_storeMem _ _ _ hs23 ?_; intro t24 hs24
  refine run_storeMem _ _ _ hs24 ?_; intro t25 hs25
  refine reach_nil hs25 ⟨fun b o hb => by simp [hb], ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.zero_mod, Nat.zero_add, add_zero] at e0 e1 e2 e3 eW g0 g1 g2 g3
  simp only [mem4, limbsNat] at hx1 hx2
  have key := sub_arith _ _ _ _ _ _ _ _ hx1 hx2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D0.isLt D1.isLt D2.isLt D3.isLt E0.isLt E1.isLt E2.isLt E3.isLt (cb_le_one b3)
    (sbb_mask19 W a b3 eW) e0 e1 e2 e3 g0 (by simpa using g1) (by simpa using g2)
    (by simpa using g3)
  simp only [mem4, limbsNat, upd, opv, ↓reduceIte, String.reduceEq, and_self,
    Int.reduceEq, and_false, and_mask63]
  exact key

/-! ## Machine-level statements for add and sub -/

theorem outNat_eq_mem4 (s : JState 64) : outNat s = mem4 s.mem "z" := rfl

/-- The abstract state of a two-input field operation: the values of `x`, `y` and `z`. -/
structure AFe where
  /-- The value of `x`. -/
  x : Nat
  /-- The value of `y`. -/
  y : Nat
  /-- The value of `z`. -/
  z : Nat

/-- The state relation: `x`, `y`, `z` are the four-word buffers at the memory names `"x"`,
    `"y"`, `"z"`. -/
def SRfe (st : JState 64) (a : AFe) : Prop :=
  mem4 st.mem "x" = a.x ∧ mem4 st.mem "y" = a.y ∧ mem4 st.mem "z" = a.z

/-- `feAddBlock` refines `z := (x + y) mod p25519` for `x + y < 2 · p25519`. -/
theorem feAddBlock_corresJ :
    CorresJ SRfe (fun a => a.x + a.y < 2 * p25519)
      (fun a => { a with z := (a.x + a.y) % p25519 }) feAddBlock := by
  intro st ⟨x, y, z⟩ ⟨hx, hy, _⟩ hlt
  subst hx hy
  obtain ⟨_, _, _, _, M', hs', hfr, hv⟩ := add_spec _ _ _ _ _ st (desc_self st) hlt
  refine ⟨?_, ?_, ?_⟩ <;> rw [hs'.mem]
  · simp only [mem4, hfr "x" _ (by decide)]
  · simp only [mem4, hfr "y" _ (by decide)]
  · exact hv

/-- `feSubBlock` refines `z := (x + p25519 - y) mod p25519` for `x < y + p25519` and
    `y ≤ x + p25519`. -/
theorem feSubBlock_corresJ :
    CorresJ SRfe (fun a => a.x < a.y + p25519 ∧ a.y ≤ a.x + p25519)
      (fun a => { a with z := (a.x + p25519 - a.y) % p25519 }) feSubBlock := by
  intro st ⟨x, y, z⟩ ⟨hx, hy, _⟩ ⟨h1, h2⟩
  subst hx hy
  obtain ⟨_, _, _, _, M', hs', hfr, hv⟩ := sub_spec _ _ _ _ _ st (desc_self st) h1 h2
  refine ⟨?_, ?_, ?_⟩ <;> rw [hs'.mem]
  · simp only [mem4, hfr "x" _ (by decide)]
  · simp only [mem4, hfr "y" _ (by decide)]
  · exact hv

/-- **`feAddBlock` computes addition modulo `p25519`.** For every machine state whose four
    words at `x` and `y` satisfy `x + y < 2 · p25519` (in particular for `x, y < p25519`),
    running `feAddBlock` stores at `[z + 0], …, [z + 24]` the value `(x + y) mod p25519`;
    so `z < p25519` and `z = x + y` in `ZMod p25519`. No memory outside `z` is written. -/
theorem feAddBlock_correct (st : JState 64)
    (h : mem4 st.mem "x" + mem4 st.mem "y" < 2 * p25519) :
    mem4 (runBlock st feAddBlock).mem "z" = (mem4 st.mem "x" + mem4 st.mem "y") % p25519 ∧
      mem4 (runBlock st feAddBlock).mem "z" < p25519 ∧
      ((mem4 (runBlock st feAddBlock).mem "z" : Nat) : ZMod p25519)
        = (mem4 st.mem "x" : ZMod p25519) + (mem4 st.mem "y" : Nat) ∧
      ∀ b o, b ≠ "z" → (runBlock st feAddBlock).mem b o = st.mem b o := by
  obtain ⟨_, _, _, _, M', hs', hfr, hv⟩ := add_spec _ _ _ _ _ st (desc_self st) h
  rw [hs'.mem, hv]
  refine ⟨rfl, Nat.mod_lt _ (by decide), ?_, hfr⟩
  rw [ZMod.natCast_mod]
  push_cast
  rfl

/-- **`feSubBlock` computes subtraction modulo `p25519`.** For every machine state whose
    four words at `x` and `y` satisfy `x < y + p25519` and `y ≤ x + p25519` (in particular
    for `x, y < p25519`), running `feSubBlock` stores at `[z + 0], …, [z + 24]` the value
    `(x + p25519 - y) mod p25519`; so `z < p25519` and `z = x - y` in `ZMod p25519`. No
    memory outside `z` is written. -/
theorem feSubBlock_correct (st : JState 64)
    (h1 : mem4 st.mem "x" < mem4 st.mem "y" + p25519)
    (h2 : mem4 st.mem "y" ≤ mem4 st.mem "x" + p25519) :
    mem4 (runBlock st feSubBlock).mem "z"
        = (mem4 st.mem "x" + p25519 - mem4 st.mem "y") % p25519 ∧
      mem4 (runBlock st feSubBlock).mem "z" < p25519 ∧
      ((mem4 (runBlock st feSubBlock).mem "z" : Nat) : ZMod p25519)
        = (mem4 st.mem "x" : ZMod p25519) - (mem4 st.mem "y" : Nat) ∧
      ∀ b o, b ≠ "z" → (runBlock st feSubBlock).mem b o = st.mem b o := by
  obtain ⟨_, _, _, _, M', hs', hfr, hv⟩ := sub_spec _ _ _ _ _ st (desc_self st) h1 h2
  rw [hs'.mem, hv]
  refine ⟨rfl, Nat.mod_lt _ (by decide), ?_, hfr⟩
  rw [ZMod.natCast_mod, Nat.cast_sub h2]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-! ## The comb table select, parametric in the number of entries -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel
  (entryStride combSelectBlock combSelect5Block combSelect6Block initState initState5
    initState6 outLimbs)

/-- One entry of the linear scan: compare the index with `j`, then conditionally move the
    four words at `[tbl + 32·j + 8·k]` into `a0 … a3`. -/
def selEntry (j : Nat) : List (JInstr 64) :=
  let base : Int := Int.ofNat j * entryStride
  [ .mov "mask" (.reg "d")
  , .sub "mask" (.imm j)
  , .loadMem "c" "tbl" (base + 0),  .cmove "a0" (.reg "c")
  , .loadMem "c" "tbl" (base + 8),  .cmove "a1" (.reg "c")
  , .loadMem "c" "tbl" (base + 16), .cmove "a2" (.reg "c")
  , .loadMem "c" "tbl" (base + 24), .cmove "a3" (.reg "c") ]

/-- The accumulator zeroing that precedes the scan. -/
def selPre : List (JInstr 64) :=
  [ .mov "a0" (.imm 0), .mov "a1" (.imm 0), .mov "a2" (.imm 0), .mov "a3" (.imm 0) ]

/-- The output stores that follow the scan. -/
def selPost : List (JInstr 64) :=
  [ .storeMem "z" 0 (.reg "a0"), .storeMem "z" 8 (.reg "a1")
  , .storeMem "z" 16 (.reg "a2"), .storeMem "z" 24 (.reg "a3") ]

/-- The `n`-entry constant-time select. -/
def selBlock (n : Nat) : List (JInstr 64) :=
  selPre ++ (List.range n).flatMap selEntry ++ selPost

theorem combSelectBlock_eq : combSelectBlock = selBlock 16 := rfl
theorem combSelect5Block_eq : combSelect5Block = selBlock 32 := rfl
theorem combSelect6Block_eq : combSelect6Block = selBlock 64 := rfl

/-- The accumulator word at offset `off` after the entries `0, …, k - 1`: the word of
    entry `D` when `D < k`, and `0` otherwise. -/
def selAcc (M : JMem 64) (D : BitVec 64) (k : Nat) (off : Int) : BitVec 64 :=
  if D.toNat < k then M "tbl" (Int.ofNat D.toNat * entryStride + off) else 0

/-- The scan invariant after the entries `0, …, k - 1`: memory is `M`, register `d` holds
    `D`, and `a0 … a3` hold `selAcc M D k` at offsets `0, 8, 16, 24`. -/
def SelInv (M : JMem 64) (D : BitVec 64) (k : Nat) (st : JState 64) : Prop :=
  ∃ R cf of zf, Desc R cf of zf M st ∧ R "d" = D ∧ R "a0" = selAcc M D k 0 ∧
    R "a1" = selAcc M D k 8 ∧ R "a2" = selAcc M D k 16 ∧ R "a3" = selAcc M D k 24

theorem selAcc_succ (M : JMem 64) (D : BitVec 64) (j : Nat) (hj : j < 2 ^ 64) (off : Int) :
    (if D = BitVec.ofNat 64 j then M "tbl" (Int.ofNat j * entryStride + off)
      else selAcc M D j off) = selAcc M D (j + 1) off := by
  unfold selAcc
  by_cases h : D = BitVec.ofNat 64 j
  · have hD : D.toNat = j := by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
    rw [if_pos h, hD, if_pos (by omega)]
  · have hD : D.toNat ≠ j := fun e => h (BitVec.eq_of_toNat_eq
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]; exact e))
    rw [if_neg h]
    by_cases hlt : D.toNat < j
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- One scan entry advances the invariant from `j` to `j + 1`. -/
theorem selEntry_corresJ (M : JMem 64) (D : BitVec 64) (j : Nat) :
    CorresJ (fun st k => SelInv M D k st) (fun k => k = j ∧ j < 2 ^ 64) (fun k => k + 1) (selEntry j) := by
  intro st k ⟨R, cf, of, zf, hs, hd, h0, h1, h2, h3⟩ ⟨hk, hj⟩
  subst hk
  simp only [selEntry]
  refine run_mov _ _ hs ?_; intro t0 hs0
  refine run_sub_imm _ _ hs0 ?_; intro q0 q1 t1 hs1
  refine run_loadMem _ _ _ hs1 ?_; intro t2 hs2
  refine run_cmove _ _ hs2 ?_; intro t3 hs3
  refine run_loadMem _ _ _ hs3 ?_; intro t4 hs4
  refine run_cmove _ _ hs4 ?_; intro t5 hs5
  refine run_loadMem _ _ _ hs5 ?_; intro t6 hs6
  refine run_cmove _ _ hs6 ?_; intro t7 hs7
  refine run_loadMem _ _ _ hs7 ?_; intro t8 hs8
  refine run_cmove _ _ hs8 ?_; intro t9 hs9
  refine ⟨_, _, _, _, hs9, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd, opv, ↓reduceIte, String.reduceEq, hd, h0, h1, h2, h3, decide_eq_true_eq] <;>
    exact selAcc_succ M D _ hj _

theorem selScan_inv (M : JMem 64) (D : BitVec 64) (st : JState 64) :
    ∀ k, k ≤ 2 ^ 64 → SelInv M D 0 st →
      SelInv M D k (runBlock st ((List.range k).flatMap selEntry)) := by
  intro k
  induction k with
  | zero => intro _ h; exact h
  | succ k ih =>
    intro hk h
    rw [List.range_succ, List.flatMap_append, runBlock_append, List.flatMap_singleton]
    exact selEntry_corresJ M D k _ k (ih (by omega) h) ⟨rfl, by omega⟩

/-- **The `n`-entry select stores the table entry at the index.** For every machine state
    whose register `d` holds an index `D < n` (with `n ≤ 2^64`), running `selBlock n`
    stores at `[z + 8·k]` the word at `[tbl + 32·D + 8·k]`, for `k < 4`. No memory outside
    `z` is written. -/
theorem selBlock_correct (n : Nat) (hn : n ≤ 2 ^ 64) (st : JState 64)
    (hd : (st.regs "d").toNat < n) :
    (∀ k : Nat, k < 4 →
      (runBlock st (selBlock n)).mem "z" (8 * (k : Int))
        = st.mem "tbl" (32 * ((st.regs "d").toNat : Int) + 8 * (k : Int))) ∧
      ∀ b o, b ≠ "z" → (runBlock st (selBlock n)).mem b o = st.mem b o := by
  have hs := desc_self st
  have hpre : SelInv st.mem (st.regs "d") 0 (runBlock st selPre) := by
    simp only [selPre]
    refine run_mov _ _ hs ?_; intro t0 hs0
    refine run_mov _ _ hs0 ?_; intro t1 hs1
    refine run_mov _ _ hs1 ?_; intro t2 hs2
    refine run_mov _ _ hs2 ?_; intro t3 hs3
    refine ⟨_, _, _, _, hs3, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [upd, opv, selAcc]
  obtain ⟨R, cf, of, zf, hs1, _, h0, h1, h2, h3⟩ :=
    selScan_inv _ _ _ n hn hpre
  have key : Reach (fun _ M' => (∀ b o, b ≠ "z" → M' b o = st.mem b o) ∧
      M' "z" 0 = R "a0" ∧ M' "z" 8 = R "a1" ∧ M' "z" 16 = R "a2" ∧ M' "z" 24 = R "a3")
      (runBlock (runBlock (runBlock st selPre) ((List.range n).flatMap selEntry)) selPost) := by
    simp only [selPost]
    refine run_storeMem _ _ _ hs1 ?_; intro t0 hs0
    refine run_storeMem _ _ _ hs0 ?_; intro t1 hs1'
    refine run_storeMem _ _ _ hs1' ?_; intro t2 hs2
    refine run_storeMem _ _ _ hs2 ?_; intro t3 hs3
    refine reach_nil hs3 ⟨fun b o hb => by simp [hb], ?_⟩
    simp
  obtain ⟨_, _, _, _, M', hs', hfr, e0, e1, e2, e3⟩ := key
  rw [selBlock, runBlock_append, runBlock_append, hs'.mem]
  refine ⟨?_, hfr⟩
  intro k hk
  have hsel : ∀ off : Int, selAcc st.mem (st.regs "d") n off
      = st.mem "tbl" (32 * ((st.regs "d").toNat : Int) + off) := by
    intro off
    simp only [selAcc, if_pos hd, entryStride, Int.ofNat_eq_natCast]
    rw [Int.mul_comm]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · simpa [hsel] using e0.trans h0
  · simpa [hsel] using e1.trans h1
  · simpa [hsel] using e2.trans h2
  · simpa [hsel] using e3.trans h3

/-- **`combSelectBlock` selects the table entry at the index.** For an index `D < 16` in
    register `d`, the four words stored at `z` are the words of entry `D` of the table at
    `tbl`. -/
theorem combSelectBlock_correct (st : JState 64) (hd : (st.regs "d").toNat < 16) :
    (∀ k : Nat, k < 4 →
      (runBlock st combSelectBlock).mem "z" (8 * (k : Int))
        = st.mem "tbl" (32 * ((st.regs "d").toNat : Int) + 8 * (k : Int))) ∧
      ∀ b o, b ≠ "z" → (runBlock st combSelectBlock).mem b o = st.mem b o :=
  combSelectBlock_eq ▸ selBlock_correct 16 (by norm_num) st hd

/-- **`combSelect5Block` selects the table entry at the index**, for an index `D < 32`. -/
theorem combSelect5Block_correct (st : JState 64) (hd : (st.regs "d").toNat < 32) :
    (∀ k : Nat, k < 4 →
      (runBlock st combSelect5Block).mem "z" (8 * (k : Int))
        = st.mem "tbl" (32 * ((st.regs "d").toNat : Int) + 8 * (k : Int))) ∧
      ∀ b o, b ≠ "z" → (runBlock st combSelect5Block).mem b o = st.mem b o :=
  combSelect5Block_eq ▸ selBlock_correct 32 (by norm_num) st hd

/-- **`combSelect6Block` selects the table entry at the index**, for an index `D < 64`. -/
theorem combSelect6Block_correct (st : JState 64) (hd : (st.regs "d").toNat < 64) :
    (∀ k : Nat, k < 4 →
      (runBlock st combSelect6Block).mem "z" (8 * (k : Int))
        = st.mem "tbl" (32 * ((st.regs "d").toNat : Int) + 8 * (k : Int))) ∧
      ∀ b o, b ≠ "z" → (runBlock st combSelect6Block).mem b o = st.mem b o :=
  combSelect6Block_eq ▸ selBlock_correct 64 (by norm_num) st hd

theorem tbl_off_toNat (j k : Nat) :
    (32 * (j : Int) + 8 * (k : Int)).toNat = 32 * j + 8 * k := by
  omega

/-- **`combSelectBlock` on the kernel's table state.** From `initState tab didx` with
    `didx < 16`, limb `k` of the output is limb `k` of `tab didx`. -/
theorem combSelectBlock_initState (tab : Fin 16 → Fin 4 → BitVec 64) (didx : BitVec 64)
    (hd : didx.toNat < 16) (k : Fin 4) :
    outLimbs (runBlock (initState tab didx) combSelectBlock) k = tab ⟨didx.toNat, hd⟩ k := by
  have hr : (initState tab didx).regs "d" = didx := by simp [initState]
  have h := (combSelectBlock_correct (initState tab didx) (by rw [hr]; exact hd)).1 k.val k.isLt
  simp only [outLimbs, JState.load]
  rw [h, hr]
  simp only [initState, ↓reduceIte, tbl_off_toNat]
  rw [if_pos (by omega)]
  exact congrArg₂ tab (Fin.ext (by show _ % 16 = didx.toNat; omega))
    (Fin.ext (by show _ % 4 = k.val; omega))

/-- **`combSelect5Block` on the kernel's table state**, for `didx < 32`. -/
theorem combSelect5Block_initState (tab : Fin 32 → Fin 4 → BitVec 64) (didx : BitVec 64)
    (hd : didx.toNat < 32) (k : Fin 4) :
    outLimbs (runBlock (initState5 tab didx) combSelect5Block) k = tab ⟨didx.toNat, hd⟩ k := by
  have hr : (initState5 tab didx).regs "d" = didx := by simp [initState5]
  have h := (combSelect5Block_correct (initState5 tab didx) (by rw [hr]; exact hd)).1 k.val
    k.isLt
  simp only [outLimbs, JState.load]
  rw [h, hr]
  simp only [initState5, ↓reduceIte, tbl_off_toNat]
  rw [if_pos (by omega)]
  exact congrArg₂ tab (Fin.ext (by show _ % 32 = didx.toNat; omega))
    (Fin.ext (by show _ % 4 = k.val; omega))

/-- **`combSelect6Block` on the kernel's table state**, for `didx < 64`. -/
theorem combSelect6Block_initState (tab : Fin 64 → Fin 4 → BitVec 64) (didx : BitVec 64)
    (hd : didx.toNat < 64) (k : Fin 4) :
    outLimbs (runBlock (initState6 tab didx) combSelect6Block) k = tab ⟨didx.toNat, hd⟩ k := by
  have hr : (initState6 tab didx).regs "d" = didx := by simp [initState6]
  have h := (combSelect6Block_correct (initState6 tab didx) (by rw [hr]; exact hd)).1 k.val
    k.isLt
  simp only [outLimbs, JState.load]
  rw [h, hr]
  simp only [initState6, ↓reduceIte, tbl_off_toNat]
  rw [if_pos (by omega)]
  exact congrArg₂ tab (Fin.ext (by show _ % 64 = didx.toNat; omega))
    (Fin.ext (by show _ % 4 = k.val; omega))

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof
