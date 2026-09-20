/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Proof
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel

/-!
# Correctness of the Curve25519 field-multiply and field-square blocks

This module proves that `Fe25519MulKernel.feMulBlock` and `Fe25519OpsKernel.feSqrBlock`
compute the product and the square modulo `p25519 = 2^255 - 19` under `runBlock`, for all
four-limb inputs. The output is canonical: the stored value is below `p25519`.

## Memory and calling convention

`JState.mem` is keyed by the base register's name. Both blocks read `x` from the bank
`"x"`, `feMulBlock` reads `y` from the bank `"y"`, and both write `z` to the bank `"z"`;
the four limbs at offsets `0, 8, 16, 24` are read little-endian by `mem4`. Distinct names
are distinct banks, so an output buffer aliasing an input buffer is outside the model.
`feSqrBlock` is `feMulBlock` with the multiplier bank `"y"` replaced by `"x"`
(`feMulBlock_eq`, `feSqrBlock_eq`), so one proof, parametric in the multiplier bank `yb`,
covers both.

## Proof structure

* Transport lemmas: the instruction forms of `S2nMontmulP384Proof` (`run_mov`,
  `run_mulxMem`, `run_adcx`, …) are reused over its state description `Desc`; this module
  adds `run_shl_imm`, `run_shr_imm`, `run_imul_imm`, `run_add_imm` and `run_and`.
* Seven segments (`fieldSegs`): the first multiply row (`row0Seg`, `row0_spec`,
  `row0_arith`), three further rows (`rowSeg`, `row1_spec` … `row3_spec`, `row_arith`),
  the quotient estimate (`quotSeg`, `quot_spec`, `quot_arith`), the fold of `38 · h` with
  the `19 · q` correction (`foldSeg`, `fold_spec`, `fold_arith`) and the canonical
  correction with the output stores (`finalSeg`, `final_spec`, `final_arith`). Every
  segment specification holds on all inputs.
* The abstract reduction `redAbs` (quotient estimate `qOf`, fold `foldF`, correction
  `finalZ`) equals `T mod p25519` for every `T < 2^512` (`redAbs_eq`). The estimate
  `q = ⌊(38 · h₃ + l₃) / 2^63⌋ + 1` satisfies `(q - 1) · 2^255 ≤ l + 38 · h < q · 2^255 +
  38 · 2^192`, so `l + 38 · h - q · p25519` lies in `[-p25519, p25519)`; bit `255` of the
  folded value, compared with the parity of `q` (`sign_bit`), tells the two cases apart.
* Each segment specification gives a `CorresJ (SRf yb)` step over the abstract state
  `AFe` (`corresJ_row0` … `corresJ_final`), and `corresJ_append` composes the seven.

## Main results

* `fieldSegs_corresJ`, `feMulBlock_corresJ`, `feSqrBlock_corresJ`: the blocks refine the
  abstract field multiply `fieldAbs` through `SRf`.
* `redAbs_eq`: the fused-quotient reduction is exact on all eight-limb values.
* `feMulBlock_mod`, `feSqrBlock_mod`: the stored value is `x · y mod p25519`,
  respectively `x² mod p25519`.
* `feMulBlock_correct`, `feSqrBlock_correct`: the stored value is below `p25519` and
  equals `x · y`, respectively `x²`, in `ZMod p25519`.
* `feMulComputes_all`, `feSqr_initState1`: the same statements from the kernel modules'
  initial states, in terms of `Fe25519MulKernel.limbsNat`.

Provenance class: `@proved-hand-kernel theorems: feMulBlock_correct, feSqrBlock_correct`.
-/

@[expose] public section

set_option autoImplicit false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
  (cb cb_le_one upd opv Desc Desc.eval Reach reach_nil cb_false run_mov run_loadMem
    run_xor_self run_mulxMem run_mulx run_adcx run_adox run_adc run_add run_sub run_sbb
    run_storeMem desc_self ydig)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (p25519 limbsNat)

section Transport

variable {Q : JState 64 → Prop} {rest : List (JInstr 64)} {R : String → BitVec 64}
  {cf of zf : Bool} {M : JMem 64} {s : JState 64}

/-- An instruction whose register effect is `R'` and which leaves memory unchanged. -/
theorem run_regs (i : JInstr 64) (R' : String → BitVec 64) (_hs : Desc R cf of zf M s)
    (hr : ∀ r, (evalInstr s i).regs r = R' r) (hm : (evalInstr s i).mem = M)
    (h : ∀ (c o' z : Bool) t, Desc R' c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (i :: rest)) := by
  rw [runBlock_cons]
  exact h _ _ _ _ ⟨funext hr, hm, rfl, rfl, rfl⟩

theorem run_shl_imm (d : String) (k : Nat) (hk0 : 0 < k) (hk : k < 64)
    (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool), w.toNat = (R d).toNat * 2 ^ k % 2 ^ 64 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.shl d (.imm k) :: rest)) := by
  have hv : (R d <<< k).toNat = (R d).toNat * 2 ^ k % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  refine run_regs _ (upd R d (R d <<< k)) hs ?_ hs.mem (fun c o' z => h _ c o' z hv)
  intro r
  have hk' : k % 64 = k := Nat.mod_eq_of_lt hk
  have hk'' : k ≠ 0 := by omega
  simp [evalInstr, JState.writeB5W, x86_SHL, shiftCount, rflags_OF, wshl, upd, hs.regs,
    hk', hk'', Nat.min_eq_right hk.le]

theorem run_shr_imm (d : String) (k : Nat) (hk0 : 0 < k) (hk : k < 64)
    (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool), w.toNat = (R d).toNat / 2 ^ k →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.shr d (.imm k) :: rest)) := by
  have hv : (R d >>> k).toNat = (R d).toNat / 2 ^ k := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine run_regs _ (upd R d (R d >>> k)) hs ?_ hs.mem (fun c o' z => h _ c o' z hv)
  intro r
  have hk' : k % 64 = k := Nat.mod_eq_of_lt hk
  have hk'' : k ≠ 0 := by omega
  simp [evalInstr, JState.writeB5W, x86_SHR, shiftCount, rflags_OF, wshr, upd, hs.regs,
    hk', hk'', Nat.min_eq_right hk.le]

theorem run_imul_imm (d : String) (k : Nat) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool), w.toNat = (R d).toNat * (k % 2 ^ 64) % 2 ^ 64 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.imul d (.imm k) :: rest)) := by
  have hv : (R d * BitVec.ofNat 64 k).toNat = (R d).toNat * (k % 2 ^ 64) % 2 ^ 64 := by
    simp [BitVec.toNat_mul]
  refine run_regs _ (upd R d (R d * BitVec.ofNat 64 k)) hs ?_ hs.mem
    (fun c o' z => h _ c o' z hv)
  intro r
  simp [evalInstr, JState.writeB5W, x86_IMULt, rflags_of_mul, upd, hs.regs]

theorem run_add_imm (d : String) (k : Nat) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool),
      w.toNat + 2 ^ 64 * cb c = (R d).toNat + k % 2 ^ 64 → cb c ≤ 1 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.add d (.imm k) :: rest)) := by
  rw [runBlock_cons]
  have hx := (R d).isLt
  have hy : k % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hf := S2nMontmulP384.addc_fact _ _ _ hx hy (Nat.zero_le 1)
  simp only [Nat.add_zero] at hf
  refine h (BitVec.ofNat 64 ((R d).toNat + k % 2 ^ 64))
    (decide (2 ^ 64 ≤ (R d).toNat + k % 2 ^ 64)) _ _ hf (cb_le_one _) _
    ⟨?_, hs.mem, ?_, rfl, rfl⟩
  · funext r
    simp only [evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop, JState.get,
      JOperand.eval, upd, hs.regs]
    split
    · apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]
    · rfl
  · simp only [evalInstr, JOperand.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_ADD, rflags_of_aluop, wunsigned,
      BitVec.toNat_add, BitVec.toNat_ofNat, Option.getD_some]
    apply decide_eq_decide.mpr
    constructor <;> intro <;> omega

theorem run_and (d src : String) (hs : Desc R cf of zf M s)
    (h : ∀ (c o' z : Bool) t, Desc (upd R d (R d &&& R src)) c o' z M t →
      Q (runBlock t rest)) :
    Q (runBlock s (.and_ d (.reg src) :: rest)) := by
  refine run_regs _ _ hs ?_ hs.mem h
  intro r
  simp [evalInstr, JState.writeB5W, x86_AND, rflags_of_bwop, upd, hs.regs]

end Transport

theorem and_mask_toNat (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 0x7fffffffffffffff).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have : (0x7fffffffffffffff : Nat) % 2 ^ 64 = 2 ^ 63 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-! ## Limb arithmetic of the segments -/

/-- The carry equations of the first multiply row: one `CF` chain adds each high word to
    the low word of the next product; the carry out of the top limb is zero because the
    product is below `2^320`. -/
theorem row0_arith (p0 p1 p2 p3 h0 l0 h1 l1 h2 l2 h3 l3 : Nat)
    (m0 : h0 * 2 ^ 64 + l0 = p0) (m1 : h1 * 2 ^ 64 + l1 = p1) (m2 : h2 * 2 ^ 64 + l2 = p2)
    (m3 : h3 * 2 ^ 64 + l3 = p3)
    (hP : p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 < 2 ^ 320)
    (A1 A2 A3 A4 c1 c2 c3 c4 : Nat)
    (e1 : A1 + 2 ^ 64 * c1 = h0 + l1 + 0)
    (e2 : A2 + 2 ^ 64 * c2 = h1 + l2 + c1)
    (e3 : A3 + 2 ^ 64 * c3 = h2 + l3 + c2)
    (e4 : A4 + 2 ^ 64 * c4 = h3 + 0 + c3) :
    l0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3 + 2 ^ 256 * A4
      = p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 := by
  omega

/-- The carry equations of a later multiply row: the `CF` chain `e0 … e4` and the `OF`
    chain `f0 … f3` add the four partial products to the four-limb window; both carries
    out of the fifth limb are zero because the window plus the product is below
    `2^320`. -/
theorem row_arith (a0 a1 a2 a3 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64)
    (p0 p1 p2 p3 h0 l0 h1 l1 h2 l2 h3 l3 : Nat)
    (m0 : h0 * 2 ^ 64 + l0 = p0) (m1 : h1 * 2 ^ 64 + l1 = p1) (m2 : h2 * 2 ^ 64 + l2 = p2)
    (m3 : h3 * 2 ^ 64 + l3 = p3)
    (hP : p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 ≤ 2 ^ 320)
    (A0 A1 A2 A3 A4 B1 B2 B3 B4 c0 c1 c2 c3 c4 o1 o2 o3 o4 : Nat)
    (e0 : A0 + 2 ^ 64 * c0 = a0 + l0 + 0)
    (f0 : B1 + 2 ^ 64 * o1 = a1 + h0 + 0)
    (e1 : A1 + 2 ^ 64 * c1 = B1 + l1 + c0)
    (f1 : B2 + 2 ^ 64 * o2 = a2 + h1 + o1)
    (e2 : A2 + 2 ^ 64 * c2 = B2 + l2 + c1)
    (f2 : B3 + 2 ^ 64 * o3 = a3 + h2 + o2)
    (e3 : A3 + 2 ^ 64 * c3 = B3 + l3 + c2)
    (f3 : B4 + 2 ^ 64 * o4 = h3 + 0 + o3)
    (e4 : A4 + 2 ^ 64 * c4 = B4 + 0 + c3) :
    A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3 + 2 ^ 256 * A4
      = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3
        + (p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3) := by
  omega

/-- The carry equations of the quotient estimate: `hi · 2^64 + lo = 38 · h₃ + l₃` is
    formed by `mulx`/`add`/`adc`, and `q = 2 · hi + ⌊lo / 2^63⌋ + 1` by `shr`/`shl`/`add`;
    no step overflows, so `q = ⌊(38 · h₃ + l₃) / 2^63⌋ + 1 ≤ 78`. -/
theorem quot_arith (h3 l3 : Nat) (hh : h3 < 2 ^ 64) (hl : l3 < 2 ^ 64)
    (Hq Lq E0 k1 E1 k2 Y1 E2 E3 k3 Q k4 : Nat) (hE0 : E0 < 2 ^ 64) (hE1 : E1 < 2 ^ 64)
    (bk1 : k1 ≤ 1)
    (m : Hq * 2 ^ 64 + Lq = 38 * h3)
    (e1 : E0 + 2 ^ 64 * k1 = Lq + l3)
    (e2 : E1 + 2 ^ 64 * k2 = Hq + 0 + k1)
    (eY : Y1 = E0 / 2 ^ 63)
    (eS : E2 = E1 * 2 ^ 1 % 2 ^ 64)
    (e3 : E3 + 2 ^ 64 * k3 = E2 + Y1)
    (e4 : Q + 2 ^ 64 * k4 = E3 + 1) :
    Q = (38 * h3 + l3) / 2 ^ 63 + 1 ∧ Q ≤ 78 := by
  have hHq : Hq ≤ 37 := by clear * - m hh; omega
  have hE1v : E1 = Hq + k1 := by clear * - e2 hHq bk1 hE1; omega
  have hE2v : E2 = 2 * E1 := by
    rw [eS, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; ring
  have hY1 : Y1 ≤ 1 := by clear * - eY hE0; omega
  have hE3v : E3 = E2 + Y1 := by clear * - e3 hE2v hE1v hHq bk1 hY1; omega
  have hQv : Q = E3 + 1 := by clear * - e4 hE3v hE2v hE1v hHq bk1 hY1; omega
  have hsum : 38 * h3 + l3 = 2 ^ 64 * E1 + E0 := by clear * - m e1 e2 hE1v; omega
  rw [hsum]
  clear * - hQv hE3v hE2v hE1v hHq bk1 eY hY1 hE0
  omega

/-- The carry equations of the fold: the `OF` chain adds `G` and the high words of
    `38 · hᵢ`, the `CF` chain adds the low words; the four limbs hold
    `(l + 38 · h + G) mod 2^256`. -/
theorem fold_arith (l0 l1 l2 l3 h0 h1 h2 h3 G : Nat)
    (H0 L0 H1 L1 H2 L2 H3 L3 U0 U1 U2 U3 S0 S1 S2 S3 o1 o2 o3 o4 c1 c2 c3 c4 : Nat)
    (hS0 : S0 < 2 ^ 64) (hS1 : S1 < 2 ^ 64) (hS2 : S2 < 2 ^ 64) (hS3 : S3 < 2 ^ 64)
    (f0 : U0 + 2 ^ 64 * o1 = l0 + G + 0)
    (m0 : H0 * 2 ^ 64 + L0 = 38 * h0)
    (e0 : S0 + 2 ^ 64 * c1 = U0 + L0 + 0)
    (f1 : U1 + 2 ^ 64 * o2 = l1 + H0 + o1)
    (m1 : H1 * 2 ^ 64 + L1 = 38 * h1)
    (e1 : S1 + 2 ^ 64 * c2 = U1 + L1 + c1)
    (f2 : U2 + 2 ^ 64 * o3 = l2 + H1 + o2)
    (m2 : H2 * 2 ^ 64 + L2 = 38 * h2)
    (e2 : S2 + 2 ^ 64 * c3 = U2 + L2 + c2)
    (f3 : U3 + 2 ^ 64 * o4 = l3 + H2 + o3)
    (m3 : H3 * 2 ^ 64 + L3 = 38 * h3)
    (e3 : S3 + 2 ^ 64 * c4 = U3 + L3 + c3) :
    S0 + 2 ^ 64 * S1 + 2 ^ 128 * S2 + 2 ^ 192 * S3
      = (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3
          + 38 * (h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2 + 2 ^ 192 * h3) + G) % 2 ^ 256 := by
  have key : S0 + 2 ^ 64 * S1 + 2 ^ 128 * S2 + 2 ^ 192 * S3 + 2 ^ 256 * (o4 + c4 + H3)
      = l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3
          + 38 * (h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2 + 2 ^ 192 * h3) + G := by
    zify at *
    linear_combination e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3 + f0 + 2 ^ 64 * f1
      + 2 ^ 128 * f2 + 2 ^ 192 * f3 + m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3
  rw [← key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  clear * - hS0 hS1 hS2 hS3
  omega

/-- The canonical correction: with `sg` the sign bit of `⌊S / 2^192⌋ − (q mod 2) · 2^63`
    (mod `2^64`), subtract `19 · sg` from `S` modulo `2^256` and clear bit `255`. -/
def finalZ (S q : Nat) : Nat :=
  (S + 2 ^ 256 - 19 * ((S / 2 ^ 192 + 2 ^ 64 - q % 2 * 2 ^ 63) % 2 ^ 64 / 2 ^ 63))
    % 2 ^ 256 % 2 ^ 255

/-- The carry equations of the canonical correction segment. -/
theorem final_arith (s0 s1 s2 s3 q : Nat) (hs0 : s0 < 2 ^ 64) (hs1 : s1 < 2 ^ 64)
    (hs2 : s2 < 2 ^ 64) (hs3 : s3 < 2 ^ 64)
    (Y D b sg amt Z0 Z1 Z2 Z3 b0 b1 b2 b3 : Nat) (hD : D < 2 ^ 64) (hZ0 : Z0 < 2 ^ 64)
    (hZ1 : Z1 < 2 ^ 64) (hZ2 : Z2 < 2 ^ 64) (hZ3 : Z3 < 2 ^ 64) (bb3 : b3 ≤ 1)
    (eY : Y = q * 2 ^ 63 % 2 ^ 64)
    (eD : s3 + 2 ^ 64 * b = D + Y)
    (eg : sg = D / 2 ^ 63)
    (ea : amt = sg * 19 % 2 ^ 64)
    (e0 : s0 + 2 ^ 64 * b0 = Z0 + amt)
    (e1 : s1 + 2 ^ 64 * b1 = Z1 + 0 + b0)
    (e2 : s2 + 2 ^ 64 * b2 = Z2 + 0 + b1)
    (e3 : s3 + 2 ^ 64 * b3 = Z3 + 0 + b2) :
    Z0 + 2 ^ 64 * Z1 + 2 ^ 128 * Z2 + 2 ^ 192 * (Z3 % 2 ^ 63)
      = finalZ (s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3) q := by
  unfold finalZ
  have hS3 : (s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3) / 2 ^ 192 = s3 := by
    clear * - hs0 hs1 hs2 hs3; omega
  have hSlt : s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 < 2 ^ 256 := by
    clear * - hs0 hs1 hs2 hs3; omega
  rw [hS3]
  generalize hS : s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 = S at hSlt
  have hYv : Y = q % 2 * 2 ^ 63 := by clear * - eY; omega
  have hDv : D = (s3 + 2 ^ 64 - q % 2 * 2 ^ 63) % 2 ^ 64 := by
    clear * - eD hYv hD hs3; omega
  have hsg : sg ≤ 1 := by clear * - eg hD; omega
  have hamt : amt = 19 * sg := by clear * - ea hsg; omega
  rw [← hDv, ← eg, ← hamt]
  have hchain : Z0 + 2 ^ 64 * Z1 + 2 ^ 128 * Z2 + 2 ^ 192 * Z3 + amt
      = S + 2 ^ 256 * b3 := by
    rw [← hS]; clear * - e0 e1 e2 e3; omega
  have hZ : Z0 + 2 ^ 64 * Z1 + 2 ^ 128 * Z2 + 2 ^ 192 * (Z3 % 2 ^ 63)
      = (Z0 + 2 ^ 64 * Z1 + 2 ^ 128 * Z2 + 2 ^ 192 * Z3) % 2 ^ 255 := by
    clear * - hZ0 hZ1 hZ2 hZ3; omega
  have hZlt : Z0 + 2 ^ 64 * Z1 + 2 ^ 128 * Z2 + 2 ^ 192 * Z3 < 2 ^ 256 := by
    clear * - hZ0 hZ1 hZ2 hZ3; omega
  rw [hZ]
  congr 1
  generalize Z0 + 2 ^ 64 * Z1 + 2 ^ 128 * Z2 + 2 ^ 192 * Z3 = Zv at hchain hZlt
  clear * - hchain hZlt hSlt hamt hsg bb3
  omega

/-! ## The abstract reduction -/

/-- The quotient estimate of the reduction of an eight-limb value `T`:
    `⌊(38 · h₃ + l₃) / 2^63⌋ + 1`, with `h₃`, `l₃` the top limbs of the high and low
    halves. -/
def qOf (T : Nat) : Nat := (38 * (T / 2 ^ 448) + T / 2 ^ 192 % 2 ^ 64) / 2 ^ 63 + 1

/-- The fold `(l + 38 · h + 19 · q) mod 2^256` of the halves `l`, `h` of `T`. -/
def foldF (T q : Nat) : Nat := (T % 2 ^ 256 + 38 * (T / 2 ^ 256) + 19 * q) % 2 ^ 256

/-- The abstract reduction of an eight-limb value: fold with the quotient correction,
    then the canonical correction. -/
def redAbs (T : Nat) : Nat := finalZ (foldF T (qOf T)) (qOf T)

/-- The sign bit read by the canonical correction is the exclusive or of bit `255` of the
    folded value and the parity of `q`. -/
theorem sign_bit (c r D : Nat) (hc : c ≤ 1) (hr : r ≤ 1) (hD : D < 2 ^ 255) :
    ((2 ^ 255 * c + D) / 2 ^ 192 + 2 ^ 64 - r * 2 ^ 63) % 2 ^ 64 / 2 ^ 63 = (c + r) % 2 := by
  have h1 : (2 ^ 255 * c + D) / 2 ^ 192 = 2 ^ 63 * c + D / 2 ^ 192 := by omega
  have h2 : D / 2 ^ 192 < 2 ^ 63 := by omega
  rw [h1]
  generalize D / 2 ^ 192 = e at h2
  interval_cases c <;> interval_cases r <;> omega

/-- **The fused-quotient reduction is exact on all eight-limb values.** For every
    `T < 2^512`, `redAbs T = T mod p25519`. -/
theorem redAbs_eq (T : Nat) (hT : T < 2 ^ 512) : redAbs T = T % p25519 := by
  unfold redAbs qOf foldF finalZ p25519
  have hH : T / 2 ^ 256 < 2 ^ 256 := by omega
  generalize hL : T % 2 ^ 256 = L
  generalize hHd : T / 2 ^ 256 = H at hH
  have hLlt : L < 2 ^ 256 := by omega
  have hTv : T = L + 2 ^ 256 * H := by omega
  have ha : T / 2 ^ 448 = H / 2 ^ 192 := by omega
  have hb : T / 2 ^ 192 % 2 ^ 64 = L / 2 ^ 192 := by omega
  rw [ha, hb, hTv]
  clear ha hb hL hHd hTv hT
  generalize hq : (38 * (H / 2 ^ 192) + L / 2 ^ 192) / 2 ^ 63 + 1 = q
  have hq1 : 1 ≤ q := by omega
  have hq78 : q ≤ 78 := by omega
  have hlow : 2 ^ 255 * (q - 1) ≤ L + 38 * H := by omega
  have hhigh : L + 38 * H < 2 ^ 255 * q + 38 * 2 ^ 192 := by omega
  clear hq
  have hTp : L + 2 ^ 256 * H = L + 38 * H + (2 ^ 255 - 19) * (2 * H) := by omega
  rw [hTp]
  generalize hN : L + 38 * H = N at hlow hhigh
  clear hN hTp hLlt
  by_cases hc : 2 ^ 255 * q ≤ N + 19 * q
  · -- the estimate is exact: `N - q p ∈ [0, p)`
    obtain ⟨D, hD⟩ : ∃ D, N + 19 * q = 2 ^ 255 * q + D := ⟨N + 19 * q - 2 ^ 255 * q, by omega⟩
    have hDlt : D < 38 * 2 ^ 192 + 19 * 78 := by omega
    have hS : (N + 19 * q) % 2 ^ 256 = 2 ^ 255 * (q % 2) + D := by omega
    have hNv : N + (2 ^ 255 - 19) * (2 * H) = D + (2 ^ 255 - 19) * (q + 2 * H) := by omega
    rw [hS, hNv, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show D < 2 ^ 255 - 19 by clear * - hDlt; omega)]
    have hr : q % 2 ≤ 1 := by omega
    rw [sign_bit _ _ _ hr hr (by omega)]
    clear hS hNv hD hc hlow hhigh
    generalize q % 2 = r at hr
    interval_cases r <;> clear * - hDlt <;> omega
  · -- the estimate is one too large: `N - q p ∈ [-p, 0)`
    obtain ⟨D, hD⟩ : ∃ D, N + 19 * q = 2 ^ 255 * (q - 1) + D :=
      ⟨N + 19 * q - 2 ^ 255 * (q - 1), by omega⟩
    have hDlt : D < 2 ^ 255 := by omega
    have hD19 : 19 ≤ D := by omega
    have hNv : N + (2 ^ 255 - 19) * (2 * H)
        = (D - 19) + (2 ^ 255 - 19) * (q - 1 + 2 * H) := by omega
    rw [hNv, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show D - 19 < 2 ^ 255 - 19 by clear * - hDlt hD19; omega)]
    rcases Nat.mod_two_eq_zero_or_one q with hr | hr
    · have hS : (N + 19 * q) % 2 ^ 256 = 2 ^ 255 * 1 + D := by
        clear hNv; omega
      rw [hS, sign_bit _ _ _ le_rfl (by omega) hDlt, hr]
      clear * - hDlt hD19
      omega
    · have hS : (N + 19 * q) % 2 ^ 256 = 2 ^ 255 * 0 + D := by
        clear hNv; omega
      rw [hS, sign_bit _ _ _ (Nat.zero_le 1) (by omega) hDlt, hr]
      clear * - hDlt hD19
      omega

/-! ## The segments -/

/-- The first multiply row, reading the multiplier word at `[yb + 0]`, preceded by the
    zero-register setup. -/
def row0Seg (yb : String) : List (JInstr 64) :=
  [ .mov "zr" (.imm 0)
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" yb 0
  , .mulxMem "t1" "t0" (.reg "yd") "x" 0
  , .mulxMem "t2" "lo" (.reg "yd") "x" 8
  , .adcx "t1" (.reg "lo")
  , .mulxMem "t3" "lo" (.reg "yd") "x" 16
  , .adcx "t2" (.reg "lo")
  , .mulxMem "t4" "lo" (.reg "yd") "x" 24
  , .adcx "t3" (.reg "lo")
  , .adcx "t4" (.reg "zr") ]

/-- A later multiply row over the window `a0, …, a4`, reading the multiplier word at
    `[yb + off]`. -/
def rowSeg (yb : String) (off : Int) (a0 a1 a2 a3 a4 : String) : List (JInstr 64) :=
  [ .xor_ "zr" (.reg "zr")
  , .loadMem "yd" yb off
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx a0 (.reg "lo"), .adox a1 (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8
  , .adcx a1 (.reg "lo"), .adox a2 (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16
  , .adcx a2 (.reg "lo"), .adox a3 (.reg "hi")
  , .mulxMem a4 "lo" (.reg "yd") "x" 24
  , .adcx a3 (.reg "lo")
  , .adox a4 (.reg "zr")
  , .adcx a4 (.reg "zr") ]

/-- The quotient estimate `q` of the reduction, and `19 · q`. -/
def quotSeg : List (JInstr 64) :=
  [ .mov "yd" (.imm 38)
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .add "lo" (.reg "t3")
  , .adc "hi" (.reg "zr")
  , .mov "y" (.reg "lo")
  , .shr "y" (.imm 63)
  , .shl "hi" (.imm 1)
  , .add "hi" (.reg "y")
  , .add "hi" (.imm 1)
  , .mov "y" (.reg "hi")
  , .imul "hi" (.imm 19) ]

/-- The fold of `38 · h` into `l` with `19 · q` injected. -/
def foldSeg : List (JInstr 64) :=
  [ .xor_ "zr" (.reg "zr")
  , .adox "t0" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t4")
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t5")
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t6")
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .adc "t3" (.reg "lo") ]

/-- The canonical correction and the four output stores. -/
def finalSeg : List (JInstr 64) :=
  [ .shl "y" (.imm 63)
  , .mov "lo" (.reg "t3")
  , .sub "lo" (.reg "y")
  , .shr "lo" (.imm 63)
  , .imul "lo" (.imm 19)
  , .sub "t0" (.reg "lo")
  , .sbb "t1" (.reg "zr")
  , .sbb "t2" (.reg "zr")
  , .sbb "t3" (.reg "zr")
  , .mov "hi" (.imm 0x7fffffffffffffff)
  , .and_ "t3" (.reg "hi")
  , .storeMem "z" 0 (.reg "t0")
  , .storeMem "z" 8 (.reg "t1")
  , .storeMem "z" 16 (.reg "t2")
  , .storeMem "z" 24 (.reg "t3") ]

/-- The multiply-or-square block with multiplier bank `yb`, as seven segments. -/
def fieldSegs (yb : String) : List (JInstr 64) :=
  row0Seg yb ++ rowSeg yb 8 "t1" "t2" "t3" "t4" "t5" ++ rowSeg yb 16 "t2" "t3" "t4" "t5" "t6"
    ++ rowSeg yb 24 "t3" "t4" "t5" "t6" "t7" ++ quotSeg ++ foldSeg ++ finalSeg

theorem feMulBlock_eq :
    CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock
      = fieldSegs "y" := rfl

theorem feSqrBlock_eq :
    CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock
      = fieldSegs "x" := rfl

/-! ## Limb windows -/

/-- The value of the four registers `a0, …, a3`, little-endian. -/
def v4 (R : String → BitVec 64) (a0 a1 a2 a3 : String) : Nat :=
  (R a0).toNat + 2 ^ 64 * (R a1).toNat + 2 ^ 128 * (R a2).toNat + 2 ^ 192 * (R a3).toNat

/-- The value of the five registers `a0, …, a4`, little-endian. -/
def v5 (R : String → BitVec 64) (a0 a1 a2 a3 a4 : String) : Nat :=
  v4 R a0 a1 a2 a3 + 2 ^ 256 * (R a4).toNat

/-- The value of the four memory words at `[b + 0], …, [b + 24]`, little-endian. -/
def mem4 (M : JMem 64) (b : String) : Nat :=
  (M b 0).toNat + 2 ^ 64 * (M b 8).toNat + 2 ^ 128 * (M b 16).toNat + 2 ^ 192 * (M b 24).toNat

/-- The four partial products of the word `M yb off` with the words of `x`, each at its
    weight. -/
def rowProd4 (M : JMem 64) (yb : String) (off : Int) : Nat :=
  (M yb off).toNat * (M "x" 0).toNat + 2 ^ 64 * ((M yb off).toNat * (M "x" 8).toNat)
    + 2 ^ 128 * ((M yb off).toNat * (M "x" 16).toNat)
    + 2 ^ 192 * ((M yb off).toNat * (M "x" 24).toNat)

theorem rowProd4_eq (M : JMem 64) (yb : String) (off : Int) :
    rowProd4 M yb off = (M yb off).toNat * mem4 M "x" := by
  simp only [rowProd4, mem4]; ring

theorem mem4_lt (M : JMem 64) (b : String) : mem4 M b < 2 ^ 256 := by
  have := (M b 0).isLt; have := (M b 8).isLt; have := (M b 16).isLt; have := (M b 24).isLt
  simp only [mem4]
  omega

theorem rowProd4_bound (M : JMem 64) (yb : String) (off : Int) :
    (M yb off).toNat * (M "x" 0).toNat + 2 ^ 64 * ((M yb off).toNat * (M "x" 8).toNat)
      + 2 ^ 128 * ((M yb off).toNat * (M "x" 16).toNat)
      + 2 ^ 192 * ((M yb off).toNat * (M "x" 24).toNat) + 2 ^ 256 ≤ 2 ^ 320 := by
  have h := rowProd4_eq M yb off
  simp only [rowProd4] at h
  rw [h]
  have h1 : (M yb off).toNat ≤ 2 ^ 64 - 1 := by have := (M yb off).isLt; omega
  have h2 : mem4 M "x" ≤ 2 ^ 256 - 1 := by have := mem4_lt M "x"; omega
  have h3 := Nat.mul_le_mul h1 h2
  have h4 : (2 ^ 64 - 1) * (2 ^ 256 - 1) + 2 ^ 256 ≤ (2 : Nat) ^ 320 := by norm_num
  omega

/-! ## Segment specifications -/

/-- The first multiply row stores the product of the word `[yb + 0]` with `x` in the five
    registers `t0, …, t4` and leaves the zero register at zero. -/
def Row0Spec (yb : String) : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s →
    Reach (fun R' M' => M' = M ∧ R' "zr" = 0 ∧
      v5 R' "t0" "t1" "t2" "t3" "t4" = rowProd4 M yb 0)
      (runBlock s (row0Seg yb))

theorem row0_spec (yb : String) : Row0Spec yb := by
  intro R cf of zf M s hs
  simp only [row0Seg]
  refine run_mov _ _ hs ?_; intro t0 hs0
  refine run_xor_self _ hs0 ?_; intro z1 t1 hs1
  refine run_loadMem _ _ _ hs1 ?_; intro t2 hs2
  refine run_mulxMem _ _ _ _ _ hs2 ?_; intro H0 L0 m0 t3 hs3
  refine run_mulxMem _ _ _ _ _ hs3 ?_; intro H1 L1 m1 t4 hs4
  refine run_adcx _ _ hs4 ?_; intro A1 c1 e1 bc1 t5 hs5
  refine run_mulxMem _ _ _ _ _ hs5 ?_; intro H2 L2 m2 t6 hs6
  refine run_adcx _ _ hs6 ?_; intro A2 c2 e2 bc2 t7 hs7
  refine run_mulxMem _ _ _ _ _ hs7 ?_; intro H3 L3 m3 t8 hs8
  refine run_adcx _ _ hs8 ?_; intro A3 c3 e3 bc3 t9 hs9
  refine run_adcx _ _ hs9 ?_; intro A4 c4 e4 bc4 t10 hs10
  refine reach_nil hs10 ⟨rfl, by simp only [upd, ↓reduceIte, String.reduceEq], ?_⟩
  simp only [upd, ↓reduceIte, String.reduceEq, cb_false] at m0 m1 m2 m3 e1 e2 e3 e4
  simp only [v4, v5, rowProd4, upd, ↓reduceIte, String.reduceEq]
  have hP := rowProd4_bound M yb 0
  exact row0_arith _ _ _ _ _ _ _ _ _ _ _ _ m0 m1 m2 m3 (by omega) _ _ _ _ _ _ _ _ e1 e2 e3 e4

/-- A later multiply row over the window `a0, …, a4`: the five registers afterwards hold the
    four registers before plus the product of the word `[yb + off]` with `x`; the zero
    register is zero and the registers `p0`, `p1`, `p2` are unchanged. -/
def RowSpec (yb : String) (off : Int) (a0 a1 a2 a3 a4 p0 p1 p2 : String) : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s →
    Reach (fun R' M' => M' = M ∧ R' "zr" = 0 ∧ R' p0 = R p0 ∧ R' p1 = R p1 ∧ R' p2 = R p2 ∧
      v5 R' a0 a1 a2 a3 a4 = v4 R a0 a1 a2 a3 + rowProd4 M yb off)
      (runBlock s (rowSeg yb off a0 a1 a2 a3 a4))

/-- The symbolic run of a later multiply row, closed by `row_arith`. -/
macro "row_tac" : tactic => `(tactic| (
  intro R cf of zf M s hs
  simp only [rowSeg]
  refine run_xor_self _ hs ?_; intro z0 t0 hs0
  refine run_loadMem _ _ _ hs0 ?_; intro t1 hs1
  refine run_mulxMem _ _ _ _ _ hs1 ?_; intro H0 L0 m0 t2 hs2
  refine run_adcx _ _ hs2 ?_; intro A0 c0 e0 bc0 t3 hs3
  refine run_adox _ _ hs3 ?_; intro B1 o1 f0 bo1 t4 hs4
  refine run_mulxMem _ _ _ _ _ hs4 ?_; intro H1 L1 m1 t5 hs5
  refine run_adcx _ _ hs5 ?_; intro A1 c1 e1 bc1 t6 hs6
  refine run_adox _ _ hs6 ?_; intro B2 o2 f1 bo2 t7 hs7
  refine run_mulxMem _ _ _ _ _ hs7 ?_; intro H2 L2 m2 t8 hs8
  refine run_adcx _ _ hs8 ?_; intro A2 c2 e2 bc2 t9 hs9
  refine run_adox _ _ hs9 ?_; intro B3 o3 f2 bo3 t10 hs10
  refine run_mulxMem _ _ _ _ _ hs10 ?_; intro H3 L3 m3 t11 hs11
  refine run_adcx _ _ hs11 ?_; intro A3 c3 e3 bc3 t12 hs12
  refine run_adox _ _ hs12 ?_; intro B4 o4 f3 bo4 t13 hs13
  refine run_adcx _ _ hs13 ?_; intro A4 c4 e4 bc4 t14 hs14
  refine reach_nil hs14 ⟨rfl, by simp only [upd, ↓reduceIte, String.reduceEq],
    by simp only [upd, ↓reduceIte, String.reduceEq],
    by simp only [upd, ↓reduceIte, String.reduceEq],
    by simp only [upd, ↓reduceIte, String.reduceEq], ?_⟩
  simp only [upd, ↓reduceIte, String.reduceEq, cb_false, BitVec.toNat_zero] at m0 m1 m2 m3 e0 e1 e2 e3 e4 f0 f1 f2 f3
  simp only [v4, v5, rowProd4, upd, ↓reduceIte, String.reduceEq]
  exact row_arith _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    _ _ _ _ _ _ _ _ _ _ _ _ m0 m1 m2 m3 (rowProd4_bound _ _ _)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 f0 e1 f1 e2 f2 e3 f3 e4))

theorem row1_spec (yb : String) :
    RowSpec yb 8 "t1" "t2" "t3" "t4" "t5" "t0" "t0" "t0" := by
  row_tac

theorem row2_spec (yb : String) :
    RowSpec yb 16 "t2" "t3" "t4" "t5" "t6" "t0" "t1" "t1" := by
  row_tac

theorem row3_spec (yb : String) :
    RowSpec yb 24 "t3" "t4" "t5" "t6" "t7" "t0" "t1" "t2" := by
  row_tac

/-- The value of the eight registers `t0, …, t7`, little-endian. -/
def v8 (R : String → BitVec 64) : Nat :=
  v4 R "t0" "t1" "t2" "t3" + 2 ^ 256 * v4 R "t4" "t5" "t6" "t7"

/-- The quotient segment leaves `t0, …, t7`, the memory and the zero register unchanged,
    sets `yd` to `38`, `y` to `q = ⌊(38 · t7 + t3) / 2^63⌋ + 1` and `hi` to `19 · q`. -/
def QuotSpec : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s → R "zr" = 0 →
    Reach (fun R' M' => M' = M ∧ R' "zr" = 0 ∧ R' "yd" = BitVec.ofNat 64 38 ∧
      v8 R' = v8 R ∧
      (R' "y").toNat = (38 * (R "t7").toNat + (R "t3").toNat) / 2 ^ 63 + 1 ∧
      (R' "hi").toNat = 19 * ((38 * (R "t7").toNat + (R "t3").toNat) / 2 ^ 63 + 1))
      (runBlock s quotSeg)

theorem quot_spec : QuotSpec := by
  intro R cf of zf M s hs hz
  simp only [quotSeg]
  refine run_mov _ _ hs ?_; intro t0 hs0
  refine run_mulx _ _ _ _ hs0 ?_; intro Hq Lq m t1 hs1
  refine run_add _ _ hs1 ?_; intro E0 k1 q1 q2 e1 bk1 t2 hs2
  refine run_adc _ _ hs2 ?_; intro E1 k2 q3 q4 e2 bk2 hz2 t3 hs3
  refine run_mov _ _ hs3 ?_; intro t4 hs4
  refine run_shr_imm _ 63 (by decide) (by decide) hs4 ?_; intro Y1 q5 q6 q7 eY t5 hs5
  refine run_shl_imm _ 1 (by decide) (by decide) hs5 ?_; intro E2 q8 q9 q10 eS t6 hs6
  refine run_add _ _ hs6 ?_; intro E3 k3 q11 q12 e3 bk3 t7 hs7
  refine run_add_imm _ 1 hs7 ?_; intro Q k4 q13 q14 e4 bk4 t8 hs8
  refine run_mov _ _ hs8 ?_; intro t9 hs9
  refine run_imul_imm _ 19 hs9 ?_; intro G q15 q16 q17 eG t10 hs10
  simp only [upd, opv, ↓reduceIte, String.reduceEq, hz, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at m e1 e2 eY eS e3 e4 eG
  have hq := quot_arith _ _ (R "t7").isLt (R "t3").isLt _ _ _ _ _ _ _ _ _ _ _ _
    E0.isLt E1.isLt (cb_le_one _) m e1 e2 eY eS e3 e4
  refine reach_nil hs10 ⟨rfl, by simp only [upd, ↓reduceIte, String.reduceEq, hz],
    by simp only [upd, opv, ↓reduceIte, String.reduceEq], ?_, ?_, ?_⟩
  · simp only [v8, v4, upd, ↓reduceIte, String.reduceEq]
  · simp only [upd, ↓reduceIte, String.reduceEq]
    exact hq.1
  · simp only [upd, ↓reduceIte]
    rw [eG, ← hq.1]
    omega

/-- The fold segment leaves the memory and `y` unchanged, zeroes the zero register, and
    stores `(l + 38 · h + hi) mod 2^256` in `t0, …, t3`, when `yd` holds `38`. -/
def FoldSpec : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s → R "yd" = BitVec.ofNat 64 38 →
    Reach (fun R' M' => M' = M ∧ R' "zr" = 0 ∧ R' "y" = R "y" ∧
      v4 R' "t0" "t1" "t2" "t3" = (v4 R "t0" "t1" "t2" "t3"
        + 38 * v4 R "t4" "t5" "t6" "t7" + (R "hi").toNat) % 2 ^ 256)
      (runBlock s foldSeg)

theorem fold_spec : FoldSpec := by
  intro R cf of zf M s hs hyd
  simp only [foldSeg]
  refine run_xor_self _ hs ?_; intro z0 t0 hs0
  refine run_adox _ _ hs0 ?_; intro U0 o1 f0 bo1 t1 hs1
  refine run_mulx _ _ _ _ hs1 ?_; intro H0 L0 m0 t2 hs2
  refine run_adcx _ _ hs2 ?_; intro S0 c1 e0 bc1 t3 hs3
  refine run_adox _ _ hs3 ?_; intro U1 o2 f1 bo2 t4 hs4
  refine run_mulx _ _ _ _ hs4 ?_; intro H1 L1 m1 t5 hs5
  refine run_adcx _ _ hs5 ?_; intro S1 c2 e1 bc2 t6 hs6
  refine run_adox _ _ hs6 ?_; intro U2 o3 f2 bo3 t7 hs7
  refine run_mulx _ _ _ _ hs7 ?_; intro H2 L2 m2 t8 hs8
  refine run_adcx _ _ hs8 ?_; intro S2 c3 e2 bc3 t9 hs9
  refine run_adox _ _ hs9 ?_; intro U3 o4 f3 bo4 t10 hs10
  refine run_mulx _ _ _ _ hs10 ?_; intro H3 L3 m3 t11 hs11
  refine run_adc _ _ hs11 ?_; intro S3 c4 q1 q2 e3 bc4 hz3 t12 hs12
  refine reach_nil hs12 ⟨rfl, by simp only [upd, ↓reduceIte, String.reduceEq],
    by simp only [upd, ↓reduceIte, String.reduceEq], ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq, hyd, cb_false, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at f0 m0 e0 f1 m1 e1 f2 m2 e2 f3 m3 e3
  simp only [v4, upd, ↓reduceIte, String.reduceEq]
  exact fold_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    S0.isLt S1.isLt S2.isLt S3.isLt f0 m0 e0 f1 m1 e1 f2 m2 e2 f3 m3 e3

/-- The final segment stores `finalZ (t0 … t3) y` at `[z + 0], …, [z + 24]` and writes no
    other memory bank, when the zero register is zero. -/
def FinalSpec : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s → R "zr" = 0 →
    Reach (fun _ M' => (∀ b o, b ≠ "z" → M' b o = M b o) ∧
      mem4 M' "z" = finalZ (v4 R "t0" "t1" "t2" "t3") (R "y").toNat)
      (runBlock s finalSeg)

theorem final_spec : FinalSpec := by
  intro R cf of zf M s hs hz
  simp only [finalSeg]
  refine run_shl_imm _ 63 (by decide) (by decide) hs ?_; intro Y q0 q1 q2 eY t0 hs0
  refine run_mov _ _ hs0 ?_; intro t1 hs1
  refine run_sub _ _ hs1 ?_; intro D b q3 q4 eD bb t2 hs2
  refine run_shr_imm _ 63 (by decide) (by decide) hs2 ?_; intro sg q5 q6 q7 eg t3 hs3
  refine run_imul_imm _ 19 hs3 ?_; intro amt q8 q9 q10 ea t4 hs4
  refine run_sub _ _ hs4 ?_; intro Z0 b0 q11 q12 e0 bb0 t5 hs5
  refine run_sbb _ _ hs5 ?_; intro Z1 b1 q13 q14 e1 bb1 t6 hs6
  refine run_sbb _ _ hs6 ?_; intro Z2 b2 q15 q16 e2 bb2 t7 hs7
  refine run_sbb _ _ hs7 ?_; intro Z3 b3 q17 q18 e3 bb3 t8 hs8
  refine run_mov _ _ hs8 ?_; intro t9 hs9
  refine run_and _ _ hs9 ?_; intro q19 q20 q21 t10 hs10
  refine run_storeMem _ _ _ hs10 ?_; intro t11 hs11
  refine run_storeMem _ _ _ hs11 ?_; intro t12 hs12
  refine run_storeMem _ _ _ hs12 ?_; intro t13 hs13
  refine run_storeMem _ _ _ hs13 ?_; intro t14 hs14
  refine reach_nil hs14 ⟨fun b o hb => by simp [hb], ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq, hz, Nat.reducePow, Nat.reduceMod] at eY eD eg ea e0 e1 e2 e3
  simp only [mem4, v4, upd, opv, ↓reduceIte, String.reduceEq, and_self, and_mask_toNat]
  exact final_arith _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    _ _ _ _ _ _ _ _ _ _ _ _ _ D.isLt Z0.isLt Z1.isLt Z2.isLt Z3.isLt (cb_le_one _)
    eY eD eg ea e0 e1 e2 e3

/-! ## The abstract algorithm and the segment correspondences -/

/-- The abstract state of the block: the stage reached (the number of segments run), the
    inputs `x`, `y`, the accumulator and the quotient estimate. -/
structure AFe where
  /-- Segments run. -/
  stage : Nat
  /-- The value of `x`. -/
  x : Nat
  /-- The value of `y`. -/
  y : Nat
  /-- The accumulator. -/
  acc : Nat
  /-- The quotient estimate. -/
  q : Nat

/-- The value of the six registers `t0, …, t5`, little-endian. -/
def v6 (R : String → BitVec 64) : Nat := v5 R "t0" "t1" "t2" "t3" "t4" + 2 ^ 320 * (R "t5").toNat

/-- The value of the seven registers `t0, …, t6`, little-endian. -/
def v7 (R : String → BitVec 64) : Nat := v6 R + 2 ^ 384 * (R "t6").toNat

/-- Where the accumulator and the quotient live after each stage. -/
def StageRel : Nat → JState 64 → AFe → Prop
  | 1, st, a => st.regs "zr" = 0 ∧ v5 st.regs "t0" "t1" "t2" "t3" "t4" = a.acc
  | 2, st, a => st.regs "zr" = 0 ∧ v6 st.regs = a.acc
  | 3, st, a => st.regs "zr" = 0 ∧ v7 st.regs = a.acc
  | 4, st, a => st.regs "zr" = 0 ∧ v8 st.regs = a.acc
  | 5, st, a => st.regs "zr" = 0 ∧ v8 st.regs = a.acc ∧ st.regs "yd" = BitVec.ofNat 64 38 ∧
      (st.regs "y").toNat = a.q ∧ (st.regs "hi").toNat = 19 * a.q
  | 6, st, a => st.regs "zr" = 0 ∧ v4 st.regs "t0" "t1" "t2" "t3" = a.acc ∧
      (st.regs "y").toNat = a.q
  | 7, st, a => mem4 st.mem "z" = a.acc
  | _, _, _ => True

/-- The state relation for multiplier bank `yb`: `x` and `y` are the four words at `"x"`
    and `yb`, and the accumulator is where `StageRel` places it. -/
def SRf (yb : String) (st : JState 64) (a : AFe) : Prop :=
  mem4 st.mem "x" = a.x ∧ mem4 st.mem yb = a.y ∧ StageRel a.stage st a

theorem digit0 (M : JMem 64) (b : String) : (M b 0).toNat = ydig (mem4 M b) 0 := by
  have := (M b 0).isLt; have := (M b 8).isLt; have := (M b 16).isLt; have := (M b 24).isLt
  simp only [ydig, mem4]; omega

theorem digit1 (M : JMem 64) (b : String) : (M b 8).toNat = ydig (mem4 M b) 1 := by
  have := (M b 0).isLt; have := (M b 8).isLt; have := (M b 16).isLt; have := (M b 24).isLt
  simp only [ydig, mem4]; omega

theorem digit2 (M : JMem 64) (b : String) : (M b 16).toNat = ydig (mem4 M b) 2 := by
  have := (M b 0).isLt; have := (M b 8).isLt; have := (M b 16).isLt; have := (M b 24).isLt
  simp only [ydig, mem4]; omega

theorem digit3 (M : JMem 64) (b : String) : (M b 24).toNat = ydig (mem4 M b) 3 := by
  have := (M b 0).isLt; have := (M b 8).isLt; have := (M b 16).isLt; have := (M b 24).isLt
  simp only [ydig, mem4]; omega

theorem v8_parts (R : String → BitVec 64) :
    (R "t7").toNat = v8 R / 2 ^ 448 ∧ (R "t3").toNat = v8 R / 2 ^ 192 % 2 ^ 64 ∧
      v8 R % 2 ^ 256 = v4 R "t0" "t1" "t2" "t3" ∧
      v8 R / 2 ^ 256 = v4 R "t4" "t5" "t6" "t7" := by
  have := (R "t0").isLt; have := (R "t1").isLt; have := (R "t2").isLt
  have := (R "t3").isLt; have := (R "t4").isLt; have := (R "t5").isLt
  have := (R "t6").isLt; have := (R "t7").isLt
  simp only [v8, v4]
  omega

/-- The first multiply row refines its abstract step. -/
theorem corresJ_row0 (yb : String) :
    CorresJ (SRf yb) (fun a => a.stage = 0)
      (fun a => { a with stage := 1, acc := ydig a.y 0 * a.x }) (row0Seg yb) := by
  intro st a ⟨hx, hy, _⟩ _
  obtain ⟨R', _, _, _, M', hs', hM, hz, hv⟩ := row0_spec yb _ _ _ _ _ st (desc_self st)
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  show (runBlock st (row0Seg yb)).regs "zr" = 0 ∧
    v5 (runBlock st (row0Seg yb)).regs "t0" "t1" "t2" "t3" "t4" = ydig a.y 0 * a.x
  rw [hs'.regs]
  exact ⟨hz, by rw [hv, rowProd4_eq, digit0, hx, hy, Nat.mul_comm]⟩

/-- The second multiply row refines its abstract step. -/
theorem corresJ_row1 (yb : String) :
    CorresJ (SRf yb) (fun a => a.stage = 1)
      (fun a => { a with stage := 2, acc := a.acc + 2 ^ 64 * (ydig a.y 1 * a.x) })
      (rowSeg yb 8 "t1" "t2" "t3" "t4" "t5") := by
  intro st a ⟨hx, hy, hrel⟩ hk
  rw [hk] at hrel
  obtain ⟨_, hv0⟩ := hrel
  obtain ⟨R', _, _, _, M', hs', hM, hz, hp, -, -, hv⟩ :=
    row1_spec yb _ _ _ _ _ st (desc_self st)
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  show (runBlock st _).regs "zr" = 0 ∧ v6 (runBlock st _).regs = _
  rw [hs'.regs]
  refine ⟨hz, ?_⟩
  dsimp only
  rw [← hv0, ← hx, ← hy, ← digit1, Nat.mul_comm, ← rowProd4_eq]
  simp only [v6, v5, v4] at hv hv0 ⊢
  rw [hp]
  omega

/-- The third multiply row refines its abstract step. -/
theorem corresJ_row2 (yb : String) :
    CorresJ (SRf yb) (fun a => a.stage = 2)
      (fun a => { a with stage := 3, acc := a.acc + 2 ^ 128 * (ydig a.y 2 * a.x) })
      (rowSeg yb 16 "t2" "t3" "t4" "t5" "t6") := by
  intro st a ⟨hx, hy, hrel⟩ hk
  rw [hk] at hrel
  obtain ⟨_, hv0⟩ := hrel
  obtain ⟨R', _, _, _, M', hs', hM, hz, hp0, hp1, -, hv⟩ :=
    row2_spec yb _ _ _ _ _ st (desc_self st)
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  show (runBlock st _).regs "zr" = 0 ∧ v7 (runBlock st _).regs = _
  rw [hs'.regs]
  refine ⟨hz, ?_⟩
  dsimp only
  rw [← hv0, ← hx, ← hy, ← digit2, Nat.mul_comm, ← rowProd4_eq]
  simp only [v7, v6, v5, v4] at hv hv0 ⊢
  rw [hp0, hp1]
  omega

/-- The fourth multiply row refines its abstract step. -/
theorem corresJ_row3 (yb : String) :
    CorresJ (SRf yb) (fun a => a.stage = 3)
      (fun a => { a with stage := 4, acc := a.acc + 2 ^ 192 * (ydig a.y 3 * a.x) })
      (rowSeg yb 24 "t3" "t4" "t5" "t6" "t7") := by
  intro st a ⟨hx, hy, hrel⟩ hk
  rw [hk] at hrel
  obtain ⟨_, hv0⟩ := hrel
  obtain ⟨R', _, _, _, M', hs', hM, hz, hp0, hp1, hp2, hv⟩ :=
    row3_spec yb _ _ _ _ _ st (desc_self st)
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  show (runBlock st _).regs "zr" = 0 ∧ v8 (runBlock st _).regs = _
  rw [hs'.regs]
  refine ⟨hz, ?_⟩
  dsimp only
  rw [← hv0, ← hx, ← hy, ← digit3, Nat.mul_comm, ← rowProd4_eq]
  simp only [v8, v7, v6, v5, v4] at hv hv0 ⊢
  rw [hp0, hp1, hp2]
  omega

/-- The quotient segment refines the choice `q := qOf acc`. -/
theorem corresJ_quot (yb : String) :
    CorresJ (SRf yb) (fun a => a.stage = 4)
      (fun a => { a with stage := 5, q := qOf a.acc }) quotSeg := by
  intro st a ⟨hx, hy, hrel⟩ hk
  rw [hk] at hrel
  obtain ⟨hz0, hv0⟩ := hrel
  obtain ⟨R', _, _, _, M', hs', hM, hz, hyd, hv, hyq, hhi⟩ :=
    quot_spec _ _ _ _ _ st (desc_self st) hz0
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  obtain ⟨h7, h3, -, -⟩ := v8_parts st.regs
  have hq : qOf a.acc = (38 * (st.regs "t7").toNat + (st.regs "t3").toNat) / 2 ^ 63 + 1 := by
    rw [qOf, h7, h3, hv0]
  show (runBlock st _).regs "zr" = 0 ∧ v8 (runBlock st _).regs = _ ∧ _ ∧ _ ∧ _
  dsimp only
  rw [hs'.regs, hq]
  exact ⟨hz, hv.trans hv0, hyd, hyq, hhi⟩

/-- The fold segment refines `foldF`. -/
theorem corresJ_fold (yb : String) :
    CorresJ (SRf yb) (fun a => a.stage = 5)
      (fun a => { a with stage := 6, acc := foldF a.acc a.q }) foldSeg := by
  intro st a ⟨hx, hy, hrel⟩ hk
  rw [hk] at hrel
  obtain ⟨-, hv0, hyd, hyq, hhi⟩ := hrel
  obtain ⟨R', _, _, _, M', hs', hM, hz, hy', hv⟩ := fold_spec _ _ _ _ _ st (desc_self st) hyd
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  obtain ⟨-, -, hlo, hhi'⟩ := v8_parts st.regs
  show (runBlock st _).regs "zr" = 0 ∧ v4 (runBlock st _).regs "t0" "t1" "t2" "t3" = _ ∧ _
  dsimp only
  rw [hs'.regs, hv, hy', foldF, ← hv0, hlo, hhi', hhi]
  exact ⟨hz, rfl, hyq⟩

/-- The final segment refines `finalZ`. -/
theorem corresJ_final (yb : String) (hyb : yb ≠ "z") :
    CorresJ (SRf yb) (fun a => a.stage = 6)
      (fun a => { a with stage := 7, acc := finalZ a.acc a.q }) finalSeg := by
  intro st a ⟨hx, hy, hrel⟩ hk
  rw [hk] at hrel
  obtain ⟨hz0, hv0, hyq⟩ := hrel
  obtain ⟨R', _, _, _, M', hs', hfr, hv⟩ := final_spec _ _ _ _ _ st (desc_self st) hz0
  have hxm : mem4 M' "x" = mem4 st.mem "x" := by
    simp only [mem4, hfr "x" _ (by decide)]
  have hym : mem4 M' yb = mem4 st.mem yb := by
    simp only [mem4, hfr yb _ hyb]
  refine ⟨by rw [hs'.mem, hxm]; exact hx, by rw [hs'.mem, hym]; exact hy, ?_⟩
  show mem4 (runBlock st finalSeg).mem "z" = finalZ a.acc a.q
  rw [hs'.mem, hv, hv0, hyq]

/-- The schoolbook accumulator: the four rows `y_j · x` at their weights. -/
def schoolAcc (x y : Nat) : Nat :=
  ydig y 0 * x + 2 ^ 64 * (ydig y 1 * x) + 2 ^ 128 * (ydig y 2 * x) + 2 ^ 192 * (ydig y 3 * x)

/-- The abstract field multiply the block refines: the schoolbook, then `redAbs`. -/
def fieldAbs (x y : Nat) : Nat := redAbs (schoolAcc x y)

theorem schoolAcc_eq (x y : Nat) (hy : y < 2 ^ 256) : schoolAcc x y = x * y := by
  have hy' : y = ydig y 0 + 2 ^ 64 * ydig y 1 + 2 ^ 128 * ydig y 2 + 2 ^ 192 * ydig y 3 := by
    simp only [ydig]
    norm_num
    omega
  conv_rhs => rw [hy']
  unfold schoolAcc
  ring

/-- **The segments refine the abstract field multiply.** From stage `0`, running
    `fieldSegs yb` under `runBlock` reaches stage `7`, where the four words at `"z"` hold
    `fieldAbs x y`. Composed from the seven segment correspondences by `corresJ_append`. -/
theorem fieldSegs_corresJ (yb : String) (hyb : yb ≠ "z") :
    CorresJ (SRf yb) (fun a => a.stage = 0)
      (fun a => AFe.mk 7 a.x a.y (fieldAbs a.x a.y) (qOf (schoolAcc a.x a.y)))
      (fieldSegs yb) := by
  have c5 := corresJ_append (SRf yb) (corresJ_fold yb) (corresJ_final yb hyb)
    (fun _ _ => rfl)
  have c4 := corresJ_append (SRf yb) (corresJ_quot yb) c5 (fun _ _ => rfl)
  have c3 := corresJ_append (SRf yb) (corresJ_row3 yb) c4 (fun _ _ => rfl)
  have c2 := corresJ_append (SRf yb) (corresJ_row2 yb) c3 (fun _ _ => rfl)
  have c1 := corresJ_append (SRf yb) (corresJ_row1 yb) c2 (fun _ _ => rfl)
  have c0 := corresJ_append (SRf yb) (corresJ_row0 yb) c1 (fun _ _ => rfl)
  unfold fieldSegs
  simp only [List.append_assoc]
  exact c0

theorem mul_lt_512 (x y : Nat) (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) : x * y < 2 ^ 512 :=
  calc x * y < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul'' hx hy
    _ = 2 ^ 512 := by norm_num

/-- For every machine state, `fieldSegs yb` stores `(x · y) mod p25519` at `"z"`, with `x`
    the four words at `"x"` and `y` the four words at `yb`, when `yb` is not `"z"`. -/
theorem fieldSegs_mod (yb : String) (hyb : yb ≠ "z") (st : JState 64) :
    mem4 (runBlock st (fieldSegs yb)).mem "z" = mem4 st.mem "x" * mem4 st.mem yb % p25519 := by
  have h := fieldSegs_corresJ yb hyb st ⟨0, mem4 st.mem "x", mem4 st.mem yb, 0, 0⟩
    ⟨rfl, rfl, trivial⟩ rfl
  have hz : mem4 (runBlock st (fieldSegs yb)).mem "z"
      = fieldAbs (mem4 st.mem "x") (mem4 st.mem yb) := h.2.2
  rw [hz, fieldAbs, schoolAcc_eq _ _ (mem4_lt _ _),
    redAbs_eq _ (mul_lt_512 _ _ (mem4_lt _ _) (mem4_lt _ _))]

theorem p25519_pos : 0 < p25519 := by unfold p25519; norm_num

/-! ## The machine-level results -/

/-- **The field-multiply block refines the abstract field multiply.** -/
theorem feMulBlock_corresJ :
    CorresJ (SRf "y") (fun a => a.stage = 0)
      (fun a => AFe.mk 7 a.x a.y (fieldAbs a.x a.y) (qOf (schoolAcc a.x a.y)))
      CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock := by
  rw [feMulBlock_eq]
  exact fieldSegs_corresJ "y" (by decide)

/-- **The field-square block refines the abstract field multiply of `x` with itself.** -/
theorem feSqrBlock_corresJ :
    CorresJ (SRf "x") (fun a => a.stage = 0)
      (fun a => AFe.mk 7 a.x a.y (fieldAbs a.x a.y) (qOf (schoolAcc a.x a.y)))
      CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock := by
  rw [feSqrBlock_eq]
  exact fieldSegs_corresJ "x" (by decide)

/-- **`feMulBlock` computes the Curve25519 field product.** For every machine state, with
    `x` the four words at `"x"` and `y` the four words at `"y"`, running `feMulBlock` under
    `runBlock` stores at `["z" + 0], …, ["z" + 24]` the value `(x · y) mod p25519`. -/
theorem feMulBlock_mod (st : JState 64) :
    mem4 (runBlock st
        CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock).mem "z"
      = mem4 st.mem "x" * mem4 st.mem "y" % p25519 := by
  rw [feMulBlock_eq]
  exact fieldSegs_mod "y" (by decide) st

/-- **`feSqrBlock` computes the Curve25519 field square.** For every machine state, with
    `x` the four words at `"x"`, running `feSqrBlock` under `runBlock` stores at
    `["z" + 0], …, ["z" + 24]` the value `x² mod p25519`. -/
theorem feSqrBlock_mod (st : JState 64) :
    mem4 (runBlock st
        CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock).mem "z"
      = mem4 st.mem "x" ^ 2 % p25519 := by
  rw [feSqrBlock_eq, sq]
  exact fieldSegs_mod "x" (by decide) st

/-- **`feMulBlock` is correct in `ZMod p25519`.** For every machine state, with `x`, `y`
    the four words at `"x"`, `"y"`, the four words `z` that `feMulBlock` stores at `"z"`
    satisfy `z < p25519` and `z = x · y` in `ZMod p25519`. No hypothesis on `x`, `y`. -/
theorem feMulBlock_correct (st : JState 64) :
    mem4 (runBlock st
        CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock).mem "z"
        < p25519 ∧
      ((mem4 (runBlock st
          CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock).mem "z"
          : Nat) : ZMod p25519)
        = (mem4 st.mem "x" : ZMod p25519) * (mem4 st.mem "y" : ZMod p25519) := by
  rw [feMulBlock_mod]
  refine ⟨Nat.mod_lt _ p25519_pos, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul]

/-- **`feSqrBlock` is correct in `ZMod p25519`.** For every machine state, with `x` the four
    words at `"x"`, the four words `z` that `feSqrBlock` stores at `"z"` satisfy
    `z < p25519` and `z = x²` in `ZMod p25519`. No hypothesis on `x`. -/
theorem feSqrBlock_correct (st : JState 64) :
    mem4 (runBlock st
        CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock).mem "z"
        < p25519 ∧
      ((mem4 (runBlock st
          CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock).mem "z"
          : Nat) : ZMod p25519)
        = (mem4 st.mem "x" : ZMod p25519) ^ 2 := by
  rw [feSqrBlock_mod]
  refine ⟨Nat.mod_lt _ p25519_pos, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_pow]

/-- `feMulComputes` holds on every limb vector: from `BignumMontMulKernel.initState`, the
    stored words read little-endian equal `(x · y) mod p25519`. -/
theorem feMulComputes_all (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulComputes
      x0 x1 x2 x3 y0 y1 y2 y3 := by
  have h := feMulBlock_mod
    (CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel.initState
      x0 x1 x2 x3 y0 y1 y2 y3)
  have hx : mem4 (CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel.initState
      x0 x1 x2 x3 y0 y1 y2 y3).mem "x" = limbsNat x0 x1 x2 x3 := by
    simp [mem4, limbsNat,
      CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel.initState]
  have hy : mem4 (CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel.initState
      x0 x1 x2 x3 y0 y1 y2 y3).mem "y" = limbsNat y0 y1 y2 y3 := by
    simp [mem4, limbsNat,
      CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel.initState]
  rw [hx, hy] at h
  exact h

/-- From `Fe25519OpsKernel.initState1`, the words `feSqrBlock` stores at `"z"`, read
    little-endian, equal `x² mod p25519`. -/
theorem feSqr_initState1 (x0 x1 x2 x3 : BitVec 64) :
    limbsNat
        ((runBlock (CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.initState1
          x0 x1 x2 x3)
          CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock).load "z" 0)
        ((runBlock (CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.initState1
          x0 x1 x2 x3)
          CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock).load "z" 8)
        ((runBlock (CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.initState1
          x0 x1 x2 x3)
          CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock).load "z" 16)
        ((runBlock (CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.initState1
          x0 x1 x2 x3)
          CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.feSqrBlock).load "z" 24)
      = limbsNat x0 x1 x2 x3 ^ 2 % p25519 := by
  have h := feSqrBlock_mod
    (CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.initState1 x0 x1 x2 x3)
  have hx : mem4 (CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.initState1
      x0 x1 x2 x3).mem "x" = limbsNat x0 x1 x2 x3 := by
    simp [mem4, limbsNat, CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel.initState1]
  rw [hx] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof
