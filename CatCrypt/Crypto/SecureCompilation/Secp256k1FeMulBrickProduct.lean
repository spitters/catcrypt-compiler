/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
public import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul

/-!
# The operand-scanning product of `genMul`

`Secp256k1FeMulFront.genMul` emits an `na × nb` half-limb operand-scanning
multiply: each column binds `t = a[i]·b[j] + acc[i+j] + carry`, splits it into a
32-bit digit `p = t &&& mask32` and a carry `k = t >>> 32`, and stores the digit
back into the accumulator slot. This module gives that generator its value
semantics under `TranslateDialectScalar.semScalar`: the `na + nb` accumulator
names it returns hold, at radix `2 ^ 32`, the product of the two operands' limb
readouts.

The proof is generator-level. The two nested `Id.run do` loops are identified
with explicit `Nat`-recursions (`mAccIn` / `mAccO` for the accumulator name
array, `mCmdsIn` / `mCmdsO` for the emitted commands) through the trip-indexed
loop invariant `Secp256k1FeAddSubBrick.forInRangeIdx`, and those recursions are
then read back through `semList` one column at a time, carrying the per-limb
bound, the carry bound and the weighted column sum as a single induction. No
generated command list is reduced.

## Name hygiene

A column binds `s!"{pfx}t{i}_{j}"` and its two siblings. Distinctness of those
names across columns is what keeps a later column from overwriting an
accumulator slot, and it is decided by the decimal suffix
`toString i ++ "_" ++ toString j`, whose two indices are recoverable when both
are single digits. The results therefore carry `aN.length ≤ 10` and
`bN.length ≤ 10`, which the 8-limb secp256k1 bricks satisfy.

## Main results

* `mNm`, `mNm_inj` — the column name algebra and its injectivity.
* `mAccIn`, `mAccO`, `mCmdsIn`, `mCmdsO`, `genMulRun_spec` — the `Nat`-recursive
  mirror of the two nested generator loops.
* `mAccO_high`, `mAccO_accName` — the accumulator array's unwritten tail and the
  shape of every name it holds.
* `mCmdsIn_sem` — one outer trip's column chain: the emitted trips move the
  weighted accumulator sum by `2 ^ (32 i) · a[i] ·` the partial `b` sum.
* `mCmdsO_sem` — the outer scan: after `i` trips the accumulator holds the
  product of the first `i` limbs of `a` with all of `b`.
* `genMul_prod` — the operand-scanning multiply's accumulator names hold the
  product of the two operands' limb readouts at radix `2 ^ 32`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickProduct

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (genMul mask32 sv)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk MulI MulO genMulInnerStep genMulOuterStep genMulRun genMul_eq arrayToList_getBang)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
open CatCrypt.Crypto.SecureCompilation.Ascent (mulxProdAddBound)

/-! ## 1. The column name algebra -/

/-- The decimal index suffix a column name carries. -/
def mSfx (i j : Nat) : String := toString i ++ ("_" ++ toString j)

/-- The name a column binds under a private prefix and a one-character tag. -/
def mNm (pfx tag : String) (i j : Nat) : String := pfx ++ tag ++ toString i ++ "_" ++ toString j

theorem digit1 {i : Nat} (hi : i < 10) : (toString i).length = 1 := by
  interval_cases i <;> decide

theorem mNm_split (pfx tag : String) (i j : Nat) : mNm pfx tag i j = pfx ++ tag ++ mSfx i j := by
  simp only [mNm, mSfx, String.append_assoc]

theorem mNm_assoc (pfx tag : String) (i j : Nat) :
    mNm pfx tag i j = pfx ++ (tag ++ mSfx i j) := by
  simp only [mNm, mSfx, String.append_assoc]

theorem mSfx_len {i j : Nat} (hi : i < 10) (hj : j < 10) : (mSfx i j).length = 2 + 1 := by
  simp only [mSfx, String.length_append, digit1 hi, digit1 hj]
  decide

/-- Two column names collide only at the same tag and the same column. -/
theorem mNm_inj {pfx t u : String} {i j i' j' : Nat}
    (hi : i < 10) (hj : j < 10) (hi' : i' < 10) (hj' : j' < 10)
    (h : mNm pfx t i j = mNm pfx u i' j') : t = u ∧ i = i' ∧ j = j' := by
  rw [mNm_split, mNm_split] at h
  obtain ⟨h1, h2⟩ := appSuffixInj h (by rw [mSfx_len hi hj, mSfx_len hi' hj'])
  obtain ⟨h3, h4⟩ := appSuffixInj h2
    (by rw [String.length_append, String.length_append, digit1 hj, digit1 hj'])
  exact ⟨(String.append_right_inj pfx).mp h1,
    repr_injective (by simpa [toString] using h3),
    repr_injective (by simpa [toString] using (String.append_right_inj "_").mp h4)⟩

theorem mNm_t (pfx : String) (i j : Nat) : s!"{pfx}t{i}_{j}" = mNm pfx "t" i j := rfl

theorem mNm_p (pfx : String) (i j : Nat) : s!"{pfx}p{i}_{j}" = mNm pfx "p" i j := rfl

theorem mNm_k (pfx : String) (i j : Nat) : s!"{pfx}k{i}_{j}" = mNm pfx "k" i j := rfl

theorem mNm_notTmp {pfx : String} (hp : HeadOk pfx) (tag : String) (i j : Nat) :
    ¬ isTmpName (mNm pfx tag i j) := by
  rw [mNm_assoc]; exact (hp.append _).notTmp

/-- A name outside the private prefix is never a column name. -/
theorem outOf_ne_mNm {pfx s : String} (h : OutOf pfx s) (tag : String) (i j : Nat) :
    s ≠ mNm pfx tag i j := by
  rw [mNm_assoc]; exact h.2 _

/-! ## 2. The generator's two loops, as `Nat`-recursions -/

/-- The carry slot entering column `j` of outer trip `i`. -/
def mCar (zero pfx : String) (i : Nat) : Nat → String
  | 0 => zero
  | j + 1 => mNm pfx "k" i j

/-- The accumulator name array after `j` columns of outer trip `i`. -/
def mAccIn (pfx : String) (a0 : Array String) (i : Nat) : Nat → Array String
  | 0 => a0
  | j + 1 => (mAccIn pfx a0 i j).set! (i + j) (mNm pfx "p" i j)

/-- The three commands one column emits. -/
def mTrip (zero pfx : String) (aN bN : List String) (a0 : Array String) (i j : Nat) :
    List LowCT :=
  [ LowCT.RScalarSetExpr (mNm pfx "t" i j)
      (.SAdd (.SAdd (.SMul (sv (aN[i]!)) (sv (bN[j]!)))
        (sv ((mAccIn pfx a0 i j)[i + j]!))) (sv (mCar zero pfx i j)))
  , LowCT.RScalarSetExpr (mNm pfx "p" i j) (.SAnd (sv (mNm pfx "t" i j)) (.SLit mask32))
  , LowCT.RScalarSetExpr (mNm pfx "k" i j) (.SShr (sv (mNm pfx "t" i j)) (.SLit 32)) ]

/-- The commands outer trip `i` has emitted after `j` columns. -/
def mCmdsIn (zero pfx : String) (aN bN : List String) (a0 : Array String) (i : Nat) :
    Nat → List LowCT
  | 0 => []
  | j + 1 => mCmdsIn zero pfx aN bN a0 i j ++ mTrip zero pfx aN bN a0 i j

/-- The accumulator name array after `i` outer trips. -/
def mAccO (zero pfx : String) (na nb : Nat) : Nat → Array String
  | 0 => Array.replicate (na + nb) zero
  | i + 1 => (mAccIn pfx (mAccO zero pfx na nb i) i nb).set! (i + nb) (mCar zero pfx i nb)

/-- The commands the outer scan has emitted after `i` trips. -/
def mCmdsO (zero pfx : String) (aN bN : List String) : Nat → List LowCT
  | 0 => []
  | i + 1 => mCmdsO zero pfx aN bN i
      ++ mCmdsIn zero pfx aN bN (mAccO zero pfx aN.length bN.length i) i bN.length

theorem genMulInner_spec (zero pfx : String) (aN bN : List String) (a0 : Array String)
    (cmds0 : List LowCT) (i n : Nat) :
    (forIn [:n] (⟨a0, zero, cmds0⟩ : MulI) (genMulInnerStep zero aN bN pfx i) : Id _)
      = ⟨mAccIn pfx a0 i n, mCar zero pfx i n, cmds0 ++ mCmdsIn zero pfx aN bN a0 i n⟩ := by
  refine forInRangeIdx (fun j s => s = (⟨mAccIn pfx a0 i j, mCar zero pfx i j,
      cmds0 ++ mCmdsIn zero pfx aN bN a0 i j⟩ : MulI)) _ _ _ ?_ ?_ ?_
  · simp only [mAccIn, mCar, mCmdsIn, List.append_nil]
  · intro j s s' hs hy
    subst hs
    simp only [genMulInnerStep] at hy
    injection hy with hy
    subst hy
    simp only [mAccIn, mCar, mCmdsIn, mTrip, mNm_t, mNm_p, mNm_k,
      List.append_assoc, List.cons_append, List.nil_append]
  · intro j s s' h
    simp only [genMulInnerStep] at h
    injection h

theorem genMulRun_spec (zero pfx : String) (aN bN : List String) :
    genMulRun zero aN bN pfx
      = ⟨mAccO zero pfx aN.length bN.length aN.length, mCmdsO zero pfx aN bN aN.length⟩ := by
  unfold genMulRun
  refine forInRangeIdx
    (fun i s => s = (⟨mAccO zero pfx aN.length bN.length i, mCmdsO zero pfx aN bN i⟩ : MulO))
    _ _ _ rfl ?_ ?_
  · intro i s s' hs hy
    subst hs
    simp only [genMulOuterStep, genMulInner_spec] at hy
    injection hy with hy
    subst hy
    simp only [mAccO, mCmdsO]
  · intro i s s' h
    simp only [genMulOuterStep] at h
    injection h

theorem genMul_cmds (zero pfx : String) (aN bN : List String) :
    (genMul zero aN bN pfx).1 = mCmdsO zero pfx aN bN aN.length := by
  rw [genMul_eq, genMulRun_spec]

theorem genMul_names (zero pfx : String) (aN bN : List String) (pos : Nat) :
    (genMul zero aN bN pfx).2[pos]!
      = (mAccO zero pfx aN.length bN.length aN.length)[pos]! := by
  rw [genMul_eq, genMulRun_spec]
  exact arrayToList_getBang _ pos

/-! ## 3. The accumulator array's shape -/

theorem mAccIn_size (pfx : String) (a0 : Array String) (i : Nat) :
    ∀ j, (mAccIn pfx a0 i j).size = a0.size := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [mAccIn, setBang_size, ih]

theorem mAccO_size (zero pfx : String) (na nb : Nat) :
    ∀ i, (mAccO zero pfx na nb i).size = na + nb := by
  intro i
  induction i with
  | zero => simp [mAccO]
  | succ i ih => rw [mAccO, setBang_size, mAccIn_size, ih]

theorem mAccIn_high (pfx : String) (a0 : Array String) (i : Nat) :
    ∀ (j pos : Nat), i + j ≤ pos → (mAccIn pfx a0 i j)[pos]! = a0[pos]! := by
  intro j
  induction j with
  | zero => intro pos _; rfl
  | succ j ih =>
      intro pos hpos
      rw [mAccIn, setBang_get_ne _ _ (by omega)]
      exact ih pos (by omega)

theorem mAccO_high (zero pfx : String) (na nb : Nat) :
    ∀ (i pos : Nat), i + nb ≤ pos → pos < na + nb → (mAccO zero pfx na nb i)[pos]! = zero := by
  intro i
  induction i with
  | zero =>
      intro pos _ hlt
      rw [mAccO, getElem!_pos _ pos (by simpa using hlt), Array.getElem_replicate]
  | succ i ih =>
      intro pos hpos hlt
      rw [mAccO, setBang_get_ne _ _ (by omega), mAccIn_high _ _ _ _ _ (by omega)]
      exact ih pos (by omega) hlt

/-- The shape of a name the accumulator array can hold: the zero slot, a column
    digit at its own position, or a column carry one position above. -/
def AccName (zero pfx : String) (ii pos : Nat) (nm : String) : Prop :=
  nm = zero
  ∨ (∃ i' j', i' < 10 ∧ j' < 10 ∧ i' + j' = pos ∧ nm = mNm pfx "p" i' j')
  ∨ (∃ i' j', i' < ii ∧ i' < 10 ∧ j' < 10 ∧ i' + j' + 1 = pos ∧ nm = mNm pfx "k" i' j')

theorem AccName.mono {zero pfx : String} {ii ii' pos : Nat} {nm : String}
    (h : AccName zero pfx ii pos nm) (hle : ii ≤ ii') : AccName zero pfx ii' pos nm := by
  rcases h with h | h | ⟨i', j', h1, h2, h3, h4, h5⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨i', j', by omega, h2, h3, h4, h5⟩)

theorem accName_notTmp {zero pfx : String} (hp : HeadOk pfx) (hzo : OutOf pfx zero)
    {ii pos : Nat} {nm : String} (h : AccName zero pfx ii pos nm) : ¬ isTmpName nm := by
  rcases h with rfl | ⟨i', j', -, -, -, rfl⟩ | ⟨i', j', -, -, -, -, rfl⟩
  · exact hzo.1
  · exact mNm_notTmp hp _ _ _
  · exact mNm_notTmp hp _ _ _

theorem accName_ne_t {zero pfx : String} (hzo : OutOf pfx zero) {ii pos : Nat} {nm : String}
    (h : AccName zero pfx ii pos nm) {i j : Nat} (hi : i < 10) (hj : j < 10) :
    nm ≠ mNm pfx "t" i j := by
  rcases h with rfl | ⟨i', j', hi', hj', -, rfl⟩ | ⟨i', j', -, hi', hj', -, rfl⟩
  · exact outOf_ne_mNm hzo _ _ _
  · exact fun he => absurd (mNm_inj hi' hj' hi hj he).1 (by decide)
  · exact fun he => absurd (mNm_inj hi' hj' hi hj he).1 (by decide)

theorem accName_ne_p {zero pfx : String} (hzo : OutOf pfx zero) {ii pos : Nat} {nm : String}
    (h : AccName zero pfx ii pos nm) {i j : Nat} (hi : i < 10) (hj : j < 10)
    (hpos : pos ≠ i + j) : nm ≠ mNm pfx "p" i j := by
  rcases h with rfl | ⟨i', j', hi', hj', hsum, rfl⟩ | ⟨i', j', -, hi', hj', -, rfl⟩
  · exact outOf_ne_mNm hzo _ _ _
  · intro he
    obtain ⟨-, e1, e2⟩ := mNm_inj hi' hj' hi hj he
    omega
  · exact fun he => absurd (mNm_inj hi' hj' hi hj he).1 (by decide)

theorem accName_ne_k {zero pfx : String} (hzo : OutOf pfx zero) {ii pos : Nat} {nm : String}
    (h : AccName zero pfx ii pos nm) {i j : Nat} (hi : i < 10) (hj : j < 10)
    (hii : ii ≤ i) : nm ≠ mNm pfx "k" i j := by
  rcases h with rfl | ⟨i', j', hi', hj', -, rfl⟩ | ⟨i', j', hlt, hi', hj', -, rfl⟩
  · exact outOf_ne_mNm hzo _ _ _
  · exact fun he => absurd (mNm_inj hi' hj' hi hj he).1 (by decide)
  · intro he
    obtain ⟨-, e1, -⟩ := mNm_inj hi' hj' hi hj he
    omega

theorem mAccIn_accName (zero pfx : String) (a0 : Array String) (ii i : Nat) (hi : i < 10)
    (h0 : ∀ pos, pos < a0.size → AccName zero pfx ii pos (a0[pos]!)) :
    ∀ j, j ≤ 10 → ∀ pos, pos < a0.size →
      AccName zero pfx ii pos ((mAccIn pfx a0 i j)[pos]!) := by
  intro j
  induction j with
  | zero => intro _ pos hpos; exact h0 pos hpos
  | succ j ih =>
      intro hj pos hpos
      rw [mAccIn]
      by_cases he : pos = i + j
      · subst he
        rw [setBang_get_eq _ _ (by rw [mAccIn_size]; exact hpos)]
        exact Or.inr (Or.inl ⟨i, j, hi, by omega, rfl, rfl⟩)
      · rw [setBang_get_ne _ _ he]
        exact ih (by omega) pos hpos

theorem mAccO_accName (zero pfx : String) (na nb : Nat) (hna : na ≤ 10) (hnb : nb ≤ 10) :
    ∀ (i : Nat), i ≤ na → ∀ pos, pos < na + nb →
      AccName zero pfx i pos ((mAccO zero pfx na nb i)[pos]!) := by
  intro i
  induction i with
  | zero =>
      intro _ pos hpos
      exact Or.inl (by
        rw [mAccO, getElem!_pos _ pos (by simpa using hpos), Array.getElem_replicate])
  | succ i ih =>
      intro hin pos hpos
      have hsz : (mAccO zero pfx na nb i).size = na + nb := mAccO_size zero pfx na nb i
      rw [mAccO]
      by_cases he : pos = i + nb
      · subst he
        rw [setBang_get_eq _ _ (by rw [mAccIn_size, hsz]; exact hpos)]
        cases nb with
        | zero => exact Or.inl rfl
        | succ m =>
            exact Or.inr (Or.inr ⟨i, m, by omega, by omega, by omega, by omega, rfl⟩)
      · rw [setBang_get_ne _ _ he]
        refine AccName.mono ?_ (Nat.le_succ i)
        exact mAccIn_accName zero pfx _ i i (by omega)
          (fun p hp => ih (by omega) p (by rw [hsz] at hp; exact hp)) nb hnb pos (by
            rw [hsz]; exact hpos)

/-! ## 4. Weighted-sum arithmetic -/

theorem accN_zero_fun (n : Nat) : accN (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [accN, ih]; simp

theorem pow32_add (a b : Nat) : (2 : Nat) ^ (32 * (a + b)) = 2 ^ (32 * a) * 2 ^ (32 * b) := by
  rw [← pow_add]
  congr 1
  omega

/-- Changing one entry of a weighted limb sum. -/
theorem accN_upd (v w : Nat → Nat) (q : Nat) :
    ∀ n, q < n → (∀ k, k < n → k ≠ q → v k = w k) →
      accN w n + 2 ^ (32 * q) * v q = accN v n + 2 ^ (32 * q) * w q := by
  intro n
  induction n with
  | zero => intro h _; omega
  | succ n ih =>
      intro hq h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | heq
      · have hvw : v n = w n := h n (by omega) (by omega)
        have hih := ih hlt (fun k hk hkq => h k (by omega) hkq)
        rw [accN, accN, hvw]
        omega
      · subst heq
        have hcong : accN v q = accN w q := accN_congr q (fun k hk => h k (by omega) (by omega))
        rw [accN, accN, hcong]
        omega

theorem bvMul_toNat {a b : BitVec 64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem column_lt {x y c k : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hc : c < 2 ^ 32)
    (hk : k < 2 ^ 32) : x * y + c + k < 2 ^ 64 := by
  have := mulxProdAddBound x y c k (2 ^ 32) hx hy hc hk
  norm_num at this ⊢
  omega

/-- One operand-scanning column, read back through the 64-bit word arithmetic. -/
theorem column_sem {av bv cv kv : BitVec 64}
    (hA : av.toNat < 2 ^ 32) (hB : bv.toNat < 2 ^ 32)
    (hC : cv.toNat < 2 ^ 32) (hK : kv.toNat < 2 ^ 32) :
    (av * bv + cv + kv).toNat = av.toNat * bv.toNat + cv.toNat + kv.toNat := by
  have hT := column_lt hA hB hC hK
  have h1 : (av * bv).toNat = av.toNat * bv.toNat := bvMul_toNat (by omega)
  have h2 : (av * bv + cv).toNat = av.toNat * bv.toNat + cv.toNat := by
    rw [bvAdd_toNat (by rw [h1]; omega), h1]
  rw [bvAdd_toNat (by rw [h2]; omega), h2]

/-! ## 5. One outer trip's column chain -/

theorem mCmdsIn_sem (zero : String) (aN bN : List String) (pfx : String) (na nb : Nat)
    (hp : HeadOk pfx) (hna : na ≤ 10) (hnb : nb ≤ 10)
    (hzo : OutOf pfx zero)
    (hao : ∀ i, i < na → OutOf pfx (aN[i]!))
    (hbo : ∀ j, j < nb → OutOf pfx (bN[j]!))
    (env : SEnvScalar)
    (hz : (envReader env zero).toNat = 0)
    (hA : ∀ i, i < na → (envReader env (aN[i]!)).toNat < 2 ^ 32)
    (hB : ∀ j, j < nb → (envReader env (bN[j]!)).toNat < 2 ^ 32)
    (i : Nat) (hi : i < na) (a0 : Array String) (hsz : a0.size = na + nb)
    (hnm : ∀ pos, pos < na + nb → AccName zero pfx i pos (a0[pos]!))
    (envO : SEnvScalar)
    (hfrO : ∀ s, OutOf pfx s → envReader envO s = envReader env s)
    (hval0 : ∀ pos, pos < na + nb → (envReader envO (a0[pos]!)).toNat < 2 ^ 32) :
    ∀ j, j ≤ nb → ∀ envJ, semList (mCmdsIn zero pfx aN bN a0 i j) envO = some envJ →
      (∀ s, OutOf pfx s → envReader envJ s = envReader envO s)
      ∧ (∀ pos, pos < na + nb → (envReader envJ ((mAccIn pfx a0 i j)[pos]!)).toNat < 2 ^ 32)
      ∧ (envReader envJ (mCar zero pfx i j)).toNat < 2 ^ 32
      ∧ accN (fun pos => (envReader envJ ((mAccIn pfx a0 i j)[pos]!)).toNat) (na + nb)
            + 2 ^ (32 * (i + j)) * (envReader envJ (mCar zero pfx i j)).toNat
          = accN (fun pos => (envReader envO (a0[pos]!)).toNat) (na + nb)
            + 2 ^ (32 * i) * (envReader env (aN[i]!)).toNat
                * accN (fun k => (envReader env (bN[k]!)).toNat) j := by
  have hi10 : i < 10 := by omega
  have hAcc : ∀ j, j ≤ nb → ∀ pos, pos < na + nb →
      AccName zero pfx i pos ((mAccIn pfx a0 i j)[pos]!) := by
    intro j hj pos hpos
    exact mAccIn_accName zero pfx a0 i i hi10 (fun p hp => hnm p (by rw [hsz] at hp; exact hp))
      j (by omega) pos (by rw [hsz]; exact hpos)
  intro j
  induction j with
  | zero =>
      intro _ envJ hsem
      simp only [mCmdsIn, semList] at hsem
      obtain rfl : envJ = envO := (Option.some.inj hsem).symm
      refine ⟨fun _ _ => rfl, fun pos hpos => hval0 pos hpos, ?_, ?_⟩
      · rw [show mCar zero pfx i 0 = zero from rfl, hfrO zero hzo, hz]; norm_num
      · rw [show mCar zero pfx i 0 = zero from rfl, hfrO zero hzo, hz]
        simp [accN, mAccIn]
  | succ j ih =>
      intro hjn env' hsem
      rw [mCmdsIn] at hsem
      obtain ⟨envJ, hpre, htrip⟩ := splitApp hsem
      obtain ⟨hfr, hbnd, hcar, hacc⟩ := ih (by omega) envJ hpre
      have hj : j < nb := by omega
      have hj10 : j < 10 := by omega
      have hq : i + j < na + nb := by omega
      simp only [mTrip] at htrip
      obtain ⟨e1, h1, r1⟩ := peel htrip
      obtain ⟨e2, h2, r2⟩ := peel r1
      obtain ⟨e3, h3, r3⟩ := peel r2
      have hE : env' = e3 := (Option.some.inj r3).symm
      subst hE
      set tn := mNm pfx "t" i j with htnd
      set pn := mNm pfx "p" i j with hpnd
      set kn := mNm pfx "k" i j with hknd
      have htnt : ¬ isTmpName tn := mNm_notTmp hp _ _ _
      have hpnt : ¬ isTmpName pn := mNm_notTmp hp _ _ _
      have hknt : ¬ isTmpName kn := mNm_notTmp hp _ _ _
      have htn_pn : tn ≠ pn := fun he => absurd (mNm_inj hi10 hj10 hi10 hj10 he).1 (by decide)
      have hpn_kn : pn ≠ kn := fun he => absurd (mNm_inj hi10 hj10 hi10 hj10 he).1 (by decide)
      -- the operand and carry values entering the column
      have hfrJ : ∀ s, OutOf pfx s → envReader envJ s = envReader env s :=
        fun s hs => (hfr s hs).trans (hfrO s hs)
      have hAi : envReader envJ (aN[i]!) = envReader env (aN[i]!) := hfrJ _ (hao i hi)
      have hBj : envReader envJ (bN[j]!) = envReader env (bN[j]!) := hfrJ _ (hbo j hj)
      set A := (envReader env (aN[i]!)).toNat with hAd
      set B := (envReader env (bN[j]!)).toNat with hBd
      set C := (envReader envJ ((mAccIn pfx a0 i j)[i + j]!)).toNat with hCd
      set K := (envReader envJ (mCar zero pfx i j)).toNat with hKd
      have hAlt : A < 2 ^ 32 := hA i hi
      have hBlt : B < 2 ^ 32 := hB j hj
      have hClt : C < 2 ^ 32 := hbnd (i + j) hq
      have hKlt : K < 2 ^ 32 := hcar
      have hT : A * B + C + K < 2 ^ 64 := column_lt hAlt hBlt hClt hKlt
      -- the column's three commands
      have hv1 : (envReader e1 tn).toNat = A * B + C + K := by
        rw [stepAt h1]
        simp only [SExpr.evalBV, sv, hAi, hBj]
        exact column_sem hAlt hBlt hClt hKlt
      have ht2 : envReader e2 tn = envReader e1 tn := stepOff h2 tn htnt htn_pn
      have hv2 : (envReader e2 pn).toNat = (A * B + C + K) % 2 ^ 32 := by
        rw [stepAt h2]
        simp only [SExpr.evalBV, sv]
        rw [bvAnd_mask, hv1]
      have hv3 : (envReader env' kn).toNat = (A * B + C + K) / 2 ^ 32 := by
        rw [stepAt h3]
        simp only [SExpr.evalBV, sv]
        rw [bvShr32, ht2, hv1]
      have hpFinal : (envReader env' pn).toNat = (A * B + C + K) % 2 ^ 32 := by
        rw [stepOff h3 pn hpnt hpn_kn, hv2]
      -- every other accumulator slot is untouched
      have hkeep : ∀ pos, pos < na + nb → pos ≠ i + j →
          envReader env' ((mAccIn pfx a0 i j)[pos]!)
            = envReader envJ ((mAccIn pfx a0 i j)[pos]!) := by
        intro pos hpos hne
        have hnmp := hAcc j (by omega) pos hpos
        rw [stepOff h3 _ (accName_notTmp hp hzo hnmp)
              (accName_ne_k hzo hnmp hi10 hj10 (le_refl i)),
          stepOff h2 _ (accName_notTmp hp hzo hnmp)
              (accName_ne_p hzo hnmp hi10 hj10 hne),
          stepOff h1 _ (accName_notTmp hp hzo hnmp)
              (accName_ne_t hzo hnmp hi10 hj10)]
      have hfr' : ∀ s, OutOf pfx s → envReader env' s = envReader envO s := by
        intro s hs
        rw [stepOff h3 s hs.1 (outOf_ne_mNm hs _ _ _),
          stepOff h2 s hs.1 (outOf_ne_mNm hs _ _ _),
          stepOff h1 s hs.1 (outOf_ne_mNm hs _ _ _)]
        exact hfr s hs
      -- the new accumulator array
      have hszIn : (mAccIn pfx a0 i j).size = na + nb := by rw [mAccIn_size, hsz]
      have hnewAt : (mAccIn pfx a0 i (j + 1))[i + j]! = pn := by
        rw [mAccIn, setBang_get_eq _ _ (by rw [hszIn]; exact hq)]
      have hnewOff : ∀ pos, pos ≠ i + j →
          (mAccIn pfx a0 i (j + 1))[pos]! = (mAccIn pfx a0 i j)[pos]! := by
        intro pos hne
        rw [mAccIn, setBang_get_ne _ _ hne]
      have hvalNew : ∀ pos, pos < na + nb →
          (envReader env' ((mAccIn pfx a0 i (j + 1))[pos]!)).toNat
            = if pos = i + j then (A * B + C + K) % 2 ^ 32
              else (envReader envJ ((mAccIn pfx a0 i j)[pos]!)).toNat := by
        intro pos hpos
        by_cases he : pos = i + j
        · rw [ite_eq_left he, he, hnewAt, hpFinal]
        · rw [ite_eq_right he, hnewOff pos he, hkeep pos hpos he]
      refine ⟨hfr', ?_, ?_, ?_⟩
      · intro pos hpos
        rw [hvalNew pos hpos]
        split
        · exact Nat.mod_lt _ (by norm_num)
        · exact hbnd pos hpos
      · rw [show mCar zero pfx i (j + 1) = kn from rfl, hv3]
        exact Nat.div_lt_of_lt_mul (by norm_num at hT ⊢; omega)
      · rw [show mCar zero pfx i (j + 1) = kn from rfl, hv3]
        -- the column identity
        have hupd := accN_upd (fun pos => (envReader envJ ((mAccIn pfx a0 i j)[pos]!)).toNat)
          (fun pos => (envReader env' ((mAccIn pfx a0 i (j + 1))[pos]!)).toNat) (i + j)
          (na + nb) hq (fun k hk hkq => by
            rw [hvalNew k hk, ite_eq_right hkq])
        rw [hvalNew (i + j) hq, ite_eq_left rfl] at hupd
        rw [pow32_add i (j + 1), pow32_add j 1, pow32_add i j] at *
        rw [accN_succ]
        set p2 := (2 : Nat) ^ (32 * i) with hp2
        set q2 := (2 : Nat) ^ (32 * j) with hq2
        set X := accN (fun pos => (envReader env' ((mAccIn pfx a0 i (j + 1))[pos]!)).toNat)
          (na + nb) with hXd
        set Y := accN (fun pos => (envReader envJ ((mAccIn pfx a0 i j)[pos]!)).toNat) (na + nb)
          with hYd
        set S0 := accN (fun pos => (envReader envO (a0[pos]!)).toNat) (na + nb) with hS0d
        set Sb := accN (fun k => (envReader env (bN[k]!)).toNat) j with hSbd
        have hmd : (A * B + C + K) % 2 ^ 32 + 2 ^ 32 * ((A * B + C + K) / 2 ^ 32)
            = A * B + C + K := Nat.mod_add_div _ _
        have hpow1 : (2 : Nat) ^ (32 * 1) = 2 ^ 32 := by norm_num
        rw [hpow1]
        refine Nat.add_right_cancel (m := p2 * q2 * C) ?_
        calc X + p2 * (q2 * 2 ^ 32) * ((A * B + C + K) / 2 ^ 32) + p2 * q2 * C
            = (X + p2 * q2 * C)
                + p2 * q2 * (2 ^ 32 * ((A * B + C + K) / 2 ^ 32)) := by ring
          _ = (Y + p2 * q2 * ((A * B + C + K) % 2 ^ 32))
                + p2 * q2 * (2 ^ 32 * ((A * B + C + K) / 2 ^ 32)) := by rw [hupd]
          _ = Y + p2 * q2 * ((A * B + C + K) % 2 ^ 32
                + 2 ^ 32 * ((A * B + C + K) / 2 ^ 32)) := by ring
          _ = Y + p2 * q2 * (A * B + C + K) := by rw [hmd]
          _ = (Y + p2 * q2 * K) + p2 * A * (q2 * B) + p2 * q2 * C := by ring
          _ = (S0 + p2 * A * Sb) + p2 * A * (q2 * B) + p2 * q2 * C := by rw [hacc]
          _ = S0 + p2 * A * (Sb + q2 * B) + p2 * q2 * C := by ring

/-! ## 6. The outer scan -/

theorem mCmdsO_sem (zero : String) (aN bN : List String) (pfx : String)
    (hp : HeadOk pfx) (hna : aN.length ≤ 10) (hnb : bN.length ≤ 10)
    (hzo : OutOf pfx zero)
    (hao : ∀ i, i < aN.length → OutOf pfx (aN[i]!))
    (hbo : ∀ j, j < bN.length → OutOf pfx (bN[j]!))
    (env : SEnvScalar)
    (hz : (envReader env zero).toNat = 0)
    (hA : ∀ i, i < aN.length → (envReader env (aN[i]!)).toNat < 2 ^ 32)
    (hB : ∀ j, j < bN.length → (envReader env (bN[j]!)).toNat < 2 ^ 32) :
    ∀ i, i ≤ aN.length → ∀ envI, semList (mCmdsO zero pfx aN bN i) env = some envI →
      (∀ s, OutOf pfx s → envReader envI s = envReader env s)
      ∧ (∀ pos, pos < aN.length + bN.length →
          (envReader envI ((mAccO zero pfx aN.length bN.length i)[pos]!)).toNat < 2 ^ 32)
      ∧ accN (fun pos =>
            (envReader envI ((mAccO zero pfx aN.length bN.length i)[pos]!)).toNat)
            (aN.length + bN.length)
          = accN (fun k => (envReader env (aN[k]!)).toNat) i
            * accN (fun k => (envReader env (bN[k]!)).toNat) bN.length := by
  set na := aN.length with hnad
  set nb := bN.length with hnbd
  intro i
  induction i with
  | zero =>
      intro _ envI hsem
      simp only [mCmdsO, semList] at hsem
      obtain rfl : envI = env := (Option.some.inj hsem).symm
      have hall : ∀ pos, pos < na + nb → (mAccO zero pfx na nb 0)[pos]! = zero := by
        intro pos hpos
        rw [mAccO, getElem!_pos _ pos (by simpa using hpos), Array.getElem_replicate]
      refine ⟨fun _ _ => rfl, fun pos hpos => by rw [hall pos hpos, hz]; norm_num, ?_⟩
      rw [accN_congr (w := fun _ => 0) (na + nb)
        (fun k hk => by rw [hall k hk, hz]), accN_zero_fun]
      simp [accN]
  | succ i ih =>
      intro hin envI hsem
      rw [mCmdsO] at hsem
      obtain ⟨E, hpre, hblk⟩ := splitApp hsem
      obtain ⟨hfr, hbnd, hacc⟩ := ih (by omega) E hpre
      have hi : i < na := by omega
      have hsz : (mAccO zero pfx na nb i).size = na + nb := mAccO_size zero pfx na nb i
      obtain ⟨hfr2, hbnd2, hcar2, hacc2⟩ :=
        mCmdsIn_sem zero aN bN pfx na nb hp hna hnb hzo hao hbo env hz hA hB i hi
          (mAccO zero pfx na nb i) hsz
          (mAccO_accName zero pfx na nb hna hnb i (by omega)) E hfr hbnd
          nb (le_refl nb) envI hblk
      -- the outer trip's single array update
      have hszIn : (mAccIn pfx (mAccO zero pfx na nb i) i nb).size = na + nb := by
        rw [mAccIn_size, hsz]
      have hq : i + nb < na + nb := by omega
      have holdZero : (mAccIn pfx (mAccO zero pfx na nb i) i nb)[i + nb]! = zero := by
        rw [mAccIn_high _ _ _ _ _ (le_refl _)]
        exact mAccO_high zero pfx na nb i (i + nb) (le_refl _) hq
      have hnewAt : (mAccO zero pfx na nb (i + 1))[i + nb]! = mCar zero pfx i nb := by
        rw [mAccO, setBang_get_eq _ _ (by rw [hszIn]; exact hq)]
      have hnewOff : ∀ pos, pos ≠ i + nb →
          (mAccO zero pfx na nb (i + 1))[pos]!
            = (mAccIn pfx (mAccO zero pfx na nb i) i nb)[pos]! := by
        intro pos hne
        rw [mAccO, setBang_get_ne _ _ hne]
      have hzeroE : (envReader envI zero).toNat = 0 := by
        rw [hfr2 zero hzo, hfr zero hzo, hz]
      have hfrOut : ∀ s, OutOf pfx s → envReader envI s = envReader env s :=
        fun s hs => (hfr2 s hs).trans (hfr s hs)
      have hbndOut : ∀ pos, pos < na + nb →
          (envReader envI ((mAccO zero pfx na nb (i + 1))[pos]!)).toNat < 2 ^ 32 := by
        intro pos hpos
        by_cases he : pos = i + nb
        · rw [he, hnewAt]; exact hcar2
        · rw [hnewOff pos he]; exact hbnd2 pos hpos
      refine ⟨hfrOut, hbndOut, ?_⟩
      have hupd := accN_upd
        (fun pos => (envReader envI ((mAccIn pfx (mAccO zero pfx na nb i) i nb)[pos]!)).toNat)
        (fun pos => (envReader envI ((mAccO zero pfx na nb (i + 1))[pos]!)).toNat)
        (i + nb) (na + nb) hq (fun k hk hkq => by rw [hnewOff k hkq])
      rw [holdZero, hzeroE, hnewAt] at hupd
      rw [accN_succ]
      set p2 := (2 : Nat) ^ (32 * i) with hp2d
      set Bv := accN (fun k => (envReader env (bN[k]!)).toNat) nb with hBvd
      set Av := accN (fun k => (envReader env (aN[k]!)).toNat) i with hAvd
      set Ai := (envReader env (aN[i]!)).toNat with hAid
      set W := accN (fun pos =>
        (envReader envI ((mAccO zero pfx na nb (i + 1))[pos]!)).toNat) (na + nb) with hWd
      set V := accN (fun pos =>
        (envReader envI ((mAccIn pfx (mAccO zero pfx na nb i) i nb)[pos]!)).toNat) (na + nb)
        with hVd
      have hWV : W = V + 2 ^ (32 * (i + nb)) * (envReader envI (mCar zero pfx i nb)).toNat := by
        omega
      rw [hWV, hacc2, hacc]
      ring

/-! ## 7. The product -/

/-- **The operand-scanning multiply's accumulator names hold the product.** Under
    a private prefix, a zero slot holding `0` and both operands in 32-bit limbs,
    the `na + nb` names `genMul` returns hold, at radix `2 ^ 32`, the product of
    the two operands' limb readouts, and every name outside the prefix keeps its
    value. -/
theorem genMul_prod (zero : String) (aN bN : List String) (pfx : String)
    (hp : HeadOk pfx) (hna : aN.length ≤ 10) (hnb : bN.length ≤ 10)
    (hzo : OutOf pfx zero)
    (hao : ∀ i, i < aN.length → OutOf pfx (aN[i]!))
    (hbo : ∀ j, j < bN.length → OutOf pfx (bN[j]!))
    (env env' : SEnvScalar)
    (hz : (envReader env zero).toNat = 0)
    (hA : ∀ i, i < aN.length → (envReader env (aN[i]!)).toNat < 2 ^ 32)
    (hB : ∀ j, j < bN.length → (envReader env (bN[j]!)).toNat < 2 ^ 32)
    (hsem : semList (genMul zero aN bN pfx).1 env = some env') :
    (∀ s, OutOf pfx s → envReader env' s = envReader env s)
    ∧ (∀ pos, pos < aN.length + bN.length →
        (envReader env' ((genMul zero aN bN pfx).2[pos]!)).toNat < 2 ^ 32)
    ∧ accN (fun pos => (envReader env' ((genMul zero aN bN pfx).2[pos]!)).toNat)
          (aN.length + bN.length)
      = accN (fun k => (envReader env (aN[k]!)).toNat) aN.length
        * accN (fun k => (envReader env (bN[k]!)).toNat) bN.length := by
  rw [genMul_cmds] at hsem
  obtain ⟨hfr, hbnd, hacc⟩ :=
    mCmdsO_sem zero aN bN pfx hp hna hnb hzo hao hbo env hz hA hB
      aN.length (le_refl _) env' hsem
  refine ⟨hfr, ?_, ?_⟩
  · intro pos hpos
    rw [genMul_names]
    exact hbnd pos hpos
  · rw [accN_congr
      (v := fun pos => (envReader env' ((genMul zero aN bN pfx).2[pos]!)).toNat)
      (w := fun pos =>
        (envReader env' ((mAccO zero pfx aN.length bN.length aN.length)[pos]!)).toNat)
      (aN.length + bN.length) (fun k _ =>
        congrArg (fun w => (envReader env' w).toNat) (genMul_names zero pfx aN bN k))]
    exact hacc

#check @genMul_prod

end CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickProduct
