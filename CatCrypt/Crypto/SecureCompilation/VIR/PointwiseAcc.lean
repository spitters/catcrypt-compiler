/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord

/-!
# Accumulate-then-reduce: the inner product of a row with a vector in the NTT domain

For a row length `k`, output lane `i` of the inner product `∑_{j < k} a_j ∘ b_j` of `k`
pairs of polynomials in the NTT domain at block length `2` (`L = logN − 1`, ML-KEM) is
computed with the products of signed `w`-bit words accumulated at `2 w` bits and one
signed Montgomery reduction `smontAccW` per output word.

* Odd lane `i` (second output of pair `i / 2`): `R(∑_j a_j[i−1] b_j[i] + a_j[i] b_j[i−1])`,
  `2 k` products accumulated, one reduction.
* Even lane `i` (first output): `R(R(∑_j a_j[i+1] b_j[i+1]) · ζ + ∑_j a_j[i] b_j[i])`. The
  inner reduction of the twiddled sum is applied once to the accumulated sum, not once per
  term; it remains because the product of the unreduced sum with the twiddle `ζ` does not
  fit `2 w` bits at any ML-KEM instance.

The reduction points are justified by the closed-form bounds certificate `AccSched.Ok k`
on `ℕ`, decided by `decide +kernel` per instance: every partial sum lies inside the
`2 w`-bit accumulator, the inner reduction lies within `midB` and both outputs within
`outB`.

## Main definitions

* `macK`, `macW`: the multiply-accumulate of `n` products of sign extensions into a
  `2 w`-bit accumulator, as a `jasminDialect` schedule in continuation form and as words.
* `acc0K`, `acc1K`, `acc0W`, `acc1W`: the two outputs of a pair, accumulated over `k`
  terms, as schedules and as words.
* `AccSched`, `AccSched.Ok`: the bounds certificate for a row length `k`.
* `accProgW`: the lowering on `2 · k · 2 ^ logN` input lanes (the `k` first operands, then
  the `k` second operands, each `2 ^ logN` lanes) and `2 ^ logN` output lanes.
* `mlkemAcc2`, `mlkemAcc3`, `mlkemAcc4`: the ML-KEM instances at `k = 2, 3, 4`.

## Main results

* `macK_denote`, `acc0K_denote`, `acc1K_denote`: the schedules denote their word
  semantics.
* `macW_toInt`: inside the accumulator the word sum is the integer sum.
* `accTail_spec`: the final reduction pass on accumulator words with integer bounds.
* `acc0W_spec`, `acc1W_spec`: each output is the reduction of its integer sum and is at
  most `outB` in absolute value.
* `accProgW_denote`: every output word of `accProgW` is at most `outB` in absolute value
  and, times `2 ^ w`, is `∑_{j < k} blockMul 2` of the operand pairs, modulo `q`.
* `accProgW_basemulF`: the same against `∑_{j < k} basemulF` at `L = logN − 1`.
* `mlkemAcc2_ok`, `mlkemAcc3_ok`, `mlkemAcc4_ok`: the instance certificates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.RingDialect (Limbs basemulF rowLanes)
open Finset (range)

/-! ## 1. The multiply-accumulate schedule -/

/-- A variable seen past one multiply-accumulate step. -/
def upMac {w : ℕ} {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (v : Var Γ t) :
    Var (Rd w :: X7 w Γ) t := .there (up7 v)

/-- `acc + ∑_{j < n} sext (u j) · sext (v j)` at `2 w` bits, then `k` at the result. -/
def macK {t : jasminDialect.Ty} (w : ℕ) : {Γ : Ctxt jasminDialect} → (n : ℕ) →
    (u v : ℕ → Var Γ (Rw w)) → Var Γ (Rd w) →
    (∀ {Γ' : Ctxt jasminDialect}, Ctxt.Hom Γ Γ' → Var Γ' (Rd w) → Com jasminDialect Γ' t) →
    Com jasminDialect Γ t
  | _, 0, _, _, acc, k => k (fun v => v) acc
  | _, n + 1, u, v, acc, k =>
    prodK w (u 0) (v 0) <|
    .var (binE .add (2 * w) (up7 acc) .here) <|
    macK w n (fun j => upMac (u (j + 1))) (fun j => upMac (v (j + 1))) .here
      (fun h r => k (fun x => h (upMac x)) r)

/-- The word semantics of `macK`. -/
def macW (w : ℕ) : (n : ℕ) → (ℕ → BitVec w) → (ℕ → BitVec w) → BitVec (2 * w) →
    BitVec (2 * w)
  | 0, _, _, acc => acc
  | n + 1, u, v, acc =>
    macW w n (fun j => u (j + 1)) (fun j => v (j + 1)) (acc + sextW (u 0) * sextW (v 0))

/-- The continuation of `macK w n u v acc k` is called at an extension `Γ'` of `Γ`, at a
valuation agreeing with `V` along the renaming, and at a variable holding `macW`. A
continuation producing `r` under those two facts makes the schedule produce `r`. -/
theorem macK_denote {t : jasminDialect.Ty} (w : ℕ) :
    ∀ {Γ : Ctxt jasminDialect} (n : ℕ) (u v : ℕ → Var Γ (Rw w)) (acc : Var Γ (Rd w))
      (k : ∀ {Γ' : Ctxt jasminDialect}, Ctxt.Hom Γ Γ' → Var Γ' (Rd w) →
        Com jasminDialect Γ' t)
      (V : Valuation Γ) (uv vv : ℕ → BitVec w) (av : BitVec (2 * w))
      (r : ⟦t⟧),
      (∀ j, (u j).lookup V = uv j) → (∀ j, (v j).lookup V = vv j) → acc.lookup V = av →
      (∀ {Γ' : Ctxt jasminDialect} (h : Ctxt.Hom Γ Γ') (a : Var Γ' (Rd w))
          (V' : Valuation Γ'),
          (∀ {s : jasminDialect.Ty} (x : Var Γ s), (h x).lookup V' = x.lookup V) →
          a.lookup V' = macW w n uv vv av → (k h a).denote V' = r) →
      (macK w n u v acc k).denote V = r
  | _, 0, _, _, _, _, V, _, _, _, _, _, _, hacc, hk => hk _ _ V (fun _ => rfl) hacc
  | _, n + 1, u, v, acc, k, V, uv, vv, av, r, hu, hv, hacc, hk => by
    refine macK_denote w n _ _ _ _ _ (fun j => uv (j + 1)) (fun j => vv (j + 1))
      (av + sextW (uv 0) * sextW (vv 0)) r (fun j => hu (j + 1)) (fun j => hv (j + 1)) ?_ ?_
    · show (show BitVec (2 * w) from acc.lookup V) + sextW (show BitVec w from (u 0).lookup V)
          * sextW (show BitVec w from (v 0).lookup V) = _
      rw [hacc, hu 0, hv 0]
    · intro Γ' h a V' hh ha
      exact hk _ a V' (fun x => hh (upMac x)) ha

/-! ## 2. The two outputs of a pair, accumulated over a row -/

/-- A variable seen past a reduction, a sign extension, a constant and a product. -/
def upTw {w : ℕ} {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (v : Var Γ t) :
    Var (Rd w :: Rd w :: X3 w (X11 w Γ)) t := .there (.there (up3 (up11 v)))

/-- The first output of pair `c` accumulated over `n` terms:
`R(sext R(∑_j a₁ⱼ b₁ⱼ) · z + ∑_j a₀ⱼ b₀ⱼ)`, `z` a `2 w`-bit constant. -/
def acc0K {Γ : Ctxt jasminDialect} (w q qinv z n : ℕ) (a0 a1 b0 b1 : ℕ → Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  .var (constE (2 * w) 0) <|
  macK w n (fun j => .there (a1 j)) (fun j => .there (b1 j)) .here fun h r =>
  redK w q qinv r <|
  sextK w .here <|
  .var (constE (2 * w) z) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  macK w n (fun j => upTw (h (.there (a0 j)))) (fun j => upTw (h (.there (b0 j)))) .here
    fun _ s => redK w q qinv s (.ret .here)

/-- The second output of pair `c` accumulated over `n` terms:
`R(∑_j a₀ⱼ b₁ⱼ + ∑_j a₁ⱼ b₀ⱼ)`. -/
def acc1K {Γ : Ctxt jasminDialect} (w q qinv n : ℕ) (a0 a1 b0 b1 : ℕ → Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  .var (constE (2 * w) 0) <|
  macK w n (fun j => .there (a0 j)) (fun j => .there (b1 j)) .here fun h r =>
  macK w n (fun j => h (.there (a1 j))) (fun j => h (.there (b0 j))) r
    fun _ s => redK w q qinv s (.ret .here)

/-- The word semantics of `acc0K`. -/
def acc0W (w q qinv z n : ℕ) (a0 a1 b0 b1 : ℕ → BitVec w) : BitVec w :=
  smontAccW w q qinv (macW w n a0 b0
    (sextW (smontAccW w q qinv (macW w n a1 b1 0)) * BitVec.ofNat (2 * w) z))

/-- The word semantics of `acc1K`. -/
def acc1W (w q qinv n : ℕ) (a0 a1 b0 b1 : ℕ → BitVec w) : BitVec w :=
  smontAccW w q qinv (macW w n a1 b0 (macW w n a0 b1 0))

theorem acc0K_denote {Γ : Ctxt jasminDialect} (w q qinv z n : ℕ)
    (a0 a1 b0 b1 : ℕ → Var Γ (Rw w)) (V : Valuation Γ) :
    (acc0K w q qinv z n a0 a1 b0 b1).denote V
      = acc0W w q qinv z n (fun j => (a0 j).lookup V) (fun j => (a1 j).lookup V)
          (fun j => (b0 j).lookup V) (fun j => (b1 j).lookup V) := by
  refine macK_denote w n _ _ _ _ _ (fun j => (a1 j).lookup V) (fun j => (b1 j).lookup V) 0 _
    (fun _ => rfl) (fun _ => rfl) rfl ?_
  intro Γ' h a V' hh ha
  rw [redK_denote, sextK_denote]
  refine macK_denote w n _ _ _ _ _ (fun j => (a0 j).lookup V) (fun j => (b0 j).lookup V)
    (sextW (smontAccW w q qinv (macW w n (fun j => (a1 j).lookup V)
      (fun j => (b1 j).lookup V) 0)) * BitVec.ofNat (2 * w) z) _
    (fun j => hh (.there (a0 j))) (fun j => hh (.there (b0 j))) ?_ ?_
  · show sextW (smontAccW w q qinv (show BitVec (2 * w) from a.lookup V')) * _ = _
    rw [ha]
    rfl
  · intro Γ'' h' s V'' _ hs
    rw [redK_denote]
    show smontAccW w q qinv (show BitVec (2 * w) from s.lookup V'') = _
    rw [hs]
    rfl

theorem acc1K_denote {Γ : Ctxt jasminDialect} (w q qinv n : ℕ)
    (a0 a1 b0 b1 : ℕ → Var Γ (Rw w)) (V : Valuation Γ) :
    (acc1K w q qinv n a0 a1 b0 b1).denote V
      = acc1W w q qinv n (fun j => (a0 j).lookup V) (fun j => (a1 j).lookup V)
          (fun j => (b0 j).lookup V) (fun j => (b1 j).lookup V) := by
  refine macK_denote w n _ _ _ _ _ (fun j => (a0 j).lookup V) (fun j => (b1 j).lookup V) 0 _
    (fun _ => rfl) (fun _ => rfl) rfl ?_
  intro Γ' h a V' hh ha
  refine macK_denote w n _ _ _ _ _ (fun j => (a1 j).lookup V) (fun j => (b0 j).lookup V)
    _ _ (fun j => hh (.there (a1 j))) (fun j => hh (.there (b0 j))) ha ?_
  intro Γ'' h' s V'' _ hs
  rw [redK_denote]
  show smontAccW w q qinv (show BitVec (2 * w) from s.lookup V'') = _
  rw [hs]
  rfl

/-! ## 3. Exact accumulation -/

theorem toInt_zero_lit (n : ℕ) : (0 : BitVec n).toInt = 0 := by simp

/-- A sum of `n` products of factors bounded by `A` and `B` is at most `n · A · B`. -/
theorem abs_sum_mul_le (A B : ℤ) (n : ℕ) (u v : ℕ → ℤ) (hu : ∀ j, j < n → |u j| ≤ A)
    (hv : ∀ j, j < n → |v j| ≤ B) : |∑ j ∈ range n, u j * v j| ≤ n * (A * B) := by
  calc |∑ j ∈ range n, u j * v j| ≤ ∑ j ∈ range n, |u j * v j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range n, A * B := Finset.sum_le_sum fun j hj => by
        have hj' := Finset.mem_range.1 hj
        rw [abs_mul]
        exact mul_le_mul (hu j hj') (hv j hj') (abs_nonneg _) (le_trans (abs_nonneg _) (hu j hj'))
    _ = n * (A * B) := by simp

/-- Inside the accumulator the word sum is the integer sum. -/
theorem macW_toInt (w : ℕ) (A B : ℤ) : ∀ (n : ℕ) (u v : ℕ → BitVec w) (acc : BitVec (2 * w)),
    (∀ j, j < n → |(u j).toInt| ≤ A) → (∀ j, j < n → |(v j).toInt| ≤ B) →
    2 * (|acc.toInt| + n * (A * B)) < ((2 ^ (2 * w) : ℕ) : ℤ) →
    (macW w n u v acc).toInt = acc.toInt + ∑ j ∈ range n, (u j).toInt * (v j).toInt
  | 0, _, _, _, _, _, _ => by simp [macW]
  | n + 1, u, v, acc, hu, hv, hb => by
    have hA : 0 ≤ A := le_trans (abs_nonneg _) (hu 0 (by omega))
    have hp : |(u 0).toInt * (v 0).toInt| ≤ A * B := by
      rw [abs_mul]
      exact mul_le_mul (hu 0 (by omega)) (hv 0 (by omega)) (abs_nonneg _) hA
    have hB : 0 ≤ A * B := le_trans (abs_nonneg _) hp
    have hn : ((n + 1 : ℕ) : ℤ) * (A * B) = n * (A * B) + A * B := by push_cast; ring
    have hnAB : 0 ≤ (n : ℤ) * (A * B) := by positivity
    rw [hn] at hb
    have hs := abs_add_le acc.toInt ((u 0).toInt * (v 0).toInt)
    have hac := abs_nonneg acc.toInt
    have em : (sextW (u 0) * sextW (v 0)).toInt = (u 0).toInt * (v 0).toInt := by
      rw [toInt_mul_exact _ _ (by rw [sextW_toInt, sextW_toInt]; linarith), sextW_toInt,
        sextW_toInt]
    have e : (acc + sextW (u 0) * sextW (v 0)).toInt
        = acc.toInt + (u 0).toInt * (v 0).toInt := by
      rw [toInt_add_exact _ _ (by rw [em]; linarith), em]
    rw [macW, macW_toInt w A B n (fun j => u (j + 1)) (fun j => v (j + 1)) _
      (fun j hj => hu (j + 1) (by omega)) (fun j hj => hv (j + 1) (by omega))
      (by rw [e]; linarith), e, Finset.sum_range_succ']
    ring

/-- The accumulator start value adds to the accumulation from zero. -/
theorem macW_add (w : ℕ) : ∀ (n : ℕ) (u v : ℕ → BitVec w) (acc : BitVec (2 * w)),
    macW w n u v acc = acc + macW w n u v 0
  | 0, _, _, acc => by simp [macW]
  | n + 1, u, v, acc => by
    simp only [macW]
    rw [macW_add w n _ _ (acc + _), macW_add w n _ _ (0 + _)]
    simp [BitVec.add_assoc]

/-! ## 4. The bounds certificate -/

/-- The parameters of the row accumulation modulo `q` in signed `w`-bit words: the
Montgomery constant `qinv = q⁻¹ mod 2 ^ w`, the bounds of the first and second operands,
the bound of the inner reduction `R(∑_j a₁ⱼ b₁ⱼ)` and the output bound, all in absolute
value. -/
structure AccSched where
  /-- The word width. -/
  w : ℕ
  /-- The modulus. -/
  q : ℕ
  /-- The Montgomery constant `q⁻¹ mod 2 ^ w`. -/
  qinv : ℕ
  /-- Every first-operand word is at most `inA` in absolute value. -/
  inA : ℕ
  /-- Every second-operand word is at most `inB` in absolute value. -/
  inB : ℕ
  /-- The inner reduction `R(∑_j a₁ⱼ b₁ⱼ)` is at most `midB` in absolute value. -/
  midB : ℕ
  /-- Every output word is at most `outB` in absolute value. -/
  outB : ℕ

/-- The side condition of the accumulation over `k` terms: the Montgomery constant, the
twiddle constants fit `2 w` bits, the `k`-term sum reduced by the inner reduction lies
within `midB`, the `k`-term sum plus the twiddled inner reduction and the `2 k`-term sum
of the second output lie within `outB`, each bound below `2 ^ (w − 1)`. Every partial sum
then lies inside the `2 w`-bit accumulator. -/
def AccSched.Ok (S : AccSched) (k : ℕ) : Prop :=
  (S.q * S.qinv) % 2 ^ S.w = 1 ∧ 2 * S.q < 2 ^ (2 * S.w) ∧
    2 * (k * (S.inA * S.inB)) + 2 ^ S.w * S.q ≤ 2 * 2 ^ S.w * S.midB ∧
    2 * S.midB < 2 ^ S.w ∧
    2 * (k * (S.inA * S.inB)) + S.midB * S.q + 2 ^ S.w * S.q ≤ 2 * 2 ^ S.w * S.outB ∧
    2 * (2 * k * (S.inA * S.inB)) + 2 ^ S.w * S.q ≤ 2 * 2 ^ S.w * S.outB ∧
    2 * S.outB < 2 ^ S.w

instance (S : AccSched) (k : ℕ) : Decidable (S.Ok k) := by
  unfold AccSched.Ok; infer_instance

/-- Under `AccSched.Ok k`, `k` accumulated products fit twice over in the `2 w`-bit
accumulator. -/
theorem accSched_ok_fit {S : AccSched} {k : ℕ} (hS : S.Ok k) :
    2 * (2 * (k * (S.inA * S.inB))) < 2 ^ (2 * S.w) := by
  obtain ⟨-, -, -, -, -, h6, h7⟩ := hS
  have e : 2 ^ (2 * S.w) = 2 ^ S.w * 2 ^ S.w := by rw [two_mul, pow_add]
  have hp : 0 < 2 ^ S.w := by positivity
  rw [e]
  nlinarith

/-! ## 5. The word theorems -/

section Spec

variable (S : AccSched) (k : ℕ)

/-- **The final reduction pass.** Under `AccSched.Ok k`, on accumulators `s₀₀`, `s₁₁` at
most `k · inA · inB` and `s₀₁` at most `2 k · inA · inB` in absolute value, and a twiddle
constant `z` reading `ζ` with `2 |ζ| ≤ q`: the first output `R(s₀₀ + sext R(s₁₁) · z)` reads
`R(R(s₁₁) · ζ + s₀₀)` and the second output `R(s₀₁)` reads `R(s₀₁)`, both at most `outB`. -/
theorem accTail_spec (hS : S.Ok k) (z : ℕ) (ζ : ℤ) (hz : (BitVec.ofNat (2 * S.w) z).toInt = ζ)
    (hζ : 2 * |ζ| ≤ S.q) (s00 s11 s01 : BitVec (2 * S.w))
    (b00 : |s00.toInt| ≤ (k : ℤ) * ((S.inA : ℤ) * S.inB))
    (b11 : |s11.toInt| ≤ (k : ℤ) * ((S.inA : ℤ) * S.inB))
    (b01 : |s01.toInt| ≤ 2 * ((k : ℤ) * ((S.inA : ℤ) * S.inB))) :
    ((smontAccW S.w S.q S.qinv
          (s00 + sextW (smontAccW S.w S.q S.qinv s11) * BitVec.ofNat (2 * S.w) z)).toInt
        = smont S.w S.q S.qinv (smont S.w S.q S.qinv s11.toInt * ζ + s00.toInt) ∧
      |smont S.w S.q S.qinv (smont S.w S.q S.qinv s11.toInt * ζ + s00.toInt)| ≤ S.outB) ∧
    ((smontAccW S.w S.q S.qinv s01).toInt = smont S.w S.q S.qinv s01.toInt ∧
      |smont S.w S.q S.qinv s01.toInt| ≤ S.outB) := by
  obtain ⟨hN, hq, h3, h4, h5, h6, h7⟩ := hS
  have k3 : 2 * ((k : ℤ) * ((S.inA : ℤ) * S.inB)) + ((2 ^ S.w : ℕ) : ℤ) * S.q
      ≤ 2 * ((2 ^ S.w : ℕ) : ℤ) * S.midB := by exact_mod_cast h3
  have k4 : (2 * (S.midB : ℤ) < ((2 ^ S.w : ℕ) : ℤ)) := by exact_mod_cast h4
  have k5 : 2 * ((k : ℤ) * ((S.inA : ℤ) * S.inB)) + (S.midB : ℤ) * S.q
      + ((2 ^ S.w : ℕ) : ℤ) * S.q ≤ 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB := by exact_mod_cast h5
  have k6 : 2 * (2 * (k : ℤ) * ((S.inA : ℤ) * S.inB)) + ((2 ^ S.w : ℕ) : ℤ) * S.q
      ≤ 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB := by exact_mod_cast h6
  have k7 : (2 * (S.outB : ℤ) < ((2 ^ S.w : ℕ) : ℤ)) := by exact_mod_cast h7
  have hRR := pow_two_mul_cast S.w
  have hR : (0 : ℤ) < (2 ^ S.w : ℕ) := by positivity
  have hRq : (0 : ℤ) ≤ ((2 ^ S.w : ℕ) : ℤ) * S.q := by positivity
  have hm0 : (0 : ℤ) ≤ S.midB := Int.natCast_nonneg _
  have hMq : (0 : ℤ) ≤ (S.midB : ℤ) * S.q := by positivity
  have hkP : (0 : ℤ) ≤ (k : ℤ) * ((S.inA : ℤ) * S.inB) := by positivity
  have hfit : 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB < ((2 ^ (2 * S.w) : ℕ) : ℤ) := by
    rw [hRR]; have := mul_lt_mul_of_pos_left k7 hR; linarith only [this]
  refine ⟨?_, smontAccW_spec S.w S.q S.qinv hN hq s01
    (A2 := 2 * (2 * (k : ℤ) * ((S.inA : ℤ) * S.inB))) (M := S.outB)
    (by linarith only [b01]) k6 k7⟩
  obtain ⟨er, hr⟩ := smontAccW_spec S.w S.q S.qinv hN hq s11
    (A2 := 2 * ((k : ℤ) * ((S.inA : ℤ) * S.inB))) (M := S.midB) (by linarith only [b11]) k3 k4
  set r := smont S.w S.q S.qinv s11.toInt with hrdef
  have hrz : 2 * |r * ζ| ≤ (S.midB : ℤ) * S.q := by
    rw [abs_mul]
    have := mul_le_mul hr hζ (by linarith only [abs_nonneg ζ]) hm0
    linarith only [this]
  have et : (sextW (smontAccW S.w S.q S.qinv s11) * BitVec.ofNat (2 * S.w) z).toInt
      = r * ζ := by
    rw [toInt_mul_exact _ _ (by
      rw [sextW_toInt, er, hz]; linarith only [hrz, k5, hkP, hRq, hfit]), sextW_toInt, er, hz]
  have eu : (s00 + sextW (smontAccW S.w S.q S.qinv s11) * BitVec.ofNat (2 * S.w) z).toInt
      = r * ζ + s00.toInt := by
    rw [toInt_add_exact _ _ (by
      rw [et]; have := abs_add_le s00.toInt (r * ζ)
      linarith only [this, hrz, b00, k5, hRq, hfit]), et, add_comm]
  have := smontAccW_spec S.w S.q S.qinv hN hq _
    (A2 := 2 * ((k : ℤ) * ((S.inA : ℤ) * S.inB)) + (S.midB : ℤ) * S.q) (M := S.outB)
    (by rw [eu]; have := abs_add_le (r * ζ) s00.toInt; linarith only [this, hrz, b00])
    (by linarith only [k5]) k7
  rw [eu] at this
  exact this

/-- **The second output.** On first operands at most `inA` and second operands at most
`inB`, `acc1W` is the reduction of `∑_j a₀ⱼ b₁ⱼ + ∑_j a₁ⱼ b₀ⱼ`, at most `outB`. -/
theorem acc1W_spec (hS : S.Ok k) (a0 a1 b0 b1 : ℕ → BitVec S.w)
    (ha0 : ∀ j, j < k → |(a0 j).toInt| ≤ S.inA) (ha1 : ∀ j, j < k → |(a1 j).toInt| ≤ S.inA)
    (hb0 : ∀ j, j < k → |(b0 j).toInt| ≤ S.inB) (hb1 : ∀ j, j < k → |(b1 j).toInt| ≤ S.inB) :
    (acc1W S.w S.q S.qinv k a0 a1 b0 b1).toInt
        = smont S.w S.q S.qinv (∑ j ∈ range k, (a0 j).toInt * (b1 j).toInt
            + ∑ j ∈ range k, (a1 j).toInt * (b0 j).toInt) ∧
      |smont S.w S.q S.qinv (∑ j ∈ range k, (a0 j).toInt * (b1 j).toInt
            + ∑ j ∈ range k, (a1 j).toInt * (b0 j).toInt)| ≤ S.outB := by
  have hf : 2 * (2 * ((k : ℤ) * ((S.inA : ℤ) * S.inB))) < ((2 ^ (2 * S.w) : ℕ) : ℤ) := by
    exact_mod_cast accSched_ok_fit hS
  have s1 := abs_sum_mul_le S.inA S.inB k (fun j => (a0 j).toInt) (fun j => (b1 j).toInt)
    ha0 hb1
  have s2 := abs_sum_mul_le S.inA S.inB k (fun j => (a1 j).toInt) (fun j => (b0 j).toInt)
    ha1 hb0
  have e1 := macW_toInt S.w S.inA S.inB k a0 b1 0 ha0 hb1
    (by rw [toInt_zero_lit, abs_zero, zero_add]; linarith only [hf, s1])
  rw [toInt_zero_lit, zero_add] at e1
  have e2 := macW_toInt S.w S.inA S.inB k a1 b0 _ ha1 hb0 (by rw [e1]; linarith only [s1, hf])
  rw [e1] at e2
  have := (accTail_spec S k hS 0 _ rfl (by simp) 0 0 _ (by simp; positivity) (by simp; positivity)
    (by rw [e2]; have := abs_add_le (∑ j ∈ range k, (a0 j).toInt * (b1 j).toInt)
          (∑ j ∈ range k, (a1 j).toInt * (b0 j).toInt); linarith only [this, s1, s2])).2
  rw [e2] at this
  exact this

/-- **The first output.** On first operands at most `inA`, second operands at most `inB`
and a twiddle constant reading `ζ` with `2 |ζ| ≤ q`, `acc0W` is
`R(R(∑_j a₁ⱼ b₁ⱼ) · ζ + ∑_j a₀ⱼ b₀ⱼ)`, at most `outB`. -/
theorem acc0W_spec (hS : S.Ok k) (z : ℕ) (ζ : ℤ) (hz : (BitVec.ofNat (2 * S.w) z).toInt = ζ)
    (hζ : 2 * |ζ| ≤ S.q) (a0 a1 b0 b1 : ℕ → BitVec S.w)
    (ha0 : ∀ j, j < k → |(a0 j).toInt| ≤ S.inA) (ha1 : ∀ j, j < k → |(a1 j).toInt| ≤ S.inA)
    (hb0 : ∀ j, j < k → |(b0 j).toInt| ≤ S.inB) (hb1 : ∀ j, j < k → |(b1 j).toInt| ≤ S.inB) :
    (acc0W S.w S.q S.qinv z k a0 a1 b0 b1).toInt
        = smont S.w S.q S.qinv (smont S.w S.q S.qinv
            (∑ j ∈ range k, (a1 j).toInt * (b1 j).toInt) * ζ
            + ∑ j ∈ range k, (a0 j).toInt * (b0 j).toInt) ∧
      |smont S.w S.q S.qinv (smont S.w S.q S.qinv
            (∑ j ∈ range k, (a1 j).toInt * (b1 j).toInt) * ζ
            + ∑ j ∈ range k, (a0 j).toInt * (b0 j).toInt)| ≤ S.outB := by
  have hf : 2 * (2 * ((k : ℤ) * ((S.inA : ℤ) * S.inB))) < ((2 ^ (2 * S.w) : ℕ) : ℤ) := by
    exact_mod_cast accSched_ok_fit hS
  have s0 := abs_sum_mul_le S.inA S.inB k (fun j => (a0 j).toInt) (fun j => (b0 j).toInt)
    ha0 hb0
  have s1 := abs_sum_mul_le S.inA S.inB k (fun j => (a1 j).toInt) (fun j => (b1 j).toInt)
    ha1 hb1
  have e0 := macW_toInt S.w S.inA S.inB k a0 b0 0 ha0 hb0
    (by rw [toInt_zero_lit, abs_zero, zero_add]; linarith only [hf, s0])
  have e1 := macW_toInt S.w S.inA S.inB k a1 b1 0 ha1 hb1
    (by rw [toInt_zero_lit, abs_zero, zero_add]; linarith only [hf, s1])
  rw [toInt_zero_lit, zero_add] at e0 e1
  have := (accTail_spec S k hS z ζ hz hζ (macW S.w k a0 b0 0) (macW S.w k a1 b1 0) 0
    (by rw [e0]; exact s0) (by rw [e1]; exact s1) (by simp; positivity)).1
  rw [e0, e1, BitVec.add_comm, ← macW_add] at this
  exact this

end Spec

/-! ## 6. The lowering on lanes -/

/-- Output lane `i` of the row accumulation on `n` input lanes, operand `j` of the first
row at lanes `j · N, …, j · N + N − 1` and operand `j` of the second row at lanes
`k · N + j · N, …`: the first output of pair `i / 2` for even `i`, the second for odd
`i`. -/
def accLane (S : AccSched) (k psi L N : ℕ) :
    (n : ℕ) → ℕ → Com jasminDialect (Ctxs S.w n) (Rw S.w)
  | 0, _ => .var (constE S.w 0) (.ret .here)
  | n + 1, i =>
    if i % 2 = 0 then
      acc0K S.w S.q S.qinv (cEnc S.w (zetaM S.w S.q psi L (i / 2))) k
        (fun j => laneVarG (Rw S.w) n (j * N + i))
        (fun j => laneVarG (Rw S.w) n (j * N + (i + 1)))
        (fun j => laneVarG (Rw S.w) n (k * N + j * N + i))
        (fun j => laneVarG (Rw S.w) n (k * N + j * N + (i + 1)))
    else
      acc1K S.w S.q S.qinv k
        (fun j => laneVarG (Rw S.w) n (j * N + (i - 1)))
        (fun j => laneVarG (Rw S.w) n (j * N + i))
        (fun j => laneVarG (Rw S.w) n (k * N + j * N + (i - 1)))
        (fun j => laneVarG (Rw S.w) n (k * N + j * N + i))

/-- The row accumulation at block length `2` on `2 · k · 2 ^ logN` input lanes. -/
def accProgW (S : AccSched) (k psi logN : ℕ) :
    MultiReturnCom jasminDialect (Ctxs S.w (2 * k * 2 ^ logN)) (Ctxs S.w (2 ^ logN)) :=
  laneMapW (2 ^ logN) (accLane S k psi (logN - 1) (2 ^ logN) (2 * k * 2 ^ logN))

theorem idx_lt {j k t N : ℕ} (hj : j < k) (ht : t < N) : j * N + t < k * N := by
  have := Nat.mul_le_mul_right N (show j + 1 ≤ k by omega)
  rw [Nat.add_mul, one_mul] at this
  omega

/-- **The row accumulation on words.** On first-operand words at most `inA` and
second-operand words at most `inB` in absolute value, every output word of `accProgW` is
at most `outB` in absolute value and, times `2 ^ w`, is the sum over the row of
`blockMul 2` at the block roots of `ψ`, modulo `q`. -/
theorem accProgW_denote (S : AccSched) (k : ℕ) (hS : S.Ok k) (psi logN : ℕ)
    (hlog : 0 < logN) (hk : 0 < k) (g : ℕ → BitVec S.w)
    (hA : ∀ j t, j < k → t < 2 ^ logN → |(g (j * 2 ^ logN + t)).toInt| ≤ S.inA)
    (hB : ∀ j t, j < k → t < 2 ^ logN →
      |(g (k * 2 ^ logN + j * 2 ^ logN + t)).toInt| ≤ S.inB)
    (i : ℕ) (hi : i < 2 ^ logN) :
    |(hvGetG (Rw S.w) (0 : BitVec S.w) ((accProgW S k psi logN).denote
        (lanesVal (Rw S.w) g (2 * k * 2 ^ logN) 0)) i).toInt| ≤ S.outB ∧
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((accProgW S k psi logN).denote
        (lanesVal (Rw S.w) g (2 * k * 2 ^ logN) 0)) i).toInt : ℤ) : ZMod S.q)
        * ((2 ^ S.w : ℕ) : ZMod S.q)
      = ∑ j ∈ range k, blockMul 2 (blockRoot (psi : ZMod S.q) (logN - 1))
          (fun t => ((g (j * 2 ^ logN + t)).toInt : ZMod S.q))
          (fun t => ((g (k * 2 ^ logN + j * 2 ^ logN + t)).toInt : ZMod S.q)) i := by
  rw [accProgW, laneMapW_denote, hvGetG_denoteN _ _ _ _ _ _ hi]
  simp only [blockMul_two]
  have hN2 : 2 ^ logN = 2 * 2 ^ (logN - 1) := by
    rw [← pow_succ']; congr 1; omega
  generalize 2 ^ logN = N at *
  have hq := hS.2.1
  have hqpos : 0 < S.q := by
    obtain ⟨hN, -⟩ := hS
    rcases Nat.eq_zero_or_pos S.q with h | h
    · rw [h, zero_mul, Nat.zero_mod] at hN; exact absurd hN (by norm_num)
    · exact h
  have hkN : k * N ≤ 2 * k * N := by
    rw [Nat.mul_assoc 2]; omega
  obtain ⟨n, hn⟩ : ∃ n, 2 * k * N = n + 1 := ⟨2 * k * N - 1, by
    have := Nat.mul_le_mul_right N (show 1 ≤ k by omega)
    rw [one_mul] at this; omega⟩
  have hiA : ∀ j t, j < k → t < N → j * N + t ≤ n := fun j t hj ht => by
    have := idx_lt hj ht; omega
  have hiB : ∀ j t, j < k → t < N → k * N + j * N + t ≤ n := fun j t hj ht => by
    have := idx_lt hj ht
    have h2 : 2 * k * N = k * N + k * N := by rw [Nat.mul_assoc, two_mul]
    omega
  revert hA hB
  rw [hn]
  intro hA hB
  have hlk : ∀ j, j ≤ n → (laneVarG (Rw S.w) n j).lookup (lanesVal (Rw S.w) g (n + 1) 0)
      = g j := fun j hj => by
    rw [laneVarG_lookup (Rw S.w) g n j 0 hj, Nat.zero_add]
  rw [accLane]
  split
  · next he =>
    have hi1 : i + 1 < N := by omega
    rw [acc0K_denote]
    obtain ⟨e, hb⟩ := acc0W_spec S k hS _ _ (cEnc_toInt S.w S.q _
        (zetaM_abs S.w S.q psi (logN - 1) (i / 2) hqpos) hq)
      (zetaM_abs S.w S.q psi (logN - 1) (i / 2) hqpos)
      (fun j => (laneVarG (Rw S.w) n (j * N + i)).lookup (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j => (laneVarG (Rw S.w) n (j * N + (i + 1))).lookup (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j => (laneVarG (Rw S.w) n (k * N + j * N + i)).lookup
        (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j => (laneVarG (Rw S.w) n (k * N + j * N + (i + 1))).lookup
        (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j hj => by rw [hlk _ (hiA j i hj hi)]; exact hA j i hj hi)
      (fun j hj => by rw [hlk _ (hiA j (i + 1) hj hi1)]; exact hA j (i + 1) hj hi1)
      (fun j hj => by rw [hlk _ (hiB j i hj hi)]; exact hB j i hj hi)
      (fun j hj => by rw [hlk _ (hiB j (i + 1) hj hi1)]; exact hB j (i + 1) hj hi1)
    have s00 : ∑ j ∈ range k, ((laneVarG (Rw S.w) n (j * N + i)).lookup
          (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
          * ((laneVarG (Rw S.w) n (k * N + j * N + i)).lookup
            (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
        = ∑ j ∈ range k, (g (j * N + i)).toInt * (g (k * N + j * N + i)).toInt :=
      Finset.sum_congr rfl fun j hj => by
        have hj' := Finset.mem_range.1 hj
        rw [hlk _ (hiA j i hj' hi), hlk _ (hiB j i hj' hi)]
    have s11 : ∑ j ∈ range k, ((laneVarG (Rw S.w) n (j * N + (i + 1))).lookup
          (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
          * ((laneVarG (Rw S.w) n (k * N + j * N + (i + 1))).lookup
            (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
        = ∑ j ∈ range k, (g (j * N + (i + 1))).toInt
            * (g (k * N + j * N + (i + 1))).toInt :=
      Finset.sum_congr rfl fun j hj => by
        have hj' := Finset.mem_range.1 hj
        rw [hlk _ (hiA j (i + 1) hj' hi1), hlk _ (hiB j (i + 1) hj' hi1)]
    rw [s00, s11] at e hb
    rw [e]
    refine ⟨hb, ?_⟩
    have hr := smont_mul_radix S.w S.q S.qinv hS.1
      (∑ j ∈ range k, (g (j * N + (i + 1))).toInt * (g (k * N + j * N + (i + 1))).toInt)
    rw [smont_mul_radix S.w S.q S.qinv hS.1]
    push_cast at hr ⊢
    rw [zetaM_cast, Finset.sum_add_distrib, ← Finset.sum_mul]
    linear_combination (blockRoot (psi : ZMod S.q) (logN - 1) (i / 2)) * hr
  · next ho =>
    have hi1 : 1 ≤ i := by omega
    have hi0 : i - 1 < N := by omega
    rw [acc1K_denote]
    obtain ⟨e, hb⟩ := acc1W_spec S k hS
      (fun j => (laneVarG (Rw S.w) n (j * N + (i - 1))).lookup (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j => (laneVarG (Rw S.w) n (j * N + i)).lookup (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j => (laneVarG (Rw S.w) n (k * N + j * N + (i - 1))).lookup
        (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j => (laneVarG (Rw S.w) n (k * N + j * N + i)).lookup
        (lanesVal (Rw S.w) g (n + 1) 0))
      (fun j hj => by rw [hlk _ (hiA j (i - 1) hj hi0)]; exact hA j (i - 1) hj hi0)
      (fun j hj => by rw [hlk _ (hiA j i hj hi)]; exact hA j i hj hi)
      (fun j hj => by rw [hlk _ (hiB j (i - 1) hj hi0)]; exact hB j (i - 1) hj hi0)
      (fun j hj => by rw [hlk _ (hiB j i hj hi)]; exact hB j i hj hi)
    have s01 : ∑ j ∈ range k, ((laneVarG (Rw S.w) n (j * N + (i - 1))).lookup
          (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
          * ((laneVarG (Rw S.w) n (k * N + j * N + i)).lookup
            (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
        = ∑ j ∈ range k, (g (j * N + (i - 1))).toInt * (g (k * N + j * N + i)).toInt :=
      Finset.sum_congr rfl fun j hj => by
        have hj' := Finset.mem_range.1 hj
        rw [hlk _ (hiA j (i - 1) hj' hi0), hlk _ (hiB j i hj' hi)]
    have s10 : ∑ j ∈ range k, ((laneVarG (Rw S.w) n (j * N + i)).lookup
          (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
          * ((laneVarG (Rw S.w) n (k * N + j * N + (i - 1))).lookup
            (lanesVal (Rw S.w) g (n + 1) 0) : BitVec S.w).toInt
        = ∑ j ∈ range k, (g (j * N + i)).toInt * (g (k * N + j * N + (i - 1))).toInt :=
      Finset.sum_congr rfl fun j hj => by
        have hj' := Finset.mem_range.1 hj
        rw [hlk _ (hiA j i hj' hi), hlk _ (hiB j (i - 1) hj' hi0)]
    rw [s01, s10] at e hb
    rw [e]
    refine ⟨hb, ?_⟩
    rw [smont_mul_radix S.w S.q S.qinv hS.1]
    push_cast
    rw [Finset.sum_add_distrib]

/-! ## 7. The ring-level statement -/

/-- `basemulF` at `L = logN − 1` of residues read from lane functions is `blockMul 2` of
those lane functions. -/
theorem basemulF_eq_blockMul_two (q psi logN : ℕ) (hlog : 0 < logN)
    (x y : Limbs [q] (2 ^ logN)) (a b : ℕ → ZMod q)
    (hx : ∀ t (ht : t < 2 ^ logN), x ⟨0, by simp⟩ ⟨t, ht⟩ = a t)
    (hy : ∀ t (ht : t < 2 ^ logN), y ⟨0, by simp⟩ ⟨t, ht⟩ = b t)
    (i : ℕ) (hi : i < 2 ^ logN) :
    basemulF logN (logN - 1) [psi] x y ⟨0, by simp⟩ ⟨i, hi⟩
      = blockMul 2 (blockRoot (psi : ZMod q) (logN - 1)) a b i := by
  have hB : 2 ^ (logN - (logN - 1)) = 2 := by
    rw [show logN - (logN - 1) = 1 by omega, pow_one]
  have hK : 2 ^ logN = 2 ^ (logN - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  unfold basemulF
  simp only [List.getD_cons_zero]
  rw [hB]
  refine blockMul_congr 2 (2 ^ (logN - 1)) (by norm_num) _ _ _ _ _ ?_ ?_ i (by omega)
  · intro j hj
    simp only [rowLanes, dif_pos (show j < 2 ^ logN by omega)]
    exact hx j (by omega)
  · intro j hj
    simp only [rowLanes, dif_pos (show j < 2 ^ logN by omega)]
    exact hy j (by omega)

/-- **The row accumulation against the ring-level spec.** When the residues `x j`, `y j`
of one modulus are the readings of operand `j` of the first and second row, every output
word of `accProgW`, times `2 ^ w`, is `∑_{j < k} basemulF (x j) (y j)` at
`L = logN − 1`. -/
theorem accProgW_basemulF (S : AccSched) (k : ℕ) (hS : S.Ok k) (psi logN : ℕ)
    (hlog : 0 < logN) (hk : 0 < k) (g : ℕ → BitVec S.w)
    (hA : ∀ j t, j < k → t < 2 ^ logN → |(g (j * 2 ^ logN + t)).toInt| ≤ S.inA)
    (hB : ∀ j t, j < k → t < 2 ^ logN →
      |(g (k * 2 ^ logN + j * 2 ^ logN + t)).toInt| ≤ S.inB)
    (x y : ℕ → Limbs [S.q] (2 ^ logN))
    (hx : ∀ j t (ht : t < 2 ^ logN), j < k →
      x j ⟨0, by simp⟩ ⟨t, ht⟩ = ((g (j * 2 ^ logN + t)).toInt : ZMod S.q))
    (hy : ∀ j t (ht : t < 2 ^ logN), j < k →
      y j ⟨0, by simp⟩ ⟨t, ht⟩ = ((g (k * 2 ^ logN + j * 2 ^ logN + t)).toInt : ZMod S.q))
    (i : ℕ) (hi : i < 2 ^ logN) :
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((accProgW S k psi logN).denote
        (lanesVal (Rw S.w) g (2 * k * 2 ^ logN) 0)) i).toInt : ℤ) : ZMod S.q)
        * ((2 ^ S.w : ℕ) : ZMod S.q)
      = ∑ j ∈ range k, basemulF logN (logN - 1) [psi] (x j) (y j) ⟨0, by simp⟩ ⟨i, hi⟩ := by
  rw [(accProgW_denote S k hS psi logN hlog hk g hA hB i hi).2]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  exact (basemulF_eq_blockMul_two S.q psi logN hlog (x j) (y j) _ _
    (fun t ht => hx j t ht hj') (fun t ht => hy j t ht hj') i hi).symm

/-! ## 8. Instances -/

/-- ML-KEM at `k = 2`: `q = 3329` in signed 16-bit words, `qinv = 62209`, first operands
(the matrix, sampled below `q`) at most `q − 1`, second operands below `8 q` (the output
bound of `nttProgSW mlkemNtt mlkemSigned`). -/
def mlkemAcc2 : AccSched := ⟨16, 3329, 62209, 3328, 26632, 4370, 7075⟩

/-- ML-KEM at `k = 3`, with the operand bounds of `mlkemAcc2`. -/
def mlkemAcc3 : AccSched := ⟨16, 3329, 62209, 3328, 26632, 5722, 9779⟩

/-- ML-KEM at `k = 4`, with the operand bounds of `mlkemAcc2`. -/
def mlkemAcc4 : AccSched := ⟨16, 3329, 62209, 3328, 26632, 7075, 12484⟩

theorem mlkemAcc2_ok : mlkemAcc2.Ok 2 := by decide +kernel

theorem mlkemAcc3_ok : mlkemAcc3.Ok 3 := by decide +kernel

theorem mlkemAcc4_ok : mlkemAcc4.Ok 4 := by decide +kernel

/-- The ML-KEM-768 row accumulation on words at `ψ = 17`, `N = 256`, `L = 7`, `k = 3`. -/
theorem mlkemAcc3_basemulF (g : ℕ → BitVec 16)
    (hA : ∀ j t, j < 3 → t < 256 → |(g (j * 256 + t)).toInt| ≤ 3328)
    (hB : ∀ j t, j < 3 → t < 256 → |(g (3 * 256 + j * 256 + t)).toInt| ≤ 26632)
    (x y : ℕ → Limbs [3329] 256)
    (hx : ∀ j t (ht : t < 256), j < 3 →
      x j ⟨0, by simp⟩ ⟨t, ht⟩ = ((g (j * 256 + t)).toInt : ZMod 3329))
    (hy : ∀ j t (ht : t < 256), j < 3 →
      y j ⟨0, by simp⟩ ⟨t, ht⟩ = ((g (3 * 256 + j * 256 + t)).toInt : ZMod 3329))
    (i : ℕ) (hi : i < 256) :
    |(hvGetG (Rw 16) (0 : BitVec 16) ((accProgW mlkemAcc3 3 17 8).denote
        (lanesVal (Rw 16) g 1536 0)) i).toInt| ≤ 9779 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((accProgW mlkemAcc3 3 17 8).denote
        (lanesVal (Rw 16) g 1536 0)) i).toInt : ℤ) : ZMod 3329) * ((2 ^ 16 : ℕ) : ZMod 3329)
      = ∑ j ∈ range 3, basemulF 8 7 [17] (x j) (y j) ⟨0, by simp⟩ ⟨i, hi⟩ :=
  ⟨(accProgW_denote mlkemAcc3 3 mlkemAcc3_ok 17 8 (by norm_num) (by norm_num) g hA hB i hi).1,
    accProgW_basemulF mlkemAcc3 3 mlkemAcc3_ok 17 8 (by norm_num) (by norm_num) g hA hB x y
      hx hy i hi⟩

end CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc
