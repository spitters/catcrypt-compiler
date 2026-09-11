/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Montgomery REDC law for a 60-bit FHE NTT modmul

This is the load-bearing correctness law for the FHE-sized NTT modular multiply.
It mirrors the structure of `Plonky3BarrettLaw.lean`: an estimate is bounded into
`[0, 2q)`, then a single conditional subtract canonicalises it into `[0, q)`.

We model the emittable single-word **Montgomery REDC** at the 60-bit prime
`q = 1152921504606830593 = 2^60 − 2^14 + 1` with radix `R = 2^64`:
```
  m := (T % R) * qinv % R        -- low word × qinv, keep low word
  u := (T + m·q) / R             -- exact division by R
  montRedc T := if u ≥ q then u − q else u
```
where `qinv = −q^{-1} mod 2^64` so `q·qinv ≡ −1 mod R`.

All reasoning is over `Nat` (the cleanest layer). The headline result is
`normalMul_correct : normalMul a b = (a * b) % q` for `a, b < q`, the function a
GMP KAT checks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FheMontMulLaw

/-- The 60-bit FHE prime `q = 2^60 − 2^14 + 1`. -/
def fheQ : Nat := 1152921504606830593

/-- The Montgomery radix `R = 2^64`. -/
def fheR : Nat := 18446744073709551616

/-- `−q^{-1} mod 2^64`. -/
def fheQinv : Nat := 1080859512253956095

/-- `R^2 mod q`, the constant used to convert into Montgomery form. -/
def fheR2 : Nat := 68711088384

/-! ### Constant-verification lemmas (all `by decide`/`by norm_num`, no `native_decide`) -/

theorem fheR_eq : fheR = 2 ^ 64 := by norm_num [fheR]

/-- The defining congruence `q · qinv ≡ −1 (mod R)`, i.e. `q·qinv % R = R − 1`. -/
theorem fheQ_mul_qinv_mod : fheQ * fheQinv % fheR = fheR - 1 := by
  norm_num [fheQ, fheQinv, fheR]

/-- `R^2 ≡ R2 (mod q)`. -/
theorem fheR2_eq : fheR ^ 2 % fheQ = fheR2 := by
  norm_num [fheR, fheQ, fheR2]

theorem fheQ_pos : 0 < fheQ := by norm_num [fheQ]

theorem fheR_pos : 0 < fheR := by norm_num [fheR]

/-! ### Montgomery REDC -/

/-- **The emitted Montgomery REDC word sequence** for `T < q·R`.
    `m = (T % R)·qinv % R`; `u = (T + m·q) / R` (exact, since `T + m·q ≡ 0 mod R`);
    one conditional subtract canonicalises `u ∈ [0, 2q)` into `[0, q)`. -/
def montRedc (T : Nat) : Nat :=
  let m := (T % fheR) * fheQinv % fheR
  let u := (T + m * fheQ) / fheR
  if u ≥ fheQ then u - fheQ else u

/-- **Montgomery exact-division property.** `(T + m·q) % R = 0`, so the division
    by `R` in `montRedc` is exact. This is the heart of Montgomery reduction:
    `m·q ≡ (T%R)·qinv·q ≡ (T%R)·(−1) ≡ −T (mod R)`, hence `T + m·q ≡ 0`. -/
theorem montRedc_exact_div (T : Nat) :
    (T + ((T % fheR) * fheQinv % fheR) * fheQ) % fheR = 0 := by
  -- `m·q ≡ (T%R)·(qinv·q) ≡ (T%R)·(R−1) (mod R)`, all via `Nat.ModEq` (no
  -- rewrite-looping on the big literals).
  have hmq : (((T % fheR) * fheQinv % fheR) * fheQ) ≡ ((T % fheR) * (fheR - 1)) [MOD fheR] := by
    have h1 : ((T % fheR) * fheQinv % fheR) ≡ (T % fheR) * fheQinv [MOD fheR] :=
      Nat.mod_modEq _ _
    have h2 : ((T % fheR) * fheQinv % fheR) * fheQ ≡ ((T % fheR) * fheQinv) * fheQ [MOD fheR] :=
      h1.mul_right _
    have h3 : ((T % fheR) * fheQinv) * fheQ = (T % fheR) * (fheQinv * fheQ) := by ring
    rw [h3] at h2
    -- `qinv·q ≡ R − 1 (mod R)` (from `q·qinv % R = R − 1`)
    have h4 : (fheQinv * fheQ) ≡ (fheR - 1) [MOD fheR] := by
      unfold Nat.ModEq
      rw [Nat.mul_comm, fheQ_mul_qinv_mod, Nat.mod_eq_of_lt (by have := fheR_pos; omega)]
    exact h2.trans (h4.mul_left _)
  -- Hence `T + m·q ≡ T + (T%R)·(R−1) (mod R)`, and the RHS is `(T/R + T%R)·R ≡ 0`.
  have hsum : (T + ((T % fheR) * fheQinv % fheR) * fheQ)
      ≡ (T + (T % fheR) * (fheR - 1)) [MOD fheR] := (Nat.ModEq.refl T).add hmq
  rw [Nat.ModEq] at hsum
  rw [hsum]
  -- `T + (T%R)·(R−1) = (T/R + T%R)·R`, so `% R = 0`.
  have hR1 : (fheR - 1) + 1 = fheR := by have := fheR_pos; omega
  have hd : fheR * (T / fheR) + T % fheR = T := Nat.div_add_mod T fheR
  have key : T + (T % fheR) * (fheR - 1) = (T / fheR + T % fheR) * fheR := by
    calc T + (T % fheR) * (fheR - 1)
        = (fheR * (T / fheR) + T % fheR) + (T % fheR) * (fheR - 1) := by rw [hd]
      _ = fheR * (T / fheR) + (T % fheR) * ((fheR - 1) + 1) := by ring
      _ = fheR * (T / fheR) + (T % fheR) * fheR := by rw [hR1]
      _ = (T / fheR + T % fheR) * fheR := by ring
  rw [key, Nat.mul_mod_left]

/-- The Montgomery quotient `u = (T + m·q)/R`, named for reuse. -/
def montU (T : Nat) : Nat := (T + ((T % fheR) * fheQinv % fheR) * fheQ) / fheR

theorem montRedc_eq (T : Nat) :
    montRedc T = if montU T ≥ fheQ then montU T - fheQ else montU T := rfl

/-- **Exact division:** `u·R = T + m·q` (since `R ∣ T + m·q`). -/
theorem montU_mul_R (T : Nat) :
    montU T * fheR = T + ((T % fheR) * fheQinv % fheR) * fheQ :=
  Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (montRedc_exact_div T))

/-- **`montU` bound:** `u < 2q` for `T < q·R`, so one conditional subtract
    canonicalises. Standard Montgomery bound: `u·R = T + m·q < q·R + R·q = 2q·R`
    since `m < R`, `T < q·R`. -/
theorem montU_bound (T : Nat) (hT : T < fheQ * fheR) : montU T < 2 * fheQ := by
  have hu := montU_mul_R T
  set m := (T % fheR) * fheQinv % fheR with hmdef
  have hmlt : m < fheR := Nat.mod_lt _ fheR_pos
  -- m·q < q·R
  have hmq : m * fheQ < fheQ * fheR := by
    have h : m * fheQ < fheR * fheQ := mul_lt_mul_of_pos_right hmlt fheQ_pos
    rwa [Nat.mul_comm fheR fheQ] at h
  -- T + m·q < 2q·R
  have hub : montU T * fheR < 2 * fheQ * fheR := by
    rw [hu]
    have he : 2 * fheQ * fheR = fheQ * fheR + fheQ * fheR := by ring
    omega
  -- cancel R on the right
  have h2 : montU T * fheR < (2 * fheQ) * fheR := by rw [Nat.mul_assoc] at hub ⊢; omega
  exact Nat.lt_of_mul_lt_mul_right h2

/-- **`montRedc` is canonical:** `montRedc T < q` for `T < q·R`. -/
theorem montRedc_lt (T : Nat) (hT : T < fheQ * fheR) : montRedc T < fheQ := by
  have hb := montU_bound T hT
  rw [montRedc_eq]
  split
  · rename_i h; omega
  · rename_i h; omega

/-- **`montRedc` preserves the residue mod q:** `montRedc T ≡ u (mod q)`, since the
    conditional subtract changes `u` by a multiple of `q`. -/
theorem montRedc_modEq_u (T : Nat) : montRedc T % fheQ = montU T % fheQ := by
  rw [montRedc_eq]
  split
  · rename_i h
    conv_rhs => rw [show montU T = (montU T - fheQ) + fheQ by omega]
    rw [Nat.add_mod_right]
  · rfl

/-- **Montgomery correctness (multiplicative form).** `montRedc T · R ≡ T (mod q)`,
    i.e. `montRedc T ≡ T·R^{-1} (mod q)`. From `u·R = T + m·q ≡ T (mod q)` and the
    csub preserving the residue mod `q`. (Avoids naming `R^{-1}` explicitly.) -/
theorem montRedc_correct (T : Nat) : (montRedc T * fheR) % fheQ = T % fheQ := by
  -- u·R ≡ T (mod q)
  have huR : (montU T * fheR) % fheQ = T % fheQ := by
    rw [montU_mul_R, Nat.add_mul_mod_self_right]
  -- montRedc T ≡ u (mod q) ⇒ montRedc T · R ≡ u · R ≡ T (mod q)
  calc (montRedc T * fheR) % fheQ
      = ((montRedc T % fheQ) * fheR) % fheQ :=
        Nat.ModEq.mul_right fheR (Nat.mod_modEq (montRedc T) fheQ).symm
    _ = ((montU T % fheQ) * fheR) % fheQ := by rw [montRedc_modEq_u]
    _ = (montU T * fheR) % fheQ :=
        Nat.ModEq.mul_right fheR (Nat.mod_modEq (montU T) fheQ)
    _ = T % fheQ := huR

/-! ### Montgomery multiply and the normal-domain round trip -/

/-- Montgomery multiply: `montMul a b = REDC(a·b)`, computing `a·b·R^{-1} mod q`. -/
def montMul (a b : Nat) : Nat := montRedc (a * b)

/-- **`montMul` spec:** for `a, b < q`, `montMul a b ≡ a·b·R^{-1} (mod q)`
    (multiplicative form `montMul a b · R ≡ a·b (mod q)`) and `montMul a b < q`. -/
theorem montMul_spec (a b : Nat) (ha : a < fheQ) (hb : b < fheQ) :
    (montMul a b * fheR) % fheQ = (a * b) % fheQ ∧ montMul a b < fheQ := by
  have hab : a * b < fheQ * fheR := by
    have h1 : a * b < fheQ * fheQ := Nat.mul_lt_mul'' ha hb
    have h2 : fheQ * fheQ ≤ fheQ * fheR := by
      apply Nat.mul_le_mul_left
      norm_num [fheQ, fheR]
    exact lt_of_lt_of_le h1 h2
  exact ⟨montRedc_correct (a * b), montRedc_lt (a * b) hab⟩

/-- Normal-domain multiply: convert the Montgomery product back out by a second
    REDC against `R2 = R^2 mod q`. -/
def normalMul (a b : Nat) : Nat := montRedc (montMul a b * fheR2)

/-- **Headline correctness (the GMP-KAT target).** For `a, b < q`,
    `normalMul a b = (a · b) % q`.

    Round trip: `montMul a b ≡ a·b·R^{-1} (mod q)`, then
    `montRedc(montMul a b · R2) ≡ (a·b·R^{-1})·R^2·R^{-1} = a·b (mod q)`, and the
    result is `< q`, so the `% q` is exact equality. -/
theorem normalMul_correct (a b : Nat) (ha : a < fheQ) (hb : b < fheQ) :
    normalMul a b = (a * b) % fheQ := by
  obtain ⟨hmm, hmmlt⟩ := montMul_spec a b ha hb
  set y := montMul a b with hy
  -- bound the inner argument `y · R2 < q · R` so REDC applies
  have hyR2 : y * fheR2 < fheQ * fheR := by
    have hR2lt : fheR2 < fheR := by norm_num [fheR2, fheR]
    have h1 : y * fheR2 < fheQ * fheR2 :=
      mul_lt_mul_of_pos_right hmmlt (by norm_num [fheR2])
    have h2 : fheQ * fheR2 ≤ fheQ * fheR := Nat.mul_le_mul (le_refl fheQ) (le_of_lt hR2lt)
    exact lt_of_lt_of_le h1 h2
  -- `normalMul a b = REDC(y·R2) < q`
  have hlt : normalMul a b < fheQ := montRedc_lt (y * fheR2) hyR2
  -- `normalMul a b · R ≡ y · R2 (mod q)`
  have hcorr : (normalMul a b * fheR) % fheQ = (y * fheR2) % fheQ :=
    montRedc_correct (y * fheR2)
  -- Now show `(normalMul a b · R) % q = (a·b) % q`, then cancel `R` (gcd(R,q)=1).
  -- y · R2 ≡ y · R^2 (mod q), and y · R ≡ a·b (mod q) ⇒ y · R^2 ≡ a·b · R (mod q).
  -- Hence normalMul a b · R ≡ a·b·R (mod q) and we strip R.
  -- `fheR2 ≡ fheR·fheR (mod q)` — note `Nat.ModEq` unfolds to this `%`-equality.
  have hR2 : fheR2 ≡ fheR * fheR [MOD fheQ] := by
    have h := fheR2_eq; rw [pow_two] at h
    show fheR2 % fheQ = (fheR * fheR) % fheQ
    rw [h, Nat.mod_eq_of_lt (show fheR2 < fheQ by norm_num [fheR2, fheQ])]
  -- normalMul·R ≡ y·R2 ≡ y·(R·R) = (y·R)·R ≡ (a·b)·R (mod q)
  have chain : (normalMul a b * fheR) % fheQ = ((a * b) * fheR) % fheQ := by
    rw [hcorr]
    calc y * fheR2
        ≡ y * (fheR * fheR) [MOD fheQ] := Nat.ModEq.mul_left y hR2
      _ = (y * fheR) * fheR := by ring
      _ ≡ (a * b) * fheR [MOD fheQ] := Nat.ModEq.mul_right fheR hmm
  -- strip the common factor R (coprime to q): `x·R ≡ y·R (mod q) ⇒ x ≡ y (mod q)`.
  have hcop : fheQ.gcd fheR = 1 := by decide +kernel
  -- `chain : (normalMul·R) % q = ((a·b)·R) % q` is exactly the cancellable hypothesis.
  have hmodeq : normalMul a b % fheQ = (a * b) % fheQ :=
    Nat.ModEq.cancel_right_of_coprime hcop chain
  -- both `normalMul a b` and `(a·b) % q` are `< q`, so the residues are the values.
  have hlt2 : (a * b) % fheQ < fheQ := Nat.mod_lt _ fheQ_pos
  rw [Nat.mod_eq_of_lt hlt] at hmodeq
  exact hmodeq

end CatCrypt.Crypto.SecureCompilation.VIR.FheMontMulLaw
