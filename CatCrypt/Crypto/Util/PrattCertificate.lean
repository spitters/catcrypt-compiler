/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib

/-!
# Pratt/Lucas prime certificates over fast modular exponentiation

A reusable core for proving `Nat.Prime p` for large `p` via the Lucas primality
criterion, using a binary (square-and-multiply) modular exponentiation whose
result is checkable by `decide`/`native_decide` at cryptographic sizes.

The `ZMod p` power `a ^ (p - 1)` is unary `npowRec`, so it is not directly
evaluable for a 256-bit `p`. `powMod` computes `a ^ k % n` in `O(log k)`
multiplications, and `powMod_cast` transports a fast `powMod … = 1` check into
the `a ^ (p - 1) = 1` hypothesis of `lucas_primality`.

## Main definitions

* `powMod a k n` — binary modular exponentiation returning `a ^ k % n`.

## Main results

* `powMod_eq` — `powMod a k n = a ^ k % n` for `0 < n`.
* `powMod_cast` — `((powMod a k n : ℕ) : ZMod n) = (a : ZMod n) ^ k`.
* `lucas_of_certificate` — `Nat.Prime p` from a witness `a`, a list `qs` of the
  prime factors of `p - 1`, and fast `powMod` checks.
-/

set_option autoImplicit false

namespace CatCrypt.PrattCertificate

/-- Binary modular exponentiation with an explicit fuel bounding the number of
squarings. For `k < 2 ^ fuel`, `powModFuel a n fuel k = a ^ k % n`. -/
def powModFuel (a n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % n
  | fuel + 1, k =>
    if k = 0 then 1 % n
    else
      let half := powModFuel a n fuel (k / 2)
      let sq := (half * half) % n
      if k % 2 = 1 then (sq * a) % n else sq

/-- Binary (square-and-multiply) modular exponentiation: `powMod a k n = a ^ k % n`
(for `0 < n`), computed in `O(log k)` multiplications. -/
def powMod (a k n : ℕ) : ℕ := powModFuel a n k k

theorem powModFuel_modEq (a n : ℕ) :
    ∀ (fuel k : ℕ), k < 2 ^ fuel → powModFuel a n fuel k ≡ a ^ k [MOD n] := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk
    simp only [pow_zero] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [powModFuel, pow_zero]
    exact Nat.mod_modEq 1 n
  | succ fuel ih =>
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [powModFuel, pow_zero]
      exact Nat.mod_modEq 1 n
    · have hhalf : k / 2 < 2 ^ fuel := by
        have h2 : (2 : ℕ) ^ (fuel + 1) = 2 ^ fuel * 2 := pow_succ 2 fuel
        omega
      have ihh := ih (k / 2) hhalf
      simp only [powModFuel, if_neg hk0]
      by_cases hpar : k % 2 = 1
      · simp only [if_pos hpar]
        set h := powModFuel a n fuel (k / 2) with hdef
        have hpow : a ^ (k / 2) * a ^ (k / 2) * a = a ^ k := by
          rw [← pow_add, ← pow_succ]; congr 1; omega
        refine (Nat.mod_modEq _ _).trans ?_
        exact hpow ▸ (Nat.ModEq.mul_right a ((Nat.mod_modEq _ _).trans (ihh.mul ihh)))
      · simp only [if_neg hpar]
        set h := powModFuel a n fuel (k / 2) with hdef
        have hpow : a ^ (k / 2) * a ^ (k / 2) = a ^ k := by
          rw [← pow_add]; congr 1; omega
        exact (Nat.mod_modEq _ _).trans (hpow ▸ (ihh.mul ihh))

theorem powModFuel_lt (a n : ℕ) (hn : 0 < n) :
    ∀ (fuel k : ℕ), powModFuel a n fuel k < n := by
  intro fuel
  induction fuel with
  | zero => intro k; exact Nat.mod_lt 1 hn
  | succ fuel ih =>
    intro k
    simp only [powModFuel]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]; exact Nat.mod_lt 1 hn
    · simp only [if_neg hk0]
      by_cases hpar : k % 2 = 1
      · simp only [if_pos hpar]; exact Nat.mod_lt _ hn
      · simp only [if_neg hpar]; exact Nat.mod_lt _ hn

/-- Correctness of binary modular exponentiation. -/
theorem powMod_eq (a k n : ℕ) (hn : 0 < n) : powMod a k n = a ^ k % n := by
  have hlt : powModFuel a n k k < n := powModFuel_lt a n hn k k
  have hmod : powModFuel a n k k ≡ a ^ k [MOD n] :=
    powModFuel_modEq a n k k (Nat.lt_two_pow_self)
  calc powMod a k n = powModFuel a n k k := rfl
    _ = powModFuel a n k k % n := (Nat.mod_eq_of_lt hlt).symm
    _ = a ^ k % n := hmod

/-- The fast `powMod` result cast into `ZMod n` equals the abstract power there,
so a `powMod … = 1` check discharges an `a ^ k = 1` hypothesis over `ZMod n`. -/
theorem powMod_cast (a k n : ℕ) [NeZero n] :
    ((powMod a k n : ℕ) : ZMod n) = (a : ZMod n) ^ k := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [powMod_eq a k n hn,
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq (a ^ k) n), Nat.cast_pow]

/-- A prime dividing the product of a list of primes is a member of the list. -/
theorem prime_mem_of_dvd_listProd {q : ℕ} (hq : q.Prime) :
    ∀ (l : List ℕ), (∀ r ∈ l, Nat.Prime r) → q ∣ l.prod → q ∈ l := by
  intro l
  induction l with
  | nil =>
    intro _ hd
    simp only [List.prod_nil, Nat.dvd_one] at hd
    exact absurd hd hq.ne_one
  | cons r t ih =>
    intro hl hd
    rw [List.prod_cons] at hd
    rcases (hq.dvd_mul).1 hd with h | h
    · exact List.mem_cons.mpr
        (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (hl r (List.mem_cons.mpr (Or.inl rfl)))).1 h))
    · exact List.mem_cons.mpr
        (Or.inr (ih (fun s hs => hl s (List.mem_cons.mpr (Or.inr hs))) h))

/-- Lucas primality via a certificate. Given a witness `a`, a list `qs` of the
prime factors of `p - 1` whose product is `p - 1`, the Fermat check
`powMod a (p - 1) p = 1`, and for each factor `q` the check
`powMod a ((p - 1) / q) p ≠ 1`, conclude `Nat.Prime p`. -/
theorem lucas_of_certificate (p : ℕ) (hp1 : 1 < p) (a : ℕ) (qs : List ℕ)
    (hprod : qs.prod = p - 1)
    (hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (hfermat : powMod a (p - 1) p = 1)
    (hwit : ∀ q ∈ qs, powMod a ((p - 1) / q) p ≠ 1) :
    Nat.Prime p := by
  have hp0 : 0 < p := by omega
  haveI : NeZero p := ⟨by omega⟩
  apply lucas_primality p (a : ZMod p)
  · have hc := powMod_cast a (p - 1) p
    rw [hfermat] at hc
    simpa using hc.symm
  · intro q hqp hqd
    have hqin : q ∈ qs :=
      prime_mem_of_dvd_listProd hqp qs hqs_prime (by rw [hprod]; exact hqd)
    intro hcontra
    apply hwit q hqin
    have hc := powMod_cast a ((p - 1) / q) p
    rw [hcontra] at hc
    have hlt : powMod a ((p - 1) / q) p < p := by
      rw [powMod_eq a _ p hp0]; exact Nat.mod_lt _ hp0
    have heq : ((powMod a ((p - 1) / q) p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [hc]; simp
    rw [ZMod.natCast_eq_natCast_iff] at heq
    unfold Nat.ModEq at heq
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp1] at heq
    exact heq

/-- The Fermat prime `2 ^ 16 + 1 = 65537`, proved via `lucas_of_certificate`.
Its `p - 1 = 2 ^ 16` has the single prime factor `2`; `3` is a witness. -/
theorem prime_65537 : Nat.Prime 65537 := by
  apply lucas_of_certificate 65537 (by norm_num) 3 (List.replicate 16 2)
  · decide
  · intro q hq
    rw [List.mem_replicate] at hq
    rw [hq.2]; exact Nat.prime_two
  · decide
  · intro q hq
    rw [List.mem_replicate] at hq
    rw [hq.2]; decide

end CatCrypt.PrattCertificate
