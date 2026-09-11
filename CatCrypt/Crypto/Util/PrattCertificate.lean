/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum
public import Transfer.Examples.ZModPowMod

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

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.PrattCertificate

/-- Binary (square-and-multiply) modular exponentiation: `powMod a k n = a ^ k % n`
(for `0 < n`), computed in `O(log k)` multiplications. Reuses the **tail-recursive**
`Transfer.ZModPowMod.powMod` (which carries the running square as an accumulator),
so kernel `decide` reduces it in `O(log k)` steps — fast and axiom-free at
cryptographic sizes, unlike `native_decide` (which needs a `leanc` compile and adds
a `Lean.ofReduceBool` axiom). The tree-recursive `powModFuel` this replaced was
`decide`-slow because the kernel materialised the whole recursion. -/
def powMod (a k n : ℕ) : ℕ := Transfer.ZModPowMod.powMod a k n

/-- The output is a residue: `powMod a k n < n` for `0 < n`. -/
theorem powMod_lt (a k n : ℕ) (hn : 0 < n) : powMod a k n < n :=
  Transfer.ZModPowMod.powModGo_lt n hn k (a % n) k (1 % n) (Nat.mod_lt 1 hn)

/-- Correctness of binary modular exponentiation. -/
theorem powMod_eq (a k n : ℕ) (hn : 0 < n) : powMod a k n = a ^ k % n := by
  have hml : a ^ k % n < n := Nat.mod_lt _ hn
  have hc : ((powMod a k n : ℕ) : ZMod n) = ((a ^ k % n : ℕ) : ZMod n) := by
    rw [powMod, Transfer.ZModPowMod.powMod_cast, ZMod.natCast_mod, Nat.cast_pow]
  have hmeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
  rwa [Nat.ModEq, Nat.mod_eq_of_lt (powMod_lt a k n hn), Nat.mod_eq_of_lt hml] at hmeq

/-- The fast `powMod` result cast into `ZMod n` equals the abstract power there,
so a `powMod … = 1` check discharges an `a ^ k = 1` hypothesis over `ZMod n`. -/
theorem powMod_cast (a k n : ℕ) [NeZero n] :
    ((powMod a k n : ℕ) : ZMod n) = (a : ZMod n) ^ k := by
  rw [powMod, Transfer.ZModPowMod.powMod_cast]

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
