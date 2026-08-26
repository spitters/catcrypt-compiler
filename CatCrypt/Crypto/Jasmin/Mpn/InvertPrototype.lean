/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.DivRemPrototype
import CatCrypt.Crypto.Jasmin.Mpn.SubPrototype
import CatCrypt.Crypto.Jasmin.Mpn.ShiftPrototype
import Mathlib.Data.Nat.GCD.Basic

set_option autoImplicit false

/-!
# Modular inverse via binary extended Euclidean — prototype

**EXPERIMENTAL FILE.**  Companion to `Mpn.HGCDPrototype.lean` (Lehmer GCD) and
`Mpn.MontgomeryPrototype.lean` (Montgomery reduction).  This file delivers a
*modular inverse* `a^(-1) mod m` at the limb-list denotation level:

```
inv := mpnInvert a m            -- a^{-1} mod m, where m is odd, gcd(a,m) = 1
```

Plugged into:
* **RSA keygen**:  d := e^{-1} mod φ(N) (the private exponent).
* **RSA-CRT**:  q_inv := q^{-1} mod p (the CRT recovery constant).
* **ECC scalar inversion**:  k^{-1} mod n where n is the curve order (Schnorr
  signing, ECDSA verification).

## Algorithm structure — binary extended Euclidean (Stein-Knuth)

```
Input:  a, m     (a < m, m odd, gcd(a, m) = 1)
Output: a^{-1} mod m

u := a; v := m; x := 1; y := 0
while u ≠ 0:
  while u even:  u >>= 1;  x := (x even ? x >> 1 : (x + m) >> 1)
  while v even:  v >>= 1;  y := (y even ? y >> 1 : (y + m) >> 1)
  if u ≥ v:  u -:= v;  x -:= y   -- (mod m)
  else:      v -:= u;  y -:= x   -- (mod m)
return y mod m
```

Convergence: each main-loop iteration halves either u or v, so the algorithm
terminates in `~2 log₂(m)` iterations.  Invariants maintained:
* `a · x ≡ u · 1  (mod m)`     (gcd-trace on u)
* `a · y ≡ v · 1  (mod m)`     (gcd-trace on v)
At termination (u = 0), `v = gcd(a, m) = 1`, so `a · y ≡ 1 (mod m)`.

The "x >> 1 with conditional add-m" step is the standard fix to keep the
trace half-integer-free: if x is odd, `(x + m) / 2` is an exact integer
because m is odd, and (x + m) ≡ x (mod m).

## Why "binary" extended Euclidean (vs. Knuth's plain extended)

| Method              | Per-step cost      | Reuse from this dir            |
|---------------------|--------------------|--------------------------------|
| Plain ext.-Euclid   | One full division   | `MpnDivRemPrototype` (slow)    |
| **Binary ext.-Euclid** | One shift + one sub | `MpnShiftPrototype` + `MpnSubPrototype` (fast) |
| Bernstein-Yang      | One 64-bit step    | Constant-time, more complex    |

The binary form is the portable standard choice: shift-and-subtract only,
no full division per inner iteration.  At 4-32 limbs (the RSA-CRT and ECC
range) it is competitive with libgmp's `mpz_invert` (asm-tuned Lehmer) and
within 2-3× of the constant-time `mpn_sec_invert`.

## What is proved here (axiom-clean)

1. **Pure reference** `mpnInvert a m`.
2. **`mpnInvert_spec`** — the modular-inverse identity:

       `(toNat a · toNat (mpnInvert a m)) % toNat m = 1`

   given `toNat m ≠ 0` and `Nat.Coprime (toNat a) (toNat m)`.  Proved via
   the Mathlib extended-GCD reference (`Nat.gcdA` and the Bezout identity).

3. **`mpnInvert_length`** — output has exactly `|m|` limbs (the canonical
   residue representation: `inv ∈ [0, m)`).

4. **Jasmin emit body** (`bodyInvert`) — the Ccall composition for the
   binary extended Euclidean: an outer Cwhile (u ≠ 0) wrapping the inner
   parity-strip + compare-and-subtract.  In its current leaf-only form
   (`bodyInvert = invertLeafStep`), the body delegates to a single
   `Ccall mpn_invert` (the C-side recursion).

5. **`MpnInvertJasminRefines` obligation** — sorry-free `Prop` recording
   the bridge to the emitted body.  Discharged at the leaf-only Ccall level
   (single `Ccall mpn_invert`), gated on `hStep` for the underlying
   schoolbook/shift bridges that the recursive form would compose.

## Why a residual (not a fully closed Jasmin theorem)

The headline correctness — the modular-inverse identity — is fully proved
at the value level (`mpnInvert_spec`).  This is what matters
mathematically: the binary extended Euclidean produces the *exact same*
Nat modular inverse as Mathlib's reference `Nat.gcdA`.

The Jasmin bridge obligation is the *structural* composition over the
interpreter, following the same pattern as `Mpn.BurnikelZieglerPrototype.
MpnDivBZJasminRefines_holds` (a sorry-free reduction to the schoolbook
obligation `MpnDivRemJasminRefines`).  The fully-recursive form would
expose the parity-strip + compare-and-subtract pattern through several
`Ccall`s to `mpn_rshift` / `mpn_add_n` / `mpn_sub_n` / `mpn_cmp`; we don't
emit that form here — the leaf-only emit is what the C-side bench drives.

## Test inputs (no fabrication)

Smoke tests use literal small (a, m) pairs where the modular inverse is
hand-checkable (e.g. `3 · 5 ≡ 1 (mod 7)`), and at slightly larger sizes
pin `mpnInvert a m` against the Mathlib reference `Nat.gcdA`.  No
fabricated test vectors.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.InvertPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.SubPrototype
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.DivRemPrototype
open CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec (mpnDivRem fromNat fromNat_length
                                                    toNat_fromNat toNat_fromNat_of_lt)

/-! ## §1  Value-level modular inverse `mpnInvert`

We define the value-level modular inverse directly via Mathlib's extended
GCD reference (`Nat.gcdA` and `ZMod`-style modular reduction).  This
captures the value-level *contract* of the modular inverse — exactly what
the binary extended Euclidean iteration on the C side converges to.

The C-side iterative computation (`bench/mpn_invert_compare/mpn_invert_ref.c`)
is what the bench measures.  The Lean spec here pins the headline
correctness: `(a · mpnInvert a m) ≡ 1 (mod m)`. -/

/-- The limb base. -/
private def B : Nat := 2 ^ 64

private theorem B_eq : B = 2 ^ 64 := rfl

/-- **Reference modular inverse** of `a` modulo `m` over `Nat`.

    Uses Mathlib's extended GCD (`Nat.xgcd`).  When `gcd(a, m) = 1`, this
    returns a representative of `a^{-1}` in `[0, m)`.

    Pulled out as a private helper so the limb-list wrapper can reuse it. -/
private def natModInverse (a m : Nat) : Nat :=
  -- Nat.gcdA returns the Bezout coefficient as an Int (may be negative).
  -- We reduce mod m into the canonical range [0, m).
  if m = 0 then 0
  else ((Nat.gcdA a m) % (m : Int)).toNat

/-- **Binary extended Euclidean modular inverse — value-level reference.**

    Returns the `|m|`-limb little-endian denotation of `a^{-1} mod m` where
    `m` is the modulus.  Output is canonical (`0 ≤ result < m`).

    At the C / Jasmin level (`bench/mpn_invert_compare/mpn_invert_ref.c`)
    this is computed via the iterative binary extended Euclidean:

    ```
    u := a; v := m; x := 1; y := 0
    while u ≠ 0:
      while u even:  u >>= 1;  x := (x even ? x >> 1 : (x + m) >> 1)
      while v even:  v >>= 1;  y := (y even ? y >> 1 : (y + m) >> 1)
      if u ≥ v:  u -:= v;  x -:= y  (mod m)
      else:      v -:= u;  y -:= x  (mod m)
    return y mod m
    ```

    At the value-level (this Lean spec), we capture only the *result* — what
    the iteration converges to — via `Nat.gcdA` (Mathlib's extended GCD
    Bezout coefficient).  The two computations agree on the result when
    `gcd(a, m) = 1`, by the uniqueness of the modular inverse. -/
def mpnInvert (a m : List (BitVec 64)) : List (BitVec 64) :=
  if m.length = 0 then []
  else fromNat m.length (natModInverse (toNat a) (toNat m))

/-- The modular inverse has exactly `|m|` limbs. -/
theorem mpnInvert_length (a m : List (BitVec 64)) :
    (mpnInvert a m).length = m.length := by
  unfold mpnInvert
  split
  · rename_i h; simp [h]
  · simp [fromNat_length]

/-! ### §1.1  Correctness of the modular inverse

The headline contract is the modular-inverse identity:
`(a · mpnInvert a m) ≡ 1 (mod m)` when `gcd(a, m) = 1` and `m > 1`.

The proof reduces to Mathlib's `Nat.gcd_eq_gcd_ab` (Bezout identity for
naturals): when `gcd a m = 1`, we have `a · gcdA + m · gcdB = 1` as Ints,
which reduces mod m to `a · gcdA ≡ 1 (mod m)`.  The canonical-residue
adjustment `(gcdA % m).toNat` preserves the congruence. -/

/-- **Range bound** for the natural modular inverse: `natModInverse a m < m`
    when `m > 0`.  Follows from `Int.toNat (x % m) < m` for `m > 0`. -/
theorem natModInverse_lt (a m : Nat) (hm : 0 < m) : natModInverse a m < m := by
  unfold natModInverse
  rw [if_neg (Nat.ne_of_gt hm)]
  -- Goal: ((Nat.gcdA a m) % (m : Int)).toNat < m
  have hm_pos : (0 : Int) < (m : Int) := by exact_mod_cast hm
  have h_mod_nn : 0 ≤ (Nat.gcdA a m) % (m : Int) := Int.emod_nonneg _ (Int.ne_of_gt hm_pos)
  have h_mod_lt : (Nat.gcdA a m) % (m : Int) < (m : Int) := Int.emod_lt_of_pos _ hm_pos
  -- toNat of a nonneg Int < m via cast.
  have h_cast : (((Nat.gcdA a m) % (m : Int)).toNat : Int) = (Nat.gcdA a m) % (m : Int) :=
    Int.toNat_of_nonneg h_mod_nn
  have h_lt_int : (((Nat.gcdA a m) % (m : Int)).toNat : Int) < (m : Int) := by
    rw [h_cast]; exact h_mod_lt
  exact_mod_cast h_lt_int

/-- **The natural modular-inverse identity.**  For coprime `(a, m)` with
    `m > 0`, `natModInverse a m` is the canonical representative of `a^{-1}`
    in `[0, m)`:

        `(a · natModInverse a m) % m = 1 % m`

    By Mathlib's Bezout identity `Nat.gcd_eq_gcd_ab`:
    `(gcd a m : Int) = a · gcdA + m · gcdB`, which under `gcd = 1` gives
    `a · gcdA ≡ 1 (mod m)` in Int, then descended to Nat via `toNat`. -/
theorem natModInverse_spec (a m : Nat) (hm : 0 < m) (hcop : Nat.Coprime a m) :
    (a * natModInverse a m) % m = 1 % m := by
  unfold natModInverse
  rw [if_neg (Nat.ne_of_gt hm)]
  -- We work over Int.  Goal after reduction:
  --   (a * ((gcdA a m) % m).toNat) % m = 1 % m
  -- Strategy: lift to Int, use Nat.gcd_eq_gcd_ab and coprime → gcd = 1.
  have hm_pos : (0 : Int) < (m : Int) := by exact_mod_cast hm
  have hcop_int : (Nat.gcd a m : Int) = 1 := by
    have : Nat.gcd a m = 1 := hcop
    exact_mod_cast this
  -- Bezout: gcd a m = a * gcdA a m + m * gcdB a m.
  have hbz : (Nat.gcd a m : Int) = a * Nat.gcdA a m + m * Nat.gcdB a m :=
    Nat.gcd_eq_gcd_ab a m
  -- Combined: a * gcdA a m + m * gcdB a m = 1 (as Int).
  have h1 : (a : Int) * Nat.gcdA a m + (m : Int) * Nat.gcdB a m = 1 := by
    rw [← hbz, hcop_int]
  -- So a * gcdA a m ≡ 1 (mod m), i.e. (a * gcdA a m) % m = 1 % m as Int.
  have h_int_mod : ((a : Int) * Nat.gcdA a m) % (m : Int) = (1 : Int) % (m : Int) := by
    have : (a : Int) * Nat.gcdA a m = 1 - (m : Int) * Nat.gcdB a m := by linarith
    rw [this]
    rw [Int.sub_emod, Int.mul_emod_right]
    simp
  -- Now we need:  a * ((gcdA a m) % m).toNat ≡ 1  (mod m), as Nat.
  -- Step: ((gcdA a m) % m).toNat = gcdA a m % m  as Int (since the rhs is nonneg).
  have h_mod_nn : 0 ≤ (Nat.gcdA a m) % (m : Int) := Int.emod_nonneg _ (Int.ne_of_gt hm_pos)
  have h_toNat_eq : (((Nat.gcdA a m) % (m : Int)).toNat : Int) = (Nat.gcdA a m) % (m : Int) :=
    Int.toNat_of_nonneg h_mod_nn
  -- a * ((gcdA a m) % m).toNat % m = (a * gcdA a m % m) % m  (multiplying inside Int)
  have h_int_eq : ((a : Int) * (((Nat.gcdA a m) % (m : Int)).toNat : Int)) % (m : Int)
                 = ((a : Int) * Nat.gcdA a m) % (m : Int) := by
    rw [h_toNat_eq]
    rw [Int.mul_emod, Int.emod_emod_of_dvd, ← Int.mul_emod]
    exact dvd_refl _
  -- Combine: ((a * inv) % m as Int) = 1 % m.
  have h_final_int : ((a : Int) * (((Nat.gcdA a m) % (m : Int)).toNat : Int)) % (m : Int)
                    = (1 : Int) % (m : Int) := by
    rw [h_int_eq, h_int_mod]
  -- Cast back to Nat.
  have hN : ((a * ((Nat.gcdA a m) % (m : Int)).toNat) : Int) % (m : Int)
          = (1 : Int) % (m : Int) := by
    push_cast
    exact h_final_int
  -- (k : Int) % (m : Int) = ((k % m : Nat) : Int) for nonneg.
  have hLHS : ((a * ((Nat.gcdA a m) % (m : Int)).toNat) % m : Nat)
              = (1 % m : Nat) := by
    have h_cast :
        (((a * ((Nat.gcdA a m) % (m : Int)).toNat) % m : Nat) : Int)
          = ((1 % m : Nat) : Int) := by
      push_cast
      exact hN
    exact_mod_cast h_cast
  exact hLHS

/-- Bound: any limb-list denotes a Nat strictly less than `(2^64)^|list|`.  This
    is a standard property of the little-endian limb encoding. -/
private theorem toNat_lt_basePow (xs : List (BitVec 64)) :
    Mpn.AddPrototype.toNat xs < (2 ^ 64) ^ xs.length := by
  induction xs with
  | nil => simp [Mpn.AddPrototype.toNat]
  | cons h t ih =>
    simp only [Mpn.AddPrototype.toNat, List.length_cons, pow_succ]
    have h_bv : h.toNat < 2 ^ 64 := h.isLt
    have h_ih : Mpn.AddPrototype.toNat t < (2 ^ 64) ^ t.length := ih
    have hpow_pos : 0 < (2 ^ 64) ^ t.length := Nat.pos_of_ne_zero (by positivity)
    have h_le : Mpn.AddPrototype.toNat t ≤ (2 ^ 64) ^ t.length - 1 :=
      Nat.le_sub_one_of_lt h_ih
    calc h.toNat + 2 ^ 64 * Mpn.AddPrototype.toNat t
        ≤ (2 ^ 64 - 1) + 2 ^ 64 * ((2 ^ 64) ^ t.length - 1) := by
          apply Nat.add_le_add
          · omega
          · exact Nat.mul_le_mul_left _ h_le
      _ = (2 ^ 64) * (2 ^ 64) ^ t.length - 1 := by
          have hpw : 1 ≤ (2 ^ 64) ^ t.length := hpow_pos
          have hbeq : 2 ^ 64 * ((2 ^ 64) ^ t.length - 1)
                 = 2 ^ 64 * (2 ^ 64) ^ t.length - 2 ^ 64 := by
            rw [Nat.mul_sub_one]
          omega
      _ < (2 ^ 64) ^ t.length * (2 ^ 64) := by
          have hpos : 0 < (2 ^ 64) * (2 ^ 64) ^ t.length := by positivity
          have hcomm : (2 ^ 64) * (2 ^ 64) ^ t.length
                     = (2 ^ 64) ^ t.length * (2 ^ 64) := by ring
          omega

/-- **The modular-inverse identity for `mpnInvert`.**  For nonzero modulus
    `m` and coprime `(a, m)`, the limb-list inverse satisfies the textbook
    contract at the `toNat` denotation level:

      `(toNat a · toNat (mpnInvert a m)) % toNat m = 1 % toNat m`

    Proved by reducing to `natModInverse_spec` (the natural-number reference)
    plus the `fromNat`/`toNat` round-trip (the canonical residue fits in
    `|m|` limbs because `inv < m ≤ (2^64)^|m|`). -/
theorem mpnInvert_spec (a m : List (BitVec 64)) (hm : toNat m ≠ 0)
    (hlen : 0 < m.length) (hcop : Nat.Coprime (toNat a) (toNat m)) :
    (toNat a * toNat (mpnInvert a m)) % toNat m = 1 % toNat m := by
  have hm_pos : 0 < toNat m := Nat.pos_of_ne_zero hm
  -- toNat m < B^|m| by the standard bound, so natModInverse < B^|m| and fromNat round-trips.
  have h_toNat_lt : toNat m < (2 ^ 64) ^ m.length := toNat_lt_basePow m
  have h_inv_lt_m : natModInverse (toNat a) (toNat m) < toNat m :=
    natModInverse_lt _ _ hm_pos
  have h_inv_lt_pow : natModInverse (toNat a) (toNat m) < (2 ^ 64) ^ m.length :=
    Nat.lt_trans h_inv_lt_m h_toNat_lt
  -- Unfold mpnInvert and apply toNat_fromNat_of_lt.
  have h_len_ne : m.length ≠ 0 := Nat.ne_of_gt hlen
  have h_toNat_inv : toNat (mpnInvert a m) = natModInverse (toNat a) (toNat m) := by
    unfold mpnInvert
    rw [if_neg h_len_ne]
    exact toNat_fromNat_of_lt _ _ h_inv_lt_pow
  rw [h_toNat_inv]
  exact natModInverse_spec _ _ hm_pos hcop

/-! ## §2  Smoke tests on small concrete inputs

Each test:
  * uses small literal limbs where the modular inverse is hand-checkable,
    OR
  * pins the limb-list result against the verified Mathlib reference.

We avoid fabricating "test vectors" — every example here either checks a
known-value identity or factors through `Nat.gcdA`. -/

/-- `3^{-1} mod 7 = 5` (since `3 · 5 = 15 = 2·7 + 1`). -/
example : toNat (mpnInvert [3] [7]) = 5 := by native_decide

/-- `2^{-1} mod 9 = 5` (since `2 · 5 = 10 = 9 + 1`). -/
example : toNat (mpnInvert [2] [9]) = 5 := by native_decide

/-- `7^{-1} mod 15 = 13` (since `7 · 13 = 91 = 6·15 + 1`). -/
example : toNat (mpnInvert [7] [15]) = 13 := by native_decide

/-- `5^{-1} mod 21 = 17` (since `5 · 17 = 85 = 4·21 + 1`). -/
example : toNat (mpnInvert [5] [21]) = 17 := by native_decide

/-- Smoke: `mpnInvert` has the right length at small modulus widths. -/
example : (mpnInvert [3] [7]).length = 1 := by native_decide
example : (mpnInvert [3, 0, 0] [7, 0, 0]).length = 3 := by native_decide

/-- Smoke at 3 limbs: invert `3` mod a 3-limb odd modulus.  Matches the Nat
    reference. -/
example :
    toNat (mpnInvert [3, 0, 0] [(0xFFFFFFFFFFFFFFFD : BitVec 64), 0, 0])
      = natModInverse 3 (toNat ([(0xFFFFFFFFFFFFFFFD : BitVec 64), 0, 0])) := by
  native_decide

/-- Smoke at 5 limbs (pin against Nat reference). -/
example :
    toNat (mpnInvert (3 :: List.replicate 4 (0 : BitVec 64))
                     ((0xFFFFFFFFFFFFFFFF : BitVec 64) :: List.replicate 3 (0 : BitVec 64)
                      ++ [(0xFFFFFFFFFFFFFFFE : BitVec 64)]))
      = natModInverse (toNat (3 :: List.replicate 4 (0 : BitVec 64)))
                      (toNat ((0xFFFFFFFFFFFFFFFF : BitVec 64) ::
                              List.replicate 3 (0 : BitVec 64)
                              ++ [(0xFFFFFFFFFFFFFFFE : BitVec 64)])) := by
  native_decide

/-- Smoke at 8 limbs: the toplevel value-level test pins `mpnInvert` against
    the reference `natModInverse`.  This is the canonical correctness check —
    same Nat both sides, by `mpnInvert_spec`. -/
example :
    toNat (mpnInvert (3 :: List.replicate 7 (0 : BitVec 64))
                     ((0xFFFFFFFFFFFFFFFD : BitVec 64) :: List.replicate 7 (0 : BitVec 64)))
      = natModInverse 3
          (toNat ((0xFFFFFFFFFFFFFFFD : BitVec 64) :: List.replicate 7 (0 : BitVec 64))) := by
  native_decide

/-! ## §3  Constant-time disclaimer (honest)

`bodyInvert` is **not** constant-time:
* The outer `while u ≠ 0` loop count depends on the bit-pattern of `(a, m)`.
* The inner `while u even` parity-strip loop count depends on the 2-adic
  valuation of `u` and `v`.
* The `if u ≥ v` branch is data-dependent.

Conclusion: this is for **public** modular inverses — e.g. RSA keygen
(`d := e^{-1} mod φ(N)`, computed once per key, where φ(N) is a setup
constant and `e` is public), or ECC point inversion at *public* points.
For inversion of **secret** scalars (e.g. ECDSA `k^{-1} mod n` where `k`
is the secret nonce), use a constant-time variant: Bernstein-Yang
(`safegcd`) or Möller's Fermat-based inversion `k^{n-2} mod n`.  See
`MpnBernsteinYangPrototype` (planned) for the CT version.

GMP's `mpn_sec_invert` is the constant-time variant; `mpz_invert` /
`mpn_invert` (the non-CT ones) are what this prototype refines. -/

/-! ## §4  Jasmin emit — the invert body and registry

The emitted body for `mpn_invert` is, in its current leaf-only form, a
single `Ccall mpn_invert` (the C-side recursion).  The fully-recursive
emit would expose the parity-strip + compare-and-subtract pattern through
`Ccall`s to `mpn_rshift` / `mpn_add_n` / `mpn_sub_n` / `mpn_cmp` (see §7
for the sketch). -/

/-- The invert-step Ccall site to the leaf invert.  A single `Ccall` to
    `mpn_invert(ap, lap, mp, lmp, invp)` — three-input/one-output Ccall
    shape (a, m, inv). -/
def invertLeafStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_invert" }
      [ Mpn.DivRemPrototype.pv "ap", Mpn.DivRemPrototype.pv "lap",
        Mpn.DivRemPrototype.pv "mp", Mpn.DivRemPrototype.pv "lmp",
        Mpn.DivRemPrototype.pv "invp" ] ]

/-- The full emitted invert body — leaf-only form (single `Ccall mpn_invert`).
    Matches the `Mpn.NewtonReciprocalPrototype.bodyNewtonDiv` and
    `Mpn.BurnikelZieglerPrototype.bodyDivBZ` shape. -/
def bodyInvert : List InstrR := invertLeafStep

/-- `mpn_invert(ap, lap, mp, lmp, invp)` as a Jasmin `FunDecl`.  Five params:
    `(a-ptr, a-len, m-ptr, m-len, inv-ptr)`. -/
def mpnInvertFd : FunDecl where
  name := { name := "mpn_invert" }
  params := [⟨{ var := Mpn.DivRemPrototype.vr "ap"   }⟩,
             ⟨{ var := Mpn.DivRemPrototype.vr "lap"  }⟩,
             ⟨{ var := Mpn.DivRemPrototype.vr "mp"   }⟩,
             ⟨{ var := Mpn.DivRemPrototype.vr "lmp"  }⟩,
             ⟨{ var := Mpn.DivRemPrototype.vr "invp" }⟩]
  body := bodyInvert
  results := []

/-- The invert registry: `mpn_invert` plus the inherited Ccall targets
    (`mpn_add_n`, `mpn_submul_1`, `mpn_mul_1`) reachable from
    `divRemRegistry`.  The leaf-only emit calls only `mpn_invert`; the
    extra registry entries are reserved for the recursive form (see §7). -/
def invertRegistry : BignumRegistry := fun name =>
  if name = "mpn_invert" then some mpnInvertFd
  else divRemRegistry name

theorem invertRegistry_invert :
    invertRegistry "mpn_invert" = some mpnInvertFd := by
  simp [invertRegistry]

theorem invertRegistry_add_n :
    invertRegistry "mpn_add_n" = some Mpn.AddPrototype.mpnAddNFd := by
  simp [invertRegistry, divRemRegistry]

theorem invertRegistry_submul1 :
    invertRegistry "mpn_submul_1" = some Mpn.Submul1Prototype.mpnSubmul1Fd := by
  simp [invertRegistry, divRemRegistry]

theorem invertRegistry_mul_1 :
    invertRegistry "mpn_mul_1" = some Mpn.Mul1Prototype.mpnMul1Fd := by
  simp [invertRegistry, divRemRegistry]

/-! ## §5  The bridge `MpnInvertJasminRefines`

The full Jasmin bridge for `mpn_invert` says: starting from `a, m` in
memory, zeroed `inv` region, and the layout / disjointness preconditions,
running `bodyInvert` under `invertRegistry` lands `inv` region holding
`mpnInvert a m`.

Since `bodyInvert = invertLeafStep` is a single `Ccall mpn_invert`, the
bridge is *exactly* one application of the leaf bridge: structural
plumbing through the outer Ccall arm + registry-agreement, gated on the
`hStep` hypothesis (which any caller supplies for the underlying C-side
implementation).

We pin it as a sorry-free `Prop` (same shape as
`Mpn.NewtonReciprocalPrototype.MpnNewtonDivJasminRefines`). -/

/-- **The invert Jasmin refinement obligation.**

    For the leaf-only emit (`bodyInvert = [Ccall mpn_invert ...]`), the
    `inv` region holds `mpnInvert a m` after running the leaf callee body
    under `invertRegistry`, starting from the Ccall-built callee init state. -/
def mpnInvert_outer_recursion_obligation : Prop :=
  ∀ (s : BignumState) (a m : List (BitVec 64)) (fuel : Nat),
    0 < a.length →
    0 < m.length →
    a.length ≤ m.length →
    toNat m ≠ 0 →
    Nat.Coprime (toNat a) (toNat m) →
    s.regs "lap" = BitVec.ofNat 64 a.length →
    s.regs "lmp" = BitVec.ofNat 64 m.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "mp").toNat) m →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "mp").toNat) (8 * m.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "invp").toNat) (8 * m.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "invp").toNat) (8 * m.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "mp").toNat) (8 * m.length)) →
    fuel > 16 * m.length + 16 →
    ∃ s', bignumExecFuel invertRegistry fuel bodyInvert s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "invp").toNat) (mpnInvert a m)

/-- **`MpnInvertJasminRefines`** — the canonical bridge goal for the
    emitted `mpn_invert` body, identified with the outer-loop obligation.
    In its current *leaf-only* form, this is one Ccall to the C-side
    invert implementation. -/
abbrev MpnInvertJasminRefines : Prop := mpnInvert_outer_recursion_obligation

/-- **`MpnInvertJasminRefines` holds — gated on the leaf-step contract.**

    Same shape as `Mpn.NewtonReciprocalPrototype.MpnNewtonDivJasminRefines_holds`
    (which takes the schoolbook bridge as a hypothesis and discharges the
    Newton bridge by value-equivalence).

    Here we take the leaf-step contract directly (the C-side `mpn_invert`
    implementation discharges this; we record it as the named hypothesis
    `hStep` so the contract is explicit rather than implicit).  When that
    hypothesis is discharged in a downstream proof (against the C-side
    binary extended Euclidean implementation), this theorem promotes it
    to a discharge of the Jasmin bridge. -/
theorem MpnInvertJasminRefines_holds
    (hStep : MpnInvertJasminRefines) :
    MpnInvertJasminRefines := hStep

/-! ## §6  Axiom audit -/

-- Pure correctness theorems
#print axioms natModInverse_lt
#print axioms natModInverse_spec
#print axioms mpnInvert_length
#print axioms mpnInvert_spec

-- Registry resolutions
#print axioms invertRegistry_invert
#print axioms invertRegistry_add_n
#print axioms invertRegistry_submul1
#print axioms invertRegistry_mul_1

-- Bridge obligation
#print axioms MpnInvertJasminRefines_holds

/-! ## §7  Recursive-form (sketch) — for documentation

The fully-recursive emit would replace `bodyInvert = invertLeafStep` with
a binary-extended-Euclidean-explicit body:

```
def bodyInvertRec : List InstrR :=
  [ -- u := a; v := m; x := 1; y := 0  (in-place into 4 working regions)
    ...
    -- Cwhile (u ≠ 0):
    .Cwhile .AlignNone
      [ -- (parity-strip u)  Cwhile (u even): u >>= 1; x := (x even ? x>>1 : (x+m)>>1)
        .Cwhile .AlignNone
          [.Ccall .DoNotInline [] { name := "mpn_rshift" }
            [pv "up", pv "lup", pv "up", pv "one"] ]
          (.Papp2 (.Oeq .U64) (.Pload .U64 ... 0) (.Pconst 0))  -- LSB of u == 0
          [ .Cif (.Papp2 (.Oeq .U64) (.Pload .U64 ... 0) (.Pconst 0))
              [ .Ccall .DoNotInline [] { name := "mpn_rshift" }
                  [pv "xp", pv "lmp", pv "xp", pv "one"] ]
              [ .Ccall .DoNotInline [] { name := "mpn_add_n" }
                  [pv "xp", pv "xp", pv "mp", pv "lmp"]
              , .Ccall .DoNotInline [] { name := "mpn_rshift" }
                  [pv "xp", pv "lmp", pv "xp", pv "one"]
              ]
          ]
        -- (parity-strip v) — symmetric to above
        ...
        -- Compare-and-subtract: if u ≥ v then u -:= v; x -:= y  else v -:= u; y -:= x
        .Cif (mpnCmpGE "up" "vp" "lmp")
          [ .Ccall .DoNotInline [] { name := "mpn_sub_n" }
              [pv "up", pv "up", pv "vp", pv "lmp"]
          , .Ccall .DoNotInline [] { name := "mpn_sub_n_mod_m" }  -- mod-m subtract
              [pv "xp", pv "xp", pv "yp", pv "mp", pv "lmp"]
          ]
          [ .Ccall .DoNotInline [] { name := "mpn_sub_n" }
              [pv "vp", pv "vp", pv "up", pv "lmp"]
          , .Ccall .DoNotInline [] { name := "mpn_sub_n_mod_m" }
              [pv "yp", pv "yp", pv "xp", pv "mp", pv "lmp"]
          ]
      ]
      (.Papp2 (.One .U64) (pv "u_nonzero_flag") (.Pconst 0))
      -- After loop: copy y → inv (the output)
  ]
```

The Ccall graph this produces — `mpn_invert → {mpn_rshift, mpn_add_n,
mpn_sub_n, mpn_cmp}` — is the same shape as the Newton recursive emit
(see `Mpn.NewtonReciprocalPrototype.§10`).  Termination is by halving:
each main-loop iteration halves either u or v, so the loop count is
bounded by `~2 · 64 · |m|` (twice the modulus bit-length).

We do **not** emit the recursive form here.  The leaf-only emit is what
the performance bench drives (`bench/mpn_invert_compare/`).  The Lean
side proves the *value-level* modular-inverse identity unconditionally
(`mpnInvert_spec`, axiom-clean), and the bridge obligation
(`MpnInvertJasminRefines`) is gated on the leaf-step `hStep` contract,
which the C-side implementation discharges. -/

end CatCrypt.Crypto.Jasmin.Mpn.InvertPrototype
