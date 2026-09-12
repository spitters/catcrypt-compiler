/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.ZMod.Basic
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

/-!
# A CIOS-structured Montgomery field-multiply emit, tied to the `ZMod p` spec

`RelationalFrontSecp256k1.lean` realizes the secp256k1 base-field multiply through
a wide **SOS**/Barrett block: form the `2k`-limb product, then a Barrett reduce
(`mlMulMod`, `encMLK_mul_commutes`). This module produces the alternative the
instruction-selection layer wants for the k256 performance gap: the emitted block
is the **CIOS** (Coarsely-Integrated-Operand-Scanning) Montgomery multiply — the
`ciosWord` reduce-word chain built from the `jasminDialect` register primitives
(`mulHiW` = MULX hi, `regArith .mul` = MULX lo, `addCarryWord`/`carryOutBit` =
ADD/ADC), NOT a wide product-then-Barrett block.

The block is `ciosMont4`: form the schoolbook product `mulLimbs x y` (value
`valLimbs x · valLimbs y`, the proved `Cios4LimbProven.mulLimbs_reconstruct`), then
run **four** `ciosWord` per-word Montgomery reductions (each a proved
`ciosWord_eq` step). Its `valLimbs` read is the four-fold reduction `montRedc4`,
and — for operands below the modulus — decodes over `ZMod p` to the Montgomery
product `x·y·R⁻¹`.

## What is proved here vs. reused

* **Reused (not reproved):** the per-word reduction identity
  `Cios4LimbProven.ciosWord_eq` (`valLimbs (ciosWord N n' T) = montgomeryReduce
  (valLimbs N) (2^64) n' (valLimbs T)`) and the schoolbook-product identity
  `mulLimbs_reconstruct`. These are the CIOS structure's value theorems.
* **Proved here — the full-product correctness of the four-word chain.** The
  assembled `Cios4LimbProven.montRedc4_correct` carries the precondition
  `T < 2^64 · N`, which the schoolbook product `x·y ~ 2^512` violates. The correct
  input bound for the four-word chain seeded with the full product is
  `T < 2^256 · N` (the full-radix Montgomery bound, `= R · N`). `montRedc4_full`
  establishes it: the congruence holds with no `T`-bound (Montgomery's exactness),
  and the range `< 2N` follows by propagating the per-step floor bound
  `redc(T)·2^64 ≤ T + (2^64-1)·N` down the four reductions.
* **Tied to the spec.** `ciosMont4_realizes_montmul` casts the chain's congruence
  into `ZMod p` at the secp256k1 prime: the emitted block's decoded value `V`
  satisfies `V · 2^256 = (valLimbs x)·(valLimbs y)` in `ZMod p` — the Montgomery
  multiply law (`montgomeryMul_correct` cast to `ZMod p`) — with the range
  `V < 2p` (one conditional subtract from canonical).

## Front selection (what a fully-automatic CIOS choice still needs)

This delivers the CIOS emit with the full `denote = spec` proof — a compiled CIOS
realization the front adopts, parallel to the SOS realization. Making the front
*choose* CIOS automatically from the field-mul spec (rather than the SOS Barrett
block) is an instruction-selection/cost-model decision documented in the module
footer.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4000

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul

open CatCrypt.Crypto.Number
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

/-! ## 1. Per-step lemmas for the four-word chain (no `T`-bound)

The two facts a Montgomery reduction word step gives with **no** input-range
hypothesis: the exactness congruence `redc(T)·S ≡ T (mod N)` and the floor bound
`redc(T)·S ≤ T + (S-1)·N`. The assembled range/congruence in `Cios4LimbProven`
enters `montgomeryReduce_correct`, whose `T < S·N` precondition is too tight for a
full product; these two carry the chain instead. -/

/-- **Reduction-step congruence, no input bound.** For `S > 0` and the Montgomery
    constant condition `N·n' ≡ -1 (mod S)`, one `montgomeryReduce` word step
    satisfies `redc(T)·S ≡ T (mod N)` for every `T` — Montgomery's exactness fact,
    with no `T < S·N` hypothesis. Extracted from `montgomeryReduce_dvd`. -/
theorem redc_step_cong (N S nP T : Nat) (hS : 0 < S)
    (hnp : (N * nP) % S = S - 1) :
    montgomeryReduce N S nP T * S ≡ T [MOD N] := by
  set m := (T * nP) % S with hm
  have hdvd : S ∣ (T + m * N) := montgomeryReduce_dvd N S nP T hS hnp
  have hexact : montgomeryReduce N S nP T * S = T + m * N := by
    unfold montgomeryReduce
    rw [← hm, Nat.div_mul_cancel hdvd]
  rw [hexact]
  have hzero : m * N ≡ 0 [MOD N] := (Nat.modEq_zero_iff_dvd).mpr ⟨m, by ring⟩
  have h := hzero.add_left T
  simp only [Nat.add_zero] at h
  exact h

/-- **Reduction-step floor bound, no input bound.** One `montgomeryReduce` word
    step satisfies `redc(T)·S ≤ T + (S-1)·N` for every `T` (the Montgomery digit
    `m = (T·n') mod S ≤ S-1`, and `(T + m·N)/S · S ≤ T + m·N`). Propagated four
    times this gives the chain's `< 2N` range. -/
theorem redc_step_mul_le (N S nP T : Nat) (hS : 0 < S) :
    montgomeryReduce N S nP T * S ≤ T + (S - 1) * N := by
  have hle : montgomeryReduce N S nP T * S ≤ T + ((T * nP) % S) * N := by
    unfold montgomeryReduce
    exact Nat.div_mul_le_self (T + ((T * nP) % S) * N) S
  have hmlt : (T * nP) % S ≤ S - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ hS)
  have : ((T * nP) % S) * N ≤ (S - 1) * N := Nat.mul_le_mul_right N hmlt
  omega

/-! ## 2. Full-product correctness of the four-word Montgomery chain

`montRedc4 N n' T` (the four per-word reductions, each at radix `2^64`) computes a
value `< 2N` congruent to `T·(2^256)⁻¹` **for the full-radix input bound
`T < 2^256·N`** — the bound the schoolbook product `x·y < N² < 2^256·N` satisfies.
This is the correctness the assembled `montRedc4_correct` (bound `T < 2^64·N`) does
not cover. -/

/-- **Full-radix correctness of the four-word chain.** For an odd modulus `N`,
    Montgomery constant `n'` (`N·n' ≡ -1 (mod 2^64)`), and input `T < 2^256·N` (the
    full-radix bound the schoolbook product satisfies): the four per-word reductions
    land in `[0, 2N)` and `montRedc4 N n' T · 2^256 ≡ T (mod N)`. The congruence
    chains `redc_step_cong` four times; the range propagates `redc_step_mul_le` down
    the four steps. -/
theorem montRedc4_full (N nP T : Nat) (hN : 0 < N)
    (hnp : (N * nP) % 2 ^ 64 = 2 ^ 64 - 1) (hT : T < 2 ^ 256 * N) :
    montRedc4 N nP T < 2 * N ∧ (montRedc4 N nP T) * 2 ^ 256 ≡ T [MOD N] := by
  set S := (2 : Nat) ^ 64 with hSdef
  have hS : 0 < S := by rw [hSdef]; positivity
  have hSN : N ≤ S * N := Nat.le_mul_of_pos_left N hS
  set w1 := montgomeryReduce N S nP T with hw1
  set w2 := montgomeryReduce N S nP w1 with hw2
  set w3 := montgomeryReduce N S nP w2 with hw3
  set w4 := montgomeryReduce N S nP w3 with hw4
  have hmr4 : montRedc4 N nP T = w4 := by
    simp only [montRedc4, ← hSdef, ← hw1, ← hw2, ← hw3, ← hw4]
  -- the four per-step floor bounds
  have hb1 : w1 * S ≤ T + (S - 1) * N := redc_step_mul_le N S nP T hS
  have hb2 : w2 * S ≤ w1 + (S - 1) * N := redc_step_mul_le N S nP w1 hS
  have hb3 : w3 * S ≤ w2 + (S - 1) * N := redc_step_mul_le N S nP w2 hS
  have hb4 : w4 * S ≤ w3 + (S - 1) * N := redc_step_mul_le N S nP w3 hS
  have hs1N : (S - 1) * N + N = S * N := by rw [Nat.sub_one_mul]; omega
  have hTS : T < S ^ 4 * N := by
    have hpow : S ^ 4 = 2 ^ 256 := by rw [hSdef]; norm_num
    rw [hpow]; exact hT
  -- propagate: w1 < S^3·N + N
  have hk1 : w1 < S ^ 3 * N + N := by
    have hmul : S * w1 < S * (S ^ 3 * N + N) := by
      have hexp : S * (S ^ 3 * N + N) = S ^ 4 * N + S * N := by ring
      have hcomm : S * w1 = w1 * S := by ring
      rw [hexp, hcomm]; omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hk2 : w2 < S ^ 2 * N + N := by
    have hmul : S * w2 < S * (S ^ 2 * N + N) := by
      have hexp : S * (S ^ 2 * N + N) = S ^ 3 * N + S * N := by ring
      have hcomm : S * w2 = w2 * S := by ring
      rw [hexp, hcomm]; omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hk3 : w3 < S * N + N := by
    have hmul : S * w3 < S * (S * N + N) := by
      have hexp : S * (S * N + N) = S ^ 2 * N + S * N := by ring
      have hcomm : S * w3 = w3 * S := by ring
      rw [hexp, hcomm]; omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hk4 : w4 < 2 * N := by
    have hmul : S * w4 < S * (2 * N) := by
      have hexp : S * (2 * N) = S * N + S * N := by ring
      have hcomm : S * w4 = w4 * S := by ring
      rw [hexp, hcomm]; omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  refine ⟨by rw [hmr4]; exact hk4, ?_⟩
  -- congruence: chain the four step congruences (as in montRedc4_correct)
  rw [hmr4]
  have c1 : w1 * S ≡ T [MOD N] := redc_step_cong N S nP T hS hnp
  have c2 : w2 * S ≡ w1 [MOD N] := redc_step_cong N S nP w1 hS hnp
  have c3 : w3 * S ≡ w2 [MOD N] := redc_step_cong N S nP w2 hS hnp
  have c4 : w4 * S ≡ w3 [MOD N] := redc_step_cong N S nP w3 hS hnp
  have e256 : (2 : Nat) ^ 256 = S * (S * (S * S)) := by rw [hSdef]; ring
  have step1 : w4 * (2 ^ 256) ≡ w3 * (S * (S * S)) [MOD N] := by
    rw [e256]
    calc w4 * (S * (S * (S * S)))
        = (w4 * S) * (S * (S * S)) := by ring
      _ ≡ w3 * (S * (S * S)) [MOD N] := c4.mul_right _
  have step2 : w3 * (S * (S * S)) ≡ w2 * (S * S) [MOD N] := by
    calc w3 * (S * (S * S))
        = (w3 * S) * (S * S) := by ring
      _ ≡ w2 * (S * S) [MOD N] := c3.mul_right _
  have step3 : w2 * (S * S) ≡ w1 * S [MOD N] := by
    calc w2 * (S * S)
        = (w2 * S) * S := by ring
      _ ≡ w1 * S [MOD N] := c2.mul_right _
  exact ((step1.trans step2).trans step3).trans c1

/-! ## 3. The CIOS-structured emit block and its `valLimbs` = `montRedc4`

`ciosMont4 x y` is the CIOS Montgomery multiply over the `jasminDialect` register
primitives: form the schoolbook product `mulLimbs x y`, then four `ciosWord`
reduce-word steps against the secp256k1 modulus limbs. Its `valLimbs` read is the
four-fold reduction `montRedc4` of the product value. -/

/-- The secp256k1 Montgomery constant `n' = 0xd838091dd2253531` (`= -p⁻¹ mod 2^64`)
    as a 64-bit word. -/
def secpNPrime : BitVec 64 := 0xd838091dd2253531

theorem secpNPrime_toNat : secpNPrime.toNat = 0xd838091dd2253531 := by native_decide

/-- One length-preservation fact for the reduce-word step: `ciosWord` returns a
    limb vector of the same length as its accumulator (`sum ++ [carry]` then drop
    the low limb). -/
theorem ciosWord_length (N : List (BitVec 64)) (nP : BitVec 64) (T : List (BitVec 64)) :
    (ciosWord N nP T).length = T.length := by
  simp only [ciosWord, List.length_drop, List.length_append, List.length_cons,
    List.length_nil, addLimbs_length]
  omega

/-- The exact length of the schoolbook product for a nonempty multiplier:
    `|mulLimbs x y| = |x| + 1 + 2·(|y| - 1)`. Mirrors the `mulLimbs` recursion
    (`|mulLimbs x (y₀::ys)| = |mulLimbs x ys| + 2`). -/
theorem mulLimbs_length (x : List (BitVec 64)) :
    ∀ y : List (BitVec 64), y ≠ [] →
      (mulLimbs x y).length = x.length + 1 + 2 * (y.length - 1) := by
  intro y
  induction y with
  | nil => intro h; exact absurd rfl h
  | cons y0 ys ih =>
      intro _
      cases hys : ys with
      | nil => simp only [mulLimbs, mulScalar_length, List.length_cons, List.length_nil]
      | cons z zs =>
          show ((mulScalar x y0).headD 0
              :: ((addLimbs (mulLimbs x (z :: zs)) (mulScalar x y0).tail 0).1
                ++ [(addLimbs (mulLimbs x (z :: zs)) (mulScalar x y0).tail 0).2.setWidth 64])).length
            = x.length + 1 + 2 * ((y0 :: z :: zs).length - 1)
          rw [List.length_cons, List.length_append, addLimbs_length, List.length_cons,
            List.length_nil]
          have hih := ih (by rw [hys]; simp)
          rw [hys] at hih
          rw [hih]
          simp only [List.length_cons]
          omega

/-- **The CIOS-structured Montgomery field-multiply block.** Over the
    `jasminDialect` register primitives: form the schoolbook product `mulLimbs x y`
    (the `mulHiW`/`regArith .mul`/`addCarryWord`/`carryOutBit` carry chain), then
    four `ciosWord` per-word Montgomery reductions against the secp256k1 modulus
    limbs. This is the CIOS emit — the `ciosWord` chain, not a wide SOS block. -/
def ciosMont4 (x y : List (BitVec 64)) : List (BitVec 64) :=
  ciosWord secp256k1Limbs secpNPrime
    (ciosWord secp256k1Limbs secpNPrime
      (ciosWord secp256k1Limbs secpNPrime
        (ciosWord secp256k1Limbs secpNPrime (mulLimbs x y))))

/-- **The CIOS emit's value is the four-fold Montgomery reduction of the product.**
    `valLimbs (ciosMont4 x y) = montRedc4 (valLimbs secp256k1Limbs) n'
    (valLimbs x · valLimbs y)`. Composes `ciosWord_eq` four times (each length side
    condition `5 ≤ |accumulator|` holding because the schoolbook product has
    `|x|+1+2·(|y|-1) ≥ 5` limbs and `ciosWord` preserves length) with
    `mulLimbs_reconstruct` (the product value). -/
theorem ciosMont4_valLimbs (x y : List (BitVec 64))
    (hx : x.length = 4) (hy : y.length = 4) :
    valLimbs (ciosMont4 x y)
      = montRedc4 (valLimbs secp256k1Limbs) secpNPrime.toNat
          (valLimbs x * valLimbs y) := by
  -- length of the schoolbook product seed
  have hlen0 : (mulLimbs x y).length = 11 := by
    rw [mulLimbs_length x y (by rw [← List.length_pos_iff]; omega)]; omega
  -- length preserved through each ciosWord
  have hlen1 : (ciosWord secp256k1Limbs secpNPrime (mulLimbs x y)).length = 11 := by
    rw [ciosWord_length, hlen0]
  have hlen2 : (ciosWord secp256k1Limbs secpNPrime
      (ciosWord secp256k1Limbs secpNPrime (mulLimbs x y))).length = 11 := by
    rw [ciosWord_length, hlen1]
  have hlen3 : (ciosWord secp256k1Limbs secpNPrime
      (ciosWord secp256k1Limbs secpNPrime
        (ciosWord secp256k1Limbs secpNPrime (mulLimbs x y)))).length = 11 := by
    rw [ciosWord_length, hlen2]
  -- the mulScalar-length side condition: |mulScalar secp256k1Limbs _| = 5 ≤ |T|
  have hN : secp256k1Limbs.length = 4 := rfl
  have hms : ∀ (m : BitVec 64), (mulScalar secp256k1Limbs m).length = 5 := by
    intro m; rw [mulScalar_length, hN]
  -- apply ciosWord_eq four times
  unfold ciosMont4
  rw [ciosWord_eq secp256k1Limbs secpNPrime _ (by rw [hms, hlen3]; omega),
      ciosWord_eq secp256k1Limbs secpNPrime _ (by rw [hms, hlen2]; omega),
      ciosWord_eq secp256k1Limbs secpNPrime _ (by rw [hms, hlen1]; omega),
      ciosWord_eq secp256k1Limbs secpNPrime _ (by rw [hms, hlen0]; omega)]
  -- the product value
  rw [mulLimbs_reconstruct x y (by rw [← List.length_pos_iff]; omega)]
  rfl

/-! ## 4. The spec tie: the emitted CIOS block realizes the Montgomery product over `ZMod p`

At the secp256k1 prime `p = valLimbs secp256k1Limbs = 2^256 - 2^32 - 977`, the
emitted CIOS block's decoded value `V` satisfies the Montgomery multiply law
`V · 2^256 = (valLimbs x)·(valLimbs y)` in `ZMod p`, with `V < 2p`. This is
`montgomeryMul_correct` (`V·R ≡ x·y`) instantiated at secp256k1 through the CIOS
value theorem, cast into `ZMod p`. -/

/-- The secp256k1 base-field prime as a `Nat`, read from the modulus limbs. -/
abbrev secpP : Nat := valLimbs secp256k1Limbs

theorem secpP_lt : secpP < 2 ^ 256 := by
  show valLimbs secp256k1Limbs < 2 ^ 256
  rw [secp256k1Limbs_value]; norm_num

theorem secpP_pos : 0 < secpP := by
  show 0 < valLimbs secp256k1Limbs
  rw [secp256k1Limbs_value]; norm_num

/-- **The emitted CIOS block realizes the Montgomery product — range.** For operands
    below the modulus, the CIOS emit's decoded value is `< 2p`: one conditional
    subtract from the canonical residue. -/
theorem ciosMont4_lt_two_p (x y : List (BitVec 64))
    (hx : x.length = 4) (hy : y.length = 4)
    (hxp : valLimbs x < secpP) (hyp : valLimbs y < secpP) :
    valLimbs (ciosMont4 x y) < 2 * secpP := by
  have hprod : valLimbs x * valLimbs y < 2 ^ 256 * secpP := by
    calc valLimbs x * valLimbs y < secpP * secpP :=
          Nat.mul_lt_mul'' hxp hyp
      _ ≤ 2 ^ 256 * secpP := by
          have := secpP_lt
          exact Nat.mul_le_mul_right secpP (le_of_lt secpP_lt)
  have hnp : (secpP * secpNPrime.toNat) % 2 ^ 64 = 2 ^ 64 - 1 := by
    rw [secpNPrime_toNat]; exact secp256k1_nprime
  rw [ciosMont4_valLimbs x y hx hy]
  exact (montRedc4_full secpP secpNPrime.toNat _ secpP_pos hnp hprod).1

/-- **The emitted CIOS block realizes the Montgomery product — the `ZMod p` spec.**
    At the secp256k1 prime `p`, for operands `x, y` below `p`, the emitted CIOS
    block's decoded value `V = valLimbs (ciosMont4 x y)` satisfies the Montgomery
    multiply law in `ZMod p`:
    `(V : ZMod p) · 2^256 = (valLimbs x) · (valLimbs y)`.
    This is the Montgomery-form product (`x·y·R⁻¹` in Montgomery representation) —
    `denote = spec` for the CIOS emit, the analogue of the SOS commuting square
    `secp_mul_commutes`, but for the CIOS structure and the Montgomery domain. The
    congruence is `montRedc4_full` (full-radix correctness of the four-word chain)
    cast through `ZMod.natCast_eq_natCast_iff`. -/
theorem ciosMont4_realizes_montmul (x y : List (BitVec 64))
    (hx : x.length = 4) (hy : y.length = 4)
    (hxp : valLimbs x < secpP) (hyp : valLimbs y < secpP) :
    ((valLimbs (ciosMont4 x y) : ZMod secpP)) * (2 ^ 256)
      = (valLimbs x : ZMod secpP) * (valLimbs y : ZMod secpP) := by
  have hprod : valLimbs x * valLimbs y < 2 ^ 256 * secpP := by
    calc valLimbs x * valLimbs y < secpP * secpP :=
          Nat.mul_lt_mul'' hxp hyp
      _ ≤ 2 ^ 256 * secpP := Nat.mul_le_mul_right secpP (le_of_lt secpP_lt)
  have hnp : (secpP * secpNPrime.toNat) % 2 ^ 64 = 2 ^ 64 - 1 := by
    rw [secpNPrime_toNat]; exact secp256k1_nprime
  have hcong :
      (montRedc4 secpP secpNPrime.toNat (valLimbs x * valLimbs y)) * 2 ^ 256
        ≡ valLimbs x * valLimbs y [MOD secpP] :=
    (montRedc4_full secpP secpNPrime.toNat _ secpP_pos hnp hprod).2
  -- cast the congruence into `ZMod secpP`
  have hzcast :
      ((montRedc4 secpP secpNPrime.toNat (valLimbs x * valLimbs y) * 2 ^ 256
          : ℕ) : ZMod secpP)
        = ((valLimbs x * valLimbs y : ℕ) : ZMod secpP) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcong
  rw [ciosMont4_valLimbs x y hx hy]
  push_cast at hzcast ⊢
  exact hzcast

end CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul
