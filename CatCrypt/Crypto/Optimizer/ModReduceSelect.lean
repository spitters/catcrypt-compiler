/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
import Mathlib.Data.BitVec

/-!
# A verified `Com→Com` instruction-selection pass for pseudo-Mersenne / Solinas reduction (#393)

`Fe25519MulKernel.feMulBlock` (#391) reaches s2n parity on the Curve25519
field-multiply by HAND-porting s2n-bignum's *fused-quotient-estimate* reduce for
the single prime `2^255 - 19`. This module turns that one-kernel win into a
**compiler property**: a pass, parametric in the prime shape `p = 2^k - c`, that
*recognises* the modular-reduction step and *emits* the fused reduce
automatically. Instantiating it at `(k = 255, c = 19)` reproduces #391's reduce
semantics; the same pass instantiates at secp256k1 (`2^256 - (2^32 + 977)`),
Poly1305 (`2^130 - 5`), and any pseudo-Mersenne / Solinas prime with small `c`.

## The reduction shape this pass recognises and emits

Let `p = 2^k - c` with `1 ≤ c` (and `c` small relative to `2^k` — the
pseudo-Mersenne / Solinas regime). A field multiply produces a *double-width*
value `V = high · 2^k + low` (`high`, `low` each `< 2^k`). Because
`2^k ≡ c (mod p)`, the high half folds into the low half by a single
constant-multiply:

  `V ≡ high · c + low  (mod p)`.

`fold₁ V = high · c + low` is one fold. The folded value `t = fold₁ V` is small
enough (under the small-`c` side condition) that **one more** fold of its own
top reduces it below `2·p`, after which a single canonical conditional subtract
of `p` lands it in `[0, p)`. This is *exactly* s2n's `bignum_mul_p25519` reduce —
`fold high·38 into low` (`38 = 2·19` because s2n carries the `2^256` split, i.e.
`2·c` at `k = 255`), a quotient estimate `q` from the top, the `c·q` correction
injected in the same carry pass, and one conditional `−p` (cf.
`Fe25519MulKernel.feMulBlock` lines 178–217).

## What is proved here (general) vs concrete-checked (per prime)

* **General, value-level (the contribution).** `solinasReduce k c high low` is the
  Nat-level transcription of the two-fold + conditional-subtract the instruction
  sequence computes. `solinasReduce_eq_mod` proves, **for all** `k`, `c`, `high`,
  `low` under the explicit side condition
  `SolinasOK k c high low` (`1 ≤ c`, `c·(c+3) < 2^k`, `high, low < 2^k`), that
  `solinasReduce k c high low = (high · 2^k + low) % (2^k - c)`. This is the
  value-preservation guarantee of the selection: whatever prime the
  pass fires on, the emitted reduce computes the residue.

* **Concrete, per prime.** `solinasParams25519`, `solinasParamsSecp256k1`,
  `solinasParamsPoly1305` instantiate `(k, c)`; `*_reduce_eq_mod` discharge the
  side condition and specialise the general theorem to each. The
  `(255, 19)`-instantiation is value-identical to the residue #391's `feMulBlock`
  computes (`feMul_reduce_matches`): both equal `(x·y) mod (2^255-19)` on the
  product, so the SELECTED reduce and the HAND reduce agree by value.

* **Emitter shape.** `fusedReduceBlock k c lo hi …` emits the parametric
  `JInstr` reduce (the generalisation of `feMulBlock`'s lines 178–217, with the
  Solinas constant `2·c` and the `c·q` correction parametric). At
  `(255, 19)` it is the #391 reduce sequence; the constants `2·c`/`c` print into
  the body, checked by `fusedReduce25519_constants`.

The honest scope: the *value-level reduction identity* is fully general over
`(k, c)` under the stated side condition; the *instruction-level emission* is the
parametric generalisation of one hand-written block, concrete-checked to
reproduce it at `(255, 19)` and to carry the right Solinas constants at the other
primes. The all-inputs byte-identity of the emitted asm against a reference stays
the external KAT discipline (`bench/x25519_fieldmul_compare`), as for #391.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ModReduceSelect

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The prime shape the pass recognises

`SolinasPrime k c` packages the recognised modulus `p = 2^k - c`. The pass keys
off this shape; the only data it needs to emit the fused reduce is `(k, c)`. -/

/-- A pseudo-Mersenne / Solinas modulus descriptor: the recognised prime is
    `p = 2^k - c`. `k` is the bit width of the radix split (`2^k`), `c` the small
    subtrahend. The pass is parametric in this pair. -/
structure SolinasPrime where
  /-- The radix exponent: the modulus is `2^k - c`. -/
  k : Nat
  /-- The small subtrahend `c` in `p = 2^k - c`. -/
  c : Nat

/-- The modulus `p = 2^k - c` as a `Nat`. -/
def SolinasPrime.modulus (P : SolinasPrime) : Nat := 2 ^ P.k - P.c

/-! ## 2. The side condition for quotient-estimate correctness

The fused reduce folds the high half twice and finishes with one conditional
subtract. For the two-fold + single-subtract to land the residue in `[0, p)`,
`c` must be small enough that after the first fold the value is below
`2^k · (c + 1)` and after the second below `2 · p` (so one conditional `−p`
suffices). Two folds leave `t' < c·(c+1) + 2^k`; the conditional subtract
collapses it to `< p` provided `t' < 2·p = 2^(k+1) − 2c`, i.e.
`c·(c + 3) < 2^k`. This is the clean uniform sufficient condition, well within
reach for every deployed pseudo-Mersenne / Solinas prime:
`19·22 = 418 ≪ 2^255`, `(2^32+977)·(2^32+980) ≪ 2^256`, `5·8 = 40 ≪ 2^130`. We
also need the limbs well-formed (`high, low < 2^k`). -/

/-- The side condition under which the parametric fused reduce is exact: `c ≥ 1`,
    the limbs are below the radix, and `c·(c+3) < 2^k` (the small-`c` Solinas
    regime ensuring two folds leave the value below `2·p`). -/
structure SolinasOK (P : SolinasPrime) (high low : Nat) : Prop where
  /-- `c ≥ 1`, so `2^k - c < 2^k` is a proper modulus. -/
  c_pos : 1 ≤ P.c
  /-- The high limb is below the radix `2^k`. -/
  high_lt : high < 2 ^ P.k
  /-- The low limb is below the radix `2^k`. -/
  low_lt : low < 2 ^ P.k
  /-- The small-`c` regime: `c · (c + 3) < 2^k`, so two folds leave the value
      below `2·p` and one conditional subtract suffices. -/
  cc_lt : P.c * (P.c + 3) < 2 ^ P.k

/-! ## 3. The value-level fused reduce (transcription of the instruction sequence)

`solinasReduce` is the Nat-level arithmetic the emitted instruction sequence
performs. The instruction sequence (`feMulBlock` lines 178–217 generalised) does:

1. `t := high · c + low`            -- fold `high · 2^k ≡ high · c`
2. split `t = th · 2^k + tl`,
   `t' := th · c + tl`              -- fold once more (the quotient-estimate fold)
3. if `t' ≥ p` then `t' - p` else `t'`   -- the single canonical conditional `−p`

We define it directly in this two-fold-then-subtract form; §4 proves it equals
`(high·2^k + low) % p`. -/

/-- One Solinas fold: replace `v = vh · 2^k + vl` by `vh · c + vl`. Since
    `2^k ≡ c (mod p)`, this preserves the residue mod `p`. -/
def solinasFold (P : SolinasPrime) (v : Nat) : Nat :=
  (v / 2 ^ P.k) * P.c + v % 2 ^ P.k

/-- The value-level fused reduce: two folds (the high-half fold and the
    quotient-estimate fold of `feMulBlock`'s reduce) followed by one canonical
    conditional subtract of `p`. This is the arithmetic the emitted instruction
    sequence computes. -/
def solinasReduce (P : SolinasPrime) (high low : Nat) : Nat :=
  let t := solinasFold P (high * 2 ^ P.k + low)   -- = high·c + low
  let t' := solinasFold P t                        -- the second (quotient) fold
  if t' < P.modulus then t' else t' - P.modulus

/-! ## 4. Correctness: the fused reduce computes the residue (general over `(k,c)`)

The contribution. Each `solinasFold` preserves the residue mod `p` (it rewrites
`2^k` by `c`), and under `SolinasOK` two folds bring the value below `2·p`, so the
final conditional subtract lands it in `[0, p)`. -/

/-- `2^k ≡ c (mod p)` for `p = 2^k - c` with `c ≤ 2^k`: the defining congruence
    the fold exploits. -/
theorem two_pow_k_mod (P : SolinasPrime) (hc : P.c ≤ 2 ^ P.k) :
    (2 ^ P.k) % P.modulus = P.c % P.modulus := by
  have heq : (2 : Nat) ^ P.k = P.modulus + P.c := by
    simp only [SolinasPrime.modulus]; omega
  rw [heq, Nat.add_mod_left]

/-- A fold preserves the residue mod `p`: `solinasFold v ≡ v (mod p)`. This is
    the core algebraic fact `(vh·2^k + vl) ≡ vh·c + vl (mod p)`. -/
theorem solinasFold_mod (P : SolinasPrime) (hc : P.c ≤ 2 ^ P.k) (v : Nat) :
    solinasFold P v % P.modulus = v % P.modulus := by
  have hsplit : v = (v / 2 ^ P.k) * 2 ^ P.k + v % 2 ^ P.k := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod v _).symm
  conv_rhs => rw [hsplit]
  simp only [solinasFold]
  -- `(q·2^k + r) % p = (q·c + r) % p` because `2^k ≡ c (mod p)`.
  conv_rhs =>
    rw [Nat.add_mod, Nat.mul_mod, two_pow_k_mod P hc, ← Nat.mul_mod, ← Nat.add_mod]

/-! ### Bounding the folded value

Under `SolinasOK`, the first fold of the full product is below `2^k · (c + 1)`,
the second fold is below `2·2^k`, hence below `2·p + 2·c`, and (because the value
is also `≥ 0` and the residue is preserved) the single conditional subtract
suffices. We bound `solinasFold P t < 2 ^ k + ...` and conclude `t' < 2 · p` via
the small-`c` condition. -/

/-- After one fold of a value `v < 2^k · M`, the result is below `M · c + 2^k`
    (the high part `< M` times `c`, plus a residue `< 2^k`). -/
theorem solinasFold_lt (P : SolinasPrime) {v M : Nat} (hM : v < 2 ^ P.k * M) :
    solinasFold P v < M * P.c + 2 ^ P.k := by
  have hk : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  simp only [solinasFold]
  have hq : v / 2 ^ P.k < M := by
    rw [Nat.div_lt_iff_lt_mul hk]; rwa [Nat.mul_comm] at hM
  have hr : v % 2 ^ P.k < 2 ^ P.k := Nat.mod_lt _ hk
  calc (v / 2 ^ P.k) * P.c + v % 2 ^ P.k
      ≤ (M - 1) * P.c + v % 2 ^ P.k := by
        have : v / 2 ^ P.k ≤ M - 1 := by omega
        exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) _
    _ < M * P.c + 2 ^ P.k := by
        have hMc : (M - 1) * P.c ≤ M * P.c := Nat.mul_le_mul_right _ (by omega)
        omega

/-- **Fused-reduce correctness (general over `(k, c)`).** Under the small-`c`
    side condition `SolinasOK`, the two-fold + conditional-subtract `solinasReduce`
    computes the canonical residue: `solinasReduce k c high low =
    (high · 2^k + low) mod (2^k - c)`. This is the value-preservation guarantee of
    the instruction-selection pass — independent of which Solinas prime it fires
    on. -/
theorem solinasReduce_eq_mod (P : SolinasPrime) {high low : Nat}
    (h : SolinasOK P high low) :
    solinasReduce P high low = (high * 2 ^ P.k + low) % P.modulus := by
  have hk : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  -- c·(c+3) < 2^k gives c < 2^k and c ≤ 2^k.
  have hc_lt : P.c < 2 ^ P.k :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) h.cc_lt
  have hc_le : P.c ≤ 2 ^ P.k := le_of_lt hc_lt
  have hp_pos : 0 < P.modulus := by
    simp only [SolinasPrime.modulus]; omega
  -- The two folds preserve the residue.
  set t := solinasFold P (high * 2 ^ P.k + low) with ht
  set t' := solinasFold P t with ht'
  have hmod : t' % P.modulus = (high * 2 ^ P.k + low) % P.modulus := by
    rw [ht', solinasFold_mod P hc_le, ht, solinasFold_mod P hc_le]
  -- Bound t': first fold of a value < 2^k·(high+1) gives t < (high+1)·c + 2^k.
  have hV : high * 2 ^ P.k + low < 2 ^ P.k * (high + 1) := by
    have : low < 2 ^ P.k := h.low_lt
    calc high * 2 ^ P.k + low < high * 2 ^ P.k + 2 ^ P.k := by omega
      _ = 2 ^ P.k * (high + 1) := by ring
  have ht_lt : t < (high + 1) * P.c + 2 ^ P.k := by
    rw [ht]; exact solinasFold_lt P hV
  -- high + 1 ≤ 2^k, so t < 2^k·(c+1).
  have htM : t < 2 ^ P.k * (P.c + 1) := by
    have hh1 : high + 1 ≤ 2 ^ P.k := by have := h.high_lt; omega
    have : (high + 1) * P.c ≤ 2 ^ P.k * P.c := Nat.mul_le_mul_right _ hh1
    calc t < (high + 1) * P.c + 2 ^ P.k := ht_lt
      _ ≤ 2 ^ P.k * P.c + 2 ^ P.k := by omega
      _ = 2 ^ P.k * (P.c + 1) := by ring
  -- the second fold of t < 2^k·(c+1) gives t' < (c+1)·c + 2^k.
  have ht'_lt : t' < (P.c + 1) * P.c + 2 ^ P.k := by
    rw [ht']; exact solinasFold_lt P htM
  -- (c+1)·c + 2^k = c·c + c + 2^k.  Need t' < 2·p = 2^(k+1) - 2c, i.e. c·c + 3c < 2^k.
  have hcc : P.c * (P.c + 3) < 2 ^ P.k := h.cc_lt
  have ht'_2p : t' < 2 * P.modulus := by
    simp only [SolinasPrime.modulus]
    have hexp : (P.c + 1) * P.c + 2 ^ P.k = P.c * (P.c + 3) + 2 ^ P.k - 2 * P.c := by
      have : P.c * (P.c + 3) = (P.c + 1) * P.c + 2 * P.c := by ring
      omega
    -- 2·(2^k - c) = 2·2^k - 2c.  From c·(c+3) < 2^k: (c+1)·c + 2^k < 2·2^k - 2c.
    have key : (P.c + 1) * P.c + 2 ^ P.k < 2 * (2 ^ P.k - P.c) := by
      have hexpand : P.c * (P.c + 3) = (P.c + 1) * P.c + 2 * P.c := by ring
      have : (P.c + 1) * P.c + 2 * P.c < 2 ^ P.k := by rw [← hexpand]; exact hcc
      omega
    omega
  -- Conclude: t' < 2p and t' ≡ V (mod p), so the conditional subtract gives V mod p.
  simp only [solinasReduce, ← ht, ← ht']
  by_cases hlt : t' < P.modulus
  · rw [if_pos hlt]
    rw [← hmod, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hlt]
    have hlt : P.modulus ≤ t' := Nat.le_of_not_lt hlt
    have h1 : t' - P.modulus < P.modulus := by omega
    rw [← hmod]
    rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt h1]

/-! ## 5. Per-prime instantiations

The same pass, instantiated at the deployed Solinas primes. Each discharges the
`SolinasOK` side condition (the `c·(c+3) < 2^k` numeric check) and specialises
`solinasReduce_eq_mod`. -/

/-- Curve25519 / Ed25519: `p = 2^255 - 19`. -/
def solinasParams25519 : SolinasPrime := { k := 255, c := 19 }

/-- secp256k1 (Bitcoin's curve base field): `p = 2^256 - (2^32 + 977)`. -/
def solinasParamsSecp256k1 : SolinasPrime := { k := 256, c := 2 ^ 32 + 977 }

/-- Poly1305: `p = 2^130 - 5`. -/
def solinasParamsPoly1305 : SolinasPrime := { k := 130, c := 5 }

/-- The pass at `(255, 19)` computes the Curve25519 residue: for any well-formed
    limbs `high, low < 2^255`, `solinasReduce` equals `(high·2^255 + low) mod
    (2^255 - 19)`. -/
theorem reduce25519_eq_mod {high low : Nat}
    (hh : high < 2 ^ 255) (hl : low < 2 ^ 255) :
    solinasReduce solinasParams25519 high low
      = (high * 2 ^ 255 + low) % (2 ^ 255 - 19) :=
  solinasReduce_eq_mod solinasParams25519
    { c_pos := by norm_num [solinasParams25519]
      high_lt := hh
      low_lt := hl
      cc_lt := by
        show 19 * (19 + 3) < 2 ^ 255
        have h9 : (2 : Nat) ^ 9 ≤ 2 ^ 255 :=
          Nat.pow_le_pow_right (Nat.zero_lt_two) (by omega)
        have e9 : (2 : Nat) ^ 9 = 512 := by norm_num
        omega }

/-- The pass at secp256k1 `(256, 2^32 + 977)` computes the secp256k1 residue. -/
theorem reduceSecp256k1_eq_mod {high low : Nat}
    (hh : high < 2 ^ 256) (hl : low < 2 ^ 256) :
    solinasReduce solinasParamsSecp256k1 high low
      = (high * 2 ^ 256 + low) % (2 ^ 256 - (2 ^ 32 + 977)) :=
  solinasReduce_eq_mod solinasParamsSecp256k1
    { c_pos := by norm_num [solinasParamsSecp256k1]
      high_lt := hh
      low_lt := hl
      cc_lt := by
        show (2 ^ 32 + 977) * ((2 ^ 32 + 977) + 3) < 2 ^ 256
        have e32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
        have e33 : (2 : Nat) ^ 33 = 8589934592 := by norm_num
        have h1 : (2 : Nat) ^ 32 + 977 < 2 ^ 33 := by omega
        have h2 : (2 : Nat) ^ 32 + 977 + 3 < 2 ^ 33 := by omega
        calc (2 ^ 32 + 977) * ((2 ^ 32 + 977) + 3)
            < 2 ^ 33 * 2 ^ 33 := Nat.mul_lt_mul'' h1 h2
          _ = 2 ^ 66 := by ring
          _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (Nat.zero_lt_two) (by omega) }

/-- The pass at Poly1305 `(130, 5)` computes the Poly1305 residue. -/
theorem reducePoly1305_eq_mod {high low : Nat}
    (hh : high < 2 ^ 130) (hl : low < 2 ^ 130) :
    solinasReduce solinasParamsPoly1305 high low
      = (high * 2 ^ 130 + low) % (2 ^ 130 - 5) :=
  solinasReduce_eq_mod solinasParamsPoly1305
    { c_pos := by norm_num [solinasParamsPoly1305]
      high_lt := hh
      low_lt := hl
      cc_lt := by
        show 5 * (5 + 3) < 2 ^ 130
        have h6 : (2 : Nat) ^ 6 ≤ 2 ^ 130 :=
          Nat.pow_le_pow_right (Nat.zero_lt_two) (by omega)
        have e6 : (2 : Nat) ^ 6 = 64 := by norm_num
        omega }

/-! ## 6. Validation against the #391 hand-written reduce

`Fe25519MulKernel.feMulComputes` (#391) asserts the hand-written `feMulBlock`'s
stored output equals `(x·y) mod p25519`. The pass at `(255, 19)` targets the
**same residue**: `solinasReduce solinasParams25519 high low` reduces
`high·2^255 + low` to `… mod (2^255 - 19)`, and `Fe25519MulKernel.p25519` is
*definitionally* `2^255 - 19`. So whenever the double-width product is presented
as `high·2^255 + low` (the radix split the reduce consumes), the SELECTED reduce
and the HAND reduce land on the identical canonical residue — the selection
reproduces #391's value semantics. -/

/-- The modulus the pass uses at `(255, 19)` is *definitionally* the prime
    `Fe25519MulKernel.p25519` the #391 hand reduce targets. -/
theorem modulus25519_eq_p25519 :
    solinasParams25519.modulus
      = CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.p25519 := rfl

/-- **The selected reduce reproduces #391's reduce by value.** For any
    `high, low < 2^255`, the automatically-selected `(255, 19)` fused reduce
    computes exactly the canonical residue `(high·2^255 + low) mod p25519` that
    `Fe25519MulKernel.feMulBlock`'s hand-written reduce produces — they agree on
    every input presented in the radix split. The selection is now a compiler
    property, not a hand decision. -/
theorem feMul_reduce_matches {high low : Nat}
    (hh : high < 2 ^ 255) (hl : low < 2 ^ 255) :
    solinasReduce solinasParams25519 high low
      = (high * 2 ^ 255 + low)
          % CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.p25519 := by
  rw [← modulus25519_eq_p25519]
  simpa [solinasParams25519, SolinasPrime.modulus] using reduce25519_eq_mod hh hl

/-! ## 7. The parametric instruction emitter (the selection, at the `JInstr` level)

`fusedReduce4LimbBlock twoC c` emits the fused-quotient-estimate reduce for a
4-limb / `k = 255`-style layout, **parametric** in the two prime-dependent
immediates: `twoC` (the Solinas fold constant `2·c`, the `38` in s2n's
`bignum_mul_p25519`) and `c` (the quotient correction `19`). The four-limb radix
mechanics (`shr/shl` by `63`/`1`, the `clear bit 255` mask, the limb offsets) are
structural to the `k = 255`, 4×64 layout and stay fixed; the Solinas constants
are what the pass substitutes per prime.

This is the literal generalisation of `Fe25519MulKernel.feMulBlock` lines
178–217: at `(twoC, c) = (38, 19)` it reproduces that hand-written reduce
instruction-for-instruction (`fusedReduce_at_25519_eq_feMulReduce`). For a
different `k`-or-limb-count prime the emitter carries a different structural
skeleton. This `2^255`-class layout covers Curve25519 and Ed25519 (same
`2^255 - 19` field). The `2^256`-boundary primes (secp256k1, `2^256 - c`) use a
*distinct* reduce skeleton — `fusedReduce4LimbBlock256` in §8.1 — with a clean
256-bit split and a `cmovc`-gated correction instead of the bit-255 fold/mask.
Poly1305's `2^130 - 5` is not a 4×64 block at all (the fold boundary `2^130` is
not 64-bit-aligned), so it has the value-level `solinasReduce` correctness
(`reducePoly1305_eq_mod`) but *no* 4-limb instruction emitter here; a Poly1305
kernel uses a `2^26×5`/`2^44×3` radix, a separate emitter. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)

/-- The parametric fused-quotient-estimate reduce for the 4-limb / `k = 255`
    layout, with the Solinas fold constant `twoC = 2·c` and the quotient
    correction `c` as parameters. The product low half is `t0..t3`, high half
    `t4..t7`; scratch `lo`/`hi`/`y`; zero register `zr`; result pointer `z`. The
    body is `feMulBlock`'s lines 178–217 with `38 ↦ twoC` and `19 ↦ c`. -/
def fusedReduce4LimbBlock (twoC c : Nat) : List (JInstr 64) :=
  [ .mov "yd" (.imm twoC)
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .add "lo" (.reg "t3")
  , .adc "hi" (.reg "zr")
  , .mov "y" (.reg "lo")
  , .shr "y" (.imm 63)
  , .shl "hi" (.imm 1)
  , .add "hi" (.reg "y")
  , .add "hi" (.imm 1)
  , .mov "y" (.reg "hi")
  , .imul "hi" (.imm c)
  , .xor_ "zr" (.reg "zr")
  , .adox "t0" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t4")
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t5")
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t6")
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .adc "t3" (.reg "lo")
  , .shl "y" (.imm 63)
  , .mov "lo" (.reg "t3")
  , .sub "lo" (.reg "y")
  , .shr "lo" (.imm 63)
  , .imul "lo" (.imm c)
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

/-- The `(255, 19)` instantiation: the pass fed Curve25519's Solinas constants
    (`twoC = 2·19 = 38`, `c = 19`). -/
def fusedReduce25519 : List (JInstr 64) :=
  fusedReduce4LimbBlock (2 * solinasParams25519.c) solinasParams25519.c

/-- The reduce tail of the #391 hand-written `feMulBlock`: its last 38
    instructions (lines 178–217), the fused-quotient-estimate reduce. -/
def feMulReduceTail : List (JInstr 64) :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock.drop 56

/-- **The selected reduce is the #391 reduce (instruction-level).** The pass,
    instantiated at Curve25519's `(twoC, c) = (38, 19)`, emits *exactly* the
    instruction sequence the #391 hand reduce uses (`feMulBlock`'s reduce tail) —
    instruction for instruction. The hand instruction-selection decision is now
    reproduced by the parametric pass. -/
theorem fusedReduce_at_25519_eq_feMulReduce :
    fusedReduce25519 = feMulReduceTail := rfl

/-- The emitted reduce carries the Solinas constants the pass substitutes: at
    Curve25519 the fold constant `2·c = 38` (the first `mov yd, $imm`) and the
    quotient correction `c = 19` (the two `imul $imm`, at positions 10 and 28). -/
theorem fusedReduce25519_constants :
    (fusedReduce25519.head? = some (.mov "yd" (.imm 38)))
      ∧ fusedReduce25519[10]? = some (.imul "hi" (.imm 19))
      ∧ fusedReduce25519[28]? = some (.imul "lo" (.imm 19)) :=
  ⟨rfl, rfl, rfl⟩

/-- Instantiating the emitter at secp256k1's Solinas constants substitutes the
    matching fold constant `2·c` (the first `mov`) — the same emitter, a
    different prime's constant. (The 4-limb structural skeleton is shared with
    the `2^256`-class layout; the per-prime data is the constant.) -/
theorem fusedReduceSecp256k1_constant :
    (fusedReduce4LimbBlock (2 * solinasParamsSecp256k1.c)
        solinasParamsSecp256k1.c).head?
      = some (.mov "yd" (.imm (2 * (2 ^ 32 + 977)))) := rfl

/-! ## 8. Wiring the selected reduce into the emit path (#397)

§7 proves the *reduce tail* the pass emits is the #391 hand reduce. To make the
selection actually drive code-gen, we split `feMulBlock` into its schoolbook
prefix (the 4×4→8 product, the first 56 instructions) and let the pass supply the
reduce, then re-assemble. `feMul25519Schoolbook ++ fusedReduce25519` is then
*byte-identical* to the hand-written `feMulBlock` — the field-multiply kernel is
now `schoolbook ++ (selected reduce)` rather than `schoolbook ++ (hand reduce)`,
and the emit driver renders this composed block. -/

/-- The schoolbook prefix of `feMulBlock`: the 4×4→8 dual-carry-chain product
    that leaves the eight product words register-resident in `t0..t7`. This is the
    `2^255`-class field-mul's multiply half; the reduce half is supplied by the
    pass. -/
def feMul25519Schoolbook : List (JInstr 64) :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock.take 56

/-- The **selected** Curve25519 field-multiply: schoolbook prefix composed with
    the reduce the pass emits at `(255, 19)`. This is what the emit path renders. -/
def selectedFeMul25519 : List (JInstr 64) :=
  feMul25519Schoolbook ++ fusedReduce25519

/-- **The composed (schoolbook ++ selected-reduce) kernel is byte-identical to the
    #391 hand `feMulBlock`.** Splitting the kernel and letting the pass supply the
    reduce reproduces the hand block instruction-for-instruction, so wiring the
    pass into emit does not change the emitted Curve25519 field-multiply — the
    fe25519 (255,19) KAT and s2n parity are preserved by construction. -/
theorem selectedFeMul25519_eq_feMulBlock :
    selectedFeMul25519
      = CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.feMulBlock := by
  rfl

/-- **A generic `2^255`-class field-multiply kernel constructor.** Given the
    Curve25519-style schoolbook prefix and a `SolinasPrime` whose reduce fits the
    4-limb / `k = 255` layout (high half spilling into bit 255), emit
    `schoolbook ++ fusedReduce4LimbBlock (2·c) c`. At `solinasParams25519` this is
    `selectedFeMul25519`. The `2^256`-boundary primes (secp256k1) do NOT fit this
    constructor — their reduce uses a clean 256-bit split with no bit-255 mask
    (see the module note); they need a `2^256`-class reduce skeleton, a follow-on
    to this emitter. -/
def fieldMul255Kernel (schoolbook : List (JInstr 64)) (P : SolinasPrime) :
    List (JInstr 64) :=
  schoolbook ++ fusedReduce4LimbBlock (2 * P.c) P.c

/-- The generic constructor at Curve25519's prime is the selected kernel. -/
theorem fieldMul255Kernel_at_25519 :
    fieldMul255Kernel feMul25519Schoolbook solinasParams25519 = selectedFeMul25519 := rfl

/-! ### 8.1 The `2^256`-boundary reduce skeleton (secp256k1, #397)

secp256k1's prime `p = 2^256 - c` (`c = 2^32 + 977 = 4294968273`) sits on a *clean
2^256 boundary*, so its reduce differs structurally from the `2^255`-class
`fusedReduce4LimbBlock`: there is no bit-255 fold (`shr 63`/`shl 1`) and no
`clear bit 255` mask. The s2n-bignum reference (`bignum_mul_p256k1.S`) folds
`c·h + l` once into five digits, takes the quotient estimate `q = h + 1`, injects
`c·q`, then does a single `cmovc`-gated conditional subtract of `c`. This emitter
is the parametric transcription of that reference, with `c` the prime data.

The four-limb radix mechanics (the dual-carry fold, the `q = h + 1` estimate, the
`cmovc` correction) are structural to the `2^256`, 4×64 layout; `c` is what the
pass substitutes per `2^256 - c` prime. This is the value-level-general
`solinasReduce`'s instruction realisation for the `2^256` boundary — a distinct
skeleton from the `2^255` one, sharing the value-level correctness theorem
(`reduceSecp256k1_eq_mod`). Register roles mirror s2n's: `lo`≡rax, `hi`≡rbx,
`y` holds the quotient `q`, `zr` the zero register, `yd` (=%rdx) the `MULX`
multiplier. Input: product low half `t0..t3`, high half `t4..t7`; result `z`. -/
def fusedReduce4LimbBlock256 (c : Nat) : List (JInstr 64) :=
  [ .mov "yd" (.imm c)
  , .xor_ "zr" (.reg "zr")
    -- fold c·h into l: dual ADCX/ADOX, last digit lands fresh in t4
  , .mulx "hi" "lo" (.reg "yd") (.reg "t4")
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t5")
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t6")
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulx "t4" "lo" (.reg "yd") (.reg "t7")     -- (lo, t4) = c·h₃
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "zr")
  , .adcx "t4" (.reg "zr")                        -- 5-digit result, top in t4
    -- quotient estimate q = t4 + 1
  , .mov "y" (.reg "t4")
  , .add "y" (.imm 1)                             -- y = q
  , .mulx "hi" "lo" (.reg "yd") (.reg "y")        -- (lo, hi) = c·q
  , .add "t0" (.reg "lo")
  , .adc "t1" (.reg "hi")
  , .adc "t2" (.reg "zr")
  , .adc "t3" (.reg "zr")                          -- CF = 1 iff estimate exact
    -- correct if CF = 0: subtract c (cmovc keeps c when CF=1, else amount 0)
  , .cmovb "yd" (.reg "zr")                        -- yd := (CF ? 0 : c)
  , .sub "t0" (.reg "yd")
  , .sbb "t1" (.reg "zr")
  , .sbb "t2" (.reg "zr")
  , .sbb "t3" (.reg "zr")
  , .storeMem "z" 0 (.reg "t0")
  , .storeMem "z" 8 (.reg "t1")
  , .storeMem "z" 16 (.reg "t2")
  , .storeMem "z" 24 (.reg "t3") ]

/-- The secp256k1 `(256, 2^32+977)` instantiation of the `2^256` reduce skeleton. -/
def fusedReduceSecp256k1 : List (JInstr 64) :=
  fusedReduce4LimbBlock256 solinasParamsSecp256k1.c

/-- The secp256k1 reduce carries the prime's fold constant
    `c = 2^32 + 977 = 4294968273` in the leading `mov` — the same emitter, the
    secp256k1 prime's `c`. -/
theorem fusedReduceSecp256k1_constant_256 :
    fusedReduceSecp256k1.head? = some (.mov "yd" (.imm 4294968273)) := rfl

/-- The schoolbook prefix is shared with the `2^255` kernel — it computes the same
    `4×4→8` product. The secp256k1 field-multiply is that schoolbook composed with
    the `2^256` reduce skeleton at secp256k1's `c`. -/
def selectedFeMulSecp256k1 : List (JInstr 64) :=
  feMul25519Schoolbook ++ fusedReduceSecp256k1

/-! ## 9. Emit driver for the selected kernel

The emit path renders the *composed* `schoolbook ++ (selected reduce)` block
through the same backend (`allocGp`/`renderLeafFn`) the #391 kernel uses, with the
identical register pinning. Because `selectedFeMul25519_eq_feMulBlock` holds by
`rfl`, this produces a byte-identical `.s` to `Fe25519MulKernel.emitMain`; the
pass now *supplies* the reduce instead of it being hand-inlined. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn regOf)

/-- Register pinning, identical to `Fe25519MulKernel.feMulPinned`. -/
def selectedFeMulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("zr", "%rbp")]

/-- First-fit allocation over the composed (schoolbook ++ selected-reduce) block. -/
def selectedFeMulAlloc : GpAlloc := allocGp selectedFeMulPinned selectedFeMul25519

/-- The rendered AT&T body of the selected kernel. -/
def selectedFeMulAsmBody : List String :=
  renderBlockBody selectedFeMulAlloc selectedFeMul25519

/-- The full emitted leaf for the pass-selected Curve25519 field-multiply. -/
def selectedFeMulAsm : String :=
  renderLeafFn "fe25519_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14"
    , "\tpushq %r15", "\tpushq %rbp"
    , "\tmovq %rdx, " ++ regOf selectedFeMulAlloc "y" ]
    selectedFeMulAsmBody
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the pass-selected Curve25519 field-multiply `.s`. The body
    is `schoolbook ++ fusedReduce25519` — the reduce is supplied by the pass. -/
def emitSelected25519 : IO Unit := do
  IO.FS.createDirAll "bench/x25519_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_fieldmul_compare/gen_com/fe25519_mul_x86_from_lean.s" selectedFeMulAsm
  IO.println "wrote gen_com/fe25519_mul_x86_from_lean.s (pass-selected reduce, #397)"

/-- First-fit allocation over the secp256k1 (schoolbook ++ `2^256`-reduce) block. -/
def selectedSecp256k1Alloc : GpAlloc := allocGp selectedFeMulPinned selectedFeMulSecp256k1

/-- The full emitted leaf for the pass-selected secp256k1 field-multiply. -/
def selectedSecp256k1Asm : String :=
  renderLeafFn "secp256k1_fe_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14"
    , "\tpushq %r15", "\tpushq %rbp"
    , "\tmovq %rdx, " ++ regOf selectedSecp256k1Alloc "y" ]
    (renderBlockBody selectedSecp256k1Alloc selectedFeMulSecp256k1)
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the pass-selected secp256k1 field-multiply `.s`. The body
    is `schoolbook ++ fusedReduce4LimbBlock256 c` for `c = 2^32 + 977`. -/
def emitSelectedSecp256k1 : IO Unit := do
  IO.FS.createDirAll "bench/secp256k1_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/secp256k1_fieldmul_compare/gen_com/secp256k1_fe_mul_x86_from_lean.s"
    selectedSecp256k1Asm
  IO.println "wrote secp256k1_fe_mul_x86_from_lean.s (pass-selected 2^256 reduce, #397)"

/-! ## 10. Multi-term Solinas primes (#403): the iterated-fold generalisation

The single-fold `solinasReduce` (§3–4) is exact only in the *small-`c`* regime
`c·(c+3) < 2^k` (two folds reach `< 2·p`). The NIST curves are **multi-term**
Solinas primes whose subtrahend `c` is *large* — of order `2^{k-32}` — so two
folds do **not** suffice:

* **P-256**: `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, i.e. `c = 2^224 − 2^192 − 2^96 + 1 ≈ 2^224`.
* **P-384**: `p = 2^384 − 2^128 − 2^96 + 2^32 − 1`, i.e. `c = 2^128 + 2^96 − 2^32 + 1 ≈ 2^128`.

For such `c`, `c·(c+3) ≈ 2^{2·224} ≫ 2^256`, so `SolinasOK` fails. The fix is the
classic Solinas approach s2n-bignum's `bignum_mod_p256` uses: fold the high half
**repeatedly**. Each fold `v ↦ (v/2^k)·c + v%2^k` (i) preserves the residue mod
`p` (the fact `solinasFold_mod`, needs only `c ≤ 2^k`), and (ii) when `c < 2^k`
*shrinks* the value: a value `< 2^k·M` folds to `< M·(c/2^k)·2^k + 2^k`, i.e. the
"number of high digits" `M` is scaled by `c/2^k < 1`. After enough folds the
value is below `2^{k+1}`, where a single conditional subtract of `p` finishes
(because `c < p`, so `2^{k+1} − p = p + 2c < 3p`, and in fact `< 2p` once
`2c < p`, giving one subtract).

This section generalises to **any** `p = 2^k − c` with `0 < c` and `2c < 2^k`
(equivalently `c < p`, the only constraint a genuine modulus imposes), proving
`multiSolinasReduce` computes the residue, with the per-prime fold count `fuel`
the single explicit numeric parameter. P-256 and P-384 are instantiated and
their side conditions discharged. -/

/-- A multi-term Solinas modulus, recorded as `p = 2^k − c` together with the
    signed-power decomposition of `c` for documentation/emission. The value-level
    reduction depends only on the net subtrahend `c`; the `terms` list (each entry
    `(sign, exponent)`, `sign = true` for `+2^e`, `false` for `−2^e`) records the
    Solinas shape the instruction-level reduce would walk. -/
structure MultiSolinasPrime where
  /-- The radix exponent: modulus is `2^k − c`. -/
  k : Nat
  /-- The net subtrahend `c` (its value; may be large, of order `2^{k-32}`). -/
  c : Nat
  /-- Number of high-half folds needed to reach `< 2^{k+1}` (the per-prime fuel). -/
  fuel : Nat
  /-- The signed-power decomposition of `c` (documentation / emitter shape). -/
  terms : List (Bool × Nat) := []

/-- The modulus `p = 2^k − c`. -/
def MultiSolinasPrime.modulus (P : MultiSolinasPrime) : Nat := 2 ^ P.k - P.c

/-- The single-term descriptor `SolinasPrime` from §1 underlying a
    `MultiSolinasPrime` (same `k`, `c`); lets us reuse `solinasFold`/`solinasFold_mod`. -/
def MultiSolinasPrime.toSolinas (P : MultiSolinasPrime) : SolinasPrime :=
  { k := P.k, c := P.c }

@[simp] theorem MultiSolinasPrime.toSolinas_k (P : MultiSolinasPrime) :
    P.toSolinas.k = P.k := rfl
@[simp] theorem MultiSolinasPrime.toSolinas_c (P : MultiSolinasPrime) :
    P.toSolinas.c = P.c := rfl
@[simp] theorem MultiSolinasPrime.toSolinas_modulus (P : MultiSolinasPrime) :
    P.toSolinas.modulus = P.modulus := rfl

/-- `n`-fold iteration of `solinasFold` (fold the *result*, so the magnitude
    bound composes cleanly). -/
def multiFold (P : MultiSolinasPrime) : Nat → Nat → Nat
  | 0,        v => v
  | (n + 1),  v => solinasFold P.toSolinas (multiFold P n v)

/-- One canonical conditional subtract of `p`. -/
def condSub (P : MultiSolinasPrime) (t : Nat) : Nat :=
  if t < P.modulus then t else t - P.modulus

/-- `condSub` preserves the residue mod `p` and, on a value `< 2·p`, lands in
    `[0, p)`. -/
theorem condSub_lt_of_lt_two_mul (P : MultiSolinasPrime) {t : Nat}
    (ht : t < 2 * P.modulus) : condSub P t < P.modulus := by
  unfold condSub
  split <;> omega

/-- `condSub` decreases a value by at most `p` and preserves the residue: if
    `p ≤ t` it subtracts `p`, else leaves `t`; either way `condSub P t ≡ t`. -/
theorem condSub_mod (P : MultiSolinasPrime) (t : Nat) :
    condSub P t % P.modulus = t % P.modulus := by
  unfold condSub
  split
  · rfl
  · next h => rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt h)]

/-- `condSub` lowers a value below `t − p + p`... concretely, on `t < B` with
    `p ≤ B`, `condSub P t < B − p` when `p ≤ t`, and `< p` when `t < p`; we use
    the combined bound `condSub P t < max p (B − p)` — here packaged as: if
    `t < B` then `condSub P t < B - P.modulus ∨ condSub P t < P.modulus`. -/
theorem condSub_drop (P : MultiSolinasPrime) {t B : Nat}
    (ht : t < B) : condSub P t < P.modulus ∨ condSub P t < B - P.modulus := by
  unfold condSub
  split
  · next h => exact Or.inl h
  · next h => exact Or.inr (by omega)

/-- The multi-term reduce: fold the high half `fuel` times (each fold preserves
    the residue mod `p` and shrinks the value while `c < 2^k`), then **two**
    canonical conditional subtracts of `p` (the folded value is `< 2^{k+1}`, so up
    to two subtracts land it in `[0, p)`). -/
def multiSolinasReduce (P : MultiSolinasPrime) (high low : Nat) : Nat :=
  condSub P (condSub P (multiFold P P.fuel (high * 2 ^ P.k + low)))

/-- Each fold preserves the residue, so any number of folds does. -/
theorem multiFold_mod (P : MultiSolinasPrime) (hc : P.c ≤ 2 ^ P.k)
    (n v : Nat) : multiFold P n v % P.modulus = v % P.modulus := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [multiFold]
    have hstep := solinasFold_mod P.toSolinas (by simpa using hc) (multiFold P n v)
    rw [show P.toSolinas.modulus = P.modulus from rfl] at hstep
    rw [hstep, ih]

/-- One fold of a value `v < 2^k · M` lands below `M · c + 2^k` (reuses
    `solinasFold_lt`). -/
theorem multiFold_one_lt (P : MultiSolinasPrime) {v M : Nat}
    (hM : v < 2 ^ P.k * M) :
    solinasFold P.toSolinas v < M * P.c + 2 ^ P.k := by
  have := solinasFold_lt P.toSolinas (v := v) (M := M) (by simpa using hM)
  simpa using this

/-- Tighter one-fold bound: the high part of `v < 2^k·M` is `≤ M−1`, so
    `fold v < (M−1)·c + 2^k`. (For `M = 0` the hypothesis is vacuous.) -/
theorem multiFold_one_lt' (P : MultiSolinasPrime) {v M : Nat}
    (hM : v < 2 ^ P.k * M) :
    solinasFold P.toSolinas v < (M - 1) * P.c + 2 ^ P.k := by
  have hk : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  simp only [solinasFold, MultiSolinasPrime.toSolinas_k, MultiSolinasPrime.toSolinas_c]
  have hq : v / 2 ^ P.k ≤ M - 1 := by
    have hqM : v / 2 ^ P.k < M := by
      rw [Nat.div_lt_iff_lt_mul hk, Nat.mul_comm]; exact hM
    omega
  have hr : v % 2 ^ P.k < 2 ^ P.k := Nat.mod_lt _ hk
  have : (v / 2 ^ P.k) * P.c ≤ (M - 1) * P.c := Nat.mul_le_mul_right _ hq
  omega

/-! ### Magnitude bookkeeping for the iterated fold

We track an explicit "high-digit count" `boundM P n` with the invariant
`multiFold P n V < 2^k · boundM P n` for `V = high·2^k + low < 2^{2k}`. The
recurrence `boundM P (n+1) = (boundM P n · c)/2^k + 2` mirrors the fold's
magnitude scaling by `c/2^k < 1`. The side condition `MultiSolinasOK` asks
`boundM P fuel ≤ 1` (so the folded value is `< 2·2^k = 2^{k+1}`) — a single
numeric check, decidable per prime. -/

/-- High-digit-count bound: `boundM P 0 = 2^k` (since `V < 2^k·2^k`),
    `boundM P (n+1) = ((boundM P n − 1) · c)/2^k + 2`. The `−1` tightening (the
    high part of a value `< 2^k·M` is `≤ M−1`) plus the `+2` residue allowance
    make `2` the fixpoint, so the side condition `boundM P fuel ≤ 2` (value below
    `2^{k+1}`, two conditional subtracts) is reachable. Invariant:
    `multiFold P n V < 2^k · boundM P n`. -/
def boundM (P : MultiSolinasPrime) : Nat → Nat
  | 0 => 2 ^ P.k
  | (n + 1) => ((boundM P n - 1) * P.c) / 2 ^ P.k + 2

/-- `multiFold` stays under `2^k · boundM`, for `V < 2^{2k}`. -/
theorem multiFold_lt_boundM (P : MultiSolinasPrime)
    {V : Nat} (hV : V < 2 ^ (2 * P.k)) (n : Nat) :
    multiFold P n V < 2 ^ P.k * boundM P n := by
  have hk : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  induction n with
  | zero =>
    simp only [multiFold, boundM]
    rw [← pow_add, ← two_mul]; exact hV
  | succ n ih =>
    rw [multiFold, boundM]
    -- fold w < (boundM n − 1)·c + 2^k, where w = multiFold P n V < 2^k·(boundM n)
    have hfold := multiFold_one_lt' P (M := boundM P n) ih
    set a := (boundM P n - 1) * P.c with ha
    -- 2^k·(a/2^k + 1) ≥ a (the div lower bound), so a + 2^k ≤ 2^k·(a/2^k + 1) + 2^k
    have hge : 2 ^ P.k * (a / 2 ^ P.k + 1) ≥ a := by
      have hsplit := Nat.div_add_mod a (2 ^ P.k)
      have hmod : a % 2 ^ P.k < 2 ^ P.k := Nat.mod_lt _ hk
      have hmul : 2 ^ P.k * (a / 2 ^ P.k + 1) = 2 ^ P.k * (a / 2 ^ P.k) + 2 ^ P.k := by ring
      omega
    calc solinasFold P.toSolinas (multiFold P n V)
        < a + 2 ^ P.k := hfold
      _ ≤ 2 ^ P.k * (a / 2 ^ P.k + 2) := by
          have hexp : 2 ^ P.k * (a / 2 ^ P.k + 2)
              = 2 ^ P.k * (a / 2 ^ P.k + 1) + 2 ^ P.k := by ring
          omega

/-! ### The multi-term side condition and correctness

`MultiSolinasOK` packages exactly what the iterated-fold reduce needs: `c ≥ 1`,
`3·c < 2^k` (so `c < p`, the genuine-modulus constraint, and two conditional
subtracts collapse a value `< 2^{k+1}` into `[0, p)`), well-formed limbs, and the
single per-prime numeric check `boundM P fuel ≤ 2` (so `fuel` folds bring the
value below `2^{k+1}`). The last is a closed `Nat` computation per prime,
discharged by `norm_num`/`decide`. -/

/-- Side condition for the multi-term iterated-fold reduce. -/
structure MultiSolinasOK (P : MultiSolinasPrime) (high low : Nat) : Prop where
  /-- `c ≥ 1`. -/
  c_pos : 1 ≤ P.c
  /-- `3·c < 2^k`: gives `c < p` (genuine modulus) and that two conditional
      subtracts of `p` collapse a value `< 2^{k+1}` into `[0, p)` (since
      `2^{k+1} − 2p = 2c < p`). Satisfied by every deployed Solinas prime
      (`c ≪ 2^k`). -/
  three_c_lt : 3 * P.c < 2 ^ P.k
  /-- High limb below the radix. -/
  high_lt : high < 2 ^ P.k
  /-- Low limb below the radix. -/
  low_lt : low < 2 ^ P.k
  /-- The fuel suffices: `fuel` folds drive the value below `2^{k+1}`. -/
  fuel_ok : boundM P P.fuel ≤ 2

/-- **Multi-term fused-reduce correctness (general).** For a multi-term Solinas
    prime `p = 2^k − c` with `3c < 2^k` and a fold count
    `fuel` driving `boundM P fuel ≤ 2`, the iterated-fold reduce computes the
    residue: `multiSolinasReduce P high low = (high·2^k + low) mod (2^k − c)`.
    Unlike the single-term `solinasReduce_eq_mod`, this admits *large* `c` (of
    order `2^{k-32}`, as for the NIST curves) by folding `fuel`-many times. -/
theorem multiSolinasReduce_eq_mod (P : MultiSolinasPrime) {high low : Nat}
    (h : MultiSolinasOK P high low) :
    multiSolinasReduce P high low = (high * 2 ^ P.k + low) % P.modulus := by
  have hk : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  have hc_lt : P.c < 2 ^ P.k := by have := h.three_c_lt; have := h.c_pos; omega
  have hc_le : P.c ≤ 2 ^ P.k := le_of_lt hc_lt
  have hp_pos : 0 < P.modulus := by
    simp only [MultiSolinasPrime.modulus]; omega
  set V := high * 2 ^ P.k + low with hVdef
  have hV2k : V < 2 ^ (2 * P.k) := by
    have h2k : (2 : Nat) ^ (2 * P.k) = 2 ^ P.k * 2 ^ P.k := by
      rw [two_mul, pow_add]
    rw [hVdef, h2k]
    have hlow := h.low_lt
    have hhigh : high + 1 ≤ 2 ^ P.k := by have := h.high_lt; omega
    have hstep : (high + 1) * 2 ^ P.k ≤ 2 ^ P.k * 2 ^ P.k :=
      Nat.mul_le_mul_right _ hhigh
    have hexp : (high + 1) * 2 ^ P.k = high * 2 ^ P.k + 2 ^ P.k := by ring
    omega
  have h3c := h.three_c_lt
  set t := multiFold P P.fuel V with htdef
  -- t < 2·2^k (from fuel_ok, boundM ≤ 2)
  have ht_lt : t < 2 * 2 ^ P.k := by
    have hb := multiFold_lt_boundM P (V := V) hV2k P.fuel
    rw [← htdef] at hb
    calc t < 2 ^ P.k * boundM P P.fuel := hb
      _ ≤ 2 ^ P.k * 2 := Nat.mul_le_mul_left _ h.fuel_ok
      _ = 2 * 2 ^ P.k := by ring
  -- residue preserved by both folds and both conditional subtracts
  have hmodt : t % P.modulus = V % P.modulus := by
    rw [htdef]; exact multiFold_mod P hc_le P.fuel V
  -- first condSub: s < p, or s < 2·2^k - p = 2^k + c
  set s := condSub P t with hsdef
  have hs_drop : s < P.modulus ∨ s < 2 * 2 ^ P.k - P.modulus :=
    condSub_drop P (t := t) (B := 2 * 2 ^ P.k) ht_lt
  -- in either case s < 2·p, so the second condSub lands in [0, p)
  have hs_lt2p : s < 2 * P.modulus := by
    simp only [MultiSolinasPrime.modulus] at hs_drop ⊢
    rcases hs_drop with h1 | h2 <;> omega
  have hfinal_lt : condSub P s < P.modulus :=
    condSub_lt_of_lt_two_mul P hs_lt2p
  -- residue of the double condSub equals V mod p
  have hmod_final : condSub P s % P.modulus = V % P.modulus := by
    rw [condSub_mod P s, hsdef, condSub_mod P t, hmodt]
  -- conclude
  show condSub P (condSub P t) = V % P.modulus
  rw [← hsdef, ← hmod_final, Nat.mod_eq_of_lt hfinal_lt]

/-! ## 11. Multi-term per-prime instantiations (#403)

The NIST curves and two single-term quick wins, each instantiating
`MultiSolinasPrime` and discharging `MultiSolinasOK`. The `fuel` is the number of
high-half folds `boundM P fuel ≤ 2` requires (P-256: 8, P-384: 2; the Mersenne
P-521: 1; Goldilocks: 2), `terms` records the signed-power Solinas shape, and `c`
is the net subtrahend. The `fuel_ok` check is a closed `Nat` computation. -/

/-- P-256 / secp256r1 / prime256v1: `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`,
    i.e. `c = 2^224 − 2^192 − 2^96 + 1`. Multi-term (large `c ≈ 2^224`), 8 folds. -/
def multiP256 : MultiSolinasPrime where
  k := 256
  c := 2 ^ 224 - 2 ^ 192 - 2 ^ 96 + 1
  fuel := 8
  terms := [(false, 224), (true, 192), (true, 96), (false, 0)]

/-- P-384 / secp384r1: `p = 2^384 − 2^128 − 2^96 + 2^32 − 1`,
    i.e. `c = 2^128 + 2^96 − 2^32 + 1`. Multi-term (`c ≈ 2^128`), 2 folds. -/
def multiP384 : MultiSolinasPrime where
  k := 384
  c := 2 ^ 128 + 2 ^ 96 - 2 ^ 32 + 1
  fuel := 2
  terms := [(false, 128), (false, 96), (true, 32), (false, 0)]

/-- P-521 / secp521r1: the Mersenne prime `p = 2^521 − 1` (`c = 1`). 1 fold. -/
def multiP521 : MultiSolinasPrime where
  k := 521
  c := 1
  fuel := 1
  terms := [(false, 0)]

/-- Goldilocks (the Plonky3 64-bit field): `p = 2^64 − 2^32 + 1`,
    i.e. `c = 2^32 − 1`. 2 folds. -/
def multiGoldilocks : MultiSolinasPrime where
  k := 64
  c := 2 ^ 32 - 1
  fuel := 2
  terms := [(false, 32), (true, 0)]

/-- The P-256 net subtrahend `c = 2^224 − 2^192 − 2^96 + 1`, so
    `p = 2^256 − c = 2^256 − 2^224 + 2^192 + 2^96 − 1`. -/
theorem multiP256_modulus :
    multiP256.modulus = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1 := by
  native_decide

/-- The P-384 modulus `p = 2^384 − 2^128 − 2^96 + 2^32 − 1`. -/
theorem multiP384_modulus :
    multiP384.modulus = 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1 := by
  native_decide

/-- The P-521 modulus `p = 2^521 − 1`. -/
theorem multiP521_modulus : multiP521.modulus = 2 ^ 521 - 1 := by native_decide

/-- The Goldilocks modulus `p = 2^64 − 2^32 + 1`. -/
theorem multiGoldilocks_modulus : multiGoldilocks.modulus = 2 ^ 64 - 2 ^ 32 + 1 := by
  native_decide

/-- **P-256 reduce correctness.** For well-formed limbs, the 8-fold reduce
    computes the P-256 residue. -/
theorem reduceP256_eq_mod {high low : Nat}
    (hh : high < 2 ^ 256) (hl : low < 2 ^ 256) :
    multiSolinasReduce multiP256 high low
      = (high * 2 ^ 256 + low) % multiP256.modulus :=
  multiSolinasReduce_eq_mod multiP256
    { c_pos := by norm_num [multiP256]
      three_c_lt := by native_decide
      high_lt := hh
      low_lt := hl
      fuel_ok := by native_decide }

/-- **P-384 reduce correctness.** -/
theorem reduceP384_eq_mod {high low : Nat}
    (hh : high < 2 ^ 384) (hl : low < 2 ^ 384) :
    multiSolinasReduce multiP384 high low
      = (high * 2 ^ 384 + low) % multiP384.modulus :=
  multiSolinasReduce_eq_mod multiP384
    { c_pos := by norm_num [multiP384]
      three_c_lt := by native_decide
      high_lt := hh
      low_lt := hl
      fuel_ok := by native_decide }

/-- **P-521 reduce correctness** (Mersenne, single fold). -/
theorem reduceP521_eq_mod {high low : Nat}
    (hh : high < 2 ^ 521) (hl : low < 2 ^ 521) :
    multiSolinasReduce multiP521 high low
      = (high * 2 ^ 521 + low) % multiP521.modulus :=
  multiSolinasReduce_eq_mod multiP521
    { c_pos := by norm_num [multiP521]
      three_c_lt := by native_decide
      high_lt := hh
      low_lt := hl
      fuel_ok := by native_decide }

/-- **Goldilocks reduce correctness** (the Plonky3 field). -/
theorem reduceGoldilocks_eq_mod {high low : Nat}
    (hh : high < 2 ^ 64) (hl : low < 2 ^ 64) :
    multiSolinasReduce multiGoldilocks high low
      = (high * 2 ^ 64 + low) % multiGoldilocks.modulus :=
  multiSolinasReduce_eq_mod multiGoldilocks
    { c_pos := by norm_num [multiGoldilocks]
      three_c_lt := by native_decide
      high_lt := hh
      low_lt := hl
      fuel_ok := by native_decide }

/-! ## 12. Goldilocks field-multiply emitter (#403)

The multi-term value-level reduce `multiSolinasReduce multiGoldilocks hi lo` is
the fold–fold–condSub–condSub the emitted kernel below realises for the 64-bit
Goldilocks field `p = 2^64 − 2^32 + 1` (`c = 2^32 − 1`, `fuel = 2`). The 128-bit
product `(phi:plo)` of two field elements is reduced by:

* `fold1 = phi·c + plo`  → `(a1:a0)` (two `MULX`/`ADD`/`ADC` words; `a1 ≤ 2^32`);
* `fold2 = a1·c + a0`    → `(b1:b0)` (`b1 ≤ 1`);
* two conditional subtracts of `p` on the 65-bit `(b1:b0)` (a 2-word
  `SUB`/`SBB` + `CMOVB` pair), landing the result in `[0, p)`.

This is the `k = 64`-class reduce skeleton (single 64-bit fold boundary, 2-word
conditional subtract) — distinct from the `2^255`/`2^256` 4-limb skeletons of §7
/§8.1, and matching the verified `multiSolinasReduce` semantics fold-for-fold.
The all-inputs byte-identity against a reference is the external KAT
(`bench/goldilocks_fieldmul_compare`, vs Plonky3's `GoldilocksField` mul and GMP
`mod p`), as for the other primes. Register roles: `yd`(=%rdx) the `MULX`
multiplier, `x`/`y` the inputs, `plo`/`phi` the product words, `a0`/`a1` and
`b0`/`b1` the fold words, `pl` the constant `p`, `tmp` scratch; result in `b0`. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)

/-- The Goldilocks reduce: fold the 128-bit product `(phi:plo)` twice by
    `c = 2^32 − 1`, then two conditional subtracts of `p`. Faithful instruction
    realisation of `multiSolinasReduce multiGoldilocks phi plo`. -/
def goldilocksReduceBlock : List (JInstr 64) :=
  [ -- fold1 = phi·c + plo  →  (a1:a0)
    .mov "yd" (.imm (2 ^ 32 - 1))          -- yd := c
  , .mulx "a1" "a0" (.reg "yd") (.reg "phi")  -- (a0:a1) = c·phi
  , .add "a0" (.reg "plo")
  , .adc "a1" (.imm 0)                       -- (a1:a0) = c·phi + plo
    -- fold2 = a1·c + a0  →  (b1:b0)
  , .mulx "b1" "b0" (.reg "yd") (.reg "a1")  -- (b0:b1) = c·a1
  , .add "b0" (.reg "a0")
  , .adc "b1" (.imm 0)                       -- (b1:b0) = c·a1 + a0
    -- condSub #1: (b1:b0) ≥ p ?  subtract p across both words (cmov on borrow)
  , .mov "pl" (.imm 0xffffffff00000001)      -- pl := p (< 2^64)
  , .mov "tmp" (.reg "b0")
  , .mov "th" (.reg "b1")
  , .sub "tmp" (.reg "pl")
  , .sbb "th" (.imm 0)                        -- (th:tmp) = (b1:b0) − p, CF = borrow
  , .cmovb "tmp" (.reg "b0")                  -- CF (value < p) ⇒ keep b0, else b0−p
  , .cmovb "th" (.reg "b1")                   --                ⇒ keep b1, else b1−borrow
  , .mov "b0" (.reg "tmp")
  , .mov "b1" (.reg "th")
    -- condSub #2: same, on the (now possibly still 65-bit) (b1:b0)
  , .mov "tmp" (.reg "b0")
  , .mov "th" (.reg "b1")
  , .sub "tmp" (.reg "pl")
  , .sbb "th" (.imm 0)
  , .cmovb "tmp" (.reg "b0")
  , .mov "b0" (.reg "tmp")
    -- result (< p, fits 64 bits) in b0 → %rax
  , .mov "rax" (.reg "b0") ]

/-- The leading `MULX` of the whole kernel forms the 128-bit product `y·x`;
    the reduce above consumes `(phi:plo)`. The full straight-line body. -/
def goldilocksMulBlock : List (JInstr 64) :=
  [ .mov "yd" (.reg "y")                      -- yd := y (MULX src1)
  , .mulx "phi" "plo" (.reg "yd") (.reg "x")  -- (plo:phi) = y·x
  ] ++ goldilocksReduceBlock

/-- The Goldilocks reduce carries the field constant `c = 2^32 − 1` in the first
    fold's `mov yd, $imm`, and the modulus `p = 0xffffffff00000001` in the
    conditional-subtract `mov pl, $imm`. -/
theorem goldilocksReduce_constants :
    goldilocksReduceBlock.head? = some (.mov "yd" (.imm 4294967295))
      ∧ goldilocksReduceBlock[7]? = some (.mov "pl" (.imm 18446744069414584321)) :=
  ⟨rfl, rfl⟩

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn regOf)

/-- Register pinning for the Goldilocks leaf: inputs `x`/`y` in the SysV
    arg regs, `yd` the `MULX`-pinned `%rdx`, result in `%rax`. -/
def goldilocksMulPinned : GpAlloc :=
  [("x", "%rdi"), ("y", "%rsi"), ("yd", "%rdx"), ("rax", "%rax")]

/-- First-fit allocation over the Goldilocks multiply block. -/
def goldilocksMulAlloc : GpAlloc := allocGp goldilocksMulPinned goldilocksMulBlock

/-- The full emitted leaf `goldilocks_mul_x86_from_lean(x, y) → (x·y) mod p`. -/
def goldilocksMulAsm : String :=
  renderLeafFn "goldilocks_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14" ]
    (renderBlockBody goldilocksMulAlloc goldilocksMulBlock)
    [ "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the Goldilocks field-multiply `.s`. -/
def emitGoldilocks : IO Unit := do
  IO.FS.createDirAll "bench/goldilocks_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/goldilocks_fieldmul_compare/gen_com/goldilocks_mul_x86_from_lean.s"
    goldilocksMulAsm
  IO.println "wrote goldilocks_mul_x86_from_lean.s (multi-term reduce, #403)"

/-! ## 13. The signed-term view: `p = 2^k − Σᵢ εᵢ·2^tᵢ` as the pass's pattern

§10's `MultiSolinasPrime.terms` records the signed-power decomposition of the
subtrahend, but the value-level reduce depends only on the net `c` — nothing
ties the list to the arithmetic. This section makes the term list load-bearing,
which is what a *generated* (rather than hand-authored) instruction realisation
needs:

* `termsVal` / `TermsRep` — the recorded list evaluates to the prime's actual
  subtrahend (`c = −Σᵢ sᵢ·2^tᵢ` over the recorded signs, i.e.
  `p = 2^k − Σᵢ εᵢ·2^tᵢ` with `εᵢ = −sᵢ`), a decidable per-prime check;
* `termsFold` + `termsFold_eq_solinasFold` — the **signed-shift schedule**
  (`v ↦ v mod 2^k + Σᵢ (−sᵢ)·((v/2^k)·2^tᵢ)`: split at `2^k`, shift the high
  half by each term exponent, add/subtract per sign — the only arithmetic an
  instruction realisation performs, no multiplier) computes exactly
  `solinasFold`, hence iterates to `multiFold` and, with the two conditional
  subtracts, to the proven `multiSolinasReduce`;
* `multiSolinasReduce_eq_mod_terms` / `multiSolinasReduce_lt` — reduce
  correctness restated on the signed-term form of the prime, plus the `< p`
  landing bound.

§14 then GENERATES the x86 instruction schedule from the term list, so the
multi-term kernels come through the pass instead of being hand-authored. -/

/-- The signed value `Σᵢ sᵢ·2^tᵢ` of a term list (`(true, t) = +2^t`,
    `(false, t) = −2^t`) — the signed powers that follow `2^k` in the prime, so
    `p = 2^k + termsVal terms` and the subtrahend is `c = −termsVal terms`. -/
def termsVal : List (Bool × Nat) → Int
  | [] => 0
  | (s, t) :: ts => (if s then (1 : Int) else -1) * 2 ^ t + termsVal ts

/-- The term list represents the subtrahend: `(c : Int) = −termsVal terms`,
    i.e. the prime really is `p = 2^k − Σᵢ εᵢ·2^tᵢ` for the recorded signed
    powers (`εᵢ = +1` on a recorded `(false, tᵢ)`). Decidable; discharged per
    prime by `native_decide`. -/
def TermsRep (P : MultiSolinasPrime) : Prop := (P.c : Int) = -termsVal P.terms

/-- The signed-shift accumulation `Σᵢ (−sᵢ)·(q·2^tᵢ)` — add the shifted high
    half `q·2^tᵢ` when the recorded sign is negative, subtract when positive —
    equals `q·(−termsVal terms)`. With `TermsRep` this is `q·c`: the multi-term
    fold's constant multiply needs no multiplier, only the signed shifts. -/
theorem signedShifts_eq_mul (q : Nat) (terms : List (Bool × Nat)) :
    (terms.map (fun t => (if t.1 then (-1 : Int) else 1) * (q : Int) * 2 ^ t.2)).sum
      = (q : Int) * (-termsVal terms) := by
  induction terms with
  | nil => simp [termsVal]
  | cons t ts ih =>
    obtain ⟨s, e⟩ := t
    simp only [List.map_cons, List.sum_cons, termsVal, ih]
    cases s <;> simp <;> ring

/-- The signed-term fold: `v ↦ (v mod 2^k) + Σᵢ (−sᵢ)·((v/2^k)·2^tᵢ)` — the
    schedule a generated instruction realisation walks. Stated over `Int`
    because individual partial sums may be subtractive. -/
def termsFold (terms : List (Bool × Nat)) (k : Nat) (v : Nat) : Int :=
  ((v % 2 ^ k : Nat) : Int)
    + (terms.map (fun t => (if t.1 then (-1 : Int) else 1) * ((v / 2 ^ k : Nat) : Int) * 2 ^ t.2)).sum

/-- **The signed-shift schedule computes the Solinas fold.** Under `TermsRep`,
    the term-list walk `termsFold` equals `solinasFold` on every input — the
    per-fold correctness of the generated schedule, for any signed multi-term
    prime. -/
theorem termsFold_eq_solinasFold (P : MultiSolinasPrime) (h : TermsRep P) (v : Nat) :
    termsFold P.terms P.k v = (solinasFold P.toSolinas v : Int) := by
  have h' : (P.c : Int) = -termsVal P.terms := h
  simp only [termsFold, solinasFold, MultiSolinasPrime.toSolinas_k,
    MultiSolinasPrime.toSolinas_c, signedShifts_eq_mul, ← h']
  push_cast
  ring

/-- Under `TermsRep` (and `c ≤ 2^k`), the modulus in signed-term form:
    `(p : Int) = 2^k + termsVal terms`. -/
theorem modulus_eq_terms (P : MultiSolinasPrime) (h : TermsRep P)
    (hc : P.c ≤ 2 ^ P.k) : (P.modulus : Int) = 2 ^ P.k + termsVal P.terms := by
  simp only [MultiSolinasPrime.modulus]
  rw [Nat.cast_sub hc, h]
  push_cast
  ring

/-- The reduce lands strictly below the modulus (`result < p`) — the bound
    companion to `multiSolinasReduce_eq_mod`. -/
theorem multiSolinasReduce_lt (P : MultiSolinasPrime) {high low : Nat}
    (h : MultiSolinasOK P high low) :
    multiSolinasReduce P high low < P.modulus := by
  have hp : 0 < P.modulus := by
    have := h.three_c_lt; have := h.c_pos
    simp only [MultiSolinasPrime.modulus]; omega
  rw [multiSolinasReduce_eq_mod P h]
  exact Nat.mod_lt _ hp

/-- **Signed multi-term Solinas reduce correctness, on the term-list form.**
    For a prime recorded as `p = 2^k − Σᵢ εᵢ·2^tᵢ` (`TermsRep` ties the list to
    the subtrahend), under `MultiSolinasOK` the iterated-fold reduce computes
    the residue mod that signed-term modulus. -/
theorem multiSolinasReduce_eq_mod_terms (P : MultiSolinasPrime) {high low : Nat}
    (hrep : TermsRep P) (h : MultiSolinasOK P high low) :
    multiSolinasReduce P high low
      = (high * 2 ^ P.k + low) % ((2 ^ P.k : Int) + termsVal P.terms).toNat := by
  have hc_le : P.c ≤ 2 ^ P.k := by
    have := h.three_c_lt; omega
  have hmod : ((2 ^ P.k : Int) + termsVal P.terms).toNat = P.modulus := by
    rw [← modulus_eq_terms P hrep hc_le]
    exact Int.toNat_natCast _
  rw [hmod]
  exact multiSolinasReduce_eq_mod P h

/-! ### 13.1 SM2 and the per-prime `TermsRep` checks

SM2 (GB/T 32918) is the remaining deployed `2^256`-boundary multi-term Solinas
prime: `p_sm2 = 2^256 − 2^224 − 2^96 + 2^64 − 1`, i.e. the subtrahend
`c = 2^224 + 2^96 − 2^64 + 1 ≈ 2^224`, 9 folds (`boundM` reaches `2` at
`fuel = 9`; at `8` it is still `3`). -/

/-- SM2 (GB/T 32918): `p = 2^256 − 2^224 − 2^96 + 2^64 − 1`, i.e.
    `c = 2^224 + 2^96 − 2^64 + 1`. Multi-term (`c ≈ 2^224`), 9 folds. -/
def multiSm2 : MultiSolinasPrime where
  k := 256
  c := 2 ^ 224 + 2 ^ 96 - 2 ^ 64 + 1
  fuel := 9
  terms := [(false, 224), (false, 96), (true, 64), (false, 0)]

/-- The SM2 modulus `p = 2^256 − 2^224 − 2^96 + 2^64 − 1`. -/
theorem multiSm2_modulus :
    multiSm2.modulus = 2 ^ 256 - 2 ^ 224 - 2 ^ 96 + 2 ^ 64 - 1 := by
  native_decide

/-- **SM2 reduce correctness.** For well-formed limbs, the 9-fold reduce
    computes the SM2 residue. -/
theorem reduceSm2_eq_mod {high low : Nat}
    (hh : high < 2 ^ 256) (hl : low < 2 ^ 256) :
    multiSolinasReduce multiSm2 high low
      = (high * 2 ^ 256 + low) % multiSm2.modulus :=
  multiSolinasReduce_eq_mod multiSm2
    { c_pos := by norm_num [multiSm2]
      three_c_lt := by native_decide
      high_lt := hh
      low_lt := hl
      fuel_ok := by native_decide }

/-- The recorded SM2 term list represents the SM2 subtrahend. -/
theorem multiSm2_termsRep : TermsRep multiSm2 := by
  unfold TermsRep; native_decide

/-- The recorded P-256 term list represents the P-256 subtrahend. -/
theorem multiP256_termsRep : TermsRep multiP256 := by
  unfold TermsRep; native_decide

/-- The recorded P-384 term list represents the P-384 subtrahend. -/
theorem multiP384_termsRep : TermsRep multiP384 := by
  unfold TermsRep; native_decide

/-- The recorded P-521 term list represents the P-521 subtrahend. -/
theorem multiP521_termsRep : TermsRep multiP521 := by
  unfold TermsRep; native_decide

/-- The recorded Goldilocks term list represents the Goldilocks subtrahend. -/
theorem multiGoldilocks_termsRep : TermsRep multiGoldilocks := by
  unfold TermsRep; native_decide

/-- **The SM2 per-fold register identity.** On the full 512-bit window, the
    fold's multiply-by-`c` is exactly the signed shifts the term list records:
    `q·c = (q ≪ 224) + (q ≪ 96) − (q ≪ 64) + q` as `BitVec 512` values (a
    mod-`2^512` ring identity — the shifted-out bits above `2^512` cannot occur
    for `q < 2^256`, where the true fold value is `< 2^481`). The constant is
    the term-list combination in register form (`BitVec.twoPow`);
    `sm2FoldConstant` pins it to the `c` literal. This is the word-level fact
    the generated shift/add/sub schedule relies on. -/
theorem sm2FoldShifts (q : BitVec 512) :
    q * (BitVec.twoPow 512 224 + BitVec.twoPow 512 96 - BitVec.twoPow 512 64 + 1)
      = (q <<< 224) + (q <<< 96) - (q <<< 64) + q := by
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  ring

/-- The fold constant of `sm2FoldShifts` is the SM2 subtrahend
    `c = 2^224 + 2^96 − 2^64 + 1` as a 512-bit register value. -/
theorem sm2FoldConstant :
    (BitVec.twoPow 512 224 + BitVec.twoPow 512 96 - BitVec.twoPow 512 64 + 1 : BitVec 512)
      = BitVec.ofNat 512 (2 ^ 224 + 2 ^ 96 - 2 ^ 64 + 1) := by
  native_decide

/-! ## 14. The generated multi-term reduce (the pass's multi-term arm)

The instruction schedule is GENERATED from the term list — no hand-authored
per-prime fold. Limb-generic over `n = k/64` (requires `64 ∣ k`; `n = 4` for
SM2/P-256, `n = 6` for P-384).

Scratch layout (byte offsets into the `sp` frame, `mtFrameBytes n = 40·n`
bytes):

* `0 .. 16n−8`    — the working value `v` (2n words; initially the 2k-bit
  product the schoolbook stores, LSW first);
* `16n .. 24n−8`  — the fold's high-half copy `q` (n words);
* `24n .. 40n−8`  — the shifted-term scratch (2n words).

One fold realises `solinasFold`: copy `q := v[n..2n−1]`, zero those words (so
the accumulator holds `r = v mod 2^k` as a 2n-word value), then for each
recorded term `(s, t)` materialise the full 2n-word window of `q·2^t` (no bits
discarded — the straddle synthesis keeps everything below `2^{2k}`, and
`q·c + r < 2^{2k}` throughout) and add/subtract it per sign. Word-level
carries/borrows thread through full 2n-word chains, so the accumulator is exact
mod `2^{2k}`; since the fold's true value is nonnegative and `< 2^{2k}`, the
words are exact. After `fuel` folds the value is `< 2^{k+1}` (the proven
`boundM` bound), so words `n+1..2n−1` are zero and two conditional subtracts of
`p` over `n+1` words land the result in `[0, p)` — exactly
`multiSolinasReduce`. The all-inputs byte-identity of the emitted stream is the
external GMP KAT, as for every 512-bit-product kernel (the per-fold value
schedule is the §13 theorems; the whole-block 512-bit symbolic execution is the
externalised obligation). -/

/-- Byte offset of the fold's high-half copy `q` (n words). -/
def mtQOff (n : Nat) : Nat := 16 * n

/-- Byte offset of the shifted-term scratch (2n words). -/
def mtTermOff (n : Nat) : Nat := 24 * n

/-- Total scratch-frame bytes: `v` (2n) + `q` (n) + term (2n) words. -/
def mtFrameBytes (n : Nat) : Nat := 40 * n

/-- Load the `q` word `q[i]` into `dst`, or zero if `i` is outside `[0, n)`
    (the straddle synthesis reads one word below/above the window). -/
def mtLoadQ (n : Nat) (dst : String) (i : Int) : List (JInstr 64) :=
  if 0 ≤ i ∧ i < n then [ .loadMem dst "sp" (mtQOff n + 8 * i.toNat) ]
  else [ .mov dst (.imm 0) ]

/-- Materialise the full 2n-word window of `q·2^shamt` (the n-word `q` at
    `mtQOff`) into the term scratch. For `shamt = 64·w + b`, output word `j` is
    `(q[j−w] ≪ b) ∨ (q[j−w−1] ≫ (64−b))` (pure word move when `b = 0`) — every
    bit of `q·2^shamt` below `2^{128n}` is kept, none discarded. -/
def mtBuildShift (n shamt : Nat) : List (JInstr 64) :=
  let w := shamt / 64
  let b := shamt % 64
  (List.range (2 * n)).flatMap (fun j =>
    mtLoadQ n "lo" ((j : Int) - w) ++
    (if b == 0 then []
     else [ .shl "lo" (.imm b) ] ++
       mtLoadQ n "hi" ((j : Int) - w - 1) ++
       [ .shr "hi" (.imm (64 - b)), .or_ "lo" (.reg "hi") ]) ++
    [ .storeMem "sp" (mtTermOff n + 8 * j) (.reg "lo") ])

/-- Add the 2n-word term scratch into the 2n-word working value (full-width
    ripple chain; loads/stores/`mov`s inside the chain preserve `CF`). -/
def mtAccAdd (n : Nat) : List (JInstr 64) :=
  (List.range (2 * n)).flatMap (fun i =>
    [ .loadMem "w0" "sp" (8 * i), .loadMem "lo" "sp" (mtTermOff n + 8 * i)
    , (if i == 0 then .add "w0" (.reg "lo") else .adc "w0" (.reg "lo"))
    , .storeMem "sp" (8 * i) (.reg "w0") ])

/-- Subtract the 2n-word term scratch from the 2n-word working value (full-width
    borrow chain). -/
def mtAccSub (n : Nat) : List (JInstr 64) :=
  (List.range (2 * n)).flatMap (fun i =>
    [ .loadMem "w0" "sp" (8 * i), .loadMem "lo" "sp" (mtTermOff n + 8 * i)
    , (if i == 0 then .sub "w0" (.reg "lo") else .sbb "w0" (.reg "lo"))
    , .storeMem "sp" (8 * i) (.reg "w0") ])

/-- One generated Solinas fold: `q := v[n..2n−1]`, zero those words, then walk
    the term list — a recorded `(false, t)` is `+2^t` in the subtrahend `c`, so
    the shifted window is ADDED; a recorded `(true, t)` is subtracted. -/
def mtOneFold (n : Nat) (terms : List (Bool × Nat)) : List (JInstr 64) :=
  (List.range n).flatMap (fun i =>
    [ .loadMem "y" "sp" (8 * (n + i)), .storeMem "sp" (mtQOff n + 8 * i) (.reg "y") ]) ++
  [ .mov "y" (.imm 0) ] ++
  (List.range n).map (fun i => .storeMem "sp" (8 * (n + i)) (.reg "y")) ++
  terms.flatMap (fun t =>
    mtBuildShift n t.2 ++ (if t.1 then mtAccSub n else mtAccAdd n))

/-- Limb `i` of the modulus, as a 64-bit immediate. -/
def mtPLimb (P : MultiSolinasPrime) (i : Nat) : Nat :=
  P.modulus / 2 ^ (64 * i) % 2 ^ 64

/-- One branch-free conditional subtract of `p` from the `(n+1)`-word value
    `v[0..n]` (words above `n` are zero after the folds). Trial-subtract into
    the term scratch — the final borrow `CF = 1` iff `v < p` — then a `cmovb`
    select per word writes back the original on borrow, the trial otherwise
    (loads, stores, `mov`s and `cmovb` all preserve `CF`, so one flag state
    gates every word). -/
def mtCondSub (P : MultiSolinasPrime) (n : Nat) : List (JInstr 64) :=
  (List.range (n + 1)).flatMap (fun i =>
    [ .loadMem "lo" "sp" (8 * i)
    , .mov "hi" (.imm (if i < n then mtPLimb P i else 0))
    , (if i == 0 then .sub "lo" (.reg "hi") else .sbb "lo" (.reg "hi"))
    , .storeMem "sp" (mtTermOff n + 8 * i) (.reg "lo") ]) ++
  (List.range (n + 1)).flatMap (fun i =>
    [ .loadMem "lo" "sp" (mtTermOff n + 8 * i), .loadMem "hi" "sp" (8 * i)
    , .cmovb "lo" (.reg "hi"), .storeMem "sp" (8 * i) (.reg "lo") ])

/-- **The generated multi-term reduce block**: `fuel` term-list folds, two
    conditional subtracts of `p`, and the n-word store to `z` — the instruction
    realisation of `multiSolinasReduce P`, generated from `(k, fuel, terms)`. -/
def multiTermReduceBlock (P : MultiSolinasPrime) : List (JInstr 64) :=
  let n := P.k / 64
  (List.replicate P.fuel (mtOneFold n P.terms)).flatten ++
  mtCondSub P n ++ mtCondSub P n ++
  (List.range n).flatMap (fun i =>
    [ .loadMem "w0" "sp" (8 * i), .storeMem "z" (8 * i) (.reg "w0") ])

/-- The multi-term field-multiply kernel constructor: a schoolbook product
    (stored to the scratch frame's low 2n words) composed with the generated
    reduce — the multi-term analogue of §8's `fieldMul255Kernel`. -/
def fieldMulMultiTermKernel (schoolbook : List (JInstr 64))
    (P : MultiSolinasPrime) : List (JInstr 64) :=
  schoolbook ++ multiTermReduceBlock P

/-! ### 14.1 The selection predicate

The pass fires the generated multi-term arm exactly when the prime matches the
signed multi-term pattern: whole-limb radix (`64 ∣ k`), a non-empty term list
that represents the subtrahend (`TermsRep`, checked as a boolean), and every
term exponent below the radix. -/

/-- Decidable multi-term pattern match: `64 ∣ k`, non-empty faithful term list,
    term exponents `< k`. -/
def multiTermPatternOK (P : MultiSolinasPrime) : Bool :=
  P.k % 64 == 0 && !P.terms.isEmpty && ((P.c : Int) == -termsVal P.terms)
    && P.terms.all (fun t => t.2 < P.k)

/-- A boolean pattern match certifies `TermsRep`. -/
theorem termsRep_of_patternOK {P : MultiSolinasPrime}
    (h : multiTermPatternOK P = true) : TermsRep P := by
  simp only [multiTermPatternOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

/-- The selection: emit the generated multi-term reduce when the prime matches
    the signed multi-term pattern, nothing otherwise (single-term small-`c`
    primes take the §7/§8.1 fused arms). -/
def selectMultiTermReduce (P : MultiSolinasPrime) : Option (List (JInstr 64)) :=
  if multiTermPatternOK P then some (multiTermReduceBlock P) else none

/-- The multi-term pattern matches SM2. -/
theorem multiTermPatternOK_sm2 : multiTermPatternOK multiSm2 = true := by
  native_decide

/-- The multi-term pattern matches P-256. -/
theorem multiTermPatternOK_p256 : multiTermPatternOK multiP256 = true := by
  native_decide

/-- The multi-term pattern matches P-384. -/
theorem multiTermPatternOK_p384 : multiTermPatternOK multiP384 = true := by
  native_decide

/-- The pass fires on SM2 and emits the generated reduce. -/
theorem select_fires_sm2 :
    selectMultiTermReduce multiSm2 = some (multiTermReduceBlock multiSm2) := by
  unfold selectMultiTermReduce
  rw [multiTermPatternOK_sm2]
  rfl

/-- The pass fires on P-256. -/
theorem select_fires_p256 :
    selectMultiTermReduce multiP256 = some (multiTermReduceBlock multiP256) := by
  unfold selectMultiTermReduce
  rw [multiTermPatternOK_p256]
  rfl

/-- The pass fires on P-384 (6-limb, `n = 6`). -/
theorem select_fires_p384 :
    selectMultiTermReduce multiP384 = some (multiTermReduceBlock multiP384) := by
  unfold selectMultiTermReduce
  rw [multiTermPatternOK_p384]
  rfl

end CatCrypt.Crypto.Optimizer.ModReduceSelect
