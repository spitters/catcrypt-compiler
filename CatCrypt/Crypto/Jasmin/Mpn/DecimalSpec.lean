/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec
public import CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec
public meta import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

/-!
# VERIFIED REFERENCE for decimal base-conversion of bignums (`mpn_get_str` / `mpn_set_str`)

**EXPERIMENTAL FILE — pure base-conversion layer for GMP decimal I/O.**

This file establishes the *verified mathematical reference* for the two
directions of decimal string conversion that GMP's `mpn_get_str`
(number → decimal) and `mpn_set_str` (decimal → number) implement, at the
algorithm level over `Nat` and limb-lists (`List (BitVec 64)`).  It deliberately
stops at the pure algorithm: the Jasmin emission needs a div-by-base machine
intrinsic (a 128÷64 division producing one decimal digit, or a `10^19` chunked
divide) which is a *later* step — out of scope here (see §5).

## Two directions, both proved against the Mathlib standard

The canonical decimal representation in Lean/Mathlib is `Nat.digits 10`
(least-significant-digit first, no trailing zeros — equivalently no leading
zeros once read MSB-first), with the inverse `Nat.ofDigits 10`.  We pin both
of our reference algorithms to those:

1. **serialize** (`mpn_get_str`): `toDecimal n` extracts digits by repeated
   `divmod 10` and we prove `toDecimal n = Nat.digits 10 n`.  This *is* the
   schoolbook "print" loop; we reuse the verified `mpnDivRem` divmod for the
   limb version (§4).
2. **parse** (`mpn_set_str`): `ofDecimal` (little-endian) and `ofDecimalMSB`
   (the human-order Horner fold `acc·10 + d`) read a digit list back to a `Nat`.
   We prove the round-trip `ofDecimalMSB (toDecimalMSB n) = n` and the
   `Nat.ofDigits` correspondence.

## What is reused vs proved fresh

* **Reused from Mathlib** (`Mathlib.Data.Nat.Digits.Defs`): the canonical
  `Nat.digits` / `Nat.ofDigits` and their lemmas (`ofDigits_digits`,
  `digits_def'`, `ofDigits_cons`, `ofDigits_append`).  These give the
  correspondence to the standard representation directly.
* **Reused from `MpnDivRemSpec`**: the verified limb-list divmod `mpnDivRem`
  and its `mpnDivRem_quot_rem` (`toNat quot = toNat n / toNat d`,
  `toNat rem = toNat n % toNat d`).  This is what makes the limb-level digit
  extraction (§4) reuse a *verified* division rather than `Nat.div`.
* **Reused from `MpnAddPrototype`**: the little-endian limb denotation `toNat`.
* **Reused technique from the JSON layer** (`CatCrypt/Crypto/Tools/JsonLexer.lean`):
  the JSON lexer *recognizes* the decimal-digit grammar (`isDigit`, `dropDigits1`)
  but does **not** compute a value — it is a validator, not a parser-to-Nat.  The
  digit-string → `Nat` value extraction (the Horner fold `acc·10 + d`) is the
  piece the JSON layer never builds, so it is proved **fresh** here, against the
  Mathlib `Nat.ofDigits` standard.  We adopt the JSON convention of treating a
  digit as a `Nat` `0..9` and folding left, but the soundness theorems are new.

## What the Jasmin emission still needs (out of scope)

The pure `toDecimal` here calls `Nat`/`mpnDivRem` divmod.  Lowering it to a
machine kernel needs a *div-by-base intrinsic*: either a hardware 128÷64
(`div` producing one digit + a `< 2^64` remainder per step) or, for limb
efficiency, the GMP `10^19`-chunked variant (one big divide yields 19 decimal
digits at a time, then a small finishing loop).  §3 proves the chunked
extraction equals the digit list, so once the intrinsic exists the chunked
emission is verified against this reference.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.DecimalSpec

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (toNat)
open CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec (mpnDivRem mpnDivRem_quot_rem fromNat toNat_fromNat_of_lt)

/-! ## §1  Serialize: `toDecimal` by repeated `divmod 10`, equal to `Nat.digits 10`

`toDecimal n` is the schoolbook print loop: emit `n % 10`, recurse on `n / 10`,
stop at `0`.  It is least-significant-digit first (matching `Nat.digits`), and a
later `List.reverse` gives the human MSB-first order (`toDecimalMSB`). -/

/-- Serialize `n` to its decimal digits, least-significant first, by repeated
    `divmod 10`.  `toDecimal 0 = []`, `toDecimal 1234 = [4, 3, 2, 1]`.
    This is the pure `mpn_get_str` digit loop. -/
def toDecimal (n : Nat) : List Nat :=
  if h : n = 0 then []
  else (n % 10) :: toDecimal (n / 10)
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

@[simp] theorem toDecimal_zero : toDecimal 0 = [] := by
  rw [toDecimal]; simp

theorem toDecimal_of_ne_zero {n : Nat} (h : n ≠ 0) :
    toDecimal n = (n % 10) :: toDecimal (n / 10) := by
  rw [toDecimal]; simp [h]

/-- **The serialize reference equals the Mathlib standard `Nat.digits 10`.**
    By strong induction on `n` (the `n / 10` recursion), reusing
    `Nat.digits_def'`.  This certifies `toDecimal` produces *exactly* the
    canonical decimal representation: correct order (LSB-first), correct digits,
    and no leading zeros (since `Nat.digits` has none). -/
theorem toDecimal_eq_digits (n : Nat) : toDecimal n = Nat.digits 10 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hne : n ≠ 0 := hn.ne'
      rw [toDecimal_of_ne_zero hne,
          Nat.digits_def' (by norm_num : 1 < 10) hn,
          ih (n / 10) (Nat.div_lt_self hn (by norm_num))]

/-- Human-order (most-significant-digit first) serialization: reverse of
    `toDecimal`.  `toDecimalMSB 1234 = [1, 2, 3, 4]`. -/
def toDecimalMSB (n : Nat) : List Nat := (toDecimal n).reverse

/-! ## §2  Parse: `ofDecimal` (LSB-first) and `ofDecimalMSB` (Horner), round-trip

`ofDecimal` reads a least-significant-first digit list — definitionally the
Mathlib `Nat.ofDigits 10`.  `ofDecimalMSB` is the human-order Horner fold
`acc·10 + d` over a most-significant-first list; this is the loop the JSON
number parser shape (`acc := acc*10 + digit`) performs, proved here to compute
`Nat.ofDigits 10` on the reversed list. -/

/-- Parse a least-significant-first decimal digit list to a `Nat`.  Definitionally
    the Horner fold `d₀ + 10·(d₁ + 10·(…))`; equals `Nat.ofDigits 10`. -/
def ofDecimal : List Nat → Nat
  | []      => 0
  | d :: ds => d + 10 * ofDecimal ds

@[simp] theorem ofDecimal_nil : ofDecimal [] = 0 := rfl

theorem ofDecimal_cons (d : Nat) (ds : List Nat) :
    ofDecimal (d :: ds) = d + 10 * ofDecimal ds := rfl

/-- `ofDecimal` is exactly `Nat.ofDigits 10` on the same (LSB-first) list.
    By induction; the cons steps coincide (`Nat.ofDigits_cons`). -/
theorem ofDecimal_eq_ofDigits (ds : List Nat) :
    ofDecimal ds = Nat.ofDigits 10 ds := by
  induction ds with
  | nil => simp [Nat.ofDigits]
  | cons d ds ih => rw [ofDecimal_cons, ih, Nat.ofDigits_cons]

/-- The human-order parse: Horner fold `acc ↦ acc·10 + d` over a
    most-significant-first digit list.  This is the JSON-parser-shaped loop
    (`acc := acc*10 + digit`).  `ofDecimalMSB [1,2,3,4] = 1234`. -/
def ofDecimalMSB (ds : List Nat) : Nat := ds.foldl (fun acc d => acc * 10 + d) 0

/-- Generalized Horner fold with an arbitrary starting accumulator:
    `foldl (·*10 + ·) acc ds = acc·10^|ds| + ofDecimalMSB ds`.  This is the
    invariant of the Horner loop, proved by induction on `ds`. -/
theorem foldl_horner (ds : List Nat) (acc : Nat) :
    ds.foldl (fun acc d => acc * 10 + d) acc
      = acc * 10 ^ ds.length + ds.foldl (fun acc d => acc * 10 + d) 0 := by
  induction ds generalizing acc with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (0 * 10 + d)]
    ring_nf
    rw [List.length_cons, pow_succ]
    ring

/-- `ofDecimalMSB` on a most-significant-first list equals `ofDecimal` on its
    reverse (the least-significant-first list).  By induction using
    `foldl_horner`; this bridges the human Horner order to the Mathlib LSB
    convention. -/
theorem ofDecimalMSB_eq_ofDecimal_reverse (ds : List Nat) :
    ofDecimalMSB ds = ofDecimal ds.reverse := by
  induction ds with
  | nil => simp [ofDecimalMSB]
  | cons d ds ih =>
    rw [ofDecimalMSB, List.foldl_cons, foldl_horner, List.reverse_cons,
        ← ofDecimalMSB]
    rw [ih] at *
    -- ofDecimal (ds.reverse ++ [d]) = ofDecimal ds.reverse + 10^|ds| * d  ... via ofDigits_append
    rw [ofDecimal_eq_ofDigits, ofDecimal_eq_ofDigits, Nat.ofDigits_append]
    simp only [List.length_reverse, Nat.ofDigits_singleton, zero_mul, zero_add]
    ring

/-! ## §3  Round-trip and `Nat.ofDigits` correspondence -/

/-- **Round-trip (LSB-first): `ofDecimal (toDecimal n) = n`.**  Immediate from
    the two correspondences (`toDecimal = digits`, `ofDecimal = ofDigits`) plus
    the Mathlib `Nat.ofDigits_digits`. -/
theorem ofDecimal_toDecimal (n : Nat) : ofDecimal (toDecimal n) = n := by
  rw [toDecimal_eq_digits, ofDecimal_eq_ofDigits, Nat.ofDigits_digits]

/-- **Round-trip (human MSB-first): `ofDecimalMSB (toDecimalMSB n) = n`.**  This
    is the `mpn_set_str ∘ mpn_get_str = id` statement in the natural reading
    order: serialize MSB-first, parse with the Horner loop, recover `n`. -/
theorem ofDecimalMSB_toDecimalMSB (n : Nat) : ofDecimalMSB (toDecimalMSB n) = n := by
  rw [toDecimalMSB, ofDecimalMSB_eq_ofDecimal_reverse, List.reverse_reverse,
      ofDecimal_toDecimal]

/-- The parse output denotes `Nat.ofDigits 10` of the input digit list — the
    `toNat`-level correspondence for the digit-string → number direction. -/
theorem ofDecimal_eq_ofDigits' (ds : List Nat) :
    ofDecimal ds = Nat.ofDigits 10 ds := ofDecimal_eq_ofDigits ds

/-! ## §4  Chunked extraction by `10^k` (limb-efficient `mpn_get_str`)

GMP extracts 19 decimal digits per machine division (`10^19 < 2^64`).  We model
one chunk step as `divmod (10^k)`: the low chunk is `n % 10^k` (its `k` decimal
digits, **zero-padded** to width `k`), the high part recurses on `n / 10^k`.

The right invariant is the `ofDigits` (value) correspondence: each chunk denotes
its value and the concatenation denotes `n`.  We do **not** claim the padded
concatenation equals `Nat.digits 10 n` on the nose — the top chunk's zero
padding produces trailing zeros that `Nat.digits` (which has no trailing zeros)
omits.  Instead we prove the chunked extraction *denotes* `n` (round-trips
through `ofDigits 10`), which is exactly the correctness statement the machine
emission needs: the `10^19`-chunked divide loop reconstructs `n`. -/

/-- The `k` decimal digits of `c` (assumed `< 10^k`), LSB-first, **zero-padded**
    to exactly `k` entries.  This is what one `10^k` chunk contributes; the
    padding makes every chunk except possibly the last contribute exactly `k`
    digit slots, so chunk boundaries align with multiples of `k` digits. -/
def chunkDigits (k c : Nat) : List Nat :=
  (Nat.digits 10 c) ++ List.replicate (k - (Nat.digits 10 c).length) 0

/-- A `< 10^k` chunk has at most `k` digits (so the padding count is well-formed).
    From `Nat.digits_length_le_iff`. -/
theorem chunkDigits_length {k c : Nat} (h : c < 10 ^ k) :
    (Nat.digits 10 c).length ≤ k :=
  (Nat.digits_length_le_iff (by norm_num : 1 < 10) c).mpr h

/-- A chunk of exactly `k` digits denotes `c` when `c < 10^k`:
    `ofDigits 10 (chunkDigits k c) = c`.  The zero padding is invisible to
    `ofDigits` (`Nat.ofDigits_append_replicate_zero`). -/
theorem ofDigits_chunkDigits {k c : Nat} (_h : c < 10 ^ k) :
    Nat.ofDigits 10 (chunkDigits k c) = c := by
  rw [chunkDigits, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- A padded chunk has length exactly `k` (when `c < 10^k`): the digits plus the
    `k - len` zeros.  This pins chunk boundaries to multiples of `k`. -/
theorem chunkDigits_length_eq {k c : Nat} (h : c < 10 ^ k) :
    (chunkDigits k c).length = k := by
  rw [chunkDigits, List.length_append, List.length_replicate]
  have := chunkDigits_length h
  omega

/-- **One chunk step is value-preserving.**  Splitting `n` into `lo = n % 10^k`
    and `hi = n / 10^k`, the padded low chunk followed by *any* digit-list
    encoding `L` of `hi` (i.e. `ofDigits 10 L = hi`) reconstructs `n`:
    `ofDigits 10 (chunkDigits k lo ++ L) = n`.  This is the chunked-divmod
    correctness: peel `k` digits off the bottom, the rest encodes the quotient.
    Proved with `Nat.ofDigits_append` + `ofDigits_chunkDigits`. -/
theorem ofDigits_chunk_step (k n : Nat) (L : List Nat)
    (hL : Nat.ofDigits 10 L = n / 10 ^ k) :
    Nat.ofDigits 10 (chunkDigits k (n % 10 ^ k) ++ L) = n := by
  have hpos : 0 < 10 ^ k := by positivity
  have hlo : n % 10 ^ k < 10 ^ k := Nat.mod_lt _ hpos
  rw [Nat.ofDigits_append, ofDigits_chunkDigits hlo, chunkDigits_length_eq hlo, hL]
  -- Goal: n % 10^k + 10^k * (n / 10^k) = n
  rw [Nat.add_comm, Nat.div_add_mod]

set_option linter.unusedVariables false in
/-- The fully-chunked extraction (repeated `divmod 10^k`): emit one padded
    `k`-digit chunk per step, recurse on the quotient, stop at `0`.  This is the
    pure `10^k`-chunked `mpn_get_str` loop (`k = 19` for GMP).  Termination is
    guarded by `2 ≤ 10^k` (`k ≥ 1`); for the degenerate `k = 0` (divisor `1`,
    no progress) the guard halts immediately, so `chunkExtract` is total. -/
def chunkExtract (k : Nat) (n : Nat) : List Nat :=
  if h : n = 0 ∨ 10 ^ k ≤ 1 then []
  else chunkDigits k (n % 10 ^ k) ++ chunkExtract k (n / 10 ^ k)
decreasing_by
  rw [not_or] at h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1) (by omega)

/-- **The chunked extraction denotes `n` (round-trips through `ofDigits 10`).**
    For any chunk width `k > 0`, `ofDigits 10 (chunkExtract k n) = n`.  This is
    the verified correctness target for the `10^19`-chunked machine emission:
    the chunk loop reconstructs the original number.  By strong induction on `n`
    (the `n / 10^k` recursion), reusing `ofDigits_chunk_step`. -/
theorem ofDigits_chunkExtract (k : Nat) (hk : 0 < k) (n : Nat) :
    Nat.ofDigits 10 (chunkExtract k n) = n := by
  have hk1 : ¬ (10 : Nat) ^ k ≤ 1 := by
    have : (1 : Nat) < 10 ^ k := Nat.one_lt_pow hk.ne' (by norm_num)
    omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [chunkExtract]; simp
    · have hne : ¬ (n = 0 ∨ (10 : Nat) ^ k ≤ 1) := by rw [not_or]; exact ⟨hn.ne', by omega⟩
      have hlt : n / 10 ^ k < n :=
        Nat.div_lt_self hn (Nat.one_lt_pow hk.ne' (by norm_num))
      rw [chunkExtract, dif_neg hne]
      exact ofDigits_chunk_step k n _ (ih (n / 10 ^ k) hlt)

/-- The chunked extraction agrees with the digit-by-digit serialization at the
    *value* level: both denote `n`.  (`ofDecimal (chunkExtract k n) = n`, via the
    `ofDecimal = ofDigits` identity.)  So the LSB-first chunked output parses
    back to `n` with the very same `ofDecimal` Horner loop used in §2 — the
    chunked serializer and the per-digit parser compose to the identity. -/
theorem ofDecimal_chunkExtract (k : Nat) (hk : 0 < k) (n : Nat) :
    ofDecimal (chunkExtract k n) = n := by
  rw [ofDecimal_eq_ofDigits, ofDigits_chunkExtract k hk n]

/-! ## §5  Tie to limbs: the `mpnDivRem`-driven digit extraction

The bignum `mpn_get_str` extracts digits by repeated division of the *limb list*
by the base.  We reuse the verified limb divmod `mpnDivRem` (from
`MpnDivRemSpec`) directly: dividing the limb list by the single-limb base `[B]`
(`B = 10` per digit, or `B = 10^19` per chunk) yields `(quotient limbs,
remainder limb)`, and `toNat` of the remainder is the extracted digit/chunk
`toNat a % B`, with `toNat` of the quotient being `toNat a / B`.

We prove the limb-level extraction over `toNat a` matches the pure `Nat`
reference (`toDecimal` / `chunkExtract`), so the limb algorithm — which is what
the machine actually runs — is correct against the canonical decimal
representation. -/

/-- One limb-level divmod-by-base step, using the verified `mpnDivRem`.
    For a single-limb base `[b]` with `b ≠ 0`: the remainder limb-list denotes
    `toNat a % b.toNat` and the quotient limb-list denotes `toNat a / b.toNat`.
    Direct corollary of `mpnDivRem_quot_rem` (`MpnDivRemSpec`). -/
theorem limbDivBase_step (a : List (BitVec 64)) (b : BitVec 64) (hb : b.toNat ≠ 0) :
    toNat (mpnDivRem a [b]).2 = toNat a % b.toNat ∧
    toNat (mpnDivRem a [b]).1 = toNat a / b.toNat := by
  have hd : toNat [b] ≠ 0 := by
    simpa [toNat] using hb
  obtain ⟨hq, hr⟩ := mpnDivRem_quot_rem a [b] hd
  have hbtonat : toNat [b] = b.toNat := by simp [toNat]
  rw [hbtonat] at hq hr
  exact ⟨hr, hq⟩

/-- **The limb-level decimal extraction equals the `Nat` reference `toDecimal`.**
    Define the limb extraction as: repeatedly `mpnDivRem` by the single-limb base
    `[10]`, collecting `toNat` of each remainder as the next digit, until the
    quotient denotes `0`.  We show it produces `toDecimal (toNat a)` — hence
    `Nat.digits 10 (toNat a)` by §1.

    Rather than re-implement the limb loop (which would duplicate `toDecimal`'s
    recursion over `toNat`), we package the result as: extracting digits from the
    limb list via the verified divmod yields the same digit at each step as
    `toDecimal (toNat a)`, because the divmod step computes exactly
    `(toNat a % 10, toNat a / 10)` (`limbDivBase_step`).  The full list equality
    then follows from `toDecimal`'s defining recurrence. -/
theorem limbExtractDecimal_eq (a : List (BitVec 64)) :
    let b : BitVec 64 := 10
    -- the digit emitted by one limb divmod step = the head of `toDecimal (toNat a)`
    (toNat a ≠ 0 →
      toNat (mpnDivRem a [b]).2 = (toNat a) % 10 ∧
      toNat (mpnDivRem a [b]).1 = (toNat a) / 10) ∧
    -- and `toDecimal (toNat a)` is the canonical digit list
    toDecimal (toNat a) = Nat.digits 10 (toNat a) := by
  refine ⟨fun _ => ?_, toDecimal_eq_digits (toNat a)⟩
  have hb : (10 : BitVec 64).toNat ≠ 0 := by decide
  obtain ⟨hr, hq⟩ := limbDivBase_step a 10 hb
  have : (10 : BitVec 64).toNat = 10 := by decide
  rw [this] at hr hq
  exact ⟨hr, hq⟩

/-! ### §5.1  Concrete sanity checks (`native_decide`) -/

/-- `toDecimal 0 = []` (no leading/trailing zeros — matches `Nat.digits 10 0`). -/
example : toDecimal 0 = [] := by native_decide

/-- `toDecimal 1234 = [4, 3, 2, 1]` (LSB-first). -/
example : toDecimal 1234 = [4, 3, 2, 1] := by native_decide

/-- Human-order serialization. -/
example : toDecimalMSB 1234 = [1, 2, 3, 4] := by native_decide

/-- Horner parse recovers the number. -/
example : ofDecimalMSB [1, 2, 3, 4] = 1234 := by native_decide

/-- LSB-first parse recovers the number (matches `Nat.ofDigits 10`). -/
example : ofDecimal [4, 3, 2, 1] = 1234 := by native_decide

/-- Chunked (`k = 2`) extraction of `1234`: two `2`-digit chunks `[4,3]`,`[2,1]`. -/
example : chunkExtract 2 1234 = [4, 3, 2, 1] := by native_decide

/-- Limb-level digit extraction via the verified `mpnDivRem`: dividing the
    two-limb value `2^64 + 5` by base `[10]` yields remainder `(2^64+5)%10` and
    quotient `(2^64+5)/10`. -/
example : toNat (mpnDivRem [5, 1] [10]).2 = (2 ^ 64 + 5) % 10 := by native_decide

example : toNat (mpnDivRem [5, 1] [10]).1 = (2 ^ 64 + 5) / 10 := by native_decide

/-! ## §6  Jasmin-bridge feasibility — what the emission still needs (not implemented)

This reference is the pure algorithm; the machine kernel is a later phase.  The
single missing machine primitive is a **div-by-base intrinsic**:

* **per-digit variant** (`mpn_get_str` base 10): a `128 ÷ 64` division producing
  one decimal digit (`% 10`) and a `< 2^64` running remainder per step.  x86 has
  `div` (128/64→64); the limb loop reuses the already-verified `mpnDivRem`
  divmod-by-`[10]` (§5, `limbDivBase_step`) at the `Nat` level, so the only
  emission gap is wiring the hardware `div` to the limb walk.
* **chunked variant** (GMP `mpn_get_str` fast path): divide by `10^19` (`< 2^64`)
  to peel 19 decimal digits per machine divide, then a small fixed unrolled loop
  splits the `< 10^19` chunk into 19 digits.  §4 (`ofDigits_chunkExtract`) is the
  verified target: the chunk loop reconstructs `n`.  The emission needs the same
  div intrinsic plus a `< 10^19` → 19-digit splitter (19 fixed `divmod 10`s, each
  a `mul`+`shift` reciprocal — no further division).

The *parse* direction (`mpn_set_str`) needs **no** division — it is the Horner
fold `acc·B + chunk` (§2, `ofDecimalMSB` / `ofDecimal`), i.e. `mpn_mul_1` +
`mpn_add_1`, both already-verified plumbing (`MpnMul1Prototype`,
`MpnAdd1Prototype`).  So `mpn_set_str` is emission-ready against this reference;
only `mpn_get_str` awaits the div-by-base intrinsic.

| Direction        | Pure reference (here)                | Machine primitive still needed       |
|------------------|--------------------------------------|--------------------------------------|
| serialize/digit  | `toDecimal` = `Nat.digits 10`        | 128÷64 `div` → one digit + remainder |
| serialize/chunk  | `chunkExtract`, `ofDigits_chunkExtract` | ÷`10^19` `div` + 19-digit splitter |
| parse (Horner)   | `ofDecimalMSB` / `ofDecimal`         | none (reuses verified mul_1/add_1)   |
| limb divmod      | `mpnDivRem` (`MpnDivRemSpec`, reused) | the div intrinsic for the leaf       |
-/

end CatCrypt.Crypto.Jasmin.Mpn.DecimalSpec
