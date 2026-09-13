/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.BitVec
public import Mathlib.Data.Vector.Defs

/-!
# Fixed-point CDT Gaussian sampler for FN-DSA (FALCON / FIPS 206)

This module specifies the **FPU-free** fixed-point cumulative-distribution-table
(CDT) Gaussian sampler used by FN-DSA's hash-then-sign chain as a Lean
function, and proves a range bound for it.

## Background

The reference Falcon implementation uses a floating-point Gaussian sampler in
the inner loop of `ffSampling`. That floating-point path is the source of the
historical floating-point side-channel concerns. The Falcon specification
ships a parallel FPU-free variant (Falcon-FPU-free, FIPS 206 draft Appendix
A) where the floating-point sampler is replaced by a fixed-point CDT
sampler operating only on integer arithmetic.

This module implements the CDT half-Gaussian sampler at the **base distribution**
`χ₀` (`σ = σ_min / sqrt(2)` per the Falcon spec, equivalently fixed σ ≈ 1.8205).
The published RCDT table (Falcon-512/1024 spec §3.10.3, FIPS 206 Appendix B)
gives the reverse cumulative distribution of the half-Gaussian; every entry is
below `2^72`. A single sample packs 9 random bytes big-endian into a 72-bit
value, compares it against the 19 RCDT entries, and counts how many entries
are strictly greater. The count is the half-Gaussian sample; one extra sign
bit folds it to a centered sample.

## Main results

* `fixedPointCDTGaussian` — the sampler as a Lean function
  `Vector UInt8 9 → UInt8 → Int`.
* `rcdt_length` — the table has `RCDT_LEN = 19` entries.
* `baseSampler_le` — the half-Gaussian magnitude is at most `RCDT_LEN`.
* `fixedPointCDTGaussian_range` — the output of the Lean sampler function lies
  in `[-19, 19]`.

## Not stated in Lean

* Constant time of any implementation of the sampler.
* The statistical-distance bound of the Falcon specification (Lemma 2.1, the
  discretization error of CDT inversion).
* Any relation between these definitions and the `.jazz` text rendered in
  `FndsaEmit`.

## References

* Falcon specification, Round 3 (2022), §3.10.3 "BaseSampler"
* FIPS 206 draft, Appendix B (RCDT table)
* Lyubashevsky, Wichs — Simple Lattice Trapdoor Sampling from a Broad Class
  of Distributions, PKC 2015
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FndsaEmit.Sampler

/-! ## 1. The RCDT table (Falcon spec §3.10.3 / FIPS 206 Appendix B)

These 19 entries are the **published** cumulative-distribution constants for
the base half-Gaussian. Each entry is an integer below `2^72`, encoded as
`Nat`. The sample is the number of `RCDT[i]` *strictly greater than* the
72-bit random value read from the byte stream.

The values are those of the Falcon Round 3 specification. -/

/-- The Falcon BaseSampler reverse-CDT table (19 entries, each below `2^72`).
    Public spec constants. -/
def RCDT : List Nat :=
  [ 3024686241123004913666
  , 1564742784480091954050
  ,  636254429462080897535
  ,  199560484645026482916
  ,   47667343854657281903
  ,    8595902006365044063
  ,    1163297957344668388
  ,     117656387352093658
  ,       8867391802663976
  ,        496969357462633
  ,         20680885154299
  ,           638331848991
  ,            14602316184
  ,              247426747
  ,                3104126
  ,                  28824
  ,                    198
  ,                      1
  ,                      0
  ]

/-- Length of the RCDT table (19 entries). The sample value range is
    `[0, 19]` for the half-Gaussian, `[-19, 19]` after sign folding. -/
def RCDT_LEN : Nat := 19

/-- The RCDT table has `RCDT_LEN` entries. -/
theorem rcdt_length : RCDT.length = RCDT_LEN := rfl

/-! ## 2. Reading the 72-bit random value from 9 bytes

The sampler reads 9 bytes from the random stream and packs them big-endian
into a `Nat` below `2^72`. -/

/-- Pack 9 bytes big-endian into a single `Nat` (yields a 72-bit value). -/
def packBytesBE (bs : Vector UInt8 9) : Nat :=
  let arr := bs.toArray
  let f (acc : Nat) (b : UInt8) : Nat := acc * 256 + b.toNat
  arr.foldl f 0

/-! ## 3. The base half-Gaussian sampler

Compare the 72-bit random value against each RCDT entry in turn. Count the
number of entries strictly greater than the value. This count is the
half-Gaussian sample. The fold visits all 19 entries. -/

/-- The CDT compare-and-accumulate step: `acc + (if r < e then 1 else 0)`. -/
def cdtStep (r : Nat) (acc : Nat) (e : Nat) : Nat :=
  acc + (if r < e then 1 else 0)

/-- The base half-Gaussian sampler: 9 random bytes → integer in `[0, 19]`,
    a fold of `cdtStep` over all 19 RCDT entries. -/
def baseSampler (bs : Vector UInt8 9) : Nat :=
  RCDT.foldl (cdtStep (packBytesBE bs)) 0

/-- Sign-fold a half-Gaussian sample using one auxiliary bit (typically
    the LSB of a separate random byte). The bit `b = 0` gives `+x`, `b = 1`
    gives `-x`. This is the FN-DSA centered-Gaussian step. -/
def signFold (b : Bool) (x : Nat) : Int :=
  if b then -(x : Int) else (x : Int)

/-- The full fixed-point CDT Gaussian sampler at the base distribution.
    Reads 9 bytes for the magnitude and 1 byte for the sign (the sign byte's
    LSB is the sign bit). Output range: `[-RCDT_LEN, RCDT_LEN]`. -/
def fixedPointCDTGaussian (bs : Vector UInt8 9) (signByte : UInt8) : Int :=
  let mag := baseSampler bs
  signFold (signByte.toNat % 2 = 1) mag

/-! ## 4. Range bound -/

/-- foldl of `cdtStep r` over a list adds at most `xs.length` to `acc`. -/
theorem cdtStep_foldl_le (r : Nat) :
    ∀ (xs : List Nat) (acc : Nat),
      xs.foldl (cdtStep r) acc ≤ acc + xs.length := by
  intro xs
  induction xs with
  | nil => intro acc; simp
  | cons y ys ih =>
    intro acc
    have h := ih (acc + (if r < y then 1 else 0))
    simp [List.foldl_cons, cdtStep, List.length_cons]
    by_cases hr : r < y
    · simp [hr] at h
      have hys : ys.foldl (cdtStep r) (acc + 1) ≤ acc + 1 + ys.length := h
      simp [hr]
      omega
    · simp [hr] at h
      have hys : ys.foldl (cdtStep r) (acc + 0) ≤ acc + 0 + ys.length := h
      simp [hr]
      omega

/-- The base sampler's output lies in `[0, RCDT_LEN]` (one increment per
    RCDT entry, hence `≤ 19`). -/
theorem baseSampler_le (bs : Vector UInt8 9) :
    baseSampler bs ≤ RCDT_LEN := by
  unfold baseSampler
  have hlen : RCDT.length = RCDT_LEN := rcdt_length
  have h := cdtStep_foldl_le (packBytesBE bs) RCDT 0
  rw [hlen] at h
  simpa using h

/-- The full sampler's output is bounded below by `-RCDT_LEN`. -/
theorem fixedPointCDTGaussian_ge (bs : Vector UInt8 9) (sb : UInt8) :
    -(RCDT_LEN : Int) ≤ fixedPointCDTGaussian bs sb := by
  unfold fixedPointCDTGaussian signFold
  have h := baseSampler_le bs
  have hnn : (0 : Int) ≤ (baseSampler bs : Int) := Int.natCast_nonneg _
  by_cases hsb : sb.toNat % 2 = 1
  · simp [hsb]
    have h1 : (baseSampler bs : Int) ≤ (RCDT_LEN : Int) := by exact_mod_cast h
    omega
  · simp [hsb]

/-- The full sampler's output is bounded above by `RCDT_LEN`. -/
theorem fixedPointCDTGaussian_le (bs : Vector UInt8 9) (sb : UInt8) :
    fixedPointCDTGaussian bs sb ≤ (RCDT_LEN : Int) := by
  unfold fixedPointCDTGaussian signFold
  have h := baseSampler_le bs
  have hnn : (0 : Int) ≤ (baseSampler bs : Int) := Int.natCast_nonneg _
  by_cases hsb : sb.toNat % 2 = 1
  · simp [hsb]
  · simp [hsb]
    exact_mod_cast h

/-- The full sampler's output lies in `[-RCDT_LEN, RCDT_LEN]`. -/
theorem fixedPointCDTGaussian_range (bs : Vector UInt8 9) (sb : UInt8) :
    -(RCDT_LEN : Int) ≤ fixedPointCDTGaussian bs sb ∧
    fixedPointCDTGaussian bs sb ≤ (RCDT_LEN : Int) :=
  ⟨fixedPointCDTGaussian_ge bs sb, fixedPointCDTGaussian_le bs sb⟩

/-- The number of bytes `fixedPointCDTGaussian` consumes per sample: 9
    magnitude bytes and 1 sign byte. -/
def BYTES_PER_SAMPLE : Nat := 10

end CatCrypt.Crypto.SecureCompilation.VIR.FndsaEmit.Sampler
