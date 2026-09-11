/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.SHA256
public import Mathlib.Data.BitVec

/-!
# SHA-256 dword (16×u32) lane functions — model-free, FIPS-180-4 bit-exact

The SHA-256 round-function bodies expressed on a single 32-bit dword lane
(`BitVec 32`, the per-lane view of an AVX-512 ZMM 16×u32 register), together
with their bit-exact ties to the abstract `UInt32` FIPS-180-4 spec
(`Crypto.Primitives.SHA256`).

These functions and ties were previously stated inside the AVX-512 dword machine
model (`X86Backend/Avx512DwordModel.lean` + `Sha256DwordRoundRealization.lean`).
They are **pure `BitVec 32` ↔ `UInt32` facts** — independent of any register-file
or instruction-set model — so they live here, importing only the abstract spec.
Consumers that need "the dword lane SHA-256 body equals the spec" depend on this
module without pulling in the AVX-512 model.

The lane is already 32-bit, so every tie is **bit-exact** (no `setWidth 32`
truncation): on a 32-bit lane the right rotate `rorD` wraps mod 32 — the
SHA-256 `rotr` — unlike the 64-bit-lane analogue.

* `chD` / `majD` — `Ch`/`Maj` bodies (pure bitwise, `ch_dword_bitExact` /
  `maj_dword_bitExact`).
* `rorD` — the 32-bit right rotate `(a >>> k) ||| (a <<< (32-k))`
  (`rorD_eq_rotateRight`, `rotr_toBitVec_eq_rorD`).
* `sigma0D` / `sigma1D` — the big `Σ₀`/`Σ₁` bodies
  (`bigSigma0_dword_bitExact` / `bigSigma1_dword_bitExact`).
* `smallSigma0D` / `smallSigma1D` — the small `σ₀`/`σ₁` schedule bodies
  (`smallSigma0_dword_bitExact` / `smallSigma1_dword_bitExact`).

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane

open CatCrypt.Crypto.Primitives.SHA256
  (ch maj bigSigma0 bigSigma1 smallSigma0 smallSigma1 rotr)

/-! ## 1. The 32-bit right rotate dword lane op -/

/-- The dword (`BitVec 32`) right rotate by an immediate `k`, written as the
    `(a >>> k) ||| (a <<< (32-k))` shift decomposition **at width 32** — the
    SHA-256 `rotr`.  At width 32 the high `k` bits wrap into the low `k`
    bits, mod 32 (`VPRORD`). -/
@[simp] def rorD (a : BitVec 32) (k : Nat) : BitVec 32 :=
  (a >>> k) ||| (a <<< (32 - k))

/-- **`rorD` is `BitVec.rotateRight` at width 32.**  For `0 < k < 32` the
    shift-decomposition `(a >>> k) ||| (a <<< (32-k))` equals `a.rotateRight k` —
    the 32-bit right rotate (wraps mod 32). -/
theorem rorD_eq_rotateRight (a : BitVec 32) (k : Nat) (hk : k < 32) :
    rorD a k = a.rotateRight k := by
  have hmod : k % 32 = k := Nat.mod_eq_of_lt hk
  rw [BitVec.rotateRight_def, rorD, hmod]

/-- **`rotr` tie (dword, bit-exact).**  For each SHA-256 amount `k`, the bit-vector
    of the abstract `UInt32` right-rotate `rotr x k` equals the dword lane rotate
    `rorD x.toBitVec k`.  Stated for the six SHA-256 `Σ` amounts; the lane is
    `BitVec 32`, so the rotate wraps mod 32 — bit-exact, unlike the 64-bit lane. -/
theorem rotr_toBitVec_eq_rorD (x : UInt32) :
    ((rotr x 2).toBitVec  = rorD x.toBitVec 2)  ∧
    ((rotr x 6).toBitVec  = rorD x.toBitVec 6)  ∧
    ((rotr x 11).toBitVec = rorD x.toBitVec 11) ∧
    ((rotr x 13).toBitVec = rorD x.toBitVec 13) ∧
    ((rotr x 22).toBitVec = rorD x.toBitVec 22) ∧
    ((rotr x 25).toBitVec = rorD x.toBitVec 25) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [rotr, rorD, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight,
        UInt32.toBitVec_shiftLeft]
      rfl

/-! ## 2. `Ch` and `Maj` — bit-exact at width 32 (pure bitwise) -/

/-- The abstract SHA-256 `Ch` body at `BitVec 32`: `(x &&& y) ^^^ (~~~x &&& z)`. -/
@[simp] def chD (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- The abstract SHA-256 `Maj` body at `BitVec 32`. -/
@[simp] def majD (x y z : BitVec 32) : BitVec 32 :=
  ((x &&& y) ^^^ (x &&& z)) ^^^ (y &&& z)

/-- **`Ch` tie (dword, bit-exact).**  The dword-lane `Ch` body `chD` equals the
    bit-vector of the abstract `Primitives.SHA256.ch` — bit-exact at width 32, no
    truncation. -/
theorem ch_dword_bitExact (x y z : UInt32) :
    chD x.toBitVec y.toBitVec z.toBitVec = (ch x y z).toBitVec := by
  rw [ch]
  simp only [chD, UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_not]

/-- **`Maj` tie (dword, bit-exact).**  The dword-lane `Maj` body `majD` equals the
    bit-vector of the abstract `Primitives.SHA256.maj`. -/
theorem maj_dword_bitExact (x y z : UInt32) :
    majD x.toBitVec y.toBitVec z.toBitVec = (maj x y z).toBitVec := by
  rw [maj]
  simp only [majD, UInt32.toBitVec_xor, UInt32.toBitVec_and]

/-! ## 3. `Σ₀` and `Σ₁` — BIT-EXACT at width 32 -/

/-- The dword-lane `Σ₀` body: `rorD a 2 ⊕ rorD a 13 ⊕ rorD a 22`. -/
@[simp] def sigma0D (a : BitVec 32) : BitVec 32 :=
  ((rorD a 2) ^^^ (rorD a 13)) ^^^ (rorD a 22)

/-- The dword-lane `Σ₁` body: `rorD e 6 ⊕ rorD e 11 ⊕ rorD e 25`. -/
@[simp] def sigma1D (e : BitVec 32) : BitVec 32 :=
  ((rorD e 6) ^^^ (rorD e 11)) ^^^ (rorD e 25)

/-- **`Σ₀` tie (dword, BIT-EXACT at width 32).**  The dword-lane `Σ₀` body equals
    the bit-vector of the abstract `Primitives.SHA256.bigSigma0` — the rotate is
    the 32-bit `rorD`, so it wraps mod 32 and the tie is bit-exact. -/
theorem bigSigma0_dword_bitExact (a : UInt32) :
    sigma0D a.toBitVec = (bigSigma0 a).toBitVec := by
  obtain ⟨h2, _, _, h13, h22, _⟩ := rotr_toBitVec_eq_rorD a
  rw [bigSigma0]
  simp only [sigma0D, UInt32.toBitVec_xor, ← h2, ← h13, ← h22]

/-- **`Σ₁` tie (dword, BIT-EXACT at width 32).**  The dword-lane `Σ₁` body equals
    the bit-vector of the abstract `Primitives.SHA256.bigSigma1` — bit-exact. -/
theorem bigSigma1_dword_bitExact (e : UInt32) :
    sigma1D e.toBitVec = (bigSigma1 e).toBitVec := by
  obtain ⟨_, h6, h11, _, _, h25⟩ := rotr_toBitVec_eq_rorD e
  rw [bigSigma1]
  simp only [sigma1D, UInt32.toBitVec_xor, ← h6, ← h11, ← h25]

/-! ## 4. `σ₀` and `σ₁` — the message-schedule small sigmas, BIT-EXACT at width 32

`σ₀(x) = ρ⁷(x) ⊕ ρ¹⁸(x) ⊕ (x ≫ 3)` and `σ₁(x) = ρ¹⁷(x) ⊕ ρ¹⁹(x) ⊕ (x ≫ 10)`
(FIPS-180-4 §4.1.2).  The rotate is the 32-bit `rorD` (wraps mod 32) and the
right shift is the immediate logical `>>>` (`vpsrld`). -/

/-- The dword-lane `σ₀(x) = ρ⁷(x) ⊕ ρ¹⁸(x) ⊕ (x ≫ 3)`. -/
@[simp] def smallSigma0D (x : BitVec 32) : BitVec 32 :=
  ((rorD x 7) ^^^ (rorD x 18)) ^^^ (x >>> 3)

/-- The dword-lane `σ₁(x) = ρ¹⁷(x) ⊕ ρ¹⁹(x) ⊕ (x ≫ 10)`. -/
@[simp] def smallSigma1D (x : BitVec 32) : BitVec 32 :=
  ((rorD x 17) ^^^ (rorD x 19)) ^^^ (x >>> 10)

/-- `rotr` tie for the schedule amounts `7,18,17,19` (each `< 32`, lane wraps mod
    32 — bit-exact). -/
theorem rotr_sched_toBitVec (x : UInt32) :
    ((rotr x 7).toBitVec  = rorD x.toBitVec 7)  ∧
    ((rotr x 18).toBitVec = rorD x.toBitVec 18) ∧
    ((rotr x 17).toBitVec = rorD x.toBitVec 17) ∧
    ((rotr x 19).toBitVec = rorD x.toBitVec 19) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [rotr, rorD, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight,
        UInt32.toBitVec_shiftLeft]
      rfl

/-- **`σ₀` tie (dword, BIT-EXACT at width 32).** The dword-lane `σ₀` body equals
    the bit-vector of the abstract `Primitives.SHA256.smallSigma0` — the rotate is
    `rorD` (wraps mod 32) and the shift is `>>>`, so it is bit-exact. -/
theorem smallSigma0_dword_bitExact (x : UInt32) :
    smallSigma0D x.toBitVec = (smallSigma0 x).toBitVec := by
  obtain ⟨h7, h18, _, _⟩ := rotr_sched_toBitVec x
  rw [smallSigma0]
  simp only [smallSigma0D, UInt32.toBitVec_xor, UInt32.toBitVec_shiftRight,
    ← h7, ← h18]
  rfl

/-- **`σ₁` tie (dword, BIT-EXACT at width 32).** The dword-lane `σ₁` body equals
    the bit-vector of the abstract `Primitives.SHA256.smallSigma1` — bit-exact. -/
theorem smallSigma1_dword_bitExact (x : UInt32) :
    smallSigma1D x.toBitVec = (smallSigma1 x).toBitVec := by
  obtain ⟨_, _, h17, h19⟩ := rotr_sched_toBitVec x
  rw [smallSigma1]
  simp only [smallSigma1D, UInt32.toBitVec_xor, UInt32.toBitVec_shiftRight,
    ← h17, ← h19]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
