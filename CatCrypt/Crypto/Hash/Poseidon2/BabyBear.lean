/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.Basic

/-!
# Poseidon2 over Baby Bear (width 16)

Defines the Poseidon2 permutation over Baby Bear `F = ZMod 2013265921`
with the **upstream Plonky3 round constants and MDS matrices**, not
placeholders.

## Provenance

All concrete data is ported verbatim from Plonky3's
`p3-baby-bear-0.5.2/src/poseidon2.rs` (canonical-residue u32 literals
passed to `BabyBear::new_array`, which routes through `to_monty` —
so the input integers are canonical, not Montgomery-encoded):

* `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL` — 4 rounds × 16 lanes
* `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`   — 4 rounds × 16 lanes
* `BABYBEAR_POSEIDON2_RC_16_INTERNAL`         — 13 scalar constants
* The internal diagonal `V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4,
  1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]`.
* The external 4×4 MDS block `[[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]`
  (Plonky3's `MDSMat4` — `apply_mat4`, the optimised "7 additions + 2
  doubles" variant from `p3-poseidon2-0.5.2/src/external.rs`).
* The outer circulant: `state[i] += sum_{j ≡ i mod 4} state[j]`.

The structure (8 external rounds = 4 initial + 4 final, 13 partial rounds,
state width 16, S-box `x ↦ x^7`) matches the ePrint 2023/323 Poseidon2 spec
plus the width-16 Baby Bear parameters from the Plonky3 paper.

## What this does NOT yet deliver

* **Collision resistance** is still a literature claim. The wired-up
  `Plonky3MerkleCR` advantage bound (see `BabyBearCR.lean`) is supplied
  by the caller as a `Prop` argument.
* **A KAT lemma** would `native_decide`-check `poseidon2BabyBearPermute`
  against Plonky3's reference test vector
  (`test_default_babybear_poseidon2_width_16` in upstream `poseidon2.rs`).
  See the `KAT` section below — the inputs and expected outputs are
  recorded; the `native_decide` check is the next mechanical step.

## References

* Grassi, Khovratovich, Rechberger, Roy, Schofnegger,
  *Poseidon2: A Faster Version of the Poseidon Hash Function*,
  ePrint 2023/323.
* Plonky3 — `p3-baby-bear` crate, version 0.5.2 (constants source).
* Plonky3 — `p3-poseidon2` crate, version 0.5.2 (external/internal layer math).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Poseidon2.BabyBear

/-! ## Field -/

/-- Baby Bear prime `p = 2^31 − 2^27 + 1 = 2013265921`. -/
def babyBearPrime : ℕ := 2013265921

instance : NeZero babyBearPrime := ⟨by unfold babyBearPrime; decide⟩

instance : Fact (Nat.Prime babyBearPrime) :=
  ⟨by unfold babyBearPrime; native_decide⟩

/-- The Baby Bear field. We name it `F` for parity with the Plonky3 source. -/
abbrev F : Type := ZMod babyBearPrime

/-! ## Width and round counts (Plonky3 / ePrint 2023/323 defaults) -/

/-- Poseidon2 state width for Baby Bear in the Plonky3 default config.

    `abbrev` (not `def`) so that `Fin width = Fin 16` reduces transparently
    and `OfNat (Fin width) k` typeclass synthesis succeeds for numerals
    `0 ≤ k < 16` (needed by `sumAll` and the KAT). -/
abbrev width : ℕ := 16

/-- Number of external (full) rounds, total across the begin/end halves. -/
def fullRounds : ℕ := 8

/-- Half of the external rounds — applied before the partial rounds, and
    again after them. `fullRounds = 2 · halfFullRounds`. -/
def halfFullRounds : ℕ := 4

/-- Number of internal (partial) rounds for Baby Bear. -/
def partialRounds : ℕ := 13

/-! ## S-box

Baby Bear uses `x ↦ x^7`, which is a permutation of `F` because
`gcd(7, p − 1) = 1` for `p = 2013265921`. -/

/-- The Baby Bear S-box.

    Unrolled as `x^7 = x^4 · x^2 · x` to avoid `Nat.rec` expansion
    inside `^`, which `native_decide` would otherwise force at every
    of the 16 lanes × 21 rounds = 336 invocations. -/
def sbox (x : F) : F :=
  let x2 := x * x
  let x4 := x2 * x2
  x4 * x2 * x

/-! ## External MDS — real Plonky3 layer

`apply_mat4` is the 4×4 MDS block from `p3-poseidon2-0.5.2/src/external.rs`,
matrix

```
[2 3 1 1]
[1 2 3 1]
[1 1 2 3]
[3 1 1 2]
```

The external layer applies `apply_mat4` to each consecutive 4-lane block,
then adds `sums[k] = state[k] + state[k+4] + state[k+8] + state[k+12]` to
every lane congruent to `k` mod 4. -/

/-- The 4×4 Plonky3 external MDS block. -/
def applyMat4 (x : Fin 4 → F) : Fin 4 → F :=
  let x0 := x 0
  let x1 := x 1
  let x2 := x 2
  let x3 := x 3
  fun i => match i with
    | ⟨0, _⟩ => 2*x0 + 3*x1 + x2 + x3
    | ⟨1, _⟩ => x0 + 2*x1 + 3*x2 + x3
    | ⟨2, _⟩ => x0 + x1 + 2*x2 + 3*x3
    | ⟨3, _⟩ => 3*x0 + x1 + x2 + 2*x3

/-- Slice four consecutive lanes of the state. -/
def block4 (state : Fin width → F) (b : Fin 4) : Fin 4 → F :=
  fun j => state ⟨4 * b.val + j.val, by
    have hb : b.val < 4 := b.isLt
    have hj : j.val < 4 := j.isLt
    unfold width
    omega⟩

/-- External MDS layer (real Plonky3 width-16 external).

* Step 1: apply `applyMat4` to each block of four consecutive lanes.
* Step 2: for each lane `i`, add `sum_{j ≡ i mod 4} state'[j]`. -/
def externalMDS (state : Fin width → F) : Fin width → F :=
  let s' : Fin width → F := fun i =>
    let b : Fin 4 := ⟨i.val / 4, by
      have hi : i.val < width := i.isLt
      unfold width at hi
      omega⟩
    let inB : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
    applyMat4 (block4 state b) inB
  let sums : Fin 4 → F := fun k =>
    s' ⟨k.val,     by have := k.isLt; unfold width; omega⟩ +
    s' ⟨k.val + 4, by have := k.isLt; unfold width; omega⟩ +
    s' ⟨k.val + 8, by have := k.isLt; unfold width; omega⟩ +
    s' ⟨k.val + 12, by have := k.isLt; unfold width; omega⟩
  fun i =>
    let inB : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
    s' i + sums inB

/-! ## Internal MDS — real Plonky3 layer

The internal matrix is `M_I = 1·1ᵀ + Diag(V)` (NOT the identity — `1·1ᵀ`
is the all-ones matrix). For `state` with elementwise sum `Σ`:

```
(M_I · state)[i] = Σ + V[i] · state[i]
```

with diagonal

```
V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4,
     1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]
```

Source: `p3-baby-bear-0.5.2/src/poseidon2.rs::internal_layer_mat_mul` for
`WIDTH = 16`. -/

/-- The width-16 internal diagonal `V` from Plonky3, as canonical
    residues in `[0, p)`. Computed by hand from `p = 2^31 − 2^27 + 1`:

    * `inv(2)   = (p+1)/2     = 1006632961`
    * `inv(4)   = (3p+1)/4    = 1509949441`
    * `inv(8)   = (7p+1)/8    = 1761607681`
    * `inv(16)  = (15p+1)/16  = 1887436801`
    * `inv(256) = (255p+1)/256 = 2005401601`
    * `inv(2^27)= p − 15      = 2013265906`  (uses p−1 = 15·2^27)
    * negatives: `−x = p − x`. -/
def diagV : Fin width → F
  | ⟨0,  _⟩ => 2013265919   -- −2
  | ⟨1,  _⟩ => 1
  | ⟨2,  _⟩ => 2
  | ⟨3,  _⟩ => 1006632961   -- 1/2
  | ⟨4,  _⟩ => 3
  | ⟨5,  _⟩ => 4
  | ⟨6,  _⟩ => 1006632960   -- −1/2
  | ⟨7,  _⟩ => 2013265918   -- −3
  | ⟨8,  _⟩ => 2013265917   -- −4
  | ⟨9,  _⟩ => 2005401601   -- 1/2^8
  | ⟨10, _⟩ => 1509949441   -- 1/4
  | ⟨11, _⟩ => 1761607681   -- 1/8
  | ⟨12, _⟩ => 2013265906   -- 1/2^27
  | ⟨13, _⟩ => 7864320      -- −1/2^8
  | ⟨14, _⟩ => 125829120    -- −1/16
  | ⟨15, _⟩ => 15           -- −1/2^27
  | ⟨n+16, h⟩ => absurd h (by unfold width; omega)

/-- Elementwise sum of all 16 state lanes (explicit unfolding so that
    `native_decide` reduces without going through `Finset.fold`). -/
def sumAll (state : Fin width → F) : F :=
  state 0 + state 1 + state 2 + state 3 +
  state 4 + state 5 + state 6 + state 7 +
  state 8 + state 9 + state 10 + state 11 +
  state 12 + state 13 + state 14 + state 15

/-- Internal MDS layer (real Plonky3 width-16 internal).

```
internalMDS(state)[i] = sumAll(state) + V[i] · state[i]
```
-/
def internalMDS (state : Fin width → F) : Fin width → F :=
  let s_sum := sumAll state
  fun i => s_sum + diagV i * state i

/-! ## Round constants — real Plonky3 values

Constants from `p3-baby-bear-0.5.2/src/poseidon2.rs`:

* `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`: 4 vectors × 16 lanes
  (the first half of the external rounds).
* `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`: 4 vectors × 16 lanes
  (the second half).
* `BABYBEAR_POSEIDON2_RC_16_INTERNAL`: 13 scalars (the partial rounds).

Each entry is a canonical residue in `[0, p)`. -/

/-- External round constants, first half (rounds 0–3). -/
def rcExternalInitial : Fin halfFullRounds → Fin width → F := ![
  ![0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
    0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
    0x221e2e36, 0x1ab7202e],
  ![0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
    0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
    0x52eb6ba2, 0x50642905],
  ![0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
    0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
    0x29fbda49, 0x018afffd],
  ![0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
    0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
    0x2cc78315, 0x1e36ea47]]

/-- External round constants, second half (rounds 4–7). -/
def rcExternalFinal : Fin halfFullRounds → Fin width → F := ![
  ![0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
    0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
    0x6a2d3d10, 0x20523767],
  ![0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
    0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
    0x49a12590, 0x35ec52a1],
  ![0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
    0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
    0x45e1547b, 0x4a8db2ab],
  ![0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
    0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
    0x3c8bcd87, 0x608758b8]]

/-- All 8 external round-constant vectors, indexed in order: rounds 0–3 are
    the initial half, rounds 4–7 are the final half. -/
def fullRoundConstants : Fin fullRounds → Fin width → F :=
  fun r =>
    if h : r.val < halfFullRounds then
      rcExternalInitial ⟨r.val, h⟩
    else
      have h' : r.val - halfFullRounds < halfFullRounds := by
        have := r.isLt
        unfold fullRounds halfFullRounds at *
        omega
      rcExternalFinal ⟨r.val - halfFullRounds, h'⟩

/-- The 13 internal round constants for width-16 Baby Bear. -/
def partialRoundConstants : Fin partialRounds → F := ![
  (0x5a8053c0 : F), 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb,
  0x61210ce0, 0x3c318939, 0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d]

/-! ## Round primitives -/

/-- Add a round constant vector elementwise to the state. -/
def addRoundConstants (state c : Fin width → F) : Fin width → F :=
  fun i => state i + c i

/-- Apply the S-box to every lane of the state. -/
def sboxLayer (state : Fin width → F) : Fin width → F :=
  fun i => sbox (state i)

/-- Apply the S-box to lane 0 only, leaving the rest untouched.
    Used by the internal (partial) rounds. -/
def sboxLane0 (state : Fin width → F) : Fin width → F :=
  fun i => if i.val = 0 then sbox (state i) else state i

/-- One external (full) round: add constants, S-box every lane, external MDS. -/
def externalRound (state : Fin width → F) (c : Fin width → F) :
    Fin width → F :=
  externalMDS (sboxLayer (addRoundConstants state c))

/-- One internal (partial) round: add constant to lane 0, S-box lane 0,
    internal MDS. -/
def internalRound (state : Fin width → F) (c : F) : Fin width → F :=
  let state' := fun i => if i.val = 0 then state i + c else state i
  internalMDS (sboxLane0 state')

/-! ## Iterated round application -/

/-- Apply the first `n` external rounds (for `n ≤ halfFullRounds`),
    using the first `n` rows of `fullRoundConstants`. -/
def applyExternalPrefix (n : ℕ) (_h : n ≤ fullRounds)
    (state : Fin width → F) : Fin width → F :=
  Nat.rec (motive := fun _ => Fin width → F) state
    (fun k acc =>
      if hk : k < fullRounds then
        externalRound acc (fullRoundConstants ⟨k, hk⟩)
      else acc) n

/-- Apply all `partialRounds` internal rounds in sequence. -/
def applyAllPartialRounds (state : Fin width → F) : Fin width → F :=
  Nat.rec (motive := fun _ => Fin width → F) state
    (fun k acc =>
      if hk : k < partialRounds then
        internalRound acc (partialRoundConstants ⟨k, hk⟩)
      else acc) partialRounds

/-- Apply the second half of external rounds (indices `halfFullRounds` up to
    `fullRounds`). -/
def applyExternalSuffix (state : Fin width → F) : Fin width → F :=
  Nat.rec (motive := fun _ => Fin width → F) state
    (fun k acc =>
      let idx := halfFullRounds + k
      if hk : idx < fullRounds then
        externalRound acc (fullRoundConstants ⟨idx, hk⟩)
      else acc) halfFullRounds

/-! ## The permutation -/

/-- The Poseidon2 permutation on a 16-lane Baby Bear state, with real
    Plonky3 round constants and real MDS layers.

    **Pre-permutation external mixing**: Plonky3 applies `externalMDS` to
    the input *before* the first round constant addition (`permute_state`
    in `p3-poseidon2/src/lib.rs`). We follow that. -/
def poseidon2BabyBearPermute (state : Fin width → F) : Fin width → F :=
  let s₀ := externalMDS state                 -- pre-mix
  let s₁ := applyExternalPrefix halfFullRounds (by decide) s₀
  let s₂ := applyAllPartialRounds s₁
  applyExternalSuffix s₂

/-! ## 2-to-1 compression and sponge hash -/

/-- 2-to-1 compression. Output is `(Poseidon2(left, right, 0, …, 0))[0]`. -/
def poseidon2BabyBearCompress (left right : F) : F :=
  let state : Fin width → F := fun i =>
    if i.val = 0 then left
    else if i.val = 1 then right
    else 0
  (poseidon2BabyBearPermute state) ⟨0, by decide⟩

/-! ### Sponge hash -/

/-- Sponge rate — number of input field elements absorbed per permutation
    call. -/
def rate : ℕ := 8

/-- Initial sponge state: all zeros. -/
def initialSpongeState : Fin width → F := fun _ => 0

/-- Absorb up to `rate` elements from a list into the rate portion of the
    state by elementwise addition, then run the permutation. -/
def absorbBlock (state : Fin width → F) (block : List F) : Fin width → F :=
  let state' : Fin width → F := fun i =>
    if i.val < rate then
      match block[i.val]? with
      | some x => state i + x
      | none => state i
    else state i
  poseidon2BabyBearPermute state'

/-- Split a list into chunks of size `rate`. -/
def chunkInput : List F → List (List F)
  | [] => []
  | x :: xs => (x :: xs).take rate :: chunkInput ((x :: xs).drop rate)
  termination_by xs => xs.length
  decreasing_by
    simp only [List.length_drop, List.length_cons]
    have hr : (1 : ℕ) ≤ rate := by decide
    omega

/-- Absorb a list of blocks in order. -/
def absorbAll (state : Fin width → F) : List (List F) → Fin width → F
  | [] => state
  | b :: bs => absorbAll (absorbBlock state b) bs

/-- Sponge hash: absorb all input chunks then squeeze lane 0. -/
def poseidon2BabyBearHash (input : List F) : F :=
  let final := absorbAll initialSpongeState (chunkInput input)
  final ⟨0, by decide⟩

/-! ## KAT (known-answer-test) data — Plonky3 reference vector

From `test_default_babybear_poseidon2_width_16` in
`p3-baby-bear-0.5.2/src/poseidon2.rs::tests`. -/

/-- The reference test input. -/
def katInput : Fin width → F := ![
  (894848333 : F), 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
  120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443,
  227047920, 1783754913]

/-- The reference test expected output (from the Plonky3 test, with
    `default_babybear_poseidon2_16`). -/
def katExpected : Fin width → F := ![
  (516096821 : F), 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906,
  563338433, 319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758,
  1052633829, 1344246938]

/-- **KAT cross-check** *(still pending after two close-out attempts;
    `native_decide` times out >8 min even with explicit-`x^7` sbox,
    unrolled state sum, and numeric `diagV`)*.

    Root cause: `ZMod p`'s multiplication is symbolic in the kernel
    (each `*` opens to `Fin.mk (·.val * ·.val % p) _` with a fresh
    proof obligation), and the permutation's 21 rounds × 16 lanes
    chain those operations into a term too large for `native_decide`'s
    bytecode interpreter at this `p`.

    Two paths remain open:

    1. Replicate the permutation at the raw-`ℕ` level (`% p`
       arithmetic, `Array ℕ` state) and KAT-check that. The `F`-level
       definition becomes a thin wrapper. Verification cost drops to
       native-machine arithmetic.
    2. Drive the KAT through the catcrypt Rust-cmd extraction
       pipeline (compile the permutation to MLIR/LLVM and KAT-check
       the binary against Plonky3's). This is what
       `high-speed-crypto-in-lean` skill exists for.

    Statement (for reference):
    ```
    poseidon2BabyBearPermute katInput = katExpected
    ```
    The placeholder below is `trivial : True` so this file builds
    cleanly while the KAT is the only remaining gap. -/
theorem kat_pending : True := trivial

end CatCrypt.Crypto.Hash.Poseidon2.BabyBear
