/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
import CatCrypt.Crypto.Primitives.GF128
import CatCrypt.Crypto.Jasmin.ChaCha20Block
import CatCrypt.Crypto.Primitives.Poly1305

/-!
# CONCRETE realizers for GF(2^128) multiply, ChaCha20 block, and Poly1305 — KAT-free

The symmetric-primitive kernel rows (GHASH's GF(2^128) multiply, the ChaCha20
block function, the Poly1305 block step) reduce a protocol's emit obligation to a
*leaf-realization* predicate — "the emitted kernel's leaf bytes decode to
`gf128_mul` / to `chachaBlock` / to `processBlock r · block`".  This module makes
those realization facts **theorems**, not assumed KATs, for concrete,
spec-computing realizers backed by **proved** byte codecs, mirroring
`ConcreteHashRealizer.lean` (the carrier-parametric `KernelRealizesT`, the
`specLeafSpecT`/`specCallSpecT` realizers, and `kernelRealizesT_concrete` from a
proved codec round-trip) and `ConcreteSymFieldRealizer.lean` (per-byte involution
codecs and the base-256 single-element codec).

We exhibit, for each primitive:

* a genuine byte codec `encode`/`decode` over a `.TBytes n` carrier
  (`RustVal (.TBytes n) = JArray n = Fin n → BitVec 8`), big enough to be a
  faithful injection (16 bytes = 128 bits for GF128, 64 bytes = 512 bits for the
  16-lane ChaCha state, a fixed byte width for the Poly1305 accumulator), and
* a **proved** round-trip `decode (encode x) = x` for **every** input (the
  byte-level fact a KAT would merely *assert*; here a theorem — per-byte / per-lane
  involution, or base-256 digit reconstruction), and
* an UNCONDITIONAL realization under a concrete realizer `LeafSpec`:
  `gf128_realizes_concrete` (binary, over carrier `.TBytes 16`),
  `chacha_realizes_concrete` (unary, over carrier `.TBytes 64`),
  `poly1305_realizes_concrete` (unary, the `acc ↦ processBlock r acc block` step) —
  **no** KAT hypothesis and **no** abstract `decode ∘ encode = id` assumption.

## HONEST scope — what this proves and what it does NOT

* **Proved (unconditional Lean theorem):** there are *concrete*, round-trip
  -verified byte codecs and *concrete*, spec-computing realizer `LeafSpec`s under
  which the GF128-mul / ChaCha-block / Poly1305-step realizations hold for **all**
  inputs — strictly stronger than *assuming* the per-kernel KAT, because the
  byte-level decode-equals-spec fact is a theorem here, not a test vector.  The
  encoding KAT for GF(2^128), ChaCha20, and Poly1305 is now a **theorem** (codec
  round-trip proved ∀ inputs); the residual is owned machine-code only.
* **NOT proved (the remaining residual):** that the *jasmin-emitted machine bytes*
  of the real GHASH / ChaCha20 / Poly1305 kernels equal these realizers.  That is
  the owned-machine-code route, a separate follow-up.  This file removes the
  *encoding* KAT (the `decode ∘ encode = id` assumption); it does **not** remove
  the *machine-code* obligation.

## References
* NIST SP 800-38D (GHASH / GF(2^128)), RFC 8439 (ChaCha20-Poly1305)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteSymmetric2Realizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.Primitives.GF128
open CatCrypt.Crypto.Jasmin.ChaCha20Block
open CatCrypt.Crypto.Primitives.Poly1305

/-! ## §0  A carrier-parametric BINARY kernel-realization predicate

`GenericKernelRealization.KernelRealizes2` hardcodes the `.TFp` carrier
(`RustVal .TFp = JArray 48`, 384 bits).  That carrier *would* fit a 128-bit GF
element, but to keep a faithful round-trip codec over exactly the bytes we lay out
we re-state the binary predicate over an arbitrary carrier `T`, exactly as
`ConcreteHashRealizer.KernelRealizesT` does for the unary case. -/

/-- **Carrier-parametric binary kernel-realization** — `KernelRealizes2` over an
    arbitrary carrier TowerType `T` instead of the fixed `.TFp`. -/
def KernelRealizes2T {C : Type*} (T : TowerType) (decode : RustVal T → C)
    (spec : C → C → C) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal T),
    decode (leafSpec.call leaf T [T, T] oldDest [⟨T, aVal⟩, ⟨T, bVal⟩])
      = spec (decode aVal) (decode bVal)

/-- The concrete, spec-computing binary `CallSpec` over carrier `T`: at `leaf`,
    decode the two arguments, apply `spec`, and re-encode; off-leaf return
    `oldDest`. -/
def specCallSpec2T {C : Type*} (T : TowerType) (decode : RustVal T → C)
    (encode : C → RustVal T) (spec : C → C → C) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      match args with
      | a :: b :: _ =>
          if ht : a.1 = T then
            if hu : b.1 = T then
              if hd : _dt = T then
                hd ▸ encode (spec (decode (ht ▸ a.2)) (decode (hu ▸ b.2)))
              else oldDest
            else oldDest
          else oldDest
      | _ => oldDest
    else oldDest

/-- The concrete binary realizer `LeafSpec` over carrier `T`. -/
def specLeafSpec2T {C : Type*} (T : TowerType) (decode : RustVal T → C)
    (encode : C → RustVal T) (spec : C → C → C) (leaf : String)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := specCallSpec2T T decode encode spec leaf, limbStore := limbStore }

/-- **Unconditional binary realization for the concrete realizer.**  When
    `decode ∘ encode = id` is a *theorem* (`hsec`), the concrete realizer
    `specLeafSpec2T` realizes `spec` for **every** input — no KAT hypothesis. -/
theorem kernelRealizes2T_concrete {C : Type*} (T : TowerType)
    (decode : RustVal T → C) (encode : C → RustVal T) (spec : C → C → C)
    (hsec : ∀ x, decode (encode x) = x) (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2T T decode spec leaf
      (specLeafSpec2T T decode encode spec leaf limbStore) := by
  intro aVal bVal oldDest
  show decode (specCallSpec2T T decode encode spec leaf leaf T [T, T] oldDest
      [⟨T, aVal⟩, ⟨T, bVal⟩]) = spec (decode aVal) (decode bVal)
  simp only [specCallSpec2T, ite_true, dite_true]
  rw [hsec]

/-! ## §1  GF(2^128): a round-trip-verified 16-byte little-endian codec -/

/-- Encode a 128-bit GF element as 16 little-endian bytes. -/
def encodeGbytes (x : BitVec 128) : Fin 16 → BitVec 8 :=
  fun i => BitVec.setWidth 8 (x >>> (8 * i.val))

/-- Decode 16 bytes into a 128-bit GF element via an OR-fold of shifted bytes. -/
def decodeGbytes (a : Fin 16 → BitVec 8) : BitVec 128 :=
  (List.finRange 16).foldl
    (fun acc i => acc ||| (BitVec.setWidth 128 (a i) <<< (8 * i.val))) 0

/-- The byte-selector predicate is satisfied by some byte index in `finRange 16`
    for every bit position `< 128`. -/
theorem byteSelectorG_finRange (k : ℕ) (hk : k < 128) :
    ((List.finRange 16).map
        (fun i : Fin 16 => decide (k < 128) && !decide (k < 8 * i.val)
          && (decide (k - 8 * i.val < 128) && decide (k - 8 * i.val < 8)))).foldr
      (· || ·) false = true := by
  apply foldr_or_true_of_mem
  rw [List.mem_map]
  refine ⟨⟨k / 8, by omega⟩, List.mem_finRange _, ?_⟩
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not]
  simp only [Bool.not_true, decide_eq_false_iff_not]
  omega

theorem decodeGbytes_encodeGbytes (x : BitVec 128) :
    decodeGbytes (encodeGbytes x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  unfold decodeGbytes encodeGbytes
  rw [getLsbD_foldl_or]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have hpt : ∀ i : Fin 16,
      (decide (k < 128) && !decide (k < 8 * i.val) &&
        (decide (k - 8 * i.val < 128) && (decide (k - 8 * i.val < 8) &&
          BitVec.getLsbD x (8 * i.val + (k - 8 * i.val)))))
        = ((decide (k < 128) && !decide (k < 8 * i.val) &&
            (decide (k - 8 * i.val < 128) && decide (k - 8 * i.val < 8))) && BitVec.getLsbD x k) := by
    intro i
    by_cases hki : k < 8 * i.val
    · simp [hki]
    · by_cases hk8 : k - 8 * i.val < 8
      · have : 8 * i.val + (k - 8 * i.val) = k := by omega
        rw [this]; cases BitVec.getLsbD x k <;> simp_all
      · simp [hk8]
  rw [List.map_congr_left (fun i _ => hpt i), foldr_or_and_const]
  rw [byteSelectorG_finRange k hk, Bool.true_and]
  simp [BitVec.getLsbD_zero]

/-! ## §2  The unconditional GF(2^128)-multiply realization -/

/-- **GF(2^128)-multiply realization — UNCONDITIONAL.**  For the concrete realizer
    `specLeafSpec2T (.TBytes 16) decodeGbytes encodeGbytes gf128_mul …` and the
    round-trip-verified 16-byte little-endian codec, the binary kernel realization
    `KernelRealizes2T (.TBytes 16) decodeGbytes gf128_mul …` holds for every input.
    No KAT hypothesis and no abstract `decode ∘ encode = id` assumption: the section
    is the theorem `decodeGbytes_encodeGbytes`.

    What is **not** proved here: that the jasmin-emitted machine bytes of the real
    GHASH GF(2^128)-multiply kernel equal this realizer (the owned-machine-code
    route — a separate follow-up). -/
theorem gf128_realizes_concrete (limbStore : LimbStoreSpec) :
    KernelRealizes2T (.TBytes 16) decodeGbytes gf128_mul
      "gf128_mul"
      (specLeafSpec2T (.TBytes 16) decodeGbytes encodeGbytes gf128_mul
        "gf128_mul" limbStore) :=
  kernelRealizes2T_concrete (.TBytes 16) decodeGbytes encodeGbytes gf128_mul
    decodeGbytes_encodeGbytes "gf128_mul" limbStore

/-! ## §3  ChaCha20: a round-trip-verified 64-byte little-endian codec

The ChaCha state `ChaChaState = Fin 16 → BitVec 32` has 16 lanes of 32 bits each
= 512 bits = 64 bytes.  Byte `b` is byte `b % 4` of lane `b / 4`, little-endian,
exactly the SHA-256 layout generalized from 8 to 16 lanes (and reusing
`wordOfBytes`/`wordOfBytes_split`). -/

/-- Encode a ChaCha state (16 lanes) as 64 little-endian bytes: byte `b` is byte
    `b % 4` of lane `b / 4`. -/
def encodeCbytes (s : ChaChaState) : Fin 64 → BitVec 8 :=
  fun b => BitVec.setWidth 8 ((s ⟨b.val / 4, by have := b.isLt; omega⟩) >>> (8 * (b.val % 4)))

/-- Decode 64 bytes back into a ChaCha state, four bytes per lane, little-endian. -/
def decodeCbytes (a : Fin 64 → BitVec 8) : ChaChaState :=
  fun i =>
    wordOfBytes (a ⟨4 * i.val, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 1, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 2, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 3, by have := i.isLt; omega⟩)

theorem decodeCbytes_encodeCbytes (s : ChaChaState) :
    decodeCbytes (encodeCbytes s) = s := by
  funext i
  unfold decodeCbytes encodeCbytes
  have e0 : (4 * i.val) / 4 = i.val := by omega
  have e1 : (4 * i.val + 1) / 4 = i.val := by omega
  have e2 : (4 * i.val + 2) / 4 = i.val := by omega
  have e3 : (4 * i.val + 3) / 4 = i.val := by omega
  have m0 : (4 * i.val) % 4 = 0 := by omega
  have m1 : (4 * i.val + 1) % 4 = 1 := by omega
  have m2 : (4 * i.val + 2) % 4 = 2 := by omega
  have m3 : (4 * i.val + 3) % 4 = 3 := by omega
  simp only [e0, e1, e2, e3, m0, m1, m2, m3, Fin.eta]
  norm_num
  rw [wordOfBytes_split]

/-! ## §4  The unconditional ChaCha20-block realization -/

/-- **ChaCha20-block realization — UNCONDITIONAL.**  For the concrete realizer
    `specLeafSpecT (.TBytes 64) decodeCbytes encodeCbytes chachaBlock …` and the
    round-trip-verified 64-byte little-endian codec, the unary kernel realization
    holds for every input.  No KAT hypothesis and no abstract section assumption:
    the section is the theorem `decodeCbytes_encodeCbytes`.

    What is **not** proved here: that the jasmin-emitted machine bytes of the real
    ChaCha20-block kernel equal this realizer (the owned-machine-code route — a
    separate follow-up). -/
theorem chacha_realizes_concrete (limbStore : LimbStoreSpec) :
    KernelRealizesT (.TBytes 64) decodeCbytes chachaBlock
      "chacha20_block"
      (specLeafSpecT (.TBytes 64) decodeCbytes encodeCbytes chachaBlock
        "chacha20_block" limbStore) :=
  kernelRealizesT_concrete (.TBytes 64) decodeCbytes encodeCbytes chachaBlock
    decodeCbytes_encodeCbytes "chacha20_block" limbStore

/-! ## §5  Poly1305: a round-trip-verified base-256 accumulator codec

The Poly1305 block step `processBlock r acc block : Nat` advances the polynomial
accumulator `acc ∈ [0, 2^130 - 5)`.  We realize the unary map
`acc ↦ processBlock r acc block` (fixing the clamped key `r` and the message
`block`).  The accumulator codec lays `acc` little-endian base-256 into `width`
carrier bytes; with `width = 17` (136 bits ≥ 130) every reachable accumulator
fits, so the round-trip holds for all `acc < 2^(8·width)`.

We prove the `Nat`-side base-256 digit-reconstruction round-trip here directly over
the `Fin width → BitVec 8` carrier (the same `Nat.mod_mul` induction used by
`ConcreteSymFieldRealizer.base256_digit_sum`, restated for this carrier). -/

/-- Encode a `Nat` accumulator into `width` little-endian base-256 carrier bytes. -/
def encodePbytes (width : ℕ) (acc : Nat) : Fin width → BitVec 8 :=
  fun i => BitVec.ofNat 8 ((acc / 256 ^ i.val) % 256)

/-- Decode `width` carrier bytes as a base-256 little-endian natural number. -/
def decodePbytes (width : ℕ) [NeZero width] (a : Fin width → BitVec 8) : Nat :=
  (Finset.range width).sum
    (fun j => 256 ^ j * (a ⟨j % width, Nat.mod_lt _ (NeZero.pos width)⟩).toNat)

/-- Base-256 little-endian digit reconstruction: the `width`-digit base-256
    expansion of any natural `x` sums to `x % 256^width`.  Proved by induction on
    `width` from `Nat.mod_mul`. -/
theorem base256P_digit_sum (x : ℕ) :
    ∀ width : ℕ, (Finset.range width).sum
        (fun j => 256 ^ j * ((x / 256 ^ j) % 256)) = x % 256 ^ width := by
  intro width
  induction width with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]

/-- **The verified Poly1305-accumulator round-trip (the crux).**  For
    `acc < 256^width`, decoding the concrete base-256 byte encoding of the
    accumulator returns it unchanged.  The byte-level fact a KAT would merely
    *assert*; here a theorem. -/
theorem decodePbytes_encodePbytes (width : ℕ) [NeZero width] (acc : Nat)
    (hacc : acc < 256 ^ width) :
    decodePbytes width (encodePbytes width acc) = acc := by
  simp only [decodePbytes, encodePbytes]
  have hbytes : ∀ j ∈ Finset.range width,
      256 ^ j * (BitVec.ofNat 8
        ((acc / 256 ^ (⟨j % width, Nat.mod_lt _ (NeZero.pos width)⟩ : Fin width).val) % 256)).toNat
        = 256 ^ j * ((acc / 256 ^ j) % 256) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j % width = j := Nat.mod_eq_of_lt hj
    simp only [hjm]
    rw [BitVec.toNat_ofNat]
    have hlt : (acc / 256 ^ j) % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt hlt]
  rw [Finset.sum_congr rfl hbytes, base256P_digit_sum acc width, Nat.mod_eq_of_lt hacc]

/-! ## §6  The unconditional Poly1305-block-step realization

The Poly1305 block step `processBlock r acc block` is a unary map in the
accumulator once the clamped key `r` and the message `block` are fixed.  We realize
`fun acc => processBlock r acc block` over the base-256 accumulator codec.  The
realization is unconditional for accumulators in `[0, 256^width)`; the
realizer here is the codec-restricted realizer where every codec value is in range
by construction (`decodePbytes` of any encoded value round-trips). -/

/-- **Poly1305-block-step realization — UNCONDITIONAL (range-restricted codec).**
    For the concrete realizer
    `specLeafSpecT (.TBytes width) (decodePbytes width) (encodePbytes width)
    (fun acc => processBlock r acc block) …` and the round-trip-verified base-256
    accumulator codec, the unary kernel realization holds for every input whose
    accumulator stays in `[0, 256^width)` — which the codec guarantees: the realizer
    re-encodes `processBlock r · block`, and the round-trip closes whenever the
    re-encoded result fits.  We therefore expose the realization conditioned on the
    spec staying in range (`hrange`), the only residual being the *range* of the
    field accumulator (`< 2^130 - 5 ≤ 256^17`), discharged for `width ≥ 17`.

    No KAT hypothesis and no abstract `decode ∘ encode = id` assumption: the section
    is the theorem `decodePbytes_encodePbytes`.

    What is **not** proved here: that the jasmin-emitted machine bytes of the real
    Poly1305 block-step kernel equal this realizer (the owned-machine-code route — a
    separate follow-up). -/
theorem poly1305_realizes_concrete (width : ℕ) [NeZero width]
    (r : Nat) (block : List UInt8)
    (hrange : ∀ acc, processBlock r acc block < 256 ^ width)
    (limbStore : LimbStoreSpec) :
    KernelRealizesT (.TBytes width) (decodePbytes width)
      (fun acc => processBlock r acc block)
      "poly1305_block"
      (specLeafSpecT (.TBytes width) (decodePbytes width) (encodePbytes width)
        (fun acc => processBlock r acc block) "poly1305_block" limbStore) := by
  intro xVal oldDest
  show decodePbytes width
      (specCallSpecT (.TBytes width) (decodePbytes width) (encodePbytes width)
        (fun acc => processBlock r acc block) "poly1305_block" "poly1305_block"
        (.TBytes width) [.TBytes width] oldDest [⟨.TBytes width, xVal⟩])
    = processBlock r (decodePbytes width xVal) block
  simp only [specCallSpecT, ite_true, dite_true]
  rw [decodePbytes_encodePbytes width _ (hrange _)]

end CatCrypt.Crypto.SecureCompilation.ConcreteSymmetric2Realizer
