/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
public import CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
public import CatCrypt.Crypto.Hash.Poseidon2.BabyBear

/-!
# CONCRETE realizers for the Poseidon2 permutation and 2-to-1 compression — KAT-free

The Poseidon2-over-Baby-Bear permutation (`poseidon2BabyBearPermute`) and the
2-to-1 compression (`poseidon2BabyBearCompress`) are the leaf primitives of the
STARK / Plonky3 / Merkle ZK-friendly hash stack.  A leaf-bytes **KAT** would
*assert* that the emitted kernel's bytes decode to those specs (the upstream
`test_default_babybear_poseidon2_width_16` reference vector).  This module turns
that assertion into a **theorem** for a concrete, spec-computing realizer with a
verified byte codec — mirroring `ConcreteHashRealizer` (Keccak / SHA-256) and
`ConcreteSymFieldRealizer` (AES / field add-mul), but for the Poseidon2 family.

The encoding KAT is a theorem here: it covers STARK / Plonky3 / Merkle ZK
protocols whose Merkle-tree compression and sponge absorb are Poseidon2 calls.

We exhibit, for each Poseidon2 primitive:

* a concrete `RustVal`-byte codec (a real byte array, not a constructor wrapping
  the function), per-lane base-256 (4 bytes per Baby Bear field element — the
  prime `p = 2013265921 < 2^31 < 2^32` fits in 4 bytes), and
* a **proved** round-trip `decode ∘ encode = id` for **every** input (the
  byte-level fact a KAT would merely assert), and
* an **unconditional** realization theorem (`KernelRealizesT` for the unary
  permutation over `.TBytes 64`, `KernelRealizes2` for the binary compression
  over `.TFp`), with **no** KAT hypothesis and **no** abstract section
  assumption.

## The carriers

* **Permutation** (`Fin 16 → F`, 16 lanes × 4 bytes = 64 bytes): the carrier is
  `.TBytes 64` (`RustVal (.TBytes 64) = Fin 64 → BitVec 8`).  No round-trip can
  exist on the 48-byte `.TFp` carrier (a faithful injection of 16 × 31 = 496
  bits needs 62 bytes, above 48 — pigeonhole), so we use the carrier-parametric
  `KernelRealizesT` (`ConcreteHashRealizer`) at `.TBytes 64`.
* **Compression** (`F → F → F`, a single Baby Bear element per operand): the
  carrier is `.TFp` (48 bytes ≥ 4), reusing `ConcreteSymFieldRealizer`'s
  `decodeF`/`encodeF` field codec at `width = 4`, `q = babyBearPrime`, whose
  base-256 round-trip `decodeF_encodeF` is already a theorem.

## Scope — what this proves and what it does NOT

* **Proved (unconditional Lean theorem):** there are *concrete*, round-trip
  -verified byte codecs and *concrete*, spec-computing realizer `LeafSpec`s
  under which the Poseidon2 permutation and compression realizations hold for
  **all** inputs — strictly stronger than *assuming* a KAT, because the
  byte-level decode-equals-spec fact is a theorem here, not a test vector.
* **NOT proved (outside the scope):** that the *jasmin-emitted machine
  bytes* of the real Poseidon2 kernels equal these realizers.  That is the
  owned-machine-code route, outside this module.  This module removes the
  *encoding* KAT (the `decode ∘ encode = id` assumption); it does **not**
  remove the *machine-code* obligation, nor the upstream Plonky3 reference-
  vector cross-check ("Known-answer check" in `BabyBear.lean`).

## References
* Grassi et al., *Poseidon2*, ePrint 2023/323.
* Plonky3 — `p3-baby-bear` / `p3-poseidon2` crates, v0.5.2.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcretePoseidon2Realizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Hash.Poseidon2.BabyBear

/-! ## §0  The Baby Bear prime fits 4 bytes -/

/-- The Baby Bear prime `p = 2013265921 < 2^31 < 2^(8·4) = 2^32`, so a single
    field element fits in a 4-byte base-256 codec. -/
theorem babyBearPrime_lt : babyBearPrime < 2 ^ (8 * 4) := by
  unfold babyBearPrime; decide

/-! ## §1  Permutation: a per-lane base-256 codec over `.TBytes 64`

The state is `Fin 16 → F` (16 Baby Bear lanes).  We lay each lane into 4
consecutive little-endian base-256 bytes: lane `ℓ` occupies carrier bytes
`[4ℓ, 4ℓ+4)`, byte `4ℓ+d` holding `(lane.val / 256^d) % 256`.  `decodeP` reads
those 4 bytes back base-256, mod `p`.  The round-trip is the per-lane base-256
digit reconstruction (`base256_digit_sum`), valid because `p < 2^32`. -/

/-- Encode a 16-lane Baby Bear state into 64 little-endian base-256 bytes:
    byte `b` is digit `b % 4` of lane `b / 4`. -/
def encodeP (s : Fin width → F) : RustVal (.TBytes 64) :=
  fun b => BitVec.ofNat 8
    (((s ⟨b.val / 4, by have h : b.val < 64 := b.isLt; unfold width; omega⟩).val
        / 256 ^ (b.val % 4)) % 256)

/-- Decode 64 bytes back into a 16-lane Baby Bear state, 4 base-256 bytes per
    lane, little-endian, reduced mod `p`. -/
def decodeP (a : RustVal (.TBytes 64)) : Fin width → F :=
  fun i => ((Finset.range 4).sum
    (fun j => 256 ^ j *
      (a ⟨(4 * i.val + j) % 64, Nat.mod_lt _ (by decide)⟩).toNat) : ℕ)

/-- **The verified Poseidon2-permutation round-trip (the crux).**  Decoding the
    concrete 64-byte base-256 encoding of any 16-lane Baby Bear state returns the
    state unchanged — for **all** inputs.  The byte-level fact a KAT would merely
    *assert*; here a theorem, per lane via `base256_digit_sum` and
    `p < 2^32`. -/
theorem decodeP_encodeP (s : Fin width → F) : decodeP (encodeP s) = s := by
  funext i
  simp only [decodeP, encodeP]
  have hi : i.val < 16 := by have := i.isLt; unfold width at this; exact this
  -- Each carrier byte slot `(4·i+j) % 64 = 4·i+j` (for `j < 4`) reads back
  -- `(lane.val / 256^j) % 256` from lane `i`, since `(4·i+j)/4 = i`, `(4·i+j)%4 = j`.
  have hbytes : ∀ j ∈ Finset.range 4,
      256 ^ j *
        (BitVec.ofNat 8
          (((s ⟨((4 * i.val + j) % 64) / 4,
              by have h : (4 * i.val + j) % 64 < 64 := Nat.mod_lt _ (by decide)
                 unfold width; omega⟩).val
              / 256 ^ (((4 * i.val + j) % 64) % 4)) % 256)).toNat
      = 256 ^ j * (((s i).val / 256 ^ j) % 256) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h64 : (4 * i.val + j) % 64 = 4 * i.val + j := Nat.mod_eq_of_lt (by omega)
    have hdiv : (4 * i.val + j) / 4 = i.val := by omega
    have hmod : (4 * i.val + j) % 4 = j := by omega
    have hidx : (⟨((4 * i.val + j) % 64) / 4, by
        have h : (4 * i.val + j) % 64 < 64 := Nat.mod_lt _ (by decide)
        unfold width; omega⟩ : Fin width) = i := by
      apply Fin.ext; simp only [h64, hdiv]
    rw [hidx, h64, hmod, BitVec.toNat_ofNat]
    have hlt : ((s i).val / 256 ^ j) % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt hlt]
  -- The base-256 digit sum reconstructs `(s i).val` since `(s i).val < 256^4`.
  have key : (Finset.range 4).sum
      (fun j => 256 ^ j *
        (BitVec.ofNat 8
          (((s ⟨((4 * i.val + j) % 64) / 4,
              by have h : (4 * i.val + j) % 64 < 64 := Nat.mod_lt _ (by decide)
                 unfold width; omega⟩).val
              / 256 ^ (((4 * i.val + j) % 64) % 4)) % 256)).toNat)
      = (s i).val := by
    rw [Finset.sum_congr rfl hbytes]
    have hxlt : (s i).val < 256 ^ 4 := by
      rw [show (256 : ℕ) ^ 4 = 2 ^ (8 * 4) from by norm_num]
      exact lt_of_lt_of_le (ZMod.val_lt (s i)) (le_of_lt babyBearPrime_lt)
    rw [base256_digit_sum (s i).val 4, Nat.mod_eq_of_lt hxlt]
  rw [key, ZMod.natCast_val, ZMod.cast_id]

/-- **Poseidon2 permutation realization — UNCONDITIONAL.**  For the concrete
    realizer `specLeafSpecT (.TBytes 64) decodeP encodeP poseidon2BabyBearPermute
    …` and the round-trip-verified 64-byte base-256 codec, the kernel realization
    `KernelRealizesT (.TBytes 64) decodeP poseidon2BabyBearPermute …` holds for
    every input.  No KAT hypothesis and no abstract `decode ∘ encode = id`
    assumption: the section is the theorem `decodeP_encodeP`.

    What is **not** proved here: that the jasmin-emitted machine bytes of the
    real Poseidon2 permutation kernel equal this realizer (the owned-machine-code
    route, outside this module). -/
theorem poseidon2_perm_realizes_concrete (limbStore : LimbStoreSpec) :
    KernelRealizesT (.TBytes 64) decodeP poseidon2BabyBearPermute
      "poseidon2_babybear_permute"
      (specLeafSpecT (.TBytes 64) decodeP encodeP poseidon2BabyBearPermute
        "poseidon2_babybear_permute" limbStore) :=
  kernelRealizesT_concrete (.TBytes 64) decodeP encodeP poseidon2BabyBearPermute
    decodeP_encodeP "poseidon2_babybear_permute" limbStore

/-! ## §2  Compression: the field codec over `.TFp`, reusing `decodeF`/`encodeF`

The 2-to-1 compression `poseidon2BabyBearCompress : F → F → F` is a binary
operation on a single Baby Bear element (`F = ZMod babyBearPrime`).  It therefore
fits the existing single-element base-256 field codec (`decodeF`/`encodeF` from
`ConcreteSymFieldRealizer`) at `width = 4`, whose round-trip `decodeF_encodeF` is
already a theorem (valid since `babyBearPrime < 2^(8·4)`).  We instantiate the
generic binary realizer at this codec and at the compression op. -/

/-- The concrete compression realizer `LeafSpec`: decode the two `.TFp` operands
    via the 4-byte field codec, apply `poseidon2BabyBearCompress`, re-encode. -/
def compressLeafSpec (leaf : String) (limbStore : LimbStoreSpec) : LeafSpec :=
  fieldBinopLeafSpec (q := babyBearPrime) 4 poseidon2BabyBearCompress leaf limbStore

/-- **Poseidon2 2-to-1 compression realization — UNCONDITIONAL.**  For the
    concrete realizer `compressLeafSpec …` and the round-trip-verified 4-byte
    base-256 field codec `decodeF 4`, the binary kernel realization
    `KernelRealizes2 (decodeF 4) poseidon2BabyBearCompress …` holds for every
    input.  No KAT hypothesis and no abstract section assumption: the section is
    the theorem `decodeF_encodeF` at `width = 4`, `q = babyBearPrime`.

    What is **not** proved here: that the jasmin-emitted machine bytes of the
    real Poseidon2 compression kernel equal this realizer (the owned-machine-code
    route, outside this module). -/
theorem poseidon2_compress_realizes_concrete (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := babyBearPrime) 4) poseidon2BabyBearCompress leaf
      (compressLeafSpec leaf limbStore) :=
  fieldBinop_realizes_concrete (q := babyBearPrime) 4 (by decide) babyBearPrime_lt
    poseidon2BabyBearCompress leaf limbStore

end CatCrypt.Crypto.SecureCompilation.ConcretePoseidon2Realizer
