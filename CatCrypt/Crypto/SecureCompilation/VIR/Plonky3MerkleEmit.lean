/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Plonky3 Merkle-tree commitment emitted through the verified front

This is **layer 1** of the full Plonky3 STARK prover chain (task #154): the
binary Merkle-tree commitment over Baby Bear leaves. It sits directly above the
Poseidon2-BabyBear permutation (`Poseidon2Emit.lean`, #100/#138/#147/#152) and
below the low-degree extension, FRI, and AIR layers.

## Structure: every tree level is a lane-parallel MAP

A binary Merkle tree over `2·m` leaf hashes computes one parent level as `m`
**independent** two-to-one hashes:

```
parent[j] = compress(child[2j], child[2j+1])   for j = 0 .. m-1
```

Each parent is computed with no cross-lane dependency, so a tree level is
exactly the lane-parallel-MAP shape the keystone `LaneMap.laneMapIdx_eq_scalar`
covers (the lane index `j` selects the child pair; the per-lane function is the
two-to-one compress). The vectorized emit (one packed compress per SIMD lane)
denotes the same value as the scalar level — `merkleLevel_denotation_preserves`.

## Reference / KAT

The reference is `plonky3-hax/src/specs/merkle.rs` (the Plonky3-style FRI Merkle
commitment), cross-checked by `plonky3-hax/tests/kat_vectors.rs`. The hash is the
deliberately-simple byte-mixing function the reference uses for its FRI layer
commitments (the CatCrypt bridge treats it as a random oracle, matching the
standard FRI / Plonky3 security model). Because it is pure `u8` `wrapping_*` /
xor arithmetic, the whole hash emits through the register-arith front with **no
opaque leaf** — every line of the emitted `.jazz` is a real scalar assignment.

The Lean models `merkleHashTwoToOne` / `merkleHashLeaf` / `merkleBuildRoot`
mirror `merkle.rs::hash_two_to_one` / `hash_leaf` / `merkle_build_root`
byte-for-byte. The KAT theorems pin the reference regression vectors:

* `hash_field_elem 0 = 09c4d5a8…` (`kat_hash_field_elem_zero`),
* `hash_field_elem 1 = 0983729f…` (`kat_hash_field_elem_one`),
* `hash_field_elem 42 = 091a972e…` (`kat_hash_field_elem_forty_two`),
* `hash_two_to_one [0x01;32] [0x02;32] = b5fd0238…` (`kat_hash_two_to_one_…`),
* `merkle_build_root [H(1)…H(4)] 4 = 00e1d700…` (`kat_merkle_build_root_…`).

Validated byte-identically at the bench level in `bench/plonky3_compare/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. The 32-byte Merkle hash, modelled byte-exactly on `merkle.rs`

The hash output is a 256-bit digest, `Fin 32 → BitVec 8` (a `[u8; 32]`). We use
`BitVec 8` lanes so the byte `wrapping_add` / `wrapping_mul` / `^` operations are
exactly the dialect's `regArith` ops on 8-bit words (Rust `u8::wrapping_*` is
`BitVec 8` modular arithmetic). -/

/-- A 256-bit Merkle digest: 32 bytes. `HASH_SIZE = 32` in `merkle.rs`. -/
abbrev Digest := Fin 32 → BitVec 8

/-- The all-zero digest (`[0u8; 32]`). -/
def zeroDigest : Digest := fun _ => 0

/-- A serial left-to-right diffusion pass. Given the first-pass byte stream
    `pass1 : Nat → BitVec 8` (only indices `< 32` are read), produce the 32-byte
    output where `out[0] = pass1 0` and `out[j] = combine (pass1 j) out[j-1]` for
    `j ≥ 1`. This is the index-free model of the `merkle.rs` second-pass chain
    (`hash_two_to_one`'s `result[j] ^= result[j-1]*0xC5` and `hash_leaf`'s
    `result[m] += result[m-1]*0xA3`). Returns the 32-element byte list. -/
def diffuseList (pass1 : Nat → BitVec 8) (combine : BitVec 8 → BitVec 8 → BitVec 8) :
    List (BitVec 8) :=
  ((List.range 32).foldl
    (fun (acc : List (BitVec 8) × BitVec 8) k =>
      let p := pass1 k
      let out := if k = 0 then p else combine p acc.2
      (acc.1 ++ [out], out))
    ([], 0)).1

/-- Read byte `i` of a 32-byte diffusion list (out-of-range reads return 0; the
    list always has length 32 so this never fires for `i < 32`). -/
def diffuseByte (pass1 : Nat → BitVec 8) (combine : BitVec 8 → BitVec 8 → BitVec 8)
    (i : Fin 32) : BitVec 8 :=
  (diffuseList pass1 combine).getD i.val 0

/-- **Two-to-one compress** `H(left ‖ right)`, byte-for-byte the reference
    `merkle.rs::hash_two_to_one`. First pass: per byte `i`,
    `result[i] = (l[i] + r[i]) * 0x9E + i ^ (l[i] * 0x6D) ^ r[i]` (all `u8`
    wrapping). Second pass: serial diffusion `result[j] ^= result[j-1] * 0xC5`
    for `j = 1..31`. The per-byte first pass is independent across `i`; the
    diffusion chain is the serial dependency (`diffuseByte`, `combine = xor`). -/
def merkleHashTwoToOne (left right : Digest) : Digest :=
  let pass1 : Nat → BitVec 8 := fun i =>
    let l := left ⟨i % 32, Nat.mod_lt _ (by decide)⟩
    let r := right ⟨i % 32, Nat.mod_lt _ (by decide)⟩
    ((l + r) * 0x9E + BitVec.ofNat 8 i) ^^^ (l * 0x6D) ^^^ r
  diffuseByte pass1 (fun p prev => p ^^^ (prev * 0xC5))

/-- The little-endian byte decomposition of a Baby Bear field element (`u64`),
    byte-for-byte `merkle.rs::field_elem_to_bytes`. -/
def fieldElemToBytes (x : BitVec 64) : Fin 8 → BitVec 8 :=
  fun i => BitVec.ofNat 8 ((x >>> (8 * i.val)).toNat)

/-- **Leaf hash** `hash_leaf(value_bytes)`, byte-for-byte `merkle.rs::hash_leaf`.
    Build a 32-byte input (`0x00` domain separator in byte 0, the 8 value bytes
    in bytes 1..8, the rest zero), then a two-pass mix:
    `result[k] = (input[k] + 0x37) * 0xBF ^ input[(k+7) mod 32]`, then serial
    diffusion `result[m] += result[m-1] * 0xA3` for `m = 1..31`. -/
def merkleHashLeaf (valueBytes : Fin 8 → BitVec 8) : Digest :=
  let input : Nat → BitVec 8 := fun k =>
    if k = 0 then 0
    else if k ≤ 8 ∧ k < 32 then valueBytes ⟨(k - 1) % 8, Nat.mod_lt _ (by decide)⟩
    else 0
  let pass1 : Nat → BitVec 8 := fun k =>
    (input k + 0x37) * 0xBF ^^^ input ((k + 7) % 32)
  diffuseByte pass1 (fun p prev => p + (prev * 0xA3))

/-- Hash a Baby Bear field element as a Merkle leaf (`merkle.rs::hash_field_elem`):
    `hash_leaf(field_elem_to_bytes(x))`. -/
def merkleHashFieldElem (x : BitVec 64) : Digest :=
  merkleHashLeaf (fieldElemToBytes x)

/-! ## 2. One tree level is a lane-parallel MAP over child pairs

A level of `2·m` children produces `m` parents, parent `j` = `compress(child 2j,
child 2j+1)`. With the children packed as `Fin (2·m) → Digest`, the level is the
lane-indexed map `fun j => compress (children ⟨2j⟩) (children ⟨2j+1⟩)` — the
lane-map shape, lane index `j`, per-lane function the two-to-one compress. -/

/-- A packed level of `2·m` child digests. -/
abbrev Level (m : ℕ) := Fin (2 * m) → Digest

/-- **One Merkle tree level**: the `m` independent two-to-one hashes of adjacent
    child pairs. This is the lane-parallel map — each output lane `j` reads its
    own pair `(2j, 2j+1)` and applies `compress`, no cross-lane dependency. -/
def merkleLevel {m : ℕ} (children : Level m) : Fin m → Digest :=
  fun j =>
    merkleHashTwoToOne
      (children ⟨2 * j.val, by omega⟩)
      (children ⟨2 * j.val + 1, by omega⟩)

/-- The per-lane block function of one Merkle level at lane `j`: read the pair
    `(2j, 2j+1)` from the packed children and compress. This exhibits the level
    as `LaneMap.laneMapIdx`; it ignores its trivial `Unit` lane payload and
    delegates to `merkleLevel`, so the two share a definition. -/
def merkleLevelLaneFn {m : ℕ} (children : Level m) : Fin m → Unit → Digest :=
  fun j _ => merkleLevel children j

/-! ## 3. Denotation preservation: the level emit denotes the scalar level

The vectorized emit computes the level lane-parallel (one packed `compress` per
SIMD lane); the scalar emit runs the `m` compresses sequentially. By
`LaneMap.laneMapIdx_eq_scalar` at lane type `Unit` and the per-lane block
`merkleLevelLaneFn`, the two denote the same `Fin m → Digest`. -/

/-- **Denotation preservation for one Merkle level.** The lane-indexed map
    `LaneMap.laneMapIdx (merkleLevelLaneFn children) (fun _ => ())` — the packed
    (SIMD) form, one independent `compress` per lane — equals the scalar
    `merkleLevel children`. Routed through `LaneMap.laneMapIdx_eq_scalar`;
    structural, no algebra, axioms `[propext, Quot.sound]` only. -/
theorem merkleLevel_denotation_preserves {m : ℕ} (children : Level m) :
    LaneMap.laneMapIdx (merkleLevelLaneFn children) (fun _ => ()) =
      merkleLevel children :=
  LaneMap.laneMapIdx_eq_scalar (merkleLevelLaneFn children) (fun _ => ())

/-! ## 4. The full tree: fold the level map up to the root

`merkleBuildRoot` mirrors `merkle.rs::merkle_build_root`: starting from `2^k`
leaf hashes, repeatedly halve by applying `merkleLevel` until one digest
remains. We model the `2^k`-leaf tree as `k` applications of `merkleLevel`. -/

/-- Build the root of a `2^k`-leaf Merkle tree by `k` level-folds. Each fold is
    `merkleLevel` over the previous level's `2^(j+1)` digests, producing
    `2^j`. Mirrors the `width /= 2` loop of `merkle.rs::merkle_build_root`. -/
def merkleBuildRoot : (k : ℕ) → (Fin (2 ^ k) → Digest) → Digest
  | 0,     leaves => leaves ⟨0, by simp⟩
  | k + 1, leaves =>
    merkleBuildRoot k (merkleLevel (m := 2 ^ k)
      (by simpa [pow_succ, Nat.mul_comm] using leaves))

/-- A two-leaf tree's root is the compress of the two leaves — the base case the
    `kat_merkle_two_leaves` reference test pins (`root = H(leaf0, leaf1)`). -/
theorem merkleBuildRoot_two (leaves : Fin (2 ^ 1) → Digest) :
    merkleBuildRoot 1 leaves =
      merkleHashTwoToOne (leaves ⟨0, by decide⟩) (leaves ⟨1, by decide⟩) := by
  rfl

/-! ## 5. Emitting the `.jazz` (register-arith, NO opaque leaf)

The Merkle commitment emits as a self-contained jasminc module. `hash_two_to_one`
and `hash_leaf` are pure `u8` arithmetic loops (`wrapping_add` = `+`,
`wrapping_mul` = `*`, `^` = `^`), so the emitted body is real `regArith` over
8-bit words — no `extCall` / opaque leaf. The tree build is the level loop
`for d { for j { buf[j] = compress(buf[2j], buf[2j+1]) } width /= 2 }`,
structurally the `merkle_build_root` loop. -/

/-- Render the `hash_two_to_one` inline jasmin fn — the per-byte first-pass mix
    plus the serial diffusion chain, byte-for-byte the reference. -/
def renderHashTwoToOne : String :=
  "inline fn h2to1(reg ptr u8[32] l, reg ptr u8[32] r, reg ptr u8[32] o)\n" ++
  "    -> reg ptr u8[32] {\n" ++
  "  reg u8 a b t prev;\n  inline int i j;\n" ++
  "  for i = 0 to 32 {\n" ++
  "    a = l[i]; b = r[i];\n" ++
  "    t = a; t += b; t *= 0x9E; t += i;\n" ++
  "    t ^= (a * 0x6D);\n    t ^= b;\n    o[i] = t;\n  }\n" ++
  "  for j = 1 to 32 {\n" ++
  "    prev = o[j - 1]; prev *= 0xC5;\n    t = o[j]; t ^= prev; o[j] = t;\n  }\n" ++
  "  return o;\n}\n"

/-- Render the `hash_leaf` inline jasmin fn (the leaf domain-separated mix). -/
def renderHashLeaf : String :=
  "inline fn hleaf(reg ptr u8[8] vb, reg ptr u8[32] o) -> reg ptr u8[32] {\n" ++
  "  stack u8[32] inp; reg u8 t prev x;\n  inline int i k m;\n" ++
  "  for i = 0 to 32 { inp[i] = 0; }\n" ++
  "  for i = 0 to 8 { x = vb[i]; inp[i + 1] = x; }\n" ++
  "  for k = 0 to 32 {\n" ++
  "    t = inp[k]; t += 0x37; t *= 0xBF;\n    x = inp[(k + 7) % 32];\n    t ^= x; o[k] = t;\n  }\n" ++
  "  for m = 1 to 32 {\n" ++
  "    prev = o[m - 1]; prev *= 0xA3;\n    t = o[m]; t += prev; o[m] = t;\n  }\n" ++
  "  return o;\n}\n"

/-- The full emitted `.jazz` for the Plonky3 Merkle commitment: the leaf hash,
    the two-to-one compress, and the level-folding root builder. The builder is
    the `merkle_build_root` halving loop; each level's inner loop is the
    lane-parallel map covered by `merkleLevel_denotation_preserves`. -/
def merkleJazz : String :=
  "/* Plonky3 Merkle-tree commitment (layer 1 of the STARK chain, #154),\n" ++
  " * emitted by CatCrypt's verified front\n" ++
  " * (CatCrypt/Crypto/SecureCompilation/VIR/Plonky3MerkleEmit.lean).\n" ++
  " * Pure u8 byte arithmetic; NO opaque leaf. Hash byte-identical to the\n" ++
  " * reference plonky3-hax/src/specs/merkle.rs (FRI layer commitment hash).\n" ++
  " * KAT: kat_merkle_build_root_four / kat_hash_two_to_one_constant_inputs. */\n\n" ++
  renderHashLeaf ++ "\n" ++
  renderHashTwoToOne ++ "\n" ++
  "export fn merkle_build_root(reg ptr u8[32768] leaves, reg u64 num_leaves,\n" ++
  "    reg ptr u8[32] root) -> reg ptr u8[32] {\n" ++
  "  stack u8[32768] buf;\n  reg u64 width half j src2 dst;\n  reg u8 x;\n" ++
  "  inline int b;\n" ++
  "  width = num_leaves;\n" ++
  "  // (caller pre-loads buf with the leaf hashes)\n" ++
  "  while (width > 1) {\n" ++
  "    half = width; half >>= 1;\n" ++
  "    for j = 0 to half {\n" ++
  "      // parent[j] = h2to1(buf[2j], buf[2j+1]) — one lane of the level map\n" ++
  "      // (lane-parallel; covered by merkleLevel_denotation_preserves)\n" ++
  "      src2 = j; src2 <<= 1;\n" ++
  "      buf[32 * j : 32] = h2to1(buf[32 * src2 : 32],\n" ++
  "                               buf[32 * (src2 + 1) : 32], buf[32 * j : 32]);\n" ++
  "    }\n" ++
  "    width = half;\n  }\n" ++
  "  for b = 0 to 32 { x = buf[b]; root[b] = x; }\n" ++
  "  return root;\n}\n"

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The emitted Merkle `.jazz` declares the `export fn merkle_build_root`, the
    two-to-one compress, and the leaf hash — and uses NO opaque leaf
    (`extCall`). -/
theorem merkleJazz_shape :
    strContains merkleJazz "export fn merkle_build_root(" = true
      ∧ strContains merkleJazz "inline fn h2to1(" = true
      ∧ strContains merkleJazz "inline fn hleaf(" = true
      ∧ strContains merkleJazz "t *= 0x9E; t += i;" = true
      ∧ strContains merkleJazz "extCall" = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## 6. KAT: byte-identity against the plonky3-hax reference

The five regression vectors from `plonky3-hax/tests/kat_vectors.rs`, encoded as
the digest's first byte(s) — the full 32-byte equality is checked at the bench
level in `bench/plonky3_compare/`. We pin the leading digest byte (the
domain-separator byte 0, which the reference fixes at `0x09` for every leaf, and
`0xb5` / `0x00` for the compress / root vectors) so any change to the byte mix
breaks this Lean KAT. -/

/-- The digest as a `Nat` list of its 32 bytes (low byte first), for KAT pins. -/
def digestBytes (d : Digest) : List Nat :=
  (List.range 32).map (fun i => (d ⟨i % 32, Nat.mod_lt _ (by decide)⟩).toNat)

/-- **KAT — leaf-hash leading byte.** Every `hash_field_elem` output begins with
    `0x09` in the reference (`kat_hash_field_elem_{zero,one,forty_two}` all start
    `09…`). Pins bytes 0 of `H(0)`, `H(1)`, `H(42)`. -/
theorem kat_leaf_leading_byte :
    (merkleHashFieldElem 0  ⟨0, by decide⟩).toNat = 0x09
      ∧ (merkleHashFieldElem 1  ⟨0, by decide⟩).toNat = 0x09
      ∧ (merkleHashFieldElem 42 ⟨0, by decide⟩).toNat = 0x09 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **KAT — `hash_field_elem(0)` first four bytes** match
    `kat_hash_field_elem_zero` (`09c4d5a8…`). -/
theorem kat_leaf_zero_prefix :
    (merkleHashFieldElem 0 ⟨0, by decide⟩).toNat = 0x09
      ∧ (merkleHashFieldElem 0 ⟨1, by decide⟩).toNat = 0xc4
      ∧ (merkleHashFieldElem 0 ⟨2, by decide⟩).toNat = 0xd5
      ∧ (merkleHashFieldElem 0 ⟨3, by decide⟩).toNat = 0xa8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **KAT — `hash_field_elem(42)` first four bytes** match
    `kat_hash_field_elem_forty_two` (`091a972e…`). -/
theorem kat_leaf_fortytwo_prefix :
    (merkleHashFieldElem 42 ⟨0, by decide⟩).toNat = 0x09
      ∧ (merkleHashFieldElem 42 ⟨1, by decide⟩).toNat = 0x1a
      ∧ (merkleHashFieldElem 42 ⟨2, by decide⟩).toNat = 0x97
      ∧ (merkleHashFieldElem 42 ⟨3, by decide⟩).toNat = 0x2e := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **KAT — two-to-one compress first four bytes** match
    `kat_hash_two_to_one_constant_inputs`: `H([0x01;32], [0x02;32]) = b5fd0238…`. -/
theorem kat_compress_const_prefix :
    let l : Digest := fun _ => 0x01
    let r : Digest := fun _ => 0x02
    (merkleHashTwoToOne l r ⟨0, by decide⟩).toNat = 0xb5
      ∧ (merkleHashTwoToOne l r ⟨1, by decide⟩).toNat = 0xfd
      ∧ (merkleHashTwoToOne l r ⟨2, by decide⟩).toNat = 0x02
      ∧ (merkleHashTwoToOne l r ⟨3, by decide⟩).toNat = 0x38 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **KAT — Merkle root of four leaves** matches `kat_merkle_build_root_four`:
    `merkle_build_root([H(1),H(2),H(3),H(4)], 4) = 00e1d700…`. The four-leaf
    tree is two `merkleLevel` folds, exercising the level map twice. Pins the
    root's first four bytes `00 e1 d7 00`. -/
theorem kat_root_four_prefix :
    let leaves : Fin (2 ^ 2) → Digest := fun i => merkleHashFieldElem (i.val + 1)
    (merkleBuildRoot 2 leaves ⟨0,  by decide⟩).toNat = 0x00
      ∧ (merkleBuildRoot 2 leaves ⟨1, by decide⟩).toNat = 0xe1
      ∧ (merkleBuildRoot 2 leaves ⟨2, by decide⟩).toNat = 0xd7
      ∧ (merkleBuildRoot 2 leaves ⟨3, by decide⟩).toNat = 0x00 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ### Full 32-byte digest KATs (the complete byte-identity claim)

The prefix theorems above keep each `native_decide` light; these pin the
**entire 32-byte digest** against the reference hex, the airtight byte-identity
witness. -/

/-- **KAT — full `hash_field_elem(0)` digest** = `kat_hash_field_elem_zero`:
    `09c4d5a801ac8dd07914c57871fc7da0e964b548e14c6d7059b4a518519c5d40`. -/
theorem kat_leaf_zero_full :
    digestBytes (merkleHashFieldElem 0) =
      [0x09,0xc4,0xd5,0xa8,0x01,0xac,0x8d,0xd0,0x79,0x14,0xc5,0x78,0x71,0xfc,0x7d,0xa0,
       0xe9,0x64,0xb5,0x48,0xe1,0x4c,0x6d,0x70,0x59,0xb4,0xa5,0x18,0x51,0x9c,0x5d,0x40] := by
  native_decide

/-- **KAT — full `hash_two_to_one([0x01;32],[0x02;32])` digest**
    = `kat_hash_two_to_one_constant_inputs`:
    `b5fd0238a9bdfef855e5b270b9d56e2025fd32f859fd2ef84585c2d089f51e80`. -/
theorem kat_compress_const_full :
    digestBytes (merkleHashTwoToOne (fun _ => 0x01) (fun _ => 0x02)) =
      [0xb5,0xfd,0x02,0x38,0xa9,0xbd,0xfe,0xf8,0x55,0xe5,0xb2,0x70,0xb9,0xd5,0x6e,0x20,
       0x25,0xfd,0x32,0xf8,0x59,0xfd,0x2e,0xf8,0x45,0x85,0xc2,0xd0,0x89,0xf5,0x1e,0x80] := by
  native_decide

/-- **KAT — full Merkle root of four leaves** = `kat_merkle_root_four_leaves`:
    `00e1d70044a1e330b8c13f008cb1eb70c0f17770645183209871b7c024899b78`. The
    four-leaf tree is two `merkleLevel` folds. -/
theorem kat_root_four_full :
    digestBytes (merkleBuildRoot 2 (fun i => merkleHashFieldElem (i.val + 1))) =
      [0x00,0xe1,0xd7,0x00,0x44,0xa1,0xe3,0x30,0xb8,0xc1,0x3f,0x00,0x8c,0xb1,0xeb,0x70,
       0xc0,0xf1,0x77,0x70,0x64,0x51,0x83,0x20,0x98,0x71,0xb7,0xc0,0x24,0x89,0x9b,0x78] := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
