/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.JasminTypes
public import Mathlib.Data.List.Basic

/-!
# `LowCT` types: tower types, secrecy levels and located slots

The type layer of `LowCT` (`CatCrypt.Crypto.Jasmin.LowCT` re-exports it):
the injection `encodeStringNat`, the tower types `TowerType` with their tags
and storage widths, the runtime values `RustVal`, the information-flow levels
`SecretLevel` and `LevelTable`, and the located slots `Located`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin (JArray)

/-! ## §0  String → Nat injection

`encodeStringNat : String → Nat` is an injection from Lean strings
to Nat, used by `TowerType.byteSize` to give string-parameterised
constructors (`TFpGen`, `TFp2Gen`) unique discrimination tags so the
overall `byteSize` function stays injective (required by the
determinism proofs in `JasminSemTracedDeterminism`).

Implementation: composes `String.toList`'s injectivity (left-inverse
`String.ofList`) with a hand-rolled `List Char → Nat` injection via
`Char.toNat` (each Char is a 21-bit codepoint) and a Nat-pair-based
list encoding.
-/

/-- Hand-rolled `List Nat → Nat` injection.  Each element is paired
    with a "non-empty" bit, then list-folded via `Nat.pair`. -/
def encodeListNat : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.succ (Nat.pair x (encodeListNat xs))

theorem encodeListNat_inj : Function.Injective encodeListNat := by
  intro l1 l2 h
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp [encodeListNat] at h
  | cons x xs ih =>
    cases l2 with
    | nil => simp [encodeListNat] at h
    | cons y ys =>
      simp [encodeListNat] at h
      obtain ⟨hx, hxs⟩ := h
      have hxsEq : xs = ys := ih hxs
      rw [hx, hxsEq]

/-- Inject a Lean `String` into `Nat`.  Composes
    `String.toList : String → List Char` (injective via
    `String.ofList ∘ String.toList = id`) with `Char.toNat` and
    `encodeListNat`. -/
def encodeStringNat (s : String) : Nat :=
  encodeListNat (s.toList.map Char.toNat)

theorem encodeStringNat_inj : Function.Injective encodeStringNat := by
  intro s1 s2 h
  unfold encodeStringNat at h
  have hMap : s1.toList.map Char.toNat = s2.toList.map Char.toNat :=
    encodeListNat_inj h
  -- `Char.toNat` is injective: `Char.toNat c = c.val.toNat`, and
  -- `UInt32.toNat` is injective (UInt32 wraps `Fin 2^32`).
  have hChar : Function.Injective Char.toNat := fun c1 c2 hc => by
    have : c1.val = c2.val := UInt32.toNat_inj.mp hc
    cases c1; cases c2; simp_all
  have hList : s1.toList = s2.toList :=
    List.map_injective_iff.mpr hChar hMap
  -- `String.ofList ∘ String.toList = id` gives left-inverse → injectivity.
  have heq : String.ofList s1.toList = String.ofList s2.toList :=
    congrArg _ hList
  rw [String.ofList_toList, String.ofList_toList] at heq
  exact heq

/-! ## §1  Tower types -/

/-- Tower type hierarchy for pairing-friendly curves.

    **Extensions beyond the pairing tower:**
    * `TFp25519_4Bounded` — refinement-typed 4-limb representation.
      `bound` is the per-limb upper bound exponent;
      values represent integers below `2^(64*4)` with each limb < 2^bound.
    * `TFpGen` / `TFp2Gen` — modulus-parametric; the
      `LeafOps` typeclass lookup table provides per-curve operations.
    * `TFpL25519` / `TFpP256` — Curve25519 scalar-field and P-256
      base-field, referenced by `LowCTReflect`.
    * `TTuple` — binary product type.  Larger tuples nest.
    * `TBytes` — fixed-size byte arrays.  Used for AES /
      ChaCha20 / SHA-256 / SHA-3 byte-level kernels. -/
inductive TowerType where
  | TFp   : TowerType   -- base field element
  | TFp2  : TowerType   -- degree-2 extension
  | TFp6  : TowerType   -- degree-6 extension
  | TFp12 : TowerType   -- degree-12 extension
  | TU64  : TowerType   -- unsigned 64-bit scalar
  /-- **Unsigned 8-bit scalar.**  The element
      type produced by a `cast#8` in the hax extraction's byte-packing
      kernels (`byte_encode_12`, `poly_compress_*`).  `TFp` already
      serves as the u16 coefficient width; `TU8` / `TU32` express the
      narrower / wider intermediates the packing code threads values
      through.  Lowers to `reg u8` in Jasmin. -/
  | TU8   : TowerType
  /-- **Unsigned 32-bit scalar.**  The widen
      target of `cast#32` in the byte-packing kernels (so the bit
      shifts have headroom).  Lowers to `reg u32`. -/
  | TU32  : TowerType
  /-- Curve25519 base field: 5×u64 = 40 bytes (radix-2^51). -/
  | TFp25519 : TowerType
  /-- Curve25519 base field, alternate representation: 4×u64 = 32 bytes
      (saturated representation, matching formosa-25519's `__mul4_rsr` etc.).
      Used by the inline-substituted Jasmin extraction path (D4) so that
      the leaf-inline bodies operate over the same 4×64 layout as their
      formosa Jinc origins. The standard X25519 ladder still uses
      `TFp25519` (5×51); only protocols authored against `TFp25519_64`
      directly trigger the saturated layout. -/
  | TFp25519_64 : TowerType
  /-- Curve25519 scalar field (mod L = 2^252 + δ).  32 bytes. -/
  | TFpL25519 : TowerType
  /-- P-256 base field.  32 bytes (4×u64 saturated). -/
  | TFpP256 : TowerType
  /-- **Bounds-tracked saturated 4-limb representation.**
      Each limb < 2^bound.  Used for Sqr4, Solinas
      reduction, and any kernel where carry-bound tracking
      strengthens the Hoare invariants without runtime checks. -/
  | TFp25519_4Bounded : (bound : Nat) → TowerType
  /-- **Modulus-parametric base field.**  The `LeafOps`
      typeclass instantiated at `modulusName` provides the per-curve
      operations.  `byteSize` is fixed at the type level. -/
  | TFpGen  : (modulusName : String) → (byteSize : Nat) → TowerType
  /-- **Modulus-parametric quadratic extension.** -/
  | TFp2Gen : (modulusName : String) → (byteSize : Nat) → TowerType
  /-- **Binary product.**  Multi-element tuples nest as
      `TTuple a (TTuple b c)`.  Lowering: byte-concatenated array.  -/
  | TTuple  : TowerType → TowerType → TowerType
  /-- **Fixed-size byte array.**  `n` bytes.  Used for the
      symmetric-crypto kernels (AES blocks, ChaCha state, SHA blocks). -/
  | TBytes  : (n : Nat) → TowerType
  /-- **Array-of-slots.**  A homogeneous array
      of `n` cells, each holding a value of TowerType `t`.  Used for
      compactly expressing data structures whose elements are accessed
      by runtime index (e.g., comb tables, MSM bucket arrays).
      Runtime indexing is via `RArrLoad` / `RArrStore`; the index is a
      `u64`-typed scalar variable bound in `rsScalar`. -/
  | TArr    : (n : Nat) → (t : TowerType) → TowerType
  /-- **Polynomial mod q.**  `q` is the prime
      modulus, `n` the polynomial degree bound (coefficient count).
      For ML-KEM: `TPolyMod 3329 256`; for ML-DSA: `TPolyMod 8380417 256`.
      `storageBytes` allocates `n * ceil(log2 q / 8)` bytes. -/
  | TPolyMod : (q : Nat) → (n : Nat) → TowerType
  /-- **Vector of polynomials.**  `k` polynomials each of
      `TPolyMod q n`.  For ML-KEM polyvec: `TPolyVec 3329 256 2/3/4`. -/
  | TPolyVec : (q : Nat) → (n : Nat) → (k : Nat) → TowerType
  /-- **Matrix of polynomials.**  `k × m` polyvecs. -/
  | TPolyMat : (q : Nat) → (n : Nat) → (k : Nat) → (m : Nat) → TowerType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Byte size for BLS12-381 — used as a unique discrimination tag
    (required for the determinism proofs in
    `JasminSemTracedDeterminism`).  Every constructor occupies a disjoint Nat range via top-level
    `Nat.pair tag inner`, so `byteSize_inj` holds unconditionally.
    The actual storage byte width is exposed via
    `TowerType.storageBytes` below; lowering / runtime code that
    needs the real allocation size should call `storageBytes`. -/
def TowerType.byteSize : TowerType → Nat
  | .TFp                  => Nat.pair 0 0
  | .TFp2                 => Nat.pair 0 1
  | .TFp6                 => Nat.pair 0 2
  | .TFp12                => Nat.pair 0 3
  | .TU64                 => Nat.pair 0 4
  | .TFp25519             => Nat.pair 0 5
  | .TFp25519_64          => Nat.pair 0 6
  | .TFpL25519            => Nat.pair 0 7
  | .TFpP256              => Nat.pair 0 8
  | .TU8                  => Nat.pair 0 10
  | .TU32                 => Nat.pair 0 11
  | .TFp25519_4Bounded b  => Nat.pair 1 b
  | .TFpGen name n        => Nat.pair 2 (Nat.pair (encodeStringNat name) n)
  | .TFp2Gen name n       => Nat.pair 3 (Nat.pair (encodeStringNat name) n)
  | .TTuple a b           => Nat.pair 4 (Nat.pair a.byteSize b.byteSize)
  | .TBytes n             => Nat.pair 5 n
  | .TArr n t             => Nat.pair 6 (Nat.pair n t.byteSize)
  -- Polynomial-mod-q tower types.
  | .TPolyMod q n         => Nat.pair 7 (Nat.pair q n)
  | .TPolyVec q n k       => Nat.pair 8 (Nat.pair q (Nat.pair n k))
  | .TPolyMat q n k m     => Nat.pair 9 (Nat.pair q (Nat.pair n (Nat.pair k m)))

/-- Actual storage byte width.  This is the value
    used by Jasmin's `.sarr n` allocation, distinct from `byteSize`
    (which is a unique discrimination tag for the type).  For the
    seven pairing-tower constructors the two functions agree;
    for the extensions, `storageBytes` returns the
    natural byte width while `byteSize` returns a unique encoded
    tag.  Lowering/runtime code that needs actual storage size
    should call `storageBytes`; symbolic proofs that need
    injectivity call `byteSize`. -/
def TowerType.storageBytes : TowerType → Nat
  | .TFp     => 48
  | .TFp2    => 96
  | .TFp6    => 288
  | .TFp12   => 576
  | .TU64    => 8
  | .TU8     => 1
  | .TU32    => 4
  | .TFp25519 => 40
  | .TFp25519_64 => 32
  | .TFpL25519 => 32
  | .TFpP256 => 32
  | .TFp25519_4Bounded _ => 32
  | .TFpGen _ n => n
  | .TFp2Gen _ n => n
  | .TTuple a b => a.storageBytes + b.storageBytes
  | .TBytes n => n
  | .TArr n t => n * t.storageBytes
  -- Polynomial-mod-q storage.
  -- Each coefficient occupies ⌈(log2 q + 1) / 8⌉ bytes (`Nat.log2 q`
  -- returns ⌊log2⌋, so `Nat.log2 q + 1` is the bit-width of q-1, and
  -- `(x + 7) / 8` rounds up to a byte boundary).
  | .TPolyMod q n => n * ((Nat.log2 q + 1 + 7) / 8)
  | .TPolyVec q n k => k * (n * ((Nat.log2 q + 1 + 7) / 8))
  | .TPolyMat q n k m => k * m * (n * ((Nat.log2 q + 1 + 7) / 8))

/-- A unique numeric encoding of `TowerType`, distinct from
    `byteSize` (which has collisions among the 32-byte
    constructors).  Used by the determinism proofs in
    `JasminSemTracedDeterminism` where unique-tag per-constructor is
    required.  Injective by construction (each constructor occupies
    a disjoint range of Nat). -/
def TowerType.encode : TowerType → Nat
  | .TFp                     => 1
  | .TFp2                    => 2
  | .TFp6                    => 3
  | .TFp12                   => 4
  | .TU64                    => 5
  | .TFp25519                => 6
  | .TFp25519_64             => 7
  | .TFpL25519               => 8
  | .TFpP256                 => 9
  | .TU8                     => 10
  | .TU32                    => 11
  | .TFp25519_4Bounded b     => 100 + b
  | .TFpGen name n           => 1000000 + 1000 * name.length + n
  | .TFp2Gen name n          => 2000000 + 1000 * name.length + n
  | .TTuple a b              => 4000000 + 1000 * a.encode + b.encode
  | .TBytes n                => 8000000 + n
  | .TArr n t                => 9000000 + 1000 * n + t.encode
  -- Polynomial-mod-q encodings (disjoint Nat ranges).
  | .TPolyMod q n            => 10000000 + 1000 * q + n
  | .TPolyVec q n k          => 11000000 + 1000000 * q + 1000 * n + k
  | .TPolyMat q n k m        => 12000000 + 1000000 * q + 10000 * n + 100 * k + m

/-- Runtime value for tower type `t`: a fixed-size byte array of
    `t.storageBytes` bytes.

    Uses `t.storageBytes`, not `t.byteSize`: `byteSize` is a proof-tag
    (unique encoding via `Nat.pair`) needed for `byteSize_inj`, while
    `storageBytes` is
    the actual runtime byte width consumed by lowering (`.sarr N`,
    `Parr_init N`, etc.). See `storageBytes`' docstring above for the
    full distinction. -/
abbrev RustVal (t : TowerType) := JArray t.storageBytes

/-! ## §2  Located values -/

/-- **Information-flow level.**  Tracks whether a slot
    holds public or secret data.  Default `Public` for back-compat. -/
inductive SecretLevel where
  | Public : SecretLevel
  | Secret : SecretLevel
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Public-or-Secret join (used to combine input flow levels). -/
def SecretLevel.join : SecretLevel → SecretLevel → SecretLevel
  | .Secret, _ => .Secret
  | _, .Secret => .Secret
  | .Public, .Public => .Public

/-- A located value: a named variable together with its tower type.
    `locDst` is exposed as a function returning `locSrc`; there is no
    separate `locDst` field. The intrinsic encoding eliminates a
    structural ambiguity blocking unconditional reverse compiler
    correctness (see RustExecTraced.lean's A1.16' section). -/
structure Located where
  locVar : String
  locSrc : TowerType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- **Information-flow classification.**
    A `LevelTable` maps named slots to public/secret classification.
    The CT analyser consumes this table to reject secret-dependent
    branches.  Defaults to all-public (`fun _ => .Public`) so
    existing code without a classification compiles unchanged. -/
abbrev LevelTable := String → SecretLevel

/-- The default all-public classification.  Used when no
    information-flow analysis has been performed. -/
def LevelTable.allPublic : LevelTable := fun _ => .Public

/-- Look up the security level of a `Located` slot in a level
    table.  Convenience wrapper. -/
def Located.level (loc : Located) (lt : LevelTable) : SecretLevel :=
  lt loc.locVar

/-- Accessor `locDst`, always equal to `locSrc`. -/
abbrev Located.locDst (loc : Located) : TowerType := loc.locSrc

/-- `Located` always has positive `sizeOf` because it has at least
    one constructor weight.  Used by `decreasing_by` clauses that
    need to see Located's structural sizeOf (e.g. the
    `RCallSwap → RCall(destX)` recursion in
    `RustExecTraced.jasminSemTraced_to_rustExecTraced`). -/
theorem Located.sizeOf_pos (l : Located) : 0 < sizeOf l := by
  cases l; simp

/-- Does `dest` share a base variable with any element of `args`? -/
def callAliases (dest : Located) (args : List Located) : Bool :=
  args.any (fun a => a.locVar == dest.locVar)

end CatCrypt.Crypto.Jasmin.LowCT
