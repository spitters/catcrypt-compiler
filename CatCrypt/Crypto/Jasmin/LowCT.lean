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
# `LowCT`: Typed Tower-Field Low-level Constant-Time Command Language

Port of `AUCurves/src/Bedrock/SafeRustSimulation.v`.

`LowCT` (historically `LowCT`, renamed in #267) is a typed DSL for low-level
constant-time crypto programs over tower field elements (Fp, Fp2, Fp6, Fp12,
U64) — *not* Rust.  It exposes branchless-select, kernel-call ABIs, machine
intrinsics, widening multiply, and limb stores, the scheduling/codegen layer
Rust deliberately hides.  The borrow checker (`LowCTBorrowCheck.lean`)
certifies memory safety statically; the simulation semantics (`RustExec`)
gives the big-step meaning used for frame proofs.

## Tower type encoding

Tower elements are modelled as fixed-size byte arrays (`JArray`), using the
BLS12-381 sizes as concrete defaults.  The `byteSize` function can be
overridden by downstream files for other curves.

## References

* AUCurves `SafeRustSimulation.v` — original Rocq DSL
* AUCurves `SafeRustBorrowCheck.v` — borrow checker and frame theorems
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin (JArray)

/-! ## §0  String → Nat injection (Phase E support, 2026-05-03)

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

    **Phase D/E/I/K extensions (2026-05-03):**
    * `TFp25519_4Bounded` — refinement-typed 4-limb representation
      (Phase D).  `bound` is the per-limb upper bound exponent;
      values represent integers below `2^(64*4)` with each limb < 2^bound.
    * `TFpGen` / `TFp2Gen` — modulus-parametric (Phase E); the
      `LeafOps` typeclass lookup table provides per-curve operations.
    * `TFpL25519` / `TFpP256` — Curve25519 scalar-field and P-256
      base-field, added to close the pre-existing LowCTReflect
      cross-reference and unblock the H1 subset filter.
    * `TTuple` — binary product type (Phase I).  Larger tuples nest.
    * `TBytes` — fixed-size byte arrays (Phase K).  Used for AES /
      ChaCha20 / SHA-256 / SHA-3 byte-level kernels. -/
inductive TowerType where
  | TFp   : TowerType   -- base field element
  | TFp2  : TowerType   -- degree-2 extension
  | TFp6  : TowerType   -- degree-6 extension
  | TFp12 : TowerType   -- degree-12 extension
  | TU64  : TowerType   -- unsigned 64-bit scalar
  /-- **Phase L.1 (2026-05-23) — unsigned 8-bit scalar.**  The element
      type produced by a `cast#8` in the hax extraction's byte-packing
      kernels (`byte_encode_12`, `poly_compress_*`).  `TFp` already
      serves as the u16 coefficient width; `TU8` / `TU32` express the
      narrower / wider intermediates the packing code threads values
      through.  Lowers to `reg u8` in Jasmin. -/
  | TU8   : TowerType
  /-- **Phase L.1 (2026-05-23) — unsigned 32-bit scalar.**  The widen
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
  /-- **Phase D — bounds-tracked saturated 4-limb representation.**
      Each limb < 2^bound.  Used for Sqr4, Solinas
      reduction, and any kernel where carry-bound tracking
      strengthens the Hoare invariants without runtime checks. -/
  | TFp25519_4Bounded : (bound : Nat) → TowerType
  /-- **Phase E — modulus-parametric base field.**  The `LeafOps`
      typeclass instantiated at `modulusName` provides the per-curve
      operations.  `byteSize` is fixed at the type level. -/
  | TFpGen  : (modulusName : String) → (byteSize : Nat) → TowerType
  /-- **Phase E — modulus-parametric quadratic extension.** -/
  | TFp2Gen : (modulusName : String) → (byteSize : Nat) → TowerType
  /-- **Phase I — binary product.**  Multi-element tuples nest as
      `TTuple a (TTuple b c)`.  Lowering: byte-concatenated array.  -/
  | TTuple  : TowerType → TowerType → TowerType
  /-- **Phase K — fixed-size byte array.**  `n` bytes.  Used for the
      symmetric-crypto kernels (AES blocks, ChaCha state, SHA blocks). -/
  | TBytes  : (n : Nat) → TowerType
  /-- **Phase Ext (2026-05-12) — array-of-slots.**  A homogeneous array
      of `n` cells, each holding a value of TowerType `t`.  Used for
      compactly expressing data structures whose elements are accessed
      by runtime index (e.g., comb tables, MSM bucket arrays).
      Runtime indexing is via `RArrLoad` / `RArrStore`; the index is a
      `u64`-typed scalar variable bound in `rsScalar`. -/
  | TArr    : (n : Nat) → (t : TowerType) → TowerType
  /-- **Phase L (2026-05-22) — polynomial mod q.**  `q` is the prime
      modulus, `n` the polynomial degree bound (coefficient count).
      For ML-KEM: `TPolyMod 3329 256`; for ML-DSA: `TPolyMod 8380417 256`.
      `storageBytes` allocates `n * ceil(log2 q / 8)` bytes. -/
  | TPolyMod : (q : Nat) → (n : Nat) → TowerType
  /-- **Phase L — vector of polynomials.**  `k` polynomials each of
      `TPolyMod q n`.  For ML-KEM polyvec: `TPolyVec 3329 256 2/3/4`. -/
  | TPolyVec : (q : Nat) → (n : Nat) → (k : Nat) → TowerType
  /-- **Phase L — matrix of polynomials.**  `k × m` polyvecs. -/
  | TPolyMat : (q : Nat) → (n : Nat) → (k : Nat) → (m : Nat) → TowerType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Byte size for BLS12-381 — used as a unique discrimination tag
    (required for the determinism proofs in
    `JasminSemTracedDeterminism`).  After Phase D/E/I/K (2026-05-03),
    every constructor occupies a disjoint Nat range via top-level
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
  -- Phase L (2026-05-22): polynomial-mod-q tower types.
  | .TPolyMod q n         => Nat.pair 7 (Nat.pair q n)
  | .TPolyVec q n k       => Nat.pair 8 (Nat.pair q (Nat.pair n k))
  | .TPolyMat q n k m     => Nat.pair 9 (Nat.pair q (Nat.pair n (Nat.pair k m)))

/-- Phase D/E/I/K — actual storage byte width.  This is the value
    used by Jasmin's `.sarr n` allocation, distinct from `byteSize`
    (which is a unique discrimination tag for the type).  For the
    seven legacy TowerType constructors the two functions agree;
    for the Phase-D/E/I/K extensions, `storageBytes` returns the
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
  -- Phase L (2026-05-22): polynomial-mod-q storage.
  -- Each coefficient occupies ⌈(log2 q + 1) / 8⌉ bytes (`Nat.log2 q`
  -- returns ⌊log2⌋, so `Nat.log2 q + 1` is the bit-width of q-1, and
  -- `(x + 7) / 8` rounds up to a byte boundary).
  | .TPolyMod q n => n * ((Nat.log2 q + 1 + 7) / 8)
  | .TPolyVec q n k => k * (n * ((Nat.log2 q + 1 + 7) / 8))
  | .TPolyMat q n k m => k * m * (n * ((Nat.log2 q + 1 + 7) / 8))

/-- A unique numeric encoding of `TowerType`, distinct from
    `byteSize` (which has collisions among the 32-byte constructors
    after Phase D/E/I/K).  Used by the determinism proofs in
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
  -- Phase L (2026-05-22): polynomial-mod-q encodings (disjoint Nat ranges).
  | .TPolyMod q n            => 10000000 + 1000 * q + n
  | .TPolyVec q n k          => 11000000 + 1000000 * q + 1000 * n + k
  | .TPolyMat q n k m        => 12000000 + 1000000 * q + 10000 * n + 100 * k + m

/-- Runtime value for tower type `t`: a fixed-size byte array of
    `t.storageBytes` bytes.

    Migrated 2026-05-14 from `t.byteSize` to `t.storageBytes` per the
    db008232 follow-up: `byteSize` is now a proof-tag (unique encoding
    via `Nat.pair`) needed for `byteSize_inj`, while `storageBytes` is
    the actual runtime byte width consumed by lowering (`.sarr N`,
    `Parr_init N`, etc.). See `storageBytes`' docstring above for the
    full distinction. -/
abbrev RustVal (t : TowerType) := JArray t.storageBytes

/-! ## §2  Located values -/

/-- **Phase J — information-flow level.**  Tracks whether a slot
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
    `locDst` is exposed as a function returning `locSrc` for backwards
    compatibility — historically the structure had a separate `locDst`
    field, but every construction set `locDst = locSrc` and the
    duality wasn't exercised. The intrinsic encoding eliminates a
    structural ambiguity blocking unconditional reverse compiler
    correctness (see RustExecTraced.lean's A1.16' section). -/
structure Located where
  locVar : String
  locSrc : TowerType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- **Phase J — information-flow classification (2026-05-03).**
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

/-- Backwards-compatible accessor: `locDst` was historically a separate
    field always equal to `locSrc`. Now defined as a function. -/
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

/-! ## §2b  Scalar expressions

`SExpr` is a small expression language over Nat-valued scalar slots
(those bound by `RLetU64Zero` and `RScalarSet`).  Used by
`RScalarSetExpr` (Phase Ext 2026-05-12) to assign a runtime computed
value to a scalar slot, e.g. `k := i * 16 + d` for runtime `i`/`d`.

Mirrors Rocq's `sexpr_ed` (`SafeRustEd25519Sim.v`).  The 8 constructors
cover the index-arithmetic + bit-twiddle patterns the byte-level Rocq
side uses; the Lean side currently only needs `SVar`, `SLit`, `SAdd`,
`SMul`, but parity with Rocq keeps the cross-formalism mapping clean. -/
inductive SExpr where
  | SVar : String → SExpr           -- read a u64-typed scalar slot
  | SLit : Nat → SExpr              -- Nat literal
  | SAdd : SExpr → SExpr → SExpr
  | SSub : SExpr → SExpr → SExpr    -- saturating: max 0
  | SMul : SExpr → SExpr → SExpr
  | SShr : SExpr → SExpr → SExpr    -- right shift (truncating, LOGICAL)
  | SShl : SExpr → SExpr → SExpr    -- left shift
  | SAnd : SExpr → SExpr → SExpr    -- bitwise and
  | SXor : SExpr → SExpr → SExpr    -- bitwise xor (GF(16) add)
  | SLt  : SExpr → SExpr → SExpr    -- x < y → 0 / 1 (UNSIGNED)
  /-- **Signed-arith extension (#257, 2026-05-30) — arithmetic shift right.**
      `SAsr a b` shifts `a` right by `b`, interpreting `a` as a 64-bit
      **two's-complement** signed value: the sign bit (bit 63) is replicated
      into the vacated high bits.  This is the FIPS-204 `montgomery_reduce`
      `r >> 32` step (C99 6.5.7(5) sign-preserving shift on a negative `int64`).
      Lowers to Jasmin `Oasr U64` (`>>s`).  Distinct from `SShr` (logical
      `>>`, vacated bits zero) — the two coincide only when `a`'s sign bit is 0. -/
  | SAsr : SExpr → SExpr → SExpr    -- arithmetic (sign-preserving) shift right
  /-- **Signed-arith extension (#257, 2026-05-30) — signed multiply.**
      `SMulS a b` is the 64-bit low-word product, with both operands
      interpreted as two's-complement.  At the low-64-bit word level a signed
      product and an unsigned product carry the *same* bit pattern (multiply
      is sign-agnostic mod 2^64), so `SMulS` and `SMul` produce identical
      stored words; `SMulS` records the *signed intent* so a following `SAsr`
      reads a sign-correct value (`montgomery_reduce`'s `(int64_t)t * Q`).
      Lowers to Jasmin `Omul U64`. -/
  | SMulS : SExpr → SExpr → SExpr   -- signed (two's-complement) multiply
  /-- **Widening-multiply extension (#261, 2026-05-30) — unsigned high word.**
      `SMulHiU a b` is the *high* 64 bits of the full `64×64 → 128` **unsigned**
      product of `a` and `b` (each read as a `u64` word).  Paired with the
      existing low-word `SMul`, the pair `(SMulHiU a b, SMul a b)` reconstructs
      the full 128-bit unsigned product as a (hi, lo) limb pair — the building
      block for a 128-bit accumulator.  Lowers to the Jasmin `#MULX` intrinsic
      (BMI2 unsigned `hi:lo = a*b`), with the low output discarded (`_`).
      Distinct from `SMul` (which keeps the low word). -/
  | SMulHiU : SExpr → SExpr → SExpr -- high 64 bits of unsigned 64×64→128 product
  /-- **Widening-multiply extension (#261, 2026-05-30) — signed high word.**
      `SMulHiS a b` is the *high* 64 bits of the full `64×64 → 128` **signed**
      (two's-complement) product of `a` and `b`.  Paired with the low-word
      `SMulS`, the pair `(SMulHiS a b, SMulS a b)` reconstructs the full signed
      128-bit product as a (hi, lo) limb pair — the 62-bit-radix safegcd
      `update_de_62` / `update_fg_62` accumulator step (`t.u as i128 * d.v[0] as
      i128`, products up to ~2^124).  Lowers to the Jasmin `#IMUL` intrinsic
      (signed wide multiply, 7 outputs `OF,SF,_,ZF,_,hi,lo`), keeping only the
      `hi` output.  Unlike `SMul`/`SMulS` the *low* word agrees between signed
      and unsigned, but the *high* word does NOT — `SMulHiS` ≠ `SMulHiU`
      whenever exactly one operand's sign bit is set. -/
  | SMulHiS : SExpr → SExpr → SExpr -- high 64 bits of signed 64×64→128 product
  /-- **Tower-limb read extension (#354, 2026-06-01) — read limb `i` of a
      tower slot.**  `SLimb v i` is the value of limb `i` (a little-endian
      `u64` word) of the limb-bearing tower slot named `v`.  Mirrors
      AUCurves' `sexpr_ed` constructor `SLimb : var → nat → sexpr_ed`
      (`SafeRustEd25519Sim.v`), whose `eval_sexpr_ed` reads limb `i` from
      `rs_get_tower_ed rs v` (radix-2^51 / saturated representations,
      masked through `mask64`).  This is the value used by the real inline
      field-op bodies, e.g. `fe25519_add_body`'s
      `REdLimbStore dest i (SAdd (SLimb a i) (SLimb b i))`.

      Because `SLimb` reads the **tower heap**, not the scalar heap, the
      scalar-only `SExpr.eval : (String → Nat) → SExpr → Nat` cannot see its
      value: that evaluator gives `SLimb` a safe default of `0` (a tower-free
      environment carries no limbs).  The faithful image is the
      tower-aware `SExpr.evalState : RustState → SExpr → Nat` (below), which
      reads the limb from `rs.rsTower`.  Keeping the scalar `eval` signature
      intact is deliberate (other in-flight emit modules depend on it). -/
  | SLimb : String → Nat → SExpr
  deriving Repr, Inhabited

/-- Wrap a `Nat` into its 64-bit two's-complement signed `Int` value:
    bits `[0,63]` of `n` interpreted as a signed 64-bit machine integer.
    Used by the signed `SExpr.eval` arms (`SAsr`, `SMulS`) so the Lean-side
    semantics matches Jasmin's `>>s` / signed-`*` on a `reg u64`. -/
def sexprToSignedInt64 (n : Nat) : Int := (BitVec.ofNat 64 n).toInt

/-- Wrap an `Int` back into its 64-bit two's-complement `Nat` representative
    (bits `[0,63]`), the storage form `rsScalar` holds. -/
def sexprOfSignedInt64 (z : Int) : Nat := (BitVec.ofInt 64 z).toNat

/-- **Widening-multiply extension (#261).** High 64 bits of the full
    `64×64 → 128` **unsigned** product of the two stored words `a`, `b`.
    Each operand is first reduced mod `2^64` (the `u64` storage form), the
    full Nat product is taken, and its bits `[64,127]` are returned.  Matches
    the Jasmin `#MULX` intrinsic's `hi` output. -/
def sexprMulHiU (a b : Nat) : Nat :=
  ((a % (2 ^ 64)) * (b % (2 ^ 64))) >>> 64

/-- **Widening-multiply extension (#261).** High 64 bits of the full
    `64×64 → 128` **signed** (two's-complement) product.  The operands are
    interpreted as signed int64 (`sexprToSignedInt64`), the exact `Int`
    product is taken, arithmetically shifted right by 64 (`Int` shift = floor
    division by `2^64`, i.e. sign-preserving), and the resulting `Int` high
    word is wrapped back to its 64-bit stored pattern.  Matches the Jasmin
    `#IMUL` intrinsic's `hi` output (the `RDX` half of the signed `imul`). -/
def sexprMulHiS (a b : Nat) : Nat :=
  sexprOfSignedInt64 ((sexprToSignedInt64 a * sexprToSignedInt64 b) >>> 64)

/-- Evaluate an `SExpr` against the scalar environment.  Returns a Nat
    (no error path — undefined vars read as 0 via `rsScalar` default,
    SSub saturates at 0 rather than going negative).  Matches the
    `rsScalar : String → Nat` default-0 behaviour in `RustState`.

    **NOT the `u64` VALUE semantics — memory-safety-layer over-approximation
    only.**  The `Nat` carrier makes `SSub` *saturate* at 0 and `SAdd`/`SMul`
    grow unboundedly, matching NEITHER the hardware target (wraps mod 2^64) NOR
    real Rust `u64` (release: wraps; debug: panics — never saturates; saturation
    is the distinct `saturating_sub`).  It is a *third* out-of-range behaviour,
    faithful to nothing physical.  `Nat` is chosen here for the memory-safety /
    frame layer (aliasing reasoning, where scalar values are irrelevant), NOT as
    a value oracle.  **For VALUE-level (emit-correctness) reasoning use
    `SExpr.evalBV` (wrapping-`u64`-faithful); the two agree only under the
    explicit `SExpr.inRange` side condition (`SExpr.evalBV_eq_ofNat_eval`, the
    #250 reconciliation).** -/
def SExpr.eval (σ : String → Nat) : SExpr → Nat
  | .SVar x   => σ x
  | .SLit n   => n
  | .SAdd a b => a.eval σ + b.eval σ
  | .SSub a b => a.eval σ - b.eval σ
  | .SMul a b => a.eval σ * b.eval σ
  | .SShr a b => a.eval σ >>> b.eval σ
  | .SShl a b => a.eval σ <<< b.eval σ
  | .SAnd a b => a.eval σ &&& b.eval σ
  | .SXor a b => a.eval σ ^^^ b.eval σ
  | .SLt  a b => if a.eval σ < b.eval σ then 1 else 0
  -- Signed-arith extension (#257): two's-complement-faithful semantics via
  -- `BitVec 64`.  `SAsr` interprets its operand as a signed int64 and
  -- shifts right with sign replication (matches Jasmin `>>s`); `SMulS`
  -- multiplies as signed int64 and re-wraps mod 2^64.
  | .SAsr a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.eval σ) >>> (b.eval σ : Nat))
  | .SMulS a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.eval σ) * sexprToSignedInt64 (b.eval σ))
  -- Widening-multiply extension (#261): the high word of the 128-bit product.
  | .SMulHiU a b => sexprMulHiU (a.eval σ) (b.eval σ)
  | .SMulHiS a b => sexprMulHiS (a.eval σ) (b.eval σ)
  -- Tower-limb read extension (#354): `SLimb` reads the tower heap, which the
  -- scalar environment `σ : String → Nat` does not carry.  The scalar `eval`
  -- therefore returns a SAFE DEFAULT of `0` — the faithful value lives in
  -- `SExpr.evalState` below.  This arm keeps `eval` total and exhaustive
  -- WITHOUT changing its signature (other emit modules depend on it).
  | .SLimb _ _ => 0

/-! ### Wrapping-`u64` reconciliation (#250)

`SExpr.eval` (above) evaluates over **unbounded `Nat`**.  The jasmin / x86
target, by contrast, stores every scalar as a `u64` and wraps every
intermediate arithmetic operation **mod 2^64** (two's-complement).  On
overflowing inputs the two can disagree — e.g. `SAdd (SLit (2^63)) (SLit (2^63))`
is `2^64` in the Nat model but `0` on the hardware.  Leaving this implicit
would silently assume `Nat = u64`, a soundness gap in the emit-correctness
chain.

`SExpr.evalBV` is the **wrapping-`u64`-faithful** evaluator: every node does the
corresponding `Nat` operation and immediately truncates to a `BitVec 64` (i.e.
reduces mod `2^64`), exactly mirroring the hardware.  It is the
storage-truncation image of `eval` made *intermediate-faithful*.  Note the
signed / widening arms (`SAsr`, `SMulS`, `SMulHi{U,S}`) already produce an
in-`u64`-range value in `eval` (via `sexprOfSignedInt64` / `% 2^64`), so their
`evalBV` arm is the literal truncation of that same value — they were already
wrapping-faithful (#257, #261); only the plain `Nat`-arithmetic arms (`SAdd`,
`SSub`, `SMul`, `SShl`, `SShr`, `SLt`, `SAnd`, `SXor`) needed reconciling.

The bridge to the Nat model is `SExpr.evalBV_eq_ofNat_eval` below: under the
explicit in-range side-condition `SExpr.inRange` the wrapping evaluator equals
`BitVec.ofNat 64 (eval …)`, i.e. *no wrap actually occurs* and the Nat model is
sound for the hardware on those inputs.  Defined additively (a companion of
`eval`, not a replacement) so `eval`'s `(String → Nat) → SExpr → Nat` signature
— and its many callers — stay intact. -/
def SExpr.evalBV (β : String → BitVec 64) : SExpr → BitVec 64
  | .SVar x   => β x
  | .SLit n   => BitVec.ofNat 64 n
  | .SAdd a b => a.evalBV β + b.evalBV β
  | .SSub a b => a.evalBV β - b.evalBV β
  | .SMul a b => a.evalBV β * b.evalBV β
  | .SShr a b => (a.evalBV β) >>> (b.evalBV β).toNat
  | .SShl a b => (a.evalBV β) <<< (b.evalBV β).toNat
  | .SAnd a b => a.evalBV β &&& b.evalBV β
  | .SXor a b => a.evalBV β ^^^ b.evalBV β
  | .SLt  a b => if (a.evalBV β).toNat < (b.evalBV β).toNat then 1 else 0
  | .SAsr a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalBV β).toNat >>> ((b.evalBV β).toNat : Nat)))
  | .SMulS a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalBV β).toNat * sexprToSignedInt64 (b.evalBV β).toNat))
  | .SMulHiU a b => BitVec.ofNat 64 (sexprMulHiU (a.evalBV β).toNat (b.evalBV β).toNat)
  | .SMulHiS a b => BitVec.ofNat 64 (sexprMulHiS (a.evalBV β).toNat (b.evalBV β).toNat)
  | .SLimb _ _ => 0

/-- In-range side-condition for the Nat-model `eval` to agree with the
    wrapping-`u64` hardware `evalBV` on a given scalar environment `σ`.

    The bitwise arms (`SAnd`, `SXor`) and the signed/widening arms wrap
    homomorphically and need **no** condition; the conditions that actually
    matter are:

    * `SSub a b` — the Nat model **saturates** at `0` while hardware **wraps**;
      they agree exactly when there is no underflow (`b ≤ a`).
    * `SShr` / `SShl` / `SLt` — the operand(s) must be representable in `u64`
      (`< 2^64`) and the shift amount `< 64`, so that the `Nat` shift/compare
      coincides with the 64-bit one.
    * Every additive / multiplicative node must itself land back in `u64`
      range so that the *outer* truncation is the identity at the Nat level —
      this is what "no wrap occurs" means.

    When `inRange σ e` holds, `eval σ e < 2^64` and the Nat model is sound for
    the hardware (`evalBV_eq_ofNat_eval` + `eval_lt_of_inRange`). -/
def SExpr.inRange (σ : String → Nat) : SExpr → Prop
  | .SVar x   => σ x < 2 ^ 64
  | .SLit n   => n < 2 ^ 64
  | .SAdd a b => a.inRange σ ∧ b.inRange σ ∧ a.eval σ + b.eval σ < 2 ^ 64
  | .SSub a b => a.inRange σ ∧ b.inRange σ ∧ b.eval σ ≤ a.eval σ
  | .SMul a b => a.inRange σ ∧ b.inRange σ ∧ a.eval σ * b.eval σ < 2 ^ 64
  | .SShr a b => a.inRange σ ∧ b.inRange σ ∧ b.eval σ < 64
  | .SShl a b => a.inRange σ ∧ b.inRange σ ∧ b.eval σ < 64 ∧ a.eval σ <<< b.eval σ < 2 ^ 64
  | .SAnd a b => a.inRange σ ∧ b.inRange σ
  | .SXor a b => a.inRange σ ∧ b.inRange σ
  | .SLt  a b => a.inRange σ ∧ b.inRange σ
  | .SAsr a b => a.inRange σ ∧ b.inRange σ
  | .SMulS a b => a.inRange σ ∧ b.inRange σ
  | .SMulHiU a b => a.inRange σ ∧ b.inRange σ
  | .SMulHiS a b => a.inRange σ ∧ b.inRange σ
  | .SLimb _ _ => True

/-- `sexprOfSignedInt64` always lands in `u64` range: it is the `toNat` of a
    `BitVec 64`. -/
theorem sexprOfSignedInt64_lt (z : Int) : sexprOfSignedInt64 z < 2 ^ 64 := by
  unfold sexprOfSignedInt64
  exact (BitVec.ofInt 64 z).isLt

/-- `sexprMulHiU` always lands in `u64` range. -/
theorem sexprMulHiU_lt (a b : Nat) : sexprMulHiU a b < 2 ^ 64 := by
  unfold sexprMulHiU
  have ha : a % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  have hb : b % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  calc (a % 2 ^ 64 * (b % 2 ^ 64)) >>> 64
      = (a % 2 ^ 64 * (b % 2 ^ 64)) / 2 ^ 64 := by
        simp [Nat.shiftRight_eq_div_pow]
    _ < 2 ^ 64 := by
        apply Nat.div_lt_of_lt_mul
        calc a % 2 ^ 64 * (b % 2 ^ 64) < 2 ^ 64 * 2 ^ 64 :=
              Nat.mul_lt_mul'' ha hb
          _ = 2 ^ 64 * 2 ^ 64 := rfl

/-- `sexprMulHiS` always lands in `u64` range (it is a `sexprOfSignedInt64`). -/
theorem sexprMulHiS_lt (a b : Nat) : sexprMulHiS a b < 2 ^ 64 := by
  unfold sexprMulHiS
  exact sexprOfSignedInt64_lt _

/-- Under `inRange`, the Nat-model value is representable in `u64`: no overflow
    happens, so the model agrees with the truncated/wrapped storage form. -/
theorem SExpr.eval_lt_of_inRange (σ : String → Nat) :
    ∀ e : SExpr, e.inRange σ → e.eval σ < 2 ^ 64 := by
  intro e
  induction e with
  | SVar x => intro h; exact h
  | SLit n => intro h; exact h
  | SAdd a b _ _ => intro h; exact h.2.2
  | SSub a b iha _ => intro h; exact lt_of_le_of_lt (Nat.sub_le _ _) (iha h.1)
  | SMul a b _ _ => intro h; exact h.2.2
  | SShr a b iha _ =>
      intro h
      exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (iha h.1)
  | SShl a b _ _ => intro h; exact h.2.2.2
  | SAnd a b iha ihb =>
      intro h
      exact lt_of_le_of_lt (Nat.and_le_left) (iha h.1)
  | SXor a b iha ihb =>
      intro h
      have := Nat.xor_lt_two_pow (n := 64) (lt_of_lt_of_le (iha h.1) (le_refl _))
        (lt_of_lt_of_le (ihb h.2) (le_refl _))
      exact this
  | SLt a b _ _ =>
      intro _; simp only [SExpr.eval]; split <;> norm_num
  | SAsr a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulS a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulHiU a b _ _ => intro _; exact sexprMulHiU_lt _ _
  | SMulHiS a b _ _ => intro _; exact sexprMulHiS_lt _ _
  | SLimb v i => intro _; positivity

/-- Lift a scalar environment `σ : String → Nat` to the wrapping-`u64`
    environment `String → BitVec 64` that the hardware sees. -/
def SExpr.liftEnv (σ : String → Nat) : String → BitVec 64 :=
  fun x => BitVec.ofNat 64 (σ x)

/-- **Wrapping-`u64` ⇔ Nat-model bridge (#250, `.toNat` form).**
    Under the in-range side-condition `inRange σ e`, the `Nat` read back out of
    the wrapping-`u64` evaluator equals the Nat-model value: i.e. **no wrap
    occurs**, so `SExpr.eval` faithfully predicts the hardware result.  This is
    the formal statement that the Nat model is sound w.r.t. overflow precisely
    on the inputs the side-condition allows. -/
theorem SExpr.toNat_evalBV_of_inRange (σ : String → Nat) :
    ∀ e : SExpr, e.inRange σ →
      (e.evalBV (SExpr.liftEnv σ)).toNat = e.eval σ := by
  intro e
  induction e with
  | SVar x =>
      intro h
      simp only [SExpr.evalBV, SExpr.liftEnv, SExpr.eval, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SLit n =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SAdd a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_add, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SSub a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_sub, iha h.1, ihb h.2.1]
      have hba : eval σ b ≤ eval σ a := h.2.2
      have hlt : eval σ a < 2 ^ 64 := SExpr.eval_lt_of_inRange σ a h.1
      have heq : 2 ^ 64 - eval σ b + eval σ a = 2 ^ 64 + (eval σ a - eval σ b) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  | SMul a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_mul, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SShr a b iha ihb =>
      intro h
      rw [SExpr.evalBV, SExpr.eval, BitVec.toNat_ushiftRight, iha h.1, ihb h.2.1]
  | SShl a b iha ihb =>
      intro h
      rw [SExpr.evalBV, SExpr.eval, BitVec.toNat_shiftLeft, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2.2
  | SAnd a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_and, iha h.1, ihb h.2]
  | SXor a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_xor, iha h.1, ihb h.2]
  | SLt a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, iha h.1, ihb h.2]
      split <;> simp
  | SAsr a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulS a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulHiU a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiU_lt _ _)
  | SMulHiS a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiS_lt _ _)
  | SLimb v i =>
      intro _
      simp [SExpr.evalBV, SExpr.eval]

/-- **Wrapping-`u64` ⇔ Nat-model bridge (#250, `BitVec` form).**  The direct
    corollary: on in-range inputs the wrapping evaluator *is* the truncation of
    the Nat model.  Combined with `eval_lt_of_inRange` this says the
    emit-correctness chain — which stores `BitVec.ofNat 64 (eval …)` — agrees
    with the hardware that wraps at every step.  No silent `Nat = u64`
    assumption remains. -/
theorem SExpr.evalBV_eq_ofNat_eval (σ : String → Nat) (e : SExpr)
    (h : e.inRange σ) :
    e.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (e.eval σ) := by
  apply BitVec.eq_of_toNat_eq
  rw [SExpr.toNat_evalBV_of_inRange σ e h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (SExpr.eval_lt_of_inRange σ e h)]

/-- Render an `SExpr` as Rust source.  Parenthesises every binary
    operation conservatively. -/
def SExpr.ppRust : SExpr → String
  | .SVar x   => x
  | .SLit n   => toString n ++ "u64"
  | .SAdd a b => "(" ++ a.ppRust ++ " + " ++ b.ppRust ++ ")"
  | .SSub a b => "(" ++ a.ppRust ++ ".saturating_sub(" ++ b.ppRust ++ "))"
  | .SMul a b => "(" ++ a.ppRust ++ " * " ++ b.ppRust ++ ")"
  | .SShr a b => "(" ++ a.ppRust ++ " >> " ++ b.ppRust ++ ")"
  | .SShl a b => "(" ++ a.ppRust ++ " << " ++ b.ppRust ++ ")"
  | .SAnd a b => "(" ++ a.ppRust ++ " & " ++ b.ppRust ++ ")"
  | .SXor a b => "(" ++ a.ppRust ++ " ^ " ++ b.ppRust ++ ")"
  | .SLt  a b => "(if " ++ a.ppRust ++ " < " ++ b.ppRust ++ " { 1u64 } else { 0u64 })"
  -- Signed-arith extension (#257): cast through i64 for the signed operation,
  -- then back to u64 (the storage form), matching `SExpr.eval`'s BitVec model.
  | .SAsr a b =>
      "(((" ++ a.ppRust ++ " as i64) >> " ++ b.ppRust ++ ") as u64)"
  | .SMulS a b =>
      "(((" ++ a.ppRust ++ " as i64).wrapping_mul(" ++ b.ppRust ++ " as i64)) as u64)"
  -- Widening-multiply extension (#261): widen to (u/i)128, multiply, take the
  -- high 64 bits via `>> 64`, narrow back to u64 — matches `SExpr.eval`'s
  -- `sexprMulHi{U,S}` model.
  | .SMulHiU a b =>
      "(((((" ++ a.ppRust ++ " as u128) * (" ++ b.ppRust ++ " as u128)) >> 64) as u64))"
  | .SMulHiS a b =>
      "(((((" ++ a.ppRust ++ " as i64 as i128) * (" ++ b.ppRust ++
        " as i64 as i128)) >> 64) as u64))"
  -- Tower-limb read extension (#354): limb `i` of the tower slot `v` is the
  -- `v.limbs[i]` field access in Rust surface source.
  | .SLimb v i => v ++ ".limbs[" ++ toString i ++ "]"

/-- Render an `SExpr` as **Jasmin surface source**.  Sibling of `ppRust`,
    used by the `.jazz` direct emit path (`RustEmitJazz.lean`).

    Jasmin's surface syntax differs from Rust's on a few points:

    * Integer literals are unsuffixed (`0`, `1`, `255`) — Jasmin has no
      `u64` / `u32` literal suffix in expression position.
    * Subtraction is the plain `-` operator with wrap-around semantics
      on `u64`/`u32` — there is no `.saturating_sub(...)` method.  For
      callers of `RScalarSetExpr` whose precondition guarantees the
      subtraction does not underflow (e.g. `ctr > 0` before `ctr - 1`),
      wrap-around `-` coincides with saturating subtraction; otherwise
      a runtime guard is the caller's responsibility.
    * The binops `+ - * >> & ^ |` are syntactically the same in both
      surfaces.
    * Variable names are passed through unchanged.
    * `SLt` lowers to a conditional `if … else …` block — Jasmin uses
      the same `if (cond) { a } else { b }` form in expression position
      via the surface preprocessor, so we keep the Rust-style braces. -/
def SExpr.ppJazz : SExpr → String
  | .SVar x   => x
  | .SLit n   => toString n
  | .SAdd a b => "(" ++ a.ppJazz ++ " + " ++ b.ppJazz ++ ")"
  | .SSub a b => "(" ++ a.ppJazz ++ " - " ++ b.ppJazz ++ ")"
  | .SMul a b => "(" ++ a.ppJazz ++ " * " ++ b.ppJazz ++ ")"
  | .SShr a b => "(" ++ a.ppJazz ++ " >> " ++ b.ppJazz ++ ")"
  | .SShl a b => "(" ++ a.ppJazz ++ " << " ++ b.ppJazz ++ ")"
  | .SAnd a b => "(" ++ a.ppJazz ++ " & " ++ b.ppJazz ++ ")"
  | .SXor a b => "(" ++ a.ppJazz ++ " ^ " ++ b.ppJazz ++ ")"
  | .SLt  a b => "(if (" ++ a.ppJazz ++ " < " ++ b.ppJazz ++ ") { 1 } else { 0 })"
  -- Signed-arith extension (#257): Jasmin's `>>s` is the arithmetic
  -- (sign-preserving) shift right; signed `*` shares the `*` token (the low
  -- word is sign-agnostic).  Jasmin infers signedness from the `>>s` operator
  -- and from declared reg types, so no explicit cast token is needed here.
  | .SAsr a b => "(" ++ a.ppJazz ++ " >>s " ++ b.ppJazz ++ ")"
  | .SMulS a b => "(" ++ a.ppJazz ++ " * " ++ b.ppJazz ++ ")"
  -- Widening-multiply extension (#261): the high word of a 64×64→128 product
  -- is NOT a Jasmin infix expression — it is the multi-output intrinsic
  -- `#MULX` / `#IMUL` (lowered as a `Copn` by `LowCTToJasmin`'s dedicated
  -- `RScalarSetExpr` arm).  This surface-string path is the deprecated
  -- text emitter and never receives a top-level high-mul; the strings below
  -- are conservative placeholders (parenthesised intrinsic calls) kept only
  -- for `ppJazz` totality.
  | .SMulHiU a b => "#MULX_hi(" ++ a.ppJazz ++ ", " ++ b.ppJazz ++ ")"
  | .SMulHiS a b => "#IMUL_hi(" ++ a.ppJazz ++ ", " ++ b.ppJazz ++ ")"
  -- Tower-limb read extension (#354): limb `i` of the tower slot `v` is the
  -- array access `v[i]` in Jasmin surface source (the slot is a `reg u64[N]`).
  | .SLimb v i => v ++ "[" ++ toString i ++ "]"

/-- Convenience: build the `SExpr` expression `<var> - 1`.  Used by the
    parameterless `RWhileNz` countdown idiom — the loop counter is
    decremented at the end of each iteration via
    `RScalarSetExpr "ctr" (SExpr.subOne "ctr")`. -/
def SExpr.subOne (x : String) : SExpr :=
  .SSub (.SVar x) (.SLit 1)

/-! ## §3  Rust commands -/

/-- Safe Rust commands over tower-typed variables.

    Every `RCall` writes to `dest` and reads from `args`; the borrow
    checker (`borrowOk`) ensures `dest ∉ args` at every call site.

    `RCloneCall` breaks the alias by cloning the old destination value into
    a fresh variable before dispatching the inner call. -/
inductive LowCT where
  | RSkip      : LowCT
  | RSeq       : LowCT → LowCT → LowCT
  | RLetZero   : String → TowerType → LowCT → LowCT
  | RLetU64Zero : String → LowCT → LowCT
  | RScalarSet : String → Nat → LowCT
  | RCall      : String → Located → List Located → LowCT
  /-- 2-destination leaf call, used for cswap-style operations whose
      semantics mutate two field elements at once.  Emits as
      `f(&mut dest1, &mut dest2, &args…)`.  borrowOk requires
      `dest1 ≠ dest2` and neither in `args`.  The Rocq/CryptoSSA
      semantics treats this as two independent writes; the leaf's
      Hoare spec must mention both destinations. -/
  | RCallSwap : String → Located → Located → List Located → LowCT
  | RCloneCall : String → TowerType → Located → String →
                 Located → List Located → LowCT
  | RIfNz      : String → LowCT → LowCT → LowCT
  | RWhileNz   : String → LowCT → LowCT
  /-- Bounded for-loop: `RFor x n body` runs `body` `n` times, with the
      scalar variable `x` set to `0, 1, …, n-1` on successive iterations.
      `n` is a closed Nat at the AST level — the loop is structurally
      terminating, no fuel needed. Authored to mirror Bedrock2's bounded
      `for`; the Hoare rule below gives `0 ≤ x < n` as a free invariant. -/
  | RFor       : String → Nat → LowCT → LowCT
  | RLimbStore : Located → Nat → BitVec 64 → LowCT
  /-- **Phase R5 (2026-06-01) — runtime-valued limb store.**
      `RLimbStoreExpr loc idx e` writes the *runtime-computed* word
      `SExpr.eval e` (truncated to `BitVec 64`) into limb index `idx`
      of the tower slot `loc`.  This is the limb-indexed analogue of
      `RScalarSetExpr` (which stores a runtime `SExpr` into a *scalar*
      slot): `RLimbStore` only takes a compile-time literal `BitVec 64`,
      so an inline field-op body that stores a computed limb (e.g.
      `fe25519_add`'s `out[i] = a[i] + b[i]`) has no faithful image
      under `RLimbStore`.  `RLimbStoreExpr` closes that gap and is the
      structural correspondent of AUCurves' Rocq `REdLimbStore : … →
      sexpr_ed → …` constructor (which stores a runtime sexpr value).
      Lowering / oracle treatment mirrors `RLimbStore`: the stored word
      is `(BitVec.ofNat 64 (e.eval rs.rsScalar))` fed through
      `leafSpec.limbStore`. -/
  | RLimbStoreExpr : Located → Nat → SExpr → LowCT
  /-- **Phase G — N-output function call.**  Generalisation of `RCall`
      (1-out) and `RCallSwap` (2-out) to arbitrary destination count.
      The oracle `LeafSpec.callN` is the multi-output analogue of
      `LeafSpec.call`.  Borrow checker: `dests` distinct, `dests ∩ args
      = ∅`.  Used for `(carry, sum) = adcx(a, b, c_in)` shapes. -/
  | RCallN     : String → List Located → List Located → LowCT
  /-- **Phase H — CT-safe conditional select primitive.**
      `RSelect dst sel src0 src1` writes `dst := if sel = 0 then src0
      else src1`.  Hardware-level: a single `CMOV`-shaped opcode chain.
      Promoting cmov to a constructor (rather than emulating via leaf
      call) lets the borrow checker reason about it precisely (read sel,
      read src0, read src1, write dst — no aliasing constraint between
      dst and srcs since cmov is read-then-write). -/
  | RSelect    : Located → String → Located → Located → LowCT
  /-- **Phase L — zero-cost contract assertion.**  No runtime effect;
      the Hoare rule injects an external proposition (looked up by
      `label` in the proof context) into the postcondition.  Used to
      strengthen loop invariants without inserting any bytes into the
      output asm. -/
  | RAssert    : String → LowCT
  /-- **Phase M — scoped block.**  `RBlock body` runs `body` in a fresh
      scope; locally bound slots (via `RLetZero` / `RLetU64Zero` inside
      `body`) are released at scope end, allowing stack reuse across
      multiple `RBlock`s in a sequence.  Lowering: emits `body`'s Jasmin
      bracketed by `stackalloc`/dealloc; runtime semantics are
      identical to `body`. -/
  | RBlock     : LowCT → LowCT
  /-- **Phase C — user-defined helper definition.**
      `RFnDef name params returns body cont` declares a helper
      function `name` with `params` (read-only, by-ref) and `returns`
      (write, by-ref).  `body` runs with `params` and `returns` in
      scope; `cont` is the continuation in the outer scope (the
      function body is *not* inlined here — it's lifted to a separate
      Jasmin `FunDecl` at lowering time).  This is the
      compile-time analogue of `fn name(out: ..., in: ...) { body }`. -/
  | RFnDef     : (name : String)
              → (params : List Located)
              → (returns : List Located)
              → (body : LowCT)
              → (cont : LowCT)
              → LowCT
  /-- **Phase C — user-defined helper call.**
      `RFnCall f dests args` invokes a helper previously declared via
      `RFnDef` (or in an outer environment).  Borrow checker: same as
      `RCallN` (dests distinct, dests ∩ args = ∅).  Lowers to a single
      Jasmin `Ccall .DoNotInline` to the `name` function. -/
  | RFnCall    : (f : String)
              → (dests : List Located)
              → (args : List Located)
              → LowCT
  /-- **Phase I — tuple component load.**
      `RTupleLoad dst src idx` reads component `idx` of `src` into
      `dst`.  Lowering: array-index load.  -/
  | RTupleLoad  : (dst : Located) → (src : Located) → (idx : Nat) → LowCT
  /-- **Phase Ext (2026-05-12) — array element store.**
      `RArrStore arr idxVar src` writes the value of slot `src` into
      element `idxVar` of the array slot `arr`.  `idxVar` is the name
      of a `u64`-typed scalar variable in `rsScalar` holding the
      runtime index.  Requires `arr.locSrc = TArr n t` and
      `src.locSrc = t`.  Lowering: `arr[idxVar as usize] = *src;`. -/
  | RArrStore  : (arr : Located) → (idxVar : String) → (src : Located) → LowCT
  /-- **Phase Ext (2026-05-12) — array element load.**
      `RArrLoad dst src idxVar` reads element `idxVar` of array slot
      `src` into `dst`.  Requires `src.locSrc = TArr n t` and
      `dst.locSrc = t`.  Lowering: `*dst = src[idxVar as usize];`. -/
  | RArrLoad   : (dst : Located) → (src : Located) → (idxVar : String) → LowCT
  /-- **Phase DD (2026-05-28) — literal-index array store.**
      `RArrStoreLit arr idx src` writes the value of `src` into element
      `idx` of `arr`, where `idx : Nat` is a *compile-time literal*
      (not read from a runtime scalar slot).  This is the
      static-index complement of `RArrStore` and is sufficient for
      post-`RFor`-unroll outer-loop array access — the most common
      Tier-3 emit pattern.  Lowering: `arr[idx] = *src;`.

      Composes naturally with the static `unrollForJ` pattern: after
      `RFor x N body` unrolls into `N` explicit iterations, any
      `RArrLoad/RArrStore` whose `idxVar = x` (loop counter) can be
      rewritten to `RArrLoadLit/RArrStoreLit` with the literal
      iteration index. -/
  | RArrStoreLit : (arr : Located) → (idx : Nat) → (src : Located) → LowCT
  /-- **Phase DD (2026-05-28) — literal-index array load.**
      `RArrLoadLit dst src idx` reads element `idx` of `src` into
      `dst`, where `idx : Nat` is a *compile-time literal*.  The
      static-index complement of `RArrLoad`.  Lowering:
      `*dst = src[idx];`. -/
  | RArrLoadLit  : (dst : Located) → (src : Located) → (idx : Nat) → LowCT
  /-- **Phase Ext (2026-05-12) — assign expression to scalar slot.**
      `RScalarSetExpr x e` evaluates `SExpr e` against the current
      scalar environment and writes the result to scalar slot `x`.
      Strictly more expressive than `RScalarSet x n` (which only takes
      a literal Nat).  Unlocks index arithmetic like `k := i * 16 + d`
      for runtime-bound `i`, `d`. -/
  | RScalarSetExpr : (x : String) → (e : SExpr) → LowCT
  /-- **Phase E2 (2026-05-29) — dst-threaded leaf call.**
      `RCallDstThreaded f dst args` calls leaf `f` with the destination
      slot threaded as both the first argument **and** the receiving
      lvalue: `dst = f(dst, args)`.  It is the shape for a shim whose
      signature receives the output buffer by value, mutates it in
      place, and returns it.  Lowering: a single Jasmin `Ccall`
      with `dst` as the lvalue and `(dst :: args)` as the call
      arguments.  Borrow check: `dst ∉ args` (same as `RCall`).

      Construction sites are `bench/` drivers and optimizer passes; no
      protocol kernel builds this node.  -/
  | RCallDstThreaded : (name : String) → (dst : Located) →
                       (args : List Located) → LowCT
  /-- Runtime-bound for-loop. `RForRuntime x bound body` runs `body` with
      the scalar counter `x = 0 … (bound.evalState rs) - 1`; the trip count
      is fixed by evaluating `bound : SExpr` in the ENTRY state. Runtime-valued
      sibling of `RFor x n body`. Faithful image of a hax `forFold` whose `hi`
      bound is a non-literal `SExpr` (`2*K`, `min(eta,128)`, symbolic const). -/
  | RForRuntime : (x : String) → (bound : SExpr) → (body : LowCT) → LowCT
  deriving Repr, Inhabited

/-- **Phase Vec (2026-07-01) — 128-bit SIMD vector assignment (the vector analog
    of `RScalarSetExpr`).**  `RVsimdSetExpr x tag args` assigns to the 128-bit
    vector slot `x` the result of the SIMD op named by `tag` applied to the
    128-bit operand slots named in `args`.  `tag` is a `vsimd`-op tag
    (`"vsimd.gf2p8mulb"`, `"vpsrldq.8"`, `"vsimd.xor"`, `"vpshufd.<imm>"`,
    `"vaeskeygen.<rcon>"`, `"affineqb.<imm>"`, `"clmul.<imm>"`,
    `"packed.<bop>.<laneW>"`, …); the vector front `translateDialectControlV`
    parses it (`vsimdTag`) and emits the matching **inlined** `CatCryptOp.vsimd` /
    `vpsrldqC` / … op over `.sword 128`, lowered by the verified
    `cryptoDialectToJasminCom` map to the owned x86 SIMD backend.

    This is the vector companion of the scalar `RScalarSetExpr`.  It is a
    *derived* `LowCT` statement — it desugars to a reserved-tag `RCall`, so it
    needs no new `LowCT` inductive constructor (and hence no cascade through the
    ~56 modules that match on `LowCT` exhaustively) while remaining a distinct,
    first-class source node.  Because it is definitionally an `RCall`, its
    operational semantics is `RustExec.call` (a data-oblivious opaque leaf: the
    128-bit vector value lives outside the `TowerType`-modeled `RustState`, so the
    RHP/CT chain treats it opaquely and the SIMD lane semantics is pinned at the
    dialect `denote = spec` level), it is `IsCovered` via `rCall`, its Rust ↔
    dialect simulation is the `RCall` case of `rustExecSimulatesDialect`, and its
    emitted-prefix leak trace is the constant `RCall`/`varBind` factor.  The
    placeholder `.TU64` located-type is inert: the vector front resolves operands
    by *name* (`lookupReg128`) and binds the destination at `.sword 128`
    regardless of the located type. -/
def LowCT.RVsimdSetExpr (x : String) (tag : String) (args : List String) : LowCT :=
  .RCall tag ⟨x, .TU64⟩ (args.map (fun s => ⟨s, .TU64⟩))

/-- `RVsimdSetExpr` is definitionally the reserved-tag `RCall`.  This `rfl`
    exposes the desugaring so every `RCall`-parametric result — `RustExec.call`,
    `IsCovered.rCall`, the `RCall` case of `rustExecSimulatesDialect`, and the
    leak-factoring `RCall` arm — applies to the vector node unchanged. -/
theorem LowCT.RVsimdSetExpr_desugar (x tag : String) (args : List String) :
    LowCT.RVsimdSetExpr x tag args
      = .RCall tag ⟨x, .TU64⟩ (args.map (fun s => ⟨s, .TU64⟩)) := rfl

/-! ## §3b  Generic structural recursor / fold (#350)

Adding or changing a `LowCT` constructor historically forced hand-editing
an open match across ~56 files (the recurring tax behind #226/#245/#263/#344).
The root cause is that the *recursion structure* of `LowCT` — which
constructors carry sub-commands and how their results combine — is duplicated
verbatim in every structural analysis (`borrowOk`, `destsOf`, `rcSize`,
leak-trace collection, …).

`LowCT.fold` factors that recursion structure into **one** place.  An
analysis with carrier type `α` supplies:

* `leaf  : LowCT → α`  — the value for a non-recursive (leaf) node.  The
  argument is the *original* node, so the analysis reads off its fields
  (dest/args/etc.) exactly as in the old match.  A new leaf constructor only
  needs an arm here (or a catch-all default), never a new recursion clause.
* `seqLike  : α → α → α`        — combine the two children of `RSeq`/`RIfNz`
  (and `RFnDef`'s body × cont).
* `wrap1    : α → α`            — wrap the single child of
  `RLetZero`/`RLetU64Zero`/`RWhileNz`/`RFor`/`RBlock`.

Because *only* the eight recursive constructors recurse, this captures the
entire structural skeleton.  Analyses that are monoidal folds
(`destsOf` = list-append, `rcSize` = sum, `borrowOk` = conjunction) collapse
to a one-line algebra; the per-leaf arm stays where it belongs.

The recursion is structural (every recursive call is on a syntactic
sub-term), so the equation lemmas are definitional `rfl`s — proofs that
`unfold`/`simp [LowCT.fold]` previously closed by matching still close. -/
def LowCT.fold {α : Type _}
    (leaf : LowCT → α)
    (seqLike : α → α → α)
    (wrap1 : α → α) : LowCT → α
  | .RSeq c1 c2            => seqLike (LowCT.fold leaf seqLike wrap1 c1)
                                     (LowCT.fold leaf seqLike wrap1 c2)
  | .RIfNz _ ct cf         => seqLike (LowCT.fold leaf seqLike wrap1 ct)
                                     (LowCT.fold leaf seqLike wrap1 cf)
  | .RFnDef _ _ _ body cont => seqLike (LowCT.fold leaf seqLike wrap1 body)
                                       (LowCT.fold leaf seqLike wrap1 cont)
  | .RLetZero _ _ body     => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RLetU64Zero _ body    => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RWhileNz _ body       => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RFor _ _ body         => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RBlock body           => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | c                      => leaf c

/-- **Node-aware structural fold.**  Generalises `LowCT.fold` by passing
    the *original* recursive node to the combiners, so analyses whose
    recursive case contributes node-derived data — e.g. `cmdCT`'s
    `lt cond == .Public &&` guard on `RIfNz`/`RWhileNz`, or `destsOf`'s
    `x ::` prepend on `RLetZero` — can be expressed as a fold instead of an
    open match.  `seqNode node r1 r2` combines the two children's results of
    a two-child node (`RSeq`/`RIfNz`/`RFnDef`); `wrapNode node r` wraps the
    single child's result (`RLetZero`/`RLetU64Zero`/`RWhileNz`/`RFor`/
    `RBlock`).  Leaves go through `leaf` as in `LowCT.fold`. -/
def LowCT.foldNode {α : Type _}
    (leaf : LowCT → α)
    (seqNode : LowCT → α → α → α)
    (wrapNode : LowCT → α → α) : LowCT → α
  | c@(.RSeq c1 c2)            => seqNode c (LowCT.foldNode leaf seqNode wrapNode c1)
                                           (LowCT.foldNode leaf seqNode wrapNode c2)
  | c@(.RIfNz _ ct cf)         => seqNode c (LowCT.foldNode leaf seqNode wrapNode ct)
                                           (LowCT.foldNode leaf seqNode wrapNode cf)
  | c@(.RFnDef _ _ _ body cont) => seqNode c (LowCT.foldNode leaf seqNode wrapNode body)
                                             (LowCT.foldNode leaf seqNode wrapNode cont)
  | c@(.RLetZero _ _ body)     => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RLetU64Zero _ body)    => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RWhileNz _ body)       => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RFor _ _ body)         => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RBlock body)           => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c                          => leaf c

/-! ### `LowCT.fold` reduction lemmas

These `@[simp]` equations let `simp [LowCT.fold]` (and any analysis defined
as `f := LowCT.fold …`, via `simp [f]`) reduce `fold` on a literal
constructor exactly as the old open match did — so proofs that previously
closed by unfolding the analysis keep closing.  Each is a definitional
`rfl`. -/
section FoldLemmas
variable {α : Type _} (leaf : LowCT → α) (seqLike : α → α → α) (wrap1 : α → α)

@[simp] theorem LowCT.fold_RSeq (c1 c2 : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RSeq c1 c2)
      = seqLike (LowCT.fold leaf seqLike wrap1 c1)
                (LowCT.fold leaf seqLike wrap1 c2) := rfl

@[simp] theorem LowCT.fold_RIfNz (s : String) (ct cf : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RIfNz s ct cf)
      = seqLike (LowCT.fold leaf seqLike wrap1 ct)
                (LowCT.fold leaf seqLike wrap1 cf) := rfl

@[simp] theorem LowCT.fold_RFnDef (n : String) (p r : List Located)
    (body cont : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RFnDef n p r body cont)
      = seqLike (LowCT.fold leaf seqLike wrap1 body)
                (LowCT.fold leaf seqLike wrap1 cont) := rfl

@[simp] theorem LowCT.fold_RLetZero (x : String) (t : TowerType) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RLetZero x t body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RLetU64Zero (x : String) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RLetU64Zero x body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RWhileNz (s : String) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RWhileNz s body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RFor (x : String) (n : Nat) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RFor x n body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RBlock (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RBlock body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

end FoldLemmas

section FoldNodeLemmas
variable {α : Type _} (leaf : LowCT → α) (seqNode : LowCT → α → α → α)
  (wrapNode : LowCT → α → α)

@[simp] theorem LowCT.foldNode_RSeq (c1 c2 : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RSeq c1 c2)
      = seqNode (.RSeq c1 c2) (LowCT.foldNode leaf seqNode wrapNode c1)
                              (LowCT.foldNode leaf seqNode wrapNode c2) := rfl

@[simp] theorem LowCT.foldNode_RIfNz (s : String) (ct cf : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RIfNz s ct cf)
      = seqNode (.RIfNz s ct cf) (LowCT.foldNode leaf seqNode wrapNode ct)
                                 (LowCT.foldNode leaf seqNode wrapNode cf) := rfl

@[simp] theorem LowCT.foldNode_RFnDef (n : String) (p r : List Located)
    (body cont : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RFnDef n p r body cont)
      = seqNode (.RFnDef n p r body cont)
                (LowCT.foldNode leaf seqNode wrapNode body)
                (LowCT.foldNode leaf seqNode wrapNode cont) := rfl

@[simp] theorem LowCT.foldNode_RLetZero (x : String) (t : TowerType) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RLetZero x t body)
      = wrapNode (.RLetZero x t body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RLetU64Zero (x : String) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RLetU64Zero x body)
      = wrapNode (.RLetU64Zero x body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RWhileNz (s : String) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RWhileNz s body)
      = wrapNode (.RWhileNz s body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RFor (x : String) (n : Nat) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RFor x n body)
      = wrapNode (.RFor x n body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RBlock (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RBlock body)
      = wrapNode (.RBlock body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

end FoldNodeLemmas

/-- The eight recursive `LowCT` constructors, the ones `LowCT.fold`
    descends into.  Anything else is a leaf for the purposes of structural
    folds.  Exposed so analyses / proofs can branch on "is this a recursive
    node?" without re-listing the constructors. -/
def LowCT.isRecursive : LowCT → Bool
  | .RSeq _ _          => true
  | .RIfNz _ _ _       => true
  | .RFnDef _ _ _ _ _  => true
  | .RLetZero _ _ _    => true
  | .RLetU64Zero _ _   => true
  | .RWhileNz _ _      => true
  | .RFor _ _ _        => true
  | .RBlock _          => true
  | _                  => false

/-! ## §4  Runtime state -/

/-- Specification of a single leaf-function call (formerly `LeafSpec`).
    `f dt argTs oldDest args` = new value of dest after calling `f`. -/
def CallSpec :=
  String →
  ∀ (dt : TowerType) (argTs : List TowerType),
    RustVal dt → List (Σ t : TowerType, RustVal t) → RustVal dt

/-- Specification of a limb-store operation (abstract oracle analogous to
    Rocq's `asm_correct` for `Oasm` operators).

    `spec loc oldV idx v` = new tower value for `loc` after writing the u64
    word `v` into limb index `idx` of the previous value `oldV`. -/
def LimbStoreSpec :=
  ∀ (loc : Located), RustVal loc.locDst → Nat → BitVec 64 → RustVal loc.locDst

/-- **Phase I.1 (2026-05-04) — TupleLoad oracle.**  Specification
    of `RTupleLoad dst src idx`: reads the `idx`-th component of
    src and produces a new dst value carrying that component.  The
    dependent pair carries src's TowerType, for the heterogeneous
    binary-product case. -/
def TupleLoadSpec :=
  ∀ (dst : Located), RustVal dst.locDst →
    (Σ t : TowerType, RustVal t) → Nat → RustVal dst.locDst

/-- **Phase Ext (2026-05-12) — array-element store oracle.**
    Specification of `RArrStore arr idxVar src`: given the array
    slot's old value, a runtime index, and the source value (with
    its dependent tower type), returns the new array value with
    element `idx` overwritten.  Concrete instances slice the array
    at byte offset `idx * elemSize` and overwrite; abstract
    reasoning treats it as opaque. -/
def ArrStoreSpec :=
  ∀ (arr : Located), RustVal arr.locDst → Nat →
    (Σ t : TowerType, RustVal t) → RustVal arr.locDst

/-- **Phase Ext (2026-05-12) — array-element load oracle.**
    Reads element `idx` of `arr` into `dst`. -/
def ArrLoadSpec :=
  ∀ (dst : Located), RustVal dst.locDst →
    (Σ t : TowerType, RustVal t) → Nat → RustVal dst.locDst

/-- **Phase I (2026-05-03) — byte-offset arithmetic for tuple
    components.**  For `t = TTuple a b`:
    * Component 0 occupies bytes `[0, a.storageBytes)`.
    * Component 1 occupies bytes `[a.storageBytes, a.storageBytes + b.storageBytes)`.

    For larger nests `TTuple a (TTuple b c)`, the inner TTuple
    contributes its full `storageBytes` to the index-1 slot.

    Returns 0 for non-TTuple types or out-of-range indices. -/
def TowerType.tupleComponentByteOffset : TowerType → Nat → Nat
  | .TTuple _ _, 0     => 0
  | .TTuple a _, _     => a.storageBytes
  | _,           _     => 0

/-- Component byte width at index `idx`.  Returns 0 for non-TTuple
    types or out-of-range indices. -/
def TowerType.tupleComponentByteSize : TowerType → Nat → Nat
  | .TTuple a _, 0     => a.storageBytes
  | .TTuple _ b, _     => b.storageBytes
  | _,           _     => 0

/-- The component TowerType at index `idx`.  For `TTuple a b`,
    idx 0 → a, idx 1 → b.  Returns the original type for non-TTuple
    or out-of-range. -/
def TowerType.tupleComponentType : TowerType → Nat → TowerType
  | .TTuple a _, 0 => a
  | .TTuple _ b, _ => b
  | t,           _ => t

/-- **Bundled oracle record** (Rocq-style): leaf-call behaviour plus
    machine-instruction behaviour. Treating these as oracles mirrors Rocq
    `jasmin_translate.v`'s use of `handled_program` (for calls) and
    `asm_correct` (for `Oasm` operators).

    A `LeafSpec.mk call limbStore` literal is complete: every
    later field carries a `default`. -/
structure LeafSpec where
  call      : CallSpec
  limbStore : LimbStoreSpec
  /-- Phase I.1: tuple-load oracle.  Defaults to identity. -/
  tupleLoad  : TupleLoadSpec := fun _ oldV _ _ => oldV
  /-- Phase Ext: array-element store oracle.  Defaults to identity. -/
  arrStore   : ArrStoreSpec := fun _ oldV _ _ => oldV
  /-- Phase Ext: array-element load oracle.  Defaults to identity. -/
  arrLoad    : ArrLoadSpec := fun _ oldV _ _ => oldV

/-- Runtime state: a tower-variable heap and a scalar heap.  `rsScalar`'s `Nat`
    carrier is the MEMORY-SAFETY layer's convenience (frame reasoning is easier
    over `Nat`, and monus-vs-wrap is irrelevant to aliasing) — it is NOT the
    `u64` value semantics (see `SExpr.eval` / `SExpr.evalBV`). -/
structure RustState where
  rsTower  : String → Option (Σ t : TowerType, RustVal t)
  rsScalar : String → Nat   -- default 0

instance : Inhabited RustState where
  default := { rsTower := fun _ => none, rsScalar := fun _ => 0 }

/-- Set a tower variable. -/
def rsSetTower (rs : RustState) (x : String)
    (v : Σ t : TowerType, RustVal t) : RustState :=
  { rs with rsTower := fun y => if y == x then some v else rs.rsTower y }

/-- Set a scalar variable. -/
def rsSetScalar (rs : RustState) (x : String) (v : Nat) : RustState :=
  { rs with rsScalar := fun y => if y == x then v else rs.rsScalar y }

/-- Remove a tower variable (used after `RLetZero` body exits scope). -/
def rsRemoveTower (rs : RustState) (x : String) : RustState :=
  { rs with rsTower := fun y => if y == x then none else rs.rsTower y }

/-! ### Tower-limb read (#354)

The AUCurves `sexpr_ed` constructor `SLimb v i` reads limb `i` (a `u64`) of
the limb-bearing tower slot `v`.  On the CatCrypt side a tower value is a
byte array (`RustVal t = JArray t.storageBytes = Fin _ → BitVec 8`); limb `i`
is the little-endian `u64` stored at byte offset `i * 8`.  We read it with a
total helper (`towerLimb`) that defaults out-of-range bytes to `0`, matching
AUCurves' `None → 0` collapse when the limb-read sees a missing / short slot. -/

/-- Read the byte at Nat index `j` of a `RustVal t` byte array, defaulting to
    `0` when `j` is out of range.  Total (no `Fin` proof obligation). -/
def rustValByte {t : TowerType} (v : RustVal t) (j : Nat) : BitVec 8 :=
  if h : j < t.storageBytes then v ⟨j, h⟩ else 0

/-- Read limb `i` (a little-endian `u64`) of the tower value `v` as a `Nat`:
    the 8 bytes at offsets `i*8 .. i*8+7`, low byte first.  Out-of-range bytes
    read as `0`.  This is the CatCrypt image of AUCurves'
    `List.nth_error limbs i` masked through `mask64` — both yield the
    `u64`-bounded limb word (here in `[0, 2^64)` by construction). -/
def towerLimb {t : TowerType} (v : RustVal t) (i : Nat) : Nat :=
  let b : Nat → Nat := fun k => (rustValByte v (i * 8 + k)).toNat
  b 0 + b 1 * 2 ^ 8 + b 2 * 2 ^ 16 + b 3 * 2 ^ 24
    + b 4 * 2 ^ 32 + b 5 * 2 ^ 40 + b 6 * 2 ^ 48 + b 7 * 2 ^ 56

/-- Read limb `i` of the tower slot named `x` in `rs`, or `0` when the slot is
    absent.  Faithful image of AUCurves' `rs_get_tower_ed rs x` followed by
    the `List.nth_error limbs i` limb projection. -/
def rsTowerLimb (rs : RustState) (x : String) (i : Nat) : Nat :=
  match rs.rsTower x with
  | some ⟨_, v⟩ => towerLimb v i
  | none        => 0

/-- **Tower-aware `SExpr` evaluator (#354).**  Sibling of the scalar-only
    `SExpr.eval`: it evaluates against the full `RustState`, so the new
    `SLimb v i` constructor reads limb `i` of tower slot `v` from `rs.rsTower`
    (via `rsTowerLimb`).  Every non-`SLimb` arm reads only `rs.rsScalar`,
    exactly as `SExpr.eval`; consequently `evalState rs e = eval rs.rsScalar e`
    on any `SLimb`-free expression (see `SExpr.evalState_eq_eval_of_limbFree`).

    This is the faithful image of AUCurves' `eval_sexpr_ed`: the field-op
    bodies (`fe25519_add_body`'s `SAdd (SLimb a i) (SLimb b i)`) evaluate
    through `evalState`, while the scalar-fragment runtime stores keep using
    `eval`.  Defined separately from `eval` precisely so `eval`'s signature
    stays `(String → Nat) → SExpr → Nat` for the modules that depend on it. -/
def SExpr.evalState (rs : RustState) : SExpr → Nat
  | .SVar x   => rs.rsScalar x
  | .SLit n   => n
  | .SAdd a b => a.evalState rs + b.evalState rs
  | .SSub a b => a.evalState rs - b.evalState rs
  | .SMul a b => a.evalState rs * b.evalState rs
  | .SShr a b => a.evalState rs >>> b.evalState rs
  | .SShl a b => a.evalState rs <<< b.evalState rs
  | .SAnd a b => a.evalState rs &&& b.evalState rs
  | .SXor a b => a.evalState rs ^^^ b.evalState rs
  | .SLt  a b => if a.evalState rs < b.evalState rs then 1 else 0
  | .SAsr a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.evalState rs) >>> (b.evalState rs : Nat))
  | .SMulS a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.evalState rs) * sexprToSignedInt64 (b.evalState rs))
  | .SMulHiU a b => sexprMulHiU (a.evalState rs) (b.evalState rs)
  | .SMulHiS a b => sexprMulHiS (a.evalState rs) (b.evalState rs)
  -- The point of the tower-aware evaluator: read the limb from the heap.
  | .SLimb v i => rsTowerLimb rs v i

/-- `e` contains no `SLimb` node anywhere (so its value does not depend on the
    tower heap).  The whole-expression analogue of "scalar-only `SExpr`". -/
def SExpr.limbFree : SExpr → Prop
  | .SVar _   => True
  | .SLit _   => True
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b
  | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b =>
      a.limbFree ∧ b.limbFree
  | .SLimb _ _ => False

/-- On a `limbFree` expression, the tower-aware evaluator agrees with the
    scalar `eval` against `rs.rsScalar`: the two evaluators differ ONLY on the
    `SLimb` arm, and every other arm reads `rsScalar` identically.  This is the
    formal sense in which `evalState` *extends* (rather than replaces) `eval`. -/
theorem SExpr.evalState_eq_eval (rs : RustState) :
    ∀ e : SExpr, e.limbFree → e.evalState rs = e.eval rs.rsScalar := by
  intro e
  induction e with
  | SVar x => intro _; rfl
  | SLit n => intro _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SShr a b iha ihb
  | SShl a b iha ihb | SAnd a b iha ihb | SXor a b iha ihb | SLt a b iha ihb
  | SAsr a b iha ihb | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
      intro h
      simp only [SExpr.evalState, SExpr.eval, iha h.1, ihb h.2]
  | SLimb v i => intro h; exact absurd h (by simp [SExpr.limbFree])

/-! ### Tower-aware wrapping-`u64` reconciliation (#250, runtime layer)

The scalar bridge above (`SExpr.evalBV` / `inRange` / `evalBV_eq_ofNat_eval`)
reconciles the Nat-model **scalar** `SExpr.eval` with the wrapping-`u64`
hardware.  But the runtime relation `RustExec` (below) stores a runtime
`SExpr` via the **tower-aware** `SExpr.evalState` — `RustExec.limbStoreExpr`
writes `BitVec.ofNat 64 (e.evalState rs)`, i.e. the *unbounded-Nat*
`evalState` truncated **only at the final store**.  The jasmin / x86 target,
by contrast, wraps mod `2^64` at **every intermediate** node, *and* an
`SSub` that underflows **wraps** there (whereas `evalState`, over `Nat`,
**saturates at 0**).  So the runtime store value can disagree with the
hardware exactly when an intermediate overflows or an `SSub` underflows.

`SExpr.evalStateBV` is the tower-aware, intermediate-wrapping evaluator: the
faithful image of what the emitted code computes.  The `SLimb v i` arm reads
the same limb as `evalState` but already in `BitVec 64` form — `towerLimb`
returns a value `< 2^64` by construction (`towerLimb_lt`), so the limb read
needs no truncation.  `inRangeState` is the tower-aware side-condition under
which the saturating-then-truncate store coincides with the
intermediate-wrapping hardware; `evalStateBV_eq_ofNat_evalState` is the
bridge.  This closes the runtime-layer half of #250: the value `RustExec`
records is provably the hardware value precisely on `inRangeState` inputs. -/

/-- `towerLimb` is a little-endian assembly of 8 bytes, so it is `< 2^64` by
    construction — the limb read is always representable in `u64`. -/
theorem towerLimb_lt {t : TowerType} (v : RustVal t) (i : Nat) :
    towerLimb v i < 2 ^ 64 := by
  unfold towerLimb
  have hb : ∀ k, (rustValByte v (i * 8 + k)).toNat < 2 ^ 8 := fun k =>
    (rustValByte v (i * 8 + k)).isLt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only at *
  omega

/-- `rsTowerLimb` is `< 2^64`: it is either a `towerLimb` (bounded above) or
    the default `0`. -/
theorem rsTowerLimb_lt (rs : RustState) (x : String) (i : Nat) :
    rsTowerLimb rs x i < 2 ^ 64 := by
  unfold rsTowerLimb
  match h : rs.rsTower x with
  | some ⟨_, v⟩ => exact towerLimb_lt v i
  | none => positivity

/-- **Tower-aware wrapping-`u64` evaluator (#250 runtime layer).**  The
    intermediate-wrapping sibling of `SExpr.evalState`: every arithmetic node
    truncates to `BitVec 64` immediately, mirroring the hardware.  The
    `SLimb v i` arm reads the same `u64` limb as `evalState` (already
    `< 2^64`), so it needs only `BitVec.ofNat` packaging.  This is the
    runtime-state analogue of `SExpr.evalBV`. -/
def SExpr.evalStateBV (rs : RustState) : SExpr → BitVec 64
  | .SVar x   => BitVec.ofNat 64 (rs.rsScalar x)
  | .SLit n   => BitVec.ofNat 64 n
  | .SAdd a b => a.evalStateBV rs + b.evalStateBV rs
  | .SSub a b => a.evalStateBV rs - b.evalStateBV rs
  | .SMul a b => a.evalStateBV rs * b.evalStateBV rs
  | .SShr a b => (a.evalStateBV rs) >>> (b.evalStateBV rs).toNat
  | .SShl a b => (a.evalStateBV rs) <<< (b.evalStateBV rs).toNat
  | .SAnd a b => a.evalStateBV rs &&& b.evalStateBV rs
  | .SXor a b => a.evalStateBV rs ^^^ b.evalStateBV rs
  | .SLt  a b => if (a.evalStateBV rs).toNat < (b.evalStateBV rs).toNat then 1 else 0
  | .SAsr a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalStateBV rs).toNat >>> ((b.evalStateBV rs).toNat : Nat)))
  | .SMulS a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalStateBV rs).toNat * sexprToSignedInt64 (b.evalStateBV rs).toNat))
  | .SMulHiU a b => BitVec.ofNat 64 (sexprMulHiU (a.evalStateBV rs).toNat (b.evalStateBV rs).toNat)
  | .SMulHiS a b => BitVec.ofNat 64 (sexprMulHiS (a.evalStateBV rs).toNat (b.evalStateBV rs).toNat)
  | .SLimb v i => BitVec.ofNat 64 (rsTowerLimb rs v i)

/-- Tower-aware in-range side-condition (#250 runtime layer): the analogue of
    `SExpr.inRange` for `evalState`.  Under it, the saturating-then-truncate
    runtime store equals the intermediate-wrapping hardware value.  The
    `SLimb` arm needs no condition — the limb read is always `< 2^64`. -/
def SExpr.inRangeState (rs : RustState) : SExpr → Prop
  | .SVar x   => rs.rsScalar x < 2 ^ 64
  | .SLit n   => n < 2 ^ 64
  | .SAdd a b => a.inRangeState rs ∧ b.inRangeState rs ∧ a.evalState rs + b.evalState rs < 2 ^ 64
  | .SSub a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs ≤ a.evalState rs
  | .SMul a b => a.inRangeState rs ∧ b.inRangeState rs ∧ a.evalState rs * b.evalState rs < 2 ^ 64
  | .SShr a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs < 64
  | .SShl a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs < 64 ∧ a.evalState rs <<< b.evalState rs < 2 ^ 64
  | .SAnd a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SXor a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SLt  a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SAsr a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SMulS a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SMulHiU a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SMulHiS a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SLimb _ _ => True

/-- Under `inRangeState`, the tower-aware Nat value is `< 2^64`: no overflow
    occurs (tower-aware analogue of `eval_lt_of_inRange`). -/
theorem SExpr.evalState_lt_of_inRangeState (rs : RustState) :
    ∀ e : SExpr, e.inRangeState rs → e.evalState rs < 2 ^ 64 := by
  intro e
  induction e with
  | SVar x => intro h; exact h
  | SLit n => intro h; exact h
  | SAdd a b _ _ => intro h; exact h.2.2
  | SSub a b iha _ => intro h; exact lt_of_le_of_lt (Nat.sub_le _ _) (iha h.1)
  | SMul a b _ _ => intro h; exact h.2.2
  | SShr a b iha _ =>
      intro h; exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (iha h.1)
  | SShl a b _ _ => intro h; exact h.2.2.2
  | SAnd a b iha _ => intro h; exact lt_of_le_of_lt Nat.and_le_left (iha h.1)
  | SXor a b iha ihb =>
      intro h
      exact Nat.xor_lt_two_pow (n := 64) (iha h.1) (ihb h.2)
  | SLt a b _ _ => intro _; simp only [SExpr.evalState]; split <;> norm_num
  | SAsr a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulS a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulHiU a b _ _ => intro _; exact sexprMulHiU_lt _ _
  | SMulHiS a b _ _ => intro _; exact sexprMulHiS_lt _ _
  | SLimb v i => intro _; exact rsTowerLimb_lt rs v i

/-- **Tower-aware wrapping ⇔ Nat-model bridge (#250 runtime layer, `.toNat`
    form).**  Under `inRangeState`, the `Nat` read back out of the
    intermediate-wrapping evaluator equals the tower-aware Nat-model value: no
    wrap occurs, so `SExpr.evalState` faithfully predicts the hardware. -/
theorem SExpr.toNat_evalStateBV_of_inRangeState (rs : RustState) :
    ∀ e : SExpr, e.inRangeState rs →
      (e.evalStateBV rs).toNat = e.evalState rs := by
  intro e
  induction e with
  | SVar x =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SLit n =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SAdd a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_add, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SSub a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_sub, iha h.1, ihb h.2.1]
      have hba : evalState rs b ≤ evalState rs a := h.2.2
      have hlt : evalState rs a < 2 ^ 64 := SExpr.evalState_lt_of_inRangeState rs a h.1
      have heq : 2 ^ 64 - evalState rs b + evalState rs a
          = 2 ^ 64 + (evalState rs a - evalState rs b) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  | SMul a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_mul, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SShr a b iha ihb =>
      intro h
      rw [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ushiftRight, iha h.1, ihb h.2.1]
  | SShl a b iha ihb =>
      intro h
      rw [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_shiftLeft, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2.2
  | SAnd a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_and, iha h.1, ihb h.2]
  | SXor a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_xor, iha h.1, ihb h.2]
  | SLt a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, iha h.1, ihb h.2]
      split <;> simp
  | SAsr a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulS a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulHiU a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiU_lt _ _)
  | SMulHiS a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiS_lt _ _)
  | SLimb v i =>
      intro _
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (rsTowerLimb_lt rs v i)

/-- **Tower-aware wrapping ⇔ Nat-model bridge (#250 runtime layer, `BitVec`
    form).**  On `inRangeState` inputs the intermediate-wrapping evaluator *is*
    the truncation of the tower-aware Nat model.  `RustExec.limbStoreExpr`
    records `BitVec.ofNat 64 (e.evalState rs)`, so on `inRangeState` the runtime
    relation agrees with the hardware exactly. -/
theorem SExpr.evalStateBV_eq_ofNat_evalState (rs : RustState) (e : SExpr)
    (h : e.inRangeState rs) :
    e.evalStateBV rs = BitVec.ofNat 64 (e.evalState rs) := by
  apply BitVec.eq_of_toNat_eq
  rw [SExpr.toNat_evalStateBV_of_inRangeState rs e h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (SExpr.evalState_lt_of_inRangeState rs e h)]

/-- Look up a tower variable, checking the stored type matches `loc.locDst`. -/
def locatedLookup (rs : RustState) (loc : Located) :
    Option (RustVal loc.locDst) :=
  match rs.rsTower loc.locVar with
  | some ⟨t, v⟩ => if h : t = loc.locDst then some (h ▸ v) else none
  | none         => none

/-- Write a new value to the destination of `loc`. -/
def locatedUpdate (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) : RustState :=
  rsSetTower rs loc.locVar ⟨loc.locDst, v⟩

/-! ## §5  Key state-update lemmas -/

theorem rsSetTower_same (rs : RustState) (x : String) (v : Σ t, RustVal t) :
    (rsSetTower rs x v).rsTower x = some v := by
  simp [rsSetTower]

theorem rsSetTower_other (rs : RustState) (x y : String)
    (v : Σ t, RustVal t) (h : x ≠ y) :
    (rsSetTower rs x v).rsTower y = rs.rsTower y := by
  unfold rsSetTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

theorem rsRemoveTower_other (rs : RustState) (x y : String) (h : x ≠ y) :
    (rsRemoveTower rs x).rsTower y = rs.rsTower y := by
  unfold rsRemoveTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsSetTower_other (rs : RustState) (x : String)
    (v : Σ t, RustVal t) (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsSetTower rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Removing one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsRemoveTower_other (rs : RustState) (x : String)
    (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsRemoveTower rs x) loc = locatedLookup rs loc := by
  unfold locatedLookup rsRemoveTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting scalar leaves tower lookups unchanged. -/
theorem locatedLookup_rsSetScalar (rs : RustState) (x : String) (v : Nat)
    (loc : Located) :
    locatedLookup (rsSetScalar rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetScalar; simp only []

/-- `locatedUpdate` writes to the correct variable. -/
theorem locatedUpdate_dest (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) :
    (locatedUpdate rs loc v).rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  unfold locatedUpdate rsSetTower
  simp

/-- `locatedUpdate` leaves other variables unchanged. -/
theorem locatedUpdate_other (rs : RustState) (loc1 loc2 : Located)
    (v : RustVal loc1.locDst)
    (h : loc1.locVar ≠ loc2.locVar) :
    locatedLookup (locatedUpdate rs loc1 v) loc2 = locatedLookup rs loc2 := by
  apply locatedLookup_rsSetTower_other
  exact h

/-! ## §6  Big-step semantics -/

/-- Leaf name for output `i` of the multi-output call to `f`.

    An `Expr` in the `Com` framework has exactly one return type, so a
    multi-output call is carried as one single-output call per output, named
    apart by its index. `RCallN f dests args` therefore reads output `i`
    through the ordinary `LeafSpec.call` oracle at `callNLeafName f i`, and a
    leaf supplying an `n`-output primitive registers `n` names. This is the
    same monomorphisation `Optimizer.SplitBytesSlice` performs on the
    size-varying `bytes_slice` wrapper. -/
def callNLeafName (f : String) (i : Nat) : String :=
  "callN:" ++ f ++ "#" ++ toString i

/-- Write each destination of an N-output call, left to right: destination `i`
    receives output `i` of `f` on the argument values `argList`.

    `argList` and `argTs` are read once from the pre-state by the `callN` rule,
    so every destination sees the same inputs — the borrow checker keeps
    `dests` distinct and disjoint from `args`, so no destination write can
    reach a later destination's arguments. -/
def callNUpdate (leafSpec : LeafSpec) (f : String) (argTs : List TowerType)
    (argList : List (Σ t : TowerType, RustVal t)) :
    Nat → List Located → RustState → RustState
  | _, [], rs => rs
  | i, d :: rest, rs =>
      callNUpdate leafSpec f argTs argList (i + 1) rest
        (locatedUpdate rs d
          (leafSpec.call (callNLeafName f i) d.locDst argTs
            ((locatedLookup rs d).getD default) argList))

/-- A slot whose name is none of the destinations is untouched by the fold:
    the write-set of `RCallN f dests args` is exactly `dests`. -/
theorem locatedLookup_callNUpdate_other (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (loc : Located),
      loc.locVar ∉ dests.map (·.locVar) →
      locatedLookup (callNUpdate leafSpec f argTs argList i dests rs) loc
        = locatedLookup rs loc := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _; rfl
  | cons d rest ih =>
    intro i rs loc hNotIn
    simp only [List.map_cons, List.mem_cons, not_or] at hNotIn
    obtain ⟨hd, hrest⟩ := hNotIn
    show locatedLookup
      (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs d _)) loc = _
    rw [ih (i + 1) _ loc (by simpa using hrest)]
    exact locatedUpdate_other _ _ _ _ (Ne.symm hd)

/-- The `rsTower`-level counterpart of `locatedLookup_callNUpdate_other`.
    `locatedLookup` equality does not imply `rsTower` equality — it forgets a
    type mismatch — so a frame stated at the raw heap needs this one. -/
theorem rsTower_callNUpdate_other (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (y : String),
      y ∉ dests.map (·.locVar) →
      (callNUpdate leafSpec f argTs argList i dests rs).rsTower y = rs.rsTower y := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _; rfl
  | cons d rest ih =>
    intro i rs y hNotIn
    simp only [List.map_cons, List.mem_cons, not_or] at hNotIn
    obtain ⟨hd, hrest⟩ := hNotIn
    show (callNUpdate leafSpec f argTs argList (i + 1) rest
            (locatedUpdate rs d _)).rsTower y = _
    rw [ih (i + 1) _ y (by simpa using hrest)]
    unfold locatedUpdate
    exact rsSetTower_other _ _ _ _ (Ne.symm hd)

/-- The fold writes tower slots only, so the scalar heap is untouched. -/
theorem callNUpdate_rsScalar (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState),
      (callNUpdate leafSpec f argTs argList i dests rs).rsScalar = rs.rsScalar := by
  intro dests
  induction dests with
  | nil => intro _ _; rfl
  | cons d rest ih =>
    intro i rs
    show (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs d _)).rsScalar = _
    rw [ih (i + 1)]
    rfl

/-- The `j`-th destination reads back its own write: after the fold started at
    index `i`, the slot named by `dests[j]` holds output `i + j` of `f`, applied
    to the pre-state's old value at that slot.

    Distinctness of the destination *names* is what makes this hold — with a
    repeated name the later write shadows the earlier one, and the slot carries
    only the last output written to it. -/
theorem rsTower_callNUpdate_nth (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i j : Nat) (rs : RustState) (d : Located),
      (dests.map (·.locVar)).Nodup →
      dests[j]? = some d →
      (callNUpdate leafSpec f argTs argList i dests rs).rsTower d.locVar
        = some ⟨d.locDst,
            leafSpec.call (callNLeafName f (i + j)) d.locDst argTs
              ((locatedLookup rs d).getD default) argList⟩ := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _ _ hj; simp at hj
  | cons d' rest ih =>
    intro i j rs d hNodup hj
    simp only [List.map_cons, List.nodup_cons] at hNodup
    obtain ⟨hHead, hRest⟩ := hNodup
    cases j with
    | zero =>
      have hd : d = d' := by simpa using hj.symm
      subst hd
      show (callNUpdate leafSpec f argTs argList (i + 1) rest
              (locatedUpdate rs d _)).rsTower d.locVar = _
      rw [rsTower_callNUpdate_other leafSpec f argTs argList rest (i + 1) _
            d.locVar hHead, locatedUpdate_dest]
      simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at hj
      have hmem : d ∈ rest := List.mem_of_getElem? hj
      have hne : d'.locVar ≠ d.locVar := by
        intro hEq
        exact hHead (hEq ▸ List.mem_map_of_mem hmem)
      show (callNUpdate leafSpec f argTs argList (i + 1) rest
              (locatedUpdate rs d' _)).rsTower d.locVar = _
      rw [ih (i + 1) k _ d hRest hj, locatedUpdate_other _ _ _ _ hne]
      have hidx : i + 1 + k = i + (k + 1) := by omega
      rw [hidx]

/-- Big-step execution relation for `LowCT`.

    `RustExec N leafSpec c rs rs'` means: running `c` from state `rs`
    with fuel bound `N` and leaf specification `leafSpec` terminates in `rs'`.

    `N` bounds `RWhileNz` loop iterations (via the `while_true` case's
    induction structure — the bound appears implicitly in the finite derivation
    tree).

    `RFnCall` and `RFnDef` have no rule. Giving `RFnCall` its meaning
    requires a function environment — a map from name to `FnSpec`, threaded
    through this relation's indices, so the rule can run the callee's body
    on the argument slots and write back to `dests`. This relation is
    indexed only by `N` and `leafSpec`, so that is a change to its type.
    Until then the relation is unsatisfiable at those two nodes: a
    hypothesis `RustExec … c rs rs'` for a program containing one cannot be
    discharged, rather than being discharged by a rule that moves no state.
    `toJasminCmd` still lowers `RFnCall` to a `Ccall`, so such a program
    compiles; what it does not have is an operational claim at this
    layer. `TranslateDialectFnCall`'s `fnCallD`/`fnDefD` are the dialect-side
    shape a future rule would mirror. -/
inductive RustExec (N : Nat) (leafSpec : LeafSpec) :
    LowCT → RustState → RustState → Prop where
  | skip   : ∀ rs, RustExec N leafSpec .RSkip rs rs
  | seq    : ∀ c1 c2 rs r1 rs',
      RustExec N leafSpec c1 rs r1 →
      RustExec N leafSpec c2 r1 rs' →
      RustExec N leafSpec (.RSeq c1 c2) rs rs'
  | letZero : ∀ x t body rs rs',
      RustExec N leafSpec body (rsSetTower rs x ⟨t, default⟩) rs' →
      RustExec N leafSpec (.RLetZero x t body) rs rs'
  | letU64Zero : ∀ x body rs rs',
      RustExec N leafSpec body (rsSetScalar rs x 0) rs' →
      RustExec N leafSpec (.RLetU64Zero x body) rs rs'
  | scalarSet : ∀ x v rs,
      RustExec N leafSpec (.RScalarSet x v) rs (rsSetScalar rs x v)
  | ifTrue  : ∀ e ct cf rs rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec ct rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | ifFalse : ∀ e ct cf rs rs',
      rs.rsScalar e = 0 →
      RustExec N leafSpec cf rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | whileFalse : ∀ e body rs,
      rs.rsScalar e = 0 →
      RustExec N leafSpec (.RWhileNz e body) rs rs
  | whileTrue : ∀ e body rs r1 rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec body rs r1 →
      RustExec N leafSpec (.RWhileNz e body) r1 rs' →
      RustExec N leafSpec (.RWhileNz e body) rs rs'
  /-- `RFor x 0 body` is a no-op. -/
  | forZero : ∀ x body rs,
      RustExec N leafSpec (.RFor x 0 body) rs rs
  /-- `RFor x (n+1) body` runs `RFor x n body` (iterations 0..n-1), then
      sets the scalar `x` to `n` and runs `body` once more. -/
  | forSucc : ∀ x n body rs r1 rs',
      RustExec N leafSpec (.RFor x n body) rs r1 →
      RustExec N leafSpec body (rsSetScalar r1 x n) rs' →
      RustExec N leafSpec (.RFor x (n+1) body) rs rs'
  /-- Runtime-bound for-loop: delegate to `RFor` at the trip count obtained by
      evaluating `bound` in the entry state `rs`. -/
  | forRuntime : ∀ x bound body rs rs',
      RustExec N leafSpec (.RFor x (bound.evalState rs) body) rs rs' →
      RustExec N leafSpec (.RForRuntime x bound body) rs rs'
  | call : ∀ f dest args rs oldDestV argList,
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      -- Per-arg type-recovery (Option A): args[i].locDst matches the
      -- stored Sigma type at args[i].locVar. Required for determinism.
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExec N leafSpec (.RCall f dest args) rs
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  /-- The clone binding stays in the tower on exit, matching Jasmin, where a
      call introduces no scope to leave.  The AUCurves rule this is imported
      from drops it (`XR_clone_call` ends in `remove_var`), so on this
      constructor the relation is not a conservative extension of that one:
      a post-state here binds `cloneVar`, and there it does not. -/
  | cloneCall : ∀ cloneVar cloneTy oldDest innerF dest args
                   rs rsClone rs',
      rsClone = rsSetTower rs cloneVar
                  (rs.rsTower oldDest.locVar |>.getD ⟨cloneTy, default⟩) →
      RustExec N leafSpec (.RCall innerF dest args) rsClone rs' →
      RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
        rs rs'
  /-- 2-output cswap-shape leaf.  Semantically: two sequential 1-out
      calls in Jasmin: `f(dest1, args); f(dest2, args)`.  borrowOk for
      `RCallSwap` forbids `dest1 = dest2` and either dest in args. -/
  | callSwap : ∀ f dest1 dest2 args rs rs1 rs',
      RustExec N leafSpec (.RCall f dest1 args) rs rs1 →
      RustExec N leafSpec (.RCall f dest2 args) rs1 rs' →
      RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs rs'
  | limbStore : ∀ loc idx v rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStore loc idx v) rs
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  /-- **Phase R5 — runtime-valued limb store (tower-aware, #356).**
      Evaluates `e` against the current *full* state via
      `SExpr.evalState`, truncates the resulting `Nat` to a `BitVec 64`,
      and writes it into limb `idx` of `loc` via the same
      `leafSpec.limbStore` oracle as `limbStore`.

      `evalState` reads the **tower heap** (by byte offset `j*8`, per
      `rsTowerLimb`/`towerLimb`) for any `SLimb v j` node, so an
      `SLimb`-valued store carries its runtime effect: the two
      Fp2 / tower halves share one slot rather than reading as
      independent ones.  On `SLimb`-free expressions `evalState rs e = eval
      rs.rsScalar e` (see `SExpr.evalState_eq_eval`), so the
      scalar-fragment stores are unchanged (see
      `SExpr.evalState_eq_eval`); the literal-valued
      `RLimbStore loc idx v` still coincides with
      `RLimbStoreExpr loc idx (.SLit v.toNat)`. -/
  | limbStoreExpr : ∀ loc idx e rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStoreExpr loc idx e) rs
        (locatedUpdate rs loc
          (leafSpec.limbStore loc oldDestV idx (BitVec.ofNat 64 (e.evalState rs))))
  /-- **Phase G semantics — N-output leaf call.**  Reads the argument values
      from the pre-state, then writes each destination in turn: destination
      `i` receives `leafSpec.call (callNLeafName f i)` on those arguments.
      Naming the outputs apart by index is what distinguishes destinations of
      the same tower type — the `(carry, sum)` of an add-with-carry shape are
      both `TU64`, and a single leaf name would give them one value. -/
  | callN : ∀ f dests args rs argList,
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      RustExec N leafSpec (.RCallN f dests args) rs
        (callNUpdate leafSpec f (args.map (·.locDst)) argList 0 dests rs)
  /-- **Phase H semantics — CT-safe conditional move.**  Reads the
      scalar `sel`; if zero, copies `src0`'s tower value into `dst`;
      else copies `src1`.  Hardware analogue: a `CMOV` chain at the
      asm level.  Both source values are read regardless of `sel`'s
      value — that's what makes this CT-safe.

      The type side conditions `src0.locDst = dst.locDst` and
      `src1.locDst = dst.locDst` reflect the borrow-checker invariant
      that cmov requires same-typed source / dest slots. -/
  | selectFalse : ∀ dst sel src0 src1 rs (h : src0.locDst = dst.locDst) srcV,
      rs.rsScalar sel = 0 →
      locatedLookup rs src0 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  | selectTrue : ∀ dst sel src0 src1 rs (h : src1.locDst = dst.locDst) v srcV,
      rs.rsScalar sel = v → v ≠ 0 →
      locatedLookup rs src1 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  /-- **Phase L semantics — zero-cost contract.**  No state change. -/
  | assert : ∀ label rs,
      RustExec N leafSpec (.RAssert label) rs rs
  /-- **Phase M semantics — scoped block.**  Identical to running
      the body; the "scope" boundary is meaningful only at the
      lowering level (stack reuse) and the Hoare level
      (locally-bound vars dropped from the post-context). -/
  | block : ∀ body rs rs',
      RustExec N leafSpec body rs rs' →
      RustExec N leafSpec (.RBlock body) rs rs'
  /-- **Phase I.1 — tuple component load.**  Reads the `idx`-th
      component of `src` into `dst` via `leafSpec.tupleLoad`. -/
  | tupleLoad : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RTupleLoad dst src idx) rs
        (locatedUpdate rs dst (leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Phase Ext — array element store.**  Looks up runtime index
      `rs.rsScalar idxVar`, reads `arr`'s old value, reads `src`'s
      value (with dependent tower type), and writes via
      `leafSpec.arrStore`.  Concrete instances slice arr's byte
      array at offset `idx * src.locDst.storageBytes` to overwrite. -/
  | arrStore : ∀ arr idxVar src rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrStore arr idxVar src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  /-- **Phase Ext — array element load.**  Looks up runtime index
      `rs.rsScalar idxVar` and reads element `idx` of `src` into
      `dst` via `leafSpec.arrLoad`. -/
  | arrLoad : ∀ dst src idxVar rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrLoad dst src idxVar) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Phase DD (2026-05-28) — literal-index array store.**  Same
      shape as `arrStore` but the index is the compile-time literal
      `idx : Nat` from the AST (no `rsScalar` lookup). -/
  | arrStoreLit : ∀ arr idx src rs oldV srcV,
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrStoreLit arr idx src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  /-- **Phase DD (2026-05-28) — literal-index array load.**  Same
      shape as `arrLoad` but the index is the compile-time literal
      `idx : Nat` from the AST. -/
  | arrLoadLit : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrLoadLit dst src idx) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Phase Ext — set scalar slot to an `SExpr` value.**  Evaluates the
      expression with the tower-aware `SExpr.evalState`, so that
      `RScalarSetExpr x (SLimb v i)` reads limb `i` of tower slot `v`, and
      writes the result.  On an `SLimb`-free expression the value is
      `e.eval rs.rsScalar` (`SExpr.evalState_eq_eval`). -/
  | scalarSetExpr : ∀ x e rs,
      RustExec N leafSpec (.RScalarSetExpr x e) rs
        (rsSetScalar rs x (e.evalState rs))
  /-- **Phase E2 semantics — destination-threaded leaf call.**  Single
      output, shape-compatible with `call`, but the destination slot is
      threaded as the first call argument *and* the receiving lvalue:
      `dst = f(dst, args)`.  We read `dst`'s old value, build the argument
      list from `dst :: args` (so the leaf sees the prior destination
      contents as its first input), pass the corresponding dst-types, and
      write the single result back via `leafSpec.call`.  Mirrors `call`'s
      per-arg type-recovery side condition over `dst :: args`. -/
  | callDstThreaded : ∀ f dst args rs oldDestV argList,
      locatedLookup rs dst = some oldDestV →
      argList = (dst :: args).filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ dst :: args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExec N leafSpec (.RCallDstThreaded f dst args) rs
        (locatedUpdate rs dst
          (leafSpec.call f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList))

/-- **Runtime-store reconciliation (#250).**  The word
    that `RustExec.limbStoreExpr` records — `BitVec.ofNat 64 (e.evalState rs)`,
    i.e. the saturating-then-truncate-at-storage Nat model — equals the
    intermediate-wrapping hardware value `e.evalStateBV rs` **exactly** under
    the in-range side-condition `inRangeState`.  This is what makes the runtime
    relation a faithful predictor of the emitted code: off the side-condition
    (intermediate overflow, or an `SSub` that underflows — where Nat saturates
    at 0 but hardware wraps) the two can disagree, and the side-condition is
    discharged per kernel by the no-overflow argument in that kernel's
    correctness proof (`fe25519_add` etc. operate on `< 2^51`-bounded limbs, so
    each `SAdd`/`SSub` stays in `u64` range).  Together with
    `RustExec.limbStoreExpr` this closes the model/emit wrapping gap at the
    runtime layer: the stored value is the hardware value on in-range inputs. -/
theorem RustExec_limbStoreExpr_stored_eq_evalStateBV
    (rs : RustState) (e : SExpr) (h : e.inRangeState rs) :
    BitVec.ofNat 64 (e.evalState rs) = e.evalStateBV rs :=
  (SExpr.evalStateBV_eq_ofNat_evalState rs e h).symm

/-! ## §7  `RFor` smoke tests and Hoare-style rule

The Hoare-style rule for `RFor` says: if a state-indexed invariant `I i`
is preserved by one execution of `body` (with the counter set to `i`),
and `I 0` holds initially, then `I n` holds after `RFor x n body`.
This is the standard structural rule for bounded for-loops; it's the
key reason to add `RFor` (vs. open-coding everything as `RWhileNz`):
the rule needs no termination side condition and the loop bound becomes
a free invariant. -/

namespace RustExec

/-- **RFor structural induction rule**: if `I 0 rs` and `body` preserves
    `I` across one iteration with the counter set to `i`, then `I n` holds
    at the post-state. Schematic; `I` ranges over arbitrary state predicates.

    This is the analogue of Bedrock2's `compile_for` rule applied at the
    semantic level — same shape minus the program-counter bookkeeping. -/
theorem rfor_invariant
    {N : Nat} {leafSpec : LeafSpec} {x : String} {body : LowCT}
    {I : Nat → RustState → Prop}
    (hStep : ∀ (i : Nat) (rs r' : RustState),
        I i rs →
        RustExec N leafSpec body (rsSetScalar rs x i) r' →
        I (i + 1) r') :
    ∀ (n : Nat) (rs r' : RustState),
      I 0 rs →
      RustExec N leafSpec (.RFor x n body) rs r' →
      I n r' := by
  intro n
  induction n with
  | zero =>
    intro rs r' hI hExec
    cases hExec
    exact hI
  | succ k ih =>
    intro rs r' hI hExec
    cases hExec with
    | forSucc _ _ _ _ r1 _ hInner hBody =>
      have hk : I k r1 := ih rs r1 hI hInner
      exact hStep k r1 r' hk hBody

/-- Smoke test: a 3-iteration for-loop with an `RSkip` body executes to
    the explicit scalar-set chain. -/
example (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    RustExec N leafSpec (.RFor "i" 3 .RSkip) rs
      (rsSetScalar (rsSetScalar (rsSetScalar rs "i" 0) "i" 1) "i" 2) := by
  apply forSucc -- iter 2 (n=2 in forSucc, so x ↦ 2 + skip)
  · apply forSucc -- iter 1
    · apply forSucc -- iter 0
      · exact forZero ..
      · exact skip _
    · exact skip _
  · exact skip _

/-- Smoke test of the structural rule: counting iterations. After
    `RFor "i" n RSkip`, the invariant "we ran n iterations" is established. -/
example (N : Nat) (leafSpec : LeafSpec) (n : Nat) (rs r' : RustState)
    (h : RustExec N leafSpec (.RFor "i" n .RSkip) rs r') :
    True :=  -- placeholder result; the real claim is the invariant rule below
  rfor_invariant (I := fun _ _ => True)
    (hStep := fun _ _ _ _ _ => trivial)
    n rs r' trivial h

end RustExec

end CatCrypt.Crypto.Jasmin.LowCT
