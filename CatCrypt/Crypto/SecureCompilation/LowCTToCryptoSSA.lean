/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-!
# LowCT → CryptoSSA substrate

The substrate of the `LowCT → catCryptDialect` front: the
`TowerType → CryptoTy` encoding (`encodeTy`), the name-to-De-Bruijn map
(`VarMap`), the single-scalar-branch view (`SingleScalarSet` /
`asSingleScalarSet`) used by the `RIfNz` φ-merge, and the argument
resolver (`resolveLocatedArgs`).

One front consumes this substrate: `translateDialectControl`
(`Dialects/TranslateDialectDirectControl.lean`), which lowers `LowCT` directly to
`Com catCryptDialect`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. TowerType → CryptoTy encoding -/

/-- Encode a `TowerType` as a `CryptoTy`. Tower types become `memref`s
    whose length is the number of 64-bit limbs. -/
def encodeTy : TowerType → CryptoTy
  | .TU64     => .sword 64
  -- u8 / u32 scalars.  These only arise in byte-packing kernels; they
  -- map to small memrefs (1 / 4 bytes) so the memref-uniform witness
  -- lemmas apply.
  | .TU8      => .memref 1
  | .TU32     => .memref 4
  | .TFp      => .memref 6      -- 48 bytes = 6 limbs  (BLS12-381)
  | .TFp2     => .memref 12     -- 96 bytes = 12 limbs
  | .TFp6     => .memref 36     -- 288 bytes = 36 limbs
  | .TFp12    => .memref 72     -- 576 bytes = 72 limbs
  | .TFp25519 => .memref 5      -- 40 bytes = 5 limbs (Curve25519, radix-2^51)
  | .TFp25519_64 => .memref 4   -- 32 bytes = 4 limbs (Curve25519, saturated)
  -- Byte-encoded refs.
  | .TFpL25519 => .memref 4
  | .TFpP256 => .memref 4
  | .TFp25519_4Bounded _ => .memref 4
  -- Round byteSize up to 64-bit-limb count for memref encoding.
  | .TFpGen _ n => .memref ((n + 7) / 8)
  | .TFp2Gen _ n => .memref ((n + 7) / 8)
  | .TTuple a b => .memref ((a.storageBytes + b.storageBytes + 7) / 8)
  | .TBytes n => .memref ((n + 7) / 8)
  -- Array type — flatten to a byte-encoded memref.
  | .TArr n t => .memref ((n * t.storageBytes + 7) / 8)
  -- Polynomial-mod-q — flatten to byte-encoded memref.
  | .TPolyMod q n => .memref ((n * ((Nat.log2 q + 1 + 7) / 8) + 7) / 8)
  | .TPolyVec q n k => .memref ((k * (n * ((Nat.log2 q + 1 + 7) / 8)) + 7) / 8)
  | .TPolyMat q n k m =>
      .memref ((k * m * (n * ((Nat.log2 q + 1 + 7) / 8)) + 7) / 8)

/-! ## 2. VarMap: LowCT var names → typed De Bruijn vars -/

/-- A per-context mapping from LowCT variable names to typed De Bruijn
    variables in the CryptoSSA context `Γ`. -/
structure VarMap (Γ : Ctx) where
  lookup : String → Option (Σ t : CryptoTy, CVar Γ t)

namespace VarMap

/-- Empty environment: no names bound. -/
def empty : VarMap [] := { lookup := fun _ => none }

/-- Weaken a VarMap by a new binding at the top of the context. -/
def weaken {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ) : VarMap (t :: Γ) :=
  { lookup := fun name =>
      match vm.lookup name with
      | some ⟨t', v⟩ => some ⟨t', .there v⟩
      | none => none }

/-- Bind/rebind a name at the top of the context. Used both for fresh
    bindings and SSA-style reassignment. -/
def bind {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ) (name : String) :
    VarMap (t :: Γ) :=
  { lookup := fun n =>
      if n = name then some ⟨t, .here⟩
      else match vm.lookup n with
           | some ⟨t', v⟩ => some ⟨t', .there v⟩
           | none => none }

end VarMap

/-! ## 3. Single-scalar branch view (for the `RIfNz` φ-merge)

For the symmetric `RIfNz` φ-merge sub-case we need to detect that both
branches are a single primitive binding whose RHS lives in the entry
context `Γ`. `SingleScalarSet` encodes exactly the `RScalarSet name n`
pattern (a `bvConst`-valued binding). -/

/-- The shape of a single straight-line LowCT we can phi-merge. -/
structure SingleScalarSet where
  name : String
  val  : Nat

/-- Try to view a `LowCT` as a single `RScalarSet`. -/
def asSingleScalarSet : LowCT → Option SingleScalarSet
  | .RScalarSet name n => some { name := name, val := n }
  | _                  => none

/-! ## 4. Argument resolution -/

/-- Resolve a list of `Located` argument slots to typed De Bruijn
    variables in the current context. Returns `none` if any slot is
    unbound in the VarMap.

    This is a named helper (rather than an inline `List.foldr` at each
    call site) so that simulation proofs can `cases`/`rw` on its stable
    head symbol — `cases hMA : <foldr>` triggers Lean's motive-substitution
    quirk when the scrutinee is a `match` with `none` in a branch body, but
    the named helper sidesteps that path entirely. -/
def resolveLocatedArgs {Γ : Ctx} (vm : VarMap Γ) :
    List Located → Option (List (Σ t : CryptoTy, CVar Γ t))
  | [] => some []
  | a :: rest =>
    match vm.lookup a.locVar, resolveLocatedArgs vm rest with
    | some r, some rs => some (r :: rs)
    | _, _ => none

end CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
