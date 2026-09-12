/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# ReprBridge: Array Int ↔ Vector UInt8 n

Conversion functions between haxpipeT's `Array Int` representation and
CatCrypt's `Vector UInt8 n` (the concrete `CryptoWord` type).

These are used to connect haxpipeT-extracted protocol surface code
(operating on `Array Int`) to CatCrypt security proofs (operating on
`Vector UInt8 n` via the `HPKEDependencies W` typeclass).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.ReprBridge

/-- Convert an `Array Int` (byte-level extraction representation) to
    `Vector UInt8 n`. Each `Int` is truncated to `UInt8` range. -/
def arrayIntToVec (a : Array Int) (n : Nat) (h : a.size = n := by omega) :
    Vector UInt8 n :=
  ⟨a.map fun i => i.toNat.toUInt8, by simp [Array.size_map, h]⟩

/-- Convert a `Vector UInt8 n` to `Array Int` (extraction representation). -/
def vecToArrayInt {n : Nat} (v : Vector UInt8 n) : Array Int :=
  v.toArray.map fun b => (b.toNat : Int)

/-- For any byte `b : UInt8`, the round-trip
    `(b.toNat : Int).toNat.toUInt8 = b`. The composition is identity on `UInt8`
    because `b.toNat < 256` makes the modular reduction in `Nat → UInt8` a no-op. -/
@[simp] theorem uint8_int_natCast_toNat_toUInt8 (b : UInt8) :
    (b.toNat : Int).toNat.toUInt8 = b := by
  simp [Int.toNat_natCast]

/-- Round-trip: `arrayIntToVec (vecToArrayInt v) = v`. -/
theorem arrayIntToVec_vecToArrayInt {n : Nat} (v : Vector UInt8 n) :
    arrayIntToVec (vecToArrayInt v) n
      (by simp [vecToArrayInt, Array.size_map, Vector.size_toArray]) = v := by
  ext i hi
  simp [arrayIntToVec, vecToArrayInt]

end CatCrypt.Hax.ReprBridge
