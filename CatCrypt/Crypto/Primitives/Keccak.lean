/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Keccak-f[1600] Permutation

Constructive implementation of the Keccak-f[1600] permutation, the core
of SHA-3 and SHAKE (FIPS 202).

The state is a 5×5 array of 64-bit lanes (1600 bits total). Each round
applies five steps: θ, ρ, π, χ, ι.

All definitions are sealed with `@[irreducible]` to prevent evaluation
during proof checking.

## References

* FIPS 202 — SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions
* Keccak reference: https://keccak.team/keccak_specs_summary.html
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.Keccak

/-! ## State Representation -/

/-- Keccak state: 5×5 matrix of 64-bit words (1600 bits). -/
def KState := Fin 5 → Fin 5 → BitVec 64

instance : Inhabited KState := ⟨fun _ _ => 0⟩

/-- Zero state. -/
def KState.zero : KState := fun _ _ => 0

/-! ## Round Constants (FIPS 202, Section 3.2.5) -/

/-- The FIPS-202 ι round constants. Not `private`: a cross-module bridge proof
    (extraction ↔ this reference) has to name the table to unfold it, and a
    `private` name is not accessible outside its module. Reason over it by
    `simp [roundConstant, rcData]` — unfolding plus literal normalisation. Do not
    compute over it with `decide`, and never with `native_decide`. -/
def rcData : List (BitVec 64) := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
]

def roundConstant (r : Nat) : BitVec 64 := rcData.getD r 0

/-! ## Rotation Offsets (FIPS 202, Section 3.2.2) -/

/-- ρ rotation offsets: `rotOffsets x y` gives the rotation amount for lane (x,y).
    Public for the same reason as `rcData`. -/
def rotData : List (List Nat) := [
  [ 0, 36,  3, 41, 18],
  [ 1, 44, 10, 45,  2],
  [62,  6, 43, 15, 61],
  [28, 55, 25, 21, 56],
  [27, 20, 39,  8, 14]
]

def rotOffset (x y : Fin 5) : Nat :=
  ((rotData.getD x.val []).getD y.val 0) % 64

/-! ## Step Mappings -/

/-- θ step (FIPS 202, Section 3.2.1): column parity + XOR. -/
def theta (a : KState) : KState :=
  -- Column parities C[x] = a[x,0] ⊕ a[x,1] ⊕ a[x,2] ⊕ a[x,3] ⊕ a[x,4]
  let c : Fin 5 → BitVec 64 := fun x =>
    a x 0 ^^^ a x 1 ^^^ a x 2 ^^^ a x 3 ^^^ a x 4
  -- D[x] = C[x-1] ⊕ rot(C[x+1], 1)
  let d : Fin 5 → BitVec 64 := fun x =>
    c ⟨(x.val + 4) % 5, by omega⟩ ^^^ (c ⟨(x.val + 1) % 5, by omega⟩).rotateLeft 1
  fun x y => a x y ^^^ d x

/-- ρ step (FIPS 202, Section 3.2.2): lane rotation. -/
def rho (a : KState) : KState := fun x y =>
  (a x y).rotateLeft (rotOffset x y)

/-- π step (FIPS 202, Section 3.2.3): lane permutation. -/
def pi (a : KState) : KState := fun x y =>
  a ⟨(x.val + 3 * y.val) % 5, by omega⟩ x

/-- χ step (FIPS 202, Section 3.2.4): nonlinear mixing. -/
def chi (a : KState) : KState := fun x y =>
  let a1 := a ⟨(x.val + 1) % 5, by omega⟩ y
  let a2 := a ⟨(x.val + 2) % 5, by omega⟩ y
  a x y ^^^ (~~~a1 &&& a2)

/-- ι step (FIPS 202, Section 3.2.5): round constant addition. -/
def iota (a : KState) (rc : BitVec 64) : KState := fun x y =>
  if x.val == 0 && y.val == 0 then a x y ^^^ rc else a x y

/-! ## Full Round and Permutation -/

/-- One Keccak round: θ → ρ → π → χ → ι. -/
def keccakRound (a : KState) (rc : BitVec 64) : KState :=
  iota (chi (pi (rho (theta a)))) rc

/-- Keccak-f[1600]: 24 rounds of the permutation. -/
def keccakF (a : KState) : KState :=
  Fin.foldl 24 (init := a) fun s (r : Fin 24) =>
    keccakRound s (roundConstant r.val)

/-! ## State ↔ Byte Conversion -/

/-- Convert a byte array to a Keccak state (little-endian lane packing).
    Input is padded/truncated to 200 bytes. -/
def bytesToState (bytes : List UInt8) : KState := fun x y =>
  let laneIdx := 8 * (5 * y.val + x.val)
  Fin.foldl 8 (init := (0 : BitVec 64)) fun acc (i : Fin 8) =>
    let byte := (bytes.getD (laneIdx + i.val) 0).toNat
    acc ||| ((BitVec.ofNat 64 byte) <<< (8 * i.val))

/-- Convert a Keccak state to a byte list (200 bytes, little-endian). -/
def stateToBytes (s : KState) : List UInt8 :=
  let lanes := List.flatten <| (List.finRange 5).map fun y =>
    (List.finRange 5).map fun x => s x y
  List.flatten <| lanes.map fun lane =>
    (List.range 8).map fun i =>
      ((lane >>> (8 * i)).toNat % 256).toUInt8

/-! ## Seal all definitions -/

attribute [irreducible] keccakF keccakRound
attribute [irreducible] theta rho pi chi iota
attribute [irreducible] bytesToState stateToBytes
attribute [irreducible] roundConstant rotOffset

end CatCrypt.Crypto.Primitives.Keccak
