/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.KeccakSponge
public meta import CatCrypt.Crypto.Primitives.KeccakSponge
public import CatCryptCore.Tactics.KatGuard

/-!
# Keccak-f[1600] and the sponge on an array state

`Primitives.Keccak.keccakF` acts on the closure state `KState = Fin 5 → Fin 5 → BitVec 64`.
Compiled, each round re-evaluates the lanes of the previous round at every use, so the cost of
one permutation is exponential in the number of rounds. This module gives the permutation on
the array state `VState = Vector (BitVec 64) 25`, lane `(x, y)` at index `x + 5 y`, where every
step map produces a new array, and the sponge of `Primitives.KeccakSponge` over it.

The `@[csimp]` lemmas replace, in code compiled after this module, `keccakF` by its array form
wrapped in the conversions `ofK` and `toK`, and `sponge`, `sha3_256`, `sha3_512`, `shake128`,
`shake256` and `Primitives.SHAKE128.shake128` by their array forms. The last five are needed
because their callers compiled in earlier modules keep calling the closure permutation.

## Main definitions

* `toK`, `ofK`: the conversions between `VState` and `KState`.
* `thetaV`, `rhoV`, `piV`, `chiV`, `iotaV`, `roundV`, `keccakFV`: the permutation on `VState`.
* `absorbV`, `squeezeBlocksV`, `spongeV`: the sponge on `VState`.
* `sha3_256Is`: the known-answer predicate of SHA3-256, compiled after the `@[csimp]` lemmas.

## Main results

* `toK_keccakFV`: `toK (keccakFV v) = keccakF (toK v)`.
* `keccakF_eq_keccakFK`, `sponge_eq_spongeV`, `sha3_256_eq_sha3_256V`, …: the `@[csimp]`
  equalities.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.KeccakArray

open CatCrypt.Crypto.Primitives.Keccak
open CatCrypt.Crypto.Primitives.KeccakSponge

/-! ## The array state and the conversions -/

/-- The Keccak state as 25 lanes, lane `(x, y)` at index `x + 5 y`. -/
abbrev VState := Vector (BitVec 64) 25

/-- The 5×5 view of an array state: `toK v x y = v[x + 5 y]`. -/
def toK (v : VState) : KState := fun x y => v[x.val + 5 * y.val]

/-- The array of the 25 lanes of a closure state. -/
def ofK (a : KState) : VState :=
  Vector.ofFn fun i : Fin 25 => a ⟨i.val % 5, by omega⟩ ⟨i.val / 5, by omega⟩

/-- `toK` is a left inverse of `ofK`. -/
@[simp] theorem toK_ofK (a : KState) : toK (ofK a) = a := by
  funext x y
  simp only [toK, ofK, Vector.getElem_ofFn]
  congr 1 <;> ext <;> simp <;> omega

/-- `ofK` is a left inverse of `toK`. -/
@[simp] theorem ofK_toK (v : VState) : ofK (toK v) = v := by
  apply Vector.ext
  intro i hi
  simp only [ofK, toK, Vector.getElem_ofFn]
  congr 1
  omega

/-! ## The step maps on the array state -/

/-- θ on the array state: the five column parities and the five θ-effects are computed once. -/
def thetaV (v : VState) : VState :=
  let c : Vector (BitVec 64) 5 := Vector.ofFn fun x =>
    toK v x 0 ^^^ toK v x 1 ^^^ toK v x 2 ^^^ toK v x 3 ^^^ toK v x 4
  let d : Vector (BitVec 64) 5 := Vector.ofFn fun x : Fin 5 =>
    c[(x.val + 4) % 5] ^^^ (c[(x.val + 1) % 5]).rotateLeft 1
  ofK fun x y => toK v x y ^^^ d[x.val]

/-- ρ on the array state. -/
def rhoV (v : VState) : VState :=
  ofK fun x y => (toK v x y).rotateLeft (rotOffset x y)

/-- π on the array state. -/
def piV (v : VState) : VState :=
  ofK fun x y => toK v ⟨(x.val + 3 * y.val) % 5, by omega⟩ x

/-- χ on the array state. -/
def chiV (v : VState) : VState :=
  ofK fun x y =>
    toK v x y ^^^ (~~~toK v ⟨(x.val + 1) % 5, by omega⟩ y &&& toK v ⟨(x.val + 2) % 5, by omega⟩ y)

/-- ι on the array state: the round constant is added to lane `(0, 0)`. -/
def iotaV (v : VState) (rc : BitVec 64) : VState :=
  v.set 0 (v[0] ^^^ rc)

/-- One round on the array state: θ, ρ, π, χ, ι. -/
def roundV (v : VState) (rc : BitVec 64) : VState :=
  iotaV (chiV (piV (rhoV (thetaV v)))) rc

/-- Keccak-f[1600] on the array state: 24 rounds. -/
def keccakFV (v : VState) : VState :=
  Fin.foldl 24 (fun s (r : Fin 24) => roundV s (roundConstant r.val)) v

/-- Keccak-f[1600] on the closure state through the array state. -/
def keccakFK (a : KState) : KState := toK (keccakFV (ofK a))

/-! ## Agreement of the step maps -/

/-- `thetaV` is θ. -/
theorem toK_thetaV (v : VState) : toK (thetaV v) = theta (toK v) := by
  unfold thetaV theta
  simp only [Vector.getElem_ofFn]
  exact toK_ofK _

/-- `rhoV` is ρ. -/
theorem toK_rhoV (v : VState) : toK (rhoV v) = rho (toK v) := by
  unfold rhoV rho
  exact toK_ofK _

/-- `piV` is π. -/
theorem toK_piV (v : VState) : toK (piV v) = pi (toK v) := by
  unfold piV pi
  exact toK_ofK _

/-- `chiV` is χ. -/
theorem toK_chiV (v : VState) : toK (chiV v) = chi (toK v) := by
  unfold chiV chi
  exact toK_ofK _

/-- `iotaV` is ι. -/
theorem toK_iotaV (v : VState) (rc : BitVec 64) : toK (iotaV v rc) = iota (toK v) rc := by
  funext x y
  unfold iotaV iota toK
  grind

/-- `roundV` is a Keccak round. -/
theorem toK_roundV (v : VState) (rc : BitVec 64) :
    toK (roundV v rc) = keccakRound (toK v) rc := by
  unfold roundV keccakRound
  rw [toK_iotaV, toK_chiV, toK_piV, toK_rhoV, toK_thetaV]

/-- A map that commutes with every step commutes with a `Fin.foldl`. -/
theorem fin_foldl_hom {α β : Type} (h : α → β) (n : Nat) (f : α → Fin n → α)
    (g : β → Fin n → β) (hfg : ∀ s i, h (f s i) = g (h s) i) (s : α) :
    h (Fin.foldl n f s) = Fin.foldl n g (h s) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, hfg, ih]
    intro s i
    exact hfg s i.castSucc

/-- `keccakFV` is Keccak-f[1600]. -/
theorem toK_keccakFV (v : VState) : toK (keccakFV v) = keccakF (toK v) := by
  unfold keccakFV keccakF
  exact fin_foldl_hom toK 24 _ _ (fun s r => toK_roundV s _) v

/-- Keccak-f[1600] is computed through the array state. -/
@[csimp] theorem keccakF_eq_keccakFK : @keccakF = @keccakFK := by
  funext a
  rw [keccakFK, toK_keccakFV, toK_ofK]

/-! ## The sponge on the array state -/

/-- The zero array state. -/
def zeroV : VState := Vector.replicate 25 0

/-- `zeroV` is the zero state. -/
theorem toK_zeroV : toK zeroV = KState.zero := by
  funext x y
  simp [toK, zeroV, KState.zero]

/-- The absorbing phase on the array state. -/
def absorbV (rate : Nat) (p : List UInt8) : VState :=
  (blocks rate (p.length / rate) p).foldl
    (fun s block => keccakFV (ofK (SHAKE128.xorIn (toK s) block))) zeroV

/-- `absorbV` is the absorbing phase. -/
theorem toK_absorbV (rate : Nat) (p : List UInt8) : toK (absorbV rate p) = absorb rate p := by
  unfold absorbV absorb
  rw [← toK_zeroV]
  exact (List.foldl_hom toK (fun s block => by rw [toK_keccakFV, toK_ofK])).symm

/-- `n` further output blocks of `rate` bytes on the array state. -/
def squeezeBlocksV (rate : Nat) (s : VState) : Nat → List UInt8
  | 0 => []
  | n + 1 =>
    let t := keccakFV s
    (stateToBytes (toK t)).take rate ++ squeezeBlocksV rate t n

/-- `squeezeBlocksV` is the squeezing phase. -/
theorem squeezeBlocksV_eq (rate : Nat) (s : VState) (n : Nat) :
    squeezeBlocksV rate s n = squeezeBlocks rate (toK s) n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [squeezeBlocksV, squeezeBlocks, ih, toK_keccakFV]

/-- The sponge construction over Keccak-f[1600] on the array state. -/
def spongeV (rate : Nat) (suffix : UInt8) (msg : List UInt8) (outLen : Nat) : List UInt8 :=
  let s := absorbV rate (pad rate suffix msg)
  ((stateToBytes (toK s)).take rate ++ squeezeBlocksV rate s ((outLen - 1) / rate)).take outLen

/-- The sponge is computed on the array state. -/
@[csimp] theorem sponge_eq_spongeV : @sponge = @spongeV := by
  funext rate suffix msg outLen
  simp only [sponge, spongeV, squeezeBlocksV_eq, toK_absorbV]

/-- SHA3-256 on the array state. -/
def sha3_256V (msg : List UInt8) : List UInt8 := spongeV 136 0x06 msg 32

/-- SHA3-512 on the array state. -/
def sha3_512V (msg : List UInt8) : List UInt8 := spongeV 72 0x06 msg 64

/-- SHAKE128 on the array state. -/
def shake128V (msg : List UInt8) (outLen : Nat) : List UInt8 := spongeV 168 0x1F msg outLen

/-- SHAKE256 on the array state. -/
def shake256V (msg : List UInt8) (outLen : Nat) : List UInt8 := spongeV 136 0x1F msg outLen

/-- SHA3-256 is computed on the array state. -/
@[csimp] theorem sha3_256_eq_sha3_256V : @sha3_256 = @sha3_256V := by
  funext msg
  rw [sha3_256, sha3_256V, sponge_eq_spongeV]

/-- SHA3-512 is computed on the array state. -/
@[csimp] theorem sha3_512_eq_sha3_512V : @sha3_512 = @sha3_512V := by
  funext msg
  rw [sha3_512, sha3_512V, sponge_eq_spongeV]

/-- SHAKE128 is computed on the array state. -/
@[csimp] theorem shake128_eq_shake128V : @shake128 = @shake128V := by
  funext msg outLen
  rw [shake128, shake128V, sponge_eq_spongeV]

/-- SHAKE256 is computed on the array state. -/
@[csimp] theorem shake256_eq_shake256V : @shake256 = @shake256V := by
  funext msg outLen
  rw [shake256, shake256V, sponge_eq_spongeV]

/-- The XOF of `Primitives.SHAKE128` is computed on the array state. -/
@[csimp] theorem SHAKE128_shake128_eq_shake128V : @SHAKE128.shake128 = @shake128V := by
  funext msg outLen
  rw [shake128_eq_SHAKE128, shake128_eq_shake128V]

/-! ## Known answers (FIPS 202, SHA3-256 examples) -/

/-- Whether `sha3_256 msg` is `digest`. Compiled after the `@[csimp]` lemmas above, it calls
`sha3_256V`; a `#guard` or `#kat` term evaluated by `evalExpr` keeps calling the closure
permutation. -/
def sha3_256Is (msg digest : List UInt8) : Bool := sha3_256 msg == digest

/-! Keccak-f[1600] of the zero state, lane `(0, 0)` (Keccak team test vectors). -/
#kat (keccakFV zeroV)[0] == 0xF1258F7940E1DDE7

/-! SHA3-256 of the empty message. -/
#kat sha3_256Is []
  [0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6,
    0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8,
    0x43, 0x4a]

/-! SHA3-256 of `"abc"`. -/
#kat sha3_256Is [0x61, 0x62, 0x63]
  [0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17, 0x2d, 0x6b, 0xd3, 0x90,
    0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b, 0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43,
    0x15, 0x32]

end CatCrypt.Crypto.Primitives.KeccakArray
