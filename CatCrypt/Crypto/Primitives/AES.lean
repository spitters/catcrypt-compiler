/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.AES128
public meta import CatCrypt.Crypto.Primitives.AES128
public import CatCryptCore.Tactics.KatGuard

/-!
# AES block encryption for every key length (FIPS 197)

AES encrypts a 16-byte block under a key of `Nk` 32-bit words, `Nk ∈ {4, 6, 8}`, in
`Nr = Nk + 6` rounds (FIPS 197, §5, Figure 4). The round functions do not depend on the key
length and are those of `Primitives.AES128`; this module generalises the key expansion
(FIPS 197, §5.2) and the cipher (§5.1) over `Nk`. The key expansion produces the
`4 · (Nr + 1)` words of the round keys; for `Nk > 6` every word whose index is `4` modulo
`Nk` passes through `SubWord`.

## Main definitions

* `keyExpansionVec nk key`, `keyExpansion nk key`: the `16 · (nk + 7)` bytes of the round
  keys, as a vector and as a function.
* `encryptVec nk key block`, `encrypt nk key block`: AES encryption with an `nk`-word key in
  `nk + 6` rounds, as a vector and as a state.
* `aes128`, `aes192`, `aes256`: the instances at `nk = 4, 6, 8`.

## Main results

* `encrypt_four_eq_aes128_encrypt`: at `nk = 4`, `encrypt` is
  `Primitives.AES128.aes128_encrypt`.

Known-answer checks: FIPS 197 Appendix C.1, C.2 and C.3.

## References

* FIPS 197 — Advanced Encryption Standard (AES), §5.1, §5.2 and Appendix C
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.AES

open CatCrypt.Crypto.Primitives.AES128

/-- Extract 4-byte word `j` from an expanded key of `16 · (nk + 7)` bytes. -/
def getWord {nk : Nat} (expanded : Fin (16 * (nk + 7)) → UInt8) (j : Fin (4 * (nk + 7))) :
    Fin 4 → UInt8 := fun i =>
  expanded ⟨4 * j.val + i.val, by have := j.isLt; omega⟩

/-- AES key expansion (FIPS 197, §5.2) for a key of `nk` words: the `4 · (nk + 7)` words of
the `nk + 7` round keys, as `16 · (nk + 7)` bytes. Word `j ≥ nk` is word `j - nk` xor a
temporary word: `SubWord (RotWord w) ⊕ Rcon (j / nk)` when `nk` divides `j`,
`SubWord w` when `nk > 6` and `j ≡ 4 (mod nk)`, and `w` otherwise, with `w` word `j - 1`. -/
def keyExpansionVec (nk : Nat) (key : Fin (4 * nk) → UInt8) : Vector UInt8 (16 * (nk + 7)) :=
  let init : Fin (16 * (nk + 7)) → UInt8 := fun i =>
    if h : i.val < 4 * nk then key ⟨i.val, h⟩ else 0
  Fin.foldl (4 * (nk + 7) - nk) (fun (v : Vector UInt8 (16 * (nk + 7)))
      (wi : Fin (4 * (nk + 7) - nk)) =>
    let j := wi.val + nk
    let prev := getWord v.get ⟨j - 1, by have := wi.isLt; omega⟩
    let prevNk := getWord v.get ⟨j - nk, by have := wi.isLt; omega⟩
    let temp :=
      if j % nk == 0 then
        let rotated := rotWord prev
        let subbed := subWord rotated
        fun (i : Fin 4) =>
          if i.val == 0 then subbed i ^^^ rcon (j / nk - 1) else subbed i
      else if 6 < nk ∧ j % nk = 4 then subWord prev
      else prev
    let newWord : Fin 4 → UInt8 := fun i => prevNk i ^^^ temp i
    Fin.foldl 4 (fun (e : Vector UInt8 (16 * (nk + 7))) (bi : Fin 4) =>
      e.set (4 * j + bi.val) (newWord bi) (by have := wi.isLt; omega)) v)
    (Vector.ofFn init)

/-- The bytes of the key expansion `keyExpansionVec nk key` as a function. -/
def keyExpansion (nk : Nat) (key : Fin (4 * nk) → UInt8) : Fin (16 * (nk + 7)) → UInt8 :=
  (keyExpansionVec nk key).get

/-- Round key `r` (`r ≤ nk + 6`) of an expanded key. -/
def roundKey {nk : Nat} (expanded : Fin (16 * (nk + 7)) → UInt8) (r : Fin (nk + 7)) :
    Key128 := fun i =>
  expanded ⟨16 * r.val + i.val, by have := r.isLt; omega⟩

/-- AES encryption (FIPS 197, §5.1) of a 16-byte block under a key of `nk` words: the initial
`AddRoundKey`, `nk + 5` full rounds and the final round without `MixColumns`. The state
between rounds and the ciphertext are vectors of sixteen bytes. -/
def encryptVec (nk : Nat) (key : Fin (4 * nk) → UInt8) (block : State) : Vector UInt8 16 :=
  let expanded := keyExpansionVec nk key
  let s0 : Vector UInt8 16 :=
    Vector.ofFn (addRoundKey block (roundKey expanded.get ⟨0, by omega⟩))
  let sLast := Fin.foldl (nk + 5) (fun (s : Vector UInt8 16) (r : Fin (nk + 5)) =>
    Vector.ofFn (aesRound s.get (roundKey expanded.get ⟨r.val + 1, by omega⟩))) s0
  Vector.ofFn (aesFinalRound sLast.get (roundKey expanded.get ⟨nk + 6, by omega⟩))

/-- AES encryption with an `nk`-word key, as a function on states: the bytes of
`encryptVec nk key block`. -/
def encrypt (nk : Nat) (key : Fin (4 * nk) → UInt8) (block : State) : State :=
  (encryptVec nk key block).get

/-- AES-128: a 16-byte key, 10 rounds. -/
def aes128 : (Fin (4 * 4) → UInt8) → State → State := encrypt 4

/-- AES-192: a 24-byte key, 12 rounds. -/
def aes192 : (Fin (4 * 6) → UInt8) → State → State := encrypt 6

/-- AES-256: a 32-byte key, 14 rounds. -/
def aes256 : (Fin (4 * 8) → UInt8) → State → State := encrypt 8

/-- A map that commutes with each step of two folds commutes with the folds. -/
private theorem foldl_hom {α β : Type} (n : Nat) (h : α → β) (g : α → Fin n → α)
    (f : β → Fin n → β) (hgf : ∀ x i, h (g x i) = f (h x) i) (x : α) :
    h (Fin.foldl n g x) = Fin.foldl n f (h x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => grind [Fin.foldl_succ]

/-- Reading a vector after `set` is `Function.update` of reading it before. -/
private theorem vector_get_set {n : Nat} (v : Vector UInt8 n) (i : Nat) (x : UInt8)
    (hi : i < n) : (v.set i x hi).get = Function.update v.get ⟨i, hi⟩ x := by
  funext j
  grind [Vector.get, Function.update]

/-- Reading the vector of the values of `f` is `f`. -/
private theorem vector_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) :
    (Vector.ofFn f).get = f := by
  funext i
  simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  rfl

/-- At `nk = 4`, the key expansion is the AES-128 key expansion of `Primitives.AES128`. -/
theorem keyExpansion_four (key : Key128) : keyExpansion 4 key = AES128.keyExpansion key := by
  unfold keyExpansion keyExpansionVec AES128.keyExpansion
  dsimp only
  rw [foldl_hom _ Vector.get _ _ ?step, vector_get_ofFn]
  · intro v wi
    refine (foldl_hom _ Vector.get _ ?f ?hom v).trans ?eq
    case eq => rfl
    case hom =>
      intro e bi
      rw [vector_get_set]
      congr 1
      unfold getWord AES128.getWord
      rfl

/-- At `nk = 4`, AES encryption is `Primitives.AES128.aes128_encrypt`. -/
theorem encrypt_four_eq_aes128_encrypt (key : Key128) (block : State) :
    encrypt 4 key block = aes128_encrypt key block := by
  unfold encrypt encryptVec aes128_encrypt roundKey AES128.roundKey
  dsimp only
  rw [vector_get_ofFn, show (keyExpansionVec 4 key).get = AES128.keyExpansion key from
    keyExpansion_four key]
  congr 1
  refine (foldl_hom _ Vector.get _ ?f ?hom _).trans ?eq
  case eq => rw [vector_get_ofFn]
  case hom => exact fun s r => vector_get_ofFn _

/-! ## Known-answer checks: FIPS 197, Appendix C -/

/-- The bytes of a list as a function on `Fin n`, with `0` past the end of the list. -/
def ofList (n : Nat) (bytes : List UInt8) : Fin n → UInt8 := fun i => bytes.getD i.val 0

/-- The FIPS 197 Appendix C plaintext `00 11 22 … ff`. -/
def katPlaintext : State :=
  ofList 16 [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
    0xee, 0xff]

/-- The FIPS 197 Appendix C key of `4 · nk` bytes `00 01 02 …`. -/
def katKey (nk : Nat) : Fin (4 * nk) → UInt8 := fun i => i.val.toUInt8

/-! FIPS 197 C.1, AES-128. -/
set_option linter.hashCommand false in
set_option kat.ms 3000 in
#kat (encryptVec 4 (katKey 4) katPlaintext).toList ==
  [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5,
    0x5a]

/-! FIPS 197 C.2, AES-192. -/
set_option linter.hashCommand false in
#kat (encryptVec 6 (katKey 6) katPlaintext).toList ==
  [0xdd, 0xa9, 0x7c, 0xa4, 0x86, 0x4c, 0xdf, 0xe0, 0x6e, 0xaf, 0x70, 0xa0, 0xec, 0x0d, 0x71,
    0x91]

/-! FIPS 197 C.3, AES-256. -/
set_option linter.hashCommand false in
#kat (encryptVec 8 (katKey 8) katPlaintext).toList ==
  [0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60,
    0x89]

end CatCrypt.Crypto.Primitives.AES
