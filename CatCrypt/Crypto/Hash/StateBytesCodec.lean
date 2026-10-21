/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.Keccak
public import CatCrypt.Crypto.Primitives.SHA256
public import Mathlib.Tactic.NormNum
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

/-!
# Byte codecs of the Keccak and SHA-256 states

The 1600-bit Keccak state as 200 little-endian bytes and the eight-word SHA-256 state as 32
little-endian bytes, with the round trips `decode ∘ encode = id`.

## Main results

* `decodeKbytes_encodeKbytes`: decoding the 200 bytes of a Keccak state returns the state.
* `decodeSbytes_encodeSbytes`: decoding the 32 bytes of a SHA-256 state returns the state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.StateBytesCodec

open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Primitives.SHA256

/-! ## Keccak: a 200-byte little-endian codec -/

/-- Encode a 1600-bit state as 200 little-endian bytes. -/
def encodeKbytes (s : KeccakState) : Fin 200 → BitVec 8 :=
  fun i => BitVec.setWidth 8 (s >>> (8 * i.val))

/-- Decode 200 bytes into a 1600-bit state via an OR-fold of shifted bytes. -/
def decodeKbytes (a : Fin 200 → BitVec 8) : KeccakState :=
  (List.finRange 200).foldl
    (fun acc i => acc ||| (BitVec.setWidth 1600 (a i) <<< (8 * i.val))) 0

/-- getLsbD of an OR-fold distributes: the bit is set iff the init has it or some
    folded contribution has it. -/
theorem getLsbD_foldl_or {w : ℕ} {α : Type*} (f : α → BitVec w) (k : ℕ) :
    ∀ (l : List α) (init : BitVec w),
      (l.foldl (fun acc i => acc ||| f i) init).getLsbD k
        = (init.getLsbD k || (l.map (fun i => (f i).getLsbD k)).foldr (· || ·) false) := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons x xs ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.foldr_cons]
      rw [ih (init ||| f x)]
      simp only [BitVec.getLsbD_or]
      rw [Bool.or_assoc]

/-- A foldr-OR of (predicate AND constant) factors the constant out. -/
theorem foldr_or_and_const {α : Type*} (P : α → Bool) (b : Bool) (l : List α) :
    (l.map (fun i => P i && b)).foldr (· || ·) false
      = ((l.map P).foldr (· || ·) false && b) := by
  induction l with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      rw [List.map_cons, List.map_cons, List.foldr_cons, List.foldr_cons]
      cases b <;> cases hpx : P x <;> simp_all

/-- A foldr-OR is `true` whenever some element of the list is `true`. -/
theorem foldr_or_true_of_mem {l : List Bool} (h : true ∈ l) :
    l.foldr (· || ·) false = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with hx | hx
      · subst hx; simp
      · rw [ih hx]; simp

/-- The byte-selector predicate is satisfied by some byte index in `finRange 200`
    for every bit position `< 1600`. -/
theorem byteSelector_finRange (k : ℕ) (hk : k < 1600) :
    ((List.finRange 200).map
        (fun i : Fin 200 => decide (k < 1600) && !decide (k < 8 * i.val)
          && (decide (k - 8 * i.val < 1600) && decide (k - 8 * i.val < 8)))).foldr
      (· || ·) false = true := by
  apply foldr_or_true_of_mem
  rw [List.mem_map]
  refine ⟨⟨k / 8, by omega⟩, List.mem_finRange _, ?_⟩
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not]
  simp only [Bool.not_true, decide_eq_false_iff_not]
  omega

theorem decodeKbytes_encodeKbytes (s : KeccakState) :
    decodeKbytes (encodeKbytes s) = s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  unfold decodeKbytes encodeKbytes
  rw [getLsbD_foldl_or]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  -- Pointwise: each contribution = (byte-selector i) && s.getLsbD k.
  have hpt : ∀ i : Fin 200,
      (decide (k < 1600) && !decide (k < 8 * i.val) &&
        (decide (k - 8 * i.val < 1600) && (decide (k - 8 * i.val < 8) &&
          BitVec.getLsbD s (8 * i.val + (k - 8 * i.val)))))
        = ((decide (k < 1600) && !decide (k < 8 * i.val) &&
            (decide (k - 8 * i.val < 1600) && decide (k - 8 * i.val < 8))) && BitVec.getLsbD s k) := by
    intro i
    by_cases hki : k < 8 * i.val
    · simp [hki]
    · by_cases hk8 : k - 8 * i.val < 8
      · have : 8 * i.val + (k - 8 * i.val) = k := by omega
        rw [this]; cases BitVec.getLsbD s k <;> simp_all
      · simp [hk8]
  rw [List.map_congr_left (fun i _ => hpt i), foldr_or_and_const]
  rw [byteSelector_finRange k hk, Bool.true_and]
  simp [BitVec.getLsbD_zero]

/-! ## SHA-256: a 32-byte little-endian codec -/

/-- Encode a SHA-256 state (8 words) as 32 little-endian bytes: byte `b` is byte
    `b % 4` of word `b / 4`. -/
def encodeSbytes (s : State256) : Fin 32 → BitVec 8 :=
  fun b => BitVec.setWidth 8 ((s ⟨b.val / 4, by have := b.isLt; omega⟩).toBitVec >>> (8 * (b.val % 4)))

/-- Reassemble one 32-bit word from its 4 little-endian bytes. -/
def wordOfBytes (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  BitVec.setWidth 32 b0 ||| (BitVec.setWidth 32 b1 <<< 8)
    ||| (BitVec.setWidth 32 b2 <<< 16) ||| (BitVec.setWidth 32 b3 <<< 24)

/-- Decode 32 bytes back into a SHA-256 state, four bytes per word, little-endian. -/
def decodeSbytes (a : Fin 32 → BitVec 8) : State256 :=
  fun i => UInt32.ofBitVec
    (wordOfBytes (a ⟨4 * i.val, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 1, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 2, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 3, by have := i.isLt; omega⟩))

/-- The per-word round-trip: reassembling the four little-endian bytes of a 32-bit
    word returns the word. A 32-bit `bv_decide` fact. -/
theorem wordOfBytes_split (w : BitVec 32) :
    wordOfBytes (BitVec.setWidth 8 w) (BitVec.setWidth 8 (w >>> 8))
      (BitVec.setWidth 8 (w >>> 16)) (BitVec.setWidth 8 (w >>> 24)) = w := by
  unfold wordOfBytes
  bv_decide

theorem decodeSbytes_encodeSbytes (s : State256) :
    decodeSbytes (encodeSbytes s) = s := by
  funext i
  unfold decodeSbytes encodeSbytes
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

end CatCrypt.Crypto.Hash.StateBytesCodec
