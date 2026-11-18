/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.Keccak
public import CatCrypt.Crypto.Primitives.SHAKE128

/-!
# The Keccak sponge on byte strings (FIPS 202)

`sponge rate suffix msg outLen` is the sponge construction `SPONGE[f, pad, r]` of FIPS 202
§4 over `f = Keccak-f[1600]` (`Primitives.Keccak.keccakF`), with a rate of `rate` bytes and
the padding rule pad10*1 of §5.1 preceded by the domain-separation suffix of §6.1-6.2, all
in the byte form of FIPS 202 Appendix B.2: the first padding byte is `suffix` (`0x06` for
SHA-3, `0x1F` for SHAKE), the last padding byte has its bit `0x80` set, and the two coincide
when one byte of padding is needed.

The absorbing phase is a left fold of `keccakF ∘ xorIn` over the blocks of the padded message
(`blocks`, structural in the number of blocks); the squeezing phase (`squeezeBlocks`) is
structural in the number of permutations after the first output block.

## Main definitions

* `padBytes`, `pad`: the byte form of the domain suffix followed by pad10*1 (§5.1, B.2).
* `blocks`, `absorb`, `squeezeBlocks`, `sponge`: the sponge construction (§4).
* `sha3_256`, `sha3_512` (§6.1), `shake128`, `shake256` (§6.2): applications of `sponge`.

## Main results

* `pad_length`: the padded message has a length divisible by the rate.
* `shake128_eq_SHAKE128`: the XOF of `Primitives.SHAKE128` agrees with `shake128` on every
  message whose length is not one less than a multiple of the rate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.KeccakSponge

open CatCrypt.Crypto.Primitives.Keccak

/-! ## Padding (FIPS 202 §5.1, §6.1-6.2, Appendix B.2) -/

/-- The `q` padding bytes appended to a message, for `1 ≤ q`: the domain suffix byte with
the first bit of pad10*1, zero bytes, and the byte `0x80` carrying the last bit of pad10*1;
for `q = 1` the single byte `suffix ||| 0x80`. -/
def padBytes (suffix : UInt8) (q : Nat) : List UInt8 :=
  if q = 1 then [suffix ||| 0x80]
  else suffix :: List.replicate (q - 2) 0 ++ [0x80]

/-- The padded message `msg ‖ suffix ‖ pad10*1` at a rate of `rate` bytes: between 1 and
`rate` bytes are appended, so that the length is a multiple of the rate. -/
def pad (rate : Nat) (suffix : UInt8) (msg : List UInt8) : List UInt8 :=
  msg ++ padBytes suffix (rate - msg.length % rate)

/-! ## Absorbing (FIPS 202 §4, Algorithm 8, step 6) -/

/-- The first `n` blocks of `rate` bytes of `l`. -/
def blocks (rate : Nat) : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | n + 1, l => l.take rate :: blocks rate n (l.drop rate)

/-- The state after absorbing the padded message `p`: `keccakF (S ⊕ Pᵢ ‖ 0^c)` for each block
`Pᵢ` of `rate` bytes, from the zero state. -/
def absorb (rate : Nat) (p : List UInt8) : KState :=
  (blocks rate (p.length / rate) p).foldl
    (fun s block => keccakF (SHAKE128.xorIn s block)) KState.zero

/-! ## Squeezing (FIPS 202 §4, Algorithm 8, steps 7-10) -/

/-- `n` further output blocks of `rate` bytes: each permutes the state and reads its first
`rate` bytes. -/
def squeezeBlocks (rate : Nat) (s : KState) : Nat → List UInt8
  | 0 => []
  | n + 1 =>
    let t := keccakF s
    (stateToBytes t).take rate ++ squeezeBlocks rate t n

/-- The sponge construction over Keccak-f[1600]: absorb `pad rate suffix msg`, then output
the first `outLen` bytes of the squeezed stream (`(outLen - 1) / rate` permutations after the
absorbing phase). -/
def sponge (rate : Nat) (suffix : UInt8) (msg : List UInt8) (outLen : Nat) : List UInt8 :=
  let s := absorb rate (pad rate suffix msg)
  ((stateToBytes s).take rate ++ squeezeBlocks rate s ((outLen - 1) / rate)).take outLen

/-! ## SHA-3 and SHAKE (FIPS 202 §6) -/

/-- SHA3-256 (FIPS 202 §6.1): rate 136 bytes, suffix `01`, 32 output bytes. -/
def sha3_256 (msg : List UInt8) : List UInt8 := sponge 136 0x06 msg 32

/-- SHA3-512 (FIPS 202 §6.1): rate 72 bytes, suffix `01`, 64 output bytes. -/
def sha3_512 (msg : List UInt8) : List UInt8 := sponge 72 0x06 msg 64

/-- SHAKE128 (FIPS 202 §6.2): rate 168 bytes, suffix `1111`, `outLen` output bytes. -/
def shake128 (msg : List UInt8) (outLen : Nat) : List UInt8 := sponge 168 0x1F msg outLen

/-- SHAKE256 (FIPS 202 §6.2): rate 136 bytes, suffix `1111`, `outLen` output bytes. -/
def shake256 (msg : List UInt8) (outLen : Nat) : List UInt8 := sponge 136 0x1F msg outLen

/-! ## Padding length -/

/-- `padBytes suffix q` has `q` bytes. -/
theorem padBytes_length (suffix : UInt8) (q : Nat) (hq : 1 ≤ q) :
    (padBytes suffix q).length = q := by
  unfold padBytes
  split <;> simp <;> omega

/-- The padded message has a length divisible by the rate. -/
theorem pad_length (rate : Nat) (suffix : UInt8) (msg : List UInt8) (hr : 0 < rate) :
    (pad rate suffix msg).length = (msg.length / rate + 1) * rate := by
  have h1 : msg.length % rate < rate := Nat.mod_lt _ hr
  have h2 := Nat.div_add_mod msg.length rate
  have h3 : 1 ≤ rate - msg.length % rate := by omega
  rw [pad, List.length_append, padBytes_length suffix _ h3, Nat.add_mul, Nat.one_mul,
    Nat.mul_comm]
  omega

/-! ## Agreement with `Primitives.SHAKE128` -/

/-- `Keccak.stateToBytes` has 200 bytes. -/
theorem stateToBytes_length (s : KState) : (stateToBytes s).length = 200 := by
  unfold stateToBytes
  simp [Function.comp_def]
  rfl

/-- `SHAKE128.chunkByRate` of the empty message has no blocks. -/
theorem chunkByRate_nil : SHAKE128.chunkByRate [] = [] := by
  rw [SHAKE128.chunkByRate]

/-- `SHAKE128.chunkByRate` of a nonempty message: its first 168 bytes, then the blocks of the
rest. -/
theorem chunkByRate_cons (a : UInt8) (t : List UInt8) :
    SHAKE128.chunkByRate (a :: t) =
      (a :: t).take 168 :: SHAKE128.chunkByRate ((a :: t).drop 168) := by
  rw [SHAKE128.chunkByRate]
  rfl


/-- `SHAKE128.padMessage` on a message shorter than one block of 168 bytes, other than one
of 167 bytes. -/
theorem padMessage_of_lt (msg : List UInt8) (h1 : msg.length < 168) (h2 : msg.length ≠ 167) :
    SHAKE128.padMessage msg = [msg ++ padBytes 0x1F (168 - msg.length)] := by
  cases msg with
  | nil => rw [SHAKE128.padMessage, chunkByRate_nil]; rfl
  | cons a t =>
    have hl : (a :: t).length ≤ 168 := by omega
    rw [SHAKE128.padMessage, chunkByRate_cons,
      List.take_of_length_le (by simpa [SHAKE128.rate] using hl),
      List.drop_eq_nil_of_le (by simpa [SHAKE128.rate] using hl), chunkByRate_nil]
    have hq : 168 - (a :: t).length ≠ 1 := by omega
    simp only [List.getLast?_singleton, List.dropLast_singleton, List.nil_append, padBytes, hq,
      ↓reduceIte, SHAKE128.rate, h1]
    simp

/-- `SHAKE128.padMessage` on a message of at least one block of 168 bytes. -/
theorem padMessage_of_le (msg : List UInt8) (h : 168 ≤ msg.length) :
    SHAKE128.padMessage msg = msg.take 168 :: SHAKE128.padMessage (msg.drop 168) := by
  obtain ⟨a, t, rfl⟩ : ∃ a t, msg = a :: t := by
    cases msg with
    | nil => simp at h
    | cons a t => exact ⟨a, t, rfl⟩
  have hx : ((a :: t).take 168).length = 168 := by simp at h ⊢; omega
  rw [SHAKE128.padMessage, chunkByRate_cons]
  conv => rhs; rw [SHAKE128.padMessage]
  generalize SHAKE128.chunkByRate ((a :: t).drop 168) = rest
  generalize (a :: t).take 168 = x at hx ⊢
  cases rest with
  | nil =>
    simp only [List.getLast?_singleton, List.getLast?_nil, hx,
      show ¬ (168 < SHAKE128.rate) from by decide, ↓reduceIte]
    rfl
  | cons y ys =>
    rw [List.getLast?_cons_cons, List.dropLast_cons_cons]
    cases hl : (y :: ys).getLast? with
    | none => simp at hl
    | some lb => simp only; split <;> simp

/-- The blocks of `SHAKE128.padMessage` are the blocks of `pad 168 0x1F` on every message whose
length is not one less than a multiple of 168. -/
theorem padMessage_eq_blocks (msg : List UInt8) (h : msg.length % 168 ≠ 167) :
    SHAKE128.padMessage msg = blocks 168 (msg.length / 168 + 1) (pad 168 0x1F msg) := by
  obtain ⟨n, hn⟩ : ∃ n, msg.length = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing msg with
  | _ n ih =>
  by_cases hlt : msg.length < 168
  · rw [padMessage_of_lt msg hlt (by omega)]
    have hp : (pad 168 0x1F msg).length = 168 := by
      rw [pad_length 168 0x1F msg (by decide)]; omega
    have hd : msg.length / 168 = 0 := by omega
    rw [hd, blocks, blocks, List.take_of_length_le (by omega)]
    simp [pad, Nat.mod_eq_of_lt hlt]
  · have hle : 168 ≤ msg.length := by omega
    have hm : (msg.drop 168).length % 168 ≠ 167 := by simp; omega
    rw [padMessage_of_le msg hle, ih _ (by simp; omega) _ hm rfl]
    have hk : msg.length / 168 + 1 = ((msg.drop 168).length / 168 + 1) + 1 := by
      simp; omega
    have hmod : (msg.drop 168).length % 168 = msg.length % 168 := by simp; omega
    rw [hk, pad, pad, hmod]
    conv => rhs; rw [blocks]
    rw [List.take_append_of_le_length hle, List.drop_append_of_le_length hle]

/-- The absorbing phase of `Primitives.SHAKE128` is `absorb 168` of `pad 168 0x1F` on every
message whose length is not one less than a multiple of 168. -/
theorem absorb_eq_SHAKE128 (msg : List UInt8) (h : msg.length % 168 ≠ 167) :
    SHAKE128.absorb msg = absorb 168 (pad 168 0x1F msg) := by
  rw [SHAKE128.absorb, absorb, pad_length 168 0x1F msg (by decide),
    Nat.mul_div_cancel _ (by decide), padMessage_eq_blocks msg h]

/-- The squeezing loop of `Primitives.SHAKE128` appends the first `n` bytes of the stream that
`sponge` squeezes at rate 168. -/
theorem squeeze_go_eq (s : KState) (n : Nat) (acc : List UInt8) :
    SHAKE128.squeeze.go s n acc =
      acc ++ ((stateToBytes s).take 168 ++ squeezeBlocks 168 s ((n - 1) / 168)).take n := by
  induction n using Nat.strongRecOn generalizing s acc with
  | _ n ih =>
  have hB : ((stateToBytes s).take 168).length = 168 := by simp [stateToBytes_length]
  rw [SHAKE128.squeeze.go]
  by_cases h0 : n = 0
  · subst h0
    simp
  · simp only [SHAKE128.squeezeBlock, SHAKE128.rate, beq_iff_eq, h0, ↓reduceIte]
    by_cases hle : n ≤ 168
    · simp only [hle, ↓reduceIte, List.take_take, Nat.min_eq_left hle]
      rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left hle]
    · simp only [hle, ↓reduceIte, List.take_take, Nat.min_self]
      rw [ih (n - 168) (by omega)]
      have hk : (n - 1) / 168 = ((n - 168) - 1) / 168 + 1 := by omega
      rw [hk, squeezeBlocks, List.take_append (l₁ := List.take 168 (stateToBytes s)), hB,
        List.take_take, Nat.min_eq_right (by omega : 168 ≤ n), List.append_assoc]

/-- The XOF of `Primitives.SHAKE128` agrees with `shake128` on every message whose length is
not one less than a multiple of the rate 168. -/
theorem shake128_eq_SHAKE128 (msg : List UInt8) (outLen : Nat)
    (h : msg.length % 168 ≠ 167) :
    SHAKE128.shake128 msg outLen = shake128 msg outLen := by
  rw [SHAKE128.shake128, SHAKE128.squeeze, squeeze_go_eq, absorb_eq_SHAKE128 msg h]
  simp [shake128, sponge]

end CatCrypt.Crypto.Primitives.KeccakSponge
