/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Primitives.Keccak

/-!
# SHAKE-128 Extendable-Output Function (FIPS 202)

Constructive implementation of SHAKE-128 using the Keccak-f[1600]
permutation. SHAKE-128 is a sponge-based XOF with:
- Rate `r = 1344` bits (168 bytes)
- Capacity `c = 256` bits (32 bytes)
- Domain separation suffix `0x1F` (FIPS 202, Section 6.2)

All definitions are sealed with `@[irreducible]`.

## References

* FIPS 202, Section 6.2 — SHAKE128
* Bertoni, Daemen, Peeters, Van Assche — *Keccak Specifications Summary*
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.SHAKE128

open CatCrypt.Crypto.Primitives.Keccak

/-! ## Sponge Parameters -/

/-- SHAKE-128 rate in bytes: 168 = (1600 - 256) / 8. -/
def rate : Nat := 168

/-! ## Absorb Phase -/

/-- XOR a message block (up to `rate` bytes) into the Keccak state. -/
def xorIn (s : KState) (block : List UInt8) : KState := fun x y =>
  let laneIdx := 5 * y.val + x.val
  let byteOff := 8 * laneIdx
  -- XOR in the bytes that fall within this lane
  Fin.foldl 8 (init := s x y) fun acc (i : Fin 8) =>
    let globalIdx := byteOff + i.val
    if globalIdx < block.length then
      acc ^^^ (BitVec.ofNat 64 (block.getD globalIdx 0).toNat <<< (8 * i.val))
    else acc

/-- Split message into rate-sized chunks. -/
def chunkByRate (msg : List UInt8) : List (List UInt8) :=
  match _h : msg with
  | [] => []
  | _ :: _ =>
    let chunk := msg.take rate
    let rest := msg.drop rate
    chunk :: chunkByRate rest
termination_by msg.length
decreasing_by simp_wf; simp [_h, rate]; omega

/-- Pad a message for SHAKE-128 (FIPS 202, Section 6.2).
    Appends domain separation `0x1F`, then `0x00` padding,
    then sets the last byte's high bit `0x80`. -/
def padMessage (msg : List UInt8) : List (List UInt8) :=
  let blocks := chunkByRate msg
  match blocks.getLast? with
  | none =>
    -- Empty message: single padded block
    [[0x1F] ++ List.replicate (rate - 2) 0x00 ++ [0x80]]
  | some lastBlock =>
    if lastBlock.length < rate then
      -- Last block has room: append padding
      let padLen := rate - lastBlock.length
      let padded := lastBlock ++ [0x1F] ++ List.replicate (padLen - 2) 0x00 ++ [0x80]
      blocks.dropLast ++ [padded]
    else
      -- Last block is full: add a new padding block
      blocks ++ [[0x1F] ++ List.replicate (rate - 2) 0x00 ++ [0x80]]

/-- Absorb phase: XOR each padded block into the state and permute. -/
def absorb (msg : List UInt8) : KState :=
  let blocks := padMessage msg
  blocks.foldl (fun s block => keccakF (xorIn s block)) KState.zero

/-! ## Squeeze Phase -/

/-- Extract `rate` bytes from the current state. -/
def squeezeBlock (s : KState) : List UInt8 :=
  (stateToBytes s).take rate

/-- Squeeze phase: extract `outLen` bytes from the sponge state. -/
def squeeze (s : KState) (outLen : Nat) : List UInt8 :=
  go s outLen []
where
  go (s : KState) (remaining : Nat) (acc : List UInt8) : List UInt8 :=
    if remaining == 0 then acc
    else
      let block := squeezeBlock s
      if remaining ≤ rate then
        acc ++ block.take remaining
      else
        let acc' := acc ++ block.take rate
        go (keccakF s) (remaining - rate) acc'
  termination_by remaining
  decreasing_by simp_wf; simp [rate] at *; omega

/-! ## SHAKE-128 XOF -/

/-- SHAKE-128 extendable-output function.

    `shake128 msg outLen` absorbs `msg` and squeezes `outLen` bytes. -/
def shake128 (msg : List UInt8) (outLen : Nat) : List UInt8 :=
  squeeze (absorb msg) outLen

/-! ## Convenience Wrappers -/

/-- SHAKE-128 with fixed 32-byte output (used by SLH-DSA for n=16 seeds). -/
def shake128_32 (input : List UInt8) : List UInt8 :=
  shake128 input 32

/-- SHAKE-128 with fixed 16-byte output (used by SLH-DSA hash chains). -/
def shake128_16 (input : List UInt8) : List UInt8 :=
  shake128 input 16

/-! ## Seal all definitions -/

attribute [irreducible] shake128 shake128_32 shake128_16
attribute [irreducible] absorb squeeze xorIn padMessage squeezeBlock

end CatCrypt.Crypto.Primitives.SHAKE128
