/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddDecode

/-!
# The shipped `ed25519_point_add` block at the byte level

`Ed25519PointAddShippedProof.paShipped_correct_addr` proves that
`Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock`, run under `runBlockA`,
leaves at `%rdi + 32k` the four coordinates of `paSpec`. This module states that result over
bytes.

`outValOf c sa k` is the value of output coordinate `k` after running the block `c` on the
address state `sa`: the four words at `%rdi + 32k`. `paBytes_correct_of_decode` reads a byte
string `bs` that `decodeJStream` takes to `ed25519PointAddShippedBlock` and gives the four
coordinates of `paSpec` in `outValOf` of the decoded block. `paShippedBytes_correct`
instantiates it at `encodeJBlock s2nAlloc ed25519PointAddShippedBlock`, whose decode is
`Ed25519PointAddDecode.paShipped_decode`.

## Main results

* `outValOf`: the output coordinates of an arbitrary block on the address state.
* `paBytes_correct_of_decode`: a byte string decoding to the shipped block computes the
  coordinates of `paSpec` at `%rdi + 32k`.
* `paShippedBytes_correct`: the bytes `encodeJBlock s2nAlloc ed25519PointAddShippedBlock`
  decode to a block that computes them.
-/

@[expose] public section

set_option autoImplicit false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddBytes

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddDecode
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc)

/-! ## 1. The address-machine statement over an arbitrary block -/

/-- The value of output coordinate `k` after running the block `c` on the address state
    `sa`: the four words at `%rdi + 32k`. -/
def outValOf (c : List (JInstr 64)) (sa : AState) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i =>
    read64 (runBlockA sa c).mem (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * (4 * k + i) : Nat) : Int)))

/-- At the shipped block, `outValOf` is `paOutValA`. -/
theorem outValOf_shipped (sa : AState) (k : Nat) :
    outValOf ed25519PointAddShippedBlock sa k = paOutValA sa k := rfl

/-! ## 2. The byte-level result -/

/-- **A byte string that decodes to the shipped block computes the addition.** For `bs`
    that `decodeJStream` reads as `ed25519PointAddShippedBlock.length` instructions forming
    `ed25519PointAddShippedBlock`, when the cells of `paCells` occupy pairwise disjoint
    eight-byte ranges and the eight input coordinates at `%rsi + 32k` are below `p25519`,
    running the decoded block under `runBlockA` leaves at `%rdi + 32k` the four coordinates
    of `paSpec` on those values. -/
theorem paBytes_correct_of_decode (bs : List (BitVec 8))
    (hdec : decodeJStream ed25519PointAddShippedBlock.length bs
      = some ed25519PointAddShippedBlock)
    (sa : AState) (hsep : Separated shippedBank sa.regs paCells)
    (b0 : paInValA sa 0 < 2 ^ 255 - 19) (b1 : paInValA sa 1 < 2 ^ 255 - 19)
    (b2 : paInValA sa 2 < 2 ^ 255 - 19) (b3 : paInValA sa 3 < 2 ^ 255 - 19)
    (b4 : paInValA sa 4 < 2 ^ 255 - 19) (b5 : paInValA sa 5 < 2 ^ 255 - 19)
    (b6 : paInValA sa 6 < 2 ^ 255 - 19) (b7 : paInValA sa 7 < 2 ^ 255 - 19) :
    ∃ c, decodeJStream ed25519PointAddShippedBlock.length bs = some c ∧
      outValOf c sa 0 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).1
        ∧ outValOf c sa 1 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).2.1
        ∧ outValOf c sa 2 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).2.2.1
        ∧ outValOf c sa 3 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).2.2.2 :=
  ⟨ed25519PointAddShippedBlock, hdec,
    paShipped_correct_addr sa hsep b0 b1 b2 b3 b4 b5 b6 b7⟩

/-- **The shipped block's encoding computes the addition.** The bytes
    `encodeJBlock s2nAlloc ed25519PointAddShippedBlock` decode to a block which, when the cells
    of `paCells` occupy pairwise disjoint eight-byte ranges and the eight input coordinates at
    `%rsi + 32k` are below `p25519`, leaves at `%rdi + 32k` the four coordinates of `paSpec`
    on those values. -/
theorem paShippedBytes_correct (sa : AState) (hsep : Separated shippedBank sa.regs paCells)
    (b0 : paInValA sa 0 < 2 ^ 255 - 19) (b1 : paInValA sa 1 < 2 ^ 255 - 19)
    (b2 : paInValA sa 2 < 2 ^ 255 - 19) (b3 : paInValA sa 3 < 2 ^ 255 - 19)
    (b4 : paInValA sa 4 < 2 ^ 255 - 19) (b5 : paInValA sa 5 < 2 ^ 255 - 19)
    (b6 : paInValA sa 6 < 2 ^ 255 - 19) (b7 : paInValA sa 7 < 2 ^ 255 - 19) :
    ∃ c, decodeJStream ed25519PointAddShippedBlock.length
        (encodeJBlock s2nAlloc ed25519PointAddShippedBlock) = some c ∧
      outValOf c sa 0 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).1
        ∧ outValOf c sa 1 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).2.1
        ∧ outValOf c sa 2 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).2.2.1
        ∧ outValOf c sa 3 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
          (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
          (paInValA sa 7)).2.2.2 := by
  refine paBytes_correct_of_decode _ ?_ sa hsep b0 b1 b2 b3 b4 b5 b6 b7
  rw [ed25519PointAddShippedBlock_length]
  exact paShipped_decode

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddBytes
