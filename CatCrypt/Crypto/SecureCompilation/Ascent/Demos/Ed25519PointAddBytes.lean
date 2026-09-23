/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres

/-!
# The shipped `ed25519_point_add` block at the byte level

`Ed25519PointAddShippedProof.paShipped_correct_addr` proves that
`Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock`, run under `runBlockA`,
leaves at `%rdi + 32k` the four coordinates of `paSpec`. This module states that result over
a byte string, and records the position of the block with respect to the covered set of the
`encodeJBlock`/`decodeJStream` round trip.

## The byte-level statement

`outValOf c sa k` is the value of output coordinate `k` after running the block `c` on the
address state `sa`: the four words at `%rdi + 32k`. `paBytes_correct_of_decode` reads a byte
string `bs` that `decodeJStream` takes to `ed25519PointAddShippedBlock` and gives the four
coordinates of `paSpec` in `outValOf` of the decoded block.

## The covered set

`SailX86Decoder.blockCovered` is the set of instruction forms `decodeJ1` inverts, and it is
the hypothesis of `SailX86Decoder.roundtrip_block` and of
`EncodedBlockCorres.encodeJBlock_bytesCorresJ`. Four forms the shipped block contains lie
outside it — `bt`, `setc`, `test` and `adcxMem` (`bt_not_covered`, `setc_not_covered`,
`test_not_covered`, `adcxMem_not_covered`) — and `ScalarEncoder.encodeJInstr` maps `bt` to
the empty byte list (`encodeJInstr_bt`). `paShipped_not_all_covered` states the consequence
for the block: it is not in the covered set, so `encodeJBlock_bytesCorresJ` does not apply to
it and the hypothesis of `paBytes_correct_of_decode` is not discharged from `encodeJBlock`
here.

## Main results

* `outValOf`: the output coordinates of an arbitrary block on the address state.
* `bt_not_covered`, `setc_not_covered`, `test_not_covered`, `adcxMem_not_covered`: the four
  forms of the shipped block outside the covered set.
* `encodeJInstr_bt`: the scalar encoder emits no bytes for `bt`.
* `paShipped_not_all_covered`: the shipped block is not in the covered set.
* `paBytes_correct_of_decode`: a byte string decoding to the shipped block computes the
  coordinates of `paSpec` at `%rdi + 32k`.
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

/-! ## 1. The four forms outside the covered set -/

/-- `bt` has no `decodeJ1` arm, so it is outside the covered set. -/
theorem bt_not_covered (r : String) (s : JOperand) : blockCovered (.bt r s) = false := rfl

/-- `setc` has no `decodeJ1` arm, so it is outside the covered set. -/
theorem setc_not_covered (r : String) : blockCovered (.setc r) = false := rfl

/-- `test` has no `decodeJ1` arm, so it is outside the covered set. -/
theorem test_not_covered (a : String) (b : JOperand) : blockCovered (.test a b) = false := rfl

/-- `adcxMem` has no `decodeJ1` arm, so it is outside the covered set. -/
theorem adcxMem_not_covered (d base : String) (off : Int) :
    blockCovered (.adcxMem d base off) = false := rfl

/-- The scalar encoder emits no bytes for `bt`. -/
theorem encodeJInstr_bt (alloc : GpAlloc) (r : String) (s : JOperand) :
    encodeJInstr alloc (.bt r s) = [] := rfl

/-! ## 2. The shipped block against the covered set -/

/-- Segment 5 of the body is not in the covered set: it contains `bt` and `setc`. -/
theorem paSeg005_not_covered :
    ed25519PointAddShippedSeg005.all blockCovered = false := by decide

/-- The shipped block is not in the covered set, by its fifth segment. -/
theorem paShipped_not_covered :
    ed25519PointAddShippedBlock.all blockCovered = false := by
  simp only [ed25519PointAddShippedBlock, ed25519PointAddShippedPart01, List.all_append,
    paSeg005_not_covered, Bool.and_false, Bool.false_and]

/-- **The shipped block is outside the covered set of the byte round trip.** The hypothesis
    `∀ i ∈ block, blockCovered i = true` of `SailX86BlockRoundtrip.roundtrip_block` and of
    `EncodedBlockCorres.encodeJBlock_bytesCorresJ` fails on
    `ed25519PointAddShippedBlock`, whose fifth segment contains `bt` and `setc`. -/
theorem paShipped_not_all_covered :
    ¬ ∀ i ∈ ed25519PointAddShippedBlock, blockCovered i = true := by
  intro h
  have hall := List.all_eq_true.mpr h
  rw [paShipped_not_covered] at hall
  exact Bool.noConfusion hall

/-! ## 3. The address-machine statement over an arbitrary block -/

/-- The value of output coordinate `k` after running the block `c` on the address state
    `sa`: the four words at `%rdi + 32k`. -/
def outValOf (c : List (JInstr 64)) (sa : AState) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i =>
    read64 (runBlockA sa c).mem (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * (4 * k + i) : Nat) : Int)))

/-- At the shipped block, `outValOf` is `paOutValA`. -/
theorem outValOf_shipped (sa : AState) (k : Nat) :
    outValOf ed25519PointAddShippedBlock sa k = paOutValA sa k := rfl

/-! ## 4. The byte-level result -/

/-- **A byte string that decodes to the shipped block computes the addition.** For `bs`
    that `decodeJStream` reads as `ed25519PointAddShippedBlock.length` instructions forming
    `ed25519PointAddShippedBlock`, when the cells of `paCells` occupy pairwise disjoint
    eight-byte ranges and the eight input coordinates at `%rsi + 32k` are below `p25519`,
    running the decoded block under `runBlockA` leaves at `%rdi + 32k` the four coordinates
    of `paSpec` on those values.

    The decode hypothesis is not discharged here: `paShipped_not_all_covered` places the
    block outside the covered set of `encodeJBlock`/`decodeJStream`. -/
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

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddBytes
