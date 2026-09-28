/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Addr
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Bytes

/-!
# A certificate for third-party machine code: s2n-bignum's `bignum_montmul_p384`

`s2nMontmulP384Block` is the instruction list imported from s2n-bignum's hand-written x86-64
Montgomery multiplication modulo `p384` (`Ascent/Demos/S2nMontmulP384.lean` records the
source file, its commit and its SHA-256). No part of this package produced the code. The
ascent proves, once for all machine states, what the code computes; this module states the
certificate in the form a caller of the kernel uses.

The certificate has two parts, both proved elsewhere.

* Over address memory: `s2nMontmulP384_correct_addr` states that `runBlockA` on the block
  stores at `pz` the Montgomery product of the six words at `px` and `py`, for any overlap of
  the three buffers, under s2n-bignum's precondition `x · y ≤ 2^384 · p384`.
* Over bytes: `s2nMontmulP384_decode` states that this package's encoding of the block
  decodes back to the block, and `s2nMontmulP384Bytes_correct` that the decoded
  instructions compute the Montgomery product under the base-register-keyed machine
  `runBlock`.

`s2nMontmulP384_correct_reduced` replaces the product precondition by the condition a
caller holds, that both inputs are reduced below `p384`.

## Main results

* `p384_le_two_pow`: `p384 ≤ 2^384`.
* `s2nMontmulP384_correct_reduced`: for inputs below `p384` at `%rsi` and `%rdx`, the block
  run on the address machine stores at `%rdi` a value below `p384` equal to
  `x · y · (2^384)⁻¹` in `ZMod p384`.
* `s2nMontmulP384_bytes_decode`: the encoded bytes decode to the imported block.
-/

@[expose] public section

set_option autoImplicit false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CertifyThirdPartyDemo

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Addr

/-- The P-384 prime is at most `2^384`. -/
theorem p384_le_two_pow : p384 ≤ 2 ^ 384 := by
  unfold p384
  omega

/-- **The imported s2n-bignum kernel on reduced inputs.** For every address state whose
entry registers `%rsi`, `%rdx`, `%rdi` hold `px`, `py`, `pz`, and whose six words at `px`
and at `py` are below `p384`, the block run by `runBlockA` stores at `pz` a value below
`p384` equal to `x · y · (2^384)⁻¹` in `ZMod p384`. The buffers may overlap. -/
theorem s2nMontmulP384_correct_reduced (sa : AState) (px py pz : BitVec 64)
    (hx : sa.regs "%rsi" = px) (hy : sa.regs "%rdx" = py) (hz : sa.regs "%rdi" = pz)
    (hxr : limbs6 sa.mem px < p384) (hyr : limbs6 sa.mem py < p384) :
    limbs6 (runBlockA sa s2nMontmulP384Block).mem pz < p384 ∧
      ((limbs6 (runBlockA sa s2nMontmulP384Block).mem pz : Nat) : ZMod p384)
        = (limbs6 sa.mem px : ZMod p384) * (limbs6 sa.mem py : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ :=
  s2nMontmulP384_correct_addr sa px py pz hx hy hz
    ((Nat.mul_le_mul hxr.le hyr.le).trans (Nat.mul_le_mul_right _ p384_le_two_pow))

/-- The byte string this package's encoder lays down for the imported block decodes, as 264
instructions, to the block itself. -/
theorem s2nMontmulP384_bytes_decode :
    X86Backend.SailX86Decoder.decodeJStream 264
        (X86Backend.ScalarEncoder.encodeJBlock s2nAlloc s2nMontmulP384Block)
      = some s2nMontmulP384Block :=
  s2nMontmulP384_decode

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CertifyThirdPartyDemo

end
