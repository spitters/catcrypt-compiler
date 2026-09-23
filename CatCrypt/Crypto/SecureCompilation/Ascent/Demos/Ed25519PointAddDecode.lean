/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Bytes
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip
public meta import CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped

/-!
# The shipped `ed25519_point_add` block decodes from its encoding

`ed25519PointAddShippedBlock` (4909 instructions) is encoded by
`ScalarEncoder.encodeJBlock` under the identity allocation `s2nAlloc` on the sixteen
`%rN` names, and `SailX86Decoder.decodeJStream` reads those bytes back as the block
itself.

## Main results

* `paShipped_instrOk`: every instruction of the block is in the covered set of the
  byte round trip, reads the `MULX` multiplier from `%rdx`, and names only canonical
  `%rN` registers.
* `paShipped_covered`: every instruction of the block satisfies `blockCovered`.
* `paShipped_decode`: `decodeJStream 4909 (encodeJBlock s2nAlloc
  ed25519PointAddShippedBlock) = some ed25519PointAddShippedBlock`.

## Scope

The bytes of `paShipped_decode` are `encodeJBlock`'s. They are not the bytes `as`
produces for the source file: the source writes small constants as `movl $imm, %r32`
(`B8+r id`) and `movq $-1, %r` with a sign-extended `imm32`, while `encodeJBlock`
encodes `mov r (.imm v)` as `REX.W C7 /0 id` below `2 ^ 31` and as the ten-byte
`REX.W B8+r io` above it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddDecode

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc s2nInstrOk)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes (decode_phys)
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped

/-- Every instruction of the shipped block satisfies `s2nInstrOk`: it is in the covered
    set, a `MULX` reads its multiplier from `%rdx` under `s2nAlloc`, and every name it
    mentions is a canonical `%rN` name. A static check over the 4909 instructions,
    evaluated by `native_decide`. -/
theorem paShipped_instrOk : ed25519PointAddShippedBlock.all s2nInstrOk = true := by
  native_decide

/-- Every instruction of the shipped block is in the covered set of the byte round
    trip. -/
theorem paShipped_covered : ∀ i ∈ ed25519PointAddShippedBlock, blockCovered i = true :=
  fun i hi => by
    have := List.all_eq_true.mp paShipped_instrOk i hi
    simp only [s2nInstrOk, Bool.and_eq_true] at this
    exact this.1.1

/-- **The encoded shipped block decodes to itself.** `decodeJStream` reads
    `encodeJBlock s2nAlloc ed25519PointAddShippedBlock` as exactly 4909 instructions,
    and they are `ed25519PointAddShippedBlock`. -/
theorem paShipped_decode :
    decodeJStream 4909 (encodeJBlock s2nAlloc ed25519PointAddShippedBlock)
      = some ed25519PointAddShippedBlock := by
  have h := decode_phys _ paShipped_instrOk
  rwa [ed25519PointAddShippedBlock_length] at h

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddDecode
