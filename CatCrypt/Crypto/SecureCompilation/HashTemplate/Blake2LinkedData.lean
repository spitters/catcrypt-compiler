/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

/-!
# The layout of the BLAKE2b compression kernel

The layout `blake2bKAbi` of the linked BLAKE2b compression `Blake2Linked.blake2bKernel` at
which the frame size of its code is read. The module defines no constant whose value runs the
back half, so an executable that imports it computes no compile at start-up.

## Main definitions

* `blake2bKFrameLo`: the lower bound of the stack displacements of the layout.
* `blake2bKAbi`: the layout at which the frame size of the code is read.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked

open CatCrypt.Crypto.SecureCompilation.Haxc

/-- The lower bound of the stack displacements of the layout at which the frame size of the
    code is read. -/
def blake2bKFrameLo : Int := -4096

/-- **The layout of the BLAKE2b compression** at which the frame size of the code is read: the
    output array `h` (8 words) at `%rdi`, the flag word `f0` at `%rsi`, the counter words `t1`
    at `%rdx` and `t0` at `%rcx`, the input array `hm` (24 words) at `%r8`, the result the 8
    words at `%rdi`, and the stack words at the displacements from `blake2bKFrameLo` to `-8`.
    The kernel has the layout `redLayout blake2bKAbi blake2bKFrame`. -/
def blake2bKAbi : AbiLayout :=
  AbiLayout.mk [⟨"h", "%rdi", .words 8⟩, ⟨"f0", "%rsi", .scalar⟩, ⟨"t1", "%rdx", .scalar⟩,
    ⟨"t0", "%rcx", .scalar⟩, ⟨"hm", "%r8", .words 24⟩] [] (.words "%rdi" 8) []
    blake2bKFrameLo (-8) []

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked
