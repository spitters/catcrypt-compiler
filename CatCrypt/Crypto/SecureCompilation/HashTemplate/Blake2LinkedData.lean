/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel

/-!
# The layout, store policy and clobber set of the BLAKE2b compression kernel

The layout `blake2bKAbi` of the linked BLAKE2b compression `Blake2Linked.blake2bKernel` at
which the frame size of its code is read, with the store policy and the clobber set of the
check `frameCheck` of the kernel. The module defines no constant whose value runs the
back half, so an executable that imports it computes no compile at start-up.

## Main definitions

* `blake2bKFrameLo`: the lower bound of the stack displacements of the layout.
* `blake2bKAbi`: the layout at which the frame size of the code is read.
* `blake2bKClob`, `blake2bKPol`: the clobber set and the store policy of the kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (StorePol)

/-- The registers the code of the BLAKE2b compression may change: every general-purpose
    register other than the stack register. -/
def blake2bKClob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- **The store policy of the BLAKE2b compression**: the red zone of `redZone` bytes, and the
    out window of the 8 words of the output array at the entry value of `%rdi`. -/
def blake2bKPol : StorePol := ⟨redZone, [("%rdi", 0, 64)]⟩

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
    blake2bKFrameLo (-8) [] []

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked
