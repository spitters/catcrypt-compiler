/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel

/-!
# The layouts, store policies and clobber sets of the SHA-2 compression kernels

The layout `sha512Abi` of the linked SHA-512 compression `Sha2Linked.sha512Kernel` at which the
frame size of its code is read, and the layout `sha256Abi` of the SHA-256 compression at the
u64-slot layout: each 32-bit word of the arrays is held in a 64-bit slot with zero high bits,
the valuation `NarrowWords.mapVal V` that the back half reads after its widening of narrow
words. The module defines no constant whose value runs the back half,
so an executable that imports it computes no compile at start-up.

## Main definitions

* `sha512LayoutFrame`: the bound of the stack words of the layout.
* `sha512Abi`: the layout at which the frame size of the code is read.
* `sha256Abi`: the u64-slot layout of the SHA-256 compression.
* `sha512Clob`, `sha512Pol`, `Sha256Linked.sha256KClob`, `Sha256Linked.sha256KPol`: the
  clobber sets and the store policies of the two kernels, the inputs of their `frameCheck`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (StorePol)

/-- The registers the code of the SHA-512 compression may change: every general-purpose
    register other than the stack register. -/
def sha512Clob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- The store policy of the code of the SHA-512 compression: the red zone of `redZone` bytes,
    and the out window of the 64 bytes of the output array at `%rdi`. -/
def sha512Pol : StorePol := ⟨redZone, [("%rdi", 0, 64)]⟩

/-- The bound of the stack words of the layout at which the frame size of the code is read. -/
def sha512LayoutFrame : Nat := 4096

/-- **The layout of the SHA-512 compression** at which the frame size of the code is read: the
    output array `h` (8 words) at `%rdi`, the input array `hm` (24 words) at `%rsi`, the result
    the 8 words at `%rdi`, and the stack words from `sha512LayoutFrame` bytes below the entry
    stack pointer. The kernel has the layout `redLayout sha512Abi sha512Frame`. -/
def sha512Abi : AbiLayout :=
  AbiLayout.mk [⟨"h", "%rdi", .words 8⟩, ⟨"hm", "%rsi", .words 24⟩] [] (.words "%rdi" 8) []
    (-(sha512LayoutFrame : Int)) (-8) [] []

/-- **The u64-slot layout of the SHA-256 compression**: the output array `h` (8 slots) at `%rdi`,
    the input array `hm` (24 slots) at `%rsi`, each slot a 64-bit word holding a 32-bit word with
    zero high bits; the result the 8 slots at `%rdi`, and the stack words from
    `sha512LayoutFrame` bytes below the entry stack pointer. -/
def sha256Abi : AbiLayout :=
  AbiLayout.mk [⟨"h", "%rdi", .words 8⟩, ⟨"hm", "%rsi", .words 24⟩] [] (.words "%rdi" 8) []
    (-(sha512LayoutFrame : Int)) (-8) [] []

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha256Linked

open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (StorePol)

/-- The registers the code of the SHA-256 compression may change: every general-purpose
    register other than the stack register. -/
def sha256KClob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- **The store policy of the SHA-256 compression**: the red zone of `redZone` bytes, and the
    out window of the 8 slots of the output array at the entry value of `%rdi`. -/
def sha256KPol : StorePol := ⟨redZone, [("%rdi", 0, 64)]⟩

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha256Linked
