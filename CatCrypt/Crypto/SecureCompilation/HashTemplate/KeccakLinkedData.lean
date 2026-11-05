/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Keccak
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

/-!
# The layout and the template of the Keccak-f[1600] kernel

The layout `keccakFAbi` of the linked Keccak-f[1600] permutation `KeccakLinked.keccakFKernel`
at which the frame size of its code is read, and the template `keccakFLayoutBody` over the
context of the two arrays of that layout. The module defines no constant whose value runs the
back half, so an executable that imports it computes no compile at start-up.

## Main definitions

* `keccakFAbi`: the layout of `keccak_f(dst, src)` at which the frame size of the code is
  read.
* `keccakFCtxt`, `keccakFHom`: the context of the layout and the renaming into it.
* `keccakFLayoutBody`: the template over the context of the input and the output array.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc

/-- **The layout of the Keccak-f[1600] permutation** `keccak_f(dst, src)` at which the frame
    size of the code is read: the output array `dst` (25 words) at `%rdi`, the input array
    `src` (25 words) at `%rsi`, the result the 25 words at `%rdi`, and the stack words at the
    displacements from `-4096` to `-8`. The kernel has the layout
    `redLayout keccakFAbi keccakFFrame`. -/
def keccakFAbi : AbiLayout :=
  AbiLayout.mk [⟨"dst", "%rdi", .words 25⟩, ⟨"src", "%rsi", .words 25⟩] [] (.words "%rdi" 25)
    [] (-4096) (-8) []

/-- The context of the layout: the input array, then the output array. -/
abbrev keccakFCtxt : Ctxt jasminDialect := [.stackArr 64 25, .stackArr 64 25]

/-- The renaming of the context of `keccakFBody` into `keccakFCtxt`: its one array is the
    input array. -/
def keccakFHom : Ctxt.Hom (d := jasminDialect) [JasminTy.stackArr 64 25] keccakFCtxt
  | _, .here => .here

/-- **The Keccak-f[1600] template over the context of the layout**: `keccakFBody` reading the
    input array, the output array unused. -/
def keccakFLayoutBody : Com jasminDialect keccakFCtxt (.stackArr 64 25) :=
  keccakFBody.rename keccakFHom

end CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked
