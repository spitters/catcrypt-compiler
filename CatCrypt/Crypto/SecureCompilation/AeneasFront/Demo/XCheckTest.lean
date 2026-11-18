/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.XCheck
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.ReifiedHax
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestScalars
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.XCheckHaxSide

/-!
# The cross-check `xcheck` on straight-line scalar functions

`xcheck σ m s` compares the hax translation of the module `m` (the typed extraction of the
haxpipeT output, `Demo.XCheckHaxSide`) with the Aeneas translation of the source `s` (the
program of `reifyAeneas%` on the Aeneas test output) under one layout `σ`. Each function below
is a pair of a module and a source over `u32` parameters, an input of `xcheck`.

## Main results

* `lay1`, `lay2`: the layouts of one and two `u32` parameters.
* `wrapAddSrc`, `addAndSrc`, `xorSrc`, `shiftSrc`: the Aeneas sides of the pairs.
* `wrapAddMod`, `wrapSubMod`, `addAndMod`, `xorMod`, `shiftMod`, `rotMod`: the hax sides.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.XCheckTest

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.Hax (HaxModule)

/-- The layout of a function of one `u32` parameter `x`: the word in `%rdi`, the result in
    `%rax`. -/
def lay1 (x : String) : AbiLayout where
  args := [⟨x, "%rdi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- The layout of a function of two `u32` parameters `x`, `y`: the layout lists the last
    parameter first. -/
def lay2 (x y : String) : AbiLayout where
  args := [⟨y, "%rsi", .scalar⟩, ⟨x, "%rdi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- The reading of `scalars.u32_use_wrapping_add`. -/
def wrapAddP := reifyAeneas% scalars.u32_use_wrapping_add

/-- The reading of `scalars.add_and`. -/
def addAndP := reifyAeneas% scalars.add_and

/-- The Aeneas source of `scalars.u32_use_wrapping_add`. -/
def wrapAddSrc : AeSrc :=
  AeSrc.ofFn [.u .U32 (by decide), .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => scalars.u32_use_wrapping_add a.1 a.2.1) wrapAddP.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := Reify.toDenote (wrapAddP.sound a.1 a.2.1) h
      exact ⟨N, hN N le_rfl⟩)

/-- The Aeneas source of `scalars.add_and`. -/
def addAndSrc : AeSrc :=
  AeSrc.ofFn [.u .U32 (by decide), .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => scalars.add_and a.1 a.2.1) addAndP.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := Reify.toDenote (addAndP.sound a.1 a.2.1) h
      exact ⟨N, hN N le_rfl⟩)

/-- The Aeneas source of `bitwise.xor_u32` (hax backend output). -/
def xorSrc : AeSrc :=
  AeSrc.ofFn [.u .U32 (by decide), .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => Hax.bitwise.xor_u32 a.1 a.2.1) Hax.xorU32.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := Hax.xorU32_denote a.1 a.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- The Aeneas source of `bitwise.shift_u32` (hax backend output). -/
def shiftSrc : AeSrc :=
  AeSrc.ofFn [.u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => Hax.bitwise.shift_u32 a.1) Hax.shiftU32.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := Hax.shiftU32_denote a.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- The hax module of `u32_use_wrapping_add`. -/
def wrapAddMod : HaxModule := XCheckHax.u32_use_wrapping_add_texpr

/-- The hax module of `u32_use_wrapping_sub`. -/
def wrapSubMod : HaxModule := XCheckHax.u32_use_wrapping_sub_texpr

/-- The hax module of `add_and`. -/
def addAndMod : HaxModule := XCheckHax.add_and_texpr

/-- The hax module of `xor_u32`. -/
def xorMod : HaxModule := XCheckHax.xor_u32_texpr

/-- The hax module of `shift_u32`. -/
def shiftMod : HaxModule := XCheckHax.shift_u32_texpr

/-- The hax module of `u32_use_rotate_left`. -/
def rotMod : HaxModule := XCheckHax.u32_use_rotate_left_texpr

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.XCheckTest
