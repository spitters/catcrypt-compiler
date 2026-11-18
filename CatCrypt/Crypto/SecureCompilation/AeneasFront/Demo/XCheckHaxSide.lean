/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST
public import HaxLean.TExpr

/-!
# The typed hax extractions of six Aeneas test functions

The `TExpr` literals the haxpipeT extraction produces for `xor_u32` and `shift_u32` of the
crate `bitwise` and for `u32_use_wrapping_add`, `u32_use_wrapping_sub`, `add_and` and
`u32_use_rotate_left` of the crate `scalars` (the sources of the Aeneas tests of the same
names), with the type annotations `ty_u32` (`u32`), `ty_usize` (`usize`) and `ty_unk`
(`.unknown`) in place of the generated numbered abbreviations. They are the hax side of the
checks of `AeneasFront.Demo.XCheckTest`.

## Main results

* `xor_u32_texpr`, `shift_u32_texpr`, `u32_use_wrapping_add_texpr`,
  `u32_use_wrapping_sub_texpr`, `add_and_texpr`, `u32_use_rotate_left_texpr`: the six
  extractions; the module states no theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.XCheckHax

open Hax

/-- The type `u32`. -/
abbrev ty_u32 : ImpType := (.uint .w32)

/-- The type `usize`. -/
abbrev ty_usize : ImpType := (.uint .wsize)

/-- The type of a sequencing node. -/
abbrev ty_unk : ImpType := .unknown

/-- `bitwise::xor_u32`: `a ^ b`. -/
def xor_u32_texpr : TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_u32) (.mk (.letBind "b" (.mk (.var "b") ty_u32)
    (.mk (.app "BitXor#32" [(.mk (.var "a") ty_u32), (.mk (.var "b") ty_u32)]) ty_u32))
    ty_u32)) ty_u32)

/-- `bitwise::shift_u32`: `(a >> 16) << 16`, the shift amount bound to `i` first. -/
def shift_u32_texpr : TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_u32) (.mk (.letBind "i" (.mk (.lit (ImpLit.int 16))
    ty_usize) (.mk (.letBind "t" (.mk (.app "Shr#32" [(.mk (.var "a") ty_u32),
    (.mk (.var "i") ty_usize)]) ty_u32) (.mk (.seq (.mk (.seq (.mk (.letBind "t"
    (.mk (.app "Shl#32" [(.mk (.var "t") ty_u32), (.mk (.var "i") ty_usize)]) ty_u32)
    (.mk (.var "t") ty_u32)) ty_u32) (.mk .unitVal .unit)) .unit) (.mk (.var "t") ty_u32))
    ty_u32)) ty_unk)) ty_u32)) ty_u32)

/-- `scalars::u32_use_wrapping_add`: `x.wrapping_add(y)`. -/
def u32_use_wrapping_add_texpr : TExpr :=
  (.mk (.letBind "x" (.mk (.var "x") ty_u32) (.mk (.letBind "y" (.mk (.var "y") ty_u32)
    (.mk (.app "wrapping_add#32" [(.mk (.var "x") ty_u32), (.mk (.var "y") ty_u32)]) ty_u32))
    ty_u32)) ty_u32)

/-- `scalars::u32_use_wrapping_sub`: `x.wrapping_sub(y)`. -/
def u32_use_wrapping_sub_texpr : TExpr :=
  (.mk (.letBind "x" (.mk (.var "x") ty_u32) (.mk (.letBind "y" (.mk (.var "y") ty_u32)
    (.mk (.app "wrapping_sub#32" [(.mk (.var "x") ty_u32), (.mk (.var "y") ty_u32)]) ty_u32))
    ty_u32)) ty_u32)

/-- `scalars::add_and`: `(b & a) + (b & a)`, a checked addition. -/
def add_and_texpr : TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_u32) (.mk (.letBind "b" (.mk (.var "b") ty_u32)
    (.mk (.app "Add#32" [(.mk (.app "BitAnd#32" [(.mk (.var "b") ty_u32),
    (.mk (.var "a") ty_u32)]) ty_u32), (.mk (.app "BitAnd#32" [(.mk (.var "b") ty_u32),
    (.mk (.var "a") ty_u32)]) ty_u32)]) ty_u32)) ty_u32)) ty_u32)

/-- `scalars::u32_use_rotate_left`: `x.rotate_left(2)`. -/
def u32_use_rotate_left_texpr : TExpr :=
  (.mk (.letBind "x" (.mk (.var "x") ty_u32) (.mk (.app "rotate_left#32"
    [(.mk (.var "x") ty_u32), (.mk (.lit (ImpLit.int 2)) ty_u32)]) ty_u32)) ty_u32)

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.XCheckHax
