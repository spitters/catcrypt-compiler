/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.RustSemantics.Encode
public import CatCrypt.Hax.RustSemantics.Arith
public import CatCrypt.Hax.RustSemantics.Casts
public import CatCrypt.Hax.RustSemantics.Bitwise
public import CatCrypt.Hax.RustSemantics.Arrays

/-!
# The Hax runtime against the Aeneas `Std` model: the operation table

For each of the 83 runtime operations of the ascent leaf audit (section 2, with its
census counts), the relation between the runtime operation (`HaxLean.Runtime`,
unbounded `Int`, total) and the Aeneas operation (`HaxLean.Rust`, machine integers
over `BitVec`, failing where Rust panics in its debug profile), stated through the
success-restricted relation `CatCrypt.Hax.RustSemantics.RCompOk` and the encoding of
`CatCrypt.Hax.RustSemantics.Encode`:

* class 1: a square `RCompOk EncRel (opA args) (pure (opC (enc args)))`, proved: on
  every input where the Aeneas operation returns `ok r`, the runtime computes the
  encoding of `r`;
* class 2: the negation of that square at a concrete input, proved: the Aeneas
  operation returns a value and the runtime computes a different one.

A width-tagged name `op#<w>` carries the width and, since the signed width-aware
runtime family, the sign of its operand: `<w>` (bare digits) for unsigned,
`i<w>` for signed, and (`cast` only) `u<w>` for an unsigned target cast from a
signed source (`HaxAdapter`'s `intTypeTag?`/`castTag?`). Each tag is compared
with the Aeneas operation of matching width and sign; every audited name has an
Aeneas counterpart, so no row is without a theorem. All names are in namespace
`CatCrypt.Hax.RustSemantics`.

## Arrays and collections (audit 2.1)

## Main results

| name | count | class | theorem |
|---|---|---|---|
| `index` | 4684 | 1 | `index_array_square`, `index_slice_square` |
| `array_update` | 2489 | 1 | `array_update_square` |
| `repeat` | 1115 | 1 | `repeat_square` |
| `array_lit` | 363 | 1 | `array_lit_square` |
| `len` | 329 | 1 | `len_slice_square`, `len_vec_square` |
| `push` | 151 | 1 | `push_square` |
| `deref` | 101 | 1 | `deref_square` |
| `with_capacity` | 84 | 1 | `with_capacity_square` |
| `new` | 44 | 1 | `new_square` |
| `extend_from_slice` | 41 | 1 (`Clone` returning its argument) | `extend_from_slice_square` |
| `RangeTo` | 37 | 1 (as `index arr (RangeTo n)`, printed `Hax.slice_to`) | `slice_to_square` |
| `copy_from_slice` | 37 | 1 | `copy_from_slice_square` |
| `index_mut` | 32 | 1 (element; scalar index printed `Hax.index`) | `index_mut_array_square` |
| `slice_update` | 29 | 1 | `slice_update_square` |
| `from_elem` | 29 | 1 (`Clone` returning its argument) | `from_elem_square` |

## Untagged arithmetic, comparison, logic (audit 2.2)

| name | count | class | theorem |
|---|---|---|---|
| `Add` | 1841 | 1 | `add_u_square`, `add_i_square` |
| `Mul` | 694 | 1 | `mul_u_square`, `mul_i_square` |
| `Lt` | 632 | 1 | `lt_u_square`, `lt_i_square` |
| `Sub` | 582 | 1 | `sub_u_square`, `sub_i_square` |
| `Eq` | 257 | 1 | `beq_u_square`, `beq_i_square` |
| `Rem` | 210 | 1 unsigned, 2 signed | `rem_u_square`, `rem_i_counterexample` |
| `Ne` | 165 | 1 | `bne_u_square`, `bne_i_square` |
| `Ge` | 152 | 1 | `ge_u_square`, `ge_i_square` |
| `&&` | 149 | 1 | `band_square` |
| `Gt` | 133 | 1 | `gt_u_square`, `gt_i_square` |
| `Div` | 124 | 1 unsigned, 2 signed | `div_u_square`, `div_i_counterexample` |
| `Not` | 88 | 1 `Bool` and signed, 2 unsigned | `not_bool_square`, `not_i_square`, `not_u_counterexample` |
| `None` | 63 | 1 | `none_square` |
| `eq` | 43 | 1 | `beq_u_square`, `beq_i_square` |
| `Le` | 35 | 1 | `le_u_square`, `le_i_square` |
| `Some` | 35 | 1 | `some_square` |
| `\|\|` | 30 | 1 | `bor_square` |

## Width families (audit 2.3)

Every row is class 1: each width-tagged family now has a signed sibling tag
(`#i<w>`, or `#u<w>` for a signed-to-unsigned cast) naming a distinct, correct
runtime operation, so no signed counterexample remains for a tagged name.

| name | count | class | theorem |
|---|---|---|---|
| `cast#8`, `cast#16`, `cast#32`, `cast#64`, `cast#128` | 497, 73, 289, 453, 129 | 1 | `cast_u_square` |
| `cast#u8`, …, `cast#u128` | (signed-to-unsigned casts of the same names) | 1 | `cast_iu_square` |
| `cast#i8`, …, `cast#i128` | (casts to a signed type of the same names) | 1 | `cast_ii_square`, `cast_ui_square` |
| `BitXor#8`, `#16`, `#32`, `#64`, `#128` | 455, 14, 208, 135, 4 | 1 | `bitxor_w_u_square` |
| `BitXor#i8`, …, `#i128` | (signed operands of the same names) | 1 | `bitxor_iw_square` |
| `BitXor` | 124 | 1 unsigned, 2 signed | `bitxor_u_square`, `bitxor_i_counterexample` |
| `BitAnd#8`, `#16`, `#32`, `#64`, `#128` | 64, 7, 144, 176, 8 | 1 | `bitand_w_u_square` |
| `BitAnd#i8`, …, `#i128` | (signed operands of the same names) | 1 | `bitand_iw_square` |
| `BitAnd` | 38 | 1 unsigned, 2 signed | `bitand_u_square`, `bitand_i_counterexample` |
| `BitOr#8`, `#16`, `#32`, `#64`, `#128` | 14, 1, 76, 90, 3 | 1 | `bitor_w_u_square` |
| `BitOr#i8`, …, `#i128` | (signed operands of the same names) | 1 | `bitor_iw_square` |
| `BitOr` | 52 | 1 unsigned, 2 signed | `bitor_u_square`, `bitor_i_counterexample` |
| `Shr#8`, `#16`, `#32`, `#64`, `#128` | 38, 18, 154, 281, 42 | 1 | `shr_w_u_square` |
| `Shr#i8`, …, `#i128` | (signed operands of the same names) | 1 | `shr_iw_square` |
| `Shr` | 26 | 1 unsigned, 2 signed | `shr_u_square`, `shr_i_counterexample` |
| `Shl#8`, `#16`, `#32`, `#64`, `#128` | 28, 15, 97, 146, 20 | 1 | `shl_w_u_square` |
| `Shl#i8`, …, `#i128` | (signed operands of the same names) | 1 | `shl_iw_square` |
| `Shl` | 2 | 2 | `shl_u_counterexample`, `shl_i_counterexample` |
| `Not#8`, `Not#32`, `Not#64` | 4, 18, 21 | 1 | `bitnot_w_u_square` |
| `Not#i8`, `Not#i32`, `Not#i64` | (signed operands of the same names) | 1 | `bitnot_iw_square` |
| `rotate_right#32`, `rotate_right#64` | 178, 60 | 1 | `rotate_right_w_u_square` |
| `rotate_right#i32`, `rotate_right#i64` | (signed operands of the same names) | 1 | `rotate_right_iw_square` |
| `rotate_right` | 2 | 1 at `u64`, 2 at `u32` and signed | `rotate_right_u64_square`, `rotate_right_u32_counterexample`, `rotate_right_i_counterexample` |
| `wrapping_add#32`, `#64`, `#8`, `#128` | 342, 71, 2, 7 | 1 | `wrapping_add_w_u_square` |
| `wrapping_add#i32`, `#i64`, `#i8`, `#i128` | (signed operands of the same names) | 1 | `wrapping_add_iw_square` |
| `wrapping_add` | 22 | 2 | `wrapping_add_u_counterexample`, `wrapping_add_i_counterexample` |
| `wrapping_mul#8`, `#32`, `#64`, `#128` | 2, 4, 37, 5 | 1 | `wrapping_mul_w_u_square` |
| `wrapping_mul#i8`, `#i32`, `#i64`, `#i128` | (signed operands of the same names) | 1 | `wrapping_mul_iw_square` |
| `wrapping_mul` | 14 | 2 | `wrapping_mul_u_counterexample`, `wrapping_mul_i_counterexample` |

Beyond the 83 names, `overflowing_sub_w_square` states the square of
`overflowing_sub#w` at a borrow.

The untagged `Shl`, `wrapping_add` and `wrapping_mul` are class 2 on unsigned
operands as well: the runtime operation does not reduce to a width. The
untagged families reach the runtime only when the extraction pipeline cannot
resolve the operand's type; the signed-width fix does not touch them.
-/
