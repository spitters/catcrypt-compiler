/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Denote

/-!
# MLIR `vector` dialect — AVX-512 lowering pass (task #276)

A second lowering target for the abstract `VectorOp` alphabet, next to the
AVX2 / per-lane `ScalarExpansion` lowering in [`Lowering.lean`](Lowering.lean).
A `VectorOp` term is lowered to a 512-bit mnemonic instruction by one pass,
`lowerAVX512 : LaneWidth → VectorOp α n → Option (AVX512Inst α n)`, instead of
per-primitive mnemonic tables.

This file defines:

* `AVX512Inst` — a 512-bit mnemonic instruction (the `zmm` analogue of the
  `__m256i` mnemonics emitted at AVX2 width, e.g. `#VPADD_8u64`,
  `#VPMULL_16u32`, `#VPSRA_*`);
* `lowerAVX512` — the lowering pass, one rule per `VectorOp` constructor;
* `renderAVX512` — the mnemonic line for an instruction;
* `denote512` — a meaning for each instruction, and the theorems
  `lowerAVX512_*_correct`, one per constructor.

## What the theorems state

Each `AVX512Inst` constructor stores the lane function of the abstract op it was
lowered from (`op`, `shf`, `aff`, `rnd`), and `denote512` applies that stored
function lane-wise. The `lowerAVX512_*_correct` theorems are therefore `rfl`:
they say that lowering does not change the stored lane function. `denote512` is
not a model of the named x86 instruction. Nothing ties the mnemonic to the
function it carries (an `.add` with a multiplication as `op` is rendered as
`#VPADD`), nor the `LaneWidth` to the lane type `α` or the lane count `n`.

## Lane-count contract

AVX-512 doubles the lane count of AVX2 at every element width:

| element | AVX2 (`__m256i`) | AVX-512 (`zmm`) | mnemonic suffix |
|---------|------------------|-----------------|-----------------|
| u64     | 4 lanes          | **8** lanes     | `8u64`          |
| u32     | 8 lanes          | **16** lanes    | `16u32`         |
| u16     | 16 lanes         | **32** lanes    | `32u16`         |
| u8      | 32 lanes         | **64** lanes    | `64u8`          |

The abstract `VectorOp α n` is lane-count-polymorphic (`n` is a parameter). The
width is recorded in the instruction's `LaneWidth` argument so `renderAVX512`
produces the `_8u64` / `_16u32` / … suffix; the caller chooses a width consistent
with `α` and `n`.

## ISA extensions

`affineByte` lowers to `VGF2P8AFFINEQB zmm` (the `AVX512_GFNI` extension) and
`aesRound` to `VAESENC zmm` (the `AVX512_VAES` extension). `AVX512Inst.ext` tags
these two with `Ext.gfni512` / `Ext.vaes512`, so a backend targeting a CPU
without them can reject them, and tags every other instruction `Ext.f`. That
tagging is coarser than the ISA: the byte and word forms (`VPADDB`/`VPADDW`,
`VPBROADCASTB`/`W`, `VPMULLW`, `VPMULHW`, `VPSRAW`, `VPERMW`) require
`AVX512BW`, `VPERMB` requires `AVX512_VBMI`, and `VPMULLQ` requires `AVX512DQ`,
none of which `Ext` records. x86 has no high-half multiply at 32- or 64-bit lane
width, so `#VPMULH_16u32` / `#VPMULH_8u64` name no single instruction.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

open VectorOp

/-! ## 1. The AVX-512 instruction target

A 512-bit mnemonic instruction. This is the `zmm`-width analogue of the
`__m256i` mnemonic lines the migrated consumers (`MldsaNtt4WayVec.render`,
`ChaCha4WayVec`) emit at AVX2 width. We keep the *structure* (which mnemonic,
which width suffix, which carried lane op) so that:

* `render512` can produce the jasmin / MLIR `x86vector` text, and
* `denote512` can give the instruction a `Fin n → α` semantics that we prove
  equal to the abstract op's denotation. -/

/-- The element-width suffix of an AVX-512 packed instruction. Determines both
    the mnemonic spelling (`_8u64` etc.) and the `zmm` lane count. -/
inductive LaneWidth where
  /-- 8 × u64 lanes (`zmm` as 8 quadwords). -/
  | w8u64
  /-- 16 × u32 lanes (`zmm` as 16 doublewords). -/
  | w16u32
  /-- 32 × u16 lanes (`zmm` as 32 words). -/
  | w32u16
  /-- 64 × u8 lanes (`zmm` as 64 bytes). -/
  | w64u8
  deriving DecidableEq, Repr

/-- The `_<lanes><elt>` mnemonic suffix string for a width. -/
def LaneWidth.suffix : LaneWidth → String
  | .w8u64  => "8u64"
  | .w16u32 => "16u32"
  | .w32u16 => "32u16"
  | .w64u8  => "64u8"

/-- The `zmm` lane count for a width (AVX-512 = double the AVX2 count). -/
def LaneWidth.lanes : LaneWidth → Nat
  | .w8u64  => 8
  | .w16u32 => 16
  | .w32u16 => 32
  | .w64u8  => 64

/-- An ISA extension an AVX-512 mnemonic may require on top of baseline
    `AVX512F`: `f` for the baseline, `gfni512` / `vaes512` for the two
    extensions this model tracks (`AVX512BW`, `AVX512DQ` and `AVX512_VBMI` are
    not represented). -/
inductive Ext where
  /-- Baseline `AVX512F`, present on every AVX-512 target. -/
  | f
  /-- `AVX512_GFNI` (the `VGF2P8AFFINEQB zmm` family). -/
  | gfni512
  /-- `AVX512_VAES` (the `VAESENC zmm` family). -/
  | vaes512
  deriving DecidableEq, Repr

/-- A 512-bit mnemonic instruction the AVX-512 lowering pass emits. Each
    constructor stores the lane function of the abstract op it came from
    (`α → α → α` / `α → Nat → α` / `α → α`), which `denote512` applies; the
    `width` records the `zmm` element shape used in the rendered suffix. -/
inductive AVX512Inst (α : Type) (n : Nat) where
  /-- `#VPBROADCAST_<w>(x)` — splat scalar `x` to all `zmm` lanes. -/
  | vpbroadcast (width : LaneWidth) (x : α) : AVX512Inst α n
  /-- `#VPADD_<w>(v, w)` — packed lane add (the carried op may be `+`, `xor`,
      `-`; the mnemonic family is `VPADD`/`VPXOR`/`VPSUB`, all binary `map₂`). -/
  | vpaddFamily (mnem : String) (width : LaneWidth) (op : α → α → α)
      (v w : VectorTy α n) : AVX512Inst α n
  /-- `#VPMULL_<w>(v, w)` — packed low-half lane multiply. -/
  | vpmull (width : LaneWidth) (op : α → α → α) (v w : VectorTy α n) :
      AVX512Inst α n
  /-- `#VPMULH_<w>(v, w)` — packed high-half lane multiply (`VPMULHW` zmm). -/
  | vpmulh (width : LaneWidth) (op : α → α → α) (v w : VectorTy α n) :
      AVX512Inst α n
  /-- `#VPSLL_<w>(v, imm)` — packed logical shift-left by immediate. -/
  | vpsll (width : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
      AVX512Inst α n
  /-- `#VPSRL_<w>(v, imm)` — packed logical shift-right by immediate. -/
  | vpsrl (width : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
      AVX512Inst α n
  /-- `#VPSRA_<w>(v, imm)` — packed arithmetic (signed) shift-right (`VPSRAW`/
      `VPSRAD`/`VPSRAQ` zmm). -/
  | vpsra (width : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
      AVX512Inst α n
  /-- `#VPERM_<w>(v, idx)` — full cross-lane permute (`VPERMD`/`VPERMQ`/
      `VPERMW`/`VPERMB` zmm). AVX-512 has full cross-`zmm` permutes, unlike
      AVX2's in-128-bit-lane shuffles. -/
  | vperm (width : LaneWidth) (v : VectorTy α n) (π : Fin n → Fin n) :
      AVX512Inst α n
  /-- `#VGF2P8AFFINEQB_512(v)` — per-lane GF(2) affine. Requires `AVX512_GFNI`
      (`ext = .gfni512`). The matrix/bias are closed over in `aff`. -/
  | vgf2p8affine (aff : α → α) (v : VectorTy α n) : AVX512Inst α n
  /-- `#VAESENC_512(state, key)` — per-lane AES round. Requires `AVX512_VAES`
      (`ext = .vaes512`). -/
  | vaesenc (rnd : α → α → α) (state key : VectorTy α n) : AVX512Inst α n

namespace AVX512Inst

variable {α : Type} {n : Nat}

/-- The ISA extension tag of an instruction: `gfni512` / `vaes512` for the
    `affineByte` / `aesRound` lowerings, `f` for every other constructor
    regardless of width (see the module header for the extensions this omits). -/
def ext : AVX512Inst α n → Ext
  | .vgf2p8affine _ _ => .gfni512
  | .vaesenc _ _ _ => .vaes512
  | _ => .f

/-- The width suffix string for an instruction (the GFNI/VAES extension
    instructions operate on bytes; their full-`zmm` form is `_512`). -/
def widthSuffix : AVX512Inst α n → String
  | .vpbroadcast w _ => w.suffix
  | .vpaddFamily _ w _ _ _ => w.suffix
  | .vpmull w _ _ _ => w.suffix
  | .vpmulh w _ _ _ => w.suffix
  | .vpsll w _ _ _ => w.suffix
  | .vpsrl w _ _ _ => w.suffix
  | .vpsra w _ _ _ => w.suffix
  | .vperm w _ _ => w.suffix
  | .vgf2p8affine _ _ => "512"
  | .vaesenc _ _ _ => "512"

/-! ## 2. Per-instruction denotation (`Fin n → α`)

Each instruction's meaning as a lane vector: the stored lane function applied
lane-wise (or the stored permutation / broadcast value). The mnemonic and the
width do not enter. -/

/-- The `Fin n → α` meaning of an AVX-512 instruction: its stored lane function
    applied lane-wise. It is not an x86 semantics of the mnemonic. -/
@[reducible] def denote512 : AVX512Inst α n → VectorTy α n
  | .vpbroadcast _ x => VectorTy.replicate x
  | .vpaddFamily _ _ op v w => VectorTy.map₂ op v w
  | .vpmull _ op v w => VectorTy.map₂ op v w
  | .vpmulh _ op v w => VectorTy.map₂ op v w
  | .vpsll _ shf m v => VectorTy.map₁imm shf m v
  | .vpsrl _ shf m v => VectorTy.map₁imm shf m v
  | .vpsra _ shf m v => VectorTy.map₁imm shf m v
  | .vperm _ v π => VectorTy.shuffle π v
  | .vgf2p8affine aff v => VectorTy.map₁ aff v
  | .vaesenc rnd s k => VectorTy.map₂ rnd s k

end AVX512Inst

/-! ## 3. The AVX-512 lowering pass

`lowerAVX512 width op` maps a vector-result `VectorOp` to a 512-bit mnemonic
instruction at the chosen `width`. Scalar-result ops (`extract` / `reduce`), the
single-lane `insert` and the integer `fma` return `none`. The pass has one rule
per constructor. -/
def lowerAVX512 {α : Type} {n : Nat} (width : LaneWidth) :
    VectorOp α n → Option (AVX512Inst α n)
  | .broadcast x => some (.vpbroadcast width x)
  | .extract _ _ => none
  | .insert _ _ _ =>
      -- `insert` is a single-lane store; AVX-512 spells it `VPINSR`/blend,
      -- not a packed `zmm` op. Out of scope for this lane-parallel pass
      -- (same as AVX2 `lower`, which expands it as a one-lane store).
      none
  | .add op v w => some (.vpaddFamily "#VPADD" width op v w)
  | .mul op v w => some (.vpmull width op v w)
  | .fma _ _ _ _ _ =>
      -- AVX-512 has `VFMADD*` for floats; the integer-lane FMA the dialect
      -- models (`a*b+c` over `BitVec`/`ZMod` lanes) is a mul-then-add pair,
      -- not a single integer mnemonic. Emitted as the mul/add pair, not a
      -- single instruction — out of scope for the single-instruction pass.
      none
  | .shuffle v π => some (.vperm width v π)
  | .reduce _ _ _ => none
  | .shiftL shf m v => some (.vpsll width shf m v)
  | .shiftR shf m v => some (.vpsrl width shf m v)
  | .mulHi op v w => some (.vpmulh width op v w)
  | .shiftRA shf m v => some (.vpsra width shf m v)
  | .affineByte aff v => some (.vgf2p8affine aff v)
  | .aesRound rnd s k => some (.vaesenc rnd s k)

/-! ## 4. Rendering — the emitted 512-bit mnemonic line

`renderAVX512` produces jasmin / `x86vector` mnemonic text in the
`dst = #MNEM_<width>(args);` shape of `MldsaNtt4WayVec.LatticeNttVecOp.render`,
at `zmm` width, against named string operands. No theorem relates the rendered
text to `denote512`. -/

/-- Render an AVX-512 instruction to its mnemonic line, given string operand
    names. Binary ops take two source names; unary/immediate ops take one
    plus the immediate. -/
def renderAVX512 {α : Type} {n : Nat} (dst : String) (srcs : List String) :
    AVX512Inst α n → String
  | .vpbroadcast w _ =>
      dst ++ " = #VPBROADCAST_" ++ w.suffix ++ "(" ++ (srcs.headD "x") ++ ");"
  | .vpaddFamily mnem w _ _ _ =>
      dst ++ " = " ++ mnem ++ "_" ++ w.suffix ++ "("
        ++ String.intercalate ", " (srcs.take 2) ++ ");"
  | .vpmull w _ _ _ =>
      dst ++ " = #VPMULL_" ++ w.suffix ++ "("
        ++ String.intercalate ", " (srcs.take 2) ++ ");"
  | .vpmulh w _ _ _ =>
      dst ++ " = #VPMULH_" ++ w.suffix ++ "("
        ++ String.intercalate ", " (srcs.take 2) ++ ");"
  | .vpsll w _ m _ =>
      dst ++ " = #VPSLL_" ++ w.suffix ++ "(" ++ (srcs.headD "v") ++ ", "
        ++ toString m ++ ");"
  | .vpsrl w _ m _ =>
      dst ++ " = #VPSRL_" ++ w.suffix ++ "(" ++ (srcs.headD "v") ++ ", "
        ++ toString m ++ ");"
  | .vpsra w _ m _ =>
      dst ++ " = #VPSRA_" ++ w.suffix ++ "(" ++ (srcs.headD "v") ++ ", "
        ++ toString m ++ ");"
  | .vperm w _ _ =>
      dst ++ " = #VPERM_" ++ w.suffix ++ "(" ++ (srcs.headD "v") ++ ", idx);"
  | .vgf2p8affine _ _ =>
      dst ++ " = #VGF2P8AFFINEQB_512(" ++ (srcs.headD "v") ++ ", mat);"
  | .vaesenc _ _ _ =>
      dst ++ " = #VAESENC_512(" ++ String.intercalate ", " (srcs.take 2) ++ ");"

/-! ## 5. Lowering keeps the stored lane function

For each constructor, `(lowerAVX512 w op).map (·.denote512)` equals the lane
vector obtained by applying the abstract op's own lane function, in the shape of
the AVX2 `lower_*_correct` lemmas. Every proof is `rfl`, because the instruction
stores that function and `denote512` applies it; the statements do not describe
the x86 instruction named by the mnemonic. -/

/-- Lowering `.broadcast x` and applying `denote512` gives `replicate x`. -/
theorem lowerAVX512_broadcast_correct {α : Type} {n : Nat}
    (w : LaneWidth) (x : α) :
    (lowerAVX512 w (.broadcast x : VectorOp α n)).map (·.denote512)
      = some (VectorTy.replicate x) := rfl

/-- Lowering `.add op` (rendered `#VPADD_<w>`) and applying `denote512` gives
    `op` applied lane-wise, for any `op`. -/
theorem lowerAVX512_add_correct {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.add op v w' : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ op v w') := rfl

/-- Lowering `.mul op` (rendered `#VPMULL_<w>`) and applying `denote512` gives
    `op` applied lane-wise, for any `op`. -/
theorem lowerAVX512_mul_correct {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.mul op v w' : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ op v w') := rfl

/-- Lowering `.mulHi op` (rendered `#VPMULH_<w>`) and applying `denote512` gives
    `op` applied lane-wise, for any `op`. -/
theorem lowerAVX512_mulHi_correct {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.mulHi op v w' : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ op v w') := rfl

/-- Lowering `.shiftL shf m` (rendered `#VPSLL_<w>`) and applying `denote512`
    gives `shf · m` applied lane-wise, for any `shf`. -/
theorem lowerAVX512_shiftL_correct {α : Type} {n : Nat}
    (w : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lowerAVX512 w (.shiftL shf m v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁imm shf m v) := rfl

/-- Lowering `.shiftR shf m` (rendered `#VPSRL_<w>`) and applying `denote512`
    gives `shf · m` applied lane-wise, for any `shf`. -/
theorem lowerAVX512_shiftR_correct {α : Type} {n : Nat}
    (w : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lowerAVX512 w (.shiftR shf m v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁imm shf m v) := rfl

/-- Lowering `.shiftRA shf m` (rendered `#VPSRA_<w>`) and applying `denote512`
    gives `shf · m` applied lane-wise, for any `shf`. -/
theorem lowerAVX512_shiftRA_correct {α : Type} {n : Nat}
    (w : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lowerAVX512 w (.shiftRA shf m v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁imm shf m v) := rfl

/-- Lowering `.shuffle v π` (rendered `#VPERM_<w>`) and applying `denote512`
    gives `VectorTy.shuffle π v`. The rendered line passes the fixed operand
    name `idx`; the index vector is not rendered from `π`. -/
theorem lowerAVX512_shuffle_correct {α : Type} {n : Nat}
    (w : LaneWidth) (v : VectorTy α n) (π : Fin n → Fin n) :
    (lowerAVX512 w (.shuffle v π : VectorOp α n)).map (·.denote512)
      = some (VectorTy.shuffle π v) := rfl

/-- Lowering `.affineByte aff` (rendered `#VGF2P8AFFINEQB_512`, tagged
    `ext = .gfni512`) and applying `denote512` gives `aff` applied lane-wise, for
    any `aff`. -/
theorem lowerAVX512_affineByte_correct {α : Type} {n : Nat}
    (w : LaneWidth) (aff : α → α) (v : VectorTy α n) :
    (lowerAVX512 w (.affineByte aff v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁ aff v) := rfl

/-- Lowering `.aesRound rnd` (rendered `#VAESENC_512`, tagged `ext = .vaes512`)
    and applying `denote512` gives `rnd` applied lane-wise, for any `rnd`. -/
theorem lowerAVX512_aesRound_correct {α : Type} {n : Nat}
    (w : LaneWidth) (rnd : α → α → α) (s k : VectorTy α n) :
    (lowerAVX512 w (.aesRound rnd s k : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ rnd s k) := rfl

/-! ## 6. Agreement with `denoteVectorOp`

For `add` and `mulHi`, the lowered instruction's `denote512`, wrapped as a
vector result, equals the abstract `denoteVectorOp`. Only these two
constructors are stated. -/

/-- For `.add op`, `denote512` of the lowered instruction, wrapped as
    `VectorOp.Result.vec`, equals `denoteVectorOp` of the abstract op (`rfl`). -/
theorem lowerAVX512_add_eq_abstract {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.add op v w' : VectorOp α n)).map
        (fun i => VectorOp.Result.vec i.denote512)
      = some (denoteVectorOp (.add op v w' : VectorOp α n)) := rfl

/-- The same statement as `lowerAVX512_add_eq_abstract` for `.mulHi op`. -/
theorem lowerAVX512_mulHi_eq_abstract {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.mulHi op v w' : VectorOp α n)).map
        (fun i => VectorOp.Result.vec i.denote512)
      = some (denoteVectorOp (.mulHi op v w' : VectorOp α n)) := rfl

/-! ## 7. Extension tags

`ext` tags the `affineByte` and `aesRound` lowerings with `AVX512_GFNI` /
`AVX512_VAES`, so a backend targeting a CPU without them can reject them. The
theorems below evaluate the tag at one width each. -/

/-- At width `w64u8`, the lowering of `affineByte` is tagged `Ext.gfni512`. -/
theorem affineByte_requires_gfni512 {α : Type} {n : Nat} (aff : α → α)
    (v : VectorTy α n) :
    ((lowerAVX512 .w64u8 (.affineByte aff v)).map AVX512Inst.ext)
      = some Ext.gfni512 := rfl

/-- At width `w64u8`, the lowering of `aesRound` is tagged `Ext.vaes512`. -/
theorem aesRound_requires_vaes512 {α : Type} {n : Nat} (rnd : α → α → α)
    (s k : VectorTy α n) :
    ((lowerAVX512 .w64u8 (.aesRound rnd s k)).map AVX512Inst.ext)
      = some Ext.vaes512 := rfl

/-- At width `w16u32`, the lowering of `add` is tagged `Ext.f`. Only this op and
    width are stated; the other constructors are tagged `f` by the definition
    of `ext`. -/
theorem add_is_avx512f {α : Type} {n : Nat} (op : α → α → α)
    (v w : VectorTy α n) :
    ((lowerAVX512 .w16u32 (.add op v w)).map AVX512Inst.ext) = some Ext.f := rfl

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
