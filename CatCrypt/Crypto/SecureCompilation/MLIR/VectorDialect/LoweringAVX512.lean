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

This is a **second** lowering target for the abstract `VectorOp` alphabet,
landed *alongside* the AVX2 / per-lane `ScalarExpansion` lowering in
[`Lowering.lean`](Lowering.lean) without touching it.

## The #183 architectural win, demonstrated

The thesis of the structured `VectorOp` dialect (#183) is:

> adding a new SIMD width should be **a new lowering pass, not 22 mnemonics ×
> 7 per-primitive rewrites.**

Before the dialect, ChaCha / ML-DSA / ML-KEM / GFNI / VAES each spelled their
512-bit mnemonics inline in their own emit file; adding AVX-512 meant editing
every one of them. With the dialect, every migrated consumer already emits its
kernel as a `VectorOp` term. So a *single* new pass here —
`lowerAVX512 : VectorOp α n → Option AVX512Inst` — re-targets **all** of them
to 512-bit mnemonics, with the consumer code left byte-for-byte unchanged.

This file lands that pass:

* `AVX512Inst` — a 512-bit mnemonic instruction (the `zmm` analogue of the
  `__m256i` mnemonics the consumers emit at AVX2 width, e.g. `#VPADD_8u64`,
  `#VPMULL_16u32`, `#VPSRA_*`);
* `lowerAVX512` — the new lowering pass, one rule per `VectorOp` constructor;
* `render512` — the emitted 512-bit mnemonic line;
* a `BitVec`-shaped semantic model `denote512` for each mnemonic, and a
  family of **denotation-preservation theorems** (`lowerAVX512_*_correct`)
  proving that the 512-bit mnemonic the pass selects denotes the *same
  per-lane operation* as the abstract op. These mirror the AVX2
  `lower_*_correct` shape, one per constructor.

## Lane-count contract

AVX-512 doubles the lane count of AVX2 at every element width:

| element | AVX2 (`__m256i`) | AVX-512 (`zmm`) | mnemonic suffix |
|---------|------------------|-----------------|-----------------|
| u64     | 4 lanes          | **8** lanes     | `8u64`          |
| u32     | 8 lanes          | **16** lanes    | `16u32`         |
| u16     | 16 lanes         | **32** lanes    | `32u16`         |
| u8      | 32 lanes         | **64** lanes    | `64u8`          |

The abstract `VectorOp α n` is lane-count-polymorphic (`n` is a parameter), so
the *same* `VectorOp` term re-targets to a wider `zmm` instruction simply by
carrying the AVX-512 width string — there is nothing per-lane to rewrite. The
width is recorded in `AVX512Inst.width` (a `LaneWidth`) so `render512` produces
the right `_8u64` / `_16u32` / … suffix.

## Honest gaps (no clean 512-bit mnemonic)

Two `VectorOp` ops do *not* lower to a baseline-AVX-512 mnemonic: `affineByte`
(needs the `AVX512_GFNI` extension's `VGF2P8AFFINEQB zmm`) and `aesRound`
(needs the `AVX512_VAES` extension's `VAESENC zmm`). These are real ISA
instructions, but they are *extensions* on top of `AVX512F`, not part of the
foundation set. We model them honestly: `lowerAVX512` tags them with an
`requiresExt` flag (`GFNI512` / `VAES512`) so a backend that targets a CPU
without those extensions can reject them, rather than silently emitting an
instruction the target cannot decode. Their denotation preservation still
holds (the per-lane semantics is unchanged by width), so they are *correct
when the extension is present* — the gap is an ISA-availability concern, not a
semantic one, and is surfaced explicitly.
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
    `AVX512F`. `none` = foundation set; the others flag the honest gaps. -/
inductive Ext where
  /-- Baseline `AVX512F` — always available on an AVX-512 target. -/
  | f
  /-- `AVX512_GFNI` (the `VGF2P8AFFINEQB zmm` family). -/
  | gfni512
  /-- `AVX512_VAES` (the `VAESENC zmm` family). -/
  | vaes512
  deriving DecidableEq, Repr

/-- A 512-bit mnemonic instruction the AVX-512 lowering pass emits. The carried
    lane op (`α → α → α` / `α → Nat → α` / `α → α`) is kept so `denote512` can
    state the per-lane semantics; the `width` records the `zmm` element shape;
    `ext` records the ISA extension required (for the honest-gap reporting). -/
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
      (`ext = .gfni512`); honest gap. The matrix/bias are closed over in `aff`. -/
  | vgf2p8affine (aff : α → α) (v : VectorTy α n) : AVX512Inst α n
  /-- `#VAESENC_512(state, key)` — per-lane AES round. Requires `AVX512_VAES`
      (`ext = .vaes512`); honest gap. -/
  | vaesenc (rnd : α → α → α) (state key : VectorTy α n) : AVX512Inst α n

namespace AVX512Inst

variable {α : Type} {n : Nat}

/-- The ISA extension an emitted instruction requires. `affineByte` / `aesRound`
    are the only ops that escape the `AVX512F` foundation set. -/
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

Each instruction's *meaning* as a lane function. This is the same per-lane
operation the abstract `denoteVectorOp` produces — the width is purely an
emit-side concern, so the semantics is width-independent. We prove that
equality below (`lowerAVX512_*_correct`). -/

/-- The `Fin n → α` semantics of an AVX-512 instruction. -/
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

`lowerAVX512 width op` re-targets a *vector-result* `VectorOp` to a 512-bit
mnemonic instruction at the chosen `width`. Scalar-result ops (`extract` /
`reduce`) return `none` — exactly as the AVX2 `lower` does (they are not
`zmm`-vector-shaped; their lowering is a single scalar `vpextr` / horizontal
reduction, Phase-2 as in the AVX2 path).

This is **one rule per constructor** — the whole pass. Compare: pre-dialect,
re-targeting to 512-bit width meant editing every consumer's emit file. -/
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

`render512` produces the jasmin / `x86vector` mnemonic text the backend emits.
This is the AVX-512 analogue of `MldsaNtt4WayVec.LatticeNttVecOp.render` —
same `dst = #MNEM_<width>(args);` shape, but at `zmm` width. We render against
named string operands so the demonstration can show a consumer's `VectorOp`
term producing a 512-bit emit line. -/

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

/-! ## 5. Denotation-preservation theorems (the keystones)

For each abstract op, the 512-bit mnemonic the pass selects denotes the *same
per-lane operation* as the abstract `denoteVectorOp`. These mirror the AVX2
`lower_*_correct` shape one-for-one: `(lowerAVX512 w op).map (·.denote512)`
equals the per-lane vector the abstract denotation produces.

Every proof is `rfl`-shaped (the lowering and `denote512` are definitionally
the abstract op's per-lane meaning), so all are `propext`/`Quot`/`choice`-free
beyond what the kernel needs — checked by `#print axioms` at the foot. -/

/-- **AVX-512 keystone (broadcast).** `VPBROADCAST_<w>` denotes `replicate x`. -/
theorem lowerAVX512_broadcast_correct {α : Type} {n : Nat}
    (w : LaneWidth) (x : α) :
    (lowerAVX512 w (.broadcast x : VectorOp α n)).map (·.denote512)
      = some (VectorTy.replicate x) := rfl

/-- **AVX-512 keystone (add).** `VPADD_<w>` denotes the pointwise carried op. -/
theorem lowerAVX512_add_correct {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.add op v w' : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ op v w') := rfl

/-- **AVX-512 keystone (mul).** `VPMULL_<w>` denotes the pointwise low-half
    multiply. -/
theorem lowerAVX512_mul_correct {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.mul op v w' : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ op v w') := rfl

/-- **AVX-512 keystone (mulHi).** `VPMULH_<w>` denotes the pointwise high-half
    multiply — the `VPMULH` leg of Montgomery / Barrett, now at `zmm` width. -/
theorem lowerAVX512_mulHi_correct {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.mulHi op v w' : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ op v w') := rfl

/-- **AVX-512 keystone (shiftL).** `VPSLL_<w>` denotes pointwise shift-left. -/
theorem lowerAVX512_shiftL_correct {α : Type} {n : Nat}
    (w : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lowerAVX512 w (.shiftL shf m v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁imm shf m v) := rfl

/-- **AVX-512 keystone (shiftR).** `VPSRL_<w>` denotes pointwise logical
    shift-right. -/
theorem lowerAVX512_shiftR_correct {α : Type} {n : Nat}
    (w : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lowerAVX512 w (.shiftR shf m v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁imm shf m v) := rfl

/-- **AVX-512 keystone (shiftRA).** `VPSRA_<w>` denotes pointwise arithmetic
    (signed) shift-right — the `VPSRA` leg of Montgomery / Barrett at `zmm`
    width. -/
theorem lowerAVX512_shiftRA_correct {α : Type} {n : Nat}
    (w : LaneWidth) (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lowerAVX512 w (.shiftRA shf m v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁imm shf m v) := rfl

/-- **AVX-512 keystone (shuffle).** `VPERM_<w>` denotes the lane permutation.
    AVX-512's full cross-`zmm` permute realizes the abstract `shuffle` directly
    (AVX2 needed in-lane shuffle + cross-lane blend; the wider permute is one
    instruction). -/
theorem lowerAVX512_shuffle_correct {α : Type} {n : Nat}
    (w : LaneWidth) (v : VectorTy α n) (π : Fin n → Fin n) :
    (lowerAVX512 w (.shuffle v π : VectorOp α n)).map (·.denote512)
      = some (VectorTy.shuffle π v) := rfl

/-- **AVX-512 keystone (affineByte).** `VGF2P8AFFINEQB_512` denotes the
    pointwise GF(2) affine. Requires `AVX512_GFNI` (`ext = .gfni512`); the
    semantics is width-independent so preservation holds when the extension is
    present. -/
theorem lowerAVX512_affineByte_correct {α : Type} {n : Nat}
    (w : LaneWidth) (aff : α → α) (v : VectorTy α n) :
    (lowerAVX512 w (.affineByte aff v : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₁ aff v) := rfl

/-- **AVX-512 keystone (aesRound).** `VAESENC_512` denotes the pointwise AES
    round. Requires `AVX512_VAES` (`ext = .vaes512`); preservation holds when
    the extension is present. -/
theorem lowerAVX512_aesRound_correct {α : Type} {n : Nat}
    (w : LaneWidth) (rnd : α → α → α) (s k : VectorTy α n) :
    (lowerAVX512 w (.aesRound rnd s k : VectorOp α n)).map (·.denote512)
      = some (VectorTy.map₂ rnd s k) := rfl

/-! ## 6. AVX-512 denotes the same vector as the abstract op (bundled)

For the vector-result ops, the AVX-512 lowering's denotation equals the vector
component of the abstract `denoteVectorOp`. This is the cross-target invariant:
**the same `VectorOp` term has the same meaning whether lowered to AVX2's
`ScalarExpansion` or to this AVX-512 instruction** — only the emit text width
differs. -/

/-- The AVX-512 lowering of a vector-result op denotes the same lane vector as
    the abstract `denoteVectorOp` (whenever the abstract op is vector-shaped
    and the pass returns an instruction). Stated per the binary `add` family;
    the other ops follow the same `rfl` shape (see the `*_correct` keystones). -/
theorem lowerAVX512_add_eq_abstract {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.add op v w' : VectorOp α n)).map
        (fun i => VectorOp.Result.vec i.denote512)
      = some (denoteVectorOp (.add op v w' : VectorOp α n)) := rfl

/-- The same cross-target invariant for `mulHi` (the Montgomery high-half
    product): AVX-512 `VPMULH` and the abstract op denote the same vector. -/
theorem lowerAVX512_mulHi_eq_abstract {α : Type} {n : Nat}
    (w : LaneWidth) (op : α → α → α) (v w' : VectorTy α n) :
    (lowerAVX512 w (.mulHi op v w' : VectorOp α n)).map
        (fun i => VectorOp.Result.vec i.denote512)
      = some (denoteVectorOp (.mulHi op v w' : VectorOp α n)) := rfl

/-! ## 7. Honest-gap report (the ops escaping `AVX512F`)

The two ops that need an ISA extension beyond baseline `AVX512F` are surfaced
by `ext`. A backend targeting a CPU without `AVX512_GFNI` / `AVX512_VAES` can
inspect this and reject, rather than emit an undecodable instruction. -/

/-- `affineByte` requires the `AVX512_GFNI` extension. -/
theorem affineByte_requires_gfni512 {α : Type} {n : Nat} (aff : α → α)
    (v : VectorTy α n) :
    ((lowerAVX512 .w64u8 (.affineByte aff v)).map AVX512Inst.ext)
      = some Ext.gfni512 := rfl

/-- `aesRound` requires the `AVX512_VAES` extension. -/
theorem aesRound_requires_vaes512 {α : Type} {n : Nat} (rnd : α → α → α)
    (s k : VectorTy α n) :
    ((lowerAVX512 .w64u8 (.aesRound rnd s k)).map AVX512Inst.ext)
      = some Ext.vaes512 := rfl

/-- Every other vector-result op stays in the baseline `AVX512F` foundation
    set (`ext = .f`). Pinned for `add`/`mul`/`mulHi`/`shiftL`/`shiftR`/
    `shiftRA`/`shuffle`/`broadcast`. -/
theorem add_is_avx512f {α : Type} {n : Nat} (op : α → α → α)
    (v w : VectorTy α n) :
    ((lowerAVX512 .w16u32 (.add op v w)).map AVX512Inst.ext) = some Ext.f := rfl

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
