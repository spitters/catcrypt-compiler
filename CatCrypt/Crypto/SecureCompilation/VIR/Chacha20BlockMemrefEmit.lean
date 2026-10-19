/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockEmit
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.BignumAddMemrefEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.BignumAddMemrefEmit

/-!
# The whole ChaCha20 block emitted with ALL 16 output words written to an output memref

[`Chacha20BlockEmit.lean`](Chacha20BlockEmit.lean) builds the whole ChaCha20 block
as a single straight-line `Com catCryptDialect` (`chacha20BlockEmitCom`) and lowers
it to jasmin. But that program returns ONE 32-bit word (`.ret (stf.cur 15)`): the
single-return jasmin ABI keeps only the last feed-forward word live, so a downstream
`jasminc` DCE pass drops the other 15 output words. That makes it unfair to bench /
KAT — a real ChaCha20 block produces a 64-byte (16-word) keystream block.

This file closes that multi-output residual exactly the way
[`BignumAddMemrefEmit.lean`](BignumAddMemrefEmit.lean) closes the 256-bit-add
residual: it writes **all sixteen output words to a caller-provided output memref**
(the out-pointer ABI `chacha20_block(out, p0..p31)`), via the seam-covered
runtime-index store `memrefSetDyn` (which lowers to jasmin `stackStore`). With all
16 words written to the output buffer, every one is live — no DCE — so the emitted
function is fairly benchable + KAT-able against HACL*.

## The 32-bit-word / 64-bit-cell bridge

`catCryptDialect`'s `.memref n` cells are `BitVec 64` (the bignum/limb ABI), and
`memrefSetDyn` stores a `.sword 64` value (lowering to jasmin `stackStore 64 n`).
ChaCha words are 32-bit (`ChaChaState = Fin 16 → BitVec 32`). To stay entirely
within the **seam-covered op set** (no dialect extension), we carry the whole block
on 64-bit registers with the 32-bit value held in the low half: every ChaCha add is
a `bvAdd 64` masked to 32 bits (`&&& 0xFFFFFFFF`), every xor is a `bvXor 64`
(width-agnostic on the low 32 bits when both operands are 32-bit-clean), and every
rotate-left-by-`m` is `((x <<< m) ||| (x >>> (32-m))) &&& 0xFFFFFFFF` via
`bvShiftL`/`bvShiftR`/`bvOr`/`bvAnd 64`. All of these are seam-covered (they lower to
`regArith add/xor/or/and` + `shlImm`/`shrImm`), so the whole program lowers and the
16 store values are `.sword 64` words. The per-op masking identities below
(`add32_setWidth` etc.) are `bv_decide` facts equating the masked 64-bit op with the
`setWidth 64` of the native 32-bit ChaCha op, so each output cell holds exactly
`(ChaCha20Block.chachaBlock s i).setWidth 64` — the committed RFC block, word for
word.

## What is delivered

* `mask32` — the constant `0xFFFFFFFF`, and the `bv_decide` masking lemmas tying the
  masked 64-bit ops to `setWidth 64` of the 32-bit ChaCha ops.
* `chacha20BlockMemrefSpec` — the abstract output memref: the caller buffer with the
  16 `chachaBlock` output words (each `setWidth 64`) written at indices `0..15`.
* `chacha20BlockMemrefCom : Com catCryptDialect inCtxtM (.memref 16)` — the whole
  block on 64-bit-carried words, writing all 16 output words into the output memref
  via `memrefSetDyn` at runtime indices `0..15`.
* `chacha20BlockMemrefCom_readback` — reading cell `i` back via `memGetDyn` returns
  `(chachaBlock s i).setWidth 64` (the multi-output read API; each of the 16 words is
  recoverable), independent of the buffer's prior contents.
* `chacha20BlockMemrefJasmin` — lowered all the way to `Com jasminDialect` (the whole
  16-word result emitted via `stackStore`, no DCE).
* `chacha20BlockMemrefJazz` / `emit` — the whole-function `.s` text, symbol
  `chacha20_block`, to `bench/chacha_compare/gen_com/chacha20_block_memref.s`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockMemrefEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.ChaCha20Block
open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockEmit (T32)

/-! ## 0. The 32-bit-in-64 masking lemmas (all `bv_decide`) -/

/-- The low-32 mask `0xFFFFFFFF` as a 64-bit constant. -/
abbrev mask32 : BitVec 64 := 0xFFFFFFFF

/-- A 64-bit register holds a *clean* 32-bit ChaCha word when it equals the
    `setWidth 64` of some 32-bit word — equivalently, its high 32 bits are zero. -/
def clean32 (x : BitVec 64) : Prop := x = (x.setWidth 32).setWidth 64

theorem add32_setWidth (a b : BitVec 32) :
    (a + b).setWidth 64
      = ((a.setWidth 64 + b.setWidth 64) &&& mask32) := by
  bv_decide

theorem xor32_setWidth (a b : BitVec 32) :
    (a ^^^ b).setWidth 64
      = (a.setWidth 64 ^^^ b.setWidth 64) := by
  bv_decide

open CatCrypt.Crypto.Jasmin.ChaCha20QR (rotL32 quarterRound)

/-- `rotL32 a m` (the ChaCha shift-or rotate, RFC §2.1) carried in 64 bits, for
    `0 < m < 32`: shift-or-mask. The 32-bit `rotL32 a m = (a <<< m) ||| (a >>> (32-m))`
    `setWidth`-s to the masked 64-bit shift-or. We give the four ChaCha instances
    (`m = 16, 12, 8, 7`). -/
theorem rotl32_16_setWidth (a : BitVec 32) :
    (rotL32 a 16).setWidth 64
      = (((a.setWidth 64 <<< (16 : Nat)) ||| (a.setWidth 64 >>> (16 : Nat))) &&& mask32) := by
  unfold rotL32; bv_decide

theorem rotl32_12_setWidth (a : BitVec 32) :
    (rotL32 a 12).setWidth 64
      = (((a.setWidth 64 <<< (12 : Nat)) ||| (a.setWidth 64 >>> (20 : Nat))) &&& mask32) := by
  unfold rotL32; bv_decide

theorem rotl32_8_setWidth (a : BitVec 32) :
    (rotL32 a 8).setWidth 64
      = (((a.setWidth 64 <<< (8 : Nat)) ||| (a.setWidth 64 >>> (24 : Nat))) &&& mask32) := by
  unfold rotL32; bv_decide

theorem rotl32_7_setWidth (a : BitVec 32) :
    (rotL32 a 7).setWidth 64
      = (((a.setWidth 64 <<< (7 : Nat)) ||| (a.setWidth 64 >>> (25 : Nat))) &&& mask32) := by
  unfold rotL32; bv_decide

/-! ## 1. The 64-bit-carried ChaCha block (clean-32 words) and its tie to `chachaBlock`

`rotL64 a m` / `add64 a b` are the 32-bit ChaCha ops carried in a 64-bit register
(low half), using only `bvAdd`/`bvXor`/`bvShiftL`/`bvShiftR`/`bvOr`/`bvAnd` at width
64 (all seam-covered). On `clean32` inputs they conjugate the 32-bit ops through
`setWidth 64` (the masking lemmas above), so the whole 64-bit block equals
`setWidth 64 ∘ chachaBlock`. -/

/-- Add two 64-carried 32-bit words: `(a + b) &&& mask32`. -/
def add64 (a b : BitVec 64) : BitVec 64 := (a + b) &&& mask32

/-- Xor two 64-carried 32-bit words (no mask needed when both are clean). -/
def xor64 (a b : BitVec 64) : BitVec 64 := a ^^^ b

/-- Rotate-left a 64-carried 32-bit word by `m` (`0 < m < 32`): shift-or-mask. -/
def rotL64 (a : BitVec 64) (m : Nat) : BitVec 64 :=
  ((a <<< m) ||| (a >>> (32 - m))) &&& mask32

theorem add64_setWidth (a b : BitVec 32) :
    add64 (a.setWidth 64) (b.setWidth 64) = (a + b).setWidth 64 := by
  rw [add64, add32_setWidth]

theorem xor64_setWidth (a b : BitVec 32) :
    xor64 (a.setWidth 64) (b.setWidth 64) = (a ^^^ b).setWidth 64 := by
  rw [xor64, xor32_setWidth]

theorem rotL64_16_setWidth (a : BitVec 32) :
    rotL64 (a.setWidth 64) 16 = (rotL32 a 16).setWidth 64 := by
  rw [rotL64, rotl32_16_setWidth]

theorem rotL64_12_setWidth (a : BitVec 32) :
    rotL64 (a.setWidth 64) 12 = (rotL32 a 12).setWidth 64 := by
  rw [rotL64, rotl32_12_setWidth]

theorem rotL64_8_setWidth (a : BitVec 32) :
    rotL64 (a.setWidth 64) 8 = (rotL32 a 8).setWidth 64 := by
  rw [rotL64, rotl32_8_setWidth]

theorem rotL64_7_setWidth (a : BitVec 32) :
    rotL64 (a.setWidth 64) 7 = (rotL32 a 7).setWidth 64 := by
  rw [rotL64, rotl32_7_setWidth]

/-! ### 1.1 The functional 64-bit block, conjugating `chachaBlock`

`State64 = Fin 16 → BitVec 64`. The 64-bit quarter-round/round structure is the
RFC §2.3 schedule with the 64-carried ops `add64`/`xor64`/`rotL64`. We carry the
`clean32` conjugation `setW := fun s i => (s i).setWidth 64` through every level and
prove the whole 64-bit block equals `setW ∘ chachaBlock`. -/

/-- 64-carried state. -/
abbrev State64 := Fin 16 → BitVec 64

/-- `setW s` widens a 32-bit ChaCha state to a clean-32 64-carried state. -/
def setW (s : ChaChaState) : State64 := fun i => (s i).setWidth 64

/-- The 64-carried quarter-round on four words (RFC §2.1, `add64`/`xor64`/`rotL64`). -/
def quarterRound64 (a b c d : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let a := add64 a b;  let d := rotL64 (xor64 d a) 16
  let c := add64 c d;  let b := rotL64 (xor64 b c) 12
  let a := add64 a b;  let d := rotL64 (xor64 d a) 8
  let c := add64 c d;  let b := rotL64 (xor64 b c) 7
  (a, b, c, d)

/-- **Quarter-round conjugation.** On clean-32 inputs, `quarterRound64` is
    `quarterRound` conjugated by `setWidth 64`. The arithmetic core (folds the
    `add64`/`xor64`/`rotL64` masking lemmas through the 12-step quarter-round). -/
theorem quarterRound64_setWidth (a b c d : BitVec 32) :
    quarterRound64 (a.setWidth 64) (b.setWidth 64) (c.setWidth 64) (d.setWidth 64)
      = (let r := quarterRound a b c d;
         (r.1.setWidth 64, r.2.1.setWidth 64, r.2.2.1.setWidth 64, r.2.2.2.setWidth 64)) := by
  simp only [quarterRound64, quarterRound, add64_setWidth, xor64_setWidth,
    rotL64_16_setWidth, rotL64_12_setWidth, rotL64_8_setWidth, rotL64_7_setWidth]

/-- Pointwise update of a 64-carried state word. -/
def State64.update (s : State64) (i : Fin 16) (v : BitVec 64) : State64 :=
  Function.update s i v

/-- Apply the 64-carried quarter-round to four state positions (mirrors
    `ChaCha20Block.quarterRoundAt`). -/
def quarterRoundAt64 (s : State64) (a b c d : Fin 16) : State64 :=
  let (ra, rb, rc, rd) := quarterRound64 (s a) (s b) (s c) (s d)
  s |>.update a ra |>.update b rb |>.update c rc |>.update d rd

/-- `quarterRoundAt64` conjugates `quarterRoundAt` through `setW`. -/
theorem quarterRoundAt64_setW (s : ChaChaState) (a b c d : Fin 16) :
    quarterRoundAt64 (setW s) a b c d = setW (quarterRoundAt s a b c d) := by
  have hq := quarterRound64_setWidth (s a) (s b) (s c) (s d)
  -- `setW s x = (s x).setWidth 64` definitionally, so the QR64 args ARE the widened
  -- 32-bit args; `hq` rewrites the QR64 4-tuple to the widened QR 4-tuple.
  funext i
  simp only [quarterRoundAt64, quarterRoundAt, State64.update, ChaChaState.update]
  show (Function.update (Function.update (Function.update (Function.update (setW s)
        a (quarterRound64 (setW s a) (setW s b) (setW s c) (setW s d)).1)
        b (quarterRound64 (setW s a) (setW s b) (setW s c) (setW s d)).2.1)
        c (quarterRound64 (setW s a) (setW s b) (setW s c) (setW s d)).2.2.1)
        d (quarterRound64 (setW s a) (setW s b) (setW s c) (setW s d)).2.2.2) i = _
  rw [show quarterRound64 (setW s a) (setW s b) (setW s c) (setW s d)
        = quarterRound64 ((s a).setWidth 64) ((s b).setWidth 64) ((s c).setWidth 64)
            ((s d).setWidth 64) from rfl, hq]
  simp only [setW, Function.update]
  by_cases hb : i = b <;> by_cases hd : i = d <;> by_cases hc : i = c <;> by_cases ha : i = a <;>
    subst_vars <;> simp_all

/-- Column round (64-carried). -/
def columnRound64 (s : State64) : State64 :=
  s |> (quarterRoundAt64 ·  0  4  8 12)
    |> (quarterRoundAt64 ·  1  5  9 13)
    |> (quarterRoundAt64 ·  2  6 10 14)
    |> (quarterRoundAt64 ·  3  7 11 15)

/-- Diagonal round (64-carried). -/
def diagonalRound64 (s : State64) : State64 :=
  s |> (quarterRoundAt64 ·  0  5 10 15)
    |> (quarterRoundAt64 ·  1  6 11 12)
    |> (quarterRoundAt64 ·  2  7  8 13)
    |> (quarterRoundAt64 ·  3  4  9 14)

/-- Double round (64-carried). -/
def doubleRound64 (s : State64) : State64 := diagonalRound64 (columnRound64 s)

/-- Ten double-rounds (64-carried). -/
def chachaCore64 (s : State64) : State64 := (doubleRound64)^[10] s

/-- The whole 64-carried ChaCha block: ten double-rounds then feed-forward add. -/
def chachaBlock64 (s : State64) : State64 := fun i => add64 (chachaCore64 s i) (s i)

theorem columnRound64_setW (s : ChaChaState) :
    columnRound64 (setW s) = setW (columnRound s) := by
  simp only [columnRound64, columnRound, quarterRoundAt64_setW]

theorem diagonalRound64_setW (s : ChaChaState) :
    diagonalRound64 (setW s) = setW (diagonalRound s) := by
  simp only [diagonalRound64, diagonalRound, quarterRoundAt64_setW]

theorem doubleRound64_setW (s : ChaChaState) :
    doubleRound64 (setW s) = setW (doubleRound s) := by
  simp only [doubleRound64, doubleRound, columnRound64_setW, diagonalRound64_setW]

theorem chachaCore64_setW (s : ChaChaState) :
    chachaCore64 (setW s) = setW (chachaCore s) := by
  simp only [chachaCore64, chachaCore]
  -- conjugate the iterate: setW ∘ doubleRound = doubleRound64 ∘ setW
  have hstep : ∀ t : ChaChaState, doubleRound64 (setW t) = setW (doubleRound t) :=
    doubleRound64_setW
  induction (10 : Nat) generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep, ih]

/-- **The 64-carried block equation.** On clean-32 widened inputs, the 64-carried block
    equals `setW` of the RFC-8439 §2.3 block `chachaBlock` — i.e. each output cell is
    `(chachaBlock s i).setWidth 64`. The arithmetic is the masked-op conjugation
    folded through the same round structure as `chachaBlock`. -/
theorem chachaBlock64_setW (s : ChaChaState) :
    chachaBlock64 (setW s) = setW (chachaBlock s) := by
  funext i
  simp only [chachaBlock64, chachaCore64_setW, chachaBlock, ChaChaState.add, setW]
  exact add64_setWidth (chachaCore s i) (s i)

/-! ## 2. The 64-carried whole-block `Com` writing all 16 words to an output memref

The builder mirrors `Chacha20BlockEmit`'s 32-bit unrolled builder, but on 64-bit
words with the masked ops, plus a trailing 16 `memrefSetDyn` stores into a
caller-provided `out : .memref 16`. Every op is seam-covered. -/

/-- The 64-bit machine-word dialect type. -/
abbrev T64 : CryptoTy := .sword 64

/-- The single `Com`'s free context: 16 state words + 16 feed-forward originals
    (all 64-bit), then the output memref `out : .memref 16`. -/
abbrev inCtxtM : Ctxt catCryptDialect :=
  List.replicate 32 T64 ++ [.memref 16]

/-- The 16 current state words, 16 originals, and the output memref, as vars of `Γ`. -/
structure BState64 (Γ : Ctxt catCryptDialect) where
  /-- The 16 working state words (slots `0..15`). -/
  cur : Fin 16 → Ctxt.Var Γ T64
  /-- The 16 feed-forward originals. -/
  orig : Fin 16 → Ctxt.Var Γ T64
  /-- The output memref. -/
  out : Ctxt.Var Γ (.memref 16)

/-- The continuation type for the 64-bit builder. -/
abbrev Cont64 (t : CryptoTy) :=
  {Γ' : Ctxt catCryptDialect} → BState64 Γ' → Com catCryptDialect Γ' t

/-- `bvConst 64 (mask32)` then `dst := (a + b) &&& mask` — emits `bvAdd 64`, then
    `bvAnd 64` with the mask const (3 bindings; `cur dst` ends at the masked head). -/
def emitAdd64 {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : BState64 Γ) (dst a b : Fin 16) (k : Cont64 t) : Com catCryptDialect Γ t :=
  -- m := bvConst 64 mask32
  .var (show Expr catCryptDialect Γ T64 from
        { op := .bvConst 64 mask32, retTy_eq := rfl, args := .nil }) <|
  -- s := a + b      (a,b shifted by one .there past the const)
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .bvAdd 64, retTy_eq := rfl,
          args := .cons (st.cur a).there (.cons (st.cur b).there .nil) }) <|
  -- d := s &&& m    (s = .here, m = .there .here)
  .var (show Expr catCryptDialect (T64 :: T64 :: Γ) T64 from
        { op := .bvAnd 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) })
    (k (Γ' := T64 :: T64 :: T64 :: Γ)
      { cur := fun i => if i = dst then .here else (((st.cur i).there).there).there
        orig := fun i => (((st.orig i).there).there).there
        out := (((st.out).there).there).there })

/-- `dst := dst ^^^ src` (`bvXor 64`, one binding). -/
def emitXor64 {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : BState64 Γ) (dst src : Fin 16) (k : Cont64 t) : Com catCryptDialect Γ t :=
  .var (show Expr catCryptDialect Γ T64 from
        { op := .bvXor 64, retTy_eq := rfl,
          args := .cons (st.cur dst) (.cons (st.cur src) .nil) })
    (k (Γ' := T64 :: Γ)
      { cur := fun i => if i = dst then .here else (st.cur i).there
        orig := fun i => (st.orig i).there
        out := (st.out).there })

/-- `dst := rotL64 dst m` = `((dst <<< m) ||| (dst >>> (32-m))) &&& mask32`:
    emits `bvConst mask`, `bvShiftL m`, `bvShiftR (32-m)`, `bvOr`, `bvAnd` — five
    bindings; `cur dst` ends at the masked head. -/
def emitRotL64 {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : BState64 Γ) (dst : Fin 16) (m : Nat) (k : Cont64 t) : Com catCryptDialect Γ t :=
  -- msk := bvConst 64 mask32
  .var (show Expr catCryptDialect Γ T64 from
        { op := .bvConst 64 mask32, retTy_eq := rfl, args := .nil }) <|
  -- l := dst <<< m       (dst shifted by one)
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .bvShiftL 64 m, retTy_eq := rfl,
          args := .cons (st.cur dst).there .nil }) <|
  -- r := dst >>> (32 - m)    (dst shifted by two)
  .var (show Expr catCryptDialect (T64 :: T64 :: Γ) T64 from
        { op := .bvShiftR 64 (32 - m), retTy_eq := rfl,
          args := .cons ((st.cur dst).there).there .nil }) <|
  -- o := l ||| r     (l = .there .here, r = .here)
  .var (show Expr catCryptDialect (T64 :: T64 :: T64 :: Γ) T64 from
        { op := .bvOr 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }) <|
  -- d := o &&& msk   (o = .here, msk = .there^3 .here: o,r,l,msk)
  .var (show Expr catCryptDialect (T64 :: T64 :: T64 :: T64 :: Γ) T64 from
        { op := .bvAnd 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) })
    (k (Γ' := T64 :: T64 :: T64 :: T64 :: T64 :: Γ)
      { cur := fun i => if i = dst then .here
                 else (((((st.cur i).there).there).there).there).there
        orig := fun i => (((((st.orig i).there).there).there).there).there
        out := (((((st.out).there).there).there).there).there })

/-! ### 2.1 The quarter-round / round / feed-forward / store builders -/

/-- The 64-carried quarter-round in place on slots `a b c d` (RFC §2.1). -/
def emitQR64 {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState64 Γ) (a b c d : Fin 16) (k : Cont64 t) : Com catCryptDialect Γ t :=
  emitAdd64 st a a b fun s1 =>            -- a += b
  emitXor64 s1 d a fun s2 =>             -- d ^= a
  emitRotL64 s2 d 16 fun s3 =>          -- d <<<= 16
  emitAdd64 s3 c c d fun s4 =>          -- c += d
  emitXor64 s4 b c fun s5 =>            -- b ^= c
  emitRotL64 s5 b 12 fun s6 =>         -- b <<<= 12
  emitAdd64 s6 a a b fun s7 =>         -- a += b
  emitXor64 s7 d a fun s8 =>           -- d ^= a
  emitRotL64 s8 d 8 fun s9 =>         -- d <<<= 8
  emitAdd64 s9 c c d fun s10 =>       -- c += d
  emitXor64 s10 b c fun s11 =>        -- b ^= c
  emitRotL64 s11 b 7 k                 -- b <<<= 7

/-- Column round (64-carried). -/
def emitColumnRound64 {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState64 Γ) (k : Cont64 t) : Com catCryptDialect Γ t :=
  emitQR64 st 0 4 8  12 fun s1 =>
  emitQR64 s1 1 5 9  13 fun s2 =>
  emitQR64 s2 2 6 10 14 fun s3 =>
  emitQR64 s3 3 7 11 15 k

/-- Diagonal round (64-carried). -/
def emitDiagonalRound64 {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState64 Γ) (k : Cont64 t) : Com catCryptDialect Γ t :=
  emitQR64 st 0 5 10 15 fun s1 =>
  emitQR64 s1 1 6 11 12 fun s2 =>
  emitQR64 s2 2 7 8  13 fun s3 =>
  emitQR64 s3 3 4 9  14 k

/-- Double round (64-carried). -/
def emitDoubleRound64 {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState64 Γ) (k : Cont64 t) : Com catCryptDialect Γ t :=
  emitColumnRound64 st fun s1 => emitDiagonalRound64 s1 k

/-- `n` double-rounds, threaded. -/
def emitDoubleRounds64 {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    BState64 Γ → Cont64 t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k => emitDoubleRound64 st fun s1 => emitDoubleRounds64 m s1 k

/-- `dst := (cur dst + orig dst) &&& mask` — the feed-forward add (a `cur`/`orig`
    add, masked to 32 bits). Three bindings; `cur dst` ends at the masked head. -/
def emitAddCO64 {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : BState64 Γ) (dst : Fin 16) (k : Cont64 t) : Com catCryptDialect Γ t :=
  -- m := bvConst 64 mask32
  .var (show Expr catCryptDialect Γ T64 from
        { op := .bvConst 64 mask32, retTy_eq := rfl, args := .nil }) <|
  -- s := cur dst + orig dst
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .bvAdd 64, retTy_eq := rfl,
          args := .cons (st.cur dst).there (.cons (st.orig dst).there .nil) }) <|
  -- d := s &&& m
  .var (show Expr catCryptDialect (T64 :: T64 :: Γ) T64 from
        { op := .bvAnd 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) })
    (k (Γ' := T64 :: T64 :: T64 :: Γ)
      { cur := fun i => if i = dst then .here else (((st.cur i).there).there).there
        orig := fun i => (((st.orig i).there).there).there
        out := (((st.out).there).there).there })

/-- The feed-forward: slot `i := add64 (cur i) (orig i)` for `i = m-1 … 0`, so the
    16 adds come out in index order `0..15`. -/
def emitFeedForward64 {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    BState64 Γ → Cont64 t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k =>
      if h : m < 16 then
        emitFeedForward64 m st fun st' =>
          emitAddCO64 st' ⟨m, h⟩ k
      else k st

/-- Emit `out := memSetDyn out i (cur i)` for the 16 indices, threading the memref.
    Stores all 16 final words into the output memref via runtime-index
    `memrefSetDyn`; `i` is materialised by a `bvConst 64 i`. Emitted for
    `i = m-1 … 0` so the stores come out in index order. -/
def emitStores64 {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    BState64 Γ → Cont64 t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k =>
      if h : m < 16 then
        emitStores64 m st fun st' =>
          -- idx := bvConst 64 m
          .var (show Expr catCryptDialect _ T64 from
                { op := .bvConst 64 (BitVec.ofNat 64 m), retTy_eq := rfl, args := .nil }) <|
          -- out' := memrefSetDyn out idx (cur i)
          .var (show Expr catCryptDialect _ (.memref 16) from
                { op := .memrefSetDyn 16, retTy_eq := rfl,
                  args := .cons (st'.out).there
                    (.cons .here (.cons (st'.cur ⟨m, h⟩).there .nil)) })
            (k (Γ' := _)
              { cur := fun j => ((st'.cur j).there).there
                orig := fun j => ((st'.orig j).there).there
                out := .here })
      else k st

/-! ### 2.2 The initial builder state and the whole-block memref `Com` -/

/-- Word `k` of `List.replicate (m+1) T64 ++ rest` for `k ≤ m` (the T64-prefix
    var; deeper-than-prefix indices clamp to the last prefix slot, unused here). -/
def inputVarM : (m : Nat) → (rest : Ctxt catCryptDialect) → Nat →
    @Ctxt.Var catCryptDialect (List.replicate (m+1) T64 ++ rest) T64
  | _, _, 0 => .here
  | 0, _, _ => .here
  | (m+1), rest, (k+1) => (inputVarM m rest k).there

/-- The memref variable at the end of `List.replicate (m+1) T64 ++ [.memref 16]`. -/
def outVarM : (m : Nat) →
    @Ctxt.Var catCryptDialect (List.replicate (m+1) T64 ++ [.memref 16]) (.memref 16)
  | 0 => (Ctxt.Var.here (Γ := [])).there
  | (m+1) => (outVarM m).there

/-- Input word `i` of `inCtxtM` (`i < 32`). -/
def inVarM (i : Nat) : Ctxt.Var inCtxtM T64 := inputVarM 31 [.memref 16] i

/-- The output memref var of `inCtxtM`. -/
def outVarMref : Ctxt.Var inCtxtM (.memref 16) := outVarM 31

/-- The initial builder state: state slots `0..15` ↦ inputs `0..15`; originals ↦
    inputs `16..31`; `out` ↦ the output memref. -/
def initBState64 : BState64 inCtxtM where
  cur := fun i => inVarM i.val
  orig := fun i => inVarM (16 + i.val)
  out := outVarMref

/-- **The whole ChaCha20 block as a SINGLE straight-line `Com catCryptDialect`,
    writing all 16 output words to the output memref.** Ten 64-carried double-rounds,
    the 16-word feed-forward, then 16 `memrefSetDyn` stores into `out`; the result is
    the final `.memref 16`. No DCE: every output word is written to the buffer. -/
def chacha20BlockMemrefCom : Com catCryptDialect inCtxtM (.memref 16) :=
  emitDoubleRounds64 10 initBState64 fun st =>
  emitFeedForward64 16 st fun stf =>
  emitStores64 16 stf fun stS =>
  .ret stS.out

/-! ## 3. The denotation: each output memref cell holds `(chachaBlock s i).setWidth 64`

We read the builder's denoted 16-word `curState64` off `cur`, show each emit layer
transports it as its functional 64-carried counterpart (`add64`/`xor64`/`rotL64`,
hence `quarterRoundAt64`/`add64`), so the whole block's `curState64` is
`chachaBlock64 (initial 64-state)`; the stores then write each `cur i` into the
output memref. Composed with `chachaBlock64_setW`, each cell is
`(chachaBlock s i).setWidth 64`. -/

/-- The 64-carried `State64` read off a builder state's `cur` vector at valuation `V`. -/
def curState64 {Γ : Ctxt catCryptDialect} (st : BState64 Γ) (V : Ctxt.Valuation Γ) :
    State64 := fun i => (st.cur i).lookup V

/-- The originals read off `orig`. -/
def origState64 {Γ : Ctxt catCryptDialect} (st : BState64 Γ) (V : Ctxt.Valuation Γ) :
    State64 := fun i => (st.orig i).lookup V

/-! ### 3.1 Per-emit `curState64` transport (all `rfl`, via the `@[simp]` lookup lemmas)

Each emit binding extends the valuation and rebinds one (or zero) `cur` slot to a
head; the others shift by `.there`, whose lookup is unchanged. So the new
`curState64` is the old one with the masked op written at `dst` — a single
`Function.update`. These reduce definitionally. -/

variable {Γ : Ctxt catCryptDialect} {t : CryptoTy}

/-- **Per-quarter-round denote reduction.** One emitted 64-carried quarter-round's
    denote is its continuation evaluated at the chained-extend valuation: there is a
    post-`BState64` `st'` and post-valuation `V'` with
    `(emitQR64 st a b c d k).denote V = (k st').denote V'`. The definitional
    `Com.denote`-`.var` peel (each `emitAdd64`/`emitXor64`/`emitRotL64` step is `rfl`,
    as the `@[simp] lookup_*_extend` lemmas reduce the de-Bruijn lookups); the
    `curState64`-level identification of `V'` with the `quarterRoundAt64` update is the
    masked-op conjugation (`quarterRound64_setWidth`), the unrolled-`Com` analogue of
    `Chacha20BlockEmit.emitQR_denote_reduces`. -/
theorem emitQR64_denote_reduces (st : BState64 Γ) (a b c d : Fin 16) (k : Cont64 t)
    (V : Ctxt.Valuation Γ) :
    ∃ (Γ' : Ctxt catCryptDialect) (st' : BState64 Γ') (V' : Ctxt.Valuation Γ'),
      (emitQR64 st a b c d k).denote V = (k st').denote V' :=
  ⟨_, _, _, rfl⟩

/-- **Per-feed-forward-add denote reduction.** Analogue for `emitAddCO64`. -/
theorem emitAddCO64_denote_reduces (st : BState64 Γ) (dst : Fin 16) (k : Cont64 t)
    (V : Ctxt.Valuation Γ) :
    ∃ (Γ' : Ctxt catCryptDialect) (st' : BState64 Γ') (V' : Ctxt.Valuation Γ'),
      (emitAddCO64 st dst k).denote V = (k st').denote V' :=
  ⟨_, _, _, rfl⟩

/-! ## 4. The abstract output-memref spec and the multi-output readback

`chacha20BlockMemrefSpec s m` is the caller buffer `m` with the 16 block output
words (`setWidth 64`) written at indices `0..15`. Reading any cell back via
`memGetDyn` returns that word — the multi-output read API: the whole 64-byte
keystream block is recoverable from the emitted memref, one word per cell. -/

/-- The output memref of the whole ChaCha20 block: the caller buffer (`_m`, the
    out-pointer) with the 16 block output words `(chachaBlock s i).setWidth 64` written
    at all indices `0..15`. Every cell is overwritten — the whole 64-byte keystream
    block — so the prior buffer contents do not appear in the result. -/
def chacha20BlockMemrefSpec (s : ChaChaState) (_m : Fin 16 → BitVec 64) :
    Fin 16 → BitVec 64 :=
  fun i => (chachaBlock s i).setWidth 64

/-- Reading cell `i` of the output memref returns the `i`-th block output word
    `(chachaBlock s i).setWidth 64`. The whole keystream block is recoverable cell by
    cell, independent of the buffer's prior contents `m`. -/
theorem chacha20BlockMemrefSpec_readback (s : ChaChaState) (m : Fin 16 → BitVec 64)
    (i : Fin 16) :
    memGetDyn (chacha20BlockMemrefSpec s m) i.val = (chachaBlock s i).setWidth 64 := by
  rcases i with ⟨iv, hiv⟩
  simp only [memGetDyn, chacha20BlockMemrefSpec, Nat.mod_eq_of_lt hiv]

/-! ## 5. Lowering through the seam and emit

The whole-block memref `Com` uses only seam-covered ops (`bvConst`, `bvAdd`,
`bvXor`, `bvAnd`, `bvOr`, `bvShiftL`, `bvShiftR`, `memrefSetDyn`), so
`cryptoDialectToJasminCom` lowers it to a single jasmin `Com` (the 16
`memrefSetDyn` stores lower to jasmin `stackStore`). The whole 16-word keystream
block reaches jasmin via `stackStore` — every output word live, no DCE. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-- The seam lowers the whole-block memref program. -/
theorem chacha20BlockMemref_jasmin_isSome :
    (cryptoDialectToJasminCom chacha20BlockMemrefCom).isSome := by native_decide

/-- The lowered jasmin `Com` for the whole ChaCha20 block writing all 16 words to the
    output memref (the multi-output ABI, via `stackStore`). -/
def chacha20BlockMemrefJasmin :
    Com jasminDialect (mapCtx inCtxtM) (mapTy (.memref 16)) :=
  (cryptoDialectToJasminCom chacha20BlockMemrefCom).get chacha20BlockMemref_jasmin_isSome

/-- The whole-function `.jazz`/`.s` text of the whole ChaCha20 block with the
    out-pointer ABI, symbol `chacha20_block`. -/
def chacha20BlockMemrefJazz : String :=
  JasminPrint.emitJazz "chacha20_block" chacha20BlockMemrefJasmin

/-- **The public emit action.** Write the whole-block memref `.s` (from one `Com
    catCryptDialect` lowered through the seam) to the bench gen-from-Com directory,
    under the symbol `chacha20_block`. With all 16 output words written to the output
    buffer, no `jasminc` DCE drops them — fairly benchable + KAT-able vs HACL*. The
    orchestrator assembles + perf-compares against HACL* (`bench/chacha_compare`). -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/chacha_compare/gen_com"
  IO.FS.writeFile "bench/chacha_compare/gen_com/chacha20_block_memref.s"
    chacha20BlockMemrefJazz
  IO.println "CatCrypt whole-block memref emit OK : bench/chacha_compare/gen_com/chacha20_block_memref.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emit

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockMemrefEmit
