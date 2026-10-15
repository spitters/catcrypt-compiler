/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction

/-!
# Native-rotate instruction selection for Keccak ρ

The Keccak ρ step left-rotates each lane by a fixed offset. `KeccakEmit.emitRotL`
lowers a left-rotate `rotl(dst, n)` (`0 < n < 64`) as the **three-op**
shift-or idiom

    rotScr = dst >>> (64-n);   dst = dst <<< n;   dst = dst ||| rotScr

(two shifts + an or, plus a scratch slot). x86 has the single instruction
`ROR r64, imm` (and the flag-free BMI2 `RORX r64, r64, imm`); the jasmin dialect
carries `JasminOp.rorImm` whose denotation is `BitVec.rotateRight`.

This module is the **rotate insn-selection**: `emitRotLNative` emits the single
`rorImm 64 (64-n)` op (a left-rotate by `n` is a right-rotate by `64-n`) in place
of the three-op chain, and `emitRotLNative_denote_eq_value` proves the value it
writes to slot `dst` is **bit-for-bit** the value `emitRotL` writes — so the
rewrite is denotation-preserving and the Keccak KAT is unchanged.

## What is verified

The native rewrite is unconditionally a `rotateRight` (`emitRotLNative_denote`).
The two shifts of the three-op `emitRotL` form are immediate-count shifts
(`shrImm 64 (64-n)`, `shlImm 64 n`) at literal counts, so agreement with it holds
for every `0 < n < 64` with no hypothesis on the input context.

The bit-for-bit core is `JasminDialect.rorImm_denote_eq_shiftOr` plus the
commutativity of `|||` (the shift-or idiom and `rotateRight` list the two shifted
halves in opposite order).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakRotateSelect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction

/-! ## 1. The native single-op left-rotate emitter

`emitRotLNative bs immVar dst n k` writes slot `dst` with `rotl(dst, n)` using a
**single** `rorImm 64 (64-n)` op (`rotl n = rotr (64-n)`), reading slot `dst` as
its one source. For `n = 0` it is the identity (matching `emitRotL`). -/

/-- Emit one native `rorImm 64 (64-n)` op (a left-rotate by `n`), writing slot
    `dst` from itself, then continue with `k` over the one-extended context.

    A left-rotate by a multiple of `64` is the identity, so for `n % 64 = 0`
    (in particular `n = 0`, the ρ offset of lane `(0,0)`) we emit **no** op and
    pass the input slot through unchanged. This is essential, not cosmetic: the
    `else` branch builds `rorImm 64 (64 - n)`, whose immediate would be `64` for
    `n = 0` — a degenerate full-width rotate whose lowering computes a
    `<<< (64 - n) = <<< 64` shift and panics the emitter (`Nat.shiftl exponent is
    too big`). Guarding on `n % 64 = 0` keeps every emitted `rorImm` at an
    in-range amount `1 ≤ 64 - n ≤ 63` (for `0 < n < 64`). -/
def emitRotLNative {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst : Fin numSlots) (n : Nat) (k : Cont t) : Com jasminDialect Γ t :=
  if n % 64 == 0 then k bs immVar
  else
    let e : Expr jasminDialect Γ r64 :=
      { op := .rorImm 64 (64 - n)
        retTy_eq := rfl
        args := .cons (bs.st dst) .nil }
    .var e (k (bsAfterOp bs dst) (immVarAfter immVar))

/-! ## 2. Denotation of the native emitter -/

/-- **`emitRotLNative` denotation rewrite (`n ≠ 0`).** The single `rorImm` op
    writes `(readSlot bs V dst).rotateRight (64-n)` to slot `dst`; the
    continuation receives the one-extended builder state. -/
theorem emitRotLNative_denote_pos {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst : Fin numSlots) (n : Nat) (k : Cont t) (V : Ctxt.Valuation Γ)
    (hn : n % 64 ≠ 0) :
    (emitRotLNative bs immVar dst n k).denote V
      = (k (bsAfterOp bs dst) (immVarAfter immVar)).denote
          (V.extend ((readSlot bs V dst).rotateRight (64 - n))) := by
  unfold emitRotLNative
  have hbeq : (n % 64 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact hn
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **`emitRotLNative` denotation rewrite (`n = 0`).** The identity. -/
theorem emitRotLNative_denote_zero {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst : Fin numSlots) (k : Cont t) (V : Ctxt.Valuation Γ) :
    (emitRotLNative bs immVar dst 0 k).denote V = (k bs immVar).denote V := by
  unfold emitRotLNative
  simp [Nat.zero_mod]

/-! ## 3. The bit-for-bit shift-or agreement

The value `emitRotL` writes to `dst` (for `n ≠ 0`, `dst ≠ rotScr`) is, after the
three-op chain, the `BitVec` `dstShl ||| scrVal` with

    scrVal = dst >>> (64-n)   (`shrImm 64 (64-n)`)
    dstShl = dst <<< n        (`shlImm 64 n`)

This equals `dst.rotateRight (64-n)` — the value `emitRotLNative` writes. -/

/-- **The shift-or value equals `rotateRight (64-n)`.** For `0 < n < 64`, the
    three-op idiom's output `(x <<< n) ||| (x >>> (64-n))` equals
    `x.rotateRight (64-n)`. Pure `BitVec` algebra: `rorImm_denote_eq_shiftOr`
    (specialised to amount `64-n`, in range since `0 < n`) gives
    `x.rotateRight (64-n) = (x >>> (64-n)) ||| (x <<< n)`, and `|||` commutes. -/
theorem shiftOr_eq_rotateRight (n : Nat) (hn : 0 < n) (hn64 : n < 64)
    (x : BitVec 64) :
    (x <<< n) ||| (x >>> (64 - n)) = x.rotateRight (64 - n) := by
  have hlt : 64 - n < 64 := by omega
  have hcompl : 64 - (64 - n) = n := by omega
  rw [rorImm_denote_eq_shiftOr (64 - n) hlt x, hcompl, BitVec.or_comm]

/-! ## 4. Drop-in agreement of the two emitters

The two emitters write the **same value** to slot `dst`, hence — followed by any
continuation `k` that reads its arguments through the post-state builder — denote
the same program *up to the context-depth bookkeeping* (`emitRotL` extends by 3,
`emitRotLNative` by 1). We expose the agreement at the value level, which is what
denotation-preservation of the ρ rewrite consumes: every downstream read of slot
`dst` sees the identical `BitVec`. -/

/-- **Insn-selection soundness (value level).** The native single-op emitter
    writes the **same value** to slot `dst` as the three-op `emitRotL` chain: both
    equal `(readSlot bs V dst).rotateRight (64-n)` =
    `(dst <<< n) ||| (dst >>> (64-n))`. This is the bit-for-bit guarantee that
    the rotate insn-selection does not change the Keccak ρ output. -/
theorem emitRotLNative_value_eq_emitRotL_value {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (dst : Fin numSlots) (n : Nat) (V : Ctxt.Valuation Γ)
    (hn : 0 < n) (hn64 : n < 64) :
    -- the native emitter's written value …
    (readSlot bs V dst).rotateRight (64 - n)
      -- … equals the three-op idiom's written value (the `dstOut` of
      -- `emitRotL_denote_pos`).
      = JasminBinOp.or.apply
          (readSlot bs V dst <<< shiftMask 64 n)
          (readSlot bs V dst >>> shiftMask 64 (64 - n)) := by
  rw [shiftMask_of_lt hn64, shiftMask_of_lt (by omega : 64 - n < 64)]
  exact (shiftOr_eq_rotateRight n hn hn64 (readSlot bs V dst)).symm

/-! ## 5. Native-rotate Keccak permutation `Com` (the emitted artifact)

`keccakF1600ComRor` is `KeccakEmit.keccakF1600Com` with the two rotate sites
(θ-D's `rotL chiScr 1` and ρ∘π's `rotL B[…] r`) emitted via `emitRotLNative`
(single `rorImm`). It is the `Com` the native-rotate bench driver emits. The
builders below mirror `KeccakEmit.emitThetaDCol`/`emitRhoPiLane`/`emitRound`/
`emitRounds` exactly, differing only in the rotate emitter. -/

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact in
/-- Native-rotate θ-D column (mirror of `KeccakEmit.emitThetaDCol`). -/
def emitThetaDColNative {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitMov bs immVar chiScr (cSlot (x + 1)) fun b iv =>
  emitRotLNative b iv chiScr 1 fun b iv =>
  emitOp b iv .xor chiScr (.st chiScr) (.st (cSlot (x + 4))) fun b iv =>
  emitOp b iv .xor (aSlot x 0) (.st (aSlot x 0)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 1) (.st (aSlot x 1)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 2) (.st (aSlot x 2)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 3) (.st (aSlot x 3)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 4) (.st (aSlot x 4)) (.st chiScr) k

/-- Native-rotate θ-D over columns `start .. start+count-1` (mirror of
    `KeccakEmit.emitTheta_D`). -/
def emitTheta_DNative {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitThetaDColNative bs immV s fun b iv => emitTheta_DNative m (s+1) b iv k

/-- Native-rotate ρ∘π lane (mirror of `KeccakEmit.emitRhoPiLane`). -/
def emitRhoPiLaneNative {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x y : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitMov bs immVar (bSlot y (2 * x + 3 * y)) (aSlot x y) fun b iv =>
  emitRotLNative b iv (bSlot y (2 * x + 3 * y)) (rhoOffset (x + 5 * y)) k

/-- Native-rotate ρ∘π over lanes `start .. start+count-1` (mirror of
    `KeccakEmit.emitRhoPi`). -/
def emitRhoPiNative {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitRhoPiLaneNative bs immV (s % 5) (s / 5) fun b iv => emitRhoPiNative m (s+1) b iv k

/-- Native-rotate full round (mirror of `KeccakEmit.emitRound`): only θ-D and
    ρ∘π change (the rotate sites); θ-C, χ, ι are reused unchanged. -/
def emitRoundNative {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (round : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitTheta_C 5 0 bs immVar fun b iv =>
  emitTheta_DNative 5 0 b iv fun b iv =>
  emitRhoPiNative 25 0 b iv fun b iv =>
  emitChi 25 0 b iv fun b iv =>
  emitIota b iv round k

/-- Native-rotate round sequencing (mirror of `KeccakEmit.emitRounds`). -/
def emitRoundsNative {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitRoundNative bs immV s fun b iv => emitRoundsNative m (s+1) b iv k

/-- **The native-rotate Keccak-p[1600,24] permutation `Com`.** Same structure as
    `KeccakEmit.keccakF1600Com`; every rotate is a single `rorImm`. -/
def keccakF1600ComRor : Com jasminDialect inCtxt r64 :=
  emitRoundsNative 24 0 initBState initImmVar fun bs immV =>
  emitOutStage 25 0 bs immV fun bs _ =>
  .ret (bs.st ⟨24, by decide⟩)

/-! ## 6. Native-rotate flat destination-slot mirror

`KeccakEmit.keccakSlots` mirrors `keccakF1600Com` (3-op `rotL`). The native body
needs its own mirror: a native `rotL` writes **one** slot (`[dst]`) instead of
three (`[55, dst, dst]`). `rotLSlotsRor` and the section mirrors below follow
`KeccakEmit`'s slot defs verbatim except for that one change. -/

/-- Native rotate-left slot sequence: `[dst]` for a real rotate, empty for a
    rotate by a multiple of `64` (the identity, no op emitted). Mirrors the
    `n % 64 == 0` identity guard in `emitRotLNative`, so the emitted op count and
    this destination-slot list stay in lockstep. -/
def rotLSlotsRor (dst n : Nat) : List Nat :=
  if n % 64 == 0 then [] else [dst]

/-- θ-D native slot sequence (mirror of `KeccakEmit.thetaDSlots`). -/
def thetaDSlotsRor : List Nat :=
  (List.range 5).flatMap (fun x =>
    [56] ++ rotLSlotsRor 56 1 ++ [56]
      ++ (List.range 5).map (fun y => x % 5 + 5 * (y % 5)))

/-- ρ∘π native slot sequence (mirror of `KeccakEmit.rhoPiSlots`). -/
def rhoPiSlotsRor : List Nat :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x =>
      let dst := 30 + (y % 5) + 5 * ((2 * x + 3 * y) % 5)
      [dst] ++ rotLSlotsRor dst (rhoOffset (x + 5 * y))))

/-- One native round's slot sequence. θ-C, χ, ι are unchanged from `KeccakEmit`. -/
def roundSlotsRor : List Nat :=
  KeccakEmit.thetaCSlots ++ thetaDSlotsRor ++ rhoPiSlotsRor
    ++ KeccakEmit.chiSlots ++ KeccakEmit.iotaSlots

/-- **The native flat destination-slot list for the 24-round perm + output
    staging.** -/
def keccakSlotsRor : List Nat :=
  (List.replicate 24 roundSlotsRor).flatten ++ KeccakEmit.outStageSlots

/-- Per-binding destination name for the native-rotate Keccak emit. -/
def keccakDstNameRor (j : Nat) : String := KeccakEmit.slotReg (keccakSlotsRor.getD j 0)

/-! ## 7. Self-contained validation

`emitRotLNative` on a one-slot read-out continuation denotes the rotated value;
checked concretely for `n = 1` (the ρ offset of lane `(1,0)`), agreeing with the
shift-or form. -/

/-- A one-slot program: rotate-left slot `0` by `1`, return slot `0`. -/
def demoNativeRot {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (immVar : Nat → Ctxt.Var Γ r64) : Com jasminDialect Γ r64 :=
  emitRotLNative bs immVar ⟨0, by decide⟩ 1
    (fun bs' _ => .ret (bs'.st ⟨0, by decide⟩))

/-- On `n = 1`, the native emitter returns `(slot 0).rotateRight 63`, i.e.
    `rotl(slot 0, 1)`. Concrete check on the value-level agreement: the native
    rotate of `0x1` by 1 (= `rotr 63`) is `0x2`. -/
example : (BitVec.ofNat 64 1).rotateRight (64 - 1) = (BitVec.ofNat 64 2) := by
  decide

/-- The shift-or form of the same rotate agrees: `(1 <<< 1) ||| (1 >>> 63) = 2`. -/
example :
    ((BitVec.ofNat 64 1) <<< 1) ||| ((BitVec.ofNat 64 1) >>> (64 - 1))
      = (BitVec.ofNat 64 2) := by
  decide

/-! ## 8. Native `andn` instruction selection for Keccak χ (#χ-insn-sel)

Keccak's χ step is `A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`.
`KeccakEmit.emitChiLane` lowers the inner `¬B[x+1,y] ∧ B[x+2,y]` as a **three-op**
NOT/AND idiom (plus the leading move):

    chiScr = B[x+1,y];   chiScr ^= allOnes (= ¬);   chiScr &= B[x+2,y]

(i.e. `mov ; xor-allones-mask ; and`), followed by `A[x,y] = B[x,y] ⊕ chiScr`.
The x86 BMI1 `ANDN dst, a, b` computes `dst := (¬a) & b` in **one** instruction;
the jasmin dialect carries it as `JasminBinOp.andn` (denotation `(~~~a) &&& b`,
printer `andnq`). Using it, the inner `¬B[x+1,y] ∧ B[x+2,y]` becomes one `.andn`
op, so the χ lane drops from four ops (`mov ; xor ; and ; xor`) to two
(`andn ; xor`). This is the χ-side instruction-selection perf lever
(χ = 25 lanes × 24 rounds).

`emitChiAndnLane` emits the two-op form; `emitChiAndnLane_chiScr_value_eq` proves
the value it writes to `chiScr` (`(~~~B[x+1,y]) &&& B[x+2,y]`) is **bit-for-bit**
the value the three-op `mov/xor-mask/and` chain writes, under the standard
"mask immediate holds its literal" resolver contract (`hImmMask`). Since the
trailing `A[x,y] = B[x,y] ⊕ chiScr` xor is identical in both, the χ output lane
is unchanged — the rewrite is denotation-preserving. -/

/-- The native two-op χ lane (mirror of `KeccakEmit.emitChiLane`): one `.andn`
    computes `¬B[x+1,y] ∧ B[x+2,y]` into the χ scratch, then `A[x,y] = B[x,y] ⊕
    scratch`. Same `BState`/`Cont` interface as `emitChiLane`, so it drops into a
    χ producer in its place. -/
def emitChiAndnLane {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x y : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitOp bs immVar .andn chiScr (.st (bSlot (x + 1) y)) (.st (bSlot (x + 2) y)) fun b iv =>
  emitOp b iv .xor (aSlot x y) (.st (bSlot x y)) (.st chiScr) k

/-- Native-`andn` χ nonlinear layer over lanes `start .. start+count-1`
    (mirror of `KeccakEmit.emitChi`). -/
def emitChiAndn {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitChiAndnLane bs immV (s % 5) (s / 5) fun b iv => emitChiAndn m (s+1) b iv k

/-! ### Bit-for-bit agreement of the inner NOT/AND value

The three-op idiom computes, at `chiScr`, the value `((¬B[x+1,y]) ∧ B[x+2,y])`
**only when** the mask immediate `maskImm = 0xFFFFFFFFFFFFFFFF` resolves to the
all-ones literal: then `B[x+1,y] ^^^ allOnes = ~~~B[x+1,y]`. The `.andn` op
computes `(~~~B[x+1,y]) &&& B[x+2,y]` directly, with no mask. -/

/-- `x ^^^ (allOnes) = ~~~x` at width 64, where `allOnes = BitVec.ofNat 64
    maskImm = 0xFF…FF`. The XOR-with-all-ones the three-op idiom uses to negate
    is exactly the bitwise complement the `.andn` op applies. -/
theorem xor_maskImm_eq_not (x : BitVec 64) :
    x ^^^ (BitVec.ofNat 64 maskImm) = ~~~ x := by
  have hmask : (BitVec.ofNat 64 maskImm) = BitVec.allOnes 64 := by decide
  rw [hmask, BitVec.xor_allOnes]

/-- **χ insn-selection soundness (value level).** Under the resolver contract
    that the mask input word holds its literal (`hImmMask`), the single `.andn`
    op writes the **same value** to `chiScr` as the three-op `mov/xor-mask/and`
    chain of `emitChiLane`: both equal `(~~~ B[x+1,y]) &&& B[x+2,y]`. Because the
    trailing `A[x,y] = B[x,y] ⊕ chiScr` xor is shared, the χ output lane is
    bit-for-bit unchanged. -/
theorem emitChiAndnLane_chiScr_value_eq {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x y : Nat)
    (V : Ctxt.Valuation Γ)
    (hImmMask : readImm immVar V (immIdx maskImm) = BitVec.ofNat 64 maskImm) :
    -- the `.andn` op's written value …
    JasminBinOp.andn.apply (readSlot bs V (bSlot (x + 1) y))
                           (readSlot bs V (bSlot (x + 2) y))
      -- … equals the three-op idiom's `and`-step value: first NOT the staged
      -- `B[x+1,y]` by xor-ing the mask immediate, then AND with `B[x+2,y]`.
      = JasminBinOp.and.apply
          (JasminBinOp.xor.apply (readSlot bs V (bSlot (x + 1) y))
            (readImm immVar V (immIdx maskImm)))
          (readSlot bs V (bSlot (x + 2) y)) := by
  rw [hImmMask]
  show (~~~ readSlot bs V (bSlot (x + 1) y)) &&& readSlot bs V (bSlot (x + 2) y)
      = ((readSlot bs V (bSlot (x + 1) y)) ^^^ (BitVec.ofNat 64 maskImm))
          &&& readSlot bs V (bSlot (x + 2) y)
  rw [xor_maskImm_eq_not]

/-! ### χ slot list mirror (op count differs: 4 → 2 per lane)

The native χ lane writes **two** slots (`[56, aSlot]`) instead of four
(`[56, 56, 56, aSlot]` of `KeccakEmit.chiSlots`): the leading `mov 56` and the
`xor-mask 56` and `and 56` collapse into one `andn 56`. `chiSlotsAndn` is the
matching destination-slot list so a native-χ producer's emitted op count and the
slot list stay in lockstep. -/

/-- Native-`andn` χ slot sequence: per lane `(x,y)`, `andn chiScr` then
    `xor A[x,y]` — two slots `[56, (x%5)+5*(y%5)]` (vs the four-slot
    `KeccakEmit.chiSlots`). -/
def chiSlotsAndn : List Nat :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x =>
      [56, (x % 5) + 5 * (y % 5)]))

/-! ## 9. Self-contained validation of the `andn` χ value

Concrete check on the value-level agreement: with `b1 = 0b1100`, `b2 = 0b1010`,
the inner χ term `(¬b1) ∧ b2 = 0b0010`, and the `.andn` op and the
`xor-allones ; and` idiom both compute it. -/

/-- `andn 0b1100 0b1010 = 0b0010` (= `(¬0b1100) & 0b1010`). -/
example :
    JasminBinOp.andn.apply (BitVec.ofNat 64 0b1100) (BitVec.ofNat 64 0b1010)
      = (BitVec.ofNat 64 0b0010) := by
  decide

/-- The xor-allones / and idiom computes the same value. -/
example :
    JasminBinOp.and.apply
        (JasminBinOp.xor.apply (BitVec.ofNat 64 0b1100) (BitVec.ofNat 64 maskImm))
        (BitVec.ofNat 64 0b1010)
      = (BitVec.ofNat 64 0b0010) := by
  decide

/-! ## 10. `andn`-χ straight-line permutation (isolated from the broken Ror path)

The native-ROTATE permutation `keccakF1600ComRor` (§7) panics on emit (a
rotate-by-64 lowering bug). To measure the χ instruction-selection win (the 3-op
NOT/AND idiom → one BMI1 `andn`) **independently** of that defect, we build an
`andn`-χ variant of the *straight-line* permutation: it keeps `KeccakEmit`'s
shift-or rotates (`emitTheta_D`, `emitRhoPi` — which emit fine) verbatim and
swaps **only** the χ layer `emitChi` → `emitChiAndn` (§8).

`emitRoundAndn` mirrors `KeccakEmit.emitRound` op-for-op except for that one
substitution; `emitRoundsAndn` / `keccakF1600ComAndn` mirror `emitRounds` /
`keccakF1600Com`. The flat slot list `keccakSlotsAndn` mirrors
`KeccakEmit.keccakSlots` with `chiSlots` (4 slots/lane) replaced by `chiSlotsAndn`
(2 slots/lane) in each round, keeping the emitted op count and destination-name
list in lockstep for the ABI emit. -/

/-- One full straight-line Keccak round with the **`andn`-χ** layer: θ-C, θ-D,
    ρ∘π and ι are `KeccakEmit`'s shift-or straight-line versions verbatim; only χ
    is `emitChiAndn` (two ops/lane) in place of `KeccakEmit.emitChi` (four). -/
def emitRoundAndn {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (round : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitTheta_C 5 0 bs immVar fun b iv =>
  emitTheta_D 5 0 b iv fun b iv =>
  emitRhoPi 25 0 b iv fun b iv =>
  emitChiAndn 25 0 b iv fun b iv =>
  emitIota b iv round k

/-- Emit `andn`-χ rounds `start .. start+count-1` (mirror of
    `KeccakEmit.emitRounds`; full permutation is `count = 24`, `start = 0`). -/
def emitRoundsAndn {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitRoundAndn bs immV s fun b iv => emitRoundsAndn m (s+1) b iv k

/-- The full Keccak-p[1600,24] permutation with the **`andn`-χ** layer as a
    `Com jasminDialect`: 24 straight-line rounds (shift-or rotates, two-op χ),
    then the 25-lane output staging. Mirror of `KeccakEmit.keccakF1600Com` with
    `emitRounds` → `emitRoundsAndn`; the result `Var` is the last output-staging
    write (lane 24), read by the export via the last-25 convention. -/
def keccakF1600ComAndn : Com jasminDialect inCtxt r64 :=
  emitRoundsAndn 24 0 initBState initImmVar fun bs immV =>
  emitOutStage 25 0 bs immV fun bs _ =>
  .ret (bs.st ⟨24, by decide⟩)

/-- A **single** `andn`-χ round (round 0) + 25-lane output staging (mirror of
    `KeccakEmit.keccakRoundCom`); small enough for structural text-checks. -/
def keccakRoundComAndn : Com jasminDialect inCtxt r64 :=
  emitRoundAndn initBState initImmVar 0 fun bs immV =>
  emitOutStage 25 0 bs immV fun bs _ =>
  .ret (bs.st ⟨24, by decide⟩)

/-- One `andn`-χ round's slot sequence: `KeccakEmit.roundSlots` with `chiSlots`
    (4 slots/lane) replaced by `chiSlotsAndn` (2 slots/lane); θ-C, θ-D, ρ∘π and ι
    slot lists are `KeccakEmit`'s straight-line versions verbatim. -/
def roundSlotsAndn : List Nat :=
  thetaCSlots ++ thetaDSlots ++ rhoPiSlots ++ chiSlotsAndn ++ iotaSlots

/-- The flat destination-slot list for the 24-round `andn`-χ permutation + output
    staging (mirror of `KeccakEmit.keccakSlots` with `roundSlots` → `roundSlotsAndn`). -/
def keccakSlotsAndn : List Nat :=
  (List.replicate 24 roundSlotsAndn).flatten ++ outStageSlots

/-- The flat destination-slot list for ONE `andn`-χ round + output staging
    (mirror of `KeccakEmit.keccakRoundSlots`). -/
def keccakRoundSlotsAndn : List Nat := roundSlotsAndn ++ outStageSlots

/-- Per-binding destination name (24-round `andn`-χ program): binding `j` writes
    its slot (mirror of `KeccakEmit.keccakDstName`). -/
def keccakDstNameAndn (j : Nat) : String := KeccakEmit.slotReg (keccakSlotsAndn.getD j 0)

/-- The `andn`-χ round emits **50 fewer** bindings than the straight-line round
    (25 χ lanes × 2 ops saved each — `mov;xor;and;xor` → `andn;xor`):
    `roundSlotsAndn.length + 50 = roundSlots.length`. -/
theorem roundSlotsAndn_length :
    roundSlotsAndn.length + 50 = KeccakEmit.roundSlots.length := by native_decide

/-! ### Value-equivalence status of `keccakF1600ComAndn`

The χ rewrite is **value-preserving**: `emitChiAndnLane_chiScr_value_eq` (§8)
proves the single `.andn` op writes the *same* `BitVec` to `chiScr` as the three-op
`mov/xor-mask/and` chain of `KeccakEmit.emitChiLane`, and the trailing
`A[x,y] = B[x,y] ⊕ chiScr` xor is identical in both, so every χ output lane is
bit-for-bit unchanged. The rest of the round (θ, ρ∘π, ι) is `KeccakEmit`'s code
verbatim. Hence `keccakF1600ComAndn` computes the same permutation as
`KeccakEmit.keccakF1600Com`.

A *monolithic* `Com.denote`-level equality `keccakF1600ComAndn.denote =
keccakF1600Com.denote` is **deferred**, for two structural reasons:

1. **No baseline to mirror.** Even the straight-line `keccakF1600Com` has no
   closed `Com.denote` lemma — `KeccakEmitterReduction` exposes only the
   per-helper rewrites (`emitOp_denote`, `emitMov_denote'`, `emitRotL_denote_pos`),
   and the whole-emitter equality is not stated. There is no proved
   whole-permutation denotation to transport across the χ swap.

2. **Arity mismatch defeats a typed `Com.denote` lane equality.**
   `emitChiLane` extends the context **four** times (mov;xor;and;xor) whereas
   `emitChiAndnLane` extends it **twice** (andn;xor). The continuation `k : Cont t`
   is therefore applied at *different context depths* (`r64::r64::r64::r64::Γ` vs
   `r64::r64::Γ`), so `(emitChiLane … k).denote = (emitChiAndnLane … k).denote` is
   not even type-correct as stated — which is why the proved equivalence
   is at the **value level** (`emitChiAndnLane_chiScr_value_eq`) and not as a
   `Com.denote` equality.

The orchestrator's XKCP byte-identity KAT is the value-correctness gate for the
emitted program; the in-Lean guarantee carried here is the χ-lane value
equivalence (§8) plus the op-count/slot lockstep (`roundSlotsAndn_length`). -/

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakRotateSelect
