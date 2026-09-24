/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction

/-!
# Native-rotate instruction selection for SHA-2 Σ/σ

SHA-2's four sigma functions `Σ0, Σ1, σ0, σ1` (FIPS 180-4 §4.1) are built from
right-rotations `rotr(x, n)`. `Sha2Emit.emitRotr` lowers each as the
**three-op** shift-or idiom

    scA = src >>> n;   scB = src <<< (w-n);   out = scA ||| scB

(two shifts + an or, plus two scratch slots). x86 has `ROR r{w}, imm` (one op,
clobbers flags) and BMI2 `RORX r{w}, r{w}, imm` (one op, flag-free); the jasmin
dialect carries `JasminOp.rorImm` denoting `BitVec.rotateRight`.

This module is the **rotate insn-selection** for SHA-2: `emitRotrNative` emits a
single `rorImm w n` op in place of the three-op chain, and
`emitRotrNative_value_eq_emitRotr_value` proves the value it writes to slot `out`
is **bit-for-bit** the value `emitRotr` writes — so the rewrite is
denotation-preserving and the SHA-256/SHA-512 KAT is unchanged.

## What is verified, and the side condition

The native rewrite unconditionally writes `src.rotateRight n`
(`emitRotrNative_denote_pos`). Agreement with the three-op `emitRotr` form needs
one fact about the resolver: the input words holding the shift amounts `n` and
`w-n` carry the literals `n` and `w-n` (`BitVec.ofNat w ·`). This is exactly what
the emit's input resolver renders for the `amtIdx`-addressed shift literals, and
it is the standard "immediate input holds its literal" contract carried by the
SHA-2 reduction substrate. We make it explicit (`hAmtN`, `hAmtWN`) rather than
bake it in.

The bit-for-bit core is `JasminDialect.rorImm_denote_eq_shiftOr` plus `|||`
commutativity.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2RotateSelect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction

/-! ## 1. The native single-op right-rotate emitter -/

/-- Emit one native `rorImm w n` op (a right-rotate by `n`), writing slot `out`
    from slot `src`, then continue with `k` over the one-extended context.
    Replaces the three-op `Sha2Emit.emitRotr` chain. -/
def emitRotrNative {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src n : Nat) (k : SCont w s) : Com jasminDialect Γ s :=
  let ex : Expr jasminDialect Γ (Rw w) :=
    { op := .rorImm w n
      retTy_eq := rfl
      args := .cons (e.slot src) .nil }
  .var ex (k (envAfterOp e out))

/-! ## 2. Denotation of the native emitter -/

/-- **`emitRotrNative` denotation rewrite.** The single `rorImm` op writes
    `(readSlot e V src).rotateRight n` to slot `out`; the continuation receives
    the one-extended environment. -/
theorem emitRotrNative_denote_pos {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src n : Nat) (k : SCont w s) (V : Ctxt.Valuation Γ) :
    (emitRotrNative e out src n k).denote V
      = (k (envAfterOp e out)).denote
          (V.extend ((readSlot e V src).rotateRight n)) := by
  rfl

/-! ## 3. The bit-for-bit shift-or agreement -/

/-- **The shift-or value equals `rotateRight n`.** For `0 < n < w`, the three-op
    idiom's output `(x >>> n) ||| (x <<< (w-n))` equals `x.rotateRight n`. This
    is `rorImm_denote_eq_shiftOr` itself (no `|||` reordering needed — `emitRotr`
    lists the halves in the same `>>>`-then-`<<<` order as `rotateRight_def`). -/
theorem shiftOr_eq_rotateRight {w : Nat} (n : Nat) (hn : n < w) (x : BitVec w) :
    (x >>> n) ||| (x <<< (w - n)) = x.rotateRight n :=
  (rorImm_denote_eq_shiftOr n hn x).symm

/-! ## 4. Drop-in agreement of the two emitters

The two emitters write the **same value** to slot `out`. We expose the agreement
at the value level (the native single op vs. the `outVal` of `emitRotr_denote`),
which is what denotation-preservation of the Σ/σ rewrite consumes: every
downstream read of slot `out` sees the identical `BitVec`. -/

/-- **Insn-selection soundness (value level).** Under the resolver contract that
    the shift-amount input words hold their literals (`hAmtN`, `hAmtWN`), the
    native single-op emitter writes the **same value** to slot `out` as the
    three-op `emitRotr` chain: both equal `(readSlot e V src).rotateRight n` =
    `(src >>> n) ||| (src <<< (w-n))`. The bit-for-bit guarantee that the rotate
    insn-selection does not change the SHA-2 Σ/σ output. -/
theorem emitRotrNative_value_eq_emitRotr_value {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (out src n : Nat) (V : Ctxt.Valuation Γ)
    (hn0 : 0 < n) (hnw : n < w)
    (hAmtN : readInp e V (amtIdx n) = BitVec.ofNat w n)
    (hAmtWN : readInp e V (amtIdx (w - n)) = BitVec.ofNat w (w - n)) :
    -- the native emitter's written value …
    (readSlot e V src).rotateRight n
      -- … equals the three-op idiom's written value (the `outVal` of
      -- `emitRotr_denote`), read through the immediate resolver.
      = JasminBinOp.or.apply
          (JasminBinOp.shr.apply (readSlot e V src) (readInp e V (amtIdx n)))
          (JasminBinOp.shl.apply (readSlot e V src) (readInp e V (amtIdx (w - n)))) := by
  set x := readSlot e V src with hx
  show x.rotateRight n
      = JasminBinOp.or.apply
          (JasminBinOp.shr.apply x (readInp e V (amtIdx n)))
          (JasminBinOp.shl.apply x (readInp e V (amtIdx (w - n))))
  rw [hAmtN, hAmtWN]
  show x.rotateRight n
      = (x >>> (BitVec.ofNat w n).toNat) ||| (x <<< (BitVec.ofNat w (w - n)).toNat)
  have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hnt : (BitVec.ofNat w n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hnt' : (BitVec.ofNat w (w - n)).toNat = w - n := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hnt, hnt']
  exact (shiftOr_eq_rotateRight n hnw x).symm

/-! ## 5. Native-rotate SHA-2 compression `Com` (the emitted artifact)

`compressComRor` is `Sha2Emit.compressCom` with every `emitRotr` (3-op
shift-or) swapped for `emitRotrNative` (single `rorImm`). It is the `Com` the
native-rotate bench driver emits; `JasminAbiEmit.emitBodyReg` renders the
`rorImm` op as a single `#ROR_w`. The sigma/sched/round builders below mirror
`Sha2Emit.emitSigma`/`emitSched`/`emitRound`/`emitRounds` exactly, differing
only in the rotate emitter. -/

/-- Native-rotate `emitSigma`: `rotr r1 ^ rotr r2 ^ (rotr|shr) r3`, with each
    rotate a single `rorImm`. Mirrors `Sha2Emit.emitSigma` (the `scA scB` rotate
    scratch is unused by the native rotate; kept in the signature for a
    drop-in shape). -/
def emitSigmaNative {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src r1 r2 r3 : Nat) (r3IsShr : Bool) (scC : Nat)
    (k : SCont w s) : Com jasminDialect Γ s :=
  emitRotrNative e out src r1 fun e1 =>
  emitRotrNative e1 scC src r2 fun e2 =>
  emitOp e2 .xor out (.sl out) (.sl scC) fun e3 =>
  (if r3IsShr then emitShr e3 scC src r3 else emitRotrNative e3 scC src r3) fun e4 =>
  emitOp e4 .xor out (.sl out) (.sl scC) k

/-- Native-rotate schedule expansion (mirror of `Sha2Emit.emitSched`). -/
def emitSchedNative (sp : Sha2Spec) :
    List Nat → {Γ : Ctxt jasminDialect} → Env sp.w Γ → SCont sp.w (Rw sp.w) →
    Com jasminDialect Γ (Rw sp.w)
  | [], _, e, k => k e
  | tt :: rest, _, e, k =>
      emitSigmaNative e sigS (tt - 2) sp.smallSig1.1 sp.smallSig1.2.1 sp.smallSig1.2.2 true
          scC fun e1 =>
      emitOp e1 .add scD (.sl sigS) (.sl (tt - 7)) fun e2 =>
      emitSigmaNative e2 sigS (tt - 15) sp.smallSig0.1 sp.smallSig0.2.1 sp.smallSig0.2.2 true
          scC fun e3 =>
      emitOp e3 .add scD (.sl scD) (.sl sigS) fun e4 =>
      emitOp e4 .add tt (.sl scD) (.sl (tt - 16)) fun e5 =>
      emitSchedNative sp rest e5 k

/-- Native-rotate compression round (mirror of `Sha2Emit.emitRound`). -/
def emitRoundNative (sp : Sha2Spec) (rt : Nat) {Γ : Ctxt jasminDialect}
    (e : Env sp.w Γ) (k : SCont sp.w (Rw sp.w)) : Com jasminDialect Γ (Rw sp.w) :=
  let a := wkA; let b := wkA+1; let c := wkA+2; let d := wkA+3
  let e' := wkA+4; let f := wkA+5; let g := wkA+6; let h := wkA+7
  emitSigmaNative e sigS e' sp.bigSig1.1 sp.bigSig1.2.1 sp.bigSig1.2.2 false scC fun s1 =>
  emitOp s1 .add t1S (.sl h) (.sl sigS) fun s2 =>
  emitOp s2 .and chmS (.sl e') (.sl f) fun s3 =>
  emitOp s3 .xor scC (.sl e') (.iw allOnesIdx) fun s4 =>
  emitOp s4 .and scC (.sl scC) (.sl g) fun s5 =>
  emitOp s5 .xor chmS (.sl chmS) (.sl scC) fun s6 =>
  emitOp s6 .add t1S (.sl t1S) (.sl chmS) fun s7 =>
  emitOp s7 .add t1S (.sl t1S) (.iw (kIdx rt)) fun s8 =>
  emitOp s8 .add t1S (.sl t1S) (.sl rt) fun s9 =>
  emitSigmaNative s9 t2S a sp.bigSig0.1 sp.bigSig0.2.1 sp.bigSig0.2.2 false scC fun s10 =>
  emitOp s10 .and chmS (.sl a) (.sl b) fun s11 =>
  emitOp s11 .and scC (.sl a) (.sl c) fun s12 =>
  emitOp s12 .xor chmS (.sl chmS) (.sl scC) fun s13 =>
  emitOp s13 .and scC (.sl b) (.sl c) fun s14 =>
  emitOp s14 .xor chmS (.sl chmS) (.sl scC) fun s15 =>
  emitOp s15 .add t2S (.sl t2S) (.sl chmS) fun s16 =>
  emitOp s16 .add scD (.sl d) (.sl t1S) fun s17 =>
  emitOp s17 .add chmS (.sl t1S) (.sl t2S) fun s18 =>
  cp s18 h g fun r1 => cp r1 g f fun r2 => cp r2 f e' fun r3 => cp r3 e' scD fun r4 =>
  cp r4 d c fun r5 => cp r5 c b fun r6 => cp r6 b a fun r7 => cp r7 a chmS k

/-- Native-rotate round sequencing (mirror of `Sha2Emit.emitRounds`). -/
def emitRoundsNative (sp : Sha2Spec) :
    List Nat → {Γ : Ctxt jasminDialect} → Env sp.w Γ → SCont sp.w (Rw sp.w) →
    Com jasminDialect Γ (Rw sp.w)
  | [], _, e, k => k e
  | rt :: rest, _, e, k => emitRoundNative sp rt e fun e1 => emitRoundsNative sp rest e1 k

/-- **The native-rotate SHA-2 compression `Com`.** `Sha2Emit.compressCom` with
    every rotate emitted as a single `rorImm` (`#ROR_w`) instead of the
    `shr; shl; or` triple. Same schedule / rounds / feed-forward shape. -/
def compressComRor (sp : Sha2Spec) : Com jasminDialect (inCtxt sp.w) (Rw sp.w) :=
  emitSchedNative sp ((List.range (sp.rounds - 16)).map (· + 16)) (initEnv sp) fun e1 =>
  emitRoundsNative sp (List.range sp.rounds) e1 fun e2 =>
  emitFeed sp (List.range 8) e2 fun e3 =>
  .ret (e3.slot (outA + 7))

/-! ## 6. Native-rotate flat destination-slot mirror

`Sha2Emit.slotSeq` is the per-binding destination-slot list of `compressCom`
(3-op rotates). `compressComRor` has a different per-binding shape (1 op per
rotate), so it needs its own flat mirror `slotSeqRor`, kept in lock-step with
`emitSigmaNative`/`emitSchedNative`/`emitRoundNative` exactly as `slotSeq` mirrors
the canonical builders. The driver `sha2_ror_emit.lean` names binding `k`'s
destination `st[(slotSeqRor sp).getD k 0]`. -/

/-- Slots written by `emitSigmaNative out _ _ _ _ r3IsShr scC`: five bindings —
    `out, scC, out, (scC), out`. -/
def sigmaSlotsRor (out r3IsShr scC : Nat) : List Nat :=
  [out, scC, out, scC, out]

/-- Slots written by one native schedule step (mirrors `emitSchedNative`). -/
def schedStepSlotsRor (tt : Nat) : List Nat :=
  sigmaSlotsRor sigS 1 scC ++ [scD] ++ sigmaSlotsRor sigS 1 scC ++ [scD] ++ [tt]

/-- Slots written by one native round (mirrors `emitRoundNative`). -/
def roundSlotsRor : List Nat :=
  let a := wkA; let b := wkA+1; let c := wkA+2; let d := wkA+3
  let e := wkA+4; let f := wkA+5; let g := wkA+6; let h := wkA+7
  sigmaSlotsRor sigS 0 scC ++ [t1S] ++
  [chmS, scC, scC, chmS, t1S, t1S, t1S] ++
  sigmaSlotsRor t2S 0 scC ++
  [chmS, scC, chmS, scC, chmS, t2S, scD, chmS] ++
  [h, g, f, e, d, c, b, a]

/-- Slots written by the 8-word feed-forward (identical to the canonical mirror). -/
def feedSlotsRor : List Nat := (List.range 8).map (fun j => outA + j)

/-- **The full per-binding destination-slot list for `compressComRor sp`.** -/
def slotSeqRor (sp : Sha2Spec) : List Nat :=
  ((List.range (sp.rounds - 16)).map (· + 16)).flatMap schedStepSlotsRor ++
  (List.replicate sp.rounds roundSlotsRor).flatten ++
  feedSlotsRor

/-- Per-binding destination name for the native-rotate emit: binding `k` writes
    `st[slot]`. (Identity-RA style; the native body's slot reuse already keeps
    the working/scratch slots in a small file `0..127`.) -/
def dstNameRor (sp : Sha2Spec) (k : Nat) : String :=
  "st[" ++ toString ((slotSeqRor sp).getD k 0) ++ "]"

/-- Per-step binding counts: a native sigma is 5 bindings (`sigmaSlotsRor` has 5
    entries), a sched step `5+1+5+1+1 = 13`, a round `5+1+7+5+8+8 = 34`, and the
    feed-forward 8. `slotSeqRor` length is therefore
    `13·(rounds-16) + 34·rounds + 8`, which the driver checks equals
    `comBindings (compressComRor sp)` at emit time (a cheap fold over the built
    Com), avoiding a heavy in-kernel `native_decide` on the unrolled body. -/
theorem sigmaSlotsRor_length (out r3IsShr scC : Nat) :
    (sigmaSlotsRor out r3IsShr scC).length = 5 := rfl

/-! ## 8. Self-contained validation

SHA-512 `σ0` rotates by `1`, `8` (and shifts by `7`). Check the native rotate of
a 64-bit value by 1 agrees with the shift-or form. -/

/-- The native right-rotate of `0x2` by 1 is `0x1`. -/
example : (BitVec.ofNat 64 2).rotateRight 1 = (BitVec.ofNat 64 1) := by decide

/-- The shift-or form of the same rotate agrees. -/
example :
    ((BitVec.ofNat 64 2) >>> 1) ||| ((BitVec.ofNat 64 2) <<< (64 - 1))
      = (BitVec.ofNat 64 1) := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2RotateSelect
