/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The multi-limb EC multiply leaf over the ascent `CorresJ` runBlock layer

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`)._

`RunBlockCorres.lean` supplies the flag-carrying forward simulation `CorresJ` over
the total machine fold `runBlock`, its structural core
(`corresJ_nil`/`corresJ_append`/`corresJ_weaken`), the single flag leaves
(`corresJ_sbb`/`corresJ_adc`), the base-`2^64` recomposition `limbVal`, and the
carry-tracking relation `SRcarry`. `EcMultiLimbCapstone.lean` assembles those into
the multi-limb subtract capstone (`sbbLimbs`/`sbbLimbs_spec`/`corresJ_sbbChain`).

This module is the **multiply analogue**. It supplies the arithmetic core the
EC field-multiply kernels need:

* `mulxLimbs`, a pure base-`2^64` operand-scanning (schoolbook) multiply of two
  little-endian limb lists, threading the per-word carry through a fused
  multiply-accumulate pass (`mulxMac`), and its clean multiprecision correctness
  `mulLimbs_spec` — the recomposed product value equals `⟦xs⟧ · ⟦ys⟧` over `ℤ`.
  This is the multiply analogue of `sbbLimbs_spec`: proved by induction, each step
  peeling the low limb and folding the high partial products through the induction
  hypothesis.
* `corresJ_mulx`, a `CorresJ` flag leaf for one `MULX` limb: running the single
  BMI2 widening-multiply instruction under `runBlock` writes the low and high
  product words to the two destination registers and touches no flag, refining the
  abstract `mulxStep` transition through `SRcarry`. `mulxStep_recompose` recovers
  the full 128-bit product `dstHi:dstLo = a · b` across the two output registers.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## Arithmetic scaffolding for the operand-scanning carry threading

Two `Nat` facts under everything: a schoolbook multiply-accumulate column
`x·y + a + c` never overflows a double word (so its high half fits in one limb),
and a low/high word pair recomposes to the underlying integer. Extracted once so
`omega`/`linear_combination` can consume them at every limb step. -/

/-- **The column bound.** One operand-scanning column `x·y + a + c` with all four
    inputs below `B` stays below `B²`; hence its high word `⌊·/B⌋` fits in one limb.
    The single nonlinear fact the carry threading rests on. -/
theorem mulxProdAddBound (x y a c B : Nat)
    (hx : x < B) (hy : y < B) (ha : a < B) (hc : c < B) :
    x * y + a + c < B * B := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have hp : x * y ≤ k * k := Nat.mul_le_mul (by omega) (by omega)
  have hexp : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  omega

/-- **Low/high recomposition.** A double-word value `n < 2^64·2^64` split into its
    low word `n % 2^64` and high word `n / 2^64` recomposes to `n`. The single-limb
    identity every accumulation step reduces to. -/
theorem mulxLohiRecompose (n : Nat) (h : n < 2 ^ 64 * 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat + 2 ^ 64 * (BitVec.ofNat 64 (n / 2 ^ 64)).toNat = n := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (by positivity)).mpr h)]
  have hmd := Nat.mod_add_div n (2 ^ 64)
  omega

/-- `limbVal` peels its low limb: `⟦acc⟧ = head + 2^64·⟦tail⟧`, uniformly over the
    empty and non-empty cases (`headD 0` on `[]` reads `0`). The identity the
    multiply-accumulate step uses to reconcile the accumulator's head with the
    partial product's low column. -/
theorem mulxLimbValHeadTail (acc : List (BitVec 64)) :
    limbVal acc = (acc.headD 0).toNat + 2 ^ 64 * limbVal acc.tail := by
  cases acc with
  | nil => simp [limbVal]
  | cons a as => simp [limbVal]

/-! ## The add-carry pass and the fused multiply-accumulate

`mulxAddCarry acc c` folds a single carry word `c` up through the limb list `acc`
(the tail of the accumulation once the multiplier is exhausted); `mulxMac x ys acc
c` is the fused pass computing the limbs of `x·⟦ys⟧ + ⟦acc⟧ + c`, threading the
one-word carry column by column. -/

/-- Propagate a carry word `c` up through the limbs of `acc`, producing the limbs of
    `⟦acc⟧ + c`. The tail of an operand-scanning pass after the multiplier list is
    exhausted. -/
def mulxAddCarry : List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | [], c => [c]
  | a :: as, c =>
      BitVec.ofNat 64 (a.toNat + c.toNat)
        :: mulxAddCarry as (BitVec.ofNat 64 ((a.toNat + c.toNat) / 2 ^ 64))

/-- **Add-carry correctness.** The recomposed output equals `⟦acc⟧ + c`. A single
    clean induction: each step peels the low word `(a+c) % 2^64` and threads the
    carry `(a+c) / 2^64`. -/
theorem mulxAddCarry_spec (acc : List (BitVec 64)) (c : BitVec 64) :
    limbVal (mulxAddCarry acc c) = limbVal acc + c.toNat := by
  induction acc generalizing c with
  | nil => simp [mulxAddCarry, limbVal]
  | cons a as ih =>
    rw [mulxAddCarry]
    simp only [limbVal]
    rw [ih (BitVec.ofNat 64 ((a.toNat + c.toNat) / 2 ^ 64))]
    set p := a.toNat + c.toNat with hp
    have hb : p < 2 ^ 64 * 2 ^ 64 := by
      have := mulxProdAddBound 0 0 a.toNat c.toNat (2 ^ 64)
        (by positivity) (by positivity) a.isLt c.isLt
      simpa [hp] using this
    have hlo : (BitVec.ofNat 64 p).toNat = p % 2 ^ 64 := by rw [BitVec.toNat_ofNat]
    have hpc : (BitVec.ofNat 64 (p / 2 ^ 64)).toNat = p / 2 ^ 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (by positivity)).mpr hb)]
    have hmd := Nat.mod_add_div p (2 ^ 64)
    rw [hlo, hpc]
    omega

/-- Fused multiply-accumulate: the little-endian limbs of `x·⟦ys⟧ + ⟦acc⟧ + c`,
    threading a single carry word `c`. Recursion is structural on the multiplier
    list `ys`; when `ys` is exhausted the remaining accumulator limbs and the final
    carry are folded through `mulxAddCarry`. -/
def mulxMac (x : BitVec 64) : List (BitVec 64) → List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | [], acc, c => mulxAddCarry acc c
  | y :: ys, acc, c =>
      BitVec.ofNat 64 (x.toNat * y.toNat + (acc.headD 0).toNat + c.toNat)
        :: mulxMac x ys acc.tail
            (BitVec.ofNat 64 ((x.toNat * y.toNat + (acc.headD 0).toNat + c.toNat) / 2 ^ 64))

/-- **Multiply-accumulate correctness** (the crux). The recomposed output equals
    `x·⟦ys⟧ + ⟦acc⟧ + c`. Proved by induction on the multiplier list `ys`,
    generalizing the accumulator and the carry: each step peels the low column
    `(x·y + head + c) % 2^64`, threads the carry `⌊·/2^64⌋` (bounded by
    `mulxProdAddBound`), reconciles the accumulator head with `mulxLimbValHeadTail`,
    and folds the high partial products through the induction hypothesis. The partial
    product distributes by `ring`; the carry recomposition is closed by `omega`. -/
theorem mulxMac_spec (x : BitVec 64) :
    ∀ (ys acc : List (BitVec 64)) (c : BitVec 64),
      limbVal (mulxMac x ys acc c) = x.toNat * limbVal ys + limbVal acc + c.toNat := by
  intro ys
  induction ys with
  | nil =>
    intro acc c
    simp [mulxMac, mulxAddCarry_spec, limbVal]
  | cons y ys ih =>
    intro acc c
    rw [mulxMac]
    simp only [limbVal]
    rw [ih acc.tail (BitVec.ofNat 64 ((x.toNat * y.toNat + (acc.headD 0).toNat + c.toNat) / 2 ^ 64))]
    set p := x.toNat * y.toNat + (acc.headD 0).toNat + c.toNat with hp
    have hb : p < 2 ^ 64 * 2 ^ 64 :=
      mulxProdAddBound x.toNat y.toNat (acc.headD 0).toNat c.toNat (2 ^ 64)
        x.isLt y.isLt (acc.headD 0).isLt c.isLt
    have hlo : (BitVec.ofNat 64 p).toNat = p % 2 ^ 64 := by rw [BitVec.toNat_ofNat]
    have hpc : (BitVec.ofNat 64 (p / 2 ^ 64)).toNat = p / 2 ^ 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (by positivity)).mpr hb)]
    have hacc : limbVal acc = (acc.headD 0).toNat + 2 ^ 64 * limbVal acc.tail :=
      mulxLimbValHeadTail acc
    have hdist : x.toNat * (y.toNat + 2 ^ 64 * limbVal ys)
        = x.toNat * y.toNat + 2 ^ 64 * (x.toNat * limbVal ys) := by ring
    rw [hlo, hpc, hacc, hdist]
    omega

/-! ## The operand-scanning multiply and its multiprecision specification -/

/-- **Base-`2^64` operand-scanning (schoolbook) multiply.** For each multiplier limb
    `x` (least significant first), fuse its partial product `x·⟦ys⟧` into the
    running accumulator shifted up by one limb (`0 :: ·`), via the carry-threaded
    `mulxMac`. Returns the little-endian limbs of `⟦xs⟧ · ⟦ys⟧`. -/
def mulxLimbs : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], _ => []
  | x :: xs, ys => mulxMac x ys ((0 : BitVec 64) :: mulxLimbs xs ys) (0 : BitVec 64)

/-- **The multiprecision multiply specification, `ℕ` core.** The recomposed product
    value equals the true product `⟦xs⟧ · ⟦ys⟧`. Proved by induction on the multiplier
    list `xs`: each step folds one partial product `x·⟦ys⟧` at limb weight `2^64` (the
    `0 :: ·` shift) through `mulxMac_spec` and the induction hypothesis, closing by
    `ring`. -/
theorem mulLimbs_specNat (xs ys : List (BitVec 64)) :
    limbVal (mulxLimbs xs ys) = limbVal xs * limbVal ys := by
  induction xs with
  | nil => simp [mulxLimbs, limbVal]
  | cons x xs' ih =>
    rw [mulxLimbs, mulxMac_spec]
    simp only [limbVal]
    rw [ih]
    have h0 : (0 : BitVec 64).toNat = 0 := by simp
    rw [h0]
    ring

/-- **The multiprecision multiply specification** (the multiply analogue of
    `sbbLimbs_spec`). The recomposed product value equals the true integer product
    `⟦xs⟧ · ⟦ys⟧` over `ℤ`. The `ℤ` cast of the `ℕ` core `mulLimbs_specNat`. -/
theorem mulLimbs_spec (xs ys : List (BitVec 64)) :
    (limbVal (mulxLimbs xs ys) : Int) = (limbVal xs : Int) * (limbVal ys : Int) := by
  exact_mod_cast mulLimbs_specNat xs ys

/-! ## The single-`MULX` flag leaf

`x86_MULX_lo_hi a b = (lo, hi)` with `lo = a·b mod 2^64` and `hi = ⌊a·b / 2^64⌋`,
touching no flag. `mulxStep` is the abstract two-register write, and `corresJ_mulx`
proves `runBlock` realizes it through the carry-tracking relation `SRcarry` — the
`MULX` companion of the `corresJ_sbb`/`corresJ_adc` carry leaves. -/

/-- The low output word of `MULX` is `a·b mod 2^64` (definitional). -/
theorem mulxLoHi_lo (v1 v2 : BitVec 64) :
    (x86_MULX_lo_hi v1 v2).1 = BitVec.ofNat 64 (v1.toNat * v2.toNat) := rfl

/-- The high output word of `MULX` is `⌊a·b / 2^64⌋` (definitional). -/
theorem mulxLoHi_hi (v1 v2 : BitVec 64) :
    (x86_MULX_lo_hi v1 v2).2 = BitVec.ofNat 64 (v1.toNat * v2.toNat / 2 ^ 64) := rfl

/-- **The full 128-bit product recomposition.** The `MULX` low and high output words
    recompose to the full unsigned product `a·b` — the two-register widening multiply
    is exact. -/
theorem mulxLoHi_recompose (v1 v2 : BitVec 64) :
    ((x86_MULX_lo_hi v1 v2).1).toNat + 2 ^ 64 * ((x86_MULX_lo_hi v1 v2).2).toNat
      = v1.toNat * v2.toNat := by
  rw [mulxLoHi_lo, mulxLoHi_hi]
  refine mulxLohiRecompose _ ?_
  have := mulxProdAddBound v1.toNat v2.toNat 0 0 (2 ^ 64) v1.isLt v2.isLt
    (by positivity) (by positivity)
  simpa using this

/-- The abstract single-`MULX` transition `dstHi:dstLo := a·b`: the low product word
    goes to `dstLo`, the high product word to `dstHi` (on a `dstHi = dstLo` clash the
    high word wins, mirroring `evalInstr`'s write order), and no flag is touched. -/
def mulxStep (dstHi dstLo ra rb : String) (ac : ACarry) : ACarry :=
  { regs := fun r =>
      if r = dstHi then BitVec.ofNat 64 ((ac.regs ra).toNat * (ac.regs rb).toNat / 2 ^ 64)
      else if r = dstLo then BitVec.ofNat 64 ((ac.regs ra).toNat * (ac.regs rb).toNat)
      else ac.regs r
    cf := ac.cf }

/-- **The `MULX` flag leaf.** Running the single instruction `mulx dstHi dstLo ra rb`
    under `runBlock` refines the abstract `mulxStep` transition through the
    carry-tracking relation `SRcarry`: both destination registers get the low/high
    product words, and the carry flag is left untouched (`MULX` writes no flag).
    The BMI2 widening-multiply companion of `corresJ_sbb`/`corresJ_adc`. -/
theorem corresJ_mulx (dstHi dstLo ra rb : String) :
    CorresJ SRcarry (fun _ => True) (mulxStep dstHi dstLo ra rb)
      [.mulx dstHi dstLo (.reg ra) (.reg rb)] := by
  intro st ac hSR _
  obtain ⟨hreg, hcf⟩ := hSR
  refine ⟨?_, ?_⟩
  · -- register agreement
    intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, high_bits,
      JState.setReg, JState.get, JOperand.eval, mulxStep, hreg]
  · -- carry-flag agreement (MULX writes no flag)
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, high_bits,
      JState.setReg, JState.flagB, mulxStep]
    exact hcf

/-- **The two-register product readout.** After `mulxStep`, provided the two output
    registers are distinct, the recomposed pair `dstHi:dstLo` equals the full
    unsigned product `a·b`. The abstract-side witness that the `MULX` leaf tracks the
    complete 128-bit product across both registers. -/
theorem mulxStep_recompose (dstHi dstLo ra rb : String) (ac : ACarry) (h : dstHi ≠ dstLo) :
    ((mulxStep dstHi dstLo ra rb ac).regs dstLo).toNat
      + 2 ^ 64 * ((mulxStep dstHi dstLo ra rb ac).regs dstHi).toNat
      = (ac.regs ra).toNat * (ac.regs rb).toNat := by
  have e1 : (mulxStep dstHi dstLo ra rb ac).regs dstHi
      = BitVec.ofNat 64 ((ac.regs ra).toNat * (ac.regs rb).toNat / 2 ^ 64) := by
    simp [mulxStep]
  have e2 : (mulxStep dstHi dstLo ra rb ac).regs dstLo
      = BitVec.ofNat 64 ((ac.regs ra).toNat * (ac.regs rb).toNat) := by
    simp [mulxStep, Ne.symm h]
  rw [e1, e2]
  refine mulxLohiRecompose _ ?_
  have := mulxProdAddBound (ac.regs ra).toNat (ac.regs rb).toNat 0 0 (2 ^ 64)
    (ac.regs ra).isLt (ac.regs rb).isLt (by positivity) (by positivity)
  simpa using this

/-! ## The `mulx`-chain emit block and its `CorresJ` refinement

The multiply-block analogue of `EcMultiLimbCapstone.lean`'s `sbbBlock` /
`sbbAbs` / `corresJ_sbbChain`. Each entry is a widening-multiply tuple
`(dstHi, dstLo, ra, rb)`; the chain is the fold of the `corresJ_mulx` leaf. -/

/-- The concrete emit block for a widening-multiply chain: one
    `mulx dstHi dstLo ra rb` per tuple, in order (limb 0 first). -/
def mulxBlock : List (String × String × String × String) → List (JInstr 64)
  | [] => []
  | (dh, dl, ra, rb) :: ps => .mulx dh dl (.reg ra) (.reg rb) :: mulxBlock ps

/-- The abstract widening-multiply fold matching `mulxBlock`'s execution order:
    `mulxStep` per tuple, the first tuple applied innermost. -/
def mulxAbs : List (String × String × String × String) → ACarry → ACarry
  | [], a => a
  | (dh, dl, ra, rb) :: ps, a => mulxAbs ps (mulxStep dh dl ra rb a)

/-- **The `mulx`-chain refinement.** An arbitrary-length chain of `MULX`
    instructions refines the composed abstract widening-multiply fold `mulxAbs`
    through the carry-tracking relation `SRcarry`: each limb writes its low/high
    product words to its destination registers and touches no flag, so the carry
    bit threads through unchanged. Assembled from `corresJ_mulx` through
    `corresJ_append` by induction on the tuple list. The `MULX` analogue of
    `corresJ_sbbChain`. -/
theorem corresJ_mulxChain (tuples : List (String × String × String × String)) :
    CorresJ SRcarry (fun _ => True) (mulxAbs tuples) (mulxBlock tuples) := by
  induction tuples with
  | nil => exact corresJ_weaken SRcarry (corresJ_nil SRcarry) (fun _ _ => trivial)
  | cons p ps ih =>
    obtain ⟨dh, dl, ra, rb⟩ := p
    show CorresJ SRcarry (fun _ => True) (fun a => mulxAbs ps (mulxStep dh dl ra rb a))
      ([.mulx dh dl (.reg ra) (.reg rb)] ++ mulxBlock ps)
    exact corresJ_append SRcarry (corresJ_mulx dh dl ra rb) ih (fun _ _ => trivial)

/-! ## The `adcx` add-with-carry flag leaf and its chain

The `MULX` partial products land in registers; the operand-scanning accumulation
folds them with `ADCX` (add through the `CF` chain) and `ADOX` (add through the
`OF` chain). This section supplies the `CF`-chain leaf `corresJ_adcx` and its
fold `corresJ_adcxChain`, both refining the abstract `adcStep` transition through
`SRcarry` (which tracks `CF`). `.adcx` reads/writes only `CF` and its data/carry
words are the machine's own `waddcarry`, so — unlike `.adc`, whose `CF` is stated
as an "unsigned result differs" predicate — no residue rewrite is needed: the
carry-out already reads as `decide (2^64 ≤ dst + src + CF)`, exactly `adcStep`. -/

/-- **The `adcx` add-with-carry flag leaf.** Running the single ADX instruction
    `adcx dst src` under `runBlock` refines the abstract `adcStep` transition
    through `SRcarry`: the destination register gets the two's-complement carry
    sum `dst + src + CF`, and the concrete `CF` after the step equals the abstract
    carry-out bit. `.adcx` writes only `CF` (leaving `OF`/`SF`/`PF`/`ZF`), so it
    refines the same `adcStep` that `corresJ_adc` (the full-flag `.adc`) does. -/
theorem corresJ_adcx (dst src : String) :
    CorresJ SRcarry (fun _ => True) (adcStep dst src) [.adcx dst (.reg src)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf⟩ := hSR
  refine ⟨?_, ?_⟩
  · -- register agreement
    intro r
    by_cases hr : r = dst
    · subst hr
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        add_carry, adcStep, JState.get, JOperand.eval, hcf, hreg]
    · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        adcStep, JState.get, JOperand.eval, hcf, hreg, if_neg hr]
  · -- carry-flag agreement
    have hcf' : Option.getD st.flags.cf false = a.cf := by simpa [JState.flagB] using hcf
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, Option.getD_some, adcStep, JState.get, JOperand.eval, hcf', hreg]

/-- The concrete emit block for an `adcx` limb chain: one `adcx dst src` per
    `(dst, src)` register pair, in order (limb 0 first). -/
def adcxBlock : List (String × String) → List (JInstr 64)
  | [] => []
  | (d, s) :: ps => .adcx d (.reg s) :: adcxBlock ps

/-- The abstract add-with-carry fold matching `adcxBlock`'s execution order:
    `adcStep` per pair, limb 0 applied innermost. -/
def adcxAbs : List (String × String) → ACarry → ACarry
  | [], a => a
  | (d, s) :: ps, a => adcxAbs ps (adcStep d s a)

/-- **The `adcx`-chain refinement.** An arbitrary-length chain of `adcx`
    instructions refines the composed abstract add-carry fold `adcxAbs` through
    `SRcarry`: the concrete `CF` written by each limb is exactly the `CF` the next
    limb reads. Assembled from `corresJ_adcx` through `corresJ_append` by induction
    on the pair list. The `ADCX` analogue of `corresJ_sbbChain`. -/
theorem corresJ_adcxChain (pairs : List (String × String)) :
    CorresJ SRcarry (fun _ => True) (adcxAbs pairs) (adcxBlock pairs) := by
  induction pairs with
  | nil => exact corresJ_weaken SRcarry (corresJ_nil SRcarry) (fun _ _ => trivial)
  | cons p ps ih =>
    obtain ⟨d, s⟩ := p
    show CorresJ SRcarry (fun _ => True) (fun a => adcxAbs ps (adcStep d s a))
      ([.adcx d (.reg s)] ++ adcxBlock ps)
    exact corresJ_append SRcarry (corresJ_adcx d s) ih (fun _ _ => trivial)

/-! ## The dual-carry (`CF` + `OF`) accumulation and the whole `mulx`/`adcx`/`adox` block

`bignum_mul_4_8` runs two independent carry chains at once: `ADCX` folds through
`CF`, `ADOX` folds through `OF`, and the `MULX` partial products feed both. A
single-flag `SRcarry` cannot state that — an `adox` step must leave `CF` alone
while an interleaved `adcx` leaves `OF` alone. `ACarry2`/`SRcarry2` track **both**
carry bits, so the two chains thread independently through one `CorresJ`.

`corresJ_adxBlock` is the whole-block refinement: for an arbitrary interleaving of
`mulx`/`adcx`/`adox` (`bignum_mul_4_8`'s exact instruction repertoire), the emitted
block refines the composed abstract fold `adxAbs` over `SRcarry2`. -/

/-- The dual-carry abstract state: a register valuation plus **both** the `CF` and
    `OF` carry bits. The two-chain analogue of `ACarry` — the field an `adcx`/`adox`
    interleaving needs so each chain's flag survives the other's steps. -/
structure ACarry2 where
  /-- Abstract register valuation. -/
  regs : String → BitVec 64
  /-- Abstract `CF` carry bit (the `ADCX` chain). -/
  cf : Bool
  /-- Abstract `OF` carry bit (the `ADOX` chain). -/
  of : Bool

/-- `SRcarry2`: the `JState`↔`ACarry2` relation. Registers agree pointwise, and
    both concrete condition flags `CF` and `OF` equal their abstract bits. The
    dual-carry generalization of `SRcarry`. -/
def SRcarry2 (st : JState 64) (a : ACarry2) : Prop :=
  (∀ r, st.regs r = a.regs r) ∧ st.flagB (·.cf) = a.cf ∧ st.flagB (·.of) = a.of

/-- The abstract `adcx` limb `dst := dst + src + CF` over `ACarry2`: the carry-out
    goes to `CF`, and `OF` is left untouched (the property that lets an `adcx` step
    thread through an interleaved `adox` chain). -/
def adcxStep2 (dst src : String) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = dst then
      add_carry (a.regs dst) (a.regs src) (if a.cf then 1 else 0) else a.regs r
    cf := decide (2 ^ 64 ≤ (a.regs dst).toNat + (a.regs src).toNat + (if a.cf then 1 else 0))
    of := a.of }

/-- The abstract `adox` limb `dst := dst + src + OF` over `ACarry2`: the carry-out
    goes to `OF`, and `CF` is left untouched. The `OF`-chain mirror of `adcxStep2`. -/
def adoxStep2 (dst src : String) (a : ACarry2) : ACarry2 :=
  { regs := fun r => if r = dst then
      add_carry (a.regs dst) (a.regs src) (if a.of then 1 else 0) else a.regs r
    cf := a.cf
    of := decide (2 ^ 64 ≤ (a.regs dst).toNat + (a.regs src).toNat + (if a.of then 1 else 0)) }

/-- The abstract `mulx` limb over `ACarry2`: the low/high product words go to
    `dstLo`/`dstHi` (high wins on a clash, mirroring `evalInstr`'s write order),
    and **neither** carry flag is touched — `MULX` writes no flag, so both the `CF`
    and `OF` chains pass through it unchanged. -/
def mulxStep2 (dstHi dstLo ra rb : String) (a : ACarry2) : ACarry2 :=
  { regs := fun r =>
      if r = dstHi then BitVec.ofNat 64 ((a.regs ra).toNat * (a.regs rb).toNat / 2 ^ 64)
      else if r = dstLo then BitVec.ofNat 64 ((a.regs ra).toNat * (a.regs rb).toNat)
      else a.regs r
    cf := a.cf
    of := a.of }

/-- **The dual-carry `adcx` leaf.** `adcx dst src` under `runBlock` refines
    `adcxStep2` through `SRcarry2`: `dst` gets the carry sum, `CF` gets the
    carry-out, and `OF` is preserved. -/
theorem corresJ_adcx2 (dst src : String) :
    CorresJ SRcarry2 (fun _ => True) (adcxStep2 dst src) [.adcx dst (.reg src)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf, hof⟩ := hSR
  have hcf' : Option.getD st.flags.cf false = a.cf := by simpa [JState.flagB] using hcf
  have hof' : Option.getD st.flags.of false = a.of := by simpa [JState.flagB] using hof
  refine ⟨?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = dst
    · subst hr
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        add_carry, adcxStep2, JState.get, JOperand.eval, hcf, hreg]
    · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        adcxStep2, JState.get, JOperand.eval, hcf, hreg, if_neg hr]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, Option.getD_some, adcxStep2, JState.get, JOperand.eval, hcf', hreg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, adcxStep2]
    exact hof'

/-- **The dual-carry `adox` leaf.** `adox dst src` under `runBlock` refines
    `adoxStep2` through `SRcarry2`: `dst` gets the carry sum, `OF` gets the
    carry-out, and `CF` is preserved. The `OF`-chain mirror of `corresJ_adcx2`. -/
theorem corresJ_adox2 (dst src : String) :
    CorresJ SRcarry2 (fun _ => True) (adoxStep2 dst src) [.adox dst (.reg src)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf, hof⟩ := hSR
  have hcf' : Option.getD st.flags.cf false = a.cf := by simpa [JState.flagB] using hcf
  have hof' : Option.getD st.flags.of false = a.of := by simpa [JState.flagB] using hof
  refine ⟨?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = dst
    · subst hr
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        add_carry, adoxStep2, JState.get, JOperand.eval, hof, hreg]
    · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
        adoxStep2, JState.get, JOperand.eval, hof, hreg, if_neg hr]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, adoxStep2]
    exact hcf'
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, waddcarry,
      JState.flagB, Option.getD_some, adoxStep2, JState.get, JOperand.eval, hof', hreg]

/-- **The dual-carry `mulx` leaf.** `mulx dstHi dstLo ra rb` under `runBlock`
    refines `mulxStep2` through `SRcarry2`: both destination registers get the
    low/high product words, and both carry flags are preserved. The `MULX` companion
    over the two-chain state. -/
theorem corresJ_mulx2 (dstHi dstLo ra rb : String) :
    CorresJ SRcarry2 (fun _ => True) (mulxStep2 dstHi dstLo ra rb)
      [.mulx dstHi dstLo (.reg ra) (.reg rb)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf, hof⟩ := hSR
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, high_bits,
      JState.setReg, JState.get, JOperand.eval, mulxStep2, hreg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, high_bits,
      JState.setReg, JState.flagB, mulxStep2]
    exact hcf
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, high_bits,
      JState.setReg, JState.flagB, mulxStep2]
    exact hof

/-- One instruction of the `bignum_mul_4_8` accumulation repertoire: a widening
    multiply, an `ADCX` (`CF`-chain) add, or an `ADOX` (`OF`-chain) add. -/
inductive AdxOp where
  /-- `mulx dstHi dstLo ra rb`. -/
  | mulx (dstHi dstLo ra rb : String)
  /-- `adcx dst src` (folds through `CF`). -/
  | adcx (dst src : String)
  /-- `adox dst src` (folds through `OF`). -/
  | adox (dst src : String)

/-- The concrete emit of one `AdxOp`. -/
def adxOpBlock : AdxOp → List (JInstr 64)
  | .mulx dh dl ra rb => [.mulx dh dl (.reg ra) (.reg rb)]
  | .adcx d s => [.adcx d (.reg s)]
  | .adox d s => [.adox d (.reg s)]

/-- The abstract step of one `AdxOp` over `ACarry2`. -/
def adxOpStep : AdxOp → ACarry2 → ACarry2
  | .mulx dh dl ra rb => mulxStep2 dh dl ra rb
  | .adcx d s => adcxStep2 d s
  | .adox d s => adoxStep2 d s

/-- The concrete emit block for an op list: each op's instructions, in order. -/
def adxBlock : List AdxOp → List (JInstr 64)
  | [] => []
  | o :: os => adxOpBlock o ++ adxBlock os

/-- The abstract fold matching `adxBlock`'s execution order: `adxOpStep` per op,
    the first op applied innermost. -/
def adxAbs : List AdxOp → ACarry2 → ACarry2
  | [], a => a
  | o :: os, a => adxAbs os (adxOpStep o a)

/-- **Each `mulx`/`adcx`/`adox` op refines its abstract step** over `SRcarry2`,
    dispatching to the three dual-carry leaves. -/
theorem corresJ_adxOp (o : AdxOp) :
    CorresJ SRcarry2 (fun _ => True) (adxOpStep o) (adxOpBlock o) := by
  cases o with
  | mulx dh dl ra rb => exact corresJ_mulx2 dh dl ra rb
  | adcx d s => exact corresJ_adcx2 d s
  | adox d s => exact corresJ_adox2 d s

/-- **The whole `mulx`/`adcx`/`adox` block refinement.** An arbitrary interleaving
    of widening multiplies and the two carry-chain adds — `bignum_mul_4_8`'s exact
    instruction repertoire — refines the composed abstract fold `adxAbs` through
    `SRcarry2`: the `CF` chain (`ADCX`) and the `OF` chain (`ADOX`) thread
    independently, each surviving the other's steps and the intervening `MULX`
    products, all matched by the two-flag relation. Assembled from `corresJ_adxOp`
    through `corresJ_append` by induction on the op list. This is the whole-block
    forward simulation the product/accumulation `bignum_mul_4_8` shape runs. -/
theorem corresJ_adxBlock (os : List AdxOp) :
    CorresJ SRcarry2 (fun _ => True) (adxAbs os) (adxBlock os) := by
  induction os with
  | nil => exact corresJ_weaken SRcarry2 (corresJ_nil SRcarry2) (fun _ _ => trivial)
  | cons o os ih =>
    show CorresJ SRcarry2 (fun _ => True) (fun a => adxAbs os (adxOpStep o a))
      (adxOpBlock o ++ adxBlock os)
    exact corresJ_append SRcarry2 (corresJ_adxOp o) ih (fun _ _ => trivial)

/-! ## The concrete four-limb field-multiply value capstone

Routing the `2^256` (four-limb) instance of `mulLimbs_specNat` through the
multi-limb value relation `SRcarryLimbs`, as `feSub4_capstone` routes
`sbbLimbs_spec`: from a machine state whose designated four-register limb window
recomposes to the abstract multi-precision value `a.val`, the four-limb
`mulxLimbs` on those abstract limbs computes exactly `a.val · ⟦ys⟧` — the
`bignum_mul_4_8` shape. -/

/-- **The four-limb field-multiply capstone.** From a `JState` whose limb window
    `[n0, n1, n2, n3]` recomposes (via `SRcarryLimbs`) to the abstract value
    `a.val`, the four-limb operand-scanning `mulxLimbs` on the abstract multiplier
    limbs computes exactly `a.val` times the recomposed multiplicand
    `[y0, y1, y2, y3]`. Combines `srcarryLimbs_recompose` (the value bridge) with
    the four-limb instance of `mulLimbs_specNat` (the operand-scanning
    correctness). The `2^256` `bignum_mul_4_8` product shape. -/
theorem feMul4_capstone (n0 n1 n2 n3 : String) (st : JState 64) (a : ACarryLimbs)
    (h : SRcarryLimbs [n0, n1, n2, n3] st a) (y0 y1 y2 y3 : BitVec 64) :
    limbVal (mulxLimbs [a.regs n0, a.regs n1, a.regs n2, a.regs n3] [y0, y1, y2, y3])
      = a.val * limbVal [y0, y1, y2, y3] := by
  have hrec : limbVal [a.regs n0, a.regs n1, a.regs n2, a.regs n3] = a.val := by
    have hr := srcarryLimbs_recompose [n0, n1, n2, n3] st a h
    simpa using hr
  rw [mulLimbs_specNat, hrec]

end CatCrypt.Crypto.SecureCompilation.Ascent
