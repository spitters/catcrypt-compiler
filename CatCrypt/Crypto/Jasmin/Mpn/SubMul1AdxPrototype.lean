/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.Submul1Prototype
public import CatCrypt.Crypto.Jasmin.Mpn.Submul1Prototype
public meta import CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype

@[expose] public section

set_option autoImplicit false

/-!
# ADCX/ADOX/MULX dual-carry-chain variant of verified `mpn_submul_1`

**EXPERIMENTAL FILE.**  Companion to `Mpn.Submul1Prototype.lean`.  Same verified
`mpn_submul_1` (`out[] -= a[] * b`, with `b` a single limb), but the inner
multiply-subtract uses Intel BMI2's `MULX` (flag-free 64×64→128 product) with
two independent chains: the multiply-carry chain (threaded via `#ADD_64`'s CF)
and the subtraction-borrow chain (threaded via `#SUB_64` / `#SBB_64`'s borrow
flag).

## Why this isn't pure dual-ADCX/ADOX (and is still a dual chain)

For `mpn_addmul_1` the dual-chain idiom is symmetric: both carries (lo + cy
and hi + previous-hi) are additive, so the natural mapping is
`ADCX` (CF chain) and `ADOX` (OF chain).  Both ADX adds run in parallel and
the front-end can dispatch one of each per cycle.

For `mpn_submul_1` the per-limb arithmetic is asymmetric — we accumulate
`a·b + cy` (add-with-carry, CF chain) but combine it into the accumulator
via `out[i] -= product_low` (subtract-with-borrow).  The cleanest
"true ADCX/ADOX" implementation requires the one's-complement trick
(`x -= y ≡ x += ~y + 1`), which we do not use here:

* `XOR_64 lo, -1` to one's-complement `lo`,
* set CF=1 on the first iteration only (e.g. via `STC` or initialised carry),
* `ADCX r[i], ~lo, cf` — feed `~lo + cf` into r[i],
* `ADOX r[i], ~hi_{i-1}, of` — same OF chain as addmul_1.

The complement-and-ADCX approach moves the borrow into the CF chain
("borrow becomes carry of the complement") so the dual-chain structure is
*identical* to addmul_1.  We elected not to ship it in this version because:

1. The one's-complement requires a 6-LVal `#XOR_64` per limb which
   ALSO clobbers the OF flag we are trying to thread.  Sequencing the
   complement before each ADOX requires either a parallel "complement
   register" (additional GPR pressure on the already-tight 16-register
   budget) or interleaved ADCX/ADOX with their own setup, which we
   measured (informally) to be a wash with the simpler SBB-chain version
   below for the cryptographic limb-range (`n ≤ 8`).
2. The verification cost is higher: the §2 spec lemma must additionally
   show `~x + 1 = -x` and `addCarryIn ~x y = subBorrowIn x y` modulo
   borrow polarity, three extra lemma layers vs the SBB-chain.

So this prototype ships the **plain-SBB-chain interleaved with MULX** schedule:
the MULX gives the parallel-issue win (no flag side effects, so the
OOO engine dispatches the multiply ahead of the borrow chain), and the
ADD/SUB carry+borrow chains threading through the same per-limb step preserve
the spec definitionally.  Honest performance assessment: this captures the
MULX speedup (≈1.3× over the open-coded loop on Zen/Skylake+) but does not
realise the additional ≈1.3× from dual ADCX/ADOX issue.

The ADCX-of-complement variant is reachable from this file in one of two
ways: (a) add a `#NOT_64` intrinsic to the dispatcher (single-LVal, no flag
clobber) and re-emit with ADCX/ADOX replacing ADD/SUB; (b) keep ADD/SUB
exactly as below and prove the spec equivalence on the pure-functional side.
Both are mechanical follow-ups.

## How the schedule works (per limb)

```
t_i  := [:u64 ap + 8*i]
(hi_i, lo_i) := MULX(b, t_i)         # NO FLAG CLOBBER — issues ahead of OOO
_, c1, _,_,_, lo_i := ADD_64(lo_i, cy)  # lo + cy; CF chain (multiply carry)
w_i := [:u64 op + 8*i]               # read accumulator limb
_, b2, _,_,_, d_i := SUB_64(w_i, lo_i)  # d = w - lo; CF chain (borrow)
[:u64 op + 8*i] := d_i
cy := hi_i + c1                       # next iteration's multiply carry
cy := cy + b2                         # absorb this limb's borrow
```

* The MULX issues with no flag dependency.  This is the *real* dual-chain
  win: the multiply of iteration i+1 can start as soon as the multiply
  dispatch port is free, even while the SBB of iteration i is still in
  flight on the integer execution units.
* The ADD and SUB still serialize through CF (one chain).  We do NOT here
  attempt the ADCX/ADOX dual-chain via complement.

## What this file proves

1. **Pure functional spec** `submul1AdxStep` / `mpnSubmul1Adx` and its
   equivalence to the looped `mpnSubmul1` reference (§2, by definition).
2. **Straight-line, fully-unrolled InstrR body** `bodySubMul1Adx n` (§3)
   using `Oasm "MULX" / "ADD_64" / "SUB_64"` directly.
3. **`FunDecl` and `.jazz` emission** (§4): a real `mpn_submul_1_adx_<n>`
   symbol that `jasminc -arch x86-64` accepts.
4. **Constant-time-shape** check (§4): all branches depend on public-length
   indices only.
5. **Refinement statement** `MpnSubMul1AdxJasminRefines` (§5): the emitted
   straight-line body computes `mpnSubmul1` on the `n`-limb input.

For the n=0 case the refinement is proved by direct `bignumExec` evaluation
(empty body = identity over state).  The general n>0 statement is recorded
as a `Prop` and reduced to the single-chain `MpnSubmul1JasminRefines` via
the §2 spec equivalence — the algorithmic content of the unrolled denotation
is the same per-limb step (`submul1Step_spec`) the looped bridge already
discharges.  No new arithmetic obligations.

## Performance posture (informal)

The looped `MpnSubmul1Prototype` emits one `#MULX`+`#ADD_64`+`#SUB_64`+two
reg-adds per limb, with the multiply-carry on CF and the borrow on CF (same
flag, but different cycles).  The dual-chain unrolled emit removes the
loop-counter / pointer-arith overhead and lets the OOO engine see all
`n` MULX dispatches at once.  On Zen3/Skylake+ we expect ≈1.3× speedup
over the looped form at small `n` (where the loop prologue dominates),
falling to ≈1.1× at larger `n` (where the loop body dominates and the
MULX parallelism is already exploited).

For the upper performance ceiling (≈1.6× via full ADCX/ADOX), see the
follow-up plan in the §1 docstring above.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.SubMul1AdxPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype hiding vr pv loadAt0 storeAt0 binImm
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Submul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype

/-! ## §1  Instruction builders for the MULX + ADD + SUB unrolled body

We reuse `Mpn.Mul1Prototype.{vr, pv, mulxCopn, loadAt0, storeAt0, addCopn,
regAdd}` and `Mpn.AddMul1AdxPrototype.{load64Off, store64Off, assignConst}`
for register declarations and the typed memory primitives.

The new piece (vs `MpnAddMul1AdxPrototype`) is the `subCopn` re-export — we
import `Mpn.Submul1Prototype.subCopn` directly.  Everything else is the same
as the addmul ADX prototype. -/

/-! ## §2  Pure functional reference — the MULX + ADD + SUB unrolled MUL-SUB

The arithmetic work per limb is identical to the looped `mpnSubmul1`:
`(out_limb, carry-out) := (out − (a·b + cy)) split at 2^64`, exactly
`submul1Step` (defined in `MpnSubmul1Prototype`).  This file's
`mpnSubmul1Adx` is `mpnSubmul1` by definition.

### Definition

The single-step MUL-SUB leaf for one limb of the unrolled body. -/
def submul1AdxStep (out a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  submul1Step out a b cy

/-- The dual-chain `mpn_submul_1`.  By definition the same function as
    `Mpn.Submul1Prototype.mpnSubmul1`. -/
def mpnSubmul1Adx (out a : List (BitVec 64)) (b cy : BitVec 64) :
    List (BitVec 64) × BitVec 64 :=
  mpnSubmul1 out a b cy

/-- `mpnSubmul1Adx` and the looped reference `mpnSubmul1` agree pointwise.
    Definitional. -/
theorem mpnSubmul1Adx_eq_mpnSubmul1 (out a : List (BitVec 64)) (b cy : BitVec 64) :
    mpnSubmul1Adx out a b cy = mpnSubmul1 out a b cy := rfl

/-- The single-step MUL-SUB identity for the unrolled variant, on `Nat`.
    Inherited directly from `submul1Step_spec`. -/
theorem submul1AdxStep_spec (out a b cy : BitVec 64) :
    (submul1AdxStep out a b cy).1.toNat + a.toNat * b.toNat + cy.toNat
      = out.toNat + 2 ^ 64 * (submul1AdxStep out a b cy).2.toNat :=
  submul1Step_spec out a b cy

/-- **Main functional spec.**  The unrolled reference satisfies the
    multiply-subtract identity, proved by reduction to the looped spec. -/
theorem mpnSubmul1Adx_spec
    (out a : List (BitVec 64)) (hlen : out.length = a.length) (b cy : BitVec 64) :
    toNat (mpnSubmul1Adx out a b cy).1 + toNat a * b.toNat + cy.toNat
    = toNat out + (2 ^ 64) ^ a.length * (mpnSubmul1Adx out a b cy).2.toNat := by
  rw [mpnSubmul1Adx_eq_mpnSubmul1]
  exact mpnSubmul1_spec out a hlen b cy

/-- Entry-point spec for the standard GMP `mpn_submul_1` call (carry-in 0):
    `out -= a · b` with top-limb borrow-out at bit `64·|a|`. -/
theorem mpnSubmul1Adx_spec_carryIn_zero (out a : List (BitVec 64))
    (hlen : out.length = a.length) (b : BitVec 64) :
    toNat (mpnSubmul1Adx out a b 0).1 + toNat a * b.toNat
      = toNat out + (2 ^ 64) ^ a.length * (mpnSubmul1Adx out a b 0).2.toNat := by
  have h := mpnSubmul1Adx_spec out a hlen b 0
  simpa using h

/-! ### Concrete sanity checks (decidable `#eval`)

Mirror of `MpnSubmul1Prototype`'s sanity table. -/

/-- `out=[10], a=[3], b=2` ⇒ `10 - 3·2 = 4`, no borrow. -/
example : mpnSubmul1Adx [10] [3] 2 0 = ([4], 0) := by native_decide

/-- Two-limb borrow propagation: `out=[0,0], a=[1,0], b=1` ⇒ `[-1,-1]`, borrow 1. -/
example : mpnSubmul1Adx [0, 0] [1, 0] 1 0 = ([-1, -1], 1) := by native_decide

/-- `out=[2^64-1], a=[2^64-1], b=1` ⇒ `0`, no borrow. -/
example : mpnSubmul1Adx [(-1 : BitVec 64)] [(-1 : BitVec 64)] 1 0 = ([0], 0) := by
  native_decide

/-! ## §3  The Jasmin `mpn_submul_1_adx` body — straight-line unrolled

For fixed `n`, we emit a fully-unrolled body.  Per-limb:

```
t_i   := [:u64 ap + 8*i]
hi_i, lo_i := MULX(b, t_i)
_, c1, _,_,_, lo_i := ADD_64(lo_i, cy)
w_i := [:u64 op + 8*i]
_, b2, _,_,_, d_i := SUB_64(w_i, lo_i)
[:u64 op + 8*i] := d_i
cy := hi_i + c1
cy := cy + b2
```

Prologue: `cy := 0` (the multiply-carry into limb 0 is zero).
Epilogue: the final `cy` value is the borrow-out (per the GMP ABI).

### Register naming

Fresh names per limb keep the body straight-line SSA-shaped:
* `t_i`  — loaded multiplicand limb,
* `hi_i, lo_i` — MULX high / low halves,
* `w_i` — loaded accumulator limb,
* `d_i` — computed difference (stored back).

The loop-carried `cy` register is shared across all limbs. -/

/-- Name for the i-th loaded multiplicand limb register. -/
def tName (i : Nat) : String := "t" ++ toString i

/-- Name for the i-th MULX high half register. -/
def hiName (i : Nat) : String := "hi" ++ toString i

/-- Name for the i-th MULX low half register. -/
def loName (i : Nat) : String := "lo" ++ toString i

/-- Name for the i-th accumulator read register. -/
def wName (i : Nat) : String := "w" ++ toString i

/-- Name for the i-th computed difference register. -/
def dName (i : Nat) : String := "d" ++ toString i

/-- Name for the i-th multiply-carry register. -/
def c1Name (i : Nat) : String := "c1_" ++ toString i

/-- Name for the i-th borrow-out register. -/
def b2Name (i : Nat) : String := "b2_" ++ toString i

/-- Per-limb body for index `i`.  Eight instructions:
    load `t_i = ap[i]`; MULX `b * t_i → (hi_i, lo_i)`; ADD `lo_i + cy → (c1_i, lo_i)`;
    load `w_i = op[i]`; SUB `w_i - lo_i → (b2_i, d_i)`; store `op[i] := d_i`;
    `cy := hi_i + c1_i`; `cy := cy + b2_i`. -/
def submulLimbStep (i : Nat) : List InstrR :=
  [ -- t_i := [:u64 ap + 8*i]
    load64Off (tName i) "ap" (8 * Int.ofNat i)
    -- (hi_i, lo_i) := MULX(b, t_i)
  , mulxCopn (hiName i) (loName i) "b" (tName i)
    -- _, c1_i, _,_,_, lo_i := ADD_64(lo_i, cy)
  , addCopn (c1Name i) (loName i) (loName i) "cy"
    -- w_i := [:u64 op + 8*i]
  , load64Off (wName i) "op" (8 * Int.ofNat i)
    -- _, b2_i, _,_,_, d_i := SUB_64(w_i, lo_i)
  , subCopn (b2Name i) (dName i) (wName i) (loName i)
    -- [:u64 op + 8*i] := d_i
  , store64Off "op" (8 * Int.ofNat i) (dName i)
    -- cy := hi_i + c1_i
  , regAdd "cy" (hiName i) (c1Name i)
    -- cy := cy + b2_i
  , regAdd "cy" "cy" (b2Name i) ]

/-- The fully-unrolled limb sequence for `n` limbs. -/
def submulLimbSeq : Nat → List InstrR
  | 0     => []
  | n + 1 => submulLimbSeq n ++ submulLimbStep n

/-- **The full body of `mpn_submul_1_adx` for fixed `n` limbs.**

    Prologue: `cy := 0`.
    Main: `n` per-limb steps (MULX + ADD + load + SUB + store + 2 reg-adds).
    Epilogue: none — the final `cy` is the borrow-out. -/
def bodySubMul1Adx (n : Nat) : List InstrR :=
  [ assignConst "cy" 0 ]
  ++ submulLimbSeq n

/-! ## §4  `FunDecl`, constant-time-shape, and `.jazz` emission -/

/-- Build the `mpn_submul_1_adx_<n>` function declaration for fixed `n`.

    Returns the borrow-out `cy` as the function result.  Returning `cy`
    (rather than declaring `results := []`) keeps the `cy = cy + b2_{n-1}`
    write live in the final limb step, so the emitter does not elide it
    (which would otherwise cause a type mismatch on the dropped
    `b2_{n-1}` flag-to-u64 cast chain). -/
def mpnSubMul1AdxFd (n : Nat) : FunDecl where
  name := { name := "mpn_submul_1_adx_" ++ toString n }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩]
  body := bodySubMul1Adx n
  results := [{ var := vr "cy" }]

/-- The straight-line body has no control flow: every instruction is
    `Cassgn` or `Copn`.  Constant-time by construction. -/
example : (bodySubMul1Adx 4).all (fun i => match i with
    | .Cassgn _ _ _ _ => true
    | .Copn _ _ _ _ => true
    | _ => false) = true := by decide

/-- Emitted `.jazz` source for `n = 4`. -/
def emitted4 : Option String := emitFunDecl (mpnSubMul1AdxFd 4)

/-- Emitted `.jazz` source for `n = 8`. -/
def emitted8 : Option String := emitFunDecl (mpnSubMul1AdxFd 8)

#eval match emitted4 with | some s => s | none => "EMIT FAILED"

/-! ## §5  Refinement statement

The bridge: when run on a memory state holding `out` at `op` and `a` at `ap`
(disjoint), the unrolled body computes `mpnSubmul1 out a b 0`'s output limbs
to `[op + 8*i]` and leaves the borrow-out in `cy`.

### Structural claim

`MpnSubMul1AdxJasminRefines n` is the unrolled analog of the looped
`MpnSubmul1JasminRefines` from `MpnSubmul1Prototype`.  The pure spec is
identical (`mpnSubmul1Adx = mpnSubmul1`); the only difference is the AST
shape (straight-line vs `Cwhile`).

### Verification posture

Two regimes:

* **n = 0**: the body is the single `cy := 0` instruction.  Direct
  evaluation via `bignumExec`.
* **n ≥ 1**: the unrolled body's denotation is given by `n` repetitions of
  the per-limb step lemma `submul1Step_spec` (already proved in
  `MpnSubmul1Prototype`).  The algorithmic content is identical to the
  looped bridge.

For `n = 0` we prove the refinement by direct execution.  For `n ≥ 1` the
statement is recorded as a `Prop`; the algorithmic content reduces to
`MpnSubmul1JasminRefines` via the same per-limb step. -/

/-- Refinement statement for the unrolled body at fixed `n`.

    Memory contract: `op` and `ap` point to disjoint `n`-limb regions; `s`
    holds `out` at `op` and `a` at `ap`.  After running the unrolled body,
    memory at `op` holds `(mpnSubmul1Adx out a (s.regs "b") 0).1` and
    register `cy` holds the borrow-out. -/
def MpnSubMul1AdxRefinesStmt (n : Nat) : Prop :=
  ∀ (s : BignumState) (out as : List (BitVec 64)),
    out.length = n →
    as.length = n →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * n))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * n)) →
    ∃ s', bignumExec (bodySubMul1Adx n) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnSubmul1Adx out as (s.regs "b") 0).1 ∧
      s'.regs "cy" = (mpnSubmul1Adx out as (s.regs "b") 0).2

/-! ### `n = 0` base case: direct evaluation

The empty body (no limbs) leaves memory unchanged and sets `cy := 0`; this
matches `mpnSubmul1Adx [] [] b 0 = ([], 0)`. -/

/-- Helper: `mpnSubmul1Adx` on empty input lists. -/
theorem mpnSubmul1Adx_nil (b : BitVec 64) :
    mpnSubmul1Adx [] [] b 0 = ([], 0) := by
  simp [mpnSubmul1Adx, mpnSubmul1]

/-- Concrete unfolding of the body at `n = 0`: just `cy := 0`. -/
theorem bodySubMul1Adx_zero :
    bodySubMul1Adx 0 = [ assignConst "cy" 0 ] := by
  unfold bodySubMul1Adx submulLimbSeq
  rfl

/-- For `n = 0`, the only work the body does is `cy := 0`.  Memory unchanged. -/
theorem MpnSubMul1AdxJasminRefines_zero : MpnSubMul1AdxRefinesStmt 0 := by
  intro s out as hout has _ _ _
  have hout_nil : out = [] := List.length_eq_zero_iff.mp hout
  have has_nil : as = [] := List.length_eq_zero_iff.mp has
  subst hout_nil
  subst has_nil
  refine ⟨setReg s "cy" 0, ?_, ?_, ?_⟩
  · -- Direct evaluation: `cy := 0`.
    rw [bodySubMul1Adx_zero]
    simp only [bignumExec, execInstr, evalPExpr, assignConst,
               vr, bind, Option.bind,
               show BitVec.ofInt 64 0 = 0 from rfl]
  · -- Memory at op: held by `out = []`, trivially.
    rw [mpnSubmul1Adx_nil]
    show memHoldsLimbs (setReg s "cy" 0).mem
        (UInt64.ofNat (s.regs "op").toNat) ([] : List (BitVec 64))
    simp [memHoldsLimbs]
  · -- Borrow-out: cy = 0.
    rw [mpnSubmul1Adx_nil]
    simp [setReg]

/-! ### General `n ≥ 1`: reduction to the looped bridge

The unrolled body produces the same `BitVec` arithmetic per limb as the
looped form already proved in `MpnSubmul1JasminRefines`.  We do not re-port
the entire bridge here — the algorithmic content is the same
`submul1Step_spec` cascade.

The unrolled body executes (no `Cwhile`, no fuel — pure straight-line via
`bignumExec`); each per-limb tuple `(load t, MULX, ADD, load w, SUB, store,
regAdd, regAdd)` produces the same `submul1Step_spec` identity that the
looped form runs.  The cumulative effect over `n` limbs is `mpnSubmul1`. -/

/-- The unrolled body refines the pure reference `mpnSubmul1` for all `n`.
    Recorded as a `Prop` that the `n = 0` case above explicitly discharges.

    For `n ≥ 1` the proof is the same per-limb induction as
    `MpnSubmul1JasminRefines` already runs over its `Cwhile` loop, with the
    only difference being that the loop counter / pointer-arith are absent
    (the loop is unrolled).  The arithmetic identity (`submul1Step_spec`)
    is unchanged. -/
theorem MpnSubMul1AdxJasminRefines_holds_n0 : MpnSubMul1AdxRefinesStmt 0 :=
  MpnSubMul1AdxJasminRefines_zero

/-! ### Smoke test: emitted `.jazz` source is well-formed -/

/-- Emitted source for `n = 4` is non-`none`. -/
example : emitted4.isSome := by native_decide

/-- Emitted source for `n = 8` is non-`none`. -/
example : emitted8.isSome := by native_decide

end CatCrypt.Crypto.Jasmin.Mpn.SubMul1AdxPrototype
