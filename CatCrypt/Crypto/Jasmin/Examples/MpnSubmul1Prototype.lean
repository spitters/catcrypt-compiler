/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype

set_option autoImplicit false

/-!
# Phase 2 — verified variable-length `mpn_submul_1` by template reuse

**EXPERIMENTAL FILE.**  Phase-2 companion to `MpnAddmul1Prototype.lean` /
`MpnMul1Prototype.lean`.  It proves the GMP kernel `mpn_submul_1`
(`out[] -= a[] * b`, with `b` a single limb and a u64 borrow/carry threaded
across iterations) end-to-end against the Jasmin `Cwhile` semantics —
reusing the addmul_1 / mul_1 loop-invariant machinery verbatim.

`mpn_submul_1` is the multiply-*subtract* inner loop: a multiply-decrement
that subtracts the scalar product `a[i]·b` from the running accumulator
`out[i]`.  Together with `mpn_addmul_1` it is one of the two inner loops of
Knuth's Algorithm D long division (`mpn_sub_ddmmss`-style quotient-digit
correction subtracts `q̂·divisor` via `mpn_submul_1`).

## What is reused (kernel-agnostic, imported from `MpnMul1Prototype` /
   `MpnAddmul1Prototype` / `MpnAddPrototype`)

* **Memory algebra** (`load64Mem_store64_same`, `load64Mem_store64_disjoint`,
  `memHoldsLimbs_store64_frame`).
* **The `Cwhile` fuel exit rule** (`bignumExecFuel_loop_exit`); the step rule is
  re-instantiated locally for this body (`bignumExecFuel_loopSubmul_step`).
* **The memory-frame plumbing** (`memHoldsLimbs`, `range_shift_subset`,
  `range_head_subset`, `disjoint_mono`, `range_op_head_tail_disjoint`,
  `disjoint_range_lt`).
* **The counter algebra** (`ofNat64_toNat`, `ofNat64_succ_ne_zero`,
  `ofNat64_succ_sub_one`, `regAddr`, `regAddr_advance`, `bv_uint_roundtrip`,
  the `setReg`/`storeMem` projection simp lemmas).
* **The multiply leaves** (`mulx_toNat`, `mulx_hi_le`, `addCarry_carry_le`,
  `addCarry_spec`) and the local instruction-builders (`vr`, `pv`, `loadAt0`,
  `storeAt0`, `binImm`, `regAdd`, `mulxCopn`, `addCopn`, the guard lemmas).

## What is genuinely new vs `mpn_addmul_1`

* §2–§3: the `subBorrow` leaf identity (`subBorrow_spec`, `subBorrow_carry_le`)
  — the SUB-with-borrow-out primitive is *not* used by addmul_1 (which only
  uses two `#ADD_64`s); `mpn_sub_n` uses `subBorrowIn`, a different primitive.
* §2: the pure reference `mpnSubmul1` + the one-limb `submul1Step` leaf.  The
  step computes the 128-bit product-plus-carry `a·b + cy = hi'·2^64 + lo'`
  (one `#MULX` + one `#ADD_64`), then subtracts `lo'` from `out[i]` with borrow
  (`#SUB_64`), and recombines `cy = hi' + borrow`.
* §5: the one-iteration state update (`#MULX`, `#ADD_64`, **`#SUB_64`**, store,
  two reg-adds).

The op-read-then-store invariant (the body reads `out[i]` from `op` before it
stores back) is structurally **identical** to `mpn_addmul_1`: `op` plays a dual
role (read like `ap`, head-stored each iteration), framed across the head store
via `load64Mem_store64_disjoint` (op-vs-ap) and `range_op_head_tail_disjoint`
(op-internal head/tail non-aliasing).

The third carry `cy = hi + c1 + b2` never wraps: from the exact per-limb
identity `diff + a·b + cy = out + 2^64·cy_out` with `diff ≥ 0`, `out ≥ 0`, and
`a·b + cy ≤ (2^64−1)^2 + (2^64−1) = 2^128 − 2^64`, we get
`2^64·cy_out = diff + a·b + cy − out ≤ (2^64−1) + (2^128−2^64) = 2^128−1`, so
`cy_out < 2^64`.

## Functional spec

`mpnSubmul1 out a b cy = (result, carry-out)` satisfies the multiply-subtract
identity (over equal-length `|out| = |a|`), stated all-additions to stay
Nat-safe:

```
toNat result + toNat a · b = toNat out + (2^64)^|a| · carry-out
```

i.e. (carry-in `0`)  `out[] -= a[] * b`, with the top borrow at bit `64·|a|`.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnSubmul1Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype

/-! ## §1  The Jasmin `mpn_submul_1` body — runtime `Cwhile` loop

We reuse the instruction-builders from `MpnMul1Prototype` (`vr`, `pv`,
`loadAt0`, `storeAt0`, `binImm`, `regAdd`, `mulxCopn`, `addCopn`, `flag_pre`,
`flag_post`).  The body differs from `loopBodyAddmul` only by the polarity of
the accumulator combine: where addmul_1 does a second `#ADD_64` of `out[i]`,
submul_1 does a `#SUB_64` of the product low word *from* `out[i]`, and the
final carry recombination adds the *borrow* rather than a second carry. -/

/-- `_, b2, _, _, _, r = #SUB_64(a, b);` — subtract-with-borrow-out, same
    6-LVal bundle shape `[of, cf, sf, pf, zf, dst]` as `#ADD_64` (the
    interpreter routes both through `writeSubBundle`).  Captures the borrow-out
    `b2` (position 1) and the difference `r` (position 5). -/
def subCopn (b2Name rName aName bName : String) : InstrR :=
  .Copn (flag_pre ++ [.Lvar { var := vr b2Name }] ++ flag_post
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"SUB_64"⟩)
        [pv aName, pv bName]

/-- One loop iteration body for `mpn_submul_1`:
    ```
    t       = [:u64 ap + 0];
    hi, lo  = #MULX(b, t);
    _, c1, _,_,_, lo  = #ADD_64(lo, cy);    -- lo' = lo + cy, carry c1
    w       = [:u64 op + 0];                -- read out[i]
    _, b2, _,_,_, dlo = #SUB_64(w, lo);     -- dlo = out[i] - lo', borrow b2
    [:u64 op + 0] = dlo;                    -- store accumulated low word
    cy      = hi + c1;                      -- hi'  (= (a·b + cy)/2^64)
    cy      = cy + b2;                      -- hi' + borrow (never wraps)
    ap += 8; op += 8;
    n  -= 1;
    ```
    `cy` is initialised to 0 before the loop (first iteration's `#ADD_64` adds
    `0`); the scalar multiplier sits in register `b` (= `bp`) and is never
    advanced.  Like `loopBodyAddmul`, `op` is *read* (into `w`) before it is
    *stored*, realising the multiply-subtract. -/
def loopBodySubmul : List InstrR :=
  [ loadAt0 "t" "ap"
  , mulxCopn "hi" "lo" "b" "t"
  , addCopn "c1" "lo" "lo" "cy"
  , loadAt0 "w" "op"
  , subCopn "b2" "dlo" "w" "lo"
  , storeAt0 "op" "dlo"
  , regAdd "cy" "hi" "c1"
  , regAdd "cy" "cy" "b2"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_submul_1`:
    ```
    cy = 0;
    while (n != 0) { <loopBodySubmul> }
    ```
    `cy` holds the final borrow/carry (the GMP `mpn_submul_1` ABI returns it). -/
def bodySubmul : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySubmul ]

/-- `mpn_submul_1(op, ap, b, n)` as a Jasmin `FunDecl`.  Void return (output via
    `op`, which is read-modify-written); SysV ABI `rdi=op, rsi=ap, rdx=b, rcx=n`
    — `b` (= register `bp`) is the scalar multiplier, passed by value. -/
def mpnSubmul1Fd : FunDecl where
  name := { name := "mpn_submul_1" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩, ⟨{ var := vr "n" }⟩]
  body := bodySubmul
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the public
    length `n`, never a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodySubmul = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnSubmul1Fd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional reference + the one-limb MUL-SUB step

The new arithmetic leaf vs addmul_1 is `subBorrow` (the SUB-with-borrow-out
primitive): `subBorrow a b = (borrow, a - b)` with `borrow = [a < b]`.  We
prove its `toNat` identity and one-bit borrow bound here (addmul_1 never needed
them; `mpn_sub_n` uses the *three*-argument `subBorrowIn` instead). -/

/-- `subBorrow` identity: `diff + b = a + 2^64·borrow`.  The executable
    analogue used by the MUL-SUB step. -/
theorem subBorrow_spec (a b : BitVec 64) :
    (subBorrow a b).2.toNat + b.toNat
      = a.toNat + 2 ^ 64 * (subBorrow a b).1.toNat := by
  have ha := a.isLt; have hb := b.isLt
  simp only [subBorrow, BitVec.ult, decide_eq_true_eq, BitVec.toNat_sub]
  split_ifs with h
  · -- wrapped: a < b, so a - b underflows; borrow 1.
    simp only [show ((1 : BitVec 64).toNat) = 1 from rfl]
    rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; omega
  · -- no underflow; borrow 0.
    simp only [show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.not_lt] at h ⊢
    rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; omega

/-- `subBorrow` borrow-out is a single bit. -/
theorem subBorrow_carry_le (a b : BitVec 64) : (subBorrow a b).1.toNat ≤ 1 := by
  simp only [subBorrow]
  split_ifs <;> simp

/-- One `mpn_submul_1` step on `BitVec 64`: multiply limb `a` by the scalar `b`,
    add the running carry `cy`, and subtract the resulting low word from the
    accumulator limb `out`, splitting into `(out_limb, carry-out)`.

    * `(hi, lo) = mulx b a`
    * `(c1, lo1) = addCarry lo cy`        — `lo1 = lo + cy`,  carry `c1`
    * `(b2, dlo) = subBorrow out lo1`     — `dlo = out − lo1`, borrow `b2`
    * `out_limb = dlo`, `carry-out = hi + c1 + b2` (never wraps).

    Here `hi' := hi + c1 = (a·b + cy)/2^64`, `lo1 = (a·b + cy) mod 2^64`, and the
    carry-out is `hi' + borrow`. -/
def submul1Step (out a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  let (hi, lo) := mulx b a
  let (c1, lo1) := addCarry lo cy
  let (b2, dlo) := subBorrow out lo1
  (dlo, hi + c1 + b2)

/-- Pure reference for `mpn_submul_1`: multiply-subtract a limb list `a` by a
    scalar `b` from accumulator `out`, threading a u64 carry/borrow `cy`.
    Returns `(result limbs, final carry-out)`.  Recurses in lockstep over
    `out`/`a`; the spec below is stated for equal-length inputs.  This is exactly
    the carry chain the emitted `while (n != 0)` loop walks, limb by limb. -/
def mpnSubmul1 : List (BitVec 64) → List (BitVec 64) → BitVec 64 → BitVec 64 →
    (List (BitVec 64) × BitVec 64)
  | o :: os, a :: as, b, cy =>
      let (r, cy') := submul1Step o a b cy
      let (rs, fcy) := mpnSubmul1 os as b cy'
      (r :: rs, fcy)
  | _, _, _, cy => ([], cy)

/-! ## §3  Functional spec: the carry-chain invariant

`bv_decide` cannot close an unbounded loop; the inductive invariant is the
per-limb multiply-subtract identity, fed by the §2 leaf.  The multiply leaves
(`mulx_toNat`, `mulx_hi_le`, `addCarry_carry_le`, `addCarry_spec`) are imported
from `MpnMul1Prototype`; the `subBorrow` leaves are §2. -/

/-- The single-step MUL-SUB identity, on `Nat`:
    `submul1Step out a b cy` produces `(o', cy')` with
    `o' + a·b + cy = out + 2^64·cy'`.

    The carry `cy' = hi + c1 + b2` is bounded by the exact 128-bit identity:
    `2^64·cy' = o' + a·b + cy − out ≤ (2^64−1) + (2^128−2^64) = 2^128−1`, so
    `cy' < 2^64` and the three-summand register never wraps. -/
theorem submul1Step_spec (out a b cy : BitVec 64) :
    (submul1Step out a b cy).1.toNat + a.toNat * b.toNat + cy.toNat
      = out.toNat + 2 ^ 64 * (submul1Step out a b cy).2.toNat := by
  -- Unfold the projections.
  rw [show (submul1Step out a b cy).1
        = (subBorrow out (addCarry (mulx b a).2 cy).2).2 from rfl,
      show (submul1Step out a b cy).2
        = (mulx b a).1 + (addCarry (mulx b a).2 cy).1
            + (subBorrow out (addCarry (mulx b a).2 cy).2).1 from rfl]
  set hi := (mulx b a).1 with hhi
  set lo := (mulx b a).2 with hlo
  set c1 := (addCarry lo cy).1 with hc1
  set lo1 := (addCarry lo cy).2 with hlo1
  set b2 := (subBorrow out lo1).1 with hb2
  set dlo := (subBorrow out lo1).2 with hdlo
  -- mulx: lo + 2^64·hi = b·a = a·b.
  have hmulx : lo.toNat + 2 ^ 64 * hi.toNat = a.toNat * b.toNat := by
    rw [hlo, hhi, mulx_toNat b a]; ring
  -- first addCarry: lo1 + 2^64·c1 = lo + cy.
  have hadd1 : lo1.toNat + 2 ^ 64 * c1.toNat = lo.toNat + cy.toNat := by
    rw [hlo1, hc1, addCarry_spec lo cy]
  -- subBorrow: dlo + lo1 = out + 2^64·b2.
  have hsub : dlo.toNat + lo1.toNat = out.toNat + 2 ^ 64 * b2.toNat := by
    rw [hdlo, hb2, subBorrow_spec out lo1]
  -- carry bounds.
  have hc1le : c1.toNat ≤ 1 := by rw [hc1]; exact addCarry_carry_le lo cy
  have hb2le : b2.toNat ≤ 1 := by rw [hb2]; exact subBorrow_carry_le out lo1
  have hhile : hi.toNat ≤ 2 ^ 64 - 2 := by rw [hhi]; exact mulx_hi_le a b
  have hdlobound : dlo.toNat < 2 ^ 64 := dlo.isLt
  have hlo1bound : lo1.toNat < 2 ^ 64 := lo1.isLt
  have hlobound : lo.toNat < 2 ^ 64 := lo.isLt
  have hcybound : cy.toNat < 2 ^ 64 := cy.isLt
  have houtbound : out.toNat < 2 ^ 64 := out.isLt
  have habound : a.toNat < 2 ^ 64 := a.isLt
  have hbbound : b.toNat < 2 ^ 64 := b.isLt
  -- `a·b + cy ≤ (2^64-1)^2 + (2^64-1) = 2^128 - 2^64`.
  have hprodle : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  -- From the three identities, `o' + a·b + cy = out + 2^64·(hi + c1 + b2)`.
  have hcombine : dlo.toNat + a.toNat * b.toNat + cy.toNat
      = out.toNat + 2 ^ 64 * (hi.toNat + c1.toNat + b2.toNat) := by
    have := hmulx; have := hadd1; have := hsub; ring_nf; omega
  -- `dlo ≥ 0`, `out < 2^64`, `a·b + cy ≤ 2^128 - 2^64` give `hi + c1 + b2 < 2^64`.
  have hcarrybound : hi.toNat + c1.toNat + b2.toNat < 2 ^ 64 := by
    have hkey : (2 : Nat) ^ 64 - 1 = 18446744073709551615 := by norm_num
    have hnum : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 65 + 1 := by norm_num
    omega
  -- The combined three-summand carry register never wraps.
  have hhc1 : (hi + c1).toNat = hi.toNat + c1.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsum : (hi + c1 + b2).toNat = hi.toNat + c1.toNat + b2.toNat := by
    rw [BitVec.toNat_add, hhc1, Nat.mod_eq_of_lt (by omega)]
  rw [hsum]
  -- Combine the three identities linearly; omega closes.
  omega

/-- **Main functional spec — proved by induction on the limb list.**

    For equal-length limb lists `out, a`, scalar `b`, and carry-in `cy`, the
    pure reference `mpnSubmul1` satisfies the multiply-subtract identity:
    the denotation of the output limbs plus `toNat a · b` equals `toNat out`
    plus the final carry-out shifted to bit `64·|a|`.

    This is the inductive invariant the emitted `while (n != 0)` loop maintains:
    each iteration peels one limb (`submul1Step_spec`), and the IH carries the
    identity over the `2^64`-scaled tail. -/
theorem mpnSubmul1_spec :
    ∀ (out a : List (BitVec 64)), out.length = a.length → ∀ (b cy : BitVec 64),
      toNat (mpnSubmul1 out a b cy).1 + toNat a * b.toNat + cy.toNat
      = toNat out + (2 ^ 64) ^ a.length * (mpnSubmul1 out a b cy).2.toNat := by
  intro out
  induction out with
  | nil =>
    intro a hlen b cy
    cases a with
    | nil => simp [mpnSubmul1, toNat]
    | cons _ _ => simp at hlen
  | cons o os ih =>
    intro a hlen b cy
    cases a with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      set p := submul1Step o a b cy with hp
      have hstep := submul1Step_spec o a b cy
      rw [← hp] at hstep
      set q := mpnSubmul1 os as b p.2 with hq
      have htail := ih as hlen' b p.2
      rw [← hq] at htail
      have hunfold : mpnSubmul1 (o :: os) (a :: as) b cy = (p.1 :: q.1, q.2) := by
        simp only [mpnSubmul1, hp, hq]
      rw [hunfold]
      simp only [toNat, List.length_cons]
      have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      -- IH scaled by 2^64 + head step (submul1Step_spec) close the linear goal.
      have hkey : 2 ^ 64 * toNat q.1 + 2 ^ 64 * (toNat as * b.toNat) + 2 ^ 64 * p.2.toNat
          = 2 ^ 64 * toNat os + 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat) := by
        have := congrArg (2 ^ 64 * ·) htail
        simpa [Nat.mul_add, Nat.add_assoc] using this
      have hmono : 2 ^ 64 * (2 ^ 64) ^ as.length * q.2.toNat
          = 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat) := by ring
      rw [hmono]
      have hexpand : (a.toNat + 2 ^ 64 * toNat as) * b.toNat
          = a.toNat * b.toNat + 2 ^ 64 * (toNat as * b.toNat) := by ring
      rw [hexpand]
      omega

/-- The usual entry point: carry-in 0.  `mpn_submul_1` with no incoming carry
    multiply-subtracts a bignum from an accumulator; the result plus
    `toNat a · b` equals `toNat out` plus the carry-out at bit `64·|a|` (the GMP
    `mpn_submul_1` contract — the return value is the borrow/carry-out). -/
theorem mpnSubmul1_spec_carryIn_zero (out a : List (BitVec 64))
    (hlen : out.length = a.length) (b : BitVec 64) :
    toNat (mpnSubmul1 out a b 0).1 + toNat a * b.toNat
      = toNat out + (2 ^ 64) ^ a.length * (mpnSubmul1 out a b 0).2.toNat := by
  have h := mpnSubmul1_spec out a hlen b 0
  simpa using h

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `out=[10], a=[3], b=2`: `10 - 3·2 = 4`, no borrow. -/
example : mpnSubmul1 [10] [3] 2 0 = ([4], 0) := by native_decide

/-- Two-limb borrow propagation: `out=[0,0], a=[1,0], b=1` ⇒ limb 0 is
    `0 - 1 = 2^64-1` with borrow 1; limb 1 is `0 - 0·1 - 1 = 2^64-1` with borrow
    1; final carry-out `1`.  So `([-1,-1], 1)`. -/
example : mpnSubmul1 [0, 0] [1, 0] 1 0 = ([-1, -1], 1) := by native_decide

/-- `out=[2^64-1], a=[2^64-1], b=1`: `(2^64-1) - (2^64-1)·1 = 0`, no borrow. -/
example : mpnSubmul1 [(-1 : BitVec 64)] [(-1 : BitVec 64)] 1 0 = ([0], 0) := by
  native_decide

/-- Underflow into the carry: `out=[0], a=[1], b=1` ⇒ `0 - 1 = 2^64-1` with a
    borrow of `1` (the final carry-out at bit 64). -/
example : mpnSubmul1 [0] [1] 1 0 = ([-1], 1) := by native_decide

#eval toNat (mpnSubmul1 [10] [3] 2 0).1 + toNat ([3] : List (BitVec 64)) * 2 -- 10 - 6 = 4

/-! ## §4  MULX / ADD / SUB bridge: executable intrinsics match the pure step

The emitted `#MULX` runs `BignumExec.mulx`; the emitted `#ADD_64` runs
`BignumExec.addCarry`; the emitted `#SUB_64` runs `BignumExec.subBorrow`.  The
pure `submul1Step` is *defined* directly in terms of these, so the bridge is
definitional — recorded here for clarity. -/

theorem submul1Step_out (out a b cy : BitVec 64) :
    (subBorrow out (addCarry (mulx b a).2 cy).2).2 = (submul1Step out a b cy).1 := rfl

theorem submul1Step_carry (out a b cy : BitVec 64) :
    (mulx b a).1 + (addCarry (mulx b a).2 cy).1
        + (subBorrow out (addCarry (mulx b a).2 cy).2).1
      = (submul1Step out a b cy).2 := rfl

/-! ## §5  One loop iteration as an explicit state update

`loopBodySubmul` is straight-line, so it runs via `bignumExec`.  This lemma
computes the exact effect of one pass: load `a` from `ap`, MULX by `b`, add the
running carry, **load `out` from `op`**, subtract the product low word from it
with borrow, store the difference at `op`, recombine `cy = hi + c1 + b2`,
advance `ap`/`op` by 8 and decrement `n`.

As in addmul_1, the body reads `op[0]` (into `w`) before storing, so the step
needs the *input* op-limb (`hout`). -/

theorem bignumExec_loopBodySubmul_step (s : BignumState) (out a : BitVec 64)
    (cy : BitVec 64)
    (hcy : s.regs "cy" = cy)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hout : load64Mem s.mem (regAddr s "op") = some (UInt64.ofNat out.toNat)) :
    ∃ s', bignumExec loopBodySubmul s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (submul1Step out a (s.regs "b") cy).1.toNat) ∧
      s'.regs "cy" = (submul1Step out a (s.regs "b") cy).2 ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 ∧
      s'.regs "b" = s.regs "b" := by
  simp only [loopBodySubmul, MpnMul1Prototype.loadAt0, MpnMul1Prototype.mulxCopn,
             MpnMul1Prototype.addCopn, subCopn, MpnMul1Prototype.storeAt0,
             MpnMul1Prototype.regAdd, MpnMul1Prototype.binImm,
             MpnMul1Prototype.flag_pre, MpnMul1Prototype.flag_post,
             bignumExec, execInstr, evalPExpr, MpnMul1Prototype.pv,
             MpnMul1Prototype.resolveAddr_reg, MpnMul1Prototype.vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append,
             writeMulxBundle, writeSubBundle]
  -- Resolve the `ap` load (offset 0), fire it (`ha`), decode the word.
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- Now the `op` load (offset 0): only register writes so far, so memory is still
  -- `s.mem` and the `op` register is unchanged.  Collapse the register chain,
  -- reduce the `op + 0` address, fire `hout`, decode the word.
  simp only [setReg_regs, setReg_mem, String.reduceEq, ↓reduceIte, reduceIte,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             Option.bind_some, bind, Option.bind]
  rw [show s.regs "op" + 0 = s.regs "op" from by bv_decide]
  rw [hout]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.  Read off the store, the `cy`
  -- register, the register advances, and `b` invariance.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte, hcy,
               submul1Step, show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-- `loopBodySubmul` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodySubmul_straightLine : InstrR.bodyIsStraightLine loopBodySubmul := by
  simp only [loopBodySubmul, loadAt0, mulxCopn, addCopn, subCopn, storeAt0, regAdd,
             binImm, InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodySubmul` is non-control. -/
theorem loopBodySubmul_nonControl : ∀ i ∈ loopBodySubmul, i.isNonControl := by
  intro i hi
  simp only [loopBodySubmul, loadAt0, mulxCopn, addCopn, subCopn, storeAt0, regAdd,
             binImm, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §6  One `Cwhile` iteration over `bignumExecFuel`

The imported `bignumExecFuel_loop_step` is hardcoded to add's `loopBody`, so we
re-instantiate the *same* proof for `loopBodySubmul`.  `bignumExecFuel_loop_exit`
is already generic over the body, so it is reused directly. -/

/-- **Forward one-iteration rule** for `loopBodySubmul` — same proof shape as the
    imported `bignumExecFuel_loop_step`, specialised to the MUL-SUB body. -/
theorem bignumExecFuel_loopSubmul_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodySubmul s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodySubmul] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodySubmul] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodySubmul s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodySubmul s
        loopBodySubmul_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodySubmul [.Cwhile [] cond loopBodySubmul]
        loopBodySubmul_nonControl s s_mid s' hsl hrec]

/-! ## §7  Assembly: `MpnSubmul1JasminRefines`

The full bridge.  Structurally mirrors `mpnAddmul1_loop` →
`MpnAddmul1JasminRefines`, with `op` playing a *dual* role: it is both the input
accumulator (read limb by limb, with the unread tail framed across the head
store — like `ap`) and the output buffer (head store each iteration).  Each step
peels one limb via `bignumExec_loopBodySubmul_step` and
`bignumExecFuel_loopSubmul_step`, preserving:

* the unread `ap` suffix across the `op[i]` store (`load64Mem_store64_disjoint`,
  op-vs-ap disjointness), and
* the unread `op` suffix across the `op[i]` store
  (`range_op_head_tail_disjoint`: the head store block `[op,op+8)` is disjoint
  from the op tail `[op+8, …)`),

and threading the u64 carry/borrow via `submul1Step`.  The scalar `b` lives in a
register and is read-only, so only op-vs-ap separation (plus op-internal
head/tail non-aliasing) is needed. -/

/-- The bridge statement.  The scalar `b` is `s.regs "b"`.  Memory holds the
    accumulator `out` at `op` AND the multiplicand `a` at `ap`; only op-vs-ap
    disjointness is required (the `b` register is never dereferenced, and the
    op buffer's internal head/tail non-aliasing follows from the op-vs-ap
    separation). -/
def MpnSubmul1RefinesStmt : Prop :=
  ∀ (s : BignumState) (out as : List (BitVec 64)) (fuel : Nat),
    out.length = as.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodySubmul s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnSubmul1 out as (s.regs "b") 0).1 ∧
      s'.regs "cy" = (mpnSubmul1 out as (s.regs "b") 0).2

/-- **The loop, by induction on the limb list.**  Mirror of `mpnAddmul1_loop`,
    with `op` read-then-stored each iteration (dual role).  The frame conclusion
    (last conjunct) is over blocks disjoint from BOTH the op region and the ap
    region. -/
theorem mpnSubmul1_loop :
    ∀ (out as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      out.length = as.length →
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "op") out →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySubmul] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnSubmul1 out as (s.regs "b") cy).1 ∧
        s'.regs "cy" = (mpnSubmul1 out as (s.regs "b") cy).2 ∧
        s'.regs "b" = s.regs "b" ∧
        (∀ bb, MemoryModel.Disjoint (range bb 8)
              (range (regAddr s "op") (8 * as.length)) →
            MemoryModel.Disjoint (range bb 8)
              (range (regAddr s "ap") (8 * as.length)) →
            load64Mem s'.mem bb = load64Mem s.mem bb) := by
  intro out
  induction out with
  | nil =>
    intro as s cy extra hlen hcy hn _ _ _
    cases as with
    | cons _ _ => simp at hlen
    | nil =>
      have hn0 : s.regs "n" = 0 := by simpa using hn
      refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
      · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
          simp only [List.length_nil]; omega
        rw [this]
        exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodySubmul s
          (MpnMul1Prototype.evalPExpr_loopCond_false s hn0)
      · simp [mpnSubmul1, memHoldsLimbs]
      · simpa [mpnSubmul1] using hcy
      · rfl
      · intro bb _ _; rfl
  | cons o os ih =>
    intro as s cy extra hlen hcy hn hop hap hdoa
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      have hpos : 0 < 8 * (as.length + 1) := by omega
      have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hop_head, hop_tail⟩ := hop
      obtain ⟨hap_head, hap_tail⟩ := hap
      -- Run one iteration: reads `out`-head from `op`, `a`-head from `ap`.
      obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
        bignumExec_loopBodySubmul_step s o a cy hcy hap_head hop_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0
          (UInt64.ofNat (submul1Step o a (s.regs "b") cy).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      -- The head store block `[op0, op0+8)` is disjoint from:
      --  (i) the ap tail `[ap+8, …)`  — op-vs-ap, and
      --  (ii) the op tail `[op0+8, …)` — op-internal non-aliasing.
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hsep_op : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
        range_op_head_tail_disjoint op0 as.length (by omega)
      -- Frame the `ap` tail and the `op` tail across the head store.
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
          hdoa_store_aptail hap_tail
      have hop1 : memHoldsLimbs s1.mem (regAddr s1 "op") os := by
        rw [hra_op, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (op0 + 8) op0 _ os
          (by rw [hlen']; exact hsep_op) hop_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "ap") (8 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hcy1 : s1.regs "cy" = (submul1Step o a (s.regs "b") cy).2 := hs1_cy
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      -- Apply the IH on the tail with carry `(submul1Step o a (s.regs "b") cy).2`.
      obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, hs'_frame⟩ :=
        ih as s1 (submul1Step o a (s.regs "b") cy).2 extra hlen' hcy1 hn1 hop1 hap1 hdoa1
      refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loopSubmul_step emptyRegistry (2 * as.length + 2 + extra) _
          s s1 s' (MpnMul1Prototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Memory at op: head limb at `op0` (preserved by IH frame), tail by IH.
        rw [hmem1] at hs'_frame
        refine ⟨?_, ?_⟩
        · -- `load64Mem s'.mem op0 = head_result`, via IH frame + read-back.
          rw [hs'_frame op0 (by rw [hra_op]; exact hsep_op)
                (by rw [hra_ap]; exact hdoa_store_aptail)]
          have hread := load64Mem_store64_same s.mem op0
            (UInt64.ofNat (submul1Step o a (s.regs "b") cy).1.toNat)
          rw [hread]
          -- head of `(mpnSubmul1 (o::os) (a::as) b cy).1` is `(submul1Step …).1`.
          rfl
        · -- tail: from IH (op base `op0+8`), with `s1.regs "b" = s.regs "b"`.
          have hthis := hs'_mem
          rw [hra_op, hs1_b] at hthis
          exact hthis
      · -- carry-out register.
        rw [hs'_cy, hs1_b]; simp only [mpnSubmul1]
      · -- `b` register invariant.
        rw [hs'_b, hs1_b]
      · -- frame: `bb`-block disjoint from both op and ap regions ⇒ unchanged.
        intro bb hbb_op hbb_ap
        rw [hmem1] at hs'_frame
        have hbb_op_tail : MemoryModel.Disjoint (range bb 8)
            (range (regAddr s1 "op") (8 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
          exact range_shift_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        have hbb_ap_tail : MemoryModel.Disjoint (range bb 8)
            (range (regAddr s1 "ap") (8 * as.length)) := by
          rw [hra_ap]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_ap
          exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
        rw [hs'_frame bb hbb_op_tail hbb_ap_tail]
        have hbb_head : MemoryModel.Disjoint (range bb 8) (range (regAddr s "op") 8) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
          exact range_head_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        rw [load64Mem_store64_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-- **The bridge, fully proved.**  `mpnSubmul1Fd.body` (the emitted
    `cy := 0; while (n != 0) { loopBodySubmul }`) refines the pure reference
    `mpnSubmul1` over byte memory.  Mirror of `MpnAddmul1JasminRefines`, with the
    accumulator combine subtracting (rather than adding) the scalar product. -/
theorem MpnSubmul1JasminRefines : MpnSubmul1RefinesStmt := by
  intro s out as fuel hlen hn hop hap hdoa hfuel
  set s0 : BignumState := setReg s "cy" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcy0 : s0.regs "cy" = 0 := by rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "cy" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cy" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hop0 : memHoldsLimbs s0.mem (regAddr s0 "op") out := by
    rw [hmem0, hra0 "op" (by decide)]; exact hop
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; exact hap
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; exact hdoa
  have hb0 : s0.regs "b" = s.regs "b" := hreg0 "b" (by decide)
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, _⟩ :=
    mpnSubmul1_loop out as s0 0 extra hlen hcy0 hn0' hop0 hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodySubmul s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySubmul] s0 := by
      conv_lhs => rw [bodySubmul]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    rw [hb0] at hs'_mem
    exact hs'_mem
  · rw [hs'_cy, hb0]

end CatCrypt.Crypto.Jasmin.Examples.MpnSubmul1Prototype
