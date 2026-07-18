/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype

set_option autoImplicit false

/-!
# Phase 2 — verified variable-length `mpn_addmul_1` by template reuse

**EXPERIMENTAL FILE.**  Phase-2 companion to `MpnAddPrototype.lean` /
`MpnMul1Prototype.lean`.  It proves the GMP kernel `mpn_addmul_1`
(`out[] += a[] * b`, with `b` a single limb and a u64 carry threaded across
iterations) end-to-end against the Jasmin `Cwhile` semantics — reusing the
Phase-1 / mul_1 loop-invariant machinery verbatim.

`mpn_addmul_1` is the schoolbook-multiply *inner loop*: a multiply-accumulate
that adds the scalar product `a[i]·b` into the running accumulator `out[i]`.
It is the gateway kernel for `mpn_mul` (one `mpn_mul_1` for the first row, then
`|b|−1` calls of `mpn_addmul_1` for the rest).

## What is reused (kernel-agnostic, imported from `MpnMul1Prototype` /
   `MpnAddPrototype`)

* **Memory algebra** (`load64Mem_store64_same`, `load64Mem_store64_disjoint`,
  `memHoldsLimbs_store64_frame`).
* **The `Cwhile` fuel exit rule** (`bignumExecFuel_loop_exit`); the step rule is
  re-instantiated locally for this body (`bignumExecFuel_loopAddmul_step`).
* **The memory-frame plumbing** (`memHoldsLimbs`, `range_shift_subset`,
  `range_head_subset`, `disjoint_mono`, `range_op_head_tail_disjoint`,
  `disjoint_range_lt`).
* **The counter algebra** (`ofNat64_toNat`, `ofNat64_succ_ne_zero`,
  `ofNat64_succ_sub_one`, `regAddr`, `regAddr_advance`, `bv_uint_roundtrip`,
  the `setReg`/`storeMem` projection simp lemmas).
* **The arithmetic leaves** (`mulx_toNat`, `mulx_hi_le`, `addCarry_carry_le`,
  `addCarry_spec`) and the local instruction-builders (`vr`, `pv`, `loadAt0`,
  `storeAt0`, `binImm`, `regAdd`, `mulxCopn`, `addCopn`, the guard lemmas).

## What is genuinely new vs `mpn_mul_1`: the op-read-then-store invariant

The big structural difference is that the per-limb body now **reads `out[i]`
from the `op` pointer before it stores back to `op`**:

```
t       = [:u64 ap + 0];
hi, lo  = #MULX(b, t);                  // hi·2^64 + lo = a·b
_, c1, _,_,_, lo = #ADD_64(lo, cy);     // lo += cy,     carry c1
w       = [:u64 op + 0];                // READ out[i]   ← NEW vs mul_1
_, c2, _,_,_, lo = #ADD_64(lo, w);      // lo += out[i], carry c2
[:u64 op + 0] = lo;                     // store accumulated low word
cy      = hi + c1;                      // recombine carry…
cy      = cy + c2;                      //   …in two reg-adds (never wraps)
ap += 8; op += 8; n -= 1;
```

Because `op` is read before it is stored, the step lemma's hypotheses must
ALSO assert `memHoldsLimbs` for the *input* `out` array at the `op` pointer
(in addition to `a` at `ap`).  Within one iteration the head `op[0]` is
overwritten while the unread op tail `op+8..` is read-then-framed — *exactly*
how `ap` is handled in `mpnMul1_loop` / `mpnAddN_loop` via
`load64Mem_store64_disjoint`.  So `op` plays a dual role: it is both `ap`-like
(read, then framed across the head store) and the output buffer (head store).
Crucially we do NOT need `op` disjoint from itself; we need the per-iteration
store at `op[0]` to not disturb the unread op tail at `op+8..`, which is the
op-internal `range_op_head_tail_disjoint` fact already used by mul_1's output
correctness step.  The loop invariant therefore threads the *op tail* contents
forward limb by limb, just as the mul_1 loop threads the `ap` tail.

The third carry `cy = hi + c1 + c2` never wraps: the accumulated 128-bit value
`a·b + cy + out[i] ≤ (2^64−1)^2 + (2^64−1) + (2^64−1) = 2^128 − 1 < 2^128`, so
its top half `hi + c1 + c2 = (a·b + cy + out)/2^64 < 2^64`.  We keep `cy` as the
full `hi + c1 + c2` and bound the Nat sum (`hi ≤ 2^64−2`, `c1,c2 ≤ 1`, so
`hi + c1 + c2 ≤ 2^64` as a crude bound, with the strict `< 2^64` recovered from
the exact identity).

## Functional spec

`mpnAddmul1 out a b cy = (result, carry-out)` satisfies the multiply-accumulate
identity (over equal-length `|out| = |a|`):

```
toNat result + (2^64)^|a| · carry-out = toNat out + toNat a · b + cy
```

i.e. (carry-in `0`)  `out[] += a[] * b`, with the top carry at bit `64·|a|`.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnAddmul1Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype

/-! ## §1  The Jasmin `mpn_addmul_1` body — runtime `Cwhile` loop

We reuse the instruction-builders from `MpnMul1Prototype` (`vr`, `pv`,
`loadAt0`, `storeAt0`, `binImm`, `regAdd`, `mulxCopn`, `addCopn`, `flag_pre`,
`flag_post`).  The body differs from `loopBodyMul` only by an extra load from
`op` (the read of `out[i]`), an extra `#ADD_64`, and a second carry reg-add. -/

/-- One loop iteration body for `mpn_addmul_1`:
    ```
    t       = [:u64 ap + 0];
    hi, lo  = #MULX(b, t);
    _, c1, _,_,_, lo = #ADD_64(lo, cy);
    w       = [:u64 op + 0];            -- read out[i]
    _, c2, _,_,_, lo = #ADD_64(lo, w);
    [:u64 op + 0] = lo;
    cy      = hi + c1;
    cy      = cy + c2;
    ap += 8; op += 8;
    n  -= 1;
    ```
    `cy` is initialised to 0 before the loop (first iteration's first `#ADD_64`
    adds `0`); the scalar multiplier sits in register `b` (= `bp`) and is never
    advanced.  Unlike `loopBodyMul`, `op` is *read* (into `w`) before it is
    *stored*, realising the multiply-accumulate. -/
def loopBodyAddmul : List InstrR :=
  [ loadAt0 "t" "ap"
  , mulxCopn "hi" "lo" "b" "t"
  , addCopn "c1" "lo" "lo" "cy"
  , loadAt0 "w" "op"
  , addCopn "c2" "lo" "lo" "w"
  , storeAt0 "op" "lo"
  , regAdd "cy" "hi" "c1"
  , regAdd "cy" "cy" "c2"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_addmul_1`:
    ```
    cy = 0;
    while (n != 0) { <loopBodyAddmul> }
    ```
    `cy` holds the final carry (the GMP `mpn_addmul_1` ABI returns it). -/
def bodyAddmul : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul ]

/-- `mpn_addmul_1(op, ap, b, n)` as a Jasmin `FunDecl`.  Void return (output via
    `op`, which is read-modify-written); SysV ABI `rdi=op, rsi=ap, rdx=b, rcx=n`
    — `b` (= register `bp`) is the scalar multiplier, passed by value. -/
def mpnAddmul1Fd : FunDecl where
  name := { name := "mpn_addmul_1" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩, ⟨{ var := vr "n" }⟩]
  body := bodyAddmul
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the public
    length `n`, never a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodyAddmul = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnAddmul1Fd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional reference + the one-limb MUL-ACC step -/

/-- One `mpn_addmul_1` step on `BitVec 64`: multiply limb `a` by the scalar `b`,
    add the running carry `cy` and the accumulator limb `out`, and split into
    `(out_limb, carry-out)`.  `out_limb = (a·b + cy + out) mod 2^64`,
    `carry-out = (a·b + cy + out) / 2^64`.  Defined via the executable
    `mulx`/`addCarry` so the bridge is direct:

    * `(hi, lo) = mulx b a`
    * `(c1, lo1) = addCarry lo cy`        — `lo1 = lo + cy`,  carry `c1`
    * `(c2, lo2) = addCarry lo1 out`      — `lo2 = lo1 + out`, carry `c2`
    * `out_limb = lo2`, `carry-out = hi + c1 + c2` (never wraps). -/
def addmul1Step (out a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  let (hi, lo) := mulx b a
  let (c1, lo1) := addCarry lo cy
  let (c2, lo2) := addCarry lo1 out
  (lo2, hi + c1 + c2)

/-- Pure reference for `mpn_addmul_1`: multiply-accumulate a limb list `a` by a
    scalar `b` into accumulator `out`, threading a u64 carry `cy`.  Returns
    `(result limbs, final carry-out)`.  Recurses in lockstep over `out`/`a`;
    the spec below is stated for equal-length inputs.  This is exactly the carry
    chain the emitted `while (n != 0)` loop walks, limb by limb. -/
def mpnAddmul1 : List (BitVec 64) → List (BitVec 64) → BitVec 64 → BitVec 64 →
    (List (BitVec 64) × BitVec 64)
  | o :: os, a :: as, b, cy =>
      let (r, cy') := addmul1Step o a b cy
      let (rs, fcy) := mpnAddmul1 os as b cy'
      (r :: rs, fcy)
  | _, _, _, cy => ([], cy)

/-! ## §3  Functional spec: the carry-chain invariant

`bv_decide` cannot close an unbounded loop; the inductive invariant is the
per-limb multiply-accumulate identity, fed by the §2 leaf.  The arithmetic
leaves (`mulx_toNat`, `mulx_hi_le`, `addCarry_carry_le`, `addCarry_spec`) are
imported from `MpnMul1Prototype`. -/

/-- The single-step MUL-ACC identity, on `Nat`:
    `addmul1Step out a b cy` produces `(o', cy')` with
    `o' + 2^64·cy' = a·b + cy + out`.

    The carry `cy' = hi + c1 + c2` is bounded by combining `hi ≤ 2^64−2`,
    `c1, c2 ≤ 1`, and the exact identity; the bound `< 2^64` follows from the
    full 128-bit accumulation fitting in `2^128` (`a·b + cy + out ≤ 2^128−1`). -/
theorem addmul1Step_spec (out a b cy : BitVec 64) :
    (addmul1Step out a b cy).1.toNat + 2 ^ 64 * (addmul1Step out a b cy).2.toNat
      = a.toNat * b.toNat + cy.toNat + out.toNat := by
  -- Unfold the four definitional projections.
  rw [show (addmul1Step out a b cy).1
        = (addCarry (addCarry (mulx b a).2 cy).2 out).2 from rfl,
      show (addmul1Step out a b cy).2
        = (mulx b a).1 + (addCarry (mulx b a).2 cy).1
            + (addCarry (addCarry (mulx b a).2 cy).2 out).1 from rfl]
  set hi := (mulx b a).1 with hhi
  set lo := (mulx b a).2 with hlo
  set c1 := (addCarry lo cy).1 with hc1
  set lo1 := (addCarry lo cy).2 with hlo1
  set c2 := (addCarry lo1 out).1 with hc2
  set lo2 := (addCarry lo1 out).2 with hlo2
  -- mulx: lo + 2^64·hi = b·a = a·b.
  have hmulx : lo.toNat + 2 ^ 64 * hi.toNat = a.toNat * b.toNat := by
    rw [hlo, hhi, mulx_toNat b a]; ring
  -- first addCarry: lo1 + 2^64·c1 = lo + cy.
  have hadd1 : lo1.toNat + 2 ^ 64 * c1.toNat = lo.toNat + cy.toNat := by
    rw [hlo1, hc1, addCarry_spec lo cy]
  -- second addCarry: lo2 + 2^64·c2 = lo1 + out.
  have hadd2 : lo2.toNat + 2 ^ 64 * c2.toNat = lo1.toNat + out.toNat := by
    rw [hlo2, hc2, addCarry_spec lo1 out]
  -- carry bounds.
  have hc1le : c1.toNat ≤ 1 := by rw [hc1]; exact addCarry_carry_le lo cy
  have hc2le : c2.toNat ≤ 1 := by rw [hc2]; exact addCarry_carry_le lo1 out
  have hhile : hi.toNat ≤ 2 ^ 64 - 2 := by rw [hhi]; exact mulx_hi_le a b
  have hlo2bound : lo2.toNat < 2 ^ 64 := lo2.isLt
  have hlo1bound : lo1.toNat < 2 ^ 64 := lo1.isLt
  have hlobound : lo.toNat < 2 ^ 64 := lo.isLt
  have hcybound : cy.toNat < 2 ^ 64 := cy.isLt
  have houtbound : out.toNat < 2 ^ 64 := out.isLt
  have habound : a.toNat < 2 ^ 64 := a.isLt
  have hbbound : b.toNat < 2 ^ 64 := b.isLt
  -- The full 128-bit accumulation `a·b + cy + out ≤ 2^128 - 1`:
  -- `a·b ≤ (2^64-1)^2` and `cy + out ≤ 2·(2^64-1)`, so the top half
  -- `hi + c1 + c2 = (a·b + cy + out)/2^64 < 2^64`.
  have hprodle : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  -- From the three identities, `a·b + cy + out = lo2 + 2^64·(hi + c1 + c2)`.
  have hcombine : lo2.toNat + 2 ^ 64 * (hi.toNat + c1.toNat + c2.toNat)
      = a.toNat * b.toNat + cy.toNat + out.toNat := by
    have := hmulx; have := hadd1; have := hadd2; ring_nf; omega
  -- `lo2 ≥ 0` and `a·b + cy + out ≤ 2^128 - 1` give `hi + c1 + c2 < 2^64`.
  have hcarrybound : hi.toNat + c1.toNat + c2.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat + cy.toNat + out.toNat ≤ 2 ^ 128 - 1 := by
      have : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 65 + 1 := by norm_num
      omega
    omega
  -- The combined three-summand carry register never wraps.
  have hsum01 : (hi + c1).toNat = hi.toNat + c1.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsum : (hi + c1 + c2).toNat = hi.toNat + c1.toNat + c2.toNat := by
    rw [BitVec.toNat_add, hsum01, Nat.mod_eq_of_lt (by omega)]
  rw [hsum]
  -- Combine the three identities linearly; omega closes.
  omega

/-- **Main functional spec — proved by induction on the limb list.**

    For equal-length limb lists `out, a`, scalar `b`, and carry-in `cy`, the
    pure reference `mpnAddmul1` satisfies the multiply-accumulate identity:
    the denotation of the output limbs plus the final carry-out shifted to bit
    `64·|a|` equals `toNat out + toNat a · b + cy`.

    This is the inductive invariant the emitted `while (n != 0)` loop maintains:
    each iteration peels one limb (`addmul1Step_spec`), and the IH carries the
    identity over the `2^64`-scaled tail. -/
theorem mpnAddmul1_spec :
    ∀ (out a : List (BitVec 64)), out.length = a.length → ∀ (b cy : BitVec 64),
      toNat (mpnAddmul1 out a b cy).1
        + (2 ^ 64) ^ a.length * (mpnAddmul1 out a b cy).2.toNat
      = toNat out + toNat a * b.toNat + cy.toNat := by
  intro out
  induction out with
  | nil =>
    intro a hlen b cy
    cases a with
    | nil => simp [mpnAddmul1, toNat]
    | cons _ _ => simp at hlen
  | cons o os ih =>
    intro a hlen b cy
    cases a with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      set p := addmul1Step o a b cy with hp
      have hstep := addmul1Step_spec o a b cy
      rw [← hp] at hstep
      set q := mpnAddmul1 os as b p.2 with hq
      have htail := ih as hlen' b p.2
      rw [← hq] at htail
      have hunfold : mpnAddmul1 (o :: os) (a :: as) b cy = (p.1 :: q.1, q.2) := by
        simp only [mpnAddmul1, hp, hq]
      rw [hunfold]
      simp only [toNat, List.length_cons]
      have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      -- IH scaled by 2^64 + head step (addmul1Step_spec) close the linear goal.
      have hkey : 2 ^ 64 * toNat q.1 + 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat)
          = 2 ^ 64 * (toNat os + toNat as * b.toNat + p.2.toNat) := by
        rw [← htail]; ring
      have hmono : 2 ^ 64 * (2 ^ 64) ^ as.length * q.2.toNat
          = 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat) := by ring
      rw [hmono]
      have hexpand : (a.toNat + 2 ^ 64 * toNat as) * b.toNat
          = a.toNat * b.toNat + 2 ^ 64 * (toNat as * b.toNat) := by ring
      rw [hexpand]
      omega

/-- The usual entry point: carry-in 0.  `mpn_addmul_1` with no incoming carry
    multiply-accumulates a bignum into an accumulator; the result plus the
    carry-out at bit `64·|a|` equals `toNat out + toNat a · b` (the GMP
    `mpn_addmul_1` contract — the return value is the carry-out). -/
theorem mpnAddmul1_spec_carryIn_zero (out a : List (BitVec 64))
    (hlen : out.length = a.length) (b : BitVec 64) :
    toNat (mpnAddmul1 out a b 0).1
      + (2 ^ 64) ^ a.length * (mpnAddmul1 out a b 0).2.toNat
      = toNat out + toNat a * b.toNat := by
  have h := mpnAddmul1_spec out a hlen b 0
  simpa using h

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `out=[10], a=[0xFFFF…FFFF], b=3`: `10 + 3·(2^64-1) = 7 + 3·2^64`,
    so limb `7`, carry `3` (since `3·(2^64-1)+10 = 3·2^64 + 7`). -/
example : mpnAddmul1 [10] [(-1 : BitVec 64)] 3 0 = ([7], 3) := by native_decide

/-- `out=[5,7], a=[2,3], b=10`: `[5+20, 7+30] = [25, 37]`, no carry. -/
example : mpnAddmul1 [5, 7] [2, 3] 10 0 = ([25, 37], 0) := by native_decide

/-- Carry propagation: `out=[0,0], a=[2^63,0], b=2` ⇒ `[0,1]` (top bit of the
    first product carries into limb 1). -/
example : mpnAddmul1 [0, 0] [(BitVec.ofNat 64 (2 ^ 63)), 0] 2 0 = ([0, 1], 0) := by
  native_decide

#eval toNat (mpnAddmul1 [10] [(-1 : BitVec 64)] 3 0).1
        + 2 ^ 64 * (mpnAddmul1 [10] [(-1 : BitVec 64)] 3 0).2.toNat   -- 10 + 3·(2^64-1)

/-! ## §4  MULX / ADD bridge: executable intrinsics match the pure step

The emitted `#MULX` runs `BignumExec.mulx`; the two emitted `#ADD_64`s run
`BignumExec.addCarry`.  The pure `addmul1Step` is *defined* directly in terms of
`mulx`/`addCarry`, so the bridge is definitional — recorded here for clarity. -/

theorem addmul1Step_out (out a b cy : BitVec 64) :
    (addCarry (addCarry (mulx b a).2 cy).2 out).2 = (addmul1Step out a b cy).1 := rfl

theorem addmul1Step_carry (out a b cy : BitVec 64) :
    (mulx b a).1 + (addCarry (mulx b a).2 cy).1
        + (addCarry (addCarry (mulx b a).2 cy).2 out).1
      = (addmul1Step out a b cy).2 := rfl

/-! ## §5  One loop iteration as an explicit state update

`loopBodyAddmul` is straight-line, so it runs via `bignumExec`.  This lemma
computes the exact effect of one pass: load `a` from `ap`, MULX by `b`, add the
running carry, **load `out` from `op`**, add it, store the low word at `op`,
recombine `cy = hi + c1 + c2`, advance `ap`/`op` by 8 and decrement `n`.

The new hypothesis vs `bignumExec_loopBodyMul_step` is `hout`: the body reads
`op[0]` (into `w`) before storing, so the step needs the *input* op-limb.

(The big symbolic-execution simp lists below carry a few inherited-but-unused
rewrite names — same heavy-simp pattern as the other `Examples/Mpn*` step
lemmas, e.g. `MpnAddOpenCarryPrototype`; the `unusedSimpArgs` linter is
disabled here as there.) -/

set_option linter.unusedSimpArgs false in
theorem bignumExec_loopBodyAddmul_step (s : BignumState) (out a : BitVec 64)
    (cy : BitVec 64)
    (hcy : s.regs "cy" = cy)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hout : load64Mem s.mem (regAddr s "op") = some (UInt64.ofNat out.toNat)) :
    ∃ s', bignumExec loopBodyAddmul s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (addmul1Step out a (s.regs "b") cy).1.toNat) ∧
      s'.regs "cy" = (addmul1Step out a (s.regs "b") cy).2 ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 ∧
      s'.regs "b" = s.regs "b" := by
  simp only [loopBodyAddmul, MpnMul1Prototype.loadAt0, MpnMul1Prototype.mulxCopn,
             MpnMul1Prototype.addCopn, MpnMul1Prototype.storeAt0, MpnMul1Prototype.regAdd,
             MpnMul1Prototype.binImm, MpnMul1Prototype.flag_pre, MpnMul1Prototype.flag_post,
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
  -- Now the `op` load (offset 0): the intermediate state's memory is still
  -- `s.mem` (only register writes so far), and the `op` register is unchanged
  -- through the prefix (it writes only `t, hi, lo, c1`).  Eliminate the `+ 0`
  -- offset so the address matches `regAddr s "op"`, then fire `hout`.
  -- Push the `setReg s "t" a` projections through (`op`/`b`/`t`/`cy`/`mem` are
  -- all unaffected by the `t` write), eliminate the `+ 0` offset, then fire
  -- `hout` (the address is now `UInt64.ofNat (s.regs "op").toNat = regAddr s "op"`).
  simp only [setReg_regs, setReg_mem, String.reduceEq, ↓reduceIte, reduceIte]
  rw [show s.regs "op" + 0 = s.regs "op" from by bv_decide]
  rw [hout]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.  Read off the store, the `cy`
  -- register, the register advances, and `b` invariance.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte, hcy,
               addmul1Step, show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-- `loopBodyAddmul` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodyAddmul_straightLine : InstrR.bodyIsStraightLine loopBodyAddmul := by
  simp only [loopBodyAddmul, loadAt0, mulxCopn, addCopn, storeAt0, regAdd, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodyAddmul` is non-control. -/
theorem loopBodyAddmul_nonControl : ∀ i ∈ loopBodyAddmul, i.isNonControl := by
  intro i hi
  simp only [loopBodyAddmul, loadAt0, mulxCopn, addCopn, storeAt0, regAdd, binImm,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §6  One `Cwhile` iteration over `bignumExecFuel`

The imported `bignumExecFuel_loop_step` is hardcoded to add's `loopBody`, so we
re-instantiate the *same* proof for `loopBodyAddmul`.  `bignumExecFuel_loop_exit`
is already generic over the body, so it is reused directly. -/

/-- **Forward one-iteration rule** for `loopBodyAddmul` — same proof shape as the
    imported `bignumExecFuel_loop_step`, specialised to the MUL-ACC body. -/
theorem bignumExecFuel_loopAddmul_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodyAddmul s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodyAddmul] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodyAddmul] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodyAddmul s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodyAddmul s
        loopBodyAddmul_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodyAddmul [.Cwhile [] cond loopBodyAddmul]
        loopBodyAddmul_nonControl s s_mid s' hsl hrec]

/-! ## §7  Assembly: `MpnAddmul1JasminRefines`

The full bridge.  Structurally mirrors `mpnMul1_loop` → `MpnMul1JasminRefines`,
but with `op` playing a *dual* role: it is both the input accumulator (read
limb by limb, with the unread tail framed across the head store — like `ap`)
and the output buffer (head store each iteration).  Each step peels one limb via
`bignumExec_loopBodyAddmul_step` and `bignumExecFuel_loopAddmul_step`,
preserving:

* the unread `ap` suffix across the `op[i]` store (`load64Mem_store64_disjoint`,
  op-vs-ap disjointness — as in mul_1), and
* the unread `op` suffix across the `op[i]` store
  (`range_op_head_tail_disjoint`: the head store block `[op,op+8)` is disjoint
  from the op tail `[op+8, …)`, so the to-be-read op-tail limbs survive),

and threading the u64 carry via `addmul1Step`.  The scalar `b` lives in a
register and is read-only, so only op-vs-ap separation (plus op-internal
head/tail non-aliasing) is needed. -/

/-- The bridge statement.  The scalar `b` is `s.regs "b"`.  Memory holds the
    accumulator `out` at `op` AND the multiplicand `a` at `ap`; only op-vs-ap
    disjointness is required (the `b` register is never dereferenced, and the
    op buffer's internal head/tail non-aliasing follows from `disjoint_range_lt`
    via the op-vs-ap separation). -/
def MpnAddmul1RefinesStmt : Prop :=
  ∀ (s : BignumState) (out as : List (BitVec 64)) (fuel : Nat),
    out.length = as.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyAddmul s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnAddmul1 out as (s.regs "b") 0).1 ∧
      s'.regs "cy" = (mpnAddmul1 out as (s.regs "b") 0).2

/-- **The loop, by induction on the limb list.**  Mirror of `mpnMul1_loop`,
    with `op` read-then-stored each iteration (dual role).  The frame conclusion
    (last conjunct) is over blocks disjoint from BOTH the op region and the ap
    region — the op store may touch the op region, and we read both `out` and
    `a` from memory, so we frame only outside both. -/
theorem mpnAddmul1_loop :
    ∀ (out as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      out.length = as.length →
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "op") out →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnAddmul1 out as (s.regs "b") cy).1 ∧
        s'.regs "cy" = (mpnAddmul1 out as (s.regs "b") cy).2 ∧
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
        exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodyAddmul s
          (MpnMul1Prototype.evalPExpr_loopCond_false s hn0)
      · simp [mpnAddmul1, memHoldsLimbs]
      · simpa [mpnAddmul1] using hcy
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
        bignumExec_loopBodyAddmul_step s o a cy hcy hap_head hop_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0
          (UInt64.ofNat (addmul1Step o a (s.regs "b") cy).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      -- The head store block `[op0, op0+8)` is disjoint from:
      --  (i) the ap tail `[ap+8, …)`  — op-vs-ap (as in mul_1), and
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
      have hcy1 : s1.regs "cy" = (addmul1Step o a (s.regs "b") cy).2 := hs1_cy
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      -- Apply the IH on the tail with carry `(addmul1Step o a (s.regs "b") cy).2`.
      obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, hs'_frame⟩ :=
        ih as s1 (addmul1Step o a (s.regs "b") cy).2 extra hlen' hcy1 hn1 hop1 hap1 hdoa1
      refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loopAddmul_step emptyRegistry (2 * as.length + 2 + extra) _
          s s1 s' (MpnMul1Prototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Memory at op: head limb at `op0` (preserved by IH frame), tail by IH.
        rw [hmem1] at hs'_frame
        refine ⟨?_, ?_⟩
        · -- `load64Mem s'.mem op0 = head_result`, via IH frame + read-back.
          --   the IH frame applies because op0's 8-byte block is disjoint from
          --   BOTH the tail op-region (op0+8..) and the tail ap-region (ap+8..).
          rw [hs'_frame op0 (by rw [hra_op]; exact hsep_op)
                (by rw [hra_ap]; exact hdoa_store_aptail)]
          have hread := load64Mem_store64_same s.mem op0
            (UInt64.ofNat (addmul1Step o a (s.regs "b") cy).1.toNat)
          rw [hread]
          -- head of `(mpnAddmul1 (o::os) (a::as) b cy).1` is `(addmul1Step …).1`.
          rfl
        · -- tail: from IH (op base `op0+8`), with `s1.regs "b" = s.regs "b"`.
          have hthis := hs'_mem
          rw [hra_op, hs1_b] at hthis
          exact hthis
      · -- carry-out register.
        rw [hs'_cy, hs1_b]; simp only [mpnAddmul1]
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

/-- **The bridge, fully proved.**  `mpnAddmul1Fd.body` (the emitted
    `cy := 0; while (n != 0) { loopBodyAddmul }`) refines the pure reference
    `mpnAddmul1` over byte memory.  Mirror of `MpnMul1JasminRefines`, with `op`
    read-modify-written each iteration. -/
theorem MpnAddmul1JasminRefines : MpnAddmul1RefinesStmt := by
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
    mpnAddmul1_loop out as s0 0 extra hlen hcy0 hn0' hop0 hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodyAddmul s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul] s0 := by
      conv_lhs => rw [bodyAddmul]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    rw [hb0] at hs'_mem
    exact hs'_mem
  · rw [hs'_cy, hb0]

end CatCrypt.Crypto.Jasmin.Examples.MpnAddmul1Prototype
