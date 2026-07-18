/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumConstantTime

/-!
# Completing the JInstr-level constant-time coverage: a by-construction sweep

`MachineConstantTime.lean` builds the machine-level constant-time framework over
`List (JInstr w)` (the leakage model `MLeak`/`blockLeak`, the direct-addressing
class `IsDirect`, and the keystone `blockLeak_state_independent`); `BignumConstantTime.lean`
exercises it on a *sample* (`bignumAdd4`, `mulAdd2`), with each kernel's
constant-time obligation discharged by a hand proof (`bignumAdd4_ctAddressed` etc.).

This module turns that sample into a **by-construction sweep**. We expose a single
*decidable* "constant-time class" check on a kernel body —

* `allDirect body : Bool`  (every instruction uses direct base+displacement addressing)

— and prove the **corollary** `allDirect_constant_time`: *any* straight-line leaf
with `allDirect body = true` has a machine leakage trace independent of the
initial state, hence is constant-time, with the obligation discharged by a single
`decide` / `native_decide` on the body. The hand proofs in the sample are thereby
subsumed: a conforming kernel gets constant-time *for free*.

We then **sweep** the corollary across the real JInstr-level bignum/field kernels:
`bignumAdd4` and `mulAdd2` (re-derived through the corollary, showing it subsumes
the hand proofs), plus three further genuine kernels built here —

* `bignumSub4`  — 4-limb subtract-with-borrow (`SUB`/`SBB` borrow chain);
* `bignumMontReduce` — one Montgomery word reduction step (`m := lo · μ mod 2^64`
  via a `MULX` low-word fold, then the `add`-back of `m · p`);
* `schoolbookMulStep` — a two-limb schoolbook multiply-accumulate
  (`MULX` partial products + the carry fold).

Each carries a **functional KAT** (`native_decide` against the real multi-limb
arithmetic — genuine carry/borrow/mul, not a placeholder) and a
constant-time theorem `<name>_constant_time` obtained by the corollary with
`by native_decide` on `allDirect`.

## Coverage

The **JInstr-level straight-line bignum/field kernels** are now constant-time *by
construction*: any body that passes the decidable `allDirect` check is
constant-time via `allDirect_constant_time`, and the roster below
(`bignumAdd4`, `mulAdd2`, `bignumSub4`, `bignumMontReduce`, `schoolbookMulStep`)
instantiates that across the genuine carry/borrow/multiply kernels expressible in
the `JInstr 64` model.

What this sweep does **not** cover — the honest boundary:

* **ZMM-layer kernels** (the AVX-512 / `ZOp` vector kernels — Poseidon2, the
  packed NTT/Frodo lanes). These live in the `ZOp`/`Lcmd`/`Com` IRs, not in
  `List (JInstr w)`. Their leakage model (`MLeak`, `instrLeak`, `blockLeak`) is
  defined only for `JInstr`; covering them would need the leakage framework
  **lifted** to the vector instruction type (a `ZOp`-indexed `instrLeak` with the
  vector load/store addressing modes, then a re-proof of the keystone).
* **`Lcmd`/`Com`-layer kernels** (the structured-control loop bodies and the
  whole-function `Com` programs). The strict keystone is straight-line only; the
  loop/branch IRs would additionally need the control-flow channel
  (`MLeak.branch`) connected to the structured-control evaluator, i.e. a
  `blockLeak` analogue threaded through the `Lcmd`/`Com` semantics rather than the
  flat `runBlock` fold used here.

Both boundaries are *framework lifts*, not gaps in the present sweep: every
kernel that is (or can be expressed as) a straight-line `List (JInstr 64)` is
covered here.

**0 axioms beyond the `native_decide` KAT pins** (`propext`, `Quot.sound`,
`Lean.ofReduceBool`), **0 sorries**.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.BignumConstantTime

/-! ## 1. The decidable constant-time class check

`IsDirect` carves out the direct-addressing instructions (`Decidable` per the
instance in `MachineConstantTime.lean`). `allDirect body` lifts that to a single
`Bool` on the whole body: a kernel is in the constant-time class iff every one of
its instructions is direct. The point is decidability — `allDirect body = true`
is checkable by `decide`/`native_decide`, so a conforming kernel discharges its
constant-time obligation mechanically rather than by a hand `ctAddressed` proof. -/

/-- The decidable **constant-time class** check on a kernel body: `true` iff every
    instruction uses direct (base + compile-time-constant displacement) addressing
    — no register-indexed `loadMemIdx`/`storeMemIdx`. -/
def allDirect {w : Nat} (body : List (JInstr w)) : Bool :=
  body.all (fun i => decide (IsDirect i))

/-! ## 2. Bridge: the decidable check to the membership form the keystone needs -/

/-- `allDirect body = true` ⇒ every instruction of `body` is `IsDirect`, the
    hypothesis shape `blockLeak_state_independent` consumes. -/
theorem allDirect_mem_isDirect {w : Nat} (body : List (JInstr w))
    (h : allDirect body = true) : ∀ i ∈ body, IsDirect i := by
  intro i hi
  have := (List.all_eq_true.mp h) i hi
  exact of_decide_eq_true this

/-! ## 3. The by-construction constant-time corollary

The keystone `blockLeak_state_independent` says an all-direct body has a leakage
trace independent of the initial state. Composing it with the decidable bridge
gives the corollary: **any** kernel whose `allDirect` check passes is
constant-time, with the obligation discharged by `decide`/`native_decide`. -/

/-- **By-construction constant-time.** A straight-line leaf whose decidable
    `allDirect` check passes produces the **same** machine leakage trace from any
    two initial states `s₁ s₂` — its observable control-flow + memory-address
    sequence is a function of the program text alone, so it leaks nothing about
    register values (in particular secret inputs). Any conforming kernel now
    discharges constant-time by `allDirect_constant_time (by decide)`. -/
theorem allDirect_constant_time {w : Nat} (body : List (JInstr w))
    (h : allDirect body = true) (s₁ s₂ : JState w) :
    blockLeak s₁ body = blockLeak s₂ body :=
  blockLeak_state_independent body (allDirect_mem_isDirect body h) s₁ s₂

/-- A kernel in the constant-time class takes no conditional branch: the emitted
    straight-line scalar subset has an empty control-flow channel regardless of
    state. (Holds for *every* `JInstr` body, restated here as the branch-channel
    half of the constant-time guarantee that accompanies the corollary.) -/
theorem allDirect_no_branch {w : Nat} (body : List (JInstr w)) (s : JState w) :
    (blockLeak s body).filter MLeak.isBranch = [] :=
  blockLeak_no_branch body s

/-! ## 4. Re-deriving the sample kernels through the corollary

`bignumAdd4` and `mulAdd2` were proved constant-time in `BignumConstantTime.lean`
by hand `ctAddressed` proofs. Here we re-derive their constant-time guarantee
through `allDirect_constant_time` with a single `by native_decide`, showing the
by-construction corollary subsumes the hand proofs: the only obligation is the
decidable `allDirect` check. -/

/-- `bignumAdd4` is in the decidable constant-time class. -/
theorem bignumAdd4_allDirect : allDirect bignumAdd4 = true := by native_decide

/-- **`bignumAdd4` is constant-time, by construction.** Re-derives
    `bignumAdd4_constant_time` (proved by hand in `BignumConstantTime.lean`)
    through the corollary: the leakage trace is the same from any two states, the
    obligation discharged by the single decidable check `bignumAdd4_allDirect`. -/
theorem bignumAdd4_constant_time' (s₁ s₂ : JState 64) :
    blockLeak s₁ bignumAdd4 = blockLeak s₂ bignumAdd4 :=
  allDirect_constant_time bignumAdd4 bignumAdd4_allDirect s₁ s₂

/-- `mulAdd2` (the ADX/BMI2 fast path) is in the decidable constant-time class. -/
theorem mulAdd2_allDirect : allDirect mulAdd2 = true := by native_decide

/-- **`mulAdd2` is constant-time, by construction.** The ADX/BMI2
    `MULX`/`ADCX`/`ADOX` fast path re-derived through the corollary. -/
theorem mulAdd2_constant_time' (s₁ s₂ : JState 64) :
    blockLeak s₁ mulAdd2 = blockLeak s₂ mulAdd2 :=
  allDirect_constant_time mulAdd2 mulAdd2_allDirect s₁ s₂

/-! ## 5. New kernel: a 4-limb `bignum_sub` (borrow chain)

`bignumSub4` is the straight-line body s2n-bignum's `bignum_sub` (fixed 4-word
operands) compiles to: load `a[0..3]`/`b[0..3]` through the public pointers
`ap`/`bp`, run the `SUB`/`SBB` **borrow chain** across the four limbs (the borrow
threaded through `CF`, exactly as on the machine — `SUB` for limb 0, then `SBB`
for limbs 1–3), and store `r[0..3]` to `rp`. Genuine two's-complement borrow
propagation. -/

/-- A real 4-limb `bignum_sub`: `r[0..3] := a[0..3] − b[0..3]` (mod 2²⁵⁶) with a
    borrow chain. Inputs behind the public bases `ap`/`bp`, output behind `rp`;
    the limb-data registers are secret. -/
def bignumSub4 : List (JInstr 64) :=
  [ .loadMem "a0" "ap" 0
  , .loadMem "a1" "ap" 8
  , .loadMem "a2" "ap" 16
  , .loadMem "a3" "ap" 24
  , .loadMem "b0" "bp" 0
  , .loadMem "b1" "bp" 8
  , .loadMem "b2" "bp" 16
  , .loadMem "b3" "bp" 24
    -- borrow chain: a0 -= b0 (sets CF=borrow); a1 -= b1 + CF; …
  , .sub "a0" (.reg "b0")
  , .sbb "a1" (.reg "b1")
  , .sbb "a2" (.reg "b2")
  , .sbb "a3" (.reg "b3")
    -- store r[0..3]
  , .storeMem "rp" 0 (.reg "a0")
  , .storeMem "rp" 8 (.reg "a1")
  , .storeMem "rp" 16 (.reg "a2")
  , .storeMem "rp" 24 (.reg "a3") ]

/-- Initial state holding `a[0..3]` at `ap+{0,8,16,24}` and `b[0..3]` at
    `bp+{0,8,16,24}` (distinct pointer bases as memory keys). -/
def subState (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "ap" then
        if off = 0 then a0 else if off = 8 then a1
        else if off = 16 then a2 else if off = 24 then a3 else 0
      else if base = "bp" then
        if off = 0 then b0 else if off = 8 then b1
        else if off = 16 then b2 else if off = 24 then b3 else 0
      else 0 }

/-- Reference: the `k`-th 64-bit limb of the 256-bit (mod-2²⁵⁶) difference of the
    two little-endian 4-limb numbers. The subtraction is computed over `ℤ` and
    reduced mod `2²⁵⁶`, matching the machine's two's-complement borrow chain. -/
def refSubLimb (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (k : Nat) : BitVec 64 :=
  let A : Nat := a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192
  let B : Nat := b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192
  let D : Int := ((A : Int) - (B : Int)) % (2^256)
  BitVec.ofNat 64 ((D.toNat) / 2^(64*k))

/-- The four output limbs `bignumSub4` writes, read back from the final state. -/
def subOutLimbs (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let s := runBlock (subState a0 a1 a2 a3 b0 b1 b2 b3) bignumSub4
  (s.load "rp" 0, s.load "rp" 8, s.load "rp" 16, s.load "rp" 24)

/-- **Functional KAT, vector 1 (no borrow).** `a = (10, 20, 30, 40)`,
    `b = (1, 2, 3, 4)`: a clean limbwise difference, no borrow crosses a limb. -/
theorem bignumSub4_kat1 :
    subOutLimbs 10 20 30 40 1 2 3 4 =
      ( refSubLimb 10 20 30 40 1 2 3 4 0
      , refSubLimb 10 20 30 40 1 2 3 4 1
      , refSubLimb 10 20 30 40 1 2 3 4 2
      , refSubLimb 10 20 30 40 1 2 3 4 3 ) := by
  native_decide

/-- **Functional KAT, vector 2 (full borrow propagation).** `a = (0,0,0,1)`,
    `b = (1,0,0,0)`: the borrow out of limb 0 ripples through limbs 1–2 into limb
    3 (`a − b = 2¹⁹² − 1 = (FF…FF, FF…FF, FF…FF, 0)`). -/
theorem bignumSub4_kat2 :
    subOutLimbs 0 0 0 1 1 0 0 0 =
      ( refSubLimb 0 0 0 1 1 0 0 0 0
      , refSubLimb 0 0 0 1 1 0 0 0 1
      , refSubLimb 0 0 0 1 1 0 0 0 2
      , refSubLimb 0 0 0 1 1 0 0 0 3 ) := by
  native_decide

/-- **Functional KAT, vector 3 (underflow wraps mod 2²⁵⁶).** `a = (0,0,0,0)`,
    `b = (1,0,0,0)`: `0 − 1` underflows to `2²⁵⁶ − 1 = (FF…FF, FF…FF, FF…FF, FF…FF)`,
    exercising the borrow out of the top limb. -/
theorem bignumSub4_kat3 :
    subOutLimbs 0 0 0 0 1 0 0 0 =
      ( refSubLimb 0 0 0 0 1 0 0 0 0
      , refSubLimb 0 0 0 0 1 0 0 0 1
      , refSubLimb 0 0 0 0 1 0 0 0 2
      , refSubLimb 0 0 0 0 1 0 0 0 3 ) := by
  native_decide

/-- `bignumSub4` is in the decidable constant-time class. -/
theorem bignumSub4_allDirect : allDirect bignumSub4 = true := by native_decide

/-- **`bignumSub4` is constant-time, by construction.** The `SUB`/`SBB` borrow
    chain leaks nothing about the secret limb values: its leakage trace is the
    same from any two states, by the corollary. -/
theorem bignumSub4_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ bignumSub4 = blockLeak s₂ bignumSub4 :=
  allDirect_constant_time bignumSub4 bignumSub4_allDirect s₁ s₂

/-! ## 6. New kernel: one Montgomery word-reduction step

`bignumMontReduce` is the inner word step of a Montgomery reduction in the
s2n-bignum idiom: given the current low accumulator word `t0` and the
precomputed Montgomery inverse `μ = -p⁻¹ mod 2⁶⁴` (loaded as a public constant),
form the reduction multiplier `m := t0 · μ mod 2⁶⁴` (the low word of a `MULX`),
then fold `m · p` back into the two-word accumulator `(t0, t1)` via a `MULX` and
the `ADD`/`ADC` carry — making the low word `t0` a multiple of `2⁶⁴` (i.e. zero
after the add), exactly as Montgomery's reduction clears one word per step.

We model the genuine arithmetic: `m`, the product `m·p = (hi,lo)`, and the carry
fold into `(t0,t1)`. The modulus `p` and `μ` are read through public pointers. -/

/-- One Montgomery word-reduction step. `t0`/`t1` are the two accumulator words
    (loaded from `cp`), `μ` the Montgomery inverse (from `mu`), `p` the modulus
    word (from `pp`). Computes `m := t0·μ`, then `(t0,t1) += m·p`, and stores the
    updated accumulator back to `rp`. Genuine `MULX` + `ADD`/`ADC` arithmetic. -/
def bignumMontReduce : List (JInstr 64) :=
  [ .loadMem "t0" "cp" 0                          -- accumulator low
  , .loadMem "t1" "cp" 8                          -- accumulator high
  , .loadMem "mu" "mp" 0                           -- Montgomery inverse μ
  , .loadMem "p0" "pp" 0                           -- modulus word p
    -- m := t0 · μ  (low word of the widening product)
  , .mulx "mhi" "m" (.reg "t0") (.reg "mu")
    -- (plo, phi) := m · p
  , .mulx "phi" "plo" (.reg "m") (.reg "p0")
    -- fold m·p into the accumulator: t0 += plo (sets CF); t1 += phi + CF
  , .add "t0" (.reg "plo")
  , .adc "t1" (.reg "phi")
    -- store the reduced accumulator
  , .storeMem "rp" 0 (.reg "t0")
  , .storeMem "rp" 8 (.reg "t1") ]

/-- Initial state for `bignumMontReduce`: accumulator `(t0,t1)` at `cp+{0,8}`,
    `μ` at `mp+0`, modulus `p` at `pp+0`. -/
def montState (t0 t1 mu p0 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "cp" then (if off = 0 then t0 else if off = 8 then t1 else 0)
      else if base = "mp" then (if off = 0 then mu else 0)
      else if base = "pp" then (if off = 0 then p0 else 0)
      else 0 }

/-- Reference for the Montgomery step: `m = (t0·μ) mod 2⁶⁴`; the two-word sum
    `(t0 + t1·2⁶⁴) + m·p` truncated to 128 bits, returned as `(low, high)` 64-bit
    words. Genuine multiply + carry, matching the kernel's `MULX`+`ADD`/`ADC`. -/
def refMont (t0 t1 mu p0 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let m := (t0.toNat * mu.toNat) % 2^64
  let acc := (t0.toNat + t1.toNat * 2^64) + m * p0.toNat
  (BitVec.ofNat 64 (acc % 2^64), BitVec.ofNat 64 ((acc / 2^64) % 2^64))

/-- The two accumulator words `bignumMontReduce` writes, read back. -/
def montOut (t0 t1 mu p0 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let s := runBlock (montState t0 t1 mu p0) bignumMontReduce
  (s.load "rp" 0, s.load "rp" 8)

/-- **Functional KAT, vector 1.** A small case `t = (5, 7)`, `μ = 3`, `p = 11`:
    `m = 15`, `acc = (5 + 7·2⁶⁴) + 15·11 = 170 + 7·2⁶⁴`. -/
theorem bignumMontReduce_kat1 :
    montOut 5 7 3 11 = refMont 5 7 3 11 := by native_decide

/-- **Functional KAT, vector 2 (the word actually clears).** With `p = 1` and
    `μ` chosen so `t0·μ ≡ −t0`, the low word reduces. Here `t0 = 4`, `μ = 2⁶⁴−1`
    (`≡ −1`), `p = 1`: `m = (4·(2⁶⁴−1)) mod 2⁶⁴ = 2⁶⁴−4`, `acc_lo = (4 + (2⁶⁴−4))
    mod 2⁶⁴ = 0` — the low word is cleared, the carry lands in the high word. -/
theorem bignumMontReduce_kat2 :
    montOut 4 9 0xFFFFFFFFFFFFFFFF 1 = refMont 4 9 0xFFFFFFFFFFFFFFFF 1 := by
  native_decide

/-- **Functional KAT, vector 3 (full-width carry).** Large operands forcing a
    carry out of the low word into the high word: `t0 = 2⁶⁴−1`, `t1 = 0`,
    `μ = 2`, `p = 2⁶⁴−1`. -/
theorem bignumMontReduce_kat3 :
    montOut 0xFFFFFFFFFFFFFFFF 0 2 0xFFFFFFFFFFFFFFFF
      = refMont 0xFFFFFFFFFFFFFFFF 0 2 0xFFFFFFFFFFFFFFFF := by
  native_decide

/-- `bignumMontReduce` is in the decidable constant-time class. -/
theorem bignumMontReduce_allDirect : allDirect bignumMontReduce = true := by native_decide

/-- **`bignumMontReduce` is constant-time, by construction.** The Montgomery
    word-reduction step leaks nothing about the secret accumulator: its leakage
    trace is the same from any two states, by the corollary. -/
theorem bignumMontReduce_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ bignumMontReduce = blockLeak s₂ bignumMontReduce :=
  allDirect_constant_time bignumMontReduce bignumMontReduce_allDirect s₁ s₂

/-! ## 7. New kernel: a two-limb schoolbook multiply step

`schoolbookMulStep` is a two-limb multiply-accumulate of the kind the schoolbook
multiply inner loop emits: load a multiplier `m` and two multiplicand limbs
`a[0]`, `a[1]` through public pointers, form the two partial products
`m·a[0] = (hi0,lo0)` and `m·a[1] = (hi1,lo1)` with `MULX`, then fold them into a
three-word result `(r0,r1,r2)` with the `ADD`/`ADC` carry — `r0 = lo0`,
`r1 = hi0 + lo1`, `r2 = hi1 + carry`. Genuine schoolbook partial-product +
carry arithmetic. -/

/-- A two-limb schoolbook multiply step: `(r0,r1,r2) := m · (a0 + a1·2⁶⁴)`.
    Multiplier from `mp`, multiplicand limbs from `ap`, result to `rp`. Genuine
    `MULX` partial products + `ADD`/`ADC` carry fold. -/
def schoolbookMulStep : List (JInstr 64) :=
  [ .loadMem "m"  "mp" 0                          -- multiplier
  , .loadMem "a0" "ap" 0                           -- multiplicand limb 0
  , .loadMem "a1" "ap" 8                           -- multiplicand limb 1
    -- partial products
  , .mulx "hi0" "lo0" (.reg "m") (.reg "a0")       -- m·a0 = (hi0, lo0)
  , .mulx "hi1" "lo1" (.reg "m") (.reg "a1")       -- m·a1 = (hi1, lo1)
    -- accumulate: r0 = lo0; r1 = hi0 + lo1 (CF); r2 = hi1 + CF
  , .mov "r0" (.reg "lo0")
  , .mov "r1" (.reg "hi0")
  , .add "r1" (.reg "lo1")
  , .mov "r2" (.reg "hi1")
  , .adc "r2" (.imm 0)
    -- store the three result words
  , .storeMem "rp" 0  (.reg "r0")
  , .storeMem "rp" 8  (.reg "r1")
  , .storeMem "rp" 16 (.reg "r2") ]

/-- Initial state for `schoolbookMulStep`: multiplier `m` at `mp+0`, multiplicand
    limbs `a0`/`a1` at `ap+{0,8}`. -/
def mulState (m a0 a1 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "mp" then (if off = 0 then m else 0)
      else if base = "ap" then (if off = 0 then a0 else if off = 8 then a1 else 0)
      else 0 }

/-- Reference: the `k`-th 64-bit limb (`k ∈ {0,1,2}`) of the 192-bit product
    `m · (a0 + a1·2⁶⁴)`. Genuine full-width multiply. -/
def refMul (m a0 a1 : BitVec 64) (k : Nat) : BitVec 64 :=
  let P := m.toNat * (a0.toNat + a1.toNat * 2^64)
  BitVec.ofNat 64 (P / 2^(64*k))

/-- The three result words `schoolbookMulStep` writes, read back. -/
def mulOut (m a0 a1 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let s := runBlock (mulState m a0 a1) schoolbookMulStep
  (s.load "rp" 0, s.load "rp" 8, s.load "rp" 16)

/-- **Functional KAT, vector 1 (small, no carry).** `m = 3`, `a = (5, 7)`:
    `P = 3·(5 + 7·2⁶⁴) = 15 + 21·2⁶⁴`, limbs `(15, 21, 0)`. -/
theorem schoolbookMulStep_kat1 :
    mulOut 3 5 7 = (refMul 3 5 7 0, refMul 3 5 7 1, refMul 3 5 7 2) := by
  native_decide

/-- **Functional KAT, vector 2 (partial-product carry into r1, then r2).**
    `m = 2⁶⁴−1`, `a = (2⁶⁴−1, 2⁶⁴−1)`: the largest two-limb product, forcing
    carries out of `lo0`→`r1` and `r1`→`r2`. -/
theorem schoolbookMulStep_kat2 :
    mulOut 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
      = ( refMul 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0
        , refMul 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 1
        , refMul 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 2 ) := by
  native_decide

/-- **Functional KAT, vector 3 (carry only into the top word).**
    `m = 2`, `a = (2⁶³, 2⁶³)`: `m·a0 = 2⁶⁴` (carries straight into `r1`),
    `m·a1 = 2⁶⁴` (carries into `r2`). -/
theorem schoolbookMulStep_kat3 :
    mulOut 2 0x8000000000000000 0x8000000000000000
      = ( refMul 2 0x8000000000000000 0x8000000000000000 0
        , refMul 2 0x8000000000000000 0x8000000000000000 1
        , refMul 2 0x8000000000000000 0x8000000000000000 2 ) := by
  native_decide

/-- `schoolbookMulStep` is in the decidable constant-time class. -/
theorem schoolbookMulStep_allDirect : allDirect schoolbookMulStep = true := by native_decide

/-- **`schoolbookMulStep` is constant-time, by construction.** The schoolbook
    multiply-accumulate leaks nothing about the secret operands: its leakage
    trace is the same from any two states, by the corollary. -/
theorem schoolbookMulStep_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ schoolbookMulStep = blockLeak s₂ schoolbookMulStep :=
  allDirect_constant_time schoolbookMulStep schoolbookMulStep_allDirect s₁ s₂

/-! ## 8. The roster: every JInstr-level bignum/field kernel now CT-covered

`ctRoster` collects the straight-line `JInstr 64` bignum/field kernels this sweep
covers. `ctRoster_all_constant_time` shows the by-construction corollary
discharges constant-time for **every** kernel on the roster from one decidable
check on the concatenated bodies — the single statement that the whole roster is
in the constant-time class. -/

/-- The roster of JInstr-level bignum/field kernels covered by the sweep:
    `bignumAdd4` (carry chain), `mulAdd2` (ADX/BMI2 fast path), `bignumSub4`
    (borrow chain), `bignumMontReduce` (Montgomery word step), `schoolbookMulStep`
    (schoolbook multiply step). Each is constant-time by `allDirect_constant_time`. -/
def ctRoster : List (List (JInstr 64)) :=
  [ bignumAdd4, mulAdd2, bignumSub4, bignumMontReduce, schoolbookMulStep ]

/-- **The whole roster is in the constant-time class.** Every kernel on
    `ctRoster` passes the decidable `allDirect` check, so each is constant-time by
    `allDirect_constant_time` — one `native_decide` certifies the entire sweep. -/
theorem ctRoster_all_allDirect : ctRoster.all allDirect = true := by native_decide

/-- **Every kernel on the roster is constant-time, by construction.** For each
    body in `ctRoster` and any two initial states, the machine leakage trace is
    the same: the observable control-flow + memory-address sequence is a function
    of the program text alone. The constant-time guarantee for the whole sweep,
    delivered uniformly by the corollary from the single roster check. -/
theorem ctRoster_all_constant_time :
    ∀ body ∈ ctRoster, ∀ s₁ s₂ : JState 64,
      blockLeak s₁ body = blockLeak s₂ body := by
  intro body hb s₁ s₂
  have hall : ctRoster.all allDirect = true := ctRoster_all_allDirect
  have : allDirect body = true := (List.all_eq_true.mp hall) body hb
  exact allDirect_constant_time body this s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
