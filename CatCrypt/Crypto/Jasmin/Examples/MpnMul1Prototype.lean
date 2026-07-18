/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

set_option autoImplicit false

/-!
# Phase 2 — verified variable-length `mpn_mul_1` by template reuse

**EXPERIMENTAL FILE.**  Phase-2 companion to `MpnAddPrototype.lean` /
`MpnSubPrototype.lean`.  It proves the GMP kernel `mpn_mul_1`
(`out[] = a[] * b`, with `b` a single limb and a u64 carry threaded across
iterations) end-to-end against the Jasmin `Cwhile` semantics — reusing the
Phase-1 loop-invariant machinery verbatim.

## What is reused (kernel-agnostic, imported from `MpnAddPrototype`)

* **Memory algebra** (`load64Mem_store64_same`, `load64Mem_store64_disjoint`).
* **The `Cwhile` fuel rule** (`bignumExecFuel_loop_exit`; the step lemma is
  hardcoded to add's `loopBody`, so we re-instantiate it locally).
* **The memory-frame plumbing** (`memHoldsLimbs`, `memHoldsLimbs_store64_frame`,
  `range_shift_subset`, `range_head_subset`, `disjoint_mono`,
  `range_op_head_tail_disjoint`, `disjoint_range_lt`).
* **The counter algebra** (`ofNat64_toNat`, `ofNat64_succ_ne_zero`,
  `ofNat64_succ_sub_one`, `regAddr`, `regAddr_advance`, `bv_uint_roundtrip`,
  the `setReg`/`storeMem` projection simp lemmas).
* **The induction skeleton** (`mpnAddN_loop` → `MpnAddNJasminRefines`) — copied
  structurally; only the per-limb step and the carry thread change.

## What is genuinely new (the multiply-specific arithmetic)

Multiplication is *not* a rename of add/sub: the per-limb body now runs **two**
arithmetic intrinsics (`#MULX` then `#ADD_64`) plus a register `cy = hi + c`
recombination, and the running carry is a full **u64** (not a single bit).  The
new parts are:

* §2–§3: the pure reference `mpnMul1` + the one-limb `mul1Step` leaf identity
  (`a*b + cy` fits in 128 bits; `hi ≤ 2^64-2` so `cy' = hi + c` never wraps).
* §6: the `mulx` / `addCarry` executable bridge.
* §7: the one-iteration state update (`#MULX`, `#ADD_64`, store, `cy = hi + c`,
  three pointer/counter updates).

Unlike `mpn_add_n`, the scalar multiplier `b` lives in a *register* (`bp`), not
a buffer, so the only separation hypothesis is op-vs-ap (the `bp` register is
never dereferenced).

## Functional spec

`mpnMul1 a b cy = (result, carry-out)` satisfies the multi-precision
single-limb multiplication identity:

```
toNat result + (2^64)^|a| · carry-out = toNat a · b + carry-in
```

i.e. (carry-in `0`)  `out[] = a[] * b`, with the top carry at bit `64·|a|`.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

/-! ## §1  The Jasmin `mpn_mul_1` body — runtime `Cwhile` loop

The inner intrinsics are `#MULX` (full 64×64→128 product) and `#ADD_64`
(add-with-carry-out), followed by a register recombination `cy = hi + c`.

The small instruction-builder helpers (`vr`, `pv`, `loadAt0`, `storeAt0`,
`binImm`) are `private` in `MpnAddPrototype`, so we re-declare
definitionally-identical local copies here. -/

/-- `reg u64` variable. -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- Memory load `x := [:u64 base + 0]`. -/
def loadAt0 (x base : String) : InstrR :=
  .Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
    (.Pload .U64 { var := vr base } (.Pconst 0))

/-- Memory store `[:u64 base + 0] := src`. -/
def storeAt0 (base src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := vr base } (.Pconst 0)) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- `r += k` / `r -= k` style scalar update. -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- `dst = src1 + src2` (register + register), used for the `cy = hi + c`
    carry recombination. -/
def regAdd (dst src1 src2 : String) : InstrR :=
  .Cassgn (.Lvar { var := vr dst }) .AT_none (.sword .U64)
    (.Papp2 (.Oadd .U64) (pv src1) (pv src2))

def flag_pre  : List LVal := [.Lnone {} (.sword .U64)]
def flag_post : List LVal := List.replicate 3 (.Lnone {} (.sword .U64))

/-- `hi, lo = #MULX(b, t);` — the full 64×64→128 product, 2-LVal bundle
    `[hi, lo]` (MULX touches no flags). -/
def mulxCopn (hiName loName bName tName : String) : InstrR :=
  .Copn [.Lvar { var := vr hiName }, .Lvar { var := vr loName }]
        .AT_none (.Oasm ⟨"MULX"⟩)
        [pv bName, pv tName]

/-- `_, c, _, _, _, r = #ADD_64(lo, cy);` — add the running carry into the low
    product word, capturing the carry-out `c`.  Same 6-LVal bundle shape as
    `#ADC_64`. -/
def addCopn (cName rName aName bName : String) : InstrR :=
  .Copn (flag_pre ++ [.Lvar { var := vr cName }] ++ flag_post
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"ADD_64"⟩)
        [pv aName, pv bName]

/-- One loop iteration body for `mpn_mul_1`:
    ```
    t       = [:u64 ap + 0];
    hi, lo  = #MULX(b, t);
    _, c, _, _, _, r = #ADD_64(lo, cy);
    [:u64 op + 0] = r;
    cy = hi + c;
    ap += 8; op += 8;
    n  -= 1;
    ```
    `cy` is initialised to 0 before the loop (first iteration's `#ADD_64`
    adds `0`); the scalar multiplier sits in register `b` (= `bp`) and is never
    advanced. -/
def loopBodyMul : List InstrR :=
  [ loadAt0 "t" "ap"
  , mulxCopn "hi" "lo" "b" "t"
  , addCopn "c" "lo" "lo" "cy"
  , storeAt0 "op" "lo"
  , regAdd "cy" "hi" "c"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_mul_1`:
    ```
    cy = 0;
    while (n != 0) { <loopBodyMul> }
    ```
    `cy` holds the final carry (the GMP `mpn_mul_1` ABI returns it). -/
def bodyMul : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyMul ]

/-- `mpn_mul_1(op, ap, b, n)` as a Jasmin `FunDecl`.  Void return (output via
    `op`); SysV ABI `rdi=op, rsi=ap, rdx=b, rcx=n` — note `b` (= register `bp`)
    is the scalar multiplier, passed by value. -/
def mpnMul1Fd : FunDecl where
  name := { name := "mpn_mul_1" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩, ⟨{ var := vr "n" }⟩]
  body := bodyMul
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the public
    length `n`, never a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodyMul = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnMul1Fd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional reference + the one-limb MUL step -/

/-- One `mpn_mul_1` step on `BitVec 64`: multiply limb `a` by the scalar `b`,
    add the running carry `cy`, and split into `(out_limb, carry-out)`.
    `out_limb = (a·b + cy) mod 2^64`, `carry-out = (a·b + cy) / 2^64`.
    Defined via the executable `mulx`/`addCarry` so the §7 bridge is direct. -/
def mul1Step (a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  let (hi, lo) := mulx b a
  let (c, lo') := addCarry lo cy
  (lo', hi + c)

/-- Pure reference for `mpn_mul_1`: multiply a limb list by a scalar `b`,
    threading a u64 carry `cy`.  Returns `(result limbs, final carry-out)`.
    This is exactly the carry chain the emitted `while (n != 0)` loop walks. -/
def mpnMul1 : List (BitVec 64) → BitVec 64 → BitVec 64 →
    (List (BitVec 64) × BitVec 64)
  | a :: as, b, cy =>
      let (r, cy') := mul1Step a b cy
      let (rs, fcy) := mpnMul1 as b cy'
      (r :: rs, fcy)
  | [], _, cy => ([], cy)

/-! ## §3  Functional spec: the carry-chain invariant

The load-bearing theorem.  `bv_decide` cannot close an unbounded loop; the
inductive invariant is the per-limb identity, fed by the §2 leaf. -/

/-- `mulx` recombination: `hi·2^64 + lo = a·b` (the full 128-bit product, split
    little-endian). -/
theorem mulx_toNat (a b : BitVec 64) :
    (mulx a b).2.toNat + 2 ^ 64 * (mulx a b).1.toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  unfold mulx
  simp only [BitVec.toNat_ofNat]
  -- `prod = a·b < 2^128`; lo = prod % 2^64, hi = (prod >>> 64) % 2^64 = prod / 2^64.
  set prod : Nat := a.toNat * b.toNat with hprod
  have hpos : (0 : Nat) < 2 ^ 64 := by positivity
  have hpbound : prod < 2 ^ 64 * 2 ^ 64 := by
    rw [hprod]; exact Nat.mul_lt_mul'' ha hb
  rw [Nat.shiftRight_eq_div_pow]
  -- `(prod / 2^64) % 2^64 = prod / 2^64` since `prod / 2^64 < 2^64`.
  have hhi : prod / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul hpos]; omega
  rw [Nat.mod_eq_of_lt hhi]
  -- Goal: prod % 2^64 + 2^64 * (prod / 2^64) = prod.
  omega

/-- `addCarry` carry-out is a single bit. -/
theorem addCarry_carry_le (a b : BitVec 64) : (addCarry a b).1.toNat ≤ 1 := by
  simp only [addCarry]
  split_ifs <;> simp

/-- `addCarry` identity: `lo' + 2^64·c = a + b`. -/
theorem addCarry_spec (a b : BitVec 64) :
    (addCarry a b).2.toNat + 2 ^ 64 * (addCarry a b).1.toNat = a.toNat + b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  simp only [addCarry, BitVec.ult, decide_eq_true_eq, BitVec.toNat_add]
  split_ifs with h
  · -- wrapped: r < a, so a + b ≥ 2^64; carry 1.
    simp only [show ((1 : BitVec 64).toNat) = 1 from rfl]
    omega
  · -- no wrap; carry 0.
    simp only [show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.not_lt] at h ⊢
    omega

/-- The high word of `mulx b a` is at most `2^64 - 2` (the standard schoolbook
    fact that lets `cy' = hi + c` never overflow). -/
theorem mulx_hi_le (a b : BitVec 64) : (mulx b a).1.toNat ≤ 2 ^ 64 - 2 := by
  have ha := a.isLt; have hb := b.isLt
  unfold mulx
  simp only [BitVec.toNat_ofNat]
  set prod : Nat := b.toNat * a.toNat with hprod
  have hpos : (0 : Nat) < 2 ^ 64 := by positivity
  rw [Nat.shiftRight_eq_div_pow]
  have hhi : prod / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    -- prod ≤ (2^64-1)·(2^64-1), a fixed numeral whose floor-division by 2^64
    -- is exactly 2^64-2.  Compute via monotonicity of `/` then a numeral fact.
    have hp : prod ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
      rw [hprod]; exact Nat.mul_le_mul (by omega) (by omega)
    calc prod / 2 ^ 64
        ≤ ((2 ^ 64 - 1) * (2 ^ 64 - 1)) / 2 ^ 64 := Nat.div_le_div_right hp
      _ = 2 ^ 64 - 2 := by norm_num
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hhi

/-- The single-step MUL identity, on `Nat`:
    `mul1Step a b cy` produces `(out, cy')` with
    `out + 2^64·cy' = a·b + cy`. -/
theorem mul1Step_spec (a b cy : BitVec 64) :
    (mul1Step a b cy).1.toNat + 2 ^ 64 * (mul1Step a b cy).2.toNat
      = a.toNat * b.toNat + cy.toNat := by
  -- The two projections of `mul1Step` are definitionally the executable pieces.
  rw [show (mul1Step a b cy).1 = (addCarry (mulx b a).2 cy).2 from rfl,
      show (mul1Step a b cy).2 = (mulx b a).1 + (addCarry (mulx b a).2 cy).1 from rfl]
  -- (hi, lo) = mulx b a; (c, lo') = addCarry lo cy; out = lo'; cy' = hi + c.
  set hi := (mulx b a).1 with hhi
  set lo := (mulx b a).2 with hlo
  set c := (addCarry lo cy).1 with hc
  set lo' := (addCarry lo cy).2 with hlo'
  -- mulx: lo + 2^64·hi = b·a = a·b.
  have hmulx : lo.toNat + 2 ^ 64 * hi.toNat = a.toNat * b.toNat := by
    rw [hlo, hhi, mulx_toNat b a]; ring
  -- addCarry: lo' + 2^64·c = lo + cy.
  have hadd : lo'.toNat + 2 ^ 64 * c.toNat = lo.toNat + cy.toNat := by
    rw [hlo', hc, addCarry_spec lo cy]
  -- cy' = hi + c, no wrap (hi ≤ 2^64-2, c ≤ 1).
  have hcle : c.toNat ≤ 1 := by rw [hc]; exact addCarry_carry_le lo cy
  have hhile : hi.toNat ≤ 2 ^ 64 - 2 := by rw [hhi]; exact mulx_hi_le a b
  have hcy' : (hi + c).toNat = hi.toNat + c.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [hcy']
  -- out + 2^64·(hi + c) = (lo + 2^64·c) + 2^64·hi = (lo + cy) + (a·b - lo) ...
  -- Combine the two identities linearly.
  have hlobound : lo.toNat < 2 ^ 64 := lo.isLt
  have hcybound : cy.toNat < 2 ^ 64 := cy.isLt
  omega

/-- **Main functional spec — proved by induction on the limb list.**

    For any limb list `a`, scalar `b`, and carry-in `cy`, the pure reference
    `mpnMul1` satisfies the multi-precision single-limb multiplication identity:
    the denotation of the output limbs plus the final carry-out shifted to bit
    `64·|a|` equals `toNat a · b + cy`.

    This is the inductive invariant the emitted `while (n != 0)` loop maintains:
    each iteration peels one limb (`mul1Step_spec`), and the IH carries the
    identity over the `2^64`-scaled tail. -/
theorem mpnMul1_spec :
    ∀ (a : List (BitVec 64)) (b cy : BitVec 64),
      toNat (mpnMul1 a b cy).1 + (2 ^ 64) ^ a.length * (mpnMul1 a b cy).2.toNat
      = toNat a * b.toNat + cy.toNat := by
  intro a
  induction a with
  | nil =>
    intro b cy
    simp [mpnMul1, toNat]
  | cons a as ih =>
    intro b cy
    set p := mul1Step a b cy with hp
    have hstep := mul1Step_spec a b cy
    rw [← hp] at hstep
    set q := mpnMul1 as b p.2 with hq
    have htail := ih b p.2
    rw [← hq] at htail
    have hunfold : mpnMul1 (a :: as) b cy = (p.1 :: q.1, q.2) := by
      simp only [mpnMul1, hp, hq]
    rw [hunfold]
    simp only [toNat, List.length_cons]
    have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
      rw [pow_succ]; ring
    rw [hpow]
    -- IH scaled by 2^64 + head step (mul1Step_spec) close the linear goal.
    have hkey : 2 ^ 64 * toNat q.1 + 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat)
        = 2 ^ 64 * (toNat as * b.toNat + p.2.toNat) := by
      rw [← htail]; ring
    have hmono : 2 ^ 64 * (2 ^ 64) ^ as.length * q.2.toNat
        = 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat) := by ring
    rw [hmono]
    -- Goal: p.1.toNat + 2^64*toNat q.1 + 2^64*(...) = (a.toNat + 2^64*toNat as)*b + cy.
    have hexpand : (a.toNat + 2 ^ 64 * toNat as) * b.toNat
        = a.toNat * b.toNat + 2 ^ 64 * (toNat as * b.toNat) := by ring
    rw [hexpand]
    omega

/-- The usual entry point: carry-in 0.  `mpn_mul_1` with no incoming carry
    multiplies a bignum by a scalar; the result plus the carry-out at bit
    `64·|a|` equals `toNat a · b` (the GMP `mpn_mul_1` contract — the return
    value is the carry-out). -/
theorem mpnMul1_spec_carryIn_zero (a : List (BitVec 64)) (b : BitVec 64) :
    toNat (mpnMul1 a b 0).1 + (2 ^ 64) ^ a.length * (mpnMul1 a b 0).2.toNat
      = toNat a * b.toNat := by
  have h := mpnMul1_spec a b 0
  simpa using h

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `[0xFFFF…FFFF] · 3` = `0x2_FFFFFFFFFFFFFFFD`: limb `0xFFFFFFFFFFFFFFFD`,
    carry `2`. -/
example : mpnMul1 [(-1 : BitVec 64)] 3 0 = ([0xFFFFFFFFFFFFFFFD], 2) := by
  native_decide

/-- `[5, 7] · 2` = `[10, 14]`, no carry. -/
example : mpnMul1 [5, 7] 2 0 = ([10, 14], 0) := by native_decide

/-- Carry propagation: `[2^63, 0] · 2 = [0, 1]` (top bit carries into limb 1). -/
example : mpnMul1 [(BitVec.ofNat 64 (2 ^ 63)), 0] 2 0 = ([0, 1], 0) := by
  native_decide

#eval toNat (mpnMul1 [(-1 : BitVec 64)] 3 0).1
        + 2 ^ 64 * (mpnMul1 [(-1 : BitVec 64)] 3 0).2.toNat   -- 3·(2^64-1)

/-! ## §6  MULX / ADD bridge: executable intrinsics match the pure step

The emitted `#MULX` runs `BignumExec.mulx`; the emitted `#ADD_64` runs
`BignumExec.addCarry`.  The pure `mul1Step` is *defined* directly in terms of
`mulx`/`addCarry`, so the bridge is definitional — recorded here for clarity. -/

theorem mul1Step_out (a b cy : BitVec 64) :
    (addCarry (mulx b a).2 cy).2 = (mul1Step a b cy).1 := rfl

theorem mul1Step_carry (a b cy : BitVec 64) :
    (mulx b a).1 + (addCarry (mulx b a).2 cy).1 = (mul1Step a b cy).2 := rfl

/-! ## §7  One loop iteration as an explicit state update

`loopBodyMul` is straight-line, so it runs via `bignumExec`.  This lemma
computes the exact effect of one `loopBodyMul` pass: load `a` from `ap`, MULX
by the scalar `b`, add the running carry, store the low word at `op`,
recombine `cy = hi + c`, advance `ap`/`op` by 8 and decrement `n`. -/

/-- `resolveAddr` of a register at offset 0 yields its `UInt64` address. -/
theorem resolveAddr_reg (s : BignumState) (x : String) :
    resolveAddr s { var := vr x } (.Pconst 0) = some (regAddr s x) := by
  simp only [resolveAddr, regAddr, vr]
  norm_num

theorem bignumExec_loopBodyMul_step (s : BignumState) (a : BitVec 64) (cy : BitVec 64)
    (hcy : s.regs "cy" = cy)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat)) :
    ∃ s', bignumExec loopBodyMul s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (mul1Step a (s.regs "b") cy).1.toNat) ∧
      s'.regs "cy" = (mul1Step a (s.regs "b") cy).2 ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 ∧
      s'.regs "b" = s.regs "b" := by
  simp only [loopBodyMul, loadAt0, mulxCopn, addCopn, storeAt0, regAdd, binImm,
             flag_pre, flag_post,
             bignumExec, execInstr, evalPExpr, pv, resolveAddr_reg, vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append,
             writeMulxBundle, writeSubBundle]
  -- Resolve the load address (offset 0), fire the load (`ha`), decode the word.
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.  Read off the store, the `cy`
  -- register, the three register advances, and `b` invariance.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte, hcy,
               mul1Step, show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-- `loopBodyMul` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodyMul_straightLine : InstrR.bodyIsStraightLine loopBodyMul := by
  simp only [loopBodyMul, loadAt0, mulxCopn, addCopn, storeAt0, regAdd, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodyMul` is non-control. -/
theorem loopBodyMul_nonControl : ∀ i ∈ loopBodyMul, i.isNonControl := by
  intro i hi
  simp only [loopBodyMul, loadAt0, mulxCopn, addCopn, storeAt0, regAdd, binImm,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §8  One `Cwhile` iteration over `bignumExecFuel`

The imported `bignumExecFuel_loop_step` is hardcoded to `loopBody`, so we
re-instantiate the *same* proof for `loopBodyMul`.  `bignumExecFuel_loop_exit`
is already generic over the body, so it is reused directly. -/

/-- **Forward one-iteration rule** for `loopBodyMul` — same proof shape as the
    imported `bignumExecFuel_loop_step`, specialised to the MUL body. -/
theorem bignumExecFuel_loopMul_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodyMul s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodyMul] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodyMul] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodyMul s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodyMul s loopBodyMul_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodyMul [.Cwhile [] cond loopBodyMul]
        loopBodyMul_nonControl s s_mid s' hsl hrec]

/-! ## §9  Loop-guard evaluation, machine-checked (local `pv`). -/

/-- The loop guard `n != 0` evaluates to `1` when register `n` is nonzero. -/
theorem evalPExpr_loopCond_true (s : BignumState) (hn : s.regs "n" ≠ 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 1 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_neg hn]

/-- The loop guard `n != 0` evaluates to `0` when register `n` is `0`. -/
theorem evalPExpr_loopCond_false (s : BignumState) (hn : s.regs "n" = 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 0 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_pos hn]

/-! ## §10  Assembly: `MpnMul1JasminRefines`

The full bridge.  Structurally mirrors `mpnAddN_loop` → `MpnAddNJasminRefines`:
induction on the limb list, each step peeling one limb via
`bignumExec_loopBodyMul_step` and `bignumExecFuel_loopMul_step`, preserving the
unread `ap` suffix across the `op[i]` store with `load64Mem_store64_disjoint`,
and threading the u64 carry via `mul1Step`.  The scalar multiplier `b` lives in
a register and is read-only, so only op-vs-ap separation is needed. -/

/-- The bridge statement (mirror of `MpnAddNRefinesStmt`, single-buffer input).
    The scalar `b` is `s.regs "b"`; only op-vs-ap disjointness is required (the
    `b` register is never dereferenced). -/
def MpnMul1RefinesStmt : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (fuel : Nat),
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyMul s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnMul1 as (s.regs "b") 0).1 ∧
      s'.regs "cy" = (mpnMul1 as (s.regs "b") 0).2

/-- **The loop, by induction on the limb list.**  Mirror of `mpnAddN_loop`,
    single-buffer (the scalar `b` is read-only in a register, so it is fixed
    across iterations and there is no `bp` advance). -/
theorem mpnMul1_loop :
    ∀ (as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyMul] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnMul1 as (s.regs "b") cy).1 ∧
        s'.regs "cy" = (mpnMul1 as (s.regs "b") cy).2 ∧
        s'.regs "b" = s.regs "b" ∧
        (∀ bb, MemoryModel.Disjoint (range bb 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem bb = load64Mem s.mem bb) := by
  intro as
  induction as with
  | nil =>
    intro s cy extra hcy hn _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodyMul s
        (evalPExpr_loopCond_false s hn0)
    · simp [mpnMul1, memHoldsLimbs]
    · simpa [mpnMul1] using hcy
    · rfl
    · intro bb _; rfl
  | cons a as ih =>
    intro s cy extra hcy hn hap hdoa
    have hpos : 0 < 8 * (as.length + 1) := by omega
    have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
      simpa [List.length_cons] using
        disjoint_range_lt (regAddr s "op") (regAddr s "ap")
          (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
          (by simpa using hdoa)
    have hLsucc : as.length + 1 < 2 ^ 64 := by omega
    have hn_ne : s.regs "n" ≠ 0 := by
      rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
    obtain ⟨hap_head, hap_tail⟩ := hap
    obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
      bignumExec_loopBodyMul_step s a cy hcy hap_head
    set op0 : UInt64 := regAddr s "op" with hop0
    have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
      simp only [regAddr, hs1_ap]; exact regAddr_advance _
    have hra_op : regAddr s1 "op" = op0 + 8 := by
      simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
    have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (mul1Step a (s.regs "b") cy).1.toNat) := by
      simpa [hop0, regAddr] using hs1_mem
    have hdoa_store_aptail :
        MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
      · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "ap") as.length x
          (by simpa [List.length_cons] using h)
    have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
      rw [hra_ap, hmem1]
      exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
        hdoa_store_aptail hap_tail
    have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
        (range (regAddr s1 "ap") (8 * as.length)) := by
      rw [hra_op, hra_ap]
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
      · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "ap") as.length x
          (by simpa [List.length_cons] using h)
    have hcy1 : s1.regs "cy" = (mul1Step a (s.regs "b") cy).2 := hs1_cy
    have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
      rw [hs1_n, hn]
      simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
    -- Apply the IH on the tail with carry `(mul1Step a (s.regs "b") cy).2`.
    obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, hs'_frame⟩ :=
      ih s1 (mul1Step a (s.regs "b") cy).2 extra hcy1 hn1 hap1 hdoa1
    refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
    · have hfuel : 2 * (a :: as).length + 3 + extra
          = (2 * as.length + 2 + extra) + 3 := by
        simp only [List.length_cons]; ring
      rw [hfuel]
      refine bignumExecFuel_loopMul_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
        (evalPExpr_loopCond_true s hn_ne) hs1 ?_
      simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
              from by omega] using hs'
    · rw [hmem1] at hs'_frame
      have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
        range_op_head_tail_disjoint op0 as.length (by omega)
      refine ⟨?_, ?_⟩
      · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
        have hread := load64Mem_store64_same s.mem op0
          (UInt64.ofNat (mul1Step a (s.regs "b") cy).1.toNat)
        rw [hread]
        -- head of `(mpnMul1 (a::as) b cy).1` is `(mul1Step a b cy).1` (definitional).
        rfl
      · -- tail: `(mpnMul1 as b (mul1Step a b cy).2).1`, from IH (op base `op0+8`),
        -- with `s1.regs "b" = s.regs "b"`.
        have hthis := hs'_mem
        rw [hra_op, hs1_b] at hthis
        exact hthis
    · -- carry-out register.
      rw [hs'_cy, hs1_b]; simp only [mpnMul1]
    · -- `b` register invariant.
      rw [hs'_b, hs1_b]
    · -- frame.
      intro bb hbb
      rw [hmem1] at hs'_frame
      have hbb_tail : MemoryModel.Disjoint (range bb 8)
          (range (regAddr s1 "op") (8 * as.length)) := by
        rw [hra_op]
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        exact range_shift_subset (regAddr s "op") as.length x
          (by simpa [List.length_cons] using h)
      rw [hs'_frame bb hbb_tail]
      have hbb_head : MemoryModel.Disjoint (range bb 8) (range (regAddr s "op") 8) := by
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        exact range_head_subset (regAddr s "op") as.length x
          (by simpa [List.length_cons] using h)
      rw [load64Mem_store64_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-- **The bridge, fully proved.**  `mpnMul1Fd.body` (the emitted
    `cy := 0; while (n != 0) { loopBodyMul }`) refines the pure reference
    `mpnMul1` over byte memory.  Mirror of `MpnAddNJasminRefines`. -/
theorem MpnMul1JasminRefines : MpnMul1RefinesStmt := by
  intro s as fuel hn hap hdoa hfuel
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
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; exact hap
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; exact hdoa
  have hb0 : s0.regs "b" = s.regs "b" := hreg0 "b" (by decide)
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, _⟩ :=
    mpnMul1_loop as s0 0 extra hcy0 hn0' hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodyMul s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyMul] s0 := by
      conv_lhs => rw [bodyMul]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    rw [hb0] at hs'_mem
    exact hs'_mem
  · rw [hs'_cy, hb0]

end CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype
