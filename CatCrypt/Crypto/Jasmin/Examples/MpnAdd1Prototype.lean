/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

set_option autoImplicit false

/-!
# Phase 2 — verified variable-length `mpn_add_1` / `mpn_sub_1` by template reuse

**EXPERIMENTAL FILE.**  Companion to `MpnAddPrototype.lean` /
`MpnSubPrototype.lean` / `MpnMul1Prototype.lean`.  It proves the GMP
single-limb-operand kernels

* `mpn_add_1(op, ap, n, b)` — `out[] = a[] + b`, with `b` a single limb
  added at position 0 and the carry propagating upward;
* `mpn_sub_1(op, ap, n, b)` — `out[] = a[] - b`, with `b` a single limb
  subtracted at position 0 and the borrow propagating upward;

end-to-end against the Jasmin `Cwhile` semantics — reusing the Phase-1
loop-invariant machinery verbatim.

## The single-limb-operand shape (vs. `add_n` / `mul_1`)

Unlike `mpn_add_n` (two memory arrays `ap`, `bp`), the second operand of
`mpn_add_1` is a *single limb* `b` added only at position 0.  The carry
chain is therefore: `cy₀ = b`, and each limb does `(out[i], cy_{i+1}) =
ADD_64(a[i], cy_i)` — a *two-operand* `#ADD_64` whose second input is the
running carry register, initialised to `b` instead of `0`.  After the
first iteration the carry register holds only a 0/1 carry bit, so the
remaining iterations are pure carry propagation.

This is structurally `mpn_mul_1` with the multiplier collapsed to `1` and
the `#MULX` dropped: a single input buffer `ap`, the scalar `b` threaded
through a register (here *as the carry seed*), and only an op-vs-ap
separation hypothesis (there is no `bp` buffer to dereference).  We
therefore reuse the `MpnMul1Prototype`-style single-buffer induction
skeleton.

`mpn_sub_1` is the exact mirror: the borrow register seeds with `b`, each
limb does `(out[i], bw_{i+1}) = SUB_64(a[i], bw_i)` (a two-operand
`#SUB_64`), and the borrow propagates.

## What is reused (kernel-agnostic, imported from `MpnAddPrototype`)

* **Memory algebra** (`load64Mem_store64_same`, `load64Mem_store64_disjoint`).
* **The `Cwhile` fuel rule** (`bignumExecFuel_loop_exit`; the step lemma is
  hardcoded to add-n's `loopBody`, so we re-instantiate it locally).
* **The memory-frame plumbing** (`memHoldsLimbs`, `memHoldsLimbs_store64_frame`,
  `range_shift_subset`, `range_head_subset`, `disjoint_mono`,
  `range_op_head_tail_disjoint`, `disjoint_range_lt`).
* **The counter algebra** (`ofNat64_toNat`, `ofNat64_succ_ne_zero`,
  `ofNat64_succ_sub_one`, `regAddr`, `regAddr_advance`, `bv_uint_roundtrip`,
  the `setReg`/`storeMem` projection simp lemmas).
* **The single-buffer induction skeleton** (`mpnMul1_loop` →
  `MpnMul1JasminRefines`) — copied structurally; only the per-limb step
  and the threaded value change.

## What is genuinely new (the single-limb-operand arithmetic)

* §2–§3: the pure references `mpnAdd1` / `mpnSub1` + the one-limb leaf
  identities, derived directly from the executable `addCarry` / `subBorrow`
  (the two-operand ADD/SUB-with-carry/borrow-out intrinsics).
* §7: the one-iteration state updates (`#ADD_64` / `#SUB_64`, store, carry
  recombination `cy = cy` / `bw = bw`, two pointer/counter updates).

## Functional specs

`mpnAdd1 a cy` and `mpnSub1 a bw` satisfy the single-limb multi-precision
identities (carry/borrow threaded through a u64 register, seeded with `b`):

```
toNat (mpnAdd1 a cy).1 + (2^64)^|a| · (mpnAdd1 a cy).2.toNat = toNat a + cy.toNat
toNat (mpnSub1 a bw).1 + bw.toNat = toNat a + (2^64)^|a| · (mpnSub1 a bw).2.toNat
```

so at the entry seed `cy = b` (resp. `bw = b`):

```
out + (2^64)^n · carry  = a + b            (mpn_add_1)
out + b                 = a + (2^64)^n · borrow  (mpn_sub_1)
```

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnAdd1Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

/-! ## §1  The Jasmin `mpn_add_1` / `mpn_sub_1` bodies — runtime `Cwhile` loops

The inner intrinsic is the *two-operand* `#ADD_64` (resp. `#SUB_64`),
whose second input is the running carry (resp. borrow) register.  Both
share the standard 6-LVal output bundle `[of, cf, sf, pf, zf, dst]`
(`writeSubBundle`), so the emitter/interpreter plumbing is reused
unchanged.

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

def flag_pre  : List LVal := [.Lnone {} (.sword .U64)]
def flag_post : List LVal := List.replicate 3 (.Lnone {} (.sword .U64))

/-- `_, cf, _, _, _, r = #ADD_64(a, b);` — two-operand ADD-with-carry-out,
    capturing the carry-out `cf` and the sum `r`.  Same 6-LVal bundle as
    `#ADC_64`. -/
def addCopn (cfName rName aName bName : String) : InstrR :=
  .Copn (flag_pre ++ [.Lvar { var := vr cfName }] ++ flag_post
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"ADD_64"⟩)
        [pv aName, pv bName]

/-- `_, cf, _, _, _, r = #SUB_64(a, b);` — two-operand SUB-with-borrow-out,
    capturing the borrow-out `cf` and the difference `r`. -/
def subCopn (cfName rName aName bName : String) : InstrR :=
  .Copn (flag_pre ++ [.Lvar { var := vr cfName }] ++ flag_post
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"SUB_64"⟩)
        [pv aName, pv bName]

/-- `dst = src` (register copy).  Here used (as `cy = cy` / `bw = bw`) only to
    keep the loop-body shape uniform with the `#ADC_64` template; the carry-out
    is captured directly into the threaded register `cy`/`bw`, so this copy is a
    no-op the emitter folds away. -/
def regMov (dst src : String) : InstrR :=
  .Cassgn (.Lvar { var := vr dst }) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- One loop iteration body for `mpn_add_1`:
    ```
    t = [:u64 ap + 0];
    _, cy, _, _, _, r = #ADD_64(t, cy);
    [:u64 op + 0] = r;
    cy = cy;
    ap += 8; op += 8;
    n  -= 1;
    ```
    The `#ADD_64` carry-out is captured directly into the threaded register
    `cy` (a GPR, so the emitter materializes it via `#SETcc` + zero-extend —
    no `reg bool → u64` glue).  `cy` is initialised to the single limb `b`
    before the loop (so the first iteration's `#ADD_64(a[0], cy)` is
    `a[0] + b`); afterward `cy` holds only the 0/1 propagated carry. -/
def loopBodyAdd1 : List InstrR :=
  [ loadAt0 "t" "ap"
  , addCopn "cy" "r" "t" "cy"
  , storeAt0 "op" "r"
  , regMov "cy" "cy"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- One loop iteration body for `mpn_sub_1` — the `#SUB_64` mirror of
    `loopBodyAdd1`.  `bw` is seeded with the single limb `b`. -/
def loopBodySub1 : List InstrR :=
  [ loadAt0 "t" "ap"
  , subCopn "bw" "r" "t" "bw"
  , storeAt0 "op" "r"
  , regMov "bw" "bw"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_add_1`:
    ```
    cy = b;
    while (n != 0) { <loopBodyAdd1> }
    ```
    The seed `cy := b` makes the first iteration add the single limb;
    `cy` holds the final carry (the GMP `mpn_add_1` ABI returns it). -/
def bodyAdd1 : List InstrR :=
  [ regMov "cy" "b"
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAdd1 ]

/-- Full body of `mpn_sub_1`:
    ```
    bw = b;
    while (n != 0) { <loopBodySub1> }
    ```
    The seed `bw := b` makes the first iteration subtract the single limb;
    `bw` holds the final borrow (the GMP `mpn_sub_1` ABI returns it). -/
def bodySub1 : List InstrR :=
  [ regMov "bw" "b"
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub1 ]

/-- `mpn_add_1(op, ap, n, b)` as a Jasmin `FunDecl`.  Void return (output
    via `op`); the single limb `b` is passed by value in a register. -/
def mpnAdd1Fd : FunDecl where
  name := { name := "mpn_add_1" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "n" }⟩, ⟨{ var := vr "b" }⟩]
  body := bodyAdd1
  results := []

/-- `mpn_sub_1(op, ap, n, b)` as a Jasmin `FunDecl`. -/
def mpnSub1Fd : FunDecl where
  name := { name := "mpn_sub_1" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "n" }⟩, ⟨{ var := vr "b" }⟩]
  body := bodySub1
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the
    public length `n`, never a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodyAdd1 = true := by decide
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodySub1 = true := by decide

/-- Emit the real `.jazz` source. -/
def emittedAdd1 : Option String := emitFunDecl mpnAdd1Fd
def emittedSub1 : Option String := emitFunDecl mpnSub1Fd

#eval match emittedAdd1 with | some s => s | none => "EMIT FAILED"
#eval match emittedSub1 with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional references + the one-limb ADD/SUB steps

The per-limb leaves are *defined* directly via the executable `addCarry`
/ `subBorrow` (two-operand, 64-bit, carry/borrow-out), so the §7 bridge is
definitional. -/

/-- One `mpn_add_1` step on `BitVec 64`: add limb `a` to the running carry
    `cy`, returning `(out_limb, carry-out)`.  Defined via the executable
    `addCarry` (which returns `(cf, r)`), so the bridge is direct. -/
def add1Step (a cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  let (cf, r) := addCarry a cy
  (r, cf)

/-- One `mpn_sub_1` step on `BitVec 64`: subtract the running borrow `bw`
    from limb `a`, returning `(out_limb, borrow-out)`. -/
def sub1Step (a bw : BitVec 64) : BitVec 64 × BitVec 64 :=
  let (bf, r) := subBorrow a bw
  (r, bf)

/-- Pure reference for `mpn_add_1`: walk the limb list adding the running
    carry `cy` (seeded with the single limb `b`).  Returns
    `(result limbs, final carry-out)`. -/
def mpnAdd1 : List (BitVec 64) → BitVec 64 → (List (BitVec 64) × BitVec 64)
  | a :: as, cy =>
      let (r, cy') := add1Step a cy
      let (rs, fcy) := mpnAdd1 as cy'
      (r :: rs, fcy)
  | [], cy => ([], cy)

/-- Pure reference for `mpn_sub_1`: walk the limb list subtracting the
    running borrow `bw` (seeded with the single limb `b`). -/
def mpnSub1 : List (BitVec 64) → BitVec 64 → (List (BitVec 64) × BitVec 64)
  | a :: as, bw =>
      let (r, bw') := sub1Step a bw
      let (rs, fbw) := mpnSub1 as bw'
      (r :: rs, fbw)
  | [], bw => ([], bw)

/-! ## §3  Functional specs: the carry / borrow chain invariants

The load-bearing theorems.  `bv_decide` cannot close an unbounded loop;
the inductive invariant is the per-limb identity, fed by the §2 leaf. -/

/-- `addCarry` carry-out is a single bit. -/
theorem addCarry_carry_le (a b : BitVec 64) : (addCarry a b).1.toNat ≤ 1 := by
  simp only [addCarry]
  split_ifs <;> simp

/-- `addCarry` identity: `r + 2^64·cf = a + b`. -/
theorem addCarry_spec (a b : BitVec 64) :
    (addCarry a b).2.toNat + 2 ^ 64 * (addCarry a b).1.toNat = a.toNat + b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  simp only [addCarry, BitVec.ult, decide_eq_true_eq, BitVec.toNat_add]
  split_ifs with h
  · simp only [show ((1 : BitVec 64).toNat) = 1 from rfl]; omega
  · simp only [show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.not_lt] at h ⊢; omega

/-- The single-step ADD identity, on `Nat`:
    `add1Step a cy` produces `(out, cy')` with `out + 2^64·cy' = a + cy`. -/
theorem add1Step_spec (a cy : BitVec 64) :
    (add1Step a cy).1.toNat + 2 ^ 64 * (add1Step a cy).2.toNat = a.toNat + cy.toNat := by
  rw [show (add1Step a cy).1 = (addCarry a cy).2 from rfl,
      show (add1Step a cy).2 = (addCarry a cy).1 from rfl]
  exact addCarry_spec a cy

/-- `subBorrow` borrow-out is a single bit. -/
theorem subBorrow_borrow_le (a b : BitVec 64) : (subBorrow a b).1.toNat ≤ 1 := by
  simp only [subBorrow]
  split_ifs <;> simp

/-- `subBorrow` identity: `r + b + ... ` stated all-additions:
    `r + b = a + 2^64·bf` (the difference plus the subtrahend equals the
    minuend plus the borrow at bit 64). -/
theorem subBorrow_spec (a b : BitVec 64) :
    (subBorrow a b).2.toNat + b.toNat
      = a.toNat + 2 ^ 64 * (subBorrow a b).1.toNat := by
  have ha := a.isLt; have hb := b.isLt
  -- `(a - b).toNat = (a.toNat + (2^64 - b.toNat)) % 2^64` (operand order
  -- normalized via `Nat.add_comm` so we don't depend on `toNat_sub`'s form).
  have hsub : (a - b).toNat = (a.toNat + (2 ^ 64 - b.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, Nat.add_comm]
  simp only [subBorrow, BitVec.ult, decide_eq_true_eq, hsub]
  split_ifs with h
  · -- underflow: a < b, borrow 1.  `(a + (2^64 - b)) % 2^64 = a + 2^64 - b`.
    simp only [show ((1 : BitVec 64).toNat) = 1 from rfl]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · -- no underflow: a ≥ b, borrow 0.  `(a + (2^64 - b)) % 2^64 = a - b`.
    simp only [show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.not_lt] at h ⊢
    rw [show a.toNat + (2 ^ 64 - b.toNat) = (a.toNat - b.toNat) + 2 ^ 64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The single-step SUB identity, on `Nat`:
    `sub1Step a bw` produces `(out, bw')` with `out + bw = a + 2^64·bw'`. -/
theorem sub1Step_spec (a bw : BitVec 64) :
    (sub1Step a bw).1.toNat + bw.toNat = a.toNat + 2 ^ 64 * (sub1Step a bw).2.toNat := by
  rw [show (sub1Step a bw).1 = (subBorrow a bw).2 from rfl,
      show (sub1Step a bw).2 = (subBorrow a bw).1 from rfl]
  exact subBorrow_spec a bw

/-- **Main functional spec for `mpn_add_1` — proved by induction on the limb
    list.**  The denotation of the output limbs plus the final carry-out
    shifted to bit `64·|a|` equals `toNat a + cy` (the running carry, seeded
    with the single limb `b`). -/
theorem mpnAdd1_spec :
    ∀ (a : List (BitVec 64)) (cy : BitVec 64),
      toNat (mpnAdd1 a cy).1 + (2 ^ 64) ^ a.length * (mpnAdd1 a cy).2.toNat
      = toNat a + cy.toNat := by
  intro a
  induction a with
  | nil =>
    intro cy
    simp [mpnAdd1, toNat]
  | cons a as ih =>
    intro cy
    set p := add1Step a cy with hp
    have hstep := add1Step_spec a cy
    rw [← hp] at hstep
    set q := mpnAdd1 as p.2 with hq
    have htail := ih p.2
    rw [← hq] at htail
    have hunfold : mpnAdd1 (a :: as) cy = (p.1 :: q.1, q.2) := by
      simp only [mpnAdd1, hp, hq]
    rw [hunfold]
    simp only [toNat, List.length_cons]
    have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
      rw [pow_succ]; ring
    rw [hpow]
    have hkey : 2 ^ 64 * toNat q.1 + 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat)
        = 2 ^ 64 * (toNat as + p.2.toNat) := by
      rw [← htail]; ring
    have hmono : 2 ^ 64 * (2 ^ 64) ^ as.length * q.2.toNat
        = 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat) := by ring
    rw [hmono]
    omega

/-- **Main functional spec for `mpn_sub_1` — proved by induction on the limb
    list.**  Stated all-additions to stay Nat-safe:
    `toNat out + bw = toNat a + (2^64)^|a| · borrow-out`. -/
theorem mpnSub1_spec :
    ∀ (a : List (BitVec 64)) (bw : BitVec 64),
      toNat (mpnSub1 a bw).1 + bw.toNat
      = toNat a + (2 ^ 64) ^ a.length * (mpnSub1 a bw).2.toNat := by
  intro a
  induction a with
  | nil =>
    intro bw
    simp [mpnSub1, toNat]
  | cons a as ih =>
    intro bw
    set p := sub1Step a bw with hp
    have hstep := sub1Step_spec a bw
    rw [← hp] at hstep
    set q := mpnSub1 as p.2 with hq
    have htail := ih p.2
    rw [← hq] at htail
    have hunfold : mpnSub1 (a :: as) bw = (p.1 :: q.1, q.2) := by
      simp only [mpnSub1, hp, hq]
    rw [hunfold]
    simp only [toNat, List.length_cons]
    have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
      rw [pow_succ]; ring
    rw [hpow]
    -- htail, scaled by 2^64, shaped to match the goal's monomials.
    have hkey : 2 ^ 64 * toNat q.1 + 2 ^ 64 * p.2.toNat
        = 2 ^ 64 * toNat as + 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat) := by
      have := congrArg (2 ^ 64 * ·) htail
      simpa [Nat.mul_add, Nat.add_assoc] using this
    have hmono : 2 ^ 64 * (2 ^ 64) ^ as.length * q.2.toNat
        = 2 ^ 64 * ((2 ^ 64) ^ as.length * q.2.toNat) := by ring
    rw [hmono]
    omega

/-- `mpn_add_1` contract at the entry seed `cy = b`: `out + (2^64)^n · carry
    = a + b`.  The single limb `b` is the carry seed. -/
theorem mpnAdd1_spec_seed (a : List (BitVec 64)) (b : BitVec 64) :
    toNat (mpnAdd1 a b).1 + (2 ^ 64) ^ a.length * (mpnAdd1 a b).2.toNat
      = toNat a + b.toNat :=
  mpnAdd1_spec a b

/-- `mpn_sub_1` contract at the entry seed `bw = b`: `out + b
    = a + (2^64)^n · borrow`.  The single limb `b` is the borrow seed. -/
theorem mpnSub1_spec_seed (a : List (BitVec 64)) (b : BitVec 64) :
    toNat (mpnSub1 a b).1 + b.toNat
      = toNat a + (2 ^ 64) ^ a.length * (mpnSub1 a b).2.toNat :=
  mpnSub1_spec a b

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `[0xFFFF…FFFF] + 1` overflows: limb `0`, carry `1`. -/
example : mpnAdd1 [(-1 : BitVec 64)] 1 = ([0], 1) := by native_decide

/-- Carry propagation: `[0xFFFF…, 0] + 1 = [0, 1]`, no final carry. -/
example : mpnAdd1 [(-1 : BitVec 64), 0] 1 = ([0, 1], 0) := by native_decide

/-- `[5, 7] + 3 = [8, 7]`, no carry. -/
example : mpnAdd1 [5, 7] 3 = ([8, 7], 0) := by native_decide

/-- `[0] - 1` underflows: limb `0xFFFF…FFFF`, borrow `1`. -/
example : mpnSub1 [(0 : BitVec 64)] 1 = ([-1], 1) := by native_decide

/-- Borrow propagation: `[0, 1] - 1 = [0xFFFF…, 0]`, no final borrow. -/
example : mpnSub1 [(0 : BitVec 64), 1] 1 = ([-1, 0], 0) := by native_decide

/-- `[10, 7] - 3 = [7, 7]`, no borrow. -/
example : mpnSub1 [10, 7] 3 = ([7, 7], 0) := by native_decide

#eval toNat (mpnAdd1 [(-1 : BitVec 64), 0] 1).1   -- 2^64

/-! ## §6  ADD / SUB bridge: executable intrinsics match the pure steps

The emitted `#ADD_64` runs `BignumExec.addCarry`; the emitted `#SUB_64`
runs `BignumExec.subBorrow`.  `add1Step` / `sub1Step` are *defined*
directly in terms of these, so the bridge is definitional. -/

theorem add1Step_out (a cy : BitVec 64) : (addCarry a cy).2 = (add1Step a cy).1 := rfl
theorem add1Step_carry (a cy : BitVec 64) : (addCarry a cy).1 = (add1Step a cy).2 := rfl
theorem sub1Step_out (a bw : BitVec 64) : (subBorrow a bw).2 = (sub1Step a bw).1 := rfl
theorem sub1Step_borrow (a bw : BitVec 64) : (subBorrow a bw).1 = (sub1Step a bw).2 := rfl

/-! ## §7  One loop iteration as an explicit state update

`loopBodyAdd1` / `loopBodySub1` are straight-line, so they run via
`bignumExec`.  These lemmas compute the exact effect of one pass: load `a`
from `ap`, ADD/SUB with the running carry/borrow register, store the result
word at `op`, with the carry/borrow-out captured directly into the threaded
register `cy` / `bw`, advance `ap`/`op` by 8 and decrement `n`. -/

/-- `resolveAddr` of a register at offset 0 yields its `UInt64` address. -/
theorem resolveAddr_reg (s : BignumState) (x : String) :
    resolveAddr s { var := vr x } (.Pconst 0) = some (regAddr s x) := by
  simp only [resolveAddr, regAddr, vr]
  norm_num

theorem bignumExec_loopBodyAdd1_step (s : BignumState) (a : BitVec 64) (cy : BitVec 64)
    (hcy : s.regs "cy" = cy)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat)) :
    ∃ s', bignumExec loopBodyAdd1 s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (add1Step a cy).1.toNat) ∧
      s'.regs "cy" = (add1Step a cy).2 ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  simp only [loopBodyAdd1, loadAt0, addCopn, storeAt0, regMov, binImm,
             flag_pre, flag_post,
             bignumExec, execInstr, evalPExpr, pv, resolveAddr_reg, vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  -- Resolve the load address (offset 0), fire the load (`ha`), decode the word.
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.  Read off the store, the `cy`
  -- register (= the captured carry-out), and the register advances.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte, hcy,
               add1Step, show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

theorem bignumExec_loopBodySub1_step (s : BignumState) (a : BitVec 64) (bw : BitVec 64)
    (hbw : s.regs "bw" = bw)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat)) :
    ∃ s', bignumExec loopBodySub1 s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (sub1Step a bw).1.toNat) ∧
      s'.regs "bw" = (sub1Step a bw).2 ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  simp only [loopBodySub1, loadAt0, subCopn, storeAt0, regMov, binImm,
             flag_pre, flag_post,
             bignumExec, execInstr, evalPExpr, pv, resolveAddr_reg, vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte, hbw,
               sub1Step, show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-- `loopBodyAdd1` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodyAdd1_straightLine : InstrR.bodyIsStraightLine loopBodyAdd1 := by
  simp only [loopBodyAdd1, loadAt0, addCopn, storeAt0, regMov, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

theorem loopBodySub1_straightLine : InstrR.bodyIsStraightLine loopBodySub1 := by
  simp only [loopBodySub1, loadAt0, subCopn, storeAt0, regMov, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodyAdd1` is non-control. -/
theorem loopBodyAdd1_nonControl : ∀ i ∈ loopBodyAdd1, i.isNonControl := by
  intro i hi
  simp only [loopBodyAdd1, loadAt0, addCopn, storeAt0, regMov, binImm,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> (subst h; exact True.intro)

theorem loopBodySub1_nonControl : ∀ i ∈ loopBodySub1, i.isNonControl := by
  intro i hi
  simp only [loopBodySub1, loadAt0, subCopn, storeAt0, regMov, binImm,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §8  One `Cwhile` iteration over `bignumExecFuel`

The imported `bignumExecFuel_loop_step` is hardcoded to add-n's `loopBody`,
so we re-instantiate the *same* proof for our two bodies.
`bignumExecFuel_loop_exit` is generic over the body, so it is reused. -/

theorem bignumExecFuel_loopAdd1_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodyAdd1 s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodyAdd1] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodyAdd1] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodyAdd1 s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodyAdd1 s loopBodyAdd1_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodyAdd1 [.Cwhile [] cond loopBodyAdd1]
        loopBodyAdd1_nonControl s s_mid s' hsl hrec]

theorem bignumExecFuel_loopSub1_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodySub1 s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodySub1] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodySub1] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodySub1 s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodySub1 s loopBodySub1_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodySub1 [.Cwhile [] cond loopBodySub1]
        loopBodySub1_nonControl s s_mid s' hsl hrec]

/-! ## §9  Loop-guard evaluation, machine-checked (local `pv`). -/

theorem evalPExpr_loopCond_true (s : BignumState) (hn : s.regs "n" ≠ 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 1 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_neg hn]

theorem evalPExpr_loopCond_false (s : BignumState) (hn : s.regs "n" = 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 0 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_pos hn]

/-! ## §10  Assembly: `MpnAdd1JasminRefines` / `MpnSub1JasminRefines`

The full bridges.  Structurally mirror `mpnMul1_loop` →
`MpnMul1JasminRefines`: induction on the limb list, each step peeling one
limb via the §7 step lemma and the §8 fuel rule, preserving the unread
`ap` suffix across the `op[i]` store with `load64Mem_store64_disjoint`,
and threading the carry/borrow via `add1Step` / `sub1Step`.  The single
limb `b` lives in the carry/borrow register, so only op-vs-ap separation
is needed (there is no `bp` buffer). -/

/-- The bridge statement for `mpn_add_1` (single-buffer input; the carry
    register is seeded with the single limb `b`). -/
def MpnAdd1RefinesStmt : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (fuel : Nat),
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyAdd1 s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnAdd1 as (s.regs "b")).1 ∧
      s'.regs "cy" = (mpnAdd1 as (s.regs "b")).2

/-- The bridge statement for `mpn_sub_1` (single-buffer input; the borrow
    register is seeded with the single limb `b`). -/
def MpnSub1RefinesStmt : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (fuel : Nat),
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodySub1 s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnSub1 as (s.regs "b")).1 ∧
      s'.regs "bw" = (mpnSub1 as (s.regs "b")).2

/-- **The `mpn_add_1` loop, by induction on the limb list.**  Mirror of
    `mpnMul1_loop`, single-buffer: the running carry register `cy` is the
    only threaded value (the single limb `b` is its seed). -/
theorem mpnAdd1_loop :
    ∀ (as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAdd1] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnAdd1 as cy).1 ∧
        s'.regs "cy" = (mpnAdd1 as cy).2 ∧
        (∀ bb, MemoryModel.Disjoint (range bb 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem bb = load64Mem s.mem bb) := by
  intro as
  induction as with
  | nil =>
    intro s cy extra hcy hn _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodyAdd1 s
        (evalPExpr_loopCond_false s hn0)
    · simp [mpnAdd1, memHoldsLimbs]
    · simpa [mpnAdd1] using hcy
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
    obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n⟩ :=
      bignumExec_loopBodyAdd1_step s a cy hcy hap_head
    set op0 : UInt64 := regAddr s "op" with hop0
    have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
      simp only [regAddr, hs1_ap]; exact regAddr_advance _
    have hra_op : regAddr s1 "op" = op0 + 8 := by
      simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
    have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (add1Step a cy).1.toNat) := by
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
    have hcy1 : s1.regs "cy" = (add1Step a cy).2 := hs1_cy
    have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
      rw [hs1_n, hn]
      simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
    obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_frame⟩ :=
      ih s1 (add1Step a cy).2 extra hcy1 hn1 hap1 hdoa1
    refine ⟨s', ?_, ?_, ?_, ?_⟩
    · have hfuel : 2 * (a :: as).length + 3 + extra
          = (2 * as.length + 2 + extra) + 3 := by
        simp only [List.length_cons]; ring
      rw [hfuel]
      refine bignumExecFuel_loopAdd1_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
        (evalPExpr_loopCond_true s hn_ne) hs1 ?_
      simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
              from by omega] using hs'
    · rw [hmem1] at hs'_frame
      have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
        range_op_head_tail_disjoint op0 as.length (by omega)
      refine ⟨?_, ?_⟩
      · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
        have hread := load64Mem_store64_same s.mem op0
          (UInt64.ofNat (add1Step a cy).1.toNat)
        rw [hread]
        rfl
      · have hthis := hs'_mem
        rw [hra_op] at hthis
        exact hthis
    · rw [hs'_cy]; simp only [mpnAdd1]
    · intro bb hbb
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

/-- **The `mpn_sub_1` loop, by induction on the limb list.**  Mirror of
    `mpnAdd1_loop` with `add1Step`/`#ADD_64`/`cy` swapped for
    `sub1Step`/`#SUB_64`/`bw`. -/
theorem mpnSub1_loop :
    ∀ (as : List (BitVec 64)) (s : BignumState) (bw : BitVec 64) (extra : Nat),
      s.regs "bw" = bw →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub1] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnSub1 as bw).1 ∧
        s'.regs "bw" = (mpnSub1 as bw).2 ∧
        (∀ bb, MemoryModel.Disjoint (range bb 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem bb = load64Mem s.mem bb) := by
  intro as
  induction as with
  | nil =>
    intro s bw extra hbw hn _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodySub1 s
        (evalPExpr_loopCond_false s hn0)
    · simp [mpnSub1, memHoldsLimbs]
    · simpa [mpnSub1] using hbw
    · intro bb _; rfl
  | cons a as ih =>
    intro s bw extra hbw hn hap hdoa
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
    obtain ⟨s1, hs1, hs1_mem, hs1_bw, hs1_ap, hs1_op, hs1_n⟩ :=
      bignumExec_loopBodySub1_step s a bw hbw hap_head
    set op0 : UInt64 := regAddr s "op" with hop0
    have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
      simp only [regAddr, hs1_ap]; exact regAddr_advance _
    have hra_op : regAddr s1 "op" = op0 + 8 := by
      simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
    have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (sub1Step a bw).1.toNat) := by
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
    have hbw1 : s1.regs "bw" = (sub1Step a bw).2 := hs1_bw
    have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
      rw [hs1_n, hn]
      simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
    obtain ⟨s', hs', hs'_mem, hs'_bw, hs'_frame⟩ :=
      ih s1 (sub1Step a bw).2 extra hbw1 hn1 hap1 hdoa1
    refine ⟨s', ?_, ?_, ?_, ?_⟩
    · have hfuel : 2 * (a :: as).length + 3 + extra
          = (2 * as.length + 2 + extra) + 3 := by
        simp only [List.length_cons]; ring
      rw [hfuel]
      refine bignumExecFuel_loopSub1_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
        (evalPExpr_loopCond_true s hn_ne) hs1 ?_
      simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
              from by omega] using hs'
    · rw [hmem1] at hs'_frame
      have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
        range_op_head_tail_disjoint op0 as.length (by omega)
      refine ⟨?_, ?_⟩
      · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
        have hread := load64Mem_store64_same s.mem op0
          (UInt64.ofNat (sub1Step a bw).1.toNat)
        rw [hread]
        rfl
      · have hthis := hs'_mem
        rw [hra_op] at hthis
        exact hthis
    · rw [hs'_bw]; simp only [mpnSub1]
    · intro bb hbb
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

/-- **The `mpn_add_1` bridge, fully proved.**  `mpnAdd1Fd.body` (the emitted
    `cy := b; while (n != 0) { loopBodyAdd1 }`) refines the pure reference
    `mpnAdd1` over byte memory.  The seed `cy := b` makes the first iteration
    add the single limb; the loop is then `mpnAdd1_loop`. -/
theorem MpnAdd1JasminRefines : MpnAdd1RefinesStmt := by
  intro s as fuel hn hap hdoa hfuel
  -- The prelude `cy := b` copies register `b` into `cy`.
  set s0 : BignumState := setReg s "cy" (s.regs "b") with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := vr "b" }, gs := false }))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcy0 : s0.regs "cy" = s.regs "b" := by rw [hs0]; simp [setReg]
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
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cy, _⟩ :=
    mpnAdd1_loop as s0 (s.regs "b") extra hcy0 hn0' hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodyAdd1 s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAdd1] s0 := by
      conv_lhs => rw [bodyAdd1]
      simp only [bignumExecFuel, regMov, pv, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    exact hs'_mem
  · exact hs'_cy

/-- **The `mpn_sub_1` bridge, fully proved.**  `mpnSub1Fd.body` (the emitted
    `bw := b; while (n != 0) { loopBodySub1 }`) refines the pure reference
    `mpnSub1` over byte memory.  Mirror of `MpnAdd1JasminRefines`. -/
theorem MpnSub1JasminRefines : MpnSub1RefinesStmt := by
  intro s as fuel hn hap hdoa hfuel
  set s0 : BignumState := setReg s "bw" (s.regs "b") with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "bw" }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := vr "b" }, gs := false }))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hbw0 : s0.regs "bw" = s.regs "b" := by rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "bw" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "bw" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; exact hap
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; exact hdoa
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_bw, _⟩ :=
    mpnSub1_loop as s0 (s.regs "b") extra hbw0 hn0' hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodySub1 s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub1] s0 := by
      conv_lhs => rw [bodySub1]
      simp only [bignumExecFuel, regMov, pv, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    exact hs'_mem
  · exact hs'_bw

end CatCrypt.Crypto.Jasmin.Examples.MpnAdd1Prototype
