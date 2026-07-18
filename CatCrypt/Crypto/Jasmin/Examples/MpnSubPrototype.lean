/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

set_option autoImplicit false

/-!
# Phase 2 — verified variable-length `mpn_sub_n` by template reuse

**EXPERIMENTAL FILE.**  This is the Phase-2 companion to
`MpnAddPrototype.lean`.  It proves the GMP kernel `mpn_sub_n` (subtract two
equal-length limb arrays with borrow) end-to-end against the Jasmin `Cwhile`
semantics — *reusing the Phase-1 machinery verbatim*.

## What is reused (kernel-agnostic, imported from `MpnAddPrototype`)

The Phase-1 file proved a `Cwhile` loop-invariant rule over the byte-memory
model with pointer aliasing.  Every piece of that rule is independent of the
inner arithmetic and is imported directly:

* **Memory algebra** (`load64Mem_store64_same`, `load64Mem_store64_disjoint`,
  `loadByte_store64`, `loadByte_store64_frame`) — read-back + disjoint frame.
* **The `Cwhile` fuel rule** (`bignumExecFuel_loop_step`,
  `bignumExecFuel_loop_exit`) — one iteration / loop exit.
* **The guard evaluation** (`evalPExpr_loopCond_true`/`_false`).
* **The memory-frame plumbing** (`memHoldsLimbs`, `memHoldsLimbs_store64_frame`,
  `range_shift_subset`, `range_head_subset`, `disjoint_mono`,
  `range_op_head_tail_disjoint`, `disjoint_range_lt`).
* **The counter algebra** (`ofNat64_toNat`, `ofNat64_succ_ne_zero`,
  `ofNat64_succ_sub_one`, `regAddr`, `regAddr_advance`, `bv_uint_roundtrip`,
  `resolveAddr_reg`, the `setReg`/`storeMem` projection simp lemmas).
* **The induction skeleton** (`mpnAddN_loop` → `MpnAddNJasminRefines`) — copied
  structurally; only the per-limb step lemma changes.

## What is genuinely new (the kernel-specific arithmetic)

Only §2–§3 (the pure reference + leaf identity), §6 (the `subBorrowIn` bridge),
and §7 (the one-iteration state update) are re-derived.  The bridge to `mpnSubN`
(§10) is the *same* induction as `mpnAddN_loop` with `adcStep`/`addCarryIn`
swapped for `sbbStep`/`subBorrowIn`.

## Functional spec

`mpnSubN a b bin = (result, borrow-out)` satisfies the multi-precision
subtraction identity (stated all-additions to stay Nat-safe):

```
toNat result + toNat b + (borrow-in)
  = toNat a + (2^64)^|a| · (borrow-out)
```

i.e. `result = a - b - bin` with the final borrow at bit `64·|a|`.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnSubPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

/-! ## §1  The Jasmin `mpn_sub_n` body — runtime `Cwhile` loop

Identical to the `mpn_add_n` body except the inner intrinsic is `#SBB_64`
(subtract-with-borrow) instead of `#ADC_64`.  `#SBB_64` shares the exact same
6-LVal output bundle shape `[of, cf, sf, pf, zf, dst]` as `#ADC_64`, so the
emitter/interpreter plumbing (`writeSubBundle`, the flag-bundle padding) is
reused unchanged; the borrow register `cf` threads exactly like the carry.

The small instruction-builder helpers (`vr`, `pv`, `loadAt0`, `storeAt0`,
`binImm`, the flag-bundle padding) are `private` in `MpnAddPrototype`, so we
re-declare definitionally-identical local copies here.  They are deliberately
the same shape so the emitter/interpreter behave identically. -/

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

/-- `_, cf, _, _, _, r = #SBB_64(a, b, bin);` — the borrow register `bin`
    is also the borrow-out register `cf`, threading the borrow across loop
    iterations.  Same 6-LVal bundle as `#ADC_64`. -/
def sbbCopn (cfName rName aName bName binName : String) : InstrR :=
  .Copn (flag_pre ++ [.Lvar { var := vr cfName }] ++ flag_post
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"SBB_64"⟩)
        [pv aName, pv bName, pv binName]

/-- One loop iteration body for `mpn_sub_n`:
    ```
    t = [:u64 ap + 0];
    s = [:u64 bp + 0];
    _, cf, _, _, _, r = #SBB_64(t, s, cf);
    [:u64 op + 0] = r;
    ap += 8; bp += 8; op += 8;
    n  -= 1;
    ```
    `cf` is initialised to 0 before the loop (first iteration is a plain
    subtract) and read-modify-written each iteration. -/
def loopBodySub : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , sbbCopn "cf" "r" "t" "s" "cf"
  , storeAt0 "op" "r"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_sub_n`:
    ```
    cf = 0;
    while (n != 0) { <loopBodySub> }
    ```
    `cf` holds the final borrow (the GMP `mpn_sub_n` ABI returns it). -/
def bodySub : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub ]

/-- `mpn_sub_n(op, ap, bp, n)` as a Jasmin `FunDecl`.  Void return (output
    via `op`); SysV ABI `rdi=op, rsi=ap, rdx=bp, rcx=n`. -/
def mpnSubNFd : FunDecl where
  name := { name := "mpn_sub_n" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := bodySub
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the public
    length `n`, never a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodySub = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnSubNFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional reference + the one-limb SBB step -/

/-- Boolean borrow as a Nat (0 or 1). -/
def borrowNat (c : Bool) : Nat := if c then 1 else 0

/-- One SBB step on `BitVec 64`: returns `(diff, borrow-out)`.
    `diff = (a - b - bin) mod 2^64`, `borrow-out = (a < b + bin)`. -/
def sbbStep (a b : BitVec 64) (bin : Bool) : BitVec 64 × Bool :=
  let d : Nat := b.toNat + (if bin then 1 else 0)
  (BitVec.ofNat 64 ((a.toNat + 2 ^ 64 - d) % 2 ^ 64), decide (a.toNat < d))

/-- Pure reference for `mpn_sub_n`: subtract two limb lists with a borrow
    chain, recursing in lockstep.  Returns `(result limbs, final borrow-out)`.
    This is exactly the borrow chain the emitted `while (n != 0)` loop walks. -/
def mpnSubN : List (BitVec 64) → List (BitVec 64) → Bool →
    (List (BitVec 64) × Bool)
  | a :: as, b :: bs, bin =>
      let (r, bout) := sbbStep a b bin
      let (rs, fbout) := mpnSubN as bs bout
      (r :: rs, fbout)
  | _, _, bin => ([], bin)

/-! ## §3  Functional spec: the borrow-chain invariant

The load-bearing theorem.  Like the addition case, this needs an inductive
invariant — `bv_decide` cannot close an unbounded loop.  The invariant is the
per-limb borrow-chain identity, stated all-additions to remain Nat-safe. -/

/-- The single-step SBB identity, on `Nat`:
    `sbbStep a b bin` produces `(diff, bout)` with
    `diff + b.toNat + bin = a.toNat + 2^64 · bout`. -/
theorem sbbStep_spec (a b : BitVec 64) (bin : Bool) :
    (sbbStep a b bin).1.toNat + b.toNat + borrowNat bin
      = a.toNat + 2 ^ 64 * borrowNat (sbbStep a b bin).2 := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  have hc1 : (if bin then 1 else 0) ≤ 1 := by cases bin <;> simp
  unfold sbbStep borrowNat
  simp only [BitVec.toNat_ofNat, Nat.mod_mod, decide_eq_true_eq]
  by_cases hlt : a.toNat < b.toNat + (if bin then 1 else 0)
  · have hmod : (a.toNat + 2 ^ 64 - (b.toNat + (if bin then 1 else 0))) % 2 ^ 64
        = a.toNat + 2 ^ 64 - (b.toNat + (if bin then 1 else 0)) := by
      apply Nat.mod_eq_of_lt; omega
    rw [if_pos hlt, hmod]; omega
  · have hmod : (a.toNat + 2 ^ 64 - (b.toNat + (if bin then 1 else 0))) % 2 ^ 64
        = a.toNat - (b.toNat + (if bin then 1 else 0)) := by
      have he : a.toNat + 2 ^ 64 - (b.toNat + (if bin then 1 else 0))
          = (a.toNat - (b.toNat + (if bin then 1 else 0))) + 2 ^ 64 := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [if_neg hlt, hmod]; omega

/-- **Main functional spec — proved by induction on the limb list.**

    For equal-length limb lists `a, b` and any borrow-in `bin`, the pure
    reference `mpnSubN` satisfies the multi-precision subtraction identity:
    the denotation of the output limbs, plus `toNat b` and the borrow-in,
    equals `toNat a` plus the final borrow-out shifted to bit `64·|a|`.

    This is the inductive invariant the emitted `while (n != 0)` loop
    maintains: each iteration peels one limb (`sbbStep_spec`), and the IH
    carries the identity over the `2^64`-scaled tail. -/
theorem mpnSubN_spec :
    ∀ (a b : List (BitVec 64)), a.length = b.length → ∀ (bin : Bool),
      toNat (mpnSubN a b bin).1 + toNat b + borrowNat bin
        = toNat a + (2 ^ 64) ^ a.length * borrowNat (mpnSubN a b bin).2 := by
  intro a
  induction a with
  | nil =>
    intro b hlen bin
    cases b with
    | nil => simp [mpnSubN, toNat, borrowNat]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen bin
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      set p := sbbStep a b bin with hp
      have hstep := sbbStep_spec a b bin
      rw [← hp] at hstep
      set q := mpnSubN as bs p.2 with hq
      have htail := ih bs hlen' p.2
      rw [← hq] at htail
      have hunfold : mpnSubN (a :: as) (b :: bs) bin = (p.1 :: q.1, q.2) := by
        simp only [mpnSubN, hp, hq]
      rw [hunfold]
      simp only [toNat, List.length_cons]
      have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      -- IH (scaled by 2^64) + head step (sbbStep_spec) close the linear goal.
      -- `hkey` is `htail` multiplied through by 2^64, with both sides shaped to
      -- match the goal's monomials so omega only sees linear combinations.
      have hkey : 2 ^ 64 * toNat q.1 + 2 ^ 64 * toNat bs + 2 ^ 64 * borrowNat p.2
          = 2 ^ 64 * toNat as + 2 ^ 64 * ((2 ^ 64) ^ as.length * borrowNat q.2) := by
        have := congrArg (2 ^ 64 * ·) htail
        simpa [Nat.mul_add, Nat.add_assoc] using this
      have hmono : 2 ^ 64 * (2 ^ 64) ^ as.length * borrowNat q.2
          = 2 ^ 64 * ((2 ^ 64) ^ as.length * borrowNat q.2) := by ring
      rw [hmono]
      omega

/-- The usual entry point: borrow-in 0.  `mpn_sub_n` with no incoming borrow
    subtracts two equal-length bignums; the result plus `toNat b` equals
    `toNat a` plus the borrow-out at bit `64·|a|` (the GMP `mpn_sub_n`
    contract — the return value is the borrow-out). -/
theorem mpnSubN_spec_borrowIn_false (a b : List (BitVec 64))
    (hlen : a.length = b.length) :
    toNat (mpnSubN a b false).1 + toNat b
      = toNat a + (2 ^ 64) ^ a.length * borrowNat (mpnSubN a b false).2 := by
  have h := mpnSubN_spec a b hlen false
  simpa [borrowNat] using h

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `[0] - [1]` underflows: result `0xFFFF…FFFF`, borrow-out `true`. -/
example : mpnSubN [0] [1] false = ([-1], true) := by native_decide

/-- `[12,0] - [7,0]` (two-limb) = `[5,0]`, no borrow. -/
example : mpnSubN [12, 0] [7, 0] false = ([5, 0], false) := by native_decide

/-- Borrow propagation across two limbs: `[0, 1] - [1, 0] = [0xFFFF…, 0]`. -/
example : mpnSubN [(0 : BitVec 64), 1] [1, 0] false = ([-1, 0], false) := by
  native_decide

/-! ## §6  SBB bridge: executable `subBorrowIn` matches pure `sbbStep`

The emitted `#SBB_64` runs `BignumExec.subBorrowIn` (BitVec borrow logic);
the pure reference uses `sbbStep` (Nat borrow logic).  These lemmas show they
agree once the borrow-in register encodes `borrowNat bin` as a `BitVec 64`. -/

/-- SBB diff bridge: the result word of `subBorrowIn` (borrow-in encoded as a
    `BitVec`) is the wrapped Nat difference that `sbbStep` produces. -/
theorem subBorrowIn_diff (a b : BitVec 64) (c : Bool) :
    (subBorrowIn a b (BitVec.ofNat 64 (if c then 1 else 0))).2
      = (sbbStep a b c).1 := by
  have ha := a.isLt; have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  unfold subBorrowIn sbbStep
  cases c <;>
  · simp only [Bool.false_eq_true, reduceIte, ↓reduceIte,
      show ((BitVec.ofNat 64 0 &&& 1) : BitVec 64) = 0 from by decide,
      show ((BitVec.ofNat 64 1 &&& 1) : BitVec 64) = 1 from by decide,
      BitVec.toNat_sub, BitVec.toNat_ofNat,
      show ((0 : BitVec 64).toNat) = 0 from rfl,
      show ((1 : BitVec 64).toNat) = 1 from rfl]
    rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; omega

/-- The borrow-out of `subBorrowIn` is a single bit (`0` or `1`).  Needed so
    that the `BitVec`-encoded borrow round-trips through `toNat`. -/
theorem subBorrowIn_borrow_toNat_le (a b : BitVec 64) (c01 : Nat) :
    (subBorrowIn a b (BitVec.ofNat 64 c01)).1.toNat ≤ 1 := by
  unfold subBorrowIn
  simp only [BitVec.toNat_or, BitVec.ult, decide_eq_true_eq]
  split_ifs <;> simp_all

/-- SBB `toNat` identity for `subBorrowIn`: the result word plus `b` plus the
    borrow-in equals `a` plus the borrow-out shifted to bit 64 (borrow-in
    given as a one-bit Nat).  The executable analogue of `sbbStep_spec`. -/
theorem subBorrowIn_spec (a b : BitVec 64) (c01 : Nat) (hc : c01 ≤ 1) :
    (subBorrowIn a b (BitVec.ofNat 64 c01)).2.toNat + b.toNat + c01
      = a.toNat + 2 ^ 64 * (subBorrowIn a b (BitVec.ofNat 64 c01)).1.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc' : c01 < 2 ^ 64 := by omega
  unfold subBorrowIn
  have hand : c01 &&& 1 = c01 := by
    rcases (by omega : c01 = 0 ∨ c01 = 1) with h | h <;> simp [h]
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.ult, decide_eq_true_eq, Nat.mod_eq_of_lt hc',
    show ((1 : BitVec 64).toNat) = 1 from rfl, hand]
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  split_ifs <;>
    simp only [show ((1 : BitVec 64).toNat ||| (0 : BitVec 64).toNat) = 1 from by decide,
      show ((0 : BitVec 64).toNat ||| (1 : BitVec 64).toNat) = 1 from by decide,
      show ((0 : BitVec 64).toNat ||| (0 : BitVec 64).toNat) = 0 from by decide,
      show ((1 : BitVec 64).toNat ||| (1 : BitVec 64).toNat) = 1 from by decide] <;>
    omega

/-- SBB borrow bridge: the borrow-out flag of `subBorrowIn` equals the
    `BitVec`-encoded `borrowNat` of `sbbStep`'s borrow-out.  Derived by
    cancelling the matching results (`subBorrowIn_diff`) in the two `toNat`
    identities (`subBorrowIn_spec`, `sbbStep_spec`). -/
theorem subBorrowIn_borrow (a b : BitVec 64) (c : Bool) :
    (subBorrowIn a b (BitVec.ofNat 64 (if c then 1 else 0))).1
      = BitVec.ofNat 64 (borrowNat (sbbStep a b c).2) := by
  set c01 : Nat := if c then 1 else 0 with hc01
  have hc : c01 ≤ 1 := by rw [hc01]; cases c <;> simp
  apply BitVec.eq_of_toNat_eq
  have hspec := subBorrowIn_spec a b c01 hc
  have hstep := sbbStep_spec a b c
  have hdiff : (subBorrowIn a b (BitVec.ofNat 64 c01)).2.toNat = (sbbStep a b c).1.toNat := by
    rw [subBorrowIn_diff]
  have hble := subBorrowIn_borrow_toNat_le a b c01
  have hborrowNat_le : borrowNat (sbbStep a b c).2 ≤ 1 := by
    unfold borrowNat; cases (sbbStep a b c).2 <;> simp
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold borrowNat at hstep ⊢
  omega

/-! ## §7  One loop iteration as an explicit state update

`loopBodySub` is straight-line, so it runs via `bignumExec`.  This lemma is
the SBB analogue of `bignumExec_loopBody_step`: it computes the exact effect
of one `loopBodySub` pass.  The proof is the *same* unfold-then-read-off
script as the add case, with `addCarryIn_sum`/`addCarryIn_carry` replaced by
`subBorrowIn_diff`/`subBorrowIn_borrow`.  `regAddr` (string-keyed) is imported;
the local `resolveAddr_reg` mirrors the private add-case helper for our local
`vr`. -/

/-- `resolveAddr` of a register at offset 0 yields its `UInt64` address. -/
theorem resolveAddr_reg (s : BignumState) (x : String) :
    resolveAddr s { var := vr x } (.Pconst 0) = some (regAddr s x) := by
  simp only [resolveAddr, regAddr, vr]
  norm_num

theorem bignumExec_loopBodySub_step (s : BignumState) (a b : BitVec 64) (bin : Bool)
    (hcf : s.regs "cf" = BitVec.ofNat 64 (if bin then 1 else 0))
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBodySub s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (sbbStep a b bin).1.toNat) ∧
      s'.regs "cf" = BitVec.ofNat 64 (borrowNat (sbbStep a b bin).2) ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  simp only [loopBodySub, loadAt0, sbbCopn, storeAt0, binImm, flag_pre, flag_post,
             bignumExec, execInstr, evalPExpr, pv, resolveAddr_reg, vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, hb, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  rw [show (setReg s "t" a).regs "bp" + 0 = s.regs "bp" from by
        simp only [setReg_regs]; bv_decide, setReg_mem, hb]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte,
               hcf, subBorrowIn_diff, subBorrowIn_borrow,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-- `loopBodySub` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodySub_straightLine : InstrR.bodyIsStraightLine loopBodySub := by
  simp only [loopBodySub, loadAt0, sbbCopn, storeAt0, binImm, InstrR.bodyIsStraightLine,
             InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodySub` is non-control. -/
theorem loopBodySub_nonControl : ∀ i ∈ loopBodySub, i.isNonControl := by
  intro i hi
  simp only [loopBodySub, loadAt0, sbbCopn, storeAt0, binImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §8  One `Cwhile` iteration over `bignumExecFuel`

The imported `bignumExecFuel_loop_step` is hardcoded to `loopBody`, so we
re-instantiate the *same* proof for `loopBodySub` (using the SBB body's
straight-line / non-control facts).  `bignumExecFuel_loop_exit` is already
generic over the body, so it is reused directly. -/

/-- **Forward one-iteration rule** for `loopBodySub` — same proof shape as the
    imported `bignumExecFuel_loop_step`, specialised to the SBB body. -/
theorem bignumExecFuel_loopSub_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodySub s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodySub] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodySub] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodySub s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodySub s loopBodySub_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodySub [.Cwhile [] cond loopBodySub]
        loopBodySub_nonControl s s_mid s' hsl hrec]

/-! ## §9  Loop-guard evaluation, machine-checked

The imported guard lemmas mention the add-case `private pv`; we re-state them
for our local `pv` (the proof is the same `evalPExpr`-unfold). -/

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

/-! ## §10  Assembly: `MpnSubNJasminRefines`

The full bridge.  Structurally *identical* to `mpnAddN_loop` →
`MpnAddNJasminRefines`: induction on the limb list, each step peeling one limb
via `bignumExec_loopBodySub_step` and `bignumExecFuel_loop_step`, preserving the
unread `ap`/`bp` suffixes across the `op[i]` store with
`load64Mem_store64_disjoint`, threading the borrow via `sbbStep`.  Every
control-flow / memory-frame lemma is imported from `MpnAddPrototype`. -/

/-- The bridge statement (mirror of `MpnAddNRefinesStmt`). -/
def MpnSubNRefinesStmt : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat),
    as.length = bs.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodySub s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnSubN as bs false).1 ∧
      s'.regs "cf" = BitVec.ofNat 64 (borrowNat (mpnSubN as bs false).2)

/-- **The loop, by induction on the limb list.**  Mirror of `mpnAddN_loop`. -/
theorem mpnSubN_loop :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (bin : Bool) (extra : Nat),
      as.length = bs.length →
      s.regs "cf" = BitVec.ofNat 64 (if bin then 1 else 0) →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      memHoldsLimbs s.mem (regAddr s "bp") bs →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "bp") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnSubN as bs bin).1 ∧
        s'.regs "cf" = BitVec.ofNat 64 (borrowNat (mpnSubN as bs bin).2) ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s bin extra _ hcf hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodySub s
        (evalPExpr_loopCond_false s hn0)
    · simp [mpnSubN, memHoldsLimbs]
    · simpa [mpnSubN, borrowNat] using hcf
    · intro b _; rfl
  | cons a as ih =>
    intro bs s bin extra hlen hcf hn hap hbp hdoa hdob
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
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
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      obtain ⟨s1, hs1, hs1_mem, hs1_cf, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_loopBodySub_step s a b bin hcf hap_head hbp_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 8 := by
        simp only [regAddr, hs1_bp]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (sbbStep a b bin).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob_store_bptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "bp" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
          hdoa_store_aptail hap_tail
      have hbp1 : memHoldsLimbs s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "bp" + 8) op0 _ bs
          (by rw [hlen'] at hdob_store_bptail; exact hdob_store_bptail) hbp_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "ap") (8 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "bp") (8 * as.length)) := by
        rw [hra_op, hra_bp]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      have hcf1 : s1.regs "cf" = BitVec.ofNat 64 (if (sbbStep a b bin).2 then 1 else 0) := by
        rw [hs1_cf]; simp [borrowNat]
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_cf, hs'_frame⟩ :=
        ih bs s1 (sbbStep a b bin).2 extra hlen' hcf1 hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loopSub_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
          (evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · rw [hmem1] at hs'_frame
        have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
          range_op_head_tail_disjoint op0 as.length (by omega)
        refine ⟨?_, ?_⟩
        · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          have hread := load64Mem_store64_same s.mem op0 (UInt64.ofNat (sbbStep a b bin).1.toNat)
          rw [hread]
          rfl
        · have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · rw [hs'_cf]; simp only [mpnSubN]
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

/-- **The bridge, fully proved.**  `mpnSubNFd.body` (the emitted
    `cf := 0; while (n != 0) { loopBodySub }`) refines the pure reference
    `mpnSubN` over byte memory.  Mirror of `MpnAddNJasminRefines`. -/
theorem MpnSubNJasminRefines : MpnSubNRefinesStmt := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  set s0 : BignumState := setReg s "cf" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcf0 : s0.regs "cf" = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "cf" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cf" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; exact hap
  have hbp0 : memHoldsLimbs s0.mem (regAddr s0 "bp") bs := by
    rw [hmem0, hra0 "bp" (by decide)]; exact hbp
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; exact hdoa
  have hdob0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "bp") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "bp" (by decide)]; exact hdob
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cf, _⟩ :=
    mpnSubN_loop as bs s0 false extra hlen hcf0 hn0' hap0 hbp0 hdoa0 hdob0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodySub s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub] s0 := by
      conv_lhs => rw [bodySub]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    exact hs'_mem
  · exact hs'_cf

end CatCrypt.Crypto.Jasmin.Examples.MpnSubPrototype
