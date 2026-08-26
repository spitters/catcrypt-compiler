/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.SubPrototype
import CatCrypt.Crypto.Jasmin.Mpn.AddOpenCarryPrototype

set_option autoImplicit false

/-!
# Open-coded-borrow variant of the verified `mpn_sub_n` loop

**EXPERIMENTAL FILE.**  Companion to `Mpn.SubPrototype.lean` (the `#SBB_64`
variant) and exact mirror of `Mpn.AddOpenCarryPrototype.lean` (the open-coded
`add`).  Same verified `mpn_sub_n` (subtract two equal-length limb arrays with
borrow), but the loop body threads the borrow as an **ordinary `u64` GPR value**
using an *open-coded subtract-with-borrow* (two-subtract idiom) instead of
`#SBB_64`'s physical CF flag.

## Why this variant exists (the backend gap it closes)

The committed `Mpn.SubPrototype.loopBodySub` runs the borrow through
`#SBB_64(t, s, cf)`, which both reads and writes the architectural carry flag
`cf` *across the `while (n != 0)` back-edge*.  This is the same problem the
`#ADC_64` add body had: `jasminc`'s register allocator rejects a physical CF
flag kept live across a loop back-edge, and the emitter reclassifies `cf` into
the bool-flag bank, so the `cf := 0` init becomes an `int → bool` clash.  The
add side resolved it with the committed open-coded variant
(`MpnAddOpenCarryPrototype`); this file does the identical thing for subtract.

**This file's variant has no such problem.**  The loop body is

```
d0 = t - s          -- #SUB_64 → (bw1, d0):  subBorrow t s
r  = d0 - bin       -- #SUB_64 → (bw2, r) :  subBorrow d0 bin  (bin = GPR borrow-in)
bw = bw1 ||| bw2    -- Olor: the new borrow (a u64 ∈ {0,1})
```

The threaded borrow `bw` is a `u64` value, not a flag, so it crosses the
back-edge in a general-purpose register — exactly what the register allocator
wants.  The two `#SUB_64` borrow-out flags `bw1`, `bw2` are dead within the body
(materialized to GPRs before the next flag is born), so no physical flag is live
across the back-edge.

## Reuse from `MpnSubPrototype` and `MpnAddOpenCarryPrototype`

The open-coded body computes *exactly* `BignumExec.subBorrowIn t s bw` — the
existing executable SBB, whose definition is itself the two-subtract idiom
(`s1 = a-b; bf1 = a <u b; r = s1-bin01; bf2 = s1 <u bin01; (bf1|||bf2, r)`).  So
the genuinely new proof (`openBodySub_eq_subBorrowIn`, the SBB analogue of the
add file's `openBody_eq_addCarryIn`) is just that the two `#SUB_64`s plus the
`Olor` reconstruct `subBorrowIn`, after which the borrow-chain math (`sbbStep`,
`subBorrowIn`, `mpnSubN_spec`) and *all* the general loop / memory lemmas are
inherited verbatim — the borrow→`sbbStep` bridges (`subBorrowIn_diff`,
`subBorrowIn_borrow`) from `MpnSubPrototype`, the carry-chain induction skeleton
from `mpnSubN_loop`, and the `Cwhile`-fuel / byte-memory plumbing from
`MpnAddPrototype`.  The induction structure of §4 is a clone of
`Mpn.AddOpenCarryPrototype.mpnAddN_openLoop` with `sbbStep`/`subBorrowIn` in place
of `adcStep`/`addCarryIn`.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.SubOpenCarryPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.SubPrototype

/-! ## §1  The open-coded Jasmin `mpn_sub_n` body

Reuse the `MpnSubPrototype` instruction-builder helpers (`vr`, `pv`, `loadAt0`,
`storeAt0`, `binImm`) verbatim — only the `#SUB_64` bundle and the loop body are
new.  The `#SUB_64` flag bundle has the same 6-LVal shape as `#ADD_64`
(`[_, cf, _, _, _, dst]`), so `writeSubBundle` is reused unchanged. -/

/-- The 6-LVal `#SUB_64` flag bundle `[_, bw_out, _, _, _, dst]` capturing the
    borrow-out into register `bwName` and the difference into `rName`.  Same
    bundle shape as `Mpn.AddOpenCarryPrototype.addCopn`, just the `SUB_64`
    opcode (2 operands), which the interpreter runs as `subBorrow`. -/
def subCopn (bwName rName aName bName : String) : InstrR :=
  .Copn ([.Lnone {} (.sword .U64), .Lvar { var := vr bwName }]
          ++ List.replicate 3 (.Lnone {} (.sword .U64))
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"SUB_64"⟩)
        [pv aName, pv bName]

/-- One open-coded loop iteration:
    ```
    t  = [:u64 ap + 0];
    s  = [:u64 bp + 0];
    _, bw1, _, _, _, d0 = #SUB_64(t, s);     // subBorrow t s
    _, bw2, _, _, _, r  = #SUB_64(d0, bw);   // subBorrow d0 bw (bw = GPR borrow-in)
    bw = bw1 | bw2;                          // Olor: new GPR borrow ∈ {0,1}
    [:u64 op + 0] = r;
    ap += 8; bp += 8; op += 8; n -= 1;
    ```
    `bw` is a plain `u64` register, threaded across iterations.  No `#SBB_64`,
    no physical flag across the back-edge. -/
def loopBody : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , subCopn "bw1" "d0" "t" "s"
  , subCopn "bw2" "r" "d0" "bw"
  , .Cassgn (.Lvar { var := vr "bw" }) .AT_none (.sword .U64)
      (.Papp2 (.Olor .U64) (pv "bw1") (pv "bw2"))
  , storeAt0 "op" "r"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body: `bw = 0; while (n != 0) { <loopBody> }`.  `bw` holds the final
    borrow (the GMP `mpn_sub_n` ABI returns it). -/
def body : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "bw" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody ]

/-- `mpn_sub_n(op, ap, bp, n)` as a `FunDecl`, open-coded borrow. -/
def mpnSubNFd : FunDecl where
  name := { name := "mpn_sub_n_oc" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := body
  results := []

/-- The loop is constant-time-shaped: the guard depends only on the public
    length `n`. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd body = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnSubNFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  The one genuinely new fact: open-coded body = `subBorrowIn`

The two `#SUB_64`s plus the `Olor` reconstruct `BignumExec.subBorrowIn`, whose
definition *is* the two-subtract idiom.  Everything else is inherited.  This is
the SBB mirror of `Mpn.AddOpenCarryPrototype.openBody_eq_addCarryIn`. -/

/-- `subBorrow a b = (bf, r)` where `bf = if a.ult b then 1 else 0` and
    `r = a - b`.  Definitional unfold. -/
theorem subBorrow_eq (a b : BitVec 64) :
    subBorrow a b = ((if a.ult b then 1 else 0), a - b) := rfl

/-- **Open-coded composition = `subBorrowIn`.**  Composing `subBorrow t s`
    (giving `(bw1, d0)`) with `subBorrow d0 bw` (giving `(bw2, r)`) and taking
    the new borrow as `bw1 ||| bw2` yields exactly `subBorrowIn t s bw` —
    *provided the borrow-in `bw` is already reduced to its low bit*
    (`bw &&& 1 = bw`), which the threaded GPR borrow always is (it is `0` or
    `1`).  Pure `BitVec`, closed by `bv_decide`.

    Concretely: `(borrow-out, diff) = (bw1 ||| bw2, r)` with `r = (t - s) - bw`
    and the two borrow flags from the two subtracts.  `subBorrowIn` masks its
    borrow-in (`bw &&& 1`); the open-coded body uses `bw` raw, so the two agree
    exactly when `bw` is already a low bit.  Without the hypothesis the claim is
    false for `bw ≥ 2` — the hypothesis is the loop invariant that the borrow
    stays a single bit.  SBB mirror of `openBody_eq_addCarryIn`. -/
theorem openBodySub_eq_subBorrowIn (t s bw : BitVec 64) (hbw : bw &&& 1 = bw) :
    ((subBorrow t s).1 ||| (subBorrow (subBorrow t s).2 bw).1,
      (subBorrow (subBorrow t s).2 bw).2)
      = subBorrowIn t s bw := by
  unfold subBorrow subBorrowIn
  refine Prod.ext ?_ ?_ <;> bv_decide

/-- The open-coded body, evaluated on a borrow-in encoded as a single bit,
    produces `sbbStep`'s difference word.  Bridges the two `#SUB_64`s + `Olor`
    (`openBodySub_eq_subBorrowIn`) to the borrow-chain reference via the existing
    `subBorrowIn_diff`.  SBB mirror of `openBody_sum`. -/
theorem openBodySub_diff (t s : BitVec 64) (bin : Bool) :
    (subBorrow (subBorrow t s).2 (BitVec.ofNat 64 (if bin then 1 else 0))).2
      = (sbbStep t s bin).1 := by
  have hmask : (BitVec.ofNat 64 (if bin then 1 else 0)) &&& 1
      = BitVec.ofNat 64 (if bin then 1 else 0) := by cases bin <;> bv_decide
  have h := openBodySub_eq_subBorrowIn t s (BitVec.ofNat 64 (if bin then 1 else 0)) hmask
  have h2 := congrArg Prod.snd h
  simp only at h2
  rw [h2]; exact subBorrowIn_diff t s bin

/-- The open-coded body's `bw1 ||| bw2` borrow-out, on a borrow-in encoded as a
    single bit, equals the `BitVec`-encoded `borrowNat` of `sbbStep`'s
    borrow-out.  Bridges via `openBodySub_eq_subBorrowIn` + `subBorrowIn_borrow`.
    SBB mirror of `openBody_carry`. -/
theorem openBodySub_borrow (t s : BitVec 64) (bin : Bool) :
    ((subBorrow t s).1 ||| (subBorrow (subBorrow t s).2
        (BitVec.ofNat 64 (if bin then 1 else 0))).1)
      = BitVec.ofNat 64 (borrowNat (sbbStep t s bin).2) := by
  have hmask : (BitVec.ofNat 64 (if bin then 1 else 0)) &&& 1
      = BitVec.ofNat 64 (if bin then 1 else 0) := by cases bin <;> bv_decide
  have h := openBodySub_eq_subBorrowIn t s (BitVec.ofNat 64 (if bin then 1 else 0)) hmask
  have h1 := congrArg Prod.fst h
  simp only at h1
  rw [h1]; exact subBorrowIn_borrow t s bin

/-! ## §3  One open-coded iteration as an explicit state update

Mirror of `Mpn.SubPrototype.bignumExec_loopBodySub_step` and of
`Mpn.AddOpenCarryPrototype.bignumExec_openLoopBody_step`, for the open-coded
sub body: load `a`, `b`; two `#SUB_64`s + `Olor`; store the difference at `op`;
advance the three pointers by 8 and decrement `n`.  The borrow register holds
`borrowNat` of `sbbStep`'s borrow-out — identical observable effect to the
`#SBB_64` body, by `openBodySub_diff` / `openBodySub_borrow`. -/

-- The symbolic-execution simp sets below are deliberately robust (they mirror
-- `Mpn.SubPrototype.bignumExec_loopBodySub_step` and the add open-coded step);
-- the `unusedSimpArgs` linter flags entries that happen not to fire on this
-- body, but keeping them makes the proof resilient to evaluation-order changes.
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_openLoopBodySub_step (s : BignumState) (a b : BitVec 64) (bin : Bool)
    (hbw : s.regs "bw" = BitVec.ofNat 64 (if bin then 1 else 0))
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBody s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (sbbStep a b bin).1.toNat) ∧
      s'.regs "bw" = BitVec.ofNat 64 (borrowNat (sbbStep a b bin).2) ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Unfold the body into nested `execInstr` matches, resolving the two loads,
  -- the two `#SUB_64` bundles, the `Olor`, the store, and the four advances.
  simp only [loopBody, loadAt0, subCopn, storeAt0, binImm,
             bignumExec, execInstr, evalPExpr, pv, Mpn.SubPrototype.resolveAddr_reg, vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, hb, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  -- Fire the two loads (decode `a`/`b`).
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  rw [show (setReg s "t" a).regs "bp" + 0 = s.regs "bp" from by
        simp only [setReg_regs]; bv_decide, setReg_mem, hb]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- The witness state is concrete; read off borrow (open-coded bridges), store,
  -- and the four register advances.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Reduce all the `setReg … .regs "X"` lookups (and `.mem` projections) on the
  -- concrete witness state.  The two loaded words `t`,`s` resolve to `a`,`b`;
  -- the threaded borrow register `bw` resolves (via `hbw`) to the encoded borrow
  -- bit.  `+ 0` on the store address vanishes.
  all_goals
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte, hbw,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]
  · -- memory: stored value `(subBorrow (subBorrow a b).2 bw).2` = `sbbStep` diff.
    rw [openBodySub_diff a b bin]
  · -- borrow register: `(subBorrow a b).1 ||| (subBorrow (subBorrow a b).2 bw).1`
    -- = `ofNat (borrowNat (sbbStep a b bin).2)`.
    rw [openBodySub_borrow a b bin]

/-- The open-coded `loopBody` is straight-line (`Cassgn`/`Copn` only). -/
theorem loopBody_straightLine : InstrR.bodyIsStraightLine loopBody := by
  simp only [loopBody, loadAt0, subCopn, storeAt0, binImm, InstrR.bodyIsStraightLine,
             InstrR.isStraightLine, and_self]

/-- Every instruction of the open-coded `loopBody` is non-control. -/
theorem loopBody_nonControl : ∀ i ∈ loopBody, i.isNonControl := by
  intro i hi
  simp only [loopBody, loadAt0, subCopn, storeAt0, binImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- **Forward one-iteration rule for the open-coded sub loop.**  Clone of
    `Mpn.AddOpenCarryPrototype.bignumExecFuel_openLoop_step` (and of
    `Mpn.SubPrototype.bignumExecFuel_loopSub_step`), retargeted at *this* file's
    open-coded `loopBody` via the local `loopBody_straightLine` /
    `loopBody_nonControl`.  The general fuel lemmas
    (`bignumExecFuel_eq_bignumExec_of_straightLine`, `bignumExecFuel_append_join`)
    are reused verbatim. -/
theorem bignumExecFuel_openLoopSub_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBody s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBody] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBody] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBody s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBody s loopBody_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBody [.Cwhile [] cond loopBody]
        loopBody_nonControl s s_mid s' hsl hrec]

/-! ## §4  The open-coded sub loop, by induction on the limb list

A clone of `Mpn.SubPrototype.mpnSubN_loop` (equivalently
`Mpn.AddOpenCarryPrototype.mpnAddN_openLoop`) with
`bignumExec_openLoopBodySub_step` in place of `bignumExec_loopBodySub_step`.
Each iteration peels one limb; the borrow threads through the GPR `bw`; the
per-iteration store is framed against the unread `ap`/`bp` suffixes
(`load64Mem_store64_disjoint`).  Every supporting lemma is reused verbatim from
`MpnAddPrototype` / `MpnSubPrototype` — only the one-iteration effect differs,
and it has the identical observable shape. -/

theorem mpnSubN_openLoop :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (bin : Bool) (extra : Nat),
      as.length = bs.length →
      s.regs "bw" = BitVec.ofNat 64 (if bin then 1 else 0) →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      memHoldsLimbs s.mem (regAddr s "bp") bs →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "bp") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnSubN as bs bin).1 ∧
        s'.regs "bw" = BitVec.ofNat 64 (borrowNat (mpnSubN as bs bin).2) ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s bin extra _ hbw hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBody s
        (Mpn.SubPrototype.evalPExpr_loopCond_false s hn0)
    · simp [mpnSubN, memHoldsLimbs]
    · simpa [mpnSubN, borrowNat] using hbw
    · intro b _; rfl
  | cons a as ih =>
    intro bs s bin extra hlen hbw hn hap hbp hdoa hdob
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
      -- One open-coded iteration.
      obtain ⟨s1, hs1, hs1_mem, hs1_bw, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_openLoopBodySub_step s a b bin hbw hap_head hbp_head
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
      have hbw1 : s1.regs "bw" = BitVec.ofNat 64 (if (sbbStep a b bin).2 then 1 else 0) := by
        rw [hs1_bw]; simp [borrowNat]
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_bw, hs'_frame⟩ :=
        ih bs s1 (sbbStep a b bin).2 extra hlen' hbw1 hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_openLoopSub_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
          (Mpn.SubPrototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
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
      · rw [hs'_bw]; simp only [mpnSubN]
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

/-! ## §5  Assembly: `MpnSubOpenCarryRefines`

The full bridge for the open-coded variant, identical in shape to
`Mpn.SubPrototype.MpnSubNRefinesStmt` (and to
`Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefines`): `body = [bw := 0;
while (n != 0) { … }]`, the prelude zeroes the GPR borrow, and the loop is
`mpnSubN_openLoop`. -/

/-- Bridge statement (same shape as `Mpn.SubPrototype.MpnSubNRefinesStmt`): from a
    state holding `as` at `ap`, `bs` at `bp`, `n = |as|`, with the `op` output
    region disjoint from the `ap`/`bp` input regions, running the open-coded
    `body` lands in a state whose memory at `op` holds `(mpnSubN as bs false).1`
    and whose GPR borrow register `bw` holds the borrow-out. -/
def MpnSubOpenCarryRefinesStmt : Prop :=
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
    ∃ s', bignumExecFuel emptyRegistry fuel body s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnSubN as bs false).1 ∧
      s'.regs "bw" = BitVec.ofNat 64 (borrowNat (mpnSubN as bs false).2)

/-- **The open-coded sub bridge, fully proved.**  `body` (`bw := 0;
    while (n != 0) { open-coded loopBody }`) refines `mpnSubN` over byte memory.
    The `bw := 0` prelude makes the first iteration's borrow-in `false`; the loop
    is `mpnSubN_openLoop`.  Identical proof skeleton to
    `Mpn.SubPrototype.MpnSubNJasminRefines` and
    `Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefines`. -/
theorem MpnSubOpenCarryRefines : MpnSubOpenCarryRefinesStmt := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  set s0 : BignumState := setReg s "bw" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "bw" }) .AT_none (.sword .U64) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hbw0 : s0.regs "bw" = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "bw" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "bw" → regAddr s0 x = regAddr s x := by
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
  obtain ⟨s', hs', hs'_mem, hs'_bw, _⟩ :=
    mpnSubN_openLoop as bs s0 false extra hlen hbw0 hn0' hap0 hbp0 hdoa0 hdob0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) body s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody] s0 := by
      conv_lhs => rw [body]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    exact hs'_mem
  · exact hs'_bw

end CatCrypt.Crypto.Jasmin.Mpn.SubOpenCarryPrototype
