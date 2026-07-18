/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnComparePrototype

set_option autoImplicit false

/-!
# Non-aliasing `mpn_compare` body — InstrR-level fix for `jasminc`'s
# SUB-destructive aliasing constraint

**EXPERIMENTAL FILE.**  Companion to `MpnComparePrototype.lean`.  Same verified
`mpn_compare` (forward least-significant-first scan with a branchless
result-thread), but the loop body inserts two scratch `mov` ops before the
non-destructive `#SUB_64`s so `jasminc`'s register allocator accepts the body
*as-is* — no textual `.jazz` post-process.

## The aliasing problem

`MpnComparePrototype.loopBodyCmp` emits two non-destructive `#SUB_64`s

```
_, lt, _, _, _, d1 = #SUB_64(t, s);   // dst = d1, first src = t
_, gt, _, _, _, d2 = #SUB_64(s, t);   // dst = d2, first src = s
```

`jasminc`'s x86 backend treats `SUB` as destructive (dst == first src), so it
demands `d1 ≡ t` and `d2 ≡ s`.  But `t`/`s` are live for the *other* SUB
(`d1`'s SUB reads `s`, `d2`'s SUB reads `t`), and the standard merge fails:

```
register allocation: conflicting variables "t" and "d1" must be merged
```

The previous `bench/{gmp_perf,integration}/emit.lean::fixupCmp` worked around
this by splicing scratch-copy lines

```
d1 = t;
_, lt, _, _, _, d1 = #SUB_64(d1, s);
d2 = s;
_, gt, _, _, _, d2 = #SUB_64(d2, t);
```

into the emitted `.jazz` *after* the verified emit — i.e. an **unverified**
textual rewrite.

## The InstrR-level fix

This file moves the fix into the InstrR AST itself.  `loopBodyCmp_nonAlias`
inserts two `Cassgn` register-copies (`d1 := t`, `d2 := s`) and reads the SUB
first source from the freshly-aliased scratch:

```
loadAt0 "t" "ap"
loadAt0 "s" "bp"
movReg  "d1" "t"            -- NEW
subCopn "lt" "d1" "d1" "s"   -- d1's SUB now has dst == first src ✓
movReg  "d2" "s"            -- NEW
subCopn "gt" "d2" "d2" "t"   -- d2's SUB now has dst == first src ✓
…rest unchanged…
```

The denotation is identical to `loopBodyCmp`: the SUB's borrow flags `lt`/`gt`
are the *only* observed outputs (`d1`/`d2` are dead after the SUB and were
already discarded in the original), and `subBorrow d1 s = subBorrow t s` after
`d1 := t` (same operands).  The branchless update chain that follows reads
only `lt`/`gt`, which are unchanged.

## Reuse from `MpnComparePrototype`

Everything except the per-iteration step lemma and the loop induction are
reused: the limb-list denotation `toNat`, the pure reference `mpnCmp` /
`cmpUpdate` / `mpnCompare`, all helpers (`vr`/`pv`/`loadAt0`/`subCopn`/
`binReg`/`binImm`/`binImmSrc`), and all §6/§9-loop guard lemmas.  The new
content is two extra `Cassgn` ops in `loopBodyCmp_nonAlias`, a re-proved
per-iteration step lemma, a tiny re-proof of `bignumExecFuel_loopCmp_step` at
the new body, and a re-induction over the limb list (same shape as
`mpnCmp_loop`).
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnCompareNonAliasPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnComparePrototype

/-! ## §1  The non-aliasing `mpn_compare` body -/

/-- `dst = src` register copy (a `Cassgn` of a `Pvar`). -/
def movReg (dst src : String) : InstrR :=
  .Cassgn (.Lvar { var := vr dst }) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- One loop iteration body with the scratch copies in place.  The two extra
    `movReg` ops give each `#SUB_64` a destination that already matches its
    first source operand, so `jasminc`'s SUB-destructive aliasing constraint
    is satisfied *at emit time*. -/
def loopBodyCmpNA : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , movReg "d1" "t"
  , subCopn "lt" "d1" "d1" "s"
  , movReg "d2" "s"
  , subCopn "gt" "d2" "d2" "t"
  , binReg "step" "gt" (.Osub .U64) "lt"
  , binReg "nz" "lt" (.Olor .U64) "gt"
  , binImmSrc "notmask" "nz" (.Osub .U64) 1
  , binImmSrc "mask" "notmask" (.Olxor .U64) (-1)
  , binReg "u1" "mask" (.Oland .U64) "step"
  , binReg "u2" "notmask" (.Oland .U64) "result"
  , binReg "result" "u1" (.Olor .U64) "u2"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body: `result := 0; while (n != 0) { <loopBodyCmpNA> }`. -/
def bodyCmpNA : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "result" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyCmpNA ]

/-- The non-aliasing `mpn_compare` as a Jasmin `FunDecl`.  Same params /
    semantics as `MpnComparePrototype.mpnCompareFd`; the only difference is
    the two scratch-copy `Cassgn`s in the body.  Emits directly through
    `emitFunDecl` — no textual fixup needed. -/
def mpnCompareNAFd : FunDecl where
  name := { name := "mpn_compare" }
  params := [⟨{ var := vr "ap" }⟩, ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := bodyCmpNA
  results := []

/-- Constant-time-shaped: the loop guard depends only on the public length
    `n`; the body is branchless (no data-dependent control flow). -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodyCmpNA = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnCompareNAFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  One iteration as an explicit state update

Mirror of `MpnComparePrototype.bignumExec_loopBodyCmp_step` for the non-aliased
body.  The two extra `movReg` ops are pure `Cassgn`s of `Pvar`; reducing them
via `simp only` adds two more `setReg`s to the witness state but leaves the
post-condition identical: same `result`, `ap`, `bp`, `n` outputs.  We follow
the chunked structure from `MpnAddNAdcSpillPrototype` to keep the kernel
within recursion limits.
-/

/-- Effect of one `loadAt0 x base` instruction.  Produces a state with `x` set
    to the loaded value, memory unchanged.  Cloned from
    `MpnAddNAdcSpillPrototype.execInstr_loadAt0` (we don't import that file). -/
private theorem execInstr_loadAt0 (s : BignumState) (x base : String) (v : BitVec 64)
    (hv : load64Mem s.mem (UInt64.ofNat (s.regs base).toNat)
            = some (UInt64.ofNat v.toNat)) :
    execInstr s (loadAt0 x base) = some (setReg s x v) := by
  simp only [loadAt0, execInstr, evalPExpr, pv, vr,
             resolveAddr, Option.bind_some, bind, Option.bind,
             show BitVec.ofInt 64 0 = 0 from rfl]
  rw [show s.regs base + 0 = s.regs base from by bv_decide, hv]
  simp only [bv_uint_roundtrip, bind, Option.bind, Option.bind_some]

/-- Effect of `movReg dst src`: writes `s.regs src` into `dst`. -/
private theorem execInstr_movReg (s : BignumState) (dst src : String) :
    execInstr s (movReg dst src) = some (setReg s dst (s.regs src)) := by
  simp only [movReg, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind]

/-- Effect of `subCopn cfName dstName aName bName`: sets the `cfName` register
    to the borrow flag and the `dstName` register to the difference.
    Cloned-up from MpnComparePrototype style. -/
private theorem execInstr_subCopn (s : BignumState)
    (cfName dstName aName bName : String) :
    execInstr s (subCopn cfName dstName aName bName) = some
      (setReg (setReg s cfName (subBorrow (s.regs aName) (s.regs bName)).1)
        dstName (subBorrow (s.regs aName) (s.regs bName)).2) := by
  simp only [subCopn, flag_pre, flag_post, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]

/-- Forward append-join for `bignumExec` (local copy of
    `LowCTBorrowCheckInPlace.bignumExec_append_some`). -/
private theorem bignumExec_append_some
    (b1 b2 : List InstrR) (s s_mid s' : BignumState)
    (h1 : bignumExec b1 s = some s_mid)
    (h2 : bignumExec b2 s_mid = some s') :
    bignumExec (b1 ++ b2) s = some s' := by
  induction b1 generalizing s with
  | nil =>
    simp [bignumExec] at h1
    rw [← h1] at h2; simp; exact h2
  | cons i b1' ih =>
    simp [bignumExec] at h1
    cases h_step : execInstr s i with
    | none => rw [h_step] at h1; cases h1
    | some s1 =>
      rw [h_step] at h1
      simp [bignumExec, h_step]
      exact ih s1 h1

set_option linter.unusedSimpArgs false in
/-- **One iteration of `loopBodyCmpNA`** (run via the straight-line
    interpreter), assuming memory holds limb `a` at `ap` and `b` at `bp`.
    Identical post-condition to the original `loopBodyCmp_step`:
    same `result` update, same `ap`/`bp`/`n` advances, memory unchanged. -/
theorem bignumExec_loopBodyCmpNA_step (s : BignumState) (a b : BitVec 64)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBodyCmpNA s = some s' ∧
      s'.mem = s.mem ∧
      s'.regs "result" = cmpUpdate (s.regs "result") a b ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Strategy: run the existing `loopBodyCmp_step` proof shape, but with the
  -- two extra `movReg`s spliced in.  Unfold everything in one `simp only`
  -- (same approach as the original step lemma — 16 instructions is still
  -- within the recursion limit).
  have ha' : load64Mem s.mem (UInt64.ofNat (s.regs "ap").toNat)
              = some (UInt64.ofNat a.toNat) := ha
  have hb' : load64Mem s.mem (UInt64.ofNat (s.regs "bp").toNat)
              = some (UInt64.ofNat b.toNat) := hb
  simp only [loopBodyCmpNA, loadAt0, subCopn, binReg, binImm, binImmSrc,
             movReg, flag_pre, flag_post,
             bignumExec, execInstr, evalPExpr, pv,
             MpnComparePrototype.resolveAddr_reg, vr,
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
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl,
               show BitVec.ofInt 64 (-1) = (-1 : BitVec 64) from rfl,
               subBorrow, branchless_cmpUpdate]
  exact branchless_cmpUpdate a b (s.regs "result")

/-- `loopBodyCmpNA` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodyCmpNA_straightLine : InstrR.bodyIsStraightLine loopBodyCmpNA := by
  simp only [loopBodyCmpNA, loadAt0, subCopn, binReg, binImm, binImmSrc, movReg,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodyCmpNA` is non-control. -/
theorem loopBodyCmpNA_nonControl : ∀ i ∈ loopBodyCmpNA, i.isNonControl := by
  intro i hi
  simp only [loopBodyCmpNA, loadAt0, subCopn, binReg, binImm, binImmSrc, movReg,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §3  One `Cwhile` iteration over `bignumExecFuel` -/

/-- Forward one-iteration rule for `loopBodyCmpNA`. -/
theorem bignumExecFuel_loopCmpNA_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodyCmpNA s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodyCmpNA] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodyCmpNA] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodyCmpNA s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodyCmpNA s
          loopBodyCmpNA_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodyCmpNA [.Cwhile [] cond loopBodyCmpNA]
        loopBodyCmpNA_nonControl s s_mid s' hsl hrec]

/-! ## §4  Assembly: `MpnCompareNAJasminRefines`

Mirror of `MpnComparePrototype.MpnCompareJasminRefines`.  The bridge statement
is identical (we refine the same pure `mpnCmp` reference); only the runtime
body differs.  The induction is the same proof shape — one limb peeled per
iteration via `bignumExec_loopBodyCmpNA_step` + `bignumExecFuel_loopCmpNA_step`. -/

def MpnCompareNARefinesStmt : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat),
    as.length = bs.length →
    as.length < 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyCmpNA s = some s' ∧
      s'.regs "result" = mpnCmp as bs 0

/-- **The loop, by induction on the limb list.** -/
theorem mpnCmp_loopNA :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (acc : BitVec 64) (extra : Nat),
      as.length = bs.length →
      as.length < 2 ^ 64 →
      s.regs "result" = acc →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      memHoldsLimbs s.mem (regAddr s "bp") bs →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyCmpNA] s
              = some s' ∧
        s'.regs "result" = mpnCmp as bs acc := by
  intro as
  induction as with
  | nil =>
    intro bs s acc extra _ _ hres hn _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodyCmpNA s
        (MpnComparePrototype.evalPExpr_loopCond_false s hn0)
    · rw [hres]; rfl
  | cons a as ih =>
    intro bs s acc extra hlen hwf hres hn hap hbp
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hLsucc : as.length + 1 < 2 ^ 64 := by simpa [List.length_cons] using hwf
      have hwf' : as.length < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      obtain ⟨s1, hs1, hs1_mem, hs1_res, hs1_ap, hs1_bp, hs1_n⟩ :=
        bignumExec_loopBodyCmpNA_step s a b hap_head hbp_head
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 8 := by
        simp only [regAddr, hs1_bp]; exact regAddr_advance _
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hs1_mem]; exact hap_tail
      have hbp1 : memHoldsLimbs s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hs1_mem]; exact hbp_tail
      have hres1 : s1.regs "result" = cmpUpdate acc a b := by rw [hs1_res, hres]
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_res⟩ :=
        ih bs s1 (cmpUpdate acc a b) extra hlen' hwf' hres1 hn1 hap1 hbp1
      refine ⟨s', ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loopCmpNA_step emptyRegistry (2 * as.length + 2 + extra) _
          s s1 s' (MpnComparePrototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · rw [hs'_res]; rfl

/-- **The bridge, fully proved.**  `mpnCompareNAFd.body` (`result := 0;
    while (n != 0) { loopBodyCmpNA }`) refines the pure reference `mpnCmp` over
    byte memory — same statement as `MpnCompareJasminRefines`, different
    runtime body. -/
theorem MpnCompareNAJasminRefines : MpnCompareNARefinesStmt := by
  intro s as bs fuel hlen hwf hn hap hbp hfuel
  set s0 : BignumState := setReg s "result" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "result" }) .AT_none (.sword .U64) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hres0 : s0.regs "result" = 0 := by rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "result" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "result" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]
    simpa [regAddr] using hap
  have hbp0 : memHoldsLimbs s0.mem (regAddr s0 "bp") bs := by
    rw [hmem0, hra0 "bp" (by decide)]
    simpa [regAddr] using hbp
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_res⟩ :=
    mpnCmp_loopNA as bs s0 0 extra hlen hwf hres0 hn0' hap0 hbp0
  refine ⟨s', ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodyCmpNA s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyCmpNA] s0 := by
      conv_lhs => rw [bodyCmpNA]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · exact hs'_res

/-- **The decoded contract.**  Reading the `result` register of the final state
    with `ordOf` gives the GMP `mpn_cmp` outcome.  Combines
    `MpnCompareNAJasminRefines` with the imported `mpnCompare_eq_compare`. -/
theorem MpnCompareNAJasminRefines_ordering
    (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat)
    (hlen : as.length = bs.length) (hwf : as.length < 2 ^ 64)
    (hn : s.regs "n" = BitVec.ofNat 64 as.length)
    (hap : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as)
    (hbp : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs)
    (hfuel : fuel > 2 * as.length + 2) :
    ∃ s', bignumExecFuel emptyRegistry fuel bodyCmpNA s = some s' ∧
      ordOf (s'.regs "result") = compare (toNat as) (toNat bs) := by
  obtain ⟨s', hs', hs'_res⟩ :=
    MpnCompareNAJasminRefines s as bs fuel hlen hwf hn hap hbp hfuel
  refine ⟨s', hs', ?_⟩
  rw [hs'_res]
  exact (mpnCompare_eq_compare as bs hlen)

end CatCrypt.Crypto.Jasmin.Examples.MpnCompareNonAliasPrototype
