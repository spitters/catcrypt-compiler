/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

set_option autoImplicit false

/-!
# Open-coded-carry variant of the verified `mpn_add_n` loop

**EXPERIMENTAL FILE.**  Companion to `Mpn.AddPrototype.lean`.  Same verified
`mpn_add_n` (add two equal-length limb arrays with carry), but the loop body
threads the carry as an **ordinary `u64` GPR value** using an *open-coded
add-with-carry* (two-add idiom) instead of `#ADC_64`'s physical CF flag.

## Why this variant exists (the backend gap it closes)

The committed `Mpn.AddPrototype.body` runs the carry through `#ADC_64(t, s, cf)`,
which both reads and writes the architectural carry flag `cf` *across the
`while (n != 0)` back-edge*.  The GMP differential harness (`bench/gmp_diff`,
commit `c6a10cb9`) found that this does **not** compile with `jasminc`:

* the emitter reclassifies `cf` into the bool flag bank (`reg bool of cf …`),
  so the `cf := 0` init is an `int → bool` clash; and
* `jasminc`'s register allocator rejects a physical CF flag kept live across a
  loop back-edge.

The harness worked around it with an *unverified* carry-spill rewrite.

**This file's variant has no such problem.**  The loop body is

```
sum0 = t + s        -- #ADD_64 → (cf1, r0):  addCarry t s
r    = r0 + cf      -- #ADD_64 → (cf2, r) :  addCarry r0 cf  (cf is the GPR carry-in)
cf   = cf1 ||| cf2  -- Olor: the new carry (a u64 ∈ {0,1})
```

The threaded carry `cf` is a `u64` value, not a flag, so it crosses the
back-edge in a general-purpose register — exactly what the register allocator
wants.  The two `#ADD_64` carry-out flags `cf1`, `cf2` are dead within the body
(materialized to GPRs before the next flag is born), so no physical flag is
live across the back-edge.

## Reuse from `MpnAddPrototype`

The open-coded body computes *exactly* `BignumExec.addCarryIn t s cf` — the
existing executable ADC, whose definition is itself the two-add idiom
(`s1 = a+b; cf1 = s1 <u a; r = s1+cin; cf2 = r <u s1; (cf1|||cf2, r)`).  So the
genuinely new proof (`openBody_eq_addCarryIn`) is just that the two `#ADD_64`s
plus the `Olor` reconstruct `addCarryIn`, after which the carry-chain math
(`adcStep`, `addCarryIn_spec`, `mpnAddN_spec`) and *all* the general loop /
memory lemmas are inherited verbatim from `MpnAddPrototype`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.AddOpenCarryPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

/-! ## §1  The open-coded Jasmin `mpn_add_n` body -/

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

/-- `r += k` / `r -= k` scalar update. -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- The 6-LVal `#ADD_64` flag bundle `[_, cf_out, _, _, _, dst]` capturing the
    carry-out into register `cfName` and the sum into `rName`. -/
def addCopn (cfName rName aName bName : String) : InstrR :=
  .Copn ([.Lnone {} (.sword .U64), .Lvar { var := vr cfName }]
          ++ List.replicate 3 (.Lnone {} (.sword .U64))
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"ADD_64"⟩)
        [pv aName, pv bName]

/-- One open-coded loop iteration:
    ```
    t  = [:u64 ap + 0];
    s  = [:u64 bp + 0];
    _, cf1, _, _, _, r0 = #ADD_64(t, s);     // addCarry t s
    _, cf2, _, _, _, r  = #ADD_64(r0, cf);   // addCarry r0 cf (cf = GPR carry-in)
    cf = cf1 | cf2;                          // Olor: new GPR carry ∈ {0,1}
    [:u64 op + 0] = r;
    ap += 8; bp += 8; op += 8; n -= 1;
    ```
    `cf` is a plain `u64` register, threaded across iterations.  No `#ADC_64`,
    no physical flag across the back-edge. -/
def loopBody : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , addCopn "cf1" "r0" "t" "s"
  , addCopn "cf2" "r" "r0" "cf"
  , .Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64)
      (.Papp2 (.Olor .U64) (pv "cf1") (pv "cf2"))
  , storeAt0 "op" "r"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body: `cf = 0; while (n != 0) { <loopBody> }`. -/
def body : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody ]

/-- `mpn_add_n(op, ap, bp, n)` as a `FunDecl`, open-coded carry. -/
def mpnAddNFd : FunDecl where
  name := { name := "mpn_add_n_oc" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := body
  results := []

/-- The loop is constant-time-shaped: the guard depends only on the public
    length `n`. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd body = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnAddNFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  The one genuinely new fact: open-coded body = `addCarryIn`

The two `#ADD_64`s plus the `Olor` reconstruct `BignumExec.addCarryIn`, whose
definition *is* the two-add idiom.  Everything else is inherited. -/

/-- `addCarry a b = (cf, r)` where `cf = if (a+b).ult a then 1 else 0` and
    `r = a + b`.  Definitional unfold. -/
theorem addCarry_eq (a b : BitVec 64) :
    addCarry a b = ((if (a + b).ult a then 1 else 0), a + b) := rfl

/-- **Open-coded composition = `addCarryIn`.**  Composing `addCarry t s` (giving
    `(cf1, r0)`) with `addCarry r0 cf` (giving `(cf2, r)`) and taking the new
    carry as `cf1 ||| cf2` yields exactly `addCarryIn t s cf` — *provided the
    carry-in `cf` is already reduced to its low bit* (`cf &&& 1 = cf`), which the
    threaded GPR carry always is (it is `0` or `1`).  Pure `BitVec`, closed by
    `bv_decide`.

    Concretely: `(carry-out, sum) = (cf1 ||| cf2, r)` with `r = (t + s) + cf`
    and the two carry flags from the two adds.  `addCarryIn` masks its carry-in
    (`cf &&& 1`); the open-coded body uses `cf` raw, so the two agree exactly
    when `cf` is already a low bit.  Without the hypothesis the claim is false
    for `cf ≥ 2` — the hypothesis is the loop invariant that the carry stays a
    single bit. -/
theorem openBody_eq_addCarryIn (t s cf : BitVec 64) (hcf : cf &&& 1 = cf) :
    ((addCarry t s).1 ||| (addCarry (addCarry t s).2 cf).1,
      (addCarry (addCarry t s).2 cf).2)
      = addCarryIn t s cf := by
  unfold addCarry addCarryIn
  refine Prod.ext ?_ ?_ <;> bv_decide

/-- The open-coded body, evaluated on a carry-in encoded as a single bit,
    produces `adcStep`'s `(sum, carry-out)`.  Bridges the two `#ADD_64`s + `Olor`
    (`openBody_eq_addCarryIn`) to the carry-chain reference via the existing
    `addCarryIn_sum` / `addCarryIn_carry`. -/
theorem openBody_sum (t s : BitVec 64) (cin : Bool) :
    (addCarry (addCarry t s).2 (BitVec.ofNat 64 (if cin then 1 else 0))).2
      = (adcStep t s cin).1 := by
  have hmask : (BitVec.ofNat 64 (if cin then 1 else 0)) &&& 1
      = BitVec.ofNat 64 (if cin then 1 else 0) := by cases cin <;> bv_decide
  have h := openBody_eq_addCarryIn t s (BitVec.ofNat 64 (if cin then 1 else 0)) hmask
  have h2 := congrArg Prod.snd h
  simp only at h2
  rw [h2]; exact addCarryIn_sum t s cin

theorem openBody_carry (t s : BitVec 64) (cin : Bool) :
    ((addCarry t s).1 ||| (addCarry (addCarry t s).2
        (BitVec.ofNat 64 (if cin then 1 else 0))).1)
      = BitVec.ofNat 64 (carryNat (adcStep t s cin).2) := by
  have hmask : (BitVec.ofNat 64 (if cin then 1 else 0)) &&& 1
      = BitVec.ofNat 64 (if cin then 1 else 0) := by cases cin <;> bv_decide
  have h := openBody_eq_addCarryIn t s (BitVec.ofNat 64 (if cin then 1 else 0)) hmask
  have h1 := congrArg Prod.fst h
  simp only at h1
  rw [h1]; exact addCarryIn_carry t s cin

/-! ## §3  One open-coded iteration as an explicit state update

Mirror of `Mpn.AddPrototype.bignumExec_loopBody_step`, for the open-coded body:
load `a`, `b`; two `#ADD_64`s + `Olor`; store the sum at `op`; advance the three
pointers by 8 and decrement `n`.  The carry register holds `carryNat` of
`adcStep`'s carry-out — identical observable effect to the `#ADC_64` body, by
`openBody_sum` / `openBody_carry`. -/

-- The symbolic-execution simp sets below are deliberately robust (they mirror
-- `Mpn.AddPrototype.bignumExec_loopBody_step`); the `unusedSimpArgs` linter flags
-- entries that happen not to fire on this body, but keeping them makes the proof
-- resilient to small evaluation-order changes.
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_openLoopBody_step (s : BignumState) (a b : BitVec 64) (cin : Bool)
    (hcf : s.regs "cf" = BitVec.ofNat 64 (if cin then 1 else 0))
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBody s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (adcStep a b cin).1.toNat) ∧
      s'.regs "cf" = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Unfold the body into nested `execInstr` matches, resolving the two loads,
  -- the two `#ADD_64` bundles, the `Olor`, the store, and the four advances.
  simp only [loopBody, loadAt0, addCopn, storeAt0, binImm,
             bignumExec, execInstr, evalPExpr, pv, resolveAddr_reg, vr,
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
  -- The witness state is concrete; read off carry (open-coded bridges), store,
  -- and the four register advances.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Reduce all the `setReg … .regs "X"` lookups (and `.mem` projections) on
  -- the concrete witness state.  The two loaded words `t`,`s` resolve to
  -- `a`,`b`; the threaded carry register `cf` resolves (via `hcf`) to the
  -- encoded carry bit.  `+ 0` on the store address vanishes.
  all_goals
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte, hcf,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]
  · -- memory: stored value `(addCarry (addCarry a b).2 cf).2` = `adcStep` sum.
    rw [openBody_sum a b cin]
  · -- carry register: `(addCarry a b).1 ||| (addCarry (addCarry a b).2 cf).1`
    -- = `ofNat (carryNat (adcStep a b cin).2)`.
    rw [openBody_carry a b cin]

/-- The open-coded `loopBody` is straight-line (`Cassgn`/`Copn` only). -/
theorem loopBody_straightLine : InstrR.bodyIsStraightLine loopBody := by
  simp only [loopBody, loadAt0, addCopn, storeAt0, binImm, InstrR.bodyIsStraightLine,
             InstrR.isStraightLine, and_self]

/-- Every instruction of the open-coded `loopBody` is non-control. -/
theorem loopBody_nonControl : ∀ i ∈ loopBody, i.isNonControl := by
  intro i hi
  simp only [loopBody, loadAt0, addCopn, storeAt0, binImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- **Forward one-iteration rule for the open-coded loop.**  Clone of
    `Mpn.AddPrototype.bignumExecFuel_loop_step` (which is hardcoded to that file's
    `loopBody`), retargeted at *this* file's open-coded `loopBody` via the local
    `loopBody_straightLine` / `loopBody_nonControl`.  The general fuel lemmas
    (`bignumExecFuel_eq_bignumExec_of_straightLine`, `bignumExecFuel_append_join`)
    are reused verbatim. -/
theorem bignumExecFuel_openLoop_step (reg : BignumRegistry) (f : Nat)
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

/-! ## §4  The open-coded loop, by induction on the limb list

A clone of `Mpn.AddPrototype.mpnAddN_loop` with `bignumExec_openLoopBody_step`
in place of `bignumExec_loopBody_step`.  Each iteration peels one limb; the
carry threads through the GPR `cf`; the per-iteration store is framed against
the unread `ap`/`bp` suffixes (`load64Mem_store64_disjoint`).  Every supporting
lemma (`bignumExecFuel_loop_step/_exit`, the memory frame, the range algebra) is
reused verbatim from `MpnAddPrototype` — only the one-iteration effect differs,
and it has the identical observable shape. -/

theorem mpnAddN_openLoop :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (cin : Bool) (extra : Nat),
      as.length = bs.length →
      s.regs "cf" = BitVec.ofNat 64 (if cin then 1 else 0) →
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
        memHoldsLimbs s'.mem (regAddr s "op") (mpnAddN as bs cin).1 ∧
        s'.regs "cf" = BitVec.ofNat 64 (carryNat (mpnAddN as bs cin).2) ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s cin extra _ hcf hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBody s
        (evalPExpr_loopCond_false s hn0)
    · simp [mpnAddN, memHoldsLimbs]
    · simpa [mpnAddN, carryNat] using hcf
    · intro b _; rfl
  | cons a as ih =>
    intro bs s cin extra hlen hcf hn hap hbp hdoa hdob
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
      obtain ⟨s1, hs1, hs1_mem, hs1_cf, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_openLoopBody_step s a b cin hcf hap_head hbp_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 8 := by
        simp only [regAddr, hs1_bp]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (adcStep a b cin).1.toNat) := by
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
      have hcf1 : s1.regs "cf" = BitVec.ofNat 64 (if (adcStep a b cin).2 then 1 else 0) := by
        rw [hs1_cf]; simp [carryNat]
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_cf, hs'_frame⟩ :=
        ih bs s1 (adcStep a b cin).2 extra hlen' hcf1 hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_openLoop_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
          (evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · rw [hmem1] at hs'_frame
        have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
          range_op_head_tail_disjoint op0 as.length (by omega)
        refine ⟨?_, ?_⟩
        · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          have hread := load64Mem_store64_same s.mem op0 (UInt64.ofNat (adcStep a b cin).1.toNat)
          rw [hread]
          rfl
        · have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · rw [hs'_cf]; simp only [mpnAddN]
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

/-! ## §5  Assembly: `MpnAddOpenCarryRefines`

The full bridge for the open-coded variant, identical in shape to
`Mpn.AddPrototype.MpnAddNRefinesStmt`: `body = [cf := 0; while (n != 0) { … }]`,
the prelude zeroes the GPR carry, and the loop is `mpnAddN_openLoop`. -/

/-- Bridge statement (same shape as `Mpn.AddPrototype.MpnAddNRefinesStmt`): from a
    state holding `as` at `ap`, `bs` at `bp`, `n = |as|`, with the `op` output
    region disjoint from the `ap`/`bp` input regions, running the open-coded
    `body` lands in a state whose memory at `op` holds `(mpnAddN as bs false).1`
    and whose GPR carry register `cf` holds the carry-out. -/
def MpnAddOpenCarryRefinesStmt : Prop :=
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
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnAddN as bs false).1 ∧
      s'.regs "cf" = BitVec.ofNat 64 (carryNat (mpnAddN as bs false).2)

/-- **The open-coded bridge, fully proved.**  `body` (`cf := 0;
    while (n != 0) { open-coded loopBody }`) refines `mpnAddN` over byte memory.
    The `cf := 0` prelude makes the first iteration's carry-in `false`; the loop
    is `mpnAddN_openLoop`.  Identical proof skeleton to
    `Mpn.AddPrototype.MpnAddNJasminRefines`. -/
theorem MpnAddOpenCarryRefines : MpnAddOpenCarryRefinesStmt := by
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
    mpnAddN_openLoop as bs s0 false extra hlen hcf0 hn0' hap0 hbp0 hdoa0 hdob0
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
  · exact hs'_cf

end CatCrypt.Crypto.Jasmin.Mpn.AddOpenCarryPrototype
