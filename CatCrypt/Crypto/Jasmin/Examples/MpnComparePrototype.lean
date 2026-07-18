/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

set_option autoImplicit false

/-!
# Phase 2 — verified variable-length `mpn_compare` by template reuse

**EXPERIMENTAL FILE.**  This is the Phase-2 companion to `MpnAddPrototype.lean`
and `MpnSubPrototype.lean`.  It proves the GMP kernel `mpn_compare` (compare two
equal-length limb arrays) end-to-end against the Jasmin `Cwhile` semantics —
*reusing the Phase-1 machinery verbatim*.

`mpn_compare` is one of the six primitives the verified-GMP integration seam
needs (the fallback comparison).

## The forward-scan-vs-top-down design choice

The textbook `mpn_cmp` scans **most-significant limb first** and early-exits at
the first differing limb.  That control shape (a count-DOWN over a decreasing
index with a data-dependent `break`) does *not* fit the forward, count-up
`while (n != 0)` loop rule we proved in Phase 1 — it would need a second loop
rule (a top-down loop with early exit) and a different invariant.

Instead this prototype scans **least-significant limb first** (the same
direction the add/sub loops walk) and keeps a `result` register that is
overwritten *every time* a limb differs, encoding that limb's order
(`a[i] > b[i] → 1`, `a[i] < b[i] → -1 = 0xFFFF…FFFF`, equal → leave `result`).
Because the scan runs low→high, the **last** overwrite is the **highest**
differing limb — which is exactly the limb that determines the unsigned
ordering of the two bignums.  So the final `result` is correct, with **no early
exit**, and the loop reuses the Phase-1 forward `while (n != 0)` rule
(`bignumExecFuel_loop_step` / `_exit`, `evalPExpr_loopCond_true`/`_false`)
unchanged.

Cost: the forward scan always touches all `n` limbs (the top-down version stops
early on the average input).  This is a deliberate trade — it is also *constant
time* in the number of limbs, which is the right shape for a side-channel-safe
comparison anyway.

## Branchless per-limb update (so the loop body stays straight-line)

The Phase-1 `Cwhile` rule requires the loop body to be **straight-line** (so
`bignumExecFuel` agrees with `bignumExec` and `bignumExecFuel_append_join`
applies).  A `Cif`-based "if a≠b then result := …" body would break that.  So
the per-limb update is computed branchlessly from the two `#SUB_64` borrow
flags:

```
_, lt, _, _, _, _ = #SUB_64(t, s);   // lt = 1 iff t < s
_, gt, _, _, _, _ = #SUB_64(s, t);   // gt = 1 iff t > s
step    = gt - lt;                   // 1 if t>s, 0xFF..FF if t<s, 0 if t=s
nz      = lt | gt;                   // 1 iff t ≠ s, else 0
notmask = nz - 1;                    // 0 iff t≠s, 0xFF..FF iff t=s
mask    = notmask ^ (-1);            // 0xFF..FF iff t≠s, 0 iff t=s
result  = (mask & step) | (notmask & result);  // overwrite iff t≠s
```

Every instruction here is a `Cassgn`/`Copn` the emitter supports (`#SUB_64`,
and `Papp2` over `-`, `|`, `&`, `^`); none uses `Oeq`/`Oneq` (which `binOpStr`
does not emit outside the loop guard).  `mpn_compare` only *reads* memory (no
stores), so the op-vs-ap/bp memory frame from Phase 1 is unneeded — only the
`ap`/`bp` loads must be undisturbed, and there are no stores to disturb them.

## Functional spec

`mpnCmp a b result` (forward scan, `result`-threading) at `result = 0` reflects
the unsigned ordering: reading the final register as an `Ordering`
(`0 → eq`, `1 → gt`, `0xFF..FF → lt`) gives `compare (toNat a) (toNat b)`
(`mpnCompare_eq_compare`).  The bridge `MpnCompareJasminRefines` then says the
emitted loop computes `mpnCmp` into the `result` register.

## Follow-up: unequal-length compare

The integration target compares operands of *different* limb length
(zero-extend the shorter, or compare the high limbs of the longer against zero
first).  This file does the **equal-length** case; the unequal-length wrapper is
a deliberate follow-up (it composes this loop with a "scan the extra high limbs
for nonzero" prefix — the same forward-scan idea).

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnComparePrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

/-! ## §1  The Jasmin `mpn_compare` body — runtime `Cwhile` loop

The small instruction-builder helpers are `private` in `MpnAddPrototype`, so we
re-declare definitionally-identical local copies here (same shape ⇒ identical
emitter/interpreter behavior). -/

/-- `reg u64` variable. -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- Memory load `x := [:u64 base + 0]`. -/
def loadAt0 (x base : String) : InstrR :=
  .Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
    (.Pload .U64 { var := vr base } (.Pconst 0))

/-- `r OP= k` style scalar update with an immediate (reads + writes `r`). -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- `dst = src OP k` register-immediate update (`dst` may differ from `src`). -/
def binImmSrc (dst src : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr dst }) .AT_none (.sword .U64)
    (.Papp2 op (pv src) (.Pconst k))

/-- `dst = src1 OP src2` register-register update. -/
def binReg (dst src1 : String) (op : SOp2) (src2 : String) : InstrR :=
  .Cassgn (.Lvar { var := vr dst }) .AT_none (.sword .U64)
    (.Papp2 op (pv src1) (pv src2))

def flag_pre  : List LVal := [.Lnone {} (.sword .U64)]
def flag_post : List LVal := List.replicate 3 (.Lnone {} (.sword .U64))

/-- `_, cf, _, _, _, dst = #SUB_64(a, b);` — the borrow flag `cf` is `1`
    iff `a < b` (unsigned); `dst` is the (discarded) difference. -/
def subCopn (cfName dstName aName bName : String) : InstrR :=
  .Copn (flag_pre ++ [.Lvar { var := vr cfName }] ++ flag_post
          ++ [.Lvar { var := vr dstName }])
        .AT_none (.Oasm ⟨"SUB_64"⟩)
        [pv aName, pv bName]

/-- One loop iteration body for `mpn_compare` (least-significant first):
    ```
    t = [:u64 ap + 0];
    s = [:u64 bp + 0];
    _, lt, _, _, _, d1 = #SUB_64(t, s);   // lt = (t < s)
    _, gt, _, _, _, d2 = #SUB_64(s, t);   // gt = (t > s)
    step    = gt - lt;
    nz      = lt | gt;
    notmask = nz - 1;
    mask    = notmask ^ (-1);
    u1      = mask & step;
    u2      = notmask & result;
    result  = u1 | u2;
    ap += 8; bp += 8; n -= 1;
    ```
    No store — `mpn_compare` only reads.  `result` is initialised to `0`
    (equal) before the loop and overwritten on every differing limb. -/
def loopBodyCmp : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , subCopn "lt" "d1" "t" "s"
  , subCopn "gt" "d2" "s" "t"
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

/-- Full body of `mpn_compare`:
    ```
    result = 0;
    while (n != 0) { <loopBodyCmp> }
    ```
    `result` holds the comparison outcome (`0` equal, `1` `a > b`,
    `0xFFFF…FFFF = -1` `a < b`); GMP's `mpn_cmp` returns it as a signed int. -/
def bodyCmp : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "result" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyCmp ]

/-- `mpn_compare(ap, bp, n)` as a Jasmin `FunDecl`.  Reads only; the result is
    left in the `result` register (the GMP `mpn_cmp` ABI returns it).  SysV ABI
    `rdi=ap, rsi=bp, rdx=n`. -/
def mpnCompareFd : FunDecl where
  name := { name := "mpn_compare" }
  params := [⟨{ var := vr "ap" }⟩, ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := bodyCmp
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the public
    length `n`, never a secret limb; the body is branchless (no data-dependent
    control flow). -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodyCmp = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnCompareFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional reference + Ordering decoding

`toNat` (little-endian limb denotation) is imported from `MpnAddPrototype`. -/

/-- A `k`-limb little-endian value is `< (2^64)^k`: the standard radix bound,
    by induction on the limb list. -/
theorem toNat_lt (ws : List (BitVec 64)) : toNat ws < (2 ^ 64) ^ ws.length := by
  induction ws with
  | nil => simp [toNat]
  | cons w ws ih =>
    have hw := w.isLt
    simp only [toNat, List.length_cons, pow_succ]
    -- `w.toNat + 2^64 * toNat ws < 2^64 * (2^64)^|ws|`, using `toNat ws < (2^64)^|ws|`.
    calc w.toNat + 2 ^ 64 * toNat ws
        < 2 ^ 64 + 2 ^ 64 * toNat ws := by omega
      _ ≤ 2 ^ 64 * (2 ^ 64) ^ ws.length := by
            have : toNat ws + 1 ≤ (2 ^ 64) ^ ws.length := ih
            nlinarith [ih]
      _ = (2 ^ 64) ^ ws.length * 2 ^ 64 := by ring

/-- The per-limb comparison "step", as a `BitVec 64`:
    `1` if `a > b`, `-1` (`= 0xFFFF…FFFF`) if `a < b`, `0` if `a = b`. -/
def cmpStep (a b : BitVec 64) : BitVec 64 :=
  if a.toNat > b.toNat then 1 else if a.toNat < b.toNat then (-1) else 0

/-- The result-threading update for one limb pair: overwrite the running
    `result` with `cmpStep a b` iff the limbs differ, else leave it.  This is
    exactly the branchless `result := (mask & step) | (notmask & result)`
    the loop body computes (`cmpUpdate_branchless`). -/
def cmpUpdate (result a b : BitVec 64) : BitVec 64 :=
  if a = b then result else cmpStep a b

/-- Pure reference for `mpn_compare`: a **forward** (least-significant first)
    scan threading the running `result`.  Because higher-order limbs are
    processed *later*, the last overwrite (the highest differing limb) wins —
    matching the unsigned ordering. -/
def mpnCmp : List (BitVec 64) → List (BitVec 64) → BitVec 64 → BitVec 64
  | a :: as, b :: bs, result => mpnCmp as bs (cmpUpdate result a b)
  | _, _, result => result

/-- Decode the `result` register to an `Ordering`: `1 → gt`, `-1 → lt`,
    everything else (in practice only `0`) → `eq`. -/
def ordOf (r : BitVec 64) : Ordering :=
  if r = 1 then .gt else if r = (-1 : BitVec 64) then .lt else .eq

/-- `mpn_compare a b : Ordering` — the GMP `mpn_cmp` outcome, read off the
    `result` register after a forward scan started at `0` (equal). -/
def mpnCompare (a b : List (BitVec 64)) : Ordering := ordOf (mpnCmp a b 0)

/-! ## §3  Functional spec: the forward-scan invariant

The load-bearing theorem.  Like add/sub this needs an inductive invariant
(`bv_decide` cannot close an unbounded scan).  The invariant: after scanning all
limbs from a running accumulator `acc`, the decoded result is the high-order
comparison if the operands differ, otherwise the decoded accumulator. -/

/-- `(0 : BitVec 64) ≠ 1`, `(0 : BitVec 64) ≠ -1`, `(-1 : BitVec 64) ≠ 1` —
    the three sentinel disequalities the decoder needs, via `bv_decide`. -/
theorem zero_ne_one : (0 : BitVec 64) ≠ 1 := by bv_decide
theorem zero_ne_negone : (0 : BitVec 64) ≠ (-1 : BitVec 64) := by bv_decide
theorem negone_ne_one : (-1 : BitVec 64) ≠ 1 := by bv_decide

/-- `cmpStep` decodes to the unsigned `compare` of the two limbs. -/
theorem ordOf_cmpStep (a b : BitVec 64) :
    ordOf (cmpStep a b) = compare a.toNat b.toNat := by
  rcases lt_trichotomy a.toNat b.toNat with h | h | h
  · -- a < b ⇒ step = -1 ⇒ lt
    have hs : cmpStep a b = (-1 : BitVec 64) := by
      unfold cmpStep; rw [if_neg (by omega), if_pos h]
    rw [hs, ordOf, if_neg negone_ne_one, if_pos rfl, Nat.compare_eq_lt.mpr h]
  · -- a = b ⇒ step = 0 ⇒ eq
    have hs : cmpStep a b = (0 : BitVec 64) := by
      unfold cmpStep; rw [if_neg (by omega), if_neg (by omega)]
    rw [hs, ordOf, if_neg zero_ne_one, if_neg zero_ne_negone, Nat.compare_eq_eq.mpr h]
  · -- a > b ⇒ step = 1 ⇒ gt
    have hs : cmpStep a b = (1 : BitVec 64) := by
      unfold cmpStep; rw [if_pos h]
    rw [hs, ordOf, if_pos rfl, Nat.compare_eq_gt.mpr h]

/-- **Main functional spec — proved by induction on the limb list.**

    For equal-length limb lists `a, b` and any running accumulator `acc`, the
    forward scan `mpnCmp a b acc` decodes to: the unsigned comparison of the
    bignums if they differ, otherwise the decoded accumulator.  This is the
    invariant the emitted `while (n != 0)` loop maintains — each iteration
    overwrites `result` iff the current (increasingly significant) limb differs,
    so the final register reflects the highest differing limb. -/
theorem ordOf_mpnCmp :
    ∀ (a b : List (BitVec 64)), a.length = b.length → ∀ (acc : BitVec 64),
      ordOf (mpnCmp a b acc)
        = if toNat a = toNat b then ordOf acc else compare (toNat a) (toNat b) := by
  intro a
  induction a with
  | nil =>
    intro b hlen acc
    cases b with
    | nil => simp [mpnCmp, toNat]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen acc
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have ha := a.isLt; have hb := b.isLt
      have htas : toNat as < (2 ^ 64) ^ as.length := toNat_lt as
      have htbs : toNat bs < (2 ^ 64) ^ bs.length := toNat_lt bs
      rw [hlen'] at htas
      -- One step of the scan: `a`/`b` are the LEAST-significant limbs (processed
      -- first); the tail `as`/`bs` are processed later and overwrite.  So the
      -- decision is dominated by the *tail* (higher-order limbs) — exactly the
      -- IH's `compare (toNat as) (toNat bs)`.
      rw [show mpnCmp (a :: as) (b :: bs) acc
            = mpnCmp as bs (cmpUpdate acc a b) from rfl, ih bs hlen' _]
      simp only [toNat, cmpUpdate]
      by_cases htl : toNat as = toNat bs
      · -- Tails equal: the head limb decides the whole comparison.
        rw [if_pos htl]
        by_cases hhd : a = b
        · -- Heads also equal: `result` unchanged, bignums equal.
          rw [if_pos hhd, if_pos (by rw [hhd, htl])]
        · -- Heads differ: `cmpStep a b` decodes to the head comparison, which is
          -- the whole comparison since the tails coincide.
          have hhd' : a.toNat ≠ b.toNat := fun h => hhd (BitVec.eq_of_toNat_eq h)
          rw [if_neg hhd, if_neg (by
                intro heq
                apply hhd'
                have : a.toNat % 2 ^ 64 = b.toNat % 2 ^ 64 := by omega
                rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this),
            ordOf_cmpStep, htl]
          -- `compare a.toNat b.toNat = compare (a.toNat + S) (b.toNat + S)` with
          -- `S := 2^64 * toNat bs` a common shift.
          rcases lt_trichotomy a.toNat b.toNat with h | h | h
          · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (by omega)]
          · exact absurd h hhd'
          · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (by omega)]
      · -- Tails differ: the higher-order limbs dominate; the head is irrelevant.
        -- `toNat as ≠ toNat bs` ⇒ the bignums differ and compare like the tails.
        rw [if_neg htl, if_neg (by
              intro heq
              apply htl
              -- low 64 bits cancel ⇒ tails equal
              have : (a.toNat + 2 ^ 64 * toNat as) / 2 ^ 64 = (b.toNat + 2 ^ 64 * toNat bs) / 2 ^ 64 := by
                rw [heq]
              rwa [Nat.add_mul_div_left _ _ (by norm_num), Nat.add_mul_div_left _ _ (by norm_num),
                Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.zero_add, Nat.zero_add] at this)]
        rcases lt_trichotomy (toNat as) (toNat bs) with h | h | h
        · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (by
              -- `a.toNat < 2^64 ≤ 2^64·(toNat bs - toNat as)` closes it
              have : toNat as + 1 ≤ toNat bs := h
              nlinarith [ha, hb])]
        · exact absurd h htl
        · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (by
              have : toNat bs + 1 ≤ toNat as := h
              nlinarith [ha, hb])]

/-- The GMP `mpn_cmp` contract: `mpnCompare a b` is the unsigned ordering of the
    two bignums (`mpnCompare a b = Ordering.lt ↔ toNat a < toNat b`, etc.). -/
theorem mpnCompare_eq_compare (a b : List (BitVec 64)) (hlen : a.length = b.length) :
    mpnCompare a b = compare (toNat a) (toNat b) := by
  unfold mpnCompare
  rw [ordOf_mpnCmp a b hlen 0]
  by_cases h : toNat a = toNat b
  · rw [if_pos h, h, ordOf, if_neg zero_ne_one, if_neg zero_ne_negone,
      Nat.compare_eq_eq.mpr rfl]
  · rw [if_neg h]

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `[5, 0]` vs `[7, 0]`: low limb differs, high limbs equal ⇒ `lt`. -/
example : mpnCompare [5, 0] [7, 0] = .lt := by native_decide

/-- `[7, 0]` vs `[5, 0]` ⇒ `gt`. -/
example : mpnCompare [7, 0] [5, 0] = .gt := by native_decide

/-- High limb dominates: `[100, 1]` vs `[200, 2]` ⇒ `lt` (high `1 < 2`)
    even though the low limb `100 < 200` agrees here; flip the low limb to
    confirm the high limb still wins. -/
example : mpnCompare [200, 1] [100, 2] = .lt := by native_decide

/-- Equal bignums ⇒ `eq`. -/
example : mpnCompare [42, 7] [42, 7] = .eq := by native_decide

/-! ## §6  Branchless-update bridge: executable `#SUB_64`-flag computation
    matches pure `cmpUpdate`

The emitted body computes the per-limb update from the two `#SUB_64` borrow
flags (`subBorrow`).  This lemma shows that branchless computation equals the
pure `cmpUpdate`. -/

/-- `subBorrow a b` returns the borrow flag `if a.ult b then 1 else 0`
    (position 1 of the bundle) — i.e. `1` iff `a < b` (unsigned). -/
theorem subBorrow_flag (a b : BitVec 64) :
    (subBorrow a b).1 = if a.ult b then 1 else 0 := rfl

/-- `cmpStep` in unsigned-less-than form: `1` iff `b < a`, `-1` iff `a < b`,
    else `0`.  Bridges the Nat-comparison spec to the `BitVec.ult` form the
    executable `#SUB_64` flags produce. -/
theorem cmpStep_ult (a b : BitVec 64) :
    cmpStep a b = if b.ult a then 1 else if a.ult b then (-1 : BitVec 64) else 0 := by
  unfold cmpStep
  simp only [BitVec.ult, decide_eq_true_eq, gt_iff_lt]

/-- **The branchless per-limb identity (pure `BitVec`, closed by `bv_decide`).**
    The emitted sequence
    `step = gt - lt; nz = lt|gt; notmask = nz-1; mask = notmask^(-1);
     (mask & step) | (notmask & result)`
    with `lt = (t<s)`, `gt = (s<t)` computes exactly `cmpUpdate result t s`. -/
theorem branchless_cmpUpdate (t s result : BitVec 64) :
    let lt : BitVec 64 := (subBorrow t s).1
    let gt : BitVec 64 := (subBorrow s t).1
    let step := gt - lt
    let nz := lt ||| gt
    let notmask := nz - 1
    let mask := notmask ^^^ (-1 : BitVec 64)
    (mask &&& step) ||| (notmask &&& result) = cmpUpdate result t s := by
  simp only [subBorrow_flag, cmpUpdate, cmpStep_ult]
  bv_decide

/-! ## §7  One loop iteration as an explicit state update

`loopBodyCmp` is straight-line, so it runs via `bignumExec`.  Given a state
whose memory holds limb `a` at `ap` and `b` at `bp` (no store happens — compare
only reads), one iteration overwrites `result` with `cmpUpdate (result) a b`,
leaves memory unchanged, advances `ap`,`bp` by 8 and decrements `n`.  `regAddr`
(string-keyed) and the `setReg`/`storeMem` projection lemmas are imported from
`MpnAddPrototype`; the local `resolveAddr_reg` mirrors the private add helper for
our local `vr`. -/

/-- `resolveAddr` of a register at offset 0 yields its `UInt64` address. -/
theorem resolveAddr_reg (s : BignumState) (x : String) :
    resolveAddr s { var := vr x } (.Pconst 0) = some (regAddr s x) := by
  simp only [resolveAddr, regAddr, vr]
  norm_num

/-- One iteration of `loopBodyCmp` (run via the straight-line interpreter
    `bignumExec`), assuming memory holds limb `a` at `ap` and `b` at `bp`.
    The result state leaves memory unchanged, sets `result` to
    `cmpUpdate (s.regs "result") a b`, and advances `ap`/`bp`/`n`. -/
theorem bignumExec_loopBodyCmp_step (s : BignumState) (a b : BitVec 64)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBodyCmp s = some s' ∧
      s'.mem = s.mem ∧
      s'.regs "result" = cmpUpdate (s.regs "result") a b ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Unfold the body into the nested `execInstr` matches: resolve the two loads
  -- (round-trip via `ha`/`hb`), the two `#SUB_64` flag bundles, the branchless
  -- update chain, and the `ap`/`bp`/`n` advances.
  simp only [loopBodyCmp, loadAt0, subCopn, binReg, binImm, binImmSrc, flag_pre, flag_post,
             bignumExec, execInstr, evalPExpr, pv, resolveAddr_reg, vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, hb, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  -- Eliminate the residual `+ 0` in the two load addresses; `ha`/`hb` fire and
  -- the loaded words decode to `a`/`b`.
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  rw [show (setReg s "t" a).regs "bp" + 0 = s.regs "bp" from by
        simp only [setReg_regs]; bv_decide, setReg_mem, hb]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.  Read off the registers; the
  -- `result` update is closed by the branchless identity, the rest by the
  -- string-literal `setReg` lookups.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl,
               show BitVec.ofInt 64 (-1) = (-1 : BitVec 64) from rfl,
               subBorrow, branchless_cmpUpdate]
  -- The `result` register goal: the branchless chain equals `cmpUpdate`.
  exact branchless_cmpUpdate a b (s.regs "result")

/-- `loopBodyCmp` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodyCmp_straightLine : InstrR.bodyIsStraightLine loopBodyCmp := by
  simp only [loopBodyCmp, loadAt0, subCopn, binReg, binImm, binImmSrc,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodyCmp` is non-control. -/
theorem loopBodyCmp_nonControl : ∀ i ∈ loopBodyCmp, i.isNonControl := by
  intro i hi
  simp only [loopBodyCmp, loadAt0, subCopn, binReg, binImm, binImmSrc, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §8  One `Cwhile` iteration over `bignumExecFuel`

The imported `bignumExecFuel_loop_step` is hardcoded to `loopBody`, so we
re-instantiate the *same* proof for `loopBodyCmp` (using its straight-line /
non-control facts).  `bignumExecFuel_loop_exit` is already generic over the
body, so it is reused directly. -/

/-- **Forward one-iteration rule** for `loopBodyCmp` — same proof shape as the
    imported `bignumExecFuel_loop_step`, specialised to the compare body. -/
theorem bignumExecFuel_loopCmp_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBodyCmp s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBodyCmp] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBodyCmp] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBodyCmp s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBodyCmp s loopBodyCmp_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBodyCmp [.Cwhile [] cond loopBodyCmp]
        loopBodyCmp_nonControl s s_mid s' hsl hrec]

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

/-! ## §10  Assembly: `MpnCompareJasminRefines`

The full bridge.  `bodyCmp = [result := 0; Cwhile (n != 0) loopBodyCmp]`: the
first instruction zeroes the `result` register, then the loop scans the limb
arrays.  We prove a loop lemma by induction on `as` (lockstep with `bs`), each
step peeling one limb via `bignumExec_loopBodyCmp_step` and
`bignumExecFuel_loopCmp_step`, threading the accumulator via `cmpUpdate`.

Compare only **reads** memory (no stores), so unlike add/sub there is **no**
output buffer, **no** disjointness hypotheses, and **no** memory frame — the
memory is invariant across the whole loop, so the `ap`/`bp` loads on later
iterations stay valid for free. -/

/-- The bridge statement (mirror of `MpnAddNRefinesStmt`, minus the output
    buffer + disjointness).  Starting from a state holding `as` at `ap`, `bs` at
    `bp`, with `n = |as|`, running `mpnCompareFd.body` lands in a state whose
    `result` register holds `mpnCmp as bs 0` — equivalently, whose decoded
    result is `mpnCompare as bs = compare (toNat as) (toNat bs)`. -/
def MpnCompareRefinesStmt : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat),
    as.length = bs.length →
    as.length < 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyCmp s = some s' ∧
      s'.regs "result" = mpnCmp as bs 0

/-- **The loop, by induction on the limb list.**  Running the runtime
    `while (n != 0) { loopBodyCmp }` from a state whose memory holds `as` at
    `ap`, `bs` at `bp`, `result` register `= acc`, and `n = |as|`, lands (with
    `2·|as| + 3` fuel) in a state whose `result` register holds `mpnCmp as bs
    acc`.  No memory frame is needed — `loopBodyCmp` performs no store, so the
    memory is invariant and the `ap`/`bp` loads stay valid across iterations. -/
theorem mpnCmp_loop :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (acc : BitVec 64) (extra : Nat),
      as.length = bs.length →
      as.length < 2 ^ 64 →
      s.regs "result" = acc →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      memHoldsLimbs s.mem (regAddr s "bp") bs →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyCmp] s
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
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodyCmp s
        (evalPExpr_loopCond_false s hn0)
    · rw [hres]; rfl
  | cons a as ih =>
    intro bs s acc extra hlen hwf hres hn hap hbp
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hLsucc : as.length + 1 < 2 ^ 64 := by simpa [List.length_cons] using hwf
      have hwf' : as.length < 2 ^ 64 := by omega
      -- The guard is true: `n = ofNat (L+1) ≠ 0`.
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      -- Head limb loads from `ap`, `bp`.
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      -- Run one iteration of `loopBodyCmp`.
      obtain ⟨s1, hs1, hs1_mem, hs1_res, hs1_ap, hs1_bp, hs1_n⟩ :=
        bignumExec_loopBodyCmp_step s a b hap_head hbp_head
      -- Pointer addresses advance by 8.
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 8 := by
        simp only [regAddr, hs1_bp]; exact regAddr_advance _
      -- Memory unchanged ⇒ the tail loads still hold at the advanced pointers.
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hs1_mem]; exact hap_tail
      have hbp1 : memHoldsLimbs s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hs1_mem]; exact hbp_tail
      -- `result` register after iteration encodes the head update of `acc`.
      have hres1 : s1.regs "result" = cmpUpdate acc a b := by rw [hs1_res, hres]
      -- `n` register after iteration is `ofNat L`.
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      -- Apply the IH on the tail with accumulator `cmpUpdate acc a b`.
      obtain ⟨s', hs', hs'_res⟩ :=
        ih bs s1 (cmpUpdate acc a b) extra hlen' hwf' hres1 hn1 hap1 hbp1
      refine ⟨s', ?_, ?_⟩
      · -- Fuel: `2·(L+1)+3+extra = (2·L+2+extra)+3`; step recurses at
        -- `(2·L+2+extra)+1 = 2·L+3+extra`, matching the IH fuel.
        have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loopCmp_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
          (evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- `result` after the loop: `mpnCmp (a::as) (b::bs) acc`, which unfolds to
        -- `mpnCmp as bs (cmpUpdate acc a b)` — exactly the IH result.
        rw [hs'_res]; rfl

/-- **The bridge, fully proved.**  `mpnCompareFd.body` (the emitted
    `result := 0; while (n != 0) { loopBodyCmp }`) refines the pure reference
    `mpnCmp` over byte memory: starting from a state holding `as` at `ap`, `bs`
    at `bp`, with `n = |as|`, it lands in a state whose `result` register holds
    `mpnCmp as bs 0`.  The `result := 0` prelude sets the initial accumulator to
    "equal"; the loop is then `mpnCmp_loop`.  Decoding the result register with
    `ordOf` gives `mpnCompare as bs = compare (toNat as) (toNat bs)`
    (`mpnCompare_eq_compare`). -/
theorem MpnCompareJasminRefines : MpnCompareRefinesStmt := by
  intro s as bs fuel hlen hwf hn hap hbp hfuel
  -- Step 1: the `result := 0` prelude.  `evalPExpr s (Pconst 0) = 0`, so
  -- `execInstr s (Cassgn result 0) = some (setReg s "result" 0)`; this leaves
  -- memory and the `ap`/`bp`/`n` registers untouched.
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
  -- Transfer the loop preconditions from `s` to `s0`.
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
  -- Step 2: run the loop on `s0` with accumulator `0`.
  obtain ⟨s', hs', hs'_res⟩ :=
    mpnCmp_loop as bs s0 0 extra hlen hwf hres0 hn0' hap0 hbp0
  refine ⟨s', ?_, ?_⟩
  · -- Connect `bodyCmp` at `fuel` to the loop run on `s0`.  The prelude
    -- `result := 0` runs via the straight-line catch-all arm (no fuel drop),
    -- so `bodyCmp` at `fuel` equals the loop `[Cwhile…]` at `fuel` on `s0`.
    obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodyCmp s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyCmp] s0 := by
      conv_lhs => rw [bodyCmp]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · exact hs'_res

/-- **The decoded contract.**  Reading the `result` register of the final state
    with `ordOf` gives the GMP `mpn_cmp` outcome: `compare (toNat as) (toNat
    bs)`.  Combines `MpnCompareJasminRefines` (loop computes `mpnCmp`) with
    `mpnCompare_eq_compare` (the pure spec reflects unsigned `compare`). -/
theorem MpnCompareJasminRefines_ordering
    (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat)
    (hlen : as.length = bs.length) (hwf : as.length < 2 ^ 64)
    (hn : s.regs "n" = BitVec.ofNat 64 as.length)
    (hap : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as)
    (hbp : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs)
    (hfuel : fuel > 2 * as.length + 2) :
    ∃ s', bignumExecFuel emptyRegistry fuel bodyCmp s = some s' ∧
      ordOf (s'.regs "result") = compare (toNat as) (toNat bs) := by
  obtain ⟨s', hs', hs'_res⟩ :=
    MpnCompareJasminRefines s as bs fuel hlen hwf hn hap hbp hfuel
  refine ⟨s', hs', ?_⟩
  rw [hs'_res]
  exact (mpnCompare_eq_compare as bs hlen)

end CatCrypt.Crypto.Jasmin.Examples.MpnComparePrototype
