/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import Mathlib.Data.ZMod.Basic
public import Std.Tactic.BVDecide

/-!
# The OWNED `csub` lane reduction from `BitVec 64` lanes to `ZMod P` (model-free)

The OWNED (jasminc-free) packed conditional-subtract block computes, per lane,
the branch-free `r = (x − P) + ((x − P) >>>ₐ 63 & P)` over `BitVec 64`
arithmetic (mod 2⁶⁴, the AVX-512 ZMM lane ring).  This module is the
**model-free** lane-level reduction bridge for that scalar lane function — it is
pure `BitVec 64 → ZMod P` number theory, with no machine semantics
(`runZBlock`/`ZInstr`) in the import set.

The abstract ML-KEM / BabyBear field specs live in `ZMod P` (`ZMod 3329`,
`ZMod 2013265921`, …).  This module discharges the `BitVec 64`→`ZMod P`
reduction bridge for the `csub` reduce family.  We prove: for a lane value `x`
with `x.toNat < 2·P` (the csub algorithm's domain — a single conditional
subtract canonicalizes inputs already in `[0, 2P)`), the owned csub lane output,
cast to `ZMod P`, equals the input's residue and is the canonical
representative:

* `csubLane_toNat` — the exact `Nat` value of the lane: `if x.toNat < P then
  x.toNat else x.toNat − P`.
* `csubLane_lt` — the output is `< P` (canonical).
* `csubLane_zmod` — `((csubLane x p).toNat : ZMod P) = (x.toNat : ZMod P)` —
  the residue is preserved.

These three lane facts are consumed by the unified-`Com jasminDialect`
re-anchoring `VIR/MlkemMontRedcAbstractCom.lean` (the Montgomery REDC
chain over `zmmPackQ`); being pure `BitVec`/`Nat`/`ZMod`, they transfer
unchanged to that model-free denotation.

## Scope — what this is and is NOT

The single conditional subtract only canonicalizes inputs **already in `[0, 2P)`**
(it does *one* subtraction, mapping `[P, 2P) → [0, P)` and fixing `[0, P)`).  The
precondition `x.toNat < 2·P` is the csub algorithm's domain — it is **not** a
kernel hypothesis we can drop.  We do **NOT** claim csub reduces an arbitrary
`BitVec 64` value (`[0, 2⁶⁴)`) mod `P`; that needs a Barrett or Montgomery
reduction (a different kernel), which folds the wide product down to `[0, 2P)`
*before* this csub canonicalizes.  The remaining gap from `[0, 2⁶⁴)` to `[0, 2P)`
is therefore explicitly out of scope here (residual: full-range reduction).

The other precondition, `2·P ≤ 2⁶³`, ensures the `csub` sign-bit test
(`>>>ₐ 63`) correctly detects the `x < P` underflow: with `x < 2P ≤ 2⁶³` and
`P ≤ 2⁶³`, `x − P` (mod 2⁶⁴) has its top bit set **iff** `x < P`.  Both ML-KEM
(`P = 3329`) and BabyBear (`P = 2013265921 < 2³¹`) satisfy `2P ≤ 2⁶³` with
enormous margin.

These facts are pure `BitVec`/`Nat`/`ZMod` number theory — no machine model,
no jasminc, no `jasminc_preserves_ct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ReduceZModTie

/-! ## §1  The per-lane csub scalar function -/

/-- The per-lane scalar csub expression: `t = x − p`, then `t + ((t >>>ₐ 63) & p)`.
    This is the owned block's spec evaluated at a single lane (its
    lane-projection). -/
def csubLane (x p : BitVec 64) : BitVec 64 :=
  let t := x - p
  t + (BitVec.sshiftRight t 63 &&& p)

/-! ## §2  The branch-free mask and the case split -/

/-- The `csub` mask: `(t >>>ₐ 63) & p` is `p` exactly when `t`'s sign bit is set,
    else `0`.  `>>>ₐ 63` broadcasts `t.msb` to all 64 bits; ANDing with `p` then
    selects `p` (msb set) or `0` (msb clear). -/
theorem csub_mask (t p : BitVec 64) :
    BitVec.sshiftRight t 63 &&& p = if t.msb then p else 0 := by
  rcases hm : t.msb with _ | _ <;>
    [rw [BitVec.sshiftRight_eq_of_msb_false hm]; rw [BitVec.sshiftRight_eq_of_msb_true hm]] <;>
    bv_decide

/-- `csubLane` as a branch: `x` when `(x − p)`'s sign bit is set (the `x < P`
    underflow case, where the mask adds `p` back: `(x − p) + p = x`), else `x − p`
    (the `x ≥ P` case). -/
theorem csubLane_branch (x p : BitVec 64) :
    csubLane x p = if (x - p).msb then x else (x - p) := by
  simp only [csubLane, csub_mask]
  rcases hm : (x - p).msb with _ | _ <;>
    simp only [if_false, if_true, Bool.false_eq_true] <;>
    [bv_decide; rw [BitVec.sub_add_cancel]]

/-! ## §3  The reduction-correctness facts on the csub domain `[0, 2P)`

The two preconditions are the csub algorithm's domain (`hx2 : x.toNat < 2·P`) and
the sign-test validity bound (`hP : 2·P ≤ 2⁶³`).  Under these, the sign bit of
`x − p` (mod 2⁶⁴) is set **iff** `x.toNat < P`, so the branch in `csubLane_branch`
realizes the conditional subtract exactly. -/

/-- On the csub domain, the sign bit `(x − p).msb` is set **iff** `x.toNat < P`.
    (`msb` of a `BitVec 64` is `toNat ≥ 2⁶³`.)  When `x ≥ P`: `x − p = x.toNat − P
    < P ≤ 2⁶³` (no underflow, top bit clear).  When `x < P`: `x − p = 2⁶⁴ + x.toNat
    − P > 2⁶⁴ − 2⁶³ = 2⁶³` (wrap, top bit set). -/
theorem csub_msb_iff (x p : BitVec 64) (P : Nat) (hp : p.toNat = P)
    (hP : 2 * P ≤ 2 ^ 63) (hx2 : x.toNat < 2 * P) :
    (x - p).msb = decide (x.toNat < P) := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
  subst hp
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hpw : p.toNat ≤ 2 ^ 64 := le_of_lt p.isLt
  rw [decide_eq_decide]
  by_cases hlt : x.toNat < p.toNat
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show 2 ^ 64 - p.toNat + x.toNat = 2 ^ 64 + (x.toNat - p.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The exact lane value on the csub domain.**  `(csubLane x p).toNat` is
    `x.toNat` when `x.toNat < P` (already canonical) and `x.toNat − P` otherwise
    (one subtraction).  This is the conditional-subtract specification, read at
    the `Nat` level. -/
theorem csubLane_toNat (x p : BitVec 64) (P : Nat) (hp : p.toNat = P)
    (hP : 2 * P ≤ 2 ^ 63) (hx2 : x.toNat < 2 * P) :
    (csubLane x p).toNat = if x.toNat < P then x.toNat else x.toNat - P := by
  rw [csubLane_branch, csub_msb_iff x p P hp hP hx2]
  by_cases hlt : x.toNat < P
  · simp only [hlt, decide_true, if_true]
  · simp only [hlt, decide_false, if_false, Bool.false_eq_true]
    rw [BitVec.toNat_sub]
    subst hp
    have hpw : p.toNat ≤ 2 ^ 64 := le_of_lt p.isLt
    rw [show 2 ^ 64 - p.toNat + x.toNat = 2 ^ 64 + (x.toNat - p.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- **Canonicality.**  On the csub domain the lane output is `< P` — the canonical
    representative of its residue class. -/
theorem csubLane_lt (x p : BitVec 64) (P : Nat) (hp : p.toNat = P)
    (hP : 2 * P ≤ 2 ^ 63) (hx2 : x.toNat < 2 * P) :
    (csubLane x p).toNat < P := by
  rw [csubLane_toNat x p P hp hP hx2]
  by_cases hlt : x.toNat < P
  · simp only [hlt, if_true]
  · simp only [hlt, if_false]; omega

/-- **Residue preservation in `ZMod P`.**  The owned csub lane output, cast to
    `ZMod P`, equals the input lane's residue: the subtraction of `P` (in the
    `x ≥ P` branch) is invisible mod `P`. -/
theorem csubLane_zmod (x p : BitVec 64) (P : Nat) (hp : p.toNat = P)
    (hP : 2 * P ≤ 2 ^ 63) (hx2 : x.toNat < 2 * P) :
    ((csubLane x p).toNat : ZMod P) = (x.toNat : ZMod P) := by
  rw [csubLane_toNat x p P hp hP hx2]
  by_cases hlt : x.toNat < P
  · simp only [hlt, if_true]
  · simp only [hlt, if_false]
    rw [Nat.not_lt] at hlt
    have : x.toNat = (x.toNat - P) + P := by omega
    rw [this, Nat.cast_add]
    simp only [ZMod.natCast_self, add_zero]
    congr 1
    omega

end CatCrypt.Crypto.SecureCompilation.X86Backend.ReduceZModTie
