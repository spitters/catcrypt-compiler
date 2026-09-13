/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit
public import CatCrypt.Crypto.SecureCompilation.BignumSubEmit

/-!
# Composing the emitted 2-limb blocks into a value-level Barrett reduction step

> **`@kat-target`.** Hand-authored leaf blocks + direct `runBlock` proofs — a KAT oracle /
> prototype for the bridge technique, NOT the canonical artifact. New field ops go via the
> golden path (`FieldEmitGoldenPath`); do not extend by hand.

The Barrett field reduction `MultiLimbKernel.barrettReduce x p mu W` reduces a `W`-limb
value modulo `p` by: a multiply + limb-drop (the quotient estimate `q = ⌊x·μ/2^{64W}⌋`), a
truncated multiply + subtract (the residue `r = x − q·p`), and a final conditional
subtract (`condSubLimbs`) that finishes `r ∈ [0, 2p)` to `r mod p`. Its value-correctness
(`barrettReduce_val`) rests on the Barrett quotient-error bracket
`MultiLimbKernel.barrett_bound : q·p ≤ x < (q+2)·p`, which puts `r` in `[0, 2p)`.

This file ties the **emitted x86 blocks** for the two additive tail steps to that List
stack, at the value level, for the 2-limb (128-bit) base case:

* `condSub2Block` (`BignumCondSubEmit`) — the SBB borrow chain + `CMOVcc` select — is the
  emitted **Barrett final reduction step**: `barrettFinalEmit_condSubLimbs` shows its
  `runBlock` output is exactly `bignumVal (condSubLimbs …)`, the verified List kernel, and
  `barrettFinalEmit_mod` reads that as `V mod p`.

* Sequencing an emitted subtract (writing the residue `V − q·p` into the `x` registers)
  into `condSub2Block` realises the Barrett tail `r := x − q·p` then `r mod p`:
  `barrettTailEmit_mod`, proven over `runBlock (l₁ ++ l₂)` via `runBlock_append`. The
  no-borrow hypothesis `q·p ≤ V` is the upper half of the Barrett bracket, and
  `V − q·p < 2p` its lower half — both supplied by `barrett_bound` in the full reduction.

Only the additive (sub / conditional-sub) tail is emitted-and-bridged here; the wide
products (`mulBignum`) are the `emitProductBlock4` / schoolbook kernels and the limb-drop
is `bignumVal_drop` (a reindexing). The arithmetic is kept symbolic in `2^128` and the
Nat-only obligations are discharged by `omega`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.BarrettReduceEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge
open CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit
open CatCrypt.Crypto.SecureCompilation.BignumSubEmit

/-! ## The emitted Barrett final reduction step -/

/-- **The emitted conditional subtract is the verified `condSubLimbs` kernel.** For a
    residue `V = valLimbs[x0,x1]` already in `[0, 2p)`, the emitted `condSub2Block` output
    `[d0, d1]` has the same value as the multi-limb List kernel
    `MultiLimbKernel.condSubLimbs [x0,x1] [p0,p1]`. This names `condSub2Block` as the
    emitted realisation of the Barrett final reduction step. -/
theorem barrettFinalEmit_condSubLimbs (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1"] < 2 * bignumVal [s.get "p0", s.get "p1"]) :
    bignumVal [(runBlock s condSub2Block).get "d0", (runBlock s condSub2Block).get "d1"]
      = bignumVal (condSubLimbs [s.get "x0", s.get "x1"] [s.get "p0", s.get "p1"]) := by
  rw [condSub2_bignumVal s hx,
    condSubLimbs_val [s.get "x0", s.get "x1"] [s.get "p0", s.get "p1"] rfl hx]

/-- **The emitted Barrett final reduction step computes `V mod p`.** Read through
    `condSubLimbs_val`, the same residue the verified List kernel computes. -/
theorem barrettFinalEmit_mod (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1"] < 2 * bignumVal [s.get "p0", s.get "p1"]) :
    bignumVal [(runBlock s condSub2Block).get "d0", (runBlock s condSub2Block).get "d1"]
      = bignumVal [s.get "x0", s.get "x1"] % bignumVal [s.get "p0", s.get "p1"] :=
  condSub2_bignumVal s hx

/-! ## Sequencing the emitted subtract into the conditional subtract: the Barrett tail

The Barrett tail `condSubLimbs (x − q·p) p` first subtracts the truncated product `q·p`
(register names `qp0, qp1`) from the value `x` (in `x0, x1`), in place, leaving the
residue in `x0, x1`; then runs `condSub2Block`. The subtract writes its difference into
the very registers `condSub2Block` reads (`x0, x1`), so the two blocks compose under
`runBlock_append` with no copy. -/

/-- The 2-limb subtract-with-borrow that writes the residue into the `x` registers. The
    `condSub2Block` then reads exactly these. -/
def subIntoXBlock : List (JInstr 64) :=
  [ .sbb "x0" (.reg "qp0"), .sbb "x1" (.reg "qp1") ]

/-- The subtract prefix leaves the `p` registers untouched (they are neither `x0/x1` nor
    written), so `condSub2Block` reads the same modulus afterwards. -/
theorem subIntoX_p0 (s : JState 64) : (runBlock s subIntoXBlock).get "p0" = s.get "p0" := by
  simp only [subIntoXBlock, runBlock_cons, runBlock_nil,
    emit_sbb_other _ "x1" "qp1" "p0" (by decide), emit_sbb_other _ "x0" "qp0" "p0" (by decide)]

theorem subIntoX_p1 (s : JState 64) : (runBlock s subIntoXBlock).get "p1" = s.get "p1" := by
  simp only [subIntoXBlock, runBlock_cons, runBlock_nil,
    emit_sbb_other _ "x1" "qp1" "p1" (by decide), emit_sbb_other _ "x0" "qp0" "p1" (by decide)]

/-- **Identity form of the emitted subtract prefix** (the borrow dual of the add carry
    chain, `BignumSubEmit.sub2sbb_value` for the `x ← x − qp` register layout). With `CF`
    clear on entry, `valLimbs[x0,x1]_out + valLimbs[qp0,qp1] = valLimbs[x0,x1]_in +
    borrow·2^128`. -/
theorem subIntoX_recon (s : JState 64) (hcf : s.flagB (·.cf) = false) :
    valLimbs [(runBlock s subIntoXBlock).get "x0", (runBlock s subIntoXBlock).get "x1"]
        + valLimbs [s.get "qp0", s.get "qp1"]
      = valLimbs [s.get "x0", s.get "x1"]
        + (if (runBlock s subIntoXBlock).flagB (·.cf) then 1 else 0) * 2 ^ 128 := by
  have hrun : runBlock s subIntoXBlock
      = evalInstr (evalInstr s (.sbb "x0" (.reg "qp0"))) (.sbb "x1" (.reg "qp1")) := rfl
  have h1cf : (evalInstr s (.sbb "x0" (.reg "qp0"))).flagB (·.cf)
      = decide ((s.get "x0").toNat < (s.get "qp0").toNat + (BitVec.ofNat 1 0).toNat) := by
    rw [emit_sbb_cf, hcf]; simp
  have h1a1 : (evalInstr s (.sbb "x0" (.reg "qp0"))).get "x1" = s.get "x1" :=
    emit_sbb_other s "x0" "qp0" "x1" (by decide)
  have h1b1 : (evalInstr s (.sbb "x0" (.reg "qp0"))).get "qp1" = s.get "qp1" :=
    emit_sbb_other s "x0" "qp0" "qp1" (by decide)
  set bo0 := borrowOutBit (s.get "x0") (s.get "qp0") (BitVec.ofNat 1 0) with hbo0
  have hbin1 : (BitVec.ofNat 1 (if (evalInstr s (.sbb "x0" (.reg "qp0"))).flagB (·.cf) then 1 else 0))
      = bo0 := by
    rw [h1cf, hbo0, borrowOutBit]; simp only [decide_eq_true_eq]; split_ifs <;> rfl
  have hbin1n : (if (evalInstr s (.sbb "x0" (.reg "qp0"))).flagB (·.cf) then (1 : Nat) else 0)
      = bo0.toNat := by
    rw [h1cf, hbo0, borrowOutBit]; simp only [decide_eq_true_eq]; split_ifs <;> simp
  have ha0 : (runBlock s subIntoXBlock).get "x0"
      = subBorrowWord (s.get "x0") (s.get "qp0") (BitVec.ofNat 1 0) := by
    rw [hrun, emit_sbb_other _ "x1" "qp1" "x0" (by decide), emit_sbb_word, hcf]; simp
  have ha1 : (runBlock s subIntoXBlock).get "x1"
      = subBorrowWord (s.get "x1") (s.get "qp1") bo0 := by
    rw [hrun, emit_sbb_word, h1a1, h1b1, hbin1]
  have hcfout : (runBlock s subIntoXBlock).flagB (·.cf)
      = decide ((s.get "x1").toNat < (s.get "qp1").toNat + bo0.toNat) := by
    rw [hrun, emit_sbb_cf, h1a1, h1b1, hbin1n]
  have hd0 := subb_recon (s.get "x0") (s.get "qp0") (BitVec.ofNat 1 0)
  have hd1 := subb_recon (s.get "x1") (s.get "qp1") bo0
  rw [← hbo0] at hd0
  have hbo1 : (if (runBlock s subIntoXBlock).flagB (·.cf) then (1 : Nat) else 0)
      = (borrowOutBit (s.get "x1") (s.get "qp1") bo0).toNat := by
    rw [hcfout, borrowOutBit]; simp only [decide_eq_true_eq]; split_ifs <;> simp
  have hbo0le : bo0.toNat ≤ 1 := borrowOutBit_le_one _ _ _
  rw [show (BitVec.ofNat 1 0).toNat = 0 from rfl] at hd0
  simp only [valLimbs, mul_zero, add_zero, ha0, ha1]
  rw [hbo1]
  omega

/-- **No-borrow residue.** When the prefix does not borrow out (`q·p ≤ V`, the upper half
    of the Barrett bracket), the `x` registers hold exactly `V − q·p`. -/
theorem subIntoX_value (s : JState 64) (hcf : s.flagB (·.cf) = false)
    (hnb : (runBlock s subIntoXBlock).flagB (·.cf) = false) :
    valLimbs [(runBlock s subIntoXBlock).get "x0", (runBlock s subIntoXBlock).get "x1"]
      = valLimbs [s.get "x0", s.get "x1"] - valLimbs [s.get "qp0", s.get "qp1"] := by
  have h := subIntoX_recon s hcf
  rw [hnb] at h
  simp only [Bool.false_eq_true, if_false, Nat.zero_mul, add_zero] at h
  omega

/-! ## The emitted Barrett tail: subtract then conditional subtract -/

/-- The emitted Barrett tail block: subtract the truncated product `q·p` (in `qp0, qp1`)
    from the value (in `x0, x1`), then run the conditional subtract reading `x0, x1`. -/
def barrettTailBlock : List (JInstr 64) := subIntoXBlock ++ condSub2Block

/-- **The emitted Barrett tail computes `(V − q·p) mod p`.** Sequencing the emitted
    subtract into `condSub2Block` over `runBlock (l₁ ++ l₂)` (via `runBlock_append`)
    realises the additive tail of `MultiLimbKernel.barrettReduce` at the 2-limb base case:
    with `CF` clear, no borrow out of the subtract (`q·p ≤ V`, the Barrett upper bound) and
    the residue in range (`V − q·p < 2p`, the Barrett lower bound), the output limbs
    `d0, d1` hold `(bignumVal[x0,x1] − bignumVal[qp0,qp1]) mod bignumVal[p0,p1]`. -/
theorem barrettTailEmit_mod (s : JState 64) (hcf : s.flagB (·.cf) = false)
    (hnb : (runBlock s subIntoXBlock).flagB (·.cf) = false)
    (hrange : valLimbs [s.get "x0", s.get "x1"] - valLimbs [s.get "qp0", s.get "qp1"]
        < 2 * valLimbs [s.get "p0", s.get "p1"]) :
    bignumVal [(runBlock s barrettTailBlock).get "d0", (runBlock s barrettTailBlock).get "d1"]
      = (bignumVal [s.get "x0", s.get "x1"] - bignumVal [s.get "qp0", s.get "qp1"])
          % bignumVal [s.get "p0", s.get "p1"] := by
  -- run the subtract prefix, then read off the mid-state.
  rw [barrettTailBlock, runBlock_append]
  set s' := runBlock s subIntoXBlock with hs'
  -- the mid-state's value (residue) and untouched modulus
  have hxv : valLimbs [s'.get "x0", s'.get "x1"]
      = valLimbs [s.get "x0", s.get "x1"] - valLimbs [s.get "qp0", s.get "qp1"] :=
    subIntoX_value s hcf hnb
  have hp0 : s'.get "p0" = s.get "p0" := subIntoX_p0 s
  have hp1 : s'.get "p1" = s.get "p1" := subIntoX_p1 s
  -- condSub2 hypothesis on the mid-state, in bignumVal terms
  have hmid : bignumVal [s'.get "x0", s'.get "x1"] < 2 * bignumVal [s'.get "p0", s'.get "p1"] := by
    rw [← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal, hxv, hp0, hp1]
    exact hrange
  -- apply the emitted conditional subtract on the mid-state.
  rw [condSub2_bignumVal s' hmid, ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal,
    ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal, hxv, hp0, hp1,
    valLimbs_eq_bignumVal, valLimbs_eq_bignumVal, valLimbs_eq_bignumVal]

end CatCrypt.Crypto.SecureCompilation.BarrettReduceEmit
