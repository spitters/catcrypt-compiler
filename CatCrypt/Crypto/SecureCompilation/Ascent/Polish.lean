/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Strengthen
public import CatCrypt.Crypto.SecureCompilation.Ascent.LegWeldDemo
public import CatCrypt.Crypto.SecureCompilation.Ascent.SelectLeaf

/-!
# Readable abstract programs of the demonstration kernels

For fourteen `LowCT` kernels of the ascent demonstrations, listed in the table, this
module states the abstract program the total abstraction `ascendG` produces as a Lean
definition written over the store updates `setLit` and `setVal`, and proves that the
transformer component of `ascendG` equals it. Where the guard list is not empty, a
second theorem states what the guards mean on a store. The equations are `rfl`; the
guard statements are closed by `simp`. No statement evaluates a kernel at a concrete
store. The demonstration kernels `keccakRoundBody` (`AscendMeta`), `condBranchKernel`
(`CondKernelCapstone`) and `searchLowCT` (`Demos/EarlyExitLowCT`) are not covered.

| kernel | module | abstract program | guards |
|---|---|---|---|
| `arithK` | `Demos/Decide` | `arithKAbs` | none |
| `bitK` | `Demos/Decide` | `bitKAbs` | two range guards, true on every store |
| `qrFrag` | `Demos/Scalar` | `qrFragAbs` | `qrFragGuard`: `d <<< 16` does not wrap |
| `qrClosed` | `Demos/Scalar` | `qrClosedAbs` | `qrFragGuard` after the literal writes |
| `feSubC` | `FeSubEndToEnd` | `feSubCAbs` | none |
| `feAddC` | `FeAddEndToEnd` | `feAddCAbs` | none |
| `demoC` | `LegWeldDemo` | `demoCAbs` | none |
| `avgK` | `Guards` | `avgKAbs` | `a + 6 < 2 ^ 64` |
| `sumK` | `Guards` | `sumKAbs` | none |
| `ctSelectStep1` | `SelectLeaf` | `ctSelectStep1Abs` | one range guard, true on every store |
| `ctSelectStep2` | `SelectLeaf` | `ctSelectStep2Abs` | one range guard, true on every store |
| `ctSelectChain` | `SelectLeaf` | `ctSelectChainAbs` | two range guards, true on every store |
| `countdownK` | `Demos/Strengthen` | `countdownKAbs` | the loop halts within the fuel |
| `mergeK` | `Demos/Strengthen` | the identity | `Guard.unsupported "RIfNz"` |

For `mergeK` the theorem states the whole `ascendG` output: the unsupported guard and
the identity transformer, so no abstract program is claimed for it.

## Main definitions

* `arithKAbs`, `bitKAbs`, `qrFragAbs`, `qrClosedAbs`, `feSubCAbs`, `feAddCAbs`,
  `demoCAbs`, `avgKAbs`, `sumKAbs`, `ctSelectStep1Abs`, `ctSelectStep2Abs`,
  `ctSelectChainAbs`, `countdownKAbs`: the abstract programs
* `qrFragGuard`, `avgKGuard`: the guards as propositions on the entry store

## Main results

* `arithK_ascendG`, `feSubC_ascendG`, `feAddC_ascendG`, `demoC_ascendG`,
  `sumK_ascendG`: `ascendG` returns the empty guard list and the abstract program
* `mergeK_ascendG`: `ascendG` returns the unsupported guard and the identity
* `bitK_ascendG_prog`, `qrFrag_ascendG_prog`, `qrClosed_ascendG_prog`,
  `avgK_ascendG_prog`, `ctSelectStep1_ascendG_prog`, `ctSelectStep2_ascendG_prog`,
  `ctSelectChain_ascendG_prog`, `countdownK_ascendG_prog`: the transformer component
  `.2` of the `ascendG` output is the abstract program
* `bitK_guardsHold`, `ctSelectStep1_guardsHold`, `ctSelectStep2_guardsHold`,
  `ctSelectChain_guardsHold`: the guards hold on every store
* `qrFrag_guardsHold_iff`, `qrClosed_guardsHold_iff`, `avgK_guardsHold_iff`,
  `countdownK_guardsHold_iff`: the guards hold exactly when the stated proposition does
* `feSubCAbs_r0`, `feAddCAbs_r0`, `demoCAbs_r0`, `sumKAbs_acc`: the value each
  abstract program leaves at its output name
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos

/-! ## Straight-line arithmetic kernels -/

/-- The abstract program of `arithK`: `t := a + b; r := t * c` in `ZMod 2^64`. -/
def arithKAbs (a : AField) : AField :=
  let a := setVal "t" (a "a" + a "b") a
  setVal "r" (a "t" * a "c") a

theorem arithK_ascendG (fuel : Nat) : ascendG fuel arithK = ([], arithKAbs) := rfl

/-- The abstract program of `feSubC`: `a0 := av; b0 := bv; r0 := a0 - b0`. -/
def feSubCAbs (a : AField) : AField :=
  let a := setLit "a0" av a
  let a := setLit "b0" bv a
  setVal "r0" (a "a0" - a "b0") a

theorem feSubC_ascendG (fuel : Nat) : ascendG fuel feSubC = ([], feSubCAbs) := rfl

theorem feSubCAbs_r0 (a : AField) :
    feSubCAbs a "r0" = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  simp [feSubCAbs, setLit, setVal]

/-- The abstract program of `feAddC`: `a0 := av; b0 := bv; r0 := a0 + b0`. -/
def feAddCAbs (a : AField) : AField :=
  let a := setLit "a0" av a
  let a := setLit "b0" bv a
  setVal "r0" (a "a0" + a "b0") a

theorem feAddC_ascendG (fuel : Nat) : ascendG fuel feAddC = ([], feAddCAbs) := rfl

theorem feAddCAbs_r0 (a : AField) :
    feAddCAbs a "r0" = ((av : Nat) : ZMod (2 ^ 64)) + ((bv : Nat) : ZMod (2 ^ 64)) := by
  simp [feAddCAbs, setLit, setVal]

/-- The abstract program of `demoC`: `a0 := dav; b0 := dbv; c0 := dcv;
    r0 := a0 + b0 - c0`. -/
def demoCAbs (a : AField) : AField :=
  let a := setVal "a0" ((dav : Nat) : ZMod (2 ^ 64)) a
  let a := setVal "b0" ((dbv : Nat) : ZMod (2 ^ 64)) a
  let a := setVal "c0" ((dcv : Nat) : ZMod (2 ^ 64)) a
  setVal "r0" (a "a0" + a "b0" - a "c0") a

theorem demoC_ascendG (fuel : Nat) : ascendG fuel demoC = ([], demoCAbs) := rfl

theorem demoCAbs_r0 (a : AField) :
    demoCAbs a "r0" = ((dav : Nat) : ZMod (2 ^ 64)) + ((dbv : Nat) : ZMod (2 ^ 64))
      - ((dcv : Nat) : ZMod (2 ^ 64)) := by
  simp [demoCAbs, setVal]

/-! ## Kernels with range guards -/

/-- The abstract program of `bitK`: `d := d ^^^ a; b := (b &&& c) >>> 7`, each over
    the canonical residues. -/
def bitKAbs (a : AField) : AField :=
  let a := setVal "d" (((a "d").val ^^^ (a "a").val : Nat) : ZMod (2 ^ 64)) a
  setVal "b" ((((a "b").val &&& (a "c").val) >>> 7 : Nat) : ZMod (2 ^ 64)) a

theorem bitK_ascendG_prog (fuel : Nat) : (ascendG fuel bitK).2 = bitKAbs := rfl

theorem bitK_guardsHold (fuel : Nat) (a : AField) : guardsHold (ascendG fuel bitK).1 a := by
  intro g hg
  simp only [show (ascendG fuel bitK).1 =
      [Guard.range "d" (.SXor (.SVar "d") (.SVar "a")),
        Guard.after (fun a => setVal "d" (natEval (.SXor (.SVar "d") (.SVar "a")) a) a)
          (Guard.range "b" (.SShr (.SAnd (.SVar "b") (.SVar "c")) (.SLit 7)))] from rfl,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    simp [Guard.holds, SExpr.inRange, SExpr.eval, natStore, ZMod.val_lt]

/-- The abstract program of `qrFrag`: `a := a + b` in `ZMod 2^64`, then
    `d := d ^^^ a` and `d := d <<< 16` over the canonical residues. -/
def qrFragAbs (a : AField) : AField :=
  let a := setVal "a" (a "a" + a "b") a
  let a := setVal "d" (((a "d").val ^^^ (a "a").val : Nat) : ZMod (2 ^ 64)) a
  setVal "d" (((a "d").val <<< 16 : Nat) : ZMod (2 ^ 64)) a

/-- The guard of `qrFrag`: after the first two steps, `d <<< 16` stays below `2^64`. -/
def qrFragGuard (a : AField) : Prop :=
  let a := setVal "a" (a "a" + a "b") a
  let a := setVal "d" (((a "d").val ^^^ (a "a").val : Nat) : ZMod (2 ^ 64)) a
  (a "d").val <<< 16 < 2 ^ 64

theorem qrFrag_ascendG_prog (fuel : Nat) : (ascendG fuel qrFrag).2 = qrFragAbs := rfl

theorem qrFrag_guardsHold_iff (fuel : Nat) (a : AField) :
    guardsHold (ascendG fuel qrFrag).1 a ↔ qrFragGuard a := by
  simp only [show (ascendG fuel qrFrag).1 =
      [Guard.after (fun a => setVal "a" (evalZMod a (.SAdd (.SVar "a") (.SVar "b"))) a)
          (Guard.range "d" (.SXor (.SVar "d") (.SVar "a"))),
        Guard.after (fun a => setVal "a" (evalZMod a (.SAdd (.SVar "a") (.SVar "b"))) a)
          (Guard.after (fun a => setVal "d" (natEval (.SXor (.SVar "d") (.SVar "a")) a) a)
            (Guard.range "d" (.SShl (.SVar "d") (.SLit 16))))] from rfl]
  simp [guardsHold, qrFragGuard, Guard.holds, SExpr.inRange, natStore, natEval, evalZMod,
    SExpr.eval, ZMod.val_lt]

/-- The abstract program of `qrClosed`: the literal writes `a := 1`, `b := 2`,
    `d := 5`, then `qrFragAbs`. -/
def qrClosedAbs (a : AField) : AField :=
  qrFragAbs (setLit "d" 5 (setLit "b" 2 (setLit "a" 1 a)))

theorem qrClosed_ascendG_prog (fuel : Nat) : (ascendG fuel qrClosed).2 = qrClosedAbs := rfl

theorem qrClosed_guardsHold_iff (fuel : Nat) (a : AField) :
    guardsHold (ascendG fuel qrClosed).1 a ↔
      qrFragGuard (setLit "d" 5 (setLit "b" 2 (setLit "a" 1 a))) := by
  have h : (ascendG fuel qrClosed).1 = (ascendG fuel qrFrag).1.map
      (fun g => Guard.after (setLit "a" 1) (Guard.after (setLit "b" 2)
        (Guard.after (setLit "d" 5) g))) := rfl
  rw [h, ← qrFrag_guardsHold_iff fuel]
  simp [guardsHold, Guard.holds]

/-- The abstract program of `ctSelectStep1`: `d := x ^^^ y` over the canonical
    residues. -/
def ctSelectStep1Abs (a : AField) : AField :=
  setVal "d" (((a "x").val ^^^ (a "y").val : Nat) : ZMod (2 ^ 64)) a

/-- The abstract program of `ctSelectStep2`: `r := y ^^^ (d &&& m)` over the canonical
    residues. -/
def ctSelectStep2Abs (a : AField) : AField :=
  setVal "r" (((a "y").val ^^^ ((a "d").val &&& (a "m").val) : Nat) : ZMod (2 ^ 64)) a

/-- The abstract program of `ctSelectChain`: `ctSelectStep1Abs`, then
    `ctSelectStep2Abs`. -/
def ctSelectChainAbs (a : AField) : AField :=
  ctSelectStep2Abs (ctSelectStep1Abs a)

theorem ctSelectStep1_ascendG_prog (fuel : Nat) :
    (ascendG fuel ctSelectStep1).2 = ctSelectStep1Abs := rfl

theorem ctSelectStep2_ascendG_prog (fuel : Nat) :
    (ascendG fuel ctSelectStep2).2 = ctSelectStep2Abs := rfl

theorem ctSelectChain_ascendG_prog (fuel : Nat) :
    (ascendG fuel ctSelectChain).2 = ctSelectChainAbs := rfl

theorem ctSelectChain_guardsHold (fuel : Nat) (a : AField) :
    guardsHold (ascendG fuel ctSelectChain).1 a := by
  intro g hg
  simp only [show (ascendG fuel ctSelectChain).1 =
      [Guard.range "d" (.SXor (.SVar "x") (.SVar "y")),
        Guard.after (fun a => setVal "d" (natEval (.SXor (.SVar "x") (.SVar "y")) a) a)
          (Guard.range "r" (.SXor (.SVar "y") (.SAnd (.SVar "d") (.SVar "m"))))] from rfl,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    simp [Guard.holds, SExpr.inRange, natStore, ZMod.val_lt]

theorem ctSelectStep1_guardsHold (fuel : Nat) (a : AField) :
    guardsHold (ascendG fuel ctSelectStep1).1 a := by
  intro g hg
  simp only [show (ascendG fuel ctSelectStep1).1 =
      [Guard.range "d" (.SXor (.SVar "x") (.SVar "y"))] from rfl,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  simp [Guard.holds, SExpr.inRange, natStore, ZMod.val_lt]

theorem ctSelectStep2_guardsHold (fuel : Nat) (a : AField) :
    guardsHold (ascendG fuel ctSelectStep2).1 a := by
  intro g hg
  simp only [show (ascendG fuel ctSelectStep2).1 =
      [Guard.range "r" (.SXor (.SVar "y") (.SAnd (.SVar "d") (.SVar "m")))] from rfl,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  simp [Guard.holds, SExpr.inRange, natStore, ZMod.val_lt]

/-- The abstract program of `avgK`: `b := 6; r := (a + b) >>> 1` over the canonical
    residues. -/
def avgKAbs (a : AField) : AField :=
  let a := setLit "b" 6 a
  setVal "r" ((((a "a").val + (a "b").val) >>> 1 : Nat) : ZMod (2 ^ 64)) a

/-- The guard of `avgK`: `a + 6` stays below `2^64`. -/
def avgKGuard (a : AField) : Prop := (a "a").val + 6 < 2 ^ 64

theorem avgK_ascendG_prog (fuel : Nat) : (ascendG fuel avgK).2 = avgKAbs := rfl

theorem avgK_guardsHold_iff (fuel : Nat) (a : AField) :
    guardsHold (ascendG fuel avgK).1 a ↔ avgKGuard a := by
  simp only [show (ascendG fuel avgK).1 =
      [Guard.after (setLit "b" 6)
        (Guard.range "r" (.SShr (.SAdd (.SVar "a") (.SVar "b")) (.SLit 1)))] from rfl]
  have h6 : (6 : ZMod (2 ^ 64)).val = 6 := by
    rw [show (6 : ZMod (2 ^ 64)) = ((6 : Nat) : ZMod (2 ^ 64)) by norm_num, ZMod.val_natCast]
    norm_num
  simp [guardsHold, avgKGuard, Guard.holds, SExpr.inRange, natStore, setLit, SExpr.eval,
    ZMod.val_lt, h6]

/-! ## Loops and an unsupported node -/

/-- The abstract program of `sumK`: four trips of `acc := acc + i`, the counter set to
    the trip index before each trip. -/
def sumKAbs : AField → AField :=
  forFold (setLit "i") (fun a => setVal "acc" (a "acc" + a "i") a) 4

theorem sumK_ascendG (fuel : Nat) : ascendG fuel sumK = ([], sumKAbs) := rfl

theorem sumKAbs_acc (a : AField) : sumKAbs a "acc" = a "acc" + 6 := by
  simp [sumKAbs, forFold, setLit, setVal]
  ring

/-- The abstract program of `countdownK`: the fuel-bounded do-while on `n` whose body
    is `n := n - 1`. -/
def countdownKAbs (fuel : Nat) : AField → AField :=
  awhile (nzB "n") (fun a => setVal "n" (a "n" - ((1 : Nat) : ZMod (2 ^ 64))) a) fuel

theorem countdownK_ascendG_prog (fuel : Nat) :
    (ascendG fuel countdownK).2 = countdownKAbs fuel := rfl

theorem countdownK_guardsHold_iff (fuel : Nat) (a : AField) :
    guardsHold (ascendG fuel countdownK).1 a ↔
      ahalts (nzB "n") (fun a => setVal "n" (a "n" - ((1 : Nat) : ZMod (2 ^ 64))) a) fuel a := by
  simp only [show (ascendG fuel countdownK).1 =
      [Guard.loopHalts "n" fuel
        (fun a => setVal "n" (a "n" - ((1 : Nat) : ZMod (2 ^ 64))) a)] from rfl]
  simp [guardsHold, Guard.holds]

/-- `mergeK` writes two different names, so `ascendG` returns the identity under the
    unsupported guard. -/
theorem mergeK_ascendG (fuel : Nat) :
    ascendG fuel mergeK = ([Guard.unsupported "RIfNz"], id) := rfl

end CatCrypt.Crypto.SecureCompilation.Ascent
