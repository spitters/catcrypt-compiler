/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Hax.RustSubsetToLowCT
public import CatCrypt.Crypto.Hax.RustSubsetToLowCT
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.KeystoneControl
public import CatCrypt.Crypto.SecureCompilation.Ascent.KeystoneControl

/-!
# Closing the loop source-preimage gap: a `RustSrc.forN` kernel welded to `corres_for`

`LoopSourceTower.lean` recorded a *wall*: no source construct in the hax
`ImpExpr` / `haxToLowCT` front reaches the bounded-loop ascent leaf `corres_for`
(the `RFor` arm) with a **defined** evaluation.  Its two witnesses:

* `ImpExpr.forFold` lowers to `RFor` but `evalImp (.forFold …) = none`
  (`loop_forFold_source_vacuous`), and
* `ImpExpr.whileLoop` evaluates but lowers to `RWhileNz`, which `semScalar` (and
  hence `Corres`) does not interpret.

That wall is real *for the `haxToLowCT` front only*.  The **other** verified
source front — `RustSubsetToLowCT`, the `RustSrc`/`lower`/`lowerRefines` layer the
straight-line feSub tower (`FeSubSourceTower.lean`) already welds through — carries
a bounded counted-loop constructor `RustSrc.forN` that

* **(a)** has a **total, defined** evaluation `RustSrc.exec` (a state transformer,
  not a post-phase `none`), and
* **(b)** lowers to a genuine `RFor` node: `lower (.forN x n body) = RFor x n
  (lower body)` — the exact arm `corres_for` / `keystone_for` handle.

So the source preimage the loop tower lacked exists; it just lives on the
`RustSrc` front, which `LoopSourceTower` did not examine.  This module deploys it
on a concrete fixed-trip-count copy loop

```rust
// loopSrc v n  (RustSrc):
for i in 0..n { o = v; i = 0; }
```

and delivers, on the *same* lowered `RFor` image `lower (loopSrc v n)`, both legs:

* **Source → LowCT (the descent / `RustExec` leg).**  `loopSrc_refines` is
  `RRefines (RustSrc.exec (loopSrc v n)) (lower (loopSrc v n))` via `lowerRefines`
  — the loop analogue of `feSubSrc_refines`, now over a `forN`/`RFor` body.
* **LowCT → clean spec (the ascent / `semScalar` leg).**  `loopSrc_corres` welds
  `corres_for`: the lowered `RFor` image `Corres`-refines the `n`-fold iteration
  `nfold (loopSrcStep v) n` of the counter-independent loop-invariant step.  The
  per-trip body leaf is assembled from `corres_setScalar_NT` (counter bind) and
  two `corres_setExpr`s (the `RScalarSetExpr` writes `lower` actually emits),
  re-based to the fixed step by `corres_fa_congr` — the same discipline
  `keystone_for` uses, but consuming `lower`'s real `RScalarSetExpr` output rather
  than the hand-written `RScalarSet` closed kernel.

`loopSrc_source_preimage` bundles the two legs plus the `RFor`-headed shape as one
statement: the source-preimage gap for a bounded counted loop is closed on the
`RustSubsetToLowCT` front.

## Residual (honest)

The two legs are two *denotations* of the one lowered `RFor` node: `RRefines` is
over `RustExec` (the abstract result `RustSrc.exec`, in `Nat`), `Corres` is over
`semScalar` (the abstract result `nfold (loopSrcStep v) n`, in `ZMod 2^64`).  They are
consistent through the `RustExec ↔ semScalar` bridge (`RustExecSemScalarBridge`);
fusing them into a *single* `RustSrc.exec`-indexed emit conclusion (the loop twin
of the `FeSub` capstone, via `keystone_for`) is the next step and is not attempted
here — `keystone_for` is stated over the `RScalarSet` closed kernel, so the fusion
needs a `keystone` instance over the `RScalarSetExpr` loop body.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Hax.RustSubsetToLowCT (RustSrc lower RRefines lowerRefines)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## §1  The concrete bounded counted-loop source kernel and its `RFor` image -/

/-- The loop body: `o = v; i = 0;` — write the literal `v` to output `o`, then
    reset the counter `i`.  The counter reset is what makes the loop-invariant
    abstract step counter-independent (as in `keystone_for`'s `forClosedKernel`),
    but here every write is a `RustSrc.assign`, so `lower` emits `RScalarSetExpr`
    (not the hand-written `RScalarSet`). -/
def loopBodySrc (v : Nat) : RustSrc :=
  .seq (.assign "o" (.SLit v)) (.assign "i" (.SLit 0))

/-- The bounded counted-loop source kernel `for i in 0..n { o = v; i = 0; }`. -/
def loopSrc (v n : Nat) : RustSrc :=
  .forN "i" n (loopBodySrc v)

/-- **The source lowering reaches the `RFor` ascent arm.**  `lower` sends the
    `forN` source loop to a genuine `RFor` node — the arm `corres_for` handles.
    (Definitional; the point is that a source construct with a *defined* `exec`
    lands here, unlike `forFold`.) -/
theorem loopSrc_lower (v n : Nat) :
    lower (loopSrc v n) = .RFor "i" n (lower (loopBodySrc v)) := rfl

/-- The source kernel is in the `if`-free fragment `lowerRefines` covers. -/
theorem loopSrc_ifFree (v n : Nat) : (loopSrc v n).ifFree = true := by
  simp [loopSrc, loopBodySrc, RustSrc.ifFree]

/-- **The source evaluation is defined and non-vacuous.**  Unlike `forFold`
    (`evalImp = none`), `RustSrc.exec` is a total state transformer: three trips of
    `loopSrc 7 3` leave the output slot `o` holding `7`. -/
example : RustSrc.exec (loopSrc 7 3) (fun _ => 0) "o" = 7 := by native_decide

/-! ## §2  Source → LowCT: the `RustExec` refinement leg (via `lowerRefines`) -/

/-- **`loopSrc_refines`.**  The lowered `RFor` image denotes the source loop's
    semantics under `RustExec`, assembled through `RustSubsetToLowCT`'s
    relational-compilation lemmas (`lowerRefines`, whose `forN` arm is the bounded
    `RustExec.forSucc`/`forZero` fold).  The loop/`RFor` analogue of the
    straight-line `feSubSrc_refines`. -/
theorem loopSrc_refines (v n : Nat) :
    RRefines (RustSrc.exec (loopSrc v n)) (lower (loopSrc v n)) :=
  lowerRefines (loopSrc v n) (loopSrc_ifFree v n)

/-! ## §3  LowCT → clean spec: welding `corres_for` (the ascent leg) -/

/-- The counter-independent loop-invariant abstract step: reset `i := 0`, set
    `o := v`.  (The `keystone_for.forStep` analogue for this kernel.) -/
def loopSrcStep (v : Nat) : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)) :=
  fun a s => if s = "i" then 0 else if s = "o" then (v : ZMod (2 ^ 64)) else a s

/-- **The per-trip body leaf.**  The counter-bound body `RSeq (RScalarSet i m)
    (lower (loopBodySrc v))` realizes the fixed step `loopSrcStep v` — independent of
    the trip index `m`, because the body's `i := 0` reset overwrites the counter.
    Glued from `corres_setScalar_NT` (counter bind) and two `corres_setExpr`s (the
    `RScalarSetExpr` writes `lower` emits), re-based by `corres_fa_congr`. -/
theorem loopBody_corres (v : Nat) (hv : v < 2 ^ 64) (m : Nat) :
    Corres SRwordNT (fun _ => True) (loopSrcStep v)
      (.RSeq (.RScalarSet "i" m) (lower (loopBodySrc v))) := by
  have hstep :=
    corres_seq (SR := SRwordNT) (corres_setScalar_NT "i" m)
      (corres_seq (SR := SRwordNT)
        (corres_setExpr "o" (.SLit v) hv)
        (corres_setExpr "i" (.SLit 0) (by simp only [IsArithClean]; norm_num))
        (fun _ _ => trivial))
      (fun _ _ => trivial)
  refine corres_fa_congr hstep ?_
  intro a
  funext s
  simp only [loopSrcStep, evalZMod]
  by_cases hi : s = "i"
  · simp [hi]
  · by_cases ho : s = "o" <;> simp [hi, ho]

/-- **`loopSrc_corres` — the welded source-level bounded-loop `Corres`.**  The
    lowered `RFor` image of the source loop `Corres`-refines the `n`-fold iteration
    `nfold (loopSrcStep v) n` of the loop-invariant step, welded from the per-trip leaf
    by `corres_for`.  This is the source-loop preimage reaching `corres_for` that
    `forFold` (`evalImp = none`) and `whileLoop` (`RWhileNz`) could not supply. -/
theorem loopSrc_corres (v : Nat) (hv : v < 2 ^ 64) (n : Nat) :
    Corres SRwordNT (fun _ => True) (nfold (loopSrcStep v) n) (lower (loopSrc v n)) :=
  corres_for (SR := SRwordNT) "i" (lower (loopBodySrc v))
    (loopBody_corres v hv) (fun _ _ => trivial) n

/-! ## §4  The two legs, bundled: the source-preimage gap closed -/

/-- **`loopSrc_source_preimage`.**  On the *one* lowered `RFor` image
    `lower (loopSrc v n)` of a source loop with a **defined** evaluation:
    (1) the `RustExec` refinement of the source semantics (`loopSrc_refines`),
    (2) the ascent bounded-loop `Corres` via `corres_for` (`loopSrc_corres`), and
    (3) the `RFor`-headed shape witnessing it lands on the `corres_for` arm.
    Together: the loop source-preimage gap is closed for the `RustSubsetToLowCT`
    front — a bounded counted loop whose source both evaluates and lowers to the
    bounded-loop ascent leaf. -/
theorem loopSrc_source_preimage (v : Nat) (hv : v < 2 ^ 64) (n : Nat) :
    RRefines (RustSrc.exec (loopSrc v n)) (lower (loopSrc v n))
      ∧ Corres SRwordNT (fun _ => True) (nfold (loopSrcStep v) n) (lower (loopSrc v n))
      ∧ lower (loopSrc v n) = .RFor "i" n (lower (loopBodySrc v)) :=
  ⟨loopSrc_refines v n, loopSrc_corres v hv n, loopSrc_lower v n⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
