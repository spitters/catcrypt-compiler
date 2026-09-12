/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeNeg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCmov

/-!
# Counted-loop lifts for the shift- and negate-extended bridged subsets

`RunBlockLsemAgree.lean` lifts its straight-line `runBlock` ↔ `lsemStraightMem`
agreement over a runtime trip count in `runBlock_lsem_agree_loop` (the ALU core
plus word memory), `runBlock_lsem_agreeM_loop` (adding `mulx`) and
`runBlock_lsem_agreeF_loop` (the flag-aware `JLstateCorrF` axis). This module
supplies the same lift for the two sidecar subsets that carry the plain
`JLstateCorr`:

* `InShiftSubset` (`RunBlockLsemAgreeShift.lean`), the ALU core plus the
  immediate-count shifts, lowered by `jToRMSh`;
* `InNegSubset` (`RunBlockLsemAgreeNeg.lean`), that set plus the unary
  two's-complement negate, lowered by `jToRMNeg`.

Both correspondences are `JLstateCorr`, so the back-edge `setLpc` is absorbed by
`JLstateCorr_setLpc` and the induction on the trip count is the one
`runBlock_lsem_agree_loop` runs: each trip is one application of the sidecar's
block-level agreement, and the loop folds on both sides (`runBoundedLoopMem` on
the lsem side, `LoopUnroll.runBoundedLoop` on the `JState` side) recurse on the
same remaining count.

The third sidecar subset, `InFlagReaderSubset` of `RunBlockLsemAgreeCmov.lean`,
already carries its own lift: `JLstateCorrZ_setLpc` and
`runBlock_lsem_agreeZ_loop` thread the designated `(cfN, zfN)` pair across the
back-edge there. It is imported here so that the four counted-loop contracts of
the extended subsets are reachable from one module.

## Main results

* `runBlock_lsem_agreeSh_loop`: the counted-loop lift on `InShiftSubset`.
* `runBlock_lsem_agreeNeg_loop`: the counted-loop lift on `InNegSubset`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeLoop

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeNeg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

/-! ## 1. The shift-extended subset under a counted loop -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The counted-loop lift on the shift-extended subset.** A straight-line body
    `b` all of whose opcodes are in `InShiftSubset`, iterated `n` times, agrees on
    both machine models: the `n`-fold `runBoundedLoopMem` over the lowered body
    `b.map jToRMSh` runs to completion and its result corresponds — via
    `JLstateCorr` — to the `JState`-side `n`-fold `runBoundedLoop`. Induction on
    the trip count: each trip is one `runBlock_lsem_agreeSh`, and the inter-trip
    `setLpc 1` is absorbed by `JLstateCorr_setLpc`. -/
theorem runBlock_lsem_agreeSh_loop (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InShiftSubset i) (n : Nat) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', runBoundedLoopMem (b.map jToRMSh) n ls = some ls' ∧
      JLstateCorr (runBoundedLoop s n b) ls' := by
  induction n generalizing s ls with
  | zero => exact ⟨ls, rfl, h⟩
  | succ k ih =>
      obtain ⟨ls1, hstep1, hcorr1⟩ := runBlock_lsem_agreeSh b hb s ls h
      rw [runBoundedLoopMem_succ, hstep1, Option.bind_some, runBoundedLoop_succ]
      exact ih (runBlock s b) (ls1.setLpc 1) (JLstateCorr_setLpc _ _ hcorr1 1)

/-! ## 2. The negate-extended subset under a counted loop -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The counted-loop lift on the negate-extended subset.** As
    `runBlock_lsem_agreeSh_loop` but over `InNegSubset`, which adds the unary
    two's-complement negate carrying the constant-time mask idiom, lowered by
    `jToRMNeg`. Each trip is one `runBlock_lsem_agreeNeg`; the back-edge `setLpc`
    is again absorbed by `JLstateCorr_setLpc`. -/
theorem runBlock_lsem_agreeNeg_loop (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InNegSubset i) (n : Nat) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', runBoundedLoopMem (b.map jToRMNeg) n ls = some ls' ∧
      JLstateCorr (runBoundedLoop s n b) ls' := by
  induction n generalizing s ls with
  | zero => exact ⟨ls, rfl, h⟩
  | succ k ih =>
      obtain ⟨ls1, hstep1, hcorr1⟩ := runBlock_lsem_agreeNeg b hb s ls h
      rw [runBoundedLoopMem_succ, hstep1, Option.bind_some, runBoundedLoop_succ]
      exact ih (runBlock s b) (ls1.setLpc 1) (JLstateCorr_setLpc _ _ hcorr1 1)

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeLoop
