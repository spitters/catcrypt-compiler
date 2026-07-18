/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.HetArrayFront
import CatCrypt.Crypto.SecureCompilation.LoadU32LeCompiles

/-!
# `load_u32_le` value-correct through the verified front, by composition

The real `load_u32_le` body is four runtime-indexed `u8`-array reads, each widened
to `u32`, combined little-endian: `arr[i0] | arr[i1]<<8 | arr[i2]<<16 | arr[i3]<<24`.
Two verified-front pieces already cover the two halves:

* the **array reads** — `HetArrayFront.arrLoadCom` (the `index[arr,i]` recogniser's
  `stackLoad` gather), with `arrLoadCom_denote : … = stackGet arr i.toNat`;
* the **LE-combine** — `LoadU32LeCompiles.loadU32LeModel` (the real `cast#32`/`Shl#32`/
  `BitOr#32` heads), with `loadU32LeModel_denote` giving the `setWidth`-combine.

This module **composes** them: feeding the four widened het reads as the combine's
inputs, the typed-front denotation is exactly the little-endian `u32` load over the
array. The result is the first array-bodied real-extraction shape value-correct
end-to-end through the (parallel het + homogeneous) verified front.

**Why composition, not one monolithic `Com`.** Hand-building the whole body as a
single ~15-binding heterogeneous `Com` and reducing its `.denote` is inherently
**O(n²)** for term rewriting: each `Var.lookup`/`lookupArgs` rewrite re-traverses a
valuation that grows with every binding, so an n-binding chain costs Θ(n²) and the
single-`isDefEq` `rfl` blows up. Composing the two **already-proved** denotations
sidesteps the giant valuation entirely (each half reduces in isolation), and states
the honest fact directly: the real function is *verified array reads* followed by the
*verified arithmetic combine*.
-/

set_option autoImplicit false
-- Hard fail-fast bound: the composition proof is small (one `rw` + a 4-term `simp`);
-- if a rewrite ever runs away it errors instead of spinning.
set_option maxHeartbeats 400000

namespace CatCrypt.Crypto.SecureCompilation.LoadU32LeVerbatim

open Hax
open CatCrypt.Crypto.SecureCompilation.HetArrayFront
open CatCrypt.Crypto.SecureCompilation.TExprToThir (TExpr.denoteScalarT)
open CatCrypt.Crypto.SecureCompilation.LoadU32LeCompiles
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inpGet)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet)

/-- The four widened het reads, as the `Fin 4 → BitVec 32` input vector the
    `loadU32LeModel` combine consumes: read byte `k` is `arr[(i k)]` via the verified
    `stackLoad` gather (`arrLoadCom`), widened `u8 → u32`. -/
def hetReads (arr : Fin 32 → BitVec 8) (i : Fin 4 → BitVec 64) : Fin 4 → BitVec 32 :=
  fun k => BitVec.setWidth 32 ((arrLoadCom 8 32).denote (arrInputValuation 8 32 arr (i k)))

/-- **`load_u32_le` value-correct end-to-end through the verified front.**

    Feeding the four widened het reads (`hetReads`, each the verified `stackLoad`
    gather over the `&[u8;32]` array) as the inputs of the real-head LE-combine
    `loadU32LeModel`, the typed-front denotation is exactly the little-endian `u32`
    load `arr[i0] | arr[i1]<<8 | arr[i2]<<16 | arr[i3]<<24` over the array — for every
    `arr : Fin 32 → BitVec 8` and runtime offsets `i : Fin 4 → BitVec 64`.

    This composes the verified array-read front (`arrLoadCom_denote`) with the verified
    LE-combine front (`loadU32LeModel_denote`); see the module docstring for why the
    monolithic single-`Com` form is avoided (quadratic denote). -/
theorem loadU32Le_via_het (arr : Fin 32 → BitVec 8) (i : Fin 4 → BitVec 64) :
    TExpr.denoteScalarT ["b0", "b1", "b2", "b3"] (hetReads arr i) loadU32LeModel (fun _ => none)
      = some (BitVec.setWidth 32 (stackGet arr (i 0).toNat)
              ||| (BitVec.setWidth 32 (stackGet arr (i 1).toNat) <<< (8 : Nat))
              ||| (BitVec.setWidth 32 (stackGet arr (i 2).toNat) <<< (16 : Nat))
              ||| (BitVec.setWidth 32 (stackGet arr (i 3).toNat) <<< (24 : Nat))) := by
  rw [loadU32LeModel_denote (hetReads arr i)]
  -- `inpGet … k` reduces (`k < 4`) to the `k`-th het read = `stackGet arr (i k)`, widened;
  -- the outer `setWidth 32` collapses (`setWidth_eq`); `rfl` discharges the in-range `dite`
  -- and the `(k : Fin 4) ≡ ⟨k, _⟩` defeq. Small goal — no monolithic-Com blowup.
  simp only [inpGet, hetReads, arrLoadCom_denote, BitVec.setWidth_eq]; rfl

end CatCrypt.Crypto.SecureCompilation.LoadU32LeVerbatim
