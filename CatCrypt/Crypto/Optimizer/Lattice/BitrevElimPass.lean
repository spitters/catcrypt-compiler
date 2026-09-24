/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites

/-!
# Verified "NTT without bit-reversal" pass

A decimation-in-time NTT followed by an INTT (or two reorder stages emitted
back-to-back by a tiling pass) carries a redundant pair of bit-reversal stages:
the bit-reversal that re-orders the DIT output, immediately undone by the
bit-reversal that re-orders the INTT input. The two cancel, so a correct
compiler can DELETE the pair and run the butterflies straight through — this is
the well-known "NTT without bit-reversal" optimization.

This module defines that optimization as a *correctness-preserving* pass over an
explicit NTT-pipeline model, reusing the proved bit-reversal-elimination cores
from `AbsentRewrites`:

* `reverse_reverse_rewrite : x.reverse.reverse = x` (per-index), and
* `bitrevStage_elim : (xs.map .reverse).map .reverse = xs` (whole stage).

We model a pipeline as a `List Stage` over a data vector `List (BitVec w)`. A
`bitrev` stage applies `List.map BitVec.reverse` to the vector (faithfully
re-indexing through the `w`-bit bit-reversal permutation, which is a self-inverse
involution); a `butterfly g` stage applies an arbitrary stage function `g`. The
denotation `Pipeline.denote` folds the stages over the input.

The pass `bitrevElim` deletes any two ADJACENT `bitrev` stages, and
`bitrevElim_denote` proves it leaves the denotation unchanged. The repeated form
`bitrevElimStar` canonicalizes a whole pipeline (worked example:
`[bitrev, bitrev, butterfly g] ↦ [butterfly g]`, with equal denotation).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.BitrevElimPass

open CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites

variable {w : Nat}

/-- A single NTT-pipeline stage over a data vector `List (BitVec w)`.

* `bitrev` — a bit-reversal reorder stage: maps every entry through
  `BitVec.reverse` on its `w`-bit index. `BitVec.reverse` is a self-inverse
  involution, so this models the bit-reversal permutation.
* `butterfly g` — any other stage, carrying its (opaque) stage function `g`
  (e.g. a layer of butterflies / twiddle multiplications). -/
inductive Stage (w : Nat) where
  | bitrev : Stage w
  | butterfly : (List (BitVec w) → List (BitVec w)) → Stage w

/-- The action of a single stage on the data vector. -/
def Stage.run : Stage w → List (BitVec w) → List (BitVec w)
  | .bitrev,      xs => xs.map BitVec.reverse
  | .butterfly g, xs => g xs

/-- An NTT pipeline: a list of stages, applied left-to-right. -/
abbrev Pipeline (w : Nat) := List (Stage w)

/-- Denotation of a pipeline: fold the stages over the input vector,
    left-to-right (head stage runs first). -/
def Pipeline.denote : Pipeline w → List (BitVec w) → List (BitVec w)
  | [],      xs => xs
  | s :: ps, xs => Pipeline.denote ps (s.run xs)

@[simp] theorem Pipeline.denote_nil (xs : List (BitVec w)) :
    Pipeline.denote ([] : Pipeline w) xs = xs := rfl

@[simp] theorem Pipeline.denote_cons (s : Stage w) (ps : Pipeline w)
    (xs : List (BitVec w)) :
    Pipeline.denote (s :: ps) xs = Pipeline.denote ps (s.run xs) := rfl

/-- Two adjacent `bitrev` stages are a no-op on any data vector: this is exactly
    the whole-stage bit-reversal-elimination core `bitrevStage_elim`. -/
theorem bitrev_bitrev_run (xs : List (BitVec w)) :
    Stage.run (w := w) .bitrev (Stage.run (w := w) .bitrev xs) = xs := by
  simpa [Stage.run] using bitrevStage_elim (w := w) xs

/-- **The pass.** Canonicalize a pipeline by deleting any pair of ADJACENT
    `bitrev` stages (one rewriting pass, left-to-right). -/
def bitrevElim : Pipeline w → Pipeline w
  | .bitrev :: .bitrev :: ps => bitrevElim ps
  | s :: ps                  => s :: bitrevElim ps
  | []                       => []

/-- **Correctness preservation.** The bit-reversal-elimination pass does not
    change the pipeline's denotation: `(bitrevElim p).denote xs = p.denote xs`.
    The `bitrev, bitrev` deletion is sound precisely because of
    `bitrev_bitrev_run` (a repackaging of `bitrevStage_elim`). -/
theorem bitrevElim_denote (p : Pipeline w) (xs : List (BitVec w)) :
    (bitrevElim p).denote xs = p.denote xs := by
  induction p using bitrevElim.induct generalizing xs with
  | case1 ps ih =>
      -- p = bitrev :: bitrev :: ps
      simp only [bitrevElim, Pipeline.denote_cons, ih, bitrev_bitrev_run]
  | case2 s ps _hcond ih =>
      -- p = s :: ps, with s not starting an adjacent bitrev/bitrev pair
      simp only [bitrevElim, Pipeline.denote_cons, ih]
  | case3 =>
      -- p = []
      simp only [bitrevElim]

/-- Iterate the single pass to a fixpoint bound by the pipeline length, so a
    whole run of redundant reorder stages collapses (the pass shrinks the list,
    so `length` fuel suffices). -/
def bitrevElimStar (p : Pipeline w) : Pipeline w :=
  Nat.rec (motive := fun _ => Pipeline w) p
    (fun _ q => bitrevElim q) p.length

/-- `bitrevElimStar` is also correctness-preserving: iterating a
    denotation-preserving pass preserves the denotation. -/
theorem bitrevElimStar_denote (p : Pipeline w) (xs : List (BitVec w)) :
    (bitrevElimStar p).denote xs = p.denote xs := by
  unfold bitrevElimStar
  induction p.length with
  | zero => rfl
  | succ n ih => simpa [Nat.rec, bitrevElim_denote] using ih

/-! ## Worked example

`[bitrev, bitrev, butterfly g]` canonicalizes to `[butterfly g]`, with equal
denotation on every input. This is the concrete "drop the redundant bit-reversal
around the butterflies" rewrite. -/

section Example

variable (g : List (BitVec w) → List (BitVec w))

/-- The pass deletes the leading redundant bit-reversal pair, leaving only the
    butterfly stage. -/
example : bitrevElim [Stage.bitrev, Stage.bitrev, Stage.butterfly g]
    = [Stage.butterfly g] := rfl

/-- And the canonicalized pipeline computes the same vector as the original. -/
theorem worked_example (xs : List (BitVec w)) :
    Pipeline.denote [Stage.butterfly g] xs
      = Pipeline.denote [Stage.bitrev, Stage.bitrev, Stage.butterfly g] xs := by
  simp only [Pipeline.denote_cons, Pipeline.denote_nil, Stage.run]
  rw [bitrevStage_elim]

end Example

end CatCrypt.Crypto.Optimizer.Lattice.BitrevElimPass
