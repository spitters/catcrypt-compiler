/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Bridges.ReprTransferArray
public import CatCrypt.Hax.FoldRange
public import Mathlib.Tactic.NormNum

/-!
# Tactics for extraction ↔ reference agreement proofs

An extraction bridge proves that a haxpipe-extracted routine over `Array Int`
computes a reference stated over an indexed family of abstract values. Every such
proof repeats four moves, and these tactics are those moves.

* `repr_agrees` — the simp set of per-operator agreement lemmas
  (`enc (a ⊕ b) = extracted_xor (enc a) (enc b)` and friends). Register a
  representation's operators with `@[repr_agrees]` once; the tactics below then
  normalise any expression over them.
* `fin_index` — discharge an index side-condition (`Fin` extensionality plus
  linear arithmetic over `Fin.val`/`%`/`/`). These appear on nearly every lane
  read and write.
* `lane_step` — close one loop-body step: rewrite the reads through
  `ArrayAgree.getI`, normalise the operator with `repr_agrees`, and write back
  through `ArrayAgree.updateI`.
* `fold_unroll n` — unroll a concrete-bound `Hax.foldRange` by `n` iterations
  and close the range. Bounded rather than `repeat`, because `repeat` on
  `foldRange_step` reports a spurious error at the boundary instead of stopping.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactic

open Lean Elab Tactic

/-- Simp set of per-operator agreement lemmas for a representation. Tag the
    lemma relating an abstract operation to the extracted one — for a lane
    representation, `enc (x ^^^ y) = Hax.bitxor_w 64 (enc x) (enc y)` — and the
    transfer tactics will use it. -/
register_simp_attr repr_agrees

/-- Discharge an index side-condition: prove a `Fin` equality by extensionality
    and close the resulting arithmetic (`Fin.val` of a literal, `%`, `/`) with
    `omega`. Falls back to plain `omega` when the goal is already arithmetic.

    This is the single most repeated step in a bridge proof: every lane read and
    write carries one. -/
syntax (name := finIndex) "fin_index" : tactic

macro_rules
  | `(tactic| fin_index) =>
    `(tactic|
      first
        | rfl
        | ((try simp only [Fin.val_mk, Fin.isValue]); omega)
        | (apply Fin.ext; (try simp only [Fin.val_mk, Fin.isValue]); omega)
        | (apply Fin.ext; (try simp); omega)
        | omega)

/-- Normalise an expression over a registered representation: unfold the
    extraction's arithmetic wrappers and rewrite every operator through its
    `@[repr_agrees]` lemma. -/
syntax (name := reprNorm) "repr_norm" : tactic

macro_rules
  | `(tactic| repr_norm) =>
    `(tactic| simp only [Hax.add, Hax.mul, Hax.sub, Hax.rem, repr_agrees])

/-- Close one loop-body step of an extraction bridge, given the incoming
    agreement hypothesis `h`: read the represented positions through
    `ArrayAgree.getI`, normalise the operator with `repr_agrees`, and write the
    result back through `ArrayAgree.updateI`, discharging index side-conditions
    with `fin_index`.

    Use when the goal is `ArrayAgree e n (Hax.array_update …) (Function.update …)`. -/
syntax (name := laneStep) "lane_step" (ppSpace colGt term)? : tactic

macro_rules
  | `(tactic| lane_step $h:term) =>
    `(tactic|
      (repr_norm
       first
         | exact ReprTransfer.ArrayAgree.updateI $h _ _ (by fin_index) (by fin_index) _
         | (rw [ReprTransfer.ArrayAgree.getI $h _ (by fin_index) (by fin_index)]
            repr_norm
            exact ReprTransfer.ArrayAgree.updateI $h _ _ (by fin_index) (by fin_index) _)))
  | `(tactic| lane_step) =>
    `(tactic|
      (repr_norm
       first
         | assumption
         | (apply ReprTransfer.ArrayAgree.updateI <;> first | assumption | fin_index | rfl)))

/-- Unroll a `Hax.foldRange` with a concrete bound by `n` iterations, then close
    the empty range.

    Two things this gets right that the obvious form does not. Bounded rather
    than `repeat`: at the boundary the inner `norm_num` fails on the false
    inequality and reports its own error instead of letting `repeat` stop,
    leaving spurious `⊢ False` goals. And the loop index is normalised between
    iterations: without that the bound accumulates as `0 + 1 + 1 + …`, which no
    later rewrite matches against a literal. -/
syntax (name := foldUnroll) "fold_unroll" (ppSpace colGt num)? : tactic

macro_rules
  | `(tactic| fold_unroll $n:num) =>
    `(tactic|
      (iterate $n (rw [Hax.foldRange_step _ _ _ _ (by norm_num)]; try norm_num only)
       rw [Hax.foldRange_stop _ _ _ _ (by norm_num)]
       try norm_num only))
  | `(tactic| fold_unroll) =>
    `(tactic| rw [Hax.foldRange_stop _ _ _ _ (by norm_num)])

end CatCrypt.Tactic
