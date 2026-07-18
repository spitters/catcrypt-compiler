/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites

/-!
# Montgomery-domain canonicalization pass

A peephole pass over a tiny straight-line "Montgomery-domain program" that
removes an adjacent `toMont`/`fromMont` (and `fromMont`/`toMont`) pair. The pass
is the program-level lift of the proved algebraic cores in
`AbsentRewrites` (`fromMont_toMont`, `toMont_fromMont`): a value entering and
immediately leaving the Montgomery domain is unchanged, so the encode/decode pair
may be dropped.

The whole development is PARAMETRIC in the Montgomery factor `R` — only
`R · R⁻¹ = 1` is used, so the wide literal `R = 2^(64·k) mod p` is never
materialized (the Trocq/relational-transport discipline: prove on the cheap
abstract structure, never `cbv` over the concrete Montgomery constant).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.MontDomainElimPass

open CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites

variable {p : Nat}

/-! ## A tiny Montgomery-domain straight-line program -/

/-- A single op of a straight-line Montgomery-domain program over `ZMod p`.

* `toMont R`   — encode into the Montgomery domain (`x ↦ x · R`);
* `fromMont Rinv` — decode out of it (`x ↦ x · Rinv`);
* `mul c`      — an in-domain field multiplication by a constant `c`.

`R`/`Rinv` are carried symbolically; the soundness proof only ever uses
`R · Rinv = 1`, never the literal value of `R`. -/
inductive Op (p : Nat) where
  | toMont (R : ZMod p)
  | fromMont (Rinv : ZMod p)
  | mul (c : ZMod p)
  deriving DecidableEq

/-- A program is a straight-line list of ops, applied left-to-right. -/
abbrev Prog (p : Nat) := List (Op p)

/-- Denotation of a single op as a function `ZMod p → ZMod p`. -/
def Op.denote : Op p → ZMod p → ZMod p
  | Op.toMont R, x => AbsentRewrites.toMont R x
  | Op.fromMont Rinv, x => AbsentRewrites.fromMont Rinv x
  | Op.mul c, x => x * c

/-- Denotation of a program: fold the ops left-to-right over the input. -/
def denote : Prog p → ZMod p → ZMod p
  | [], x => x
  | op :: rest, x => denote rest (op.denote x)

@[simp] theorem denote_nil (x : ZMod p) : denote ([] : Prog p) x = x := rfl

@[simp] theorem denote_cons (op : Op p) (rest : Prog p) (x : ZMod p) :
    denote (op :: rest) x = denote rest (op.denote x) := rfl

/-- Denotation distributes over append: running `q` then `r` is running their
    concatenation. -/
theorem denote_append (q r : Prog p) (x : ZMod p) :
    denote (q ++ r) x = denote r (denote q x) := by
  induction q generalizing x with
  | nil => rfl
  | cons op rest ih => simp [denote, ih]

/-! ## The pass: eliminate an adjacent `toMont`/`fromMont` pair

`montDomainElim` is parametrized by the *witness* `R Rinv` (with `R · Rinv = 1`)
that the pass is allowed to cancel. It scans the program and drops any adjacent
`toMont R; fromMont Rinv` or `fromMont Rinv; toMont R` pair, recursing into the
remainder. -/

/-- The peephole pass. Removes adjacent `toMont R; fromMont Rinv` and
    `fromMont Rinv; toMont R` pairs for the cancellation witness `R Rinv`. -/
def montDomainElim (R Rinv : ZMod p) : Prog p → Prog p
  | Op.toMont R' :: Op.fromMont Rinv' :: rest =>
      if R' = R ∧ Rinv' = Rinv then
        montDomainElim R Rinv rest
      else
        Op.toMont R' :: montDomainElim R Rinv (Op.fromMont Rinv' :: rest)
  | Op.fromMont Rinv' :: Op.toMont R' :: rest =>
      if R' = R ∧ Rinv' = Rinv then
        montDomainElim R Rinv rest
      else
        Op.fromMont Rinv' :: montDomainElim R Rinv (Op.toMont R' :: rest)
  | op :: rest => op :: montDomainElim R Rinv rest
  | [] => []

/-- **Soundness of the pass.** For any cancellation witness `R · Rinv = 1`, the
    pass preserves the denotation of the program: the optimized program computes
    the same field-domain function as the original, on every input.

    Parametric in `R` (only `h : R * Rinv = 1` is used). -/
theorem montDomainElim_denote (R Rinv : ZMod p) (h : R * Rinv = 1) :
    ∀ (prog : Prog p) (x : ZMod p),
      denote (montDomainElim R Rinv prog) x = denote prog x
  | [], _ => rfl
  | [Op.toMont _], _ => rfl
  | [Op.fromMont _], _ => rfl
  | [Op.mul _], _ => rfl
  | Op.toMont R' :: Op.fromMont Rinv' :: rest, x => by
      by_cases hcond : R' = R ∧ Rinv' = Rinv
      · obtain ⟨hR, hRinv⟩ := hcond
        subst hR; subst hRinv
        rw [show montDomainElim R' Rinv' (Op.toMont R' :: Op.fromMont Rinv' :: rest)
              = montDomainElim R' Rinv' rest from by
              simp only [montDomainElim, and_self, if_true]]
        rw [montDomainElim_denote R' Rinv' h rest]
        simp only [denote_cons, Op.denote]
        rw [fromMont_toMont R' Rinv' x h]
      · rw [show montDomainElim R Rinv (Op.toMont R' :: Op.fromMont Rinv' :: rest)
              = Op.toMont R' :: montDomainElim R Rinv (Op.fromMont Rinv' :: rest) from by
              simp only [montDomainElim, if_neg hcond]]
        simp only [denote_cons]
        rw [montDomainElim_denote R Rinv h (Op.fromMont Rinv' :: rest)]
        simp only [denote_cons]
  | Op.fromMont Rinv' :: Op.toMont R' :: rest, x => by
      by_cases hcond : R' = R ∧ Rinv' = Rinv
      · obtain ⟨hR, hRinv⟩ := hcond
        subst hR; subst hRinv
        rw [show montDomainElim R' Rinv' (Op.fromMont Rinv' :: Op.toMont R' :: rest)
              = montDomainElim R' Rinv' rest from by
              simp only [montDomainElim, and_self, if_true]]
        rw [montDomainElim_denote R' Rinv' h rest]
        simp only [denote_cons, Op.denote]
        rw [toMont_fromMont R' Rinv' x h]
      · rw [show montDomainElim R Rinv (Op.fromMont Rinv' :: Op.toMont R' :: rest)
              = Op.fromMont Rinv' :: montDomainElim R Rinv (Op.toMont R' :: rest) from by
              simp only [montDomainElim, if_neg hcond]]
        simp only [denote_cons]
        rw [montDomainElim_denote R Rinv h (Op.toMont R' :: rest)]
        simp only [denote_cons]
  | Op.toMont R' :: Op.toMont R'' :: rest, x => by
      rw [show montDomainElim R Rinv (Op.toMont R' :: Op.toMont R'' :: rest)
            = Op.toMont R' :: montDomainElim R Rinv (Op.toMont R'' :: rest) from rfl]
      simp only [denote_cons]
      rw [montDomainElim_denote R Rinv h (Op.toMont R'' :: rest)]
      simp only [denote_cons]
  | Op.toMont R' :: Op.mul c :: rest, x => by
      rw [show montDomainElim R Rinv (Op.toMont R' :: Op.mul c :: rest)
            = Op.toMont R' :: montDomainElim R Rinv (Op.mul c :: rest) from rfl]
      simp only [denote_cons]
      rw [montDomainElim_denote R Rinv h (Op.mul c :: rest)]
      simp only [denote_cons]
  | Op.fromMont Rinv' :: Op.fromMont Rinv'' :: rest, x => by
      rw [show montDomainElim R Rinv (Op.fromMont Rinv' :: Op.fromMont Rinv'' :: rest)
            = Op.fromMont Rinv' :: montDomainElim R Rinv (Op.fromMont Rinv'' :: rest) from rfl]
      simp only [denote_cons]
      rw [montDomainElim_denote R Rinv h (Op.fromMont Rinv'' :: rest)]
      simp only [denote_cons]
  | Op.fromMont Rinv' :: Op.mul c :: rest, x => by
      rw [show montDomainElim R Rinv (Op.fromMont Rinv' :: Op.mul c :: rest)
            = Op.fromMont Rinv' :: montDomainElim R Rinv (Op.mul c :: rest) from rfl]
      simp only [denote_cons]
      rw [montDomainElim_denote R Rinv h (Op.mul c :: rest)]
      simp only [denote_cons]
  | Op.mul c :: rest, x => by
      rw [show montDomainElim R Rinv (Op.mul c :: rest)
            = Op.mul c :: montDomainElim R Rinv rest from rfl]
      simp only [denote_cons]
      rw [montDomainElim_denote R Rinv h rest]
  termination_by prog => prog.length

/-! ## Worked example

`toMont R; fromMont Rinv; mul c` canonicalizes to `mul c`: the encode/decode pair
is dropped, leaving just the in-domain multiply. -/

/-- The example program: enter the Montgomery domain, immediately leave it, then
    multiply by `c`. -/
def exampleProg (R Rinv c : ZMod p) : Prog p :=
  [Op.toMont R, Op.fromMont Rinv, Op.mul c]

/-- The pass canonicalizes the example to just `[mul c]` (when `R`/`Rinv` are the
    declared cancellation witness). -/
theorem exampleProg_elim (R Rinv c : ZMod p) :
    montDomainElim R Rinv (exampleProg R Rinv c) = [Op.mul c] := by
  simp only [exampleProg, montDomainElim, and_self, if_true]

/-- And the canonicalized program denotes the same function: both compute
    `x ↦ x · c`. -/
theorem exampleProg_denote (R Rinv c : ZMod p) (h : R * Rinv = 1) (x : ZMod p) :
    denote (exampleProg R Rinv c) x = x * c := by
  rw [← montDomainElim_denote R Rinv h, exampleProg_elim]
  simp only [denote_cons, denote_nil, Op.denote]

end CatCrypt.Crypto.Optimizer.Rewrite.MontDomainElimPass
