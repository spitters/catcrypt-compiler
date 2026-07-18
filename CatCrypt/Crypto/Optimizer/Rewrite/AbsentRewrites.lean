/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic

/-!
# Three verified algebraic rewrites that the pass library was missing

A capability audit (2026-06-19) confirmed three semantics-preserving rewrites were
ABSENT from the optimizer (`Optimizer/Rewrite/{Egraph,Peephole}.lean` had
`x*1↦x`, `x+0↦x`, `x*2^k↦x<<<k`, `sub_self↦xor`, but not these). They are the
canonicalizations PrimeIR-style crypto compilers run; here each is proved as a
denotation-preserving identity over its natural carrier.

1. **`neg(neg x) = x`** — double-negation elimination on `BitVec` (the algebraic
   peephole companion to `sub_self_eq_xor`). Carrier: `BitVec w` (a `CommRing`).
2. **`fromMont ∘ toMont = id`** — Montgomery-domain canonicalization. Stated over
   the abstract field `ZMod p` and PARAMETRIC in the Montgomery factor `R` (only
   `R · R⁻¹ = 1` is used), so the wide literal `R = 2^(64·k) mod p` is NEVER
   materialized — the Trocq/relational-transport discipline ([[feedback-slow-proofs-and-probe-first]],
   `RelationalFrontBls377Mul`): prove on the cheap abstract structure, never `cbv`
   over the concrete Montgomery constant.
3. **`reverse ∘ reverse = id`** — redundant bit-reversal elimination, the core of
   the "NTT without bit-reversal" rewrite (two consecutive bit-reversal stages of
   an NTT/INTT cancel). Carrier: `BitVec w` indices (`BitVec.reverse`), plus the
   list-permutation form for a whole reordering stage.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites

/-! ## 1. Double-negation elimination: `neg (neg x) = x` on `BitVec` -/

/-- **`neg(neg x) = x`** — double-negation elimination, the absent algebraic
    peephole rule. `BitVec w` is a `CommRing`, so this is `neg_neg`; stated here as
    the rewrite-soundness core (sibling of `Peephole.sub_self_eq_xor`). -/
theorem neg_neg_rewrite {w : Nat} (x : BitVec w) : - - x = x := BitVec.neg_neg

/-- The rewrite `negElim : - - x ↦ x` is denotation-preserving for any
    interpretation `f : BitVec w → α`: `f (- - x) = f x`. -/
theorem negElim_sound {w : Nat} {α : Type*} (f : BitVec w → α) (x : BitVec w) :
    f (- - x) = f x := by rw [neg_neg_rewrite]

/-! ## 2. Montgomery-domain canonicalization: `fromMont ∘ toMont = id`

`toMont x = x · R` and `fromMont y = y · R⁻¹` over `ZMod p`, with `R` a unit
(`R · R⁻¹ = 1`). The round-trip cancels WITHOUT ever evaluating `R` — the abstract
form the relational front transports onto the emitted limb representation. -/

variable {p : Nat}

/-- Map a residue into the Montgomery domain: `x ↦ x · R`. -/
def toMont (R x : ZMod p) : ZMod p := x * R

/-- Map a residue out of the Montgomery domain: `y ↦ y · R⁻¹`, with `Rinv` the
    given inverse of `R`. -/
def fromMont (Rinv y : ZMod p) : ZMod p := y * Rinv

/-- **`fromMont ∘ toMont = id`** — the Montgomery round-trip is the identity,
    parametric in `R` (only `R · Rinv = 1` is used; `R` is never materialized). -/
theorem fromMont_toMont (R Rinv x : ZMod p) (h : R * Rinv = 1) :
    fromMont Rinv (toMont R x) = x := by
  unfold fromMont toMont
  rw [mul_assoc, h, mul_one]

/-- **`toMont ∘ fromMont = id`** — the other direction (a Montgomery-domain value
    decoded and re-encoded is unchanged). -/
theorem toMont_fromMont (R Rinv y : ZMod p) (h : R * Rinv = 1) :
    toMont R (fromMont Rinv y) = y := by
  unfold toMont fromMont
  rw [mul_assoc, mul_comm Rinv R, h, mul_one]

/-! ## 3. Redundant bit-reversal elimination: `reverse ∘ reverse = id`

Two consecutive bit-reversal stages (e.g. the bit-reversal at the end of a
decimation-in-time NTT followed by the one at the start of the INTT) cancel. -/

/-- **`reverse (reverse x) = x`** on bit-indices — the bit-reversal elimination
    core (`BitVec.reverse_reverse_eq`). A pass may drop any pair of adjacent
    bit-reversal stages. -/
theorem reverse_reverse_rewrite {w : Nat} (x : BitVec w) :
    x.reverse.reverse = x := BitVec.reverse_reverse_eq

/-- Stage form: reversing a whole index list twice is the identity, so a
    reorder-stage pass that emits `bitrev` twice is a no-op — the
    NTT-without-bit-reversal identity at the whole-stage level. -/
theorem bitrevStage_elim {w : Nat} (xs : List (BitVec w)) :
    (xs.map BitVec.reverse).map BitVec.reverse = xs := by
  simp only [List.map_map, Function.comp_def, reverse_reverse_rewrite, List.map_id']

end CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites
