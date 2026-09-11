/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic

/-!
# Generic two-modulus Chinese Remainder Theorem reconstruction

This file packages the two-modulus Chinese Remainder Theorem (CRT) for
residue-number-system (RNS) arithmetic, the reconstruction step that recombines
a value held as a pair of residues `(a mod m, b mod n)` over coprime moduli into
the unique value modulo `m * n`. This is the generic RNS reconstruction relevant
to multi-modulus NTT / FHE backends, where each coefficient is carried in several
small coprime channels and must occasionally be lifted to a single residue.

We do not hand-roll the reconstruction: Mathlib already provides it directly.

* `Nat.chineseRemainder` gives, from `co : n.Coprime m` and residues `a b : ℕ`,
  a value `k` together with proofs `k ≡ a [MOD n]` and `k ≡ b [MOD m]`. This is
  exactly the RNS round-trip property.
* `ZMod.chineseRemainder` packages the same content as a ring isomorphism
  `ZMod (m * n) ≃+* ZMod m × ZMod n`.

The definitions and lemmas below are thin wrappers exposing these in the shape an
RNS reconstruction caller wants, plus a worked example.
-/

@[expose] public section

namespace CatCrypt.Optimizer.Rewrite.CrtGeneric

open scoped Nat

/-- Two-modulus RNS reconstruction: given coprime moduli (`co : n.Coprime m`) and
residues `a` (a channel mod `n`) and `b` (a channel mod `m`), the reconstructed
natural number representing the unique value modulo `n * m`.

This is the value component of `Nat.chineseRemainder`; the two residue laws are
`crt_modEq_left` and `crt_modEq_right`. -/
def crt {m n : ℕ} (co : n.Coprime m) (a b : ℕ) : ℕ :=
  (Nat.chineseRemainder co a b : ℕ)

/-- The reconstruction agrees with the first channel: `crt co a b ≡ a [MOD n]`. -/
theorem crt_modEq_left {m n : ℕ} (co : n.Coprime m) (a b : ℕ) :
    crt co a b ≡ a [MOD n] :=
  (Nat.chineseRemainder co a b).2.1

/-- The reconstruction agrees with the second channel: `crt co a b ≡ b [MOD m]`. -/
theorem crt_modEq_right {m n : ℕ} (co : n.Coprime m) (a b : ℕ) :
    crt co a b ≡ b [MOD m] :=
  (Nat.chineseRemainder co a b).2.2

/-- Uniqueness of the reconstruction modulo `n * m`: any `z` carrying the same two
residues is congruent to `crt co a b` modulo the product. This is what makes the
RNS representation faithful (the lift is well-defined). -/
theorem crt_unique {m n : ℕ} (co : n.Coprime m) {a b z : ℕ}
    (hza : z ≡ a [MOD n]) (hzb : z ≡ b [MOD m]) :
    z ≡ crt co a b [MOD n * m] :=
  Nat.chineseRemainder_modEq_unique co hza hzb

/-- The reconstructed value lies in the canonical range `[0, n * m)` when both
moduli are nonzero, so it is the canonical RNS representative. -/
theorem crt_lt_mul {m n : ℕ} (co : n.Coprime m) (a b : ℕ)
    (hn : n ≠ 0) (hm : m ≠ 0) :
    crt co a b < n * m :=
  Nat.chineseRemainder_lt_mul co a b hn hm

/-! ### Ring-isomorphism form

`ZMod.chineseRemainder` packages the same data as a ring isomorphism. The forward
map splits a residue mod `m * n` into its two channels; its inverse is the
reconstruction. Stating the round-trip as `RingEquiv` identities is the cleanest
way to certify that splitting then reconstructing (and vice versa) is the
identity. -/

/-- The CRT ring isomorphism `ZMod (m * n) ≃+* ZMod m × ZMod n` for coprime
moduli, re-exported for RNS callers. -/
abbrev crtEquiv {m n : ℕ} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- Reconstruct-then-split is the identity on the channel pair: splitting a value
mod `m * n` and reconstructing it recovers the original channels. -/
theorem crtEquiv_symm_apply {m n : ℕ} (h : m.Coprime n) (p : ZMod m × ZMod n) :
    crtEquiv h ((crtEquiv h).symm p) = p :=
  (crtEquiv h).apply_symm_apply p

/-- Split-then-reconstruct is the identity on `ZMod (m * n)`. -/
theorem crtEquiv_symm_apply' {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    (crtEquiv h).symm (crtEquiv h x) = x :=
  (crtEquiv h).symm_apply_apply x

/-! ### Worked example

Take `m = 3`, `n = 5` (coprime), residues `a = 2` (mod `5`) and `b = 1` (mod `3`).
The reconstructed value is `7`: indeed `7 ≡ 2 [MOD 5]` and `7 ≡ 1 [MOD 3]`, and it
is the unique such value in `[0, 15)`. -/

/-- `3` and `5` are coprime (as `(5).Coprime 3`), the orientation `Nat.chineseRemainder`
expects. -/
theorem coprime_5_3 : Nat.Coprime 5 3 := by decide

example : crt coprime_5_3 2 1 = 7 := by decide +kernel

example : crt coprime_5_3 2 1 ≡ 2 [MOD 5] := crt_modEq_left coprime_5_3 2 1

example : crt coprime_5_3 2 1 ≡ 1 [MOD 3] := crt_modEq_right coprime_5_3 2 1

example : crt coprime_5_3 2 1 < 5 * 3 := crt_lt_mul coprime_5_3 2 1 (by decide) (by decide)

end CatCrypt.Optimizer.Rewrite.CrtGeneric
