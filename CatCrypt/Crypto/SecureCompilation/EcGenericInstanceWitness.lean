/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377EC
import CatCrypt.Crypto.SecureCompilation.RelationalFrontPallasEC

/-!
# Consolidation witness: the per-curve EC realizations are instances of the generic one

`EcRealizationGeneric.lean` proves the projective→affine elliptic-curve group-law
realization **once**, over an abstract `[Field F]`
(`ec_jacDouble_realizes_affineDbl` / `ec_jacAdd_realizes_affineAdd`).  The per-curve
files (`RelationalFrontBls377EC.lean`, `RelationalFrontPallasEC.lean`, …) re-prove the
*same* `dbl-2009-l` / `add-2007-bl` field-algebra ties at a fixed base-field prime, with
the carrier renamed (`Bls377Point` / `PallasPoint` instead of `ECAffPoint`, etc.).

This module **demonstrates the per-curve EC files are redundant** with the generic
parametric form, without deleting any committed file.  For BLS12-377 (`F = ZMod bls377Q`)
and Pallas (`F = ZMod pallasQ`) we exhibit the generic realization ties **purely by
`@`-instantiation of the generic theorems** — no `field_simp`/`ring` here.  Each generic
instance is the *same mathematical statement* as the matching per-curve theorem
(`bls377_jacDouble_realizes_affineDbl`, `pallas_jacAdd_realizes_affineAdd`, …): the
coordinate maps are byte-for-byte the same field formulas, only the structure name and the
literal prime differ.  So the per-curve `field_simp; ring` proof bodies were redundant —
they re-derive what `@ec_jacDouble_realizes_affineDbl (ZMod p) _ …` already gives.

## Are the per-curve defs definitionally the generic ones?

No.  The per-curve files declare *fresh* structures (`Bls377Point`, `Bls377JacPoint`,
`PallasPoint`, `PallasJacPoint`) rather than reusing
`EcRealizationGeneric.ECAffPoint`/`ECJacPoint`.  Distinct `structure` declarations are not
definitionally equal even when field-for-field identical, so the per-curve *statements* are
not literally `@generic (ZMod p) …` and cannot be closed by `exact ec_…` against the
per-curve `Bls377Point`.  What we show instead (acceptable form (b) of the task) is that the
generic theorem, **instantiated at the curve's prime**, *coincides* with the per-curve one:
identical coordinate algebra over `ZMod bls377Q` / `ZMod pallasQ`, identical hypotheses.

A future cleanup can therefore either (i) replace the per-curve proof bodies with the
one-liners below (after a trivial structure-rename / `def`-unfold bridge), or (ii) drop the
per-curve EC structures entirely and re-export `ECAffPoint (ZMod bls377Q)` etc., pruning the
duplicated algebra.  Both are out of scope here (no committed file is touched); this witness
records the redundancy.

0 sorries; no custom axioms.  The numeral-nonvanishing facts are reused from the per-curve
files (`bls377_two_ne_zero`, …), which are themselves consequences of the section hypothesis
`[Fact (Nat.Prime ·Q)]` — not asserted axioms.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcGenericInstanceWitness

open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
open CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. BLS12-377: the generic ties at `F = ZMod bls377Q`

These are the generic realization theorems instantiated at the BLS12-377 base field,
discharging the four numeral-nonvanishing hypotheses with the per-curve lemmas
(`bls377_two_ne_zero`, …).  Each statement is the same field algebra as the per-curve
`bls377_jacDouble_realizes_affineDbl` / `bls377_jacAdd_realizes_affineAdd` — over the generic
`ECAffPoint (ZMod bls377Q)` carrier rather than `Bls377Point`. -/

section Bls377

variable [Fact (Nat.Prime bls377Q)]

/-- BLS12-377 point-double realization, obtained purely by instantiating the generic theorem
    at `ZMod bls377Q` — no `field_simp`/`ring`.  Coincides with
    `bls377_jacDouble_realizes_affineDbl` (same algebra, `Bls377Point` ≅ `ECAffPoint`). -/
theorem bls377_dbl_via_generic
    (P : ECAffPoint (ZMod bls377Q)) (hy : P.y ≠ 0) :
    ecJacToAffine (ecJacDouble (ECJacPoint.ofAffine P))
      = ecAffineDbl (ecTangentSlope P.x P.y) P :=
  @ec_jacDouble_realizes_affineDbl (ZMod bls377Q) _
    bls377_two_ne_zero bls377_three_ne_zero bls377_four_ne_zero bls377_eight_ne_zero P hy

/-- BLS12-377 point-add realization, again a pure `@`-instantiation of the generic theorem.
    Coincides with `bls377_jacAdd_realizes_affineAdd`. -/
theorem bls377_add_via_generic
    (P Q : ECAffPoint (ZMod bls377Q)) (hx : Q.x - P.x ≠ 0) :
    ecJacToAffine (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q))
      = ecAffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q :=
  @ec_jacAdd_realizes_affineAdd (ZMod bls377Q) _ P Q hx

end Bls377

/-! ## 2. Pallas: the generic ties at `F = ZMod pallasQ`

The same consolidation for the Pasta Pallas base field, reusing `pallas_two_ne_zero`, …. -/

section Pallas

variable [Fact (Nat.Prime pallasQ)]

/-- Pallas point-double realization, a pure `@`-instantiation of the generic theorem at
    `ZMod pallasQ`.  Coincides with `pallas_jacDouble_realizes_affineDbl`. -/
theorem pallas_dbl_via_generic
    (P : ECAffPoint (ZMod pallasQ)) (hy : P.y ≠ 0) :
    ecJacToAffine (ecJacDouble (ECJacPoint.ofAffine P))
      = ecAffineDbl (ecTangentSlope P.x P.y) P :=
  @ec_jacDouble_realizes_affineDbl (ZMod pallasQ) _
    pallas_two_ne_zero pallas_three_ne_zero pallas_four_ne_zero pallas_eight_ne_zero P hy

/-- Pallas point-add realization, a pure `@`-instantiation of the generic theorem.
    Coincides with `pallas_jacAdd_realizes_affineAdd`. -/
theorem pallas_add_via_generic
    (P Q : ECAffPoint (ZMod pallasQ)) (hx : Q.x - P.x ≠ 0) :
    ecJacToAffine (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q))
      = ecAffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q :=
  @ec_jacAdd_realizes_affineAdd (ZMod pallasQ) _ P Q hx

end Pallas

end CatCrypt.Crypto.SecureCompilation.EcGenericInstanceWitness
