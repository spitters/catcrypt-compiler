/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# `tower_ring_377`: coordinate-equality prover for the `bls12_377` `Fp6` tower

`tower_ring_377` proves an equality of `Fp2_377` / `Fp6_377` elements by
descending the tower to its base `ZMod bls377Q` coordinates and closing each with
a small `ring`.

The tower is `Fp6_377 = Fp2_377[v]/(v³−ξ₆)`, `Fp2_377 = FpBLS377[u]/(u²−ξ₂)` over
the base field `FpBLS377 = ZMod bls377Q`. So an `Fp6_377` equality is six
base-`ZMod` equalities. The `@[ext]` structure lemmas drive the descent; the
`Fp*_377` projection lemmas — the schoolbook multiply projections
`Fp2_377.mulSchoolbook_c0/c1`, the componentwise `add`/`sub`/`neg`/`zero`/`one`
projections at each level, and the `Fp6_377.mulSchoolbook` / `Fp6_377.mul₂`
multiply definitions — rewrite each projected product/sum into base arithmetic;
a per-coordinate `ring` closes each base goal.

This is the `Fp*_377`-tower analogue of `tower_ring`. The two differ in their
simp set: `tower_ring` targets the `Fp2Tower` projection lemmas (`Fp2.mul_c0`,
…); `tower_ring_377` targets the `Fp*_377` projection lemmas
(`Fp2_377.mulSchoolbook_c0`, …).

The descent is structural: `ring` runs only on a base-`ZMod` coordinate, never on
a whole tower element. Because the base `CommRing` instance `Fp2_377.commRing` is
`@[reducible]` and defined through the schoolbook multiply, a `ring` over a whole
`Fp6_377` element normalizes through that reducible instance; descending to the
base coordinates first keeps every `ring` call at base-`ZMod` size.

The simp set is limited to the `Fp2_377` / `Fp6_377` projection lemmas so this
tactic can be used inside the `Fp6_377.commRing` definition, before `mulByV` /
`Fp12_377` are declared. The projection lemma names are written fully qualified so
this module can be imported by `RelationalFrontBls377Fp6`, which both defines
those lemmas and uses this tactic.

## Forms

* `tower_ring_377` — descend via `ext`, rewrite the `Fp*_377` projections, close
  each base coordinate with `ring`.
* `tower_ring_377 [h₁, h₂]` — same, with `h₁, h₂` added to the coordinate rewrite
  set.
-/

@[expose] public section

/-- Descend a `bls12_377` `Fp6` tower-field equality (`Fp2_377` / `Fp6_377`) to
    its base `ZMod bls377Q` coordinates and close each with a small `ring`. See
    the module docstring. -/
syntax (name := towerRing377) "tower_ring_377"
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| tower_ring_377) =>
      `(tactic|
        (ext <;>
          simp only [CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.mulSchoolbook,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.mul₂,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.mulSchoolbook_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.mulSchoolbook_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.zero_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.zero_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.one_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.one_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.add_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.add_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.neg_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.neg_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.sub_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.sub_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.zero_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.zero_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.zero_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.one_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.one_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.one_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.add_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.add_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.add_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.neg_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.neg_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.neg_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.sub_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.sub_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.sub_c2] <;>
          ring))
  | `(tactic| tower_ring_377 [$hs,*]) =>
      `(tactic|
        (ext <;>
          simp only [CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.mulSchoolbook,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.mul₂,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.mulSchoolbook_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.mulSchoolbook_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.zero_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.zero_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.one_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.one_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.add_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.add_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.neg_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.neg_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.sub_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377.sub_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.zero_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.zero_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.zero_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.one_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.one_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.one_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.add_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.add_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.add_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.neg_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.neg_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.neg_c2,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.sub_c0,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.sub_c1,
            CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp6_377.sub_c2, $hs,*] <;>
          ring))
