/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CurveFieldRefinement
public import CatCrypt.Crypto.SecureCompilation.VIR.Refinement

/-!
# Mathlib-anchored refinement spine for the curve field multiplies

This file re-anchors the curve field-multiply correctness at **Mathlib's `ZMod p`
field** (the prime field, `Mathlib.Data.ZMod.Basic`) and proves the
emitted asm **refines** that field through the canonical `Refines` relation of
`VIR.Refinement` (the relation designed to match upstream Veir's
`Interpreter/Refinement`). The source of truth is native Lean — Mathlib's `ZMod p`
and Mathlib's `*` — not fiat-crypto and not a bespoke field-mul `def`. fiat-crypto
inspires only the *shape* of the Montgomery field-element decode `feval`; it is
never the spec.

## The spine (top-down)

```
SOURCE OF TRUTH:  Mathlib  (fun (ab : ZMod p × ZMod p) => ab.1 * ab.2)   -- the field
   |  Refines        (TOP rung: the fiat-INSPIRED Montgomery decode
   |                  feval p R z := (↑z : ZMod p) * (↑R)⁻¹, R = 2^(64·#limbs) a unit;
   |                  R-cancellation: feval(montred(vx·vy)) = feval vx · feval vy)
 montgomeryReduce / valLimbs            (the representation -- montgomeryMul_correct, in-tree)
   |  Refines        (LOWER rung: runBlockProductValue = vx·vy, the Tier-A
   |                  <curve>_emit_montmul_runBlock value, under feval∘montred congruence)
 runBlock(emitted List (JInstr 64))
```

`Refines.trans` composes the two rungs into, per curve,

    Refines (fun (ab : ZMod p × ZMod p) => ab.1 * ab.2) (decoded emitted kernel)

— "the emitted asm refines Mathlib's field multiplication." The carrier is the
denotation function `LeafRun → ZMod p`: `LeafRun` bundles one execution of the
emitted product block (state + the freshness/length/reducedness hypotheses the
Tier-A headline consumes); the **source** maps such a run to the Mathlib field
product `feval x · feval y` of its decoded inputs; the **target** maps it to the
`feval` decode of the emitted block's Montgomery-reduced `runBlock` output. Both
rungs are closed Lean theorems (`CurveFieldRefinement.<curve>_emit_refines_field`,
itself over the Tier-A `<curve>_emit_montmul_runBlock` and
`Number.montgomeryMul_correct`).

## Field product, not Montgomery-domain product

The `feval` decode `z ↦ (↑z)·(↑R)⁻¹` absorbs the single `R⁻¹` that the Montgomery
multiply carries, so the decoded kernel output is the **true** `ZMod p` field
product `feval x · feval y` of the decoded inputs — Mathlib's `*` on `ZMod p`, not
the Montgomery-domain `a·b·R⁻¹`. (The undecoded register value is the
Montgomery-domain residue; the source/target here live *after* the `feval`
decode, so the source is the field product. The to/from-Montgomery
conversions are the identity in the decoded view.) This is exactly the `Refines`
restatement of `CurveFieldRefinement.<curve>_emit_refines_field`.

## Above the field: the path to Mathlib's curve group law

The field operations are the leaves of the elliptic-curve group law. Mathlib's
`WeierstrassCurve` / `EllipticCurve` builds the affine/projective addition and
doubling formulae out of `ZMod p` field `+`, `-`, `*`, and `⁻¹`. Re-anchoring the
multiply leaf at Mathlib's `ZMod p` (this file) is the field-level rung of the
same `Refines.trans` chain that — composing the curve group law's field-op leaves —
reaches the `WeierstrassCurve.Affine.add` / `EllipticCurve` group spec. That curve
group law over `ZMod p` is the high-level mathematical anchor; the
field-multiply refinement here is its leaf. (The group-law rung is
stated here as the documented path, not proved: it needs the point-addition
schedule's `Refines` against `WeierstrassCurve.Affine.add`, which composes these
field-op refinements via `Refines.congr_postcomp`/`Refines.trans`.)
-/

@[expose] public section

set_option autoImplicit false
-- The Montgomery radices `2^256` / `2^384` appear as literals in the `ZMod p`
-- casts; we never evaluate them, so raise the exponentiation pretty-printer
-- threshold to silence the benign notices.
set_option exponentiation.threshold 400
set_option maxRecDepth 4000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CurveFieldMathlibSpec

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.PastaBignumTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.CurveFieldRefinement
open CatCrypt.Crypto.SecureCompilation.VIR.Refinement

/-! ## 1. One emitted-multiply execution, bundled

`LeafRun limbs Nprime` packages a single run of the emitted Montgomery product
block at a curve whose modulus is `valLimbs limbs`: the register names, the state
`s`, and exactly the hypotheses the Tier-A `<curve>_emit_montmul_runBlock` headline
consumes (matching lengths, capacity, the `ProdFresh` layout, inputs read from the
state, a cleared accumulator file, both carry flags clear, reduced inputs, and the
full-radix Montgomery constant relation). It is the varying domain of the
`Refines` carrier — refinement holds for *every* such run, not a single fixed
state. -/

/-- A single execution of the emitted Montgomery product block at modulus
    `valLimbs limbs`, with the Tier-A `runBlock` headline's hypotheses bundled. -/
structure LeafRun (limbs : List (BitVec 64)) (radix : Nat) where
  /-- accumulator-file register names -/
  accs : List String
  /-- `x`-limb source register names -/
  as : List String
  /-- `y`-limb scalar register names -/
  ys : List String
  /-- scratch high register -/
  hi : String
  /-- scratch low register -/
  lo : String
  /-- the machine state the block runs from -/
  s : JState 64
  /-- the full-radix Montgomery constant -/
  Nprime : Nat
  /-- the `x` input limbs -/
  x : List (BitVec 64)
  /-- the `y` input limbs -/
  yv : List (BitVec 64)
  haslen : as.length = x.length
  hyslen : ys.length = yv.length
  hcap : as.length + ys.length ≤ accs.length
  hfresh : ProdFresh accs as ys hi lo
  hx : as.map s.get = x
  hy : ys.map s.get = yv
  hacc0 : ∀ r ∈ accs, s.get r = 0
  hcf : s.flagB (·.cf) = false
  hof : s.flagB (·.of) = false
  hx_red : valLimbs x < valLimbs limbs
  hy_red : valLimbs yv < valLimbs limbs
  hNprime : (valLimbs limbs * Nprime) % radix = radix - 1

/-- The emitted block's Montgomery-reduced `runBlock` output (a `Nat` residue) for
    a bundled run. -/
def LeafRun.output {limbs : List (BitVec 64)} {radix : Nat} (r : LeafRun limbs radix) : Nat :=
  Number.montgomeryReduce (valLimbs limbs) radix r.Nprime
    (runBlockProductValue r.accs r.as r.ys r.hi r.lo r.s)

/-! ## 2. The three carriers and the two rungs (generic)

For a fixed curve `limbs`/`radix`, the spine is a `Refines.trans` of:

* **`fieldSrc`** — `fun r => feval p R (valLimbs r.x) * feval p R (valLimbs r.yv)`:
  Mathlib's field product of the decoded inputs (`*` on `ZMod p`);
* **`specMid`** — `fun r => feval p R (montred (valLimbs r.x · valLimbs r.yv))`:
  the decode of the Montgomery reduction of the *Nat product spec*;
* **`emitTgt`** — `fun r => feval p R r.output`: the decode of the emitted kernel.

The **top rung** `Refines fieldSrc specMid` is the R-cancellation (the leaf
congruence `montred(vx·vy)·R ≡ vx·vy` lifted into `ZMod p`); the **lower rung**
`Refines specMid emitTgt` is the Tier-A `runBlockProductValue = vx·vy` value
(`feval∘montred` applied to both sides). -/

/-- The Mathlib `ZMod p` field-product source: the field multiply of the
    decoded inputs. The spec object is Mathlib's `ZMod (valLimbs limbs)` and its `*`. -/
noncomputable def fieldSrc {limbs : List (BitVec 64)} {radix : Nat} :
    LeafRun limbs radix → ZMod (valLimbs limbs) :=
  fun r => feval (valLimbs limbs) radix (valLimbs r.x)
    * feval (valLimbs limbs) radix (valLimbs r.yv)

/-- The intermediate carrier: the `feval` decode of the Montgomery reduction of the
    `Nat` product spec `valLimbs x · valLimbs y`. -/
noncomputable def specMid {limbs : List (BitVec 64)} {radix : Nat} :
    LeafRun limbs radix → ZMod (valLimbs limbs) :=
  fun r => feval (valLimbs limbs) radix
    (Number.montgomeryReduce (valLimbs limbs) radix r.Nprime (valLimbs r.x * valLimbs r.yv))

/-- The emitted-kernel target carrier: the `feval` decode of the emitted block's
    Montgomery-reduced `runBlock` output. -/
noncomputable def emitTgt {limbs : List (BitVec 64)} {radix : Nat} :
    LeafRun limbs radix → ZMod (valLimbs limbs) :=
  fun r => feval (valLimbs limbs) radix r.output

/-- **Lower rung (generic).** The emitted target equals the spec-mid carrier,
    because the Tier-A headline's first conjunct gives
    `runBlockProductValue … = valLimbs x · valLimbs y`. A congruence under
    `feval ∘ montgomeryReduce`. -/
theorem refines_specMid_emitTgt {limbs : List (BitVec 64)} {radix : Nat}
    (hheadline : ∀ r : LeafRun limbs radix,
      runBlockProductValue r.accs r.as r.ys r.hi r.lo r.s = valLimbs r.x * valLimbs r.yv) :
    Refines (specMid (limbs := limbs) (radix := radix)) emitTgt := by
  intro r
  simp only [emitTgt, specMid, LeafRun.output, hheadline r]

/-- **Top rung (generic).** The spec-mid carrier equals the Mathlib field product,
    via the generic R-cancellation `feval_mont_of_modEq`: from the leaf congruence
    `montred(vx·vy)·R ≡ vx·vy [MOD p]` and `R` coprime to `p`, the decode of the
    Montgomery reduction is the field product of the decoded inputs. -/
theorem refines_fieldSrc_specMid {limbs : List (BitVec 64)} {radix : Nat}
    (hcop : Nat.Coprime radix (valLimbs limbs))
    (hcong : ∀ r : LeafRun limbs radix,
      (Number.montgomeryReduce (valLimbs limbs) radix r.Nprime (valLimbs r.x * valLimbs r.yv))
        * radix ≡ valLimbs r.x * valLimbs r.yv [MOD valLimbs limbs]) :
    Refines (fieldSrc (limbs := limbs) (radix := radix)) specMid := by
  intro r
  simp only [fieldSrc, specMid]
  exact feval_mont_of_modEq hcop _ _ _ (hcong r)

/-- **The composed Mathlib-anchored spine (generic).** `Refines.trans` of the two
    rungs: the emitted kernel refines Mathlib's `ZMod p` field product of the
    decoded inputs. -/
theorem refines_fieldSrc_emitTgt {limbs : List (BitVec 64)} {radix : Nat}
    (hcop : Nat.Coprime radix (valLimbs limbs))
    (hheadline : ∀ r : LeafRun limbs radix,
      runBlockProductValue r.accs r.as r.ys r.hi r.lo r.s = valLimbs r.x * valLimbs r.yv)
    (hcong : ∀ r : LeafRun limbs radix,
      (Number.montgomeryReduce (valLimbs limbs) radix r.Nprime (valLimbs r.x * valLimbs r.yv))
        * radix ≡ valLimbs r.x * valLimbs r.yv [MOD valLimbs limbs]) :
    Refines (fieldSrc (limbs := limbs) (radix := radix)) emitTgt :=
  Refines.trans (refines_fieldSrc_specMid hcop hcong) (refines_specMid_emitTgt hheadline)

/-! ## 3. The Tier-A headline supplies both rung hypotheses (generic)

For each curve, `<curve>_emit_montmul_runBlock` gives, per run, the first conjunct
`runBlockProductValue = vx·vy` (the lower-rung hypothesis) and, after rewriting the
argument by that value, the third conjunct's congruence `montred(vx·vy)·R ≡ vx·vy`
(the top-rung hypothesis). We package this as a generic "headline ⇒ both rung
hypotheses" combinator so each per-curve `Refines` is a one-line application. -/

/-- The shape of a Tier-A `<curve>_emit_montmul_runBlock` headline, abstracted over
    the curve. Each curve theorem is exactly this with `limbs`/`radix` fixed. -/
def TierAHeadline (limbs : List (BitVec 64)) (radix : Nat) : Prop :=
  ∀ (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime : Nat),
    as.length = x.length → ys.length = yv.length →
    as.length + ys.length ≤ accs.length →
    ProdFresh accs as ys hi lo →
    as.map s.get = x → ys.map s.get = yv →
    (∀ r ∈ accs, s.get r = 0) →
    s.flagB (·.cf) = false → s.flagB (·.of) = false →
    valLimbs x < valLimbs limbs → valLimbs yv < valLimbs limbs →
    (valLimbs limbs * Nprime) % radix = radix - 1 →
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs limbs) radix Nprime
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs limbs ∧
    (Number.montgomeryReduce (valLimbs limbs) radix Nprime
        (runBlockProductValue accs as ys hi lo s)) * radix
      ≡ valLimbs x * valLimbs yv [MOD valLimbs limbs]

/-- **Generic: a Tier-A headline + radix coprimality ⇒ the Mathlib-anchored
    `Refines`.** Discharges both rung hypotheses from the headline and concludes
    the emitted kernel refines Mathlib's `ZMod p` field product. The single
    combinator every per-curve theorem instantiates. -/
theorem refines_of_tierA {limbs : List (BitVec 64)} {radix : Nat}
    (hcop : Nat.Coprime radix (valLimbs limbs))
    (hA : TierAHeadline limbs radix) :
    Refines (fieldSrc (limbs := limbs) (radix := radix)) emitTgt := by
  refine refines_fieldSrc_emitTgt hcop (fun r => ?_) (fun r => ?_)
  · exact (hA r.accs r.as r.ys r.x r.yv r.hi r.lo r.s r.Nprime
      r.haslen r.hyslen r.hcap r.hfresh r.hx r.hy r.hacc0 r.hcf r.hof
      r.hx_red r.hy_red r.hNprime).1
  · obtain ⟨hval, _, hcong⟩ := hA r.accs r.as r.ys r.x r.yv r.hi r.lo r.s r.Nprime
      r.haslen r.hyslen r.hcap r.hfresh r.hx r.hy r.hacc0 r.hcf r.hof
      r.hx_red r.hy_red r.hNprime
    rwa [hval] at hcong

/-! ## 4. Per-curve `Refines` against Mathlib's `ZMod p` field multiply

Each headline below restates the proven Tier-A theorem as a `TierAHeadline`, then
`refines_of_tierA` discharges the spine. SOURCE is Mathlib's field product
`fieldSrc` on `ZMod (valLimbs <curve>Limbs)`; TARGET is the decoded emitted kernel
`emitTgt`. The radix is `2^256` (4-limb) or `2^384` (6-limb), a unit since each
prime is odd. -/

/-- secp256k1 Tier-A headline as a `TierAHeadline`. -/
theorem secp256k1_headline :
    TierAHeadline secp256k1Limbs (2 ^ 256) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact secp256k1_emit_montmul_runBlock accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **secp256k1: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐
    `Refines fieldSrc emitTgt` over `ZMod (valLimbs secp256k1Limbs)`: for every
    bundled run of the emitted Montgomery product block, the `feval` decode of its
    `runBlock` output equals Mathlib's field product `feval x · feval y` of the
    decoded inputs. Composed by `Refines.trans` from the Tier-A
    `secp256k1_emit_montmul_runBlock` value (lower rung) and the R-cancellation
    (top rung). The spec is Mathlib's `ZMod p` and `*`, not fiat. -/
theorem secp256k1_field_refines :
    Refines (fieldSrc (limbs := secp256k1Limbs) (radix := 2 ^ 256)) emitTgt :=
  refines_of_tierA secp256k1_coprime secp256k1_headline

/-- SM2 Tier-A headline as a `TierAHeadline`. -/
theorem sm2_headline :
    TierAHeadline sm2Limbs (2 ^ 256) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact sm2_emit_montmul_runBlock_full accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **SM2: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐ As
    `secp256k1_field_refines`, at the SM2 prime. -/
theorem sm2_field_refines :
    Refines (fieldSrc (limbs := sm2Limbs) (radix := 2 ^ 256)) emitTgt :=
  refines_of_tierA sm2_coprime sm2_headline

/-- P256 Tier-A headline as a `TierAHeadline`. -/
theorem p256_headline :
    TierAHeadline p256Limbs (2 ^ 256) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact p256_emit_montmul_runBlock accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **P256: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐ -/
theorem p256_field_refines :
    Refines (fieldSrc (limbs := p256Limbs) (radix := 2 ^ 256)) emitTgt :=
  refines_of_tierA p256_coprime p256_headline

/-- BN254 Tier-A headline as a `TierAHeadline`. -/
theorem bn254_headline :
    TierAHeadline bn254Limbs (2 ^ 256) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact bn254_emit_montmul_runBlock accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **BN254: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐ -/
theorem bn254_field_refines :
    Refines (fieldSrc (limbs := bn254Limbs) (radix := 2 ^ 256)) emitTgt :=
  refines_of_tierA bn254_coprime bn254_headline

/-- P384 Tier-A headline as a `TierAHeadline` (radix `2^384`). -/
theorem p384_headline :
    TierAHeadline p384Limbs (2 ^ 384) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact p384_emit_montmul_runBlock accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **P384: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐
    Radix `2^384`. -/
theorem p384_field_refines :
    Refines (fieldSrc (limbs := p384Limbs) (radix := 2 ^ 384)) emitTgt :=
  refines_of_tierA p384_coprime p384_headline

/-- BLS12-381 Tier-A headline as a `TierAHeadline` (radix `2^384`). -/
theorem bls12381_headline :
    TierAHeadline bls12381Limbs (2 ^ 384) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact bls12381_emit_montmul_runBlock accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **BLS12-381: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐
    Radix `2^384`. The base-field leaf under `Bls12381TowerTierA.fpMul`, here in
    the uniform Mathlib `ZMod p` `Refines` shape. -/
theorem bls12381_field_refines :
    Refines (fieldSrc (limbs := bls12381Limbs) (radix := 2 ^ 384)) emitTgt :=
  refines_of_tierA bls12381_coprime bls12381_headline

/-- Pallas Tier-A headline as a `TierAHeadline`. -/
theorem pallas_headline :
    TierAHeadline pallasLimbs (2 ^ 256) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact pallas_emit_montmul_runBlock accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **Pallas: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐ -/
theorem pallas_field_refines :
    Refines (fieldSrc (limbs := pallasLimbs) (radix := 2 ^ 256)) emitTgt :=
  refines_of_tierA pallas_coprime pallas_headline

/-- Vesta Tier-A headline as a `TierAHeadline`. -/
theorem vesta_headline :
    TierAHeadline vestaLimbs (2 ^ 256) := by
  intro accs as ys x yv hi lo s Nprime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact vesta_emit_montmul_runBlock accs as ys x yv hi lo s Nprime
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- **Vesta: the emitted asm refines Mathlib's `ZMod p` field multiply.** ⭐ -/
theorem vesta_field_refines :
    Refines (fieldSrc (limbs := vestaLimbs) (radix := 2 ^ 256)) emitTgt :=
  refines_of_tierA vesta_coprime vesta_headline

end CatCrypt.Crypto.SecureCompilation.X86Backend.CurveFieldMathlibSpec
