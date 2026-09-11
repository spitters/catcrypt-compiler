/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
public import CatCrypt.Crypto.SecureCompilation.NttPassAlgebraBridge

/-!
# Pass 3.1 — discharging the off-signature residual of the NTT pass→algebra bridge

`NttPassAlgebraBridge.lean` reduced the compiler-pass obligation
`nttAgreesPolyMul` to **two** residuals:

1. `decode`-injectivity on the `.TFp` carrier (gap 1), and
2. an explicit *off-canonical-signature raw agreement* hypothesis `hoff'`
   (gap 2) — that the NTT leaf and the source poly-mul leaves return equal raw
   `RustVal`s on every call signature **other** than the canonical
   `.TFp`-binary one.

This file turns residual (2) from a *hypothesis* into a *theorem* for a
concrete class of realizers — the **pass-through realizers**, whose leaves
return the destination's previous value `oldV` unchanged off the canonical
signature (exactly the off-target behaviour of the canonical
`nttKernelCallSpec`).  For such a realizer both leaves return `oldV` off the
canonical signature, so they agree there for free.

## What this file proves

* `OffSigPassThrough leafSpec q n` — the structural predicate: off the
  canonical binary `.TFp` signature, the NTT leaf **and** every poly-mul-named
  leaf return `oldV` (pass-through).

* `offSig_agree_of_passThrough` — from `OffSigPassThrough`, the off-signature
  raw-agreement obligation `hoff'` of the bridge follows (both sides reduce to
  `oldV`).

* `nttAgreesPolyMul_of_realize` — the **assembled** reduction: from
  `decode`-injectivity, the NTT and poly-mul leaves realizing the same product,
  and `OffSigPassThrough`, conclude `nttAgreesPolyMul leafSpec q n`.  This
  removes the `hoff'` residual, leaving only the three **structural** realizer
  properties (injectivity, realization×2, pass-through).

* `mlkem_nttAgreesPolyMul_of_realize` / `mlkem_nttPolyMulMlkem_denote_eq_of_realize`
  — the ML-KEM `(q, n) = (3329, 256)` specialisations, the latter threading the
  agreement into the pass's denotational-equivalence anchor
  `nttPolyMulMlkem_denote_eq` with **no** `hoff'` left.

## Honesty: the remaining inputs are all structural

After this file the inputs to the ML-KEM pass soundness are exactly:

* (a) `decode`-injectivity on the `.TFp` carrier,
* (b) the NTT leaf and both poly-mul spellings realize the cyclic-convolution
  product (`NttEmitRealizes` / `NttKernelRealizes`), and
* (c) off-signature pass-through (`OffSigPassThrough`).

All three are **structural properties of a concrete realizer**.  A sibling
file `ConcreteNttRealizer.lean` is constructing the concrete encoding (an
injective `decode`, a product-realizing `leafSpec`, and the `oldV`
pass-through law); we deliberately do **not** import it and instead keep (a)
(b)(c) as hypotheses so this result composes with whatever concrete realizer
discharges them.  Instantiating (a)(b)(c) with that concrete realizer yields
the fully *unconditional* `nttAgreesPolyMul mlkemLeafSpec 3329 256` and hence
the unconditional ML-KEM pass soundness — we do not claim it here, since (a)
(b)(c) are not yet grounded in this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.NttPassBridgeComplete

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
open CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
open CatCrypt.Crypto.SecureCompilation.ConcreteNttEmitRealization
open CatCrypt.Crypto.SecureCompilation.NttPassAlgebraBridge

variable {R : Type*} [Field R]

/-! ## §1  The off-signature pass-through predicate

The bridge's off-signature residual `hoff'` asks for raw agreement of the NTT
leaf and the source poly-mul leaves on every **non-canonical** signature.  The
clean way to make that a theorem (rather than a hypothesis) is to restrict to
realizers that **pass `oldV` through** off the canonical signature — exactly
the off-target behaviour of the canonical `nttKernelCallSpec`.

`OffSigPassThrough leafSpec q n` says: at any call signature that is *not* the
canonical `.TFp`-binary one, both the NTT leaf `nttPolyMulName q n` and **every
poly-mul-named** leaf `f` return the destination's previous value `oldV`. -/

/-- The canonical NTT call signature: destination type `.TFp`, two `.TFp`
    arguments.  A call signature `(dt, argTs, args)` matches iff `dt = .TFp`,
    `argTs = [.TFp, .TFp]`, and `args` is a two-element `.TFp`-tagged list. -/
def IsCanonicalSig (dt : TowerType) (argTs : List TowerType)
    (args : List (Σ t : TowerType, RustVal t)) : Prop :=
  dt = TowerType.TFp ∧ argTs = [TowerType.TFp, TowerType.TFp]
    ∧ ∃ aVal bVal : RustVal .TFp, args = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]

/-- **Off-signature pass-through.**  Off the canonical `.TFp`-binary signature,
    the NTT leaf and every poly-mul-named leaf return the destination's
    previous value `oldV` (pass-through).  This is the off-target behaviour of
    the canonical `nttKernelCallSpec`, and it is a purely structural property of
    the `LeafSpec` — separate from the realization content. -/
def OffSigPassThrough (leafSpec : LeafSpec) (q n : Nat) : Prop :=
  ∀ (dt : TowerType) (argTs : List TowerType)
    (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
    ¬ IsCanonicalSig dt argTs args →
    leafSpec.call (nttPolyMulName q n) dt argTs oldV args = oldV
      ∧ (∀ f : String, isPolyMulName f = true →
          leafSpec.call f dt argTs oldV args = oldV)

/-- **Off-signature raw agreement from pass-through.**  If `leafSpec` passes
    `oldV` through off the canonical signature (`OffSigPassThrough`), then the
    NTT leaf and any poly-mul-named source leaf return **equal raw values**
    there — both reduce to `oldV`.  This is exactly the off-signature
    raw-agreement shape the canonical bridge reduction needs, restricted to
    poly-mul-named sources (the only sources it is applied to). -/
theorem offSig_agree_of_passThrough
    {q n : Nat} {leafSpec : LeafSpec}
    (hpass : OffSigPassThrough leafSpec q n)
    {src : String} (hsrc : isPolyMulName src = true)
    {dt : TowerType} {argTs : List TowerType}
    {oldV : RustVal dt} {args : List (Σ t : TowerType, RustVal t)}
    (hsig : ¬ IsCanonicalSig dt argTs args) :
    leafSpec.call (nttPolyMulName q n) dt argTs oldV args
      = leafSpec.call src dt argTs oldV args := by
  obtain ⟨hntt, hsrcLeaf⟩ := hpass dt argTs oldV args hsig
  rw [hntt, hsrcLeaf src hsrc]

/-! ## §2  The assembled reduction — `hoff'` removed

We rebuild the full pointwise agreement directly on
`NTTPolyMul.nttAgreesPolyMul_of_pointwise`, splitting each of the two poly-mul
spellings on the canonical signature: on the canonical signature use the
bridge's `nttLeaves_agree_on_canonical_sig` (realization + injectivity); off it
use `offSig_agree_of_passThrough` (structural pass-through).  This routes
around the bridge's `nttAgreesPolyMul_of_realize_and_offsig`, whose off-signature
hypothesis is stated for an *arbitrary* source name; here we only ever need the
two poly-mul-named spellings, so the pass-through structural property cleanly
discharges the off-signature side. -/

/-- **Per-source pointwise agreement.**  For a poly-mul-named source `src`
    realizing the same product as the NTT leaf, the NTT leaf and `src` agree on
    **every** call signature: canonical (via `nttLeaves_agree_on_canonical_sig`
    under injectivity) and off-canonical (via pass-through). -/
theorem nttLeaf_agree_src
    {q n : Nat} {ω : R} {decode : RustVal .TFp → (Fin n → R)}
    {src : String} {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hntt : NttEmitRealizes n ω decode (nttPolyMulName q n) leafSpec)
    (hsrcReal : NttEmitRealizes n ω decode src leafSpec)
    (hsrc : isPolyMulName src = true)
    (hpass : OffSigPassThrough leafSpec q n) :
    ∀ (dt : TowerType) (argTs : List TowerType)
      (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
      leafSpec.call (nttPolyMulName q n) dt argTs oldV args =
        leafSpec.call src dt argTs oldV args := by
  intro dt argTs oldV args
  by_cases hsig : IsCanonicalSig dt argTs args
  · obtain ⟨hdt, hargTs, aVal, bVal, hargs⟩ := hsig
    subst hdt; subst hargTs; subst hargs
    exact nttLeaves_agree_on_canonical_sig hdec hntt hsrcReal oldV aVal bVal
  · exact offSig_agree_of_passThrough hpass hsrc hsig

/-- **The assembled reduction.**  From:
    * `hdec` — `decode` injective on the `.TFp` carrier,
    * `hntt` — the NTT leaf realizes `nttMul n ω`,
    * `hpm` / `hpmul` — the `"poly_mul"` / `"polymul"` leaves realize the same
      `nttMul n ω`, and
    * `hpass` — off-signature pass-through (`OffSigPassThrough`),

    conclude the compiler-pass obligation `nttAgreesPolyMul leafSpec q n`.

    Compared with the bridge's `nttAgreesPolyMul_of_realize_and_offsig`, the
    explicit off-signature raw-agreement hypothesis `hoff'` is **gone**: it is
    derived from the structural pass-through property `hpass` via
    `offSig_agree_of_passThrough`.  The remaining inputs are the three
    structural realizer properties — injectivity, realization (×2), and
    pass-through. -/
theorem nttAgreesPolyMul_of_realize
    {q n : Nat} {ω : R} {decode : RustVal .TFp → (Fin n → R)}
    {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hntt : NttEmitRealizes n ω decode (nttPolyMulName q n) leafSpec)
    (hpm : NttEmitRealizes n ω decode "poly_mul" leafSpec)
    (hpmul : NttEmitRealizes n ω decode "polymul" leafSpec)
    (hpass : OffSigPassThrough leafSpec q n) :
    nttAgreesPolyMul leafSpec q n :=
  nttAgreesPolyMul_of_pointwise
    (nttLeaf_agree_src hdec hntt hpm isPolyMulName_poly_mul hpass)
    (nttLeaf_agree_src hdec hntt hpmul isPolyMulName_polymul hpass)

/-! ## §3  ML-KEM specialisation, into `nttPolyMulMlkem_denote_eq` -/

/-- **ML-KEM: the compiler-pass agreement obligation from realizer-structural
    properties.**  At `(q, n) = (3329, 256)`, `ω = 17`, with the NTT leaf's
    realization supplied from the ML-KEM kernel KAT
    (`hker : NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec`,
    lifted through the proven commuting square `mlkem_nttEmitRealizes_of_kernel`),
    plus realizations of both poly-mul spellings, `decode` injectivity, and the
    off-signature pass-through law, conclude `nttAgreesPolyMul leafSpec 3329 256`.

    No `hoff'` residual remains: the inputs are exactly injectivity,
    realization (×2 + the kernel KAT), and pass-through — all structural. -/
theorem mlkem_nttAgreesPolyMul_of_realize
    {decode : RustVal .TFp → (Fin 256 → ZMod 3329)} {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hker : NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec)
    (hpm : NttEmitRealizes 256 (17 : ZMod 3329) decode "poly_mul" leafSpec)
    (hpmul : NttEmitRealizes 256 (17 : ZMod 3329) decode "polymul" leafSpec)
    (hpass : OffSigPassThrough leafSpec 3329 256) :
    nttAgreesPolyMul leafSpec 3329 256 :=
  nttAgreesPolyMul_of_realize hdec
    (mlkem_nttEmitRealizes_of_kernel decode leafSpec hker) hpm hpmul hpass

/-- **ML-KEM: pass soundness from realizer-structural properties, threaded.**

    The denotational-equivalence theorem `nttPolyMulMlkem_denote_eq` (the
    pass's soundness anchor) with its agreement obligation discharged from the
    realizer-structural inputs — injectivity, realization, and pass-through —
    with **no** `hoff'` residual.  For any source command `c` and states `rs`,
    `rs'`, `nttPolyMulMlkem c` and `c` have identical big-step behaviour. -/
theorem mlkem_nttPolyMulMlkem_denote_eq_of_realize
    {decode : RustVal .TFp → (Fin 256 → ZMod 3329)} {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hker : NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec)
    (hpm : NttEmitRealizes 256 (17 : ZMod 3329) decode "poly_mul" leafSpec)
    (hpmul : NttEmitRealizes 256 (17 : ZMod 3329) decode "polymul" leafSpec)
    (hpass : OffSigPassThrough leafSpec 3329 256)
    (N : Nat) (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (nttPolyMulMlkem c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  nttPolyMulMlkem_denote_eq N leafSpec
    (mlkem_nttAgreesPolyMul_of_realize hdec hker hpm hpmul hpass)
    c rs rs'

end CatCrypt.Crypto.SecureCompilation.NttPassBridgeComplete
