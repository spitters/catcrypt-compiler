/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul_CompPoly
import CatCrypt.Crypto.SecureCompilation.ConcreteNttEmitRealization

/-!
# Pass 3.1 — the NTT poly-mul agreement, reduced to leaf realization

This file is the final structural link in the NTT-multiply chain: it ties the
**compiler-pass soundness obligation** `nttAgreesPolyMul` (the per-leaf
agreement predicate that gates `nttPolyMulMlkem_denote_eq`) to the
**emit→realization** machinery (`NttEmitRealizes`, the predicate that an
emitted leaf decodes to the abstract NTT-multiply value).

## The two predicates, and why they do not coincide on the nose

`nttAgreesPolyMul leafSpec q n` (`NTTPolyMul.lean §3`) asserts agreement on
**raw** leaf values, **universally over every call signature**:

```
∀ (f : String) (dt : TowerType) (argTs : List TowerType)
  (oldV : RustVal dt) (args : List (Σ t, RustVal t)),
  isPolyMulName f = true →
  leafSpec.call (nttPolyMulName q n) dt argTs oldV args
    = leafSpec.call f dt argTs oldV args
```

It is an equality of `RustVal dt` values (the raw oracle outputs), quantified
over **all** `dt`, `argTs`, `oldV`, `args` — not just the canonical NTT
binary signature.

`NttEmitRealizes n ω decode leaf leafSpec`
(`GenericNttEmitValue.lean §1`) constrains the leaf at exactly **one** call
signature — `dt = .TFp`, `argTs = [.TFp, .TFp]`,
`args = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]` — and at the **decoded** level:

```
decode (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
  = nttMul n ω (decode aVal) (decode bVal)
```

Two gaps therefore separate "both leaves realize the same product" from
`nttAgreesPolyMul`:

1. **Decoded vs. raw.**  `NttEmitRealizes` pins the *decoded* coefficient
   vector, while `nttAgreesPolyMul` is an equality of *raw* `RustVal`s.
   Lifting decoded-equality to raw-equality needs `decode` **injective** on
   the `.TFp` carrier.
2. **One signature vs. all signatures.**  `NttEmitRealizes` only constrains
   the canonical `.TFp`-binary call; `nttAgreesPolyMul` quantifies over every
   `dt`/`argTs`/`args`.  Off the canonical signature, the leaves must be made
   to agree by construction (both off-target branches return `oldV`, as in the
   canonical `nttKernelCallSpec`) — that off-signature agreement is a separate
   structural fact about the `LeafSpec`, not delivered by the realization.

## What this file proves

* `nttLeaves_agree_on_canonical_sig` — **on the canonical NTT signature**, if
  the NTT leaf realizes `nttMul` and the `"poly_mul"` leaf realizes the *same*
  `nttMul`, then under `decode` injectivity the two leaves return **equal raw
  values**.  This is the genuine content the realization machinery delivers:
  it discharges gap (1) at the canonical signature.

* `nttAgreesPolyMul_of_realize_and_offsig` — the full reduction: from the two
  realizations (NTT leaf and both poly-mul spellings realize the same product),
  `decode` injectivity, **and** an explicit off-signature raw-agreement
  hypothesis, conclude `nttAgreesPolyMul leafSpec q n` via
  `NTTPolyMul.nttAgreesPolyMul_of_pointwise`.  The off-signature hypothesis is
  the residual obligation; it is satisfied by-construction for a canonical
  `LeafSpec` whose poly-mul leaves dispatch to the same kernel.

* `mlkem_nttAgreesPolyMul_of_realize_and_offsig` — the ML-KEM specialisation,
  at `(q, n) = (3329, 256)`, `ω = 17`, leaf `"ntt_poly_mul_3329_256"`, feeding
  the conclusion directly into `nttPolyMulMlkem_denote_eq`.

## Honesty: conditional, not unconditional

This connection is **conditional**, on two named residuals:

* `decode`-injectivity on the `.TFp` carrier (gap 1), and
* off-canonical-signature raw agreement of the NTT and poly-mul leaves (gap 2).

Both are genuine, separate from the algebraic NTT-multiply correctness (which
is already discharged: `nttMul = cyclicConv` via `nttMul_eq_cyclicConv'`, and
the ML-KEM primitive root via `isPrimitiveRoot_17_256`).  A fully *grounded,
unconditional* `nttAgreesPolyMul mlkemLeafSpec 3329 256` would require a
concrete `mlkemLeafSpec` carrying a `decode`/`encode` round trip
(`decode_encode = id` and `encode_decode = id`, the latter being the injectivity
witness) and an off-signature `oldV`-pass-through law — exactly the
`PolyEncoding` reification deferred by `NTTPolyMul_CompPoly.lean §"The remaining
gap"`.  We do **not** fabricate such a `LeafSpec` here (doing so would smuggle
in the conclusion); we expose the residuals as hypotheses.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.NttPassAlgebraBridge

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
open CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
open CatCrypt.Crypto.SecureCompilation.ConcreteNttEmitRealization

variable {R : Type*} [Field R]

/-! ## §1  Canonical-signature raw agreement from two realizations

The realization machinery delivers agreement at the **decoded** level on the
canonical `.TFp`-binary signature.  Under `decode` injectivity this lifts to
**raw** value equality — the form `nttAgreesPolyMul` needs at that signature. -/

/-- **Canonical-signature raw agreement.**  If the NTT leaf realizes
    `nttMul n ω` (`hntt : NttEmitRealizes …`) and the source `poly` leaf
    realizes the *same* `nttMul n ω` (`hpoly`), then under `decode` injectivity
    the two leaves return **equal raw `RustVal`s** on every canonical
    `.TFp`-binary call.

    This discharges the decoded-vs-raw gap at the canonical signature: both
    decode to `nttMul n ω (decode aVal) (decode bVal)`, hence are equal raw
    values once `decode` is injective. -/
theorem nttLeaves_agree_on_canonical_sig
    {n : ℕ} {ω : R} {decode : RustVal .TFp → (Fin n → R)}
    {nttLeaf polyLeaf : String} {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hntt : NttEmitRealizes n ω decode nttLeaf leafSpec)
    (hpoly : NttEmitRealizes n ω decode polyLeaf leafSpec) :
    ∀ (oldDest aVal bVal : RustVal .TFp),
      leafSpec.call nttLeaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]
        = leafSpec.call polyLeaf .TFp [.TFp, .TFp] oldDest
            [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩] := by
  intro oldDest aVal bVal
  apply hdec
  rw [hntt aVal bVal oldDest, hpoly aVal bVal oldDest]

/-! ## §2  Full agreement, reduced to off-signature agreement

`nttAgreesPolyMul` quantifies over **all** call signatures, while §1 only
covers the canonical `.TFp`-binary one.  Off the canonical signature the two
leaves must already agree (by construction of the `LeafSpec`).  We take that as
an explicit hypothesis and feed the trivial-lift
`NTTPolyMul.nttAgreesPolyMul_of_pointwise`. -/

/-- **The full reduction.**  From:
    * `hntt` — the NTT leaf realizes `nttMul n ω`,
    * `hpm` / `hpmul` — the `"poly_mul"` / `"polymul"` leaves realize the same
      `nttMul n ω`,
    * `hdec` — `decode` is injective on the `.TFp` carrier, and
    * `hoff'` — the NTT leaf and the source poly-mul leaves agree **off** the
      canonical `.TFp`-binary signature (raw values),

    conclude the compiler-pass obligation `nttAgreesPolyMul leafSpec q n`.

    The canonical-signature obligation is discharged by §1
    (`nttLeaves_agree_on_canonical_sig`); the off-signature obligation is `hoff'`;
    together they give the universal pointwise raw agreement that
    `nttAgreesPolyMul_of_pointwise` lifts to `nttAgreesPolyMul`.

    Conditional on `hdec` and `hoff'` — see the module docstring for why these
    are the genuine residuals (the `PolyEncoding` round trip + the
    off-signature pass-through law). -/
theorem nttAgreesPolyMul_of_realize_and_offsig
    {q n : Nat} {ω : R} {decode : RustVal .TFp → (Fin n → R)}
    {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hntt : NttEmitRealizes n ω decode (nttPolyMulName q n) leafSpec)
    (hpm : NttEmitRealizes n ω decode "poly_mul" leafSpec)
    (hpmul : NttEmitRealizes n ω decode "polymul" leafSpec)
    (hoff' : ∀ (src : String) (dt : TowerType) (argTs : List TowerType)
        (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
        ¬ (dt = TowerType.TFp ∧ argTs = [TowerType.TFp, TowerType.TFp]
          ∧ ∃ aVal bVal : RustVal .TFp,
              args = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) →
        leafSpec.call (nttPolyMulName q n) dt argTs oldV args
          = leafSpec.call src dt argTs oldV args) :
    nttAgreesPolyMul leafSpec q n := by
  apply nttAgreesPolyMul_of_pointwise
  · -- "poly_mul" spelling
    intro dt argTs oldV args
    by_cases hsig : dt = TowerType.TFp ∧ argTs = [TowerType.TFp, TowerType.TFp]
        ∧ ∃ aVal bVal : RustVal .TFp, args = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]
    · obtain ⟨hdt, hargTs, aVal, bVal, hargs⟩ := hsig
      subst hdt; subst hargTs; subst hargs
      exact nttLeaves_agree_on_canonical_sig hdec hntt hpm oldV aVal bVal
    · exact hoff' "poly_mul" dt argTs oldV args hsig
  · -- "polymul" spelling
    intro dt argTs oldV args
    by_cases hsig : dt = TowerType.TFp ∧ argTs = [TowerType.TFp, TowerType.TFp]
        ∧ ∃ aVal bVal : RustVal .TFp, args = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]
    · obtain ⟨hdt, hargTs, aVal, bVal, hargs⟩ := hsig
      subst hdt; subst hargTs; subst hargs
      exact nttLeaves_agree_on_canonical_sig hdec hntt hpmul oldV aVal bVal
    · exact hoff' "polymul" dt argTs oldV args hsig

/-! ## §3  ML-KEM specialisation, into `nttPolyMulMlkem_denote_eq`

At `(q, n) = (3329, 256)`, `ω = 17`, the NTT-leaf realization can be supplied
from the leaf-bytes KAT `NttKernelRealizes` via the proven commuting square
`ConcreteNttEmitRealization.mlkem_nttEmitRealizes_of_kernel`
(`isPrimitiveRoot_17_256` + `n_ne_zero_3329`).  The two source poly-mul leaves
must likewise realize `nttMul 256 17`.  Note `nttPolyMulName 3329 256`
reduces to `"ntt_poly_mul_3329_256"`, the literal the compiler pass emits. -/

/-- **ML-KEM: the compiler-pass agreement obligation from the leaf-bytes KAT.**

    Supplying the NTT leaf's realization from the ML-KEM kernel KAT
    (`hker : NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec`,
    lifted through the proven commuting square), plus realizations of both
    poly-mul spellings, `decode` injectivity, and the off-signature
    pass-through law, conclude `nttAgreesPolyMul leafSpec 3329 256` — exactly
    the hypothesis that gates `nttPolyMulMlkem_denote_eq`.

    Conditional on the same two residuals as §2 (`hdec`, `hoff'`), plus the
    poly-mul leaves realizing the cyclic-convolution value. -/
theorem mlkem_nttAgreesPolyMul_of_realize_and_offsig
    {decode : RustVal .TFp → (Fin 256 → ZMod 3329)} {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hker : NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec)
    (hpm : NttEmitRealizes 256 (17 : ZMod 3329) decode "poly_mul" leafSpec)
    (hpmul : NttEmitRealizes 256 (17 : ZMod 3329) decode "polymul" leafSpec)
    (hoff' : ∀ (src : String) (dt : TowerType) (argTs : List TowerType)
        (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
        ¬ (dt = TowerType.TFp ∧ argTs = [TowerType.TFp, TowerType.TFp]
          ∧ ∃ aVal bVal : RustVal .TFp,
              args = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) →
        leafSpec.call (nttPolyMulName 3329 256) dt argTs oldV args
          = leafSpec.call src dt argTs oldV args) :
    nttAgreesPolyMul leafSpec 3329 256 :=
  nttAgreesPolyMul_of_realize_and_offsig hdec
    (mlkem_nttEmitRealizes_of_kernel decode leafSpec hker) hpm hpmul hoff'

/-- **ML-KEM: discharge of `nttPolyMulMlkem_denote_eq`'s hypothesis, threaded.**

    The denotational-equivalence theorem `nttPolyMulMlkem_denote_eq` (the
    pass's soundness anchor) becomes available once the agreement obligation is
    supplied.  This restates it with the obligation discharged from the
    realization residuals: for any source command `c` and states `rs`, `rs'`,
    `nttPolyMulMlkem c` and `c` have identical big-step behaviour. -/
theorem nttPolyMulMlkem_denote_eq_of_realize
    {decode : RustVal .TFp → (Fin 256 → ZMod 3329)} {leafSpec : LeafSpec}
    (hdec : Function.Injective decode)
    (hker : NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec)
    (hpm : NttEmitRealizes 256 (17 : ZMod 3329) decode "poly_mul" leafSpec)
    (hpmul : NttEmitRealizes 256 (17 : ZMod 3329) decode "polymul" leafSpec)
    (hoff' : ∀ (src : String) (dt : TowerType) (argTs : List TowerType)
        (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
        ¬ (dt = TowerType.TFp ∧ argTs = [TowerType.TFp, TowerType.TFp]
          ∧ ∃ aVal bVal : RustVal .TFp,
              args = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) →
        leafSpec.call (nttPolyMulName 3329 256) dt argTs oldV args
          = leafSpec.call src dt argTs oldV args)
    (N : Nat) (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (nttPolyMulMlkem c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  nttPolyMulMlkem_denote_eq N leafSpec
    (mlkem_nttAgreesPolyMul_of_realize_and_offsig hdec hker hpm hpmul hoff')
    c rs rs'

end CatCrypt.Crypto.SecureCompilation.NttPassAlgebraBridge
