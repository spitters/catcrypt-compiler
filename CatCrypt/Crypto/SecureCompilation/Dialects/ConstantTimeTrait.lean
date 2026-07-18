/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ThirCTSafe

/-!
# D5: the reusable constant-time-by-construction trait

This file is the **D5 phase** of the MLIR dialect-alignment restructure: the
verification overlay's *constant-time-by-construction* trait.

The in-tree CT-by-construction mechanism — the `thir` front whose
well-formedness *is* constant-time (`VIR.ThirCTSafe`), and more generally the
LowCT "no secret-dependent addressing" invariant — always has the same shape:

  * a **predicate** `ctSafe : T → Prop` over an IR's terms (a syntactic
    well-formedness condition that an IR can satisfy *by construction*), and
  * a **leakage observation** `leakageOf : T → Leakage` together with a notion
    `publicLeakage` of "this leakage reveals nothing secret", and
  * a **soundness witness** `ct_sound` that the predicate implies public
    leakage.

`ConstantTimeTrait` abstracts exactly that triple. It is deliberately small:
the whole content is the soundness arrow `ctSafe t → publicLeakage (leakageOf t)`.
That is the only thing every CT overlay shares, and it is enough to compose.

We then **instantiate it on the real `thir` mechanism**: the load-bearing
instance wires
  * `ctSafe   := jComNoMem c = true`   (the THIR-front CT-by-construction
    invariant: the lowered Jasmin `Com` contains no memory op — see
    `ThirCTSafe.jComNoMem` and the `lowerThir_noMem` discharge),
  * `Leakage  := LabelCtxt Γ → Bool`   (the addressing-leakage trace, indexed by
    the label context the program is linked under),
  * `publicLeakage ℓ := ∀ L, ℓ L = true`   (the leakage is public iff CT-safe
    under *every* labelling — the robust-CT reading), and
  * `ct_sound := ThirCTSafe.noMem_ctSafeJasmin`   (the genuine, proven soundness
    lemma of the THIR front).

So the abstraction is demonstrated by a real instance backed by the real proven
mechanism, not a vacuous shell. Other layers (`arith` / `memref` / the machine
backend) can opt in by giving their own `ConstantTimeTrait` instance; the
derived lemma `ctSafe_leakage_public` below then applies to them generically.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirCTSafe

/-! ## 1. The reusable trait -/

/-- **Constant-time-by-construction trait.** An IR term type `T` carries a
    constant-time overlay when it has a syntactic well-formedness predicate
    `ctSafe`, a leakage observation `leakageOf` into some `Leakage` type, a
    notion `publicLeakage` of leakage that betrays no secret, and — the only
    real content — a soundness proof that `ctSafe` implies public leakage.

    Instantiated for `thir` below; in principle instantiable for `arith`,
    `memref`, and the machine layer too. The point of the abstraction is the
    generic `ct_sound` arrow: any client that establishes `ctSafe t` obtains
    `publicLeakage (leakageOf t)` without knowing which IR `T` is. -/
class ConstantTimeTrait (T : Type) where
  /-- The CT-by-construction well-formedness predicate on terms. -/
  ctSafe : T → Prop
  /-- The type of leakage a term can produce (addresses, control flow, …). -/
  Leakage : Type
  /-- The leakage a given term produces. -/
  leakageOf : T → Leakage
  /-- Which leakages reveal nothing secret. -/
  publicLeakage : Leakage → Prop
  /-- **Soundness**: well-formed terms leak only public information. -/
  ct_sound : ∀ t, ctSafe t → publicLeakage (leakageOf t)

/-! ## 2. A derived lemma over the abstract trait -/

/-- The trait is usable generically: from `ctSafe t` we get public leakage for
    *any* IR with a `ConstantTimeTrait` instance, with no knowledge of `T`,
    `Leakage`, or the concrete predicates. This is just `ct_sound` repackaged as
    a client-facing entry point — clients call this, not the class field. -/
theorem ctSafe_leakage_public {T : Type} [ConstantTimeTrait T] (t : T)
    (h : ConstantTimeTrait.ctSafe t) :
    ConstantTimeTrait.publicLeakage (ConstantTimeTrait.leakageOf (T := T) t) :=
  ConstantTimeTrait.ct_sound t h

/-! ## 3. The load-bearing instance: the THIR (`thir`) front CT mechanism

We instantiate `ConstantTimeTrait` on Jasmin `Com`s — the targets of the THIR
front's `lowerThir` — using the genuinely-proven no-memory-op invariant
`jComNoMem` and its soundness `noMem_ctSafeJasmin`. The instance is parametric
in the binding context `Γ` and result type `t` of the `Com`; every `lowerThir`
output is `ctSafe` here via `lowerThir_noMem`. -/

/-- **`thir` constant-time-by-construction instance.**
    * `ctSafe c`        is `jComNoMem c = true` — the THIR-front
      CT-by-construction invariant (no memory op; the only index-bearing ops);
    * `Leakage`         is `LabelCtxt Γ → Bool` — the addressing-leakage trace,
      one bit per label context the program may be linked under;
    * `leakageOf c`     is `fun L => ctSafeJasmin c L` — whether `c`'s addressing
      is public under labelling `L`;
    * `publicLeakage ℓ` is `∀ L, ℓ L = true` — public iff CT-safe under *every*
      labelling (the robust-CT reading);
    * `ct_sound`        is `noMem_ctSafeJasmin`, the proven soundness lemma. -/
instance thirConstantTimeTrait {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ConstantTimeTrait (Com jasminDialect Γ t) where
  ctSafe c := jComNoMem c = true
  Leakage := LabelCtxt Γ → Bool
  leakageOf c := fun L => ctSafeJasmin c L
  publicLeakage ℓ := ∀ L, ℓ L = true
  ct_sound c h := fun L => noMem_ctSafeJasmin c L h

/-! ## 4. The instance applied to the real front output -/

/-- **Every `lowerThir` output is `ctSafe` for the trait** — the THIR front is
    constant-time *by construction*, expressed through the reusable trait. This
    is `lowerThir_noMem` viewed as a `ConstantTimeTrait.ctSafe` fact. -/
theorem lowerThir_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) :
    ConstantTimeTrait.ctSafe (lowerThir c) :=
  lowerThir_noMem c

/-- **Generic CT-by-construction for the THIR front via the trait.** Composing
    the abstract derived lemma `ctSafe_leakage_public` with the construction
    fact `lowerThir_ctSafe` recovers `lowerThir`'s robust constant-time
    guarantee — its addressing leakage is public under every labelling — but now
    routed entirely through the reusable D5 trait rather than the front-specific
    soundness lemma directly. Unfolding `publicLeakage`/`leakageOf` this is
    exactly `lowerThir_ctSafeJasmin`. -/
theorem lowerThir_leakage_public {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) (L : LabelCtxt Γ) :
    ctSafeJasmin (lowerThir c) L = true :=
  ctSafe_leakage_public (lowerThir c) (lowerThir_ctSafe c) L

end CatCrypt.Crypto.SecureCompilation.Dialects
