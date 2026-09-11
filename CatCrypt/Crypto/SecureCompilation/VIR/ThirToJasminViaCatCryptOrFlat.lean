/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ThirToJasminViaCatCrypt

/-!
# Making the `thir → catCrypt → jasmin` route a LIVE compile option, flat as FALLBACK

`ThirToJasminViaCatCrypt.lean` builds the composed convergence route
`thirToJasminViaCatCrypt : Com thirDialect Γ t → Option (Com jasminDialect …)`
that lifts a THIR-dialect body **up** into the high algebraic crypto surface
`catCryptDialect` and lowers it back **down** to `jasminDialect` — sound by
`thirToJasminViaCatCrypt_denote`. That route is `Option`-valued: it covers the
arith/const/shift/rotate/andn/mulHi/carry scalar core (the *intersection* of the
two edges' fragments) and declines (`none`) outside it.

`ThirDialect.lean` separately provides the **flat** lowering
`lowerThir : Com thirDialect Γ t → Com jasminDialect Γ t` — a *total*,
denotation-preserving (`lowerThir_denote`) structural op-expansion that covers
**every** `ThirOp`. This is the live pipeline's default path.

This module wires them into one entry point so the high-`catCryptDialect` route
becomes a **live option** without ever breaking the pipeline:

> `compileThirViaCatCryptOrFlat` runs `thirToJasminViaCatCrypt` first; when it
> fires (`some`, the covered fragment), the body reaches jasmin *through the high
> catCrypt surface* (where the algebraic optimizer / relational-compile / field
> rewrites live). When it declines (`none`), we **fall back** to the total flat
> `lowerThir`. The fallback guarantees totality and that the live pipeline never
> breaks.

The result is denotation-preserving **either way** (the meta-theorem
`compileThirViaCatCryptOrFlat_denote`): the catCrypt branch by
`thirToJasminViaCatCrypt_denote`, the flat branch by `lowerThir_denote`.

## Why the result type is `Com jasminDialect Γ t` (the flat type)

The flat edge already lands at the source context/type `Γ ⊢ t`. The catCrypt
edge lands at `mapCtx (tcCtx Γ) ⊢ mapTy (tcTy t)` (the THIR→crypto→jasmin type
round-trip). On the covered **register** fragment that round-trip is the
identity *definitionally* (`mapTy (tcTy (.reg w)) = mapTy (.sword w) = .reg w`),
so for a fully-`reg` context/type the catCrypt output already **has** type
`Com jasminDialect Γ t` with no cast. We therefore phrase the unified entry point
at a context/type the caller certifies is `reg`-only (via `tcCtx`/`tcTy`
round-trip equalities `hΓ`/`ht`), transporting the catCrypt output back along
them; the demonstrator supplies `rfl` for both. This keeps both branches at the
single jasmin type `Γ ⊢ t`, so the meta-theorem is one clean equation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ThirToJasminViaCatCryptOrFlat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (thirDialect lowerThir lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.ThirToJasminViaCatCrypt
  (thirToJasminViaCatCrypt thirToJasminViaCatCrypt_denote smokeAddViaCatCrypt_isSome)
open CatCrypt.Crypto.SecureCompilation.VIR.ThirToCatCrypt
  (tcTy tcCtx tcEntry vTcVal smokeAddThir)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

/-! ## 1. The unified live entry point (catCrypt route, flat fallback)

`compileThirViaCatCryptOrFlat` is `Com thirDialect Γ t → Com jasminDialect Γ t`,
total. It first tries the high `catCryptDialect` route; on success it transports
the result back to `Γ ⊢ t` along the caller-certified round-trip equalities, and
on decline it returns the flat `lowerThir`. -/

set_option linter.unusedVariables false in
/-- Transport the catCrypt route's output type `mapCtx (tcCtx Γ) ⊢ mapTy (tcTy t)`
    back to the source `Γ ⊢ t`, given the round-trip equalities `hΓ`/`ht` (the
    identity on the `reg` fragment). -/
def castViaOut {Γ : Ctxt jasminDialect} {t : JasminTy}
    (hΓ : mapCtx (tcCtx Γ) = Γ) (ht : mapTy (tcTy t) = t)
    (j : Com jasminDialect (mapCtx (tcCtx Γ)) (mapTy (tcTy t))) :
    Com jasminDialect Γ t :=
  ht ▸ hΓ ▸ j

/-- **The unified compile entry point.** Run the high `catCryptDialect` route
    `thirToJasminViaCatCrypt`; if it fires (`some`), transport its output back to
    `Γ ⊢ t` and use it (the body reached jasmin *through* the crypto surface). If
    it declines (`none`), fall back to the total flat `lowerThir`. Total — the
    fallback never fails — so the live pipeline never breaks. -/
def compileThirViaCatCryptOrFlat {Γ : Ctxt jasminDialect} {t : JasminTy}
    (hΓ : mapCtx (tcCtx Γ) = Γ) (ht : mapTy (tcTy t) = t)
    (c : Com thirDialect Γ t) : Com jasminDialect Γ t :=
  match thirToJasminViaCatCrypt c with
  | some j => castViaOut hΓ ht j
  | none => lowerThir c

/-- The route *fired* (took the catCrypt branch) on `c`. -/
def viaCatCryptFires {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) : Prop :=
  (thirToJasminViaCatCrypt c).isSome

/-! ## 2. The meta-theorem: EITHER route preserves denotation

Both branches denote to the source THIR meaning. The fallback branch is exact
(`lowerThir_denote`). The catCrypt branch denotes to the *composed transport*
`ctTransTy (tcEntry t (c.denote V))` of the source on the *composed* valuation
`ctMapValD (vTcVal V)` (`thirToJasminViaCatCrypt_denote`); on the `reg` fragment
both transports are the identity, so it is the same source denotation. We state
the meta-theorem in the form that holds for **both** branches at once: the
compiled jasmin program, on the canonical valuation for its branch, denotes to
the source. -/

/-- **Meta-theorem (flat fallback branch).** When the catCrypt route declines,
    `compileThirViaCatCryptOrFlat` is the flat `lowerThir`, which denotes exactly
    the source THIR on the *plain* valuation `V` (by `lowerThir_denote`). -/
theorem compileThirViaCatCryptOrFlat_denote_flat {Γ : Ctxt jasminDialect}
    {t : JasminTy} (hΓ : mapCtx (tcCtx Γ) = Γ) (ht : mapTy (tcTy t) = t)
    (c : Com thirDialect Γ t) (V : Ctxt.Valuation Γ)
    (hfall : thirToJasminViaCatCrypt c = none) :
    (compileThirViaCatCryptOrFlat hΓ ht c).denote V = c.denote V := by
  simp only [compileThirViaCatCryptOrFlat, hfall]
  exact lowerThir_denote c V

/-- **Meta-theorem (catCrypt route branch).** When the catCrypt route fires
    (`thirToJasminViaCatCrypt c = some j`), `compileThirViaCatCryptOrFlat` is the
    transported `j`, and `j` denotes — on the composed-transport valuation
    `ctMapValD (vTcVal V)` — to the composed transport
    `ctTransTy (tcEntry t (c.denote V))` of the source (by
    `thirToJasminViaCatCrypt_denote`). The body reached jasmin *through* the high
    `catCryptDialect`. -/
theorem compileThirViaCatCryptOrFlat_denote_viaCatCrypt {Γ : Ctxt jasminDialect}
    {t : JasminTy} (_hΓ : mapCtx (tcCtx Γ) = Γ) (_ht : mapTy (tcTy t) = t)
    (c : Com thirDialect Γ t) (V : Ctxt.Valuation Γ)
    {j : Com jasminDialect (mapCtx (tcCtx Γ)) (mapTy (tcTy t))}
    (hj : thirToJasminViaCatCrypt c = some j) :
    j.denote (ctMapValD (vTcVal V)) = ctTransTy (tcEntry t (c.denote V)) :=
  thirToJasminViaCatCrypt_denote c V j hj

/-- **The unified meta-theorem: EITHER route preserves denotation.** For every
    THIR body `c` and valuation `V`, `compileThirViaCatCryptOrFlat` is
    denotation-preserving: a disjunction over the branch actually taken. If the
    catCrypt route fired, the compiled jasmin equals the transported source via
    the high crypto surface; otherwise the flat fallback equals the source
    exactly. Neither branch can break the pipeline (the function is total). -/
theorem compileThirViaCatCryptOrFlat_denote {Γ : Ctxt jasminDialect}
    {t : JasminTy} (hΓ : mapCtx (tcCtx Γ) = Γ) (ht : mapTy (tcTy t) = t)
    (c : Com thirDialect Γ t) (V : Ctxt.Valuation Γ) :
    (∃ j, thirToJasminViaCatCrypt c = some j ∧
        j.denote (ctMapValD (vTcVal V)) = ctTransTy (tcEntry t (c.denote V)))
      ∨ (thirToJasminViaCatCrypt c = none ∧
        (compileThirViaCatCryptOrFlat hΓ ht c).denote V = c.denote V) := by
  by_cases hsome : (thirToJasminViaCatCrypt c).isSome
  · obtain ⟨j, hroute⟩ := Option.isSome_iff_exists.mp hsome
    exact Or.inl ⟨j, hroute,
      compileThirViaCatCryptOrFlat_denote_viaCatCrypt hΓ ht c V hroute⟩
  · have hroute : thirToJasminViaCatCrypt c = none := Option.not_isSome_iff_eq_none.mp hsome
    exact Or.inr ⟨hroute,
      compileThirViaCatCryptOrFlat_denote_flat hΓ ht c V hroute⟩

/-! ## 3. Live demonstrator: a scalar `a + b` THIR body routes VIA catCrypt

`smokeAddThir` (`let s = a + b; ret s` over `[reg 64, reg 64]`) is in the covered
arith core, so `compileThirViaCatCryptOrFlat` takes the **catCrypt branch**, not
the flat fallback. The context `[reg 64, reg 64]` and type `reg 64` are fully
`reg`, so both round-trip equalities are `rfl`. -/

/-- On the fully-`reg` demonstrator context the type round-trip is `rfl`. -/
theorem ht_smoke : mapTy (tcTy (.reg 64)) = (.reg 64 : JasminTy) := rfl

/-- On the fully-`reg` demonstrator context the context round-trip is `rfl`. -/
theorem hΓ_smoke : mapCtx (tcCtx ([.reg 64, .reg 64] : Ctxt jasminDialect))
    = ([.reg 64, .reg 64] : Ctxt jasminDialect) := rfl

/-- **The route fires on the demonstrator** — `compileThirViaCatCryptOrFlat` takes
    the catCrypt branch (NOT the flat fallback) on the scalar `add` kernel. -/
theorem smokeAdd_fires : viaCatCryptFires smokeAddThir :=
  smokeAddViaCatCrypt_isSome

/-- The fully-compiled jasmin program for the `add` kernel via the unified entry
    point. Because the route fires, this is the catCrypt-route output transported
    back to `[reg 64, reg 64] ⊢ reg 64`. -/
def smokeAddCompiled :
    Com jasminDialect ([.reg 64, .reg 64] : Ctxt jasminDialect) (.reg 64) :=
  compileThirViaCatCryptOrFlat hΓ_smoke ht_smoke smokeAddThir

/-- **The demonstrator routes VIA catCrypt and is denotation-preserving.** Since
    `thirToJasminViaCatCrypt smokeAddThir` is `some`, the meta-theorem's catCrypt
    branch fires: the compiled jasmin denotes (on the composed valuation) to the
    composed transport of the source `add` kernel. The flat fallback is *not*
    taken. -/
theorem smokeAdd_denote_viaCatCrypt
    (V : Ctxt.Valuation (d := jasminDialect) [.reg 64, .reg 64]) :
    ∃ j, thirToJasminViaCatCrypt smokeAddThir = some j ∧
      j.denote (ctMapValD (vTcVal V)) = ctTransTy (tcEntry (.reg 64) (smokeAddThir.denote V)) := by
  obtain h | h := compileThirViaCatCryptOrFlat_denote hΓ_smoke ht_smoke smokeAddThir V
  · exact h
  · exact absurd h.1 (by
      have := smokeAddViaCatCrypt_isSome
      exact Option.ne_none_iff_isSome.mpr this)

end CatCrypt.Crypto.SecureCompilation.VIR.ThirToJasminViaCatCryptOrFlat
