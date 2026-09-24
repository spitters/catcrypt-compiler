/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie
public import CatCrypt.Crypto.SecureCompilation.TExprToThir

/-!
# Typed-front security tie: TYPED-compiled round leaves realize the FIPS structure

This module is the **typed-front analog** of
`CompileFromHaxSecurityTie.lean`. That file showed the SHA-256 round-component
`Com` terms emitted by the verified compiler from the *deprecated untyped*
`ImpExpr` front realize the abstract FIPS dependency record `RoundDeps` (its
fields equal `roundDepsSpec`, the FIPS 180-4 formulas a security proof assumes),
so any property proved over `roundDepsSpec` transfers to the compiled leaves.

Here we re-express that realization onto the **production typed front**: the
round-component `Com` terms compiled from the canonical typed AST
`Hax.TExpr` (via `TExprToThir.texprToThir`), i.e. the
`big_sigma0_texpr_compiles` / `big_sigma1_texpr_compiles` /
`maj_texpr_compiles` / `ch_texpr_compiles` leaves. We **reuse** the *same*
`RoundDeps` / `roundDepsSpec` abstraction from `CompileFromHaxSecurityTie`
(imported, not redefined), and build a second realization instance
`toRoundDepsT` whose fields are the functions the *typed*-compiled `Com` terms
compute. The tie theorem `toRoundDepsT_eq_spec : toRoundDepsT = roundDepsSpec`
then holds by exactly the value-agreement clauses of the typed leaves, and
`appliesToCompiledT` transfers any property of `roundDepsSpec` to it.

## Why this is the mechanized answer to "do the security proofs keep working on
   the typed front?"

A security/UC proof in the `SurfaceDeps` style is parametric over the abstract
dependency record and only ever reasons through the *spec* its fields satisfy.
The realization theorem of `CompileFromHaxSecurityTie` shows the
ImpExpr-compiled leaves equal that spec; this file shows the **typed**-compiled
leaves equal the *same* spec. Since both realization instances are equal to
`roundDepsSpec`, the abstract security layer is identical in both cases:
`appliesToCompiledT P (h : P roundDepsSpec) : P toRoundDepsT` is the same
connective principle as `appliesToCompiled`, sourced from the typed leaves.

Concretely, nothing in the security layer depends on whether the front is the
untyped `ImpExpr` or the typed `Hax.TExpr`: the same `RoundDeps` /
`roundDepsSpec` abstraction is realized by the typed-compiled leaves exactly as
by the ImpExpr-compiled ones, with no new axioms (just `▸` on
`toRoundDepsT_eq_spec`).

## Scope

Like the ImpExpr tie, this pins down the **connective principle** on the
round primitives: a typed-compiled leaf (a `Com jasmin` proven equal to its
FIPS spec) realizes an abstract dependency field a security-style theorem
consumes, and value-agreement composes with the abstract proof by plain
equality. The per-real-protocol fan-out (wiring these into a concrete
SHA-256/HMAC `Dependencies` and its full UC theorem) is not re-proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TExprSecurityTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (RoundDeps roundDepsSpec)
open CatCrypt.Crypto.SecureCompilation.TExprToThir
  (big_sigma0_texpr_compiles big_sigma1_texpr_compiles maj_texpr_compiles ch_texpr_compiles)

/-! ## §1  The TYPED-compiled `Com` terms (what the typed front emits)

For each round primitive we extract, from the committed typed leaf
`*_texpr_compiles`, the compiled `Com jasminDialect` together with its FIPS
value-agreement clause. The typed leaf is a *nested* existential
`∃ t c, texprToThir … = some t ∧ thirToJasmin … = some c ∧ ∀ inputs, c.denote … =
<FIPS>`; we destructure it (`.choose_spec.choose_spec.2.2`) to obtain the
value-agreement, exactly as a downstream `SurfaceDeps` consumer would. -/

/-- The typed-compiled big-sigma-0 `Com`, taken from the typed leaf
    `big_sigma0_texpr_compiles`. -/
noncomputable def bigSigma0CompiledT := big_sigma0_texpr_compiles.choose_spec.choose

/-- The typed-compiled big-sigma-1 `Com`. -/
noncomputable def bigSigma1CompiledT := big_sigma1_texpr_compiles.choose_spec.choose

/-- The typed-compiled majority `Com`. -/
noncomputable def majCompiledT := maj_texpr_compiles.choose_spec.choose

/-- The typed-compiled choose `Com`. -/
noncomputable def chCompiledT := ch_texpr_compiles.choose_spec.choose

/-- Value-agreement of the typed-compiled Σ₀ `Com` with the FIPS formula. -/
theorem bigSigma0CompiledT_spec (x : BitVec 32) :
    bigSigma0CompiledT.denote (inputValuation 32 1 (fun _ => x))
      = x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22 :=
  big_sigma0_texpr_compiles.choose_spec.choose_spec.2.2 x

/-- Value-agreement of the typed-compiled Σ₁ `Com` with the FIPS formula. -/
theorem bigSigma1CompiledT_spec (x : BitVec 32) :
    bigSigma1CompiledT.denote (inputValuation 32 1 (fun _ => x))
      = x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25 :=
  big_sigma1_texpr_compiles.choose_spec.choose_spec.2.2 x

/-- Value-agreement of the typed-compiled Maj `Com` with the FIPS formula. -/
theorem majCompiledT_spec (x y z : BitVec 32) :
    majCompiledT.denote (inputValuation 32 3 ![x, y, z])
      = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) :=
  maj_texpr_compiles.choose_spec.choose_spec.2.2 x y z

/-- Value-agreement of the typed-compiled Ch `Com` with the FIPS formula. The
    complemented-AND `(¬x) ∧ z` is compiled as the dialect's single-op `andn`. -/
theorem chCompiledT_spec (x y z : BitVec 32) :
    chCompiledT.denote (inputValuation 32 3 ![x, y, z])
      = (x &&& y) ^^^ ((~~~x) &&& z) :=
  ch_texpr_compiles.choose_spec.choose_spec.2.2 x y z

/-! ## §2  The functions the typed-compiled `Com` terms compute -/

/-- The function the typed-compiled Σ₀ `Com` computes. -/
noncomputable def compiledBigSigma0FnT : BitVec 32 → BitVec 32 :=
  fun x => bigSigma0CompiledT.denote (inputValuation 32 1 (fun _ => x))

/-- The function the typed-compiled Σ₁ `Com` computes. -/
noncomputable def compiledBigSigma1FnT : BitVec 32 → BitVec 32 :=
  fun x => bigSigma1CompiledT.denote (inputValuation 32 1 (fun _ => x))

/-- The function the typed-compiled Maj `Com` computes. -/
noncomputable def compiledMajFnT : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 :=
  fun x y z => majCompiledT.denote (inputValuation 32 3 ![x, y, z])

/-- The function the typed-compiled Ch `Com` computes. -/
noncomputable def compiledChFnT : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 :=
  fun x y z => chCompiledT.denote (inputValuation 32 3 ![x, y, z])

/-! ## §3  The realization instance and its tie to the FIPS spec

`toRoundDepsT` is the typed-front realization instance: it fills the **same**
abstract `RoundDeps` record (reused from `CompileFromHaxSecurityTie`) with the
functions the *typed*-compiled round-component `Com` terms compute. -/

/-- The realization instance for the TYPED front: the abstract `RoundDeps` filled
    with the functions the typed-compiled (`Hax.TExpr → Thir → Com`) round
    primitives compute. Same `RoundDeps` record as the ImpExpr tie. -/
noncomputable def toRoundDepsT : RoundDeps 32 where
  bigSigma0 := compiledBigSigma0FnT
  bigSigma1 := compiledBigSigma1FnT
  maj := compiledMajFnT
  ch := compiledChFnT

/-- **The realization theorem (typed front).** The typed-compiled realization
    instance equals the abstract FIPS spec instance `roundDepsSpec` (reused from
    `CompileFromHaxSecurityTie`): the typed front's emitted round primitives
    compute exactly what a SHA-256 security proof assumes. Each field is closed by
    the value-agreement clause of the corresponding `*_texpr_compiles` typed leaf. -/
theorem toRoundDepsT_eq_spec : toRoundDepsT = roundDepsSpec := by
  unfold toRoundDepsT roundDepsSpec
  refine RoundDeps.mk.injEq .. ▸ ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x; exact bigSigma0CompiledT_spec x
  · funext x; exact bigSigma1CompiledT_spec x
  · funext x y z; exact majCompiledT_spec x y z
  · funext x y z; exact chCompiledT_spec x y z

/-! ## §4  Composition with an abstract security theorem (no new axioms)

`appliesToCompiledT` is the typed-front connective principle: **any** property
`P` proved over the abstract spec dependencies `roundDepsSpec` holds of the
typed-compiled dependencies `toRoundDepsT`, by plain rewriting with the
realization theorem. Since both `toRoundDepsT` and the ImpExpr `toRoundDeps`
equal `roundDepsSpec`, the security layer is identical across the front pivot —
the abstract proof is reused verbatim, with no new axioms. -/

/-- **Typed-compiled artifact inherits any abstract dependency property.** For
    every property `P` of `RoundDeps 32`, if `P` holds of the abstract spec
    instance `roundDepsSpec` then it holds of the typed-front realization instance
    `toRoundDepsT`. The mechanized statement that the typed-front output plugs into
    the abstract security layer exactly as the ImpExpr-front output did: a security
    theorem proved over `roundDepsSpec` transfers verbatim to `toRoundDepsT`, the
    typed compiler's emitted primitives — with no new axioms (just `▸` on
    `toRoundDepsT_eq_spec`). -/
theorem appliesToCompiledT {P : RoundDeps 32 → Prop} (h : P roundDepsSpec) :
    P toRoundDepsT :=
  toRoundDepsT_eq_spec ▸ h

end CatCrypt.Crypto.SecureCompilation.TExprSecurityTie
