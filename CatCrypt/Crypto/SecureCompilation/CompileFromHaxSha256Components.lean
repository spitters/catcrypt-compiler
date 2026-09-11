/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxVerbatim
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxDesugarNot

/-!
# The SHA-256 round-component set compiles verbatim from hax extraction

This is the **headline compile-from-hax artifact**: every SHA-256 round component
— σ₀, σ₁, Σ₀, Σ₁, Ch, Maj — compiles end to end through the *unchanged*
`compileFromHax` (C2 ∘ C1) pipeline, value-correct against FIPS 180-4, starting
from the **verbatim** `*_impExpr` literals the typed extraction pipeline emits in
`CatCrypt/Crypto/SHA256/Extraction/Sha256_haxpipe.lean` — not hand-written
sources.

`CompileFromHax.sigma0_compiles` runs on a *hand-written, already let-normalized*
σ₀ (`sigma0Src`); it is the simplest illustration, not the load-bearing claim.
The load-bearing claim is this bundle: the components are taken exactly as
extraction emits them (`#<width>`-suffixed heads, nested-app args, and — for Ch —
a bare `Not#32`), normalized only by the **verified, source-semantics-preserving**
pre-passes (`anfLift` head-normalization + arg-flattening; `desugarNotEmit` for the
complement), then compiled and proved correct via the single C3 meta-theorem
`compileFromHax_meets_spec`.

Each conjunct is the per-component verbatim result proved in its own module
(`CompileFromHaxVerbatim` for the five `BitXor`/`BitAnd`-tree components,
`CompileFromHaxDesugarNot` for `Ch` with its `Not`). This file is the single
aggregate entry point that states "the whole round-component set compiles
verbatim" in one theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256Components

open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir (anfLift)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (frontCtxt rW inputValuation)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxDesugarNot (desugarNotEmit)

/-- **The SHA-256 round-component set compiles verbatim from hax extraction.**
    One headline statement bundling the six per-component verbatim results: each
    of σ₀, σ₁, Σ₀, Σ₁, Ch, Maj compiles through `compileFromHax` (after the
    verified `anfLift` / `desugarNotEmit` pre-passes) to a `Com jasminDialect`
    whose denotation is exactly the FIPS 180-4 formula. The genuine "from a
    high-level (hax-extracted) source" claim for the SHA-256 nonlinear core. -/
theorem sha256_round_components_compile_verbatim :
    -- σ₀ : (x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)
    (∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
        (anfLift Sha256.small_sigma0_impExpr) = some c ∧
      ∀ (x : BitVec 32), c.denote (inputValuation 32 1 (fun _ => x))
        = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat)) ∧
    -- σ₁ : (x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x ≫ 10)
    (∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
        (anfLift Sha256.small_sigma1_impExpr) = some c ∧
      ∀ (x : BitVec 32), c.denote (inputValuation 32 1 (fun _ => x))
        = x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> (10 : Nat)) ∧
    -- Σ₀ : (x ⋙ 2) ⊕ (x ⋙ 13) ⊕ (x ⋙ 22)
    (∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
        (anfLift Sha256.big_sigma0_impExpr) = some c ∧
      ∀ (x : BitVec 32), c.denote (inputValuation 32 1 (fun _ => x))
        = x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22) ∧
    -- Σ₁ : (x ⋙ 6) ⊕ (x ⋙ 11) ⊕ (x ⋙ 25)
    (∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
        (anfLift Sha256.big_sigma1_impExpr) = some c ∧
      ∀ (x : BitVec 32), c.denote (inputValuation 32 1 (fun _ => x))
        = x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25) ∧
    -- Ch : (e ∧ f) ⊕ (¬e ∧ g)
    (∃ c, compileFromHax (w := 32) (nIn := 3) ["e", "f", "g"]
        (anfLift (desugarNotEmit 32 Sha256.ch_impExpr)) = some c ∧
      ∀ (x y z : BitVec 32), c.denote (inputValuation 32 3 ![x, y, z])
        = (x &&& y) ^^^ ((~~~x) &&& z)) ∧
    -- Maj : (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)
    (∃ c, compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"]
        (anfLift Sha256.maj_impExpr) = some c ∧
      ∀ (a b c' : BitVec 32), c.denote (inputValuation 32 3 ![a, b, c'])
        = (a &&& b) ^^^ (a &&& c') ^^^ (b &&& c')) :=
  ⟨CompileFromHaxVerbatim.small_sigma0_verbatim_compiles,
   CompileFromHaxVerbatim.small_sigma1_verbatim_compiles,
   CompileFromHaxVerbatim.big_sigma0_verbatim_compiles,
   CompileFromHaxVerbatim.big_sigma1_verbatim_compiles,
   CompileFromHaxDesugarNot.ch_desugar_verbatim_compiles,
   CompileFromHaxVerbatim.maj_verbatim_compiles⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256Components
