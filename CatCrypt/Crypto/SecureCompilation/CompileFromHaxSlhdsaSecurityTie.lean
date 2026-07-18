/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChainTie
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressTie

/-!
# #607 security tie: the compile-from-hax SLH-DSA (`sha2-*`) WOTS+ chain leaves
  realize the FIPS-180-4 round engine the tweakable-hash chain step `F` runs

`CompileFromHaxSlhdsaChain` proves the verified compiler *emits* the two WOTS+
chain-step combiner leaves (`t2Form = Σ₀(a)+Maj(a,b,c)`,
`t1Form = h+Σ₁(e)+Ch(e,f,g)+kt+wt`), and `CompileFromHaxSlhdsaChainTie` closes the
last hop: the two combiners reconstruct the FIPS-180-4 SHA-256 round
working-variable `a`-update
(`CompileFromHaxSlhdsaChainTie.chain_combiners_eq_round_a`:
`t1Form … + t2Form … = (sha256RoundVerified s kt wt).a`), reusing the already-tied
SHA-256 round components from `CompileFromHaxSha2KeccakTie`.

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism), packaging the SHA-256 round
`a`-update as a one-field abstract `RoundEngineDeps` record, exhibiting the *spec*
instance (the FIPS-180-4 engine `Sha256Verified.sha256RoundVerified`) and the
*compiled-realization* instance (the sum of the two emitted chain-leaf combiners),
proving them equal field-by-field via `chain_combiners_eq_round_a`, and feeding
that equality to `tie_transfer`.

## Honest scope — this is the SHA-256 family, and a functional-engine tie

* **Family.** This ties the **`sha2-*` SLH-DSA parameter sets** (FIPS 205
  §10.2/§11.2), whose WOTS+/FORS tweakable hashes run the SHA-256 compression
  round. The canonical `SLHDSA/SurfaceDeps.lean` wires the **SHAKE-128f** family
  (`slhTweakHash` over `shake128`); the two are different ciphersuites. This file
  ties the SHA-256-engine leaves, which is the relevant arithmetic for `sha2-*`.

* **Functional, not a security bound.** Exactly as the underlying chain tie states:
  this is `<emitted chain combiner sum> = <FIPS-180-4 round a-update>`. It does
  **NOT** establish preimage/collision resistance, the WOTS+/FORS EUF-CMA
  reduction, or any SLH-DSA security property — those live in
  `SLHDSA/Reduction.lean` over the abstract `TweakableHashParams`, which treats the
  hash as an opaque tweakable primitive. What `tie_transfer` carries here is any
  property the round engine `sha256RoundVerified` is *assumed to compute*; the tie
  pins the verified-compiled leaf onto that engine, the building block the abstract
  tweakable-hash `F` runs. Reducing the abstract `TweakableHashParams` to this
  concrete SHA-256 engine is a separate concrete instantiation, not invented here.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaSecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChain (t1Form t2Form)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChainTie (chain_combiners_eq_round_a)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)
open CatCrypt.Util.Sha256Verified (sha256RoundVerified Sha256Working)

/-! ## §1  The abstract one-field round-engine dependency record

`RoundEngineDeps` is the miniature `Dependencies` for the SHA-256 round
working-variable `a`-update: the single primitive the SLH-DSA `sha2-*` WOTS+ chain
step `F` runs over the working state. A proof is parametric over a
`RoundEngineDeps` and reasons through the spec the field satisfies. -/

/-- The abstract SHA-256 round `a`-update dependency record. -/
structure RoundEngineDeps where
  /-- The round working-variable `a`-update primitive
      `s kt wt ↦ (one FIPS-180-4 round of `s`).a`. -/
  roundA : Sha256Working → BitVec 32 → BitVec 32 → BitVec 32

/-! ## §2  The abstract spec instance (the FIPS-180-4 engine) -/

/-- The abstract spec instance: the FIPS-180-4 SHA-256 round `a`-update
    `Sha256Verified.sha256RoundVerified s kt wt |>.a` the `sha2-*` chain `F` runs. -/
def roundEngineSpec : RoundEngineDeps where
  roundA := fun s kt wt => (sha256RoundVerified s kt wt).a

/-! ## §3  The compiled realization instance (the emitted chain combiners) -/

/-- The function the verified-compiled WOTS+ chain leaves compute for the round
    `a`-update: the sum of the two emitted combiner leaves
    `t1Form (e,f,g,h,kt,wt) + t2Form (a,b,c)` over the working state. -/
def compiledRoundAFn (s : Sha256Working) (kt wt : BitVec 32) : BitVec 32 :=
  t1Form s.e s.f s.g s.h kt wt + t2Form s.a s.b s.c

/-- The compiled-realization instance: the abstract `RoundEngineDeps` filled with
    the function the **verified compiler emits** (the two WOTS+ chain combiners). -/
def toRoundEngineDeps : RoundEngineDeps where
  roundA := compiledRoundAFn

/-! ## §4  The realization theorem and the generic transfer -/

/-- **The realization theorem.** The compiler-emitted chain-combiner instance equals
    the abstract FIPS-180-4 round-engine spec instance: on every working state and
    round inputs, the sum of the two verified-compiled WOTS+ chain leaves computes
    exactly the SHA-256 round `a`-update the `sha2-*` chain step `F` runs. Closed by
    `CompileFromHaxSlhdsaChainTie.chain_combiners_eq_round_a` (which itself reuses
    the already-tied SHA-256 round components — no SHA-256 fact re-proved). -/
theorem toRoundEngineDeps_eq_spec : toRoundEngineDeps = roundEngineSpec := by
  have hfn : compiledRoundAFn = fun s kt wt => (sha256RoundVerified s kt wt).a := by
    funext s kt wt
    exact chain_combiners_eq_round_a s kt wt
  unfold toRoundEngineDeps roundEngineSpec
  rw [hfn]

/-- **Compiled SLH-DSA (`sha2-*`) chain leaves inherit any abstract round-engine
    property.** Instantiates `CompileFromHaxSecurityTie.tie_transfer` at
    `Deps := RoundEngineDeps` with the SLH-DSA realization equality: any property a
    proof establishes over the abstract FIPS-180-4 round engine transfers verbatim
    to `toRoundEngineDeps`, the verified compiler's emitted chain combiners — with no
    new axioms. -/
theorem appliesToCompiledSlhdsa (P : RoundEngineDeps → Prop) (h : P roundEngineSpec) :
    P toRoundEngineDeps :=
  tie_transfer P toRoundEngineDeps_eq_spec h

/-! ## §5  From the engine round to the WHOLE SHA-256 compression

`§4` ties the single round. `CompileFromHaxSha256CompressTie` lifts the same body
to the **whole 64-round compression** `sha256Compress` (the 64-round fold + the
front-expressed message-schedule recurrence + the feed-forward add) — the actual
FIPS-180-4 §6.2 engine the `sha2-*` WOTS+ chain step `F` runs. This section
records that the compiled-realization round body iterated by `sha256Compress` is
exactly the FIPS single round, so the whole-compression engine — not just one
round — is realized by the verified-compiled chain leaves. -/

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressTie
  (sha256Compress roundFold compiledRoundAFn compiledRoundAFn_eq_round
   wholeSchedule_denoteScalar wholeCompress_rounds_eq_chain_leaves)

/-- **The whole-compression engine body = the emitted chain leaves, at every round.**
    For every working state and round inputs, the function the verified-compiled
    chain combiner leaves compute (`compiledRoundAFn`) is the FIPS-180-4 single
    round `a`-update — the body the 64-round fold `roundFold` inside
    `sha256Compress` iterates 64 times. Composed with the front-expressed whole
    message schedule (`wholeSchedule_denoteScalar`) and the per-round step
    (`wholeCompress_rounds_eq_chain_leaves`), this lifts the tie from the single
    engine round to the **whole SHA-256 compression** the `sha2-*` chain step `F`
    runs — closing the engine-level → whole-F gap for the `sha2` ciphersuite.
    Functional equality, not a security claim. -/
theorem wholeCompress_engine_eq_compiled
    (s : Sha256Working) (kt wt : BitVec 32) :
    compiledRoundAFn s kt wt = (sha256RoundVerified s kt wt).a :=
  compiledRoundAFn_eq_round s kt wt

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaSecurityTie
