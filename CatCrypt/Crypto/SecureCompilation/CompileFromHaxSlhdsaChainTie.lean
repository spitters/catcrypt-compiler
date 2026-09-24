/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChain
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie
public import CatCrypt.Crypto.Util.Sha256Verified

/-!
# Hash-composition tie: the SLH-DSA WOTS+ chain-step combiners = the FIPS-180-4 round engine

This module is the **hash-composition** companion tie to `CompileFromHaxSlhdsaChain`
— the Category-C shape that **composes** the already-tied SHA-256
round-component leaves (rather than tying a single arithmetic reduce, as the
Frodo/NTRU/sntrup MAC ties do).

`CompileFromHaxSlhdsaChain` proves the verified compiler *emits* two jasmin `Com`
leaves whose `BitVec 32` denotations are the SHA-256 round combiners

* `t2Form a b c   = Σ₀(a) + Maj(a,b,c)`                       (the state-driven half)
* `t1Form e f g h kt wt = h + Σ₁(e) + Ch(e,f,g) + kt + wt`    (the schedule/const half)

This file closes the **last hop**: from those emit forms to the **named FIPS
180-4 round engine** `Sha256Verified.sha256RoundVerified` that the SLH-DSA WOTS+
chain step `F` (the `sha2-*` parameter sets, FIPS 205 §10.2 / §11.2) runs. The
`Σ₀`/`Σ₁`/`Maj`/`Ch` sub-expressions are exactly the leaves
`CompileFromHaxSha2KeccakTie` already transported onto
`Sha256Verified.{bigSigma0,bigSigma1,maj,ch}` — so this tie **reuses** them
(`bigSigma0_form_eq_spec`, `bigSigma1_form_eq_spec`, `maj_form_eq_spec`,
`ch_form_eq_spec`) and does NOT re-prove SHA-256.

## What this is — and what it is NOT (honest framing)

This is a **functional-equality** tie, not a security claim.

- Each chain-step leaf computes a closed `BitVec 32` combiner; this file shows
  those combiners are *literally* the `T1`/`T2` quantities the FIPS 180-4 round
  body (`sha256RoundVerified`) binds, and that adding them reconstructs the
  round's working-variable `a`-update — the engine the WOTS+ chain hash runs.
- It does **NOT** establish preimage/collision resistance of the chain, the
  WOTS+/FORS EUF-CMA reduction, or any SLH-DSA security property. Those live in
  `SLHDSA/Reduction.lean` over the abstract `TweakableHashParams`. The
  hash-chain's underlying SHA-256 is an unkeyed compression primitive; the claim
  here is only `<emit-form> = <FIPS-180-4 round quantity>`.

## How the SHA-256 sub-tie composes in

`Sha256Verified.sha256RoundVerified` is defined with the two locals
`t1 = h + Σ₁(e) + Ch(e,f,g) + kt + wt` and `t2 = Σ₀(a) + Maj(a,b,c)`, using the
*named* FIPS functions `bigSigma0`/`bigSigma1`/`maj`/`ch`. The chain leaves'
emit forms `t2Form`/`t1Form` spell those same functions inline (rotate/xor/and).
`CompileFromHaxSha2KeccakTie` already proved the inline spellings equal the named
functions; we rewrite by those four theorems to land the emit forms exactly on
the round engine's locals. The two single-component ties compose into the
combiner tie, which composes into the full round-`a` tie — the hash-composition
arc the WOTS+ chain step is built from.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChainTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChain
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Util.Sha256Verified (bigSigma0 bigSigma1 maj ch sha256RoundVerified Sha256Working)

/-! ## §1  The combiner emit-forms equal the FIPS-180-4 round locals

`t2Form`/`t1Form` are the inline rotate/xor/and/add spellings; the named FIPS
functions `Sha256Verified.{bigSigma0,bigSigma1,maj,ch}` are what the round engine
`sha256RoundVerified` uses. We bridge the inline spellings to the named functions
by **reusing** the already-proved SHA-256 round-component ties from
`CompileFromHaxSha2KeccakTie`. -/

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie
  (bigSigma0_form_eq_spec bigSigma1_form_eq_spec maj_form_eq_spec ch_form_eq_spec)

/-- **`t2Form` = `Σ₀(a) + Maj(a,b,c)` over the FIPS-180-4 named functions.** The
    `T2` chain-step combiner's emit form equals the named-function sum
    `Sha256Verified.bigSigma0 a + Sha256Verified.maj a b c` — exactly the `t2`
    local of the FIPS-180-4 round body. Reuses the SHA-256 round-component ties
    `bigSigma0_form_eq_spec` / `maj_form_eq_spec`; no SHA-256 fact is re-proved. -/
theorem t2Form_eq_named (a b c : BitVec 32) :
    t2Form a b c = bigSigma0 a + maj a b c := by
  unfold t2Form
  rw [bigSigma0_form_eq_spec a, maj_form_eq_spec a b c]

/-- **`t1Form` = `h + Σ₁(e) + Ch(e,f,g) + kt + wt` over the FIPS-180-4 named
    functions** — exactly the `t1` local of the FIPS-180-4 round body. Reuses the
    SHA-256 round-component ties `bigSigma1_form_eq_spec` / `ch_form_eq_spec`. -/
theorem t1Form_eq_named (e f g h kt wt : BitVec 32) :
    t1Form e f g h kt wt
      = h + bigSigma1 e + ch e f g + kt + wt := by
  unfold t1Form
  rw [bigSigma1_form_eq_spec e, ch_form_eq_spec e f g]

/-! ## §2  The combiners reconstruct the FIPS-180-4 round `a`-update

`sha256RoundVerified` binds `a' = T1 + T2`. The two chain leaves compute exactly
those locals (`§1`), so adding their emit forms reconstructs the round's `a`
output — the engine the WOTS+ chain step `F` runs over the working state. -/

/-- **The two chain-step combiners reconstruct the round `a`-update.** For working
    state `s` and round inputs `kt`/`wt`, `t1Form` (over `e,f,g,h = s.e,s.f,s.g,s.h`)
    plus `t2Form` (over `a,b,c = s.a,s.b,s.c`) equals the `.a` field of one FIPS
    180-4 round `Sha256Verified.sha256RoundVerified s kt wt`. This is the
    hash-composition tie: two emitted leaves, each composing two SHA-256 round
    components, sum to the round's working-variable update — the SHA-256 round
    engine at the heart of the SLH-DSA `sha2-*` WOTS+ chain step. -/
theorem chain_combiners_eq_round_a
    (s : Sha256Working) (kt wt : BitVec 32) :
    t1Form s.e s.f s.g s.h kt wt + t2Form s.a s.b s.c
      = (sha256RoundVerified s kt wt).a := by
  rw [t1Form_eq_named, t2Form_eq_named]
  unfold sha256RoundVerified
  rfl

/-! ## §3  Transport the emitted leaf denotations onto the round engine

Each theorem states: the verified compiler emits a program whose `BitVec 32`
denotation is the named FIPS-180-4 round local — composed from the tied SHA-256
round components. Functional-equality tie, NOT a security statement. -/

/-- **The emitted `T2` chain-step leaf computes the FIPS-180-4 round `t2` local.**
    The verified compiler emits a `Com` whose denotation is
    `Sha256Verified.bigSigma0 a + Sha256Verified.maj a b c` — the state-driven half
    of the SHA-256 round the SLH-DSA WOTS+ chain step `F` runs. Composes the tied
    `Σ₀` and `Maj` round components. -/
theorem t2_emitted_eq_round_t2 :
    ∃ (prog : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["a", "b", "c"] t2Src = some prog ∧
      ∀ (a b c : BitVec 32),
        prog.denote (inputValuation 32 3 ![a, b, c])
          = bigSigma0 a + maj a b c := by
  obtain ⟨prog, hc, hden⟩ := t2_compiles
  exact ⟨prog, hc, fun a b c => (hden a b c).trans (t2Form_eq_named a b c)⟩

/-- **The emitted `T1` chain-step leaf computes the FIPS-180-4 round `t1` local.**
    The verified compiler emits a `Com` whose denotation is
    `h + Σ₁(e) + Ch(e,f,g) + kt + wt`. Composes the tied `Σ₁` and `Ch` round
    components plus the round constant / schedule-word folds. -/
theorem t1_emitted_eq_round_t1 :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["e", "f", "g", "h", "kt", "wt"] t1Src = some prog ∧
      ∀ (e f g h kt wt : BitVec 32),
        prog.denote (inputValuation 32 6 ![e, f, g, h, kt, wt])
          = h + bigSigma1 e + ch e f g + kt + wt := by
  obtain ⟨prog, hc, hden⟩ := t1_compiles
  exact ⟨prog, hc, fun e f g h kt wt => (hden e f g h kt wt).trans (t1Form_eq_named e f g h kt wt)⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChainTie
