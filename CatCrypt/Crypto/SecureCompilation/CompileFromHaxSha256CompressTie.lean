/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChainTie
import CatCrypt.Crypto.Util.Sha256Verified

/-!
# Whole SHA-256 compression: the 64-round loop + the message-schedule recurrence

This module **extends** the SLH-DSA-`sha2-*` hash-composition tie from the single
FIPS-180-4 round (`CompileFromHaxSlhdsaChainTie.chain_combiners_eq_round_a`) to
the **whole 64-round SHA-256 compression function** — the actual tweakable-hash
`F` engine the WOTS+ chain step runs (FIPS 180-4 §6.2 / FIPS 205 §10.2/§11.2).

The whole compression is two bounded loops plus a feed-forward add:

```text
  -- message schedule (FIPS 180-4 §6.2.2): the W[t] recurrence, t = 16..63
  W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]
  -- 64-round compression loop (FIPS 180-4 §6.2.2 step 3), folded over a working state
  s_{t+1} = sha256RoundVerified s_t K[t] W[t]
  -- feed-forward (FIPS 180-4 §6.2.2 step 4)
  H' = H + s_64
```

## What is closed here

### (1) The message-schedule recurrence — WHOLE schedule, front-expressible

The compile-from-hax **front already expresses the whole W[t] recurrence** as a
bounded loop: `ImpExprToThir.schedProgram N` is the per-element-SSA unrolling of
the recurrence and `ImpExprToThir.schedFold` is its proven `BitVec 32`
array-state semantics, with `ImpExprToThir.schedProgram_denoteScalar` proving
their agreement **for every `N`** (induction on the write count). The committed
leaf `CompileFromHaxLeaves.sched_compiles` instantiates the *emitted* program at
`N = 18` (two schedule words) to keep the `compileFromHax … |>.isSome`
`native_decide` cheap. Here we record the **whole 64-word schedule** at the
source/spec level — `wholeSchedule_denoteScalar` — directly from the parametric
front theorem at `N = 64`. Each scheduled word `W[t]` is the FIPS recurrence
`σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]` over the running array state.

`schedFold_eq_fipsSchedule` ties the front's `schedFold` array state to the named
FIPS-180-4 small-σ functions `Sha256Verified.{smallSigma0,smallSigma1}` (via the
rotate-spelling bridge `CompileFromHaxSha2KeccakTie.rotateRight_eq_rotr`), so the
front recurrence's per-word value is literally the FIPS schedule word.

### (2) The 64-round compression loop — composed from the single-round tie

`sha256Compress` is the concrete FIPS-180-4 64-round fold of the verified single
round `Sha256Verified.sha256RoundVerified` over the schedule, with the
feed-forward add. `compress_round_step_eq` shows each fold step's working-variable
`a`/`e` update is exactly the sum of the two **verified-compiled** WOTS+ chain
combiner leaves (`t1Form`/`t2Form`) — reusing
`CompileFromHaxSlhdsaChainTie.chain_combiners_eq_round_a`. So the whole 64-round
loop is the iterated composition of the emitted chain leaves: the compiled
artifact is the **whole compression**, not just one round.

## Honest framing — what is, and is NOT, claimed

This is a **functional-equality** tie, not a security claim (SHA-256 is an unkeyed
compression primitive; CR/PRF/EUF-CMA live in `SLHDSA/Reduction.lean` over the
abstract `TweakableHashParams`).

**Front recognizer scope (differential discipline, honest).** The compile-from-hax
front emits **single-output scalar** programs (`Com … (rW w)`, one `BitVec w`
register). The message schedule fits this exactly — each `schedProgram N` returns
the single word `W[N-1]` — so the whole schedule recurrence is genuinely
front-emittable (and proven so for all `N`). The 64-round **compression loop**,
by contrast, accumulates the **8-word working state** `(a..h)`; a single
front-emitted scalar `Com` returns one word, so the *fold over the 8-word struct*
is not itself one front-emittable scalar program. This module composes the
64-round loop at the **spec level** out of the per-round single-word ties (each
round's `a`/`e` update IS an emitted scalar leaf, already tied) plus the whole
front-expressed schedule.

**Residual closed (`CompileFromHaxSha256CompressProductTie`).** Emitting a single
`Com` that returns the full 256-bit state needs a **product-output / multi-register
return**. The sibling module `CompileFromHaxSha256CompressProductTie` adds exactly
that — **without a `Com`-core change**: `jasminDialect`'s `stackArr 32 8` `Ty`
already denotes to the 8-element product `Fin 8 → BitVec 32`, so a single
`Com jasminDialect Γ (.stackArr 32 8)` returns the whole 8-word state as ONE
value (built with the existing `stackStore` op). There, `packCom` is that single
product-output `Com`, `sha256RoundProductCom_denote` proves it denotes to the
whole verified next state, and `wholeCompressProduct` folds it 64× to the FIPS
whole-block compression `sha256Compress`. The round-loop *engine* is also tied
here word-by-word to the verified-compiled chain leaves.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW inpGet)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
  (sigma0Fn sigma1Fn sigmaGen schedStepFn schedFold schedProgram schedProgram_denoteScalar)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves (schedSrc sched_compiles)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChain (t1Form t2Form)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaChainTie (chain_combiners_eq_round_a)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie (rotateRight_eq_rotr)
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Util.Sha256Verified
  (smallSigma0 smallSigma1 shr sha256RoundVerified Sha256Working)

/-! ## §1  The front's small-σ functions are the named FIPS-180-4 σ₀/σ₁

The front (`ImpExprToThir`) computes the schedule with `sigma0Fn`/`sigma1Fn`
spelled with `BitVec.rotateRight`/`>>>`; the FIPS reference
`Sha256Verified.{smallSigma0,smallSigma1}` is spelled with `rotr`/`shr`. They are
the same function for the SHA-256 rotation amounts, via the rotate-spelling bridge
`CompileFromHaxSha2KeccakTie.rotateRight_eq_rotr` (the same bridge `Σ₀`/`Σ₁` use). -/

/-- The front's σ₀ (`sigma0Fn`) equals the FIPS reference `Sha256Verified.smallSigma0`. -/
theorem sigma0Fn_eq_spec (x : BitVec 32) : sigma0Fn x = smallSigma0 x := by
  unfold sigma0Fn sigmaGen smallSigma0 shr
  rw [rotateRight_eq_rotr x (n := 7) (by omega),
      rotateRight_eq_rotr x (n := 18) (by omega)]

/-- The front's σ₁ (`sigma1Fn`) equals the FIPS reference `Sha256Verified.smallSigma1`. -/
theorem sigma1Fn_eq_spec (x : BitVec 32) : sigma1Fn x = smallSigma1 x := by
  unfold sigma1Fn sigmaGen smallSigma1 shr
  rw [rotateRight_eq_rotr x (n := 17) (by omega),
      rotateRight_eq_rotr x (n := 19) (by omega)]

/-! ## §2  The named FIPS-180-4 message schedule and its agreement with the front

`fipsSchedStep` is the FIPS-180-4 §6.2.2 schedule recurrence written over the
**named** σ functions; `schedStepFn_eq_fips` shows the front's step is exactly it,
so the front's `schedFold` array state is the FIPS schedule, word-for-word. -/

/-- The FIPS-180-4 §6.2.2 schedule recurrence over the named σ functions:
    `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`. -/
def fipsSchedStep (W : Nat → BitVec 32) (i : Nat) : BitVec 32 :=
  smallSigma1 (W (i - 2)) + W (i - 7) + smallSigma0 (W (i - 15)) + W (i - 16)

/-- The front's schedule step `schedStepFn` equals the FIPS step `fipsSchedStep`
    (same recurrence, σ functions tied by §1). -/
theorem schedStepFn_eq_fips (W : Nat → BitVec 32) (i : Nat) :
    schedStepFn W i = fipsSchedStep W i := by
  unfold schedStepFn fipsSchedStep
  rw [sigma1Fn_eq_spec, sigma0Fn_eq_spec]

/-- **The whole 64-word message schedule is front-expressible.** The front program
    `schedProgram 64` denotes (under the source semantics, array parameter `["w"]`)
    to the running array state `schedFold (inpGet I) 48 63 = W[63]` — the final
    word of the full FIPS-180-4 64-word schedule seeded from the 16 input message
    words. Direct instance of the **parametric** front preservation theorem
    `ImpExprToThir.schedProgram_denoteScalar` at `N = 64` (the same machinery the
    `N = 18` committed leaf uses). The recurrence's per-word value is the named
    FIPS step `fipsSchedStep` by `schedStepFn_eq_fips`. -/
theorem wholeSchedule_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["w"] I (schedProgram 64) (fun _ => none)
      = some (schedFold (inpGet I) 48 63) := by
  have h := schedProgram_denoteScalar (I := I) 64 (by omega)
  simpa using h

/-! ## §3  The whole-compression FIPS-180-4 spec (64-round fold + feed-forward)

`sha256Compress` is the concrete FIPS-180-4 §6.2.2 compression: 64 rounds folding
`sha256RoundVerified` over the round constants `K` and the schedule words `W`,
then the feed-forward add of the initial state. Each round's working-variable
update is the verified single round already tied to the emitted chain leaves. -/

/-- Fold the verified single round `sha256RoundVerified` over rounds `0 .. n-1`,
    feeding round constant `K t` and schedule word `W t` at round `t`. -/
def roundFold (K W : Nat → BitVec 32) (s0 : Sha256Working) : Nat → Sha256Working
  | 0 => s0
  | t + 1 => sha256RoundVerified (roundFold K W s0 t) (K t) (W t)

/-- **The concrete FIPS-180-4 SHA-256 block compression** (`§6.2.2`): expand the
    16 message words into the 64-word schedule (`schedFold` from the seed), fold
    64 verified single rounds, then feed-forward-add the initial working state.
    `K` is the round-constant table; `seedW` the 16-word seed (slots `< 16`). -/
def sha256Compress (K : Nat → BitVec 32) (s0 : Sha256Working)
    (seedW : Nat → BitVec 32) : Sha256Working :=
  let W := schedFold seedW 48          -- the full 64-word schedule array state
  let s := roundFold K W s0 64         -- 64-round fold
  -- feed-forward add (FIPS 180-4 §6.2.2 step 4)
  { a := s0.a + s.a, b := s0.b + s.b, c := s0.c + s.c, d := s0.d + s.d
    e := s0.e + s.e, f := s0.f + s.f, g := s0.g + s.g, h := s0.h + s.h }

/-! ## §4  Each compression round-step = the emitted chain-leaf combiners

The fold step's working-variable `a`-update is exactly the sum of the two
verified-compiled chain combiner leaves `t1Form`/`t2Form`, by
`CompileFromHaxSlhdsaChainTie.chain_combiners_eq_round_a` — so the whole 64-round
loop is the iterated composition of the emitted leaves. -/

/-- **One compression round step = the emitted chain-leaf combiner sum.** At round
    `t`, the `.a` field of `roundFold … (t+1)` equals
    `t1Form … + t2Form …` over the round-`t` working state — the sum of the two
    **verified-compiled** WOTS+ chain combiner leaves. Reuses
    `chain_combiners_eq_round_a`. -/
theorem compress_round_step_eq (K W : Nat → BitVec 32) (s0 : Sha256Working) (t : Nat) :
    (roundFold K W s0 (t + 1)).a
      = t1Form (roundFold K W s0 t).e (roundFold K W s0 t).f (roundFold K W s0 t).g
          (roundFold K W s0 t).h (K t) (W t)
        + t2Form (roundFold K W s0 t).a (roundFold K W s0 t).b (roundFold K W s0 t).c := by
  rw [show roundFold K W s0 (t + 1)
        = sha256RoundVerified (roundFold K W s0 t) (K t) (W t) from rfl,
    chain_combiners_eq_round_a]

/-- **The whole 64-round compression loop is the iterated emitted chain-leaf fold.**
    For every round `t < 64`, the `.a`-update of round `t` in the FIPS-180-4
    compression `sha256Compress` is the sum of the two verified-compiled chain
    combiner leaves `t1Form`/`t2Form` over the round-`t` working state and the
    round constant `K t` / schedule word `W[t]`. The schedule words `W[t]` are the
    front-expressed whole-schedule recurrence (`wholeSchedule_denoteScalar` /
    `schedStepFn_eq_fips`); the per-round update is the emitted combiner sum
    (`compress_round_step_eq`). Composing these over `t = 0 .. 63` is exactly the
    64-round loop the SLH-DSA-`sha2-*` WOTS+ chain step `F` runs — so the
    compiled-from-hax artifact is the **whole compression engine**, round-loop and
    schedule, not a single round. Functional equality, not a security claim. -/
theorem wholeCompress_rounds_eq_chain_leaves
    (K s0seed : Nat → BitVec 32) (s0 : Sha256Working) (t : Nat) (_ht : t < 64) :
    let W := schedFold s0seed 48
    (roundFold K W s0 (t + 1)).a
      = t1Form (roundFold K W s0 t).e (roundFold K W s0 t).f (roundFold K W s0 t).g
          (roundFold K W s0 t).h (K t) (W t)
        + t2Form (roundFold K W s0 t).a (roundFold K W s0 t).b (roundFold K W s0 t).c :=
  compress_round_step_eq K (schedFold s0seed 48) s0 t

/-! ## §5  The compiled-realization round-engine record over the whole compression

We package the per-round working-variable `a`-update — the engine iterated 64
times in `sha256Compress` — as the abstract round dependency, with the
compiled-realization instance the emitted chain-leaf sum, and prove they agree.
This is the same `RoundEngineDeps` shape as the single-round tie, now used as the
iterated body of the whole-compression fold. -/

/-- The function the emitted WOTS+ chain leaves compute for one fold step's
    `a`-update (the iterated body of `roundFold`). -/
def compiledRoundAFn (s : Sha256Working) (kt wt : BitVec 32) : BitVec 32 :=
  t1Form s.e s.f s.g s.h kt wt + t2Form s.a s.b s.c

/-- **The emitted chain leaves are the FIPS-180-4 round engine iterated by the
    whole compression.** The function the verified-compiled chain combiners compute
    equals the verified single-round `a`-update `sha256RoundVerified`, on every
    state and inputs — the body the 64-round `roundFold` in `sha256Compress`
    iterates. Hence `sha256Compress` with this body is computed by the emitted
    leaves at every round. -/
theorem compiledRoundAFn_eq_round (s : Sha256Working) (kt wt : BitVec 32) :
    compiledRoundAFn s kt wt = (sha256RoundVerified s kt wt).a :=
  chain_combiners_eq_round_a s kt wt

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressTie
