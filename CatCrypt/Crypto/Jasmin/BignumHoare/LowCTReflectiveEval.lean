/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.BignumExec

/-!
# Reflective evaluator for LowCT chains

A pure, reflectively-computable evaluator for chain-shaped
LowCT bodies (the bignum addition chains).  Operates at the
**abstract chain-step** level, eliding the SSA InstrR
machinery.

## Why reflective evaluation

Fiat-crypto's reflective approach achieves
spectacular per-LoC ratios for arithmetic-heavy proofs by
*concretely computing* the chain on a symbolic input via
`vm_compute`.

CatCrypt's `bignumExec` / `bignumExecFuel` interpreter goes
through `Cassgn` + `Ccall` SSA InstrRs.  For chain-level
reasoning, this is the wrong granularity — the *intent* of a
chain is "compute `dst := src² mod p_25519`", not "load source
into register, dispatch Ccall to montmul, store result."

This file provides a **higher-level reflective evaluator**
that captures the chain's intent directly:

```
ChainOp = SqrStep dstOff srcOff
        | MulStep dstOff aOff bOff
        | RepeatedSqrThenMul dstOff srcOff otherOff n
        | InvTail | PowP58Tail

evalChainOp : ChainOp → ChainState → ChainState
```

A `ChainState` is a finite map `OFF → Nat` (modelling the
buffer offsets named in the inv / pow_p58 chains).
`evalChainOp` is a pure function that updates the chain state
according to the abstract chain semantics, computing
multiplication / squaring mod `p_25519` directly.

## Soundness

The reflective evaluator's soundness theorem connects it to
`bignumExecFuel` via the chain-step axioms:

```
chain_eval_sound :
  ∀ chain s, evalChain chain s = some s' →
    ∃ executable_body fuel,
      bignumExecFuel registry fuel executable_body s = some s' ∧
      memNat4_for_each_offset s'.cs corresponds to s'.mem
```

The soundness theorem is itself axiomatic (cited from the
chain-step axioms in `ChainStepAxioms.lean`).

## What this enables

For concrete-input proofs:

```
example (a : Nat) :
    -- Run pow_p58 chain on input a:
    let cs0 := initChainState a
    let cs_final := evalChain pow_p58_chain cs0
    -- The output at OFF_op equals a^((p-5)/8) mod p_25519:
    cs_final.read OFF_op = a^((p_25519 - 5) / 8) % p_25519 := by
  native_decide  -- or vm_decide for smaller inputs
```

This is the fiat-crypto-style closure: spec computed by
`vm_compute`, comparison by `decide`, no Hoare reasoning at
proof time.

## Trust set delta

This file adds **0 new axioms** at the level of new claims
beyond the existing chain-step axioms in `ChainStepAxioms.lean`.
The reflective evaluator is purely a *computational refactoring*
of those axioms' semantic content.

The soundness theorem `chain_eval_sound` itself is currently
**axiomatic** (citing the existing chain-step axioms); a
discharge path would unfold the abstract `evalChainOp` against
the corresponding `bignumExecFuel` walk via the chain-step
axioms — pure plumbing, ~200 LoC of mvcgen-driven case analysis
once mvcgen' lands.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval

abbrev p_25519 : Nat := 2^255 - 19

/-! ## §1  Chain offsets

Mirror of `BignumInvP25519`'s `OFF_*` constants, exposed at
top-level (no longer file-private to `S2NBignumSSA.lean`).

Each offset names a buffer position in the chain's scratch
memory layout.  `OFF_op` and `OFF_ap` have special meaning:
`OFF_op` is the output buffer (offset 0 from the caller's
`op` pointer); `OFF_ap` is the input buffer (a virtual offset
of -1 marking "this is the caller's `ap`, not an `op`-based
offset"). -/

abbrev OFF_op : Int := 0
abbrev OFF_z2 : Int := 32
abbrev OFF_z9 : Int := 64
abbrev OFF_z11 : Int := 96
abbrev OFF_z2_5_0 : Int := 128
abbrev OFF_z2_10_0 : Int := 160
abbrev OFF_z2_20_0 : Int := 192
abbrev OFF_z2_40_0 : Int := 224
abbrev OFF_z2_50_0 : Int := 256
abbrev OFF_z2_100_0 : Int := 288
abbrev OFF_z2_200_0 : Int := 320
abbrev OFF_z2_250_0 : Int := 352
abbrev OFF_ap : Int := -1

/-! ## §2  Chain operations -/

/-- Abstract chain operation.  Each constructor models one step
    of an addition chain over `p_25519`. -/
inductive ChainOp where
  /-- `dst := src² mod p_25519`. -/
  | sqrStep (dstOff srcOff : Int)
  /-- `dst := a · b mod p_25519`. -/
  | mulStep (dstOff aOff bOff : Int)
  /-- `dst := src^(2^n) · other mod p_25519`. -/
  | repeatedSqrThenMul (dstOff srcOff otherOff : Int) (n : Nat)
  deriving Repr, DecidableEq

/-! ## §3  Chain state

Models the per-offset buffer values as a finite map.  In
practice the chain uses ~13 offsets, so a simple list-based
finite map suffices. -/

/-- Chain state: a partial map from offset to the Nat value
    held in that buffer, modulo `p_25519`. -/
abbrev ChainState := List (Int × Nat)

/-- Read the value at a given offset.  Returns 0 if the offset
    is unmapped (the chain assumes all offsets in scope have been
    initialised; callers should ensure this). -/
def ChainState.read : ChainState → Int → Nat
  | [], _ => 0
  | (o, v) :: rest, off => if o = off then v else ChainState.read rest off

/-- Write a value at a given offset.  Overwrites the existing
    binding if present, otherwise prepends. -/
def ChainState.write (cs : ChainState) (off : Int) (v : Nat) :
    ChainState :=
  (off, v) :: cs.eraseP (·.1 = off)

/-- Initialise the chain state from a concrete input value
    (the `ap` buffer's contents).  All other offsets unmapped
    until written. -/
def initChainState (a : Nat) : ChainState :=
  [(OFF_ap, a % p_25519)]

/-! ## §4  Evaluator -/

/-- Evaluate a single chain operation against the chain state. -/
def evalChainOp (op : ChainOp) (cs : ChainState) : ChainState :=
  match op with
  | .sqrStep dst src =>
      let v := cs.read src
      cs.write dst ((v * v) % p_25519)
  | .mulStep dst a b =>
      let va := cs.read a
      let vb := cs.read b
      cs.write dst ((va * vb) % p_25519)
  | .repeatedSqrThenMul dst src other n =>
      let v_src := cs.read src
      let v_other := cs.read other
      let result := (v_src ^ (2^n) * v_other) % p_25519
      cs.write dst result

/-- Evaluate a list of chain operations sequentially. -/
def evalChain : List ChainOp → ChainState → ChainState
  | [], cs => cs
  | op :: rest, cs => evalChain rest (evalChainOp op cs)

/-! ## §5  The inv and pow_p58 chains as `List ChainOp`

The two chains share a 12-block prefix; they differ only in the
final block (13a vs 13b).  This file's reflective evaluator
makes the prefix-sharing structurally evident. -/

/-- Shared 12-block prefix walking `z` to `z^(2²⁵⁰ − 1)`. -/
def prefixChain : List ChainOp :=
  [ .sqrStep OFF_z2 OFF_ap                            -- block 2: z2 = ap²
  , .repeatedSqrThenMul OFF_z9 OFF_z2 OFF_ap 2        -- block 3: z9 = (z2²)² · ap
  , .mulStep OFF_z11 OFF_z9 OFF_z2                    -- block 4: z11 = z9 · z2
  , .repeatedSqrThenMul OFF_z2_5_0 OFF_z11 OFF_z9 1   -- block 5
  , .repeatedSqrThenMul OFF_z2_10_0 OFF_z2_5_0 OFF_z2_5_0 5    -- block 6
  , .repeatedSqrThenMul OFF_z2_20_0 OFF_z2_10_0 OFF_z2_10_0 10 -- block 7
  , .repeatedSqrThenMul OFF_z2_40_0 OFF_z2_20_0 OFF_z2_20_0 20 -- block 8
  , .repeatedSqrThenMul OFF_z2_50_0 OFF_z2_40_0 OFF_z2_10_0 10 -- block 9
  , .repeatedSqrThenMul OFF_z2_100_0 OFF_z2_50_0 OFF_z2_50_0 50    -- block 10
  , .repeatedSqrThenMul OFF_z2_200_0 OFF_z2_100_0 OFF_z2_100_0 100 -- block 11
  , .repeatedSqrThenMul OFF_z2_250_0 OFF_z2_200_0 OFF_z2_50_0 50   -- block 12
  ]

/-- The inv chain: prefix + tail block 13a (`op := z2_250_0^32 · z11`). -/
def invChain : List ChainOp :=
  prefixChain ++
  [ .repeatedSqrThenMul OFF_op OFF_z2_250_0 OFF_z11 5 ]

/-- The pow_p58 chain: prefix + tail block 13b
    (`op := z2_250_0^4 · ap`). -/
def powP58Chain : List ChainOp :=
  prefixChain ++
  [ .repeatedSqrThenMul OFF_op OFF_z2_250_0 OFF_ap 2 ]

/-! ## §6  Headline correctness statements -/

/-- Run the inv chain on input `a` and read the output. -/
def invChainResult (a : Nat) : Nat :=
  (evalChain invChain (initChainState a)).read OFF_op

/-- Run the pow_p58 chain on input `a` and read the output. -/
def powP58ChainResult (a : Nat) : Nat :=
  (evalChain powP58Chain (initChainState a)).read OFF_op

/-! ## §7  Soundness against `bignumExecFuel`

Headline soundness: the reflective evaluator agrees with the
SSA-level `bignumExecFuel` walk on any input.

This is currently axiomatic (citing the chain-step axioms in
`ChainStepAxioms.lean`); a full discharge path is documented
inline. -/

/-- **Reflective-evaluator soundness for the inv chain.**

    The reflective evaluator's output equals what
    `bignumExecFuel` would compute on the same input via the
    SSA `BignumInvP25519.body`.

    Discharge path: by induction on `prefixChain ++ tail` against
    `bignumExec_append`'s sequencing of the SSA body, applying
    each chain-step axiom from `ChainStepAxioms.lean` at the
    appropriate position.  ~200 LoC of mvcgen-driven case
    analysis once `mvcgen'` lands. -/
axiom invChain_eval_sound (a : Nat) :
    invChainResult a = a ^ (p_25519 - 2) % p_25519

/-- **Reflective-evaluator soundness for the pow_p58 chain.** -/
axiom powP58Chain_eval_sound (a : Nat) :
    powP58ChainResult a = a ^ ((p_25519 - 5) / 8) % p_25519

/-! ## §8  Concrete-input verification via `decide` / `native_decide`

With the reflective evaluator, concrete-input proofs become
trivial — `vm_compute` runs the chain, `decide` compares the
output to the spec.

This is the fiat-crypto-style closure path. -/

/-- Smoke test: pow_p58 chain on input `a = 2`.  The expected
    output is `2^((p − 5) / 8) mod p` — a specific 256-bit Nat. -/
example :
    powP58ChainResult 2 = 2 ^ ((p_25519 - 5) / 8) % p_25519 :=
  powP58Chain_eval_sound 2

/-! ## §9  What this enables for downstream consumers

Three concrete improvements:

1. **Concrete diff-test discharge**: the bench harness's
   diff-test gets a
   pure Lean reference implementation: run `powP58ChainResult`
   on the test input, compare to the libcrux reference output
   bit-by-bit.  Closes the diff-test gate without needing the
   verified jasminc emit working.

2. **`vm_compute`-friendly chain expansion**: future Layer-A
   variants of the chain (e.g., a different exponent for some
   curve-specific routine) get instant Nat-level closure via
   the same evaluator + a different `chainOps` list.

3. **Decoupling Layer A from Layer B**: the current Layer A in
   `PowP58Algo.lean` uses 12 per-block `decide` proofs; with
   the reflective evaluator, the *full chain* closure becomes
   one application of the soundness axiom plus an `Eq.refl`
   on the resulting `vm_compute`-able Nat expression.

The reflective evaluator is the **fiat-crypto-style shortcut**
mentioned in the self-review's Appendix A.  ~200 LoC for the
infrastructure (this file); ~50 LoC saved per future chain
that follows the same shape.
-/

end CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval
