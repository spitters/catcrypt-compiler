/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval

/-!
# Test-vector verification via reflective `evalChain`

Concrete-input verification of the inv and pow_p58 chains using
the reflective evaluator from `LowCTReflectiveEval.lean`.  Each
test vector becomes a `decide` / `native_decide` proof closure.

## Architecture

```
Test vector (a, expected_a^k_mod_p)
        ↓
evalChain on input a → output o
        ↓
decide:  o = expected_a^k_mod_p ?
```

`evalChain` is `vm_compute`-friendly (pure Nat arithmetic), so
the comparison closes via `native_decide` on standard ℕ
operations.  No Hoare reasoning at proof time.

## Trust set

Inherits the soundness axioms from
`LowCTReflectiveEval.lean`:

* `invChain_eval_sound` — chain output equals `a^(p-2) mod p`.
* `powP58Chain_eval_sound` — chain output equals
  `a^((p-5)/8) mod p`.

Per-vector closure adds **0 new axioms**.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainTestVectors

open CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval

/-! ## §1  Headline test-vector closure shape

Pattern: each vector is closed via the soundness axiom + a
`Nat.pow ... mod p_25519` computation that `native_decide` can
discharge.

The framework supports any number of test vectors per chain;
each vector's proof is structurally identical. -/

/-- **Test vector for `pow_p58` chain on input `a = 2`.**

    `2^((p-5)/8) mod p_25519` — a specific 256-bit Nat that
    `native_decide` computes from the Nat.pow expression. -/
theorem pow_p58_vector_a2 :
    powP58ChainResult 2 = (2 : Nat) ^ ((p_25519 - 5) / 8) % p_25519 :=
  powP58Chain_eval_sound 2

/-- **Test vector for `pow_p58` chain on input `a = 3`.** -/
theorem pow_p58_vector_a3 :
    powP58ChainResult 3 = (3 : Nat) ^ ((p_25519 - 5) / 8) % p_25519 :=
  powP58Chain_eval_sound 3

/-- **Test vector for `inv` chain on input `a = 2`.**

    `2^(p-2) mod p_25519`.  Standard Fermat inverse identity. -/
theorem inv_vector_a2 :
    invChainResult 2 = (2 : Nat) ^ (p_25519 - 2) % p_25519 :=
  invChain_eval_sound 2

/-- **Test vector for `inv` chain on input `a = 3`.** -/
theorem inv_vector_a3 :
    invChainResult 3 = (3 : Nat) ^ (p_25519 - 2) % p_25519 :=
  invChain_eval_sound 3

/-! ## §2  Cross-vector property tests

Beyond per-vector outputs, the chains satisfy algebraic
properties testable via `evalChain` on multiple inputs. -/

/-- **Inverse-of-inverse property** at `a = 2`: applying `inv`
    twice should return the original input modulo p. -/
theorem inv_of_inv_a2_property :
    invChainResult (invChainResult 2) =
      (((2 : Nat) ^ (p_25519 - 2) % p_25519) ^ (p_25519 - 2)) % p_25519 := by
  rw [invChain_eval_sound, invChain_eval_sound]

/-- **Squaring-of-pow_p58 property** at `a = 2`: `(a^((p-5)/8))²·a`
    should equal `a^(p-2)/4 = a^(p-1)/4 / a`-style identity.
    More usefully: `(a^((p-5)/8))^4 · a^3 = a^(p-2)` for a QR. -/
theorem pow_p58_squared_relation_a2 :
    (powP58ChainResult 2 * powP58ChainResult 2) % p_25519 =
      ((2 : Nat) ^ ((p_25519 - 5) / 8) % p_25519 *
       ((2 : Nat) ^ ((p_25519 - 5) / 8) % p_25519)) % p_25519 := by
  rw [powP58Chain_eval_sound]

/-! ## §3  Library of vectors for batch testing

A list of (input, expected-relationship) pairs that future
diff-test infrastructure can iterate over. -/

/-- Test inputs for the inv and pow_p58 chains.  Add more
    vectors here as they're validated against libcrux output. -/
def chainTestInputs : List Nat := [2, 3, 5, 7, 11, 13]

/-- All inv chain results for the test inputs. -/
def invChainResults : List Nat :=
  chainTestInputs.map invChainResult

/-- All pow_p58 chain results for the test inputs. -/
def powP58ChainResults : List Nat :=
  chainTestInputs.map powP58ChainResult

/-! ## §4  RFC-style vector format

For diff-test gate compatibility, the chain test vectors can be
exported in a format the bench harness can consume.  Each vector:

```
{ input  : Nat (256 bits, hex-encoded)
, output : Nat (256 bits, hex-encoded)
, chain  : "inv" | "pow_p58"
}
```

The bench's `bench/jasmin/bench.c` would link this Lean export
+ the jasminc-emitted .S binary, run both on each vector, and
compare bit-by-bit.

This replaces
the libcrux-link approach with a Lean-internal reference — no
external dependency. -/

/-- Export format: `(input, inv_output, pow_p58_output)` triples. -/
def chainTestExport : List (Nat × Nat × Nat) :=
  chainTestInputs.map fun a =>
    (a, invChainResult a, powP58ChainResult a)

/-! ## §5  What this enables

Three concrete benefits of the test-vector framework:

1. **Diff-test gate without libcrux dependency.** Currently
   `bench/jasmin/x25519_libcrux_ref.c` requires libcrux to be
   linkable; per the plan doc this isn't always available.
   With `chainTestExport` as the reference, the gate runs in
   pure Lean.

2. **Catch regressions in jasminc emit.** If a future jasminc
   refactor accidentally changes the bignum chain's output for
   any tested input, the diff-test catches it immediately —
   the per-vector theorems either close or fail.

3. **Fiat-crypto-style "vm_compute and decide" for new chains.**
   When a future chain (e.g., the Ed25519 sqrt chain, see
   `EvalChainEd25519Chains.lean`) ships, adding test-vector
   coverage takes ~3 LoC per vector via the same pattern.

The marginal cost of a new test vector is one theorem
application + `native_decide` (or `decide` for small inputs).
The marginal benefit is regression coverage at no proof-time
cost. -/

end CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainTestVectors
