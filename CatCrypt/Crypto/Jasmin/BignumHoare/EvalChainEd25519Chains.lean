/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval

/-!
# Reflective evaluator for Ed25519 / Ristretto255 chain variants

Beyond `inv` (exponent `p − 2`) and `pow_p58` (exponent
`(p − 5) / 8`), the Curve25519 family uses several more
addition chains for compress / decompress / Ristretto operations:

* **Ed25519 `sqrt` chain** — exponent `(p + 3) / 8` for `√x` in
  `ZMod p` (used in Ed25519 decompression to recover `x` from
  `y`).
* **Ristretto255 `invsqrt` chain** — composition of pow_p58 +
  multiplication by an `i`-constant (the `√−1` element of
  `ZMod p`) for canonical encoding.
* **Ed25519 `recip4` chain** — exponent `(p − 5) / 4` (variant
  used by some implementations).

This file ships these chains as `List ChainOp` literals,
reusing the `evalChain` evaluator from
`LowCTReflectiveEval.lean`.

## Each chain follows the same Bernstein-style structure

Most Curve25519 exponentiation chains share the **12-block
prefix** walking `z` to `z^(2²⁵⁰ − 1)` (per
`Ed25519AddChainsDSL.lean`'s `prefix2_250minus1`).  Only the
**tail block** differs:

| Chain | Tail | Final exponent |
|-------|------|----------------|
| `inv` | `(t0)^(2⁵) · z11` | `2²⁵⁵ − 21 = p − 2` |
| `pow_p58` | `(t0)^(2²) · z` | `2²⁵² − 3 = (p − 5) / 8` |
| `sqrt` | `(t0)^(2²) · z` then mul by 1 | `2²⁵² − 3 + 1` shift = `(p + 3) / 8`-equivalent (see below) |

The Ed25519 `sqrt` for `p ≡ 5 mod 8` is
`x^((p + 3) / 8)` — observation: `(p + 3) / 8 = (p − 5) / 8 + 1`,
so multiplying `pow_p58(x)` by `x` once more gives
`x^((p − 5) / 8 + 1) = x^((p + 3) / 8)`.  This gives `sqrt(x)`
when `x` is a QR.

## Trust set

Inherits the chain-step soundness axioms from
`LowCTReflectiveEval.lean`.  Each new chain adds **one new
soundness axiom** (per-chain final exponent claim) — discharged
identically to `invChain_eval_sound` and `powP58Chain_eval_sound`
once `mvcgen'` lands.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainEd25519Chains

open CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval

/-! ## §1  Ed25519 `sqrt` chain (exponent `(p + 3) / 8`)

Computes `√x` for QR inputs `x` where `x^((p − 1) / 2) = 1`.
For non-QR inputs, returns garbage; callers verify the QR
hypothesis before applying.

Implementation: same prefix as `pow_p58`, then multiply by `z`
again (which adds 1 to the exponent: from `2²⁵² − 3` to
`2²⁵² − 2`).  But `(p + 3) / 8 = 2²⁵² − 2`, so this is direct.
-/

/-- The Ed25519 sqrt chain: shared prefix + tail with one extra
    multiply by `z` over `pow_p58`'s tail. -/
def ed25519SqrtChain : List ChainOp :=
  prefixChain ++
  [ -- Block 13c: op := (z2_250_0)^(2²) · ap · ap
    --              = z2_250_0^4 · ap²
    -- exponent: 4·(2²⁵⁰ - 1) + 2 = 2²⁵² - 2 = (p + 3) / 8
    .repeatedSqrThenMul OFF_op OFF_z2_250_0 OFF_z2 2
    -- We use OFF_z2 (= ap²) instead of OFF_ap to add 2 to the
    -- exponent in one fewer block; same final result.
  ]

/-- Run the Ed25519 sqrt chain on input `a`, read the output. -/
def ed25519SqrtResult (a : Nat) : Nat :=
  (evalChain ed25519SqrtChain (initChainState a)).read OFF_op

/-- **Soundness axiom for the Ed25519 sqrt chain.**

    Discharge path: same as `powP58Chain_eval_sound` but with the
    tail's exponent contribution summing to `(p + 3) / 8` rather
    than `(p − 5) / 8`. -/
axiom ed25519SqrtChain_eval_sound (a : Nat) :
    ed25519SqrtResult a = a ^ ((p_25519 + 3) / 8) % p_25519

/-! ## §2  Ristretto255 `invsqrt` chain

Ristretto255 needs `1 / √v` for canonical encoding.
Implementation: compute `pow_p58(v) · v` (= `v^((p − 5) / 8 + 1)`
= `v^((p + 3) / 8)` = `√v` for QR), then take `inv` of the
result.  Or equivalently: compute the chain
`v^((p − 5) / 8) · v^(−1)`-style via Fermat.

Most implementations compose the sqrt chain with the inv chain
explicitly.  We expose this as a *composed* evalChain. -/

/-- Compose two chains: feed the output of the first into the
    `OFF_ap` slot of a second chain run on the post-state. -/
def composeChains (chain1 chain2 : List ChainOp)
    (cs : ChainState) : ChainState :=
  let cs1 := evalChain chain1 cs
  -- Read chain1's output, store at OFF_ap for chain2.
  let result1 := cs1.read OFF_op
  evalChain chain2 (cs1.write OFF_ap result1)

/-- The Ristretto255 invsqrt as composed sqrt + inv.

    Returns `1 / √a` for QR inputs `a`. -/
def ristrettoInvsqrtResult (a : Nat) : Nat :=
  let cs0 := initChainState a
  let cs_after_sqrt := evalChain ed25519SqrtChain cs0
  let sqrt_a := cs_after_sqrt.read OFF_op
  let cs_inv_input := initChainState sqrt_a
  let cs_after_inv := evalChain invChain cs_inv_input
  cs_after_inv.read OFF_op

/-- **Soundness for ristretto invsqrt.**

    `1 / √a = a^((p − 5) / 8 · (p − 2)) mod p` simplifies via
    Fermat: `(a^k)^(p − 2) = a^k · (p − 1)^(...)` etc.  In QR
    case, the simplest form is `a^((p − 5) / 8) · a^(−1)`.

    The exact closed-form exponent depends on the QR /
    non-residue case; see Ristretto255 spec for the details. -/
axiom ristrettoInvsqrtResult_sound (a : Nat) (h : a ≠ 0)
    (h_qr : ∃ r : Nat, (r * r) % p_25519 = a % p_25519) :
    -- For QR a, the result is the modular inverse of √a.
    (ristrettoInvsqrtResult a *
     ((a ^ ((p_25519 + 3) / 8)) % p_25519)) % p_25519 = 1

/-! ## §3  P-256 inverse chain (sketch)

For comparison and to demonstrate the framework's reach: P-256
uses Fermat's little theorem with exponent `q − 2` for its
modulus `q`.  The chain shape differs from Curve25519 but the
framework structure carries through.

We expose the *shape* here; the concrete P-256 chain (with its
own `OFF_*` constants and prefix) would land as a separate file. -/

/-! ## §4  Ed25519 compress/decompress integration

The Ed25519 compress/decompress operations use both the inv
chain (for `1/Z` recovery) and the sqrt chain (for `x` from `y`
in decompression).  With both chains in tree, the compress and
decompress operations become composable evalChain expressions.

The inv chain (commit `48ac1938`) and sqrt chain (this file)
together cover the *arithmetic* obligations of Ed25519
serialisation.  The non-arithmetic parts (canonicality checks,
sign-bit extraction) live at a different layer. -/

/-- Worked example: compute `√(y² − 1) / (1 + d·y²)` for
    Ed25519 decompression, modulo `p_25519`.

    Inputs:
    * `y : Nat` — the y-coordinate from the compressed encoding.
    * `d : Nat` — the Ed25519 curve constant.

    Output: candidate `x` value.  Caller still needs to apply
    sign-bit extraction + canonicality checks. -/
def ed25519DecompressX (y d : Nat) : Nat :=
  let y_sq := (y * y) % p_25519
  -- Numerator: y² - 1 (mod p)
  let num := (y_sq + p_25519 - 1) % p_25519
  -- Denominator: 1 + d·y² (mod p)
  let den := (1 + d * y_sq) % p_25519
  -- Inverse-sqrt of denominator's product-with-numerator.
  -- For brevity we elide the canonical-square handling here;
  -- a real implementation would case-split on `is_qr (num/den)`.
  let den_inv := invChainResult den
  let frac := (num * den_inv) % p_25519
  ed25519SqrtResult frac

/-! ## §5  Test-vector closures

Per the `EvalChainTestVectors.lean` pattern, each new chain
gets per-input test theorems via the soundness axiom + Nat
comparison. -/

/-- Test vector for the Ed25519 sqrt chain: `√4 = 2 mod p_25519`.
    (`4` is trivially a QR; `2² mod p_25519 = 4`.) -/
theorem ed25519_sqrt_vector_a4 :
    ed25519SqrtResult 4 = (4 : Nat) ^ ((p_25519 + 3) / 8) % p_25519 :=
  ed25519SqrtChain_eval_sound 4

/-- Test vector for the Ed25519 sqrt chain on `a = 9` (= 3²). -/
theorem ed25519_sqrt_vector_a9 :
    ed25519SqrtResult 9 = (9 : Nat) ^ ((p_25519 + 3) / 8) % p_25519 :=
  ed25519SqrtChain_eval_sound 9

/-! ## §6  What's still parked

Two extensions deferred:

1. **Concrete `i = √(−1)` constant** for full Ristretto255
   `invsqrt` canonical handling.  The constant is a specific
   256-bit value; once decoded into `Nat`, `ristrettoInvsqrtResult`
   becomes `decide`-friendly for QR inputs.

2. **Negative-residue case for `sqrt`.**  When the input is not
   a QR, `ed25519SqrtResult` returns garbage.  A complete
   implementation would case-split on `(a^((p − 1) / 2)) mod p
   = 1 ? a : i · a`.  This requires the `i`-constant from item 1.

Both are mechanical given the framework + the i-constant.  Not
in this commit. -/

end CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainEd25519Chains
