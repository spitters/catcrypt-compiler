/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.X25519Program

/-!
# Addition-chain field exponentiation

Compile-time addition-chain table for `x^(p-2) mod (2^255 - 19)`.

Target: **Curve25519 / Ed25519 field inversion** via Fermat's little
theorem (`x^(p-1) = 1 ⇒ x⁻¹ = x^(p-2)`). The canonical Bernstein
chain (Curve25519 paper, §6) costs **254 squarings + 11 multiplications
= 265 field operations**, vs. ~507 ops for naive square-and-multiply.
≈ 48% reduction in the field-op count of the inverse.

## Chain encoding

We use a structured form: `Block.run` (n squarings on the accumulator)
or `Block.mulStash i` (multiply the accumulator by the `i`-th stashed
intermediate). Stashes are produced explicitly via `Block.stash`.

This shape matches how Bernstein's chain is written in
`curve25519-dalek`, `fiat-crypto`, and `libsodium`: a sequence of
"square `n` times, then multiply by some earlier intermediate".

The algebraic semantics (`applyChain`) and its `x^(p-2)` correctness
live in `FieldExpChainSemantics.lean`.

Reference: D. J. Bernstein, "Curve25519: new Diffie-Hellman speed
records" (2006), §6 (table 1). The same chain is in
`curve25519-dalek::field::FieldElement::invert`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldExpChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## 1. Chain block encoding -/

/-- One block of the addition chain: either a run of n squarings, a
    multiply by a stashed intermediate, or a stash-the-accumulator op. -/
inductive Block where
  /-- Square the accumulator `n` times in succession. -/
  | run (n : Nat) : Block
  /-- Multiply the accumulator by stash index `i`. The stash list is
      indexed in chronological order: stash 0 is the input base. -/
  | mulStash (i : Nat) : Block
  /-- Save the current accumulator into the stash list. Subsequent
      `mulStash i` refers back by index. -/
  | stash : Block
deriving Repr, DecidableEq

/-- Count squarings in a block list. -/
def Block.sqrCount : List Block → Nat
  | [] => 0
  | .run n :: rest => n + sqrCount rest
  | _ :: rest => sqrCount rest

/-- Count multiplications in a block list. -/
def Block.mulCount : List Block → Nat
  | [] => 0
  | .mulStash _ :: rest => 1 + mulCount rest
  | _ :: rest => mulCount rest

/-! ## 2. Bernstein's chain for `x^(p-2) mod (2^255 - 19)`

The chain computes successive intermediates and stashes them by index:

| Stash idx | Power computed                | How                            |
|-----------|-------------------------------|--------------------------------|
| 0         | x                             | input                          |
| 1         | x²                            | sqr                            |
| 2         | x⁹                            | (x²)²² · x ↦ pattern below     |
| 3         | x¹¹                           | x⁹ · x²                        |
| 4         | x^(2⁵ − 1)                    | x¹¹² · x⁹                      |
| 5         | x^(2¹⁰ − 1)                   | (x^(2⁵−1))^(2⁵) · x^(2⁵−1)    |
| 6         | x^(2²⁰ − 1)                   | similar                        |
| 7         | x^(2⁴⁰ − 1)                   |                                |
| 8         | x^(2⁵⁰ − 1)                   |                                |
| 9         | x^(2¹⁰⁰ − 1)                  |                                |
| 10        | x^(2²⁰⁰ − 1)                  |                                |
| 11        | x^(2²⁵⁰ − 1)                  |                                |
| out       | x^(2²⁵⁵ − 21) = x^(p−2) = x⁻¹ | (x^(2²⁵⁰−1))^5 · x¹¹            |

Total: 254 squarings + 11 multiplications = 265 field operations. -/

/-- Bernstein's chain. Reading the list: start with accumulator = x¹
    (stashed at index 0 implicitly by the builder). Each `Block`
    advances the accumulator. -/
def bernsteinInvChain : List Block :=
  -- Step 1: x² = sqr x; stash x²
  [ .run 1                -- acc = x²
  , .stash                -- stash[1] = x²
  -- Step 2: x⁹ = (((x²)²)² · x = ((x²)²)² · x = x⁸ · x; via run 2 + mul
  -- Actually: x⁹ = x⁸ · x. So: run 2 (x⁸) then mulStash 0 (· x).
  --   acc = x² →(run 2)→ x⁸ →(mul 0)→ x⁹
  , .run 2
  , .mulStash 0
  , .stash                -- stash[2] = x⁹
  -- Step 3: x¹¹ = x⁹ · x². acc = x⁹ →(mul 1)→ x¹¹.
  , .mulStash 1
  , .stash                -- stash[3] = x¹¹
  -- Step 4: x^(2⁵-1) = x³¹ = (x¹¹)² · x⁹.
  --   acc = x¹¹ →(run 1)→ x²² →(mul 2)→ x³¹.
  , .run 1
  , .mulStash 2
  , .stash                -- stash[4] = x^(2⁵-1)
  -- Step 5: x^(2¹⁰-1) = (x^(2⁵-1))^(2⁵) · x^(2⁵-1).
  , .run 5
  , .mulStash 4
  , .stash                -- stash[5] = x^(2¹⁰-1)
  -- Step 6: x^(2²⁰-1) = (x^(2¹⁰-1))^(2¹⁰) · x^(2¹⁰-1).
  , .run 10
  , .mulStash 5
  , .stash                -- stash[6] = x^(2²⁰-1)
  -- Step 7: x^(2⁴⁰-1) = (x^(2²⁰-1))^(2²⁰) · x^(2²⁰-1).
  , .run 20
  , .mulStash 6
  , .stash                -- stash[7] = x^(2⁴⁰-1)
  -- Step 8: x^(2⁵⁰-1) = (x^(2⁴⁰-1))^(2¹⁰) · x^(2¹⁰-1).
  , .run 10
  , .mulStash 5
  , .stash                -- stash[8] = x^(2⁵⁰-1)
  -- Step 9: x^(2¹⁰⁰-1) = (x^(2⁵⁰-1))^(2⁵⁰) · x^(2⁵⁰-1).
  , .run 50
  , .mulStash 8
  , .stash                -- stash[9] = x^(2¹⁰⁰-1)
  -- Step 10: x^(2²⁰⁰-1) = (x^(2¹⁰⁰-1))^(2¹⁰⁰) · x^(2¹⁰⁰-1).
  , .run 100
  , .mulStash 9
  , .stash                -- stash[10] = x^(2²⁰⁰-1)
  -- Step 11: x^(2²⁵⁰-1) = (x^(2²⁰⁰-1))^(2⁵⁰) · x^(2⁵⁰-1).
  , .run 50
  , .mulStash 8
  , .stash                -- stash[11] = x^(2²⁵⁰-1)
  -- Step 12 (final): x⁻¹ = x^(2²⁵⁵-21) = (x^(2²⁵⁰-1))^5 · x¹¹.
  , .run 5
  , .mulStash 3
  -- acc = x⁻¹; no further stash needed.
  ]

/-! ## 3. Verify the chain has the published shape

Bernstein's paper / curve25519-dalek both report **254 squarings + 11
multiplications** for this chain. Verify our encoding agrees. -/

example : Block.sqrCount bernsteinInvChain = 254 := by decide
example : Block.mulCount bernsteinInvChain = 11 := by decide

theorem bernsteinInvChain_ops :
    Block.sqrCount bernsteinInvChain = 254 ∧
    Block.mulCount bernsteinInvChain = 11 := by
  refine ⟨?_, ?_⟩ <;> decide

end CatCrypt.Crypto.SecureCompilation.VIR.FieldExpChain
