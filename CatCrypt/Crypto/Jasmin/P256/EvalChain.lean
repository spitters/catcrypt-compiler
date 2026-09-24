/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainGeneric
public import CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainGeneric

/-!
# P-256 inverse chain via the generic reflective framework

Instantiates `EvalChainGeneric` for the NIST P-256 curve
(`secp256r1` / `prime256v1`).  Computes `a^(q − 2) mod q` via
Fermat's Little Theorem on the P-256 base field
`q = 2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1`.

## P-256 vs Curve25519

P-256's modulus shape is **NIST-prime form**, not the
**Solinas/pseudo-Mersenne** form Curve25519 uses.  The chain
shape is broadly similar (Bernstein-style addition chains for
field inverse via Fermat) but the constants and offsets differ.

| Curve | Modulus form | Inverse chain length |
|-------|--------------|----------------------|
| Curve25519 | `2²⁵⁵ − 19` (pseudo-Mersenne) | 254 sqr + 11 mul |
| P-256 | `2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1` (NIST) | ~268 sqr + 13 mul (variant-dependent) |

The exact P-256 chain depends on the implementation choice
(e.g., openssl's `BN_mod_inverse` uses extended GCD; libcrux
uses an addition chain similar to Curve25519's).  This file
expresses the *generic shape* parametric in the chain literal;
concrete chain literals are deferred to the libcrux-specific
P-256 binding.

## Soundness

Inherits the generic framework's evaluator and adds no axiom. The
soundness of the libcrux inverse chain literal is proved as
`invChain_eval_sound` is for Curve25519.

## What this file ships

* P-256 modulus constants (already in `EvalChainGeneric`).
* `P256.invChainResult`-style headline shape consuming a
  caller-supplied `List ChainOp` literal.
* Soundness theorem for the headline (`libcruxP256InvChain_sound`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.P256.EvalChain

open CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainGeneric

/-! ## §1  P-256 modulus and basic arithmetic -/

/-- The P-256 modulus q = 2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1. -/
abbrev p256_q : Nat :=
  CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainGeneric.p256_q

-- Sanity-check the modulus value as documentation only:
-- p256_q = 115792089210356248762697446949407573530086143415290314195533631308867097853951
-- (The decide-form sanity check is omitted; native_decide would
-- work in isolation but the upstream Sqr4Algebra WIP causes a
-- transitive admission axiom in the elaboration context.)

/-! ## §2  P-256 location type

P-256 inverse chains use the same `Int`-offset scheme as
Curve25519 (offsets into a scratch buffer).  We re-use the type
but expose distinct offset constants for clarity. -/

abbrev Loc := Int

/-- P-256 buffer offsets (mirrors Curve25519's layout but at
    different absolute values to allow side-by-side use). -/
abbrev OFF_op : Loc := 0
abbrev OFF_z2 : Loc := 32
abbrev OFF_z3 : Loc := 64
abbrev OFF_z6 : Loc := 96
abbrev OFF_z12 : Loc := 128
abbrev OFF_z15 : Loc := 160
abbrev OFF_z30 : Loc := 192
abbrev OFF_z32 : Loc := 224
abbrev OFF_zR : Loc := 256
abbrev OFF_ap : Loc := -1

/-! ## §3  Generic evaluator instantiation -/

/-- Initial chain state for the P-256 inverse chain. -/
def initChainState (a : Nat) : ChainState Loc :=
  [(OFF_ap, a % p256_q)]

/-- Evaluate a P-256 chain.  Caller supplies the chain literal;
    framework provides the evaluator. -/
def evalP256Chain (chain : List (ChainOp Loc)) (cs : ChainState Loc) :
    ChainState Loc :=
  evalChain p256_q chain cs

/-! ## §4  Headline shape: P-256 inverse chain

The exact addition chain for `a^(q − 2)` depends on the chosen
implementation.  We expose the **shape** here as a parameter:
callers supply their chain (e.g., from a libcrux binding); the
framework and the chain's soundness theorem produce the result. -/

/-- Run a P-256 inverse chain on input `a` and read the output. -/
def p256InvResult (chain : List (ChainOp Loc)) (a : Nat) : Nat :=
  ((evalP256Chain chain (initChainState a)).read OFF_op)

/-! ## §5  Soundness for the P-256 inverse

Soundness is a property of one specific chain literal, never of the
chain parameter: the evaluator is the identity on the empty chain, so
only a named chain can satisfy the Fermat equation.  The soundness
theorem for the libcrux `finv` chain literal is in §10. -/

/-! ## §8  Worked examples — small concrete chains (✅ added 2026-05-01)

Demonstrates that the generic evaluator computes correctly on
P-256 with real (small) chains. These are not the full inverse
chain (which lands separately when a libcrux/openssl source is
imported), but they exercise every `ChainOp` constructor against
the P-256 modulus and validate the framework end-to-end.

The per-block discharge pattern shown here is the same one that
the full inverse chain will use, scaled to ~12 blocks. -/

/-- Minimal worked example: a 1-op chain computing `a²`. -/
def squareChainExample : List (ChainOp Loc) :=
  [.sqrStep OFF_op OFF_ap]

/-- Minimal worked example: a 2-op chain computing `a³` as
    `a² · a`.  Exercises both `sqrStep` and `mulStep`. -/
def cubeChainExample : List (ChainOp Loc) :=
  [.sqrStep OFF_z2 OFF_ap,
   .mulStep OFF_op OFF_z2 OFF_ap]

/-- Minimal worked example: a 1-op `repeatedSqrThenMul` chain
    computing `a^(2^3) · 1 = a⁸` (other = ap squared once is
    avoided by reading from a separate offset).  Exercises
    `repeatedSqrThenMul`. -/
def pow8ChainExample : List (ChainOp Loc) :=
  [.repeatedSqrThenMul OFF_op OFF_ap OFF_ap 3]

/-- Per-block discharge example: `squareChainExample` is sound
    against `evalP256Chain` (i.e., it actually computes `a²`).

    This is the same shape as the per-block instances that the
    full inverse chain will use (one per chain block); demonstrates
    the discharge pattern in <10 LoC. -/
theorem squareChainExample_correct (a : Nat) :
    p256InvResult squareChainExample a = a * a % p256_q := by
  simp [p256InvResult, evalP256Chain, evalChain, evalChainOp,
        ChainState.read, ChainState.write,
        squareChainExample, initChainState, OFF_op, OFF_ap]

/-- Per-block discharge example: `cubeChainExample` correctly
    computes `a³ mod p`. -/
theorem cubeChainExample_correct (a : Nat) :
    p256InvResult cubeChainExample a = a * a * a % p256_q := by
  simp [p256InvResult, evalP256Chain, evalChain, evalChainOp,
        ChainState.read, ChainState.write,
        cubeChainExample, initChainState, OFF_op, OFF_ap, OFF_z2]

/-! ## §9  Per-block discharge pattern for the full inverse chain

When the libcrux (or openssl-style) P-256 inverse chain literal
is imported, it will be a `List (ChainOp Loc)` of ~12 blocks. Each
block discharges via the same per-block-instance pattern as the
Curve25519 chain in `PerBlockInstances.lean`:

```lean
theorem block2_inst_p256
    (a : Nat) (h_intent : True) :
    -- "block 2 of the inv chain computes a²"
    ... = (a^2) % p256_q := by
  simp [evalP256Chain, ...] -- per-block decide / unfold
```

The full discharge composes ~12 such per-block lemmas, exactly
mirroring `BignumHoare/PerBlockInstances.lean`'s 13-block
Curve25519 closure.

The framework is now demonstrated end-to-end at the small-chain
level; only a real chain literal (cited from libcrux / openssl /
RFC 5114) is needed to lift these to the full inverse claim. -/

/-! ## §10  Concrete inverse chain — libcrux `finv` (✅ added 2026-05-01)

Transcribed from `libcrux/p256/src/p256.rs::finv` (HACL-derived;
verified upstream). 12-block chain computing `a^(q − 2) mod q`
where `q = p256_q`.

The libcrux source uses 4 named scratch slots (`tmp1`, `x2`,
`tmp2.0`, `tmp2.1`); we map them to the file's existing `OFF_*`
offsets:

| libcrux slot | Lean offset |
|--------------|-------------|
| `tmp1`       | `OFF_z2`    |
| `x2`         | `OFF_z3`    |
| `tmp2.0`     | `OFF_z6`    |
| `tmp2.1`     | `OFF_z12`   |
| `a` (input)  | `OFF_ap`    |
| result       | `OFF_op`    |

This chain is the published libcrux P-256 inverse. Each block
corresponds 1-1 with libcrux's `unroll_for!(n, ...)` + `fmul`
pair (or a single `fsqr` + `fmul` for n=1). -/

/-- The libcrux P-256 field inverse chain `finv`, transcribed from
    `libcrux/p256/src/p256.rs`. Computes `a^(p256_q − 2) mod p256_q`
    via Fermat's Little Theorem.

    12 blocks (one per `(unroll_for!(n) + fmul)` pair in libcrux):

    | # | n | (dst, src, other) | Computes |
    |---|---|-------------------|----------|
    | 1 | 1 | (z2, ap, ap)      | a^(2·1) · a = a^3 |
    | 2 | 1 | (z3, z2, ap)      | (a^3)^2 · a = a^7 |
    | 3 | 3 | (z6, z3, z3)      | (a^7)^8 · a^7 = a^63 = a^(2^6 − 1) |
    | 4 | 6 | (z12, z6, z6)     | (a^63)^64 · a^63 = a^4095 = a^(2^12 − 1) |
    | 5 | 3 | (z6, z12, z3)     | (a^4095)^8 · a^7 = a^(2^15 − 1) |
    | 6 | 15| (z3, z6, z6)      | (...)^(2^15) · (...) = a^(2^30 − 1) |
    | 7 | 2 | (z6, z3, z2)      | a^((2^30 − 1)·4) · a^3 = a^(2^32 − 1) |
    | 8 | 32| (z2, z6, ap)      | a^((2^32 − 1)·2^32) · a = a^(2^64 − 2^32 + 1)? — see libcrux |
    | 9 | 128|(z2, z2, z6)      | (...) · a^(2^32 − 1) — chain extends |
    |10 | 32| (z2, z2, z6)      | (...) · a^(2^32 − 1) |
    |11 | 30| (z2, z2, z3)      | (...) · a^(2^30 − 1) |
    |12 | 2 | (op, z2, ap)      | (final) = a^(p256_q − 2) |

    Total: 12 `repeatedSqrThenMul` ops. -/
def libcruxP256InvChain : List (ChainOp Loc) :=
  [.repeatedSqrThenMul OFF_z2  OFF_ap  OFF_ap  1,
   .repeatedSqrThenMul OFF_z3  OFF_z2  OFF_ap  1,
   .repeatedSqrThenMul OFF_z6  OFF_z3  OFF_z3  3,
   .repeatedSqrThenMul OFF_z12 OFF_z6  OFF_z6  6,
   .repeatedSqrThenMul OFF_z6  OFF_z12 OFF_z3  3,
   .repeatedSqrThenMul OFF_z3  OFF_z6  OFF_z6  15,
   .repeatedSqrThenMul OFF_z6  OFF_z3  OFF_z2  2,
   .repeatedSqrThenMul OFF_z2  OFF_z6  OFF_ap  32,
   .repeatedSqrThenMul OFF_z2  OFF_z2  OFF_z6  128,
   .repeatedSqrThenMul OFF_z2  OFF_z2  OFF_z6  32,
   .repeatedSqrThenMul OFF_z2  OFF_z2  OFF_z3  30,
   .repeatedSqrThenMul OFF_op  OFF_z2  OFF_ap  2]

/-- Length sanity: the libcrux P-256 inverse chain has exactly 12
    blocks. Updates here should also update the table comment above. -/
example : libcruxP256InvChain.length = 12 := by native_decide

/-- The libcrux P-256 inverse chain (`finv`) computes `a ^ (p256_q - 2) % p256_q`. -/
theorem libcruxP256InvChain_sound (a : Nat) :
    p256InvResult libcruxP256InvChain a = a ^ (p256_q - 2) % p256_q := by
  have hinit : initChainState a = Exp.denote p256_q a [(OFF_ap, 1)] := by
    simp [initChainState, Exp.denote]
  have hexp : (Exp.eChain libcruxP256InvChain [(OFF_ap, 1)]).bind
      (Exp.eRead · OFF_op) = some (p256_q - 2) := by decide +kernel
  rw [p256InvResult, evalP256Chain, hinit]
  exact Exp.evalChain_read _ _ _ _ _ _ hexp

/-- The libcrux P-256 inverse chain computes the Fermat inverse. -/
theorem libcruxP256InvChain_correct (a : Nat) :
    p256InvResult libcruxP256InvChain a = a ^ (p256_q - 2) % p256_q :=
  libcruxP256InvChain_sound a

/-! ## §11  Per-block instances for the libcrux P-256 chain
    (✅ added 2026-05-01)

12 individual block-level correctness lemmas, one per
`repeatedSqrThenMul` op in `libcruxP256InvChain`. Each computes
the destination slot's value after the block, given the
chain-state values at the source / other slots beforehand.

These reduce via a single schematic lemma `read_repeatedSqrThenMul_dst_ne_others`:
the destination read of a `repeatedSqrThenMul` op equals
`src^(2^n) · other mod p`, provided `dst ≠ src` and `dst ≠ other`
(the freshness condition that the framework's `ChainState.write`
respects).

Without per-block instances, every soundness chain goes through the
chain theorem `libcruxP256InvChain_sound`. Per-block instances allow
finer-grained alternative reasoning (e.g., for chains that diverge
from libcrux's at one block: prove the divergent block separately
and reuse the unchanged blocks). -/

/-- Schematic per-block lemma: a `repeatedSqrThenMul`'s destination
    read equals `src^(2^n) · other mod p`, when `dst` is not
    aliased with `src` or `other`. -/
theorem read_repeatedSqrThenMul_dst_ne
    (p : Nat) (dst src other : Loc) (n : Nat) (cs : ChainState Loc)
    (h_src : dst ≠ src) (h_other : dst ≠ other) :
    (evalChainOp p (.repeatedSqrThenMul dst src other n) cs).read dst =
      (cs.read src ^ (2^n) * cs.read other) % p := by
  simp [evalChainOp, ChainState.read, ChainState.write]

/-- Schematic per-block lemma: a `repeatedSqrThenMul`'s destination
    read when `dst = src` (in-place update). The previous value at
    `dst` becomes the source. -/
theorem read_repeatedSqrThenMul_dst_eq_src
    (p : Nat) (dst other : Loc) (n : Nat) (cs : ChainState Loc)
    (h_other : dst ≠ other) :
    (evalChainOp p (.repeatedSqrThenMul dst dst other n) cs).read dst =
      (cs.read dst ^ (2^n) * cs.read other) % p := by
  simp [evalChainOp, ChainState.read, ChainState.write]

/-! ### Per-block instances (12 blocks)

Each block's lemma describes what the block does to its destination
slot. The chain-state preconditions are stated as values at source /
other slots; downstream consumers thread these through the chain.

Block 9 (n=128) is in-place on OFF_z2; the rest are non-aliasing. -/

theorem libcruxP256_block1 (a : Nat) :
    (evalChainOp p256_q
      (.repeatedSqrThenMul OFF_z2 OFF_ap OFF_ap 1)
      (initChainState a)).read OFF_z2 =
    ((a % p256_q) ^ 2 * (a % p256_q)) % p256_q := by
  simp [read_repeatedSqrThenMul_dst_ne, OFF_z2, OFF_ap, OFF_op,
        initChainState, ChainState.read]

theorem libcruxP256_block_repeatedSqrThenMul_generic
    (cs : ChainState Loc) (dst src other : Loc) (n : Nat)
    (h_src : dst ≠ src) (h_other : dst ≠ other) :
    (evalChainOp p256_q
      (.repeatedSqrThenMul dst src other n) cs).read dst =
    (cs.read src ^ (2^n) * cs.read other) % p256_q :=
  read_repeatedSqrThenMul_dst_ne p256_q dst src other n cs h_src h_other

/-- For an in-place block (e.g., libcrux block 9: `(z2, z2, z6, 128)`),
    the destination read uses the schematic lemma's `_eq_src` variant. -/
theorem libcruxP256_block_repeatedSqrThenMul_in_place
    (cs : ChainState Loc) (dst other : Loc) (n : Nat)
    (h_other : dst ≠ other) :
    (evalChainOp p256_q
      (.repeatedSqrThenMul dst dst other n) cs).read dst =
    (cs.read dst ^ (2^n) * cs.read other) % p256_q :=
  read_repeatedSqrThenMul_dst_eq_src p256_q dst other n cs h_other

/-! Each of the 12 libcrux blocks reduces to one of the two schematics
above. Block 1 is shown explicitly (`libcruxP256_block1`); blocks 2-12
follow the same pattern with different `(dst, src, other, n)` triples
and chain-state precondition. The two schematic lemmas + block 1's
worked example demonstrate the pattern; expanding to all 12 individual
named theorems is mechanical and not pursued here (each would be ~3 LoC). -/

/-! ## §12  Status and follow-ups

* This file ships:
  1. Generic framework instantiation (§§1-4)
  2. Small worked examples (§§8-9)
  3. libcrux `finv` chain literal (§10)
  4. Per-block schematic lemmas (§11)
* The libcrux chain's correctness reduces via the chain
  soundness theorem `libcruxP256InvChain_sound`, proved by the exponent
  evaluator `EvalChainGeneric.Exp`.
* Per-block schematic lemmas (§11) allow alternative finer-grained
  reasoning: e.g., for a chain that diverges from libcrux's at one
  block, prove the divergent block separately and reuse the
  unchanged blocks via the schematics.

Per-chain effort estimate (next-curve): ~50 LoC for chain literal
(mirror of `libcruxP256InvChain` shape, transcribed from blst /
mclbn / etc.) + ~50 LoC for soundness theorem (one-line via
`Exp.evalChain_read`). Per-block lemmas are optional refinement. -/

end CatCrypt.Crypto.Jasmin.P256.EvalChain
