/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Transfer.Congruence.ParamSolve
import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-!
# PQC NTT-kernel lowering transport synthesized by the Param engine (`param_solve`)

## Scope

`ParamDialectTransport.lean` showed that the `Param` engine's `param_solve`
synthesizes the **Field → ModArith** lowering transport: the prime-field ops
`fAdd`/`fSub`/`fMul` are registered as `RelatedBinOp` squares over the identity
encoding on the shared carrier `ZMod p`, and `param_solve` descends an arbitrary
prime-field op-tree (with cross-head congruence) in **one tactic**, the
synthesized transport defeq to the hand op-leaf realisation.

This file does the **same thing for a post-quantum signature/KEM arithmetic
kernel** — the ML-DSA / ML-KEM **NTT butterfly** modular arithmetic at the PQC
prime. The Cooley–Tukey / Gentleman–Sande butterfly is the inner loop of every
NTT-based lattice scheme:

    (a, t)  ↦  (a + t·ζ,  a − t·ζ)      over  ZMod q

with `q = 8380417` (ML-DSA / Dilithium) or `q = 3329` (ML-KEM / Kyber). Each
component is a **same-carrier modular-arithmetic op-tree** over `ZMod q`:
`modAdd`/`modSub`/`modMul` (the zeta-multiply `t·ζ`, then the add/sub combine).

We:

1. register the ModArith op-leaf realizers (`modAddF`/`modSubF`/`modMulF`)
   **at the PQC prime** as `RelatedBinOp` squares — the Param-engine witnesses —
   for the abstract residue-ring ops (`ZMod q`'s `+`/`-`/`*`), over the identity
   encoding on the shared carrier `ZMod q`. `ML-DSA` (`q = 8380417`) and `ML-KEM`
   (`q = 3329`) are *instances of the same `{p : Nat}`-generic registration*: the
   PQC kernel is the same diagonal same-carrier fragment, only the modulus
   differs. `comm` is `rfl` (the leaf definitional equality `modAddF = (· + ·)`,
   …, from `ModArithDialect`'s `@[reducible]` leaf defs);
2. let **`param_solve` synthesize** the butterfly's lowering transport —
   descending the whole `(a + t·ζ)` / `(a − t·ζ)` op-tree (depth-2, multi-head)
   in **one tactic** where a hand proof needs a per-op `cases`/`rfl` walk — and,
   in the multi-pass case, chaining a follow-on carrier-preserving pass through
   the closure leaf (descent **and** closure in one tactic);
3. record that the synthesized statement is the underlying op-leaf realisation
   (`*_matches_hand`, `rfl`/defeq) — the engine synthesis is the hand result, not
   a weaker corollary.

### The applicability verdict (the question answered)

* **Where the engine applies.** `param_solve` synthesizes the PQC kernel's
  lowering transport on the **same-carrier modular-arithmetic fragment** — the
  NTT butterfly's `modAdd`/`modSub`/`modMul` op-tree over `ZMod q` at the PQC
  prime. This is the engine's diagonal / single-carrier mode (`Related (id :
  ZMod q → ZMod q)`), and it applies to the PQC kernel **exactly** as it did to
  Field → ModArith: same `RelatedBinOp` registration, same descent, same defeq
  to the hand op-leaf realisation. The PQC prime is just a value of `p`; nothing
  about the engine's reach is PQC-specific.

* **Where it hits the boundary — the *same* boundary as the general dialect
  transport, not a PQC-specific one.** The carrier-**changing** part of the PQC
  lowering is out of `param_solve`'s op-tree descent, for the identical reason
  the Field extension fragment was in `ParamDialectTransport`:

  - **Montgomery domain change.** The real hardware butterfly runs in the
    Montgomery domain: `t·ζ` is a `montMul` (`a·b·R⁻¹`), and entering/leaving
    the domain is `· * R` / `· * R⁻¹`. `montMulF rInv a b` is **ternary** (it
    carries the radix parameter `rInv`) — it is *not* an `A → A → A` binary op,
    so it does not fit `RelatedBinOp`, and the domain maps are a carrier
    *re-coordinatisation* (`ZMod q` Montgomery-rep vs. residue), not the identity
    encoding. This is the `CarrierTransferDom`/non-diagonal `lo32`-style frontier,
    the same one `ParamDialectTransport` documents — with the named
    radix/limb-predicate parameter `rInv` as the obstruction.

  - **Reduce / word boundary.** The concrete reduce (`barrettReduce` at `q`,
    Plantard/Montgomery reduce) is `word w → fp q` — it *changes carrier*
    (`BitVec w → ZMod q`), so it is not a same-carrier `RelatedBinOp` and is
    not reached by the descent.

  - **Op-splitting / schedule.** A whole-NTT-layer (a butterfly *network* across
    `n/2` index pairs with a fixed twiddle schedule, and the de-Bruijn–indexed
    `Com` program that lays it out) is *one logical op → a block of indexed ops*
    — the same op-splitting / no-single-target-op boundary that put `ext2Mul →
    Fp2MulSchedule` out of scope for `LoweringData` and `param_solve` alike.

So the verdict: **yes, the Param engine applies to PQC kernels at the
same-carrier modular-arithmetic fragment (the NTT butterfly's
`modAdd`/`modSub`/`modMul` op-tree at the PQC prime); the boundary is the
carrier-changing part (Montgomery-domain re-coordinatisation via the ternary
`montMul`/`rInv`, the `word → fp` reduce, and the butterfly-network schedule) —
the *same* diagonal / same-carrier boundary the general dialect transport hits,
not a PQC-specific one.**

We deliver the same-carrier butterfly arm (which genuinely synthesizes) and
state the carrier-changing arm precisely as the shared boundary, with
`CarrierTransferDom`'s non-diagonal `lo32` `TransferDom` named as the path for
the carrier-changing Montgomery/reduce part. We do **not** claim whole-PQC-kernel
synthesis: only the modular-arithmetic op-tree synthesizes here.

**0 sorries**; target axiom set `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ParamPqcKernel

open Transfer
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-! ## 0. The PQC primes (the kernel instances) -/

/-- The ML-DSA / Dilithium modulus `q = 2^23 − 2^13 + 1`. -/
abbrev mldsaQ : Nat := 8380417

/-- The ML-KEM / Kyber modulus `q = 3329`. -/
abbrev mlkemQ : Nat := 3329

/-! ## 1. The PQC modular ops as `Param`-engine `RelatedBinOp` witnesses

The three residue-ring ops lower 1:1 to ModArith leaves over the shared carrier
`ZMod p`: `modAddF = (· + ·)`, `modSubF = (· - ·)`, `modMulF = (· * ·)`
(definitional, from `ModArithDialect`'s `@[reducible]` leaf defs). We register
each as a `RelatedBinOp` square along the **identity encoding** — generic in the
modulus `p`, so the ML-DSA (`p = 8380417`) and ML-KEM (`p = 3329`) butterflies are
the *same* registration at different `p`. `comm` is `rfl`. -/

/-- **ModArith add realizes residue-ring add** at any modulus (identity encoding
    on `ZMod p`). The Param-engine witness for the PQC butterfly's `+` combine:
    `(a + b) = modAddF a b` definitionally. -/
instance pqcAddRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) (· + ·) modAddF where
  comm _ _ := rfl

/-- **ModArith sub realizes residue-ring sub** at any modulus. Param-engine
    witness for the PQC butterfly's `−` combine (the Gentleman–Sande arm). -/
instance pqcSubRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) (· - ·) modSubF where
  comm _ _ := rfl

/-- **ModArith mul realizes residue-ring mul** at any modulus. Param-engine
    witness for the PQC butterfly's twiddle multiply `t·ζ`. -/
instance pqcMulRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) (· * ·) modMulF where
  comm _ _ := rfl

/-! ## 2. The NTT butterfly arithmetic, synthesized by `param_solve` (descent)

The Cooley–Tukey butterfly combine `(a + t·ζ, a − t·ζ)` over `ZMod q` is a pair
of same-carrier modular-arithmetic op-trees. Each component (depth-2, multiple
heads) is descended by `param_solve` through the three registered squares in a
**single tactic**, leaving no per-op obligation. We state both the generic-`p`
form and the two PQC instances (ML-DSA `8380417`, ML-KEM `3329`). -/

/-- **Butterfly upper half, generic modulus, synthesized.** `a + t·ζ` lowers to
    `modAddF a (modMulF t ζ)` — `param_solve` descends the `+`/`*` op-tree through
    `pqcAddRelated`/`pqcMulRelated` in one step. -/
theorem butterflyUpper_synth {p : Nat} (a t ζ : ZMod p) :
    Related (id : ZMod p → ZMod p) (a + t * ζ) (modAddF a (modMulF t ζ)) := by
  param_solve

/-- **Butterfly lower half, generic modulus, synthesized.** `a − t·ζ` lowers to
    `modSubF a (modMulF t ζ)` — the Gentleman–Sande arm, descended in one step. -/
theorem butterflyLower_synth {p : Nat} (a t ζ : ZMod p) :
    Related (id : ZMod p → ZMod p) (a - t * ζ) (modSubF a (modMulF t ζ)) := by
  param_solve

/-- **A full butterfly stage as a combined op-tree, synthesized.** The combine
    `(a + t·ζ) + (a − t·ζ)` (a depth-3, three-distinct-head expression — `+`, `-`,
    `*`) lowers to its ModArith op-tree by a single `param_solve` descent. A hand
    proof needs the per-op leaves at each of the five nodes plus the tree walk. -/
theorem butterflyStage_synth {p : Nat} (a t ζ : ZMod p) :
    Related (id : ZMod p → ZMod p)
      ((a + t * ζ) + (a - t * ζ))
      (modAddF (modAddF a (modMulF t ζ)) (modSubF a (modMulF t ζ))) := by
  param_solve

/-- **ML-DSA (Dilithium, `q = 8380417`) butterfly upper half, synthesized.** The
    same engine, at the ML-DSA prime — the PQC instance of `butterflyUpper_synth`.
    Demonstrates the synthesis is not generic-`p`-only: it fires at the concrete
    PQC modulus. -/
theorem mldsa_butterflyUpper_synth (a t ζ : ZMod mldsaQ) :
    Related (id : ZMod mldsaQ → ZMod mldsaQ)
      (a + t * ζ) (modAddF a (modMulF t ζ)) := by
  param_solve

/-- **ML-KEM (Kyber, `q = 3329`) butterfly lower half, synthesized.** The same
    engine at the ML-KEM prime — the second PQC instance. -/
theorem mlkem_butterflyLower_synth (a t ζ : ZMod mlkemQ) :
    Related (id : ZMod mlkemQ → ZMod mlkemQ)
      (a - t * ζ) (modSubF a (modMulF t ζ)) := by
  param_solve

/-- **The same correctness as the underlying equation** (the value-level
    realisation the lowering chain composes). `param_solve` bridges the `=` to
    `Related id` and descends. This is the op-leaf realisation a
    `DialectLoweringChain` at the PQC prime would produce by transitivity — here
    synthesized by the engine. -/
theorem butterflyUpper_eq_synth {p : Nat} (a t ζ : ZMod p) :
    a + t * ζ = modAddF a (modMulF t ζ) := by
  param_solve

/-! ## 3. Butterfly descent **and** a follow-on pass in one tactic (descent + closure)

A multi-pass route — the butterfly lowering followed by a subsequent
carrier-preserving pass on the lowered value (an optimizer rewrite, a constant
fold, or a printer identity on `ZMod q`) — is, in the hand framework, a
`TransportSquare.comp` adjacency. `param_solve` chains the second pass at the
**closure leaf**: after descending the butterfly op-tree (the lowering pass), a
context hypothesis `h : modAddF … = z` is chained transitively by the closure —
the descent alone cannot reach it. So one `param_solve` performs the op-tree
descent *and* the pass adjacency. -/

/-- **Butterfly descent + a follow-on pass, in one `param_solve`.** The op-tree
    `a + t·ζ` is descended to `modAddF a (modMulF t ζ)` (the lowering pass), and a
    follow-on carrier-preserving pass `hPass : modAddF a (modMulF t ζ) = z` (a
    subsequent rewrite on the lowered `ZMod q` value — the pass-2 adjacency) is
    chained through the closure leaf to land on `z`. The hand framework needs a
    `TransportSquare.comp` for this adjacency. -/
theorem butterfly_then_pass_synth {p : Nat} (a t ζ z : ZMod p)
    (hPass : modAddF a (modMulF t ζ) = z) :
    Related (id : ZMod p → ZMod p) (a + t * ζ) z := by
  param_solve

/-! ## 4. The synthesized statement is the hand op-leaf realisation (defeq)

The engine-synthesized PQC butterfly lowering is **definitionally** the
value-level op-leaf realisation the hand framework composes — same statement,
same proof obligation, discharged by descent instead of a `cases`/`comp` walk. -/

/-- **The synthesized butterfly lowering is the underlying op-leaf equation.**
    `param_solve`'s `Related id`-synthesis carries `.rel : id lhs = rhs`, which is
    definitionally `lhs = rhs` — the same op-leaf realisation a hand chain
    produces. Witnessed by `.rel`-extraction. -/
theorem butterflyUpper_synth_matches_hand {p : Nat} (a t ζ : ZMod p) :
    a + t * ζ = modAddF a (modMulF t ζ) :=
  (butterflyUpper_synth a t ζ).rel

/-- **The synthesized correctness defeq-matches the direct op-leaf realisation.**
    Both `param_solve`'s synthesis (via `.rel`) and the direct `rfl` realisation
    (each residue-ring leaf *is* its ModArith twin) inhabit the same equation
    type; they are definitionally equal — the engine synthesis is the hand
    realisation, not a weaker corollary. -/
theorem butterflyUpper_synth_is_rfl_realisation {p : Nat} (a t ζ : ZMod p) :
    butterflyUpper_synth_matches_hand a t ζ
      = (rfl : a + t * ζ = modAddF a (modMulF t ζ)) :=
  rfl

/-! ## 5. The carrier-changing boundary, recorded honestly (NOT synthesized)

The same-carrier butterfly arm above genuinely synthesizes. The carrier-changing
part of the PQC lowering — the Montgomery-domain twiddle multiply — is out of
`param_solve`'s op-tree descent, for the *same* reason the Field extension
fragment was in `ParamDialectTransport`: it is not a same-carrier binary
`RelatedBinOp`. We record it as exactly that.

The real hardware butterfly's twiddle multiply is a `montMul` carrying the
radix-inverse parameter `rInv`: `montMulF rInv t ζ = t · ζ · R⁻¹`. This is a
**ternary** function `(rInv, t, ζ) ↦ …`, not an `A → A → A` binary op, so it does
not fit `RelatedBinOp` and is not reached by the descent. The `rInv` parameter is
the named radix / limb-predicate obstruction — the carrier re-coordinatisation
(`ZMod q` Montgomery-rep vs. residue), the non-diagonal `CarrierTransferDom` path,
exactly as the general dialect transport documents. -/

/-- **The Montgomery twiddle multiply is a value-level identity carrying the radix
    parameter — not a binary `RelatedBinOp`.** `montMulF rInv t ζ = t · ζ · rInv`
    holds (definitionally, `montMul`'s denotation), but the `rInv` argument means
    it is a *ternary* op, so it lives at the carrier-changing
    (Montgomery-domain) boundary, not the same-carrier diagonal `param_solve`
    descends. This is the shared boundary, recorded as the value-level fact it is
    (the descent does not reach it; the non-diagonal `CarrierTransferDom` would). -/
theorem montgomery_twiddle_is_value_level {p : Nat} (rInv t ζ : ZMod p) :
    montMulF rInv t ζ = t * ζ * rInv := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ParamPqcKernel
