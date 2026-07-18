/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Transfer.Congruence.ParamSolve
import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering

/-!
# Dialect lowering correctness synthesized by the Param engine (`param_solve`)

## Scope

`FieldToModArithLowering.lean` and `CompilerLoweringRegistry.lean` prove the
prime-field Field→ModArith lowering correct by **hand-composed transport
squares**: each prime-field op (`fAdd`/`fSub`/`fMul`) is given an *explicit*
per-op leaf coherence (`fpOpLowerTransports`, a `cases op` over the five tags),
and a multi-pass route is pasted with iterated `TransportSquare.comp`
(`registryChain_threePass`). For a *multi-op* expression `(a*b) + c` the
op-tree must be walked by the prover (the `cases`/`rfl` per node), and for a
multi-pass route the squares must be `comp`-chained adjacency-by-adjacency.

This file moves that **op-tree descent** and **pass chaining** from the hand
composition to the **`Param` engine's `param_solve`** (`Bridges/Transfer/ParamSolve.lean`):
the cross-head congruence descent of `rcongr` with the saturating closure of
`param_cc` as the leaf discharger. We

1. register the ModArith op-leaf realizers (`modAddF`/`modSubF`/`modMulF`) as
   `RelatedBinOp` squares — the Param-engine witnesses — for the prime-field
   abstract ops (`fAddF`/`fSubF`/`fMulF`), over the **identity encoding** on the
   shared carrier `ZMod p` (Field's `fp p` and ModArith's `fp p` both denote
   `ZMod p`, and `fAddF = modAddF`, `fMulF = modMulF`, `fSubF = modSubF`
   definitionally — `FieldDialect`'s leaf defs);
2. let **`param_solve` synthesize** a multi-op lowering-correctness goal —
   descending the whole op-tree in **one tactic** where the hand proof needed
   per-op leaves — and, in the multi-pass case, chaining a *second* pass through
   a context hypothesis at the closure leaf (descent **and** closure in one
   tactic), replacing a `TransportSquare.comp` adjacency;
3. record that the synthesized statement is the same op-leaf realisation the hand
   chain composes (`*_matches_hand`, `rfl`/defeq).

### What the engine discharges vs. what stays manual

* **Automatic (the deliverable).** Given the three registered squares,
  `param_solve` descends an arbitrary prime-field op-tree (`modAddF (modMulF a b)
  (modSubF c d)`, depth ≥ 2, multiple heads) **and** chains a context pass —
  with no per-op `cases`/`rfl` and no `TransportSquare.comp`. The op-tree walk
  and the pass adjacency are both synthesized.
* **Manual (the honest setup).** The three `RelatedBinOp` registrations
  themselves — each one `RelatedBinOp.mk` whose `comm` is `rfl` (the leaf
  definitional equality `fAddF = modAddF`, …). This is the *same* content as the
  hand proof's per-op leaf, but registered **once** as a reusable engine witness
  rather than re-walked per goal.

### Documented boundary (worked within, not fought)

The synthesis here is on the **prime-field, same-carrier fragment** — the exact
fragment `FieldToModArithLowering` identifies as the genuine 1:1 transport. The
`Related`-engine carrier is a **single type** `ZMod p` with the **identity
encoding** (`Related (id : ZMod p → ZMod p)`), which is the engine's diagonal /
same-carrier mode. This is *not* a limitation we hit by accident: the README's
"`TransferDom` domains are diagonal" boundary and `FieldToModArithLowering`'s
"the extension fragment is **not** a program transport (no `mapTy` target,
one-op-to-many)" verdict are the **same** boundary. The extension ops
(`ext2Mul → Fp2MulSchedule`, one op → a schedule of several) are **out of scope
for `param_solve`'s op-tree descent** for the identical reason they are out of
scope for `LoweringData`: there is no single target op / single carrier to
descend to. We therefore deliver the prime-field arm (which genuinely
synthesizes) and state precisely that the extension arm is the documented
non-diagonal / op-splitting boundary, shared verbatim with the hand framework.

**0 sorries**; target axiom set `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ParamDialectTransport

open Transfer
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-! ## 1. The prime-field lowering ops as `Param`-engine `RelatedBinOp` witnesses

The three prime-field ops lower 1:1 to ModArith leaves over the shared carrier
`ZMod p`: `fAddF = modAddF`, `fSubF = modSubF`, `fMulF = modMulF` (definitional,
from `FieldDialect`'s leaf defs). We register each as a `RelatedBinOp` square
along the **identity encoding** — the same data the hand proof's
`fpOpLowerTransports` carries per op, packaged once as a reusable engine witness.
`comm` is `rfl` (the leaf definitional equality). -/

/-- **ModArith add realizes prime-field add** (identity encoding on `ZMod p`).
    The Param-engine witness for the `fAdd ↦ modAdd` lowering leaf:
    `fAddF a b = modAddF a b` definitionally. -/
instance fpAddRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) fAddF modAddF where
  comm _ _ := rfl

/-- **ModArith sub realizes prime-field sub** (identity encoding on `ZMod p`).
    Param-engine witness for the `fSub ↦ modSub` lowering leaf. -/
instance fpSubRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) fSubF modSubF where
  comm _ _ := rfl

/-- **ModArith mul realizes prime-field mul** (identity encoding on `ZMod p`).
    Param-engine witness for the `fMul ↦ modMul` lowering leaf. -/
instance fpMulRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) fMulF modMulF where
  comm _ _ := rfl

/-! ## 2. Multi-op lowering correctness, synthesized by `param_solve` (descent)

The hand proof discharges `(a*b)+c`'s lowering by `fpOpLowerTransports`'s
per-op `cases`/`rfl` walk plus the whole-program `fundamental` lift. Here
`param_solve` **descends the op-tree** through the three registered squares in a
**single tactic**, leaving no per-op obligation. -/

/-- **Two-op lowering, synthesized.** The prime-field expression `fAddF (fMulF a
    b) c` lowers to `modAddF (modMulF a b) c` — `param_solve` descends the `+`/`*`
    op-tree through `fpAddRelated`/`fpMulRelated` in one step. The hand framework
    needs the per-op leaf (`fpOpLowerTransports`, `cases op`) at each node. -/
theorem twoOp_lowering_synth {p : Nat} (a b c : ZMod p) :
    Related (id : ZMod p → ZMod p) (fAddF (fMulF a b) c) (modAddF (modMulF a b) c) := by
  param_solve

/-- **Three-op, depth-2, multi-head lowering, synthesized.** `fAddF (fMulF a b)
    (fSubF c d)` — three distinct heads, depth 2 — lowers to its ModArith op-tree
    by a single `param_solve` descent. Hand: three per-op leaves + the tree walk. -/
theorem threeOp_lowering_synth {p : Nat} (a b c d : ZMod p) :
    Related (id : ZMod p → ZMod p)
      (fAddF (fMulF a b) (fSubF c d)) (modAddF (modMulF a b) (modSubF c d)) := by
  param_solve

/-- **The same correctness as the underlying equation** (the value-level
    realisation the L3→L2 chain composes). `param_solve` bridges the `=` to
    `Related id` and descends. This is the op-leaf realisation
    `FieldToModArithLowering`/`DialectLoweringChain` produce by transitivity —
    here synthesized by the engine. -/
theorem twoOp_lowering_eq_synth {p : Nat} (a b c : ZMod p) :
    fAddF (fMulF a b) c = modAddF (modMulF a b) c := by
  param_solve

/-! ## 3. Multi-op **and** multi-pass in one tactic (descent + closure leaf)

A multi-pass route in the hand framework is `TransportSquare.comp` adjacencies
(`registryChain_threePass`: `(pass1 ⋆ pass2) ⋆ pass3`). The Param engine's
`param_solve` chains a second pass at the **closure leaf**: after descending the
op-tree (the lowering pass), a context hypothesis `h : modAddF … = z` (a
*subsequent* carrier-preserving pass — e.g. an optimizer rewrite or a printer
identity on the lowered value) is chained **transitively** by `param_cc` — the
closure `rcongr` alone cannot reach. So one `param_solve` performs the op-tree
descent *and* the pass adjacency that the hand chain needs a `comp` for. -/

/-- **Lowering descent + a follow-on pass, in one `param_solve`.** The op-tree
    `fAddF (fMulF a b) c` is descended to `modAddF (modMulF a b) c` (the lowering
    pass), and a follow-on pass `hPass : modAddF (modMulF a b) c = z` (a
    carrier-preserving rewrite on the lowered program — the pass-2 adjacency) is
    chained through the closure leaf to land on `z`. The hand framework needs a
    `TransportSquare.comp` for this adjacency; `param_solve` synthesizes both the
    descent and the chain. -/
theorem lowering_then_pass_synth {p : Nat} (a b c z : ZMod p)
    (hPass : modAddF (modMulF a b) c = z) :
    Related (id : ZMod p → ZMod p) (fAddF (fMulF a b) c) z := by
  param_solve

/-! ## 4. The synthesized statement is the hand op-leaf realisation (defeq)

The engine-synthesized lowering correctness is **definitionally** the value-level
op-leaf realisation the hand framework composes — same statement, same proof
obligation, discharged by descent instead of a `cases`/`comp` walk. -/

/-- **The synthesized two-op lowering is the underlying op-leaf equation.**
    `param_solve`'s `Related id`-synthesis carries `.rel : id lhs = rhs`, which is
    definitionally `lhs = rhs` — the same op-leaf realisation
    (`fpOpLowerTransports`/`extChainDenote`-style value equality) the hand chain
    produces. Witnessed by `rfl`-extraction. -/
theorem twoOp_synth_matches_hand {p : Nat} (a b c : ZMod p) :
    fAddF (fMulF a b) c = modAddF (modMulF a b) c :=
  (twoOp_lowering_synth a b c).rel

/-- **The synthesized correctness defeq-matches the direct op-leaf realisation.**
    Both `param_solve`'s synthesis (via `.rel`) and the direct `rfl` realisation
    (each prime-field leaf *is* its ModArith twin) inhabit the same equation type;
    they are definitionally equal — the engine synthesis is the hand realisation,
    not a weaker corollary. -/
theorem twoOp_synth_is_rfl_realisation {p : Nat} (a b c : ZMod p) :
    twoOp_synth_matches_hand a b c = (rfl : fAddF (fMulF a b) c = modAddF (modMulF a b) c) :=
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ParamDialectTransport
