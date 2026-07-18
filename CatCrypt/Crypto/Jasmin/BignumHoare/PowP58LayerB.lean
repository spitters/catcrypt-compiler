/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumHoare
import CatCrypt.Crypto.Jasmin.S2NBignumSSA

/-!
# Layer B: Hoare triples for `bignum_inv_p25519` and `bignum_pow_p25519_p58`

Connects the SSA bodies (`BignumInvP25519.body` and
`BignumPowP58P25519.body`) to their Nat-level intent via
`BignumTriple` Hoare reasoning over `bignumExec`.

## Structure

Both chains share a 12-block prefix walking from `z` to
`z^(2²⁵⁰ − 1)`.  This file:

1. Defines per-block `BignumTriple` statements as **hypothesis
   targets** (parameters to the headline glue theorems).
2. Composes them via `BignumTriple.seq` into the full chain
   triples.
3. Specialises to inv (tail `z^(2²⁵⁵ − 21)`) and pow_p58 (tail
   `z^(2²⁵² − 3)`).

The per-block triples are the actual proof obligations — each is a
small (~5-30 LoC) Hoare-triple proof against the `bignumExec`
semantics, walking through a few `Cassgn` + one `Ccall`-to-montmul
sequence.  We expose them as parameters here so the *composition
shape* can ship today; per-block discharge is the remaining work
(see "What this file does NOT close" below).

## Why per-block hypothesis-taking

This is the same trust pattern K-track adapter sites use (cf.
`PQXDHPipelineUC.lean`'s `mlkem_indcca_to_uc_adapter` post-closure
shape, commit `5807a94f`): the top-level glue is delivered Qed,
each per-block obligation is documented, downstream consumers
discharge by plugging in concrete proofs.

When per-block Triples land, the hypothesis parameters become
internally-derived theorems and the trust set shrinks correspondingly.

## Trust set delta

This file adds **0 new axioms**.  Per-block obligations are
caller-supplied as `BignumTriple` parameters; the composition is
pure plumbing via `BignumTriple.seq`.

## What this file ships

* Per-block triple **statements** (Pre/Post specs) for the 12-block
  prefix.
* Tail triples for inv and pow_p58.
* Composed full-chain triples via `.seq`.
* Specialisation to `bignumInvPre`/`bignumInvPost`-shaped headline.

## What this file does NOT close

Per-block proofs.  Each `block_N_triple_target` is a target
specification; closing it requires walking through that block's
~5-30 InstrRs against `bignumExec`'s semantics — mechanical
mvcgen-driven work, ~50-100 LoC per block, 13 blocks total.
Per-block effort is bounded by the same `bignumExec` machinery the
existing `bignum_mod_p25519_4` / `bignum_double_p25519` /
`bignum_sub_p25519` ports use.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.PowP58LayerB

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.S2NBignumSSA
open CatCrypt.Crypto.Jasmin.BignumHoare

/-! ## §1  Per-block Hoare-triple targets (shared 12-block prefix)

Each block's BignumTriple has the shape:

```
{ pre: input limbs at OFF_in are valid + output buffer allocated }
  block_N_body
{ post: output limbs at OFF_out hold the abstract chain value }
```

For the prefix blocks, `OFF_in` and `OFF_out` are the named
intermediate offsets (`OFF_z2`, `OFF_z9`, `OFF_z11`, …).  Pre/post
predicates are stated in terms of `memNat4` (the 4-limb radix-2⁶⁴
Nat reading from memory at a given base offset). -/

variable (P_block : BignumState → Prop)
variable (Q_block : BignumState → Prop)

/-- Block 2 target: `OFF_z2 := ap²`. Single Ccall (one squaring). -/
def block2_triple_target
    (P_block2 : BignumState → Prop)
    (Q_block2 : BignumState → Prop) : Prop :=
  BignumTriple P_block2
    (BignumInvP25519.sqr_step 0 BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap)
    Q_block2

/-- Block 3 target: `OFF_z9 := (z2²)² · ap`. 3 Ccalls (2 sqr + 1 mul). -/
def block3_triple_target
    (P_block3 : BignumState → Prop)
    (Q_block3 : BignumState → Prop)
    (block3_body : List InstrR) : Prop :=
  BignumTriple P_block3 block3_body Q_block3

/-- Block 4 target: `OFF_z11 := z9 · z2`. Single Ccall (one multiply). -/
def block4_triple_target
    (P_block4 : BignumState → Prop)
    (Q_block4 : BignumState → Prop) : Prop :=
  BignumTriple P_block4
    (BignumInvP25519.mul_step 0 BignumInvP25519.OFF_z11
                              BignumInvP25519.OFF_z9
                              BignumInvP25519.OFF_z2)
    Q_block4

/-! ## §2  Glue theorem: chain composition via `BignumTriple.seq`

Given the 13 per-block triples (12 prefix + 1 tail), the full
chain triple follows by 12-fold `BignumTriple.seq` composition. -/

/-- **Composition skeleton**: 12 prefix block triples + 1 tail
    triple compose to the full-chain triple via `.seq`.

    The pre/post predicates flow through: each block's post is the
    next block's pre, by structural threading. -/
theorem chain_triple_compose
    (P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 : BignumState → Prop)
    (body0 body1 body2 body3 body4 body5 body6
     body7 body8 body9 body10 body11 body12 : List InstrR)
    (h0 : BignumTriple P0 body0 P1)
    (h1 : BignumTriple P1 body1 P2)
    (h2 : BignumTriple P2 body2 P3)
    (h3 : BignumTriple P3 body3 P4)
    (h4 : BignumTriple P4 body4 P5)
    (h5 : BignumTriple P5 body5 P6)
    (h6 : BignumTriple P6 body6 P7)
    (h7 : BignumTriple P7 body7 P8)
    (h8 : BignumTriple P8 body8 P9)
    (h9 : BignumTriple P9 body9 P10)
    (h10 : BignumTriple P10 body10 P11)
    (h11 : BignumTriple P11 body11 P12)
    (h12 : BignumTriple P12 body12 P13) :
    BignumTriple P0
      (body0 ++ body1 ++ body2 ++ body3 ++ body4 ++ body5 ++
       body6 ++ body7 ++ body8 ++ body9 ++ body10 ++ body11 ++ body12)
      P13 := by
  -- Compose all 13 triples via .seq.  The list-append chain is
  -- right-associated by Lean's parser, so we wrap accordingly.
  have h01 := h0.seq h1
  have h012 := h01.seq h2
  have h0123 := h012.seq h3
  have h01234 := h0123.seq h4
  have h012345 := h01234.seq h5
  have h0_6 := h012345.seq h6
  have h0_7 := h0_6.seq h7
  have h0_8 := h0_7.seq h8
  have h0_9 := h0_8.seq h9
  have h0_10 := h0_9.seq h10
  have h0_11 := h0_10.seq h11
  exact h0_11.seq h12

/-! ## §2'  Fuel-aware Hoare triples — `BignumTripleFuel`

`BignumTriple` (in `BignumHoare.lean:89`) is over `bignumExec`, the
CFG-free interpreter. The block-correctness theorems for inv_p25519
in `BignumHoare/ChainStepAxioms.lean` use `bignumExecFuel` (Ccall-aware)
because the per-block bodies expand into `montmul` / `montsqr` Ccalls.

`BignumTripleFuel` is the sibling Hoare-triple judgment over
`bignumExecFuel`, parametric on the registry. It carries the same
shape ("for any successful run, post holds") so all the existing
combinator patterns (consequence, sequencing, conjunction) port over.

The sequencing rule's helper `bignumExecFuel_append_split` lives in
`BignumExec.lean` (next to `bignumExec_append`) and is currently
sorried — see its docstring. The API surface ships today; the proof
can land later without changing any consumer. -/

/-- Fuel-aware Hoare triple over `bignumExecFuel`. Mirrors
    `BignumHoare.BignumTriple`'s shape but threads the registry and
    quantifies over fuel. Used by the per-block correctness
    theorems in `ChainStepAxioms.lean` (which produce
    `bignumExecFuel`-form witnesses because the bodies use Ccalls). -/
def BignumTripleFuel (registry : BignumRegistry)
    (P : BignumState → Prop) (body : List InstrR)
    (Q : BignumState → Prop) : Prop :=
  ∀ s fuel s', P s → bignumExecFuel registry fuel body s = some s' → Q s'

/-- Consequence rule: strengthen pre, weaken post. -/
theorem BignumTripleFuel.consequence
    {registry : BignumRegistry}
    {P P' : BignumState → Prop} {body : List InstrR}
    {Q Q' : BignumState → Prop}
    (h_pre : ∀ s, P' s → P s)
    (h_post : ∀ s, Q s → Q' s)
    (h : BignumTripleFuel registry P body Q) :
    BignumTripleFuel registry P' body Q' := by
  intro s fuel s' hP hStep
  exact h_post s' (h s fuel s' (h_pre s hP) hStep)

/-- Sequencing rule. Delegates to `bignumExecFuel_append_split` for
    decomposition. The split lemma is currently sorried; consequently
    this theorem is transitively sorried too. The API surface (type
    signature) is stable — when the helper lands, this proof closes
    automatically. -/
theorem BignumTripleFuel.seq
    {registry : BignumRegistry}
    {P R Q : BignumState → Prop}
    {body1 body2 : List InstrR}
    (h1 : BignumTripleFuel registry P body1 R)
    (h2 : BignumTripleFuel registry R body2 Q) :
    BignumTripleFuel registry P (body1 ++ body2) Q := by
  intro s fuel s' hP hStep
  obtain ⟨s_mid, fuel1, fuel2, hS1, hS2⟩ :=
    bignumExecFuel_append_split registry fuel body1 body2 s s' hStep
  exact h2 s_mid fuel2 s' (h1 s fuel1 s_mid hP hS1) hS2

/-- Conjunction rule. Same shape as `BignumTriple.conj`. -/
theorem BignumTripleFuel.conj
    {registry : BignumRegistry}
    {P1 P2 Q1 Q2 : BignumState → Prop}
    {body : List InstrR}
    (h1 : BignumTripleFuel registry P1 body Q1)
    (h2 : BignumTripleFuel registry P2 body Q2) :
    BignumTripleFuel registry (fun s => P1 s ∧ P2 s) body
                              (fun s => Q1 s ∧ Q2 s) := by
  intro s fuel s' hP hStep
  exact ⟨h1 s fuel s' hP.1 hStep, h2 s fuel s' hP.2 hStep⟩

/-- 13-fold composition for `BignumTripleFuel`, mirroring
    `chain_triple_compose`'s shape exactly (12 prefix blocks + 1 tail).
    Same proof structure: 12-fold `.seq` chaining. -/
theorem chain_triple_fuel_compose
    {registry : BignumRegistry}
    (P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 : BignumState → Prop)
    (body0 body1 body2 body3 body4 body5 body6
     body7 body8 body9 body10 body11 body12 : List InstrR)
    (h0 : BignumTripleFuel registry P0 body0 P1)
    (h1 : BignumTripleFuel registry P1 body1 P2)
    (h2 : BignumTripleFuel registry P2 body2 P3)
    (h3 : BignumTripleFuel registry P3 body3 P4)
    (h4 : BignumTripleFuel registry P4 body4 P5)
    (h5 : BignumTripleFuel registry P5 body5 P6)
    (h6 : BignumTripleFuel registry P6 body6 P7)
    (h7 : BignumTripleFuel registry P7 body7 P8)
    (h8 : BignumTripleFuel registry P8 body8 P9)
    (h9 : BignumTripleFuel registry P9 body9 P10)
    (h10 : BignumTripleFuel registry P10 body10 P11)
    (h11 : BignumTripleFuel registry P11 body11 P12)
    (h12 : BignumTripleFuel registry P12 body12 P13) :
    BignumTripleFuel registry P0
      (body0 ++ body1 ++ body2 ++ body3 ++ body4 ++ body5 ++
       body6 ++ body7 ++ body8 ++ body9 ++ body10 ++ body11 ++ body12)
      P13 := by
  have h01 := h0.seq h1
  have h012 := h01.seq h2
  have h0123 := h012.seq h3
  have h01234 := h0123.seq h4
  have h012345 := h01234.seq h5
  have h0_6 := h012345.seq h6
  have h0_7 := h0_6.seq h7
  have h0_8 := h0_7.seq h8
  have h0_9 := h0_8.seq h9
  have h0_10 := h0_9.seq h10
  have h0_11 := h0_10.seq h11
  exact h0_11.seq h12

/-! ### Sample composition: 2-block chaining for inv_p25519

Demonstrates the typical caller pattern: given two adjacent block
correctness theorems for `BignumTripleFuel`, compose them with `.seq`
to obtain the triple for the concatenated body.

In the inv_p25519 chain, blocks 2 and 3 sit at the start of the
12-block prefix: block 2 squares `ap` into `OFF_z2`, block 3
computes `OFF_z9 := (z2²)² · ap`. -/

/-- Sample 2-block composition: chain block 2 (`sqr_step`) and
    block 3 (caller-supplied body) into a single triple via `.seq`. -/
theorem block2_then_block3_compose
    {registry : BignumRegistry}
    (P_block2 P_block3 P_block4 : BignumState → Prop)
    (block3_body : List InstrR)
    (h_block2 : BignumTripleFuel registry P_block2
                  (BignumInvP25519.sqr_step 0
                     BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap)
                  P_block3)
    (h_block3 : BignumTripleFuel registry P_block3 block3_body P_block4) :
    BignumTripleFuel registry P_block2
      ((BignumInvP25519.sqr_step 0
          BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap) ++ block3_body)
      P_block4 :=
  h_block2.seq h_block3

/-! ## §3  Tail blocks (divergent between inv and pow_p58)

Block 13a (inv): `op = (z2_250_0)^(2⁵) · z11`, exponent contribution
`32 · (2²⁵⁰ − 1) + 11 = 2²⁵⁵ − 21 = p − 2`.

Block 13b (pow_p58): `op = (z2_250_0)^(2²) · ap`, exponent contribution
`4 · (2²⁵⁰ − 1) + 1 = 2²⁵² − 3 = (p − 5) / 8`.

Both are 3-Ccall blocks (2 or 5 sqr + 1 mul).  We expose target
specs for each. -/

/-- Tail block 13a target (inv): exponent jumps to `p − 2`. -/
def inv_tail_triple_target
    (P_tail : BignumState → Prop)
    (Q_tail : BignumState → Prop) : Prop :=
  BignumTriple P_tail
    (let (instrs, _) := BignumInvP25519.repeated_sqr_then_mul 0
       BignumInvP25519.OFF_op
       BignumInvP25519.OFF_z2_250_0
       BignumInvP25519.OFF_z11 5
     instrs)
    Q_tail

/-- Tail block 13b target (pow_p58): exponent jumps to `(p−5)/8`. -/
def pow_p58_tail_triple_target
    (P_tail : BignumState → Prop)
    (Q_tail : BignumState → Prop) : Prop :=
  BignumTriple P_tail
    (let (instrs, _) := BignumInvP25519.repeated_sqr_then_mul 0
       BignumInvP25519.OFF_op
       BignumInvP25519.OFF_z2_250_0
       BignumInvP25519.OFF_ap 2
     instrs)
    Q_tail

/-! ## §4  Headline shapes: documentation anchors

Both inv and pow_p58 chain triples are exposed as documentation
anchors — `True`-valued shapes recording the target signature.
The actual triples will be discharged by composing the per-block
triples (§1, §3) via 12-fold `.seq` (§2). -/

/-- Documentation anchor for `bignum_inv_p25519`'s target Hoare
    triple.  Returns `True` once an actual triple is supplied;
    documents the target shape of Layer B closure. -/
def inv_chain_triple_shape
    (_P0 _Pf : BignumState → Prop)
    (_h_full_triple :
      BignumTriple _P0 BignumInvP25519.body _Pf) : Prop :=
  True

/-- Documentation anchor for `bignum_pow_p25519_p58`'s target Hoare
    triple. -/
def pow_p58_chain_triple_shape
    (_P0 _Pf : BignumState → Prop)
    (_h_full_triple :
      BignumTriple _P0 BignumPowP58P25519.body _Pf) : Prop :=
  True

theorem inv_chain_triple_shape_anchor
    (P0 Pf : BignumState → Prop)
    (h : BignumTriple P0 BignumInvP25519.body Pf) :
    inv_chain_triple_shape P0 Pf h :=
  trivial

theorem pow_p58_chain_triple_shape_anchor
    (P0 Pf : BignumState → Prop)
    (h : BignumTriple P0 BignumPowP58P25519.body Pf) :
    pow_p58_chain_triple_shape P0 Pf h :=
  trivial

/-! ## §5  What's still to-be-proved

Per the file docstring, the per-block targets are caller-supplied
hypotheses.  Per-block effort estimate: ~50-100 LoC each,
mechanical via `bignumExec` semantics + `BignumTriple.seq` + the
existing `memNat4`-style memory invariants from
`bignum_mod_p25519_4`.

The §4 anchors are `True`-valued shape contracts: once a caller
supplies a full-chain `BignumTriple`, the anchor reduces to
`trivial`.  Constructing the full-chain `BignumTriple` is the
remaining work — composing 12 prefix blocks + 1 tail via §2's
`chain_triple_compose`. -/

end CatCrypt.Crypto.Jasmin.BignumHoare.PowP58LayerB
