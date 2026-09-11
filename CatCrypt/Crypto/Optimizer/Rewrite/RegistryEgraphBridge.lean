/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Transfer.Base.Related
public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph
public import CatCrypt.Crypto.Optimizer.Rewrite.KaratsubaGenericPass
public import CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction

/-!
# Registry ↔ e-graph bridge: one "denotation-preserving equation" representation

The equality-saturation optimizer (`Optimizer/Rewrite/Egraph`) and the
Trocq-style `Related` registry (`Bridges/Transfer/Related`) are built around the
**same certificate shape**: a *denotation-preserving equation*.

* An e-graph rewrite rule is sound exactly when the rewritten term denotes the
  same value as the original — `e'.denote V = e.denote V` (see
  `Egraph.rewriteBin_sound`, `Egraph.saturateCom_denote`). The soundness is the
  equation; the search/extraction is separate.
* A `Related` registry entry is the equation `enc a = b`; a `RelatedBinOp`
  entry is the commuting square `enc (op x y) = bop (enc x) (enc y)`. Under the
  identity encoding `enc = id` these are *plain value equations* `a = b`.

This file makes the shared shape explicit with a small adapter that converts in
both directions between "a plain denotation/value equality `lhs = rhs`" and "a
`Related id lhs rhs` registry entry", and demonstrates one algorithmic-refinement
rule — Karatsuba = schoolbook — flowing through the bridge: the existing
`ring`-proved equation `karatsubaMul_eq_schoolbook` becomes a `Related` transport
entry whose soundness certificate *is* that same `ring` proof.

## Scope

This bridges the **rule/certificate shape** — the denotation-preserving
equation — shared by the two frameworks. It does **not** bridge the *search*.
The e-graph's extraction / cost-minimisation phase (`Egraph.comCost`,
`Egraph.saturate_cost_le`) is an unverified search; the only thing proved is the
rewrite-chain certificate (`Egraph.saturateCom_denote`). This adapter shares
that certificate structure with the `Related` registry; it does **not** make the
e-graph's extraction verified, and is **not** a "fully proof-producing
equality-saturation engine" (that is separate work). The deliverable is narrow
and concrete: algorithmic-refinement equations (Karatsuba, and by the same
recipe Toom-3) and the `Related` registry share *one* "denotation-preserving
equation" representation, demonstrated by a working adapter on one refinement.

### Honest impedance

The two representations genuinely differ where there is nothing to bridge:

* **Cost model.** The e-graph carries a cost model (`opCost`/`comCost`) and a
  monotonicity certificate (`saturate_cost_le`). `Related` has *no* cost analogue
  — it is a pure correctness relation. The adapter transports the *equation*, not
  the cost; a registry entry says nothing about which side is cheaper.
* **Concrete vs. abstract.** e-graph rules are concrete `Expr`/`Com` rewrites
  with a known-constant environment (`KEnv`) and a consistency side-condition
  (`KEnv.Consistent`). `Related`/`RelatedBinOp` are abstract typeclass commuting
  squares with no environment. The adapter works at the point where both reduce
  to a closed value equality (a fixed valuation `V`, or a closed `ring` identity);
  it does not transport the `KEnv` consistency machinery.
* **Operand shape.** A clean `RelatedBinOp enc op bop` is a *binary* op on one
  carrier. Karatsuba's operands are a 4-tuple `(a1, a0, b1, b0)` of limbs (plus a
  base `B`), not a binary op on a single carrier, so it does **not** fit
  `RelatedBinOp`. The cleanest true form is therefore a `Related id` equation
  between the two triple-valued evaluators (`karatsubaMul B …` and
  `schoolbookMul B …`), documented below.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.RegistryEgraphBridge

open Transfer
open CatCrypt.Crypto.Optimizer.Rewrite
open CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The adapter: the shared "denotation-preserving equation" shape

Both frameworks' soundness certificate is a plain equality `lhs = rhs`. Under
the identity encoding, `Related id lhs rhs` unfolds (`id lhs = rhs`) to exactly
that equality. The two directions below are the adapter. They are deliberately
trivial *as proofs* — that triviality is the point: the registry's `Related`
entry and an e-graph rule's soundness lemma are the **same object**, so passing
between them needs no new content, only the identity encoding to line up the
shapes. -/

/-- **Adapter, equation → registry.** Any denotation/value equality `lhs = rhs`
is a `Related id lhs rhs` registry entry. This is the direction that registers an
e-graph rule's soundness lemma (`e'.denote V = e.denote V`, a Karatsuba/Toom
`ring` equation, …) as a Trocq transport entry. The supplied equation *is* the
soundness certificate. -/
@[reducible] def relatedOfEq {α : Type*} {lhs rhs : α} (h : lhs = rhs) :
    Related (id : α → α) lhs rhs where
  rel := h

/-- **Adapter, registry → equation.** Conversely, a `Related id lhs rhs` entry
yields the plain value equality `lhs = rhs` — the shape an e-graph rewrite rule's
soundness lemma takes. (`transferRel` specialised to `enc = id`.) -/
theorem eqOfRelated {α : Type*} {lhs rhs : α}
    (h : Related (id : α → α) lhs rhs) : lhs = rhs := h.rel

/-- The round-trip is the identity on the equation: registering an equality and
reading it back returns the same proof. Confirms the adapter loses nothing. -/
theorem eqOfRelated_relatedOfEq {α : Type*} {lhs rhs : α} (h : lhs = rhs) :
    eqOfRelated (relatedOfEq h) = h := rfl

/-- A `RewriteEq` packages the certificate shared by both frameworks: a
denotation-preserving equality together with its `Related`-registry view. It is
the explicit witness that "an e-graph rewrite rule" and "a `Related` entry" are
two readings of one object. -/
structure RewriteEq (α : Type*) where
  /-- Left-hand side (e.g. the rewritten / refined term). -/
  lhs : α
  /-- Right-hand side (e.g. the original / schoolbook term). -/
  rhs : α
  /-- The denotation-preserving equation: the soundness certificate. -/
  sound : lhs = rhs

/-- Read a `RewriteEq` as a `Related` registry entry (identity encoding). -/
@[reducible] def RewriteEq.toRelated {α : Type*} (r : RewriteEq α) :
    Related (id : α → α) r.lhs r.rhs :=
  relatedOfEq r.sound

/-- Build a `RewriteEq` from a `Related` registry entry. -/
def RewriteEq.ofRelated {α : Type*} {lhs rhs : α}
    (h : Related (id : α → α) lhs rhs) : RewriteEq α :=
  ⟨lhs, rhs, eqOfRelated h⟩

/-! ## 2. Demonstration A — an e-graph algebraic rule re-expressed as `Related`

The bridge is bidirectional. Each of the e-graph's five algebraic soundness
lemmas is a `BitVec` value equality, so by `relatedOfEq` each *is* a `Related id`
registry entry. We show `mul_one_eq` (`x * 1 = x`) and `mul_zero_eq`
(`x * 0 = 0`); the rest (`add_zero_eq`, `xor_zero_eq`, `or_zero_eq`,
`and_zero_eq`) register identically. The soundness certificate is the existing
`Egraph.*` lemma — no new proof. -/

/-- e-graph `mul-by-one` rule (`Egraph.mul_one_eq`) as a `Related` registry
entry. The certificate is the e-graph's own soundness lemma. -/
@[reducible] def mulOneRelated {w : Nat} (x : BitVec w) :
    Related (id : BitVec w → BitVec w) (x * BitVec.ofNat w 1) x :=
  relatedOfEq (Egraph.mul_one_eq x)

/-- e-graph `mul-by-zero` annihilator (`Egraph.mul_zero_eq`) as a `Related`
registry entry. -/
@[reducible] def mulZeroRelated {w : Nat} (x : BitVec w) :
    Related (id : BitVec w → BitVec w)
      (x * BitVec.ofNat w 0) (BitVec.ofNat w 0) :=
  relatedOfEq (Egraph.mul_zero_eq x)

/-- Reading the registered `mul-by-one` entry back recovers exactly the e-graph
soundness equation — the bridge is lossless in this direction too. -/
theorem mulOneRelated_eq {w : Nat} (x : BitVec w) :
    eqOfRelated (mulOneRelated x) = Egraph.mul_one_eq x := rfl

/-! ## 3. Demonstration B — the Karatsuba refinement through the bridge

`Egraph` notes (its §3 docstring) that "any e-graph / peephole rewrite that
replaces a four-multiply schoolbook expansion with the three-multiply form"
instantiates the generic identity proved in `KaratsubaGenericPass`. We take that
genuine `ring`-proved equation and route it through the adapter, exhibiting the
schoolbook ↔ Karatsuba refinement as a `Related` transport entry.

### Operand-shape impedance (honest note)

A clean `RelatedBinOp enc op bop` is a binary operation on a single carrier.
Karatsuba does **not** have that shape: its inputs are the four limbs
`(a1, a0, b1, b0)` together with a base `B`, and its output is a *triple*
`R × R × R`, not a single carrier element. So we cannot honestly write
`RelatedBinOp (· * ·) karatsuba`. The cleanest true form is a `Related id`
equation between the two evaluators at fixed limbs — the schoolbook evaluator and
the Karatsuba evaluator — which is exactly what the e-graph rule needs (a
denotation equality between the two candidate terms). The carrier `α` is the
result type `R × R × R`. -/

variable {R : Type*} [CommRing R]

/-- **Karatsuba = schoolbook as a `Related` registry entry.** At fixed base `B`
and limbs `(a1, a0, b1, b0)`, the Karatsuba coefficient triple is `Related` (via
the identity encoding on `R × R × R`) to the schoolbook triple. The soundness
certificate is the existing `ring`-proved `karatsubaMul_eq_schoolbook` — passed
verbatim through `relatedOfEq`. This is the schoolbook ↔ Karatsuba refinement
exhibited as a transport rule. -/
@[reducible] def karatsubaRelated (B a1 a0 b1 b0 : R) :
    Related (id : (R × R × R) → (R × R × R))
      (KaratsubaGeneric.karatsubaMul B a1 a0 b1 b0)
      (KaratsubaGeneric.schoolbookMul B a1 a0 b1 b0) :=
  relatedOfEq (KaratsubaGeneric.karatsubaMul_eq_schoolbook B a1 a0 b1 b0)

/-- The same refinement packaged as a `RewriteEq` — the explicit "this is one
object" witness, lhs = Karatsuba (the refined / cheaper-multiply term), rhs =
schoolbook (the original). -/
def karatsubaRewriteEq (B a1 a0 b1 b0 : R) : RewriteEq (R × R × R) :=
  ⟨KaratsubaGeneric.karatsubaMul B a1 a0 b1 b0,
   KaratsubaGeneric.schoolbookMul B a1 a0 b1 b0,
   KaratsubaGeneric.karatsubaMul_eq_schoolbook B a1 a0 b1 b0⟩

/-- Reading the Karatsuba registry entry back recovers exactly the original
`ring` equation: the bridge transports the certificate unchanged. -/
theorem karatsubaRelated_eq (B a1 a0 b1 b0 : R) :
    eqOfRelated (karatsubaRelated B a1 a0 b1 b0)
      = KaratsubaGeneric.karatsubaMul_eq_schoolbook B a1 a0 b1 b0 := rfl

/-- The `RewriteEq` view and the `Related` view agree: both expose the same
soundness equation. -/
theorem karatsubaRewriteEq_toRelated_eq (B a1 a0 b1 b0 : R) :
    eqOfRelated ((karatsubaRewriteEq B a1 a0 b1 b0).toRelated)
      = KaratsubaGeneric.karatsubaMul_eq_schoolbook B a1 a0 b1 b0 := rfl

/-! ### Evaluated form: refinement at the *value* level

The triple-level entry above also yields the more familiar "both denote the same
ring product" reading, by composing with `KaratsubaGeneric.evalLimbs`. This is
the form an e-graph would use after the assembled term is evaluated, and it is
the direct analogue of `e'.denote V = e.denote V`: the Karatsuba assembly and the
schoolbook assembly denote one and the same ring element
`(a1*B+a0)*(b1*B+b0)`. -/

/-- The evaluated Karatsuba assembly is `Related` (identity encoding on `R`) to
the evaluated schoolbook assembly: both equal the genuine product. Certificate:
`evalLimbs_karatsuba_eq_schoolbook`. This is the value-level denotation equality
that an e-graph cost-extraction would compare candidates against. -/
@[reducible] def karatsubaEvalRelated (B a1 a0 b1 b0 : R) :
    Related (id : R → R)
      (KaratsubaGeneric.evalLimbs B (KaratsubaGeneric.karatsubaMul B a1 a0 b1 b0))
      (KaratsubaGeneric.evalLimbs B (KaratsubaGeneric.schoolbookMul B a1 a0 b1 b0)) :=
  relatedOfEq (KaratsubaGeneric.evalLimbs_karatsuba_eq_schoolbook B a1 a0 b1 b0)

/-- Both evaluators denote the genuine ring product, recovered through the
bridge: `eqOfRelated` on the entry, then the schoolbook evaluation lemma. -/
theorem karatsubaEval_denotes_product (B a1 a0 b1 b0 : R) :
    KaratsubaGeneric.evalLimbs B (KaratsubaGeneric.karatsubaMul B a1 a0 b1 b0)
      = (a1 * B + a0) * (b1 * B + b0) :=
  (eqOfRelated (karatsubaEvalRelated B a1 a0 b1 b0)).trans
    (KaratsubaGeneric.evalLimbs_schoolbookMul B a1 a0 b1 b0)

/-! ## 4. The shared-certificate statement, made precise

The point of the whole file: an e-graph rewrite rule's soundness lemma and a
`Related` registry entry are interconvertible *with no loss*, because both are
the one denotation-preserving equation. The following two lemmas state exactly
that interconvertibility abstractly. -/

/-- **An e-graph soundness lemma yields a registry entry.** Given any e-graph
rewrite soundness fact in the canonical shape `lhs = rhs` (e.g. `rewriteBin`'s
`e'.denote V = (binE …).denote V`, instantiated at a value), the registry entry
`Related id lhs rhs` is immediate. -/
@[reducible] def registryOfRewriteSound {α : Type*} {lhs rhs : α} (sound : lhs = rhs) :
    Related (id : α → α) lhs rhs := relatedOfEq sound

/-- **A registry entry yields an e-graph-shaped soundness equation.** Converse of
`registryOfRewriteSound`: the registry entry's equation is exactly the shape an
e-graph rewrite rule's `*_sound` lemma asserts. -/
theorem rewriteSoundOfRegistry {α : Type*} {lhs rhs : α}
    (h : Related (id : α → α) lhs rhs) : lhs = rhs := eqOfRelated h

/-! ### Concrete instantiation on the e-graph's own `rewriteBin_sound`

To show the abstract statement is genuinely the e-graph's certificate (not a
look-alike), we feed `Egraph.rewriteBin_sound` — the real `BitVec`-algebra
soundness lemma that the saturation engine composes — straight into
`registryOfRewriteSound`, producing a `Related` registry entry for an actual
e-graph rewrite step. -/

/-- An actual `rewriteBin` step, registered as a `Related` entry. The hypotheses
are exactly `rewriteBin_sound`'s (a consistent known-constant env and a firing
rule); the conclusion registers the produced expression's denotation as
`Related` to the original. No new proof — the certificate is `rewriteBin_sound`
itself. -/
@[reducible] def rewriteBinRegistered {Γ : Ctxt jasminDialect}
    {w : Nat} (bop : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg w))
    (k : Egraph.KEnv Γ) (V : Ctxt.Valuation Γ) (hk : Egraph.KEnv.Consistent k V)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : Egraph.rewriteBin bop a b (Egraph.KEnv.lookup b k) = some e') :
    Related (id : BitVec w → BitVec w)
      (e'.denote V) ((Egraph.binE bop a b).denote V) :=
  registryOfRewriteSound (Egraph.rewriteBin_sound bop a b k V hk e' he)

/-! ## 5. Proof-carrying extraction witnesses → registry entries

`ProofCarryingExtraction.lean` factors the "extraction is trusted only up to a
kernel-checked denotation equality" contract into a reusable witness + validator
+ identity-fallback scheme. A *validated* witness is exactly a proved equation
`f start = f finish`, so by the same `relatedOfEq` adapter it is a `Related`
registry entry — closing the loop: an equality-saturation extractor's ordered
rewrite-step explanation becomes a Trocq transport entry with no new proof
content, the certificate being the witness's transitivity fold. -/

/-- **A validated rewrite witness as a registry entry.** Given any
`RewriteWitness f start finish` (an ordered explanation), its `validate`
transitivity fold yields `f start = f finish`, which `relatedOfEq` registers as
`Related id (f start) (f finish)`. The certificate is the fold of the witness's
per-step equations — no search, no new proof content. -/
@[reducible] def registryOfWitness {α : Type*} {β : Type*} {f : α → β}
    {start finish : α} (w : RewriteWitness f start finish) :
    Related (id : β → β) (f start) (f finish) :=
  relatedOfEq w.validate

/-- **The identity-fallback optimizer's output as a registry entry.** The total
`optimizeChecked` pass denotes the input on every branch
(`optimizeChecked_denote`); that unconditional equality registers as a `Related`
entry. So even the fallback (original-term) branch produces a valid registry
certificate — the registry never receives a wrong equation. -/
@[reducible] def registryOfOptimizeChecked {α : Type*} {β : Type*} [DecidableEq α]
    {f : α → β} {start finish : α} (w : RewriteWitness f start finish)
    (input cand : α) :
    Related (id : β → β) (f (optimizeChecked w input cand)) (f input) :=
  relatedOfEq (optimizeChecked_denote w input cand)

/-- Reading the witness-registry entry back recovers exactly the witness's
validated equation — the bridge is lossless for the chain certificate too. -/
theorem registryOfWitness_eq {α : Type*} {β : Type*} {f : α → β}
    {start finish : α} (w : RewriteWitness f start finish) :
    eqOfRelated (registryOfWitness w) = w.validate := rfl

/-- **Concrete instantiation on the `Com` engine.** The bounded saturation
engine's own output, packaged as a witness (`saturateWitness`) and registered as
a `Related` entry: the saturated `Com`'s denotation function is `Related` to the
input's. The certificate is `saturateCom_denote`, threaded through the witness
validator — exhibiting the production engine's output as a registry-ready,
proof-carrying extraction. -/
@[reducible] noncomputable def comSaturateRegistered {Γ : Ctxt jasminDialect}
    {t : JasminTy} (fuel : Nat) (c : Com jasminDialect Γ t) (k : Egraph.KEnv Γ)
    (hk : ∀ V, Egraph.KEnv.Consistent k V) :
    Related (id : (Ctxt.Valuation Γ → ⟦t⟧) → (Ctxt.Valuation Γ → ⟦t⟧))
      (Egraph.saturateCom fuel c k).denote c.denote :=
  relatedOfEq (saturateWitness_validate fuel c k hk)

end CatCrypt.Crypto.Optimizer.Rewrite.RegistryEgraphBridge
