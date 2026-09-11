/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectness

/-!
# Dialect lowering as a Trocq map₁ transport — the wrapper + the two-pass pilot

Every dialect-lowering pass in `CatCrypt/Crypto/SecureCompilation/VIR/` ships a
preservation lemma of the shape

    (lower c).denote (mapVal V)  =  transTy (c.denote V)

— an **input value-transport** `mapVal` on the left, an **output value-transport**
`transTy` on the right, and the lowered program's denotation equated to the
source program's denotation across them.  That is a commuting square: denotation
is *natural* along the lowering.  It is exactly a **Trocq map₁ transport** —
`g ∘ φ_in = φ_out ∘ f` — i.e. "`f` and `g` are `Related` by `(φ_in, φ_out)`", the
same shape as `Bridges/ReprTransfer`'s `BinOpHomOn` / `Related` / `composeBinOp`.
The decode is the value transport, and lowering is a *forward* refinement, so the
weakest Trocq level (map₁, no inverse, no univalence) is exactly the right one.

This is **Phase 0** of the pervasive-use plan: the wrapper that turns one such
square into a registered transport, and the **pilot** deriving the composition of
two adjacent passes by *transitivity of transports* rather than a hand `rw`-chain.

## What is built here

* `TransportSquare g φin φout f` — the map₁ transport square `f ∘ φin = φout ∘ g`
  carried as its single field.  This is the engine-agnostic restatement of every
  `lower_denote_preserved`: `g = c.denote`, `f = (lower c).denote`,
  `φin = mapVal`, `φout = transTy`.  `.related` exposes the carried square as the
  transport predicate.
* `TransportSquare.comp` — **the composition lemma** (the `Related.trans` /
  `composeBinOp` analogue): two transports sharing the middle carrier,
  `S12 : g↦h along (φin₁, φout₁)` and `S23 : h↦k along (φin₂, φout₂)`, paste to a
  single transport `g↦k along (φin₁ ∘ … , φout₂ ∘ φout₁)`.  Proved by transitivity:
  rewrite by the second square then the first.  This is the key lemma — the whole
  plan's payoff (the ~5-pass × N-protocol chain collapses to "register each square
  once, compose by `comp`") rests on it.

## The pilot — two adjacent passes of the ML-KEM NTT-mul route

The two adjacent passes are exactly the ones the hand `rw`-chain in
`CompilerCorrectness.latticeNttMul_compile_correct` composes:

* **Pass 1 (optimizer rewrite, lattice→lattice, carrier-preserving).**
  `LatticeDialect.nttMul_rewrite_denote_eq` rewrites the source `poly_mul` into the
  NTT-domain sequence `invntt (basemul (ntt a) (ntt b))`, preserving `Com.denote`.
  As a transport this is the *carrier-preserving* (degenerate) square: input and
  output transports are the identity — the optimizer stays within `latticeDialect`.
* **Pass 2 (dialect lowering, lattice→jasmin, carrier-changing).**
  `LatticeToJasminDenoteUncond.tgtCom_denote_preserved_uncond` lowers across the
  lattice→jasmin dialect conversion, transporting valuations by `mapVal` and
  values by `transTy`.

`pilot_latticeNttMul_transport` wraps each as a `TransportSquare`, then
`pilot_latticeNttMul_compose` derives their two-pass composition **by**
`TransportSquare.comp` — `exact (… .comp …).related V` — *not* by a hand
`rw`-chain.  `pilot_matches_handChain` records that the transport-derived statement
is *definitionally* the existing hand-chained `latticeNttMul_compile_correct`, so
the registry resolution genuinely replaces the manual `rw`.

## Scope

The wrapper *composes* transports; it does not *invent* leaf semantics — the
arithmetic leaves (the NTT round-trip agreement, the jasmin `extCall` semantics)
are discharged upstream (`nttMul_rewrite_denote_eq`, `latticeLeafAgrees`) and the
inherited kernel TCB is unchanged.  The pilot is a faithful re-derivation of an
*already-proved* composition by transitivity, de-risking the Phase 1–5 rollout.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport

universe u v w

/-! ## 1. The transport square (Trocq map₁) -/

/-- A **map₁ transport square**: along an input transport `φin : X → X'` and an
    output transport `φout : Y → Y'`, the realised function `f : X' → Y'` agrees
    with the abstract function `g : X → Y`, i.e. the square

        X  --g-->  Y
        |          |
      φin        φout
        |          |
        v          v
        X' --f-->  Y'

    commutes: `f (φin x) = φout (g x)` for every `x`.  This is the engine-agnostic
    restatement of a dialect-lowering preservation lemma
    `(lower c).denote (mapVal V) = transTy (c.denote V)`: take `g := c.denote`,
    `f := (lower c).denote`, `φin := mapVal`, `φout := transTy`, `X := Valuation Γ`.
    It is the weakest Trocq level (map₁: one direction, no inverse, no univalence),
    which is exactly what a *forward* compiler refinement needs. -/
structure TransportSquare {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type w}
    (g : X → Y) (φin : X → X') (φout : Y → Y') (f : X' → Y') : Prop where
  /-- The commuting square (the `lower_denote_preserved` content). -/
  square : ∀ x, f (φin x) = φout (g x)

namespace TransportSquare

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type w}
  {g : X → Y} {φin : X → X'} {φout : Y → Y'} {f : X' → Y'}

/-- The transport, as the carried `Related`/map₁ predicate: the square the engine
    consumes.  Exposes a `TransportSquare` as "`f` and `g` are related by
    `(φin, φout)`". -/
theorem related (S : TransportSquare g φin φout f) (x : X) :
    f (φin x) = φout (g x) := S.square x

/-! ## 2. Composition (the `Related.trans` analogue) -/

/-- **Composition of transports (the `Related.trans` analogue).**  Two *adjacent*
    compiler passes paste into one transport.  Pass 1 transports the abstract
    function `g` (the source program's denotation) to a realised `f₁` across
    `(φin₁, φout₁)`; pass 2 transports an abstract function `g₂` to a realised
    `f₂` across `(φin₂, φout₂)`.  The passes share the realised carrier `X'` of
    pass 1 (pass 2 reads pass 1's realised values) and are **adjacent** when pass
    2's abstract source *is* pass 1's realised target — pass 2 lowers exactly what
    pass 1 produced (`adj : f₁ = g₂`).  Then the pasted square holds:

        f₂ (φin₂ (φin₁ x))  =  φout₂ (φout₁ (g x)).

    The whole-chain correctness (`L2→L3→L4→jasmin`) is the iterated `comp` of the
    per-pass squares — *derived*, no per-pass `rw` re-proof.  Proof: peel pass 2's
    square at the point `φin₁ x`, rewrite its abstract source across `adj` to pass
    1's realised target, then apply pass 1's square. -/
theorem comp {X : Type u} {Y : Type v} {X' Z W : Type w} {Y' : Type w}
    {g : X → Y} {φin₁ : X → X'} {φout₁ : Y → Y'} {f₁ : X' → Y'}
    {g₂ : X' → Y'} {φin₂ : X' → Z} {φout₂ : Y' → W} {f₂ : Z → W}
    (S12 : TransportSquare g φin₁ φout₁ f₁)
    (S23 : TransportSquare g₂ φin₂ φout₂ f₂)
    (adj : f₁ = g₂) (x : X) :
    f₂ (φin₂ (φin₁ x)) = φout₂ (φout₁ (g x)) := by
  -- pass 2's square at the point `φin₁ x` …
  rw [S23.square]
  -- … whose abstract source `g₂ (φin₁ x)` is pass 1's realised target
  -- `f₁ (φin₁ x) = φout₁ (g x)`.
  rw [← adj, S12.square]

end TransportSquare

/-! ## 3. The pilot — the ML-KEM NTT-mul route, two adjacent passes

We instantiate the wrapper at the two real adjacent passes of the lattice route
and derive their two-pass composition by `TransportSquare.comp`, reproducing the
hand-chained `CompilerCorrectness.latticeNttMul_compile_correct` *by transitivity*.
-/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond

variable (q n : Nat)

/-! ### Pass 1 — the optimizer rewrite as a carrier-preserving transport

`nttMul_rewrite_denote_eq` says `(srcCom q n).denote V = (tgtCom q n).denote V` for
every valuation `V`.  As a transport square it is *degenerate* (the optimizer
stays inside `latticeDialect`): input and output transports are the identity, and
the realised function is `(tgtCom q n).denote`, the abstract function is
`(srcCom q n).denote`.  The carried square `(tgtCom).denote (id V) = id ((srcCom).denote V)`
is exactly the rewrite soundness. -/

/-- **Pass 1 as a transport.** The NTT-domain optimizer rewrite, as a
    carrier-preserving (`φin = φout = id`) map₁ transport from the source
    `poly_mul` denotation to the expanded `tgtCom` denotation. -/
theorem pass1_optimizer_transport :
    TransportSquare
      (g := fun V : Ctxt.Valuation (LatticeDialect.inCtxt q n) =>
              (LatticeDialect.srcCom q n).denote V)
      (φin := id) (φout := id)
      (f := fun V => (LatticeDialect.tgtCom q n).denote V) :=
  ⟨fun V => (LatticeDialect.nttMul_rewrite_denote_eq q n V).symm⟩

/-! ### Pass 2 — the lattice→jasmin lowering as a carrier-changing transport

`tgtCom_denote_preserved_uncond` says
`(lowerLatticeToJasmin (tgtCom q n)).denote (mapVal V) = transTy ((tgtCom q n).denote V)`.
As a transport square the abstract function is `(tgtCom q n).denote`, the realised
function is `(lowerLatticeToJasmin (tgtCom q n)).denote`, the input transport is
`mapVal`, the output transport is `transTy`. -/

/-- **Pass 2 as a transport.** The lattice→jasmin dialect lowering of the expanded
    target program, as a carrier-changing map₁ transport (`φin = mapVal`,
    `φout = transTy`). -/
theorem pass2_lowering_transport :
    TransportSquare
      (g := fun V : Ctxt.Valuation (LatticeDialect.inCtxt q n) =>
              (LatticeDialect.tgtCom q n).denote V)
      (φin := mapVal) (φout := transTy)
      (f := fun V' => (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)).denote V') :=
  ⟨fun V => tgtCom_denote_preserved_uncond q n V⟩

/-! ### The composition — derived by transitivity, not a hand `rw`-chain

The two passes are adjacent: pass 2's abstract source `(tgtCom).denote` *is* pass
1's realised target `(tgtCom).denote` (`adj` is `rfl`).  Pass 1 is
carrier-preserving (`φin₁ = φout₁ = id`), so the pasted square specialises to
exactly the route's end-to-end statement.  We obtain it by a **single application
of `TransportSquare.comp`** — the transport `Related.trans` — with **no** `rw
[tgtCom_denote_preserved_uncond, nttMul_rewrite_denote_eq]` hand chain. -/

/-- **Pilot: two-pass composition, derived by transport transitivity.** For the
    ML-KEM NTT-mul route, the *optimized and lowered* jasmin program denotes to the
    `transTy`-transport of the *source* `poly_mul` denotation — obtained by pasting
    the two per-pass transport squares (`pass1_optimizer_transport`,
    `pass2_lowering_transport`) with `TransportSquare.comp`, **not** by the hand
    `rw`-chain of `CompilerCorrectness.latticeNttMul_compile_correct`.

    The composition is the transport `Related.trans`: pass 1 (carrier-preserving)
    rewrites the source denotation to `tgtCom`'s, then pass 2 (carrier-changing)
    transports that across the dialect lowering — `comp`'s `adj` is exactly their
    adjacency, here `rfl`. -/
theorem pilot_latticeNttMul_compose
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)).denote (mapVal V)
      = transTy ((LatticeDialect.srcCom q n).denote V) :=
  -- the single transitivity step: paste pass 1 into pass 2; `adj` (their
  -- adjacency `tgtCom.denote = tgtCom.denote`) is `rfl`.
  TransportSquare.comp (pass1_optimizer_transport q n)
    (pass2_lowering_transport q n) rfl V

/-- **The transport-derived statement is the hand-chained one.**  The pilot
    composition `pilot_latticeNttMul_compose` is *definitionally* the existing
    `CompilerCorrectness.latticeNttMul_compile_correct` — same statement, same
    type — so the registry resolution genuinely *replaces* the manual `rw`-chain
    (it is not a weaker or differently-shaped corollary). -/
theorem pilot_matches_handChain
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    pilot_latticeNttMul_compose q n V
      = CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectness.latticeNttMul_compile_correct
          q n V :=
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport
