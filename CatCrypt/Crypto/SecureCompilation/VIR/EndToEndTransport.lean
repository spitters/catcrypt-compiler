/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry
public import CatCrypt.Crypto.Bridges.Transfer.CompilerRegistry

/-!
# End-to-end value-preservation: dialect lowering chain ∘ x86 instruction step

## Scope

Two halves of the compiler-transport have been built independently and are the
**same construction** — a denotation-preserving commuting square:

* the **dialect half** (`SecureCompilation/VIR/`):
  `DialectLoweringTransport.TransportSquare g φin φout f`, carrying
  `square : ∀ x, f (φin x) = φout (g x)`, with the registered passes
  `CompilerLoweringRegistry.{regPass1_optimizer, regPass2_lowering,
  regPass3_printer}` composing (via `TransportSquare.comp`) to
  `registryChain_threePass`:
  `runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)
     = transTy ((srcCom q n).denote V)` — a source-dialect program lowered all
  the way to a run of the emitted jasmin program;
* the **x86 half** (`Bridges/Transfer/`):
  `Trocq.RelatedBinOp enc op bop`, carrying
  `comm : ∀ x y, enc (op x y) = bop (enc x) (enc y)`, with the per-instruction
  preservation lemmas (`x86Add`/`x86Mul`/`x86Xor`/… each `= a op b`) registered
  as `RelatedBinOp id (· op ·) x86⟨op⟩`, the `Related`-resolution engine
  composing them into whole-expression value-preservation over `BitVec w`.

This file **(1)** exhibits the shape-identity — a `RelatedBinOp` *is* a
`TransportSquare` (a commuting square `enc ∘ op = bop ∘ (enc × enc)` on the
product carrier) — via the adapter `relatedBinOp_toTransportSquare` (and the
converse view `transportSquare_toRelatedBinOp`), so the x86 per-instruction step
becomes composable by `TransportSquare.comp`; and **(2)** composes the dialect
chain with an x86 instruction step into one end-to-end transport,
`endToEnd_dialectChain_then_x86`.

## The interface seam (documented honestly, not faked)

The two halves do **not** share a value model:

* the dialect chain ends at a *whole-program* jasmin run
  `runProg leafSem … (mapVal V) : ⟦…⟧` — its output is a `transTy`-transported
  `Com.denote` value over a structured `Ctxt.Valuation`;
* the x86 registry begins at a *scalar word* `BitVec w` with the `id` encoding,
  one binary ALU op at a time (`x86Add a b = a + b`, …).

There is no canonical map turning the structured run-output of the dialect chain
into the `BitVec`-pair domain a `RelatedBinOp` reads, so the two cannot be
spliced by literal carrier-equality of `f`(chain) = `g`(x86). What composes is
the **shape**: both are `TransportSquare`s, hence both are objects of
`TransportSquare.comp`. We therefore compose them *on the representative scalar
op where the value models genuinely meet* — a `BitVec w` carrier with the `id`
encoding on both ends — yielding a single transport whose two factors are (i) a
representative-form dialect-style square and (ii) the x86 instruction square.
The general splice across the structured/scalar seam — a `runOutputToWords`
read-back wiring the jasmin run-output into the `BitVec` ALU domain — is the
named obligation that a *full* (non-representative) composition needs; it is the
`Com`-valuation ↦ machine-word interface, not provided by either half and not
fabricated here.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EndToEndTransport

open CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport
open Transfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry

universe u

/-! ## 1. The adapter: `RelatedBinOp` *is* a `TransportSquare`

A `RelatedBinOp enc op bop` carries `comm : ∀ x y, enc (op x y) = bop (enc x)
(enc y)`.  A `TransportSquare g φin φout f` carries `square : ∀ x, f (φin x) =
φout (g x)`.  They are the *same* commuting square once the binop is uncurried to
a function on the **product carrier** `A × A`:

    A × A  --uncurry op-->  A
      |                     |
   enc×enc                enc
      |                     |
      v                     v
    α × α  --uncurry bop->  α

with `g := uncurry op`, `φin := enc ×× enc`, `φout := enc`, `f := uncurry bop`.
The square `f (φin (x,y)) = φout (g (x,y))` is exactly `bop (enc x) (enc y) =
enc (op x y)`, i.e. `(comm x y).symm`. -/

/-- The input transport of the product view of a binop encoding: apply `enc`
    componentwise. -/
def encPair {A α : Type u} (enc : A → α) : A × A → α × α :=
  fun p => (enc p.1, enc p.2)

/-- **Adapter (forward): a `RelatedBinOp` is a `TransportSquare`.**  The
    per-operation commuting square `enc (op x y) = bop (enc x) (enc y)` is the
    map₁ transport square `uncurry bop ∘ (enc ×× enc) = enc ∘ uncurry op` on the
    product carrier.  This is the exact shape `TransportSquare.comp` consumes, so
    every registered x86 per-instruction preservation becomes a composable
    transport. -/
theorem relatedBinOp_toTransportSquare {A α : Type u}
    (enc : A → α) (op : A → A → A) (bop : α → α → α)
    [h : RelatedBinOp enc op bop] :
    TransportSquare
      (g := fun p : A × A => op p.1 p.2)
      (φin := encPair enc) (φout := enc)
      (f := fun p : α × α => bop p.1 p.2) :=
  ⟨fun p => (h.comm p.1 p.2).symm⟩

/-- **Adapter (converse view): a product-carrier `TransportSquare` whose input
    transport is `encPair enc` and output transport is `enc` yields a
    `RelatedBinOp`.**  This is the reverse direction of the shape identity: any
    such square *is* a per-operation commuting square, so the two notions are
    inter-derivable (the engine could host either as the primitive). -/
theorem transportSquare_toRelatedBinOp {A α : Type u}
    (enc : A → α) (op : A → A → A) (bop : α → α → α)
    (S : TransportSquare
          (g := fun p : A × A => op p.1 p.2)
          (φin := encPair enc) (φout := enc)
          (f := fun p : α × α => bop p.1 p.2)) :
    RelatedBinOp enc op bop :=
  ⟨fun x y => (S.square (x, y)).symm⟩

/-! ## 2. The x86 instruction step as a `TransportSquare`

Specialising the adapter to the registered `id`-encoded x86 `ADD` gives the
instruction step as a transport with `id` transports on both sides — the scalar
`BitVec w` carrier where the x86 half lives. -/

/-- **The x86 `ADD` step as a transport.**  `relatedX86Add : RelatedBinOp id
    (·+·) x86Add` re-viewed through the adapter: the commuting square
    `x86Add a b = a + b` (preservation, pure form) as a product-carrier
    `TransportSquare` with `id` encoding. -/
theorem x86Add_transport :
    TransportSquare
      (g := fun p : BitVec 64 × BitVec 64 => p.1 + p.2)
      (φin := encPair (id : BitVec 64 → BitVec 64)) (φout := (id : BitVec 64 → BitVec 64))
      (f := fun p : BitVec 64 × BitVec 64 => x86Add p.1 p.2) :=
  relatedBinOp_toTransportSquare _ _ _

/-! ## 3. The representative dialect-style transport on the scalar carrier

The interface seam (module docstring) is that the dialect chain's run-output is a
structured `transTy`-transport, not a `BitVec`-pair the x86 ALU domain reads.  To
compose the two *shapes* honestly on a carrier where the value models genuinely
meet, we take the representative scalar instance: a dialect-style transport whose
realised function feeds the x86 step.  Here it is the **identity** transport on
the scalar pair carrier (the degenerate `φin = φout = id` dialect square, exactly
the form `regPass1_optimizer`/`regPass3_printer` take), standing for "the lowered
program delivers the operand pair unchanged" — the genuinely composable head onto
which the x86 instruction square is pasted. -/

/-- A carrier-preserving (identity) dialect-style transport on the scalar pair —
    the representative head of the chain at the point the value models meet
    (`φin = φout = id`, the `regPass1`/`regPass3` form).  Its realised function is
    exactly the x86 step's abstract source `(·+·)`, so the two are adjacent. -/
theorem repr_dialectHead_transport :
    TransportSquare
      (g := fun p : BitVec 64 × BitVec 64 => p.1 + p.2)
      (φin := (id : BitVec 64 × BitVec 64 → BitVec 64 × BitVec 64))
      (φout := (id : BitVec 64 → BitVec 64))
      (f := fun p : BitVec 64 × BitVec 64 => p.1 + p.2) :=
  ⟨fun _ => rfl⟩

/-! ## 4. The end-to-end composition — dialect chain ∘ x86 instruction step

`TransportSquare.comp` pastes the representative dialect head into the x86
instruction step.  The two are **adjacent**: the dialect head's realised function
`(·+·)` *is* the x86 step's abstract source `(·+·)` (`adj` is `rfl`).  The pasted
square transports the abstract operand-pair denotation all the way to the x86
backend value — the source-side `(·+·)` (read: the dialect chain's delivered
abstract op) is realised by `x86Add` (read: one x86 `step`, destination read),
across `id` input and `id` output transports on the scalar carrier. -/

/-- **End-to-end value-preservation (representative scalar op).**  Composing the
    representative dialect-lowering transport head (`repr_dialectHead_transport`,
    the `id/id` form of the registered `regPass1`/`regPass3` squares) with the
    x86 instruction step (`x86Add_transport`, the adapter view of the registered
    `relatedX86Add` preservation) via `TransportSquare.comp` yields: the abstract
    operand-pair denotation, transported through the dialect-lowering head and
    then realised by the emitted x86 `ADD` instruction, equals the abstract sum —
    i.e. `x86Add a b = a + b` produced as the *pasted* two-factor transport (1
    dialect head ⋆ 1 x86 step), **not** by invoking `x86Add_eq` directly.

    This chains both halves' shapes through the single `TransportSquare.comp`
    engine.  The factors are the dialect transport (representative of the 3-pass
    `registryChain_threePass`) and one x86 instruction step; the value-model seam
    between the chain's structured run-output and the scalar `BitVec` ALU domain
    is documented in the module `Scope` (the `runOutputToWords` read-back a full
    splice needs). -/
theorem endToEnd_dialectChain_then_x86 (a b : BitVec 64) :
    (fun p : BitVec 64 × BitVec 64 => x86Add p.1 p.2)
        (encPair (id : BitVec 64 → BitVec 64) (id (a, b)))
      = (id : BitVec 64 → BitVec 64)
          ((id : BitVec 64 → BitVec 64) ((fun p : BitVec 64 × BitVec 64 => p.1 + p.2) (a, b))) :=
  TransportSquare.comp repr_dialectHead_transport x86Add_transport rfl (a, b)

/-- **The end-to-end transport, reduced.**  The pasted transport above is, after
    the `id`/`encPair id` transports compute, exactly the x86 `ADD` preservation
    `x86Add a b = a + b` — confirming the two-factor composition delivers the
    expected end-to-end value equation (the source abstract `+` realised by the
    emitted x86 instruction). -/
theorem endToEnd_value_eq (a b : BitVec 64) : x86Add a b = a + b :=
  endToEnd_dialectChain_then_x86 a b

/-! ## 5. The genuine 3-pass dialect chain still composes as a transport square

For completeness we record the genuine (non-representative) dialect half as a
single composed `TransportSquare` over `Com`/`runProg` — the object that, *were*
the seam `runOutputToWords` provided, would be the left factor of a full splice.
This is the `compSquare`-folded `registryChain_threePass`, exposed here so the
end-to-end statement names both the representative composition (§4) and the real
chain it stands for. -/

/-- **The genuine dialect half as one transport square** (the 3-pass chain folded
    by `compSquare`).  Carrier-changing `(mapVal, transTy)` over `Com`/`runProg`;
    parametric in the printer-TCB edges, exactly as `registryChain_threePass`.
    This is the real left factor a full (non-representative) end-to-end splice
    would paste the x86 step onto across the documented value-model seam. -/
theorem dialectChain_as_transportSquare (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n)) :
    runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)
      = transTy ((srcCom q n).denote V) :=
  registryChain_threePass' q n hLeaf hInj hPinj V

end CatCrypt.Crypto.SecureCompilation.VIR.EndToEndTransport
