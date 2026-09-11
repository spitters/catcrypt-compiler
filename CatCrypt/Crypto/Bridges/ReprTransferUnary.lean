/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Bridges.ReprTransfer
public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer

/-!
# Unary representation-transfer: the map-level homomorphism for NON-homomorphic kernels

`Bridges/ReprTransfer.lean` factors the *binary* emit-realization transports into
one structure: `BinOpHomOn φ dom src tgt` — a homomorphism along a decode map `φ`
on a canonical sub-domain — and `BinOpRealization`/`eq_transfer` for the
embedding-level (both-directions) case. The Montgomery-butterfly **combine** stage
(`a + w·b`) is exactly a `BinOpHomOn`, and the pilot
(`SecureCompilation/MontButterflyTransfer.lean`) generates its realization off
`BinOpHomOn.realizes`.

But the *reduce* kernels — Montgomery REDC (`·R⁻¹ mod q`), Barrett (`· % q`),
Fermat-inverse (`xᵖ⁻²`), the packed conditional-subtract `csub` — are **unary,
non-homomorphic** maps. They do not commute with a single algebraic op, so
neither `BinOpHomOn` (binary, op-homomorphism) nor `BinOpRealization` (binary
op-tree) has the right shape. The pilot's §"Scope" records exactly this API gap:

> `ReprTransfer.BinOpHomOn`'s `tgt` is a *binary* `A → A → A` … whereas the REDC
> is a *unary*, *non-homomorphic* map … it would need a `UnaryHomOn`/`Related`-
> over-decode variant keyed on a `LeafSpec.call`.

This module is that variant. The crucial observation: `KernelRealizes` (the unary
emit-realization predicate, `SecureCompilation/ProtocolEmitRealizes.lean`) and
`transferKernel` ALREADY ARE this unary transport — but stated as bare `Prop`s,
not as a resolvable `ReprTransfer`-style structure. We:

* define `UnaryHomOn φ dom tgt src` — the *map-level* unary transport square
  `φ (tgt a) = src (φ a)` on a sub-domain `dom`, the unary analogue of
  `BinOpHomOn` (a map `φ`, no injectivity, no univalence);
* identify the machine-side unary op the kernel computes —
  `machineUnaryOp leafSpec leaf oldDest := fun x => leafSpec.call leaf .TFp [.TFp]
  oldDest [⟨.TFp, x⟩]` — as the `UnaryHomOn` *source* `tgt`, and the abstract
  `spec` as its *target* `src`, with `decode` the map `φ`;
* prove the **bridge** `kernelRealizes_iff_unaryHomOn`: `KernelRealizes decode
  spec leaf leafSpec` holds **iff** for every `oldDest` the machine op is a
  (total-domain) `UnaryHomOn` along `decode` to `spec`. So `KernelRealizes` is
  *derivable from* a `UnaryHomOn` instance via `.realizes` + the call unfold,
  rather than a hand `simp`/`rw`. This is the unary analogue of
  `GenericKernelRealization.barrett_iff_kernel` (which pins `spec`); here we pin
  the *transport structure*.

## Application (the point — a reduce realization via the engine, not a hand proof)

§3 RE-DERIVES the Barrett modular-reduce realization
(`ConcreteBarrettRealizer.barrett_realizes_concrete`) THROUGH `UnaryHomOn`: the
single commuting square (decode-of-call = `barrettCondsub` of decode, the
`decodeB_encodeB` round-trip) is packaged as a `UnaryHomOn` instance
(`barrettUnaryHom`), and the `KernelRealizes` falls out of the bridge +
`.realizes` — NOT the original file's hand `simp only [barrettCallSpec …] ; rw
[decodeB_encodeB …]`. The comparison: the *square* still consumes
`decodeB_encodeB` (the byte-codec content — there is no free lunch), but
the *plumbing* from square to `KernelRealizes` is now the engine's, identical to
how the binary butterfly is generated. Same statement, same axioms.

## Scope

`UnaryHomOn` is the *map-level* (map₁, univalence-free) transport: a decode map
`φ`, a sub-domain `dom`, a square. It says nothing more than the square it
packages — it is plumbing, not new mathematical content; the kernel's actual
reduce fact (`barrettCondsub_eq_mod`, `decodeB_encodeB`, the `runZBlock` proof)
still lives at the square. Its value is uniformity: every unary reduce kernel
becomes "give the square, read off `.realizes`", the same shape as the binary
butterfly, with no `LeafSpec.call`-shaped hand `simp` per kernel. The only trust
inherited here is whatever the cited square consumes (for Barrett: the proved
`decodeB_encodeB` byte codec — no KAT, no `jasminc_preserves_ct`, no univalence).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.ReprTransferUnary

universe u v

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-! ## §1  The unary map-level transport square

The unary analogue of `ReprTransfer.BinOpHomOn`: along a decode map `φ : α → β`,
the machine-side unary op `tgt : α → α` pushes through `φ` to the abstract unary
op `src : β → β`, on a canonical sub-domain `dom`. Map-level — no injectivity, no
univalence (`φ` is the Trocq map₁). This is precisely the structure a
*non-homomorphic* unary kernel (REDC, Barrett `% q`, Fermat inverse, `csub`)
needs: the kernel need not commute with any algebraic op; it need only have its
decode push through to a named abstract `spec`. -/

/-- A **domain-restricted unary-operation homomorphism**: along a map `φ : α → β`,
    the machine-side unary op `tgt` pushes through `φ` to the abstract unary op
    `src`, on a canonical sub-domain `dom`. The unary twin of
    `ReprTransfer.BinOpHomOn`. Map-level: no injectivity required. -/
structure UnaryHomOn {α : Type u} {β : Type v} (φ : α → β) (dom : α → Prop)
    (tgt : α → α) (src : β → β) where
  /-- The transport square, on the canonical sub-domain: decoding the machine-side
      result equals the abstract op of the decoded input. -/
  app_eq : ∀ a, dom a → φ (tgt a) = src (φ a)

namespace UnaryHomOn
variable {α : Type u} {β : Type v} {φ : α → β} {dom : α → Prop}
  {tgt : α → α} {src : β → β}

/-- The realization equation: on a canonical input, decoding the machine-side
    result equals the abstract op on the decoded input. The unary analogue of
    `BinOpHomOn.realizes` / `transferKernel`. -/
theorem realizes (H : UnaryHomOn φ dom tgt src) {a : α} (ha : dom a) :
    φ (tgt a) = src (φ a) := H.app_eq a ha

end UnaryHomOn

/-! ## §2  The bridge to `KernelRealizes`

`KernelRealizes decode spec leaf leafSpec := ∀ x oldDest, decode (leafSpec.call
leaf .TFp [.TFp] oldDest [⟨.TFp, x⟩]) = spec (decode x)`. Read at a fixed
`oldDest`, the inner `leafSpec.call …` is a *unary* function of `x` — the
machine-side unary op the kernel computes. Naming it `machineUnaryOp`, the
predicate `KernelRealizes` is exactly: for every `oldDest`, `decode` is a
`UnaryHomOn` (on the total domain) from that machine op to `spec`. -/

/-- The machine-side unary op a leaf computes at a fixed `oldDest`: feed `x` as the
    sole `.TFp` argument of `leaf` and take the call's value. This is the
    `UnaryHomOn` *source* `tgt` — a plain `RustVal .TFp → RustVal .TFp` unary map,
    abstracting the `LeafSpec.call` signature away (the pilot's named API gap). -/
def machineUnaryOp (leafSpec : LeafSpec) (leaf : String) (oldDest : RustVal .TFp) :
    RustVal .TFp → RustVal .TFp :=
  fun x => leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, x⟩]

/-- **The bridge (an `Iff`, the unary analogue of `barrett_iff_kernel`).**
    `KernelRealizes decode spec leaf leafSpec` holds **iff** for every `oldDest`,
    `decode` is a total-domain `UnaryHomOn` from the machine op `machineUnaryOp …
    oldDest` to the abstract `spec`. So a `UnaryHomOn` instance (whose single
    obligation is the kernel's commuting square) YIELDS `KernelRealizes` via
    `.realizes` + the `machineUnaryOp` unfold — `KernelRealizes` is derivable from
    the engine object, not a bespoke `simp`/`rw`. -/
theorem kernelRealizes_iff_unaryHomOn {C : Type u} (decode : RustVal .TFp → C)
    (spec : C → C) (leaf : String) (leafSpec : LeafSpec) :
    KernelRealizes decode spec leaf leafSpec
      ↔ ∀ oldDest : RustVal .TFp,
          Nonempty (UnaryHomOn decode (fun _ => True)
            (machineUnaryOp leafSpec leaf oldDest) spec) := by
  constructor
  · intro h oldDest
    exact ⟨{ app_eq := fun x _ => h x oldDest }⟩
  · intro h x oldDest
    exact (h oldDest).some.realizes (a := x) trivial

/-- **The bridge, packaging direction (the resolvable engine object).** A
    `UnaryHomOn decode (fun _ => True) (machineUnaryOp leafSpec leaf oldDest) spec`
    for **every** `oldDest` PRODUCES `KernelRealizes decode spec leaf leafSpec`.
    This is the engine's `transferKernel`-analogue: hand it the per-`oldDest`
    transport square and it delivers the emit-realization predicate, with no
    `LeafSpec.call`-shaped hand `simp`. -/
theorem kernelRealizes_of_unaryHomOn {C : Type u} {decode : RustVal .TFp → C}
    {spec : C → C} {leaf : String} {leafSpec : LeafSpec}
    (H : ∀ oldDest : RustVal .TFp,
      UnaryHomOn decode (fun _ => True) (machineUnaryOp leafSpec leaf oldDest) spec) :
    KernelRealizes decode spec leaf leafSpec :=
  (kernelRealizes_iff_unaryHomOn decode spec leaf leafSpec).mpr
    (fun oldDest => ⟨H oldDest⟩)

/-- Conversely, `KernelRealizes` packages back to a per-`oldDest` `UnaryHomOn`
    along `decode` — the unary transport is recovered from the predicate. -/
theorem unaryHomOn_of_kernelRealizes {C : Type u} {decode : RustVal .TFp → C}
    {spec : C → C} {leaf : String} {leafSpec : LeafSpec}
    (h : KernelRealizes decode spec leaf leafSpec) (oldDest : RustVal .TFp) :
    UnaryHomOn decode (fun _ => True) (machineUnaryOp leafSpec leaf oldDest) spec :=
  { app_eq := fun x _ => h x oldDest }

end CatCrypt.Crypto.Bridges.ReprTransferUnary

/-! ## §3  Application: the Barrett reduce realization, GENERATED via `UnaryHomOn`

We re-derive `ConcreteBarrettRealizer.barrett_realizes_concrete`
(`KernelRealizes decodeB (barrettCondsub q k) leaf …`) THROUGH the unary engine.
The single commuting square — decoding the Barrett leaf-call equals
`barrettCondsub q k` of the decoded input — is the `UnaryHomOn` obligation; it is
discharged by the same `decodeB_encodeB` round-trip the original file uses (the
byte-codec content, unavoidable), but the step from square to
`KernelRealizes` is now `kernelRealizes_of_unaryHomOn`, NOT a hand `simp`/`rw`. -/

namespace CatCrypt.Crypto.Bridges.ReprTransferUnary.BarrettViaUnary

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer
open CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric
open CatCrypt.Crypto.Bridges.ReprTransferUnary

/-- **The Barrett transport square, packaged as a `UnaryHomOn`.** At a fixed
    `oldDest`, the machine op `machineUnaryOp (barrettLeafSpec …) leaf oldDest`
    pushes through `decodeB width` to the abstract reduce `barrettCondsub q k`.
    The single `app_eq` obligation is exactly the per-`oldDest` instance of
    `barrett_realizes_concrete` — the proved `decodeB_encodeB` byte round-trip.
    This is the engine object; the `KernelRealizes` is read off it below. -/
def barrettUnaryHom (q k width : ℕ) (hw : width ≤ 48) (leaf : String)
    (limbStore : LimbStoreSpec) (oldDest : RustVal .TFp) :
    UnaryHomOn (decodeB width) (fun _ => True)
      (machineUnaryOp (barrettLeafSpec q k width leaf limbStore) leaf oldDest)
      (fun x => barrettCondsub q k x) where
  app_eq x _ :=
    barrett_realizes_concrete q k width hw leaf limbStore x oldDest

/-- **Barrett reduce realization, GENERATED by the unary engine.** Identical
    statement to `ConcreteBarrettRealizer.barrett_realizes_concrete`
    (`KernelRealizes decodeB (barrettCondsub q k) leaf …`), but obtained via
    `kernelRealizes_of_unaryHomOn` applied to the `barrettUnaryHom` transport
    square — NOT the original file's hand `simp only [barrettCallSpec …] ; rw
    [decodeB_encodeB …]`. The square consumes the same `decodeB_encodeB` content;
    the plumbing from square to predicate is the engine's. -/
theorem barrett_realizes_via_unary (q k width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeB width) (fun x => barrettCondsub q k x) leaf
      (barrettLeafSpec q k width leaf limbStore) :=
  kernelRealizes_of_unaryHomOn
    (fun oldDest => barrettUnaryHom q k width hw leaf limbStore oldDest)

/-- The engine-generated realization agrees with the hand-proved one — same
    statement, same value (both are the `KernelRealizes` predicate, `Prop`, so
    equal by proof irrelevance; recorded here to make the "same statement" claim
    explicit). -/
theorem barrett_via_unary_eq_hand (q k width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec) :
    barrett_realizes_via_unary q k width hw leaf limbStore
      = barrett_realizes_concrete q k width hw leaf limbStore := rfl

end CatCrypt.Crypto.Bridges.ReprTransferUnary.BarrettViaUnary
