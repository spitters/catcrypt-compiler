/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

/-!
# A leaf whose oracle agreement is a THEOREM: the `poly_add` width-16 kernel

Two design paths carry a leaf's semantics into a deployed `Com jasminDialect`
kernel; this module exhibits the first, alongside `Pairing.Eip197Denote`'s
witness of the second.

## Path 1 — the fixed semantics already realises the leaf (this file)

For a leaf that the dialect's *fixed* leaf semantics `jasminExtSem` already
computes, the leaf's agreement with an abstract spec is a **theorem**, and the
deployed kernel needs **no leaf axiom**. `jasminExtSem`'s width-16 binary arm
(`JasminDialect.jasminExtSem`) gives every
`[.stackArr 16 _, .stackArr 16 _] → .stackArr 16 _` leaf named `"poly_add"` the
concrete elementwise-sum semantics `fun j => a j + b j`. So:

* `polyAdd a b := fun j => a j + b j` — the abstract spec;
* `PolyAddAgrees leafSem` — the leaf agreement (`leafSem` computes `polyAdd`);
* `jasminExtSem_polyAdd_agrees : PolyAddAgrees jasminExtSem` — the agreement
  **discharged by the actual `jasminExtSem` semantics** (a theorem: the arm is
  the elementwise sum, `stackGet` on an in-range index is the entry). No oracle
  axiom is introduced — the fixed semantics *is* the realiser.
* `myPolyKernel_denote` — the front-sourced kernel, denoted through the
  **default** `jasminDenote` (whose `extCall` arm consults `jasminExtSem`
  directly — no `jasminDenoteWith`, no abstract oracle), computes `polyAdd a b`.
  Its correctness is fully in-kernel: no leaf assumption appears.

## Path 2 — a leaf outside the fixed semantics, oracle defined from the primitive (`Pairing.Eip197Denote`)

For a leaf the fixed semantics does not compute — a pairing (`bn254_pairing`), a
Keccak permutation, any leaf `jasminExtSem` sends to `JasminTy.default` — the
kernel is denoted through `jasminDenoteWith leafSem` against a leaf oracle
defined from an uninterpreted primitive, and the agreement `leafSem` ↔ the
primitive (`Eip197Denote.eip197LeafOracle_agrees`) is a theorem that holds by
construction of that oracle. The kernel theorem states what the orchestration
computes when each leaf computes its primitive and carries no assumption; it
says nothing about the emitted leaf code, which a byte-KAT against the reference
implementation (`bench/bn254_compare/`) checks outside Lean.

The kernel here is the same straight-line-`Com`-over-leaves shape as the EIP-197
verifier — a `buildOrchCom` phase schedule, one leaf, threaded to `.ret` — but
because its one leaf is width-16 `poly_add`, the agreement is a theorem about the
dialect's own leaf semantics, `jasminExtSem_polyAdd_agrees`, rather than about an
oracle defined from the primitive.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.LeafProvenDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

/-! ## 1. Wire layout for the width-16 poly buffer -/

/-- The lane count of the poly buffer (a small ML-KEM/NTT-style 16-bit lane
    vector). Concrete so the front's generation gate reduces by `rfl`. -/
def polyN : Nat := 16

/-- The leaf symbol the front emits for the elementwise poly add — the exact
    name `jasminExtSem`'s width-16 binary arm realises as the elementwise sum. -/
def polyAddLeafName : String := "poly_add"

/-- The poly-add leaf signature: two 16-bit-lane buffers. -/
def polyArgTys : List JasminTy := [.stackArr 16 polyN, .stackArr 16 polyN]

/-- The poly-add leaf returns a 16-bit-lane buffer. -/
def polyRetTy : JasminTy := .stackArr 16 polyN

/-! ## 2. The abstract spec + the leaf agreement -/

/-- The abstract spec: elementwise sum of two 16-bit-lane vectors. -/
def polyAdd (a b : Fin polyN → BitVec 16) : Fin polyN → BitVec 16 :=
  fun j => a j + b j

/-- The leaf agreement: `leafSem` on the `poly_add` signature computes `polyAdd`
    of its two operands. For a pairing/Keccak leaf the corresponding agreement
    holds by construction of an oracle defined from the primitive (Path 2); for
    `poly_add` it is proved below for the dialect's fixed semantics (Path 1). -/
def PolyAddAgrees
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) polyArgTys,
    leafSem polyAddLeafName polyArgTys polyRetTy args = polyAdd args.head args.tail.head

/-- **The leaf agreement, discharged by the actual `jasminExtSem` semantics.**
    A THEOREM, not an axiom: `jasminExtSem`'s width-16 binary arm on the
    `"poly_add"` name is `fun j => stackGet a j.val + stackGet b j.val`, and
    `stackGet` on an in-range `Fin polyN` index is exactly the underlying entry
    (`stackGet_id`), so the arm equals `polyAdd a b`. No leaf oracle is posited —
    the fixed semantics itself realises the primitive. -/
theorem jasminExtSem_polyAdd_agrees : PolyAddAgrees jasminExtSem := by
  intro args
  funext j
  show stackGet args.head j.val + stackGet args.tail.head j.val
      = args.head j + args.tail.head j
  rw [stackGet_id, stackGet_id]

/-! ## 3. The front-sourced kernel -/

/-- Input buffer context for the poly-add kernel: `[a, b]` (root slots from the
    tail: `b = 0`, `a = 1`). -/
def polyAddCtxt : Ctxt jasminDialect := [.stackArr 16 polyN, .stackArr 16 polyN]

/-- The kernel as a one-phase front schedule: `out = poly_add(a, b)`. -/
def polyAddSchedule : List CallPhase :=
  [ { leaf := polyAddLeafName, argTys := polyArgTys, retTy := polyRetTy,
      argSlots := [1, 0] } ]            -- out = poly_add(a, b)  (a = slot 1, b = slot 0)

/-- **Generation gate.** The front resolves the poly-add schedule. -/
theorem myPolyKernelCom_isSome :
    (buildOrchCom polyAddCtxt polyAddSchedule 2 polyRetTy).isSome = true := by rfl

/-- The poly-add kernel, **front-sourced** through
    `OrchestrationFront.buildOrchCom` — one opaque `.extCall "poly_add"` leaf,
    threaded straight to `.ret`. -/
def myPolyKernelCom : Com jasminDialect polyAddCtxt polyRetTy :=
  (buildOrchCom polyAddCtxt polyAddSchedule 2 polyRetTy).get myPolyKernelCom_isSome

/-- **The deployed kernel at the DEFAULT `jasminDenote`.** Denoted through the
    ordinary `jasminDenote` instance — whose `extCall` arm consults the fixed
    `jasminExtSem`, no `jasminDenoteWith` and no abstract oracle — the kernel
    computes `polyAdd a b`. Correctness is fully proven with **no leaf axiom**:
    the single `poly_add` leaf's semantics is concrete, so its agreement
    (`jasminExtSem_polyAdd_agrees`) is a theorem, not an assumption. -/
theorem myPolyKernel_denote (a b : Fin polyN → BitVec 16) :
    @Com.denote _ _ _ jasminDenote _ _ myPolyKernelCom (.cons a (.cons b .nil))
      = polyAdd a b := by
  show jasminExtSem polyAddLeafName polyArgTys polyRetTy (.cons a (.cons b .nil))
      = polyAdd a b
  exact jasminExtSem_polyAdd_agrees (.cons a (.cons b .nil))

end CatCrypt.Crypto.Pairing.LeafProvenDenote
