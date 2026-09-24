/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
public import CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric

/-!
# The generic NTT-multiply emit → poly-VALUE bridge

This is the NTT analogue of `GenericFieldEmitValue.lean` — the emit→value MIDDLE
SEAM for NTT-multiply.  Where the field bridge ties an emitted field-op leaf to
the abstract `ZMod q` field value, this module ties an emitted **NTT-multiply
leaf** (`ntt_poly_mul`, a named binary call) to the abstract **polynomial
product** value: the cyclic convolution of two length-`n` coefficient vectors,
computed in the evaluation (DFT) domain via transform · pointwise-multiply ·
inverse-transform.

The emitter is *reused* unchanged: an NTT-multiply leaf is just a named binary
call, so `emitFieldBinop "ntt_poly_mul" dest a b` lowers to one `.RCall` exactly
as a field-op leaf does.  The carrier is abstract: a `decode : RustVal .TFp →
(Fin n → R)` reading the `.TFp` slot as a length-`n` coefficient vector over a
field `R`, with a primitive `n`-th root `ω`.

This module composes:

1. the **structural emit** `emitFieldBinop "ntt_poly_mul" dest a b`
   (= one `.RCall`), reused from the field bridge, with
2. the **operational denotation** `RustExec N leafSpec` (`Jasmin/LowCT.lean §6`),
   threaded by the *op-agnostic* `emitFieldBinop_exec`, with
3. a **leaf-realization hypothesis** (`NttEmitRealizes`) — the localized residual
   that the emitted leaf decodes to the abstract NTT-multiply value
   `nttMul n ω (decode aVal) (decode bVal)`.

## What is closed here vs. localized

* **Closed (Lean theorem):** the structural-emit ↔ operational-denotation
  composition.  The `RustExec`-threading lemma `emitFieldBinop_exec` is
  op-agnostic (it talks only about `leafSpec.call`, not the carrier or op) and is
  reused verbatim; the field bridge's `emitFieldBinop_realizes_value` itself fixes
  the carrier to `ZMod q`, so its small composition body is reproduced here over
  the abstract `Fin n → R` polynomial carrier with `op := nttMul n ω`.
* **Closed (Lean theorem):** the **commuting-square discharge**
  `nttEmitRealizes_of_cyclicConv`.  The NTT-multiply correctness theorem
  `nttMul_eq_cyclicConv'` (UNCONDITIONAL over a field with `IsPrimitiveRoot ω n`
  and `(n:R) ≠ 0`) rewrites `nttMul = cyclicConv`, so a leaf realizing the
  **cyclic convolution** (`NttKernelRealizes`) automatically realizes `nttMul`.
  The transform·pointwise·inverse = convolution content is discharged by the
  proven theorem; the residual after the square is exactly "the leaf decodes to
  the cyclic convolution" — a structural/KAT fact about the emitted kernel.
* **Localized (named hypothesis `NttKernelRealizes`):** that the opaque leaf-call
  value decodes to the length-`n` cyclic convolution `cyclicConv n (decode aVal)
  (decode bVal)` the emitted kernel actually computes.  This is the leaf-bytes
  KAT residual.

## Non-vacuity

`nttEmitRealizes_canonical` exhibits a concrete `LeafSpec` (built from a
`cyclicConv`-returning realizer) under which `NttKernelRealizes` — hence
`NttEmitRealizes` — holds, so the hypotheses are satisfiable, not an
unsatisfiable over-constraint.  The cross-prover content is the gap
between this canonical realizer and the emitted NTT kernel's real byte
semantics, which lives outside Lean.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric

variable {R : Type*} [Field R]

/-! ## §1  The NTT-multiply leaf-realization predicate (the value content)

`NttEmitRealizes n ω decode leaf leafSpec` is the NTT analogue of
`GenericFieldEmitValue.FieldEmitRealizes`, with the abstract binop fixed to the
NTT-multiply pipeline `nttMul n ω`.  It asserts: the CatCrypt `leafSpec.call`
oracle, applied at `leaf` on the `.TFp` carrier to two polynomial arguments
`aVal`, `bVal`, produces a destination value whose decoded coefficient vector is
`nttMul n ω (decode aVal) (decode bVal)` — the value the NTT-multiply commuting
square computes. -/

/-- **The localized NTT-multiply leaf-realization predicate.**  For every operand
    pair `aVal`, `bVal` (and any prior dest value `oldDest`), the leaf-call value
    decodes to `nttMul n ω (decode aVal) (decode bVal)` — the abstract
    transform·pointwise·inverse polynomial product.

    This is `FieldEmitRealizes`'s residual with `op := nttMul n ω`.  It is **not**
    a Lean theorem: that `leafSpec.call`'s opaque value coincides with the
    abstract NTT-multiply value is the cross-prover edge, named here. -/
def NttEmitRealizes (n : ℕ) (ω : R) (decode : RustVal .TFp → (Fin n → R))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = nttMul n ω (decode aVal) (decode bVal)

/-- **The localized NTT-multiply KERNEL-realization predicate.**  The residual
    the emitted kernel *actually* satisfies byte-wise: the leaf-call value decodes
    to the length-`n` **cyclic convolution** `cyclicConv n (decode aVal) (decode
    bVal)` — multiplication in `R[X]/(Xⁿ − 1)`.  This is the leaf-bytes KAT fact;
    the commuting square (`nttMul_eq_cyclicConv'`) lifts it to `NttEmitRealizes`. -/
def NttKernelRealizes (n : ℕ) [NeZero n] (decode : RustVal .TFp → (Fin n → R))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = cyclicConv n (decode aVal) (decode bVal)

/-! ## §2  The payload: emit → poly VALUE (inherited from the field bridge)

`emitFieldBinop_realizes_value` is parametric in the binop `op` and the decoder
`decode`, and the emitter `emitFieldBinop` and `RustExec`-threading
`emitFieldBinop_exec` are op-agnostic.  So the NTT payload is a *direct
specialization* with `op := nttMul n ω` — no proof is copied. -/

/-- **The generic NTT-multiply emit→value bridge.**  Given the localized
    leaf-realization `NttEmitRealizes n ω decode leaf leafSpec` (the residual the
    NTT commuting square + leaf-bytes KAT discharge outside Lean), *running*
    `emitFieldBinop leaf dest a b` under `leafSpec` from a state holding `aVal`,
    `bVal` writes into `dest` a value that **decodes to the NTT-multiply value**
    `nttMul n ω (decode aVal) (decode bVal)`.

    The structural-emit ↔ `RustExec`-denotation thread is reused verbatim from
    the op-agnostic `emitFieldBinop_exec` (it talks only about `leafSpec.call`,
    not the carrier or op); only the localized `decode`/`op` residual differs.
    (The field bridge's `emitFieldBinop_realizes_value` fixes the carrier to
    `ZMod q`, so it is not directly specializable to the abstract `Fin n → R`
    polynomial carrier; the small composition body is reproduced here over the
    op-agnostic `emitFieldBinop_exec`.) -/
theorem emitNttMul_realizes_value
    (N : Nat) (n : ℕ) (ω : R) (decode : RustVal .TFp → (Fin n → R))
    (leafSpec : LeafSpec) (leaf dest a b : String)
    (aVal bVal oldDest : RustVal .TFp)
    (hda : dest ≠ a) (hdb : dest ≠ b) (hab : a ≠ b)
    (hreal : NttEmitRealizes n ω decode leaf leafSpec) :
    ∃ rs',
      RustExec N leafSpec (emitFieldBinop leaf dest a b)
          (operandState dest a b aVal bVal oldDest) rs'
        ∧ (∀ v, locatedLookup rs' ⟨dest, .TFp⟩ = some v →
            decode v = nttMul n ω (decode aVal) (decode bVal)) := by
  refine ⟨_, emitFieldBinop_exec N leafSpec leaf dest a b aVal bVal oldDest
      hda hdb hab, ?_⟩
  intro v hv
  -- The post-state's `dest` slot is the leaf-call value (by `locatedUpdate_dest`),
  -- which `NttEmitRealizes` decodes to the NTT-multiply value.
  have hdest : locatedLookup
      (locatedUpdate (operandState dest a b aVal bVal oldDest) ⟨dest, .TFp⟩
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])) ⟨dest, .TFp⟩
      = some (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) := by
    unfold locatedLookup
    rw [locatedUpdate_dest]
    simp
  rw [hdest] at hv
  have : v = leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
      [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩] := by
    exact (Option.some.injEq _ _).mp hv.symm
  rw [this]
  exact hreal aVal bVal oldDest

/-! ## §3  The commuting-square discharge

`nttMul_eq_cyclicConv'` (UNCONDITIONAL over a field with `IsPrimitiveRoot ω n`
and `(n:R) ≠ 0`) is the proven content that transform·pointwise·inverse equals
the cyclic convolution.  It lifts a kernel-realization (leaf = cyclic conv) to a
full NTT-multiply realization (leaf = `nttMul`): after rewriting `nttMul =
cyclicConv`, the goal *is* the kernel residual. -/

/-- **The commuting-square discharge.**  From the kernel-realization residual
    `NttKernelRealizes n decode leaf leafSpec` (the leaf decodes to the cyclic
    convolution — the leaf-bytes KAT fact) plus a primitive `n`-th root `ω` and
    `(n:R) ≠ 0`, conclude the full NTT-multiply realization `NttEmitRealizes n ω
    decode leaf leafSpec`.

    The transform·pointwise·inverse = convolution content is discharged by the
    proven `nttMul_eq_cyclicConv'`; what remains after the square is exactly the
    kernel residual `hker`. -/
theorem nttEmitRealizes_of_cyclicConv
    {n : ℕ} [NeZero n] {ω : R} (decode : RustVal .TFp → (Fin n → R))
    (leaf : String) (leafSpec : LeafSpec)
    (hω : IsPrimitiveRoot ω n) (hn : (n : R) ≠ 0)
    (hker : NttKernelRealizes n decode leaf leafSpec) :
    NttEmitRealizes n ω decode leaf leafSpec := by
  intro aVal bVal oldDest
  rw [hker aVal bVal oldDest, nttMul_eq_cyclicConv' hω hn]

/-! ## §4  Non-vacuity: a canonical realizer satisfies `NttKernelRealizes`

As in `GenericFieldEmitValue.fieldEmitRealizes_canonical`, we exhibit a concrete
`LeafSpec` under which `NttKernelRealizes` holds — confirming the predicate is
the right shape (an inhabited cross-prover claim).  Composed with the §3 square,
it also satisfies `NttEmitRealizes`. -/

/-- The canonical `CallSpec` realizing NTT-multiply (as its cyclic-convolution
    kernel) at leaf `leaf`: at the target name it decodes the two positional
    `.TFp` polynomial arguments, computes their length-`n` cyclic convolution,
    and re-encodes via a section `encode`; off-target it returns `oldDest`.  The
    NTT analogue of `GenericFieldEmitValue.fieldBinopCallSpec`. -/
def nttKernelCallSpec {n : ℕ} [NeZero n] (decode : RustVal .TFp → (Fin n → R))
    (encode : (Fin n → R) → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → (Fin n → R) := fun a =>
        if ht : a.1 = TowerType.TFp then decode (ht ▸ a.2) else 0
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encode (cyclicConv n (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity witness for `NttKernelRealizes`.**  For the canonical `LeafSpec`
    built from `nttKernelCallSpec` with a decoder section `encode` (`decode ∘
    encode = id`), the kernel-realization holds — so the localized hypothesis is
    satisfiable.  The cross-prover content is precisely the gap between
    this canonical realizer and the emitted NTT kernel's real byte semantics
    (the leaf-bytes KAT), which lives outside Lean. -/
theorem nttKernelRealizes_canonical
    {n : ℕ} [NeZero n] (decode : RustVal .TFp → (Fin n → R))
    (encode : (Fin n → R) → RustVal .TFp)
    (hsection : ∀ p : Fin n → R, decode (encode p) = p)
    (leaf : String) (limbStore : LimbStoreSpec) :
    NttKernelRealizes n decode leaf
      { call := nttKernelCallSpec decode encode leaf, limbStore := limbStore } := by
  intro aVal bVal oldDest
  show decode (nttKernelCallSpec decode encode leaf leaf .TFp [.TFp, .TFp]
      oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = cyclicConv n (decode aVal) (decode bVal)
  simp only [nttKernelCallSpec, ite_true, dite_true, hsection]

/-- **Non-vacuity witness for `NttEmitRealizes`.**  Composing the canonical
    kernel realizer (§4) with the commuting-square discharge (§3): for a primitive
    `n`-th root `ω` with `(n:R) ≠ 0`, the canonical `LeafSpec` also satisfies the
    full NTT-multiply realization. -/
theorem nttEmitRealizes_canonical
    {n : ℕ} [NeZero n] {ω : R} (decode : RustVal .TFp → (Fin n → R))
    (encode : (Fin n → R) → RustVal .TFp)
    (hsection : ∀ p : Fin n → R, decode (encode p) = p)
    (hω : IsPrimitiveRoot ω n) (hn : (n : R) ≠ 0)
    (leaf : String) (limbStore : LimbStoreSpec) :
    NttEmitRealizes n ω decode leaf
      { call := nttKernelCallSpec decode encode leaf, limbStore := limbStore } :=
  nttEmitRealizes_of_cyclicConv decode leaf _ hω hn
    (nttKernelRealizes_canonical decode encode hsection leaf limbStore)

end CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
