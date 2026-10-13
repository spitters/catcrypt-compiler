/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
public import CatCrypt.Crypto.Optimizer.Lattice.NegacyclicMultiplyCorrect
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances

/-!
# The NEGACYCLIC NTT-multiply emit → poly-VALUE bridge

This is the **negacyclic** counterpart of `GenericNttEmitValue.lean` (the cyclic
seam).  ML-DSA multiplies in `Z_q[X]/(Xⁿ + 1)` — the *negacyclic* ring — so its
NTT-multiply leaf computes the **negacyclic convolution**, not the cyclic one;
the cyclic seam (`GenericNttEmitValue`) does not fit a negacyclic leaf.  This
module mirrors the cyclic seam structure exactly, swapping the cyclic pipeline
`nttMul n ω` for the negacyclic pipeline `nttNegaMul ψ` (pre-twist, cyclic
multiply at `ω = ψ²`, untwist) and the cyclic-convolution residual `cyclicConv`
for the negacyclic-convolution residual `negaConv`.

The carrier is abstract: a `decode : RustVal .TFp → (Fin n → R)` reading the
`.TFp` slot as a length-`n` coefficient vector over a field `R`, with a `2n`-th
twist root `ψ` (so `ψ² = ω` is the underlying primitive `n`-th root).

## What is closed here vs. localized

* **Closed (Lean theorem):** the structural-emit ↔ operational-denotation
  composition `emitNttNegaMul_realizes_value` — a direct specialization of the
  op-agnostic `emitFieldBinop_exec` thread (reused verbatim from the field
  bridge) with the abstract op fixed to `nttNegaMul ψ`.
* **Closed (Lean theorem):** the **commuting-square discharge**
  `nttNegaEmitRealizes_of_negaConv`.  The negacyclic-multiply correctness
  theorem `nttNegaMul_eq_negaConv` (over a field with `IsPrimitiveRoot (ψ²) n`
  and `(n:R) ≠ 0`) rewrites `nttNegaMul = negaConv`, so a leaf realizing the
  **negacyclic convolution** (`NttNegaKernelRealizes`) automatically realizes
  `nttNegaMul`.  The twist·cyclic·untwist = negacyclic-convolution content is
  discharged by the proven theorem; the residual after the square is exactly
  "the leaf decodes to the negacyclic convolution" — the leaf-bytes KAT fact.
* **Closed (Lean theorem):** the **concrete ML-DSA instantiation**
  `mldsa_nttNegaEmitRealizes_of_kernel`.  At the real ML-DSA leaf
  `"ntt_poly_mul_8380417_256"` (`Z_8380417[X]/(X²⁵⁶+1)`, twist root `ψ = 1753`,
  inner root `ω = 1753² = ψ²`), the discharge instantiates at the concrete
  primitive root `isPrimitiveRoot_1753sq_256` and `n_ne_zero_8380417`, reducing
  the seam to ONE concrete leaf-bytes KAT — closing the ML-DSA NTT-multiply
  compiler leaf the cyclic seam could not.
* **Localized (named hypothesis `NttNegaKernelRealizes`):** that the opaque
  leaf-call value decodes to the length-`n` negacyclic convolution `negaConv ψ
  (decode aVal) (decode bVal)` — the ring product in `R[X]/(Xⁿ+1)` the emitted
  kernel actually computes.  This is the leaf-bytes KAT residual.

## Non-vacuity

`nttNegaEmitRealizes_canonical` exhibits a concrete `LeafSpec` (built from a
`negaConv`-returning realizer) under which `NttNegaKernelRealizes` — hence
`NttNegaEmitRealizes` — holds, so the hypotheses are satisfiable.  The
cross-prover content is the gap between this canonical realizer and the emitted
negacyclic NTT kernel's real byte semantics, which lives outside Lean.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.NegacyclicEmitRealization

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NegacyclicMultiplyCorrect
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances
open CatCrypt.Crypto.Lattice.ConcreteNttRoots

variable {R : Type*} [Field R]

/-! ## §1  The negacyclic NTT-multiply leaf-realization predicate

`NttNegaEmitRealizes ψ decode leaf leafSpec` is the negacyclic analogue of
`GenericNttEmitValue.NttEmitRealizes`, with the abstract binop fixed to the
negacyclic-multiply pipeline `nttNegaMul ψ` (`untwist ∘ nttMul (ψ²) ∘ twist`).
It asserts: the `leafSpec.call` oracle, applied at `leaf` on the `.TFp` carrier
to two polynomial arguments `aVal`, `bVal`, produces a destination value whose
decoded coefficient vector is `nttNegaMul ψ (decode aVal) (decode bVal)`. -/

/-- **The localized negacyclic NTT-multiply leaf-realization predicate.**  For
    every operand pair `aVal`, `bVal` (and any prior dest value `oldDest`), the
    leaf-call value decodes to `nttNegaMul ψ (decode aVal) (decode bVal)` — the
    abstract twist·cyclic·untwist polynomial product in `R[X]/(Xⁿ+1)`.

    This is `NttEmitRealizes`'s residual with `op := nttNegaMul ψ`. -/
def NttNegaEmitRealizes {n : ℕ} [NeZero n] (ψ : R)
    (decode : RustVal .TFp → (Fin n → R))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = nttNegaMul ψ (decode aVal) (decode bVal)

/-- **The localized negacyclic NTT-multiply KERNEL-realization predicate.**  The
    residual the emitted kernel *actually* satisfies byte-wise: the leaf-call
    value decodes to the length-`n` **negacyclic convolution** `negaConv ψ
    (decode aVal) (decode bVal)` — multiplication in `R[X]/(Xⁿ + 1)`.  This is
    the leaf-bytes KAT fact; the commuting square (`nttNegaMul_eq_negaConv`)
    lifts it to `NttNegaEmitRealizes`. -/
def NttNegaKernelRealizes {n : ℕ} [NeZero n] (ψ : R)
    (decode : RustVal .TFp → (Fin n → R))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = negaConv ψ (decode aVal) (decode bVal)

/-! ## §2  The payload: emit → poly VALUE (inherited from the field bridge)

The emitter `emitFieldBinop` and `RustExec`-threading `emitFieldBinop_exec` are
op-agnostic, so the negacyclic payload is the cyclic seam's
`emitNttMul_realizes_value` body with `op := nttNegaMul ψ`. -/

/-- **The generic negacyclic NTT-multiply emit→value bridge.**  Given the
    localized leaf-realization `NttNegaEmitRealizes ψ decode leaf leafSpec`,
    *running* `emitFieldBinop leaf dest a b` under `leafSpec` from a state
    holding `aVal`, `bVal` writes into `dest` a value that **decodes to the
    negacyclic-multiply value** `nttNegaMul ψ (decode aVal) (decode bVal)`.

    The structural-emit ↔ `RustExec`-denotation thread is reused verbatim from
    the op-agnostic `emitFieldBinop_exec`; only the localized `decode`/`op`
    residual differs. -/
theorem emitNttNegaMul_realizes_value
    (N : Nat) {n : ℕ} [NeZero n] (ψ : R) (decode : RustVal .TFp → (Fin n → R))
    (leafSpec : LeafSpec) (leaf dest a b : String)
    (aVal bVal oldDest : RustVal .TFp)
    (hda : dest ≠ a) (hdb : dest ≠ b) (hab : a ≠ b)
    (hreal : NttNegaEmitRealizes ψ decode leaf leafSpec) :
    ∃ rs',
      RustExec N leafSpec (emitFieldBinop leaf dest a b)
          (operandState dest a b aVal bVal oldDest) rs'
        ∧ (∀ v, locatedLookup rs' ⟨dest, .TFp⟩ = some v →
            decode v = nttNegaMul ψ (decode aVal) (decode bVal)) := by
  refine ⟨_, emitFieldBinop_exec N leafSpec leaf dest a b aVal bVal oldDest
      hda hdb hab, ?_⟩
  intro v hv
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

`nttNegaMul_eq_negaConv` (over a field with `IsPrimitiveRoot (ψ²) n` and
`(n:R) ≠ 0`) is the proven content that twist·cyclic·untwist equals the
negacyclic convolution.  It lifts a kernel-realization (leaf = negacyclic conv)
to a full negacyclic-multiply realization (leaf = `nttNegaMul`). -/

/-- **The commuting-square discharge.**  From the kernel-realization residual
    `NttNegaKernelRealizes ψ decode leaf leafSpec` (the leaf decodes to the
    negacyclic convolution — the leaf-bytes KAT fact) plus a primitive `n`-th
    root `ω = ψ²` and `(n:R) ≠ 0`, conclude the full negacyclic-multiply
    realization `NttNegaEmitRealizes ψ decode leaf leafSpec`.

    The twist·cyclic·untwist = negacyclic-convolution content is discharged by
    the proven `nttNegaMul_eq_negaConv`; what remains after the square is
    exactly the kernel residual `hker`. -/
theorem nttNegaEmitRealizes_of_negaConv
    {n : ℕ} [NeZero n] {ψ : R} (decode : RustVal .TFp → (Fin n → R))
    (leaf : String) (leafSpec : LeafSpec)
    (hω : IsPrimitiveRoot (ψ ^ 2) n) (hn : (n : R) ≠ 0)
    (hker : NttNegaKernelRealizes ψ decode leaf leafSpec) :
    NttNegaEmitRealizes ψ decode leaf leafSpec := by
  intro aVal bVal oldDest
  rw [hker aVal bVal oldDest, nttNegaMul_eq_negaConv hω hn]

/-! ## §4  Non-vacuity: a canonical realizer satisfies `NttNegaKernelRealizes`

As in the cyclic seam's `nttKernelRealizes_canonical`, we exhibit a concrete
`LeafSpec` under which `NttNegaKernelRealizes` holds — confirming the predicate
is the right shape.  Composed with the §3 square, it also satisfies
`NttNegaEmitRealizes`. -/

/-- The canonical `CallSpec` realizing negacyclic NTT-multiply (as its
    negacyclic-convolution kernel) at leaf `leaf`: at the target name it decodes
    the two positional `.TFp` polynomial arguments, computes their length-`n`
    negacyclic convolution `negaConv ψ`, and re-encodes via a section `encode`;
    off-target it returns `oldDest`. -/
noncomputable def nttNegaKernelCallSpec {n : ℕ} [NeZero n] (ψ : R)
    (decode : RustVal .TFp → (Fin n → R))
    (encode : (Fin n → R) → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → (Fin n → R) := fun a =>
        if ht : a.1 = TowerType.TFp then decode (ht ▸ a.2) else 0
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encode (negaConv ψ (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity witness for `NttNegaKernelRealizes`.**  For the canonical
    `LeafSpec` built from `nttNegaKernelCallSpec` with a decoder section `encode`
    (`decode ∘ encode = id`), the kernel-realization holds — so the localized
    hypothesis is satisfiable.  The cross-prover content is the gap
    between this canonical realizer and the emitted negacyclic NTT kernel's real
    byte semantics, which lives outside Lean. -/
theorem nttNegaKernelRealizes_canonical
    {n : ℕ} [NeZero n] (ψ : R) (decode : RustVal .TFp → (Fin n → R))
    (encode : (Fin n → R) → RustVal .TFp)
    (hsection : ∀ p : Fin n → R, decode (encode p) = p)
    (leaf : String) (limbStore : LimbStoreSpec) :
    NttNegaKernelRealizes ψ decode leaf
      { call := nttNegaKernelCallSpec ψ decode encode leaf,
        limbStore := limbStore } := by
  intro aVal bVal oldDest
  show decode (nttNegaKernelCallSpec ψ decode encode leaf leaf .TFp [.TFp, .TFp]
      oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = negaConv ψ (decode aVal) (decode bVal)
  simp only [nttNegaKernelCallSpec, ite_true, dite_true, hsection]

/-- **Non-vacuity witness for `NttNegaEmitRealizes`.**  Composing the canonical
    kernel realizer (§4) with the commuting-square discharge (§3): for a
    primitive `n`-th root `ω = ψ²` with `(n:R) ≠ 0`, the canonical `LeafSpec`
    also satisfies the full negacyclic-multiply realization. -/
theorem nttNegaEmitRealizes_canonical
    {n : ℕ} [NeZero n] {ψ : R} (decode : RustVal .TFp → (Fin n → R))
    (encode : (Fin n → R) → RustVal .TFp)
    (hsection : ∀ p : Fin n → R, decode (encode p) = p)
    (hω : IsPrimitiveRoot (ψ ^ 2) n) (hn : (n : R) ≠ 0)
    (leaf : String) (limbStore : LimbStoreSpec) :
    NttNegaEmitRealizes ψ decode leaf
      { call := nttNegaKernelCallSpec ψ decode encode leaf,
        limbStore := limbStore } :=
  nttNegaEmitRealizes_of_negaConv decode leaf _ hω hn
    (nttNegaKernelRealizes_canonical ψ decode encode hsection leaf limbStore)

/-! ## §5  Concrete ML-DSA instantiation

The real ML-DSA NTT-multiply compiler leaf is `"ntt_poly_mul_8380417_256"`
(`nttPolyMulName 8380417 256`), operating in `Z_8380417[X]/(X²⁵⁶+1)` — a
*negacyclic* ring with twist root `ψ = 1753` (order `512 = 2·256`), inner root
`ω = ψ² = 1753²` (primitive `256`-th root).  Instantiating the §3 discharge at
the concrete primitive root `isPrimitiveRoot_1753sq_256` and `n_ne_zero_8380417`
reduces the seam to ONE concrete leaf-bytes KAT at the REAL ML-DSA leaf —
closing what the cyclic seam (`GenericNttEmitValue`) could not. -/

/-- **ML-DSA negacyclic emit→realization at the real leaf.**  From the
    leaf-bytes KAT residual `NttNegaKernelRealizes 1753 decode
    "ntt_poly_mul_8380417_256" leafSpec` (the emitted ML-DSA NTT-multiply kernel
    decodes to the negacyclic convolution `negaConv 1753`), the full negacyclic
    NTT-multiply realization `NttNegaEmitRealizes 1753 …` holds — the emitted
    leaf decodes to the negacyclic-multiply pipeline `nttNegaMul 1753`.

    The discharge instantiates `nttNegaEmitRealizes_of_negaConv` at the concrete
    ML-DSA root `isPrimitiveRoot_1753sq_256 : IsPrimitiveRoot ((1753)² ) 256`
    (= the `IsPrimitiveRoot (ψ²) n` hypothesis with `ψ = 1753`, `n = 256`) and
    `n_ne_zero_8380417 : (256 : ZMod 8380417) ≠ 0`.  The residual is
    a single concrete leaf-bytes KAT at the ML-DSA `Z_8380417[X]/(X²⁵⁶+1)`
    kernel — the negacyclic compiler leaf the cyclic seam could not close. -/
theorem mldsa_nttNegaEmitRealizes_of_kernel
    (decode : RustVal .TFp → (Fin 256 → ZMod 8380417)) (leafSpec : LeafSpec)
    (hker : NttNegaKernelRealizes (1753 : ZMod 8380417) decode
      "ntt_poly_mul_8380417_256" leafSpec) :
    NttNegaEmitRealizes (1753 : ZMod 8380417) decode
      "ntt_poly_mul_8380417_256" leafSpec :=
  nttNegaEmitRealizes_of_negaConv decode "ntt_poly_mul_8380417_256" leafSpec
    isPrimitiveRoot_1753sq_256 n_ne_zero_8380417 hker

end CatCrypt.Crypto.SecureCompilation.NegacyclicEmitRealization
