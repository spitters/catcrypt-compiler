/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer

/-!
# A fully-grounded ML-KEM NTT-multiply — the realization is a THEOREM, not a KAT

The ML-KEM NTT-multiply is the lattice-crypto core kernel.  Its emit→value
realization is, here, an **unconditional Lean theorem** — not a hypothesised
leaf-bytes KAT.  Two facts make it so, and both are proved (no hypotheses):

* the concrete two-bytes-per-coefficient little-endian `.TPolyMod 3329 256`
  codec has a proved round-trip `decodeP_encodeP` valid for **every** input
  (`q = 3329 < 2¹⁶`), so the leaf realizer provably computes the cyclic
  convolution (`ConcreteNttRealizer.nttKernelRealizesP_concrete`), and
* `nttMul 256 17 = cyclicConv 256` unconditionally at the proven primitive root
  (`NTTMultiplyCorrectGeneric.nttMul_eq_cyclicConv'`, discharged by
  `isPrimitiveRoot_17_256` + `n_ne_zero_3329`).

Composing them (`ConcreteNttRealizer.mlkem_nttEmitRealizes_concrete`) gives the
full NTT-multiply realization with **ZERO** `NttKernelRealizes`/KAT hypotheses.

This module is the clean grounded packaging of that already-unconditional
realizer:

* `mlkem_ntt_grounded` — the single-kernel headline: `NttEmitRealizesP 3329 256
  17 …` holds for the concrete realizer `LeafSpec`, no assumed hypothesis.
* `mlkem_ntt_computes_cyclicConv` — the corollary tying the decoded leaf value to
  `cyclicConv 256` directly (via `nttMul_eq_cyclicConv'`), again no hypothesis.
* `grounded_mlkem_matvec_realizes` — a `k`-step pipeline of pointwise ML-KEM
  NTT-multiplies (the shape of an ML-KEM matrix–vector product, `k²` pointwise
  NTT-mults) whose every step is the proved realization — assembled from `k`
  copies of `mlkem_ntt_grounded` with **no** kernel hypotheses.

## HONEST scope

The ML-KEM realizer is already unconditional; this file does not re-assume a
KAT, and adds no `sorry`/`axiom`.  The single residual is the **owned
machine-code** obligation — that the jasmin-emitted bytes of the real
`ntt_poly_mul_3329_256` kernel equal this realizer `LeafSpec`.  That is the
owned-machine-code route (addressed structurally by the `NttLoopRealized` owned
realization), *not* a per-kernel hypothesis of any theorem here.

## References
* NIST FIPS 203 (ML-KEM)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots

/-! ## §1  The grounded single-kernel ML-KEM NTT-multiply realization

`mlkem_nttEmitRealizes_concrete` (in `ConcreteNttRealizer`) is the unconditional
realization: the concrete realizer `cyclicConvLeafSpecP 3329 256 …` decodes its
leaf-call value to `nttMul 256 17 …` for **every** input, with no KAT and no
abstract `decode ∘ encode = id` assumption.  We re-export it under a clean name —
the headline of this file — and pin the two grounded data (the decoder and the
realizer `LeafSpec`) so downstream statements share them. -/

/-- The grounded ML-KEM decoder: the concrete `.TPolyMod 3329 256` byte codec's
    decode, with the width equality `(.TPolyMod 3329 256).storageBytes =
    256 * coeffBytes` discharged by `rfl`. -/
def mlkemDecode : RustVal (.TPolyMod 3329 256) → (Fin 256 → ZMod 3329) :=
  decodeTPoly (q := 3329) (n := 256) (by rfl)

/-- The grounded ML-KEM NTT-multiply realizer `LeafSpec`, wired to the concrete
    round-trip-verified codec at the leaf `"ntt_poly_mul_3329_256"`. -/
def mlkemNttLeafSpec (limbStore : LimbStoreSpec) : LeafSpec :=
  cyclicConvLeafSpecP (q := 3329) (n := 256) (by rfl)
    "ntt_poly_mul_3329_256" limbStore

/-- **GROUNDED ML-KEM NTT-multiply realization — UNCONDITIONAL (no KAT).**

    The concrete realizer `mlkemNttLeafSpec` decodes its leaf-call value to
    `nttMul 256 17 …` for **every** input.  No `NttKernelRealizes`/KAT hypothesis
    and no abstract `decode ∘ encode = id` assumption: the byte-level
    decode-equals-convolution fact is the proved round-trip `decodeP_encodeP`,
    and `nttMul = cyclicConv` at the proven primitive root `17` is supplied by
    `nttMul_eq_cyclicConv'` via the commuting square.  The lattice-crypto core
    kernel, realized with nothing assumed.

    Residual = owned machine-code only: that the jasmin-emitted bytes of the real
    `ntt_poly_mul_3329_256` kernel equal `mlkemNttLeafSpec` (the owned route,
    addressed structurally by `NttLoopRealized`) — *not* a hypothesis here. -/
theorem mlkem_ntt_grounded (limbStore : LimbStoreSpec) :
    NttEmitRealizesP 3329 256 (17 : ZMod 3329)
      mlkemDecode "ntt_poly_mul_3329_256" (mlkemNttLeafSpec limbStore) :=
  mlkem_nttEmitRealizes_concrete limbStore

/-- **Corollary: the decoded leaf value IS the cyclic convolution.**  Rewriting
    the headline `nttMul 256 17 …` through the unconditional
    `nttMul_eq_cyclicConv'` (proven primitive root `isPrimitiveRoot_17_256`,
    `n_ne_zero_3329`) ties the decoded ML-KEM NTT-multiply leaf value directly to
    `cyclicConv 256` — for every input, with no kernel/KAT hypothesis. -/
theorem mlkem_ntt_computes_cyclicConv (limbStore : LimbStoreSpec)
    (aVal bVal oldDest : RustVal (.TPolyMod 3329 256)) :
    mlkemDecode
        ((mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
          (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
          [⟨.TPolyMod 3329 256, aVal⟩, ⟨.TPolyMod 3329 256, bVal⟩])
      = cyclicConv 256 (mlkemDecode aVal) (mlkemDecode bVal) := by
  rw [mlkem_ntt_grounded limbStore aVal bVal oldDest,
    nttMul_eq_cyclicConv' isPrimitiveRoot_17_256 n_ne_zero_3329]

/-! ## §2  A grounded `k`-step pipeline — the ML-KEM matrix–vector product shape

An ML-KEM matrix–vector product `A · s` over `R_q^{k×k}` is, in the NTT domain,
`k²` pointwise NTT-multiplies (plus accumulation).  Here we ground the
*pointwise-multiply backbone*: a `k`-step list of ML-KEM NTT-multiplies, each
multiplying a running operand against the next column entry.  Every step is the
proved `mlkem_ntt_computes_cyclicConv` — so the whole `k`-step pipeline decodes
to the iterated cyclic convolution with **ZERO** kernel/KAT hypotheses.

We work directly at the value level (as `GroundedFieldProtocol`'s Horner step
does), since the NTT-multiply is *binary* over the `.TPolyMod` carrier (the
unary `pipeN` template of `ProtocolEmitRealizes` is `.TFp`-carrier and unary). -/

/-- The value of a `k`-step chain of ML-KEM NTT-multiplies: fold the column
    entries `bs : List (RustVal (.TPolyMod 3329 256))` left-to-right, each step
    multiplying the running accumulator against the next entry via the grounded
    `mlkemNttLeafSpec` leaf. -/
def matvecChainValue (limbStore : LimbStoreSpec) (oldDest : RustVal (.TPolyMod 3329 256))
    (bs : List (RustVal (.TPolyMod 3329 256))) (acc0 : RustVal (.TPolyMod 3329 256)) :
    RustVal (.TPolyMod 3329 256) :=
  bs.foldl
    (fun acc b =>
      (mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, acc⟩, ⟨.TPolyMod 3329 256, b⟩])
    acc0

/-- The matching abstract spec of the `k`-step chain: fold `cyclicConv 256`
    against the decoded column entries, left-to-right. -/
def matvecChainSpec (bs : List (RustVal (.TPolyMod 3329 256))) (acc0 : Fin 256 → ZMod 3329) :
    Fin 256 → ZMod 3329 :=
  bs.foldl (fun acc b => cyclicConv 256 acc (mlkemDecode b)) acc0

/-- **GROUNDED ML-KEM matrix–vector NTT-multiply chain — ZERO kernel hypotheses.**

    A `k`-step pipeline of ML-KEM NTT-multiplies (the pointwise backbone of an
    ML-KEM matrix–vector product, `k` pointwise multiplies per row) decodes to the
    iterated cyclic convolution of the decoded operands.  Every step is the proved
    `mlkem_ntt_computes_cyclicConv` — itself the unconditional grounded
    realization, no KAT and no abstract section.  The whole chain therefore
    assumes **nothing** about its kernels.

    Residual = owned machine-code only (the emitted `ntt_poly_mul_3329_256` bytes
    equal `mlkemNttLeafSpec`), not a per-kernel hypothesis. -/
theorem grounded_mlkem_matvec_realizes (limbStore : LimbStoreSpec)
    (oldDest : RustVal (.TPolyMod 3329 256))
    (bs : List (RustVal (.TPolyMod 3329 256))) (acc0 : RustVal (.TPolyMod 3329 256)) :
    mlkemDecode (matvecChainValue limbStore oldDest bs acc0)
      = matvecChainSpec bs (mlkemDecode acc0) := by
  unfold matvecChainValue matvecChainSpec
  induction bs generalizing acc0 with
  | nil => simp
  | cons b restB ih =>
      simp only [List.foldl_cons]
      rw [ih ((mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, acc0⟩, ⟨.TPolyMod 3329 256, b⟩])]
      rw [mlkem_ntt_computes_cyclicConv limbStore acc0 b oldDest]

end CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt
