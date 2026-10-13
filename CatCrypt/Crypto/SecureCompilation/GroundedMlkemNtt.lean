/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer

/-!
# The `nttMul 256 17` leaf realizer over `ZMod 3329`, and a `k`-step chain of it

This module packages the realization theorem of `ConcreteNttRealizer` for the
concrete realizer `LeafSpec` at `q = 3329`, `n = 256`, `ω = 17`, and iterates it
over a list of operands.  The object realized is `nttMul 256 17` over
`ZMod 3329`, which equals `cyclicConv 256`, multiplication in
`Z_3329[X]/(X^256 − 1)`.  Two proved facts compose:

* the two-bytes-per-coefficient little-endian `.TPolyMod 3329 256` codec has the
  round-trip `decodeP_encodeP` for every input (`q = 3329 < 2¹⁶`), so the leaf
  realizer computes the cyclic convolution
  (`ConcreteNttRealizer.nttKernelRealizesP_concrete`), and
* `nttMul 256 17 = cyclicConv 256` at the primitive root `17`
  (`NTTMultiplyCorrectGeneric.nttMul_eq_cyclicConv'`, discharged by
  `isPrimitiveRoot_17_256` + `n_ne_zero_3329`).

Their composition is `ConcreteNttRealizer.mlkem_nttEmitRealizes_concrete`; the
theorems here have no `NttKernelRealizes` or KAT hypothesis:

* `mlkem_ntt_grounded` — `NttEmitRealizesP 3329 256 17 …` for the concrete
  realizer `LeafSpec`.
* `mlkem_ntt_computes_cyclicConv` — the decoded leaf value equals
  `cyclicConv 256` of the decoded operands (via `nttMul_eq_cyclicConv'`).
* `grounded_mlkem_matvec_realizes` — a `k`-step left fold of the leaf call
  decodes to the `k`-step left fold of `cyclicConv 256`, assembled from `k`
  copies of `mlkem_ntt_computes_cyclicConv`.

## What these objects are not

`nttMul 256 17` is the length-256 cyclic convolution, i.e. multiplication in
`Z_3329[X]/(X^256 − 1)`.  It is not FIPS 203's ML-KEM transform: ML-KEM's NTT is
the incomplete 7-layer transform of `Z_3329[X]/(X^256 + 1)` into 128 quadratic
residues, and no full negacyclic diagonalisation exists at this modulus because
`3328 = 2^8 · 13` gives `ZMod 3329` no element of order 512
(`ConcreteNttInstances.lean`, "ML-KEM is cyclic here, not negacyclic").  The
jasmin leaf named `ntt_poly_mul_3329_256` in
`bench/mlkem_compare/include/leaves.jinc` is formosa-mlkem's `_poly_basemul`,
an NTT-domain pointwise multiply on already-transformed data, which is a third
function.  The owned ML-KEM NTT that passes the NIST KAT is a separate artifact
and is not described by this module.

## Scope

The theorems here assume nothing beyond the imports and add no admitted proof or
`axiom`.  They say nothing about emitted machine bytes: no theorem here relates
the realizer `LeafSpec` to the bytes of any kernel.

## References
* NIST FIPS 203 (ML-KEM).  Its transform is the incomplete 7-layer NTT of
  `X^256 + 1`, which differs from the cyclic convolution realized here as
  described above.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Lattice.ConcreteNttRoots

/-! ## §1  The single-leaf `nttMul 256 17` realization

`mlkem_nttEmitRealizes_concrete` (in `ConcreteNttRealizer`) states that the
concrete realizer `cyclicConvLeafSpecP 3329 256 …` decodes its leaf-call value
to `nttMul 256 17 …` for every input, with no KAT and no abstract
`decode ∘ encode = id` assumption.  This section re-exports it under the name
`mlkem_ntt_grounded` and names the two data it is stated over (the decoder and
the realizer `LeafSpec`) so the statements below share them. -/

/-- The decoder of the `.TPolyMod 3329 256` byte codec, with the width equality
    `(.TPolyMod 3329 256).storageBytes = 256 * coeffBytes` discharged by `rfl`. -/
def mlkemDecode : RustVal (.TPolyMod 3329 256) → (Fin 256 → ZMod 3329) :=
  decodeTPoly (q := 3329) (n := 256) (by rfl)

/-- The cyclic-convolution realizer `LeafSpec` at `q = 3329`, `n = 256`, wired to
    the round-trip-verified codec at the leaf name `"ntt_poly_mul_3329_256"`.
    The leaf name is a string key of the `LeafSpec`; it does not tie this
    realizer to the jasmin function of the same name, which is formosa-mlkem's
    `_poly_basemul` (see the module docstring). -/
def mlkemNttLeafSpec (limbStore : LimbStoreSpec) : LeafSpec :=
  cyclicConvLeafSpecP (q := 3329) (n := 256) (by rfl)
    "ntt_poly_mul_3329_256" limbStore

/-- The realizer `mlkemNttLeafSpec` decodes its leaf-call value to
    `nttMul 256 17 …` over `ZMod 3329` for every input.  There is no
    `NttKernelRealizes` or KAT hypothesis and no abstract `decode ∘ encode = id`
    assumption: the byte-level decode-equals-convolution fact is the round-trip
    `decodeP_encodeP`, and `nttMul = cyclicConv` at the primitive root `17` is
    `nttMul_eq_cyclicConv'` via the commuting square.

    `nttMul 256 17` is the cyclic convolution of `X^256 − 1`, not FIPS 203's
    transform of `X^256 + 1`.  No statement about emitted machine bytes is made
    here. -/
theorem mlkem_ntt_grounded (limbStore : LimbStoreSpec) :
    NttEmitRealizesP 3329 256 (17 : ZMod 3329)
      mlkemDecode "ntt_poly_mul_3329_256" (mlkemNttLeafSpec limbStore) :=
  mlkem_nttEmitRealizes_concrete limbStore

/-- The decoded leaf value of `mlkemNttLeafSpec` equals `cyclicConv 256` of the
    decoded operands: `mlkem_ntt_grounded` rewritten through
    `nttMul_eq_cyclicConv'` (primitive root `isPrimitiveRoot_17_256`,
    `n_ne_zero_3329`).  Holds for every input, with no kernel or KAT
    hypothesis. -/
theorem mlkem_ntt_computes_cyclicConv (limbStore : LimbStoreSpec)
    (aVal bVal oldDest : RustVal (.TPolyMod 3329 256)) :
    mlkemDecode
        ((mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
          (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
          [⟨.TPolyMod 3329 256, aVal⟩, ⟨.TPolyMod 3329 256, bVal⟩])
      = cyclicConv 256 (mlkemDecode aVal) (mlkemDecode bVal) := by
  rw [mlkem_ntt_grounded limbStore aVal bVal oldDest,
    nttMul_eq_cyclicConv' isPrimitiveRoot_17_256 n_ne_zero_3329]

/-! ## §2  A `k`-step chain of the leaf call

A `k`-step left fold of the `mlkemNttLeafSpec` leaf call, each step multiplying
a running operand against the next list entry.  Every step is
`mlkem_ntt_computes_cyclicConv`, so the fold decodes to the iterated
`cyclicConv 256` with no kernel or KAT hypothesis.  The iterated product is in
`Z_3329[X]/(X^256 − 1)`; it is not an ML-KEM matrix–vector product, whose
pointwise multiplies act in the NTT domain of `X^256 + 1`.

The statement is at the value level (as `GroundedFieldProtocol`'s Horner step
is), since the leaf call is binary over the `.TPolyMod` carrier while the
`pipeN` template of `ProtocolEmitRealizes` is unary over the `.TFp` carrier. -/

/-- The value of a `k`-step chain of the leaf call: fold the entries
    `bs : List (RustVal (.TPolyMod 3329 256))` left-to-right, each step
    multiplying the running accumulator against the next entry via the
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

/-- The abstract value of the `k`-step chain: fold `cyclicConv 256` against the
    decoded entries, left-to-right. -/
def matvecChainSpec (bs : List (RustVal (.TPolyMod 3329 256))) (acc0 : Fin 256 → ZMod 3329) :
    Fin 256 → ZMod 3329 :=
  bs.foldl (fun acc b => cyclicConv 256 acc (mlkemDecode b)) acc0

/-- A `k`-step chain of the `mlkemNttLeafSpec` leaf call decodes to the
    iterated `cyclicConv 256` of the decoded operands.  Every step is
    `mlkem_ntt_computes_cyclicConv`, so the chain has no kernel or KAT
    hypothesis.  The chain multiplies in `Z_3329[X]/(X^256 − 1)` and makes no
    statement about emitted machine bytes. -/
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
