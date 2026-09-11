/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PolyRewrites
public import CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic

/-!
# Poly-dialect ML-KEM NTT migration tie (#482-4, step 4 — additive)

Connects the new **Poly Veir-dialect** NTT multiply (`PolyDialect.nttMul`,
denoting the abstract polynomial-ring product via CompPoly's `realNttMul`) to the
**verified emitted ML-KEM-style NTT program** of `LatticeNTTSemantic`
(`realSrcCom` / `realTgtCom` — the one-multiply program and its expanded
`invntt (basemul (ntt a) (ntt b))` bracket over the *real* CompPoly NTT
operations, the form whose negacyclic-product soundness
`realSrcCom_negacyclic_coeff` is proved against CompPoly's
`fastMulImpl_eq_mul` + the negacyclic fold).

This is the **first NTT emitter migrated onto the Poly dialect**, additively:
neither `PolyDialect.lean` nor `LatticeNTTSemantic.lean` is modified.  The bridge
is the observation that both the emitter's `realLatticeDialect.polyMulC` /
`basemul` and the Poly dialect's `nttMul` op denote to the **same**
`realNttMul (D q) a b` — so the dialect's `nttMul` is backed by the same verified
CompPoly NTT round-trip the emitter's negacyclic KAT validates, with no new opaque
poly leaf and no broken proof.

## The one-tie-per-level payoff

The plan's headline (`docs/dialect-restructure-plan.md` §"Verification payoff"):
the realization ties connect **once per dialect level** (structural) instead of
per-protocol.  Here that is concrete:

* the **field** leaves tie once at L3 (`FieldDialect`);
* the **NTT / polynomial ring** ties once at L4′ (this file):
  `nttMul_matches_emitter` is the single structural tie connecting the verified
  emitted ML-KEM NTT-mul program to the dialect's abstract NTT op.  Every
  NTT-using protocol (ML-KEM, ML-DSA, Plonky3, FAEST) inherits the negacyclic
  convolution correctness without re-proving the transform.

## What this lands

* `emitterMatchesNttMul` — the emitter's `realLatticeDialect.polyMulC`
  denotation equals the Poly dialect's `nttMul` denotation (both are
  `realNttMul (ND.dom q)`), the **structural migration bridge**.
* `nttMul_matches_emitter_src` / `_tgt` — the **migration headline**: the emitted
  ML-KEM NTT-mul program (`realSrcCom` / its NTT-expanded `realTgtCom`), on the
  encoded inputs, denotes to the **same** value as the Poly dialect's `nttMul`
  op, and (via `PolyDialect.nttMul_negacyclic_coeff`) that value's negacyclic
  reduction is the genuine negacyclic convolution.

## Deferred (the continuation, #482-5)

The Plonky3 NTT (`Plonky3NttLayerEmit` / `Plonky3NttButterflyEmit`) and the
ML-DSA 4-way batched NTT (`LatticeNttEmit` / `MldsaNtt4WayVec`) emitted-kernel
ties, and the `Com polyDialect` lowering-out to `jasminDialect`, are deferred:
the Poly dialect already *denotes* the full negacyclic ring product
(`PolyDialect.lean`) and the same structural `realNttMul`-bridge lifts each
emitter onto it.  Only the ML-KEM `nttMul` tie is landed here as the
proof-of-concept of the one-tie-per-level structure (mirroring the BN254 `padd`
proof-of-concept of the EllipticCurve migration).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic
open CompPoly.CPolynomial.NTT (Domain)
open CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic (negaPoly)
open CompPoly (CPolynomial)
open Polynomial

variable {q n : Nat} [ND : NttDomains]

/-! ## 1. The structural migration bridge

Both the emitter's `realLatticeDialect.polyMulC` op and the Poly dialect's
`nttMul` op denote, for a prime modulus, to the **same** `realNttMul (ND.dom q)`.
This is the structural bridge: the dialect's abstract NTT op *is* the emitter's
verified NTT round-trip. -/

/-- **Migration bridge.** For a prime modulus, the emitter's coefficient-form
    NTT multiply (`realLatticeDialect.polyMulC`, the source op of `realSrcCom`)
    and the Poly dialect's `nttMul` op denote to the *same* value —
    `realNttMul (ND.dom q) a b`.  The dialect op is backed by the emitter's
    verified CompPoly NTT round-trip. -/
theorem emitterMatchesNttMul [Fact (Nat.Prime q)] (a b : CPolynomial (ZMod q)) :
    LatticeNTTSemantic.realLatticeDenote.denote (.polyMulC q n)
        (.cons a (.cons b .nil))
      = polyDenote.denote (.nttMul q n) (.cons a (.cons b .nil)) := by
  rw [nttMul_denote (q := q) (n := n) a b]
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩; realNttMul (ND.dom q) a b)
        else (0 : CPolynomial (ZMod q))) = realNttMul (ND.dom q) a b
  rw [dif_pos (Fact.out : Nat.Prime q)]

/-! ## 2. The migration headline (source + NTT-expanded target)

The emitted ML-KEM NTT-mul program denotes to the Poly dialect's `nttMul` op,
and inherits the dialect's negacyclic tie. -/

/-- **ML-KEM NTT migration headline (source program).** The emitted one-multiply
    program `realSrcCom` (the emitter's coefficient-form NTT multiply), on the
    encoded inputs `enc a`, `enc b`, denotes to the **same** value as the Poly
    dialect's `nttMul` op.  This is the single one-tie-per-level structural tie:
    the verified emitted ML-KEM NTT-mul is connected to the dialect's abstract
    NTT op. -/
theorem nttMul_matches_emitter_src [Fact (Nat.Prime q)]
    (a b : Fin n → BitVec 16) :
    (realSrcCom q n).denote (.cons (enc q n a) (.cons (enc q n b) .nil))
      = polyDenote.denote (.nttMul q n)
          (.cons (enc q n a) (.cons (enc q n b) .nil)) := by
  rw [realSrcCom_denote q n (enc q n a) (enc q n b),
    nttMul_denote (q := q) (n := n) (enc q n a) (enc q n b)]

/-- **ML-KEM NTT migration headline (NTT-expanded target).** The emitted
    NTT-expanded bracket `invntt (basemul (ntt a) (ntt b))` (`realTgtCom`),
    on the encoded inputs, denotes to the same value as the Poly dialect's
    `nttMul` op — the dialect op is backed by the verified NTT round-trip in its
    expanded butterfly form. -/
theorem nttMul_matches_emitter_tgt [Fact (Nat.Prime q)]
    (a b : Fin n → BitVec 16) :
    (realTgtCom q n).denote (.cons (enc q n a) (.cons (enc q n b) .nil))
      = polyDenote.denote (.nttMul q n)
          (.cons (enc q n a) (.cons (enc q n b) .nil)) := by
  rw [realTgtCom_denote q n (enc q n a) (enc q n b),
    nttMul_denote (q := q) (n := n) (enc q n a) (enc q n b)]

/-- **Negacyclic correctness inherited through the migration.** The emitted
    ML-KEM NTT-mul program, transported onto the Poly dialect's `nttMul` op, has
    the genuine negacyclic-convolution `k`-th coefficient (`k < n`) — combining
    the migration bridge (`nttMul_matches_emitter_src`) with the dialect's
    once-per-dialect negacyclic tie (`nttMul_negacyclic_coeff`).  This is the
    payoff: the protocol's emitted NTT inherits the convolution correctness from
    the dialect, not re-proved per protocol. -/
theorem emitter_negacyclic_via_dialect [Fact (Nat.Prime q)]
    (hD : 2 * n ≤ (ND.dom q).n) (hn : 0 < n)
    (a b : Fin n → BitVec 16) {k : Nat} (hk : k < n) :
    (((realSrcCom q n).denote
          (.cons (enc q n a) (.cons (enc q n b) .nil))).toPoly %ₘ negaPoly n).coeff k
      = (∑ ij ∈ Finset.antidiagonal k,
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2)
        - (∑ ij ∈ Finset.antidiagonal (k + n),
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2) := by
  rw [nttMul_matches_emitter_src (q := q) (n := n) a b]
  exact nttMul_negacyclic_coeff (q := q) (n := n) hD hn a b hk

/-! ## 3. Smoke test: the bridge is reflexive on a concrete prime

The migration bridge for ML-KEM-768's `q = 3329` is the dialect/emitter
denotation equality — instantiated structurally. -/

example [Fact (Nat.Prime 3329)] (a b : CPolynomial (ZMod 3329)) :
    LatticeNTTSemantic.realLatticeDenote.denote (.polyMulC 3329 256)
        (.cons a (.cons b .nil))
      = polyDenote.denote (.nttMul 3329 256) (.cons a (.cons b .nil)) :=
  emitterMatchesNttMul a b

end CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
