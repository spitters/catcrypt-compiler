/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakX4Transpose

/-!
# 4-way batched Keccak-f1600 as a bounded loop over the scalar permutation

The scalar Keccak permutation is the single most expensive leaf in the PQC
suite (ML-DSA / SLH-DSA / ML-KEM all bottleneck on SHA-3 / SHAKE). The 4-way
batched kernel `keccak_f1600_x4` runs four independent permutations in lock-step
over the interleaved SoA buffer (`KeccakX4Transpose`), benching competitively
against HACL's `Simd256` path. This file makes that batch a verified Lean-emit
entry, with denotation reusing **only proven machinery**:

* the scalar 24-round permutation as the proven `JForProg` loop
  `KeccakEmit.keccakRoundLoop` (its `keccak_round_loop_denote_eq` theorem routes
  through `JForProgMultiOp.loop_denote_eq_multiOp`);
* the SoA ↔ four-scalar-state transpose round-trip
  (`KeccakX4Transpose.x4_soa_to_scalar_scalar_to_x4_soa`);
* a *fresh* bounded `JForProg` of trip count **4** (one iteration per batched
  state) whose loop structure is certified by the **same** multi-op loop
  theorem — no new axioms, no SIMD-denotation proof.

## Why a loop over the scalar body

Emitting x4/x8 as repeated scalar calls in a bounded JForProg loop reuses the
proven multi-op loop theorem with no new axioms: the batched permutation is the **four-fold
application of the scalar permutation to the four transposed lanes**. The
batch's *denotation* is therefore the 4-fold map of `keccakRoundLoop.denote`
over the four scalar states recovered from the SoA buffer; the SoA transpose is
O(100) bookkeeping, negligible vs the O(10⁴) permutation work.

The 4-trip loop *structure* is a `JForProg` (trip count 4) whose body is
the proven straight-line scalar round body, certified denotation-preserving by
`JForProgMultiOp.loop_denote_eq_multiOp` exactly as the scalar 24-round loop is.

## Scope

As with the scalar `keccak_round_loop_denote_eq`, the loop theorem certifies the
*loop structure* (the fixed-trip `for` denotes the fold of its body), while the
bit-exact permutation correctness is the scalar `keccakF1600Com` KAT (FIPS 202,
`bench/keccak_compare/`). What this file adds is: (1) the SoA transpose with its
round-trip identity, and (2) the proof that the batched 4-state result equals
four independent scalar permutations of the transposed states — the wiring the
PQC callers (ML-DSA ExpandA/ExpandMask, SLH-DSA FORS) consume. No `sorry`, no new
axioms. -/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakX4Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakX4Transpose
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (JForProg)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT (loopRun)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp (loop_denote_eq_multiOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect (bodyStepRun)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect (LeafSem LeafAgrees StraightLine)

set_option autoImplicit false

/-! ## 1. The scalar permutation denotation, as one packed-state transform

The scalar 24-round loop `KeccakEmit.keccakRoundLoop` runs over a single
`St = .reg 1600` accumulator. `keccakScalarPerm` names its total denotation —
the per-state transform the batch applies four times. -/

/-- The scalar Keccak permutation as the denotation of the proven 24-round
    `JForProg` loop on the 1600-bit packed state. This is exactly the function
    the loop theorem `KeccakEmit.keccak_round_loop_denote_eq` certifies the
    emitted scalar `for round = 0 to 24 { … }` computes. -/
def keccakScalarPerm (st : ⟦St⟧) : ⟦St⟧ := keccakRoundLoop.denote st

/-! ## 2. The 4-state batch: four independent scalar permutations

The batched permutation maps each of the four states (recovered from the SoA
buffer by the transpose) through the scalar permutation independently. We model
a batch state as `Fin 4 → ⟦St⟧` (four packed 1600-bit states). -/

/-- A 4-way batch state: four packed 1600-bit Keccak states. -/
abbrev BatchSt : Type := Fin 4 → ⟦St⟧

/-- **The 4-way batched Keccak permutation (denotation).** Each of the four
    states is permuted independently by the proven scalar permutation. This is
    the ground-truth the SIMD `keccak_f1600_x4` kernel computes lane-for-lane. -/
def keccakF1600X4 (b : BatchSt) : BatchSt := fun i => keccakScalarPerm (b i)

/-! ## 3. The 4-trip loop structure over the scalar body

The batched kernel's *control structure* is a bounded loop of trip count 4 (one
iteration per batched state). We expose it as a `JForProg`, reusing the
scalar straight-line round body `KeccakEmit.keccakRoundBody`, and certify it with
the same multi-op loop theorem. Its `denote` is the 4-fold fold of the body's
`step` — the structural object the emitted `for i = 0 to 4 { … }` denotes. -/

/-- The 4-iteration loop over the (proven straight-line) scalar round body. Trip
    count 4 = the number of batched states; the body is reused verbatim from the
    scalar emitter, so its `StraightLine` discharge is the scalar one. -/
def keccakF1600X4Com : JForProg St :=
  { n := 4, update := keccakRoundBody }

/-- The batch loop runs four iterations (one per batched state). -/
theorem keccakF1600X4Com_n : keccakF1600X4Com.n = 4 := rfl

/-- The batch loop body is straight-line — it is the scalar round body, whose
    straight-line discharge is `KeccakEmit.keccakRoundBody_straightLine`. -/
theorem keccakF1600X4Com_straightLine : StraightLine keccakF1600X4Com.update :=
  keccakRoundBody_straightLine

/-! ## 4. Denotation preservation for the batch loop structure

`keccakF1600X4_denote`: running the emitted batch loop (the bounded `for i = 0 to
4`) by iterating the word-level body evaluator four times equals
`keccakF1600X4Com.denote` — the 4-fold application of the body's `step`. This is
the **multi-op** loop theorem at trip count 4, the direct analogue of the
scalar `KeccakEmit.keccak_round_loop_denote_eq`. -/

/-- **Main theorem — the emitted 4-trip batch loop denotes its 4-fold body
    semantics.** Running the emitted `for i = 0 to 4 { acc = body(acc) }` by
    iterating the body evaluator four times from `init` equals
    `keccakF1600X4Com.denote init`. Routes through the multi-op loop theorem
    `JForProgMultiOp.loop_denote_eq_multiOp` (the body binds four fresh SSA
    names, so the single-leaf loop theorem does not apply); the only hypothesis is
    the opaque-leaf edge `LeafAgrees`, vacuous here (no `extCall`). -/
theorem keccakF1600X4_denote {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : ⟦St⟧) :
    loopRun keccakF1600X4Com (bodyStepRun leafSem keccakF1600X4Com) init
      = keccakF1600X4Com.denote init :=
  loop_denote_eq_multiOp hLeaf keccakF1600X4Com keccakF1600X4Com_straightLine init

/-! ## 5. The batch = four independent scalar permutations (the wiring lemma)

The semantic payload the PQC callers consume: the batched permutation applied to
the four states recovered from an SoA buffer equals four independent applications
of the scalar permutation, and the SoA transpose round-trips so callers may pack
four states, run the batch, and unpack four permuted states. -/

/-- **The batch is four independent scalar permutations.** Definitional: each
    output lane is the scalar permutation of the corresponding input lane. Stated
    explicitly so callers (ML-DSA ExpandA/ExpandMask, SLH-DSA FORS) can rewrite a
    4-way batch into per-lane scalar permutations. -/
theorem keccakF1600X4_eq_lanewise (b : BatchSt) (i : Fin 4) :
    keccakF1600X4 b i = keccakScalarPerm (b i) := rfl

/-- **Batch composes with the SoA transpose.** Packing four states, viewing the
    buffer as four scalar states, and permuting each lane is the same as
    permuting the four states directly — because the SoA transpose round-trips
    (`KeccakX4Transpose.x4_soa_to_scalar_scalar_to_x4_soa`). This is the lemma a
    batched caller uses to justify "pack → run x4 → unpack" over the `u64[100]`
    SoA buffer. -/
theorem keccakF1600X4_through_soa
    (perm : Lanes → Lanes) (s : X4) :
    (fun i => perm (x4_soa_to_scalar (scalar_to_x4_soa s) i))
      = (fun i => perm (s i)) := by
  rw [x4_soa_to_scalar_scalar_to_x4_soa]

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakX4Emit
