/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types

/-!
# The PACKED run-output read-back: splicing the dialect chain into the SIMD lane domain

## Scope

`RunOutputReadback.lean` read **one scalar slot** `i : Fin n` out of the dialect
chain's structured run-output `Fin n → BitVec 16` (`runOutputToWords`) and spliced
that single word through one *scalar* x86 `ADD` (`slot_runOutput_x86Add_eq`,
`RelatedBinOp id (·+·) x86Add`, a scalar-binary ALU op). Its `Scope` named the
residual precisely: turning the **whole** `Fin n → BitVec 16` run-output into the
operand model of a **vector / multi-result** SIMD step needs (a) a *packed*
read-back of the entire array into a lane bundle, and (b) a **vector** preservation
lemma, because `RelatedBinOp` is scalar-binary. This file **builds that packed
read-back** and **proves the vector splice** — extending the read-back+splice from
one scalar slot to the per-lane SIMD case.

The two value models, made precise:

* the dialect chain (`CompilerLoweringRegistry.registryChain_threePass'`, reused via
  `RunOutputReadback.runOutputToWords_chain_eq`) ends at a structured stack-array
  run-output of Lean type `⟦.stackArr 16 n⟧ = (Fin n → BitVec 16)`, equal by the
  chain to `transTy ((srcCom q n).denote V)` — the lowered ML-KEM NTT-mul result;
* the SIMD lane op (`LaneMap.vmap₂`, the per-lane binary lane-map, with the
  `MLIR.VectorDialect.VectorTy.map₂` form the AVX-512/AVX2 register model
  `Avx512Model`/`Avx512DwordModel` uses for every `vpadd*` mnemonic) reads a
  **packed** `VectorTy (BitVec 16) n = (Fin n → BitVec 16)` lane bundle and applies
  a width-16 lane add `laneAddW` (`vpaddw`) to every lane in parallel.

`runOutputToVec` is the packed read-back: it maps the whole structured run-output to
the SIMD lane bundle the vector ALU consumes. Because the dialect's stack-array
run-output type `Fin n → BitVec 16` **is** the lane-function model `VectorTy
(BitVec 16) n` (`VectorTy α n := Fin n → α`, `@[reducible]`), the pack is the
natural identity-shaped marshal — exactly how the emitted SIMD kernel packs the
length-`n` coefficient array into vector registers (the SoA layout: lane `i` of the
packed register holds coefficient `i`).

The vector splice `vec_runOutput_vpaddw_eq` then composes the 3-pass dialect
chain (read back **as a whole array** via `runOutputToVec`) with the per-lane
`vpaddw` SIMD step: the packed run-output of the *source* dialect program, fed to the
SIMD lane add against a second packed operand `b`, equals — **at every lane `i`** —
the abstract sum of the source program's `i`-th coefficient and `b i`. This is the
vector analogue of `slot_runOutput_x86Add_eq`: its left factor is the full
`registryChain_threePass'` (via `runOutputToWords_chain_eq`, per slot) and its right
factor is the SIMD lane op, joined **through** the packed read-back across all lanes
at once.

### What is per-lane-covered vs cross-lane-remaining

The coverage is **per-lane**; the boundary is:

* **Covered (per-lane SIMD).** A `vpaddw` (16-bit packed add, `laneAddW`) over the
  `n` lanes of the packed run-output: lane `i` of the result is `out i + b i`,
  independently of every other lane. The splice realises the *whole* `n`-coefficient
  source result by the one SIMD instruction across all `n` lanes. The same shape
  covers any per-lane-independent binary lane op (`vpaddw`/`vpaddd`/`vpxord`/…): swap
  `laneAddW` for the lane op and the abstract `(·+·)` for its abstract operation —
  the structural per-lane argument (`LaneMap.vmap₂_eq_scalar`) is identical.
  The op spliced here is **`vpaddw`** (width-16 packed add), over **`n` lanes** (the
  full coefficient array; e.g. `n = 256` for an ML-KEM degree-256 NTT polynomial,
  which an AVX-512 `vpaddw` covers 32 `u16` lanes at a time / a YMM `vpaddw` 16 at a
  time — this file's splice is lane-count-generic in `n`).

* **Remaining (cross-lane).** Operations whose output lane `i` depends on input lanes
  `j ≠ i` — **shuffles / permutes / broadcasts / horizontal reductions**
  (`VPSHUFB`, `VPERMD`, `VPBROADCAST`, the NTT bit-reversal/butterfly cross-lane
  routing, horizontal `hsum`) — are **NOT** per-lane and are **NOT** covered here.
  Those need the lane-permutation modelling (`VectorTy.shuffle`, `LaneMap.laneMapIdx`
  for index-dependent ops, or `VectorReduce` for horizontal folds), not this
  per-lane splice. This file does **not** claim cross-lane SIMD coverage.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PackedRunOutputReadback

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry
open CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The packed read-back: whole stack-array run-output ↦ SIMD lane bundle

The dialect chain's run-output has type `⟦.stackArr 16 n⟧ = (Fin n → BitVec 16)`.
A packed SIMD register holding the coefficient array is a `VectorTy (BitVec 16) n`
lane bundle (`= Fin n → BitVec 16`, the lane-function model `VectorTy α n := Fin n
→ α`). The packed read-back marshals the **whole** array into that lane bundle —
the SoA pack the emitted SIMD kernel performs (coefficient `i` ↦ lane `i`). -/

/-- **The packed run-output read-back (SIMD lane bundle).** Marshal the *whole*
    structured stack-array run-output `out : Fin n → BitVec 16` into the SIMD lane
    bundle `VectorTy (BitVec 16) n` the packed vector ALU consumes — coefficient `i`
    into lane `i`. Because the run-output type and the lane-function model coincide
    (`VectorTy α n := Fin n → α`), this is the natural identity-shaped pack; it
    mirrors how the emitted SIMD kernel packs the length-`n` coefficient array into
    vector registers (SoA layout). The whole-array (vector) analogue of the scalar
    `RunOutputReadback.runOutputToWords` (which read one slot). -/
def runOutputToVec {n : Nat} (out : Fin n → BitVec 16) : VectorTy (BitVec 16) n :=
  out

/-- The packed read-back recovers the scalar slot read-back at every lane: lane `i`
    of `runOutputToVec out` is exactly `runOutputToWords out i`. The packed pack
    is the scalar slot read-back done at all lanes simultaneously, not a
    different marshal. -/
theorem runOutputToVec_lane {n : Nat} (out : Fin n → BitVec 16) (i : Fin n) :
    (runOutputToVec out) i = runOutputToWords out i := rfl

/-! ## 2. The width-16 SIMD lane add (`vpaddw`)

`Avx512Model`/`Avx512DwordModel` model each `vpadd*` mnemonic as a
`VectorTy.map₂ laneAdd?` over its lane width (`laneAddQ = a + b` at 64,
`laneAddD = a + b` at 32; both `a + b` definitionally, per those models' docstrings —
the width-add ops match the Intel SDM pseudocode definitionally, so a "reference"
lemma is `rfl`). The dialect run-output is `BitVec 16`, so the matching SIMD op is
`VPADDW` (16-bit packed add); we record its lane op in the **same** definitional
`a + b` form, and the SIMD step as a `VectorTy.map₂` over the packed lanes — the
exact shape the register models use. -/

/-- **`VPADDW` lane op: wrapping 16-bit packed add** — the per-lane operation of
    `vpaddw`, in the same definitional `a + b` form `Avx512Model`'s `laneAddD`
    (`= a + b` at 32) and `laneAddQ` (`= a + b` at 64) take. Faithful to the Intel
    SDM `VPADDW` pseudocode definitionally (`laneAddW_eq` below is `rfl`), matching
    the convention that the trivial width-add lane ops need no separate reference
    lemma. -/
def laneAddW (a b : BitVec 16) : BitVec 16 := a + b

/-- `VPADDW` faithfulness (definitional): the 16-bit packed lane add is `BitVec 16`
    addition — the same `rfl`-form faithfulness `Avx512Model` records for `laneAddD`
    (`= a + b`) / `laneAddQ` (`= a + b`). -/
theorem laneAddW_eq (a b : BitVec 16) : laneAddW a b = a + b := rfl

/-- **The `vpaddw` SIMD step over a packed lane bundle.** One `VPADDW` applied to two
    packed `VectorTy (BitVec 16) n` operands is `VectorTy.map₂ laneAddW` — the exact
    `VectorTy.map₂ laneAdd?` shape `Avx512Model`/`Avx512DwordModel` use for every
    `vpadd*` (`step … (.vpaddd …) = s.setZ dst (VectorTy.map₂ laneAddD …)`). This is
    also `LaneMap.vmap₂ laneAddW` (the verified per-lane binary lane-map), so it
    inherits `LaneMap.vmap₂_eq_scalar`. -/
def vpaddw {n : Nat} (a b : VectorTy (BitVec 16) n) : VectorTy (BitVec 16) n :=
  VectorTy.map₂ laneAddW a b

/-- The `vpaddw` SIMD step **is** the verified per-lane binary lane-map
    `LaneMap.vmap₂ laneAddW`: both unfold to `fun i => laneAddW (a i) (b i)`. This
    ties the register-model `VectorTy.map₂` form to the `LaneMap` faithfulness layer,
    so the splice can quote `LaneMap.vmap₂_eq_scalar` directly. -/
theorem vpaddw_eq_vmap₂ {n : Nat} (a b : VectorTy (BitVec 16) n) :
    vpaddw a b = vmap₂ laneAddW a b := rfl

/-! ## 3. The vector splice: dialect chain (packed read-back) ∘ `vpaddw`

The genuine end-to-end vector statement. The left factor is the real 3-pass chain
`registryChain_threePass'` read back **as a whole array** via `runOutputToVec` (and,
per lane, via `RunOutputReadback.runOutputToWords_chain_eq`); the right factor is the
`vpaddw` per-lane SIMD step. They join through the packed read-back: every lane of the
packed run-output feeds one lane of the SIMD add. This is the vector analogue of
`RunOutputReadback.slot_runOutput_x86Add_eq` — the scalar slot splice is the per-lane
instance of this. -/

/-- **End-to-end vector splice through the packed read-back (`vpaddw`, `n` lanes).**

    Let `out` be the structured run-output of the emitted jasmin program
    (`runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)`) and
    `b : VectorTy (BitVec 16) n` a second packed operand. Then the emitted `VPADDW`
    instruction applied to the **packed read-back** `runOutputToVec out` and `b` is,
    **at every lane `i : Fin n`**, the abstract sum of (the `i`-th coefficient of the
    *source* dialect program's denotation) and `b i`:

        (vpaddw (runOutputToVec out) b) i
          = runOutputToVec (transTy ((srcCom q n).denote V)) i + b i.

    This is the end-to-end **vector** value-preservation: the *whole*
    source-dialect array result (`(srcCom q n).denote V`), packed into a SIMD lane
    bundle (`runOutputToVec`), realised by the emitted `vpaddw` instruction across
    **all `n` lanes**, equal lane-by-lane to the abstract per-lane op. Its left
    factor is the full 3-pass `registryChain_threePass'` (via
    `RunOutputReadback.runOutputToWords_chain_eq`, per lane) — **not** a
    representative `id/id` square — and its right factor is the per-lane SIMD add
    (`LaneMap.vmap₂_eq_scalar` faithfulness, width-16 `laneAddW`); the two are joined
    **through** `runOutputToVec` across every lane.

    **Coverage:** the SIMD op is `vpaddw` (16-bit packed add), over `n` lanes (the
    full coefficient array). It is **per-lane** — lane `i` depends only on input lane
    `i`. Cross-lane ops (shuffles/permutes/broadcasts/horizontal reductions) are NOT
    covered (see module `Scope`). -/
theorem vec_runOutput_vpaddw_eq (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n))
    (b : VectorTy (BitVec 16) n) (i : Fin n) :
    (vpaddw
        (runOutputToVec
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V))) b) i
      = runOutputToVec (transTy ((srcCom q n).denote V)) i + b i := by
  -- right factor: the per-lane SIMD add reduces lane `i` to `laneAddW (out i) (b i)`
  rw [vpaddw_eq_vmap₂, vmap₂_eq_scalar]
  -- left factor: the 3-pass chain, read back at lane `i`
  show laneAddW _ (b i) = _
  rw [laneAddW_eq]
  -- both packed read-backs are the per-lane scalar slot read-back
  exact congrArg (· + b i) (runOutputToWords_chain_eq q n hLeaf hInj hPinj V i)

/-- **The whole-array form of the vector splice.** Stated as a `funext`-level
    equality of the two packed lane bundles: the packed `vpaddw` of the emitted
    run-output and `b` equals, as a whole `VectorTy (BitVec 16) n`, the lane-wise
    abstract sum of the source program's packed coefficients and `b`. This is
    `vec_runOutput_vpaddw_eq` quantified over all lanes — the single equation
    realising the entire `n`-coefficient source result by the one SIMD instruction. -/
theorem vec_runOutput_vpaddw_eq_packed (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n))
    (b : VectorTy (BitVec 16) n) :
    vpaddw
        (runOutputToVec
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V))) b
      = fun i => runOutputToVec (transTy ((srcCom q n).denote V)) i + b i := by
  funext i
  exact vec_runOutput_vpaddw_eq q n hLeaf hInj hPinj V b i

/-- **The two-packed-operand vector splice.** Choosing the second operand to also be
    a packed read-back makes both SIMD operands come from emitted jasmin run-outputs:
    the emitted `vpaddw` of two run-output lane bundles equals, at every lane `i`, the
    abstract sum of the source program's `i`-th coefficients of each. The vector,
    two-operand analogue of `RunOutputReadback.slot_runOutput_x86Add_eq_pair`; both
    operands cross the run-output ↦ packed-lane seam. -/
theorem vec_runOutput_vpaddw_eq_pair (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V W : Ctxt.Valuation (inCtxt q n)) (i : Fin n) :
    (vpaddw
        (runOutputToVec
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)))
        (runOutputToVec
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal W)))) i
      = runOutputToVec (transTy ((srcCom q n).denote V)) i
          + runOutputToVec (transTy ((srcCom q n).denote W)) i := by
  rw [vpaddw_eq_vmap₂, vmap₂_eq_scalar]
  show laneAddW _ _ = _
  rw [laneAddW_eq]
  exact congrArg₂ (· + ·) (runOutputToWords_chain_eq q n hLeaf hInj hPinj V i)
    (runOutputToWords_chain_eq q n hLeaf hInj hPinj W i)

end CatCrypt.Crypto.SecureCompilation.VIR.PackedRunOutputReadback
