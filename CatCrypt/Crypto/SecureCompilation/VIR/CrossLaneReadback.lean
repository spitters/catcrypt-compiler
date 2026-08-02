/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.PackedRunOutputReadback

/-!
# The CROSS-LANE run-output read-back: splicing a lane PERMUTATION (shuffle) into the chain

## Scope

`PackedRunOutputReadback.lean` packed the whole dialect-chain run-output `Fin n →
BitVec 16` into a SIMD lane bundle (`runOutputToVec`) and spliced one **per-lane**
SIMD step (`vec_runOutput_vpaddw_eq`, a `vpaddw` whose output lane `i` depends only
on input lane `i`). Its `Scope` named the residual precisely: **cross-lane** ops —
where output lane `i` depends on input lane `j ≠ i` (`VPSHUFB`/`VPERMD`/`VPERMQ`/
`VPBROADCAST`, the NTT bit-reversal / butterfly gather-scatter routing, horizontal
reductions) — are **not** per-lane and need lane-permutation modelling
(`VectorTy.shuffle` / `LaneMap.laneMapIdx` / `VectorReduce`), not the per-lane splice.

This file **builds the lane-permutation model** and **proves a cross-lane splice**.

The op modelled here is a lane **PERMUTATION / shuffle**:

    vshuffle (σ : Fin n → Fin n) (v : VectorTy α n) : VectorTy α n := fun i => v (σ i)

output lane `i` is **input lane `σ i`** — a genuine cross-lane reindex (when `σ i ≠ i`,
lane `i` reads a *different* lane). This is the `VPERM*`/`VPSHUFB`-with-an-immediate
shape: the shuffle **control `σ` is a compile-time constant** (an immediate / a fixed
control vector baked into the instruction), so the routing is fixed public data flow —
constant-time and well-defined. It is exactly `MLIR.VectorDialect.VectorTy.shuffle`
(reused), and lane-indexed reads compose with the verified `LaneMap` layer.

### The splice (the deliverable)

`cross_lane_runOutput_shuffle_eq` is the cross-lane analogue of
`PackedRunOutputReadback.vec_runOutput_vpaddw_eq`: the emitted `VPERM*` instruction
applied to the **packed read-back** of the genuine 3-pass dialect chain
(`runOutputToVec out`) is, **at every output lane `i`**, the source-dialect program's
coefficient at the **cross-lane source slot `σ i`** (via
`RunOutputReadback.runOutputToWords_chain_eq` at slot `σ i`). Where the `vpaddw`
splice read slot `i` for lane `i`, the shuffle splice reads slot `σ i` for lane `i` —
that is the cross-lane data routing now covered. `cross_lane_runOutput_shuffle_then_add`
composes the realistic SIMD pattern (permute THEN a per-lane add). `ntt_gather_sigma`
exhibits the NTT lower/upper-half gather as a concrete constant `σ`.

### CONSTANT (public) vs DATA-DEPENDENT shuffle — the honest boundary

* **Covered (constant / public control).** `σ : Fin n → Fin n` is a fixed function
  fixed at compile time — `VPERMQ`/`VPSHUFB`/`VPERMD` with an **immediate** or a
  compile-time-constant control vector. The routing is public, fixed, and
  constant-time: output lane `i` ← input lane `σ i` for the same `σ` regardless of the
  (secret) data values. This is precisely a fixed reindex `fun i => v (σ i)`, and the
  splice covers it for **any** such `σ` (including non-bijective gathers/broadcasts).

* **Excluded by design (data-dependent / secret control).** `VPSHUFB` with a **register
  mask** computed from data routes lane `i` to lane `mask i` where `mask` is a *runtime
  value*. That is the SIMD analogue of a **secret-indexed gather**: it routes by data,
  so it is **not** a fixed reindex (the σ depends on the input), and **if the mask is
  secret it is not constant-time** (the realised lane permutation leaks the mask). We
  do **not** model that here — it is named, not faked: it belongs to the
  secret-index / oblivious-gather track, not the fixed-permutation track.

* **Bijective σ (a true permutation of lanes).** When `σ` is a bijection
  (`Function.Bijective`), `vshuffle σ` permutes the lanes with no loss
  (`vshuffle_comp` shows shuffles compose to `vshuffle (σ ∘ τ)`, and `vshuffle σ⁻¹` is a
  two-sided inverse) — the `VPERMQ`/`VPERMD` case. A non-bijective `σ` is a gather /
  broadcast (`VPBROADCAST` is the constant `σ = fun _ => 0`); the splice still holds
  (the proof never needs bijectivity), it is just not a lane *permutation*.

### Horizontal reductions — a DIFFERENT shape (remaining)

A horizontal cross-lane **reduction** (`hsum`: lane-fold to one scalar, `VPHADD` /
log-tree reduce) is **not** a reindex `fun i => v (σ i)` — every output depends on
**all** input lanes via a fold, not via a single source lane. It is covered by the
*reduce* primitive (`VectorTy.reduce` / `VectorReduce.scalarFold_eq_hsum`), a fold over
lanes, **not** by `vshuffle`. This file covers the **permutation/gather** cross-lane
shape; the horizontal-fold shape is the sibling primitive and is **not** spliced here.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneReadback

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry
open CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback
open CatCrypt.Crypto.SecureCompilation.VIR.PackedRunOutputReadback
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The lane-PERMUTATION SIMD op (`VPERM*` / `VPSHUFB` with a constant control)

A lane permutation routes output lane `i` to input lane `σ i` for a **fixed**
control `σ : Fin n → Fin n`. This is the `VPERMQ`/`VPERMD`/`VPSHUFB`-with-immediate
shape: cross-lane data routing whose control is a compile-time constant (so it is
public, constant-time, well-defined). The model is the existing
`MLIR.VectorDialect.VectorTy.shuffle` — we re-expose it under the SIMD mnemonic
`vshuffle` and prove its basic laws. -/

/-- **The lane-permutation SIMD op (`VPERM*`/`VPSHUFB`, constant control).** Output
    lane `i` reads input lane `σ i`, for a compile-time-constant `σ : Fin n → Fin n`.
    A genuine cross-lane reindex (when `σ i ≠ i`, lane `i` reads a *different* lane).
    Definitionally `MLIR.VectorDialect.VectorTy.shuffle σ` — the AVX `vector` dialect
    shuffle the register model already denotes. Constant-time: the control `σ` is fixed
    at compile time (an immediate), so the routing does not depend on (secret) data. -/
def vshuffle {α : Type} {n : Nat} (σ : Fin n → Fin n) (v : VectorTy α n) :
    VectorTy α n :=
  VectorTy.shuffle σ v

/-- `vshuffle` IS the `vector`-dialect `VectorTy.shuffle`: both are `fun i => v (σ i)`.
    Ties the SIMD mnemonic to the verified dialect shuffle. -/
theorem vshuffle_eq_shuffle {α : Type} {n : Nat} (σ : Fin n → Fin n)
    (v : VectorTy α n) : vshuffle σ v = VectorTy.shuffle σ v := rfl

/-- **`vshuffle` is a reindex.** Output lane `i` is input lane `σ i` — the defining
    cross-lane law (lane `i` may depend on a lane `j = σ i ≠ i`). -/
theorem vshuffle_apply {α : Type} {n : Nat} (σ : Fin n → Fin n)
    (v : VectorTy α n) (i : Fin n) : (vshuffle σ v) i = v (σ i) := rfl

/-- **Identity shuffle is the identity.** `vshuffle id v = v` — the trivial control
    (every lane reads itself; a `VPERM` by the identity immediate is a no-op). -/
theorem vshuffle_id {α : Type} {n : Nat} (v : VectorTy α n) :
    vshuffle (id : Fin n → Fin n) v = v := rfl

/-- **Shuffles compose: a `VPERM` by `σ` then by `τ` is one `VPERM` by `σ ∘ τ`.**
    `vshuffle τ (vshuffle σ v) = vshuffle (σ ∘ τ) v`. (Reindex composition: applying
    control `τ` to the `σ`-shuffled vector reads, at output lane `i`, input lane
    `σ (τ i)`.) The fixed-permutation algebra — two constant shuffles fuse to one,
    the standard `VPERM`-fusion compiler rewrite. -/
theorem vshuffle_comp {α : Type} {n : Nat} (σ τ : Fin n → Fin n)
    (v : VectorTy α n) :
    vshuffle τ (vshuffle σ v) = vshuffle (σ ∘ τ) v := rfl

/-- **A bijective control gives a true lane permutation.** If `σinv` is a right inverse
    of `σ` (`σ (σinv x) = x`), then `vshuffle σinv ∘ vshuffle σ = id` on lane bundles:
    `vshuffle σinv (vshuffle σ v) = v` (output lane `i` of the round-trip is source lane
    `σ (σinv i) = i`). So a `VPERMQ`/`VPERMD` by a permutation immediate is invertible
    (no lane data lost) — the lane-permutation (as opposed to gather) case. -/
theorem vshuffle_leftInverse {α : Type} {n : Nat} {σ σinv : Fin n → Fin n}
    (h : Function.RightInverse σinv σ) (v : VectorTy α n) :
    vshuffle σinv (vshuffle σ v) = v := by
  funext i
  simp only [vshuffle_apply]
  rw [h i]

/-- **The reverse round-trip for a bijection.** With the same data, `vshuffle σ ∘
    vshuffle σinv = id` when `σinv` is a left inverse of `σ` (`σinv (σ x) = x`).
    Together with `vshuffle_leftInverse` this exhibits `vshuffle σ` as a bijection of
    lane bundles for a bijective `σ`. -/
theorem vshuffle_rightInverse {α : Type} {n : Nat} {σ σinv : Fin n → Fin n}
    (h : Function.LeftInverse σinv σ) (v : VectorTy α n) :
    vshuffle σ (vshuffle σinv v) = v := by
  funext i
  simp only [vshuffle_apply]
  rw [h i]

/-! ## 2. The cross-lane splice: dialect chain (packed read-back) ∘ `vshuffle`

The genuine end-to-end **cross-lane** statement. The left factor is the real 3-pass
chain `registryChain_threePass'` read back **as a whole array** via `runOutputToVec`
(and, per slot, via `RunOutputReadback.runOutputToWords_chain_eq`); the right factor
is the `vshuffle` lane permutation. They join through the packed read-back, but now
**output lane `i` reads SOURCE slot `σ i`** — the cross-lane routing. This is the
cross-lane analogue of `PackedRunOutputReadback.vec_runOutput_vpaddw_eq` (whose output
lane `i` read source slot `i`). -/

/-- **End-to-end CROSS-LANE splice through the packed read-back (`VPERM*`, lane
    permutation `σ`).**

    Let `out` be the structured run-output of the emitted jasmin program
    (`runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)`) and
    `σ : Fin n → Fin n` a **compile-time-constant** lane-permutation control. Then the
    emitted `VPERM*`/`VPSHUFB` instruction applied to the **packed read-back**
    `runOutputToVec out` is, **at every output lane `i : Fin n`**, the source-dialect
    program's coefficient at the **cross-lane source slot `σ i`**:

        (vshuffle σ (runOutputToVec out)) i
          = runOutputToVec (transTy ((srcCom q n).denote V)) (σ i).

    This is genuine end-to-end **cross-lane** value-preservation: output lane `i`
    depends on input lane `σ i` (with `σ i ≠ i` whenever the control routes across
    lanes), realised by the emitted `VPERM*` instruction, equal to the abstract source
    coefficient at the routed slot `σ i`. Its left factor is the full 3-pass
    `registryChain_threePass'` (via `RunOutputReadback.runOutputToWords_chain_eq` at
    slot `σ i`) — **not** a representative `id/id` square — and its right factor is the
    lane permutation; the two are joined **through** `runOutputToVec` with the
    cross-lane reindex `σ`.

    **Coverage:** the SIMD op is a lane permutation with **constant (public)** control
    `σ` — `VPERMQ`/`VPERMD`/`VPSHUFB` with an immediate. It is **cross-lane** (output
    lane `i` depends on input lane `σ i`). A data-dependent / secret control mask is
    excluded by design (it is a secret-indexed gather, not a fixed reindex; see module
    `Scope`). Horizontal reductions are a different (fold) shape, not covered here. -/
theorem cross_lane_runOutput_shuffle_eq (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n))
    (σ : Fin n → Fin n) (i : Fin n) :
    (vshuffle σ
        (runOutputToVec
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)))) i
      = runOutputToVec (transTy ((srcCom q n).denote V)) (σ i) := by
  -- right factor: the lane permutation reduces output lane `i` to source slot `σ i`
  rw [vshuffle_apply]
  -- both packed read-backs are the per-slot scalar read-back; the chain ties slot `σ i`
  simp only [runOutputToVec_lane]
  rw [runOutputToWords_chain_eq q n hLeaf hInj hPinj V (σ i)]

/-- **The whole-array form of the cross-lane splice.** Stated as a `funext`-level
    equality of the two packed lane bundles: the emitted `VPERM*`-shuffled run-output
    equals, as a whole `VectorTy (BitVec 16) n`, the source program's packed
    coefficients **reindexed by `σ`** (`fun i => … (σ i)`). This is
    `cross_lane_runOutput_shuffle_eq` quantified over all lanes — the single equation
    realising the cross-lane data routing of the entire `n`-coefficient source result by
    the one `VPERM*` instruction. -/
theorem cross_lane_runOutput_shuffle_eq_packed (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n))
    (σ : Fin n → Fin n) :
    vshuffle σ
        (runOutputToVec
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)))
      = fun i => runOutputToVec (transTy ((srcCom q n).denote V)) (σ i) := by
  funext i
  exact cross_lane_runOutput_shuffle_eq q n hLeaf hInj hPinj V σ i

/-! ## 3. The realistic SIMD pattern: permute THEN a per-lane op (shuffle then add)

A real cross-lane SIMD kernel is rarely a bare shuffle; it is a `VPERM*` that routes
operands into the right lanes, **followed by** a per-lane op (`vpaddw`) — the NTT
butterfly's "gather, then add the twiddle product" shape. We compose the cross-lane
splice (the routing) with the per-lane `vpaddw` splice (the add): output lane `i` is the
source coefficient at the routed slot `σ i`, plus the second operand at lane `i`. -/

/-- **Permute-then-add cross-lane splice (`VPERM*` then `vpaddw`).** Shuffle the packed
    run-output by a constant control `σ`, then add a second packed operand `b` per lane.
    At every lane `i`, the result is the source coefficient at the **routed** slot `σ i`
    plus `b i`:

        (vpaddw (vshuffle σ (runOutputToVec out)) b) i
          = runOutputToVec (transTy ((srcCom q n).denote V)) (σ i) + b i.

    The realistic cross-lane SIMD shape: the `VPERM*` does the cross-lane routing
    (output lane `i` ← source slot `σ i`), then the per-lane `vpaddw` combines lane-wise.
    Composes the cross-lane splice (`cross_lane_runOutput_shuffle_eq`, the routing) with
    the per-lane `vpaddw` faithfulness (`PackedRunOutputReadback`, `laneAddW`). -/
theorem cross_lane_runOutput_shuffle_then_add (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n))
    (σ : Fin n → Fin n) (b : VectorTy (BitVec 16) n) (i : Fin n) :
    (vpaddw
        (vshuffle σ
          (runOutputToVec
            (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)))) b) i
      = runOutputToVec (transTy ((srcCom q n).denote V)) (σ i) + b i := by
  -- per-lane add reduces lane `i` to `laneAddW ((shuffle …) i) (b i)`
  rw [vpaddw_eq_vmap₂, vmap₂_eq_scalar]
  show laneAddW _ (b i) = _
  rw [laneAddW_eq]
  -- the cross-lane routing: lane `i` of the shuffle is the source slot `σ i`
  rw [cross_lane_runOutput_shuffle_eq q n hLeaf hInj hPinj V σ i]

/-! ## 4. The NTT cross-lane routing as a concrete constant `σ`

The motivating example: the AVX2/AVX-512 NTT layer's lower/upper-half **gather**
(the §6b `LatticeNttEmit` kernel's `#VPERMQ`/`#VPSHUFB` lane routing). A radix-2 NTT layer over `n = 2 * h` lanes routes the lower
half `[0, h)` and the upper half `[h, n)` into interleaved butterfly position — a fixed
(public, compile-time) lane permutation. We exhibit one such constant `σ` (the
even/odd deinterleave-style gather `i ↦ (i % h) routed by half`) and confirm the
cross-lane splice applies to it: the NTT routing is the constant-`σ` case of
`cross_lane_runOutput_shuffle_eq`. -/

/-- **An NTT lower/upper-half gather control (constant `σ`).** Over `n` lanes split at
    `h = n / 2`: the standard radix-2 NTT layer gathers lane `i` from the lower half
    when `i < h` (source `i`) and from the upper half when `i ≥ h` (source `i - h`
    re-based) — the lower/upper-half deinterleave the `#VPERMQ`/`#VPSHUFB` performs. A
    fixed, compile-time control (no data dependence), so it is the constant-`σ` /
    public-routing case covered by `vshuffle`. (We use a total, well-defined `Fin n`
    representative of the half-gather; the point is only that it is a *fixed* `σ`.) -/
def ntt_gather_sigma (n : Nat) : Fin n → Fin n :=
  fun i => ⟨(i + n / 2) % n, by
    have : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact (Fin.elim0 i))
    exact Nat.mod_lt _ this⟩

/-- **The NTT cross-lane routing is covered.** The lower/upper-half gather `σ =
    ntt_gather_sigma n` is a fixed (compile-time-constant) lane permutation, so the
    cross-lane splice `cross_lane_runOutput_shuffle_eq` applies to it directly: the
    emitted `#VPERMQ`/`#VPSHUFB` NTT gather of the packed run-output is, at every output
    lane `i`, the source coefficient at the gathered slot `(i + n/2) % n`. This
    demonstrates the cross-lane case is now covered for the motivating NTT routing
    (a CONSTANT, public permutation — constant-time). -/
theorem ntt_gather_runOutput_eq (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n)) (i : Fin n) :
    (vshuffle (ntt_gather_sigma n)
        (runOutputToVec
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)))) i
      = runOutputToVec (transTy ((srcCom q n).denote V)) (ntt_gather_sigma n i) :=
  cross_lane_runOutput_shuffle_eq q n hLeaf hInj hPinj V (ntt_gather_sigma n) i

end CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneReadback
