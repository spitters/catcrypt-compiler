/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.Optimizer.Lattice.NttButterflyComDenote
import CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
import CatCrypt.Crypto.Number.MontgomeryReduction

/-!
# A DENOTABLE multi-lane `Com` NTT **layer** tied to `nttIter`

## Scope

`NttButterflyComDenote.lean` builds a denotable `VIR.Com` for ONE Cooley–Tukey
radix-2 butterfly over `ZMod 3329` and proves its `Com.denote` equals
`NTTButterflyPass.ctButterfly`. This file extends that single butterfly to ONE
FULL radix-2 NTT **layer** over `Fin (2^(e+1)) → ZMod 3329`:

* a denotable dialect `nttLayerDialect` with a **vector** type `vec e`
  (`⟦vec e⟧ = Fin (2^e) → ZMod 3329`), a **Montgomery reduce** op
  (`montRed`, denoting `y · R⁻¹` over `ZMod 3329`), and a **layer** op
  (`layer e`, denoting one `nttIter`-merge layer with **cross-lane** lower/upper
  gather + scatter and per-index twiddle);
* `nttLayerCom`, a one-op denotable `Com` realizing that layer; and
* `nttLayerCom_denote_eq_nttIter`, the **whole-layer tie**: the `Com.denote` of
  `nttLayerCom` on the two already-transformed contiguous halves
  `L = nttIter e (ω²) (lowerHalf x)`, `U = nttIter e (ω²) (upperHalf x)`, and the
  twiddle vector `k ↦ ω^k`, equals one `nttIter (e+1) ω x` layer — pointwise over
  all `2^(e+1)` output lanes — provided the negacyclic root condition
  `ω^(2^e) = -1`.

The genuinely-new content over the single butterfly is (1) the **cross-lane
routing** (`lowerHalf`/`upperHalf` gather and the lower/upper scatter), expressed
as the layer denotation, composed across all `2^e` index pairs from
`NttButterflyComDenote.nttIter_succ_pair_eq_ctButterfly`; and (2) the
**Montgomery twiddle bridge** `montMulBridge`: storing twiddles in Montgomery
form `mont ω = ω·R` and reducing the product recovers the plain product —
`montRed (a · mont ω) = a · ω` — reusing the prime-parametric reduction
correctness `CatCrypt.Crypto.Number.montgomeryReduce_correct` (cast into
`ZMod 3329`), NOT a re-proof of modular reduction.

### The Com-vs-jazz-vs-bytes boundary (read carefully — do NOT overclaim)

As in `NttButterflyComDenote`, three distinct objects and two distinct gaps:

* **(this file) `nttLayerCom`** — a `VIR.Com nttLayerDialect` with a real
  `Com.denote`. We prove `nttLayerCom_denote_eq_nttIter`: its denotation equals
  one genuine `nttIter` layer. This is a Com-denotation ⟷ spec equality.
* **the `.jazz`-rendered §6b kernel** (`LatticeNttEmit.emitMlkemNttFull16wayJazz`)
  — a `String` over `BitVec` AVX2 lanes with `#VPERMQ`/`#VPSHUFB_256` shuffles
  and Montgomery reduction. **We do not prove `nttLayerCom` equals that emitted
  `.jazz` text**, nor that the emitted bytes equal anything here.
* **the emitted machine bytes** — tied to the spec only via the C byte-KAT
  against `PQCLEAN_MLKEM768_CLEAN_ntt`. **NOT proven here.**

So this file closes the *semantic* gap (a denotable Com layer whose meaning is a
genuine `nttIter` layer, cross-lane routing and Montgomery bridge included); it
does **not** close the Com-↔-jazz-text gap nor the jazz-↔-bytes (machine) gap.

### What iterating to ALL layers needs

`nttLayerCom` is ONE layer (the `e+1` merge), tied to ONE `nttIter (e+1)` step
given the two transformed halves. The full forward transform
`nttIter 8 ω = mlkemNttKernelSpec` (8 layers, `len = 128,…,1`) is the fold of
this layer over decreasing widths. Composing this layer Com to the full kernel
needs, beyond this file:

1. a **layer-fold `Com`** that sequences `nttLayerCom` at widths `e = 7,…,0`,
   threading each layer's output vector into the next layer's input halves — i.e.
   a `Com` over the `vec` type whose `denote` is the `nttIter` recursion unrolled,
   discharging the per-layer `ω^(2^e) = -1` obligation from `mlkemOmega = 17`
   (`ConcreteNttRoots.isPrimitiveRoot_17_256`);
2. the **bit-reversal** front permutation (`bitrevPerm`) as a `Com` reindex op
   (`IterativeNttEqRec.nttIter_comp_bitrev` then ties the fold to `dft`);
3. the Montgomery domain threaded across all layers (twiddles pre-stored in
   Montgomery form, one `montRed` per multiply — `montMulBridge` is the per-mul
   ingredient; the cross-layer accounting is the remaining obligation).

Only the single denotable layer + its `nttIter`-layer tie (+ the Montgomery
per-multiply bridge) is delivered here; the layer-fold Com and the bit-reversal
reindex op are the named remaining work.

The only thing "trusted" here is nothing beyond Lean's kernel: `nttLayerDialect`
is a toy denotable dialect over `ZMod 3329`, and the layer/Montgomery
denotations are closed by `ring`/`Fin.ext`/the cast of the Nat-level Montgomery
law. No machine model, no `jasminc_preserves_ct`, no `native_decide`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NttLayerComDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass
open CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
open CatCrypt.Crypto.Optimizer.Lattice.NttButterflyComDenote
  (q nttIter_succ_pair_eq_ctButterfly)

/-! ## 1. The merge-layer function and its tie to `nttIter`

`mergeLayer e ω L U` performs one radix-2 NTT merge layer: given the two
already-transformed contiguous halves `L U : Fin (2^e) → R` and the twiddle base
`ω`, it produces the length-`2^(e+1)` output with the **cross-lane** lower/upper
routing — output lane `k < 2^e` is the sum lane `L k + ω^k · U k`, output lane
`k + 2^e` is the diff lane `L k − ω^k · U k`. This is exactly `nttIter (e+1)`
once `L`/`U` are the half-transforms, under the negacyclic root condition. -/

variable {R : Type*} [CommRing R]

/-- One radix-2 NTT merge layer with explicit cross-lane lower/upper routing.
For `k < 2^e` (lower lane) the output is `L k + ω^k · U k`; for `k ≥ 2^e`
(upper lane, index `k − 2^e`) the output is `L (k−2^e) − ω^(k−2^e) · U (k−2^e)`.
The two lanes are the sum/diff of `ctButterfly (ω^j) (L j) (U j)`. -/
def mergeLayer (e : ℕ) (ω : R) (L U : Fin (2 ^ e) → R) :
    Fin (2 ^ (e + 1)) → R := fun k =>
  if h : k.val < 2 ^ e then
    (ctButterfly (ω ^ k.val) (L ⟨k.val, h⟩) (U ⟨k.val, h⟩)).1
  else
    (ctButterfly (ω ^ (k.val - 2 ^ e))
        (L ⟨k.val - 2 ^ e, by
              have hk : k.val < 2 ^ (e + 1) := k.isLt
              have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
              omega⟩)
        (U ⟨k.val - 2 ^ e, by
              have hk : k.val < 2 ^ (e + 1) := k.isLt
              have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
              omega⟩)).2

/-- **The merge layer is one `nttIter` layer.** With the negacyclic root
condition `ω^(2^e) = -1`, applying `mergeLayer` to the two half-transforms
`L = nttIter e (ω²) (lowerHalf x)` and `U = nttIter e (ω²) (upperHalf x)`
reproduces, pointwise on every output lane, one full `nttIter (e+1) ω x` layer.
This is the whole-layer composition of `nttIter_succ_pair_eq_ctButterfly` across
all `2^e` index pairs, with the cross-lane lower/upper scatter made explicit. -/
theorem mergeLayer_eq_nttIter (e : ℕ) (ω : R) (x : Fin (2 ^ (e + 1)) → R)
    (hneg : ω ^ (2 ^ e) = -1) :
    mergeLayer e ω (nttIter e (ω ^ 2) (lowerHalf e x))
        (nttIter e (ω ^ 2) (upperHalf e x))
      = nttIter (e + 1) ω x := by
  funext k
  set L := nttIter e (ω ^ 2) (lowerHalf e x) with hL
  set U := nttIter e (ω ^ 2) (upperHalf e x) with hU
  by_cases h : k.val < 2 ^ e
  · -- lower lane: butterfly sum, and `nttIter` lower branch.
    have hpair := nttIter_succ_pair_eq_ctButterfly e ω x ⟨k.val, h⟩ hneg
    simp only [mergeLayer, dif_pos h]
    -- nttIter lower output (k.val < 2^e branch)
    have : nttIter (e + 1) ω x k
        = (ctButterfly (ω ^ k.val) (L ⟨k.val, h⟩) (U ⟨k.val, h⟩)).1 := by
      rw [ctButterfly]
      simp only [nttIter, hL, hU]
      rw [dif_pos h]
    rw [this]
  · -- upper lane: butterfly diff, and `nttIter` upper branch.
    have hk : k.val < 2 ^ (e + 1) := k.isLt
    have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have hlt : k.val - 2 ^ e < 2 ^ e := by omega
    have hpair := nttIter_succ_pair_eq_ctButterfly e ω x ⟨k.val - 2 ^ e, hlt⟩ hneg
    simp only [mergeLayer, dif_neg h]
    -- the upper output of `nttIter` at index k = (k.val - 2^e) + 2^e
    have hidx : k.val - 2 ^ e + 2 ^ e = k.val := by omega
    -- read off the snd lane of the butterfly via the pair lemma
    have hsnd := congrArg Prod.snd hpair
    simp only at hsnd
    -- nttIter upper branch
    have hnt : nttIter (e + 1) ω x k
        = (ctButterfly (ω ^ (k.val - 2 ^ e)) (L ⟨k.val - 2 ^ e, hlt⟩)
            (U ⟨k.val - 2 ^ e, hlt⟩)).2 := by
      rw [ctButterfly]
      simp only [nttIter, hL, hU]
      rw [dif_neg h]
      simp only [hneg]
      ring
    rw [hnt]

/-! ## 2. The Montgomery twiddle bridge over `ZMod 3329`

In the §6b kernel the twiddles are pre-stored in **Montgomery form** `ω·R` and
each butterfly multiply is followed by a Montgomery reduce. We model this in
`ZMod 3329` with `R = 2^16` (the ML-KEM Montgomery radix): `montRepr x = x·R`,
`montRed y = y·R⁻¹`. The bridge `montMulBridge` shows the Montgomery-domain
multiply-then-reduce recovers the plain product, so storing twiddles in
Montgomery form does not change the layer's meaning. The reduce's correctness is
the cast of the prime-parametric Nat-level law `montgomeryReduce_correct`. -/

/-- The ML-KEM Montgomery radix `R = 2^16`. -/
abbrev mlkemR : ℕ := 65536

/-- `(R : ZMod 3329)` is a unit: `gcd(2^16, 3329) = 1`. -/
theorem mlkemR_isUnit : IsUnit (mlkemR : ZMod q) := by
  rw [ZMod.isUnit_iff_coprime]
  decide

/-- The inverse of the Montgomery radix in `ZMod 3329`. -/
noncomputable def Rinv : ZMod q := (mlkemR_isUnit.unit⁻¹ : (ZMod q)ˣ)

/-- `R · R⁻¹ = 1` in `ZMod 3329`. -/
theorem mul_Rinv : (mlkemR : ZMod q) * Rinv = 1 := by
  rw [Rinv]
  exact mlkemR_isUnit.mul_val_inv

/-- Montgomery representative: `montRepr x = x · R`. -/
noncomputable def montRepr (x : ZMod q) : ZMod q := x * mlkemR

/-- Montgomery reduce: `montRed y = y · R⁻¹`. This is the `ZMod 3329` shadow of
the Nat-level `CatCrypt.Crypto.Number.montgomeryReduce` (whose congruence law
`(redc T)·R ≡ T (mod N)` casts to `(redc T : ZMod q) = T · R⁻¹`). -/
noncomputable def montRed (y : ZMod q) : ZMod q := y * Rinv

/-- **Montgomery reduce inverts the representative.** `montRed (montRepr x) = x`.
-/
@[simp] theorem montRed_montRepr (x : ZMod q) : montRed (montRepr x) = x := by
  simp only [montRed, montRepr]
  rw [mul_assoc, mul_Rinv, mul_one]

/-- **The Montgomery twiddle bridge.** Multiplying a plain residue `a` by a
twiddle stored in Montgomery form `montRepr ω = ω·R`, then Montgomery-reducing,
recovers the plain product `a · ω`. This is the per-multiply fact a layer in the
Montgomery domain rests on; it lets the layer store twiddles as `ω·R` without
changing the layer's meaning. -/
theorem montMulBridge (a ω : ZMod q) : montRed (a * montRepr ω) = a * ω := by
  simp only [montRed, montRepr]
  linear_combination a * ω * mul_Rinv

/-- **The `ZMod 3329` Montgomery reduce agrees with the cast Nat-level law.**
For any Montgomery digit input `T < R·N` reducible by
`CatCrypt.Crypto.Number.montgomeryReduce` (radix `R = 2^16`, with the ML-KEM
Montgomery constant `Nprime`), the Nat reduction cast into `ZMod 3329` equals
`montRed (T : ZMod 3329)` — i.e. our field-level `montRed` is the image of the
prime-parametric Nat reduction, not a re-proof. -/
theorem montRed_eq_natReduce_cast
    (Nprime T : ℕ) (hNprime : (q * Nprime) % mlkemR = mlkemR - 1)
    (hT : T < mlkemR * q) :
    ((CatCrypt.Crypto.Number.montgomeryReduce q mlkemR Nprime T : ℕ) : ZMod q)
      = montRed (T : ZMod q) := by
  obtain ⟨_, hcong⟩ :=
    CatCrypt.Crypto.Number.montgomeryReduce_correct q mlkemR Nprime T
      (by decide) (by decide) hNprime hT
  -- cast the Nat congruence `(redc T) · R ≡ T [MOD q]` into `ZMod q`
  have hc : ((CatCrypt.Crypto.Number.montgomeryReduce q mlkemR Nprime T : ℕ) : ZMod q)
      * (mlkemR : ZMod q) = (T : ZMod q) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ q).mpr hcong
    push_cast at this
    simpa using this
  -- multiply both sides by R⁻¹
  rw [montRed]
  have := congrArg (· * Rinv) hc
  simp only [mul_assoc, mul_Rinv, mul_one] at this
  exact this

/-! ## 3. A denotable dialect with a vector type, a Montgomery reduce op, and a
layer op

`nttLayerDialect` denotes:

* `fq ↦ ZMod 3329`,
* `vec e ↦ (Fin (2^e) → ZMod 3329)`.

Ops:

* `montRedOp : fq → fq` denotes `montRed`;
* `layerOp e : vec e → vec e → vec e → vec (e+1)` denotes
  `fun L U tw => mergeLayerTw e L U tw` — one merge layer parameterized by an
  explicit per-index twiddle vector `tw k = ω^k` (so the dialect op carries no
  field root; the twiddles are data, matching an in-place kernel).

The layer op denotes to a `mergeLayer`-shaped routing keyed by the twiddle
vector, then `mergeLayerTw_eq_mergeLayer` reconnects it to `mergeLayer` (hence to
`nttIter`). -/

/-- The twiddle-vector form of one merge layer: lower lane `L k + tw k · U k`,
upper lane `L j − tw j · U j` (`j = k − 2^e`). Same cross-lane routing as
`mergeLayer`, but the twiddle is supplied as data `tw : Fin (2^e) → R`. -/
def mergeLayerTw (e : ℕ) (L U tw : Fin (2 ^ e) → R) :
    Fin (2 ^ (e + 1)) → R := fun k =>
  if h : k.val < 2 ^ e then
    L ⟨k.val, h⟩ + tw ⟨k.val, h⟩ * U ⟨k.val, h⟩
  else
    L ⟨k.val - 2 ^ e, by
          have hk : k.val < 2 ^ (e + 1) := k.isLt
          have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
          omega⟩
      - tw ⟨k.val - 2 ^ e, by
            have hk : k.val < 2 ^ (e + 1) := k.isLt
            have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
            omega⟩
        * U ⟨k.val - 2 ^ e, by
              have hk : k.val < 2 ^ (e + 1) := k.isLt
              have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
              omega⟩

/-- `mergeLayerTw` with the geometric twiddles `tw k = ω^k` is `mergeLayer`. -/
theorem mergeLayerTw_eq_mergeLayer (e : ℕ) (ω : R) (L U : Fin (2 ^ e) → R) :
    mergeLayerTw e L U (fun j => ω ^ j.val) = mergeLayer e ω L U := by
  funext k
  by_cases h : k.val < 2 ^ e
  · simp only [mergeLayerTw, mergeLayer, dif_pos h, ctButterfly]
  · simp only [mergeLayerTw, mergeLayer, dif_neg h, ctButterfly]

/-- The dialect types: `fq = ZMod 3329` and a vector bundle `vec e`. -/
inductive LTy where
  | fq
  | vec (e : ℕ)
  deriving DecidableEq

/-- `fq ↦ ZMod 3329`, `vec e ↦ (Fin (2^e) → ZMod 3329)`. -/
@[reducible] def LTy.denote : LTy → Type
  | .fq => ZMod q
  | .vec e => Fin (2 ^ e) → ZMod q

instance : TyDenote LTy where
  denote := LTy.denote

/-- The ops: Montgomery reduce (`fq → fq`), and a merge layer at width `e`
(`vec e × vec e × vec e → vec (e+1)`: halves `L`, `U`, and the twiddle vector). -/
inductive LOp where
  | montRedOp
  | layerOp (e : ℕ)
  deriving DecidableEq

/-- The NTT-layer dialect. -/
@[reducible] def nttLayerDialect : Dialect :=
  { Op := LOp, Ty := LTy }

instance : DialectSignature nttLayerDialect where
  sig op := match op with
    | .montRedOp => [LTy.fq]
    | .layerOp e => [LTy.vec e, LTy.vec e, LTy.vec e]
  ret op := match op with
    | .montRedOp => LTy.fq
    | .layerOp e => LTy.vec (e + 1)

noncomputable instance nttLayerDenote : DialectDenote nttLayerDialect where
  denote op := match op with
    | .montRedOp => fun args =>
        let y : ZMod q := args.head
        montRed y
    | .layerOp e => fun args =>
        let L : Fin (2 ^ e) → ZMod q := args.head
        let U : Fin (2 ^ e) → ZMod q := args.tail.head
        let tw : Fin (2 ^ e) → ZMod q := args.tail.tail.head
        mergeLayerTw e L U tw

/-! ## 4. The layer `Com` and its denotation ⟷ `nttIter` tie

Input context `[vec e, vec e, vec e]` holds `[L, U, tw]` (de Bruijn: `.here` =
`tw`, `.there .here` = `U`, `.there .there .here` = `L`). The one-op `Com`
applies `layerOp e` and returns. -/

/-- `layerOp e L U tw` expression. -/
def layerExpr (e : ℕ) {Γ : Ctxt nttLayerDialect}
    (L U tw : Ctxt.Var Γ (LTy.vec e)) :
    Expr nttLayerDialect Γ (LTy.vec (e + 1)) :=
  { op := .layerOp e, retTy_eq := rfl, args := .cons L (.cons U (.cons tw .nil)) }

/-- The input context for a layer: `[L, U, tw]`, all `vec e`. -/
abbrev Γlayer (e : ℕ) : Ctxt nttLayerDialect :=
  [LTy.vec e, LTy.vec e, LTy.vec e]

/-- **The denotable NTT merge layer as a `VIR.Com`.** Inputs `[L, U, tw]`; output
the merged `vec (e+1)`. -/
def nttLayerCom (e : ℕ) : Com nttLayerDialect (Γlayer e) (LTy.vec (e + 1)) :=
  -- Γlayer e = [L, U, tw]: .here = tw, .there .here = U, .there .there .here = L
  let tw_in : Ctxt.Var (Γlayer e) (LTy.vec e) := .here
  let u_in  : Ctxt.Var (Γlayer e) (LTy.vec e) := .there .here
  let l_in  : Ctxt.Var (Γlayer e) (LTy.vec e) := .there (.there .here)
  .var (layerExpr e l_in u_in tw_in) (.ret .here)

/-- The input valuation `[L, U, tw]` for `Γlayer e`. -/
def encodeLayer (e : ℕ) (L U tw : Fin (2 ^ e) → ZMod q) :
    Ctxt.Valuation (Γlayer e) :=
  .cons tw (.cons U (.cons L .nil))

/-- **The layer Com denotation is `mergeLayerTw`.** A direct unfold: the one-op
`nttLayerCom` denotes to exactly the merge-layer routing on its three input
vectors. -/
theorem nttLayerCom_denote_eq_mergeLayerTw (e : ℕ) (L U tw : Fin (2 ^ e) → ZMod q) :
    (nttLayerCom e).denote (encodeLayer e L U tw) = mergeLayerTw e L U tw := rfl

/-- **The whole-layer tie: the layer Com denotation is one `nttIter` layer.**

With twiddles `tw k = ω^k` and the two contiguous half-transforms
`L = nttIter e (ω²) (lowerHalf x)`, `U = nttIter e (ω²) (upperHalf x)`, under the
negacyclic root condition `ω^(2^e) = -1`, the `Com.denote` of the denotable
`nttLayerCom` equals one full `nttIter (e+1) ω x` layer — pointwise over all
`2^(e+1)` output lanes, cross-lane lower/upper routing included. This composes
`NttButterflyComDenote.nttIter_succ_pair_eq_ctButterfly` across every index pair
into a whole-layer `Com`-denotation ⟷ `nttIter`-layer equality. -/
theorem nttLayerCom_denote_eq_nttIter (e : ℕ) (ω : ZMod q)
    (x : Fin (2 ^ (e + 1)) → ZMod q) (hneg : ω ^ (2 ^ e) = -1) :
    (nttLayerCom e).denote
        (encodeLayer e (nttIter e (ω ^ 2) (lowerHalf e x))
          (nttIter e (ω ^ 2) (upperHalf e x)) (fun j => ω ^ j.val))
      = nttIter (e + 1) ω x := by
  rw [nttLayerCom_denote_eq_mergeLayerTw, mergeLayerTw_eq_mergeLayer,
    mergeLayer_eq_nttIter e ω x hneg]

/-! ## 5. Two-layer composition (sanity that the layer chains)

Composing two layers: applying `nttLayerCom (e+1)` to the outputs of two width-`e`
layers (the `e+1` recursion of `nttIter`) reproduces one `nttIter (e+2)` layer,
whenever the two negacyclic conditions hold. This shows the layer Com chains; the
named remaining work (§Scope) is sequencing this as a single `Com`-over-`vec`
fold across all `e`. -/

/-- **Two layers chain to `nttIter (e+2)`.** The outer layer Com at width `e+1`,
fed the two width-`e` half-layers and twiddle `ω^k`, equals one `nttIter (e+2)`
layer. (This is `nttLayerCom_denote_eq_nttIter` at width `e+1`; the inner layers
are already `nttIter (e+1)`-shaped.) -/
theorem nttLayerCom_two_layers (e : ℕ) (ω : ZMod q)
    (x : Fin (2 ^ (e + 2)) → ZMod q) (hneg : ω ^ (2 ^ (e + 1)) = -1) :
    (nttLayerCom (e + 1)).denote
        (encodeLayer (e + 1) (nttIter (e + 1) (ω ^ 2) (lowerHalf (e + 1) x))
          (nttIter (e + 1) (ω ^ 2) (upperHalf (e + 1) x)) (fun j => ω ^ j.val))
      = nttIter (e + 2) ω x :=
  nttLayerCom_denote_eq_nttIter (e + 1) ω x hneg

end CatCrypt.Crypto.Optimizer.Lattice.NttLayerComDenote
