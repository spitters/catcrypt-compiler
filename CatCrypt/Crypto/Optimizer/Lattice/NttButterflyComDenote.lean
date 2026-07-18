/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass
import CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec

/-!
# A DENOTABLE `Com` butterfly tied to the genuine Cooley–Tukey spec

## Scope

The emitted ML-KEM forward NTT (`SecureCompilation/VIR/LatticeNttEmit.lean`,
§6b `emitMlkemNttFull16wayJazz`) is a `.jazz` **text/AST renderer**: it has no
`Com.denote`, so its byte-tie to the genuine transform spec
(`MlkemNttLayout.mlkemNttKernelSpec = nttIter 8 (17 : ZMod 3329)`, tied to `dft`
via `bitrevPerm`) is **KAT-gated** only (`bench/mlkem_compare/…`).

This file builds a **different** artifact: a genuinely DENOTABLE `VIR.Com` model
of ONE Cooley–Tukey radix-2 butterfly over `ZMod 3329`, and proves its
`Com.denote` EQUALS the genuine butterfly spec
`NTTButterflyPass.ctButterfly (ω a b ↦ (a + ω·b, a − ω·b))`. Unlike the
`LatticeNttEmit` renderer, `nttButterflyCom` carries a real `VIR.Com.denote`
(the generic `VIR.Com.denote` over `VIR.Core`), so the tie here is an in-Lean
**Com-denotation ⟷ spec** equality, not a text-render structural check and not a
KAT.

### The Com-vs-jazz-vs-bytes boundary (read carefully — do NOT overclaim)

There are three distinct objects and two distinct gaps:

* **(this file) `nttButterflyCom`** — a `VIR.Com nttDialect` with a real
  `Com.denote : Valuation Γ → ZMod 3329 × ZMod 3329`. We prove
  `nttButterflyCom_denote_eq_ctButterfly`:
  `nttButterflyCom.denote (encode a b ω) = ctButterfly ω a b`. This is a
  Com-denotation ⟷ spec equality.

* **the `.jazz`-rendered §6b kernel** (`emitMlkemNttFull16wayJazz`) — a `String`.
  It is NOT this `Com`: it is rendered text over `BitVec` lanes with Montgomery
  reduction, cross-lane shuffles, and the 16-way AVX2 layout. **We do not prove
  `nttButterflyCom` equals the emitted `.jazz` text**, and we do not prove the
  emitted bytes equal anything here.

* **the emitted machine bytes** — tied to the spec only via the C byte-KAT
  against `PQCLEAN_MLKEM768_CLEAN_ntt`. **NOT proven here.**

So: this file closes the *semantic* gap (a denotable Com whose meaning is the
genuine CT butterfly) for the butterfly unit; it does **not** close the
Com-↔-jazz-text gap nor the jazz-↔-bytes (machine) gap. Those remain the further
steps the §6b renderer needs (a denotation of `emitMlkemNttFull16wayJazz` over
the lane layout, then an equality to `nttButterflyCom` composed across the 16
vectors, then a byte/encoder agreement).

### What composing to the full `nttIter` kernel needs

`nttButterflyCom` is the merge-butterfly unit. The genuine `nttIter (e+1)` layer
(`IterativeNttEqRec.nttIter`) at a fixed index `k < 2^e` produces the pair
`(L k + ω^k · U k, L⟨k+2^e⟩ + ω^(2^e)·ω^k · U⟨k+2^e⟩)`. Under the negacyclic
root condition `ω^(2^e) = -1` this lower/upper output pair is exactly
`ctButterfly (ω^k) (L k) (U k)` — recorded here as
`nttIter_succ_pair_eq_ctButterfly`. Composing the single-butterfly `Com` to a
full `nttIter` layer therefore needs, beyond this file:

1. a **layer-fold `Com`**: a `Com` that maps the `2^e` index pairs through
   `nttButterflyCom` with the per-index twiddle `ω^k` and routes lower/upper
   lanes — i.e. an array/memref-typed `Com` over the `2^e` lanes, not the
   straight-line 3-input one here;
2. the **cross-lane data routing** (`lowerHalf`/`upperHalf` gather and the
   lower/upper scatter) expressed as `Com` ops, matching the §6b kernel's
   `#VPERMQ`/`#VPSHUFB_256` shuffles;
3. iterating (1)+(2) across the `len = 128,…,2` layers and discharging the
   per-layer `ω^(2^e) = -1` obligation from the ML-KEM root facts
   (`mlkemOmega = 17`).

Only the single-butterfly Com-denotation ⟷ `ctButterfly` tie (plus the
`nttIter`-merge bridge lemma) is delivered here; the layer-fold Com and the
cross-lane routing are the named remaining work.

The only thing "trusted" here is nothing beyond Lean's kernel: `nttDialect` is a
toy denotable dialect over `ZMod 3329`, its three ops denote to the ring `+`,
`−`, `·`, and the butterfly equality is closed by `ring`. No machine model, no
`jasminc_preserves_ct`, no `native_decide` (except a concrete root-of-unity fact
if used).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NttButterflyComDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

/-! ## 1. A toy denotable dialect over `ZMod 3329`

A minimal `VIR.Dialect` whose single type `fq` denotes to `ZMod 3329` and whose
ops are the field `+`, `−`, `·` plus a `pair` builder so a single straight-line
`Com` can return the two butterfly lanes `(a + ω·b, a − ω·b)` as one value. This
is genuinely denotable: it reuses the generic `VIR.Com.denote` from `VIR.Core`. -/

/-- ML-KEM prime. -/
abbrev q : ℕ := 3329

/-- The dialect types: a field element `fq = ZMod 3329`, and a `pair` of two
field elements (for the butterfly's two-lane output). -/
inductive NttTy where
  | fq
  | pair
  deriving DecidableEq

/-- `fq ↦ ZMod 3329`, `pair ↦ ZMod 3329 × ZMod 3329`. -/
@[reducible] def NttTy.denote : NttTy → Type
  | .fq => ZMod q
  | .pair => ZMod q × ZMod q

instance : TyDenote NttTy where
  denote := NttTy.denote

/-- The ops: field add / sub / mul (all `fq fq → fq`), and a `mkPair`
(`fq fq → pair`). These are exactly the gates a radix-2 butterfly needs. -/
inductive NttOp where
  | add
  | sub
  | mul
  | mkPair
  deriving DecidableEq

/-- The toy NTT dialect: `Op = NttOp`, `Ty = NttTy`. -/
@[reducible] def nttDialect : Dialect :=
  { Op := NttOp, Ty := NttTy }

instance : DialectSignature nttDialect where
  sig op := match op with
    | .add | .sub | .mul => [NttTy.fq, NttTy.fq]
    | .mkPair => [NttTy.fq, NttTy.fq]
  ret op := match op with
    | .add | .sub | .mul => NttTy.fq
    | .mkPair => NttTy.pair

instance nttDenote : DialectDenote nttDialect where
  denote op := match op with
    | .add => fun args =>
        let a : ZMod q := args.head
        let b : ZMod q := args.tail.head
        a + b
    | .sub => fun args =>
        let a : ZMod q := args.head
        let b : ZMod q := args.tail.head
        a - b
    | .mul => fun args =>
        let a : ZMod q := args.head
        let b : ZMod q := args.tail.head
        a * b
    | .mkPair => fun args =>
        let a : ZMod q := args.head
        let b : ZMod q := args.tail.head
        (a, b)

/-! ## 2. The butterfly `Com`

Input context `[fq, fq, fq]` holds `[ω, a, b]` (de Bruijn: `.here` = `b`,
`.there .here` = `a`, `.there .there .here` = `ω`). The straight line is:

```
t0 = ω * b          -- mul
s  = a + t0         -- add  → a + ω·b   (sum lane)
d  = a - t0         -- sub  → a − ω·b   (diff lane)
o  = mkPair s d
ret o
```

which is exactly `ctButterfly ω a b = (a + ω·b, a − ω·b)`. -/

/-- The input context: `[ω, a, b]`, all `fq`. -/
abbrev Γbf : Ctxt nttDialect := [NttTy.fq, NttTy.fq, NttTy.fq]

/-- `ω * b` expression. -/
def mulExpr {Γ : Ctxt nttDialect} (a b : Ctxt.Var Γ NttTy.fq) :
    Expr nttDialect Γ NttTy.fq :=
  { op := .mul, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- `a + b` expression. -/
def addExpr {Γ : Ctxt nttDialect} (a b : Ctxt.Var Γ NttTy.fq) :
    Expr nttDialect Γ NttTy.fq :=
  { op := .add, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- `a - b` expression. -/
def subExpr {Γ : Ctxt nttDialect} (a b : Ctxt.Var Γ NttTy.fq) :
    Expr nttDialect Γ NttTy.fq :=
  { op := .sub, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- `mkPair a b` expression. -/
def pairExpr {Γ : Ctxt nttDialect} (a b : Ctxt.Var Γ NttTy.fq) :
    Expr nttDialect Γ NttTy.pair :=
  { op := .mkPair, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- **The denotable Cooley–Tukey radix-2 butterfly as a `VIR.Com`.** Inputs
`[ω, a, b]`; output the pair `(a + ω·b, a − ω·b)` via the straight line
`t0 = ω·b; s = a + t0; d = a − t0; mkPair s d`. -/
def nttButterflyCom : Com nttDialect Γbf NttTy.pair :=
  -- Γbf = [ω, a, b]: .here = b, .there .here = a, .there .there .here = ω
  let b_in  : Ctxt.Var Γbf NttTy.fq := .here
  let _a_in : Ctxt.Var Γbf NttTy.fq := .there .here
  let w_in  : Ctxt.Var Γbf NttTy.fq := .there (.there .here)
  -- t0 = ω * b
  .var (mulExpr w_in b_in)
    -- Γ1 = fq :: Γbf; t0 = .here, b = .there .here, a = .there (.there .here), ω = .there^3 .here
    (.var (addExpr (.there (.there .here)) .here)
      -- Γ2 = fq :: Γ1; s = .here, t0 = .there .here, a = .there (.there (.there .here))
      (.var (subExpr (.there (.there (.there .here))) (.there .here))
        -- Γ3 = fq :: Γ2; d = .here, s = .there .here
        (.var (pairExpr (.there .here) .here)
          (.ret .here))))

/-! ## 3. The denotation ⟷ spec tie

`encodeBf a b ω` is the input valuation `[ω, a, b]`. The theorem states the
`Com.denote` of `nttButterflyCom` on that valuation equals `ctButterfly ω a b`. -/

/-- The input valuation `[ω, a, b]` for `Γbf`. -/
def encodeBf (a b ω : ZMod q) : Ctxt.Valuation Γbf :=
  .cons (b : ZMod q) (.cons (a : ZMod q) (.cons (ω : ZMod q) .nil))

/-- **The in-Lean emit-denotation ⟷ spec tie for the butterfly.** The denotation
of the DENOTABLE `nttButterflyCom` on input `[ω, a, b]` is exactly the genuine
Cooley–Tukey butterfly spec `ctButterfly ω a b = (a + ω·b, a − ω·b)`. This is the
semantic tie the `LatticeNttEmit` `.jazz` renderer lacks — a real `Com.denote`,
not a text render or a KAT. -/
theorem nttButterflyCom_denote_eq_ctButterfly (a b ω : ZMod q) :
    nttButterflyCom.denote (encodeBf a b ω) = ctButterfly ω a b := rfl

/-- Projection: the sum lane of the butterfly Com denotation is `a + ω·b`. -/
theorem nttButterflyCom_denote_fst (a b ω : ZMod q) :
    (nttButterflyCom.denote (encodeBf a b ω)).1 = a + ω * b := by
  rw [nttButterflyCom_denote_eq_ctButterfly]; rfl

/-- Projection: the difference lane of the butterfly Com denotation is `a − ω·b`. -/
theorem nttButterflyCom_denote_snd (a b ω : ZMod q) :
    (nttButterflyCom.denote (encodeBf a b ω)).2 = a - ω * b := by
  rw [nttButterflyCom_denote_eq_ctButterfly]; rfl

/-! ## 4. Bridge to `nttIter`: the merge butterfly is one `ctButterfly`

`IterativeNttEqRec.nttIter (e+1)` at a fixed lower index `k < 2^e` emits, on the
two recursed half-transforms `L = nttIter e (ω²) (lowerHalf …)` and
`U = nttIter e (ω²) (upperHalf …)`:

* lower output (index `k`):       `L k + ω^k · U k`
* upper output (index `k + 2^e`): `L k + ω^(2^e)·ω^k · U k`

Under the negacyclic root condition `ω^(2^e) = -1`, the upper output is
`L k − ω^k · U k`, so the lower/upper pair is exactly
`ctButterfly (ω^k) (L k) (U k)`. This identifies the genuine `nttIter` merge step
(over a generic `CommRing`, here instantiable at `ZMod 3329`) with the
single-butterfly unit the denotable `nttButterflyCom` realizes. -/

open CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec

variable {R : Type*} [CommRing R]

/-- **The `nttIter` merge step is a single Cooley–Tukey butterfly.** With
`ω^(2^e) = -1`, the lower output `nttIter (e+1) ω x k` (`k < 2^e`) and the upper
output `nttIter (e+1) ω x ⟨k+2^e⟩` are exactly the two lanes of
`ctButterfly (ω^k) (L k) (U k)`, where `L`/`U` are the half-transforms. This is
the merge-butterfly bridge: the genuine `nttIter` layer is the layer-fold of this
butterfly. (`nttButterflyCom` realizes the `R = ZMod 3329` instance of this
butterfly with twiddle `ω^k`.) -/
theorem nttIter_succ_pair_eq_ctButterfly
    (e : ℕ) (ω : R) (x : Fin (2 ^ (e + 1)) → R) (k : Fin (2 ^ e))
    (hneg : ω ^ (2 ^ e) = -1) :
    let L := nttIter e (ω ^ 2) (lowerHalf e x)
    let U := nttIter e (ω ^ 2) (upperHalf e x)
    ( nttIter (e + 1) ω x ⟨k.val, by
          have := k.isLt; have : (2:ℕ)^(e+1) = 2*2^e := by rw [pow_succ]; ring
          omega⟩
    , nttIter (e + 1) ω x ⟨k.val + 2 ^ e, by
          have := k.isLt; have : (2:ℕ)^(e+1) = 2*2^e := by rw [pow_succ]; ring
          omega⟩ )
      = ctButterfly (ω ^ k.val) (L k) (U k) := by
  intro L U
  have hk : k.val < 2 ^ e := k.isLt
  -- lower output: the `dif` branch with `k.val < 2^e` is true.
  have hlow : nttIter (e + 1) ω x ⟨k.val, by
        have := k.isLt; have : (2:ℕ)^(e+1) = 2*2^e := by rw [pow_succ]; ring
        omega⟩
      = L k + ω ^ k.val * U k := by
    simp only [nttIter]
    rw [dif_pos hk]
  -- upper output: `(k.val + 2^e) < 2^e` is false; the else branch fires.
  have hupp : nttIter (e + 1) ω x ⟨k.val + 2 ^ e, by
        have := k.isLt; have : (2:ℕ)^(e+1) = 2*2^e := by rw [pow_succ]; ring
        omega⟩
      = L k + ω ^ (2 ^ e) * ω ^ (k.val + 2 ^ e - 2 ^ e) * U k := by
    simp only [nttIter]
    rw [dif_neg (by omega)]
    rw [show (⟨k.val + 2 ^ e - 2 ^ e, by
          have := k.isLt; have : (2:ℕ)^(e+1) = 2*2^e := by rw [pow_succ]; ring
          omega⟩ : Fin (2 ^ e)) = k from by apply Fin.ext; simp]
  rw [hlow, hupp, ctButterfly]
  refine Prod.ext rfl ?_
  -- diff lane: L k − ω^k · U k = L k + ω^(2^e)·ω^(k+2^e-2^e)·U k, using ω^(2^e)=-1
  have hidx : k.val + 2 ^ e - 2 ^ e = k.val := by omega
  simp only [hidx, hneg]
  ring

end CatCrypt.Crypto.Optimizer.Lattice.NttButterflyComDenote
