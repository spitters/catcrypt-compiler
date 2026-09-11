/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
public import CatCrypt.Crypto.Optimizer.Lattice.NTTHoist

/-!
# The `invntt` hoist, re-platformed onto the lattice dialect

This is Project-2's `nttHoist` (the `invntt`-out-of-the-accumulation-loop
optimization) re-expressed over the VIR lattice dialect's denotation —
the Phase-3 "move the optimizer onto `Com`" step for the hoist.

The optimization (the `polyvec_dot` shape): a coefficient-form inner
product `Σ_i polyMulC a_i b_i` recomputes `invntt` once per term; because
`invntt` is additive, the accumulation can run in the NTT domain with a
single closing `invntt`:

```
Σ_i invntt (basemul (ntt a_i) (ntt b_i))  =  invntt (Σ_i basemul (ntt a_i) (ntt b_i))
```

The verified core is `NTTHoist.foldl_invntt_fusion_zero` (linearity of an
additive map over a left fold) — it is dialect-agnostic and is reused
here verbatim. `latticeHoist_generic` is the operational statement over
abstract lattice operations (the re-platforming of
`nttHoist_maccLoop_eq`); `latticeHoist_eq` instantiates it at the lattice
dialect's concrete denotations.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect

open CatCrypt.Crypto.Optimizer.Lattice.NTTHoist (foldl_invntt_fusion_zero)

/-! ## §1  Generic hoist (any additive `φ`)

`add` is the (domain-shared) accumulator op, `φ` the inverse transform
(`invntt`), `ntt` the forward transform, `basemul` the NTT-domain
pointwise product.  The only hypotheses are additivity of `φ` and that
`φ` fixes the unit `z`. -/

theorem latticeHoist_generic {V : Type _}
    (add : V → V → V) (φ ntt : V → V) (basemul : V → V → V) (z : V)
    (hadd : ∀ x y, add (φ x) (φ y) = φ (add x y)) (hz : φ z = z)
    (pairs : List (V × V)) :
    pairs.foldl (fun acc p => add acc (φ (basemul (ntt p.1) (ntt p.2)))) z
      = φ (pairs.foldl (fun acc p => add acc (basemul (ntt p.1) (ntt p.2))) z) := by
  -- Let `cOf p = basemul (ntt p.1) (ntt p.2)`; rewrite both folds over
  -- `pairs.map cOf`, apply fold-fusion, then map back.
  have e1 : pairs.foldl (fun acc p => add acc (φ (basemul (ntt p.1) (ntt p.2)))) z
      = (pairs.map (fun p => basemul (ntt p.1) (ntt p.2))).foldl
          (fun acc c => add acc (φ c)) z := by
    rw [List.foldl_map]
  have e2 : pairs.foldl (fun acc p => add acc (basemul (ntt p.1) (ntt p.2))) z
      = (pairs.map (fun p => basemul (ntt p.1) (ntt p.2))).foldl
          (fun acc c => add acc c) z := by
    rw [List.foldl_map]
  rw [e1, e2, foldl_invntt_fusion_zero add φ z hadd hz]

/-! ## §2  Concrete instance at the lattice dialect's denotations

`invnttF`/`nttF` are the (`id`-modelled) inverse pair, `polyAddNF` the
pointwise add, `basemulF` the pointwise NTT product, and `polyMulCF` is
definitionally `invnttF ∘ basemul ∘ ntt`.  Additivity (`hadd`) and
`φ z = z` (`hz`) hold by reduction. -/

theorem latticeHoist_eq {n : Nat}
    (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16))) :
    pairs.foldl (fun acc p => polyAddNF acc (polyMulCF p.1 p.2)) default
      = invnttF (pairs.foldl
          (fun acc p => polyAddNF acc (basemulF (nttF p.1) (nttF p.2))) default) := by
  have key := latticeHoist_generic
    (V := Fin n → BitVec 16) polyAddNF invnttF nttF basemulF default
    (fun _ _ => rfl) rfl pairs
  -- `polyMulCF a b` reduces to `invnttF (basemulF (nttF a) (nttF b))`.
  simpa [polyMulCF] using key

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
