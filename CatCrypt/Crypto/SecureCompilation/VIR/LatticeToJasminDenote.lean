/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin

/-!
# `lowerLatticeToJasmin` is denotation-preserving — UNDER leaf agreement

`LatticeToJasmin.lean` builds the typed dialect lowering
`lowerLatticeToJasmin : Com latticeDialect Γ t → Com jasminDialect (Γ.map tau) (tau t)`
and proves it is a *syntactic* (emission-aimed) lowering: the Jasmin `extCall`
denotes to a stub default (`JasminTy.default`), so as stated the lowering says
nothing about `Com.denote`.

This file closes the *denotational* half **parametrically**, exactly mirroring
`LatticeDialect.nttMul_rewrite_denote_eq_general`: that theorem takes the
NTT leaf agreement as a hypothesis (`hAgree`) and concludes the rewrite
preserves `Com.denote`. Here we take a **leaf-agreement hypothesis** `hLeaf`
saying that each lowered Jasmin `extCall` denotation agrees with the
corresponding lattice op denotation, and conclude that `lowerLatticeToJasmin`
preserves `Com.denote`. The concrete leaf-spec'd Jasmin `extCall` denotation
(the witness that makes `hLeaf` true) is the remaining deferred piece, the
analogue of the deferred byte-layout encoding.

## Why values coincide across the dialect boundary

The type map `tau` sends both polynomial forms to the same Jasmin stack array:

    tau (polyC q n) = tau (polyN q n) = stackArr 16 n

and crucially the *denotations* coincide:

    ⟦polyC q n⟧ = ⟦polyN q n⟧ = ⟦stackArr 16 n⟧ = Fin n → BitVec 16

The catch: `tau` is defined by pattern matching, so `⟦tau t⟧` is *stuck* for an
abstract `t : LatticeTy` — the equality only reduces once `t` is a concrete
constructor (`cases t`). We therefore make the per-value transport explicit as
`transTy : ⟦t⟧ → ⟦tau t⟧`, defined by casing on `t` with `id` in each branch
(well-typed because each branch's source and target denotation are *the same*
`Fin n → BitVec 16`). `transTy` *computes* to `id` on concrete constructors, so
the `.here`/`mapVal_extend` steps close by `rfl`, while the abstract program
induction threads `transTy` uniformly.

## The transport `mapVal`

We transport a lattice valuation `V : Ctxt.Valuation Γ` to a Jasmin valuation
`mapVal V : Ctxt.Valuation (Γ.map tau)`, applying `transTy` per binding,
mirroring `mapVarHV`. We prove `mapVal` commutes with variable lookup
(`mapVal_lookup`), then lift to expressions and to whole programs.

## Scope

* `lowerLatticeToJasmin_denote_eq` — the **general** parametric theorem, by
  induction on the program. This is the must-have.
* `tgtCom_denote_preserved` / `srcCom_denote_preserved` — smoke instances on the
  canonical NTT-expanded `tgtCom` and the unexpanded `srcCom`, under `hLeaf`.

All goals closed. The leaf-agreement hypothesis `hLeaf` is **discharged** in
`LatticeToJasminDenoteUncond.lean`: `JasminDialect.jasminExtSem` now gives the
16-bit stack-array leaves their real (data-oblivious) semantics, so
`lowerLatticeToJasmin_denote_eq_uncond` holds with no hypothesis.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin

/-! ## 1. The per-value transport `transTy`

`⟦t⟧ = ⟦tau t⟧` for every lattice type `t` (both are `Fin n → BitVec 16`), but
`tau` is defined by pattern matching, so the equality is *stuck* for an abstract
`t`. We make the transport explicit by casing on `t`: in each branch source and
target denotation are the *same* type, so the value is returned unchanged. This
*computes* to the identity on concrete constructors. -/

/-- Transport a lattice value to its `tau`-image type. Casing on `t` makes the
    source `⟦t⟧` and target `⟦tau t⟧` denotations *the same* `Fin n → BitVec 16`
    in each branch, so the value passes through unchanged. -/
def transTy : {t : LatticeTy} → TyDenote.denote t → TyDenote.denote (tau t)
  | .polyC _ _, v => v
  | .polyN _ _, v => v

/-- On a concrete coefficient-form type, `transTy` is the identity. -/
theorem transTy_polyC {q n : Nat} (v : Fin n → BitVec 16) :
    transTy (t := .polyC q n) v = v := rfl

/-! ## 2. The valuation transport `mapVal`

Mirror `mapVarHV`: recurse on the context / valuation `HVector`, applying
`transTy` per binding. -/

/-- Transport a lattice valuation to the `tau`-mapped Jasmin context, applying
    `transTy` per binding. -/
def mapVal {Γ : Ctxt latticeDialect} :
    Ctxt.Valuation Γ → Ctxt.Valuation (d := jasminDialect) (Γ.map tau)
  | .nil => .nil
  | .cons (t := t) v rest => .cons (transTy (t := t) v) (mapVal rest)

/-! ## 3. `mapVal` commutes with variable lookup

`(mapVar v).lookup (mapVal V) = transTy (v.lookup V)`. Both sides have Lean type
`⟦tau s⟧`. Proved by induction on the variable. -/

/-- Variable lookup commutes with the valuation transport: looking up the
    transported variable in the transported valuation yields `transTy` of looking
    up the original variable. -/
theorem mapVal_lookup {Γ : Ctxt latticeDialect} {s : LatticeTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = transTy (v.lookup V) := by
  induction v with
  | here =>
      cases V with
      | cons a rest => rfl
  | there v ih =>
      cases V with
      | cons a rest => exact ih rest

/-! ## 4. The leaf-agreement hypothesis

For one lattice expression `e`, the Jasmin lowering `lowerExpr e` denotes (under
the transported valuation) to the same value as `e`. The two values live in
`⟦tau t⟧` resp. `⟦t⟧`, definitionally equal. This is the *parametric*
hypothesis: the Jasmin `extCall` denotation is a stub today, so we abstract over
the fact that it agrees with the lattice op. A concrete leaf-spec'd `extCall`
semantics would discharge it (the deferred piece). -/

/-- Per-expression leaf agreement: the lowered Jasmin expression's denotation
    agrees with `transTy` of the original lattice expression's denotation.
    Quantified over all contexts/types/expressions/valuations so it slots into
    the program induction. -/
def LeafAgrees : Prop :=
  ∀ {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) (V : Ctxt.Valuation Γ),
    (lowerExpr e).denote (mapVal V) = transTy (e.denote V)

/-! ## 5. `mapVal` commutes with valuation extension

`mapVal (V.extend x) = (mapVal V).extend (transTy x)`. Holds by `rfl` since
`mapVal` is the matching `.cons` and `Valuation.extend` is `.cons`. -/

/-- `mapVal` commutes with valuation extension via `transTy` on the new value.
    By `rfl`. -/
theorem mapVal_extend {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (V : Ctxt.Valuation Γ) (x : TyDenote.denote t) :
    mapVal (V.extend x) = (mapVal V).extend (transTy (t := t) x) :=
  rfl

/-! ## 6. The general preservation theorem

By induction on the program. The `.ret` case is exactly `mapVal_lookup`; the
`.var` case uses `hLeaf` for the bound expression and the IH for the body, with
the `mapVal_extend` commute step. -/

/-- **Preservation (general), parametric over leaf agreement.** Under the leaf
    agreement hypothesis `hLeaf`, the dialect lowering `lowerLatticeToJasmin`
    preserves `Com.denote`: the lowered Jasmin program on the transported
    valuation denotes to `transTy` of the original lattice program's denotation.
    Since `transTy` is the (computed) identity transport `⟦t⟧ → ⟦tau t⟧`, this is
    exactly "the lowering preserves the denotation".

    The concrete leaf-spec'd Jasmin `extCall` denotation that would make `hLeaf`
    provable unconditionally is the deferred piece. -/
theorem lowerLatticeToJasmin_denote_eq
    (hLeaf : LeafAgrees)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} :
    (com : Com latticeDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (lowerLatticeToJasmin com).denote (mapVal V) = transTy (com.denote V)
  | .ret v, V => by
      -- `.ret v ↦ .ret (mapVar v)`; both denotes are lookups.
      simpa [lowerLatticeToJasmin, Com.denote] using mapVal_lookup v V
  | .var e body, V => by
      -- `.var e body ↦ .var (lowerExpr e) (lower body)`.
      -- Step the bound expression through `hLeaf`, then the body through the IH.
      show (lowerLatticeToJasmin body).denote
            ((mapVal V).extend ((lowerExpr e).denote (mapVal V))) = _
      rw [hLeaf e V, ← mapVal_extend V (e.denote V)]
      exact lowerLatticeToJasmin_denote_eq hLeaf body (V.extend (e.denote V))

/-! ## 7. Smoke instances on `srcCom` / `tgtCom`

We instantiate the general theorem on the canonical NTT programs. Both are
straight-line `Com`s over the 2-input context `inCtxt q n`. Under `hLeaf` the
preserved-denotation statement holds by direct application of the general
theorem. -/

/-- **Smoke (target).** Under leaf agreement, lowering the NTT-expanded target
    program `tgtCom q n` preserves its denotation. -/
theorem tgtCom_denote_preserved
    (hLeaf : LeafAgrees) (q n : Nat)
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)).denote (mapVal V)
      = transTy ((LatticeDialect.tgtCom q n).denote V) :=
  lowerLatticeToJasmin_denote_eq hLeaf (LatticeDialect.tgtCom q n) V

/-- **Smoke (source).** Under leaf agreement, lowering the unexpanded source
    program `srcCom q n` preserves its denotation. -/
theorem srcCom_denote_preserved
    (hLeaf : LeafAgrees) (q n : Nat)
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    (lowerLatticeToJasmin (LatticeDialect.srcCom q n)).denote (mapVal V)
      = transTy ((LatticeDialect.srcCom q n).denote V) :=
  lowerLatticeToJasmin_denote_eq hLeaf (LatticeDialect.srcCom q n) V

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
