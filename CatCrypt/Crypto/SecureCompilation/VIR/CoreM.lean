/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# Effectful VIR denotation

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

Adds a **monadic denotation** layer on top of VIR's pure `Core.lean`,
without disturbing the pure path. Two new typeclasses parameterise the
denotation by an effect monad `M`:

* `DialectDenoteM d M` — per-op denotation `op → HVector args → M ⟦ret⟧`.
* `Com.denoteM` — propagates `M` through the let-binding chain via
  `Monad.bind`.

This unblocks two long-standing gaps:

1. **Classical sampling** (`CryptoSSA.CExpr.sampleBit`/`sampleBv`) —
   currently `CryptoToVIR.toVIRExpr` returns `none` for these because
   their denotation lives in `SPComp`, not `Id`. With `M = SPComp` they
   become first-class VIR ops.

2. **Quantum effects** — a future `quantumDialect` whose denotation
   lives in `Quantum.State → Quantum.State` (or `QComp n Unit`).
   Reformulating `CatCrypt/Quantum/QuantumSSA.lean` on top of VIR was
   gated on exactly this — see the Track 4 exploration agent's report.

## Compatibility with existing pure path

`M = Id` recovers the pure `Com.denote` exactly:
```
Com.denoteM (M := Id) c V = Com.denote c V
```
(see `denoteM_id_eq_denote` below). Existing CryptoSSA→VIR proofs that
reason about `Com.denote` continue to work; new effectful ops use
`Com.denoteM` with the appropriate monad.

## Reference

VEIR (opencompl/veir) doesn't expose this directly — its `Veir.IR.Run`
uses a state-passing interpreter rather than a parametric monad. Our
parametric approach matches lean-mlir's `EffectKind` shape more closely
without requiring a regions/EffectKind refactor of `Com`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

/-! ## 1. Monadic dialect denotation -/

/-- A monadic interpretation of a dialect's operations.

    Parametric over an effect monad `M`. For pure dialects, instantiate
    with `M = Id` and `denoteM op args = pure (DialectDenote.denote op args)`. -/
class DialectDenoteM (d : Dialect) (M : Type → Type) [TyDenote d.Ty]
    [DialectSignature d] where
  denoteM : (op : d.Op) →
    HVector (fun t => ⟦t⟧) (DialectSignature.sig op) →
    M ⟦DialectSignature.ret op⟧

/-! ## 2. `Expr.denoteM` -/

namespace Expr

/-- Monadic denotation of an expression. -/
def denoteM {d : Dialect} {M : Type → Type} [TyDenote d.Ty]
    [DialectSignature d] [DialectDenoteM d M]
    {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Ctxt.Valuation Γ) :
    M ⟦t⟧ :=
  e.retTy_eq ▸ DialectDenoteM.denoteM e.op (lookupArgs e.args V)

end Expr

/-! ## 3. `Com.denoteM` -/

namespace Com

/-- Monadic denotation of a `Com`. Threads the monad `M` through each
    let-binding via `Monad.bind`. -/
def denoteM {d : Dialect} {M : Type → Type} [Monad M] [TyDenote d.Ty]
    [DialectSignature d] [DialectDenoteM d M] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Ctxt.Valuation Γ → M ⟦t⟧
  | _, _, .ret v, V => pure (v.lookup V)
  | _, _, .var e body, V =>
      e.denoteM V >>= fun val => body.denoteM (V.extend val)

end Com

/-! ## 4. Bridge: `M = Id` recovers the pure path

When the chosen monad is `Id`, the monadic denotation collapses to the
pure one. This justifies using `Com.denoteM` for new effectful ops
while keeping existing pure proofs about `Com.denote` valid. -/

/-- The pure dialect denotation lifts trivially to an `Id`-monadic one. -/
instance instDialectDenoteM_Id (d : Dialect) [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d] : DialectDenoteM d Id where
  denoteM op args := DialectDenote.denote op args

@[simp]
theorem Expr.denoteM_id_eq_denote {d : Dialect} [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d]
    {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Ctxt.Valuation Γ) :
    e.denoteM (M := Id) V = e.denote V := rfl

@[simp]
theorem Com.denoteM_id_eq_denote {d : Dialect} [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d] :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ),
      c.denoteM (M := Id) V = c.denote V
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V =>
      -- `M = Id` so `>>=` reduces to function application; the IH closes
      -- the recursive call. Definitionally equal under Id reduction.
      Com.denoteM_id_eq_denote body (V.extend (e.denote V))

end CatCrypt.Crypto.SecureCompilation.VIR
