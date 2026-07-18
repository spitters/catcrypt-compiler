/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.Vector

/-!
# `Com vector → Com jasmin` — the D0 verified-lowering (vector fan-out)

The `arith` mirror for the neutral `vector` dialect (D0 of the MLIR
dialect-alignment restructure). Structural `Com→Com` recursion along the
`VectorTy.toJasmin` / `VectorOp.toJasmin` maps, with denotation preservation
(closed in `VectorToJasminDenote.lean`).

`VectorOp.toJasmin` maps to the *concrete* jasmin op `vpackZMM bop`, so
`sig (op.toJasmin) = (sig op).map toJasmin` is propositional (`Vector.toJasmin_sig`,
`rfl` per op) rather than definitional, and `lowerExpr` transports the arg
`HVector` across that proof — exactly as in the `arith` template.

Since `vectorDenote` was defined to equal the jasmin image's denotation
(`zmmPackQ bop`, reused from `JasminDialect`) on `pack`, the preservation theorem is
exact (no value drift).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Vector

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The de Bruijn variable transport along `VectorTy.toJasmin` -/

/-- Transport a `vector` de Bruijn variable into the `toJasmin`-mapped jasmin
    context. `(t :: Γ).map toJasmin = toJasmin t :: Γ.map toJasmin` definitionally. -/
def mapVar {Γ : Ctxt vectorDialect} {s : VectorTy} :
    Ctxt.Var Γ s → Ctxt.Var (d := jasminDialect) (Γ.map VectorTy.toJasmin) (VectorTy.toJasmin s)
  | .here => .here
  | .there v => .there (mapVar v)

/-- Lift `mapVar` pointwise over an arg `HVector`, transporting the index list. -/
def mapVarHV {Γ : Ctxt vectorDialect} :
    {tys : List VectorTy} →
    HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := jasminDialect) (Γ.map VectorTy.toJasmin) ty)
      (tys.map VectorTy.toJasmin)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (mapVar v) (mapVarHV rest)

/-! ## 2. Lower one `Expr[vector]` to an `Expr[jasmin]` -/

/-- Lower a `vector` expression to its jasmin image. The op is `e.op.toJasmin`; its
    signature matches `(sig e.op).map toJasmin` via `toJasmin_sig` (so the args are
    cast across that proof), and its result type matches via `toJasmin_ret`. -/
def lowerExpr {Γ : Ctxt vectorDialect} {t : VectorTy} (e : Expr vectorDialect Γ t) :
    Expr jasminDialect (Γ.map VectorTy.toJasmin) (VectorTy.toJasmin t) :=
  { op := e.op.toJasmin
    retTy_eq := (toJasmin_ret e.op).trans (congrArg VectorTy.toJasmin e.retTy_eq)
    args := (toJasmin_sig e.op).symm ▸ mapVarHV e.args }

/-! ## 3. Lower a `Com[vector]` to a `Com[jasmin]` -/

/-- Lower a `vector` program to a jasmin program over the `toJasmin`-mapped context
    and result type. -/
def lowerVectorToJasmin {Γ : Ctxt vectorDialect} {t : VectorTy} :
    Com vectorDialect Γ t → Com jasminDialect (Γ.map VectorTy.toJasmin) (VectorTy.toJasmin t)
  | .ret v => .ret (mapVar v)
  | .var e body => .var (lowerExpr e) (lowerVectorToJasmin body)

/-! ## 4. Denotation preservation (transport facts)

The value transport is the IDENTITY: `⟦vector .v512⟧ = BitVec 512 = ⟦jasmin .reg 512⟧`
definitionally, so a transported valuation holds the same `BitVec`s and the lowered
program computes the same value (no drift). -/

/-- The per-value transport along `VectorTy.toJasmin`, made an explicit
    per-constructor match. With a single `VectorTy` constructor the underlying
    `⟦s⟧ = ⟦toJasmin s⟧` defeq let `mapVal` reuse `V.head` directly; a SECOND
    constructor (`v128`) breaks that one-line defeq, so the transport is named
    here and `mapVal` / `mapVal_lookup` route through it. Each arm is `id` up to
    the definitional `BitVec`-width equality (`⟦v512⟧ = ⟦reg 512⟧`,
    `⟦v128⟧ = ⟦reg 128⟧`). -/
def transTy : {s : VectorTy} → ⟦s⟧ → ⟦VectorTy.toJasmin s⟧
  | .v512, v => v
  | .v128, v => v

/-- Valuation transport along `VectorTy.toJasmin`, routed through `transTy`
    (identity on the underlying `BitVec` values). -/
def mapVal {Γ : Ctxt vectorDialect} :
    Ctxt.Valuation Γ → Ctxt.Valuation (d := jasminDialect) (Γ.map VectorTy.toJasmin) :=
  match Γ with
  | [] => fun _ => .nil
  | _ :: _ => fun V => .cons (transTy V.head) (mapVal V.tail)

/-- Looking up a transported variable in a transported valuation yields the
    `transTy`-image of the original lookup. -/
theorem mapVal_lookup {Γ : Ctxt vectorDialect} {s : VectorTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = transTy (v.lookup V) := by
  induction v with
  | here => match V with | .cons _ _ => rfl
  | there v ih => match V with | .cons _ V' => exact ih V'

end CatCrypt.Crypto.SecureCompilation.Dialects.Vector
