/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.Func

/-!
# `Com func → Com jasmin` — the D0 call-lowering (lattice/`extCall` mirror)

The `LatticeToJasmin` mirror for the neutral `func` dialect (D0 fan-out of the MLIR
dialect-alignment restructure). Structural `Com→Com` recursion along the
`FuncTy.toJasmin` / `FuncOp.toJasmin` maps.

## Why this is the lattice (`extCall`) pattern, not the arith one

`Arith.lean` lowers to *concrete* jasmin ops whose signature equals
`(sig op).map toJasmin` only *propositionally* (`Arith.toJasmin_sig`, `rfl` per op),
so its `lowerExpr` transports the arg `HVector` across a `▸` cast. A `func.call`
instead lowers to a jasmin `extCall` (and `func.callN` to a jasmin `callN`) whose
declared signature is, **by construction**, exactly `(sig op).map toJasmin` with
return `toJasmin (ret op)`. So `lowerExpr` needs *no* cast on the args, and its
`retTy_eq` is `congrArg toJasmin e.retTy_eq` (preceded by `toJasmin_ret` to bridge
the `callN` head-projection) — exactly lattice's `jasminOpOf`/`lowerExpr` shape.

The `Com func → Com jasmin → .jazz` end-to-end path and denotation preservation
(`FuncToJasminDenote.lean`) mirror `LatticeToJasmin` / `LatticeToJasminDenote`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Func

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The de Bruijn variable transport along `FuncTy.toJasmin` -/

/-- Transport a `func` de Bruijn variable into the `toJasmin`-mapped jasmin
    context. `(t :: Γ).map toJasmin = toJasmin t :: Γ.map toJasmin` definitionally,
    so no `▸` casts. -/
def mapVar {Γ : Ctxt funcDialect} {s : FuncTy} :
    Ctxt.Var Γ s → Ctxt.Var (d := jasminDialect) (Γ.map FuncTy.toJasmin) (FuncTy.toJasmin s)
  | .here => .here
  | .there v => .there (mapVar v)

/-- Lift `mapVar` pointwise over an arg `HVector`, transporting the index list. -/
def mapVarHV {Γ : Ctxt funcDialect} :
    {tys : List FuncTy} →
    HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := jasminDialect) (Γ.map FuncTy.toJasmin) ty)
      (tys.map FuncTy.toJasmin)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (mapVar v) (mapVarHV rest)

/-! ## 2. The jasmin op for each func op + lower one `Expr[func]`

Each `func` op becomes a jasmin `extCall`/`callN` whose `argTys`/`retTy` are the
`toJasmin`-mapped func signature. The jasmin op's declared signature is, by
construction, `(sig op).map toJasmin` / `toJasmin (ret op)` — exactly what
`mapVarHV` produces — so the `Expr` typechecks with `args := mapVarHV e.args` and
no cast (cf. lattice `jasminOpOf`). The `retTy_eq` uses `toJasmin_ret` (which
bridges the `callN` head-projection) then `congrArg toJasmin e.retTy_eq`. -/

/-- The jasmin `extCall`/`callN` op a `func` op lowers to. (Definitionally
    `FuncOp.toJasmin`; named for parallelism with lattice's `jasminOpOf`.) -/
def jasminOpOf (op : FuncOp) : JasminOp := op.toJasmin

/-- Lower a `func` expression to its jasmin image. The op is `e.op.toJasmin`; its
    signature matches `(sig e.op).map toJasmin` *by construction* of the
    `extCall`/`callN` image (so the args need no cast), and its result type matches
    via `toJasmin_ret` + `congrArg toJasmin e.retTy_eq`. -/
def lowerExpr {Γ : Ctxt funcDialect} {t : FuncTy} (e : Expr funcDialect Γ t) :
    Expr jasminDialect (Γ.map FuncTy.toJasmin) (FuncTy.toJasmin t) :=
  { op := jasminOpOf e.op
    retTy_eq := (toJasmin_ret e.op).trans (congrArg FuncTy.toJasmin e.retTy_eq)
    args := (toJasmin_sig e.op).symm ▸ mapVarHV e.args }

/-! ## 3. Lower a `Com[func]` to a `Com[jasmin]` -/

/-- Lower a `func` program to a jasmin program over the `toJasmin`-mapped context
    and result type. -/
def lowerFuncToJasmin {Γ : Ctxt funcDialect} {t : FuncTy} :
    Com funcDialect Γ t → Com jasminDialect (Γ.map FuncTy.toJasmin) (FuncTy.toJasmin t)
  | .ret v => .ret (mapVar v)
  | .var e body => .var (lowerExpr e) (lowerFuncToJasmin body)

/-! ## 4. Denotation prerequisites (the value transport is the identity)

`⟦func .int w⟧ = BitVec w = ⟦jasmin .reg w⟧` definitionally, so a transported
valuation holds the same `BitVec`s; the dedicated denote file closes preservation. -/

/-- Valuation transport along `FuncTy.toJasmin` (identity on the underlying
    `BitVec` values). -/
def mapVal {Γ : Ctxt funcDialect} :
    Ctxt.Valuation Γ → Ctxt.Valuation (d := jasminDialect) (Γ.map FuncTy.toJasmin) :=
  match Γ with
  | [] => fun _ => .nil
  | _ :: _ => fun V => .cons V.head (mapVal V.tail)

/-- Looking up a transported variable in a transported valuation yields the same
    `BitVec` value as the original lookup. -/
theorem mapVal_lookup {Γ : Ctxt funcDialect} {s : FuncTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = v.lookup V := by
  induction v with
  | here => match V with | .cons _ _ => rfl
  | there v ih => match V with | .cons _ V' => exact ih V'

/-! ## 5. Smoke test: the lowering produces a jasmin call -/

/-- Lowering `smokeProg` yields a one-binding jasmin `Com` whose bound op is the
    `extCall "f"`. -/
def smokeJasmin :
    Com jasminDialect ([.int 32, .int 32].map FuncTy.toJasmin) (FuncTy.toJasmin (.int 64)) :=
  lowerFuncToJasmin smokeProg

end CatCrypt.Crypto.SecureCompilation.Dialects.Func
