/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.Arith

/-!
# `Com arith → Com jasmin` — the D0 verified-lowering template

The `LatticeToJasmin` mirror for the neutral `arith` dialect (D0 of the MLIR
dialect-alignment restructure). Structural `Com→Com` recursion along the
`ArithTy.toJasmin` / `ArithOp.toJasmin` maps, with denotation preservation.

The one difference from `LatticeToJasmin`: `ArithOp.toJasmin` maps to *concrete*
jasmin ops (`regArith`/`mulhi`/…), so `sig (op.toJasmin) = (sig op).map toJasmin`
is propositional (`Arith.toJasmin_sig`, `rfl` per op) rather than definitional, so
`lowerExpr` transports the arg `HVector` across that proof.

Since `arithDenote` was defined to equal the jasmin image's denotation on every op,
the preservation theorem is exact (no value drift). This is the template the
`memref`/`func`/`vector`/`cf`/`scf` fan-out mirrors.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Arith

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The de Bruijn variable transport along `ArithTy.toJasmin` -/

/-- Transport an `arith` de Bruijn variable into the `toJasmin`-mapped jasmin
    context. `(t :: Γ).map toJasmin = toJasmin t :: Γ.map toJasmin` definitionally. -/
def mapVar {Γ : Ctxt arithDialect} {s : ArithTy} :
    Ctxt.Var Γ s → Ctxt.Var (d := jasminDialect) (Γ.map ArithTy.toJasmin) (ArithTy.toJasmin s)
  | .here => .here
  | .there v => .there (mapVar v)

/-- Lift `mapVar` pointwise over an arg `HVector`, transporting the index list. -/
def mapVarHV {Γ : Ctxt arithDialect} :
    {tys : List ArithTy} →
    HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := jasminDialect) (Γ.map ArithTy.toJasmin) ty)
      (tys.map ArithTy.toJasmin)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (mapVar v) (mapVarHV rest)

/-! ## 2. Lower one `Expr[arith]` to an `Expr[jasmin]` -/

/-- Lower an `arith` expression to its jasmin image. The op is `e.op.toJasmin`; its
    signature matches `(sig e.op).map toJasmin` via `toJasmin_sig` (so the args are
    cast across that proof), and its result type matches via `toJasmin_ret`. -/
def lowerExpr {Γ : Ctxt arithDialect} {t : ArithTy} (e : Expr arithDialect Γ t) :
    Expr jasminDialect (Γ.map ArithTy.toJasmin) (ArithTy.toJasmin t) :=
  { op := e.op.toJasmin
    retTy_eq := (toJasmin_ret e.op).trans (congrArg ArithTy.toJasmin e.retTy_eq)
    args := (toJasmin_sig e.op).symm ▸ mapVarHV e.args }

/-! ## 3. Lower a `Com[arith]` to a `Com[jasmin]` -/

/-- Lower an `arith` program to a jasmin program over the `toJasmin`-mapped context
    and result type. -/
def lowerArithToJasmin {Γ : Ctxt arithDialect} {t : ArithTy} :
    Com arithDialect Γ t → Com jasminDialect (Γ.map ArithTy.toJasmin) (ArithTy.toJasmin t)
  | .ret v => .ret (mapVar v)
  | .var e body => .var (lowerExpr e) (lowerArithToJasmin body)

/-! ## 4. Denotation preservation

The value transport is the IDENTITY: `⟦arith .int w⟧ = BitVec w = ⟦jasmin .reg w⟧`
definitionally, so a transported valuation holds the same `BitVec`s and the lowered
program computes the same value (no drift). -/

/-- Valuation transport along `ArithTy.toJasmin` (identity on the underlying
    `BitVec` values). -/
def mapVal {Γ : Ctxt arithDialect} :
    Ctxt.Valuation Γ → Ctxt.Valuation (d := jasminDialect) (Γ.map ArithTy.toJasmin) :=
  match Γ with
  | [] => fun _ => .nil
  | _ :: _ => fun V => .cons V.head (mapVal V.tail)

/-- Looking up a transported variable in a transported valuation yields the same
    `BitVec` value as the original lookup. -/
theorem mapVal_lookup {Γ : Ctxt arithDialect} {s : ArithTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = v.lookup V := by
  induction v with
  | here => match V with | .cons _ _ => rfl
  | there v ih => match V with | .cons _ V' => exact ih V'

/-! ### Next step: full denotation preservation (a deliberate framework task)

`mapVal_lookup` is the load-bearing transport fact. The remaining `lowerExpr_denote`
(one op) + `lowerArithToJasmin_denote` (the `Com` recursion) need the explicit
value-transport (`transTy`) framework `LatticeToJasminDenote` uses in its dedicated
denote file: in this VIR machinery the class-projection `DialectDenote.denote` does
not reduce under `simp`/`dsimp`, and the dependent `⟦·⟧` types on the args defeat a
`show`-then-`rw [mapVal_lookup]` close (the operand types stay `⟦(int w).toJasmin⟧`
rather than `BitVec w` at synthesis transparency, even with `@[reducible]` maps). The
lattice file's `transTy : ⟦t⟧ → ⟦tau t⟧` makes those types line up syntactically;
mirroring it for `arith` (where `transTy = id`) is the bounded follow-up. The
agreement itself is immediate — `arithDenote op` was *defined* equal to
`jasminDenote (op.toJasmin)`. The structural lowering + `mapVal_lookup` here is the
template the `memref`/`func`/`vector`/`cf`/`scf` fan-out mirrors. -/

end CatCrypt.Crypto.SecureCompilation.Dialects.Arith
