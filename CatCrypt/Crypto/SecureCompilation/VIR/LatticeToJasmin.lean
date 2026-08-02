/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# `Com latticeDialect → Com jasminDialect → .jazz` (Phase 4: backend unification)

This file closes the missing link of the Jasmin ⇄ VIR convergence
(`jasmin-vir-convergence-plan.md` §6, "backend unification"): the optimizer
runs on the **lattice** dialect (`Com latticeDialect`, see `LatticeDialect.lean`),
while the `.jazz` printer (`JasminPrint.lean`) emits from the **Jasmin** dialect
(`Com jasminDialect → JasminProg → .jazz`). To get an *optimized* lattice
program into the printer we need a dialect conversion:

```
Com[latticeDialect]  ──lowerLatticeToJasmin──▶  Com[jasminDialect]  ──emitJazz──▶ .jazz
```

## Approach A: a typed dialect conversion `Com[lattice] → Com[jasmin]`

This is the principled MLIR way — a real `Com → Com` rewrite over the de Bruijn
substrate, with both the context `Γ` and the result type transported along a
type map `tau : LatticeTy → JasminTy`. Each lattice op becomes a Jasmin
`extCall` to a named NTT leaf:

| lattice op       | jasmin `extCall` name        |
|------------------|------------------------------|
| `ntt q n`        | `ntt_{q}_{n}`                |
| `invntt q n`     | `ntt_invntt_{q}_{n}`         |
| `basemul q n`    | `ntt_basemul_{q}_{n}`        |
| `polyAddN q n`   | `poly_add`                   |
| `polyMulC q n`   | `poly_mul`                   |

### The type map `tau`

Both polynomial forms denote to `Fin n → BitVec 16`, so both map to the same
Jasmin stack-array type:

    tau (polyC q n) = stackArr 16 n
    tau (polyN q n) = stackArr 16 n

### The `Ctxt.Var` transport (the crux)

We transport a `Var Γ s` to a `Var (Γ.map tau) (tau s)` by structural recursion
on the variable (a de Bruijn membership index). The cons-commute fact
`(t :: Γ).map tau = tau t :: Γ.map tau` holds **definitionally** for `List.map`,
so `.here ↦ .here` and `.there v ↦ .there (recurse v)` type-check directly with
no `▸` casts. We lift this pointwise over the op's argument `HVector`
(`mapVarHV`). No existing `Ctxt.Var` cross-type transport was found in `Core.lean`
/ `MergeCom.lean` (`Ctxt.Hom` is same-`Ty`, same-dialect), so we write the small
total recursion here.

The lattice dialect's `DialectSignature` has fixed-shape signatures, so each op's
arg-`HVector` (and the lowered `extCall`'s `argTys`) line up by `List.map tau`
applied to the lattice signature — making the conversion total and structural.

## Denotation preservation

`JasminDialect.jasminExtSem` gives the `ntt_*` / `poly_*` 16-bit stack-array
leaves their real (data-oblivious) semantics, and the lattice op denotations
agree with those leaves. Hence this conversion is denotation-preserving:
`LatticeToJasminDenoteUncond.lowerLatticeToJasmin_denote_eq_uncond` proves it
with no hypothesis. This file's own contribution is the structural end-to-end
path (`Com[lattice] → Com[jasmin] → .jazz`) plus a smoke test that the emitted
`.jazz` carries the expected NTT leaf calls; the denotational half lives in
`LatticeToJasminDenote.lean` (parametric) and `LatticeToJasminDenoteUncond.lean`
(discharged).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.Jasmin

/-! ## 1. The type map `tau` -/

/-- Map a lattice value-type to a Jasmin value-type. Both polynomial forms
    (coefficient and NTT) denote to `Fin n → BitVec 16`, so both map to the same
    16-bit, `n`-element stack array. -/
def tau : LatticeTy → JasminTy
  | .polyC _ n => .stackArr 16 n
  | .polyN _ n => .stackArr 16 n

/-! ## 2. The `Ctxt.Var` transport along `tau`

`(t :: Γ).map tau = tau t :: Γ.map tau` holds definitionally for `List.map`, so
the de Bruijn index transport needs no `▸` casts: `.here ↦ .here`,
`.there v ↦ .there (mapVar v)`. -/

/-- Transport a lattice-dialect de Bruijn variable to the `tau`-mapped Jasmin
    context. Structural recursion on the membership witness. -/
def mapVar {Γ : Ctxt latticeDialect} {s : LatticeTy} :
    Ctxt.Var Γ s → Ctxt.Var (d := jasminDialect) (Γ.map tau) (tau s)
  | .here => .here
  | .there v => .there (mapVar v)

/-- Lift `mapVar` pointwise over an `HVector` of argument variables, transporting
    the index list along `tau`. -/
def mapVarHV {Γ : Ctxt latticeDialect} :
    {tys : List LatticeTy} →
    HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := jasminDialect) (Γ.map tau) ty) (tys.map tau)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (mapVar v) (mapVarHV rest)

/-! ## 3. The leaf name for each lattice op -/

/-- The Jasmin `extCall` leaf name for a lattice op. -/
def leafName : LatticeOp → String
  | .ntt q n => "ntt_" ++ toString q ++ "_" ++ toString n
  | .invntt q n => "ntt_invntt_" ++ toString q ++ "_" ++ toString n
  | .basemul q n => "ntt_basemul_" ++ toString q ++ "_" ++ toString n
  | .polyAddN _ _ => "poly_add"
  | .polyMulC _ _ => "poly_mul"

/-! ## 4. Lower one `Expr[lattice]` to an `Expr[jasmin]`

Each lattice op becomes a Jasmin `extCall` whose `argTys`/`retTy` are the
`tau`-mapped lattice signature, and whose args are the `tau`-transported lattice
arg `HVector`. The `extCall`'s declared signature is, by construction, exactly
`(sig op).map tau` / `tau (ret op)`, which is what `mapVarHV` produces — so the
`Expr` typechecks with `retTy_eq := rfl`. -/

/-- The Jasmin `extCall` op for a lattice op: leaf name, `tau`-mapped arg types,
    `tau`-mapped return type. -/
def jasminOpOf (op : LatticeOp) : JasminOp :=
  .extCall (leafName op)
    ((DialectSignature.sig (d := latticeDialect) op).map tau)
    (tau (DialectSignature.ret (d := latticeDialect) op))

/-- Lower a lattice expression to a Jasmin expression in the `tau`-mapped
    context. The `extCall`'s signature is `(sig op).map tau` with return
    `tau (ret op)`, so both `retTy_eq` and the `args` type align by `rfl`. -/
def lowerExpr {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) :
    Expr jasminDialect (Γ.map tau) (tau t) :=
  { op := jasminOpOf e.op
    -- `ret (jasminOpOf op) = tau (ret op) = tau t`: the `extCall`'s `retTy`
    -- field is `tau (ret op)` by definition of `jasminOpOf`, so the goal is
    -- `tau (ret op) = tau t`, closed by `congrArg tau e.retTy_eq`.
    retTy_eq := congrArg tau e.retTy_eq
    -- `sig (jasminOpOf op) = (sig op).map tau` definitionally (it is the
    -- `extCall`'s `argTys` field), matching `mapVarHV e.args`.
    args := mapVarHV e.args }

/-! ## 5. Lower a `Com[lattice]` to a `Com[jasmin]`

Structural recursion: `.ret v ↦ .ret (mapVar v)`,
`.var e body ↦ .var (lowerExpr e) (recurse body)`. The bound type `t` shifts to
`tau t`, and the body's context `t :: Γ` maps to `tau t :: Γ.map tau` (cons
commutes definitionally), so the recursion is well-typed. -/

/-- Lower a lattice-dialect program to a Jasmin-dialect program over the
    `tau`-mapped context and result type. -/
def lowerLatticeToJasmin {Γ : Ctxt latticeDialect} {t : LatticeTy} :
    Com latticeDialect Γ t → Com jasminDialect (Γ.map tau) (tau t)
  | .ret v => .ret (mapVar v)
  | .var e body => .var (lowerExpr e) (lowerLatticeToJasmin body)

/-! ## 6. End-to-end: `Com[lattice] → .jazz` -/

/-- End-to-end emission: lower a lattice program to Jasmin and pretty-print to
    `.jazz` text via the existing `JasminPrint.emitJazz`. This is the deliverable
    path `Com latticeDialect → … → .jazz`. -/
def emitLatticeJazz {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (name : String) (com : Com latticeDialect Γ t) : String :=
  JasminPrint.emitJazz name (lowerLatticeToJasmin com)

/-! ## 7. Smoke test: emit `tgtCom` (and `srcCom`) and check for leaf calls

We emit the NTT-expanded target program `tgtCom` (`ntt a; ntt b; basemul; invntt;
ret`) at ML-KEM-flavoured parameters `(q, n) = (3329, 256)` and check the `.jazz`
contains the expected NTT leaf calls. We also emit the unoptimized `srcCom`
(`poly_mul`) to confirm the unexpanded path. -/

/-- The Jasmin `Com` obtained by lowering `tgtCom 3329 256`. -/
def tgtJasmin : Com jasminDialect ((LatticeDialect.inCtxt 3329 256).map tau) (tau (.polyC 3329 256)) :=
  lowerLatticeToJasmin (LatticeDialect.tgtCom 3329 256)

/-- The emitted `.jazz` for the NTT-expanded target program. -/
def tgtJazz : String := emitLatticeJazz "ntt_mul" (LatticeDialect.tgtCom 3329 256)

/-- The emitted `.jazz` for the unexpanded source program (`poly_mul`). -/
def srcJazz : String := emitLatticeJazz "poly_mul_src" (LatticeDialect.srcCom 3329 256)

-- Print the emitted `.jazz` text for visual inspection.
#eval IO.println tgtJazz
#eval IO.println srcJazz

/-- The lowered target `Com` has four bindings (`ntt`, `ntt`, `basemul`,
    `invntt`) before its `ret`, so it lowers to a four-instruction body. -/
def tgtProg : JasminProg := lowerComToProg "ntt_mul" tgtJasmin

/-- Exactly one function is produced. -/
theorem tgt_one_func : tgtProg.funcs.length = 1 := by decide

/-- The function takes two parameters (the two coefficient-form polynomial
    inputs `a`, `b`). -/
theorem tgt_two_params :
    (tgtProg.funcs.head?.map (fun fd => fd.params.length)) = some 2 := by
  decide

/-- The body has four instructions: `ntt a`, `ntt b`, `basemul`, `invntt`. -/
theorem tgt_four_instrs :
    (tgtProg.funcs.head?.map (fun fd => fd.body.length)) = some 4 := by
  decide

/- The emitted target `.jazz` contains the `ntt_basemul_` leaf call. -/
#guard (strContains tgtJazz "ntt_basemul_")

/- The emitted target `.jazz` contains the `ntt_invntt_` leaf call. -/
#guard (strContains tgtJazz "ntt_invntt_")

/- The emitted target `.jazz` contains the forward `ntt_` leaf call. -/
#guard (strContains tgtJazz "ntt_3329_256")

/- The emitted source `.jazz` contains the unexpanded `poly_mul` leaf call. -/
#guard (strContains srcJazz "poly_mul")

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
