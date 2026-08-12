/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect

/-!
# A *denoting* MLIR `polynomial` dialect in the VIR framework

> **STATUS — MLIR-CORRESPONDENCE LAYER, NOT THE EMIT PATH.** `rfl`
> semantic-agreement lemmas proving CatCrypt polynomial ops match upstream MLIR
> `polynomial`; NO lowering out, ZERO emit traffic (see "Status: THEORY artifact,
> not the emit path" below). `polyDialect` / `latticeDialect` are the real
> lattice substrate; this dialect duplicates them for correspondence only.

This is the **lattice** analogue of `MlirArithDialect.lean` and
`MlirMemrefDialect.lean`. Those files supply denoting MLIR `arith` / `memref`
dialects for the scalar / array fragment of `catCryptDialect`. Here we do the
same for the *polynomial* fragment, taking the local `latticeDialect`
(`LatticeDialect.lean`) as the source and an upstream-MLIR-`polynomial`-flavoured
target.

The upstream MLIR `polynomial` dialect provides ring operations on quotient
polynomials `Z_q[X]/(f)` together with the NTT pair `polynomial.ntt` /
`polynomial.intt`. We model the fragment that `latticeDialect` exercises:

| MLIR `polynomial` op | latticeDialect op | denotation              |
|----------------------|-------------------|-------------------------|
| `polynomial.ntt`     | `ntt q n`         | `nttF`                  |
| `polynomial.intt`    | `invntt q n`      | `invnttF`               |
| `polynomial.mul`     | `basemul q n`     | `basemulF` (NTT-domain) |
| `polynomial.add`     | `polyAddN q n`    | `polyAddNF`             |
| `polynomial.mul_scalar` (coeff-form) | `polyMulC q n` | `polyMulCF` |

We **reuse `latticeDialect`'s `Ty`** (so the value types `polyC q n` / `polyN q n`
denote identically via the shared `TyDenote LatticeTy` instance) and **reuse the
same leaf functions** `nttF` / `invnttF` / `basemulF` / `polyAddNF` / `polyMulCF`
in this dialect's `DialectDenote`. Consequently each per-op semantic agreement
(§3) is literally `rfl`: the two dialects assign identical meaning to every
polynomial op. The static modulus/degree `q`/`n` are threaded as op parameters
exactly as in `LatticeOp`, so the source and target denotations are the *same
function*.

Note that the leaf functions `nttF` / `invnttF` / `basemulF` / `polyAddNF` /
`polyMulCF` are the concrete (total, non-axiomatic) functions defined in
`LatticeDialect.lean` (`nttF = invnttF = id`, `basemulF`/`polyAddNF` pointwise,
`polyMulCF` the composite). Reusing them verbatim is what makes every agreement
lemma definitional.

All agreement lemmas close by `rfl`, and the constructive `Com → Com`
translation `translate` together with its denotation-preservation theorem
`translate_denote_eq` are fully proven, mirroring the arith / memref files
(only here the shared `Ty` is `LatticeTy` rather than `CryptoTy`).

## Status: THEORY artifact, not the emit path

This dialect is a **theory layer**, not a live lowering island. It supplies a
`DialectDenote` so that per-op semantic agreement between `latticeDialect` and an
upstream-MLIR-`polynomial`-flavoured target can be *proved* (the `rfl` agreement
lemmas above), but it has **no lowering out** — no `Com → JasminProg`, no Veir
emission. The real lattice lowering on the emit path goes
`latticeDialect → jasminDialect` directly via `lowerLatticeToJasmin` in
`VIR/LatticeToJasmin.lean`. Keep this module for the semantic-agreement proofs;
do not mistake it for a backend.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlirPolynomialDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect

/-! ## 1. Op tags

The MLIR `polynomial` ops we lower to. Types reuse `LatticeTy` (so `polyC q n`
and `polyN q n` denote to `Fin n → BitVec 16`, matching `latticeDialect`
exactly). -/

/-- Operation tags for the local denoting MLIR `polynomial` dialect. Each
    constructor corresponds to an upstream MLIR `polynomial.*` opcode, modelling
    exactly the fragment `latticeDialect` exercises. The modulus `q` and degree
    `n` are carried as parameters, mirroring `LatticeOp`. -/
inductive MlirPolynomialOp where
  /-- `polynomial.ntt`: `polyC q n → polyN q n` — forward NTT. -/
  | ntt (q n : Nat)
  /-- `polynomial.intt`: `polyN q n → polyC q n` — inverse NTT. -/
  | intt (q n : Nat)
  /-- `polynomial.mul`: `polyN q n → polyN q n → polyN q n` — NTT-domain product. -/
  | mul (q n : Nat)
  /-- `polynomial.add`: `polyN q n → polyN q n → polyN q n` — NTT-domain addition. -/
  | add (q n : Nat)
  /-- `polynomial.mul_scalar` (coeff-form): `polyC q n → polyC q n → polyC q n`. -/
  | mul_scalar (q n : Nat)
  deriving DecidableEq

/-! ## 2. The dialect, signature and denotation -/

/-- The local MLIR `polynomial` dialect: `Op` is `MlirPolynomialOp`, `Ty` is
    `LatticeTy` (shared with `latticeDialect`, so the `TyDenote LatticeTy`
    instance from `LatticeDialect.lean` applies). -/
@[reducible] def mlirPolynomialDialect : Dialect :=
  { Op := MlirPolynomialOp, Ty := LatticeTy }

/-- Operation signatures: argument types + return type. Chosen to match the
    `latticeDialect` op the constructor mirrors. -/
instance : DialectSignature mlirPolynomialDialect where
  sig op := match op with
    | .ntt q n => [.polyC q n]
    | .intt q n => [.polyN q n]
    | .mul q n => [.polyN q n, .polyN q n]
    | .add q n => [.polyN q n, .polyN q n]
    | .mul_scalar q n => [.polyC q n, .polyC q n]
  ret op := match op with
    | .ntt q n => .polyN q n
    | .intt q n => .polyC q n
    | .mul q n => .polyN q n
    | .add q n => .polyN q n
    | .mul_scalar q n => .polyC q n

/-- Operation denotation: the **standard MLIR `polynomial` ring semantics**,
    reusing the *identical* leaf functions of `latticeDialect`. Each clause is
    chosen to coincide with `latticeDenote`'s clause for the op the polynomial
    lowering maps from (see §3). -/
instance mlirPolynomialDenote : DialectDenote mlirPolynomialDialect where
  denote op := match op with
    | .ntt _ _ => fun args =>
        nttF args.head
    | .intt _ _ => fun args =>
        invnttF args.head
    | .mul _ _ => fun args =>
        basemulF args.head args.tail.head
    | .add _ _ => fun args =>
        polyAddNF args.head args.tail.head
    | .mul_scalar _ _ => fun args =>
        polyMulCF args.head args.tail.head

/-! ## 3. Per-op semantic agreement

For each `latticeDialect` op, its `DialectDenote.denote` equals the
corresponding `mlirPolynomialDialect` op's `DialectDenote.denote` on the same
arguments. Because the two `DialectDenote` instances were written with matching
clauses reusing the *same* leaf functions (and identical
`DialectSignature.sig`/`ret`, so the argument `HVector` and return types
coincide definitionally), every lemma closes by `rfl`.

This is the per-op analogue of the arith / memref `agree_*` families: it
certifies that each target of the polynomial lowering denotes to the same
function as its source. The modulus `q` / degree `n` are threaded through both
sides, so the denotations are literally the same function. -/

section Agreement

/-- `ntt q n` agrees with `ntt q n` (`polynomial.ntt`). -/
theorem agree_ntt (q n : Nat) :
    DialectDenote.denote (d := latticeDialect) (.ntt q n)
      = DialectDenote.denote (d := mlirPolynomialDialect) (.ntt q n) := rfl

/-- `invntt q n` agrees with `intt q n` (`polynomial.intt`). -/
theorem agree_invntt (q n : Nat) :
    DialectDenote.denote (d := latticeDialect) (.invntt q n)
      = DialectDenote.denote (d := mlirPolynomialDialect) (.intt q n) := rfl

/-- `basemul q n` agrees with `mul q n` (`polynomial.mul`, NTT-domain product). -/
theorem agree_basemul (q n : Nat) :
    DialectDenote.denote (d := latticeDialect) (.basemul q n)
      = DialectDenote.denote (d := mlirPolynomialDialect) (.mul q n) := rfl

/-- `polyAddN q n` agrees with `add q n` (`polynomial.add`, NTT-domain sum). -/
theorem agree_polyAddN (q n : Nat) :
    DialectDenote.denote (d := latticeDialect) (.polyAddN q n)
      = DialectDenote.denote (d := mlirPolynomialDialect) (.add q n) := rfl

/-- `polyMulC q n` agrees with `mul_scalar q n` (coeff-form
    `polynomial.mul_scalar`). -/
theorem agree_polyMulC (q n : Nat) :
    DialectDenote.denote (d := latticeDialect) (.polyMulC q n)
      = DialectDenote.denote (d := mlirPolynomialDialect) (.mul_scalar q n) := rfl

end Agreement

/-! ## 4. The op-correspondence and master agreement

The agreement lemmas above are the per-op crux. We package them into the op
correspondence `catToPoly` (the semantic-level counterpart of the polynomial
lowering) together with signature preservation and the uniform HEq agreement,
mirroring `MlirArithDialect.catToArith*` / `MlirMemrefDialect.catToMemref*`.

Unlike the arith / memref fronts, `catToPoly` is **total**: every `LatticeOp`
has a `polynomial.*` target, so `catToPoly` never returns `none`. We keep the
`Option` codomain for uniformity with the templates (so `translate` has the
same shape). -/

/-- Semantic-level op correspondence: each `LatticeOp` mapped to the
    `MlirPolynomialOp` whose denotation §3 proves equal. Total here — every
    lattice op has a `polynomial.*` target. The modulus `q` / degree `n` are
    carried straight through, so the corresponded ops have coinciding
    denotations. -/
def catToPoly : LatticeOp → Option MlirPolynomialOp
  | .ntt q n => some (.ntt q n)
  | .invntt q n => some (.intt q n)
  | .basemul q n => some (.mul q n)
  | .polyAddN q n => some (.add q n)
  | .polyMulC q n => some (.mul_scalar q n)

/-- The semantic op-correspondence `catToPoly` preserves signatures: when it
    succeeds, source and target have the same argument types and return type.
    (Definitional — every successful case has matching `sig`/`ret` by
    construction.) -/
theorem catToPoly_sig (op : LatticeOp) (op' : MlirPolynomialOp)
    (h : catToPoly op = some op') :
    DialectSignature.sig (d := latticeDialect) op
      = DialectSignature.sig (d := mlirPolynomialDialect) op'
    ∧ DialectSignature.ret (d := latticeDialect) op
      = DialectSignature.ret (d := mlirPolynomialDialect) op' := by
  cases op <;>
    simp only [catToPoly, Option.some.injEq] at h <;>
    subst h <;> exact ⟨rfl, rfl⟩

/-- **Master per-op agreement.** Whenever `catToPoly` succeeds with `op'`, the
    two dialects denote `op` and `op'` to the same function. This is the uniform
    statement of §3, discharged by case analysis (each case `rfl`). It is the
    single hypothesis a full `Com→Com` preservation proof consumes.

    The dependent rewrite is along `catToPoly_sig`, transporting the
    `mlirPolynomialDialect` denotation back to the source op's argument/return
    types. -/
theorem catToPoly_denote (op : LatticeOp) (op' : MlirPolynomialOp)
    (h : catToPoly op = some op') :
    HEq (DialectDenote.denote (d := latticeDialect) op)
        (DialectDenote.denote (d := mlirPolynomialDialect) op') := by
  cases op <;>
    simp only [catToPoly, Option.some.injEq] at h <;>
    subst h <;> exact HEq.rfl

/-! ## 5. Variable / argument transport between the two dialects

Both dialects share `Ty = LatticeTy`, so `Ctxt` and `Ctxt.Valuation` are
*literally the same* types on either side. The one piece that is *not*
definitionally shared is `Ctxt.Var`: it is an inductive indexed by the
`Dialect` value, so `Var latticeDialect Γ t` and `Var mlirPolynomialDialect Γ t`
are distinct types even though their constructors mention only `d.Ty`. We bridge
them with a structural transport `varCM`, which lookup respects
(`varCM_lookup`). The argument `HVector` is bridged pointwise by `argsCM`, which
`lookupArgs` respects (`argsCM_lookup`). These collapse the only nontrivial
transport in the pass. (Re-derived locally, mirroring the arith / memref
files.) -/

/-- Transport a De Bruijn variable from the `latticeDialect` indexing to the
    `mlirPolynomialDialect` one. Structural identity (`here ↦ here`,
    `there ↦ there`); needed only because `Ctxt.Var` is indexed by the whole
    `Dialect` value. -/
def varCM {Γ : Ctxt latticeDialect} {t : LatticeTy} :
    Ctxt.Var (d := latticeDialect) Γ t →
    Ctxt.Var (d := mlirPolynomialDialect) Γ t
  | .here => .here
  | .there v => .there (varCM v)

/-- Looking up a transported variable in a (shared) valuation gives the same
    value as looking up the original. By induction on the variable. -/
theorem varCM_lookup {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (v : Ctxt.Var (d := latticeDialect) Γ t) (V : Ctxt.Valuation Γ) :
    (varCM v).lookup V = v.lookup V := by
  induction v with
  | here => cases V; rfl
  | there v ih => cases V; exact ih _

/-- Transport an `HVector` of `latticeDialect` variables to one of
    `mlirPolynomialDialect` variables over the same index list, pointwise via
    `varCM`. -/
def argsCM {Γ : Ctxt latticeDialect} :
    {tys : List LatticeTy} →
    HVector (fun ty => Ctxt.Var (d := latticeDialect) Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := mlirPolynomialDialect) Γ ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (varCM v) (argsCM rest)

/-- Resolving a transported argument vector against a valuation gives the same
    resolved `HVector` of values as the original. By induction on the list /
    vector, using `varCM_lookup` per entry. -/
theorem argsCM_lookup {Γ : Ctxt latticeDialect} :
    {tys : List LatticeTy} →
    (args : HVector (fun ty => Ctxt.Var (d := latticeDialect) Γ ty) tys) →
    (V : Ctxt.Valuation Γ) →
    Expr.lookupArgs (d := mlirPolynomialDialect) (argsCM args) V
      = Expr.lookupArgs (d := latticeDialect) args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((varCM v).lookup V)
        (Expr.lookupArgs (d := mlirPolynomialDialect) (argsCM rest) V) = _
      rw [varCM_lookup, argsCM_lookup rest V]
      rfl

/-- Heterogeneous congruence for the two op denotations applied to transported
    arguments. Stated fully generically over the (free) argument-type lists
    `s`/`s'` and return types `r`/`r'`, so the type equalities `hty`/`hr` are
    `cases`-eliminable: once substituted, the function HEq `hf` and the
    `argsCM_lookup` agreement of the resolved arguments collapse the goal to a
    plain `congrArg`. This is the single dependent-transport step in the pass. -/
theorem denote_cong {Γ : Ctxt latticeDialect}
    {s s' : List LatticeTy} {r r' : LatticeTy}
    (f : HVector (fun t => ⟦t⟧) s → ⟦r⟧)
    (g : HVector (fun t => ⟦t⟧) s' → ⟦r'⟧)
    (hty : s = s') (hr : r = r') (hf : HEq f g)
    (args : HVector (fun ty => Ctxt.Var (d := latticeDialect) Γ ty) s)
    (V : Ctxt.Valuation Γ) :
    HEq (g (Expr.lookupArgs (d := mlirPolynomialDialect) (hty ▸ argsCM args) V))
        (f (Expr.lookupArgs (d := latticeDialect) args V)) := by
  cases hty
  cases hr
  cases hf
  exact heq_of_eq (congrArg f (argsCM_lookup args V))

/-! ## 6. Constructive `Com → Com` translation -/

/-- Translate a single `latticeDialect` expression to a `mlirPolynomialDialect`
    expression at the **same** context and return type. Looks the op up in
    `catToPoly` (total here, so this never fails). On success it rebuilds the
    `Expr`, transporting the argument `HVector` (pointwise via `argsCM`, then
    along the arg-type-list equality) and the return-type witness along the
    signature-preservation fact `catToPoly_sig`. -/
def translateExpr {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) : Option (Expr mlirPolynomialDialect Γ t) :=
  match h : catToPoly e.op with
  | none => none
  | some op' =>
      let hsig := catToPoly_sig e.op op' h
      some { op := op'
             retTy_eq := hsig.2 ▸ e.retTy_eq
             args := hsig.1 ▸ argsCM e.args }

/-- Translate a `latticeDialect` program to a `mlirPolynomialDialect` program at
    the same context and return type. `.ret v ↦ .ret (varCM v)`. `.var e body ↦
    .var e' body'` once both `translateExpr e` and the recursive `translate body`
    succeed. (Since `catToPoly` is total, `translate` in fact always succeeds.) -/
def translate : {Γ : Ctxt latticeDialect} → {t : LatticeTy} →
    Com latticeDialect Γ t → Option (Com mlirPolynomialDialect Γ t)
  | _, _, .ret v => some (.ret (varCM v))
  | _, _, .var e body =>
      match translateExpr e with
      | none => none
      | some e' =>
          match translate body with
          | none => none
          | some body' => some (.var e' body')

/-! ## 7. The denotation-preservation theorem

`translate` is denotation-preserving. The `.ret` case is a variable-lookup
identity (`Com.denote` of a return is `v.lookup V`; `varCM_lookup` closes it).
The `.var` case combines the per-expression agreement (the bound `Expr`s denote
equally, via `catToPoly_denote` + `argsCM_lookup`) with the induction hypothesis
on the body. Because the types coincide (both dialects share `Ty = LatticeTy`),
there is no `mapTy`/`mapCtx`, so the valuation transport is the identity. -/

/-- Per-expression agreement: a translated expression denotes to the same value
    as its source on the same valuation. The transported `HVector` resolves to
    the same values (`argsCM_lookup`) and the op denotations agree by
    `catToPoly_denote`; the return-type / arg-type-list casts are discharged by
    substituting the signature equalities. -/
theorem translateExpr_denote_eq {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) (e' : Expr mlirPolynomialDialect Γ t)
    (V : Ctxt.Valuation Γ) (h : translateExpr e = some e') :
    e'.denote V = e.denote V := by
  -- Destruct `e` so its `op`, `retTy_eq`, `args` fields are exposed.
  obtain ⟨op, hret, args⟩ := e
  -- It suffices to prove the heterogeneous equality.
  apply eq_of_heq
  -- Reduce `translateExpr`; the op must have a target (`some op'`).
  simp only [translateExpr] at h
  split at h
  · exact absurd h (by simp)
  · next op' hop =>
      simp only [Option.some.injEq] at h
      -- Per-op agreement (HEq of the denotations) + signature preservation.
      have hden := catToPoly_denote op op' hop
      obtain ⟨hsigArg, hsigRet⟩ := catToPoly_sig op op' hop
      subst h
      -- Peel the two `retTy_eq ▸` casts in `Expr.denote` via `eqRec_heq`, leaving
      -- the op-denotations applied to the (transported) looked-up args.
      simp only [Expr.denote]
      refine HEq.trans (eqRec_heq _ _) (HEq.trans ?_ (eqRec_heq _ _).symm)
      -- The remaining heterogeneous congruence is exactly `denote_cong`.
      exact denote_cong _ _ hsigArg hsigRet hden args V

/-- **Translation preserves denotation.** Whenever `translate c = some c'`, the
    two programs denote to the same value on every valuation. -/
theorem translate_denote_eq {Γ : Ctxt latticeDialect} {t : LatticeTy} :
    (c : Com latticeDialect Γ t) → (c' : Com mlirPolynomialDialect Γ t) →
    (V : Ctxt.Valuation Γ) → translate c = some c' → c'.denote V = c.denote V
  | .ret v, c', V, h => by
      -- `.ret v ↦ .ret (varCM v)`; both denote to a lookup, equal by `varCM_lookup`.
      simp only [translate, Option.some.injEq] at h
      subst h
      show (varCM v).lookup V = v.lookup V
      exact varCM_lookup v V
  | .var e body, c', V, h => by
      -- `.var e body ↦ .var e' body'` once both sub-translations succeed.
      simp only [translate] at h
      split at h
      · exact absurd h (by simp)
      · next e' he =>
          split at h
          · exact absurd h (by simp)
          · next body' hbody =>
              simp only [Option.some.injEq] at h
              subst h
              -- Step both denotations through the `.var` clause of `Com.denote`.
              show body'.denote ((V.extend (e'.denote V)))
                = body.denote (V.extend (e.denote V))
              -- The bound expressions agree, so the extended valuations match;
              -- then apply the body IH.
              rw [translateExpr_denote_eq e e' V he]
              exact translate_denote_eq body body' _ hbody

end CatCrypt.Crypto.SecureCompilation.VIR.MlirPolynomialDialect
