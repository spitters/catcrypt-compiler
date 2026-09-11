/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# A *denoting* MLIR `memref` dialect in the VIR framework

> **STATUS — MLIR-CORRESPONDENCE LAYER, NOT THE EMIT PATH.** `rfl`
> semantic-agreement lemmas proving CatCrypt ops match upstream MLIR `memref`; NO
> lowering out, ZERO emit traffic. Duplicates `jasminDialect`'s memory ops + the
> Lprog ABI, which ARE the real substrate. See
> `CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md`.

This is the `memref`-op analogue of `MlirArithDialect.lean`. The MLIR emission
pass lowers the `memref`-flavoured `CatCryptOp`s (`memrefZero` / `memrefSet` /
`memrefGet`) to the standard MLIR `memref` dialect (`memref.alloca`-of-zeros /
`memref.store` / `memref.load`). As with the Veir `arith` lowering, that
emission is only *structurally* correct unless we can name a denoting target
dialect and prove the per-op semantics coincide.

This file supplies that semantic foundation. It defines a **local** denoting
MLIR `memref` dialect `mlirMemrefDialect` inside the VIR
`Dialect`/`DialectDenote` framework (the same framework `catCryptDialect`
lives in), with the *standard MLIR `memref` array semantics*:

| op                  | denotation                                  |
|---------------------|---------------------------------------------|
| `allocaZero n`      | the all-zero array `fun _ => 0`             |
| `store n i`         | functional update at index `i`             |
| `load n i`          | indexing at `i`                            |

The model uses pure functional arrays `Fin n → BitVec 64` (the denotation of
`CryptoTy.memref n`, shared with `catCryptDialect`). The static array size `n`
and the access index `i : Fin n` are carried as op parameters, exactly as in
`CatCryptOp` — this threading of `i`/`n` is what makes the source and target
denotations literally the same function.

The semantics are deliberately chosen to **match** `catCryptDialect`'s memref
denotations. The payoff is the per-op **semantic agreement** lemmas in §3: for
each catCrypt memref op, its `DialectDenote.denote` equals the matching
`mlirMemrefDialect` op's on the same arguments. These are the per-op analogue
of the arith `agree_*` family and the crux that makes a full
denotation-preserving `Com catCryptDialect → Com mlirMemrefDialect` translation
provable.

All agreement lemmas close by `rfl` (the denotations are definitionally the
same function), confirming the two dialects assign identical meaning to the
memref fragment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlirMemrefDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-! ## 1. Op tags

The MLIR `memref` ops we lower to. Types reuse `CryptoTy` (so `memref n` and
`sword 64` denote to `Fin n → BitVec 64` and `BitVec 64`, matching
`catCryptDialect` exactly). -/

/-- Operation tags for the local denoting MLIR `memref` dialect. Each
    constructor corresponds to a registered MLIR `memref.*` opcode that the
    memref lowering targets. The array size `n` and access index `i : Fin n`
    are carried as parameters, mirroring `CatCryptOp`'s `memref*` ops. -/
inductive MlirMemrefOp where
  /-- `memref.alloca` of an `n`-element array initialised to zeros. -/
  | allocaZero (n : Nat)
  /-- `memref.store %v, %arr[%i]` — functional update at static index `i`. -/
  | store (n : Nat) (i : Fin n)
  /-- `memref.load %arr[%i]` — index at static index `i`. -/
  | load (n : Nat) (i : Fin n)
  deriving DecidableEq

/-! ## 2. The dialect, signature and denotation -/

/-- The local MLIR `memref` dialect: `Op` is `MlirMemrefOp`, `Ty` is `CryptoTy`
    (shared with `catCryptDialect`, so the `TyDenote CryptoTy` instance from
    `CatCryptDialect.lean` applies). -/
@[reducible] def mlirMemrefDialect : Dialect :=
  { Op := MlirMemrefOp, Ty := CryptoTy }

/-- Operation signatures: argument types + return type. Chosen to match the
    catCrypt memref op the constructor mirrors. -/
instance : DialectSignature mlirMemrefDialect where
  sig op := match op with
    | .allocaZero _ => []
    | .store n _ => [.memref n, .sword 64]
    | .load n _ => [.memref n]
  ret op := match op with
    | .allocaZero n => .memref n
    | .store n _ => .memref n
    | .load _ _ => .sword 64

/-- Operation denotation: the **standard MLIR `memref` array semantics**.
    Each clause is chosen to coincide with `catCryptDenote`'s clause for the
    op the memref lowering maps from (see §3). -/
instance mlirMemrefDenote : DialectDenote mlirMemrefDialect where
  denote op := match op with
    | .allocaZero _ => fun _ => fun _ => 0
    | .store _ i => fun args =>
        let arr : Fin _ → BitVec 64 := args.head
        let v : BitVec 64 := args.tail.head
        fun j => if j = i then v else arr j
    | .load _ i => fun args =>
        let arr : Fin _ → BitVec 64 := args.head
        arr i

/-! ## 3. Per-op semantic agreement

For each catCrypt memref op, its `DialectDenote.denote` equals the
corresponding `mlirMemrefDialect` op's `DialectDenote.denote` on the same
arguments. Because the two `DialectDenote` instances were written with matching
clauses (and identical `DialectSignature.sig`/`ret`, so the argument `HVector`
and return types coincide definitionally), every lemma closes by `rfl`.

This is the per-op analogue of the arith `agree_*` family: it certifies that
each target of the memref lowering denotes to the same function as its source.
The index `i` / size `n` are threaded through both sides, so the denotations
are literally the same function. -/

section Agreement

/-- `memrefZero n` agrees with `allocaZero n` (`memref.alloca` of zeros). -/
theorem agree_memrefZero (n : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.memrefZero n)
      = DialectDenote.denote (d := mlirMemrefDialect) (.allocaZero n) := rfl

/-- `memrefSet n i` agrees with `store n i` (`memref.store`, functional
    update at index `i`). -/
theorem agree_memrefSet (n : Nat) (i : Fin n) :
    DialectDenote.denote (d := catCryptDialect) (.memrefSet n i)
      = DialectDenote.denote (d := mlirMemrefDialect) (.store n i) := rfl

/-- `memrefGet n i` agrees with `load n i` (`memref.load`, index at `i`). -/
theorem agree_memrefGet (n : Nat) (i : Fin n) :
    DialectDenote.denote (d := catCryptDialect) (.memrefGet n i)
      = DialectDenote.denote (d := mlirMemrefDialect) (.load n i) := rfl

end Agreement

/-! ## 4. The op-correspondence and master agreement

The agreement lemmas above are the per-op crux. We package them into the op
correspondence `catToMemref` (the semantic-level counterpart of the memref
lowering) together with signature preservation and the uniform HEq agreement,
mirroring `MlirArithDialect.catToArith*`.

Only the memref fragment of `CatCryptOp` is in the domain of `catToMemref`; the
arith / algebraic-datatype / extCall ops are out of scope for a memref pass
(they have no `memref.*` target), so the translation is partial (`Option`). -/

/-- Semantic-level op correspondence: the memref fragment of `CatCryptOp`, each
    mapped to the `MlirMemrefOp` whose denotation §3 proves equal. Returns
    `none` on the non-memref ops (bit/bitvec/pair/sum/extCall/constUnit). The
    index `i` / size `n` are carried straight through, so the corresponded ops
    have coinciding denotations. -/
def catToMemref : CatCryptOp → Option MlirMemrefOp
  | .memrefZero n => some (.allocaZero n)
  | .memrefSet n i => some (.store n i)
  | .memrefGet n i => some (.load n i)
  -- Dynamic (runtime-index) memref ops: the static `MlirMemrefOp` (Fin-indexed
  -- store/load) cannot represent a runtime index, so this correspondence has no
  -- target — the dynamic ops lower to jasmin `stackLoad/stackStore` directly
  -- (DialectToJasminCom). Extending `MlirMemrefDialect` with dynamic load/store
  -- (MLIR's `memref.load/store` are inherently dynamic) is the follow-up.
  | .memrefSetDyn _ | .memrefGetDyn _ | .memrefGetDyn128 _ => none
  | .constBit _ | .constUnit | .xor | .and | .or | .not | .eqBit
  | .mkPair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _
  | .bvConst _ _ | .bvXor _ | .bvAnd _ | .bvOr _ | .bvNot _ | .bvAdd _
  | .bvSub _ | .bvMul _ | .bvEq _ | .bvShiftL _ _ | .bvShiftR _ _
  | .bvRor _ _ | .bvRol _ _ | .bvShiftRA _ _ | .andn _
  | .bvShiftLV _ | .bvShiftRV _
  | .ite _ | .bitToSword _ | .extCall _ _ _
  | .bvAdd64 _ | .bvAdc _
  | .bvMulHi _ | .bvAddCarryLo _ | .bvAddCarryHi _
  | .vsimd _ | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _ | .vpslldqC _
  | .vconst128 _
  | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2
  | .sampleBit | .sampleBv _ => none

/-- The semantic op-correspondence `catToMemref` preserves signatures: when it
    succeeds, source and target have the same argument types and return type.
    (Definitional — every successful case has matching `sig`/`ret` by
    construction.) -/
theorem catToMemref_sig (op : CatCryptOp) (op' : MlirMemrefOp)
    (h : catToMemref op = some op') :
    DialectSignature.sig (d := catCryptDialect) op
      = DialectSignature.sig (d := mlirMemrefDialect) op'
    ∧ DialectSignature.ret (d := catCryptDialect) op
      = DialectSignature.ret (d := mlirMemrefDialect) op' := by
  cases op <;>
    simp only [catToMemref, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact ⟨rfl, rfl⟩

/-- **Master per-op agreement.** Whenever `catToMemref` succeeds with `op'`,
    the two dialects denote `op` and `op'` to the same function. This is the
    uniform statement of §3, discharged by case analysis (each case `rfl`). It
    is the single hypothesis a full `Com→Com` preservation proof consumes.

    The dependent rewrite is along `catToMemref_sig`, transporting the
    `mlirMemrefDialect` denotation back to the source op's argument/return
    types. -/
theorem catToMemref_denote (op : CatCryptOp) (op' : MlirMemrefOp)
    (h : catToMemref op = some op') :
    HEq (DialectDenote.denote (d := catCryptDialect) op)
        (DialectDenote.denote (d := mlirMemrefDialect) op') := by
  cases op <;>
    simp only [catToMemref, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact HEq.rfl

/-! ## 5. Variable / argument transport between the two dialects

Both dialects share `Ty = CryptoTy`, so `Ctxt` and `Ctxt.Valuation` are
*literally the same* types on either side. The one piece that is *not*
definitionally shared is `Ctxt.Var`: it is an inductive indexed by the
`Dialect` value, so `Var catCryptDialect Γ t` and `Var mlirMemrefDialect Γ t`
are distinct types even though their constructors mention only `d.Ty`. We
bridge them with a structural transport `varCM`, which lookup respects
(`varCM_lookup`). The argument `HVector` is bridged pointwise by `argsCM`,
which `lookupArgs` respects (`argsCM_lookup`). These collapse the only
nontrivial transport in the pass. (Re-derived locally, mirroring the arith
file.) -/

/-- Transport a De Bruijn variable from the `catCryptDialect` indexing to the
    `mlirMemrefDialect` one. Structural identity (`here ↦ here`,
    `there ↦ there`); needed only because `Ctxt.Var` is indexed by the whole
    `Dialect` value. -/
def varCM {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    Ctxt.Var (d := catCryptDialect) Γ t → Ctxt.Var (d := mlirMemrefDialect) Γ t
  | .here => .here
  | .there v => .there (varCM v)

/-- Looking up a transported variable in a (shared) valuation gives the same
    value as looking up the original. By induction on the variable. -/
theorem varCM_lookup {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (v : Ctxt.Var (d := catCryptDialect) Γ t) (V : Ctxt.Valuation Γ) :
    (varCM v).lookup V = v.lookup V := by
  induction v with
  | here => cases V; rfl
  | there v ih => cases V; exact ih _

/-- Transport an `HVector` of `catCryptDialect` variables to one of
    `mlirMemrefDialect` variables over the same index list, pointwise via
    `varCM`. -/
def argsCM {Γ : Ctxt catCryptDialect} :
    {tys : List CryptoTy} →
    HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := mlirMemrefDialect) Γ ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (varCM v) (argsCM rest)

/-- Resolving a transported argument vector against a valuation gives the same
    resolved `HVector` of values as the original. By induction on the list /
    vector, using `varCM_lookup` per entry. -/
theorem argsCM_lookup {Γ : Ctxt catCryptDialect} :
    {tys : List CryptoTy} →
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys) →
    (V : Ctxt.Valuation Γ) →
    Expr.lookupArgs (d := mlirMemrefDialect) (argsCM args) V
      = Expr.lookupArgs (d := catCryptDialect) args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((varCM v).lookup V)
        (Expr.lookupArgs (d := mlirMemrefDialect) (argsCM rest) V) = _
      rw [varCM_lookup, argsCM_lookup rest V]
      rfl

/-- Heterogeneous congruence for the two op denotations applied to transported
    arguments. Stated fully generically over the (free) argument-type lists
    `s`/`s'` and return types `r`/`r'`, so the type equalities `hty`/`hr` are
    `cases`-eliminable: once substituted, the function HEq `hf` and the
    `argsCM_lookup` agreement of the resolved arguments collapse the goal to a
    plain `congrArg`. This is the single dependent-transport step in the pass. -/
theorem denote_cong {Γ : Ctxt catCryptDialect}
    {s s' : List CryptoTy} {r r' : CryptoTy}
    (f : HVector (fun t => ⟦t⟧) s → ⟦r⟧)
    (g : HVector (fun t => ⟦t⟧) s' → ⟦r'⟧)
    (hty : s = s') (hr : r = r') (hf : HEq f g)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) s)
    (V : Ctxt.Valuation Γ) :
    HEq (g (Expr.lookupArgs (d := mlirMemrefDialect) (hty ▸ argsCM args) V))
        (f (Expr.lookupArgs (d := catCryptDialect) args V)) := by
  cases hty
  cases hr
  cases hf
  exact heq_of_eq (congrArg f (argsCM_lookup args V))

/-! ## 6. Constructive `Com → Com` translation -/

/-- Translate a single `catCryptDialect` expression to a `mlirMemrefDialect`
    expression at the **same** context and return type. Looks the op up in
    `catToMemref`; on a non-memref op returns `none`. On success it rebuilds the
    `Expr`, transporting the argument `HVector` (pointwise via `argsCM`, then
    along the arg-type-list equality) and the return-type witness along the
    signature-preservation fact `catToMemref_sig`. -/
def translateExpr {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) : Option (Expr mlirMemrefDialect Γ t) :=
  match h : catToMemref e.op with
  | none => none
  | some op' =>
      let hsig := catToMemref_sig e.op op' h
      some { op := op'
             retTy_eq := hsig.2 ▸ e.retTy_eq
             args := hsig.1 ▸ argsCM e.args }

/-- Translate a `catCryptDialect` program to a `mlirMemrefDialect` program at the
    same context and return type. `.ret v ↦ .ret (varCM v)`. `.var e body ↦
    .var e' body'` once both `translateExpr e` and the recursive `translate body`
    succeed; `none` if any bound op is non-memref. -/
def translate : {Γ : Ctxt catCryptDialect} → {t : CryptoTy} →
    Com catCryptDialect Γ t → Option (Com mlirMemrefDialect Γ t)
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
equally, via `catToMemref_denote` + `argsCM_lookup`) with the induction
hypothesis on the body. Because the types coincide (both dialects share
`Ty = CryptoTy`), there is no `mapTy`/`mapCtx`, so the valuation transport is
the identity. -/

/-- Per-expression agreement: a translated expression denotes to the same value
    as its source on the same valuation. The transported `HVector` resolves to
    the same values (`argsCM_lookup`) and the op denotations agree by
    `catToMemref_denote`; the return-type / arg-type-list casts are discharged
    by substituting the signature equalities. -/
theorem translateExpr_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) (e' : Expr mlirMemrefDialect Γ t)
    (V : Ctxt.Valuation Γ) (h : translateExpr e = some e') :
    e'.denote V = e.denote V := by
  -- Destruct `e` so its `op`, `retTy_eq`, `args` fields are exposed.
  obtain ⟨op, hret, args⟩ := e
  -- It suffices to prove the heterogeneous equality.
  apply eq_of_heq
  -- Reduce `translateExpr`; the op must be memref (`some op'`).
  simp only [translateExpr] at h
  split at h
  · exact absurd h (by simp)
  · next op' hop =>
      simp only [Option.some.injEq] at h
      -- Per-op agreement (HEq of the denotations) + signature preservation.
      have hden := catToMemref_denote op op' hop
      obtain ⟨hsigArg, hsigRet⟩ := catToMemref_sig op op' hop
      subst h
      -- Peel the two `retTy_eq ▸` casts in `Expr.denote` via `eqRec_heq`, leaving
      -- the op-denotations applied to the (transported) looked-up args.
      simp only [Expr.denote]
      refine HEq.trans (eqRec_heq _ _) (HEq.trans ?_ (eqRec_heq _ _).symm)
      -- The remaining heterogeneous congruence is exactly `denote_cong`.
      exact denote_cong _ _ hsigArg hsigRet hden args V

/-- **Translation preserves denotation.** Whenever `translate c = some c'`, the
    two programs denote to the same value on every valuation. -/
theorem translate_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    (c : Com catCryptDialect Γ t) → (c' : Com mlirMemrefDialect Γ t) →
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

end CatCrypt.Crypto.SecureCompilation.VIR.MlirMemrefDialect
