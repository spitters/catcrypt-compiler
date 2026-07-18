/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote

/-!
# `lowerLatticeToJasmin` is denotation-preserving — UNCONDITIONALLY

`LatticeToJasminDenote.lean` proves the dialect lowering
`lowerLatticeToJasmin : Com latticeDialect → Com jasminDialect` preserves
`Com.denote` *under* a leaf-agreement hypothesis `LeafAgrees`, which it leaves
open because the Jasmin `extCall` used to denote to an opaque stub.

`JasminDialect.jasminExtSem` now gives the 16-bit stack-array leaves their real,
data-oblivious semantics: the unary leaves (`ntt_*`, `ntt_invntt_*`) are the
identity, and the binary leaves are pointwise product (`ntt_basemul_*`,
`"poly_mul"`) or pointwise sum (`"poly_add"`). Those are exactly the lattice op
denotations transported across `tau` (both polynomial forms denote to
`Fin n → BitVec 16`). This file **discharges** `LeafAgrees` against that
semantics and feeds it to the parametric theorem, yielding the unconditional
preservation result and its `srcCom`/`tgtCom` corollaries.

The `if name = "poly_add"` discriminator in `jasminExtSem` reduces by `decide`
for each lattice leaf: the leaf names differ from `"poly_add"` already at a
concrete leading character (`ntt_basemul_*` at index 0, `"poly_mul"` at index 5),
so no reasoning about the embedded `toString q`/`toString n` is needed.

0 sorries. The only remaining parametric edge on the jasmin path is
`CryptoToJasminComCorrect.JasminLeafAgrees` for *genuine* external leaves
(e.g. CryptoSSA `fp_*` intrinsics), which keep the opaque default by design.
-/

set_option autoImplicit true -- SSA IR: context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote

/-! ## 1. Discharging the leaf agreement

For each lattice op `e`, the lowered Jasmin `extCall` denotes (under the
transported valuation) to `transTy` of the lattice op's denotation. Both forms
denote to `Fin n → BitVec 16` and `transTy`/`tau` are the identity transport, so
each case reduces to: the leaf semantics (identity / pointwise product / sum)
read via the total `stackGet` agrees with the lattice leaf function on in-range
indices (`stackGet_id`). -/

/-- The forward-`basemul` leaf name is never the `"poly_add"` leaf, for any
    parameters. A length argument: `"ntt_basemul_" ++ …` is at least 13 long,
    `"poly_add"` is 8. Lets the binary `jasminExtSem` discriminator (`sum` only
    for `"poly_add"`) resolve `basemul` to `product` without deciding the
    embedded `toString q`/`toString n`. -/
private theorem leafName_basemul_ne_polyAdd (q n : Nat) :
    ("ntt_basemul_" ++ toString q ++ "_" ++ toString n) ≠ "poly_add" := by
  intro h
  have hlen := congrArg String.length h
  have e1 : ("ntt_basemul_").length = 12 := by decide
  have e2 : ("_").length = 1 := by decide
  have e3 : ("poly_add").length = 8 := by decide
  simp only [String.length_append, e1, e2, e3] at hlen
  omega

/-- **Leaf agreement, discharged.** The Jasmin leaf semantics
    (`JasminDialect.jasminExtSem`) agrees with every lattice op denotation
    transported across `tau`. This is the hypothesis the parametric preservation
    theorem leaves open; with the concrete `extCall` semantics it holds. -/
theorem latticeLeafAgrees : LatticeToJasminDenote.LeafAgrees := by
  intro Γ t e V
  obtain ⟨op, hop, args⟩ := e
  cases op with
  | ntt q n =>
      cases hop
      cases args with
      | cons v args' => cases args' with
        | nil =>
            funext j
            dsimp only [lowerExpr, jasminOpOf, leafName, tau, Expr.denote,
              Expr.lookupArgs, mapVarHV, HVector.head, DialectSignature.sig,
              DialectSignature.ret, DialectDenote.denote, jasminDenote, jasminExtSem,
              latticeDenote, nttF, transTy, List.map_cons, List.map_nil]
            simp only [stackGet_id]
            show ((mapVar v).lookup (mapVal V)) j = (v.lookup V) j
            simp only [mapVal_lookup, transTy]
  | invntt q n =>
      cases hop
      cases args with
      | cons v args' => cases args' with
        | nil =>
            funext j
            dsimp only [lowerExpr, jasminOpOf, leafName, tau, Expr.denote,
              Expr.lookupArgs, mapVarHV, HVector.head, DialectSignature.sig,
              DialectSignature.ret, DialectDenote.denote, jasminDenote, jasminExtSem,
              latticeDenote, invnttF, transTy, List.map_cons, List.map_nil]
            simp only [stackGet_id]
            show ((mapVar v).lookup (mapVal V)) j = (v.lookup V) j
            simp only [mapVal_lookup, transTy]
  | basemul q n =>
      cases hop
      cases args with
      | cons va args' => cases args' with
        | cons vb args'' => cases args'' with
          | nil =>
              funext j
              dsimp only [lowerExpr, jasminOpOf, leafName, tau, Expr.denote,
                Expr.lookupArgs, mapVarHV, HVector.head, HVector.tail,
                DialectSignature.sig, DialectSignature.ret, DialectDenote.denote,
                jasminDenote, jasminExtSem, latticeDenote, basemulF, transTy,
                List.map_cons, List.map_nil]
              rw [if_neg (leafName_basemul_ne_polyAdd q n)]
              simp only [stackGet_id]
              show ((mapVar va).lookup (mapVal V)) j * ((mapVar vb).lookup (mapVal V)) j
                = (va.lookup V) j * (vb.lookup V) j
              simp only [mapVal_lookup, transTy]
  | polyAddN q n =>
      cases hop
      cases args with
      | cons va args' => cases args' with
        | cons vb args'' => cases args'' with
          | nil =>
              funext j
              dsimp only [lowerExpr, jasminOpOf, leafName, tau, Expr.denote,
                Expr.lookupArgs, mapVarHV, HVector.head, HVector.tail,
                DialectSignature.sig, DialectSignature.ret, DialectDenote.denote,
                jasminDenote, jasminExtSem, latticeDenote, polyAddNF, transTy,
                List.map_cons, List.map_nil]
              rw [if_pos rfl]
              simp only [stackGet_id]
              show ((mapVar va).lookup (mapVal V)) j + ((mapVar vb).lookup (mapVal V)) j
                = (va.lookup V) j + (vb.lookup V) j
              simp only [mapVal_lookup, transTy]
  | polyMulC q n =>
      cases hop
      cases args with
      | cons va args' => cases args' with
        | cons vb args'' => cases args'' with
          | nil =>
              funext j
              dsimp only [lowerExpr, jasminOpOf, leafName, tau, Expr.denote,
                Expr.lookupArgs, mapVarHV, HVector.head, HVector.tail,
                DialectSignature.sig, DialectSignature.ret, DialectDenote.denote,
                jasminDenote, jasminExtSem, latticeDenote, polyMulCF, invnttF,
                basemulF, nttF, transTy, List.map_cons, List.map_nil]
              rw [if_neg (by decide)]
              simp only [stackGet_id]
              show ((mapVar va).lookup (mapVal V)) j * ((mapVar vb).lookup (mapVal V)) j
                = (va.lookup V) j * (vb.lookup V) j
              simp only [mapVal_lookup, transTy]

/-! ## 2. Unconditional preservation -/

/-- **Preservation (unconditional).** The lattice→jasmin dialect lowering
    preserves `Com.denote`: the lowered Jasmin program on the transported
    valuation denotes to `transTy` of the original lattice program's denotation.
    No leaf-agreement hypothesis — it is discharged by `latticeLeafAgrees`. -/
theorem lowerLatticeToJasmin_denote_eq_uncond
    {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (com : Com latticeDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerLatticeToJasmin com).denote (mapVal V) = transTy (com.denote V) :=
  LatticeToJasminDenote.lowerLatticeToJasmin_denote_eq latticeLeafAgrees com V

/-- **Target program, unconditional.** Lowering the NTT-expanded target program
    `tgtCom q n` preserves its denotation, with no hypothesis. -/
theorem tgtCom_denote_preserved_uncond (q n : Nat)
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)).denote (mapVal V)
      = transTy ((LatticeDialect.tgtCom q n).denote V) :=
  lowerLatticeToJasmin_denote_eq_uncond (LatticeDialect.tgtCom q n) V

/-- **Source program, unconditional.** Lowering the unexpanded source program
    `srcCom q n` (a single `poly_mul`) preserves its denotation, with no
    hypothesis. -/
theorem srcCom_denote_preserved_uncond (q n : Nat)
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    (lowerLatticeToJasmin (LatticeDialect.srcCom q n)).denote (mapVal V)
      = transTy ((LatticeDialect.srcCom q n).denote V) :=
  lowerLatticeToJasmin_denote_eq_uncond (LatticeDialect.srcCom q n) V

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
