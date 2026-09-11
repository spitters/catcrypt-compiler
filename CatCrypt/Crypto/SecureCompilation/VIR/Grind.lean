/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# `@[grind =]` database for VIR

Equational unfoldings of `Var.lookup`, `HVector` accessors, `Expr.lookupArgs`,
and `Com.denote` — annotated so peephole / refinement / translation
correctness proofs collapse to a one-word `grind`.

Mirrors VEIR's `Veir/IR/Grind.lean` (which uses `@[grind =_]` for iff
biconditionals around `Option.maybe`-lifted predicates); ours uses `@[grind =]`
because VIR's lemmas are direct equalities, not iffs.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

/-! ## 1. `Var.lookup` -/

namespace Ctxt

@[grind =]
theorem Var.lookup_here {d : Dialect} [TyDenote d.Ty]
    {Γ : Ctxt d} {t : d.Ty} (v : ⟦t⟧) (V : Valuation Γ) :
    Var.lookup (Γ := t :: Γ) (t := t) .here (.cons v V) = v := rfl

@[grind =]
theorem Var.lookup_there {d : Dialect} [TyDenote d.Ty]
    {Γ : Ctxt d} {s t : d.Ty} (x : Var Γ t) (v : ⟦s⟧) (V : Valuation Γ) :
    Var.lookup (Γ := s :: Γ) (t := t) (.there x) (.cons v V) = x.lookup V := rfl

end Ctxt

/-! ## 2. `HVector` basic accessors -/

namespace HVector

@[grind =]
theorem head_cons {α : Type u} {f : α → Type v} {t : α} {ts : List α}
    (x : f t) (xs : HVector f ts) : HVector.head (.cons x xs) = x := rfl

@[grind =]
theorem tail_cons {α : Type u} {f : α → Type v} {t : α} {ts : List α}
    (x : f t) (xs : HVector f ts) : HVector.tail (.cons x xs) = xs := rfl

end HVector

/-! ## 3. `Expr.lookupArgs` -/

namespace Expr

@[grind =]
theorem lookupArgs_nil {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d}
    (V : Ctxt.Valuation Γ) : lookupArgs (tys := []) .nil V = .nil := rfl

@[grind =]
theorem lookupArgs_cons {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d}
    {t : d.Ty} {tys : List d.Ty}
    (v : Ctxt.Var Γ t) (rest : HVector (fun ty => Ctxt.Var Γ ty) tys)
    (V : Ctxt.Valuation Γ) :
    lookupArgs (tys := t :: tys) (.cons v rest) V =
      .cons (v.lookup V) (lookupArgs rest V) := rfl

end Expr

/-! ## 4. `Com.denote` -/

namespace Com

@[grind =]
theorem denote_ret {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {Γ : Ctxt d} {t : d.Ty}
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ) :
    Com.denote (.ret v) V = v.lookup V := rfl

@[grind =]
theorem denote_var {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {Γ : Ctxt d} {t s : d.Ty}
    (e : Expr d Γ t) (body : Com d (t :: Γ) s) (V : Ctxt.Valuation Γ) :
    Com.denote (.var e body) V = body.denote (V.extend (e.denote V)) := rfl

end Com

/-! ## 5. `CatCryptDialect` per-op denotation

Each `catCryptDenote.denote` case unfolded to its body. Lets `grind`
discharge BitVec/peephole-style rewrites by combining these with
`HVector.head_cons` / `Var.lookup_*`. -/

namespace CatCryptDialect

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

@[grind =]
theorem denote_constBit (v : Bool) (args) :
    catCryptDenote.denote (.constBit v) args = v := rfl

@[grind =]
theorem denote_constUnit (args) :
    catCryptDenote.denote .constUnit args = () := rfl

@[grind =]
theorem denote_xor (a b : Bool) :
    catCryptDenote.denote .xor (.cons a (.cons b .nil)) = Bool.xor a b := rfl

@[grind =]
theorem denote_and (a b : Bool) :
    catCryptDenote.denote .and (.cons a (.cons b .nil)) = (a && b) := rfl

@[grind =]
theorem denote_or (a b : Bool) :
    catCryptDenote.denote .or (.cons a (.cons b .nil)) = (a || b) := rfl

@[grind =]
theorem denote_not (a : Bool) :
    catCryptDenote.denote .not (.cons a .nil) = !a := rfl

@[grind =]
theorem denote_bvXor {w} (a b : BitVec w) :
    catCryptDenote.denote (.bvXor w) (.cons a (.cons b .nil)) = a ^^^ b := rfl

@[grind =]
theorem denote_bvAnd {w} (a b : BitVec w) :
    catCryptDenote.denote (.bvAnd w) (.cons a (.cons b .nil)) = a &&& b := rfl

@[grind =]
theorem denote_bvOr {w} (a b : BitVec w) :
    catCryptDenote.denote (.bvOr w) (.cons a (.cons b .nil)) = a ||| b := rfl

@[grind =]
theorem denote_bvNot {w} (a : BitVec w) :
    catCryptDenote.denote (.bvNot w) (.cons a .nil) = ~~~a := rfl

@[grind =]
theorem denote_bvAdd {w} (a b : BitVec w) :
    catCryptDenote.denote (.bvAdd w) (.cons a (.cons b .nil)) = a + b := rfl

@[grind =]
theorem denote_bvSub {w} (a b : BitVec w) :
    catCryptDenote.denote (.bvSub w) (.cons a (.cons b .nil)) = a - b := rfl

@[grind =]
theorem denote_bvMul {w} (a b : BitVec w) :
    catCryptDenote.denote (.bvMul w) (.cons a (.cons b .nil)) = a * b := rfl

@[grind =]
theorem denote_bvConst {w} (v : BitVec w) (args) :
    catCryptDenote.denote (.bvConst w v) args = v := rfl

@[grind =]
theorem denote_bitToSword (n : Nat) (c : Bool) :
    catCryptDenote.denote (.bitToSword n) (.cons c .nil) =
      (if c then BitVec.allOnes n else 0) := rfl

@[grind =]
theorem denote_memrefGet {n : Nat} (i : Fin n)
    (arr : Fin n → BitVec 64) :
    catCryptDenote.denote (.memrefGet n i) (.cons arr .nil) = arr i := rfl

@[grind =]
theorem denote_extCall (name : String) (argTys : List CryptoTy)
    (retTy : CryptoTy) (args) :
    catCryptDenote.denote (.extCall name argTys retTy) args =
      CryptoTy.default retTy := rfl

end CatCryptDialect

end CatCrypt.Crypto.SecureCompilation.VIR
