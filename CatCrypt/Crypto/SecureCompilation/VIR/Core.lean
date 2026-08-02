/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# VIR: a minimal verified MLIR-style SSA framework

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

Reimplementation of lean-mlir's core `Dialect`/`Com`/`Ctxt`/`Expr` framework,
stripped to what CatCrypt needs: single-return-type, no monadic effect kinds,
no regions, no `Qq`/reflection. Designed to be API-compatible with
opencompl/lean-mlir so we can migrate later once a v4.28.0-compatible
upstream release exists.

~300 LoC instead of upstream's ~3400; we re-expand features as we need them.

## References

* opencompl/lean-mlir (`LeanMLIR/Framework/Basic.lean`, `ErasedContext.lean`,
  `HVector.lean`): the structural ancestor.
* `CatCrypt/Crypto/SecureCompilation/CryptoSSA.lean`: already mirrors this
  framework informally; VIR makes the mirror structural.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

/-! ## 1. Dialect -/

/-- A dialect is a pair of an `Op` type (operation tags) and a `Ty` type
    (the dialect's value-type alphabet). Analogue of lean-mlir's
    `structure Dialect`. -/
structure Dialect where
  Op : Type u
  Ty : Type v

/-- Pure denotation of dialect types to Lean types. Analogue of lean-mlir's
    `TyDenote` class. -/
class TyDenote (τ : Type v) where
  denote : τ → Type

notation "⟦" t "⟧" => TyDenote.denote t

/-! ## 2. HVector (heterogeneous list) -/

/-- A heterogeneous vector indexed by a list of tags, with a type-function
    `f` giving each entry's Lean type. -/
inductive HVector {α : Type u} (f : α → Type v) : List α → Type (max u v) where
  | nil : HVector f []
  | cons {t : α} {ts : List α} : f t → HVector f ts → HVector f (t :: ts)

namespace HVector

/-- Head of a non-empty HVector. -/
def head {α : Type u} {f : α → Type v} {t : α} {ts : List α} :
    HVector f (t :: ts) → f t
  | cons x _ => x

/-- Tail of a non-empty HVector. -/
def tail {α : Type u} {f : α → Type v} {t : α} {ts : List α} :
    HVector f (t :: ts) → HVector f ts
  | cons _ xs => xs

end HVector

/-! ## 3. Typing context and variables -/

/-- A typing context: a list of dialect types, treated as a De Bruijn
    environment. Newest binding is at the head of the list. -/
abbrev Ctxt (d : Dialect) : Type v := List d.Ty

namespace Ctxt

/-- An intrinsically-typed De Bruijn variable. `Var Γ t` witnesses that
    type `t` appears in context `Γ`. -/
inductive Var {d : Dialect} : Ctxt d → d.Ty → Type v where
  /-- The most recently bound variable (de Bruijn index 0). -/
  | here {Γ : Ctxt d} {t : d.Ty} : Var (t :: Γ) t
  /-- A variable bound earlier (de Bruijn shift). -/
  | there {Γ : Ctxt d} {t s : d.Ty} : Var Γ t → Var (s :: Γ) t

/-- A valuation for a context: one value per binding, well-typed. -/
abbrev Valuation {d : Dialect} [TyDenote d.Ty] (Γ : Ctxt d) : Type :=
  HVector (fun t => ⟦t⟧) Γ

namespace Valuation

/-- Extend a valuation with a new binding. -/
def extend {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d} {t : d.Ty}
    (V : Valuation Γ) (v : ⟦t⟧) : Valuation (t :: Γ) :=
  .cons v V

end Valuation

/-- Look up a variable's value in a valuation. -/
def Var.lookup {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d} {t : d.Ty} :
    Var Γ t → Valuation Γ → ⟦t⟧
  | .here, .cons v _ => v
  | .there v, .cons _ V => v.lookup V

end Ctxt

open Ctxt (Var)

/-! ## 4. Operation signatures and denotation -/

/-- A dialect's operation signature: for each op, its argument types and
    return type. (Single-return simplification vs lean-mlir's `List`; we
    don't need multi-return for CryptoSSA-style dialects.) -/
class DialectSignature (d : Dialect) where
  sig : d.Op → List d.Ty
  ret : d.Op → d.Ty

/-- A dialect's operation denotation: for each op, a pure function from
    its typed arguments to its return value. -/
class DialectDenote (d : Dialect) [TyDenote d.Ty] [DialectSignature d] where
  denote : (op : d.Op) →
    HVector (fun t => ⟦t⟧) (DialectSignature.sig op) →
    ⟦DialectSignature.ret op⟧

/-! ## 5. Expressions and Com -/

/-- An expression: an operation applied to variables from the context. The
    `retTy = t` witness lets us index `Expr` by the expected return type. -/
structure Expr (d : Dialect) [DialectSignature d] (Γ : Ctxt d) (t : d.Ty)
    where
  op : d.Op
  retTy_eq : DialectSignature.ret op = t
  args : HVector (fun ty => Var Γ ty) (DialectSignature.sig op)

/-- A program in A-normal form. Analogue of lean-mlir's `Com`, but with
    single return type (no multi-return) and no regions. -/
inductive Com (d : Dialect) [DialectSignature d] : Ctxt d → d.Ty → Type _ where
  /-- Return a variable. -/
  | ret {Γ t} (v : Var Γ t) : Com d Γ t
  /-- Let-bind an expression and continue with its result in scope. -/
  | var {Γ t s} (e : Expr d Γ t) (body : Com d (t :: Γ) s) : Com d Γ s

/-! ## 6. Denotation of `Expr` and `Com` -/

namespace Expr

/-- Resolve an `HVector` of variables against a valuation. -/
def lookupArgs {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d} :
    {tys : List d.Ty} → HVector (fun ty => Var Γ ty) tys →
    Ctxt.Valuation Γ → HVector (fun t => ⟦t⟧) tys
  | [], .nil, _ => .nil
  | _ :: _, .cons v rest, V => .cons (v.lookup V) (lookupArgs rest V)

/-- Denotation of an expression: apply the op to its looked-up arguments. -/
def denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Ctxt.Valuation Γ) : ⟦t⟧ :=
  e.retTy_eq ▸ DialectDenote.denote e.op (lookupArgs e.args V)

end Expr

namespace Com

/-- Denotation of a program by case analysis. -/
def denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .ret v, V => v.lookup V
  | _, _, .var e body, V => body.denote (V.extend (e.denote V))

end Com

end CatCrypt.Crypto.SecureCompilation.VIR
