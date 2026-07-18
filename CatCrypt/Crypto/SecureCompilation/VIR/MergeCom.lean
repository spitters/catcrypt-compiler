/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# Direct merge translator (D2.1 approach #3)

Take two `Com d Γ t1` and `Com d Γ t2` programs that share a common
prefix of let-bindings and produce a single `MultiReturnCom d Γ
[t1, t2]` that emits both results from one program. When such a
sharing exists, the resulting MLIR has fewer `func.call`s on shared
work — directly addressing the writeup §5.5 CSE-trap.

## Strategy

Lockstep walk. At each step:
* `(.ret v1, .ret v2)` → emit `.ret (v1, v2)`. Done.
* `(.var e1 body1, .var e2 body2)` with **structurally equal** `e1`
  and `e2` (same binding type, same op, same arg-vars) → emit
  `.var e1` once and recurse on the bodies (both bodies live in
  `bs :: Γ` for the same fresh `bs`).
* Any divergence → fall back to **concat**: emit c1's tail, then
  c2's tail with all variable references shifted to skip over c1's
  freshly-bound ones, then return `(v1, v2)` (with v1 weakened).

Requires `DecidableEq d.Op` and `DecidableEq d.Ty`. `CatCryptOp` was
given `deriving DecidableEq` in `CatCryptDialect.lean`; `CryptoTy`
already had it.

## Naming pitfall

In `Com.var {Γ t s} (e : Expr d Γ t) (body : Com d (t :: Γ) s) :
Com d Γ s`, the constructor's `t` is the **binding** type (the freshly
introduced variable's type) and `s` is the **output** type. When
pattern-matching, use `(t := bs)` to bind the binding type.
`MultiReturnCom.var` similarly uses `t` for the binding type.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

open Ctxt (Var)

/-! ## 1. Context homomorphisms (renamings) -/

/-- A homomorphism from one context to another: a map on variables
preserving types. -/
abbrev Ctxt.Hom {d : Dialect} (Γ Γ' : Ctxt d) : Type _ :=
  ∀ {t : d.Ty}, Var Γ t → Var Γ' t

/-- Identity homomorphism. -/
def Ctxt.Hom.id {d : Dialect} (Γ : Ctxt d) : Ctxt.Hom Γ Γ := fun v => v

/-- Lift a homomorphism through a fresh binding `s`. -/
def Ctxt.Hom.lift {d : Dialect} {Γ Γ' : Ctxt d} {s : d.Ty}
    (h : Ctxt.Hom Γ Γ') : Ctxt.Hom (s :: Γ) (s :: Γ') := fun
  | .here => .here
  | .there v => .there (h v)

/-- Weaken-by-one. -/
def Ctxt.Hom.weakenOne {d : Dialect} (Γ : Ctxt d) (s : d.Ty) :
    Ctxt.Hom Γ (s :: Γ) := fun v => .there v

/-- Compose two homomorphisms. -/
def Ctxt.Hom.comp {d : Dialect} {Γ₁ Γ₂ Γ₃ : Ctxt d}
    (h₂ : Ctxt.Hom Γ₂ Γ₃) (h₁ : Ctxt.Hom Γ₁ Γ₂) : Ctxt.Hom Γ₁ Γ₃ :=
  fun v => h₂ (h₁ v)

/-! ## 2. Renaming on HVector / Expr / Com / MultiReturnCom -/

/-- Apply a renaming to an HVector of variables. -/
def HVector.renameVars {d : Dialect} {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') :
    {ts : List d.Ty} → HVector (fun ty => Var Γ ty) ts →
    HVector (fun ty => Var Γ' ty) ts
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (h v) (renameVars h rest)

/-- Apply a renaming to an `Expr`. -/
def Expr.rename {d : Dialect} [DialectSignature d] {Γ Γ' : Ctxt d}
    {t : d.Ty} (h : Ctxt.Hom Γ Γ') (e : Expr d Γ t) : Expr d Γ' t :=
  { op := e.op, retTy_eq := e.retTy_eq,
    args := HVector.renameVars h e.args }

/-- Apply a renaming to a `Com`. The constructor's `t` here is the
binding type (the type of the freshly introduced variable). -/
def Com.rename {d : Dialect} [DialectSignature d] :
    {Γ Γ' : Ctxt d} → {τ : d.Ty} → Ctxt.Hom Γ Γ' → Com d Γ τ →
    Com d Γ' τ
  | _, _, _, h, .ret v => .ret (h v)
  | _, _, _, h, .var (t := _) e body =>
      .var (e.rename h) (Com.rename h.lift body)

/-- Apply a renaming to a `MultiReturnCom`. -/
def MultiReturnCom.rename {d : Dialect} [DialectSignature d] :
    {Γ Γ' : Ctxt d} → {ts : List d.Ty} → Ctxt.Hom Γ Γ' →
    MultiReturnCom d Γ ts → MultiReturnCom d Γ' ts
  | _, _, _, h, .ret vs => .ret (HVector.renameVars h vs)
  | _, _, _, h, .var (t := _) e body =>
      .var (e.rename h) (MultiReturnCom.rename h.lift body)

/-! ## 3. Decidable equality on variables and arg-HVectors -/

/-- Boolean equality on variables of the same context and type. -/
def Var.beq {d : Dialect} : {Γ : Ctxt d} → {t : d.Ty} →
    Var Γ t → Var Γ t → Bool
  | _, _, .here, .here => true
  | _, _, .there v₁, .there v₂ => Var.beq v₁ v₂
  | _, _, .here, .there _ => false
  | _, _, .there _, .here => false

/-- Boolean equality on argument HVectors of the same shape. -/
def HVector.beqVars {d : Dialect} {Γ : Ctxt d} :
    {ts : List d.Ty} → (vs₁ vs₂ : HVector (fun ty => Var Γ ty) ts) → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons v₁ rest₁, .cons v₂ rest₂ =>
      Var.beq v₁ v₂ && HVector.beqVars rest₁ rest₂

/-! ## 4. Continuation-style emission of a `Com`'s let-bindings -/

/-- Emit each `.var` of `c` as a binding, then call `k` with the
captured return-variable. The continuation receives a homomorphism
`h : Γ → Γ'` so it can lift other-context variables into the final
extended context. -/
def Com.foldVar {d : Dialect} [DialectSignature d] {ts : List d.Ty} :
    {Γ : Ctxt d} → {τ : d.Ty} → Com d Γ τ →
    (∀ {Γ' : Ctxt d}, Ctxt.Hom Γ Γ' → Var Γ' τ →
       MultiReturnCom d Γ' ts) →
    MultiReturnCom d Γ ts
  | _, _, .ret v, k => k (Ctxt.Hom.id _) v
  | _, _, .var (t := bs) e body, k =>
      .var e (Com.foldVar body
        (fun {_} h v => k (h.comp (Ctxt.Hom.weakenOne _ bs)) v))

/-! ## 5. Pair-merge: concat + lockstep -/

/-- **Concatenation.** Emit c1's bindings first, then c2's bindings
with vars renamed to skip c1's results, then return `(v1, v2)`. -/
def Com.concat2 {d : Dialect} [DialectSignature d] {Γ : Ctxt d}
    {t1 t2 : d.Ty} (c1 : Com d Γ t1) (c2 : Com d Γ t2) :
    MultiReturnCom d Γ [t1, t2] :=
  Com.foldVar (ts := [t1, t2]) c1 (fun {_} h1 v1 =>
    Com.foldVar (c2.rename h1) (fun {_} h2 v2 =>
      .ret (.cons (h2 v1) (.cons v2 .nil))))

/-- **Lockstep merge.** Walk c1 and c2 in parallel, peeling off
identically-shaped `.var` heads into a single shared binding. On the
first divergence, fall back to `concat2`. -/
def Com.mergeTwo {d : Dialect} [DialectSignature d]
    [DecidableEq d.Op] [DecidableEq d.Ty] :
    {Γ : Ctxt d} → {t1 t2 : d.Ty} → Com d Γ t1 → Com d Γ t2 →
    MultiReturnCom d Γ [t1, t2]
  | _, _, _, .ret v1, .ret v2 =>
      .ret (.cons v1 (.cons v2 .nil))
  | _, _, _, .ret v1, .var e2 body2 =>
      Com.concat2 (.ret v1) (.var e2 body2)
  | _, _, _, .var e1 body1, .ret v2 =>
      Com.concat2 (.var e1 body1) (.ret v2)
  | _, _, _, .var (t := bs1) e1 body1, .var (t := bs2) e2 body2 =>
      if h_s : bs1 = bs2 then
        let e2'    : Expr d _ bs1     := h_s ▸ e2
        let body2' : Com d (bs1 :: _) _ := h_s ▸ body2
        if h_op : e1.op = e2'.op then
          let args₂ : HVector (fun ty => Var _ ty)
              (DialectSignature.sig e1.op) := h_op ▸ e2'.args
          if HVector.beqVars e1.args args₂ then
            .var e1 (Com.mergeTwo body1 body2')
          else Com.concat2 (.var e1 body1) (.var e2 body2)
        else Com.concat2 (.var e1 body1) (.var e2 body2)
      else
        Com.concat2 (.var e1 body1) (.var e2 body2)

end CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 6. Smoke test

Two trivial CatCrypt programs sharing a 2-step prefix. The merge
should peel both shared steps and emit a tuple-return at the end. -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.MergeSmoke

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

abbrev W : CryptoTy := .sword 8

def addExpr {Γ : Ctxt catCryptDialect}
    (a b : Ctxt.Var Γ W) : Expr catCryptDialect Γ W :=
  { op := .bvAdd 8, retTy_eq := rfl,
    args := .cons a (.cons b .nil) }

def subExpr {Γ : Ctxt catCryptDialect}
    (a b : Ctxt.Var Γ W) : Expr catCryptDialect Γ W :=
  { op := .bvSub 8, retTy_eq := rfl,
    args := .cons a (.cons b .nil) }

def constExpr {Γ : Ctxt catCryptDialect}
    (c : BitVec 8) : Expr catCryptDialect Γ W :=
  { op := .bvConst 8 c, retTy_eq := rfl, args := .nil }

/-- `let a = const 3; let b = const 4; let c = add a b; ret c`. -/
def prog1 : Com catCryptDialect [] W :=
  .var (constExpr 3)
    (.var (constExpr 4)
      (.var (addExpr (.there .here) .here)
        (.ret .here)))

/-- Same prefix as prog1, but `sub` instead of `add`. -/
def prog2 : Com catCryptDialect [] W :=
  .var (constExpr 3)
    (.var (constExpr 4)
      (.var (subExpr (.there .here) .here)
        (.ret .here)))

/-- The merged program. Lockstep peels `const 3` and `const 4` once
each, then concats the divergent `add`/`sub` tails. -/
def merged : MultiReturnCom catCryptDialect [] [W, W] :=
  Com.mergeTwo prog1 prog2

end CatCrypt.Crypto.SecureCompilation.VIR.MergeSmoke

/-! ## Note on rendering

To see the merged program as MLIR text, import this file together
with `CatCryptPrint.lean` (which provides the `DialectPrint`
instance for `catCryptDialect`) from a downstream file and call
`MultiReturnCom.printModule merged "merge_smoke"`. We don't render
here to avoid a circular dependency with `CatCryptPrint` (which
already imports `CryptoToVIR`, which now imports this file).

The expected output of merging `prog1` (using `bvAdd`) and `prog2`
(using `bvSub`), both prefixed by `let a = 3; let b = 4`, is:

```
func.func @merge_smoke() -> (i8, i8) {
  %0 = "arith.constant"() {value = 3 : i8} : () -> i8
  %1 = "arith.constant"() {value = 4 : i8} : () -> i8
  %2 = "arith.addi"(%0, %1) : (i8, i8) -> i8
  %3 = "arith.subi"(%0, %1) : (i8, i8) -> i8
  return %2, %3 : i8, i8
}
```

The `const 3` and `const 4` bindings appear once each (the
shared prefix), and the divergent `add`/`sub` operations both
reference the shared `%0` and `%1` rather than duplicating them. -/
