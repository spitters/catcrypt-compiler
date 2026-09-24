/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole
public import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom

/-!
# Verified copy-propagation pass for `Com` (typed VIR `jasminDialect`)

A **denotation-preserving copy-propagation `Com → Com` pass** over the typed VIR
`jasminDialect`. Copy propagation rewrites uses of a variable that was bound to a
*pure copy* of an already-in-scope variable so that they refer to the copy's
*source* directly. After this rewrite the copy binding becomes dead and a later
dead-code-elimination pass can drop it; here we keep the binding (so the De
Bruijn shape and the cost/CT facts of the surrounding chain are undisturbed) and
only redirect the body's uses.

## What counts as a copy

In the carry-free `jasminDialect` alphabet a *register copy* of a variable `a`
can be written as the idempotent self-`or` binding

    let z = a ||| a      -- z denotes exactly `a`   (`a ||| a = a`)

`a ||| a` denotes `a.lookup V` bit-for-bit (`BitVec.or_self`), so the freshly
bound `z` (`Ctxt.Var.here`) and the *shifted* source `a` (`Ctxt.Var.there a`)
look up the **same** entry of the extended valuation `V.extend (a.lookup V)`.
Replacing `z` by `a.there` throughout the body is therefore denotation-preserving
— this is the soundness core of the pass.

## The pass

`copyProp` walks the let-chain (reusing the `peepCom`-style traversal in
`Optimizer/Rewrite/Peephole.lean`). At each `.var e body`:

* if `e` is a self-`or` copy `a ||| a`, it renames every use of the bound
  variable in `body` to the shifted source `a` (via the de-Bruijn renaming
  `copyHom`, built on the `Ctxt.Hom`/`Com.rename` machinery in `MergeCom.lean`),
  then recurses;
* otherwise it leaves the binding and recurses.

## Preservation theorem

* `copyProp_denote` : `(copyProp c).denote V = c.denote V`, by induction over the
  `Com` let-chain, using the de-Bruijn substitution laws
  (`Com.denote_rename`, `pullV`) proved here on top of `Expr.denote_rename`.
  **Not** `rfl`.

The pass is conservative: it propagates **only** through a provably
denotation-preserving copy (a variable-to-variable alias), never through an
arbitrary expression. All goals closed; no open goals.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.CopyProp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## 0. De-Bruijn substitution laws (pullback valuations)

Standard intrinsically-typed substitution lemmas: looking up a renamed variable
in `V` equals looking up the original in the **pullback** of `V` along the
renaming. (Re-proved locally rather than imported, to keep this file's
dependency footprint to `MergeCom`'s `Ctxt.Hom` / `Com.rename`.) -/

/-- Pullback of a `Valuation Γ'` along a context homomorphism `h : Γ → Γ'`. -/
def pullV : {Γ : Ctxt jasminDialect} → {Γ' : Ctxt jasminDialect} →
    Ctxt.Hom Γ Γ' → Ctxt.Valuation Γ' → Ctxt.Valuation Γ
  | [], _, _, _ => HVector.nil
  | _ :: _, _, h, V =>
      HVector.cons ((h Ctxt.Var.here).lookup V)
        (pullV (fun v => h (.there v)) V)

/-- Looking up a renamed variable in `V` equals looking up the original variable
in the pullback of `V`. -/
theorem Ctxt.Var.lookup_rename {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') {t : JasminTy} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ') :
    (h v).lookup V = v.lookup (pullV h V) := by
  induction v with
  | here => rfl
  | @there Γ₀ t s w ih =>
      simp only [pullV]
      exact ih (fun v => h (.there v))

/-- Renaming arguments and looking them up against a valuation equals looking up
the original arguments against the pulled-back valuation. -/
theorem lookupArgs_renameVars {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') :
    {tys : List JasminTy} →
    (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (V : Ctxt.Valuation Γ') →
    Expr.lookupArgs (HVector.renameVars h args) V
      = Expr.lookupArgs args (pullV h V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      · exact Ctxt.Var.lookup_rename h v V
      · exact lookupArgs_renameVars h rest V

/-- Renaming an `Expr` and denoting it against `V` equals denoting the original
expression against the pulled-back valuation. -/
theorem Expr.denote_rename {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Ctxt.Valuation Γ') :
    (e.rename h).denote V = e.denote (pullV h V) := by
  cases e with
  | mk op retTy_eq args =>
      simp only [Expr.rename, Expr.denote]
      rw [lookupArgs_renameVars h args V]

/-! ## 1. `Com.denote_rename`: renaming commutes with denotation

We extend `Expr.denote_rename` to whole `Com`s. The only new ingredient is that
the pullback valuation commutes with lifting a renaming through one fresh
binding. -/

/-- Pulling back along a renaming whose image is entirely *shifted* past a fresh
binding `s` ignores the fresh entry. Stated for an arbitrary `g : Γ → Γ'`
post-composed with `weakenOne`: `pullV (weakenOne ∘ g) (V.extend x) = pullV g V`.
The de-Bruijn weakening/pullback law. -/
theorem pullV_weaken {Γ Γ' : Ctxt jasminDialect} {s : JasminTy} (x : ⟦s⟧) :
    ∀ (g : Ctxt.Hom Γ Γ') (V : Ctxt.Valuation Γ'),
      pullV (fun {_} v => Ctxt.Var.there (g v)) (V.extend x) = pullV g V
  | g, V => by
      induction Γ with
      | nil => rfl
      | cons t Γ₀ ih =>
          simp only [pullV]
          congr 1
          exact ih (fun {_} v => g (.there v))

/-- Pulling back along the identity renaming is the identity on valuations. -/
theorem pullV_id {Γ : Ctxt jasminDialect} :
    ∀ (V : Ctxt.Valuation Γ), pullV (Ctxt.Hom.id Γ) V = V := by
  induction Γ with
  | nil => intro V; cases V; rfl
  | cons t Γ₀ ih =>
      intro V
      cases V with
      | cons v0 Vrest =>
          simp only [pullV]
          congr 1
          -- tail: pullV (fun v => id (.there v)) (cons v0 Vrest) = Vrest
          show pullV (fun {_} v => Ctxt.Var.there (Ctxt.Hom.id Γ₀ v))
                (Ctxt.Valuation.extend Vrest v0) = Vrest
          rw [pullV_weaken v0 (Ctxt.Hom.id Γ₀) Vrest]
          exact ih Vrest

/-- Pulling a *lifted* renaming back through an extended valuation equals
extending the pulled-back valuation. (The de-Bruijn lift/pullback compatibility
law.) -/
theorem pullV_lift {Γ Γ' : Ctxt jasminDialect} (h : Ctxt.Hom Γ Γ')
    {s : JasminTy} (V : Ctxt.Valuation Γ') (x : ⟦s⟧) :
    pullV (h.lift) (V.extend x) = (pullV h V).extend x := by
  simp only [pullV, Ctxt.Valuation.extend]
  congr 1
  -- tail: pullV (fun v => h.lift (.there v)) (V.extend x) = pullV h V
  show pullV (fun {_} v => Ctxt.Hom.lift h (.there v)) (V.extend x) = pullV h V
  exact pullV_weaken x h V

/-- **Renaming commutes with `Com` denotation.** Denoting a renamed `Com`
against `V` equals denoting the original against the pulled-back valuation.
By induction over the let-chain; the binder case uses `pullV_lift` and
`Expr.denote_rename`. **Not** `rfl`. -/
theorem Com.denote_rename {Γ Γ' : Ctxt jasminDialect} {τ : JasminTy} :
    ∀ (h : Ctxt.Hom Γ Γ') (c : Com jasminDialect Γ τ) (V : Ctxt.Valuation Γ'),
      (c.rename h).denote V = c.denote (pullV h V)
  | h, .ret v, V => by
      simp only [Com.rename, Com.denote]
      exact Ctxt.Var.lookup_rename h v V
  | h, .var e body, V => by
      simp only [Com.rename, Com.denote]
      rw [Expr.denote_rename h e V]
      rw [Com.denote_rename h.lift body (V.extend (e.denote (pullV h V)))]
      rw [pullV_lift h V (e.denote (pullV h V))]

/-! ## 2. Detecting a self-`or` copy

A `.var`-bound expression is a register copy of `a` when it is `binE .or a a`
(equivalently `a ||| a`). `isCopy` returns the source variable `a` if the
expression has that exact shape. -/

/-- If a `bs`-typed binding `e` is the self-`or` register copy `a ||| a`, return
`some a`. For any other binding type or expression shape, return `none`. The
return type matches the binding type `bs`, so the redirect renaming `copyHom`
applies directly. -/
def isCopy {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (e : Expr jasminDialect Γ bs) : Option (Ctxt.Var Γ bs) :=
  match e with
  | ⟨.regArith bop _, hop, args⟩ =>
      match bop with
      | .or =>
          let a := args.head
          let b := args.tail.head
          if varEq a b then some (hop ▸ a) else none
      | _ => none
  | _ => none

/-- **Soundness of `isCopy`.** If `isCopy e = some a` then `e` denotes exactly
`a.lookup V` (the copy is a faithful alias of `a`). -/
theorem isCopy_denote {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (e : Expr jasminDialect Γ bs) (a : Ctxt.Var Γ bs)
    (V : Ctxt.Valuation Γ) (he : isCopy e = some a) :
    e.denote V = a.lookup V := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w' =>
      cases hop
      match args, (rfl : args = args) with
      | .cons x (.cons y .nil), _ =>
        cases bop
        case or =>
          simp only [isCopy, HVector.head, HVector.tail] at he
          by_cases hv : varEq x y
          · have hxy : x = y := varEq_sound x y hv
            subst hxy
            simp only [hv, if_true, Option.some.injEq] at he
            subst he
            show (binE .or x x).denote V = x.lookup V
            rw [binE_denote]
            simp [JasminBinOp.apply]
          · simp only [hv, Bool.false_eq_true, if_false] at he
            exact absurd he (by simp)
        all_goals
          (simp only [isCopy] at he
           exact absurd he (by simp))
  | stackLoad w n => simp only [isCopy] at he; exact absurd he (by simp)
  | stackStore w n => simp only [isCopy] at he; exact absurd he (by simp)
  | castW w w' => simp only [isCopy] at he; exact absurd he (by simp)
  | extCall nm aa r => simp only [isCopy] at he; exact absurd he (by simp)
  | regConst w n => simp only [isCopy] at he; exact absurd he (by simp)
  | vpackZMM bop => simp only [isCopy] at he; exact absurd he (by simp)
  | vpackZMMd bop => simp only [isCopy] at he; exact absurd he (by simp)
  | vprordZMM n => simp only [isCopy] at he; exact absurd he (by simp)
  | vpslldq n => simp only [isCopy] at he; exact absurd he (by simp)
  | vpsrldq n => simp only [isCopy] at he; exact absurd he (by simp)
  | vsimd op => simp only [isCopy] at he; exact absurd he (by simp)
  | vymm op => simp only [isCopy] at he; exact absurd he (by simp)
  | mulhi w => simp only [isCopy] at he; exact absurd he (by simp)
  | addCarryLo w => simp only [isCopy] at he; exact absurd he (by simp)
  | addCarryHi w => simp only [isCopy] at he; exact absurd he (by simp)
  | rorImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | shrImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | sarImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | shlImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | select w => simp only [isCopy] at he; exact absurd he (by simp)
  | callN name argTys retTys => simp only [isCopy] at he; exact absurd he (by simp)
  | cmp c w => simp only [isCopy] at he; exact absurd he (by simp)
  | cmpImm c w n => simp only [isCopy] at he; exact absurd he (by simp)

/-! ## 3. The redirecting renaming

When the head binding `let z = a ||| a` is a copy of `a`, the body lives in
context `reg w :: Γ`. We redirect the bound variable `z` (`.here`) to the
shifted source `a.there`, leaving every other variable fixed. -/

/-- The de-Bruijn renaming that redirects the just-bound variable `.here` to the
shifted source `a.there`, and is the identity on every other variable. Stated
for an arbitrary binding type `bs` (the redirect logic does not depend on the
type being a register). -/
def copyHom {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (a : Ctxt.Var Γ bs) : Ctxt.Hom (bs :: Γ) (bs :: Γ) := fun
  | .here => .there a
  | .there v => .there v

/-- **The redirect is a no-op on the aliasing valuation.** When the freshly
bound entry is `a.lookup V`, pulling back along `copyHom a` returns the same
extended valuation — the bound entry and `a.there` agree. -/
theorem pullV_copyHom {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (a : Ctxt.Var Γ bs) (V : Ctxt.Valuation Γ) :
    pullV (copyHom a) (V.extend (a.lookup V)) = V.extend (a.lookup V) := by
  simp only [pullV, Ctxt.Valuation.extend]
  congr 1
  -- tail: pullV (fun v => copyHom a (.there v)) (V.extend (a.lookup V)) = V
  -- on `.there v`, `copyHom a` is `.there`, i.e. `weakenOne ∘ id`.
  show pullV (fun {_} v => Ctxt.Var.there (Ctxt.Hom.id Γ v))
        (V.extend (a.lookup V)) = V
  rw [pullV_weaken (a.lookup V) (Ctxt.Hom.id Γ) V]
  exact pullV_id V

/-! ## 4. The copy-propagation pass

`copyProp` walks the let-chain. At each `.var e body` whose return type is a
register `reg w`, if `e` is a self-`or` copy of some source variable `a`, it
renames every use of the bound variable in `body` to the shifted source
`a.there` (`copyHom a`) and recurses; otherwise it recurses unchanged. The copy
binding itself is retained (a later DCE pass drops it). -/

/-- One copy-propagation pass over a `Com`. At each `.var e body`: if `e` is a
register copy of a source variable `a`, redirect every use of the bound variable
in `body` to the shifted source `a` (via `copyHom a`) and recurse; otherwise
recurse unchanged. The copy binding is retained for a later DCE pass to drop. -/
def copyProp {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | .ret v => .ret v
  | .var e body =>
      match isCopy e with
      | some a => .var e ((copyProp body).rename (copyHom a))
      | none   => .var e (copyProp body)

/-- **Denotation preservation for copy propagation.** `copyProp c` denotes the
same function as `c`. By induction over the `Com` let-chain; the copy case uses
`isCopy_denote`, `Com.denote_rename` and `pullV_copyHom`. **Not** `rfl`. -/
theorem copyProp_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      (copyProp c).denote V = c.denote V
  | .ret v, _ => rfl
  | .var e body, V => by
      show (match isCopy e with
            | some a => Com.var e ((copyProp body).rename (copyHom a))
            | none   => Com.var e (copyProp body)).denote V
            = (Com.var e body).denote V
      rcases hc : isCopy e with _ | a
      · -- no copy: structural recurse
        simp only [Com.denote]
        exact copyProp_denote body (V.extend (e.denote V))
      · -- copy of `a`: e.denote V = a.lookup V, and the rename is a no-op
        simp only [Com.denote]
        rw [Com.denote_rename (copyHom a) (copyProp body) (V.extend (e.denote V))]
        rw [isCopy_denote e a V hc]
        rw [pullV_copyHom a V]
        exact copyProp_denote body (V.extend (a.lookup V))

/-! ## 5. Self-contained validation

A small `Com jasminDialect [reg 32] (reg 32)` exercising copy propagation:

    let z = x ||| x      -- z is a register copy of x  (`x ||| x = x`)
    let w = z + z        -- uses the copy z
    ret w

`copyProp` redirects the uses of `z` in the body to the shifted source `x`
(leaving the now-dead `z` binding in place for a later DCE pass). Denotation is
preserved: both programs map `x` to `x + x`. -/

/-- The copy demo: `let z = x ||| x; let w = z + z; ret w`. -/
def demoCopy : Com jasminDialect [.reg 32] (.reg 32) :=
  .var (binE .or .here .here)          -- z = x ||| x   (x is `.here`)
    (.var (binE .add .here .here)      -- w = z + z     (z is `.here`)
      (.ret .here))

/-- **Denotation preserved** for the copy demo, via `copyProp_denote`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (copyProp demoCopy).denote V = demoCopy.denote V :=
  copyProp_denote demoCopy V

/-- Concretely, on `x = 21`, both denote `42` (`= 21 + 21`). -/
example : demoCopy.denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

example :
    (copyProp demoCopy).denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) :=
  rfl

/-- The pass actually redirects: in the rewritten body the `add` reads the
shifted source `x` (`.there .here`) rather than the copy `z` (`.here`). -/
example : copyProp demoCopy =
    Com.var (binE .or .here .here)
      (Com.var (binE .add (.there .here) (.there .here)) (.ret .here)) := by
  rfl

/-- A `ret` program is unchanged. -/
example : copyProp (Com.ret (Γ := [JasminTy.reg 8]) (t := JasminTy.reg 8) .here)
    = Com.ret .here := rfl

end CatCrypt.Crypto.Optimizer.CopyProp
