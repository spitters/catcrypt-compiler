/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.CoreM


@[expose] public section
set_option autoImplicit false

/-!
# Multi-binder VIR — pair destructor on top of `Com` (Phase 4 #7)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`Com d Γ t` (single binder per `var`) is the substrate. Many dialect ops
return a `.pair`-typed value (e.g., `mkPair`, `cnot`/`cz` from the
quantum dialect). Consuming both components downstream forces walking
through `.fst` / `.snd` projection chains, which is awkward for proofs
(the QFT-2 SWAP completion is blocked on exactly this).

This file introduces a **destructor-side** solution: `ComMulti` adds a
`letProj` constructor that takes an *existing* variable of pair type
`Var Γ (pairTy t₁ t₂)` and unbinds both components into the body's
context. The binding source is unchanged (still `Com.var (mkPair …)`);
we just give consumers a clean way to split the pair.

A full "multi-return-binding" refactor — where `Expr` itself returns a
`List Ty` and a single `var` binds several new variables at once — would
require changes to `Expr` and `DialectSignature.ret` shape across the
codebase. That is a much bigger change, deliberately not in scope.

The companion file `MultiReturnCom.lean` (D2 skeleton, 2026-04)
addresses *returning* multiple values from a program; this file
addresses *consuming* a pair-typed binding. The two are complementary
and non-overlapping.

## `PairDialect` typeclass

Pair structure is exposed via a `PairDialect d` typeclass providing:

* `pairTy : d.Ty → d.Ty → d.Ty` — form the pair type at the dialect level
* `proj₁`, `proj₂` — first/second projection at the denotation level

Both `CatCryptDialect` and `quantumDialect` use the standard `× `
product on Lean types for `.pair`, so the instances are trivial
(`proj₁ p := p.1`, `proj₂ p := p.2`).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)

universe u v

/-! ## 1. `PairDialect` -/

/-- A dialect equipped with pair types and (Lean-level) projections.

    Required to denote `ComMulti.letProj`: the `letProj` case projects
    the pair value via `proj₁` / `proj₂`. -/
class PairDialect (d : Dialect) [TyDenote d.Ty] where
  /-- Form a pair type from two component types. -/
  pairTy : d.Ty → d.Ty → d.Ty
  /-- First projection at the denotation level. -/
  proj₁ {t₁ t₂ : d.Ty} : ⟦pairTy t₁ t₂⟧ → ⟦t₁⟧
  /-- Second projection at the denotation level. -/
  proj₂ {t₁ t₂ : d.Ty} : ⟦pairTy t₁ t₂⟧ → ⟦t₂⟧

/-! ## 2. `ComMulti`: `Com` plus a `letProj` destructor -/

/-- Programs in A-normal form with an added pair destructor.

    Carries one extra constructor over `Com`:

    * `letProj v body` — pattern-match on an existing pair-typed
      variable `v : Var Γ (pairTy t₁ t₂)`. The body extends `Γ` with
      two new bindings, ordered so that:
      - `.here` is the second component (type `t₂`)
      - `.there .here` is the first component (type `t₁`)

      This matches the convention `let (a, b) = p` where the
      most-recently-bound name (`b`) sits at de Bruijn 0. -/
inductive ComMulti (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    [PairDialect d] : Ctxt d → d.Ty → Type _ where
  /-- Return a variable. -/
  | ret {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) : ComMulti d Γ t
  /-- Let-bind an expression and continue with its result in scope.
      Identical to `Com.var`. -/
  | var {Γ : Ctxt d} {t s : d.Ty}
      (e : Expr d Γ t) (body : ComMulti d (t :: Γ) s) : ComMulti d Γ s
  /-- Project an existing pair-typed variable into its two components.
      `body` runs in `t₂ :: t₁ :: Γ`. -/
  | letProj {Γ : Ctxt d} {t₁ t₂ s : d.Ty}
      (v : Var Γ (PairDialect.pairTy t₁ t₂))
      (body : ComMulti d (t₂ :: t₁ :: Γ) s) : ComMulti d Γ s

/-! ## 3. `Com.toMulti` — trivial structural embedding -/

/-- Lift a `Com` to `ComMulti`. No `letProj` cases are produced. -/
def Com.toMulti {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [PairDialect d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → ComMulti d Γ t
  | _, _, .ret v        => .ret v
  | _, _, .var e body   => .var e body.toMulti

/-! ## 4. Pure denotation -/

namespace ComMulti

/-- Pure denotation of a `ComMulti`. Mirrors `Com.denote` plus a
    `letProj` case that splits the pair via `PairDialect.proj₁` /
    `PairDialect.proj₂` and threads the two components into the body's
    valuation (second component bound first, so it lands at `.here`). -/
def denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    [PairDialect d] :
    {Γ : Ctxt d} → {t : d.Ty} → ComMulti d Γ t → Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .ret v, V => v.lookup V
  | _, _, .var e body, V => body.denote (V.extend (e.denote V))
  | _, _, .letProj v body, V =>
      let p := v.lookup V
      body.denote ((V.extend (PairDialect.proj₁ p)).extend (PairDialect.proj₂ p))

/-! ## 5. Monadic denotation -/

/-- Monadic denotation of a `ComMulti`. Mirrors `Com.denoteM`. The
    `letProj` case has no monadic side effect of its own (the pair
    destructor is a pure lookup); it threads the components through to
    the body's monadic denotation. -/
def denoteM {d : Dialect} {M : Type → Type} [Monad M] [TyDenote d.Ty]
    [DialectSignature d] [DialectDenoteM d M] [PairDialect d] :
    {Γ : Ctxt d} → {t : d.Ty} → ComMulti d Γ t → Ctxt.Valuation Γ → M ⟦t⟧
  | _, _, .ret v, V => pure (v.lookup V)
  | _, _, .var e body, V =>
      e.denoteM V >>= fun val => body.denoteM (V.extend val)
  | _, _, .letProj v body, V =>
      let p := v.lookup V
      body.denoteM ((V.extend (PairDialect.proj₁ p)).extend (PairDialect.proj₂ p))

end ComMulti

/-! ## 6. Bridge: pure denotation preserved by `toMulti` -/

/-- `Com.toMulti` preserves the pure denotation. -/
theorem Com.denote_toMulti {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] [PairDialect d] :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ),
      c.toMulti.denote V = c.denote V
  | _, _, .ret _, _   => rfl
  | _, _, .var e body, V => by
      show body.toMulti.denote (V.extend (e.denote V)) =
           body.denote (V.extend (e.denote V))
      exact Com.denote_toMulti body (V.extend (e.denote V))

/-- `Com.toMulti` preserves the monadic denotation. -/
theorem Com.denoteM_toMulti {d : Dialect} {M : Type → Type} [Monad M]
    [TyDenote d.Ty] [DialectSignature d] [DialectDenoteM d M] [PairDialect d] :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ),
      c.toMulti.denoteM (M := M) V = c.denoteM (M := M) V
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V => by
      show e.denoteM V >>= (fun val => body.toMulti.denoteM (V.extend val)) =
           e.denoteM V >>= (fun val => body.denoteM (V.extend val))
      apply congrArg (e.denoteM V >>= ·)
      funext val
      exact Com.denoteM_toMulti body (V.extend val)

/-! ## 7. Smoke test -/

namespace SmokeTest

/-- A trivial dialect with one type (`bit`) and one binary constructor
    (`pair`), plus a "make pair" op. Self-contained so the smoke test
    doesn't depend on the heavy `CatCryptDialect` import chain. -/
inductive Ty : Type where
  | bit : Ty
  | pair : Ty → Ty → Ty
  deriving DecidableEq

/-- Lean denotation: `bit ↦ Bool`, `pair a b ↦ a × b`. -/
def Ty.denote : Ty → Type
  | .bit => Bool
  | .pair a b => a.denote × b.denote

instance : TyDenote Ty where denote := Ty.denote

/-- Op: a "make pair" combinator (specialised to two bits for simplicity).
    The dialect has only this one op. -/
inductive Op : Type where
  | mkPairBit : Op

@[reducible] def D : Dialect := { Op := Op, Ty := Ty }

instance : DialectSignature D where
  sig | .mkPairBit => [.bit, .bit]
  ret | .mkPairBit => .pair .bit .bit

instance : DialectDenote D where
  denote
  | .mkPairBit => fun args =>
      let a : Bool := args.head
      let b : Bool := args.tail.head
      (a, b)

instance : PairDialect D where
  pairTy := .pair
  proj₁ := Prod.fst
  proj₂ := Prod.snd

/-- Smoke test program: in the 2-input context `[bit, bit]` with the
    valuation `cons x (cons y nil)` we have `.here = x` (head of the
    valuation) and `.there .here = y`. We:

    1. Bind `p = mkPair (.here) (.there .here)` — i.e. `p = (x, y)`.
    2. `letProj p` — the body sees `b = .here = y` and `a = .there .here = x`.
    3. Return `.there .here = a = x`.

    Full program denotes to `x`. -/
def prog : ComMulti D [.bit, .bit] .bit :=
  .var ⟨.mkPairBit, rfl, .cons .here (.cons (.there .here) .nil)⟩ <|
  .letProj .here <|
  .ret (.there .here)

/-- The full program denotes to the first input (`x`). -/
theorem prog_denote (x y : Bool) :
    prog.denote (.cons x (.cons y .nil)) = x := by
  -- `Expr.denote` uses `retTy_eq ▸` which doesn't reduce under bare
  -- `rfl`; reduce through the projection by hand.
  show (Expr.denote
          (d := D)
          ⟨.mkPairBit, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.cons x (.cons y .nil))).1 = x
  rfl

/-- Companion: returning the second projection denotes to `y`. -/
def prog₂ : ComMulti D [.bit, .bit] .bit :=
  .var ⟨.mkPairBit, rfl, .cons .here (.cons (.there .here) .nil)⟩ <|
  .letProj .here <|
  .ret .here

theorem prog₂_denote (x y : Bool) :
    prog₂.denote (.cons x (.cons y .nil)) = y := by
  show (Expr.denote
          (d := D)
          ⟨.mkPairBit, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.cons x (.cons y .nil))).2 = y
  rfl

end SmokeTest

end CatCrypt.Crypto.SecureCompilation.VIR
