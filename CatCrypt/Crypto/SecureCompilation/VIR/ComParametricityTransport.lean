/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# `Com`-parametricity fundamental lemma: per-op leaf transport lifts to whole-program transport

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A dialect lowering pass `lower : Com d Γ t → Com d' (mapΓ) (mapTy t)` is
*denotation-preserving* exactly when its whole-program transport square commutes:
`(lower c).denote (mapVal V) = transTy (c.denote V)`. This file proves the
**fundamental lemma** of `Com`-parametricity: for a *structural* lowering — one
that recurses over the `Com.ret` / `Com.var` skeleton, rewriting each operation
leaf locally — the whole-`Com` square **follows by induction** from
1. the per-operation leaf squares (each `Expr` lowering transports), and
2. the structural coherences (variables transport by `mapVal`, binding threads
   the transport through `Valuation.extend`).

This is a structural induction over the same skeleton as the constant-time checker
`ComLevelCheck.levelCheck_sound`
and of the `owned_fold` combinators (which discharge an `N`-fold induction once).
Where those fold a CT/leak property, this folds the *value transport* itself,
phrased in the composable `Related`-square ("commuting square") vocabulary of
`Bridges/ReprTransfer` (`BinOpHomOn.app_eq`, `BinOpRealization.commutes`).

The payoff for each MLIR-lowering pass is: prove only your instruction leaves
(`OpLowerTransports`) and obtain whole-program preservation
(`ComLowerTransports`) for free — the "MLIR-lowering-as-Trocq-transport" plan,
Phase 1.

## Scope

* The lemma is **generic over the dialects and the lowering**: it is parametric
  in the source dialect `d`, the target dialect `d'`, the type map `mapTy`, the
  per-binding context map, the value transport `transTy`, the variable map, and
  the per-expression lowering. Any structural pass instantiates it.
* "Structural" is made precise: the `Com` lowering is the *canonical* one built
  from a variable map and an expression lowering
  (`StructuralLowering.lowerCom`), threading `ret ↦ ret ∘ mapVar` and
  `var e body ↦ var (lowerExpr e) (lowerCom body)`. This is the homomorphic
  (single-op-to-block, leaf-local) shape that covers per-op MLIR rewrites. A
  lowering that *reassociates* binders (splits one op into several, or fuses) is
  not of this canonical shape; the explicit coherence hypotheses below state
  exactly what such a pass would additionally have to provide.
* The two leaf coherences are stated as **explicit hypotheses**, not hidden:
  `VarTransports` (variables transport across `mapVal`) and `OpLowerTransports`
  (each lowered expression transports, with the bound value threaded through
  `Valuation.extend`). No side condition is left unstated.

**All goals closed**; target axiom set `{propext, Classical.choice, Quot.sound}` (the
ambient Mathlib/Core set), with **no** `jasminc_preserves_ct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt

universe u v

/-! ## 1. The data of a structural lowering

A structural lowering between dialects `d` and `d'` is given by a type map, a
context map compatible with it, a value transport, a variable map, and a
per-expression lowering. From these the `Com` lowering is *determined* by the
canonical structural recursion. -/

/-- The static (type-level + syntactic) data of a structural `Com` lowering from
    dialect `d` to dialect `d'`.

    * `mapTy` / `mapCtx` : the type and context maps (we keep `mapCtx` abstract
      rather than forcing `List.map mapTy`, so passes that reshape the context —
      e.g. inserting scratch bindings — still fit, as long as they provide the
      coherences below).
    * `mapVar` : transports a source variable to a target variable over the
      mapped context.
    * `lowerExpr` : lowers each source expression to a target expression of the
      mapped return type over the mapped context. -/
structure LoweringData (d d' : Dialect) [DialectSignature d] [DialectSignature d']
    where
  /-- Type map on the dialect type alphabets. -/
  mapTy : d.Ty → d'.Ty
  /-- Context map (kept abstract so context-reshaping passes still fit). -/
  mapCtx : Ctxt d → Ctxt d'
  /-- The mapped context of a `cons` is the `cons` of the mapped head onto the
      mapped tail — the structural compatibility that lets binding thread. -/
  mapCtx_cons : ∀ (t : d.Ty) (Γ : Ctxt d), mapCtx (t :: Γ) = mapTy t :: mapCtx Γ
  /-- Variable transport. -/
  mapVar : ∀ {Γ : Ctxt d} {t : d.Ty}, Var Γ t → Var (mapCtx Γ) (mapTy t)
  /-- Per-expression lowering: each source `Expr` becomes a target `Expr` of the
      mapped return type. (The leaf rewrite.) -/
  lowerExpr : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Expr d' (mapCtx Γ) (mapTy t)

namespace LoweringData

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']

/-- **The canonical structural `Com` lowering.** Recurses over the
    `ret` / `var` skeleton: a return becomes the mapped variable, a let-binding
    becomes the lowered expression bound ahead of the lowered body. This is the
    *definition* of "structural lowering" the fundamental lemma is about. -/
def lowerCom (L : LoweringData d d') :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Com d' (L.mapCtx Γ) (L.mapTy t)
  | _, _, .ret v => .ret (L.mapVar v)
  | Γ, _, .var (t := t) e body =>
      .var (L.lowerExpr e)
        (L.mapCtx_cons t Γ ▸ L.lowerCom body)

end LoweringData

/-! ## 2. The semantic transport data and the leaf squares

To denote both sides we need `TyDenote` + `DialectDenote` on each dialect, a
value transport `transTy`, and a valuation transport `mapVal`. The two leaf
coherences — `VarTransports` and `OpLowerTransports` — are the per-op squares the
pass must prove; everything else is the structural induction. -/

variable {d d' : Dialect}
variable [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
variable [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

/-- The value transport `⟦t⟧ → ⟦mapTy t⟧` carried by a lowering: how a source
    value of type `t` is realized as a target value of type `mapTy t`. -/
abbrev TransTy (L : LoweringData d d') :=
  ∀ {t : d.Ty}, ⟦t⟧ → ⟦L.mapTy t⟧

/-- The valuation transport `Valuation Γ → Valuation (mapCtx Γ)` carried by a
    lowering: how a source input environment is realized as a target one. -/
abbrev MapVal (L : LoweringData d d') :=
  ∀ {Γ : Ctxt d}, Valuation Γ → Valuation (L.mapCtx Γ)

/-- **Variable-transport coherence (the `ret`/`var` leaf at the value level).**
    Looking up the mapped variable in the mapped valuation equals transporting
    the source lookup. This is the reflexivity-flavoured half of structural
    parametricity: variables carry no computation, so their transport is forced
    by `mapVal`/`transTy`. It is exactly what the `ret` case of the fundamental
    lemma needs, and (threaded through `extend`) what closes binder lookups. -/
def VarTransports (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L) :
    Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) (V : Valuation Γ),
    (L.mapVar v).lookup (mapVal V) = transTy (v.lookup V)

/-- **Per-operation leaf transport (`OpLowerTransports`).** For *every* source
    expression `e` and input valuation `V`, the lowered expression denotes (under
    the mapped valuation) to the transport of `e`'s denotation. This is a
    commuting square in the `Related` sense (cf. `BinOpHomOn.app_eq`,
    `BinOpRealization.commutes`): `lowerExpr` is a homomorphism along
    `transTy`/`mapVal`.

    This is the **only op-specific obligation** a pass must discharge —
    one square per instruction leaf. The fundamental lemma lifts it to the whole
    program. To make binding thread, the coherence additionally fixes how the
    *extended* mapped valuation is formed: extending the mapped valuation by the
    lowered expression's value equals mapping the source-extended valuation
    (`mapVal_extend` below packages this). -/
def OpLowerTransports (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L) :
    Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
    (L.lowerExpr e).denote (mapVal V) = transTy (e.denote V)

/-- **Binding-threading coherence.** Mapping a source-extended valuation equals
    extending the mapped valuation by the transport of the bound value, modulo
    the `mapCtx_cons` reindexing. This is the one structural side condition that
    a context-reshaping pass would have to supply; for the standard
    `mapCtx = List.map mapTy`, `mapVal = HVector.map transTy` shape it holds
    definitionally. We keep it explicit rather than baking in a representation. -/
def MapValExtends (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L) :
    Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (V : Valuation Γ) (x : ⟦t⟧),
    mapVal (Valuation.extend V x)
      = (L.mapCtx_cons t Γ ▸ Valuation.extend (mapVal V) (transTy x))

/-! ## 3. The whole-program transport square -/

/-- **`ComLowerTransports`** — the whole-`Com` transport square for a single
    program `c`: the lowered program denotes (under any mapped input valuation)
    to the transport of the source denotation. This is the goal the fundamental
    lemma delivers for every `c` from the per-op leaves. -/
def ComLowerTransports (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) : Prop :=
  ∀ V : Valuation Γ, (L.lowerCom c).denote (mapVal V) = transTy (c.denote V)

/-! ## 4. The fundamental lemma -/

/-- **Fundamental lemma of `Com`-parametricity (per-op leaves lift to the whole
    program).** For a structural lowering `L`, if every variable transports
    (`VarTransports`), every operation leaf transports
    (`OpLowerTransports`), and binding threads the transport
    (`MapValExtends`), then **every** program transports
    (`ComLowerTransports`): the whole-`Com` denotation-preservation square
    commutes for all `c`.

    Proved by induction on the `Com` skeleton:
    * `ret` case = `VarTransports` (the variable leaf);
    * `var` case = `OpLowerTransports` (the op leaf) composed with the IH on the
      body, glued by `MapValExtends` threading the bound value through
      `Valuation.extend`.

    This is the Phase-1 result: a pass proves only its instruction leaves and
    gets whole-program preservation for free. It is generic over both dialects
    and the lowering. -/
theorem fundamental
    (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : OpLowerTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t),
      ComLowerTransports L transTy mapVal c
  | _, _, .ret v => by
      intro V
      simpa [LoweringData.lowerCom, Com.denote] using hVar v V
  | Γ, _, .var (t := t) e body => by
      intro V
      -- Lowered program: `.var (lowerExpr e) (mapCtx_cons ▸ lowerCom body)`.
      -- Source program: `.var e body`, denote = `body.denote (V.extend (e.denote V))`.
      show (L.lowerCom (.var e body)).denote (mapVal V) = _
      simp only [LoweringData.lowerCom, Com.denote]
      -- The bound target value is `(lowerExpr e).denote (mapVal V) = transTy (e.denote V)`.
      have hleaf : (L.lowerExpr e).denote (mapVal V) = transTy (e.denote V) := hOp e V
      -- The IH on the body, instantiated at the extended source valuation.
      have IH := fundamental L transTy mapVal hVar hOp hExt body
        (Valuation.extend V (e.denote V))
      -- Thread: extending the mapped valuation by the lowered value = mapping the
      -- source-extended valuation (modulo `mapCtx_cons`).
      have hext := hExt V (e.denote V)
      -- Close by rewriting along the three coherences.
      rw [hleaf]
      -- After `rw [hleaf]`, the bound value is `transTy (e.denote V)`; `hext` and
      -- `IH` align the body denotations through the `mapCtx_cons` transport.
      grind [LoweringData.lowerCom, Com.denote]

/-! ## 5. Validation: re-derive a whole-program square from per-op leaves alone

To show the fundamental lemma is **usable, not vacuous**, we instantiate it at a
concrete lowering and watch the whole-`Com` square pop out from the per-op
hypotheses. We use a one-operation toy dialect and its identity self-lowering:
the per-op leaf and per-var coherences are each a one-line `rfl`-style fact, and
`fundamental` lifts them to *every* program over the dialect — including a
multi-binding one — with no further induction by hand. The same instantiation
shape is what a real per-op MLIR pass uses (it supplies `lowerExpr` and proves
`OpLowerTransports` per instruction; everything else is this lemma). -/

namespace Validation

/-- A one-type, one-operation toy dialect: type `()`, a single binary op `dup`
    whose denotation is the identity on `Nat` (`dup x y = x`). Just enough
    structure to host a non-trivial `Com` with several bindings. -/
def toyDialect : Dialect where
  Op := Unit
  Ty := Unit

instance : TyDenote toyDialect.Ty where
  denote := fun _ => Nat

instance : DialectSignature toyDialect where
  sig := fun _ => [(), ()]
  ret := fun _ => ()

instance : DialectDenote toyDialect where
  denote := fun _ args => args.head

/-- The identity self-lowering of `toyDialect`: every map is the identity, every
    leaf rewrite is the identity expression. This is the simplest *concrete*
    lowering; a real pass differs only in supplying a non-trivial `lowerExpr`. -/
def idLowering : LoweringData toyDialect toyDialect where
  mapTy := id
  mapCtx := id
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => v
  lowerExpr := fun e => e

/-- The identity value transport. -/
def idTransTy : TransTy idLowering := fun x => x

/-- The identity valuation transport. -/
def idMapVal : MapVal idLowering := fun V => V

/-- **Per-var leaf (validation).** Variables transport — here by `rfl`, since
    every map is the identity. One line; no induction. -/
theorem idVarTransports : VarTransports idLowering idTransTy idMapVal :=
  fun _ _ => rfl

/-- **Per-op leaf (validation) — the only op-specific obligation.**
    Each lowered expression transports. Here the lowering is the identity, so the
    square is `rfl`. A real pass discharges this per instruction; `fundamental`
    does the rest. -/
theorem idOpLowerTransports : OpLowerTransports idLowering idTransTy idMapVal :=
  fun _ _ => rfl

/-- **Binding-threading (validation).** Mapping the extended valuation = extending
    the mapped valuation — `rfl` for the identity transport. -/
theorem idMapValExtends : MapValExtends idLowering idTransTy idMapVal :=
  fun _ _ => rfl

/-- **The whole-program square, derived from the per-op leaves alone.** This is
    `fundamental` applied to the three one-line leaf facts above: for *every*
    program `c` over `toyDialect` — of arbitrary binding depth — the identity
    lowering preserves denotation. No induction is performed here; the
    fundamental lemma supplies it. This witnesses that the lemma is non-vacuous
    and usable: leaves in, whole program out. -/
theorem idComLowerTransports {Γ : Ctxt toyDialect} {t : toyDialect.Ty}
    (c : Com toyDialect Γ t) :
    ComLowerTransports idLowering idTransTy idMapVal c :=
  fundamental idLowering idTransTy idMapVal
    idVarTransports idOpLowerTransports idMapValExtends c

/-- A concrete two-binding program over `toyDialect` (`let a = dup _ _; let b =
    dup a _; ret b`) to make the validation tangible. We build it over the
    one-element context `[()]`. -/
def sampleProg : Com toyDialect [()] () :=
  .var ⟨(), rfl, .cons .here (.cons .here .nil)⟩
    (.var ⟨(), rfl, .cons .here (.cons (.there .here) .nil)⟩
      (.ret .here))

/-- **The whole-program square on a concrete multi-binding program, popping out
    of the per-op leaves.** Instantiation of `idComLowerTransports` at
    `sampleProg`: the identity lowering's whole-`Com` preservation for a
    two-binding program is obtained with **no** program-specific induction — only
    the three one-line leaf lemmas fed to `fundamental`. -/
theorem sampleProg_transports :
    ComLowerTransports idLowering idTransTy idMapVal sampleProg :=
  idComLowerTransports sampleProg

end Validation

end ComParametricityTransport
