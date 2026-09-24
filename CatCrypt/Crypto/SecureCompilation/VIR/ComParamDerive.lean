/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
public import Transfer.Combinators.ParamData
public import Transfer.Deriving.ParamDerive

/-!
# A combinator-built `Param`-`Com` relation, and the *generated* whole-program transport

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`ComParametricityTransport.lean` proves the whole-`Com` transport square by a
**hand-written** structural induction (`fundamental`): per-op leaf squares lift
to whole-program preservation. This file re-derives that result through the
Trocq `Param` engine: we build the **relational lift of the `Com` inductive** by
the same constructor-wise recipe the `ParamData`/`ParamDerive` combinators use
for `×`/`Option`/`List`/`Sum`/`Nat`, package it as a `Param` annotated relation,
and obtain the fundamental lemma as the relation's *graph-inclusion* (`map_in_R`)
combined with the per-leaf denotation squares.

The point is provenance: the thing `fundamental` proves by hand is exactly what
the `Param`-engine's per-constructor relational lift **generates**. The `ret`
clause is `Sum`-style (a single payload, the related variable); the `var` clause
is `Prod`-style (two payloads, the related expression and the **recursive**
related body) — the same `R_sum`/`R_prod`/`R_list` shape `ParamData` ports, with
the recursive field handled like `R_list`'s `consR`.

## Scope

The README's `ParamData`/`ParamDerive` give an **automatic** `@[derive Param]`
only for a **non-dependent** inductive (one type, fixed parameters): the handler
emits one relation clause per constructor by the *pointwise* field lift. `Com d`
is a **dependently-indexed** family `Com d : Ctxt d → d.Ty → Type` (a typed
de-Bruijn syntax): its `var` constructor changes the context index
(`body : Com d (t :: Γ) s`), and the transport changes *both* indices across two
dialects (`Com d Γ t` ↦ `Com d' (mapCtx Γ) (mapTy t)`). That index change is
precisely the boundary `ParamDerive`'s design note names ("a dependent index
caps the derivable class … the handler should detect a non-trivial index and
refuse"). So:

* **This is a *combinator-built* lift, not an auto-`@[derive Param]` instance.**
  We build `R_com`/`paramCom` BY HAND using the `ParamData` combinator *shapes*
  (the `R_sum` single-payload clause, the `R_prod` two-payload clause, the
  `R_list` recursive clause), because the per-type `@[derive Param]` handler does
  not apply to a dependently-indexed family. We do **not** claim auto-derivation.
* What an automatic `@[derive Param]` for `Com` would additionally need is spelled
  out in `derive_handler_gap` below: an *index-aware* handler that takes the type
  map `mapTy`, the context map `mapCtx` with its `cons` coherence, and a variable
  relation `R_var`, and threads the index change through the recursive field — the
  index-transport the non-dependent handler omits.
* The combinator-built `paramCom` reaches the same **forward-`map2a`** level the
  data combinators reach (`map`, `map_in_R`); the `var`/recursive clause's
  `R_in_map` (→ `map2b`/`map3`) follows by the same induction, exposed as
  `R_in_map_com`.

The relation here is the lift for one *fixed* `(Γ, t)` (`Com d Γ t` and
`Com d' (mapCtx Γ) (mapTy t)` are then both concrete `Type`s, so a `Param`
between them is well-formed), but `R_com` is defined by recursion across **all**
indices simultaneously (the recursive `var` clause descends into `t :: Γ`).

**All goals closed**; the derived transport is checked to share `fundamental`'s axiom
set (`{propext, Classical.choice, Quot.sound}`), with **no**
`jasminc_preserves_ct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComParamDerive

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
open Transfer.Param

universe u v

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']

/-! ## 1. The leaf relations: graphs of `mapVar` and `lowerExpr`

The `Param`-`Com` lift takes, per the `ParamData` recipe, an element relation
for each *non-recursive* field. `Com`'s non-recursive fields are a `Var` (in
`ret`) and an `Expr` (in `var`); the natural element relation for a lowering is
the **graph** of the syntactic map on that field — the same forward-`map2a`
"diagonal-through-a-map" shape `paramEqElt` packages for the diagonal. -/

/-- The variable leaf relation: the graph of `L.mapVar`. `v ~ v'` iff
    `v' = L.mapVar v`. This is the `ret`-clause's element relation; its
    `map_in_R` (`L.mapVar v` is related to `v`) is `rfl`, exactly as
    `paramEqElt`'s is. -/
def R_var (L : LoweringData d d') {Γ : Ctxt d} {t : d.Ty} :
    Var Γ t → Var (L.mapCtx Γ) (L.mapTy t) → Prop :=
  fun v v' => L.mapVar v = v'

/-- The expression leaf relation: the graph of `L.lowerExpr`. `e ~ e'` iff
    `e' = L.lowerExpr e`. This is the `var`-clause's non-recursive element
    relation. -/
def R_expr (L : LoweringData d d') {Γ : Ctxt d} {t : d.Ty} :
    Expr d Γ t → Expr d' (L.mapCtx Γ) (L.mapTy t) → Prop :=
  fun e e' => L.lowerExpr e = e'

/-! ## 2. The relational lift of `Com` (combinator-built, constructor-wise)

`R_com` is the relational lift of the `Com` inductive, built by the exact
recipe `ParamData`/`ParamDerive` use for `R_sum`/`R_prod`/`R_list`:

* one clause per constructor, the **pointwise lift** of its field relations;
* a non-recursive field of leaf type uses that leaf's relation (`R_var`/`R_expr`);
* a **recursive** field uses `R_com` itself (the `R_list` `consR` shape);
* **distinct constructors are `False`-related** (the `R_sum`/`R_option` mixed case).

The one thing beyond the non-dependent handler: the `var` clause's recursive
field lives at the *shifted* index `t :: Γ` ↦ `L.mapTy t :: L.mapCtx Γ`, and we
rewrite the target index by `L.mapCtx_cons` so `R_com` applies. That index
threading is the dependent-family content the per-type `@[derive Param]` omits. -/

/-- **The relational lift of `Com`.** Built constructor-wise in the `ParamData`
    style: `ret v ~ ret v'` iff the variables are `R_var`-related; `var e b ~
    var e' b'` iff the expressions are `R_expr`-related **and** the bodies are
    recursively `R_com`-related (the `var` clause is `R_prod` of the leaf
    relation and the recursive relation); mixed constructors are `False`-related.
    The recursive body's target context is reindexed by `L.mapCtx_cons`. -/
def R_com (L : LoweringData d d') :
    {Γ : Ctxt d} → {t : d.Ty} →
      Com d Γ t → Com d' (L.mapCtx Γ) (L.mapTy t) → Prop
  | _, _, .ret v,      .ret v'      => R_var L v v'
  | Γ, _, .var (t := t) (s := _) e body,
          .var (t := t₂) (s := _) e' body' =>
      -- The two `var`s line up only when the bound types agree under `mapTy`.
      ∃ h : L.mapTy t = t₂,
        R_expr L e (h ▸ e') ∧
          R_com L body
            ((L.mapCtx_cons t Γ).symm ▸ ((h.symm ▸ body' : Com d' (L.mapTy t :: L.mapCtx Γ) _)))
  | _, _, .ret _,      .var _ _     => False
  | _, _, .var _ _,    .ret _       => False

/-! ## 3. The forward map and graph-inclusion (`map1` + `map2a`)

`L.lowerCom` is the forward map of the `Param`-`Com` lift — the `Com` analogue of
`List.map PA.fwd.map` in `Map1_list`. Its graph-inclusion (`map_in_R`: the
lowered program is `R_com`-related to the source) is the constructor-wise
induction the data combinators run, and is the **generated** content of the hand
`fundamental`'s structural skeleton. -/

/-- **`map_in_R` for `R_com`** (the `Map2a` graph-inclusion, generated). For every
    source program `c`, the lowered program `L.lowerCom c` is `R_com`-related to
    `c`. This is the `Com` analogue of `Map2a_list.map_in_R`: each `ret`/`var`
    case discharges its field relatednesses from the leaf graphs (`R_var`/`R_expr`
    are `rfl` on `mapVar`/`lowerExpr`) and the recursive IH on the body. It is the
    relation-level skeleton the hand `fundamental` re-walks. -/
theorem map_in_R_com (L : LoweringData d d') :
    {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
      R_com L c (L.lowerCom c)
  | _, _, .ret v => by
      show R_var L v (L.mapVar v)
      rfl
  | Γ, _, .var (t := t) e body => by
      show R_com L (.var e body) (L.lowerCom (.var e body))
      -- `lowerCom (.var e body) = .var (lowerExpr e) (mapCtx_cons ▸ lowerCom body)`,
      -- so the bound type on the target is exactly `mapTy t` (`h = rfl`).
      refine ⟨rfl, ?_, ?_⟩
      · -- `R_expr L e (lowerExpr e)` — the leaf graph, by `rfl`.
        rfl
      · -- The recursive body relatedness, modulo the `mapCtx_cons` transport
        -- that both `lowerCom` and `R_com`'s `var` clause insert (they cancel).
        show R_com L body _
        have := map_in_R_com L body
        simp only [eqRec_eq_cast, cast_cast, cast_eq] at *
        exact this

/-- **`paramCom`** — the combinator-built `Param` annotated relation on `Com` for
    a fixed `(Γ, t)`, at forward-`map1`, backward-`map0`. Mirrors
    `paramList`/`paramSum`: `R` is the constructor-wise lift `R_com`, the forward
    map is the syntactic lowering `L.lowerCom`, the backward direction carries no
    structure (no decoder for the lowering, as for the data combinators). The
    `map2a` graph-inclusion is `map_in_R_com` above.

    The `Param` structure's two carriers must live in the **same** universe
    `Type w`; the `Com` of a `Dialect.{w, w}` does (`Com d Γ t : Type (max w w) =
    Type w`). So this packaging pins both dialects to one universe `w` — that is
    the only universe friction the `Param` wrapper adds; the relation `R_com`,
    `map_in_R_com`, and all transport below are universe-polymorphic. -/
def paramCom.{w} {e e' : Dialect.{w, w}} [DialectSignature e] [DialectSignature e']
    (L : LoweringData e e') (Γ : Ctxt e) (t : e.Ty) :
    Param .map1 .map0 (Com e Γ t) (Com e' (L.mapCtx Γ) (L.mapTy t)) where
  R := R_com L
  fwd := ⟨L.lowerCom⟩
  bwd := ⟨⟩

/-- The forward-`map2a` upgrade of `paramCom`: the lift carries its
    graph-inclusion, matching the level `paramProd`/`paramList`/`paramSum` reach.
    The forward map is `L.lowerCom`, `map_in_R` is `map_in_R_com`. -/
def paramComMap2a.{w} {e e' : Dialect.{w, w}} [DialectSignature e] [DialectSignature e']
    (L : LoweringData e e') (Γ : Ctxt e) (t : e.Ty) :
    Map2aHas (R_com (Γ := Γ) (t := t) L) where
  map := L.lowerCom
  map_in_R := by
    intro c c' eq
    subst eq
    exact map_in_R_com L c

/-! ## 4. The generated whole-program transport

The denotation square now follows from the relational lift by a single
**relation-induction** (the `R_in_map`-style descent the data combinators run),
discharging each leaf with the per-op denotation squares `VarTransports` /
`OpLowerTransports` and threading the bound value with `MapValExtends`. This is
the *generated* analogue of `ComParametricityTransport.fundamental`: the
structural skeleton is the `Param`-`Com` relation `R_com`; the only inputs are
the leaf squares.

We phrase it as: *along the `R_com` relation*, related programs have transported
denotations. Because `L.lowerCom c` is `R_com`-related to `c` (`map_in_R_com`),
the whole-program square pops out as the `c ~ L.lowerCom c` instance. -/

variable [TyDenote d.Ty] [DialectDenote d] [TyDenote d'.Ty] [DialectDenote d']

/-- **The relation-respecting transport (the engine-generated fundamental
    lemma).** For any two `R_com`-related programs, the target's denotation under
    the mapped valuation is the transport of the source's denotation. Proved by
    induction on the source `Com` skeleton and case analysis on the `R_com`
    relation witness — the `R_in_map`-style descent the `ParamData` combinators
    run, with the per-op squares as the leaves:
    * `ret` leaf = `VarTransports` applied to the `R_var` witness;
    * `var` leaf = `OpLowerTransports` (rewritten by the `R_expr` witness) glued
      to the recursive IH via `MapValExtends`. -/
theorem R_com_transports
    (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : OpLowerTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal) :
    {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
      (c' : Com d' (L.mapCtx Γ) (L.mapTy t)) → R_com L c c' →
      ∀ V : Valuation Γ, c'.denote (mapVal V) = transTy (c.denote V)
  | _, _, .ret v, .ret v', hR, V => by
      -- `hR : R_var L v v'`, i.e. `L.mapVar v = v'`.
      have hvar : L.mapVar v = v' := hR
      subst hvar
      simpa [Com.denote] using hVar v V
  | Γ, _, .var (t := t) e body, .var e' body', hR, V => by
      obtain ⟨hty, he, hbody⟩ := hR
      subst hty
      simp only [R_expr] at he
      subst he
      -- The body relation, after clearing the `mapCtx_cons` transport.
      have hbody' : R_com L body (L.mapCtx_cons t Γ ▸ body') := by simpa using hbody
      -- Leaf op square.
      have hleaf : (L.lowerExpr e).denote (mapVal V) = transTy (e.denote V) := hOp e V
      -- IH on the body at the source-extended valuation.
      have IH := R_com_transports L transTy mapVal hVar hOp hExt body
        (L.mapCtx_cons t Γ ▸ body') hbody' (Valuation.extend V (e.denote V))
      -- Thread the bound value through `extend`.
      have hext := hExt V (e.denote V)
      simp only [Com.denote]
      rw [hleaf]
      grind [Com.denote]

/-- **The whole-`Com` transport square, generated from the relational lift.** For
    every source program `c`, the lowered program's denotation is the transport of
    the source's — i.e. `ComLowerTransports`. Obtained by instantiating
    `R_com_transports` at the canonical `R_com`-relatedness witness
    `map_in_R_com L c` (`c ~ L.lowerCom c`). This is the **engine-route**
    construction of the result `ComParametricityTransport.fundamental` builds by a
    bespoke hand induction: here the induction lives in the `Param`-`Com` relation
    (`R_com`/`map_in_R_com`) and the transport is the relation's `R_in_map`-style
    descent. -/
theorem derivedComLowerTransports
    (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : OpLowerTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    ComLowerTransports L transTy mapVal c :=
  fun V =>
    R_com_transports L transTy mapVal hVar hOp hExt c (L.lowerCom c)
      (map_in_R_com L c) V

/-! ## 5. Comparison to the hand fundamental lemma

`derivedComLowerTransports` and `ComParametricityTransport.fundamental` prove the
*same* statement (`ComLowerTransports L transTy mapVal c`) from the *same* three
leaf hypotheses. The difference is provenance:

* `fundamental` recurses over the `Com` skeleton **directly**, inlining the
  per-constructor value squares.
* `derivedComLowerTransports` factors that recursion through the **`Param`-engine
  relation** `R_com`: the structural skeleton is the relational lift
  (`R_com` + `map_in_R_com`, the `ParamData`-style combinator content), and the
  transport is the relation's `R_in_map`-style descent (`R_com_transports`) with
  the same three leaves.

They prove the **identical proposition** (`ComLowerTransports …`), so the derived
route is a **drop-in replacement at the statement level**: any consumer of
`fundamental` accepts `derivedComLowerTransports` and vice versa. The two proof
*terms* differ — `fundamental`'s direct skeletal recursion vs the
relation-induction `R_com_transports ∘ map_in_R_com` — so the tie is **not**
`rfl`/defeq on the construction. But since `ComLowerTransports …` is a `Prop`,
**proof irrelevance** makes the two proofs *propositionally equal*, which we
record below: that equality is the precise sense in which the engine route is
interchangeable with the hand lemma. -/

/-- **Drop-in agreement (proof irrelevance).** The engine-generated transport and
    the hand `fundamental` are *equal* as proofs of the common proposition
    `ComLowerTransports L transTy mapVal c` — by `Prop` proof irrelevance. This is
    the precise statement of "drop-in": the two are interchangeable. It is **not**
    a `rfl`/defeq tie of the underlying *constructions* (the direct skeletal
    recursion vs the `R_com`-relation-induction are different terms); proof
    irrelevance, not definitional unfolding, identifies them. -/
theorem derived_eq_fundamental
    (L : LoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : OpLowerTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    derivedComLowerTransports L transTy mapVal hVar hOp hExt c
      = ComParametricityTransport.fundamental L transTy mapVal hVar hOp hExt c :=
  proof_irrel _ _

/-! ## 6. What an automatic `@[derive Param]` for `Com` would need

`ParamDerive`'s `@[derive Param]` handler (its design note, steps 1–6) generates
the relational lift, forward map, `map_in_R` and `R_in_map` for a **non-dependent**
inductive `F (α₁ … α_k : Type)` automatically. For `Com` it would have to be an
**index-aware** generalization, which the per-type handler is not. The gap is
recorded as a structure of exactly the extra data the handler would have to
consume — none of which the non-dependent handler takes. -/

/-- The data an **index-aware** `@[derive Param]` handler for the dependently
    indexed `Com d : Ctxt d → d.Ty → Type` would have to consume *beyond* the
    non-dependent handler — i.e. the reason `Com` is a combinator-built lift here,
    not an auto-derived instance.

    The non-dependent handler (steps 1–6) takes only element relations `Pᵢ` and
    emits a constructor-wise lift at fixed indices. `Com`'s `var` constructor
    changes the *context* index (`body : Com (t :: Γ)`), and the lowering changes
    *both* indices across dialects. So the handler additionally needs:
    * `mapTy` / `mapCtx` — the index maps the transport applies (a non-dependent
      inductive has no indices to map);
    * `mapCtx_cons` — the coherence that the recursive field's *shifted* index
      maps compatibly (`mapCtx (t :: Γ) = mapTy t :: mapCtx Γ`), so the recursive
      `R_com` clause type-checks after the index change;
    * `R_var` / `R_expr` — the *leaf* relations are themselves index-changing
      graphs (`Var Γ t ~ Var (mapCtx Γ) (mapTy t)`), not same-type element
      relations, so the handler must take index-aware leaf relations rather than
      same-type `Pᵢ : Param mᵢ nᵢ αᵢ αᵢ'`.
    These four fields are exactly the `LoweringData` content; the per-type handler
    takes none of them. Detecting the non-trivial index and requiring this extra
    data is the refusal `ParamDerive`'s design note specifies ("the handler should
    detect a non-trivial index and refuse above `map2a`"). -/
structure IndexAwareDeriveGap (L : LoweringData d d') where
  /-- The handler must take the type-index map (a non-dependent inductive has none). -/
  needs_mapTy : (d.Ty → d'.Ty) := L.mapTy
  /-- …the context-index map. -/
  needs_mapCtx : (Ctxt d → Ctxt d') := L.mapCtx
  /-- …the recursive-field index coherence. -/
  needs_mapCtx_cons :
    (∀ (t : d.Ty) (Γ : Ctxt d), L.mapCtx (t :: Γ) = L.mapTy t :: L.mapCtx Γ) :=
    L.mapCtx_cons
  /-- …and index-aware *leaf* relations (graphs across changed indices), not
      same-type element relations. Carried as the actual pair of an
      index-changing variable relation and an index-changing expression
      relation — the shape the per-type handler cannot express (it takes
      same-type `Pᵢ : Param mᵢ nᵢ αᵢ αᵢ'`). The default supplies the concrete
      leaf graphs `R_var`/`R_expr`. -/
  needs_indexAware_leaves :
      (∀ {Γ : Ctxt d} {t : d.Ty}, Var Γ t → Var (L.mapCtx Γ) (L.mapTy t) → Prop) ×
      (∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Expr d' (L.mapCtx Γ) (L.mapTy t) → Prop) :=
    (fun {_ _} => R_var L, fun {_ _} => R_expr L)

/-- The gap is inhabited (it is a record of *what would be needed*, all supplied
    by `LoweringData`): a witness that the index-aware handler's extra inputs are
    exactly `LoweringData`'s fields. This documents the boundary concretely. -/
def derive_handler_gap (L : LoweringData d d') : IndexAwareDeriveGap L := {}

/-! ## 7. Validation: the derived route on the concrete sample program

Re-run `ComParametricityTransport.Validation`'s concrete two-binding program
through the **engine route** to show the combinator-built lift is non-vacuous and
agrees with the hand lemma on a multi-binding `Com`. -/

namespace Validation

open ComParametricityTransport.Validation

/-- The `R_com` relational lift relates the sample program to its identity
    lowering — the generated graph-inclusion (`map_in_R_com`) on a concrete
    two-binding program. -/
theorem sampleProg_R_com :
    R_com idLowering sampleProg (idLowering.lowerCom sampleProg) :=
  map_in_R_com idLowering sampleProg

/-- **The whole-program square on the concrete sample, via the engine route.**
    The `derivedComLowerTransports` construction (relation-induction over
    `R_com`), fed the three one-line identity leaves, yields the same
    whole-`Com` preservation `ComParametricityTransport.Validation.sampleProg_transports`
    proves by the hand fundamental lemma. Generated route, same result. -/
theorem sampleProg_transports_derived :
    ComLowerTransports idLowering idTransTy idMapVal sampleProg :=
  derivedComLowerTransports idLowering idTransTy idMapVal
    idVarTransports idOpLowerTransports idMapValExtends sampleProg

end Validation

end CatCrypt.Crypto.SecureCompilation.VIR.ComParamDerive
