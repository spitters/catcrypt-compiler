/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerGeneric

/-!
# Composition of structural dialect lowerings

A `LoweringData d d'` (`ComParametricityTransport.lean`) packages a *structural*,
one-operation-to-one-operation dialect lowering: a type map, a context map
compatible with `cons`, a variable map, and a per-expression leaf rewrite, from
which the canonical `Com` lowering `LoweringData.lowerCom` is determined. The
generic compiler `CompilerGeneric.compileVia` runs such a lowering into jasmin
and `compileVia_correct` proves it correct from the three per-op transport
squares of `fundamental`.

This file defines the composition of lowerings: two 1-to-1 lowerings
`L1 : LoweringData d d'` and `L2 : LoweringData d' d''` compose into a single
`L1.comp L2 : LoweringData d d''`, and a 1-to-1 chain collapses into one
`LoweringData` usable directly by `compileVia`. Concretely:

1. `LoweringData.comp` — the composite static data. The type and context maps
   are the function composites; because `Ctxt`-composition is *definitional*,
   the variable and expression leaves are the plain composites with **no cast**.
   The only derived field is `mapCtx_cons`, glued from `L1.mapCtx_cons` and
   `L2.mapCtx_cons`.
2. `lowerCom_comp` — the composite's canonical `Com` recursion is the
   composite of the two recursions: `(L1.comp L2).lowerCom c =
   L2.lowerCom (L1.lowerCom c)`. A plain `Eq` (no `HEq`): the two sides have
   *definitionally equal* types since `comp`'s maps are literal composites. The
   sole subtlety is the `mapCtx_cons ▸` cast in the `.var` case, handled by a
   standalone cons-commute `have`.
3. `comp_fundamental` — the whole-program transport square for `L1.comp L2`,
   derived by **chaining** `fundamental L2` (on `L1.lowerCom c`) after
   `fundamental L1` (on `c`), from the per-op transport hypotheses of `L1` and
   `L2`, without a new induction on `c`.

The composite transports `⟦t⟧ → ⟦L2.mapTy (L1.mapTy t)⟧` via
`transTy2 ∘ transTy1` and valuations via `mapVal2 ∘ mapVal1`.

The file contains no open goals and declares no axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LoweringDataComp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport

universe u v

/-! ## 1. Composition of the static lowering data -/

variable {d d' d'' : Dialect}
variable [DialectSignature d] [DialectSignature d'] [DialectSignature d'']

/-- **Composition of two structural lowerings.** Type and context maps compose
    as functions; the variable and expression leaves are the plain composites
    (the codomain `Ctxt`/`Ty` of the composite map is *definitionally* the
    nested application, so no transport is required on the leaves). The
    `mapCtx_cons` of the composite is glued from the two component `mapCtx_cons`
    facts. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport.LoweringData.comp
    (L1 : LoweringData d d') (L2 : LoweringData d' d'') : LoweringData d d'' where
  mapTy := L2.mapTy ∘ L1.mapTy
  mapCtx := L2.mapCtx ∘ L1.mapCtx
  mapCtx_cons := fun t Γ => by
    -- L2.mapCtx (L1.mapCtx (t :: Γ)) = L2.mapTy (L1.mapTy t) :: L2.mapCtx (L1.mapCtx Γ)
    simp only [Function.comp_apply, L1.mapCtx_cons, L2.mapCtx_cons]
  mapVar := fun v => L2.mapVar (L1.mapVar v)
  lowerExpr := fun e => L2.lowerExpr (L1.lowerExpr e)

variable (L1 : LoweringData d d') (L2 : LoweringData d' d'')

/-- The composite's `mapTy` is the function composite (definitional; named for
    `rw`). -/
@[simp] theorem comp_mapTy : (L1.comp L2).mapTy = L2.mapTy ∘ L1.mapTy := rfl

/-- The composite's `mapCtx` is the function composite (definitional). -/
@[simp] theorem comp_mapCtx : (L1.comp L2).mapCtx = L2.mapCtx ∘ L1.mapCtx := rfl

/-- The composite's `mapVar` is the composite of the two variable maps. -/
@[simp] theorem comp_mapVar {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) :
    (L1.comp L2).mapVar v = L2.mapVar (L1.mapVar v) := rfl

/-- The composite's `lowerExpr` is the composite of the two expression leaves. -/
@[simp] theorem comp_lowerExpr {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) :
    (L1.comp L2).lowerExpr e = L2.lowerExpr (L1.lowerExpr e) := rfl

/-! ## 2. The composite recursion is the composite of the recursions -/

/-- A `▸` cast over a (possibly proof-dependent) motive is `HEq` to the uncast
    term — the local restatement of `eqRec_heq` whose motive `(x : α) → a = x →
    Sort` matches the exact `Eq.rec` shape produced by `LoweringData.lowerCom`'s
    `mapCtx_cons ▸`, so it unifies. Proved by `cases` on the equality proof. -/
theorem heq_eqRec_lc {α : Sort u} {a : α} {motive : (x : α) → a = x → Sort v}
    (x : motive a rfl) {b : α} (h : a = b) : @Eq.rec α a motive x b h ≍ x := by
  cases h; rfl

/-- **`lowerCom_comp`.** The canonical `Com` recursion of the composite lowering
    equals the composite of the two canonical recursions:
    `(L1.comp L2).lowerCom c = L2.lowerCom (L1.lowerCom c)`.

    A plain `Eq` — **no `HEq`** — because `comp`'s `mapTy`/`mapCtx` are literal
    function composites, so both sides inhabit the *definitionally equal* type
    `Com d'' (L2.mapCtx (L1.mapCtx Γ)) (L2.mapTy (L1.mapTy t))`. The induction is
    on the `Com` skeleton; the `.var` case must reconcile the `mapCtx_cons ▸`
    cast that `LoweringData.lowerCom` inserts on each side. -/
theorem lowerCom_comp :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t),
      (L1.comp L2).lowerCom c = L2.lowerCom (L1.lowerCom c)
  | _, _, .ret v => rfl
  | Γ, _, .var (t := t) e body => by
      -- Heads (`lowerExpr`) agree definitionally; reduce to the bound bodies.
      simp only [LoweringData.lowerCom]
      congr 1
      -- IH on the body, then reconcile the two `mapCtx_cons ▸` casts via HEq.
      rw [lowerCom_comp body]
      apply eq_of_heq
      -- Strip the two outer casts; the inner `L1`-cast lives under `L2.lowerCom`.
      refine (heq_eqRec_lc _ _).trans (HEq.symm ((heq_eqRec_lc _ _).trans ?_))
      -- `L2.lowerCom (mc1 ▸ x) ≍ L2.lowerCom x`: congruence over the inner cast.
      congr 1
      · exact (L1.mapCtx_cons t Γ).symm
      · exact heq_eqRec_lc _ _

/-! ## 3. The composite transport square (chaining `fundamental`)

To phrase the semantic composition we need denotation on all three dialects.
The composite transports values by `transTy2 ∘ transTy1` and valuations by
`mapVal2 ∘ mapVal1` (both type-check at the composite's maps because those are
literal function composites). -/

section Semantic

variable [TyDenote d.Ty] [DialectDenote d]
variable [TyDenote d'.Ty] [DialectDenote d']
variable [TyDenote d''.Ty] [DialectDenote d'']

/-- The composite value transport `⟦t⟧ → ⟦L2.mapTy (L1.mapTy t)⟧`. -/
def compTransTy (transTy1 : TransTy L1) (transTy2 : TransTy L2) :
    TransTy (L1.comp L2) :=
  fun {_t} x => transTy2 (transTy1 x)

/-- The composite valuation transport `Valuation Γ → Valuation (L2.mapCtx
    (L1.mapCtx Γ))`. -/
def compMapVal (mapVal1 : MapVal L1) (mapVal2 : MapVal L2) :
    MapVal (L1.comp L2) :=
  fun {_Γ} V => mapVal2 (mapVal1 V)

/-- **`comp_fundamental` — the composite whole-program transport square.**

    For a 1-to-1 chain `L1 ; L2` (collapsed into `L1.comp L2` by `comp`), the
    composite lowering transports every program end-to-end, derived purely by
    **chaining** the two `fundamental` lemmas — `fundamental L2` on the
    once-lowered program `L1.lowerCom c`, after `fundamental L1` on `c`. No fresh
    induction: the hypotheses are the per-op transport squares of each lowering
    (`hVar*`/`hOp*`/`hExt*`).

    Concretely, for every `c` and input valuation `V`:

        ((L1.comp L2).lowerCom c).denote ((mapVal2 ∘ mapVal1) V)
          = (transTy2 ∘ transTy1) (c.denote V)

    i.e. `ComLowerTransports (L1.comp L2) (compTransTy …) (compMapVal …) c`. When
    `d'' = jasminDialect`, `L1.comp L2` is a lowering that
    `CompilerGeneric.compileVia` accepts (see `compileVia_comp_correct`). -/
theorem comp_fundamental
    (transTy1 : TransTy L1) (mapVal1 : MapVal L1)
    (hVar1 : VarTransports L1 transTy1 mapVal1)
    (hOp1 : OpLowerTransports L1 transTy1 mapVal1)
    (hExt1 : MapValExtends L1 transTy1 mapVal1)
    (transTy2 : TransTy L2) (mapVal2 : MapVal L2)
    (hVar2 : VarTransports L2 transTy2 mapVal2)
    (hOp2 : OpLowerTransports L2 transTy2 mapVal2)
    (hExt2 : MapValExtends L2 transTy2 mapVal2)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    ComLowerTransports (L1.comp L2)
      (compTransTy L1 L2 transTy1 transTy2)
      (compMapVal L1 L2 mapVal1 mapVal2) c := by
  intro V
  -- The composite recursion is the composite of the recursions.
  show ((L1.comp L2).lowerCom c).denote (mapVal2 (mapVal1 V))
      = transTy2 (transTy1 (c.denote V))
  rw [lowerCom_comp L1 L2 c]
  -- `fundamental L2` on the once-lowered program at `mapVal1 V`, then
  -- `fundamental L1` on the source program — chained as a term equality
  -- (the `∀ {…}`-eta forms are defeq, so `Eq.trans`/`congrArg` align them).
  have h2 := fundamental L2 transTy2 mapVal2 hVar2 hOp2 hExt2 (L1.lowerCom c) (mapVal1 V)
  have h1 := fundamental L1 transTy1 mapVal1 hVar1 hOp1 hExt1 c V
  exact h2.trans (congrArg transTy2 h1)

end Semantic

/-! ## 4. Sanity: a collapsed chain feeds the generic compiler

When the final dialect is jasmin, the composite `L1.comp L2` is a single
`LoweringData d jasminDialect`, so `CompilerGeneric.compileVia` accepts it
directly — a 1-to-1 chain collapses into one object the generic compiler can
run. -/

section CompileViaSanity

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerGeneric

variable (Lj1 : LoweringData d d')
variable (Lj2 : LoweringData d' jasminDialect)
variable {Γ : Ctxt d} {tt : d.Ty} (c : Com d Γ tt)

-- The collapsed chain `Lj1.comp Lj2 : LoweringData d jasminDialect` is exactly
-- what `compileVia` consumes; this `#check` confirms the composite plugs into
-- the generic compiler with no glue.
#check (compileVia (Lj1.comp Lj2) c :
  Com jasminDialect ((Lj1.comp Lj2).mapCtx Γ) ((Lj1.comp Lj2).mapTy tt))

end CompileViaSanity

/-! ## 5. The multi-dialect compile theorem

`comp_fundamental` (§3) gives the composite *transport square*; composing it with
the owned whole-function backend gives the `runProg`-level correctness for a
program compiled through two dialects `d → d' → jasmin`. It has the same
CompCert-style equation as `CompilerGeneric.compileVia_correct`, for the
composite `L1.comp L2`. -/

section CompileViaComp

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerGeneric
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering

variable [TyDenote d.Ty] [DialectDenote d]
variable [TyDenote d'.Ty] [DialectDenote d']

/-- **`compileVia_comp_correct` — two-dialect compile correctness.**

    For a source dialect `d`, an intermediate dialect `d'`, structural lowerings
    `L1 : d → d'` and `L2 : d' → jasmin`, the jasmin program
    `compileVia (L1.comp L2) c`, run under `leafSem`, computes the composite
    value transport of the source denotation:

        runProg leafSem (compileVia (L1.comp L2) c) (compMapVal … V)
          = compTransTy … (c.denote V)

    The hypotheses are the transport squares of each lowering
    (`hVar₁/hOp₁/hExt₁`, `hVar₂/hOp₂/hExt₂`), the leaf agreement `hJLeaf`, and
    the straight-line condition `hStraight` on the compiled program. The
    `runProg` step is `lowerComToProg_sem_eq'`, and the denotation equality is
    `comp_fundamental`. A chain of more than two lowerings can be written with
    nested `comp`s; applying this theorem to it requires the transport squares
    of the nested composite as hypotheses. -/
theorem compileVia_comp_correct
    (L1 : LoweringData d d') (L2 : LoweringData d' jasminDialect)
    (transTy1 : TransTy L1) (mapVal1 : MapVal L1)
    (hVar1 : VarTransports L1 transTy1 mapVal1)
    (hOp1 : OpLowerTransports L1 transTy1 mapVal1)
    (hExt1 : MapValExtends L1 transTy1 mapVal1)
    (transTy2 : TransTy L2) (mapVal2 : MapVal L2)
    (hVar2 : VarTransports L2 transTy2 mapVal2)
    (hOp2 : OpLowerTransports L2 transTy2 mapVal2)
    (hExt2 : MapValExtends L2 transTy2 mapVal2)
    {leafSem : LeafSem} (hJLeaf : JasminPrintSemCorrect.LeafAgrees leafSem)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (hStraight : StraightLine (compileVia (L1.comp L2) c))
    (V : Ctxt.Valuation Γ) :
    runProg leafSem (compileVia (L1.comp L2) c)
        (compMapVal L1 L2 mapVal1 mapVal2 V)
      = compTransTy L1 L2 transTy1 transTy2 (c.denote V) := by
  rw [lowerComToProg_sem_eq' hJLeaf (compileVia (L1.comp L2) c) hStraight
        (compMapVal L1 L2 mapVal1 mapVal2 V)]
  exact comp_fundamental L1 L2 transTy1 mapVal1 hVar1 hOp1 hExt1
      transTy2 mapVal2 hVar2 hOp2 hExt2 c V

end CompileViaComp

end CatCrypt.Crypto.SecureCompilation.VIR.LoweringDataComp
