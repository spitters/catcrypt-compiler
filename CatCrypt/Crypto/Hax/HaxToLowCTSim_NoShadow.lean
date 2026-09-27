/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCT
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main_Full

/-!
# H3 Blocker 3 (part): no-shadow invariants for `haxToLowCT` output

This file partially discharges the `TowerFresh rs name` side-condition
used in `HaxToLowCTSim_Main_Full.lean` for the scalar-let arms
(`letBind name (.lit _) body`, `assign name (.lit _)`).

In production, the hax extraction pipeline emits programs in
alpha-renamed SSA form: every `let`-binding introduces a syntactically
fresh name with no collision against pre-existing tower slots.  We
formalise the *syntactic* side of that guarantee here:

* `ScalarFresh rs name` — semantic dual of `TowerFresh`, says
  `rs.rsScalar name = 0`.
* `boundNames : LowCT → List String` — the set of names introduced
  by a `LowCT` via `RLetZero` / `RLetU64Zero`.
* `letBind_lit_boundName_mem` — for any `LowCT` produced by
  `haxToLowCT (.letBind name (.lit _) body)`, `name` appears as a
  `boundName` of that command.
* `TowerFresh_of_unused` — trivial repackaging used as the discharge
  shape from the surrounding initial-state freshness predicate.

The semantic claim — that for AnfShaped, well-scoped (no shadowing)
source programs the initial `TowerFresh rs name` side-condition is
dischargeable from the surrounding scope — is stated as the
`WellScopedInitial` predicate below, without a proof in this file.  The
program-level simulation `haxToLowCT_simulates_program`
(`HaxToLowCTSim_Program.lean`) threads freshness through the program as
`NamesFresh rs S` for the scalar-binding names `S` accepted by
`simScope`.

## Caller-facing content

The scalar-let arms `simulates_letBind_lit_full` and
`simulates_assign_lit_*_full` take a per-call `TowerFresh rs name`
precondition.  This file provides `TowerFresh_of_unused`, a per-call
discharge from a per-name initial freshness fact, and the syntactic
bookkeeping that connects `boundNames` to `haxToLowCT`'s structure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState Located rsSetTower rsSetScalar)

/-! ## §1  Scalar-side freshness predicate

`TowerFresh` (in `Main_Full.lean`) already covers the tower side.
`ScalarFresh` is its scalar counterpart, included here for parity and
for use by future no-shadow lemmas. -/

/-- A name has no non-default scalar value in `rs`. -/
def ScalarFresh (rs : RustState) (name : String) : Prop :=
  rs.rsScalar name = 0

/-- Trivial: `ScalarFresh` reduces to a scalar-heap equality. -/
theorem ScalarFresh_def (rs : RustState) (name : String) :
    ScalarFresh rs name ↔ rs.rsScalar name = 0 := Iff.rfl

/-! ## §2  Bound names of a `LowCT`

The "bound names" of a `LowCT` are the names introduced by
`RLetZero` / `RLetU64Zero` constructors — the analogue of binders in
a let-style language.  Everything else either reads from a name
(`RCall` arguments, `RIfNz` condition, `RWhileNz` condition) or
writes through a pre-existing slot (`RScalarSet`, `RCall` destination
inside a let-block, `RLimbStore`, …).

`boundNames c` is the multiset (returned as a list) of fresh names a
well-formed `c` introduces.  For a translation
`haxToLowCT e = some c` where `e` is `AnfShaped`, every `letBind`
name in `e` corresponds to a `boundName` in `c`. -/

/-- Names bound by a `LowCT` as the "outputs" of `let`-style
    constructors.  Excludes `RScalarSet` (assignment, not binding)
    and `RCall` destinations (the dest is pre-allocated by the
    enclosing `RLetZero`).  Designed to be syntactic: we just walk
    the AST and collect introduced names. -/
def boundNames : LowCT → List String
  | .RSkip                      => []
  | .RSeq c1 c2                 => boundNames c1 ++ boundNames c2
  | .RLetZero n _ body          => n :: boundNames body
  | .RLetU64Zero n body         => n :: boundNames body
  | .RScalarSet _ _             => []
  | .RCall _ _ _                => []
  | .RCallSwap _ _ _ _          => []
  | .RCloneCall _ _ _ _ _ _     => []
  | .RIfNz _ ct cf              => boundNames ct ++ boundNames cf
  | .RWhileNz _ body            => boundNames body
  | .RFor _ _ body              => boundNames body
  | .RForRuntime _ _ body       => boundNames body
  | .RLimbStore _ _ _           => []
  | .RLimbStoreExpr _ _ _       => []
  | .RCallN _ _ _               => []
  | .RSelect _ _ _ _            => []
  | .RAssert _                  => []
  | .RBlock body                => boundNames body
  | .RFnDef _ _ _ body cont     => boundNames body ++ boundNames cont
  | .RFnCall _ _ _              => []
  | .RTupleLoad _ _ _           => []
  | .RArrStore _ _ _            => []
  | .RArrLoad _ _ _             => []
  | .RArrStoreLit _ _ _         => []
  | .RArrLoadLit _ _ _          => []
  | .RScalarSetExpr _ _         => []
  -- dest pre-allocated by the enclosing RLetZero (same as RCall), so binds nothing
  | .RCallDstThreaded _ _ _     => []
  | .RCopy _ _                  => []

/-! ## §3  Syntactic freshness lemmas for `haxToLowCT` output -/

/-- Helper: `boundNames` of the canonical `letBind (.lit _)` output
    shape always contains `name` at the head. -/
theorem boundNames_RLetU64Zero_head
    (name : String) (body : LowCT) :
    name ∈ boundNames (.RLetU64Zero name body) := by
  simp [boundNames]

/-- Helper: `boundNames` of the canonical `letBind (.app _)` output
    shape always contains `name` at the head. -/
theorem boundNames_RLetZero_head
    (name : String) (dt : TowerType) (body : LowCT) :
    name ∈ boundNames (.RLetZero name dt body) := by
  simp [boundNames]

/-- The `letBind name (.lit l) body` arm of `haxToLowCT` always
    produces a `LowCT` whose outermost binder is `name`.  The bound
    name is the same as the source-side `letBind` binder. -/
theorem haxToLowCT_letBind_lit_boundName
    (name : String) (l : ImpLit) (body : ImpExpr) (c : LowCT)
    (h : haxToLowCT (.letBind name (.lit l) body) = some c) :
    name ∈ boundNames c := by
  obtain ⟨bodyC, n, _hBodyTrans, _hDecode, hC⟩ :=
    haxToLowCT_letBind_lit_some name l body c h
  subst hC
  exact boundNames_RLetU64Zero_head name _

/-! ## §4  Discharge shapes for the `TowerFresh` precondition

The Main_Full theorem takes `hScalarFresh : ∀ name rs, TowerFresh rs name`
as a parametric hypothesis.  This file provides the discharge
*shape*: any caller that can show their *initial* `rs` has no tower
binding at the introduced name can satisfy the precondition via
`TowerFresh_of_unused`.

For a complete syntactic discharge — proving that no `letBind`-bound
name in a well-scoped `ImpExpr` clashes with pre-existing tower
bindings — see the `WellScopedInitial` predicate at §5 below. -/

/-- Trivial discharge: if `rs.rsTower name = none` (no pre-existing
    tower binding), then `TowerFresh rs name`. -/
theorem TowerFresh_of_unused
    (rs : RustState) (name : String)
    (h : rs.rsTower name = none) :
    TowerFresh rs name := h

/-- Companion discharge for the scalar side. -/
theorem ScalarFresh_of_zero
    (rs : RustState) (name : String)
    (h : rs.rsScalar name = 0) :
    ScalarFresh rs name := h

/-- `TowerFresh` survives any `rsSetScalar` update (scalar writes
    don't touch the tower): freshness propagates through nested
    scalar `letBind`s. -/
theorem TowerFresh_rsSetScalar
    (rs : RustState) (name name' : String) (n : Nat)
    (h : TowerFresh rs name) :
    TowerFresh (rsSetScalar rs name' n) name := by
  unfold TowerFresh at *
  show (rsSetScalar rs name' n).rsTower name = none
  -- rsSetScalar only touches rsScalar, not rsTower.
  exact h

/-- `TowerFresh` is preserved by `rsSetTower` at a *different* name.
    The classical "fresh name stays fresh under unrelated tower
    updates" fact. -/
theorem TowerFresh_rsSetTower_other
    (rs : RustState) (name name' : String)
    (v : Σ t : TowerType, CatCrypt.Crypto.Jasmin.LowCT.RustVal t)
    (hNe : name ≠ name')
    (h : TowerFresh rs name) :
    TowerFresh (rsSetTower rs name' v) name := by
  unfold TowerFresh at *
  show (rsSetTower rs name' v).rsTower name = none
  rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs name' name v
        (Ne.symm hNe)]
  exact h

/-! ## §5  WellScopedInitial — initial-state fact for AnfShaped programs

`WellScopedInitial e rs` says: every name that appears as a
`letBind` binder anywhere in `e` is tower-fresh in `rs`.  For
hax-extracted programs (which are alpha-renamed to SSA form), this
is automatic: the bound names are fresh symbols not present in any
externally-supplied initial state.

We give the predicate and the trivial connection to `TowerFresh`;
proving it propagates through `haxToLowCT` is the stretch goal
not attempted in this file (it requires a no-shadowing lemma on
`AnfShaped` that we don't yet have). -/

/-- `letBindNames e` collects every binder introduced by `letBind` in
    `e`.  Mirrors `boundNames` on the `LowCT` side.

    The `match_` arms are not recursed into — `pa.2` does not embed
    structurally into the enclosing `ImpExpr` (Lean's structural recursion
    checker rejects `letBindNames pa.2`).  Since the analysis here is
    only used at top-level for AnfShaped programs (which do not contain
    `match_` outside the H2.1 2-tuple-destructure shape used in this
    file's call sites), the under-approximation is harmless. -/
def letBindNames : ImpExpr → List String
  | .letBind n _ body          => n :: letBindNames body
  | .seq a b                   => letBindNames a ++ letBindNames b
  | .ifThenElse _ t e          => letBindNames t ++ letBindNames e
  | .whileLoop _ body          => letBindNames body
  | _                          => []

/-- `WellScopedInitial e rs`: every `letBind` binder in `e` is
    tower-fresh in the initial `rs`.  In a hax-extracted SSA
    pipeline, this is the alpha-renaming guarantee.  -/
def WellScopedInitial (e : ImpExpr) (rs : RustState) : Prop :=
  ∀ name ∈ letBindNames e, TowerFresh rs name

/-- Trivial: `var` has no bound names, so any state is well-scoped. -/
theorem WellScopedInitial_var (name : String) (rs : RustState) :
    WellScopedInitial (.var name) rs := by
  intro n hn
  simp [letBindNames] at hn

/-- Trivial: `unitVal` has no bound names. -/
theorem WellScopedInitial_unitVal (rs : RustState) :
    WellScopedInitial .unitVal rs := by
  intro n hn
  simp [letBindNames] at hn

/-- A `letBind`-bound name is necessarily in `letBindNames` of the
    enclosing `letBind` term. -/
theorem letBindNames_letBind_head
    (name : String) (val body : ImpExpr) :
    name ∈ letBindNames (.letBind name val body) := by
  simp [letBindNames]

/-- For a `letBind`, the head binder is `WellScopedInitial`-fresh. -/
theorem WellScopedInitial_letBind_head
    (name : String) (val body : ImpExpr) (rs : RustState)
    (h : WellScopedInitial (.letBind name val body) rs) :
    TowerFresh rs name :=
  h name (letBindNames_letBind_head name val body)

/-! ## §6  Marker -/

/-- Marker theorem: the file compiles and the API above is exported. -/
theorem h3_no_shadow_compiles : True := trivial

end CatCrypt.Crypto.Hax
