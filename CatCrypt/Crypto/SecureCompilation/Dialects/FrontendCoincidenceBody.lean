/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState

/-!
# DF whole-body coincidence — the two frontend denotations agree on the whole
# heap-free scalar `ImpExpr` body, completing the let-step recursion

The prior increments closed the **single-`let`-step** coincidence:

* `FrontendCoincidence.lean` — the leaf step
  (`denoteScalar_coincides_evalBV`): the two frontend denotations agree on a
  `toSExpr`-acceptable scalar-ALU leaf (atom / one binary-ALU layer).
* `FrontendCoincidenceLet.lean` — the let-extension engine
  (`envAgree_update`) and the `evalBV`-level let combinator
  (`letBind_coincides`).
* `FrontendCoincidenceRustState.lean` — the `RustState`-level refinement
  (`StateAgree`, `stateAgree_update`,
  `derivedBeta_scalarStore_eq_evalStateBV`,
  `letBind_rustState_coincides{,_stateAgree}`): a single scalar `let` store
  preserves `StateAgree` and materialises the bound value across the
  `Nat`↔`BitVec 64` store.

Each of those is a **single step**. This file performs the **structural
recursion** over a whole heap-free scalar `ImpExpr` body — nested `.letBind`s
over `toSExpr`-acceptable bound expressions ending in a `toSExpr`-acceptable
leaf — gluing the single-step pieces into one whole-body coincidence.

## §1 — The whole-body `evalBV` coincidence (the recursion)

`ScalarBodyImage params I body ρ β` (a recursive predicate) descends through the
nested `.letBind`s of `body`, threading the §1 `updRho`/`updBeta` let-extension
on both paths. At each `.letBind x v rest`, it requires the bound expr `v` to be
`toSExpr`-acceptable (so the leaf step `denoteScalar_coincides_evalBV` applies to
`v`), then continues into `rest` under the §1-extended environments; at the leaf,
it requires the leaf to be `toSExpr`-acceptable. `denoteScalar_body_coincides`
proves the whole body's `denoteScalar` succeeds and equals `some (evalBV β'
leafImage)` for the accumulated `β'`. The `.letBind` case chains
`envAgree_update` (transport `EnvAgree` across the store) + `letBind_coincides`
(the combinator) + the IH; the leaf case is the base
`denoteScalar_coincides_evalBV`.

## §2 — The `RustState`/`RustExec` whole-body store

`bodyLowerExec` lowers a scalar body to the Path-B `RScalarSetExpr` command
sequence (one per `.letBind`, each storing the bound `SExpr`), and
`stateAgree_bodyExec` runs that sequence under `RustExec`, threading
`StateAgree` across each store via `stateAgree_update` (the §2 engine) — the
deterministic whole-body store post-state agreement. Combined with §1 this is
the whole-body coincidence: the two frontend denotations agree on the entire
heap-free, fresh-local, in-range scalar `ImpExpr` body.

## Residual `RustExec`-derivation step (stated precisely)

The §2 `RustExec` derivation threads the *store* post-state under `StateAgree`
and uses the `scalarSetExpr` constructor's stored value `e.eval rs.rsScalar`.
What it does **not** internalise is the per-let `inRangeState`-discharge that
ties `e.eval rs.rsScalar`'s `Nat` value to `e.evalStateBV rs`'s wrapping
`BitVec 64` value *inside the running derivation* — that wrap-discharge is the
single-step `derivedBeta_scalarStore_eq_evalStateBV` (proved in the prior file),
which we invoke per store. The honest residual is exactly the per-let
`inRangeState` side-condition that the running `RustExec` value must satisfy for
the `evalState`↔`evalStateBV` materialisation to hold at that store; we carry it
as an explicit hypothesis on each let, not a hidden `sorry`.

No `sorry`, no new axioms, no `native_decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceBody

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState

/-! ## §1  The whole-body `evalBV` coincidence (the recursion)

A heap-free scalar `ImpExpr` body is `let x₁ = v₁ in … let xₙ = vₙ in leaf`,
where every `vᵢ` and the `leaf` are `toSExpr`-acceptable scalar-ALU expressions.
`ScalarBodyImage` is the recursive descriptor pairing each layer with its `SExpr`
image; `denoteScalar_body_coincides` is the structural recursion gluing the
single-step pieces of the prior files. -/

/-- **Whole-body image descriptor.** `ScalarBodyImage params I body β v` holds
    when `body` is a nested `.letBind` chain whose every bound expr and final
    leaf is `toSExpr`-acceptable, with the §1 let-extension threaded on the
    Path-B total env `β`, all let-bound names fresh (`∉ params`), and `v` the
    Path-B value of the final leaf under the *accumulated* env. Recursive on
    `body`:
    * `.letBind x e rest` — there is an `SExpr` image `se` of the bound `e`
      (`toSExpr e = some se`), `x ∉ params`, and the rest is a body image under
      the extended env `updBeta β x (evalBV β se)`, yielding the same final
      value `v`.
    * any other (the leaf) — `toSExpr body = some sleaf` for some `sleaf` whose
      Path-B value `evalBV β sleaf` is `v`. -/
def ScalarBodyImage {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64) :
    ImpExpr → (String → BitVec 64) → BitVec 64 → Prop
  | .letBind x e rest, β, v =>
      x ∉ params ∧ ∃ se : SExpr, toSExpr e = some se ∧
        ScalarBodyImage params I rest (updBeta β x (SExpr.evalBV β se)) v
  | body, β, v => ∃ sleaf : SExpr, toSExpr body = some sleaf ∧
        SExpr.evalBV β sleaf = v

/-- **§1 — whole-body coincidence (the recursion).** For a heap-free scalar body
    matched by `ScalarBodyImage` to a final Path-B value `v`, Path A
    `denoteScalar` of the *whole* body succeeds and equals `some v`. This is the
    structural recursion completing the single-`let`-step coincidence: the
    `.letBind` case chains `envAgree_update` (the §1 let-extension engine of
    `FrontendCoincidenceLet`) with `letBind_coincides` (the combinator) and the
    IH; the leaf case is the base `denoteScalar_coincides_evalBV`. -/
theorem denoteScalar_body_coincides {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) :
    (body : ImpExpr) → (ρ : String → Option (BitVec 64)) →
    (β : String → BitVec 64) → (v : BitVec 64) →
    EnvAgree params I ρ β → ScalarBodyImage params I body β v →
    ImpExpr.denoteScalar params I body ρ = some v
  | .letBind x e rest, ρ, β, v, hβ, himg => by
      -- Unfold the body image: `x ∉ params`, bound expr image `se`, rest image.
      obtain ⟨hx, se, hse, hrest⟩ := himg
      -- Path A bound-value coincidence (base leaf step on `e`).
      have hv : ImpExpr.denoteScalar params I e ρ = some (SExpr.evalBV β se) :=
        denoteScalar_coincides_evalBV params I ρ β hβ e hse
      -- §1 engine: the extended environments again agree.
      have hβ' : EnvAgree params I (updRho ρ x (SExpr.evalBV β se))
          (updBeta β x (SExpr.evalBV β se)) :=
        envAgree_update params I ρ β hβ x hx (SExpr.evalBV β se)
      -- IH on the rest, under the extended environments — same final value `v`.
      have hbody : ImpExpr.denoteScalar params I rest
          (updRho ρ x (SExpr.evalBV β se)) = some v :=
        denoteScalar_body_coincides params I rest
          (updRho ρ x (SExpr.evalBV β se)) (updBeta β x (SExpr.evalBV β se))
          v hβ' hrest
      -- Combinator: the whole `let` denotes to the body value.
      exact letBind_coincides params I ρ x e rest (SExpr.evalBV β se) v hv hbody
  | .var y, ρ, β, v, hβ, himg => by
      obtain ⟨sleaf, hs, hval⟩ := himg
      rw [denoteScalar_coincides_evalBV params I ρ β hβ (.var y) hs, hval]
  | .lit l, ρ, β, v, hβ, himg => by
      obtain ⟨sleaf, hs, hval⟩ := himg
      rw [denoteScalar_coincides_evalBV params I ρ β hβ (.lit l) hs, hval]
  | .app f args, ρ, β, v, hβ, himg => by
      obtain ⟨sleaf, hs, hval⟩ := himg
      rw [denoteScalar_coincides_evalBV params I ρ β hβ (.app f args) hs, hval]

/-- **§1, anchored at a `RustState`.** Specialising `denoteScalar_body_coincides`
    to the derived env `β = derivedBeta rs` of a `RustState` satisfying
    `StateAgree`: the whole scalar body denotes to `some v` for the threaded
    Path-B final value `v`. The `StateAgree` hypothesis supplies the `EnvAgree`
    half via `stateAgree_envAgree`. This is the entry point a `RustExec`/store
    recursion consumes — the Path-A value of the whole body, pinned to the input
    state. -/
theorem denoteScalar_body_coincides_stateAgree {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64)) (rs : RustState)
    (hsa : StateAgree params I ρ rs)
    (body : ImpExpr) (v : BitVec 64)
    (himg : ScalarBodyImage params I body (derivedBeta rs) v) :
    ImpExpr.denoteScalar params I body ρ = some v :=
  denoteScalar_body_coincides params I body ρ (derivedBeta rs) v
    (stateAgree_envAgree params I ρ rs hsa) himg

/-! ## §2  The `RustState`/`RustExec` whole-body store

The Path-B `let` chain lowers to a sequence of `RScalarSetExpr` commands — one
per `.letBind`, each storing the bound `SExpr` value into the bound scalar slot.
`bodyLowerExec` is that lowering; `stateAgree_bodyExec` runs it under `RustExec`,
threading `StateAgree` across each store via the §2 engine `stateAgree_update`.

To pin each store's bound value to the §1 `updBeta` chain, each let carries an
explicit `inRangeState` side-condition on its bound `SExpr` at the *running*
state (the honest residual stated in the module doc): the wrap-discharge
`derivedBeta_scalarStore_eq_evalStateBV` then materialises the stored `Nat` value
at exactly the `BitVec 64` value the §1 recursion threads. -/

/-- The Path-B command lowering of a scalar body to an `RScalarSetExpr`
    sequence. Each `.letBind x v rest` (with `toSExpr v = some sv`) emits
    `RSeq (RScalarSetExpr x sv) (lowering of rest)`; the leaf emits `RSkip`
    (its value is read out of the final state, not stored). Returns `none` if
    any layer is not `toSExpr`-acceptable. -/
def bodyLowerExec : ImpExpr → Option LowCT
  | .letBind x v rest =>
      (toSExpr v).bind fun sv =>
        (bodyLowerExec rest).map fun cr =>
          .RSeq (.RScalarSetExpr x sv) cr
  | _ => some .RSkip

/-- **A single `RScalarSetExpr` store, under `StateAgree` with the §1 `evalBV`
    value.** Running `RScalarSetExpr x sv` from `rs` reaches
    `rsSetScalar rs x (sv.eval rs.rsScalar)`, whose derived β at `x` is exactly
    `sv.evalStateBV rs` (when `sv` is `limbFree` and `inRangeState rs`). When
    additionally `sv.evalStateBV rs = SExpr.evalBV (derivedBeta rs) sv` (the
    two Path-B evaluators agree at `rs` — the §1 thread value), the store's
    derived-β update is `updBeta (derivedBeta rs) x (evalBV (derivedBeta rs) sv)`,
    and `StateAgree` transports across it (for `x ∉ params`). Bundles the §2
    `stateAgree_update` with the §3 wrap-discharge of the prior file. -/
theorem stateAgree_scalarSetExpr {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64))
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hsa : StateAgree params I ρ rs)
    (x : String) (hx : x ∉ params) (sv : SExpr)
    (hlf : sv.limbFree) (hir : sv.inRangeState rs)
    (hev : sv.evalStateBV rs = SExpr.evalBV (derivedBeta rs) sv) :
    RustExec N leafSpec (.RScalarSetExpr x sv) rs
        (rsSetScalar rs x (sv.eval rs.rsScalar))
      ∧ StateAgree params I (updRho ρ x (SExpr.evalBV (derivedBeta rs) sv))
          (rsSetScalar rs x (sv.eval rs.rsScalar)) := by
  refine ⟨RustExec.scalarSetExpr x sv rs, ?_⟩
  -- The stored `Nat` value `sv.eval rs.rsScalar` equals `(sv.evalStateBV rs).toNat`.
  have hstore : sv.eval rs.rsScalar = (SExpr.evalBV (derivedBeta rs) sv).toNat := by
    -- `eval = evalState` off `SLimb`; `evalState` is `evalStateBV.toNat` on range.
    rw [← SExpr.evalState_eq_eval rs sv hlf, ← hev]
    exact (SExpr.toNat_evalStateBV_of_inRangeState rs sv hir).symm
  rw [hstore, ← hev]
  -- Now the store is `rsSetScalar rs x (sv.evalStateBV rs).toNat`; transport.
  exact stateAgree_update params I ρ rs hsa x hx (sv.evalStateBV rs)

/-- **Whole-body store image (the §2 recursion descriptor).** Mirrors
    `ScalarBodyImage`, additionally carrying — per `.letBind` — the bound expr's
    `limbFree` + `inRangeState` (at the running state) and the per-store
    Path-B-evaluator agreement `evalStateBV = evalBV (derivedBeta rs)`, so that
    `stateAgree_scalarSetExpr` applies at each step. -/
def ScalarBodyStore {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64) :
    ImpExpr → RustState → (String → Option (BitVec 64)) → Prop
  | .letBind x v rest, rs, ρ =>
      x ∉ params ∧ ∃ sv : SExpr, toSExpr v = some sv ∧
        sv.limbFree ∧ sv.inRangeState rs ∧
        sv.evalStateBV rs = SExpr.evalBV (derivedBeta rs) sv ∧
        ScalarBodyStore params I rest
          (rsSetScalar rs x (sv.eval rs.rsScalar))
          (updRho ρ x (SExpr.evalBV (derivedBeta rs) sv))
  | _, _, _ => True

/-- **§2 — the whole-body `RustExec` store, threading `StateAgree`.** Running the
    `RScalarSetExpr` command sequence `bodyLowerExec body` from a state `rs` with
    `StateAgree params I ρ rs` — provided each let satisfies the
    `ScalarBodyStore` side-conditions (`x ∉ params`, bound expr `limbFree` +
    `inRangeState` at the running state, and per-store Path-B-evaluator
    agreement) — terminates in a state `rs'` that again satisfies `StateAgree`
    on the §1-extended local env. The whole-body store post-state agrees with the
    Path-A let-extended env. The `.letBind` case threads
    `stateAgree_scalarSetExpr` (single store + transport) + `RustExec.seq` + IH;
    the leaf case is `RustExec.skip`. -/
theorem stateAgree_bodyExec {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (N : Nat) (leafSpec : LeafSpec) :
    (body : ImpExpr) → (rs : RustState) → (ρ : String → Option (BitVec 64)) →
    (c : LowCT) → bodyLowerExec body = some c →
    StateAgree params I ρ rs → ScalarBodyStore params I body rs ρ →
    ∃ rs' ρ', RustExec N leafSpec c rs rs' ∧ StateAgree params I ρ' rs'
  | .letBind x v rest, rs, ρ, c, hc, hsa, hst => by
      -- Unfold store image.
      obtain ⟨hx, sv, hsv, hlf, hir, hev, hrest⟩ := hst
      -- Unfold the lowering: `c = RSeq (RScalarSetExpr x sv) cr`.
      simp only [bodyLowerExec, hsv, Option.bind_some, Option.map_eq_some_iff] at hc
      obtain ⟨cr, hcr, hceq⟩ := hc
      subst hceq
      -- Single store: derivation + transported `StateAgree`.
      obtain ⟨hexec1, hsa1⟩ :=
        stateAgree_scalarSetExpr params I ρ N leafSpec rs hsa x hx sv hlf hir hev
      -- IH on the rest, from the post-store state.
      obtain ⟨rs', ρ', hexec2, hsa2⟩ :=
        stateAgree_bodyExec params I N leafSpec rest
          (rsSetScalar rs x (sv.eval rs.rsScalar))
          (updRho ρ x (SExpr.evalBV (derivedBeta rs) sv)) cr hcr hsa1 hrest
      exact ⟨rs', ρ', RustExec.seq _ _ _ _ _ hexec1 hexec2, hsa2⟩
  | .var _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .lit _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .lam _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .app _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .unitVal, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .questionMark _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .earlyReturn _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .break_ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .continue_, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .cfBreak _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .cfContinue _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .cfBreakContinue _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .deref _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .borrow _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .seq _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .assign _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .tuple _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .proj _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .ifThenElse _ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .match_ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .whileLoop _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .whileFold _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .whileFoldReturn _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .forLoop _ _ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .forLoopRev _ _ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .forFold _ _ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .forFoldRev _ _ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .forFoldReturn _ _ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .forFoldRevReturn _ _ _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
  | .typeAscription _ _, rs, ρ, _, hc, hsa, _ => leafCase rs ρ hc hsa
where
  /-- Leaf-case helper: a non-`.letBind` body lowers to `RSkip` (a no-op store);
      `RustExec.skip` gives the derivation and the input `StateAgree` carries. -/
  leafCase {nIn : Nat} {params : List String} {I : Fin nIn → BitVec 64}
      {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
      (rs : RustState) (ρ : String → Option (BitVec 64))
      (hc : some (.RSkip : LowCT) = some c)
      (hsa : StateAgree params I ρ rs) :
      ∃ rs' ρ', RustExec N leafSpec c rs rs' ∧ StateAgree params I ρ' rs' :=
    ⟨rs, ρ, by cases hc; exact RustExec.skip rs, hsa⟩

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceBody
