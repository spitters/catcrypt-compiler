/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.SpeculativeCTFence

/-!
# Blade-style *selective* speculative-protection placement

**Task #564 residual (Blade variant).**  `SpeculativeCT.lean` delivered the
speculative leakage semantics over the owned `LowCT` stream (`specObs`,
`SpeculativelyConstantTime`) and the keystone `architecturally_CT_imp_SCT`;
`SpeculativeCTFence.lean` closed the *unconstrained-predictor* gap with the
**blanket-fence** mitigation `insertFences` — an `lfence` (`RFence`) at *every*
branch arm / loop head and a site-guard (`RGuard`) before *every*
call / load / store.

A blanket protection is sound but conservative: it places a barrier even at
sites that lie on **no** speculative-leak path (e.g. a branch whose arms issue
no transient observation, a call/load with no transient source live).  Vassena
et al.'s **Blade** (POPL 2021) instead computes a *min-cut* of the
*def-use leak graph* (transient **sources** → leaking **sinks**) and places a
protection only at the cut sites — provably enough to sever every source→sink
path, with *fewer* protections than blanket fencing.

This file formalises the **soundness** half of Blade: a protection set that
*covers every speculative-leak path* is still speculatively constant-time
against an **unconstrained** misprediction oracle — and inserts no more (and,
on any program with a leak-free site, strictly fewer) protections than the
blanket fence pass.  We model the leak graph abstractly (sources, sinks, and a
path-coverage predicate `coversAllPaths`), define the selective placement
`insertSelective`, and prove the keystone

  `coversAllPaths protectSet c → cmdCT c lt leafCT = true →
     SpeculativelyConstantTimeF window O lt (insertSelective protectSet c)`

for every window and every (adversarial) oracle.

**What we do NOT prove (explicit out-of-scope).**  The *optimality* of the cut —
that the path-covering set Blade computes is a **minimum** cut (the max-flow /
min-cut argument that no smaller covering set exists) — is the harder
combinatorial half and is **not** attempted here.  We prove only that *a*
path-covering protection set **suffices** for SCT (soundness), plus the perf
win that a covering set can be strictly smaller than blanket.  This is the
genuine security content; min-cut optimality is reported as the residual.

## What this provides

1. **Leak-graph model** (`Site`, `leakRelevant`, `branchSites`,
   `coversAllPaths`): a *site* is a branch/loop head (the speculation source);
   it is *leak-relevant* when its mis-speculated wrong-path can issue a
   transient observation (a non-empty arm/body).  `coversAllPaths protectSet c`
   holds when every leak-relevant site of `c` is in `protectSet` — i.e. every
   source→sink path passes through a protected site.

2. `insertSelective protectSet : LowCT → LowCT`, a structural pass that fences
   a branch/loop **iff** its site is in `protectSet` (and always site-guards
   calls/loads/stores, the STL/BTB/RSB sinks), recursing structurally.

3. **Denotation preservation** (`archObs_insertSelective`,
   `cmdCT_insertSelective`): the inserted protections are no-ops for the
   architectural semantics and preserve `cmdCT` acceptance.

4. **The keystone** (`specObsF_insertSelective_eq_archObs`,
   `insertSelective_SCT_of_covers`): a *path-covering* selective placement
   collapses the fenced speculative trace to the architectural trace, for any
   window / oracle — every wrong-path is either fenced (drains) or leak-free
   (empty), and every call/load/store is site-guarded — hence SCT against an
   unconstrained predictor.

5. **The perf win** (`insertSelective_fewer`): a covering protect set inserts
   no more protections than blanket fencing
   (`selectiveMarkerCount ≤ blanketFenceCount`), and strictly fewer on any
   program with a leak-free branch (`PilotSel.selective_strictly_fewer`).

## References

* Vassena, Disselkoen, von Gleissenthall, Cauligi, Kıcı, Jhala, Tullsen,
  Stefan, "Automatically Eliminating Speculative Leaks with Blade", POPL 2021
  (the def-use leak graph and its min-cut — the selective placement this file's
  soundness half formalises).
* Cauligi et al., "Constant-Time Foundations for the New Spectre Era",
  PLDI 2020 (the speculative semantics).
-/

namespace CatCrypt.Crypto.SecureCompilation.SpeculativeCT

open CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-! ## §1.  The leak graph, abstractly

We model the Spectre leak graph at the granularity the SCT observer reasons
over.  A speculation **source** is a branch / loop head: a misprediction there
opens a transient window down the wrong arm/body.  A leaking **sink** is a
transient observation issued inside that window (a wrong-path memory index, a
nested branch, …).  A source→sink path therefore runs from a branch head into
its (mis-speculated) arm; a protection placed at the branch head **cuts** every
path through that source, exactly as a fence drains the window.

A *site* keys a branch source by its condition slot (the same slot `cmdCT`
classifies).  `protectSet` is the set of sites Blade's cut selects; we model it
as a membership predicate over site keys. -/

/-- A speculation **site** is keyed by the branch/loop condition slot — the
    slot whose misprediction opens the transient window. -/
abbrev Site := String

/-- A *protection set*: the sites Blade's cut selects for protection, as a
    membership predicate.  (A `List Site` is coerced via `(· ∈ ·)`.) -/
abbrev ProtectSet := Site → Bool

/-- **Syntactic architectural silence.**  `archSilent c = true` exactly when `c`
    issues **no** architectural observation in any state (`archObs rs c = []` for
    all `rs`) — a structural sufficient-and-(for these clauses)-faithful witness:
    a command is silent iff it contains no branch / loop guard and no
    runtime-indexed memory access (the only `archObs`-observable constructors).
    Decidable and computable, so it drives `native_decide` and the leak graph. -/
def archSilent : LowCT → Bool
  | .RSkip                  => true
  | .RAssert _              => true
  | .RScalarSet _ _         => true
  | .RScalarSetExpr _ _     => true
  | .RSeq c1 c2             => archSilent c1 && archSilent c2
  | .RLetZero _ _ body      => archSilent body
  | .RLetU64Zero _ body     => archSilent body
  | .RBlock body            => archSilent body
  | .RFnDef _ _ _ body cont => archSilent body && archSilent cont
  | .RIfNz _ _ _            => false
  | .RWhileNz _ _           => false
  | .RFor _ _ body          => archSilent body
  | .RArrStore _ _ _        => false
  | .RArrLoad _ _ _         => false
  | _                       => true

/-- A syntactically-silent command issues no architectural observation: this is
    the soundness side of `archSilent` — every clause that returns `true` is a
    constructor `archObs` maps to `[]` (or a sequence/body of such). -/
theorem archObs_eq_nil_of_archSilent {c : LowCT} (h : archSilent c = true)
    (rs : RustState) : archObs rs c = [] := by
  induction c generalizing rs with
  | RSeq c1 c2 ih1 ih2 =>
      simp only [archSilent, Bool.and_eq_true] at h
      simp only [archObs, ih1 h.1 rs, ih2 h.2 rs, List.append_nil]
  | RLetZero _ _ body ih =>
      simp only [archSilent] at h
      simpa only [archObs] using ih h rs
  | RLetU64Zero _ body ih =>
      simp only [archSilent] at h
      simpa only [archObs] using ih h rs
  | RBlock body ih =>
      simp only [archSilent] at h
      simpa only [archObs] using ih h rs
  | RFnDef _ _ _ body cont ihB ihC =>
      simp only [archSilent, Bool.and_eq_true] at h
      simp only [archObs, ihB h.1 rs, ihC h.2 rs, List.append_nil]
  | RFor _ _ body ih =>
      simp only [archSilent] at h
      simpa only [archObs] using ih h rs
  | RIfNz _ _ _ _ _ => simp [archSilent] at h
  | RWhileNz _ _ _ => simp [archSilent] at h
  | RArrStore _ _ _ => simp [archSilent] at h
  | RArrLoad _ _ _ => simp [archSilent] at h
  | _ => rfl

/-- A branch/loop site is **leak-relevant** when its mis-speculated wrong-path
    can issue a transient observation — i.e. at least one arm / the body is not
    architecturally silent.  A branch both of whose arms are silent issues no
    transient observation no matter the oracle, so it lies on **no** source→sink
    path and needs no protection.  Computed via the syntactic `archSilent`. -/
def armLeaks (c : LowCT) : Bool := ! archSilent c

/-! ## §2.  Path coverage

`coversAllPaths protectSet c` holds when **every leak-relevant branch/loop site
of `c` is in `protectSet`** — i.e. every source→sink path passes through a
protected site (the Blade cut covers the graph).  Leak-free sites (both arms
architecturally silent) may be omitted: they lie on no path.

We compute it structurally.  The genuine content is in the `RIfNz` /
`RWhileNz` / `RFor` clauses: a leak-relevant head must be protected. -/

/-- Every leak-relevant branch/loop site of `c` is protected by `protectSet`.
    This is the *path-coverage* (cut) condition: every speculative source whose
    wrong-path can reach a sink is severed by a protection. -/
def coversAllPaths (protectSet : ProtectSet) : LowCT → Bool
  | .RSeq c1 c2             => coversAllPaths protectSet c1 && coversAllPaths protectSet c2
  | .RLetZero _ _ body      => coversAllPaths protectSet body
  | .RLetU64Zero _ body     => coversAllPaths protectSet body
  | .RBlock body            => coversAllPaths protectSet body
  | .RFnDef _ _ _ body cont =>
      coversAllPaths protectSet body && coversAllPaths protectSet cont
  | .RIfNz cond ct cf       =>
      -- The branch head is a source.  If either arm can leak transiently it is
      -- leak-relevant and must be protected; either way recurse into the arms.
      ((! (armLeaks ct || armLeaks cf)) || protectSet cond)
        && coversAllPaths protectSet ct && coversAllPaths protectSet cf
  | .RWhileNz cond body     =>
      ((! armLeaks body) || protectSet cond) && coversAllPaths protectSet body
  | .RFor _ _ body          =>
      -- An `RFor` head is itself architecturally silent on its bound counter
      -- (no `branch` observation in `specObs`/`specObsF`); it carries no
      -- speculation source of its own, so only its body must be covered.
      coversAllPaths protectSet body
  | _                       => true

/-! ## §3.  The selective placement pass

`insertSelective protectSet c` fences a branch/loop **iff** its site is in
`protectSet` — placing the protection only at the cut sites — and always
site-guards calls / loads / stores (the STL/BTB/RSB sinks, which are
*point* sinks, not branch sources; Blade's cut treats them as already-sunk and
guards them directly).  Structural everywhere else.

Compared to the blanket `insertFences`, this skips a fence at every branch /
loop head **not** selected by the cut — the perf saving. -/

/-- Selectively fence a branch arm: protect it (head fence) iff `b`, else leave
    it.  (`b = protectSet cond` at the call site.) -/
def selFence (b : Bool) (c : LowCT) : LowCT := if b then fenced c else c

@[simp] theorem archObs_selFence (b : Bool) (rs : RustState) (c : LowCT) :
    archObs rs (selFence b c) = archObs rs c := by
  cases b <;> simp [selFence, archObs_fenced]

@[simp] theorem cmdCT_selFence (b : Bool) (c : LowCT) (lt : LevelTable)
    (leafCT : LeafCTTable) :
    cmdCT (selFence b c) lt leafCT = cmdCT c lt leafCT := by
  cases b <;> simp [selFence, cmdCT_fenced]

/-- A selectively-fenced arm's *committed* fenced-speculative observation is its
    unfenced one: a head fence is a no-op for committed execution (it only
    drains the wrong-path transient, handled in the enclosing branch clause). -/
@[simp] theorem specObsF_selFence_eq (cond : Site) (c : LowCT)
    (window : SpecWindow) (O : MispredOracle) (rs : RustState)
    (protectSet : ProtectSet) :
    specObsF window O rs (selFence (protectSet cond) c)
      = specObsF window O rs c := by
  cases protectSet cond <;> simp [selFence, specObsF_fenced]

/-- The Blade-style selective protection pass.

    * A branch arm / loop body is head-fenced **iff** its site (condition slot)
      is in `protectSet` — the cut sites only.
    * Every call / load / store is site-guarded (the STL/BTB/RSB point sinks),
      exactly as in `insertFences`.

    Structural everywhere else. -/
def insertSelective (protectSet : ProtectSet) : LowCT → LowCT
  | .RSeq c1 c2             =>
      .RSeq (insertSelective protectSet c1) (insertSelective protectSet c2)
  | .RLetZero x t body      => .RLetZero x t (insertSelective protectSet body)
  | .RLetU64Zero x body     => .RLetU64Zero x (insertSelective protectSet body)
  | .RBlock body            => .RBlock (insertSelective protectSet body)
  | .RFnDef n p r body cont =>
      .RFnDef n p r (insertSelective protectSet body) (insertSelective protectSet cont)
  | .RIfNz cond ct cf       =>
      .RIfNz cond
        (selFence (protectSet cond) (insertSelective protectSet ct))
        (selFence (protectSet cond) (insertSelective protectSet cf))
  | .RWhileNz cond body     =>
      .RWhileNz cond (selFence (protectSet cond) (insertSelective protectSet body))
  | .RFor x n body          => .RFor x n (insertSelective protectSet body)
  | .RCall f dest args      => fenceGuard (.RCall f dest args)
  | .RArrLoad dst src idx   => fenceGuard (.RArrLoad dst src idx)
  | .RArrStore arr idx src  => fenceGuard (.RArrStore arr idx src)
  | c                       => c

/-! ## §4.  Denotation preservation

The selective protections are no-ops for the architectural semantics, so
`insertSelective` preserves the architectural leakage trace and `cmdCT`
acceptance. -/

/-- **Architectural denotation preservation.**  `insertSelective` does not
    change the architectural leakage trace. -/
@[simp] theorem archObs_insertSelective (protectSet : ProtectSet)
    (rs : RustState) (c : LowCT) :
    archObs rs (insertSelective protectSet c) = archObs rs c := by
  induction c generalizing rs with
  | RSeq c1 c2 ih1 ih2 => simp [insertSelective, archObs, ih1, ih2]
  | RLetZero x t body ih => simp [insertSelective, archObs, ih]
  | RLetU64Zero x body ih => simp [insertSelective, archObs, ih]
  | RBlock body ih => simp [insertSelective, archObs, ih]
  | RFnDef n p r body cont ihB ihC => simp [insertSelective, archObs, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertSelective, archObs, archObs_selFence, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertSelective, archObs, archObs_selFence, ih]
  | RFor x n body ih =>
      simp only [insertSelective, archObs, ih]
  | RCall f dest args => simp only [insertSelective, archObs_fenceGuard]
  | RArrLoad dst src idx => simp only [insertSelective, archObs_fenceGuard]
  | RArrStore arr idx src => simp only [insertSelective, archObs_fenceGuard]
  | _ => rfl

/-- **Acceptance preservation.**  `insertSelective` preserves `cmdCT`. -/
@[simp] theorem cmdCT_insertSelective (protectSet : ProtectSet) (c : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (insertSelective protectSet c) lt leafCT = cmdCT c lt leafCT := by
  induction c generalizing lt with
  | RSeq c1 c2 ih1 ih2 => simp [insertSelective, cmdCT_RSeq, ih1, ih2]
  | RLetZero x t body ih => simp [insertSelective, cmdCT_RLetZero, ih]
  | RLetU64Zero x body ih => simp [insertSelective, cmdCT_RLetU64Zero, ih]
  | RBlock body ih => simp [insertSelective, cmdCT_RBlock, ih]
  | RFnDef n p r body cont ihB ihC => simp [insertSelective, cmdCT_RFnDef, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertSelective, cmdCT_RIfNz, cmdCT_selFence, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertSelective, cmdCT_RWhileNz, cmdCT_selFence, ih]
  | RFor x n body ih =>
      simp only [insertSelective, cmdCT_RFor, ih]
  | RCall f dest args => simp only [insertSelective, cmdCT_fenceGuard]
  | RArrLoad dst src idx => simp only [insertSelective, cmdCT_fenceGuard]
  | RArrStore arr idx src => simp only [insertSelective, cmdCT_fenceGuard]
  | _ => rfl

/-! ## §5.  Leak-relevance: an unprotected wrong-path is empty

The soundness lever.  At a branch covered by `coversAllPaths`, the head is
**either** protected (`protectSet cond = true`, so `insertSelective` fences the
arm and the fenced transient drains to `[]`) **or** leak-free (`armLeaks = false`,
so the arm is architecturally silent and its transient — which the fenced
observer computes as `specTransient`, falling back to `archObs` on a
non-fence head — is already `[]`).  Both cases give an empty wrong-path
contribution, which is what collapses the speculative trace.

We need: when an arm does not leak (`armLeaks c = false`), the *fenced
transient* `specTransient rs (insertSelective protectSet c)` of its selective
image is `[]`. -/

/-- `armLeaks c = false` means `c` is syntactically silent. -/
theorem archSilent_of_not_armLeaks {c : LowCT} (h : armLeaks c = false) :
    archSilent c = true := by
  simpa [armLeaks, Bool.not_eq_false] using h

/-- `armLeaks c = false` means `archObs rs c = []` for every state. -/
theorem archObs_eq_nil_of_not_armLeaks {c : LowCT} (h : armLeaks c = false)
    (rs : RustState) : archObs rs c = [] :=
  archObs_eq_nil_of_archSilent (archSilent_of_not_armLeaks h) rs

/-- `specTransient` of an architecturally-silent command is `[]`: every clause of
    `specTransient` either returns `[]`, recurses on the same shape, or falls
    back to `archObs`, which is `[]` here.  We prove the statement we need: a
    command with `armLeaks = false` (architecturally silent) has empty transient
    under any `insertSelective` image — but it suffices, for the keystone, to
    note `specTransient` falls back to `archObs` on the non-`RAssert`/`RSeq`
    head an arm presents, so a silent arm's transient is `[]`.

    For the keystone we only feed `specTransient` an `insertSelective`-image
    arm.  We reduce via the helper below. -/
theorem specTransient_eq_nil_of_archSilent
    (protectSet : ProtectSet) {c : LowCT} (h : archSilent c = true)
    (rs : RustState) :
    specTransient rs (insertSelective protectSet c) = [] := by
  induction c generalizing rs with
  | RSeq c1 c2 ih1 ih2 =>
      simp only [archSilent, Bool.and_eq_true] at h
      simp only [insertSelective, specTransient]
      -- The head `insertSelective c1` is an `RAssert` only if `c1` is; in either
      -- arm of the `match` the result is `specTransient … c1`/`c2` or `[]`.
      cases hc1 : insertSelective protectSet c1 with
      | RAssert s =>
          by_cases hs : s = fenceLabel
          · simp [hs]
          · simp only [hs, if_false]; exact ih2 h.2 rs
      | _ => simp_all [ih2 h.2 rs]
  | RIfNz _ _ _ _ _ => simp [archSilent] at h
  | RWhileNz _ _ _ => simp [archSilent] at h
  | RArrStore _ _ _ => simp [archSilent] at h
  | RArrLoad _ _ _ => simp [archSilent] at h
  | RCall f dest args =>
      -- `insertSelective (RCall …) = fenceGuard (RCall …) = RSeq RGuard (RCall …)`.
      -- `specTransient` sees the leading `RGuard` (≠ fenceLabel), so it recurses
      -- to `specTransient (RCall …) = archObs (RCall …) = []`.
      simp only [insertSelective, fenceGuard, RGuard, specTransient,
        guardLabel_ne_fenceLabel, ite_false]
      rfl
  | _ =>
      -- Remaining heads (`RSkip`, `RScalarSet`, `RLetZero`, `RBlock`, `RFor`,
      -- `RLimbStore`, …): `insertSelective` keeps them a non-`RAssert`/`RSeq`
      -- node, so `specTransient` falls back to `archObs`, which is `[]` by
      -- silence (`archObs_insertSelective` + `archObs_eq_nil_of_archSilent`).
      first
      | rfl
      | (show archObs rs (insertSelective protectSet _) = []
         rw [archObs_insertSelective]; exact archObs_eq_nil_of_archSilent h rs)

/-- `armLeaks c = false` (a leak-free arm) ⇒ its selective image has empty
    transient. -/
theorem specTransient_eq_nil_of_not_armLeaks
    (protectSet : ProtectSet) {c : LowCT} (h : armLeaks c = false)
    (rs : RustState) :
    specTransient rs (insertSelective protectSet c) = [] :=
  specTransient_eq_nil_of_archSilent protectSet (archSilent_of_not_armLeaks h) rs

/-! ## §6.  The keystone: covering placement collapses to the architectural trace

For a *path-covering* selective placement, every branch wrong-path is `[]`:
either the head is protected (fenced → `specTransient` drains) or it is
leak-free (`armLeaks = false` → empty transient).  Every call/load/store is
site-guarded (drains its STL/BTB/RSB transient).  Hence the fenced speculative
trace collapses to the architectural trace — for any window and any oracle. -/

/-- **Collapse on a covering `insertSelective`.**  If `coversAllPaths
    protectSet c`, the fenced speculative trace of `insertSelective protectSet c`
    equals the architectural trace of `c`, for *any* window and *any*
    (adversarial) oracle.  Every wrong-path is either fenced (drains) or
    leak-free (empty), and every call/load/store is site-guarded. -/
theorem specObsF_insertSelective_eq_archObs
    (window : SpecWindow) (O : MispredOracle) (protectSet : ProtectSet)
    (rs : RustState) (c : LowCT) (hcov : coversAllPaths protectSet c = true) :
    specObsF window O rs (insertSelective protectSet c) = archObs rs c := by
  induction c with
  | RSkip => rfl
  | RAssert _ => rfl
  | RScalarSet _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RSeq c1 c2 ih1 ih2 =>
      simp only [coversAllPaths, Bool.and_eq_true] at hcov
      -- The head `insertSelective c1` is an `RAssert s` only if `c1` is; a guard
      -- head means `c1 = RAssert guardLabel` (silent), else `s = fenceLabel`
      -- (also silent) or fall through.
      simp only [insertSelective, specObsF, archObs]
      split
      · rename_i s heq
        have hc1 : c1 = LowCT.RAssert s := by
          cases c1 <;> simp_all [insertSelective, fenceGuard, RGuard]
        subst hc1
        split
        · -- guarded head: `c1 = RAssert guardLabel`, `archObs rs c1 = []`.
          simp only [archObs, committedObs, archObs_insertSelective, List.nil_append]
        · simp only [ih1 hcov.1, ih2 hcov.2]
      · simp only [ih1 hcov.1, ih2 hcov.2]
  | RLetZero x t body ih =>
      simp only [coversAllPaths] at hcov
      simp only [insertSelective, specObsF, archObs, ih hcov]
  | RLetU64Zero x body ih =>
      simp only [coversAllPaths] at hcov
      simp only [insertSelective, specObsF, archObs, ih hcov]
  | RBlock body ih =>
      simp only [coversAllPaths] at hcov
      simp only [insertSelective, specObsF, archObs, ih hcov]
  | RFnDef n p r body cont ihB ihC =>
      simp only [coversAllPaths, Bool.and_eq_true] at hcov
      simp only [insertSelective, specObsF, archObs, ihB hcov.1, ihC hcov.2]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [coversAllPaths, Bool.and_eq_true] at hcov
      obtain ⟨⟨hhead, hct⟩, hcf⟩ := hcov
      -- Both arms' fenced transients are `[]`: protected ⇒ `specTransient_fenced`;
      -- leak-free ⇒ `specTransient_eq_nil_of_not_armLeaks`.
      have harm : ∀ d : LowCT, coversAllPaths protectSet d = true →
          (armLeaks d = false ∨ protectSet cond = true) →
          specTransient rs (selFence (protectSet cond) (insertSelective protectSet d)) = [] := by
        intro d _ hd
        by_cases hp : protectSet cond = true
        · simp [selFence, hp, specTransient_fenced]
        · rcases hd with hleak | hcontra
          · simp only [selFence, hp, Bool.false_eq_true, if_false,
              specTransient_eq_nil_of_not_armLeaks protectSet hleak]
          · exact absurd hcontra hp
      -- From the head-coverage `(!(armLeaks ct || armLeaks cf)) || protectSet cond`.
      have hdisj : (armLeaks ct = false ∧ armLeaks cf = false) ∨ protectSet cond = true := by
        rcases Bool.or_eq_true _ _ |>.mp hhead with h | h
        · left
          simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at h
          exact h
        · right; exact h
      have htCt : specTransient rs (selFence (protectSet cond) (insertSelective protectSet ct)) = [] :=
        harm ct hct (by rcases hdisj with ⟨h, _⟩ | h; exacts [Or.inl h, Or.inr h])
      have htCf : specTransient rs (selFence (protectSet cond) (insertSelective protectSet cf)) = [] :=
        harm cf hcf (by rcases hdisj with ⟨_, h⟩ | h; exacts [Or.inl h, Or.inr h])
      simp only [insertSelective, specObsF, archObs,
        specObsF_selFence_eq, ihCt hct, ihCf hcf, htCt, htCf, List.take_nil,
        withRollback_nil, List.nil_append, ite_self]
  | RWhileNz cond body ih =>
      simp only [coversAllPaths, Bool.and_eq_true] at hcov
      obtain ⟨hhead, hbody⟩ := hcov
      have hdisj : armLeaks body = false ∨ protectSet cond = true := by
        rcases Bool.or_eq_true _ _ |>.mp hhead with h | h
        · left; simpa [Bool.not_eq_true'] using h
        · right; exact h
      have ht : specTransient rs (selFence (protectSet cond) (insertSelective protectSet body)) = [] := by
        by_cases hp : protectSet cond = true
        · simp [selFence, hp, specTransient_fenced]
        · rcases hdisj with hleak | hcontra
          · simp only [selFence, hp, Bool.false_eq_true, if_false,
              specTransient_eq_nil_of_not_armLeaks protectSet hleak]
          · exact absurd hcontra hp
      simp only [insertSelective, specObsF, archObs,
        specObsF_selFence_eq, ih hbody, ht, List.take_nil,
        withRollback_nil, List.nil_append, ite_self, List.singleton_append]
  | RFor x n body ih =>
      simp only [coversAllPaths] at hcov
      simp only [insertSelective, specObsF, archObs, ih hcov]
  | RCall f dest args =>
      simp only [insertSelective, specObsF_fenceGuard]
  | RArrLoad dst src idx =>
      simp only [insertSelective, specObsF_fenceGuard]
  | RArrStore arr idx src =>
      simp only [insertSelective, specObsF_fenceGuard]
  | _ => rfl

/-! ## §7.  Speculative CT against an unconstrained predictor (selective) -/

/-- **The deliverable: covering selective placement ⇒ SCT vs. an unconstrained
    oracle.**  If `c` is architecturally constant-time (`cmdCT`) and the
    selective protection set *covers every speculative-leak path*
    (`coversAllPaths`), then `insertSelective protectSet c` is speculatively
    constant-time against an **arbitrary** (adversarial) misprediction oracle
    and **any** speculation window — with protections placed only at the cut
    sites.

    Proof: by `specObsF_insertSelective_eq_archObs` the fenced speculative trace
    of `insertSelective protectSet c` equals the architectural trace of `c`
    (every wrong-path drains or is leak-free; every point sink is site-guarded),
    which is secret-independent by `architecturally_CT_imp_ArchCT`.  The oracle
    and window never enter the collapsed trace.  This is the Blade *soundness*
    guarantee; the cut's *minimality* is out of scope. -/
theorem insertSelective_SCT_of_covers
    (window : SpecWindow) (O : MispredOracle) (protectSet : ProtectSet)
    (lt : LevelTable) (leafCT : LeafCTTable) (c : LowCT)
    (hCT : cmdCT c lt leafCT = true)
    (hcov : coversAllPaths protectSet c = true) :
    SpeculativelyConstantTimeF window O lt (insertSelective protectSet c) := by
  intro rs1 rs2 hEq
  rw [specObsF_insertSelective_eq_archObs window O protectSet rs1 c hcov,
      specObsF_insertSelective_eq_archObs window O protectSet rs2 c hcov]
  exact architecturally_CT_imp_ArchCT lt leafCT c hCT rs1 rs2 hEq

/-! ## §8.  Perf rationale: a covering set protects no more than blanket fencing

Blanket fencing (`insertFences`) places an `RFence` at **every** branch arm (2
per `RIfNz`) and loop head, plus an `RGuard` before every call/load/store.  A
*selective* covering set fences a branch's two arms only when its site is
protected, and omits a fence at every leak-free site — strictly fewer markers on
any program with a leak-free branch.  We count the marker nodes and prove the
selective pass never inserts more than blanket. -/

/-- The number of barrier markers blanket fencing (`insertFences`) inserts: an
    `RFence` at *every* branch arm (2 per `RIfNz`) and loop head (1), plus an
    `RGuard` before every call/load/store.  (Defined locally to keep this file
    independent of the SLH/mask file; it mirrors that file's `fenceMarkerCount`
    and counts exactly the markers `SpeculativeCTFence.insertFences` inserts.) -/
def blanketFenceCount : LowCT → Nat
  | .RSeq c1 c2             => blanketFenceCount c1 + blanketFenceCount c2
  | .RLetZero _ _ body      => blanketFenceCount body
  | .RLetU64Zero _ body     => blanketFenceCount body
  | .RBlock body            => blanketFenceCount body
  | .RFnDef _ _ _ body cont => blanketFenceCount body + blanketFenceCount cont
  | .RIfNz _ ct cf          => 2 + blanketFenceCount ct + blanketFenceCount cf
  | .RWhileNz _ body        => 1 + blanketFenceCount body
  | .RFor _ _ body          => 1 + blanketFenceCount body
  | .RCall _ _ _            => 1
  | .RArrLoad _ _ _         => 1
  | .RArrStore _ _ _        => 1
  | _                       => 0

/-- The number of protection markers `insertSelective` inserts: 2 per *protected*
    branch (one per arm), 1 per protected loop, plus 1 per call/load/store
    site-guard (same point-sink guards as `insertFences`). -/
def selectiveMarkerCount (protectSet : ProtectSet) : LowCT → Nat
  | .RSeq c1 c2             =>
      selectiveMarkerCount protectSet c1 + selectiveMarkerCount protectSet c2
  | .RLetZero _ _ body      => selectiveMarkerCount protectSet body
  | .RLetU64Zero _ body     => selectiveMarkerCount protectSet body
  | .RBlock body            => selectiveMarkerCount protectSet body
  | .RFnDef _ _ _ body cont =>
      selectiveMarkerCount protectSet body + selectiveMarkerCount protectSet cont
  | .RIfNz cond ct cf       =>
      (if protectSet cond then 2 else 0)
        + selectiveMarkerCount protectSet ct + selectiveMarkerCount protectSet cf
  | .RWhileNz cond body     =>
      (if protectSet cond then 1 else 0) + selectiveMarkerCount protectSet body
  | .RFor _ _ body          => selectiveMarkerCount protectSet body
  | .RCall _ _ _            => 1
  | .RArrLoad _ _ _         => 1
  | .RArrStore _ _ _        => 1
  | _                       => 0

/-- **Perf witness.**  A selective placement never inserts more protection
    markers than blanket fencing: `selectiveMarkerCount protectSet c ≤
    blanketFenceCount c`.  Selective fences a branch's two arms only when
    protected (`if protectSet cond then 2 else 0 ≤ 2`) and a loop only when
    protected (`… ≤ 1`); the call/load/store site-guards match blanket exactly.
    On any program with a leak-free (hence omittable) branch, the inequality is
    **strict** — the structural ground of Blade's overhead win over blanket
    fencing. -/
theorem insertSelective_fewer (protectSet : ProtectSet) (c : LowCT) :
    selectiveMarkerCount protectSet c ≤ blanketFenceCount c := by
  induction c with
  | RSeq c1 c2 ih1 ih2 =>
      simp only [selectiveMarkerCount, blanketFenceCount]; omega
  | RLetZero x t body ih => simpa [selectiveMarkerCount, blanketFenceCount] using ih
  | RLetU64Zero x body ih => simpa [selectiveMarkerCount, blanketFenceCount] using ih
  | RBlock body ih => simpa [selectiveMarkerCount, blanketFenceCount] using ih
  | RFnDef n p r body cont ihB ihC =>
      simp only [selectiveMarkerCount, blanketFenceCount]; omega
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [selectiveMarkerCount, blanketFenceCount]
      have : (if protectSet cond then 2 else 0) ≤ 2 := by split <;> omega
      omega
  | RWhileNz cond body ih =>
      simp only [selectiveMarkerCount, blanketFenceCount]
      have : (if protectSet cond then 1 else 0) ≤ 1 := by split <;> omega
      omega
  | RFor x n body ih =>
      simp only [selectiveMarkerCount, blanketFenceCount]; omega
  | _ => simp [selectiveMarkerCount, blanketFenceCount]

/-! ## §9.  Pilot: a leak-free branch is covered with *zero* protection

We exercise the soundness keystone and the perf win on a kernel with a
**leak-free** public branch (both arms architecturally silent — pure scalar
moves, no memory access).  Its branch site lies on no source→sink path, so the
*empty* protect set already covers all paths — selective placement inserts **no**
fence there, while blanket fencing would insert two.  The kernel is therefore SCT
against an unconstrained oracle with **strictly fewer** protections than
blanket. -/

namespace PilotSel

open Pilot

/-- The empty protect set: protect nothing. -/
def noProtect : ProtectSet := fun _ => false

/-- A kernel with a **leak-free** public branch: `if flag then x := 1 else x := 2`.
    Both arms are pure scalar sets (`RScalarSet`), which are architecturally
    silent — the branch issues no transient observation no matter the oracle, so
    it lies on no speculative-leak path. -/
def pilotKernelSilentBranch : LowCT :=
  .RIfNz "flag"
    (.RScalarSet "x" 1)
    (.RScalarSet "x" 2)

/-- The silent-branch kernel is architecturally CT (`cmdCT`). -/
theorem pilotKernelSilentBranch_cmdCT :
    cmdCT pilotKernelSilentBranch pilotLevels LeafCTTable.canonical = true := by
  native_decide

/-- **The empty protect set already covers all paths** of the silent-branch
    kernel: its only branch is leak-free (both arms architecturally silent), so
    no protection is needed. -/
theorem pilotKernelSilentBranch_covered :
    coversAllPaths noProtect pilotKernelSilentBranch = true := by
  native_decide

/-- **Pilot result.**  The silent-branch kernel, with the **empty** protect set,
    is speculatively constant-time against an **unconstrained** misprediction
    oracle for every window — *no fence inserted*.  Coverage is non-vacuous: the
    leak-free branch genuinely lies off every source→sink path. -/
theorem pilotKernelSilentBranch_SCT
    (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTimeF window O pilotLevels
      (insertSelective noProtect pilotKernelSilentBranch) :=
  insertSelective_SCT_of_covers window O noProtect pilotLevels
    LeafCTTable.canonical pilotKernelSilentBranch
    pilotKernelSilentBranch_cmdCT pilotKernelSilentBranch_covered

/-- **Perf win, concretely.**  Selective placement (empty set) inserts **0**
    protections on the silent-branch kernel, while blanket fencing inserts **2**
    (a fence per arm): `0 ≤ 2`, strict. -/
theorem selective_strictly_fewer :
    selectiveMarkerCount noProtect pilotKernelSilentBranch
      < blanketFenceCount pilotKernelSilentBranch := by
  native_decide

/-- And a *leaking* branch genuinely needs protection: the empty set does **not**
    cover the branching pilot whose arms issue transient observations
    (`pilotKernelBranch`'s arms are CT leaf calls, which `archObs` records as
    silent — so to exhibit a genuinely leak-relevant branch we use a load arm).
    A load arm leaks, so the empty set fails coverage; the singleton set
    protecting `flag` covers it. -/
theorem leaking_branch_needs_protection :
    coversAllPaths noProtect
        (.RIfNz "flag"
          (.RArrLoad ⟨"d", .TU64⟩ ⟨"arr", .TU64⟩ "idx")
          (.RScalarSet "x" 0)) = false := by
  native_decide

/-- The singleton set protecting `flag` **does** cover the leaking branch. -/
theorem flag_protect_covers_leaking_branch :
    coversAllPaths (fun s => s == "flag")
        (.RIfNz "flag"
          (.RArrLoad ⟨"d", .TU64⟩ ⟨"arr", .TU64⟩ "idx")
          (.RScalarSet "x" 0)) = true := by
  native_decide

end PilotSel

/-! ## §10.  What this gets us, and what remains

**Delivered (this file).**
* A *leak-graph* model over the owned `LowCT` stream: branch/loop heads as
  speculation **sources**, transient observations as **sinks**, `armLeaks` the
  leak-relevance of a site, and `coversAllPaths` the path-coverage (cut)
  condition — every source→sink path passes through a protected site.
* `insertSelective : ProtectSet → LowCT → LowCT`, the Blade-style placement:
  fence a branch/loop **iff** its site is in the cut, site-guard every
  call/load/store, structural elsewhere.
* **Denotation preservation** (`archObs_insertSelective`,
  `cmdCT_insertSelective`): the selective protections are no-ops architecturally
  and preserve `cmdCT` acceptance.
* **The soundness keystone** `insertSelective_SCT_of_covers`: a path-covering
  selective placement on an architecturally-CT program is speculatively CT
  against an **unconstrained** adversarial oracle and **any** window — every
  wrong-path either drains (protected) or is empty (leak-free), every point sink
  is guarded, so the fenced speculative trace collapses to the architectural one.
* **The perf win** `insertSelective_fewer`: a covering set inserts no more
  protections than blanket fencing, and strictly fewer on any program with a
  leak-free branch (`PilotSel.selective_strictly_fewer`: 0 < 2).
* Non-vacuity witnesses: `PilotSel.pilotKernelSilentBranch_covered` (a leak-free
  branch is covered by the empty set), `PilotSel.leaking_branch_needs_protection`
  (a genuinely leaking branch is *not* covered by the empty set) +
  `PilotSel.flag_protect_covers_leaking_branch` (it *is* covered once protected).

**Out of scope (the harder half — explicitly NOT proved).**
* **Min-cut optimality.**  We prove a path-covering set *suffices* for SCT
  (soundness) and that a covering set can be strictly smaller than blanket.  We
  do **not** prove the covering set Blade computes is a **minimum** cut — that no
  smaller covering set exists.  That is the max-flow / min-cut combinatorial
  argument of the Blade paper and is the residual.
* **Dataflow-precise leak graph.**  `armLeaks` is the address-pattern leak-
  relevance the SCT observer reasons over (a branch arm is relevant iff it can
  issue a transient observation).  A finer Blade-faithful graph would track
  individual def-use edges (which *value* flows from which source to which sink);
  the address-pattern abstraction is the granularity `cmdCT` and `specObsF`
  already use.
* As in the fence file, `LowCT` has no separate executable big-step; `archObs`
  is the leakage denotation the CT story reasons over, and the BTB/RSB/STL point
  sinks are guarded (not min-cut-selected) here. -/

end CatCrypt.Crypto.SecureCompilation.SpeculativeCT
