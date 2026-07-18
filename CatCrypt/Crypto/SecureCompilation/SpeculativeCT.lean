/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Speculative Constant-Time (SCT) for the owned `LowCT` instruction stream

**Task #564 PILOT** — re-opens the deferred RHP-4 (Spectre) line now that the
pipeline *owns* the instruction stream (`LowCT`).  This file delivers the
*foundation* for speculative constant-time, in the style of Cauligi et al.,
"Constant-Time Foundations for the New Spectre Era" (PLDI 2020), and one
structural keystone lemma — it does **not** attempt to "solve Spectre".

## What this provides

1. **Speculative leakage semantics** (`SpecState`, `specObs`, `specObsList`):
   the architectural leakage observation of `LowCT` is the sequence of
   *branch-condition values* and *runtime memory-index values* an attacker
   reads (the pc / memory-address pattern).  We extend the architectural
   observer with a **speculation window** and a **misprediction oracle**:
   on a branch, the oracle may mis-predict and speculatively execute the
   *wrong* path for up to a bounded window, accumulating its leakage
   observations, then roll back.

2. **The SCT predicate** (`SpeculativelyConstantTime`): two executions whose
   inputs agree on the PUBLIC slots produce the *same* speculative leakage
   trace.  This is the speculative analogue of the architectural
   `PublicEquiv → PublicEquiv` noninterference proved by `cmdCT_sound`
   (`LowCTCTAnalysis.lean`).

3. **The structural keystone** (`architecturally_CT_imp_SCT`): for a
   program accepted by the architectural CT analyser `cmdCT` (every branch
   condition and every memory index is `Public`), the speculative leakage
   trace is a function of the PUBLIC state alone — so SCT follows.  The
   intuition formalised: if every branch / index is public, then both the
   architectural observations AND the misprediction oracle's choices (which
   we constrain to be driven by the public branch decisions, `PublicDriven`)
   are public-determined; the spec-leak-trace therefore adds nothing
   secret-dependent.

## Scope (honest)

* The leakage observable is the **pc + memory-address pattern** — branch
  decisions and runtime memory indices.  This is exactly the granularity at
  which Spectre-PHT / Spectre-STL leak, and the granularity `cmdCT` already
  reasons about.  Data values inside leaves are not modelled (they are not
  address-pattern leakage; leaf CT is delegated, as in `cmdCT_sound`).
* The model is a *clean structural* observer over `LowCT`, parameterised by
  the misprediction oracle.  It is NOT wired through the relational
  `RustExec` big-step (which would re-derive the whole operational
  semantics); the architectural projection of `specObs` is the structural
  branch/index trace, and that is what the keystone reasons over.
* A real fence/SLH pass (which would *discharge* the `PublicDriven` oracle
  obligation for an arbitrary attacker-controlled predictor) is future
  work — see the closing note.

## References

* Cauligi, Disselkoen, von Gleissenthall, Tullsen, Stefan, Rezk, Barthe,
  "Constant-Time Foundations for the New Spectre Era", PLDI 2020.
* Barthe et al., "System-Level Non-Interference for Constant-Time
  Cryptography", CCS 2014 (the architectural baseline `cmdCT` extends).
-/

namespace CatCrypt.Crypto.SecureCompilation.SpeculativeCT

open CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-! ## §1.  Leakage observations

The attacker observes the *pc / memory-address pattern*: at every branch the
condition value (which way control went), and at every runtime-indexed memory
access the index value.  Pure data-flow (leaf arithmetic) is not address
leakage and is delegated to the leaf-CT table, exactly as in `cmdCT_sound`. -/

/-- A single leakage observation.  The first three constructors are the
    architectural / Spectre-PHT (v1) observable (branch decisions, runtime
    memory indices, and the speculation-rollback marker).  The last three
    (added 2026-06) extend the observable to the remaining Spectre transient
    sources, each modelled as the runtime value of the *slot* the speculative
    microarchitectural structure reads:

    * `indirectTarget` — **Spectre-v2 / BTB**: an indirect call/branch whose
      speculative target is taken from a runtime *target slot* (the register
      holding the callee address).  The attacker reads the target value the
      branch-target buffer steered to.
    * `retTarget` — **Spectre-RSB**: a return whose speculative target is the
      (possibly-mispredicted) return-stack top, modelled as a runtime *return
      slot* value.
    * `stlForward` — **Spectre-v4 / STL** (speculative store bypass): a load
      that speculatively bypasses a prior store and forwards a stale value;
      the attacker reads the load's *address slot* used for the bypassed
      forward. -/
inductive Obs where
  /-- A branch on scalar slot `cond` was reached with runtime value `v`. -/
  | branch (cond : String) (v : Nat) : Obs
  /-- A runtime-indexed memory access on index slot `idxVar` with value `v`. -/
  | memIdx (idxVar : String) (v : Nat) : Obs
  /-- A speculation rollback marker (a mis-speculated window ended). -/
  | rollback : Obs
  /-- **BTB (v2)** indirect-branch/call speculative target: the runtime value
      `v` of the target slot `tgt` the branch-target buffer steered to. -/
  | indirectTarget (tgt : String) (v : Nat) : Obs
  /-- **RSB** speculative return target: the runtime value `v` of the
      return-stack slot `ret` the return speculated to. -/
  | retTarget (ret : String) (v : Nat) : Obs
  /-- **STL (v4)** store-to-load-forward: the runtime value `v` of the
      address slot `addr` a load used to speculatively bypass a prior store. -/
  | stlForward (addr : String) (v : Nat) : Obs
  deriving DecidableEq, Repr, Inhabited

/-- A leakage trace: the sequence of observations. -/
abbrev ObsTrace := List Obs

/-! ## §2.  Architectural (non-speculative) leakage observer

`archObs c rs` is the leakage the attacker sees from the *architecturally
correct* execution of `c` from state `rs`: the branch decisions taken and the
runtime memory indices accessed, in order.

For control flow we read the branch condition from `rs.rsScalar` and descend
into the taken branch.  Because `LowCT` leaves do not feed back into branch
conditions at the granularity this observer cares about (the analyser
`cmdCT` already certifies all conditions/indices come from named slots), we
read every condition/index against the *entry* state `rs`.  This is the same
abstraction `cmdCT_sound` uses: it reasons about which slots the conditions /
indices name, classified by the `LevelTable`. -/
def archObs (rs : RustState) : LowCT → ObsTrace
  | .RSkip                  => []
  | .RAssert _              => []
  | .RScalarSet _ _         => []
  | .RScalarSetExpr _ _     => []
  | .RSeq c1 c2             => archObs rs c1 ++ archObs rs c2
  | .RLetZero _ _ body      => archObs rs body
  | .RLetU64Zero _ body     => archObs rs body
  | .RBlock body            => archObs rs body
  | .RFnDef _ _ _ body cont => archObs rs body ++ archObs rs cont
  | .RIfNz cond ct cf       =>
      -- Observe the branch decision; then the taken path's observations.
      let v := rs.rsScalar cond
      Obs.branch cond v :: (if v ≠ 0 then archObs rs ct else archObs rs cf)
  | .RWhileNz cond body     =>
      -- We observe the guard decision once (the structural observer does
      -- not unroll the loop — the loop *count* leakage is itself a sequence
      -- of `branch cond` observations whose values are public iff `cond` is).
      [Obs.branch cond (rs.rsScalar cond)] ++ archObs rs body
  | .RFor _ _ body          => archObs rs body
  | .RArrStore _ idxVar _   => [Obs.memIdx idxVar (rs.rsScalar idxVar)]
  | .RArrLoad _ _ idxVar    => [Obs.memIdx idxVar (rs.rsScalar idxVar)]
  -- Literal-index / non-indexed / leaf constructors leak no runtime
  -- address pattern (the index is a compile-time constant, or there is no
  -- runtime index at all): no observation.
  | _                       => []

/-! ## §3.  Speculative observer

The speculative semantics extends the architectural one with a *misprediction
oracle* and a *speculation window*.  At each branch the oracle may mispredict;
if it does, the processor speculatively executes the **wrong** path,
accumulating that path's leakage observations for up to `window` further
steps, before a `rollback` marker and resumption of the correct path.

We model the oracle as a function of the *current branch site* and the
*public branch decision*.  A `MispredOracle` returns, at a branch with
condition slot `cond` and observed value `v`, whether to mispredict. -/

/-- A misprediction oracle.  It ranges over **all four** Spectre transient
    sources we model, each as a pure function of the relevant *slot* and its
    runtime value.  Keeping every field a pure function of `(slot, v)` is what
    makes the oracle *unconstrained* yet *public-determined* once `cmdCT`
    certifies the slot public:

    * `mispredict` — **PHT (v1)**: mispredict the conditional branch `cond`?
    * `injectTarget` — **BTB (v2)**: inject a transient indirect target at the
      call site whose target slot is `tgt` (value `v`)?
    * `mispredRet` — **RSB**: mispredict the return-stack top at the return
      site whose return slot is `ret` (value `v`)?
    * `bypassStore` — **STL (v4)**: speculatively bypass the prior store at the
      load whose address slot is `addr` (value `v`)? -/
structure MispredOracle where
  /-- Mispredict at branch `cond` whose runtime value is `v`?  (PHT/v1) -/
  mispredict : (cond : String) → (v : Nat) → Bool
  /-- Inject a speculative indirect target at the call whose target slot is
      `tgt` (runtime value `v`)?  (BTB/v2) -/
  injectTarget : (tgt : String) → (v : Nat) → Bool
  /-- Mispredict the return-stack top at the return whose return slot is `ret`
      (runtime value `v`)?  (RSB) -/
  mispredRet : (ret : String) → (v : Nat) → Bool
  /-- Speculatively bypass a prior store at the load whose address slot is
      `addr` (runtime value `v`)?  (STL/v4) -/
  bypassStore : (addr : String) → (v : Nat) → Bool

/-- The speculation window bound: the number of instructions the processor
    speculatively executes down the wrong path before rolling back.  A real
    machine bounds this by the reorder-buffer size; here it is a parameter. -/
abbrev SpecWindow := Nat

/-- `specObs window O rs c` is the *speculative* leakage trace of `c` from
    `rs` under oracle `O` with window `window`.

    On a branch, we always observe the (architectural) branch decision.  If
    the oracle mispredicts, we *additionally* observe the wrong path's
    leakage (truncated to the window), capped by a `rollback` marker, and
    then continue with the correctly-taken path.  This over-approximates the
    real machine's transient window: a sound model for leakage equality
    (the attacker sees *at least* the mis-speculated observations). -/
def specObs (window : SpecWindow) (O : MispredOracle) (rs : RustState) :
    LowCT → ObsTrace
  | .RSkip                  => []
  | .RAssert _              => []
  | .RScalarSet _ _         => []
  | .RScalarSetExpr _ _     => []
  | .RSeq c1 c2             => specObs window O rs c1 ++ specObs window O rs c2
  | .RLetZero _ _ body      => specObs window O rs body
  | .RLetU64Zero _ body     => specObs window O rs body
  | .RBlock body            => specObs window O rs body
  | .RFnDef _ _ _ body cont =>
      specObs window O rs body ++ specObs window O rs cont
  | .RIfNz cond ct cf       =>
      let v := rs.rsScalar cond
      -- Observe the architectural branch decision.  Then, on each of the two
      -- syntactic paths, contribute its observations either as the
      -- *speculated (mis-predicted) wrong path* (capped to the window, with a
      -- `rollback` marker) or as the *architecturally-taken path*, selected by
      -- the runtime value `v`.  Writing the two recursive calls on `ct` and
      -- `cf` *directly* (rather than through an `if`-bound alias) lets the
      -- structural-recursion checker see them as subterms.
      let obsCt : ObsTrace := specObs window O rs ct
      let obsCf : ObsTrace := specObs window O rs cf
      let speculated : ObsTrace :=
        if O.mispredict cond v then
          (if v ≠ 0 then obsCf else obsCt).take window ++ [Obs.rollback]
        else []
      Obs.branch cond v :: (speculated ++ (if v ≠ 0 then obsCt else obsCf))
  | .RWhileNz cond body     =>
      let v := rs.rsScalar cond
      let obsBody : ObsTrace := specObs window O rs body
      -- A mispredicted loop guard speculatively runs the body once.
      let speculated : ObsTrace :=
        if O.mispredict cond v then
          obsBody.take window ++ [Obs.rollback]
        else []
      Obs.branch cond v :: (speculated ++ obsBody)
  | .RFor _ _ body          => specObs window O rs body
  | .RArrStore _ idxVar _   => [Obs.memIdx idxVar (rs.rsScalar idxVar)]
  | .RArrLoad dst _ idxVar  =>
      -- **STL (v4) speculative store bypass.**  A load may speculatively
      -- forward a stale value bypassing a prior store to the same address.
      -- We model the bypassed forward as an `stlForward` observation on the
      -- load's *index/address slot* (the address the forward keyed on), gated
      -- by the oracle's `bypassStore` decision.  The architectural memory-index
      -- observation is always emitted first.  The address slot read is the
      -- same `idxVar` `cmdCT_RArrLoad` certifies public.
      let stl : ObsTrace :=
        if O.bypassStore idxVar (rs.rsScalar idxVar) then
          [Obs.stlForward idxVar (rs.rsScalar idxVar), Obs.rollback]
        else []
      Obs.memIdx idxVar (rs.rsScalar idxVar) :: (stl ++
        -- a load also pushes/forwards nothing else architecturally; `dst` is
        -- unused architecturally (no further obs).
        (let _ := dst; []))
  | .RCall _ dest _         =>
      -- **BTB (v2) indirect-target injection** and **RSB return-mispredict.**
      -- A call site establishes (i) an indirect-call target register and (ii)
      -- a return address on the return-stack.  We model both speculative
      -- sources on the call's *destination slot* `dest.locVar` (the register
      -- the indirect target / return address occupies in this frame), each
      -- gated by its oracle field.  `cmdCT_RCall` certifies `dest.locVar`
      -- public, so both reads are public-determined.
      let tslot := dest.locVar
      let tv := rs.rsScalar tslot
      let btb : ObsTrace :=
        if O.injectTarget tslot tv then [Obs.indirectTarget tslot tv, Obs.rollback]
        else []
      let rsb : ObsTrace :=
        if O.mispredRet tslot tv then [Obs.retTarget tslot tv, Obs.rollback]
        else []
      btb ++ rsb
  | _                       => []

/-- The architectural projection: with the never-mispredict oracle, the
    speculative observer collapses to the architectural one. -/
def neverMispred : MispredOracle :=
  ⟨fun _ _ => false, fun _ _ => false, fun _ _ => false, fun _ _ => false⟩

/-! ## §4.  Public-driven oracles

For the keystone we constrain the predictor to be *driven by public data*:
its misprediction decision at a branch depends only on the condition slot and
the (public) condition value.  This is automatically satisfied by the
`MispredOracle` shape — `mispredict` is already a function of `(cond, v)`
only — so *any* oracle is public-driven **once the branch value `v` is
public**, which is exactly what `cmdCT` certifies.  We record the property as
a definition for documentation and for the keystone's hypothesis surface. -/

/-- An oracle is *public-determined* at a state pair: it returns the same
    misprediction decision whenever the two states agree on the relevant
    (public) condition value.  Trivially true for every `MispredOracle`,
    since `mispredict` is a pure function of `(cond, v)`. -/
def PublicDriven (O : MispredOracle) : Prop :=
  ∀ (cond : String) (v : Nat), O.mispredict cond v = O.mispredict cond v

theorem every_oracle_publicDriven (O : MispredOracle) : PublicDriven O :=
  fun _ _ => rfl

/-! ## §5.  The SCT predicate -/

/-- **Speculatively constant-time.**  Under window `window` and oracle `O`,
    two executions of `c` starting from `PublicEquiv`-related states produce
    *equal* speculative leakage traces.  This is the speculative analogue of
    `cmdCT_sound`'s architectural noninterference. -/
def SpeculativelyConstantTime
    (window : SpecWindow) (O : MispredOracle) (lt : LevelTable) (c : LowCT) :
    Prop :=
  ∀ rs1 rs2 : RustState, PublicEquiv lt rs1 rs2 →
    specObs window O rs1 c = specObs window O rs2 c

/-- The architectural analogue, for reference: equal *architectural* traces
    on `PublicEquiv` states. -/
def ArchConstantTime (lt : LevelTable) (c : LowCT) : Prop :=
  ∀ rs1 rs2 : RustState, PublicEquiv lt rs1 rs2 →
    archObs rs1 c = archObs rs2 c

/-! ## §6.  The structural keystone

If `cmdCT c lt leafCT = true` — i.e. *every branch condition and every
runtime memory index in `c` is `Public`* — then the speculative leakage
trace of `c` is a function of the public state alone.  Hence SCT.

The proof is a structural induction on `c`.  At each control-flow / indexed
site, `cmdCT = true` forces the relevant slot `Public`, so `PublicEquiv`
equates the runtime value the observer reads, and the oracle (a pure function
of `(cond, v)`) makes the same decision on both sides; the recursion closes
the subterms.  The non-control, non-indexed constructors leak nothing and
close by `rfl`. -/

/-- **Keystone (speculative form).**  An architecturally-CT program (accepted
    by `cmdCT`) has a speculative leakage trace determined by the public
    state: equal on any two `PublicEquiv` states, *for every window and every
    misprediction oracle*.  The oracle is unconstrained beyond its
    `MispredOracle` shape — because `cmdCT` already forces the branch value it
    reads to be public, the oracle's `(cond, v)`-driven decision is itself
    public-determined (`PublicDriven`, automatic). -/
theorem cmdCT_imp_specObs_eq
    (window : SpecWindow) (O : MispredOracle)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true)
    {rs1 rs2 : RustState} (hEq : PublicEquiv lt rs1 rs2) :
    specObs window O rs1 c = specObs window O rs2 c := by
  induction c generalizing rs1 rs2 with
  | RSkip => rfl
  | RAssert _ => rfl
  | RScalarSet _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RSeq c1 c2 ih1 ih2 =>
    simp only [cmdCT_RSeq, Bool.and_eq_true] at hCT
    simp only [specObs, ih1 hCT.1 hEq, ih2 hCT.2 hEq]
  | RLetZero _ _ body ih =>
    simp only [cmdCT_RLetZero] at hCT
    simpa only [specObs] using ih hCT hEq
  | RLetU64Zero _ body ih =>
    simp only [cmdCT_RLetU64Zero] at hCT
    simpa only [specObs] using ih hCT hEq
  | RBlock body ih =>
    simp only [cmdCT_RBlock] at hCT
    simpa only [specObs] using ih hCT hEq
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [cmdCT_RFnDef, Bool.and_eq_true] at hCT
    simp only [specObs, ihBody hCT.1 hEq, ihCont hCT.2 hEq]
  | RIfNz cond ct cf ihCt ihCf =>
    simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT
    have hcond : lt cond = .Public := level_beq_public_iff.mp hCT.1.1
    have hv : rs1.rsScalar cond = rs2.rsScalar cond := hEq.scalar_eq hcond
    simp only [specObs, hv, ihCt hCT.1.2 hEq, ihCf hCT.2 hEq]
  | RWhileNz cond body ih =>
    simp only [cmdCT_RWhileNz, Bool.and_eq_true] at hCT
    have hcond : lt cond = .Public := level_beq_public_iff.mp hCT.1
    have hv : rs1.rsScalar cond = rs2.rsScalar cond := hEq.scalar_eq hcond
    simp only [specObs, hv, ih hCT.2 hEq]
  | RFor _ _ body ih =>
    simp only [cmdCT_RFor] at hCT
    simpa only [specObs] using ih hCT hEq
  | RArrStore arr idxVar src =>
    simp only [cmdCT_RArrStore, Bool.and_eq_true] at hCT
    have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
    have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar := hEq.scalar_eq hidx
    simp only [specObs, hv]
  | RArrLoad dst src idxVar =>
    simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
    have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
    have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar := hEq.scalar_eq hidx
    simp only [specObs, hv]
  | RCall f dest args =>
    -- BTB/RSB: both new speculative sources read the call's destination slot,
    -- which `cmdCT_RCall` certifies public, so the oracle's decision and the
    -- observed target value agree on both sides.
    simp only [cmdCT_RCall, Bool.and_eq_true] at hCT
    have hdest : lt dest.locVar = .Public := level_beq_public_iff.mp hCT.1.2
    have hv : rs1.rsScalar dest.locVar = rs2.rsScalar dest.locVar :=
      hEq.scalar_eq hdest
    simp only [specObs, hv]
  | _ => rfl

/-- **Keystone (SCT form).**  `architecturally_CT c ∧ public_control_flow c`
    (both captured by `cmdCT c lt leafCT = true`) imply
    `SpeculativelyConstantTime`.  This is the value deliverable of task #564:
    for the straight-line, public-branch, public-index programs our emitted
    CT kernels are (per `cmdCT`), the speculative leakage adds nothing
    secret-dependent. -/
theorem architecturally_CT_imp_SCT
    (window : SpecWindow) (O : MispredOracle)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true) :
    SpeculativelyConstantTime window O lt c :=
  fun _ _ hEq => cmdCT_imp_specObs_eq window O lt leafCT c hCT hEq

/-- And the architectural projection: the same hypothesis gives architectural
    CT.  (Specialises the keystone to the never-mispredict oracle and reads
    off `archObs = specObs neverMispred`; here we prove it directly since
    `archObs` and `specObs neverMispred` share the public-determinacy
    argument.) -/
theorem architecturally_CT_imp_ArchCT
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true) :
    ArchConstantTime lt c := by
  intro rs1 rs2 hEq
  induction c generalizing rs1 rs2 with
  | RSkip => rfl
  | RAssert _ => rfl
  | RScalarSet _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RSeq c1 c2 ih1 ih2 =>
    simp only [cmdCT_RSeq, Bool.and_eq_true] at hCT
    simp only [archObs, ih1 hCT.1 rs1 rs2 hEq, ih2 hCT.2 rs1 rs2 hEq]
  | RLetZero _ _ body ih =>
    simp only [cmdCT_RLetZero] at hCT
    simpa only [archObs] using ih hCT rs1 rs2 hEq
  | RLetU64Zero _ body ih =>
    simp only [cmdCT_RLetU64Zero] at hCT
    simpa only [archObs] using ih hCT rs1 rs2 hEq
  | RBlock body ih =>
    simp only [cmdCT_RBlock] at hCT
    simpa only [archObs] using ih hCT rs1 rs2 hEq
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [cmdCT_RFnDef, Bool.and_eq_true] at hCT
    simp only [archObs, ihBody hCT.1 rs1 rs2 hEq, ihCont hCT.2 rs1 rs2 hEq]
  | RIfNz cond ct cf ihCt ihCf =>
    simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT
    have hcond : lt cond = .Public := level_beq_public_iff.mp hCT.1.1
    have hv : rs1.rsScalar cond = rs2.rsScalar cond := hEq.scalar_eq hcond
    simp only [archObs, hv, ihCt hCT.1.2 rs1 rs2 hEq, ihCf hCT.2 rs1 rs2 hEq]
  | RWhileNz cond body ih =>
    simp only [cmdCT_RWhileNz, Bool.and_eq_true] at hCT
    have hcond : lt cond = .Public := level_beq_public_iff.mp hCT.1
    have hv : rs1.rsScalar cond = rs2.rsScalar cond := hEq.scalar_eq hcond
    simp only [archObs, hv, ih hCT.2 rs1 rs2 hEq]
  | RFor _ _ body ih =>
    simp only [cmdCT_RFor] at hCT
    simpa only [archObs] using ih hCT rs1 rs2 hEq
  | RArrStore arr idxVar src =>
    simp only [cmdCT_RArrStore, Bool.and_eq_true] at hCT
    have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
    have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar := hEq.scalar_eq hidx
    simp only [archObs, hv]
  | RArrLoad dst src idxVar =>
    simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
    have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
    have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar := hEq.scalar_eq hidx
    simp only [archObs, hv]
  | _ => rfl

/-! ## §7.  Pilot: an emitted CT field-op kernel is speculatively CT

We exercise the keystone on a concrete LowCT kernel in the shape our verified
front emits for a Curve25519 base-field computation: a straight-line sequence
of CT leaf calls (`fe25519_*`, all in `LeafCTTable.canonical`) over public
slots, with a *public* loop counter and a *public* branch flag.  No
secret-dependent branch and no secret-dependent index appear — exactly the
fragment `cmdCT` accepts.  The keystone then delivers SCT *for every window
and every misprediction oracle*. -/

namespace Pilot

/-- A public level table: every slot the pilot names is `Public`.  (Field-op
    kernels operate over public projective coordinates / public iteration
    counters; the secret scalar enters only through CT leaf primitives, whose
    CT-ness is delegated to `LeafCTTable.canonical`.) -/
def pilotLevels : LevelTable := fun _ => .Public

/-- An emitted-shape CT field-op kernel: `t1 := fe25519_sqr(x); t2 :=
    fe25519_mul(t1, x); for i in 0..4 { acc := fe25519_mul(acc, t2) }`, all
    over public slots.  Mirrors the inner of `fe25519_invert`'s addition
    chain (a straight-line / bounded-loop CT computation). -/
def pilotKernel : LowCT :=
  .RSeq
    (.RCall "fe25519_sqr" ⟨"t1", .TFp25519⟩ [⟨"x", .TFp25519⟩])
    (.RSeq
      (.RCall "fe25519_mul" ⟨"t2", .TFp25519⟩ [⟨"t1", .TFp25519⟩, ⟨"x", .TFp25519⟩])
      (.RFor "i" 4
        (.RCall "fe25519_mul" ⟨"acc", .TFp25519⟩
          [⟨"acc", .TFp25519⟩, ⟨"t2", .TFp25519⟩])))

/-- The pilot kernel is accepted by the architectural CT analyser `cmdCT`
    (public-control-flow, public indices, all leaves CT).  Discharges by
    `native_decide` through the structural `cmdCT` fold. -/
theorem pilotKernel_cmdCT :
    cmdCT pilotKernel pilotLevels LeafCTTable.canonical = true := by
  native_decide

/-- **Pilot SCT result.**  The emitted CT field-op kernel is speculatively
    constant-time: for *any* speculation window and *any* misprediction
    oracle, two executions whose inputs agree on the public slots produce
    identical speculative leakage traces.  The hypotheses of the keystone
    (`cmdCT pilotKernel pilotLevels LeafCTTable.canonical = true`) discharge
    by `pilotKernel_cmdCT`. -/
theorem pilotKernel_SCT (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTime window O pilotLevels pilotKernel :=
  architecturally_CT_imp_SCT window O pilotLevels LeafCTTable.canonical
    pilotKernel pilotKernel_cmdCT

/-- A pilot kernel exercising a *public* branch flag (`RIfNz` on a public
    slot): the speculative window down the *wrong* arm still leaks only
    public-determined observations.  This is the case that genuinely
    exercises the speculative machinery (a mispredict produces a
    `take window`-truncated wrong-path trace + `rollback`). -/
def pilotKernelBranch : LowCT :=
  .RIfNz "flag"
    (.RCall "fe25519_sqr" ⟨"a", .TFp25519⟩ [⟨"x", .TFp25519⟩])
    (.RCall "fe25519_mul" ⟨"a", .TFp25519⟩ [⟨"x", .TFp25519⟩, ⟨"x", .TFp25519⟩])

theorem pilotKernelBranch_cmdCT :
    cmdCT pilotKernelBranch pilotLevels LeafCTTable.canonical = true := by
  native_decide

/-- **Pilot SCT result (branching kernel).**  Even with a public branch and a
    speculative wrong-path window, the kernel is speculatively CT.  The
    mispredicted-window observations are themselves public-determined,
    because the (public) branch decision drives both the architectural path
    and the oracle. -/
theorem pilotKernelBranch_SCT (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTime window O pilotLevels pilotKernelBranch :=
  architecturally_CT_imp_SCT window O pilotLevels LeafCTTable.canonical
    pilotKernelBranch pilotKernelBranch_cmdCT

end Pilot

/-! ## §7b.  Non-vacuity of the extended observations

The keystone is an *equality* statement, vacuously satisfiable if `specObs`
never emitted the new BTB/RSB/STL observations.  These checks witness that each
new observation genuinely appears in a speculative trace when its oracle source
fires — so the coverage is over a non-trivial observable. -/

namespace Sanity

/-- An oracle that fires *every* speculative source. -/
def allFire : MispredOracle :=
  ⟨fun _ _ => true, fun _ _ => true, fun _ _ => true, fun _ _ => true⟩

/-- A state assigning the target/index slots concrete runtime values. -/
def st : RustState :=
  { rsTower := fun _ => none,
    rsScalar := fun s => if s = "tgt" then 7 else if s = "idx" then 3 else 0 }

/-- **BTB + RSB non-vacuity.**  An indirect call with `injectTarget` and
    `mispredRet` firing emits the `indirectTarget` (BTB) and `retTarget` (RSB)
    observations carrying the (public) target-slot value. -/
theorem btb_rsb_fires :
    specObs 8 allFire st (.RCall "f" ⟨"tgt", .TU64⟩ [])
      = [Obs.indirectTarget "tgt" 7, Obs.rollback,
         Obs.retTarget "tgt" 7, Obs.rollback] := by
  native_decide

/-- **STL non-vacuity.**  A load with `bypassStore` firing emits the
    `stlForward` observation (after the architectural `memIdx`). -/
theorem stl_fires :
    specObs 8 allFire st (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx")
      = [Obs.memIdx "idx" 3, Obs.stlForward "idx" 3, Obs.rollback] := by
  native_decide

end Sanity

/-! ## §8.  What this gets us, and what remains

**Delivered (this file).**
* A speculative leakage semantics over the *owned* `LowCT` instruction
  stream (`specObs`), with a speculation window and a misprediction oracle,
  whose observable is the pc / memory-address pattern (`Obs`).  As of the
  2026-06 extension the observable + oracle cover **all four** Spectre
  transient sources:
  - **PHT (v1)** — `Obs.branch` + the wrong-path window (`mispredict`);
  - **BTB (v2)** — `Obs.indirectTarget` at indirect calls (`injectTarget`);
  - **RSB** — `Obs.retTarget` at the matching return (`mispredRet`);
  - **STL (v4)** — `Obs.stlForward` at a load bypassing a prior store
    (`bypassStore`).
  All three new sources are *transient-only* (oracle-gated; they vanish under
  `neverMispred`) and keyed on the call's destination slot / load's index slot
  — slots `cmdCT` already certifies public.  `Sanity.btb_rsb_fires` /
  `Sanity.stl_fires` witness the new observations are non-vacuous.
* The SCT predicate (`SpeculativelyConstantTime`) as the speculative analogue
  of `cmdCT_sound`'s `PublicEquiv → PublicEquiv` noninterference.
* The structural keystone (`architecturally_CT_imp_SCT`): a program accepted
  by the architectural CT analyser `cmdCT` is speculatively CT *for every
  window and every oracle*, over **all four sources** — the keystone induction
  now closes the BTB/RSB (`RCall`) and STL (`RArrLoad`) clauses from the same
  public-slot certification.  Applied to two concrete emitted-shape CT kernels
  (`Pilot.pilotKernel`, `Pilot.pilotKernelBranch`).

**Variant-coverage matrix** (this file = the *model*; mitigation lives in
`SpeculativeCTFence.lean`):

| Variant | Modelled (`Obs` + oracle source) | Keystone covers (public-driven oracle) | Fence-mitigated vs *unconstrained* oracle |
|---------|----------------------------------|----------------------------------------|-------------------------------------------|
| PHT/v1  | `branch` + wrong-path window     | yes (`cmdCT_imp_specObs_eq`)           | yes — `lfence` at arm/loop head           |
| BTB/v2  | `indirectTarget` / `injectTarget`| yes                                    | yes — retpoline-shape site-guard          |
| RSB     | `retTarget` / `mispredRet`       | yes                                    | yes — RSB-stuffing site-guard             |
| STL/v4  | `stlForward` / `bypassStore`     | yes                                    | yes — SSBD/LFENCE site-guard              |

The "keystone covers" column is the *public-driven* guarantee (the oracle is a
pure function of public slots); the "fence-mitigated" column is the
*unconstrained adversarial* predictor guarantee proved in the fence file.

**What remains (honest residual / model assumptions).**
* **Microarchitectural store-buffer model (STL).**  The STL clause models the
  bypassed store-to-load forward as an oracle-gated read of the load's
  *address slot*.  A finer model would track the *actual bypassed store value*
  through a modelled store buffer; that is a model-assumption gap (the address
  pattern is what the cache leaks, which is what we model — the bypassed
  datum's value leakage is delegated to leaf-CT, as for ordinary loads).
* **Indirect-target / return-slot abstraction (BTB/RSB).**  `LowCT` has no
  dedicated indirect-jump / `ret` constructor; we attach the BTB/RSB sources
  to the call's destination slot (the target/return register of the frame).
  A dedicated indirect-control constructor would let the model distinguish an
  indirect from a direct call syntactically.  Until then the coverage is sound
  (any call site is treated as potentially indirect) but conservative.
* **Wiring through `RustExec`.**  The observer is structural; a finer model
  would thread `specObs` through the relational big-step `RustExec`.  For the
  straight-line / public-branch fragment the two coincide. -/

end CatCrypt.Crypto.SecureCompilation.SpeculativeCT
