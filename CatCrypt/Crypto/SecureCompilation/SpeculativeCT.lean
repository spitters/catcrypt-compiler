/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Speculative constant-time for the owned `LowCT` instruction stream

A leakage observer over `LowCT` extending the architectural branch-and-index
trace with a speculation window and a misprediction oracle, the constant-time
predicate over that observer, and its consequence for programs the
architectural analyser `cmdCT` accepts.

## What the observer emits

`archObs rs c` is the architectural leakage of `c` from `rs`: the branch
decisions taken and the runtime memory indices accessed, in order.  `specObs
window O rs c` extends it with the oracle `O` and the window bound.

* **Conditional-branch misprediction (PHT).**  `RIfNz` and `RWhileNz`
  contribute, when `O.mispredict` fires, the *other* arm's observations
  truncated to `window` and capped by `Obs.rollback`, followed by the
  architecturally taken arm's observations.  The transient contribution is the
  wrong path's own trace, so this clause separates a mispredicted run from a
  correctly predicted one.
* **Store bypass (STL).**  The `RArrLoad` clause emits, when `O.bypassStore`
  fires, `Obs.stlForward src.locVar (rsTowerLimb rs src.locVar i)` — the word
  the load is forwarded out of the source slot, read at the load's runtime
  index `i`.  Because the observer reads against the entry state, that word is
  the contents the slot held before any store the command itself performs, so
  it is the value a load bypassing every pending store receives.  It is a
  memory read, not the index the architectural `Obs.memIdx` at the same site
  carries.
* **Indirect-branch and return misprediction (BTB, RSB).**  The `RCall` clause
  emits `Obs.indirectTarget dest.locVar (rsTowerLimb rs dest.locVar 0)` and
  `Obs.retTarget dest.locVar (rsTowerLimb rs dest.locVar 1)`: the predicted
  callee pointer and the predicted return address, read as the first two words
  of the call's destination slot.  `archObs` emits nothing at a call.

A store-to-load forward that carries the value a *particular* buffered store
overwrote, and that enters the state and from there later addresses, is
expressible over `SpeculativeCTStoreBuffer.specRun`, whose state carries a
store buffer of overwritten slot values.
`SpeculativeCTStoreBuffer.cmdCT_not_imp_SCT` exhibits a `cmdCT`-accepted
command that leaks under that model.

## Scope

* The observable is the branch-decision, memory-address and transiently
  forwarded-word pattern.  Data values inside leaves are delegated to the
  leaf-CT table, as in `cmdCT_sound`.
* The observer is structural over `LowCT` and reads every condition, index and
  memory word against the entry state; it is not threaded through the
  relational `RustExec` big-step.  A load therefore sees the slot contents the
  command started with, and a second store to a slot the command already wrote
  is invisible to it.
* `LowCT` has no indirect-jump and no return constructor, so the indirect
  target and the return address are modelled as the first two words of the
  call's destination slot.
* `architecturally_CT_imp_SCT` states that a `cmdCT`-accepted program has equal
  `specObs` traces on `PublicEquiv` states.  It rests on `cmdCT` classifying
  the source, destination and index slots `Public`: `Separation.loadSecretArr`
  and `Separation.callSecretDest` are architecturally constant-time commands
  whose `specObs` traces separate two `PublicEquiv` states, and both are
  rejected by `cmdCT`.

## References

* Cauligi, Disselkoen, von Gleissenthall, Tullsen, Stefan, Rezk, Barthe,
  "Constant-Time Foundations for the New Spectre Era", PLDI 2020.
* Barthe et al., "System-Level Non-Interference for Constant-Time
  Cryptography", CCS 2014 (the architectural baseline `cmdCT` extends).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.SpeculativeCT

open CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-! ## §1.  Leakage observations

The attacker observes the *pc / memory-address pattern*: at every branch the
condition value (which way control went), and at every runtime-indexed memory
access the index value.  Pure data-flow (leaf arithmetic) is not address
leakage and is delegated to the leaf-CT table, exactly as in `cmdCT_sound`. -/

/-- A single leakage observation.

    `branch`, `memIdx` and `rollback` are the architectural and
    branch-misprediction observable: branch decisions, runtime memory indices,
    and the rollback marker that caps a mis-speculated window.

    `indirectTarget`, `retTarget` and `stlForward` are the transient
    observations of the three remaining speculation sites.  Each carries a
    memory word: the predicted callee pointer, the predicted return address,
    and the word a bypassing load is forwarded. -/
inductive Obs where
  /-- A branch on scalar slot `cond` was reached with runtime value `v`. -/
  | branch (cond : String) (v : Nat) : Obs
  /-- A runtime-indexed memory access on index slot `idxVar` with value `v`. -/
  | memIdx (idxVar : String) (v : Nat) : Obs
  /-- A speculation rollback marker (a mis-speculated window ended). -/
  | rollback : Obs
  /-- Indirect-branch site: the predicted callee pointer `v`, read from slot
      `tgt`. -/
  | indirectTarget (tgt : String) (v : Nat) : Obs
  /-- Return site: the predicted return address `v`, read from slot `ret`. -/
  | retTarget (ret : String) (v : Nat) : Obs
  /-- Store bypass: the word `v` a bypassing load is forwarded out of the
      source slot `addr`. -/
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

/-- A misprediction oracle: four independent decisions, each a pure function of
    a slot name and a runtime value.

    * `mispredict` — mispredict the conditional branch `cond` at value `v`?
    * `injectTarget` — mispredict the indirect target at the call whose
      destination slot is `tgt` (value `v`)?
    * `mispredRet` — mispredict the return address at the call whose
      destination slot is `ret` (value `v`)?
    * `bypassStore` — bypass the pending stores at the load whose index slot is
      `addr` (value `v`)?

    Every field ranges over a slot name and its runtime value only, so once
    `cmdCT` certifies that slot `Public`, the decision agrees on any two
    `PublicEquiv` states — this is `PublicDriven`.  A predictor that reads the
    whole speculative state, including a store buffer, is
    `SpeculativeCTStoreBuffer.SpecOracle`, and `PublicDrivenSB` is a restriction
    on it that `SpeculativeCTStoreBuffer.peekOracle` fails. -/
structure MispredOracle where
  /-- Mispredict at branch `cond` whose runtime value is `v`? -/
  mispredict : (cond : String) → (v : Nat) → Bool
  /-- Mispredict the indirect target at the call whose destination slot is
      `tgt` (runtime value `v`)? -/
  injectTarget : (tgt : String) → (v : Nat) → Bool
  /-- Mispredict the return address at the call whose destination slot is `ret`
      (runtime value `v`)? -/
  mispredRet : (ret : String) → (v : Nat) → Bool
  /-- Bypass the pending stores at the load whose index slot is `addr` (runtime
      value `v`)? -/
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
  | .RArrLoad _ src idxVar  =>
      -- The architectural index observation, then — when `O.bypassStore`
      -- fires — the word the load is forwarded out of the source slot at that
      -- index.  The observer reads against the entry state, so the word is the
      -- contents the slot held before any store the command performs.
      let i := rs.rsScalar idxVar
      let stl : ObsTrace :=
        if O.bypassStore idxVar i then
          [Obs.stlForward src.locVar (rsTowerLimb rs src.locVar i), Obs.rollback]
        else []
      Obs.memIdx idxVar i :: stl
  | .RCall _ dest _         =>
      -- The predicted callee pointer and the predicted return address, gated by
      -- `O.injectTarget` and `O.mispredRet`.  `LowCT` has no indirect-jump and
      -- no return constructor, so the two are read as the first two words of
      -- the call's destination slot.
      let tslot := dest.locVar
      let tv := rs.rsScalar tslot
      let btb : ObsTrace :=
        if O.injectTarget tslot tv then
          [Obs.indirectTarget tslot (rsTowerLimb rs tslot 0), Obs.rollback]
        else []
      let rsb : ObsTrace :=
        if O.mispredRet tslot tv then
          [Obs.retTarget tslot (rsTowerLimb rs tslot 1), Obs.rollback]
        else []
      btb ++ rsb
  | _                       => []

/-- The architectural projection: with the never-mispredict oracle, the
    speculative observer collapses to the architectural one. -/
def neverMispred : MispredOracle :=
  ⟨fun _ _ => false, fun _ _ => false, fun _ _ => false, fun _ _ => false⟩

/-! ## §4.  Public-drivenness of the oracle

Whether a transient window opens is itself an observation, so leakage equality
across two states needs the oracle to take the same decision on both.
`PublicDriven` is that property.  Every `MispredOracle` has it, because each
field is a function of a slot name and a runtime value and `PublicEquiv` equates
the runtime value of a `Public` slot.  A predictor that reads the whole
speculative state does not: `SpeculativeCTStoreBuffer.PublicDrivenSB` is the
same property for such a predictor and `SpeculativeCTStoreBuffer.peekOracle`
fails it. -/

/-- **Public-driven oracle.**  On any two `PublicEquiv` states the oracle takes
    the same branch-misprediction and store-bypass decision at every `Public`
    slot. -/
def PublicDriven (lt : LevelTable) (O : MispredOracle) : Prop :=
  ∀ rs1 rs2 : RustState, PublicEquiv lt rs1 rs2 →
    (∀ cond, lt cond = .Public →
        O.mispredict cond (rs1.rsScalar cond) = O.mispredict cond (rs2.rsScalar cond)) ∧
      (∀ addr, lt addr = .Public →
        O.bypassStore addr (rs1.rsScalar addr) = O.bypassStore addr (rs2.rsScalar addr))

/-- Every `MispredOracle` is public-driven: each field reads a slot name and a
    runtime value, and `PublicEquiv` equates the runtime value of a `Public`
    slot. -/
theorem every_oracle_publicDriven (lt : LevelTable) (O : MispredOracle) :
    PublicDriven lt O :=
  fun _ _ hEq =>
    ⟨fun _ hc => by rw [hEq.scalar_eq hc], fun _ ha => by rw [hEq.scalar_eq ha]⟩

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

/-! ## §6.  `cmdCT` acceptance and the `specObs` trace

If `cmdCT c lt leafCT = true` — every branch condition and every runtime
memory index in `c` is `Public` — then the `specObs` trace of `c` is equal on
any two `PublicEquiv` states.

The proof is a structural induction on `c`.  At each control-flow and indexed
site, `cmdCT = true` forces the relevant slot `Public`, so `PublicEquiv`
equates the runtime value the observer reads, and the oracle, a function of
that slot and value, makes the same decision on both sides; the recursion
closes the subterms.  The remaining constructors emit nothing and close by
`rfl`. -/

/-- The `specObs` trace of a `cmdCT`-accepted program is equal on any two
    `PublicEquiv` states, for every window and every misprediction oracle.  The
    oracle is unconstrained beyond its `MispredOracle` shape: each field is a
    function of a slot name and a runtime value, and `cmdCT` forces the slots
    the observer reads to be `Public`. -/
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
    -- The index slot and the source slot are both `Public`, so the index the
    -- gate reads and the forwarded word both agree.
    simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
    have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
    have hsrc : lt src.locVar = .Public := level_beq_public_iff.mp hCT.2
    have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar := hEq.scalar_eq hidx
    have hT : rs1.rsTower src.locVar = rs2.rsTower src.locVar := hEq.tower_eq hsrc
    simp only [specObs, hv, rsTowerLimb, hT]
  | RCall f dest args =>
    -- Both call-site markers read the call's destination slot, which
    -- `cmdCT_RCall` classifies `Public`, so the oracle's decision and the two
    -- predicted target words agree on both sides.
    simp only [cmdCT_RCall, Bool.and_eq_true] at hCT
    have hdest : lt dest.locVar = .Public := level_beq_public_iff.mp hCT.1.2
    have hv : rs1.rsScalar dest.locVar = rs2.rsScalar dest.locVar :=
      hEq.scalar_eq hdest
    have hT : rs1.rsTower dest.locVar = rs2.rsTower dest.locVar := hEq.tower_eq hdest
    simp only [specObs, hv, rsTowerLimb, hT]
  | _ => rfl

/-- `cmdCT c lt leafCT = true` implies `SpeculativelyConstantTime` over
    `specObs`, for every window and every misprediction oracle.

    The oracle needs no side condition because every `MispredOracle` is
    `PublicDriven`.  The three transient clauses need `cmdCT`'s classification
    of the source and destination slots: `Separation.loadSecretArr` and
    `Separation.callSecretDest` are architecturally constant-time and not
    speculatively constant-time, and `cmdCT` rejects both.

    `specObs` reads memory against the entry state.  A store-to-load forward
    carrying the value a particular buffered store overwrote is expressible over
    `SpeculativeCTStoreBuffer.specRun`, where the analogous statement needs the
    two further hypotheses of
    `SpeculativeCTStoreBuffer.cmdCT_cmov_publicDriven_imp_SCT_SB`. -/
theorem architecturally_CT_imp_SCT
    (window : SpecWindow) (O : MispredOracle)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true) :
    SpeculativelyConstantTime window O lt c :=
  fun _ _ hEq => cmdCT_imp_specObs_eq window O lt leafCT c hCT hEq

/-- The same hypothesis gives architectural CT over `archObs`.  Proved
    directly, by the same public-determinacy induction.

    `archObs` reads every condition and index against the entry state, so it
    does not see a write the command itself performs.  The state-threading
    committed run is `SpeculativeCTStoreBuffer.archRun`, and
    `SpeculativeCTStoreBuffer.cmdCT_not_imp_ArchCT` exhibits a `cmdCT`-accepted
    command whose `archRun` trace separates two `PublicEquiv` states. -/
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

`architecturally_CT_imp_SCT` applied to a concrete `LowCT` kernel in the shape
the front emits for a Curve25519 base-field computation: a straight-line
sequence of CT leaf calls (`fe25519_*`, all in `LeafCTTable.canonical`) over
public slots, with a public loop counter and a public branch flag.  No
secret-dependent branch and no secret-dependent index appear, which is the
fragment `cmdCT` accepts. -/

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

/-- The emitted CT field-op kernel has equal `specObs` traces on states that
    agree on the public slots, for every speculation window and every
    misprediction oracle. -/
theorem pilotKernel_SCT (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTime window O pilotLevels pilotKernel :=
  architecturally_CT_imp_SCT window O pilotLevels LeafCTTable.canonical
    pilotKernel pilotKernel_cmdCT

/-- A pilot kernel with a public branch flag (`RIfNz` on a public slot).  This
    is the case that exercises the branch-misprediction clause: a mispredict
    produces the other arm's trace truncated to the window, then
    `Obs.rollback`. -/
def pilotKernelBranch : LowCT :=
  .RIfNz "flag"
    (.RCall "fe25519_sqr" ⟨"a", .TFp25519⟩ [⟨"x", .TFp25519⟩])
    (.RCall "fe25519_mul" ⟨"a", .TFp25519⟩ [⟨"x", .TFp25519⟩, ⟨"x", .TFp25519⟩])

theorem pilotKernelBranch_cmdCT :
    cmdCT pilotKernelBranch pilotLevels LeafCTTable.canonical = true := by
  native_decide

/-- The branching kernel has equal `specObs` traces on states that agree on the
    public slots.  The mispredicted-window observations are the other arm's,
    read from a public branch decision at public slots. -/
theorem pilotKernelBranch_SCT (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTime window O pilotLevels pilotKernelBranch :=
  architecturally_CT_imp_SCT window O pilotLevels LeafCTTable.canonical
    pilotKernelBranch pilotKernelBranch_cmdCT

end Pilot

/-! ## §7b.  The transient observations appear in a trace

`cmdCT_imp_specObs_eq` is an equality statement, so it holds whenever the
observations it compares are absent.  These checks compute the traces in which
each transient observation appears, so the equality is over a trace that
contains them.  Each carries a memory word read from the named slot. -/

namespace Sanity

/-- An oracle whose four decisions all fire. -/
def allFire : MispredOracle :=
  ⟨fun _ _ => true, fun _ _ => true, fun _ _ => true, fun _ _ => true⟩

/-- A one-byte value. -/
def byteVal (n : Nat) : RustVal .TU8 := fun _ => BitVec.ofNat 8 n

/-- A state assigning the target/index slots concrete runtime values. -/
def st : RustState :=
  { rsTower := fun _ => none,
    rsScalar := fun s => if s = "tgt" then 7 else if s = "idx" then 3 else 0 }

/-- A call with `injectTarget` and `mispredRet` firing emits the predicted
    callee pointer and the predicted return address, read as the first two words
    of the call's destination slot.  The slot is absent from `st`'s heap, so both
    words are `0`. -/
theorem btb_rsb_fires :
    specObs 8 allFire st (.RCall "f" ⟨"tgt", .TU64⟩ [])
      = [Obs.indirectTarget "tgt" 0, Obs.rollback,
         Obs.retTarget "tgt" 0, Obs.rollback] := by
  decide

/-- A load with `bypassStore` firing emits, after the architectural `memIdx`,
    the word the load is forwarded out of the source slot.  The slot is absent
    from `st`'s heap, so that word is `0`. -/
theorem stl_fires :
    specObs 8 allFire st (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx")
      = [Obs.memIdx "idx" 3, Obs.stlForward "a" 0, Obs.rollback] := by
  decide

/-- A state holding a one-byte value in the call's destination slot and in the
    array slot. -/
def stMem : RustState :=
  { rsTower := fun x =>
      if x = "tgt" then some ⟨.TU8, byteVal 5⟩
      else if x = "a" then some ⟨.TU8, byteVal 9⟩
      else none,
    rsScalar := fun s => if s = "tgt" then 7 else 0 }

/-- On a state whose heap holds the destination slot, the two call-site
    observations carry that slot's first two words. -/
theorem btb_rsb_carries_word :
    specObs 8 allFire stMem (.RCall "f" ⟨"tgt", .TU64⟩ [])
      = [Obs.indirectTarget "tgt" 5, Obs.rollback,
         Obs.retTarget "tgt" 0, Obs.rollback] := by
  decide

/-- On a state whose heap holds the source slot, the store-bypass observation
    carries the word at the load's runtime index. -/
theorem stl_carries_word :
    specObs 8 allFire stMem (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx")
      = [Obs.memIdx "idx" 0, Obs.stlForward "a" 9, Obs.rollback] := by
  decide

end Sanity

/-! ## §7c.  The transient observations separate states the architectural
observer does not

`archObs` emits only branch decisions and runtime indices.  The three transient
clauses read memory words, so a command whose `archObs` trace is constant can
have a `specObs` trace that is not.  Both commands below are rejected by
`cmdCT`, which is the hypothesis `architecturally_CT_imp_SCT` carries. -/

namespace Separation

open Sanity (allFire byteVal)

/-- Every slot is `Public` except the array slot `sarr`. -/
def secretLevels : LevelTable := fun x => if x = "sarr" then .Secret else .Public

/-- A state whose secret array slot holds the one-byte value `n`. -/
def sarrState (n : Nat) : RustState where
  rsTower := fun x => if x = "sarr" then some ⟨.TU8, byteVal n⟩ else none
  rsScalar := fun _ => 0

/-- The states differ only on the secret array slot. -/
theorem sarrState_publicEquiv (a b : Nat) :
    PublicEquiv secretLevels (sarrState a) (sarrState b) := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro x hx
  have hne : x ≠ "sarr" := by
    intro he; rw [he] at hx; simp [secretLevels] at hx
  simp [sarrState, hne]

/-- A load from the secret array slot at a public index. -/
def loadSecretArr : LowCT := .RArrLoad ⟨"d", .TU8⟩ ⟨"sarr", .TU8⟩ "i"

theorem loadSecretArr_not_cmdCT :
    cmdCT loadSecretArr secretLevels LeafCTTable.canonical = false := by decide

/-- The load is architecturally constant-time: `archObs` emits the runtime
    index, which is read from a `Public` slot. -/
theorem loadSecretArr_ArchCT : ArchConstantTime secretLevels loadSecretArr := by
  intro rs1 rs2 hEq
  have hi : rs1.rsScalar "i" = rs2.rsScalar "i" := hEq.scalar_eq (by simp [secretLevels])
  simp only [loadSecretArr, archObs, hi]

/-- **The store-bypass observation separates two states the architectural
    observer does not.**  The forwarded word is the secret array slot's
    contents. -/
theorem loadSecretArr_not_SCT :
    ¬ SpeculativelyConstantTime 8 allFire secretLevels loadSecretArr := by
  intro h
  have := h (sarrState 0) (sarrState 1) (sarrState_publicEquiv 0 1)
  revert this
  decide

/-- A call whose destination is the secret array slot. -/
def callSecretDest : LowCT := .RCall "fe25519_mul" ⟨"sarr", .TU8⟩ []

theorem callSecretDest_not_cmdCT :
    cmdCT callSecretDest secretLevels LeafCTTable.canonical = false := by decide

/-- The call is architecturally constant-time: `archObs` emits nothing at a
    call. -/
theorem callSecretDest_ArchCT : ArchConstantTime secretLevels callSecretDest :=
  fun _ _ _ => rfl

/-- **The indirect-target observation separates two states the architectural
    observer does not.**  The predicted callee pointer is the destination
    slot's first word. -/
theorem callSecretDest_not_SCT :
    ¬ SpeculativelyConstantTime 8 allFire secretLevels callSecretDest := by
  intro h
  have := h (sarrState 0) (sarrState 1) (sarrState_publicEquiv 0 1)
  revert this
  decide

/-- Architectural constant-time does not imply speculative constant-time, and
    `cmdCT` rejects both witnesses. -/
theorem archCT_not_imp_SCT :
    (ArchConstantTime secretLevels loadSecretArr ∧
        ¬ SpeculativelyConstantTime 8 allFire secretLevels loadSecretArr ∧
          cmdCT loadSecretArr secretLevels LeafCTTable.canonical = false) ∧
      (ArchConstantTime secretLevels callSecretDest ∧
        ¬ SpeculativelyConstantTime 8 allFire secretLevels callSecretDest ∧
          cmdCT callSecretDest secretLevels LeafCTTable.canonical = false) :=
  ⟨⟨loadSecretArr_ArchCT, loadSecretArr_not_SCT, loadSecretArr_not_cmdCT⟩,
   ⟨callSecretDest_ArchCT, callSecretDest_not_SCT, callSecretDest_not_cmdCT⟩⟩

end Separation

/-! ## §8.  What the model expresses

**In this file.**
* `specObs`, a leakage observer over `LowCT` with a speculation window and a
  misprediction oracle, whose observable is the branch-decision and
  memory-address pattern (`Obs`).
* `SpeculativelyConstantTime`, equality of `specObs` traces on `PublicEquiv`
  states, and `ArchConstantTime`, the same over `archObs`.
* `cmdCT_imp_specObs_eq` and `architecturally_CT_imp_SCT`: a `cmdCT`-accepted
  program has equal `specObs` traces, for every window and every oracle.
  Applied to `Pilot.pilotKernel` and `Pilot.pilotKernelBranch`.

* `Separation.archCT_not_imp_SCT`: two architecturally constant-time commands
  whose `specObs` traces separate two `PublicEquiv` states, both rejected by
  `cmdCT`.

**What each observation carries.**

| Clause | Transient contribution | What it reads |
|--------|------------------------|---------------|
| `RIfNz`, `RWhileNz` | the other arm's trace, truncated to the window, then `Obs.rollback` | the wrong path's own trace |
| `RArrLoad`, `Obs.stlForward` | the word the load is forwarded out of the source slot at the runtime index | `rs.rsTower src.locVar`, a memory read |
| `RCall`, `Obs.indirectTarget` | the predicted callee pointer | word `0` of `rs.rsTower dest.locVar` |
| `RCall`, `Obs.retTarget` | the predicted return address | word `1` of `rs.rsTower dest.locVar` |

**Where a per-store bypass is expressed.**
`SpeculativeCTStoreBuffer` threads a `SpecState` carrying a store buffer of
overwritten slot values through a run function, forwards the value a *particular*
buffered store overwrote to a bypassing load, and lets that value reach later
addresses.  `SpeculativeCTStoreBuffer.cmdCT_not_imp_SCT` is a `cmdCT`-accepted
command whose store-buffer trace separates two `PublicEquiv` states under a
public-determined predictor, and
`SpeculativeCTStoreBuffer.cmdCT_cmov_publicDriven_imp_SCT_SB` is the statement
that survives there.  `SpeculativeCTStoreBuffer.cmdCT_not_imp_ArchCT` is a
`cmdCT`-accepted command whose state-threading committed trace already separates
them.

**Model assumptions.**
* Indirect control has no `LowCT` constructor, so the predicted callee pointer
  and the predicted return address are the first two words of the call's
  destination slot.  A dedicated indirect-control node would let the model read
  a target register.
* The observer is structural and reads against the entry state, so a load sees
  the memory the command started with; a load bypassing one of several pending
  stores to the same slot is expressed over `SpeculativeCTStoreBuffer.specRun`.
* The observer is not threaded through the relational big-step `RustExec`. -/

end CatCrypt.Crypto.SecureCompilation.SpeculativeCT
