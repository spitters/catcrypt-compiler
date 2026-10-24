/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SpeculativeCT

/-!
# A store-buffer model of Spectre-v4 for the `LowCT` instruction stream

`SpeculativeCT.specObs` observes a `LowCT` command against a fixed `RustState`,
so at a load it reads the memory the command started with. This module threads
the state: a run function whose state carries a store buffer of overwritten
tower-slot values, and whose loads may be forwarded the value a particular
buffered store overwrote instead of the committed one. The forwarded value is
both emitted as `Obs.stlForward` and written into the state, so it also reaches
later addresses.

## The model

`SpecState` carries a `RustState`, a `StoreBuf` recording for each write the
value the written slot held before it, and a speculation window bounding how
many transient forwards may occur. `SpecOracle` is a pair of predictors, each an
arbitrary function of the whole speculative state, so a predictor may read
secret slots. `specRun` threads that state through a command and returns the
final state together with the leakage trace: the branch decisions, runtime
memory indices, transient forwards and rollback markers an attacker reads.

A store (`RArrStore`, `RArrStoreLit`, `RLimbStore`, `RLimbStoreExpr`) pushes the
overwritten slot value onto the buffer. A load (`RArrLoad`) either reads the
committed array, or — when the window is open, the oracle fires, and the buffer
holds an overwritten value for the loaded slot — is forwarded the element of
that stale value, emits it as `Obs.stlForward`, and consumes one unit of window.
A mispredicted branch contributes the wrong arm's trace, truncated to the window
and capped by a rollback marker, and its state is discarded.

`archRun` is the same semantics with no buffer, no window and no oracle.
`specRun_neverSpeculate` and `specRun_of_window_zero` are the projections onto
it.

`cmdCT_not_imp_SCT` is a `cmdCT`-accepted command that leaks here, and
`cmdCT_cmov_publicDriven_imp_SCT_SB` is the constant-time statement that holds:
`cmdCT`, a `PublicDrivenSB` predictor and `SelectAgrees` — agreeing sources at
every conditional move — give equal traces for every window.
`StlGadget.sct_SB_hypotheses_sharp` refutes each of the two added hypotheses on a
command satisfying the other.

## Scope

Modelled: the memory-address channel at `(index slot, runtime index value)`
granularity, over the constructors that read or write state — `RScalarSet`,
`RScalarSetExpr`, `RSelect`, `RCall`, `RLimbStore`, `RLimbStoreExpr`,
`RArrStore`, `RArrStoreLit`, `RArrLoad`, `RArrLoadLit`, `RCopy` — and the
control-flow constructors. Store-to-load forwarding is at whole-slot granularity:
a buffer entry records the value a slot held before an element store
(`RLimbStore`, `RLimbStoreExpr`, `RArrStore`, `RArrStoreLit`), and a bypassing
element load reads its element out of that stale slot value. The whole-slot
writes `RSelect`, `RCall` and `RCopy` update the committed state without a
buffer entry, and the whole-slot read of `RCopy` is not forwarded.

Not modelled: the remaining `LowCT` constructors, which are state-preserving and
leak nothing here; loop unrolling — `RWhileNz` and `RFor` run their body once,
as `SpeculativeCT.archObs` does; indirect-branch and return misprediction
(Spectre-BTB, Spectre-RSB), which `SpeculativeCT.specObs` reads off a call's
destination slot; cache-line granularity and timing.

`RScalarSetExpr` is interpreted with the tower-aware `SExpr.evalState`, so an
`SLimb` node reads the tower heap, as in `RustExec.scalarSetExpr`.

## References

* Cauligi, Disselkoen, von Gleissenthall, Tullsen, Stefan, Rezk, Barthe,
  "Constant-Time Foundations for the New Spectre Era", PLDI 2020.
* Vassena, Disselkoen, von Gleissenthall, Cauligi, Kıcı, Jhala, Tullsen, Stefan,
  "Automatically Eliminating Speculative Leaks with Blade", POPL 2021.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SpeculativeCTStoreBuffer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.SpeculativeCT

/-! ## 1. The store buffer and the speculative state -/

/-- A tower value together with its type tag, as the tower heap stores it. -/
abbrev TowerVal := Σ t : TowerType, RustVal t

/-- A store buffer, newest entry first. An entry `(x, v)` records that a write to
    tower slot `x` overwrote the slot contents `v`; `v` is what a load that
    bypasses that write is forwarded. -/
abbrev StoreBuf := List (String × Option TowerVal)

/-- The contents the newest buffered write to slot `x` overwrote, if the buffer
    holds an entry for `x`. -/
def sbLookup : StoreBuf → String → Option (Option TowerVal)
  | [], _ => none
  | (y, v) :: rest, x => if y = x then some v else sbLookup rest x

@[simp] theorem sbLookup_nil (x : String) : sbLookup [] x = none := rfl

/-- The speculative state: the `RustState` the committed semantics works on, the
    buffer of overwritten slot values, and the number of transient forwards the
    speculation window still permits. -/
structure SpecState where
  /-- The committed runtime state. -/
  rs : RustState
  /-- The overwritten slot values a bypassing load may be forwarded. -/
  buf : StoreBuf := []
  /-- The number of transient events still permitted. -/
  window : Nat := 0

/-- The two predictors. Each is an arbitrary function of the whole speculative
    state, of a slot name and of a runtime value, so a predictor may read secret
    slots.

    * `bypassStore x i` — at a load of element `i` of slot `x`, does the load
      bypass the pending write to `x` and take the buffered value?
    * `mispredict cond v` — at a branch on slot `cond` with runtime value `v`,
      does the processor speculate down the other arm? -/
structure SpecOracle where
  /-- Bypass the pending write to slot `x` at a load of element `i`? -/
  bypassStore : SpecState → String → Nat → Bool
  /-- Speculate down the other arm at a branch on `cond` with value `v`? -/
  mispredict : SpecState → String → Nat → Bool

/-- The predictor that neither bypasses nor mispredicts. -/
def neverSpeculate : SpecOracle := ⟨fun _ _ _ => false, fun _ _ _ => false⟩

/-- The predictor that bypasses every store and never mispredicts a branch. -/
def alwaysBypass : SpecOracle := ⟨fun _ _ _ => true, fun _ _ _ => false⟩

/-- The value a load of element `i` of slot `x` is forwarded by a bypass: the
    buffered contents of `x`, when the window is open, the oracle fires, and the
    buffer holds contents for `x`. -/
def bypasses (O : SpecOracle) (σ : SpecState) (x : String) (i : Nat) :
    Option TowerVal :=
  if 0 < σ.window ∧ O.bypassStore σ x i = true then
    match sbLookup σ.buf x with
    | some (some v) => some v
    | _ => none
  else none

@[simp] theorem neverSpeculate_mispredict (σ : SpecState) (cond : String) (v : Nat) :
    neverSpeculate.mispredict σ cond v = false := rfl

@[simp] theorem neverSpeculate_bypassStore (σ : SpecState) (x : String) (i : Nat) :
    neverSpeculate.bypassStore σ x i = false := rfl

@[simp] theorem bypasses_neverSpeculate (σ : SpecState) (x : String) (i : Nat) :
    bypasses neverSpeculate σ x i = none := by
  simp [bypasses, neverSpeculate]

@[simp] theorem bypasses_of_window_zero (O : SpecOracle) (σ : SpecState)
    (h : σ.window = 0) (x : String) (i : Nat) : bypasses O σ x i = none := by
  simp [bypasses, h]

/-! ## 2. The speculative run -/

/-- `specRun leafSpec O σ c` runs `c` from the speculative state `σ` under the
    predictors `O`, returning the final state and the leakage trace.

    A store pushes the overwritten slot contents onto the buffer. A runtime-index
    load emits its index observation and then either takes the committed array
    element or, when `bypasses` supplies a stale slot value, takes that value's
    element, emits `Obs.stlForward` carrying the forwarded word together with
    `Obs.rollback`, and consumes one unit of window. A branch emits its decision;
    when the oracle mispredicts and the window is open it also emits the other
    arm's trace truncated to the window, capped by `Obs.rollback`, and the
    mis-speculated state is discarded. -/
def specRun (leafSpec : LeafSpec) (O : SpecOracle) (σ : SpecState) :
    LowCT → SpecState × ObsTrace
  | .RSkip => (σ, [])
  | .RAssert _ => (σ, [])
  | .RScalarSet x n => ({ σ with rs := rsSetScalar σ.rs x n }, [])
  | .RScalarSetExpr x e =>
      ({ σ with rs := rsSetScalar σ.rs x (e.evalState σ.rs) }, [])
  | .RSeq c1 c2 =>
      let r1 := specRun leafSpec O σ c1
      let r2 := specRun leafSpec O r1.1 c2
      (r2.1, r1.2 ++ r2.2)
  | .RLetZero _ _ body => specRun leafSpec O σ body
  | .RLetU64Zero _ body => specRun leafSpec O σ body
  | .RBlock body => specRun leafSpec O σ body
  | .RFnDef _ _ _ body cont =>
      let r1 := specRun leafSpec O σ body
      let r2 := specRun leafSpec O r1.1 cont
      (r2.1, r1.2 ++ r2.2)
  | .RIfNz cond ct cf =>
      let v := σ.rs.rsScalar cond
      let rt := specRun leafSpec O σ ct
      let rf := specRun leafSpec O σ cf
      let mis : ObsTrace :=
        if 0 < σ.window ∧ O.mispredict σ cond v = true then
          (if v ≠ 0 then rf.2 else rt.2).take σ.window ++ [Obs.rollback]
        else []
      ((if v ≠ 0 then rt.1 else rf.1),
        Obs.branch cond v :: (mis ++ (if v ≠ 0 then rt.2 else rf.2)))
  | .RWhileNz cond body =>
      let v := σ.rs.rsScalar cond
      let rb := specRun leafSpec O σ body
      let mis : ObsTrace :=
        if 0 < σ.window ∧ O.mispredict σ cond v = true then
          rb.2.take σ.window ++ [Obs.rollback]
        else []
      (rb.1, Obs.branch cond v :: (mis ++ rb.2))
  | .RFor _ _ body => specRun leafSpec O σ body
  | .RSelect dst sel src0 src1 =>
      let s := if σ.rs.rsScalar sel = 0 then src0 else src1
      match locatedLookup σ.rs s with
      | some v =>
          if h : s.locDst = dst.locDst then
            ({ σ with rs := locatedUpdate σ.rs dst (h ▸ v) }, [])
          else (σ, [])
      | none => (σ, [])
  | .RCall f dest args =>
      match locatedLookup σ.rs dest with
      | some oldV =>
          let newV :=
            leafSpec.call f dest.locDst (args.map (fun a => a.locDst)) oldV
              (args.filterMap (fun a => σ.rs.rsTower a.locVar))
          ({ σ with rs := locatedUpdate σ.rs dest newV }, [])
      | none => (σ, [])
  | .RLimbStore loc i v =>
      match locatedLookup σ.rs loc with
      | some oldV =>
          ({ rs := locatedUpdate σ.rs loc (leafSpec.limbStore loc oldV i v)
             buf := (loc.locVar, σ.rs.rsTower loc.locVar) :: σ.buf
             window := σ.window }, [])
      | none => (σ, [])
  | .RLimbStoreExpr loc i e =>
      match locatedLookup σ.rs loc with
      | some oldV =>
          ({ rs := locatedUpdate σ.rs loc
               (leafSpec.limbStore loc oldV i (BitVec.ofNat 64 (e.evalState σ.rs)))
             buf := (loc.locVar, σ.rs.rsTower loc.locVar) :: σ.buf
             window := σ.window }, [])
      | none => (σ, [])
  | .RArrStore arr idxVar src =>
      let i := σ.rs.rsScalar idxVar
      match locatedLookup σ.rs arr, locatedLookup σ.rs src with
      | some oldV, some srcV =>
          ({ rs := locatedUpdate σ.rs arr
               (leafSpec.arrStore arr oldV i ⟨src.locDst, srcV⟩)
             buf := (arr.locVar, σ.rs.rsTower arr.locVar) :: σ.buf
             window := σ.window }, [Obs.memIdx idxVar i])
      | _, _ => (σ, [Obs.memIdx idxVar i])
  | .RArrStoreLit arr i src =>
      match locatedLookup σ.rs arr, locatedLookup σ.rs src with
      | some oldV, some srcV =>
          ({ rs := locatedUpdate σ.rs arr
               (leafSpec.arrStore arr oldV i ⟨src.locDst, srcV⟩)
             buf := (arr.locVar, σ.rs.rsTower arr.locVar) :: σ.buf
             window := σ.window }, [])
      | _, _ => (σ, [])
  | .RArrLoad dst src idxVar =>
      let i := σ.rs.rsScalar idxVar
      match locatedLookup σ.rs dst with
      | some oldDst =>
          match bypasses O σ src.locVar i with
          | some stale =>
              ({ rs := locatedUpdate σ.rs dst (leafSpec.arrLoad dst oldDst stale i)
                 buf := σ.buf
                 window := σ.window - 1 },
                [Obs.memIdx idxVar i,
                 Obs.stlForward src.locVar (towerLimb stale.2 i), Obs.rollback])
          | none =>
              match locatedLookup σ.rs src with
              | some srcV =>
                  let newV := leafSpec.arrLoad dst oldDst ⟨src.locDst, srcV⟩ i
                  ({ σ with rs := locatedUpdate σ.rs dst newV },
                    [Obs.memIdx idxVar i])
              | none => (σ, [Obs.memIdx idxVar i])
      | none => (σ, [Obs.memIdx idxVar i])
  | .RArrLoadLit dst src i =>
      match locatedLookup σ.rs dst with
      | some oldDst =>
          match bypasses O σ src.locVar i with
          | some stale =>
              ({ rs := locatedUpdate σ.rs dst (leafSpec.arrLoad dst oldDst stale i)
                 buf := σ.buf
                 window := σ.window - 1 },
                [Obs.stlForward src.locVar (towerLimb stale.2 i), Obs.rollback])
          | none =>
              match locatedLookup σ.rs src with
              | some srcV =>
                  let newV := leafSpec.arrLoad dst oldDst ⟨src.locDst, srcV⟩ i
                  ({ σ with rs := locatedUpdate σ.rs dst newV }, [])
              | none => (σ, [])
      | none => (σ, [])
  | .RCopy dst src =>
      match locatedLookup σ.rs src with
      | some v =>
          if h : src.locDst = dst.locDst then
            ({ σ with rs := locatedUpdate σ.rs dst (h ▸ v) }, [])
          else (σ, [])
      | none => (σ, [])
  | _ => (σ, [])

/-- `archRun leafSpec rs c` is the committed run of `c`: the same semantics with
    no store buffer, no speculation window and no predictor. -/
def archRun (leafSpec : LeafSpec) (rs : RustState) :
    LowCT → RustState × ObsTrace
  | .RSkip => (rs, [])
  | .RAssert _ => (rs, [])
  | .RScalarSet x n => (rsSetScalar rs x n, [])
  | .RScalarSetExpr x e => (rsSetScalar rs x (e.evalState rs), [])
  | .RSeq c1 c2 =>
      let r1 := archRun leafSpec rs c1
      let r2 := archRun leafSpec r1.1 c2
      (r2.1, r1.2 ++ r2.2)
  | .RLetZero _ _ body => archRun leafSpec rs body
  | .RLetU64Zero _ body => archRun leafSpec rs body
  | .RBlock body => archRun leafSpec rs body
  | .RFnDef _ _ _ body cont =>
      let r1 := archRun leafSpec rs body
      let r2 := archRun leafSpec r1.1 cont
      (r2.1, r1.2 ++ r2.2)
  | .RIfNz cond ct cf =>
      let v := rs.rsScalar cond
      let rt := archRun leafSpec rs ct
      let rf := archRun leafSpec rs cf
      ((if v ≠ 0 then rt.1 else rf.1),
        Obs.branch cond v :: (if v ≠ 0 then rt.2 else rf.2))
  | .RWhileNz cond body =>
      let v := rs.rsScalar cond
      let rb := archRun leafSpec rs body
      (rb.1, Obs.branch cond v :: rb.2)
  | .RFor _ _ body => archRun leafSpec rs body
  | .RSelect dst sel src0 src1 =>
      let s := if rs.rsScalar sel = 0 then src0 else src1
      match locatedLookup rs s with
      | some v =>
          if h : s.locDst = dst.locDst then (locatedUpdate rs dst (h ▸ v), [])
          else (rs, [])
      | none => (rs, [])
  | .RCall f dest args =>
      match locatedLookup rs dest with
      | some oldV =>
          let newV :=
            leafSpec.call f dest.locDst (args.map (fun a => a.locDst)) oldV
              (args.filterMap (fun a => rs.rsTower a.locVar))
          (locatedUpdate rs dest newV, [])
      | none => (rs, [])
  | .RLimbStore loc i v =>
      match locatedLookup rs loc with
      | some oldV => (locatedUpdate rs loc (leafSpec.limbStore loc oldV i v), [])
      | none => (rs, [])
  | .RLimbStoreExpr loc i e =>
      match locatedLookup rs loc with
      | some oldV =>
          (locatedUpdate rs loc
            (leafSpec.limbStore loc oldV i (BitVec.ofNat 64 (e.evalState rs))), [])
      | none => (rs, [])
  | .RArrStore arr idxVar src =>
      let i := rs.rsScalar idxVar
      match locatedLookup rs arr, locatedLookup rs src with
      | some oldV, some srcV =>
          (locatedUpdate rs arr (leafSpec.arrStore arr oldV i ⟨src.locDst, srcV⟩),
            [Obs.memIdx idxVar i])
      | _, _ => (rs, [Obs.memIdx idxVar i])
  | .RArrStoreLit arr i src =>
      match locatedLookup rs arr, locatedLookup rs src with
      | some oldV, some srcV =>
          (locatedUpdate rs arr (leafSpec.arrStore arr oldV i ⟨src.locDst, srcV⟩), [])
      | _, _ => (rs, [])
  | .RArrLoad dst src idxVar =>
      let i := rs.rsScalar idxVar
      match locatedLookup rs dst with
      | some oldDst =>
          match locatedLookup rs src with
          | some srcV =>
              (locatedUpdate rs dst
                (leafSpec.arrLoad dst oldDst ⟨src.locDst, srcV⟩ i), [Obs.memIdx idxVar i])
          | none => (rs, [Obs.memIdx idxVar i])
      | none => (rs, [Obs.memIdx idxVar i])
  | .RArrLoadLit dst src i =>
      match locatedLookup rs dst with
      | some oldDst =>
          match locatedLookup rs src with
          | some srcV =>
              (locatedUpdate rs dst
                (leafSpec.arrLoad dst oldDst ⟨src.locDst, srcV⟩ i), [])
          | none => (rs, [])
      | none => (rs, [])
  | .RCopy dst src =>
      match locatedLookup rs src with
      | some v =>
          if h : src.locDst = dst.locDst then (locatedUpdate rs dst (h ▸ v), [])
          else (rs, [])
      | none => (rs, [])
  | _ => (rs, [])

/-! ## 3. The architectural projections

Under the never-speculate predictor, and under any predictor once the window is
closed, `specRun` computes the committed state and the committed trace. -/

theorem specRun_neverSpeculate (leafSpec : LeafSpec) (c : LowCT) (σ : SpecState) :
    (specRun leafSpec neverSpeculate σ c).1.rs = (archRun leafSpec σ.rs c).1 ∧
      (specRun leafSpec neverSpeculate σ c).2 = (archRun leafSpec σ.rs c).2 := by
  induction c generalizing σ with
  | RSkip => exact ⟨rfl, rfl⟩
  | RAssert _ => exact ⟨rfl, rfl⟩
  | RScalarSet _ _ => exact ⟨rfl, rfl⟩
  | RScalarSetExpr _ _ => exact ⟨rfl, rfl⟩
  | RSeq c1 c2 ih1 ih2 =>
    have h1 := ih1 σ
    have h2 := ih2 (specRun leafSpec neverSpeculate σ c1).1
    rw [h1.1] at h2
    refine ⟨?_, ?_⟩
    · simpa only [specRun, archRun] using h2.1
    · simp only [specRun, archRun]
      rw [h1.2, h2.2]
  | RLetZero _ _ _ ih => simpa only [specRun, archRun] using ih σ
  | RLetU64Zero _ _ ih => simpa only [specRun, archRun] using ih σ
  | RBlock _ ih => simpa only [specRun, archRun] using ih σ
  | RFnDef _ _ _ body cont ih1 ih2 =>
    have h1 := ih1 σ
    have h2 := ih2 (specRun leafSpec neverSpeculate σ body).1
    rw [h1.1] at h2
    refine ⟨?_, ?_⟩
    · simpa only [specRun, archRun] using h2.1
    · simp only [specRun, archRun]
      rw [h1.2, h2.2]
  | RIfNz cond ct cf iht ihf =>
    have ht := iht σ
    have hf := ihf σ
    refine ⟨?_, ?_⟩ <;>
      simp only [specRun, archRun, neverSpeculate_mispredict, Bool.false_eq_true,
        and_false, ite_false, List.nil_append] <;>
      split
    · exact ht.1
    · exact hf.1
    · rw [ht.2]
    · rw [hf.2]
  | RWhileNz cond body ih =>
    have hb := ih σ
    refine ⟨?_, ?_⟩ <;>
      simp only [specRun, archRun, neverSpeculate_mispredict, Bool.false_eq_true,
        and_false, ite_false, List.nil_append]
    · exact hb.1
    · rw [hb.2]
  | RFor _ _ _ ih => simpa only [specRun, archRun] using ih σ
  | RSelect dst sel src0 src1 =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, rfl⟩
  | RCall _ dest _ =>
    simp only [specRun, archRun]
    split <;> exact ⟨rfl, rfl⟩
  | RLimbStore loc _ _ =>
    simp only [specRun, archRun]
    split <;> exact ⟨rfl, rfl⟩
  | RLimbStoreExpr loc _ _ =>
    simp only [specRun, archRun]
    split <;> exact ⟨rfl, rfl⟩
  | RArrStore arr idxVar src =>
    simp only [specRun, archRun]
    split <;> exact ⟨rfl, rfl⟩
  | RArrStoreLit arr _ src =>
    simp only [specRun, archRun]
    split <;> exact ⟨rfl, rfl⟩
  | RArrLoad dst src idxVar =>
    simp only [specRun, archRun, bypasses_neverSpeculate]
    split <;> [split; skip] <;> exact ⟨rfl, rfl⟩
  | RArrLoadLit dst src _ =>
    simp only [specRun, archRun, bypasses_neverSpeculate]
    split <;> [split; skip] <;> exact ⟨rfl, rfl⟩
  | RCopy dst src =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

theorem specRun_of_window_zero (leafSpec : LeafSpec) (O : SpecOracle) (c : LowCT)
    (σ : SpecState) (h : σ.window = 0) :
    (specRun leafSpec O σ c).1.rs = (archRun leafSpec σ.rs c).1 ∧
      (specRun leafSpec O σ c).1.window = 0 ∧
      (specRun leafSpec O σ c).2 = (archRun leafSpec σ.rs c).2 := by
  induction c generalizing σ with
  | RSkip => exact ⟨rfl, h, rfl⟩
  | RAssert _ => exact ⟨rfl, h, rfl⟩
  | RScalarSet _ _ => exact ⟨rfl, h, rfl⟩
  | RScalarSetExpr _ _ => exact ⟨rfl, h, rfl⟩
  | RSeq c1 c2 ih1 ih2 =>
    have h1 := ih1 σ h
    have h2 := ih2 (specRun leafSpec O σ c1).1 h1.2.1
    rw [h1.1] at h2
    refine ⟨?_, ?_, ?_⟩
    · simpa only [specRun, archRun] using h2.1
    · simpa only [specRun, archRun] using h2.2.1
    · simp only [specRun, archRun]
      rw [h1.2.2, h2.2.2]
  | RLetZero _ _ _ ih => simpa only [specRun, archRun] using ih σ h
  | RLetU64Zero _ _ ih => simpa only [specRun, archRun] using ih σ h
  | RBlock _ ih => simpa only [specRun, archRun] using ih σ h
  | RFnDef _ _ _ body cont ih1 ih2 =>
    have h1 := ih1 σ h
    have h2 := ih2 (specRun leafSpec O σ body).1 h1.2.1
    rw [h1.1] at h2
    refine ⟨?_, ?_, ?_⟩
    · simpa only [specRun, archRun] using h2.1
    · simpa only [specRun, archRun] using h2.2.1
    · simp only [specRun, archRun]
      rw [h1.2.2, h2.2.2]
  | RIfNz cond ct cf iht ihf =>
    have ht := iht σ h
    have hf := ihf σ h
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [specRun, archRun, h, lt_self_iff_false, false_and, ite_false,
        List.nil_append] <;>
      split
    · exact ht.1
    · exact hf.1
    · exact ht.2.1
    · exact hf.2.1
    · rw [ht.2.2]
    · rw [hf.2.2]
  | RWhileNz cond body ih =>
    have hb := ih σ h
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [specRun, archRun, h, lt_self_iff_false, false_and, ite_false,
        List.nil_append]
    · exact hb.1
    · exact hb.2.1
    · rw [hb.2.2]
  | RFor _ _ _ ih => simpa only [specRun, archRun] using ih σ h
  | RSelect dst sel src0 src1 =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RCall _ dest _ =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RLimbStore loc _ _ =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RLimbStoreExpr loc _ _ =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RArrStore arr idxVar src =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RArrStoreLit arr _ src =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RArrLoad dst src idxVar =>
    simp only [specRun, archRun, bypasses_of_window_zero O σ h]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RArrLoadLit dst src _ =>
    simp only [specRun, archRun, bypasses_of_window_zero O σ h]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | RCopy dst src =>
    simp only [specRun, archRun]
    repeat' split
    all_goals exact ⟨rfl, h, rfl⟩
  | _ => exact ⟨rfl, h, rfl⟩

/-! ## 4. Constant-time against the store-buffer observer -/

/-- **Speculatively constant-time.** Two runs of `c` from `PublicEquiv` states,
    each with an empty store buffer and window `window`, produce equal leakage
    traces. -/
def SpeculativelyConstantTimeSB (leafSpec : LeafSpec) (window : Nat) (O : SpecOracle)
    (lt : LevelTable) (c : LowCT) : Prop :=
  ∀ rs1 rs2 : RustState, PublicEquiv lt rs1 rs2 →
    (specRun leafSpec O ⟨rs1, [], window⟩ c).2
      = (specRun leafSpec O ⟨rs2, [], window⟩ c).2

/-- **Architecturally constant-time** for the committed run. -/
def ArchConstantTimeSB (leafSpec : LeafSpec) (lt : LevelTable) (c : LowCT) : Prop :=
  ∀ rs1 rs2 : RustState, PublicEquiv lt rs1 rs2 →
    (archRun leafSpec rs1 c).2 = (archRun leafSpec rs2 c).2

/-- At window `0` the two predicates coincide, for every predictor. -/
theorem window_zero_SCT (leafSpec : LeafSpec) (O : SpecOracle) (lt : LevelTable)
    (c : LowCT) (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec 0 O lt c := by
  intro rs1 rs2 hEq
  rw [(specRun_of_window_zero leafSpec O c ⟨rs1, [], 0⟩ rfl).2.2,
    (specRun_of_window_zero leafSpec O c ⟨rs2, [], 0⟩ rfl).2.2]
  exact h rs1 rs2 hEq

/-- Under the never-speculate predictor the two predicates coincide, for every
    window. -/
theorem neverSpeculate_SCT (leafSpec : LeafSpec) (window : Nat) (lt : LevelTable)
    (c : LowCT) (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec window neverSpeculate lt c := by
  intro rs1 rs2 hEq
  rw [(specRun_neverSpeculate leafSpec c ⟨rs1, [], window⟩).2,
    (specRun_neverSpeculate leafSpec c ⟨rs2, [], window⟩).2]
  exact h rs1 rs2 hEq

/-- **Public-determined predictor.** A predictor whose decisions agree on any two
    speculative states whose committed parts are `PublicEquiv` and whose buffer
    and window agree. `SpeculativeCT.PublicDriven` is the corresponding property
    for an oracle that is a function of a slot name and a runtime value only,
    where it holds by reflexivity; here the predictor sees the whole state, so
    the property constrains it. -/
def PublicDrivenSB (lt : LevelTable) (O : SpecOracle) : Prop :=
  ∀ σ1 σ2 : SpecState, PublicEquiv lt σ1.rs σ2.rs → σ1.buf = σ2.buf →
    σ1.window = σ2.window →
      (∀ x i, O.bypassStore σ1 x i = O.bypassStore σ2 x i) ∧
        (∀ cond v, O.mispredict σ1 cond v = O.mispredict σ2 cond v)

theorem neverSpeculate_publicDriven (lt : LevelTable) :
    PublicDrivenSB lt neverSpeculate :=
  fun _ _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem alwaysBypass_publicDriven (lt : LevelTable) :
    PublicDrivenSB lt alwaysBypass :=
  fun _ _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- A predictor that bypasses exactly when the scalar slot `s` is nonzero. -/
def peekOracle (s : String) : SpecOracle :=
  ⟨fun σ _ _ => σ.rs.rsScalar s != 0, fun _ _ _ => false⟩

/-! ## 5. An architecturally constant-time command that leaks speculatively

The command selects between two values under a secret selector, writes the
result into an array cell, overwrites that cell with a public value, reloads the
cell, and uses the reloaded byte as an array index. Committed execution reloads
the public value, so the index — hence the whole leakage trace — is the same from
either state. A load that bypasses the second write is forwarded the cell
contents the first write left behind, and the index is then the secret-selected
byte.

`cmdCT` accepts the command: every branch, index, source and destination slot it
names is `Public`. The secret slot is read only at the `RSelect` selector, which
`cmdCT` does not constrain — `cmdCT_sound` covers that read with its separate
`CMOVInvariant` hypothesis, which this command does not satisfy, and which
`SpeculativeCT.architecturally_CT_imp_SCT` does not assume. -/

namespace StlGadget

/-- An array whose cells are single bytes: cell `i` is byte `i`. -/
def arrStoreByte : ArrStoreSpec := fun _ oldV i sv k =>
  if k.val = i then rustValByte sv.2 0 else oldV k

/-- The matching load: cell `i` of the source becomes byte `0` of the
    destination. -/
def arrLoadByte : ArrLoadSpec := fun _ oldV sv i k =>
  if k.val = 0 then rustValByte sv.2 i else oldV k

/-- The leaf oracle table: byte-cell arrays, and identity for the leaf call and
    limb store, which the command does not use. -/
def leafSpecByte : LeafSpec where
  call := fun _ _ _ oldV _ => oldV
  limbStore := fun _ oldV _ _ => oldV
  arrStore := arrStoreByte
  arrLoad := arrLoadByte

/-- A one-byte value. -/
def u8val (n : Nat) : RustVal .TU8 := fun _ => BitVec.ofNat 8 n

/-- A four-cell zero array. -/
def arrZero : RustVal (.TArr 4 .TU8) := fun _ => 0

/-- The slots the command names. -/
def aL : Located := ⟨"a", .TU8⟩
/-- The first selector source. -/
def x0L : Located := ⟨"x0", .TU8⟩
/-- The second selector source. -/
def x1L : Located := ⟨"x1", .TU8⟩
/-- The public value that overwrites the cell. -/
def pubL : Located := ⟨"pubv", .TU8⟩
/-- The array the command stores into and reloads from. -/
def arrL : Located := ⟨"arr", .TArr 4 .TU8⟩
/-- The reload destination. -/
def ldL : Located := ⟨"ld", .TU8⟩
/-- The array the reloaded byte indexes. -/
def tblL : Located := ⟨"tbl", .TArr 4 .TU8⟩
/-- The final load's destination. -/
def outL : Located := ⟨"out", .TU8⟩

/-- Secret-selected value into an array cell, overwritten by a public value,
    reloaded, and used as an array index. -/
def stlGadget : LowCT :=
  .RSeq (.RSelect aL "sel" x0L x1L)
  (.RSeq (.RArrStore arrL "z" aL)
  (.RSeq (.RArrStore arrL "z" pubL)
  (.RSeq (.RArrLoad ldL arrL "z")
  (.RSeq (.RScalarSetExpr "j" (.SLimb "ld" 0))
         (.RArrLoad outL tblL "j")))))

/-- The command's store and reload, without the selector: the shape used to
    exhibit a predictor that reads a secret slot. -/
def stlStoreLoad : LowCT :=
  .RSeq (.RArrStore arrL "z" pubL) (.RArrLoad ldL arrL "z")

/-- Every slot is `Public` except the selector `sel`. -/
def stlLevels : LevelTable := fun x => if x = "sel" then .Secret else .Public

/-- The initial state, parameterised by the secret selector value. -/
def stlState (sel : Nat) : RustState where
  rsTower := fun x =>
    if x = "x0" then some ⟨.TU8, u8val 0⟩
    else if x = "x1" then some ⟨.TU8, u8val 1⟩
    else if x = "a" then some ⟨.TU8, u8val 0⟩
    else if x = "pubv" then some ⟨.TU8, u8val 7⟩
    else if x = "arr" then some ⟨.TArr 4 .TU8, arrZero⟩
    else if x = "ld" then some ⟨.TU8, u8val 0⟩
    else if x = "tbl" then some ⟨.TArr 4 .TU8, arrZero⟩
    else if x = "out" then some ⟨.TU8, u8val 0⟩
    else none
  rsScalar := fun s => if s = "sel" then sel else 0

/-- The states differ only on the secret selector slot. -/
theorem stlState_publicEquiv (a b : Nat) :
    PublicEquiv stlLevels (stlState a) (stlState b) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro x hx
  have hne : x ≠ "sel" := by
    intro he; rw [he] at hx; simp [stlLevels] at hx
  simp [stlState, hne]

/-- **`PublicDrivenSB` is a restriction.** A predictor that bypasses on the value
    of a `Secret` slot takes different decisions on two states the level table
    does not separate. -/
theorem peekOracle_not_publicDrivenSB :
    ¬ PublicDrivenSB stlLevels (peekOracle "sel") := by
  intro h
  have hd := (h ⟨stlState 0, [], 0⟩ ⟨stlState 1, [], 0⟩
    (stlState_publicEquiv 0 1) rfl rfl).1 "arr" 0
  simp [peekOracle, stlState] at hd

/-- The architectural constant-time analyser accepts the command. -/
theorem stlGadget_cmdCT :
    cmdCT stlGadget stlLevels LeafCTTable.canonical = true := by decide

/-- The command's `RSelect` sources hold different values, so it is outside the
    `CMOVInvariant` hypothesis of `cmdCT_sound`.
    `SpeculativeCT.architecturally_CT_imp_SCT` does not assume that hypothesis. -/
theorem stlGadget_not_CMOVInvariant : ¬ CMOVInvariant stlGadget := by
  intro h
  simp only [stlGadget, CMOVInvariant] at h
  have h1 : (stlState 0).rsTower "x0" = (stlState 0).rsTower "x1" := h.1 (stlState 0)
  have h2 : (⟨.TU8, u8val 0⟩ : Σ t : TowerType, RustVal t) = ⟨.TU8, u8val 1⟩ := by
    simpa [stlState] using h1
  have h3 : u8val 0 = u8val 1 := eq_of_heq (Sigma.mk.inj h2).2
  have h4 := congrFun h3 ⟨0, by decide⟩
  simp [u8val] at h4

/-- Committed execution of the command produces the same leakage trace from
    either state: the reload sees the public value the second store left in the
    cell, so the final index is public. -/
theorem stlGadget_arch_agree :
    (archRun leafSpecByte (stlState 0) stlGadget).2
      = (archRun leafSpecByte (stlState 1) stlGadget).2 := by decide

/-- The committed trace, explicitly: three accesses at the public cell index and
    one at the reloaded public byte. -/
theorem stlGadget_arch_trace :
    (archRun leafSpecByte (stlState 0) stlGadget).2
      = [Obs.memIdx "z" 0, Obs.memIdx "z" 0, Obs.memIdx "z" 0, Obs.memIdx "j" 7] := by
  decide

/-- The speculative trace from the state whose selector is `0`: the transient
    forward carries the word the second store overwrote, then a table access at
    byte `0`. -/
theorem stlGadget_spec_trace_zero :
    (specRun leafSpecByte alwaysBypass ⟨stlState 0, [], 2⟩ stlGadget).2
      = [Obs.memIdx "z" 0, Obs.memIdx "z" 0, Obs.memIdx "z" 0,
         Obs.stlForward "arr" 0, Obs.rollback, Obs.memIdx "j" 0] := by
  decide

/-- The speculative trace from the state whose selector is `1`: the transient
    forward carries the secret-selected byte, then a table access at byte
    `1`. -/
theorem stlGadget_spec_trace_one :
    (specRun leafSpecByte alwaysBypass ⟨stlState 1, [], 2⟩ stlGadget).2
      = [Obs.memIdx "z" 0, Obs.memIdx "z" 0, Obs.memIdx "z" 0,
         Obs.stlForward "arr" 1, Obs.rollback, Obs.memIdx "j" 1] := by
  decide

/-- **The command is not speculatively constant-time.** Under a predictor that
    bypasses the pending write, the reload is forwarded the cell contents the
    first store left behind, and the final load addresses the table at the
    secret-selected byte. -/
theorem stlGadget_speculative_leak :
    (specRun leafSpecByte alwaysBypass ⟨stlState 0, [], 2⟩ stlGadget).2
      ≠ (specRun leafSpecByte alwaysBypass ⟨stlState 1, [], 2⟩ stlGadget).2 := by
  decide

/-- **`cmdCT` acceptance does not imply speculative constant-time**, for a
    predictor that is itself public-determined. -/
theorem cmdCT_not_imp_SCT :
    cmdCT stlGadget stlLevels LeafCTTable.canonical = true ∧
      PublicDrivenSB stlLevels alwaysBypass ∧
        ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
            stlGadget :=
  ⟨stlGadget_cmdCT, alwaysBypass_publicDriven stlLevels,
    fun hSCT => stlGadget_speculative_leak
      (hSCT (stlState 0) (stlState 1) (stlState_publicEquiv 0 1))⟩

/-- A predictor reading the secret slot separates the traces of a store followed
    by a reload: the transient forward occurs from one state and not the
    other. -/
theorem peek_speculative_leak :
    (specRun leafSpecByte (peekOracle "sel") ⟨stlState 0, [], 2⟩ stlStoreLoad).2
      ≠ (specRun leafSpecByte (peekOracle "sel") ⟨stlState 1, [], 2⟩ stlStoreLoad).2 := by
  decide

/-- The store-and-reload command is accepted by `cmdCT` under a level table with
    a secret slot, so a secret-reading predictor breaks speculative constant-time
    on it. -/
theorem stlStoreLoad_cmdCT :
    cmdCT stlStoreLoad stlLevels LeafCTTable.canonical = true := by decide

/-- `SpeculativeCT.specObs` gives the command the same trace from both states,
    for every window and every misprediction oracle. Its `Obs.stlForward` reads
    the source slot against the entry state, where the array holds the zero value
    both states start from; the secret-selected byte the command writes into that
    array is a state change the entry-state observer does not see. -/
theorem stlGadget_specObs_agree (window : SpecWindow) (O : MispredOracle) :
    specObs window O (stlState 0) stlGadget = specObs window O (stlState 1) stlGadget :=
  architecturally_CT_imp_SCT window O stlLevels LeafCTTable.canonical stlGadget
    stlGadget_cmdCT _ _ (stlState_publicEquiv 0 1)

/-! ## 6. `cmdCT` and the committed trace

The fence and mask passes conclude speculative constant-time from `cmdCT` in two
steps: the hardened speculative trace collapses to the committed trace, and the
committed trace is constant-time by `SpeculativeCT.architecturally_CT_imp_ArchCT`.
`window_zero_SCT` and `neverSpeculate_SCT` are the collapse step for the
store-buffer observer. The second step does not carry over from `cmdCT` alone:
`cmdCT` constrains the selector of an `RSelect` nowhere, so a `cmdCT`-accepted
command can move a secret-selected value into a slot the analyser classifies
`Public` and from there into an address. `cmdCT_sound` covers that read with its
`CMOVInvariant` hypothesis; `architecturally_CT_imp_ArchCT` does not need it
because `SpeculativeCT.archObs` reads every slot against the entry state and so
never sees the write. §7 adds that hypothesis back, as `SelectAgrees`. -/

/-- Secret-selected value straight into an array index, with no store or reload.
    Committed execution already leaks. -/
def archLeakGadget : LowCT :=
  .RSeq (.RSelect aL "sel" x0L x1L)
  (.RSeq (.RScalarSetExpr "j" (.SLimb "a" 0))
         (.RArrLoad outL tblL "j"))

theorem archLeakGadget_cmdCT :
    cmdCT archLeakGadget stlLevels LeafCTTable.canonical = true := by decide

theorem archLeakGadget_arch_leak :
    (archRun leafSpecByte (stlState 0) archLeakGadget).2
      ≠ (archRun leafSpecByte (stlState 1) archLeakGadget).2 := by decide

/-- **`cmdCT` acceptance does not imply constant-time for the committed
    store-buffer run.** -/
theorem cmdCT_not_imp_ArchCT :
    cmdCT archLeakGadget stlLevels LeafCTTable.canonical = true ∧
      ¬ ArchConstantTimeSB leafSpecByte stlLevels archLeakGadget :=
  ⟨archLeakGadget_cmdCT, fun h => archLeakGadget_arch_leak
    (h (stlState 0) (stlState 1) (stlState_publicEquiv 0 1))⟩

end StlGadget

/-! ## 7. Constant-time under a public-driven predictor and agreeing CMOV sources

`cmdCT` alone does not give `SpeculativelyConstantTimeSB` (`cmdCT_not_imp_SCT`).
Two further conditions close the gap:

* the predictor is `PublicDrivenSB`;
* at every `RSelect` the two sources have the same tower type and hold the same
  contents in every state (`SelectAgrees`).

`cmdCT` classifies the destination and the two sources of an `RSelect` but not
its selector, so a `cmdCT`-accepted command may move a secret-selected value into
a `Public` slot. `SelectAgrees` is `CMOVInvariant` together with the type
agreement the run needs for both runs to take the same branch of the destination
type check.

Each condition is refuted on its own by a command satisfying the other, and both
hold of `StlGadget.cmovStlGadget`, whose speculative trace contains a transient
forward and whose selector is `Secret`. -/

/-- At every `RSelect` the two sources have the same tower type and hold the same
    contents in every state. -/
def SelectAgrees : LowCT → Prop
  | .RSelect _ _ src0 src1 =>
      src0.locSrc = src1.locSrc ∧
        ∀ rs : RustState, rs.rsTower src0.locVar = rs.rsTower src1.locVar
  | .RSeq c1 c2             => SelectAgrees c1 ∧ SelectAgrees c2
  | .RLetZero _ _ body      => SelectAgrees body
  | .RLetU64Zero _ body     => SelectAgrees body
  | .RBlock body            => SelectAgrees body
  | .RFor _ _ body          => SelectAgrees body
  | .RForRuntime _ _ body   => SelectAgrees body
  | .RIfNz _ c1 c2          => SelectAgrees c1 ∧ SelectAgrees c2
  | .RWhileNz _ body        => SelectAgrees body
  | .RFnDef _ _ _ body cont => SelectAgrees body ∧ SelectAgrees cont
  | _                       => True

/-- `SelectAgrees` is `CMOVInvariant` with the type agreement added. -/
theorem cmovInvariant_of_selectAgrees (c : LowCT) : SelectAgrees c → CMOVInvariant c := by
  induction c with
  | RSelect _ _ _ _ => exact fun h => h.2
  | RSeq _ _ ih1 ih2 => exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | RLetZero _ _ _ ih => exact fun h => ih h
  | RLetU64Zero _ _ ih => exact fun h => ih h
  | RBlock _ ih => exact fun h => ih h
  | RFor _ _ _ ih => exact fun h => ih h
  | RForRuntime _ _ _ ih => exact fun h => ih h
  | RIfNz _ _ _ ih1 ih2 => exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | RWhileNz _ _ ih => exact fun h => ih h
  | RFnDef _ _ _ _ _ ih1 ih2 => exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | _ => exact fun _ => trivial

/-- Two speculative states are related when their committed parts are
    `PublicEquiv` and their buffers and windows agree. -/
def SpecEquiv (lt : LevelTable) (σ1 σ2 : SpecState) : Prop :=
  PublicEquiv lt σ1.rs σ2.rs ∧ σ1.buf = σ2.buf ∧ σ1.window = σ2.window

/-- A public-driven predictor forwards the same value on related states. -/
theorem bypasses_pub_determined {lt : LevelTable} {O : SpecOracle}
    (hO : PublicDrivenSB lt O) {σ1 σ2 : SpecState} (h : SpecEquiv lt σ1 σ2)
    (x : String) (i : Nat) : bypasses O σ1 x i = bypasses O σ2 x i := by
  simp only [bypasses, (hO σ1 σ2 h.1 h.2.1 h.2.2).1 x i, h.2.1, h.2.2]

/-- Public argument slots give equal argument lists. -/
theorem args_tower_eq {lt : LevelTable} {rs1 rs2 : RustState}
    (hEq : PublicEquiv lt rs1 rs2) {args : List Located}
    (hArgs : args.all (fun a => lt a.locVar == .Public) = true) :
    args.filterMap (fun a => rs1.rsTower a.locVar)
      = args.filterMap (fun a => rs2.rsTower a.locVar) := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hArgs
    have hA : lt a.locVar = .Public := level_beq_public_iff.mp hArgs.1
    simp [List.filterMap_cons, hEq.tower_eq hA, ih hArgs.2]

/-- **The speculative run is public-determined.** A `cmdCT`-accepted command
    whose `RSelect` sources agree, run under a public-driven predictor from two
    related speculative states, produces equal leakage traces and related
    post-states. -/
theorem specRun_pub_determined (leafSpec : LeafSpec) (lt : LevelTable)
    (leafCT : LeafCTTable) {O : SpecOracle} (hO : PublicDrivenSB lt O) (c : LowCT) :
    cmdCT c lt leafCT = true → SelectAgrees c →
      ∀ σ1 σ2 : SpecState, SpecEquiv lt σ1 σ2 →
        (specRun leafSpec O σ1 c).2 = (specRun leafSpec O σ2 c).2 ∧
          SpecEquiv lt (specRun leafSpec O σ1 c).1 (specRun leafSpec O σ2 c).1 := by
  induction c with
  | RScalarSet x n =>
    intro _ _ σ1 σ2 h
    refine ⟨rfl, ?_⟩
    exact ⟨h.1.set_scalar_same x n, h.2.1, h.2.2⟩
  | RScalarSetExpr x e =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RScalarSetExpr] at hCT
    have he : e.evalState σ1.rs = e.evalState σ2.rs :=
      SExpr.evalState_eq_of_isPublic h.1 e hCT
    refine ⟨rfl, ?_⟩
    simp only [specRun, he]
    exact ⟨h.1.set_scalar_same x _, h.2.1, h.2.2⟩
  | RSeq c1 c2 ih1 ih2 =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RSeq, Bool.and_eq_true] at hCT
    obtain ⟨t1, s1⟩ := ih1 hCT.1 hSA.1 σ1 σ2 h
    obtain ⟨t2, s2⟩ := ih2 hCT.2 hSA.2 _ _ s1
    exact ⟨by simp only [specRun]; rw [t1, t2], by simpa only [specRun] using s2⟩
  | RLetZero _ _ _ ih =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RLetZero] at hCT
    simpa only [specRun] using ih hCT hSA σ1 σ2 h
  | RLetU64Zero _ _ ih =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RLetU64Zero] at hCT
    simpa only [specRun] using ih hCT hSA σ1 σ2 h
  | RBlock _ ih =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RBlock] at hCT
    simpa only [specRun] using ih hCT hSA σ1 σ2 h
  | RFor _ _ _ ih =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RFor] at hCT
    simpa only [specRun] using ih hCT hSA σ1 σ2 h
  | RFnDef _ _ _ body cont ih1 ih2 =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RFnDef, Bool.and_eq_true] at hCT
    obtain ⟨t1, s1⟩ := ih1 hCT.1 hSA.1 σ1 σ2 h
    obtain ⟨t2, s2⟩ := ih2 hCT.2 hSA.2 _ _ s1
    exact ⟨by simp only [specRun]; rw [t1, t2], by simpa only [specRun] using s2⟩
  | RIfNz cond ct cf iht ihf =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT
    have hc : lt cond = .Public := level_beq_public_iff.mp hCT.1.1
    have hv : σ1.rs.rsScalar cond = σ2.rs.rsScalar cond := h.1.scalar_eq hc
    have hm : ∀ v, O.mispredict σ1 cond v = O.mispredict σ2 cond v :=
      fun v => (hO σ1 σ2 h.1 h.2.1 h.2.2).2 cond v
    obtain ⟨tt, st⟩ := iht hCT.1.2 hSA.1 σ1 σ2 h
    obtain ⟨tf, sf⟩ := ihf hCT.2 hSA.2 σ1 σ2 h
    refine ⟨by simp only [specRun, hv, tt, tf, hm, h.2.2], ?_⟩
    simp only [specRun, hv]
    split
    · exact st
    · exact sf
  | RWhileNz cond body ih =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RWhileNz, Bool.and_eq_true] at hCT
    have hc : lt cond = .Public := level_beq_public_iff.mp hCT.1
    have hv : σ1.rs.rsScalar cond = σ2.rs.rsScalar cond := h.1.scalar_eq hc
    have hm : ∀ v, O.mispredict σ1 cond v = O.mispredict σ2 cond v :=
      fun v => (hO σ1 σ2 h.1 h.2.1 h.2.2).2 cond v
    obtain ⟨tb, sb⟩ := ih hCT.2 hSA σ1 σ2 h
    exact ⟨by simp only [specRun, hv, tb, hm, h.2.2],
           by simpa only [specRun] using sb⟩
  | RSelect dst sel src0 src1 =>
    intro hCT hSA σ1 σ2 h
    simp only [cmdCT_RSelect, Bool.and_eq_true] at hCT
    have hs0 : lt src0.locVar = .Public := level_beq_public_iff.mp hCT.1.2
    have hs1 : lt src1.locVar = .Public := level_beq_public_iff.mp hCT.2
    obtain ⟨hty, hcm⟩ := hSA
    obtain ⟨w0, t0⟩ := src0
    obtain ⟨w1, t1⟩ := src1
    have hty' : t0 = t1 := hty
    subst hty'
    have hcm' : ∀ rs : RustState, rs.rsTower w0 = rs.rsTower w1 := hcm
    have hsame : ∀ rs : RustState,
        locatedLookup rs (⟨w0, t0⟩ : Located) = locatedLookup rs ⟨w1, t0⟩ := by
      intro rs
      simp only [locatedLookup, hcm' rs]
    have e00 : locatedLookup σ1.rs (⟨w0, t0⟩ : Located)
        = locatedLookup σ2.rs ⟨w0, t0⟩ := h.1.locatedLookup_eq hs0
    have e11 : locatedLookup σ1.rs (⟨w1, t0⟩ : Located)
        = locatedLookup σ2.rs ⟨w1, t0⟩ := h.1.locatedLookup_eq hs1
    have e01 : locatedLookup σ1.rs (⟨w0, t0⟩ : Located)
        = locatedLookup σ2.rs ⟨w1, t0⟩ := by rw [e00, hsame σ2.rs]
    have e10 : locatedLookup σ1.rs (⟨w1, t0⟩ : Located)
        = locatedLookup σ2.rs ⟨w0, t0⟩ := by rw [e11, ← hsame σ2.rs]
    by_cases h1 : σ1.rs.rsScalar sel = 0 <;> by_cases h2 : σ2.rs.rsScalar sel = 0 <;>
      simp only [specRun]
    · rw [ite_eq_left h1, ite_eq_left h2, e00]
      repeat' split
      all_goals first
        | exact ⟨rfl, h⟩
        | exact ⟨rfl, h.1.set_tower_same _ _, h.2.1, h.2.2⟩
    · rw [ite_eq_left h1, ite_eq_right h2, e01]
      repeat' split
      all_goals first
        | exact ⟨rfl, h⟩
        | exact ⟨rfl, h.1.set_tower_same _ _, h.2.1, h.2.2⟩
    · rw [ite_eq_right h1, ite_eq_left h2, e10]
      repeat' split
      all_goals first
        | exact ⟨rfl, h⟩
        | exact ⟨rfl, h.1.set_tower_same _ _, h.2.1, h.2.2⟩
    · rw [ite_eq_right h1, ite_eq_right h2, e11]
      repeat' split
      all_goals first
        | exact ⟨rfl, h⟩
        | exact ⟨rfl, h.1.set_tower_same _ _, h.2.1, h.2.2⟩
  | RCall f dest args =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RCall, Bool.and_eq_true] at hCT
    have hdest : lt dest.locVar = .Public := level_beq_public_iff.mp hCT.1.2
    have hlk : locatedLookup σ1.rs dest = locatedLookup σ2.rs dest :=
      h.1.locatedLookup_eq hdest
    have ha : args.filterMap (fun a => σ1.rs.rsTower a.locVar)
        = args.filterMap (fun a => σ2.rs.rsTower a.locVar) := args_tower_eq h.1 hCT.2
    refine ⟨?_, ?_⟩ <;> simp only [specRun, hlk, ha] <;> repeat' split
    all_goals first
      | rfl
      | exact h
      | exact ⟨h.1.set_tower_same _ _, h.2.1, h.2.2⟩
  | RLimbStore loc i v =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RLimbStore] at hCT
    have hloc : lt loc.locVar = .Public := level_beq_public_iff.mp hCT
    have hlk : locatedLookup σ1.rs loc = locatedLookup σ2.rs loc :=
      h.1.locatedLookup_eq hloc
    have hT : σ1.rs.rsTower loc.locVar = σ2.rs.rsTower loc.locVar := h.1.tower_eq hloc
    refine ⟨?_, ?_⟩ <;> simp only [specRun, hlk, hT, h.2.1] <;> repeat' split
    all_goals first
      | rfl
      | exact h
      | exact ⟨h.1.set_tower_same _ _, rfl, h.2.2⟩
  | RLimbStoreExpr loc i e =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RLimbStoreExpr, Bool.and_eq_true] at hCT
    have hloc : lt loc.locVar = .Public := level_beq_public_iff.mp hCT.1
    have hlk : locatedLookup σ1.rs loc = locatedLookup σ2.rs loc :=
      h.1.locatedLookup_eq hloc
    have hT : σ1.rs.rsTower loc.locVar = σ2.rs.rsTower loc.locVar := h.1.tower_eq hloc
    have he : e.evalState σ1.rs = e.evalState σ2.rs :=
      SExpr.evalState_eq_of_isPublic h.1 e hCT.2
    refine ⟨?_, ?_⟩ <;> simp only [specRun, hlk, hT, he, h.2.1] <;> repeat' split
    all_goals first
      | rfl
      | exact h
      | exact ⟨h.1.set_tower_same _ _, rfl, h.2.2⟩
  | RArrStore arr idxVar src =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RArrStore, Bool.and_eq_true] at hCT
    have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
    have harr : lt arr.locVar = .Public := level_beq_public_iff.mp hCT.1.2
    have hsrc : lt src.locVar = .Public := level_beq_public_iff.mp hCT.2
    have hi : σ1.rs.rsScalar idxVar = σ2.rs.rsScalar idxVar := h.1.scalar_eq hidx
    have hlkA : locatedLookup σ1.rs arr = locatedLookup σ2.rs arr :=
      h.1.locatedLookup_eq harr
    have hlkS : locatedLookup σ1.rs src = locatedLookup σ2.rs src :=
      h.1.locatedLookup_eq hsrc
    have hT : σ1.rs.rsTower arr.locVar = σ2.rs.rsTower arr.locVar := h.1.tower_eq harr
    refine ⟨?_, ?_⟩ <;>
      simp only [specRun, hi, hlkA, hlkS, hT, h.2.1] <;> repeat' split
    all_goals first
      | rfl
      | exact h
      | exact ⟨h.1.set_tower_same _ _, rfl, h.2.2⟩
  | RArrStoreLit arr i src =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RArrStoreLit, Bool.and_eq_true] at hCT
    have harr : lt arr.locVar = .Public := level_beq_public_iff.mp hCT.1
    have hsrc : lt src.locVar = .Public := level_beq_public_iff.mp hCT.2
    have hlkA : locatedLookup σ1.rs arr = locatedLookup σ2.rs arr :=
      h.1.locatedLookup_eq harr
    have hlkS : locatedLookup σ1.rs src = locatedLookup σ2.rs src :=
      h.1.locatedLookup_eq hsrc
    have hT : σ1.rs.rsTower arr.locVar = σ2.rs.rsTower arr.locVar := h.1.tower_eq harr
    refine ⟨?_, ?_⟩ <;>
      simp only [specRun, hlkA, hlkS, hT, h.2.1] <;> repeat' split
    all_goals first
      | rfl
      | exact h
      | exact ⟨h.1.set_tower_same _ _, rfl, h.2.2⟩
  | RArrLoad dst src idxVar =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
    have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
    have hdst : lt dst.locVar = .Public := level_beq_public_iff.mp hCT.1.2
    have hsrc : lt src.locVar = .Public := level_beq_public_iff.mp hCT.2
    have hi : σ1.rs.rsScalar idxVar = σ2.rs.rsScalar idxVar := h.1.scalar_eq hidx
    have hlkD : locatedLookup σ1.rs dst = locatedLookup σ2.rs dst :=
      h.1.locatedLookup_eq hdst
    have hlkS : locatedLookup σ1.rs src = locatedLookup σ2.rs src :=
      h.1.locatedLookup_eq hsrc
    have hb : ∀ j, bypasses O σ1 src.locVar j = bypasses O σ2 src.locVar j :=
      fun j => bypasses_pub_determined hO h src.locVar j
    refine ⟨?_, ?_⟩ <;>
      simp only [specRun, hi, hlkD, hlkS, hb] <;> repeat' split
    all_goals first
      | rfl
      | exact h
      | exact ⟨h.1.set_tower_same _ _, h.2.1, by rw [h.2.2]⟩
  | RArrLoadLit dst src i =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RArrLoadLit, Bool.and_eq_true] at hCT
    have hdst : lt dst.locVar = .Public := level_beq_public_iff.mp hCT.1
    have hsrc : lt src.locVar = .Public := level_beq_public_iff.mp hCT.2
    have hlkD : locatedLookup σ1.rs dst = locatedLookup σ2.rs dst :=
      h.1.locatedLookup_eq hdst
    have hlkS : locatedLookup σ1.rs src = locatedLookup σ2.rs src :=
      h.1.locatedLookup_eq hsrc
    have hb : ∀ j, bypasses O σ1 src.locVar j = bypasses O σ2 src.locVar j :=
      fun j => bypasses_pub_determined hO h src.locVar j
    refine ⟨?_, ?_⟩ <;>
      simp only [specRun, hlkD, hlkS, hb] <;> repeat' split
    all_goals first
      | rfl
      | exact h
      | exact ⟨h.1.set_tower_same _ _, h.2.1, by rw [h.2.2]⟩
  | RCopy dst src =>
    intro hCT _ σ1 σ2 h
    simp only [cmdCT_RCopy] at hCT
    rcases Bool.or_eq_true_iff.mp hCT with hS | hD
    · have hlk : locatedLookup σ1.rs src = locatedLookup σ2.rs src :=
        h.1.locatedLookup_eq (level_beq_public_iff.mp hS)
      refine ⟨?_, ?_⟩ <;> simp only [specRun, hlk] <;> repeat' split
      all_goals first
        | rfl
        | exact h
        | exact ⟨h.1.set_tower_same _ _, h.2.1, h.2.2⟩
    · have hSec : lt dst.locVar ≠ .Public := by
        intro hP
        rw [hP] at hD
        exact absurd hD (by decide)
      refine ⟨?_, ?_⟩ <;> simp only [specRun] <;> repeat' split
      all_goals first
        | rfl
        | exact h
        | exact ⟨h.1.set_tower_secret hSec _ _, h.2.1, h.2.2⟩
        | exact ⟨h.1.set_tower_secret_left hSec _, h.2.1, h.2.2⟩
        | exact ⟨(h.1.symm.set_tower_secret_left hSec _).symm, h.2.1, h.2.2⟩
  | _ => exact fun _ _ _ _ h => ⟨rfl, h⟩

/-- **Store-buffer speculative constant-time.** A `cmdCT`-accepted command whose
    `RSelect` sources agree is speculatively constant-time against the
    store-buffer observer under a public-driven predictor, for every speculation
    window. -/
theorem cmdCT_cmov_publicDriven_imp_SCT_SB (leafSpec : LeafSpec) (window : Nat)
    (lt : LevelTable) (leafCT : LeafCTTable) {O : SpecOracle}
    (hO : PublicDrivenSB lt O) (c : LowCT) (hCT : cmdCT c lt leafCT = true)
    (hSA : SelectAgrees c) : SpeculativelyConstantTimeSB leafSpec window O lt c :=
  fun rs1 rs2 hEq =>
    (specRun_pub_determined leafSpec lt leafCT hO c hCT hSA ⟨rs1, [], window⟩
      ⟨rs2, [], window⟩ ⟨hEq, rfl, rfl⟩).1

namespace StlGadget

/-- The store-to-load gadget with the conditional move's two sources made the
    same slot: a move on a `Secret` selector whose sources agree, followed by the
    same store, reload and table access. -/
def cmovStlGadget : LowCT :=
  .RSeq (.RSelect aL "sel" x0L x0L)
  (.RSeq (.RArrStore arrL "z" aL)
  (.RSeq (.RArrStore arrL "z" pubL)
  (.RSeq (.RArrLoad ldL arrL "z")
  (.RSeq (.RScalarSetExpr "j" (.SLimb "ld" 0))
         (.RArrLoad outL tblL "j")))))

theorem cmovStlGadget_cmdCT :
    cmdCT cmovStlGadget stlLevels LeafCTTable.canonical = true := by decide

theorem cmovStlGadget_selectAgrees : SelectAgrees cmovStlGadget :=
  ⟨⟨rfl, fun _ => rfl⟩, trivial, trivial, trivial, trivial, trivial⟩

/-- The gadget's speculative trace contains a transient forward, so the
    constant-time conclusion below is not an equality between transient-free
    traces. -/
theorem cmovStlGadget_trace :
    (specRun leafSpecByte alwaysBypass ⟨stlState 0, [], 2⟩ cmovStlGadget).2
      = [Obs.memIdx "z" 0, Obs.memIdx "z" 0, Obs.memIdx "z" 0,
         Obs.stlForward "arr" 0, Obs.rollback, Obs.memIdx "j" 0] := by
  decide

/-- **The hypotheses are satisfiable on a command that reads a `Secret` slot and
    forwards transiently.** -/
theorem cmovStlGadget_SCT_SB (window : Nat) :
    SpeculativelyConstantTimeSB leafSpecByte window alwaysBypass stlLevels
      cmovStlGadget :=
  cmdCT_cmov_publicDriven_imp_SCT_SB leafSpecByte window stlLevels
    LeafCTTable.canonical (alwaysBypass_publicDriven stlLevels) cmovStlGadget
    cmovStlGadget_cmdCT cmovStlGadget_selectAgrees

theorem stlGadget_not_selectAgrees : ¬ SelectAgrees stlGadget :=
  fun h => stlGadget_not_CMOVInvariant (cmovInvariant_of_selectAgrees stlGadget h)

theorem stlStoreLoad_selectAgrees : SelectAgrees stlStoreLoad := ⟨trivial, trivial⟩

theorem stlStoreLoad_not_SCT_SB :
    ¬ SpeculativelyConstantTimeSB leafSpecByte 2 (peekOracle "sel") stlLevels
        stlStoreLoad :=
  fun hSCT => peek_speculative_leak
    (hSCT (stlState 0) (stlState 1) (stlState_publicEquiv 0 1))

/-- **Neither hypothesis of `cmdCT_cmov_publicDriven_imp_SCT_SB` is removable.**
    The first command satisfies `cmdCT` and is run under a public-driven
    predictor, fails `SelectAgrees`, and leaks. The second satisfies `cmdCT` and
    `SelectAgrees`, is run under a predictor that is not public-driven, and
    leaks. -/
theorem sct_SB_hypotheses_sharp :
    (cmdCT stlGadget stlLevels LeafCTTable.canonical = true ∧
        PublicDrivenSB stlLevels alwaysBypass ∧ ¬ SelectAgrees stlGadget ∧
          ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
              stlGadget) ∧
      (cmdCT stlStoreLoad stlLevels LeafCTTable.canonical = true ∧
        SelectAgrees stlStoreLoad ∧
          ¬ PublicDrivenSB stlLevels (peekOracle "sel") ∧
            ¬ SpeculativelyConstantTimeSB leafSpecByte 2 (peekOracle "sel")
                stlLevels stlStoreLoad) :=
  ⟨⟨stlGadget_cmdCT, alwaysBypass_publicDriven stlLevels, stlGadget_not_selectAgrees,
    cmdCT_not_imp_SCT.2.2⟩,
   ⟨stlStoreLoad_cmdCT, stlStoreLoad_selectAgrees, peekOracle_not_publicDrivenSB,
    stlStoreLoad_not_SCT_SB⟩⟩

end StlGadget

/-! ## 8. Scope of the model

Covered: store-to-load forwarding at whole-slot granularity, with the forwarded
word both emitted as `Obs.stlForward` and entering the committed state, so it also
reaches later addresses; a predictor that reads the whole speculative state; the
memory-address and branch-decision channel; the constant-time statement that
survives on it (`cmdCT_cmov_publicDriven_imp_SCT_SB`).

Not covered: indirect-branch and return misprediction, which
`SpeculativeCT.specObs` reads off a call's destination slot and which this module
leaves as it found them; per-cell store buffering — an entry records a whole slot,
so a bypassing load reads the cell out of the slot value the write overwrote;
loop unrolling, since `RWhileNz` and `RFor` run their body once; the transient
window's own memory effects, since a mispredicted branch contributes its trace and
its state is discarded; cache-line granularity and timing; the `LowCT`
constructors outside the list in the module header, which are state-preserving
here.

`specRun` and `archRun` are deterministic total functions, whereas `RustExec` is a
relation; on the constructors both model they agree. `RScalarSetExpr` is
interpreted with the tower-aware `SExpr.evalState`, as in
`RustExec.scalarSetExpr`. -/

end CatCrypt.Crypto.SecureCompilation.SpeculativeCTStoreBuffer
