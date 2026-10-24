/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# `scheduleBlock`: verified intra-block instruction scheduling for ILP

A `Com → Com` (here `LowCT → LowCT`) transform that **reorders
independent straight-line statements** to shorten the critical
data-dependence path and fill latency shadows (the classic *list
scheduling* pass).  It sits alongside the other verified Com→Com passes
(`BarrettReduce`, `MontgomeryReduce`, `Lattice.NTTPolyMul`, …) in this
directory, and follows the same shape: a syntactic rewrite together with
a `RustExec`-equivalence theorem.

## Motivation

Latency-bound kernels — the safegcd-62 divstep's
`#IMUL → #IMUL → SAR` Montgomery accumulate chain, NTT butterflies — are
measured to be bottlenecked by serial dependency chains, not spills.  Register
allocation cannot help a chain whose every instruction reads the
previous one's output.  Instruction scheduling is the classical answer:
hoist *independent* ops (e.g. the next product `plo`/`phi`) up to run in
the shadow of a long-latency op, so the out-of-order issue window stays
fed.

## What this pass does

A **basic block** is a maximal straight-line run of two statement
shapes that dominate the hot accumulate loops:

* `RScalarSetExpr x e` — a scalar assignment `x := eval e` (the `#IMUL` /
  `SAR` / add chain is *all* of these), and
* `RCall f dst args` — a leaf call writing `dst` from `args`.

`scheduleBlock` reorders the block by a *latency-aware list schedule*:
topological order over the data-dependence DAG with a priority that
pulls long-latency producers (multiplies) earlier so their consumers
land outside the latency shadow.  Every reorder move is an **adjacent
transposition of two independent statements** — independence = no
read-after-write, write-after-read, or write-after-write hazard between
them.  That is the *only* sound move, and it is exactly the move whose
denotational neutrality we prove below.

## What we prove

1. **Denotation preservation** (`scheduleBlock_denote_eq`): for *any*
   block, `RustExec (blockToCmd (scheduleBlock b)) rs rs' ↔
   RustExec (blockToCmd b) rs rs'`.  Reordering respects data
   dependencies — every move is an adjacent independent swap, whose
   denotational neutrality is `bbSwap_exec_iff` — so the result state is
   identical.  No side condition: the scheduler only ever emits
   `indep`-gated swaps.

2. **CT preservation** (`scheduleBlock_isCT_eq`): `cmdCT (blockToCmd
   (scheduleBlock b)) = cmdCT (blockToCmd b)`.  Scheduling reorders
   public-structure statements and introduces no data-dependent control
   flow, so the constant-time classification (`cmdCT`)
   is invariant.  `cmdCT` of a block is the `&&`-conjunction of the
   per-statement classifications, and `&&` is commutative — so any
   permutation preserves it.

The kernel of both proofs is the **adjacent independent-swap**
commutation lemma (`bbSwap_exec_iff`), proved separately for the scalar
and call statement shapes against `LowCT`'s big-step `RustExec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SchedulerPass

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Basic-block statements

We model the two statement shapes that make up the latency-bound
straight-line code.  A block is a `List BBStmt`; `BBStmt.toCmd` lowers
one statement to a `LowCT`, and `blockToCmd` right-nests a list into
an `RSeq` chain (terminated by `RSkip`). -/

/-- A single straight-line statement in a basic block. -/
inductive BBStmt where
  /-- `x := eval e` — a scalar assignment (`RScalarSetExpr`). -/
  | sset : String → SExpr → BBStmt
  /-- `dst := f(args)` — a leaf call (`RCall`). -/
  | call : String → Located → List Located → BBStmt
  deriving Repr, Inhabited

/-- Lower a basic-block statement to its `LowCT`. -/
def BBStmt.toCmd : BBStmt → LowCT
  | .sset x e     => .RScalarSetExpr x e
  | .call f d as  => .RCall f d as

/-- Right-nest a list of statements into an `RSeq` chain. -/
def blockToCmd : List BBStmt → LowCT
  | []      => .RSkip
  | s :: ss => .RSeq s.toCmd (blockToCmd ss)

/-! ## §2  Dependence model

Each statement has a set of *written* variables (its def) and *read*
variables (its uses).  For the scalar shape, reads are `SExpr.freeVars`
and the write is the assigned scalar.  For the call shape, the write is
the destination slot and the reads are the argument slots (the
dst-threaded ABI also reads `dst`, but `dst` is already the write, so
the WAW/WAR/RAW checks below subsume it).

`indep s1 s2` holds iff `s1` and `s2` have **no hazard**: distinct
writes (no WAW), neither writes what the other reads (no WAR/RAW).
This is a `Bool`, so the scheduler's per-swap independence gate is
`decide`-able and every reorder move is certified at the point it is
made. -/

/-- The variable a statement writes. -/
def BBStmt.writeVar : BBStmt → String
  | .sset x _     => x
  | .call _ d _   => d.locVar

/-- The variables a statement reads. -/
def BBStmt.readVars : BBStmt → List String
  | .sset _ e     => e.freeVars
  | .call _ _ as  => as.map (·.locVar)

/-- Two statements are independent (no RAW / WAR / WAW hazard).  When
    `indep s1 s2 = true`, swapping their adjacent execution order
    preserves `RustExec` (`bbSwap_exec_iff`). -/
def indep (s1 s2 : BBStmt) : Bool :=
  -- WAW: distinct write targets
  (s1.writeVar != s2.writeVar) &&
  -- WAR: s2 must not read what s1 writes
  (s2.readVars.all (fun y => y != s1.writeVar)) &&
  -- RAW: s1 must not read what s2 writes
  (s1.readVars.all (fun y => y != s2.writeVar))

/-! ## §3  Adjacent independent-swap commutation (the kernel lemma)

We prove that two independent adjacent statements commute under
`RustExec`.  This is done per statement shape and assembled into the
generic `bbSwap_exec_iff`.  The proofs against the big-step semantics
use only frame lemmas already in `LowCT.lean` plus expression-eval
invariance. -/

/-! ### §3.1  State-update commutation helpers -/

/-- A write to one var leaves the tower lookup at a different var
    unchanged. -/
theorem locatedUpdate_rsTower_other (rs : RustState) (l : Located)
    (v : RustVal l.locDst) (y : String) (h : y ≠ l.locVar) :
    (locatedUpdate rs l v).rsTower y = rs.rsTower y := by
  unfold locatedUpdate rsSetTower; simp only []
  have : (y == l.locVar) = false := beq_eq_false_iff_ne.mpr h
  simp [this]

/-- `filterMap`-collected arg values are invariant under a write to a
    var disjoint from the args. -/
theorem filterMap_tower_invariant (rs : RustState) (l : Located)
    (v : RustVal l.locDst) (args : List Located)
    (h : ∀ a ∈ args, a.locVar ≠ l.locVar) :
    args.filterMap (fun a => (locatedUpdate rs l v).rsTower a.locVar)
  = args.filterMap (fun a => rs.rsTower a.locVar) := by
  apply List.filterMap_congr; intro a ha
  rw [locatedUpdate_rsTower_other rs l v a.locVar (h a ha)]

/-- Two tower writes to distinct vars commute. -/
theorem locatedUpdate_comm (rs : RustState) (l1 l2 : Located)
    (v1 : RustVal l1.locDst) (v2 : RustVal l2.locDst)
    (h : l1.locVar ≠ l2.locVar) :
    locatedUpdate (locatedUpdate rs l1 v1) l2 v2
  = locatedUpdate (locatedUpdate rs l2 v2) l1 v1 := by
  unfold locatedUpdate rsSetTower
  simp only [RustState.mk.injEq, and_true]; funext y
  by_cases hy1 : (y == l1.locVar) = true <;> by_cases hy2 : (y == l2.locVar) = true <;>
    simp_all [beq_iff_eq]

/-- A tower write to one var leaves the `locatedLookup` at a different
    var unchanged. -/
theorem locatedLookup_update_other (rs : RustState) (l1 l2 : Located)
    (v : RustVal l1.locDst) (h : l1.locVar ≠ l2.locVar) :
    locatedLookup (locatedUpdate rs l1 v) l2 = locatedLookup rs l2 := by
  unfold locatedUpdate
  exact locatedLookup_rsSetTower_other rs l1.locVar ⟨l1.locDst, v⟩ l2 h

/-- Two scalar writes to distinct vars commute. -/
theorem rsSetScalar_comm (rs : RustState) (x1 x2 : String) (v1 v2 : Nat)
    (h : x1 ≠ x2) :
    rsSetScalar (rsSetScalar rs x1 v1) x2 v2
  = rsSetScalar (rsSetScalar rs x2 v2) x1 v1 := by
  unfold rsSetScalar; simp only [RustState.mk.injEq, true_and]; funext y
  by_cases hy1 : (y == x1) = true <;> by_cases hy2 : (y == x2) = true <;>
    simp_all [beq_iff_eq]

/-- A scalar write to one var leaves the scalar read at a different var
    unchanged. -/
theorem rsSetScalar_other (rs : RustState) (x y : String) (v : Nat)
    (h : y ≠ x) :
    (rsSetScalar rs x v).rsScalar y = rs.rsScalar y := by
  unfold rsSetScalar; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr h
  simp [this]

/-- `SExpr.eval` depends only on the expression's free variables. -/
theorem SExpr.eval_eq_of_agree (σ1 σ2 : String → Nat) :
    ∀ (e : SExpr), (∀ y ∈ e.freeVars, σ1 y = σ2 y) → e.eval σ1 = e.eval σ2 := by
  intro e
  induction e with
  | SVar x => intro h; simp [SExpr.eval, SExpr.freeVars] at *; exact h
  | SLit n => intro _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SShr a b iha ihb
  | SShl a b iha ihb | SAnd a b iha ihb | SXor a b iha ihb | SLt a b iha ihb
  | SAsr a b iha ihb | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
      intro h; simp only [SExpr.freeVars, List.mem_append] at h
      simp only [SExpr.eval, iha (fun y hy => h y (Or.inl hy)),
        ihb (fun y hy => h y (Or.inr hy))]
  -- Tower-limb read extension: the SCALAR `eval` returns the constant
  -- `0` for `SLimb` (it cannot read the tower heap), so the value is the same
  -- on any two scalar environments.
  | SLimb v i => intro _; rfl

/-- `SExpr.evalState` depends only on the scalar and tower heaps at the
    expression's free variables: a scalar read `SVar x` uses `rsScalar x`, a
    limb read `SLimb v i` uses `rsTower v`. -/
theorem SExpr.evalState_eq_of_agree (rs1 rs2 : RustState) :
    ∀ (e : SExpr), (∀ y ∈ e.freeVars,
        rs1.rsScalar y = rs2.rsScalar y ∧ rs1.rsTower y = rs2.rsTower y) →
      e.evalState rs1 = e.evalState rs2 := by
  intro e
  induction e with
  | SVar x => intro h; exact (h x (by simp [SExpr.freeVars])).1
  | SLit n => intro _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SShr a b iha ihb
  | SShl a b iha ihb | SAnd a b iha ihb | SXor a b iha ihb | SLt a b iha ihb
  | SAsr a b iha ihb | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
      intro h; simp only [SExpr.freeVars, List.mem_append] at h
      simp only [SExpr.evalState, iha (fun y hy => h y (Or.inl hy)),
        ihb (fun y hy => h y (Or.inr hy))]
  | SLimb v i =>
      intro h
      simp only [SExpr.evalState, rsTowerLimb, (h v (by simp [SExpr.freeVars])).2]

/-- A scalar write outside the free variables of `e` leaves `e.evalState`
    unchanged. -/
theorem SExpr.evalState_rsSetScalar_of_not_mem (rs : RustState) (x : String) (v : Nat)
    (e : SExpr) (hx : x ∉ e.freeVars) :
    e.evalState (rsSetScalar rs x v) = e.evalState rs :=
  SExpr.evalState_eq_of_agree _ _ e fun y hy =>
    ⟨rsSetScalar_other rs x y v (fun hc => hx (hc ▸ hy)), rfl⟩

/-- A tower write outside the free variables of `e` leaves `e.evalState`
    unchanged. -/
theorem SExpr.evalState_locatedUpdate_of_not_mem (rs : RustState) (l : Located)
    (w : RustVal l.locDst) (e : SExpr) (hl : l.locVar ∉ e.freeVars) :
    e.evalState (locatedUpdate rs l w) = e.evalState rs :=
  SExpr.evalState_eq_of_agree _ _ e fun y hy =>
    ⟨rfl, locatedUpdate_rsTower_other rs l w y (fun hc => hl (hc ▸ hy))⟩

/-! ### §3.2 Per-shape commutation (forward direction) -/

/-- Two independent scalar assignments commute (forward direction). -/
theorem scalar_scalar_comm_fwd (N : Nat) (leafSpec : LeafSpec)
    (x1 x2 : String) (e1 e2 : SExpr) (rs rs' : RustState)
    (hWAW : x1 ≠ x2) (hWAR : x2 ∉ e1.freeVars) (hRAW : x1 ∉ e2.freeVars)
    (hExec : RustExec N leafSpec
      (.RSeq (.RScalarSetExpr x1 e1) (.RScalarSetExpr x2 e2)) rs rs') :
    RustExec N leafSpec
      (.RSeq (.RScalarSetExpr x2 e2) (.RScalarSetExpr x1 e1)) rs rs' := by
  cases hExec with
  | seq _ _ _ rmid _ h1 h2 =>
    cases h1; cases h2
    have he2 : e2.evalState (rsSetScalar rs x1 (e1.evalState rs)) = e2.evalState rs :=
      SExpr.evalState_rsSetScalar_of_not_mem rs x1 _ e2 hRAW
    have he1 : e1.evalState (rsSetScalar rs x2 (e2.evalState rs)) = e1.evalState rs :=
      SExpr.evalState_rsSetScalar_of_not_mem rs x2 _ e1 hWAR
    refine RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr x2 e2 rs) ?_
    rw [he2]
    have hc := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) x1 e1
      (rsSetScalar rs x2 (e2.evalState rs))
    rw [he1] at hc
    rw [rsSetScalar_comm rs x1 x2 _ _ hWAW] at *
    convert hc using 2

/-- Two independent leaf calls commute (forward direction). -/
theorem call_call_comm_fwd (N : Nat) (leafSpec : LeafSpec)
    (f1 f2 : String) (d1 d2 : Located) (a1 a2 : List Located)
    (rs rs' : RustState)
    (hWAW : d1.locVar ≠ d2.locVar)
    (hWAR : ∀ a ∈ a1, a.locVar ≠ d2.locVar)
    (hRAW : ∀ a ∈ a2, a.locVar ≠ d1.locVar)
    (hExec : RustExec N leafSpec
      (.RSeq (.RCall f1 d1 a1) (.RCall f2 d2 a2)) rs rs') :
    RustExec N leafSpec (.RSeq (.RCall f2 d2 a2) (.RCall f1 d1 a1)) rs rs' := by
  cases hExec with
  | seq _ _ _ rmid _ h1 h2 =>
    cases h1 with
    | call _ _ _ _ oldD1 argL1 hLook1 hargL1 hTy1 =>
      cases h2 with
      | call _ _ _ _ oldD2 argL2 hLook2 hargL2 hTy2 =>
        set v1 := leafSpec.call f1 d1.locDst (List.map (fun x => x.locDst) a1) oldD1 argL1
          with hv1
        have hLook2' : locatedLookup rs d2 = some oldD2 := by
          rw [← hLook2]; exact (locatedLookup_update_other rs d1 d2 v1 hWAW).symm
        have hargL2' : argL2 = a2.filterMap (fun a => rs.rsTower a.locVar) := by
          rw [hargL2]; exact filterMap_tower_invariant rs d1 v1 a2 hRAW
        have hTy2' : ∀ a ∈ a2, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
          intro a ha; have := hTy2 a ha
          rwa [locatedUpdate_rsTower_other rs d1 v1 a.locVar (hRAW a ha)] at this
        set v2 := leafSpec.call f2 d2.locDst (List.map (fun x => x.locDst) a2) oldD2 argL2
          with hv2
        have hStep2 : RustExec N leafSpec (.RCall f2 d2 a2) rs (locatedUpdate rs d2 v2) := by
          rw [hv2, hargL2']
          exact RustExec.call (N := N) (leafSpec := leafSpec) f2 d2 a2 rs oldD2 _
            hLook2' rfl hTy2'
        set rs2 := locatedUpdate rs d2 v2 with hrs2
        have hLook1' : locatedLookup rs2 d1 = some oldD1 := by
          rw [hrs2, locatedLookup_update_other rs d2 d1 v2 (Ne.symm hWAW)]; exact hLook1
        have hargL1' : argL1 = a1.filterMap (fun a => rs2.rsTower a.locVar) := by
          rw [hrs2, hargL1]; symm; exact filterMap_tower_invariant rs d2 v2 a1 hWAR
        have hTy1' : ∀ a ∈ a1, ∃ v, rs2.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
          intro a ha; have := hTy1 a ha
          rwa [hrs2, locatedUpdate_rsTower_other rs d2 v2 a.locVar (hWAR a ha)]
        have hStep1 : RustExec N leafSpec (.RCall f1 d1 a1) rs2
            (locatedUpdate rs2 d1 v1) := by
          have hc := RustExec.call (N := N) (leafSpec := leafSpec) f1 d1 a1 rs2 oldD1
            (a1.filterMap (fun a => rs2.rsTower a.locVar)) hLook1' rfl hTy1'
          have hval : leafSpec.call f1 d1.locDst (List.map (fun x => x.locDst) a1) oldD1
                        (a1.filterMap (fun a => rs2.rsTower a.locVar)) = v1 := by
            rw [hv1, ← hargL1']
          rw [hval] at hc; exact hc
        have hfinal : locatedUpdate rs2 d1 v1
                    = locatedUpdate (locatedUpdate rs d1 v1) d2 v2 := by
          rw [hrs2]; exact (locatedUpdate_comm rs d1 d2 v1 v2 hWAW).symm
        rw [← hfinal]
        exact RustExec.seq _ _ _ _ _ hStep2 hStep1

/-! ### §3.2b  Mixed-shape commutation

`RScalarSetExpr` writes only the **scalar** heap and `RCall` writes only the
**tower** heap, so the two writes commute as states.  The scalar expression may
read the tower heap through `SLimb v i`, whose free variable is the slot `v`;
the assignment and the call commute when the call's destination is not a free
variable of the expression, which `indep` supplies (`readVars` of an assignment
is `e.freeVars`). -/

/-- A scalar write and a tower write commute as states. -/
theorem setScalar_update_comm (rs : RustState) (x : String) (v : Nat)
    (l : Located) (w : RustVal l.locDst) :
    locatedUpdate (rsSetScalar rs x v) l w = rsSetScalar (locatedUpdate rs l w) x v := by
  unfold locatedUpdate rsSetTower rsSetScalar; rfl

/-- Scalar-assignment then call commutes to call then scalar-assignment. -/
theorem scalar_call_comm_fwd (N : Nat) (leafSpec : LeafSpec) (x : String) (e : SExpr)
    (f : String) (d : Located) (as : List Located) (rs rs' : RustState)
    (hRAW : d.locVar ∉ e.freeVars)
    (hExec : RustExec N leafSpec (.RSeq (.RScalarSetExpr x e) (.RCall f d as)) rs rs') :
    RustExec N leafSpec (.RSeq (.RCall f d as) (.RScalarSetExpr x e)) rs rs' := by
  cases hExec with
  | seq _ _ _ rmid _ h1 h2 =>
    cases h1
    cases h2 with
    | call _ _ _ _ oldD argL hLook hargL hTy =>
      set ev := e.evalState rs with hev
      have hLook' : locatedLookup rs d = some oldD := by
        rw [← hLook]; exact (locatedLookup_rsSetScalar rs x ev d).symm
      have hStepC : RustExec N leafSpec (.RCall f d as) rs
          (locatedUpdate rs d
            (leafSpec.call f d.locDst (List.map (fun x => x.locDst) as) oldD argL)) := by
        rw [hargL]
        exact RustExec.call (N := N) (leafSpec := leafSpec) f d as rs oldD _ hLook' rfl hTy
      set w := leafSpec.call f d.locDst (List.map (fun x => x.locDst) as) oldD argL with hw
      refine RustExec.seq _ _ _ _ _ hStepC ?_
      have hc := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) x e
        (locatedUpdate rs d w)
      rw [SExpr.evalState_locatedUpdate_of_not_mem rs d w e hRAW, ← hev] at hc
      rw [setScalar_update_comm rs x ev d w] at *
      convert hc using 1

/-- Call then scalar-assignment commutes to scalar-assignment then call. -/
theorem call_scalar_comm_fwd (N : Nat) (leafSpec : LeafSpec)
    (f : String) (d : Located) (as : List Located) (x : String) (e : SExpr)
    (rs rs' : RustState)
    (hRAW : d.locVar ∉ e.freeVars)
    (hExec : RustExec N leafSpec (.RSeq (.RCall f d as) (.RScalarSetExpr x e)) rs rs') :
    RustExec N leafSpec (.RSeq (.RScalarSetExpr x e) (.RCall f d as)) rs rs' := by
  cases hExec with
  | seq _ _ _ rmid _ h1 h2 =>
    cases h1 with
    | call _ _ _ _ oldD argL hLook hargL hTy =>
      cases h2
      set w := leafSpec.call f d.locDst (List.map (fun x => x.locDst) as) oldD argL with hw
      have hStepS : RustExec N leafSpec (.RScalarSetExpr x e) rs
          (rsSetScalar rs x (e.evalState rs)) := RustExec.scalarSetExpr x e rs
      set ev := e.evalState rs with hev
      set rsS := rsSetScalar rs x ev with hrsS
      refine RustExec.seq _ _ _ _ _ hStepS ?_
      have hLook' : locatedLookup rsS d = some oldD := by
        rw [hrsS, locatedLookup_rsSetScalar rs x ev d]; exact hLook
      have hargL' : argL = as.filterMap (fun a => rsS.rsTower a.locVar) := by
        rw [hrsS]; exact hargL
      have hTy' : ∀ a ∈ as, ∃ ww, rsS.rsTower a.locVar = some ⟨a.locDst, ww⟩ := by
        rw [hrsS]; exact hTy
      have hStepC := RustExec.call (N := N) (leafSpec := leafSpec) f d as rsS oldD
        (as.filterMap (fun a => rsS.rsTower a.locVar)) hLook' rfl hTy'
      have hval : leafSpec.call f d.locDst (List.map (fun x => x.locDst) as) oldD
                    (as.filterMap (fun a => rsS.rsTower a.locVar)) = w := by
        rw [hw, ← hargL']
      rw [hval] at hStepC
      rw [SExpr.evalState_locatedUpdate_of_not_mem rs d w e hRAW, ← hev]
      rw [hrsS] at hStepC
      rw [setScalar_update_comm rs x ev d w] at hStepC
      rw [hrsS]; exact hStepC

/-! ### §3.3  Bridging `indep` to the per-shape hypotheses -/

/-- `indep` unfolded into the three hazard-free conjuncts (as Props). -/
theorem indep_iff (s1 s2 : BBStmt) :
    indep s1 s2 = true ↔
      (s1.writeVar ≠ s2.writeVar) ∧
      (∀ y ∈ s2.readVars, y ≠ s1.writeVar) ∧
      (∀ y ∈ s1.readVars, y ≠ s2.writeVar) := by
  unfold indep
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · intro y hy; have := h2 y hy; simpa [bne_iff_ne] using this
    · intro y hy; have := h3 y hy; simpa [bne_iff_ne] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · intro y hy; simpa [bne_iff_ne] using h2 y hy
    · intro y hy; simpa [bne_iff_ne] using h3 y hy

/-! ### §3.4  Generic adjacent-swap iff -/

/-- **Adjacent independent-swap commutation.**  If `s1` and `s2` are
    independent (`indep s1 s2 = true`), then executing `s1; s2` and
    `s2; s1` from the same state reaches the same final state.  This is
    the *only* reorder move the scheduler makes; the iff is the
    denotational neutrality the whole pass rests on. -/
theorem bbSwap_exec_iff (N : Nat) (leafSpec : LeafSpec) (s1 s2 : BBStmt)
    (rs rs' : RustState) (h : indep s1 s2 = true) :
    RustExec N leafSpec (.RSeq s1.toCmd s2.toCmd) rs rs'
  ↔ RustExec N leafSpec (.RSeq s2.toCmd s1.toCmd) rs rs' := by
  -- `indep` is symmetric, so each direction is an instance of the
  -- forward per-shape lemma with the roles swapped.  `hRead2` says s2's
  -- reads avoid s1's write; `hRead1` says s1's reads avoid s2's write.
  obtain ⟨hWAW, hRead2, hRead1⟩ := (indep_iff s1 s2).mp h
  constructor
  · intro hexec
    cases s1 with
    | sset x1 e1 => cases s2 with
      | sset x2 e2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        -- need: x2 ∉ e1.freeVars (hRead1: e1=s1.reads, x2=s2.write),
        --       x1 ∉ e2.freeVars (hRead2: e2=s2.reads, x1=s1.write)
        refine scalar_scalar_comm_fwd N leafSpec x1 x2 e1 e2 rs rs'
          (by simpa [BBStmt.writeVar] using hWAW)
          (fun hc => hRead1 x2 (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar]))
          (fun hc => hRead2 x1 (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar])) hexec
      | call f2 d2 a2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        exact scalar_call_comm_fwd N leafSpec x1 e1 f2 d2 a2 rs rs'
          (fun hc => hRead1 d2.locVar (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar])) hexec
    | call f1 d1 a1 => cases s2 with
      | sset x2 e2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        exact call_scalar_comm_fwd N leafSpec f1 d1 a1 x2 e2 rs rs'
          (fun hc => hRead2 d1.locVar (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar])) hexec
      | call f2 d2 a2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        refine call_call_comm_fwd N leafSpec f1 f2 d1 d2 a1 a2 rs rs'
          (by simpa [BBStmt.writeVar] using hWAW) ?_ ?_ hexec
        · intro a ha
          have := hRead1 a.locVar (by simp only [BBStmt.readVars, List.mem_map]; exact ⟨a, ha, rfl⟩)
          simpa [BBStmt.writeVar] using this
        · intro a ha
          have := hRead2 a.locVar (by simp only [BBStmt.readVars, List.mem_map]; exact ⟨a, ha, rfl⟩)
          simpa [BBStmt.writeVar] using this
  · intro hexec
    cases s1 with
    | sset x1 e1 => cases s2 with
      | sset x2 e2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        refine scalar_scalar_comm_fwd N leafSpec x2 x1 e2 e1 rs rs'
          (by simpa [BBStmt.writeVar] using (Ne.symm hWAW))
          (fun hc => hRead2 x1 (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar]))
          (fun hc => hRead1 x2 (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar])) hexec
      | call f2 d2 a2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        exact call_scalar_comm_fwd N leafSpec f2 d2 a2 x1 e1 rs rs'
          (fun hc => hRead1 d2.locVar (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar])) hexec
    | call f1 d1 a1 => cases s2 with
      | sset x2 e2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        exact scalar_call_comm_fwd N leafSpec x2 e2 f1 d1 a1 rs rs'
          (fun hc => hRead2 d1.locVar (by simpa [BBStmt.readVars] using hc)
            (by simp [BBStmt.writeVar])) hexec
      | call f2 d2 a2 =>
        simp only [BBStmt.toCmd] at hexec ⊢
        refine call_call_comm_fwd N leafSpec f2 f1 d2 d1 a2 a1 rs rs'
          (by simpa [BBStmt.writeVar] using (Ne.symm hWAW)) ?_ ?_ hexec
        · intro a ha
          have := hRead2 a.locVar (by simp only [BBStmt.readVars, List.mem_map]; exact ⟨a, ha, rfl⟩)
          simpa [BBStmt.writeVar] using this
        · intro a ha
          have := hRead1 a.locVar (by simp only [BBStmt.readVars, List.mem_map]; exact ⟨a, ha, rfl⟩)
          simpa [BBStmt.writeVar] using this

/-! ## §4  Lifting the swap to a whole block

`blockToCmd` of a list is a right-nested `RSeq` chain.  We lift the
adjacent swap from §3 first to the head of a suffix, then to an
arbitrary position inside a prefix context, by induction. -/

/-- Peel the head of a `blockToCmd` chain. -/
theorem block_cons_iff (N : Nat) (leafSpec : LeafSpec) (s : BBStmt)
    (ss : List BBStmt) (rs rs' : RustState) :
    RustExec N leafSpec (blockToCmd (s :: ss)) rs rs'
  ↔ ∃ m, RustExec N leafSpec s.toCmd rs m
       ∧ RustExec N leafSpec (blockToCmd ss) m rs' := by
  simp only [blockToCmd]
  constructor
  · intro h; cases h with | seq _ _ _ m _ h1 h2 => exact ⟨m, h1, h2⟩
  · rintro ⟨m, h1, h2⟩; exact RustExec.seq _ _ _ _ _ h1 h2

/-- Swapping the first two statements of a block (when independent)
    preserves `RustExec`. -/
theorem block_swap_head (N : Nat) (leafSpec : LeafSpec) (s1 s2 : BBStmt)
    (post : List BBStmt) (rs rs' : RustState) (h : indep s1 s2 = true) :
    RustExec N leafSpec (blockToCmd (s1 :: s2 :: post)) rs rs'
  ↔ RustExec N leafSpec (blockToCmd (s2 :: s1 :: post)) rs rs' := by
  rw [block_cons_iff, block_cons_iff]
  constructor
  · rintro ⟨m1, hs1, hrest⟩
    rw [block_cons_iff] at hrest; obtain ⟨m2, hs2, hpost⟩ := hrest
    have hpair' :=
      (bbSwap_exec_iff N leafSpec s1 s2 rs m2 h).mp (RustExec.seq _ _ _ _ _ hs1 hs2)
    cases hpair' with | seq _ _ _ m _ hs2' hs1' =>
      exact ⟨m, hs2', by rw [block_cons_iff]; exact ⟨m2, hs1', hpost⟩⟩
  · rintro ⟨m1, hs2, hrest⟩
    rw [block_cons_iff] at hrest; obtain ⟨m2, hs1, hpost⟩ := hrest
    have hpair' :=
      (bbSwap_exec_iff N leafSpec s1 s2 rs m2 h).mpr (RustExec.seq _ _ _ _ _ hs2 hs1)
    cases hpair' with | seq _ _ _ m _ hs1' hs2' =>
      exact ⟨m, hs1', by rw [block_cons_iff]; exact ⟨m2, hs2', hpost⟩⟩

/-! ## §5  Latency-aware list scheduler

The concrete scheduler performs a **selection by latency priority over
the ready set**, realized as iterated left-bubble passes of adjacent
*independent* swaps.  In one `bubble` pass we scan the block; for each
adjacent pair `(s1, s2)` where `s2` is a longer-latency producer
(`latencyPrio s1 < latencyPrio s2`) **and** independent of `s1`, we swap
them — pulling the long-latency op earlier so its consumers land outside
its latency shadow.  Every swap is gated by `indep`, so each pass (and
hence the whole schedule) is denotationally neutral (`bubble_exec_iff`,
`scheduleBlock_denote_eq`).

`latencyPrio` is a producer-latency estimate (higher = longer latency =
schedule earlier).  Correctness does **not** depend on the numbers being
exact — only the ILP win does; the denotation/CT theorems hold for *any*
priority. -/

/-- Producer-latency estimate (x86-64 Zen/Skylake ballpark).  Higher =
    longer latency = scheduled earlier.  Used only as the priority; the
    correctness theorems are independent of these numbers. -/
def latencyPrio : BBStmt → Nat
  | .sset _ e =>
      match e with
      | .SMulHiS _ _ => 4   -- #IMUL high word (signed wide multiply)
      | .SMulHiU _ _ => 4   -- #MULX high word
      | .SMul _ _    => 3
      | .SMulS _ _   => 3
      | _            => 1   -- add / shift / logical (≈1 cycle)
  | .call _ _ _ => 3        -- leaf call: assume a few cycles

/-- One left-bubble pass.  At each adjacent pair, pull the longer-latency
    `s2` ahead of `s1` when they are independent.  Structural recursion on
    the list. -/
def bubble : List BBStmt → List BBStmt
  | []  => []
  | [s] => [s]
  | s1 :: s2 :: rest =>
      if indep s1 s2 && (latencyPrio s1 < latencyPrio s2) then
        s2 :: bubble (s1 :: rest)
      else
        s1 :: bubble (s2 :: rest)

/-- **One bubble pass is denotationally neutral.**  Each swap it performs
    is gated by `indep`, so it reduces to `block_swap_head`. -/
theorem bubble_exec_iff (N : Nat) (leafSpec : LeafSpec) :
    ∀ (b : List BBStmt) (rs rs' : RustState),
      (RustExec N leafSpec (blockToCmd (bubble b)) rs rs'
     ↔ RustExec N leafSpec (blockToCmd b) rs rs') := by
  intro b
  induction b using bubble.induct with
  | case1 => intro rs rs'; simp only [bubble]
  | case2 s => intro rs rs'; simp only [bubble]
  | case3 s1 s2 rest hcond ih =>
    intro rs rs'
    have hindep : indep s1 s2 = true := by
      have := hcond; simp only [Bool.and_eq_true] at this; exact this.1
    simp only [bubble, ite_eq_left hcond]
    rw [block_cons_iff]
    constructor
    · rintro ⟨m, hs2, hr⟩
      rw [ih] at hr
      rw [block_cons_iff] at hr; obtain ⟨m2, hs1, hpost⟩ := hr
      have hback : RustExec N leafSpec (blockToCmd (s2 :: s1 :: rest)) rs rs' := by
        rw [block_cons_iff]; exact ⟨m, hs2, by rw [block_cons_iff]; exact ⟨m2, hs1, hpost⟩⟩
      exact (block_swap_head N leafSpec s1 s2 rest rs rs' hindep).mpr hback
    · intro hexec
      have hsw := (block_swap_head N leafSpec s1 s2 rest rs rs' hindep).mp hexec
      rw [block_cons_iff] at hsw; obtain ⟨m, hs2, hr⟩ := hsw
      exact ⟨m, hs2, by rw [ih]; exact hr⟩
  | case4 s1 s2 rest hcond ih =>
    intro rs rs'
    simp only [bubble, ite_eq_right hcond]
    rw [block_cons_iff, block_cons_iff]
    constructor
    · rintro ⟨m, hs1, hr⟩; exact ⟨m, hs1, (ih m rs').mp hr⟩
    · rintro ⟨m, hs1, hr⟩; exact ⟨m, hs1, (ih m rs').mpr hr⟩

/-- Iterate `bubble` `k` times.  `k = length` suffices to drive every
    independent producer as far left as the dependence DAG allows. -/
def bubbleN : Nat → List BBStmt → List BBStmt
  | 0,     b => b
  | k + 1, b => bubbleN k (bubble b)

/-- Iterating `bubble` stays denotationally neutral. -/
theorem bubbleN_exec_iff (N : Nat) (leafSpec : LeafSpec) :
    ∀ (k : Nat) (b : List BBStmt) (rs rs' : RustState),
      (RustExec N leafSpec (blockToCmd (bubbleN k b)) rs rs'
     ↔ RustExec N leafSpec (blockToCmd b) rs rs') := by
  intro k
  induction k with
  | zero => intro b rs rs'; rfl
  | succ k ih =>
    intro b rs rs'
    simp only [bubbleN]
    rw [ih (bubble b) rs rs', bubble_exec_iff N leafSpec b rs rs']

/-- **The scheduler.**  Reorder a basic block for ILP by `length`-many
    latency-priority bubble passes.  Every move is an adjacent
    independent swap, so the result is denotationally equal to the input
    (`scheduleBlock_denote_eq`). -/
def scheduleBlock (b : List BBStmt) : List BBStmt :=
  bubbleN b.length b

/-! ## §6  Denotation preservation (the correctness obligation)

The headline result: scheduling a block does not change what it
computes.  `(scheduleBlock b).denote = b.denote`, phrased over the
big-step `RustExec` relation as the other passes phrase theirs. -/

/-- **Denotation preservation.**  Scheduling preserves the big-step
    semantics: the scheduled block reaches exactly the same final states
    as the original from any start state.  This is the correctness
    obligation — reordering respects all data dependencies. -/
theorem scheduleBlock_denote_eq (N : Nat) (leafSpec : LeafSpec)
    (b : List BBStmt) (rs rs' : RustState) :
    RustExec N leafSpec (blockToCmd (scheduleBlock b)) rs rs'
  ↔ RustExec N leafSpec (blockToCmd b) rs rs' := by
  unfold scheduleBlock
  exact bubbleN_exec_iff N leafSpec b.length b rs rs'

/-! ## §7  Constant-time preservation

`cmdCT` of a `blockToCmd` chain is the `&&`-conjunction of the
per-statement classifications.  A single adjacent swap reorders the
conjunction; `&&` is commutative/associative, so the classification is
invariant.  Hence one bubble pass — and the whole schedule — preserves
`cmdCT`. -/

/-- `cmdCT` of a block reduces to the `&&` of per-statement `cmdCT`s.
    (`RScalarSetExpr` and `RCall` both have a flat `cmdCT` arm, and
    `RSkip` is `true`.) -/
theorem cmdCT_blockToCmd (lt : LevelTable) (leafCT : LeafCTTable) :
    ∀ (b : List BBStmt),
      cmdCT (blockToCmd b) lt leafCT
    = b.all (fun s => cmdCT s.toCmd lt leafCT) := by
  intro b
  induction b with
  | nil => simp [blockToCmd, cmdCT_RSkip]
  | cons s ss ih =>
    simp only [blockToCmd, cmdCT_RSeq, List.all_cons, ih]

/-- One bubble pass preserves the per-statement multiset, hence the
    `cmdCT` conjunction. -/
theorem bubble_cmdCT_eq (lt : LevelTable) (leafCT : LeafCTTable) :
    ∀ (b : List BBStmt),
      cmdCT (blockToCmd (bubble b)) lt leafCT
    = cmdCT (blockToCmd b) lt leafCT := by
  intro b
  induction b using bubble.induct with
  | case1 => simp only [bubble]
  | case2 s => simp only [bubble]
  | case3 s1 s2 rest hcond ih =>
    -- bubble (s1::s2::rest) = s2 :: bubble (s1::rest)
    simp only [bubble, ite_eq_left hcond]
    rw [cmdCT_blockToCmd, cmdCT_blockToCmd] at ih ⊢
    simp only [List.all_cons] at ih ⊢
    rw [ih]; ac_rfl
  | case4 s1 s2 rest hcond ih =>
    simp only [bubble, ite_eq_right hcond]
    rw [cmdCT_blockToCmd, cmdCT_blockToCmd] at ih ⊢
    simp only [List.all_cons] at ih ⊢
    rw [ih]

/-- **CT preservation.**  Scheduling preserves the constant-time
    classification: `cmdCT (scheduleBlock b) = cmdCT b`.  Reordering
    public-structure statements introduces no data-dependent control
    flow, so the leak-trace classification is invariant. -/
theorem scheduleBlock_isCT_eq (lt : LevelTable) (leafCT : LeafCTTable)
    (b : List BBStmt) :
    cmdCT (blockToCmd (scheduleBlock b)) lt leafCT
  = cmdCT (blockToCmd b) lt leafCT := by
  unfold scheduleBlock
  suffices h : ∀ (k : Nat) (b : List BBStmt),
      cmdCT (blockToCmd (bubbleN k b)) lt leafCT
    = cmdCT (blockToCmd b) lt leafCT by
    exact h b.length b
  intro k
  induction k with
  | zero => intro b; rfl
  | succ k ih => intro b; simp only [bubbleN]; rw [ih (bubble b), bubble_cmdCT_eq lt leafCT b]

end CatCrypt.Crypto.Optimizer.SchedulerPass
