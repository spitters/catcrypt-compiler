/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak
public import CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak

/-!
# Flow-sensitive constant-time analysis for `LowCT`

The syntactic checker `cmdCT` (`LowCTCTAnalysis.lean`) is **flow-insensitive**:
it takes a caller-supplied *closed* `LevelTable` — one `.Public`/`.Secret`
label per variable name for the whole program — and rejects
`RScalarSetExpr x e` whenever `e` reads any `.Secret` slot, because a
flow-insensitive table cannot record that `x` is public *after* an
overwrite.  A register that holds a secret and is later overwritten with a
public value is therefore rejected even when the later use is constant-time.

`cmdCTFlow` **threads** the `LevelTable` through the program.  A scalar
assignment `RScalarSetExpr x e` (and `RScalarSet x _`) *updates*
`label(x)` to the join of the labels `e` reads (public if all reads are
public, else secret) and continues with the updated table.  Branch and loop
guards (`RIfNz`/`RWhileNz`) are gated on the **current, propagated** label.
The result is that a variable reclassified public downstream of an
overwrite is accepted as a public guard — the enlargement Vale's
flow-sensitive taint tracking provides.

## What is threaded and what is deferred

`cmdCTFlow` adds flow-sensitivity precisely to the straight-line + branch
fragment — `RScalarSet`, `RScalarSetExpr`, `RSeq`, `RBlock`, `RLetU64Zero`,
`RLetZero`, `RIfNz`.  Every other constructor (leaf calls, array
load/store, and the `RWhileNz`/`RFor`/`RFnDef` loop/definition nodes) falls
back to the flow-insensitive `cmdCT` check on the *current* table and
returns that table unchanged.  This is sound: those constructors never write
a scalar guard with a secret value once `cmdCT` accepts them (an
`RScalarSetExpr` reading a secret is rejected by `cmdCT`), so the
propagated scalar classification is preserved.

The scalar-relevant state transition is `flowStep`; the flow-sensitive
dynamic trace is `dynLeakTraceF`, which — unlike the sequential clause of
`dynLeakTrace` — evaluates the second component of an `RSeq` at the state
*reached* by the first (`flowStep c1 rs`), so a guard downstream of a
reassignment is read after the reassignment.  Loops are treated exactly as
in `dynLeakTrace`: a static node here, with the iteration-count leakage
carried by the separate `dynLeakTraceWhile` + `BodyStepPreservesPublic` model
(`LowCTVartimeLeak.lean`).

## Soundness

`cmdCTFlow_sound`: if `cmdCTFlow c lt leafCT = some lt'` and the two input
states are scalar-public-equivalent under `lt`, then the flow-sensitive
dynamic leak traces are equal, and the output states are scalar-public-
equivalent under the output table `lt'`.  The `RScalarSetExpr` inductive
step (`scalarPublicEquiv_setScalarExpr`) is the crux: overwriting `x` with a
public-valued expression re-establishes the invariant under the reclassified
table.

`cmdCTFlow_noninterference` restates the trace half against the ambient
`PublicEquiv` used by `dynLeakTrace_noninterference`, so the flow-sensitive
checker delivers the same noninterference-modulo-public conclusion.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.LowCTFlowCT

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace
open CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak

set_option autoImplicit false

/-! ## §1. Table update and expression level -/

/-- Update one slot's classification, leaving the rest of the table intact. -/
def updLevel (lt : LevelTable) (x : String) (l : SecretLevel) : LevelTable :=
  fun y => if y = x then l else lt y

/-- The classification of an expression's value: `.Public` iff every slot it
reads is public (i.e. `SExpr.isPublic`), else `.Secret`.  This is the join,
over `e`'s free variables, of their current labels. -/
def exprLevel (lt : LevelTable) (e : SExpr) : SecretLevel :=
  if e.isPublic lt then .Public else .Secret

theorem exprLevel_public_iff (lt : LevelTable) (e : SExpr) :
    exprLevel lt e = .Public ↔ e.isPublic lt = true := by
  unfold exprLevel
  by_cases h : e.isPublic lt = true <;> simp [h]

/-! ## §2. The flow-sensitive checker -/

/-- Flow-sensitive constant-time checker.  Threads the `LevelTable`: scalar
assignments reclassify their target, branch/loop guards are gated on the
current propagated table, and the final table is returned (`none` on a
violation).  Constructors outside the threaded fragment defer to the
flow-insensitive `cmdCT` on the current table and return it unchanged. -/
def cmdCTFlow : LowCT → LevelTable → LeafCTTable → Option LevelTable
  | .RScalarSet x _, lt, _ => some (updLevel lt x .Public)
  | .RScalarSetExpr x e, lt, _ => some (updLevel lt x (exprLevel lt e))
  | .RSeq c1 c2, lt, leafCT =>
      match cmdCTFlow c1 lt leafCT with
      | some lt1 => cmdCTFlow c2 lt1 leafCT
      | none => none
  | .RBlock body, lt, leafCT => cmdCTFlow body lt leafCT
  | .RLetU64Zero x body, lt, leafCT => cmdCTFlow body (updLevel lt x .Public) leafCT
  | .RLetZero _ _ body, lt, leafCT => cmdCTFlow body lt leafCT
  | .RIfNz cond ct cf, lt, leafCT =>
      if lt cond == .Public then
        match cmdCTFlow ct lt leafCT, cmdCTFlow cf lt leafCT with
        | some lt1, some lt2 => some (fun v => (lt1 v).join (lt2 v))
        | _, _ => none
      else none
  | c, lt, leafCT => if cmdCT c lt leafCT then some lt else none

/-! ## §3. The scalar-relevant state transition -/

/-- The scalar projection of one command's effect.  Scalar guards read
`rsScalar`, and only `RScalarSet`/`RScalarSetExpr`/`RLetU64Zero` write it;
every other constructor leaves `rsScalar` unchanged (leaf calls and tower
ops write `rsTower`).  `flowStep` therefore tracks exactly the scalar slots a
guard can observe.  Loops are the identity here, matching `dynLeakTraceF`
(their iteration leakage is modelled by `dynLeakTraceWhile`). -/
def flowStep : LowCT → RustState → RustState
  | .RScalarSet x n, rs => rsSetScalar rs x n
  | .RScalarSetExpr x e, rs => rsSetScalar rs x (e.eval rs.rsScalar)
  | .RSeq c1 c2, rs => flowStep c2 (flowStep c1 rs)
  | .RBlock body, rs => flowStep body rs
  | .RLetU64Zero x body, rs => flowStep body (rsSetScalar rs x 0)
  | .RLetZero _ _ body, rs => flowStep body rs
  | .RIfNz cond ct cf, rs =>
      if guardBit rs cond then flowStep ct rs else flowStep cf rs
  | _, rs => rs

/-! ## §4. The flow-sensitive dynamic leak trace -/

/-- Flow-sensitive dynamic leak trace.  Coincides with `dynLeakTrace` on
`RIfNz`/`RBlock`/the data-oblivious constructors, but the sequential clause
threads state: the second command's trace is taken at `flowStep c1 rs`, so a
guard downstream of a reassignment is read *after* the reassignment. -/
def dynLeakTraceF : LowCT → RustState → LeakTrace
  | .RIfNz cond ct cf, rs =>
      if guardBit rs cond
      then branchEvent true :: dynLeakTraceF ct rs
      else branchEvent false :: dynLeakTraceF cf rs
  | .RSeq c1 c2, rs => dynLeakTraceF c1 rs ++ dynLeakTraceF c2 (flowStep c1 rs)
  | .RBlock body, rs => dynLeakTraceF body rs
  | .RLetU64Zero x body, rs => dynLeakTraceF body (rsSetScalar rs x 0)
  | .RLetZero _ _ body, rs => dynLeakTraceF body rs
  | c, _ => LowCT.leakTrace c

/-! ## §5. Scalar public equivalence -/

/-- Two states agree on every public-classified *scalar* slot.  This is the
projection of `PublicEquiv` onto the scalar heap — exactly what a scalar
guard can observe — and it is the invariant threaded by the flow-sensitive
analysis (reclassifying a scalar slot cannot be tracked by the unified
`PublicEquiv`, whose tower clause a scalar overwrite does not re-establish). -/
def ScalarPublicEquiv (lt : LevelTable) (rs1 rs2 : RustState) : Prop :=
  ∀ x, lt x = .Public → rs1.rsScalar x = rs2.rsScalar x

theorem PublicEquiv.toScalar {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) : ScalarPublicEquiv lt rs1 rs2 := h.2

/-! ## §6. Expression evaluation depends only on read slots -/

/-- `SExpr.eval` depends only on the slots the expression reads. -/
theorem SExpr.eval_eq_of_agree (e : SExpr) {σ1 σ2 : String → Nat}
    (h : ∀ v, v ∈ e.freeVars → σ1 v = σ2 v) : e.eval σ1 = e.eval σ2 := by
  induction e with
  | SVar x => exact h x (by simp [SExpr.freeVars])
  | SLit n => rfl
  | SLimb v i => rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb
  | SShr a b iha ihb | SShl a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SLt a b iha ihb | SAsr a b iha ihb
  | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
    all_goals (
      have hA := iha (fun v hv => h v (List.mem_append_left _ hv))
      have hB := ihb (fun v hv => h v (List.mem_append_right _ hv))
      simp only [SExpr.eval, hA, hB])

/-- On scalar-public-equivalent states, a public expression evaluates equally. -/
theorem eval_eq_of_isPublic_scalar {lt : LevelTable} {rs1 rs2 : RustState}
    (h : ScalarPublicEquiv lt rs1 rs2) (e : SExpr) (hp : e.isPublic lt = true) :
    e.eval rs1.rsScalar = e.eval rs2.rsScalar := by
  refine SExpr.eval_eq_of_agree e (fun v hv => ?_)
  have : (lt v == SecretLevel.Public) = true := by
    have := (List.all_eq_true.mp hp) v hv
    simpa using this
  exact h v (level_beq_public_iff.mp this)

/-! ## §7. Reclassification preserves scalar public equivalence -/

/-- Setting the same literal on both sides, with the target reclassified
`.Public`, preserves scalar-public-equivalence. -/
theorem scalarPublicEquiv_setScalar {lt : LevelTable} {rs1 rs2 : RustState}
    (h : ScalarPublicEquiv lt rs1 rs2) (x : String) (n : Nat) :
    ScalarPublicEquiv (updLevel lt x .Public)
      (rsSetScalar rs1 x n) (rsSetScalar rs2 x n) := by
  intro y hy
  unfold rsSetScalar
  by_cases hxy : y = x
  · subst hxy; simp
  · simp only [beq_eq_false_iff_ne.mpr hxy]
    have : lt y = .Public := by
      unfold updLevel at hy; simpa [hxy] using hy
    exact h y this

/-- Setting the same fixed value `v` on both sides, with the target
reclassified `.Public`, preserves scalar-public-equivalence. -/
theorem scalarPublicEquiv_setScalar_const {lt : LevelTable} {rs1 rs2 : RustState}
    (h : ScalarPublicEquiv lt rs1 rs2) (x : String) (v : Nat) :
    ScalarPublicEquiv (updLevel lt x .Public)
      (rsSetScalar rs1 x v) (rsSetScalar rs2 x v) :=
  scalarPublicEquiv_setScalar h x v

/-- **Key inductive step (`RScalarSetExpr`).**  Overwriting `x` with the
expression `e`, and reclassifying `x` to `exprLevel lt e` (public iff every
slot `e` reads is public), preserves scalar-public-equivalence.  When the new
label is public the reads agree (`eval_eq_of_isPublic_scalar`), so the two
overwrites store equal values; when it is secret the target is excluded from
the invariant, and untouched slots are handled by the incoming equivalence. -/
theorem scalarPublicEquiv_setScalarExpr {lt : LevelTable} {rs1 rs2 : RustState}
    (h : ScalarPublicEquiv lt rs1 rs2) (x : String) (e : SExpr) :
    ScalarPublicEquiv (updLevel lt x (exprLevel lt e))
      (rsSetScalar rs1 x (e.eval rs1.rsScalar))
      (rsSetScalar rs2 x (e.eval rs2.rsScalar)) := by
  intro y hy
  unfold rsSetScalar
  by_cases hxy : y = x
  · subst hxy
    simp only [beq_self_eq_true, if_true]
    have hpub : exprLevel lt e = .Public := by
      unfold updLevel at hy; simpa using hy
    exact eval_eq_of_isPublic_scalar h e ((exprLevel_public_iff lt e).mp hpub)
  · simp only [beq_eq_false_iff_ne.mpr hxy]
    have : lt y = .Public := by
      unfold updLevel at hy; simpa [hxy] using hy
    exact h y this

/-! ## §8. Join facts -/

theorem join_eq_public_left {a b : SecretLevel} (h : a.join b = .Public) :
    a = .Public := by
  cases a <;> cases b <;> simp_all [SecretLevel.join]

theorem join_eq_public_right {a b : SecretLevel} (h : a.join b = .Public) :
    b = .Public := by
  cases a <;> cases b <;> simp_all [SecretLevel.join]

/-! ## §9. A reusable closing lemma for the deferred (leaf) constructors -/

/-- For any constructor `cmdCTFlow` defers to `cmdCT` (returning the table
unchanged), whose `flowStep` is the identity and whose `dynLeakTraceF` is the
static `LowCT.leakTrace`, soundness is immediate: the trace is data-oblivious
and the state is unchanged. -/
theorem leaf_sound {c : LowCT} {lt lt' : LevelTable} {leafCT : LeafCTTable}
    (hopt : cmdCTFlow c lt leafCT = (if cmdCT c lt leafCT then some lt else none))
    (hflow : ∀ rs, flowStep c rs = rs)
    (htrace : ∀ rs, dynLeakTraceF c rs = LowCT.leakTrace c)
    (hCT : cmdCTFlow c lt leafCT = some lt')
    {rs1 rs2 : RustState} (h : ScalarPublicEquiv lt rs1 rs2) :
    dynLeakTraceF c rs1 = dynLeakTraceF c rs2 ∧
      ScalarPublicEquiv lt' (flowStep c rs1) (flowStep c rs2) := by
  rw [hopt] at hCT
  split at hCT
  · injection hCT with hlt; subst hlt
    refine ⟨?_, ?_⟩
    · rw [htrace, htrace]
    · rw [hflow, hflow]; exact h
  · exact absurd hCT (by simp)

/-! ## §10. Soundness of the flow-sensitive checker -/

/-- **Flow-sensitive soundness.**  If `cmdCTFlow c lt leafCT = some lt'` and
the two states are scalar-public-equivalent under the input table `lt`, then
the flow-sensitive dynamic leak traces are equal *and* the two states after
`c` are scalar-public-equivalent under the output table `lt'`.

The reclassifying arms use `scalarPublicEquiv_setScalar[Expr]`; the sequential
arm threads the intermediate table and state; the branch arm uses the public
guard to force the same branch and the join-table facts to combine the two
arm outputs; every deferred constructor is closed by `leaf_sound`. -/
theorem cmdCTFlow_sound (leafCT : LeafCTTable) :
    ∀ (c : LowCT) (lt lt' : LevelTable),
      cmdCTFlow c lt leafCT = some lt' →
      ∀ {rs1 rs2 : RustState}, ScalarPublicEquiv lt rs1 rs2 →
        dynLeakTraceF c rs1 = dynLeakTraceF c rs2 ∧
          ScalarPublicEquiv lt' (flowStep c rs1) (flowStep c rs2)
  | .RScalarSet x n, lt, lt', hCT, rs1, rs2, h => by
      simp only [cmdCTFlow] at hCT
      injection hCT with hlt; subst hlt
      refine ⟨rfl, ?_⟩
      simpa [flowStep] using scalarPublicEquiv_setScalar h x n
  | .RScalarSetExpr x e, lt, lt', hCT, rs1, rs2, h => by
      simp only [cmdCTFlow] at hCT
      injection hCT with hlt; subst hlt
      refine ⟨rfl, ?_⟩
      simpa [flowStep] using scalarPublicEquiv_setScalarExpr h x e
  | .RSeq c1 c2, lt, lt', hCT, rs1, rs2, h => by
      simp only [cmdCTFlow] at hCT
      revert hCT
      cases hc1 : cmdCTFlow c1 lt leafCT with
      | none => intro hCT; simp at hCT
      | some lt1 =>
        intro hCT
        obtain ⟨ht1, hs1⟩ := cmdCTFlow_sound leafCT c1 lt lt1 hc1 h
        obtain ⟨ht2, hs2⟩ := cmdCTFlow_sound leafCT c2 lt1 lt' hCT hs1
        refine ⟨?_, ?_⟩
        · simp only [dynLeakTraceF]
          rw [ht1, ht2]
        · simp only [flowStep]; exact hs2
  | .RBlock body, lt, lt', hCT, rs1, rs2, h => by
      simp only [cmdCTFlow] at hCT
      obtain ⟨ht, hs⟩ := cmdCTFlow_sound leafCT body lt lt' hCT h
      exact ⟨ht, hs⟩
  | .RLetU64Zero x body, lt, lt', hCT, rs1, rs2, h => by
      simp only [cmdCTFlow] at hCT
      have hstep : ScalarPublicEquiv (updLevel lt x .Public)
          (rsSetScalar rs1 x 0) (rsSetScalar rs2 x 0) :=
        scalarPublicEquiv_setScalar_const h x 0
      obtain ⟨ht, hs⟩ :=
        cmdCTFlow_sound leafCT body (updLevel lt x .Public) lt' hCT hstep
      exact ⟨ht, hs⟩
  | .RLetZero y t body, lt, lt', hCT, rs1, rs2, h => by
      simp only [cmdCTFlow] at hCT
      obtain ⟨ht, hs⟩ := cmdCTFlow_sound leafCT body lt lt' hCT h
      exact ⟨ht, hs⟩
  | .RIfNz cond ct cf, lt, lt', hCT, rs1, rs2, h => by
      simp only [cmdCTFlow] at hCT
      revert hCT
      by_cases hg : (lt cond == SecretLevel.Public) = true
      · simp only [hg, if_true]
        cases hct : cmdCTFlow ct lt leafCT with
        | none => intro hCT; simp at hCT
        | some lt1 =>
          cases hcf : cmdCTFlow cf lt leafCT with
          | none => intro hCT; simp at hCT
          | some lt2 =>
            intro hCT
            injection hCT with hlt; subst hlt
            have hgpub : lt cond = .Public := level_beq_public_iff.mp hg
            have hcondEq : rs1.rsScalar cond = rs2.rsScalar cond := h cond hgpub
            have hbit : guardBit rs1 cond = guardBit rs2 cond := by
              simp only [guardBit, hcondEq]
            obtain ⟨ht1, hs1⟩ := cmdCTFlow_sound leafCT ct lt lt1 hct h
            obtain ⟨ht2, hs2⟩ := cmdCTFlow_sound leafCT cf lt lt2 hcf h
            refine ⟨?_, ?_⟩
            · simp only [dynLeakTraceF, hbit]
              by_cases hb : guardBit rs2 cond
              · simp only [hb, if_true]; rw [ht1]
              · simp only [hb, Bool.false_eq_true, if_false]; rw [ht2]
            · simp only [flowStep, hbit]
              by_cases hb : guardBit rs2 cond
              · simp only [hb, if_true]
                intro y hy
                exact hs1 y (join_eq_public_left hy)
              · simp only [hb, Bool.false_eq_true, if_false]
                intro y hy
                exact hs2 y (join_eq_public_right hy)
      · simp only [hg]; intro hCT; simp at hCT
  -- Deferred constructors: `cmdCTFlow` falls back to `cmdCT`, `flowStep` is
  -- the identity, and `dynLeakTraceF` is the static trace.
  | .RSkip, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RAssert s, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RCall f d a, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RCallSwap f d1 d2 a, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RCallN f d a, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RFnCall f d a, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RCloneCall cv ct od inF d a, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RSelect d s s0 s1, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RLimbStore l i v, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RLimbStoreExpr l i e, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RArrStore arr i s, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RArrLoad d s i, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RTupleLoad d s i, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RArrLoadLit d s i, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RArrStoreLit arr i s, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RCallDstThreaded f d a, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RForRuntime x b body, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RWhileNz cond body, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RFor x n body, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h
  | .RFnDef n p r body cont, lt, lt', hCT, rs1, rs2, h =>
      leaf_sound rfl (fun _ => rfl) (fun _ => rfl) hCT h

/-- **Flow-sensitive noninterference modulo public.**  Restated against the
ambient `PublicEquiv` used by `dynLeakTrace_noninterference`: an accepted
program's flow-sensitive dynamic leak trace is a function of the public
projection of the input only. -/
theorem cmdCTFlow_noninterference (leafCT : LeafCTTable)
    (c : LowCT) (lt lt' : LevelTable)
    (hCT : cmdCTFlow c lt leafCT = some lt')
    {rs1 rs2 : RustState} (hPE : PublicEquiv lt rs1 rs2) :
    dynLeakTraceF c rs1 = dynLeakTraceF c rs2 :=
  (cmdCTFlow_sound leafCT c lt lt' hCT (PublicEquiv.toScalar hPE)).1

/-! ## §11. Enlargement witness

A concrete kernel the flow-insensitive `cmdCT` rejects but the flow-sensitive
`cmdCTFlow` accepts: a slot `"x"` classified `.Secret`, overwritten with a
public expression, then used as a branch guard.  `cmdCT` sees the closed
`.Secret` label on `"x"` and rejects the branch; `cmdCTFlow` propagates the
overwrite to `.Public` and accepts. -/

/-- Level table: `"x"` secret, everything else public. -/
def witnessLT : LevelTable := fun v => if v = "x" then .Secret else .Public

/-- `x := 42` (a public literal expression), then branch on the now-public
`x`.  Models reuse of a register across a secret→public lifetime. -/
def flowWitness : LowCT :=
  .RSeq (.RScalarSetExpr "x" (.SLit 42))
    (.RIfNz "x" (.RScalarSet "y" 1) (.RScalarSet "z" 2))

/-- The flow-insensitive checker rejects the witness (`"x"` is `.Secret` in the
closed table, so the branch guard is rejected).  The witness has no leaf calls,
so the leaf table is immaterial; the canonical table is used to keep the goal
closed. -/
theorem flowWitness_cmdCT_rejects :
    cmdCT flowWitness witnessLT LeafCTTable.canonical = false := by decide

/-- The flow-sensitive checker accepts the witness: the overwrite reclassifies
`"x"` to `.Public`, so the downstream branch guard passes. -/
theorem flowWitness_cmdCTFlow_accepts :
    (cmdCTFlow flowWitness witnessLT LeafCTTable.canonical).isSome = true := by decide

-- `cmdCT` rejects (`false`); `cmdCTFlow` accepts (`isSome = true`).
#eval cmdCT flowWitness witnessLT LeafCTTable.canonical
#eval (cmdCTFlow flowWitness witnessLT LeafCTTable.canonical).isSome

end CatCrypt.Crypto.SecureCompilation.LowCTFlowCT
