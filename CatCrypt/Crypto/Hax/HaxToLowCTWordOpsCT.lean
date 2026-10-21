/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTWordOps
public import CatCrypt.Crypto.SecureCompilation.CT.LowCTLevelCheck

/-!
# Leakage of the word-operation passes

`scalarizeWordOps` and `scalarizeNarrowOps` replace a binding
`RLetZero x t (RSeq (RCall f x args) body)` of a word call by
`RLetU64Zero x (RSeq (RScalarSetExpr x se) body)`: the result is written to the
scalar slot of `x` instead of its tower slot, and the call's event
`callLeak M f args` is replaced by the operand events `sexprLeak M rs se` of the
scalar expression.

`ScalarizeRel D M c c'` relates a program `c` to a program `c'` obtained from it
by such rewrites, for a set `D` of names (as a predicate) whose slots may hold
different values in the two programs. Each rewritten binding writes a name of
`D`; a rewritten call is not variable time under `M.leafVT` and its scalar
expression has no node whose operands `M` makes observable (`sexprQuiet`). Every
command the two programs share reads no name of `D` at an observable position
(the guard of `RIfNz` and `RWhileNz`, the bound of `RForRuntime`, an array index,
an operand of a leaking scalar-expression node or of a variable-time leaf call),
and a command reading a name of `D` writes only names of `D` (`leafOk`). The
state relation is `LevelCheck.Rel D {}`: the two states agree on every name
outside `D`, in both heaps.

`scalarizeRel_leak` runs the two programs in lockstep: from states agreeing
outside `D`, terminating traced runs of `c` and `c'` have the same trace and end
in states agreeing outside `D`. Constant time transfers from `c` to `c'`
(`scalarizeRel_ct`), and the relation composes (`ScalarizeRel.trans`).

`wordOpsOk D M c` and `narrowOk D M W c` are decidable conditions on the input of
the passes under which the pass output is related to the input
(`scalarizeWordOps_rel`, `scalarizeNarrowIn_rel`). Under the owned model the
scalar expressions both passes produce are quiet (`wordOpSExpr_quiet_owned`,
`narrowOpSExpr_quiet_owned`, `narrowUnSExpr_quiet_owned`): every mnemonic they
lower to is on the DOIT list.

## Main definitions

* `nodeQuiet`, `sexprQuiet` — no node of a scalar expression leaks its operands.
* `leafOk` — a command without subcommands respects `D`.
* `ScalarizeRel` — the rewrite relation.
* `wordOpsOk`, `narrowLetOk`, `narrowOk` — the conditions on the pass inputs.

## Main results

* `scalarizeRel_leak` — lockstep runs have equal traces.
* `scalarizeRel_ct` — equal traces of `c` on two runs give equal traces of `c'`.
* `ScalarizeRel.trans`
* `scalarizeWordOps_rel`, `scalarizeWordOps_ct`
* `scalarizeNarrowIn_rel`, `scalarizeNarrowOps_ct`
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ScalarizeCT

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CT
open CatCrypt.Crypto.SecureCompilation.CT.LevelCheck (Levels lk sLvl sVtOk secArgs vtCallOk)

/-- The split with no override: a name is in `D` exactly when the base split
    marks it. -/
abbrev noOv : Levels := {}

/-- Two states agree outside `D`, in both heaps. -/
abbrev AgreeOff (D : String → Bool) (rs rs' : RustState) : Prop :=
  LevelCheck.Rel D noOv rs rs'

/-! ## 1. Quiet scalar expressions -/

/-- The node `e` makes no operand observable under `M`. -/
def nodeQuiet (M : LowCTLeakModel) (e : SExpr) : Bool :=
  match M.mnem e with
  | some m => !M.regime.leaksOperands m
  | none => true

/-- No node of the scalar expression makes its operands observable under `M`. -/
def sexprQuiet (M : LowCTLeakModel) : SExpr → Bool
  | .SVar _ | .SLit _ | .SLimb _ _ => true
  | .SAdd a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SAdd a b)
  | .SSub a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SSub a b)
  | .SMul a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SMul a b)
  | .SShr a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SShr a b)
  | .SShl a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SShl a b)
  | .SAnd a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SAnd a b)
  | .SXor a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SXor a b)
  | .SLt a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SLt a b)
  | .SAsr a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SAsr a b)
  | .SMulS a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SMulS a b)
  | .SMulHiU a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SMulHiU a b)
  | .SMulHiS a b => sexprQuiet M a && sexprQuiet M b && nodeQuiet M (.SMulHiS a b)

theorem nodeLeak_of_quiet {M : LowCTLeakModel} {e : SExpr} (h : nodeQuiet M e = true)
    (rs : RustState) (a b : SExpr) : nodeLeak M rs e a b = [] := by
  unfold nodeQuiet at h
  unfold nodeLeak
  split <;> simp_all

/-- A quiet scalar expression emits no event. -/
theorem sexprLeak_of_quiet {M : LowCTLeakModel} (rs : RustState) :
    ∀ e : SExpr, sexprQuiet M e = true → sexprLeak M rs e = [] := by
  intro e
  induction e with
  | SVar _ => intro _; rfl
  | SLit _ => intro _; rfl
  | SLimb _ _ => intro _; rfl
  | _ a b iha ihb =>
    intro h
    simp only [sexprQuiet, Bool.and_eq_true] at h
    simp only [sexprLeak, iha h.1.1, ihb h.1.2, nodeLeak_of_quiet h.2]
    rfl

/-! ## 2. The state relation -/

theorem agreeOff_refl (D : String → Bool) (rs : RustState) : AgreeOff D rs rs :=
  fun _ => ⟨fun _ => rfl, fun _ => rfl⟩

theorem AgreeOff.setTower_left {D : String → Bool} {rs rs' : RustState} (h : AgreeOff D rs rs')
    {x : String} (hx : D x = true) (v : Σ t : TowerType, RustVal t) :
    AgreeOff D (rsSetTower rs x v) rs' := by
  intro y
  refine ⟨(h y).1, fun hy => ?_⟩
  by_cases hyx : y = x
  · subst hyx; simp [lk, hx] at hy
  · simp [rsSetTower, hyx, (h y).2 hy]

theorem AgreeOff.setScalar_right {D : String → Bool} {rs rs' : RustState} (h : AgreeOff D rs rs')
    {x : String} (hx : D x = true) (v : Nat) : AgreeOff D rs (rsSetScalar rs' x v) := by
  intro y
  refine ⟨fun hy => ?_, (h y).2⟩
  by_cases hyx : y = x
  · subst hyx; simp [lk, hx] at hy
  · simp [rsSetScalar, hyx, (h y).1 hy]

theorem AgreeOff.setScalar_eq {D : String → Bool} {rs rs' : RustState} (h : AgreeOff D rs rs')
    (x : String) (v : Nat) : AgreeOff D (rsSetScalar rs x v) (rsSetScalar rs' x v) := by
  intro y
  refine ⟨fun hy => ?_, (h y).2⟩
  by_cases hyx : y = x
  · simp [rsSetScalar, hyx]
  · simp [rsSetScalar, hyx, (h y).1 hy]

theorem AgreeOff.setScalar_of {D : String → Bool} {rs rs' : RustState} (h : AgreeOff D rs rs')
    (x : String) (v v' : Nat) (hv : D x = false → v = v') :
    AgreeOff D (rsSetScalar rs x v) (rsSetScalar rs' x v') := by
  cases hx : D x with
  | false => rw [hv hx]; exact h.setScalar_eq x v'
  | true =>
    intro y
    refine ⟨fun hy => ?_, (h y).2⟩
    by_cases hyx : y = x
    · subst hyx; simp [lk, hx] at hy
    · simp [rsSetScalar, hyx, (h y).1 hy]

theorem AgreeOff.setTower_of {D : String → Bool} {rs rs' : RustState} (h : AgreeOff D rs rs')
    (x : String) (v v' : Σ t : TowerType, RustVal t) (hv : D x = false → v = v') :
    AgreeOff D (rsSetTower rs x v) (rsSetTower rs' x v') := by
  cases hx : D x with
  | false => rw [hv hx]; exact LevelCheck.Rel.setTower_eq h x v'
  | true => exact LevelCheck.Rel.setTower_secret h (x := x) hx v v'

theorem lookup_eq_of {D : String → Bool} {rs rs' : RustState} (h : AgreeOff D rs rs')
    {loc : Located} (hl : D loc.locVar = false) {v v' : RustVal loc.locDst}
    (h₁ : locatedLookup rs loc = some v) (h₂ : locatedLookup rs' loc = some v') : v = v' := by
  rw [LevelCheck.lookup_eq h hl, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-! ## 3. Commands that respect `D` -/

/-- A command without subcommands respects `D`: it reads no name of `D` at an
    observable position, and when it reads a name of `D` it writes only names of
    `D`. Commands with subcommands, and `RFnDef`/`RFnCall`, are not accepted. -/
def leafOk (D : String → Bool) (M : LowCTLeakModel) : LowCT → Bool
  | .RSkip | .RAssert _ | .RScalarSet _ _ | .RLimbStore _ _ _ => true
  | .RScalarSetExpr x e => sVtOk M D noOv e && (!sLvl D noOv e || D x)
  | .RLimbStoreExpr loc _ e => sVtOk M D noOv e && (!sLvl D noOv e || D loc.locVar)
  | .RCall f dest args =>
      vtCallOk M D noOv f args && (!secArgs D noOv (dest :: args) || D dest.locVar)
  | .RCloneCall cloneVar _ oldDest innerF dest args =>
      (!D oldDest.locVar || D cloneVar) &&
        vtCallOk M D noOv innerF args && (!secArgs D noOv (dest :: args) || D dest.locVar)
  | .RCallSwap f d1 d2 args =>
      vtCallOk M D noOv f args && (!secArgs D noOv (d1 :: args) || D d1.locVar) &&
        (!secArgs D noOv (d2 :: args) || D d2.locVar)
  | .RCallN f dests args =>
      vtCallOk M D noOv f args &&
        (dests.all (fun d => D d.locVar) || !secArgs D noOv (dests ++ args))
  | .RSelect dst sel src0 src1 =>
      (!D sel && !D src0.locVar && !D src1.locVar) || D dst.locVar
  | .RTupleLoad dst src _ => !D src.locVar || D dst.locVar
  | .RArrStore arr idxVar src => !D idxVar && (!D src.locVar || D arr.locVar)
  | .RArrLoad dst src idxVar => !D idxVar && (!D src.locVar || D dst.locVar)
  | .RArrStoreLit arr _ src => !D src.locVar || D arr.locVar
  | .RArrLoadLit dst src _ => !D src.locVar || D dst.locVar
  | .RCallDstThreaded f dst args =>
      vtCallOk M D noOv f (dst :: args) && (!secArgs D noOv (dst :: args) || D dst.locVar)
  | .RCopy dst src => !D src.locVar || D dst.locVar
  | _ => false

/-! ## 4. The rewrite relation -/

/-- `c'` is `c` with bindings of calls rewritten to scalar assignments of quiet
    scalar expressions into names of `D`, and every shared command respecting
    `D`. -/
inductive ScalarizeRel (D : String → Bool) (M : LowCTLeakModel) : LowCT → LowCT → Prop where
  | leaf : ∀ c, leafOk D M c = true → ScalarizeRel D M c c
  | seq : ∀ a a' b b', ScalarizeRel D M a a' → ScalarizeRel D M b b' →
      ScalarizeRel D M (.RSeq a b) (.RSeq a' b')
  | letZero : ∀ x t b b', ScalarizeRel D M b b' →
      ScalarizeRel D M (.RLetZero x t b) (.RLetZero x t b')
  | letU64Zero : ∀ x b b', ScalarizeRel D M b b' →
      ScalarizeRel D M (.RLetU64Zero x b) (.RLetU64Zero x b')
  | ifNz : ∀ e ct ct' cf cf', D e = false → ScalarizeRel D M ct ct' →
      ScalarizeRel D M cf cf' → ScalarizeRel D M (.RIfNz e ct cf) (.RIfNz e ct' cf')
  | whileNz : ∀ e b b', D e = false → ScalarizeRel D M b b' →
      ScalarizeRel D M (.RWhileNz e b) (.RWhileNz e b')
  | forLit : ∀ x n b b', ScalarizeRel D M b b' →
      ScalarizeRel D M (.RFor x n b) (.RFor x n b')
  | forRuntime : ∀ x bound b b', sLvl D noOv bound = false → sVtOk M D noOv bound = true →
      ScalarizeRel D M b b' → ScalarizeRel D M (.RForRuntime x bound b) (.RForRuntime x bound b')
  | block : ∀ b b', ScalarizeRel D M b b' → ScalarizeRel D M (.RBlock b) (.RBlock b')
  | letRw : ∀ x t b b', D x = true → ScalarizeRel D M b b' →
      ScalarizeRel D M (.RLetZero x t b) (.RLetU64Zero x b')
  | callRw : ∀ f dest args x se, D dest.locVar = true → D x = true → M.leafVT f = false →
      sexprQuiet M se = true → ScalarizeRel D M (.RCall f dest args) (.RScalarSetExpr x se)

/-! ## 5. Lockstep runs -/

theorem secArgs_tail {D : String → Bool} {d : Located} {args : List Located}
    (h : secArgs D noOv (d :: args) = false) : secArgs D noOv args = false := by
  unfold secArgs at h ⊢
  simp only [List.any_cons, Bool.or_eq_false_iff] at h
  exact h.2

theorem secArgs_head {D : String → Bool} {d : Located} {args : List Located}
    (h : secArgs D noOv (d :: args) = false) : D d.locVar = false :=
  LevelCheck.secArgs_false h d (by simp)

/-- One leaf call `dest := f(args)` run from two states agreeing outside `D`
    gives the same event and states agreeing outside `D`. -/
theorem call_agree {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel} {D : String → Bool}
    {f : String} {dest : Located} {args : List Located}
    (hok : leafOk D M (.RCall f dest args) = true) {rs rs' r r' : RustState} {t t' : List CTLeak}
    (hS : AgreeOff D rs rs') (h : RustExecLeak N leafSpec M (.RCall f dest args) rs t r)
    (h' : RustExecLeak N leafSpec M (.RCall f dest args) rs' t' r') :
    t' = t ∧ AgreeOff D r r' := by
  simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨hvt, hw⟩ := hok
  cases h with
  | call _ _ _ _ o al h1 h2 _ =>
  cases h' with
  | call _ _ _ _ o' al' h1' h2' _ =>
  subst h2 h2'
  refine ⟨(LevelCheck.callLeak_eq hS hvt).symm, ?_⟩
  unfold locatedUpdate
  refine hS.setTower_of _ _ _ fun hd => ?_
  have hs : secArgs D noOv (dest :: args) = false := by
    rcases hw with hw | hw
    · exact hw
    · simp [hw] at hd
  rw [lookup_eq_of hS (secArgs_head hs) h1 h1', LevelCheck.argList_eq hS (secArgs_tail hs)]

/-- **Lockstep runs.** Terminating traced runs of `c` and of a program `c'`
    related to it by `ScalarizeRel D M`, from states agreeing outside `D`, have the
    same trace and end in states agreeing outside `D`. -/
theorem scalarizeRel_leak {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {D : String → Bool} {c : LowCT} {rs r : RustState} {t : List CTLeak}
    (h : RustExecLeak N leafSpec M c rs t r) :
    ∀ {c' : LowCT} {rs' r' : RustState} {t' : List CTLeak}, ScalarizeRel D M c c' →
      AgreeOff D rs rs' → RustExecLeak N leafSpec M c' rs' t' r' → t' = t ∧ AgreeOff D r r' := by
  induction h with
  | skip rs =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ _ => cases h'; exact ⟨rfl, hS⟩
  | seq c1 c2 rs r1 rs₂ t1 t2 _ _ ih1 ih2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | seq _ a' _ b' ha hb =>
      cases h' with
      | seq _ _ _ r1' _ t1' t2' h1' h2' =>
      obtain ⟨e1, s1⟩ := ih1 ha hS h1'
      obtain ⟨e2, s2⟩ := ih2 hb s1 h2'
      exact ⟨by rw [e1, e2], s2⟩
  | letZero x ty body rs rs₂ tr _ ih =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | letZero _ _ _ b' hb =>
      cases h' with
      | letZero _ _ _ _ _ _ h1' => exact ih hb (LevelCheck.Rel.setTower_eq hS _ _) h1'
    | letRw _ _ _ b' hx hb =>
      cases h' with
      | letU64Zero _ _ _ _ _ h1' => exact ih hb ((hS.setTower_left hx _).setScalar_right hx _) h1'
  | letU64Zero x body rs rs₂ tr _ ih =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | letU64Zero _ _ b' hb =>
      cases h' with
      | letU64Zero _ _ _ _ _ h1' => exact ih hb (hS.setScalar_eq _ _) h1'
  | scalarSet x v rs =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ _ => cases h'; exact ⟨rfl, hS.setScalar_eq _ _⟩
  | ifTrue e ct cf rs rs₂ v tr hv hv0 _ ih =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | ifNz _ _ ct' _ cf' he hct _ =>
      cases h' with
      | ifTrue _ _ _ _ _ _ _ _ _ h1' =>
        obtain ⟨e1, s1⟩ := ih hct hS h1'
        exact ⟨by rw [e1], s1⟩
      | ifFalse _ _ _ _ _ _ hv' _ =>
        exact absurd (hv ▸ ((hS e).1 he).trans hv') hv0
  | ifFalse e ct cf rs rs₂ tr hv _ ih =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | ifNz _ _ ct' _ cf' he _ hcf =>
      cases h' with
      | ifTrue _ _ _ _ _ v' _ hv' hv0' _ =>
        exact absurd (hv' ▸ ((hS e).1 he).symm.trans hv) hv0'
      | ifFalse _ _ _ _ _ _ _ h1' =>
        obtain ⟨e1, s1⟩ := ih hcf hS h1'
        exact ⟨by rw [e1], s1⟩
  | whileFalse e body rs hv =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | whileNz _ _ b' he hb =>
      cases h' with
      | whileFalse _ _ _ _ => exact ⟨rfl, hS⟩
      | whileTrue _ _ _ _ _ v' _ _ hv' hv0' _ _ =>
        exact absurd (hv' ▸ ((hS e).1 he).symm.trans hv) hv0'
  | whileTrue e body rs r1 rs₂ v t1 t2 hv hv0 _ _ ih1 ih2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | whileNz _ _ b' he hb =>
      cases h' with
      | whileFalse _ _ _ hv' => exact absurd (hv ▸ ((hS e).1 he).trans hv') hv0
      | whileTrue _ _ _ r1' _ _ t1' t2' _ _ h1' h2' =>
        obtain ⟨e1, s1⟩ := ih1 hb hS h1'
        obtain ⟨e2, s2⟩ := ih2 (.whileNz _ _ _ he hb) s1 h2'
        exact ⟨by rw [e1, e2], s2⟩
  | forZero x body rs =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | forLit _ _ _ b' hb =>
      cases h' with
      | forZero => exact ⟨rfl, hS⟩
  | forSucc x n body rs r1 rs₂ t1 t2 _ _ ih1 ih2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | forLit _ _ _ b' hb =>
      cases h' with
      | forSucc _ _ _ _ r1' _ t1' t2' h1' h2' =>
        obtain ⟨e1, s1⟩ := ih1 (.forLit _ _ _ _ hb) hS h1'
        obtain ⟨e2, s2⟩ := ih2 hb (s1.setScalar_eq _ _) h2'
        exact ⟨by rw [e1, e2], s2⟩
  | forRuntime x bound body rs rs₂ tr _ ih =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | forRuntime _ _ _ b' hl hvt hb =>
      cases h' with
      | forRuntime _ _ _ _ _ tr' h1' =>
        have hev := LevelCheck.sLvl_eval hS bound hl
        rw [← hev] at h1'
        obtain ⟨e1, s1⟩ := ih (.forLit _ _ _ _ hb) hS h1'
        exact ⟨by rw [e1, ← hev, LevelCheck.sexprLeak_eq hS bound hvt], s1⟩
  | call f dest args rs o al h1 h2 h3 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => exact call_agree hok hS (.call f dest args rs o al h1 h2 h3) h'
    | callRw _ _ _ x se hd hx hvt hq =>
      cases h' with
      | scalarSetExpr =>
        refine ⟨?_, ?_⟩
        · rw [sexprLeak_of_quiet _ se hq]; simp [callLeak, hvt]
        · exact (hS.setTower_left hd _).setScalar_right hx _
  | cloneCall cloneVar cloneTy oldDest innerF dest args rs rsClone rs₂ tr hc _ ih =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      cases h' with
      | cloneCall _ _ _ _ _ _ _ rsClone' _ _ hc' h1' =>
        have hok' := hok
        simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok'
        obtain ⟨⟨hcl, hvt⟩, hw⟩ := hok'
        have hcall : leafOk D M (.RCall innerF dest args) = true := by
          simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
          exact ⟨hvt, hw⟩
        subst hc hc'
        refine ih (.leaf _ hcall) (hS.setTower_of _ _ _ fun hd => ?_) h1'
        rcases hcl with hcl | hcl
        · rw [(hS oldDest.locVar).2 hcl]
        · simp [hcl] at hd
  | callSwap f d1 d2 args rs rs1 rs₂ t1 t2 _ _ ih1 ih2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true] at hok
      obtain ⟨⟨hvt, hw1⟩, hw2⟩ := hok
      have hc1 : leafOk D M (.RCall f d1 args) = true := by simp [leafOk, hvt, hw1]
      have hc2 : leafOk D M (.RCall f d2 args) = true := by simp [leafOk, hvt, hw2]
      cases h' with
      | callSwap _ _ _ _ _ rs1' _ t1' t2' h1' h2' =>
        obtain ⟨e1, s1⟩ := ih1 (.leaf _ hc1) hS h1'
        obtain ⟨e2, s2⟩ := ih2 (.leaf _ hc2) s1 h2'
        exact ⟨by rw [e1, e2], s2⟩
  | limbStore loc idx v rs o h1 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ _ =>
      cases h' with
      | limbStore _ _ _ _ o' h1' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        exact hS.setTower_of _ _ _ fun hd => by rw [lookup_eq_of hS hd h1 h1']
  | limbStoreExpr loc idx e rs o h1 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hvt, hw⟩ := hok
      cases h' with
      | limbStoreExpr _ _ _ _ o' h1' =>
        refine ⟨(LevelCheck.sexprLeak_eq hS e hvt).symm, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        have he : sLvl D noOv e = false := by
          rcases hw with hw | hw
          · exact hw
          · simp [hw] at hd
        rw [lookup_eq_of hS hd h1 h1', LevelCheck.sLvl_eval hS e he]
  | callN f dests args rs al h1 h2 h3 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hvt, hw⟩ := hok
      cases h' with
      | callN _ _ _ _ al' h1' _ _ =>
        subst h1 h1'
        refine ⟨(LevelCheck.callLeak_eq hS hvt).symm, ?_⟩
        rcases hw with hw | hw
        · exact LevelCheck.callNUpdate_secret _ _ _ _ _ dests 0 _ _ hS
            (fun d hd => by simpa [lk] using List.all_eq_true.1 hw d hd)
        · have hall := LevelCheck.secArgs_false hw
          have hargs : secArgs D noOv args = false := by
            unfold secArgs at hw ⊢; rw [List.any_append, Bool.or_eq_false_iff] at hw; exact hw.2
          rw [LevelCheck.argList_eq hS hargs]
          exact LevelCheck.callNUpdate_public _ _ _ _ dests 0 _ _ hS
            (fun d hd => hall d (List.mem_append_left _ hd))
  | selectFalse dst sel src0 src1 rs hh sv hsel h1 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      cases h' with
      | selectFalse _ _ _ _ _ hh' sv' hsel' h1' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with ⟨⟨_, h0⟩, _⟩ | hok
        · rw [lookup_eq_of hS h0 h1 h1']
        · simp [hok] at hd
      | selectTrue _ _ _ _ _ hh' v' sv' hsel' hv' h1' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with ⟨⟨hs, _⟩, _⟩ | hok
        · exact absurd (hsel' ▸ ((hS sel).1 hs).symm.trans hsel) hv'
        · simp [hok] at hd
  | selectTrue dst sel src0 src1 rs hh v sv hsel hv h1 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      cases h' with
      | selectFalse _ _ _ _ _ hh' sv' hsel' h1' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with ⟨⟨hs, _⟩, _⟩ | hok
        · exact absurd (hsel ▸ ((hS sel).1 hs).trans hsel') hv
        · simp [hok] at hd
      | selectTrue _ _ _ _ _ hh' v' sv' hsel' hv' h1' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with ⟨_, h0⟩ | hok
        · rw [lookup_eq_of hS h0 h1 h1']
        · simp [hok] at hd
  | assert label rs =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ _ => cases h'; exact ⟨rfl, hS⟩
  | block body rs rs₂ tr _ ih =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok => simp [leafOk] at hok
    | block _ b' hb =>
      cases h' with
      | block _ _ _ _ h1' => exact ih hb hS h1'
  | tupleLoad dst src idx rs o sv h1 h2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.or_eq_true, Bool.not_eq_true'] at hok
      cases h' with
      | tupleLoad _ _ _ _ o' sv' h1' h2' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with hok | hok
        · rw [lookup_eq_of hS hd h1 h1', lookup_eq_of hS hok h2 h2']
        · simp [hok] at hd
  | arrStore arr idxVar src rs idx o sv hi h1 h2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hix, hw⟩ := hok
      cases h' with
      | arrStore _ _ _ _ idx' o' sv' hi' h1' h2' =>
        have he : idx' = idx := by rw [← hi, ← hi', (hS idxVar).1 hix]
        subst he
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hw with hw | hw
        · rw [lookup_eq_of hS hd h1 h1', lookup_eq_of hS hw h2 h2']
        · simp [hw] at hd
  | arrLoad dst src idxVar rs idx o sv hi h1 h2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hix, hw⟩ := hok
      cases h' with
      | arrLoad _ _ _ _ idx' o' sv' hi' h1' h2' =>
        have he : idx' = idx := by rw [← hi, ← hi', (hS idxVar).1 hix]
        subst he
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hw with hw | hw
        · rw [lookup_eq_of hS hd h1 h1', lookup_eq_of hS hw h2 h2']
        · simp [hw] at hd
  | arrStoreLit arr idx src rs o sv h1 h2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.or_eq_true, Bool.not_eq_true'] at hok
      cases h' with
      | arrStoreLit _ _ _ _ o' sv' h1' h2' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with hok | hok
        · rw [lookup_eq_of hS hd h1 h1', lookup_eq_of hS hok h2 h2']
        · simp [hok] at hd
  | arrLoadLit dst src idx rs o sv h1 h2 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.or_eq_true, Bool.not_eq_true'] at hok
      cases h' with
      | arrLoadLit _ _ _ _ o' sv' h1' h2' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with hok | hok
        · rw [lookup_eq_of hS hd h1 h1', lookup_eq_of hS hok h2 h2']
        · simp [hok] at hd
  | scalarSetExpr x e rs =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hvt, hw⟩ := hok
      cases h' with
      | scalarSetExpr =>
        refine ⟨(LevelCheck.sexprLeak_eq hS e hvt).symm, hS.setScalar_of _ _ _ fun hd => ?_⟩
        rcases hw with hw | hw
        · exact LevelCheck.sLvl_eval hS e hw
        · simp [hw] at hd
  | callDstThreaded f dst args rs o al h1 h2 h3 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hvt, hw⟩ := hok
      cases h' with
      | callDstThreaded _ _ _ _ o' al' h1' h2' _ =>
        subst h2 h2'
        refine ⟨(LevelCheck.callLeak_eq hS hvt).symm, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        have hs : secArgs D noOv (dst :: args) = false := by
          rcases hw with hw | hw
          · exact hw
          · simp [hw] at hd
        rw [lookup_eq_of hS (secArgs_head hs) h1 h1', LevelCheck.argList_eq hS hs]
  | copy dst src rs hh sv h1 =>
    intro c' rs' r' t' hR hS h'
    cases hR with
    | leaf _ hok =>
      simp only [leafOk, Bool.or_eq_true, Bool.not_eq_true'] at hok
      cases h' with
      | copy _ _ _ hh' sv' h1' =>
        refine ⟨rfl, ?_⟩
        unfold locatedUpdate
        refine hS.setTower_of _ _ _ fun hd => ?_
        rcases hok with hok | hok
        · rw [lookup_eq_of hS hok h1 h1']
        · simp [hok] at hd

/-- **Constant time through the rewrite.** If two terminating runs of `c` have
    equal traces, the runs of `c'` from the same two states have equal traces. -/
theorem scalarizeRel_ct {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {D : String → Bool} {c c' : LowCT} (hR : ScalarizeRel D M c c')
    {rs₁ rs₂ r₁ r₂ r₁' r₂' : RustState} {t₁ t₂ t₁' t₂' : List CTLeak}
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂)
    (ht : t₁ = t₂)
    (h₁' : RustExecLeak N leafSpec M c' rs₁ t₁' r₁')
    (h₂' : RustExecLeak N leafSpec M c' rs₂ t₂' r₂') : t₁' = t₂' := by
  rw [(scalarizeRel_leak h₁ hR (agreeOff_refl D rs₁) h₁').1,
    (scalarizeRel_leak h₂ hR (agreeOff_refl D rs₂) h₂').1, ht]

/-- The rewrite relation composes. -/
theorem ScalarizeRel.trans {D : String → Bool} {M : LowCTLeakModel} {c c₁ : LowCT}
    (h₁ : ScalarizeRel D M c c₁) : ∀ {c₂ : LowCT}, ScalarizeRel D M c₁ c₂ →
      ScalarizeRel D M c c₂ := by
  induction h₁ with
  | leaf _ _ => exact id
  | seq _ _ _ _ _ _ iha ihb =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | seq _ _ _ _ ha hb => exact .seq _ _ _ _ (iha ha) (ihb hb)
  | letZero _ _ _ _ _ ih =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | letZero _ _ _ _ hb => exact .letZero _ _ _ _ (ih hb)
    | letRw _ _ _ _ hx hb => exact .letRw _ _ _ _ hx (ih hb)
  | letU64Zero _ _ _ _ ih =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | letU64Zero _ _ _ hb => exact .letU64Zero _ _ _ (ih hb)
  | ifNz _ _ _ _ _ he _ _ iht ihf =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | ifNz _ _ _ _ _ _ ht hf => exact .ifNz _ _ _ _ _ he (iht ht) (ihf hf)
  | whileNz _ _ _ he _ ih =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | whileNz _ _ _ _ hb => exact .whileNz _ _ _ he (ih hb)
  | forLit _ _ _ _ _ ih =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | forLit _ _ _ _ hb => exact .forLit _ _ _ _ (ih hb)
  | forRuntime _ _ _ _ hl hv _ ih =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | forRuntime _ _ _ _ _ _ hb => exact .forRuntime _ _ _ _ hl hv (ih hb)
  | block _ _ _ ih =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | block _ _ hb => exact .block _ _ (ih hb)
  | letRw _ _ _ _ hx _ ih =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ hok => simp [leafOk] at hok
    | letU64Zero _ _ _ hb => exact .letRw _ _ _ _ hx (ih hb)
  | callRw _ _ _ _ _ hd hx hvt hq =>
    intro c₂ h₂
    cases h₂ with
    | leaf _ _ => exact .callRw _ _ _ _ _ hd hx hvt hq

/-- A program related to `RSeq (RCall f dest args) body` is related to the program
    with the call replaced by a quiet scalar assignment into a name of `D`. -/
theorem ScalarizeRel.callHead {D : String → Bool} {M : LowCTLeakModel} {b body : LowCT}
    {f x : String} {dest : Located} {args : List Located} {se : SExpr}
    (h : ScalarizeRel D M b (.RSeq (.RCall f dest args) body)) (hd : D dest.locVar = true)
    (hx : D x = true) (hvt : M.leafVT f = false) (hq : sexprQuiet M se = true) :
    ScalarizeRel D M b (.RSeq (.RScalarSetExpr x se) body) := by
  cases h with
  | leaf _ hok => simp [leafOk] at hok
  | seq a _ _ _ ha hb =>
    cases ha with
    | leaf _ _ => exact .seq _ _ _ _ (.callRw _ _ _ _ _ hd hx hvt hq) hb

/-! ## 6. The word-operation pass -/

/-- The condition on a binding of `x` with body `b` under which `scalarizeWordOps`
    may rewrite it: when `b` starts with a word call into `x`, `x` is in `D`, the
    call is not variable time and its scalar expression is quiet. -/
def wordLetOk (D : String → Bool) (M : LowCTLeakModel) (x : String) : LowCT → Bool
  | .RSeq (.RCall f dest [a, b]) _ =>
      match wordOpSExpr f (.SVar a.locVar) (.SVar b.locVar) with
      | some se => if dest.locVar = x then D x && !M.leafVT f && sexprQuiet M se else true
      | none => true
  | _ => true

/-- The input condition of `scalarizeWordOps`: every shared command respects `D`
    and every rewritten binding satisfies `wordLetOk`. -/
def wordOpsOk (D : String → Bool) (M : LowCTLeakModel) : LowCT → Bool
  | .RLetZero x _ b => wordOpsOk D M b && wordLetOk D M x b
  | .RSeq a b => wordOpsOk D M a && wordOpsOk D M b
  | .RLetU64Zero _ b => wordOpsOk D M b
  | .RIfNz v t e => !D v && wordOpsOk D M t && wordOpsOk D M e
  | .RWhileNz v b => !D v && wordOpsOk D M b
  | .RFor _ _ b => wordOpsOk D M b
  | .RForRuntime _ bound b =>
      !sLvl D noOv bound && sVtOk M D noOv bound && wordOpsOk D M b
  | .RBlock b => wordOpsOk D M b
  | c => leafOk D M c

/-- `scalarizeWordOps` relates its output to its input when the input satisfies
    `wordOpsOk`. -/
theorem scalarizeWordOps_rel {D : String → Bool} {M : LowCTLeakModel} (c : LowCT)
    (hok : wordOpsOk D M c = true) : ScalarizeRel D M c (scalarizeWordOps c) := by
  fun_induction scalarizeWordOps c with
  | case1 t f dest a b body se hse ih =>
    simp only [wordOpsOk, wordLetOk, hse, if_true, Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨_, hb⟩, ⟨hx, hvt⟩, hq⟩ := hok
    exact .letRw _ _ _ _ hx (.seq _ _ _ _ (.callRw _ _ _ _ _ hx hx hvt hq) (ih hb))
  | case2 x t f dest a b body se _ _ ih =>
    simp only [wordOpsOk, Bool.and_eq_true] at hok
    exact .letZero _ _ _ _ (.seq _ _ _ _ (.leaf _ hok.1.1) (ih hok.1.2))
  | case3 x t f dest a b body _ ih =>
    simp only [wordOpsOk, Bool.and_eq_true] at hok
    exact .letZero _ _ _ _ (.seq _ _ _ _ (.leaf _ hok.1.1) (ih hok.1.2))
  | case4 a b iha ihb =>
    simp only [wordOpsOk, Bool.and_eq_true] at hok
    exact .seq _ _ _ _ (iha hok.1) (ihb hok.2)
  | case5 x t b _ ih =>
    simp only [wordOpsOk, Bool.and_eq_true] at hok
    exact .letZero _ _ _ _ (ih hok.1)
  | case6 x b ih =>
    simp only [wordOpsOk] at hok
    exact .letU64Zero _ _ _ (ih hok)
  | case7 v t e iht ihe =>
    simp only [wordOpsOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact .ifNz _ _ _ _ _ hok.1.1 (iht hok.1.2) (ihe hok.2)
  | case8 v b ih =>
    simp only [wordOpsOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact .whileNz _ _ _ hok.1 (ih hok.2)
  | case9 x n b ih =>
    simp only [wordOpsOk] at hok
    exact .forLit _ _ _ _ (ih hok)
  | case10 x bound b ih =>
    simp only [wordOpsOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact .forRuntime _ _ _ _ hok.1.1 hok.1.2 (ih hok.2)
  | case11 b ih =>
    simp only [wordOpsOk] at hok
    exact .block _ _ (ih hok)
  | case12 c _ hseq hlet hu64 hif hwh hfor hrt hblk =>
    refine .leaf _ ?_
    cases c <;>
      first
      | exact (hseq _ _ rfl).elim
      | exact (hlet _ _ _ rfl).elim
      | exact (hu64 _ _ rfl).elim
      | exact (hif _ _ _ rfl).elim
      | exact (hwh _ _ rfl).elim
      | exact (hfor _ _ _ rfl).elim
      | exact (hrt _ _ _ rfl).elim
      | exact (hblk _ rfl).elim
      | simpa only [wordOpsOk] using hok

/-- **Constant time through `scalarizeWordOps`.** For an input satisfying
    `wordOpsOk`, if two terminating runs of `c` have equal traces, the runs of
    `scalarizeWordOps c` from the same two states have equal traces. -/
theorem scalarizeWordOps_ct {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {D : String → Bool} {c : LowCT} (hok : wordOpsOk D M c = true)
    {rs₁ rs₂ r₁ r₂ r₁' r₂' : RustState} {t₁ t₂ t₁' t₂' : List CTLeak}
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂)
    (ht : t₁ = t₂)
    (h₁' : RustExecLeak N leafSpec M (scalarizeWordOps c) rs₁ t₁' r₁')
    (h₂' : RustExecLeak N leafSpec M (scalarizeWordOps c) rs₂ t₂' r₂') : t₁' = t₂' :=
  scalarizeRel_ct (scalarizeWordOps_rel c hok) h₁ h₂ ht h₁' h₂'

/-! ## 7. The narrow-operation pass -/

/-- The condition on a binding of `x` whose body, after the pass, is `b'` under
    which `narrowLetIn W x` may rewrite it: when `b'` starts with a narrow word
    call, cast or complement into `x` that the pass lowers, `x` is in `D`, the call
    is not variable time and its scalar expression is quiet. -/
def narrowLetOk (D : String → Bool) (M : LowCTLeakModel) (W : List String) (x : String) :
    LowCT → Bool
  | .RSeq (.RCall f dest [a, b]) _ =>
      match narrowOpSExpr f (.SVar a.locVar) (.SVar b.locVar) with
      | some se => if dest.locVar = x then D x && !M.leafVT f && sexprQuiet M se else true
      | none => true
  | .RSeq (.RCall f dest [a]) _ =>
      match narrowUnSExpr W f a.locVar with
      | some se => if dest.locVar = x then D x && !M.leafVT f && sexprQuiet M se else true
      | none => true
  | _ => true

/-- The input condition of `scalarizeNarrowIn W`: every shared command respects
    `D` and every rewritten binding satisfies `narrowLetOk`, with the known words
    threaded as the pass threads them. -/
def narrowOk (D : String → Bool) (M : LowCTLeakModel) : List String → LowCT → Bool
  | W, .RLetZero x _ b =>
      narrowOk D M (bindWord W x (bindsWord x b)) b &&
        narrowLetOk D M W x (scalarizeNarrowIn (bindWord W x (bindsWord x b)) b)
  | W, .RSeq a b => narrowOk D M W a && narrowOk D M W b
  | W, .RLetU64Zero x b => narrowOk D M (x :: W) b
  | W, .RIfNz v t e => !D v && narrowOk D M W t && narrowOk D M W e
  | W, .RWhileNz v b => !D v && narrowOk D M W b
  | W, .RFor x _ b => narrowOk D M (x :: W) b
  | W, .RForRuntime x bound b =>
      !sLvl D noOv bound && sVtOk M D noOv bound && narrowOk D M (x :: W) b
  | W, .RBlock b => narrowOk D M W b
  | _, c => leafOk D M c

theorem narrowLetIn_rel {D : String → Bool} {M : LowCTLeakModel} {W : List String}
    {x : String} {t : TowerType} {b b' : LowCT} (hR : ScalarizeRel D M b b')
    (hok : narrowLetOk D M W x b' = true) :
    ScalarizeRel D M (.RLetZero x t b) (narrowLetIn W x t b') := by
  fun_cases narrowLetIn W x t b'
  all_goals
    first
    | exact .letZero _ _ _ _ hR
    | (simp only [narrowLetOk, *, if_true, Bool.and_eq_true, Bool.not_eq_true'] at hok
       obtain ⟨⟨hx, hvt⟩, hq⟩ := hok
       exact .letRw _ _ _ _ hx (hR.callHead (by simp_all) hx hvt hq))

/-- `scalarizeNarrowIn W` relates its output to its input when the input
    satisfies `narrowOk D M W`. -/
theorem scalarizeNarrowIn_rel {D : String → Bool} {M : LowCTLeakModel} :
    ∀ (W : List String) (c : LowCT), narrowOk D M W c = true →
      ScalarizeRel D M c (scalarizeNarrowIn W c) := by
  intro W c
  induction c generalizing W with
  | RLetZero x t b ih =>
    intro hok
    simp only [narrowOk, Bool.and_eq_true] at hok
    simp only [scalarizeNarrowIn]
    exact narrowLetIn_rel (ih _ hok.1) hok.2
  | RSeq a b iha ihb =>
    intro hok
    simp only [narrowOk, Bool.and_eq_true] at hok
    exact .seq _ _ _ _ (iha W hok.1) (ihb W hok.2)
  | RLetU64Zero x b ih =>
    intro hok
    simp only [narrowOk] at hok
    exact .letU64Zero _ _ _ (ih _ hok)
  | RIfNz v t e iht ihe =>
    intro hok
    simp only [narrowOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact .ifNz _ _ _ _ _ hok.1.1 (iht W hok.1.2) (ihe W hok.2)
  | RWhileNz v b ih =>
    intro hok
    simp only [narrowOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact .whileNz _ _ _ hok.1 (ih W hok.2)
  | RFor x n b ih =>
    intro hok
    simp only [narrowOk] at hok
    exact .forLit _ _ _ _ (ih _ hok)
  | RForRuntime x bound b ih =>
    intro hok
    simp only [narrowOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact .forRuntime _ _ _ _ hok.1.1 hok.1.2 (ih _ hok.2)
  | RBlock b ih =>
    intro hok
    simp only [narrowOk] at hok
    exact .block _ _ (ih W hok)
  | _ =>
    intro hok
    exact .leaf _ (by simpa only [narrowOk] using hok)

/-- **Constant time through `scalarizeNarrowOps`.** For an input satisfying
    `narrowOk D M []`, if two terminating runs of `c` have equal traces, the runs of
    `scalarizeNarrowOps c` from the same two states have equal traces. -/
theorem scalarizeNarrowOps_ct {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {D : String → Bool} {c : LowCT} (hok : narrowOk D M [] c = true)
    {rs₁ rs₂ r₁ r₂ r₁' r₂' : RustState} {t₁ t₂ t₁' t₂' : List CTLeak}
    (h₁ : RustExecLeak N leafSpec M c rs₁ t₁ r₁) (h₂ : RustExecLeak N leafSpec M c rs₂ t₂ r₂)
    (ht : t₁ = t₂)
    (h₁' : RustExecLeak N leafSpec M (scalarizeNarrowOps c) rs₁ t₁' r₁')
    (h₂' : RustExecLeak N leafSpec M (scalarizeNarrowOps c) rs₂ t₂' r₂') : t₁' = t₂' :=
  scalarizeRel_ct (scalarizeNarrowIn_rel [] c hok) h₁ h₂ ht h₁' h₂'

/-- Both passes, in the order of the production front, relate their output to
    their input. -/
theorem scalarizeBoth_rel {D : String → Bool} {M : LowCTLeakModel} {c : LowCT}
    (hN : narrowOk D M [] c = true) (hW : wordOpsOk D M (scalarizeNarrowOps c) = true) :
    ScalarizeRel D M c (scalarizeWordOps (scalarizeNarrowOps c)) :=
  (scalarizeNarrowIn_rel [] c hN).trans (scalarizeWordOps_rel _ hW)

/-! ## 8. Quiet expressions of the owned model -/

/-- The scalar expressions of the `u64` word calls are quiet in the owned model. -/
theorem wordOpSExpr_quiet_owned {f : String} {a b : String} {se : SExpr}
    (h : wordOpSExpr f (.SVar a) (.SVar b) = some se) : sexprQuiet .owned se = true := by
  unfold wordOpSExpr at h
  split at h <;> cases h <;>
    simp [sexprQuiet, nodeQuiet, LowCTLeakModel.owned, sexprMnem, DoitRegime.leaksOperands,
      X86Mnem.timing]

/-- The scalar expressions of the narrow word calls are quiet in the owned model. -/
theorem narrowOpSExpr_quiet_owned {f : String} {a b : String} {se : SExpr}
    (h : narrowOpSExpr f (.SVar a) (.SVar b) = some se) : sexprQuiet .owned se = true := by
  unfold narrowOpSExpr at h
  cases hf : narrowOpOf f with
  | none => simp [hf] at h
  | some p =>
    obtain ⟨w, op⟩ := p
    simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h
    cases op <;>
      simp [NarrowOp.sexpr, narrowMask, narrowAmt, narrowRotSExpr,
        SecureCompilation.Ascent.sOrExpr, SecureCompilation.Ascent.sNotExpr, sexprQuiet,
        nodeQuiet, LowCTLeakModel.owned, sexprMnem, DoitRegime.leaksOperands, X86Mnem.timing]

/-- The scalar expressions of the casts and complements are quiet in the owned
    model. -/
theorem narrowUnSExpr_quiet_owned {W : List String} {f a : String} {se : SExpr}
    (h : narrowUnSExpr W f a = some se) : sexprQuiet .owned se = true := by
  unfold narrowUnSExpr at h
  split at h
  · split at h <;> cases h
    simp [narrowMask, sexprQuiet, nodeQuiet, LowCTLeakModel.owned, sexprMnem,
      DoitRegime.leaksOperands, X86Mnem.timing]
  · cases hn : narrowNotOf f with
    | none => simp [hn] at h
    | some w =>
      simp only [hn, Option.map_some, Option.some.injEq] at h
      subst h
      simp [narrowNotSExpr, narrowMask, SecureCompilation.Ascent.sNotExpr, sexprQuiet, nodeQuiet,
        LowCTLeakModel.owned, sexprMnem, DoitRegime.leaksOperands, X86Mnem.timing]

end CatCrypt.Crypto.Hax.ScalarizeCT
