/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTExitWordOpsValue
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteSeq

/-!
# The value of the exit scalarisation on runtime-count loops

`HaxToLowCTExitWordOpsValue` relates a loop-free output of the typed exit front to its
scalarisation (`ExitScalRel`) and tracks a `RustExec` run of the one by `semScalar` of the
guarded conversion of the other (`exitScal_taken`). This module adds runtime-count loops on
the spine of sequences and word binders: `ExitScalRelL` relates `RForRuntime x b body` to
`RForRuntime x b body'` when the trip bodies are related by `ExitScalRel` and the bound `b` is
a source name or a source name minus a literal (`loopBoundB`). A run is tracked by the
guarded semantics with loops `GuardedRouteSeq.semG`: each trip of the loop by one trip of
`guardedTrips` (`exitLoop_trips`), and every loop-free part as before
(`exitScalL_semG`).

The agreement condition of a run extends to loops trip by trip (`AgreeRunL`), and follows
from the check `setExprsAgreeBL` on the input (`agreeRunL_of_checks`); the Boolean test
`exitScalBL` gives the relation (`exitScalBL_sound`).

## Main definitions

* `loopBoundB` — the loop bounds of the fragment.
* `ExitScalRelL` — a program with runtime-count loops and its scalarisation.
* `readsL`, `AgreeRunL` — the read and agreement conditions of such a program.
* `exitScalBL`, `setExprsAgreeBL` — the Boolean tests on the input of the pass.

## Main results

* `ExitScalRel.loopFreeB_left`, `ExitScalRel.loopFreeB_right`, `ExitScalRelL.toBase` — the
  loop-free parts of the relation.
* `boundVal_eq_evalState` — the trip count of `semG` is the trip count of `RustExec`.
* `exitLoop_trips` — the trip fold tracks the trips of a related loop.
* `exitScalL_semG` — `semG` of the scalarised program tracks a `RustExec` run of the input.
* `exitScalL_inRange`, `agreeRunL_of_checks` — the checks give the agreement condition.
* `exitScalBL_sound` — an input accepted by `exitScalBL I` is related to its scalarisation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
  (EnvBoundOn ScalarInRange envReader_of_envBoundOn envBoundOn_updExpr scalarInRange_upd
    envBoundOn_mono)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop (guardedTrips guardedTripCmd)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteSeq
  (loopFreeB semG boundG boundVal semG_of_loopFree boundG_of_loopFree loopFreeB_of_covered)

/-! ## 1. The relation -/

/-- The loop bounds of the fragment: a source name, or a source name minus a literal. -/
def loopBoundB : SExpr → Bool
  | .SVar n => srcNameB n
  | .SSub (.SVar n) (.SLit _) => srcNameB n
  | _ => false

/-- `ExitScalRelL c c'`: `c'` is the scalarisation of `c`, where `c` is built from loop-free
    parts related by `ExitScalRel` by sequences, word binders and runtime-count loops whose
    trip bodies are related by `ExitScalRel`. -/
inductive ExitScalRelL : LowCT → LowCT → Prop
  | base {c c' : LowCT} : ExitScalRel c c' → ExitScalRelL c c'
  | seq {a a' b b' : LowCT} : ExitScalRelL a a' → ExitScalRelL b b' →
      ExitScalRelL (.RSeq a b) (.RSeq a' b')
  | letU64Zero {x : String} {b b' : LowCT} (hx : srcName x) : ExitScalRelL b b' →
      ExitScalRelL (.RLetU64Zero x b) (.RLetU64Zero x b')
  | loop {x : String} {bd : SExpr} {body body' : LowCT} (hx : srcName x)
      (hb : loopBoundB bd = true) : ExitScalRel body body' →
      ExitScalRelL (.RForRuntime x bd body) (.RForRuntime x bd body')

theorem ExitScalRel.loopFreeB_right {c c' : LowCT} (h : ExitScalRel c c') :
    loopFreeB c' = true :=
  loopFreeB_of_covered h.covered.1

theorem loopFreeB_of_marshalOk (k : LowCT) (h : marshalOk k = true) : loopFreeB k = true := by
  fun_induction marshalOk k with
  | case1 _ _ _ _ _ _ ih =>
      simp only [Bool.and_eq_true] at h
      simp [loopFreeB, ih h.2]
  | case2 => rfl
  | case3 => simp_all

theorem ExitScalRel.loopFreeB_left {c c' : LowCT} (h : ExitScalRel c c') :
    loopFreeB c = true := by
  induction h <;> simp_all [loopFreeB, loopFreeB_of_marshalOk]

/-- A loop-free scalarisation of the relation with loops is one of the loop-free relation. -/
theorem ExitScalRelL.toBase {c c' : LowCT} (h : ExitScalRelL c c') (hf : loopFreeB c' = true) :
    ExitScalRel c c' := by
  induction h with
  | base h => exact h
  | seq _ _ iha ihb =>
      simp only [loopFreeB, Bool.and_eq_true] at hf
      exact .seq (iha hf.1) (ihb hf.2)
  | letU64Zero hx _ ih =>
      simp only [loopFreeB] at hf
      exact .letU64Zero hx (ih hf)
  | loop => simp [loopFreeB] at hf

/-! ## 2. Reads and agreement -/

/-- The reads of a program with loops are bound: `readsG` on its loop-free parts, and on a
    loop the variables of the bound and the reads of the trip body with the index bound. -/
def readsL (B : String → Prop) : LowCT → Prop
  | .RSeq a b => readsL B a ∧ readsL (afterG B a) b
  | .RLetU64Zero x b => readsL (fun y => B y ∨ y = x) b
  | .RForRuntime x bd body => varsIn B bd ∧ readsG (fun y => B y ∨ y = x) body
  | c => readsG B c

theorem readsG_of_readsL : ∀ {c : LowCT} {B : String → Prop}, loopFreeB c = true →
    readsL B c → readsG B c := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro B hf h
      simp only [loopFreeB, Bool.and_eq_true] at hf
      exact ⟨iha hf.1 h.1, ihb hf.2 h.2⟩
  | RLetU64Zero x b ih =>
      intro B hf h
      exact ih hf h
  | RForRuntime => intro _ hf; simp [loopFreeB] at hf
  | _ => intro _ _ h; exact h

/-- The agreement condition of a run of a program with loops: `AgreeRun` on its loop-free
    parts, and on a loop a trip count of at most `2^64` and `AgreeRun` of the trip body at the
    entry state of every trip. -/
def AgreeRunL (N : Nat) (L : LeafSpec) : LowCT → RustState → Prop
  | .RSeq a b, rs => AgreeRunL N L a rs ∧ ∀ r1, RustExec N L a rs r1 → AgreeRunL N L b r1
  | .RLetU64Zero x b, rs => AgreeRunL N L b (rsSetScalar rs x 0)
  | .RForRuntime x bd body, rs => bd.evalState rs ≤ 2 ^ 64 ∧
      ∀ t, t < bd.evalState rs → ∀ r, RustExec N L (.RFor x t body) rs r →
        AgreeRun N L body (rsSetScalar r x t)
  | c, rs => AgreeRun N L c rs

theorem agreeRun_of_agreeRunL {N : Nat} {L : LeafSpec} : ∀ {c : LowCT} {rs : RustState},
    loopFreeB c = true → AgreeRunL N L c rs → AgreeRun N L c rs := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs hf h
      simp only [loopFreeB, Bool.and_eq_true] at hf
      exact ⟨iha hf.1 h.1, fun r1 hr1 => ihb hf.2 (h.2 r1 hr1)⟩
  | RLetU64Zero x b ih =>
      intro rs hf h
      exact ih hf h
  | RForRuntime => intro _ hf; simp [loopFreeB] at hf
  | _ => intro _ _ h; exact h

theorem agreeRunL_of_agreeRun {N : Nat} {L : LeafSpec} : ∀ {c : LowCT} {rs : RustState},
    loopFreeB c = true → AgreeRun N L c rs → AgreeRunL N L c rs := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs hf h
      simp only [loopFreeB, Bool.and_eq_true] at hf
      exact ⟨iha hf.1 h.1, fun r1 hr1 => ihb hf.2 (h.2 r1 hr1)⟩
  | RLetU64Zero x b ih =>
      intro rs hf h
      exact ih hf h
  | RForRuntime => intro _ hf; simp [loopFreeB] at hf
  | _ => intro _ _ h; exact h

/-! ## 3. The trip count -/

theorem srcName_of_loopBoundB {bd : SExpr} (h : loopBoundB bd = true) :
    ∃ n, srcName n ∧ (bd = .SVar n ∨ ∃ m, bd = .SSub (.SVar n) (.SLit m)) := by
  match bd, h with
  | .SVar n, h => exact ⟨n, srcName_of_srcNameB h, Or.inl rfl⟩
  | .SSub (.SVar n) (.SLit m), h => exact ⟨n, srcName_of_srcNameB h, Or.inr ⟨m, rfl⟩⟩

/-- The trip count of a loop bound is at most the word its name holds. -/
theorem evalState_le_of_loopBoundB {bd : SExpr} (h : loopBoundB bd = true) {rs : RustState}
    (hir : ScalarInRange rs) : bd.evalState rs < 2 ^ 64 := by
  obtain ⟨n, -, rfl | ⟨m, rfl⟩⟩ := srcName_of_loopBoundB h
  · exact hir n
  · simp only [SExpr.evalState]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (hir n)

/-- **The trip count of `semG` is the trip count of `RustExec`.** -/
theorem boundVal_eq_evalState {bd : SExpr} (h : loopBoundB bd = true) {B : String → Prop}
    (hv : varsIn B bd) {rs : RustState} {env : SEnvScalar} (henv : EnvBoundOn rs env B)
    (hir : ScalarInRange rs) : boundVal bd env = bd.evalState rs := by
  obtain ⟨n, hn, rfl | ⟨m, rfl⟩⟩ := srcName_of_loopBoundB h
  · simp only [boundVal, SExpr.eval, SExpr.evalState,
      envReader_of_envBoundOn henv n hv hn.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir n)]
  · simp only [boundVal, SExpr.eval, SExpr.evalState,
      envReader_of_envBoundOn henv n hv.1 hn.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir n)]

/-! ## 4. The simulation -/

/-- **The trip fold tracks the trips of a related loop.** For trip bodies related by
    `ExitScalRel` and reading names of `B` and the index, `n ≤ 2^64` trips of a `RustExec` run
    of `RFor x n body`, each satisfying the agreement condition, from a state reflected on `B`
    by `env`, are tracked by `n` trips of `guardedTrips x S body'`. -/
theorem exitLoop_trips {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {body body' : LowCT}
    (hrel : ExitScalRel body body') {x : String} {S : List String} {B : String → Prop}
    (hx : srcName x) (hS : SrcList S) (hB : ∀ y, B y → y ∈ S)
    (hreads : readsG (fun y => B y ∨ y = x) body') {rs : RustState} {env : SEnvScalar} :
    ∀ (n : Nat) {rs' : RustState}, n ≤ 2 ^ 64 → RustExec N L (.RFor x n body) rs rs' →
      (∀ t, t < n → ∀ r, RustExec N L (.RFor x t body) rs r →
        AgreeRun N L body (rsSetScalar r x t)) →
      EnvBoundOn rs env B → Bound env S → ScalarInRange rs →
      ∃ env', guardedTrips x S body' n env = some env' ∧ EnvBoundOn rs' env' B ∧
        Bound env' S ∧ ScalarInRange rs'
  | 0, _, _, hexec, _, henv, hb, hir => by
      cases hexec
      exact ⟨env, rfl, henv, hb, hir⟩
  | n + 1, _, hn, hexec, hag, henv, hb, hir => by
      cases hexec with
      | forSucc _ _ _ _ r₁ _ hf hbd =>
          obtain ⟨e₁, he₁, henv₁, hb₁, hir₁⟩ := exitLoop_trips hL hrel hx hS hB hreads n
            (by omega) hf (fun t ht r hr => hag t (by omega) r hr) henv hb hir
          have hb0 : Bound (e₁.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (x :: S) := by
            intro y hy
            by_cases hyx : y = x
            · subst hyx; rw [readU64_of_env upd_self]; rfl
            · rw [readU64_eq_of_env (upd_ne hyx)]
              exact hb₁ y (List.mem_of_ne_of_mem hyx hy)
          have henv0 : EnvBoundOn (rsSetScalar r₁ x n)
              (e₁.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (fun y => B y ∨ y = x) := by
            intro y hy hnt
            by_cases hyx : y = x
            · subst hyx; rw [upd_self]; simp [rsSetScalar]
            · rw [upd_ne hyx, henv₁ y (hy.resolve_right hyx) hnt]
              simp [rsSetScalar, hyx]
          obtain ⟨env', hs, henv', hir', hbd', -⟩ :=
            exitScal_taken hL hrel none (x :: S) 0 (fun y => B y ∨ y = x) (rsSetScalar r₁ x n)
              _ _ hbd (hag n (by omega) r₁ hf) hreads (fun _ h => by cases h)
              (srcList_cons hx hS) hb0 (sub_cons x hB) henv0
              (scalarInRange_upd hir₁ x (by omega))
          obtain ⟨_, hsubS, _, _⟩ := ifConvert_static hrel.covered.1 none (x :: S) 0
            (fun y => B y ∨ y = x) (srcList_cons hx hS) (sub_cons x hB)
          refine ⟨env', ?_, envBoundOn_mono henv' (fun y hy => le_afterG body' _ y (Or.inl hy)),
            fun y hy => hbd' y (hsubS y (List.mem_cons_of_mem _ hy)), hir'⟩
          simp only [guardedTrips, he₁, Option.bind_some]
          exact hs

/-- The loop-free case of `exitScalL_semG`. -/
theorem exitScal_semG {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {c c' : LowCT}
    (h : ExitScalRel c c') (S : List String) (B : String → Prop) (rs rs' : RustState)
    (env : SEnvScalar) (hexec : RustExec N L c rs rs') (hag : AgreeRunL N L c rs)
    (hr : readsL B c') (hS : SrcList S) (hb : Bound env S) (hB : ∀ y, B y → y ∈ S)
    (henv : EnvBoundOn rs env B) (hir : ScalarInRange rs) :
    ∃ env', semG S c' env = some env' ∧ EnvBoundOn rs' env' (afterG B c') ∧
      ScalarInRange rs' ∧ Bound env' (boundG S c') ∧ SrcList (boundG S c') ∧
      (∀ y, afterG B c' y → y ∈ boundG S c') := by
  obtain ⟨env', hs, henv', hir', hb', -⟩ := exitScal_taken hL h none S 0 B rs rs' env hexec
    (agreeRun_of_agreeRunL h.loopFreeB_left hag) (readsG_of_readsL h.loopFreeB_right hr)
    (fun _ h => by cases h) hS hb hB henv hir
  obtain ⟨hSa, -, hBa, -⟩ := ifConvert_static h.covered.1 none S 0 B hS hB
  rw [semG_of_loopFree h.loopFreeB_right, boundG_of_loopFree h.loopFreeB_right]
  exact ⟨env', hs, henv', hir', hb', hSa, hBa⟩

/-- **`semG` of the scalarised program tracks the input's run.** A `RustExec` run of `c`
    satisfying the agreement condition `AgreeRunL`, from a state whose scalars are words and
    which `env` reflects on the names `B ⊆ S`, is tracked by `semG S c'`: its output
    environment binds every name bound after `c'` to the word of its output value, and binds
    the bound list after `c'`. -/
theorem exitScalL_semG {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {c c' : LowCT}
    (h : ExitScalRelL c c') :
    ∀ (S : List String) (B : String → Prop) (rs rs' : RustState) (env : SEnvScalar),
      RustExec N L c rs rs' → AgreeRunL N L c rs → readsL B c' → SrcList S → Bound env S →
      (∀ y, B y → y ∈ S) → EnvBoundOn rs env B → ScalarInRange rs →
      ∃ env', semG S c' env = some env' ∧ EnvBoundOn rs' env' (afterG B c') ∧
        ScalarInRange rs' ∧ Bound env' (boundG S c') ∧ SrcList (boundG S c') ∧
        (∀ y, afterG B c' y → y ∈ boundG S c') := by
  induction h with
  | base h => exact exitScal_semG hL h
  | @seq a a' b b' hab hbb iha ihb =>
      intro S B rs rs' env hexec hag hr hS hb hB henv hir
      by_cases hf : loopFreeB (.RSeq a' b') = true
      · exact exitScal_semG hL ((ExitScalRelL.seq hab hbb).toBase hf) S B rs rs' env hexec hag
          hr hS hb hB henv hir
      · have hf' : (loopFreeB a' && loopFreeB b') = false := by
          simpa [loopFreeB] using hf
        cases hexec with
        | seq _ _ _ r1 _ h1 h2 =>
            obtain ⟨e₁, hs₁, henv₁, hir₁, hb₁, hS₁, hB₁⟩ :=
              iha S B rs r1 env h1 hag.1 hr.1 hS hb hB henv hir
            obtain ⟨e₂, hs₂, henv₂, hir₂, hb₂, hS₂, hB₂⟩ :=
              ihb (boundG S a') (afterG B a') r1 rs' e₁ h2 (hag.2 r1 h1) hr.2 hS₁ hb₁ hB₁ henv₁
                hir₁
            refine ⟨e₂, ?_, henv₂, hir₂, ?_, ?_, ?_⟩
            · simp only [semG, hf', Bool.false_eq_true, if_false, hs₁, Option.bind_some]
              exact hs₂
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hb₂
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hS₂
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hB₂
  | @letU64Zero x b b' hx hbb ih =>
      intro S B rs rs' env hexec hag hr hS hb hB henv hir
      by_cases hf : loopFreeB b' = true
      · exact exitScal_semG hL ((ExitScalRelL.letU64Zero hx hbb).toBase (by simpa [loopFreeB]))
          S B rs rs' env hexec hag hr hS hb hB henv hir
      · have hf' : loopFreeB b' = false := by simpa using hf
        cases hexec with
        | letU64Zero _ _ _ _ hbody =>
            obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit 0) (S := S) (flag := none)
              (k := 0) (fun _ h => by cases h) hx (show (0 : Nat) < 2 ^ 64 by decide) trivial hb
            obtain ⟨hb1, -⟩ :=
              write_facts (w := (SExpr.SLit 0).evalBV (envReader env)) hotb hx hS hb
            have henv1 := envBoundOn_updExpr henv hotb x 0
            obtain ⟨env3, hs3, henv3, hir3, hb3, hS3, hB3⟩ :=
              ih (x :: S) (fun y => B y ∨ y = x) _ rs' _ hbody hag hr (srcList_cons hx hS) hb1
                (sub_cons x hB) henv1 (scalarInRange_upd hir x (by norm_num))
            refine ⟨env3, ?_, henv3, hir3, ?_, ?_, ?_⟩
            · simp only [semG, hf', Bool.false_eq_true, if_false, hs2, Option.bind_some]
              exact hs3
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hb3
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hS3
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hB3
  | @loop x bd body body' hx hbd hrel =>
      intro S B rs rs' env hexec hag hr hS hb hB henv hir
      have hcnt := boundVal_eq_evalState hbd hr.1 henv hir
      cases hexec with
      | forRuntime _ _ _ _ _ hf =>
          obtain ⟨env', hs, henv', hb', hir'⟩ := exitLoop_trips hL hrel hx hS hB hr.2
            (bd.evalState rs) hag.1 hf hag.2 henv hb hir
          refine ⟨env', ?_, henv', hir', hb', hS, hB⟩
          simp only [semG, hcnt]
          exact hs

/-! ## 5. The checks -/

/-- The expression check of a program with loops: `setExprsAgreeB` on its loop-free parts and
    on every trip body. -/
def setExprsAgreeBL : LowCT → Bool
  | .RSeq a b => setExprsAgreeBL a && setExprsAgreeBL b
  | .RLetU64Zero _ b => setExprsAgreeBL b
  | .RForRuntime _ _ body => setExprsAgreeB body
  | c => setExprsAgreeB c

theorem setExprsAgreeB_of_L : ∀ {c : LowCT}, loopFreeB c = true → setExprsAgreeBL c = true →
    setExprsAgreeB c = true := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro hf h
      simp only [loopFreeB, setExprsAgreeBL, Bool.and_eq_true] at hf h
      simp only [setExprsAgreeB, iha hf.1 h.1, ihb hf.2 h.2, Bool.and_self]
  | RLetU64Zero x b ih =>
      intro hf h
      exact ih hf h
  | RForRuntime => intro hf; simp [loopFreeB] at hf
  | _ => intro _ h; exact h

/-- A run of `RFor x n body` over related trip bodies whose expressions agree keeps the
    scalars words, when every counter value is a word. -/
theorem rFor_inRange {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {body body' : LowCT}
    (hrel : ExitScalRel body body') (hB : setExprsAgreeB body = true) {x : String} :
    ∀ (n : Nat) {rs r : RustState}, n ≤ 2 ^ 64 → RustExec N L (.RFor x n body) rs r →
      ScalarInRange rs → ScalarInRange r
  | 0, _, _, _, h, hir => by cases h; exact hir
  | n + 1, _, _, hn, h, hir => by
      cases h with
      | forSucc _ _ _ _ r₁ _ hf hb =>
          exact exitScal_inRange hL hrel hB _ _ hb
            (scalarInRange_upd (rFor_inRange hL hrel hB n (by omega) hf hir) x (by omega))

/-- A run of a related input whose expressions agree keeps the scalars words. -/
theorem exitScalL_inRange {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {c c' : LowCT}
    (h : ExitScalRelL c c') :
    setExprsAgreeBL c = true → ∀ rs r, RustExec N L c rs r → ScalarInRange rs →
      ScalarInRange r := by
  induction h with
  | base h =>
      intro ha rs r hr hir
      exact exitScal_inRange hL h (setExprsAgreeB_of_L h.loopFreeB_left ha) rs r hr hir
  | seq _ _ iha ihb =>
      intro ha rs r hr hir
      simp only [setExprsAgreeBL, Bool.and_eq_true] at ha
      cases hr with
      | seq _ _ _ r1 _ h1 h2 => exact ihb ha.2 r1 r h2 (iha ha.1 rs r1 h1 hir)
  | letU64Zero hx _ ih =>
      intro ha rs r hr hir
      cases hr with
      | letU64Zero _ _ _ _ hb => exact ih ha _ r hb (scalarInRange_upd hir _ (by norm_num))
  | loop hx hbd hrel =>
      intro ha rs r hr hir
      cases hr with
      | forRuntime _ _ _ _ _ hf =>
          exact rFor_inRange hL hrel ha _ (evalState_le_of_loopBoundB hbd hir).le hf hir

/-- **The agreement condition from the checks.** For a related input whose expressions pass
    `setExprsAgreeBL`, every run from a state whose scalars are words satisfies
    `AgreeRunL`. -/
theorem agreeRunL_of_checks {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {c c' : LowCT}
    (h : ExitScalRelL c c') :
    setExprsAgreeBL c = true → ∀ rs, ScalarInRange rs → AgreeRunL N L c rs := by
  induction h with
  | base h =>
      intro ha rs hir
      exact agreeRunL_of_agreeRun h.loopFreeB_left
        (agreeRun_of_setExprsAgreeB hL h (setExprsAgreeB_of_L h.loopFreeB_left ha) rs hir)
  | @seq a a' b b' hab _ iha ihb =>
      intro ha rs hir
      simp only [setExprsAgreeBL, Bool.and_eq_true] at ha
      exact ⟨iha ha.1 rs hir, fun r1 hr1 =>
        ihb ha.2 r1 (exitScalL_inRange hL hab ha.1 rs r1 hr1 hir)⟩
  | letU64Zero hx _ ih =>
      intro ha rs hir
      exact ih ha _ (scalarInRange_upd hir _ (by norm_num))
  | @loop x bd body body' hx hbd hrel =>
      intro ha rs hir
      have hlt := evalState_le_of_loopBoundB hbd hir
      refine ⟨hlt.le, fun t ht r hr => ?_⟩
      exact agreeRun_of_setExprsAgreeB hL hrel ha _
        (scalarInRange_upd (rFor_inRange hL hrel ha t (by omega) hr hir) x (by omega))

/-- The Boolean test on the input of `scalarizeExitIn W I` for programs with loops: accepted
    by `exitScalB I`, or a sequence or word binder of accepted parts, or a runtime-count loop
    over a source-name index with a bound of `loopBoundB` and a trip body accepted by
    `exitScalB I`. -/
def exitScalBL (I : List String) : LowCT → Bool
  | .RSeq a b => exitScalB I (.RSeq a b) || (exitScalBL I a && exitScalBL I b)
  | .RLetU64Zero x b => exitScalB I (.RLetU64Zero x b) || (srcNameB x && exitScalBL I b)
  | .RForRuntime x bd body => srcNameB x && loopBoundB bd && exitScalB I body
  | c => exitScalB I c

theorem exitScalB_letZero {I : List String} {x : String} {t : TowerType} {b : LowCT} :
    exitScalB I (.RLetZero x t b) = false := by
  simp [exitScalB]

/-- **The pass on an accepted input with loops.** An input accepted by `exitScalBL I` is
    related by `ExitScalRelL` to its lowering `scalarizeExitIn W I c`. -/
theorem exitScalBL_sound (W I : List String) :
    ∀ c : LowCT, exitScalBL I c = true → ExitScalRelL c (scalarizeExitIn W I c) := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro h
      simp only [exitScalBL, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨ha, hb⟩
      · exact .base (exitScalB_sound W I _ h)
      · have hsplit : scalarizeExitIn W I (.RSeq a b) =
            .RSeq (scalarizeExitIn W I a) (scalarizeExitIn W I b) := by
          rw [scalarizeExitIn.eq_def]
          split
          · rename_i c₀ dr₀ k₀ n₀ c₀' b₀ heq
            simp only [LowCT.RSeq.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            simp [exitScalBL, exitScalB_letZero] at ha
          all_goals simp_all
        rw [hsplit]
        exact .seq (iha ha) (ihb hb)
  | RLetU64Zero x b ih =>
      intro h
      simp only [exitScalBL, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hx, hb⟩
      · exact .base (exitScalB_sound W I _ h)
      · simp only [scalarizeExitIn]
        exact .letU64Zero (srcName_of_srcNameB hx) (ih hb)
  | RForRuntime x bd body =>
      intro h
      simp only [exitScalBL, Bool.and_eq_true] at h
      obtain ⟨⟨hx, hbd⟩, hb⟩ := h
      simp only [scalarizeExitIn]
      exact .loop (srcName_of_srcNameB hx) hbd (exitScalB_sound W I body hb)
  | _ => intro h; exact .base (exitScalB_sound W I _ h)

end CatCrypt.Crypto.Hax
