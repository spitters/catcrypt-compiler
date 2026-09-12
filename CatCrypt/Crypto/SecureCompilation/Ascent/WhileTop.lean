/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.While
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote

/-!
# The ascent rule for `RWhileNz`, at the unified waist

`Corres` is stated over `semScalar`, which has no `RWhileNz` arm: it reaches the
catch-all `none`, so the `∃ env', step c env = some env'` conclusion is
unsatisfiable on a loop node and a `Corres`-over-`semScalar` loop rule would hold
vacuously.

`semU` does denote the loop node: `semU fuel (.RWhileNz name body)` is the
do-while `semScalarWhile` at the node-derived guard `guardNz name`, by `rfl`.
`CorresU` is `Corres` at that waist, and `corresU_while` is the invariant-carrying
rule over it. The abstract post-state is existentially quantified, because the
trip count is data-dependent and no single abstract function characterises the
loop.

Two facts keep the rule from being vacuous. `corresU_of_corres` transports a
straight-line leaf's `Corres` to `CorresU`, so body correspondences exist; and
the closing `example` exhibits a loop whose run hypothesis holds.

## Main definitions

* `semWhileTop` / `topWhileTrips` — the top-tested loop, where a zero-trip run is
  possible, against `semScalarWhile`'s do-while
* `CorresU` — the correspondence at the unified waist
* `corresU_while` — the invariant-carrying loop rule
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## A. Exit conditions the existing layer does not state -/

theorem semScalarWhile_guard_false
    (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool) :
    ∀ (fuel : Nat) (env env' : SEnvScalar),
      semScalarWhile semBody guard fuel env = some env' → guard env' = false := by
  intro fuel
  induction fuel with
  | zero => intro env env' h; simp [semScalarWhile] at h
  | succ k ih =>
      intro env env' h
      simp only [semScalarWhile] at h
      cases hb : semBody env with
      | none => simp [hb] at h
      | some b =>
          simp only [hb] at h
          by_cases hg : guard b
          · exact ih b env' (by simpa [hg] using h)
          · simp only [Bool.not_eq_true] at hg
            simp only [hg, Bool.false_eq_true, if_false] at h
            obtain rfl := Option.some.inj h
            exact hg

theorem scalarWhileTrips_pos
    (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool) :
    ∀ (fuel : Nat) (env env' : SEnvScalar),
      semScalarWhile semBody guard fuel env = some env' →
      0 < scalarWhileTrips semBody guard fuel env := by
  intro fuel
  cases fuel with
  | zero => intro env env' h; simp [semScalarWhile] at h
  | succ k =>
      intro env env' h
      simp only [semScalarWhile] at h
      simp only [scalarWhileTrips]
      cases hb : semBody env with
      | none => simp [hb] at h
      | some b =>
          by_cases hg : guard b <;> simp [hg]

/-! ## B. The top-tested waist (the `RustExec.whileFalse/whileTrue` shape) -/

/-- Fuel-bounded top-tested `while`: the guard is read on the ENTRY state, so a
    zero-trip run is possible.  This is the shape `RustExec.whileFalse` /
    `RustExec.whileTrue` describe; `semScalarWhile` is a do-while and admits no
    zero-trip run. -/
def semWhileTop (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool) :
    Nat → SEnvScalar → Option SEnvScalar
  | 0, env => if guard env then none else some env
  | k + 1, env =>
      if guard env then (semBody env).bind (semWhileTop semBody guard k) else some env

/-- The data-dependent trip count of the top-tested `while`. -/
def topWhileTrips (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool) :
    Nat → SEnvScalar → Nat
  | 0, _ => 0
  | k + 1, env =>
      if guard env then
        match semBody env with
        | some b => topWhileTrips semBody guard k b + 1
        | none => 0
      else 0

/-- The top-tested loop exits with the guard false. -/
theorem semWhileTop_guard_false
    (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool) :
    ∀ (fuel : Nat) (env env' : SEnvScalar),
      semWhileTop semBody guard fuel env = some env' → guard env' = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro env env' h
      simp only [semWhileTop] at h
      by_cases hg : guard env
      · simp [hg] at h
      · simp only [Bool.not_eq_true] at hg
        simp only [hg, Bool.false_eq_true, if_false, Option.some.injEq] at h
        exact h ▸ hg
  | succ k ih =>
      intro env env' h
      simp only [semWhileTop] at h
      by_cases hg : guard env
      · simp only [hg, if_true] at h
        cases hb : semBody env with
        | none => simp [hb] at h
        | some b => simp only [hb, Option.bind_some] at h; exact ih b env' h
      · simp only [Bool.not_eq_true] at hg
        simp only [hg, Bool.false_eq_true, if_false, Option.some.injEq] at h
        exact h ▸ hg

/-- Fuel/termination bridge for the top-tested loop: a run halting within `fuel`
    equals the unconditional `k`-fold body iteration at the trip count read off
    the run. -/
theorem semWhileTop_eq_iter (semBody : SEnvScalar → Option SEnvScalar)
    (guard : SEnvScalar → Bool) :
    ∀ (fuel : Nat) (env env' : SEnvScalar),
      semWhileTop semBody guard fuel env = some env' →
      semWhileIter semBody (topWhileTrips semBody guard fuel env) env = some env' := by
  intro fuel
  induction fuel with
  | zero =>
      intro env env' h
      simp only [semWhileTop] at h
      by_cases hg : guard env
      · simp [hg] at h
      · simp only [Bool.not_eq_true] at hg
        simp only [hg, Bool.false_eq_true, if_false] at h
        simp only [topWhileTrips, semWhileIter]
        exact h
  | succ k ih =>
      intro env env' h
      simp only [semWhileTop] at h
      simp only [topWhileTrips]
      by_cases hg : guard env
      · simp only [hg, if_true] at h ⊢
        cases hb : semBody env with
        | none => simp [hb] at h
        | some b =>
            simp only [hb, Option.bind_some] at h
            rw [semWhileIter_succ_front, hb]
            exact ih b env' h
      · simp only [Bool.not_eq_true] at hg
        simp only [hg, Bool.false_eq_true, if_false] at h ⊢
        simp only [semWhileIter]
        exact h

/-! ## C. The node-level ascent rule over `semU` -/

/-- `semU` on the loop node is the do-while `semScalarWhile` at the node-derived
    guard `guardNz name`. -/
theorem semU_rWhileNz (fuel : Nat) (name : String) (body : LowCT) (env : SEnvScalar) :
    semU fuel (.RWhileNz name body) env
      = semScalarWhile (fun e => semU fuel body e) (guardNz name) fuel env := rfl

/-- The unified-waist correspondence relation: `Corres`, with `semU` in place of
    `semScalar`.  On a non-`isSeqLike` command `semU fuel c = semScalar c`, so a
    straight-line leaf's `Corres` transports here unchanged. -/
def CorresU {AState : Type} (fuel : Nat) (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) : Prop :=
  ∀ env a, SR env a → P a → ∃ env', semU fuel c env = some env' ∧ SR env' (fa a)

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

/-- Trip-indexed simulation of the loop body at the unified waist. -/
theorem corresU_while_iter {fuel : Nat} {P : AState → Prop} {fb : AState → AState}
    {body : LowCT} (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a)) :
    ∀ env a k env', SR env a → P a →
      semWhileIter (fun e => semU fuel body e) k env = some env' →
      SR env' (kfold fb k a) := by
  intro env a k env' hSR hP
  induction k generalizing env' with
  | zero =>
      intro hrun
      simp only [semWhileIter] at hrun
      obtain rfl := Option.some.inj hrun
      simpa only [kfold] using hSR
  | succ n ih =>
      intro hrun
      simp only [semWhileIter] at hrun
      rcases hpre : semWhileIter (fun e => semU fuel body e) n env with _ | envPre
      · rw [hpre] at hrun; simp at hrun
      · rw [hpre] at hrun
        simp only at hrun
        have hSRpre : SR envPre (kfold fb n a) := ih envPre hpre
        have hPpre : P (kfold fb n a) := kfold_pres hinv n a hP
        obtain ⟨env'', hstep, hSR''⟩ := hbody envPre (kfold fb n a) hSRpre hPpre
        rw [hstep] at hrun
        obtain rfl := Option.some.inj hrun
        simpa only [kfold] using hSR''

/-- **The node-level ascent `while` rule.**  For the loop node
    `.RWhileNz name body` at the unified waist `semU`, from a body correspondence
    whose abstract step `fb` preserves the invariant `P`, any terminating run
    lands in a state related to SOME abstract state satisfying `P`, with the
    node's own guard `guardNz name` false at exit.  The abstract post-state is
    existentially quantified — the trip count is data-dependent, so no single
    abstract function characterises the loop. -/
theorem corresU_while {fuel : Nat} {P : AState → Prop} {fb : AState → AState}
    {name : String} {body : LowCT}
    (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (env : SEnvScalar) (a : AState) (env' : SEnvScalar)
    (hSR : SR env a) (hP : P a)
    (hrun : semU fuel (.RWhileNz name body) env = some env') :
    ∃ a', SR env' a' ∧ P a' ∧ guardNz name env' = false := by
  rw [semU_rWhileNz] at hrun
  refine ⟨kfold fb (scalarWhileTrips (fun e => semU fuel body e) (guardNz name) fuel env) a,
    ?_, ?_, ?_⟩
  · exact corresU_while_iter SR hbody hinv env a _ env' hSR hP
      (semScalarWhile_eq_iter (fun e => semU fuel body e) (guardNz name) fuel env env' hrun)
  · exact kfold_pres hinv _ a hP
  · exact semScalarWhile_guard_false (fun e => semU fuel body e) (guardNz name) fuel env env' hrun

/-- `RSeq` at the unified waist: `semU fuel (RSeq c₁ c₂)` is the bind of the two
    phases, so two `CorresU` phases compose when the first re-establishes the
    second's precondition. -/
theorem corresU_seq {fuel : Nat} {P Q : AState → Prop} {fa ga : AState → AState}
    {c₁ c₂ : LowCT}
    (h₁ : CorresU fuel SR P fa c₁) (h₂ : CorresU fuel SR Q ga c₂) (hpre : ∀ a, P a → Q (fa a)) :
    CorresU fuel SR P (fun a => ga (fa a)) (.RSeq c₁ c₂) := by
  intro env a hSR hP
  obtain ⟨env₁, hstep₁, hSR₁⟩ := h₁ env a hSR hP
  obtain ⟨env₂, hstep₂, hSR₂⟩ := h₂ env₁ (fa a) hSR₁ (hpre a hP)
  exact ⟨env₂, by simp only [semU, hstep₁, Option.bind_some, hstep₂], hSR₂⟩

/-! ## D. Non-vacuity: the hypotheses of `corresU_while` are jointly satisfiable -/

/-- On a leaf that is not one of the five combinator shapes, `semU` is `semScalar`,
    so a `Corres` leaf is a `CorresU` leaf. -/
theorem corresU_of_corres {fuel : Nat} {P : AState → Prop} {fa : AState → AState}
    {c : LowCT} (hne : isSeqLike c = false) (h : Corres SR P fa c) :
    CorresU fuel SR P fa c := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := h env a hSR hP
  refine ⟨env', ?_, hSR'⟩
  -- `semU`'s conditional arm matches only `.RIfNz _ _ .RSkip`; a conditional with
  -- any other else-branch reaches the catch-all, so the else-branch is cased too.
  cases c
  case RIfNz name thenBlk elseBlk => cases elseBlk <;> simp_all [semU, isSeqLike]
  all_goals simp_all [semU, isSeqLike]

/-- The loop `while (n != 0) { n := 0 }` runs, in one trip, from an env where `n`
    is nonzero.  Witness that `semU`'s loop arm returns `some` — the run
    hypothesis of `corresU_while` is satisfiable. -/
example :
    (semU 4 (.RWhileNz "n" (.RScalarSet "n" 0))
      (SEnvScalar.upd (fun _ => none) "n" (t := .sword 64) (7 : BitVec 64))).isSome = true := by
  decide

end CatCrypt.Crypto.SecureCompilation.Ascent
