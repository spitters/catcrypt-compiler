/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

/-!
# Deciding the scalar coverage fragments

`IsCoveredS` (straight-line) and `IsCoveredSCtl` (straight-line plus `RFor`,
`RIfNz`, `RLetU64Zero`, `RLetZero`) are the coverage hypotheses of the scalar
front's denotation theorems, including the loop-body step of the rolled and
runtime-trip loops (`frontLoopBodyJ_denote`, `rolledForLoopNRtNested_denote`).
This module gives each a `Bool` test and a soundness lemma, so a concrete body's
coverage is discharged by `decide` over the test.

The only non-structural side condition is `srcClean` on the expression of an
`RScalarSetExpr`. `isTmpName s` is `∃ k, s = tmpName k` and is not decidable as
stated; the decidable sufficient condition is the head character, since every
`tmpName k` is `"__sx" ++ toString k`. Names are tested through `String.toList`,
which the kernel reduces on string literals.

## Main definitions

* `Ascent.notTmpB` / `Ascent.litOkB` / `Ascent.srcCleanB` — the `srcClean` test
* `coveredSB` / `isCoveredS_of_coveredSB` — the straight-line test
* `coveredB` / `isCoveredSCtl_of_coveredB` — the control-extended test
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-- A name is certainly not a fresh temp when its first character is not `'_'`.
    The empty name is not a temp either, every `tmpName` being four characters or
    more. -/
def notTmpB (s : String) : Bool :=
  match s.toList with
  | c :: _ => c != '_'
  | []     => true

/-- Literals below `2 ^ 64` are the `srcClean` leaf condition on constants. -/
def litOkB (n : Nat) : Bool := n < 2 ^ 64

theorem notTmpB_sound (s : String) (h : notTmpB s = true) : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  subst hk
  simp [notTmpB,
    CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms.tmpName] at h

/-- `srcClean`, as a decision procedure (the `notTmpB` head-character test on
    variables, the `2 ^ 64` bound on literals). -/
def srcCleanB : SExpr → Bool
  | .SVar x => notTmpB x
  | .SLit n => litOkB n
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => srcCleanB a && srcCleanB b
  | _ => false

theorem srcCleanB_sound : ∀ (e : SExpr), srcCleanB e = true → srcClean e
  | .SVar x, h => notTmpB_sound x h
  | .SLit _, h => by simpa [srcClean, srcCleanB, litOkB] using h
  | .SAdd a b, h | .SSub a b, h | .SMul a b, h | .SAnd a b, h | .SXor a b, h
  | .SShl a b, h | .SShr a b, h | .SMulHiU a b, h => by
      simp only [srcCleanB, Bool.and_eq_true] at h
      exact ⟨srcCleanB_sound a h.1, srcCleanB_sound b h.2⟩

end CatCrypt.Crypto.SecureCompilation.Ascent

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Ascent (srcCleanB srcCleanB_sound)

/-- The Boolean test for `IsCoveredS`: every arm of the straight-line fragment,
    with `srcCleanB` on the expression of an `RScalarSetExpr`. -/
def coveredSB : LowCT → Bool
  | .RSkip => true
  | .RBlock b => coveredSB b
  | .RSeq a b => coveredSB a && coveredSB b
  | .RScalarSet _ _ => true
  | .RLetU64Zero _ b => coveredSB b
  | .RCall _ _ _ | .RSelect _ _ _ _ | .RCallDstThreaded _ _ _ | .RTupleLoad _ _ _
  | .RArrLoadLit _ _ _ | .RArrStoreLit _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ | .RCallN _ _ _
  | .RArrLoad _ _ _ | .RArrStore _ _ _ | .RAssert _ => true
  | .RScalarSetExpr _ e => srcCleanB e
  | _ => false

theorem isCoveredS_of_coveredSB : ∀ c : LowCT, coveredSB c = true → IsCoveredS c := by
  intro c
  induction c with
  | RSkip => intro _; exact .rSkip
  | RBlock b ih => intro h; exact .rBlock (ih h)
  | RSeq a b iha ihb =>
      intro h; simp only [coveredSB, Bool.and_eq_true] at h
      exact .rSeq (iha h.1) (ihb h.2)
  | RScalarSet x n => intro _; exact .rScalarSet x n
  | RLetU64Zero x b ih => intro h; exact .rLetU64Zero (ih h)
  | RCall f d as => intro _; exact .rCall f d as
  | RSelect d s a b => intro _; exact .rSelect d s a b
  | RCallDstThreaded f d as => intro _; exact .rCallDstThreaded f d as
  | RTupleLoad d s i => intro _; exact .rTupleLoad d s i
  | RArrLoadLit d s i => intro _; exact .rArrLoadLit d s i
  | RArrStoreLit a i s => intro _; exact .rArrStoreLit a i s
  | RCallSwap f d1 d2 as => intro _; exact .rCallSwap f d1 d2 as
  | RCloneCall cv tt od f nd as => intro _; exact .rCloneCall cv tt od f nd as
  | RLimbStore l i v => intro _; exact .rLimbStore l i v
  | RCallN f ds as => intro _; exact .rCallN f ds as
  | RArrLoad d s i => intro _; exact .rArrLoad d s i
  | RArrStore a i s => intro _; exact .rArrStore a i s
  | RAssert l => intro _; exact .rAssert l
  | RScalarSetExpr x e => intro h; exact .rScalarSetExpr x e (srcCleanB_sound e h)
  | _ => intro h; simp [coveredSB] at h

/-- The Boolean test for `IsCoveredSCtl`: the control arms `RSeq` / `RFor` /
    `RIfNz` / `RLetU64Zero` / `RLetZero` over tested bodies, and `coveredSB` on
    every other command. -/
def coveredB : LowCT → Bool
  | .RSeq a b => coveredB a && coveredB b
  | .RFor _ _ b => coveredB b
  | .RIfNz _ t e => coveredB t && coveredB e
  | .RLetU64Zero _ b => coveredB b
  | .RLetZero _ _ b => coveredB b
  | c => coveredSB c

theorem isCoveredSCtl_of_coveredB : ∀ c : LowCT, coveredB c = true → IsCoveredSCtl c := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro h; simp only [coveredB, Bool.and_eq_true] at h
      exact .rSeq (iha h.1) (ihb h.2)
  | RFor x N b ih => intro h; exact .rFor (ih h)
  | RIfNz g t e iht ihe =>
      intro h; simp only [coveredB, Bool.and_eq_true] at h
      exact .rIfNz (iht h.1) (ihe h.2)
  | RLetU64Zero x b ih => intro h; exact .rLetU64Zero (ih h)
  | RLetZero x tt b ih => intro h; exact .rLetZero (ih h)
  | _ => intro h; exact .ofStraight (isCoveredS_of_coveredSB _ h)

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
