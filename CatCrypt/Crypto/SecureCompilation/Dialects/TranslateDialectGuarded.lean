/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt

/-!
# The guarded translator: conditionals as branch-free guarded writes

`translateDialectControl` compiles `RIfNz` as a conditional only for two single
`RScalarSet` on one slot, and `semScalar` follows it. The guarded translator
compiles every `RIfNz` of the fragment `IsCoveredSCtlGuarded` (scalar writes,
`RLetU64Zero`, `RSeq`, `RSkip` and `RIfNz`, over expressions that may contain
`SLt`) through a conversion `ifConvert` into straight-line code, and then through
`translateDialectControl`.

The conversion of `RIfNz g t e` under a guard flag `f` (a slot holding `0` or
`1`, absent at top level) computes the flags `ft := f * (0 < g)` and
`fe := f * (1 - (0 < g))` into the fresh slots `guardName k` and
`guardName (k + 1)`, then converts both branches, `t` under `ft` and `e` under
`fe`. Under a flag, every write `x := v` of either branch becomes the merge
`x := x + f * (v - x)` when `x` is bound before it (the list `S`), and
`x := f * v` otherwise; so the branch whose flag is `0` leaves every bound slot
unchanged. `SLt` is replaced by `GuardedLt.ltExpr`. The output lies in the
straight-line covered fragment `IsCoveredS`, so the denotation theorem of
`translateDialectControl` applies to it.

## Main definitions

* `guardName`, `srcName`: the flag slots and the source names
* `gWrite`, `ifConvert`: the guarded write and the conversion
* `IsCoveredSCtlGuarded`: the guarded fragment
* `translateDialectGuarded`, `semScalarGuarded`: the translator and its scalar
  semantics
* `coveredGuardedB`: the Boolean test for the fragment

## Main results

* `ifConvert_covered`: the conversion lands in `IsCoveredS`
* `translateDialectGuarded_denote`: the emitted prefix denotes the
  `semScalarGuarded` run
* `isCoveredSCtlGuarded_of_coveredGuardedB`: soundness of the Boolean test
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt

/-! ## Guard flag slots -/

/-- The `k`-th guard flag slot. -/
def guardName (k : Nat) : String := "__gf" ++ toString k

/-- A name is a guard flag slot. -/
def isGuardName (s : String) : Prop := ∃ k, s = guardName k

/-- A source name: neither a lowering temporary nor a guard flag slot. -/
def srcName (s : String) : Prop := ¬ isTmpName s ∧ ¬ isGuardName s

theorem guardName_injective : Function.Injective guardName := by
  intro a b h
  unfold guardName at h
  simp only [String.append_right_inj] at h
  exact repr_injective (by simpa [toString] using h)

theorem not_isTmpName_guardName (k : Nat) : ¬ isTmpName (guardName k) := by
  rintro ⟨j, h⟩
  have := congrArg (fun s => s.toList.take 4) h
  simp [TranslateDialectDirectArms.tmpName, guardName] at this

theorem srcName_ne_guardName {s : String} (hs : srcName s) (k : Nat) : s ≠ guardName k :=
  fun h => hs.2 ⟨k, h⟩

/-! ## The guarded conversion -/

/-- Multiply an expression by the flag slot, when there is one. -/
def andFlag : Option String → SExpr → SExpr
  | none, e => e
  | some f, e => .SMul (.SVar f) e

/-- The write of `v` into `x` under the guard flag: unconditional without a flag;
    under flag `f` the merge `x + f * (v - x)` when `x` is in the bound list `S`,
    and `f * v` otherwise. -/
def gWrite (flag : Option String) (S : List String) (x : String) (v : SExpr) : LowCT :=
  match flag with
  | none => .RScalarSetExpr x v
  | some f =>
      if x ∈ S then .RScalarSetExpr x (.SAdd (.SVar x) (.SMul (.SVar f) (.SSub v (.SVar x))))
      else .RScalarSetExpr x (.SMul (.SVar f) v)

/-- The nonzero test `0 < g` of a guard slot. -/
def nzExpr (g : String) : SExpr := ltExpr (.SLit 0) (.SVar g)

/-- The guarded conversion: `ifConvert flag S k c` is the straight-line command,
    the bound list after it, and the next free flag index. -/
def ifConvert : Option String → List String → Nat → LowCT → LowCT × List String × Nat
  | _, S, k, .RSkip => (.RSkip, S, k)
  | flag, S, k, .RSeq a b =>
      let ra := ifConvert flag S k a
      let rb := ifConvert flag ra.2.1 ra.2.2 b
      (.RSeq ra.1 rb.1, rb.2.1, rb.2.2)
  | flag, S, k, .RLetU64Zero x b =>
      let rb := ifConvert flag (x :: S) k b
      (.RSeq (gWrite flag S x (.SLit 0)) rb.1, rb.2.1, rb.2.2)
  | flag, S, k, .RScalarSet x n => (gWrite flag S x (.SLit n), x :: S, k)
  | flag, S, k, .RScalarSetExpr x e => (gWrite flag S x (elimLt e), x :: S, k)
  | flag, S, k, .RIfNz g t e =>
      let rt := ifConvert (some (guardName k)) S (k + 2) t
      let re := ifConvert (some (guardName (k + 1))) rt.2.1 rt.2.2 e
      (.RSeq (.RScalarSetExpr (guardName k) (andFlag flag (nzExpr g)))
        (.RSeq (.RScalarSetExpr (guardName (k + 1))
            (andFlag flag (.SSub (.SLit 1) (nzExpr g))))
          (.RSeq rt.1 re.1)), re.2.1, re.2.2)
  | _, S, k, c => (c, S, k)

/-- The guarded fragment: scalar writes and `RLetU64Zero` on source names,
    `RSeq`, `RSkip`, and `RIfNz` on a source guard, over `ltClean` expressions
    reading source names. -/
inductive IsCoveredSCtlGuarded : LowCT → Prop
  | rSkip : IsCoveredSCtlGuarded .RSkip
  | rSeq {a b : LowCT} : IsCoveredSCtlGuarded a → IsCoveredSCtlGuarded b →
      IsCoveredSCtlGuarded (.RSeq a b)
  | rLetU64Zero {x : String} {b : LowCT} (hx : srcName x) :
      IsCoveredSCtlGuarded b → IsCoveredSCtlGuarded (.RLetU64Zero x b)
  | rScalarSet {x : String} {n : Nat} (hx : srcName x) (hn : n < 2 ^ 64) :
      IsCoveredSCtlGuarded (.RScalarSet x n)
  | rScalarSetExpr {x : String} {e : SExpr} (hx : srcName x) (he : ltClean e)
      (hv : varsIn srcName e) : IsCoveredSCtlGuarded (.RScalarSetExpr x e)
  | rIfNz {g : String} {t e : LowCT} (hg : srcName g) :
      IsCoveredSCtlGuarded t → IsCoveredSCtlGuarded e → IsCoveredSCtlGuarded (.RIfNz g t e)

theorem srcClean_nzExpr {g : String} (hg : ¬ isTmpName g) : srcClean (nzExpr g) := by
  simp only [nzExpr, ltExpr, carryExpr, srcClean]
  exact ⟨⟨⟨⟨hg, by decide⟩, ⟨⟨by decide, by decide⟩, by decide⟩⟩,
    ⟨⟨hg, by decide⟩, ⟨⟨by decide, by decide⟩, by decide⟩⟩⟩, by decide⟩

theorem srcClean_andFlag {flag : Option String} {e : SExpr}
    (hf : ∀ f, flag = some f → ¬ isTmpName f) (he : srcClean e) :
    srcClean (andFlag flag e) := by
  cases flag with
  | none => exact he
  | some f => exact ⟨hf f rfl, he⟩

theorem gWrite_covered {flag : Option String} {S : List String} {x : String} {v : SExpr}
    (hf : ∀ f, flag = some f → ¬ isTmpName f) (hx : ¬ isTmpName x) (hv : srcClean v) :
    IsCoveredS (gWrite flag S x v) := by
  cases flag with
  | none => exact .rScalarSetExpr x v hv
  | some f =>
      simp only [gWrite]
      split_ifs
      · exact .rScalarSetExpr x _ ⟨hx, hf f rfl, hv, hx⟩
      · exact .rScalarSetExpr x _ ⟨hf f rfl, hv⟩

/-- The conversion of a guarded-fragment command is straight-line covered. -/
theorem ifConvert_covered {c : LowCT} (hc : IsCoveredSCtlGuarded c) :
    ∀ (flag : Option String) (S : List String) (k : Nat),
      (∀ f, flag = some f → ¬ isTmpName f) → IsCoveredS (ifConvert flag S k c).1 := by
  induction hc with
  | rSkip => intro _ _ _ _; exact .rSkip
  | rSeq _ _ iha ihb =>
      intro flag S k hf
      simp only [ifConvert]
      exact .rSeq (iha flag S k hf) (ihb _ _ _ hf)
  | rLetU64Zero hx _ ihb =>
      intro flag S k hf
      simp only [ifConvert]
      exact .rSeq (gWrite_covered hf hx.1 (show (0 : Nat) < 2 ^ 64 by decide)) (ihb _ _ _ hf)
  | rScalarSet hx hn =>
      intro flag S k hf
      exact gWrite_covered hf hx.1 hn
  | rScalarSetExpr hx he _ =>
      intro flag S k hf
      exact gWrite_covered hf hx.1 (srcClean_elimLt _ he)
  | rIfNz hg _ _ iht ihe =>
      intro flag S k hf
      simp only [ifConvert]
      refine .rSeq (.rScalarSetExpr _ _ (srcClean_andFlag hf (srcClean_nzExpr hg.1)))
        (.rSeq (.rScalarSetExpr _ _ (srcClean_andFlag hf
          ⟨show (1 : Nat) < 2 ^ 64 by decide, srcClean_nzExpr hg.1⟩))
          (.rSeq (iht _ _ _ ?_) (ihe _ _ _ ?_)))
      · intro f hf'; cases hf'; exact not_isTmpName_guardName _
      · intro f hf'; cases hf'; exact not_isTmpName_guardName _

/-! ## The translator and its denotation -/

/-- The straight-line command the guarded translator compiles. -/
def guardedCmd (c : LowCT) : LowCT := (ifConvert none [] 0 c).1

/-- The guarded translator: `translateDialectControl` on the guarded conversion. -/
def translateDialectGuarded {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) : Option (DTransOut Γ) :=
  translateDialectControl vm (guardedCmd c)

/-- The scalar semantics of the guarded fragment: `semScalar` on the guarded
    conversion. -/
def semScalarGuarded (c : LowCT) (env : SEnvScalar) : Option SEnvScalar :=
  semScalar (guardedCmd c) env

theorem guardedCmd_covered {c : LowCT} (hc : IsCoveredSCtlGuarded c) :
    IsCoveredSCtl (guardedCmd c) :=
  .ofStraight (ifConvert_covered hc none [] 0 (fun _ h => by cases h))

/-- The denotation theorem of the guarded translator: the emitted prefix denotes
    the `semScalarGuarded` run. -/
theorem translateDialectGuarded_denote {c : LowCT} (hc : IsCoveredSCtlGuarded c)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hcons : ConsistentS vm V env) (htr : translateDialectGuarded vm c = some o)
    (hsem : semScalarGuarded c env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  translateDialectControl_denote_ctl (guardedCmd_covered hc) vm V env env' o hcons htr hsem

/-! ## A Boolean test for the fragment -/

/-- A name whose first four characters are neither `__sx` nor `__gf`. -/
def srcNameB (s : String) : Bool :=
  s.toList.take 4 != "__sx".toList && s.toList.take 4 != "__gf".toList

theorem srcName_of_srcNameB {s : String} (h : srcNameB s = true) : srcName s := by
  simp only [srcNameB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨?_, ?_⟩
  · rintro ⟨k, rfl⟩
    exact h.1 (by simp [TranslateDialectDirectArms.tmpName])
  · rintro ⟨k, rfl⟩
    exact h.2 (by simp [guardName])

/-- The Boolean test for `ltClean e ∧ varsIn srcName e`. -/
def ltCleanSrcB : SExpr → Bool
  | .SVar x => srcNameB x
  | .SLit n => decide (n < 2 ^ 64)
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b | .SLt a b => ltCleanSrcB a && ltCleanSrcB b
  | _ => false

theorem ltCleanSrcB_sound : ∀ e : SExpr, ltCleanSrcB e = true → ltClean e ∧ varsIn srcName e := by
  intro e
  induction e with
  | SVar x => intro h; have := srcName_of_srcNameB h; exact ⟨this.1, this⟩
  | SLit n =>
      intro h
      have hn : n < 2 ^ 64 := by simpa [ltCleanSrcB] using h
      exact ⟨hn, trivial⟩
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb
  | SLt a b iha ihb =>
      intro h
      simp only [ltCleanSrcB, Bool.and_eq_true] at h
      exact ⟨⟨(iha h.1).1, (ihb h.2).1⟩, ⟨(iha h.1).2, (ihb h.2).2⟩⟩
  | _ => intro h; simp [ltCleanSrcB] at h

/-- The Boolean test for `IsCoveredSCtlGuarded`. -/
def coveredGuardedB : LowCT → Bool
  | .RSkip => true
  | .RSeq a b => coveredGuardedB a && coveredGuardedB b
  | .RLetU64Zero x b => srcNameB x && coveredGuardedB b
  | .RScalarSet x n => srcNameB x && decide (n < 2 ^ 64)
  | .RScalarSetExpr x e => srcNameB x && ltCleanSrcB e
  | .RIfNz g t e => srcNameB g && coveredGuardedB t && coveredGuardedB e
  | _ => false

theorem isCoveredSCtlGuarded_of_coveredGuardedB :
    ∀ c : LowCT, coveredGuardedB c = true → IsCoveredSCtlGuarded c := by
  intro c
  induction c with
  | RSkip => intro _; exact .rSkip
  | RSeq a b iha ihb =>
      intro h; simp only [coveredGuardedB, Bool.and_eq_true] at h
      exact .rSeq (iha h.1) (ihb h.2)
  | RLetU64Zero x b ih =>
      intro h; simp only [coveredGuardedB, Bool.and_eq_true] at h
      exact .rLetU64Zero (srcName_of_srcNameB h.1) (ih h.2)
  | RScalarSet x n =>
      intro h; simp only [coveredGuardedB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .rScalarSet (srcName_of_srcNameB h.1) h.2
  | RScalarSetExpr x e =>
      intro h; simp only [coveredGuardedB, Bool.and_eq_true] at h
      exact .rScalarSetExpr (srcName_of_srcNameB h.1) (ltCleanSrcB_sound e h.2).1
        (ltCleanSrcB_sound e h.2).2
  | RIfNz g t e iht ihe =>
      intro h; simp only [coveredGuardedB, Bool.and_eq_true] at h
      exact .rIfNz (srcName_of_srcNameB h.1.1) (iht h.1.2) (ihe h.2)
  | _ => intro h; simp [coveredGuardedB] at h

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
