/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote


@[expose] public section
set_option autoImplicit false

/-!
# Control-level sequencing: widening `IsCoveredSCtl` past its non-closure boundary

`TranslateDialectScalar.IsCoveredSCtl` (the control-extended scalar-covered
fragment the Stage-2 homomorphism `translateDialectControl_denote_ctl` proves) is
`ofStraight` (a straight-line `IsCoveredS` block) ∪ `rFor` (a bounded loop over a
covered body) ∪ `rIfNz` (a conditional over covered branches). It has **no
control-level `RSeq`/`RBlock` closure**: `IsCoveredSCtl` reaches an `RSeq` only
through `ofStraight`, and `IsCoveredS.rSeq` demands both sides be straight-line
(no `RFor`/`RIfNz`). So a loop-then-loop (`RSeq (RFor …) (RFor …)`), or any
sequence more than one of whose statements is a control construct, sits OUTSIDE
the covered sublanguage — a boundary shared by `IsCoveredCtl` (its `ofCovered`
likewise reaches `RSeq` only through the straight-line `IsCovered.rSeq`).

The canonical front matches this: `translateDialectControl` special-cases `RFor`
and `RIfNz` and delegates every other arm — `RSeq`/`RBlock` included — to
`translateDialectFull`, whose `RSeq` arm recurses through `translateDialectFull`
(which declines `RFor`/`RIfNz`). So the canonical front cannot sequence control
constructs.

This module widens the verified value-preservation fragment by exactly that
construct, in a companion combinator:

* `transCtlSeq` — the control-sequencing front: it folds `translateDialectControl`
  along the `RSeq`/`RBlock` spine via `ComCont.comp` (the same primitive
  `translateDialectFull`/`translateDialectControl` use internally), delegating
  every leaf to `translateDialectControl`. On leaves and straight-line `RSeq`
  it coincides definitionally with `translateDialectControl`
  (`transCtlSeq_eq_control`), so it is a conservative extension.
* `IsCoveredSCtlSeq` — `IsCoveredSCtl` closed under `RSeq`/`RBlock`.
* `transCtlSeq_denote_seq` — the extended homomorphism: for every
  `IsCoveredSCtlSeq` body whose `transCtlSeq` succeeds, the emitted `Com`-prefix
  denotes exactly the body's `semScalar` waist. The `ofCtl` leaves delegate to
  `translateDialectControl_denote_ctl`; the `RSeq` spine is the `ComCont.comp`
  fold (the same fold the (C-otherwise) `RIfNz` case uses), reconciled with
  `semScalar`'s `RSeq = bind`; `RBlock` is the direct pass-through.

Everything is proved against the EXISTING `semScalar` / `scalar_step` /
`translateDialectControl_denote_ctl` — no new waist semantics.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## 1. The control-sequencing front `transCtlSeq` -/

/-- The control-sequencing front: fold `translateDialectControl` along the
    `RSeq`/`RBlock` spine (composing prefixes with `ComCont.comp`), delegating
    every other arm to `translateDialectControl`. Unlike the canonical front
    (whose `RSeq` delegates to `translateDialectFull`, which declines control
    constructs), this recurses through itself on the spine, so it accepts
    sequences of `RFor`/`RIfNz`. -/
def transCtlSeq {Γ : Ctx} (vm : VarMap Γ) : LowCT → Option (DTransOut Γ)
  | .RSeq c₁ c₂ =>
      match transCtlSeq vm c₁ with
      | some o₁ =>
          match transCtlSeq o₁.vm c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | none => none
  | .RBlock body => transCtlSeq vm body
  | c => translateDialectControl vm c

/-! ## 2. The extended covered fragment `IsCoveredSCtlSeq` -/

/-- `IsCoveredSCtl` closed under control-level `RSeq`/`RBlock` sequencing. A
    sequence any number of whose statements is a full control construct
    (`RFor`/`RIfNz`) — impossible in `IsCoveredSCtl` or `IsCoveredCtl` — is
    covered here. -/
inductive IsCoveredSCtlSeq : LowCT → Prop
  | ofCtl {c : LowCT} : IsCoveredSCtl c → IsCoveredSCtlSeq c
  | rSeq {c₁ c₂ : LowCT} :
      IsCoveredSCtlSeq c₁ → IsCoveredSCtlSeq c₂ → IsCoveredSCtlSeq (.RSeq c₁ c₂)
  | rBlock {body : LowCT} :
      IsCoveredSCtlSeq body → IsCoveredSCtlSeq (.RBlock body)

/-! ## 3. `transCtlSeq` is a conservative extension of `translateDialectControl` -/

/-- On the straight-line covered fragment, folding `transCtlSeq` along the
    `RSeq`/`RBlock` spine agrees with `translateDialectFull`. Leaves reduce
    definitionally (`transCtlSeq → translateDialectControl → translateDialectFull`,
    all through the shared wildcard arm); the spine agrees by the recursive fold
    against `translateDialectFull`'s own `RSeq`/`RBlock` fold. -/
theorem transCtlSeq_eq_full_of_covered {c : LowCT} (h : IsCovered c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ), transCtlSeq vm c = translateDialectFull vm c := by
  induction h with
  | rAssert _ => intro Γ vm; rfl
  | rSeq _ _ ih1 ih2 =>
      intro Γ vm
      simp only [transCtlSeq, translateDialectFull]
      split
      · next o₁ heq1 =>
          rw [ih1 vm] at heq1
          split
          · next o₂ heq2 => rw [ih2 o₁.vm] at heq2; simp only [heq1, heq2]
          · next heq2 => rw [ih2 o₁.vm] at heq2; simp only [heq1, heq2]
      · next heq1 => rw [ih1 vm] at heq1; simp only [heq1]
  | rBlock body ih =>
      intro Γ vm
      simp only [transCtlSeq, translateDialectFull]
      exact ih vm
  | rSkip => intro Γ vm; rfl
  | rScalarSet _ _ => intro Γ vm; rfl
  | rLetU64Zero hb _ =>
      intro Γ vm
      exact translateDialectControl_eq_full_of_covered vm (.rLetU64Zero hb)
  | rCall _ _ _ => intro Γ vm; rfl
  | rSelect _ _ _ _ => intro Γ vm; rfl
  | rCallDstThreaded _ _ _ => intro Γ vm; rfl
  | rTupleLoad _ _ _ => intro Γ vm; rfl
  | rArrLoadLit _ _ _ => intro Γ vm; rfl
  | rArrStoreLit _ _ _ => intro Γ vm; rfl
  | rArrLoad _ _ _ => intro Γ vm; rfl
  | rArrStore _ _ _ => intro Γ vm; rfl
  | rLimbStore _ _ _ => intro Γ vm; rfl
  | rCallSwap _ _ _ _ => intro Γ vm; rfl
  | rCloneCall _ _ _ _ _ _ => intro Γ vm; rfl
  | rCallN _ _ _ => intro Γ vm; rfl
  | rScalarSetExpr _ _ => intro Γ vm; rfl

/-- On an `IsCoveredSCtl` body, the control-sequencing front `transCtlSeq`
    coincides with the canonical `translateDialectControl`: `RFor`/`RIfNz`
    leaves reduce definitionally through the shared wildcard arm, and a
    straight-line `RSeq`/`RBlock` fold matches `translateDialectFull` (hence
    `translateDialectControl` on the covered fragment). -/
theorem transCtlSeq_eq_control {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (h : IsCoveredSCtl c) : transCtlSeq vm c = translateDialectControl vm c := by
  cases h with
  | ofStraight hs =>
      rw [transCtlSeq_eq_full_of_covered hs.toIsCovered vm,
        translateDialectControl_eq_full_of_covered vm hs.toIsCovered]
  | rFor _ => rfl
  | rIfNz _ _ => rfl
  | rLetU64Zero _ => rfl

/-! ## 4. The extended homomorphism -/

/-- **Front-general scalar preservation, control-sequencing-extended.** For any
    `IsCoveredSCtlSeq`-covered body — the full `IsCoveredSCtl` fragment closed
    under `RSeq`/`RBlock` — the `transCtlSeq`-emitted `Com`-prefix denotes exactly
    the body's `semScalar` waist. Induction on the coverage: `ofCtl` leaves
    delegate to `translateDialectControl_denote_ctl` (after `transCtlSeq_eq_control`);
    `RSeq` is the `ComCont.comp` fold reconciled with `semScalar`'s `bind`;
    `RBlock` is the direct pass-through. -/
theorem transCtlSeq_denote_seq {c : LowCT} (hcov : IsCoveredSCtlSeq c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      transCtlSeq vm c = some o →
      semScalar c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  induction hcov with
  | @ofCtl c hs =>
      intro Γ vm V env env' o hc htr hsem
      rw [transCtlSeq_eq_control vm hs] at htr
      exact translateDialectControl_denote_ctl hs vm V env env' o hc htr hsem
  | @rSeq c₁ c₂ _ _ ih1 ih2 =>
      intro Γ vm V env env' o hc htr hsem
      rcases ht1 : transCtlSeq vm c₁ with _ | o₁
      · simp [transCtlSeq, ht1] at htr
      · rcases ht2 : transCtlSeq o₁.vm c₂ with _ | o₂
        · simp [transCtlSeq, ht1, ht2] at htr
        · simp only [transCtlSeq, ht1, ht2, Option.some.injEq] at htr
          obtain rfl := htr
          simp only [semScalar] at hsem
          rcases hs1 : semScalar c₁ env with _ | env₁
          · rw [hs1] at hsem; simp at hsem
          · simp only [hs1, Option.bind_some] at hsem
            obtain ⟨V₁, hc₁, hcont₁⟩ := ih1 vm V env env₁ o₁ hc ht1 hs1
            obtain ⟨V₂, hc₂, hcont₂⟩ := ih2 o₁.vm V₁ env₁ env' o₂ hc₁ ht2 hsem
            refine ⟨V₂, hc₂, ?_⟩
            intro t tail
            obtain ⟨com₂, hcom₂, hden₂⟩ := hcont₂ tail
            obtain ⟨com, hcom, hden⟩ := hcont₁ com₂
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp o₁.cont o₂.cont tail = some com
              simp only [ComCont.comp, hcom₂, hcom]
            · rw [hden, hden₂]
  | @rBlock body _ ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [transCtlSeq] at htr
      simp only [semScalar] at hsem
      exact ih vm V env env' o hc htr hsem

/-! ## 5. Worked examples (past the `IsCoveredSCtl` boundary) -/

/-- Two bounded loops in sequence — NOT expressible in `IsCoveredSCtl`
    (`IsCoveredS.rSeq` needs both sides straight-line) — is covered here. -/
example (x y : String) (N M : Nat) :
    IsCoveredSCtlSeq (.RSeq (.RFor x N .RSkip) (.RFor y M .RSkip)) :=
  .rSeq (.ofCtl (.rFor (.ofStraight .rSkip))) (.ofCtl (.rFor (.ofStraight .rSkip)))

/-- A conditional followed by a loop — a mixed control sequence — is covered. -/
example (name x y : String) (N : Nat) :
    IsCoveredSCtlSeq
      (.RSeq (.RIfNz name (.RScalarSet y 1) (.RScalarSet y 0)) (.RFor x N .RSkip)) :=
  .rSeq
    (.ofCtl (.rIfNz (.ofStraight (.rScalarSet y 1)) (.ofStraight (.rScalarSet y 0))))
    (.ofCtl (.rFor (.ofStraight .rSkip)))

/-- The front-success hypothesis is satisfiable: whenever both statements of a
    sequence front-compile via `transCtlSeq`, so does the sequence — the emitted
    prefix is the `ComCont.comp` of the two. -/
theorem transCtlSeq_rSeq_isSome {Γ : Ctx} (vm : VarMap Γ) (c₁ c₂ : LowCT)
    (o₁ : DTransOut Γ) (h1 : transCtlSeq vm c₁ = some o₁)
    (h2 : (transCtlSeq o₁.vm c₂).isSome) :
    (transCtlSeq vm (.RSeq c₁ c₂)).isSome := by
  simp only [transCtlSeq, h1]
  rcases h : transCtlSeq o₁.vm c₂ with _ | o₂
  · rw [h] at h2; simp at h2
  · simp

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
