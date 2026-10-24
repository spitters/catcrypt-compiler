/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.RustToJasminComWhile

/-!
# The operational (`RustExec`) leg for the unified front

`RustToJasminComWhile.transU_to_jasminCom_endToEnd` closes the **value** leg of the
`while`-carrying (`IsCoveredSU`) end-to-end over the unified waist `semU`. This file
supplies the operational leg — `RustToJasminComWhile.RustExecSimulatesUnified_Statement`
— and pairs the two in `transU_to_jasminCom_endToEnd_withRustExec`.

## The two halves of the operational leg

**The state shape.** `RustStateSubstrate.noAlias_canonical_witness` builds, for any
`rs'` and any alias-free output var-map, a valuation satisfying the byte-layout
invariant `RustStateInterp o.vm rs' _`. §1–§2 supply the alias-freedom for the
unified descent: `transU_preserves_noAlias`, the `IsCoveredSU` analogue of
`translateDialectControl_preserves_noAlias`, by induction on `IsCoveredSU`, with the
`RWhileNz` case handled by a trip-indexed `loopWhileDEnv` preservation lemma
(`loopWhileDEnv_preserves_noAlias`), the `RFor` case by its counted twin
(`loopRForDEnv_preserves_noAlias`), the guarded conditional by the `condSkipD` case
split, and the leaf through `IsCoveredSCtl.toIsCoveredCtl`.

That half constrains no execution: it holds at every post-state whatsoever, so an
`∃ Vb', RustStateInterp o.vm rs' Vb'` conclusion is dischargeable with the
`RustExec` hypothesis unused.

**The values.** §3 ties the post-state to the source semantics.
`rustExec_semU_agree` is the unified-front analogue of
`RustExecSemScalarBridge.rustExec_semScalar_agree_scoped`: on the coverage
`IsCoveredAdeqU` — an `IsCoveredAdeq` word leaf under `RSeq`/`RBlock`/the guarded
conditional/the counted `RFor` — a `RustExec` `Nat`-model run and a `semU`
`BitVec`-model run started from an entry state and env agreeing on a bound set `B`
end in a state and env agreeing on the write set `afterB B c`. `rustExecSimulatesUnified`
(§4) then conjoins the two halves: the post-state valuation satisfies the byte-layout
invariant *and* reads back, at each tracked non-temp write, the value `env'` carries.

## The `RWhileNz` arm

`IsCoveredAdeqU` has no `RWhileNz` constructor. `RustExec` tests the loop guard on
the entry state (`whileFalse` exits with the state unchanged) while `semU`'s waist
`semScalarWhile` is a do-while that runs the body once and tests the guard on its
output env, so the two models disagree at a zero entry guard. §5 proves the arm
under a nonzero entry guard (`agreeWhileNzU`) and states the unconditional form as
`RWhileNzUnifiedAgreement_Statement`, with the reason it does not hold.

**All goals closed; no new axioms.**
-/

@[expose] public section

set_option autoImplicit true

namespace CatCrypt.Crypto.SecureCompilation.VIR.RustExecSimulatesUnified

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.RustToJasminComWhile
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Core

/-! ## 1. `NoAliasVM` preservation for the two env-threaded loop combinators -/

/-- The env-threaded runtime-loop front `loopWhileDEnv` preserves `NoAliasVM`, given
    per-trip body preservation. Trip index induction: each trip threads the body at
    the run-time env `envPre`; there is no per-trip counter bind (the `while` body
    reads/decrements its own counter), so preservation is a straight `ihBody`
    application over the `NoAliasVM oPre.vm` from the trip IH. -/
theorem loopWhileDEnv_preserves_noAlias (fuel : Nat) (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (env : SEnvScalar) (o : DTransOut Γ),
      transU fuel vm env body = some o → NoAliasVM vm → NoAliasVM o.vm) :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (env : SEnvScalar) (o : DTransOut Γ),
      loopWhileDEnv (fun vm' e => transU fuel vm' e body) (fun e => semU fuel body e)
        vm env N = some o →
      NoAliasVM vm → NoAliasVM o.vm := by
  intro N
  induction N with
  | zero =>
      intro Γ vm env o htr hNA
      simp only [loopWhileDEnv, Option.some.injEq] at htr
      subst htr; exact hNA
  | succ n ihN =>
      intro Γ vm env o htr hNA
      simp only [loopWhileDEnv] at htr
      rcases hpre : loopWhileDEnv (fun vm' e => transU fuel vm' e body)
          (fun e => semU fuel body e) vm env n with _ | oPre
      · rw [hpre] at htr; simp at htr
      · simp only [hpre] at htr
        rcases hspre : semWhileIter (fun e => semU fuel body e) n env with _ | envPre
        · simp only [hspre] at htr; simp at htr
        · simp only [hspre] at htr
          rcases hbt : transU fuel oPre.vm envPre body with _ | oBody
          · rw [hbt] at htr; simp at htr
          · rw [hbt] at htr; simp only [Option.some.injEq] at htr
            subst htr
            exact ihBody oPre.vm envPre oBody hbt (ihN vm env oPre hpre hNA)

/-- The env-threaded counted-loop front `loopRForDEnv` preserves `NoAliasVM`, given
    per-trip body preservation. As `loopRForD_preserves_noAlias`, but env-threaded:
    each trip binds the counter (`noAlias_bind`) then threads the body at the
    trip-`n` env. -/
theorem loopRForDEnv_preserves_noAlias (fuel : Nat) (x : String) (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (env : SEnvScalar) (o : DTransOut Γ),
      transU fuel vm env body = some o → NoAliasVM vm → NoAliasVM o.vm) :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (env : SEnvScalar) (o : DTransOut Γ),
      loopRForDEnv x (fun vm' e => transU fuel vm' e body) (fun e => semU fuel body e)
        vm env N = some o →
      NoAliasVM vm → NoAliasVM o.vm := by
  intro N
  induction N with
  | zero =>
      intro Γ vm env o htr hNA
      simp only [loopRForDEnv, Option.some.injEq] at htr
      subst htr; exact hNA
  | succ n ihN =>
      intro Γ vm env o htr hNA
      simp only [loopRForDEnv] at htr
      rcases hpre : loopRForDEnv x (fun vm' e => transU fuel vm' e body)
          (fun e => semU fuel body e) vm env n with _ | oPre
      · rw [hpre] at htr; simp at htr
      · simp only [hpre] at htr
        rcases hspre : semRForD (fun e => semU fuel body e) x n env with _ | envPre
        · simp only [hspre] at htr; simp at htr
        · simp only [hspre] at htr
          rcases hbt : transU fuel (oPre.vm.bind x)
              (envPre.upd x (t := .sword 64) (BitVec.ofNat 64 n)) body with _ | oBody
          · rw [hbt] at htr; simp at htr
          · rw [hbt] at htr; simp only [Option.some.injEq] at htr
            subst htr
            exact ihBody (oPre.vm.bind x) _ oBody hbt
              (noAlias_bind (ihN vm env oPre hpre hNA) x)

/-! ## 2. `NoAliasVM` preservation for the unified front -/

/-- **The unified front `transU` preserves `NoAliasVM`** (the `IsCoveredSU` analogue
    of `translateDialectControl_preserves_noAlias`, with an `RWhileNz` arm).
    Induction on `IsCoveredSU`:

    * `ofCtl` → `translateDialectControl_preserves_noAlias` (after `transU_leaf` and
      `IsCoveredSCtl.toIsCoveredCtl`);
    * `rSeq` → thread the two child preservations along the `ComCont.comp` fold;
    * `rBlock` → the pass-through IH;
    * `rCond` → the trivial `condSkipD` guard split (`false ↦ vm` unchanged,
      `true ↦` the block IH);
    * `rWhile` → `loopWhileDEnv_preserves_noAlias` (the **new** data-dependent loop
      case), with the coverage IH as body preservation;
    * `rFor` → `loopRForDEnv_preserves_noAlias`, with the coverage IH as body
      preservation. -/
theorem transU_preserves_noAlias (fuel : Nat) {c : LowCT} (hcov : IsCoveredSU c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (env : SEnvScalar) (o : DTransOut Γ),
      transU fuel vm env c = some o → NoAliasVM vm → NoAliasVM o.vm := by
  induction hcov with
  | @ofCtl c hs hns =>
      intro Γ vm env o htr hNA
      rw [transU_leaf fuel vm env hns] at htr
      exact translateDialectControl_preserves_noAlias vm hs.toIsCoveredCtl htr hNA
  | @rSeq c₁ c₂ _ _ ih1 ih2 =>
      intro Γ vm env o htr hNA
      rcases ht1 : transU fuel vm env c₁ with _ | o₁
      · simp [transU, ht1] at htr
      · rcases hs1 : semU fuel c₁ env with _ | env₁
        · simp [transU, ht1, hs1] at htr
        · rcases ht2 : transU fuel o₁.vm env₁ c₂ with _ | o₂
          · simp [transU, ht1, hs1, ht2] at htr
          · simp only [transU, ht1, hs1, ht2, Option.some.injEq] at htr
            obtain rfl := htr
            exact ih2 o₁.vm env₁ o₂ ht2 (ih1 vm env o₁ ht1 hNA)
  | @rBlock body _ ih =>
      intro Γ vm env o htr hNA
      simp only [transU] at htr
      exact ih vm env o htr hNA
  | @rCond name thenBlk _ ih =>
      intro Γ vm env o htr hNA
      simp only [transU] at htr
      cases hb : guardNz name env with
      | false =>
          rw [hb] at htr
          simp only [condSkipD, Option.some.injEq] at htr
          subst htr; exact hNA
      | true =>
          rw [hb] at htr
          simp only [condSkipD] at htr
          exact ih vm env o htr hNA
  | @rWhile name body _ ih =>
      intro Γ vm env o htr hNA
      simp only [transU] at htr
      exact loopWhileDEnv_preserves_noAlias fuel body
        (fun vm env o ht hn => ih vm env o ht hn)
        (scalarWhileTrips (fun e => semU fuel body e) (guardNz name) fuel env)
        vm env o htr hNA
  | @rFor x N body _ ih =>
      intro Γ vm env o htr hNA
      simp only [transU] at htr
      exact loopRForDEnv_preserves_noAlias fuel x body
        (fun vm env o ht hn => ih vm env o ht hn)
        N vm env o htr hNA

/-! ## 3. The `RustExec` ↔ `semU` value agreement on the unified fragment -/

/-- `semScalar` of a dynamic-index array load writes only its destination name. -/
theorem semScalar_arrLoad_frame {dst src : Located} {idxVar : String}
    {env env' : SEnvScalar} (h : semScalar (.RArrLoad dst src idxVar) env = some env')
    (y : String) (hy : y ≠ dst.locVar) : env' y = env y := by
  simp only [semScalar] at h
  split at h <;> (cases h; simp [SEnvScalar.upd, hy])

/-- `semScalar` of a dynamic-index array store writes only the array name. -/
theorem semScalar_arrStore_frame {arr src : Located} {idxVar : String}
    {env env' : SEnvScalar} (h : semScalar (.RArrStore arr idxVar src) env = some env')
    (y : String) (hy : y ≠ arr.locVar) : env' y = env y := by
  simp only [semScalar] at h
  repeat' split at h
  all_goals (cases h; simp [SEnvScalar.upd, hy])

/-- The unified guard read through the entry reflection: on a `B`-bound non-temp
    name whose `RustState` scalar is a `u64`, `guardNz` is the nonzero test on that
    scalar. -/
theorem guardNz_eq_decide {rs : RustState} {env : SEnvScalar} {B : String → Prop}
    (henv : EnvBoundOn rs env B) (hIR : ScalarInRange rs) (name : String)
    (hB : B name) (hnt : ¬ isTmpName name) :
    guardNz name env = decide (rs.rsScalar name ≠ 0) := by
  have hbind := henv name hB hnt
  simp only [guardNz, envReadU64, hbind, Option.getD_some]
  exact decide_eq_decide.mpr (not_congr (ofNat_eq_zero_iff (hIR name)))

/-- The counted-loop arm of the unified agreement, by `Nat`-induction on the trip
    count with the body agreement passed in. Each trip binds the counter `x` to the
    trip index on both sides — `RustExec.forSucc`'s `rsSetScalar r1 x n` against
    `semRForD`'s `envPre.upd x (BitVec.ofNat 64 n)` — and folds the body's write
    set back to `B` (`afterB` is conservative at `RFor`). -/
theorem agreeForU {N : Nat} {leafSpec : LeafSpec} (fuel : Nat)
    {x : String} {body : LowCT}
    (ihBody : ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec body rs rs' → semU fuel body env = some env' →
      EnvBoundOn rs env B → ScalarInRange rs → readsOKU B body →
      EnvBoundOn rs' env' (afterB B body) ∧ ScalarInRange rs') :
    ∀ (M : Nat), M ≤ 2 ^ 64 →
      ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B : String → Prop},
        RustExec N leafSpec (.RFor x M body) rs rs' →
        semRForD (fun e => semU fuel body e) x M env = some env' →
        EnvBoundOn rs env B → ScalarInRange rs →
        readsOKU (fun y => B y ∨ y = x) body →
        EnvBoundOn rs' env' B ∧ ScalarInRange rs' := by
  intro M
  induction M with
  | zero =>
      intro _ rs rs' env env' B hexec hsem henv hIR _
      cases hexec
      simp only [semRForD, Option.some.injEq] at hsem
      subst hsem
      exact ⟨henv, hIR⟩
  | succ n ihN =>
      intro hM rs rs' env env' B hexec hsem henv hIR hreads
      cases hexec with
      | forSucc _ _ _ _ _ _ hFor hBody =>
          rcases hpre : semRForD (fun e => semU fuel body e) x n env with _ | envPre
          · simp only [semRForD, hpre] at hsem
            exact absurd hsem (by simp)
          · simp only [semRForD, hpre] at hsem
            obtain ⟨hePre, hiPre⟩ := ihN (by omega) hFor hpre henv hIR hreads
            obtain ⟨he', hi'⟩ :=
              ihBody hBody hsem (envBoundOn_upd hePre x n)
                (scalarInRange_upd hiPre x (by omega)) hreads
            exact ⟨envBoundOn_mono he' (fun y hy => le_afterB body _ y (Or.inl hy)), hi'⟩

/-- **The unified value agreement.** A `RustExec` `Nat`-model run and a `semU`
    `BitVec`-model run of the same `IsCoveredAdeqU`-covered command, started from an
    entry state and env that agree on the bound set `B`, end in a state and env that
    agree on the write set `afterB B c`.

    Induction on `IsCoveredAdeqU`:

    * `ofAdeq` → `semU_leaf` routes the node to `semScalar`, and the straight-line
      agreement `rustExec_semScalar_agree_scoped` applies;
    * `rSeq` / `rBlock` → thread the two child agreements along `semU`'s `bind`;
    * `rCond` → `guardNz_eq_decide` matches the `semScalarCond` guard against
      `RustExec.ifTrue`/`ifFalse`; the false leg leaves both sides untouched;
    * `rFor` → `agreeForU`;
    * the array arms → the access writes a tower slot on the `RustExec` side and
      the name `readsOKU` keeps outside `B` on the `semScalar` side
      (`semScalar_arrLoad_frame`, `semScalar_arrStore_frame`), so the scalar
      reflection is untouched. -/
theorem rustExec_semU_agree {N : Nat} {leafSpec : LeafSpec} (fuel : Nat) {c : LowCT}
    (h : IsCoveredAdeqU c) :
    ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec c rs rs' → semU fuel c env = some env' →
      EnvBoundOn rs env B → ScalarInRange rs → readsOKU B c →
      EnvBoundOn rs' env' (afterB B c) ∧ ScalarInRange rs' := by
  induction h with
  | @ofAdeq c hAdeq hns =>
      intro rs rs' env env' B hexec hsem henv hIR hreads
      rw [semU_leaf fuel env hns] at hsem
      obtain ⟨e2, hs2, he2, hi2⟩ :=
        rustExec_semScalar_agree_scoped hAdeq hexec henv hIR
          (readsOKU.toReadsOK c B hreads)
      rw [hs2] at hsem
      obtain rfl := Option.some.inj hsem
      exact ⟨he2, hi2⟩
  | @rSeq c₁ c₂ _ _ ih₁ ih₂ =>
      intro rs rs' env env' B hexec hsem henv hIR hreads
      obtain ⟨hr1, hr2⟩ := hreads
      cases hexec with
      | seq _ _ _ _ _ h1 h2 =>
          rcases hs1 : semU fuel c₁ env with _ | env₁
          · simp only [semU, hs1, Option.bind_none] at hsem
            exact absurd hsem (by simp)
          · simp only [semU, hs1, Option.bind_some] at hsem
            obtain ⟨he1, hi1⟩ := ih₁ h1 hs1 henv hIR hr1
            exact ih₂ h2 hsem he1 hi1 hr2
  | @rBlock body _ ih =>
      intro rs rs' env env' B hexec hsem henv hIR hreads
      cases hexec with
      | block _ _ _ hb =>
          simp only [semU] at hsem
          exact ih hb hsem henv hIR hreads
  | @rCond name thenBlk hname _ ih =>
      intro rs rs' env env' B hexec hsem henv hIR hreads
      obtain ⟨hBname, hrThen, _⟩ := hreads
      have hg := guardNz_eq_decide henv hIR name hBname hname
      cases hexec with
      | ifTrue _ _ _ _ _ v hveq hvne hct =>
          have hgt : guardNz name env = true := by
            rw [hg]; exact decide_eq_true (hveq ▸ hvne)
          simp only [semU, semScalarCond, hgt, cond_true] at hsem
          obtain ⟨he', hi'⟩ := ih hct hsem henv hIR hrThen
          exact ⟨envBoundOn_mono he' (fun y hy => le_afterB thenBlk B y hy), hi'⟩
      | ifFalse _ _ _ _ _ hveq hcf =>
          cases hcf
          have hgf : guardNz name env = false := by
            rw [hg]; exact decide_eq_false (by simp [hveq])
          simp only [semU, semScalarCond, hgf, cond_false, Option.some.injEq] at hsem
          subst hsem
          exact ⟨henv, hIR⟩
  | @rFor x M body hM _ ih =>
      intro rs rs' env env' B hexec hsem henv hIR hreads
      simp only [semU] at hsem
      exact agreeForU fuel (fun hb hs he hi hr => ih hb hs he hi hr) M hM
        hexec hsem henv hIR hreads
  | rArrLoad d s i k _ _ _ | rArrLoadBytes d s i k _ _ _ =>
      intro rs rs' env env' B hexec hsem henv hIR hreads
      have hnB : ¬ B d := hreads
      rw [semU_leaf fuel env rfl] at hsem
      cases hexec with
      | arrLoad _ _ _ _ idx oldV srcV _ _ _ =>
          refine ⟨fun y hy hnt => ?_, fun y => by
            simpa only [locatedUpdate, rsSetTower] using hIR y⟩
          have hyB : B y := hy
          have hyd : y ≠ d := fun h => hnB (h ▸ hyB)
          rw [semScalar_arrLoad_frame hsem y hyd]
          simp only [locatedUpdate, rsSetTower]
          exact henv y hyB hnt
  | rArrStore a i s k _ _ _ | rArrStoreBytes a i s k _ _ _ =>
      intro rs rs' env env' B hexec hsem henv hIR hreads
      have hnB : ¬ B a := hreads
      rw [semU_leaf fuel env rfl] at hsem
      cases hexec with
      | arrStore _ _ _ _ idx oldV srcV _ _ _ =>
          refine ⟨fun y hy hnt => ?_, fun y => by
            simpa only [locatedUpdate, rsSetTower] using hIR y⟩
          have hyB : B y := hy
          have hya : y ≠ a := fun h => hnB (h ▸ hyB)
          rw [semScalar_arrStore_frame hsem y hya]
          simp only [locatedUpdate, rsSetTower]
          exact henv y hyB hnt

/-- The leaf arm of the word-slot unified agreement: on a `notSeqLike`
    `IsCoveredAdeqArr` node `semU` is `semScalar`, and
    `rustExec_semScalar_agree_arrW` applies. -/
theorem agreeLeafUW {N : Nat} {leafSpec : LeafSpec} (fuel : Nat)
    (hload : ArrLoadWord leafSpec) (hstore : ArrStoreWord leafSpec)
    (hlimb : LimbStoreWord leafSpec) (TW : String → Prop) [DecidablePred TW] {c : LowCT}
    (hArr : IsCoveredAdeqArr c) (hns : isSeqLike c = false) :
    ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (towerSpellC TW c) rs rs' → semU fuel c env = some env' →
      EnvBoundOn rs env B → TowerWordsOn rs env T → TowerU64On rs TW →
      (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
      readsOKUW TW B c → towerOKW T TW c →
      EnvBoundOn rs' env' (afterBW TW B c) ∧ TowerWordsOn rs' env' T ∧
        TowerU64On rs' TW ∧ ScalarInRange rs' := by
  intro rs rs' env env' B T hexec hsem henv htw hu hTW hdisj hir hreads htok
  rw [semU_leaf fuel env hns] at hsem
  obtain ⟨e2, hs2, he2, hw2, hu2, hi2⟩ :=
    rustExec_semScalar_agree_arrW hload hstore hlimb TW hArr hexec henv htw hu hTW hdisj hir
      (readsOKUW.toReadsOKW TW c B hreads) htok
  rw [hs2] at hsem
  obtain rfl := Option.some.inj hsem
  exact ⟨he2, hw2, hu2, hi2⟩

/-- The counted-loop arm of the word-slot unified agreement, by `Nat`-induction on
    the trip count with the body agreement passed in: `agreeForU` with the tower
    reflection `TowerWordsOn` and the word-typedness `TowerU64On` carried as loop
    invariants (the counter lies outside `T`). -/
theorem agreeForUW {N : Nat} {leafSpec : LeafSpec} (fuel : Nat)
    (TW : String → Prop) [DecidablePred TW] {x : String} {body : LowCT}
    (ihBody : ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (towerSpellC TW body) rs rs' → semU fuel body env = some env' →
      EnvBoundOn rs env B → TowerWordsOn rs env T → TowerU64On rs TW →
      (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
      readsOKUW TW B body → towerOKW T TW body →
      EnvBoundOn rs' env' (afterBW TW B body) ∧ TowerWordsOn rs' env' T ∧
        TowerU64On rs' TW ∧ ScalarInRange rs') :
    ∀ (M : Nat), M ≤ 2 ^ 64 →
      ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B T : String → Prop},
        RustExec N leafSpec (.RFor x M (towerSpellC TW body)) rs rs' →
        semRForD (fun e => semU fuel body e) x M env = some env' →
        EnvBoundOn rs env B → TowerWordsOn rs env T → TowerU64On rs TW →
        (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
        readsOKUW TW (fun y => B y ∨ y = x) body → ¬ T x → towerOKW T TW body →
        EnvBoundOn rs' env' B ∧ TowerWordsOn rs' env' T ∧
          TowerU64On rs' TW ∧ ScalarInRange rs' := by
  intro M
  induction M with
  | zero =>
      intro _ rs rs' env env' B T hexec hsem henv htw hu _ _ hir _ _ _
      cases hexec
      simp only [semRForD, Option.some.injEq] at hsem
      subst hsem
      exact ⟨henv, htw, hu, hir⟩
  | succ n ihN =>
      intro hM rs rs' env env' B T hexec hsem henv htw hu hTW hdisj hir hreads hTx htok
      cases hexec with
      | forSucc _ _ _ _ _ _ hFor hBody =>
          rcases hpre : semRForD (fun e => semU fuel body e) x n env with _ | envPre
          · simp only [semRForD, hpre] at hsem
            exact absurd hsem (by simp)
          · simp only [semRForD, hpre] at hsem
            obtain ⟨hePre, hwPre, huPre, hiPre⟩ :=
              ihN (by omega) hFor hpre henv htw hu hTW hdisj hir hreads hTx htok
            have hdisj' : ∀ y, (B y ∨ y = x) → ¬ T y := by
              intro y hy
              rcases hy with hy | rfl
              · exact hdisj y hy
              · exact hTx
            obtain ⟨he', hw', hu', hi'⟩ :=
              ihBody hBody hsem (envBoundOn_upd hePre x n)
                (towerWordsOn_updScalar hwPre (onlyTmpBelow_refl envPre 0) x hTx _ n)
                (towerU64On_setScalar huPre _ _) hTW hdisj'
                (scalarInRange_upd hiPre x (by omega)) hreads htok
            exact ⟨envBoundOn_mono he' (fun y hy => le_afterBW TW body _ y (Or.inl hy)),
              hw', hu', hi'⟩

/-- **The unified value agreement with word arrays and word slots.** For a covered
    `c` and the word names `TW`, a `RustExec` run of the spelling `towerSpellC TW c`
    under one-word array oracles (`ArrLoadWord`, `ArrStoreWord`) and a word-writing
    `limbStore` oracle (`LimbStoreWord`), and a `semU` run of `c`, started from an
    entry state and env related on the scalar set `B` (`EnvBoundOn`) and on the
    tower names `T` (`TowerWordsOn`), with the word names `TU64`-typed
    (`TowerU64On`), `TW ⊆ T` and `B ∩ T = ∅`, end in a state and env related on the
    scalar write set `afterBW TW B c` and on `T`, with `TW` still `TU64`-typed.

    The scopings are `readsOKUW TW B c` (every read resolved when it happens) and
    `towerOKW T TW c` (the name-kind discipline). Induction on `IsCoveredAdeqU`, as
    `rustExec_semU_agree`: the leaves (`ofAdeq` and the four array arms) by
    `agreeLeafUW`, the counted loop by `agreeForUW`, so a counted loop over an array
    body is covered. -/
theorem rustExec_semU_agree_arr {N : Nat} {leafSpec : LeafSpec} (fuel : Nat)
    (hload : ArrLoadWord leafSpec) (hstore : ArrStoreWord leafSpec)
    (hlimb : LimbStoreWord leafSpec) (TW : String → Prop) [DecidablePred TW] {c : LowCT}
    (h : IsCoveredAdeqU c) :
    ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (towerSpellC TW c) rs rs' → semU fuel c env = some env' →
      EnvBoundOn rs env B → TowerWordsOn rs env T → TowerU64On rs TW →
      (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
      readsOKUW TW B c → towerOKW T TW c →
      EnvBoundOn rs' env' (afterBW TW B c) ∧ TowerWordsOn rs' env' T ∧
        TowerU64On rs' TW ∧ ScalarInRange rs' := by
  induction h with
  | ofAdeq hAdeq hns => exact agreeLeafUW fuel hload hstore hlimb TW hAdeq.toArr hns
  | rArrLoad d s i k hd hs hi =>
      exact agreeLeafUW fuel hload hstore hlimb TW (.ofStraight (.rArrLoad d s i k hd hs hi)) rfl
  | rArrStore a i s k ha hs hi =>
      exact agreeLeafUW fuel hload hstore hlimb TW
        (.ofStraight (.rArrStore a i s k ha hs hi)) rfl
  | rArrLoadBytes d s i m hd hs hi =>
      exact agreeLeafUW fuel hload hstore hlimb TW
        (.ofStraight (.rArrLoadBytes d s i m hd hs hi)) rfl
  | rArrStoreBytes a i s m ha hs hi =>
      exact agreeLeafUW fuel hload hstore hlimb TW
        (.ofStraight (.rArrStoreBytes a i s m ha hs hi)) rfl
  | @rSeq c₁ c₂ _ _ ih₁ ih₂ =>
      intro rs rs' env env' B T hexec hsem henv htw hu hTW hdisj hir hreads htok
      obtain ⟨hr1, hr2⟩ := hreads
      obtain ⟨ht1, ht2⟩ := htok
      simp only [towerSpellC] at hexec
      cases hexec with
      | seq _ _ _ _ _ h1 h2 =>
          rcases hs1 : semU fuel c₁ env with _ | env₁
          · simp only [semU, hs1, Option.bind_none] at hsem
            exact absurd hsem (by simp)
          · simp only [semU, hs1, Option.bind_some] at hsem
            obtain ⟨he1, hw1, hu1, hi1⟩ := ih₁ h1 hs1 henv htw hu hTW hdisj hir hr1 ht1
            exact ih₂ h2 hsem he1 hw1 hu1 hTW (afterBW_disj _ B T TW ht1 hdisj) hi1 hr2 ht2
  | @rBlock body _ ih =>
      intro rs rs' env env' B T hexec hsem henv htw hu hTW hdisj hir hreads htok
      simp only [towerSpellC] at hexec
      cases hexec with
      | block _ _ _ hb =>
          simp only [semU] at hsem
          exact ih hb hsem henv htw hu hTW hdisj hir hreads htok
  | @rCond name thenBlk hname _ ih =>
      intro rs rs' env env' B T hexec hsem henv htw hu hTW hdisj hir hreads htok
      obtain ⟨hBname, hrThen, _⟩ := hreads
      have hg := guardNz_eq_decide henv hir name hBname hname
      have hskip : towerSpellC TW .RSkip = .RSkip := rfl
      simp only [towerSpellC, hskip] at hexec
      cases hexec with
      | ifTrue _ _ _ _ _ v hveq hvne hct =>
          have hgt : guardNz name env = true := by
            rw [hg]; exact decide_eq_true (hveq ▸ hvne)
          simp only [semU, semScalarCond, hgt, cond_true] at hsem
          obtain ⟨he', hw', hu', hi'⟩ := ih hct hsem henv htw hu hTW hdisj hir hrThen htok.1
          exact ⟨envBoundOn_mono he' (fun y hy => le_afterBW TW thenBlk B y hy), hw', hu', hi'⟩
      | ifFalse _ _ _ _ _ hveq hcf =>
          cases hcf
          have hgf : guardNz name env = false := by
            rw [hg]; exact decide_eq_false (by simp [hveq])
          simp only [semU, semScalarCond, hgf, cond_false, Option.some.injEq] at hsem
          subst hsem
          exact ⟨henv, htw, hu, hir⟩
  | @rFor x M body hM _ ih =>
      intro rs rs' env env' B T hexec hsem henv htw hu hTW hdisj hir hreads htok
      simp only [towerSpellC] at hexec
      simp only [semU] at hsem
      exact agreeForUW fuel TW
        (fun hb hs he hw hu' hT hd hi hr ht => ih hb hs he hw hu' hT hd hi hr ht) M hM
        hexec hsem henv htw hu hTW hdisj hir hreads htok.1 htok.2

/-! ## 4. The operational bridge -/

/-- **The operational bridge for the unified front.** For an `IsCoveredAdeqU`-covered
    `c` translated by `transU fuel` to `o`, a `RustExec` run `rs ↦ rs'` and a `semU`
    run `env ↦ env'` from an entry state/env pair agreeing on `B`, there is a
    post-state valuation `Vb'` that

    * satisfies the byte-layout invariant `RustStateInterp o.vm rs' Vb'`, and
    * reads back, at every tracked non-temp write `name ↦ w` of `c`, exactly the
      value the source semantics leaves in `env'`.

    The second conjunct is what consumes `hExec`: `RustStateInterp` pins `Vb'` to
    `rs'`, so `noAlias_canonical_witness` alone realises the first conjunct at any
    post-state, and only the value agreement `rustExec_semU_agree` ties `env'` — the
    prediction of the source semantics — to the state the execution reaches.

    `transU_preserves_noAlias` supplies `NoAliasVM o.vm` for the witness, through
    `IsCoveredAdeqU.toIsCoveredSU`. -/
theorem rustExecSimulatesUnified
    {Γ : Ctx} (fuel : Nat) (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState) (env env' : SEnvScalar)
    (B : String → Prop)
    (hCov : IsCoveredAdeqU c)
    (hTrans : transU fuel vm env c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hSem : semU fuel c env = some env')
    (hBound : EnvBoundOn rs env B) (hIR : ScalarInRange rs) (hReads : readsOKU B c)
    (Vb : HVec Γ) (hInv : RustStateInterp vm rs Vb) :
    ∃ Vb' : HVec o.Γ',
      RustStateInterp o.vm rs' Vb' ∧
      ∀ (name : String) (w : CVar o.Γ' (.sword 64)),
        afterB B c name → ¬ isTmpName name →
        o.vm.lookup name = some ⟨.sword 64, w⟩ →
        env' name = some ⟨.sword 64, w.lookup Vb'⟩ := by
  obtain ⟨hAgree, _⟩ := rustExec_semU_agree fuel hCov hExec hSem hBound hIR hReads
  have hNA : NoAliasVM o.vm :=
    transU_preserves_noAlias fuel hCov.toIsCoveredSU vm env o hTrans hInv.noAlias
  refine ⟨_, noAlias_canonical_witness hNA rs', ?_⟩
  intro name w hafter hnt hLook
  have hword : w.lookup (HVec.ofVarFn (fun {t} v => witVarFn o.vm rs' v))
      = BitVec.ofNat 64 (rs'.rsScalar name) :=
    (noAlias_canonical_witness hNA rs').binding name (.sword 64) w hLook
  rw [hword]
  exact hAgree name hafter hnt

/-- The named residual `Prop` from `RustToJasminComWhile`, discharged. -/
theorem rustExecSimulatesUnified_statement_holds :
    RustToJasminComWhile.RustExecSimulatesUnified_Statement := by
  intro fuel Γ vm c o N leafSpec rs rs' env env' B hCov hTrans hExec hSem
    hBound hIR hReads Vb hInv
  exact rustExecSimulatesUnified fuel vm c o N leafSpec rs rs' env env' B
    hCov hTrans hExec hSem hBound hIR hReads Vb hInv

/-! ## 5. The `RWhileNz` arm -/

/-- The `RWhileNz` arm of the unified agreement, under a nonzero entry guard.
    `RustExec` tests the guard on the entry state and `semScalarWhile` tests it on
    the env the body produces, so from a state at which the guard holds the two loop
    models step together: each trip runs the body once and both re-test on that
    trip's output. Induction on the `semScalarWhile` fuel, with the body agreement
    passed in. -/
theorem agreeWhileNzU {N : Nat} {leafSpec : LeafSpec} (fuel : Nat)
    {name : String} {body : LowCT} (hnt : ¬ isTmpName name)
    (ihBody : ∀ {rs rs' : RustState} {env env' : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec body rs rs' → semU fuel body env = some env' →
      EnvBoundOn rs env B → ScalarInRange rs → readsOKU B body →
      EnvBoundOn rs' env' (afterB B body) ∧ ScalarInRange rs') :
    ∀ (k : Nat) {rs rs' : RustState} {env env' : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec (.RWhileNz name body) rs rs' →
      semScalarWhile (fun e => semU fuel body e) (guardNz name) k env = some env' →
      EnvBoundOn rs env B → ScalarInRange rs → readsOKU B body → B name →
      rs.rsScalar name ≠ 0 →
      EnvBoundOn rs' env' B ∧ ScalarInRange rs' := by
  intro k
  induction k with
  | zero =>
      intro rs rs' env env' B _ hsem _ _ _ _ _
      simp only [semScalarWhile] at hsem
      exact absurd hsem (by simp)
  | succ k ihk =>
      intro rs rs' env env' B hexec hsem henv hIR hreads hBname hgz
      cases hexec with
      | whileFalse _ _ _ hz => exact absurd hz hgz
      | whileTrue _ _ _ r1 _ v _ _ hbody hrest =>
          rcases hb : semU fuel body env with _ | b
          · simp only [semScalarWhile, hb] at hsem
            exact absurd hsem (by simp)
          · simp only [semScalarWhile, hb] at hsem
            obtain ⟨hB1, hIR1⟩ := ihBody hbody hb henv hIR hreads
            have hB1' : EnvBoundOn r1 b B :=
              envBoundOn_mono hB1 (fun y hy => le_afterB body B y hy)
            have hg : guardNz name b = decide (r1.rsScalar name ≠ 0) :=
              guardNz_eq_decide hB1' hIR1 name hBname hnt
            by_cases hz : r1.rsScalar name = 0
            · rw [hg, decide_eq_false (by simp [hz]), ite_eq_right (by simp)] at hsem
              obtain rfl := Option.some.inj hsem
              cases hrest with
              | whileFalse _ _ _ _ => exact ⟨hB1', hIR1⟩
              | whileTrue _ _ _ _ _ v' hv' hne' _ _ => exact absurd (hv' ▸ hz) hne'
            · rw [hg, decide_eq_true hz, ite_eq_left rfl] at hsem
              exact ihk hrest hsem hB1' hIR1 hreads hBname hz

/-- The `RWhileNz` arm at an `IsCoveredAdeqU` body and a nonzero entry guard:
    `agreeWhileNzU` with the body agreement supplied by `rustExec_semU_agree`, at the
    trip bound `fuel` the `semU` waist uses. This is
    `RWhileNzUnifiedAgreement_Statement` plus the hypothesis `rs.rsScalar name ≠ 0`. -/
theorem rustExec_semU_agree_whileNz {N : Nat} {leafSpec : LeafSpec} (fuel : Nat)
    {name : String} {body : LowCT} (hCov : IsCoveredAdeqU body)
    (hnt : ¬ isTmpName name)
    {rs rs' : RustState} {env env' : SEnvScalar} {B : String → Prop}
    (hexec : RustExec N leafSpec (.RWhileNz name body) rs rs')
    (hsem : semU fuel (.RWhileNz name body) env = some env')
    (henv : EnvBoundOn rs env B) (hIR : ScalarInRange rs)
    (hreads : readsOKU B body) (hBname : B name) (hgz : rs.rsScalar name ≠ 0) :
    EnvBoundOn rs' env' B ∧ ScalarInRange rs' := by
  simp only [semU] at hsem
  exact agreeWhileNzU fuel hnt
    (fun hb hs he hi hr => rustExec_semU_agree fuel hCov hb hs he hi hr)
    fuel hexec hsem henv hIR hreads hBname hgz

/-- The `RWhileNz` arm of the unified agreement without an entry-guard hypothesis —
    what an `IsCoveredAdeqU` `rWhile` constructor would need.

    It is refutable as stated. `RustExec` tests the loop guard on the entry state:
    at `rs.rsScalar name = 0` the `whileFalse` rule ends the loop with the state
    unchanged. `semU`'s waist for `RWhileNz` is `semScalarWhile`, a do-while, which
    runs the body once and tests the guard on the env the body produced. At a zero
    entry guard the two models therefore end in unrelated states.

    `rustExec_semU_agree_whileNz` is this statement with `rs.rsScalar name ≠ 0`
    added, and is proved. Discharging the arm for every entry state requires the two
    loop models reconciled — a top-tested `RWhileNz` waist for `semU`, or a do-while
    `RustExec` rule — rather than a proof of this `Prop`. A second obstacle sits behind it:
    `transU` meta-unrolls the loop to the trip count read off the run, so the front
    artifact the agreement would feed is the unrolled one, not a rolled emission
    with a back edge. -/
def RWhileNzUnifiedAgreement_Statement : Prop :=
  ∀ (N fuel : Nat) (leafSpec : LeafSpec) (name : String) (body : LowCT)
    (rs rs' : RustState) (env env' : SEnvScalar) (B : String → Prop),
    IsCoveredAdeqU body → ¬ isTmpName name →
    RustExec N leafSpec (.RWhileNz name body) rs rs' →
    semU fuel (.RWhileNz name body) env = some env' →
    EnvBoundOn rs env B → ScalarInRange rs → readsOKU B body → B name →
    EnvBoundOn rs' env' B ∧ ScalarInRange rs'

/-! ## 6. The two-conjunct end-to-end -/

/-- **The end-to-end for the unified front**: the value leg and the operational leg
    together, on the `IsCoveredAdeqU` fragment.

    Given the unified front descent `transU fuel` and the A1 lowering both succeed,
    the entry valuation/state agree with the entry env, and the unified waist
    `semU fuel` runs `c` to `env'` leaving `val` in the tracked output `name`, then

    * (value) the emitted jasmin program computes `val`
      (`jcom.denote (ctMapValD V) = ctTransTy val`), and
    * (operational) every concrete `RustExec` trace `rs ↦ rs'` lands a post-state
      byte-layout witness `Vb'` whose value at each tracked non-temp write is the
      one `env'` carries.

    The value conjunct is `transU_to_jasminCom_endToEnd`; the operational conjunct is
    `rustExecSimulatesUnified`. This reproduces the two-conjunct shape of
    `CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional`. -/
theorem transU_to_jasminCom_endToEnd_withRustExec
    {Γ : Ctx} {t : CryptoTy}
    (fuel : Nat)
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState) (Vb : HVec Γ)
    (B : String → Prop)
    (hCov : IsCoveredAdeqU c)
    (hTrans : transU fuel vm env c = some o)
    (hCons : ConsistentS vm V env)
    (hSem : semU fuel c env = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hExec : RustExec N leafSpec c rs rs')
    (hBound : EnvBoundOn rs env B) (hIR : ScalarInRange rs) (hReads : readsOKU B c)
    (hInv : RustStateInterp vm rs Vb) :
    jcom.denote (ctMapValD V) = ctTransTy val
      ∧ ∃ Vb' : HVec o.Γ',
          RustStateInterp o.vm rs' Vb' ∧
          ∀ (nm : String) (u : CVar o.Γ' (.sword 64)),
            afterB B c nm → ¬ isTmpName nm →
            o.vm.lookup nm = some ⟨.sword 64, u⟩ →
            env' nm = some ⟨.sword 64, u.lookup Vb'⟩ :=
  ⟨transU_to_jasminCom_endToEnd fuel vm c o V env env' name w val com jcom
      hCov.toIsCoveredSU hTrans hCons hSem hName hVal hRet hCom,
   rustExecSimulatesUnified fuel vm c o N leafSpec rs rs' env env' B
      hCov hTrans hExec hSem hBound hIR hReads Vb hInv⟩

end CatCrypt.Crypto.SecureCompilation.VIR.RustExecSimulatesUnified
