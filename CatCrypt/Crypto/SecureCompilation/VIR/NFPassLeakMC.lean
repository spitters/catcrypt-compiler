/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelectLeak
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop

/-!
# The leakage of three jasmin-level passes at a call environment

The two-run leakage statements of `NFProg.lowerSelects`, the range stage `RangeNFLoop.loopRange`
and the e-graph
pass at the jasmin rule set, for the runs `NFProg.leakRunMC` at a call environment `E`, in
which a `call` node runs its callee and emits no event.

Each pass keeps a `call` node with its arguments and traverses its continuation: the
lowering renames the arguments, the range stage binds the call results at the full lane
range, and the e-graph pass renames and hash-conses the arguments. Two runs of the source
call the callee at the arguments the output passes, so the call case of each proof is the
continuation case at the call results. The statements carry no side condition on `E`.

The lowering of a branch to selects moves the continuation of the branch after the selects
(`NFProg.lowerIte?`); the continuation may contain calls, so the run of a lowered branch is
restated at `E` (`NFProg.lowerIte?_leakRunMC`). The arms of a lowered branch are
straight-line and contain no call.

## Main results

* `NFProg.lowerSel_ctRelC`, `NFProg.lowerSelects_ctRelC` — equal source events at `E` give
  equal events after the lowering of branches to selects.
* `RangeNFLoop.carriedGo_ctRelC`, `RangeNFLoop.loopRange_ctRelC` — equal source events at
  `E` give equal events after the range stage, at every annotation of the loop-carried
  variables.
* `AegraphNF.aegraphOptNF_jasminRules_ctRelC` — the e-graph pass at the jasmin rule set,
  from `AegraphNF.aegraphOptNF_ctRelC`.
-/

@[expose] public section

set_option autoImplicit false

/-! ## 1. The lowering of branches to selects -/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Expr.ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d] [HasSelect d]

/-- **The results of the lowering at a call environment.** A program lowered along a
    renaming relating `V` to `W` runs at `E` and `W` to the results of the source at `E`
    and `V`. -/
theorem lowerSel_leakRunMC_fst (M : LeakModel d) (E : CallEnv d) (fuel : Nat)
    {Γ Δ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (ren : Ctxt.Hom Γ Δ)
    (V : Valuation Γ) (W : Valuation Δ) (h : Agrees ren V W) :
    (NFProg.leakRunMC M E fuel (lowerSel p ren) W).map Prod.fst =
      (NFProg.leakRunMC M E fuel p V).map Prod.fst := by
  rw [NFProg.leakRunMC_fst, NFProg.leakRunMC_fst]
  let _ : CallDenote d := ⟨E⟩
  exact denote_lowerSel fuel p ren V W h

/-- A run at `E` of the lowering and a run at `E` of the source at related valuations have
    the same results. -/
theorem lowerSel_fst_eqC (M : LeakModel d) (E : CallEnv d) (fuel : Nat) {Γ Δ : Ctxt d}
    {ts : List d.Ty} {p : NFProg d Γ ts} {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : Agrees ren V W) {r s : Valuation ts × List CTLeak}
    (hr : NFProg.leakRunMC M E fuel p V = some r)
    (hs : NFProg.leakRunMC M E fuel (lowerSel p ren) W = some s) : s.1 = r.1 := by
  have := lowerSel_leakRunMC_fst M E fuel p ren V W h
  rw [hr, hs] at this
  exact Option.some.inj this

/-- **The events of a speculated arm at a call environment do not depend on the
    valuation**, under the hypothesis of `leakRun_indep_of_straightSpec`. -/
theorem leakRunMC_indep_of_straightSpec (M : LeakModel d) (E : CallEnv d)
    (hQ : ∀ op : d.Op, HasSelect.quiet op = true →
      ∀ a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
        ComLevelCheck.opLeak M op a = ComLevelCheck.opLeak M op b) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : straightSpec p = true) :
    ∀ V V' : Valuation Γ, (NFProg.leakRunMC M E fuel p V).map Prod.snd =
      (NFProg.leakRunMC M E fuel p V').map Prod.snd := by
  induction p with
  | ret vs => intro V V'; rfl
  | var e k ih =>
      intro V V'
      simp only [straightSpec, Bool.and_eq_true] at hp
      have h1 : Expr.ctLeak M e V = Expr.ctLeak M e V' := hQ _ hp.1.2 _ _
      have h2 := ih hp.2 (V.extend (e.denote V)) (V'.extend (e.denote V'))
      simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
        Option.map_map, h1]
      rcases hx : NFProg.leakRunMC M E fuel k (V.extend (e.denote V)) with _ | x <;>
        rcases hy : NFProg.leakRunMC M E fuel k (V'.extend (e.denote V')) with _ | y <;>
        rw [hx, hy] at h2 <;> simp_all
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

/-- **The run of the bindings of an arm at a call environment.** The statement
    `emitArm?_leakRun` for the runs `NFProg.leakRunMC` at `E`. -/
theorem emitArm?_leakRunMC (M : LeakModel d) (E : CallEnv d) (fuel : Nat)
    {ts : List d.Ty} {Γ : Ctxt d} {rs : List d.Ty} (p : NFProg d Γ rs)
    (hp : straightSpec p = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        Option (NFProg d Δ' ts))
      (q : NFProg d Δ ts), emitArm? p ren kont = some q →
      ∃ (Δ' : Ctxt d) (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs)
        (q' : NFProg d Δ' ts), kont r res = some q' ∧
        ∀ (V : Valuation Γ) (W : Valuation Δ), Agrees ren V W →
          ∃ (W' : Valuation Δ') (a : Valuation rs × List CTLeak), Agrees r W W' ∧
            NFProg.leakRunMC M E fuel p V = some a ∧ Expr.lookupArgs res W' = a.1 ∧
            NFProg.leakRunMC M E fuel q W =
              (NFProg.leakRunMC M E fuel q' W').map fun s => (s.1, a.2 ++ s.2) := by
  induction p with
  | ret vs =>
      intro Δ ren kont q hq
      exact ⟨Δ, fun v => v, HVector.renameVars ren vs, q, hq, fun V W h =>
        ⟨W, (Expr.lookupArgs vs V, []), agrees_id W, rfl, lookupArgs_renameVars h vs, by
          cases NFProg.leakRunMC M E fuel q W <;> rfl⟩⟩
  | var e k ih =>
      intro Δ ren kont q hq
      simp only [straightSpec, Bool.and_eq_true] at hp
      obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨Δ', r0, res, q', hk, H⟩ := ih hp.2 (Ctxt.Hom.lift ren)
        (fun r res => kont (fun v => r (.there v)) res) q0 hq0
      refine ⟨Δ', fun v => r0 (.there v), res, q', hk, fun V W h => ?_⟩
      obtain ⟨W', a, hr, ha, hv, hl⟩ := H (V.extend (e.denote V)) (W.extend (e.denote V))
        (agrees_lift h (e.denote V))
      refine ⟨W', (a.1, Expr.ctLeak M e V ++ a.2), fun v => hr (.there v), ?_, hv, ?_⟩
      · simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some, ha]
        rfl
      · simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
          denote_rename_of_agrees h, ctLeak_rename_of_agrees M h, hl]
        cases NFProg.leakRunMC M E fuel q' W' <;>
          simp only [Option.map_some, Option.map_none, List.append_assoc]
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

/-- **The run of the selects at a call environment.** The statement `emitSels_leakRun` for
    the runs `NFProg.leakRunMC` at `E`. -/
theorem emitSels_leakRunMC (M : LeakModel d) (E : CallEnv d)
    (hS : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      M.kind (HasSelect.sel h c a b).op = .quiet) (fuel : Nat) {ts : List d.Ty} :
    ∀ {Δ : Ctxt d} {rs : List d.Ty} (h : rs.all HasSelect.selects = true)
      (c : Var Δ (HasBitType.bit (d := d))) (va vb : HVector (fun t => Var Δ t) rs)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        NFProg d Δ' ts),
      ∃ (Δ' : Ctxt d) (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
        ∀ W : Valuation Δ, ∃ W' : Valuation Δ', Agrees r W W' ∧
          Expr.lookupArgs res W' =
            (if HasBoolBit.toBool (d := d) (c.lookup W) then Expr.lookupArgs va W
              else Expr.lookupArgs vb W) ∧
          NFProg.leakRunMC M E fuel (emitSels h c va vb kont) W =
            NFProg.leakRunMC M E fuel (kont r res) W'
  | Δ, [], _, _, .nil, .nil, kont =>
      ⟨Δ, fun v => v, .nil, fun W => ⟨W, agrees_id W, by split <;> rfl, by rw [emitSels]⟩⟩
  | Δ, _ :: _, h, c, .cons a va, .cons b vb, kont => by
      obtain ⟨Δ', r0, res0, H⟩ := emitSels_leakRunMC M E hS fuel (selects_tail h) (.there c)
        (shiftVars va) (shiftVars vb)
        (fun r res => kont (fun v => r (.there v)) (.cons (r .here) res))
      refine ⟨Δ', fun v => r0 (.there v), .cons (r0 .here) res0, fun W => ?_⟩
      have hsel : (HasSelect.sel (selects_head h) c a b).denote W =
          (if HasBoolBit.toBool (d := d) (c.lookup W) then a.lookup W else b.lookup W) := by
        have := HasSelect.denoteM_sel (selects_head h) c a b W
        rw [Expr.denoteM_option_eq_some] at this
        exact Option.some.inj this
      obtain ⟨W', hr, hv, hl⟩ := H (W.extend ((HasSelect.sel (selects_head h) c a b).denote W))
      refine ⟨W', fun v => hr (.there v), ?_, ?_⟩
      · show HVector.cons ((r0 .here).lookup W') (Expr.lookupArgs res0 W') = _
        rw [hr .here, hv, lookupArgs_shiftVars, lookupArgs_shiftVars]
        show HVector.cons ((HasSelect.sel (selects_head h) c a b).denote W)
          (if HasBoolBit.toBool (d := d) (c.lookup W) then _ else _) = _
        rw [hsel]
        cases HasBoolBit.toBool (d := d) (c.lookup W) <;> rfl
      · rw [emitSels]
        simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
          ctLeak_eq_nil_of_quiet M _ W (hS _ c a b), hl]
        cases NFProg.leakRunMC M E fuel _ W' <;> rfl

/-- **The run of a lowered branch at a call environment.** The statement `lowerIte?_leakRun`
    for the runs `NFProg.leakRunMC` at `E`; the continuation `kont` may contain calls. -/
theorem lowerIte?_leakRunMC (M : LeakModel d) (E : CallEnv d)
    (hS : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      M.kind (HasSelect.sel h c a b).op = .quiet) (fuel : Nat)
    {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    (c : Var Δ (HasBitType.bit (d := d))) (thn els : NFProg d Δ rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts)
    (q : NFProg d Δ ts) (hq : lowerIte? c thn els kont = some q) :
    ∃ (Δ' : Ctxt d) (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
      ∀ W : Valuation Δ, ∃ (W' : Valuation Δ') (a₁ a₂ : Valuation rs × List CTLeak),
        Agrees r W W' ∧ NFProg.leakRunMC M E fuel thn W = some a₁ ∧
        NFProg.leakRunMC M E fuel els W = some a₂ ∧
        Expr.lookupArgs res W' =
          (if HasBoolBit.toBool (d := d) (c.lookup W) then a₁.1 else a₂.1) ∧
        NFProg.leakRunMC M E fuel q W =
          (NFProg.leakRunMC M E fuel (kont r res) W').map
            fun s => (s.1, (a₁.2 ++ a₂.2) ++ s.2) := by
  unfold lowerIte? at hq
  split at hq
  next h =>
    simp only [Lowerable, Bool.and_eq_true] at h
    obtain ⟨Δ1, r1, va, q1, hk1, H1⟩ := emitArm?_leakRunMC M E fuel thn h.1.2 _ _ q hq
    obtain ⟨Δ2, r2, vb, q2, hk2, H2⟩ := emitArm?_leakRunMC M E fuel els h.2 _ _ q1 hk1
    have hk2' := Option.some.inj hk2
    subst hk2'
    obtain ⟨Δ3, r3, res, H3⟩ := emitSels_leakRunMC M E hS fuel _ (r2 (r1 c))
      (HVector.renameVars r2 va) vb (fun r3 res => kont (fun v => r3 (r2 (r1 v))) res)
    refine ⟨Δ3, fun v => r3 (r2 (r1 v)), res, fun W => ?_⟩
    obtain ⟨W1, a₁, g1, e1, v1, l1⟩ := H1 W W (agrees_id W)
    obtain ⟨W2, a₂, g2, e2, v2, l2⟩ := H2 W W1 g1
    obtain ⟨W3, g3, v3, l3⟩ := H3 W2
    refine ⟨W3, a₁, a₂, agrees_comp (agrees_comp g1 g2) g3, e1, e2, ?_, ?_⟩
    · rw [v3, g2 (r1 c), g1 c, lookupArgs_renameVars g2, v1, v2]
    · rw [l1, l2, l3]
      cases NFProg.leakRunMC M E fuel (kont (fun v => r3 (r2 (r1 v))) res) W3 <;>
        simp only [Option.map_some, Option.map_none, List.append_assoc]
  next => cases hq

/-- **Leakage of the lowering at a call environment, two-run.** The statement
    `lowerSel_ctRel` for the runs `NFProg.leakRunMC` at `E`. A call node is kept with
    renamed arguments, so two runs call the callee at the arguments of the source runs. -/
theorem lowerSel_ctRelC (M : LeakModel d) (E : CallEnv d)
    (hQ : ∀ op : d.Op, HasSelect.quiet op = true →
      ∀ a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
        ComLevelCheck.opLeak M op a = ComLevelCheck.opLeak M op b)
    (hS : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      M.kind (HasSelect.sel h c a b).op = .quiet) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (V₁ V₂ : Valuation Γ) (W₁ W₂ : Valuation Δ),
      Agrees ren V₁ W₁ → Agrees ren V₂ W₂ →
      ∀ (r₁ r₂ s₁ s₂ : Valuation ts × List CTLeak),
      NFProg.leakRunMC M E fuel p V₁ = some r₁ → NFProg.leakRunMC M E fuel p V₂ = some r₂ →
      NFProg.leakRunMC M E fuel (lowerSel p ren) W₁ = some s₁ →
      NFProg.leakRunMC M E fuel (lowerSel p ren) W₂ = some s₂ → r₁.2 = r₂.2 →
      s₁.2 = s₂.2 := by
  induction p with
  | ret vs =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [lowerSel, NFProg.leakRunMC, Option.some.injEq] at h₃ h₄
      subst h₃ h₄
      rfl
  | var e k ih =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      simp only [lowerSel, NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
        denote_rename_of_agrees g₁, ctLeak_rename_of_agrees M g₁] at h₃
      simp only [lowerSel, NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
        denote_rename_of_agrees g₂, ctLeak_rename_of_agrees M g₂] at h₄
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hE, hB⟩ := List.append_inj he
        (CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.opLeak_length M e.op _ _)
      have hk := ih _ _ _ _ _ (agrees_lift g₁ (e.denote V₁)) (agrees_lift g₂ (e.denote V₂))
        u₁ u₂ t₁ t₂ hu₁ hu₂ ht₁ ht₂ hB
      show Expr.ctLeak M e V₁ ++ t₁.2 = Expr.ctLeak M e V₂ ++ t₂.2
      rw [hE, hk]
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [lowerSel, NFProg.leakRunMC, lookupArgs_renameVars g₁, g₁ count] at h₃
      simp only [lowerSel, NFProg.leakRunMC, lookupArgs_renameVars g₂, g₂ count] at h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hn, he'⟩ := List.cons.inj he
      injection hn with hn
      rw [← hn] at hi₂ hj₂
      obtain ⟨hi, hj, hji₁, hji₂⟩ :=
        CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.forIterLeak_ctRel
        (fun i X => NFProg.leakRunMC M E fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₁)))
        (fun i X => NFProg.leakRunMC M E fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₂)))
        (fun i X => NFProg.leakRunMC M E fuel
          (lowerSel body (appLift _ (Ctxt.Hom.lift ren)))
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) W₁)))
        (fun i X => NFProg.leakRunMC M E fuel
          (lowerSel body (appLift _ (Ctxt.Hom.lift ren)))
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) W₂)))
        (fun i X => lowerSel_leakRunMC_fst M E fuel body _ _ _
          (agrees_appLift (agrees_lift g₁ _) _ X))
        (fun i X => lowerSel_leakRunMC_fst M E fuel body _ _ _
          (agrees_appLift (agrees_lift g₂ _) _ X))
        (fun i X Y r r' x y h h' hxy =>
          NFProg.leakRunMC_prefix M E fuel body _ _ r r' x y h h' hxy)
        (fun i X Y r r' s s' h h' g g' hr =>
          ihb _ _ _ _ _ (agrees_appLift (agrees_lift g₁ _) _ X)
            (agrees_appLift (agrees_lift g₂ _) _ Y) r r' s s' h h' g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he'
      rw [hi] at he'
      have hq := List.append_cancel_left he'
      have hk := ihk _ _ _ _ _ (agrees_appLift g₁ _ j₁.1) (agrees_appLift g₂ _ j₂.1)
        q₁ q₂ t₁ t₂ (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hq
      show _ :: (j₁.2 ++ t₁.2) = _ :: (j₂.2 ++ t₂.2)
      rw [hj, hk, hn]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨hc, he'⟩ := List.cons.inj he
      injection hc with hc
      rw [← hc] at ha₂
      have ha : a₁.2 = a₂.2 := by
        cases hcb : HasBoolBit.toBool (d := d) (cond.lookup V₁) <;>
          simp only [hcb, ite_true, ite_false, Bool.false_eq_true] at ha₁ ha₂
        · exact NFProg.leakRunMC_prefix M E fuel els _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
        · exact NFProg.leakRunMC_prefix M E fuel thn _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
      rw [ha] at he'
      have hq := List.append_cancel_left he'
      rw [lowerSel] at h₃ h₄
      split at h₃
      next q hl =>
        simp only [hl] at h₄
        obtain ⟨hst, hse⟩ := straightSpec_of_lowerIte? hl
        obtain ⟨Δ', r, res, H⟩ := lowerIte?_leakRunMC M E hS fuel (ren cond)
          (lowerSel thn ren) (lowerSel els ren) _ q hl
        obtain ⟨W₁', x₁, y₁, gw₁, hx₁, hy₁, hv₁, hr₁⟩ := H W₁
        obtain ⟨W₂', x₂, y₂, gw₂, hx₂, hy₂, hv₂, hr₂⟩ := H W₂
        have ex : x₁.2 = x₂.2 := by
          have := leakRunMC_indep_of_straightSpec M E hQ fuel _ hst W₁ W₂
          rw [hx₁, hx₂] at this
          exact Option.some.inj this
        have ey : y₁.2 = y₂.2 := by
          have := leakRunMC_indep_of_straightSpec M E hQ fuel _ hse W₁ W₂
          rw [hy₁, hy₂] at this
          exact Option.some.inj this
        rw [hr₁] at h₃
        rw [hr₂] at h₄
        obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
        obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
        rw [g₁ cond] at hv₁
        rw [g₂ cond, ← hc] at hv₂
        have e : Expr.lookupArgs res W₁' = a₁.1 ∧ Expr.lookupArgs res W₂' = a₂.1 := by
          cases hcb : HasBoolBit.toBool (d := d) (cond.lookup V₁) <;>
            simp only [hcb, ite_true, ite_false, Bool.false_eq_true] at ha₁ ha₂ hv₁ hv₂
          · exact ⟨hv₁.trans (lowerSel_fst_eqC M E fuel g₁ ha₁ hy₁),
              hv₂.trans (lowerSel_fst_eqC M E fuel g₂ ha₂ hy₂)⟩
          · exact ⟨hv₁.trans (lowerSel_fst_eqC M E fuel g₁ ha₁ hx₁),
              hv₂.trans (lowerSel_fst_eqC M E fuel g₂ ha₂ hx₂)⟩
        have G₁ : Agrees (bindHom res (fun v => r (ren v)))
            (hvAppend (Expr.lookupArgs res W₁') V₁) W₁' :=
          agrees_bindHom (agrees_comp g₁ gw₁) res
        have G₂ : Agrees (bindHom res (fun v => r (ren v)))
            (hvAppend (Expr.lookupArgs res W₂') V₂) W₂' :=
          agrees_bindHom (agrees_comp g₂ gw₂) res
        rw [e.1] at G₁
        rw [e.2] at G₂
        have hk := ihk _ _ _ _ _ G₁ G₂ q₁ q₂ t₁ t₂ hq₁ hq₂ ht₁ ht₂ hq
        show (x₁.2 ++ y₁.2) ++ t₁.2 = (x₂.2 ++ y₂.2) ++ t₂.2
        rw [ex, ey, hk]
      next hl =>
        simp only [hl] at h₄
        simp only [NFProg.leakRunMC, g₁ cond] at h₃
        simp only [NFProg.leakRunMC, g₂ cond] at h₄
        obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
        obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
        obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
        obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
        rw [← hc] at hb₂
        have harm : b₁.2 = b₂.2 ∧ b₁.1 = a₁.1 ∧ b₂.1 = a₂.1 := by
          cases hcb : HasBoolBit.toBool (d := d) (cond.lookup V₁) <;>
            simp only [hcb, ite_true, ite_false, Bool.false_eq_true] at ha₁ ha₂ hb₁ hb₂
          · exact ⟨ihe _ _ _ _ _ g₁ g₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha,
              lowerSel_fst_eqC M E fuel g₁ ha₁ hb₁, lowerSel_fst_eqC M E fuel g₂ ha₂ hb₂⟩
          · exact ⟨iht _ _ _ _ _ g₁ g₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha,
              lowerSel_fst_eqC M E fuel g₁ ha₁ hb₁, lowerSel_fst_eqC M E fuel g₂ ha₂ hb₂⟩
        obtain ⟨hb, hba₁, hba₂⟩ := harm
        have hk := ihk _ _ _ _ _ (agrees_appLift g₁ _ b₁.1) (agrees_appLift g₂ _ b₂.1)
          q₁ q₂ t₁ t₂ (by rw [hba₁]; exact hq₁) (by rw [hba₂]; exact hq₂) ht₁ ht₂ hq
        show _ :: (b₁.2 ++ t₁.2) = _ :: (b₂.2 ++ t₂.2)
        rw [hb, hk, hc]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [lowerSel, NFProg.leakRunMC, lookupArgs_renameVars g₁] at h₃
      simp only [lowerSel, NFProg.leakRunMC, lookupArgs_renameVars g₂] at h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hi, hj, hji₁, hji₂⟩ :=
        CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.whileIterLeak_ctRel
        (fun X => NFProg.leakRunMC M E fuel body (hvAppend X V₁))
        (fun X => NFProg.leakRunMC M E fuel body (hvAppend X V₂))
        (fun X => NFProg.leakRunMC M E fuel (lowerSel body (appLift _ ren)) (hvAppend X W₁))
        (fun X => NFProg.leakRunMC M E fuel (lowerSel body (appLift _ ren)) (hvAppend X W₂))
        (fun X => lowerSel_leakRunMC_fst M E fuel body _ _ _ (agrees_appLift g₁ _ X))
        (fun X => lowerSel_leakRunMC_fst M E fuel body _ _ _ (agrees_appLift g₂ _ X))
        (fun X Y r r' x y h h' hxy =>
          NFProg.leakRunMC_prefix M E fuel body _ _ r r' x y h h' hxy)
        (fun X Y r r' s s' h h' g g' hr =>
          ihb _ _ _ _ _ (agrees_appLift g₁ _ X) (agrees_appLift g₂ _ Y) r r' s s' h h' g g'
            hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he
      rw [hi] at he
      have hq := List.append_cancel_left he
      have hk := ihk _ _ _ _ _ (agrees_appLift g₁ _ j₁.1) (agrees_appLift g₂ _ j₂.1)
        q₁ q₂ t₁ t₂ (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hq
      show j₁.2 ++ t₁.2 = j₂.2 ++ t₂.2
      rw [hj, hk]
  | call f args k ih =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [lowerSel, NFProg.leakRunMC, lookupArgs_renameVars g₁] at h₃
      simp only [lowerSel, NFProg.leakRunMC, lookupArgs_renameVars g₂] at h₄
      obtain ⟨c₁, hc₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨c₂, hc₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      rw [hc₁, Option.bind_some] at h₃
      rw [hc₂, Option.bind_some] at h₄
      exact ih _ _ _ _ _ (agrees_appLift g₁ _ c₁) (agrees_appLift g₂ _ c₂) r₁ r₂ s₁ s₂
        h₁ h₂ h₃ h₄ he

/-- **Leakage of the lowering of branches to selects at a call environment, two-run.** The
    statement `lowerSelects_ctRel` for the runs `NFProg.leakRunMC` at `E`: two runs of `p`
    at `E` that succeed give two runs of `lowerSelects p` at `E` that succeed, with the same
    results, and with equal events when the events of `p` are equal. -/
theorem lowerSelects_ctRelC (M : LeakModel d) (E : CallEnv d)
    (hQ : ∀ op : d.Op, HasSelect.quiet op = true →
      ∀ a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
        ComLevelCheck.opLeak M op a = ComLevelCheck.opLeak M op b)
    (hS : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      M.kind (HasSelect.sel h c a b).op = .quiet) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V₁ V₂ : Valuation Γ)
    (r₁ r₂ : Valuation ts × List CTLeak) (h₁ : NFProg.leakRunMC M E fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRunMC M E fuel p V₂ = some r₂) :
    ∃ s₁ s₂, NFProg.leakRunMC M E fuel (lowerSelects p) V₁ = some s₁ ∧
      NFProg.leakRunMC M E fuel (lowerSelects p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧
      s₂.1 = r₂.1 ∧ (r₁.2 = r₂.2 → s₁.2 = s₂.2) := by
  have f₁ := lowerSel_leakRunMC_fst M E fuel p (fun v => v) V₁ V₁ (agrees_id V₁)
  have f₂ := lowerSel_leakRunMC_fst M E fuel p (fun v => v) V₂ V₂ (agrees_id V₂)
  rw [h₁, Option.map_some] at f₁
  rw [h₂, Option.map_some] at f₂
  obtain ⟨s₁, hs₁, e₁⟩ := Option.map_eq_some_iff.mp f₁
  obtain ⟨s₂, hs₂, e₂⟩ := Option.map_eq_some_iff.mp f₂
  exact ⟨s₁, s₂, hs₁, hs₂, e₁, e₂, fun he =>
    lowerSel_ctRelC M E hQ hS fuel p _ V₁ V₂ V₁ V₂ (agrees_id V₁) (agrees_id V₂) r₁ r₂ s₁ s₂
      h₁ h₂ hs₁ hs₂ he⟩

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 2. The range stage with checked carried intervals -/

namespace CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Expr.ctLeak)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.Optimizer.Rewrite.ComGVN (opLeak_length)

/-- The leakage run at `E` of the body of a counted loop keeps `CarriedOK` at the result of
    the checker. -/
theorem forInductive_leakStepC (M : LeakModel jasminDialect) (E : CallEnv jasminDialect)
    (fuel : Nat) {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ} {len : Nat} {a : CarriedAnn}
    {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V) (i : Nat)
    (X : Ctxt.Valuation (d := jasminDialect) cs)
    (r : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)
    (hP : CarriedOK (forInductive A len a inits body) cs a.ivs X)
    (hr : NFProg.leakRunMC M E fuel body
      (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) = some r) :
    CarriedOK (forInductive A len a inits body) cs a.ivs r.1 := by
  have h := NFProg.leakRunMC_fst M E fuel body
    (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V))
  rw [hr, Option.map_some] at h
  let _ : CallDenote jasminDialect := ⟨E⟩
  exact forInductive_step fuel hlen hA X i r.1 hP h.symm

/-- The leakage run at `E` of the body of an exit-flag loop keeps `CarriedOK` at the result
    of the checker. -/
theorem whileInductive_leakStepC (M : LeakModel jasminDialect) (E : CallEnv jasminDialect)
    (fuel : Nat) {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ} {len : Nat} {a : CarriedAnn}
    {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs)}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V)
    (X : Ctxt.Valuation (d := jasminDialect) cs)
    (r : Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs) ×
      List CTLeak)
    (hP : CarriedOK (whileInductive A len a inits body) cs a.ivs X)
    (hr : NFProg.leakRunMC M E fuel body (hvAppend X V) = some r) :
    CarriedOK (whileInductive A len a inits body) cs a.ivs r.1.tail := by
  have h := NFProg.leakRunMC_fst M E fuel body (hvAppend X V)
  rw [hr, Option.map_some] at h
  let _ : CallDenote jasminDialect := ⟨E⟩
  exact whileInductive_step fuel hlen hA X r.1 hP h.symm

/-- The results of the leakage run at `E` of the traversal are those of the source. -/
theorem carriedGo_leakRunMC_fst (M : LeakModel jasminDialect) (E : CallEnv jasminDialect)
    (fuel : Nat) {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat) (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ) (hlen : len = Γ.length)
    (hA : EnvOK A V) :
    (NFProg.leakRunMC M E fuel (carriedGo A len a p) V).map Prod.fst =
      (NFProg.leakRunMC M E fuel p V).map Prod.fst := by
  rw [NFProg.leakRunMC_fst, NFProg.leakRunMC_fst]
  let _ : CallDenote jasminDialect := ⟨E⟩
  exact carriedGo_denote fuel A len a p V hlen hA

/-- A run at `E` of the traversal and a run at `E` of the source have the same results. -/
theorem carriedGo_fst_eqC (M : LeakModel jasminDialect) (E : CallEnv jasminDialect)
    (fuel : Nat) {Γ : JCtxt} {ts : List JasminTy} {A : AEnv Γ} {len : Nat} {a : CarriedAnn}
    {p : NFProg jasminDialect Γ ts} {V : Ctxt.Valuation Γ} (hlen : len = Γ.length)
    (hA : EnvOK A V) {r s : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak}
    (h : NFProg.leakRunMC M E fuel p V = some r)
    (h' : NFProg.leakRunMC M E fuel (carriedGo A len a p) V = some s) : s.1 = r.1 := by
  have := carriedGo_leakRunMC_fst M E fuel A len a p V hlen hA
  rw [h, h'] at this
  exact Option.some.inj this

variable {L : LeakModel jasminDialect}

/-- **Leakage of the traversal at a call environment, two-run.** The statement
    `carriedGo_ctRel` for the runs `NFProg.leakRunMC` at `E`. A call node is kept and its
    results enter the abstract environment at the full lane range, which holds of every
    value the callee returns. -/
theorem carriedGo_ctRelC (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    (E : CallEnv jasminDialect) (fuel : Nat) :
    ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat) (a : CarriedAnn)
      (p : NFProg jasminDialect Γ ts) (V₁ V₂ : Ctxt.Valuation Γ), len = Γ.length →
      EnvOK A V₁ → EnvOK A V₂ →
      ∀ (r₁ r₂ s₁ s₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak),
      NFProg.leakRunMC L E fuel p V₁ = some r₁ → NFProg.leakRunMC L E fuel p V₂ = some r₂ →
      NFProg.leakRunMC L E fuel (carriedGo A len a p) V₁ = some s₁ →
      NFProg.leakRunMC L E fuel (carriedGo A len a p) V₂ = some s₂ → r₁.2 = r₂.2 →
      s₁.2 = s₂.2
  | _, _, _, _, _, .ret vs, V₁, V₂, _, _, _, r₁, r₂, s₁, s₂, _, _, h₃, h₄, _ => by
      simp only [carriedGo, NFProg.leakRunMC, Option.some.injEq] at h₃ h₄
      subst h₃ h₄
      rfl
  | _, _, A, len, a, .var e k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂, s₁, s₂, h₁, h₂, h₃, h₄,
      he => by
      simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨hE, hB⟩ := List.append_inj he (opLeak_length L e.op _ _)
      simp only [carriedGo, NFProg.leakRunMC, Expr.denoteM_option_eq_some,
        Option.bind_some] at h₃ h₄
      rw [rangeExpr_denote hA₁ hlen e] at h₃
      rw [rangeExpr_denote hA₂ hlen e] at h₄
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hE2 : Expr.ctLeak L (rangeExpr A len e) V₁ =
          Expr.ctLeak L (rangeExpr A len e) V₂ := by
        rcases rangeExpr_leak hq A len e with h' | h'
        · rw [h']
          exact hE
        · exact h' _ _
      show Expr.ctLeak L (rangeExpr A len e) V₁ ++ t₁.2 =
        Expr.ctLeak L (rangeExpr A len e) V₂ ++ t₂.2
      rw [hE2]
      congr 1
      exact carriedGo_ctRelC hq E fuel _ (len + 1) a k _ _ (by simp [hlen])
        (hA₁.cons (stageAbs_sound hA₁ hlen e)) (hA₂.cons (stageAbs_sound hA₂ hlen e))
        u₁ u₂ t₁ t₂ hu₁ hu₂ ht₁ ht₂ hB
  | Γ, _, A, len, a, .forLoop (cs := cs) count inits body k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [carriedGo, NFProg.leakRunMC] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hn, he'⟩ := List.cons.inj he
      injection hn with hn
      rw [← hn] at hi₂ hj₂
      have hb : ∀ (V : Ctxt.Valuation Γ) (X : Ctxt.Valuation (d := jasminDialect) cs)
          (i : Nat), EnvOK A V → CarriedOK (forInductive A len a inits body) cs a.ivs X →
          EnvOK
            (carriedEnv (forInductive A len a inits body) cs a.ivs
              (topCons (HasWord64.word (d := jasminDialect)) A))
            (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun V X i h hX => envOK_carriedEnv cs a.ivs X hX (envOK_topCons h _)
      have hlb := length_body cs (HasWord64.word (d := jasminDialect)) hlen
      obtain ⟨hi, hj, hji₁, hji₂, hp₁, hp₂⟩ := forIterLeak_carried
        (CarriedOK (forInductive A len a inits body) cs a.ivs)
        (fun i X => NFProg.leakRunMC L E fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₁)))
        (fun i X => NFProg.leakRunMC L E fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₂)))
        (fun i X => NFProg.leakRunMC L E fuel
          (carriedGo
            (carriedEnv (forInductive A len a inits body) cs a.ivs
              (topCons (HasWord64.word (d := jasminDialect)) A))
            (cs.length + (len + 1)) a.inner body)
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₁)))
        (fun i X => NFProg.leakRunMC L E fuel
          (carriedGo
            (carriedEnv (forInductive A len a inits body) cs a.ivs
              (topCons (HasWord64.word (d := jasminDialect)) A))
            (cs.length + (len + 1)) a.inner body)
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₂)))
        (fun i X r hX hr => forInductive_leakStepC L E fuel hlen hA₁ i X r hX hr)
        (fun i X r hX hr => forInductive_leakStepC L E fuel hlen hA₂ i X r hX hr)
        (fun i X hX => carriedGo_leakRunMC_fst L E fuel _ _ _ body _ hlb (hb V₁ X i hA₁ hX))
        (fun i X hX => carriedGo_leakRunMC_fst L E fuel _ _ _ body _ hlb (hb V₂ X i hA₂ hX))
        (fun i X Y r r' x y _ _ h h' hxy =>
          NFProg.leakRunMC_prefix L E fuel body _ _ r r' x y h h' hxy)
        (fun i X Y r r' s s' hX hY h h' g g' hr =>
          carriedGo_ctRelC hq E fuel _ _ a.inner body _ _ hlb (hb V₁ X i hA₁ hX)
            (hb V₂ Y i hA₂ hY) r r' s s' h h' g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 (forInductive_init hA₁) (forInductive_init hA₂)
        hi₁ hi₂ hj₁ hj₂ he'
      rw [hi] at he'
      have hqq := List.append_cancel_left he'
      have hk := carriedGo_ctRelC hq E fuel _ _ a.rest k _ _ (length_app cs hlen)
        (envOK_carriedEnv cs a.ivs j₁.1 (by rw [hji₁]; exact hp₁) hA₁)
        (envOK_carriedEnv cs a.ivs j₂.1 (by rw [hji₂]; exact hp₂) hA₂) q₁ q₂ t₁ t₂
        (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hqq
      show _ :: (j₁.2 ++ t₁.2) = _ :: (j₂.2 ++ t₂.2)
      rw [hj, hk, hn]
  | _, _, A, len, a, .ifThenElse (rs := rs) cond thn els k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [carriedGo, NFProg.leakRunMC] at h₃ h₄
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hc, he'⟩ := List.cons.inj he
      injection hc with hc
      rw [← hc] at ha₂ hb₂
      have harm : a₁.2 = a₂.2 ∧ b₁.2 = b₂.2 ∧ b₁.1 = a₁.1 ∧ b₂.1 = a₂.1 := by
        cases hcb : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁) <;>
          simp only [hcb, ite_true, ite_false, Bool.false_eq_true] at ha₁ ha₂ hb₁ hb₂
        · have ha := NFProg.leakRunMC_prefix L E fuel els _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, carriedGo_ctRelC hq E fuel A len a.other els V₁ V₂ hlen hA₁ hA₂ a₁ a₂
            b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha, carriedGo_fst_eqC L E fuel hlen hA₁ ha₁ hb₁,
            carriedGo_fst_eqC L E fuel hlen hA₂ ha₂ hb₂⟩
        · have ha := NFProg.leakRunMC_prefix L E fuel thn _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, carriedGo_ctRelC hq E fuel A len a.inner thn V₁ V₂ hlen hA₁ hA₂ a₁ a₂
            b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha, carriedGo_fst_eqC L E fuel hlen hA₁ ha₁ hb₁,
            carriedGo_fst_eqC L E fuel hlen hA₂ ha₂ hb₂⟩
      obtain ⟨ha, hb, hba₁, hba₂⟩ := harm
      rw [ha] at he'
      have hqq := List.append_cancel_left he'
      have hk := carriedGo_ctRelC hq E fuel _ _ a.rest k _ _ (length_app rs hlen)
        (envOK_topApp rs b₁.1 hA₁) (envOK_topApp rs b₂.1 hA₂) q₁ q₂ t₁ t₂
        (by rw [hba₁]; exact hq₁) (by rw [hba₂]; exact hq₂) ht₁ ht₂ hqq
      show _ :: (b₁.2 ++ t₁.2) = _ :: (b₂.2 ++ t₂.2)
      rw [hb, hk, hc]
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [carriedGo, NFProg.leakRunMC] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hla := length_app cs hlen
      obtain ⟨hi, hj, hji₁, hji₂, hp₁, hp₂⟩ := whileIterLeak_carried
        (CarriedOK (whileInductive A len a inits body) cs a.ivs)
        (fun X => NFProg.leakRunMC L E fuel body (hvAppend X V₁))
        (fun X => NFProg.leakRunMC L E fuel body (hvAppend X V₂))
        (fun X => NFProg.leakRunMC L E fuel
          (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
            (cs.length + len) a.inner body) (hvAppend X V₁))
        (fun X => NFProg.leakRunMC L E fuel
          (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
            (cs.length + len) a.inner body) (hvAppend X V₂))
        (fun X r hX hr => whileInductive_leakStepC L E fuel hlen hA₁ X r hX hr)
        (fun X r hX hr => whileInductive_leakStepC L E fuel hlen hA₂ X r hX hr)
        (fun X hX => carriedGo_leakRunMC_fst L E fuel _ _ _ body _ hla
          (envOK_carriedEnv cs a.ivs X hX hA₁))
        (fun X hX => carriedGo_leakRunMC_fst L E fuel _ _ _ body _ hla
          (envOK_carriedEnv cs a.ivs X hX hA₂))
        (fun X Y r r' x y _ _ h h' hxy =>
          NFProg.leakRunMC_prefix L E fuel body _ _ r r' x y h h' hxy)
        (fun X Y r r' s s' hX hY h h' g g' hr =>
          carriedGo_ctRelC hq E fuel _ _ a.inner body _ _ hla
            (envOK_carriedEnv cs a.ivs X hX hA₁) (envOK_carriedEnv cs a.ivs Y hY hA₂)
            r r' s s' h h' g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 (whileInductive_init hA₁) (whileInductive_init hA₂)
        hi₁ hi₂ hj₁ hj₂ he
      rw [hi] at he
      have hqq := List.append_cancel_left he
      have hk := carriedGo_ctRelC hq E fuel _ _ a.rest k _ _ hla
        (envOK_carriedEnv cs a.ivs j₁.1 (by rw [hji₁]; exact hp₁) hA₁)
        (envOK_carriedEnv cs a.ivs j₂.1 (by rw [hji₂]; exact hp₂) hA₂) q₁ q₂ t₁ t₂
        (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hqq
      show j₁.2 ++ t₁.2 = j₂.2 ++ t₂.2
      rw [hj, hk]
  | _, _, A, len, a, .call (rs := rs) f args k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂, s₁, s₂,
      h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRunMC] at h₁ h₂
      simp only [carriedGo, NFProg.leakRunMC] at h₃ h₄
      obtain ⟨c₁, hc₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨c₂, hc₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      rw [hc₁, Option.bind_some] at h₃
      rw [hc₂, Option.bind_some] at h₄
      exact carriedGo_ctRelC hq E fuel _ _ a k _ _ (length_app rs hlen)
        (envOK_topApp rs c₁ hA₁) (envOK_topApp rs c₂ hA₂) r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he

/-- **Leakage of the stage at a call environment, two-run.** The statement
    `loopRange_ctRel` for the runs `NFProg.leakRunMC` at `E`: under a leakage model whose
    `regArith` operations are quiet, two runs of `p` at `E` that succeed with equal events
    give two runs of `loopRange a p` at `E` that succeed, with the same results and equal
    events, for every annotation `a`. -/
theorem loopRange_ctRelC (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    (E : CallEnv jasminDialect) (fuel : Nat) {Γ : JCtxt} {ts : List JasminTy}
    (a : CarriedAnn) (p : NFProg jasminDialect Γ ts) (V₁ V₂ : Ctxt.Valuation Γ)
    (r₁ r₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak)
    (h₁ : NFProg.leakRunMC L E fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRunMC L E fuel p V₂ = some r₂) (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRunMC L E fuel (loopRange a p) V₁ = some s₁ ∧
      NFProg.leakRunMC L E fuel (loopRange a p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      s₁.2 = s₂.2 := by
  have f₁ := carriedGo_leakRunMC_fst L E fuel (topEnv Γ) Γ.length a p V₁ rfl
    (envOK_topEnv V₁)
  have f₂ := carriedGo_leakRunMC_fst L E fuel (topEnv Γ) Γ.length a p V₂ rfl
    (envOK_topEnv V₂)
  rw [h₁, Option.map_some] at f₁
  rw [h₂, Option.map_some] at f₂
  obtain ⟨s₁, hs₁, e₁⟩ := Option.map_eq_some_iff.mp f₁
  obtain ⟨s₂, hs₂, e₂⟩ := Option.map_eq_some_iff.mp f₂
  exact ⟨s₁, s₂, hs₁, hs₂, e₁, e₂,
    carriedGo_ctRelC hq E fuel _ _ a p V₁ V₂ rfl (envOK_topEnv V₁) (envOK_topEnv V₂) r₁ r₂
      s₁ s₂ h₁ h₂ hs₁ hs₂ he⟩

end CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop

/-! ## 3. The e-graph pass at the jasmin rule set -/

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-- **Leakage of the e-graph pass at the jasmin rule set at a call environment, two-run.**
    Under a leakage model whose `regArith` operations are quiet, the statement
    `aegraphOptNF_ctRelC` at `Aegraph.jasminRules`. -/
theorem aegraphOptNF_jasminRules_ctRelC {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (E : CallEnv jasminDialect)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List _} (p : NFProg jasminDialect Γ ts)
    (V₁ V₂ : Ctxt.Valuation Γ) (r₁ r₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak)
    (h₁ : NFProg.leakRunMC L E fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRunMC L E fuel p V₂ = some r₂) (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRunMC L E fuel (aegraphOptNF Aegraph.jasminRules p) V₁ = some s₁ ∧
      NFProg.leakRunMC L E fuel (aegraphOptNF Aegraph.jasminRules p) V₂ = some s₂ ∧
      s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧ s₁.2 = s₂.2 :=
  aegraphOptNF_ctRelC Aegraph.jasminRules (Aegraph.jasminRules_indep hq) E fuel p V₁ V₂
    r₁ r₂ h₁ h₂ he

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
