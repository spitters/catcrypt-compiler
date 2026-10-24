/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
public import CatCrypt.Crypto.Hax.NFToCat
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNFLeak

/-!
# The leakage of the lowering of branches to selects

`NFProg.lowerSelects` rewrites only the `ifThenElse` nodes of a program. On a program
without `ifThenElse` (`NFProg.ifFree`) it is a renaming, so its leakage run at a valuation
the renaming relates is the leakage run of the source (`NFProg.leakRun_lowerSelects`): the
leakage transformer is the identity.

A lowered branch runs both arms and the selects. The test `NFProg.Lowerable` admits only
arms whose ops the dialect lists quiet (`HasSelect.quiet`). In a leakage model where the
events of a listed op do not depend on its argument values (a quiet op, or an op with no
argument) and the select ops are quiet, the lowered branch emits the events of both arms,
the same from every valuation (`NFProg.leakRun_indep_of_straightSpec`), while the source
emits `branch b` and the events of the arm `b` selects. Two runs of the source with equal
events are therefore lowered to two runs with equal events (`NFProg.lowerSel_ctRel`,
`NFProg.lowerSelects_ctRel`), and the lowering keeps `NFCT` (`NFProg.nfCT_lowerSelects`).

## Main results

* `NFProg.leakRun_lowerSel`, `NFProg.leakRun_lowerSelects` — on a branch-free program the
  lowering keeps the leakage run.
* `NFProg.leakRun_indep_of_straightSpec` — the events of a speculated arm do not depend on
  the valuation.
* `NFProg.emitArm?_leakRun`, `NFProg.emitSels_leakRun`, `NFProg.lowerIte?_leakRun` — a
  lowered branch runs as its continuation at an extended valuation, after the events of
  both arms.
* `NFProg.lowerSel_ctRel`, `NFProg.lowerSelects_ctRel` — equal source events give equal
  events after the lowering.
* `NFProg.nfCT_lowerSelects` — the lowering keeps constant time.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Expr.ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d] [HasSelect d]

omit [HasWord64 d] [HasBoolBit d] [DialectDenote d] [HasSelect d] in
/-- A renamed expression emits in `W` the events of the source in `V`, for a renaming
    relating `V` to `W`. -/
theorem ctLeak_rename_of_agrees (M : LeakModel d) {Γ Δ : Ctxt d} {t : d.Ty}
    {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : Agrees ren V W)
    (e : Expr d Γ t) : Expr.ctLeak M (e.rename ren) W = Expr.ctLeak M e V := by
  obtain ⟨op, rfl, args⟩ := e
  show ComLevelCheck.opLeak M op (Expr.lookupArgs (HVector.renameVars ren args) W) = _
  rw [lookupArgs_renameVars h args]
  rfl

omit [HasWord64 d] [HasBoolBit d] [HasSelect d] in
/-- A renamed expression denotes in `W` what the source denotes in `V`, for a renaming
    relating `V` to `W`. -/
theorem denote_rename_of_agrees {Γ Δ : Ctxt d} {t : d.Ty} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : Agrees ren V W) (e : Expr d Γ t) :
    (e.rename ren).denote W = e.denote V := by
  have := denoteM_rename h e
  rw [Expr.denoteM_option_eq_some, Expr.denoteM_option_eq_some] at this
  exact Option.some.inj this

/-- **The lowering keeps the leakage run of a branch-free program.** A branch-free program
    lowered along a renaming relating `V` to `W` runs at `W` to the results and the events
    of the source at `V`, at every fuel. -/
theorem leakRun_lowerSel (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : ifFree p = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ) (W : Valuation Δ),
      Agrees ren V W → NFProg.leakRun M fuel (lowerSel p ren) W =
        NFProg.leakRun M fuel p V := by
  induction p with
  | ret vs =>
      intro Δ ren V W h
      simp only [lowerSel, NFProg.leakRun, lookupArgs_renameVars h]
  | var e k ih =>
      have hk : ifFree k = true := by
        simpa only [ifFree, ctSafeNF, nodesOk, Bool.true_and] using hp
      intro Δ ren V W h
      simp only [lowerSel, NFProg.leakRun, denote_rename_of_agrees h,
        ctLeak_rename_of_agrees M h]
      rw [ih hk _ _ _ (agrees_lift h (e.denote V))]
  | forLoop count inits body k ihb ihk =>
      have hbk : ifFree body = true ∧ ifFree k = true := by
        simpa only [ifFree, ctSafeNF, nodesOk, Bool.and_eq_true] using hp
      intro Δ ren V W h
      have hb : ∀ i acc, NFProg.leakRun M fuel (lowerSel body (appLift _ (Ctxt.Hom.lift ren)))
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W)) =
          NFProg.leakRun M fuel body (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) :=
        fun i acc => ihb hbk.1 _ _ _ (agrees_appLift (agrees_lift h _) _ acc)
      have hk' : ∀ acc, NFProg.leakRun M fuel (lowerSel k (appLift _ ren)) (hvAppend acc W) =
          NFProg.leakRun M fuel k (hvAppend acc V) :=
        fun acc => ihk hbk.2 _ _ _ (agrees_appLift h _ acc)
      simp only [lowerSel, NFProg.leakRun, lookupArgs_renameVars h, h count, hb, hk']
  | ifThenElse =>
      simp [ifFree, ctSafeNF, nodesOk] at hp
  | whileLoop inits body k ihb ihk =>
      have hbk : ifFree body = true ∧ ifFree k = true := by
        simpa only [ifFree, ctSafeNF, nodesOk, Bool.and_eq_true] using hp
      intro Δ ren V W h
      have hb : ∀ acc, NFProg.leakRun M fuel (lowerSel body (appLift _ ren)) (hvAppend acc W) =
          NFProg.leakRun M fuel body (hvAppend acc V) :=
        fun acc => ihb hbk.1 _ _ _ (agrees_appLift h _ acc)
      have hk' : ∀ acc, NFProg.leakRun M fuel (lowerSel k (appLift _ ren)) (hvAppend acc W) =
          NFProg.leakRun M fuel k (hvAppend acc V) :=
        fun acc => ihk hbk.2 _ _ _ (agrees_appLift h _ acc)
      simp only [lowerSel, NFProg.leakRun, lookupArgs_renameVars h, hb, hk']
  | call => intro Δ ren V W h; rfl

/-- **The lowering keeps the leakage run of a branch-free program.** `lowerSelects p` runs
    to the results and the events of `p`, at every fuel and valuation, when `p` has no
    `ifThenElse`. -/
theorem leakRun_lowerSelects (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : ifFree p = true) (V : Valuation Γ) :
    NFProg.leakRun M fuel (lowerSelects p) V = NFProg.leakRun M fuel p V :=
  leakRun_lowerSel M fuel p hp _ V V (agrees_id V)

/-! ## The leakage of a lowered branch -/

omit [HasWord64 d] [HasBoolBit d] [DialectDenote d] [HasSelect d] in
/-- An expression whose operation is quiet emits no event. -/
theorem ctLeak_eq_nil_of_quiet (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (V : Valuation Γ) (h : M.kind e.op = .quiet) : Expr.ctLeak M e V = [] := by
  simp only [Expr.ctLeak, ComLevelCheck.opLeak, h]

/-- **The results of the lowering.** A program lowered along a renaming relating `V` to `W`
    runs at `W` to the results of the source at `V`. -/
theorem lowerSel_leakRun_fst (M : LeakModel d) (fuel : Nat) {Γ Δ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ) (W : Valuation Δ)
    (h : Agrees ren V W) :
    (NFProg.leakRun M fuel (lowerSel p ren) W).map Prod.fst =
      (NFProg.leakRun M fuel p V).map Prod.fst := by
  rw [NFProg.leakRun_fst, NFProg.leakRun_fst]
  let _ : CallDenote d := ⟨CallEnv.empty⟩
  exact denote_lowerSel fuel p ren V W h

/-- A run of the lowering and a run of the source at related valuations have the same
    results. -/
theorem lowerSel_fst_eq (M : LeakModel d) (fuel : Nat) {Γ Δ : Ctxt d} {ts : List d.Ty}
    {p : NFProg d Γ ts} {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (h : Agrees ren V W) {r s : Valuation ts × List CTLeak}
    (hr : NFProg.leakRun M fuel p V = some r)
    (hs : NFProg.leakRun M fuel (lowerSel p ren) W = some s) : s.1 = r.1 := by
  have := lowerSel_leakRun_fst M fuel p ren V W h
  rw [hr, hs] at this
  exact Option.some.inj this

/-- **The events of a speculated arm do not depend on the valuation.** When each op the
    dialect lists quiet emits events that do not depend on its argument values, a
    straight-line arm with listed ops emits the same events from every valuation. -/
theorem leakRun_indep_of_straightSpec (M : LeakModel d)
    (hQ : ∀ op : d.Op, HasSelect.quiet op = true →
      ∀ a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
        ComLevelCheck.opLeak M op a = ComLevelCheck.opLeak M op b) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : straightSpec p = true) :
    ∀ V V' : Valuation Γ, (NFProg.leakRun M fuel p V).map Prod.snd =
      (NFProg.leakRun M fuel p V').map Prod.snd := by
  induction p with
  | ret vs => intro V V'; rfl
  | var e k ih =>
      intro V V'
      simp only [straightSpec, Bool.and_eq_true] at hp
      have h1 : Expr.ctLeak M e V = Expr.ctLeak M e V' := hQ _ hp.1.2 _ _
      have h2 := ih hp.2 (V.extend (e.denote V)) (V'.extend (e.denote V'))
      rw [NFProg.leakRun, NFProg.leakRun, Option.map_map, Option.map_map, h1]
      rcases hx : NFProg.leakRun M fuel k (V.extend (e.denote V)) with _ | x <;>
        rcases hy : NFProg.leakRun M fuel k (V'.extend (e.denote V')) with _ | y <;>
        rw [hx, hy] at h2 <;> simp_all
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

/-- **The run of the bindings of an arm.** For a straight-line arm `p`, a program
    `emitArm? p ren kont` returns is, at a fixed extension of the context, a program of the
    continuation: from valuations `ren` relates, the arm runs to results `a`, and the
    program runs as that program of the continuation at an extended valuation, after the
    events of the arm; the returned variables read the results of `p`. -/
theorem emitArm?_leakRun (M : LeakModel d) (fuel : Nat)
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
            NFProg.leakRun M fuel p V = some a ∧ Expr.lookupArgs res W' = a.1 ∧
            NFProg.leakRun M fuel q W =
              (NFProg.leakRun M fuel q' W').map fun s => (s.1, a.2 ++ s.2) := by
  induction p with
  | ret vs =>
      intro Δ ren kont q hq
      exact ⟨Δ, fun v => v, HVector.renameVars ren vs, q, hq, fun V W h =>
        ⟨W, (Expr.lookupArgs vs V, []), agrees_id W, rfl, lookupArgs_renameVars h vs, by
          cases NFProg.leakRun M fuel q W <;> rfl⟩⟩
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
      · rw [NFProg.leakRun, ha]
        rfl
      · rw [NFProg.leakRun, denote_rename_of_agrees h, ctLeak_rename_of_agrees M h, hl]
        cases NFProg.leakRun M fuel q' W' <;>
          simp only [Option.map_some, Option.map_none, List.append_assoc]
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

/-- **The run of the selects.** With quiet select ops, the selects followed by the
    continuation run, at a fixed extension of the context, as a program of the continuation
    at an extended valuation, with no event; the selected variables read the values of `va`
    when `c` reads as `true` and those of `vb` otherwise. -/
theorem emitSels_leakRun (M : LeakModel d)
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
          NFProg.leakRun M fuel (emitSels h c va vb kont) W =
            NFProg.leakRun M fuel (kont r res) W'
  | Δ, [], _, _, .nil, .nil, kont =>
      ⟨Δ, fun v => v, .nil, fun W => ⟨W, agrees_id W, by split <;> rfl, by rw [emitSels]⟩⟩
  | Δ, _ :: _, h, c, .cons a va, .cons b vb, kont => by
      obtain ⟨Δ', r0, res0, H⟩ := emitSels_leakRun M hS fuel (selects_tail h) (.there c)
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
      · rw [emitSels, NFProg.leakRun, ctLeak_eq_nil_of_quiet M _ W (hS _ c a b), hl]
        cases NFProg.leakRun M fuel _ W' <;> rfl

/-- The arms of a branch `lowerIte?` lowers are straight-line with listed ops. -/
theorem straightSpec_of_lowerIte? {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    {c : Var Δ (HasBitType.bit (d := d))} {thn els : NFProg d Δ rs}
    {kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts}
    {q : NFProg d Δ ts} (hq : lowerIte? c thn els kont = some q) :
    straightSpec thn = true ∧ straightSpec els = true := by
  unfold lowerIte? at hq
  split at hq
  next h =>
    simp only [Lowerable, Bool.and_eq_true] at h
    exact ⟨h.1.2, h.2⟩
  next => cases hq

/-- **The run of a lowered branch.** With quiet select ops, a program
    `lowerIte? c thn els kont` returns runs, at a fixed extension of the context, as a
    program of the continuation at an extended valuation, after the events of both arms
    and with no event of the selects; the selected variables read the results of the arm
    `c` selects. -/
theorem lowerIte?_leakRun (M : LeakModel d)
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
        Agrees r W W' ∧ NFProg.leakRun M fuel thn W = some a₁ ∧
        NFProg.leakRun M fuel els W = some a₂ ∧
        Expr.lookupArgs res W' =
          (if HasBoolBit.toBool (d := d) (c.lookup W) then a₁.1 else a₂.1) ∧
        NFProg.leakRun M fuel q W =
          (NFProg.leakRun M fuel (kont r res) W').map fun s => (s.1, (a₁.2 ++ a₂.2) ++ s.2) := by
  unfold lowerIte? at hq
  split at hq
  next h =>
    simp only [Lowerable, Bool.and_eq_true] at h
    obtain ⟨Δ1, r1, va, q1, hk1, H1⟩ := emitArm?_leakRun M fuel thn h.1.2 _ _ q hq
    obtain ⟨Δ2, r2, vb, q2, hk2, H2⟩ := emitArm?_leakRun M fuel els h.2 _ _ q1 hk1
    have hk2' := Option.some.inj hk2
    subst hk2'
    obtain ⟨Δ3, r3, res, H3⟩ := emitSels_leakRun M hS fuel _ (r2 (r1 c))
      (HVector.renameVars r2 va) vb (fun r3 res => kont (fun v => r3 (r2 (r1 v))) res)
    refine ⟨Δ3, fun v => r3 (r2 (r1 v)), res, fun W => ?_⟩
    obtain ⟨W1, a₁, g1, e1, v1, l1⟩ := H1 W W (agrees_id W)
    obtain ⟨W2, a₂, g2, e2, v2, l2⟩ := H2 W W1 g1
    obtain ⟨W3, g3, v3, l3⟩ := H3 W2
    refine ⟨W3, a₁, a₂, agrees_comp (agrees_comp g1 g2) g3, e1, e2, ?_, ?_⟩
    · rw [v3, g2 (r1 c), g1 c, lookupArgs_renameVars g2, v1, v2]
    · rw [l1, l2, l3]
      cases NFProg.leakRun M fuel (kont (fun v => r3 (r2 (r1 v))) res) W3 <;>
        simp only [Option.map_some, Option.map_none, List.append_assoc]
  next => cases hq

/-- **Leakage of the lowering, two-run.** Let the events of each op the dialect lists quiet
    not depend on its argument values in `M`, and let the select ops be quiet in `M`. Two
    runs of the source with equal events, at valuations the renaming relates to `W₁` and
    `W₂`, give, for any two runs of the lowered program at `W₁` and `W₂`, equal events: a
    lowered branch emits the events of both arms, which do not depend on the valuation, and
    the source emits `branch b` and the events of the arm `b` selects, which the two runs
    share. -/
theorem lowerSel_ctRel (M : LeakModel d)
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
      NFProg.leakRun M fuel p V₁ = some r₁ → NFProg.leakRun M fuel p V₂ = some r₂ →
      NFProg.leakRun M fuel (lowerSel p ren) W₁ = some s₁ →
      NFProg.leakRun M fuel (lowerSel p ren) W₂ = some s₂ → r₁.2 = r₂.2 → s₁.2 = s₂.2 := by
  induction p with
  | ret vs =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [lowerSel, NFProg.leakRun, Option.some.injEq] at h₃ h₄
      subst h₃ h₄
      rfl
  | var e k ih =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [NFProg.leakRun] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      rw [lowerSel, NFProg.leakRun, denote_rename_of_agrees g₁,
        ctLeak_rename_of_agrees M g₁] at h₃
      rw [lowerSel, NFProg.leakRun, denote_rename_of_agrees g₂,
        ctLeak_rename_of_agrees M g₂] at h₄
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
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [lowerSel, NFProg.leakRun, lookupArgs_renameVars g₁, g₁ count] at h₃
      simp only [lowerSel, NFProg.leakRun, lookupArgs_renameVars g₂, g₂ count] at h₄
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
        (fun i X => NFProg.leakRun M fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₁)))
        (fun i X => NFProg.leakRun M fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) V₂)))
        (fun i X => NFProg.leakRun M fuel (lowerSel body (appLift _ (Ctxt.Hom.lift ren)))
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) W₁)))
        (fun i X => NFProg.leakRun M fuel (lowerSel body (appLift _ (Ctxt.Hom.lift ren)))
          (hvAppend X (.cons (HasWord64.ofNat (d := d) i) W₂)))
        (fun i X => lowerSel_leakRun_fst M fuel body _ _ _
          (agrees_appLift (agrees_lift g₁ _) _ X))
        (fun i X => lowerSel_leakRun_fst M fuel body _ _ _
          (agrees_appLift (agrees_lift g₂ _) _ X))
        (fun i X Y r r' x y h h' hxy =>
          NFProg.leakRun_prefix M fuel body _ _ r r' x y h h' hxy)
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
      simp only [NFProg.leakRun] at h₁ h₂
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
        · exact NFProg.leakRun_prefix M fuel els _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
        · exact NFProg.leakRun_prefix M fuel thn _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
      rw [ha] at he'
      have hq := List.append_cancel_left he'
      rw [lowerSel] at h₃ h₄
      split at h₃
      next q hl =>
        simp only [hl] at h₄
        obtain ⟨hst, hse⟩ := straightSpec_of_lowerIte? hl
        obtain ⟨Δ', r, res, H⟩ := lowerIte?_leakRun M hS fuel (ren cond)
          (lowerSel thn ren) (lowerSel els ren) _ q hl
        obtain ⟨W₁', x₁, y₁, gw₁, hx₁, hy₁, hv₁, hr₁⟩ := H W₁
        obtain ⟨W₂', x₂, y₂, gw₂, hx₂, hy₂, hv₂, hr₂⟩ := H W₂
        have ex : x₁.2 = x₂.2 := by
          have := leakRun_indep_of_straightSpec M hQ fuel _ hst W₁ W₂
          rw [hx₁, hx₂] at this
          exact Option.some.inj this
        have ey : y₁.2 = y₂.2 := by
          have := leakRun_indep_of_straightSpec M hQ fuel _ hse W₁ W₂
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
          · exact ⟨hv₁.trans (lowerSel_fst_eq M fuel g₁ ha₁ hy₁),
              hv₂.trans (lowerSel_fst_eq M fuel g₂ ha₂ hy₂)⟩
          · exact ⟨hv₁.trans (lowerSel_fst_eq M fuel g₁ ha₁ hx₁),
              hv₂.trans (lowerSel_fst_eq M fuel g₂ ha₂ hx₂)⟩
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
        simp only [NFProg.leakRun, g₁ cond] at h₃
        simp only [NFProg.leakRun, g₂ cond] at h₄
        obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
        obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
        obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
        obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
        rw [← hc] at hb₂
        have harm : b₁.2 = b₂.2 ∧ b₁.1 = a₁.1 ∧ b₂.1 = a₂.1 := by
          cases hcb : HasBoolBit.toBool (d := d) (cond.lookup V₁) <;>
            simp only [hcb, ite_true, ite_false, Bool.false_eq_true] at ha₁ ha₂ hb₁ hb₂
          · exact ⟨ihe _ _ _ _ _ g₁ g₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha,
              lowerSel_fst_eq M fuel g₁ ha₁ hb₁, lowerSel_fst_eq M fuel g₂ ha₂ hb₂⟩
          · exact ⟨iht _ _ _ _ _ g₁ g₂ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha,
              lowerSel_fst_eq M fuel g₁ ha₁ hb₁, lowerSel_fst_eq M fuel g₂ ha₂ hb₂⟩
        obtain ⟨hb, hba₁, hba₂⟩ := harm
        have hk := ihk _ _ _ _ _ (agrees_appLift g₁ _ b₁.1) (agrees_appLift g₂ _ b₂.1)
          q₁ q₂ t₁ t₂ (by rw [hba₁]; exact hq₁) (by rw [hba₂]; exact hq₂) ht₁ ht₂ hq
        show _ :: (b₁.2 ++ t₁.2) = _ :: (b₂.2 ++ t₂.2)
        rw [hb, hk, hc]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V₁ V₂ W₁ W₂ g₁ g₂ r₁ r₂ s₁ s₂ h₁ h₂ h₃ h₄ he
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [lowerSel, NFProg.leakRun, lookupArgs_renameVars g₁] at h₃
      simp only [lowerSel, NFProg.leakRun, lookupArgs_renameVars g₂] at h₄
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
        (fun X => NFProg.leakRun M fuel body (hvAppend X V₁))
        (fun X => NFProg.leakRun M fuel body (hvAppend X V₂))
        (fun X => NFProg.leakRun M fuel (lowerSel body (appLift _ ren)) (hvAppend X W₁))
        (fun X => NFProg.leakRun M fuel (lowerSel body (appLift _ ren)) (hvAppend X W₂))
        (fun X => lowerSel_leakRun_fst M fuel body _ _ _ (agrees_appLift g₁ _ X))
        (fun X => lowerSel_leakRun_fst M fuel body _ _ _ (agrees_appLift g₂ _ X))
        (fun X Y r r' x y h h' hxy =>
          NFProg.leakRun_prefix M fuel body _ _ r r' x y h h' hxy)
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
      simp [NFProg.leakRun] at h₁

/-- **Leakage of the lowering of branches to selects, two-run.** Let the events of each op
    the dialect lists quiet not depend on its argument values in `M`, and let the select ops
    be quiet in `M`. Two runs of `p` that succeed give two runs of `lowerSelects p` that
    succeed, with the same results, and with equal events when the events of `p` are
    equal. -/
theorem lowerSelects_ctRel (M : LeakModel d)
    (hQ : ∀ op : d.Op, HasSelect.quiet op = true →
      ∀ a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
        ComLevelCheck.opLeak M op a = ComLevelCheck.opLeak M op b)
    (hS : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      M.kind (HasSelect.sel h c a b).op = .quiet) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V₁ V₂ : Valuation Γ)
    (r₁ r₂ : Valuation ts × List CTLeak) (h₁ : NFProg.leakRun M fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRun M fuel p V₂ = some r₂) :
    ∃ s₁ s₂, NFProg.leakRun M fuel (lowerSelects p) V₁ = some s₁ ∧
      NFProg.leakRun M fuel (lowerSelects p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      (r₁.2 = r₂.2 → s₁.2 = s₂.2) := by
  have f₁ := lowerSel_leakRun_fst M fuel p (fun v => v) V₁ V₁ (agrees_id V₁)
  have f₂ := lowerSel_leakRun_fst M fuel p (fun v => v) V₂ V₂ (agrees_id V₂)
  rw [h₁, Option.map_some] at f₁
  rw [h₂, Option.map_some] at f₂
  obtain ⟨s₁, hs₁, e₁⟩ := Option.map_eq_some_iff.mp f₁
  obtain ⟨s₂, hs₂, e₂⟩ := Option.map_eq_some_iff.mp f₂
  exact ⟨s₁, s₂, hs₁, hs₂, e₁, e₂, fun he =>
    lowerSel_ctRel M hQ hS fuel p _ V₁ V₂ V₁ V₂ (agrees_id V₁) (agrees_id V₂) r₁ r₂ s₁ s₂
      h₁ h₂ hs₁ hs₂ he⟩

/-- **The lowering of branches to selects keeps constant time.** Let the events of each op
    the dialect lists quiet not depend on its argument values in `M`, and let the select ops
    be quiet in `M`. A program constant time for the labels `L` at a fuel is lowered to a
    program constant time for `L` at that fuel. -/
theorem nfCT_lowerSelects (M : LeakModel d)
    (hQ : ∀ op : d.Op, HasSelect.quiet op = true →
      ∀ a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
        ComLevelCheck.opLeak M op a = ComLevelCheck.opLeak M op b)
    (hS : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      M.kind (HasSelect.sel h c a b).op = .quiet) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (L : ComLevelCheck.Labels Γ) (p : NFProg d Γ ts)
    (h : NFCT M L fuel p) : NFCT M L fuel (lowerSelects p) := by
  intro V₁ V₂ hV
  have c := h V₁ V₂ hV
  have f₁ : (NFProg.leakRun M fuel (lowerSelects p) V₁).map Prod.fst =
      (NFProg.leakRun M fuel p V₁).map Prod.fst :=
    lowerSel_leakRun_fst M fuel p (fun v => v) V₁ V₁ (agrees_id V₁)
  have f₂ : (NFProg.leakRun M fuel (lowerSelects p) V₂).map Prod.fst =
      (NFProg.leakRun M fuel p V₂).map Prod.fst :=
    lowerSel_leakRun_fst M fuel p (fun v => v) V₂ V₂ (agrees_id V₂)
  rcases h₁ : NFProg.leakRun M fuel p V₁ with _ | r₁
  · rw [h₁, Option.map_none] at c f₁
    have h₂ : NFProg.leakRun M fuel p V₂ = none := Option.map_eq_none_iff.mp c.symm
    rw [h₂, Option.map_none] at f₂
    rw [Option.map_eq_none_iff.mp f₁, Option.map_eq_none_iff.mp f₂]
  · rw [h₁, Option.map_some] at c
    obtain ⟨r₂, h₂, e⟩ := Option.map_eq_some_iff.mp c.symm
    obtain ⟨s₁, s₂, hs₁, hs₂, -, -, he⟩ :=
      lowerSelects_ctRel M hQ hS fuel p V₁ V₂ r₁ r₂ h₁ h₂
    rw [hs₁, hs₂, Option.map_some, Option.map_some, he e.symm]

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
