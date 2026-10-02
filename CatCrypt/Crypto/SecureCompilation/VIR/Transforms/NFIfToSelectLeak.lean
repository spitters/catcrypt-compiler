/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
public import CatCrypt.Crypto.Hax.NFToCat

/-!
# The leakage of the lowering of branches to selects on branch-free programs

`NFProg.lowerSelects` rewrites only the `ifThenElse` nodes of a program. On a program
without `ifThenElse` (`NFProg.ifFree`) it is a renaming, so its leakage run at a valuation
the renaming relates is the leakage run of the source (`NFProg.leakRun_lowerSelects`): the
leakage transformer is the identity.

The translation `NFToCat.nfToCat` refuses branches, so every program it returns is
branch-free (`NFToCat.ifFree_nfToCat`).

## Main results

* `NFProg.leakRun_lowerSel`, `NFProg.leakRun_lowerSelects` — on a branch-free program the
  lowering keeps the leakage run.
* `NFToCat.ifFree_emitRes`, `NFToCat.ifFree_nfToCat` — the output of `nfToCat` is
  branch-free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Expr.ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

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

/-- **The lowering keeps the leakage run of a branch-free program.** `lowerSelects p` runs
    to the results and the events of `p`, at every fuel and valuation, when `p` has no
    `ifThenElse`. -/
theorem leakRun_lowerSelects (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : ifFree p = true) (V : Valuation Γ) :
    NFProg.leakRun M fuel (lowerSelects p) V = NFProg.leakRun M fuel p V :=
  leakRun_lowerSel M fuel p hp _ V V (agrees_id V)

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR

namespace CatCrypt.Crypto.Hax.NFToCat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-- The bindings `emitRes` places before a branch-free continuation form a branch-free
    program. -/
theorem ifFree_emitRes {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    (hc : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ') p', cont σ' = some p' →
      NFProg.ifFree p' = true) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ) p',
      emitRes cont h res σ = some p' → NFProg.ifFree p' = true
  | _, _, _, .rd _, _, _, he => hc _ _ he
  | _, _, _, .expr _, _, _, he => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp he
      simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using
        hc _ _ hk'
  | _, _, _, .expr1 _ _, _, _, he => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp he
      simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using
        hc _ _ hk'
  | _, _, h, .bind _ _ rest, σ, _, he => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp he
      simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using
        ifFree_emitRes cont hc h rest σ.wk k' hk'

/-- **The output of `nfToCat` is branch-free.** `nfToCat` refuses branches and exit-flag
    loops, so a program it returns has no `ifThenElse`. -/
theorem ifFree_nfToCat : ∀ {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (σ : TRd Γ Δ) (p' : NFProg catCryptDialect Δ (ts.map catTy)),
    nfToCat p σ = some p' → NFProg.ifFree p' = true
  | _, _, _, .ret _, _, _, he => by
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp he
      rfl
  | _, _, _, .var ⟨_, h, _⟩ k, σ, _, he => by
      obtain ⟨res, _, he⟩ := Option.bind_eq_some_iff.mp he
      exact ifFree_emitRes _ (fun σ' p' hp' => ifFree_nfToCat k σ' p' hp') h res σ _ he
  | _, _, _, .forLoop count _ body k, σ, _, he => by
      simp only [nfToCat] at he
      split at he
      · obtain ⟨_, _, he⟩ := Option.bind_eq_some_iff.mp he
        obtain ⟨body', hb, he⟩ := Option.bind_eq_some_iff.mp he
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp he
        simp only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true]
        exact ⟨ifFree_nfToCat body _ body' hb, ifFree_nfToCat k _ k' hk⟩
      · cases he
  | _, _, _, .ifThenElse .., _, _, he => by simp [nfToCat] at he
  | _, _, _, .whileLoop .., _, _, he => by simp [nfToCat] at he

end CatCrypt.Crypto.Hax.NFToCat
