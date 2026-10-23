/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-!
# The leakage of `NFProg` over a partial denotation, and a level checker with branches

`NFProg.leakRunM M fuel p V` is the leakage run of `NFLeak.NFProg.leakRun` for a dialect whose
operations denote in `Option` (`DialectDenoteM d Option`): an operation may fail, and the run
is then `none`. Its events are those of `leakRun`; under a pure denotation the two runs
coincide (`leakRunM_eq_leakRun`). Like `leakRun`, it refuses a `call` node.

`NFCTRel M L fuel p` is constant time relative to the runs that succeed: two valuations that
agree on the positions `L` marks public, from which the program runs to results, give equal
events.

`NFProg.levelCheck'` extends the level checker `NFLeak.NFProg.levelCheck` to exit-flag
loops, with the same rule for a branch: a public condition, and results at the join of the
levels of the two arms. An exit-flag loop requires its flag to be public; its carried values
take the levels of their initial values when the body keeps them, and the secret level
otherwise. The checker refuses calls. An exit-flag loop fails when its fuel runs out and an
operation of a partial denotation may fail, so the soundness statement of `levelCheck'` is
relative to the runs that succeed (`NFCTRel`), where that of `levelCheck` includes the
success of both runs (`NFCT`).

`NFProg.levelCheck'` is `NFProg.levelCheckD M (fun _ => false)`: the checker with
declassification, in which an operation marked by `isDeclass` accepts arguments at every level
and gives its result the public level, at the predicate that marks no operation. Under
`DeclassOk M isDeclass isDeclEv`, the soundness statement of `levelCheckD` gives equal events
of two successful runs or a first difference at a declassification event (`DeclDiff`); with
no marked operation no such difference exists.

## Main definitions

* `NFProg.leakRunM`, `NFCTRel`
* `ExprEv`, `OpEvents`, `OpEvents.toExprEv` — event functions of the expressions and of the
  operations of a dialect; a leakage model `M` is the event function `Expr.ctLeak M` by a
  coercion.
* `NFProg.leakRunMC` — the leakage run at a call environment with an event function, in which
  a `call` node runs its callee and emits no event.
* `Com.OpsQuiet` — every operation of a straight-line program has no event.
* `DeclDiff` — two traces first differ at a declassification event.
* `DeclassOk` — the marked operations emit one declassification event that determines their
  result.
* `flagOk`, `NFProg.levelCheckD`, `NFProg.levelCheck'`

## Main results

* `NFProg.leakRunM_fst` — the results of `leakRunM` are the denotation of the program in
  the empty call environment.
* `NFProg.leakRunM_eq_leakRun` — under a pure denotation the two leakage runs coincide.
* `NFProg.levelCheckD_sound` — events equal with results agreeing on the public positions,
  or a first difference at a declassification event.
* `NFProg.levelCheck'_sound`, `NFProg.nfCTRel_of_levelCheck'` — on valuations that agree on
  the public positions and from which the program runs, a program the checker accepts emits
  equal events.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-! ## The leakage run over a partial denotation -/

section Partial

variable [DialectDenoteM d Option]

/-- The run of a program from a valuation with the list of its events, for a dialect whose
    operations denote in `Option`. The events are those of `NFProg.leakRun`. -/
def NFProg.leakRunM (M : LeakModel d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Valuation Γ →
    Option (Valuation ts × List CTLeak)
  | _, _, .ret vs, V => some (Expr.lookupArgs vs V, [])
  | _, _, .var e k, V =>
      (e.denoteM (M := Option) V).bind fun x =>
        (NFProg.leakRunM M fuel k (V.extend x)).map fun r => (r.1, Expr.ctLeak M e V ++ r.2)
  | _, _, .forLoop count inits body k, V =>
      (forIterLeak
          (fun i acc => NFProg.leakRunM M fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRunM M fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .trip (HasWord64.toNat (d := d) (count.lookup V)) :: (r.2 ++ q.2))
  | _, _, .ifThenElse cond thn els k, V =>
      (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunM M fuel thn V
        else NFProg.leakRunM M fuel els V).bind fun r =>
        (NFProg.leakRunM M fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (r.2 ++ q.2))
  | _, _, .whileLoop inits body k, V =>
      (whileIterLeak (fun acc => NFProg.leakRunM M fuel body (hvAppend acc V)) fuel
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRunM M fuel k (hvAppend r.1 V)).map fun q => (q.1, r.2 ++ q.2)
  | _, _, .call .., _ => none

/-- Constant time of a program for the entry labels `L`, relative to the runs that succeed:
    two valuations that agree on the positions `L` marks public, from which the program runs
    to results, give equal events. -/
def NFCTRel (M : LeakModel d) {Γ : Ctxt d} {ts : List d.Ty} (L : Labels Γ) (fuel : Nat)
    (p : NFProg d Γ ts) : Prop :=
  ∀ (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation ts × List CTLeak), PubEqV L V₁ V₂ →
    NFProg.leakRunM M fuel p V₁ = some r₁ → NFProg.leakRunM M fuel p V₂ = some r₂ → r₁.2 = r₂.2

/-- **The results of the leakage run** are the denotation of the program in the empty call
    environment. -/
theorem NFProg.leakRunM_fst (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V : Valuation Γ) :
    (NFProg.leakRunM M fuel p V).map Prod.fst = p.denoteAt CallEnv.empty fuel V := by
  let _ : CallDenote d := ⟨CallEnv.empty⟩
  show (NFProg.leakRunM M fuel p V).map Prod.fst = p.denote fuel V
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.leakRunM, NFProg.denote, Option.bind_eq_bind]
      rcases e.denoteM (M := Option) V with _ | x
      · rfl
      · simp only [Option.bind_some, Option.map_map]
        exact ih _
  | forLoop count inits body k ihb ihk =>
      rw [NFProg.denote_forLoop, ← forIterLeak_fst _ _ (fun i acc => ihb _)]
      simp only [NFProg.leakRunM, Option.bind_eq_bind]
      rcases forIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | ifThenElse cond thn els k iht ihe ihk =>
      rw [NFProg.denote_ifThenElse]
      have hc : (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
          else els.denote fuel V) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunM M fuel thn V
            else NFProg.leakRunM M fuel els V).map Prod.fst := by
        split <;> simp only [iht, ihe]
      rw [hc]
      simp only [NFProg.leakRunM, Option.bind_eq_bind]
      rcases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunM M fuel thn V
        else NFProg.leakRunM M fuel els V) with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | whileLoop inits body k ihb ihk =>
      rw [NFProg.denote_whileLoop, ← whileIterLeak_fst _ _ (fun acc => ihb _)]
      simp only [NFProg.leakRunM, Option.bind_eq_bind]
      rcases whileIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | call => rfl

/-- **An event function of the expressions of `d`**: the events of a binding of an
    expression at a valuation of its context. -/
structure ExprEv (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] where
  /-- The events of the expression `e` at the valuation `V`. -/
  ev : (Γ : Ctxt d) → (t : d.Ty) → Expr d Γ t → Valuation Γ → List CTLeak

/-- The events of each operation of `d` on its argument values. `opLeak M` is the event
    function of a leakage model `M`. -/
abbrev OpEvents (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] : Type :=
  (op : d.Op) → HVector (fun t => ⟦t⟧) (DialectSignature.sig op) → List CTLeak

/-- The events of an expression under the event function `ev` of the operations: the events
    `ev` of its operation on its argument values. -/
def OpEvents.toExprEv (ev : OpEvents d) : ExprEv d :=
  ⟨fun _ _ e V => ev e.op (Expr.lookupArgs e.args V)⟩

/-- A leakage model gives the events `Expr.ctLeak M` of an expression. -/
instance : Coe (LeakModel d) (ExprEv d) := ⟨fun M => ⟨fun _ _ e V => Expr.ctLeak M e V⟩⟩

/-- The leakage run of a program at the call environment `E` with the events `ev`: a binding
    of an expression `e` at `V` emits `ev.ev _ _ e V`, a `call` node runs the callee of `E` at
    the looked-up arguments and emits no event, and its continuation runs at the results. At a
    leakage model `M`, whose events are `Expr.ctLeak M` by the coercion, it extends the run
    `NFProg.leakRunM M` by the calls of `E` (`leakRunMC_empty`). -/
def NFProg.leakRunMC (ev : ExprEv d) (E : CallEnv d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Valuation Γ →
    Option (Valuation ts × List CTLeak)
  | _, _, .ret vs, V => some (Expr.lookupArgs vs V, [])
  | _, _, .var e k, V =>
      (e.denoteM (M := Option) V).bind fun x =>
        (NFProg.leakRunMC ev E fuel k (V.extend x)).map fun r => (r.1, ev.ev _ _ e V ++ r.2)
  | _, _, .forLoop count inits body k, V =>
      (forIterLeak
          (fun i acc => NFProg.leakRunMC ev E fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRunMC ev E fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .trip (HasWord64.toNat (d := d) (count.lookup V)) :: (r.2 ++ q.2))
  | _, _, .ifThenElse cond thn els k, V =>
      (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunMC ev E fuel thn V
        else NFProg.leakRunMC ev E fuel els V).bind fun r =>
        (NFProg.leakRunMC ev E fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (r.2 ++ q.2))
  | _, _, .whileLoop inits body k, V =>
      (whileIterLeak (fun acc => NFProg.leakRunMC ev E fuel body (hvAppend acc V)) fuel
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRunMC ev E fuel k (hvAppend r.1 V)).map fun q => (q.1, r.2 ++ q.2)
  | _, _, .call (as := as) (rs := rs) f args k, V =>
      (E.call f as rs (Expr.lookupArgs args V)).bind fun r =>
        NFProg.leakRunMC ev E fuel k (hvAppend r V)

/-- **The results of the leakage run at a call environment** are the denotation of the
    program at that environment. -/
theorem NFProg.leakRunMC_fst (ev : ExprEv d) (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) :
    (NFProg.leakRunMC ev E fuel p V).map Prod.fst = p.denoteAt E fuel V := by
  let _ : CallDenote d := ⟨E⟩
  show (NFProg.leakRunMC ev E fuel p V).map Prod.fst = p.denote fuel V
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.leakRunMC, NFProg.denote, Option.bind_eq_bind]
      rcases e.denoteM (M := Option) V with _ | x
      · rfl
      · simp only [Option.bind_some, Option.map_map]
        exact ih _
  | forLoop count inits body k ihb ihk =>
      rw [NFProg.denote_forLoop, ← forIterLeak_fst _ _ (fun i acc => ihb _)]
      simp only [NFProg.leakRunMC, Option.bind_eq_bind]
      rcases forIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | ifThenElse cond thn els k iht ihe ihk =>
      rw [NFProg.denote_ifThenElse]
      have hc : (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
          else els.denote fuel V) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunMC ev E fuel thn V
            else NFProg.leakRunMC ev E fuel els V).map Prod.fst := by
        split <;> simp only [iht, ihe]
      rw [hc]
      simp only [NFProg.leakRunMC, Option.bind_eq_bind]
      rcases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunMC ev E fuel thn V
        else NFProg.leakRunMC ev E fuel els V) with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | whileLoop inits body k ihb ihk =>
      rw [NFProg.denote_whileLoop, ← whileIterLeak_fst _ _ (fun acc => ihb _)]
      simp only [NFProg.leakRunMC, Option.bind_eq_bind]
      rcases whileIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | call f args k ih =>
      rw [NFProg.denote_call]
      simp only [NFProg.leakRunMC, Option.bind_eq_bind]
      rcases E.call f _ _ (Expr.lookupArgs args V) with _ | r
      · rfl
      · exact ih _

/-- **On a program without `call` the leakage run at a call environment is `leakRunM`.** -/
theorem NFProg.leakRunMC_of_callFree (M : LeakModel d) (E : CallEnv d) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.callFree = true)
    (V : Valuation Γ) : NFProg.leakRunMC M E fuel p V = NFProg.leakRunM M fuel p V := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.callFree] at hp
      simp only [NFProg.leakRunMC, NFProg.leakRunM, ih hp]
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [NFProg.leakRunMC, NFProg.leakRunM, ihb hp.1, ihk hp.2]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [NFProg.leakRunMC, NFProg.leakRunM, iht hp.1.1, ihe hp.1.2, ihk hp.2]
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [NFProg.leakRunMC, NFProg.leakRunM, ihb hp.1, ihk hp.2]
  | call => simp [NFProg.callFree] at hp

/-- **At the empty call environment the leakage run is `leakRunM`**: both refuse a `call`
    node. -/
theorem NFProg.leakRunMC_empty (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V : Valuation Γ) :
    NFProg.leakRunMC M CallEnv.empty fuel p V = NFProg.leakRunM M fuel p V := by
  induction p with
  | ret vs => rfl
  | var e k ih => simp only [NFProg.leakRunMC, NFProg.leakRunM, ih]
  | forLoop count inits body k ihb ihk => simp only [NFProg.leakRunMC, NFProg.leakRunM, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.leakRunMC, NFProg.leakRunM, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk => simp only [NFProg.leakRunMC, NFProg.leakRunM, ihb, ihk]
  | call => rfl

/-- **The leakage run reads the call environment at the calls of the program only**: two
    environments that agree at every call of `p` give the same run. -/
theorem NFProg.leakRunMC_congr (ev : ExprEv d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (E E' : CallEnv d)
    (h : ∀ f as rs (x : Valuation as), p.Calls f as rs → E.call f as rs x = E'.call f as rs x)
    (fuel : Nat) (V : Valuation Γ) :
    NFProg.leakRunMC ev E fuel p V = NFProg.leakRunMC ev E' fuel p V := by
  induction p with
  | ret vs => rfl
  | var e k ih => simp only [NFProg.leakRunMC, ih h]
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.leakRunMC, ihb fun f as rs x hc => h f as rs x (Or.inl hc),
        ihk fun f as rs x hc => h f as rs x (Or.inr hc)]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.leakRunMC, iht fun f as rs x hc => h f as rs x (Or.inl hc),
        ihe fun f as rs x hc => h f as rs x (Or.inr (Or.inl hc)),
        ihk fun f as rs x hc => h f as rs x (Or.inr (Or.inr hc))]
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.leakRunMC, ihb fun f as rs x hc => h f as rs x (Or.inl hc),
        ihk fun f as rs x hc => h f as rs x (Or.inr hc)]
  | call f args k ih =>
      simp only [NFProg.leakRunMC, h f _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩),
        ih fun f as rs x hc => h f as rs x (Or.inr hc)]

end Partial

/-- Every operation the straight-line program `c` binds has no event at the leakage
    model `M`. -/
def Com.OpsQuiet (M : LeakModel d) : {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e k => M.kind e.op = .quiet ∧ Com.OpsQuiet M k

/-- **A straight-line program of quiet operations has no event**: its embedding runs to its
    denotation and to the empty list of events. -/
theorem NFProg.leakRunM_ofCom_quiet [DialectDenote d] (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (hc : Com.OpsQuiet M c) (V : Valuation Γ) :
    NFProg.leakRunM M fuel (NFProg.ofCom c) V = some (.cons (c.denote V) .nil, []) := by
  induction c with
  | ret v => rfl
  | var e k ih =>
      obtain ⟨he, hk⟩ := hc
      simp only [NFProg.ofCom, NFProg.leakRunM, Expr.denoteM_option_eq_some, Option.bind_some,
        ih hk, Option.map_some, Expr.ctLeak, opLeak, he, List.nil_append]
      rfl

/-- **Under a pure denotation the two leakage runs coincide.** -/
theorem NFProg.leakRunM_eq_leakRun [DialectDenote d] (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) :
    NFProg.leakRunM M fuel p V = NFProg.leakRun M fuel p V := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.leakRunM, NFProg.leakRun, Expr.denoteM_option_eq_some,
        Option.bind_some, ih]
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.leakRunM, NFProg.leakRun, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.leakRunM, NFProg.leakRun, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.leakRunM, NFProg.leakRun, ihb, ihk]
  | call => rfl

/-! ## The level checker with branches and exit-flag loops -/

/-- The levels of the result of an exit-flag loop body keep the carried levels `A`: a public
    flag, and carried levels at most `A`. -/
def flagOk {cs : List d.Ty} (FB : Labels (HasBitType.bit (d := d) :: cs)) (A : Labels cs) :
    Bool :=
  decide (FB.head = .Public) && lvlsLe FB.tail A

/-! ### First differences at a declassification event -/

/-- The traces `t₁` and `t₂` share a prefix, after which their next events differ and both
    satisfy `isDeclEv`. -/
def DeclDiff (isDeclEv : CTLeak → Bool) (t₁ t₂ : List CTLeak) : Prop :=
  ∃ (pre s₁ s₂ : List CTLeak) (a₁ a₂ : CTLeak), a₁ ≠ a₂ ∧ isDeclEv a₁ = true ∧
    isDeclEv a₂ = true ∧ t₁ = pre ++ a₁ :: s₁ ∧ t₂ = pre ++ a₂ :: s₂

namespace DeclDiff

variable {D : CTLeak → Bool} {t₁ t₂ : List CTLeak}

theorem append_right (h : DeclDiff D t₁ t₂) (u₁ u₂ : List CTLeak) :
    DeclDiff D (t₁ ++ u₁) (t₂ ++ u₂) := by
  obtain ⟨pre, s₁, s₂, a₁, a₂, hne, h₁, h₂, rfl, rfl⟩ := h
  exact ⟨pre, s₁ ++ u₁, s₂ ++ u₂, a₁, a₂, hne, h₁, h₂, by simp, by simp⟩

/-- A common prefix keeps a first difference at a declassification event. -/
theorem prepend (c : List CTLeak) (h : DeclDiff D t₁ t₂) :
    DeclDiff D (c ++ t₁) (c ++ t₂) := by
  obtain ⟨pre, s₁, s₂, a₁, a₂, hne, h₁, h₂, rfl, rfl⟩ := h
  exact ⟨c ++ pre, s₁, s₂, a₁, a₂, hne, h₁, h₂, by simp, by simp⟩

/-- No two traces first differ at a declassification event when no event is one. -/
theorem not_false : ¬ DeclDiff (fun _ => false) t₁ t₂ := by
  rintro ⟨_, _, _, _, _, _, h, _⟩
  exact Bool.false_ne_true h

end DeclDiff

/-- Sequential composition of two pieces of trace, each with equal events and a property, or
    a first difference at a declassification event. -/
theorem declDiff_seq {D : CTLeak → Bool} {t₁ t₂ u₁ u₂ : List CTLeak} {P Q : Prop}
    (h : (t₁ = t₂ ∧ P) ∨ DeclDiff D t₁ t₂)
    (hk : P → (u₁ = u₂ ∧ Q) ∨ DeclDiff D u₁ u₂) :
    (t₁ ++ u₁ = t₂ ++ u₂ ∧ Q) ∨ DeclDiff D (t₁ ++ u₁) (t₂ ++ u₂) := by
  rcases h with ⟨rfl, hP⟩ | hd
  · rcases hk hP with ⟨rfl, hQ⟩ | hd
    · exact Or.inl ⟨rfl, hQ⟩
    · exact Or.inr (hd.prepend _)
  · exact Or.inr (hd.append_right _ _)

/-- A common first event keeps equal events or a first difference at a declassification
    event. -/
theorem declDiff_cons {D : CTLeak → Bool} {t₁ t₂ : List CTLeak} {Q : Prop}
    (c : CTLeak) (h : (t₁ = t₂ ∧ Q) ∨ DeclDiff D t₁ t₂) :
    (c :: t₁ = c :: t₂ ∧ Q) ∨ DeclDiff D (c :: t₁) (c :: t₂) := by
  rcases h with ⟨rfl, hQ⟩ | hd
  · exact Or.inl ⟨rfl, hQ⟩
  · exact Or.inr (hd.prepend [c])

/-- **The level checker with branches, exit-flag loops and declassification.** It extends
    `NFProg.levelCheck`: a branch requires a public condition, and its results take the join
    of the levels of its arms; an exit-flag loop requires a public flag, and its carried
    values take the levels of their initial values when the body keeps them (`flagOk`), and
    the secret level otherwise. An operation marked by `isDeclass` accepts arguments at every
    level and gives its result the public level. -/
def NFProg.levelCheckD (M : LeakModel d) (isDeclass : d.Op → Bool) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Labels Γ → Option (Labels ts)
  | _, _, .ret vs, L => some (retLvls L vs)
  | _, _, .var e k, L =>
      if isDeclass e.op then NFProg.levelCheckD M isDeclass k (.cons .Public L)
      else if opAccepts M e.op (argLvls L e.args) then
        NFProg.levelCheckD M isDeclass k (.cons (joinAll (argLvls L e.args)) L)
      else none
  | _, _, .forLoop (cs := cs') count inits body k, L =>
      if lvlOf count L = .Public then
        if (NFProg.levelCheckD M isDeclass body
            (hvAppend (retLvls L inits) (.cons .Public L))).any
            (fun B => lvlsLe B (retLvls L inits)) then
          NFProg.levelCheckD M isDeclass k (hvAppend (retLvls L inits) L)
        else if (NFProg.levelCheckD M isDeclass body
            (hvAppend (allSecret cs') (.cons .Public L))).isSome
        then NFProg.levelCheckD M isDeclass k (hvAppend (allSecret cs') L)
        else none
      else none
  | _, _, .ifThenElse cond thn els k, L =>
      if lvlOf cond L = .Public then
        match NFProg.levelCheckD M isDeclass thn L, NFProg.levelCheckD M isDeclass els L with
        | some R₁, some R₂ => NFProg.levelCheckD M isDeclass k (hvAppend (lvlJoin R₁ R₂) L)
        | _, _ => none
      else none
  | _, _, .whileLoop (cs := cs') inits body k, L =>
      if (NFProg.levelCheckD M isDeclass body (hvAppend (retLvls L inits) L)).any
          (fun FB => flagOk FB (retLvls L inits)) then
        NFProg.levelCheckD M isDeclass k (hvAppend (retLvls L inits) L)
      else if (NFProg.levelCheckD M isDeclass body (hvAppend (allSecret cs') L)).any
          (fun FB => flagOk FB (allSecret cs')) then
        NFProg.levelCheckD M isDeclass k (hvAppend (allSecret cs') L)
      else none
  | _, _, .call .., _ => none

/-- **The level checker with branches and exit-flag loops**: `NFProg.levelCheckD` with no
    marked operation. It is irreducible, and its equation lemmas are the clauses of
    `levelCheckD` at the constant `false` predicate (`levelCheck'_ret`, …, `levelCheck'_call`),
    so that `simp [NFProg.levelCheck']` rewrites by these clauses. -/
def NFProg.levelCheck' (M : LeakModel d) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Labels Γ → Option (Labels ts) :=
  NFProg.levelCheckD M (fun _ => false)

/-- Unfolding lemma of `NFProg.levelCheck'`. -/
theorem NFProg.levelCheck'_def (M : LeakModel d) :
    @NFProg.levelCheck' d _ _ _ _ M = @NFProg.levelCheckD d _ _ _ _ M (fun _ => false) := rfl

/-- Equation lemma of `NFProg.levelCheck'` at `ret`. -/
theorem NFProg.levelCheck'_ret (M : LeakModel d) {Γ : Ctxt d} {ts : List d.Ty}
    (vs : HVector (fun t => Var Γ t) ts) (L : Labels Γ) :
    NFProg.levelCheck' M (.ret vs) L = some (retLvls L vs) := rfl

/-- Equation lemma of `NFProg.levelCheck'` at `var`. -/
theorem NFProg.levelCheck'_var (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty}
    (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts) (L : Labels Γ) :
    NFProg.levelCheck' M (.var e k) L =
      if opAccepts M e.op (argLvls L e.args) then
        NFProg.levelCheck' M k (.cons (joinAll (argLvls L e.args)) L)
      else none := rfl

/-- Equation lemma of `NFProg.levelCheck'` at `forLoop`. -/
theorem NFProg.levelCheck'_forLoop (M : LeakModel d) {Γ : Ctxt d} {cs ts : List d.Ty}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (L : Labels Γ) :
    NFProg.levelCheck' M (.forLoop count inits body k) L =
      if lvlOf count L = .Public then
        if (NFProg.levelCheck' M body (hvAppend (retLvls L inits) (.cons .Public L))).any
            (fun B => lvlsLe B (retLvls L inits)) then
          NFProg.levelCheck' M k (hvAppend (retLvls L inits) L)
        else if (NFProg.levelCheck' M body (hvAppend (allSecret cs) (.cons .Public L))).isSome
        then NFProg.levelCheck' M k (hvAppend (allSecret cs) L)
        else none
      else none := rfl

/-- Equation lemma of `NFProg.levelCheck'` at `ifThenElse`. -/
theorem NFProg.levelCheck'_ifThenElse (M : LeakModel d) {Γ : Ctxt d} {rs ts : List d.Ty}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts) (L : Labels Γ) :
    NFProg.levelCheck' M (.ifThenElse cond thn els k) L =
      if lvlOf cond L = .Public then
        match NFProg.levelCheck' M thn L, NFProg.levelCheck' M els L with
        | some R₁, some R₂ => NFProg.levelCheck' M k (hvAppend (lvlJoin R₁ R₂) L)
        | _, _ => none
      else none := rfl

/-- Equation lemma of `NFProg.levelCheck'` at `whileLoop`. -/
theorem NFProg.levelCheck'_whileLoop (M : LeakModel d) {Γ : Ctxt d} {cs ts : List d.Ty}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts)
    (L : Labels Γ) :
    NFProg.levelCheck' M (.whileLoop inits body k) L =
      if (NFProg.levelCheck' M body (hvAppend (retLvls L inits) L)).any
          (fun FB => flagOk FB (retLvls L inits)) then
        NFProg.levelCheck' M k (hvAppend (retLvls L inits) L)
      else if (NFProg.levelCheck' M body (hvAppend (allSecret cs) L)).any
          (fun FB => flagOk FB (allSecret cs)) then
        NFProg.levelCheck' M k (hvAppend (allSecret cs) L)
      else none := rfl

/-- Equation lemma of `NFProg.levelCheck'` at `call`. -/
theorem NFProg.levelCheck'_call (M : LeakModel d) {Γ : Ctxt d} {as rs ts : List d.Ty}
    (f : String) (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts)
    (L : Labels Γ) :
    NFProg.levelCheck' M (.call f args k) L = none := rfl

attribute [irreducible] NFProg.levelCheck'

attribute [eqns NFProg.levelCheck'_ret NFProg.levelCheck'_var NFProg.levelCheck'_forLoop
  NFProg.levelCheck'_ifThenElse NFProg.levelCheck'_whileLoop NFProg.levelCheck'_call]
  NFProg.levelCheck'

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] in
/-- The iterations of two counted-loop runs that both succeed, whose steps from values that
    agree on the public positions of `A` emit equal events and end at results that agree on
    those positions, or first differ at a declassification event, do the same. -/
theorem forIterLeak_relD (D : CTLeak → Bool) {cs : List d.Ty} (A : Labels cs)
    (step₁ step₂ : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (hs : ∀ i (X₁ X₂ : Valuation cs) r₁ r₂, PubEqV A X₁ X₂ → step₁ i X₁ = some r₁ →
      step₂ i X₂ = some r₂ → (r₁.2 = r₂.2 ∧ PubEqV A r₁.1 r₂.1) ∨ DeclDiff D r₁.2 r₂.2) :
    ∀ (is : List Nat) (X₁ X₂ : Valuation cs) q₁ q₂, PubEqV A X₁ X₂ →
      forIterLeak step₁ is X₁ = some q₁ → forIterLeak step₂ is X₂ = some q₂ →
      (q₁.2 = q₂.2 ∧ PubEqV A q₁.1 q₂.1) ∨ DeclDiff D q₁.2 q₂.2
  | [], X₁, X₂, q₁, q₂, h, h₁, h₂ => by
      simp only [forIterLeak, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      exact Or.inl ⟨rfl, h⟩
  | i :: is, X₁, X₂, q₁, q₂, h, h₁, h₂ => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨r₁, hr₁, q₁', hq₁, rfl⟩ := h₁
      obtain ⟨r₂, hr₂, q₂', hq₂, rfl⟩ := h₂
      exact declDiff_seq (hs i X₁ X₂ r₁ r₂ h hr₁ hr₂) fun hp =>
        forIterLeak_relD D A step₁ step₂ hs is _ _ q₁' q₂' hp hq₁ hq₂

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] in
/-- The iterations of two counted-loop runs that both succeed, whose steps preserve the
    agreement on the public positions of `A` and emit equal events when they succeed, emit
    equal events and end at results that agree on the public positions of `A`. -/
theorem forIterLeak_relM {cs : List d.Ty} (A : Labels cs)
    (step₁ step₂ : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (hs : ∀ i (X₁ X₂ : Valuation cs) r₁ r₂, PubEqV A X₁ X₂ → step₁ i X₁ = some r₁ →
      step₂ i X₂ = some r₂ → r₁.2 = r₂.2 ∧ PubEqV A r₁.1 r₂.1) :
    ∀ (is : List Nat) (X₁ X₂ : Valuation cs) q₁ q₂, PubEqV A X₁ X₂ →
      forIterLeak step₁ is X₁ = some q₁ → forIterLeak step₂ is X₂ = some q₂ →
      q₁.2 = q₂.2 ∧ PubEqV A q₁.1 q₂.1 :=
  fun is X₁ X₂ q₁ q₂ h h₁ h₂ =>
    (forIterLeak_relD (fun _ => false) A step₁ step₂
      (fun i X₁ X₂ r₁ r₂ hX h₁ h₂ => Or.inl (hs i X₁ X₂ r₁ r₂ hX h₁ h₂))
      is X₁ X₂ q₁ q₂ h h₁ h₂).resolve_right DeclDiff.not_false

omit [DialectSignature d] [HasWord64 d] in
/-- The iterations of two exit-flag loop runs that both succeed, whose bodies from values that
    agree on the public positions of `A` emit equal events, return equal flags and carried
    values that agree on those positions, or first differ at a declassification event, emit
    equal events and end at results that agree on those positions, or first differ at a
    declassification event. -/
theorem whileIterLeak_relD (D : CTLeak → Bool) {cs : List d.Ty} (A : Labels cs)
    (step₁ step₂ : Valuation cs →
      Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (hs : ∀ (X₁ X₂ : Valuation cs) r₁ r₂, PubEqV A X₁ X₂ → step₁ X₁ = some r₁ →
      step₂ X₂ = some r₂ →
      (r₁.2 = r₂.2 ∧ r₁.1.head = r₂.1.head ∧ PubEqV A r₁.1.tail r₂.1.tail) ∨
        DeclDiff D r₁.2 r₂.2) :
    ∀ (n : Nat) (X₁ X₂ : Valuation cs) q₁ q₂, PubEqV A X₁ X₂ →
      whileIterLeak step₁ n X₁ = some q₁ → whileIterLeak step₂ n X₂ = some q₂ →
      (q₁.2 = q₂.2 ∧ PubEqV A q₁.1 q₂.1) ∨ DeclDiff D q₁.2 q₂.2
  | 0, _, _, _, _, _, h₁, _ => by simp [whileIterLeak] at h₁
  | n + 1, X₁, X₂, q₁, q₂, h, h₁, h₂ => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨r₁, hr₁, h₁⟩ := h₁
      obtain ⟨r₂, hr₂, h₂⟩ := h₂
      rcases hs X₁ X₂ r₁ r₂ h hr₁ hr₂ with ⟨he, hf, hp⟩ | hd
      · rw [← hf] at h₂
        split at h₁
        · rw [if_pos (by assumption)] at h₂
          obtain ⟨q₁', hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
          obtain ⟨q₂', hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
          exact declDiff_seq (Or.inl ⟨he, trivial⟩) fun _ => declDiff_cons _
            (whileIterLeak_relD D A step₁ step₂ hs n _ _ q₁' q₂' hp hq₁ hq₂)
        · rw [if_neg (by assumption)] at h₂
          simp only [Option.some.injEq] at h₁ h₂
          subst h₁ h₂
          exact Or.inl ⟨by simp only [he], hp⟩
      · obtain ⟨u₁, hu₁⟩ : ∃ u, q₁.2 = r₁.2 ++ u := by
          split at h₁
          · obtain ⟨q', -, rfl⟩ := Option.map_eq_some_iff.mp h₁
            exact ⟨_, rfl⟩
          · simp only [Option.some.injEq] at h₁
            subst h₁
            exact ⟨_, rfl⟩
        obtain ⟨u₂, hu₂⟩ : ∃ u, q₂.2 = r₂.2 ++ u := by
          split at h₂
          · obtain ⟨q', -, rfl⟩ := Option.map_eq_some_iff.mp h₂
            exact ⟨_, rfl⟩
          · simp only [Option.some.injEq] at h₂
            subst h₂
            exact ⟨_, rfl⟩
        rw [hu₁, hu₂]
        exact Or.inr (hd.append_right _ _)

omit [DialectSignature d] [HasWord64 d] in
/-- The iterations of two exit-flag loop runs that both succeed, whose bodies emit equal
    events, return equal flags and carried values that agree on the public positions of `A`
    when they succeed, emit equal events and end at results that agree on the public
    positions of `A`. -/
theorem whileIterLeak_relM {cs : List d.Ty} (A : Labels cs)
    (step₁ step₂ : Valuation cs →
      Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (hs : ∀ (X₁ X₂ : Valuation cs) r₁ r₂, PubEqV A X₁ X₂ → step₁ X₁ = some r₁ →
      step₂ X₂ = some r₂ → r₁.2 = r₂.2 ∧ r₁.1.head = r₂.1.head ∧ PubEqV A r₁.1.tail r₂.1.tail) :
    ∀ (n : Nat) (X₁ X₂ : Valuation cs) q₁ q₂, PubEqV A X₁ X₂ →
      whileIterLeak step₁ n X₁ = some q₁ → whileIterLeak step₂ n X₂ = some q₂ →
      q₁.2 = q₂.2 ∧ PubEqV A q₁.1 q₂.1 :=
  fun n X₁ X₂ q₁ q₂ h h₁ h₂ =>
    (whileIterLeak_relD (fun _ => false) A step₁ step₂
      (fun X₁ X₂ r₁ r₂ hX h₁ h₂ => Or.inl (hs X₁ X₂ r₁ r₂ hX h₁ h₂))
      n X₁ X₂ q₁ q₂ h h₁ h₂).resolve_right DeclDiff.not_false

section Partial

variable [DialectDenoteM d Option]

/-- **The marked operations are declassifications** for the leakage model `M`: each emits
    one event satisfying `isDeclEv`, and this event determines the result of the operation. -/
structure DeclassOk (M : LeakModel d) (isDeclass : d.Op → Bool) (isDeclEv : CTLeak → Bool) :
    Prop where
  /-- A marked operation emits one declassification event. -/
  ev_single : ∀ op, isDeclass op = true → ∀ vals, ∃ a, opLeak M op vals = [a] ∧ isDeclEv a = true
  /-- The event of a marked operation determines its result. -/
  denoteM_of_ev : ∀ op, isDeclass op = true → ∀ vals₁ vals₂,
    opLeak M op vals₁ = opLeak M op vals₂ →
    DialectDenoteM.denoteM (M := Option) op vals₁ = DialectDenoteM.denoteM (M := Option) op vals₂

omit [HasWord64 d] [HasBoolBit d] in
/-- With no marked operation, every predicate on events makes the marked operations
    declassifications. -/
theorem declassOk_false (M : LeakModel d) (isDeclEv : CTLeak → Bool) :
    DeclassOk M (fun _ => false) isDeclEv where
  ev_single _ h := absurd h Bool.false_ne_true
  denoteM_of_ev _ h := absurd h Bool.false_ne_true

/-- **Soundness of the level checker with declassification.** On valuations that agree on
    the positions `L` marks public, two runs of a program the checker accepts with result
    levels `R` that both succeed emit equal events and end at results that agree on the
    positions `R` marks public, or their events first differ at a declassification event. -/
theorem NFProg.levelCheckD_sound (M : LeakModel d) (isDeclass : d.Op → Bool)
    (isDeclEv : CTLeak → Bool) (hD : DeclassOk M isDeclass isDeclEv) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ (L : Labels Γ) (R : Labels ts), NFProg.levelCheckD M isDeclass p L = some R →
      ∀ (V₁ V₂ : Valuation Γ) r₁ r₂, PubEqV L V₁ V₂ →
      NFProg.leakRunM M fuel p V₁ = some r₁ → NFProg.leakRunM M fuel p V₂ = some r₂ →
      (r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1) ∨ DeclDiff isDeclEv r₁.2 r₂.2 := by
  induction p with
  | ret vs =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheckD, Option.some.injEq] at h
      simp only [NFProg.leakRunM, Option.some.injEq] at h₁ h₂
      subst h h₁ h₂
      exact Or.inl ⟨rfl, pubEqV_retLvls hp vs⟩
  | var e k ih =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheckD] at h
      simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨x₁, hx₁, s₁, hs₁, rfl⟩ := h₁
      obtain ⟨x₂, hx₂, s₂, hs₂, rfl⟩ := h₂
      split at h
      · rename_i hdecl
        by_cases hev : Expr.ctLeak M e V₁ = Expr.ctLeak M e V₂
        · have hx : x₁ = x₂ := by
            have hden : e.denoteM (M := Option) V₁ = e.denoteM (M := Option) V₂ := by
              unfold Expr.denoteM
              rw [hD.denoteM_of_ev e.op hdecl (Expr.lookupArgs e.args V₁)
                (Expr.lookupArgs e.args V₂) hev]
            rw [hx₁, hx₂, Option.some.injEq] at hden
            exact hden
          have hp' : PubEqV (.cons .Public L) (V₁.extend x₁) (V₂.extend x₂) :=
            pubEqV_cons hp _ _ _ fun _ => hx
          exact declDiff_seq (Or.inl ⟨hev, trivial⟩) fun _ => ih _ R h _ _ s₁ s₂ hp' hs₁ hs₂
        · obtain ⟨a₁, ha₁, hd₁⟩ := hD.ev_single e.op hdecl (Expr.lookupArgs e.args V₁)
          obtain ⟨a₂, ha₂, hd₂⟩ := hD.ev_single e.op hdecl (Expr.lookupArgs e.args V₂)
          refine Or.inr ⟨[], s₁.2, s₂.2, a₁, a₂, ?_, hd₁, hd₂, ?_, ?_⟩
          · rintro rfl
            exact hev (by simp only [Expr.ctLeak, ha₁, ha₂])
          · simp [Expr.ctLeak, ha₁]
          · simp [Expr.ctLeak, ha₂]
      · split at h
        · rename_i hacc
          have hp' : PubEqV (.cons (joinAll (argLvls L e.args)) L) (V₁.extend x₁)
              (V₂.extend x₂) :=
            pubEqV_cons hp _ _ _ fun hj => by
              have hden : e.denoteM (M := Option) V₁ = e.denoteM (M := Option) V₂ := by
                unfold Expr.denoteM
                rw [lookupArgs_eq_of_pub hp e.args hj]
              rw [hx₁, hx₂, Option.some.injEq] at hden
              exact hden
          have hev : Expr.ctLeak M e V₁ = Expr.ctLeak M e V₂ := by
            simp only [Expr.ctLeak, opLeak_eq_of_accepts M hp e.op e.args hacc]
          exact declDiff_seq (Or.inl ⟨hev, trivial⟩) fun _ => ih _ R h _ _ s₁ s₂ hp' hs₁ hs₂
        · cases h
  | forLoop count inits body k ihb ihk =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheckD] at h
      split at h
      · rename_i hcount
        have htrip : count.lookup V₁ = count.lookup V₂ := hp _ count hcount
        have hloop : ∀ A : Labels _,
            (NFProg.levelCheckD M isDeclass body (hvAppend A (.cons .Public L))).any
              (fun B => lvlsLe B A) = true →
            NFProg.levelCheckD M isDeclass k (hvAppend A L) = some R → PubEqV A
              (Expr.lookupArgs inits V₁) (Expr.lookupArgs inits V₂) →
            (r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1) ∨ DeclDiff isDeclEv r₁.2 r₂.2 := by
          intro A hbody hk hinit
          obtain ⟨B, hB, hle⟩ : ∃ B, NFProg.levelCheckD M isDeclass body
              (hvAppend A (.cons .Public L)) = some B ∧ lvlsLe B A = true := by
            rcases hb : NFProg.levelCheckD M isDeclass body (hvAppend A (.cons .Public L))
              with _ | B
            · rw [hb] at hbody; cases hbody
            · rw [hb] at hbody; exact ⟨B, rfl, hbody⟩
          simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
          obtain ⟨q₁, k₁, s₁, l₁, rfl⟩ := h₁
          obtain ⟨q₂, k₂, s₂, l₂, rfl⟩ := h₂
          rw [← htrip] at k₂
          have hit := forIterLeak_relD isDeclEv A _ _
            (fun i X₁ X₂ a₁ a₂ hX ha₁ ha₂ => by
              rcases ihb _ B hB _ _ a₁ a₂
                (pubEqV_hvAppend (pubEqV_cons hp .Public _ _ fun _ => rfl) A X₁ X₂ hX) ha₁ ha₂
                with ⟨he, hr⟩ | hd
              · exact Or.inl ⟨he, pubEqV_mono B A hle _ _ hr⟩
              · exact Or.inr hd)
            _ _ _ q₁ q₂ hinit k₁ k₂
          rw [htrip]
          exact declDiff_cons _ (declDiff_seq hit fun kr =>
            ihk _ R hk _ _ s₁ s₂ (pubEqV_hvAppend hp A _ _ kr) l₁ l₂)
        split at h
        · exact hloop _ (by assumption) h (pubEqV_retLvls hp inits)
        · split at h
          · rename_i hsome
            refine hloop _ ?_ h (pubEqV_allSecret _ _)
            rcases hb : NFProg.levelCheckD M isDeclass body
                (hvAppend (allSecret _) (.cons .Public L)) with _ | B
            · rw [hb] at hsome; cases hsome
            · exact lvlsLe_allSecret B
          · cases h
      · cases h
  | ifThenElse cond thn els k iht ihe ihk =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheckD] at h
      split at h
      · rename_i hcond
        have hc : cond.lookup V₁ = cond.lookup V₂ := hp _ cond hcond
        split at h
        · rename_i R₁ R₂ hR₁ hR₂
          simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
          obtain ⟨a₁, ha₁, s₁, l₁, rfl⟩ := h₁
          obtain ⟨a₂, ha₂, s₂, l₂, rfl⟩ := h₂
          rw [← hc] at ha₂
          have harm : (a₁.2 = a₂.2 ∧ PubEqV (lvlJoin R₁ R₂) a₁.1 a₂.1) ∨
              DeclDiff isDeclEv a₁.2 a₂.2 := by
            split at ha₁
            · rw [if_pos (by assumption)] at ha₂
              rcases iht L R₁ hR₁ _ _ _ _ hp ha₁ ha₂ with ⟨e, r⟩ | hd
              · exact Or.inl ⟨e, pubEqV_mono _ _ (lvlsLe_join_left R₁ R₂) _ _ r⟩
              · exact Or.inr hd
            · rw [if_neg (by assumption)] at ha₂
              rcases ihe L R₂ hR₂ _ _ _ _ hp ha₁ ha₂ with ⟨e, r⟩ | hd
              · exact Or.inl ⟨e, pubEqV_mono _ _ (lvlsLe_join_right R₁ R₂) _ _ r⟩
              · exact Or.inr hd
          rw [hc]
          exact declDiff_cons _ (declDiff_seq harm fun hr =>
            ihk _ R h _ _ s₁ s₂ (pubEqV_hvAppend hp _ _ _ hr) l₁ l₂)
        · cases h
      · cases h
  | whileLoop inits body k ihb ihk =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheckD] at h
      have hloop : ∀ A : Labels _,
          (NFProg.levelCheckD M isDeclass body (hvAppend A L)).any
            (fun FB => flagOk FB A) = true →
          NFProg.levelCheckD M isDeclass k (hvAppend A L) = some R → PubEqV A
            (Expr.lookupArgs inits V₁) (Expr.lookupArgs inits V₂) →
          (r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1) ∨ DeclDiff isDeclEv r₁.2 r₂.2 := by
        intro A hbody hk hinit
        obtain ⟨FB, hB, hok⟩ : ∃ FB, NFProg.levelCheckD M isDeclass body (hvAppend A L) =
            some FB ∧ flagOk FB A = true := by
          rcases hb : NFProg.levelCheckD M isDeclass body (hvAppend A L) with _ | FB
          · rw [hb] at hbody; cases hbody
          · rw [hb] at hbody; exact ⟨FB, rfl, hbody⟩
        simp only [flagOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
        obtain ⟨q₁, k₁, s₁, l₁, rfl⟩ := h₁
        obtain ⟨q₂, k₂, s₂, l₂, rfl⟩ := h₂
        have hit := whileIterLeak_relD isDeclEv A _ _
          (fun X₁ X₂ a₁ a₂ hX ha₁ ha₂ => by
            rcases ihb _ FB hB _ _ a₁ a₂ (pubEqV_hvAppend hp A X₁ X₂ hX) ha₁ ha₂
              with ⟨he, hr⟩ | hd
            · refine Or.inl ?_
              revert hr
              rcases FB with _ | ⟨f, B⟩
              rcases a₁ with ⟨_ | ⟨x₁, Y₁⟩, t₁⟩
              rcases a₂ with ⟨_ | ⟨x₂, Y₂⟩, t₂⟩
              intro hr
              refine ⟨he, hr _ .here hok.1, pubEqV_mono B A hok.2 _ _ ?_⟩
              exact fun t' v hv => hr t' (.there v) hv
            · exact Or.inr hd)
          _ _ _ q₁ q₂ hinit k₁ k₂
        exact declDiff_seq hit fun kr =>
          ihk _ R hk _ _ s₁ s₂ (pubEqV_hvAppend hp A _ _ kr) l₁ l₂
      split at h
      · exact hloop _ (by assumption) h (pubEqV_retLvls hp inits)
      · split at h
        · exact hloop _ (by assumption) h (pubEqV_allSecret _ _)
        · cases h
  | call => intro L R h; simp [NFProg.levelCheckD] at h

/-- **Soundness of the level checker with branches and exit-flag loops.** On valuations that
    agree on the positions `L` marks public, two runs of a program the checker accepts with
    result levels `R` that both succeed emit equal events and end at results that agree on
    the positions `R` marks public. -/
theorem NFProg.levelCheck'_sound (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ (L : Labels Γ) (R : Labels ts), NFProg.levelCheck' M p L = some R →
      ∀ (V₁ V₂ : Valuation Γ) r₁ r₂, PubEqV L V₁ V₂ →
      NFProg.leakRunM M fuel p V₁ = some r₁ → NFProg.leakRunM M fuel p V₂ = some r₂ →
      r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1 := by
  intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
  rw [NFProg.levelCheck'_def] at h
  exact (NFProg.levelCheckD_sound M (fun _ => false) (fun _ => false) (declassOk_false M _) fuel p
    L R h V₁ V₂ r₁ r₂ hp h₁ h₂).resolve_right DeclDiff.not_false

/-- A program the checker `levelCheck'` accepts for the entry labels `L` is constant time for
    `L` relative to the runs that succeed, at every fuel. -/
theorem NFProg.nfCTRel_of_levelCheck' (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' M p L).isSome) : NFCTRel M L fuel p := by
  intro V₁ V₂ r₁ r₂ hp h₁ h₂
  rcases hR : NFProg.levelCheck' M p L with _ | R
  · rw [hR] at h; cases h
  · exact (NFProg.levelCheck'_sound M fuel p L R hR V₁ V₂ r₁ r₂ hp h₁ h₂).1

end Partial

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
