/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg

/-!
# The constant-time leakage of `NFProg` and its level checker

The leakage of a structured program of `NFProg d` over a leakage model `M` of the dialect
`d`, for a dialect with a pure denotation.

`NFProg.leakRun M fuel p V` runs `p` from `V` and returns its results with the list of its
events:

* a binding emits the events of its operation (`Expr.ctLeak`);
* a counted loop emits `trip n` for its trip count `n`, then the events of its iterations in
  order, then the events of its continuation;
* a branch emits `branch b` for the bit `b` it reads, then the events of the arm it runs;
* a loop in exit-flag form emits the events of each run of its body followed by
  `branch b` for the flag `b` it tests.

`NFCT M L fuel p` is constant time for the entry labels `L`: valuations that agree on the
positions `L` marks public give the same events (and both runs succeed or both fail).

`NFProg.levelCheck M p L` is a level checker for the fragment of bindings and counted
loops. It returns the levels of the results. A counted loop requires a public trip count;
its carried values take the levels of their initial values when the body keeps them,
and the secret level otherwise. The checker refuses branches and exit-flag loops.

## Main definitions

* `forIterLeak`, `whileIterLeak`, `NFProg.leakRun`, `NFCT`
* `retLvls`, `lvlLe`, `lvlsLe`, `allSecret`, `NFProg.levelCheck`

## Main results

* `NFProg.leakRun_fst` — the results of `leakRun` are the denotation of the program.
* `NFProg.levelCheck_sound` — on valuations that agree on the public positions, a program
  the checker accepts runs to equal events and to results that agree on the levels the
  checker returns.
* `NFProg.nfCT_of_levelCheck` — a program the checker accepts is `NFCT`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-! ## The leakage -/

/-- The run of the iterations `is` of a counted loop from the carried tuple `acc`, with the
    events of each iteration in order: `none` when an iteration fails. -/
def forIterLeak {cs : List d.Ty}
    (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak)) :
    List Nat → Valuation cs → Option (Valuation cs × List CTLeak)
  | [], acc => some (acc, [])
  | i :: is, acc => (step i acc).bind fun r =>
      (forIterLeak step is r.1).map fun q => (q.1, r.2 ++ q.2)

/-- The fuel-bounded run of a loop in exit-flag form from the carried tuple `acc`: each run
    of the body `step` emits its events and the event `branch b` of the flag `b` it
    returns; a `false` flag returns the tuple, fuel `0` fails. -/
def whileIterLeak {cs : List d.Ty}
    (step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak)) :
    Nat → Valuation cs → Option (Valuation cs × List CTLeak)
  | 0, _ => none
  | n + 1, acc => (step acc).bind fun r =>
      if HasBoolBit.toBool (d := d) r.1.head then
        (whileIterLeak step n r.1.tail).map fun q => (q.1, r.2 ++ .branch true :: q.2)
      else some (r.1.tail, r.2 ++ [.branch false])

variable [DialectDenote d]

/-- The run of a program from a valuation with the list of its events, in execution order.
    `fuel` bounds the runs of each exit-flag loop body. -/
def NFProg.leakRun (M : LeakModel d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Valuation Γ →
    Option (Valuation ts × List CTLeak)
  | _, _, .ret vs, V => some (Expr.lookupArgs vs V, [])
  | _, _, .var e k, V =>
      (NFProg.leakRun M fuel k (V.extend (e.denote V))).map fun r =>
        (r.1, Expr.ctLeak M e V ++ r.2)
  | _, _, .forLoop count inits body k, V =>
      (forIterLeak
          (fun i acc => NFProg.leakRun M fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRun M fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .trip (HasWord64.toNat (d := d) (count.lookup V)) :: (r.2 ++ q.2))
  | _, _, .ifThenElse cond thn els k, V =>
      (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRun M fuel thn V
        else NFProg.leakRun M fuel els V).bind fun r =>
        (NFProg.leakRun M fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (r.2 ++ q.2))
  | _, _, .whileLoop inits body k, V =>
      (whileIterLeak (fun acc => NFProg.leakRun M fuel body (hvAppend acc V)) fuel
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRun M fuel k (hvAppend r.1 V)).map fun q => (q.1, r.2 ++ q.2)

/-- Constant time of a program for the entry labels `L`: valuations that agree on the
    positions `L` marks public give the same events. -/
def NFCT (M : LeakModel d) {Γ : Ctxt d} {ts : List d.Ty} (L : Labels Γ) (fuel : Nat)
    (p : NFProg d Γ ts) : Prop :=
  ∀ V₁ V₂ : Valuation Γ, PubEqV L V₁ V₂ →
    (NFProg.leakRun M fuel p V₁).map Prod.snd = (NFProg.leakRun M fuel p V₂).map Prod.snd

/-! ## The results of the leakage run -/

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- The results of `forIterLeak` are the monadic fold of the results of its steps. -/
theorem forIterLeak_fst {cs : List d.Ty}
    (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (f : Valuation cs → Nat → Option (Valuation cs))
    (hf : ∀ i acc, (step i acc).map Prod.fst = f acc i) :
    ∀ (is : List Nat) (acc : Valuation cs),
      (forIterLeak step is acc).map Prod.fst = is.foldlM f acc
  | [], _ => rfl
  | i :: is, acc => by
      rw [List.foldlM_cons, ← hf i acc]
      simp only [forIterLeak]
      rcases step i acc with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact forIterLeak_fst step f hf is a

omit [DialectSignature d] [HasWord64 d] [DialectDenote d] in
/-- The results of `whileIterLeak` are the iteration `whileIter` of the results of its
    body. -/
theorem whileIterLeak_fst {cs : List d.Ty}
    (step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (f : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs)))
    (hf : ∀ acc, (step acc).map Prod.fst = f acc) :
    ∀ (n : Nat) (acc : Valuation cs),
      (whileIterLeak step n acc).map Prod.fst = NFProg.whileIter f n acc
  | 0, _ => rfl
  | n + 1, acc => by
      simp only [whileIterLeak, NFProg.whileIter, ← hf acc]
      rcases step acc with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.bind_eq_bind]
        split
        · rw [Option.map_map]
          exact whileIterLeak_fst step f hf n a.tail
        · rfl

/-- **The results of the leakage run** are the denotation of the program. -/
theorem NFProg.leakRun_fst (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V : Valuation Γ) :
    (NFProg.leakRun M fuel p V).map Prod.fst = p.denote fuel V := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.leakRun, NFProg.denote, Expr.denoteM_option_eq_some,
        Option.bind_eq_bind, Option.bind_some, Option.map_map]
      exact ih _
  | forLoop count inits body k ihb ihk =>
      rw [NFProg.denote_forLoop, ← forIterLeak_fst _ _ (fun i acc => ihb _)]
      simp only [NFProg.leakRun, Option.bind_eq_bind]
      rcases forIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | ifThenElse cond thn els k iht ihe ihk =>
      rw [NFProg.denote_ifThenElse]
      have hc : (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
          else els.denote fuel V) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRun M fuel thn V
            else NFProg.leakRun M fuel els V).map Prod.fst := by
        split <;> simp only [iht, ihe]
      rw [hc]
      simp only [NFProg.leakRun, Option.bind_eq_bind]
      rcases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRun M fuel thn V
        else NFProg.leakRun M fuel els V) with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | whileLoop inits body k ihb ihk =>
      rw [NFProg.denote_whileLoop, ← whileIterLeak_fst _ _ (fun acc => ihb _)]
      simp only [NFProg.leakRun, Option.bind_eq_bind]
      rcases whileIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _

/-! ## The level checker -/

/-- The levels of the returned variables `vs`. -/
def retLvls {Γ : Ctxt d} (L : Labels Γ) :
    {ts : List d.Ty} → HVector (fun t => Var Γ t) ts → Labels ts
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (lvlOf v L) (retLvls L rest)

/-- The order of levels: public below secret. -/
def lvlLe (a b : SecretLevel) : Bool :=
  decide (a = .Public) || decide (b = .Secret)

/-- The pointwise order of the levels of a tuple. -/
def lvlsLe : {cs : List d.Ty} → Labels cs → Labels cs → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons a A, .cons b B => lvlLe a b && lvlsLe A B

/-- The secret level at every position of a tuple. -/
def allSecret : (cs : List d.Ty) → Labels cs
  | [] => .nil
  | _ :: cs => .cons .Secret (allSecret cs)

/-- **The level checker of the fragment of bindings and counted loops.** It returns the
    levels of the results, or `none` when it refuses the program. A binding takes the join
    of the levels of its arguments and requires its operation's constraint (`opAccepts`). A
    counted loop requires a public trip count; its carried values take the levels of their
    initial values when the body, checked with a public trip index, returns values at most
    as secret, and the secret level otherwise. A branch or an exit-flag loop is refused. -/
def NFProg.levelCheck (M : LeakModel d) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Labels Γ → Option (Labels ts)
  | _, _, .ret vs, L => some (retLvls L vs)
  | _, _, .var e k, L =>
      if opAccepts M e.op (argLvls L e.args) then
        NFProg.levelCheck M k (.cons (joinAll (argLvls L e.args)) L)
      else none
  | _, _, .forLoop (cs := cs') count inits body k, L =>
      if lvlOf count L = .Public then
        if (NFProg.levelCheck M body (hvAppend (retLvls L inits) (.cons .Public L))).any
            (fun B => lvlsLe B (retLvls L inits)) then
          NFProg.levelCheck M k (hvAppend (retLvls L inits) L)
        else if (NFProg.levelCheck M body (hvAppend (allSecret cs') (.cons .Public L))).isSome
        then NFProg.levelCheck M k (hvAppend (allSecret cs') L)
        else none
      else none
  | _, _, .ifThenElse .., _ => none
  | _, _, .whileLoop .., _ => none

/-! ## Soundness of the level checker -/

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- Valuations of a tuple and of a context that agree on their public positions agree, after
    appending, on the public positions of the appended labels. -/
theorem pubEqV_hvAppend {Γ : Ctxt d} {L : Labels Γ} {W₁ W₂ : Valuation Γ}
    (hL : PubEqV L W₁ W₂) :
    {cs : List d.Ty} → (A : Labels cs) → (X₁ X₂ : Valuation cs) → PubEqV A X₁ X₂ →
    PubEqV (hvAppend A L) (hvAppend X₁ W₁) (hvAppend X₂ W₂)
  | [], .nil, .nil, .nil, _ => hL
  | _ :: _, .cons a A, .cons x₁ X₁, .cons x₂ X₂, hA => by
      intro t v hv
      cases v with
      | here => exact hA _ .here hv
      | there v =>
          exact pubEqV_hvAppend hL A X₁ X₂ (fun t' w hw => hA t' (.there w) hw) t v hv

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- Extending valuations that agree on the public positions by values that are equal when
    their level is public keeps the agreement. -/
theorem pubEqV_cons {Γ : Ctxt d} {L : Labels Γ} {W₁ W₂ : Valuation Γ} {t : d.Ty}
    (hL : PubEqV L W₁ W₂) (l : SecretLevel) (x₁ x₂ : ⟦t⟧) (hx : l = .Public → x₁ = x₂) :
    PubEqV (Γ := t :: Γ) (.cons l L) (.cons x₁ W₁) (.cons x₂ W₂) := by
  intro t' v hv
  cases v with
  | here => exact hx hv
  | there v => exact hL _ v hv

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- Agreement on the public positions of lower levels gives agreement on the public
    positions of higher levels. -/
theorem pubEqV_mono : {cs : List d.Ty} → (B A : Labels cs) → lvlsLe B A = true →
    (X₁ X₂ : Valuation cs) → PubEqV B X₁ X₂ → PubEqV A X₁ X₂
  | [], .nil, .nil, _, _, _, _ => fun _ v => nomatch v
  | _ :: _, .cons b B, .cons a A, hle, .cons x₁ X₁, .cons x₂ X₂, hB => by
      simp only [lvlsLe, Bool.and_eq_true] at hle
      intro t v hv
      cases v with
      | here =>
          apply hB _ .here
          simp only [lvlOf] at hv ⊢
          simp only [lvlLe, Bool.or_eq_true, decide_eq_true_eq, hv] at hle
          rcases hle.1 with h | h
          · exact h
          · cases h
      | there v =>
          exact pubEqV_mono B A hle.2 X₁ X₂ (fun t' w hw => hB t' (.there w) hw) t v hv

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- Every tuple of levels is below the secret levels. -/
theorem lvlsLe_allSecret : {cs : List d.Ty} → (B : Labels cs) → lvlsLe B (allSecret cs) = true
  | [], .nil => rfl
  | _ :: _, .cons b B => by
      simp only [lvlsLe, allSecret, lvlLe, Bool.and_eq_true, Bool.or_eq_true, decide_true,
        or_true, true_and]
      exact lvlsLe_allSecret B

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- Valuations of a tuple agree on every public position of the secret labels. -/
theorem pubEqV_allSecret : {cs : List d.Ty} → (X₁ X₂ : Valuation cs) →
    PubEqV (allSecret cs) X₁ X₂
  | [], .nil, .nil => fun _ v => nomatch v
  | _ :: _, .cons _ X₁, .cons _ X₂ => by
      intro t v hv
      cases v with
      | here => cases hv
      | there v => exact pubEqV_allSecret X₁ X₂ t v hv

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- Returned variables agree on the public positions of their levels. -/
theorem pubEqV_retLvls {Γ : Ctxt d} {L : Labels Γ} {V₁ V₂ : Valuation Γ}
    (h : PubEqV L V₁ V₂) : {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    PubEqV (retLvls L vs) (Expr.lookupArgs vs V₁) (Expr.lookupArgs vs V₂)
  | [], .nil => fun _ v => nomatch v
  | _ :: _, .cons w rest => by
      intro t v hv
      cases v with
      | here => exact h _ w hv
      | there v => exact pubEqV_retLvls h rest t v hv

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- The iterations of two counted-loop runs whose steps preserve the agreement on the public
    positions of `A` and emit equal events both succeed, with equal events and results that
    agree on the public positions of `A`. -/
theorem forIterLeak_rel {cs : List d.Ty} (A : Labels cs)
    (step₁ step₂ : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (hs : ∀ i (X₁ X₂ : Valuation cs), PubEqV A X₁ X₂ → ∃ r₁ r₂, step₁ i X₁ = some r₁ ∧
      step₂ i X₂ = some r₂ ∧ r₁.2 = r₂.2 ∧ PubEqV A r₁.1 r₂.1) :
    ∀ (is : List Nat) (X₁ X₂ : Valuation cs), PubEqV A X₁ X₂ →
      ∃ r₁ r₂, forIterLeak step₁ is X₁ = some r₁ ∧ forIterLeak step₂ is X₂ = some r₂ ∧
        r₁.2 = r₂.2 ∧ PubEqV A r₁.1 r₂.1
  | [], X₁, X₂, h => ⟨(X₁, []), (X₂, []), rfl, rfl, rfl, h⟩
  | i :: is, X₁, X₂, h => by
      obtain ⟨r₁, r₂, h₁, h₂, he, hr⟩ := hs i X₁ X₂ h
      obtain ⟨q₁, q₂, k₁, k₂, ke, kr⟩ := forIterLeak_rel A step₁ step₂ hs is r₁.1 r₂.1 hr
      refine ⟨(q₁.1, r₁.2 ++ q₁.2), (q₂.1, r₂.2 ++ q₂.2), ?_, ?_, ?_, kr⟩
      · simp only [forIterLeak, h₁, Option.bind_some, k₁, Option.map_some]
      · simp only [forIterLeak, h₂, Option.bind_some, k₂, Option.map_some]
      · simp only [he, ke]

/-- **Soundness of the level checker.** On valuations that agree on the positions `L` marks
    public, a program the checker accepts with result levels `R` runs to `some` results in
    both runs, with equal events, and the results agree on the positions `R` marks
    public. -/
theorem NFProg.levelCheck_sound (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ (L : Labels Γ) (R : Labels ts), NFProg.levelCheck M p L = some R →
      ∀ V₁ V₂ : Valuation Γ, PubEqV L V₁ V₂ →
      ∃ r₁ r₂, NFProg.leakRun M fuel p V₁ = some r₁ ∧ NFProg.leakRun M fuel p V₂ = some r₂ ∧
        r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1 := by
  induction p with
  | ret vs =>
      intro L R h V₁ V₂ hp
      simp only [NFProg.levelCheck, Option.some.injEq] at h
      subst h
      exact ⟨_, _, rfl, rfl, rfl, pubEqV_retLvls hp vs⟩
  | var e k ih =>
      intro L R h V₁ V₂ hp
      simp only [NFProg.levelCheck] at h
      split at h
      · rename_i hacc
        have hp' : PubEqV (.cons (joinAll (argLvls L e.args)) L) (V₁.extend (e.denote V₁))
            (V₂.extend (e.denote V₂)) :=
          pubEqV_cons hp _ _ _ fun hj => by
            unfold Expr.denote
            rw [lookupArgs_eq_of_pub hp e.args hj]
        obtain ⟨r₁, r₂, h₁, h₂, he, hr⟩ := ih _ R h _ _ hp'
        refine ⟨(r₁.1, Expr.ctLeak M e V₁ ++ r₁.2), (r₂.1, Expr.ctLeak M e V₂ ++ r₂.2),
          ?_, ?_, ?_, hr⟩
        · simp only [NFProg.leakRun, h₁, Option.map_some]
        · simp only [NFProg.leakRun, h₂, Option.map_some]
        · simp only [Expr.ctLeak, opLeak_eq_of_accepts M hp e.op e.args hacc, he]
      · cases h
  | forLoop count inits body k ihb ihk =>
      intro L R h V₁ V₂ hp
      simp only [NFProg.levelCheck] at h
      split at h
      · rename_i hcount
        have htrip : count.lookup V₁ = count.lookup V₂ := hp _ count hcount
        have hloop : ∀ A : Labels _, (∀ X₁ X₂ : Valuation _, PubEqV A X₁ X₂ →
            PubEqV (hvAppend A L) (hvAppend X₁ V₁) (hvAppend X₂ V₂)) →
            (NFProg.levelCheck M body (hvAppend A (.cons .Public L))).any
              (fun B => lvlsLe B A) = true →
            NFProg.levelCheck M k (hvAppend A L) = some R → PubEqV A
              (Expr.lookupArgs inits V₁) (Expr.lookupArgs inits V₂) →
            ∃ r₁ r₂, NFProg.leakRun M fuel (.forLoop count inits body k) V₁ = some r₁ ∧
              NFProg.leakRun M fuel (.forLoop count inits body k) V₂ = some r₂ ∧
              r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1 := by
          intro A hApp hbody hk hinit
          obtain ⟨B, hB, hle⟩ : ∃ B, NFProg.levelCheck M body (hvAppend A (.cons .Public L)) =
              some B ∧ lvlsLe B A = true := by
            rcases hb : NFProg.levelCheck M body (hvAppend A (.cons .Public L)) with _ | B
            · rw [hb] at hbody; cases hbody
            · rw [hb] at hbody; exact ⟨B, rfl, hbody⟩
          have hstep : ∀ i (X₁ X₂ : Valuation _), PubEqV A X₁ X₂ → ∃ r₁ r₂,
              NFProg.leakRun M fuel body
                (hvAppend X₁ (.cons (HasWord64.ofNat (d := d) i) V₁)) = some r₁ ∧
              NFProg.leakRun M fuel body
                (hvAppend X₂ (.cons (HasWord64.ofNat (d := d) i) V₂)) = some r₂ ∧
              r₁.2 = r₂.2 ∧ PubEqV A r₁.1 r₂.1 := by
            intro i X₁ X₂ hX
            obtain ⟨r₁, r₂, h₁, h₂, he, hr⟩ := ihb _ B hB _ _
              (pubEqV_hvAppend (pubEqV_cons hp .Public _ _ fun _ => rfl) A X₁ X₂ hX)
            exact ⟨r₁, r₂, h₁, h₂, he, pubEqV_mono B A hle _ _ hr⟩
          obtain ⟨q₁, q₂, k₁, k₂, ke, kr⟩ := forIterLeak_rel A _ _ hstep
            (List.range (HasWord64.toNat (d := d) (count.lookup V₁))) _ _ hinit
          rw [htrip] at k₂
          obtain ⟨s₁, s₂, l₁, l₂, le, lr⟩ := ihk _ R hk _ _ (hApp _ _ kr)
          refine ⟨(s₁.1, .trip (HasWord64.toNat (d := d) (count.lookup V₁)) :: (q₁.2 ++ s₁.2)),
            (s₂.1, .trip (HasWord64.toNat (d := d) (count.lookup V₂)) :: (q₂.2 ++ s₂.2)),
            ?_, ?_, ?_, lr⟩
          · simp only [NFProg.leakRun, k₁, Option.bind_some, l₁, Option.map_some]
          · simp only [NFProg.leakRun, k₂, Option.bind_some, l₂, Option.map_some]
          · simp only [htrip, ke, le]
        split at h
        · rename_i hbody
          exact hloop _ (fun X₁ X₂ hX => pubEqV_hvAppend hp _ X₁ X₂ hX) hbody h
            (pubEqV_retLvls hp inits)
        · split at h
          · rename_i hsome
            refine hloop _ (fun X₁ X₂ hX => pubEqV_hvAppend hp _ X₁ X₂ hX) ?_ h
              (pubEqV_allSecret _ _)
            rcases hb : NFProg.levelCheck M body (hvAppend (allSecret _) (.cons .Public L))
              with _ | B
            · rw [hb] at hsome; cases hsome
            · exact lvlsLe_allSecret B
          · cases h
      · cases h
  | ifThenElse => intro L R h; simp [NFProg.levelCheck] at h
  | whileLoop => intro L R h; simp [NFProg.levelCheck] at h

/-- A program the level checker accepts for the entry labels `L` is constant time for `L`,
    at every fuel. -/
theorem NFProg.nfCT_of_levelCheck (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (L : Labels Γ) (h : (NFProg.levelCheck M p L).isSome) :
    NFCT M L fuel p := by
  intro V₁ V₂ hp
  rcases hR : NFProg.levelCheck M p L with _ | R
  · rw [hR] at h; cases h
  · obtain ⟨r₁, r₂, h₁, h₂, he, -⟩ := NFProg.levelCheck_sound M fuel p L R hR V₁ V₂ hp
    rw [h₁, h₂, Option.map_some, Option.map_some, he]

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
