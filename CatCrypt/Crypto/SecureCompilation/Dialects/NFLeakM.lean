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
coincide (`leakRunM_eq_leakRun`).

`NFCTRel M L fuel p` is constant time relative to the runs that succeed: two valuations that
agree on the positions `L` marks public, from which the program runs to results, give equal
events.

`NFProg.levelCheck'` extends the level checker `NFLeak.NFProg.levelCheck` to branches and
exit-flag loops. A branch requires a public condition, and its results take the join of the
levels of the two arms. An exit-flag loop requires its flag to be public; its carried values
take the levels of their initial values when the body keeps them, and the secret level
otherwise.

## Main definitions

* `NFProg.leakRunM`, `NFCTRel`
* `lvlJoin`, `NFProg.levelCheck'`

## Main results

* `NFProg.leakRunM_fst` — the results of `leakRunM` are the denotation of the program.
* `NFProg.leakRunM_eq_leakRun` — under a pure denotation the two leakage runs coincide.
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

/-- Constant time of a program for the entry labels `L`, relative to the runs that succeed:
    two valuations that agree on the positions `L` marks public, from which the program runs
    to results, give equal events. -/
def NFCTRel (M : LeakModel d) {Γ : Ctxt d} {ts : List d.Ty} (L : Labels Γ) (fuel : Nat)
    (p : NFProg d Γ ts) : Prop :=
  ∀ (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation ts × List CTLeak), PubEqV L V₁ V₂ →
    NFProg.leakRunM M fuel p V₁ = some r₁ → NFProg.leakRunM M fuel p V₂ = some r₂ → r₁.2 = r₂.2

/-- **The results of the leakage run** are the denotation of the program. -/
theorem NFProg.leakRunM_fst (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V : Valuation Γ) :
    (NFProg.leakRunM M fuel p V).map Prod.fst = p.denote fuel V := by
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

end Partial

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

/-! ## The level checker with branches and exit-flag loops -/

/-- The pointwise join of the levels of a tuple. -/
def lvlJoin : {cs : List d.Ty} → Labels cs → Labels cs → Labels cs
  | [], .nil, .nil => .nil
  | _ :: _, .cons a A, .cons b B => .cons (a.join b) (lvlJoin A B)

/-- The levels of the result of an exit-flag loop body keep the carried levels `A`: a public
    flag, and carried levels at most `A`. -/
def flagOk {cs : List d.Ty} (FB : Labels (HasBitType.bit (d := d) :: cs)) (A : Labels cs) :
    Bool :=
  decide (FB.head = .Public) && lvlsLe FB.tail A

/-- **The level checker with branches and exit-flag loops.** It extends
    `NFProg.levelCheck`: a branch requires a public condition, and its results take the join
    of the levels of its arms; an exit-flag loop requires a public flag, and its carried
    values take the levels of their initial values when the body keeps them (`flagOk`), and
    the secret level otherwise. -/
def NFProg.levelCheck' (M : LeakModel d) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Labels Γ → Option (Labels ts)
  | _, _, .ret vs, L => some (retLvls L vs)
  | _, _, .var e k, L =>
      if opAccepts M e.op (argLvls L e.args) then
        NFProg.levelCheck' M k (.cons (joinAll (argLvls L e.args)) L)
      else none
  | _, _, .forLoop (cs := cs') count inits body k, L =>
      if lvlOf count L = .Public then
        if (NFProg.levelCheck' M body (hvAppend (retLvls L inits) (.cons .Public L))).any
            (fun B => lvlsLe B (retLvls L inits)) then
          NFProg.levelCheck' M k (hvAppend (retLvls L inits) L)
        else if (NFProg.levelCheck' M body (hvAppend (allSecret cs') (.cons .Public L))).isSome
        then NFProg.levelCheck' M k (hvAppend (allSecret cs') L)
        else none
      else none
  | _, _, .ifThenElse cond thn els k, L =>
      if lvlOf cond L = .Public then
        match NFProg.levelCheck' M thn L, NFProg.levelCheck' M els L with
        | some R₁, some R₂ => NFProg.levelCheck' M k (hvAppend (lvlJoin R₁ R₂) L)
        | _, _ => none
      else none
  | _, _, .whileLoop (cs := cs') inits body k, L =>
      if (NFProg.levelCheck' M body (hvAppend (retLvls L inits) L)).any
          (fun FB => flagOk FB (retLvls L inits)) then
        NFProg.levelCheck' M k (hvAppend (retLvls L inits) L)
      else if (NFProg.levelCheck' M body (hvAppend (allSecret cs') L)).any
          (fun FB => flagOk FB (allSecret cs')) then
        NFProg.levelCheck' M k (hvAppend (allSecret cs') L)
      else none

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] in
/-- A tuple of levels is below its join with another. -/
theorem lvlsLe_join_left : {cs : List d.Ty} → (A B : Labels cs) → lvlsLe A (lvlJoin A B) = true
  | [], .nil, .nil => rfl
  | _ :: _, .cons a A, .cons b B => by
      simp only [lvlsLe, lvlJoin, Bool.and_eq_true]
      refine ⟨?_, lvlsLe_join_left A B⟩
      cases a <;> cases b <;> rfl

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] in
/-- A tuple of levels is below the join of another with it. -/
theorem lvlsLe_join_right : {cs : List d.Ty} → (A B : Labels cs) →
    lvlsLe B (lvlJoin A B) = true
  | [], .nil, .nil => rfl
  | _ :: _, .cons a A, .cons b B => by
      simp only [lvlsLe, lvlJoin, Bool.and_eq_true]
      refine ⟨?_, lvlsLe_join_right A B⟩
      cases a <;> cases b <;> rfl

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
      q₁.2 = q₂.2 ∧ PubEqV A q₁.1 q₂.1
  | [], X₁, X₂, q₁, q₂, h, h₁, h₂ => by
      simp only [forIterLeak, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨rfl, h⟩
  | i :: is, X₁, X₂, q₁, q₂, h, h₁, h₂ => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨r₁, hr₁, q₁', hq₁, rfl⟩ := h₁
      obtain ⟨r₂, hr₂, q₂', hq₂, rfl⟩ := h₂
      obtain ⟨he, hp⟩ := hs i X₁ X₂ r₁ r₂ h hr₁ hr₂
      obtain ⟨he', hp'⟩ := forIterLeak_relM A step₁ step₂ hs is _ _ q₁' q₂' hp hq₁ hq₂
      exact ⟨by simp only [he, he'], hp'⟩

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
      q₁.2 = q₂.2 ∧ PubEqV A q₁.1 q₂.1
  | 0, _, _, _, _, _, h₁, _ => by simp [whileIterLeak] at h₁
  | n + 1, X₁, X₂, q₁, q₂, h, h₁, h₂ => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨r₁, hr₁, h₁⟩ := h₁
      obtain ⟨r₂, hr₂, h₂⟩ := h₂
      obtain ⟨he, hf, hp⟩ := hs X₁ X₂ r₁ r₂ h hr₁ hr₂
      rw [← hf] at h₂
      split at h₁
      · rw [if_pos (by assumption)] at h₂
        obtain ⟨q₁', hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨q₂', hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨he', hp'⟩ := whileIterLeak_relM A step₁ step₂ hs n _ _ q₁' q₂' hp hq₁ hq₂
        exact ⟨by simp only [he, he'], hp'⟩
      · rw [if_neg (by assumption)] at h₂
        simp only [Option.some.injEq] at h₁ h₂
        subst h₁ h₂
        exact ⟨by simp only [he], hp⟩

section Partial

variable [DialectDenoteM d Option]

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
  induction p with
  | ret vs =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheck', Option.some.injEq] at h
      simp only [NFProg.leakRunM, Option.some.injEq] at h₁ h₂
      subst h h₁ h₂
      exact ⟨rfl, pubEqV_retLvls hp vs⟩
  | var e k ih =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheck'] at h
      split at h
      · rename_i hacc
        simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
        obtain ⟨x₁, hx₁, s₁, hs₁, rfl⟩ := h₁
        obtain ⟨x₂, hx₂, s₂, hs₂, rfl⟩ := h₂
        have hp' : PubEqV (.cons (joinAll (argLvls L e.args)) L) (V₁.extend x₁)
            (V₂.extend x₂) :=
          pubEqV_cons hp _ _ _ fun hj => by
            have hden : e.denoteM (M := Option) V₁ = e.denoteM (M := Option) V₂ := by
              unfold Expr.denoteM
              rw [lookupArgs_eq_of_pub hp e.args hj]
            rw [hx₁, hx₂, Option.some.injEq] at hden
            exact hden
        obtain ⟨he, hr⟩ := ih _ R h _ _ s₁ s₂ hp' hs₁ hs₂
        refine ⟨?_, hr⟩
        simp only [Expr.ctLeak, opLeak_eq_of_accepts M hp e.op e.args hacc, he]
      · cases h
  | forLoop count inits body k ihb ihk =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheck'] at h
      split at h
      · rename_i hcount
        have htrip : count.lookup V₁ = count.lookup V₂ := hp _ count hcount
        have hloop : ∀ A : Labels _,
            (NFProg.levelCheck' M body (hvAppend A (.cons .Public L))).any
              (fun B => lvlsLe B A) = true →
            NFProg.levelCheck' M k (hvAppend A L) = some R → PubEqV A
              (Expr.lookupArgs inits V₁) (Expr.lookupArgs inits V₂) →
            r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1 := by
          intro A hbody hk hinit
          obtain ⟨B, hB, hle⟩ : ∃ B, NFProg.levelCheck' M body (hvAppend A (.cons .Public L)) =
              some B ∧ lvlsLe B A = true := by
            rcases hb : NFProg.levelCheck' M body (hvAppend A (.cons .Public L)) with _ | B
            · rw [hb] at hbody; cases hbody
            · rw [hb] at hbody; exact ⟨B, rfl, hbody⟩
          simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
          obtain ⟨q₁, k₁, s₁, l₁, rfl⟩ := h₁
          obtain ⟨q₂, k₂, s₂, l₂, rfl⟩ := h₂
          rw [← htrip] at k₂
          obtain ⟨ke, kr⟩ := forIterLeak_relM A _ _
            (fun i X₁ X₂ a₁ a₂ hX ha₁ ha₂ => by
              obtain ⟨he, hr⟩ := ihb _ B hB _ _ a₁ a₂
                (pubEqV_hvAppend (pubEqV_cons hp .Public _ _ fun _ => rfl) A X₁ X₂ hX) ha₁ ha₂
              exact ⟨he, pubEqV_mono B A hle _ _ hr⟩)
            _ _ _ q₁ q₂ hinit k₁ k₂
          obtain ⟨le, lr⟩ := ihk _ R hk _ _ s₁ s₂ (pubEqV_hvAppend hp A _ _ kr) l₁ l₂
          exact ⟨by simp only [htrip, ke, le], lr⟩
        split at h
        · exact hloop _ (by assumption) h (pubEqV_retLvls hp inits)
        · split at h
          · rename_i hsome
            refine hloop _ ?_ h (pubEqV_allSecret _ _)
            rcases hb : NFProg.levelCheck' M body (hvAppend (allSecret _) (.cons .Public L))
              with _ | B
            · rw [hb] at hsome; cases hsome
            · exact lvlsLe_allSecret B
          · cases h
      · cases h
  | ifThenElse cond thn els k iht ihe ihk =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheck'] at h
      split at h
      · rename_i hcond
        have hc : cond.lookup V₁ = cond.lookup V₂ := hp _ cond hcond
        split at h
        · rename_i R₁ R₂ hR₁ hR₂
          simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
          obtain ⟨a₁, ha₁, s₁, l₁, rfl⟩ := h₁
          obtain ⟨a₂, ha₂, s₂, l₂, rfl⟩ := h₂
          rw [← hc] at ha₂
          have harm : a₁.2 = a₂.2 ∧ PubEqV (lvlJoin R₁ R₂) a₁.1 a₂.1 := by
            split at ha₁
            · rw [if_pos (by assumption)] at ha₂
              obtain ⟨e, r⟩ := iht L R₁ hR₁ _ _ _ _ hp ha₁ ha₂
              exact ⟨e, pubEqV_mono _ _ (lvlsLe_join_left R₁ R₂) _ _ r⟩
            · rw [if_neg (by assumption)] at ha₂
              obtain ⟨e, r⟩ := ihe L R₂ hR₂ _ _ _ _ hp ha₁ ha₂
              exact ⟨e, pubEqV_mono _ _ (lvlsLe_join_right R₁ R₂) _ _ r⟩
          obtain ⟨le, lr⟩ := ihk _ R h _ _ s₁ s₂ (pubEqV_hvAppend hp _ _ _ harm.2) l₁ l₂
          exact ⟨by simp only [hc, harm.1, le], lr⟩
        · cases h
      · cases h
  | whileLoop inits body k ihb ihk =>
      intro L R h V₁ V₂ r₁ r₂ hp h₁ h₂
      simp only [NFProg.levelCheck'] at h
      have hloop : ∀ A : Labels _,
          (NFProg.levelCheck' M body (hvAppend A L)).any (fun FB => flagOk FB A) = true →
          NFProg.levelCheck' M k (hvAppend A L) = some R → PubEqV A
            (Expr.lookupArgs inits V₁) (Expr.lookupArgs inits V₂) →
          r₁.2 = r₂.2 ∧ PubEqV R r₁.1 r₂.1 := by
        intro A hbody hk hinit
        obtain ⟨FB, hB, hok⟩ : ∃ FB, NFProg.levelCheck' M body (hvAppend A L) = some FB ∧
            flagOk FB A = true := by
          rcases hb : NFProg.levelCheck' M body (hvAppend A L) with _ | FB
          · rw [hb] at hbody; cases hbody
          · rw [hb] at hbody; exact ⟨FB, rfl, hbody⟩
        simp only [flagOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        simp only [NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
        obtain ⟨q₁, k₁, s₁, l₁, rfl⟩ := h₁
        obtain ⟨q₂, k₂, s₂, l₂, rfl⟩ := h₂
        obtain ⟨ke, kr⟩ := whileIterLeak_relM A _ _
          (fun X₁ X₂ a₁ a₂ hX ha₁ ha₂ => by
            obtain ⟨he, hr⟩ := ihb _ FB hB _ _ a₁ a₂ (pubEqV_hvAppend hp A X₁ X₂ hX) ha₁ ha₂
            revert hr
            rcases FB with _ | ⟨f, B⟩
            rcases a₁ with ⟨_ | ⟨x₁, Y₁⟩, t₁⟩
            rcases a₂ with ⟨_ | ⟨x₂, Y₂⟩, t₂⟩
            intro hr
            refine ⟨he, hr _ .here hok.1, pubEqV_mono B A hok.2 _ _ ?_⟩
            exact fun t' v hv => hr t' (.there v) hv)
          _ _ _ q₁ q₂ hinit k₁ k₂
        obtain ⟨le, lr⟩ := ihk _ R hk _ _ s₁ s₂ (pubEqV_hvAppend hp A _ _ kr) l₁ l₂
        exact ⟨by simp only [ke, le], lr⟩
      split at h
      · exact hloop _ (by assumption) h (pubEqV_retLvls hp inits)
      · split at h
        · exact hloop _ (by assumption) h (pubEqV_allSecret _ _)
        · cases h

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
