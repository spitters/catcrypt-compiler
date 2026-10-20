/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakM

/-!
# A level checker with declassification for `NFProg`

`NFProg.levelCheckD M isDeclass` is the level checker `NFProg.levelCheck'` in which an
operation marked by `isDeclass` is a declassification: it accepts arguments at every level and
gives its result the public level. A declassification emits its argument as its event:
`DeclassOk M isDeclass isDeclEv` states that the events of a marked operation are one event
satisfying `isDeclEv`, and that this event determines the result of the operation.

The soundness statement is relative to the runs that succeed, as for `levelCheck'`: on
valuations that agree on the public positions, the events of two runs are equal, or they
first differ at a declassification event (`DeclDiff`). The declassified sequence of a trace is
its subsequence of declassification events; when both runs have the same declassified
sequence (`DeclIs`), their events are equal (`NFCTRelD`).

## Main definitions

* `DeclDiff` — two traces first differ at a declassification event.
* `DeclassOk` — the marked operations emit one declassification event that determines their
  result.
* `NFProg.levelCheckD`
* `DeclIs`, `NFCTRelD` — the declassified sequence of the successful runs, and constant time
  for runs with a given declassified sequence.

## Main results

* `NFProg.levelCheckD_sound` — events equal with results agreeing on the public positions,
  or a first difference at a declassification event.
* `NFProg.levelCheckD_trace` — the events of two runs are equal or first differ at a
  declassification event.
* `NFProg.nfCTRelD_of_levelCheckD` — a program the checker accepts is constant time for the
  runs with a given declassified sequence.
* `NFProg.levelCheckD_none` — without marked operations the checker is `levelCheck'`.
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

/-! ## First differences at a declassification event -/

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

theorem append_left (c : List CTLeak) (h : DeclDiff D t₁ t₂) :
    DeclDiff D (c ++ t₁) (c ++ t₂) := by
  obtain ⟨pre, s₁, s₂, a₁, a₂, hne, h₁, h₂, rfl, rfl⟩ := h
  exact ⟨c ++ pre, s₁, s₂, a₁, a₂, hne, h₁, h₂, by simp, by simp⟩

/-- The declassified sequences of two traces that first differ at a declassification event
    differ. -/
theorem filter_ne (h : DeclDiff D t₁ t₂) : t₁.filter D ≠ t₂.filter D := by
  obtain ⟨pre, s₁, s₂, a₁, a₂, hne, h₁, h₂, rfl, rfl⟩ := h
  intro heq
  simp only [List.filter_append, List.filter_cons, h₁, h₂, if_true, List.append_cancel_left_eq,
    List.cons.injEq] at heq
  exact hne heq.1

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
    · exact Or.inr (hd.append_left _)
  · exact Or.inr (hd.append_right _ _)

/-- A common first event keeps equal events or a first difference at a declassification
    event. -/
theorem declDiff_cons {D : CTLeak → Bool} {t₁ t₂ : List CTLeak} {Q : Prop}
    (c : CTLeak) (h : (t₁ = t₂ ∧ Q) ∨ DeclDiff D t₁ t₂) :
    (c :: t₁ = c :: t₂ ∧ Q) ∨ DeclDiff D (c :: t₁) (c :: t₂) := by
  rcases h with ⟨rfl, hQ⟩ | hd
  · exact Or.inl ⟨rfl, hQ⟩
  · exact Or.inr (hd.append_left [c])

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-! ## The level checker with declassification -/

/-- **The level checker with declassification.** It is `NFProg.levelCheck'`, except that an
    operation marked by `isDeclass` accepts arguments at every level and gives its result the
    public level. -/
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

/-- Without marked operations, the checker with declassification is `NFProg.levelCheck'`. -/
theorem NFProg.levelCheckD_none (M : LeakModel d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (L : Labels Γ) :
    NFProg.levelCheckD M (fun _ => false) p L = NFProg.levelCheck' M p L := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.levelCheckD, NFProg.levelCheck', Bool.false_eq_true, if_false, ih]
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.levelCheckD, NFProg.levelCheck', ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.levelCheckD, NFProg.levelCheck', iht, ihe, ihk]
      rcases NFProg.levelCheck' M thn L with _ | R₁ <;>
        rcases NFProg.levelCheck' M els L with _ | R₂ <;> rfl
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.levelCheckD, NFProg.levelCheck', ihb, ihk]
  | call => rfl

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

/-- Every successful leakage run of `p` from `V` has declassified sequence `ds`: its
    subsequence of events satisfying `isDeclEv`. -/
def DeclIs (M : LeakModel d) (isDeclEv : CTLeak → Bool) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) (ds : List CTLeak) : Prop :=
  ∀ r, NFProg.leakRunM M fuel p V = some r → r.2.filter isDeclEv = ds

/-- Constant time of a program for the entry labels `L` modulo the declassified sequence
    `ds`: two valuations that agree on the positions `L` marks public, whose successful runs
    have declassified sequence `ds`, from which the program runs to results, give equal
    events. -/
def NFCTRelD (M : LeakModel d) (isDeclEv : CTLeak → Bool) {Γ : Ctxt d} {ts : List d.Ty}
    (L : Labels Γ) (fuel : Nat) (p : NFProg d Γ ts) (ds : List CTLeak) : Prop :=
  ∀ (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation ts × List CTLeak), PubEqV L V₁ V₂ →
    DeclIs M isDeclEv fuel p V₁ ds → DeclIs M isDeclEv fuel p V₂ ds →
    NFProg.leakRunM M fuel p V₁ = some r₁ → NFProg.leakRunM M fuel p V₂ = some r₂ → r₁.2 = r₂.2

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

/-- On valuations that agree on the positions `L` marks public, the events of two successful
    runs of a program the checker accepts are equal or first differ at a declassification
    event. -/
theorem NFProg.levelCheckD_trace (M : LeakModel d) (isDeclass : d.Op → Bool)
    (isDeclEv : CTLeak → Bool) (hD : DeclassOk M isDeclass isDeclEv) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheckD M isDeclass p L).isSome) (V₁ V₂ : Valuation Γ)
    (r₁ r₂ : Valuation ts × List CTLeak) (hp : PubEqV L V₁ V₂)
    (h₁ : NFProg.leakRunM M fuel p V₁ = some r₁) (h₂ : NFProg.leakRunM M fuel p V₂ = some r₂) :
    r₁.2 = r₂.2 ∨ DeclDiff isDeclEv r₁.2 r₂.2 := by
  rcases hR : NFProg.levelCheckD M isDeclass p L with _ | R
  · rw [hR] at h; cases h
  · rcases NFProg.levelCheckD_sound M isDeclass isDeclEv hD fuel p L R hR V₁ V₂ r₁ r₂ hp h₁ h₂
      with ⟨he, -⟩ | hd
    · exact Or.inl he
    · exact Or.inr hd

/-- A program the checker `levelCheckD` accepts for the entry labels `L` is constant time for
    `L` modulo every declassified sequence, at every fuel. -/
theorem NFProg.nfCTRelD_of_levelCheckD (M : LeakModel d) (isDeclass : d.Op → Bool)
    (isDeclEv : CTLeak → Bool) (hD : DeclassOk M isDeclass isDeclEv) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheckD M isDeclass p L).isSome) (ds : List CTLeak) :
    NFCTRelD M isDeclEv L fuel p ds := by
  intro V₁ V₂ r₁ r₂ hp hd₁ hd₂ h₁ h₂
  rcases NFProg.levelCheckD_trace M isDeclass isDeclEv hD fuel p L h V₁ V₂ r₁ r₂ hp h₁ h₂
    with he | hd
  · exact he
  · exact absurd ((hd₁ r₁ h₁).trans (hd₂ r₂ h₂).symm) hd.filter_ne

end Partial

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
