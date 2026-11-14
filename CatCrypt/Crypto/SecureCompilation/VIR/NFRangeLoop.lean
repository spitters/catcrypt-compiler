/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFRangeSound

/-!
# Soundness of the interval checker at counted loops

`forSound`: the step of the counted loop of the interval checker `NFRange.run` is sound, so
`check_sound'` states the soundness of the checker under the soundness of the name
specification alone.

A counted loop with the counter `cnt` runs its body for the trip indices `0, …, n - 1`, where
`n` is the value of `cnt`; the denotation of a counted loop consumes no fuel. The checker reads
the loop in one of three ways, by the interval `ci` of `cnt`:

* `ci` at most `0`: the loop runs no iteration, and its results are its initial values;
* `ci` a point of at most `S.unroll`: iteration `i` runs from the results of iteration
  `i - 1` with the counter the point `i` (`foldlM_sim`);
* otherwise: the invariant `J` that `loopFix` accepts holds of the initial values and is kept
  by one iteration with the counter in `[0, ci.2 - 1]` (`loopFix_sound`), so it holds of the
  values after each iteration (`foldlM_inv`).

## Main results

* `AVal.ok_le`, `AVals.ok_le` — the inclusion of abstract values is sound.
* `loopFix_sound` — the invariant `loopFix` returns contains its start and is closed under
  the abstract iteration.
* `forSound` — the step of the counted loop is sound.
* `check_sound'` — the soundness of the checker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFRange

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## 1. Inclusion and widening -/

/-- An abstract value holds of every value its included values hold of. -/
theorem AVal.mem_le :
    (t : NfTy) → (a b : AVal t) → (x : t.denote) → AVal.le t a b = true → AVal.Mem t a x →
      AVal.Mem t b x
  | .bit, a, b, x, hle, h => by
    simp only [AVal.le, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none,
      beq_iff_eq] at hle
    simp only [AVal.Mem] at h ⊢
    grind
  | .word _, _, _, _, hle, h => Iv.Has.le h hle
  | .arr _ t, a, b, f, hle, h => fun j => AVal.mem_le t a b (f j) hle (h j)
  | .unit, _, _, _, _, _ | .pair _ _, _, _, _, _, _ | .uint _, _, _, _, _, _
  | .sint _, _, _, _, _, _ | .int, _, _, _, _, _ | .tnil, _, _, _, _, _
  | .tcons _ _, _, _, _, _, _ | .slice _, _, _, _, _, _ => trivial

/-- An abstract value holds, with its facts, of every value its included values hold of. -/
theorem AVal.ok_le {P : Fact → Prop} (t : NfTy) (a b : AVal t) (x : t.denote)
    (hle : AVal.le t a b = true) (h : AVal.Ok P t a x) : AVal.Ok P t b x := by
  refine ⟨AVal.mem_le t a b x hle h.1, ?_⟩
  cases t
  case bit =>
    have h2 := h.2
    simp only [AVal.le, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hle
    intro f hf
    cases x <;> simp_all
  all_goals trivial

/-- The pointwise inclusion of abstract values is sound. -/
theorem AVals.ok_le {P : Fact → Prop} :
    {ts : List NfTy} → (A B : AVals ts) → (W : HVector NfTy.denote ts) →
      AVals.le A B = true → AVals.Ok P A W → AVals.Ok P B W
  | [], .nil, .nil, .nil, _, _ => trivial
  | _ :: _, .cons a A, .cons b B, .cons x W, hle, h => by
    simp only [AVals.le, Bool.and_eq_true] at hle
    exact ⟨AVal.ok_le _ a b x hle.1 h.1, AVals.ok_le A B W hle.2 h.2⟩

/-- The widening of `a` holds of every value `a` holds of. -/
theorem AVal.ok_widen_left {P : Fact → Prop} (t : NfTy) (a b : AVal t) (x : t.denote)
    (h : AVal.Ok P t a x) : AVal.Ok P t (AVal.widen t a b) x := by
  unfold AVal.widen
  split
  · exact h
  · exact AVal.ok_top t x

/-- The pointwise widening of `A` holds of every valuation `A` holds of. -/
theorem AVals.ok_widen_left {P : Fact → Prop} :
    {ts : List NfTy} → (A B : AVals ts) → (W : HVector NfTy.denote ts) → AVals.Ok P A W →
      AVals.Ok P (AVals.widen A B) W
  | [], .nil, .nil, .nil, _ => trivial
  | _ :: _, .cons a A, .cons b B, .cons x W, h =>
    ⟨AVal.ok_widen_left _ a b x h.1, AVals.ok_widen_left A B W h.2⟩

/-! ## 2. The invariant search -/

/-- The invariant `loopFix` returns holds of every valuation its start holds of, and one
    abstract iteration from it stays in it. -/
theorem loopFix_sound {P : Fact → Prop} {cs : List NfTy}
    (step : AVals cs → Except String (AVals cs)) :
    (n : Nat) → (J0 J : AVals cs) → loopFix step n J0 = .ok J →
      (∀ W, AVals.Ok P J0 W → AVals.Ok P J W) ∧ ∃ r, step J = .ok r ∧ AVals.le r J = true
  | 0, J0, J, h => by
    rw [loopFix] at h
    obtain ⟨r, hr, h⟩ := except_bind_ok h
    split at h
    · cases h
      exact ⟨fun _ hW => hW, r, hr, by assumption⟩
    · cases h
  | n + 1, J0, J, h => by
    rw [loopFix] at h
    obtain ⟨r, hr, h⟩ := except_bind_ok h
    split at h
    · cases h
      exact ⟨fun _ hW => hW, r, hr, by assumption⟩
    · obtain ⟨hpres, hstep⟩ := loopFix_sound step n _ J h
      refine ⟨fun W hW => hpres W ?_, hstep⟩
      split
      · exact AVals.ok_widen_left _ _ W hW
      · exact AVals.ok_join_left _ _ W hW

/-! ## 3. Folds over the trip indices -/

/-- A fold of a step that keeps the predicate `Q` at each index of `l`, at every fuel and
    with one result, keeps `Q`. -/
theorem foldlM_inv {β : Type} (l : List Nat) (fc : Nat → β → Nat → Option β) (Q : β → Prop)
    (h : ∀ i ∈ l, ∀ b, Q b → ∃ b', (∀ fuel, fc fuel b i = some b') ∧ Q b') :
    ∀ b0, Q b0 → ∃ bN, (∀ fuel, l.foldlM (fc fuel) b0 = some bN) ∧ Q bN := by
  induction l with
  | nil => intro b0 hb; exact ⟨b0, fun _ => rfl, hb⟩
  | cons i l ih =>
    intro b0 hb
    obtain ⟨b1, hb1, hq⟩ := h i List.mem_cons_self b0 hb
    obtain ⟨bN, hN, hqN⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) b1 hq
    exact ⟨bN, fun fuel => by rw [List.foldlM_cons, hb1 fuel]; exact hN fuel, hqN⟩

/-- A fold of a concrete step simulated by a fold of an abstract step: the relation `R`
    between the abstract and the concrete states is kept at each index of `l`. -/
theorem foldlM_sim {α β : Type} (l : List Nat) (fa : α → Nat → Except String α)
    (fc : Nat → β → Nat → Option β) (R : α → β → Prop)
    (h : ∀ i ∈ l, ∀ a a' b, fa a i = .ok a' → R a b →
      ∃ b', (∀ fuel, fc fuel b i = some b') ∧ R a' b') :
    ∀ a0 aN b0, l.foldlM fa a0 = .ok aN → R a0 b0 →
      ∃ bN, (∀ fuel, l.foldlM (fc fuel) b0 = some bN) ∧ R aN bN := by
  induction l with
  | nil =>
    intro a0 aN b0 ha hb
    cases ha
    exact ⟨b0, fun _ => rfl, hb⟩
  | cons i l ih =>
    intro a0 aN b0 ha hb
    obtain ⟨a1, ha1, ha⟩ := except_bind_ok ha
    obtain ⟨b1, hb1, hr⟩ := h i List.mem_cons_self a0 a1 b0 ha1 hb
    obtain ⟨bN, hN, hrN⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) a1 aN b1 ha hr
    exact ⟨bN, fun fuel => by rw [List.foldlM_cons, hb1 fuel]; exact hN fuel, hrN⟩

/-! ## 4. One iteration -/

/-- One abstract iteration of a sound body, from abstract carried values that hold of the
    carried values with their facts on the enclosing valuation `V` and a counter interval that
    holds the counter, gives carried values that hold of the values after one iteration. -/
theorem body_step (S : NameSpec) (T : NfLeafTable) {Γ : Ctxt nfDialect} {cs : List NfTy}
    {body : NFProg nfDialect (cs ++ HasWord64.word (d := nfDialect) :: Γ) cs}
    (hb : Sound S T body) {A : AEnv Γ} {V : Valuation Γ} (hA : AVals.Ok (Fact.Holds V) A V)
    (ctr : Iv) (c : BitVec 64) (hc : ctr.Has c.toNat) (J r : AVals cs)
    (acc : Valuation (d := nfDialect) cs) (hJ : AVals.Ok (Fact.Holds V) J acc)
    (hr : (AVals.restrict Γ.length <$>
      run S (hvAppend (d := nfDialect) (f := AVal) J (HVector.cons (t := NfTy.word 64) ctr A))
        body) = .ok r) :
    ∃ acc', (∀ fuel, @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel _ _ body
      (hvAppend (d := nfDialect) acc (HVector.cons (t := NfTy.word 64) c V)) = some acc') ∧
      AVals.Ok (Fact.Holds V) r acc' := by
  obtain ⟨r0, hr0, rfl⟩ := except_map_ok hr
  have hV1 : ∀ f : Fact, f.Holds V →
      f.Holds (hvAppend (d := nfDialect) acc (HVector.cons (t := NfTy.word 64) c V)) :=
    fun f hf => (hf.append (HVector.cons (t := NfTy.word 64) c .nil)).append acc
  have hA' := (AVals.ok_append (P := Fact.Holds
      (hvAppend (d := nfDialect) acc (HVector.cons (t := NfTy.word 64) c V)))
    (HVector.cons (t := NfTy.word 64) ctr A) (HVector.cons c V) J acc).2
    ⟨hJ.mono hV1, ⟨⟨hc, trivial⟩, hA.mono hV1⟩⟩
  obtain ⟨W, hW, hB⟩ := hb _ _ _ hr0 hA'
  refine ⟨W, hW, AVals.ok_restrict _ r0 W (hB.mono fun f hf hl hr => ?_)⟩
  exact (Fact.Below.of_append (HVector.cons (t := NfTy.word 64) c .nil)
    (Fact.Below.of_append acc hf)) hl hr

/-! ## 5. The counted loop -/

/-- **The step of the counted loop is sound**: a counted loop is sound when its body and its
    continuation are. -/
theorem forSound (S : NameSpec) (T : NfLeafTable) : ForSound S T := by
  intro Γ cs ts cnt inits body k hb hk A B V h hA
  let _ : DialectDenoteM nfDialect Option := nfDenote T
  have hcnt : Iv.Has (A.get cnt) ((cnt.lookup V : BitVec 64).toNat : Int) :=
    (AEnv.ok_get hA cnt).1
  have hlt : (cnt.lookup V : BitVec 64).toNat < 2 ^ 64 := (cnt.lookup V : BitVec 64).isLt
  have hinit := AEnv.ok_getArgs hA inits
  have finish : ∀ (J : AVals cs) (accN : Valuation (d := nfDialect) cs),
      run S (hvAppend (d := nfDialect) (f := AVal) J A) k = .ok B →
      (∀ fuel, (List.range (HasWord64.toNat (d := nfDialect) (cnt.lookup V))).foldlM
        (fun acc i => body.denote fuel
          (hvAppend acc (.cons (HasWord64.ofNat (d := nfDialect) i) V)))
        (Expr.lookupArgs inits V) = some accN) →
      AVals.Ok (Fact.Holds V) J accN →
      ∃ W, (∀ fuel, NFProg.denote fuel (NFProg.forLoop cnt inits body k) V = some W) ∧
        AVals.Ok (Fact.Below V) B W := by
    intro J accN hrun hN hJN
    have hA' := (AVals.ok_append (P := Fact.Holds (hvAppend (d := nfDialect) accN V)) A V J
      accN).2 ⟨hJN.mono fun f hf => hf.append accN, hA.mono fun f hf => hf.append accN⟩
    obtain ⟨W, hW, hB⟩ := hk _ _ _ hrun hA'
    refine ⟨W, fun fuel => ?_, hB.mono fun f hf => hf.of_append accN⟩
    rw [NFProg.denote_forLoop, hN fuel]
    exact hW fuel
  unfold run at h
  dsimp only at h
  split at h
  · rename_i hle
    obtain ⟨J, hJ, h⟩ := except_bind_ok h
    cases hJ
    have h0 : (cnt.lookup V : BitVec 64).toNat = 0 := by
      have := hcnt.2
      omega
    refine finish _ _ h (fun fuel => ?_) hinit
    change (List.range (cnt.lookup V : BitVec 64).toNat).foldlM _ _ = _
    rw [h0]
    rfl
  · split at h
    · rename_i hne hpt
      obtain ⟨J, hJ, h⟩ := except_bind_ok h
      simp only [bind_pure_comp, List.map_eq_map, List.foldlM_map] at hJ
      have hn : (A.get cnt).2.toNat = HasWord64.toNat (d := nfDialect) (cnt.lookup V) := by
        change _ = (cnt.lookup V : BitVec 64).toNat
        have := hcnt.1
        have := hcnt.2
        omega
      rw [hn] at hJ
      have hstep : ∀ i ∈ List.range (HasWord64.toNat (d := nfDialect) (cnt.lookup V)),
          ∀ (a a' : AVals cs) b, (AVals.restrict Γ.length <$>
            run S (hvAppend (d := nfDialect) (f := AVal) a
              (HVector.cons (t := NfTy.word 64) (ivPoint (i : Int)) A)) body) = .ok a' →
          AVals.Ok (Fact.Holds V) a b → ∃ b', (∀ fuel,
            @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel _ _ body
              (hvAppend b (.cons (HasWord64.ofNat (d := nfDialect) i) V)) = some b') ∧
            AVals.Ok (Fact.Holds V) a' b' := by
        intro i hi a a' b ha hab
        have hi' : i < (cnt.lookup V : BitVec 64).toNat := List.mem_range.1 hi
        have hc : Iv.Has (ivPoint (i : Int)) ((BitVec.ofNat 64 i).toNat : Int) := by
          simp only [Iv.Has, ivPoint, BitVec.toNat_ofNat]
          omega
        exact body_step S T hb hA _ (BitVec.ofNat 64 i) hc a a' b hab ha
      obtain ⟨accN, hN, hJN⟩ :=
        foldlM_sim _ _ _ (fun a b => AVals.Ok (Fact.Holds V) a b) hstep _ _ _ hJ hinit
      exact finish J accN h hN hJN
    · rename_i hne hpt
      obtain ⟨J, hJ, h⟩ := except_bind_ok h
      obtain ⟨hpres, r, hr, hle⟩ := loopFix_sound (P := Fact.Holds V) _ 3 _ J hJ
      have hstep : ∀ i ∈ List.range (HasWord64.toNat (d := nfDialect) (cnt.lookup V)),
          ∀ b, AVals.Ok (Fact.Holds V) J b → ∃ b', (∀ fuel,
            @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel _ _ body
              (hvAppend b (.cons (HasWord64.ofNat (d := nfDialect) i) V)) = some b') ∧
            AVals.Ok (Fact.Holds V) J b' := by
        intro i hi b hbJ
        have hi' : i < (cnt.lookup V : BitVec 64).toNat := List.mem_range.1 hi
        have hc : Iv.Has (0, (A.get cnt).2 - 1) ((BitVec.ofNat 64 i).toNat : Int) := by
          simp only [Iv.Has, BitVec.toNat_ofNat]
          have := hcnt.2
          omega
        obtain ⟨b', hb', hrb⟩ := body_step S T hb hA (0, (A.get cnt).2 - 1)
          (BitVec.ofNat 64 i) hc J r b hbJ hr
        exact ⟨b', hb', AVals.ok_le r J b' hle hrb⟩
      obtain ⟨accN, hN, hJN⟩ := foldlM_inv _ _ _ hstep _ (hpres _ hinit)
      exact finish J accN h hN hJN

/-- **Soundness of the interval checker.** When the name specification `S` is sound for the
    leaf table `T`, a program the checker accepts from `A` with the results `B` denotes, from
    every valuation in `A`, at every fuel and with the leaves of `T`, results `W` in `B`. -/
theorem check_sound' {S : NameSpec} {T : NfLeafTable} (hS : S.SoundAt T)
    {Γ : Ctxt nfDialect} {ts : List NfTy} {A : AEnv Γ} {B : AVals ts}
    {p : NFProg nfDialect Γ ts} {V : Valuation Γ} (hc : check S A p = some B)
    (hV : A.Sat V) :
    ∃ W : Valuation (d := nfDialect) ts,
      (∀ fuel, @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V = some W) ∧
      AVals.Mem B W :=
  check_sound hS (forSound S T) hc hV

end CatCrypt.Crypto.SecureCompilation.VIR.NFRange
