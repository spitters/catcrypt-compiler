/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFRangeCheck

/-!
# Soundness of the interval checker of NF programs

`check_sound`: when the name specification `S` is sound for the leaf table `T` and the
checker `NFRange.check S A p` returns `B`, then from every valuation `V` in which the abstract
environment `A` holds, `p` denotes, under the leaf table `T` and at every fuel, results `W`
in the abstract values `B`. The statement takes the step of the counted loop as the hypothesis
`ForSound S T`: a counted loop is sound when its body and its continuation are.

The proof runs by induction over the program with the invariant `AVals.Ok`: each abstract
value holds of its value (`AVal.Mem`) and the facts of each bit for its value satisfy a
predicate on facts (`AVal.Facts`). Inside the program the predicate is `Fact.Holds` of the
current valuation; for results, `Fact.Below` of the valuation at the start, which reads only
the facts on the variables of that valuation. A fact on the levels of a valuation holds in
every extension of it (`Fact.holds_append_iff`), so the facts of an environment survive the
variables a program binds.

## Main definitions

* `AVal.Facts`, `AVal.Ok`, `AVals.Ok` — abstract values that hold of values, with their
  facts.
* `Fact.Below` — a fact that holds of a valuation when its levels are those of the
  valuation.
* `Sound` — the soundness of the checker at one program.
* `ForSound` — the soundness of the step of the counted loop.

## Main results

* `AEnv.sat_iff` — `AEnv.Sat` is `AVals.Ok` at `Fact.Holds`.
* `AEnv.ok_refineBit`, `AEnv.reach_of_lookup` — the refinement by a branch condition is
  sound, and the arm the condition selects is reachable.
* `evalOp_sound`, `evalExpr_sound` — the abstract operations are sound.
* `sound_ret`, `sound_var`, `sound_ite` — the steps at a return, a binding and a branch.
* `check_sound` — the soundness of the checker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFRange

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## 1. Abstract values with their facts -/

/-- The facts of an abstract value for a value satisfy `P`: those of a bit for its value; no
    other abstract value has facts. -/
@[reducible] def AVal.Facts (P : Fact → Prop) : (t : NfTy) → AVal t → t.denote → Prop
  | .bit, a, b => ∀ f ∈ (if b then a.tt else a.ff), P f
  | _, _, _ => True

/-- An abstract value holds of a value, and its facts for the value satisfy `P`. -/
@[reducible] def AVal.Ok (P : Fact → Prop) (t : NfTy) (a : AVal t) (x : t.denote) : Prop :=
  AVal.Mem t a x ∧ AVal.Facts P t a x

/-- Each abstract value holds of the value at its position, with its facts satisfying `P`. -/
@[reducible] def AVals.Ok (P : Fact → Prop) :
    {ts : List NfTy} → AVals ts → HVector NfTy.denote ts → Prop
  | [], .nil, .nil => True
  | t :: _, .cons a as, .cons x xs => AVal.Ok P t a x ∧ AVals.Ok P as xs

/-- A fact holds of `V` when its levels are levels of `V`. -/
def Fact.Below {Γ : Ctxt nfDialect} (V : Valuation Γ) (f : Fact) : Prop :=
  f.l < Γ.length → f.r < Γ.length → f.Holds V

theorem AVal.Facts.mono {P Q : Fact → Prop} (h : ∀ f, P f → Q f) {t : NfTy} {a : AVal t}
    {x : t.denote} (hf : AVal.Facts P t a x) : AVal.Facts Q t a x := by
  cases t <;> first | trivial | exact fun f hf' => h f (hf f hf')

theorem AVal.Ok.mono {P Q : Fact → Prop} (h : ∀ f, P f → Q f) {t : NfTy} {a : AVal t}
    {x : t.denote} (hf : AVal.Ok P t a x) : AVal.Ok Q t a x :=
  ⟨hf.1, hf.2.mono h⟩

theorem AVals.Ok.mono {P Q : Fact → Prop} (h : ∀ f, P f → Q f) :
    {ts : List NfTy} → {A : AVals ts} → {V : HVector NfTy.denote ts} → AVals.Ok P A V →
      AVals.Ok Q A V
  | [], .nil, .nil, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, hc => And.intro (hc.1.mono h) (AVals.Ok.mono h hc.2)

theorem AVals.mem_of_ok {P : Fact → Prop} :
    {ts : List NfTy} → {A : AVals ts} → {V : HVector NfTy.denote ts} → AVals.Ok P A V →
      AVals.Mem A V
  | [], .nil, .nil, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, h => And.intro h.1.1 (AVals.mem_of_ok h.2)

theorem AVals.ok_append {P : Fact → Prop} {ys : List NfTy} (A : AVals ys)
    (V : HVector NfTy.denote ys) :
    {xs : List NfTy} → (R : AVals xs) → (W : HVector NfTy.denote xs) →
      (AVals.Ok P (hvAppend (d := nfDialect) R A) (hvAppend (d := nfDialect) W V) ↔
        AVals.Ok P R W ∧ AVals.Ok P A V)
  | [], .nil, .nil => by simp [hvAppend, AVals.Ok]
  | _ :: _, .cons a R, .cons x W =>
    (and_congr_right' (AVals.ok_append A V R W)).trans and_assoc.symm

theorem AEnv.ok_get {P : Fact → Prop} :
    {Γ : Ctxt nfDialect} → {t : NfTy} → {A : AEnv Γ} → {V : Valuation Γ} → AVals.Ok P A V →
      (v : Var Γ t) → AVal.Ok P t (A.get v) (v.lookup V)
  | _, _, .cons _ _, .cons _ _, h, .here => h.1
  | _, _, .cons _ _, .cons _ _, h, .there v => AEnv.ok_get h.2 v

theorem AEnv.ok_getArgs {P : Fact → Prop} {Γ : Ctxt nfDialect} {A : AEnv Γ}
    {V : Valuation Γ} (h : AVals.Ok P A V) :
    {ts : List NfTy} → (vs : HVector (fun t => Var Γ t) ts) →
      AVals.Ok P (A.getArgs vs) (Expr.lookupArgs vs V)
  | [], .nil => trivial
  | _ :: _, .cons v vs => ⟨AEnv.ok_get h v, AEnv.ok_getArgs h vs⟩

theorem AEnv.ok_set {P : Fact → Prop} :
    {Γ : Ctxt nfDialect} → {t : NfTy} → {A : AEnv Γ} → {V : Valuation Γ} → AVals.Ok P A V →
      (v : Var Γ t) → {a : AVal t} → AVal.Ok P t a (v.lookup V) → AVals.Ok P (A.set v a) V
  | _, _, .cons _ _, .cons _ _, h, .here, _, ha => ⟨ha, h.2⟩
  | _, _, .cons _ _, .cons _ _, h, .there v, _, ha => ⟨h.1, AEnv.ok_set h.2 v ha⟩

/-! ## 2. Restriction, join, top, emptiness -/

theorem AVal.mem_restrict (n : Nat) :
    (t : NfTy) → (a : AVal t) → (x : t.denote) →
      (AVal.Mem t (AVal.restrict n t a) x ↔ AVal.Mem t a x)
  | .arr _ t, a, f => forall_congr' fun j => AVal.mem_restrict n t a (f j)
  | .bit, _, _ | .word _, _, _ | .unit, _, _ | .pair _ _, _, _ | .uint _, _, _
  | .sint _, _, _ | .int, _, _ | .tnil, _, _ | .tcons _ _, _, _ | .slice _, _, _ => Iff.rfl

theorem AVal.ok_restrict {P : Fact → Prop} (n : Nat) (t : NfTy) (a : AVal t) (x : t.denote)
    (h : AVal.Ok (fun f => f.l < n → f.r < n → P f) t a x) :
    AVal.Ok P t (AVal.restrict n t a) x := by
  refine ⟨(AVal.mem_restrict n t a x).2 h.1, ?_⟩
  cases t
  case bit =>
    intro f hf
    have h2 := h.2
    cases x <;> simp_all [AVal.restrict, AVal.Facts, List.mem_filter]
  all_goals trivial

theorem AVals.ok_restrict {P : Fact → Prop} (n : Nat) :
    {ts : List NfTy} → (A : AVals ts) → (W : HVector NfTy.denote ts) →
      AVals.Ok (fun f => f.l < n → f.r < n → P f) A W → AVals.Ok P (AVals.restrict n A) W
  | [], .nil, .nil, _ => trivial
  | _ :: _, .cons a A, .cons x W, h =>
    And.intro (AVal.ok_restrict n _ a x h.1) (AVals.ok_restrict n A W h.2)

theorem AVal.mem_join_left :
    (t : NfTy) → (a b : AVal t) → (x : t.denote) → AVal.Mem t a x →
      AVal.Mem t (AVal.join t a b) x
  | .bit, a, b, x, hm => by
    simp only [AVal.join, AVal.Mem] at hm ⊢
    split <;> simp_all
  | .word _, _, _, _, hm => Iv.Has.hull_left hm
  | .arr _ t, a, b, f, hm => fun j => AVal.mem_join_left t a b (f j) (hm j)
  | .unit, _, _, _, _ | .pair _ _, _, _, _, _ | .uint _, _, _, _, _ | .sint _, _, _, _, _
  | .int, _, _, _, _ | .tnil, _, _, _, _ | .tcons _ _, _, _, _, _ | .slice _, _, _, _, _ =>
    trivial

theorem AVal.mem_join_right :
    (t : NfTy) → (a b : AVal t) → (x : t.denote) → AVal.Mem t b x →
      AVal.Mem t (AVal.join t a b) x
  | .bit, a, b, x, hm => by
    simp only [AVal.join, AVal.Mem] at hm ⊢
    split <;> simp_all
  | .word _, _, _, _, hm => Iv.Has.hull_right hm
  | .arr _ t, a, b, f, hm => fun j => AVal.mem_join_right t a b (f j) (hm j)
  | .unit, _, _, _, _ | .pair _ _, _, _, _, _ | .uint _, _, _, _, _ | .sint _, _, _, _, _
  | .int, _, _, _, _ | .tnil, _, _, _, _ | .tcons _ _, _, _, _, _ | .slice _, _, _, _, _ =>
    trivial

theorem AVal.ok_join_left {P : Fact → Prop} (t : NfTy) (a b : AVal t) (x : t.denote)
    (h : AVal.Ok P t a x) : AVal.Ok P t (AVal.join t a b) x := by
  refine ⟨AVal.mem_join_left t a b x h.1, ?_⟩
  cases t
  case bit =>
    intro f hf
    have h2 := h.2
    cases x <;> simp_all [AVal.join, List.mem_filter]
  all_goals trivial

theorem AVal.ok_join_right {P : Fact → Prop} (t : NfTy) (a b : AVal t) (x : t.denote)
    (h : AVal.Ok P t b x) : AVal.Ok P t (AVal.join t a b) x := by
  refine ⟨AVal.mem_join_right t a b x h.1, ?_⟩
  cases t
  case bit =>
    intro f hf
    have h2 := h.2
    cases x <;> simp_all [AVal.join, List.mem_filter]
  all_goals trivial

theorem AVals.ok_join_left {P : Fact → Prop} :
    {ts : List NfTy} → (A B : AVals ts) → (W : HVector NfTy.denote ts) → AVals.Ok P A W →
      AVals.Ok P (AVals.join A B) W
  | [], .nil, .nil, .nil, _ => trivial
  | _ :: _, .cons a A, .cons b B, .cons x W, h =>
    And.intro (AVal.ok_join_left _ a b x h.1) (AVals.ok_join_left A B W h.2)

theorem AVals.ok_join_right {P : Fact → Prop} :
    {ts : List NfTy} → (A B : AVals ts) → (W : HVector NfTy.denote ts) → AVals.Ok P B W →
      AVals.Ok P (AVals.join A B) W
  | [], .nil, .nil, .nil, _ => trivial
  | _ :: _, .cons a A, .cons b B, .cons x W, h =>
    And.intro (AVal.ok_join_right _ a b x h.1) (AVals.ok_join_right A B W h.2)

theorem AVal.mem_top : (t : NfTy) → (x : t.denote) → AVal.Mem t (AVal.top t) x
  | .bit, _ => Or.inl rfl
  | .word _, x => ⟨by simp [AVal.top], by have := x.isLt; simp [AVal.top]; grind⟩
  | .arr _ t, f => fun j => AVal.mem_top t (f j)
  | .unit, _ | .pair _ _, _ | .uint _, _ | .sint _, _ | .int, _ | .tnil, _ | .tcons _ _, _
  | .slice _, _ => trivial

theorem AVal.ok_top {P : Fact → Prop} (t : NfTy) (x : t.denote) :
    AVal.Ok P t (AVal.top t) x := by
  refine ⟨AVal.mem_top t x, ?_⟩
  cases t
  case bit => intro f hf; cases x <;> simp [AVal.top] at hf
  all_goals trivial

theorem AVals.ok_top {P : Fact → Prop} :
    {ts : List NfTy} → (W : HVector NfTy.denote ts) → AVals.Ok P (AVals.top ts) W
  | [], .nil => trivial
  | _ :: _, .cons x W => And.intro (AVal.ok_top _ x) (AVals.ok_top W)

theorem AVal.empty_of_mem : (t : NfTy) → (a : AVal t) → (x : t.denote) → AVal.Mem t a x →
    AVal.empty t a = false
  | .word _, _, _, h => by
    have := h.1; have := h.2
    simp only [AVal.empty, decide_eq_false_iff_not]
    omega
  | .arr n t, a, f, h => by
    simp only [AVal.empty]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [AVal.empty_of_mem t a (f ⟨0, hn⟩) (h _)]
  | .bit, _, _, _ | .unit, _, _, _ | .pair _ _, _, _, _ | .uint _, _, _, _ | .sint _, _, _, _
  | .int, _, _, _ | .tnil, _, _, _ | .tcons _ _, _, _, _ | .slice _, _, _, _ => rfl

theorem AVals.isEmpty_of_ok {P : Fact → Prop} :
    {ts : List NfTy} → (A : AVals ts) → (W : HVector NfTy.denote ts) → AVals.Ok P A W →
      AVals.isEmpty A = false
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons a A, .cons x W, h => by
    simp [AVals.isEmpty, AVal.empty_of_mem _ a x h.1.1, AVals.isEmpty_of_ok A W h.2]

/-! ## 3. Facts under extensions of a valuation -/

theorem valIntAt_append {Γ : Ctxt nfDialect} (V : Valuation Γ) :
    {xs : List NfTy} → (X : Valuation (d := nfDialect) xs) → (k : Nat) →
      valIntAt (hvAppend (d := nfDialect) X V) (xs.length + k) = valIntAt V k
  | [], .nil, k => by simp [hvAppend]
  | _ :: xs, .cons _ X, k => by
    rw [List.length_cons, Nat.add_right_comm]
    exact valIntAt_append V X k

theorem bind_levelIdx_append {Γ : Ctxt nfDialect} {xs : List NfTy}
    (X : Valuation (d := nfDialect) xs) (V : Valuation Γ) {l : Nat} (hl : l < Γ.length) :
    (levelIdx (xs ++ Γ).length l).bind (valIntAt (hvAppend (d := nfDialect) X V)) =
      (levelIdx Γ.length l).bind (valIntAt V) := by
  have h1 : levelIdx (xs ++ Γ).length l = some (xs.length + (Γ.length - 1 - l)) := by
    simp only [levelIdx, List.length_append, show l < xs.length + Γ.length by omega,
      ↓reduceIte, Option.some.injEq]
    omega
  have h2 : levelIdx Γ.length l = some (Γ.length - 1 - l) := by simp [levelIdx, hl]
  rw [h1, h2, Option.bind_some, Option.bind_some, valIntAt_append]

theorem Fact.lt_of_holds {Γ : Ctxt nfDialect} {V : Valuation Γ} {f : Fact}
    (h : f.Holds V) : f.l < Γ.length ∧ f.r < Γ.length := by
  obtain ⟨m, n, hm, hn, -⟩ := h
  constructor
  · by_contra hc
    simp [levelIdx, hc] at hm
  · by_contra hc
    simp [levelIdx, hc] at hn

theorem Fact.holds_append_iff {Γ : Ctxt nfDialect} {xs : List NfTy}
    (X : Valuation (d := nfDialect) xs) (V : Valuation Γ) {f : Fact} (hl : f.l < Γ.length)
    (hr : f.r < Γ.length) : f.Holds (hvAppend (d := nfDialect) X V) ↔ f.Holds V := by
  unfold Fact.Holds
  rw [bind_levelIdx_append X V hl, bind_levelIdx_append X V hr]

theorem Fact.Holds.append {Γ : Ctxt nfDialect} {xs : List NfTy}
    (X : Valuation (d := nfDialect) xs) {V : Valuation Γ} {f : Fact} (h : f.Holds V) :
    f.Holds (hvAppend (d := nfDialect) X V) :=
  (Fact.holds_append_iff X V (Fact.lt_of_holds h).1 (Fact.lt_of_holds h).2).2 h

theorem Fact.Below.of_append {Γ : Ctxt nfDialect} {xs : List NfTy}
    (X : Valuation (d := nfDialect) xs) {V : Valuation Γ} {f : Fact}
    (h : f.Below (hvAppend (d := nfDialect) X V)) : f.Below V := fun hl hr =>
  (Fact.holds_append_iff X V hl hr).1
    (h (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega))

/-! ## 4. `AEnv.Sat` as `AVals.Ok` -/

/-- Unfolding lemma of `valBitAt` at a successor position. -/
theorem valBitAt_cons_succ {Γ : Ctxt nfDialect} {t : NfTy} (x : t.denote) (V : Valuation Γ)
    (n : Nat) : valBitAt (Γ := t :: Γ) (HVector.cons x V) (n + 1) = valBitAt V n := by
  cases t <;> rfl

/-- Unfolding lemma of `valBitAt` at the position of a bit. -/
theorem valBitAt_bit_zero {Γ : Ctxt nfDialect} (x : Bool) (V : Valuation Γ) :
    valBitAt (Γ := .bit :: Γ) (HVector.cons x V) 0 = some x := rfl

/-- Unfolding lemma of `AEnv.bitAt` at a successor position. -/
theorem bitAt_cons_succ {Γ : Ctxt nfDialect} {t : NfTy} (a : AVal t) (A : AEnv Γ)
    (n : Nat) : AEnv.bitAt (Γ := t :: Γ) (HVector.cons a A) (n + 1) = A.bitAt n := rfl

theorem AVals.ok_iff {P : Fact → Prop} :
    {Γ : Ctxt nfDialect} → (A : AEnv Γ) → (V : Valuation Γ) →
      (AVals.Ok P A V ↔ AVals.Mem A V ∧ ∀ n a b, A.bitAt n = some a →
        valBitAt V n = some b → ∀ f ∈ (if b then a.tt else a.ff), P f)
  | [], .nil, .nil => by simp [AVals.Mem, AEnv.bitAt]
  | t :: Γ, .cons a A, .cons x V => by
    have ih := AVals.ok_iff (P := P) A V
    constructor
    · intro h
      obtain ⟨hm, hB⟩ := ih.1 h.2
      refine ⟨And.intro h.1.1 hm, ?_⟩
      intro n a' b ha hb
      cases n with
      | zero =>
        have hf := h.1.2
        cases t <;> simp only [AEnv.bitAt, bitArg, reduceCtorEq, Option.some.injEq] at ha
        rw [valBitAt_bit_zero, Option.some.injEq] at hb
        subst ha hb
        exact hf
      | succ n =>
        rw [bitAt_cons_succ] at ha
        rw [valBitAt_cons_succ] at hb
        exact hB n a' b ha hb
    · rintro ⟨hm, hB⟩
      refine And.intro (And.intro hm.1 ?_) (ih.2 ⟨hm.2, fun n a' b ha hb => hB (n + 1) a' b
        (by rw [bitAt_cons_succ]; exact ha) (by rw [valBitAt_cons_succ]; exact hb)⟩)
      cases t
      case bit => exact hB 0 a x rfl rfl
      all_goals trivial

theorem AEnv.sat_iff {Γ : Ctxt nfDialect} (A : AEnv Γ) (V : Valuation Γ) :
    A.Sat V ↔ AVals.Ok (Fact.Holds V) A V :=
  (AVals.ok_iff A V).symm

/-! ## 5. Refinement by a branch condition -/

theorem AEnv.ivAt_sound {P : Fact → Prop} :
    {Γ : Ctxt nfDialect} → (A : AEnv Γ) → (V : Valuation Γ) → AVals.Ok P A V →
      (n : Nat) → (i : Iv) → A.ivAt n = some i → ∃ m, valIntAt V n = some m ∧ i.Has m
  | [], .nil, .nil, _, _, _, h => by simp [AEnv.ivAt] at h
  | t :: _, .cons a A, .cons x V, h, 0, i, hi => by
    have hm := h.1.1
    cases t <;> simp only [AEnv.ivAt, wordArg, reduceCtorEq, Option.some.injEq] at hi
    subst hi
    exact ⟨_, rfl, hm⟩
  | _ :: _, .cons _ A, .cons _ V, h, n + 1, i, hi => AEnv.ivAt_sound A V h.2 n i hi

theorem AEnv.ok_setIvAt {P : Fact → Prop} :
    {Γ : Ctxt nfDialect} → (A : AEnv Γ) → (V : Valuation Γ) → AVals.Ok P A V →
      (n : Nat) → (i : Iv) → (m : Int) → valIntAt V n = some m → i.Has m →
        AVals.Ok P (A.setIvAt n i) V
  | [], .nil, .nil, h, _, _, _, _, _ => h
  | t :: _, .cons a A, .cons x V, h, 0, i, m, hm, hi => by
    refine And.intro ?_ h.2
    cases t
    case word w =>
      change some ((x.toNat : Nat) : Int) = some m at hm
      rw [Option.some.injEq] at hm
      subst hm
      exact ⟨hi, trivial⟩
    all_goals exact h.1
  | _ :: _, .cons a A, .cons x V, h, n + 1, i, m, hm, hi =>
    And.intro h.1 (AEnv.ok_setIvAt A V h.2 n i m hm hi)

theorem AEnv.ok_applyFact {Γ : Ctxt nfDialect} (A : AEnv Γ) (V : Valuation Γ) (f : Fact)
    (hA : AVals.Ok (Fact.Holds V) A V) (hf : f.Holds V) :
    AVals.Ok (Fact.Holds V) (A.applyFact f) V := by
  obtain ⟨m, n, hm, hn, hmn⟩ := hf
  unfold AEnv.applyFact
  split
  · rename_i il ir hil hir
    rw [hil, Option.bind_some] at hm
    rw [hir, Option.bind_some] at hn
    split
    · rename_i a b ha hb
      obtain ⟨m', hm', ham⟩ := AEnv.ivAt_sound A V hA il a ha
      obtain ⟨n', hn', hbn⟩ := AEnv.ivAt_sound A V hA ir b hb
      rw [hm] at hm'
      rw [hn] at hn'
      cases hm'
      cases hn'
      have hd : m + (if f.strict then 1 else 0) ≤ n := by split at hmn <;> simp_all
      dsimp only
      generalize (if f.strict = true then (1 : Int) else 0) = d at hd ⊢
      have h1 := ham.1; have h2 := ham.2; have h3 := hbn.1; have h4 := hbn.2
      refine AEnv.ok_setIvAt _ V
        (AEnv.ok_setIvAt A V hA il (a.1, min a.2 (b.2 - d)) m hm ⟨h1, ?_⟩) ir
        (max b.1 (a.1 + d), b.2) n hn ⟨?_, h4⟩
      · simp only; omega
      · simp only; omega
    · exact hA
  · exact hA

theorem AEnv.ok_refineBit {Γ : Ctxt nfDialect} (A : AEnv Γ) (V : Valuation Γ)
    (c : Var Γ .bit) (hA : AVals.Ok (Fact.Holds V) A V) :
    AVals.Ok (Fact.Holds V) (A.refineBit c (c.lookup V)) V := by
  have hc := AEnv.ok_get hA c
  have h0 : AVals.Ok (Fact.Holds V) (A.set c { A.get c with val := some (c.lookup V) }) V :=
    AEnv.ok_set hA c (And.intro (Or.inr rfl) hc.2)
  have key : ∀ (fs : List Fact) (B : AEnv Γ), (∀ f ∈ fs, f.Holds V) →
      AVals.Ok (Fact.Holds V) B V → AVals.Ok (Fact.Holds V) (fs.foldl AEnv.applyFact B) V := by
    intro fs
    induction fs with
    | nil => intro B _ hB; exact hB
    | cons f fs ih =>
      intro B hfs hB
      exact ih _ (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
        (AEnv.ok_applyFact B V f hB (hfs f List.mem_cons_self))
  exact key _ _ hc.2 h0

theorem AEnv.reach_of_lookup {Γ : Ctxt nfDialect} (A : AEnv Γ) (V : Valuation Γ)
    (c : Var Γ .bit) (hA : AVals.Ok (Fact.Holds V) A V) : A.reach c (c.lookup V) = true := by
  have hc := (AEnv.ok_get hA c).1
  have he := AVals.isEmpty_of_ok _ V (AEnv.ok_refineBit A V c hA)
  unfold AEnv.reach
  rw [he]
  rcases hc with h | h <;> simp [h]

/-! ## 6. Abstract operations -/

/-- Unfolding lemma of `AVal.Ok` at a bit. -/
theorem AVal.ok_bit_iff {P : Fact → Prop} {a : ABit} {b : Bool} :
    AVal.Ok P .bit a b ↔
      (a.val = none ∨ a.val = some b) ∧ ∀ f ∈ (if b then a.tt else a.ff), P f :=
  Iff.rfl

theorem ABit.ok_known {P : Fact → Prop} (b : Bool) : AVal.Ok P .bit (ABit.known b) b := by
  rw [AVal.ok_bit_iff]
  cases b <;> simp [ABit.known]

theorem ABit.ok_not {P : Fact → Prop} {a : ABit} {b : Bool} (h : AVal.Ok P .bit a b) :
    AVal.Ok P .bit a.not (!b) := by
  rw [AVal.ok_bit_iff] at h ⊢
  obtain ⟨hm, hf⟩ := h
  refine And.intro ?_ ?_
  · rcases hm with hm | hm <;> simp [ABit.not, hm]
  · cases b <;> simpa [ABit.not] using hf

theorem ABit.ok_and {P : Fact → Prop} {a c : ABit} {x y : Bool} (ha : AVal.Ok P .bit a x)
    (hc : AVal.Ok P .bit c y) : AVal.Ok P .bit (ABit.and a c) (x && y) := by
  rw [AVal.ok_bit_iff] at ha hc ⊢
  obtain ⟨ham, haf⟩ := ha
  obtain ⟨hcm, hcf⟩ := hc
  refine And.intro ?_ ?_
  · rcases ham with ham | ham <;> rcases hcm with hcm | hcm <;> simp only [ABit.and, ham, hcm] <;>
      cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp_all [ABit.and]
    grind

theorem ABit.ok_or {P : Fact → Prop} {a c : ABit} {x y : Bool} (ha : AVal.Ok P .bit a x)
    (hc : AVal.Ok P .bit c y) : AVal.Ok P .bit (ABit.or a c) (x || y) := by
  rw [AVal.ok_bit_iff] at ha hc ⊢
  obtain ⟨ham, haf⟩ := ha
  obtain ⟨hcm, hcf⟩ := hc
  refine And.intro ?_ ?_
  · rcases ham with ham | ham <;> rcases hcm with hcm | hcm <;> simp only [ABit.or, ham, hcm] <;>
      cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp_all [ABit.or]
    grind

theorem ABit.ok_orElse {P : Fact → Prop} {c a : ABit} {x : Bool} (hc : AVal.Ok P .bit c x)
    (ha : AVal.Mem .bit a x) : AVal.Ok P .bit { c with val := c.val <|> a.val } x := by
  refine And.intro ?_ hc.2
  change a.val = none ∨ a.val = some x at ha
  change (c.val <|> a.val) = none ∨ (c.val <|> a.val) = some x
  rcases hc.1 with h | h <;> rw [h] <;> simp_all

theorem varIdx_lt : {Γ : Ctxt nfDialect} → {t : NfTy} → (v : Var Γ t) →
    varLevel.varIdx v < Γ.length
  | _, _, .here => by simp [varLevel.varIdx]
  | _, _, .there v => Nat.add_lt_add_right (varIdx_lt v) 1

theorem valIntAt_varIdx : {Γ : Ctxt nfDialect} → {w : Nat} → (v : Var Γ (.word w)) →
    (V : Valuation Γ) → valIntAt V (varLevel.varIdx v) = some ((v.lookup V).toNat : Int)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ V => valIntAt_varIdx v V

theorem bind_varLevel {Γ : Ctxt nfDialect} {w : Nat} (v : Var Γ (.word w)) (V : Valuation Γ) :
    (levelIdx Γ.length (varLevel v)).bind (valIntAt V) = some ((v.lookup V).toNat : Int) := by
  have h := varIdx_lt v
  have h' : levelIdx Γ.length (varLevel v) = some (varLevel.varIdx v) := by
    unfold levelIdx
    simp only [show varLevel v < Γ.length by unfold varLevel; omega, ↓reduceIte,
      Option.some.injEq]
    unfold varLevel
    omega
  rw [h', Option.bind_some]
  exact valIntAt_varIdx v V

theorem cmpFacts_holds {Γ : Ctxt nfDialect} {w : Nat} (p : NfPred) (x y : Var Γ (.word w))
    (V : Valuation Γ) :
    ∀ f ∈ (if p.denote (x.lookup V) (y.lookup V) then (cmpFacts p (varLevel x) (varLevel y)).1
      else (cmpFacts p (varLevel x) (varLevel y)).2), f.Holds V := by
  intro f hf
  have hx := bind_varLevel x V
  have hy := bind_varLevel y V
  generalize x.lookup V = a at hx hf
  generalize y.lookup V = b at hy hf
  have h1 : ∀ s : Bool, (if s then (a.toNat : Int) < b.toNat else (a.toNat : Int) ≤ b.toNat) →
      Fact.Holds V ⟨s, varLevel x, varLevel y⟩ := fun s h => ⟨_, _, hx, hy, h⟩
  have h2 : ∀ s : Bool, (if s then (b.toNat : Int) < a.toNat else (b.toNat : Int) ≤ a.toNat) →
      Fact.Holds V ⟨s, varLevel y, varLevel x⟩ := fun s h => ⟨_, _, hy, hx, h⟩
  have hab : a = b ↔ a.toNat = b.toNat := BitVec.toNat_inj.symm
  cases p <;> simp only [cmpFacts, NfPred.denote, BitVec.ult, BitVec.ule, hab] at hf
  all_goals (unfold Fact.Holds; grind)

theorem ok_callBit (S : NameSpec) (T : NfLeafTable) (hS : S.SoundAt T) {Γ : Ctxt nfDialect}
    (A : AEnv Γ) (V : Valuation Γ) (hA : AVals.Ok (Fact.Holds V) A V) (f : String)
    (as : List NfTy) (args : HVector (fun t => Var Γ t) as) (a : ABit) (y : Bool)
    (hy : T.call f as .bit (Expr.lookupArgs args V) = some y)
    (ha : AVal.Ok (Fact.Holds V) .bit a y) :
    AVal.Ok (Fact.Holds V) .bit (callBit S A f as args a) y := by
  match as, args with
  | [], .nil => exact ha
  | [t], .cons x .nil =>
    cases t
    case bit =>
      dsimp only [callBit]
      rcases hc : S.conn? f with _ | _ | _ | _ <;> dsimp only
      · exact ha
      · exact ha
      · exact ha
      · have := hS.not_ f (x.lookup V) y hc hy
        subst this
        exact ABit.ok_orElse (ABit.ok_not (AEnv.ok_get hA x)) ha.1
    all_goals exact ha
  | [t1, t2], .cons x (.cons z .nil) =>
    cases t1 <;> cases t2 <;> try exact ha
    case bit.bit =>
      dsimp only [callBit]
      rcases hc : S.conn? f with _ | _ | _ | _ <;> dsimp only
      · exact ha
      · have := hS.and_ f (x.lookup V) (z.lookup V) y hc hy
        subst this
        exact ABit.ok_orElse (ABit.ok_and (AEnv.ok_get hA x) (AEnv.ok_get hA z)) ha.1
      · have := hS.or_ f (x.lookup V) (z.lookup V) y hc hy
        subst this
        exact ABit.ok_orElse (ABit.ok_or (AEnv.ok_get hA x) (AEnv.ok_get hA z)) ha.1
      · exact ha
    case word.word w w' =>
      dsimp only [callBit]
      rcases hp : S.cmp? f with _ | p <;> dsimp only
      · exact ha
      · change AVal.Ok _ .bit (if w = w' then _ else a) y
        by_cases hw : w = w'
        · subst hw
          simp only [↓reduceIte]
          have := hS.cmp f p w (x.lookup V) (z.lookup V) y hp hy
          subst this
          exact And.intro ha.1 (cmpFacts_holds p x z V)
        · simp only [hw, ↓reduceIte]
          exact ha
  | t1 :: t2 :: t3 :: ts, .cons _ (.cons _ (.cons _ _)) =>
    cases t1 <;> cases t2 <;> exact ha

theorem ok_callXfer (S : NameSpec) (T : NfLeafTable) (hS : S.SoundAt T) {Γ : Ctxt nfDialect}
    (A : AEnv Γ) (V : Valuation Γ) (hA : AVals.Ok (Fact.Holds V) A V) (f : String)
    (as : List NfTy) (r : NfTy) (args : HVector (fun t => Var Γ t) as) (a : AVal r)
    (h : callXfer S A f as r args = .ok a) :
    ∃ y, T.call f as r (Expr.lookupArgs args V) = some y ∧ AVal.Ok (Fact.Holds V) r a y := by
  unfold callXfer at h
  dsimp only at h
  rcases h0 : S.xfer f as r (A.getArgs args) with _ | a0 <;> rw [h0] at h <;> dsimp only at h
  · cases h
  · obtain ⟨y, hy, hm⟩ := hS.xfer f as r _ a0 _ h0 (AVals.mem_of_ok (AEnv.ok_getArgs hA args))
    refine ⟨y, hy, ?_⟩
    have hr : AVal.Ok (Fact.Holds V) r (AVal.restrict 0 r a0) y :=
      AVal.ok_restrict 0 r a0 y (And.intro hm (by cases r <;> first | trivial | grind))
    cases r
    case bit =>
      cases h
      exact ok_callBit S T hS A V hA f as args _ y hy hr
    all_goals (cases h; exact hr)

theorem ok_ofLit {P : Fact → Prop} (t : NfTy) (v : Int) (y : t.denote)
    (h : NfTy.ofLit? t v = some y) : AVal.Ok P t (AVal.ofLit t v) y := by
  cases t
  case word w =>
    simp only [NfTy.ofLit?] at h
    split at h
    · rename_i hv
      cases h
      refine And.intro ?_ trivial
      simp only [AVal.ofLit, AVal.Mem, ivPoint, Iv.Has]
      grind only [Int.eq_natCast_toNat, = BitVec.toNat_ofNatLT, Int.toNat_lt]
    · cases h
  all_goals exact AVal.ok_top _ y

theorem evalOp_sound (S : NameSpec) (T : NfLeafTable) (hS : S.SoundAt T) {Γ : Ctxt nfDialect}
    {A : AEnv Γ} {V : Valuation Γ} (hA : AVals.Ok (Fact.Holds V) A V) :
    (op : NfOp) → (args : HVector (fun t => Var Γ t) op.sig) → (a : AVal op.ret) →
      evalOp S A op args = .ok a →
      ∃ y, nfDenoteOp T op (Expr.lookupArgs args V) = some y ∧
        AVal.Ok (Fact.Holds V) op.ret a y
  | .const _ v, _, a, h => by
    cases h
    exact ⟨v, rfl, And.intro (Iv.has_point _) trivial⟩
  | .constBit b, _, a, h => by
    cases h
    exact ⟨b, rfl, ABit.ok_known b⟩
  | .constUnit, _, a, h => by
    cases h
    exact ⟨(), rfl, And.intro trivial trivial⟩
  | .ilit t v, _, a, h => by
    change (if (NfTy.ofLit? t v).isSome then .ok (AVal.ofLit t v)
      else .error s!"literal {v} outside the type {reprStr t}") = Except.ok a at h
    split at h
    · rename_i hs
      cases h
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨y, hy, ok_ofLit t v y hy⟩
    · cases h
  | .notB, .cons x .nil, a, h => by
    cases h
    exact ⟨_, rfl, ABit.ok_not (AEnv.ok_get hA x)⟩
  | .andB, .cons x (.cons z .nil), a, h => by
    cases h
    exact ⟨_, rfl, ABit.ok_and (AEnv.ok_get hA x) (AEnv.ok_get hA z)⟩
  | .orB, .cons x (.cons z .nil), a, h => by
    cases h
    exact ⟨_, rfl, ABit.ok_or (AEnv.ok_get hA x) (AEnv.ok_get hA z)⟩
  | .call f as r, args, a, h => ok_callXfer S T hS A V hA f as r args a h
  | .named _ op, args, a, h => evalOp_sound S T hS hA op args a h
  | .abort _, _, _, h => by cases h
  | .bin _ _, _, _, h | .un _ _, _, _, h | .cast _ _, _, _, h | .scast _ _, _, _, h
  | .cmp _ _, _, _, h | .xorB, _, _, h | .eqB, _, _, h | .index _ _, _, _, h
  | .update _ _, _, _, h | .arrLit _ _, _, _, h | .arrRepeat _ _, _, _, h
  | .mkPair _ _, _, _, h | .fst _ _, _, _, h | .snd _ _, _, _, h | .ctr, _, _, h
  | .trip _, _, _, h | .boundInt _, _, _, h | .tnilV, _, _, h | .tconsV _ _, _, _, h
  | .thead _ _, _, _, h | .ttail _ _, _, _, h => by cases h

theorem evalExpr_sound (S : NameSpec) (T : NfLeafTable) (hS : S.SoundAt T)
    {Γ : Ctxt nfDialect} {t : NfTy} {A : AEnv Γ} {V : Valuation Γ}
    (hA : AVals.Ok (Fact.Holds V) A V) (e : Expr nfDialect Γ t) (a : AVal t)
    (h : evalExpr S A e = .ok a) :
    ∃ y, @Expr.denoteM nfDialect Option _ _ (nfDenote T) Γ t e V = some y ∧
      AVal.Ok (Fact.Holds V) t a y := by
  obtain ⟨op, rfl, args⟩ := e
  exact evalOp_sound S T hS hA op args a h

/-! ## 7. Programs -/

theorem except_bind_ok {α β : Type} {x : Except String α} {g : α → Except String β} {b : β}
    (h : (x >>= g) = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem except_map_ok {α β : Type} {x : Except String α} {g : α → β} {b : β}
    (h : (g <$> x) = .ok b) : ∃ a, x = .ok a ∧ g a = b := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

/-- The soundness of the checker at the program `p`: from every abstract environment and every
    valuation in it, a run of the checker with results `B` gives results `W` of `p` at every
    fuel, in `B` with the facts on the levels of the valuation. -/
def Sound (S : NameSpec) (T : NfLeafTable) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ (A : AEnv Γ) (B : AVals ts) (V : Valuation Γ), run S A p = .ok B →
    AVals.Ok (Fact.Holds V) A V →
    ∃ W : Valuation (d := nfDialect) ts,
      (∀ fuel, @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V = some W) ∧
      AVals.Ok (Fact.Below V) B W

/-- The soundness of the step of the counted loop: a counted loop is sound when its body and
    its continuation are. -/
def ForSound (S : NameSpec) (T : NfLeafTable) : Prop :=
  ∀ {Γ : Ctxt nfDialect} {cs ts : List NfTy} (cnt : Var Γ (HasWord64.word (d := nfDialect)))
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg nfDialect (cs ++ HasWord64.word (d := nfDialect) :: Γ) cs)
    (k : NFProg nfDialect (cs ++ Γ) ts),
    Sound S T body → Sound S T k → Sound S T (.forLoop cnt inits body k)

theorem sound_ret (S : NameSpec) (T : NfLeafTable) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (vs : HVector (fun t => Var Γ t) ts) : Sound S T (NFProg.ret (d := nfDialect) vs) := by
  intro A B V h hA
  cases h
  exact ⟨_, fun _ => rfl, (AEnv.ok_getArgs hA vs).mono fun f hf _ _ => hf⟩

theorem sound_var (S : NameSpec) (T : NfLeafTable) (hS : S.SoundAt T) {Γ : Ctxt nfDialect}
    {t : NfTy} {ts : List NfTy} (e : Expr nfDialect Γ t) (k : NFProg nfDialect (t :: Γ) ts)
    (hk : Sound S T k) : Sound S T (.var e k) := by
  intro A B V h hA
  obtain ⟨a, ha, hk'⟩ := except_bind_ok (x := evalExpr S A e) (g := fun a => run S (.cons a A) k) h
  obtain ⟨y, hy, hay⟩ := evalExpr_sound S T hS hA e a ha
  have hA' : AVals.Ok (Fact.Holds (V.extend y)) (HVector.cons a A) (V.extend y) :=
    And.intro (hay.mono fun f hf => hf.append (HVector.cons y .nil))
      (hA.mono fun f hf => hf.append (HVector.cons y .nil))
  obtain ⟨W, hW, hB⟩ := hk _ _ _ hk' hA'
  refine ⟨W, fun fuel => ?_, hB.mono fun f hf => hf.of_append (HVector.cons y .nil)⟩
  let _ : DialectDenoteM nfDialect Option := nfDenote T
  rw [NFProg.denote_var, hy]
  exact hW fuel

theorem ite_finish (S : NameSpec) (T : NfLeafTable) {Γ : Ctxt nfDialect} {rs ts : List NfTy}
    {k : NFProg nfDialect (rs ++ Γ) ts} (hk : Sound S T k) {A : AEnv Γ} {V : Valuation Γ}
    (hA : AVals.Ok (Fact.Holds V) A V) {r : AVals rs} {W1 : Valuation (d := nfDialect) rs}
    (hr : AVals.Ok (Fact.Below V) r W1) {B : AVals ts}
    (h : run S (hvAppend (d := nfDialect) (f := AVal) (AVals.restrict Γ.length r) A) k = .ok B) :
    ∃ W, (∀ fuel, @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel _ _ k
      (hvAppend (d := nfDialect) W1 V) = some W) ∧ AVals.Ok (Fact.Below V) B W := by
  have hR : AVals.Ok (Fact.Holds V) (AVals.restrict Γ.length r) W1 :=
    AVals.ok_restrict _ r W1 hr
  have hA' : AVals.Ok (Fact.Holds (hvAppend (d := nfDialect) W1 V))
      (hvAppend (d := nfDialect) (AVals.restrict Γ.length r) A)
      (hvAppend (d := nfDialect) W1 V) :=
    (AVals.ok_append A V _ W1).2
      ⟨hR.mono fun f hf => hf.append W1, hA.mono fun f hf => hf.append W1⟩
  obtain ⟨W, hW, hB⟩ := hk _ _ _ h hA'
  exact ⟨W, hW, hB.mono fun f hf => hf.of_append W1⟩

theorem sound_ite (S : NameSpec) (T : NfLeafTable) {Γ : Ctxt nfDialect} {rs ts : List NfTy}
    (c : Var Γ (HasBitType.bit (d := nfDialect))) (thn els : NFProg nfDialect Γ rs)
    (k : NFProg nfDialect (rs ++ Γ) ts) (ht : Sound S T thn) (he : Sound S T els)
    (hk : Sound S T k) : Sound S T (.ifThenElse c thn els k) := by
  intro A B V h hA
  let _ : DialectDenoteM nfDialect Option := nfDenote T
  have hreach := AEnv.reach_of_lookup A V c hA
  have href := AEnv.ok_refineBit A V c hA
  have hbool : HasBoolBit.toBool (d := nfDialect) (c.lookup V) = c.lookup V := rfl
  have key : ∀ (r : AVals rs) (W1 : Valuation (d := nfDialect) rs),
      (∀ fuel, (if HasBoolBit.toBool (d := nfDialect) (c.lookup V) then thn.denote fuel V
        else els.denote fuel V) = some W1) →
      AVals.Ok (Fact.Below V) r W1 →
      run S (hvAppend (d := nfDialect) (f := AVal) (AVals.restrict Γ.length r) A) k = .ok B →
      ∃ W, (∀ fuel, NFProg.denote fuel (.ifThenElse c thn els k) V = some W) ∧
        AVals.Ok (Fact.Below V) B W := by
    intro r W1 hW1 hr h
    obtain ⟨W, hW, hB⟩ := ite_finish S T hk hA hr h
    refine ⟨W, fun fuel => ?_, hB⟩
    rw [NFProg.denote_ifThenElse, hW1 fuel]
    exact hW fuel
  have armT : c.lookup V = true → ∀ x, run S (A.refineBit c true) thn = .ok x →
      ∃ W1 : Valuation (d := nfDialect) rs,
        (∀ fuel, (if HasBoolBit.toBool (d := nfDialect) (c.lookup V) then thn.denote fuel V
          else els.denote fuel V) = some W1) ∧ AVals.Ok (Fact.Below V) x W1 := by
    intro hb x hx
    rw [hb] at href
    obtain ⟨W1, hW1, hx1⟩ := ht _ _ _ hx href
    exact ⟨W1, fun fuel => by simp only [hb]; exact hW1 fuel, hx1⟩
  have armE : c.lookup V = false → ∀ y, run S (A.refineBit c false) els = .ok y →
      ∃ W1 : Valuation (d := nfDialect) rs,
        (∀ fuel, (if HasBoolBit.toBool (d := nfDialect) (c.lookup V) then thn.denote fuel V
          else els.denote fuel V) = some W1) ∧ AVals.Ok (Fact.Below V) y W1 := by
    intro hb y hy
    rw [hb] at href
    obtain ⟨W1, hW1, hy1⟩ := he _ _ _ hy href
    exact ⟨W1, fun fuel => by
      simp only [hb]; exact hW1 fuel, hy1⟩
  unfold run at h
  dsimp only at h
  rcases h1 : A.reach c true with _ | _ <;> rcases h2 : A.reach c false with _ | _ <;>
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  · cases hb : c.lookup V <;> rw [hb] at hreach <;> simp_all
  · obtain ⟨re, hre, h⟩ := except_bind_ok h
    obtain ⟨y, hy, rfl⟩ := except_map_ok hre
    have hb : c.lookup V = false := by
      cases hb : c.lookup V <;> simp_all
    obtain ⟨W1, hW1, hy1⟩ := armE hb y hy
    exact key y W1 hW1 hy1 h
  · obtain ⟨rt, hrt, h⟩ := except_bind_ok h
    obtain ⟨x, hx, rfl⟩ := except_map_ok hrt
    have hb : c.lookup V = true := by
      cases hb : c.lookup V <;> simp_all
    obtain ⟨W1, hW1, hx1⟩ := armT hb x hx
    exact key x W1 hW1 hx1 h
  · obtain ⟨rt, hrt, h⟩ := except_bind_ok h
    obtain ⟨x, hx, rfl⟩ := except_map_ok hrt
    obtain ⟨re, hre, h⟩ := except_bind_ok h
    obtain ⟨y, hy, rfl⟩ := except_map_ok hre
    cases hb : c.lookup V
    · obtain ⟨W1, hW1, hy1⟩ := armE hb y hy
      exact key _ W1 hW1 (AVals.ok_join_right x y W1 hy1) h
    · obtain ⟨W1, hW1, hx1⟩ := armT hb x hx
      exact key _ W1 hW1 (AVals.ok_join_left x y W1 hx1) h

/-- **The checker is sound at every program**, given the step of the counted loop. -/
theorem sound_all (S : NameSpec) (T : NfLeafTable) (hS : S.SoundAt T) (hfor : ForSound S T) :
    {Γ : Ctxt nfDialect} → {ts : List NfTy} → (p : NFProg nfDialect Γ ts) → Sound S T p
  | _, _, .ret vs => sound_ret S T vs
  | _, _, .var e k => sound_var S T hS e k (sound_all S T hS hfor k)
  | _, _, .forLoop cnt inits body k =>
    hfor cnt inits body k (sound_all S T hS hfor body) (sound_all S T hS hfor k)
  | _, _, .ifThenElse c thn els k =>
    sound_ite S T c thn els k (sound_all S T hS hfor thn) (sound_all S T hS hfor els)
      (sound_all S T hS hfor k)
  | _, _, .whileLoop _ _ _ => fun _ _ _ h => by cases h
  | _, _, .call _ _ _ => fun _ _ _ h => by cases h

/-- **Soundness of the interval checker.** When the name specification `S` is sound for the
    leaf table `T` and the step of the counted loop is sound, a program the checker accepts from
    `A` with the results `B` denotes, from every valuation in `A`, at every fuel and with the
    leaves of `T`, results `W` in `B`. -/
theorem check_sound {S : NameSpec} {T : NfLeafTable} (hS : S.SoundAt T) (hfor : ForSound S T)
    {Γ : Ctxt nfDialect} {ts : List NfTy} {A : AEnv Γ} {B : AVals ts}
    {p : NFProg nfDialect Γ ts} {V : Valuation Γ} (hc : check S A p = some B)
    (hV : A.Sat V) :
    ∃ W : Valuation (d := nfDialect) ts,
      (∀ fuel, @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V = some W) ∧
      AVals.Mem B W := by
  have hrun : run S A p = .ok B := by
    unfold check at hc
    cases hr : run S A p with
    | error e => rw [hr] at hc; cases hc
    | ok b => rw [hr] at hc; cases hc; rfl
  obtain ⟨W, hW, hB⟩ := sound_all S T hS hfor p A B V hrun ((AEnv.sat_iff A V).1 hV)
  exact ⟨W, hW, AVals.mem_of_ok hB⟩

end CatCrypt.Crypto.SecureCompilation.VIR.NFRange
