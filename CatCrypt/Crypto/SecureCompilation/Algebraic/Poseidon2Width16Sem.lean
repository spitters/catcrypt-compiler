/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16Compile

/-!
# Value semantics of the width-16 Poseidon2 step lists

A value semantics for the step lists of `Poseidon2Width16Compile`: a slot vector
holds a field value for every working and constant slot, and a step list acts on it
by `semRun`. `run_denote` relates it to the denotation of the program `run` builds.
`Eff ss f` states that `ss` maps the 16 state lanes by `f` and keeps the constant
slots at `constVal`; `Eff.append`, `Eff.flatMap` and `Eff.pointwise` compose such
statements. `powSteps_sem` is the square-and-multiply S-box chain, by induction on
the exponent.

## Main definitions

* `Sem`, `stepSem`, `semRun`: the value semantics of a step list on a slot vector.
* `Agrees`: a builder state and a slot vector agree under a valuation.
* `Eff ss f`: the step list `ss` maps the state lanes by `f` and keeps the
  constant slots at `constVal`.

## Main results

* `run_denote`: the program `run ss st k` denotes the continuation on the slot
  vector `semRun ss σ`, whenever `st` agrees with `σ` under the valuation.
* `pointwise_flatMap`, `Eff.pointwise`: lane-parallel step lists.
* `powSteps_sem`, `sboxSteps_lanes`: the S-box chain computes `x ^ n`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField)
open CatCrypt.Crypto.Hash.Poseidon2.Width16

variable {P : Params}

/-! ## 1. Value semantics of steps -/

variable (P) in
/-- A slot vector: the value of every working slot and every constant slot. -/
structure Sem where
  /-- Working slots. -/
  lane : Fin 24 → F P
  /-- Constant slots. -/
  const : Fin (nConst P) → F P

/-- The value of an operand. -/
def Sem.get (σ : Sem P) : Src P → F P
  | .lane i => σ.lane i
  | .const j => σ.const j

/-- The value semantics of one step. -/
def stepSem (σ : Sem P) : Step P → Sem P
  | .add dst a b => { σ with lane := fun i => if i = dst then σ.get a + σ.get b else σ.lane i }
  | .mul dst a b => { σ with lane := fun i => if i = dst then σ.get a * σ.get b else σ.lane i }
  | .copy dst a => { σ with lane := fun i => if i = dst then σ.get a else σ.lane i }
  | .konst j₀ c => { σ with const := fun j => if j = j₀ then c else σ.const j }

/-- The value semantics of a step list. -/
def semRun (ss : List (Step P)) (σ : Sem P) : Sem P := ss.foldl stepSem σ

theorem semRun_nil (σ : Sem P) : semRun [] σ = σ := rfl

theorem semRun_cons (s : Step P) (ss : List (Step P)) (σ : Sem P) :
    semRun (s :: ss) σ = semRun ss (stepSem σ s) := rfl

theorem semRun_append (ss ts : List (Step P)) (σ : Sem P) :
    semRun (ss ++ ts) σ = semRun ts (semRun ss σ) := List.foldl_append

@[simp] theorem Sem.get_lane (σ : Sem P) (i : Fin 24) : σ.get (.lane i) = σ.lane i := rfl

@[simp] theorem Sem.get_const (σ : Sem P) (j : Fin (nConst P)) :
    σ.get (.const j) = σ.const j := rfl

@[simp] theorem stepSem_add_lane (σ : Sem P) (d : Fin 24) (a b : Src P) (k : Fin 24) :
    (stepSem σ (.add d a b)).lane k = if k = d then σ.get a + σ.get b else σ.lane k := rfl

@[simp] theorem stepSem_mul_lane (σ : Sem P) (d : Fin 24) (a b : Src P) (k : Fin 24) :
    (stepSem σ (.mul d a b)).lane k = if k = d then σ.get a * σ.get b else σ.lane k := rfl

@[simp] theorem stepSem_copy_lane (σ : Sem P) (d : Fin 24) (a : Src P) (k : Fin 24) :
    (stepSem σ (.copy d a)).lane k = if k = d then σ.get a else σ.lane k := rfl

@[simp] theorem stepSem_add_const (σ : Sem P) (d : Fin 24) (a b : Src P) :
    (stepSem σ (.add d a b)).const = σ.const := rfl

@[simp] theorem stepSem_mul_const (σ : Sem P) (d : Fin 24) (a b : Src P) :
    (stepSem σ (.mul d a b)).const = σ.const := rfl

@[simp] theorem stepSem_copy_const (σ : Sem P) (d : Fin 24) (a : Src P) :
    (stepSem σ (.copy d a)).const = σ.const := rfl

/-- A builder state agrees with a slot vector under a valuation. -/
def Agrees {Γ : Ctxt fieldDialect} (st : BState P Γ) (V : Ctxt.Valuation Γ) (σ : Sem P) :
    Prop :=
  (∀ i, (st.lane i).lookup V = σ.lane i) ∧ (∀ j, (st.const j).lookup V = σ.const j)

theorem Agrees.get {Γ : Ctxt fieldDialect} {st : BState P Γ} {V : Ctxt.Valuation Γ}
    {σ : Sem P} (h : Agrees st V σ) (a : Src P) : (st.get a).lookup V = σ.get a := by
  cases a with
  | lane i => exact h.1 i
  | const j => exact h.2 j

theorem Agrees.after {Γ : Ctxt fieldDialect} {st : BState P Γ} {V : Ctxt.Valuation Γ}
    {σ : Sem P} (h : Agrees st V σ) (s : Step P) :
    Agrees (st.after s) (V.extend ((stepExpr st s).denote V)) (stepSem σ s) := by
  cases s with
  | add dst a b =>
    refine ⟨fun i => ?_, fun j => h.2 j⟩
    by_cases hi : i = dst
    · subst hi
      simp only [BState.after, stepSem, ite_true]
      rw [← h.get a, ← h.get b]
      rfl
    · simp only [BState.after, stepSem, hi, ite_false]
      exact h.1 i
  | mul dst a b =>
    refine ⟨fun i => ?_, fun j => h.2 j⟩
    by_cases hi : i = dst
    · subst hi
      simp only [BState.after, stepSem, ite_true]
      rw [← h.get a, ← h.get b]
      rfl
    · simp only [BState.after, stepSem, hi, ite_false]
      exact h.1 i
  | copy dst a =>
    refine ⟨fun i => ?_, fun j => h.2 j⟩
    by_cases hi : i = dst
    · subst hi
      simp only [BState.after, stepSem, ite_true]
      rw [← h.get a]
      rfl
    · simp only [BState.after, stepSem, hi, ite_false]
      exact h.1 i
  | konst j₀ c =>
    refine ⟨fun i => h.1 i, fun j => ?_⟩
    by_cases hj : j = j₀
    · subst hj
      simp only [BState.after, stepSem, ite_true]
      rfl
    · simp only [BState.after, stepSem, hj, ite_false]
      exact h.2 j

/-- **Denotation of `run`.** If `st` agrees with `σ` under `V` and the
    continuation denotes `R` on every state agreeing with `semRun ss σ`, then
    `run ss st k` denotes `R`. -/
theorem run_denote (ss : List (Step P)) {Γ : Ctxt fieldDialect} (st : BState P Γ)
    (V : Ctxt.Valuation Γ) (σ : Sem P) (h : Agrees st V σ)
    (k : {Γ' : Ctxt fieldDialect} → BState P Γ' → Com fieldDialect Γ' (FP P)) (R : F P)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (st' : BState P Γ') (V' : Ctxt.Valuation Γ'),
      Agrees st' V' (semRun ss σ) → (k st').denote V' = R) :
    (run ss st k).denote V = R := by
  induction ss generalizing Γ σ with
  | nil => exact hk st V h
  | cons s ss ih => exact ih (st.after s) _ (stepSem σ s) (h.after s) hk

/-! ## 2. Slot and constant facts -/

theorem laneSlot_eq_iff (i j : Fin 16) : laneSlot i = laneSlot j ↔ i = j := by
  simp [laneSlot, Fin.ext_iff]

theorem laneSlot_ne (i : Fin 16) (k : Fin 24) (hk : 16 ≤ k.val) : laneSlot i ≠ k := by
  intro h; have := congrArg Fin.val h; simp [laneSlot] at this; omega

@[simp] theorem laneSlot_ne_tpow (i : Fin 16) : laneSlot i ≠ tpow :=
  laneSlot_ne i tpow (by decide)
@[simp] theorem laneSlot_ne_acc (i : Fin 16) : laneSlot i ≠ acc := laneSlot_ne i acc (by decide)
@[simp] theorem laneSlot_ne_tmp (i : Fin 16) : laneSlot i ≠ tmp := laneSlot_ne i tmp (by decide)
@[simp] theorem laneSlot_ne_colSlot (i : Fin 16) (c : Fin 4) : laneSlot i ≠ colSlot c :=
  laneSlot_ne i (colSlot c) (by simp [colSlot])
@[simp] theorem acc_ne_tmp : acc ≠ tmp := by decide
@[simp] theorem tmp_ne_acc : tmp ≠ acc := by decide
@[simp] theorem tpow_ne_laneSlot (i : Fin 16) : tpow ≠ laneSlot i := (laneSlot_ne_tpow i).symm
@[simp] theorem acc_ne_laneSlot (i : Fin 16) : acc ≠ laneSlot i := (laneSlot_ne_acc i).symm
@[simp] theorem tmp_ne_laneSlot (i : Fin 16) : tmp ≠ laneSlot i := (laneSlot_ne_tmp i).symm
@[simp] theorem colSlot_ne_laneSlot (c : Fin 4) (i : Fin 16) : colSlot c ≠ laneSlot i :=
  (laneSlot_ne_colSlot i c).symm

theorem constVal_cExt (r : Fin (2 * P.halfFullRounds)) (i : Fin 16) :
    constVal P (cExt P r i) = P.rcExternal r i := by
  have hr := r.isLt
  have hi := i.isLt
  have h : (cExt P r i).val < 32 * P.halfFullRounds := by simp only [cExt]; omega
  refine (dite_eq_left h).trans ?_
  congr 1
  · apply Fin.ext; simp only [cExt]; omega
  · apply Fin.ext; simp only [cExt]; omega

theorem constVal_cInt (r : Fin P.partialRounds) : constVal P (cInt P r) = P.rcInternal r := by
  have hr := r.isLt
  have h : ¬ (cInt P r).val < 32 * P.halfFullRounds := by simp only [cInt]; omega
  have h' : (cInt P r).val < 32 * P.halfFullRounds + P.partialRounds := by
    simp only [cInt]; omega
  refine (dite_eq_right h).trans ((dite_eq_left h').trans ?_)
  exact congrArg P.rcInternal (Fin.ext (by simp only [cInt]; omega))

theorem constVal_cDiag (i : Fin 16) : constVal P (cDiag P i) = P.diag i := by
  have h : ¬ (cDiag P i).val < 32 * P.halfFullRounds := by simp only [cDiag]; omega
  have h' : ¬ (cDiag P i).val < 32 * P.halfFullRounds + P.partialRounds := by
    simp only [cDiag]; omega
  refine (dite_eq_right h).trans ((dite_eq_right h').trans ?_)
  exact congrArg P.diag (Fin.ext (by simp only [cDiag]; omega))

/-! ## 3. Lane effects -/

/-- The 16 state lanes of a slot vector. -/
def lanes (σ : Sem P) : Fin 16 → F P := fun i => σ.lane (laneSlot i)

variable (P) in
/-- `Eff ss f`: on every slot vector whose constant slots hold `constVal`, the
    step list `ss` keeps the constant slots and maps the state lanes by `f`. -/
def Eff (ss : List (Step P)) (f : (Fin 16 → F P) → Fin 16 → F P) : Prop :=
  ∀ σ : Sem P, σ.const = constVal P →
    (semRun ss σ).const = constVal P ∧ lanes (semRun ss σ) = f (lanes σ)

theorem Eff.append {ss ts : List (Step P)} {f g : (Fin 16 → F P) → Fin 16 → F P}
    (h₁ : Eff P ss f) (h₂ : Eff P ts g) : Eff P (ss ++ ts) (fun x => g (f x)) := by
  intro σ hσ
  obtain ⟨c₁, l₁⟩ := h₁ σ hσ
  obtain ⟨c₂, l₂⟩ := h₂ _ c₁
  rw [semRun_append]
  exact ⟨c₂, by rw [l₂, l₁]⟩

theorem Eff.congr {ss : List (Step P)} {f g : (Fin 16 → F P) → Fin 16 → F P}
    (h : Eff P ss f) (hfg : ∀ x, f x = g x) : Eff P ss g := by
  intro σ hσ
  obtain ⟨c, l⟩ := h σ hσ
  exact ⟨c, by rw [l, hfg]⟩

theorem Eff.flatMap {α : Type} (h : α → List (Step P))
    (G : α → (Fin 16 → F P) → Fin 16 → F P) (hG : ∀ a, Eff P (h a) (G a)) :
    ∀ l : List α, Eff P (l.flatMap h) (fun x => l.foldl (fun x a => G a x) x)
  | [] => fun σ hσ => ⟨hσ, rfl⟩
  | a :: l => by
    rw [List.flatMap_cons]
    exact ((hG a).append (Eff.flatMap h G hG l)).congr fun x => rfl

/-- **Lane-parallel step lists.** If the block `g i` preserves `Inv`, keeps the
    constant slots, maps lane `i` by `φ i` and keeps every other lane, then the
    concatenation of the blocks over a duplicate-free list `l` maps each lane in
    `l` by its `φ` and keeps the others. -/
theorem pointwise_flatMap (Inv : Sem P → Prop) (g : Fin 16 → List (Step P))
    (φ : Fin 16 → F P → F P)
    (hg : ∀ i σ, Inv σ → Inv (semRun (g i) σ) ∧ (semRun (g i) σ).const = σ.const ∧
      ∀ j, lanes (semRun (g i) σ) j = if j = i then φ i (lanes σ i) else lanes σ j) :
    ∀ (l : List (Fin 16)), l.Nodup → ∀ σ, Inv σ →
      Inv (semRun (l.flatMap g) σ) ∧ (semRun (l.flatMap g) σ).const = σ.const ∧
      ∀ j, lanes (semRun (l.flatMap g) σ) j = if j ∈ l then φ j (lanes σ j) else lanes σ j
  | [], _, σ, hσ => ⟨hσ, rfl, fun j => by simp [semRun_nil]⟩
  | i :: l, hl, σ, hσ => by
    rw [List.flatMap_cons, semRun_append]
    obtain ⟨hi, hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨inv₁, c₁, l₁⟩ := hg i σ hσ
    obtain ⟨inv₂, c₂, l₂⟩ := pointwise_flatMap Inv g φ hg l hl' _ inv₁
    refine ⟨inv₂, c₂.trans c₁, fun j => ?_⟩
    rw [l₂, l₁]
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [hj]

/-- A lane-parallel step list over all 16 lanes is an `Eff`. -/
theorem Eff.pointwise (g : Fin 16 → List (Step P)) (φ : Fin 16 → F P → F P)
    (hg : ∀ i σ, σ.const = constVal P → (semRun (g i) σ).const = σ.const ∧
      ∀ j, lanes (semRun (g i) σ) j = if j = i then φ i (lanes σ i) else lanes σ j) :
    Eff P ((List.finRange 16).flatMap g) (fun x j => φ j (x j)) := by
  intro σ hσ
  obtain ⟨_, c, l⟩ := pointwise_flatMap (fun σ => σ.const = constVal P) g φ
    (fun i σ h => ⟨(hg i σ h).1.trans h, hg i σ h⟩) _ (List.nodup_finRange 16) σ hσ
  exact ⟨c.trans hσ, funext fun j => by rw [l]; simp⟩

/-! ## 4. The S-box chain -/

/-- **The square-and-multiply chain.** For `n ≥ 1` and a base slot other than
    `tpow`, `powSteps P x n tgt` writes `x ^ n` to `tgt`, keeps the constant slots
    and every working slot other than `tpow` and `tgt`. -/
theorem powSteps_sem (x : Fin 24) (hx : x ≠ tpow) :
    ∀ (n : Nat), 1 ≤ n → ∀ (tgt : Fin 24) (σ : Sem P),
      (semRun (powSteps P x n tgt) σ).const = σ.const ∧
      (semRun (powSteps P x n tgt) σ).lane tgt = σ.lane x ^ n ∧
      ∀ k, k ≠ tpow → k ≠ tgt → (semRun (powSteps P x n tgt) σ).lane k = σ.lane k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn tgt σ
    rw [powSteps]
    split_ifs with h1 h2 h3
    · have : n = 1 := by omega
      subst this
      refine ⟨rfl, ?_, fun k _ hk => ?_⟩
      · simp [semRun_cons, semRun_nil]
      · simp [semRun_cons, semRun_nil, hk]
    · subst h2
      refine ⟨rfl, ?_, fun k _ hk => ?_⟩
      · simp [semRun_cons, semRun_nil, sq]
      · simp [semRun_cons, semRun_nil, hk]
    · obtain ⟨c, v, o⟩ := ih (n / 2) (by omega) (by omega) tpow σ
      rw [semRun_append]
      refine ⟨c, ?_, fun k hk hk' => ?_⟩
      · simp only [semRun_cons, semRun_nil, stepSem_mul_lane, ite_true, Sem.get_lane, v]
        rw [← pow_add]
        congr 1
        omega
      · simp only [semRun_cons, semRun_nil, stepSem_mul_lane, hk', ite_false]
        exact o k hk hk
    · obtain ⟨c, v, o⟩ := ih (n - 1) (by omega) (by omega) tpow σ
      rw [semRun_append]
      refine ⟨c, ?_, fun k hk hk' => ?_⟩
      · simp only [semRun_cons, semRun_nil, stepSem_mul_lane, ite_true, Sem.get_lane, v,
          o x hx hx]
        rw [← pow_succ]
        congr 1
        omega
      · simp only [semRun_cons, semRun_nil, stepSem_mul_lane, hk', ite_false]
        exact o k hk hk

theorem sboxSteps_lanes (hd : 1 ≤ P.sboxDeg) (i : Fin 16) (σ : Sem P) :
    (semRun (sboxSteps P i) σ).const = σ.const ∧
    ∀ j, lanes (semRun (sboxSteps P i) σ) j =
      if j = i then sbox P (lanes σ i) else lanes σ j := by
  obtain ⟨c, v, o⟩ := powSteps_sem (P := P) (laneSlot i) (laneSlot_ne_tpow i) _ hd
    (laneSlot i) σ
  refine ⟨c, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    simp only [lanes, ite_true]
    exact v
  · simp only [lanes, hj, ite_false]
    exact o _ (laneSlot_ne_tpow j) (by rwa [Ne, laneSlot_eq_iff])

end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16
