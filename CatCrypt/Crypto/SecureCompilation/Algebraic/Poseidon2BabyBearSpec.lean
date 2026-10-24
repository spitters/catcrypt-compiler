/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBearCompile

/-!
# The Poseidon2 BabyBear field program computes the Poseidon2 specification

The permutation program `permComAt i` of `Poseidon2BabyBearCompile` is proved
equal to lane `i` of `Hash.Poseidon2.BabyBear.poseidon2BabyBearPermute`. The proof
reads the step list `permSteps` through a value semantics on slot vectors and
follows the schedule segment by segment: each segment is shown to act on the 16
state lanes as the matching specification layer (`Eff`), and the segments are
composed. Lane-parallel segments (round constants, S-box layer, lane updates of
the MDS layers, output copies) are handled once by `pointwise_flatMap`; the
4×4 blocks, column sums and the internal accumulator are evaluated on their
own step lists.

## Main definitions

* `Sem`, `stepSem`, `semRun`: the value semantics of a step list on a slot vector.
* `Eff ss f`: the step list `ss` maps the state lanes by `f` and keeps the
  constant slots at `constVal`.
* `inputState V`: the 16-lane state read from an input valuation; lane `i` is
  entry `i` of the valuation, entry `0` being its head.

## Main results

* `run_denote`: the program `run ss st k` denotes the continuation on the slot
  vector `semRun ss σ`, whenever `st` agrees with `σ` under the valuation.
* `externalRoundSteps_eff`, `internalRoundSteps_eff`, `externalMDSSteps_eff`:
  the round segments compute `externalRound`, `internalRound` and `externalMDS`.
* `permComAt_spec`: `(permComAt i).denote V = poseidon2BabyBearPermute (inputState V) i`.
* `permJasminAt_spec`: the lowered program returns the BabyBear encoding of the
  same lane.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBear

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.BabyBear (P babyBear)
open CatCrypt.Crypto.Hash.Poseidon2.BabyBear

/-! ## 1. Value semantics of steps -/

/-- A slot vector: the value of every working slot and every constant slot. -/
structure Sem where
  /-- Working slots. -/
  lane : Fin 24 → F
  /-- Constant slots. -/
  const : Fin 157 → F

/-- The value of an operand. -/
def Sem.get (σ : Sem) : Src → F
  | .lane i => σ.lane i
  | .const j => σ.const j

/-- The value semantics of one step. -/
def stepSem (σ : Sem) : Step → Sem
  | .add dst a b => { σ with lane := fun i => if i = dst then σ.get a + σ.get b else σ.lane i }
  | .mul dst a b => { σ with lane := fun i => if i = dst then σ.get a * σ.get b else σ.lane i }
  | .copy dst a => { σ with lane := fun i => if i = dst then σ.get a else σ.lane i }
  | .konst j₀ c => { σ with const := fun j => if j = j₀ then c else σ.const j }

/-- The value semantics of a step list. -/
def semRun (ss : List Step) (σ : Sem) : Sem := ss.foldl stepSem σ

theorem semRun_nil (σ : Sem) : semRun [] σ = σ := rfl

theorem semRun_cons (s : Step) (ss : List Step) (σ : Sem) :
    semRun (s :: ss) σ = semRun ss (stepSem σ s) := rfl

theorem semRun_append (ss ts : List Step) (σ : Sem) :
    semRun (ss ++ ts) σ = semRun ts (semRun ss σ) := List.foldl_append

@[simp] theorem Sem.get_lane (σ : Sem) (i : Fin 24) : σ.get (.lane i) = σ.lane i := rfl

@[simp] theorem Sem.get_const (σ : Sem) (j : Fin 157) : σ.get (.const j) = σ.const j := rfl

@[simp] theorem stepSem_add_lane (σ : Sem) (d : Fin 24) (a b : Src) (k : Fin 24) :
    (stepSem σ (.add d a b)).lane k = if k = d then σ.get a + σ.get b else σ.lane k := rfl

@[simp] theorem stepSem_mul_lane (σ : Sem) (d : Fin 24) (a b : Src) (k : Fin 24) :
    (stepSem σ (.mul d a b)).lane k = if k = d then σ.get a * σ.get b else σ.lane k := rfl

@[simp] theorem stepSem_copy_lane (σ : Sem) (d : Fin 24) (a : Src) (k : Fin 24) :
    (stepSem σ (.copy d a)).lane k = if k = d then σ.get a else σ.lane k := rfl

@[simp] theorem stepSem_add_const (σ : Sem) (d : Fin 24) (a b : Src) :
    (stepSem σ (.add d a b)).const = σ.const := rfl

@[simp] theorem stepSem_mul_const (σ : Sem) (d : Fin 24) (a b : Src) :
    (stepSem σ (.mul d a b)).const = σ.const := rfl

@[simp] theorem stepSem_copy_const (σ : Sem) (d : Fin 24) (a : Src) :
    (stepSem σ (.copy d a)).const = σ.const := rfl

/-- A builder state agrees with a slot vector under a valuation. -/
def Agrees {Γ : Ctxt fieldDialect} (st : BState Γ) (V : Ctxt.Valuation Γ) (σ : Sem) : Prop :=
  (∀ i, (st.lane i).lookup V = σ.lane i) ∧ (∀ j, (st.const j).lookup V = σ.const j)

theorem Agrees.get {Γ : Ctxt fieldDialect} {st : BState Γ} {V : Ctxt.Valuation Γ} {σ : Sem}
    (h : Agrees st V σ) (a : Src) : (st.get a).lookup V = σ.get a := by
  cases a with
  | lane i => exact h.1 i
  | const j => exact h.2 j

theorem Agrees.after {Γ : Ctxt fieldDialect} {st : BState Γ} {V : Ctxt.Valuation Γ} {σ : Sem}
    (h : Agrees st V σ) (s : Step) :
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
theorem run_denote (ss : List Step) {Γ : Ctxt fieldDialect} (st : BState Γ)
    (V : Ctxt.Valuation Γ) (σ : Sem) (h : Agrees st V σ)
    (k : {Γ' : Ctxt fieldDialect} → BState Γ' → Com fieldDialect Γ' FP) (R : F)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (st' : BState Γ') (V' : Ctxt.Valuation Γ'),
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

@[simp] theorem laneSlot_ne_t2 (i : Fin 16) : laneSlot i ≠ t2 := laneSlot_ne i t2 (by decide)
@[simp] theorem laneSlot_ne_t4 (i : Fin 16) : laneSlot i ≠ t4 := laneSlot_ne i t4 (by decide)
@[simp] theorem laneSlot_ne_acc (i : Fin 16) : laneSlot i ≠ acc := laneSlot_ne i acc (by decide)
@[simp] theorem laneSlot_ne_tmp (i : Fin 16) : laneSlot i ≠ tmp := laneSlot_ne i tmp (by decide)
@[simp] theorem laneSlot_ne_colSlot (i : Fin 16) (c : Fin 4) : laneSlot i ≠ colSlot c :=
  laneSlot_ne i (colSlot c) (by simp [colSlot])
@[simp] theorem t2_ne_t4 : t2 ≠ t4 := by decide
@[simp] theorem t4_ne_t2 : t4 ≠ t2 := by decide
@[simp] theorem acc_ne_tmp : acc ≠ tmp := by decide
@[simp] theorem tmp_ne_acc : tmp ≠ acc := by decide
@[simp] theorem t2_ne_laneSlot (i : Fin 16) : t2 ≠ laneSlot i := (laneSlot_ne_t2 i).symm
@[simp] theorem t4_ne_laneSlot (i : Fin 16) : t4 ≠ laneSlot i := (laneSlot_ne_t4 i).symm
@[simp] theorem acc_ne_laneSlot (i : Fin 16) : acc ≠ laneSlot i := (laneSlot_ne_acc i).symm
@[simp] theorem tmp_ne_laneSlot (i : Fin 16) : tmp ≠ laneSlot i := (laneSlot_ne_tmp i).symm
@[simp] theorem colSlot_ne_laneSlot (c : Fin 4) (i : Fin 16) : colSlot c ≠ laneSlot i :=
  (laneSlot_ne_colSlot i c).symm

theorem constVal_cExt (r : Fin 8) (i : Fin 16) :
    constVal (cExt r i) = fullRoundConstants r i := by
  have h : (cExt r i).val < 128 := by simp [cExt]; omega
  refine (dite_eq_left h).trans ?_
  have hi : i.val < 16 := i.isLt
  have hr : r.val < 8 := r.isLt
  congr 1
  · apply Fin.ext; simp only [cExt]; omega
  · apply Fin.ext; simp only [cExt]; omega

theorem constVal_cInt (r : Fin 13) : constVal (cInt r) = partialRoundConstants r := by
  have h : ¬ (cInt r).val < 128 := by simp [cInt]
  have h' : (cInt r).val < 141 := by simp [cInt]; omega
  refine (dite_eq_right h).trans ((dite_eq_left h').trans ?_)
  exact congrArg partialRoundConstants (Fin.ext (by simp [cInt]))

theorem constVal_cDiag (i : Fin 16) : constVal (cDiag i) = diagV i := by
  have h : ¬ (cDiag i).val < 128 := by simp [cDiag]; omega
  have h' : ¬ (cDiag i).val < 141 := by simp [cDiag]
  refine (dite_eq_right h).trans ((dite_eq_right h').trans ?_)
  exact congrArg diagV (Fin.ext (by simp [cDiag]))

/-! ## 3. Lane effects -/

/-- The 16 state lanes of a slot vector. -/
def lanes (σ : Sem) : Fin width → F := fun i => σ.lane (laneSlot i)

/-- `Eff ss f`: on every slot vector whose constant slots hold `constVal`, the
    step list `ss` keeps the constant slots and maps the state lanes by `f`. -/
def Eff (ss : List Step) (f : (Fin width → F) → Fin width → F) : Prop :=
  ∀ σ : Sem, σ.const = constVal →
    (semRun ss σ).const = constVal ∧ lanes (semRun ss σ) = f (lanes σ)

theorem Eff.append {ss ts : List Step} {f g : (Fin width → F) → Fin width → F}
    (h₁ : Eff ss f) (h₂ : Eff ts g) : Eff (ss ++ ts) (fun x => g (f x)) := by
  intro σ hσ
  obtain ⟨c₁, l₁⟩ := h₁ σ hσ
  obtain ⟨c₂, l₂⟩ := h₂ _ c₁
  rw [semRun_append]
  exact ⟨c₂, by rw [l₂, l₁]⟩

theorem Eff.congr {ss : List Step} {f g : (Fin width → F) → Fin width → F}
    (h : Eff ss f) (hfg : ∀ x, f x = g x) : Eff ss g := by
  intro σ hσ
  obtain ⟨c, l⟩ := h σ hσ
  exact ⟨c, by rw [l, hfg]⟩

theorem Eff.flatMap {α : Type} (h : α → List Step)
    (G : α → (Fin width → F) → Fin width → F) (hG : ∀ a, Eff (h a) (G a)) :
    ∀ l : List α, Eff (l.flatMap h) (fun x => l.foldl (fun x a => G a x) x)
  | [] => fun σ hσ => ⟨hσ, rfl⟩
  | a :: l => by
    rw [List.flatMap_cons]
    exact ((hG a).append (Eff.flatMap h G hG l)).congr fun x => rfl

/-- **Lane-parallel step lists.** If the block `g i` preserves `Inv`, keeps the
    constant slots, maps lane `i` by `φ i` and keeps every other lane, then the
    concatenation of the blocks over a duplicate-free list `l` maps each lane in
    `l` by its `φ` and keeps the others. -/
theorem pointwise_flatMap (Inv : Sem → Prop) (g : Fin 16 → List Step)
    (φ : Fin 16 → F → F)
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
theorem Eff.pointwise (g : Fin 16 → List Step) (φ : Fin 16 → F → F)
    (hg : ∀ i σ, σ.const = constVal → (semRun (g i) σ).const = σ.const ∧
      ∀ j, lanes (semRun (g i) σ) j = if j = i then φ i (lanes σ i) else lanes σ j) :
    Eff ((List.finRange 16).flatMap g) (fun x j => φ j (x j)) := by
  intro σ hσ
  obtain ⟨_, c, l⟩ := pointwise_flatMap (fun σ => σ.const = constVal) g φ
    (fun i σ h => ⟨(hg i σ h).1.trans h, hg i σ h⟩) _ (List.nodup_finRange 16) σ hσ
  exact ⟨c.trans hσ, funext fun j => by rw [l]; simp⟩

/-! ## 4. Per-lane blocks -/

theorem sboxSteps_lanes (i : Fin 16) (σ : Sem) :
    (semRun (sboxSteps (laneSlot i) (laneSlot i)) σ).const = σ.const ∧
    ∀ j, lanes (semRun (sboxSteps (laneSlot i) (laneSlot i)) σ) j =
      if j = i then sbox (lanes σ i) else lanes σ j := by
  refine ⟨rfl, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    simp [semRun_cons, semRun_nil, sboxSteps,Sem.get, lanes, sbox]
  · simp [semRun_cons, semRun_nil, sboxSteps, lanes, hj, laneSlot_eq_iff]

theorem addSteps_lanes (src : Fin 16 → Src) (i : Fin 16) (σ : Sem) :
    (semRun [.add (laneSlot i) (.lane (laneSlot i)) (src i)] σ).const = σ.const ∧
    ∀ j, lanes (semRun [.add (laneSlot i) (.lane (laneSlot i)) (src i)] σ) j =
      if j = i then lanes σ i + σ.get (src i) else lanes σ j := by
  refine ⟨rfl, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj; simp [semRun_cons, semRun_nil, Sem.get, lanes]
  · simp [semRun_cons, semRun_nil, lanes, hj, laneSlot_eq_iff]

theorem copySteps_lanes (i : Fin 16) (σ : Sem) :
    (semRun [.copy (laneSlot i) (.lane (laneSlot i))] σ).const = σ.const ∧
    ∀ j, lanes (semRun [.copy (laneSlot i) (.lane (laneSlot i))] σ) j =
      if j = i then lanes σ i else lanes σ j := by
  refine ⟨rfl, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj; simp [semRun_cons, semRun_nil, Sem.get, lanes]
  · simp [semRun_cons, semRun_nil, lanes, hj, laneSlot_eq_iff]

/-- The lane map of the 4×4 block `b`: `applyMat4` on lanes `4b .. 4b+3`, the
    identity elsewhere. -/
def mat4Map (b : Fin 4) (x : Fin width → F) : Fin width → F := fun j =>
  if j.val / 4 = b.val then applyMat4 (block4 x b) ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩
  else x j

theorem mat4Steps_eff_0 : Eff (mat4Steps 0) (mat4Map 0) := by
  intro σ hσ
  refine ⟨hσ, funext fun j => ?_⟩
  fin_cases j <;>
    simp [semRun_cons, semRun_nil, mat4Steps,Sem.get, lanes, laneSlot, mat4Map,
      applyMat4, block4, acc, tmp, s0, s1, s2, s3] <;> ring

theorem mat4Steps_eff_1 : Eff (mat4Steps 1) (mat4Map 1) := by
  intro σ hσ
  refine ⟨hσ, funext fun j => ?_⟩
  fin_cases j <;>
    simp [semRun_cons, semRun_nil, mat4Steps,Sem.get, lanes, laneSlot, mat4Map,
      applyMat4, block4, acc, tmp, s0, s1, s2, s3] <;> ring

theorem mat4Steps_eff_2 : Eff (mat4Steps 2) (mat4Map 2) := by
  intro σ hσ
  refine ⟨hσ, funext fun j => ?_⟩
  fin_cases j <;>
    simp [semRun_cons, semRun_nil, mat4Steps,Sem.get, lanes, laneSlot, mat4Map,
      applyMat4, block4, acc, tmp, s0, s1, s2, s3] <;> ring

theorem mat4Steps_eff_3 : Eff (mat4Steps 3) (mat4Map 3) := by
  intro σ hσ
  refine ⟨hσ, funext fun j => ?_⟩
  fin_cases j <;>
    simp [semRun_cons, semRun_nil, mat4Steps,Sem.get, lanes, laneSlot, mat4Map,
      applyMat4, block4, acc, tmp, s0, s1, s2, s3] <;> ring

/-! ## 5. Layers -/

/-- The four 4×4 blocks applied to the input state, lane by lane. -/
def mdsPre (x : Fin width → F) : Fin width → F := fun i =>
  applyMat4 (block4 x ⟨i.val / 4, by have := i.isLt; unfold width at this; omega⟩)
    ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- Lane `i` plus the sum of the four lanes congruent to `i` modulo 4. -/
def colSumMap (s : Fin width → F) : Fin width → F := fun i =>
  let inB : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  s i + (s ⟨inB.val, by have := inB.isLt; unfold width; omega⟩ +
    s ⟨inB.val + 4, by have := inB.isLt; unfold width; omega⟩ +
    s ⟨inB.val + 8, by have := inB.isLt; unfold width; omega⟩ +
    s ⟨inB.val + 12, by have := inB.isLt; unfold width; omega⟩)

theorem externalMDS_eq (x : Fin width → F) : externalMDS x = colSumMap (mdsPre x) := rfl

theorem mat4All_eff :
    Eff ((List.finRange 4).flatMap mat4Steps) (fun x => mdsPre x) := by
  refine (Eff.flatMap mat4Steps mat4Map (fun b => ?_) (List.finRange 4)).congr fun x => ?_
  · fin_cases b
    · exact mat4Steps_eff_0
    · exact mat4Steps_eff_1
    · exact mat4Steps_eff_2
    · exact mat4Steps_eff_3
  · rw [show List.finRange 4 = [0, 1, 2, 3] from rfl]
    funext j
    fin_cases j <;> simp [mat4Map, mdsPre, block4, applyMat4]

theorem colSumSteps_eff : Eff colSumSteps colSumMap := by
  intro σ hσ
  unfold colSumSteps
  rw [semRun_append, List.map_eq_flatMap]
  set σ₁ := semRun ((List.finRange 4).flatMap fun c =>
    [ .add acc (.lane (laneSlot ⟨c.val, by omega⟩)) (.lane (laneSlot ⟨c.val + 4, by omega⟩)),
      .add acc (.lane acc) (.lane (laneSlot ⟨c.val + 8, by omega⟩)),
      .add (colSlot c) (.lane acc) (.lane (laneSlot ⟨c.val + 12, by omega⟩)) ]) σ with hσ₁
  have c₁ : σ₁.const = σ.const := by
    rw [hσ₁, show List.finRange 4 = [0, 1, 2, 3] from rfl]; rfl
  have l₁ : lanes σ₁ = lanes σ := by
    rw [hσ₁, show List.finRange 4 = [0, 1, 2, 3] from rfl]
    funext j
    simp [semRun_cons, semRun_nil, lanes]
  have s₁ : ∀ c : Fin 4, σ₁.lane (colSlot c) =
      σ.lane (laneSlot ⟨c.val, by omega⟩) + σ.lane (laneSlot ⟨c.val + 4, by omega⟩) +
        σ.lane (laneSlot ⟨c.val + 8, by omega⟩) + σ.lane (laneSlot ⟨c.val + 12, by omega⟩) := by
    rw [hσ₁, show List.finRange 4 = [0, 1, 2, 3] from rfl]
    intro c
    fin_cases c <;> simp [semRun_cons, semRun_nil, Sem.get, laneSlot, colSlot, acc]
  obtain ⟨_, c₂, l₂⟩ := pointwise_flatMap
    (fun τ => ∀ c : Fin 4, τ.lane (colSlot c) = σ₁.lane (colSlot c))
    (fun i => [.add (laneSlot i) (.lane (laneSlot i)) (.lane (colSlot ⟨i.val % 4, by omega⟩))])
    (fun i x => x + σ₁.lane (colSlot ⟨i.val % 4, by omega⟩))
    (fun i τ hτ => by
      obtain ⟨c, l⟩ := addSteps_lanes (fun i => .lane (colSlot ⟨i.val % 4, by omega⟩)) i τ
      refine ⟨fun c' => ?_, c, fun j => ?_⟩
      · rw [← hτ c']
        simp [semRun_cons, semRun_nil]
      · rw [l j]
        simp only [Sem.get, hτ])
    _ (List.nodup_finRange 16) σ₁ (fun _ => rfl)
  refine ⟨c₂.trans (c₁.trans hσ), funext fun j => ?_⟩
  rw [l₂ j, ite_eq_left (List.mem_finRange j), s₁, l₁]
  rfl

theorem externalMDSSteps_eff : Eff externalMDSSteps externalMDS :=
  (mat4All_eff.append colSumSteps_eff).congr fun x => (externalMDS_eq x).symm

theorem addConst_eff (r : Fin 8) :
    Eff ((List.finRange 16).map fun i => Step.add (laneSlot i) (.lane (laneSlot i)) (.const (cExt r i)))
      (fun x => addRoundConstants x (fullRoundConstants r)) := by
  rw [List.map_eq_flatMap]
  refine (Eff.pointwise _ (fun i x => x + fullRoundConstants r i) fun i σ hσ => ?_).congr
    fun x => rfl
  obtain ⟨c, l⟩ := addSteps_lanes (fun i => .const (cExt r i)) i σ
  refine ⟨c, fun j => ?_⟩
  rw [l j]
  simp only [Sem.get, hσ, constVal_cExt]

theorem sboxLayer_eff :
    Eff ((List.finRange 16).flatMap fun i => sboxSteps (laneSlot i) (laneSlot i)) sboxLayer :=
  (Eff.pointwise _ (fun _ x => sbox x) fun i σ _ => sboxSteps_lanes i σ).congr fun _ => rfl

theorem externalRoundSteps_eff (r : Fin 8) :
    Eff (externalRoundSteps r) (fun x => externalRound x (fullRoundConstants r)) :=
  ((addConst_eff r).append sboxLayer_eff).append externalMDSSteps_eff |>.congr fun _ => rfl

theorem sumAcc_eff (σ : Sem) :
    (semRun (.add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
      (List.finRange 14).map fun i => .add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩)))
      σ).const = σ.const ∧
    lanes (semRun (.add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
      (List.finRange 14).map fun i => .add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩)))
      σ) = lanes σ ∧
    (semRun (.add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
      (List.finRange 14).map fun i => .add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩)))
      σ).lane acc = sumAll (lanes σ) := by
  rw [show List.finRange 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from rfl]
  refine ⟨rfl, funext fun j => ?_, ?_⟩
  · simp [semRun_cons, semRun_nil, lanes]
  · simp [semRun_cons, semRun_nil, Sem.get, lanes, sumAll, laneSlot, acc]

theorem internalMDSSteps_eff : Eff internalMDSSteps internalMDS := by
  intro σ hσ
  unfold internalMDSSteps
  rw [List.cons_append, ← List.cons_append, semRun_append]
  obtain ⟨c₁, l₁, a₁⟩ := sumAcc_eff σ
  obtain ⟨_, c₂, l₂⟩ := pointwise_flatMap
    (fun τ => τ.lane acc = sumAll (lanes σ) ∧ τ.const = constVal)
    (fun i => [.mul tmp (.const (cDiag i)) (.lane (laneSlot i)),
      .add (laneSlot i) (.lane acc) (.lane tmp)])
    (fun i x => sumAll (lanes σ) + diagV i * x)
    (fun i τ hτ => by
      refine ⟨⟨?_, hτ.2⟩, rfl, fun j => ?_⟩
      · simp [semRun_cons, semRun_nil, hτ.1]
      · by_cases hj : j = i
        · subst hj
          simp [semRun_cons, semRun_nil, Sem.get, lanes, hτ.1, hτ.2, constVal_cDiag]
        · simp [semRun_cons, semRun_nil, lanes, hj, laneSlot_eq_iff])
    _ (List.nodup_finRange 16) _ ⟨a₁, c₁.trans hσ⟩
  refine ⟨c₂.trans (c₁.trans hσ), funext fun j => ?_⟩
  rw [l₂ j, ite_eq_left (List.mem_finRange j), l₁]
  rfl

theorem internalRoundSteps_eff (r : Fin 13) :
    Eff (internalRoundSteps r) (fun x => internalRound x (partialRoundConstants r)) := by
  have head : Eff (.add (laneSlot 0) (.lane (laneSlot 0)) (.const (cInt r)) ::
      sboxSteps (laneSlot 0) (laneSlot 0))
      (fun x => sboxLane0 (fun i => if i.val = 0 then x i + partialRoundConstants r else x i)) := by
    intro σ hσ
    rw [semRun_cons]
    obtain ⟨c, l⟩ := sboxSteps_lanes 0 (stepSem σ (.add (laneSlot 0) (.lane (laneSlot 0))
      (.const (cInt r))))
    refine ⟨c.trans hσ, funext fun j => ?_⟩
    rw [l j]
    by_cases hj : j = 0
    · subst hj
      simp [lanes, sboxLane0, hσ, constVal_cInt]
    · have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [lanes, sboxLane0, hj, hj', laneSlot_eq_iff]
  exact (head.append internalMDSSteps_eff).congr fun _ => rfl

theorem outStageSteps_eff : Eff outStageSteps id := by
  unfold outStageSteps
  rw [List.map_eq_flatMap]
  exact (Eff.pointwise _ (fun _ x => x) fun i σ _ => copySteps_lanes i σ).congr fun _ => rfl

theorem constSteps_semRun (l : List (Fin 157)) (σ : Sem) :
    (semRun (l.map fun j => .konst j (constVal j)) σ).lane = σ.lane ∧
    ∀ j, (semRun (l.map fun j => .konst j (constVal j)) σ).const j =
      if j ∈ l then constVal j else σ.const j := by
  induction l generalizing σ with
  | nil => exact ⟨rfl, fun j => by simp [semRun_nil]⟩
  | cons j₀ l ih =>
    obtain ⟨h₁, h₂⟩ := ih (stepSem σ (.konst j₀ (constVal j₀)))
    refine ⟨h₁, fun j => ?_⟩
    rw [List.map_cons, semRun_cons, h₂ j]
    simp only [stepSem, List.mem_cons]
    by_cases hm : j ∈ l
    · exact (ite_eq_left hm).trans (ite_eq_left (Or.inr hm)).symm
    by_cases hj : j = j₀
    · subst hj
      exact (ite_eq_right hm).trans ((ite_eq_left rfl).trans (ite_eq_left (Or.inl rfl)).symm)
    · exact (ite_eq_right hm).trans ((ite_eq_right hj).trans (ite_eq_right (by tauto)).symm)

/-! ## 6. The permutation -/

/-- The schedule after the constant bindings: the external MDS pre-mix, four
    external rounds, thirteen internal rounds, four external rounds and the
    output copies. -/
def permRest : List Step :=
  externalMDSSteps ++
    ((List.finRange 4).flatMap (fun r => externalRoundSteps ⟨r.val, by omega⟩) ++
    ((List.finRange 13).flatMap internalRoundSteps ++
    ((List.finRange 4).flatMap (fun r => externalRoundSteps ⟨r.val + 4, by omega⟩) ++
    outStageSteps)))

theorem permSteps_eq : permSteps = constSteps ++ permRest := by
  simp only [permSteps, permRest, List.append_assoc]

/-- The constant bindings leave the working slots alone and put `constVal` in
    every constant slot. -/
theorem constSteps_eff (σ : Sem) :
    (semRun constSteps σ).lane = σ.lane ∧ (semRun constSteps σ).const = constVal := by
  unfold constSteps
  obtain ⟨hl, hc⟩ := constSteps_semRun (List.finRange 157) σ
  exact ⟨hl, funext fun j => (hc j).trans (ite_eq_left (List.mem_finRange j))⟩

theorem applyExternalPrefix_eq_foldl (x : Fin width → F) :
    applyExternalPrefix halfFullRounds (by decide) x =
      (List.finRange 4).foldl (fun x (r : Fin 4) =>
        externalRound x (fullRoundConstants ⟨r.val, by unfold fullRounds; omega⟩)) x := rfl

/-- The first `n` internal rounds. -/
def partialIter (n : Nat) (x : Fin width → F) : Fin width → F :=
  Nat.rec (motive := fun _ => Fin width → F) x
    (fun k acc => if hk : k < partialRounds then
      internalRound acc (partialRoundConstants ⟨k, hk⟩) else acc) n

theorem applyAllPartialRounds_eq_foldl (x : Fin width → F) :
    applyAllPartialRounds x =
      (List.finRange 13).foldl (fun (x : Fin width → F) (r : Fin 13) =>
        internalRound x (partialRoundConstants r)) x := by
  rw [show List.finRange 13 = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List (Fin 13)) from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  show partialIter 13 x = _
  rw [show partialIter 13 x
        = internalRound (partialIter 12 x) (partialRoundConstants ⟨12, by decide⟩) from rfl,
    show partialIter 12 x
        = internalRound (partialIter 11 x) (partialRoundConstants ⟨11, by decide⟩) from rfl,
    show partialIter 11 x
        = internalRound (partialIter 10 x) (partialRoundConstants ⟨10, by decide⟩) from rfl,
    show partialIter 10 x
        = internalRound (partialIter 9 x) (partialRoundConstants ⟨9, by decide⟩) from rfl,
    show partialIter 9 x
        = internalRound (partialIter 8 x) (partialRoundConstants ⟨8, by decide⟩) from rfl,
    show partialIter 8 x
        = internalRound (partialIter 7 x) (partialRoundConstants ⟨7, by decide⟩) from rfl,
    show partialIter 7 x
        = internalRound (partialIter 6 x) (partialRoundConstants ⟨6, by decide⟩) from rfl,
    show partialIter 6 x
        = internalRound (partialIter 5 x) (partialRoundConstants ⟨5, by decide⟩) from rfl,
    show partialIter 5 x
        = internalRound (partialIter 4 x) (partialRoundConstants ⟨4, by decide⟩) from rfl,
    show partialIter 4 x
        = internalRound (partialIter 3 x) (partialRoundConstants ⟨3, by decide⟩) from rfl,
    show partialIter 3 x
        = internalRound (partialIter 2 x) (partialRoundConstants ⟨2, by decide⟩) from rfl,
    show partialIter 2 x
        = internalRound (partialIter 1 x) (partialRoundConstants ⟨1, by decide⟩) from rfl,
    show partialIter 1 x
        = internalRound (partialIter 0 x) (partialRoundConstants ⟨0, by decide⟩) from rfl]
  rfl

theorem applyExternalSuffix_eq_foldl (x : Fin width → F) :
    applyExternalSuffix x =
      (List.finRange 4).foldl (fun x (r : Fin 4) =>
        externalRound x (fullRoundConstants ⟨r.val + 4, by unfold fullRounds; omega⟩)) x := rfl

theorem permRest_eff : Eff permRest poseidon2BabyBearPermute := by
  refine (externalMDSSteps_eff.append
    ((Eff.flatMap (fun r : Fin 4 => externalRoundSteps ⟨r.val, by omega⟩)
      (fun r x => externalRound x (fullRoundConstants ⟨r.val, by unfold fullRounds; omega⟩))
      (fun r => externalRoundSteps_eff _) _).append
    ((Eff.flatMap internalRoundSteps
      (fun r x => internalRound x (partialRoundConstants r))
      (fun r => internalRoundSteps_eff r) _).append
    ((Eff.flatMap (fun r : Fin 4 => externalRoundSteps ⟨r.val + 4, by omega⟩)
      (fun r x => externalRound x
        (fullRoundConstants ⟨r.val + 4, by unfold fullRounds; omega⟩))
      (fun r => externalRoundSteps_eff _) _).append
    outStageSteps_eff)))).congr fun x => ?_
  simp only [poseidon2BabyBearPermute, applyExternalPrefix_eq_foldl,
    applyAllPartialRounds_eq_foldl, applyExternalSuffix_eq_foldl, id]

/-- The 16-lane state read from an input valuation: lane `i` is entry `i` of
    `V : Ctxt.Valuation inCtxt`, where entry `0` is the head of the valuation
    (the most recently bound input variable). -/
def inputState (V : Ctxt.Valuation inCtxt) : Fin width → F :=
  fun i => (inputVar 15 i.val).lookup V

/-- **The field program computes the specification.** Lane `i` of the
    `fieldDialect` permutation program, run on the valuation `V`, is lane `i` of
    `poseidon2BabyBearPermute` applied to the input state of `V`. -/
theorem permComAt_spec (i : Fin 16) (V : Ctxt.Valuation inCtxt) :
    (permComAt i).denote V = poseidon2BabyBearPermute (inputState V) i := by
  let σ₀ : Sem := ⟨fun k => (initState.lane k).lookup V, fun j => (initState.const j).lookup V⟩
  refine run_denote permSteps initState V σ₀ ⟨fun _ => rfl, fun _ => rfl⟩ _ _ ?_
  intro Γ' st' V' h
  change (st'.lane (laneSlot i)).lookup V' = _
  rw [h.1]
  obtain ⟨hl, hc'⟩ := constSteps_eff σ₀
  have e := congrFun (permRest_eff _ hc').2 i
  have hin : lanes (semRun constSteps σ₀) = inputState V := by
    funext k
    simp only [lanes]
    rw [show (semRun constSteps σ₀).lane = σ₀.lane from hl]
    simp only [σ₀, initState, laneSlot, inputState, k.isLt, ite_eq_left]
    rfl
  rw [hin] at e
  simp only [lanes] at e
  rw [permSteps_eq, semRun_append]
  exact e

/-- **The compiled program computes the specification.** The lowered
    permutation program, run on the BabyBear encoding of `V`, returns the
    encoding of lane `i` of `poseidon2BabyBearPermute` applied to the input state
    of `V`. -/
theorem permJasminAt_spec (i : Fin 16) (V : Ctxt.Valuation inCtxt) :
    (permJasminAt i).denote (mapValW babyBear V) =
      babyBear.enc (poseidon2BabyBearPermute (inputState V) i) := by
  rw [permComAt_lowerK_denote, permComAt_spec]

end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBear
