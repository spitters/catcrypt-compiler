/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16Sem

/-!
# The width-16 Poseidon2 field program computes the Poseidon2 specification

For every parameter record `P` with `1 ≤ P.sboxDeg`, the permutation program
`permComAt P i` of `Poseidon2Width16Compile` is equal to lane `i` of
`Hash.Poseidon2.Width16.permute P`. The proof follows the schedule segment by
segment in the value semantics of `Poseidon2Width16Sem`: each segment acts on the 16
state lanes as the matching specification layer (`Eff`), and the segments are
composed.

## Main definitions

* `inputState P V`: the 16-lane state read from an input valuation; lane `i` is
  entry `i` of the valuation, entry `0` being its head.

## Main results

* `externalRoundSteps_eff`, `internalRoundSteps_eff`, `externalMDSSteps_eff`:
  the round segments compute `externalRound`, `internalRound` and `externalMDS`.
* `permComAt_spec`: `(permComAt P i).denote V = permute P (inputState P V) i`.
* `permJasminAt_spec`: the lowered program, through any single-word field `F` at
  the modulus `P.p`, returns the encoding of the same lane.
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

/-! ## 1. The external MDS layer -/

/-- The lane map of the 4×4 block `b`: `mdsPre` on lanes `4b .. 4b+3`, the
    identity elsewhere. -/
def mat4Map (b : Fin 4) (x : Fin 16 → F P) : Fin 16 → F P := fun j =>
  if j.val / 4 = b.val then mdsPre x j else x j

theorem mat4Steps_eff (b : Fin 4) : Eff P (mat4Steps P b) (mat4Map b) := by
  intro σ hσ
  refine ⟨hσ, funext fun j => ?_⟩
  fin_cases b <;> fin_cases j <;>
    simp [semRun_cons, semRun_nil, mat4Steps, lanes, laneSlot, mat4Map, mdsPre, mat4,
      acc, tmp, s0, s1, s2, s3] <;> ring

theorem mat4All_eff : Eff P ((List.finRange 4).flatMap (mat4Steps P)) mdsPre := by
  refine (Eff.flatMap (mat4Steps P) mat4Map mat4Steps_eff (List.finRange 4)).congr
    fun x => ?_
  rw [show List.finRange 4 = [0, 1, 2, 3] from rfl]
  funext j
  fin_cases j <;> simp [mat4Map, mdsPre, mat4]

theorem addSteps_lanes (src : Fin 16 → Src P) (i : Fin 16) (σ : Sem P) :
    (semRun [.add (laneSlot i) (.lane (laneSlot i)) (src i)] σ).const = σ.const ∧
    ∀ j, lanes (semRun [.add (laneSlot i) (.lane (laneSlot i)) (src i)] σ) j =
      if j = i then lanes σ i + σ.get (src i) else lanes σ j := by
  refine ⟨rfl, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj; simp [semRun_cons, semRun_nil, lanes]
  · simp [semRun_cons, semRun_nil, lanes, hj, laneSlot_eq_iff]

theorem colSumSteps_eff : Eff P (colSumSteps P) colSumMap := by
  intro σ hσ
  unfold colSumSteps
  rw [semRun_append, List.map_eq_flatMap]
  set σ₁ := semRun ((List.finRange 4).flatMap fun c =>
    [ Step.add acc (.lane (laneSlot ⟨c.val, by omega⟩)) (.lane (laneSlot ⟨c.val + 4, by omega⟩)),
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
    fin_cases c <;> simp [semRun_cons, semRun_nil, laneSlot, colSlot, acc]
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

theorem externalMDSSteps_eff : Eff P (externalMDSSteps P) externalMDS :=
  (mat4All_eff.append colSumSteps_eff).congr fun _ => rfl

/-! ## 2. Rounds -/

theorem addConst_eff (r : Fin (2 * P.halfFullRounds)) :
    Eff P ((List.finRange 16).map fun i =>
        Step.add (laneSlot i) (.lane (laneSlot i)) (.const (cExt P r i)))
      (fun x i => x i + P.rcExternal r i) := by
  rw [List.map_eq_flatMap]
  refine (Eff.pointwise _ (fun i x => x + P.rcExternal r i) fun i σ hσ => ?_).congr
    fun x => rfl
  obtain ⟨c, l⟩ := addSteps_lanes (fun i => .const (cExt P r i)) i σ
  refine ⟨c, fun j => ?_⟩
  rw [l j]
  simp only [Sem.get, hσ, constVal_cExt]

theorem sboxLayer_eff (hd : 1 ≤ P.sboxDeg) :
    Eff P ((List.finRange 16).flatMap (sboxSteps P)) (fun x i => sbox P (x i)) :=
  (Eff.pointwise _ (fun _ x => sbox P x) fun i σ _ => sboxSteps_lanes hd i σ).congr
    fun _ => rfl

theorem externalRoundSteps_eff (hd : 1 ≤ P.sboxDeg) (r : Fin (2 * P.halfFullRounds)) :
    Eff P (externalRoundSteps P r) (fun x => externalRound P x (P.rcExternal r)) :=
  ((addConst_eff r).append (sboxLayer_eff hd)).append externalMDSSteps_eff |>.congr
    fun _ => rfl

theorem sumAcc_eff (σ : Sem P) :
    (semRun (Step.add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
      (List.finRange 14).map fun i => Step.add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩)))
      σ).const = σ.const ∧
    lanes (semRun (Step.add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
      (List.finRange 14).map fun i => Step.add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩)))
      σ) = lanes σ ∧
    (semRun (Step.add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
      (List.finRange 14).map fun i => Step.add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩)))
      σ).lane acc = sumAll (lanes σ) := by
  rw [show List.finRange 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from rfl]
  refine ⟨rfl, funext fun j => ?_, ?_⟩
  · simp [semRun_cons, semRun_nil, lanes]
  · simp [semRun_cons, semRun_nil, lanes, sumAll, laneSlot, acc]

theorem internalMDSSteps_eff : Eff P (internalMDSSteps P) (internalMDS P) := by
  intro σ hσ
  unfold internalMDSSteps
  rw [List.cons_append, ← List.cons_append, semRun_append]
  obtain ⟨c₁, l₁, a₁⟩ := sumAcc_eff σ
  obtain ⟨_, c₂, l₂⟩ := pointwise_flatMap
    (fun τ => τ.lane acc = sumAll (lanes σ) ∧ τ.const = constVal P)
    (fun i => [.mul tmp (.const (cDiag P i)) (.lane (laneSlot i)),
      .add (laneSlot i) (.lane acc) (.lane tmp)])
    (fun i x => sumAll (lanes σ) + P.diag i * x)
    (fun i τ hτ => by
      refine ⟨⟨?_, hτ.2⟩, rfl, fun j => ?_⟩
      · simp [semRun_cons, semRun_nil, hτ.1]
      · by_cases hj : j = i
        · subst hj
          simp [semRun_cons, semRun_nil, lanes, hτ.1, hτ.2, constVal_cDiag]
        · simp [semRun_cons, semRun_nil, lanes, hj, laneSlot_eq_iff])
    _ (List.nodup_finRange 16) _ ⟨a₁, c₁.trans hσ⟩
  refine ⟨c₂.trans (c₁.trans hσ), funext fun j => ?_⟩
  rw [l₂ j, ite_eq_left (List.mem_finRange j), l₁]
  rfl

theorem internalRoundSteps_eff (hd : 1 ≤ P.sboxDeg) (r : Fin P.partialRounds) :
    Eff P (internalRoundSteps P r) (fun x => internalRound P x (P.rcInternal r)) := by
  have head : Eff P (Step.add (laneSlot 0) (.lane (laneSlot 0)) (.const (cInt P r)) ::
      sboxSteps P 0)
      (fun x i => if i.val = 0 then sbox P (x i + P.rcInternal r) else x i) := by
    intro σ hσ
    rw [semRun_cons]
    obtain ⟨c, l⟩ := sboxSteps_lanes hd 0 (stepSem σ (.add (laneSlot 0) (.lane (laneSlot 0))
      (.const (cInt P r))))
    refine ⟨c.trans hσ, funext fun j => ?_⟩
    rw [l j]
    by_cases hj : j = 0
    · subst hj
      simp [lanes, hσ, constVal_cInt]
    · have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [lanes, hj, hj', laneSlot_eq_iff]
  exact (head.append internalMDSSteps_eff).congr fun _ => rfl

theorem copySteps_lanes (i : Fin 16) (σ : Sem P) :
    (semRun [.copy (laneSlot i) (.lane (laneSlot i))] σ).const = σ.const ∧
    ∀ j, lanes (semRun [.copy (laneSlot i) (.lane (laneSlot i))] σ) j =
      if j = i then lanes σ i else lanes σ j := by
  refine ⟨rfl, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj; simp [semRun_cons, semRun_nil, lanes]
  · simp [semRun_cons, semRun_nil, lanes, hj, laneSlot_eq_iff]

theorem outStageSteps_eff : Eff P (outStageSteps P) id := by
  unfold outStageSteps
  rw [List.map_eq_flatMap]
  exact (Eff.pointwise _ (fun _ x => x) fun i σ _ => copySteps_lanes i σ).congr fun _ => rfl

/-! ## 3. The permutation -/

theorem constSteps_semRun (l : List (Fin (nConst P))) (σ : Sem P) :
    (semRun (l.map fun j => .konst j (constVal P j)) σ).lane = σ.lane ∧
    ∀ j, (semRun (l.map fun j => .konst j (constVal P j)) σ).const j =
      if j ∈ l then constVal P j else σ.const j := by
  induction l generalizing σ with
  | nil => exact ⟨rfl, fun j => by simp [semRun_nil]⟩
  | cons j₀ l ih =>
    obtain ⟨h₁, h₂⟩ := ih (stepSem σ (.konst j₀ (constVal P j₀)))
    refine ⟨h₁, fun j => ?_⟩
    rw [List.map_cons, semRun_cons, h₂ j]
    simp only [stepSem, List.mem_cons]
    by_cases hm : j ∈ l
    · exact (ite_eq_left hm).trans (ite_eq_left (Or.inr hm)).symm
    by_cases hj : j = j₀
    · subst hj
      exact (ite_eq_right hm).trans ((ite_eq_left rfl).trans (ite_eq_left (Or.inl rfl)).symm)
    · exact (ite_eq_right hm).trans ((ite_eq_right hj).trans (ite_eq_right (by tauto)).symm)

/-- The constant bindings leave the working slots alone and put `constVal` in
    every constant slot. -/
theorem constSteps_eff (σ : Sem P) :
    (semRun (constSteps P) σ).lane = σ.lane ∧ (semRun (constSteps P) σ).const = constVal P := by
  unfold constSteps
  obtain ⟨hl, hc⟩ := constSteps_semRun (List.finRange (nConst P)) σ
  exact ⟨hl, funext fun j => (hc j).trans (ite_eq_left (List.mem_finRange j))⟩

theorem permRest_eff (hd : 1 ≤ P.sboxDeg) : Eff P (permRest P) (permute P) :=
  (externalMDSSteps_eff.append
    ((Eff.flatMap (fun r : Fin P.halfFullRounds => externalRoundSteps P ⟨r.val, by omega⟩)
      (fun r x => externalRound P x (rcInitial P r))
      (fun r => externalRoundSteps_eff hd _) _).append
    ((Eff.flatMap (internalRoundSteps P)
      (fun r x => internalRound P x (P.rcInternal r))
      (fun r => internalRoundSteps_eff hd r) _).append
    ((Eff.flatMap (fun r : Fin P.halfFullRounds =>
        externalRoundSteps P ⟨P.halfFullRounds + r.val, by omega⟩)
      (fun r x => externalRound P x (rcFinal P r))
      (fun r => externalRoundSteps_eff hd _) _).append
    outStageSteps_eff)))).congr fun _ => rfl

variable (P) in
/-- The 16-lane state read from an input valuation: lane `i` is entry `i` of
    `V : Ctxt.Valuation (inCtxt P)`, where entry `0` is the head of the valuation
    (the most recently bound input variable). -/
def inputState (V : Ctxt.Valuation (inCtxt P)) : Fin 16 → F P :=
  fun i => (inputVar 15 i.val).lookup V

/-- **The field program computes the specification.** Lane `i` of the
    `fieldDialect` permutation program, run on the valuation `V`, is lane `i` of
    `permute P` applied to the input state of `V`. -/
theorem permComAt_spec (hd : 1 ≤ P.sboxDeg) (i : Fin 16) (V : Ctxt.Valuation (inCtxt P)) :
    (permComAt P i).denote V = permute P (inputState P V) i := by
  let σ₀ : Sem P := ⟨fun k => ((initState P).lane k).lookup V,
    fun j => ((initState P).const j).lookup V⟩
  refine run_denote (permSteps P) (initState P) V σ₀ ⟨fun _ => rfl, fun _ => rfl⟩ _ _ ?_
  intro Γ' st' V' h
  change (st'.lane (laneSlot i)).lookup V' = _
  rw [h.1]
  obtain ⟨hl, hc'⟩ := constSteps_eff σ₀
  have e := congrFun ((permRest_eff hd) _ hc').2 i
  have hin : lanes (semRun (constSteps P) σ₀) = inputState P V := by
    funext k
    simp only [lanes]
    rw [show (semRun (constSteps P) σ₀).lane = σ₀.lane from hl]
    simp only [σ₀, initState, laneSlot, inputState, k.isLt, ite_eq_left]
  rw [hin] at e
  simp only [lanes] at e
  rw [permSteps, semRun_append]
  exact e

/-- **The compiled program computes the specification.** The lowered permutation
    program, run on the encoding of `V` through `F`, returns the encoding of lane `i`
    of `permute P` applied to the input state of `V`. -/
theorem permJasminAt_spec (hd : 1 ≤ P.sboxDeg) (F : SingleWordField P.p) (i : Fin 16)
    (V : Ctxt.Valuation (inCtxt P)) :
    (permJasminAt P F i).denote (mapValW F V) = F.enc (permute P (inputState P V) i) := by
  rw [permComAt_lowerK_denote, permComAt_spec hd]


end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16
