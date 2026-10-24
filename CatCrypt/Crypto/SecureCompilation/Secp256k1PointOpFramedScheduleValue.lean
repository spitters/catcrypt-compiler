/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedBrickValue

/-!
# The framed doubling body's frame-slot value, folded over the schedule

`Secp256k1PointOpFramedBrickValue` moves one `emitFOpFramed` brick's output frame
slot by one base-field operation. This module folds that single-brick step over a
whole schedule and ties the fold to `jacDblBodyFramed`.

`stepFramed` and `scheduleEvalFramed` are the slot-indexed analogues of
`Secp256k1PointOpCompositional.stepFOpG` / `scheduleEvalG`: they update a
`Nat → Nat` slot valuation with the `fm` / `fa` / `fs` base-field operation at the
output slot of each op. `brickFoldFramed` runs a `Forall₂`-generic list of framed
bricks and re-establishes both the frame-slot invariant `FrameSlots` and the
operand-range invariant `_ < pNat` at every step. `jacDblBodyFramed_cells`
instantiates it at `jacDblSchedule`.

## Main results

* `stepFramed`, `scheduleEvalFramed` — the slot-valuation step and its fold.
* `brickFoldFramed` — a `Forall₂`-generic list of framed bricks lands
  `FrameSlots` at `scheduleEvalFramed` and preserves the operand-range bound.
* `jacDblBodyFramed_cells` — running `jacDblBodyFramed` over a frame satisfying
  `FrameSlots arr V active` (with the active slots bounded `< pNat` and the
  schedule's slots in scope) lands `FrameSlots fr (scheduleEvalFramed slotOfDbl
  jacDblSchedule V) active`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedScheduleValue

open CatCrypt.Crypto.Jasmin.LowCT (LowCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll pNat)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront (FOp fm fa fs jacDblSchedule jacDblSpec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote (semScalar_seqAll_append)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedCells (FrameSlots slotVal)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
  (emitFOpFramed jacDblBodyFramed slotOfDbl frameCells dblNames)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional
  (scheduleEvalG stepFOpG envUpd jacDblSpecG dblEnv0 jacDblSchedule_realizes_spec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedBrickValue
  (emitFOpFramed_mul_value emitFOpFramed_add_value emitFOpFramed_sub_value)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue (pNat_pos)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered (notTmp_of_len)

/-! ## 1. The slot-indexed valuation step and fold -/

/-- One field-op's effect on a frame-slot valuation: update the output slot to the
    matching base-field operation on the two operand slot values. The slot analogue
    of `Secp256k1PointOpCompositional.stepFOpG` at `fm` / `fa` / `fs`. -/
def stepFramed (slotOf : String → Nat) (V : Nat → Nat) : FOp → (Nat → Nat)
  | .mul o a b => Function.update V (slotOf o) (fm (V (slotOf a)) (V (slotOf b)))
  | .add o a b => Function.update V (slotOf o) (fa (V (slotOf a)) (V (slotOf b)))
  | .sub o a b => Function.update V (slotOf o) (fs (V (slotOf a)) (V (slotOf b)))

/-- Fold `stepFramed` over a schedule: the frame-slot valuation each slot ends
    holding after the whole framed body runs. -/
def scheduleEvalFramed (slotOf : String → Nat) (ops : List FOp) (V : Nat → Nat) : Nat → Nat :=
  ops.foldl (stepFramed slotOf) V

/-- The static per-op side-conditions the single-brick value lemmas need: both
    operand slots are in the active window, both operand slots and the output slot
    address inside the physical frame. -/
def FramedOpOk (fw active : Nat) (slotOf : String → Nat) : FOp → Prop
  | .mul o a b | .add o a b | .sub o a b =>
      slotOf a < active ∧ slotOf b < active ∧
      4 * slotOf a + 4 ≤ 2 ^ 64 ∧ 4 * slotOf b + 4 ≤ 2 ^ 64 ∧
      4 * slotOf o + 4 ≤ (fw + 7) / 8

instance (fw active : Nat) (slotOf : String → Nat) : DecidablePred (FramedOpOk fw active slotOf) :=
  fun op => by cases op <;> unfold FramedOpOk <;> infer_instance

/-! ## 2. Base-field operations stay below the prime -/

/-- `fm a b < pNat`. -/
theorem fm_lt_pNat (a b : Nat) : fm a b < pNat := Nat.mod_lt _ pNat_pos

/-- `fa a b < pNat`. -/
theorem fa_lt_pNat (a b : Nat) : fa a b < pNat := Nat.mod_lt _ pNat_pos

/-- `fs a b < pNat`. -/
theorem fs_lt_pNat (a b : Nat) : fs a b < pNat := Nat.mod_lt _ pNat_pos

/-- One `stepFramed` preserves the operand-range invariant: if every active slot
    of `V` is below the prime, so is every active slot of the stepped valuation. -/
theorem stepFramed_lt {slotOf : String → Nat} {V : Nat → Nat} {active : Nat}
    (op : FOp) (hVlt : ∀ s, s < active → V s < pNat) :
    ∀ s, s < active → stepFramed slotOf V op s < pNat := by
  intro s hs
  cases op with
  | mul o a b =>
      simp only [stepFramed]
      by_cases ho : s = slotOf o
      · subst ho; rw [Function.update_self]; exact fm_lt_pNat _ _
      · rw [Function.update_of_ne ho]; exact hVlt s hs
  | add o a b =>
      simp only [stepFramed]
      by_cases ho : s = slotOf o
      · subst ho; rw [Function.update_self]; exact fa_lt_pNat _ _
      · rw [Function.update_of_ne ho]; exact hVlt s hs
  | sub o a b =>
      simp only [stepFramed]
      by_cases ho : s = slotOf o
      · subst ho; rw [Function.update_self]; exact fs_lt_pNat _ _
      · rw [Function.update_of_ne ho]; exact hVlt s hs

/-! ## 3. `Forall₂` from `mapIdx` for the framed emitter -/

/-- Any index-map whose entries are framed bricks yields the `Forall₂` the fold
    consumes. The `emitFOpFramed` analogue of
    `Secp256k1PointOpFrontDenote.forall2_mapIdx`. -/
theorem forall2_mapIdxFramed (fw : Nat) (frame : String) (slotOf : String → Nat) :
    ∀ (ops : List FOp) (g : Nat → FOp → List LowCT),
      (∀ i op, ∃ j, g i op = emitFOpFramed fw frame slotOf j op) →
      List.Forall₂ (fun op l => ∃ i, l = emitFOpFramed fw frame slotOf i op) ops (ops.mapIdx g) := by
  intro ops
  induction ops with
  | nil => intro g _; exact .nil
  | cons a l ih =>
      intro g hg
      rw [List.mapIdx_cons]
      exact .cons (hg 0 a) (ih (fun i => g (i + 1)) (fun i op => hg (i + 1) op))

/-! ## 4. The brick fold -/

/-- **A `Forall₂`-generic list of framed bricks lands the frame-slot value.**
    From a frame satisfying `FrameSlots arr V active` with every active slot below
    the prime, running the flattened framed bricks lands `FrameSlots` at the
    slot-fold `scheduleEvalFramed` and re-establishes the operand-range bound.
    Mirrors `Secp256k1PointOpBrickInv.brickFold_scheduleEval_inv` over the framed
    emit. -/
theorem brickFoldFramed {fw : Nat} {frame : String} {slotOf : String → Nat}
    {ca : Char} {ra : List Char} {active : Nat}
    (harr : frame.toList = ca :: ra) (hcaTmp : ¬ isTmpName frame)
    (hcaf : ca ≠ 'f') (hcai : ca ≠ 'i') (hcaZ : ca ≠ 'Z') (hcaC : ca ≠ 'C') (hcaP : ca ≠ 'P')
    (hNcap : (fw + 7) / 8 ≤ 2 ^ 64)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ (fw + 7) / 8) :
    ∀ (ops : List FOp) (ls : List (List LowCT)),
      List.Forall₂ (fun op l => ∃ i, l = emitFOpFramed fw frame slotOf i op) ops ls →
      (∀ op ∈ ops, FramedOpOk fw active slotOf op) →
      ∀ (V : Nat → Nat) (arr : Fin ((fw + 7) / 8) → BitVec 64) (env env' : SEnvScalar),
        env frame = some ⟨.memref ((fw + 7) / 8), arr⟩ →
        FrameSlots arr V active →
        (∀ s, s < active → V s < pNat) →
        semScalar (seqAll ls.flatten) env = some env' →
        ∃ fr : Fin ((fw + 7) / 8) → BitVec 64,
          env' frame = some ⟨.memref ((fw + 7) / 8), fr⟩ ∧
          FrameSlots fr (scheduleEvalFramed slotOf ops V) active ∧
          (∀ s, s < active → scheduleEvalFramed slotOf ops V s < pNat) := by
  intro ops
  induction ops with
  | nil =>
      intro ls hf _ V arr env env' hF hFrame hVlt hsem
      cases hf
      simp only [List.flatten_nil] at hsem
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      exact ⟨arr, hF, hFrame, hVlt⟩
  | cons op ops ih =>
      intro ls hf hOk V arr env env' hF hFrame hVlt hsem
      cases hf with
      | cons hl hrest =>
          rename_i l ls'
          obtain ⟨i, rfl⟩ := hl
          rw [List.flatten_cons, semScalar_seqAll_append] at hsem
          obtain ⟨e1, hstep, htail⟩ := Option.bind_eq_some_iff.mp hsem
          have hHeadOk := hOk op List.mem_cons_self
          have hstepLt := stepFramed_lt (slotOf := slotOf) (active := active) op hVlt
          have hbody : ∃ fr : Fin ((fw + 7) / 8) → BitVec 64,
              e1 frame = some ⟨.memref ((fw + 7) / 8), fr⟩ ∧
              FrameSlots fr (stepFramed slotOf V op) active := by
            cases op with
            | mul o a b =>
                obtain ⟨hAact, hBact, hAcap, hBcap, hso4⟩ := hHeadOk
                simp only [stepFramed]
                exact emitFOpFramed_mul_value i o a b harr hcaTmp hcaf hcai hcaZ hcaC hcaP
                  hF hFrame hNcap hAcap hBcap hso4 hactive hAact hBact
                  (hVlt _ hAact) (hVlt _ hBact) hstep
            | add o a b =>
                obtain ⟨hAact, hBact, hAcap, hBcap, hso4⟩ := hHeadOk
                simp only [stepFramed]
                exact emitFOpFramed_add_value i o a b harr hcaTmp hcaf hcai hcaZ hcaC hcaP
                  hF hFrame hNcap hAcap hBcap hso4 hactive hAact hBact
                  (hVlt _ hAact) (hVlt _ hBact) hstep
            | sub o a b =>
                obtain ⟨hAact, hBact, hAcap, hBcap, hso4⟩ := hHeadOk
                simp only [stepFramed]
                exact emitFOpFramed_sub_value i o a b harr hcaTmp hcaf hcai hcaZ hcaC hcaP
                  hF hFrame hNcap hAcap hBcap hso4 hactive hAact hBact
                  (hVlt _ hAact) (hVlt _ hBact) hstep
          obtain ⟨fr1, hF1, hFrame1⟩ := hbody
          obtain ⟨fr', hF', hFrame', hVlt'⟩ :=
            ih ls' hrest (fun o ho => hOk o (List.mem_cons_of_mem _ ho))
              (stepFramed slotOf V op) fr1 e1 env' hF1 hFrame1 hstepLt htail
          refine ⟨fr', hF', ?_, ?_⟩
          · show FrameSlots fr' (scheduleEvalFramed slotOf (op :: ops) V) active
            rw [scheduleEvalFramed, List.foldl_cons]; exact hFrame'
          · show ∀ s, s < active → scheduleEvalFramed slotOf (op :: ops) V s < pNat
            rw [scheduleEvalFramed, List.foldl_cons]; exact hVlt'

/-! ## 5. The framed doubling body's frame-slot value -/

/-- **The framed doubling body lands `FrameSlots` at the schedule slot-fold.**
    Running `jacDblBodyFramed` from a frame satisfying `FrameSlots arr V active`
    (with the active slots below the prime, and every doubling-schedule op's slots
    in scope and addressable in the 88-cell frame) leaves the frame satisfying
    `FrameSlots` at `scheduleEvalFramed slotOfDbl jacDblSchedule V`. -/
theorem jacDblBodyFramed_cells {env env' : SEnvScalar}
    {arr : Fin 88 → BitVec 64} {V : Nat → Nat} {active : Nat}
    (hF : env "F" = some ⟨.memref 88, arr⟩)
    (hFrame : FrameSlots arr V active)
    (hVlt : ∀ s, s < active → V s < pNat)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ 88)
    (hOk : ∀ op ∈ jacDblSchedule, FramedOpOk (8 * frameCells) active slotOfDbl op)
    (hrun : semScalar jacDblBodyFramed env = some env') :
    ∃ fr : Fin 88 → BitVec 64, env' "F" = some ⟨.memref 88, fr⟩ ∧
      FrameSlots fr (scheduleEvalFramed slotOfDbl jacDblSchedule V) active := by
  have hfa := forall2_mapIdxFramed (8 * frameCells) "F" slotOfDbl jacDblSchedule
    (fun i op => emitFOpFramed (8 * frameCells) "F" slotOfDbl i op) (fun i op => ⟨i, rfl⟩)
  obtain ⟨fr, hF', hFrame', _⟩ :=
    brickFoldFramed (frame := "F") (show ("F").toList = 'F' :: [] from rfl)
      (notTmp_of_len "F" (by decide)) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by intro s hs; exact hactive s hs)
      jacDblSchedule _ hfa hOk V arr env env' hF hFrame hVlt hrun
  exact ⟨fr, hF', hFrame'⟩

/-! ## 6. The slot fold agrees with the named schedule interpreter -/

/-- A field op whose output and both operands are field-element names of the
    doubling schedule. -/
def DblNamed : FOp → Prop
  | .mul o a b => o ∈ dblNames ∧ a ∈ dblNames ∧ b ∈ dblNames
  | .add o a b => o ∈ dblNames ∧ a ∈ dblNames ∧ b ∈ dblNames
  | .sub o a b => o ∈ dblNames ∧ a ∈ dblNames ∧ b ∈ dblNames

instance : DecidablePred DblNamed := fun op => by
  cases op <;> unfold DblNamed <;> infer_instance

/-- `dblNames` has 22 entries: the three inputs and the 19 schedule outputs. -/
theorem dblNames_length : dblNames.length = 22 := by decide

/-- Every doubling name sits in one of the 22 frame slots. -/
theorem slotOfDbl_lt {m : String} (hm : m ∈ dblNames) : slotOfDbl m < 22 := by
  show dblNames.idxOf m < 22
  rw [← dblNames_length]
  exact List.idxOf_lt_length_of_mem hm

/-- A doubling-named op satisfies the static frame side-conditions of the
    single-brick value lemmas: both operand slots are in the active window, and
    all three slots address inside the 88-cell frame. Derived from name
    membership through `slotOfDbl_lt`, so no `2 ^ 64` is reduced in the kernel. -/
theorem framedOpOk_of_dblNamed {op : FOp} (hop : DblNamed op) :
    FramedOpOk (8 * frameCells) 22 slotOfDbl op := by
  have hb2 : ∀ k, k < 22 → 4 * k + 4 ≤ 2 ^ 64 := fun k hk =>
    Nat.le_trans (show 4 * k + 4 ≤ 88 by omega) (by norm_num)
  have hbf : ∀ k, k < 22 → 4 * k + 4 ≤ (8 * frameCells + 7) / 8 := by
    intro k hk; simp only [frameCells]; omega
  cases op with
  | mul o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      exact ⟨slotOfDbl_lt ha, slotOfDbl_lt hb,
        hb2 _ (slotOfDbl_lt ha), hb2 _ (slotOfDbl_lt hb), hbf _ (slotOfDbl_lt ho)⟩
  | add o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      exact ⟨slotOfDbl_lt ha, slotOfDbl_lt hb,
        hb2 _ (slotOfDbl_lt ha), hb2 _ (slotOfDbl_lt hb), hbf _ (slotOfDbl_lt ho)⟩
  | sub o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      exact ⟨slotOfDbl_lt ha, slotOfDbl_lt hb,
        hb2 _ (slotOfDbl_lt ha), hb2 _ (slotOfDbl_lt hb), hbf _ (slotOfDbl_lt ho)⟩

/-- Every op of the doubling schedule is doubling-named. Discharged per op so the
    kernel decides one triple of name memberships at a time. -/
theorem jacDblSchedule_dblNamed : ∀ op ∈ jacDblSchedule, DblNamed op := by
  intro op hop
  fin_cases hop <;> decide

/-- **`slotOfDbl` is injective on the doubling names.** `dblNames.idxOf` returns
    the first occurrence, so two names with the same slot index sit at the same
    list position and are equal. -/
theorem slotOfDbl_inj {m o : String} (hm : m ∈ dblNames) (ho : o ∈ dblNames)
    (h : slotOfDbl m = slotOfDbl o) : m = o := by
  have em : dblNames[dblNames.idxOf m]'(List.idxOf_lt_length_of_mem hm) = m :=
    List.getElem_idxOf _
  have eo : dblNames[dblNames.idxOf o]'(List.idxOf_lt_length_of_mem ho) = o :=
    List.getElem_idxOf _
  rw [← em, ← eo]
  congr 1

/-- One `stepFramed` step matches one `stepFOpG` step under the slot↔name
    correspondence `V ∘ slotOfDbl ↔ env`, at every doubling name. -/
theorem stepFramed_pullback (op : FOp) (hop : DblNamed op)
    (V : Nat → Nat) (env : String → Nat)
    (hR : ∀ m ∈ dblNames, V (slotOfDbl m) = env m) :
    ∀ m ∈ dblNames, stepFramed slotOfDbl V op (slotOfDbl m) = stepFOpG fm fa fs env op m := by
  intro m hm
  cases op with
  | mul o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · rw [Function.update_of_ne (fun h => hmo (slotOfDbl_inj hm ho h)), ite_eq_right hmo]
        exact hR m hm
  | add o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · rw [Function.update_of_ne (fun h => hmo (slotOfDbl_inj hm ho h)), ite_eq_right hmo]
        exact hR m hm
  | sub o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · rw [Function.update_of_ne (fun h => hmo (slotOfDbl_inj hm ho h)), ite_eq_right hmo]
        exact hR m hm

/-- **The framed slot fold agrees with the named schedule interpreter.** For a
    schedule of doubling-named ops, `scheduleEvalFramed slotOfDbl` at a name's
    slot equals `scheduleEvalG fm fa fs` at that name, under the pointwise
    correspondence `V ∘ slotOfDbl ↔ env`. -/
theorem scheduleEvalFramed_bridge :
    ∀ (ops : List FOp), (∀ op ∈ ops, DblNamed op) →
    ∀ (V : Nat → Nat) (env : String → Nat),
      (∀ m ∈ dblNames, V (slotOfDbl m) = env m) →
    ∀ n ∈ dblNames,
      scheduleEvalFramed slotOfDbl ops V (slotOfDbl n)
        = scheduleEvalG fm fa fs ops env n := by
  intro ops
  induction ops with
  | nil =>
      intro _ V env hR n hn
      simp only [scheduleEvalFramed, scheduleEvalG, List.foldl_nil]
      exact hR n hn
  | cons op ops ih =>
      intro hops V env hR n hn
      show scheduleEvalFramed slotOfDbl ops (stepFramed slotOfDbl V op) (slotOfDbl n)
        = scheduleEvalG fm fa fs ops (stepFOpG fm fa fs env op) n
      exact ih (fun o ho => hops o (List.mem_cons_of_mem _ ho))
        (stepFramed slotOfDbl V op) (stepFOpG fm fa fs env op)
        (stepFramed_pullback op (hops op List.mem_cons_self) V env hR) n hn

/-- **The framed doubling slot fold carries `jacDblSpec` in the output slots.**
    When `V` matches the `dblEnv0` entry environment on the frame slots — the
    input coordinates in the `X`/`Y`/`Z` slots and `0` in every intermediate
    slot — the slot fold's values in the `Xp`/`Yp`/`Zp` slots are `jacDblSpec X Y Z`.
    The framed slot fold is carried to the named schedule interpreter at `dblEnv0`
    by the structural `scheduleEvalFramed_bridge`, then the committed
    `jacDblSchedule_realizes_spec` supplies the arithmetic; no fold is unrolled. -/
theorem jacDblSchedule_framed_realizes (V : Nat → Nat) (X Y Z : Nat)
    (hV0 : ∀ m ∈ dblNames, V (slotOfDbl m) = dblEnv0 X Y Z m) :
    (scheduleEvalFramed slotOfDbl jacDblSchedule V (slotOfDbl "Xp"),
     scheduleEvalFramed slotOfDbl jacDblSchedule V (slotOfDbl "Yp"),
     scheduleEvalFramed slotOfDbl jacDblSchedule V (slotOfDbl "Zp"))
      = jacDblSpec X Y Z := by
  have hdbl : ∀ op ∈ jacDblSchedule, DblNamed op := jacDblSchedule_dblNamed
  rw [scheduleEvalFramed_bridge jacDblSchedule hdbl V (dblEnv0 X Y Z) hV0 "Xp" (by decide),
      scheduleEvalFramed_bridge jacDblSchedule hdbl V (dblEnv0 X Y Z) hV0 "Yp" (by decide),
      scheduleEvalFramed_bridge jacDblSchedule hdbl V (dblEnv0 X Y Z) hV0 "Zp" (by decide)]
  exact jacDblSchedule_realizes_spec X Y Z

/-! ## 7. The framed doubling body's output-slot values -/

/-- **The framed doubling body computes `jacDblSpec` in its output slots.**
    Running `jacDblBodyFramed` from a frame satisfying `FrameSlots arr V 22`, whose
    slots match the `dblEnv0` entry environment (input coordinates in the
    `X`/`Y`/`Z` slots, `0` in every intermediate slot) and are below the prime,
    lands a frame whose `Xp`/`Yp`/`Zp` slots hold `jacDblSpec X Y Z`. -/
theorem jacDblBodyFramed_spec {env env' : SEnvScalar}
    {arr : Fin 88 → BitVec 64} {V : Nat → Nat} (X Y Z : Nat)
    (hF : env "F" = some ⟨.memref 88, arr⟩)
    (hFrame : FrameSlots arr V 22)
    (hVlt : ∀ s, s < 22 → V s < pNat)
    (hV0 : ∀ m ∈ dblNames, V (slotOfDbl m) = dblEnv0 X Y Z m)
    (hrun : semScalar jacDblBodyFramed env = some env') :
    ∃ fr : Fin 88 → BitVec 64, env' "F" = some ⟨.memref 88, fr⟩ ∧
      slotVal fr (slotOfDbl "Xp") = (jacDblSpec X Y Z).1 ∧
      slotVal fr (slotOfDbl "Yp") = (jacDblSpec X Y Z).2.1 ∧
      slotVal fr (slotOfDbl "Zp") = (jacDblSpec X Y Z).2.2 := by
  have hactive : ∀ s, s < 22 → 4 * s + 4 ≤ 88 := by intro s hs; omega
  have hOk : ∀ op ∈ jacDblSchedule, FramedOpOk (8 * frameCells) 22 slotOfDbl op :=
    fun op hop => framedOpOk_of_dblNamed (jacDblSchedule_dblNamed op hop)
  obtain ⟨fr, hF', hFrame'⟩ := jacDblBodyFramed_cells hF hFrame hVlt hactive hOk hrun
  have hTuple := jacDblSchedule_framed_realizes V X Y Z hV0
  refine ⟨fr, hF', ?_, ?_, ?_⟩
  · rw [hFrame' (slotOfDbl "Xp") (by decide)]; exact congrArg Prod.fst hTuple
  · rw [hFrame' (slotOfDbl "Yp") (by decide)]; exact congrArg (fun p => p.2.1) hTuple
  · rw [hFrame' (slotOfDbl "Zp") (by decide)]; exact congrArg (fun p => p.2.2) hTuple

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedScheduleValue
