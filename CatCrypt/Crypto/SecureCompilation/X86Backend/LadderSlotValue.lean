/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedScheduleValue

/-!
# Frame-slot values of the ladder-step doubling and addition segments

`Secp256k1PointOpFramedScheduleValue` folds the per-brick framed value step over
a schedule at the doubling tiling (`slotOfDbl`, 88 cells). The fold machinery
(`brickFoldFramed`, `scheduleEvalFramed`) is slot-map-generic; this module
instantiates it at the unified ladder slot maps (`slotLadDbl` / `slotLadAdd`,
256 cells) of `Secp256k1PointOpFrontFramedLadder.ladderStepFramed`, and adds the
name-generic bridge from the slot fold to the named schedule interpreter
`scheduleEvalG` that both instantiations share.

`ladDblBody` and `ladAddBody` are the first and third segments of
`ladderStepFramed` (the middle segment is the select trip). Their `_spec`
theorems are stated at the active window `51` — slots `0..50`, every slot the
two schedules and the select candidates touch — so the two value lemmas
compose across the trip: each returns the full `FrameSlots` invariant at its
slot fold together with the operand-range bound, and pins the three output
slots to `jacDblSpec` / `jacAddSpec` of the input slots.

The `_spec_inputs` forms ask for the slot↔name correspondence at the
schedule's input names only. Both schedules are write-before-read — every
intermediate is written by an earlier op than the one reading it — so
`scheduleEvalFramed_bridge_of_inputs` propagates the correspondence from the
input names to every name the schedule writes, and the output slots and
intermediate slots may hold anything at segment entry. That is what an
iterated ladder offers: the doubling segment's intermediates carry the
previous trip's values, and the addition segment's output slots `6,7,8` carry
the previous trip's sum row.

The middle segment gets its value lemma here too: `emitSelectFramed_value`
reads one framed select brick back as a frame-slot mux — the brick's
operand-load prefix through `Secp256k1PointOpFramedBrickValue.framedPrefix`,
its body through `semScalar_setExpr_eq` / the `RArrLoad` waist arm /
`setExprChain_values`, and its copy-and-store tail through `framedCopy_run`
and `storeFieldTo_cells` — and `selectTrip_spec` composes it over the three
coordinates, threading the selector cell (untouched by the three four-cell
stores) across the trip.

## Main results

* `SchedNamed`, `stepFramed_pullback_of_inj`, `scheduleEvalFramed_bridge_of_inj`
  — the slot fold agrees with the named schedule interpreter at any slot map
  injective on the schedule's names.
* `writeBeforeRead`, `schedAvail`, `stepFramed_pullback_of_avail`,
  `scheduleEvalFramed_bridge_of_inputs` — the same agreement from the slot↔name
  correspondence at the schedule's input names only, for a schedule that writes
  each intermediate before reading it.
* `scheduleEvalFramed_of_notMem` — the slot fold leaves every slot that no
  schedule op writes unchanged.
* `ladDblBody_cells` / `ladDblBody_spec_inputs` / `ladDblBody_spec` — the
  ladder-step doubling segment lands `FrameSlots` at the `slotLadDbl` slot fold;
  from a frame matching `dblEnv0` on the three input-coordinate slots (`0,1,2`),
  its `Xp`/`Yp`/`Zp` slots (`3,4,5`) end holding `jacDblSpec X Y Z`.
* `ladAddBody_cells` / `ladAddBody_spec_inputs` / `ladAddBody_spec` — the
  ladder-step addition segment lands `FrameSlots` at the `slotLadAdd` slot fold;
  from a frame matching `addEnv0` on the six input-coordinate slots
  (`3,4,5` and `9,10,11`), its `Xp`/`Yp`/`Zp` slots (`6,7,8`) end holding
  `jacAddSpec X1 Y1 Z1 X2 Y2 Z2`.
* `setExprChain_values` — a chain of scalar assignments over pairwise-distinct
  names none of whose expressions read a chain output, read back as values.
* `selWord_mux` — the per-limb branch-free select word
  `B ^^^ ((A ^^^ B) &&& (bit · 0xFFFFFFFF))` is a mux for `bit ∈ {0, 1}`.
* `emitSelectFramed_value` — one framed select brick resets its output slot to
  the slot value of the `a` candidate at selector `1` and of the `b` candidate
  at selector `0`, leaving every cell outside the output window unchanged.
* `selectTrip_spec` — the select trip writes the sum row (selector `1`) or the
  doubled row (selector `0`) into the accumulator slots `(accX, accY, accZ)`,
  keyed on the selector word at slot `51`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LadderSlotValue

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
  (semScalar_setExpr_eq evalBV_congr_vars)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll pNat sv mask32)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp fm fa fs jacDblSchedule jacAddSchedule jacDblSpec jacAddSpec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (hd hdAppend neOfHd pfxNe feHN feHN_eq accN accN_congr feVal_eq_accN headOk_of_hd
   ofNat_toNat)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal semScalar_seqAll_append semScalar_seqAll_cons)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (envReader_of_bound slot_inj half_lo)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal (map_range_getBang)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedCells
  (FrameSlots slotVal memGetDyn_lt slotVal_hit slotVal_miss storeFieldTo_cells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue (oh_bridge)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedBrickValue
  (framedPrefix framedCopy_run headF_toList hd_ix pNat_lt_pow256)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed (emitFOpFramed dblNames)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedAdd (addNames)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder
  (slotLadDbl slotLadAdd slotLadSel ladderFrameCells emitSelectFramed selBody selectTrip)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional
  (scheduleEvalG stepFOpG envUpd dblEnv0 addEnv0 jacDblSchedule_realizes_spec
   jacAddSchedule_realizes_spec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedScheduleValue
  (stepFramed scheduleEvalFramed FramedOpOk brickFoldFramed forall2_mapIdxFramed
   DblNamed jacDblSchedule_dblNamed)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered (notTmp_of_len HeadOk)

/-! ## 1. The ladder-step doubling and addition segments -/

/-- The doubling segment of `ladderStepFramed`: the 19 doubling bricks over the
    256-cell ladder frame at the `slotLadDbl` slot map. -/
def ladDblBody : LowCT :=
  seqAll ((jacDblSchedule.mapIdx
    (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadDbl i op)).flatten)

/-- The addition segment of `ladderStepFramed`: the 23 addition bricks over the
    256-cell ladder frame at the `slotLadAdd` slot map. -/
def ladAddBody : LowCT :=
  seqAll ((jacAddSchedule.mapIdx
    (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadAdd i op)).flatten)

/-! ## 2. The name-generic slot-fold ↔ named-interpreter bridge -/

/-- A field op whose output and both operands are members of a given name list.
    The name-generic form of `Secp256k1PointOpFramedScheduleValue.DblNamed`. -/
def SchedNamed (names : List String) : FOp → Prop
  | .mul o a b | .add o a b | .sub o a b => o ∈ names ∧ a ∈ names ∧ b ∈ names

instance (names : List String) : DecidablePred (SchedNamed names) := fun op => by
  cases op <;> unfold SchedNamed <;> infer_instance

/-- One `stepFramed` step matches one `stepFOpG` step under the slot↔name
    correspondence `V ∘ slotOf ↔ env`, at every name, for any slot map injective
    on the name list. -/
theorem stepFramed_pullback_of_inj {names : List String} {slotOf : String → Nat}
    (hinj : ∀ m ∈ names, ∀ o ∈ names, slotOf m = slotOf o → m = o)
    (op : FOp) (hop : SchedNamed names op)
    (V : Nat → Nat) (env : String → Nat)
    (hR : ∀ m ∈ names, V (slotOf m) = env m) :
    ∀ m ∈ names, stepFramed slotOf V op (slotOf m) = stepFOpG fm fa fs env op m := by
  intro m hm
  cases op with
  | mul o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · rw [Function.update_of_ne (fun h => hmo (hinj m hm o ho h)), ite_eq_right hmo]
        exact hR m hm
  | add o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · rw [Function.update_of_ne (fun h => hmo (hinj m hm o ho h)), ite_eq_right hmo]
        exact hR m hm
  | sub o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · rw [Function.update_of_ne (fun h => hmo (hinj m hm o ho h)), ite_eq_right hmo]
        exact hR m hm

/-- **The framed slot fold agrees with the named schedule interpreter, at any
    slot map injective on the schedule's names.** The name-generic form of
    `Secp256k1PointOpFramedScheduleValue.scheduleEvalFramed_bridge`. -/
theorem scheduleEvalFramed_bridge_of_inj {names : List String} {slotOf : String → Nat}
    (hinj : ∀ m ∈ names, ∀ o ∈ names, slotOf m = slotOf o → m = o) :
    ∀ (ops : List FOp), (∀ op ∈ ops, SchedNamed names op) →
    ∀ (V : Nat → Nat) (env : String → Nat),
      (∀ m ∈ names, V (slotOf m) = env m) →
    ∀ n ∈ names,
      scheduleEvalFramed slotOf ops V (slotOf n)
        = scheduleEvalG fm fa fs ops env n := by
  intro ops
  induction ops with
  | nil =>
      intro _ V env hR n hn
      simp only [scheduleEvalFramed, scheduleEvalG, List.foldl_nil]
      exact hR n hn
  | cons op ops ih =>
      intro hops V env hR n hn
      show scheduleEvalFramed slotOf ops (stepFramed slotOf V op) (slotOf n)
        = scheduleEvalG fm fa fs ops (stepFOpG fm fa fs env op) n
      exact ih (fun o ho => hops o (List.mem_cons_of_mem _ ho))
        (stepFramed slotOf V op) (stepFOpG fm fa fs env op)
        (stepFramed_pullback_of_inj hinj op (hops op List.mem_cons_self) V env hR) n hn

/-! ## 2b. Agreement on the schedule's input names alone -/

/-- The two names a field op reads. -/
def opIns : FOp → List String
  | .mul _ a b | .add _ a b | .sub _ a b => [a, b]

/-- The name a field op writes. -/
def opOut : FOp → String
  | .mul o _ _ | .add o _ _ | .sub o _ _ => o

/-- Every op of the schedule reads only names available where it sits: names of
    `avail`, or names an earlier op of the schedule wrote. -/
def writeBeforeRead (avail : List String) : List FOp → Bool
  | [] => true
  | op :: ops =>
      (opIns op).all (fun v => decide (v ∈ avail))
        && writeBeforeRead (opOut op :: avail) ops

/-- The names available after the whole schedule has run: `avail` extended by
    every schedule output. -/
def schedAvail (avail : List String) : List FOp → List String
  | [] => avail
  | op :: ops => schedAvail (opOut op :: avail) ops

/-- A field op whose names are all members of a name list writes into that
    list. -/
theorem opOut_mem_of_schedNamed {names : List String} {op : FOp}
    (hop : SchedNamed names op) : opOut op ∈ names := by
  cases op <;> exact hop.1

/-- One `stepFramed` step matches one `stepFOpG` step at every available name,
    from agreement on the names available before the step, provided the step's
    two operands are among them. -/
theorem stepFramed_pullback_of_avail {names : List String} {slotOf : String → Nat}
    (hinj : ∀ m ∈ names, ∀ o ∈ names, slotOf m = slotOf o → m = o)
    {avail : List String} (hsub : ∀ m ∈ avail, m ∈ names)
    (op : FOp) (hop : SchedNamed names op) (hins : ∀ v ∈ opIns op, v ∈ avail)
    (V : Nat → Nat) (env : String → Nat)
    (hR : ∀ m ∈ avail, V (slotOf m) = env m) :
    ∀ m ∈ opOut op :: avail,
      stepFramed slotOf V op (slotOf m) = stepFOpG fm fa fs env op m := by
  intro m hm
  cases op with
  | mul o a b =>
      obtain ⟨ho, -, -⟩ := hop
      have ha : a ∈ avail := hins a (by simp [opIns])
      have hb : b ∈ avail := hins b (by simp [opIns])
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · have hm' : m ∈ avail := by
          rcases List.mem_cons.mp hm with h | h
          · exact absurd h hmo
          · exact h
        rw [Function.update_of_ne (fun h => hmo (hinj m (hsub m hm') o ho h)), ite_eq_right hmo]
        exact hR m hm'
  | add o a b =>
      obtain ⟨ho, -, -⟩ := hop
      have ha : a ∈ avail := hins a (by simp [opIns])
      have hb : b ∈ avail := hins b (by simp [opIns])
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · have hm' : m ∈ avail := by
          rcases List.mem_cons.mp hm with h | h
          · exact absurd h hmo
          · exact h
        rw [Function.update_of_ne (fun h => hmo (hinj m (hsub m hm') o ho h)), ite_eq_right hmo]
        exact hR m hm'
  | sub o a b =>
      obtain ⟨ho, -, -⟩ := hop
      have ha : a ∈ avail := hins a (by simp [opIns])
      have hb : b ∈ avail := hins b (by simp [opIns])
      simp only [stepFramed, stepFOpG, envUpd, hR a ha, hR b hb]
      by_cases hmo : m = o
      · subst hmo; simp [Function.update_self]
      · have hm' : m ∈ avail := by
          rcases List.mem_cons.mp hm with h | h
          · exact absurd h hmo
          · exact h
        rw [Function.update_of_ne (fun h => hmo (hinj m (hsub m hm') o ho h)), ite_eq_right hmo]
        exact hR m hm'

/-- **The framed slot fold agrees with the named schedule interpreter from
    agreement on the schedule's input names alone.** A write-before-read
    schedule needs the slot↔name correspondence only at the names available at
    entry; every later name it reads it has already written, so the fold and
    the interpreter agree at every name of `schedAvail`. -/
theorem scheduleEvalFramed_bridge_of_inputs {names : List String} {slotOf : String → Nat}
    (hinj : ∀ m ∈ names, ∀ o ∈ names, slotOf m = slotOf o → m = o) :
    ∀ (ops : List FOp) (avail : List String),
      (∀ m ∈ avail, m ∈ names) → (∀ op ∈ ops, SchedNamed names op) →
      writeBeforeRead avail ops = true →
    ∀ (V : Nat → Nat) (env : String → Nat),
      (∀ m ∈ avail, V (slotOf m) = env m) →
    ∀ n ∈ schedAvail avail ops,
      scheduleEvalFramed slotOf ops V (slotOf n)
        = scheduleEvalG fm fa fs ops env n := by
  intro ops
  induction ops with
  | nil =>
      intro avail _ _ _ V env hR n hn
      simp only [scheduleEvalFramed, scheduleEvalG, List.foldl_nil]
      exact hR n hn
  | cons op ops ih =>
      intro avail hsub hops hwbr V env hR n hn
      simp only [writeBeforeRead, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at hwbr
      have hsub' : ∀ m ∈ opOut op :: avail, m ∈ names := by
        intro m hm
        rcases List.mem_cons.mp hm with rfl | h
        · exact opOut_mem_of_schedNamed (hops op List.mem_cons_self)
        · exact hsub m h
      show scheduleEvalFramed slotOf ops (stepFramed slotOf V op) (slotOf n)
        = scheduleEvalG fm fa fs ops (stepFOpG fm fa fs env op) n
      exact ih (opOut op :: avail) hsub'
        (fun o ho => hops o (List.mem_cons_of_mem _ ho)) hwbr.2
        (stepFramed slotOf V op) (stepFOpG fm fa fs env op)
        (stepFramed_pullback_of_avail hinj hsub op (hops op List.mem_cons_self)
          hwbr.1 V env hR) n hn

/-! ## 3. Slots no schedule op writes are unchanged by the fold -/

/-- The frame slot a field op writes. -/
def outSlot (slotOf : String → Nat) (op : FOp) : Nat := slotOf (opOut op)

/-- One `stepFramed` step leaves every slot other than the op's output slot
    unchanged. -/
theorem stepFramed_of_ne {slotOf : String → Nat} {V : Nat → Nat} {s : Nat}
    (op : FOp) (h : s ≠ outSlot slotOf op) :
    stepFramed slotOf V op s = V s := by
  cases op with
  | mul o a b =>
      simp only [stepFramed]
      exact Function.update_of_ne (by simpa [outSlot] using! h) _ _
  | add o a b =>
      simp only [stepFramed]
      exact Function.update_of_ne (by simpa [outSlot] using! h) _ _
  | sub o a b =>
      simp only [stepFramed]
      exact Function.update_of_ne (by simpa [outSlot] using! h) _ _

/-- **The slot fold leaves every slot no schedule op writes unchanged.** -/
theorem scheduleEvalFramed_of_notMem {slotOf : String → Nat} {s : Nat} :
    ∀ (ops : List FOp), (∀ op ∈ ops, s ≠ outSlot slotOf op) →
    ∀ V : Nat → Nat, scheduleEvalFramed slotOf ops V s = V s := by
  intro ops
  induction ops with
  | nil => intro _ V; rfl
  | cons op ops ih =>
      intro h V
      show scheduleEvalFramed slotOf ops (stepFramed slotOf V op) s = V s
      rw [ih (fun o ho => h o (List.mem_cons_of_mem _ ho)) (stepFramed slotOf V op),
        stepFramed_of_ne op (h op List.mem_cons_self)]

/-! ## 4. Static side-conditions at the ladder slot maps -/

/-- A schedule op whose names all sit below the active window and whose slots
    all address inside the 256-cell ladder frame satisfies the per-brick static
    side-conditions. -/
theorem framedOpOk_of_schedNamed {names : List String} {slotOf : String → Nat}
    {active : Nat} {op : FOp}
    (hlt : ∀ m ∈ names, slotOf m < active) (hcap : active ≤ 64)
    (hop : SchedNamed names op) :
    FramedOpOk (8 * ladderFrameCells) active slotOf op := by
  have hb2 : ∀ k, k < active → 4 * k + 4 ≤ 2 ^ 64 := fun k hk =>
    Nat.le_trans (show 4 * k + 4 ≤ 256 by omega) (by norm_num)
  have hbf : ∀ k, k < active → 4 * k + 4 ≤ (8 * ladderFrameCells + 7) / 8 := by
    intro k hk; simp only [ladderFrameCells]; omega
  cases op with
  | mul o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      exact ⟨hlt a ha, hlt b hb,
        hb2 _ (hlt a ha), hb2 _ (hlt b hb), hbf _ (hlt o ho)⟩
  | add o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      exact ⟨hlt a ha, hlt b hb,
        hb2 _ (hlt a ha), hb2 _ (hlt b hb), hbf _ (hlt o ho)⟩
  | sub o a b =>
      obtain ⟨ho, ha, hb⟩ := hop
      exact ⟨hlt a ha, hlt b hb,
        hb2 _ (hlt a ha), hb2 _ (hlt b hb), hbf _ (hlt o ho)⟩

/-! ## 5. The doubling segment at `slotLadDbl` -/

/-- Every doubling-schedule op's names are doubling names — restated from the
    committed `jacDblSchedule_dblNamed` in the name-generic form. -/
theorem jacDblSchedule_schedNamed : ∀ op ∈ jacDblSchedule, SchedNamed dblNames op := by
  intro op hop
  have h := jacDblSchedule_dblNamed op hop
  cases op <;> exact h

/-- Every doubling name's ladder slot is below `31` (the doubling window: the
    boundary slots `0..5` and the intermediates `15..30`). -/
theorem slotLadDbl_lt : ∀ m ∈ dblNames, slotLadDbl m < 31 := by decide

/-- `slotLadDbl` is injective on the doubling names. -/
theorem slotLadDbl_inj : ∀ m ∈ dblNames, ∀ o ∈ dblNames,
    slotLadDbl m = slotLadDbl o → m = o := by decide

/-- Every doubling-schedule op satisfies the per-brick static side-conditions at
    the ladder doubling slot map, at any active window between `31` and `64`. -/
theorem jacDblSchedule_framedOpOk_lad {active : Nat} (h31 : 31 ≤ active)
    (h64 : active ≤ 64) :
    ∀ op ∈ jacDblSchedule, FramedOpOk (8 * ladderFrameCells) active slotLadDbl op :=
  fun op hop => framedOpOk_of_schedNamed
    (fun m hm => Nat.lt_of_lt_of_le (slotLadDbl_lt m hm) h31) h64
    (jacDblSchedule_schedNamed op hop)

/-- **The ladder-step doubling segment lands `FrameSlots` at the `slotLadDbl`
    slot fold.** The `slotLadDbl`/256-cell instantiation of
    `Secp256k1PointOpFramedScheduleValue.jacDblBodyFramed_cells`, keeping the
    operand-range bound in the conclusion so segments compose. -/
theorem ladDblBody_cells {env env' : SEnvScalar}
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat} {active : Nat}
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V active)
    (hVlt : ∀ s, s < active → V s < pNat)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ 256)
    (hOk : ∀ op ∈ jacDblSchedule, FramedOpOk (8 * ladderFrameCells) active slotLadDbl op)
    (hrun : semScalar ladDblBody env = some env') :
    ∃ fr : Fin 256 → BitVec 64, env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr (scheduleEvalFramed slotLadDbl jacDblSchedule V) active ∧
      (∀ s, s < active → scheduleEvalFramed slotLadDbl jacDblSchedule V s < pNat) := by
  have hfa := forall2_mapIdxFramed (8 * ladderFrameCells) "F" slotLadDbl jacDblSchedule
    (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadDbl i op)
    (fun i op => ⟨i, rfl⟩)
  exact brickFoldFramed (frame := "F") (show ("F").toList = 'F' :: [] from rfl)
    (notTmp_of_len "F" (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro s hs; exact hactive s hs)
    jacDblSchedule _ hfa hOk V arr env env' hF hFrame hVlt hrun

/-- The doubling schedule's input names: the three input coordinates. -/
def dblInputs : List String := ["X", "Y", "Z"]

/-- The doubling schedule reads only its three input coordinates and names an
    earlier op of the schedule wrote. -/
theorem jacDblSchedule_writeBeforeRead :
    writeBeforeRead dblInputs jacDblSchedule = true := by decide

/-- The doubling inputs are doubling names. -/
theorem dblInputs_sub : ∀ m ∈ dblInputs, m ∈ dblNames := by decide

/-- **The ladder doubling slot fold carries `jacDblSpec` in the output slots,
    from the input slots alone.** When `V` matches the `dblEnv0` entry
    environment on the three input-coordinate slots — nothing is asked of the
    intermediate slots — the slot fold's values in the `Xp`/`Yp`/`Zp` slots are
    `jacDblSpec X Y Z`. -/
theorem ladDbl_framed_realizes_inputs (V : Nat → Nat) (X Y Z : Nat)
    (hV0 : ∀ m ∈ dblInputs, V (slotLadDbl m) = dblEnv0 X Y Z m) :
    (scheduleEvalFramed slotLadDbl jacDblSchedule V (slotLadDbl "Xp"),
     scheduleEvalFramed slotLadDbl jacDblSchedule V (slotLadDbl "Yp"),
     scheduleEvalFramed slotLadDbl jacDblSchedule V (slotLadDbl "Zp"))
      = jacDblSpec X Y Z := by
  have hb := scheduleEvalFramed_bridge_of_inputs slotLadDbl_inj jacDblSchedule dblInputs
    dblInputs_sub jacDblSchedule_schedNamed jacDblSchedule_writeBeforeRead
    V (dblEnv0 X Y Z) hV0
  rw [hb "Xp" (by decide), hb "Yp" (by decide), hb "Zp" (by decide)]
  exact jacDblSchedule_realizes_spec X Y Z

/-- **The ladder-step doubling segment computes `jacDblSpec` in its output
    slots, from its input slots alone.** `ladDblBody_spec` with the entry
    hypothesis restricted to the three input-coordinate slots `0,1,2`, so a
    frame whose intermediate slots `15..30` still hold an earlier trip's values
    satisfies it. -/
theorem ladDblBody_spec_inputs {env env' : SEnvScalar}
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat} (X Y Z : Nat)
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V 51)
    (hVlt : ∀ s, s < 51 → V s < pNat)
    (hV0 : ∀ m ∈ dblInputs, V (slotLadDbl m) = dblEnv0 X Y Z m)
    (hrun : semScalar ladDblBody env = some env') :
    ∃ fr : Fin 256 → BitVec 64, env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr (scheduleEvalFramed slotLadDbl jacDblSchedule V) 51 ∧
      (∀ s, s < 51 → scheduleEvalFramed slotLadDbl jacDblSchedule V s < pNat) ∧
      slotVal fr (slotLadDbl "Xp") = (jacDblSpec X Y Z).1 ∧
      slotVal fr (slotLadDbl "Yp") = (jacDblSpec X Y Z).2.1 ∧
      slotVal fr (slotLadDbl "Zp") = (jacDblSpec X Y Z).2.2 := by
  obtain ⟨fr, hF', hFrame', hVlt'⟩ :=
    ladDblBody_cells hF hFrame hVlt (by intro s hs; omega)
      (jacDblSchedule_framedOpOk_lad (by norm_num) (by norm_num)) hrun
  have hTuple := ladDbl_framed_realizes_inputs V X Y Z hV0
  refine ⟨fr, hF', hFrame', hVlt', ?_, ?_, ?_⟩
  · rw [hFrame' (slotLadDbl "Xp") (by decide)]; exact congrArg Prod.fst hTuple
  · rw [hFrame' (slotLadDbl "Yp") (by decide)]; exact congrArg (fun p => p.2.1) hTuple
  · rw [hFrame' (slotLadDbl "Zp") (by decide)]; exact congrArg (fun p => p.2.2) hTuple

/-- **The ladder doubling slot fold carries `jacDblSpec` in the output slots.**
    `ladDbl_framed_realizes_inputs` with the entry hypothesis asked of every
    doubling name rather than of the three inputs. -/
theorem ladDbl_framed_realizes (V : Nat → Nat) (X Y Z : Nat)
    (hV0 : ∀ m ∈ dblNames, V (slotLadDbl m) = dblEnv0 X Y Z m) :
    (scheduleEvalFramed slotLadDbl jacDblSchedule V (slotLadDbl "Xp"),
     scheduleEvalFramed slotLadDbl jacDblSchedule V (slotLadDbl "Yp"),
     scheduleEvalFramed slotLadDbl jacDblSchedule V (slotLadDbl "Zp"))
      = jacDblSpec X Y Z :=
  ladDbl_framed_realizes_inputs V X Y Z (fun m hm => hV0 m (dblInputs_sub m hm))

/-- **The ladder-step doubling segment computes `jacDblSpec` in its output
    slots.** `ladDblBody_spec_inputs` with the entry hypothesis asked of every
    doubling name rather than of the three inputs: running `ladDblBody` from a
    frame satisfying `FrameSlots arr V 51` whose slots match the `dblEnv0` entry
    environment on the doubling names and are below the prime lands a frame
    whose `Xp`/`Yp`/`Zp` slots (`3,4,5`) hold `jacDblSpec X Y Z`; the full
    `FrameSlots` at the slot fold and the operand-range bound come with it, so
    the select and addition segments can continue from the conclusion. -/
theorem ladDblBody_spec {env env' : SEnvScalar}
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat} (X Y Z : Nat)
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V 51)
    (hVlt : ∀ s, s < 51 → V s < pNat)
    (hV0 : ∀ m ∈ dblNames, V (slotLadDbl m) = dblEnv0 X Y Z m)
    (hrun : semScalar ladDblBody env = some env') :
    ∃ fr : Fin 256 → BitVec 64, env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr (scheduleEvalFramed slotLadDbl jacDblSchedule V) 51 ∧
      (∀ s, s < 51 → scheduleEvalFramed slotLadDbl jacDblSchedule V s < pNat) ∧
      slotVal fr (slotLadDbl "Xp") = (jacDblSpec X Y Z).1 ∧
      slotVal fr (slotLadDbl "Yp") = (jacDblSpec X Y Z).2.1 ∧
      slotVal fr (slotLadDbl "Zp") = (jacDblSpec X Y Z).2.2 :=
  ladDblBody_spec_inputs X Y Z hF hFrame hVlt
    (fun m hm => hV0 m (dblInputs_sub m hm)) hrun

/-! ## 6. The addition segment at `slotLadAdd` -/

/-- Every addition-schedule op's names are addition names. Discharged per op so
    the kernel decides one triple of name memberships at a time. -/
theorem jacAddSchedule_schedNamed : ∀ op ∈ jacAddSchedule, SchedNamed addNames op := by
  intro op hop
  fin_cases hop <;> decide

/-- Every addition name's ladder slot is below `51` (the addition window: the
    boundary slots `0..8` and the intermediates `31..50`). -/
theorem slotLadAdd_lt : ∀ m ∈ addNames, slotLadAdd m < 51 := by decide

/-- `slotLadAdd` is injective on the addition names. -/
theorem slotLadAdd_inj : ∀ m ∈ addNames, ∀ o ∈ addNames,
    slotLadAdd m = slotLadAdd o → m = o := by decide

/-- Every addition-schedule op satisfies the per-brick static side-conditions at
    the ladder addition slot map, at any active window between `51` and `64`. -/
theorem jacAddSchedule_framedOpOk_lad {active : Nat} (h51 : 51 ≤ active)
    (h64 : active ≤ 64) :
    ∀ op ∈ jacAddSchedule, FramedOpOk (8 * ladderFrameCells) active slotLadAdd op :=
  fun op hop => framedOpOk_of_schedNamed
    (fun m hm => Nat.lt_of_lt_of_le (slotLadAdd_lt m hm) h51) h64
    (jacAddSchedule_schedNamed op hop)

/-- **The ladder-step addition segment lands `FrameSlots` at the `slotLadAdd`
    slot fold.** The addition analogue of `ladDblBody_cells`. -/
theorem ladAddBody_cells {env env' : SEnvScalar}
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat} {active : Nat}
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V active)
    (hVlt : ∀ s, s < active → V s < pNat)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ 256)
    (hOk : ∀ op ∈ jacAddSchedule, FramedOpOk (8 * ladderFrameCells) active slotLadAdd op)
    (hrun : semScalar ladAddBody env = some env') :
    ∃ fr : Fin 256 → BitVec 64, env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr (scheduleEvalFramed slotLadAdd jacAddSchedule V) active ∧
      (∀ s, s < active → scheduleEvalFramed slotLadAdd jacAddSchedule V s < pNat) := by
  have hfa := forall2_mapIdxFramed (8 * ladderFrameCells) "F" slotLadAdd jacAddSchedule
    (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadAdd i op)
    (fun i op => ⟨i, rfl⟩)
  exact brickFoldFramed (frame := "F") (show ("F").toList = 'F' :: [] from rfl)
    (notTmp_of_len "F" (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro s hs; exact hactive s hs)
    jacAddSchedule _ hfa hOk V arr env env' hF hFrame hVlt hrun

/-- The addition schedule's input names: the six input coordinates. -/
def addInputs : List String := ["X1", "Y1", "Z1", "X2", "Y2", "Z2"]

/-- The addition schedule reads only its six input coordinates and names an
    earlier op of the schedule wrote. -/
theorem jacAddSchedule_writeBeforeRead :
    writeBeforeRead addInputs jacAddSchedule = true := by decide

/-- The addition inputs are addition names. -/
theorem addInputs_sub : ∀ m ∈ addInputs, m ∈ addNames := by decide

/-- **The ladder addition slot fold carries `jacAddSpec` in the output slots,
    from the input slots alone.** When `V` matches the `addEnv0` entry
    environment on the six input-coordinate slots — nothing is asked of the
    output slots `6,7,8` or of the intermediate slots — the slot fold's values
    in the `Xp`/`Yp`/`Zp` slots are `jacAddSpec X1 Y1 Z1 X2 Y2 Z2`. -/
theorem ladAdd_framed_realizes_inputs (V : Nat → Nat) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hV0 : ∀ m ∈ addInputs, V (slotLadAdd m) = addEnv0 X1 Y1 Z1 X2 Y2 Z2 m) :
    (scheduleEvalFramed slotLadAdd jacAddSchedule V (slotLadAdd "Xp"),
     scheduleEvalFramed slotLadAdd jacAddSchedule V (slotLadAdd "Yp"),
     scheduleEvalFramed slotLadAdd jacAddSchedule V (slotLadAdd "Zp"))
      = jacAddSpec X1 Y1 Z1 X2 Y2 Z2 := by
  have hb := scheduleEvalFramed_bridge_of_inputs slotLadAdd_inj jacAddSchedule addInputs
    addInputs_sub jacAddSchedule_schedNamed jacAddSchedule_writeBeforeRead
    V (addEnv0 X1 Y1 Z1 X2 Y2 Z2) hV0
  rw [hb "Xp" (by decide), hb "Yp" (by decide), hb "Zp" (by decide)]
  exact jacAddSchedule_realizes_spec X1 Y1 Z1 X2 Y2 Z2

/-- **The ladder-step addition segment computes `jacAddSpec` in its output
    slots, from its input slots alone.** `ladAddBody_spec` with the entry
    hypothesis restricted to the six input-coordinate slots `3,4,5` and
    `9,10,11`, so a frame whose output slots `6,7,8` still hold an earlier
    trip's sum row and whose intermediate slots `31..50` still hold an earlier
    trip's values satisfies it. -/
theorem ladAddBody_spec_inputs {env env' : SEnvScalar}
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat} (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V 51)
    (hVlt : ∀ s, s < 51 → V s < pNat)
    (hV0 : ∀ m ∈ addInputs, V (slotLadAdd m) = addEnv0 X1 Y1 Z1 X2 Y2 Z2 m)
    (hrun : semScalar ladAddBody env = some env') :
    ∃ fr : Fin 256 → BitVec 64, env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr (scheduleEvalFramed slotLadAdd jacAddSchedule V) 51 ∧
      (∀ s, s < 51 → scheduleEvalFramed slotLadAdd jacAddSchedule V s < pNat) ∧
      slotVal fr (slotLadAdd "Xp") = (jacAddSpec X1 Y1 Z1 X2 Y2 Z2).1 ∧
      slotVal fr (slotLadAdd "Yp") = (jacAddSpec X1 Y1 Z1 X2 Y2 Z2).2.1 ∧
      slotVal fr (slotLadAdd "Zp") = (jacAddSpec X1 Y1 Z1 X2 Y2 Z2).2.2 := by
  obtain ⟨fr, hF', hFrame', hVlt'⟩ :=
    ladAddBody_cells hF hFrame hVlt (by intro s hs; omega)
      (jacAddSchedule_framedOpOk_lad (by norm_num) (by norm_num)) hrun
  have hTuple := ladAdd_framed_realizes_inputs V X1 Y1 Z1 X2 Y2 Z2 hV0
  refine ⟨fr, hF', hFrame', hVlt', ?_, ?_, ?_⟩
  · rw [hFrame' (slotLadAdd "Xp") (by decide)]; exact congrArg Prod.fst hTuple
  · rw [hFrame' (slotLadAdd "Yp") (by decide)]; exact congrArg (fun p => p.2.1) hTuple
  · rw [hFrame' (slotLadAdd "Zp") (by decide)]; exact congrArg (fun p => p.2.2) hTuple

/-- **The ladder addition slot fold carries `jacAddSpec` in the output slots.**
    `ladAdd_framed_realizes_inputs` with the entry hypothesis asked of every
    addition name rather than of the six inputs. -/
theorem ladAdd_framed_realizes (V : Nat → Nat) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hV0 : ∀ m ∈ addNames, V (slotLadAdd m) = addEnv0 X1 Y1 Z1 X2 Y2 Z2 m) :
    (scheduleEvalFramed slotLadAdd jacAddSchedule V (slotLadAdd "Xp"),
     scheduleEvalFramed slotLadAdd jacAddSchedule V (slotLadAdd "Yp"),
     scheduleEvalFramed slotLadAdd jacAddSchedule V (slotLadAdd "Zp"))
      = jacAddSpec X1 Y1 Z1 X2 Y2 Z2 :=
  ladAdd_framed_realizes_inputs V X1 Y1 Z1 X2 Y2 Z2
    (fun m hm => hV0 m (addInputs_sub m hm))

/-- **The ladder-step addition segment computes `jacAddSpec` in its output
    slots.** `ladAddBody_spec_inputs` with the entry hypothesis asked of every
    addition name rather than of the six inputs: running `ladAddBody` from a
    frame satisfying `FrameSlots arr V 51` whose slots match the `addEnv0` entry
    environment on the addition names and are below the prime lands a frame
    whose `Xp`/`Yp`/`Zp` slots (`6,7,8` — the sum slots) hold
    `jacAddSpec X1 Y1 Z1 X2 Y2 Z2`. -/
theorem ladAddBody_spec {env env' : SEnvScalar}
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat} (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V 51)
    (hVlt : ∀ s, s < 51 → V s < pNat)
    (hV0 : ∀ m ∈ addNames, V (slotLadAdd m) = addEnv0 X1 Y1 Z1 X2 Y2 Z2 m)
    (hrun : semScalar ladAddBody env = some env') :
    ∃ fr : Fin 256 → BitVec 64, env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr (scheduleEvalFramed slotLadAdd jacAddSchedule V) 51 ∧
      (∀ s, s < 51 → scheduleEvalFramed slotLadAdd jacAddSchedule V s < pNat) ∧
      slotVal fr (slotLadAdd "Xp") = (jacAddSpec X1 Y1 Z1 X2 Y2 Z2).1 ∧
      slotVal fr (slotLadAdd "Yp") = (jacAddSpec X1 Y1 Z1 X2 Y2 Z2).2.1 ∧
      slotVal fr (slotLadAdd "Zp") = (jacAddSpec X1 Y1 Z1 X2 Y2 Z2).2.2 :=
  ladAddBody_spec_inputs X1 Y1 Z1 X2 Y2 Z2 hF hFrame hVlt
    (fun m hm => hV0 m (addInputs_sub m hm)) hrun

/-! ## 7. Scalar-assignment chains, read back as values -/

/-- **A chain of scalar assignments over pairwise-distinct names none of whose
    expressions read a chain output, read back as values.** Each written name
    ends holding its expression's word evaluated at the entry environment, and
    every other non-temporary slot is unchanged. -/
theorem setExprChain_values (nm : Nat → String) (ex : Nat → SExpr)
    (hnt : ∀ k, ¬ isTmpName (nm k))
    (hinj : ∀ k j, k ≠ j → nm k ≠ nm j)
    (hvne : ∀ k j, ∀ v ∈ sexprVars (ex k), v ≠ nm j)
    (hvnt : ∀ k, ∀ v ∈ sexprVars (ex k), ¬ isTmpName v) :
    ∀ (n : Nat) {env env' : SEnvScalar},
      semScalar (seqAll ((List.range n).map (fun k => LowCT.RScalarSetExpr (nm k) (ex k)))) env
        = some env' →
      (∀ k, k < n → env' (nm k) = some ⟨.sword 64, SExpr.evalBV (envReader env) (ex k)⟩)
        ∧ (∀ t, ¬ isTmpName t → (∀ j, j < n → t ≠ nm j) → env' t = env t) := by
  intro n
  induction n with
  | zero =>
      intro env env' hsem
      obtain rfl : env' = env := by simpa using (Option.some.inj hsem).symm
      exact ⟨fun k hk => absurd hk (by omega), fun _ _ _ => rfl⟩
  | succ n ih =>
      intro env env' hsem
      rw [show (List.range (n + 1)).map (fun k => LowCT.RScalarSetExpr (nm k) (ex k))
            = (List.range n).map (fun k => LowCT.RScalarSetExpr (nm k) (ex k))
              ++ [LowCT.RScalarSetExpr (nm n) (ex n)] from by
            rw [List.range_succ, List.map_append]; rfl,
          semScalar_seqAll_append] at hsem
      obtain ⟨E1, hpre, htail⟩ := Option.bind_eq_some_iff.mp hsem
      rw [show seqAll [LowCT.RScalarSetExpr (nm n) (ex n)]
            = LowCT.RScalarSetExpr (nm n) (ex n) from rfl] at htail
      obtain ⟨hval1, hkeep1⟩ := ih hpre
      obtain ⟨hat, hoff⟩ := semScalar_setExpr_eq htail
      have hev : SExpr.evalBV (envReader E1) (ex n) = SExpr.evalBV (envReader env) (ex n) :=
        evalBV_congr_vars _ _ (ex n) (fun v hv => by
          simp only [envReader, hkeep1 v (hvnt n v hv) (fun j _ => hvne n j v hv)])
      refine ⟨?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · rw [hoff (nm k) (hnt k) (hinj k n (by omega))]
          exact hval1 k h
        · subst h
          rw [hat, hev]
      · intro t hnt' hne
        rw [hoff t hnt' (hne n (by omega)), hkeep1 t hnt' (fun j hj => hne j (by omega))]

/-! ## 8. The branch-free word select -/

/-- **The per-limb branch-free select is a mux.** With a `{0,1}` selector word and
    32-bit operands, `B ^^^ ((A ^^^ B) &&& (bit · 0xFFFFFFFF))` selects `A` at
    `bit = 1` and `B` at `bit = 0`. -/
theorem selWord_mux {A B bit : BitVec 64} (hbit : bit = 0 ∨ bit = 1)
    (hA : A.toNat < 2 ^ 32) (hB : B.toNat < 2 ^ 32) :
    B ^^^ ((A ^^^ B) &&& (bit * BitVec.ofNat 64 4294967295))
      = if bit = 1 then A else B := by
  rcases hbit with rfl | rfl
  · simp
  · rw [ite_eq_left rfl,
      show (1 : BitVec 64) * BitVec.ofNat 64 4294967295 = BitVec.ofNat 64 4294967295 from by
        decide]
    have hxlt : (A ^^^ B).toNat < 2 ^ 32 := by
      rw [BitVec.toNat_xor]
      exact Nat.xor_lt_two_pow hA hB
    have hmask : (A ^^^ B) &&& BitVec.ofNat 64 4294967295 = A ^^^ B := by
      apply BitVec.eq_of_toNat_eq
      rw [show (BitVec.ofNat 64 4294967295) = BitVec.ofNat 64 mask32 from rfl, half_lo]
      exact Nat.mod_eq_of_lt hxlt
    rw [hmask, BitVec.xor_comm A B, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-! ## 9. Name algebra for the select brick -/

/-- A half-limb slot of a sibling field element and a `Sel`-result name of the
    same brick differ. -/
theorem hSlotNeSel {pfx t : String} {ct : Char} (ht : hd t = some ct) (hne : ct ≠ 'S')
    (k j : Nat) : s!"{pfx ++ t}h{k}" ≠ s!"{pfx}Sel{j}" := by
  have e1 : s!"{pfx ++ t}h{k}" = pfx ++ (t ++ ("h" ++ toString k)) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx}Sel{j}" = pfx ++ ("Sel" ++ toString j) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e1, e2]
  exact pfxNe (neOfHd (hdAppend ht) (hdAppend rfl) hne)

/-- A half-limb slot of a sibling field element and the brick's selector-index
    name differ. -/
theorem hSlotNeIxbit {pfx t : String} {ct : Char} (ht : hd t = some ct) (hne : ct ≠ 'i')
    (k : Nat) : s!"{pfx ++ t}h{k}" ≠ s!"{pfx}ixbit" := by
  have e1 : s!"{pfx ++ t}h{k}" = pfx ++ (t ++ ("h" ++ toString k)) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx}ixbit" = pfx ++ "ixbit" := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl]
  rw [e1, e2]
  exact pfxNe (neOfHd (hdAppend ht) rfl hne)

/-- A half-limb slot of a sibling field element and the brick's selector-word
    name differ. -/
theorem hSlotNeBit {pfx t : String} {ct : Char} (ht : hd t = some ct) (hne : ct ≠ 'b')
    (k : Nat) : s!"{pfx ++ t}h{k}" ≠ s!"{pfx}bit" := by
  have e1 : s!"{pfx ++ t}h{k}" = pfx ++ (t ++ ("h" ++ toString k)) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx}bit" = pfx ++ "bit" := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl]
  rw [e1, e2]
  exact pfxNe (neOfHd (hdAppend ht) rfl hne)

/-- The brick's selector-word name and a `Sel`-result name differ. -/
theorem bitNeSel {pfx : String} (j : Nat) : s!"{pfx}bit" ≠ s!"{pfx}Sel{j}" := by
  have e1 : s!"{pfx}bit" = pfx ++ "bit" := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl]
  have e2 : s!"{pfx}Sel{j}" = pfx ++ ("Sel" ++ toString j) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e1, e2]
  exact pfxNe (neOfHd rfl (hdAppend rfl) (by decide))

/-- A `Sel`-result name and an `Oh`-output slot of the same brick differ. -/
theorem selNeOh {pfx : String} (k j : Nat) : s!"{pfx}Sel{k}" ≠ s!"{pfx}Oh{j}" := by
  have e1 : s!"{pfx}Sel{k}" = pfx ++ ("Sel" ++ toString k) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx}Oh{j}" = pfx ++ ("Oh" ++ toString j) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e1, e2]
  exact pfxNe (neOfHd (hdAppend rfl) (hdAppend rfl) (by decide))

/-! ## 10. The framed select brick, as a frame-slot value -/

/-- **One framed select brick writes the mux of its two candidate slots.**
    Running `emitSelectFramed` on the 256-cell ladder frame, from a frame whose
    selector word (the first cell of slot `s`) is `0` or `1`, lands a frame whose
    output slot holds the `a`-candidate slot value at selector `1` and the
    `b`-candidate slot value at selector `0`; every cell outside the output
    slot's four-cell window is unchanged. -/
theorem emitSelectFramed_value {slotOf : String → Nat} (idx : Nat) (s a b o : String)
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat} {active : Nat} {env env' : SEnvScalar}
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V active)
    (hAcap : 4 * slotOf a + 4 ≤ 2 ^ 64) (hBcap : 4 * slotOf b + 4 ≤ 2 ^ 64)
    (hscap : 4 * slotOf s < 2 ^ 64) (hso4 : 4 * slotOf o + 4 ≤ 256)
    (hactive : ∀ t, t < active → 4 * t + 4 ≤ 256)
    (hAact : slotOf a < active) (hBact : slotOf b < active)
    (hAlt : V (slotOf a) < pNat) (hBlt : V (slotOf b) < pNat)
    (hbit : memGetDyn arr (4 * slotOf s) = 0 ∨ memGetDyn arr (4 * slotOf s) = 1)
    (hrun : semScalar (seqAll (emitSelectFramed (8 * ladderFrameCells) slotOf idx s a b o))
        env = some env') :
    ∃ fr : Fin 256 → BitVec 64,
      env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr (Function.update V (slotOf o)
        (if memGetDyn arr (4 * slotOf s) = 1 then V (slotOf a) else V (slotOf b))) active ∧
      (∀ m : Fin 256, m.val < 4 * slotOf o ∨ 4 * slotOf o + 4 ≤ m.val → fr m = arr m) := by
  simp only [emitSelectFramed] at hrun
  set pfx := s!"fop{idx}" with hpfxdef
  have hdpfx : hd pfx = some 'f' := hdAppend rfl
  have hdF : hd "F" = some 'F' := rfl
  have hdIxbit : hd s!"{pfx}ixbit" = some 'f' := hdAppend hdpfx
  have hdBit : hd s!"{pfx}bit" = some 'f' := hdAppend hdpfx
  have hdSel : ∀ k : Nat, hd s!"{pfx}Sel{k}" = some 'f' := fun _ => hdAppend (hdAppend hdpfx)
  have hdOh : ∀ k : Nat, hd s!"{pfx}Oh{k}" = some 'f' := fun _ => hdAppend (hdAppend hdpfx)
  have hdAh : ∀ k : Nat, hd (feHN (pfx ++ "A") k) = some 'f' :=
    fun _ => hdAppend (hdAppend (hdAppend hdpfx))
  have hdBh : ∀ k : Nat, hd (feHN (pfx ++ "B") k) = some 'f' :=
    fun _ => hdAppend (hdAppend (hdAppend hdpfx))
  have hFnt : ¬ isTmpName "F" := notTmp_of_len "F" (by decide)
  -- split the emitted brick: prefix / body / copies / store
  rw [semScalar_seqAll_append, semScalar_seqAll_append, semScalar_seqAll_append] at hrun
  obtain ⟨Ed, hPBC, hstore⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨Ec, hPB, hcopy⟩ := Option.bind_eq_some_iff.mp hPBC
  obtain ⟨E3, hpre, hbody⟩ := Option.bind_eq_some_iff.mp hPB
  -- the constant/index/operand-load prefix, read back
  obtain ⟨hFE3, -, hvalA, hvalB, hltA, hltB, hixO⟩ :=
    framedPrefix (N := 256) idx a b o (show ("F").toList = 'F' :: [] from rfl)
      hFnt (by decide) (by decide) (by decide) (by decide) (by decide) hAcap hBcap hF hpre
  -- the brick body: the selector-index bind, the selector load, the eight selects
  simp only [selBody] at hbody
  rw [semScalar_seqAll_cons] at hbody
  obtain ⟨Ea, hc1, hbody2⟩ := Option.bind_eq_some_iff.mp hbody
  rw [semScalar_seqAll_cons] at hbody2
  obtain ⟨Eb, hc2, hchain⟩ := Option.bind_eq_some_iff.mp hbody2
  obtain ⟨hIxAt, hc1Keep⟩ := semScalar_setExpr_eq hc1
  have hIxVal : Ea s!"{pfx}ixbit" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf s)⟩ := hIxAt
  have hFEa : Ea "F" = some ⟨.memref 256, arr⟩ := by
    rw [hc1Keep "F" hFnt (neOfHd hdF hdIxbit (by decide))]; exact hFE3
  simp only [semScalar, hFEa, hIxVal] at hc2
  have hc2' := Option.some.inj hc2
  have hIxToNat : (BitVec.ofNat 64 (4 * slotOf s)).toNat = 4 * slotOf s := ofNat_toNat hscap
  have hEbOff : ∀ t : String, t ≠ s!"{pfx}bit" → Eb t = Ea t := by
    intro t ht
    rw [← hc2']
    simp only [SEnvScalar.upd, ite_eq_right ht]
  have hBitVal : Eb s!"{pfx}bit" = some ⟨.sword 64, memGetDyn arr (4 * slotOf s)⟩ := by
    rw [← hc2', hIxToNat]
    simp [SEnvScalar.upd]
  have hName3 : ∀ t : String, ¬ isTmpName t → t ≠ s!"{pfx}ixbit" → t ≠ s!"{pfx}bit" →
      Eb t = E3 t := fun t hnt h1 h2 => by rw [hEbOff t h2, hc1Keep t hnt h1]
  -- the eight selects, read back as mux words
  obtain ⟨hSelVal, hchainKeep⟩ :=
    setExprChain_values (fun k => s!"{pfx}Sel{k}")
      (fun k => .SXor (sv s!"{pfx ++ "B"}h{k}")
        (.SAnd (.SXor (sv s!"{pfx ++ "A"}h{k}") (sv s!"{pfx ++ "B"}h{k}"))
          (.SMul (sv s!"{pfx}bit") (.SLit 4294967295))))
      (fun k => (headOk_of_hd (hdSel k) (by decide)).notTmp)
      (fun k j hkj he => hkj (slot_inj he))
      (fun k j v hv => by
        simp only [sv, sexprVars, List.mem_append, List.mem_singleton, List.not_mem_nil,
          or_false] at hv
        rcases hv with rfl | (rfl | rfl) | rfl
        · exact hSlotNeSel rfl (by decide) k j
        · exact hSlotNeSel rfl (by decide) k j
        · exact hSlotNeSel rfl (by decide) k j
        · exact bitNeSel j)
      (fun k v hv => by
        simp only [sv, sexprVars, List.mem_append, List.mem_singleton, List.not_mem_nil,
          or_false] at hv
        rcases hv with rfl | (rfl | rfl) | rfl
        · exact (headOk_of_hd (hdBh k) (by decide)).notTmp
        · exact (headOk_of_hd (hdAh k) (by decide)).notTmp
        · exact (headOk_of_hd (hdBh k) (by decide)).notTmp
        · exact (headOk_of_hd hdBit (by decide)).notTmp)
      8 hchain
  -- operand half-limbs and the selector survive to the select entry
  have hAhKeep : ∀ k : Nat, Eb (feHN (pfx ++ "A") k) = E3 (feHN (pfx ++ "A") k) :=
    fun k => hName3 (feHN (pfx ++ "A") k) ((headOk_of_hd (hdAh k) (by decide)).notTmp)
      (hSlotNeIxbit rfl (by decide) k) (hSlotNeBit rfl (by decide) k)
  have hBhKeep : ∀ k : Nat, Eb (feHN (pfx ++ "B") k) = E3 (feHN (pfx ++ "B") k) :=
    fun k => hName3 (feHN (pfx ++ "B") k) ((headOk_of_hd (hdBh k) (by decide)).notTmp)
      (hSlotNeIxbit rfl (by decide) k) (hSlotNeBit rfl (by decide) k)
  have hAhEb : ∀ k : Nat, envReader Eb (feHN (pfx ++ "A") k)
      = envReader E3 (feHN (pfx ++ "A") k) := fun k => by simp only [envReader, hAhKeep k]
  have hBhEb : ∀ k : Nat, envReader Eb (feHN (pfx ++ "B") k)
      = envReader E3 (feHN (pfx ++ "B") k) := fun k => by simp only [envReader, hBhKeep k]
  have hBitEb : envReader Eb s!"{pfx}bit" = memGetDyn arr (4 * slotOf s) :=
    envReader_of_bound hBitVal
  -- each select result is the per-limb mux
  have hSelWord : ∀ k : Nat, k < 8 →
      SExpr.evalBV (envReader Eb)
        (.SXor (sv s!"{pfx ++ "B"}h{k}")
          (.SAnd (.SXor (sv s!"{pfx ++ "A"}h{k}") (sv s!"{pfx ++ "B"}h{k}"))
            (.SMul (sv s!"{pfx}bit") (.SLit 4294967295))))
        = (if memGetDyn arr (4 * slotOf s) = 1
            then envReader E3 (feHN (pfx ++ "A") k)
            else envReader E3 (feHN (pfx ++ "B") k)) := by
    intro k hk
    simp only [SExpr.evalBV, sv, feHN_eq, hAhEb k, hBhEb k, hBitEb]
    exact selWord_mux hbit (hltA k hk) (hltB k hk)
  -- the copy block, read back
  have hrnEq : ∀ k : Nat, k < 8 →
      (selBody (8 * ladderFrameCells) (4 * slotOf s) pfx).2[k]! = s!"{pfx}Sel{k}" := by
    intro k hk
    simp only [selBody]
    exact map_range_getBang 8 _ k hk
  obtain ⟨hOhval, hcopyKeep⟩ :=
    framedCopy_run pfx (fun k => (selBody (8 * ladderFrameCells) (4 * slotOf s) pfx).2[k]!)
      (fun k _ => (headOk_of_hd (hdOh k) (by decide)).notTmp)
      (fun k j _ _ hne he => hne (slot_inj he))
      (fun k hk => by
        show ¬ isTmpName ((selBody (8 * ladderFrameCells) (4 * slotOf s) pfx).2[k]!)
        rw [hrnEq k hk]; exact (headOk_of_hd (hdSel k) (by decide)).notTmp)
      (fun k j hk _ => by
        show (selBody (8 * ladderFrameCells) (4 * slotOf s) pfx).2[k]! ≠ s!"{pfx}Oh{j}"
        rw [hrnEq k hk]; exact selNeOh k j)
      Ec 8 (le_refl 8) Ed hcopy
  -- the mux limb each output slot carries
  have hRnVal : ∀ k : Nat, k < 8 →
      envReader Ec ((selBody (8 * ladderFrameCells) (4 * slotOf s) pfx).2[k]!)
        = (if memGetDyn arr (4 * slotOf s) = 1
            then envReader E3 (feHN (pfx ++ "A") k)
            else envReader E3 (feHN (pfx ++ "B") k)) := by
    intro k hk
    rw [hrnEq k hk, envReader_of_bound (hSelVal k hk), hSelWord k hk]
  -- frame and output cell indices survive to the store
  have hFEc : Ec "F" = some ⟨.memref 256, arr⟩ := by
    rw [hchainKeep "F" hFnt (fun j _ => neOfHd hdF (hdSel j) (by decide)),
      hName3 "F" hFnt (neOfHd hdF hdIxbit (by decide)) (neOfHd hdF hdBit (by decide))]
    exact hFE3
  have hFEd : Ed "F" = some ⟨.memref 256, arr⟩ := by
    rw [hcopyKeep "F" hFnt (fun j _ => neOfHd hdF (hdOh j) (by decide))]
    exact hFEc
  have hixNt : ∀ c : Nat, ¬ isTmpName s!"ix{c}" :=
    fun c => (headOk_of_hd (hd_ix c) (by decide)).notTmp
  have hixOEd : ∀ j : Nat, j < 4 → Ed s!"ix{4 * slotOf o + j}"
      = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf o + j)⟩ := by
    intro j hj
    rw [hcopyKeep _ (hixNt _) (fun j' _ => neOfHd (hd_ix _) (hdOh j') (by decide)),
      hchainKeep _ (hixNt _) (fun j' _ => neOfHd (hd_ix _) (hdSel j') (by decide)),
      hName3 _ (hixNt _) (neOfHd (hd_ix _) hdIxbit (by decide))
        (neOfHd (hd_ix _) hdBit (by decide))]
    exact hixO j hj
  -- the output field element at the store entry
  have hOhEq : ∀ k : Nat, feHN (pfx ++ "O") k = s!"{pfx}Oh{k}" :=
    fun k => (feHN_eq _ _).symm.trans (oh_bridge _ _).symm
  have hbnd : ∀ k, k < 8 → Ed (feHN (pfx ++ "O") k)
      = some ⟨.sword 64, envReader Ed (feHN (pfx ++ "O") k)⟩ := by
    intro k hk
    have hb := hOhval k hk
    rw [hOhEq k, hb, envReader_of_bound hb]
  have hltO : ∀ k, k < 8 → (envReader Ed (feHN (pfx ++ "O") k)).toNat < 2 ^ 32 := by
    intro k hk
    rw [hOhEq k, envReader_of_bound (hOhval k hk), hRnVal k hk]
    split
    · exact hltA k hk
    · exact hltB k hk
  have hfeValO : feVal Ed (pfx ++ "O")
      = (if memGetDyn arr (4 * slotOf s) = 1
          then slotVal arr (slotOf a) else slotVal arr (slotOf b)) := by
    have hOh : ∀ k, k < 8 → (envReader Ed (feHN (pfx ++ "O") k)).toNat
        = ((if memGetDyn arr (4 * slotOf s) = 1
            then envReader E3 (feHN (pfx ++ "A") k)
            else envReader E3 (feHN (pfx ++ "B") k))).toNat := by
      intro k hk
      rw [hOhEq k, envReader_of_bound (hOhval k hk), hRnVal k hk]
    rcases hbit with h0 | h1
    · have hne : ¬ memGetDyn arr (4 * slotOf s) = 1 := by rw [h0]; decide
      rw [ite_eq_right hne]
      calc feVal Ed (pfx ++ "O")
          = accN (fun k => (envReader Ed (feHN (pfx ++ "O") k)).toNat) 8 :=
            feVal_eq_accN Ed (pfx ++ "O")
        _ = accN (fun k => (envReader E3 (feHN (pfx ++ "B") k)).toNat) 8 :=
            accN_congr 8 (fun k hk => by rw [hOh k hk, ite_eq_right hne])
        _ = feVal E3 (pfx ++ "B") := (feVal_eq_accN E3 (pfx ++ "B")).symm
        _ = slotVal arr (slotOf b) := hvalB
    · rw [ite_eq_left h1]
      calc feVal Ed (pfx ++ "O")
          = accN (fun k => (envReader Ed (feHN (pfx ++ "O") k)).toNat) 8 :=
            feVal_eq_accN Ed (pfx ++ "O")
        _ = accN (fun k => (envReader E3 (feHN (pfx ++ "A") k)).toNat) 8 :=
            accN_congr 8 (fun k hk => by rw [hOh k hk, ite_eq_left h1])
        _ = feVal E3 (pfx ++ "A") := (feVal_eq_accN E3 (pfx ++ "A")).symm
        _ = slotVal arr (slotOf a) := hvalA
  have hrvlt : (if memGetDyn arr (4 * slotOf s) = 1
      then slotVal arr (slotOf a) else slotVal arr (slotOf b)) < 2 ^ 256 := by
    have ha' : slotVal arr (slotOf a) < 2 ^ 256 := by
      rw [hFrame (slotOf a) hAact]; exact lt_trans hAlt pNat_lt_pow256
    have hb' : slotVal arr (slotOf b) < 2 ^ 256 := by
      rw [hFrame (slotOf b) hBact]; exact lt_trans hBlt pNat_lt_pow256
    split <;> assumption
  -- the store
  have hso4' : 4 * slotOf o + 4 ≤ (8 * ladderFrameCells + 7) / 8 := by
    simpa [ladderFrameCells] using hso4
  obtain ⟨envF, fr, hstoreF, hbfr, hhit, hmiss⟩ :=
    storeFieldTo_cells (fw := 8 * ladderFrameCells) (o := 4 * slotOf o)
      (headF_toList (hdAppend hdpfx)) (by decide) (by decide)
      (show ("F").toList = 'F' :: [] from rfl) (by decide) hFnt (by decide)
      hso4' (by decide) hFEd hixOEd hbnd hltO
  obtain rfl : env' = envF := Option.some.inj (hstore.symm.trans hstoreF)
  refine ⟨fr, hbfr, ?_, fun m hm => hmiss m hm⟩
  intro t ht
  by_cases hto : t = slotOf o
  · subst hto
    rw [Function.update_self,
      slotVal_hit (N := 256) fr (slotOf o) _ hrvlt hso4
        (fun j hj m hm => by rw [hhit j hj m hm, hfeValO]),
      hFrame (slotOf a) hAact, hFrame (slotOf b) hBact]
  · rw [Function.update_of_ne hto, ← hFrame t ht,
      slotVal_miss (N := 256) fr arr (slotOf o) t (hactive t ht) hto
        (fun m hm => hmiss m hm)]

/-! ## 11. The select trip, as frame-slot values -/

/-- **The select trip writes the mux of the two computed rows into the
    accumulator slots.** Running `selectTrip` from a frame whose selector word
    (the first cell of slot `51`) is `0` or `1` lands a frame whose accumulator
    slots `(accX, accY, accZ)` hold the sum row at selector `1` and the doubled
    row at selector `0`; every cell above the accumulator slots' twelve-cell
    window `[0, 12)` is unchanged. -/
theorem selectTrip_spec {env env' : SEnvScalar}
    {arr : Fin 256 → BitVec 64} {V : Nat → Nat}
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hFrame : FrameSlots arr V 51)
    (hVlt : ∀ t, t < 51 → V t < pNat)
    (hbit : memGetDyn arr (4 * slotLadSel "bit") = 0
      ∨ memGetDyn arr (4 * slotLadSel "bit") = 1)
    (hrun : semScalar (seqAll selectTrip) env = some env') :
    ∃ fr : Fin 256 → BitVec 64,
      env' "F" = some ⟨.memref 256, fr⟩ ∧
      FrameSlots fr
        (Function.update (Function.update (Function.update V
          (slotLadSel "accX") (if memGetDyn arr (4 * slotLadSel "bit") = 1
            then V (slotLadSel "sumX") else V (slotLadSel "midX")))
          (slotLadSel "accY") (if memGetDyn arr (4 * slotLadSel "bit") = 1
            then V (slotLadSel "sumY") else V (slotLadSel "midY")))
          (slotLadSel "accZ") (if memGetDyn arr (4 * slotLadSel "bit") = 1
            then V (slotLadSel "sumZ") else V (slotLadSel "midZ"))) 51 ∧
      (∀ m : Fin 256, 4 * slotLadSel "accZ" + 4 ≤ m.val → fr m = arr m) := by
  have e0 : slotLadSel "accX" = 0 := by decide
  have e1 : slotLadSel "accY" = 1 := by decide
  have e2 : slotLadSel "accZ" = 2 := by decide
  have e3 : slotLadSel "midX" = 3 := by decide
  have e4 : slotLadSel "midY" = 4 := by decide
  have e5 : slotLadSel "midZ" = 5 := by decide
  have e6 : slotLadSel "sumX" = 6 := by decide
  have e7 : slotLadSel "sumY" = 7 := by decide
  have e8 : slotLadSel "sumZ" = 8 := by decide
  have e51 : slotLadSel "bit" = 51 := by decide
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e51]
  rw [e51] at hbit
  simp only [selectTrip] at hrun
  rw [semScalar_seqAll_append, semScalar_seqAll_append] at hrun
  obtain ⟨env01, h01, h2run⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨env0, h0run, h1run⟩ := Option.bind_eq_some_iff.mp h01
  -- select 0: accX := bit ? sumX : midX
  obtain ⟨fr0, hF0, hFrame0, hmiss0⟩ :=
    emitSelectFramed_value 0 "bit" "sumX" "midX" "accX" hF hFrame
      (by decide) (by decide) (by decide) (by decide) (fun t ht => by omega)
      (by decide) (by decide) (hVlt _ (by decide)) (hVlt _ (by decide))
      (by rw [e51]; exact hbit) h0run
  rw [e0, e6, e3, e51] at hFrame0
  rw [e0] at hmiss0
  -- the selector cell survives the accX-slot store
  have hbitc0 : memGetDyn fr0 (4 * 51) = memGetDyn arr (4 * 51) := by
    rw [memGetDyn_lt fr0 (by omega : 4 * 51 < 256),
      memGetDyn_lt arr (by omega : 4 * 51 < 256)]
    exact hmiss0 ⟨4 * 51, by omega⟩
      (show (4 * 51 : Nat) < 4 * 0 ∨ 4 * 0 + 4 ≤ 4 * 51 by omega)
  -- select 1: accY := bit ? sumY : midY
  obtain ⟨fr1, hF1, hFrame1, hmiss1⟩ :=
    emitSelectFramed_value 1 "bit" "sumY" "midY" "accY" hF0 hFrame0
      (by decide) (by decide) (by decide) (by decide) (fun t ht => by omega)
      (by decide) (by decide)
      (by rw [e7, Function.update_of_ne (by omega : (7 : Nat) ≠ 0)]
          exact hVlt 7 (by omega))
      (by rw [e4, Function.update_of_ne (by omega : (4 : Nat) ≠ 0)]
          exact hVlt 4 (by omega))
      (by rw [e51, hbitc0]; exact hbit) h1run
  rw [e1, e7, e4, e51, hbitc0,
    Function.update_of_ne (by omega : (7 : Nat) ≠ 0),
    Function.update_of_ne (by omega : (4 : Nat) ≠ 0)] at hFrame1
  rw [e1] at hmiss1
  -- the selector cell survives the accY-slot store
  have hbitc1 : memGetDyn fr1 (4 * 51) = memGetDyn arr (4 * 51) := by
    rw [memGetDyn_lt fr1 (by omega : 4 * 51 < 256),
      memGetDyn_lt arr (by omega : 4 * 51 < 256),
      hmiss1 ⟨4 * 51, by omega⟩
        (show (4 * 51 : Nat) < 4 * 1 ∨ 4 * 1 + 4 ≤ 4 * 51 by omega),
      hmiss0 ⟨4 * 51, by omega⟩
        (show (4 * 51 : Nat) < 4 * 0 ∨ 4 * 0 + 4 ≤ 4 * 51 by omega)]
  -- select 2: accZ := bit ? sumZ : midZ
  obtain ⟨fr2, hF2, hFrame2, hmiss2⟩ :=
    emitSelectFramed_value 2 "bit" "sumZ" "midZ" "accZ" hF1 hFrame1
      (by decide) (by decide) (by decide) (by decide) (fun t ht => by omega)
      (by decide) (by decide)
      (by rw [e8, Function.update_of_ne (by omega : (8 : Nat) ≠ 1),
            Function.update_of_ne (by omega : (8 : Nat) ≠ 0)]
          exact hVlt 8 (by omega))
      (by rw [e5, Function.update_of_ne (by omega : (5 : Nat) ≠ 1),
            Function.update_of_ne (by omega : (5 : Nat) ≠ 0)]
          exact hVlt 5 (by omega))
      (by rw [e51, hbitc1]; exact hbit) h2run
  rw [e2, e8, e5, e51, hbitc1,
    Function.update_of_ne (by omega : (8 : Nat) ≠ 1),
    Function.update_of_ne (by omega : (8 : Nat) ≠ 0),
    Function.update_of_ne (by omega : (5 : Nat) ≠ 1),
    Function.update_of_ne (by omega : (5 : Nat) ≠ 0)] at hFrame2
  rw [e2] at hmiss2
  refine ⟨fr2, hF2, hFrame2, ?_⟩
  intro m hm
  rw [hmiss2 m (by omega), hmiss1 m (by omega), hmiss0 m (by omega)]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LadderSlotValue
