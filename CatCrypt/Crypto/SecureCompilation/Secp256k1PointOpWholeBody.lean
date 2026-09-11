/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpEpilogue
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue

/-!
# The whole `jacDbl` body, from the input point frame to the output cells

`Secp256k1PointOpFront.jacDblBody` is the prologue (index slots, reduction
constants, three coordinate loads), the doubling schedule, and the three
`storeField` blocks. This module joins the three stages into one statement about
the array the final environment holds at `out`.

## The slot-boundness obligation

`Secp256k1PointOpEpilogue.pointOpEpilogue_cells` reads each output field
element's eight half-limb slots through the `SExpr` lowering, which declines an
unbound name, so it asks for those slots to be *bound* at 64-bit word type.
`Secp256k1FeAddSubBrick.BrickScope.limbs` does not give that: it bounds
`envReader`, which returns `0` on an unbound name. Boundness comes instead from
the schedule having written the slots — the copy block `wireBody` at the end of
each emitted brick binds the output field element's eight slots, and a later
brick, whose commands are all scalar assignments, cannot unbind them.

## Main results

* `SlotsBound`, `slotsBound_reads` — a field element's eight half-limb slots
  bound at `.sword 64`, and the form the store block reads them in.
* `env_seqAll_frame`, `bound_seqAll` — a command list that binds only `P`-names
  leaves every other non-temporary slot alone, and never unbinds a word slot.
* `Extends`, `fopOut`, `BrickWrites` — a private-prefix namespace, a schedule
  entry's output field element, and the names one emitted brick binds.
* `emitFOp_writes` — each emitted brick binds only names extending its private
  `op{idx}` prefix and the output field element's half-limb slots. The three
  per-brick write sets it composes live in `Secp256k1FeMulBrickFrame`.
* `wireBody_bound`, `emitFOp_bound_out` — the copy block at the end of a brick
  binds the output field element's eight half-limb slots.
* `brickFold_slotsBound_pres`, `brickFold_slotsBound`,
  `jacDblSchedule_slotsBound` — boundness survives later bricks, and a field
  element written by some schedule entry is bound at the schedule's exit.
* `brickFold_frame`, `jacDblSchedule_frame`, `jacDblSchedule_out`,
  `jacDblSchedule_ix` — a name no brick binds comes through the schedule, and
  the output pointer and the index slots are such names.
* `out_ne_opPfx` — the output pointer is not a name in a brick's private
  namespace.
* `jacDblPrologue_frame` — the frame pointer, the index slots and the output
  pointer come through the prologue.
* `jacDblBody_split` — `jacDblBody` as three waists.
* `jacDblBody_cells` — from a `PrologueEntry` environment whose `out` holds a
  12-cell frame, running `jacDblBody` leaves `out` holding
  `pointCells (jacDblSpec X Y Z)`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
  (semList semList_single semScalar_setExpr_eq)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp emitFOp runSchedule jacDblSchedule jacDblSpec jacDblBody storeField
   pointCells feH feMulHalves feAddHalves feSubHalves)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal schedNameB semScalar_seqAll_append semScalar_seqAll_cons forall2_mapIdx)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk notTmp_of_len forIn_range_inv)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (BrickScope feHN feHN_inj wireBody splitApp peel hd hdAppend neOfHd hd_feHN hd_PL
   headOk_of_hd semScalar_seqAll_eq_semList hd_opPfx)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickFrame
  (WritesIn SuffixClosed writesIn_nil writesIn_append writesIn_snoc writesIn_cons
   writesIn_mono writesIn_map_range genAdd_writes genSub_writes feMulHalves_writes
   feAddHalves_writes feSubHalves_writes map_range_getBang_or_empty)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (envReader_of_bound)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope
  (jacDblSchedule_waist_value_brickScope jacDblSchedule_waist_scope)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpEpilogue
  (pointOpEpilogue_cells hd_out)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue
  (PrologueEntry jacDblPrologue jacDblPrologue_value jacDblBody_eq_prologue_append
   FrameIdx idxConst_run idxInit_run constInit_run loadCoord_run keep_load
   semScalar_append_run preLast feHN_ne_of_preLast feHN_ne_ix hd_ix notTmp_ix
   hd_X hd_Y hd_Z)

/-! ## 1. A field element's half-limb slots, bound -/

/-- The eight half-limb slots of a field element are bound at 64-bit word type. -/
def SlotsBound (env : SEnvScalar) (fe : String) : Prop :=
  ∀ k, k < 8 → ∃ v : BitVec 64, env (feHN fe k) = some ⟨.sword 64, v⟩

/-- Bound slots, in the form the store block's `SExpr` lowering reads them. -/
theorem slotsBound_reads {env : SEnvScalar} {fe : String} (h : SlotsBound env fe) :
    ∀ k, k < 8 → env (feHN fe k) = some ⟨.sword 64, envReader env (feHN fe k)⟩ := by
  intro k hk
  obtain ⟨v, hv⟩ := h k hk
  rw [hv, envReader_of_bound hv]

/-! ## 2. What a block of scalar assignments does to a slot -/

/-- **A command list that binds only `P`-names leaves every other non-temporary
    slot alone**, at the environment rather than only at the word reader. -/
theorem env_seqAll_frame (P : String → Prop) :
    ∀ (l : List LowCT), WritesIn P l →
      ∀ (env env' : SEnvScalar), semScalar (seqAll l) env = some env' →
        ∀ s, ¬ isTmpName s → ¬ P s → env' s = env s := by
  intro l
  induction l with
  | nil =>
      intro _ env env' hsem s _ _
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      rfl
  | cons c cs ih =>
      intro hw env env' hsem s hts hps
      obtain ⟨x, e, rfl, hx⟩ := hw c (.head _)
      rw [semScalar_seqAll_cons] at hsem
      cases hc : semScalar (LowCT.RScalarSetExpr x e) env with
      | none => rw [hc] at hsem; simp at hsem
      | some e1 =>
          rw [hc] at hsem
          simp only [Option.bind_some] at hsem
          have hne : s ≠ x := by rintro rfl; exact hps hx
          rw [ih (fun d hd => hw d (.tail _ hd)) e1 env' hsem s hts hps,
            (semScalar_setExpr_eq hc).2 s hts hne]

/-- **A command list of scalar assignments never unbinds a word slot.** Off the
    bound names the slot survives by the frame clause; at a bound name the
    assignment rebinds it at the same 64-bit word type. -/
theorem bound_seqAll (P : String → Prop) :
    ∀ (l : List LowCT), WritesIn P l →
      ∀ (env env' : SEnvScalar), semScalar (seqAll l) env = some env' →
        ∀ s, ¬ isTmpName s → (∃ v : BitVec 64, env s = some ⟨.sword 64, v⟩) →
          ∃ v : BitVec 64, env' s = some ⟨.sword 64, v⟩ := by
  intro l
  induction l with
  | nil =>
      intro _ env env' hsem s _ hb
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      exact hb
  | cons c cs ih =>
      intro hw env env' hsem s hts hb
      obtain ⟨x, e, rfl, -⟩ := hw c (.head _)
      rw [semScalar_seqAll_cons] at hsem
      cases hc : semScalar (LowCT.RScalarSetExpr x e) env with
      | none => rw [hc] at hsem; simp at hsem
      | some e1 =>
          rw [hc] at hsem
          simp only [Option.bind_some] at hsem
          refine ih (fun d hd => hw d (.tail _ hd)) e1 env' hsem s hts ?_
          by_cases hne : s = x
          · subst hne
            exact ⟨_, (semScalar_setExpr_eq hc).1⟩
          · rw [(semScalar_setExpr_eq hc).2 s hts hne]
            exact hb

/-! ## 3. The write set of an emitted brick -/

/-- A name extending a private prefix. -/
def Extends (pfx x : String) : Prop := ∃ u, x = pfx ++ u

theorem suffixClosed_extends (pfx : String) : SuffixClosed (Extends pfx) := by
  rintro s u ⟨w, rfl⟩
  exact ⟨w ++ u, by rw [String.append_assoc]⟩

theorem extends_self (pfx : String) : Extends pfx pfx := ⟨"", by simp⟩

/-- The output field element of a schedule entry. -/
def fopOut : FOp → String
  | .mul o _ _ => o
  | .add o _ _ => o
  | .sub o _ _ => o

/-- The names one emitted brick binds: its private `op{idx}` namespace, the empty
    name an out-of-range builder index reads, and the output field element's
    eight half-limb slots. -/
def BrickWrites (idx : Nat) (o : String) (x : String) : Prop :=
  Extends s!"op{idx}" x ∨ x = "" ∨ ∃ k, k < 8 ∧ x = feHN o k

/-- **The emitted brick binds only `op{idx}`-namespace names and the output field
    element's half-limb slots**, on all three arms. -/
theorem emitFOp_writes (idx : Nat) (op : FOp) :
    WritesIn (BrickWrites idx (fopOut op)) (emitFOp idx op) := by
  have hQ := suffixClosed_extends s!"op{idx}"
  have hp := extends_self s!"op{idx}"
  cases op with
  | mul o a b =>
      exact writesIn_append
        (writesIn_mono (fun x hx => hx.imp id Or.inl)
          (feMulHalves_writes hQ s!"op{idx}" (feH a) (feH b) hp))
        (writesIn_map_range 8 _ _ (fun k hk => Or.inr (Or.inr ⟨k, hk, rfl⟩)))
  | add o a b =>
      exact writesIn_append
        (writesIn_mono (fun x hx => hx.imp id Or.inl)
          (feAddHalves_writes hQ s!"op{idx}" (feH a) (feH b) hp))
        (writesIn_map_range 8 _ _ (fun k hk => Or.inr (Or.inr ⟨k, hk, rfl⟩)))
  | sub o a b =>
      exact writesIn_append
        (writesIn_mono (fun x hx => hx.imp id Or.inl)
          (feSubHalves_writes hQ s!"op{idx}" (feH a) (feH b) hp))
        (writesIn_map_range 8 _ _ (fun k hk => Or.inr (Or.inr ⟨k, hk, rfl⟩)))

/-! ## 4. The copy block binds the output field element's slots -/

/-- **The copy block binds the slots it has written.** After `i` of the eight
    copies the first `i` half-limb slots of the output field element are bound at
    64-bit word type: the `i`-th copy binds the `i`-th slot, and a later copy
    writes a different slot. -/
theorem wireBody_bound (o : String) (rn : List String)
    (hOnt : ∀ k, k < 8 → ¬ isTmpName (feHN o k)) (E : SEnvScalar) :
    ∀ i, i ≤ 8 → ∀ E', semList (wireBody o rn i) E = some E' →
      ∀ k, k < i → ∃ v : BitVec 64, E' (feHN o k) = some ⟨.sword 64, v⟩ := by
  intro i
  induction i with
  | zero => intro _ E' _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ i ih =>
      intro hin E' hsem k hk
      have hi8 : i < 8 := by omega
      rw [wireBody] at hsem
      obtain ⟨E1, hpre, htail⟩ := splitApp hsem
      obtain ⟨E2, h1, r1⟩ := peel htail
      have hE : E' = E2 := (Option.some.inj r1).symm
      subst hE
      have hstep := semScalar_setExpr_eq (by rwa [semList_single] at h1)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · obtain ⟨v, hv⟩ := ih (by omega) E1 hpre k h
        refine ⟨v, ?_⟩
        rw [hstep.2 (feHN o k) (hOnt k (by omega))
          (fun he => (by omega : k ≠ i) (feHN_inj (by omega) hi8 he).2)]
        exact hv
      · subst h
        exact ⟨_, hstep.1⟩

/-- **One emitted brick binds its output field element's eight half-limb
    slots.** The brick body runs into an environment the copy block then writes
    the eight slots from. -/
theorem emitFOp_bound_out (idx : Nat) (op : FOp) (env env' : SEnvScalar)
    (hOnt : ∀ k, k < 8 → ¬ isTmpName (feHN (fopOut op) k))
    (hsem : semScalar (seqAll (emitFOp idx op)) env = some env') :
    SlotsBound env' (fopOut op) := by
  rw [semScalar_seqAll_eq_semList] at hsem
  cases op with
  | mul o a b =>
      rw [show emitFOp idx (FOp.mul o a b)
          = (feMulHalves s!"op{idx}" (feH a) (feH b)).1
            ++ wireBody o (feMulHalves s!"op{idx}" (feH a) (feH b)).2 8 from rfl] at hsem
      obtain ⟨Eb, -, hwire⟩ := splitApp hsem
      exact fun k hk => wireBody_bound o _ hOnt Eb 8 (le_refl 8) env' hwire k hk
  | add o a b =>
      rw [show emitFOp idx (FOp.add o a b)
          = (feAddHalves s!"op{idx}" (feH a) (feH b)).1
            ++ wireBody o (feAddHalves s!"op{idx}" (feH a) (feH b)).2 8 from rfl] at hsem
      obtain ⟨Eb, -, hwire⟩ := splitApp hsem
      exact fun k hk => wireBody_bound o _ hOnt Eb 8 (le_refl 8) env' hwire k hk
  | sub o a b =>
      rw [show emitFOp idx (FOp.sub o a b)
          = (feSubHalves s!"op{idx}" (feH a) (feH b)).1
            ++ wireBody o (feSubHalves s!"op{idx}" (feH a) (feH b)).2 8 from rfl] at hsem
      obtain ⟨Eb, -, hwire⟩ := splitApp hsem
      exact fun k hk => wireBody_bound o _ hOnt Eb 8 (le_refl 8) env' hwire k hk

/-! ## 5. Over a whole schedule -/

/-- **Slot boundness survives later bricks.** A brick's commands are all scalar
    assignments, so a slot already bound at 64-bit word type stays bound. -/
theorem brickFold_slotsBound_pres (fe : String)
    (hnt : ∀ k, k < 8 → ¬ isTmpName (feHN fe k)) :
    ∀ (ops : List FOp) (ls : List (List LowCT)),
      List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops ls →
      ∀ (env env' : SEnvScalar), SlotsBound env fe →
        semScalar (seqAll ls.flatten) env = some env' → SlotsBound env' fe := by
  intro ops
  induction ops with
  | nil =>
      intro ls hf env env' hb hsem
      cases hf
      simp only [List.flatten_nil] at hsem
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      exact hb
  | cons op ops ih =>
      intro ls hf env env' hb hsem
      cases hf with
      | cons hl hrest =>
          rename_i l ls'
          obtain ⟨i, rfl⟩ := hl
          rw [List.flatten_cons, semScalar_seqAll_append] at hsem
          cases he : semScalar (seqAll (emitFOp i op)) env with
          | none => rw [he] at hsem; simp at hsem
          | some e1 =>
              rw [he] at hsem
              simp only [Option.bind_some] at hsem
              refine ih ls' hrest e1 env' (fun k hk => ?_) hsem
              exact bound_seqAll (BrickWrites i (fopOut op)) _ (emitFOp_writes i op)
                env e1 he (feHN fe k) (hnt k hk) (hb k hk)

/-- **A field element some schedule entry writes is bound at the schedule's
    exit.** The brick that writes it binds its eight slots, and the bricks after
    it keep them bound. -/
theorem brickFold_slotsBound (fe : String)
    (hnt : ∀ k, k < 8 → ¬ isTmpName (feHN fe k)) :
    ∀ (ops : List FOp) (ls : List (List LowCT)),
      List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops ls →
      fe ∈ ops.map fopOut →
      ∀ (env env' : SEnvScalar),
        semScalar (seqAll ls.flatten) env = some env' → SlotsBound env' fe := by
  intro ops
  induction ops with
  | nil => intro ls _ hmem; simp at hmem
  | cons op ops ih =>
      intro ls hf hmem env env' hsem
      cases hf with
      | cons hl hrest =>
          rename_i l ls'
          obtain ⟨i, rfl⟩ := hl
          rw [List.flatten_cons, semScalar_seqAll_append] at hsem
          cases he : semScalar (seqAll (emitFOp i op)) env with
          | none => rw [he] at hsem; simp at hsem
          | some e1 =>
              rw [he] at hsem
              simp only [Option.bind_some] at hsem
              rw [List.map_cons, List.mem_cons] at hmem
              rcases hmem with hmem | hmem
              · subst hmem
                exact brickFold_slotsBound_pres _ hnt ops ls' hrest e1 env'
                  (emitFOp_bound_out i op env e1 hnt he) hsem
              · exact ih ls' hrest hmem e1 env' hsem

/-- **A name no brick binds comes through a whole schedule.** -/
theorem brickFold_frame (s : String) (hnt : ¬ isTmpName s)
    (hpfx : ∀ (i : Nat) (w : String), s ≠ s!"op{i}" ++ w) (hemp : s ≠ "")
    (hslot : ∀ (fe : String) (k : Nat), k < 8 → s ≠ feHN fe k) :
    ∀ (ops : List FOp) (ls : List (List LowCT)),
      List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops ls →
      ∀ (env env' : SEnvScalar),
        semScalar (seqAll ls.flatten) env = some env' → env' s = env s := by
  intro ops
  induction ops with
  | nil =>
      intro ls hf env env' hsem
      cases hf
      simp only [List.flatten_nil] at hsem
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      rfl
  | cons op ops ih =>
      intro ls hf env env' hsem
      cases hf with
      | cons hl hrest =>
          rename_i l ls'
          obtain ⟨i, rfl⟩ := hl
          rw [List.flatten_cons, semScalar_seqAll_append] at hsem
          cases he : semScalar (seqAll (emitFOp i op)) env with
          | none => rw [he] at hsem; simp at hsem
          | some e1 =>
              rw [he] at hsem
              simp only [Option.bind_some] at hsem
              rw [ih ls' hrest e1 env' hsem]
              refine env_seqAll_frame (BrickWrites i (fopOut op)) _ (emitFOp_writes i op)
                env e1 he s hnt ?_
              rintro (⟨w, hw⟩ | hw | ⟨k, hk, hw⟩)
              · exact hpfx i w hw
              · exact hemp hw
              · exact hslot _ k hk hw

/-- The `Forall₂` witness the two folds consume at a concrete schedule. -/
theorem schedule_forall2 (ops : List FOp) :
    List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops
      (ops.mapIdx (fun i op => emitFOp i op)) :=
  forall2_mapIdx ops (fun i op => emitFOp i op) (fun i _op => ⟨i, rfl⟩)

/-- **A field element the doubling schedule writes is bound at its exit.** -/
theorem jacDblSchedule_slotsBound (fe : String)
    (hnt : ∀ k, k < 8 → ¬ isTmpName (feHN fe k))
    (hmem : fe ∈ jacDblSchedule.map fopOut) (env env' : SEnvScalar)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    SlotsBound env' fe :=
  brickFold_slotsBound fe hnt jacDblSchedule _ (schedule_forall2 jacDblSchedule)
    hmem env env' hSem

/-- **A name no brick binds comes through the doubling schedule.** -/
theorem jacDblSchedule_frame (s : String) (hnt : ¬ isTmpName s)
    (hpfx : ∀ (i : Nat) (w : String), s ≠ s!"op{i}" ++ w) (hemp : s ≠ "")
    (hslot : ∀ (fe : String) (k : Nat), k < 8 → s ≠ feHN fe k)
    (env env' : SEnvScalar)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    env' s = env s :=
  brickFold_frame s hnt hpfx hemp hslot jacDblSchedule _
    (schedule_forall2 jacDblSchedule) env env' hSem

/-! ## 6. The output pointer and the index slots -/

theorem notTmp_out : ¬ isTmpName "out" := notTmp_of_len "out" (by decide)

/-- A name with a first character is not the empty name. -/
theorem ne_empty_of_hd {s : String} {c : Char} (h : hd s = some c) : s ≠ "" := by
  intro he
  rw [he] at h
  simp [hd] at h

/-- The output pointer shares its first character with a brick's private prefix
    and differs at the second. -/
theorem out_ne_opPfx (i : Nat) (w : String) : ("out" : String) ≠ s!"op{i}" ++ w := by
  intro h
  have h2 : ("out" : String).toList = (s!"op{i}" ++ w).toList := congrArg String.toList h
  rw [show ("out" : String).toList = ['o', 'u', 't'] from rfl, String.toList_append,
    String.toList_append, show (toString "op" : String).toList = ['o', 'p'] from rfl] at h2
  simp at h2

/-- **The output pointer comes through the doubling schedule.** -/
theorem jacDblSchedule_out {env env' : SEnvScalar}
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    env' "out" = env "out" :=
  jacDblSchedule_frame "out" notTmp_out out_ne_opPfx (ne_empty_of_hd hd_out)
    (fun _ k hk => Ne.symm (feHN_ne_of_preLast hk (by decide))) env env' hSem

/-- **An index slot comes through the doubling schedule.** -/
theorem jacDblSchedule_ix {env env' : SEnvScalar} (i : Nat) (hi : i < 12)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    env' s!"ix{i}" = env s!"ix{i}" :=
  jacDblSchedule_frame s!"ix{i}" (notTmp_ix i)
    (fun j _ => neOfHd (hd_ix i) (hdAppend (hd_opPfx j)) (by decide))
    (ne_empty_of_hd (hd_ix i))
    (fun _ k hk => Ne.symm (feHN_ne_ix hk hi)) env env' hSem

/-- **A schedule output with a head-clean name is bound at the schedule's
    exit.** -/
theorem slotsBound_of_hd (fe : String) (c : Char) (hdfe : hd fe = some c) (hc : c ≠ '_')
    (hmem : fe ∈ jacDblSchedule.map fopOut) (env env' : SEnvScalar)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    SlotsBound env' fe :=
  jacDblSchedule_slotsBound fe
    (fun k _ => HeadOk.notTmp (headOk_of_hd (hd_feHN hdfe k) hc)) hmem env env' hSem

/-! ## 7. The whole body -/

/-- `jacDblBody` as the prologue, the schedule, and the three-`storeField`
    epilogue, associated so each stage is one waist. -/
theorem jacDblBody_split :
    jacDblBody = seqAll (jacDblPrologue ++ (runSchedule jacDblSchedule
      ++ (storeField 96 0 "Xp" ++ storeField 96 4 "Yp" ++ storeField 96 8 "Zp"))) := by
  rw [jacDblBody_eq_prologue_append]
  simp only [List.append_assoc]

/-- **The frame pointer, the index slots and the output pointer come through the
    `jacDbl` prologue.** The index and constant blocks write neither `out` nor a
    name starting with `o`, and each coordinate load writes only its own field
    element's staging and half-limb slots. -/
theorem jacDblPrologue_frame {n : Nat} {env env₁ : SEnvScalar} {a : Fin n → BitVec 64}
    (hP : env "P" = some ⟨.memref n, a⟩)
    (hSem : semScalar (seqAll jacDblPrologue) env = some env₁) :
    FrameIdx env₁ a ∧ env₁ "out" = env "out" := by
  obtain ⟨E2, hs2, hFI2, -, -⟩ := idxConst_run hP
  obtain ⟨E1', h1', -, hfr1⟩ := idxInit_run env
  obtain ⟨E2', h2', -, -, -, -, hfr2⟩ := constInit_run E1'
  have hEq : E2 = E2' := by
    have hb := semScalar_append_run h1' h2'
    rw [hs2] at hb
    exact Option.some.inj hb
  have hout2 : E2 "out" = env "out" := by
    rw [hEq, hfr2 "out" notTmp_out (by decide) (by decide) (by decide)
        (fun i _ => neOfHd hd_out (hd_PL i) (by decide)),
      hfr1 "out" notTmp_out (fun i _ => neOfHd hd_out (hd_ix i) (by decide))]
  obtain ⟨E3, hs3, -, -, hFI3, hfr3⟩ :=
    loadCoord_run (o := 0) (fe := "X") (c := 'X') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI2
  obtain ⟨E4, hs4, -, -, hFI4, hfr4⟩ :=
    loadCoord_run (o := 4) (fe := "Y") (c := 'Y') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI3
  obtain ⟨E5, hs5, -, -, hFI5, hfr5⟩ :=
    loadCoord_run (o := 8) (fe := "Z") (c := 'Z') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI4
  have hrun : semScalar (seqAll jacDblPrologue) env = some E5 :=
    semScalar_append_run (semScalar_append_run (semScalar_append_run hs2 hs3) hs4) hs5
  rw [hSem] at hrun
  obtain rfl : env₁ = E5 := Option.some.inj hrun
  refine ⟨hFI5, ?_⟩
  rw [keep_load hfr5 hd_Z notTmp_out hd_out (by decide),
    keep_load hfr4 hd_Y notTmp_out hd_out (by decide),
    keep_load hfr3 hd_X notTmp_out hd_out (by decide)]
  exact hout2

/-- **The `jacDbl` body's output frame.** From an entry environment satisfying
    `Secp256k1PointOpPrologue.PrologueEntry` whose `out` holds a 12-cell frame,
    a successful run of `Secp256k1PointOpFront.jacDblBody` leaves `out` holding
    `Secp256k1PointOpFront.pointCells` of `jacDblSpec X Y Z` — cells `0..3` the
    limbs of `X'`, cells `4..7` those of `Y'`, cells `8..11` those of `Z'`. -/
theorem jacDblBody_cells {n : Nat} {env env' : SEnvScalar} {a : Fin n → BitVec 64}
    {b : Fin 12 → BitVec 64} {X Y Z : Nat}
    (hE : PrologueEntry env a X Y Z)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hRun : semScalar jacDblBody env = some env') :
    ∃ fr : Fin 12 → BitVec 64, env' "out" = some ⟨.memref 12, fr⟩
      ∧ ∀ m : Fin 12, (fr m).toNat = (pointCells (jacDblSpec X Y Z)).getD m.val 0 := by
  rw [jacDblBody_split, semScalar_seqAll_append] at hRun
  cases h1 : semScalar (seqAll jacDblPrologue) env with
  | none => rw [h1] at hRun; simp at hRun
  | some E1 =>
      rw [h1, Option.bind_some, semScalar_seqAll_append] at hRun
      cases h2 : semScalar (seqAll (runSchedule jacDblSchedule)) E1 with
      | none => rw [h2] at hRun; simp at hRun
      | some E2 =>
          rw [h2, Option.bind_some] at hRun
          obtain ⟨hsc1, hv1⟩ := jacDblPrologue_value env E1 a X Y Z hE h1
          obtain ⟨hFI1, ho1⟩ := jacDblPrologue_frame hE.frame h1
          have hb2 : E2 "out" = some ⟨.memref 12, b⟩ := by
            rw [jacDblSchedule_out h2, ho1]
            exact hout
          have hix2 : ∀ i, i < 12 → E2 s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩ := by
            intro i hi
            rw [jacDblSchedule_ix i hi h2]
            exact hFI1.idx i hi
          obtain ⟨env'', fr, hsem3, hout3, hcells⟩ :=
            pointOpEpilogue_cells (jacDblSchedule_waist_scope E1 E2 hsc1 h2) hb2 hix2
              (slotsBound_reads (slotsBound_of_hd "Xp" 'X' rfl (by decide) (by decide) E1 E2 h2))
              (slotsBound_reads (slotsBound_of_hd "Yp" 'Y' rfl (by decide) (by decide) E1 E2 h2))
              (slotsBound_reads (slotsBound_of_hd "Zp" 'Z' rfl (by decide) (by decide) E1 E2 h2))
          rw [hRun] at hsem3
          obtain rfl : env' = env'' := Option.some.inj hsem3
          refine ⟨fr, hout3, fun m => ?_⟩
          rw [hcells m, jacDblSchedule_waist_value_brickScope E1 E2 X Y Z hsc1 hv1 h2]

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody
