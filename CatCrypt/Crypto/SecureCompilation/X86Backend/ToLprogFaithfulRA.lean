/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary

/-!
# RA-construction facts for `CoverData`: the `physScanStep` allocation invariant

`ToLprogFaithfulNary.physBody_lsem_result_uniform` is unconditional in
`BodyCover` for an arbitrary-length `UniformRegArith` `Com`, **given** a threaded
`CoverData` whose per-binding payload carries the two head-naming facts and the
RA-correctness facts `hcol` (two-address collapse) and `hinj` (renaming
injectivity, inside each `BinopBinding`). This module characterizes how the
shipped linear-scan RA (`physScanStep`/`physMap`/`physTable`) actually assigns
registers, and proves the tractable structural core from that construction.

## The exact `physScanStep`/`physMap` register-assignment invariant

`physMap tr s` (`JasminLprogExport.lean`:1086) looks `s` up in `physAssign tr`
(:1081), which runs `physScanAux` (:1039) — a Poletto–Sarkar linear scan. Each
binding's allocation is one `physScanStep st en busy nextFresh`
(`JasminLprogExport.lean`:1011–1017): it frees the physical registers whose
owner's range ended (`busy.filter (·.2 ≥ st)`), then **takes the lowest free
physical register** `(List.range nextFresh).find? (∉ busySlots)`, or a fresh one
beyond `nextFresh` if none is free.

**Consequence for `hcol`.** `physScanStep` does **not** prefer a binding's first
source `s0`'s register for its destination `dst` — it takes the *lowest free*
register, which only *coincidentally* equals `s0`'s register (when `s0` died and
its register is the lowest free one). So **`hcol` (`physRename dst = physRename
s0`) is a derived side-condition, NOT a structural fact of `physScanStep`.** The
lowering is robust to its failure (the collapse-or-mov dichotomy, §4).

**Consequence for `hinj`.** `physMap` is **deliberately not globally injective**:
it reuses a register across slots whose live ranges do not overlap. Injectivity
holds only on **simultaneously-live** slots — exactly the registers that are
busy at the same scan position. The precise structural seed of this is the
`physScanStep` *freshness invariant* (§1): the register a step hands out is fresh
against everything still busy.

## What this module proves (zero `sorry`, axioms ⊆ {propext, Classical.choice,
Quot.sound})

* **§1 `physScanStep_fresh` / `physScanStep_busy_lt`.** One step's emitted
  register is not among the still-busy registers, and every busy entry stays
  `< nextFresh'` — the two invariants that thread the scan.

* **§2 `physScanStep_busy_nodup`.** One step preserves pairwise-distinctness of
  the busy registers: combined with §1, **simultaneously-busy slots receive
  distinct physical registers**.

* **§3 `scanBusyState_ScanInv` (+ `_init`).** The whole-scan recursive carrier:
  `ScanInv` (busy `< nextFresh` ∧ busy registers `Nodup`) is maintained across
  the entire `physScanAux` run, from the initial `ScanInv [] 0`. This is the
  whole-body invariant a full `hinj` proof consumes.

* **§4 `lowerTwoAddr_dichotomy` / `lowerTwoAddr_collapse_of_eq`.** The
  collapse-or-mov dichotomy: `lowerTwoAddr` is *exactly* the collapse form when
  the physical `dst = s0`, and the `legalizeMov`-prefixed form otherwise. So
  `hcol` selects the collapse branch; its negation routes through the
  already-discharged `legalizeMov` prefix. **`hcol` is never required** — it is
  an optimization the RA may or may not enable, and the lowering is faithful
  either way.

* **§5 `physRegName_injOn_gp` / `physRegName_gp_ne_spill` / `physRegName_injOn_spill`
  / `physRegName_inj`.** The rendering layer of `hinj`, **fully closed (global)**:
  `physRegName` is injective on the GP-register block (via `gpRegNames_nodup`),
  never confuses a GP index with a spill index, and is injective on the spill
  block — the last bottoming out in the decimal-string injectivity
  `toDigits_inj`/`toString_nat_inj` (proved here from the Batteries
  `Nat.toDigits` recurrence; Mathlib/Batteries has no `Nat.repr` injectivity
  lemma). The three combine into `physRegName_inj` (injective on all of `Nat`).

* **§5 `nameSlot_injOn`.** The naming layer of `hinj`, **closed on the live set**:
  `nameSlot body n = (bodyNames body).idxOf n` is injective on names that occur in
  the body (`List.getElem_idxOf` left inverse). It is *not* globally injective
  (absent names collapse to the sentinel slot), which is exactly why `hinj` is
  live-set-scoped.

* **§6 `physRename_injOn_live`.** The composition: with the rendering layer
  (`physRegName_inj`, global) and naming layer (`nameSlot_injOn`, live) both
  discharged, `hinj` reduces to the **single** slot-level fact that
  `physMapTabled tbl` is injective on the (distinct, live) source/destination
  slots. Everything *above* the linear-scan core is proved.

## Residual (named honestly — NOT proved here)

The **slot-level RA injectivity** `physMapTabled (physTable …)`-injectivity on
simultaneously-live slots — the one remaining factor `physRename_injOn_live`
(§6) consumes as its `hslot` hypothesis. Two sub-steps remain, both linear-scan
analysis over the threaded carrier (the structural foundations §3 supplies —
`scanBusyState_ScanInv` slot-distinctness and `physScanAux_acc_extends`
accumulator agreement — are proved; the residual is wiring them into a
slot-level injectivity):

1. **`physMap`-from-`scanBusyState` (register half).** `physScanAux_acc_extends`
   (§3) already shows `physAssign` is the per-step emitted `(slot, ph)` list;
   what remains is the joint accumulator/busy invariant proving the `ph` a slot
   `find?`s back is the register busy at its allocation step, so §3's
   busy-register distinctness becomes distinctness of *assigned* registers.

2. **Live-at-same-position ⇒ simultaneously busy.** That two slots live at a
   common trace position are both in the `busy` set at that position (so §3's
   `Nodup` applies). This is the linear-scan liveness invariant.

Both feed `physRename_injOn_live`'s `hslot`; with them `hinj` would be
hypothesis-free, and `physBody_lsem_result_uniform` would no longer carry it.

**The `JState↔Lstate` question.** `RegMachineSim.jinstr_renameBlock_sound`
(`JInstrRegMachineSim.lean`:202) proves per-block RA soundness for a **uniform**
renaming `ρ` over the `JInstr 64`/`JState 64` machine, under a **global**
`Function.Injective ρ` (not "injective on the live set"). It does **not**
transfer to `physBody`/`Lstate` directly, for two independent reasons: (a)
`physBody` is **not a uniform renaming** — it interleaves the two-address `mov`s
and the spill reloads (`legalizeBinop`), so there is no single `ρ` to feed
`renameBlockS`; (b) even abstracting that, the keystone wants *global*
injectivity, whereas `physMap` is only injective on simultaneously-live slots
(§3). So the genuine missing bridge is **not** a mechanical `JState↔Lstate`
state-correspondence transfer of the keystone; it is the live-set-restricted
re-proof of the maintenance step over `Lstate` for the *non-uniform* `physBody`
emission — which is why `ToLprogFaithfulWriteSide` already carries `hinj` as a
per-block liveness hypothesis rather than deriving it from the keystone. This
module supplies the RA-side fact (§3) that a future such re-proof would feed in;
it does not perform that re-proof.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. The single-step freshness invariant of `physScanStep` -/

/-- **`physScanStep` freshness.** The physical register `physScanStep` hands out
    is not among the registers still busy after this step's reclamation (the
    `busy'` whose owner's range did not end before `st`). Both arms guarantee it:
    the `some ph` arm picks `ph` with `!busySlots.contains ph` (from `find?`); the
    `none` arm returns `nextFresh`, which is `< nextFresh`-free by the standing
    `busy < nextFresh` invariant. -/
theorem physScanStep_fresh (st en : Nat) (busy : List (Nat × Nat))
    (nextFresh : Nat) (hbusy : ∀ p ∈ busy, p.1 < nextFresh) :
    ((physScanStep st en busy nextFresh).1)
      ∉ ((busy.filter (fun p => p.2 ≥ st)).map Prod.fst) := by
  unfold physScanStep
  cases hf : (List.range nextFresh).find?
      (fun ph => !((busy.filter (fun p => p.2 ≥ st)).map Prod.fst).contains ph) with
  | some ph =>
      simp only [hf]
      have hfs := List.find?_some hf
      simpa using hfs
  | none =>
      simp only [hf]
      -- nextFresh ∉ busySlots because every busy slot is < nextFresh
      intro hmem
      rcases List.mem_map.mp hmem with ⟨p, hp, hpe⟩
      have hsub : p ∈ busy := List.mem_of_mem_filter hp
      exact absurd (hpe ▸ hbusy p hsub) (Nat.lt_irrefl nextFresh)

/-- **`physScanStep` preserves the `busy < nextFresh` bound.** After a step, every
    busy entry (the freshly-allocated one plus the retained `busy'`) is `<` the
    updated `nextFresh'`. This is the invariant that threads `physScanStep_fresh`
    across the whole scan: the next step's `hbusy` premise is re-established. -/
theorem physScanStep_busy_lt (st en : Nat) (busy : List (Nat × Nat))
    (nextFresh : Nat) (hbusy : ∀ p ∈ busy, p.1 < nextFresh) :
    ∀ p ∈ (physScanStep st en busy nextFresh).2.1,
      p.1 < (physScanStep st en busy nextFresh).2.2 := by
  unfold physScanStep
  cases hf : (List.range nextFresh).find?
      (fun ph => !((busy.filter (fun p => p.2 ≥ st)).map Prod.fst).contains ph) with
  | some ph =>
      simp only [hf]
      intro p hp
      rcases List.mem_cons.mp hp with hpe | hpf
      · subst hpe
        have hfs := List.mem_of_find?_eq_some hf
        exact List.mem_range.mp hfs
      · exact hbusy p (List.mem_of_mem_filter hpf)
  | none =>
      simp only [hf]
      intro p hp
      rcases List.mem_cons.mp hp with hpe | hpf
      · subst hpe; exact Nat.lt_succ_self nextFresh
      · exact Nat.lt_succ_of_lt (hbusy p (List.mem_of_mem_filter hpf))

/-! ## 2. Distinct physical registers for simultaneously-busy slots

The freshness invariant of §1 yields the allocator's key correctness property:
the physical registers `physScanStep` keeps *simultaneously busy* are pairwise
distinct. This is the per-step seed of the whole-body injectivity `hinj` needs
(distinct SSA names that are live at the same time receive distinct physical
registers). -/

/-- **`physScanStep` preserves busy-register distinctness.** If the physical
    registers in `busy` are pairwise distinct (`busy.map Prod.fst` is `Nodup`)
    and all `< nextFresh`, then after a step the retained-plus-new busy list still
    has pairwise-distinct physical registers. By `physScanStep_fresh`, the new
    register is fresh against the retained ones, and filtering preserves
    `Nodup`. -/
theorem physScanStep_busy_nodup (st en : Nat) (busy : List (Nat × Nat))
    (nextFresh : Nat) (hbusy : ∀ p ∈ busy, p.1 < nextFresh)
    (hnd : (busy.map Prod.fst).Nodup) :
    ((physScanStep st en busy nextFresh).2.1.map Prod.fst).Nodup := by
  have hfresh : (physScanStep st en busy nextFresh).1
      ∉ ((busy.filter (fun p => p.2 ≥ st)).map Prod.fst) :=
    physScanStep_fresh st en busy nextFresh hbusy
  -- retained busy after filter
  have hndf : (((busy.filter (fun p => p.2 ≥ st)).map Prod.fst)).Nodup :=
    (List.filter_sublist (l := busy)).map Prod.fst |>.nodup hnd
  -- the busy list after the step is `(reg, en) :: busy'`
  have hstep : (physScanStep st en busy nextFresh).2.1
      = ((physScanStep st en busy nextFresh).1, en)
        :: (busy.filter (fun p => p.2 ≥ st)) := by
    unfold physScanStep
    dsimp only
    split <;> rfl
  rw [hstep, List.map_cons]
  exact List.nodup_cons.mpr ⟨hfresh, hndf⟩

/-! ## 3. The whole-scan freshness/distinctness invariant

The per-step lemmas of §1–2 thread through the recursive `physScanAux`: every
intermediate `busy` list keeps physical registers `< nextFresh` and pairwise
distinct, and each emitted assignment uses a register fresh against the busy set
at its allocation time. We expose the recursive carrier as a predicate
`ScanInv` and prove `physScanStep` re-establishes it, giving the inductive
invariant the whole-body injectivity proof would consume. -/

/-- The running invariant carried by `physScanAux`: the busy list's physical
    registers are all `< nextFresh` and pairwise distinct. Re-established by every
    `physScanStep` (combining `physScanStep_busy_lt` and
    `physScanStep_busy_nodup`). -/
def ScanInv (busy : List (Nat × Nat)) (nextFresh : Nat) : Prop :=
  (∀ p ∈ busy, p.1 < nextFresh) ∧ (busy.map Prod.fst).Nodup

/-- `physScanStep` re-establishes `ScanInv` on its updated `(busy', nextFresh')`.
    This is the single induction step for threading freshness through the whole
    scan: the next `physScanStep` again sees a `< nextFresh`, `Nodup` busy list,
    so its emitted register is again fresh against everything still busy. -/
theorem physScanStep_ScanInv (st en : Nat) (busy : List (Nat × Nat))
    (nextFresh : Nat) (h : ScanInv busy nextFresh) :
    ScanInv (physScanStep st en busy nextFresh).2.1
      (physScanStep st en busy nextFresh).2.2 :=
  ⟨physScanStep_busy_lt st en busy nextFresh h.1,
   physScanStep_busy_nodup st en busy nextFresh h.1 h.2⟩

/-- The busy/nextFresh state threaded *out* of a whole `physScanAux` run: walk
    the items, applying `physScanStep` and keeping only the resulting
    `(busy, nextFresh)` (the accumulator is dropped). The carrier on which the
    whole-scan `ScanInv` is maintained. -/
def scanBusyState (fuel : Nat) (items : List (Nat × Nat × Nat))
    (busy : List (Nat × Nat)) (nextFresh : Nat) : List (Nat × Nat) × Nat :=
  match fuel, items with
  | 0, _ => (busy, nextFresh)
  | _, [] => (busy, nextFresh)
  | fuel' + 1, (_, st, en) :: rest =>
      let r := physScanStep st en busy nextFresh
      scanBusyState fuel' rest r.2.1 r.2.2

/-- **Whole-scan invariant (the recursive carrier).** Running the linear scan
    over any item list from a `ScanInv`-respecting `(busy, nextFresh)` keeps
    `ScanInv` on the final threaded busy state. Inducts on `fuel`/`items`,
    re-establishing `ScanInv` after each `physScanStep` via
    `physScanStep_ScanInv`. This is the invariant a whole-body injectivity proof
    consumes: at every allocation point the busy registers are pairwise distinct,
    so simultaneously-live slots never collide. -/
theorem scanBusyState_ScanInv (fuel : Nat) :
    ∀ (items : List (Nat × Nat × Nat)) (busy : List (Nat × Nat)) (nextFresh : Nat),
      ScanInv busy nextFresh →
      ScanInv (scanBusyState fuel items busy nextFresh).1
        (scanBusyState fuel items busy nextFresh).2 := by
  induction fuel with
  | zero => intro items busy nextFresh h; exact h
  | succ fuel' ih =>
      intro items busy nextFresh h
      cases items with
      | nil => exact h
      | cons it rest =>
          obtain ⟨s, st, en⟩ := it
          simp only [scanBusyState]
          exact ih rest _ _ (physScanStep_ScanInv st en busy nextFresh h)

/-- The scan starts from `ScanInv [] 0` (empty busy, no register allocated yet),
    so by `scanBusyState_ScanInv` the whole shipped allocation
    (`physScanAux items.length items [] 0`) threads a `ScanInv` busy state
    throughout. -/
theorem scanBusyState_ScanInv_init (fuel : Nat) (items : List (Nat × Nat × Nat)) :
    ScanInv (scanBusyState fuel items [] 0).1 (scanBusyState fuel items [] 0).2 :=
  scanBusyState_ScanInv fuel items [] 0 ⟨by intro p hp; simp at hp, by simp⟩

/-- **`physScanAux` extends its accumulator.** Each step appends one
    `(slot, ph)` to the accumulator and never touches the prefix, so the whole run
    is `acc ++ (the run started from the empty accumulator)`. The structural seed
    of Step 1 (relating the shipped `physAssign tr = physScanAux … [] 0 []`
    `find?`-lookup to the per-step emitted assignment): the assignment slot `s`
    receives is exactly the `physScanStep` register at the step that processes
    `s`. -/
theorem physScanAux_acc_extends (fuel : Nat) :
    ∀ (items : List (Nat × Nat × Nat)) (busy : List (Nat × Nat)) (nextFresh : Nat)
      (acc : List (Nat × Nat)),
      ∃ rest, physScanAux fuel items busy nextFresh acc = acc ++ rest
        ∧ physScanAux fuel items busy nextFresh [] = rest := by
  induction fuel with
  | zero => intro items busy nextFresh acc; exact ⟨[], by simp [physScanAux]⟩
  | succ f ih =>
      intro items busy nextFresh acc
      cases items with
      | nil => exact ⟨[], by simp [physScanAux]⟩
      | cons it rest =>
          obtain ⟨s, st, en⟩ := it
          obtain ⟨r1, h1a, h1b⟩ := ih rest (physScanStep st en busy nextFresh).2.1
            (physScanStep st en busy nextFresh).2.2 (acc ++ [(s, (physScanStep st en busy nextFresh).1)])
          obtain ⟨r0, h0a, h0b⟩ := ih rest (physScanStep st en busy nextFresh).2.1
            (physScanStep st en busy nextFresh).2.2 [(s, (physScanStep st en busy nextFresh).1)]
          have hr : r1 = r0 := by rw [← h1b, ← h0b]
          refine ⟨(s, (physScanStep st en busy nextFresh).1) :: r0, ?_, ?_⟩
          · simp only [physScanAux]
            rw [h1a, hr]; simp
          · simp only [physScanAux, List.nil_append]
            rw [h0a]; simp

/-! ## 4. The collapse-or-mov dichotomy of `lowerTwoAddr`

`physScanStep` does **not** structurally place a binop's `dst` on its first
source's register (it picks the lowest free register — `JasminLprogExport.lean`
:1011–1017). So `hcol` (`physRename dst = physRename s0`) is a *derived
side-condition*, not a structural fact of the RA. The lowering is robust to its
failure: `lowerTwoAddr` (`JasminLprogExport.lean`:1209–1215) branches on
`dst = s0`. When `hcol` holds (physical `dst = s0`), the leading `mov` collapses;
when it fails, `lowerTwoAddr` emits the `legalizeMov dst s0` prefix — the case
already discharged by the two-address probe's `dst ≠ s0` arm. We make the
dichotomy explicit as a definitional case split, so the `hcol`/`mov` split is a
provable fact about `lowerTwoAddr` (not an assumption). -/

/-- **The collapse-or-mov dichotomy.** On the 32-bit (`MOV`) path,
    `lowerTwoAddr` is *exactly* the collapse form `legalizeBinop dst s1 opn` when
    `dst = s0`, and the mov-prefixed form `legalizeMov dst s0 ++ legalizeBinop
    dst s1 opn` when `dst ≠ s0`. Hence `hcol` (which forces the physical
    `dst = s0`) selects the collapse branch; its negation routes through the
    already-handled `legalizeMov` prefix. The collapse is therefore never
    *required* — it is an optimization the RA may or may not enable, and the
    lowering is faithful either way. -/
theorem lowerTwoAddr_dichotomy (dst s0 s1 opn : String) :
    lowerTwoAddr (.reg dst) (.reg s0) (.reg s1) opn "MOV"
      = (if dst = s0
          then legalizeBinop (.reg dst) (.reg s1) opn "MOV"
          else legalizeMov (.reg dst) (.reg s0) "MOV"
                ++ legalizeBinop (.reg dst) (.reg s1) opn "MOV") := by
  unfold lowerTwoAddr
  rw [materializeWideImm_MOV]
  by_cases h : (LOperand.reg dst) = (LOperand.reg s0)
  · have hds : dst = s0 := by injection h
    simp [hds]
  · have hds : dst ≠ s0 := fun he => h (by rw [he])
    simp [hds]

/-- The `hcol` collapse condition `physRename body tbl s0 = physRename body tbl
    (dst)` is precisely the equality of the *physical* operand names the lowering
    branches on: when it holds, `lowerTwoAddr` (over the physical names) takes the
    collapse branch. This ties the abstract `hcol` carried in `CoverData` to the
    concrete `dst = s0` test of `lowerTwoAddr_dichotomy`. -/
theorem lowerTwoAddr_collapse_of_eq (dst s0 s1 opn : String) (hcol : dst = s0) :
    lowerTwoAddr (.reg dst) (.reg s0) (.reg s1) opn "MOV"
      = legalizeBinop (.reg dst) (.reg s1) opn "MOV" := by
  rw [lowerTwoAddr_dichotomy, if_pos hcol]

/-! ## 5. `physRegName` injectivity — the rendering layer of `hinj`

`hinj` is `physRename`-injectivity into a binding's destination:
`physRename = physRegName ∘ physMapTabled tbl ∘ nameSlot`. The whole-body bridge
(deferred residual) must compose three injectivities: `nameSlot` injective on
distinct live names, `physMap` injective on simultaneously-live slots (seeded by
the `ScanInv` of §3), and `physRegName` injective on the slot-index range. The
last is a finite/arithmetic fact we discharge here. -/

/-- No GP register name begins with the character `'k'`; the spill names
    `"k." ++ …` all begin with `'k'`. The character-level discriminator that
    separates the GP block from the spill block of `physRegName`. -/
theorem gpRegNames_head_ne_k : ∀ r ∈ gpRegNames, r.toList.head? ≠ some 'k' := by decide

/-- A spill name `"k." ++ toString n` begins with `'k'`. -/
theorem kdot_head_eq_k (n : Nat) : ("k." ++ toString n).toList.head? = some 'k' := by
  simp [String.toList_append]

/-- `gpRegNames` has no duplicate entries. -/
theorem gpRegNames_nodup : gpRegNames.Nodup := by decide

/-- A GP register name is never a `"k."`-spill name (their leading characters
    differ). -/
theorem gpRegName_ne_kdot {r : String} (hr : r ∈ gpRegNames) (n : Nat) :
    r ≠ "k." ++ toString n := by
  intro he
  exact gpRegNames_head_ne_k r hr (by rw [he, kdot_head_eq_k])

/-- **`physRegName` injective on the GP-register block.** Two physical indices
    both below `numGPRegs` render to the same name only if equal — the
    duplicate-free `gpRegNames` (`gpRegNames_nodup`) makes `physRegName` injective
    on `[0, numGPRegs)`, the registers the allocator hands out in the no-spill
    (common) case. The rendering layer of `hinj` on the GP block. -/
theorem physRegName_injOn_gp {a b : Nat} (ha : a < numGPRegs) (hb : b < numGPRegs)
    (hab : physRegName a = physRegName b) : a = b := by
  unfold physRegName at hab
  have ha' : a < gpRegNames.length := by simpa [numGPRegs] using ha
  have hb' : b < gpRegNames.length := by simpa [numGPRegs] using hb
  rw [List.getElem?_eq_getElem ha', List.getElem?_eq_getElem hb'] at hab
  exact (List.Nodup.getElem_inj_iff gpRegNames_nodup (hi := ha') (hj := hb')).mp hab

/-- **`physRegName` does not confuse the GP and spill blocks.** A GP-block index
    (`< numGPRegs`) and a spill-block index (`≥ numGPRegs`) never render to the
    same name (GP names do not start with `'k'`, spill names do). Together with
    `physRegName_injOn_gp` this fixes the GP block as a clean injective region. -/
theorem physRegName_gp_ne_spill {a b : Nat} (ha : a < numGPRegs) (hb : numGPRegs ≤ b) :
    physRegName a ≠ physRegName b := by
  unfold physRegName
  have ha' : a < gpRegNames.length := by simpa [numGPRegs] using ha
  have hb' : ¬ b < gpRegNames.length := by simpa [numGPRegs] using Nat.not_lt.mpr hb
  rw [List.getElem?_eq_getElem ha', List.getElem?_eq_none (Nat.le_of_not_lt hb')]
  exact gpRegName_ne_kdot (List.getElem_mem ha') (b - numGPRegs)

/-! ### `Nat.toDigits 10` injectivity — the decimal-rendering atom of the spill block

`physRegName`'s spill names are `"k." ++ toString (phys - numGPRegs)`, so spill-
block injectivity bottoms out in injectivity of `toString` on `Nat`
(= `Nat.repr = String.ofList ∘ Nat.toDigits 10`). Mathlib/Batteries has **no**
`Nat.repr`/`Nat.toDigits` injectivity lemma, so we prove the decimal-string
injectivity from the Batteries recurrence (`toDigits_append_toDigits`,
`toDigits_of_lt_base`) by strong induction. -/

/-- One decimal-digit peel: for `n ≥ 10`, `toDigits 10 n` is the digits of `n/10`
    followed by the units digit `(n%10).digitChar`. Derived from
    `Nat.toDigits_append_toDigits`. -/
theorem toDigits_rec (n : Nat) (hn : 10 ≤ n) :
    Nat.toDigits 10 n = Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar] := by
  have h1 : 0 < n / 10 := Nat.div_pos hn (by decide)
  have h2 : n % 10 < 10 := Nat.mod_lt _ (by decide)
  have hkey := Nat.toDigits_append_toDigits (b := 10) (n := n / 10) (d := n % 10)
    (by decide) h1 h2
  rw [Nat.toDigits_of_lt_base h2] at hkey
  rw [hkey]; congr 1; omega

/-- The decimal rendering of any `Nat` is non-empty. -/
theorem toDigits_ne_nil (k : Nat) : Nat.toDigits 10 k ≠ [] := by
  by_cases hk : k < 10
  · rw [Nat.toDigits_of_lt_base hk]; simp
  · rw [toDigits_rec k (by omega)]; simp

/-- `Nat.digitChar` is injective on `[0, 10)` (the base-10 digit alphabet). -/
theorem digitChar_inj10 : ∀ a < 10, ∀ b < 10, Nat.digitChar a = Nat.digitChar b → a = b := by
  decide

/-- **`Nat.toDigits 10` is injective.** Proved by strong induction on `m`: the
    `< 10` × `< 10` case is `digitChar` injectivity; mixed-length cases are length
    contradictions (`toDigits_ne_nil`); the `≥ 10` × `≥ 10` case peels the units
    digit (`toDigits_rec`, `List.append_singleton_inj`) and recurses on `·/10`.
    The decimal-string atom Mathlib/Batteries lacks. -/
theorem toDigits_inj : ∀ (m n : Nat), Nat.toDigits 10 m = Nat.toDigits 10 n → m = n := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n h
    by_cases hm : m < 10 <;> by_cases hn : n < 10
    · rw [Nat.toDigits_of_lt_base hm, Nat.toDigits_of_lt_base hn] at h
      simp only [List.cons.injEq, and_true] at h
      exact digitChar_inj10 m hm n hn h
    · exfalso
      rw [Nat.toDigits_of_lt_base hm, toDigits_rec n (by omega)] at h
      have hl := congrArg List.length h
      have hpos : 0 < (Nat.toDigits 10 (n / 10)).length :=
        List.length_pos_iff.mpr (toDigits_ne_nil (n / 10))
      simp only [List.length_cons, List.length_nil, List.length_append] at hl
      omega
    · exfalso
      rw [Nat.toDigits_of_lt_base hn, toDigits_rec m (by omega)] at h
      have hl := congrArg List.length h
      have hpos : 0 < (Nat.toDigits 10 (m / 10)).length :=
        List.length_pos_iff.mpr (toDigits_ne_nil (m / 10))
      simp only [List.length_cons, List.length_nil, List.length_append] at hl
      omega
    · rw [toDigits_rec m (by omega), toDigits_rec n (by omega)] at h
      obtain ⟨hpre, hlast⟩ := List.append_singleton_inj.mp h
      have hmod : m % 10 = n % 10 :=
        digitChar_inj10 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) hlast
      have hdiv : m / 10 = n / 10 := ih (m / 10) (by omega) (n / 10) hpre
      omega

/-- **`toString` is injective on `Nat`.** Since `toString k = Nat.repr k =
    String.ofList (Nat.toDigits 10 k)`, this follows from `toDigits_inj` through
    `String.ofList` injectivity (`String.toList_ofList`). -/
theorem toString_nat_inj (m n : Nat) (h : toString m = toString n) : m = n := by
  have hr : ∀ k : Nat, toString k = String.ofList (Nat.toDigits 10 k) := fun _ => rfl
  rw [hr, hr] at h
  have ht := congrArg String.toList h
  rw [String.toList_ofList, String.toList_ofList] at ht
  exact toDigits_inj m n ht

/-- The spill name `physRegName` renders for a slot index `≥ numGPRegs`. -/
theorem physRegName_spill_eq {a : Nat} (ha : numGPRegs ≤ a) :
    physRegName a = "k." ++ toString (a - numGPRegs) := by
  unfold physRegName
  rw [List.getElem?_eq_none (by simpa [numGPRegs] using ha)]

/-- **`physRegName` injective on the spill block.** Two indices `≥ numGPRegs`
    render to the same `"k." ++ toString (·-numGPRegs)` name only if equal — by
    `toString_nat_inj` on the offsets. The spill-block counterpart of
    `physRegName_injOn_gp`. -/
theorem physRegName_injOn_spill {a b : Nat} (ha : numGPRegs ≤ a) (hb : numGPRegs ≤ b)
    (hab : physRegName a = physRegName b) : a = b := by
  rw [physRegName_spill_eq ha, physRegName_spill_eq hb] at hab
  have hoff : toString (a - numGPRegs) = toString (b - numGPRegs) :=
    (String.append_right_inj "k.").mp hab
  have : a - numGPRegs = b - numGPRegs := toString_nat_inj _ _ hoff
  omega

/-! ### `nameSlot` injectivity on the live set

`nameSlot body n = (bodyNames body).idxOf n` is the first-appearance rank of `n`.
On names that **occur** in the body (`n ∈ bodyNames body` — the live set), the
rank is a left inverse of indexing (`List.getElem_idxOf`), so distinct live names
get distinct slots. (It is *not* globally injective: every name absent from
`bodyNames` collapses onto the out-of-universe sentinel `bodyNames.length`, which
is exactly why `hinj` is scoped to the live set.) -/

/-- **`nameSlot` injective on live names.** Two names that both occur in the body
    (`∈ bodyNames body`) with the same first-appearance rank are equal. The
    name-level seed of `hinj`, restricted (as it must be) to the live set. -/
theorem nameSlot_injOn {body : Lcmd} {m n : String}
    (hm : m ∈ bodyNames body) (hn : n ∈ bodyNames body)
    (h : nameSlot body m = nameSlot body n) : m = n := by
  unfold nameSlot at h
  have hra := List.getElem_idxOf (x := m) (xs := bodyNames body)
    (List.idxOf_lt_length_iff.mpr hm)
  have hrb := List.getElem_idxOf (x := n) (xs := bodyNames body)
    (List.idxOf_lt_length_iff.mpr hn)
  rw [← hra, ← hrb]; simp only [h]

/-- **`physRegName` is globally injective.** The GP block (`< numGPRegs`,
    `physRegName_injOn_gp`) and the spill block (`≥ numGPRegs`,
    `physRegName_injOn_spill`) are each injective and disjoint
    (`physRegName_gp_ne_spill`), so `physRegName` is injective on all of `Nat` —
    the full rendering layer of `hinj`, hypothesis-free. -/
theorem physRegName_inj {a b : Nat} (hab : physRegName a = physRegName b) : a = b := by
  rcases Nat.lt_or_ge a numGPRegs with ha | ha <;> rcases Nat.lt_or_ge b numGPRegs with hb | hb
  · exact physRegName_injOn_gp ha hb hab
  · exact absurd hab (physRegName_gp_ne_spill ha hb)
  · exact absurd hab.symm (physRegName_gp_ne_spill hb ha)
  · exact physRegName_injOn_spill ha hb hab

/-! ## 6. Composing the rendering and naming layers of `hinj`

`hinj` (carried in each `BinopBinding`) is
`∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst`, where
`physRename body tbl n = physRegName (physMapTabled tbl (nameSlot body n))`
(definitionally). This module discharges **two of its three composed
injectivities outright**: `physRegName` (the rendering layer, fully — global,
`physRegName_inj`) and `nameSlot` (the naming layer, on the live set,
`nameSlot_injOn`). The remaining factor is `physMapTabled (physTable …)`
injectivity on simultaneously-live slots — the linear-scan core whose structural
seed is the `ScanInv` of §3 (slot-distinctness) plus the `physScanAux`
accumulator characterization (`physScanAux_acc_extends`, §3). We reduce `hinj` to
*exactly* that single slot-level hypothesis. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill in
/-- **`hinj` reduced to slot-level RA injectivity.** With the two rendering/naming
    layers discharged here (`physRegName_inj` global, `nameSlot_injOn` on the live
    set), the per-binding destination injectivity `hinj` follows from the single
    remaining fact `hslot`: `physMapTabled tbl` maps the (distinct, live) source
    slot and destination slot to distinct physical registers. This isolates the
    residual to the linear-scan core — `physMapTabled`-injectivity on
    simultaneously-live slots — with everything *above* it (rendering, naming)
    proved. `physRename body tbl n` unfolds to
    `physRegName (physMapTabled tbl (nameSlot body n))` by `rfl`. -/
theorem physRename_injOn_live {body : Lcmd} {tbl : Array Nat} {m nDst : String}
    (hm : m ∈ bodyNames body) (hnDst : nDst ∈ bodyNames body)
    (hslot : physMapTabled tbl (nameSlot body m) = physMapTabled tbl (nameSlot body nDst) →
      nameSlot body m = nameSlot body nDst)
    (h : physRename body tbl m = physRename body tbl nDst) : m = nDst := by
  -- peel the rendering layer (physRegName injective, global)
  have hmap : physMapTabled tbl (nameSlot body m) = physMapTabled tbl (nameSlot body nDst) :=
    physRegName_inj h
  -- peel the RA slot layer (the residual hypothesis), then the naming layer
  exact nameSlot_injOn hm hnDst (hslot hmap)

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA
