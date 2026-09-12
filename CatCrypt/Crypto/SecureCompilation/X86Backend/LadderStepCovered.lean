/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LadderTripFrontSpec

/-!
# The framed secp256k1 ladder step lies in the scalar covered fragment

`Secp256k1PointOpFrontFramedLadder.ladderStepFramed` composes the frame-relative
doubling body, the frame-relative addition body and the three-select trip over a
single 256-cell memref frame. This module proves that every command a framed
field-op brick (`Secp256k1PointOpFrontFramed.emitFOpFramed`) emits is an arm of
`TranslateDialectScalar.IsCoveredS`, and composes the brick coverage with the
select-trip coverage
(`Secp256k1PointOpFrontFramedLadder.emitSelectFramed_coveredS`) into coverage of
the two framed point-op bodies and of the whole ladder step.

The proofs are generator-level: the brick coverage is parametric in the slot
map, its only side condition is that every slot's four cell indices fit in
64 bits, and nothing reduces the emitted command lists. The side condition is
discharged once per slot map — by the `idxOf` length bound for the
first-appearance maps (`slotOfDbl`, `slotOfAdd`), and by the lookup-default
bound for the keyed ladder maps (`slotLadDbl`, `slotLadAdd`).

## Main results

* `emitFOpFramed_clean` — a framed field-op brick emits covered commands
  whenever every slot of its slot map keeps its four cell indices below
  `2 ^ 64`.
* `jacDblBodyFramed_coveredSCtl` / `jacAddBodyFramed_coveredSCtl` — the framed
  doubling and addition bodies lie in the control-extended covered fragment.
* `ladderStepFramed_coveredSCtl` — the whole framed ladder step (double body ++
  add body ++ select trip) lies in the control-extended covered fragment, the
  hypothesis `translateDialectControl_denote_ctl` takes.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LadderStepCovered

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp constInit loadField feH jacDblSchedule jacAddSchedule)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk CmdsClean NamesClean cmdsClean_append cmdsClean_map_range' cmdsClean_mapIdx
   isCoveredS_seqAll constInit_clean loadField_clean namesClean_feH
   feMulHalves_clean feAddHalves_clean feSubHalves_clean)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
  (emitFOpFramed brickFn idxCells storeFieldTo slotOfDbl dblNames frameCells
   jacDblBodyFramed)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedAdd
  (slotOfAdd addNames addFrameCells jacAddBodyFramed)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder
  (idxCells_clean storeFieldTo_clean emitSelectFramed_coveredS emitSelectFramed
   selectTrip ladderStepFramed ladderFrameCells slotLadDbl slotLadAdd slotLadSel
   ladderBitFetch_clean)

/-! ## 1. Slot-map cell-index bounds -/

/-- A slot index at most `99` keeps its highest cell index below `2 ^ 64`. -/
theorem lt64_of_le99 {n : Nat} (h : n ≤ 99) : 4 * n + 3 < 2 ^ 64 := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  omega

/-- A keyed lookup with an in-bound default and in-bound values stays in
    bound. -/
theorem lookup_getD_le (l : List (String × Nat)) (s : String) (d bound : Nat)
    (hd : d ≤ bound) (hv : ∀ p ∈ l, p.2 ≤ bound) :
    (l.lookup s).getD d ≤ bound := by
  induction l with
  | nil => simpa using hd
  | cons p t ih =>
      obtain ⟨k, v⟩ := p
      rw [List.lookup_cons]
      split
      · simpa using hv (k, v) List.mem_cons_self
      · exact ih (fun q hq => hv q (List.mem_cons_of_mem _ hq))

/-- Every `slotOfDbl` slot index is at most `99`: an `idxOf` into the 22-name
    doubling layout is at most the layout's length. -/
theorem slotOfDbl_le (s : String) : slotOfDbl s ≤ 99 := by
  have h : dblNames.idxOf s ≤ dblNames.length := List.idxOf_le_length
  have hlen : dblNames.length = 22 := rfl
  show dblNames.idxOf s ≤ 99
  omega

/-- Every `slotOfAdd` slot index is at most `99`: an `idxOf` into the 29-name
    addition layout is at most the layout's length. -/
theorem slotOfAdd_le (s : String) : slotOfAdd s ≤ 99 := by
  have h : addNames.idxOf s ≤ addNames.length := List.idxOf_le_length
  have hlen : addNames.length = 29 := rfl
  show addNames.idxOf s ≤ 99
  omega

/-- Every `slotLadDbl` slot index is at most `99` — each keyed value and the
    lookup default are. -/
theorem slotLadDbl_le (s : String) : slotLadDbl s ≤ 99 :=
  lookup_getD_le _ s 99 99 le_rfl (by decide)

/-- Every `slotLadAdd` slot index is at most `99` — each keyed value and the
    lookup default are. -/
theorem slotLadAdd_le (s : String) : slotLadAdd s ≤ 99 :=
  lookup_getD_le _ s 99 99 le_rfl (by decide)

/-- `slotOfDbl` keeps every cell index in 64 bits. -/
theorem slotOfDbl_lt (s : String) : 4 * slotOfDbl s + 3 < 2 ^ 64 :=
  lt64_of_le99 (slotOfDbl_le s)

/-- `slotOfAdd` keeps every cell index in 64 bits. -/
theorem slotOfAdd_lt (s : String) : 4 * slotOfAdd s + 3 < 2 ^ 64 :=
  lt64_of_le99 (slotOfAdd_le s)

/-- `slotLadDbl` keeps every cell index in 64 bits. -/
theorem slotLadDbl_lt (s : String) : 4 * slotLadDbl s + 3 < 2 ^ 64 :=
  lt64_of_le99 (slotLadDbl_le s)

/-- `slotLadAdd` keeps every cell index in 64 bits. -/
theorem slotLadAdd_lt (s : String) : 4 * slotLadAdd s + 3 < 2 ^ 64 :=
  lt64_of_le99 (slotLadAdd_le s)

/-! ## 2. The framed field-op brick is covered -/

/-- The brick body of any field op emits covered commands and non-temp result
    names at the brick-local operand names `pfx ++ "A"` / `pfx ++ "B"`. -/
theorem brickFn_clean (op : FOp) (pfx : String) (hpfx : HeadOk pfx) :
    CmdsClean ((brickFn op).1 (pfx ++ "C") (feH (pfx ++ "A")) (feH (pfx ++ "B"))).1
      ∧ NamesClean ((brickFn op).1 (pfx ++ "C") (feH (pfx ++ "A")) (feH (pfx ++ "B"))).2 := by
  have hA := namesClean_feH (pfx ++ "A") (HeadOk.append hpfx "A")
  have hB := namesClean_feH (pfx ++ "B") (HeadOk.append hpfx "B")
  have hC : HeadOk (pfx ++ "C") := HeadOk.append hpfx "C"
  cases op with
  | mul o a b => exact feMulHalves_clean _ _ _ hA hB hC
  | add o a b => exact feAddHalves_clean _ _ _ hA hB hC
  | sub o a b => exact feSubHalves_clean _ _ _ hA hB hC

/-- Coverage of the assembled framed brick at explicit slot indices: the
    twelve cell-index binds, the constants, the two frame loads, the brick
    body, the eight result copies and the frame store are all `IsCoveredS`
    arms. -/
theorem framedParts_clean (fw : Nat) (frame : String) (sa sb so : Nat) (pfx : String)
    (hpfx : HeadOk pfx) (bc : List LowCT) (br : List String)
    (hbc : CmdsClean bc) (hbr : NamesClean br)
    (ha : 4 * sa + 3 < 2 ^ 64) (hb : 4 * sb + 3 < 2 ^ 64) (ho : 4 * so + 3 < 2 ^ 64) :
    CmdsClean (idxCells ((List.range 4).map (4 * sa + ·) ++ (List.range 4).map (4 * sb + ·)
        ++ (List.range 4).map (4 * so + ·))
      ++ constInit
      ++ loadField fw frame (4 * sa) (pfx ++ "A")
      ++ loadField fw frame (4 * sb) (pfx ++ "B")
      ++ bc
      ++ (List.range 8).map (fun k => (.RScalarSetExpr s!"{pfx}Oh{k}" (sv (br[k]!)) : LowCT))
      ++ storeFieldTo fw frame (4 * so) (pfx ++ "O")) := by
  refine cmdsClean_append (cmdsClean_append (cmdsClean_append (cmdsClean_append
      (cmdsClean_append (cmdsClean_append (idxCells_clean _ ?_) constInit_clean)
        (loadField_clean fw frame _ _ (HeadOk.append hpfx "A")))
      (loadField_clean fw frame _ _ (HeadOk.append hpfx "B")))
      hbc)
      (cmdsClean_map_range' 8 _ (fun k _ => .rScalarSetExpr _ _ (hbr k))))
      (storeFieldTo_clean fw frame _ _ (HeadOk.append hpfx "O"))
  intro c hc
  rcases List.mem_append.mp hc with hab | hco
  · rcases List.mem_append.mp hab with hca | hcb
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hca
      have hj4 := List.mem_range.mp hj
      omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcb
      have hj4 := List.mem_range.mp hj
      omega
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hco
    have hj4 := List.mem_range.mp hj
    omega

/-- **A framed field-op brick lies in the straight-line covered scalar
    fragment** whenever its slot map keeps every slot's four cell indices in
    64 bits: every command is a literal index bind, a dynamic-index frame load
    or store, or a `srcClean` scalar assignment, so the front's
    `RScalarSetExpr` / `RArrLoad` / `RArrStore` arms cover it structurally. -/
theorem emitFOpFramed_clean (fw : Nat) (frame : String) (slotOf : String → Nat)
    (idx : Nat) (op : FOp) (hslot : ∀ s, 4 * slotOf s + 3 < 2 ^ 64) :
    CmdsClean (emitFOpFramed fw frame slotOf idx op) := by
  have hpfx : HeadOk s!"fop{idx}" :=
    HeadOk.append (⟨'f', ['o', 'p'], rfl, by decide⟩ : HeadOk "fop") _
  obtain ⟨hbc, hbn⟩ := brickFn_clean op s!"fop{idx}" hpfx
  cases op with
  | mul o a b =>
      exact framedParts_clean fw frame (slotOf a) (slotOf b) (slotOf o) _ hpfx _ _
        hbc hbn (hslot a) (hslot b) (hslot o)
  | add o a b =>
      exact framedParts_clean fw frame (slotOf a) (slotOf b) (slotOf o) _ hpfx _ _
        hbc hbn (hslot a) (hslot b) (hslot o)
  | sub o a b =>
      exact framedParts_clean fw frame (slotOf a) (slotOf b) (slotOf o) _ hpfx _ _
        hbc hbn (hslot a) (hslot b) (hslot o)

/-! ## 3. The framed point-op bodies are covered -/

/-- **The frame-relative `jacDbl` body is in the straight-line scalar covered
    fragment**: each of its nineteen framed bricks is, at the `slotOfDbl` cell
    indices. -/
theorem jacDblBodyFramed_coveredS : IsCoveredS jacDblBodyFramed :=
  isCoveredS_seqAll _ (cmdsClean_mapIdx jacDblSchedule _
    (fun i op _ => emitFOpFramed_clean (8 * frameCells) "F" slotOfDbl i op slotOfDbl_lt))

/-- **The frame-relative `jacDbl` body is in the control-extended covered
    fragment**, the hypothesis `translateDialectControl_denote_ctl` takes. -/
theorem jacDblBodyFramed_coveredSCtl : IsCoveredSCtl jacDblBodyFramed :=
  .ofStraight jacDblBodyFramed_coveredS

/-- **The frame-relative `jacAdd` body is in the straight-line scalar covered
    fragment**: each of its twenty-three framed bricks is, at the `slotOfAdd`
    cell indices. -/
theorem jacAddBodyFramed_coveredS : IsCoveredS jacAddBodyFramed :=
  isCoveredS_seqAll _ (cmdsClean_mapIdx jacAddSchedule _
    (fun i op _ => emitFOpFramed_clean (8 * addFrameCells) "F" slotOfAdd i op slotOfAdd_lt))

/-- **The frame-relative `jacAdd` body is in the control-extended covered
    fragment.** -/
theorem jacAddBodyFramed_coveredSCtl : IsCoveredSCtl jacAddBodyFramed :=
  .ofStraight jacAddBodyFramed_coveredS

/-! ## 4. The framed ladder step is covered -/

/-- The select trip's flat command list is covered: each of its three framed
    selects is, at the concrete `slotLadSel` cell indices. -/
theorem selectTrip_clean : CmdsClean selectTrip := by
  refine cmdsClean_append (cmdsClean_append ?_ ?_) ?_
  all_goals
    exact emitSelectFramed_coveredS (8 * ladderFrameCells) slotLadSel _ _ _ _ _
      (by decide) (by decide) (by decide) (by decide)

/-- **The framed ladder step is in the straight-line scalar covered
    fragment**: the per-trip key-bit fetch, the doubling bricks at the
    `slotLadDbl` indices, the addition bricks at the `slotLadAdd` indices, and
    the select trip at the `slotLadSel` indices are all covered. -/
theorem ladderStepFramed_coveredS : IsCoveredS ladderStepFramed :=
  isCoveredS_seqAll _
    (cmdsClean_append
      (cmdsClean_append
        (cmdsClean_append
          ladderBitFetch_clean
          (cmdsClean_mapIdx jacDblSchedule _ (fun i op _ =>
            emitFOpFramed_clean (8 * ladderFrameCells) "F" slotLadDbl i op slotLadDbl_lt)))
        (cmdsClean_mapIdx jacAddSchedule _ (fun i op _ =>
          emitFOpFramed_clean (8 * ladderFrameCells) "F" slotLadAdd i op slotLadAdd_lt)))
      selectTrip_clean)

/-- **The framed ladder step is in the control-extended covered fragment**, the
    hypothesis `translateDialectControl_denote_ctl` takes. -/
theorem ladderStepFramed_coveredSCtl : IsCoveredSCtl ladderStepFramed :=
  .ofStraight ladderStepFramed_coveredS

end CatCrypt.Crypto.SecureCompilation.X86Backend.LadderStepCovered
