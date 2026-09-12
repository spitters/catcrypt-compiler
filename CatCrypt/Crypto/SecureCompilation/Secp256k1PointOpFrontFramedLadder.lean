/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedAdd

/-!
# secp256k1 frame-relative ladder step: the conditional-select brick and the assembly

A frame-relative doubling body (`Secp256k1PointOpFrontFramed.jacDblBodyFramed`) and
a frame-relative addition body (`Secp256k1PointOpFrontFramedAdd.jacAddBodyFramed`)
are composed here into one ladder step over a single memref frame `F`, together with
the two new bricks their composition needs: a frame-relative conditional select,
and a per-trip key-bit fetch that derives the select's selector word from the
loop-index variable.

## The framed select brick

`emitSelectFramed` selects, per limb and branch-free, between two candidate field
elements loaded from their frame slots, keyed on a selector word loaded from the
frame. With the selector word `bit ∈ {0, 1}` it forms the limb mask
`bit · 0xFFFFFFFF` and writes `B ^ ((A ^ B) & mask)` — the candidate `A` when
`bit = 1`, the candidate `B` when `bit = 0` — into the output slot. It reuses the
shared operand-load prefix and store of `emitFOpFramed`
(`Secp256k1PointOpFramedValue.framed_assemble`); the select is not an `FOp`, so its
body replaces the field-op brick body with a literal binding of the selector cell
index, a frame load of the selector word at that index, and the per-limb selects.
The index binding is what lets the front's dynamic-index `RArrLoad` arm resolve
the load (it requires the index variable to be bound) rather than falling to the
opaque `extCall "arrLoadDyn"` leaf.

## The per-trip key-bit fetch

`ladderBitFetch` sources the selector word from the key: it binds the key-bit
cell index `ladderBitBase + i` by index arithmetic over the loop-index variable
`i` (an `RScalarSetExpr` in the covered `SExpr` fragment), loads the key bit
from that frame cell with the dynamic-index `RArrLoad` arm, binds the selector
cell index (the first cell of slot `51`), and stores the key bit there with the
dynamic-index `RArrStore` arm — the cell every select of the trip reads.

## The unified slot layout

The ladder step doubles the accumulator, adds the fixed base point to the doubled
accumulator, and selects between the sum and the doubled accumulator on the key
bit. Both addition operands are computed rows, so the key bit reaches the step
only through the final select. A single frame `F` carries every field element, and
three slot maps place the boundary values so the accumulator persists across the
trip without a copy:

* slots `0,1,2` — the accumulator `(X,Y,Z)`, read by the double, overwritten by
  the select's outputs;
* slots `3,4,5` — the doubled point, written by the double's outputs `(Xp,Yp,Zp)`,
  read by the add's first input `(X1,Y1,Z1)` and by the select's key-bit-`0`
  candidate;
* slots `6,7,8` — the sum, written by the add's outputs `(Xp,Yp,Zp)` and read by
  the select's key-bit-`1` candidate;
* slots `9,10,11` — the base-point row, read by the add's second input
  `(X2,Y2,Z2)`;
* slots `15..30` — the doubling intermediates;
* slots `31..50` — the addition intermediates;
* slot `51` (its first cell, cell `204`) — the selector word read by every select
  of the trip;
* cells `208..255` — the key-bit region: cell `ladderBitBase + i` holds the key
  bit (value `0` or `1`) the trip at loop index `i` consumes, one bit per cell,
  so one frame carries a 48-trip window.

The doubling range, the addition range and the base-point row are pairwise
disjoint; the boundary slots `0..8` are the only shared ones and are shared by
intent. The key-bit region lies above every cell the three slot maps assign
(`0..207`).

## Main results

* `emitSelectFramed` — the frame-relative conditional-select brick as a `List LowCT`.
* `emitSelectFramed_runs` — the select brick runs to a defined exit environment from
  any input environment.
* `emitSelectFramed_coveredS` / `selectTrip_coveredSCtl` — the select brick (and the
  three-select trip at the concrete slot map) lies in the front's covered scalar
  fragment, so the front covers it structurally.
* `ladderBitFetch` — the per-trip key-bit fetch as a `List LowCT`.
* `ladderBitFetch_clean` — the fetch lies in the front's covered scalar fragment.
* `ladderBitFetch_runs` — the fetch runs from any environment binding the loop
  index `i` at 64-bit word type.
* `ladderBitFetch_spec` — the fetch writes the key-bit cell's value for the
  current loop index into the selector cell and leaves every other frame cell
  and every other non-temporary name unchanged.
* `ladderStepFramed` — the framed ladder step: key-bit fetch ++ double body ++
  add body ++ select trip over the single frame `F` with the unified slot maps.
* `ladderStepFramed_runs` — the whole framed ladder step runs to a defined exit
  environment from any input environment binding the loop index at word type.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp constInit loadField feH jacDblSchedule jacAddSchedule)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk CmdsClean cmdsClean_nil cmdsClean_cons cmdsClean_append cmdsClean_map_range'
   cmdsClean_flatMap_range isCoveredS_seqAll constInit_clean loadField_clean lt64_32
   notTmp_of_len)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote (semScalar_seqAll_append)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal
  (RunsFrom ReadsFrom SrcSet AllIn runsFrom_addPre runsFrom_append runsFrom_mapRange
   readsFrom_var readsFrom_lit readsFrom_xor readsFrom_and readsFrom_mul
   readsFrom_add map_range_getBang semLowerSExpr_run)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed (idxCells storeFieldTo)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedAdd (slotOfAdd)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue
  (Bbody bbody_src arrLoad1_runs framed_assemble mapIdxFlatten_runs
   runsFrom_litSetExpr arrStore_runs)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (semScalar_setExpr_run semScalar_arrLoad semScalar_arrStore seqAll_step)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed (emitFOpFramed)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue (emitFOpFramed_runs)

/-! ## 1. The framed select brick -/

/-- The brick body of a frame-relative select: a literal binding of the selector
    cell index `cbit`, a frame load of the selector word `bit` at that index, and
    the eight per-limb branch-free selects
    `Sel{k} = B{k} ^ ((A{k} ^ B{k}) & (bit · 0xFFFFFFFF))`. The pair carries the body
    and the eight result half-limb names, in the shape `framed_assemble` consumes. -/
def selBody (fw cbit : Nat) (pfx : String) : List LowCT × List String :=
  ((.RScalarSetExpr s!"{pfx}ixbit" (.SLit cbit) : LowCT)
      :: (.RArrLoad ⟨s!"{pfx}bit", .TU64⟩ ⟨"F", .TBytes fw⟩ s!"{pfx}ixbit" : LowCT)
      :: (List.range 8).map (fun k =>
        (.RScalarSetExpr s!"{pfx}Sel{k}"
          (.SXor (sv s!"{pfx ++ "B"}h{k}")
            (.SAnd (.SXor (sv s!"{pfx ++ "A"}h{k}") (sv s!"{pfx ++ "B"}h{k}"))
              (.SMul (sv s!"{pfx}bit") (.SLit 4294967295)))) : LowCT)),
    (List.range 8).map (fun k => s!"{pfx}Sel{k}"))

/-- Emit a frame-relative conditional select `fop{idx}` over frame `F` (`fw` bytes
    wide, slots assigned by `slotOf`): load both candidate field elements from their
    slots (`a`, `b`), bind the selector cell index (the first cell of slot `s`) and
    load the selector word from it, form the eight per-limb selects, and store the
    eight results into the output slot (`o`). Reuses the shared operand-load prefix
    and frame store of `emitFOpFramed`. -/
def emitSelectFramed (fw : Nat) (slotOf : String → Nat) (idx : Nat) (s a b o : String) :
    List LowCT :=
  idxCells ((List.range 4).map (4 * slotOf a + ·) ++ (List.range 4).map (4 * slotOf b + ·)
      ++ (List.range 4).map (4 * slotOf o + ·))
    ++ constInit
    ++ loadField fw "F" (4 * slotOf a) (s!"fop{idx}" ++ "A")
    ++ loadField fw "F" (4 * slotOf b) (s!"fop{idx}" ++ "B")
    ++ (selBody fw (4 * slotOf s) s!"fop{idx}").1
    ++ (List.range 8).map (fun k =>
        (.RScalarSetExpr s!"{s!"fop{idx}"}Oh{k}"
          (sv ((selBody fw (4 * slotOf s) s!"fop{idx}").2[k]!)) : LowCT))
    ++ storeFieldTo fw "F" (4 * slotOf o) (s!"fop{idx}" ++ "O")

/-! ## 2. The select brick runs -/

/-- **One frame-relative select brick runs from any environment.** The frame loads
    and store never decline, and the brick binds every word the per-limb selects read
    (the two operand half-limb slots it loads from the frame, the selector cell
    index and the frame-loaded selector word). -/
theorem emitSelectFramed_runs (fw : Nat) (slotOf : String → Nat) (idx : Nat)
    (s a b o : String) (env : SEnvScalar) :
    ∃ env', semScalar (seqAll (emitSelectFramed fw slotOf idx s a b o)) env = some env' := by
  have hpfx : HeadOk s!"fop{idx}" :=
    HeadOk.append (⟨'f', ['o', 'p'], rfl, by decide⟩ : HeadOk "fop") _
  have hntBit : ¬ isTmpName s!"{s!"fop{idx}"}bit" :=
    HeadOk.notTmp (HeadOk.append hpfx "bit")
  have hntIx : ¬ isTmpName s!"{s!"fop{idx}"}ixbit" :=
    HeadOk.notTmp (HeadOk.append hpfx "ixbit")
  -- The select body runs from the operand-load exit set `Bbody`.
  refine framed_assemble fw idx slotOf a b o env s!"fop{idx}" rfl hpfx
    (selBody fw (4 * slotOf s) s!"fop{idx}").1 (selBody fw (4 * slotOf s) s!"fop{idx}").2
    (by simp [selBody]) ?_
  -- Assemble the brick-body run predicate `hbrick`.
  set pfx := s!"fop{idx}" with hpfxdef
  -- The literal binding of the selector cell index.
  have hset := runsFrom_addPre
    (runsFrom_litSetExpr (Bbody pfx) s!"{pfx}ixbit" (4 * slotOf s) hntIx)
  -- The frame load of the selector word, keeping the earlier names bound.
  have hload' := runsFrom_append hset
    (arrLoad1_runs (fun y => y = s!"{pfx}ixbit" ∨ Bbody pfx y) s!"{pfx}bit"
      (⟨"F", .TBytes fw⟩ : Located) s!"{pfx}ixbit" hntBit)
    (fun x hx => Or.inr hx)
  -- The exit set after the eight per-limb selects.
  refine ⟨fun y => (((y = s!"{pfx}ixbit" ∨ Bbody pfx y) ∨ y = s!"{pfx}bit")
      ∨ ∃ i, i < 8 ∧ y = s!"{pfx}Sel{i}"),
    ?_, ?_, ?_, ?_⟩
  · -- `SrcSet`: every exit name is outside the reserved fresh-temporary namespace.
    rintro y ((((rfl | hb) | rfl) | ⟨i, _, rfl⟩))
    · exact hntIx
    · exact bbody_src pfx hpfx y hb
    · exact hntBit
    · exact HeadOk.notTmp (HeadOk.append (HeadOk.append hpfx "Sel") _)
  · -- The operand-load set is contained in the exit set.
    exact fun x hx => Or.inl (Or.inl (Or.inr hx))
  · -- The body runs from `Bbody pfx`.
    have hmap := runsFrom_mapRange (B := Bbody pfx)
      (nm := fun k => s!"{pfx}Sel{k}")
      (ex := fun k => (.SXor (sv s!"{pfx ++ "B"}h{k}")
        (.SAnd (.SXor (sv s!"{pfx ++ "A"}h{k}") (sv s!"{pfx ++ "B"}h{k}"))
          (.SMul (sv s!"{pfx}bit") (.SLit 4294967295)))))
      hload' 8
      (fun k _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hpfx "Sel") _))
      (fun k hk => readsFrom_xor
        (readsFrom_var
          (HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append hpfx "B") "h") _))
          (Or.inl (Or.inr (Or.inr ⟨k, hk, rfl⟩))))
        (readsFrom_and
          (readsFrom_xor
            (readsFrom_var
              (HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append hpfx "A") "h") _))
              (Or.inl (Or.inr (Or.inl (Or.inr ⟨k, hk, rfl⟩)))))
            (readsFrom_var
              (HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append hpfx "B") "h") _))
              (Or.inl (Or.inr (Or.inr ⟨k, hk, rfl⟩)))))
          (readsFrom_mul
            (readsFrom_var hntBit (Or.inr rfl))
            (readsFrom_lit (by norm_num)))))
    exact hmap
  · -- Every result name lies in the exit set.
    intro k hk
    have hk8 : k < 8 := by
      simpa [selBody] using hk
    rw [show (selBody fw (4 * slotOf s) pfx).2[k]! = s!"{pfx}Sel{k}" from by
      simp only [selBody]; exact map_range_getBang 8 _ k hk8]
    exact Or.inr ⟨k, hk8, rfl⟩

/-! ## 2b. The select brick lies in the covered scalar fragment -/

/-- The cell-index binds of `idxCells` are covered when every cell index fits in
    64 bits. -/
theorem idxCells_clean (cells : List Nat) (h : ∀ c ∈ cells, c < 2 ^ 64) :
    CmdsClean (idxCells cells) := by
  intro c hc
  simp only [idxCells, List.mem_map] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact .rScalarSetExpr _ _ (h i hi)

/-- The array-name-general frame store emits covered commands: `srcClean` limb
    recombinations and dynamic-index `RArrStore`s. -/
theorem storeFieldTo_clean (fw : Nat) (arr : String) (o : Nat) (fe : String)
    (h : HeadOk fe) : CmdsClean (storeFieldTo fw arr o fe) := by
  have hh : ∀ j : Nat, ¬ isTmpName (s!"{fe}h{j}") :=
    fun j => HeadOk.notTmp (HeadOk.append (HeadOk.append h _) _)
  refine cmdsClean_flatMap_range 4 _ (fun j _ => ?_)
  exact cmdsClean_cons (.rScalarSetExpr _ _ ⟨hh (2 * j), ⟨hh (2 * j + 1), lt64_32⟩⟩)
    (cmdsClean_cons (.rArrStore _ _ _) cmdsClean_nil)

/-- The select brick body emits covered commands: a literal index bind, a
    dynamic-index `RArrLoad`, and eight `srcClean` per-limb selects. -/
theorem selBody_clean (fw cbit : Nat) (pfx : String) (hpfx : HeadOk pfx)
    (hc : cbit < 2 ^ 64) : CmdsClean (selBody fw cbit pfx).1 := by
  have hntBit : ¬ isTmpName s!"{pfx}bit" := HeadOk.notTmp (HeadOk.append hpfx "bit")
  have hA : ∀ k : Nat, ¬ isTmpName s!"{pfx ++ "A"}h{k}" :=
    fun k => HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append hpfx "A") "h") _)
  have hB : ∀ k : Nat, ¬ isTmpName s!"{pfx ++ "B"}h{k}" :=
    fun k => HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append hpfx "B") "h") _)
  exact cmdsClean_cons (.rScalarSetExpr _ _ hc)
    (cmdsClean_cons (.rArrLoad _ _ _)
      (cmdsClean_map_range' 8 _ (fun k _ =>
        .rScalarSetExpr _ _
          ⟨hB k, ⟨hA k, hB k⟩, hntBit, (by norm_num : (4294967295 : Nat) < 2 ^ 64)⟩)))

/-- **The framed select brick lies in the straight-line covered scalar
    fragment** whenever its four slots' cell indices fit in 64 bits: every
    command is a literal index bind, a dynamic-index frame load or store, or a
    `srcClean` scalar assignment, so the front's `RScalarSetExpr` / `RArrLoad` /
    `RArrStore` arms cover it structurally. -/
theorem emitSelectFramed_coveredS (fw : Nat) (slotOf : String → Nat) (idx : Nat)
    (s a b o : String) (ha : 4 * slotOf a + 3 < 2 ^ 64) (hb : 4 * slotOf b + 3 < 2 ^ 64)
    (ho : 4 * slotOf o + 3 < 2 ^ 64) (hs : 4 * slotOf s < 2 ^ 64) :
    CmdsClean (emitSelectFramed fw slotOf idx s a b o) := by
  have hpfx : HeadOk s!"fop{idx}" :=
    HeadOk.append (⟨'f', ['o', 'p'], rfl, by decide⟩ : HeadOk "fop") _
  refine cmdsClean_append (cmdsClean_append (cmdsClean_append (cmdsClean_append
      (cmdsClean_append (cmdsClean_append (idxCells_clean _ ?cells) constInit_clean)
        (loadField_clean fw "F" (4 * slotOf a) (s!"fop{idx}" ++ "A") (HeadOk.append hpfx "A")))
      (loadField_clean fw "F" (4 * slotOf b) (s!"fop{idx}" ++ "B") (HeadOk.append hpfx "B")))
    (selBody_clean fw (4 * slotOf s) s!"fop{idx}" hpfx hs)) ?copies)
    (storeFieldTo_clean fw "F" (4 * slotOf o) (s!"fop{idx}" ++ "O") (HeadOk.append hpfx "O"))
  case cells =>
    intro c hcm
    rcases List.mem_append.mp hcm with hab | hco
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
  case copies =>
    refine cmdsClean_map_range' 8 _ (fun k hk => ?_)
    rw [show (selBody fw (4 * slotOf s) s!"fop{idx}").2[k]! = s!"{s!"fop{idx}"}Sel{k}" from by
      simp only [selBody]; exact map_range_getBang 8 _ k hk]
    exact .rScalarSetExpr _ _
      (HeadOk.notTmp (HeadOk.append (HeadOk.append hpfx "Sel") _))

/-! ## 3. The unified slot layout -/

/-- The number of frame cells the ladder-step frame `F` holds (`256` cells,
    `2048` bytes) — comfortably covering the highest slot the layout uses. -/
def ladderFrameCells : Nat := 256

/-- Slot map of the doubling body: the accumulator inputs at `0,1,2`, the doubled
    outputs `(Xp,Yp,Zp)` at `3,4,5`, the sixteen doubling intermediates at `15..30`. -/
def slotLadDbl (s : String) : Nat :=
  ([("X", 0), ("Y", 1), ("Z", 2), ("Xp", 3), ("Yp", 4), ("Zp", 5),
    ("YY", 15), ("XYY", 16), ("S2", 17), ("S", 18), ("XX", 19), ("M2", 20), ("M", 21),
    ("Msq", 22), ("TwoS", 23), ("SmXp", 24), ("MSmXp", 25), ("YYsq", 26), ("Y2", 27),
    ("Y4", 28), ("Y8", 29), ("YZ", 30)].lookup s).getD 99

/-- Slot map of the addition body: the first input `(X1,Y1,Z1)` at the doubled slots
    `3,4,5`, the second input `(X2,Y2,Z2)` at the base-point row `9,10,11`, the
    outputs `(Xp,Yp,Zp)` at the sum slots `6,7,8`, the twenty addition
    intermediates at `31..50`. -/
def slotLadAdd (s : String) : Nat :=
  ([("X1", 3), ("Y1", 4), ("Z1", 5), ("X2", 9), ("Y2", 10), ("Z2", 11),
    ("Xp", 6), ("Yp", 7), ("Zp", 8),
    ("Z1sq", 31), ("Z2sq", 32), ("Z1cu", 33), ("Z2cu", 34), ("U1", 35), ("U2", 36),
    ("S1", 37), ("S2", 38), ("H", 39), ("R", 40), ("Hsq", 41), ("Hcu", 42), ("U1Hsq", 43),
    ("Rsq", 44), ("T", 45), ("TwoU1Hsq", 46), ("U1HsqX3", 47), ("RU", 48), ("S1Hcu", 49),
    ("Z1Z2", 50)].lookup s).getD 99

/-- Slot map of the select trip: the two candidate rows (the sum at `6,7,8`, the
    doubled accumulator at `3,4,5`), the accumulator output `(accX,accY,accZ)` at
    `0,1,2`, and the selector word at slot `51` (its first cell, cell `204`). -/
def slotLadSel (s : String) : Nat :=
  ([("sumX", 6), ("sumY", 7), ("sumZ", 8), ("midX", 3), ("midY", 4), ("midZ", 5),
    ("accX", 0), ("accY", 1), ("accZ", 2), ("bit", 51)].lookup s).getD 99

/-! ## 3b. The per-trip key-bit fetch -/

/-- First cell of the key-bit region: cells `ladderBitBase + i` hold the key
    bits, one per cell, above every cell the three slot maps assign (`0..207`)
    and inside the 256-cell frame for loop indices `i < 48`. -/
def ladderBitBase : Nat := 208

/-- The per-trip key-bit fetch: bind the key-bit cell index `ladderBitBase + i`
    from the loop-index variable `i`, load the key bit from that frame cell,
    bind the selector cell index (the first cell of slot `51`), and store the
    key bit there — the cell every select of the trip reads. -/
def ladderBitFetch : List LowCT :=
  [(.RScalarSetExpr "ladixkey" (.SAdd (sv "i") (.SLit ladderBitBase)) : LowCT),
   (.RArrLoad ⟨"ladkeybit", .TU64⟩ ⟨"F", .TBytes (8 * ladderFrameCells)⟩ "ladixkey" : LowCT),
   (.RScalarSetExpr "ladixbit" (.SLit (4 * slotLadSel "bit")) : LowCT),
   (.RArrStore ⟨"F", .TBytes (8 * ladderFrameCells)⟩ "ladixbit"
     (⟨"ladkeybit", .TU64⟩ : Located) : LowCT)]

/-- The key-bit word the fetch binds is outside the reserved fresh-temporary
    namespace. -/
theorem notTmp_ladkeybit : ¬ isTmpName "ladkeybit" :=
  HeadOk.notTmp ⟨'l', ['a', 'd', 'k', 'e', 'y', 'b', 'i', 't'], rfl, by decide⟩

/-- **The key-bit fetch lies in the straight-line covered scalar fragment**: an
    index-arithmetic bind over the loop index, a dynamic-index frame load, a
    literal index bind, and a dynamic-index frame store. -/
theorem ladderBitFetch_clean : CmdsClean ladderBitFetch :=
  cmdsClean_cons (.rScalarSetExpr _ _
      ⟨notTmp_of_len "i" (by decide), show ladderBitBase < 2 ^ 64 by decide⟩)
    (cmdsClean_cons (.rArrLoad _ _ _)
      (cmdsClean_cons (.rScalarSetExpr _ _ (show 4 * slotLadSel "bit" < 2 ^ 64 by decide))
        (cmdsClean_cons (.rArrStore _ _ _) cmdsClean_nil)))

/-- The key-bit cell-index expression lowers to a defined result whenever the
    loop index `i` is bound at 64-bit word type. -/
theorem lowerKeyIx_isSome {env : SEnvScalar} {iv : BitVec 64}
    (hi : env "i" = some ⟨.sword 64, iv⟩) :
    (semLowerSExpr env 0 (.SAdd (sv "i") (.SLit ladderBitBase))).isSome := by
  have hrd : ReadsFrom (fun y => y = "i") (.SAdd (sv "i") (.SLit ladderBitBase)) :=
    readsFrom_add (readsFrom_var (notTmp_of_len "i" (by decide)) rfl)
      (readsFrom_lit (by decide))
  obtain ⟨e2, nm, cnt', hh, -⟩ := semLowerSExpr_run _ env 0 hrd.1
    (fun s hs => by rw [hrd.2 s hs]; simp only [envReadU64, hi, Option.isSome_some])
  rw [hh]
  rfl

/-- **The key-bit fetch runs from any environment binding the loop index `i` at
    64-bit word type.** The frame load and store never decline, and the two
    index binds read only `i` and a literal. -/
theorem ladderBitFetch_runs (env : SEnvScalar) (iv : BitVec 64)
    (hi : env "i" = some ⟨.sword 64, iv⟩) :
    ∃ env', semScalar (seqAll ladderBitFetch) env = some env' := by
  obtain ⟨e1, hs1, -, -⟩ := semScalar_setExpr_run (y := "ladixkey") (lowerKeyIx_isSome hi)
  have hstep2 : ∃ e2, semScalar
      (.RArrLoad ⟨"ladkeybit", .TU64⟩ ⟨"F", .TBytes (8 * ladderFrameCells)⟩ "ladixkey") e1
      = some e2 := by
    simp only [semScalar]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨e2, hs2⟩ := hstep2
  obtain ⟨e3, hs3, -, -⟩ := semScalar_setExpr_run (y := "ladixbit")
    (e := .SLit (4 * slotLadSel "bit")) (env := e2)
    (by simp only [semLowerSExpr, Option.isSome_some])
  obtain ⟨e4, hs4, -⟩ := arrStore_runs ⟨"F", .TBytes (8 * ladderFrameCells)⟩
    ⟨"ladkeybit", .TU64⟩ "ladixbit" e3
  refine ⟨e4, ?_⟩
  unfold ladderBitFetch
  rw [seqAll_step hs1, seqAll_step hs2, seqAll_step hs3]
  exact hs4

/-- **The key-bit fetch writes the key bit for the current loop index into the
    selector cell.** Running `ladderBitFetch` from an environment whose frame
    `F` holds `arr` and whose loop index `i` holds a word inside the key window
    lands a frame equal to `arr` except that the selector cell (the first cell
    of slot `51`) holds the key-bit cell's value; the loop index and every
    non-temporary name other than the frame and the fetch's three scratch words
    are unchanged. -/
theorem ladderBitFetch_spec {env env' : SEnvScalar} {arr : Fin 256 → BitVec 64}
    {iv : BitVec 64}
    (hF : env "F" = some ⟨.memref 256, arr⟩)
    (hi : env "i" = some ⟨.sword 64, iv⟩)
    (hiv : iv.toNat < 48)
    (hrun : semScalar (seqAll ladderBitFetch) env = some env') :
    env' "F" = some ⟨.memref 256,
        memSetDyn arr (4 * slotLadSel "bit") (memGetDyn arr (ladderBitBase + iv.toNat))⟩
      ∧ env' "i" = some ⟨.sword 64, iv⟩
      ∧ ∀ s, ¬ isTmpName s → s ≠ "F" → s ≠ "ladixkey" → s ≠ "ladkeybit" →
          s ≠ "ladixbit" → env' s = env s := by
  -- Step 1: bind the key-bit cell index.
  obtain ⟨e1, hs1, hv1, hf1⟩ := semScalar_setExpr_run (y := "ladixkey") (lowerKeyIx_isSome hi)
  have hev1 : SExpr.evalBV (envReader env) (.SAdd (sv "i") (.SLit ladderBitBase))
      = iv + BitVec.ofNat 64 ladderBitBase := by
    simp only [SExpr.evalBV, sv, envReader, hi]
  rw [hev1] at hv1
  have hF1 : e1 "F" = some ⟨.memref 256, arr⟩ := by
    rw [hf1 "F" (notTmp_of_len "F" (by decide)) (by decide)]; exact hF
  have hi1 : e1 "i" = some ⟨.sword 64, iv⟩ := by
    rw [hf1 "i" (notTmp_of_len "i" (by decide)) (by decide)]; exact hi
  -- Step 2: load the key bit from the frame.
  obtain ⟨e2, hs2, hv2, hf2⟩ := semScalar_arrLoad (dstN := "ladkeybit")
    (tw := .TBytes (8 * ladderFrameCells)) hF1 hv1
  have hF2 : e2 "F" = some ⟨.memref 256, arr⟩ := by
    rw [hf2 "F" (by decide)]; exact hF1
  have hi2 : e2 "i" = some ⟨.sword 64, iv⟩ := by
    rw [hf2 "i" (by decide)]; exact hi1
  -- Step 3: bind the selector cell index.
  obtain ⟨e3, hs3, hv3, hf3⟩ := semScalar_setExpr_run (y := "ladixbit")
    (e := .SLit (4 * slotLadSel "bit")) (env := e2)
    (by simp only [semLowerSExpr, Option.isSome_some])
  have hev3 : SExpr.evalBV (envReader e2) (.SLit (4 * slotLadSel "bit"))
      = BitVec.ofNat 64 (4 * slotLadSel "bit") := rfl
  rw [hev3] at hv3
  have hF3 : e3 "F" = some ⟨.memref 256, arr⟩ := by
    rw [hf3 "F" (notTmp_of_len "F" (by decide)) (by decide)]; exact hF2
  have hi3 : e3 "i" = some ⟨.sword 64, iv⟩ := by
    rw [hf3 "i" (notTmp_of_len "i" (by decide)) (by decide)]; exact hi2
  have hv2' : e3 "ladkeybit" = some ⟨.sword 64,
      memGetDyn arr (iv + BitVec.ofNat 64 ladderBitBase).toNat⟩ := by
    rw [hf3 "ladkeybit" notTmp_ladkeybit (by decide)]; exact hv2
  -- Step 4: store the key bit into the selector cell.
  obtain ⟨e4, hs4, hv4, hf4⟩ := semScalar_arrStore (fw := 8 * ladderFrameCells)
    hF3 hv3 hv2'
  -- The two dynamic indices, as naturals.
  have hidx : (iv + BitVec.ofNat 64 ladderBitBase).toNat = ladderBitBase + iv.toNat := by
    have h208 : ladderBitBase % 2 ^ 64 = ladderBitBase :=
      Nat.mod_eq_of_lt (by norm_num [ladderBitBase])
    have hlt : iv.toNat + ladderBitBase < 2 ^ 64 := by
      have h256 : iv.toNat + ladderBitBase < 256 := by
        simp only [ladderBitBase]; omega
      exact lt_of_lt_of_le h256 (by norm_num)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, h208, Nat.mod_eq_of_lt hlt]
    omega
  have hbitc : (BitVec.ofNat 64 (4 * slotLadSel "bit")).toNat = 4 * slotLadSel "bit" := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by decide)
  rw [hidx, hbitc] at hv4
  -- Identify `env'` with the computed exit environment.
  have hchain : semScalar (seqAll ladderBitFetch) env = some e4 := by
    unfold ladderBitFetch
    rw [seqAll_step hs1, seqAll_step hs2, seqAll_step hs3]
    exact hs4
  rw [hchain] at hrun
  obtain rfl : e4 = env' := Option.some.inj hrun
  refine ⟨hv4, ?_, ?_⟩
  · rw [hf4 "i" (by decide)]; exact hi3
  · intro s hs hsF hsK hsB hsX
    rw [hf4 s hsF, hf3 s hs hsX, hf2 s hsB, hf1 s hs hsK]

/-! ## 4. The framed ladder step and its termination -/

/-- The select trip: one framed select per coordinate, keyed on the shared
    selector word at slot `bit`, writing the accumulator `(accX,accY,accZ)` from
    the sum row at key-bit word `1` and from the doubled row at key-bit word `0`. -/
def selectTrip : List LowCT :=
  emitSelectFramed (8 * ladderFrameCells) slotLadSel 0 "bit" "sumX" "midX" "accX"
    ++ emitSelectFramed (8 * ladderFrameCells) slotLadSel 1 "bit" "sumY" "midY" "accY"
    ++ emitSelectFramed (8 * ladderFrameCells) slotLadSel 2 "bit" "sumZ" "midZ" "accZ"

/-- **The framed ladder step over one frame `F`.** The key-bit fetch writes the
    trip's key bit from the key-bit region into the selector cell, the doubling
    body writes the doubled accumulator into the shared `(X1,Y1,Z1)` slots, the
    addition body adds the fixed base-point row to it into the sum slots, and the
    select trip writes the sum or the doubled accumulator back into the
    accumulator slots according to the selector cell. Both operands of the
    addition are the doubled accumulator and the base point, so the key bit
    chooses between two computed rows rather than steering an operand of the
    addition. -/
def ladderStepFramed : LowCT :=
  seqAll (
    ladderBitFetch
      ++ (jacDblSchedule.mapIdx
        (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadDbl i op)).flatten
      ++ (jacAddSchedule.mapIdx
        (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadAdd i op)).flatten
      ++ selectTrip)

/-- **The select trip lies in the direct control front's covered scalar
    fragment**: each of its three framed selects does, at the concrete
    `slotLadSel` cell indices. -/
theorem selectTrip_coveredSCtl : IsCoveredSCtl (seqAll selectTrip) := by
  refine .ofStraight (isCoveredS_seqAll _ (cmdsClean_append (cmdsClean_append ?_ ?_) ?_))
  all_goals
    exact emitSelectFramed_coveredS (8 * ladderFrameCells) slotLadSel _ _ _ _ _
      (by decide) (by decide) (by decide) (by decide)

/-- **The select trip runs from any environment.** -/
theorem selectTrip_runs (env : SEnvScalar) :
    ∃ env', semScalar (seqAll selectTrip) env = some env' := by
  obtain ⟨ea, ha⟩ := emitSelectFramed_runs (8 * ladderFrameCells) slotLadSel 0
    "bit" "sumX" "midX" "accX" env
  obtain ⟨eb, hb⟩ := emitSelectFramed_runs (8 * ladderFrameCells) slotLadSel 1
    "bit" "sumY" "midY" "accY" ea
  obtain ⟨ec, hc⟩ := emitSelectFramed_runs (8 * ladderFrameCells) slotLadSel 2
    "bit" "sumZ" "midZ" "accZ" eb
  refine ⟨ec, ?_⟩
  show semScalar (seqAll (_ ++ _ ++ _)) env = some ec
  rw [semScalar_seqAll_append, semScalar_seqAll_append, ha, Option.bind_some, hb,
    Option.bind_some, hc]

/-- **The framed ladder step runs to a defined exit environment from any input
    environment binding the loop index `i` at 64-bit word type.** The key-bit
    fetch runs from any such environment, and the doubling body, the addition
    body and the select trip each run unconditionally, so their composition over
    the single frame `F` does too. -/
theorem ladderStepFramed_runs (env : SEnvScalar) (iv : BitVec 64)
    (hi : env "i" = some ⟨.sword 64, iv⟩) :
    ∃ env', semScalar ladderStepFramed env = some env' := by
  obtain ⟨e0, h0⟩ := ladderBitFetch_runs env iv hi
  obtain ⟨e1, h1⟩ := mapIdxFlatten_runs jacDblSchedule
    (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadDbl i op)
    (fun i op e => emitFOpFramed_runs (8 * ladderFrameCells) slotLadDbl i op e) e0
  obtain ⟨e2, h2⟩ := mapIdxFlatten_runs jacAddSchedule
    (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadAdd i op)
    (fun i op e => emitFOpFramed_runs (8 * ladderFrameCells) slotLadAdd i op e) e1
  obtain ⟨e3, h3⟩ := selectTrip_runs e2
  refine ⟨e3, ?_⟩
  show semScalar (seqAll (_ ++ _ ++ _ ++ _)) env = some e3
  rw [semScalar_seqAll_append, semScalar_seqAll_append, semScalar_seqAll_append,
    h0, Option.bind_some, h1, Option.bind_some, h2, Option.bind_some, h3]

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder
