/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope
import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip

/-!
# The secp256k1 point-op epilogue: half-limbs back into the 12-cell output frame

`Secp256k1PointOpFront.jacDblBody` ends with
`storeField 96 0 "Xp" ++ storeField 96 4 "Yp" ++ storeField 96 8 "Zp"`. Each
`storeField 96 o fe` recombines the eight 32-bit half-limb slots of `fe` into
four `u64` and writes them into cells `o … o+3` of the `.TBytes 96` pointer
`out`, whose `CryptoTy` encoding is `.memref 12`.

Under `TranslateDialectScalar.semScalar` an `RArrStore` rebinds the name `out`
to the `memSetDyn`-updated array, so the epilogue's value statement is about the
array the final environment holds at `out`: its twelve cells carry
`pointCells (feVal env "Xp", feVal env "Yp", feVal env "Zp")`, the little-endian
`u64` limbs of the three half-limb residue readouts that the schedule waist
theorem `Secp256k1PointOpBrickScope.jacDblSchedule_waist_value_brickScope`
speaks about.

`Secp256k1PointOpFrameRoundTrip.semScalar_storeField` gives the array one
`storeField` leaves at `out`, as a fourfold `memSetDyn` of the recombined words.
Two things are added here. A frame clause for the block, so the three
`storeField`s chain: each must leave the following field element's half-limb
slots and the index slots alone. And the value reading of the `memSetDyn` fold
against `limbs4`, which needs the half-limbs below `2 ^ 32` — the bound
`Secp256k1FeAddSubBrick.BrickScope.limbs` carries.

## Main results

* `memSetDyn_at` — a `memSetDyn` at an in-range index, read at a cell.
* `foldl_memSetDyn_hit`, `foldl_memSetDyn_miss` — the four-cell write window of
  one `storeField`: inside the window a cell is the word written there, outside
  it is the incoming cell.
* `cellWord_toNat` — the recombined word `A + (B <<< 32)` has value
  `A + 2 ^ 32 · B` when both halves are below `2 ^ 32`.
* `feVal_of_reads`, `limbs4_of_halves` — the half-limb readout as an explicit
  eight-term weighted sum, and its four base-`2 ^ 64` limbs as the four
  half-limb pairs.
* `feVal_congr` — `feVal` depends only on the eight half-limb slot readings.
* `pointCells_getD` — the twelve cells of a point frame, by index.
* `arrStore_frame`, `recombineStore_frame`, `storeField_frame` — an `RArrStore`,
  and a whole `storeField` block, change only the array name `out` and the
  block's own recombination slots.
* `storeField_cells` — one `storeField 96 o fe`: `out` ends holding an array
  whose cells `o … o+3` are the four little-endian `u64` limbs of
  `feVal env fe`, and whose other cells are unchanged.
* `pointOpEpilogue_cells` — the three-`storeField` epilogue: `out` ends holding
  the 12-cell frame
  `pointCells (feVal env "Xp", feVal env "Yp", feVal env "Zp")`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpEpilogue

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
  (semScalar_setExpr_eq semList semList_cons_eq)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (storeField limbs4 pointCells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote (feVal)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered (HeadOk)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (BrickScope feHN feHN_eq ofNat_toNat accN_congr hd hdAppend neOfHd hd_feHN
   headOk_of_hd semScalar_seqAll_eq_semList feVal_eq_accN)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (upd_ne semScalar_storeField toNat_ofNat_32)

/-! ## 1. Reading a `memSetDyn` window -/

/-- A `memSetDyn` at an index below the memref length, read at a cell. -/
theorem memSetDyn_at {n : Nat} (a : Fin n → BitVec 64) (k : Nat) (v : BitVec 64)
    (hk : k < n) (m : Fin n) :
    memSetDyn a k v m = if m.val = k then v else a m := by
  match n, a with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (p + 1), a =>
      simp only [memSetDyn, Nat.mod_eq_of_lt hk]
      by_cases h : m.val = k
      · rw [if_pos (Fin.ext h), if_pos h]
      · rw [if_neg (fun hc => h (by rw [hc])), if_neg h]

/-- The four-cell write window of one `storeField`, at a written cell. -/
theorem foldl_memSetDyn_hit (b : Fin 12 → BitVec 64) (o : Nat) (V : Nat → BitVec 64)
    (ho : o + 4 ≤ 12) (j : Nat) (hj : j < 4) (m : Fin 12) (hm : m.val = o + j) :
    ((List.range 4).foldl
        (fun arr i => memSetDyn arr (BitVec.ofNat 64 (o + i)).toNat (V i)) b) m = V j := by
  have e0 : (BitVec.ofNat 64 (o + 0)).toNat = o + 0 := ofNat_toNat (by omega)
  have e1 : (BitVec.ofNat 64 (o + 1)).toNat = o + 1 := ofNat_toNat (by omega)
  have e2 : (BitVec.ofNat 64 (o + 2)).toNat = o + 2 := ofNat_toNat (by omega)
  have e3 : (BitVec.ofNat 64 (o + 3)).toNat = o + 3 := ofNat_toNat (by omega)
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e1, e2, e3]
  rw [memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega),
    memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega)]
  interval_cases j <;> split_ifs <;> first | rfl | omega

/-- The four-cell write window of one `storeField`, at a cell outside it. -/
theorem foldl_memSetDyn_miss (b : Fin 12 → BitVec 64) (o : Nat) (V : Nat → BitVec 64)
    (ho : o + 4 ≤ 12) (m : Fin 12) (hm : m.val < o ∨ o + 4 ≤ m.val) :
    ((List.range 4).foldl
        (fun arr i => memSetDyn arr (BitVec.ofNat 64 (o + i)).toNat (V i)) b) m = b m := by
  have e0 : (BitVec.ofNat 64 (o + 0)).toNat = o + 0 := ofNat_toNat (by omega)
  have e1 : (BitVec.ofNat 64 (o + 1)).toNat = o + 1 := ofNat_toNat (by omega)
  have e2 : (BitVec.ofNat 64 (o + 2)).toNat = o + 2 := ofNat_toNat (by omega)
  have e3 : (BitVec.ofNat 64 (o + 3)).toNat = o + 3 := ofNat_toNat (by omega)
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e1, e2, e3]
  rw [memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega),
    memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega)]
  split_ifs <;> first | rfl | omega

/-! ## 2. The recombined word and the base-`2 ^ 64` limbs -/

/-- The value of the word recombined from two 32-bit halves. -/
theorem cellWord_toNat {A B : BitVec 64} (hA : A.toNat < 2 ^ 32) (hB : B.toNat < 2 ^ 32) :
    (A + B <<< (BitVec.ofNat 64 32).toNat).toNat = A.toNat + 2 ^ 32 * B.toNat := by
  rw [toNat_ofNat_32, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The half-limb residue readout as an explicit eight-term weighted sum. -/
theorem feVal_of_reads (env : SEnvScalar) (fe : String) (a : Nat → Nat)
    (h : ∀ k, k < 8 → (envReader env (feHN fe k)).toNat = a k) :
    feVal env fe = a 0 + 2 ^ 32 * a 1 + 2 ^ 64 * a 2 + 2 ^ 96 * a 3 + 2 ^ 128 * a 4
      + 2 ^ 160 * a 5 + 2 ^ 192 * a 6 + 2 ^ 224 * a 7 := by
  simp only [feVal, feHN_eq, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)]
  ring

/-- The four base-`2 ^ 64` limbs of a sum of eight 32-bit half-limbs are the four
    half-limb pairs. -/
theorem limbs4_of_halves (a0 a1 a2 a3 a4 a5 a6 a7 : Nat)
    (h0 : a0 < 2 ^ 32) (h1 : a1 < 2 ^ 32) (h2 : a2 < 2 ^ 32) (h3 : a3 < 2 ^ 32)
    (h4 : a4 < 2 ^ 32) (h5 : a5 < 2 ^ 32) (h6 : a6 < 2 ^ 32) (h7 : a7 < 2 ^ 32) :
    limbs4 (a0 + 2 ^ 32 * a1 + 2 ^ 64 * a2 + 2 ^ 96 * a3 + 2 ^ 128 * a4
        + 2 ^ 160 * a5 + 2 ^ 192 * a6 + 2 ^ 224 * a7)
      = [a0 + 2 ^ 32 * a1, a2 + 2 ^ 32 * a3, a4 + 2 ^ 32 * a5, a6 + 2 ^ 32 * a7] := by
  simp only [limbs4, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- `feVal` depends only on the eight half-limb slot readings. -/
theorem feVal_congr {env e : SEnvScalar} {fe : String}
    (h : ∀ k, k < 8 → envReader e (feHN fe k) = envReader env (feHN fe k)) :
    feVal e fe = feVal env fe := by
  rw [feVal_eq_accN, feVal_eq_accN]
  exact accN_congr 8 (fun k hk => by rw [h k hk])

/-- The twelve cells of a point frame, by index: cells `0..3` are the limbs of
    the first coordinate, `4..7` of the second, `8..11` of the third. -/
theorem pointCells_getD (X Y Z : Nat) (i : Nat) (hi : i < 12) :
    (pointCells (X, Y, Z)).getD i 0
      = if i < 4 then (limbs4 X).getD i 0
        else if i < 8 then (limbs4 Y).getD (i - 4) 0 else (limbs4 Z).getD (i - 8) 0 := by
  interval_cases i <;> simp [pointCells, limbs4]

/-! ## 3. What one `storeField` block leaves alone -/

/-- An `RArrStore` rebinds only the array name. -/
theorem arrStore_frame {arr : Located} {idxN : String} {src : Located}
    {env env' : SEnvScalar}
    (h : semScalar (.RArrStore arr idxN src) env = some env') :
    ∀ s, s ≠ arr.locVar → env' s = env s := by
  intro s hs
  have hex : ∃ (t : CryptoTy) (v : ⟦t⟧), env' = env.upd arr.locVar v := by
    simp only [semScalar] at h
    split at h <;> (try split at h) <;> exact ⟨_, _, (Option.some.inj h).symm⟩
  obtain ⟨t, v, rfl⟩ := hex
  exact upd_ne hs

/-- The recombine-and-store block over an arbitrary index list changes only
    `out` and its own recombination slots. -/
theorem recombineStore_frame (fw o : Nat) (fe : String) :
    ∀ (js : List Nat) (env env' : SEnvScalar),
      semScalar (seqAll (js.flatMap (fun j =>
          [(LowCT.RScalarSetExpr s!"{fe}o{j}"
              (.SAdd (sv s!"{fe}h{2 * j}") (.SShl (sv s!"{fe}h{2 * j + 1}") (.SLit 32)))),
           (LowCT.RArrStore ⟨"out", .TBytes fw⟩ s!"ix{o + j}" ⟨s!"{fe}o{j}", .TU64⟩)])))
          env = some env' →
      ∀ s, ¬ isTmpName s → s ≠ "out" → (∀ j : Nat, s ≠ s!"{fe}o{j}") → env' s = env s := by
  intro js
  induction js with
  | nil =>
      intro env env' h s _ _ _
      simp only [List.flatMap_nil] at h
      obtain rfl : env' = env := (Option.some.inj h).symm
      rfl
  | cons j js ih =>
      intro env env' h s hsT hso hoj
      rw [semScalar_seqAll_eq_semList] at h
      simp only [List.flatMap_cons, List.cons_append, List.nil_append] at h
      obtain ⟨e1, h1, hrest⟩ := semList_cons_eq h
      obtain ⟨e2, h2, h3⟩ := semList_cons_eq hrest
      rw [← semScalar_seqAll_eq_semList] at h3
      rw [ih e2 env' h3 s hsT hso hoj, arrStore_frame h2 s hso,
        (semScalar_setExpr_eq h1).2 s hsT (hoj j)]

/-- **One `storeField` block changes only `out` and its own recombination
    slots.** The frame clause that lets three `storeField`s chain: the next
    block's half-limb and index slots survive this one. -/
theorem storeField_frame {fw o : Nat} {fe : String} {env env' : SEnvScalar}
    (h : semScalar (seqAll (storeField fw o fe)) env = some env') :
    ∀ s, ¬ isTmpName s → s ≠ "out" → (∀ j : Nat, s ≠ s!"{fe}o{j}") → env' s = env s :=
  recombineStore_frame fw o fe (List.range 4) env env' h

/-! ## 4. One `storeField`, as four frame cells -/

/-- **One `storeField 96 o fe`, as a value statement on the output frame.** From
    an environment whose eight `fe` half-limb slots are bound below `2 ^ 32` and
    whose index slots `ix{o} … ix{o+3}` carry their own numbers, the name `out`
    ends holding an array whose cells `o … o+3` are the four little-endian `u64`
    limbs of `feVal env fe`, whose remaining cells are the incoming ones; and the
    block leaves every other non-temporary name outside `fe`'s recombination
    slots alone. -/
theorem storeField_cells {o : Nat} {fe : String} {cf : Char} {rf : List Char}
    {b : Fin 12 → BitVec 64} {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i') (hco : cf ≠ 'o')
    (ho : o + 4 ≤ 12)
    (hb : env "out" = some ⟨.memref 12, b⟩)
    (hix : ∀ j, j < 4 → env s!"ix{o + j}" = some ⟨.sword 64, BitVec.ofNat 64 (o + j)⟩)
    (hbnd : ∀ k, k < 8 → env (feHN fe k) = some ⟨.sword 64, envReader env (feHN fe k)⟩)
    (hlt : ∀ k, k < 8 → (envReader env (feHN fe k)).toNat < 2 ^ 32) :
    ∃ (env' : SEnvScalar) (fr : Fin 12 → BitVec 64),
      semScalar (seqAll (storeField 96 o fe)) env = some env'
        ∧ env' "out" = some ⟨.memref 12, fr⟩
        ∧ (∀ (j : Nat), j < 4 → ∀ (m : Fin 12), m.val = o + j →
            (fr m).toNat = (limbs4 (feVal env fe)).getD j 0)
        ∧ (∀ (m : Fin 12), m.val < o ∨ o + 4 ≤ m.val → fr m = b m)
        ∧ (∀ s, ¬ isTmpName s → s ≠ "out" → (∀ i : Nat, s ≠ s!"{fe}o{i}") →
            env' s = env s) := by
  obtain ⟨env', hs, hfin⟩ :=
    semScalar_storeField (fw := 96) (o := o) (b := b)
      (iw := fun j => BitVec.ofNat 64 (o + j))
      (A := fun j => envReader env (feHN fe (2 * j)))
      (B := fun j => envReader env (feHN fe (2 * j + 1)))
      hfe hcf hci hco hb hix
      (fun j hj => hbnd (2 * j) (by omega)) (fun j hj => hbnd (2 * j + 1) (by omega))
  refine ⟨env',
    (List.range 4).foldl (fun arr i => memSetDyn arr (BitVec.ofNat 64 (o + i)).toNat
      (envReader env (feHN fe (2 * i))
        + envReader env (feHN fe (2 * i + 1)) <<< (BitVec.ofNat 64 32).toNat)) b,
    hs, hfin, ?_, ?_, storeField_frame hs⟩
  · intro j hj m hm
    rw [foldl_memSetDyn_hit b o
        (fun i => envReader env (feHN fe (2 * i))
          + envReader env (feHN fe (2 * i + 1)) <<< (BitVec.ofNat 64 32).toNat) ho j hj m hm,
      cellWord_toNat (hlt (2 * j) (by omega)) (hlt (2 * j + 1) (by omega)),
      feVal_of_reads env fe (fun k => (envReader env (feHN fe k)).toNat) (fun _ _ => rfl),
      limbs4_of_halves _ _ _ _ _ _ _ _
        (hlt 0 (by norm_num)) (hlt 1 (by norm_num)) (hlt 2 (by norm_num))
        (hlt 3 (by norm_num)) (hlt 4 (by norm_num)) (hlt 5 (by norm_num))
        (hlt 6 (by norm_num)) (hlt 7 (by norm_num))]
    interval_cases j <;> norm_num
  · intro m hm
    exact foldl_memSetDyn_miss b o _ ho m hm

/-! ## 5. The three-`storeField` epilogue -/

/-- The head character of a field element's `j`-th recombination slot. -/
theorem hd_feO {fe : String} {c : Char} (h : hd fe = some c) (j : Nat) :
    hd s!"{fe}o{j}" = some c := hdAppend (hdAppend h)

/-- The head character of an index slot. -/
theorem hd_ix (i : Nat) : hd s!"ix{i}" = some 'i' := hdAppend rfl

/-- The head character of the output pointer name. -/
theorem hd_out : hd "out" = some 'o' := rfl

/-- **The point-op epilogue's output frame.** Running the three `storeField`
    blocks that close `Secp256k1PointOpFront.jacDblBody` and `jacAddBody`, from
    an environment in the brick scope whose `Xp`/`Yp`/`Zp` half-limb slots are
    bound at 64-bit word type and whose twelve index slots carry their own
    numbers, the name `out` ends holding the 12-cell frame
    `pointCells (feVal env "Xp", feVal env "Yp", feVal env "Zp")` — cells `0..3`
    the limbs of `Xp`, cells `4..7` those of `Yp`, cells `8..11` those of
    `Zp`. -/
theorem pointOpEpilogue_cells {b : Fin 12 → BitVec 64} {env : SEnvScalar}
    (hsc : BrickScope env)
    (hb : env "out" = some ⟨.memref 12, b⟩)
    (hix : ∀ i, i < 12 → env s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩)
    (hbX : ∀ k, k < 8 → env (feHN "Xp" k) = some ⟨.sword 64, envReader env (feHN "Xp" k)⟩)
    (hbY : ∀ k, k < 8 → env (feHN "Yp" k) = some ⟨.sword 64, envReader env (feHN "Yp" k)⟩)
    (hbZ : ∀ k, k < 8 → env (feHN "Zp" k) = some ⟨.sword 64, envReader env (feHN "Zp" k)⟩) :
    ∃ (env' : SEnvScalar) (fr : Fin 12 → BitVec 64),
      semScalar (seqAll (storeField 96 0 "Xp" ++ storeField 96 4 "Yp"
          ++ storeField 96 8 "Zp")) env = some env'
        ∧ env' "out" = some ⟨.memref 12, fr⟩
        ∧ ∀ (m : Fin 12), (fr m).toNat
            = (pointCells (feVal env "Xp", feVal env "Yp", feVal env "Zp")).getD m.val 0 := by
  have hltX : ∀ k, k < 8 → (envReader env (feHN "Xp" k)).toNat < 2 ^ 32 :=
    fun k hk => hsc.limbs "Xp" (by decide) k hk
  have hltY : ∀ k, k < 8 → (envReader env (feHN "Yp" k)).toNat < 2 ^ 32 :=
    fun k hk => hsc.limbs "Yp" (by decide) k hk
  have hltZ : ∀ k, k < 8 → (envReader env (feHN "Zp" k)).toNat < 2 ^ 32 :=
    fun k hk => hsc.limbs "Zp" (by decide) k hk
  -- block 1: cells 0..3 from `Xp`
  obtain ⟨e1, fr1, hs1, hb1, hit1, hmiss1, hfr1⟩ :=
    storeField_cells (o := 0) (fe := "Xp") (b := b) rfl (by decide) (by decide) (by decide)
      (by norm_num) hb (fun j hj => hix (0 + j) (by omega)) hbX hltX
  have hkeep1 : ∀ (s : String) (c : Char), hd s = some c → c ≠ '_' → c ≠ 'o' → c ≠ 'X' →
      e1 s = env s :=
    fun s c hhd hc hco hcX =>
      hfr1 s (HeadOk.notTmp (headOk_of_hd hhd hc)) (neOfHd hhd hd_out hco)
        (fun i => neOfHd hhd (hd_feO (fe := "Xp") (c := 'X') rfl i) hcX)
  have hix1 : ∀ j, j < 4 → e1 s!"ix{4 + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 + j)⟩ := by
    intro j hj
    rw [hkeep1 _ 'i' (hd_ix (4 + j)) (by decide) (by decide) (by decide)]
    exact hix (4 + j) (by omega)
  have hkeepY : ∀ k, k < 8 → e1 (feHN "Yp" k) = env (feHN "Yp" k) :=
    fun k _ => hkeep1 _ 'Y' (hd_feHN rfl k) (by decide) (by decide) (by decide)
  have hkeepZ1 : ∀ k, k < 8 → e1 (feHN "Zp" k) = env (feHN "Zp" k) :=
    fun k _ => hkeep1 _ 'Z' (hd_feHN rfl k) (by decide) (by decide) (by decide)
  have hrY1 : ∀ k, k < 8 → envReader e1 (feHN "Yp" k) = envReader env (feHN "Yp" k) :=
    fun k hk => by simp only [envReader, hkeepY k hk]
  have hrZ1 : ∀ k, k < 8 → envReader e1 (feHN "Zp" k) = envReader env (feHN "Zp" k) :=
    fun k hk => by simp only [envReader, hkeepZ1 k hk]
  -- block 2: cells 4..7 from `Yp`
  obtain ⟨e2, fr2, hs2, hb2, hit2, hmiss2, hfr2⟩ :=
    storeField_cells (o := 4) (fe := "Yp") (b := fr1) rfl (by decide) (by decide) (by decide)
      (by norm_num) hb1 hix1
      (fun k hk => by rw [hkeepY k hk, hrY1 k hk]; exact hbY k hk)
      (fun k hk => by rw [hrY1 k hk]; exact hltY k hk)
  have hkeep2 : ∀ (s : String) (c : Char), hd s = some c → c ≠ '_' → c ≠ 'o' → c ≠ 'Y' →
      e2 s = e1 s :=
    fun s c hhd hc hco hcY =>
      hfr2 s (HeadOk.notTmp (headOk_of_hd hhd hc)) (neOfHd hhd hd_out hco)
        (fun i => neOfHd hhd (hd_feO (fe := "Yp") (c := 'Y') rfl i) hcY)
  have hix2 : ∀ j, j < 4 → e2 s!"ix{8 + j}" = some ⟨.sword 64, BitVec.ofNat 64 (8 + j)⟩ := by
    intro j hj
    rw [hkeep2 _ 'i' (hd_ix (8 + j)) (by decide) (by decide) (by decide),
      hkeep1 _ 'i' (hd_ix (8 + j)) (by decide) (by decide) (by decide)]
    exact hix (8 + j) (by omega)
  have hkeepZ2 : ∀ k, k < 8 → e2 (feHN "Zp" k) = env (feHN "Zp" k) := by
    intro k hk
    rw [hkeep2 _ 'Z' (hd_feHN rfl k) (by decide) (by decide) (by decide)]
    exact hkeepZ1 k hk
  have hrZ2 : ∀ k, k < 8 → envReader e2 (feHN "Zp" k) = envReader env (feHN "Zp" k) :=
    fun k hk => by simp only [envReader, hkeepZ2 k hk]
  -- block 3: cells 8..11 from `Zp`
  obtain ⟨e3, fr3, hs3, hb3, hit3, hmiss3, _⟩ :=
    storeField_cells (o := 8) (fe := "Zp") (b := fr2) rfl (by decide) (by decide) (by decide)
      (by norm_num) hb2 hix2
      (fun k hk => by rw [hkeepZ2 k hk, hrZ2 k hk]; exact hbZ k hk)
      (fun k hk => by rw [hrZ2 k hk]; exact hltZ k hk)
  have hvY : feVal e1 "Yp" = feVal env "Yp" := feVal_congr hrY1
  have hvZ : feVal e2 "Zp" = feVal env "Zp" := feVal_congr hrZ2
  refine ⟨e3, fr3, ?_, hb3, ?_⟩
  · rw [Secp256k1PointOpFrontDenote.semScalar_seqAll_append,
      Secp256k1PointOpFrontDenote.semScalar_seqAll_append, hs1, Option.bind_some, hs2,
      Option.bind_some]
    exact hs3
  · intro m
    have hm12 : m.val < 12 := m.isLt
    rcases Nat.lt_or_ge m.val 4 with h4 | h4
    · rw [hmiss3 m (Or.inl (by omega)), hmiss2 m (Or.inl (by omega)),
        hit1 m.val h4 m (by omega), pointCells_getD _ _ _ m.val hm12, if_pos h4]
    · rcases Nat.lt_or_ge m.val 8 with h8 | h8
      · rw [hmiss3 m (Or.inl (by omega)),
          hit2 (m.val - 4) (by omega) m (by omega), hvY,
          pointCells_getD _ _ _ m.val hm12, if_neg (by omega), if_pos h8]
      · rw [hit3 (m.val - 8) (by omega) m (by omega), hvZ,
          pointCells_getD _ _ _ m.val hm12, if_neg (by omega), if_neg (by omega)]

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpEpilogue
