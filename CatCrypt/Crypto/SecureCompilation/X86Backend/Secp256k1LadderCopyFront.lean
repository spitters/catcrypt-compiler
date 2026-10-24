/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# A FRONT-SOURCED register-window slot copy for the threaded secp256k1 ladder step

The threaded ladder step `Secp256k1LadderStepThreaded.ladderStepThreaded` keeps the
accumulator in frame slots `0,1,2` by inserting register-window copy-backs
(`copyDblBack`, `copyResBack`) between the emitted point-op blocks.  Those
copy-backs are hand-written `loadSlot4`/`storeSlot4` `JInstr` pairs.

This module expresses the same slot copy through the verified front: a `LowCT`
program of four `RArrLoad`s (the four `u64` words of the source slot) followed by
four `RArrStore`s (into the destination slot) over a single memref frame `F`, run
through the direct control front to a `Com catCryptDialect`.  The front's own
`Com` denotation is proved to move the destination slot's four cells to the source
slot's, leaving every other cell unchanged — the front-world analogue of
`Secp256k1LadderStepThreaded.copySlot_slotLimbs_dst` /
`copySlot_slotLimbs_other`, established over the front's denotation rather than a
hand-authored `JInstr` block.

The copy body binds its own cell-index scalars, so it runs from the frame-only
entry environment the direct control front descends against; the slot indices are
supplied as literal `RScalarSetExpr`s.  Slot `s` occupies cells `4·s .. 4·s+3` of
the frame, the same tiling `Secp256k1PointOpFrontFramed` uses.

## Main results

* `copySlotLowCT` — the slot-copy front program over frame `F`.
* `copySlotLowCT_coveredSCtl` — the body lies in the direct control front's
  covered scalar fragment, so `translateDialectControl_denote_ctl` applies.
* `copySlotLowCT_sem` — the body's `semScalar` waist runs from a frame-bound entry
  environment, leaving `F` holding the source slot copied into the destination
  slot.
* `copySlotFront_denote` — the front-compiled `Com`'s denotation is that copied
  frame.
* `copySlotFront_denote_get_dst`, `copySlotFront_denote_get_other` — the
  destination slot reads the source slot's cells and every other cell is preserved.
* `copySlotFront_jasmin_denote` — the same one dialect down, at the
  `Com jasminDialect` the owned backend consumes.

## What remains

`copySlotLowCT_sem` and the readouts are over the direct control front's
`SEnvScalar` / `Com.denote` model.  Substituting the front-compiled copy for
`copyDblBack` / `copyResBack` inside `ladderStepThreaded_realizes` needs a bridge
between that model and the committed `JState` / `runBlock` / `slotFieldVal` model
the threaded step is stated over; that bridge is not part of this file.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Secp256k1LadderCopyFront

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
  (cryptoDialectToJasminCom_denote_eq' ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy_memref)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (semScalar SEnvScalar isTmpName envReader semLowerSExpr ConsistentS IsCoveredS IsCoveredSCtl
   translateDialectControl_denote_ctl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (slot_inj seqAll_step semScalar_setExpr_run semScalar_arrLoadList semScalar_arrStore
   head_ne ix_toList upd_ne)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (semScalar_seqAll_cons semScalar_seqAll_append)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk isCoveredS_seqAll cmdsClean_append cmdsClean_cons cmdsClean_nil cmdsClean_map_range')

/-! ## 1. Name hygiene -/

theorem cp_toList (j : Nat) : (s!"cp{j}").toList = 'c' :: 'p' :: (toString j).toList := by
  rw [String.toList_append]; rfl

theorem cpInj : Function.Injective (fun j : Nat => s!"cp{j}") :=
  fun _ _ h => slot_inj (p := "") (u := "cp") h

theorem F_toList : ("F" : String).toList = 'F' :: [] := rfl

theorem F_ne_cp (j : Nat) : ("F" : String) ≠ s!"cp{j}" := head_ne F_toList (cp_toList j) (by decide)
theorem cp_ne_F (j : Nat) : s!"cp{j}" ≠ ("F" : String) := (F_ne_cp j).symm
theorem ix_ne_cp (c j : Nat) : s!"ix{c}" ≠ s!"cp{j}" := head_ne (ix_toList c) (cp_toList j) (by decide)
theorem ix_ne_F (c : Nat) : s!"ix{c}" ≠ ("F" : String) := head_ne (ix_toList c) F_toList (by decide)
theorem F_ne_ix (c : Nat) : ("F" : String) ≠ s!"ix{c}" := (ix_ne_F c).symm

theorem ixEq {a b : Nat} (h : s!"ix{a}" = s!"ix{b}") : a = b := slot_inj (p := "") (u := "ix") h

theorem ixNt (i : Nat) : ¬ isTmpName s!"ix{i}" :=
  HeadOk.notTmp (HeadOk.append (⟨'i', ['x'], rfl, by decide⟩ : HeadOk "ix") (toString i))

theorem notTmp_F : ¬ isTmpName ("F" : String) :=
  HeadOk.notTmp (⟨'F', [], rfl, by decide⟩ : HeadOk "F")

theorem hlowLit (env : SEnvScalar) (i : Nat) : (semLowerSExpr env 0 (SExpr.SLit i)).isSome := by
  simp only [semLowerSExpr, Option.isSome_some]

theorem ofNatToNat {c : Nat} (h : c < 2 ^ 64) : (BitVec.ofNat 64 c).toNat = c := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## 2. The slot-copy front program -/

/-- Bind the cell-index scalars `ix{base}..ix{base+3}` to their literal values. -/
def copyIdx (base : Nat) : List LowCT :=
  (List.range 4).map (fun j => (.RScalarSetExpr s!"ix{base+j}" (.SLit (base+j)) : LowCT))

/-- Load the four `u64` words of slot `src` (frame cells `4·src .. 4·src+3`) into
    the register window `cp0..cp3`. -/
def copyLoads (fw src : Nat) : List LowCT :=
  (List.range 4).map (fun j =>
    (.RArrLoad ⟨s!"cp{j}", .TU64⟩ ⟨"F", .TBytes fw⟩ s!"ix{4*src+j}" : LowCT))

/-- Store the register window `cp0..cp3` into the four words of slot `dst`. -/
def copyStores (fw dst : Nat) : List LowCT :=
  (List.range 4).map (fun j =>
    (.RArrStore ⟨"F", .TBytes fw⟩ s!"ix{4*dst+j}" ⟨s!"cp{j}", .TU64⟩ : LowCT))

/-- The slot-copy front program over frame `F` (`fw` bytes wide): bind the eight
    touched cell indices, load slot `src`, store into slot `dst`. -/
def copySlotLowCT (fw src dst : Nat) : LowCT :=
  seqAll (copyIdx (4*src) ++ copyIdx (4*dst) ++ copyLoads fw src ++ copyStores fw dst)

/-- Single-frame context: one memref of `(fw+7)/8` cells. -/
def inΓF (fw : Nat) : Ctx := [.memref ((fw+7)/8)]

/-- Single-frame `VarMap`: the sole memref bound as `F`. -/
def inVMF (fw : Nat) : VarMap (inΓF fw) := VarMap.empty.bind (t := .memref ((fw+7)/8)) "F"

/-- **The slot-copy body lies in the direct control front's covered scalar
    fragment.** Its index binds are literal `RScalarSetExpr`s and its loads and
    stores are dynamic-index `RArrLoad` / `RArrStore` arms, so
    `translateDialectControl_denote_ctl` applies. -/
theorem copySlotLowCT_coveredSCtl (fw src dst : Nat)
    (hsrc : 4*src+3 < (fw+7)/8) (hdst : 4*dst+3 < (fw+7)/8) (hb : (fw+7)/8 ≤ 2 ^ 64) :
    IsCoveredSCtl (copySlotLowCT fw src dst) := by
  refine .ofStraight (isCoveredS_seqAll _ ?_)
  simp only [copyIdx, copyLoads, copyStores]
  exact cmdsClean_append (cmdsClean_append (cmdsClean_append
    (cmdsClean_map_range' 4 _ (fun j hj => .rScalarSetExpr _ _ (show (4*src+j) < 2 ^ 64 by omega)))
    (cmdsClean_map_range' 4 _ (fun j hj => .rScalarSetExpr _ _ (show (4*dst+j) < 2 ^ 64 by omega))))
    (cmdsClean_map_range' 4 _ (fun _ _ => .rArrLoad _ _ _)))
    (cmdsClean_map_range' 4 _ (fun _ _ => .rArrStore _ _ _))

/-! ## 3. Termination-and-value of the index block -/

theorem ixNe {base j k : Nat} (h : j ≠ k) : s!"ix{base+j}" ≠ s!"ix{base+k}" :=
  fun hc => h (Nat.add_left_cancel (ixEq hc))

/-- **The index block binds each `ix{base+j}` to its literal.** -/
theorem copyIdx_sem (base : Nat) (env : SEnvScalar) :
    ∃ env', semScalar (seqAll (copyIdx base)) env = some env'
      ∧ (∀ j, j < 4 → env' s!"ix{base+j}" = some ⟨.sword 64, BitVec.ofNat 64 (base+j)⟩)
      ∧ (∀ s, ¬ isTmpName s → (∀ j, j < 4 → s ≠ s!"ix{base+j}") → env' s = env s) := by
  simp only [copyIdx, show List.range 4 = [0,1,2,3] from rfl, List.map_cons, List.map_nil]
  obtain ⟨e0, hs0, hv0, hf0⟩ := semScalar_setExpr_run (y := s!"ix{base+0}") (hlowLit env (base+0))
  obtain ⟨e1, hs1, hv1, hf1⟩ := semScalar_setExpr_run (y := s!"ix{base+1}") (hlowLit e0 (base+1))
  obtain ⟨e2, hs2, hv2, hf2⟩ := semScalar_setExpr_run (y := s!"ix{base+2}") (hlowLit e1 (base+2))
  obtain ⟨e3, hs3, hv3, hf3⟩ := semScalar_setExpr_run (y := s!"ix{base+3}") (hlowLit e2 (base+3))
  refine ⟨e3, ?_, ?_, ?_⟩
  · rw [seqAll_step hs0, seqAll_step hs1, seqAll_step hs2]
    show semScalar (seqAll [_]) e2 = some e3
    rw [show seqAll [(LowCT.RScalarSetExpr s!"ix{base+3}" (.SLit (base+3)))]
          = LowCT.RScalarSetExpr s!"ix{base+3}" (.SLit (base+3)) from rfl, hs3]
  · intro j hj
    interval_cases j
    · rw [hf3 _ (ixNt _) (ixNe (by decide)), hf2 _ (ixNt _) (ixNe (by decide)),
        hf1 _ (ixNt _) (ixNe (by decide)), hv0]; simp only [SExpr.evalBV]
    · rw [hf3 _ (ixNt _) (ixNe (by decide)), hf2 _ (ixNt _) (ixNe (by decide)), hv1]
      simp only [SExpr.evalBV]
    · rw [hf3 _ (ixNt _) (ixNe (by decide)), hv2]; simp only [SExpr.evalBV]
    · rw [hv3]; simp only [SExpr.evalBV]
  · intro s hnt hs
    rw [hf3 s hnt (hs 3 (by decide)), hf2 s hnt (hs 2 (by decide)),
      hf1 s hnt (hs 1 (by decide)), hf0 s hnt (hs 0 (by decide))]

/-! ## 4. A `List.map`-indexed family of frame stores -/

/-- **A block of frame stores runs**, each writing its source word into the frame
    at its index word, folding the frame from left to right. -/
theorem semScalar_arrStoreList {fw : Nat} {arrN : String} {sN gN : Nat → String}
    {iw vw : Nat → BitVec 64}
    (hsA : ∀ j, sN j ≠ arrN) (hgA : ∀ j, gN j ≠ arrN) :
    ∀ (js : List Nat) (a : Fin ((fw+7)/8) → BitVec 64) (env : SEnvScalar),
      env arrN = some ⟨.memref ((fw+7)/8), a⟩ →
      (∀ j ∈ js, env (gN j) = some ⟨.sword 64, iw j⟩) →
      (∀ j ∈ js, env (sN j) = some ⟨.sword 64, vw j⟩) →
      ∃ env', semScalar (seqAll (js.map (fun j =>
            LowCT.RArrStore ⟨arrN, .TBytes fw⟩ (gN j) ⟨sN j, .TU64⟩))) env = some env'
        ∧ env' arrN = some ⟨.memref ((fw+7)/8),
              js.foldl (fun arr j => memSetDyn arr (iw j).toNat (vw j)) a⟩
        ∧ (∀ s, s ≠ arrN → env' s = env s) := by
  intro js
  induction js with
  | nil => intro a env ha _ _; exact ⟨env, rfl, ha, fun s _ => rfl⟩
  | cons j js ih =>
      intro a env ha hg hv
      obtain ⟨e1, hs1, ha1, hf1⟩ :=
        semScalar_arrStore (fw := fw) ha (hg j (.head _)) (hv j (.head _))
      have hg1 : ∀ j' ∈ js, e1 (gN j') = some ⟨.sword 64, iw j'⟩ :=
        fun j' hj' => by rw [hf1 _ (hgA j')]; exact hg j' (.tail _ hj')
      have hv1 : ∀ j' ∈ js, e1 (sN j') = some ⟨.sword 64, vw j'⟩ :=
        fun j' hj' => by rw [hf1 _ (hsA j')]; exact hv j' (.tail _ hj')
      obtain ⟨env', hsem, hfin, hfr⟩ := ih _ e1 ha1 hg1 hv1
      refine ⟨env', ?_, ?_, ?_⟩
      · rw [List.map_cons, seqAll_step hs1]; exact hsem
      · rw [List.foldl_cons]; exact hfin
      · intro s hs; rw [hfr s hs, hf1 s hs]

/-! ## 5. The waist semantics of the whole copy -/

/-- **The slot-copy body runs from a frame-bound entry environment.** Its exit
    environment holds at `F` the input frame with the four cells of slot `dst`
    overwritten by the four cells of slot `src`. -/
theorem copySlotLowCT_sem (fw src dst : Nat)
    (hsrc : 4*src+3 < (fw+7)/8) (hsd : src ≠ dst)
    (hb : (fw+7)/8 ≤ 2 ^ 64)
    (a : Fin ((fw+7)/8) → BitVec 64) (env : SEnvScalar)
    (hF : env "F" = some ⟨.memref ((fw+7)/8), a⟩) :
    ∃ envF, semScalar (copySlotLowCT fw src dst) env = some envF
      ∧ envF "F" = some ⟨.memref ((fw+7)/8),
          (List.range 4).foldl
            (fun arr j => memSetDyn arr (BitVec.ofNat 64 (4*dst+j)).toNat
              (memGetDyn a (4*src+j))) a⟩ := by
  have hcell_src : ∀ j, j < 4 → 4*src+j < 2 ^ 64 := fun j hj => by omega
  -- index blocks
  obtain ⟨ea, hsa, hva, hfa⟩ := copyIdx_sem (4*src) env
  obtain ⟨eb, hsb, hvb, hfb⟩ := copyIdx_sem (4*dst) ea
  -- F survives both index blocks
  have hFb : eb "F" = some ⟨.memref ((fw+7)/8), a⟩ := by
    rw [hfb "F" notTmp_F (fun k _ => F_ne_ix (4*dst+k)),
        hfa "F" notTmp_F (fun k _ => F_ne_ix (4*src+k))]; exact hF
  -- the src indices survive the dst index block
  have hgb : ∀ j ∈ List.range 4, eb s!"ix{4*src+j}"
      = some ⟨.sword 64, BitVec.ofNat 64 (4*src+j)⟩ := by
    intro j hj
    have hj4 : j < 4 := List.mem_range.mp hj
    rw [hfb s!"ix{4*src+j}" (ixNt _)
        (fun k hk => fun hc => (show 4*src+j ≠ 4*dst+k by omega) (ixEq hc))]
    exact hva j hj4
  -- loads
  obtain ⟨ec, hsc, hvc, hfc⟩ :=
    semScalar_arrLoadList (tw := .TBytes fw) (a := a)
      (iw := fun j => BitVec.ofNat 64 (4*src+j)) (f := fun j => s!"cp{j}")
      (g := fun j => s!"ix{4*src+j}") cpInj (fun j => F_ne_cp j)
      (fun j j' => ix_ne_cp (4*src+j) j') (List.range 4) List.nodup_range eb hFb hgb
  -- F survives the loads
  have hFc : ec "F" = some ⟨.memref ((fw+7)/8), a⟩ := by
    rw [hfc "F" (fun j _ => F_ne_cp j)]; exact hFb
  -- the dst indices survive the loads
  have hgc : ∀ j ∈ List.range 4, ec s!"ix{4*dst+j}"
      = some ⟨.sword 64, BitVec.ofNat 64 (4*dst+j)⟩ := by
    intro j hj
    have hj4 : j < 4 := List.mem_range.mp hj
    rw [hfc s!"ix{4*dst+j}" (fun k _ => ix_ne_cp (4*dst+j) k)]
    exact hvb j hj4
  -- the loaded words are the source slot's cells
  have hsrcv : ∀ j ∈ List.range 4, ec s!"cp{j}"
      = some ⟨.sword 64, memGetDyn a (4*src+j)⟩ := by
    intro j hj
    have hj4 : j < 4 := List.mem_range.mp hj
    rw [hvc j hj, ofNatToNat (hcell_src j hj4)]
  -- stores
  obtain ⟨envF, hsem, hfin, _⟩ :=
    semScalar_arrStoreList (fw := fw) (sN := fun j => s!"cp{j}")
      (gN := fun j => s!"ix{4*dst+j}") (iw := fun j => BitVec.ofNat 64 (4*dst+j))
      (vw := fun j => memGetDyn a (4*src+j)) (fun j => cp_ne_F j)
      (fun j => ix_ne_F (4*dst+j)) (List.range 4) a ec hFc hgc hsrcv
  refine ⟨envF, ?_, hfin⟩
  -- assemble the four blocks
  rw [copySlotLowCT, copyLoads, copyStores,
    show copyIdx (4*src) ++ copyIdx (4*dst) ++ (List.range 4).map (fun j =>
        (LowCT.RArrLoad ⟨s!"cp{j}", .TU64⟩ ⟨"F", .TBytes fw⟩ s!"ix{4*src+j}"))
      ++ (List.range 4).map (fun j =>
        (LowCT.RArrStore ⟨"F", .TBytes fw⟩ s!"ix{4*dst+j}" ⟨s!"cp{j}", .TU64⟩))
      = copyIdx (4*src) ++ (copyIdx (4*dst) ++ ((List.range 4).map (fun j =>
          (LowCT.RArrLoad ⟨s!"cp{j}", .TU64⟩ ⟨"F", .TBytes fw⟩ s!"ix{4*src+j}"))
        ++ (List.range 4).map (fun j =>
          (LowCT.RArrStore ⟨"F", .TBytes fw⟩ s!"ix{4*dst+j}" ⟨s!"cp{j}", .TU64⟩)))) by
      simp only [List.append_assoc]]
  rw [semScalar_seqAll_append, hsa, Option.bind_some, semScalar_seqAll_append, hsb,
    Option.bind_some, semScalar_seqAll_append, hsc, Option.bind_some]
  exact hsem

/-! ## 6. The written frame, cell by cell -/

theorem memSetDyn_at {n : Nat} (arr : Fin n → BitVec 64) (k : Nat) (v : BitVec 64)
    (hk : k < n) (m : Fin n) : memSetDyn arr k v m = if m.val = k then v else arr m := by
  match n, arr with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (p + 1), arr =>
      simp only [memSetDyn, Nat.mod_eq_of_lt hk]
      by_cases h : m.val = k
      · rw [ite_eq_left (Fin.ext h), ite_eq_left h]
      · rw [ite_eq_right (fun hc => h (by rw [hc])), ite_eq_right h]

theorem memGetDyn_lt {n : Nat} (arr : Fin n → BitVec 64) {k : Nat} (hk : k < n) :
    memGetDyn arr k = arr ⟨k, hk⟩ := by
  match n, arr with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (p + 1), arr => simp only [memGetDyn]; congr 1; exact Fin.ext (Nat.mod_eq_of_lt hk)

/-- The copied frame, read at a destination-slot cell. -/
theorem copyFold_hit {fw src dst : Nat} (hdst : 4*dst+3 < (fw+7)/8) (hb : (fw+7)/8 ≤ 2 ^ 64)
    (a : Fin ((fw+7)/8) → BitVec 64) (j : Nat) (hj : j < 4) (m : Fin ((fw+7)/8))
    (hm : m.val = 4*dst+j) :
    ((List.range 4).foldl
        (fun arr i => memSetDyn arr (BitVec.ofNat 64 (4*dst+i)).toNat (memGetDyn a (4*src+i))) a) m
      = memGetDyn a (4*src+j) := by
  have e : ∀ i, i < 4 → (BitVec.ofNat 64 (4*dst+i)).toNat = 4*dst+i :=
    fun i hi => ofNatToNat (by omega)
  simp only [show List.range 4 = [0,1,2,3] from rfl, List.foldl_cons, List.foldl_nil,
    e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
  rw [memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega),
      memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega)]
  interval_cases j <;> split_ifs <;> first | rfl | omega

/-- The copied frame, read outside the destination slot. -/
theorem copyFold_miss {fw src dst : Nat} (hdst : 4*dst+3 < (fw+7)/8) (hb : (fw+7)/8 ≤ 2 ^ 64)
    (a : Fin ((fw+7)/8) → BitVec 64) (m : Fin ((fw+7)/8))
    (hm : m.val < 4*dst ∨ 4*dst+4 ≤ m.val) :
    ((List.range 4).foldl
        (fun arr i => memSetDyn arr (BitVec.ofNat 64 (4*dst+i)).toNat (memGetDyn a (4*src+i))) a) m
      = a m := by
  have e : ∀ i, i < 4 → (BitVec.ofNat 64 (4*dst+i)).toNat = 4*dst+i :=
    fun i hi => ofNatToNat (by omega)
  simp only [show List.range 4 = [0,1,2,3] from rfl, List.foldl_cons, List.foldl_nil,
    e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
  rw [memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega),
      memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega)]
  split_ifs <;> first | rfl | omega

/-! ## 7. The front-compiled copy denotes the copied frame -/

/-- **The front-compiled slot-copy `Com` denotes the copied frame.**

`o` is what the direct control front makes of `copySlotLowCT fw src dst` over the
single-frame context, `w` the slot its post-varmap resolves `F` to, and `com` the
emitted prefix capped with `ret F`.  On a valuation consistent with a frame-bound
entry environment, the `Com` denotes the input frame `a` with slot `src` copied
into slot `dst`.  The two front matches (`hTrans`, `hName`) and the cap (`hRet`)
appear as hypotheses rather than by unfolding a `Com` definition, so the proof
never forces the `translateDialectControl` scrutinee. -/
theorem copySlotFront_denote (fw src dst : Nat)
    (hsrc : 4*src+3 < (fw+7)/8) (hdst : 4*dst+3 < (fw+7)/8) (hsd : src ≠ dst)
    (hb : (fw+7)/8 ≤ 2 ^ 64)
    (o : DTransOut (inΓF fw)) (V : Ctxt.Valuation (d := catCryptDialect) (inΓF fw))
    (env : SEnvScalar) (w : CVar o.Γ' (.memref ((fw+7)/8)))
    (com : Com catCryptDialect (inΓF fw) (.memref ((fw+7)/8)))
    (a : Fin ((fw+7)/8) → BitVec 64)
    (hF : env "F" = some ⟨.memref ((fw+7)/8), a⟩)
    (hTrans : translateDialectControl (inVMF fw) (copySlotLowCT fw src dst) = some o)
    (hCons : ConsistentS (inVMF fw) V env)
    (hName : o.vm.lookup "F" = some ⟨.memref ((fw+7)/8), w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    com.denote V
      = (List.range 4).foldl
          (fun arr j => memSetDyn arr (BitVec.ofNat 64 (4*dst+j)).toNat
            (memGetDyn a (4*src+j))) a := by
  obtain ⟨envF, hsem, hval⟩ := copySlotLowCT_sem fw src dst hsrc hsd hb a env hF
  obtain ⟨V', hc', hcont⟩ :=
    translateDialectControl_denote_ctl
      (copySlotLowCT_coveredSCtl fw src dst hsrc hdst hb) (inVMF fw) V env envF o
      hCons hTrans hsem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hRet] at hcom'
  obtain rfl := Option.some.inj hcom'
  rw [hden]
  exact hc'.lookup_eq hName hval

/-- The destination slot's `j`-th cell of the front-compiled copy reads the source
    slot's `j`-th cell.  The front-world analogue of
    `Secp256k1LadderStepThreaded.copySlot_slotLimbs_dst`. -/
theorem copySlotFront_denote_get_dst (fw src dst : Nat)
    (hsrc : 4*src+3 < (fw+7)/8) (hdst : 4*dst+3 < (fw+7)/8) (hsd : src ≠ dst)
    (hb : (fw+7)/8 ≤ 2 ^ 64)
    (o : DTransOut (inΓF fw)) (V : Ctxt.Valuation (d := catCryptDialect) (inΓF fw))
    (env : SEnvScalar) (w : CVar o.Γ' (.memref ((fw+7)/8)))
    (com : Com catCryptDialect (inΓF fw) (.memref ((fw+7)/8)))
    (a : Fin ((fw+7)/8) → BitVec 64)
    (hF : env "F" = some ⟨.memref ((fw+7)/8), a⟩)
    (hTrans : translateDialectControl (inVMF fw) (copySlotLowCT fw src dst) = some o)
    (hCons : ConsistentS (inVMF fw) V env)
    (hName : o.vm.lookup "F" = some ⟨.memref ((fw+7)/8), w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (j : Nat) (hj : j < 4) :
    memGetDyn (com.denote V) (4*dst+j) = memGetDyn a (4*src+j) := by
  rw [copySlotFront_denote fw src dst hsrc hdst hsd hb o V env w com a hF hTrans hCons hName hRet]
  have hlt : 4*dst+j < (fw+7)/8 := by omega
  rw [memGetDyn_lt _ hlt]
  exact copyFold_hit hdst hb a j hj ⟨4*dst+j, hlt⟩ rfl

/-- A cell outside the destination slot of the front-compiled copy is preserved.
    The front-world analogue of
    `Secp256k1LadderStepThreaded.copySlot_slotLimbs_other`. -/
theorem copySlotFront_denote_get_other (fw src dst : Nat)
    (hsrc : 4*src+3 < (fw+7)/8) (hdst : 4*dst+3 < (fw+7)/8) (hsd : src ≠ dst)
    (hb : (fw+7)/8 ≤ 2 ^ 64)
    (o : DTransOut (inΓF fw)) (V : Ctxt.Valuation (d := catCryptDialect) (inΓF fw))
    (env : SEnvScalar) (w : CVar o.Γ' (.memref ((fw+7)/8)))
    (com : Com catCryptDialect (inΓF fw) (.memref ((fw+7)/8)))
    (a : Fin ((fw+7)/8) → BitVec 64)
    (hF : env "F" = some ⟨.memref ((fw+7)/8), a⟩)
    (hTrans : translateDialectControl (inVMF fw) (copySlotLowCT fw src dst) = some o)
    (hCons : ConsistentS (inVMF fw) V env)
    (hName : o.vm.lookup "F" = some ⟨.memref ((fw+7)/8), w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (c : Nat) (hc : c < (fw+7)/8) (hout : c < 4*dst ∨ 4*dst+4 ≤ c) :
    memGetDyn (com.denote V) c = memGetDyn a c := by
  rw [copySlotFront_denote fw src dst hsrc hdst hsd hb o V env w com a hF hTrans hCons hName hRet,
    memGetDyn_lt _ hc, memGetDyn_lt a hc]
  exact copyFold_miss hdst hb a ⟨c, hc⟩ hout

/-! ## 8. One dialect down -/

/-- **The front-compiled slot copy, lowered to `Com jasminDialect`, denotes the
    copied frame.** `ctTransTy` is the identity on `.memref`, so the cells cross
    the dialect boundary unchanged; `hLower` supplies the lowering match. -/
theorem copySlotFront_jasmin_denote (fw src dst : Nat)
    (hsrc : 4*src+3 < (fw+7)/8) (hdst : 4*dst+3 < (fw+7)/8) (hsd : src ≠ dst)
    (hb : (fw+7)/8 ≤ 2 ^ 64)
    (o : DTransOut (inΓF fw)) (V : Ctxt.Valuation (d := catCryptDialect) (inΓF fw))
    (env : SEnvScalar) (w : CVar o.Γ' (.memref ((fw+7)/8)))
    (com : Com catCryptDialect (inΓF fw) (.memref ((fw+7)/8)))
    (jcom : Com jasminDialect (mapCtx (inΓF fw)) (mapTy (.memref ((fw+7)/8))))
    (a : Fin ((fw+7)/8) → BitVec 64)
    (hF : env "F" = some ⟨.memref ((fw+7)/8), a⟩)
    (hTrans : translateDialectControl (inVMF fw) (copySlotLowCT fw src dst) = some o)
    (hCons : ConsistentS (inVMF fw) V env)
    (hName : o.vm.lookup "F" = some ⟨.memref ((fw+7)/8), w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hLower : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V)
      = (List.range 4).foldl
          (fun arr j => memSetDyn arr (BitVec.ofNat 64 (4*dst+j)).toNat
            (memGetDyn a (4*src+j))) a := by
  rw [cryptoDialectToJasminCom_denote_eq' com V jcom hLower, ctTransTy_memref,
    copySlotFront_denote fw src dst hsrc hdst hsd hb o V env w com a hF hTrans hCons hName hRet]

end CatCrypt.Crypto.SecureCompilation.X86Backend.Secp256k1LadderCopyFront
