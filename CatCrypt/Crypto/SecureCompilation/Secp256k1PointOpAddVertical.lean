/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody

/-!
# The front-compiled secp256k1 `jacAdd` kernel, from `Com.denote` to the spec

`Secp256k1PointOpFront.jacAddBody` opens with the index slots, the reduction
constants and six coordinate loads — three out of the frame `P1` into
`X1`/`Y1`/`Z1` and three out of the frame `P2` into `X2`/`Y2`/`Z2` — then runs
the `add-2007-bl` schedule and stores `Xp`/`Yp`/`Zp` into the output frame.
This module carries that body from the covered-fragment membership its front
compilation needs to a value statement about the twelve cells the descended
`Com catCryptDialect` denotes.

The `Com` in the final statement is the front's own `ret out` cap: `o` is the
output of `translateDialectControl inVM3 jacAddBody` and `com` is `o.cont`
applied to `Com.ret` at the slot `o.vm` resolves `out` to — the two matches
`Secp256k1PointOpFront.jacAddFrontCom` is defined by. Rewriting that definition
inside a proof forces the match scrutinee, the out-of-memory evaluation recorded
for a single whole-op `Com.denote` (over 11 GB), so the two matches appear as the
hypotheses `hTrans` and `hName`.

## Main results

The coverage of `jacAddBody` and the `Com`-denotation of the front-compiled
kernel live beside their `jacDbl` twins, in
`Secp256k1PointOpFrontCovered.jacAddBody_coveredS` / `_coveredSCtl` and
`Secp256k1PointOpFrontDenote.jacAddFront_denote`; the brick scope from a
canonicality bound is `Secp256k1PointOpPrologue.brickScope_ofLt`, which
`brickScope_of` is an instance of.

* `frame_ne_pl`, `AddFrameIdx`, `idxConst2_run`, `loadCoordA_run` — a two-character
  `P`-headed frame name against the modulus limb slots, the two point frames with
  the cell-index slots, the index and constant block over them, and one coordinate
  load out of a named frame.
* `constVals_load`, `slots_keep`, `slots_trans` — the reduction constants and a
  field element's half-limb slots across a load of a different element.
* `addSched_value`, `addSched_limbs` — the six-coordinate schedule-name readout
  and the half-limb bounds.
* `AddPrologueEntry`, `jacAddPrologue`, `jacAddPrologue_run`,
  `jacAddPrologue_value` — the entry conditions and the two-frame prologue's run
  into `Secp256k1FeAddSubBrick.BrickScope` at
  `Secp256k1PointOpCompositional.addEnv0`, carrying the two frame pointers, the
  index slots and the output pointer through.
* `jacAddSchedule_slotsBound`, `jacAddSchedule_frame`, `jacAddSchedule_out`,
  `jacAddSchedule_ix` — boundness and framing across the addition schedule.
* `jacAddBody_cells` — from an `AddPrologueEntry` environment, `jacAddBody` leaves
  `out` holding `pointCells (jacAddSpec X1 Y1 Z1 X2 Y2 Z2)`.
* `jacAddFrontCom_denote_cells` — the descended addition `Com` denotes those cells.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpAddVertical

open CatCrypt.Crypto.Jasmin.LowCT (LowCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll mask32 pNat)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (idxInit constInit loadField storeField runSchedule jacAddBody jacAddSchedule
   jacAddSpec pointCells inΓ3 inVM3)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk notTmp_of_len)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal schedNameB semScalar_seqAll_append jacAddFront_denote)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional (addEnv0)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (BrickScope hd hdAppend neOfHd headOk_of_hd hd_feHN hd_ZZ hd_CC0 hd_CC1 hd_PL
   feHN feHN_ne_short feHN_ne_cc0 feHN_ne_cc1 feHN_ne_pl hd_opPfx
   ofNat_toNat pl32_lt hd_of_schedName)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (envReader_of_bound semScalar_loadField)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue
  (ConstVals LoadFrame cellVal keep_load feHN_keep_load feVal_load
   limbs_load feVal_congr feVal_eq_zero semScalar_append_run envReader_of_eq
   idxInit_run constInit_run notTmp_ix notTmp_ZZ notTmp_CC0 notTmp_CC1 notTmp_PL
   hd_ix feHN_ne_ix feHN_ne_of_preLast pNat_pos brickScope_ofLt)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope
  (jacAddSchedule_waist_value_brickScope jacAddSchedule_waist_scope)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpEpilogue
  (pointOpEpilogue_cells hd_out)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody
  (SlotsBound fopOut slotsBound_reads brickFold_slotsBound brickFold_frame
   schedule_forall2 notTmp_out ne_empty_of_hd out_ne_opPfx)

/-! ## 3. Two point frames and the cell-index slots -/

theorem notTmp_P1 : ¬ isTmpName "P1" := notTmp_of_len "P1" (by decide)
theorem notTmp_P2 : ¬ isTmpName "P2" := notTmp_of_len "P2" (by decide)

theorem hd_P1 : hd "P1" = some 'P' := rfl
theorem hd_P2 : hd "P2" = some 'P' := rfl
theorem hd_X1 : hd "X1" = some 'X' := rfl
theorem hd_Y1 : hd "Y1" = some 'Y' := rfl
theorem hd_Z1 : hd "Z1" = some 'Z' := rfl
theorem hd_X2 : hd "X2" = some 'X' := rfl
theorem hd_Y2 : hd "Y2" = some 'Y' := rfl
theorem hd_Z2 : hd "Z2" = some 'Z' := rfl

/-- A two-character frame name is not one of the modulus limb slots: both begin
    with `P`, and the modulus slot's second character is `L`. -/
theorem frame_ne_pl {P : String} {d : Char} (hP : P.toList = ['P', d]) (hd2 : d ≠ 'L')
    (i : Nat) : P ≠ s!"PL{i}" := by
  intro h
  have h2 : P.toList = (s!"PL{i}" : String).toList := congrArg String.toList h
  rw [hP, show (s!"PL{i}" : String) = "PL" ++ toString i from rfl, String.toList_append,
    show ("PL" : String).toList = ['P', 'L'] from rfl] at h2
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h2
  exact hd2 h2.2.1

theorem P1_ne_pl (i : Nat) : ("P1" : String) ≠ s!"PL{i}" := frame_ne_pl rfl (by decide) i
theorem P2_ne_pl (i : Nat) : ("P2" : String) ≠ s!"PL{i}" := frame_ne_pl rfl (by decide) i

/-- The two input point frames resolve to their memrefs and the twelve
    cell-index slots hold their indices. -/
structure AddFrameIdx {n : Nat} (E : SEnvScalar) (a1 a2 : Fin n → BitVec 64) : Prop where
  /-- `P1` resolves to the first input point frame. -/
  frame1 : E "P1" = some ⟨.memref n, a1⟩
  /-- `P2` resolves to the second input point frame. -/
  frame2 : E "P2" = some ⟨.memref n, a2⟩
  /-- `ix0 … ix11` hold `0 … 11`. -/
  idx : ∀ i, i < 12 → E s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩

/-- **The index block followed by the constant block, over two frames.** Both
    frame pointers and the index slots are in place, the reduction constants hold
    their values, every half-limb slot of a name with a non-underscore first
    character is untouched, and so is any non-temporary name whose first character
    is none of the block's own. -/
theorem idxConst2_run {n : Nat} {env : SEnvScalar} {a1 a2 : Fin n → BitVec 64}
    (hP1 : env "P1" = some ⟨.memref n, a1⟩) (hP2 : env "P2" = some ⟨.memref n, a2⟩) :
    ∃ E, semScalar (seqAll (idxInit ++ constInit)) env = some E
      ∧ AddFrameIdx E a1 a2 ∧ ConstVals E
      ∧ (∀ (fe : String) (c : Char), hd fe = some c → c ≠ '_' →
          ∀ k, k < 8 → E (feHN fe k) = env (feHN fe k))
      ∧ (∀ (s : String) (c : Char), hd s = some c → ¬ isTmpName s →
          c ≠ 'Z' → c ≠ 'C' → c ≠ 'P' → c ≠ 'i' → E s = env s) := by
  obtain ⟨E1, hs1, hix1, hfr1⟩ := idxInit_run env
  obtain ⟨E2, hs2, hZZ2, hC02, hC12, hPL2, hfr2⟩ := constInit_run E1
  have hframe : ∀ P : String, ¬ isTmpName P → hd P = some 'P' →
      (∀ i, i < 8 → P ≠ s!"PL{i}") → E2 P = env P := by
    intro P hnt hdP hpl
    rw [hfr2 P hnt (neOfHd hdP hd_ZZ (by decide)) (neOfHd hdP hd_CC0 (by decide))
        (neOfHd hdP hd_CC1 (by decide)) hpl,
      hfr1 P hnt (fun i _ => neOfHd hdP (hd_ix i) (by decide))]
  refine ⟨E2, semScalar_append_run hs1 hs2, ⟨?_, ?_, ?_⟩, ⟨hZZ2, hC02, hC12, hPL2⟩, ?_, ?_⟩
  · rw [hframe "P1" notTmp_P1 hd_P1 (fun i _ => P1_ne_pl i)]; exact hP1
  · rw [hframe "P2" notTmp_P2 hd_P2 (fun i _ => P2_ne_pl i)]; exact hP2
  · intro i hi
    rw [hfr2 _ (notTmp_ix i) (neOfHd (hd_ix i) hd_ZZ (by decide))
      (neOfHd (hd_ix i) hd_CC0 (by decide)) (neOfHd (hd_ix i) hd_CC1 (by decide))
      (fun i' _ => neOfHd (hd_ix i) (hd_PL i') (by decide))]
    exact hix1 i hi
  · intro fe c hdc hc' k hk
    have nt : ¬ isTmpName (feHN fe k) := (headOk_of_hd (hd_feHN hdc k) hc').notTmp
    rw [hfr2 (feHN fe k) nt (feHN_ne_short hk hdc (by decide)) (feHN_ne_cc0 hk)
        (feHN_ne_cc1 hk) (fun i hi => feHN_ne_pl hk hi),
      hfr1 (feHN fe k) nt (fun i hi => feHN_ne_ix hk hi)]
  · intro s c hdc hnt hZ hC hP hi
    rw [hfr2 s hnt (neOfHd hdc hd_ZZ hZ) (neOfHd hdc hd_CC0 hC) (neOfHd hdc hd_CC1 hC)
        (fun i' _ => neOfHd hdc (hd_PL i') hP),
      hfr1 s hnt (fun i' _ => neOfHd hdc (hd_ix i') hi)]

/-! ## 4. One coordinate load out of a named frame -/

/-- **One coordinate load out of a `P`-headed point frame.** The eight half-limb
    slots of `fe` carry the halves of the four frame cells at offset `o`, and both
    frame pointers and the index slots come through unchanged. -/
theorem loadCoordA_run {n o : Nat} {a1 a2 a : Fin n → BitVec 64} {E : SEnvScalar}
    {arrN fe : String} {cf ca : Char} {rf ra : List Char}
    (hfe : fe.toList = cf :: rf) (hcU : cf ≠ '_') (hci : cf ≠ 'i') (hcP : cf ≠ 'P')
    (harr : arrN.toList = ca :: ra) (hcaP : ca = 'P') (ho : o + 3 < 12)
    (ha : E arrN = some ⟨.memref n, a⟩) (hFI : AddFrameIdx E a1 a2) :
    ∃ E', semScalar (seqAll (loadField 96 arrN o fe)) E = some E'
      ∧ (∀ j, j < 4 → E' s!"{fe}h{2 * j}"
            = some ⟨.sword 64, memGetDyn a (BitVec.ofNat 64 (o + j)).toNat
                &&& BitVec.ofNat 64 mask32⟩)
      ∧ (∀ j, j < 4 → E' s!"{fe}h{2 * j + 1}"
            = some ⟨.sword 64, memGetDyn a (BitVec.ofNat 64 (o + j)).toNat
                >>> (BitVec.ofNat 64 32).toNat⟩)
      ∧ AddFrameIdx E' a1 a2 ∧ LoadFrame fe E' E := by
  have hdfe : hd fe = some cf := by
    show fe.toList.head? = some cf
    rw [hfe]
    rfl
  obtain ⟨E', hs, hlo, hhi, hfr⟩ :=
    semScalar_loadField (fw := 96) (o := o) (arrN := arrN) (fe := fe) (a := a)
      (iw := fun j => BitVec.ofNat 64 (o + j)) (cf := cf) (rf := rf) (ca := ca) (ra := ra)
      hfe hcU hci harr (by rw [hcaP]; exact Ne.symm hcP) ha
      (fun j hj => hFI.idx (o + j) (by omega))
  exact ⟨E', hs, hlo, hhi,
    ⟨(keep_load hfr hdfe notTmp_P1 hd_P1 (Ne.symm hcP)).trans hFI.frame1,
     (keep_load hfr hdfe notTmp_P2 hd_P2 (Ne.symm hcP)).trans hFI.frame2,
     fun i hi => (keep_load hfr hdfe (notTmp_ix i) (hd_ix i) (Ne.symm hci)).trans
       (hFI.idx i hi)⟩,
    hfr⟩

/-- **The reduction constants come through one coordinate load.** -/
theorem constVals_load {E E' : SEnvScalar} {fe : String} {c : Char}
    (hfr : LoadFrame fe E' E) (hdfe : hd fe = some c) (hcC : c ≠ 'C') (hcP : c ≠ 'P')
    (hZZ : ∀ j, j < 4 → ("ZZ" : String) ≠ s!"{fe}u{j}")
    (hC : ConstVals E) : ConstVals E' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfr "ZZ" notTmp_ZZ hZZ (fun k hk => Ne.symm (feHN_ne_short hk hdfe (by decide)))]
    exact hC.zz
  · rw [keep_load hfr hdfe notTmp_CC0 hd_CC0 (Ne.symm hcC)]; exact hC.lo
  · rw [keep_load hfr hdfe notTmp_CC1 hd_CC1 (Ne.symm hcC)]; exact hC.hi
  · intro i hi
    rw [keep_load hfr hdfe (notTmp_PL i) (hd_PL i) (Ne.symm hcP)]
    exact hC.pl i hi

/-- **A field element's half-limb slots survive a load of a different element.** -/
theorem slots_keep {E E' : SEnvScalar} {fe g : String} {c : Char}
    (hfr : LoadFrame g E' E) (hdfe : hd fe = some c) (hc : c ≠ '_') (hne : fe ≠ g) :
    ∀ k, k < 8 → E' (feHN fe k) = E (feHN fe k) :=
  fun k hk => feHN_keep_load hfr ((headOk_of_hd (hd_feHN hdfe k) hc).notTmp) hk hne

/-- Two half-limb-slot agreements compose. -/
theorem slots_trans {E1 E2 E3 : SEnvScalar} {fe : String}
    (h1 : ∀ k, k < 8 → E3 (feHN fe k) = E2 (feHN fe k))
    (h2 : ∀ k, k < 8 → E2 (feHN fe k) = E1 (feHN fe k)) :
    ∀ k, k < 8 → E3 (feHN fe k) = E1 (feHN fe k) :=
  fun k hk => (h1 k hk).trans (h2 k hk)

/-! ## 5. The two-frame prologue -/

/-- The index slots, the reduction constants and the six coordinate loads that
    open `Secp256k1PointOpFront.jacAddBody`. -/
def jacAddPrologue : List LowCT :=
  idxInit ++ constInit
    ++ loadField 96 "P1" 0 "X1" ++ loadField 96 "P1" 4 "Y1" ++ loadField 96 "P1" 8 "Z1"
    ++ loadField 96 "P2" 0 "X2" ++ loadField 96 "P2" 4 "Y2" ++ loadField 96 "P2" 8 "Z2"

/-- `jacAddBody` is the prologue followed by the schedule and the three stores. -/
theorem jacAddBody_eq_prologue_append :
    jacAddBody = seqAll (jacAddPrologue ++ (runSchedule jacAddSchedule
      ++ storeField 96 0 "Xp" ++ storeField 96 4 "Yp" ++ storeField 96 8 "Zp")) := by
  simp only [jacAddBody, jacAddPrologue, List.append_assoc]

/-- **Entry conditions of the `jacAdd` prologue.** The frame pointers `P1` and
    `P2` hold the memrefs `a1` and `a2`, whose cells `0..3`, `4..7` and `8..11`
    carry the coordinates of the two input points little-endian; every
    schedule-name half-limb slot reads `0`; and the six coordinates are canonical
    residues below `p`. -/
structure AddPrologueEntry {n : Nat} (env : SEnvScalar) (a1 a2 : Fin n → BitVec 64)
    (X1 Y1 Z1 X2 Y2 Z2 : Nat) : Prop where
  /-- `P1` resolves to the first input point frame. -/
  frame1 : env "P1" = some ⟨.memref n, a1⟩
  /-- `P2` resolves to the second input point frame. -/
  frame2 : env "P2" = some ⟨.memref n, a2⟩
  /-- Cells `0..3` of `P1` carry `X1`. -/
  coordX1 : cellVal a1 0 = X1
  /-- Cells `4..7` of `P1` carry `Y1`. -/
  coordY1 : cellVal a1 4 = Y1
  /-- Cells `8..11` of `P1` carry `Z1`. -/
  coordZ1 : cellVal a1 8 = Z1
  /-- Cells `0..3` of `P2` carry `X2`. -/
  coordX2 : cellVal a2 0 = X2
  /-- Cells `4..7` of `P2` carry `Y2`. -/
  coordY2 : cellVal a2 4 = Y2
  /-- Cells `8..11` of `P2` carry `Z2`. -/
  coordZ2 : cellVal a2 8 = Z2
  /-- No schedule-name half-limb slot is bound on entry. -/
  zeroed : ∀ fe, schedNameB fe = true → ∀ k, k < 8 → envReader env (feHN fe k) = 0
  /-- `X1` is a canonical residue. -/
  ltX1 : X1 < pNat
  /-- `Y1` is a canonical residue. -/
  ltY1 : Y1 < pNat
  /-- `Z1` is a canonical residue. -/
  ltZ1 : Z1 < pNat
  /-- `X2` is a canonical residue. -/
  ltX2 : X2 < pNat
  /-- `Y2` is a canonical residue. -/
  ltY2 : Y2 < pNat
  /-- `Z2` is a canonical residue. -/
  ltZ2 : Z2 < pNat

theorem addEnv0_lt {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h1 : X1 < pNat) (h2 : Y1 < pNat)
    (h3 : Z1 < pNat) (h4 : X2 < pNat) (h5 : Y2 < pNat) (h6 : Z2 < pNat) (fe : String) :
    addEnv0 X1 Y1 Z1 X2 Y2 Z2 fe < pNat := by
  simp only [addEnv0]
  split_ifs <;> first | assumption | exact pNat_pos
/-- **The schedule-name readout is `addEnv0`.** The six input coordinates carry
    their frame values and every other schedule name reads `0`. -/
theorem addSched_value {E : SEnvScalar} {X1 Y1 Z1 X2 Y2 Z2 : Nat}
    (hx1 : feVal E "X1" = X1) (hy1 : feVal E "Y1" = Y1) (hz1 : feVal E "Z1" = Z1)
    (hx2 : feVal E "X2" = X2) (hy2 : feVal E "Y2" = Y2) (hz2 : feVal E "Z2" = Z2)
    (hzero : ∀ fe, schedNameB fe = true → fe ≠ "X1" → fe ≠ "Y1" → fe ≠ "Z1" →
        fe ≠ "X2" → fe ≠ "Y2" → fe ≠ "Z2" →
        ∀ k, k < 8 → envReader E (feHN fe k) = 0) :
    ∀ fe, schedNameB fe = true → feVal E fe = addEnv0 X1 Y1 Z1 X2 Y2 Z2 fe := by
  intro fe hfe
  by_cases h1 : fe = "X1"
  · subst h1; rw [hx1]; simp [addEnv0]
  by_cases h2 : fe = "Y1"
  · subst h2; rw [hy1]; simp [addEnv0]
  by_cases h3 : fe = "Z1"
  · subst h3; rw [hz1]; simp [addEnv0]
  by_cases h4 : fe = "X2"
  · subst h4; rw [hx2]; simp [addEnv0]
  by_cases h5 : fe = "Y2"
  · subst h5; rw [hy2]; simp [addEnv0]
  by_cases h6 : fe = "Z2"
  · subst h6; rw [hz2]; simp [addEnv0]
  rw [feVal_eq_zero (hzero fe hfe h1 h2 h3 h4 h5 h6)]
  simp [addEnv0, h1, h2, h3, h4, h5, h6]

/-- **Every schedule-name half-limb is below `2^32`.** -/
theorem addSched_limbs {E : SEnvScalar}
    (hx1 : ∀ k, k < 8 → (envReader E (feHN "X1" k)).toNat < 2 ^ 32)
    (hy1 : ∀ k, k < 8 → (envReader E (feHN "Y1" k)).toNat < 2 ^ 32)
    (hz1 : ∀ k, k < 8 → (envReader E (feHN "Z1" k)).toNat < 2 ^ 32)
    (hx2 : ∀ k, k < 8 → (envReader E (feHN "X2" k)).toNat < 2 ^ 32)
    (hy2 : ∀ k, k < 8 → (envReader E (feHN "Y2" k)).toNat < 2 ^ 32)
    (hz2 : ∀ k, k < 8 → (envReader E (feHN "Z2" k)).toNat < 2 ^ 32)
    (hzero : ∀ fe, schedNameB fe = true → fe ≠ "X1" → fe ≠ "Y1" → fe ≠ "Z1" →
        fe ≠ "X2" → fe ≠ "Y2" → fe ≠ "Z2" →
        ∀ k, k < 8 → envReader E (feHN fe k) = 0) :
    ∀ fe, schedNameB fe = true → ∀ k, k < 8 →
      (envReader E (feHN fe k)).toNat < 2 ^ 32 := by
  intro fe hfe k hk
  by_cases h1 : fe = "X1"
  · subst h1; exact hx1 k hk
  by_cases h2 : fe = "Y1"
  · subst h2; exact hy1 k hk
  by_cases h3 : fe = "Z1"
  · subst h3; exact hz1 k hk
  by_cases h4 : fe = "X2"
  · subst h4; exact hx2 k hk
  by_cases h5 : fe = "Y2"
  · subst h5; exact hy2 k hk
  by_cases h6 : fe = "Z2"
  · subst h6; exact hz2 k hk
  rw [hzero fe hfe h1 h2 h3 h4 h5 h6 k hk]
  simp

/-- **The `jacAdd` prologue runs into the brick scope at `addEnv0`.** From an
    entry environment satisfying `AddPrologueEntry`, the index slots, the
    reduction constants and the six coordinate loads leave an environment in
    `Secp256k1FeAddSubBrick.BrickScope` whose schedule-name half-limb readout is
    `Secp256k1PointOpCompositional.addEnv0 X1 Y1 Z1 X2 Y2 Z2`. -/
theorem jacAddPrologue_run {n : Nat} (env : SEnvScalar) (a1 a2 : Fin n → BitVec 64)
    (X1 Y1 Z1 X2 Y2 Z2 : Nat) (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2) :
    ∃ env₁, semScalar (seqAll jacAddPrologue) env = some env₁
      ∧ BrickScope env₁
      ∧ (∀ fe, schedNameB fe = true →
          feVal env₁ fe = addEnv0 X1 Y1 Z1 X2 Y2 Z2 fe)
      ∧ AddFrameIdx env₁ a1 a2
      ∧ env₁ "out" = env "out" := by
  obtain ⟨E2, hs2, hFI2, hCV2, hslot2, hkeep2⟩ := idxConst2_run hE.frame1 hE.frame2
  obtain ⟨E3, hs3, hloX1, hhiX1, hFI3, hfr3⟩ :=
    loadCoordA_run (o := 0) (arrN := "P1") (fe := "X1") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI2.frame1 hFI2
  obtain ⟨E4, hs4, hloY1, hhiY1, hFI4, hfr4⟩ :=
    loadCoordA_run (o := 4) (arrN := "P1") (fe := "Y1") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI3.frame1 hFI3
  obtain ⟨E5, hs5, hloZ1, hhiZ1, hFI5, hfr5⟩ :=
    loadCoordA_run (o := 8) (arrN := "P1") (fe := "Z1") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI4.frame1 hFI4
  obtain ⟨E6, hs6, hloX2, hhiX2, hFI6, hfr6⟩ :=
    loadCoordA_run (o := 0) (arrN := "P2") (fe := "X2") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI5.frame2 hFI5
  obtain ⟨E7, hs7, hloY2, hhiY2, hFI7, hfr7⟩ :=
    loadCoordA_run (o := 4) (arrN := "P2") (fe := "Y2") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI6.frame2 hFI6
  obtain ⟨E8, hs8, hloZ2, hhiZ2, hFI8, hfr8⟩ :=
    loadCoordA_run (o := 8) (arrN := "P2") (fe := "Z2") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI7.frame2 hFI7
  have hrun : semScalar (seqAll jacAddPrologue) env = some E8 :=
    semScalar_append_run (semScalar_append_run (semScalar_append_run
      (semScalar_append_run (semScalar_append_run (semScalar_append_run hs2 hs3) hs4)
        hs5) hs6) hs7) hs8
  have hCV8 : ConstVals E8 :=
    constVals_load hfr8 hd_Z2 (by decide) (by decide)
      (fun j hj => by interval_cases j <;> decide)
      (constVals_load hfr7 hd_Y2 (by decide) (by decide)
        (fun j hj => by interval_cases j <;> decide)
        (constVals_load hfr6 hd_X2 (by decide) (by decide)
          (fun j hj => by interval_cases j <;> decide)
          (constVals_load hfr5 hd_Z1 (by decide) (by decide)
            (fun j hj => by interval_cases j <;> decide)
            (constVals_load hfr4 hd_Y1 (by decide) (by decide)
              (fun j hj => by interval_cases j <;> decide)
              (constVals_load hfr3 hd_X1 (by decide) (by decide)
                (fun j hj => by interval_cases j <;> decide) hCV2)))))
  have kX1 : ∀ k, k < 8 → E8 (feHN "X1" k) = E3 (feHN "X1" k) :=
    slots_trans (slots_keep hfr8 hd_X1 (by decide) (by decide))
      (slots_trans (slots_keep hfr7 hd_X1 (by decide) (by decide))
        (slots_trans (slots_keep hfr6 hd_X1 (by decide) (by decide))
          (slots_trans (slots_keep hfr5 hd_X1 (by decide) (by decide))
            (slots_keep hfr4 hd_X1 (by decide) (by decide)))))
  have kY1 : ∀ k, k < 8 → E8 (feHN "Y1" k) = E4 (feHN "Y1" k) :=
    slots_trans (slots_keep hfr8 hd_Y1 (by decide) (by decide))
      (slots_trans (slots_keep hfr7 hd_Y1 (by decide) (by decide))
        (slots_trans (slots_keep hfr6 hd_Y1 (by decide) (by decide))
          (slots_keep hfr5 hd_Y1 (by decide) (by decide))))
  have kZ1 : ∀ k, k < 8 → E8 (feHN "Z1" k) = E5 (feHN "Z1" k) :=
    slots_trans (slots_keep hfr8 hd_Z1 (by decide) (by decide))
      (slots_trans (slots_keep hfr7 hd_Z1 (by decide) (by decide))
        (slots_keep hfr6 hd_Z1 (by decide) (by decide)))
  have kX2 : ∀ k, k < 8 → E8 (feHN "X2" k) = E6 (feHN "X2" k) :=
    slots_trans (slots_keep hfr8 hd_X2 (by decide) (by decide))
      (slots_keep hfr7 hd_X2 (by decide) (by decide))
  have kY2 : ∀ k, k < 8 → E8 (feHN "Y2" k) = E7 (feHN "Y2" k) :=
    slots_keep hfr8 hd_Y2 (by decide) (by decide)
  have hvX1 : feVal E8 "X1" = X1 := by
    rw [feVal_congr kX1, feVal_load (by norm_num) hloX1 hhiX1]; exact hE.coordX1
  have hvY1 : feVal E8 "Y1" = Y1 := by
    rw [feVal_congr kY1, feVal_load (by norm_num) hloY1 hhiY1]; exact hE.coordY1
  have hvZ1 : feVal E8 "Z1" = Z1 := by
    rw [feVal_congr kZ1, feVal_load (by norm_num) hloZ1 hhiZ1]; exact hE.coordZ1
  have hvX2 : feVal E8 "X2" = X2 := by
    rw [feVal_congr kX2, feVal_load (by norm_num) hloX2 hhiX2]; exact hE.coordX2
  have hvY2 : feVal E8 "Y2" = Y2 := by
    rw [feVal_congr kY2, feVal_load (by norm_num) hloY2 hhiY2]; exact hE.coordY2
  have hvZ2 : feVal E8 "Z2" = Z2 := by
    rw [feVal_load (by norm_num) hloZ2 hhiZ2]; exact hE.coordZ2
  have hbX1 : ∀ k, k < 8 → (envReader E8 (feHN "X1" k)).toNat < 2 ^ 32 := fun k hk => by
    rw [envReader_of_eq (kX1 k hk)]
    exact limbs_load (a := a1) (iw := fun j => BitVec.ofNat 64 (0 + j)) hloX1 hhiX1 k hk
  have hbY1 : ∀ k, k < 8 → (envReader E8 (feHN "Y1" k)).toNat < 2 ^ 32 := fun k hk => by
    rw [envReader_of_eq (kY1 k hk)]
    exact limbs_load (a := a1) (iw := fun j => BitVec.ofNat 64 (4 + j)) hloY1 hhiY1 k hk
  have hbZ1 : ∀ k, k < 8 → (envReader E8 (feHN "Z1" k)).toNat < 2 ^ 32 := fun k hk => by
    rw [envReader_of_eq (kZ1 k hk)]
    exact limbs_load (a := a1) (iw := fun j => BitVec.ofNat 64 (8 + j)) hloZ1 hhiZ1 k hk
  have hbX2 : ∀ k, k < 8 → (envReader E8 (feHN "X2" k)).toNat < 2 ^ 32 := fun k hk => by
    rw [envReader_of_eq (kX2 k hk)]
    exact limbs_load (a := a2) (iw := fun j => BitVec.ofNat 64 (0 + j)) hloX2 hhiX2 k hk
  have hbY2 : ∀ k, k < 8 → (envReader E8 (feHN "Y2" k)).toNat < 2 ^ 32 := fun k hk => by
    rw [envReader_of_eq (kY2 k hk)]
    exact limbs_load (a := a2) (iw := fun j => BitVec.ofNat 64 (4 + j)) hloY2 hhiY2 k hk
  have hbZ2 : ∀ k, k < 8 → (envReader E8 (feHN "Z2" k)).toNat < 2 ^ 32 :=
    limbs_load (a := a2) (iw := fun j => BitVec.ofNat 64 (8 + j)) hloZ2 hhiZ2
  have hother : ∀ fe, schedNameB fe = true → fe ≠ "X1" → fe ≠ "Y1" → fe ≠ "Z1" →
      fe ≠ "X2" → fe ≠ "Y2" → fe ≠ "Z2" →
      ∀ k, k < 8 → envReader E8 (feHN fe k) = 0 := by
    intro fe hfe h1 h2 h3 h4 h5 h6 k hk
    obtain ⟨c, hdc, -, hc'⟩ := hd_of_schedName hfe
    have nt : ¬ isTmpName (feHN fe k) := (headOk_of_hd (hd_feHN hdc k) hc').notTmp
    have hchain : E8 (feHN fe k) = env (feHN fe k) := by
      rw [feHN_keep_load hfr8 nt hk h6, feHN_keep_load hfr7 nt hk h5,
        feHN_keep_load hfr6 nt hk h4, feHN_keep_load hfr5 nt hk h3,
        feHN_keep_load hfr4 nt hk h2, feHN_keep_load hfr3 nt hk h1,
        hslot2 fe c hdc hc' k hk]
    rw [envReader_of_eq hchain]
    exact hE.zeroed fe hfe k hk
  have hval := addSched_value hvX1 hvY1 hvZ1 hvX2 hvY2 hvZ2 hother
  have hout : E8 "out" = env "out" := by
    rw [keep_load hfr8 hd_Z2 notTmp_out hd_out (by decide),
      keep_load hfr7 hd_Y2 notTmp_out hd_out (by decide),
      keep_load hfr6 hd_X2 notTmp_out hd_out (by decide),
      keep_load hfr5 hd_Z1 notTmp_out hd_out (by decide),
      keep_load hfr4 hd_Y1 notTmp_out hd_out (by decide),
      keep_load hfr3 hd_X1 notTmp_out hd_out (by decide),
      hkeep2 "out" 'o' hd_out notTmp_out (by decide) (by decide) (by decide) (by decide)]
  refine ⟨E8, hrun, brickScope_ofLt hCV8
    (addSched_limbs hbX1 hbY1 hbZ1 hbX2 hbY2 hbZ2 hother) (fun fe hfe => ?_), hval,
    hFI8, hout⟩
  rw [hval fe hfe]
  exact addEnv0_lt hE.ltX1 hE.ltY1 hE.ltZ1 hE.ltX2 hE.ltY2 hE.ltZ2 fe

/-- **The `jacAdd` prologue's value tie, in hypothesis form.** Whatever
    environment the prologue runs to lies in `BrickScope`, holds `addEnv0`, keeps
    both frame pointers with the index slots, and keeps the output pointer. -/
theorem jacAddPrologue_value {n : Nat} (env env₁ : SEnvScalar)
    (a1 a2 : Fin n → BitVec 64) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2)
    (hSem : semScalar (seqAll jacAddPrologue) env = some env₁) :
    BrickScope env₁
      ∧ (∀ fe, schedNameB fe = true → feVal env₁ fe = addEnv0 X1 Y1 Z1 X2 Y2 Z2 fe)
      ∧ AddFrameIdx env₁ a1 a2 ∧ env₁ "out" = env "out" := by
  obtain ⟨e, hs, hsc, hv, hFI, hout⟩ := jacAddPrologue_run env a1 a2 X1 Y1 Z1 X2 Y2 Z2 hE
  rw [hSem] at hs
  obtain rfl := Option.some.inj hs
  exact ⟨hsc, hv, hFI, hout⟩

/-! ## 6. Across the addition schedule -/

/-- **A field element the addition schedule writes is bound at its exit.** -/
theorem jacAddSchedule_slotsBound (fe : String)
    (hnt : ∀ k, k < 8 → ¬ isTmpName (feHN fe k))
    (hmem : fe ∈ jacAddSchedule.map fopOut) (env env' : SEnvScalar)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    SlotsBound env' fe :=
  brickFold_slotsBound fe hnt jacAddSchedule _ (schedule_forall2 jacAddSchedule)
    hmem env env' hSem

/-- **A name no brick binds comes through the addition schedule.** -/
theorem jacAddSchedule_frame (s : String) (hnt : ¬ isTmpName s)
    (hpfx : ∀ (i : Nat) (w : String), s ≠ s!"op{i}" ++ w) (hemp : s ≠ "")
    (hslot : ∀ (fe : String) (k : Nat), k < 8 → s ≠ feHN fe k)
    (env env' : SEnvScalar)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    env' s = env s :=
  brickFold_frame s hnt hpfx hemp hslot jacAddSchedule _
    (schedule_forall2 jacAddSchedule) env env' hSem

/-- **The output pointer comes through the addition schedule.** -/
theorem jacAddSchedule_out {env env' : SEnvScalar}
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    env' "out" = env "out" :=
  jacAddSchedule_frame "out" notTmp_out out_ne_opPfx (ne_empty_of_hd hd_out)
    (fun _ k hk => Ne.symm (feHN_ne_of_preLast hk (by decide))) env env' hSem

/-- **An index slot comes through the addition schedule.** -/
theorem jacAddSchedule_ix {env env' : SEnvScalar} (i : Nat) (hi : i < 12)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    env' s!"ix{i}" = env s!"ix{i}" :=
  jacAddSchedule_frame s!"ix{i}" (notTmp_ix i)
    (fun j _ => neOfHd (hd_ix i) (hdAppend (hd_opPfx j)) (by decide))
    (ne_empty_of_hd (hd_ix i))
    (fun _ k hk => Ne.symm (feHN_ne_ix hk hi)) env env' hSem

/-- **An addition-schedule output with a head-clean name is bound at the
    schedule's exit.** -/
theorem slotsBound_of_hdA (fe : String) (c : Char) (hdfe : hd fe = some c) (hc : c ≠ '_')
    (hmem : fe ∈ jacAddSchedule.map fopOut) (env env' : SEnvScalar)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    SlotsBound env' fe :=
  jacAddSchedule_slotsBound fe
    (fun k _ => HeadOk.notTmp (headOk_of_hd (hd_feHN hdfe k) hc)) hmem env env' hSem

/-! ## 7. The whole body -/

/-- `jacAddBody` as the prologue, the schedule, and the three-`storeField`
    epilogue, associated so each stage is one waist. -/
theorem jacAddBody_split :
    jacAddBody = seqAll (jacAddPrologue ++ (runSchedule jacAddSchedule
      ++ (storeField 96 0 "Xp" ++ storeField 96 4 "Yp" ++ storeField 96 8 "Zp"))) := by
  rw [jacAddBody_eq_prologue_append]
  simp only [List.append_assoc]

/-- **The `jacAdd` body's output frame.** From an entry environment satisfying
    `AddPrologueEntry` whose `out` holds a 12-cell frame, a successful run of
    `Secp256k1PointOpFront.jacAddBody` leaves `out` holding
    `Secp256k1PointOpFront.pointCells` of `jacAddSpec X1 Y1 Z1 X2 Y2 Z2` — cells
    `0..3` the limbs of `X3`, cells `4..7` those of `Y3`, cells `8..11` those of
    `Z3`. -/
theorem jacAddBody_cells {n : Nat} {env env' : SEnvScalar} {a1 a2 : Fin n → BitVec 64}
    {b : Fin 12 → BitVec 64} {X1 Y1 Z1 X2 Y2 Z2 : Nat}
    (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hRun : semScalar jacAddBody env = some env') :
    ∃ fr : Fin 12 → BitVec 64, env' "out" = some ⟨.memref 12, fr⟩
      ∧ ∀ m : Fin 12, (fr m).toNat
          = (pointCells (jacAddSpec X1 Y1 Z1 X2 Y2 Z2)).getD m.val 0 := by
  rw [jacAddBody_split, semScalar_seqAll_append] at hRun
  cases h1 : semScalar (seqAll jacAddPrologue) env with
  | none => rw [h1] at hRun; simp at hRun
  | some E1 =>
      rw [h1, Option.bind_some, semScalar_seqAll_append] at hRun
      cases h2 : semScalar (seqAll (runSchedule jacAddSchedule)) E1 with
      | none => rw [h2] at hRun; simp at hRun
      | some E2 =>
          rw [h2, Option.bind_some] at hRun
          obtain ⟨hsc1, hv1, hFI1, ho1⟩ :=
            jacAddPrologue_value env E1 a1 a2 X1 Y1 Z1 X2 Y2 Z2 hE h1
          have hb2 : E2 "out" = some ⟨.memref 12, b⟩ := by
            rw [jacAddSchedule_out h2, ho1]
            exact hout
          have hix2 : ∀ i, i < 12 → E2 s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩ := by
            intro i hi
            rw [jacAddSchedule_ix i hi h2]
            exact hFI1.idx i hi
          obtain ⟨env'', fr, hsem3, hout3, hcells⟩ :=
            pointOpEpilogue_cells (jacAddSchedule_waist_scope E1 E2 hsc1 h2) hb2 hix2
              (slotsBound_reads
                (slotsBound_of_hdA "Xp" 'X' rfl (by decide) (by decide) E1 E2 h2))
              (slotsBound_reads
                (slotsBound_of_hdA "Yp" 'Y' rfl (by decide) (by decide) E1 E2 h2))
              (slotsBound_reads
                (slotsBound_of_hdA "Zp" 'Z' rfl (by decide) (by decide) E1 E2 h2))
          rw [hRun] at hsem3
          obtain rfl : env' = env'' := Option.some.inj hsem3
          refine ⟨fr, hout3, fun m => ?_⟩
          rw [hcells m,
            jacAddSchedule_waist_value_brickScope E1 E2 X1 Y1 Z1 X2 Y2 Z2 hsc1 hv1 h2]

/-! ## 8. The descended addition `Com` -/

/-- **The descended addition `Com` denotes the spec's cell frame.** On a valuation
    consistent with an entry environment in `AddPrologueEntry`, the front's
    `ret out` cap denotes the twelve cells of
    `pointCells (jacAddSpec X1 Y1 Z1 X2 Y2 Z2)`. -/
theorem jacAddFrontCom_denote_cells {n : Nat}
    (o : DTransOut inΓ3) (V : Ctxt.Valuation (d := catCryptDialect) inΓ3)
    (env env' : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (com : Com catCryptDialect inΓ3 (.memref 12))
    (a1 a2 : Fin n → BitVec 64) (b : Fin 12 → BitVec 64) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hTrans : translateDialectControl inVM3 jacAddBody = some o)
    (hCons : ConsistentS inVM3 V env)
    (hSem : semScalar jacAddBody env = some env')
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    ∀ m : Fin 12,
      ((com.denote V) m).toNat
        = (pointCells (jacAddSpec X1 Y1 Z1 X2 Y2 Z2)).getD m.val 0 := by
  obtain ⟨fr, hfr, hcells⟩ := jacAddBody_cells hE hout hSem
  rw [jacAddFront_denote o V env env' w fr com hTrans hCons hSem hName hfr hRet]
  exact hcells

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpAddVertical
