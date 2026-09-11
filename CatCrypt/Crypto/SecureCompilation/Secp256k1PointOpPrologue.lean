/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip

/-!
# The prologue of the front-compiled secp256k1 doubling kernel

`Secp256k1PointOpFront.jacDblBody` opens with the index slots `ix0 … ix11`, the
reduction constants `ZZ`/`CC0`/`CC1`/`PL0 … PL7`, and the three coordinate loads
that split the twelve `u64` cells of the input frame `P` into the half-limb slots
of the field elements `X`, `Y` and `Z`. This module runs that block through the
scalar waist semantics `TranslateDialectScalar.semScalar` and reads off the two
facts the schedule's value tie assumes: the resulting environment lies in
`Secp256k1FeAddSubBrick.BrickScope`, and its half-limb readout on the schedule
names is `Secp256k1PointOpCompositional.dblEnv0`.

## The entry conditions

`PrologueEntry env a X Y Z` says that `P` holds the memref `a`, that the four
cells at offsets `0`, `4` and `8` carry `X`, `Y` and `Z` little-endian, that every
schedule-name half-limb slot reads `0`, and that the three coordinates are
canonical residues below `p`. The zero condition describes a fresh entry
environment: the front's argument context binds `out` and `P` only, so no
field-element slot is bound when the body starts.

## Main results

* `preLast`, `feHN_ne_of_preLast` — a half-limb slot name ends in `h` followed by
  one digit, so a name whose one-before-last character differs is not one.
* `semScalar_litList` — a block of literal scalar assignments binds each name to
  its literal and leaves every other non-temporary slot alone.
* `idxInit_run`, `constInit_run` — the index slots and the reduction constants.
* `loadCoord_run` — one coordinate load out of the frame, with `LoadFrame` as
  its frame condition. The underlying waist semantics is
  `Secp256k1PointOpFrameRoundTrip.semScalar_loadField`.
* `feVal_load`, `limbs_load` — a loaded field element's half-limb readout is the
  little-endian value of the four frame cells, and each half-limb is below `2^32`.
* `idxConst_run`, `loadCoord_run` — the two prologue stages, each carrying its
  postcondition as `FrameIdx` and `ConstVals` and its frame condition as
  `LoadFrame`.
* `sched_value`, `sched_limbs`, `brickScope_ofLt`, `brickScope_of` — the
  schedule-name readout, the half-limb bounds, and the `BrickScope` they
  assemble, in the canonicality-bound form and at `dblEnv0`.
* `jacDblPrologue_run`, `jacDblPrologue_value` — the prologue runs from a
  `PrologueEntry` environment to one in `BrickScope` whose schedule-name readout
  is `dblEnv0 X Y Z`, in existential and in hypothesis form.
* `jacDblBody_eq_prologue_append` — `jacDblBody` is the prologue followed by the
  schedule and the three coordinate stores.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (seqAll mask32 pNat pl32 cc0 cc1)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (idxInit constInit loadField storeField runSchedule jacDblBody jacDblSchedule)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote (feVal schedNameB)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional (dblEnv0)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk notTmp_of_len)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (BrickScope hd hdAppend neOfHd headOk_of_hd hd_feHN hd_ZZ hd_CC0 hd_CC1 hd_PL
   feHN feHN_assoc feHN_inj feHN_ne_short feHN_ne_cc0 feHN_ne_cc1 feHN_ne_pl
   feVal_eq_accN accN accN_congr ofNat_toNat pl32_lt idxNe hd_of_schedName)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (semScalar_setExpr_run semScalar_arrLoadList semScalar_halfSplitList seqAll_step
   semScalar_loadField
   envReader_of_bound feVal_of_halves half_lo half_hi toNat_ofNat_32 slot_inj
   slot_ne_tag head_ne_slot ix_toList)

/-! ## 1. Slot-name algebra -/

/-- The character one place before the last of a name. -/
def preLast (v : String) : Option Char := v.toList.reverse.tail.head?

/-- A half-limb slot name ends in `h` followed by one digit. -/
theorem preLast_feHN {u : String} {k : Nat} (hk : k < 8) :
    preLast (feHN u k) = some 'h' := by
  obtain ⟨d, hdig⟩ : ∃ d : Char, ("h" ++ toString k).toList = ['h', d] := by
    interval_cases k <;> exact ⟨_, rfl⟩
  -- Rewrite the character list first: left to `simp`, the digit suffix unfolds
  -- into `Nat.toDigits` internals instead of matching `hdig`.
  have hl : (feHN u k).toList = u.toList ++ ['h', d] := by
    rw [feHN_assoc, String.toList_append, hdig]
  simp [preLast, hl]

/-- A name whose one-before-last character is not `h` is not a half-limb slot. -/
theorem feHN_ne_of_preLast {u v : String} {k : Nat} (hk : k < 8)
    (h : preLast v ≠ some 'h') : feHN u k ≠ v := by
  intro he
  apply h
  rw [← he]
  exact preLast_feHN hk

/-- A `u64` staging slot name is not a half-limb slot name. -/
theorem feHN_ne_uSlot {u v : String} {k j : Nat} (hk : k < 8) (hj : j < 4) :
    feHN u k ≠ s!"{v}u{j}" := by
  have h : (s!"{v}u{j}" : String) = v ++ ("u" ++ toString j) := by
    show (v ++ "u") ++ toString j = v ++ ("u" ++ toString j)
    rw [String.append_assoc]
  rw [h]
  refine Secp256k1FeAddSubBrick.feHN_ne_suffix2 hk ?_ ?_
  · interval_cases j <;> decide
  · intro he
    rw [hdAppend (u := "u") (v := toString j) rfl] at he
    exact absurd he (by decide)

/-- A cell-index slot name is not a half-limb slot name. -/
theorem feHN_ne_ix {u : String} {k i : Nat} (hk : k < 8) (hi : i < 12) :
    feHN u k ≠ s!"ix{i}" :=
  feHN_ne_of_preLast hk (by interval_cases i <;> decide)

/-- The `u64` staging slots of a field element inherit its first character. -/
theorem hd_uSlot {v : String} {c : Char} (h : hd v = some c) (j : Nat) :
    hd s!"{v}u{j}" = some c := hdAppend (hdAppend h)

theorem hd_ix (i : Nat) : hd s!"ix{i}" = some 'i' := hdAppend rfl
theorem hd_P : hd "P" = some 'P' := rfl
theorem hd_X : hd "X" = some 'X' := rfl
theorem hd_Y : hd "Y" = some 'Y' := rfl
theorem hd_Z : hd "Z" = some 'Z' := rfl

theorem notTmp_ix (i : Nat) : ¬ isTmpName s!"ix{i}" :=
  (headOk_of_hd (hd_ix i) (by decide)).notTmp

theorem notTmp_P : ¬ isTmpName "P" := notTmp_of_len "P" (by decide)
theorem notTmp_ZZ : ¬ isTmpName "ZZ" := notTmp_of_len "ZZ" (by decide)
theorem notTmp_CC0 : ¬ isTmpName "CC0" := notTmp_of_len "CC0" (by decide)
theorem notTmp_CC1 : ¬ isTmpName "CC1" := notTmp_of_len "CC1" (by decide)

theorem notTmp_PL (i : Nat) : ¬ isTmpName s!"PL{i}" :=
  (headOk_of_hd (hd_PL i) (by decide)).notTmp

theorem ix_inj : Function.Injective (fun i : Nat => s!"ix{i}") := by
  intro i j h
  by_contra hne
  exact idxNe "ix" hne h

theorem pl_inj : Function.Injective (fun i : Nat => s!"PL{i}") := by
  intro i j h
  by_contra hne
  exact idxNe "PL" hne h

/-- The frame pointer is not one of the modulus limb slots. -/
theorem P_ne_pl (i : Nat) : ("P" : String) ≠ s!"PL{i}" := by
  intro h
  have h1 : ("P" : String).length = (s!"PL{i}" : String).length := congrArg String.length h
  rw [show (s!"PL{i}" : String) = "PL" ++ toString i from rfl, String.length_append,
    show ("PL" : String).length = 2 from rfl, show ("P" : String).length = 1 from rfl] at h1
  omega

/-- The word reader follows an environment equality at the read name. -/
theorem envReader_of_eq {E E' : SEnvScalar} {s : String} (h : E s = E' s) :
    envReader E s = envReader E' s := by simp only [envReader, h]

/-! ## 2. A block of literal scalar assignments -/

theorem lower_lit (env : SEnvScalar) (m : Nat) :
    (semLowerSExpr env 0 (.SLit m)).isSome := rfl

/-- **A block of literal scalar assignments.** Each listed name ends bound to its
    literal, and every other non-temporary slot keeps its value. -/
theorem semScalar_litList {nm : Nat → String} {val : Nat → Nat}
    (hinj : Function.Injective nm) (hT : ∀ i, ¬ isTmpName (nm i)) :
    ∀ (is : List Nat), is.Nodup → ∀ (env : SEnvScalar),
      ∃ env', semScalar (seqAll (is.map (fun i =>
            (LowCT.RScalarSetExpr (nm i) (.SLit (val i)))))) env = some env'
        ∧ (∀ i ∈ is, env' (nm i) = some ⟨.sword 64, BitVec.ofNat 64 (val i)⟩)
        ∧ (∀ s, ¬ isTmpName s → (∀ i ∈ is, s ≠ nm i) → env' s = env s) := by
  intro is
  induction is with
  | nil => intro _ env; exact ⟨env, rfl, by simp, fun s _ _ => rfl⟩
  | cons i is ih =>
      intro hnd env
      have hins : i ∉ is := (List.nodup_cons.mp hnd).1
      obtain ⟨e1, hs1, hv1, hf1⟩ :=
        semScalar_setExpr_run (y := nm i) (e := .SLit (val i)) (lower_lit env (val i))
      obtain ⟨env', hsem, hval, hfr⟩ := ih (List.nodup_cons.mp hnd).2 e1
      refine ⟨env', ?_, ?_, ?_⟩
      · rw [List.map_cons, seqAll_step hs1]; exact hsem
      · intro i' hi'
        rcases List.mem_cons.mp hi' with heq | hi'
        · have hne : ∀ i'' ∈ is, nm i ≠ nm i'' :=
            fun i'' hi'' hc => hins (by rw [hinj hc]; exact hi'')
          rw [heq, hfr _ (hT i) hne, hv1]
          rfl
        · exact hval i' hi'
      · intro s hsT hs
        rw [hfr s hsT (fun i' hi' => hs i' (.tail _ hi')), hf1 s hsT (hs i (.head _))]

/-! ## 3. The index slots and the reduction constants -/

/-- **The twelve cell-index slots.** -/
theorem idxInit_run (env : SEnvScalar) :
    ∃ env₁, semScalar (seqAll idxInit) env = some env₁
      ∧ (∀ i, i < 12 → env₁ s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩)
      ∧ (∀ s, ¬ isTmpName s → (∀ i, i < 12 → s ≠ s!"ix{i}") → env₁ s = env s) := by
  obtain ⟨env₁, hs, hv, hf⟩ :=
    semScalar_litList (nm := fun i => s!"ix{i}") (val := fun i => i) ix_inj notTmp_ix
      (List.range 12) List.nodup_range env
  exact ⟨env₁, hs, fun i hi => hv i (List.mem_range.mpr hi),
    fun s hsT hne => hf s hsT (fun i hi => hne i (List.mem_range.mp hi))⟩

/-- **The reduction constants.** `ZZ` holds `0`, `CC0`/`CC1` the two Solinas
    coefficients, and `PL0 … PL7` the 32-bit limbs of `p`. -/
theorem constInit_run (env : SEnvScalar) :
    ∃ env₂, semScalar (seqAll constInit) env = some env₂
      ∧ env₂ "ZZ" = some ⟨.sword 64, BitVec.ofNat 64 0⟩
      ∧ env₂ "CC0" = some ⟨.sword 64, BitVec.ofNat 64 cc0⟩
      ∧ env₂ "CC1" = some ⟨.sword 64, BitVec.ofNat 64 cc1⟩
      ∧ (∀ i, i < 8 → env₂ s!"PL{i}"
            = some ⟨.sword 64, BitVec.ofNat 64 (pl32.getD i 0)⟩)
      ∧ (∀ s, ¬ isTmpName s → s ≠ "ZZ" → s ≠ "CC0" → s ≠ "CC1" →
            (∀ i, i < 8 → s ≠ s!"PL{i}") → env₂ s = env s) := by
  obtain ⟨e1, hs1, hv1, hf1⟩ :=
    semScalar_setExpr_run (y := "ZZ") (e := .SLit 0) (lower_lit env 0)
  obtain ⟨e2, hs2, hv2, hf2⟩ :=
    semScalar_setExpr_run (y := "CC0") (e := .SLit cc0) (lower_lit e1 cc0)
  obtain ⟨e3, hs3, hv3, hf3⟩ :=
    semScalar_setExpr_run (y := "CC1") (e := .SLit cc1) (lower_lit e2 cc1)
  obtain ⟨env₂, hs4, hv4, hf4⟩ :=
    semScalar_litList (nm := fun i => s!"PL{i}") (val := fun i => pl32.getD i 0)
      pl_inj notTmp_PL (List.range 8) List.nodup_range e3
  have hf4' : ∀ s, ¬ isTmpName s → (∀ i, i < 8 → s ≠ s!"PL{i}") → env₂ s = e3 s :=
    fun s hsT hne => hf4 s hsT (fun i hi => hne i (List.mem_range.mp hi))
  have hcl : constInit
      = (LowCT.RScalarSetExpr "ZZ" (.SLit 0))
        :: (LowCT.RScalarSetExpr "CC0" (.SLit cc0))
        :: (LowCT.RScalarSetExpr "CC1" (.SLit cc1))
        :: ((List.range 8).map (fun i =>
              (LowCT.RScalarSetExpr s!"PL{i}" (.SLit (pl32.getD i 0))))) := rfl
  refine ⟨env₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcl, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3]
    exact hs4
  · rw [hf4' _ notTmp_ZZ (fun i _ => neOfHd hd_ZZ (hd_PL i) (by decide)),
      hf3 _ notTmp_ZZ (by decide), hf2 _ notTmp_ZZ (by decide), hv1]
    rfl
  · rw [hf4' _ notTmp_CC0 (fun i _ => neOfHd hd_CC0 (hd_PL i) (by decide)),
      hf3 _ notTmp_CC0 (by decide), hv2]
    rfl
  · rw [hf4' _ notTmp_CC1 (fun i _ => neOfHd hd_CC1 (hd_PL i) (by decide)), hv3]
    rfl
  · exact fun i hi => hv4 i (List.mem_range.mpr hi)
  · intro s hsT hz h0 h1 hpl
    rw [hf4' s hsT hpl, hf3 s hsT h1, hf2 s hsT h0, hf1 s hsT hz]

/-- The frame pointer resolves to `a` and the twelve cell-index slots hold their
    indices. -/
structure FrameIdx {n : Nat} (E : SEnvScalar) (a : Fin n → BitVec 64) : Prop where
  /-- `P` resolves to the input point frame. -/
  frame : E "P" = some ⟨.memref n, a⟩
  /-- `ix0 … ix11` hold `0 … 11`. -/
  idx : ∀ i, i < 12 → E s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩

/-- The reduction constants hold the values `constInit` binds. -/
structure ConstVals (E : SEnvScalar) : Prop where
  /-- `ZZ` holds `0`. -/
  zz : E "ZZ" = some ⟨.sword 64, BitVec.ofNat 64 0⟩
  /-- `CC0` holds the low Solinas coefficient. -/
  lo : E "CC0" = some ⟨.sword 64, BitVec.ofNat 64 cc0⟩
  /-- `CC1` holds the high Solinas coefficient. -/
  hi : E "CC1" = some ⟨.sword 64, BitVec.ofNat 64 cc1⟩
  /-- `PL0 … PL7` hold the 32-bit limbs of `p`. -/
  pl : ∀ i, i < 8 → E s!"PL{i}" = some ⟨.sword 64, BitVec.ofNat 64 (pl32.getD i 0)⟩

/-- Two blocks run in sequence. -/
theorem semScalar_append_run {l₁ l₂ : List LowCT} {e₁ e₂ e₃ : SEnvScalar}
    (h1 : semScalar (seqAll l₁) e₁ = some e₂)
    (h2 : semScalar (seqAll l₂) e₂ = some e₃) :
    semScalar (seqAll (l₁ ++ l₂)) e₁ = some e₃ := by
  rw [Secp256k1PointOpFrontDenote.semScalar_seqAll_append, h1]
  exact h2

/-- **The index block followed by the constant block.** The frame pointer and the
    index slots are in place, the reduction constants hold their values, and every
    half-limb slot of a name with a non-underscore first character is untouched. -/
theorem idxConst_run {n : Nat} {env : SEnvScalar} {a : Fin n → BitVec 64}
    (hP : env "P" = some ⟨.memref n, a⟩) :
    ∃ E, semScalar (seqAll (idxInit ++ constInit)) env = some E
      ∧ FrameIdx E a ∧ ConstVals E
      ∧ (∀ (fe : String) (c : Char), hd fe = some c → c ≠ '_' →
          ∀ k, k < 8 → E (feHN fe k) = env (feHN fe k)) := by
  obtain ⟨E1, hs1, hix1, hfr1⟩ := idxInit_run env
  obtain ⟨E2, hs2, hZZ2, hC02, hC12, hPL2, hfr2⟩ := constInit_run E1
  refine ⟨E2, semScalar_append_run hs1 hs2, ⟨?_, ?_⟩, ⟨hZZ2, hC02, hC12, hPL2⟩, ?_⟩
  · rw [hfr2 "P" notTmp_P (by decide) (by decide) (by decide) (fun i _ => P_ne_pl i),
      hfr1 "P" notTmp_P (fun i _ => neOfHd hd_P (hd_ix i) (by decide))]
    exact hP
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

/-! ## 4. One coordinate load -/


/-- The names a `loadField` block into `fe` leaves alone: every non-temporary name
    outside `fe`'s four `u64` staging slots and its eight half-limb slots. -/
def LoadFrame (fe : String) (E' E : SEnvScalar) : Prop :=
  ∀ s, ¬ isTmpName s → (∀ j, j < 4 → s ≠ s!"{fe}u{j}") →
    (∀ k, k < 8 → s ≠ feHN fe k) → E' s = E s

/-- A name whose first character differs from the loaded element's survives a load. -/
theorem keep_load {E E' : SEnvScalar} {fe s : String} {c d : Char}
    (hfr : LoadFrame fe E' E) (hdfe : hd fe = some d) (hsT : ¬ isTmpName s)
    (hs : hd s = some c) (hcd : c ≠ d) : E' s = E s :=
  hfr s hsT (fun j _ => neOfHd hs (hd_uSlot hdfe j) hcd)
    (fun k _ => neOfHd hs (hd_feHN hdfe k) hcd)

/-- A half-limb slot of a different field element survives a load. -/
theorem feHN_keep_load {E E' : SEnvScalar} {fe g : String} {k : Nat}
    (hfr : LoadFrame g E' E) (hnt : ¬ isTmpName (feHN fe k)) (hk : k < 8)
    (hne : fe ≠ g) : E' (feHN fe k) = E (feHN fe k) :=
  hfr _ hnt (fun _ hj => feHN_ne_uSlot hk hj)
    (fun _ hk' he => hne (feHN_inj hk hk' he).1)

/-- **One coordinate load out of the point frame.** The eight half-limb slots of `fe`
    carry the halves of the four frame cells at offset `o`, and the frame pointer and
    the index slots come through unchanged. -/
theorem loadCoord_run {n o : Nat} {a : Fin n → BitVec 64} {E : SEnvScalar}
    {fe : String} {c : Char} (hfe : fe.toList = [c]) (hcU : c ≠ '_') (hci : c ≠ 'i')
    (hcP : c ≠ 'P') (ho : o + 3 < 12) (hFI : FrameIdx E a) :
    ∃ E', semScalar (seqAll (loadField 96 "P" o fe)) E = some E'
      ∧ (∀ j, j < 4 → E' s!"{fe}h{2 * j}"
            = some ⟨.sword 64, memGetDyn a (BitVec.ofNat 64 (o + j)).toNat
                &&& BitVec.ofNat 64 mask32⟩)
      ∧ (∀ j, j < 4 → E' s!"{fe}h{2 * j + 1}"
            = some ⟨.sword 64, memGetDyn a (BitVec.ofNat 64 (o + j)).toNat
                >>> (BitVec.ofNat 64 32).toNat⟩)
      ∧ FrameIdx E' a ∧ LoadFrame fe E' E := by
  have hdfe : hd fe = some c := by
    show fe.toList.head? = some c
    rw [hfe]
    rfl
  obtain ⟨E', hs, hlo, hhi, hfr⟩ :=
    semScalar_loadField (fw := 96) (o := o) (arrN := "P") (fe := fe) (a := a)
      (iw := fun j => BitVec.ofNat 64 (o + j)) (cf := c) (rf := []) (ca := 'P') (ra := [])
      hfe hcU hci rfl (Ne.symm hcP) hFI.frame (fun j hj => hFI.idx (o + j) (by omega))
  exact ⟨E', hs, hlo, hhi,
    ⟨(keep_load hfr hdfe notTmp_P hd_P (Ne.symm hcP)).trans hFI.frame,
     fun i hi => (keep_load hfr hdfe (notTmp_ix i) (hd_ix i) (Ne.symm hci)).trans
       (hFI.idx i hi)⟩,
    hfr⟩

/-- **The reduction constants come through the three coordinate loads.** -/
theorem constVals_load3 {E2 E3 E4 E5 : SEnvScalar}
    (h3 : LoadFrame "X" E3 E2) (h4 : LoadFrame "Y" E4 E3) (h5 : LoadFrame "Z" E5 E4)
    (hC : ConstVals E2) : ConstVals E5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h5 "ZZ" notTmp_ZZ (fun j hj => by interval_cases j <;> decide)
        (fun k hk => Ne.symm (feHN_ne_short hk hd_Z (by decide))),
      keep_load h4 hd_Y notTmp_ZZ hd_ZZ (by decide),
      keep_load h3 hd_X notTmp_ZZ hd_ZZ (by decide)]
    exact hC.zz
  · rw [keep_load h5 hd_Z notTmp_CC0 hd_CC0 (by decide),
      keep_load h4 hd_Y notTmp_CC0 hd_CC0 (by decide),
      keep_load h3 hd_X notTmp_CC0 hd_CC0 (by decide)]
    exact hC.lo
  · rw [keep_load h5 hd_Z notTmp_CC1 hd_CC1 (by decide),
      keep_load h4 hd_Y notTmp_CC1 hd_CC1 (by decide),
      keep_load h3 hd_X notTmp_CC1 hd_CC1 (by decide)]
    exact hC.hi
  · intro i hi
    rw [keep_load h5 hd_Z (notTmp_PL i) (hd_PL i) (by decide),
      keep_load h4 hd_Y (notTmp_PL i) (hd_PL i) (by decide),
      keep_load h3 hd_X (notTmp_PL i) (hd_PL i) (by decide)]
    exact hC.pl i hi

/-! ## 5. The half-limb readout of a loaded coordinate -/

/-- The little-endian value of the four `u64` cells at offset `o`. -/
def cellVal {n : Nat} (a : Fin n → BitVec 64) (o : Nat) : Nat :=
  (memGetDyn a (o + 0)).toNat + 2 ^ 64 * (memGetDyn a (o + 1)).toNat
    + 2 ^ 128 * (memGetDyn a (o + 2)).toNat + 2 ^ 192 * (memGetDyn a (o + 3)).toNat

/-- **A loaded coordinate's readout is its frame value.** -/
theorem feVal_load {o n : Nat} {fe : String} {a : Fin n → BitVec 64} {E : SEnvScalar}
    (ho : o + 3 < 2 ^ 64)
    (hlo : ∀ j, j < 4 → E s!"{fe}h{2 * j}" = some ⟨.sword 64,
        memGetDyn a (BitVec.ofNat 64 (o + j)).toNat &&& BitVec.ofNat 64 mask32⟩)
    (hhi : ∀ j, j < 4 → E s!"{fe}h{2 * j + 1}" = some ⟨.sword 64,
        memGetDyn a (BitVec.ofNat 64 (o + j)).toNat >>> (BitVec.ofNat 64 32).toNat⟩) :
    feVal E fe = cellVal a o := by
  have hfv := feVal_of_halves hlo hhi
  have e : ∀ j, j < 4 → (BitVec.ofNat 64 (o + j)).toNat = o + j :=
    fun j hj => ofNat_toNat (by omega)
  rw [hfv, cellVal, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
    e 3 (by norm_num)]

/-- **A loaded coordinate's half-limbs are below `2^32`.** -/
theorem limbs_load {n : Nat} {fe : String} {a : Fin n → BitVec 64}
    {iw : Nat → BitVec 64} {E : SEnvScalar}
    (hlo : ∀ j, j < 4 → E s!"{fe}h{2 * j}"
        = some ⟨.sword 64, memGetDyn a (iw j).toNat &&& BitVec.ofNat 64 mask32⟩)
    (hhi : ∀ j, j < 4 → E s!"{fe}h{2 * j + 1}"
        = some ⟨.sword 64, memGetDyn a (iw j).toNat >>> (BitVec.ofNat 64 32).toNat⟩) :
    ∀ k, k < 8 → (envReader E (feHN fe k)).toNat < 2 ^ 32 := by
  have hL : ∀ j, j < 4 → (envReader E s!"{fe}h{2 * j}").toNat < 2 ^ 32 := by
    intro j hj
    rw [envReader_of_bound (hlo j hj), half_lo]
    exact Nat.mod_lt _ (by norm_num)
  have hH : ∀ j, j < 4 → (envReader E s!"{fe}h{2 * j + 1}").toNat < 2 ^ 32 := by
    intro j hj
    rw [envReader_of_bound (hhi j hj), toNat_ofNat_32, half_hi]
    have hb : (memGetDyn a (iw j).toNat).toNat < 2 ^ 64 := BitVec.isLt _
    refine Nat.div_lt_of_lt_mul ?_
    rw [show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 from by norm_num]
    exact hb
  intro k hk
  interval_cases k
  · exact hL 0 (by norm_num)
  · exact hH 0 (by norm_num)
  · exact hL 1 (by norm_num)
  · exact hH 1 (by norm_num)
  · exact hL 2 (by norm_num)
  · exact hH 2 (by norm_num)
  · exact hL 3 (by norm_num)
  · exact hH 3 (by norm_num)

/-- The half-limb readout depends only on the eight half-limb slots. -/
theorem feVal_congr {E E' : SEnvScalar} {fe : String}
    (h : ∀ k, k < 8 → E' (feHN fe k) = E (feHN fe k)) : feVal E' fe = feVal E fe := by
  rw [feVal_eq_accN, feVal_eq_accN]
  exact accN_congr 8 (fun k hk => by rw [envReader_of_eq (h k hk)])

/-- A field element whose eight half-limb slots read `0` has readout `0`. -/
theorem feVal_eq_zero {E : SEnvScalar} {fe : String}
    (h : ∀ k, k < 8 → envReader E (feHN fe k) = 0) : feVal E fe = 0 := by
  rw [feVal_eq_accN,
    accN_congr (w := fun _ => 0) 8 (fun k hk => by rw [h k hk]; rfl)]
  rfl

/-! ## 6. The prologue -/

/-- The index slots, the reduction constants and the three coordinate loads that
    open `Secp256k1PointOpFront.jacDblBody`. -/
def jacDblPrologue : List LowCT :=
  idxInit ++ constInit ++ loadField 96 "P" 0 "X" ++ loadField 96 "P" 4 "Y"
    ++ loadField 96 "P" 8 "Z"

/-- `jacDblBody` is the prologue followed by the schedule and the three stores. -/
theorem jacDblBody_eq_prologue_append :
    jacDblBody = seqAll (jacDblPrologue ++ (runSchedule jacDblSchedule
      ++ storeField 96 0 "Xp" ++ storeField 96 4 "Yp" ++ storeField 96 8 "Zp")) := by
  simp only [jacDblBody, jacDblPrologue, List.append_assoc]

/-- **Entry conditions of the `jacDbl` prologue.** The frame pointer `P` holds the
    memref `a`, whose cells `0..3`, `4..7` and `8..11` carry the coordinates
    `X`, `Y` and `Z` little-endian; every schedule-name half-limb slot reads `0`;
    and the three coordinates are canonical residues below `p`. -/
structure PrologueEntry {n : Nat} (env : SEnvScalar) (a : Fin n → BitVec 64)
    (X Y Z : Nat) : Prop where
  /-- `P` resolves to the input point frame. -/
  frame : env "P" = some ⟨.memref n, a⟩
  /-- Cells `0..3` carry `X`. -/
  coordX : cellVal a 0 = X
  /-- Cells `4..7` carry `Y`. -/
  coordY : cellVal a 4 = Y
  /-- Cells `8..11` carry `Z`. -/
  coordZ : cellVal a 8 = Z
  /-- No schedule-name half-limb slot is bound on entry. -/
  zeroed : ∀ fe, schedNameB fe = true → ∀ k, k < 8 → envReader env (feHN fe k) = 0
  /-- `X` is a canonical residue. -/
  ltX : X < pNat
  /-- `Y` is a canonical residue. -/
  ltY : Y < pNat
  /-- `Z` is a canonical residue. -/
  ltZ : Z < pNat

theorem pNat_pos : 0 < pNat := by norm_num [Secp256k1FeMulFront.pNat]

theorem dblEnv0_lt {X Y Z : Nat} (hX : X < pNat) (hY : Y < pNat) (hZ : Z < pNat)
    (fe : String) : dblEnv0 X Y Z fe < pNat := by
  simp only [dblEnv0]
  split_ifs <;> first | exact hX | exact hY | exact hZ | exact pNat_pos

/-- **The schedule-name readout is `dblEnv0`.** The three coordinates carry their
    frame values and every other schedule name reads `0`. -/
theorem sched_value {E : SEnvScalar} {X Y Z : Nat}
    (hvX : feVal E "X" = X) (hvY : feVal E "Y" = Y) (hvZ : feVal E "Z" = Z)
    (hzero : ∀ fe, schedNameB fe = true → fe ≠ "X" → fe ≠ "Y" → fe ≠ "Z" →
        ∀ k, k < 8 → envReader E (feHN fe k) = 0) :
    ∀ fe, schedNameB fe = true → feVal E fe = dblEnv0 X Y Z fe := by
  intro fe hfe
  by_cases hX : fe = "X"
  · subst hX; rw [hvX]; simp [dblEnv0]
  by_cases hY : fe = "Y"
  · subst hY; rw [hvY]; simp [dblEnv0]
  by_cases hZ : fe = "Z"
  · subst hZ; rw [hvZ]; simp [dblEnv0]
  rw [feVal_eq_zero (hzero fe hfe hX hY hZ)]
  simp [dblEnv0, hX, hY, hZ]

/-- **Every schedule-name half-limb is below `2^32`.** -/
theorem sched_limbs {E : SEnvScalar}
    (hbX : ∀ k, k < 8 → (envReader E (feHN "X" k)).toNat < 2 ^ 32)
    (hbY : ∀ k, k < 8 → (envReader E (feHN "Y" k)).toNat < 2 ^ 32)
    (hbZ : ∀ k, k < 8 → (envReader E (feHN "Z" k)).toNat < 2 ^ 32)
    (hzero : ∀ fe, schedNameB fe = true → fe ≠ "X" → fe ≠ "Y" → fe ≠ "Z" →
        ∀ k, k < 8 → envReader E (feHN fe k) = 0) :
    ∀ fe, schedNameB fe = true → ∀ k, k < 8 →
      (envReader E (feHN fe k)).toNat < 2 ^ 32 := by
  intro fe hfe k hk
  by_cases hX : fe = "X"
  · subst hX; exact hbX k hk
  by_cases hY : fe = "Y"
  · subst hY; exact hbY k hk
  by_cases hZ : fe = "Z"
  · subst hZ; exact hbZ k hk
  rw [hzero fe hfe hX hY hZ k hk]
  simp

/-- **The brick scope from the constants and a canonicality bound.** The form
    that does not mention a particular initial environment: the four constant
    slots come from `ConstVals`, the limb bounds and the canonicality of every
    schedule name are hypotheses. -/
theorem brickScope_ofLt {E : SEnvScalar} (hC : ConstVals E)
    (hlimb : ∀ fe, schedNameB fe = true → ∀ k, k < 8 →
        (envReader E (feHN fe k)).toNat < 2 ^ 32)
    (hlt : ∀ fe, schedNameB fe = true → feVal E fe < pNat) : BrickScope E := by
  refine ⟨?_, ?_, ?_, ?_, hlimb, hlt⟩
  · rw [envReader_of_bound hC.zz]; exact ofNat_toNat (by norm_num)
  · rw [envReader_of_bound hC.lo]
    exact ofNat_toNat (by norm_num [Secp256k1FeMulFront.cc0])
  · rw [envReader_of_bound hC.hi]
    exact ofNat_toNat (by norm_num [Secp256k1FeMulFront.cc1])
  · intro i hi
    rw [envReader_of_bound (hC.pl i hi)]
    exact ofNat_toNat (lt_trans (pl32_lt i) (by norm_num))

/-- **The brick scope from the constant values and the schedule-name readout.**
    `brickScope_ofLt` at `dblEnv0`. -/
theorem brickScope_of {E : SEnvScalar} {X Y Z : Nat} (hC : ConstVals E)
    (hlimb : ∀ fe, schedNameB fe = true → ∀ k, k < 8 →
        (envReader E (feHN fe k)).toNat < 2 ^ 32)
    (hval : ∀ fe, schedNameB fe = true → feVal E fe = dblEnv0 X Y Z fe)
    (hX : X < pNat) (hY : Y < pNat) (hZ : Z < pNat) : BrickScope E :=
  brickScope_ofLt hC hlimb (fun fe hfe => by
    rw [hval fe hfe]; exact dblEnv0_lt hX hY hZ fe)

/-- **The `jacDbl` prologue runs into the brick scope at `dblEnv0`.** From an
    entry environment satisfying `PrologueEntry`, the index slots, the reduction
    constants and the three coordinate loads leave an environment in
    `Secp256k1FeAddSubBrick.BrickScope` whose schedule-name half-limb readout is
    `Secp256k1PointOpCompositional.dblEnv0 X Y Z`. -/
theorem jacDblPrologue_run {n : Nat} (env : SEnvScalar) (a : Fin n → BitVec 64)
    (X Y Z : Nat) (hE : PrologueEntry env a X Y Z) :
    ∃ env₁, semScalar (seqAll jacDblPrologue) env = some env₁
      ∧ BrickScope env₁
      ∧ ∀ fe, schedNameB fe = true → feVal env₁ fe = dblEnv0 X Y Z fe := by
  obtain ⟨E2, hs2, hFI2, hCV2, hslot2⟩ := idxConst_run hE.frame
  obtain ⟨E3, hs3, hloX, hhiX, hFI3, hfr3⟩ :=
    loadCoord_run (o := 0) (fe := "X") (c := 'X') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI2
  obtain ⟨E4, hs4, hloY, hhiY, hFI4, hfr4⟩ :=
    loadCoord_run (o := 4) (fe := "Y") (c := 'Y') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI3
  obtain ⟨E5, hs5, hloZ, hhiZ, -, hfr5⟩ :=
    loadCoord_run (o := 8) (fe := "Z") (c := 'Z') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI4
  have hrun : semScalar (seqAll jacDblPrologue) env = some E5 :=
    semScalar_append_run (semScalar_append_run (semScalar_append_run hs2 hs3) hs4) hs5
  have hXkeep : ∀ k, k < 8 → E5 (feHN "X" k) = E3 (feHN "X" k) := by
    intro k hk
    have nt : ¬ isTmpName (feHN "X" k) :=
      (headOk_of_hd (hd_feHN hd_X k) (by decide)).notTmp
    rw [feHN_keep_load hfr5 nt hk (by decide), feHN_keep_load hfr4 nt hk (by decide)]
  have hYkeep : ∀ k, k < 8 → E5 (feHN "Y" k) = E4 (feHN "Y" k) := fun k hk =>
    feHN_keep_load hfr5 ((headOk_of_hd (hd_feHN hd_Y k) (by decide)).notTmp) hk
      (by decide)
  have hother : ∀ fe, schedNameB fe = true → fe ≠ "X" → fe ≠ "Y" → fe ≠ "Z" →
      ∀ k, k < 8 → envReader E5 (feHN fe k) = 0 := by
    intro fe hfe hX hY hZ k hk
    obtain ⟨c, hdc, _, hc'⟩ := hd_of_schedName hfe
    have nt : ¬ isTmpName (feHN fe k) := (headOk_of_hd (hd_feHN hdc k) hc').notTmp
    have hchain : E5 (feHN fe k) = env (feHN fe k) := by
      rw [feHN_keep_load hfr5 nt hk hZ, feHN_keep_load hfr4 nt hk hY,
        feHN_keep_load hfr3 nt hk hX, hslot2 fe c hdc hc' k hk]
    rw [envReader_of_eq hchain]
    exact hE.zeroed fe hfe k hk
  have hvalX : feVal E5 "X" = X := by
    rw [feVal_congr hXkeep, feVal_load (by norm_num) hloX hhiX]
    exact hE.coordX
  have hvalY : feVal E5 "Y" = Y := by
    rw [feVal_congr hYkeep, feVal_load (by norm_num) hloY hhiY]
    exact hE.coordY
  have hvalZ : feVal E5 "Z" = Z := by
    rw [feVal_load (by norm_num) hloZ hhiZ]
    exact hE.coordZ
  have hval := sched_value hvalX hvalY hvalZ hother
  have hlimb := sched_limbs (E := E5)
    (fun k hk => by
      rw [envReader_of_eq (hXkeep k hk)]
      exact limbs_load (a := a) (iw := fun j => BitVec.ofNat 64 (0 + j)) hloX hhiX k hk)
    (fun k hk => by
      rw [envReader_of_eq (hYkeep k hk)]
      exact limbs_load (a := a) (iw := fun j => BitVec.ofNat 64 (4 + j)) hloY hhiY k hk)
    (limbs_load (a := a) (iw := fun j => BitVec.ofNat 64 (8 + j)) hloZ hhiZ) hother
  exact ⟨E5, hrun,
    brickScope_of (constVals_load3 hfr3 hfr4 hfr5 hCV2) hlimb hval
      hE.ltX hE.ltY hE.ltZ,
    hval⟩

/-- **The `jacDbl` prologue's value tie, in hypothesis form.** The form the
    decomposition of `jacDblBody`'s waist semantics hands over: whatever
    environment the prologue runs to lies in `BrickScope` and holds `dblEnv0`. -/
theorem jacDblPrologue_value {n : Nat} (env env₁ : SEnvScalar) (a : Fin n → BitVec 64)
    (X Y Z : Nat) (hE : PrologueEntry env a X Y Z)
    (hSem : semScalar (seqAll jacDblPrologue) env = some env₁) :
    BrickScope env₁ ∧ ∀ fe, schedNameB fe = true → feVal env₁ fe = dblEnv0 X Y Z fe := by
  obtain ⟨e, hs, hsc, hv⟩ := jacDblPrologue_run env a X Y Z hE
  rw [hSem] at hs
  obtain rfl := Option.some.inj hs
  exact ⟨hsc, hv⟩

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue
