/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedCells
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickReduce

/-!
# The single-brick framed value step of the secp256k1 doubling body

`Secp256k1PointOpFrontFramed.emitFOpFramed` re-tiles one `dbl-2009-l` field-op
brick so its two operands are loaded from frame slots, the shared brick body runs,
and the eight result half-limbs are stored back into the output frame slot. This
module carries the frame-slot analogue of the SSA-name brick value step
`Secp256k1FeMulBrickReduce.mulBrickValue_of_heads`: running one `emitFOpFramed`
brick from a state whose frame satisfies `FrameSlots` updates the frame so
`FrameSlots` holds again with only the output slot changed to the brick's
base-field operation value.

## Main results

* `emitFOpFramed_mul_value`, `emitFOpFramed_add_value`, `emitFOpFramed_sub_value`
  — one `emitFOpFramed` brick moves the output frame slot by one `fm` / `fa` /
  `fs` base-field operation on the operand slot values, leaving the other slots
  unchanged.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedBrickValue

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv mask32 pNat pl32 genSub)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (feH feMulHalves feAddHalves feSubHalves FOp constInit loadField fm fa fs)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody
  (env_seqAll_frame Extends suffixClosed_extends extends_self)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickFrame
  (WritesIn SuffixClosed feMulHalves_writes feAddHalves_writes feSubHalves_writes)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal semScalar_seqAll_append semScalar_seqAll_cons)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered (HeadOk)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (hd hdAppend neOfHd OutOf outOf_of_hd sibOut headOk_of_hd nameAssoc hd_ZZ hd_PL
   hd_A hd_S hd_R hd_feHN feHN feHN_eq feVal_eq_accN accN accN_congr ofNat_toNat sib2Ne subNe
   pfxNe hd_CC0 hd_CC1 feH_len feH_getBang feH_getD feH_getD_ge rNamesOf_getBang
   feAddHalves_sem_gen feSubHalves_sem_gen feAddHalves_names feSubHalves_names
   take_getBang genAdd_name pmNamesOf pmNamesOf_len genSub_len
   stepAt splitApp semScalar_seqAll_eq_semList)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy (semList semScalar_setExpr_eq)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickReduce
  (ConstsAt genMulSpec_holds feMulHalves_sem_gen feMulHalves_names GenMulSpec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (semScalar_loadField feVal_of_loadField semScalar_setExpr_run envReader_of_bound
   half_lo half_hi seqAll_step slot_inj)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue (constInit_run notTmp_ix lower_lit ix_inj)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedCells
  (slotVal FrameSlots frameSlots_store loadFieldF_slotVal)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
  (idxCells storeFieldTo brickFn emitFOpFramed)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue (oh_bridge)

/-! ## 1. Numeric facts -/

/-- The secp256k1 field prime is below `2 ^ 256`. -/
theorem pNat_lt_pow256 : pNat < 2 ^ 256 := by norm_num [pNat]

/-! ## 2. The per-brick index block, as values -/

/-- **`idxCells` binds each cell index to its own number.** Even with a repeated
    cell (a squaring brick's two operands share a slot) every listed `ix{c}` slot
    ends holding `c`, and every non-`ix{c}` slot is unchanged. -/
theorem idxCells_run : ∀ (cells : List Nat) (env : SEnvScalar),
    ∃ E, semScalar (seqAll (idxCells cells)) env = some E
      ∧ (∀ c ∈ cells, E s!"ix{c}" = some ⟨.sword 64, BitVec.ofNat 64 c⟩)
      ∧ (∀ s, ¬ isTmpName s → (∀ c ∈ cells, s ≠ s!"ix{c}") → E s = env s) := by
  intro cells
  induction cells with
  | nil => intro env; exact ⟨env, rfl, by simp, fun s _ _ => rfl⟩
  | cons c cs ih =>
      intro env
      obtain ⟨e1, hs1, hv1, hf1⟩ :=
        semScalar_setExpr_run (y := s!"ix{c}") (e := .SLit c) (lower_lit env c)
      obtain ⟨E, hsE, hvE, hfE⟩ := ih e1
      refine ⟨E, ?_, ?_, ?_⟩
      · rw [show idxCells (c :: cs)
              = LowCT.RScalarSetExpr s!"ix{c}" (.SLit c) :: idxCells cs from rfl,
          seqAll_step hs1]
        exact hsE
      · intro c0 hc0
        rcases List.mem_cons.mp hc0 with heq | hmem
        · subst heq
          by_cases hin : c0 ∈ cs
          · exact hvE c0 hin
          · rw [hfE s!"ix{c0}" (notTmp_ix c0)
                (fun c' hc' => fun he => hin ((ix_inj he) ▸ hc')), hv1]
            rfl
        · exact hvE c0 hmem
      · intro s hsnt hne
        rw [hfE s hsnt (fun c' hc' => hne c' (List.mem_cons_of_mem c hc')),
          hf1 s hsnt (hne c (List.mem_cons.mpr (Or.inl rfl)))]

/-! ## 3. The per-brick output copy block, as values -/

/-- **The output copy block, read back as slot bindings.** From a successful run
    of the eight `{pfx}Oh{k} := {rn k}` copies, each `{pfx}Oh{k}` ends holding the
    `u64` value of `{rn k}` at the entry, and every non-`{pfx}Oh` slot is
    unchanged. The run's success is enough — a copy of an unbound source would
    decline. -/
theorem framedCopy_run (pfx : String) (rn : Nat → String)
    (hOnt : ∀ k, k < 8 → ¬ isTmpName s!"{pfx}Oh{k}")
    (hOinj : ∀ k j, k < 8 → j < 8 → k ≠ j → s!"{pfx}Oh{k}" ≠ s!"{pfx}Oh{j}")
    (hrnnt : ∀ k, k < 8 → ¬ isTmpName (rn k))
    (hrne : ∀ k j, k < 8 → j < 8 → rn k ≠ s!"{pfx}Oh{j}")
    (Eb : SEnvScalar) :
    ∀ n, n ≤ 8 → ∀ E, semScalar (seqAll ((List.range n).map
        (fun k => LowCT.RScalarSetExpr s!"{pfx}Oh{k}" (sv (rn k))))) Eb = some E →
      (∀ k, k < n → E s!"{pfx}Oh{k}" = some ⟨.sword 64, envReader Eb (rn k)⟩)
      ∧ (∀ s, ¬ isTmpName s → (∀ j, j < n → s ≠ s!"{pfx}Oh{j}") → E s = Eb s) := by
  intro n
  induction n with
  | zero =>
      intro _ E hsem
      obtain rfl : E = Eb := by simpa using (Option.some.inj hsem).symm
      exact ⟨fun k hk => absurd hk (by omega), fun _ _ _ => rfl⟩
  | succ n ih =>
      intro hle E hsem
      have hsplit : (List.range (n + 1)).map
            (fun k => LowCT.RScalarSetExpr s!"{pfx}Oh{k}" (sv (rn k)))
          = (List.range n).map (fun k => LowCT.RScalarSetExpr s!"{pfx}Oh{k}" (sv (rn k)))
            ++ [LowCT.RScalarSetExpr s!"{pfx}Oh{n}" (sv (rn n))] := by
        rw [List.range_succ, List.map_append]; rfl
      rw [hsplit, semScalar_seqAll_append] at hsem
      obtain ⟨E1, hpre, htail⟩ :=
        Option.bind_eq_some_iff.mp hsem
      have hlast : semScalar (LowCT.RScalarSetExpr s!"{pfx}Oh{n}" (sv (rn n))) E1 = some E := by
        rw [show seqAll [LowCT.RScalarSetExpr s!"{pfx}Oh{n}" (sv (rn n))]
              = LowCT.RScalarSetExpr s!"{pfx}Oh{n}" (sv (rn n)) from rfl] at htail
        exact htail
      obtain ⟨hval, hkeep⟩ := ih (by omega) E1 hpre
      obtain ⟨hat, hoff⟩ := semScalar_setExpr_eq hlast
      have hrnval : envReader E1 (rn n) = envReader Eb (rn n) := by
        simp only [envReader,
          hkeep (rn n) (hrnnt n (by omega)) (fun j hj => hrne n j (by omega) (by omega))]
      refine ⟨?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · rw [hoff s!"{pfx}Oh{k}" (hOnt k (by omega)) (hOinj k n (by omega) (by omega) (by omega))]
          exact hval k h
        · subst h
          rw [hat]
          simp only [sv, SExpr.evalBV, hrnval]
      · intro s hsnt hne
        rw [hoff s hsnt (hne n (by omega)), hkeep s hsnt (fun j hj => hne j (by omega))]

/-! ## 4. One operand load, as a value and a limb bound -/

/-- `w &&& (2^32-1)` is below `2 ^ 32`. -/
theorem and_mask32_lt (w : BitVec 64) : (w &&& BitVec.ofNat 64 mask32).toNat < 2 ^ 32 := by
  rw [half_lo w]; exact Nat.mod_lt _ (by norm_num)

/-- `w >>> 32` is below `2 ^ 32`. -/
theorem shr32_lt (w : BitVec 64) :
    (w >>> (BitVec.ofNat 64 32).toNat).toNat < 2 ^ 32 := by
  rw [show (BitVec.ofNat 64 32).toNat = 32 from ofNat_toNat (by norm_num), half_hi w]
  have hlt : w.toNat < 2 ^ 32 * 2 ^ 32 := by
    have := w.isLt; simpa [show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 from by norm_num] using this
  exact Nat.div_lt_of_lt_mul hlt

/-- **One operand load carries the slot value and 32-bit limbs.** Loading frame
    slot `s` into `fe` leaves `feVal fe` equal to `slotVal arr s`, every one of
    `fe`'s eight half-limb slots below `2 ^ 32`, and every slot outside `fe`'s
    `u`/`h` tags unchanged. -/
theorem loadOperand {fw s N : Nat} {frame fe : String} {cf ca : Char} {rf ra : List Char}
    {arr : Fin N → BitVec 64} {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i')
    (harr : frame.toList = ca :: ra) (hca : ca ≠ cf) (hcap : 4 * s + 4 ≤ 2 ^ 64)
    (ha : env frame = some ⟨.memref N, arr⟩)
    (hix : ∀ j, j < 4 → env s!"ix{4 * s + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * s + j)⟩) :
    ∃ env', semScalar (seqAll (loadField fw frame (4 * s) fe)) env = some env'
      ∧ feVal env' fe = slotVal arr s
      ∧ (∀ k, k < 8 → (envReader env' (feHN fe k)).toNat < 2 ^ 32)
      ∧ (∀ t, ¬ isTmpName t → (∀ j, j < 4 → t ≠ s!"{fe}u{j}") →
            (∀ k, k < 8 → t ≠ s!"{fe}h{k}") → env' t = env t) := by
  obtain ⟨e1, hs1, hval⟩ := loadFieldF_slotVal hfe hcf hci harr hca hcap ha hix
  obtain ⟨e2, hs2, hlo, hhi, hfr⟩ :=
    semScalar_loadField (fw := fw) (o := 4 * s) (iw := fun j => BitVec.ofNat 64 (4 * s + j))
      hfe hcf hci harr hca ha hix
  obtain rfl : e1 = e2 := Option.some.inj (hs1 ▸ hs2)
  refine ⟨e1, hs1, hval, ?_, hfr⟩
  intro k hk
  obtain ⟨j, hj, rfl | rfl⟩ : ∃ j, j < 4 ∧ (k = 2 * j ∨ k = 2 * j + 1) :=
    ⟨k / 2, by omega, by omega⟩
  · rw [← feHN_eq, envReader_of_bound (hlo j hj)]; exact and_mask32_lt _
  · rw [← feHN_eq, envReader_of_bound (hhi j hj)]; exact shr32_lt _

/-! ## 5. Name inequalities for the brick prefix -/

/-- `ix{c}` has first character `'i'`. -/
theorem hd_ix (c : Nat) : hd s!"ix{c}" = some 'i' := hdAppend rfl

/-- Two half-limb-style slots of sibling field elements under a common prefix
    differ when the sub-prefixes' first characters differ. -/
theorem sibHNe {pfx t u : String} {ct cu : Char} (ht : hd t = some ct) (hu : hd u = some cu)
    (hne : ct ≠ cu) (k j : Nat) : s!"{pfx ++ t}h{k}" ≠ s!"{pfx ++ u}h{j}" := by
  have e1 : s!"{pfx ++ t}h{k}" = pfx ++ t ++ ("h" ++ toString k) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx ++ u}h{j}" = pfx ++ u ++ ("h" ++ toString j) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e1, e2]; exact sib2Ne ht hu hne _ _

/-- A half-limb slot and a `u`-word slot of sibling field elements differ. -/
theorem sibHUNe {pfx t u : String} {ct cu : Char} (ht : hd t = some ct) (hu : hd u = some cu)
    (hne : ct ≠ cu) (k j : Nat) : s!"{pfx ++ t}h{k}" ≠ s!"{pfx ++ u}u{j}" := by
  have e1 : s!"{pfx ++ t}h{k}" = pfx ++ t ++ ("h" ++ toString k) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx ++ u}u{j}" = pfx ++ u ++ ("u" ++ toString j) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e1, e2]; exact sib2Ne ht hu hne _ _

/-! ## 6. The shared brick prefix, as values -/

/-- **The constant/index/operand-load prefix of a framed brick, read back as
    values.** Running the per-brick index block, the reduction constants and the
    two operand frame loads leaves the frame pointer in place, the reduction
    constants at their values, each operand field element holding its frame slot
    value in 32-bit limbs, and the output-slot cell indices bound. -/
theorem framedPrefix {N fw : Nat} {slotOf : String → Nat} {frame : String} (idx : Nat)
    (a b o : String) {ca : Char} {ra : List Char}
    (harr : frame.toList = ca :: ra) (hcaTmp : ¬ isTmpName frame)
    (hcaf : ca ≠ 'f') (hcai : ca ≠ 'i') (hcaZ : ca ≠ 'Z') (hcaC : ca ≠ 'C') (hcaP : ca ≠ 'P')
    {arr : Fin N → BitVec 64} {env E3 : SEnvScalar}
    (hAcap : 4 * slotOf a + 4 ≤ 2 ^ 64) (hBcap : 4 * slotOf b + 4 ≤ 2 ^ 64)
    (hF : env frame = some ⟨.memref N, arr⟩)
    (hpre : semScalar (seqAll (idxCells
        ((List.range 4).map (4 * slotOf a + ·) ++ (List.range 4).map (4 * slotOf b + ·)
          ++ (List.range 4).map (4 * slotOf o + ·))
        ++ constInit
        ++ loadField fw frame (4 * slotOf a) (s!"fop{idx}" ++ "A")
        ++ loadField fw frame (4 * slotOf b) (s!"fop{idx}" ++ "B"))) env = some E3) :
    E3 frame = some ⟨.memref N, arr⟩
      ∧ ConstsAt E3
      ∧ feVal E3 (s!"fop{idx}" ++ "A") = slotVal arr (slotOf a)
      ∧ feVal E3 (s!"fop{idx}" ++ "B") = slotVal arr (slotOf b)
      ∧ (∀ k, k < 8 → (envReader E3 (feHN (s!"fop{idx}" ++ "A") k)).toNat < 2 ^ 32)
      ∧ (∀ k, k < 8 → (envReader E3 (feHN (s!"fop{idx}" ++ "B") k)).toNat < 2 ^ 32)
      ∧ (∀ j, j < 4 →
          E3 s!"ix{4 * slotOf o + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf o + j)⟩) := by
  set pfx := s!"fop{idx}" with hpfx
  set cells := (List.range 4).map (4 * slotOf a + ·) ++ (List.range 4).map (4 * slotOf b + ·)
    ++ (List.range 4).map (4 * slotOf o + ·) with hcells
  -- head facts
  have hdfe : ∀ w : String, hd (pfx ++ w) = some 'f' :=
    fun w => hdAppend (hdAppend (rfl : hd "fop" = some 'f'))
  have hfeH : ∀ w : String, (pfx ++ w).toList = 'f' :: ((pfx ++ w).toList.tail) := by
    intro w
    have := hdfe w
    unfold hd at this
    cases hl : (pfx ++ w).toList with
    | nil => rw [hl] at this; simp at this
    | cons x t => rw [hl] at this; simp only [List.head?_cons, Option.some.injEq] at this
                  subst this; rfl
  -- membership of the operand and output cells
  have hmemA : ∀ j, j < 4 → (4 * slotOf a + j) ∈ cells := by
    intro j hj
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
  have hmemB : ∀ j, j < 4 → (4 * slotOf b + j) ∈ cells := by
    intro j hj
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
  have hmemO : ∀ j, j < 4 → (4 * slotOf o + j) ∈ cells := by
    intro j hj
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  -- head facts and generic name inequalities
  have hdframe : hd frame = some ca := by unfold hd; rw [harr]; rfl
  have hd_B : hd "B" = some 'B' := rfl
  have hdSlotU : ∀ (w : String) (n : Nat), hd s!"{pfx ++ w}u{n}" = some 'f' :=
    fun w n => hdAppend (hdAppend (hdfe w))
  have hdSlotH : ∀ (w : String) (n : Nat), hd s!"{pfx ++ w}h{n}" = some 'f' :=
    fun w n => hdAppend (hdAppend (hdfe w))
  -- a name whose head is not `'f'` and which is not temporary survives one operand load
  have keepLoad : ∀ (w : String) {t : String} {c : Char}, hd t = some c → c ≠ 'f' →
      (∀ j, j < 4 → t ≠ s!"{pfx ++ w}u{j}") ∧ (∀ k, k < 8 → t ≠ s!"{pfx ++ w}h{k}") := by
    intro w t c ht hc
    exact ⟨fun j _ => neOfHd ht (hdSlotU w j) hc, fun k _ => neOfHd ht (hdSlotH w k) hc⟩
  have notTmpOf : ∀ {t : String} {c : Char}, hd t = some c → c ≠ '_' → ¬ isTmpName t :=
    fun ht hc => (headOk_of_hd ht hc).notTmp
  -- split the prefix run into its four blocks (outer bind = loadB)
  rw [semScalar_seqAll_append, semScalar_seqAll_append, semScalar_seqAll_append] at hpre
  obtain ⟨EA, hIC_A, hloadBrun⟩ := Option.bind_eq_some_iff.mp hpre
  obtain ⟨E2, hIC, hloadArun⟩ := Option.bind_eq_some_iff.mp hIC_A
  obtain ⟨E1, hidxrun, hconstrun⟩ := Option.bind_eq_some_iff.mp hIC
  -- idxCells values and frame
  obtain ⟨E1', hidx', hixv, hidxfr⟩ := idxCells_run cells env
  obtain rfl : E1 = E1' := Option.some.inj (hidxrun.symm.trans hidx')
  -- constInit values and frame
  obtain ⟨E2', hconst', hzz, hcc0, hcc1, hplv, hconstfr⟩ := constInit_run E1
  obtain rfl : E2 = E2' := Option.some.inj (hconstrun.symm.trans hconst')
  -- frame and the output cell indices at E2 (after idx + const)
  have hframeE1 : E1 frame = some ⟨.memref N, arr⟩ := by
    rw [hidxfr frame hcaTmp (fun c _ => neOfHd hdframe (hd_ix c) hcai)]; exact hF
  have hframeE2 : E2 frame = some ⟨.memref N, arr⟩ := by
    rw [hconstfr frame hcaTmp (neOfHd hdframe hd_ZZ hcaZ) (neOfHd hdframe hd_CC0 hcaC)
      (neOfHd hdframe hd_CC1 hcaC) (fun i _ => neOfHd hdframe (hd_PL i) hcaP)]
    exact hframeE1
  have hixE1 : ∀ j, j < 4 →
      E1 s!"ix{4 * slotOf a + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf a + j)⟩ :=
    fun j hj => hixv _ (hmemA j hj)
  have hixAE2 : ∀ j, j < 4 →
      E2 s!"ix{4 * slotOf a + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf a + j)⟩ := by
    intro j hj
    rw [hconstfr _ (notTmpOf (hd_ix _) (by decide)) (neOfHd (hd_ix _) hd_ZZ (by decide))
      (neOfHd (hd_ix _) hd_CC0 (by decide)) (neOfHd (hd_ix _) hd_CC1 (by decide))
      (fun i _ => neOfHd (hd_ix _) (hd_PL i) (by decide))]
    exact hixE1 j hj
  -- load operand A
  obtain ⟨EA', hloadA', hvalA, hltA, hfrA⟩ :=
    loadOperand (s := slotOf a) (hfeH "A") (by decide) (by decide) harr hcaf hAcap hframeE2 hixAE2
  obtain rfl : EA = EA' := Option.some.inj (hloadArun.symm.trans hloadA')
  -- frame and B's / output cell indices survive loadA
  have hframeEA : EA frame = some ⟨.memref N, arr⟩ := by
    rw [hfrA frame hcaTmp (keepLoad "A" hdframe hcaf).1 (keepLoad "A" hdframe hcaf).2]
    exact hframeE2
  have hixBEA : ∀ j, j < 4 →
      EA s!"ix{4 * slotOf b + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf b + j)⟩ := by
    intro j hj
    rw [hfrA _ (notTmpOf (hd_ix _) (by decide)) (keepLoad "A" (hd_ix _) (by decide)).1
      (keepLoad "A" (hd_ix _) (by decide)).2]
    rw [hconstfr _ (notTmpOf (hd_ix _) (by decide)) (neOfHd (hd_ix _) hd_ZZ (by decide))
      (neOfHd (hd_ix _) hd_CC0 (by decide)) (neOfHd (hd_ix _) hd_CC1 (by decide))
      (fun i _ => neOfHd (hd_ix _) (hd_PL i) (by decide))]
    exact hixv _ (hmemB j hj)
  -- load operand B
  obtain ⟨E3', hloadB', hvalB, hltB, hfrB⟩ :=
    loadOperand (s := slotOf b) (hfeH "B") (by decide) (by decide) harr hcaf hBcap hframeEA hixBEA
  obtain rfl : E3 = E3' := Option.some.inj (hloadBrun.symm.trans hloadB')
  -- frame survives loadB
  have hframeE3 : E3 frame = some ⟨.memref N, arr⟩ := by
    rw [hfrB frame hcaTmp (keepLoad "B" hdframe hcaf).1 (keepLoad "B" hdframe hcaf).2]
    exact hframeEA
  -- A's half-limbs survive loadB
  have hAsurv : ∀ k, k < 8 → E3 (feHN (pfx ++ "A") k) = EA (feHN (pfx ++ "A") k) := by
    intro k hk
    have h := hfrB s!"{pfx ++ "A"}h{k}" (notTmpOf (hdSlotH "A" k) (by decide))
      (fun j _ => sibHUNe (hd_A) hd_B (by decide) k j)
      (fun k' _ => sibHNe (hd_A) hd_B (by decide) k k')
    rw [feHN_eq] at h; exact h
  -- constants survive both loads → ConstsAt E3
  have constKeep : ∀ {t : String} {c : Char}, hd t = some c → c ≠ 'f' → ¬ isTmpName t →
      E3 t = E2 t := by
    intro t c ht hc hnt
    rw [hfrB t hnt (keepLoad "B" ht hc).1 (keepLoad "B" ht hc).2,
      hfrA t hnt (keepLoad "A" ht hc).1 (keepLoad "A" ht hc).2]
  have erdc : ∀ {t : String}, E3 t = E2 t → envReader E3 t = envReader E2 t :=
    fun h => by simp only [envReader, h]
  have hConst : ConstsAt E3 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [erdc (constKeep hd_ZZ (by decide) (notTmpOf hd_ZZ (by decide))),
        envReader_of_bound hzz]; rfl
    · rw [erdc (constKeep hd_CC0 (by decide) (notTmpOf hd_CC0 (by decide))),
        envReader_of_bound hcc0]; exact ofNat_toNat (by norm_num [Secp256k1FeMulFront.cc0])
    · rw [erdc (constKeep hd_CC1 (by decide) (notTmpOf hd_CC1 (by decide))),
        envReader_of_bound hcc1]; exact ofNat_toNat (by norm_num [Secp256k1FeMulFront.cc1])
    · intro i hi
      rw [erdc (constKeep (hd_PL i) (by decide) (notTmpOf (hd_PL i) (by decide))),
        envReader_of_bound (hplv i hi)]
      exact ofNat_toNat (by
        have : pl32.getD i 0 < 2 ^ 32 := by
          interval_cases i <;> decide
        omega)
  -- output cell indices survive both loads
  have hixOE3 : ∀ j, j < 4 →
      E3 s!"ix{4 * slotOf o + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf o + j)⟩ := by
    intro j hj
    rw [constKeep (hd_ix _) (by decide) (notTmpOf (hd_ix _) (by decide)),
      hconstfr _ (notTmpOf (hd_ix _) (by decide)) (neOfHd (hd_ix _) hd_ZZ (by decide))
        (neOfHd (hd_ix _) hd_CC0 (by decide)) (neOfHd (hd_ix _) hd_CC1 (by decide))
        (fun i _ => neOfHd (hd_ix _) (hd_PL i) (by decide))]
    exact hixv _ (hmemO j hj)
  -- assemble
  refine ⟨hframeE3, hConst, ?_, hvalB, ?_, hltB, hixOE3⟩
  · have hcong : accN (fun k => (envReader E3 (feHN (pfx ++ "A") k)).toNat) 8
        = accN (fun k => (envReader EA (feHN (pfx ++ "A") k)).toNat) 8 :=
      accN_congr 8 (fun k hk => by have hh := hAsurv k hk; simp only [envReader, hh])
    rw [feVal_eq_accN, hcong, ← feVal_eq_accN]; exact hvalA
  · intro k hk
    have h : envReader E3 (feHN (pfx ++ "A") k) = envReader EA (feHN (pfx ++ "A") k) := by
      have hh := hAsurv k hk; simp only [envReader, hh]
    rw [h]; exact hltA k hk

/-! ## 7. The copy-and-store tail of a framed brick -/

/-- `x.toList` of a name whose first character is `'f'`. -/
theorem headF_toList {x : String} (h : hd x = some 'f') :
    x.toList = 'f' :: x.toList.tail := by
  unfold hd at h
  cases hl : x.toList with
  | nil => rw [hl] at h; simp at h
  | cons c t => rw [hl] at h; simp only [List.head?_cons, Option.some.injEq] at h
                subst h; rfl

/-- **The copy-and-store tail of one framed brick moves the output slot to
    `rval`.** From the post-brick environment `Eb` whose result names `rn` carry
    the 32-bit limbs of `rval`, running the eight output copies and the frame
    store lands `FrameSlots` with the output slot reset to `rval`. -/
theorem framedTail {fw : Nat} {frame : String} {slotOf : String → Nat}
    (pfx o : String) (hdpfx : hd pfx = some 'f') {ca : Char} {ra : List Char}
    (harr : frame.toList = ca :: ra) (hcaTmp : ¬ isTmpName frame)
    (hcaf : ca ≠ 'f') (hcai : ca ≠ 'i')
    {arr : Fin ((fw + 7) / 8) → BitVec 64} {V : Nat → Nat} {active : Nat}
    {E3 Eb E5 env' : SEnvScalar} (bc : List LowCT) (rn : Nat → String) (rval : Nat)
    (hso4 : 4 * slotOf o + 4 ≤ (fw + 7) / 8) (hNcap : (fw + 7) / 8 ≤ 2 ^ 64)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ (fw + 7) / 8)
    (hInv : FrameSlots arr V active) (hvlt : rval < 2 ^ 256)
    (hFE3 : E3 frame = some ⟨.memref ((fw + 7) / 8), arr⟩)
    (hixOE3 : ∀ j, j < 4 →
      E3 s!"ix{4 * slotOf o + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf o + j)⟩)
    (hbcW : WritesIn (fun x => Extends (pfx ++ "C") x ∨ x = "") bc)
    (hbrick : semScalar (seqAll bc) E3 = some Eb)
    (hrnNt : ∀ k, k < 8 → ¬ isTmpName (rn k))
    (hrnNeOh : ∀ (k : Nat), k < 8 → ∀ (j : Nat), rn k ≠ s!"{pfx}Oh{j}")
    (hltR : ∀ k, k < 8 → (envReader Eb (rn k)).toNat < 2 ^ 32)
    (haccR : accN (fun k => (envReader Eb (rn k)).toNat) 8 = rval)
    (hcopy : semScalar (seqAll ((List.range 8).map
        (fun k => LowCT.RScalarSetExpr s!"{pfx}Oh{k}" (sv (rn k))))) Eb = some E5)
    (hstore : semScalar (seqAll (storeFieldTo fw frame (4 * slotOf o) (pfx ++ "O"))) E5
        = some env') :
    ∃ fr : Fin ((fw + 7) / 8) → BitVec 64,
      env' frame = some ⟨.memref ((fw + 7) / 8), fr⟩ ∧
      FrameSlots fr (Function.update V (slotOf o) rval) active := by
  have hdOh : ∀ k : Nat, hd s!"{pfx}Oh{k}" = some 'f' := fun k => hdAppend (hdAppend hdpfx)
  have hdframe : hd frame = some ca := by unfold hd; rw [harr]; rfl
  -- frame and the output cell indices do not extend the brick prefix
  have notExt : ¬ ((fun x => Extends (pfx ++ "C") x ∨ x = "") frame) := by
    rintro (⟨u, hu⟩ | rfl)
    · have h2 : hd frame = some 'f' := by rw [hu]; exact hdAppend (hdAppend hdpfx)
      rw [hdframe] at h2; exact hcaf (Option.some.inj h2)
    · exact absurd harr (by simp)
  have notExtIx : ∀ c : Nat, ¬ ((fun x => Extends (pfx ++ "C") x ∨ x = "") s!"ix{c}") := by
    intro c
    rintro (⟨u, hu⟩ | he)
    · have h2 : hd s!"ix{c}" = some 'f' := by rw [hu]; exact hdAppend (hdAppend hdpfx)
      rw [hd_ix c] at h2; exact absurd (Option.some.inj h2) (by decide)
    · have h3 := hd_ix c; rw [he] at h3; simp [hd] at h3
  -- E3 → Eb: binding-level frame preservation through the brick body
  have hFEb : Eb frame = some ⟨.memref ((fw + 7) / 8), arr⟩ := by
    rw [env_seqAll_frame _ bc hbcW E3 Eb hbrick frame hcaTmp notExt]; exact hFE3
  have hixOEb : ∀ j, j < 4 →
      Eb s!"ix{4 * slotOf o + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf o + j)⟩ := by
    intro j hj
    rw [env_seqAll_frame _ bc hbcW E3 Eb hbrick s!"ix{4 * slotOf o + j}"
      ((headOk_of_hd (hd_ix _) (by decide)).notTmp) (notExtIx (4 * slotOf o + j))]
    exact hixOE3 j hj
  -- copy block
  obtain ⟨hOhval, hcopyKeep⟩ :=
    framedCopy_run pfx rn (fun k _ => (headOk_of_hd (hdOh k) (by decide)).notTmp)
      (fun k j _ _ hne he => hne (slot_inj he)) hrnNt (fun k j hk _ => hrnNeOh k hk j) Eb 8
      (le_refl 8) E5 hcopy
  -- frame and output cell indices survive the copy block
  have hFE5 : E5 frame = some ⟨.memref ((fw + 7) / 8), arr⟩ := by
    rw [hcopyKeep frame hcaTmp
      (fun j _ => neOfHd hdframe (hdOh j) hcaf)]
    exact hFEb
  have hixOE5 : ∀ j, j < 4 →
      E5 s!"ix{4 * slotOf o + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * slotOf o + j)⟩ := by
    intro j hj
    rw [hcopyKeep _ ((headOk_of_hd (hd_ix _) (by decide)).notTmp)
      (fun j' _ => neOfHd (hd_ix _) (hdOh j') (by decide))]
    exact hixOEb j hj
  -- the output field element's slots at E5
  have hOhEq : ∀ k, feHN (pfx ++ "O") k = s!"{pfx}Oh{k}" :=
    fun k => (feHN_eq _ _).symm.trans (oh_bridge _ _).symm
  have hbnd : ∀ k, k < 8 →
      E5 (feHN (pfx ++ "O") k) = some ⟨.sword 64, envReader E5 (feHN (pfx ++ "O") k)⟩ := by
    intro k hk
    have hb := hOhval k hk
    rw [hOhEq k, hb, envReader_of_bound hb]
  have hltO : ∀ k, k < 8 → (envReader E5 (feHN (pfx ++ "O") k)).toNat < 2 ^ 32 := by
    intro k hk
    rw [hOhEq k, envReader_of_bound (hOhval k hk)]; exact hltR k hk
  have hfeVal : feVal E5 (pfx ++ "O") = rval := by
    rw [feVal_eq_accN, ← haccR]
    exact accN_congr 8 (fun k hk => by
      rw [hOhEq k, envReader_of_bound (hOhval k hk)])
  -- store
  obtain ⟨envF, fr, hstoreF, hbfr, hInvF⟩ :=
    frameSlots_store (so := slotOf o) (headF_toList (hdAppend hdpfx)) (by decide) (by decide)
      harr hcaf hcaTmp hcai hso4 hNcap hactive hFE5 hixOE5 hbnd hltO (hfeVal ▸ hvlt) hInv
  obtain rfl : env' = envF := Option.some.inj (hstore.symm.trans hstoreF)
  exact ⟨fr, hbfr, by rw [← hfeVal]; exact hInvF⟩

/-! ## 8. Brick-prefix `OutOf` and result-name inequalities -/

/-- `"C"` has first character `'C'`. -/
theorem hd_Ctag : hd "C" = some 'C' := rfl

/-- An operand half-limb of a sibling field element is outside the `"C"` output
    element's namespace. -/
theorem sibOutH {pfx t : String} {ct : Char} (hpfx : HeadOk pfx) (ht : hd t = some ct)
    (hne : ct ≠ 'C') (k : Nat) : OutOf (pfx ++ "C") s!"{pfx ++ t}h{k}" := by
  have e : s!"{pfx ++ t}h{k}" = pfx ++ t ++ ("h" ++ toString k) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e]; exact sibOut hpfx ht hd_Ctag hne _

/-- A `"C"`-result name and an `"Oh"`-output slot of the same brick differ. -/
theorem RNeOh {pfx : String} (k j : Nat) : s!"{pfx ++ "C"}R{k}" ≠ s!"{pfx}Oh{j}" := by
  have e1 : s!"{pfx ++ "C"}R{k}" = pfx ++ ("C" ++ ("R" ++ toString k)) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx}Oh{j}" = pfx ++ ("Oh" ++ toString j) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e1, e2]
  exact pfxNe (neOfHd (hdAppend rfl) (hdAppend (rfl : hd "Oh" = some 'O')) (by decide))

/-- A `"CA"`-sum result name (the subtract brick's output) and an `"Oh"`-output
    slot of the same brick differ. -/
theorem SubNeOh {pfx : String} (k j : Nat) : s!"{pfx ++ "C" ++ "A"}s{k}" ≠ s!"{pfx}Oh{j}" := by
  have e1 : s!"{pfx ++ "C" ++ "A"}s{k}" = pfx ++ ("C" ++ ("A" ++ ("s" ++ toString k))) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  have e2 : s!"{pfx}Oh{j}" = pfx ++ ("Oh" ++ toString j) := by
    simp only [show ∀ s : String, toString s = s from fun _ => rfl, String.append_assoc]
  rw [e1, e2]
  exact pfxNe (neOfHd (hdAppend rfl) (hdAppend (rfl : hd "Oh" = some 'O')) (by decide))

/-! ## 9. The single-brick framed value step -/

/-- **The multiply brick's framed value step.** Running one `emitFOpFramed`
    multiply brick over the frame updates the frame so `FrameSlots` holds again
    with the output slot reset to `fm` of the two operand slot values, all other
    slots unchanged. -/
theorem emitFOpFramed_mul_value {fw : Nat} {frame : String} {slotOf : String → Nat}
    (idx : Nat) (o a b : String) {ca : Char} {ra : List Char}
    (harr : frame.toList = ca :: ra) (hcaTmp : ¬ isTmpName frame)
    (hcaf : ca ≠ 'f') (hcai : ca ≠ 'i') (hcaZ : ca ≠ 'Z') (hcaC : ca ≠ 'C') (hcaP : ca ≠ 'P')
    {arr : Fin ((fw + 7) / 8) → BitVec 64} {V : Nat → Nat} {active : Nat} {env env' : SEnvScalar}
    (hF : env frame = some ⟨.memref ((fw + 7) / 8), arr⟩)
    (hFrame : FrameSlots arr V active) (hNcap : (fw + 7) / 8 ≤ 2 ^ 64)
    (hAcap : 4 * slotOf a + 4 ≤ 2 ^ 64) (hBcap : 4 * slotOf b + 4 ≤ 2 ^ 64)
    (hso4 : 4 * slotOf o + 4 ≤ (fw + 7) / 8)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ (fw + 7) / 8)
    (hAact : slotOf a < active) (hBact : slotOf b < active)
    (hAltP : V (slotOf a) < pNat) (hBltP : V (slotOf b) < pNat)
    (hrun : semScalar (seqAll (emitFOpFramed fw frame slotOf idx (FOp.mul o a b))) env = some env') :
    ∃ fr : Fin ((fw + 7) / 8) → BitVec 64,
      env' frame = some ⟨.memref ((fw + 7) / 8), fr⟩ ∧
      FrameSlots fr (Function.update V (slotOf o) (fm (V (slotOf a)) (V (slotOf b)))) active := by
  simp only [emitFOpFramed, brickFn] at hrun
  have hdpfx : hd s!"fop{idx}" = some 'f' := hdAppend rfl
  have hpfxHead : HeadOk s!"fop{idx}" := headOk_of_hd hdpfx (by decide)
  have hdC : hd (s!"fop{idx}" ++ "C") = some 'f' := hdAppend hdpfx
  set bc := (feMulHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
    (feH (s!"fop{idx}" ++ "B"))).1 with hbcdef
  set br := (feMulHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
    (feH (s!"fop{idx}" ++ "B"))).2 with hbrdef
  -- split the emitted brick into prefix / body / copies / store
  rw [semScalar_seqAll_append, semScalar_seqAll_append, semScalar_seqAll_append] at hrun
  obtain ⟨E5, hPBC, hstore⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨Eb, hPB, hcopy⟩ := Option.bind_eq_some_iff.mp hPBC
  obtain ⟨E3, hprefix, hbrick⟩ := Option.bind_eq_some_iff.mp hPB
  -- prefix values
  obtain ⟨hFE3, hConst, hvalA, hvalB, hltA, hltB, hixO⟩ :=
    framedPrefix idx a b o harr hcaTmp hcaf hcai hcaZ hcaC hcaP hAcap hBcap hF hprefix
  -- operand accumulators
  have hAc : accN (fun k => (envReader E3 (feHN (s!"fop{idx}" ++ "A") k)).toNat) 8 < pNat := by
    rw [← feVal_eq_accN, hvalA, hFrame (slotOf a) hAact]; exact hAltP
  have hBc : accN (fun k => (envReader E3 (feHN (s!"fop{idx}" ++ "B") k)).toNat) 8 < pNat := by
    rw [← feVal_eq_accN, hvalB, hFrame (slotOf b) hBact]; exact hBltP
  -- the brick body's value semantics
  have hbrickL : semList bc E3 = some Eb := by rw [← semScalar_seqAll_eq_semList]; exact hbrick
  obtain ⟨-, hltR, haccR⟩ :=
    feMulHalves_sem_gen genMulSpec_holds (s!"fop{idx}" ++ "C") (s!"fop{idx}" ++ "A")
      (s!"fop{idx}" ++ "B") hdC (by decide) (by decide) (by decide) (by decide)
      (outOf_of_hd hdC hd_ZZ (by decide) (by decide))
      (fun i => outOf_of_hd hdC (hd_PL i) (by decide) (by decide))
      (fun k hk => by rw [feH_len] at hk; rw [feH_getBang _ k hk, ← feHN_eq]
                      exact sibOutH hpfxHead hd_A (by decide) k)
      (fun k hk => by rw [feH_len] at hk; rw [feH_getBang _ k hk, ← feHN_eq]
                      exact sibOutH hpfxHead (by decide : hd "B" = some 'B') (by decide) k)
      E3 Eb hConst hltA hltB hAc hBc hbrickL
  -- result names
  have hbrEq : ∀ k, k < 8 → br[k]! = s!"{s!"fop{idx}" ++ "C"}R{k}" := by
    intro k hk; rw [hbrdef, feMulHalves_names]; exact rNamesOf_getBang _ k hk
  have hstep1 : accN (fun k => (envReader Eb (br[k]!)).toNat) 8
      = accN (fun k => (envReader Eb s!"{s!"fop{idx}" ++ "C"}R{k}").toNat) 8 :=
    accN_congr 8 (fun k hk => by rw [hbrEq k hk])
  have haccRn : accN (fun k => (envReader Eb (br[k]!)).toNat) 8
      = fm (V (slotOf a)) (V (slotOf b)) := by
    rw [hstep1, haccR]
    congr 1
    · rw [← feVal_eq_accN, hvalA]; exact hFrame (slotOf a) hAact
    · rw [← feVal_eq_accN, hvalB]; exact hFrame (slotOf b) hBact
  -- assemble via the copy-and-store tail
  refine framedTail (s!"fop{idx}") o hdpfx harr hcaTmp hcaf hcai bc (fun k => br[k]!)
    (fm (V (slotOf a)) (V (slotOf b))) hso4 hNcap hactive hFrame
    (by rw [fm]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [pNat])) (le_of_lt pNat_lt_pow256))
    hFE3 hixO
    (hbcdef ▸ feMulHalves_writes (suffixClosed_extends (s!"fop{idx}" ++ "C"))
      (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))
      (extends_self (s!"fop{idx}" ++ "C")))
    hbrick
    (fun k hk => by show ¬ isTmpName br[k]!
                    rw [hbrEq k hk]
                    exact (headOk_of_hd (hdAppend (hdAppend hdC)) (by decide)).notTmp)
    (fun k hk j => by show br[k]! ≠ _; rw [hbrEq k hk]; exact RNeOh k j)
    (fun k hk => by show (envReader Eb br[k]!).toNat < 2 ^ 32; rw [hbrEq k hk]; exact hltR k hk)
    haccRn hcopy hstore

/-- **The add brick's framed value step.** One `emitFOpFramed` add brick resets
    the output frame slot to `fa` of the two operand slot values. -/
theorem emitFOpFramed_add_value {fw : Nat} {frame : String} {slotOf : String → Nat}
    (idx : Nat) (o a b : String) {ca : Char} {ra : List Char}
    (harr : frame.toList = ca :: ra) (hcaTmp : ¬ isTmpName frame)
    (hcaf : ca ≠ 'f') (hcai : ca ≠ 'i') (hcaZ : ca ≠ 'Z') (hcaC : ca ≠ 'C') (hcaP : ca ≠ 'P')
    {arr : Fin ((fw + 7) / 8) → BitVec 64} {V : Nat → Nat} {active : Nat} {env env' : SEnvScalar}
    (hF : env frame = some ⟨.memref ((fw + 7) / 8), arr⟩)
    (hFrame : FrameSlots arr V active) (hNcap : (fw + 7) / 8 ≤ 2 ^ 64)
    (hAcap : 4 * slotOf a + 4 ≤ 2 ^ 64) (hBcap : 4 * slotOf b + 4 ≤ 2 ^ 64)
    (hso4 : 4 * slotOf o + 4 ≤ (fw + 7) / 8)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ (fw + 7) / 8)
    (hAact : slotOf a < active) (hBact : slotOf b < active)
    (hAltP : V (slotOf a) < pNat) (hBltP : V (slotOf b) < pNat)
    (hrun : semScalar (seqAll (emitFOpFramed fw frame slotOf idx (FOp.add o a b))) env = some env') :
    ∃ fr : Fin ((fw + 7) / 8) → BitVec 64,
      env' frame = some ⟨.memref ((fw + 7) / 8), fr⟩ ∧
      FrameSlots fr (Function.update V (slotOf o) (fa (V (slotOf a)) (V (slotOf b)))) active := by
  simp only [emitFOpFramed, brickFn] at hrun
  have hdpfx : hd s!"fop{idx}" = some 'f' := hdAppend rfl
  have hpfxHead : HeadOk s!"fop{idx}" := headOk_of_hd hdpfx (by decide)
  have hdC : hd (s!"fop{idx}" ++ "C") = some 'f' := hdAppend hdpfx
  set bc := (feAddHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
    (feH (s!"fop{idx}" ++ "B"))).1 with hbcdef
  set br := (feAddHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
    (feH (s!"fop{idx}" ++ "B"))).2 with hbrdef
  rw [semScalar_seqAll_append, semScalar_seqAll_append, semScalar_seqAll_append] at hrun
  obtain ⟨E5, hPBC, hstore⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨Eb, hPB, hcopy⟩ := Option.bind_eq_some_iff.mp hPBC
  obtain ⟨E3, hprefix, hbrick⟩ := Option.bind_eq_some_iff.mp hPB
  obtain ⟨hFE3, hConst, hvalA, hvalB, hltA, hltB, hixO⟩ :=
    framedPrefix idx a b o harr hcaTmp hcaf hcai hcaZ hcaC hcaP hAcap hBcap hF hprefix
  have hAc : accN (fun k => (envReader E3 (feHN (s!"fop{idx}" ++ "A") k)).toNat) 8 < pNat := by
    rw [← feVal_eq_accN, hvalA, hFrame (slotOf a) hAact]; exact hAltP
  have hBc : accN (fun k => (envReader E3 (feHN (s!"fop{idx}" ++ "B") k)).toNat) 8 < pNat := by
    rw [← feVal_eq_accN, hvalB, hFrame (slotOf b) hBact]; exact hBltP
  have hbrickL : semList bc E3 = some Eb := by rw [← semScalar_seqAll_eq_semList]; exact hbrick
  obtain ⟨-, hltR, haccR⟩ :=
    feAddHalves_sem_gen (s!"fop{idx}" ++ "C") (s!"fop{idx}" ++ "A") (s!"fop{idx}" ++ "B")
      hdC (by decide)
      (fun i => by
        by_cases hi : i < 8
        · rw [feH_getD _ _ i hi, ← feHN_eq]; exact sibOutH hpfxHead hd_A (by decide) i
        · rw [feH_getD_ge _ _ i (by omega)]; exact outOf_of_hd hdC hd_ZZ (by decide) (by decide))
      (fun i => by
        by_cases hi : i < 8
        · rw [feH_getD _ _ i hi, ← feHN_eq]
          exact sibOutH hpfxHead (by decide : hd "B" = some 'B') (by decide) i
        · rw [feH_getD_ge _ _ i (by omega)]; exact outOf_of_hd hdC hd_ZZ (by decide) (by decide))
      (outOf_of_hd hdC hd_ZZ (by decide) (by decide))
      (fun i => outOf_of_hd hdC (hd_PL i) (by decide) (by decide))
      E3 Eb hConst.zero hConst.modulus hltA hltB hAc hBc hbrickL
  have hbrEq : ∀ k, k < 8 → br[k]! = s!"{s!"fop{idx}" ++ "C"}R{k}" := by
    intro k hk; rw [hbrdef, feAddHalves_names]; exact rNamesOf_getBang _ k hk
  have hstep1 : accN (fun k => (envReader Eb (br[k]!)).toNat) 8
      = accN (fun k => (envReader Eb s!"{s!"fop{idx}" ++ "C"}R{k}").toNat) 8 :=
    accN_congr 8 (fun k hk => by rw [hbrEq k hk])
  have haccRn : accN (fun k => (envReader Eb (br[k]!)).toNat) 8
      = fa (V (slotOf a)) (V (slotOf b)) := by
    rw [hstep1, haccR]
    congr 1
    · rw [← feVal_eq_accN, hvalA]; exact hFrame (slotOf a) hAact
    · rw [← feVal_eq_accN, hvalB]; exact hFrame (slotOf b) hBact
  refine framedTail (s!"fop{idx}") o hdpfx harr hcaTmp hcaf hcai bc (fun k => br[k]!)
    (fa (V (slotOf a)) (V (slotOf b))) hso4 hNcap hactive hFrame
    (by rw [fa]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [pNat])) (le_of_lt pNat_lt_pow256))
    hFE3 hixO
    (hbcdef ▸ feAddHalves_writes (suffixClosed_extends (s!"fop{idx}" ++ "C"))
      (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))
      (extends_self (s!"fop{idx}" ++ "C")))
    hbrick
    (fun k hk => by show ¬ isTmpName br[k]!
                    rw [hbrEq k hk]
                    exact (headOk_of_hd (hdAppend (hdAppend hdC)) (by decide)).notTmp)
    (fun k hk j => by show br[k]! ≠ _; rw [hbrEq k hk]; exact RNeOh k j)
    (fun k hk => by show (envReader Eb br[k]!).toNat < 2 ^ 32; rw [hbrEq k hk]; exact hltR k hk)
    haccRn hcopy hstore

/-- **The subtract brick's framed value step.** One `emitFOpFramed` subtract brick
    resets the output frame slot to `fs` of the two operand slot values. -/
theorem emitFOpFramed_sub_value {fw : Nat} {frame : String} {slotOf : String → Nat}
    (idx : Nat) (o a b : String) {ca : Char} {ra : List Char}
    (harr : frame.toList = ca :: ra) (hcaTmp : ¬ isTmpName frame)
    (hcaf : ca ≠ 'f') (hcai : ca ≠ 'i') (hcaZ : ca ≠ 'Z') (hcaC : ca ≠ 'C') (hcaP : ca ≠ 'P')
    {arr : Fin ((fw + 7) / 8) → BitVec 64} {V : Nat → Nat} {active : Nat} {env env' : SEnvScalar}
    (hF : env frame = some ⟨.memref ((fw + 7) / 8), arr⟩)
    (hFrame : FrameSlots arr V active) (hNcap : (fw + 7) / 8 ≤ 2 ^ 64)
    (hAcap : 4 * slotOf a + 4 ≤ 2 ^ 64) (hBcap : 4 * slotOf b + 4 ≤ 2 ^ 64)
    (hso4 : 4 * slotOf o + 4 ≤ (fw + 7) / 8)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ (fw + 7) / 8)
    (hAact : slotOf a < active) (hBact : slotOf b < active)
    (hAltP : V (slotOf a) < pNat) (hBltP : V (slotOf b) < pNat)
    (hrun : semScalar (seqAll (emitFOpFramed fw frame slotOf idx (FOp.sub o a b))) env = some env') :
    ∃ fr : Fin ((fw + 7) / 8) → BitVec 64,
      env' frame = some ⟨.memref ((fw + 7) / 8), fr⟩ ∧
      FrameSlots fr (Function.update V (slotOf o) (fs (V (slotOf a)) (V (slotOf b)))) active := by
  simp only [emitFOpFramed, brickFn] at hrun
  have hdpfx : hd s!"fop{idx}" = some 'f' := hdAppend rfl
  have hpfxHead : HeadOk s!"fop{idx}" := headOk_of_hd hdpfx (by decide)
  have hdC : hd (s!"fop{idx}" ++ "C") = some 'f' := hdAppend hdpfx
  set bc := (feSubHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
    (feH (s!"fop{idx}" ++ "B"))).1 with hbcdef
  set br := (feSubHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
    (feH (s!"fop{idx}" ++ "B"))).2 with hbrdef
  rw [semScalar_seqAll_append, semScalar_seqAll_append, semScalar_seqAll_append] at hrun
  obtain ⟨E5, hPBC, hstore⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨Eb, hPB, hcopy⟩ := Option.bind_eq_some_iff.mp hPBC
  obtain ⟨E3, hprefix, hbrick⟩ := Option.bind_eq_some_iff.mp hPB
  obtain ⟨hFE3, hConst, hvalA, hvalB, hltA, hltB, hixO⟩ :=
    framedPrefix idx a b o harr hcaTmp hcaf hcai hcaZ hcaC hcaP hAcap hBcap hF hprefix
  have hAc : accN (fun k => (envReader E3 (feHN (s!"fop{idx}" ++ "A") k)).toNat) 8 < pNat := by
    rw [← feVal_eq_accN, hvalA, hFrame (slotOf a) hAact]; exact hAltP
  have hBc : accN (fun k => (envReader E3 (feHN (s!"fop{idx}" ++ "B") k)).toNat) 8 < pNat := by
    rw [← feVal_eq_accN, hvalB, hFrame (slotOf b) hBact]; exact hBltP
  have hbrickL : semList bc E3 = some Eb := by rw [← semScalar_seqAll_eq_semList]; exact hbrick
  obtain ⟨-, hltR, haccR⟩ :=
    feSubHalves_sem_gen (s!"fop{idx}" ++ "C") (s!"fop{idx}" ++ "A") (s!"fop{idx}" ++ "B")
      hdC (by decide)
      (outOf_of_hd hdC hd_ZZ (by decide) (by decide))
      (fun i => outOf_of_hd hdC (hd_PL i) (by decide) (by decide))
      (fun k _ => by rw [← feHN_eq]; exact sibOutH hpfxHead hd_A (by decide) k)
      (fun k _ => by rw [← feHN_eq]; exact sibOutH hpfxHead (by decide : hd "B" = some 'B') (by decide) k)
      E3 Eb hConst.zero hConst.modulus hltA hltB hAc hBc hbrickL
  have hbrEq : ∀ k, k < 8 → br[k]! = s!"{s!"fop{idx}" ++ "C" ++ "A"}s{k}" := by
    intro k hk
    rw [hbrdef, feSubHalves_names, take_getBang _ 8 k hk]
    refine genAdd_name "ZZ"
      (genSub "ZZ" (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))
        (s!"fop{idx}" ++ "C" ++ "S")).2.1
      (pmNamesOf (s!"fop{idx}" ++ "C")) (s!"fop{idx}" ++ "C" ++ "A") k ?_
    rw [genSub_len, feH_len, pmNamesOf_len]; simpa using hk
  have hstep1 : accN (fun k => (envReader Eb (br[k]!)).toNat) 8
      = accN (fun k => (envReader Eb s!"{s!"fop{idx}" ++ "C" ++ "A"}s{k}").toNat) 8 :=
    accN_congr 8 (fun k hk => by rw [hbrEq k hk])
  have haccRn : accN (fun k => (envReader Eb (br[k]!)).toNat) 8
      = fs (V (slotOf a)) (V (slotOf b)) := by
    rw [hstep1, haccR]
    congr 1
    · rw [← feVal_eq_accN, hvalA]; exact hFrame (slotOf a) hAact
    · rw [← feVal_eq_accN, hvalB]; exact hFrame (slotOf b) hBact
  refine framedTail (s!"fop{idx}") o hdpfx harr hcaTmp hcaf hcai bc (fun k => br[k]!)
    (fs (V (slotOf a)) (V (slotOf b))) hso4 hNcap hactive hFrame
    (by rw [fs]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [pNat])) (le_of_lt pNat_lt_pow256))
    hFE3 hixO
    (hbcdef ▸ feSubHalves_writes (suffixClosed_extends (s!"fop{idx}" ++ "C"))
      (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))
      (extends_self (s!"fop{idx}" ++ "C")))
    hbrick
    (fun k hk => by show ¬ isTmpName br[k]!
                    rw [hbrEq k hk]
                    exact (headOk_of_hd (hdAppend (hdAppend (hdAppend hdC))) (by decide)).notTmp)
    (fun k hk j => by show br[k]! ≠ _; rw [hbrEq k hk]; exact SubNeOh k j)
    (fun k hk => by show (envReader Eb br[k]!).toNat < 2 ^ 32; rw [hbrEq k hk]; exact hltR k hk)
    haccRn hcopy hstore

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedBrickValue
