/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapClose
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInitSort

@[expose] public section

set_option autoImplicit false

/-!
# The merge conditions of a region export at the allocation certificate

The check `regionMergeB` of the region gate holds on the parts `regionCoParts` of a region
export under the merge conditions `MergeSep` (`regionMergeB_regionLprogC`). This module
states the names the export writes and, from them, fields of `MergeSep` at the certificate of
the allocation `regionLprogC`.

## Main definitions

* `ExportRegName`: a name whose first character is `r` or `L`.

## Main results

* `exportR_defNames`: every name an instruction of the region export writes is an
  `ExportRegName`.
* `regDefs_regionCoParts_ren`: every register name an instruction of the renamed code of the
  parts writes is an `ExportRegName`, except the target of the result copy written by the
  last instruction.
* `renOf_certMerge_allocCertOf_eq_empty`: the merge of an allocation certificate gives the
  empty image to the empty name only.
* `empty_regionLprogC`, `defNe_regionLprogC`: the fields `empty` and `defNe` of `MergeSep`.
* `plainDefs_regionLprogC`: the written names premise of `sep_regionLprogC`.
* `noTag_regionCoCode`: the code of the parts mentions no tagged name.
* `entry_regionCoParts`, `entry_regionLprogC`: the field `entry` of `MergeSep`, from
  definite assignment of the tagged code of the parts (`cert_regionCoCodeS`).
* `mergeSep_regionLprogC`: all fields of `MergeSep` at the allocation.
* `exportR_allocInput`: definite assignment, forward reachability and loop headers of the
  input of the allocation of a region export without a callee, and definite assignment of
  that input preceded by the entry pin, when the output array is an argument name.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapLive

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs
  memRegDefs storeHit? arrDefs arrUse? jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference (LiveAt)
open RegionAllocMapComplete RegionExportDefInit RegionAllocMapAlign RegionAllocMapClose
open RegionExportDefInitSort (tagA untag IsTag NoTag notTag_of_head notTag_argName untag_of_not
  untag_tagA renArr_of_cmp isSome_cmpArgs?_of_renArr ArgS ExportES
  exportR_certS noTag_of_cert regionAllocCode_chain sortName_of_arr)

/-! ## 1. Export register names -/

/-- **An export register name**: a name whose first character is `r` or `L`. The register
    names the region export writes are of this form: `regName d`, the names of the carried
    blocks `carriedRegs d n`, the loop counters `loopCtr n`, and the registers `copyIdx` and
    `copyTmp` of the result copy. -/
def ExportRegName (x : String) : Prop :=
  x.toList.head? = some 'r' ∨ x.toList.head? = some 'L'

theorem exportRegName_regName (d : Nat) : ExportRegName (regName d) :=
  Or.inl (by simp [regName, String.toList_append])

theorem exportRegName_loopCtr (n : Nat) : ExportRegName (loopCtr n) :=
  Or.inr (by simp [loopCtr, String.toList_append])

theorem exportRegName_carriedRegs {d n : Nat} {x : String} (h : x ∈ carriedRegs d n) :
    ExportRegName x := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  exact exportRegName_regName _

theorem exportRegName_copyIdx : ExportRegName copyIdx := Or.inl (by decide)

theorem exportRegName_copyTmp : ExportRegName copyTmp := Or.inl (by decide)

/-- An export register name is no hardware register name. -/
theorem ExportRegName.not_hw {x : String} (h : ExportRegName x) :
    isHwRegName x = false := by
  have hall : ∀ y ∈ hwRegNames, y.toList.head? ≠ some 'r' ∧ y.toList.head? ≠ some 'L' := by
    decide
  cases hb : isHwRegName x with
  | false => rfl
  | true =>
    have hm : x ∈ hwRegNames := by
      simpa [isHwRegName, List.contains_iff_mem] using hb
    obtain ⟨h1, h2⟩ := hall x hm
    exact (h.elim h1 h2).elim

/-- An export register name is a plain name. -/
theorem ExportRegName.plainName {x : String} (h : ExportRegName x) : PlainName x := by
  refine ⟨h.not_hw, ?_, ?_⟩
  · unfold ExportRegName at h
    have hpre : ∀ p : String, p.toList.head? ≠ some 'r' → p.toList.head? ≠ some 'L' →
        p.toList ≠ [] → hasPrefix x p = false := by
      intro p h1 h2 h3
      cases hp : p.toList with
      | nil => exact absurd hp h3
      | cons c t =>
        cases hx : x.toList with
        | nil => rcases h with h | h <;> rw [hx] at h <;> cases h
        | cons c' t' =>
          rw [hp] at h1 h2
          rw [hx] at h
          have hc : c' ≠ c := by
            rcases h with h | h <;> simp only [List.head?_cons, Option.some.injEq] at h <;>
              subst h <;> simp_all [eq_comm]
          simp only [hasPrefix, hp, hx, List.isPrefixOf, Bool.and_eq_false_iff]
          exact Or.inl (beq_false_of_ne (Ne.symm hc))
    unfold isFrameSlotName
    rw [hpre "k." (by decide) (by decide) (by decide), hpre "kv." (by decide) (by decide)
      (by decide), hpre "qsave." (by decide) (by decide) (by decide),
      hpre "mem." (by decide) (by decide) (by decide)]
    rfl
  · have hall : ∀ y ∈ vectorRegNames, y.toList.head? ≠ some 'r' ∧ y.toList.head? ≠ some 'L' := by
      decide
    intro hm
    obtain ⟨h1, h2⟩ := hall x hm
    exact h.elim h1 h2

/-- An export register name is not empty. -/
theorem ExportRegName.ne_empty {x : String} (h : ExportRegName x) : x ≠ "" := by
  rintro rfl
  rcases h with h | h <;> cases h

/-- An export register name is no argument name. -/
theorem ExportRegName.notTag {x : String} (h : ExportRegName x) : ¬ IsTag x := by
  rcases h with h | h <;> exact notTag_of_head h (by decide)

theorem ExportRegName.ne_argName {x : String} (h : ExportRegName x) (j : Nat) :
    x ≠ argName j := by
  rintro rfl
  rcases h with h | h <;> simp [argName, String.toList_append] at h

/-! ## 2. The names the export writes -/

/-- The names an instruction writes (`defNames`) are export register names. -/
def DefsR (i : LinstrRM) : Prop := ∀ x ∈ defNames i.1, ExportRegName x

theorem defsR_reg {i : LinstrRM} {x o : String} {ss : List LOperand}
    (h : i.1 = .Lopn [.reg x] o ss) (hx : ExportRegName x) : DefsR i := by
  intro y hy
  rw [h] at hy
  simp [defNames_Lopn, JasminLsemExportRewrites.opNames] at hy
  subst hy
  exact hx

theorem defsR_nonLopn {i : LinstrRM} (h : ∀ ds o ss, i.1 ≠ .Lopn ds o ss) : DefsR i := by
  intro y hy
  rw [defNames_nonLopn h] at hy
  cases hy

theorem defsR_movI {dst : String} (src : LOperand) (h : ExportRegName dst) :
    DefsR (movI dst src) :=
  defsR_reg rfl h

theorem defsR_seedMoves {car : List String} (ops : List LOperand)
    (h : ∀ x ∈ car, ExportRegName x) : ∀ i ∈ seedMoves car ops, DefsR i := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact defsR_movI _ (h _ (List.of_mem_zip hp).1)

theorem defsR_arrMoves {z t : String} {mv : List ArrMove} (ht : ExportRegName t)
    (hd : ∀ a ∈ mv, ExportRegName a.dst) : ∀ i ∈ arrMoves z t mv, DefsR i := by
  intro i hi
  obtain ⟨a, ha, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact defsR_reg rfl ht
  · exact defsR_reg rfl (hd a ha)

theorem dst_mem_arrPairs {tp : List (JasminTy × String × String)} {a : ArrMove}
    (h : a ∈ arrPairs tp) : ∃ p ∈ tp, a.dst = p.2.1 := by
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp h
  refine ⟨p, hp, ?_⟩
  obtain ⟨ty, x, y⟩ := p
  cases ty <;> simp at he
  subst he
  rfl

theorem fst_mem_regPairs {tp : List (JasminTy × String × String)} {q : String × String}
    (h : q ∈ regPairs tp) : ∃ p ∈ tp, q.1 = p.2.1 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨p, (List.mem_filter.mp hp).1, rfl⟩

theorem defsR_typedMoves {z t : String} {tp : List (JasminTy × String × String)}
    (ht : ExportRegName t) (hd : ∀ p ∈ tp, ExportRegName p.2.1) :
    ∀ i ∈ typedMoves z t tp, DefsR i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · refine defsR_arrMoves ht (fun a ha => ?_) i hi
    obtain ⟨p, hp, he⟩ := dst_mem_arrPairs ha
    exact he ▸ hd p hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
    obtain ⟨p, hp, he⟩ := fst_mem_regPairs hq
    exact defsR_movI _ (he ▸ hd p hp)

theorem dst_arrStage : ∀ (D : Nat) (mv : List ArrMove), ∀ a ∈ arrStage D mv,
    ExportRegName a.dst
  | _, [] => by simp [arrStage]
  | D, _ :: mv => by
    intro a ha
    simp only [arrStage, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact exportRegName_regName D
    · exact dst_arrStage (D + 1) mv a ha

theorem dst_arrCommit {mv : List ArrMove} (hd : ∀ a ∈ mv, ExportRegName a.dst) :
    ∀ (D : Nat), ∀ a ∈ arrCommit D mv, ExportRegName a.dst := by
  induction mv with
  | nil => simp [arrCommit]
  | cons b mv ih =>
    intro D a ha
    simp only [arrCommit, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hd b List.mem_cons_self
    · exact ih (fun a h => hd a (List.mem_cons_of_mem _ h)) (D + 1) a ha

theorem defsR_arrParMoves {z t : String} (D : Nat) {mv : List ArrMove} (ht : ExportRegName t)
    (hd : ∀ a ∈ mv, ExportRegName a.dst) : ∀ i ∈ arrParMoves z t D mv, DefsR i := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact defsR_arrMoves ht hd i hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact defsR_arrMoves ht (dst_arrStage D mv) i hi
    · exact defsR_arrMoves ht (dst_arrCommit hd D) i hi

theorem defsR_parMoves (D : Nat) {tgts : List String} (ops : List LOperand)
    (h : ∀ x ∈ tgts, ExportRegName x) : ∀ i ∈ ExportRegions.parMoves D tgts ops, DefsR i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact defsR_movI _ (exportRegName_regName _)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    exact defsR_movI _ (h _ (List.fst_mem_of_mem_zipIdx hp))

theorem defsR_advanceOps {idx ctr : String} (h1 : ExportRegName idx) (h2 : ExportRegName ctr) :
    ∀ i ∈ advanceOps idx ctr, DefsR i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact defsR_reg rfl h1
  · exact defsR_reg rfl h2

theorem tgt_carriedPairs {cs : List JasminTy} {car : List String} {ops : List LOperand}
    {p : JasminTy × String × String} (h : p ∈ carriedPairs cs car ops) : p.2.1 ∈ car :=
  (List.of_mem_zip (List.of_mem_zip h).2).1

theorem defsR_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, DefsR i := by
  have hc : ∀ p ∈ ifResPairs rs d ops, ExportRegName p.2.1 :=
    fun p hp => exportRegName_carriedRegs (tgt_carriedPairs hp)
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · simp at hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact defsR_movI _ (exportRegName_regName _)
      · refine defsR_arrParMoves _ (exportRegName_regName _) (fun a ha => ?_) i hi
        obtain ⟨p, hp, he⟩ := dst_mem_arrPairs ha
        exact he ▸ hc p hp
  · refine defsR_parMoves _ _ (fun x hx => ?_) i hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, hp, he⟩ := fst_mem_regPairs hq
    exact he ▸ hc p hp

theorem defsR_flagWord {r z : String} (op : LOperand) (hr : ExportRegName r)
    (hz : ExportRegName z) : ∀ i ∈ flagWord x86Data r z op, DefsR i := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact defsR_movI _ hr
    · exact defsR_movI _ hz
    · exact defsR_reg rfl hr
  · simp only [List.mem_singleton] at hi
    subst hi
    exact defsR_movI _ hr

theorem defsR_loopGuard {ctr : String} (top : LLabel) (h : ExportRegName ctr) :
    ∀ i ∈ (x86Data.loopGuard ctr top).map guardI, DefsR i := by
  intro i hi
  simp only [List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact defsR_reg rfl h
  · exact defsR_nonLopn fun _ _ _ e => by cases e

theorem defsR_zeroTripGuard {ctr : String} (top endL : LLabel) (h : ExportRegName ctr) :
    ∀ i ∈ (x86Data.zeroTripGuard ctr top endL).map guardI, DefsR i := by
  intro i hi
  simp only [List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact defsR_reg rfl h
  · exact defsR_nonLopn fun _ _ _ e => by cases e

theorem defsR_labelI (l : LLabel) : DefsR (labelI l) :=
  defsR_nonLopn fun _ _ _ e => by cases e

theorem defsR_forArrFrame (d n : Nat) (cs : List JasminTy) (initOps : List LOperand)
    (countOp : LOperand) {bodyC : List LinstrRM} (bodyOps : List LOperand) (bodyD : Nat)
    (hb : ∀ i ∈ bodyC, DefsR i) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data, DefsR i := by
  have hr := exportRegName_regName
  have hcar : ∀ (ops : List LOperand) p, p ∈ carriedPairs cs (carriedRegs (d + 1) cs.length) ops →
      ExportRegName p.2.1 := fun _ _ hp => exportRegName_carriedRegs (tgt_carriedPairs hp)
  have hsh : ∀ p ∈ shiftPairs d cs, ExportRegName p.2.1 := by
    intro p hp
    exact exportRegName_carriedRegs
      (List.of_mem_zip (List.of_mem_zip (List.mem_reverse.mp hp)).2).1
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact defsR_movI _ (hr _)
  · exact defsR_typedMoves (hr _) (hcar _) i hi
  · exact defsR_seedMoves _ (by simp [exportRegName_loopCtr]) i hi
  · exact defsR_zeroTripGuard n (n + 1) (exportRegName_loopCtr n) i hi
  · exact defsR_labelI _
  · exact hb i hi
  · exact defsR_movI _ (hr _)
  · refine defsR_arrParMoves _ (hr _) (fun a ha => ?_) i hi
    obtain ⟨p, hp, he⟩ := dst_mem_arrPairs ha
    exact he ▸ hcar _ p hp
  · refine defsR_parMoves _ _ (fun x hx => ?_) i hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, hp, he⟩ := fst_mem_regPairs hq
    exact he ▸ hcar _ p hp
  · exact defsR_advanceOps (hr _) (exportRegName_loopCtr _) i hi
  · exact defsR_loopGuard n (exportRegName_loopCtr n) i hi
  · exact defsR_labelI _
  · exact defsR_movI _ (hr _)
  · exact defsR_typedMoves (hr _) hsh i hi

theorem defsR_ifFrame (fn : String) (d n : Nat) (rs : List JasminTy) (condOp : LOperand)
    {thnC : List LinstrRM} (thnOps : List LOperand) (thnD : Nat) {elsC : List LinstrRM}
    (elsOps : List LOperand) (elsD : Nat) (ht : ∀ i ∈ thnC, DefsR i)
    (he : ∀ i ∈ elsC, DefsR i) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data, DefsR i := by
  have hr := exportRegName_regName
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact defsR_flagWord _ (hr _) (hr _) i hi
  · exact defsR_zeroTripGuard n (n + 1) (hr d) i hi
  · exact defsR_labelI _
  · exact ht i hi
  · exact defsR_ifResMoves _ _ _ _ i hi
  · exact defsR_movI _ (hr _)
  · exact defsR_loopGuard (n + 2) (hr _) i hi
  · exact defsR_labelI _
  · exact he i hi
  · exact defsR_ifResMoves _ _ _ _ i hi
  · exact defsR_labelI _

theorem defsR_whileFrame (d n nCar : Nat) (initOps : List LOperand) {bodyC : List LinstrRM}
    (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat) (hb : ∀ i ∈ bodyC, DefsR i) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data, DefsR i := by
  have hr := exportRegName_regName
  have hcar : ∀ x ∈ carriedRegs d nCar, ExportRegName x := fun _ h => exportRegName_carriedRegs h
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact defsR_seedMoves _ hcar i hi
  · exact defsR_labelI _
  · exact hb i hi
  · exact defsR_flagWord _ (hr _) (hr _) i hi
  · exact defsR_parMoves _ _ hcar i hi
  · exact defsR_loopGuard n (hr _) i hi

/-- **The names the region export writes are export register names**: every name an
    instruction of the code of the export `exportR` on x86 writes (`defNames`) begins with
    `r` or `L`. The bindings and calls write `regName d`, the frames write the carried blocks
    `carriedRegs`, the loop counters `loopCtr` and temporaries `regName`, and the array moves
    store into carried names. -/
theorem exportR_defNames (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      ∀ i ∈ r.code, DefsR i := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      intro i hi; simp at hi
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨o, ss, tag, hb, -⟩ := bindOps_shape nArgs e d
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact defsR_reg rfl (exportRegName_regName d)
      · exact ih _ _ _ hk i hi
  | call f args k ih =>
      intro d n r h
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact defsR_reg rfl (exportRegName_regName d)
      · exact ih _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact defsR_forArrFrame _ _ _ _ _ _ _ (ihb _ _ _ hb) i hi
      · exact ihk _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact defsR_ifFrame _ _ _ _ _ _ _ _ _ (iht _ _ _ ht) (ihe _ _ _ he) i hi
      · exact ihk _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact defsR_whileFrame _ _ _ _ _ _ _ (ihb _ _ _ hb) i hi
      · exact ihk _ _ _ hk i hi

/-- A web name of an export register name is an export register name: the web name begins
    with the name. -/
theorem ExportRegName.web {x : String} (h : ExportRegName x) (n : Nat) :
    ExportRegName (x ++ "#w" ++ toString n) := by
  unfold ExportRegName at h ⊢
  rcases h with h | h <;>
    [left; right] <;>
    · obtain ⟨c, l, hl⟩ : ∃ c l, x.toList = c :: l := by
        cases hx : x.toList with
        | nil => rw [hx] at h; cases h
        | cons c l => exact ⟨c, l, rfl⟩
      rw [hl, List.head?_cons, Option.some.injEq] at h
      simp [String.toList_append, hl, h]

/-- **The written names of an exported code** on x86 of a program without `call` that passes
    `regionExportableB`: the export by `exportR_defNames`; its webs write the names the export
    writes or web names of them (`mem_defNames_renArr`), which begin with the same letter. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.defsR {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {ex : List String} {r : Exported} (h : RegionExp fn p ex r)
    (hp : regionExportableB p = true) (hc : p.callFree = true) : ∀ i ∈ r.code, DefsR i := by
  obtain ⟨r0, h0, hr | hr⟩ := h <;> subst r
  · exact exportR_defNames _ _ p _ _ r0 h0
  · have key := forall_mem_regionWebs_web
      (P := fun i => RegionCoComplete.NoShadow i ∧ DefsR i)
      (fun σ i hσ hi => ⟨RegionCoComplete.noShadow_renArr σ hi.1, fun x hx => by
        rcases mem_defNames_renArr σ hi.1 hx with hx | ⟨y, hy, rfl⟩
        · exact hi.2 x hx
        · rcases hσ y with he | ⟨n, he⟩ <;> rw [he]
          · exact hi.2 y hy
          · exact (hi.2 y hy).web n⟩) ex r0 (fun _ _ => none) (fun _ => none)
      (fun i hi => ⟨RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow
        _ _ p hp hc _ _ r0 h0 i hi, exportR_defNames _ _ p _ _ r0 h0 i hi⟩)
    exact fun i hi => (key i hi).2

/-- **The certificate of definite assignment of an exported code** on x86 of a program
    without `call` that passes `regionExportableB` (`RegionExp.cert_of_exportR`): the export
    writes export register names, which are untagged (`exportR_defNames`), and its array
    zeroings read no name (`RegionCoComplete.exportR_zeroOK`). -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.cert_x86 {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {ex : List String} {r : Exported} (h : RegionExp fn p ex r)
    (hp : regionExportableB p = true) (hc : p.callFree = true) :
    ∃ D, Cert (ExportE Γ.length r.code) r.code D ∧
      ∀ x ∈ r.res.flatMap JasminLsemExportRewrites.opNames,
        D r.code.length x ∨ ExportE Γ.length r.code x :=
  h.cert_of_exportR hp hc
    (fun r0 h0 i hi x hx => (exportR_defNames _ _ p _ _ r0 h0 i hi x hx).notTag)
    (fun r0 h0 i hi w n e => RegionCoComplete.exportR_zeroOK _ _ _ p _ _ r0 h0 i hi w n e)

/-- The returned operands of an exported code are registers. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.res_isReg {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {ex : List String} {r : Exported} (h : RegionExp fn p ex r) :
    ∀ o ∈ r.res, o = .reg (JasminLsemWidthN.operandName o) := by
  obtain ⟨r0, h0, -⟩ := id h
  rw [h.res h0]
  exact exportR_res_isReg Γ.length fn p _ _ r0 h0

/-- **The symbol-base loads of the export from those of an exported code**: the renaming of
    array positions keeps the symbol-base loads of an instruction (`symReads_renArr`), so an
    exported code without symbol-base load is the export or the webs of an export without
    one. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.symReads_export {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {ex : List String} {r : Exported} (h : RegionExp fn p ex r)
    (hp : regionExportableB p = true) (hc : p.callFree = true) {r0 : Exported}
    (h0 : exportR Γ.length fn p Γ.length 0 x86Data = some r0)
    (hsym : ∀ i ∈ r.code, symReads i = []) : ∀ i ∈ r0.code, symReads i = [] := by
  obtain ⟨r1, h1, hr⟩ := h
  obtain rfl := Option.some.inj (h1.symm.trans h0)
  have hns := RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p
    hp hc _ _ r1 h1
  rcases hr with rfl | rfl
  · exact hsym
  · intro i hi
    unfold regionWebs at hsym
    split at hsym
    · dsimp only [X86Backend.ArrWebs.webRen] at hsym
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
      have := hsym _ (List.mem_mapIdx.mpr ⟨k, hk, rfl⟩)
      rwa [RegionExportDefInitSort.symReads_renArr (hns _ (List.getElem_mem hk))] at this
    · exact hsym i hi

/-- **Definite assignment of the tagged code of the parts of an exported code at the
    argument names of the layout** (`RegionExportDefInitSort.cert_regionCoCodeS_of` at
    `RegionExp.certS_of_exportR`): for an exported code `r` (`RegionExp`) on x86 of a program
    without `call` that passes `regionExportableB`, without symbol-base load, at a layout with
    at least `Γ.length` parameters. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.cert_regionCoCodeS
    {fn : String} {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {ex : List String} {r : Exported} (h : RegionExp fn p ex r)
    (hp : regionExportableB p = true) (hc : p.callFree = true) (σ : AbiLayout)
    (nm : String → String) (hsym : ∀ i ∈ r.code, symReads i = [])
    (hlen : Γ.length ≤ σ.args.length) :
    ∃ D, Cert (ArgS σ.args.length)
      ((regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)).map
        (X86Backend.ImageCoalesceCfg.renArr tagA)) D :=
  RegionExportDefInitSort.cert_regionCoCodeS_of Γ.length (h.noShadow hp hc) σ nm hsym hlen
    (h.certS_of_exportR hp hc
      (fun r0 h0 => RegionExportDefInitSort.noTag_exportR fn p hp hc h0
        (h.symReads_export hp hc h0 hsym)
        (fun i hi x hx => (exportR_defNames _ _ p _ _ r0 h0 i hi x hx).notTag))
      (fun r0 h0 i hi w n e => RegionCoComplete.exportR_zeroOK _ _ _ p _ _ r0 h0 i hi w n e))

/-! ## 3. The written registers under the renamings of the reference -/

/-- The register names an instruction writes are among the names it writes. -/
theorem regDefs_sub_defNames (i : LinstrRM) : ∀ x ∈ regDefs i, x ∈ defNames i.1 := by
  intro x hx
  unfold regDefs memRegDefs at hx
  split_ifs at hx <;> simp_all

theorem isSome_storeHit?_renRM (τ : String → String) (i : LinstrRM) :
    (storeHit? (JasminLsemExportTransfer.renRM τ i)).isSome = (storeHit? i).isSome := by
  obtain ⟨w, tag⟩ := i
  cases tag <;>
    simp [storeHit?, JasminLsemExportTransfer.renRM, JasminLsemExportRewrites.storeStruct?_ren,
      JasminLsemExportRewrites.zeroStruct?_ren, JasminLsemExportRewrites.storeImmStruct?_ren]

/-- **The register names a renamed instruction writes are the renamed register names.** -/
theorem regDefs_renRM (τ : String → String) (i : LinstrRM) :
    regDefs (JasminLsemExportTransfer.renRM τ i) = (regDefs i).map τ := by
  unfold regDefs memRegDefs
  rw [JasminLsemExportRewrites.cmpArgs?_ren, JasminLsemExportRewrites.movRegArgs?_ren,
    isSome_storeHit?_renRM, Option.isSome_map, Option.isSome_map]
  have hd : defNames (JasminLsemExportTransfer.renRM τ i).1 = (defNames i.1).map τ :=
    defNames_renLinstrR τ i.1
  split_ifs <;> simp [hd]

/-- An array zeroing writes no register. -/
theorem regDefs_zero (d : String) (ss : List LOperand) (w n : Nat) :
    regDefs (.Lopn [.reg d] "ZEROARR" ss, .zero w n) = [] := by
  have hm : stripWidthTag "ZEROARR" ≠ "MOV" := by decide +kernel
  have hz : (storeHit? (.Lopn [.reg d] "ZEROARR" ss, .zero w n)).isSome = true := by
    simp [storeHit?, zeroStruct?]
  unfold regDefs memRegDefs
  rw [hz]
  rcases ss with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> (try cases a) <;>
    simp [JasminLsemMemFlagGuard.movRegArgs?, hm]

/-- **The renaming of array positions keeps the written registers** of an instruction that is
    no shadow instruction of a call: it renames the base of a load, which is read, and the
    destination of a store or an array zeroing, which is no register definition. -/
theorem regDefs_renArr (ρ : String → String) {i : LinstrRM}
    (h : RegionCoComplete.NoShadow i) :
    regDefs (X86Backend.ImageCoalesceCfg.renArr ρ i) = regDefs i := by
  obtain ⟨w, tag⟩ := i
  have hc : X86Backend.ImageCoalesceCfg.renCallW ρ w = w := by
    unfold X86Backend.ImageCoalesceCfg.renCallW
    rw [show LprogIsa.shadowCall? w = none from h]
  cases tag with
  | load _ _ =>
    show regDefs (X86Backend.ImageCoalesceCfg.renLoad ρ w, _) = _
    unfold X86Backend.ImageCoalesceCfg.renLoad
    split
    · split_ifs <;> rfl
    · rfl
  | store _ _ =>
    show regDefs (X86Backend.ImageCoalesceCfg.renStore ρ w, _) = _
    unfold X86Backend.ImageCoalesceCfg.renStore
    split
    · split_ifs with ho
      · subst ho; rfl
      · rfl
    · rfl
  | zero _ _ =>
    show regDefs (X86Backend.ImageCoalesceCfg.renZero ρ w, _) = _
    unfold X86Backend.ImageCoalesceCfg.renZero
    split
    · split_ifs with ho
      · subst ho
        exact (regDefs_zero _ _ _ _).trans (regDefs_zero _ _ _ _).symm
      · rfl
    · rfl
  | storeImm _ _ =>
    show regDefs (X86Backend.ImageCoalesceCfg.renStoreImm ρ w, _) = _
    unfold X86Backend.ImageCoalesceCfg.renStoreImm
    split
    · split_ifs with ho
      · subst ho; rfl
      · rfl
    · rfl
  | _ => simp only [X86Backend.ImageCoalesceCfg.renArr, hc]

theorem mem_defNames_movesOf {ps : List (String × String)} {j : LinstrRM} (hj : j ∈ movesOf ps)
    {y : String} (hy : y ∈ defNames j.1) : ∃ p ∈ ps, y = p.2 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
  simp [JasminLsemExportLower.movWire, defNames_Lopn, JasminLsemExportRewrites.opNames] at hy
  exact ⟨p, hp, hy⟩

/-- The register names the result copy `resCopyCode` writes are its index and scratch
    registers; its stores write the versions of the result buffer, which are array names. -/
theorem regDefs_resCopyCode (src D : String) (m : Nat) :
    ∀ j ∈ resCopyCode src D m, ∀ y ∈ regDefs j, ExportRegName y := by
  intro j hj y hy
  obtain ⟨l, -, hj⟩ := List.mem_flatMap.mp hj
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · have := regDefs_sub_defNames _ y hy
    simp [movImmI, movI, defNames_Lopn, JasminLsemExportRewrites.opNames] at this
    exact this ▸ exportRegName_copyIdx
  · have := regDefs_sub_defNames _ y hy
    simp [defNames_Lopn, JasminLsemExportRewrites.opNames] at this
    exact this ▸ exportRegName_copyTmp
  · have h0 : regDefs ((.Lopn [.reg (copyName D (l + 1))] "STOREIDX"
        [.arrIdx (copyName D l) copyIdx 8, .reg copyTmp], .store 64 m) : LinstrRM) = [] := rfl
    rw [h0] at hy
    cases hy

/-- The pairs `certArgs σ cert` fix every export register name: their first components are
    argument names. -/
theorem renOf_certArgs_of_ne (σ : AbiLayout) (cert : List (String × String))
    {y : String} (hy : ∀ j, y ≠ argName j) : renOf (certArgs σ cert) y = y := by
  apply JasminLsemRenameLoop.renOf_of_not_mem
  intro hm
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  have hb := (List.mem_filter.mp hq).2
  simp only [isArgNameB, List.any_eq_true, List.mem_range, beq_iff_eq] at hb
  obtain ⟨j, -, hj⟩ := hb
  exact hy j hj.symm

theorem renOf_certArgs_of_exportRegName (σ : AbiLayout) (cert : List (String × String))
    {y : String} (hy : ExportRegName y) : renOf (certArgs σ cert) y = y :=
  renOf_certArgs_of_ne σ cert hy.ne_argName

/-- A hardware register name is not empty and no argument name. -/
theorem hw_ne {y : String} (hy : isHwRegName y = true) : y ≠ "" ∧ ∀ j, y ≠ argName j := by
  have hall : ∀ z ∈ hwRegNames, z.toList.head? ≠ none ∧ z.toList.head? ≠ some 'a' := by
    decide
  have hm : y ∈ hwRegNames := by simpa [isHwRegName, List.contains_iff_mem] using hy
  obtain ⟨h1, h2⟩ := hall y hm
  refine ⟨fun he => h1 (by simp [he]), fun j he => h2 ?_⟩
  rw [he]
  simp [argName, String.toList_append]

/-- **The register names the reference writes** (`regDefs_regionCoParts_ren`). For exported
    code `code` whose instructions write export register names and contain no shadow
    instruction of a call, every register name that an instruction at the position `k` of
    the renamed code `ren` of the parts `regionCoParts σ nm body t code res cert` without a
    callee writes is an export register name, or the instruction is the last one and the
    name is the image under the pairs `ps` of a target of the result copy. The coalescing
    renaming `renArr` keeps the register names written (`regDefs_renArr`), the pairs `ps`
    fix the export register names, and the result move `nm RA := res` of a register result
    is the last instruction of the reference. -/
theorem regDefs_regionCoParts_ren (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) {code : List LinstrRM} (res : List LOperand) (cert : List (String × String))
    (hc : ∀ i ∈ code, DefsR i) (hs : ∀ i ∈ code, RegionCoComplete.NoShadow i) :
    let d := regionCoParts σ nm body t code res cert none
    ∀ (k : Nat) (i : LinstrRM), d.ren[k]? = some i → ∀ x ∈ regDefs i,
      ExportRegName x ∨ (k + 1 = d.ren.length ∧ x ∈ d.outs.map (renOf d.ps)) := by
  intro d k i hi x hx
  let cp := regionCopy σ nm t none code res
  let C := regionCoCode σ nm t code res cp
  let ρ := canonMemrefName (regionAliasTab σ nm t none res C)
  have hren : d.ren = C.map (fun j => JasminLsemExportTransfer.renRM (renOf d.ps)
      (X86Backend.ImageCoalesceCfg.renArr ρ j)) := by
    show (regionCoBody σ nm t code res none).map _ = _
    unfold regionCoBody
    rw [List.map_map]
    rfl
  have hsC := RegionCoComplete.noShadow_regionCoCode σ nm t code res cp hs
  rw [hren, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  have hjC := List.mem_of_getElem? hj
  rw [regDefs_renRM, regDefs_renArr ρ (hsC j hjC)] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hfix : ExportRegName y → ExportRegName (renOf d.ps y) := fun h =>
    (renOf_certArgs_of_exportRegName σ cert h).symm ▸ h
  obtain ⟨R, hCR, hR⟩ : ∃ R, regionCoCode σ nm t code res (regionCopy σ nm t none code res)
      = code ++ R ∧ ∀ j ∈ R, ∀ y ∈ regDefs j, ExportRegName y ∨ (R.length = 1 ∧ y ∈ d.outs) := by
    unfold regionCoCode
    cases hcp : regionCopy σ nm t none code res with
    | none =>
      refine ⟨_, rfl, fun j hj y hy => Or.inr ?_⟩
      obtain ⟨p, hp, rfl⟩ := mem_defNames_movesOf hj (regDefs_sub_defNames j y hy)
      refine ⟨?_, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
      cases hq : regionRet σ nm t res with
      | none => rw [hq] at hp; cases hp
      | some q => simp [movesOf]
    | some c =>
      obtain ⟨src, D, m⟩ := c
      obtain ⟨-, rfl, -⟩ := regionCopy_some hcp
      refine ⟨resCopyCode src D m, by simp [regionRet, movesOf], fun j hj y hy =>
        Or.inl (regDefs_resCopyCode src D m j hj y hy)⟩
  change (regionCoCode σ nm t code res (regionCopy σ nm t none code res))[k]? = some j at hj
  rw [hren, List.length_map]
  change _ ∨ k + 1 = (regionCoCode σ nm t code res (regionCopy σ nm t none code res)).length
    ∧ _
  rw [hCR] at hj ⊢
  by_cases hk : k < code.length
  · rw [List.getElem?_append_left hk] at hj
    exact Or.inl (hfix (hc j (List.mem_of_getElem? hj) y (regDefs_sub_defNames j y hy)))
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hk)] at hj
    have hlt := (List.getElem?_eq_some_iff.mp hj).1
    rcases hR j (List.mem_of_getElem? hj) y hy with h | ⟨h1, h2⟩
    · exact Or.inl (hfix h)
    · exact Or.inr ⟨by rw [List.length_append]; omega, List.mem_map.mpr ⟨y, h2, rfl⟩⟩

/-- **The written names of the reference of a region export** (`exportR_regDefs_ren`): the
    statement of `regDefs_regionCoParts_ren` at the code of the export `exportR` on x86 of a
    program without `call` that passes `regionExportableB`. -/
theorem exportR_regDefs_ren (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) {dd n : Nat} {r : Exported}
    (hr : exportR nArgs fn p dd n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (body : Lcmd) (t : JasminTy) (cert : List (String × String)) :
    let d := regionCoParts σ nm body t r.code r.res cert none
    ∀ (k : Nat) (i : LinstrRM), d.ren[k]? = some i → ∀ x ∈ regDefs i,
      ExportRegName x ∨ (k + 1 = d.ren.length ∧ x ∈ d.outs.map (renOf d.ps)) :=
  regDefs_regionCoParts_ren σ nm body t r.res cert (exportR_defNames nArgs fn p dd n r hr)
    (RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow nArgs fn p hp
      hcf dd n r hr)

/-- **The written names of the reference are plain except the result move**: under the
    hypotheses of `regDefs_regionCoParts_ren` and the export name `nm RA` of a result
    register `RA` of the layout being a hardware register name, every name written at a
    position `k` of the renamed code is plain (`PlainName`), or the instruction is the last
    one and the name is a hardware register name. This is the written-names premise of
    `sep_regionLprogC`. -/
theorem plainDefs_regionCoParts (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) {code : List LinstrRM} (res : List LOperand) (cert : List (String × String))
    (hc : ∀ i ∈ code, DefsR i) (hs : ∀ i ∈ code, RegionCoComplete.NoShadow i)
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) :
    let d := regionCoParts σ nm body t code res cert none
    ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
      ∀ x ∈ regDefs i, PlainName x
        ∨ (k + 1 = (d.pre ++ d.ren).length ∧ isHwRegName x = true) := by
  intro d k i hk hi x hx
  rw [List.getElem?_append_right hk] at hi
  rcases regDefs_regionCoParts_ren σ nm body t res cert hc hs _ i hi x hx with h | ⟨h1, h2⟩
  · exact Or.inl h.plainName
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h2
    have hw := outs_hw_regionCoParts body t code res cert none hRA y hy
    have hfx : renOf d.ps y = y := renOf_certArgs_of_ne σ cert (hw_ne hw).2
    rw [hfx]
    change k - d.pre.length + 1 = d.ren.length at h1
    exact Or.inr ⟨by rw [List.length_append]; omega, hw⟩

/-- An instruction of the renamed code writes no empty name, under the hypotheses of
    `plainDefs_regionCoParts`. -/
theorem defs_ne_empty_regionCoParts (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) {code : List LinstrRM} (res : List LOperand) (cert : List (String × String))
    (hc : ∀ i ∈ code, DefsR i) (hs : ∀ i ∈ code, RegionCoComplete.NoShadow i)
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) :
    let d := regionCoParts σ nm body t code res cert none
    ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
      ∀ x ∈ regDefs i, x ≠ "" := by
  intro d k i hk hi x hx
  rw [List.getElem?_append_right hk] at hi
  rcases regDefs_regionCoParts_ren σ nm body t res cert hc hs _ i hi x hx with h | ⟨-, h2⟩
  · exact h.ne_empty
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h2
    have hw := outs_hw_regionCoParts body t code res cert none hRA y hy
    have hfx : renOf (regionCoParts σ nm body t code res cert).ps y = y :=
      renOf_certArgs_of_ne σ cert (hw_ne hw).2
    rw [hfx]
    exact (hw_ne hw).1

/-! ## 4. The fields of the merge conditions at the allocation -/

/-- **The merge of an allocation certificate gives the empty image to the empty name only**:
    a kept name goes to its `allocName`, which is a hardware register name, a frame-slot
    name, a vector register name or the name itself (`allocName_cases`), and every other name
    goes to itself. -/
theorem renOf_certMerge_allocCertOf_eq_empty {σ : AbiLayout} {arrs X : List String}
    {body : Lcmd} {tbl : Array Nat} {x : String}
    (h : renOf (certMerge σ arrs X (allocCertOf body tbl)) x = "") : x = "" := by
  rw [renOf_certMerge_allocCertOf] at h
  split_ifs at h
  · rcases allocName_cases body tbl x with hc | hc | hc | hc <;> rw [h] at hc
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact hc.symm
  · exact h

/-- **The merge fixes the empty name** (the field `empty` of `MergeSep`) at the certificate
    of the allocation `regionLprogC a p none ex`, when the empty name is no name of the
    certified body `regionAllocBody a Γ.length ts r`: the merge renames only names of the
    certificate. -/
theorem empty_regionLprogC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy),
        "" ∉ bodyNames (regionAllocBody a Γ.length ts r) →
        renOf (regionCoParts σ nm body t r.code r.res cert none).tau "" = "" := by
  obtain ⟨r0, r, hr, rfl, rfl⟩ := regionLprogC_cert a p ex hP
  refine ⟨r0, _, hr, rfl, fun σ nm body t hB => ?_⟩
  refine (renOf_certMerge_allocCertOf _ _ _ _ _ _ "").trans (ite_eq_right fun h => hB ?_)
  exact (List.mem_filter.mp h.1).1

/-- **No written name has the empty image** (the field `defNe` of `MergeSep`) at the
    certificate of the allocation `regionLprogC a p none ex` of a program without `call` that
    passes `regionExportableB`, when the export name `nm RA` of a result register `RA` of the
    layout is a hardware register name: the written names are export register names or that
    hardware register name (`defs_ne_empty_regionCoParts`), and the merge gives the empty
    image to the empty name only. -/
theorem defNe_regionLprogC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy),
        let d := regionCoParts σ nm body t r.code r.res cert none
        (∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) →
        ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ x ∈ regDefs i, renOf d.tau x ≠ "" := by
  obtain ⟨r0, r, hr, rfl, rfl⟩ := regionLprogC_cert a p ex hP
  refine ⟨r0, _, hr, rfl, fun σ nm body t hRA k i hk hi x hx he => ?_⟩
  exact defs_ne_empty_regionCoParts σ nm body t _ _
    ((regionExp_webs ex hr).defsR hp hcf) ((regionExp_webs ex hr).noShadow hp hcf) hRA k i hk
    hi x hx (renOf_certMerge_allocCertOf_eq_empty he)

/-- **The written-names premise of `sep_regionLprogC`** at the allocation
    `regionLprogC a p none ex` of a program without `call` that passes `regionExportableB`:
    under the export name `nm RA` of a result register `RA` of the layout being a hardware
    register name, every name written at a position of the renamed code is plain, or written
    by the last instruction and a hardware register name. -/
theorem plainDefs_regionLprogC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy),
        let d := regionCoParts σ nm body t r.code r.res cert none
        (∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) →
        ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ x ∈ regDefs i, PlainName x
            ∨ (k + 1 = (d.pre ++ d.ren).length ∧ isHwRegName x = true) := by
  obtain ⟨r0, r, hr, rfl, -⟩ := regionLprogC_cert a p ex hP
  exact ⟨r0, _, hr, rfl, fun σ nm body t hRA => plainDefs_regionCoParts σ nm body t _ cert
    ((regionExp_webs ex hr).defsR hp hcf) ((regionExp_webs ex hr).noShadow hp hcf) hRA⟩

/-! ## 5. The names live at the entry of the renamed code -/

/-- **A path through a prefix of operations**: in the code `P ++ C` whose prefix `P` consists
    of operations, every position `k ≤ P.length` ends a path from the entry whose positions
    are below `k`. -/
theorem path_prefix_of_isLopn {P C : List LinstrRM}
    (hP : ∀ y ∈ P, JasminLsemMemLoop.IsLopn y) :
    ∀ k, k ≤ P.length → ∃ ks, Path (P ++ C) k ks ∧ ∀ j ∈ ks, j < k
  | 0, _ => ⟨[], Path.nil, by simp⟩
  | k + 1, hk => by
      obtain ⟨ks, hp, hks⟩ := path_prefix_of_isLopn hP k (by omega)
      have hlt : k < P.length := by omega
      have hi : (P ++ C)[k]? = some P[k] := by
        rw [List.getElem?_append_left hlt]
        exact List.getElem?_eq_getElem hlt
      refine ⟨k :: ks, Path.cons hp hi ?_, fun j hj => ?_⟩
      · rw [webSuccs_of_isLopn (hP _ (List.getElem_mem hlt))]
        exact List.mem_singleton_self _
      · rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · exact Nat.lt_succ_of_lt (hks j hj)

/-- **The merge fixes the names live at the entry of the renamed code** (the field `entry` of
    `MergeSep`), from definite assignment. Let `d` be the parts
    `regionCoParts σ nm body t code res cert` without a callee, `C` the code `regionCoCode` with
    its array result copy and `ρ` its coalescing renaming. When `C` mentions no tagged name,
    its tagged code `C.map (renArr tagA)` has a certificate `D` of definite assignment at the
    names `E`, the merge fixes the image under `untag ρ` and the pairs `d.ps` of every name of
    `E`, every name the prefix `d.pre` reads or writes, every name an instruction of the
    renamed code writes as a name other than a register and does not read, and the targets of
    the result copy, then the merge fixes every name of the liveness table at the first
    position of the renamed code. The certificate carries over the renaming of the array
    positions (`Cert.renArrS`), the renaming by the pairs and the prefix; a name of the table
    there is in the certificate, hence written by the prefix, in `E`, or of `ArrOnly`
    (`liveRegTab_bound`). -/
theorem entry_regionCoParts (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    {E : String → Prop} {D : Nat → String → Prop} :
    let d := regionCoParts σ nm body t code res cert none
    let C := regionCoCode σ nm t code res (regionCopy σ nm t none code res)
    let ρ := canonMemrefName (regionAliasTab σ nm t none res C)
    Cert E (C.map (X86Backend.ImageCoalesceCfg.renArr tagA)) D →
    NoTag C →
    (∀ y, E y → renOf d.tau (renOf d.ps (untag ρ y)) = renOf d.ps (untag ρ y)) →
    (∀ i ∈ d.pre, ∀ x ∈ useNames i.1 ++ defNames i.1, renOf d.tau x = x) →
    (∀ i ∈ d.ren, ∀ x ∈ defNames i.1, x ∉ regDefs i → x ∉ useNames i.1 →
      renOf d.tau x = x) →
    (∀ y ∈ d.outs, renOf d.tau y = y) →
    ∀ x ∈ tabAt d.live d.pre.length, renOf d.tau x = x := by
  intro d C ρ hC hT hE hpre hA hout x hx
  have hren : d.ren = (C.map (X86Backend.ImageCoalesceCfg.renArr ρ)).map
      (JasminLsemExportTransfer.renRM (renOf d.ps)) := by
    show (regionCoBody σ nm t code res none).map _ = _
    rfl
  have hR := (RegionExportDefInitSort.Cert.renArrS hC hT ρ).renRM (renOf d.ps)
  rw [← hren] at hR
  have hR' := hR.monoE (E' := fun x => renOf d.tau x = x) (by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact hE y hy)
  have hPl : ∀ y ∈ d.pre, JasminLsemMemLoop.IsLopn y := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact JasminLsemRenameLoop.movesOf_isLopn _ y h
    · exact JasminLsemRenameLoop.movesOf_isLopn _ y h
  obtain ⟨D', hC', -⟩ := hR'.prefix d.pre hPl
    (fun y hy r hr => hpre y hy r (List.mem_append_left _ hr))
  rcases liveRegTab_bound (code := d.pre ++ d.ren) hC' (outs := d.outs)
      (fun r hr => Or.inr (hout r hr)) d.pre.length x hx with h | h | h
  · obtain ⟨ks, hp, hks⟩ := path_prefix_of_isLopn (C := d.ren) hPl d.pre.length le_rfl
    obtain ⟨j, hj, i, hi, hxi⟩ := hC'.written hp x h
    rw [List.getElem?_append_left (hks j hj)] at hi
    exact hpre i (List.mem_of_getElem? hi) x (List.mem_append_right _ hxi)
  · exact h
  · obtain ⟨i, hi, hd, hr, hu⟩ := h
    rcases List.mem_append.mp hi with hi | hi
    · exact hpre i hi x (List.mem_append_right _ hd)
    · exact hA i hi x hd hr hu

/-- A version `copyName D (k + 1)` of the result buffer is no argument name. -/
theorem copyName_succ_ne_argName (D : String) (k j : Nat) : copyName D (k + 1) ≠ argName j := by
  intro h
  have h1 : '#' ∈ (copyName D (k + 1)).toList := by
    simp [copyName, String.toList_append]
  rw [h] at h1
  simp only [argName, String.toList_append, List.mem_append] at h1
  rcases h1 with h1 | h1
  · simp at h1
  · have h2 : '#' ∈ Nat.toDigits 10 j := by
      simpa [Nat.toString_eq_repr, Nat.repr_eq_ofList_toDigits] using h1
    have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h2
    revert this
    decide

/-- **The coalescing renaming fixes a name no instruction writes**: on code without a shadow
    instruction of a call, the alias table `aliasTab outs C` has an entry only at the
    destination of a store, so it fixes every name that no instruction of `C` writes. -/
theorem canonMemrefName_aliasTab_of_not_def (outs : List (String × Nat)) {C : List LinstrRM}
    {n : String} (hs : ∀ i ∈ C, RegionCoComplete.NoShadow i)
    (hn : ∀ i ∈ C, n ∉ defNames i.1) :
    canonMemrefName (X86Backend.ImageStraightRoute.aliasTab outs C) n = n := by
  suffices h : ∀ (L : List LinstrRM) (m : Std.HashMap String String),
      (∀ i ∈ L, RegionCoComplete.NoShadow i) → (∀ i ∈ L, n ∉ defNames i.1) → m[n]? = none →
        (L.foldl (X86Backend.ImageStraightRoute.aliasStepO outs) m)[n]? = none by
    unfold canonMemrefName X86Backend.ImageStraightRoute.aliasTab
    rw [Std.HashMap.getD_eq_getD_getElem?, h C {} hs hn (by simp)]
    rfl
  intro L
  induction L with
  | nil => exact fun _ _ _ hm => hm
  | cons i L ih =>
    intro m hs hn hm
    rw [List.foldl_cons]
    refine ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj))
      (fun j hj => hn j (List.mem_cons_of_mem _ hj)) ?_
    have hn0 := hn i List.mem_cons_self
    unfold X86Backend.ImageStraightRoute.aliasStepO
    rw [show LprogIsa.shadowCall? i.1 = none from hs i List.mem_cons_self]
    dsimp only
    split
    · next dst opn base _ _ rest heq =>
      rw [heq] at hn0
      have hne : dst ≠ n := fun h => hn0 (by simp [h, defNames, JasminLsemExportRewrites.opNames])
      split_ifs
      · rw [Std.HashMap.getElem?_insert]
        simp [hne, hm]
      · exact hm
    · next dst opn base rest heq =>
      rw [heq] at hn0
      have hne : dst ≠ n := fun h => hn0 (by simp [h, defNames, JasminLsemExportRewrites.opNames])
      split_ifs
      · rw [Std.HashMap.getElem?_insert]
        simp [hne, hm]
      · exact hm
    · exact hm

/-- **The coalescing renaming with a result alias fixes a name no instruction writes**: the
    result root is zeroed by the code, so a name that no instruction of `C` writes is not the
    result root, and `canonMemrefName_aliasTab_of_not_def` applies. -/
theorem canonMemrefName_resAliasTab_of_not_def (outs : List (String × Nat))
    (rr : Option (String × String)) {C : List LinstrRM} {n : String}
    (hs : ∀ i ∈ C, RegionCoComplete.NoShadow i) (hn : ∀ i ∈ C, n ∉ defNames i.1) :
    canonMemrefName (resAliasTab outs rr C) n = n := by
  have h0 := canonMemrefName_aliasTab_of_not_def outs hs hn
  cases rr with
  | none => exact h0
  | some p =>
    obtain ⟨D, src⟩ := p
    show X86Backend.ImageStraightRoute.chainAliasRes outs D src C n = n
    rw [X86Backend.ImageStraightRoute.chainAliasRes_apply]
    split
    · rename_i r0 hr0
      obtain ⟨-, -, -, hz⟩ := X86Backend.ImageStraightRoute.resRoot?_some hr0
      obtain ⟨i, hi, hd⟩ := RegionCoComplete.exists_lopnDst_of_zeroFirstB hz
      have h0' : X86Backend.ImageStraightRoute.chainAliasO outs C n = n := h0
      rw [h0', ite_eq_right]
      rintro rfl
      refine hn i hi ?_
      obtain ⟨w, tag⟩ := i
      unfold RegionCoComplete.lopnDst at hd
      split at hd
      · rename_i hw
        cases hd
        simp only at hw
        simp [hw, defNames, JasminLsemExportRewrites.opNames]
      · cases hd
    · exact h0

/-- An instruction whose memory step writes the array `s` writes the name `s` only. -/
theorem defNames_of_storeHit? {i : LinstrRM} {s : String} (h : storeHit? i = some s) :
    defNames i.1 = [s] := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [storeHit?] at h <;> try cases h
  · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold storeStruct? at hp
    split at hp
    · split_ifs at hp
      cases hp
      simp [defNames, JasminLsemExportRewrites.opNames]
    · cases hp
  · unfold zeroStruct? at h
    split at h
    · split_ifs at h
      cases h
      simp [defNames, JasminLsemExportRewrites.opNames]
    · cases h
  · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold storeImmStruct? at hp
    split at hp
    · split_ifs at hp
      cases hp
      simp [defNames, JasminLsemExportRewrites.opNames]
    · cases hp

/-- **The merge fixes the array names an instruction of the renamed code writes**: a name an
    instruction of the renamed code of the parts writes as a name other than a register,
    when the instruction is no compare, is the array its memory step writes, an array name
    of the parts. -/
theorem fix_of_not_regDefs_ren (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    {i : LinstrRM} (hi : i ∈ (regionCoParts σ nm body t code res cert none).ren)
    (hc : (JasminLsemMemFlagGuard.cmpArgs? i).isSome = false) {x : String} (hd : x ∈ defNames i.1)
    (hr : x ∉ regDefs i) :
    renOf (regionCoParts σ nm body t code res cert none).tau x = x := by
  unfold regDefs at hr
  rw [ite_eq_right (by simp [hc])] at hr
  split_ifs at hr with h2
  · exact absurd hd hr
  · unfold memRegDefs at hr
    split_ifs at hr with h3
    · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h3
      rw [defNames_of_storeHit? hs, List.mem_singleton] at hd
      subst hd
      have ha : x ∈ arrDefs i := by
        unfold arrDefs
        rw [ite_eq_right (by simp [hc]), ite_eq_right h2]
        simp [JasminLsemExportRegAlloc.memArrDefs, hs]
      refine renOf_tau_arrs σ nm body t code res cert none x ?_
      exact List.mem_append_left _ (List.mem_append_left _ (mem_arrNames_def hi ha))
    · exact absurd hd hr

/-- An argument name of the layout is `argName j` for a parameter `j`. -/
theorem exists_of_isArgNameB {σ : AbiLayout} {x : String} (h : isArgNameB σ x = true) :
    ∃ j, j < σ.args.length ∧ x = argName j := by
  unfold isArgNameB at h
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨j, hj, rfl⟩ := h
  exact ⟨j, hj, rfl⟩

theorem isArgNameB_argName {σ : AbiLayout} {j : Nat} (h : j < σ.args.length) :
    isArgNameB σ (argName j) = true := by
  unfold isArgNameB
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨j, h, rfl⟩

/-- The merge fixes an argument name of the layout. -/
theorem renOf_certMerge_of_isArgNameB {σ : AbiLayout} {arrs X : List String}
    {cert : List (String × String)} {n : String} (h : isArgNameB σ n = true) :
    renOf (certMerge σ arrs X cert) n = n :=
  renOf_certMerge_of_not (by simp [certMergeKeep, h])

/-- **The merge fixes the image of an argument name under the allocation** when that image is
    no vector register name: it is a hardware register name, a frame-slot name or the
    argument name itself (`allocName_cases`). -/
theorem renOf_certMerge_allocName {σ : AbiLayout} {arrs X : List String} {B : Lcmd}
    {tbl : Array Nat} {cert : List (String × String)} {n : String} (h : isArgNameB σ n = true)
    (hv : allocName B tbl n ∉ vectorRegNames) :
    renOf (certMerge σ arrs X cert) (allocName B tbl n) = allocName B tbl n := by
  rcases allocName_cases B tbl n with hc | hc | hc | hc
  · exact renOf_certMerge_of_not (by simp [certMergeKeep, hc])
  · exact renOf_certMerge_of_not (by simp [certMergeKeep, hc])
  · exact absurd hc hv
  · rw [hc]
    exact renOf_certMerge_of_isArgNameB h

/-- **The merge fixes the image of an argument name under the pairs of the renaming** at an
    allocation certificate, when its image under the allocation is no vector register name. -/
theorem renOf_certMerge_certArgs {σ : AbiLayout} {arrs X : List String} {B : Lcmd}
    {tbl : Array Nat} {cert : List (String × String)} {n : String} (h : isArgNameB σ n = true)
    (hv : allocName B tbl n ∉ vectorRegNames) :
    renOf (certMerge σ arrs X cert) (renOf (certArgs σ (allocCertOf B tbl)) n)
      = renOf (certArgs σ (allocCertOf B tbl)) n := by
  unfold certArgs
  rw [renOf_filter_allocCertOf B tbl _ (isArgNameB σ) n]
  split_ifs
  · exact renOf_certMerge_allocName h hv
  · exact renOf_certMerge_of_isArgNameB h

/-- **The result copies of the code of the parts**: an instruction of `regionCoCode` is an
    instruction of the exported code, or it writes no argument name and is no compare. -/
theorem regionCoCode_suffix (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cp : Option (String × String × Nat))
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) (j : Nat) :
    ∀ i ∈ regionCoCode σ nm t code res cp, i ∈ code
      ∨ (argName j ∉ defNames i.1 ∧ JasminLsemMemFlagGuard.cmpArgs? i = none) := by
  have hmv : ∀ i ∈ movesOf (regionRet σ nm t res).toList,
      argName j ∉ defNames i.1 ∧ JasminLsemMemFlagGuard.cmpArgs? i = none := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
    have hw := outs_hw_regionCoParts (σ := σ) (nm := nm) [] t code res [] none hRA q.2
      (List.mem_map_of_mem hq)
    refine ⟨fun h => ?_, rfl⟩
    simp [JasminLsemExportLower.movWire, defNames, JasminLsemExportRewrites.opNames] at h
    exact (hw_ne hw).2 j h.symm
  have hrc : ∀ src D m, ∀ i ∈ resCopyCode src D m,
      argName j ∉ defNames i.1 ∧ JasminLsemMemFlagGuard.cmpArgs? i = none := by
    intro src D m i hi
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hi
    simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine ⟨fun h => ?_, rfl⟩
      simp [movImmI, movI, defNames, JasminLsemExportRewrites.opNames] at h
      exact exportRegName_copyIdx.ne_argName j h.symm
    · refine ⟨fun h => ?_, rfl⟩
      simp [defNames, JasminLsemExportRewrites.opNames] at h
      exact exportRegName_copyTmp.ne_argName j h.symm
    · refine ⟨fun h => ?_, by
        simp only [JasminLsemMemFlagGuard.cmpArgs?]
        rw [ite_eq_right (by decide)]⟩
      simp [defNames, JasminLsemExportRewrites.opNames] at h
      exact copyName_succ_ne_argName D k j h.symm
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with h | h
    · exact Or.inl h
    · exact Or.inr (hmv i h)
  · rcases List.mem_append.mp hi with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (hmv i h)
    · exact Or.inr (hrc _ _ _ i h)

/-- A renamed compare is the renaming of a compare. -/
theorem isSome_cmpArgs?_of_renRM (τ : String → String) {i : LinstrRM}
    (h : (JasminLsemMemFlagGuard.cmpArgs? (JasminLsemExportTransfer.renRM τ i)).isSome = true) :
    (JasminLsemMemFlagGuard.cmpArgs? i).isSome = true := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss =>
    rcases ds with _ | ⟨d, _ | _⟩ <;> rcases ss with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
      simp_all [JasminLsemMemFlagGuard.cmpArgs?, JasminLsemExportTransfer.renRM,
        JasminLsemExportTransfer.renLinstrR]
  | _ => simp [JasminLsemMemFlagGuard.cmpArgs?, JasminLsemExportTransfer.renRM,
      JasminLsemExportTransfer.renLinstrR] at h

/-- **Definite assignment of the code of the parts at the argument names of the layout**: for
    an exported code `r` (the export or its webs, `RegionExp`) of a program over `Γ` on x86
    without `call` that passes `regionExportableB`, without symbol-base loads, at a layout with
    at least `Γ.length` parameters, the code `regionCoCode` with its result copies has a
    certificate of definite assignment at the argument names `isArgNameB σ`. The exported
    code has one (`RegionExp.cert_x86`); the result move reads a returned name, and the array result
    copy reads the returned name and the result buffer, an argument name of the layout. -/
theorem cert_regionCoCode (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (σ : AbiLayout)
    (nm : String → String) (t : JasminTy) (hsym : ∀ i ∈ r.code, symReads i = [])
    (hlen : Γ.length ≤ σ.args.length) :
    ∃ D, Cert (fun y => isArgNameB σ y = true)
      (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) D := by
  have hEA : ∀ y, ExportE Γ.length r.code y → isArgNameB σ y = true := by
    rintro y (⟨j, hj, rfl⟩ | ⟨i, hi, hy⟩)
    · exact isArgNameB_argName (by omega)
    · rw [hsym i hi] at hy
      cases hy
  obtain ⟨D0, hC0, hres0⟩ := h.cert_x86 hp hc
  have hC1 := hC0.monoE hEA
  have hres : ∀ x ∈ r.res.flatMap JasminLsemExportRewrites.opNames,
      D0 r.code.length x ∨ isArgNameB σ x = true :=
    fun x hx => (hres0 x hx).imp_right (hEA x)
  have hopn : ∀ op ∈ r.res, JasminLsemWidthN.operandName op
      ∈ r.res.flatMap JasminLsemExportRewrites.opNames := by
    intro op hop
    refine List.mem_flatMap.mpr ⟨op, hop, ?_⟩
    rw [h.res_isReg op hop]
    simp [JasminLsemExportRewrites.opNames, JasminLsemWidthN.operandName]
  let L := (regionRet σ nm t r.res).toList
  have hmovs : movesOf L = L.map fun q => movI q.2 (.reg q.1) := rfl
  obtain ⟨D1, hC2, hD1⟩ : ∃ D1, Cert (fun y => isArgNameB σ y = true) (r.code ++ movesOf L) D1
      ∧ ∀ x, D0 r.code.length x → D1 (r.code ++ movesOf L).length x := by
    refine hC1.append_blk (Λ := fun _ _ => False) ?_ (JasminLsemRenameLoop.movesOf_isLopn _)
    rw [hmovs]
    refine (blk_movs (fun q => q.2) (fun q => .reg q.1) L (X := D0 r.code.length)
      (fun q hq x hx => ?_)).mono (fun _ h => h) (fun x hx => Or.inl hx)
    simp only [JasminLsemExportRewrites.opNames, List.mem_singleton] at hx
    subst hx
    change q ∈ (regionRet σ nm t r.res).toList at hq
    unfold regionRet at hq
    split at hq
    · split at hq
      · rename_i op _ hr1
        simp only [Option.toList_some, List.mem_singleton] at hq
        subst hq
        exact hres _ (hopn op (by rw [hr1]; exact List.mem_singleton_self op))
      · cases hq
    · cases hq
  unfold regionCoCode
  split
  · exact ⟨D1, hC2⟩
  · rename_i src Dn m hcp
    obtain ⟨-, -, ⟨op, hr1, hsrc⟩, ⟨j, q, hq, -, rfl⟩, -, -⟩ := regionCopy_some hcp
    have hjl : j < σ.args.length := (List.getElem?_eq_some_iff.mp hq).1
    have hs : D1 (r.code ++ movesOf L).length src ∨ isArgNameB σ src = true := by
      rcases hres src (hsrc ▸ hopn op (by rw [hr1]; exact List.mem_singleton_self op)) with
        h1 | h1
      · exact Or.inl (hD1 src h1)
      · exact Or.inr h1
    obtain ⟨D2, hC3, -⟩ := hC2.append_blk (Λ := fun _ _ => False)
      (blk_resCopy src (argName j) m hs (Or.inr (isArgNameB_argName hjl)) m)
      (isLopn_resCopyCode src (argName j) m)
    exact ⟨D2, hC3⟩

/-- The merge fixes the names the copies `movesOf qs` read and write when it fixes both
    components of every pair. -/
theorem fix_movesOf {τ : String → String} {qs : List (String × String)}
    (h : ∀ q ∈ qs, τ q.1 = q.1 ∧ τ q.2 = q.2) :
    ∀ i ∈ movesOf qs, ∀ x ∈ useNames i.1 ++ defNames i.1, τ x = x := by
  intro i hi x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
  simp only [JasminLsemExportLower.movWire, useNames, defNames,
    JasminLsemExportRewrites.opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (h q hq).1
  · exact (h q hq).2

/-! ### The code of the parts mentions no tagged name -/

theorem notTag_of_hw {y : String} (hy : isHwRegName y = true) : ¬ IsTag y := by
  have hall : ∀ z ∈ hwRegNames, z.toList.head? ≠ some '@' := by decide
  exact hall y (by simpa [isHwRegName, List.contains_iff_mem] using hy)

/-- The names the result copy into an argument name writes are untagged. -/
theorem notTag_defs_resCopyCode (src : String) (j m : Nat) :
    ∀ i ∈ resCopyCode src (argName j) m, ∀ x ∈ defNames i.1, ¬ IsTag x := by
  intro i hi x hx
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · simp [movImmI, movI, defNames, JasminLsemExportRewrites.opNames] at hx
    subst hx
    exact exportRegName_copyIdx.notTag
  · simp [defNames, JasminLsemExportRewrites.opNames] at hx
    subst hx
    exact exportRegName_copyTmp.notTag
  · simp [defNames, JasminLsemExportRewrites.opNames] at hx
    subst hx
    exact notTag_of_head (c := 'a') (by simp [copyName, argName, String.toList_append])
      (by decide)

/-- **The code of the parts mentions no tagged name**: for an exported code `r` (`RegionExp`)
    of a program without `call` that passes `regionExportableB` and has no symbol-base load, at a
    layout with at
    least `Γ.length` parameters whose result register has a hardware register name, the code
    `regionCoCode` with its result copy satisfies `NoTag`. It reads argument names or names
    written before (`cert_regionCoCode`), and it writes export register names
    (`exportR_defNames`), hardware register names and the names of the result copy into an
    argument name. -/
theorem noTag_regionCoCode (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (σ : AbiLayout)
    (nm : String → String) (t : JasminTy)
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true)
    (hsym : ∀ i ∈ r.code, symReads i = []) (hlen : Γ.length ≤ σ.args.length) :
    NoTag (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) := by
  obtain ⟨D, hC⟩ := cert_regionCoCode fn p hp hc h σ nm t hsym hlen
  have hdef := h.defsR hp hc
  have hGr := h.noGoto
  have hns := h.noShadow hp hc
  have hmv : ∀ i ∈ movesOf (regionRet σ nm t r.res).toList,
      JasminLsemMemLoop.IsLopn i ∧ ∀ x ∈ defNames i.1, ¬ IsTag x := by
    intro i hi
    refine ⟨JasminLsemRenameLoop.movesOf_isLopn _ i hi, fun x hx => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
    have hw := outs_hw_regionCoParts (σ := σ) (nm := nm) [] t r.code r.res [] none hRA q.2
      (List.mem_map_of_mem hq)
    simp [JasminLsemExportLower.movWire, defNames, JasminLsemExportRewrites.opNames] at hx
    subst hx
    exact notTag_of_hw hw
  have hrc : ∀ src D m, regionCopy σ nm t none r.code r.res = some (src, D, m) →
      ∀ i ∈ resCopyCode src D m,
        JasminLsemMemLoop.IsLopn i ∧ ∀ x ∈ defNames i.1, ¬ IsTag x := by
    intro src D m hcp i hi
    obtain ⟨-, -, -, ⟨j, -, -, -, rfl⟩, -, -⟩ := regionCopy_some hcp
    exact ⟨isLopn_resCopyCode src _ m i hi, notTag_defs_resCopyCode src j m i hi⟩
  have hparts : ∀ i ∈ regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res),
      i ∈ r.code ∨ (JasminLsemMemLoop.IsLopn i ∧ ∀ x ∈ defNames i.1, ¬ IsTag x) := by
    intro i hi
    unfold regionCoCode at hi
    split at hi
    · rcases List.mem_append.mp hi with h' | h'
      · exact Or.inl h'
      · exact Or.inr (hmv i h')
    · rename_i src D m hcp
      rcases List.mem_append.mp hi with h' | h'
      · rcases List.mem_append.mp h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (hmv i h')
      · exact Or.inr (hrc src D m hcp i h')
  refine noTag_of_cert hC (fun i hi => ?_) (fun x hx => ?_) (fun i hi => ?_)
    (RegionCoComplete.noShadow_regionCoCode σ nm t r.code r.res _ hns)
  · rcases hparts i hi with h' | h'
    · exact hGr i h'
    · exact isGoto_of_isLopn h'.1
  · obtain ⟨j, -, rfl⟩ := exists_of_isArgNameB hx
    exact notTag_argName j
  · rcases hparts i hi with h' | h'
    · exact fun x hx => (hdef i h' x hx).notTag
    · exact h'.2

/-- **The merge fixes the names live at the entry of the renamed code** (the field `entry` of
    `MergeSep`) at the certificate of the allocation `regionLprogC a p none ex` of a program
    without `call` that passes `regionExportableB`. Let `r` be the webs of the export, `B` the
    certified body, `d` the parts `regionCoParts σ nm body t r.code r.res cert`, `C` their code
    `regionCoCode` with its result copies and `ρ` its coalescing renaming. The hypotheses: the
    export names of the result register and of the parameter registers of the layout are
    hardware register names; the layout has at least `Γ.length` parameters; the allocation
    places no argument name of the layout in a vector register; the exported code has no
    symbol-base load; every compare of the exported code reads its destination; and the
    result types of the program are `[t]`. The names the tagged code reads without a prior
    write are argument names in either namespace (`cert_regionCoCodeS`), whose images under
    `untag ρ` are argument names, which the coalescing renaming fixes
    (`canonMemrefName_aliasTab_of_not_def`) and which the pairs send to images the merge
    fixes (`renOf_certMerge_certArgs`); the prefix copies the parameter registers and the
    argument names; and a name written as a name other than a register is an array name of
    the parts (`fix_of_not_regDefs_ren`). -/
theorem entry_regionLprogC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy),
        let B := regionAllocBody a Γ.length ts r
        let d := regionCoParts σ nm body t r.code r.res cert none
        (∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) →
        (∀ q ∈ σ.args, isHwRegName (nm q.reg) = true) →
        Γ.length ≤ σ.args.length →
        (∀ n, isArgNameB σ n = true → allocName B (regionAllocTbl ts B) n ∉ vectorRegNames) →
        (∀ i ∈ r.code, symReads i = []) →
        (∀ i ∈ r.code, (JasminLsemMemFlagGuard.cmpArgs? i).isSome = true →
          ∀ x ∈ defNames i.1, x ∈ useNames i.1) →
        ts = [t] →
        ∀ x ∈ tabAt d.live d.pre.length, renOf d.tau x = x := by
  obtain ⟨r0, r, hr0, rfl, rfl⟩ := regionLprogC_cert a p ex hP
  refine ⟨r0, _, hr0, rfl, ?_⟩
  have hr : RegionExp a.fname p ex (regionWebsAt ex none r0) := regionExp_webs ex hr0
  generalize regionWebsAt ex none r0 = r at hr ⊢
  intro σ nm body t B d hRA hArg hlen hvec hsym hcmp hts
  let C := regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)
  let ρ := canonMemrefName (regionAliasTab σ nm t none r.res C)
  subst hts
  have hdef := hr.defsR hp hcf
  have hns := hr.noShadow hp hcf
  have hnsC := RegionCoComplete.noShadow_regionCoCode σ nm t r.code r.res
    (regionCopy σ nm t none r.code r.res) hns
  obtain ⟨D, hC⟩ := hr.cert_regionCoCodeS hp hcf σ nm hsym hlen
  have hT := noTag_regionCoCode a.fname p hp hcf hr σ nm t hRA hsym hlen
  have hfixA : ∀ n, isArgNameB σ n = true → renOf d.tau n = n := fun n h =>
    renOf_certMerge_of_isArgNameB h
  refine entry_regionCoParts σ nm body t r.code r.res _ hC hT ?_ ?_ ?_
    (outs_regionCoParts body t r.code r.res _ none hRA)
  · intro y hy
    obtain ⟨j, hj, hyj⟩ := hy
    have hρ : ρ (argName j) = argName j := by
      refine canonMemrefName_resAliasTab_of_not_def [] _ hnsC fun i hi hm => ?_
      rcases regionCoCode_suffix σ nm t r.code r.res _ hRA j i hi with h | ⟨h, -⟩
      · exact (hdef i h _ hm).ne_argName j rfl
      · exact h hm
    have hu : untag ρ y = argName j := by
      rcases hyj with rfl | rfl
      · exact untag_of_not (notTag_argName j)
      · rw [untag_tagA]
        exact hρ
    rw [hu]
    exact renOf_certMerge_certArgs (isArgNameB_argName hj) (hvec _ (isArgNameB_argName hj))
  · intro i hi
    rcases List.mem_append.mp hi with h | h
    · refine fix_movesOf (fun q hq => ⟨?_, ?_⟩) i h
      · obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hq
        have hw := hArg _ (List.getElem_mem hj)
        unfold X86Backend.ImageAddrRoute.srcOf
        split_ifs
        · exact renOf_certMerge_of_not (by
            simp [certMergeKeep, JasminLsemAddrImage.slotOfReg, isFrameSlotName,
              hasPrefix_append])
        · exact renOf_certMerge_of_not (by simp [certMergeKeep, hw])
      · obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hq
        exact hfixA _ (isArgNameB_argName hj)
    · refine fix_movesOf (fun q hq => ?_) i h
      obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
      obtain ⟨n, m⟩ := q
      obtain ⟨-, rfl⟩ := mem_allocCertOf.mp hq1
      exact ⟨hfixA n hq2, renOf_certMerge_allocName hq2 (hvec n hq2)⟩
  · intro i hi x hd hrd hu
    by_cases hc : (JasminLsemMemFlagGuard.cmpArgs? i).isSome = true
    · exfalso
      have hi' : i ∈ (C.map (X86Backend.ImageCoalesceCfg.renArr ρ)).map
          (JasminLsemExportTransfer.renRM (renOf d.ps)) := hi
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hi'
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk0
      have hck := isSome_cmpArgs?_of_renArr ρ (isSome_cmpArgs?_of_renRM _ hc)
      rw [renArr_of_cmp ρ hck] at hd hu
      have hkc : k ∈ r.code := by
        rcases regionCoCode_suffix σ nm t r.code r.res _ hRA 0 k hk with h | ⟨-, h⟩
        · exact h
        · rw [h] at hck
          cases hck
      simp only [JasminLsemExportTransfer.renRM, defNames_renLinstrR,
        useNames_renLinstrR, List.mem_map] at hd hu
      obtain ⟨z, hz, rfl⟩ := hd
      exact hu ⟨z, hcmp k hkc hck z hz, rfl⟩
    · exact fix_of_not_regDefs_ren σ nm body t r.code r.res _ hi (by simpa using hc) hd hrd

/-- **The merge conditions at the allocation** (`mergeSep_regionLprogC`): at the certificate
    of the allocation `regionLprogC a p none ex` of a program without `call` that passes
    `regionExportableB`, the parts satisfy `MergeSep` under the hypotheses of
    `empty_regionLprogC` (the empty name is no name of the certified body), of
    `entry_regionLprogC` (with the result types `[t]` of the program), and of `sep_regionLprogC`
    apart from its written-names premise,
    which `plainDefs_regionLprogC` gives: the size bound of the allocation, a body without a
    straight-line call, and the two conditions on the live ranges of the certified body. -/
theorem mergeSep_regionLprogC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy),
        let B := regionAllocBody a Γ.length ts r
        let d := regionCoParts σ nm body t r.code r.res cert none
        let K : String → Prop := fun n => n ∈ allocCertNames B
          ∧ certMergeKeep σ d.arrs (crossNames (d.pre ++ d.ren)) n = true
        "" ∉ bodyNames B →
        (∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) →
        (∀ q ∈ σ.args, isHwRegName (nm q.reg) = true) →
        Γ.length ≤ σ.args.length →
        (∀ n, isArgNameB σ n = true → allocName B (regionAllocTbl ts B) n ∉ vectorRegNames) →
        (∀ i ∈ r.code, symReads i = []) →
        (∀ i ∈ r.code, (JasminLsemMemFlagGuard.cmpArgs? i).isSome = true →
          ∀ x ∈ defNames i.1, x ∈ useNames i.1) →
        ts = [t] →
        numGPRegs + (physLiveItems (bodyTraceOut B [])).length ≤ vectorBase →
        bodyStraightCall B = false →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, y ≠ x → K y → K x →
            ∃ pos, LiveAt (bodyTraceOut B []) pos (nameSlot B y)
              ∧ LiveAt (bodyTraceOut B []) pos (nameSlot B x)) →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, ¬ PlainName y → K x →
            y ≠ allocName B (regionAllocTbl ts B) x) →
        MergeSep d := by
  obtain ⟨r, w, hr, rfl, hE⟩ := empty_regionLprogC a p ex hP
  obtain ⟨r1, w1, hr1, rfl, hN⟩ := entry_regionLprogC a p hp hcf ex hP
  obtain ⟨r2, w2, hr2, rfl, hD⟩ := defNe_regionLprogC a p hp hcf ex hP
  obtain ⟨r3, w3, hr3, rfl, hL⟩ := plainDefs_regionLprogC a p hp hcf ex hP
  obtain ⟨r4, w4, hr4, rfl, hS⟩ := sep_regionLprogC a p ex hP
  obtain rfl : r1 = r := Option.some.inj (hr1.symm.trans hr)
  obtain rfl : r2 = r1 := Option.some.inj (hr2.symm.trans hr1)
  obtain rfl : r3 = r2 := Option.some.inj (hr3.symm.trans hr2)
  obtain rfl : r4 = r3 := Option.some.inj (hr4.symm.trans hr3)
  refine ⟨r4, _, hr4, rfl, ?_⟩
  intro σ nm body t B d K h0 hRA hArg hlen hvec hsym hcmp hts hfit hsc hcov hnp
  obtain ⟨r5, w5, hr5, rfl, rfl⟩ := regionLprogC_cert a p ex hP
  obtain rfl : r5 = r4 := Option.some.inj (hr5.symm.trans hr4)
  exact
    { empty := hE σ nm body t h0
      entry := hN σ nm body t hRA hArg hlen hvec hsym hcmp hts
      outs := outs_regionCoParts body t _ _ _ none hRA
      defNe := hD σ nm body t hRA
      sep := hS σ nm body t hRA hfit hsc (hL σ nm body t hRA) hcov hnp }

/-! ## 6. The input of the allocation without a callee -/

/-- **The input of the allocation of a region export without a callee.** Let `r` be the export
    of a program without `call` that passes `regionExportableB` and has no symbol-base load,
    over `Γ` on x86 from the depth and the argument count `Γ.length` and the label `0`, `C`
    its code followed by the array result copy `regionLprogCopy a none ts r.code r.res` (the
    code `regionLprog` gives the allocation without a callee, where `regionWebsAt` is the
    identity), `rr` the result alias `resAliasOf none (some a.outArg) ts r.res` and `σ` the
    coalescing renaming `canonMemrefName (resAliasTab [] rr C)`. When the
    output array `a.outArg` is an argument name below `Γ.length`, `C` has a certificate of
    definite assignment at the argument names and symbol operands (`ExportE`); the input
    `regionAllocCode C [] rr` of the allocation has definite assignment at the images under
    `untag σ` of the argument names in both namespaces and symbol operands (`ExportES`) and
    the `ArrOnly` names, and so has that input preceded by the entry pin; every one of its
    positions is forward reachable; and every one of its back edges targets a loop header.
    The tagged code of `C` has a certificate (`exportR_certS`, `Cert.regionLprogCopyS`) and
    `C` mentions no tagged name (`noTag_of_cert`), so `regionAllocCode_chain` applies. -/
theorem exportR_allocInput (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (a : AbiNames)
    (hout : ArgName Γ.length a.outArg) (hsym : ∀ i ∈ r.code, symReads i = []) :
    let C := r.code ++ Haxc.regionLprogCopy a none ts r.code r.res
    let rr := resAliasOf none (some a.outArg) ts r.res
    let σ := canonMemrefName (resAliasTab [] rr C)
    ∃ DC, Cert (ExportE Γ.length r.code) C DC ∧
      DefInit (fun x => img (untag σ)
            (ExportES Γ.length (r.code.map (X86Backend.ImageCoalesceCfg.renArr tagA))) x
          ∨ ArrOnly (Haxc.pinSelfMoves (C.map (X86Backend.ImageCoalesceCfg.renArr σ))) x)
          (regionAllocCode C [] rr)
        ∧ DefInit (fun x => (img (untag σ)
              (ExportES Γ.length (r.code.map (X86Backend.ImageCoalesceCfg.renArr tagA))) x
            ∨ ArrOnly (Haxc.pinSelfMoves (C.map (X86Backend.ImageCoalesceCfg.renArr σ))) x)
            ∨ ArrOnly (regionAllocCode C [] rr) x
            ∨ x ∈ (argBasePairsPos (a.outArg :: a.inArgs) a.abiArgs).map Prod.fst)
          (entryPinRM a (regionAllocCode C [] rr) ++ regionAllocCode C [] rr)
        ∧ (∀ k, k ≤ (regionAllocCode C [] rr).length → FwdPath (regionAllocCode C [] rr) k)
        ∧ ∀ k q, BackEdge (regionAllocCode C [] rr) k q →
            LoopHeader (regionAllocCode C [] rr) q k := by
  intro C rr σ
  obtain ⟨D, hC, hres⟩ := exportR_cert fn p h
  obtain ⟨DC, hCC, -⟩ := hC.regionLprogCopy a none ts r.res
    (fun t src Dn m _ hts hcopy => exportR_resCopy_defined fn p h a hout hres t src Dn m hts hcopy)
  refine ⟨DC, hCC, ?_⟩
  have hDn : ∀ t src Dn m, resCopyOf a.outArg t r.code r.res = some (src, Dn, m) →
      Dn = a.outArg := by
    intro t src Dn m hcopy
    unfold resCopyOf at hcopy
    split at hcopy
    · split_ifs at hcopy
      simp only [Option.some.injEq, Prod.mk.injEq] at hcopy
      exact hcopy.2.1.symm
    · cases hcopy
  obtain ⟨DS, hCS0, hresS⟩ := exportR_certS fn p hp hc h
  obtain ⟨DS', hCS, -⟩ := RegionExportDefInitSort.Cert.regionLprogCopyS hCS0 a none ts r.res
    (fun t src Dn m _ hts hcopy => by
      refine ⟨?_, ?_⟩
      · unfold resCopyOf at hcopy
        split at hcopy
        · rename_i w m' op hr
          split_ifs at hcopy
          simp only [Option.some.injEq, Prod.mk.injEq] at hcopy
          obtain ⟨rfl, -, -⟩ := hcopy
          have := hresS (.stackArr w m', op) (by rw [hts, hr]; simp)
          rwa [sortName_of_arr rfl] at this
        · cases hcopy
      · obtain ⟨j, hj, he⟩ := hout
        rw [hDn t src Dn m hcopy]
        exact Or.inr (Or.inl ⟨j, hj, Or.inr (by rw [he])⟩))
  have hNr := exportR_nest Γ.length fn p _ _ r h
  have hGr := exportR_noGoto Γ.length fn p _ _ r h
  have hRr := exportR_regDsts Γ.length fn p _ _ r h
  have hcl := isLopn_regionLprogCopy a none ts r.code r.res
  have hNC : Nest C :=
    Nest.append hNr (nest_of_noLabel (labelsOf_of_isLopn hcl))
      (fun l hl => by simp [targetsOf_of_isLopn hcl] at hl)
      (fun l _ hI => by have := hI.mem; simp [labelsOf_of_isLopn hcl] at this)
  have hGC : NoGoto C := fun i hi => by
    rcases List.mem_append.mp hi with hi | hi
    · exact hGr i hi
    · exact isGoto_of_isLopn (hcl i hi)
  have hRC : RegDsts C := fun i hi => by
    rcases List.mem_append.mp hi with hi | hi
    · exact hRr i hi
    · exact regShape_regionLprogCopy a none ts r.code r.res i hi
  have hT : NoTag C := by
    have hdef := exportR_defNames _ _ p _ _ r h
    have hns := RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p
      hp hc _ _ r h
    obtain ⟨j, -, hj⟩ := hout
    have hcp : ∀ i ∈ Haxc.regionLprogCopy a none ts r.code r.res,
        RegionCoComplete.NoShadow i ∧ ∀ x ∈ defNames i.1, ¬ IsTag x := by
      intro i hi
      unfold Haxc.regionLprogCopy at hi
      split at hi
      · split at hi
        · next src Dn m hcopy =>
          rw [hDn _ src Dn m hcopy, hj] at hi
          exact ⟨RegionCoComplete.noShadow_resCopyCode _ _ _ i hi,
            notTag_defs_resCopyCode src j m i hi⟩
        · simp at hi
      · simp at hi
    refine noTag_of_cert hCC hGC (fun x hx => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · rcases hx with ⟨k, -, rfl⟩ | ⟨i, hi, hx⟩
      · exact notTag_argName k
      · rw [hsym i hi] at hx
        cases hx
    · rcases List.mem_append.mp hi with hi | hi
      · exact fun x hx => (hdef i hi x hx).notTag
      · exact (hcp i hi).2
    · rcases List.mem_append.mp hi with hi | hi
      · exact hns i hi
      · exact (hcp i hi).1
  obtain ⟨⟨D', hC', -⟩, hF, hL⟩ := regionAllocCode_chain hCS hT hNC hGC hRC [] rr
  exact ⟨hC'.defInit, entryPin_defInit hC' a, hF, hL⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapLive
