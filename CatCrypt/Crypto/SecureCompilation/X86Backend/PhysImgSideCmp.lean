/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass

/-!
# The free reload scratch at the compare-spill reload from the bases of the accesses

The compare-spill reload `CmpSpillReload.cmpReload` keeps the image class when the reload scan
of the base of no indexed access carries the reload scratch `reloadScratch` (`R15`) to the
position after a compare on a spilled first operand (`PhysImgPrint.cmpScratchFreeB`). This
module derives that condition from a condition on the bases and on the moves out of the reload
scratch, `noScratchBaseB`: the base of every indexed access is a general-purpose name other than
the reload scratch, and the reload scan of the reload scratch from a move of it into a
general-purpose name, after a compare on a spilled first operand, carries no reload scratch to
the position after the compare.

The reload scan of a general-purpose name other than the reload scratch carries only
general-purpose names, and it changes the carried name only at a move into the carried name. It
carries the reload scratch out of a segment only through a move of the reload scratch into a
general-purpose name whose own scan carries the reload scratch out of the segment
(`scanExit_scratch_witness`).

## Main results

* `scanExit_scratch_witness`: the move of the reload scratch through which a scan of another
  general-purpose name carries the reload scratch out of a segment.
* `cmpScratchFreeB_of_baseNoScratch`: `noScratchBaseB` implies `cmpScratchFreeB`.
* `noScratchBaseB_of_noScratchMov`: a body whose bases are general-purpose names other than the
  reload scratch and with no move of the reload scratch into a general-purpose name satisfies
  `noScratchBaseB`.
* `noScratchBaseB_append`, `noScratchBaseB_flatten`: `noScratchBaseB` of a concatenation whose
  back parts are scratch-local (`ScratchLocal`).
* `noScratchBaseB_of_scratchPrev`: a body each of whose moves of the reload scratch into a
  general-purpose name directly follows a write of the reload scratch (`scratchPrevB`)
  satisfies `noScratchBaseB` and is scratch-local.
* `physExpand_scratchPrev`, `physExpand_acc_baseR14`: the scratch moves and the bases of one
  expansion of the allocator.
* `noScratchBaseB_lfundefPhysAbiOfVirtCert`: `noScratchBaseB` on the body of the call-free
  looped physical ABI export.

The reload scan stops at every instruction other than an operation. The condition
`cmpAccFreeB` (no indexed access or constant-index array write, `isMemB`, follows a compare
with only operations between them) therefore
implies `cmpScratchFreeB` (`cmpScratchFreeB_of_cmpAccFree`), and it is carried through the
passes by a refinement of blocks (`CmpRefines`): a pass refines its input when, from every
open-compare state from which the input passes, the output passes and leaves a compare open only
when the input does.

* `cmpRefines_fuseMulHiBody`, `cmpRefines_sublist_append`, `cmpRefines_optimizeBasicBlocks`,
  `cmpRefines_foldIndexedBody`, `cmpRefines_reallocBody`, `cmpRefines_twoAddrBody`: the fusion,
  the shape of the dead-write elimination, the optimiser, the fold, the re-allocation and the
  two-address legalisation refine their inputs.
* `cmpAccFreeB_lfundefPhysAbiOfVirtCert`: `cmpAccFreeB` on the body of the export from
  `cmpAccFreeB` on the body it expands.
* `cmpScratchFreeB_twoAddrBody`: `cmpScratchFreeB` on the two-address legalisation of the
  re-allocated, folded and optimised body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
  (physExpand physExpand_eq physRmap)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (MnOf legalizeInstr_mnOf)

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The condition -/

/-- The instruction `r` is no indexed access and no constant-index array write (`isAccB`,
    `isArrImmB`), or the base of its first source (an indexed operand, or the register of a
    `ZEROARR` or `STOREIMM`) is a general-purpose name other than the reload scratch. -/
def baseNoScratchB (r : LinstrR) : Bool :=
  !(isAccB r || isArrImmB r) ||
    match r with
    | .Lopn _ _ (.arrIdx x _ _ :: _) => gpNameB x && x != reloadScratch
    | .Lopn _ _ (.reg x :: _) => !isArrImmB r || (gpNameB x && x != reloadScratch)
    | _ => true

/-- An instruction whose bases are general-purpose names other than the reload scratch
    (`baseNoScratchB`) satisfies `baseScanFreeB` at a position from which the reload scan of no
    such name carries the reload scratch out of the segment. -/
theorem baseScanFreeB_of_baseNoScratch {c : Lcmd} {m : Nat} {r : LinstrR}
    (h : ∀ x, gpNameB x = true → x ≠ reloadScratch →
      scanExit slotArr c m x ≠ some reloadScratch)
    (hb : baseNoScratchB r = true) : baseScanFreeB slotArr c m r = true := by
  cases r with
  | Lopn ds o ss =>
    rcases ss with _ | ⟨s, ss⟩
    · simp [baseScanFreeB]
    · cases s with
      | arrIdx x y sc =>
        simp only [baseScanFreeB, baseNoScratchB, Bool.or_eq_true, Bool.not_eq_true',
          Bool.and_eq_true, bne_iff_ne, ne_eq] at hb ⊢
        rcases hb with hb | hb
        · exact Or.inl hb
        · exact Or.inr (h x hb.1 hb.2)
      | reg x =>
        simp only [baseScanFreeB, baseNoScratchB, Bool.or_eq_true, Bool.not_eq_true',
          Bool.and_eq_true, bne_iff_ne, ne_eq] at hb ⊢
        rcases hb with hb | hb | hb
        · exact Or.inl hb
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr (h x hb.1 hb.2))
      | arr _ _ => simp [baseScanFreeB]
      | imm _ => simp [baseScanFreeB]
  | _ => simp [baseScanFreeB]

/-- An instruction satisfies `baseScanFreeB` at a position from which the reload scan of no
    name carries the reload scratch out of the segment. -/
theorem baseScanFreeB_of_scan {c : Lcmd} {m : Nat} {r : LinstrR}
    (h : ∀ x, scanExit slotArr c m x ≠ some reloadScratch) :
    baseScanFreeB slotArr c m r = true := by
  unfold baseScanFreeB
  split <;> simp [h]

/-- The instruction `r` at position `m` of the segment `c` is no move of the reload scratch into
    a general-purpose name, or the reload scan of the reload scratch from `m` carries no reload
    scratch out of `c`. -/
def movScanFreeB (slotArr : String → Option (String × Nat)) (c : Lcmd) (m : Nat)
    (r : LinstrR) : Bool :=
  match slotMov? r with
  | some (d, s) => !(s == reloadScratch && gpNameB d) ||
      scanExit slotArr c m reloadScratch != some reloadScratch
  | none => true

/-- **The bases and the scratch moves after the spilled compares**: the base of every indexed
    access of `body` is a general-purpose name other than the reload scratch
    (`baseNoScratchB`), and at every compare on a spilled first operand at position `k`, every
    later move of the reload scratch into a general-purpose name satisfies `movScanFreeB` on the
    segment after `k`. -/
def noScratchBaseB (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  body.all (fun j => baseNoScratchB j.li_i) &&
    (List.range body.length).all fun k =>
      match body[k]? with
      | some i => (spillCmp? i.li_i).isNone ||
          (List.range (body.drop (k + 1)).length).all fun m =>
            match (body.drop (k + 1))[m]? with
            | some j => movScanFreeB slotArr (body.drop (k + 1)) m j.li_i
            | none => true
      | none => true

/-! ## 2. The witness move of a scan that carries the reload scratch -/

/-- **The witness move.** When the reload scan of a general-purpose name `x` other than the
    reload scratch carries the reload scratch out of `c` from position `m`, some position
    `m' < m` holds a move of the reload scratch into a general-purpose name whose own scan
    carries the reload scratch out of `c`. -/
theorem scanExit_scratch_witness (slotArr : String → Option (String × Nat)) (c : Lcmd) :
    ∀ (m : Nat) (x : String), gpNameB x = true → x ≠ reloadScratch →
      scanExit slotArr c m x = some reloadScratch →
      ∃ m' j d, m' < m ∧ c[m']? = some j ∧ slotMov? j.li_i = some (d, reloadScratch) ∧
        gpNameB d = true ∧ scanExit slotArr c m' reloadScratch = some reloadScratch
  | 0, x, _, hx, h => by
    simp only [scanExit, Option.some.injEq] at h
    exact absurd h hx
  | m + 1, x, hgx, hx, h => by
    have ih := scanExit_scratch_witness slotArr c m
    unfold scanExit at h
    split at h
    · rename_i j hj
      split at h
      · rename_i d q hmov
        split_ifs at h with hdx hcond hsd
        · simp only [Bool.and_eq_true] at hcond
          by_cases hq : q = reloadScratch
          · subst hq hdx
            exact ⟨m, j, d, Nat.lt_succ_self m, hj, hmov, hgx, h⟩
          · obtain ⟨m', j', d', hlt, h1, h2, h3, h4⟩ := ih q hcond.2 hq h
            exact ⟨m', j', d', by omega, h1, h2, h3, h4⟩
        · obtain ⟨m', j', d', hlt, h1, h2, h3, h4⟩ := ih x hgx hx h
          exact ⟨m', j', d', by omega, h1, h2, h3, h4⟩
      · split at h
        · split_ifs at h
          obtain ⟨m', j', d', hlt, h1, h2, h3, h4⟩ := ih x hgx hx h
          exact ⟨m', j', d', by omega, h1, h2, h3, h4⟩
        · cases h
    · cases h

/-! ## 3. The free reload scratch -/

/-- **`noScratchBaseB` implies `cmpScratchFreeB`.** -/
theorem cmpScratchFreeB_of_baseNoScratch {body : Lcmd}
    (h : noScratchBaseB slotArr body = true) : cmpScratchFreeB slotArr body = true := by
  simp only [noScratchBaseB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hb, hm⟩ := h
  unfold cmpScratchFreeB
  refine List.all_eq_true.mpr fun k hk => ?_
  have hmk := hm k hk
  cases hbk : body[k]? with
  | none => rfl
  | some i =>
    rw [hbk] at hmk
    simp only [Bool.or_eq_true, List.all_eq_true] at hmk ⊢
    rcases hmk with hn | hmk
    · exact Or.inl hn
    refine Or.inr fun m hm' => ?_
    cases hcm : (body.drop (k + 1))[m]? with
    | none => rfl
    | some j =>
      simp only
      have hjb : j ∈ body := List.mem_of_mem_drop (List.mem_of_getElem? hcm)
      refine baseScanFreeB_of_baseNoScratch (fun x hgx hx hex => ?_) (hb j hjb)
      obtain ⟨m', j', d', hlt, h1, h2, h3, h4⟩ :=
        scanExit_scratch_witness slotArr _ m x hgx hx hex
      have hlen : m' < (body.drop (k + 1)).length := (List.getElem?_eq_some_iff.mp h1).1
      have hfree := hmk m' (List.mem_range.mpr hlen)
      rw [h1] at hfree
      simp only [movScanFreeB, h2, beq_self_eq_true, h3, Bool.and_self, Bool.not_true,
        Bool.false_or, h4, bne_self_eq_false, Bool.false_eq_true] at hfree

/-- **A body without moves of the reload scratch into general-purpose names** whose bases are
    general-purpose names other than the reload scratch satisfies `noScratchBaseB`. -/
theorem noScratchBaseB_of_noScratchMov {body : Lcmd}
    (hb : body.all (fun j => baseNoScratchB j.li_i) = true)
    (hmov : ∀ j ∈ body, ∀ d, slotMov? j.li_i = some (d, reloadScratch) → gpNameB d = false) :
    noScratchBaseB slotArr body = true := by
  simp only [noScratchBaseB, hb, Bool.true_and]
  refine List.all_eq_true.mpr fun k _ => ?_
  cases hbk : body[k]? with
  | none => rfl
  | some i =>
    simp only [Bool.or_eq_true, List.all_eq_true]
    refine Or.inr fun m _ => ?_
    cases hcm : (body.drop (k + 1))[m]? with
    | none => rfl
    | some j =>
      have hjb : j ∈ body := List.mem_of_mem_drop (List.mem_of_getElem? hcm)
      simp only [movScanFreeB]
      split
      · rename_i d s hs
        by_cases hsr : s = reloadScratch
        · subst hsr
          simp [hmov j hjb d hs]
        · simp [hsr]
      · rfl

/-! ## 4. Blocks whose scratch moves read the reload scratch inside the block -/

/-- Every move of the reload scratch into a general-purpose name in `c` reads a value written
    inside `c`: the reload scan of the reload scratch from the move carries no reload scratch out
    of `c`. -/
def ScratchLocal (slotArr : String → Option (String × Nat)) (c : Lcmd) : Prop :=
  ∀ m j d, c[m]? = some j → slotMov? j.li_i = some (d, reloadScratch) → gpNameB d = true →
    scanExit slotArr c m reloadScratch ≠ some reloadScratch

/-- The reload scan of a general-purpose name carries only general-purpose names. -/
theorem scanExit_gpName (slotArr : String → Option (String × Nat)) (c : Lcmd) :
    ∀ (m : Nat) (x y : String), gpNameB x = true → scanExit slotArr c m x = some y →
      gpNameB y = true
  | 0, x, y, hx, h => by
    simp only [scanExit, Option.some.injEq] at h
    exact h ▸ hx
  | m + 1, x, y, hx, h => by
    have ih := scanExit_gpName slotArr c m
    unfold scanExit at h
    split at h
    · split at h
      · split_ifs at h with hdx hcond
        · simp only [Bool.and_eq_true] at hcond
          exact ih _ y hcond.2 h
        · exact ih x y hx h
      · split at h
        · split_ifs at h
          exact ih x y hx h
        · cases h
    · cases h

/-- **The scratch moves of a concatenation.** When the front part is scratch-local and the scan
    of the reload scratch from position `m` of the back part carries no reload scratch out of
    it, the scan from the same position of the concatenation carries none out of it. -/
theorem scanExit_append_scratch {a c : Lcmd} (ha : ScratchLocal slotArr a)
    {m : Nat} (hc : scanExit slotArr c m reloadScratch ≠ some reloadScratch) :
    scanExit slotArr (a ++ c) (a.length + m) reloadScratch ≠ some reloadScratch := by
  rw [PhysImgSideAlloc.scanExit_append_right]
  cases hy : scanExit slotArr c m reloadScratch with
  | none => simp
  | some y =>
    simp only [Option.bind_some]
    have hy15 : y ≠ reloadScratch := fun h => hc (h ▸ hy)
    have hgy : gpNameB y = true := scanExit_gpName slotArr c m _ _ (by decide) hy
    intro hex
    obtain ⟨m', j', d', -, h1, h2, h3, h4⟩ :=
      scanExit_scratch_witness slotArr a a.length y hgy hy15 hex
    exact ha m' j' d' h1 h2 h3 h4

/-- Scratch-local parts concatenate to a scratch-local body. -/
theorem ScratchLocal.append {a c : Lcmd} (ha : ScratchLocal slotArr a)
    (hc : ScratchLocal slotArr c) : ScratchLocal slotArr (a ++ c) := by
  intro m j d hm hmov hgd
  by_cases hlt : m < a.length
  · rw [PhysImgPass.scanExit_append_left slotArr a c m _ hlt.le]
    exact ha m j d (by rwa [List.getElem?_append_left hlt] at hm) hmov hgd
  · obtain ⟨k, rfl⟩ : ∃ k, m = a.length + k := ⟨m - a.length, by omega⟩
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hm
    exact scanExit_append_scratch ha (hc k j d hm hmov hgd)

theorem ScratchLocal.nil : ScratchLocal slotArr [] := fun m j d hm => by simp at hm

/-- A body without moves of the reload scratch into general-purpose names is scratch-local. -/
theorem ScratchLocal.of_noMov {c : Lcmd}
    (h : ∀ j ∈ c, ∀ d, slotMov? j.li_i = some (d, reloadScratch) → gpNameB d = false) :
    ScratchLocal slotArr c := fun m j d hm hmov hgd => by
  rw [h j (List.mem_of_getElem? hm) d hmov] at hgd
  cases hgd

/-- **`noScratchBaseB` of a concatenation.** When both parts satisfy `noScratchBaseB` and the
    back part is scratch-local, the concatenation satisfies `noScratchBaseB`. -/
theorem noScratchBaseB_append {a c : Lcmd} (ha : noScratchBaseB slotArr a = true)
    (hc : noScratchBaseB slotArr c = true) (hcl : ScratchLocal slotArr c) :
    noScratchBaseB slotArr (a ++ c) = true := by
  simp only [noScratchBaseB, Bool.and_eq_true, List.all_eq_true] at ha hc ⊢
  obtain ⟨hba, hma⟩ := ha
  obtain ⟨hbc, hmc⟩ := hc
  refine ⟨fun j hj => (List.mem_append.mp hj).elim (hba j) (hbc j), fun k hk => ?_⟩
  have hk' : k < (a ++ c).length := List.mem_range.mp hk
  cases hbk : (a ++ c)[k]? with
  | none => rfl
  | some i =>
    simp only [Bool.or_eq_true, List.all_eq_true]
    by_cases hlt : k < a.length
    · have hma' := hma k (List.mem_range.mpr hlt)
      rw [← List.getElem?_append_left (l₂ := c) hlt, hbk] at hma'
      simp only [Bool.or_eq_true, List.all_eq_true] at hma'
      rcases hma' with hn | hma'
      · exact Or.inl hn
      refine Or.inr fun m _ => ?_
      have hdrop : (a ++ c).drop (k + 1) = a.drop (k + 1) ++ c :=
        List.drop_append_of_le_length hlt
      rw [hdrop]
      cases hcm : (a.drop (k + 1) ++ c)[m]? with
      | none => rfl
      | some j =>
        simp only [movScanFreeB]
        cases hs : slotMov? j.li_i with
        | none => rfl
        | some p =>
          obtain ⟨d, s⟩ := p
          by_cases hsr : s = reloadScratch
          swap
          · simp [hsr]
          subst hsr
          cases hgd : gpNameB d with
          | false => simp [hgd]
          | true =>
            simp only [beq_self_eq_true, hgd, Bool.and_self, Bool.not_true, Bool.false_or,
              bne_iff_ne, ne_eq]
            by_cases hlm : m < (a.drop (k + 1)).length
            · rw [PhysImgPass.scanExit_append_left slotArr _ c m _ hlm.le]
              have hfa := hma' m (List.mem_range.mpr hlm)
              rw [← List.getElem?_append_left (l₂ := c) hlm, hcm] at hfa
              simpa [movScanFreeB, hs, hgd] using hfa
            · obtain ⟨n, rfl⟩ : ∃ n, m = (a.drop (k + 1)).length + n :=
                ⟨m - (a.drop (k + 1)).length, by omega⟩
              rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hcm
              refine scanExit_append_scratch (fun m' j' d' h1 h2 h3 h4 => ?_)
                (hcl n j d hcm hs hgd)
              have hfa := hma' m' (List.mem_range.mpr (List.getElem?_eq_some_iff.mp h1).1)
              rw [h1] at hfa
              simp [movScanFreeB, h2, h3, h4] at hfa
    · obtain ⟨k', rfl⟩ : ∃ k', k = a.length + k' := ⟨k - a.length, by omega⟩
      have hk'' : k' < c.length := by simp at hk'; omega
      have hmc' := hmc k' (List.mem_range.mpr hk'')
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hbk
      rw [hbk] at hmc'
      simp only [Bool.or_eq_true, List.all_eq_true] at hmc'
      have hdrop : (a ++ c).drop (a.length + k' + 1) = c.drop (k' + 1) := by
        rw [show a.length + k' + 1 = a.length + (k' + 1) by omega, List.drop_append]
        simp
      rw [hdrop]
      exact hmc'

/-- **`noScratchBaseB` of a flattening.** When every block satisfies `noScratchBaseB` and is
    scratch-local, so is their concatenation. -/
theorem noScratchBaseB_flatten :
    ∀ {L : List Lcmd}, (∀ c ∈ L, noScratchBaseB slotArr c = true ∧ ScratchLocal slotArr c) →
      noScratchBaseB slotArr L.flatten = true ∧ ScratchLocal slotArr L.flatten
  | [], _ => ⟨by simp [noScratchBaseB], ScratchLocal.nil⟩
  | c :: L, h => by
    have ih := noScratchBaseB_flatten (L := L) fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    have hc := h c List.mem_cons_self
    rw [List.flatten_cons]
    exact ⟨noScratchBaseB_append hc.1 ih.1 ih.2, hc.2.append ih.2⟩

/-- A body without compares on a spilled first operand whose bases are general-purpose names
    other than the reload scratch satisfies `noScratchBaseB`. -/
theorem noScratchBaseB_of_noSpillCmp {c : Lcmd}
    (hb : c.all (fun j => baseNoScratchB j.li_i) = true)
    (hc : ∀ j ∈ c, spillCmp? j.li_i = none) : noScratchBaseB slotArr c = true := by
  simp only [noScratchBaseB, hb, Bool.true_and]
  refine List.all_eq_true.mpr fun k _ => ?_
  cases hbk : c[k]? with
  | none => rfl
  | some i => simp [hc i (List.mem_of_getElem? hbk)]

/-- A one-instruction block whose base is no reload scratch satisfies `noScratchBaseB`. -/
theorem noScratchBaseB_singleton {i : Linstr} (hb : baseNoScratchB i.li_i = true) :
    noScratchBaseB slotArr [i] = true := by
  simp [noScratchBaseB, hb]

/-! ## 5. Scratch moves behind a write of the reload scratch -/

/-- The instruction is no move of the reload scratch into a general-purpose name. -/
def scratchMovFreeB (r : LinstrR) : Bool :=
  match slotMov? r with
  | some (d, s) => !(s == reloadScratch && gpNameB d)
  | none => true

/-- The operand is the register `reloadScratch`. -/
def isScratchOp : LOperand → Bool
  | .reg q => q == reloadScratch
  | _ => false

/-- The instruction is an operation other than a move and a `LIVEPIN` that writes the reload
    scratch. -/
def writesScratchB (r : LinstrR) : Bool :=
  match r with
  | .Lopn ds o _ => (slotMov? r).isNone && o != "LIVEPIN" && ds.any isScratchOp
  | _ => false

/-- Every move of the reload scratch into a general-purpose name in `l` directly follows an
    instruction that writes the reload scratch (`writesScratchB`); `w` says whether the
    instruction before `l` writes it. -/
def scratchPrevB : Bool → List LinstrR → Bool
  | _, [] => true
  | w, r :: l => (scratchMovFreeB r || w) && scratchPrevB (writesScratchB r) l

theorem scratchMovFreeB_iff {r : LinstrR} :
    scratchMovFreeB r = true ↔
      ∀ d, slotMov? r = some (d, reloadScratch) → gpNameB d = false := by
  unfold scratchMovFreeB
  cases h : slotMov? r with
  | none => simp
  | some p =>
    obtain ⟨d, s⟩ := p
    by_cases hs : s = reloadScratch
    · subst hs; simp
    · simp [hs]

theorem scratchPrevB_mono : ∀ {w : Bool} (l : List LinstrR), scratchPrevB false l = true →
    scratchPrevB w l = true
  | _, [], _ => rfl
  | w, r :: l, h => by
    simp only [scratchPrevB, Bool.or_false, Bool.and_eq_true] at h ⊢
    exact ⟨by simp [h.1], h.2⟩

theorem scratchPrevB_append : ∀ {w : Bool} (a c : List LinstrR), scratchPrevB w a = true →
    scratchPrevB false c = true → scratchPrevB w (a ++ c) = true
  | _, [], c, _, hc => scratchPrevB_mono c hc
  | w, r :: a, c, ha, hc => by
    simp only [scratchPrevB, Bool.and_eq_true, List.cons_append] at ha ⊢
    exact ⟨ha.1, scratchPrevB_append a c ha.2 hc⟩

theorem scratchPrevB_flatMap {α : Type} {f : α → List LinstrR} :
    ∀ (l : List α), (∀ x ∈ l, scratchPrevB false (f x) = true) →
      scratchPrevB false (l.flatMap f) = true
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons]
    exact scratchPrevB_append _ _ (h x List.mem_cons_self)
      (scratchPrevB_flatMap l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A list without moves of the reload scratch into general-purpose names. -/
theorem scratchPrevB_of_free {w : Bool} : ∀ {l : List LinstrR},
    (∀ r ∈ l, scratchMovFreeB r = true) → scratchPrevB w l = true
  | [], _ => rfl
  | r :: l, h => by
    simp only [scratchPrevB, h r List.mem_cons_self, Bool.true_or, Bool.true_and]
    exact scratchPrevB_of_free fun r' hr' => h r' (List.mem_cons_of_mem _ hr')

/-- Removing instructions that are neither scratch moves nor writes of the reload scratch keeps
    `scratchPrevB`. -/
theorem scratchPrevB_filter (p : LinstrR → Bool) : ∀ {w : Bool} {l : List LinstrR},
    (∀ r ∈ l, p r = false → scratchMovFreeB r = true ∧ writesScratchB r = false) →
    scratchPrevB w l = true → scratchPrevB w (l.filter p) = true
  | _, [], _, _ => rfl
  | w, r :: l, hn, h => by
    simp only [scratchPrevB, Bool.and_eq_true] at h
    have hn' : ∀ r' ∈ l, p r' = false → scratchMovFreeB r' = true ∧ writesScratchB r' = false :=
      fun r' hr' => hn r' (List.mem_cons_of_mem _ hr')
    cases hp : p r with
    | true =>
      simp only [List.filter_cons, hp, ite_true, scratchPrevB, Bool.and_eq_true]
      exact ⟨h.1, scratchPrevB_filter p hn' h.2⟩
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, ite_false]
      have hr := hn r List.mem_cons_self hp
      rw [hr.2] at h
      exact scratchPrevB_mono _ (scratchPrevB_filter p hn' h.2)

/-- The position form of `scratchPrevB`: a scratch move at position `m` is at position `0` with
    `w`, or follows a write of the reload scratch. -/
theorem scratchPrevB_pos : ∀ {w : Bool} {l : List LinstrR}, scratchPrevB w l = true →
    ∀ m r, l[m]? = some r → scratchMovFreeB r = false →
      (m = 0 ∧ w = true) ∨ ∃ m' r', m = m' + 1 ∧ l[m']? = some r' ∧ writesScratchB r' = true
  | _, [], _, m, r, hm, _ => by simp at hm
  | w, a :: l, h, m, r, hm, hf => by
    simp only [scratchPrevB, Bool.and_eq_true] at h
    cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      rw [hf, Bool.false_or] at h
      exact Or.inl ⟨rfl, h.1⟩
    | succ m =>
      simp only [List.getElem?_cons_succ] at hm
      rcases scratchPrevB_pos h.2 m r hm hf with ⟨rfl, hw⟩ | ⟨m', r', rfl, h1, h2⟩
      · exact Or.inr ⟨0, a, rfl, rfl, hw⟩
      · exact Or.inr ⟨m' + 1, r', rfl, h1, h2⟩

/-- The scan of the reload scratch from just after a write of it ends there. -/
theorem scanExit_of_writesScratch {c : Lcmd} {m : Nat} {j : Linstr} (hj : c[m]? = some j)
    (hw : writesScratchB j.li_i = true) :
    scanExit slotArr c (m + 1) reloadScratch = none := by
  simp only [scanExit, hj]
  cases hr : j.li_i with
  | Lopn ds o ss =>
    rw [hr] at hw
    simp only [writesScratchB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hw
    obtain ⟨⟨hs, -⟩, hany⟩ := hw
    have : ds.any (dstHitB slotArr reloadScratch) = true := by
      obtain ⟨x, hx, hx'⟩ := List.any_eq_true.mp hany
      refine List.any_eq_true.mpr ⟨x, hx, ?_⟩
      cases x <;> simp_all [isScratchOp, dstHitB]
    simp [hs, this]
  | _ => rw [hr] at hw; simp [writesScratchB] at hw

/-- A compare on a spilled first operand writes no reload scratch. -/
theorem writesScratchB_of_spillCmp {r : LinstrR} (h : (spillCmp? r).isSome = true) :
    writesScratchB r = false := by
  unfold spillCmp? at h
  split at h
  · rename_i d opn a s
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have hd : d ≠ reloadScratch := by
        rintro rfl
        have h15 : (LOperand.reg reloadScratch).isSpill = false := by
          simp only [LOperand.isSpill, PhysAbiShape.isPrefixOf_eq_list]; decide
        rw [h15] at hc
        simp at hc
      simp [writesScratchB, isScratchOp, hd]
    · cases h
  · cases h

/-- **`noScratchBaseB` from the scratch writes.** A body whose bases are general-purpose names
    other than the reload scratch, and each of whose moves of the reload scratch into a
    general-purpose name directly follows a write of the reload scratch, satisfies
    `noScratchBaseB` and is scratch-local. -/
theorem noScratchBaseB_of_scratchPrev {c : Lcmd}
    (hb : c.all (fun j => baseNoScratchB j.li_i) = true)
    (hp : scratchPrevB false (c.map Linstr.li_i) = true) :
    noScratchBaseB slotArr c = true ∧ ScratchLocal slotArr c := by
  have hpos : ∀ m j, c[m]? = some j → scratchMovFreeB j.li_i = false →
      ∃ m' j', m = m' + 1 ∧ c[m']? = some j' ∧ writesScratchB j'.li_i = true := by
    intro m j hm hf
    rcases scratchPrevB_pos hp m j.li_i (by simp [hm]) hf with ⟨-, h⟩ | ⟨m', r', rfl, h1, h2⟩
    · cases h
    · simp only [List.getElem?_map, Option.map_eq_some_iff] at h1
      obtain ⟨j', h1, rfl⟩ := h1
      exact ⟨m', j', rfl, h1, h2⟩
  have hfree : ∀ (j : Linstr) d, slotMov? j.li_i = some (d, reloadScratch) → gpNameB d = true →
      scratchMovFreeB j.li_i = false := by
    intro j d hs hg
    simp [scratchMovFreeB, hs, hg]
  refine ⟨?_, fun m j d hm hs hg => ?_⟩
  · simp only [noScratchBaseB, hb, Bool.true_and]
    refine List.all_eq_true.mpr fun k _ => ?_
    cases hbk : c[k]? with
    | none => rfl
    | some i =>
      simp only [Bool.or_eq_true, List.all_eq_true]
      cases hsc : spillCmp? i.li_i with
      | none => exact Or.inl rfl
      | some t =>
      refine Or.inr fun m _ => ?_
      cases hcm : (c.drop (k + 1))[m]? with
      | none => rfl
      | some j =>
        simp only [movScanFreeB]
        cases hs : slotMov? j.li_i with
        | none => rfl
        | some p =>
          obtain ⟨d, s⟩ := p
          by_cases hsr : s = reloadScratch
          swap
          · simp [hsr]
          subst hsr
          cases hgd : gpNameB d with
          | false => simp [hgd]
          | true =>
            simp only [beq_self_eq_true, hgd, Bool.and_self, Bool.not_true, Bool.false_or,
              bne_iff_ne, ne_eq]
            rw [List.getElem?_drop] at hcm
            obtain ⟨m', j', he, h1, h2⟩ := hpos _ j hcm (hfree j d hs hgd)
            cases m with
            | zero =>
              have hki : k = m' := by omega
              subst hki
              rw [h1] at hbk
              cases hbk
              rw [writesScratchB_of_spillCmp (by simp [hsc])] at h2
              cases h2
            | succ n =>
              have hd : (c.drop (k + 1))[n]? = some j' := by
                rw [List.getElem?_drop]; rw [← h1]; congr 1; omega
              rw [scanExit_of_writesScratch hd h2]
              simp
  · obtain ⟨m', j', rfl, h1, h2⟩ := hpos _ j hm (hfree j d hs hg)
    rw [scanExit_of_writesScratch h1 h2]
    simp

/-! ## 6. The scratch moves of the lowering -/

theorem scratchMovFreeB_of_src {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ∀ x ∈ ss, isScratchOp x = false) : scratchMovFreeB (.Lopn ds o ss) = true :=
  scratchMovFreeB_iff.mpr fun d hd => by
    obtain ⟨o', ho⟩ := slotMov?_eq hd
    cases ho
    simp [isScratchOp] at h

theorem scratchMovFreeB_two {ds : List LOperand} {o : String} {a b : LOperand}
    {ss : List LOperand} : scratchMovFreeB (.Lopn ds o (a :: b :: ss)) = true :=
  scratchMovFreeB_iff.mpr fun d hd => by
    obtain ⟨o', ho⟩ := slotMov?_eq hd
    cases ho

theorem gpNameB_of_isSpill {n : String} (h : (LOperand.reg n).isSpill = true) :
    gpNameB n = false :=
  PhysImgFold.gpNameB_of_spill (by
    simp only [LOperand.isSpill, PhysAbiShape.isPrefixOf_eq_list] at h
    have h' : ['k', '.'].isPrefixOf n.toList = true := h
    simp only [LprogBytes.isSpillOrQsave, hasPrefix, Bool.or_eq_true]
    exact Or.inl h')

theorem scratchMovFreeB_of_isSpill {dst s : LOperand} {o : String} (h : dst.isSpill = true) :
    scratchMovFreeB (.Lopn [dst] o [s]) = true :=
  scratchMovFreeB_iff.mpr fun d hd => by
    obtain ⟨o', ho⟩ := slotMov?_eq hd
    cases ho
    exact gpNameB_of_isSpill h

theorem scratchMovFreeB_of_opn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o ≠ "MOVQ" ∧ o ≠ "MOV:64") : scratchMovFreeB (.Lopn ds o ss) = true := by
  rw [scratchMovFreeB_iff]
  intro d hd
  obtain ⟨o', ho⟩ := slotMov?_eq hd
  cases ho
  simp [slotMov?, h.1, h.2] at hd

theorem writesScratchB_r15 {o : String} {ss : List LOperand}
    (hm : slotMov? (.Lopn [.reg reloadScratch] o ss) = none) (hl : o ≠ "LIVEPIN") :
    writesScratchB (.Lopn [.reg reloadScratch] o ss) = true := by
  simp [writesScratchB, hm, hl, isScratchOp]

/-- An instruction the `LIVEPIN` filter removes is neither a scratch move nor a write of the
    reload scratch. -/
theorem neutral_of_livePin {r : Linstr} (h : PhysAbiShape.notLivePin r = false) :
    scratchMovFreeB r.li_i = true ∧ writesScratchB r.li_i = false := by
  unfold PhysAbiShape.notLivePin at h
  split at h
  · rename_i ds o ss he
    simp only [bne_eq_false_iff_eq] at h
    subst h
    rw [he]
    exact ⟨scratchMovFreeB_of_opn (by decide), by simp [writesScratchB]⟩
  · cases h

theorem isScratchOp_of_isSpill {x : LOperand} (h : x.isSpill = true) : isScratchOp x = false := by
  cases x with
  | reg n =>
    have := gpNameB_of_isSpill h
    simp only [isScratchOp, beq_eq_false_iff_ne]
    rintro rfl
    exact absurd this (by decide)
  | _ => rfl

theorem isScratchOp_r14 : isScratchOp (.reg reloadScratch2) = false := by decide

theorem legalizeMov_scratchPrev (d s : LOperand) (mov : String) (hs : isScratchOp s = false) :
    scratchPrevB false (legalizeMov d s mov) = true := by
  unfold legalizeMov
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    simp [scratchPrevB, scratchMovFreeB_of_src, hs, scratchMovFreeB_of_isSpill h.1]
  · simp [scratchPrevB, scratchMovFreeB_of_src, hs]

theorem legalizeBinop_scratchPrev (d s : LOperand) (opn mov : String)
    (hd : isScratchOp d = false) (hs : isScratchOp s = false) :
    scratchPrevB false (legalizeBinop d s opn mov) = true := by
  unfold legalizeBinop
  split <;> rename_i h1 h2 <;>
    simp [scratchPrevB, scratchMovFreeB_of_src, scratchMovFreeB_two, hs, hd,
      scratchMovFreeB_of_isSpill, h1]

theorem materializeWideImm_scratch (s : LOperand) (mov : String) (hs : isScratchOp s = false) :
    scratchPrevB false (materializeWideImm s mov).1 = true ∧
      isScratchOp (materializeWideImm s mov).2 = false := by
  unfold materializeWideImm
  split
  · split
    · exact ⟨by simp [scratchPrevB, scratchMovFreeB_of_src (ss := [.imm _]) (by simp [isScratchOp])],
        isScratchOp_r14⟩
    · exact ⟨rfl, hs⟩
  · exact ⟨rfl, hs⟩

theorem lowerTwoAddr_scratchPrev (d s0 s1 : LOperand) (opn mov : String)
    (hd : isScratchOp d = false) (h0 : isScratchOp s0 = false) (h1 : isScratchOp s1 = false) :
    scratchPrevB false (lowerTwoAddr d s0 s1 opn mov) = true := by
  have hw := materializeWideImm_scratch s1 mov h1
  unfold lowerTwoAddr
  rcases hmw : materializeWideImm s1 mov with ⟨pre, s1v⟩
  rw [hmw] at hw
  simp only at hw ⊢
  split
  · exact scratchPrevB_append _ _ hw.1 (legalizeBinop_scratchPrev _ _ _ _ hd hw.2)
  · split
    · rename_i _ hsp
      refine scratchPrevB_append _ _ (scratchPrevB_append _ _ hw.1 ?_) ?_
      · unfold scratchBinop
        split <;> simp [scratchPrevB, scratchMovFreeB_of_src, scratchMovFreeB_two, h0, hw.2]
      · simp [scratchPrevB, scratchMovFreeB_of_isSpill hsp]
    · exact scratchPrevB_append _ _ (scratchPrevB_append _ _ (legalizeMov_scratchPrev _ _ _ h0)
        hw.1) (legalizeBinop_scratchPrev _ _ _ _ hd hw.2)

theorem lowerTwoAddrShiftImm_scratchPrev (d s0 : LOperand) (v : Nat) (opn mov : String)
    (h0 : isScratchOp s0 = false) :
    scratchPrevB false (lowerTwoAddrShiftImm d s0 v opn mov) = true := by
  unfold lowerTwoAddrShiftImm
  split
  · rename_i h
    simp [scratchPrevB, scratchMovFreeB_of_src, scratchMovFreeB_two, h0,
      scratchMovFreeB_of_isSpill h]
  · split
    · simp [scratchPrevB, scratchMovFreeB_two]
    · exact scratchPrevB_append _ _ (legalizeMov_scratchPrev _ _ _ h0)
        (by simp [scratchPrevB, scratchMovFreeB_two])

theorem ne_of_isNativeShiftRotate {o : String} (h : isNativeShiftRotate o = true) :
    o ≠ "MOVQ" ∧ o ≠ "MOV:64" ∧ o ≠ "LIVEPIN" := by
  have key : ∀ o' b, stripWidthTag o' = b →
      (∀ p ∈ ["ROR:", "ROL:", "SHL:", "SHR:", "SAR:"], p.isPrefixOf b = false) →
      isNativeShiftRotate o' = false := by
    intro o' b hs hp
    simp only [isNativeShiftRotate, hs, List.any_eq_false]
    intro p hpm
    simp [hp p hpm]
  have hp : ∀ b ∈ ["MOVQ", "MOV", "LIVEPIN"],
      ∀ p ∈ ["ROR:", "ROL:", "SHL:", "SHR:", "SAR:"], p.isPrefixOf b = false := by
    intro b hb p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb hp
    simp only [PhysAbiShape.isPrefixOf_eq_list]
    rcases hb with rfl | rfl | rfl <;> rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> revert h
  · rw [key "MOVQ" "MOVQ" (by decide +kernel) (hp _ (by simp))]; simp
  · rw [key "MOV:64" "MOV" (by decide +kernel) (hp _ (by simp))]; simp
  · rw [key "LIVEPIN" "LIVEPIN" (by decide +kernel) (hp _ (by simp))]; simp

theorem lowerNativeShiftRotate_scratchPrev (d s : LOperand) (opn mov : String)
    (hs : isScratchOp s = false) (ho : isNativeShiftRotate opn = true) :
    scratchPrevB false (lowerNativeShiftRotate d s opn mov) = true := by
  obtain ⟨h1, h2, h3⟩ := ne_of_isNativeShiftRotate ho
  have hm : slotMov? (.Lopn [.reg reloadScratch] opn [.reg reloadScratch]) = none := by
    simp [slotMov?, h1, h2]
  unfold lowerNativeShiftRotate
  split
  · simp [scratchPrevB, scratchMovFreeB_of_src, hs, scratchMovFreeB_of_opn ⟨h1, h2⟩,
      writesScratchB_r15 hm h3]
  · simp [scratchPrevB, scratchMovFreeB_of_src, hs]

theorem legalizeOneSrc_scratchPrev (u64 : Bool) (opn : String) (d s : LOperand)
    (hs : isScratchOp s = false) : scratchPrevB false (legalizeOneSrc u64 opn d s) = true := by
  unfold legalizeOneSrc
  split
  · exact legalizeMov_scratchPrev d s _ hs
  · simp [scratchPrevB, scratchMovFreeB_of_src, hs]

theorem scratchMovFreeB_of_not_gp {d o : String} {s : LOperand} (h : gpNameB d = false) :
    scratchMovFreeB (.Lopn [.reg d] o [s]) = true :=
  scratchMovFreeB_iff.mpr fun d' hd => by
    obtain ⟨o', ho⟩ := slotMov?_eq hd
    cases ho
    exact h

theorem isScratchOp_of_sibNameSpill {n : String} (h : sibNameSpill n = true) :
    isScratchOp (.reg n) = false := by
  simp only [isScratchOp, beq_eq_false_iff_ne]
  rintro rfl
  have : sibNameSpill reloadScratch = false := by rw [sibNameSpill_eq_list]; decide
  rw [this] at h
  cases h

theorem legalizeSibElem_scratch (o : LOperand) (ho : isScratchOp o = false) :
    scratchPrevB false (legalizeSibElem o).1 = true ∧
      isScratchOp (legalizeSibElem o).2 = false := by
  cases o with
  | arrIdx b i sc =>
    refine ⟨?_, rfl⟩
    simp only [legalizeSibElem]
    refine scratchPrevB_of_free fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with hr | hr <;> split at hr <;> simp only [List.mem_singleton,
      List.not_mem_nil] at hr <;> subst hr <;> rename_i h <;>
      exact scratchMovFreeB_of_src (by simp [isScratchOp_of_sibNameSpill h])
  | _ => exact ⟨rfl, ho⟩

theorem legalizeMemLoad_scratchPrev (d s : LOperand) (opn mov : String)
    (hs : isScratchOp s = false) :
    scratchPrevB false (legalizeMemLoad d s opn mov) = true := by
  have hw := legalizeSibElem_scratch s hs
  unfold legalizeMemLoad
  rcases hl : legalizeSibElem s with ⟨pre, s'⟩
  rw [hl] at hw
  simp only at hw ⊢
  refine scratchPrevB_append _ _ hw.1 ?_
  split
  · rename_i h
    simp [scratchPrevB, scratchMovFreeB_of_src, hw.2, scratchMovFreeB_of_isSpill h]
  · simp [scratchPrevB, scratchMovFreeB_of_src, hw.2]

theorem gpNameB_mem14 : gpNameB ("mem." ++ reloadScratch2 ++ ".0") = false := by decide +kernel

theorem legalizeMemStore_scratchPrev (dArr addr val : LOperand) (opn mov : String)
    (ha : isScratchOp addr = false) (hv : isScratchOp val = false) :
    scratchPrevB false (legalizeMemStore dArr addr val opn mov) = true := by
  have hw := legalizeSibElem_scratch addr ha
  unfold legalizeMemStore
  rcases hl : legalizeSibElem addr with ⟨pre, a'⟩
  rw [hl] at hw
  simp only at hw ⊢
  split
  · split
    · refine scratchPrevB_append _ _ hw.1 ?_
      simp [scratchPrevB, scratchMovFreeB_of_src (ss := [.arrIdx _ _ _]) (by simp [isScratchOp]),
        scratchMovFreeB_of_src (ss := [val]) (by simp [hv]),
        scratchMovFreeB_of_not_gp gpNameB_mem14]
    · refine scratchPrevB_append _ _ hw.1 ?_
      simp [scratchPrevB, scratchMovFreeB_of_src, scratchMovFreeB_two, hv]
  · exact scratchPrevB_append _ _ hw.1
      (by simp [scratchPrevB, scratchMovFreeB_of_src, scratchMovFreeB_two, hv])
  · exact scratchPrevB_append _ _ hw.1 (by simp [scratchPrevB, scratchMovFreeB_two])

theorem legalizeMemStoreK_scratchPrev (k : Option Nat) (dArr addr val : LOperand)
    (opn mov : String) (ha : isScratchOp addr = false) (hv : isScratchOp val = false) :
    scratchPrevB false (legalizeMemStoreK k dArr addr val opn mov) = true := by
  unfold legalizeMemStoreK
  cases hc : constIdxStore? k addr val with
  | none => exact legalizeMemStore_scratchPrev _ _ _ _ _ ha hv
  | some l =>
    simp only
    unfold constIdxStore? at hc
    split at hc
    · rename_i b i sc
      split_ifs at hc with h1 hb
      all_goals
        cases k with
        | none => cases hc
        | some c =>
          simp only at hc
          split_ifs at hc with hcc
          cases hc
          refine scratchPrevB_append _ _ ?_
            (by simp [scratchPrevB, scratchMovFreeB_of_src, hv, scratchMovFreeB_of_opn])
          first
          | rfl
          | simp [scratchPrevB, scratchMovFreeB_of_src (ss := [.reg b])
              (by simp [isScratchOp_of_sibNameSpill hb])]
    · cases hc

theorem legalizeSpillDst_scratchPrev (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) (hs : ∀ x ∈ srcs, isScratchOp x = false) :
    scratchPrevB false (legalizeSpillDst dsts opn srcs) = true := by
  unfold legalizeSpillDst
  split
  · rename_i l h
    unfold cmovSpillDst? at h
    split at h
    · split at h
      · cases h
        unfold cmovSpillSeq
        refine scratchPrevB_append _ _ ?_ ?_
        · split <;> simp_all [scratchPrevB, scratchMovFreeB_of_src]
        · split
          · rename_i hd
            simp [scratchPrevB, scratchMovFreeB_two, scratchMovFreeB_of_isSpill hd]
          · simp [scratchPrevB, scratchMovFreeB_two]
      · cases h
    · cases h
  · split
    · rename_i l _ h
      unfold setccSpill? at h
      split at h
      · split_ifs at h with hc
        cases h
        simp only [Bool.and_eq_true] at hc
        have hl : opn ≠ "LIVEPIN" := by
          rintro rfl
          have : isSetccMnem "LIVEPIN" = false := by decide +kernel
          rw [this] at hc
          exact Bool.false_ne_true hc.2
        have hm : slotMov? (.Lopn [.reg reloadScratch] opn
            [.reg reloadScratch, .reg reloadScratch2]) = none := by simp [slotMov?]
        simp_all [scratchPrevB, scratchMovFreeB_of_src, scratchMovFreeB_two,
          writesScratchB_r15 hm hl]
      · cases h
    · split
      · rename_i h
        unfold andnSpill? andnSpillI? at h
        rw [CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Abi_reload,
          CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Abi_reloadSnd] at h
        split at h
        · split_ifs at h with hc
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨-, rfl⟩ := hc
          have hm : slotMov? (.Lopn [.reg reloadScratch] "ANDN:64"
              [.reg reloadScratch, .reg reloadScratch2]) = none := by simp [slotMov?]
          simp_all [scratchPrevB, scratchMovFreeB_of_src, scratchMovFreeB_two,
            writesScratchB_r15 hm (by decide : "ANDN:64" ≠ "LIVEPIN")]
        · cases h
      · simp [scratchPrevB, scratchMovFreeB_of_src hs]

theorem reloadMemrefBase_scratch (mbr : String → Option String)
    (hmbr : ∀ b q, mbr b = some q → q ≠ reloadScratch) (o : LOperand)
    (ho : isScratchOp o = false) :
    scratchPrevB false (reloadMemrefBase mbr o).1 = true ∧
      isScratchOp (reloadMemrefBase mbr o).2 = false := by
  unfold reloadMemrefBase
  split
  · split
    · rename_i q hq
      refine ⟨?_, rfl⟩
      rcases ptrLoad_cases q with hp | hp <;>
        simp [hp, scratchPrevB, scratchMovFreeB_of_src (ss := [.reg q])
          (by simpa [isScratchOp] using hmbr _ q hq)]
    · exact ⟨rfl, ho⟩
  · exact ⟨rfl, ho⟩

theorem scratchPrevB_map_li (ii : Nat) (l : List LinstrR) (h : scratchPrevB false l = true) :
    scratchPrevB false ((l.map (fun r => (⟨ii, r⟩ : Linstr))).map Linstr.li_i) = true := by
  rw [List.map_map]
  have he : (Linstr.li_i ∘ fun r => (⟨ii, r⟩ : Linstr)) = id := rfl
  rw [he, List.map_id]
  exact h

/-- **The scratch moves of one expansion.** Under an operand map whose images are no reload
    scratch and a memref base reload map whose save slots are no reload scratch, every move of
    the reload scratch into a general-purpose name in the expansion `physExpand` of an
    instruction directly follows a write of the reload scratch. -/
theorem physExpand_scratchPrev (shiftImm : ShiftImmOracle) (u64 : Bool)
    (rmap : LOperand → LOperand) (mbr : String → Option String) (i : Linstr)
    (hrmS : ∀ x, isScratchOp (rmap x) = false)
    (hmbr : ∀ b q, mbr b = some q → q ≠ reloadScratch) :
    scratchPrevB false ((physExpand shiftImm u64 rmap mbr i).map Linstr.li_i) = true := by
  obtain ⟨ii, w⟩ := i
  cases w with
  | Lopn ds o ss =>
    rw [physExpand_eq]
    dsimp only
    split
    · rename_i d _ opn s0 s1 _ heq
      cases heq
      split
      · split
        · exact scratchPrevB_map_li _ _ (lowerTwoAddrShiftImm_scratchPrev _ _ _ _ _ (hrmS _))
        · exact scratchPrevB_map_li _ _ (lowerTwoAddr_scratchPrev _ _ _ _ _ (hrmS _) (hrmS _)
            (hrmS _))
      · split
        · rename_i d' opn' addr val heq
          cases heq
          split
          · have hb := reloadMemrefBase_scratch mbr hmbr (rmap s0) (hrmS _)
            simp only [List.map_append]
            exact scratchPrevB_append _ _ (scratchPrevB_map_li _ _ hb.1)
              (scratchPrevB_map_li _ _ (legalizeMemStoreK_scratchPrev _ _ _ _ _ _ hb.2
                (hrmS _)))
          · exact scratchPrevB_map_li _ _ (legalizeSpillDst_scratchPrev _ _ _
              (by simp [hrmS]))
        · rename_i heq
          cases heq
          exact scratchPrevB_map_li _ _ (legalizeSpillDst_scratchPrev _ _ _
            (fun x hx => by
              obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
              exact hrmS y))
        · rename_i hno
          exact absurd rfl (hno _ _ _)
    · rename_i d opn s heq
      cases heq
      split
      · rename_i hns
        exact scratchPrevB_map_li _ _ (lowerNativeShiftRotate_scratchPrev _ _ _ _ (hrmS _) hns)
      · split
        · have hb := reloadMemrefBase_scratch mbr hmbr (rmap s) (hrmS _)
          simp only [List.map_append]
          exact scratchPrevB_append _ _ (scratchPrevB_map_li _ _ hb.1)
            (scratchPrevB_map_li _ _ (legalizeMemLoad_scratchPrev _ _ _ _ hb.2))
        · exact scratchPrevB_map_li _ _ (legalizeOneSrc_scratchPrev _ _ _ _ (hrmS _))
    · rename_i dsts opn srcs _ _ heq
      cases heq
      simp only [List.map_cons, List.map_nil, scratchPrevB, Bool.or_false, Bool.and_true]
      exact scratchMovFreeB_of_src (by simp [hrmS])
    · rename_i hno
      exact absurd rfl (hno _ _ _)
  | _ =>
    simp [physExpand_eq, scratchPrevB, scratchMovFreeB, slotMov?]

/-! ## 7. The bases of the expansion -/

/-- The first indexed source of the instruction, if any, is based at `R14`, and so is the
    register first source of a `ZEROARR` or `STOREIMM`. -/
def baseR14B : LinstrR → Bool
  | .Lopn _ _ (.arrIdx x _ _ :: _) => x == reloadScratch2
  | .Lopn ds o (.reg x :: ss) => !isArrImmB (.Lopn ds o (.reg x :: ss)) || x == reloadScratch2
  | _ => true

theorem baseNoScratchB_of_baseR14B {r : LinstrR} (h : baseR14B r = true) :
    baseNoScratchB r = true := by
  have h14 : gpNameB reloadScratch2 = true ∧ reloadScratch2 ≠ reloadScratch :=
    ⟨by decide, by decide⟩
  cases r with
  | Lopn ds o ss =>
    rcases ss with _ | ⟨s, ss⟩
    · simp [baseNoScratchB]
    · cases s with
      | arrIdx x y sc =>
        simp only [baseR14B, beq_iff_eq] at h
        subst h
        simp [baseNoScratchB, h14]
      | reg x =>
        simp only [baseR14B, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
        rcases h with h | rfl
        · simp [baseNoScratchB, h]
        · simp [baseNoScratchB, h14]
      | arr _ _ => simp [baseNoScratchB]
      | imm _ => simp [baseNoScratchB]
  | _ => simp [baseNoScratchB]

theorem baseR14B_of_idxFree {r : LinstrR}
    (h : PhysImgSideAlloc.idxFreeB r = true ∧ isArrImmB r = false) : baseR14B r = true := by
  unfold baseR14B
  split
  · simp [PhysImgSideAlloc.idxFreeB] at h
  · simp [h.2]
  · rfl

theorem legalizeMemLoad_baseR14 (n y mov : String) :
    (legalizeMemLoad (.reg n) (.arrIdx reloadScratch2 y 8) "LOADIDX" mov).all baseR14B
      = true := by
  simp only [legalizeMemLoad, legalizeSibElem, sibNameSpill_reloadScratch2]
  split_ifs <;> simp_all [baseR14B, isArrImmB]

theorem legalizeMemStoreK_baseR14 (kc : Option Nat) (na y v mov : String) :
    (legalizeMemStoreK kc (.reg na) (.arrIdx reloadScratch2 y 8) (.reg v) "STOREIDX" mov).all
      baseR14B = true := by
  unfold legalizeMemStoreK
  split
  · rename_i l hc
    unfold constIdxStore? at hc
    simp only at hc
    split_ifs at hc
    all_goals
      cases kc with
      | none => cases hc
      | some c =>
        simp only at hc
        split_ifs at hc
        cases hc
        simp [baseR14B, isArrImmB]
  · simp only [legalizeMemStore, legalizeSibElem, sibNameSpill_reloadScratch2]
    split <;> (try split) <;> (try split_ifs) <;> simp_all [baseR14B, isArrImmB]

/-- **The bases of the access arms.** The expansion of an indexed access whose base is
    reloaded has every indexed first source based at `R14`. -/
theorem physExpand_acc_baseR14 (shiftImm : ShiftImmOracle) (u64 : Bool)
    (rmap : LOperand → LOperand) (mbr : String → Option String) (i : Linstr)
    (hreg : ∀ n, ∃ n', rmap (.reg n) = .reg n')
    (hacc : AccForm slotArr rmap mbr i.li_i) (hA : isAccB i.li_i = true) :
    ∀ r ∈ physExpand shiftImm u64 rmap mbr i, baseR14B r.li_i = true := by
  obtain ⟨ii, w⟩ := i
  simp only at hA hacc ⊢
  cases w with
  | Lopn ds o ss =>
    have ho : o = "LOADIDX" ∨ o = "STOREIDX" := by
      have hu : LprogAsmPrinter.untagCaret o = "LOADIDX" ∨
          LprogAsmPrinter.untagCaret o = "STOREIDX" := by
        simpa [isAccB] using hA
      rw [← (hacc ds o ss rfl).2.2.2.2 (by rcases hu with h | h <;> simp [h])]
      exact hu
    obtain ⟨hL, hS, -⟩ := hacc ds o ss rfl
    rcases ho with rfl | rfl
    · obtain ⟨dn, b, y, rfl, rfl, b', y', q, hrmA, hmb, hq, hfa⟩ := hL rfl
      obtain ⟨n', hn'⟩ := hreg dn
      simp only [physExpand_eq, isNativeShiftRotate_loadIdx, isMemLoad_loadIdx,
        Bool.false_eq_true, ite_false, ite_true, hrmA, hn', reloadMemrefBase, hmb,
        ptrLoad_qsave hfa]
      have h := legalizeMemLoad_baseR14 n' y' (if hasSuffix "LOADIDX" ":64" then "MOV:64"
        else "MOV")
      intro r hr
      simp only [List.mem_append, List.mem_map] at hr
      rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
      · simp only [List.mem_singleton] at hr'
        subst hr'
        rfl
      · exact List.all_eq_true.mp h r' hr'
    · obtain ⟨dn, b, y, v, rfl, rfl, b', y', q, hrmA, hmb, hq, hfa⟩ := hS rfl
      obtain ⟨n', hn'⟩ := hreg dn
      obtain ⟨v', hv'⟩ := hreg v
      simp only [physExpand_eq, isTwoAddrBinop_storeIdx, isMemStore_storeIdx,
        Bool.false_eq_true, ite_false, ite_true, hrmA, hn', hv', reloadMemrefBase, hmb,
        ptrLoad_qsave hfa]
      intro r hr
      simp only [List.mem_append, List.mem_map] at hr
      rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
      · simp only [List.mem_singleton] at hr'
        subst hr'
        rfl
      · exact List.all_eq_true.mp (legalizeMemStoreK_baseR14 _ _ _ _ _) r' hr'
  | _ => simp [isAccB] at hA

/-! ## 8. The export -/

theorem scratchPrevB_dropLast : ∀ {w : Bool} (l : List LinstrR), scratchPrevB w l = true →
    scratchPrevB w l.dropLast = true
  | _, [], _ => rfl
  | _, [_], _ => rfl
  | w, r :: s :: l, h => by
    rw [scratchPrevB, Bool.and_eq_true] at h
    rw [List.dropLast_cons_cons, scratchPrevB, Bool.and_eq_true]
    exact ⟨h.1, scratchPrevB_dropLast (s :: l) h.2⟩

theorem abiSaveOfExt_ne_scratch {r s : String} (h : abiSaveOfExt r = some s) :
    s ≠ reloadScratch := by
  obtain ⟨rfl, hr⟩ := abiSaveOfExt_spec h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem abiSlotOfExt_ne_scratch {r s : String} (h : abiSlotOfExt r = some s) :
    s ≠ reloadScratch := by
  unfold abiSlotOfExt at h
  split at h
  · rename_i s' hs
    cases h
    exact abiSaveOfExt_ne_scratch hs
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    intro he
    have := congrArg (fun t : String => t.toList.head?) he
    simp [String.toList_append, reloadScratch] at this

theorem buildArgPtrMaterialize_free (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (inLoadMap : InLoadMap) (habi : reloadScratch ∉ abiArgs) :
    ∀ r ∈ buildArgPtrMaterialize virt tbl abiArgs inLoadMap, scratchMovFreeB r.li_i = true := by
  intro r hr
  unfold buildArgPtrMaterialize at hr
  obtain ⟨⟨abiReg, j⟩, hmem, hr⟩ := List.mem_flatMap.mp hr
  have hab : abiReg ≠ reloadScratch := by
    obtain ⟨-, -, he⟩ := List.mem_zipIdx hmem
    rintro rfl
    exact habi (he ▸ List.getElem_mem _)
  simp only at hr
  split at hr
  · simp at hr
  · split_ifs at hr <;>
      rcases hs : abiSlotOfExt abiReg with _ | s <;>
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      (try rcases hr with rfl | rfl) <;>
      first
      | exact scratchMovFreeB_of_isSpill (by assumption)
      | exact scratchMovFreeB_of_src (by
          simp only [List.mem_singleton, forall_eq, isScratchOp, beq_eq_false_iff_ne]
          first
          | exact hab
          | exact abiSlotOfExt_ne_scratch hs)

theorem scratchPrevB_filter_livePin {l : Lcmd} (h : scratchPrevB false (l.map Linstr.li_i) = true) :
    scratchPrevB false ((l.filter PhysAbiShape.notLivePin).map Linstr.li_i) = true := by
  have he : l.filter PhysAbiShape.notLivePin =
      l.filter ((fun r => PhysAbiShape.notLivePin ⟨0, r⟩) ∘ Linstr.li_i) := rfl
  rw [he, ← List.filter_map]
  exact scratchPrevB_filter _ (fun r _ hp => neutral_of_livePin (r := ⟨0, r⟩) hp) h

/-- **`noScratchBaseB` on the call-free looped physical ABI export.** Under the hypotheses of
    `PhysImgSideAlloc.fuseSiteOkB_lfundefPhysAbiOfVirtCert` that concern the accesses and
    their operands, and when no argument register of the ABI is the reload scratch, the body of
    the export satisfies `noScratchBaseB` and is scratch-local: every base of an indexed access
    is `R14`, and every move of the reload scratch into a general-purpose name directly follows
    a write of the reload scratch. -/
theorem noScratchBaseB_lfundefPhysAbiOfVirtCert
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false →
      ∀ x ∈ lopnOperands i.li_i, PhysImgSideAlloc.noIdxB x = true)
    (habi : reloadScratch ∉ abiArgs) :
    noScratchBaseB slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
        abiArgs abiTyin x86Abi posBind).1.lfd_body = true ∧
      ScratchLocal slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
        abiArgs abiTyin x86Abi posBind).1.lfd_body := by
  rw [PhysImgSideAlloc.lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf]
  let rm := fun o =>
    remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o
  have hrmE : physRmap body1 [] = rm := by
    simp only [physRmap, hcf, Bool.false_eq_true, ite_false]
    rfl
  have hmq : ∀ b q, mbr b = some q → q ≠ reloadScratch := by
    intro b q h
    rw [hmbr] at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨a, -, ha⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some hp)
    split at ha
    · rename_i s hs
      cases ha
      exact abiSlotOfExt_ne_scratch hs
    · cases ha
  have hrmS : ∀ x, isScratchOp (rm x) = false := by
    intro x
    cases x with
    | reg m =>
      simp only [rm, remapOperand, isScratchOp, beq_eq_false_iff_ne]
      intro he
      exact PhysImgSideAlloc.physRegName_not_scratch _ (by
        rw [he]; simp [FuseMulHi.fuseReloadScratches])
    | _ => simp [rm, remapOperand, isScratchOp]
  have hF : scratchPrevB false ((reloadArrImmBody mbr ((body1.flatMap
      (physExpand (PhysImgSideAlloc.certShiftImm shiftImm body1)
        (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr)).filter
          PhysAbiShape.notLivePin)).map Linstr.li_i) = true := by
    rw [PhysImgSideAlloc.reloadArrImmBody_filter_flatMap, List.map_flatMap]
    refine scratchPrevB_flatMap _ fun i hi => scratchPrevB_filter_livePin ?_
    rw [hrmE]
    by_cases hz : ∃ ds o ss, i.li_i = .Lopn ds o ss ∧ (o = "ZEROARR" ∨ o = "STOREIMM")
    · obtain ⟨ds, o, ss, hx, hz⟩ := hz
      obtain ⟨ii, w⟩ := i
      simp only at hx
      subst hx
      obtain ⟨b, q, hb, -, ⟨n, w, he⟩ | ⟨v, v', k, -, -, he⟩ | ⟨v, v', k, -, hv', he⟩⟩ :=
        PhysImgSideAlloc.reloadArrImmBody_physExpand_arrImm _ _ rm mbr ii ds o ss (hshape _ hi)
          hz (fun _ => rfl) (fun n => ⟨_, rfl⟩) <;>
        rw [he] <;> refine scratchPrevB_of_free fun r hr => ?_ <;>
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hr
      rotate_left 2
      · rcases hr with rfl | rfl | rfl
        · exact scratchMovFreeB_of_src (by simpa [isScratchOp] using hmq _ _ hb)
        · exact scratchMovFreeB_of_src (by simpa [isScratchOp, hv'] using hrmS (.reg v))
        · exact scratchMovFreeB_of_opn (by decide)
      all_goals
        rcases hr with rfl | rfl
      all_goals first
        | exact scratchMovFreeB_of_opn (by decide)
        | exact scratchMovFreeB_of_src (by simpa [isScratchOp] using hmq _ _ hb)
    · rw [PhysImgSideAlloc.reloadArrImmBody_physExpand_of_ne _ _ _ _ _ _ fun ds o ss hx =>
        not_or.mp fun hz' => hz ⟨ds, o, ss, hx, hz'⟩]
      exact physExpand_scratchPrev _ _ rm mbr i hrmS hmq
  have hFb : ∀ j ∈ reloadArrImmBody mbr ((body1.flatMap
      (physExpand (PhysImgSideAlloc.certShiftImm shiftImm body1)
        (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr)).filter
          PhysAbiShape.notLivePin), baseNoScratchB j.li_i = true := by
    intro j hj
    rw [PhysImgSideAlloc.reloadArrImmBody_filter_flatMap] at hj
    obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp hj
    replace hj := List.mem_of_mem_filter hj
    rw [hrmE] at hj
    refine baseNoScratchB_of_baseR14B ?_
    by_cases hz : ∃ ds o ss, i.li_i = .Lopn ds o ss ∧ (o = "ZEROARR" ∨ o = "STOREIMM")
    · obtain ⟨ds, o, ss, hx, hz⟩ := hz
      obtain ⟨ii, w⟩ := i
      simp only at hx
      subst hx
      obtain ⟨b, q, hb, -, ⟨n, w, he⟩ | ⟨v, v', k, -, -, he⟩ | ⟨v, v', k, -, -, he⟩⟩ :=
        PhysImgSideAlloc.reloadArrImmBody_physExpand_arrImm _ _ rm mbr ii ds o ss (hshape _ hi)
          hz (fun _ => rfl) (fun n => ⟨_, rfl⟩) <;>
        rw [he] at hj <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      · rcases hj with rfl | rfl <;> simp [baseR14B, isArrImmB]
      · rcases hj with rfl | rfl <;> simp [baseR14B, isArrImmB]
      · rcases hj with rfl | rfl | rfl <;> simp [baseR14B, isArrImmB]
    · have hne : ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM" :=
        fun ds o ss hx => not_or.mp fun hz' => hz ⟨ds, o, ss, hx, hz'⟩
      rw [PhysImgSideAlloc.reloadArrImmBody_physExpand_of_ne _ _ _ _ _ _ hne] at hj
      cases hA : isAccB i.li_i
      · exact baseR14B_of_idxFree ⟨PhysImgSideAlloc.physExpand_idxFree _ _ rm mbr i
          (fun x hx => PhysImgSideAlloc.noIdxB_remapOperand _ _ hx) (hidx i hi hA) j hj,
          PhysImgSideAlloc.physExpand_arrImmFree _ _ rm mbr i hne
            (fun ds o ss h => (hshape i hi ds o ss h).2.2.2.2) j hj⟩
      · exact physExpand_acc_baseR14 _ _ rm mbr i (fun n => ⟨_, rfl⟩) (hshape i hi) hA j hj
  have hplain : ∀ j, PhysImgSideAlloc.PlainB j → baseNoScratchB j.li_i = true :=
    fun j h => baseNoScratchB_of_baseR14B (baseR14B_of_idxFree h.2.1)
  have hPro : scratchPrevB false ((buildPrologue { virt0 with lfd_body := body1 }
      (physTableOut body1 []) (fun _ => none)).map Linstr.li_i) = true := by
    have hP : buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 [])
        (fun _ => none) = buildPrologue {} #[] (fun _ => none) := rfl
    rw [hP]
    decide +kernel
  have hX : scratchPrevB false ((extraSaves abiArgs).map Linstr.li_i) = true := by
    refine scratchPrevB_of_free fun r hr => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    obtain ⟨a, s, hs, rfl⟩ := mem_extraSaves hj
    obtain ⟨-, ha⟩ := abiSaveOfExt_spec hs
    refine scratchMovFreeB_of_src ?_
    simp only [List.mem_singleton, forall_eq, isScratchOp, beq_eq_false_iff_ne]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hM : scratchPrevB false ((buildArgPtrMaterialize { virt0 with lfd_body := body1 }
      (physTableOut body1 []) abiArgs (fun _ => none)).map Linstr.li_i) = true := by
    refine scratchPrevB_of_free fun r hr => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    exact buildArgPtrMaterialize_free _ _ _ _ habi j hj
  have hE : scratchPrevB false
      ((calleeSaveRestoreEpilogue ++ [(⟨0, .Lret⟩ : Linstr)]).map Linstr.li_i)
      = true := by decide +kernel
  refine noScratchBaseB_of_scratchPrev (List.all_eq_true.mpr fun j hj => ?_) ?_
  · simp only [insertEpilogue, List.mem_append] at hj
    rcases hj with (hj | hj) | hj | (hj | hj) | hj
    · exact hplain j (PhysImgSideAlloc.prologue_plainB _ _ abiArgs j
        (List.mem_append_left (extraSaves abiArgs) hj))
    · exact hplain j (PhysImgSideAlloc.prologue_plainB { virt0 with lfd_body := body1 }
        (physTableOut body1 []) abiArgs j (List.mem_append_right _ hj))
    · exact hplain j (PhysImgSideAlloc.buildArgPtrMaterialize_plainB _ _ _ _ j hj)
    · exact hFb j (List.dropLast_subset _ hj)
    · exact hplain j (PhysImgSideAlloc.epilogue_plainB j (List.mem_append_left _ hj))
    · exact hplain j (PhysImgSideAlloc.epilogue_plainB j (List.mem_append_right _ hj))
  · simp only [insertEpilogue, List.map_append, List.append_assoc] at hE ⊢
    refine scratchPrevB_append _ _ hPro (scratchPrevB_append _ _ hX
      (scratchPrevB_append _ _ hM (scratchPrevB_append _ _ ?_ hE)))
    rw [List.map_dropLast]
    exact scratchPrevB_dropLast _ hF

/-! ## 9. No indexed access while a compare is open -/

/-- The instruction is an operation. -/
def isOpnB : LinstrR → Bool
  | .Lopn _ _ _ => true
  | _ => false

/-- The instruction is an operation whose mnemonic has the base `CMP`. -/
def isCmpB : LinstrR → Bool
  | .Lopn _ o _ => stripWidthTag o == "CMP"
  | _ => false

/-- The open-compare state after `r` from the state `w`: an operation keeps the state and opens
    it at a compare, and every other instruction closes it. -/
def cmpOpenStep (w : Bool) (r : LinstrR) : Bool := isOpnB r && (w || isCmpB r)

/-- The open-compare state after the block `l` from the state `w`. -/
def cmpOpenAfter (w : Bool) (l : Lcmd) : Bool := l.foldl (fun w j => cmpOpenStep w j.li_i) w

/-- The instruction is an indexed access or a constant-index array write (`isAccB`,
    `isArrImmB`): an instruction with a base (`AccBase`) that the image class reads. -/
def isMemB (r : LinstrR) : Bool := isAccB r || isArrImmB r

/-- **No indexed access while a compare is open**: no indexed access or constant-index array
    write (`isMemB`) of `l` follows a compare with only operations between them; `w` says
    whether a compare is open before `l`. -/
def cmpAccFreeB : Bool → Lcmd → Bool
  | _, [] => true
  | w, j :: l => !(w && isMemB j.li_i) && cmpAccFreeB (cmpOpenStep w j.li_i) l

theorem cmpOpenAfter_cons (w : Bool) (j : Linstr) (l : Lcmd) :
    cmpOpenAfter w (j :: l) = cmpOpenAfter (cmpOpenStep w j.li_i) l := rfl

theorem cmpOpenAfter_append (w : Bool) (a b : Lcmd) :
    cmpOpenAfter w (a ++ b) = cmpOpenAfter (cmpOpenAfter w a) b := by
  simp [cmpOpenAfter, List.foldl_append]

theorem cmpAccFreeB_append : ∀ (w : Bool) (a b : Lcmd),
    cmpAccFreeB w (a ++ b) = (cmpAccFreeB w a && cmpAccFreeB (cmpOpenAfter w a) b)
  | w, [], b => by simp [cmpAccFreeB, cmpOpenAfter]
  | w, j :: a, b => by
    rw [List.cons_append, cmpAccFreeB, cmpAccFreeB, cmpAccFreeB_append, cmpOpenAfter_cons,
      Bool.and_assoc]

theorem cmpOpenStep_mono {w1 w2 : Bool} (h : w1 = true → w2 = true) (r : LinstrR) :
    cmpOpenStep w1 r = true → cmpOpenStep w2 r = true := by
  unfold cmpOpenStep
  revert h
  cases w1 <;> cases w2 <;> simp +contextual

theorem cmpOpenAfter_mono : ∀ (l : Lcmd) {w1 w2 : Bool}, (w1 = true → w2 = true) →
    cmpOpenAfter w1 l = true → cmpOpenAfter w2 l = true
  | [], _, _, h => h
  | j :: l, _, _, h => by
    rw [cmpOpenAfter_cons, cmpOpenAfter_cons]
    exact cmpOpenAfter_mono l (cmpOpenStep_mono h j.li_i)

theorem cmpAccFreeB_mono : ∀ (l : Lcmd) {w1 w2 : Bool}, (w1 = true → w2 = true) →
    cmpAccFreeB w2 l = true → cmpAccFreeB w1 l = true
  | [], _, _, _, _ => rfl
  | j :: l, w1, w2, h, h2 => by
    rw [cmpAccFreeB, Bool.and_eq_true] at h2 ⊢
    obtain ⟨h21, h22⟩ := h2
    refine ⟨?_, cmpAccFreeB_mono l (cmpOpenStep_mono h j.li_i) h22⟩
    revert h h21
    cases w1 <;> cases w2 <;> simp

theorem cmpAccFreeB_of_append_left {w : Bool} {a b : Lcmd} (h : cmpAccFreeB w (a ++ b) = true) :
    cmpAccFreeB w a = true := by
  rw [cmpAccFreeB_append, Bool.and_eq_true] at h
  exact h.1

theorem cmpAccFreeB_dropLast : ∀ {w : Bool} (l : Lcmd), cmpAccFreeB w l = true →
    cmpAccFreeB w l.dropLast = true
  | _, [], _ => rfl
  | _, [_], _ => rfl
  | w, r :: s :: l, h => by
    rw [cmpAccFreeB, Bool.and_eq_true] at h
    rw [List.dropLast_cons_cons, cmpAccFreeB, Bool.and_eq_true]
    exact ⟨h.1, cmpAccFreeB_dropLast (s :: l) h.2⟩

/-! ### Evaluation on blocks of a fixed kind -/

theorem isOpnB_of_isCmpB {r : LinstrR} (h : isCmpB r = true) : isOpnB r = true := by
  cases r <;> simp_all [isCmpB, isOpnB]

theorem isMemB_of_isCmpB {r : LinstrR} (h : isCmpB r = true) : isMemB r = false := by
  cases r with
  | Lopn ds o ss =>
    cases ha : isMemB (.Lopn ds o ss)
    · rfl
    · simp only [isMemB, isAccB, isArrImmB, Bool.or_eq_true, beq_iff_eq] at ha
      simp only [isCmpB, beq_iff_eq] at h
      unfold LprogAsmPrinter.untagCaret at ha
      split_ifs at ha <;>
        first
        | (rw [h] at ha; revert ha; decide)
        | (rcases ha with (rfl | rfl) | (rfl | rfl) <;> exact absurd h (by decide +kernel))
  | _ => rfl

theorem isCmpB_of_movMnems {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o ∈ movMnems) : isCmpB (.Lopn ds o ss) = false := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [isCmpB]
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem isMemB_of_movMnems {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o ∈ movMnems) : isMemB (.Lopn ds o ss) = false := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [isMemB, isAccB, isArrImmB]

/-- A block without indexed accesses and constant-index array writes passes from every
    state. -/
theorem cmpAccFreeB_of_noAcc : ∀ {l : Lcmd} (w : Bool), (∀ j ∈ l, isMemB j.li_i = false) →
    cmpAccFreeB w l = true
  | [], _, _ => rfl
  | j :: l, w, h => by
    rw [cmpAccFreeB, h j List.mem_cons_self, Bool.and_false, Bool.not_false, Bool.true_and]
    exact cmpAccFreeB_of_noAcc _ fun r hr => h r (List.mem_cons_of_mem _ hr)

/-- A block without compares leaves a compare open only when one is open before it, and passes
    from the closed state. -/
theorem noCmp_eval : ∀ {l : Lcmd}, (∀ j ∈ l, isCmpB j.li_i = false) → ∀ w : Bool,
    (cmpOpenAfter w l = true → w = true) ∧ (w = false → cmpAccFreeB w l = true)
  | [], _, _ => ⟨id, fun _ => rfl⟩
  | j :: l, h, w => by
    have ih := noCmp_eval (l := l) (fun r hr => h r (List.mem_cons_of_mem _ hr))
    have hj := h j List.mem_cons_self
    have hs : cmpOpenStep w j.li_i = true → w = true := by
      simp [cmpOpenStep, hj]
    refine ⟨fun h' => hs ((ih _).1 (by rwa [cmpOpenAfter_cons] at h')), fun hw => ?_⟩
    subst hw
    have hs0 : cmpOpenStep false j.li_i = false := by simp [cmpOpenStep, hj]
    rw [cmpAccFreeB, hs0, (ih false).2 rfl]
    simp

/-- A compare is open after a block when one is open before it or the block has one, and the
    block consists of operations. -/
theorem cmpOpenAfter_ops : ∀ {l : Lcmd}, (∀ j ∈ l, isOpnB j.li_i = true) → ∀ w : Bool,
    (w = true ∨ ∃ j ∈ l, isCmpB j.li_i = true) → cmpOpenAfter w l = true
  | [], _, w, hw => by simpa [cmpOpenAfter] using hw
  | j :: l, h, w, hw => by
    rw [cmpOpenAfter_cons]
    refine cmpOpenAfter_ops (fun r hr => h r (List.mem_cons_of_mem _ hr)) _ ?_
    rcases hw with rfl | ⟨r, hr, hc⟩
    · left; simp [cmpOpenStep, h j List.mem_cons_self]
    · rcases List.mem_cons.mp hr with rfl | hr
      · left; simp [cmpOpenStep, h r List.mem_cons_self, hc]
      · exact Or.inr ⟨r, hr, hc⟩

/-- A compare is open after a block only when one is open before it or the block has one. -/
theorem cmpOpenAfter_true : ∀ {l : Lcmd} {w : Bool}, cmpOpenAfter w l = true →
    w = true ∨ ∃ j ∈ l, isCmpB j.li_i = true
  | [], _, h => Or.inl h
  | j :: l, w, h => by
    rw [cmpOpenAfter_cons] at h
    rcases cmpOpenAfter_true h with h1 | ⟨r, hr, hc⟩
    · simp only [cmpOpenStep, Bool.and_eq_true, Bool.or_eq_true] at h1
      rcases h1.2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨j, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hc⟩

/-- A block of operations without compares keeps the state, and passes from an open compare
    only when it has no indexed access and no constant-index array write. -/
theorem opsNoCmp_eval : ∀ {l : Lcmd},
    (∀ j ∈ l, isOpnB j.li_i = true ∧ isCmpB j.li_i = false) → ∀ w : Bool,
    cmpOpenAfter w l = w ∧ (cmpAccFreeB true l = true → ∀ j ∈ l, isMemB j.li_i = false)
  | [], _, _ => ⟨rfl, fun _ j hj => by simp at hj⟩
  | j :: l, h, w => by
    have ih := opsNoCmp_eval (l := l) (fun r hr => h r (List.mem_cons_of_mem _ hr))
    have hj := h j List.mem_cons_self
    have hs : ∀ w, cmpOpenStep w j.li_i = w := fun w => by simp [cmpOpenStep, hj.1, hj.2]
    refine ⟨by rw [cmpOpenAfter_cons, hs, (ih w).1], fun ht r hr => ?_⟩
    rw [cmpAccFreeB, hs, Bool.and_eq_true, Bool.true_and, Bool.not_eq_true'] at ht
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ht.1
    · exact (ih w).2 ht.2 r hr

/-! ### Refinement -/

/-- The block `B` refines the block `A` for `cmpAccFreeB`: from every state from which `A`
    passes, `B` passes and leaves a compare open only when `A` does. -/
def CmpRefines (B A : Lcmd) : Prop :=
  ∀ w, cmpAccFreeB w A = true →
    cmpAccFreeB w B = true ∧ (cmpOpenAfter w B = true → cmpOpenAfter w A = true)

theorem CmpRefines.refl (A : Lcmd) : CmpRefines A A := fun _ h => ⟨h, id⟩

theorem CmpRefines.trans {C B A : Lcmd} (hCB : CmpRefines C B) (hBA : CmpRefines B A) :
    CmpRefines C A := by
  intro w hA
  obtain ⟨hB, hB'⟩ := hBA w hA
  obtain ⟨hC, hC'⟩ := hCB w hB
  exact ⟨hC, fun h => hB' (hC' h)⟩

theorem CmpRefines.final {B A : Lcmd} (h : CmpRefines B A) (hA : cmpAccFreeB false A = true) :
    cmpAccFreeB false B = true :=
  (h false hA).1

theorem CmpRefines.append {B1 A1 B2 A2 : Lcmd} (h1 : CmpRefines B1 A1)
    (h2 : CmpRefines B2 A2) : CmpRefines (B1 ++ B2) (A1 ++ A2) := by
  intro w hA
  rw [cmpAccFreeB_append, Bool.and_eq_true] at hA
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hw1⟩ := h1 w hA1
  obtain ⟨hB2, hw2⟩ := h2 _ (cmpAccFreeB_mono A2 hw1 hA2)
  refine ⟨by simp [cmpAccFreeB_append, hB1, hB2], fun h => ?_⟩
  rw [cmpOpenAfter_append] at h ⊢
  exact cmpOpenAfter_mono A2 hw1 (hw2 h)

theorem CmpRefines.cons (a : Linstr) {B A : Lcmd} (h : CmpRefines B A) :
    CmpRefines (a :: B) (a :: A) :=
  (CmpRefines.refl [a]).append h

/-- Removing an operation in front of a block keeps a refinement. -/
theorem CmpRefines.cons_op {B A : Lcmd} {a : Linstr} (ha : isOpnB a.li_i = true)
    (h : CmpRefines B A) : CmpRefines B (a :: A) := by
  intro w hA
  rw [cmpAccFreeB, Bool.and_eq_true] at hA
  have hw : w = true → cmpOpenStep w a.li_i = true := fun hw => by simp [cmpOpenStep, ha, hw]
  obtain ⟨hB, hB'⟩ := h w (cmpAccFreeB_mono A hw hA.2)
  refine ⟨hB, fun h' => ?_⟩
  rw [cmpOpenAfter_cons]
  exact cmpOpenAfter_mono A hw (hB' h')

theorem cmpRefines_flatMap {α : Type} {f g : α → Lcmd} : ∀ (l : List α),
    (∀ x ∈ l, CmpRefines (f x) (g x)) → CmpRefines (l.flatMap f) (l.flatMap g)
  | [], _ => CmpRefines.refl _
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h x List.mem_cons_self).append
      (cmpRefines_flatMap l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem cmpRefines_flatMap_single {f : Linstr → Lcmd} (l : Lcmd)
    (h : ∀ i ∈ l, CmpRefines (f i) [i]) : CmpRefines (l.flatMap f) l := by
  have e : ∀ l : Lcmd, l.flatMap (fun i => [i]) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.flatMap_cons, ih]; rfl
  have := cmpRefines_flatMap (g := fun i => [i]) l h
  rwa [e] at this

theorem cmpRefines_flatten_map (f : Lcmd → Lcmd) : ∀ (L : List Lcmd),
    (∀ seg ∈ L, CmpRefines (f seg) seg) → CmpRefines (L.map f).flatten L.flatten
  | [], _ => CmpRefines.refl _
  | a :: L, h => by
    rw [List.map_cons, List.flatten_cons, List.flatten_cons]
    exact (h a List.mem_cons_self).append
      (cmpRefines_flatten_map f L fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- Removing operations keeps a refinement: a filter that removes only operations. -/
theorem cmpRefines_filter (p : Linstr → Bool) : ∀ {l : Lcmd},
    (∀ j ∈ l, p j = false → isOpnB j.li_i = true) → CmpRefines (l.filter p) l
  | [], _ => CmpRefines.refl _
  | a :: l, h => by
    have ih := cmpRefines_filter p (l := l) fun j hj => h j (List.mem_cons_of_mem _ hj)
    cases hp : p a with
    | true =>
      simp only [List.filter_cons, hp, ite_true]
      exact ih.cons a
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, ite_false]
      exact ih.cons_op (h a List.mem_cons_self hp)

/-- **A sublist of a block of operations** refines it. -/
theorem cmpRefines_sublist {l' l : Lcmd} (hs : l'.Sublist l)
    (hop : ∀ j ∈ l, isOpnB j.li_i = true) : CmpRefines l' l := by
  induction hs with
  | slnil => exact CmpRefines.refl _
  | cons a _ ih =>
    exact (ih fun j hj => hop j (List.mem_cons_of_mem _ hj)).cons_op (hop a List.mem_cons_self)
  | cons_cons a _ ih => exact (ih fun j hj => hop j (List.mem_cons_of_mem _ hj)).cons a

/-- **The shape of the dead-write elimination**: a sublist of a front part of operations,
    followed by the same back part, refines the body. -/
theorem cmpRefines_sublist_append {pre' pre : Lcmd} (c : Lcmd) (hs : pre'.Sublist pre)
    (hop : ∀ j ∈ pre, isOpnB j.li_i = true) : CmpRefines (pre' ++ c) (pre ++ c) :=
  (cmpRefines_sublist hs hop).append (CmpRefines.refl c)

/-- **A block refines one operation** when it has an indexed access, a constant-index array
    write (`isMemB`) or a compare only where the operation is one. -/
theorem cmpRefines_ops {B : Lcmd} {i : Linstr} (hi : isOpnB i.li_i = true)
    (hacc : ∀ r ∈ B, isMemB r.li_i = true → isMemB i.li_i = true)
    (hcmp : ∀ r ∈ B, isCmpB r.li_i = true → isCmpB i.li_i = true) : CmpRefines B [i] := by
  intro w hA
  simp only [cmpAccFreeB, Bool.and_true, Bool.not_eq_true'] at hA
  cases hc : isCmpB i.li_i with
  | true =>
    have hna : isMemB i.li_i = false := isMemB_of_isCmpB hc
    refine ⟨cmpAccFreeB_of_noAcc w fun r hr => ?_, fun _ => ?_⟩
    · cases h : isMemB r.li_i
      · rfl
      · rw [hacc r hr h] at hna; cases hna
    · simp [cmpOpenAfter, cmpOpenStep, hi, hc]
  | false =>
    have hnc : ∀ r ∈ B, isCmpB r.li_i = false := fun r hr => by
      cases h : isCmpB r.li_i
      · rfl
      · rw [hcmp r hr h] at hc; cases hc
    have he := noCmp_eval hnc w
    refine ⟨?_, fun h => ?_⟩
    · cases w with
      | false => exact he.2 rfl
      | true =>
        simp only [Bool.true_and] at hA
        exact cmpAccFreeB_of_noAcc true fun r hr => by
          cases h : isMemB r.li_i
          · rfl
          · rw [hacc r hr h] at hA; cases hA
    · have := he.1 h
      subst this
      simp [cmpOpenAfter, cmpOpenStep, hi]

/-- Blocks of operations without compares: `B` refines `A` when `B` has an indexed access or a
    constant-index array write (`isMemB`) only where `A` has one. -/
theorem cmpRefines_noCmp {B A : Lcmd}
    (hA : ∀ j ∈ A, isOpnB j.li_i = true ∧ isCmpB j.li_i = false)
    (hB : ∀ j ∈ B, isOpnB j.li_i = true ∧ isCmpB j.li_i = false)
    (hacc : ∀ j ∈ B, isMemB j.li_i = true → ∃ i ∈ A, isMemB i.li_i = true) :
    CmpRefines B A := by
  intro w h
  have eA := opsNoCmp_eval hA w
  have eB := opsNoCmp_eval hB w
  refine ⟨?_, fun h' => by rw [eA.1]; rwa [eB.1] at h'⟩
  cases w with
  | false => exact (noCmp_eval (fun j hj => (hB j hj).2) false).2 rfl
  | true =>
    have hA0 := eA.2 h
    exact cmpAccFreeB_of_noAcc true fun j hj => by
      cases hj' : isMemB j.li_i
      · rfl
      · obtain ⟨i, hi, hi'⟩ := hacc j hj hj'
        rw [hA0 i hi] at hi'
        cases hi'

/-- A block `B` without indexed accesses and constant-index array writes refines a block `A`
    of operations when `B` has a compare only when `A` has one. -/
theorem cmpRefines_noAcc {B A : Lcmd} (hA : ∀ j ∈ A, isOpnB j.li_i = true)
    (hB : ∀ j ∈ B, isMemB j.li_i = false)
    (hcmp : ∀ j ∈ B, isCmpB j.li_i = true → ∃ i ∈ A, isCmpB i.li_i = true) :
    CmpRefines B A := by
  intro w _
  refine ⟨cmpAccFreeB_of_noAcc w hB, fun h => cmpOpenAfter_ops hA w ?_⟩
  rcases cmpOpenAfter_true h with hw | ⟨j, hj, hc⟩
  · exact Or.inl hw
  · exact Or.inr (hcmp j hj hc)


/-- A block of operations under the mnemonic of an operation or a move mnemonic refines the
    operation. -/
theorem cmpRefines_mnOf {B : Lcmd} {i : Linstr} {ds : List LOperand} {o : String}
    {ss : List LOperand} (hi : i.li_i = .Lopn ds o ss) (h : ∀ r ∈ B, MnOf o r.li_i) :
    CmpRefines B [i] := by
  refine cmpRefines_ops (by simp [hi, isOpnB]) (fun r hr ha => ?_) (fun r hr hc => ?_)
  · obtain ⟨ds', o', ss', he, ho⟩ := h r hr
    rw [he] at ha
    rcases ho with rfl | ho | ⟨w, rfl⟩
    · rw [hi]; exact ha
    · rw [isMemB_of_movMnems ho] at ha; cases ha
    · rcases PhysImgPrint.untagCaret_withWidthTag_mov w with h' | h' <;>
        simp [isMemB, isAccB, isArrImmB, h'] at ha
  · obtain ⟨ds', o', ss', he, ho⟩ := h r hr
    rw [he] at hc
    rcases ho with rfl | ho | ⟨w, rfl⟩
    · rw [hi]; exact hc
    · rw [isCmpB_of_movMnems ho] at hc; cases hc
    · simp [isCmpB, stripWidthTag_withWidthTag w (by decide +kernel : tagSepFree "MOV" = true)]
        at hc

/-- **The constant-shape base reload refines the body**: each reloaded write becomes a move
    and the write under its own mnemonic. -/
theorem cmpRefines_reloadArrImmBody (mbr : String → Option String) (l : Lcmd) :
    CmpRefines (reloadArrImmBody mbr l) l := by
  unfold reloadArrImmBody
  refine cmpRefines_flatMap_single l fun i _ => ?_
  split
  · rename_i l' hl
    obtain ⟨b, q, -, ⟨n, w, hi, rfl⟩ | ⟨d, v, k, hi, rfl⟩⟩ := reloadArrImm_eq_some hl
    · refine cmpRefines_mnOf hi fun r hr => ?_
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases ptrLoad_cases q with hq | hq <;>
        rcases hr with rfl | rfl <;> simp [MnOf, movMnems, hq]
    · refine cmpRefines_mnOf hi fun r hr => ?_
      simp only [List.map_cons, List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨x, hx, rfl⟩
      · rcases ptrLoad_cases q with hq | hq <;> simp [MnOf, movMnems, hq]
      · rcases mem_storeImmVia hx with rfl | rfl | rfl <;> simp [MnOf, movMnems]
  · exact CmpRefines.refl _

/-! ### The free reload scratch at the compare-spill reload -/

theorem isCmpB_of_spillCmp {r : LinstrR} (h : (spillCmp? r).isSome = true) : isCmpB r = true := by
  unfold spillCmp? at h
  split at h
  · split_ifs at h with hc
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp [isCmpB, hc.1.1.1]
    · cases h
  · cases h

/-- The reload scan from position `m` ends inside `c` when an instruction other than an
    operation lies before `m`. -/
theorem scanExit_of_ctl (c : Lcmd) : ∀ (m : Nat) (x : String),
    (∃ p < m, ∃ j, c[p]? = some j ∧ isOpnB j.li_i = false) → scanExit slotArr c m x = none
  | 0, _, ⟨_, hp, _⟩ => absurd hp (Nat.not_lt_zero _)
  | m + 1, x, ⟨p, hp, j, hj, hn⟩ => by
    have ih := scanExit_of_ctl c m
    unfold scanExit
    by_cases hpm : p = m
    · subst hpm
      rw [hj]
      have hs : slotMov? j.li_i = none := by
        cases h : j.li_i <;> simp_all [isOpnB, slotMov?]
      simp only [hs]
      split
      · rename_i ds _ _ he
        rw [he] at hn
        cases hn
      · rfl
    · have ih' := fun y => ih y ⟨p, by omega, j, hj, hn⟩
      rcases hc : c[m]? with _ | j'
      · rfl
      · simp only
        split
        · split_ifs
          all_goals first | rfl | exact ih' _
        · split
          · split_ifs
            all_goals first | rfl | exact ih' _
          · rfl

/-- After an open compare, an indexed access or a constant-index array write of a block that
    passes `cmpAccFreeB` follows an instruction other than an operation. -/
theorem ctl_before_acc : ∀ {c : Lcmd}, cmpAccFreeB true c = true →
    ∀ (m : Nat) (j : Linstr), c[m]? = some j →
    isMemB j.li_i = true → ∃ p < m, ∃ j', c[p]? = some j' ∧ isOpnB j'.li_i = false
  | [], _, m, j, hm, _ => by simp at hm
  | j0 :: c, h, m, j, hm, ha => by
    rw [cmpAccFreeB, Bool.and_eq_true] at h
    cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      simp [ha] at h
    | succ m =>
      simp only [List.getElem?_cons_succ] at hm
      cases ho : isOpnB j0.li_i with
      | false => exact ⟨0, Nat.succ_pos _, j0, rfl, ho⟩
      | true =>
        have hs : cmpOpenStep true j0.li_i = true := by simp [cmpOpenStep, ho]
        rw [hs] at h
        obtain ⟨p, hp, j', h1, h2⟩ := ctl_before_acc h.2 m j hm ha
        exact ⟨p + 1, by omega, j', by simpa using h1, h2⟩

/-- **`cmpAccFreeB` implies `cmpScratchFreeB`.** After a compare on a spilled first operand, the
    reload scan of the base of an indexed access ends at an instruction other than an
    operation before it reaches the compare. -/
theorem cmpScratchFreeB_of_cmpAccFree {body : Lcmd} (h : cmpAccFreeB false body = true) :
    cmpScratchFreeB slotArr body = true := by
  unfold cmpScratchFreeB
  refine List.all_eq_true.mpr fun k _ => ?_
  cases hbk : body[k]? with
  | none => rfl
  | some i =>
    simp only [Bool.or_eq_true, List.all_eq_true]
    cases hs : spillCmp? i.li_i with
    | none => exact Or.inl rfl
    | some t =>
      right
      have hcmp : isCmpB i.li_i = true := isCmpB_of_spillCmp (by rw [hs]; rfl)
      obtain ⟨hk', hi⟩ := List.getElem?_eq_some_iff.mp hbk
      have h' := h
      rw [← List.take_append_drop k body, cmpAccFreeB_append, Bool.and_eq_true,
        List.drop_eq_getElem_cons hk', hi, cmpAccFreeB, Bool.and_eq_true] at h'
      have hst : cmpOpenStep (cmpOpenAfter false (body.take k)) i.li_i = true := by
        simp [cmpOpenStep, hcmp, isOpnB_of_isCmpB hcmp]
      rw [hst] at h'
      have hc := h'.2.2
      intro m _
      cases hcm : (body.drop (k + 1))[m]? with
      | none => rfl
      | some j =>
        simp only
        cases hacc : isMemB j.li_i with
        | false =>
          unfold baseScanFreeB
          simp only [isMemB] at hacc
          rw [hacc]
          rfl
        | true =>
          have hp := ctl_before_acc hc m j hcm hacc
          exact baseScanFreeB_of_scan fun x => by simp [scanExit_of_ctl _ m _ hp]

/-! ### The passes -/

section Passes

open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiAux fuseMulHiBody
  ScratchEnv isMulHiMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (optimizeBasicBlocks
  optRunBody splitStraightRuns splitStraightRuns_flatten bodyAllModeled instrModeled)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold (foldIndexedBody
  constIndexFoldBody dropDeadImmBody spellMemBody foldCore dropDeadCore deadImmReg?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (reallocBody reallocRun
  reallocWith goAcc FI FI.toL Piece pieces)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (legalizeInstr twoAddrBody
  scratchRoute x86Data)

/-- **The high-product fusion** refines the body: every site is a block of moves and `MULX`s
    in place of a `MULXHI`. -/
theorem cmpRefines_fuseMulHiAux (s : Bool) : ∀ (b : Lcmd) (env : ScratchEnv)
    (pend : List (String × String)), CmpRefines (fuseMulHiAux s env pend b) b
  | [], env, pend => by rw [fuseMulHiAux]; exact CmpRefines.refl _
  | i :: rest, env, pend => by
    obtain ⟨L, env', pend', he, hL⟩ := PhysImgSidePass.fuseMulHiAux_cons_out s env pend i rest
    rw [he]
    show CmpRefines _ ([i] ++ rest)
    refine CmpRefines.append ?_ (cmpRefines_fuseMulHiAux s rest env' pend')
    rcases hL with rfl | ⟨d, opn, s1, s2, heq, -, hout⟩
    · exact CmpRefines.refl _
    · refine cmpRefines_ops (by simp [heq, isOpnB]) (fun r hr ha => ?_) (fun r hr hc => ?_)
      · obtain ⟨ds, o, y, he', ho, -⟩ := hout r hr
        rw [he'] at ha
        rcases ho with rfl | rfl | rfl <;> simp [isMemB, isAccB, isArrImmB] at ha
      · obtain ⟨ds, o, y, he', ho, -⟩ := hout r hr
        rw [he'] at hc
        simp only [isCmpB] at hc
        rcases ho with rfl | rfl | rfl <;> exact absurd hc (by decide +kernel)

theorem cmpRefines_fuseMulHiBody (s : Bool) (b : Lcmd) : CmpRefines (fuseMulHiBody b s) b :=
  cmpRefines_fuseMulHiAux s b [] []

/-- A modeled instruction is an operation and no compare. -/
theorem instrModeled_noCmp {j : Linstr} (h : instrModeled j = true) :
    isOpnB j.li_i = true ∧ isCmpB j.li_i = false := by
  obtain ⟨d, o, ss, he⟩ := PhysImgOpt.instrModeled_shape h
  rw [he]
  refine ⟨rfl, ?_⟩
  simp only [isCmpB]
  cases hc : (stripWidthTag o == "CMP")
  · rfl
  · exfalso
    rw [beq_iff_eq] at hc
    have hp : parseImmShiftMnem o = none := by
      by_cases hca : '^' ∈ o.toList
      · have hT : o.toList.takeWhile (· != '^') = ['C', 'M', 'P'] := by
          unfold stripWidthTag at hc
          rw [ite_eq_left (by simpa using hca)] at hc
          simpa using congrArg String.toList hc
        unfold parseImmShiftMnem
        rw [ite_eq_left (by simpa using hca), hT]
        split <;> rfl
      · have hl : o.toList = ['C', 'M', 'P'] ∨ o.toList = ['C', 'M', 'P', ':', '6', '4'] := by
          unfold stripWidthTag at hc
          rw [ite_eq_right (by simpa using hca)] at hc
          split at hc
          · right
            rename_i hs
            obtain ⟨t, ht⟩ := List.isSuffixOf_iff_suffix.mp hs
            have h2 : o.toList = t ++ [':', '6', '4'] := ht.symm
            rw [h2] at hc ⊢
            have h3 : t = ['C', 'M', 'P'] := by
              simpa [List.dropLast_append_cons] using congrArg String.toList hc
            rw [h3]; rfl
          · left; subst hc; rfl
        unfold parseImmShiftMnem
        rw [ite_eq_right (by simpa using hca)]
        rcases hl with hl | hl <;> rw [hl] <;> rfl
    unfold instrModeled at h
    rw [he] at h
    simp only [hc, hp] at h
    split at h <;> simp_all

/-- **The basic-block optimiser** refines the body: an optimised run has no compare, and has an
    indexed access only where the run has one. -/
theorem cmpRefines_optimizeBasicBlocks (b : Lcmd) : CmpRefines (optimizeBasicBlocks b) b := by
  unfold optimizeBasicBlocks
  suffices h : CmpRefines ((splitStraightRuns b).map
      (fun seg => if LprogOptPipeline.bodyIsStraightLine seg then optRunBody seg else seg)).flatten
      (splitStraightRuns b).flatten by
    rwa [splitStraightRuns_flatten] at h
  refine cmpRefines_flatten_map _ _ fun seg _ => ?_
  split
  · unfold optRunBody
    split
    · rename_i hm
      have hseg : ∀ j ∈ seg, instrModeled j = true := List.all_eq_true.mp hm
      let P : Linstr → Prop := fun j => isOpnB j.li_i = true ∧ isCmpB j.li_i = false ∧
        (isMemB j.li_i = true → ∃ i ∈ seg, isMemB i.li_i = true)
      have hP : ∀ j ∈ seg, P j := fun j hj =>
        ⟨(instrModeled_noCmp (hseg j hj)).1, (instrModeled_noCmp (hseg j hj)).2,
          fun ha => ⟨j, hj, ha⟩⟩
      have hrw : PhysImgSidePass.RwClosed P := by
        intro i dsts opn srcs g hi he _
        obtain ⟨h1, h2, h3⟩ := hi
        rw [he] at h1 h2 h3
        exact ⟨rfl, h2, h3⟩
      have hmv : PhysImgSidePass.MvClosed P := by
        intro i d mn s r hi he _
        obtain ⟨h1, h2, h3⟩ := hi
        rw [he] at h1 h2 h3
        exact ⟨rfl, h2, h3⟩
      have hout := PhysImgSidePass.forall_loadCSE hmv (PhysImgSidePass.forall_preLoad hrw hP)
      exact cmpRefines_noCmp (fun j hj => ⟨(hP j hj).1, (hP j hj).2.1⟩)
        (fun j hj => ⟨(hout j hj).1, (hout j hj).2.1⟩) fun j hj => (hout j hj).2.2
    · exact CmpRefines.refl _
  · exact CmpRefines.refl _

theorem cmpRefines_map (f : Linstr → Linstr) : ∀ (l : Lcmd),
    (∀ i ∈ l, CmpRefines [f i] [i]) → CmpRefines (l.map f) l
  | [], _ => CmpRefines.refl _
  | a :: l, h => by
    rw [List.map_cons]
    exact (h a List.mem_cons_self).append
      (cmpRefines_map f l fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- An operation under a mnemonic that is neither a compare nor an access mnemonic (`isMemB`). -/
theorem quiet_of_mn {ds : List LOperand} {o : String} {ss : List LOperand}
    (hc : (stripWidthTag o == "CMP") = false)
    (ha : (LprogAsmPrinter.untagCaret o == "LOADIDX" || LprogAsmPrinter.untagCaret o == "STOREIDX" ||
      (LprogAsmPrinter.untagCaret o == "ZEROARR" || LprogAsmPrinter.untagCaret o == "STOREIMM")) =
        false) :
    isCmpB (.Lopn ds o ss) = false ∧ isMemB (.Lopn ds o ss) = false :=
  ⟨hc, ha⟩

/-- One operation in place of an operation refines it when it is neither a compare nor an
    indexed access or a constant-index array write. -/
theorem cmpRefines_quiet_one {i j : Linstr} (hi : isOpnB i.li_i = true)
    (hj : isCmpB j.li_i = false ∧ isMemB j.li_i = false) : CmpRefines [j] [i] := by
  refine cmpRefines_ops hi (fun r hr ha => ?_) (fun r hr hc => ?_)
  · rw [List.mem_singleton] at hr; subst hr; rw [hj.2] at ha; cases ha
  · rw [List.mem_singleton] at hr; subst hr; rw [hj.1] at hc; cases hc

theorem cmpRefines_foldCore (p : Nat × Nat × Nat) (ex : List String) :
    ∀ (env : ConstIndexFold.KEnv) (b : Lcmd), CmpRefines (foldCore p ex env b) b
  | _, [] => by rw [foldCore]; exact CmpRefines.refl _
  | env, i :: is => by
    rw [foldCore]
    show CmpRefines ([_] ++ _) ([i] ++ is)
    refine CmpRefines.append ?_ (cmpRefines_foldCore p ex _ is)
    rcases PhysImgFold.foldInstr_cases ex env i.li_i with hf | ⟨d, B, x, sc, off, hi, hf⟩ |
        ⟨d, B, x, sc, vn, off, hi, hf⟩ | ⟨d, x, n, hi, hf, -⟩
    · have he : ({ i with li_i := ConstIndexFold.foldInstr ex env i.li_i } : Linstr) = i := by
        rw [hf]
      rw [he]
      exact CmpRefines.refl _
    all_goals
      refine cmpRefines_quiet_one (by rw [hi]; rfl) ?_
      dsimp only
      rw [hf]
      exact quiet_of_mn (by decide +kernel) (by decide +kernel)

theorem cmpRefines_dropDeadCore (p : Nat × Nat × Nat)
    (hop : ∀ i : Linstr, (deadImmReg? p i).isSome = true → isOpnB i.li_i = true) :
    ∀ b : Lcmd, CmpRefines (dropDeadCore p b) b
  | [] => by rw [dropDeadCore]; exact CmpRefines.refl _
  | i :: is => by
    rw [dropDeadCore]
    split
    · rename_i r hr
      split
      · exact (cmpRefines_dropDeadCore p hop is).cons_op (hop i (by rw [hr]; rfl))
      · exact (cmpRefines_dropDeadCore p hop is).cons i
    · exact (cmpRefines_dropDeadCore p hop is).cons i

theorem cmpRefines_spellMemBody (b : Lcmd) : CmpRefines (spellMemBody b) b := by
  unfold spellMemBody
  refine cmpRefines_map _ b fun i _ => ?_
  rcases PhysImgFold.spellMemInstr_cases i.li_i with he | ⟨d, B, off, hi, o, he, ho⟩ |
      ⟨d, B, off, vn, hi, o, he, ho⟩
  · have : ({ i with li_i := ConstIndexFold.spellMemInstr i.li_i } : Linstr) = i := by rw [he]
    rw [this]
    exact CmpRefines.refl _
  all_goals
    refine cmpRefines_quiet_one (by rw [hi]; rfl) ?_
    dsimp only
    rw [he]
    rcases ho with rfl | rfl <;> exact quiet_of_mn (by decide +kernel) (by decide +kernel)

theorem isOpnB_of_deadImmReg {p : Nat × Nat × Nat} {i : Linstr}
    (h : (deadImmReg? p i).isSome = true) : isOpnB i.li_i = true := by
  unfold deadImmReg? at h
  cases hi : i.li_i with
  | Lopn _ _ _ => rfl
  | _ =>
    rw [hi] at h
    simp [ConstIndexFold.lowerPrinted, GatherImmForms.lowerCov6, SpillSlotEncode.lowerCov5,
      GatherFullBody.lowerLinstrExtCov4,
      GatherInPlace.lowerLinstrExtCov3, LoweringCoverageCmovSar.lowerLinstrExtCov2,
      LoweringExtendedCoverage.lowerLinstrExtCov, LoweringExtended.lowerLinstrExt2,
      LoweringExtended.lowerLinstrExt] at h

/-- **The constant-index fold** refines the body: the fold and the spelling rewrite an access or
    a move into a load, a store or a move, and the dead-move elimination removes operations. -/
theorem cmpRefines_foldIndexedBody (b : Lcmd) : CmpRefines (foldIndexedBody b) b := by
  have hdrop : ∀ c, CmpRefines (dropDeadImmBody c) c := by
    intro c
    unfold dropDeadImmBody
    dsimp only
    split
    · exact cmpRefines_dropDeadCore _ (fun _ h => isOpnB_of_deadImmReg h) _
    · exact CmpRefines.refl _
  have hconst : CmpRefines (constIndexFoldBody b) b := by
    unfold constIndexFoldBody
    dsimp only
    split
    · exact cmpRefines_foldCore _ _ _ _
    · exact CmpRefines.refl _
  unfold foldIndexedBody
  exact (cmpRefines_spellMemBody _).trans ((hdrop _).trans hconst)


/-- **The register re-allocation** refines the body: a re-allocated run has no indexed access,
    and a compare only where the run has one. -/
theorem cmpRefines_reallocBody (res : List String) (b : Lcmd) :
    CmpRefines (reallocBody res b) b := by
  rw [LprogGpReallocLeak.reallocBody_eq]
  suffices h : CmpRefines (LprogGpReallocLeak.outSegs res (LprogGpRealloc.labelLiveFrames b)
      (pieces b)).flatten ((pieces b).map LprogGpReallocLeak.Piece.toLcmd).flatten by
    rwa [LprogGpReallocLeak.pieces_flatten] at h
  have hps := LprogGpReallocCT.pieces_spec (recog := LcmdCopyPropagate.isRecognizedOpn) b
  have hgood := LprogGpReallocLeak.pieces_good b
  generalize LprogGpRealloc.labelLiveFrames b = lf
  generalize pieces b = ps at hps hgood
  induction ps with
  | nil => exact CmpRefines.refl _
  | cons p ps ih =>
    simp only [LprogGpReallocLeak.outSegs, List.map_cons, List.flatten_cons]
    refine CmpRefines.append ?_ (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (fun q hq => hgood q (List.mem_cons_of_mem _ hq)))
    have hg := hgood p List.mem_cons_self
    rcases hps p List.mem_cons_self with ⟨li, -, rfl⟩ | ⟨is, rfl, hwf⟩
    · exact CmpRefines.refl _
    · simp only [LprogGpReallocLeak.outSeg, LprogGpReallocLeak.Piece.toLcmd]
      refine cmpRefines_noAcc (fun j hj => ?_) (fun j hj => ?_) (fun j hj hc => ?_)
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hj
        rfl
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        obtain ⟨i, hi, he⟩ := PhysImgSidePass.reallocRun_opn _ is k hk
        have hw := hwf i hi
        have hz := PhysImgFold.fragOf?_untagCaret_ne (hg.2 i hi)
        simp only [LprogGpRealloc.FI.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
        simp [FI.toL, LprogGpRealloc.FI.toR, isMemB, isAccB, isArrImmB, he, hw.1.2, hw.2,
          hz.1, hz.2]
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        obtain ⟨i, hi, he⟩ := PhysImgSidePass.reallocRun_opn _ is k hk
        exact ⟨i.toL, List.mem_map_of_mem hi, by
          simpa [FI.toL, LprogGpRealloc.FI.toR, isCmpB, he] using hc⟩

/-- **The two-address legalisation** refines the body. -/
theorem cmpRefines_twoAddrBody (b : Lcmd) : CmpRefines (twoAddrBody b) b := by
  unfold twoAddrBody LegalizeShiftImm.legalizeBody
  dsimp only
  refine cmpRefines_flatMap_single b fun i _ => ?_
  cases h : i.li_i with
  | Lopn ds o ss => exact cmpRefines_mnOf h (legalizeInstr_mnOf _ i h)
  | _ =>
    unfold legalizeInstr
    split
    · rename_i he; rw [h] at he; cases he
    · exact CmpRefines.refl _

/-! ### The export -/

theorem mnOf_of_armOut {ins : List LOperand} {o : String} {r : LinstrR} (h : ArmOut ins o r) :
    MnOf o r := by
  obtain ⟨ds, o', ss, rfl, ho, -⟩ := h
  exact ⟨ds, o', ss, rfl, ho.elim Or.inl (fun h => Or.inr (Or.inl h))⟩

/-- Every instruction of the expansion of an operation under `o` is an operation under `o` or
    a move mnemonic. -/
theorem physExpand_mnOf (shiftImm : ShiftImmOracle) (u64 : Bool) (rmap : LOperand → LOperand)
    (mbr : String → Option String) (ii : Nat) (ds : List LOperand) (o : String)
    (ss : List LOperand) :
    ∀ r ∈ physExpand shiftImm u64 rmap mbr ⟨ii, .Lopn ds o ss⟩, MnOf o r.li_i := by
  have harm : ∀ (ins : List LOperand) (L : List LinstrR), (∀ r ∈ L, ArmOut ins o r) →
      ∀ r ∈ L.map (fun r => (⟨ii, r⟩ : Linstr)), MnOf o r.li_i := by
    intro ins L h r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact mnOf_of_armOut (h a ha)
  rw [physExpand_eq]
  dsimp only
  split
  · rename_i d _ opn s0 s1 _ heq
    cases heq
    split
    · split
      · exact harm _ _ (lowerTwoAddrShiftImm_armOut _ _ _ _ _ (movFor_ok _))
      · exact harm _ _ (lowerTwoAddr_armOut _ _ _ _ _ (movFor_ok _))
    · split
      · rename_i d' opn' addr val heq
        cases heq
        split
        · exact List.forall_mem_append.mpr ⟨harm _ _ (reloadMemrefBase_armOut mbr _ _),
            harm _ _ (legalizeMemStoreK_armOut _ _ _ _ _ _ (movFor_ok _))⟩
        · exact harm _ _ (legalizeSpillDst_armOut _ _ _)
      · rename_i heq
        cases heq
        exact harm _ _ (legalizeSpillDst_armOut _ _ _)
      · rename_i hno
        exact absurd rfl (hno _ _ _)
  · rename_i d opn s heq
    cases heq
    split
    · exact harm _ _ (lowerNativeShiftRotate_armOut _ _ _ _ (movFor_ok _))
    · split
      · exact List.forall_mem_append.mpr ⟨harm _ _ (reloadMemrefBase_armOut mbr _ _),
          harm _ _ (legalizeMemLoad_armOut _ _ _ _ (movFor_ok _))⟩
      · exact harm _ _ (legalizeOneSrc_armOut _ _ _ _)
  · rename_i dsts opn srcs _ _ heq
    cases heq
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, _, _, rfl, Or.inl rfl⟩
  · rename_i hno
    exact absurd rfl (hno _ _ _)

/-- **The expansion of an instruction** refines it. -/
theorem cmpRefines_physExpand (shiftImm : ShiftImmOracle) (u64 : Bool)
    (rmap : LOperand → LOperand) (mbr : String → Option String) (i : Linstr) :
    CmpRefines (physExpand shiftImm u64 rmap mbr i) [i] := by
  obtain ⟨ii, w⟩ := i
  cases w with
  | Lopn ds o ss => exact cmpRefines_mnOf rfl (physExpand_mnOf shiftImm u64 rmap mbr ii ds o ss)
  | _ => simp only [physExpand_eq]; exact CmpRefines.refl _

/-- The instruction is neither a compare nor an indexed access. -/
def QuietI (j : Linstr) : Prop := isCmpB j.li_i = false ∧ isMemB j.li_i = false

theorem quiet_eval {l : Lcmd} (h : ∀ j ∈ l, QuietI j) (w : Bool) :
    cmpAccFreeB w l = true ∧ (cmpOpenAfter w l = true → w = true) :=
  ⟨cmpAccFreeB_of_noAcc w fun j hj => (h j hj).2, (noCmp_eval (fun j hj => (h j hj).1) w).1⟩

theorem cmpAccFreeB_quiet_left {w : Bool} {a b : Lcmd} (ha : ∀ j ∈ a, QuietI j)
    (hb : cmpAccFreeB w b = true) : cmpAccFreeB w (a ++ b) = true := by
  have e := quiet_eval ha w
  rw [cmpAccFreeB_append, e.1, Bool.true_and]
  exact cmpAccFreeB_mono b e.2 hb

theorem cmpAccFreeB_quiet_right {w : Bool} {a b : Lcmd} (ha : cmpAccFreeB w a = true)
    (hb : ∀ j ∈ b, QuietI j) : cmpAccFreeB w (a ++ b) = true := by
  rw [cmpAccFreeB_append, ha, Bool.true_and]
  exact (quiet_eval hb _).1

theorem quietI_of_slotMov {j : Linstr} (h : (slotMov? j.li_i).isSome = true) : QuietI j := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  unfold slotMov? at hp
  split at hp
  · rename_i dst opn src he
    unfold QuietI
    rw [he]
    split_ifs at hp with h1
    all_goals
      rcases h1 with rfl | rfl <;> exact quiet_of_mn (by decide +kernel) (by decide +kernel)
  · cases hp

/-- **`cmpAccFreeB` on the call-free looped physical ABI export.** When the body `body1` that
    the export expands passes `cmpAccFreeB`, so does the body of the export: the prologue, the
    saves, the argument materialization and the epilogue are moves, and the expansion of an
    instruction has a compare or an indexed access only where the instruction is one. -/
theorem cmpAccFreeB_lfundefPhysAbiOfVirtCert
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false) (hacc : cmpAccFreeB false body1 = true) :
    cmpAccFreeB false (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
        abiArgs abiTyin x86Abi posBind).1.lfd_body = true := by
  rw [PhysImgSideAlloc.lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf]
  have hlp : ∀ j ∈ body1.flatMap (physExpand (PhysImgSideAlloc.certShiftImm shiftImm body1)
      (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr),
      PhysAbiShape.notLivePin j = false → isOpnB j.li_i = true := by
    intro j _ hj
    unfold PhysAbiShape.notLivePin at hj
    split at hj
    · rename_i ds o ss he
      rw [he]
      rfl
    · cases hj
  have hF := (((cmpRefines_reloadArrImmBody mbr _).trans
    (cmpRefines_filter PhysAbiShape.notLivePin hlp)).trans
    (cmpRefines_flatMap_single body1 fun i _ =>
      cmpRefines_physExpand (PhysImgSideAlloc.certShiftImm shiftImm body1)
        (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr i)).final hacc
  have hP : ∀ j ∈ buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 [])
      (fun _ => none) ++ extraSaves abiArgs, QuietI j :=
    fun j hj => quietI_of_slotMov ((prologue_moves _ _ abiArgs).1 j hj)
  have hM : ∀ j ∈ buildArgPtrMaterialize { virt0 with lfd_body := body1 }
      (physTableOut body1 []) abiArgs (fun _ => none), QuietI j := by
    intro r hr
    unfold buildArgPtrMaterialize at hr
    obtain ⟨⟨abiReg, j⟩, -, hr⟩ := List.mem_flatMap.mp hr
    simp only at hr
    split at hr
    · simp at hr
    · split_ifs at hr <;>
        rcases hs : abiSlotOfExt abiReg with _ | s <;>
        simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
        (try rcases hr with rfl | rfl) <;>
        exact quiet_of_mn (by decide +kernel) (by decide +kernel)
  have hE : ∀ j ∈ calleeSaveRestoreEpilogue ++ [(⟨0, .Lret⟩ : Linstr)], QuietI j := by
    intro j hj
    simp only [calleeSaveRestoreEpilogue, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide +kernel, by decide +kernel⟩
  have hT := cmpAccFreeB_quiet_right (cmpAccFreeB_dropLast _ hF) hE
  rw [← List.append_assoc] at hT
  unfold insertEpilogue
  exact cmpAccFreeB_quiet_left hP (cmpAccFreeB_quiet_left hM hT)

/-- **The dead-write elimination shape on a body with a last instruction**: a sublist of the
    instructions before the last one, all of them operations, followed by the last one,
    refines the body. -/
theorem cmpRefines_dropLast_sublist {b pre' : Lcmd} {r : Linstr} (hr : b.getLast? = some r)
    (hs : pre'.Sublist b.dropLast) (hop : ∀ j ∈ b.dropLast, isOpnB j.li_i = true) :
    CmpRefines (pre' ++ [r]) b := by
  have hb : b.dropLast ++ [r] = b := List.dropLast_append_getLast? r (by simp [hr])
  have := cmpRefines_sublist_append [r] hs hop
  rwa [hb] at this

/-- **`cmpAccFreeB` on the body of the two-address legalisation** of the re-allocated, folded
    and optimised body `b1`, when `b1` refines the fusion of the allocated body `b0` and `b0`
    passes `cmpAccFreeB`. -/
theorem cmpAccFreeB_twoAddrBody (res : List String) {b0 b1 : Lcmd}
    (h0 : cmpAccFreeB false b0 = true) (hb1 : CmpRefines b1 (fuseMulHiBody b0 true)) :
    cmpAccFreeB false
      (twoAddrBody (reallocBody res (foldIndexedBody (optimizeBasicBlocks b1)))) = true :=
  ((cmpRefines_twoAddrBody _).trans ((cmpRefines_reallocBody res _).trans
    ((cmpRefines_foldIndexedBody _).trans ((cmpRefines_optimizeBasicBlocks _).trans
      (hb1.trans (cmpRefines_fuseMulHiBody true b0)))))).final h0

/-- **The compare scratch on the body of the compare-spill reload** (conjunct 8 of the side
    conditions of the region gate): when the allocated body `b0` passes `cmpAccFreeB` and `b1`
    refines its fusion, the reload scan of the base of no indexed access of the two-address
    legalisation of the re-allocated, folded and optimised `b1` carries the reload scratch to
    the position after a compare on a spilled first operand. -/
theorem cmpScratchFreeB_twoAddrBody (res : List String) {b0 b1 : Lcmd}
    (h0 : cmpAccFreeB false b0 = true) (hb1 : CmpRefines b1 (fuseMulHiBody b0 true)) :
    cmpScratchFreeB slotArr
      (twoAddrBody (reallocBody res (foldIndexedBody (optimizeBasicBlocks b1)))) = true :=
  cmpScratchFreeB_of_cmpAccFree (cmpAccFreeB_twoAddrBody res h0 hb1)

end Passes

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp
