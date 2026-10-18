/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (physExpand physRmap)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The condition -/

/-- The instruction `r` is no indexed access, or the base of its first source is a
    general-purpose name other than the reload scratch. -/
def baseNoScratchB (r : LinstrR) : Bool :=
  !isAccB r ||
    match r with
    | .Lopn _ _ (.arrIdx x _ _ :: _) => gpNameB x && x != reloadScratch
    | _ => true

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
      have hbj := hb j hjb
      unfold baseScanFreeB
      unfold baseNoScratchB at hbj
      cases hacc : isAccB j.li_i with
      | false => rfl
      | true =>
        rw [hacc] at hbj
        simp only [Bool.not_true, Bool.false_or] at hbj ⊢
        split
        · rename_i _ _ _ x _ _ _ hr
          rw [hr] at hbj
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hbj
          rw [bne_iff_ne, ne_eq]
          intro hex
          obtain ⟨m', j', d', hlt, h1, h2, h3, h4⟩ :=
            scanExit_scratch_witness slotArr _ m x hbj.1 hbj.2 hex
          have hlen : m' < (body.drop (k + 1)).length := by
            have := (List.getElem?_eq_some_iff.mp h1).1
            exact this
          have hfree := hmk m' (List.mem_range.mpr hlen)
          rw [h1] at hfree
          simp only [movScanFreeB, h2, beq_self_eq_true, h3, Bool.and_self, Bool.not_true,
            Bool.false_or, h4, bne_self_eq_false, Bool.false_eq_true] at hfree
        · rfl

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
      simp only [List.filter_cons, hp, if_true, scratchPrevB, Bool.and_eq_true]
      exact ⟨h.1, scratchPrevB_filter p hn' h.2⟩
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, if_false]
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
      simp [scratchPrevB, scratchMovFreeB_of_src (ss := [.reg q])
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
    unfold physExpand
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
    simp [physExpand, scratchPrevB, scratchMovFreeB, slotMov?]

/-! ## 7. The bases of the expansion -/

/-- The first indexed source of the instruction, if any, is based at `R14`. -/
def baseR14B : LinstrR → Bool
  | .Lopn _ _ (.arrIdx x _ _ :: _) => x == reloadScratch2
  | _ => true

theorem baseNoScratchB_of_baseR14B {r : LinstrR} (h : baseR14B r = true) :
    baseNoScratchB r = true := by
  unfold baseNoScratchB
  split
  · rename_i x _ _ _ _ _
    simp only [baseR14B, beq_iff_eq] at h
    subst h
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact Or.inr ⟨by decide, by decide⟩
  · simp

theorem baseR14B_of_idxFree {r : LinstrR} (h : PhysImgSideAlloc.idxFreeB r = true) :
    baseR14B r = true := by
  unfold baseR14B
  split
  · simp [PhysImgSideAlloc.idxFreeB] at h
  · rfl

theorem legalizeMemLoad_baseR14 (n y mov : String) :
    (legalizeMemLoad (.reg n) (.arrIdx reloadScratch2 y 8) "LOADIDX" mov).all baseR14B
      = true := by
  simp only [legalizeMemLoad, legalizeSibElem, sibNameSpill_reloadScratch2]
  split_ifs <;> simp [baseR14B]

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
        simp [baseR14B]
  · simp only [legalizeMemStore, legalizeSibElem, sibNameSpill_reloadScratch2]
    split <;> (try split) <;> (try split_ifs) <;> simp_all [baseR14B]

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
    have ho : o = "LOADIDX" ∨ o = "STOREIDX" := by simpa [isAccB] using hA
    obtain ⟨hL, hS⟩ := hacc ds o ss rfl
    rcases ho with rfl | rfl
    · obtain ⟨dn, b, y, rfl, rfl, b', y', q, hrmA, hmb, hq⟩ := hL rfl
      obtain ⟨n', hn'⟩ := hreg dn
      simp only [physExpand, isNativeShiftRotate_loadIdx, isMemLoad_loadIdx,
        Bool.false_eq_true, if_false, if_true, hrmA, hn', reloadMemrefBase, hmb]
      have h := legalizeMemLoad_baseR14 n' y' (if hasSuffix "LOADIDX" ":64" then "MOV:64"
        else "MOV")
      intro r hr
      simp only [List.mem_append, List.mem_map] at hr
      rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
      · simp only [List.mem_singleton] at hr'
        subst hr'
        rfl
      · exact List.all_eq_true.mp h r' hr'
    · obtain ⟨dn, b, y, v, rfl, rfl, b', y', q, hrmA, hmb, hq⟩ := hS rfl
      obtain ⟨n', hn'⟩ := hreg dn
      obtain ⟨v', hv'⟩ := hreg v
      simp only [physExpand, isTwoAddrBinop_storeIdx, isMemStore_storeIdx,
        Bool.false_eq_true, if_false, if_true, hrmA, hn', hv', reloadMemrefBase, hmb]
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
        match abiSaveOfExt p.2 with
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
    simp only [physRmap, hcf, Bool.false_eq_true, if_false]
    rfl
  have hmq : ∀ b q, mbr b = some q → q ≠ reloadScratch := by
    intro b q h
    rw [hmbr] at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨a, -, ha⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some hp)
    split at ha
    · rename_i s hs
      cases ha
      exact abiSaveOfExt_ne_scratch hs
    · cases ha
  have hrmS : ∀ x, isScratchOp (rm x) = false := by
    intro x
    cases x with
    | reg m =>
      simp only [rm, remapOperand, isScratchOp, beq_eq_false_iff_ne]
      intro he
      exact PhysImgSideAlloc.physRegName_not_scratch _ (by
        rw [he]; simp [FheMontMulEmit.fuseReloadScratches])
    | _ => simp [rm, remapOperand, isScratchOp]
  have hF : scratchPrevB false (((body1.flatMap (physExpand (PhysImgSideAlloc.certShiftImm
      shiftImm body1) (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr)).filter
        PhysAbiShape.notLivePin).map Linstr.li_i) = true := by
    refine scratchPrevB_filter_livePin ?_
    rw [List.map_flatMap]
    exact scratchPrevB_flatMap _ fun i _ => by
      rw [hrmE]
      exact physExpand_scratchPrev _ _ rm mbr i hrmS hmq
  have hFb : ∀ j ∈ (body1.flatMap (physExpand (PhysImgSideAlloc.certShiftImm
      shiftImm body1) (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr)).filter
        PhysAbiShape.notLivePin, baseNoScratchB j.li_i = true := by
    intro j hj
    obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp (List.mem_of_mem_filter hj)
    rw [hrmE] at hj
    refine baseNoScratchB_of_baseR14B ?_
    cases hA : isAccB i.li_i
    · exact baseR14B_of_idxFree (PhysImgSideAlloc.physExpand_idxFree _ _ rm mbr i
        (fun x hx => PhysImgSideAlloc.noIdxB_remapOperand _ _ hx) (hidx i hi hA) j hj)
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp
