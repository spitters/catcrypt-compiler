/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint

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

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp
