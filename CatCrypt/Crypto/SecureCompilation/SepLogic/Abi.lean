/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.X86State
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Array
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim

/-!
# The System V layout and the image separation as assertions

The entry conditions `AbiLayout.Regions` of a compiled function, the read-back
`AbiLayout.ResultOf` of its result, and the separation `ImageAddrSim.ImgSep` of the image
simulation are each the holding of an assertion over the address machine `AState`.

`abiPre σ rv` is the precondition of the layout `σ` at the entry register values `rv`: the
registers of the layout hold their values, the bounded registers are within their bounds,
the stack words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and the words of each pointer region
are owned and separated by `∗`, and the stack parameters hold the words at `%rsp + 8 k`. The
stack parameters lie in the stack words, so they are joined by the conjunction
`SAssert.conj`, which takes the union of the footprints and requires no disjointness.

`imgSepA` is the separation of the image simulation: the cells of the slot arrays are
separated from the frame words and from the red-zone word, the frame words and the cells
are each pairwise separated (`SAssert.iSep`, the separating conjunction of a family), and
the length, general-purpose and slot conditions of `ImgSep` are pure.

## Main definitions

* `SAssert.conj`, `SAssert.iSep`: the conjunction of two assertions and the separating
  conjunction of a family.
* `X86.wordLocs`, `X86.wordsLocs`: the memory locations of a word and of a set of words.
* `X86.regsAt`, `X86.stackAt`, `X86.abiPre`: the precondition of a layout.
* `X86.valAt`: the read-back of a result value as an assertion on the exit state.
* `X86.imgFrames`, `X86.imgCells`, `X86.imgSepA`: the image separation as an assertion.

## Main results

* `X86.disjoint_wordLocs_iff`, `X86.disjoint_wordsLocs_iff`: disjoint word locations are
  `Disjoint8` words.
* `X86.holds_abiPre`, `X86.regions_iff_abiPre`: `σ.Regions sa` holds exactly when the
  precondition of `σ` holds at some entry register values.
* `X86.valAt_holds_iff`: `valAt` holds exactly at the read-back of the result.
* `X86.imgSep_iff_sep`: `ImgSep` is the holding of `imgSepA`.
* `X86.imgSepA_frames`, `X86.imgSepA_cellFrame`, `X86.imgSepA_cells`, `X86.imgSepA_red`: the
  `Disjoint8` facts of the image separation by projection.
* `X86.imgSepA_store_frame`: a store into a frame word keeps every other frame word and
  every cell of a slot array.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

namespace SAssert

universe u v w

variable {σ : Type u} {L : Type v} [Footprinted σ L]

/-- The conjunction of two assertions: the union of the footprints and both predicates,
    with no disjointness. -/
def conj (P Q : SAssert σ L) : SAssert σ L where
  fp := P.fp ∪ Q.fp
  holds s := P.holds s ∧ Q.holds s
  supp s t h := fun ⟨hp, hq⟩ =>
    ⟨P.supp s t (Footprinted.agreeOn_anti Set.subset_union_left h) hp,
      Q.supp s t (Footprinted.agreeOn_anti Set.subset_union_right h) hq⟩

@[simp] theorem fp_conj (P Q : SAssert σ L) : (conj P Q).fp = P.fp ∪ Q.fp := rfl

@[simp] theorem holds_conj (P Q : SAssert σ L) (s : σ) :
    (conj P Q).holds s ↔ P.holds s ∧ Q.holds s := Iff.rfl

/-- The separating conjunction of a family: the union of the footprints, which are
    pairwise disjoint at distinct indices, and every member. -/
def iSep {ι : Type w} (P : ι → SAssert σ L) : SAssert σ L where
  fp := ⋃ i, (P i).fp
  holds s := (∀ i j, i ≠ j → Disjoint (P i).fp (P j).fp) ∧ ∀ i, (P i).holds s
  supp s t h := fun ⟨hd, hp⟩ =>
    ⟨hd, fun i => (P i).supp s t
      (Footprinted.agreeOn_anti (Set.subset_iUnion (fun i => (P i).fp) i) h) (hp i)⟩

@[simp] theorem fp_iSep {ι : Type w} (P : ι → SAssert σ L) : (iSep P).fp = ⋃ i, (P i).fp :=
  rfl

@[simp] theorem holds_iSep {ι : Type w} (P : ι → SAssert σ L) (s : σ) :
    (iSep P).holds s ↔ (∀ i j, i ≠ j → Disjoint (P i).fp (P j).fp) ∧ ∀ i, (P i).holds s :=
  Iff.rfl

/-- Two members of a satisfied family separation at distinct indices have disjoint
    footprints. -/
theorem iSep_disj {ι : Type w} {P : ι → SAssert σ L} {s : σ} (h : (iSep P).holds s) {i j : ι}
    (hij : i ≠ j) : Disjoint (P i).fp (P j).fp :=
  h.1 i j hij

end SAssert

namespace X86

open SAssert
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState AMem read64 write64 Disjoint8
  read64_write64_of_disjoint)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout AbiArg ResultKind stackArgReg wordsAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk)

/-! ## Word locations -/

/-- The memory locations of the eight bytes from `a`. -/
def wordLocs (a : BitVec 64) : Set Loc := Loc.mem '' (⟨a, 8⟩ : Rng 64).toSet

/-- The memory locations of the eight-byte words from the addresses of `S`. -/
def wordsLocs (S : Set (BitVec 64)) : Set Loc := ⋃ a ∈ S, wordLocs a

/-- The locations of two words are disjoint exactly when the words are `Disjoint8`. -/
theorem disjoint_wordLocs_iff {a b : BitVec 64} :
    Disjoint (wordLocs a) (wordLocs b) ↔ Disjoint8 a b := by
  rw [wordLocs, wordLocs, Set.disjoint_image_iff loc_mem_injective, disjoint8_iff_disj,
    Rng.disj_iff_disjoint (r := ⟨a, 8⟩) (s := ⟨b, 8⟩) (Nat.succ_pos 7) (Nat.succ_pos 7)]

/-- The locations of two sets of words are disjoint exactly when every word of the first
    is `Disjoint8` from every word of the second. -/
theorem disjoint_wordsLocs_iff {S T : Set (BitVec 64)} :
    Disjoint (wordsLocs S) (wordsLocs T) ↔ ∀ a ∈ S, ∀ b ∈ T, Disjoint8 a b := by
  simp only [wordsLocs, Set.disjoint_iUnion_left, Set.disjoint_iUnion_right,
    disjoint_wordLocs_iff]
  exact ⟨fun h a ha b hb => h b hb a ha, fun h b hb a ha => h a ha b hb⟩

theorem wordsLocs_mono {S T : Set (BitVec 64)} (h : S ⊆ T) : wordsLocs S ⊆ wordsLocs T :=
  Set.biUnion_subset_biUnion_left h

/-- Register locations are disjoint from memory locations. -/
theorem disjoint_reg_wordsLocs (R : Set String) (S : Set (BitVec 64)) :
    Disjoint (Loc.reg '' R) (wordsLocs S) := by
  rw [Set.disjoint_left]
  rintro _ ⟨r, -, rfl⟩ h
  simp only [wordsLocs, wordLocs, Set.mem_iUnion, Set.mem_image] at h
  obtain ⟨_, _, _, _, h⟩ := h
  cases h

/-- States that agree on the locations of the word at `a` read the same word there. -/
theorem read64_congr {a : BitVec 64} {s t : AState}
    (h : Footprinted.AgreeOn (wordLocs a) s t) : read64 s.mem a = read64 t.mem a := by
  rw [← readLE_eight_eq_addrMem_read64, ← readLE_eight_eq_addrMem_read64]
  exact readLE_congr 8 a fun x hx => h (.mem x) ⟨x, hx, rfl⟩

/-- The words at `p + 8 k`, `k < n`. -/
def regionWords (p : BitVec 64) (n : Nat) : Set (BitVec 64) :=
  {x | ∃ k, k < n ∧ x = p + BitVec.ofNat 64 (8 * k)}

/-- The words at `rsp + o`, `lo ≤ o ≤ hi`. -/
def frameWords (rsp : BitVec 64) (lo hi : Int) : Set (BitVec 64) :=
  {x | ∃ o : Int, lo ≤ o ∧ o ≤ hi ∧ x = rsp + BitVec.ofInt 64 o}

theorem forall_mem_regionWords {p : BitVec 64} {n : Nat} {P : BitVec 64 → Prop} :
    (∀ x ∈ regionWords p n, P x) ↔ ∀ k, k < n → P (p + BitVec.ofNat 64 (8 * k)) :=
  ⟨fun h k hk => h _ ⟨k, hk, rfl⟩, fun h _ ⟨k, hk, e⟩ => e ▸ h k hk⟩

theorem forall_mem_frameWords {rsp : BitVec 64} {lo hi : Int} {P : BitVec 64 → Prop} :
    (∀ x ∈ frameWords rsp lo hi, P x) ↔
      ∀ o : Int, lo ≤ o → o ≤ hi → P (rsp + BitVec.ofInt 64 o) :=
  ⟨fun h o h1 h2 => h _ ⟨o, h1, h2, rfl⟩, fun h _ ⟨o, h1, h2, e⟩ => e ▸ h o h1 h2⟩

/-! ## The precondition of a layout -/

/-- The registers of `R` hold their values under `rv`. -/
def regsAt (R : List String) (rv : String → BitVec 64) : SAssert AState Loc where
  fp := Loc.reg '' {r | r ∈ R}
  holds s := ∀ r ∈ R, s.regs r = rv r
  supp s t h hs r hr :=
    (show s.regs r = t.regs r from h (.reg r) ⟨r, hr, rfl⟩).symm.trans (hs r hr)

@[simp] theorem holds_regsAt (R : List String) (rv : String → BitVec 64) (s : AState) :
    (regsAt R rv).holds s ↔ ∀ r ∈ R, s.regs r = rv r := Iff.rfl

/-- The addresses `rsp + 8 k` of the stack parameters `stackArgReg k` of `σ`. -/
def stackWords (σ : AbiLayout) (rsp : BitVec 64) : Set (BitVec 64) :=
  {x | ∃ a ∈ σ.args, ∃ k, a.reg = stackArgReg k ∧ x = rsp + BitVec.ofNat 64 (8 * k)}

/-- The stack parameters of `σ` at the entry register values `rv`: the value of the
    carrier name `stackArgReg k` of each stack parameter is the word at `%rsp + 8 k`. -/
def stackAt (σ : AbiLayout) (rv : String → BitVec 64) : SAssert AState Loc where
  fp := wordsLocs (stackWords σ (rv "%rsp"))
  holds s := ∀ a ∈ σ.args, ∀ k, a.reg = stackArgReg k →
    rv a.reg = read64 s.mem (rv "%rsp" + BitVec.ofNat 64 (8 * k))
  supp _ _ h hs a ha k hk :=
    (hs a ha k hk).trans (read64_congr (Footprinted.agreeOn_anti
      (Set.subset_biUnion_of_mem (u := wordLocs)
        (show rv "%rsp" + BitVec.ofNat 64 (8 * k) ∈ stackWords σ (rv "%rsp") from
          ⟨a, ha, k, hk, rfl⟩)) h))

/-- The registers a layout reads at entry: the stack pointer, the bounded registers and the
    parameter registers. -/
def abiRegs (σ : AbiLayout) : List String :=
  "%rsp" :: (σ.bounds.map (·.1) ++ σ.args.map (·.reg))

/-- **The precondition of the layout `σ`** at the entry register values `rv`: the registers
    of `abiRegs σ` hold their values; every bounded register is within its bound; the stack
    words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and the words of each pointer region are owned
    and separated; and, joined by `conj`, the stack parameters at entry. -/
def abiPre (σ : AbiLayout) (rv : String → BitVec 64) : SAssert AState Loc :=
  conj (regsAt (abiRegs σ) rv ∗ ⌜∀ b ∈ σ.bounds, (rv b.1).toNat ≤ b.2⌝ ∗
      own (wordsLocs (frameWords (rv "%rsp") σ.frameLo σ.frameHi)) ∗
      bigSep (σ.regions.map fun p => own (wordsLocs (regionWords (rv p.1) p.2))))
    (stackAt σ rv)

/-- A list is pairwise related under a symmetric relation exactly when its entries at any two
    distinct positions are related. -/
theorem pairwise_iff_getElem?_ne {α : Type} {R : α → α → Prop} (hR : ∀ {x y}, R x y → R y x)
    {l : List α} :
    l.Pairwise R ↔ ∀ (i j : Nat) (p q : α), i ≠ j → l[i]? = some p → l[j]? = some q → R p q := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j p q hij hp hq
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hp
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hq
    rcases Nat.lt_or_gt_of_ne hij with h1 | h1
    · exact h i j hi hj h1
    · exact hR (h j i hj hi h1)
  · intro h i j hi hj hij
    exact h i j _ _ (Nat.ne_of_lt hij) (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)

/-- The precondition of `σ` at `rv` holds at `s` exactly when the registers of `abiRegs σ`
    hold their values under `rv` and the entry conditions of `σ` hold at `s` with the
    register file `rv`. -/
theorem holds_abiPre (σ : AbiLayout) (rv : String → BitVec 64) (s : AState) :
    (abiPre σ rv).holds s ↔
      (∀ r ∈ abiRegs σ, s.regs r = rv r) ∧ σ.Regions { s with regs := rv } := by
  have hreg : ∀ (R : Set String) (X : Set Loc) (S : Set (BitVec 64)), X ⊆ wordsLocs S →
      Disjoint (Loc.reg '' R) X := fun R X S hX => (disjoint_reg_wordsLocs R S).mono_right hX
  have hdisj : Disjoint (regsAt (abiRegs σ) rv).fp
      ((⌜∀ b ∈ σ.bounds, (rv b.1).toNat ≤ b.2⌝ : SAssert AState Loc) ∗
        own (wordsLocs (frameWords (rv "%rsp") σ.frameLo σ.frameHi)) ∗
        bigSep (σ.regions.map fun p => own (wordsLocs (regionWords (rv p.1) p.2)))).fp := by
    refine hreg _ _ (frameWords (rv "%rsp") σ.frameLo σ.frameHi ∪
      ⋃ p ∈ σ.regions, regionWords (rv p.1) p.2) ?_
    rintro x (hx | hx | hx)
    · exact absurd hx (Set.notMem_empty x)
    · exact wordsLocs_mono (S := frameWords (rv "%rsp") σ.frameLo σ.frameHi)
        Set.subset_union_left hx
    · obtain ⟨P, hP, hx⟩ := mem_fp_bigSep.1 hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hP
      exact wordsLocs_mono (S := regionWords (rv p.1) p.2)
        (fun y hy => Or.inr (Set.mem_iUnion₂_of_mem hp hy)) hx
  have hpw : ∀ p q : String × Nat,
      Disjoint (own (wordsLocs (regionWords (rv p.1) p.2)) : SAssert AState Loc).fp
        (own (wordsLocs (regionWords (rv q.1) q.2)) : SAssert AState Loc).fp ↔
      ∀ k k', k < p.2 → k' < q.2 →
        Disjoint8 (rv p.1 + BitVec.ofNat 64 (8 * k)) (rv q.1 + BitVec.ofNat 64 (8 * k')) := by
    intro p q
    simp only [fp_own, disjoint_wordsLocs_iff, forall_mem_regionWords]
    exact ⟨fun h k k' hk hk' => h k hk k' hk', fun h k hk k' hk' => h k k' hk hk'⟩
  have hfr : Disjoint (own (wordsLocs (frameWords (rv "%rsp") σ.frameLo σ.frameHi)) :
        SAssert AState Loc).fp
        (bigSep (σ.regions.map fun p =>
          (own (wordsLocs (regionWords (rv p.1) p.2)) : SAssert AState Loc))).fp ↔
      ∀ p ∈ σ.regions, ∀ k, k < p.2 → ∀ o : Int, σ.frameLo ≤ o → o ≤ σ.frameHi →
        Disjoint8 (rv "%rsp" + BitVec.ofInt 64 o) (rv p.1 + BitVec.ofNat 64 (8 * k)) := by
    simp only [disjoint_fp_bigSep, List.forall_mem_map, fp_own, disjoint_wordsLocs_iff,
      forall_mem_frameWords, forall_mem_regionWords]
    exact ⟨fun h p hp k hk o h1 h2 => h p hp o h1 h2 k hk,
      fun h p hp o h1 h2 k hk => h p hp k hk o h1 h2⟩
  simp only [abiPre, holds_conj, holds_sep, holds_pure, holds_own, holds_bigSep,
    List.forall_mem_map, fp_pure, Set.empty_disjoint, true_and, implies_true, and_true]
  rw [List.pairwise_map, pairwise_iff_getElem?_ne (fun h => h.symm), hfr]
  simp only [hpw]
  unfold AbiLayout.Regions AbiLayout.StackIn
  constructor
  · rintro ⟨⟨-, hr, hb, hf, hpair⟩, hst⟩
    exact ⟨hr, hb, hpair, hf, hst⟩
  · rintro ⟨hr, hb, hpair, hf, hst⟩
    exact ⟨⟨hdisj, hr, hb, hf, hpair⟩, hst⟩

/-- A pointer region of a layout is the region of a parameter, carried in its register. -/
theorem mem_regions {σ : AbiLayout} {p : String × Nat} (hp : p ∈ σ.regions) :
    ∃ a ∈ σ.args, a.reg = p.1 := by
  obtain ⟨a, ha, hr⟩ := List.mem_filterMap.1 hp
  refine ⟨a, ha, ?_⟩
  unfold AbiArg.region at hr
  split at hr
  · cases hr
  · cases hr; rfl

/-- The entry conditions of `σ` read the register file only at `abiRegs σ`. -/
theorem regions_congr {σ : AbiLayout} {s t : AState}
    (h : ∀ r ∈ abiRegs σ, s.regs r = t.regs r) (hm : s.mem = t.mem) (hs : σ.Regions s) :
    σ.Regions t := by
  have hsp : s.regs "%rsp" = t.regs "%rsp" := h _ List.mem_cons_self
  have hb : ∀ b ∈ σ.bounds, s.regs b.1 = t.regs b.1 := fun b hb =>
    h _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hb)))
  have ha : ∀ a ∈ σ.args, s.regs a.reg = t.regs a.reg := fun a ha =>
    h _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
  have hp : ∀ p ∈ σ.regions, s.regs p.1 = t.regs p.1 := fun p hp => by
    obtain ⟨a, ha', e⟩ := mem_regions hp
    rw [← e]; exact ha a ha'
  obtain ⟨h1, h2, h3, h4⟩ := hs
  refine ⟨fun b hb' => hb b hb' ▸ h1 b hb', fun i j p q hij hpi hqj k k' hk hk' => ?_,
    fun p hp' k hk o ho1 ho2 => ?_, fun a ha' k hk => ?_⟩
  · rw [← hp p (List.mem_of_getElem? hpi), ← hp q (List.mem_of_getElem? hqj)]
    exact h2 i j p q hij hpi hqj k k' hk hk'
  · rw [← hsp, ← hp p hp']
    exact h3 p hp' k hk o ho1 ho2
  · rw [← ha a ha', ← hsp, ← hm]
    exact h4 a ha' k hk

/-- **The entry conditions of a layout as its precondition**: `σ.Regions sa` holds exactly
    when the precondition `abiPre σ rv` holds at `sa` for some entry register values `rv`.
    The separation conjuncts of `Regions` are the disjointness of the footprints of `∗`. -/
theorem regions_iff_abiPre (σ : AbiLayout) (sa : AState) :
    σ.Regions sa ↔ ∃ rv, (abiPre σ rv).holds sa := by
  constructor
  · intro h
    exact ⟨sa.regs, (holds_abiPre σ sa.regs sa).2 ⟨fun _ _ => rfl, h⟩⟩
  · rintro ⟨rv, h⟩
    obtain ⟨hr, hreg⟩ := (holds_abiPre σ rv sa).1 h
    exact regions_congr (s := { sa with regs := rv }) (fun r hr' => (hr r hr').symm) rfl hreg

/-! ## The read-back of a result -/

mutual

/-- The locations the read-back `κ` reads in the exit state, from the entry state `sa`. -/
def resLocs (sa : AState) : ResultKind → Set Loc
  | .reg r => {.reg r}
  | .words r n => wordsLocs (regionWords (sa.regs r) n)
  | .wordAt r i => wordLocs (sa.regs r + BitVec.ofNat 64 (8 * (sa.regs i).toNat))
  | .tuple ks => resLocsList sa ks

/-- `resLocs` of each entry of a list, joined. -/
def resLocsList (sa : AState) : List ResultKind → Set Loc
  | [] => ∅
  | k :: ks => resLocs sa k ∪ resLocsList sa ks

end

mutual

/-- Exit states that agree on `resLocs sa κ` have the same read-back. -/
theorem read_congr (sa : AState) {s t : AState} :
    (κ : ResultKind) → Footprinted.AgreeOn (resLocs sa κ) s t → κ.read sa s = κ.read sa t
  | .reg r, h => by
    simp only [ResultKind.read]
    rw [show s.regs r = t.regs r from h (.reg r) rfl]
  | .words r n, h => by
    simp only [ResultKind.read, wordsAt]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [read64_congr (Footprinted.agreeOn_anti (Set.subset_biUnion_of_mem (u := wordLocs)
      (show sa.regs r + BitVec.ofNat 64 (8 * j) ∈ regionWords (sa.regs r) n from
        ⟨j, List.mem_range.1 hj, rfl⟩)) h)]
  | .wordAt r i, h => by
    simp only [ResultKind.read]
    rw [read64_congr h]
  | .tuple ks, h => by
    simp only [ResultKind.read]
    rw [readList_congr sa ks h]

/-- `read_congr` on each entry of a list. -/
theorem readList_congr (sa : AState) {s t : AState} :
    (ks : List ResultKind) → Footprinted.AgreeOn (resLocsList sa ks) s t →
      ResultKind.readList sa s ks = ResultKind.readList sa t ks
  | [], _ => rfl
  | k :: ks, h => by
    simp only [ResultKind.readList]
    rw [read_congr sa (s := s) (t := t) k (Footprinted.agreeOn_anti Set.subset_union_left h),
      readList_congr sa ks (Footprinted.agreeOn_anti Set.subset_union_right h)]

end

/-- **The result value `v` laid out as `σ` reads it back** from the entry state `sa`: an
    assertion on the exit state, with the registers and memory words the read-back reads as
    its footprint. -/
def valAt (σ : AbiLayout) (sa : AState) (v : _root_.Hax.Value) : SAssert AState Loc where
  fp := resLocs sa σ.result
  holds s := v = σ.result.read sa s
  supp _ _ h hs := hs.trans (read_congr sa σ.result h)

/-- `valAt` holds at the exit state `sa'` exactly when `v` is the read-back of the
    result. -/
theorem valAt_holds_iff (σ : AbiLayout) (sa sa' : AState) (v : _root_.Hax.Value) :
    (valAt σ sa v).holds sa' ↔ σ.ResultOf sa sa' v := Iff.rfl

/-! ## The separation of the image simulation -/

/-- The locations of an optional word. -/
def optWordLocs : Option (BitVec 64) → Set Loc
  | some a => wordLocs a
  | none => ∅

/-- The locations of the cell `j` of the slot array `A`: the word `cellAt (base A) j` when
    some slot holds an array `A` of more than `j` words, and none otherwise. -/
def cellLocs (slotArr : String → Option (String × Nat)) (base : String → BitVec 64)
    (c : String × Nat) : Set Loc :=
  {l | (∃ q n, slotArr q = some (c.1, n) ∧ c.2 < n) ∧ l ∈ wordLocs (cellAt (base c.1) c.2)}

/-- The frame words, owned and pairwise separated. -/
def imgFrames (frame : String → Option (BitVec 64)) : SAssert AState Loc :=
  iSep fun q => own (optWordLocs (frame q))

/-- The cells of the slot arrays, owned and pairwise separated. -/
def imgCells (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) :
    SAssert AState Loc :=
  iSep fun c => own (cellLocs slotArr base c)

/-- The length, general-purpose and slot conditions of `ImgSep`. -/
def ImgSide (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat)) :
    Prop :=
  (∀ q q' A n n', slotArr q = some (A, n) → slotArr q' = some (A, n') → n = n')
    ∧ (∀ r, gpOk r = true → frame r = none)
    ∧ ∀ q A n, slotArr q = some (A, n) → ∃ a, frame q = some a

/-- **The image separation as an assertion**: the side conditions as a pure fact, and the
    cells of the slot arrays separated from the frame words and from the red-zone word. -/
def imgSepA (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) : SAssert AState Loc :=
  ⌜ImgSide frame slotArr⌝ ∗ imgCells slotArr base ∗ conj (imgFrames frame) (own (wordLocs (redW rsp)))

theorem disjoint_optWordLocs_iff {a b : Option (BitVec 64)} :
    Disjoint (optWordLocs a) (optWordLocs b) ↔
      ∀ x y, a = some x → b = some y → Disjoint8 x y := by
  cases a <;> cases b <;> simp [optWordLocs, disjoint_wordLocs_iff]

theorem disjoint_cellLocs_iff {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {c : String × Nat} {X : Set Loc} :
    Disjoint (cellLocs slotArr base c) X ↔
      ((∃ q n, slotArr q = some (c.1, n) ∧ c.2 < n) →
        Disjoint (wordLocs (cellAt (base c.1) c.2)) X) := by
  by_cases hc : ∃ q n, slotArr q = some (c.1, n) ∧ c.2 < n
  · have e : cellLocs slotArr base c = wordLocs (cellAt (base c.1) c.2) := by
      ext l; simp [cellLocs, hc]
    rw [e]; exact ⟨fun h _ => h, fun h => h hc⟩
  · have e : cellLocs slotArr base c = ∅ := by
      ext l; simp [cellLocs, hc]
    rw [e]; exact ⟨fun _ h => absurd h hc, fun _ => Set.empty_disjoint X⟩

section Projections

variable {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
  {base : String → BitVec 64} {rsp : BitVec 64} {s : AState}

/-- The footprint of the cells is disjoint from those of the frame words and of the red-zone
    word, at the cell `j` of an array `A` some slot holds. -/
theorem imgSepA_cell_disj (h : (imgSepA frame slotArr base rsp).holds s) {q A : String}
    {n j : Nat} (hq : slotArr q = some (A, n)) (hj : j < n) :
    (∀ q', Disjoint (wordLocs (cellAt (base A) j)) (optWordLocs (frame q'))) ∧
      Disjoint (wordLocs (cellAt (base A) j)) (wordLocs (redW rsp)) := by
  have h1 : Disjoint (⋃ c, cellLocs slotArr base c)
      ((⋃ q, optWordLocs (frame q)) ∪ wordLocs (redW rsp)) := h.2.2.1
  have h2 : Disjoint (cellLocs slotArr base (A, j))
      ((⋃ q, optWordLocs (frame q)) ∪ wordLocs (redW rsp)) :=
    h1.mono_left (Set.subset_iUnion (cellLocs slotArr base) (A, j))
  have h3 := disjoint_cellLocs_iff.1 h2 ⟨q, n, hq, hj⟩
  exact ⟨fun q' => h3.mono_right
      ((Set.subset_iUnion (fun q => optWordLocs (frame q)) q').trans Set.subset_union_left),
    h3.mono_right Set.subset_union_right⟩

/-- Distinct frame words of the image separation are `Disjoint8`. -/
theorem imgSepA_frames (h : (imgSepA frame slotArr base rsp).holds s) {q q' : String}
    {a a' : BitVec 64} (ha : frame q = some a) (ha' : frame q' = some a') (hne : q ≠ q') :
    Disjoint8 a a' := by
  have h1 := iSep_disj (P := fun q => (own (optWordLocs (frame q)) : SAssert AState Loc))
    h.2.2.2.2.1 hne
  simp only [fp_own, ha, ha', optWordLocs] at h1
  exact disjoint_wordLocs_iff.1 h1

/-- A cell of a slot array is `Disjoint8` from every frame word. -/
theorem imgSepA_cellFrame (h : (imgSepA frame slotArr base rsp).holds s) {q A : String}
    {n j : Nat} (hq : slotArr q = some (A, n)) (hj : j < n) {q' : String} {a : BitVec 64}
    (ha : frame q' = some a) : Disjoint8 (cellAt (base A) j) a := by
  have h1 := (imgSepA_cell_disj h hq hj).1 q'
  rw [ha] at h1
  exact disjoint_wordLocs_iff.1 h1

/-- The red-zone word is `Disjoint8` from every cell of a slot array. -/
theorem imgSepA_red (h : (imgSepA frame slotArr base rsp).holds s) {q A : String} {n j : Nat}
    (hq : slotArr q = some (A, n)) (hj : j < n) : Disjoint8 (redW rsp) (cellAt (base A) j) :=
  (disjoint_wordLocs_iff.1 (imgSepA_cell_disj h hq hj).2).symm

/-- Distinct cells of the slot arrays are `Disjoint8`. -/
theorem imgSepA_cells (h : (imgSepA frame slotArr base rsp).holds s) {q q' A A' : String}
    {n n' j j' : Nat} (hq : slotArr q = some (A, n)) (hq' : slotArr q' = some (A', n'))
    (hj : j < n) (hj' : j' < n') (hne : A ≠ A' ∨ j ≠ j') :
    Disjoint8 (cellAt (base A) j) (cellAt (base A') j') := by
  have h1 := iSep_disj (P := fun c => (own (cellLocs slotArr base c) : SAssert AState Loc))
    h.2.2.2.1 (i := (A, j)) (j := (A', j')) (by rintro ⟨⟩; rcases hne with h | h <;> exact h rfl)
  simp only [fp_own] at h1
  rw [disjoint_cellLocs_iff] at h1
  have h2 := h1 ⟨q, n, hq, hj⟩
  rw [disjoint_comm, disjoint_cellLocs_iff] at h2
  exact disjoint_wordLocs_iff.1 (h2 ⟨q', n', hq', hj'⟩).symm

/-- **A store into a frame word keeps the other words** of the image separation: every other
    frame word and every cell of a slot array read the same after the store, the memory
    step of `ImageAddrSim.rel_sstore`. -/
theorem imgSepA_store_frame (h : (imgSepA frame slotArr base rsp).holds s) {q : String}
    {a : BitVec 64} (ha : frame q = some a) (mem : AMem) (v : BitVec 64) :
    (∀ q' a', frame q' = some a' → q' ≠ q → read64 (write64 mem a v) a' = read64 mem a') ∧
      ∀ q' A n j, slotArr q' = some (A, n) → j < n →
        read64 (write64 mem a v) (cellAt (base A) j) = read64 mem (cellAt (base A) j) :=
  ⟨fun _ _ ha' hne => read64_write64_of_disjoint _ _ _ _ (imgSepA_frames h ha ha' (Ne.symm hne)),
    fun _ _ _ _ hq hj => read64_write64_of_disjoint _ _ _ _ (imgSepA_cellFrame h hq hj ha).symm⟩

end Projections

/-- **`ImgSep` is the holding of `imgSepA`** at every state. -/
theorem imgSep_iff_sep (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (s : AState) : ImgSep frame slotArr base rsp ↔ (imgSepA frame slotArr base rsp).holds s := by
  constructor
  · intro h
    refine ⟨Set.empty_disjoint _, ⟨h.len, h.gp, h.slotFrame⟩, ?_, ⟨?_, fun _ => trivial⟩,
      ⟨?_, fun _ => trivial⟩, trivial⟩
    · show Disjoint (⋃ c, cellLocs slotArr base c)
        ((⋃ q, optWordLocs (frame q)) ∪ wordLocs (redW rsp))
      rw [Set.disjoint_iUnion_left]
      rintro ⟨A, j⟩
      rw [disjoint_cellLocs_iff]
      rintro ⟨q, n, hq, hj⟩
      rw [Set.disjoint_union_right, Set.disjoint_iUnion_right]
      refine ⟨fun q' => ?_, (disjoint_wordLocs_iff.2 (h.red q A n j hq hj)).symm⟩
      cases ha : frame q' with
      | none => exact Set.disjoint_empty _
      | some a => exact disjoint_wordLocs_iff.2 (h.cellFrame q A n j hq hj q' a ha)
    · rintro ⟨A, j⟩ ⟨A', j'⟩ hne
      show Disjoint (cellLocs slotArr base (A, j)) (cellLocs slotArr base (A', j'))
      rw [disjoint_cellLocs_iff]
      rintro ⟨q, n, hq, hj⟩
      rw [disjoint_comm, disjoint_cellLocs_iff]
      rintro ⟨q', n', hq', hj'⟩
      refine (disjoint_wordLocs_iff.2 (h.cells q A n q' A' n' j j' hq hq' hj hj' ?_)).symm
      by_cases hA : A = A'
      · subst hA
        exact Or.inr fun e => hne (by rw [e])
      · exact Or.inl hA
    · intro q q' hne
      show Disjoint (optWordLocs (frame q)) (optWordLocs (frame q'))
      rw [disjoint_optWordLocs_iff]
      intro a a' ha ha'
      exact h.frames q q' a a' ha ha' hne
  · intro h
    exact ⟨fun q q' a a' ha ha' hne => imgSepA_frames h ha ha' hne,
      fun q A n j hq hj q' a ha => imgSepA_cellFrame h hq hj ha,
      fun q A n q' A' n' j j' hq hq' hj hj' hne => imgSepA_cells h hq hq' hj hj' hne,
      h.2.1.1, fun q A n j hq hj => imgSepA_red h hq hj, h.2.1.2.1, h.2.1.2.2⟩

/-! ## Instances -/

/-- A layout with two pointer regions of two words and a frame of three words. -/
private def exLayout : AbiLayout where
  args := [⟨"x", "%rdi", .words 2⟩, ⟨"y", "%rsi", .words 2⟩]
  consts := []
  result := .tuple [.words "%rdi" 2, .wordAt "%rsi" "%rdi"]
  bounds := []
  frameLo := -16
  frameHi := 0

/-- An entry state of `exLayout`. -/
private def exState : AState where
  regs r := if r = "%rdi" then 0x1000 else if r = "%rsi" then 0x2000 else
    if r = "%rsp" then 0x8000 else 0
  mem _ := 0

private theorem exLayout_abiPre : ∃ rv, (abiPre exLayout rv).holds exState := by
  refine (regions_iff_abiPre _ _).1 ⟨fun b hb => by simp [exLayout] at hb, ?_, ?_,
    AbiLayout.stackIn_of_regCarriedB (by decide) _⟩
  · intro i j p q hij hp hq k k' hk hk'
    have e : exLayout.regions = [("%rdi", 2), ("%rsi", 2)] := rfl
    rw [e] at hp hq
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
      simp at hp hq hij <;> subst hp hq <;> simp only at hk hk' <;>
      simp only [exState, Disjoint8, if_pos, if_neg, String.reduceEq, not_false_eq_true, BitVec.reduceToNat,
        BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  · intro p hp k hk o ho1 ho2
    have e : exLayout.regions = [("%rdi", 2), ("%rsi", 2)] := rfl
    rw [e] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [exLayout] at ho1 ho2
    rcases hp with rfl | rfl <;> simp only at hk <;>
      simp only [exState, Disjoint8, if_pos, if_neg, String.reduceEq, not_false_eq_true, BitVec.reduceToNat,
        BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt] <;> omega

example : (valAt exLayout exState (.tuple [.array [.int 0, .int 0], .int 0])).holds
    { exState with mem := fun _ => 0 } := by
  rw [valAt_holds_iff]
  rfl

/-- Two frame words `s0`, `s1` holding the pointers of the arrays `A` and `B`. -/
private def exFrame (q : String) : Option (BitVec 64) :=
  if q = "s0" then some 0x7f00 else if q = "s1" then some 0x7f08 else none

private def exSlot (q : String) : Option (String × Nat) :=
  if q = "s0" then some ("A", 2) else if q = "s1" then some ("B", 1) else none

private def exBase (A : String) : BitVec 64 := if A = "A" then 0x1000 else 0x2000

private theorem exFrame_imgSepA : (imgSepA exFrame exSlot exBase 0x8000).holds exState := by
  refine (imgSep_iff_sep _ _ _ _ _).1 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q q' a a' ha ha' hne
    simp only [exFrame] at ha ha'
    split_ifs at ha ha' <;> cases ha <;> cases ha' <;> simp_all [Disjoint8]
  · intro q A n j hq hj q' a ha
    simp only [exFrame, exSlot] at ha hq
    split_ifs at ha hq <;> cases ha <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at hq <;>
      obtain ⟨rfl, rfl⟩ := hq <;>
      simp only [cellAt, exBase, Disjoint8, if_pos, if_neg, String.reduceEq,
        not_false_eq_true, BitVec.reduceToNat, BitVec.toNat_sub, BitVec.toNat_add,
        BitVec.toNat_ofNat] <;> omega
  · intro q A n q' A' n' j j' hq hq' hj hj' hne
    simp only [exSlot] at hq hq'
    split_ifs at hq hq' <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at hq hq' <;>
      obtain ⟨rfl, rfl⟩ := hq <;> obtain ⟨rfl, rfl⟩ := hq' <;>
      simp only [cellAt, exBase, Disjoint8, if_pos, if_neg, String.reduceEq, ne_eq,
        not_true_eq_false, false_or, not_false_eq_true, BitVec.reduceToNat, BitVec.toNat_sub,
        BitVec.toNat_add, BitVec.toNat_ofNat] at hne ⊢ <;> omega
  · intro q q' A n n' hq hq'
    simp only [exSlot] at hq hq'
    split_ifs at hq hq' <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at hq hq' <;>
      obtain ⟨rfl, rfl⟩ := hq <;> obtain ⟨h1, rfl⟩ := hq' <;>
      first | rfl | exact absurd h1 (by decide)
  · intro q A n j hq hj
    simp only [exSlot] at hq
    split_ifs at hq <;> simp only [Option.some.injEq, Prod.mk.injEq] at hq <;>
      obtain ⟨rfl, rfl⟩ := hq <;>
      simp only [redW, X86Backend.LprogBytes.cmovRedZone, cellAt, exBase, Disjoint8, if_pos,
        if_neg, String.reduceEq, not_false_eq_true, BitVec.reduceToNat, BitVec.toNat_sub,
        BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt] <;> omega
  · intro r hr
    simp only [exFrame]
    split_ifs with h1 h2
    · subst h1; revert hr; decide
    · subst h2; revert hr; decide
    · rfl
  · intro q A n hq
    simp only [exSlot, exFrame] at hq ⊢
    split_ifs at hq ⊢ <;> simp_all

end X86

end CatCrypt.Crypto.SecureCompilation.SepLogic
