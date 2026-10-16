/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.X86State
public import CatCrypt.Crypto.SecureCompilation.Ascent.Footprint

/-!
# The footprint calculus of `runBlockA` in the separation logic

`Ascent.Footprint` states frame rules for the straight-line run `AddrMem.runBlockA` over
memory predicates with ranges (`Supported S R`) and over the word ranges a run reads and
writes (`reads`, `writes`). This module states them in the separation logic over
`AddrMem.AState` (`SepLogic.X86`).

## Main results

* a memory predicate supported on the ranges `S` is the predicate of an assertion whose
  footprint is the memory locations of the bytes of `S` (`X86.ofSupported`,
  `X86.supported_iff_sassert`);
* the run of a block writes in the registers, the flags and the bytes of its written ranges
  (`X86.writesIn_runBlockA`);
* `X86.runFoot blk W D` owns the registers, the flags and the bytes `W ∪ D` and states that
  the run of `blk` writes in `W` and reads in `D`; it depends only on its footprint, by
  `Footprint.runBlockA_local`. `Triple.frame` then gives the frame rule of the run for every
  separated assertion (`X86.triple_runBlockA_frame`);
* a run preserves an assertion whose footprint avoids the registers, the flags and the
  written bytes (`X86.runBlockA_frame`); `Footprint.supported_frame` is its instance at
  `X86.ofSupported`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic.X86

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
open Footprinted SAssert

/-- The memory locations of the bytes of the ranges `S`. -/
def rngLocs (S : List Ascent.Footprint.Rng) : Set Loc := Loc.mem '' {x | ∃ r ∈ S, x ∈ r}

/-- The assertion of a memory predicate supported on the ranges `S`: footprint the bytes of
    `S`. -/
def ofSupported (S : List Ascent.Footprint.Rng) (R : AMem → Prop) (h : Supported S R) :
    SAssert AState Loc where
  fp := rngLocs S
  holds s := R s.mem
  supp s t hst hs := h s.mem t.mem
    (fun r hr x hx => (hst (.mem x) ⟨x, ⟨r, hr, hx⟩, rfl⟩).symm) hs

/-- **Supported predicates are assertions.** A memory predicate is supported on the ranges
    `S` exactly when it is the predicate of an assertion with footprint the bytes of `S`. -/
theorem supported_iff_sassert {S : List Ascent.Footprint.Rng} {R : AMem → Prop} :
    Supported S R ↔ ∃ P : SAssert AState Loc, P.fp = rngLocs S ∧ ∀ s, P.holds s ↔ R s.mem := by
  refine ⟨fun h => ⟨ofSupported S R h, rfl, fun _ => Iff.rfl⟩, ?_⟩
  rintro ⟨P, hfp, hP⟩ m m' hmm hR
  refine (hP { regs := fun _ => 0, mem := m' }).1
    (P.supp { regs := fun _ => 0, mem := m } _ ?_ ((hP _).2 hR))
  rw [hfp]
  rintro _ ⟨x, ⟨r, hr, hx⟩, rfl⟩
  exact (hmm r hr x hx).symm

/-- The register and flag locations. -/
def ctlLocs : Set Loc := {l | ∀ a, l ≠ .mem a}

/-- The bytes of the ranges the run of `blk` from `s` writes. -/
def writeBytes (blk : List (JInstr 64)) (s : AState) : Set (BitVec 64) :=
  {x | ∃ w ∈ writes blk s, x ∈ w}

/-- The bytes of the ranges the run of `blk` from `s` reads. -/
def readBytes (blk : List (JInstr 64)) (s : AState) : Set (BitVec 64) :=
  {x | ∃ w ∈ reads blk s, x ∈ w}

theorem reg_mem_ctlLocs (r : String) : Loc.reg r ∈ ctlLocs := fun _ h => by cases h

theorem flag_mem_ctlLocs (f : Flag) : Loc.flag f ∈ ctlLocs := fun _ h => by cases h

/-- The run of a block writes in the registers, the flags and the bytes of its written
    ranges. -/
theorem writesIn_runBlockA (blk : List (JInstr 64)) :
    WritesIn (fun s => runBlockA s blk) (fun s => ctlLocs ∪ Loc.mem '' writeBytes blk s) := by
  intro s l hl
  cases l with
  | reg r => exact absurd (Or.inl (reg_mem_ctlLocs r)) hl
  | flag f => exact absurd (Or.inl (flag_mem_ctlLocs f)) hl
  | mem x =>
    show s.mem x = (runBlockA s blk).mem x
    exact (writes_sound blk s x fun w hw hxw => hl (Or.inr ⟨x, ⟨w, hw, hxw⟩, rfl⟩)).symm

/-- The run of `blk` writes in the bytes `W` and reads in the bytes `D`; footprint the
    registers, the flags and the bytes of `W ∪ D`. -/
def runFoot (blk : List (JInstr 64)) (W D : Set (BitVec 64)) : SAssert AState Loc where
  fp := ctlLocs ∪ Loc.mem '' (W ∪ D)
  holds s := writeBytes blk s ⊆ W ∧ readBytes blk s ⊆ D
  supp s t hst hs := by
    have hr : s.regs = t.regs := funext fun r => hst (.reg r) (Or.inl (reg_mem_ctlLocs r))
    have hf : s.flags = t.flags := by
      have g : ∀ f : Flag, f.get s.flags = f.get t.flags :=
        fun f => hst (.flag f) (Or.inl (flag_mem_ctlLocs f))
      revert g
      generalize s.flags = F
      generalize t.flags = G
      intro g
      have g1 := g .cf
      have g2 := g .pf
      have g3 := g .zf
      have g4 := g .sf
      have g5 := g .of
      cases F
      cases G
      simp_all [Flag.get]
    have hm : ∀ r ∈ reads blk s, ∀ x, x ∈ r → t.mem x = s.mem x := fun r hr' x hx =>
      (hst (.mem x) (Or.inr ⟨x, Or.inr (hs.2 ⟨r, hr', hx⟩), rfl⟩)).symm
    obtain ⟨-, -, -, -, k5, k6⟩ := runBlockA_local blk s t hr hf hm
    refine ⟨fun x hx => hs.1 ?_, fun x hx => hs.2 ?_⟩
    · simpa only [writeBytes, k6] using hx
    · simpa only [readBytes, k5] using hx

/-- **The frame rule of `runBlockA` as an instance of `Triple.frame`.** A run that writes in
    `W` and reads in `D` preserves every assertion separated from the registers, the flags
    and the bytes of `W ∪ D`. -/
theorem triple_runBlockA_frame (blk : List (JInstr 64)) (W D : Set (BitVec 64))
    (R : SAssert AState Loc) :
    Triple (runFoot blk W D ∗ R) (fun s => runBlockA s blk) (own (runFoot blk W D).fp ∗ R) :=
  Triple.frame R (fun _ _ => trivial) (writesIn_runBlockA blk)
    (fun _ hs => Set.union_subset_union_right _
      (Set.image_mono (hs.1.trans Set.subset_union_left))) subset_rfl

/-- **The frame rule of `runBlockA` at a state.** A run preserves every assertion whose
    footprint avoids the registers, the flags and the bytes the run writes. -/
theorem runBlockA_frame (blk : List (JInstr 64)) (R : SAssert AState Loc) {s : AState}
    (hd : Disjoint R.fp (ctlLocs ∪ Loc.mem '' writeBytes blk s)) (h : R.holds s) :
    R.holds (runBlockA s blk) :=
  R.supp _ _ (agreeOn_anti (fun _ hl hw => Set.disjoint_left.1 hd hl hw)
    (writesIn_runBlockA blk s)) h

/-- The bytes of supported ranges disjoint from every written range avoid the registers,
    the flags and the written bytes. -/
theorem rngLocs_disjoint {S : List Ascent.Footprint.Rng} {blk : List (JInstr 64)} {s : AState}
    (hd : ∀ w ∈ writes blk s, ∀ r ∈ S, w.Disj r) :
    Disjoint (rngLocs S) (ctlLocs ∪ Loc.mem '' writeBytes blk s) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, ⟨r, hr, hx⟩, rfl⟩ (hc | ⟨y, ⟨w, hw, hy⟩, he⟩)
  · exact hc x rfl
  · cases he
    exact (hd w hw r hr).not_mem hy hx

/-- `Footprint.supported_frame` is the frame rule `runBlockA_frame` at `ofSupported`. -/
example {S : List Ascent.Footprint.Rng} {R : AMem → Prop} (hR : Supported S R)
    (blk : List (JInstr 64)) (s : AState) (hd : ∀ w ∈ writes blk s, ∀ r ∈ S, w.Disj r)
    (h : R s.mem) : R (runBlockA s blk).mem :=
  runBlockA_frame blk (ofSupported S R hR) (rngLocs_disjoint hd) h

end CatCrypt.Crypto.SecureCompilation.SepLogic.X86
