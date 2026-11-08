/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxAnnotFix
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVComplete

/-!
# Completeness of the bounds-invariant check on straight-line bodies

`IdxInvCheck.idxInvCheckB` checks a body block by block under an annotation of index facts.
A non-empty straight-line body has one block, which falls off the end (`cfgOf_straight`), so
the check reduces to two conditions: the index obligations of the symbolic run of the whole
body (`symObl`) follow from the facts of block `0`, and the entry facts give the facts of
block `0`. The second holds for the annotation `idxAnnot` (`idxAnnot_entry`). The first holds
without any fact when every obligation has an immediate index of width `64` below the length
of its array: the affine form of such an index is its value (`oblsOk_of_imm`).

## Main results

* `oblsOk_of_imm`: obligations with immediate indices below their lengths pass `oblsOk` under
  any facts.
* `idxInvCheckB_idxAnnot_straight`: on a non-empty straight-line body whose symbolic run is
  inside the fragment and whose index obligations are immediates below their lengths, the
  check accepts any entry facts with the annotation `idxAnnot`.
* `idxInvCheckB_straight`: the same at the entry facts `boundFacts σ nm` of a layout.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)

/-- **Obligations over immediate indices pass**: when every obligation of `os` has an
    immediate index `c` of width `64` below the length of its array, `oblsOk F os` holds for
    every list of facts `F`. -/
theorem oblsOk_of_imm (F : List SFact) {os : List SObl}
    (h : ∀ o ∈ os, ∃ c, o.1 = .immW 64 c ∧ c < o.2) : oblsOk F os = true := by
  simp only [oblsOk, List.all_eq_true]
  intro o ho
  obtain ⟨c, hc, hlt⟩ := h o ho
  have h1 := oblsOk_of_bounds (F := F) (t := o.1) (n := o.2) (by omega) (fun _ => 0)
    (by simp [hc, affOf]) (by simp [hc, affOf]; omega)
  simpa [oblsOk] using h1

/-- **Completeness on straight-line bodies.** A non-empty body of straight-line instructions
    (no terminator, label or barred instruction) whose symbolic run is inside the fragment and
    whose index obligations are immediates of width `64` below the lengths of their arrays
    passes `idxInvCheckB` from any entry facts `entry` with the annotation `idxAnnot`. -/
theorem idxInvCheckB_idxAnnot_straight (entry : List IdxFact) {B : List LinstrRM}
    (hne : B ≠ []) (hs : ∀ p ∈ B, straightR p.1 = true)
    (hunk : symRun B SSt.start ≠ .unk)
    (hidx : ∀ o ∈ symObl B SSt.start, ∃ c, o.1 = .immW 64 c ∧ c < o.2) :
    idxInvCheckB entry (idxAnnot entry B) B = true := by
  have hG := cfgOf_straight (wl := B.map Prod.fst) (by simpa using hne)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs p hp)
  have hterm : ∀ n, ((straightCFG n).blk 0).term = .fall none := fun _ => rfl
  unfold idxInvCheckB
  rw [hG]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun k hk => ?_, fun f hf => idxAnnot_entry f hf⟩
  have hk0 : k = 0 := by simpa [straightCFG] using hk
  subst hk0
  unfold blockInvOk
  simp only [hterm, bodyAt_straight]
  cases hr : symRun B SSt.start with
  | ok ss gs =>
      simp only [termInvOk, Bool.and_true]
      exact oblsOk_of_imm _ hidx
  | fail => rfl
  | unk => exact absurd hr hunk

/-- **Completeness on straight-line bodies at a layout's entry facts.** The check
    `idxInvCheckB` accepts, from the facts `boundFacts σ nm` of the register bounds of the
    layout `σ` and with the annotation `idxAnnot`, a non-empty straight-line body whose
    symbolic run is inside the fragment and whose index obligations are immediates of width
    `64` below the lengths of their arrays. -/
theorem idxInvCheckB_straight (σ : AbiLayout) (nm : String → String) {B : List LinstrRM}
    (hne : B ≠ []) (hs : ∀ p ∈ B, straightR p.1 = true)
    (hunk : symRun B SSt.start ≠ .unk)
    (hidx : ∀ o ∈ symObl B SSt.start, ∃ c, o.1 = .immW 64 c ∧ c < o.2) :
    idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B = true :=
  idxInvCheckB_idxAnnot_straight _ hne hs hunk hidx

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
