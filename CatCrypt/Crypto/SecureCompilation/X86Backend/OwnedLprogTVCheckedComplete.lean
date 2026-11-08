/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm

/-!
# Completeness of the checker on bounds-checked runs for straight-line bodies

`OwnedLprogTVChecked.ownedCheckMC` extends `OwnedLprogTV.ownedCheckM` by the must-constant
table (`constAnnotArr`, checked by `factCheck`), the shared runs from the facts of each block
(`runsOfC`), the index obligations (`oblCheckWith`) and the conjuncts `hasOutsB` and
`blocksRunCB`. This module proves that it accepts two straight-line bodies whose shared runs
agree up to guards (`ResW`), as `ownedCheckM` does (`ownedCheckM_of_resW`).

A non-empty straight-line body has one block (`cfgOf_straight`), so the must-constant table
is empty, every block starts from no fact, `factCheck` holds (`factCheck_nil`) and the shared
runs from the facts are the shared runs of `ownedCheckM`. The remaining conjuncts follow from
properties of the runs: an observed name gives `hasOutsB`; a call-free body has one piece
between its calls (`callFreePieces_of_isNone`), and a symbolic run that does not fail gives
`blocksRunCB`; index obligations of the rewritten body that are obligations of the source
body over constant indices give `oblCheckWith`.

## Main results

* `ResW_of_Res`: agreement of runs gives agreement up to guards.
* `callFreePieces_of_isNone`: a body without call shadows is its only piece.
* `ownedCheckMC_of_resW`, `ownedCheckMC_of_res`: completeness of `ownedCheckMC` on
  straight-line bodies.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-- Agreement of the runs (`Res`) gives agreement up to guards (`ResW`). -/
theorem ResW_of_Res {T' : Tbl} {o : SOut} {r : Tbl × SOut} (h : Res T' o r) : ResW T' o r := by
  obtain ⟨R, o'⟩ := r
  cases o with
  | ok s g =>
      cases o' with
      | ok s' g' =>
          obtain ⟨h1, h2, rfl⟩ := h
          exact ⟨h1, h2, fun x hx => hx⟩
      | fail => exact h.elim
      | unk => exact h.elim
  | fail => trivial
  | unk => trivial

/-- A list of instructions without call shadows is its only piece between calls. -/
theorem callFreePieces_of_isNone :
    ∀ {B : List LinstrRM}, (∀ p ∈ B, (LprogIsa.shadowCall? p.1).isNone = true) →
      callFreePieces B = [B]
  | [], _ => rfl
  | i :: is, h => by
      have ih := callFreePieces_of_isNone (fun p hp => h p (List.mem_cons_of_mem _ hp))
      have hi := h i List.mem_cons_self
      simp_all [callFreePieces]

/-- The must-constant table of a straight-line graph is empty: every block has no fact. -/
theorem annotAt_constAnnotArr_straight (B : List LinstrRM) (n : Nat)
    (sym : LinstrRM → SSt → SOut) :
    annotAt (constAnnotArr B (straightCFG n) sym) = fun _ => [] := by
  funext k
  simp [annotAt, constAnnotArr, straightCFG]

/-- **Completeness for straight-line bodies, up to guards.** Two non-empty straight-line
    typed bodies whose shared runs agree up to guards (`ResW`), the source run being inside the
    fragment and not failing, pass `ownedCheckMC` when an output is observed, the source body
    has no call shadow, and every index obligation of the rewritten body is an obligation of
    the source body whose index is a constant (it reads no name and no flag). -/
theorem ownedCheckMC_of_resW (outs : List String) {B B' : List LinstrRM} (hne : B ≠ [])
    (hne' : B' ≠ []) (hs : ∀ p ∈ B, straightR p.1 = true)
    (hs' : ∀ p ∈ B', straightR p.1 = true)
    (hres : ResW (tRun B SSt.start Tbl.empty).1 (tRun B SSt.start Tbl.empty).2
      (tRun B' SSt.start (tRun B SSt.start Tbl.empty).1))
    (hunk : (tRun B SSt.start Tbl.empty).2 ≠ .unk) (hout : outs ≠ [])
    (hcall : ∀ p ∈ B, (LprogIsa.shadowCall? p.1).isNone = true)
    (hstep : symRun B SSt.start ≠ .fail)
    (hobl : ∀ o ∈ symObl B' SSt.start,
      o ∈ symObl B SSt.start ∧ o.1.vars = [] ∧ o.1.readsF = false) :
    ownedCheckMC outs B B' = true := by
  have hM := ownedCheckM_of_resW outs hne hne' hs hs' hres hunk
  have hG := cfgOf_straight (wl := B.map Prod.fst) (by simpa using hne)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs p hp)
  have hG' := cfgOf_straight (wl := B'.map Prod.fst) (by simpa using hne')
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs' p hp)
  have hRC : ∀ n n', runsOfC (fun _ => []) (fun _ => []) B B' (straightCFG n)
      (straightCFG n') symStep = runsOf B B' (straightCFG n) (straightCFG n') symStep :=
    fun _ _ => rfl
  have hterm : ∀ n, ((straightCFG n).blk 0).term = .fall none := fun _ => rfl
  unfold ownedCheckM at hM
  rw [hG, hG'] at hM
  unfold ownedCheckMC
  rw [hG, hG']
  dsimp only
  simp only [annotAt_constAnnotArr_straight, hRC]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hM, ?_⟩, factCheck_nil _ _ _⟩, factCheck_nil _ _ _⟩, ?_⟩, ?_⟩
  · simp only [oblCheckWith, hG, hG', List.all_eq_true, List.mem_range]
    intro k hk
    have hk0 : k = 0 := by simpa [straightCFG] using hk
    subst hk0
    rw [hterm]
    simp only [oblOk, startC_nil, bodyAt_straight]
    split
    · simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem]
      intro o ho
      obtain ⟨h1, h2, h3⟩ := hobl o ho
      exact ⟨h1, by simp [okIn, vIn, h2, h3]⟩
    · rfl
  · simp [hasOutsB, hout]
  · simp only [blocksRunCB, hG, List.all_eq_true, List.mem_range]
    intro k hk
    have hk0 : k = 0 := by simpa [straightCFG] using hk
    subst hk0
    rw [hterm, bodyAt_straight, callFreePieces_of_isNone hcall]
    simp only [List.mem_singleton, forall_eq]

/-- **Completeness for straight-line bodies.** Two non-empty straight-line typed bodies whose
    shared runs agree (`Res`), with the further conditions of `ownedCheckMC_of_resW`, pass
    `ownedCheckMC`. -/
theorem ownedCheckMC_of_res (outs : List String) {B B' : List LinstrRM} (hne : B ≠ [])
    (hne' : B' ≠ []) (hs : ∀ p ∈ B, straightR p.1 = true)
    (hs' : ∀ p ∈ B', straightR p.1 = true)
    (hres : Res (tRun B SSt.start Tbl.empty).1 (tRun B SSt.start Tbl.empty).2
      (tRun B' SSt.start (tRun B SSt.start Tbl.empty).1))
    (hunk : (tRun B SSt.start Tbl.empty).2 ≠ .unk) (hout : outs ≠ [])
    (hcall : ∀ p ∈ B, (LprogIsa.shadowCall? p.1).isNone = true)
    (hstep : symRun B SSt.start ≠ .fail)
    (hobl : ∀ o ∈ symObl B' SSt.start,
      o ∈ symObl B SSt.start ∧ o.1.vars = [] ∧ o.1.readsF = false) :
    ownedCheckMC outs B B' = true :=
  ownedCheckMC_of_resW outs hne hne' hs hs' (ResW_of_Res hres) hunk hout hcall hstep hobl

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
