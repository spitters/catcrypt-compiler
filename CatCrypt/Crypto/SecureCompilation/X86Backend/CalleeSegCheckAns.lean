/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCutAns

/-!
# The checks of the segments of a calling body, at the answers of the callees

`CalleeSegCheck.segSimI_of_checks` builds, from the checks `calleeSegB` of the segments of a
calling body `ref` against its image `img`, a simulation `CutSimI` whose steps at the calls are
the steps of the summaries. This module builds from the same checks the simulation
`LprogCallCutAns.CutSimIA` at the steps `GlueA` after a call at an arbitrary word answer: a
step at the answer `w` at a site of `ref` is matched by the step at the same answer at the
corresponding site of `img`. The relations at the entries and exits are those of
`segSimI_of_checks`; no condition on the summaries enters, since the answer is not computed
from the operands.

## Main results

* `glue_congrA`: the step at an answer at a site of `B` is matched at a site of `B'` with the
  same shadow instruction, from every state.
* `segSimA_of_checksI`, `segSimA_of_checks`: the simulation of the cut programs at the steps
  at an answer, on an instruction set whose runs are the bounds-checked runs of `x86Isa` and
  on `CheckedIsaCall.x86IsaK`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheckAns

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable procCall? retWord
  shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCutAns (GlueA CutSimIA)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (goto)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs Rel symLaws_x86
  symSubst_x86)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMCIn_sound_rel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall (x86IsaK fnStable_x86IsaK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck

/-- **The step at an answer at a site of `B` is matched at a site of `B'`** whose shadow
    instruction equals that of `B`: the state after the step at the word `w` is `u` with `w`
    in the destination, and from every state `u'` the step at `w` at the site of `B'` leads
    to `u'` with `w` in the destination. -/
theorem glue_congrA {T : ProcTable} {fn : String} {B B' : List LinstrRM} {p q : Nat}
    {dst f : String} {srcs : List LOperand}
    (hp : shadowAt B p = some (dst, f, srcs)) (hpq : shadowAt B' q = shadowAt B p)
    {u u' v : LstateMF} {w : BitVec 64} (hg : GlueA T (singletonProgM fn B) p u w v) :
    v = retWord dst w u ∧ GlueA T (singletonProgM fn B') q u' w (retWord dst w u') := by
  obtain ⟨i, pr, dst1, srcs1, hi, hpc, rfl⟩ := hg
  have hsi : shadowCall? i.fst = some (dst, f, srcs) := by
    grind [shadowAt, singletonProgM]
  have hT : T f = some pr ∧ dst = dst1 ∧ srcs = srcs1 := by
    simpa [procCall?, hsi] using hpc
  obtain ⟨hT, rfl, rfl⟩ := hT
  have hj : ∃ j, B'[q]? = some j ∧ shadowCall? j.fst = some (dst, f, srcs) := by
    rw [hp] at hpq
    grind [shadowAt]
  obtain ⟨j, hj, hsj⟩ := hj
  exact ⟨rfl, j, pr, dst, srcs, hj, by simp [procCall?, hsj, hT], rfl⟩

/-- **The simulation of the cut programs at the steps at an answer, from the checks of the
    segments**, on an instruction set `I` whose runs are the bounds-checked runs of `x86Isa`
    and whose steps stay in the function. The relations at the entries and the exits are
    those of `segSimI_of_checks`; a step at the word `w` at a site of `ref` is matched by the
    step at `w` at the corresponding site of `img`. -/
def segSimA_of_checksI {I : Isa} (hK : I.lsemFuelMemF = x86Isa.lsemFuelMemFk true)
    (hS : FnStable I) {T : ProcTable}
    {fn : String} {fin : LLabel} {ins : Option Nat → List String} {outs : List String}
    {ref img : List LinstrRM}
    (h : calleeSegB T fn fin ins outs ref img = true) :
    CutSimIA I T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img)
      (GlueA T (singletonProgM fn ref)) (GlueA T (singletonProgM fn img)) where
  site := siteMap T ref img
  R e s s' := Rel (ins e, false) s s'
  Q x u u' := Obs (segOutsAt ref ins outs x) u u' ∧ u'.prog.lfn = u.prog.lfn
  site_none := rfl
  init _ := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun h => by cases h⟩
  seg := by
    intro e x s s' u he hx hfn' hR hrun
    simp only [calleeSegB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    have hchk := h.2 e (mem_of_isSite he) x (mem_of_isSite hx)
    obtain ⟨k, q, hk⟩ := hrun
    have hfn : s.prog.lfn = fn := hR.1.symm.trans hfn'
    have h0 := hk 0
    rw [hK] at h0
    obtain ⟨f', t', hr', hobs⟩ := ownedCheckMCIn_sound_rel symLaws_x86 symSubst_x86 hchk fn
      (goto s 0) (goto s' 0) (goto u q) hfn rfl rfl hR (k + 0) h0
    rw [← hK] at hr'
    refine ⟨t', cutRun_of_run hr', obs_goto.mp hobs, ?_⟩
    have e1 := hS.lsemFuelMemF_lfn _ _ _ _ hr'
    have e2 := hS.lsemFuelMemF_lfn _ _ _ _ (hk 0)
    exact e1.trans (hfn'.trans (hfn.symm.trans e2.symm))
  fin _ _ hQ := hQ.1
  glue := by
    intro p u u' w v hQ hg
    simp only [calleeSegB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hmap, -⟩, -⟩ := h
    have hp : IsSite T ref (some p) := by
      obtain ⟨i, pr', dst, srcs, hi, hpq, -⟩ := hg
      exact ⟨i, hi, by simp only [isProcB, hpq, Option.isSome_some]⟩
    have hl : (sites T ref).length = (sites T img).length := by
      simpa using congrArg List.length hmap
    obtain ⟨q, hq, -⟩ := siteMap_some hl hp
    have hpq : shadowAt img q = shadowAt ref p := by
      obtain ⟨k, hk, hk'⟩ := siteMapL_index hq
      have e := congrArg (·[k]?) hmap
      simpa [hk, hk'] using e.symm
    have hsh : ∃ d f srcs, shadowAt ref p = some (d, f, srcs) := by
      obtain ⟨i, pr', dst, srcs, hi, hpc, -⟩ := hg
      change ref[p]? = some i at hi
      unfold procCall? at hpc
      cases hs : shadowCall? i.fst with
      | none => simp [hs] at hpc
      | some r => exact ⟨r.1, r.2.1, r.2.2, by simp [shadowAt, hi, hs]⟩
    obtain ⟨res, f, srcs, hsh⟩ := hsh
    have hseg : segOutsAt ref ins outs (some p)
        = regsOf srcs ++ (ins (some p)).filter (· != res) := by
      simp only [segOutsAt, hsh]
    obtain ⟨hobs, hfn⟩ := hQ
    rw [hseg] at hobs
    obtain ⟨rfl, hg'⟩ := glue_congrA (u' := u') hsh hpq hg
    have hoff : ∀ r ∈ ins (some p), r ≠ res →
        u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r := fun r hr hrr =>
      hobs.1 r (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, by simpa using hrr⟩))
    refine ⟨q, retWord res w u', hq, hg', hfn, hobs.2.1, hobs.2.2, fun r hr => ?_,
      fun h => by cases h⟩
    by_cases hrr : r = res
    · subst hrr
      simp [retWord]
    · have e : ∀ z : LstateMF, (retWord res w z).prog.base.reg.lvm r = z.prog.base.reg.lvm r :=
        fun z => by simp [retWord, hrr]
      rw [e, e]
      exact hoff r hr hrr

/-- **The simulation of the cut programs of a calling body by those of its image at the
    steps at an answer**, on the bounds-checked x86 instruction set, from the checks of the
    segments. -/
def segSimA_of_checks {T : ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (h : calleeSegB T fn fin ins outs ref img = true) :
    CutSimIA x86IsaK T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img)
      (GlueA T (singletonProgM fn ref)) (GlueA T (singletonProgM fn img)) :=
  segSimA_of_checksI x86IsaK_lsemFuelMemF fnStable_x86IsaK h

end CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheckAns
