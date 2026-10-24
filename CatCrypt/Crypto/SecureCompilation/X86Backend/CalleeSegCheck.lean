/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall

@[expose] public section

set_option autoImplicit false

/-!
# The checks of the segments of a calling body

A calling body `ref` and its image `img` are cut at their shadow instructions of calls into
cut programs (`LprogCallCut.cutAt`), one for every entry and every exit. The check
`calleeSegB` validates every cut program of `img` against the cut program of `ref` with the
same entry and exit by the register allocation checker with an entry set
(`OwnedLprogTVChecked.ownedCheckMCIn`). The sites of `img` correspond to those of `ref` in
order (`siteMap`). From these checks, `segSim_of_checks` builds the simulation
`LprogCallCut.CutSimI` of the cut programs of `ref` by those of `img` on the bounds-checked
x86 instruction set `CheckedIsaCall.x86IsaK`: states at an entry are related when they agree
on the entry set of that entry, end states of segments when they agree on the names read
after the exit, and the step of the summary of the callee at a site of `ref` is matched at
the corresponding site of `img`.

## Main definitions

* `siteMap`: the `k`-th site of one body to the `k`-th site of another.
* `segOuts`: the names two end states of segments agree on.
* `calleeSegB`: the checks of the segments.
* `segSimI_of_checks`, `segSim_of_checks`: the simulation of the cut programs.

## Main results

* `x86IsaK_lsemFuelMemF`: the runs of `x86IsaK` are the bounds-checked runs of `x86Isa`.
* `siteMap_some`, `procStep_congr`, `glue_congr`.
* `calleeSegB_soundK`: under the soundness of the validation by segments, a halting run of
  `x86IsaK.withProcs T` on `ref` is matched by a halting run on `img`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable ProcSummary procCall? procStep
  retWord)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (goto)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs Rel symStep symDec
  symLaws_x86 symSubst_x86)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMCIn
  ownedCheckMCIn_sound_rel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall (x86IsaK x86IsaK_step
  fnStable_x86IsaK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (siteShapeB
  sitesOf_of_siteShapeB)

/-- **The runs of the bounds-checked x86 instruction set are the bounds-checked runs of
    `x86Isa`.** -/
theorem x86IsaK_lsemFuelMemF : x86IsaK.lsemFuelMemF = x86Isa.lsemFuelMemFk true := by
  funext P fuel
  induction fuel with
  | zero => funext s; rfl
  | succ n ih =>
      funext s
      simp only [Isa.lsemFuelMemF, Isa.lsemFuelMemFk, ih, Isa.evalInstrPMemFk_true, x86IsaK_step,
        JasminLsemMemChecked.evalInstrPMemFk_true, x86Isa_step]

/-! ## 1. The sites of the image -/

/-- The position of `qs` at the index of `x` in `ps`, or `none` when `x` is not in `ps`. -/
def siteMapL : List Nat → List Nat → Nat → Option Nat
  | p :: ps, q :: qs, x => if x = p then some q else siteMapL ps qs x
  | _, _, _ => none

theorem siteMapL_mem : ∀ {ps qs : List Nat} {x q : Nat}, siteMapL ps qs x = some q → q ∈ qs
  | [], _, _, _, h => by simp [siteMapL] at h
  | _ :: _, [], _, _, h => by simp [siteMapL] at h
  | p :: ps, q' :: qs, x, q, h => by
      unfold siteMapL at h
      split at h
      · cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (siteMapL_mem h)

theorem siteMapL_some : ∀ {ps qs : List Nat} {x : Nat}, x ∈ ps → ps.length = qs.length →
    ∃ q, siteMapL ps qs x = some q
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | _ :: _, [], _, _, hl => by simp at hl
  | p :: ps, q :: qs, x, h, hl => by
      unfold siteMapL
      split
      · exact ⟨q, rfl⟩
      · rename_i hx
        exact siteMapL_some ((List.mem_cons.mp h).resolve_left hx) (by simpa using hl)

/-- **The site map of two bodies**: the entry `none` to `none`, and the position of the
    `k`-th shadow instruction of a call of a symbol of `T` in `B` to the position of the
    `k`-th one in `B'`. -/
def siteMap (T : ProcTable) (B B' : List LinstrRM) : Option Nat → Option Nat
  | none => none
  | some p => siteMapL (sites T B) (sites T B') p

theorem isSite_of_mem_sites {T : ProcTable} {B : List LinstrRM} {p : Nat}
    (h : p ∈ sites T B) : IsSite T B (some p) := by
  simp only [sites, List.mem_filter, List.mem_range] at h
  obtain ⟨-, ha⟩ := h
  cases hb : B[p]? with
  | none => rw [hb] at ha; cases ha
  | some i => rw [hb] at ha; exact ⟨i, hb, by simpa using ha⟩

/-- **A site of `B` is sent to a site of `B'`** when the two bodies have equally many
    sites. -/
theorem siteMap_some {T : ProcTable} {B B' : List LinstrRM}
    (hl : (sites T B).length = (sites T B').length) {p : Nat} (hp : IsSite T B (some p)) :
    ∃ q, siteMap T B B' (some p) = some q ∧ IsSite T B' (some q) := by
  have hm : p ∈ sites T B := by simpa using mem_of_isSite hp
  obtain ⟨q, hq⟩ := siteMapL_some hm hl
  exact ⟨q, hq, isSite_of_mem_sites (siteMapL_mem hq)⟩

/-! ## 2. The step of the summary on agreeing states -/

theorem mapM_reg_congr {R R' : LstateN} : ∀ {args : List String},
    (∀ r ∈ args, R'.lvm r = R.lvm r) →
    (args.map LOperand.reg).mapM (evalOperandN R' 64)
      = (args.map LOperand.reg).mapM (evalOperandN R 64)
  | [], _ => rfl
  | a :: as, h => by
      have hg : R'.getW a 64 = R.getW a 64 := by
        unfold LstateN.getW
        rw [h a List.mem_cons_self]
      simp only [List.map_cons, List.mapM_cons, evalOperandN, hg,
        mapM_reg_congr (fun r hr => h r (List.mem_cons_of_mem _ hr))]

/-- **The step of a summary on register operands at two states that agree on the operands
    and on the arrays** writes the same result `x`, a word when the summary has no word-array
    result. -/
theorem procStep_congr {pr : ProcSummary} {dst : String} {args : List String}
    {u u' v : LstateMF} (hag : ∀ r ∈ args, u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r)
    (hla : u'.prog.base.larr = u.prog.base.larr)
    (h : procStep pr dst (args.map LOperand.reg) u = some v) :
    ∃ x, v = LprogIsa.retRes dst x u ∧
      procStep pr dst (args.map LOperand.reg) u' = some (LprogIsa.retRes dst x u') ∧
      (pr.RetWord → ∃ w, x = .word w) := by
  unfold procStep at h ⊢
  split at h
  · rename_i hlen
    obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨x, rfl, ?_, fun hrw => ?_⟩
    · rw [ite_eq_left hlen, LprogIsa.argsRead_regs_congr pr.arrArgs hla 0 hag, hvs]
      simp [hx]
    · rw [LprogIsa.ProcSummary.result_of_retWord hrw] at hx
      obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact ⟨w, rfl⟩
  · cases h

/-- **The step of the summary at a site of `B` is matched at a site of `B'`** from a state
    that agrees on the operands, for bodies whose shadow instructions are calls of `pr` on
    the registers `args` with the destination `res`. The result `x` is a word when `pr` has
    no word-array result. -/
theorem glue_congr {T : ProcTable} {fn : String} {B B' : List LinstrRM} {pr : ProcSummary}
    {res : String} {args : List String}
    (hs : ∀ (p : Nat) (i : LinstrRM) (pr' : ProcSummary) (dst : String)
      (srcs : List LOperand), B[p]? = some i → procCall? T i.fst = some (pr', dst, srcs) →
      pr' = pr ∧ dst = res ∧ srcs = args.map LOperand.reg)
    (hs' : ∀ (p : Nat) (i : LinstrRM) (pr' : ProcSummary) (dst : String)
      (srcs : List LOperand), B'[p]? = some i → procCall? T i.fst = some (pr', dst, srcs) →
      pr' = pr ∧ dst = res ∧ srcs = args.map LOperand.reg)
    {p q : Nat} (hq : IsSite T B' (some q)) {u u' v : LstateMF}
    (hag : ∀ r ∈ args, u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r)
    (hla : u'.prog.base.larr = u.prog.base.larr)
    (hg : Glue T (singletonProgM fn B) p u v) :
    ∃ x, v = LprogIsa.retRes res x u
      ∧ Glue T (singletonProgM fn B') q u' (LprogIsa.retRes res x u')
      ∧ (pr.RetWord → ∃ w, x = .word w) := by
  obtain ⟨i, pr1, dst, srcs, hi, hpq, hstep⟩ := hg
  obtain ⟨rfl, rfl, rfl⟩ := hs p i pr1 dst srcs hi hpq
  obtain ⟨x, rfl, hstep', hxw⟩ := procStep_congr hag hla hstep
  obtain ⟨j, hj, hjp⟩ := hq
  simp only [isProcB] at hjp
  obtain ⟨⟨pr2, dst2, srcs2⟩, hq'⟩ := Option.isSome_iff_exists.mp hjp
  obtain ⟨rfl, rfl, rfl⟩ := hs' q j pr2 dst2 srcs2 hj hq'
  exact ⟨x, rfl, ⟨j, _, _, _, hj, hq', hstep'⟩, hxw⟩

/-! ## 3. The checks of the segments -/

/-- **A halting run of a cut program from the counter `0` is a `CutRun`.** -/
theorem cutRun_of_run {I : Isa} {fn : String} {C : List LinstrRM} {s t : LstateMF} {n : Nat}
    (h : I.lsemFuelMemF (singletonProgM fn C) n (goto s 0) = some t) : CutRun I fn C s t :=
  ⟨n, t.prog.base.lpc, fun j => I.lsemFuelMemF_add _ n j _ _ h⟩

/-- The observed agreement does not read the counter. -/
theorem obs_goto {outs : List String} {u t : LstateMF} {q : Nat} :
    Obs outs (goto u q) t ↔ Obs outs u t := Iff.rfl

/-- The names the end states of two segments with the exit `x` agree on: `outs` at the end
    of the body, and at a shadow instruction the operands `args` and the names of `ins` at
    the entry after it other than the destination `res`. -/
def segOuts (res : String) (args : List String) (ins : Option Nat → List String)
    (outs : List String) : Option Nat → List String
  | none => outs
  | some p => args ++ (ins (some p)).filter (· != res)

/-- **The checks of the segments of a calling body**: `ref` and `img` have equally many
    shadow instructions of calls of symbols of `T`, and for every entry `e` and every exit
    `x` of `ref`, `ownedCheckMCIn` accepts the cut program of `ref` against the cut program
    of `img` at the sites `siteMap T ref img`, at the function `fn` and the label `fin`, with
    the entry set `ins e` and the observed names `segOuts res args ins outs x`. -/
def calleeSegB (T : ProcTable) (res : String) (args : List String) (fn : String)
    (fin : LLabel) (ins : Option Nat → List String) (outs : List String)
    (ref img : List LinstrRM) : Bool :=
  let es := none :: (sites T ref).map some
  (sites T ref).length == (sites T img).length
    && es.all fun e => es.all fun x =>
      ownedCheckMCIn (ins e) (segOuts res args ins outs x) (cutAt fn fin ref e x)
        (cutAt fn fin img (siteMap T ref img e) (siteMap T ref img x))

/-- **The simulation of the cut programs from the checks of the segments**, on an
    instruction set `I` whose runs are the bounds-checked runs of `x86Isa` and whose steps
    stay in the function. A state at the entry `e` is related to the states that agree with
    it on the function, the names `ins e`, the arrays and the word memory; the end states of
    two segments with the exit `x` are related when they agree on the function, the names
    `segOuts res args ins outs x`, the arrays and the word memory. The summary `pr` has no
    word-array result, or the destination `res` is among the operands `args`. -/
def segSimI_of_checks {I : Isa} (hK : I.lsemFuelMemF = x86Isa.lsemFuelMemFk true)
    (hS : FnStable I) {T : ProcTable} {pr : ProcSummary} {res : String}
    {args : List String} (hres : pr.RetWord ∨ res ∈ args)
    {fn : String} {fin : LLabel} {ins : Option Nat → List String} {outs : List String}
    {ref img : List LinstrRM}
    (hsr : ∀ (p : Nat) (i : LinstrRM) (pr' : ProcSummary) (dst : String)
      (srcs : List LOperand), ref[p]? = some i → procCall? T i.fst = some (pr', dst, srcs) →
      pr' = pr ∧ dst = res ∧ srcs = args.map LOperand.reg)
    (hsi : ∀ (p : Nat) (i : LinstrRM) (pr' : ProcSummary) (dst : String)
      (srcs : List LOperand), img[p]? = some i → procCall? T i.fst = some (pr', dst, srcs) →
      pr' = pr ∧ dst = res ∧ srcs = args.map LOperand.reg)
    (h : calleeSegB T res args fn fin ins outs ref img = true) :
    CutSimI I T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img) where
  site := siteMap T ref img
  R e s s' := Rel (ins e, false) s s'
  Q x u u' := Obs (segOuts res args ins outs x) u u' ∧ u'.prog.lfn = u.prog.lfn
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
    intro p u u' v hQ hg
    simp only [calleeSegB, Bool.and_eq_true, beq_iff_eq] at h
    have hp : IsSite T ref (some p) := by
      obtain ⟨i, pr', dst, srcs, hi, hpq, -⟩ := hg
      exact ⟨i, hi, by simp only [isProcB, hpq, Option.isSome_some]⟩
    obtain ⟨q, hq, hqs⟩ := siteMap_some h.1 hp
    obtain ⟨hobs, hfn⟩ := hQ
    obtain ⟨x, rfl, hg', hxw⟩ := glue_congr hsr hsi hqs
      (fun r hr => hobs.1 r (List.mem_append_left _ hr)) hobs.2.1 hg
    have hoff : ∀ r ∈ ins (some p), r ≠ res →
        u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r := fun r hr hrr =>
      hobs.1 r (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, by simpa using hrr⟩))
    cases x with
    | word w =>
      refine ⟨q, retWord res w u', hq, hg', hfn, hobs.2.1, hobs.2.2, fun r hr => ?_,
        fun h => by cases h⟩
      by_cases hrr : r = res
      · subst hrr
        simp [retWord]
      · have e : ∀ z : LstateMF, (retWord res w z).prog.base.reg.lvm r = z.prog.base.reg.lvm r :=
          fun z => by simp [retWord, hrr]
        rw [LprogIsa.retRes_word, e, e]
        exact hoff r hr hrr
    | arr a =>
      have hmem : res ∈ args := by
        rcases hres with hrw | hm
        · obtain ⟨w, hw⟩ := hxw hrw
          cases hw
        · exact hm
      refine ⟨q, LprogIsa.retArr res a u', hq, hg', hfn, ?_, hobs.2.2, fun r hr => ?_,
        fun h => by cases h⟩
      · show (u'.prog.base.setArr res a).larr = (u.prog.base.setArr res a).larr
        unfold LstateM.setArr
        rw [hobs.2.1]
      · show u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r
        by_cases hrr : r = res
        · subst hrr
          exact hobs.1 r (List.mem_append_left _ hmem)
        · exact hoff r hr hrr

/-- **The simulation of the cut programs of a calling body by those of its image** on the
    bounds-checked x86 instruction set, from the checks of the segments, for bodies whose
    shadow instructions are calls of the symbol `f` of `T` on the registers `args` with the
    destination `res`, where the summary of `f` has no word-array result or `res` is among
    `args`. -/
def segSim_of_checks {T : ProcTable} {f res : String} {args : List String} {pr : ProcSummary}
    (hT : T f = some pr) (hres : pr.RetWord ∨ res ∈ args) {fn : String} {fin : LLabel}
    {ins : Option Nat → List String}
    {outs : List String} {ref img : List LinstrRM} (hsr : siteShapeB f res args ref = true)
    (hsi : siteShapeB f res args img = true)
    (h : calleeSegB T res args fn fin ins outs ref img = true) :
    CutSimI x86IsaK T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img) :=
  segSimI_of_checks x86IsaK_lsemFuelMemF fnStable_x86IsaK hres (sitesOf_of_siteShapeB hsr hT)
    (sitesOf_of_siteShapeB hsi hT) h

/-- **Soundness of the checks of the segments.** For bodies whose shadow instructions are
    calls of the symbol `f` of `T` on the registers `args` with the destination `res`, where
    the summary of `f` has no word-array result or `res` is among `args`, under the
    soundness `CutCheckSoundI` of the validation by segments of the cut programs `cutAt`
    at the function `fn` and the label `fin`, every halting run of `x86IsaK.withProcs T` on
    `ref` from a state of `fn` at the counter `0` is matched by a halting run on `img` from
    the same state, the end states agreeing on the registers `outs`, the arrays and the word
    memory. -/
theorem calleeSegB_soundK {T : ProcTable} {f res : String} {args : List String}
    {pr : ProcSummary} (hT : T f = some pr) {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (hsr : siteShapeB f res args ref = true) (hsi : siteShapeB f res args img = true)
    (h : calleeSegB T res args fn fin ins outs ref img = true)
    (hsound : CutCheckSoundI x86IsaK T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img))
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0) (fuel : Nat)
    (hrun : (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn ref) fuel s = some t)
    (hres : pr.RetWord ∨ res ∈ args := by exact Or.inl rfl) :
    ∃ fuel' t', (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn img) fuel' s = some t'
      ∧ Obs outs t t' :=
  hsound (segSim_of_checks hT hres hsr hsi h) s t hfn hpc fuel hrun

end CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck
