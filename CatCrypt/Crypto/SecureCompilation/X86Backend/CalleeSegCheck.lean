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
* `shadowAt`: the destination, symbol and operands of the shadow instruction at a position.
* `segOutsAt`: the names two end states of segments agree on, read from the shadow
  instruction of `ref` at the exit.
* `calleeSegB`: the checks of the segments.
* `segSimI_of_checks`, `segSim_of_checks`: the simulation of the cut programs.

## Main results

* `x86IsaK_lsemFuelMemF`: the runs of `x86IsaK` are the bounds-checked runs of `x86Isa`.
* `siteMap_some`, `siteMapL_index`, `procStep_congr`, `glue_congr`.
* `calleeSegB_soundK`: under the soundness of the validation by segments, a halting run of
  `x86IsaK.withProcs T` on `ref` is matched by a halting run on `img`. Each site carries its
  own destination, symbol and operands; the sites of `ref` and `img` agree in order.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable ProcSummary procCall? procStep
  retWord shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (goto)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs Rel symStep symDec
  symLaws_x86 symSubst_x86)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMCIn
  ownedCheckMCIn_sound_rel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall (x86IsaK x86IsaK_step
  fnStable_x86IsaK)

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

/-- **`siteMapL` pairs positions at a common index.** -/
theorem siteMapL_index : ∀ {ps qs : List Nat} {x q : Nat}, siteMapL ps qs x = some q →
    ∃ k : Nat, ps[k]? = some x ∧ qs[k]? = some q
  | [], _, _, _, h => by simp [siteMapL] at h
  | _ :: _, [], _, _, h => by simp [siteMapL] at h
  | p :: ps, q' :: qs, x, q, h => by
      unfold siteMapL at h
      split at h
      · rename_i hx
        cases h
        exact ⟨0, by simp [hx], rfl⟩
      · obtain ⟨k, hk, hk'⟩ := siteMapL_index h
        exact ⟨k + 1, hk, hk'⟩

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

/-- The destination, the symbol and the operands of the shadow instruction of a call at the
    position `p` of `B`, or `none` when `B` holds no such instruction at `p`. -/
def shadowAt (B : List LinstrRM) (p : Nat) : Option (String × String × List LOperand) :=
  B[p]?.bind (shadowCall? ·.fst)

/-- **Every shadow instruction of a call in `B` calls a symbol accepted by `ok`.** At one
    symbol `g` the predicate is `(· == g)`. -/
def callSymsB (ok : String → Bool) (B : List LinstrRM) : Bool :=
  B.all fun i => (shadowCall? i.fst).all fun q => ok q.2.1

/-- The register names of a list of operands. -/
def regsOf (srcs : List LOperand) : List String := srcs.filterMap LOperand.regName?

@[simp] theorem regsOf_map_reg (xs : List String) : regsOf (xs.map LOperand.reg) = xs := by
  simp [regsOf, List.filterMap_map, Function.comp_def, LOperand.regName?]

/-- **The step of the summary at a site of `B` is matched at a site of `B'`** whose shadow
    instruction equals that of `B`, from a state that agrees on the operands and on the
    arrays, when the operands are the registers `args`. The result `x` is a word when the
    summary has no word-array result. -/
theorem glue_congr {T : ProcTable} {fn : String} {B B' : List LinstrRM} {p q : Nat}
    {dst f : String} {args : List String}
    (hp : shadowAt B p = some (dst, f, args.map LOperand.reg))
    (hpq : shadowAt B' q = shadowAt B p) {u u' v : LstateMF}
    (hag : ∀ r ∈ args, u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r)
    (hla : u'.prog.base.larr = u.prog.base.larr)
    (hg : Glue T (singletonProgM fn B) p u v) :
    ∃ pr x, T f = some pr ∧ v = LprogIsa.retRes dst x u
      ∧ Glue T (singletonProgM fn B') q u' (LprogIsa.retRes dst x u')
      ∧ (pr.RetWord → ∃ w, x = .word w) := by
  obtain ⟨i, pr, dst1, srcs, hi, hpc, hstep⟩ := hg
  have hsi : shadowCall? i.fst = some (dst, f, args.map LOperand.reg) := by
    grind [shadowAt, singletonProgM]
  have hT : T f = some pr ∧ dst = dst1 ∧ args.map LOperand.reg = srcs := by
    simpa [procCall?, hsi] using hpc
  obtain ⟨hT, rfl, rfl⟩ := hT
  obtain ⟨x, rfl, hstep', hxw⟩ := procStep_congr hag hla hstep
  have hj : ∃ j, B'[q]? = some j ∧ shadowCall? j.fst = some (dst, f, args.map LOperand.reg) := by
    rw [hp] at hpq
    grind [shadowAt]
  obtain ⟨j, hj, hsj⟩ := hj
  exact ⟨pr, x, hT, rfl, ⟨j, pr, dst, _, hj, by simp [procCall?, hsj, hT], hstep'⟩, hxw⟩

/-! ## 3. The checks of the segments -/

/-- **A halting run of a cut program from the counter `0` is a `CutRun`.** -/
theorem cutRun_of_run {I : Isa} {fn : String} {C : List LinstrRM} {s t : LstateMF} {n : Nat}
    (h : I.lsemFuelMemF (singletonProgM fn C) n (goto s 0) = some t) : CutRun I fn C s t :=
  ⟨n, t.prog.base.lpc, fun j => I.lsemFuelMemF_add _ n j _ _ h⟩

/-- The observed agreement does not read the counter. -/
theorem obs_goto {outs : List String} {u t : LstateMF} {q : Nat} :
    Obs outs (goto u q) t ↔ Obs outs u t := Iff.rfl

/-- The names the end states of two segments of `ref` with the exit `x` agree on: `outs` at
    the end of the body, and at a shadow instruction of `ref` the register names of its
    operands and the names of `ins` at the entry after it other than its destination. -/
def segOutsAt (ref : List LinstrRM) (ins : Option Nat → List String) (outs : List String) :
    Option Nat → List String
  | none => outs
  | some p =>
      match shadowAt ref p with
      | some (dst, _, srcs) => regsOf srcs ++ (ins (some p)).filter (· != dst)
      | none => []

/-- **The checks of the segments of a calling body**: the shadow instructions at the sites
    of `ref` are, in order, those at the sites of `img`; the operands of every shadow
    instruction at a site of `ref` are registers; and for every entry `e` and every exit `x`
    of `ref`, `ownedCheckMCIn` accepts the cut program of `ref` against the cut program of
    `img` at the sites `siteMap T ref img`, at the function `fn` and the label `fin`, with
    the entry set `ins e` and the observed names `segOutsAt ref ins outs x`. -/
def calleeSegB (T : ProcTable) (fn : String) (fin : LLabel) (ins : Option Nat → List String)
    (outs : List String) (ref img : List LinstrRM) : Bool :=
  let es := none :: (sites T ref).map some
  (sites T ref).map (shadowAt ref) == (sites T img).map (shadowAt img)
    && (sites T ref).all (fun p =>
      (shadowAt ref p).all fun q => q.2.2 == (regsOf q.2.2).map LOperand.reg)
    && es.all fun e => es.all fun x =>
      ownedCheckMCIn (ins e) (segOutsAt ref ins outs x) (cutAt fn fin ref e x)
        (cutAt fn fin img (siteMap T ref img e) (siteMap T ref img x))

/-- **The simulation of the cut programs from the checks of the segments**, on an
    instruction set `I` whose runs are the bounds-checked runs of `x86Isa` and whose steps
    stay in the function. A state at the entry `e` is related to the states that agree with
    it on the function, the names `ins e`, the arrays and the word memory; the end states of
    two segments with the exit `x` are related when they agree on the function, the names
    `segOutsAt ref ins outs x`, the arrays and the word memory. At every site of `ref`, the
    summary of the symbol has no word-array result, or the destination is among the
    operands. -/
def segSimI_of_checks {I : Isa} (hK : I.lsemFuelMemF = x86Isa.lsemFuelMemFk true)
    (hS : FnStable I) {T : ProcTable}
    {fn : String} {fin : LLabel} {ins : Option Nat → List String} {outs : List String}
    {ref img : List LinstrRM}
    (hres : ∀ (p : Nat) (d f : String) (xs : List String) (pr : ProcSummary),
      shadowAt ref p = some (d, f, xs.map LOperand.reg) → T f = some pr → pr.RetWord ∨ d ∈ xs)
    (h : calleeSegB T fn fin ins outs ref img = true) :
    CutSimI I T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img) where
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
    intro p u u' v hQ hg
    simp only [calleeSegB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hmap, hregs⟩, -⟩ := h
    have hp : IsSite T ref (some p) := by
      obtain ⟨i, pr', dst, srcs, hi, hpq, -⟩ := hg
      exact ⟨i, hi, by simp only [isProcB, hpq, Option.isSome_some]⟩
    have hmem : p ∈ sites T ref := by simpa using mem_of_isSite hp
    have hl : (sites T ref).length = (sites T img).length := by
      simpa using congrArg List.length hmap
    obtain ⟨q, hq, hqs⟩ := siteMap_some hl hp
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
    have hsrcs : srcs = (regsOf srcs).map LOperand.reg := by
      simpa [hsh] using hregs p hmem
    have hsh' : shadowAt ref p = some (res, f, (regsOf srcs).map LOperand.reg) := by
      rw [hsh, ← hsrcs]
    have hseg : segOutsAt ref ins outs (some p)
        = regsOf srcs ++ (ins (some p)).filter (· != res) := by
      simp only [segOutsAt, hsh]
    obtain ⟨hobs, hfn⟩ := hQ
    rw [hseg] at hobs
    obtain ⟨pr, x, hT, rfl, hg', hxw⟩ := glue_congr hsh' hpq
      (fun r hr => hobs.1 r (List.mem_append_left _ hr)) hobs.2.1 hg
    have hres := hres p res f (regsOf srcs) pr hsh' hT
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
      have hmem : res ∈ regsOf srcs := by
        rcases hres with hrw | hm
        · obtain ⟨w, hw⟩ := hxw hrw
          cases hw
        · exact hm
      refine ⟨q, LprogIsa.retArr res a u', hq, hg', hfn, ?_, hobs.2.2, fun r hr => ?_,
        fun h => by cases h⟩
      · change (u'.prog.base.setArr res a).larr = (u.prog.base.setArr res a).larr
        unfold LstateM.setArr
        rw [hobs.2.1]
      · change u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r
        by_cases hrr : r = res
        · subst hrr
          exact hobs.1 r (List.mem_append_left _ hmem)
        · exact hoff r hr hrr

/-- **The simulation of the cut programs of a calling body by those of its image** on the
    bounds-checked x86 instruction set, from the checks of the segments, where at every site
    of `ref` the summary of the symbol has no word-array result or the destination is among
    the operands. -/
def segSim_of_checks {T : ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (hres : ∀ (p : Nat) (d f : String) (xs : List String) (pr : ProcSummary),
      shadowAt ref p = some (d, f, xs.map LOperand.reg) → T f = some pr → pr.RetWord ∨ d ∈ xs)
    (h : calleeSegB T fn fin ins outs ref img = true) :
    CutSimI x86IsaK T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img) :=
  segSimI_of_checks x86IsaK_lsemFuelMemF fnStable_x86IsaK hres h

/-- **Soundness of the checks of the segments.** Where at every site of `ref` the summary
    of the symbol has no word-array result or the destination is among the operands, under
    the soundness `CutCheckSoundI` of the validation by segments of the cut programs `cutAt`
    at the function `fn` and the label `fin`, every halting run of `x86IsaK.withProcs T` on
    `ref` from a state of `fn` at the counter `0` is matched by a halting run on `img` from
    the same state, the end states agreeing on the registers `outs`, the arrays and the word
    memory. -/
theorem calleeSegB_soundK {T : ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (h : calleeSegB T fn fin ins outs ref img = true)
    (hsound : CutCheckSoundI x86IsaK T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img))
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0) (fuel : Nat)
    (hrun : (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn ref) fuel s = some t)
    (hres : ∀ (p : Nat) (d f : String) (xs : List String) (pr : ProcSummary),
      shadowAt ref p = some (d, f, xs.map LOperand.reg) → T f = some pr → pr.RetWord ∨ d ∈ xs) :
    ∃ fuel' t', (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn img) fuel' s = some t'
      ∧ Obs outs t t' :=
  hsound (segSim_of_checks hres h) s t hfn hpc fuel hrun

end CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck
