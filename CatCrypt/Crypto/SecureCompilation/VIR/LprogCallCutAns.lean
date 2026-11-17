/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut

/-!
# The cut of a body at its calls, at the answers of the callees

`LprogCallCut.Glue` joins two segments of a body by the step `procStep` of the summary of the
callee, so the state after a call carries the value of the summary. This module states the
step after a call at an answer: `GlueA` writes an arbitrary word `w` to the destination of the
shadow instruction. The chains of segments and of runs of cut programs are stated over an
arbitrary step relation with answers (`RunChainA`, `CutChainA`), indexed by the list of the
answers in order; `GlueLaws` collects the facts about a step relation that the chains use.

The summary step is an instance: at a site whose summary has no word-array result, `Glue` is
`GlueA` at the word the summary returns (`glue_iff_glueA`), and `RunChain` and `CutChain` are
the chains at the step relation `glueU` with the trivial answer (`runChain_iff_runChainA`,
`cutChain_iff_cutChainA`).

## Main definitions

* `GlueA`: the step after a call at the answer `w`.
* `SumAns`: the summary of the callee returns the word `w` at the operands.
* `glueU`: the summary step as a step relation with the trivial answer.
* `GlueLaws`: a step relation with answers is at a site, keeps the function and does not read
  the counter.
* `RunChainA`, `CutChainA`: chains of segments and of runs of cut programs joined by a step
  relation with answers.
* `CutSimIA`: a simulation of the cut programs of one body by those of another, joined by a
  step relation with answers on each body, the answers equal on both sides.
* `CutSimI.toA`, `CutSimIA.toI`: `CutSimI` is `CutSimIA` at the summary steps.

## Main results

* `GlueA.atPc_succ`, `GlueA.goto`, `glueLaws_glueA`, `glueLaws_glueU`.
* `glue_iff_glueA`: the summary step is `GlueA` at the answer of the summary.
* `runChain_iff_runChainA`, `cutChain_iff_cutChainA`: the chains of `LprogCallCut` are the
  chains at `glueU`.
* `runChainA_of_cutChainA`: under `CutSimIA`, a chain of runs of cut programs of one body is
  a chain of segments of the other at the same answers, the end states agreeing on the
  observed registers, the arrays and the word memory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCutAns

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)

/-! ## 1. The step after a call at an answer -/

/-- **The step after a call at the answer `w`** at the position `p` of `P`: the instruction
    at `p` is a shadow instruction of a call of a symbol of `T`, and `v` is `u` with the word
    `w` in its destination and the counter advanced. -/
def GlueA (T : ProcTable) (P : LprogM) (p : Nat) (u : LstateMF) (w : BitVec 64)
    (v : LstateMF) : Prop :=
  ∃ i pr dst srcs, P.body[p]? = some i ∧ procCall? T i.fst = some (pr, dst, srcs) ∧
    v = retWord dst w u

/-- The state after the step at an answer is at the position after `p`. -/
theorem GlueA.atPc_succ {T : ProcTable} {P : LprogM} {p : Nat} {u v : LstateMF}
    {w : BitVec 64} (hu : atPc P p u) (hg : GlueA T P p u w v) : atPc P (p + 1) v := by
  obtain ⟨i, pr, dst, srcs, -, -, rfl⟩ := hg
  exact ⟨(lfn_retRes dst (.word w) u).trans hu.1, by rw [← retRes_word, lpc_retRes, hu.2]⟩

/-- The step at an answer does not read the counter. -/
theorem GlueA.goto {T : ProcTable} {P : LprogM} {p : Nat} {u v : LstateMF} {w : BitVec 64}
    (hg : GlueA T P p u w v) (k : Nat) : GlueA T P p (goto u k) w (goto v (k + 1)) := by
  obtain ⟨i, pr, dst, srcs, hi, hq, rfl⟩ := hg
  exact ⟨i, pr, dst, srcs, hi, hq, rfl⟩

/-- **The summary returns the word `w`** at the shadow instruction at `p` of `P`, read on the
    state `u`. -/
def SumAns (T : ProcTable) (P : LprogM) (p : Nat) (u : LstateMF) (w : BitVec 64) : Prop :=
  ∃ i pr dst srcs vs, P.body[p]? = some i ∧ procCall? T i.fst = some (pr, dst, srcs) ∧
    srcs.length = pr.arity ∧ argsRead pr.arrArgs u.prog.base 0 srcs = some vs ∧
    pr.result vs = some (.word w)

/-- **The summary step is the step at the answer of the summary.** At a position whose
    summary has no word-array result, `Glue` from `u` to `v` holds exactly when `GlueA` holds
    at a word that the summary returns on `u`. -/
theorem glue_iff_glueA {T : ProcTable} {P : LprogM} {p : Nat} {u v : LstateMF}
    (hw : ∀ i pr dst srcs, P.body[p]? = some i → procCall? T i.fst = some (pr, dst, srcs) →
      pr.RetWord) :
    Glue T P p u v ↔ ∃ w, GlueA T P p u w v ∧ SumAns T P p u w := by
  constructor
  · rintro ⟨i, pr, dst, srcs, hi, hq, hstep⟩
    unfold procStep at hstep
    split at hstep
    · rename_i hlen
      obtain ⟨vs, hvs, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hstep
      have hx' := hx
      rw [ProcSummary.result_of_retWord (hw i pr dst srcs hi hq)] at hx'
      obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp hx'
      exact ⟨w, ⟨i, pr, dst, srcs, hi, hq, rfl⟩,
        i, pr, dst, srcs, vs, hi, hq, hlen, hvs, hx⟩
    · cases hstep
  · rintro ⟨w, ⟨i, pr, dst, srcs, hi, hq, rfl⟩, i', pr', dst', srcs', vs, hi', hq', hlen,
      hvs, hx⟩
    rw [hi] at hi'
    cases hi'
    rw [hq] at hq'
    cases hq'
    refine ⟨i, pr, dst, srcs, hi, hq, ?_⟩
    unfold procStep
    rw [ite_eq_left hlen, hvs]
    simp [hx]

/-- **The summary step as a step relation with the trivial answer.** -/
def glueU (T : ProcTable) (P : LprogM) (p : Nat) (u : LstateMF) (_ : Unit) (v : LstateMF) :
    Prop :=
  Glue T P p u v

/-! ## 2. The laws of a step relation with answers -/

/-- **The laws of a step relation with answers** on the body `B`: a step is at a shadow
    instruction of a call of a symbol of `T`, keeps the function and does not read the
    counter. -/
structure GlueLaws (T : ProcTable) (B : List LinstrRM) {α : Type}
    (G : Nat → LstateMF → α → LstateMF → Prop) : Prop where
  site : ∀ p u a v, G p u a v → IsSite T B (some p)
  lfn : ∀ p u a v, G p u a v → v.prog.lfn = u.prog.lfn
  goto : ∀ p u a v, G p u a v → ∀ k, G p (goto u k) a (goto v (k + 1))

/-- The step at an answer meets the laws. -/
theorem glueLaws_glueA (T : ProcTable) (fn : String) (B : List LinstrRM) :
    GlueLaws T B (GlueA T (singletonProgM fn B)) where
  site _ _ _ _ hg := by
    obtain ⟨i, pr, dst, srcs, hi, hq, -⟩ := hg
    exact ⟨i, hi, by simp only [isProcB, hq, Option.isSome_some]⟩
  lfn _ u w _ hg := by
    obtain ⟨i, pr, dst, srcs, -, -, rfl⟩ := hg
    exact lfn_retRes dst (.word w) u
  goto _ _ _ _ hg k := hg.goto k

/-- The summary step meets the laws. -/
theorem glueLaws_glueU (T : ProcTable) (fn : String) (B : List LinstrRM) :
    GlueLaws T B (glueU T (singletonProgM fn B)) where
  site _ _ _ _ hg := by
    obtain ⟨i, pr, dst, srcs, hi, hq, -⟩ := hg
    exact ⟨i, hi, by simp only [isProcB, hq, Option.isSome_some]⟩
  lfn _ u _ _ hg := by
    obtain ⟨i, pr, dst, srcs, -, -, hstep⟩ := hg
    unfold procStep at hstep
    split at hstep
    · obtain ⟨vs, -, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp hstep
      exact lfn_retRes dst x u
    · cases hstep
  goto _ _ _ _ hg k := Glue.goto hg k

/-! ## 3. Chains joined by a step relation with answers -/

/-- **A chain of segments** of `P` on `I` from `s` to `t` joined by the step relation `G`,
    with the answers `as` of its steps in order: a segment to a halted state `t`, or a segment
    to a shadow instruction, a step of `G` at an answer, and a chain from the state after
    it. -/
inductive RunChainA (I : Isa) (T : ProcTable) (P : LprogM) {α : Type}
    (G : Nat → LstateMF → α → LstateMF → Prop) : LstateMF → List α → LstateMF → Prop
  | done {s t : LstateMF} : SegTo I T P s none t → RunChainA I T P G s [] t
  | call {s u v t : LstateMF} {a : α} {as : List α} (p : Nat) : SegTo I T P s (some p) u →
      G p u a v → RunChainA I T P G v as t → RunChainA I T P G s (a :: as) t

/-- **A chain of halting runs of cut programs** of the body `B` on `I`, from the state `s` at
    the entry `e` to the state `t`, joined by the step relation `G`, with the answers `as` of
    its steps in order. -/
inductive CutChainA (I : Isa) (T : ProcTable) (fn : String) (B : List LinstrRM)
    (cut : Option Nat → Option Nat → List LinstrRM) {α : Type}
    (G : Nat → LstateMF → α → LstateMF → Prop) :
    Option Nat → LstateMF → List α → LstateMF → Prop
  | done {e : Option Nat} {s t : LstateMF} : CutRun I fn (cut e none) s t →
      Halted (singletonProgM fn B) t → CutChainA I T fn B cut G e s [] t
  | call {e : Option Nat} {s u v t : LstateMF} {a : α} {as : List α} (p : Nat) :
      CutRun I fn (cut e (some p)) s u → atPc (singletonProgM fn B) p u →
      G p u a v → CutChainA I T fn B cut G (some p) v as t →
      CutChainA I T fn B cut G e s (a :: as) t

/-- **`RunChain` is the chain at the summary step.** -/
theorem runChain_iff_runChainA {I : Isa} {T : ProcTable} {P : LprogM} {s t : LstateMF} :
    RunChain I T P s t ↔ ∃ as, RunChainA I T P (glueU T P) s as t := by
  constructor
  · intro h
    induction h with
    | done hs => exact ⟨[], .done hs⟩
    | call p hs hg _ ih =>
        obtain ⟨as, ih⟩ := ih
        exact ⟨() :: as, .call p hs hg ih⟩
  · rintro ⟨as, h⟩
    induction h with
    | done hs => exact .done hs
    | call p hs hg _ ih => exact .call p hs hg ih

/-- **`CutChain` is the chain of cut programs at the summary step.** -/
theorem cutChain_iff_cutChainA {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {cut : Option Nat → Option Nat → List LinstrRM} {e : Option Nat} {s t : LstateMF} :
    CutChain I T fn B cut e s t ↔
      ∃ as, CutChainA I T fn B cut (glueU T (singletonProgM fn B)) e s as t := by
  constructor
  · intro h
    induction h with
    | done hr hh => exact ⟨[], .done hr hh⟩
    | call p hr hat hg _ ih =>
        obtain ⟨as, ih⟩ := ih
        exact ⟨() :: as, .call p hr hat hg ih⟩
  · rintro ⟨as, h⟩
    induction h with
    | done hr hh => exact .done hr hh
    | call p hr hat hg _ ih => exact .call p hr hat hg ih

/-! ## 4. The simulation of cut programs at a step relation with answers -/

/-- **A simulation of the cut programs of `B` by the cut programs of `B'` on `I`, joined by
    the step relations `G` on `B` and `G'` on `B'`.** The fields `site`, `R`, `Q`, `site_none`,
    `init`, `seg` and `fin` are those of `CutSimI`; from states related by `Q` at a shadow
    instruction, a step of `G` at the answer `a` is matched by a step of `G'` at the same
    answer, at the corresponding site, to states related by `R`. -/
structure CutSimIA (I : Isa) (T : ProcTable) (outs : List String) (fn : String)
    (B B' : List LinstrRM) (cut cut' : Option Nat → Option Nat → List LinstrRM) {α : Type}
    (G G' : Nat → LstateMF → α → LstateMF → Prop) : Type where
  site : Option Nat → Option Nat
  R : Option Nat → LstateMF → LstateMF → Prop
  Q : Option Nat → LstateMF → LstateMF → Prop
  site_none : site none = none
  init : ∀ s, R none s s
  seg : ∀ e x s s' u, IsSite T B e → IsSite T B x → s'.prog.lfn = fn → R e s s' →
    CutRun I fn (cut e x) s u →
    ∃ u', CutRun I fn (cut' (site e) (site x)) s' u' ∧ Q x u u'
  fin : ∀ t t', Q none t t' → Obs outs t t'
  glue : ∀ p u u' a v, Q (some p) u u' → G p u a v →
    ∃ q v', site (some p) = some q ∧ G' q u' a v' ∧ R (some p) v v'

/-- **`CutSimI` is the simulation at the summary steps.** -/
def CutSimI.toA {I : Isa} {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    (sim : CutSimI I T outs fn B B' cut cut') :
    CutSimIA I T outs fn B B' cut cut' (glueU T (singletonProgM fn B))
      (glueU T (singletonProgM fn B')) where
  site := sim.site
  R := sim.R
  Q := sim.Q
  site_none := sim.site_none
  init := sim.init
  seg := sim.seg
  fin := sim.fin
  glue p u u' _ v hQ hg := sim.glue p u u' v hQ hg

/-- **A simulation at the summary steps is a `CutSimI`.** -/
def CutSimIA.toI {I : Isa} {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    (sim : CutSimIA I T outs fn B B' cut cut' (glueU T (singletonProgM fn B))
      (glueU T (singletonProgM fn B'))) :
    CutSimI I T outs fn B B' cut cut' where
  site := sim.site
  R := sim.R
  Q := sim.Q
  site_none := sim.site_none
  init := sim.init
  seg := sim.seg
  fin := sim.fin
  glue p u u' v hQ hg := sim.glue p u u' () v hQ hg

/-- **A chain of halting runs of cut programs of `B` joined by `G` is, under a simulation
    `CutSimIA`, a chain of segments of `B'` joined by `G'` at the same answers.** The branch
    condition of `I` does not read the counter, `I` refuses the procedures of `T`, the steps
    of `I` stay in the function, the cut programs of `B'` are cuts that halt only at their
    exits, and `G` and `G'` meet `GlueLaws`. From a state of `fn` related by `R e` to the
    start of the chain, for an entry `e` of `B`, the chain of segments of `B'` starts at the
    entry position of `site e` and ends in a state that agrees with the end of the chain on
    the registers `outs`, the arrays and the word memory. -/
theorem runChainA_of_cutChainA {I : Isa} {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    {pos' : Option Nat → Option Nat → Nat → Nat} {α : Type}
    {G G' : Nat → LstateMF → α → LstateMF → Prop} (hI : PcFree I) (hR : I.RefusesProcs T)
    (hS : FnStable I)
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x))
    (hG : GlueLaws T B G) (hG' : GlueLaws T B' G')
    (sim : CutSimIA I T outs fn B B' cut cut' G G') {e : Option Nat} {s t : LstateMF}
    {as : List α} (h : CutChainA I T fn B cut G e s as t) :
    ∀ (s' : LstateMF), sim.R e s s' → s'.prog.lfn = fn → IsSite T B e →
      IsSite T B' (sim.site e) →
      ∃ t', RunChainA I T (singletonProgM fn B') G'
        (goto s' (entryPos (sim.site e))) as t' ∧ Obs outs t t' := by
  have hle : ∀ e, IsSite T B' e → entryPos e ≤ B'.length := by
    intro e he
    cases e with
    | none => exact Nat.zero_le _
    | some p =>
        obtain ⟨i, hi, -⟩ := he
        exact (List.getElem?_eq_some_iff.mp hi).1
  induction h with
  | @done e s t hrun _ =>
      intro s' hRs hfn hB he
      obtain ⟨u', hrun', hQ⟩ := sim.seg e none s s' t hB trivial hfn hRs hrun
      rw [sim.site_none] at hrun'
      obtain ⟨hc, hv⟩ := hcut' (sim.site e) none he trivial
      obtain ⟨q, hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
      have ho : Obs outs t u' := sim.fin _ _ hQ
      exact ⟨_, .done hseg, ho.1, ho.2.1, ho.2.2⟩
  | @call e s u v t a as p hrun _ hglue _ ih =>
      intro s' hRs hfn hB he
      have hp : IsSite T B (some p) := hG.site _ _ _ _ hglue
      obtain ⟨u', hrun', hQ⟩ := sim.seg e (some p) s s' u hB hp hfn hRs hrun
      obtain ⟨q, v', hsite, hglue', hR'⟩ := sim.glue p u u' a v hQ hglue
      have hq : IsSite T B' (some q) := hG'.site _ _ _ _ hglue'
      rw [hsite] at hrun'
      obtain ⟨hc, hv⟩ := hcut' (sim.site e) (some q) he hq
      obtain ⟨q', hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
      have hat : atPc (singletonProgM fn B') q (goto u' q') := by
        obtain ⟨_, _, hat, _⟩ := hseg
        exact hat
      have hqq : q' = q := hat.2
      subst hqq
      have hg := hG'.goto _ _ _ _ hglue' q'
      have hfn' : v'.prog.lfn = fn := (hG'.lfn _ _ _ _ hglue').trans hat.1
      obtain ⟨t', hch, hobs⟩ := ih v' hR' hfn' hp (by rw [hsite]; exact hq)
      rw [hsite] at hch
      exact ⟨t', .call q' hseg hg hch, hobs⟩

end CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCutAns
