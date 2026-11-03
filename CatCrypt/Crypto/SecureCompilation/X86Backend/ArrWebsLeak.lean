/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak

@[expose] public section

set_option autoImplicit false

/-!
# The leakage of a body with array names split into webs

`ArrWebs.lsemFuelMemF_webs` matches a halting run of a body accepted by `webB` by a run of
the renamed body `webRen w ao body` on the flag machine. This module states the same
simulation for the traced flag machine `lsemFuelMemFLeak`.

The instruction at position `k` is renamed by its step renaming `stepRen w ao k i`, so the
events of a step of the renamed body are the events of the step of the body mapped by
`renEv (stepRen w ao k i)`, a map that depends on the position. The trace of the renamed run
is therefore the trace `GTr (webG w ao body)` computed along the run of the body, which maps
the events of each step by the renaming of its position. Two runs of the body from one
position with one trace take the same positions (`ImageLoopWLeak.gTr_eq`), so they have one
computed trace, and constant time of the body gives constant time of the renamed body.

## Main definitions

* `webLeakB`: every instruction passes `leakFixB` under its step renaming.
* `webG`: the events of a step at a position, mapped by the step renaming of that position.
* `WebStart`: the entry states `lsemFuelMemF_webs_entry` relates.
* `WebPub`: the public-equality relation of the renamed body.

## Main results

* `lsemFuelMemFLeak_webs`: a halting traced run of an accepted body is matched, with the
  same fuel, by a halting traced run of the renamed body whose trace is the trace computed
  by `webG` along the run of the body.
* `lsemFuelMemFLeak_webs_entry`: the same run from position `0`.
* `memFCT_webs`: constant time of the body at `pubEq` gives constant time of the renamed
  body at `WebPub fn body L pubEq`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebsLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (renEv)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (CoRel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak (leakFixB
  instrLeakF_coalesce)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak (GTr gTr_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstGuard (GuardInv guardInv_zero
  takenAt_of_guardInv guardInv_step)

/-! ## 1. The check and the computed trace -/

/-- **The check of the events of a renamed body**: the instruction at each position `k`
    passes `leakFixB` under its step renaming `stepRen w ao k i`. -/
def webLeakB (w : Nat → String → String) (ao : String → Option Nat) (body : List LinstrRM) :
    Bool :=
  (List.range body.length).all fun k =>
    match body[k]? with
    | some i => leakFixB (stepRen w ao k i) i
    | none => true

theorem webLeakB_instr {w : Nat → String → String} {ao : String → Option Nat}
    {body : List LinstrRM} (h : webLeakB w ao body = true) {k : Nat} {i : LinstrRM}
    (hi : body[k]? = some i) : leakFixB (stepRen w ao k i) i = true := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have := (List.all_eq_true.mp h) k (List.mem_range.mpr hk)
  rw [hi] at this
  exact this

/-- **The events of a step of the renamed body**: the events `e` of the step of `body` at
    position `k`, mapped by `renEv` of the step renaming of the instruction at `k`. -/
def webG (w : Nat → String → String) (ao : String → Option Nat) (body : List LinstrRM)
    (k : Nat) (e : List CTLeak) : List CTLeak :=
  match body[k]? with
  | some i => e.map (renEv (stepRen w ao k i))
  | none => e

/-! ## 2. The traced run -/

/-- **The traced run of the renamed body.** For a body accepted by `webB w body L obs aa ao`
    and by `webLeakB w ao body`, a halting traced run of the flag machine on `body` with
    trace `ℓ`, from a state `s` of the function `fn` at a position `k` at most
    `body.length` that satisfies `ConstGuard.GuardInv`, is matched with the same fuel by a halting traced run on the renamed
    body `webRen w ao body` from every state `s'` that has the registers, word memory, flags,
    function name and zero flag of `s` and whose arrays agree with those of `s` through
    `w k` on `L k`. The trace of the renamed run is the trace computed by `webG w ao body`
    along the run of `body` from `s`. The final states have equal registers, word memory
    and flags, their arrays agree through `w body.length` on `obs`, and the run on `body`
    ends at position `body.length`. -/
theorem lsemFuelMemFLeak_webs {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {fn : String} {body : List LinstrRM} {L : Nat → List String} {obs : List String}
    {w : Nat → String → String} (hc : webB w body L obs aa ao = true)
    (hx : webLeakB w ao body = true) :
    ∀ (fuel : Nat) {s s' t : LstateMF} {ℓ : List CTLeak}, s.prog.lfn = fn →
      s.prog.base.lpc ≤ body.length → GuardInv body s →
      CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base →
      s'.prog.lfn = s.prog.lfn → s'.zf = s.zf →
      lsemFuelMemFLeak (singletonProgM fn body) fuel s = some (t, ℓ) →
      ∃ t' g, lsemFuelMemFLeak (singletonProgM fn (webRen w ao body)) fuel s' = some (t', g)
        ∧ GTr (webG w ao body) (singletonProgM fn body) s g
        ∧ CoRel (w body.length) obs t.prog.base t'.prog.base ∧ t'.zf = t.zf
        ∧ t.prog.base.lpc = body.length := by
  have hfetch : ∀ {s s' : LstateMF}, s.prog.lfn = fn →
      CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base →
      s'.prog.lfn = s.prog.lfn →
      findInstrMem (singletonProgM fn body) s.prog = body[s.prog.base.lpc]?
        ∧ findInstrMem (singletonProgM fn (webRen w ao body)) s'.prog
            = (body[s.prog.base.lpc]?).map
                (fun i => renArr (stepRen w ao s.prog.base.lpc i) i) := by
    intro s s' hf hR hfn
    refine ⟨findInstrMem_singleton fn body s.prog hf, ?_⟩
    rw [findInstrMem_singleton fn _ s'.prog (hfn.trans hf), coRel_lpc hR]
    simp only [webRen, List.getElem?_mapIdx]
  have hhalt : ∀ (fuel : Nat) {s s' t : LstateMF} {ℓ : List CTLeak}, s.prog.lfn = fn →
      s.prog.base.lpc ≤ body.length →
      CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base →
      s'.prog.lfn = s.prog.lfn → s'.zf = s.zf → body[s.prog.base.lpc]? = none →
      lsemFuelMemFLeak (singletonProgM fn body) fuel s = some (t, ℓ) →
      ∃ t' g, lsemFuelMemFLeak (singletonProgM fn (webRen w ao body)) fuel s' = some (t', g)
        ∧ GTr (webG w ao body) (singletonProgM fn body) s g
        ∧ CoRel (w body.length) obs t.prog.base t'.prog.base ∧ t'.zf = t.zf
        ∧ t.prog.base.lpc = body.length := by
    intro fuel s s' t ℓ hf hle hR hfn hz hb h
    obtain ⟨e1, e2⟩ := hfetch hf hR hfn
    rw [lsemFuelMemFLeak_halt _ _ s (e1.trans hb)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hlen : s.prog.base.lpc = body.length := by
      have := List.getElem?_eq_none_iff.mp hb
      omega
    refine ⟨s', [], lsemFuelMemFLeak_halt _ _ s' (by rw [e2, hb]; rfl),
      GTr.halt s (e1.trans hb), ?_, hz, hlen⟩
    rw [hlen] at hR
    exact hR.mono (webB_obs hc)
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t ℓ hf hle hgi hR hfn hz h
      cases hb : body[s.prog.base.lpc]? with
      | none => exact hhalt 0 hf hle hR hfn hz hb h
      | some i =>
          obtain ⟨e1, -⟩ := hfetch hf hR hfn
          simp [lsemFuelMemFLeak, e1, hb] at h
  | succ n ih =>
      intro s s' t ℓ hf hle hgi hR hfn hz h
      cases hb : body[s.prog.base.lpc]? with
      | none => exact hhalt (n + 1) hf hle hR hfn hz hb h
      | some i =>
          obtain ⟨e1, e2⟩ := hfetch hf hR hfn
          cases he : evalInstrPMemF (singletonProgM fn body) i s with
          | none => simp [lsemFuelMemFLeak, e1, hb, he] at h
          | some u =>
              rw [lsemFuelMemFLeak_step _ _ i s u (e1.trans hb) he] at h
              obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
              have hlt : s.prog.base.lpc < body.length := (List.getElem?_eq_some_iff.mp hb).1
              have hci := webB_instr hc hb
              unfold webInstrB at hci
              simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hci
              obtain ⟨⟨⟨hco, hpre⟩, hsucc⟩, -⟩ := hci
              have hRσ := coRel_congr hR (fun r hr => (hpre r hr).symm)
              have hn : shadowCall? i.1 = none := by
                by_contra hne
                rw [evalInstrPMemF_shadowCall _ i s hne] at he
                cases he
              obtain ⟨u', hu', hRu, hfu, hfs, hzu, hleu⟩ :=
                evalInstrPMemF_coalesce hco hlt (takenAt_of_guardInv hgi hb) hRσ hfn hz he
              have hnext := (evalInstrPMemF_next _ i s u he).2
              have hRu' := coRel_congr hRu (hsucc _ (mem_webSuccs_of_nextPc hnext))
              have hu'' : evalInstrPMemF (singletonProgM fn (webRen w ao body))
                  (renArr (stepRen w ao s.prog.base.lpc i) i) s' = some u' := by
                rw [evalInstrPMemF_congr_labels
                  (b2 := body.map (renArr (stepRen w ao s.prog.base.lpc i)))
                  (fun l => by rw [findLabelMem_webRen, findLabelMem_map_renArr])]
                exact hu'
              obtain ⟨t', g, ht', hg, hRt, hzt, hlt'⟩ := ih (hfs.trans hf) hleu
                (guardInv_step hgi hb he) hRu' hfu hzu hq
              refine ⟨t', webG w ao body s.prog.base.lpc (instrLeakF i s) ++ g, ?_,
                GTr.step s u i g (e1.trans hb) he hg, hRt, hzt, hlt'⟩
              rw [lsemFuelMemFLeak_step _ _ _ s' u' (by rw [e2, hb]; rfl) hu'', ht',
                Option.map_some, instrLeakF_coalesce (webLeakB_instr hx hb) hn hR.reg hz]
              simp only [webG, hb]

/-- **The traced run of the renamed body from its entry.** For a body accepted by `webB` and
    `webLeakB`, a halting traced run of the flag machine on `body` from a state `s` of the
    function `fn` at position `0` is matched with the same fuel by a halting traced run on
    `webRen w ao body` from every state `s'` that has the registers, word memory, flags,
    function name and zero flag of `s` and the arrays of `s` at the names of `L 0`. The
    trace of the renamed run is the trace computed by `webG w ao body` along the run of
    `body`; the final states have equal registers, word memory and flags, and equal arrays
    at the names of `obs`, and the run on `body` ends at position `body.length`. -/
theorem lsemFuelMemFLeak_webs_entry {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {w : Nat → String → String} (hc : webB w body L obs aa ao = true)
    (hx : webLeakB w ao body = true) (fuel : Nat) {s s' t : LstateMF} {ℓ : List CTLeak}
    (hf : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (hR : CoRel id (L 0) s.prog.base s'.prog.base) (hfn : s'.prog.lfn = s.prog.lfn)
    (hz : s'.zf = s.zf) (h : lsemFuelMemFLeak (singletonProgM fn body) fuel s = some (t, ℓ)) :
    ∃ t' g, lsemFuelMemFLeak (singletonProgM fn (webRen w ao body)) fuel s' = some (t', g)
      ∧ GTr (webG w ao body) (singletonProgM fn body) s g
      ∧ CoRel id obs t.prog.base t'.prog.base ∧ t'.zf = t.zf
      ∧ t.prog.base.lpc = body.length := by
  have hR0 : CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base := by
    rw [hpc]
    exact coRel_congr hR (fun r hr => (webB_entry hc r hr).symm)
  obtain ⟨t', g, ht', hg, hRt, hzt, hlt⟩ :=
    lsemFuelMemFLeak_webs hc hx fuel hf (by omega) (guardInv_zero body hpc) hR0 hfn hz h
  exact ⟨t', g, ht', hg, coRel_congr hRt (webB_exit hc), hzt, hlt⟩

/-! ## 3. Constant time -/

/-- **The entry states of the renamed body.** `s` is a state of the function `fn` at
    position `0`, and `s'` has the registers, word memory, flags, function name and zero
    flag of `s`, with the arrays of `s` at the names of `L 0`. -/
def WebStart (fn : String) (L : Nat → List String) (s s' : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ s.prog.base.lpc = 0 ∧ CoRel id (L 0) s.prog.base s'.prog.base
    ∧ s'.prog.lfn = s.prog.lfn ∧ s'.zf = s.zf

/-- **The public-equality relation of the renamed body.** Two states are related when they
    are the images, by `WebStart fn L`, of two states related by `pubEq` from each of which
    `body` has a terminating run. -/
def WebPub (fn : String) (body : List LinstrRM) (L : Nat → List String)
    (pubEq : LstateMF → LstateMF → Prop) (s₁' s₂' : LstateMF) : Prop :=
  ∃ s₁ s₂, pubEq s₁ s₂ ∧ WebStart fn L s₁ s₁' ∧ WebStart fn L s₂ s₂'
    ∧ (∃ ℓ, FRun (singletonProgM fn body) s₁ ℓ) ∧ (∃ ℓ, FRun (singletonProgM fn body) s₂ ℓ)

/-- **Constant time of the renamed body.** For a body accepted by `webB w body L obs aa ao`
    and `webLeakB w ao body`, constant time of `body` on the flag machine at `pubEq` gives
    constant time of the renamed body `webRen w ao body` at `WebPub fn body L pubEq`: two
    terminating runs of the renamed body, from the images of two `pubEq`-related states
    from which `body` terminates, have equal traces. -/
theorem memFCT_webs {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {fn : String} {body : List LinstrRM} {L : Nat → List String} {obs : List String}
    {w : Nat → String → String} (hc : webB w body L obs aa ao = true)
    (hx : webLeakB w ao body = true) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn body) pubEq) :
    MemFCT (singletonProgM fn (webRen w ao body)) (WebPub fn body L pubEq) := by
  rintro s₁' s₂' ℓ₁' ℓ₂' ⟨s₁, s₂, hp, ⟨hf₁, hpc₁, hR₁, hfn₁, hz₁⟩, ⟨hf₂, hpc₂, hR₂, hfn₂, hz₂⟩,
    ⟨ℓ₁, f₁, t₁, r₁⟩, ⟨ℓ₂, f₂, t₂, r₂⟩⟩ hr₁ hr₂
  have heq : ℓ₁ = ℓ₂ := hct s₁ s₂ ℓ₁ ℓ₂ hp ⟨f₁, t₁, r₁⟩ ⟨f₂, t₂, r₂⟩
  subst heq
  obtain ⟨t₁', g₁, ht₁, hg₁, -⟩ :=
    lsemFuelMemFLeak_webs_entry hc hx f₁ hf₁ hpc₁ hR₁ hfn₁ hz₁ r₁
  obtain ⟨t₂', g₂, ht₂, hg₂, -⟩ :=
    lsemFuelMemFLeak_webs_entry hc hx f₂ hf₂ hpc₂ hR₂ hfn₂ hz₂ r₂
  rw [fRun_unique hr₁ ⟨f₁, t₁', ht₁⟩, fRun_unique hr₂ ⟨f₂, t₂', ht₂⟩]
  exact gTr_eq (webG w ao body) fn body f₁ s₁ t₁ ℓ₁ r₁ f₂ s₂ t₂ r₂ hf₁ hf₂
    (hpc₁.trans hpc₂.symm) g₁ g₂ hg₁ hg₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebsLeak
