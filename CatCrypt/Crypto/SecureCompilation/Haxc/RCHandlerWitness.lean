/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed

/-!
# Target handlers that meet the separation contracts

The robust-compilation theorems over handlers (`haxc_rcH`, `haxc_rcHKeyed`, `haxc_rcHSt`)
quantify over target handlers coupled with a source oracle on the separation contracts of the
linked functions (`HandlerCoupledCG`, `HandlerCoupledKeyed`, `HandlerCoupledSt`). This module
gives such a target handler and characterises when one exists.

The event relation `contractREG m` fixes the source event of a target event `e₂`: it is the
linked call `e₂.call`. The target handler `specHandler m ans` answers `e₂` by a return state that
holds the source answer `ans e₂.call` in the sense of the separation contracts (`RetOK`), chosen
among the return states with that property, as a point mass. Such a return state exists at every
related event exactly when the records of the linked functions are realisable at the answers
(`Realizes`): every value answer is written by some return state that satisfies the record
postcondition, the result read-back of the layout and the frame contract. For the meanings of
the linked functions, `Realizes m (linkHandler m)` is equivalent to the existence of a target
handler of `HandlerCoupledCG` at equal heaps (`exists_handlerCoupledCG_iff`).

## Main definitions

* `RetOK`: a return state that holds an answer on the separation contracts.
* `specHandler`: the target handler answering a call by a return state of `RetOK`.
* `Realizes`: at every related event, a return state of `RetOK` exists for the answer.

## Main results

* `handlerCoupled_specHandler`: `specHandler m ans` is coupled with the point mass at `ans` on
  the separation contracts at an answer predicate satisfied by `ans`.
* `handlerCoupledCG_specHandler`: the witness of `HandlerCoupledCG` at the meanings.
* `realizes_of_handlerCoupledCG`, `exists_handlerCoupledCG_iff`: a handler of `HandlerCoupledCG`
  exists exactly when the records are realisable at the meanings.
* `handlerCoupledKeyed_specHandler`, `handlerCoupledKeyed_point_specHandler`: the witnesses of
  `HandlerCoupledKeyed` at a keyed oracle and at `pointOracle`.
* `handlerCoupledSt_keyedSt_specHandler`: the witness of `HandlerCoupledSt` at the stateful
  oracle of a keyed oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerWitness

open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (contractRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (entryRegs)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP (HandlerCoupled)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful
open _root_.Hax

/-! ## Return states that hold an answer -/

/-- **A return state that holds the answer `a` to the call `e₂`** on the separation contracts:
    for the linked function `l` of the name of the call and every value answer `v`, the return
    state holds `v` in the result read-back of the layout and is a return state of the frame
    contract of `l`; when `v` is the meaning of `l` at the arguments, it also satisfies the
    record postcondition and holds `v` in the read-back from the entry registers of every
    logical variable whose resources hold at the entry. -/
def RetOK (m : HaxModule) (e₂ : KCall AState) (a : Option Value) (s' : AState) : Prop :=
  ∀ l, m.linked.find? (·.name == e₂.call.name) = some l → ∀ v, a = some v →
    l.layout.ResultOf e₂.entry s' v ∧ contractRun l.frameContract () e₂.entry () s' ∧
      (l.sem e₂.call.args = some v → l.post e₂.entry s' ∧
        ∀ x, (l.entryAt x).holds e₂.entry → l.layout.ResultOf (entryRegs x.rv) s' v)

open Classical in
/-- **The target handler of an answer function** `ans`: a call `e₂` is answered by a return
    state that holds the source answer `ans e₂.call` (`RetOK`), chosen among those, and by
    `none` when there is none. -/
noncomputable def specAns (m : HaxModule) (ans : ∀ e : linkSig.Event, linkSig.Resp e)
    (e₂ : KCall AState) : Option AState :=
  if h : ∃ s', RetOK m e₂ (ans e₂.call) s' then some h.choose else none

/-- The target handler of an answer function as a handler in `SPComp`: the point mass at
    `specAns`. -/
noncomputable def specHandler (m : HaxModule) (ans : ∀ e : linkSig.Event, linkSig.Resp e) :
    ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e) :=
  fun e₂ => SPComp.pure (specAns m ans e₂)

/-- **The records of the linked functions are realisable at the answers `ans`**: at every
    target event related by `contractREG` to its linked call, a return state holds the answer
    of `ans` at that call. -/
def Realizes (m : HaxModule) (ans : ∀ e : linkSig.Event, linkSig.Resp e) : Prop :=
  ∀ e₂ : KCall AState, contractREG m e₂.call e₂ → ∃ s', RetOK m e₂ (ans e₂.call) s'

/-- Under realisability, the answer of `specAns` at a related event holds the source answer. -/
theorem specAns_retOK {m : HaxModule} {ans : ∀ e : linkSig.Event, linkSig.Resp e}
    (hr : Realizes m ans) {e₂ : KCall AState} (he : contractREG m e₂.call e₂) :
    ∃ s', specAns m ans e₂ = some s' ∧ RetOK m e₂ (ans e₂.call) s' := by
  have h := hr e₂ he
  exact ⟨h.choose, by simp [specAns, h], h.choose_spec⟩

/-! ## The coupling -/

/-- **The target handler `specHandler m ans` is coupled with the point mass at `ans`** on the
    separation contracts at an answer predicate `A` that the answers satisfy, at every heap
    relation, when the records are realisable at `ans`. -/
theorem handlerCoupled_specHandler {m : HaxModule} {A : AnsPred}
    {ans : ∀ e : linkSig.Event, linkSig.Resp e} (hA : ∀ e, SkipAns A m e (ans e))
    (hr : Realizes m ans) (I : RPre) :
    HandlerCoupled I (contractREG m) (contractRACA A m) (fun e => SPComp.pure (ans e))
      (specHandler m ans) := by
  intro e₁ e₂ he
  obtain ⟨hc, l, hl, -, -⟩ := id he
  subst hc
  obtain ⟨s', hs', hok⟩ := specAns_retOK hr he
  refine rHoare_ret fun s₁ s₂ hI => ⟨⟨l, hl, ?_, fun v hv => ⟨s', hs', hok l hl v hv⟩⟩, hI⟩
  have h := hA e₂.call
  simp only [SkipAns, hl] at h
  exact h

/-- **A witness of `HandlerCoupledCG`**: when the records of the linked functions are
    realisable at their meanings, the target handler `specHandler m (linkHandler m)` is coupled
    with the meanings on the separation contracts, at every heap relation. -/
theorem handlerCoupledCG_specHandler {m : HaxModule} (hr : Realizes m (linkHandler m))
    (I : RPre) : HandlerCoupledCG m I (specHandler m (linkHandler m)) := by
  intro e₁ e₂ he
  refine rHoare_mono_post
    (handlerCoupled_specHandler (A := SemAns) (fun e => skipAns_sem_iff.mpr rfl) hr I e₁ e₂ he)
    fun _ _ _ _ hp => ⟨(contractRACA_sem_iff he).mp hp.1, hp.2⟩

/-- **A handler of `HandlerCoupledCG` at equal heaps makes the records realisable at the
    meanings**: at a related event, the answer of the handler from any heap holds the meaning. -/
theorem realizes_of_handlerCoupledCG {m : HaxModule}
    {h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledCG m eqPre h₂) : Realizes m (linkHandler m) := by
  intro e₂ he
  have hk := hc e₂.call e₂ he
  have hnf : ∀ s, h₂ e₂ s none = 0 :=
    rHoare_noFail_right (Φ := eqPre) hk (fun s => ⟨s, rfl⟩) fun _ => SDistr.pure_apply_none _
  obtain ⟨o, ho⟩ := (h₂ e₂ Heap.empty).support_nonempty
  cases o with
  | none => exact absurd (hnf _) ((PMF.mem_support_iff _ _).mp ho)
  | some p =>
    obtain ⟨hra, -⟩ := rHoare_pure_left_support hk (rfl : eqPre Heap.empty Heap.empty)
      ((PMF.mem_support_iff _ _).mp ho)
    obtain ⟨l, hl, -, hv⟩ := (contractRACA_sem_iff he).mpr hra
    by_cases hs : ∃ v, linkHandler m e₂.call = some v
    · obtain ⟨v, hv'⟩ := hs
      obtain ⟨s', -, hres, hrun, hsem⟩ := hv v hv'
      refine ⟨s', fun l' hl' w hw => ?_⟩
      rw [hl] at hl'
      cases hl'
      rw [hv'] at hw
      cases hw
      exact ⟨hres, hrun, hsem⟩
    · refine ⟨e₂.entry, fun l' _ w hw => absurd ⟨w, hw⟩ hs⟩

/-- **A target handler of `HandlerCoupledCG` exists exactly when the records of the linked
    functions are realisable at their meanings.** -/
theorem exists_handlerCoupledCG_iff (m : HaxModule) :
    (∃ h₂, HandlerCoupledCG m eqPre h₂) ↔ Realizes m (linkHandler m) :=
  ⟨fun ⟨_, hc⟩ => realizes_of_handlerCoupledCG hc,
    fun hr => ⟨_, handlerCoupledCG_specHandler hr eqPre⟩⟩

/-! ## Keyed and stateful oracles -/

/-- **A witness of `HandlerCoupledKeyed`**: when the records are realisable at the answers of
    every key, the family of target handlers `specHandler m (O.ans k)` is coupled with the keyed
    oracle `O`. -/
theorem handlerCoupledKeyed_specHandler {m : HaxModule} (O : KeyedOracle m)
    (hr : ∀ k, Realizes m (O.ans k)) :
    HandlerCoupledKeyed O fun k => specHandler m (O.ans k) :=
  fun k => handlerCoupled_specHandler (O.typed k) (hr k) eqPre

/-- **A witness of `HandlerCoupledKeyed` at `pointOracle`**: the target handler
    `specHandler m (linkHandler m)`, through `handlerCoupledKeyed_point`. -/
theorem handlerCoupledKeyed_point_specHandler {m : HaxModule}
    (hr : Realizes m (linkHandler m)) :
    HandlerCoupledKeyed (pointOracle m) fun _ => specHandler m (linkHandler m) :=
  handlerCoupledKeyed_point (handlerCoupledCG_specHandler hr eqPre)

/-- **A witness of `HandlerCoupledSt` at the stateful oracle of a keyed oracle**: the family
    `specHandler m (O.ans k)` indexed by the key, as a stateful handler, through
    `handlerCoupledSt_keyedSt`. -/
theorem handlerCoupledSt_keyedSt_specHandler {m : HaxModule} (O : KeyedOracle m)
    (hr : ∀ k, Realizes m (O.ans k)) :
    HandlerCoupledSt (keyedSt O) (constSt fun k => specHandler m (O.ans k)) :=
  handlerCoupledSt_keyedSt (handlerCoupledKeyed_specHandler O hr)

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerWitness
