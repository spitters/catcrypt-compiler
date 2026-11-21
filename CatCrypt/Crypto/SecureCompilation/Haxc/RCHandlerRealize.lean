/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerWitness
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiEncode
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportContract
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnFrame

/-!
# Realisability of the records of linked kernels

`Realizes m (linkHandler m)` (module `RCHandlerWitness`) holds when, at every target event
related by `contractREG` to its linked call, some return state holds the meaning of the linked
function on the separation contracts. This module derives it from four facts about each linked
function `l` of `m` (`RecordRealizes`):

* its code meets its contract (`LinkedFn.Meets`), so that a run of the code from an entry state
  satisfying the contract precondition ends in a return state of the contract postcondition;
* the read-back of its result reads at entry only registers of `abiRegs` (the registers whose
  values the resources at entry fix);
* the contract postcondition gives the record postcondition `l.post` (`PostCompat`);
* at an entry state satisfying `l.pre` at which no contract precondition holds, the meaning is
  read back from some return state that satisfies `l.post` (`PostReal`).

At an entry state satisfying a contract precondition the return state is the end of a run of
the code; at another entry state the frame clauses of `RetOK` are vacuous and the return state
is the one of `PostReal`.

## Main definitions

* `PostCompat`: the contract postcondition gives the record postcondition.
* `PostReal`: off the contract precondition, a return state satisfies the record
  postcondition and holds the meaning.
* `RecordRealizes`: the four facts about a linked function.

## Main results

* `contractPre_of_entryAt`: the resources at entry at a state where the meaning of the
  arguments the layout reads is defined give the contract precondition.
* `realizes_linkHandler`: the records of the linked functions of `m` are realisable at their
  meanings when each satisfies `RecordRealizes`.
* `handlerCoupledCG_linkHandler`: under the same facts, `specHandler m (linkHandler m)` is a
  target handler of `HandlerCoupledCG` at every heap relation.
* `exists_resultOf_enc_words`: the encoding of `n` words is the read-back of a result of `n`
  words at some return state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerRealize

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState Disjoint8)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.Hax.ImpToNF (enc)
open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (contractRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnFrame (framePost_of_contractPost)
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerWitness
open _root_.Hax

/-! ## The facts about a record -/

/-- **The contract postcondition gives the record postcondition**: a return state of the
    postcondition of `LinkedFn.contract` at logical variables whose precondition holds at the
    entry state satisfies `l.post` with that entry state. -/
def PostCompat (l : LinkedFn) : Prop :=
  ∀ a s s', (l.contractPre a).holds s → (l.contractPost a).holds s' → l.post s s'

/-- **Off the contract precondition, the record is realisable**: at an entry state satisfying
    `l.pre` at which the precondition of `LinkedFn.contract` holds at no logical variables, a
    value `v` of the meaning at the arguments the layout reads is read back from a return state
    that satisfies `l.post`. -/
def PostReal (l : LinkedFn) : Prop :=
  ∀ s v, l.pre s → l.sem (l.layout.args.map (·.read s)) = some v →
    (∀ a, ¬ (l.contractPre a).holds s) → ∃ s', l.post s s' ∧ l.layout.ResultOf s s' v

/-- **The facts that make the record of a linked function realisable**: its code meets its
    contract, the read-back of its result reads at entry only registers of `abiRegs`, the
    contract postcondition gives the record postcondition (`PostCompat`), and off the contract
    precondition the record is realisable (`PostReal`). -/
def RecordRealizes (l : LinkedFn) : Prop :=
  l.Meets ∧ (∀ r ∈ resultRegs l.layout.result, r ∈ abiRegs l.layout) ∧ PostCompat l ∧
    PostReal l

/-! ## Realisability at the meanings -/

/-- **The contract precondition from the resources at entry**: at a state where the resources
    at entry hold at `a` and the meaning of the arguments the layout reads is defined, the
    precondition of `LinkedFn.contract` holds at `a`. -/
theorem contractPre_of_entryAt {l : LinkedFn} {a : CallVar} {s : AState}
    (h : (l.entryAt a).holds s) (hs : (l.sem (l.layout.args.map (·.read s))).isSome = true) :
    (l.contractPre a).holds s := by
  refine ⟨by simp, h, ?_⟩
  rw [← (holds_entryAt h).2.2.1]
  exact hs

/-- **The records of the linked functions are realisable at their meanings** when each linked
    function of `m` satisfies `RecordRealizes`. -/
theorem realizes_linkHandler {m : HaxModule} (hK : ∀ l ∈ m.linked, RecordRealizes l) :
    Realizes m (linkHandler m) := by
  intro e₂ he
  obtain ⟨-, l, hl, hpre, hargs⟩ := he
  obtain ⟨hM, hsub, hC, hR⟩ := hK l (List.mem_of_find?_eq_some hl)
  have hans : linkHandler m e₂.call = l.sem e₂.call.args := by
    unfold linkHandler
    rw [hl]
  rcases hv : l.sem e₂.call.args with _ | v
  · exact ⟨e₂.entry, fun l' _ w hw => by simp [hans, hv] at hw⟩
  have hreads : l.layout.args.map (·.read e₂.entry) = e₂.call.args := hargs.symm
  have hdef : (l.sem (l.layout.args.map (·.read e₂.entry))).isSome = true := by
    rw [hreads, hv]
    rfl
  have key : ∃ s', l.layout.ResultOf e₂.entry s' v ∧
      contractRun l.frameContract () e₂.entry () s' ∧ l.post e₂.entry s' ∧
      ∀ x, (l.entryAt x).holds e₂.entry → l.layout.ResultOf (entryRegs x.rv) s' v := by
    by_cases hc : ∃ a, (l.contractPre a).holds e₂.entry
    · obtain ⟨a, ha⟩ := hc
      obtain ⟨q, -, hS⟩ := hM.code
      obtain ⟨t, s', hr⟩ := hS.halts a _ ha
      have hall : ∀ b, (l.entryAt b).holds e₂.entry → (l.contractPost b).holds s' ∧
          Footprinted.AgreeOn (l.contractWrites b)ᶜ e₂.entry s' := fun b hb =>
        ⟨hS.post b _ t s' (contractPre_of_entryAt hb hdef) hr,
          hS.keep b _ t s' (contractPre_of_entryAt hb hdef) hr⟩
      have hres : ∀ b, (l.entryAt b).holds e₂.entry →
          l.layout.ResultOf (entryRegs b.rv) s' v := by
        intro b hb
        obtain ⟨w, hw, hrw⟩ := (hall b hb).1.2.2.2
        rw [← (holds_entryAt hb).2.2.1, hreads, hv] at hw
        cases hw
        exact hrw
      refine ⟨s', ?_, ⟨rfl, fun b hb => ⟨framePost_of_contractPost (hall b hb).1, (hall b hb).2⟩⟩,
        hC a _ s' ha (hS.post a _ t s' ha hr), hres⟩
      exact (hres a (entryAt_of_pre ha)).trans (read_entry_congr _ fun r hr =>
        ((holds_entryAt (entryAt_of_pre ha)).1 r (hsub r hr)).symm)
    · have hno : ∀ b, ¬ (l.entryAt b).holds e₂.entry := fun b hb =>
        hc ⟨b, contractPre_of_entryAt hb hdef⟩
      obtain ⟨s', hpost, hres⟩ := hR _ v (hpre (by simp [hv])) (by rw [hreads, hv])
        fun a ha => hc ⟨a, ha⟩
      exact ⟨s', hres, ⟨rfl, fun b hb => absurd hb (hno b)⟩, hpost, fun b hb => absurd hb (hno b)⟩
  obtain ⟨s', h1, h2, h3, h4⟩ := key
  refine ⟨s', fun l' hl' w hw => ?_⟩
  rw [hl] at hl'
  cases hl'
  rw [hans, hv] at hw
  cases hw
  exact ⟨h1, h2, fun _ => ⟨h3, h4⟩⟩

/-- **A witness of `HandlerCoupledCG` from the facts about the records**: when each linked
    function of `m` satisfies `RecordRealizes`, the target handler `specHandler m (linkHandler m)`
    is coupled with the meanings on the separation contracts, at every heap relation. -/
theorem handlerCoupledCG_linkHandler {m : HaxModule} (hK : ∀ l ∈ m.linked, RecordRealizes l)
    (I : RPre) : HandlerCoupledCG m I (specHandler m (linkHandler m)) :=
  handlerCoupledCG_specHandler (realizes_linkHandler hK) I

/-! ## Return states of a word result -/

/-- **The encoding of `n` words is the read-back of a result of `n` words**: when the result of
    `σ` is the `n` words at the register `r` and `8 n ≤ 2 ^ 64`, the state `s` with the words of
    `x` stored at the address `r` holds at entry reads back `enc (.arr n (.word 64)) x`. -/
theorem exists_resultOf_enc_words {σ : AbiLayout} {r : String} {n : Nat}
    (hres : σ.result = .words r n) (hn : 8 * n ≤ 2 ^ 64) (s : AState) (x : Fin n → BitVec 64) :
    ∃ s', σ.ResultOf s s' (enc (.arr n (.word 64)) x) := by
  let ws : List (BitVec 64 × BitVec 64) :=
    List.ofFn fun i : Fin n => (s.regs r + BitVec.ofNat 64 (8 * i.val), x i)
  have hpw : ws.Pairwise fun a b => Disjoint8 a.1 b.1 := by
    simp only [ws, List.pairwise_ofFn]
    intro i j hij
    exact disjoint8_words _ i.2 j.2 hn (by omega)
  refine ⟨{ s with mem := writeWords s.mem ws }, ?_⟩
  unfold AbiLayout.ResultOf
  rw [hres]
  simp only [ResultKind.read, enc, wordsAt]
  congr 1
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [read64_writeWords_mem _ _ hpw (List.mem_ofFn.2 ⟨⟨j, by simpa using h2⟩, rfl⟩)]

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerRealize
