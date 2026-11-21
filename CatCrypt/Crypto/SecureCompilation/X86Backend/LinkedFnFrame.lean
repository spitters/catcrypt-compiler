/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked

/-!
# The frame contract of a linked function

The contract `LinkedFn.contract l` fixes the result of a call to the meaning `l.sem`: its
precondition asks the meaning to be defined at the argument values, and its postcondition
contains `resultAt l.layout l.sem`. The frame contract `LinkedFn.frameContract l` keeps the
resources and the frame facts of the contract and states nothing about the result:

* the precondition is the resources at entry `LinkedFn.entryAt`;
* the postcondition `LinkedFn.framePost` owns the locations of the precondition and keeps the
  stack register and the return word at their entry values;
* the write set and the public relation are those of the contract.

A callee whose answer is read from its return state, rather than computed by the meaning,
meets the frame contract. The entry state of a call satisfies the postcondition
(`framePost_of_entryAt`), so the run relation `contractRun` of the frame contract meets it
with no hypothesis (`sContract_contractRun_frame`), and meets its interface
`LinkedFn.frameSig` (`calleeSpec_contractRun_frame`).

The contract is the frame contract with the result of the meaning added: a run relation that
meets the frame contract and gives the result of the meaning from the precondition of the
contract meets the contract (`sContract_contract_of_frame`), and likewise for the run relation
of a contract (`contractRun_contract_of_frame`).

## Main definitions

* `LinkedFn.framePost`, `LinkedFn.frameContract`: the frame contract.
* `LinkedFn.frameSig`: the frame contract read as a `CalleeSig`.

## Main results

* `framePost_of_entryAt`, `framePost_of_contractPost`: the postcondition at the entry state and
  from the postcondition of the contract.
* `sContract_contract_of_frame`, `contractRun_contract_of_frame`: the contract from the frame
  contract and the result of the meaning.
* `calleeSpec_frameSig_of_sContract`: a run relation that meets the frame contract meets its
  interface.
* `sContract_contractRun_frame`, `calleeSpec_contractRun_frame`: the run relation of the frame
  contract meets the frame contract and its interface.
* `footBelow_frameSig`: the footprint of the interface of a register result is among the
  `frame` bytes below the entry stack register.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (FootBelow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (contractRun)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax (LinkedFn)
open Footprinted SAssert

namespace CatCrypt.Crypto.Hax.LinkedFn

/-- **The postcondition of the frame contract**: the locations of the resources at entry
    owned, and the stack register and the return word at their entry values. -/
def framePost (l : LinkedFn) (a : CallVar) : SAssert AState Loc :=
  conj (own (l.entryAt a).fp) (conj (regPts "%rsp" a.sp) (retAt a.sp a.ret))

/-- **The frame contract of a linked function**: the resources at entry as precondition,
    `framePost` as postcondition, and the write set and the public relation of the contract.
    It states nothing about the result of the call. -/
def frameContract (l : LinkedFn) : ContractSpec AState Loc CallVar where
  pre := l.entryAt
  post := l.framePost
  writes a _ := l.contractWrites a
  pub := l.pubRegsAgree

/-- **The interface of the frame contract** at the argument names `args` and the result name
    `res`: the clobbered registers of the record; as precondition, the resources at entry at
    some logical variables; as footprint, the memory of the write set; as postcondition,
    `framePost` at logical variables whose resources hold at entry; and the public relation of
    the contract. -/
def frameSig (l : LinkedFn) (args : List String) (res : Option String) : CalleeSig where
  args := args
  res := res
  clob := fun x => l.clob.contains x
  pre s := ∃ a, (l.entryAt a).holds s
  foot s x := ∃ a, (l.entryAt a).holds s ∧ Loc.mem x ∈ l.contractWrites a
  post s s' := ∃ a, (l.entryAt a).holds s ∧ (l.framePost a).holds s'
  pub := l.pubRegsAgree

end CatCrypt.Crypto.Hax.LinkedFn

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnFrame

/-! ## 1. The postcondition of the frame contract -/

/-- **The entry state satisfies the postcondition of the frame contract.** -/
theorem framePost_of_entryAt {l : LinkedFn} {a : CallVar} {s : AState}
    (h : (l.entryAt a).holds s) : (l.framePost a).holds s :=
  ⟨trivial, (holds_entryAt h).2.1, h.1.2.2.2.2.2.1⟩

/-- **The postcondition of the contract gives that of the frame contract.** -/
theorem framePost_of_contractPost {l : LinkedFn} {a : CallVar} {s' : AState}
    (h : (l.contractPost a).holds s') : (l.framePost a).holds s' :=
  ⟨trivial, h.2.1, h.2.2.1⟩

/-! ## 2. The contract from the frame contract -/

/-- **The contract is the frame contract with the result of the meaning.** A run relation that
    meets the frame contract, and whose runs from the precondition of the contract end at the
    result of the meaning, meets the contract. -/
theorem sContract_contract_of_frame {l : LinkedFn} {X : CalleeRun}
    (h : SContract X l.frameContract)
    (hres : ∀ a s t s', (l.contractPre a).holds s → X s t s' →
      (resultAt l.layout l.sem a.rv a.vals).holds s') :
    SContract X l.contract where
  halts a s hs := h.halts a s (entryAt_of_pre hs)
  post a s t s' hs hr := by
    obtain ⟨-, hsp, hret⟩ := h.post a s t s' (entryAt_of_pre hs) hr
    exact ⟨trivial, hsp, hret, hres a s t s' hs hr⟩
  keep a s t s' hs hr := h.keep a s t s' (entryAt_of_pre hs) hr
  ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ :=
    h.ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' (entryAt_of_pre h₁) (entryAt_of_pre h₂) hp hX₁ hX₂

/-- **A run of the frame contract at the result of the meaning is a run of the contract.** A
    run of the run relation of the frame contract whose return state holds the result of the
    meaning at every logical variable of the precondition of the contract is a run of the run
    relation of the contract. -/
theorem contractRun_contract_of_frame {l : LinkedFn} {Tr : Type} {tr₀ : Tr} {s s' : AState}
    {tr : Tr} (h : contractRun l.frameContract tr₀ s tr s')
    (hres : ∀ a, (l.contractPre a).holds s → (resultAt l.layout l.sem a.rv a.vals).holds s') :
    contractRun l.contract tr₀ s tr s' := by
  refine ⟨h.1, fun a ha => ?_⟩
  obtain ⟨⟨-, hsp, hret⟩, hag⟩ := h.2 a (entryAt_of_pre ha)
  exact ⟨⟨trivial, hsp, hret, hres a ha⟩, hag⟩

/-! ## 3. The interface of the frame contract -/

/-- **A run relation that meets the frame contract meets its interface**, at every argument
    names and result name. -/
theorem calleeSpec_frameSig_of_sContract {l : LinkedFn} {X : CalleeRun}
    (h : SContract X l.frameContract) (args : List String) (res : Option String) :
    CalleeSpec X (l.frameSig args res) := by
  refine calleeSpec_of_contract h (fun s ⟨a, ha⟩ => ⟨a, ha, fun s' h' => ⟨a, ha, h'⟩, ?_⟩)
    (fun _ _ hp => hp)
  rintro (r | f | y) hx
  · exact ⟨by simpa [LinkedFn.frameSig] using hx.1, hx.2⟩
  · trivial
  · exact ⟨a, ha, hx⟩

/-- **The run relation of the frame contract meets the frame contract**, with no hypothesis:
    the entry state is a return state of it. -/
theorem sContract_contractRun_frame (l : LinkedFn) (tr₀ : List CTLeak) :
    SContract (contractRun l.frameContract tr₀) l.frameContract where
  halts _ s _ := ⟨tr₀, s, rfl, fun _ hb => ⟨framePost_of_entryAt hb, fun _ _ => rfl⟩⟩
  post a _ _ _ hs hr := (hr.2 a hs).1
  keep a _ _ _ hs hr := (hr.2 a hs).2
  ct _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ := h₁.1.trans h₂.1.symm

/-- **The run relation of the frame contract meets its interface**, at every argument names
    and result name. -/
theorem calleeSpec_contractRun_frame (l : LinkedFn) (tr₀ : List CTLeak) (args : List String)
    (res : Option String) : CalleeSpec (contractRun l.frameContract tr₀) (l.frameSig args res) :=
  calleeSpec_frameSig_of_sContract (sContract_contractRun_frame l tr₀) args res

/-- **The footprint of the interface of a register result** is among the `frame` bytes below
    the entry stack register. -/
theorem footBelow_frameSig {l : LinkedFn} {r : String} (hr : l.layout.result = .reg r)
    (args : List String) (res : Option String) : FootBelow (l.frameSig args res) l.frame := by
  rintro s x ⟨a, ha, hx | hx⟩
  · obtain ⟨-, hsp, -⟩ := holds_entryAt ha
    rw [hsp]
    exact hx
  · rw [hr] at hx
    cases hx

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnFrame
