/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTarget

/-!
# The kinds and the run relations of the callees of a module

The back half at a table `T` of callees takes a kind of each callee, a run relation `X` that meets
the specification of the kind, and a procedure table whose summaries are those of the kinds. The
answer relation `BackRA PT X` asks the target answer of a call to be a return state of the run
relation of its symbol. For the answers of a target handler that meets the separation contracts
of the linked functions (`contractRAC`), the run relation is the run relation of the contract
(`NFProgCallTreeCallsLinked.contractRun`), which admits every return state the contract admits:
an answer of the separation contracts at a defined meaning is a return state of it
(`contractRun_of_contractRAC`).

At the linked kernels of a module with distinct names, the kinds `moduleKind` meet their top
hypotheses and their specifications at the run relations of the contracts, since the code of each
kernel meets its contract (`LinkedKernel.contract_code`, `sContract_contractRun`), and the
procedure table of the summaries of the kinds has those summaries (`kinds_of_linked`).

## Main definitions

* `contractRunOf`: the run relation of the contract of the first linked function with a name.
* `summaryOf`: the procedure table of the summaries of the kinds of the linked functions.

## Main results

* `contractRunOf_of_contractRAC`: an answer of the separation contracts at a defined meaning is
  a return state of `contractRunOf` at the symbol of the call.
* `kinds_of_linked`: the hypotheses of the back half on the kinds, the run relations and the
  summaries, at the kinds `moduleKind` and the run relations of the contracts of the linked
  kernels of a module.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeKinds

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (contractRun
  sContract_contractRun)
open CatCrypt.Crypto.Hax (LinkedFn)

/-- **The run relation of the contract of a linked function by name**: the run relation of the
    contract of the first linked function of `ls` with the name `f`, at the trace `tr₀`; no run at
    another name. -/
def contractRunOf (ls : List LinkedFn) (tr₀ : List CTLeak) (f : String) : CalleeRun :=
  match ls.find? (·.name == f) with
  | some l => contractRun l.contract tr₀
  | none => fun _ _ _ => False

/-- **An answer of the separation contracts is a return state of the run relation of its
    symbol.** At an answer related by `contractRAC` whose source answer is a value, the target
    answer is a return state of `contractRunOf ls tr₀` at the name of the call, from the entry
    state of the call, at the trace `tr₀`. -/
theorem contractRunOf_of_contractRAC {m : CatCrypt.Crypto.Hax.HaxModule}
    {e₁ : NFCallTree.linkSig.Event} {e₂ : (TargetCallTree.kSig Ascent.AddrMem.AState).Event}
    {a₁ : NFCallTree.linkSig.Resp e₁} {a₂ : (TargetCallTree.kSig Ascent.AddrMem.AState).Resp e₂}
    (h : RegionLinkContract.contractRAC m e₁ e₂ a₁ a₂) {v : _root_.Hax.Value}
    (hv : (a₁ : Option _root_.Hax.Value) = some v) (tr₀ : List CTLeak) :
    ∃ s', (a₂ : Option Ascent.AddrMem.AState) = some s'
      ∧ contractRunOf m.linked tr₀ (NFCallTree.LinkCall.name e₁) (TargetCallTree.KCall.entry e₂)
        tr₀ s' := by
  obtain ⟨l, hl, -, -⟩ := id h
  obtain ⟨s', hs', hrun⟩ := NFProgCallTreeCallsLinked.contractRun_of_contractRAC hl h hv tr₀
  refine ⟨s', hs', ?_⟩
  simp only [contractRunOf, hl]
  exact hrun

/-- The procedure table of the summaries of the kinds `moduleKind ls d`. -/
def summaryOf (ls : List LinkedFn) (d : CalleeKind) : LprogIsa.ProcTable :=
  fun f => some (moduleKind ls d f).summary

/-- **The kinds of the linked kernels of a module at the run relations of their contracts.** Let
    the linked functions `ls` have distinct names and each be a linked kernel, and the functions of
    the table `T` be among their data. At every function of `T`, the kind `moduleKind ls d` meets
    its top hypotheses and its specification at the run relation of the contract of the linked
    function, and the procedure table `summaryOf ls d` has the summary of the kind. -/
theorem kinds_of_linked {ls : List LinkedFn} (hnd : (ls.map (·.name)).Nodup)
    (hk : ∀ l ∈ ls, LinkedKernel l) {T : CalleeTab}
    (hsub : T.fns.Sublist (ls.filterMap LinkedFn.calleeData)) (d : CalleeKind)
    (tr₀ : List CTLeak) :
    (∀ c ∈ T.fns, (moduleKind ls d c.name).Top c
      ∧ (moduleKind ls d c.name).Spec (contractRunOf ls tr₀ c.name))
    ∧ ∀ c ∈ T.fns, summaryOf ls d c.name = some (moduleKind ls d c.name).summary := by
  refine ⟨fun c hc => ?_, fun _ _ => rfl⟩
  obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hc)
  have hn := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1
  have hf : ls.find? (·.name == c.name) = some l := by
    rw [hn]
    exact find?_name_of_nodup hnd hl
  have hkk : moduleKind ls d c.name = kernelKind l c := by
    simp [moduleKind, hf, hlc]
  have hX : contractRunOf ls tr₀ c.name = contractRun l.contract tr₀ := by
    simp only [contractRunOf, hf]
  obtain ⟨htop, hspec, -, -⟩ := (hk l hl).kind_facts hlc
  obtain ⟨q, -, hm⟩ := (hk l hl).contract_code hlc
  rw [hkk, hX]
  exact ⟨htop, hspec _ (sContract_contractRun hm tr₀)⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeKinds
