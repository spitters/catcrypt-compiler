/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
public import CatCrypt.Crypto.SecureCompilation.Haxc.LinkedKernel

/-!
# The call trees of `compileA` related up to the separation contracts of the linked functions

`TargetCallTree.R3Statement` relates the source call tree `nfTree` of a module and the target
call tree `targetTree` of the calling body of `compileA` by `Rutt`, at the event relation
`contractRE`, the answer relation `contractRA` and the read-back `resRel`. Two features of the
compiler are outside that relation:

* the chain of `compileA` removes a let-binding whose value is unread (`dceStep`, before the
  translation of calls `extCallStep`), and a call of a linked function is such a binding
  (`NfOp.call`): a source call whose value is unread performs an event that the target does not
  perform;
* the calling body keeps values in registers and in its stack frame across a call, and relies
  on the callee to keep every location outside the write set of its contract
  (`LinkedFn.contract`, through `CalleeKind.Spec`); `contractRA` constrains the return state by
  the field `LinkedFn.post` only, which need not keep these locations.

This module states the relation with both: `RuttS` is `Rutt` in which a source event may be
skipped, its continuation taken at the answer of the source handler, and `contractRAC` adds to
`contractRA` the postcondition and the frame of `LinkedFn.contract` at every logical variable
whose precondition holds at the entry state. The statement `R3StatementC` is this relation
between the trees of `R3Statement`.

## Main definitions

* `RuttS`: two finite call trees related up to relations on events, answers and leaves, with
  source events that the target skips.
* `contractRAC`, `HandlerMeetsC`: the answer relation of the separation contracts of the linked
  functions, and a target handler that meets it.
* `R3StatementC`: the call trees of `compileA` related by `RuttS` at the contracts.

## Main results

* `RuttS.of_rutt`: a relation by `Rutt` is a relation by `RuttS`.
* `interp_ruttS`: under related handlers, trees related by `RuttS` interpret to a failed source
  leaf or to related leaves.
* `contractRA_of_contractRAC`, `handlerMeets_of_handlerMeetsC`: the answer relation of the
  separation contracts implies `contractRA`, and a handler that meets it meets `HandlerMeets`.
* `r3c_consequence`: from the relation of `R3StatementC` and a target handler meeting the
  separation contracts, a source run to a value gives a target run reading it back.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open _root_.Hax
open _root_.Hax.InlineLocalClosures

/-! ## Related trees with skipped source events -/

/-- **Two finite call trees related up to relations, with skipped source events**: the
    clauses of `Rutt`, and a source event `e₁` that the target does not perform, whose
    continuation at the answer `h₁ e₁` of the source handler is related to the target tree. -/
inductive RuttS {E₁ E₂ : EventSig} {R₁ R₂ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
    (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (RR : R₁ → R₂ → Prop) (Fail : R₁ → Prop) : CallTree E₁ R₁ → CallTree E₂ R₂ → Prop
  | ret {r₁ : R₁} {r₂ : R₂} (h : RR r₁ r₂) : RuttS h₁ RE RA RR Fail (.ret r₁) (.ret r₂)
  | fail {r₁ : R₁} {t₂ : CallTree E₂ R₂} (h : Fail r₁) : RuttS h₁ RE RA RR Fail (.ret r₁) t₂
  | vis {e₁ : E₁.Event} {e₂ : E₂.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁}
      {k₂ : E₂.Resp e₂ → CallTree E₂ R₂} (he : RE e₁ e₂)
      (hk : ∀ a₁ a₂, RA e₁ e₂ a₁ a₂ → RuttS h₁ RE RA RR Fail (k₁ a₁) (k₂ a₂)) :
      RuttS h₁ RE RA RR Fail (.vis e₁ k₁) (.vis e₂ k₂)
  | skip {e₁ : E₁.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
      (hk : RuttS h₁ RE RA RR Fail (k₁ (h₁ e₁)) t₂) :
      RuttS h₁ RE RA RR Fail (.vis e₁ k₁) t₂

section RuttS

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
  {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}

/-- **A relation by `Rutt` is a relation by `RuttS`**, at every source handler. -/
theorem RuttS.of_rutt {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : Rutt RE RA RR Fail t₁ t₂) : RuttS h₁ RE RA RR Fail t₁ t₂ := by
  induction h with
  | ret h => exact .ret h
  | fail h => exact .fail h
  | vis he _ ih => exact .vis he ih

/-- **Interpretation of trees related with skipped source events**: under a target handler
    whose answers at related events are related to those of the source handler, two trees
    related by `RuttS` interpret to a failed source leaf or to related leaves. -/
theorem interp_ruttS (h₂ : ∀ e : E₂.Event, E₂.Resp e)
    (hh : ∀ e₁ e₂, RE e₁ e₂ → RA e₁ e₂ (h₁ e₁) (h₂ e₂))
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttS h₁ RE RA RR Fail t₁ t₂) :
    Fail (interp h₁ t₁) ∨ RR (interp h₁ t₁) (interp h₂ t₂) := by
  induction h with
  | ret h => exact .inr h
  | fail h => exact .inl h
  | vis he _ ih => exact ih _ _ (hh _ _ he)
  | skip _ ih => exact ih

end RuttS

/-! ## The separation contracts of the linked functions -/

/-- **The answer relation of the separation contracts**: the answer relation `contractRA`,
    and at every logical variable `a` whose precondition of the contract `LinkedFn.contract`
    holds at the entry state, the return state satisfies its postcondition and agrees with the
    entry state outside its write set. -/
def contractRAC (m : HaxModule) (e₁ : linkSig.Event) (e₂ : (kSig AState).Event)
    (a₁ : linkSig.Resp e₁) (a₂ : (kSig AState).Resp e₂) : Prop :=
  ∃ l, m.linked.find? (·.name == LinkCall.name e₁) = some l ∧
    (a₁ : Option Value) = l.sem (LinkCall.args e₁) ∧
    ∀ v, (a₁ : Option Value) = some v → ∃ s', (a₂ : Option AState) = some s' ∧
      l.post (KCall.entry e₂) s' ∧ l.layout.ResultOf (KCall.entry e₂) s' v ∧
      ∀ a, (l.contract.pre a).holds (KCall.entry e₂) →
        (l.contract.post a).holds s' ∧
        SepLogic.Footprinted.AgreeOn (l.contract.writes a (KCall.entry e₂))ᶜ
          (KCall.entry e₂) s'

/-- The answer relation of the separation contracts implies `contractRA`. -/
theorem contractRA_of_contractRAC {m : HaxModule} {e₁ : linkSig.Event}
    {e₂ : (kSig AState).Event} {a₁ : linkSig.Resp e₁} {a₂ : (kSig AState).Resp e₂}
    (h : contractRAC m e₁ e₂ a₁ a₂) : contractRA m e₁ e₂ a₁ a₂ := by
  obtain ⟨l, hl, hsem, hv⟩ := h
  refine ⟨l, hl, hsem, fun v hav => ?_⟩
  obtain ⟨s', hs', hpost, hres, -⟩ := hv v hav
  exact ⟨s', hs', hpost, hres⟩

/-- A target handler meets the separation contracts of the linked functions of `m`: at related
    events, the source handler of the meanings and the target handler give answers related by
    `contractRAC`. -/
def HandlerMeetsC (m : HaxModule) (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) :
    Prop :=
  ∀ e₁ e₂, contractRE m e₁ e₂ → contractRAC m e₁ e₂ (linkHandler m e₁) (h₂ e₂)

/-- A target handler meeting the separation contracts meets `HandlerMeets`. -/
theorem handlerMeets_of_handlerMeetsC {m : HaxModule}
    {h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e} (h : HandlerMeetsC m h₂) :
    HandlerMeets m h₂ :=
  fun e₁ e₂ he => contractRA_of_contractRAC (h e₁ e₂ he)

/-- **The call trees of `compileA` related up to the separation contracts.** The statement
    `R3Statement` with `RuttS` at the source handler `linkHandler m` in place of `Rutt` and the
    answer relation `contractRAC` in place of `contractRA`: on a module whose linked functions
    are linked kernels with distinct names, the bytes of `compileA` decode to a calling body
    `pc` followed by the region `Q` of the kernel blocks, with a symbol map `sym` of its call
    targets, such that from every entry state satisfying `σ.Regions` and every source
    environment `σ` reads off it, the source call tree of the entry is related, at some target
    fuel, to the target call tree of `pc`. -/
def R3StatementC : Prop :=
  ∀ (m : HaxModule) (σ : AbiLayout) (fname : String) (P : VIR.JasminLprogExport.Lprog)
    (bytes : List (BitVec 8)), compileA m σ fname = some (P, bytes) →
    (m.linked.map (·.name)).Nodup → (∀ l ∈ m.linked, RegionLinkCall.LinkedKernel l) →
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      X86Backend.LprogBytesDecode.decodeLprog bytes =
          some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel, ∃ fuelT,
          RuttS (linkHandler m) (contractRE m) (contractRAC m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (targetTree aMachine pc sym (linkRead m) fuelT 0 sa)

/-- **The consequence of the corrected statement**: from source and target trees related by
    `RuttS` at the separation contracts, under every target handler meeting them, a source run
    of the call tree under the meanings of the linked functions to a value that is not a
    control-flow value is read back by `σ` from the leaf of the target tree under the
    handler. -/
theorem r3c_consequence (m : HaxModule) (σ : AbiLayout) (sa : AState)
    (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) (hh : HandlerMeetsC m h₂)
    {t₁ : CallTree linkSig (Outcome × Env)} {t₂ : CallTree (kSig AState) (Option AState)}
    (hr : RuttS (linkHandler m) (contractRE m) (contractRAC m) (resRel σ sa) srcFail t₁ t₂)
    {v : Value} {env' : Env} (hv : interp (linkHandler m) t₁ = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ s', interp h₂ t₂ = some s' ∧ σ.ResultOf sa s' v := by
  rcases interp_ruttS h₂ hh hr with hf | hR
  · rw [hv] at hf
    have := hf v rfl
    rw [hcf] at this
    exact absurd this (by simp)
  · exact hR v (by rw [hv]) hcf

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract
