/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeBack
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract

/-!
# Call trees related at a target fuel chosen per segment

`RegionLinkContract.R3StatementC` relates the source call tree of a module entry to the target
call tree `targetTree` of the calling body at one target fuel `fuelT`, chosen before the
relation `RuttS` quantifies over the answers of the calls. The target tree consumes fuel at
every step, so this fuel bounds the steps of the calling body along every sequence of answers
related by the contracts. The correctness proofs of the back half give halting runs (`Halts`,
`HaltsO`), one per answer sequence, whose length is not bounded uniformly in the answers: a
uniform bound needs a count of the steps of the calling body that depends on the source fuel
only, which those proofs do not carry.

This module states the relation with the target fuel chosen per segment of the target tree, the
part of a run between two calls. `RuttF` relates a source tree to a family of target trees
indexed by fuel: a target leaf is reached at some fuel, and a target event is reached at some
fuel `n` from which the family is that event followed, at each answer, by a family of its own.
The answer sequence then fixes the fuel of each segment, and the target fuel of a whole run is
their sum. The family of `targetTree` at the fuels has this shape (`targetTree_vis_family`), a
relation by `RuttS` at one fuel gives a relation by `RuttF` (`ruttF_of_ruttS_targetTree`), so
`R3StatementF`, the statement `R3StatementC` with `RuttF` in place of `RuttS` at one fuel, is
implied by it (`r3StatementF_of_r3StatementC`) and gives the same consequence under a target
handler meeting the separation contracts (`r3f_consequence`), at a target fuel that depends on
the handler.

## Main definitions

* `RuttF`: a source call tree and a fuel-indexed family of target call trees related up to
  relations on events, answers and leaves, with source events that the target skips.
* `IsTargetFamily`: the families of the target trees of a decoded program from a fixed index
  and state, and the constant family of the leaf `none`.
* `R3StatementF`: the call trees of `compileA` related by `RuttF` at the separation contracts.

## Main results

* `interp_ruttF`: under related handlers, a source tree and a family related by `RuttF`
  interpret to a failed source leaf or, at some fuel, to related leaves.
* `RuttS.trans_ruttF`: a relation by `RuttS` followed by a relation by `RuttF` composes.
* `targetTree_vis_family`: an event of the target tree at a fuel is the event of the target
  family from some fuel on, its continuation a target family.
* `ruttF_of_ruttS_targetTree`: a relation by `RuttS` with the target tree at one fuel is a
  relation by `RuttF` with the family of the target trees.
* `r3StatementF_of_r3StatementC`, `r3f_consequence`: the corrected statement follows from the
  statement at one fuel, and gives a target run reading back every source value under a target
  handler meeting the separation contracts.
* `ruttF_compileRegion_callFree`: the back half on a program without `call` in the form of
  `RuttF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA RuttS.trans)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr callOps retOps)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax (HaxModule)
open _root_.Hax
open _root_.Hax.InlineLocalClosures

/-! ## Trees related to a family of trees indexed by fuel -/

/-- **A source tree and a fuel-indexed family of target trees related, with skipped source
    events.** A source leaf related by `RR` to the leaf of the family at some fuel; a failed
    source leaf; a source event related by `RE` to an event `e₂` that the family performs from
    some fuel `n` on, the family at `n + m` continuing at each answer `a` with the family
    `K a` at `m`, the source continuations related to these families at answers related by
    `RA`; or a source event that the target does not perform, its continuation taken at the
    answer of the source handler. -/
inductive RuttF {E₁ E₂ : EventSig} {R₁ R₂ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
    (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (RR : R₁ → R₂ → Prop) (Fail : R₁ → Prop) :
    CallTree E₁ R₁ → (Nat → CallTree E₂ R₂) → Prop
  | ret {r₁ : R₁} {r₂ : R₂} {T : Nat → CallTree E₂ R₂} (n : Nat) (hT : T n = .ret r₂)
      (h : RR r₁ r₂) : RuttF h₁ RE RA RR Fail (.ret r₁) T
  | fail {r₁ : R₁} {T : Nat → CallTree E₂ R₂} (h : Fail r₁) : RuttF h₁ RE RA RR Fail (.ret r₁) T
  | vis {e₁ : E₁.Event} {e₂ : E₂.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁}
      {T : Nat → CallTree E₂ R₂} {K : E₂.Resp e₂ → Nat → CallTree E₂ R₂} (n : Nat)
      (hT : ∀ m, T (n + m) = .vis e₂ fun a => K a m) (he : RE e₁ e₂)
      (hk : ∀ a₁ a₂, RA e₁ e₂ a₁ a₂ → RuttF h₁ RE RA RR Fail (k₁ a₁) (K a₂)) :
      RuttF h₁ RE RA RR Fail (.vis e₁ k₁) T
  | skip {e₁ : E₁.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂}
      (hk : RuttF h₁ RE RA RR Fail (k₁ (h₁ e₁)) T) : RuttF h₁ RE RA RR Fail (.vis e₁ k₁) T

section RuttF

variable {E₀ E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
  {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}

/-- **Interpretation of a tree and a related family**: under a target handler whose answers at
    related events are related to those of the source handler, a source tree and a family
    related by `RuttF` interpret to a failed source leaf, or to related leaves at some fuel of
    the family. -/
theorem interp_ruttF (h₂ : ∀ e : E₂.Event, E₂.Resp e)
    (hh : ∀ e₁ e₂, RE e₁ e₂ → RA e₁ e₂ (h₁ e₁) (h₂ e₂))
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂} (h : RuttF h₁ RE RA RR Fail t₁ T) :
    Fail (interp h₁ t₁) ∨ ∃ n, RR (interp h₁ t₁) (interp h₂ (T n)) := by
  induction h with
  | ret n hT h => exact .inr ⟨n, by rw [hT]; exact h⟩
  | fail h => exact .inl h
  | @vis e₁ e₂ k₁ T K n hT he _ ih =>
    rcases ih _ _ (hh _ _ he) with hf | ⟨m, hm⟩
    · exact .inl hf
    · exact .inr ⟨n + m, by rw [hT m]; exact hm⟩
  | skip _ ih => exact ih

/-- `RuttF` is monotone in the relation of the leaves. -/
theorem RuttF.mono {RR' : R₁ → R₂ → Prop} (hR : ∀ a b, RR a b → RR' a b)
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂} (h : RuttF h₁ RE RA RR Fail t₁ T) :
    RuttF h₁ RE RA RR' Fail t₁ T := by
  induction h with
  | ret n hT h => exact .ret n hT (hR _ _ h)
  | fail h => exact .fail h
  | vis n hT he _ ih => exact .vis n hT he ih
  | skip _ ih => exact .skip ih

/-- **A relation of trees followed by a relation with a family composes.** Under the
    hypotheses of `RuttS.trans`, `RuttS h₀ RE₁ RA₁ RR₁ F t₀ t₁` and
    `RuttF h₁ RE₂ RA₂ RR₂ F' t₁ T` give the relation of `t₀` and `T` at the compositions of the
    relations. -/
theorem RuttS.trans_ruttF {R₀ : Type} {h₀ : ∀ e : E₀.Event, E₀.Resp e}
    {RE₁ : E₀.Event → E₁.Event → Prop}
    {RA₁ : (e₀ : E₀.Event) → (e₁ : E₁.Event) → E₀.Resp e₀ → E₁.Resp e₁ → Prop}
    {RR₁ : R₀ → R₁ → Prop} {F : R₀ → Prop}
    (hh : ∀ e₀ e₁, RE₁ e₀ e₁ → RA₁ e₀ e₁ (h₀ e₀) (h₁ e₁))
    (hF : ∀ r₀ r₁, RR₁ r₀ r₁ → Fail r₁ → F r₀)
    {t₀ : CallTree E₀ R₀} {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂}
    (h01 : RuttS h₀ RE₁ RA₁ RR₁ F t₀ t₁) (h12 : RuttF h₁ RE RA RR Fail t₁ T) :
    RuttF h₀ (CompRE RE₁ RE) (CompRA RE₁ RE RA₁ RA) (Relation.Comp RR₁ RR) F t₀ T := by
  induction h01 generalizing T with
  | ret h =>
    cases h12 with
    | ret n hT h' => exact .ret n hT ⟨_, h, h'⟩
    | fail h' => exact .fail (hF _ _ h h')
  | fail h => exact .fail h
  | @vis e₀ e₁ k₀ k₁ he _ ih =>
    cases h12 with
    | vis n hT he' hk' =>
      refine .vis n hT ⟨e₁, he, he'⟩ fun a₀ a₂ ha => ?_
      obtain ⟨a₁, ha₁, ha₂⟩ := ha e₁ he he'
      exact ih a₀ a₁ ha₁ (hk' a₁ a₂ ha₂)
    | skip hk' => exact .skip (ih _ _ (hh _ _ he) hk')
  | skip _ ih => exact .skip (ih h12)

end RuttF

/-! ## The family of the target trees -/

section Target

variable {σ : Type} (M : Machine σ) (prog : List RInstr) (sym : Nat → String)
  (rd : String → σ → List Value)

/-- The continuation family of a target call at the index `pc`: at the answer `some sc`, the
    target trees from the next index on the state after the return; at `none`, the leaf
    `none`. -/
def contFamily (pc : Nat) (r : Option σ) (m : Nat) : CallTree (kSig σ) (Option σ) :=
  match r with
  | some sc => targetTree M prog sym rd m (pc + 1) (retOps.foldl M.exec sc)
  | none => .ret none

/-- **The target families**: the target trees of `prog` from a fixed index and state, indexed
    by the fuel, and the constant family of the leaf `none`. -/
def IsTargetFamily (T : Nat → CallTree (kSig σ) (Option σ)) : Prop :=
  (∃ pc s, T = fun n => targetTree M prog sym rd n pc s) ∨ T = fun _ => .ret none

/-- The continuation family of a call is a target family. -/
theorem isTargetFamily_contFamily (pc : Nat) (r : Option σ) :
    IsTargetFamily M prog sym rd (contFamily M prog sym rd pc r) := by
  cases r with
  | some sc => exact .inl ⟨pc + 1, retOps.foldl M.exec sc, rfl⟩
  | none => exact .inr rfl

/-- **An event of the target tree is an event of its family from some fuel on.** If the
    target tree at the fuel `F` from `pc` and `s` is the event `e₂` with the continuation
    `k₂`, there is a fuel `n` from which the target trees are `e₂` followed by a continuation
    family, `k₂` is that family at the fuel `F - n`, and each continuation family is a target
    family. -/
theorem targetTree_vis_family {e₂ : (kSig σ).Event}
    {k₂ : (kSig σ).Resp e₂ → CallTree (kSig σ) (Option σ)} :
    ∀ (F pc : Nat) (s : σ), targetTree M prog sym rd F pc s = .vis e₂ k₂ →
      ∃ (n F' : Nat) (K : (kSig σ).Resp e₂ → Nat → CallTree (kSig σ) (Option σ)),
        (∀ m, targetTree M prog sym rd (n + m) pc s = .vis e₂ fun a => K a m)
        ∧ (∀ a, IsTargetFamily M prog sym rd (K a)) ∧ k₂ = fun a => K a F' := by
  intro F
  induction F with
  | zero => intro pc s h; simp [targetTree] at h
  | succ F ih =>
    intro pc s h
    simp only [targetTree] at h
    split at h
    · rename_i t hpc
      simp only [CallTree.vis.injEq] at h
      obtain ⟨rfl, hk⟩ := h
      refine ⟨1, F, contFamily M prog sym rd pc, fun m => ?_,
        isTargetFamily_contFamily M prog sym rd pc, ?_⟩
      · rw [Nat.add_comm]
        simp only [targetTree, hpc]
        congr 1
      · funext r
        rw [← eq_of_heq hk]
        cases r <;> rfl
    · rename_i hpc
      split at h
      · cases h
      · cases h
      · rename_i pc' s' hs
        obtain ⟨n, F', K, hK, hKf, hk⟩ := ih pc' s' h
        refine ⟨n + 1, F', K, fun m => ?_, hKf, hk⟩
        rw [show n + 1 + m = (n + m) + 1 by omega]
        have hstep : targetTree M prog sym rd (n + m + 1) pc s =
            targetTree M prog sym rd (n + m) pc' s' := by
          simp only [targetTree]
          split <;> simp_all
        rw [hstep]
        exact hK m

/-- **A path of steps is a prefix of every target tree with enough fuel.** A path of `step`s
    from `pc` and `s` to `pc'` and `s'` (which passes no `call`, at which `step` is stuck) has
    a length `j` such that the target tree at the fuel `j + m` from `pc` and `s` is the target
    tree at `m` from `pc'` and `s'`. -/
theorem targetTree_of_reaches {pc pc' : Nat} {s s' : σ} (h : Reaches M prog pc s pc' s') :
    ∃ j, ∀ m, targetTree M prog sym rd (j + m) pc s = targetTree M prog sym rd m pc' s' := by
  induction h with
  | refl => exact ⟨0, fun m => by rw [Nat.zero_add]⟩
  | @next pc s pc₁ s₁ pc₂ s₂ hs _ ih =>
    obtain ⟨j, hj⟩ := ih
    refine ⟨j + 1, fun m => ?_⟩
    rw [show j + 1 + m = (j + m) + 1 by omega]
    simp only [targetTree]
    split
    · rename_i t ht
      simp [step, ht] at hs
    · rw [hs]
      exact hj m

/-- **A halting path without call is a leaf of every target tree with enough fuel.** -/
theorem targetTree_of_haltsNoCall {pc : Nat} {s s' : σ} (h : HaltsNoCall M prog pc s s') :
    ∃ n, ∀ m, targetTree M prog sym rd (n + m) pc s = .ret (some s') := by
  obtain ⟨pc', hr, hret⟩ := h
  obtain ⟨j, hj⟩ := targetTree_of_reaches M prog sym rd hr
  refine ⟨j + 1, fun m => ?_⟩
  rw [show j + 1 + m = j + (m + 1) by omega, hj]
  simp [targetTree, hret, step]

/-- **A path to a `call` is the event of the call in every target tree with enough fuel**: a
    path of steps from `pc` and `s` to an index `pc'` holding `call t`, in the state `s'`, has a
    fuel `n` from which the target tree from `pc` and `s` is the linked call of `sym t` at the
    entry state after the stack operations of the call, continued by the continuation family
    of the call at `pc'`. -/
theorem targetTree_of_reaches_call {pc pc' t : Nat} {s s' : σ}
    (h : Reaches M prog pc s pc' s') (hc : prog[pc']? = some (.call t)) :
    ∃ n, ∀ m, targetTree M prog sym rd (n + m) pc s =
      .vis (⟨⟨sym t, rd (sym t) ((callOps (pc' + 1)).foldl M.exec s')⟩,
          (callOps (pc' + 1)).foldl M.exec s'⟩ : KCall σ)
        fun r => contFamily M prog sym rd pc' r m := by
  obtain ⟨j, hj⟩ := targetTree_of_reaches M prog sym rd h
  refine ⟨j + 1, fun m => ?_⟩
  rw [show j + 1 + m = j + (m + 1) by omega, hj]
  simp only [targetTree, hc]
  congr 1

/-- **A relation with the target tree at one fuel is a relation with its family.** A source
    tree related by `RuttS` to the tree of a target family at some fuel is related by `RuttF`
    to the family. -/
theorem ruttF_of_ruttS_targetFamily {E₁ : EventSig} {R₁ : Type}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e} {RE : E₁.Event → (kSig σ).Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : (kSig σ).Event) → E₁.Resp e₁ → (kSig σ).Resp e₂ → Prop}
    {RR : R₁ → Option σ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ R₁}
    {t₂ : CallTree (kSig σ) (Option σ)} (h : RuttS h₁ RE RA RR Fail t₁ t₂) :
    ∀ (T : Nat → CallTree (kSig σ) (Option σ)) (F : Nat), IsTargetFamily M prog sym rd T →
      T F = t₂ → RuttF h₁ RE RA RR Fail t₁ T := by
  induction h with
  | ret h => intro T F _ hF; exact .ret F hF h
  | fail h => intro _ _ _ _; exact .fail h
  | vis he _ ih =>
    intro T F hT hF
    rcases hT with ⟨pc, s, rfl⟩ | rfl
    · obtain ⟨n, F', K, hK, hKf, rfl⟩ := targetTree_vis_family M prog sym rd F pc s hF
      exact .vis n hK he fun a₁ a₂ ha => ih a₁ a₂ ha (K a₂) F' (hKf a₂) rfl
    · cases hF
  | skip _ ih => intro T F hT hF; exact .skip (ih T F hT hF)

/-- **A relation with the target tree at one fuel is a relation with the target trees at the
    fuels**, from the same index and state. -/
theorem ruttF_of_ruttS_targetTree {E₁ : EventSig} {R₁ : Type}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e} {RE : E₁.Event → (kSig σ).Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : (kSig σ).Event) → E₁.Resp e₁ → (kSig σ).Resp e₂ → Prop}
    {RR : R₁ → Option σ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ R₁} {F pc : Nat}
    {s : σ} (h : RuttS h₁ RE RA RR Fail t₁ (targetTree M prog sym rd F pc s)) :
    RuttF h₁ RE RA RR Fail t₁ fun n => targetTree M prog sym rd n pc s :=
  ruttF_of_ruttS_targetFamily M prog sym rd h _ F (.inl ⟨pc, s, rfl⟩) rfl

end Target

/-! ## The statement with the target fuel chosen per segment -/

/-- **The call trees of `compileA` related at a target fuel chosen per segment.** The statement
    `R3StatementC` with `RuttF`, at the family of the target trees of the calling body `pc` from
    index `0` and the entry state, in place of `RuttS` at one target fuel. -/
def R3StatementF : Prop :=
  ∀ (m : HaxModule) (σ : AbiLayout) (fname : String) (P : VIR.JasminLprogExport.Lprog)
    (bytes : List (BitVec 8)), compileA m σ fname = some (P, bytes) →
    (m.linked.map (·.name)).Nodup → (∀ l ∈ m.linked, RegionLinkCall.LinkedKernel l) →
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      X86Backend.LprogBytesDecode.decodeLprog bytes =
          some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttF (linkHandler m) (contractRE m) (contractRAC m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa)

/-- **The statement at one target fuel implies the statement at a fuel per segment.** -/
theorem r3StatementF_of_r3StatementC (h : R3StatementC) : R3StatementF := by
  intro m σ fname P bytes hc hnd hk
  obtain ⟨pc, Q, sym, hd, hrel⟩ := h m σ fname P bytes hc hnd hk
  refine ⟨pc, Q, sym, hd, fun sa hreg env henv fuelC fuel => ?_⟩
  obtain ⟨fuelT, hr⟩ := hrel sa hreg env henv fuelC fuel
  exact ruttF_of_ruttS_targetTree aMachine pc sym (linkRead m) hr

/-- **The consequence of the statement at a fuel per segment**: from a source tree and the
    target family related by `RuttF` at the separation contracts, under every target handler
    meeting them, a source run under the meanings of the linked functions to a value that is
    not a control-flow value is read back by `σ` from the leaf of the target family under the
    handler at some fuel. -/
theorem r3f_consequence (m : HaxModule) (σ : AbiLayout) (sa : AState)
    (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) (hh : HandlerMeetsC m h₂)
    {t₁ : CallTree linkSig (Outcome × Env)} {T : Nat → CallTree (kSig AState) (Option AState)}
    (hr : RuttF (linkHandler m) (contractRE m) (contractRAC m) (resRel σ sa) srcFail t₁ T)
    {v : Value} {env' : Env} (hv : interp (linkHandler m) t₁ = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ fuelT s', interp h₂ (T fuelT) = some s' ∧ σ.ResultOf sa s' v := by
  rcases interp_ruttF h₂ hh hr with hf | ⟨n, hR⟩
  · rw [hv] at hf
    have := hf v rfl
    rw [hcf] at this
    exact absurd this (by simp)
  · obtain ⟨s', hs', hres⟩ := hR v (by rw [hv]) hcf
    exact ⟨n, s', hs', hres⟩

/-! ## The back half on a program without `call` -/

section Back

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (OutRel)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeBack (ruttS_compileRegion_callFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open NarrowWords (wideTy)

/-- **The back half on a program without `call`, at a target fuel per segment.**
    `ruttS_compileRegion_callFree` with the target trees of the decoded program at the fuels. -/
theorem ruttF_compileRegion_callFree
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
    (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
      (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : VIR.JasminLprogExport.Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes))
    (hcf : p.callFree = true) {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnc : ∀ (i tg : Nat), prog[i]? ≠ some (RInstr.call tg))
    (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa (NarrowWords.mapVal V))
    (hreg : σ.Regions sa) (fuel : Nat) :
    RuttF h₁ RE RA
      (OutRel fun (v : Ctxt.Valuation (d := jasminDialect) [t]) (s' : AState) =>
        σ.ResultOf sa s' (denVal (wideTy t) (NarrowWords.transTy
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))))
      (fun o => o = none) (mfTree fuel p V)
      (fun fuelT => targetTree aMachine prog sym rd fuelT 0 sa) := by
  obtain ⟨fuelT, hr⟩ :=
    ruttS_compileRegion_callFree h₁ RE RA h hcf hd hnc sym rd sa V hV hreg fuel
  exact ruttF_of_ruttS_targetTree aMachine prog sym rd hr

end Back

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls
