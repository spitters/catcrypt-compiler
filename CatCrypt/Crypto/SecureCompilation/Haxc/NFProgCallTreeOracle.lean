/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts
public import CatCryptCore.Relational.Rules

/-!
# The call trees of `compileA` at oracle contexts

`R3StatementFG` relates the source call tree of a module to the target trees of its calling body
at the answer relation `contractRAC`, which fixes the source answer of a call of a linked function
`l` to its meaning `l.sem args`, and at a skip clause that continues a skipped source event at the
answer of the meanings `linkHandler m`. This module states the relation at an answer predicate
`A` of the linked functions: the answer relation `contractRACA A m` asks `A l e a` of the source
answer in place of the equation, and the tree relation `RuttFA` continues a skipped source event
at every answer the skip predicate `SkipAns A m` admits. At the meaning predicate `SemAns` the
statement is `R3StatementFG` (`r3StatementFA_sem_iff`); at the typing predicate `TypedAns`, an
answer that decodes at the result type of the linked function, it is the statement at oracle
contexts, and it implies `R3StatementFG` (`r3StatementFG_of_r3StatementFA_typed`).

Under a pure source handler whose answers satisfy the skip predicate and a target handler meeting
the contracts at `A`, a source run to a value is read back from a target run (`r3fa_consequence`).
For a source handler in `SPComp`, a skipped event whose computation is discardable,
`c.bind (fun _ => k) = k`, is removed at every relation of the heaps (`rHoare_discard_bind_left`).

## Main definitions

* `SemAns`, `TypedAns`: the meaning and the typing predicates of the answers of a linked function.
* `contractRACA`, `SkipAns`: the answer relation of the separation contracts and the skip
  predicate at an answer predicate.
* `RuttFA`: `RuttF` with skipped source events continued at every answer of a skip predicate.
* `R3StatementFA`: the call trees of `compileA` related by `RuttFA` at an answer predicate.
* `HandlerMeetsCA`: a target handler meeting the separation contracts at an answer predicate.
* `Discardable`: a computation that can be removed in front of every computation.

## Main results

* `ruttFA_iff_ruttF`: at the answers of a pure handler, `RuttFA` is `RuttF`.
* `r3StatementFA_sem_iff`, `r3StatementFA_mono`, `r3StatementFG_of_r3StatementFA_typed`: the
  meaning instance, monotonicity in the predicate, and the oracle statement implies
  `R3StatementFG`.
* `r3fa_consequence`: the read-back of a source run under a pure oracle handler.
* `rHoare_discard_bind_left`: a discardable computation on the left is removed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts (R3StatementFG)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open _root_.Hax

/-! ## Answer predicates -/

/-- A predicate on the answers of a linked function at a call event. -/
abbrev AnsPred : Type := LinkedFn → (e : linkSig.Event) → linkSig.Resp e → Prop

/-- **The meaning predicate**: the answer is the meaning of the linked function at the arguments
    of the call. -/
def SemAns : AnsPred := fun l e a => (a : Option Value) = l.sem (LinkCall.args e)

/-- **The typing predicate**: a value answer decodes at the result type of the linked function. -/
def TypedAns : AnsPred := fun l _ a =>
  ∀ v, (a : Option Value) = some v → (CatCrypt.Crypto.Hax.ImpToNF.dec l.res v).isSome

/-- An answer that is the meaning is typed. -/
theorem typedAns_of_semAns {l : LinkedFn} {e : linkSig.Event} {a : linkSig.Resp e}
    (h : SemAns l e a) : TypedAns l e a := by
  intro v hv
  exact l.sem_res _ v (by rw [← hv]; exact h.symm)

/-- **The answer relation of the separation contracts at an answer predicate** `A`: the relation
    `contractRAC` with `A l e₁ a₁` in place of the equation of the source answer with the
    meaning. -/
def contractRACA (A : AnsPred) (m : HaxModule) (e₁ : linkSig.Event) (e₂ : (kSig AState).Event)
    (a₁ : linkSig.Resp e₁) (a₂ : (kSig AState).Resp e₂) : Prop :=
  ∃ l, m.linked.find? (·.name == LinkCall.name e₁) = some l ∧ A l e₁ a₁ ∧
    ∀ v, (a₁ : Option Value) = some v → ∃ s', (a₂ : Option AState) = some s' ∧
      l.post (KCall.entry e₂) s' ∧ l.layout.ResultOf (KCall.entry e₂) s' v ∧
      ∀ a, (l.contract.pre a).holds (KCall.entry e₂) →
        (l.contract.post a).holds s' ∧
        SepLogic.Footprinted.AgreeOn (l.contract.writes a (KCall.entry e₂))ᶜ
          (KCall.entry e₂) s'

/-- `contractRACA` is antitone in the answer predicate. -/
theorem contractRACA_mono {A A' : AnsPred} (hA : ∀ l e a, A l e a → A' l e a) {m : HaxModule}
    {e₁ : linkSig.Event} {e₂ : (kSig AState).Event} {a₁ : linkSig.Resp e₁}
    {a₂ : (kSig AState).Resp e₂} (h : contractRACA A m e₁ e₂ a₁ a₂) :
    contractRACA A' m e₁ e₂ a₁ a₂ := by
  obtain ⟨l, hl, ha, hv⟩ := h
  exact ⟨l, hl, hA _ _ _ ha, hv⟩

/-- **The skip predicate at an answer predicate** `A`: at a call of a linked function `l` of `m`,
    the answers satisfying `A l`; at a call of another name, the answer `none`. -/
def SkipAns (A : AnsPred) (m : HaxModule) (e : linkSig.Event) (a : linkSig.Resp e) : Prop :=
  match m.linked.find? (·.name == LinkCall.name e) with
  | some l => A l e a
  | none => (a : Option Value) = none

/-- `SkipAns` is monotone in the answer predicate. -/
theorem skipAns_mono {A A' : AnsPred} (hA : ∀ l e a, A l e a → A' l e a) {m : HaxModule}
    {e : linkSig.Event} {a : linkSig.Resp e} (h : SkipAns A m e a) : SkipAns A' m e a := by
  unfold SkipAns at *
  split at h <;> grind

/-- At the meaning predicate, the skip predicate admits exactly the answer of the meanings. -/
theorem skipAns_sem_iff {m : HaxModule} {e : linkSig.Event} {a : linkSig.Resp e} :
    SkipAns SemAns m e a ↔ a = linkHandler m e := by
  unfold SkipAns SemAns linkHandler
  rcases hf : m.linked.find? (·.name == LinkCall.name e) with _ | l <;> simp only [hf]

/-! ## Related trees with skips at a predicate -/

/-- **A source call tree and a fuel family of target trees related with skips at a predicate**:
    the clauses of `RuttF`, with a skipped source event continued at every answer `a` that the
    skip predicate `Sk` admits. -/
inductive RuttFA {E₁ E₂ : EventSig} {R₁ R₂ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
    (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (RR : R₁ → R₂ → Prop) (Fail : R₁ → Prop) :
    CallTree E₁ R₁ → (Nat → CallTree E₂ R₂) → Prop
  | ret {r₁ : R₁} {r₂ : R₂} {T : Nat → CallTree E₂ R₂} (n : Nat) (hT : T n = .ret r₂)
      (h : RR r₁ r₂) : RuttFA Sk RE RA RR Fail (.ret r₁) T
  | fail {r₁ : R₁} {T : Nat → CallTree E₂ R₂} (h : Fail r₁) : RuttFA Sk RE RA RR Fail (.ret r₁) T
  | vis {e₁ : E₁.Event} {e₂ : E₂.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁}
      {T : Nat → CallTree E₂ R₂} {K : E₂.Resp e₂ → Nat → CallTree E₂ R₂} (n : Nat)
      (hT : ∀ m, T (n + m) = .vis e₂ fun a => K a m) (he : RE e₁ e₂)
      (hk : ∀ a₁ a₂, RA e₁ e₂ a₁ a₂ → RuttFA Sk RE RA RR Fail (k₁ a₁) (K a₂)) :
      RuttFA Sk RE RA RR Fail (.vis e₁ k₁) T
  | skip {e₁ : E₁.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂}
      (hk : ∀ a, Sk e₁ a → RuttFA Sk RE RA RR Fail (k₁ a) T) :
      RuttFA Sk RE RA RR Fail (.vis e₁ k₁) T

section RuttFA

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type}

/-- **`RuttFA` is monotone in the relations of events, leaves and failure and antitone in the
    skip predicate and the answer relation.** -/
theorem RuttFA.imp {Sk Sk' : (e : E₁.Event) → E₁.Resp e → Prop}
    {RE RE' : E₁.Event → E₂.Event → Prop}
    {RA RA' : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR RR' : R₁ → R₂ → Prop} {Fail Fail' : R₁ → Prop}
    (hS : ∀ e a, Sk' e a → Sk e a) (hE : ∀ e₁ e₂, RE e₁ e₂ → RE' e₁ e₂)
    (hA : ∀ e₁ e₂ a₁ a₂, RE e₁ e₂ → RA' e₁ e₂ a₁ a₂ → RA e₁ e₂ a₁ a₂)
    (hR : ∀ r₁ r₂, RR r₁ r₂ → RR' r₁ r₂) (hF : ∀ r₁, Fail r₁ → Fail' r₁)
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂} (h : RuttFA Sk RE RA RR Fail t₁ T) :
    RuttFA Sk' RE' RA' RR' Fail' t₁ T := by
  induction h with
  | ret n hT h => exact .ret n hT (hR _ _ h)
  | fail h => exact .fail (hF _ h)
  | vis n hT he _ ih => exact .vis n hT (hE _ _ he) fun a₁ a₂ ha => ih a₁ a₂ (hA _ _ _ _ he ha)
  | skip _ ih => exact .skip fun a ha => ih a (hS _ _ ha)

/-- **At the answers of a pure handler, `RuttFA` is `RuttF`.** -/
theorem ruttFA_iff_ruttF {h₁ : ∀ e : E₁.Event, E₁.Resp e} {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ R₁}
    {T : Nat → CallTree E₂ R₂} :
    RuttFA (fun e a => a = h₁ e) RE RA RR Fail t₁ T ↔ RuttF h₁ RE RA RR Fail t₁ T := by
  constructor
  · intro h
    induction h with
    | ret n hT h => exact .ret n hT h
    | fail h => exact .fail h
    | vis n hT he _ ih => exact .vis n hT he ih
    | skip _ ih => exact .skip (ih _ rfl)
  · intro h
    induction h with
    | ret n hT h => exact .ret n hT h
    | fail h => exact .fail h
    | vis n hT he _ ih => exact .vis n hT he ih
    | skip _ ih => exact .skip fun a ha => ha ▸ ih

/-- **Interpretation under a pure handler whose answers satisfy the skip predicate**: under a
    target handler whose answers at related events are related to those of the source handler,
    a source tree and a family related by `RuttFA` interpret to a failed source leaf or to
    related leaves at some fuel of the family. -/
theorem interp_ruttFA {Sk : (e : E₁.Event) → E₁.Resp e → Prop}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (h₁ : ∀ e : E₁.Event, E₁.Resp e) (h₂ : ∀ e : E₂.Event, E₂.Resp e)
    (hS : ∀ e, Sk e (h₁ e)) (hh : ∀ e₁ e₂, RE e₁ e₂ → RA e₁ e₂ (h₁ e₁) (h₂ e₂))
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂} (h : RuttFA Sk RE RA RR Fail t₁ T) :
    Fail (interp h₁ t₁) ∨ ∃ n, RR (interp h₁ t₁) (interp h₂ (T n)) :=
  NFProgCallTreeCalls.interp_ruttF h₂ hh (ruttFA_iff_ruttF.mp
    (h.imp (fun e _ ha => ha ▸ hS e) (fun _ _ he => he) (fun _ _ _ _ _ ha => ha)
      (fun _ _ hr => hr) (fun _ hf => hf)))

end RuttFA

/-! ## The statement at an answer predicate -/

/-- **The call trees of `compileA` related at an answer predicate** `A`: the statement
    `R3StatementFG` with the answer relation `contractRACA A m` and skipped source events
    continued at every answer of `SkipAns A m`. At `TypedAns` it is the statement at oracle
    contexts. -/
def R3StatementFA (A : AnsPred) : Prop :=
  ∀ (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)), compileA m σ fname = some (P, bytes) →
    (m.linked.map (·.name)).Nodup → (∀ l ∈ m.linked, LinkedKernel l) →
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      X86Backend.LprogBytesDecode.decodeLprog bytes =
          some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttFA (SkipAns A m) (contractREG m) (contractRACA A m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa)

/-- **`R3StatementFA` is antitone in the answer predicate**: a statement at a larger predicate
    implies the statement at a smaller one. -/
theorem r3StatementFA_mono {A A' : AnsPred} (hA : ∀ l e a, A' l e a → A l e a)
    (h : R3StatementFA A) : R3StatementFA A' := by
  intro m σ fname P bytes hc hnd hk
  obtain ⟨pc, Q, sym, hd, hrel⟩ := h m σ fname P bytes hc hnd hk
  exact ⟨pc, Q, sym, hd, fun sa hreg env henv fuelC fuel =>
    (hrel sa hreg env henv fuelC fuel).imp (fun _ _ ha => skipAns_mono hA ha)
      (fun _ _ he => he) (fun _ _ _ _ _ ha => contractRACA_mono hA ha)
      (fun _ _ hr => hr) (fun _ hf => hf)⟩

/-- **At the meaning predicate, the statement is `R3StatementFG`.** -/
theorem r3StatementFA_sem_iff : R3StatementFA SemAns ↔ R3StatementFG := by
  constructor
  · intro h m σ fname P bytes hc hnd hk
    obtain ⟨pc, Q, sym, hd, hrel⟩ := h m σ fname P bytes hc hnd hk
    exact ⟨pc, Q, sym, hd, fun sa hreg env henv fuelC fuel =>
      ruttFA_iff_ruttF.mp ((hrel sa hreg env henv fuelC fuel).imp
        (fun _ _ ha => skipAns_sem_iff.mpr ha) (fun _ _ he => he)
        (fun _ _ _ _ _ ha => ha) (fun _ _ hr => hr) (fun _ hf => hf))⟩
  · intro h m σ fname P bytes hc hnd hk
    obtain ⟨pc, Q, sym, hd, hrel⟩ := h m σ fname P bytes hc hnd hk
    exact ⟨pc, Q, sym, hd, fun sa hreg env henv fuelC fuel =>
      (ruttFA_iff_ruttF.mpr (hrel sa hreg env henv fuelC fuel)).imp
        (fun _ _ ha => skipAns_sem_iff.mp ha) (fun _ _ he => he)
        (fun _ _ _ _ _ ha => ha) (fun _ _ hr => hr) (fun _ hf => hf)⟩

/-- **The statement at oracle contexts implies `R3StatementFG`.** -/
theorem r3StatementFG_of_r3StatementFA_typed (h : R3StatementFA TypedAns) : R3StatementFG :=
  r3StatementFA_sem_iff.mp (r3StatementFA_mono (fun _ _ _ ha => typedAns_of_semAns ha) h)

/-- A target handler meets the separation contracts at the answer predicate `A` against the pure
    source handler `hS`: at events related by `contractREG`, the answers are related by
    `contractRACA A m`. -/
def HandlerMeetsCA (A : AnsPred) (m : HaxModule) (hS : ∀ e : linkSig.Event, linkSig.Resp e)
    (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) : Prop :=
  ∀ e₁ e₂, contractREG m e₁ e₂ → contractRACA A m e₁ e₂ (hS e₁) (h₂ e₂)

/-- **The consequence at a pure oracle handler.** Let a source tree and the target family be
    related by `RuttFA` at the skip predicate and the separation contracts at `A`, the answers of
    the source handler `hS` satisfy the skip predicate, and the target handler meet the contracts
    at `A` against `hS`. A source run under `hS` to a value that is not a control-flow value is
    read back by `σ` from the leaf of the target family at some fuel. -/
theorem r3fa_consequence {A : AnsPred} (m : HaxModule) (σ : AbiLayout) (sa : AState)
    (hS : ∀ e : linkSig.Event, linkSig.Resp e)
    (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e)
    (hsk : ∀ e, SkipAns A m e (hS e)) (hh : HandlerMeetsCA A m hS h₂)
    {t₁ : CallTree linkSig (Outcome × Env)} {T : Nat → CallTree (kSig AState) (Option AState)}
    (hr : RuttFA (SkipAns A m) (contractREG m) (contractRACA A m) (resRel σ sa) srcFail t₁ T)
    {v : Value} {env' : Env} (hv : interp hS t₁ = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ fuelT s', interp h₂ (T fuelT) = some s' ∧ σ.ResultOf sa s' v := by
  rcases interp_ruttFA hS h₂ hsk hh hr with hf | ⟨n, hR⟩
  · rw [hv] at hf
    have := hf v rfl
    rw [hcf] at this
    exact absurd this (by simp)
  · obtain ⟨s', hs', hres⟩ := hR v (by rw [hv]) hcf
    exact ⟨n, s', hs', hres⟩

/-! ## Discardable source computations -/

/-- **A discardable computation**: sequencing it in front of any computation and discarding its
    result gives that computation. -/
def Discardable {α : Type} (c : SPComp α) : Prop :=
  ∀ (β : Type) (k : SPComp β), c.bind (fun _ => k) = k

/-- A discardable computation keeps the heap and does not fail: every outcome of nonzero weight
    from the heap `s` has the final heap `s`, and the failure weight is zero. -/
theorem Discardable.heap_and_noFail {α : Type} {c : SPComp α} (hd : Discardable c) (s : Heap) :
    (∀ a s', c s (some (a, s')) ≠ 0 → s' = s) ∧ c s none = 0 := by
  have h := congrFun (hd Heap fun s => SDistr.pure (s, s)) s
  change SDistr.bind (c s) (fun p : α × Heap => SDistr.pure (p.2, p.2)) = SDistr.pure (s, s) at h
  have hmem : ∀ o, o ∈ PMF.support (SDistr.bind (c s) fun p : α × Heap =>
      SDistr.pure (p.2, p.2)) → o = some (s, s) := by
    intro o ho
    rw [h] at ho
    simpa [SDistr.pure] using ho
  refine ⟨fun a s' ha => ?_, ?_⟩
  · have := hmem (some (s', s')) (by
      unfold SDistr.bind
      rw [PMF.mem_support_bind_iff]
      exact ⟨some (a, s'), (PMF.mem_support_iff _ _).mpr ha, by simp [SDistr.pure]⟩)
    simpa using this
  · by_contra hn
    have := hmem none (by
      unfold SDistr.bind
      rw [PMF.mem_support_bind_iff]
      exact ⟨none, (PMF.mem_support_iff _ _).mpr hn, by simp⟩)
    simp at this

/-- **A discardable computation on the left is removed**, at every relation `I` of the heaps:
    when every answer of nonzero weight of `c` satisfies `P` and the continuation at every answer
    satisfying `P` is related to `d`, the sequence `c.bind f` is related to `d`. -/
theorem rHoare_discard_bind_left {α β γ : Type} {I : RPre} {c : SPComp α} {P : α → Prop}
    (hd : Discardable c) (hP : ∀ s a s', c s (some (a, s')) ≠ 0 → P a)
    {f : α → SPComp β} {d : SPComp γ} {Q : RPost β γ}
    (hf : ∀ a, P a → rHoare I (f a) d Q) : rHoare I (c.bind f) d Q := by
  have hc : rHoare I c (SPComp.pure ()) (fun a s₁ _ s₂ => P a ∧ I s₁ s₂) := by
    intro s₁ s₂ hI
    obtain ⟨hs, hn⟩ := hd.heap_and_noFail s₁
    refine ⟨Coupling.prod _ _ (by simp [SDistr.mass, hn]) (SDistr.mass_pure _), ?_⟩
    intro p₁ p₂ hp
    have h1 := Coupling.in_left_support _ hp
    have h2 := Coupling.in_right_support _ hp
    have hp2 : p₂ = ((), s₂) := by
      classical
      simpa [SPComp.pure, SDistr.pure, PMF.pure_apply, eq_comm] using h2
    refine ⟨hP s₁ p₁.1 p₁.2 h1, ?_⟩
    rw [hp2, hs p₁.1 p₁.2 h1]
    exact hI
  have h := rHoare_bind (f₂ := fun _ => d) hc fun a _ s₁ s₂ hΨ => hf a hΨ.1 s₁ s₂ hΨ.2
  rwa [SPComp.pure_bind] at h

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
