/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Contract
public import Std.Do

/-!
# `Std.Do` triples over machine runs and their contracts

`RunM σ T := StateT (σ × T) Option` is the monad of runs over a machine state `σ` that
accumulate a trace `T` and may fail. Its `Std.Do` weakest precondition is the total-correctness
one: a triple `⦃fun st => ⌜P st⌝⦄ x ⦃⇓ a st => ⌜Q a st⌝⦄` says that from every state satisfying
`P` the run returns a value and a state satisfying `Q` (`triple_iff_run`).

`runRel x` is the run relation of `x` started on the empty trace, and `AppendOnly x` says that
starting `x` on a trace `t₀` prefixes `t₀` to the trace of the run from the empty trace.
`RunWritesIn x W` says that every run of `x` keeps the locations outside `W` of the entry state.

## Main definitions

* `VC.RunM`, `VC.runRel`, `VC.AppendOnly`, `VC.RunWritesIn`.

## Main results

* `VC.triple_iff_run`: a triple over `RunM` with pure assertions is a statement on `run`.
* `VC.triple_frame_conj`: the conjunctive frame rule; an assertion `F` whose footprint avoids
  the write set holds after the run when it holds before.
* `VC.sContract_of_triple`: a fuel-indexed program meets the contract given by its triples,
  a write set, and a trace that is a function of a public view of the entry state.
* `VC.runRel_seq`: the run relation of `x >>= fun _ => y` meets the sequenced contract
  `C₁.seq (runRel x) C₂`.
* `SContract.of_le_det`: a contract transfers to a deterministic run relation that contains
  the original one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

universe u v w x

open Footprinted

/-- **Transfer to a deterministic relation.** If every run of `X` is a run of `Y` and `Y`
    has at most one trace and final state from each entry state, then `Y` meets every
    contract that `X` meets. -/
theorem SContract.of_le_det {σ : Type u} {L : Type v} [Footprinted σ L] {T : Type w}
    {α : Type x} {X Y : σ → T → σ → Prop} {C : ContractSpec σ L α} (h : SContract X C)
    (hXY : ∀ s t s', X s t s' → Y s t s')
    (hdet : ∀ s t₁ s₁ t₂ s₂, Y s t₁ s₁ → Y s t₂ s₂ → t₁ = t₂ ∧ s₁ = s₂) :
    SContract Y C where
  halts a s hs := by
    obtain ⟨t, s', hX⟩ := h.halts a s hs
    exact ⟨t, s', hXY _ _ _ hX⟩
  post a s t s' hs hY := by
    obtain ⟨t₀, s₀, hX⟩ := h.halts a s hs
    obtain ⟨-, rfl⟩ := hdet _ _ _ _ _ hY (hXY _ _ _ hX)
    exact h.post a s _ _ hs hX
  keep a s t s' hs hY := by
    obtain ⟨t₀, s₀, hX⟩ := h.halts a s hs
    obtain ⟨-, rfl⟩ := hdet _ _ _ _ _ hY (hXY _ _ _ hX)
    exact h.keep a s _ _ hs hX
  ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hY₁ hY₂ := by
    obtain ⟨u₁, m₁, hX₁⟩ := h.halts a₁ s₁ h₁
    obtain ⟨u₂, m₂, hX₂⟩ := h.halts a₂ s₂ h₂
    obtain ⟨rfl, -⟩ := hdet _ _ _ _ _ hY₁ (hXY _ _ _ hX₁)
    obtain ⟨rfl, -⟩ := hdet _ _ _ _ _ hY₂ (hXY _ _ _ hX₂)
    exact h.ct a₁ a₂ s₁ s₂ _ _ _ _ h₁ h₂ hp hX₁ hX₂

namespace VC

open Std.Do

/-- Runs over the machine state `σ` that accumulate a trace `T` and may fail. -/
abbrev RunM (σ T : Type u) : Type u → Type u := StateT (σ × T) Option

section Run

variable {σ T α : Type u}

set_option linter.auxLemma false in
/-- **Triples over `RunM` are statements on `run`.** With pure assertions, the `Std.Do`
    triple says that from every state satisfying `P` the run returns a value and a state
    satisfying `Q`. -/
theorem triple_iff_run (x : RunM σ T α) (P : σ × T → Prop) (Q : α → σ × T → Prop) :
    ⦃fun st => ⌜P st⌝⦄ x ⦃⇓ a st => ⌜Q a st⌝⦄ ↔
      ∀ st, P st → ∃ a st', x.run st = some (a, st') ∧ Q a st' := by
  have hwp : ∀ st, (wp⟦x⟧ (⇓ a st => ⌜Q a st⌝) st).down ↔
      (match x.run st with | some p => Q p.1 p.2 | none => False) := fun st => by
    simp only [wp, Option.instWP._aux_1, Id.run, OptionT.run, StateT.run]
    simp [ExceptConds.false, ExceptConds.const]
    split <;> split <;> simp_all
  rw [Triple.iff, SPred.entails_1]
  refine forall_congr' fun st => imp_congr Iff.rfl ?_
  rw [hwp st]
  grind

/-- The run relation of `x` started on the empty trace: `runRel x s t s'` says that the run
    from `s` returns with final state `s'` and trace `t`. -/
def runRel [EmptyCollection T] (x : RunM σ T α) : σ → T → σ → Prop :=
  fun s t s' => ∃ a, x.run (s, ∅) = some (a, (s', t))

/-- The run started on a trace `t₀` returns `t₀ ++ t`, where `t` is the trace of the run
    started on the empty trace. -/
def AppendOnly [EmptyCollection T] [Append T] (x : RunM σ T α) : Prop :=
  ∀ s t₀ a s' t, x.run (s, ∅) = some (a, (s', t)) → x.run (s, t₀) = some (a, (s', t₀ ++ t))

/-- The run relation is deterministic. -/
theorem runRel_det [EmptyCollection T] {x : RunM σ T α} {s s₁ s₂ : σ} {t₁ t₂ : T}
    (h₁ : runRel x s t₁ s₁) (h₂ : runRel x s t₂ s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  grind only [= runRel.eq_def]

/-- A sequence of a run of `x` and a run of an append-only `y` is a run of
    `x >>= fun _ => y`. -/
theorem runRel_bind_of_seqRun [EmptyCollection T] [Append T] {β : Type u} {x : RunM σ T α}
    {y : RunM σ T β} (hy : AppendOnly y) {s s' : σ} {t : T}
    (h : seqRun (runRel x) (runRel y) s t s') : runRel (x >>= fun _ => y) s t s' := by
  obtain ⟨t₁, s₁, t₂, ⟨a, ha⟩, ⟨b, hb⟩, rfl⟩ := h
  exact ⟨b, by simp [StateT.run_bind, ha, hy _ _ _ _ _ hb]⟩

end Run

section Contract

variable {σ T α : Type u} {L : Type v} [Footprinted σ L]

/-- Every run of `x` from `s` keeps the locations outside `W s`. -/
def RunWritesIn (x : RunM σ T α) (W : σ → Set L) : Prop :=
  ∀ s t a s' t', x.run (s, t) = some (a, (s', t')) → AgreeOn (W s)ᶜ s s'

/-- **The conjunctive frame rule.** If the runs of `x` write in `W` and `W` of every state
    satisfying `P` avoids the footprint of `F`, then `F` is preserved:
    `F ⊓ wp x Q ⊑ wp x (F ⊓ Q)` on the states satisfying `P`. -/
theorem triple_frame_conj {x : RunM σ T α} {W : σ → Set L} (hW : RunWritesIn x W)
    (F : SAssert σ L) {P : σ × T → Prop} {Q : α → σ × T → Prop}
    (h : ⦃fun st => ⌜P st⌝⦄ x ⦃⇓ a st => ⌜Q a st⌝⦄)
    (hF : ∀ st, P st → Disjoint (W st.1) F.fp) :
    ⦃fun st => ⌜P st ∧ F.holds st.1⌝⦄ x ⦃⇓ a st => ⌜Q a st ∧ F.holds st.1⌝⦄ := by
  refine (triple_iff_run x _ _).2 ?_
  rintro st ⟨hp, hf⟩
  obtain ⟨a, st', hrun, hq⟩ := (triple_iff_run x _ _).1 h st hp
  refine ⟨a, st', hrun, hq, F.supp _ _ (agreeOn_anti ?_ (hW st.1 st.2 a st'.1 st'.2 hrun)) hf⟩
  exact Set.subset_compl_iff_disjoint_left.mpr (hF st hp)

/-- **Contracts from triples.** Let `prog n` be the run with fuel `n` and `fuel s` the fuel
    from the entry state `s`. If, from every entry state `s₀` satisfying `pre a` and the empty
    trace, the run reaches a state satisfying `post a` that agrees with `s₀` outside
    `W a s₀`, with the trace `τ (pubView s₀)`, then the run relation meets the contract whose
    public relation is equality of the public views. -/
theorem sContract_of_triple {β γ : Type u} {Pub : Type w} [EmptyCollection T]
    (prog : ℕ → RunM σ T β) (fuel : σ → ℕ) (pubView : σ → Pub) (τ : Pub → T)
    {pre post : γ → SAssert σ L} {W : γ → σ → Set L}
    (h : ∀ a s₀, (pre a).holds s₀ →
      ⦃fun st => ⌜st = (s₀, ∅)⌝⦄ prog (fuel s₀)
        ⦃⇓ _ st => ⌜(post a).holds st.1 ∧ AgreeOn (W a s₀)ᶜ s₀ st.1 ∧
          st.2 = τ (pubView s₀)⌝⦄) :
    SContract (fun s => runRel (prog (fuel s)) s)
      ({ pre := pre, post := post, writes := W,
         pub := fun s₁ s₂ => pubView s₁ = pubView s₂ } : ContractSpec σ L γ) := by
  have H : ∀ a s₀, (pre a).holds s₀ → ∃ b s' t,
      (prog (fuel s₀)).run (s₀, ∅) = some (b, (s', t)) ∧
      (post a).holds s' ∧ AgreeOn (W a s₀)ᶜ s₀ s' ∧ t = τ (pubView s₀) := fun a s₀ hs => by
    obtain ⟨b, st', hr, hq⟩ := (triple_iff_run _ _ _).1 (h a s₀ hs) (s₀, ∅) rfl
    exact ⟨b, st'.1, st'.2, hr, hq⟩
  have huniq : ∀ a s₀ t s', (pre a).holds s₀ → runRel (prog (fuel s₀)) s₀ t s' →
      (post a).holds s' ∧ AgreeOn (W a s₀)ᶜ s₀ s' ∧ t = τ (pubView s₀) := by
    rintro a s₀ t s' hs ⟨b, hb⟩
    obtain ⟨b', s'', t', hr, hq⟩ := H a s₀ hs
    rw [hr] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl, rfl⟩ := hb
    exact hq
  refine ⟨fun a s hs => ?_, fun a s t s' hs hX => (huniq a s t s' hs hX).1,
    fun a s t s' hs hX => (huniq a s t s' hs hX).2.1, ?_⟩
  · obtain ⟨b, s', t, hr, -⟩ := H a s hs
    exact ⟨t, s', b, hr⟩
  · intro a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂
    rw [(huniq a₁ s₁ t₁ s₁' h₁ hX₁).2.2, (huniq a₂ s₂ t₂ s₂' h₂ hX₂).2.2]
    exact congrArg τ hp

/-- **Sequencing.** The run relation of `x >>= fun _ => y` meets the sequenced contract
    `C₁.seq (runRel x) C₂` under the side conditions of `SContract.seq`, when the run of `y`
    only appends to the trace. -/
theorem runRel_seq [EmptyCollection T] [Append T] {β γ : Type u} {x : RunM σ T α}
    {y : RunM σ T β} {C₁ C₂ : ContractSpec σ L γ} (hy : AppendOnly y)
    (h₁ : SContract (runRel x) C₁) (h₂ : SContract (runRel y) C₂)
    (hmid : ∀ a s, (C₁.post a).holds s → (C₂.pre a).holds s)
    (hpub : ∀ a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂', (C₁.pre a₁).holds s₁ → (C₁.pre a₂).holds s₂ →
      C₁.pub s₁ s₂ → runRel x s₁ t₁ s₁' → runRel x s₂ t₂ s₂' → C₂.pub s₁' s₂') :
    SContract (runRel (x >>= fun _ => y)) (C₁.seq (runRel x) C₂) :=
  (h₁.seq h₂ hmid hpub).of_le_det (fun _ _ _ => runRel_bind_of_seqRun hy)
    (fun _ _ _ _ _ => runRel_det)

end Contract

end VC

end CatCrypt.Crypto.SecureCompilation.SepLogic
