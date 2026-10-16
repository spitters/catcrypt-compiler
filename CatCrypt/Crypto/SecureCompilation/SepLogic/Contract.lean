/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Core

/-!
# Contracts of run relations over footprinted states

A run relation `X : σ → T → σ → Prop` relates an entry state, a trace and a final state; a
callee given as a relation may be nondeterministic and leaks its trace. A contract
`C : ContractSpec σ L α` has logical variables `α`: a precondition `C.pre a` and a
postcondition `C.post a`, both footprinted assertions, a write set `C.writes a s` that depends
on the logical variables and on the entry state, and a public relation `C.pub` on entry
states. `SContract X C` says that `X` meets `C`: from every state satisfying `C.pre a` there
is a run (termination), every run ends in a state satisfying `C.post a` and agrees with the
entry state outside `C.writes a s`, and two runs from entry states related by `C.pub` that
satisfy the precondition (at any two values of the logical variables) have equal traces.

The postcondition is a family of one-state assertions indexed by the logical variables. A
relation between the entry state and the final state is stated by a logical variable that
names the entry values the postcondition refers to (`a` in `C.pre a` and `C.post a`); a
state-dependent footprint is a footprint that depends on a logical variable fixed by the
precondition. The postcondition of the frame rule is then a separating conjunction of two
assertions over the final state.

`detRun f tr` is the run relation of a state transformer with a trace function; its contracts
are the total triples of `Triple` with a write set and equality of traces
(`sContract_detRun_iff`).

## Main definitions

* `ContractSpec`: precondition, postcondition, write set, public relation.
* `SContract`: a run relation meets a contract.
* `detRun`, `seqRun`: the run of a transformer, and the sequential composition of two runs.
* `ContractSpec.frame`, `ContractSpec.seq`: the contracts of the frame and sequencing rules.

## Main results

* `SContract.adapt`: the rule of adaptation of the logical variables, with consequence.
* `SContract.conseq`: consequence at fixed logical variables.
* `SContract.sexists`: a logical variable that the postcondition and the write set do not
  mention moves into an existential precondition.
* `SContract.frame`: the frame rule.
* `SContract.seq`: sequencing.
* `sContract_detRun_iff`: contracts of a deterministic run are triples with a write set and
  equal traces.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

universe u v w x y z

open Footprinted SAssert

/-- A contract over states `σ` with locations `L` and logical variables `α`. -/
structure ContractSpec (σ : Type u) (L : Type v) [Footprinted σ L] (α : Type x) where
  /-- The precondition at the logical variables. -/
  pre : α → SAssert σ L
  /-- The postcondition at the logical variables, on the final state. -/
  post : α → SAssert σ L
  /-- The locations a run may change, from the logical variables and the entry state. -/
  writes : α → σ → Set L
  /-- The relation between two entry states that agree on the public data. -/
  pub : σ → σ → Prop

section Contract

variable {σ : Type u} {L : Type v} [Footprinted σ L] {T : Type w} {α : Type x}

/-- **The run relation `X` meets the contract `C`.** -/
structure SContract (X : σ → T → σ → Prop) (C : ContractSpec σ L α) : Prop where
  /-- A run exists from every state that satisfies the precondition. -/
  halts : ∀ a s, (C.pre a).holds s → ∃ t s', X s t s'
  /-- Every run from the precondition ends in the postcondition. -/
  post : ∀ a s t s', (C.pre a).holds s → X s t s' → (C.post a).holds s'
  /-- Every run from the precondition keeps the locations outside the write set. -/
  keep : ∀ a s t s', (C.pre a).holds s → X s t s' → AgreeOn (C.writes a s)ᶜ s s'
  /-- Two runs from publicly related entry states that satisfy the precondition have equal
      traces. -/
  ct : ∀ a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂', (C.pre a₁).holds s₁ → (C.pre a₂).holds s₂ →
    C.pub s₁ s₂ → X s₁ t₁ s₁' → X s₂ t₂ s₂' → t₁ = t₂

/-- **Adaptation.** A contract `D` follows from `C` when every state satisfying `D.pre b`
    satisfies `C.pre a` for some `a` whose postcondition implies `D.post b` and whose write
    set lies in that of `D`, and the public relation of `D` implies that of `C`. -/
theorem SContract.adapt {β : Type y} {X : σ → T → σ → Prop} {C : ContractSpec σ L α}
    {D : ContractSpec σ L β} (h : SContract X C)
    (hpre : ∀ b s, (D.pre b).holds s → ∃ a, (C.pre a).holds s ∧
      (∀ s', (C.post a).holds s' → (D.post b).holds s') ∧ C.writes a s ⊆ D.writes b s)
    (hpub : ∀ s₁ s₂, D.pub s₁ s₂ → C.pub s₁ s₂) : SContract X D where
  halts b s hs := by
    obtain ⟨a, ha, -, -⟩ := hpre b s hs
    exact h.halts a s ha
  post b s t s' hs hX := by
    obtain ⟨a, ha, hQ, -⟩ := hpre b s hs
    exact hQ _ (h.post a s t s' ha hX)
  keep b s t s' hs hX := by
    obtain ⟨a, ha, -, hW⟩ := hpre b s hs
    exact agreeOn_anti (Set.compl_subset_compl.2 hW) (h.keep a s t s' ha hX)
  ct b₁ b₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ := by
    obtain ⟨a₁, ha₁, -, -⟩ := hpre b₁ s₁ h₁
    obtain ⟨a₂, ha₂, -, -⟩ := hpre b₂ s₂ h₂
    exact h.ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' ha₁ ha₂ (hpub _ _ hp) hX₁ hX₂

/-- **Consequence** at fixed logical variables: a stronger precondition, a weaker
    postcondition, a larger write set and a stronger public relation. -/
theorem SContract.conseq {X : σ → T → σ → Prop} {C : ContractSpec σ L α} (h : SContract X C)
    {P Q : α → SAssert σ L} {W : α → σ → Set L} {pub : σ → σ → Prop}
    (hP : ∀ a, P a ⊢ₛ C.pre a) (hQ : ∀ a, C.post a ⊢ₛ Q a)
    (hW : ∀ a s, (P a).holds s → C.writes a s ⊆ W a s)
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → C.pub s₁ s₂) : SContract X ⟨P, Q, W, pub⟩ :=
  h.adapt (fun a s hs => ⟨a, (hP a s hs).1, fun s' h' => (hQ a s' h').1, hW a s hs⟩) hpub

/-- **The existential rule.** A logical variable `c` that the postcondition and the write set
    do not mention moves into the precondition as an existential, over a footprint `F`
    common to the preconditions. -/
theorem SContract.sexists {β : Type y} {γ : Type z} {X : σ → T → σ → Prop}
    {C : ContractSpec σ L (β × γ)} (h : SContract X C) (F : Set L)
    (hF : ∀ p, (C.pre p).fp = F) {Q : β → SAssert σ L} {W : β → σ → Set L}
    (hQ : ∀ b c, C.post (b, c) = Q b) (hW : ∀ b c, C.writes (b, c) = W b) :
    SContract X ⟨fun b => SAssert.sexists F (fun c => C.pre (b, c)) (fun c => hF (b, c)),
      Q, W, C.pub⟩ :=
  h.adapt (fun b s ⟨c, hc⟩ => ⟨(b, c), hc,
      fun s' h' => show (Q b).holds s' from hQ b c ▸ h', (congrFun (hW b c) s).le⟩)
    (fun _ _ hp => hp)

/-- The contract of the frame rule: the frame `R a` is added to both conditions. -/
def ContractSpec.frame (C : ContractSpec σ L α) (R : α → SAssert σ L) : ContractSpec σ L α where
  pre a := C.pre a ∗ R a
  post a := C.post a ∗ R a
  writes := C.writes
  pub := C.pub

/-- **The frame rule.** If the runs from the precondition write only inside its footprint and
    the footprint of the postcondition lies in that of the precondition, a frame separated
    from the precondition is preserved. -/
theorem SContract.frame {X : σ → T → σ → Prop} {C : ContractSpec σ L α} (R : α → SAssert σ L)
    (h : SContract X C) (hWP : ∀ a s, (C.pre a).holds s → C.writes a s ⊆ (C.pre a).fp)
    (hQ : ∀ a, (C.post a).fp ⊆ (C.pre a).fp) : SContract X (C.frame R) where
  halts a s hs := h.halts a s hs.2.1
  post a s t s' hs hX := by
    obtain ⟨hd, hp, hr⟩ := hs
    refine ⟨hd.mono_left (hQ a), h.post a s t s' hp hX,
      (R a).supp s s' (agreeOn_anti ?_ (h.keep a s t s' hp hX)) hr⟩
    exact fun l hl hlW => Set.disjoint_left.1 hd (hWP a s hp hlW) hl
  keep a s t s' hs hX := h.keep a s t s' hs.2.1 hX
  ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ :=
    h.ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁.2.1 h₂.2.1 hp hX₁ hX₂

/-- The sequential composition of two run relations: the traces are concatenated. -/
def seqRun [Append T] (X Y : σ → T → σ → Prop) : σ → T → σ → Prop :=
  fun s t s' => ∃ t₁ s₁ t₂, X s t₁ s₁ ∧ Y s₁ t₂ s' ∧ t = t₁ ++ t₂

/-- The contract of a sequence: the precondition and public relation of the first contract,
    the postcondition of the second, and as write set the writes of the first run together
    with the writes of the second from every state the first run reaches. -/
def ContractSpec.seq (X : σ → T → σ → Prop) (C₁ C₂ : ContractSpec σ L α) :
    ContractSpec σ L α where
  pre := C₁.pre
  post := C₂.post
  writes a s := C₁.writes a s ∪ {l | ∃ t s₁, X s t s₁ ∧ l ∈ C₂.writes a s₁}
  pub := C₁.pub

/-- **Sequencing.** If the postcondition of the first contract implies the precondition of
    the second, and two runs of `X` from publicly related entry states end in states related
    by the public relation of the second contract, the sequence meets `C₁.seq X C₂`. -/
theorem SContract.seq [Append T] {X Y : σ → T → σ → Prop} {C₁ C₂ : ContractSpec σ L α}
    (h₁ : SContract X C₁) (h₂ : SContract Y C₂)
    (hmid : ∀ a s, (C₁.post a).holds s → (C₂.pre a).holds s)
    (hpub : ∀ a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂', (C₁.pre a₁).holds s₁ → (C₁.pre a₂).holds s₂ →
      C₁.pub s₁ s₂ → X s₁ t₁ s₁' → X s₂ t₂ s₂' → C₂.pub s₁' s₂') :
    SContract (seqRun X Y) (C₁.seq X C₂) where
  halts a s hs := by
    obtain ⟨t₁, s₁, hX⟩ := h₁.halts a s hs
    obtain ⟨t₂, s', hY⟩ := h₂.halts a s₁ (hmid a s₁ (h₁.post a s t₁ s₁ hs hX))
    exact ⟨t₁ ++ t₂, s', t₁, s₁, t₂, hX, hY, rfl⟩
  post a s t s' hs := by
    rintro ⟨t₁, s₁, t₂, hX, hY, -⟩
    exact h₂.post a s₁ t₂ s' (hmid a s₁ (h₁.post a s t₁ s₁ hs hX)) hY
  keep a s t s' hs := by
    rintro ⟨t₁, s₁, t₂, hX, hY, -⟩
    refine agreeOn_trans
      (agreeOn_anti (Set.compl_subset_compl.2 Set.subset_union_left) (h₁.keep a s t₁ s₁ hs hX))
      (agreeOn_anti (Set.compl_subset_compl.2 fun l hl => Or.inr ⟨t₁, s₁, hX, hl⟩)
        (h₂.keep a s₁ t₂ s' (hmid a s₁ (h₁.post a s t₁ s₁ hs hX)) hY))
  ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' hs₁ hs₂ hp := by
    rintro ⟨u₁, m₁, v₁, hX₁, hY₁, rfl⟩ ⟨u₂, m₂, v₂, hX₂, hY₂, rfl⟩
    rw [h₁.ct a₁ a₂ s₁ s₂ u₁ u₂ m₁ m₂ hs₁ hs₂ hp hX₁ hX₂,
      h₂.ct a₁ a₂ m₁ m₂ v₁ v₂ s₁' s₂' (hmid a₁ m₁ (h₁.post a₁ s₁ u₁ m₁ hs₁ hX₁))
        (hmid a₂ m₂ (h₁.post a₂ s₂ u₂ m₂ hs₂ hX₂))
        (hpub a₁ a₂ s₁ s₂ u₁ u₂ m₁ m₂ hs₁ hs₂ hp hX₁ hX₂) hY₁ hY₂]

/-- The run relation of a state transformer `f` whose trace is `tr` of the entry state. -/
def detRun (f : σ → σ) (tr : σ → T) : σ → T → σ → Prop :=
  fun s t s' => t = tr s ∧ s' = f s

/-- **Contracts of a deterministic run.** `detRun f tr` meets `C` exactly when `f` satisfies
    the triples `Triple (C.pre a) f (C.post a)`, keeps the locations outside the write set
    from the precondition, and `tr` agrees on publicly related states that satisfy the
    precondition. -/
theorem sContract_detRun_iff {f : σ → σ} {tr : σ → T} {C : ContractSpec σ L α} :
    SContract (detRun f tr) C ↔
      (∀ a, Triple (C.pre a) f (C.post a)) ∧
      (∀ a s, (C.pre a).holds s → AgreeOn (C.writes a s)ᶜ s (f s)) ∧
      (∀ a₁ a₂ s₁ s₂, (C.pre a₁).holds s₁ → (C.pre a₂).holds s₂ → C.pub s₁ s₂ →
        tr s₁ = tr s₂) := by
  constructor
  · intro h
    exact ⟨fun a s hs => h.post a s _ _ hs ⟨rfl, rfl⟩,
      fun a s hs => h.keep a s _ _ hs ⟨rfl, rfl⟩,
      fun a₁ a₂ s₁ s₂ h₁ h₂ hp => h.ct a₁ a₂ s₁ s₂ _ _ _ _ h₁ h₂ hp ⟨rfl, rfl⟩ ⟨rfl, rfl⟩⟩
  · rintro ⟨hT, hK, hC⟩
    refine ⟨fun a s _ => ⟨_, _, rfl, rfl⟩, ?_, ?_, ?_⟩
    · rintro a s t s' hs ⟨-, rfl⟩
      exact hT a s hs
    · rintro a s t s' hs ⟨-, rfl⟩
      exact hK a s hs
    · rintro a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ⟨rfl, -⟩ ⟨rfl, -⟩
      exact hC a₁ a₂ s₁ s₂ h₁ h₂ hp

end Contract

/-! ## Examples over the states `ℕ → ℕ`

The transformer `bump` increments the cell `0` and leaks the cell `1`. -/

section Examples

/-- The cell `i` of a function state holds `v`. -/
def ptsFn {ι : Type u} {β : Type v} (i : ι) (v : β) : SAssert (ι → β) ι where
  fp := {i}
  holds s := s i = v
  supp _ _ h hs := (h i (Set.mem_singleton i)).symm.trans hs

/-- Increment the cell `0`. -/
def bump (s : ℕ → ℕ) : ℕ → ℕ := Function.update s 0 (s 0 + 1)

/-- The run of `bump`, leaking the cell `1`. -/
def bumpRun : (ℕ → ℕ) → List ℕ → (ℕ → ℕ) → Prop := detRun bump fun s => [s 1]

/-- The contract of `bump` at the initial value `n` of the cell `0`, shifted by `k`. -/
def bumpSpec (k : ℕ) : ContractSpec (ℕ → ℕ) ℕ ℕ where
  pre n := ptsFn 0 (n + k)
  post n := ptsFn 0 (n + k + 1)
  writes _ _ := {0}
  pub s₁ s₂ := s₁ 1 = s₂ 1

theorem bump_contract (k : ℕ) : SContract bumpRun (bumpSpec k) := by
  refine sContract_detRun_iff.2 ⟨fun n s hs => ?_, fun n s _ l hl => ?_,
    fun _ _ s₁ s₂ _ _ (hp : s₁ 1 = s₂ 1) => by rw [hp]⟩
  · change Function.update s 0 (s 0 + 1) 0 = n + k + 1
    change s 0 = n + k at hs
    simp [hs]
  · change l ≠ 0 at hl
    exact (Function.update_of_ne hl _ _).symm

/-- The frame rule at `bump`: the cell `1` is kept. -/
example (k : ℕ) : SContract bumpRun ((bumpSpec k).frame fun _ => ptsFn 1 7) :=
  (bump_contract k).frame _ (fun _ _ _ => subset_rfl) (fun _ => subset_rfl)

/-- Consequence at `bump`: from the precondition `0 ↦ n` the cell `0` is owned at the end. -/
example : SContract bumpRun
    ⟨fun n => ptsFn 0 n, fun _ => SAssert.own {0}, fun _ _ => {0}, fun s₁ s₂ => s₁ 1 = s₂ 1⟩ :=
  (bump_contract 0).conseq (fun _ => Entails.refl _) (fun _ _ _ => ⟨trivial, subset_rfl⟩)
    (fun _ _ _ => subset_rfl) (fun _ _ hp => hp)

/-- Sequencing at `bump`: two increments add two, and the trace has two entries. -/
example : SContract (seqRun bumpRun bumpRun) ((bumpSpec 0).seq bumpRun (bumpSpec 1)) :=
  (bump_contract 0).seq (bump_contract 1) (fun _ _ h => h) (by
    rintro _ _ s₁ s₂ _ _ _ _ _ _ hp ⟨-, rfl⟩ ⟨-, rfl⟩
    simpa [bumpSpec, bump] using hp)

/-- The existential rule at `bump`: from the precondition `∃ n, 0 ↦ n` the cell `0` is
    owned at the end. -/
example : SContract bumpRun
    ⟨fun _ : Unit => SAssert.sexists {0} (fun n => ptsFn 0 n) (fun _ => rfl),
      fun _ => SAssert.own {0}, fun _ _ => {0}, fun s₁ s₂ => s₁ 1 = s₂ 1⟩ :=
  SContract.sexists (C := ⟨fun p : Unit × ℕ => ptsFn 0 p.2, fun _ => SAssert.own {0},
      fun _ _ => {0}, fun s₁ s₂ => s₁ 1 = s₂ 1⟩)
    ((bump_contract 0).adapt (fun p _ hs => ⟨p.2, hs, fun _ _ => trivial, subset_rfl⟩)
      (fun _ _ hp => hp)) {0} (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end Examples

end CatCrypt.Crypto.SecureCompilation.SepLogic
