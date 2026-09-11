/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.UCMonad.RoundM

/-!
# Bounded ITree with Visible Events (Level 2 UC)

This file defines `ITreeN n E α`, a bounded interaction tree with visible events,
extending `RoundM n` from Level 1.5 to Level 2 of the UC hierarchy.

## Key idea

```
ITreeN 0 E α       = SPComp α
ITreeN (n+1) E α   = SPComp (α ⊕ ITreeN n E α ⊕ (Σ e : E.Event, E.Resp e → ITreeN n E α))
```

Three cases per step:
- `.inl a` — done (return value)
- `.inr (.inl k)` — silent τ (continue without interaction)
- `.inr (.inr ⟨e, k⟩)` — visible event (adversary interaction)

## Handler parameterization

The `bind` operation requires a handler `h : ∀ e, SPComp (E.Resp e)` to resolve
visible events at round boundaries. The monad and metric instances are parameterized
by this handler. For `emptyEvSig` (no events), the handler is trivial.

## Axiom status

**0 axioms**, **0 sorries**. All monad laws proved by induction on `n`.
-/

@[expose] public section

namespace UCMonad.ITreeNUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal
open UCMonad.RoundMUC (RoundM)

/-! ## Section 1: Event Signature -/

/-- An event signature describes the adversary interface. -/
structure EventSig where
  Event : Type
  Resp : Event → Type

/-- The empty event signature: no adversary interaction. -/
def emptyEvSig : EventSig where
  Event := Empty
  Resp := Empty.elim

/-! ## Section 2: ITreeN Type -/

/-- Bounded interaction tree with visible events. -/
noncomputable def ITreeN : Nat → EventSig → Type → Type
  | 0, _, α => SPComp α
  | n + 1, E, α => SPComp (α ⊕ ITreeN n E α ⊕ (Σ (e : E.Event), E.Resp e → ITreeN n E α))

/-- The step type abbreviation. -/
abbrev ITreeNStep (n : Nat) (E : EventSig) (α : Type) :=
  α ⊕ ITreeN n E α ⊕ (Σ (e : E.Event), E.Resp e → ITreeN n E α)

/-! ## Section 3: Constructors -/

noncomputable def ITreeN.done {α : Type} {E : EventSig} : (n : Nat) → α → ITreeN n E α
  | 0, a => SPComp.pure a
  | _ + 1, a => SPComp.pure (.inl a)

noncomputable def ITreeN.yield {α : Type} {E : EventSig} (n : Nat)
    (k : ITreeN n E α) : ITreeN (n + 1) E α :=
  SPComp.pure (.inr (.inl k))

noncomputable def ITreeN.vis {α : Type} {E : EventSig} (n : Nat)
    (e : E.Event) (k : E.Resp e → ITreeN n E α) : ITreeN (n + 1) E α :=
  SPComp.pure (.inr (.inr ⟨e, k⟩))

noncomputable def ITreeN.fail {α : Type} {E : EventSig} : (n : Nat) → ITreeN n E α
  | 0 => SPComp.fail
  | n + 1 => (SPComp.fail : SPComp (ITreeNStep n E α))

/-! ## Section 4: Flatten -/

/-- Flatten resolves one level using a handler for visible events. -/
noncomputable def ITreeN.flatten {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    (n : Nat) → ITreeN (n + 1) E α → ITreeN n E α
  | 0, c => SPComp.bind c (fun
    | .inl a => SPComp.pure a
    | .inr (.inl k) => k
    | .inr (.inr ⟨e, k⟩) => SPComp.bind (handler e) k)
  | n + 1, c => SPComp.bind c (fun
    | .inl a => (SPComp.pure (Sum.inl a) : SPComp (ITreeNStep n E α))
    | .inr (.inl k) => k
    | .inr (.inr ⟨e, k⟩) => SPComp.bind (handler e) k)

@[simp] theorem ITreeN.flatten_zero {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (c : ITreeN 1 E α) :
    ITreeN.flatten handler 0 c = SPComp.bind c (fun
      | .inl a => SPComp.pure a
      | .inr (.inl k) => k
      | .inr (.inr ⟨e, k⟩) => SPComp.bind (handler e) k) := rfl

@[simp] theorem ITreeN.flatten_succ {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat) (c : ITreeN (n + 2) E α) :
    ITreeN.flatten handler (n + 1) c = SPComp.bind c (fun
      | .inl a => (SPComp.pure (Sum.inl a) : SPComp (ITreeNStep n E α))
      | .inr (.inl k) => k
      | .inr (.inr ⟨e, k⟩) => SPComp.bind (handler e) k) := rfl

/-! ## Section 5: Bind -/

noncomputable def ITreeN.bind' {α β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    (n : Nat) → ITreeN n E α → (α → ITreeN n E β) → ITreeN n E β
  | 0, c, f => SPComp.bind c f
  | n + 1, c, f => SPComp.bind c (fun
    | .inl a => f a
    | .inr (.inl k) => (SPComp.pure (Sum.inr (Sum.inl
        (ITreeN.bind' handler n k (fun a => ITreeN.flatten handler n (f a))))) :
        SPComp (ITreeNStep n E β))
    | .inr (.inr ⟨e, k⟩) => (SPComp.pure (Sum.inr (Sum.inr
        ⟨e, fun r => ITreeN.bind' handler n (k r)
          (fun a => ITreeN.flatten handler n (f a))⟩)) :
        SPComp (ITreeNStep n E β)))

@[simp] theorem ITreeN.bind'_zero {α β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (c : SPComp α) (f : α → SPComp β) :
    ITreeN.bind' (E := E) handler 0 c f = SPComp.bind c f := rfl

@[simp] theorem ITreeN.bind'_succ {α β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (c : ITreeN (n + 1) E α) (f : α → ITreeN (n + 1) E β) :
    ITreeN.bind' handler (n + 1) c f = SPComp.bind c (fun
      | .inl a => f a
      | .inr (.inl k) => (SPComp.pure (Sum.inr (Sum.inl
          (ITreeN.bind' handler n k (fun a => ITreeN.flatten handler n (f a))))) :
          SPComp (ITreeNStep n E β))
      | .inr (.inr ⟨e, k⟩) => (SPComp.pure (Sum.inr (Sum.inr
          ⟨e, fun r => ITreeN.bind' handler n (k r)
            (fun a => ITreeN.flatten handler n (f a))⟩)) :
          SPComp (ITreeNStep n E β))) := rfl

/-! ## Section 6: Flatten-Bind Commutativity -/

set_option maxHeartbeats 800000 in
theorem flatten_bind' {α β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (c : ITreeN (n + 1) E α) (g : α → ITreeN (n + 1) E β) :
    ITreeN.flatten handler n (ITreeN.bind' handler (n + 1) c g) =
    ITreeN.bind' handler n (ITreeN.flatten handler n c)
      (fun a => ITreeN.flatten handler n (g a)) := by
  cases n with
  | zero =>
    simp only [ITreeN.flatten_zero, ITreeN.bind'_succ, ITreeN.bind'_zero, SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl a => simp [SPComp.pure_bind]
    | inr s => cases s with
      | inl k => simp [SPComp.pure_bind]
      | inr vc =>
        obtain ⟨e, k⟩ := vc
        simp only [SPComp.pure_bind, SPComp.bind_assoc]
  | succ m =>
    simp only [ITreeN.flatten_succ, ITreeN.bind'_succ, SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl a => simp [SPComp.pure_bind]
    | inr s => cases s with
      | inl k => simp [SPComp.pure_bind]
      | inr vc =>
        obtain ⟨e, k⟩ := vc
        simp only [SPComp.pure_bind, SPComp.bind_assoc]

/-! ## Section 6b: FlattenAll -/

noncomputable def ITreeN.flattenAll {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    (n : Nat) → ITreeN n E α → SPComp α
  | 0, c => c
  | n + 1, c => ITreeN.flattenAll handler n (ITreeN.flatten handler n c)

@[simp] theorem ITreeN.flattenAll_zero {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (c : SPComp α) :
    ITreeN.flattenAll (E := E) handler 0 c = c := rfl

@[simp] theorem ITreeN.flattenAll_succ {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat) (c : ITreeN (n + 1) E α) :
    ITreeN.flattenAll handler (n + 1) c =
    ITreeN.flattenAll handler n (ITreeN.flatten handler n c) := rfl

set_option maxHeartbeats 800000 in
theorem flattenAll_bind {α β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (c : ITreeN n E α) (f : α → ITreeN n E β) :
    ITreeN.flattenAll handler n (ITreeN.bind' handler n c f) =
    SPComp.bind (ITreeN.flattenAll handler n c)
      (fun a => ITreeN.flattenAll handler n (f a)) := by
  induction n generalizing α β with
  | zero => rfl
  | succ n ih =>
    simp only [ITreeN.flattenAll_succ]
    rw [flatten_bind' handler n c f, ih]

/-! ## Section 7: Monad Laws -/

theorem itreeN_pure_bind {α β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (a : α) (f : α → ITreeN n E β) :
    ITreeN.bind' handler n (ITreeN.done n a) f = f a := by
  cases n with
  | zero => exact SPComp.pure_bind a f
  | succ n =>
    show SPComp.bind (SPComp.pure (Sum.inl a)) _ = f a
    exact SPComp.pure_bind (Sum.inl a) _

theorem flatten_done {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    (n : Nat) → (a : α) → ITreeN.flatten handler n (ITreeN.done (n + 1) a) = ITreeN.done n a
  | 0, a => by
    unfold ITreeN.flatten ITreeN.done
    exact SPComp.pure_bind (Sum.inl a) _
  | _ + 1, a => by
    unfold ITreeN.flatten ITreeN.done
    exact SPComp.pure_bind (Sum.inl a) _

theorem itreeN_bind_done {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (m : ITreeN n E α) :
    ITreeN.bind' handler n m (ITreeN.done n) = m := by
  induction n with
  | zero => exact SPComp.bind_pure m
  | succ n ih =>
    change SPComp.bind m _ = m
    conv_rhs => rw [← SPComp.bind_pure m]
    congr 1; funext x; cases x with
    | inl _ => rfl
    | inr s => cases s with
      | inl k =>
        simp only [flatten_done handler n]
        exact congrArg SPComp.pure (congrArg (Sum.inr ∘ Sum.inl) (ih k))
      | inr vc =>
        obtain ⟨e, k⟩ := vc
        simp only [flatten_done handler n]
        exact congrArg SPComp.pure (congrArg Sum.inr
          (congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (funext fun r => ih (k r))))))

set_option maxHeartbeats 1600000 in
theorem itreeN_bind_assoc {α β γ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (m : ITreeN n E α) (f : α → ITreeN n E β) (g : β → ITreeN n E γ) :
    ITreeN.bind' handler n (ITreeN.bind' handler n m f) g =
    ITreeN.bind' handler n m (fun a => ITreeN.bind' handler n (f a) g) := by
  induction n with
  | zero => exact SPComp.bind_assoc m f g
  | succ n ih =>
    change SPComp.bind (SPComp.bind m _) _ = SPComp.bind m _
    rw [SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl _ => rfl
    | inr s => cases s with
      | inl k =>
        simp only [SPComp.pure_bind]
        exact congrArg SPComp.pure (congrArg (Sum.inr ∘ Sum.inl) (by
          rw [ih]
          congr 1; funext a
          exact (flatten_bind' handler n (f a) g).symm))
      | inr vc =>
        obtain ⟨e, k⟩ := vc
        simp only [SPComp.pure_bind]
        exact congrArg SPComp.pure (congrArg Sum.inr (congrArg Sum.inr
          (Sigma.ext rfl (heq_of_eq (funext fun r => by
            dsimp only []
            rw [ih]
            congr 1; funext a
            exact (flatten_bind' handler n (f a) g).symm)))))

/-! ## Section 7b: Monad + LawfulMonad Instances -/

/-- Monad instance parameterized by handler. -/
@[reducible] noncomputable def instMonadITreeN (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) : Monad (ITreeN n E) where
  pure := ITreeN.done n
  bind := ITreeN.bind' handler n

set_option maxHeartbeats 400000 in
noncomputable def instLawfulMonadITreeN (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    @LawfulMonad (ITreeN n E) (instMonadITreeN n E handler) := by
  letI : Monad (ITreeN n E) := instMonadITreeN n E handler
  exact LawfulMonad.mk'
    (id_map := itreeN_bind_done handler n)
    (pure_bind := itreeN_pure_bind handler n)
    (bind_assoc := itreeN_bind_assoc handler n)

/-! ## Section 8: Depth Embedding -/

noncomputable def ITreeN.embed {α : Type} {E : EventSig} :
    (n : Nat) → ITreeN n E α → ITreeN (n + 1) E α
  | 0, c => SPComp.bind c (fun a => SPComp.pure (Sum.inl a))
  | n + 1, c => SPComp.bind c (fun
    | .inl a => SPComp.pure (Sum.inl a)
    | .inr (.inl k) => SPComp.pure (Sum.inr (Sum.inl (ITreeN.embed n k)))
    | .inr (.inr ⟨e, k⟩) =>
      (SPComp.pure (Sum.inr (Sum.inr ⟨e, fun r => ITreeN.embed n (k r)⟩)) :
        SPComp (ITreeNStep (n + 1) E α)))

noncomputable def ITreeN.pad {α : Type} {E : EventSig} (n : Nat) :
    (k : Nat) → ITreeN n E α → ITreeN (n + k) E α
  | 0, c => c
  | k + 1, c => ITreeN.embed (n + k) (ITreeN.pad n k c)

/-! ## Section 9: Parallel Composition on Sum -/

noncomputable def mapSumITreeN {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (f : α → ITreeN n E β) (g : γ → ITreeN n E δ) :
    (α ⊕ γ) → ITreeN n E (β ⊕ δ)
  | .inl a => ITreeN.bind' handler n (f a) (fun b => ITreeN.done n (Sum.inl b))
  | .inr c => ITreeN.bind' handler n (g c) (fun d => ITreeN.done n (Sum.inr d))

theorem mapSumITreeN_pure_pure {α β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat) :
    mapSumITreeN handler n (ITreeN.done (E := E) n : α → ITreeN n E α)
      (ITreeN.done n : β → ITreeN n E β) = ITreeN.done n := by
  funext x; cases x with
  | inl a => exact itreeN_pure_bind handler n a _
  | inr b => exact itreeN_pure_bind handler n b _

set_option maxHeartbeats 800000 in
theorem mapSumITreeN_pure_kleisli {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f : β → ITreeN n E γ) (g : γ → ITreeN n E δ) :
    (fun x : α ⊕ β =>
      ITreeN.bind' handler n
        (mapSumITreeN handler n (ITreeN.done n) f x)
        (mapSumITreeN handler n (ITreeN.done n) g))
    = mapSumITreeN handler n (ITreeN.done n) (fun b => ITreeN.bind' handler n (f b) g) := by
  funext x; cases x with
  | inl a =>
    -- Both mapSumITreeN reduce to bind (done a) (fun b => done (.inl b))
    change ITreeN.bind' handler n
      (ITreeN.bind' handler n (ITreeN.done n a) (fun b => ITreeN.done n (Sum.inl b)))
      (mapSumITreeN handler n (ITreeN.done n) g) =
      ITreeN.bind' handler n (ITreeN.done n a) (fun b => ITreeN.done n (Sum.inl b))
    rw [itreeN_pure_bind, itreeN_pure_bind]
    -- Goal: mapSumITreeN ... g (.inl a) = done (.inl a)
    unfold mapSumITreeN; dsimp only []
  | inr b =>
    change ITreeN.bind' handler n
      (ITreeN.bind' handler n (f b) (fun c => ITreeN.done n (Sum.inr c)))
      (mapSumITreeN handler n (ITreeN.done n) g) =
      ITreeN.bind' handler n (ITreeN.bind' handler n (f b) g)
        (fun d => ITreeN.done n (Sum.inr d))
    rw [itreeN_bind_assoc, itreeN_bind_assoc]
    congr 1; funext c
    rw [itreeN_pure_bind]
    -- Goal: mapSumITreeN ... g (.inr c) = bind (g c) (fun d => done (.inr d))
    rfl

/-! ## Section 10: Statistical Distance -/

noncomputable def sdistITreeN {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) : ℝ≥0∞ :=
  sdist (fun a => ITreeN.flattenAll handler n (f a))
        (fun a => ITreeN.flattenAll handler n (g a))

@[simp] theorem sdistITreeN_self {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f : α → ITreeN n E β) : sdistITreeN n E handler f f = 0 := sdist_self _

theorem sdistITreeN_sym {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) :
    sdistITreeN n E handler f g = sdistITreeN n E handler g f := sdist_sym _ _

@[grind] theorem sdistITreeN_triangle {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g h : α → ITreeN n E β) :
    sdistITreeN n E handler f h ≤
    sdistITreeN n E handler f g + sdistITreeN n E handler g h :=
  sdist_triangle _ _ _

/-! ## Game Hop Lemmas for sdistITreeN -/

/-- 2-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₂ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ : ℝ≥0∞}
    {f₀ f₁ f₂ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂) :
    sdistITreeN n E handler f₀ f₂ ≤ ε₁ + ε₂ :=
  le_trans (sdistITreeN_triangle n E handler f₀ f₁ f₂) (add_le_add h₁ h₂)

/-- 3-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₃ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃) :
    sdistITreeN n E handler f₀ f₃ ≤ ε₁ + ε₂ + ε₃ := by
  calc sdistITreeN n E handler f₀ f₃
      ≤ sdistITreeN n E handler f₀ f₂ + sdistITreeN n E handler f₂ f₃ :=
        sdistITreeN_triangle n E handler f₀ f₂ f₃
    _ ≤ (ε₁ + ε₂) + ε₃ := add_le_add (sdistITreeN_game_hop₂ h₁ h₂) h₃

/-- 4-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₄ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ ε₄ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ f₄ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄) :
    sdistITreeN n E handler f₀ f₄ ≤ ε₁ + ε₂ + ε₃ + ε₄ := by
  calc sdistITreeN n E handler f₀ f₄
      ≤ sdistITreeN n E handler f₀ f₃ + sdistITreeN n E handler f₃ f₄ :=
        sdistITreeN_triangle n E handler f₀ f₃ f₄
    _ ≤ (ε₁ + ε₂ + ε₃) + ε₄ := add_le_add (sdistITreeN_game_hop₃ h₁ h₂ h₃) h₄

/-- 5-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₅ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ ε₄ ε₅ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ f₄ f₅ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄)
    (h₅ : sdistITreeN n E handler f₄ f₅ ≤ ε₅) :
    sdistITreeN n E handler f₀ f₅ ≤ ε₁ + ε₂ + ε₃ + ε₄ + ε₅ := by
  calc sdistITreeN n E handler f₀ f₅
      ≤ sdistITreeN n E handler f₀ f₄ + sdistITreeN n E handler f₄ f₅ :=
        sdistITreeN_triangle n E handler f₀ f₄ f₅
    _ ≤ (ε₁ + ε₂ + ε₃ + ε₄) + ε₅ := add_le_add (sdistITreeN_game_hop₄ h₁ h₂ h₃ h₄) h₅

/-- 6-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₆ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ ε₄ ε₅ ε₆ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄)
    (h₅ : sdistITreeN n E handler f₄ f₅ ≤ ε₅)
    (h₆ : sdistITreeN n E handler f₅ f₆ ≤ ε₆) :
    sdistITreeN n E handler f₀ f₆ ≤ ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ := by
  calc sdistITreeN n E handler f₀ f₆
      ≤ sdistITreeN n E handler f₀ f₅ + sdistITreeN n E handler f₅ f₆ :=
        sdistITreeN_triangle n E handler f₀ f₅ f₆
    _ ≤ (ε₁ + ε₂ + ε₃ + ε₄ + ε₅) + ε₆ :=
        add_le_add (sdistITreeN_game_hop₅ h₁ h₂ h₃ h₄ h₅) h₆

/-- 7-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₇ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ ε₄ ε₅ ε₆ ε₇ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄)
    (h₅ : sdistITreeN n E handler f₄ f₅ ≤ ε₅)
    (h₆ : sdistITreeN n E handler f₅ f₆ ≤ ε₆)
    (h₇ : sdistITreeN n E handler f₆ f₇ ≤ ε₇) :
    sdistITreeN n E handler f₀ f₇ ≤ ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ + ε₇ := by
  calc sdistITreeN n E handler f₀ f₇
      ≤ sdistITreeN n E handler f₀ f₆ + sdistITreeN n E handler f₆ f₇ :=
        sdistITreeN_triangle n E handler f₀ f₆ f₇
    _ ≤ (ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆) + ε₇ :=
        add_le_add (sdistITreeN_game_hop₆ h₁ h₂ h₃ h₄ h₅ h₆) h₇

/-- 8-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₈ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ ε₄ ε₅ ε₆ ε₇ ε₈ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄)
    (h₅ : sdistITreeN n E handler f₄ f₅ ≤ ε₅)
    (h₆ : sdistITreeN n E handler f₅ f₆ ≤ ε₆)
    (h₇ : sdistITreeN n E handler f₆ f₇ ≤ ε₇)
    (h₈ : sdistITreeN n E handler f₇ f₈ ≤ ε₈) :
    sdistITreeN n E handler f₀ f₈ ≤ ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ + ε₇ + ε₈ := by
  calc sdistITreeN n E handler f₀ f₈
      ≤ sdistITreeN n E handler f₀ f₇ + sdistITreeN n E handler f₇ f₈ :=
        sdistITreeN_triangle n E handler f₀ f₇ f₈
    _ ≤ (ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ + ε₇) + ε₈ :=
        add_le_add (sdistITreeN_game_hop₇ h₁ h₂ h₃ h₄ h₅ h₆ h₇) h₈

/-- 9-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₉ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ ε₄ ε₅ ε₆ ε₇ ε₈ ε₉ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄)
    (h₅ : sdistITreeN n E handler f₄ f₅ ≤ ε₅)
    (h₆ : sdistITreeN n E handler f₅ f₆ ≤ ε₆)
    (h₇ : sdistITreeN n E handler f₆ f₇ ≤ ε₇)
    (h₈ : sdistITreeN n E handler f₇ f₈ ≤ ε₈)
    (h₉ : sdistITreeN n E handler f₈ f₉ ≤ ε₉) :
    sdistITreeN n E handler f₀ f₉ ≤ ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ + ε₇ + ε₈ + ε₉ := by
  calc sdistITreeN n E handler f₀ f₉
      ≤ sdistITreeN n E handler f₀ f₈ + sdistITreeN n E handler f₈ f₉ :=
        sdistITreeN_triangle n E handler f₀ f₈ f₉
    _ ≤ (ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ + ε₇ + ε₈) + ε₉ :=
        add_le_add (sdistITreeN_game_hop₈ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈) h₉

/-- 10-step sdistITreeN game hop. -/
theorem sdistITreeN_game_hop₁₀ {α β : Type} {n : Nat} {E : EventSig}
    {handler : ∀ e : E.Event, SPComp (E.Resp e)}
    {ε₁ ε₂ ε₃ ε₄ ε₅ ε₆ ε₇ ε₈ ε₉ ε₁₀ : ℝ≥0∞}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : α → ITreeN n E β}
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄)
    (h₅ : sdistITreeN n E handler f₄ f₅ ≤ ε₅)
    (h₆ : sdistITreeN n E handler f₅ f₆ ≤ ε₆)
    (h₇ : sdistITreeN n E handler f₆ f₇ ≤ ε₇)
    (h₈ : sdistITreeN n E handler f₇ f₈ ≤ ε₈)
    (h₉ : sdistITreeN n E handler f₈ f₉ ≤ ε₉)
    (h₁₀ : sdistITreeN n E handler f₉ f₁₀ ≤ ε₁₀) :
    sdistITreeN n E handler f₀ f₁₀ ≤
      ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ + ε₇ + ε₈ + ε₉ + ε₁₀ := by
  calc sdistITreeN n E handler f₀ f₁₀
      ≤ sdistITreeN n E handler f₀ f₉ + sdistITreeN n E handler f₉ f₁₀ :=
        sdistITreeN_triangle n E handler f₀ f₉ f₁₀
    _ ≤ (ε₁ + ε₂ + ε₃ + ε₄ + ε₅ + ε₆ + ε₇ + ε₈ + ε₉) + ε₁₀ :=
        add_le_add (sdistITreeN_game_hop₉ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉) h₁₀

/-! ## PPL Lemmas -/

theorem sdistITreeN_comp_right {α β γ : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) (k : β → ITreeN n E γ) :
    sdistITreeN n E handler (fun a => ITreeN.bind' handler n (f a) k)
      (fun a => ITreeN.bind' handler n (g a) k) ≤ sdistITreeN n E handler f g := by
  unfold sdistITreeN
  simp only [flattenAll_bind]
  exact sdist_comp_right _ _ _

theorem sdistITreeN_comp_left {α β γ : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f : α → ITreeN n E β) (g₁ g₂ : β → ITreeN n E γ) :
    sdistITreeN n E handler (fun a => ITreeN.bind' handler n (f a) g₁)
      (fun a => ITreeN.bind' handler n (f a) g₂) ≤ sdistITreeN n E handler g₁ g₂ := by
  unfold sdistITreeN
  simp only [flattenAll_bind]
  exact sdist_comp_left _ _ _

/-! ## Section 10b: UCMonadMetric Instance -/

noncomputable def instUCMonadMetricITreeN (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    UCMonadMetric (ITreeN n E) := by
  letI : Monad (ITreeN n E) := instMonadITreeN n E handler
  letI : LawfulMonad (ITreeN n E) := instLawfulMonadITreeN n E handler
  exact {
    ucMapSum := mapSumITreeN handler n
    ucMapSum_inl := fun _f _g _a => rfl
    ucMapSum_inr := fun _f _g _c => rfl
    ucMapSum_pure_pure := mapSumITreeN_pure_pure handler n
    ucMapSum_pure_kleisli := fun f g => mapSumITreeN_pure_kleisli handler n f g
    ucSdist := sdistITreeN n E handler
    ucSdist_self := sdistITreeN_self n E handler
    ucSdist_sym := sdistITreeN_sym n E handler
    ucSdist_triangle := sdistITreeN_triangle n E handler
    ucSdist_comp_right := sdistITreeN_comp_right n E handler
    ucSdist_comp_left := sdistITreeN_comp_left n E handler
  }

/-! ## Section 11: Backward Compatibility — emptyEvSig ≅ RoundM -/

noncomputable def emptyHandler : ∀ e : emptyEvSig.Event, SPComp (emptyEvSig.Resp e) :=
  fun e => e.elim

noncomputable instance instMonadITreeNEmpty (n : Nat) : Monad (ITreeN n emptyEvSig) :=
  instMonadITreeN n emptyEvSig emptyHandler

/-- Convert `RoundM n α` to `ITreeN n emptyEvSig α`. -/
noncomputable def ofRoundM {α : Type} : (n : Nat) → RoundM n α → ITreeN n emptyEvSig α
  | 0, c => c
  | n + 1, c => SPComp.bind c (fun
    | .inl a => SPComp.pure (Sum.inl a)
    | .inr k => SPComp.pure (Sum.inr (Sum.inl (ofRoundM n k))))

/-- Convert `ITreeN n emptyEvSig α` to `RoundM n α`. -/
noncomputable def toRoundM {α : Type} : (n : Nat) → ITreeN n emptyEvSig α → RoundM n α
  | 0, c => c
  | n + 1, c => SPComp.bind c (fun
    | .inl a => SPComp.pure (Sum.inl a)
    | .inr (.inl k) => SPComp.pure (Sum.inr (toRoundM n k))
    | .inr (.inr ⟨e, _⟩) => e.elim)

set_option maxHeartbeats 800000 in
theorem toRoundM_ofRoundM {α : Type} :
    (n : Nat) → (c : RoundM n α) → toRoundM n (ofRoundM n c) = c
  | 0, _ => rfl
  | n + 1, c => by
    show SPComp.bind (SPComp.bind c _) _ = c
    rw [SPComp.bind_assoc]
    conv_rhs => rw [← SPComp.bind_pure c]
    congr 1; funext x; cases x with
    | inl a => simp [SPComp.pure_bind]
    | inr k =>
      simp only [SPComp.pure_bind]
      exact congrArg SPComp.pure (congrArg Sum.inr (toRoundM_ofRoundM n k))

set_option maxHeartbeats 800000 in
theorem ofRoundM_toRoundM {α : Type} :
    (n : Nat) → (c : ITreeN n emptyEvSig α) → ofRoundM n (toRoundM n c) = c
  | 0, _ => rfl
  | n + 1, c => by
    show SPComp.bind (SPComp.bind c _) _ = c
    rw [SPComp.bind_assoc]
    conv_rhs => rw [← SPComp.bind_pure c]
    congr 1; funext x; cases x with
    | inl a => simp [SPComp.pure_bind]
    | inr s => cases s with
      | inl k =>
        simp only [SPComp.pure_bind]
        exact congrArg SPComp.pure (congrArg (Sum.inr ∘ Sum.inl) (ofRoundM_toRoundM n k))
      | inr vc => exact vc.1.elim

end UCMonad.ITreeNUC
