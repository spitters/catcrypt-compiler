/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Self-Contained RustM Monad

Minimal, standalone copy of the `RustM` monad from hax-lib, providing just
enough to support `UCMonad.RustMBridge` and `CTypeBridge` without depending
on the `hax-lib` package.

## What is provided

* `Error` — error cases (assertion failure, overflow, out-of-bounds, etc.)
* `RustM` — the result monad: `.ok v | .fail e | .div`
* `Monad RustM`, `LawfulMonad RustM`
* `RustM.isOk`, `RustM.of_isOk` — predicates and extraction
* `PanicFree` — predicate witnessing that a `RustM` function never errors

## Design

This file is intentionally minimal: it does NOT include WP instances,
loop combinators, checked arithmetic, or array operations. Those belong
to the old hax-lib `Rust_primitives` and are not needed for the UC bridge.
-/

@[expose] public section

set_option autoImplicit false

/-- Error cases for `RustM` computations.
    Mirrors Rust's panic/error modes. -/
inductive Error where
  | assertionFailure
  | integerOverflow
  | divisionByZero
  | arrayOutOfBounds
  | maximumSizeExceeded
  | panic
  | undef
  deriving Repr, BEq, DecidableEq

/-- The `RustM` monad, representing possible results of Rust computations.
    * `.ok v` — successful completion with value `v`
    * `.fail e` — runtime error (panic, overflow, out-of-bounds, etc.)
    * `.div` — divergence (non-termination) -/
inductive RustM.{u} (α : Type u) where
  | ok (v : α) : RustM α
  | fail (e : Error) : RustM α
  | div
  deriving Repr, BEq, DecidableEq, Inhabited

namespace RustM

@[simp]
instance instPure : Pure RustM where
  pure x := .ok x

@[simp]
def bind {α β : Type} (x : RustM α) (f : α → RustM β) : RustM β :=
  match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

@[simp]
instance instMonad : Monad RustM where
  pure := pure
  bind := RustM.bind

@[simp]
instance instLawfulMonad : LawfulMonad RustM where
  id_map x := by cases x <;> rfl
  map_const := by intros; rfl
  seqLeft_eq x y := by
    simp only [SeqLeft.seqLeft, Seq.seq, Functor.map, bind]
    cases x <;> simp <;> cases y <;> rfl
  seqRight_eq x y := by
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, bind]
    cases x <;> simp <;> cases y <;> rfl
  pure_seq g x := by rfl
  bind_pure_comp f x := by rfl
  bind_map f x := by cases f <;> rfl
  pure_bind x f := by rfl
  bind_assoc x f g := by cases x <;> rfl

/-- Is a `RustM` computation successful? -/
@[reducible]
def isOk {α : Type} (x : RustM α) : Bool :=
  match x with
  | .ok _ => true
  | _ => false

/-- Extract the value from a successful `RustM` computation. -/
@[reducible]
def of_isOk {α : Type} (x : RustM α) (_ : RustM.isOk x) : α :=
  match x with
  | .ok v => v

@[simp]
theorem ok_of_isOk {α : Type} (v : α) (h : isOk (ok v)) :
    (ok v).of_isOk h = v := rfl

/-- `IsOk x` witnesses that `x = .ok v` for some `v`. -/
def IsOk {α : Type} (x : RustM α) : Prop := ∃ v, x = .ok v

@[simp] theorem isOk_ok {α : Type} {v : α} : IsOk (.ok v) := ⟨v, rfl⟩
@[simp] theorem isOk_pure {α : Type} {a : α} : IsOk (pure a : RustM α) := ⟨a, rfl⟩

theorem not_isOk_fail {α : Type} {e : Error} : ¬ IsOk (.fail e : RustM α) := by
  intro ⟨_, h⟩; exact absurd h (by intro hc; cases hc)

theorem not_isOk_div {α : Type} : ¬ IsOk (.div : RustM α) := by
  intro ⟨_, h⟩; exact absurd h (by intro hc; cases hc)

@[simp] theorem ok_bind {α β : Type} (v : α) (f : α → RustM β) :
    (RustM.ok v >>= f) = f v := rfl

theorem isOk_bind {α β : Type} {x : RustM α} {f : α → RustM β}
    (hx : IsOk x) (hf : ∀ v, IsOk (f v)) : IsOk (x >>= f) := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨w, hw⟩ := hf v
  exact ⟨w, by simp only [hv, ok_bind, hw]⟩

@[simp] theorem fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e >>= f) = .fail e := rfl

@[simp] theorem div_bind {α β : Type} (f : α → RustM β) :
    (RustM.div >>= f) = .div := rfl

/-- Extract the value from a successful computation, or return `default`. -/
def extractPure {α : Type} [Inhabited α] (x : RustM α) : α :=
  match x with
  | .ok v => v
  | _ => default

theorem extractPure_ok {α : Type} [Inhabited α] {x : RustM α} {v : α}
    (h : x = .ok v) : extractPure x = v := by
  subst h; rfl

theorem ok_extractPure {α : Type} [Inhabited α] (x : RustM α) (h : IsOk x) :
    x = .ok (extractPure x) := by
  obtain ⟨v, hv⟩ := h; subst hv; rfl

/-- Hax uses `failure` for unimplemented features. Maps to `RustM.fail .panic`. -/
def failure {α : Type} (_msg _label : String) : RustM α := .fail .panic

end RustM
