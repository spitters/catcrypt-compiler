/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.SemanticsCF

/-!
# The control-flow contract of hax-lean's width-aware builtin tables

`Hax.Builtins.DeepNoControlFlow bi` says that the builtin table `bi` returns a
value without `controlFlow` wrappers at any depth whenever its arguments have
none.  hax-lean's control-flow pipeline theorems (`pipeline_correct'`,
`pipeline_full_correct`) take it as the contract on the table, and hax-lean
discharges it for `defaultBuiltins`.

This module discharges it for the width-aware tables of `HaxLean/Semantics.lean`.

## Main results

* `deepNoControlFlow_orElse` — a table that tries one contract-satisfying table
  and falls back to another satisfies the contract;
* one lemma per component table (`widthArithOps`, `widthBitwiseOps`,
  `widthCmpOps`, `widthCastOps`, `widthArrayOps`, `signedArithOps`,
  `signedCmpOps`);
* `widthOps_deepNoControlFlow`, `panicOps_deepNoControlFlow`,
  `widthAwareBuiltins_deepNoControlFlow` and `fullBuiltins_deepNoControlFlow`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (Value Builtins widthArithOps widthBitwiseOps widthCmpOps widthCastOps
  widthArrayOps signedArithOps signedCmpOps widthOps panicOps widthAwareBuiltins
  fullBuiltins defaultBuiltins wrapUint wrapSint)

/-! ## Lists of values -/

/-- A list of values has no `controlFlow` wrapper at any depth exactly when each of
    its elements has none. -/
theorem deepNoControlFlowList_iff (vs : List Value) :
    Value.deepNoControlFlow.deepNoControlFlowList vs = true ↔
      ∀ v ∈ vs, v.deepNoControlFlow = true := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih]

/-- An array value has no `controlFlow` wrapper at any depth exactly when each of
    its elements has none. -/
theorem deepNoControlFlow_array_iff (vs : List Value) :
    (Value.array vs).deepNoControlFlow = true ↔ ∀ v ∈ vs, v.deepNoControlFlow = true :=
  deepNoControlFlowList_iff vs

/-! ## Combinators -/

/-- A table that tries a `DeepNoControlFlow` table and falls back to another is
    `DeepNoControlFlow`. -/
theorem deepNoControlFlow_orElse (t₁ t₂ : Builtins)
    (h₁ : Builtins.DeepNoControlFlow t₁) (h₂ : Builtins.DeepNoControlFlow t₂) :
    Builtins.DeepNoControlFlow (fun f a => t₁ f a <|> t₂ f a) := by
  intro f args v h hargs
  cases ht : t₁ f args with
  | some w =>
      simp only [ht, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at h
      exact h ▸ h₁ f args w ht hargs
  | none =>
      simp only [ht, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
      exact h₂ f args v h hargs

/-! ## The component tables -/

/-- The unsigned arithmetic table returns `uint` words only. -/
theorem widthArithOps_deepNoControlFlow : Builtins.DeepNoControlFlow widthArithOps := by
  intro f args v h _
  revert h; unfold widthArithOps
  split <;> intro h <;> (try split at h) <;> cases h <;>
    simp [Value.deepNoControlFlow, wrapUint]

/-- The unsigned bitwise table returns `uint` words only. -/
theorem widthBitwiseOps_deepNoControlFlow : Builtins.DeepNoControlFlow widthBitwiseOps := by
  intro f args v h _
  revert h; unfold widthBitwiseOps
  split <;> intro h <;> cases h <;> simp [Value.deepNoControlFlow, wrapUint]

/-- The unsigned comparison table returns booleans only. -/
theorem widthCmpOps_deepNoControlFlow : Builtins.DeepNoControlFlow widthCmpOps := by
  intro f args v h _
  revert h; unfold widthCmpOps
  split <;> intro h <;> cases h <;> simp [Value.deepNoControlFlow]

/-- The cast table returns scalar values only. -/
theorem widthCastOps_deepNoControlFlow : Builtins.DeepNoControlFlow widthCastOps := by
  intro f args v h _
  revert h; unfold widthCastOps
  split <;> intro h <;> cases h <;> simp [Value.deepNoControlFlow]

/-- The array table returns an element of an argument array other than a
    `controlFlow` value, a length, or an array built from argument values. -/
theorem widthArrayOps_deepNoControlFlow : Builtins.DeepNoControlFlow widthArrayOps := by
  intro f args v h hargs
  have h0 : ∀ {x : Value} {xs : List Value}, args = x :: xs → x.deepNoControlFlow = true :=
    fun hx => hargs _ (hx ▸ List.mem_cons_self)
  revert h; unfold widthArrayOps
  split <;> intro h <;> (try split at h)
  all_goals first
    | (cases h; done)
    | (obtain rfl := Option.some.inj h
       simp [Value.deepNoControlFlow]; done)
    | skip
  case h_1 | h_2.isTrue =>
    obtain ⟨a, ha, hm⟩ := Option.bind_eq_some_iff.mp h
    have hv := (deepNoControlFlow_array_iff _).mp (h0 rfl) a (List.mem_of_getElem? ha)
    cases a <;> first | (cases hm; done) | (cases hm; exact hv)
  case h_4 =>
    obtain rfl := Option.some.inj h
    have hvs := (deepNoControlFlow_array_iff _).mp (h0 rfl)
    refine (deepNoControlFlow_array_iff _).mpr fun y hy => ?_
    rcases List.mem_append.mp hy with hy | hy
    · exact hvs y hy
    · obtain rfl := List.mem_singleton.mp hy
      exact hargs _ (by simp)
  case h_5 | h_6.isTrue =>
    obtain rfl := Option.some.inj h
    refine (deepNoControlFlow_array_iff _).mpr fun y hy => ?_
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hy
    exact h0 rfl
  case h_7 =>
    obtain rfl := Option.some.inj h
    exact (deepNoControlFlow_array_iff _).mpr hargs
  case h_9.isTrue | h_10.isTrue =>
    obtain rfl := Option.some.inj h
    have hvs := (deepNoControlFlow_array_iff _).mp (h0 rfl)
    refine (deepNoControlFlow_array_iff _).mpr fun y hy => ?_
    rcases List.mem_or_eq_of_mem_set hy with hy | rfl
    · exact hvs y hy
    · exact hargs _ (by simp)
  case h_11 =>
    obtain rfl := Option.some.inj h
    have hvs := (deepNoControlFlow_array_iff _).mp (h0 rfl)
    exact (deepNoControlFlow_array_iff _).mpr fun y hy => hvs y (List.mem_reverse.mp hy)
  case h_12 | h_13.isTrue =>
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
    have hvs := (deepNoControlFlow_array_iff _).mp (h0 rfl)
    refine (deepNoControlFlow_array_iff [a, _]).mpr fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hvs _ (List.mem_of_getElem? ha)
    · exact (deepNoControlFlow_array_iff _).mpr fun z hz => hvs z (List.mem_of_mem_eraseIdx hz)

/-- The signed arithmetic table returns `sint` words only. -/
theorem signedArithOps_deepNoControlFlow : Builtins.DeepNoControlFlow signedArithOps := by
  intro f args v h _
  revert h; unfold signedArithOps
  split <;> intro h <;> (try split at h) <;> cases h <;>
    simp [Value.deepNoControlFlow, wrapSint]

/-- The signed comparison table returns booleans only. -/
theorem signedCmpOps_deepNoControlFlow : Builtins.DeepNoControlFlow signedCmpOps := by
  intro f args v h _
  revert h; unfold signedCmpOps
  split <;> intro h <;> cases h <;> simp [Value.deepNoControlFlow]

/-- The signed bitwise table returns signed words only. -/
theorem signedBitwiseOps_deepNoControlFlow : Builtins.DeepNoControlFlow Hax.signedBitwiseOps := by
  intro f args v h _
  revert h; unfold Hax.signedBitwiseOps
  split <;> intro h <;> (try split at h) <;> cases h <;>
    simp [Value.deepNoControlFlow, wrapSint]

/-- The panic table returns a value contained in an argument, or a boolean. -/
theorem panicOps_deepNoControlFlow : Builtins.DeepNoControlFlow panicOps := by
  intro f args v h hargs
  revert h; unfold panicOps
  split <;> intro h
  all_goals first
    | (cases h; done)
    | (cases h; simp [Value.deepNoControlFlow]; done)
    | (cases h
       simp [Value.deepNoControlFlow] at hargs
       first | exact hargs | exact hargs.1 | exact hargs.2)

/-! ## The composite tables -/

/-- `widthOps`, the width-specific operations, never fabricates a control-flow
    value. -/
theorem widthOps_deepNoControlFlow : Builtins.DeepNoControlFlow widthOps :=
  deepNoControlFlow_orElse _ _ widthArithOps_deepNoControlFlow
    (deepNoControlFlow_orElse _ _ widthBitwiseOps_deepNoControlFlow
      (deepNoControlFlow_orElse _ _ widthCmpOps_deepNoControlFlow
        (deepNoControlFlow_orElse _ _ widthCastOps_deepNoControlFlow
          (deepNoControlFlow_orElse _ _ widthArrayOps_deepNoControlFlow
            (deepNoControlFlow_orElse _ _ signedArithOps_deepNoControlFlow
              (deepNoControlFlow_orElse _ _ signedCmpOps_deepNoControlFlow
                signedBitwiseOps_deepNoControlFlow))))))

/-- `widthAwareBuiltins`, `widthOps` with `defaultBuiltins` as fallback, never
    fabricates a control-flow value. -/
theorem widthAwareBuiltins_deepNoControlFlow :
    Builtins.DeepNoControlFlow widthAwareBuiltins := by
  intro f args v h hargs
  unfold widthAwareBuiltins at h
  cases hw : widthOps f args with
  | some w =>
      rw [hw] at h
      exact Option.some.inj h ▸ widthOps_deepNoControlFlow f args w hw hargs
  | none =>
      rw [hw] at h
      exact Builtins.defaultBuiltins_deepNoControlFlow f args v h hargs

/-- `fullBuiltins`, `widthOps` then `panicOps` then `defaultBuiltins`, never
    fabricates a control-flow value. -/
theorem fullBuiltins_deepNoControlFlow : Builtins.DeepNoControlFlow fullBuiltins :=
  deepNoControlFlow_orElse _ _ widthOps_deepNoControlFlow
    (deepNoControlFlow_orElse _ _ panicOps_deepNoControlFlow
      Builtins.defaultBuiltins_deepNoControlFlow)

end CatCrypt.Crypto.Hax
