/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Hax.CType
public import HaxLean.Value

/-!
# CType ↔ Value Bridge

Injection and projection functions between the typed universe `CType.denote`
and the untyped runtime `Hax.Value` of the hax reference interpreter.

## Main definitions

* `CType.inject` — embed `τ.denote` into `Value`
* `CType.project` — extract `τ.denote` from `Value` (partial)
* `CType.project_inject` — roundtrip: `project (inject v) = some v`
* `CType.inject_injective` — `inject` is injective for each `τ`

## Integer representation

A fixed-width integer is injected as the width-indexed `Value.uint w n` with
`n` the integer's `toNat` (`u8 ↦ .w8`, …, `usize ↦ .wsize`), the value
`Value.ofLit` produces for a `uintLit`.  Projection reads both `Value.uint w n`
at the matching width and the width-erased `Value.int n` that `defaultBuiltins`
arithmetic produces, in either case only when `n` lies below the width's
modulus.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax

open _root_.Hax (Value)

namespace CType

/-! ## Injection: typed → untyped -/

/-- Embed a typed value into the untyped `Value` representation. -/
def inject : (τ : CType) → τ.denote → Value
  | .u8, n => .uint .w8 n.toNat
  | .u16, n => .uint .w16 n.toNat
  | .u32, n => .uint .w32 n.toNat
  | .u64, n => .uint .w64 n.toNat
  | .u128, n => .uint .w128 n.toNat
  | .usize, n => .uint .wsize n.toNat
  | .bool, b => .bool b
  | .unit, () => .unit
  | .pair a b, (x, y) => .tuple [a.inject x, b.inject y]
  | .array elem n, v => .tuple ((List.finRange n).map fun i => elem.inject v[i])
  | .option _, none => .option none
  | .option a, some x => .option (some (a.inject x))
  | .result ok _, .inl x => .result true (ok.inject x)
  | .result _ err, .inr x => .result false (err.inject x)

/-! ## Projection: untyped → typed -/

/-- Try to extract a typed value from an untyped `Value`.
    Returns `none` on type mismatch. -/
def project : (τ : CType) → Value → Option τ.denote
  | .u8, .uint .w8 n => if n < 256 then some (UInt8.ofNat n) else none
  | .u8, .int n =>
    if 0 ≤ n ∧ n < 256 then some (UInt8.ofNat n.toNat) else none
  | .u16, .uint .w16 n => if n < 65536 then some (UInt16.ofNat n) else none
  | .u16, .int n =>
    if 0 ≤ n ∧ n < 65536 then some (UInt16.ofNat n.toNat) else none
  | .u32, .uint .w32 n => if n < 4294967296 then some (UInt32.ofNat n) else none
  | .u32, .int n =>
    if 0 ≤ n ∧ n < 4294967296 then some (UInt32.ofNat n.toNat) else none
  | .u64, .uint .w64 n =>
    if n < 18446744073709551616 then some (UInt64.ofNat n) else none
  | .u64, .int n =>
    if 0 ≤ n ∧ n < 18446744073709551616 then some (UInt64.ofNat n.toNat) else none
  | .u128, .uint .w128 n => if n < 2 ^ 128 then some (BitVec.ofNat 128 n) else none
  | .u128, .int n =>
    if 0 ≤ n ∧ n < 2 ^ 128 then some (BitVec.ofNat 128 n.toNat) else none
  | .usize, .uint .wsize n =>
    if n < 18446744073709551616 then some (UInt64.ofNat n) else none
  | .usize, .int n =>
    if 0 ≤ n ∧ n < 18446744073709551616 then some (UInt64.ofNat n.toNat) else none
  | .bool, .bool b => some b
  | .unit, .unit => some ()
  | .pair a b, .tuple [x, y] => do
    let vx ← a.project x
    let vy ← b.project y
    some (vx, vy)
  | .array elem n, .tuple vs =>
    if h : vs.length = n then
      projectList elem vs n h
    else none
  | .option _, .option none => some none
  | .option a, .option (some v) => Option.map some (a.project v)
  | .result ok _, .result true payload => Option.map Sum.inl (ok.project payload)
  | .result _ err, .result false payload => Option.map Sum.inr (err.project payload)
  | _, _ => none
where
  /-- Project a list of values with known length into a `Vector`,
      preserving element order (first list element → index 0). -/
  projectList (elem : CType) : (vs : List Value) → (n : Nat) →
      vs.length = n → Option (Vector elem.denote n)
    | [], 0, _ => some #v[]
    | v :: vs, n + 1, h => do
      let x ← elem.project v
      let rest ← projectList elem vs n (by simp [List.length_cons] at h; omega)
      some ⟨#[x] ++ rest.toArray, by simp [rest.size_toArray]; omega⟩
    | [], _ + 1, h => by simp at h
    | _ :: _, 0, h => by simp at h

/-! ## Roundtrip helpers -/

/-- Helper: `projectList` applied to a mapped list recovers the list as a vector. -/
theorem projectList_map_inject (elem : CType)
    (h_elem : ∀ (x : elem.denote), elem.project (elem.inject x) = some x) :
    ∀ (xs : List elem.denote) (n : Nat) (hlen : (xs.map elem.inject).length = n),
    project.projectList elem (xs.map elem.inject) n hlen =
      some ⟨xs.toArray, by simp at hlen; rw [← hlen]; simp⟩
  | [], 0, _ => by simp [project.projectList]
  | x :: xs, n + 1, hlen => by
    simp only [List.map_cons, project.projectList, h_elem x]
    have hlen' : (xs.map elem.inject).length = n := by simp at hlen ⊢; omega
    rw [projectList_map_inject elem h_elem xs n hlen']; simp
  | [], n + 1, hlen => by simp at hlen
  | _ :: _, 0, hlen => by simp at hlen

/-! ## Roundtrip theorem -/

/-- Roundtrip: projecting an injected value recovers the original.

    Integer cases use `UIntN.ofNat ∘ toNat = id` with the `toNat` bound. -/
theorem project_inject : (τ : CType) → (v : τ.denote) →
    τ.project (τ.inject v) = some v
  | .bool, b => by simp [inject, project]
  | .unit, () => by simp [inject, project]
  | .u8, n => by
    have := n.toNat_lt
    simp [inject, project, this]
  | .u16, n => by
    have := n.toNat_lt
    simp [inject, project, this]
  | .u32, n => by
    have := n.toNat_lt
    simp [inject, project, this]
  | .u64, n => by
    have := n.toNat_lt
    simp [inject, project, this]
  | .u128, n => by
    have := n.isLt
    simp [inject, project, this]
  | .usize, n => by
    have := n.toNat_lt
    simp [inject, project, this]
  | .pair a b, (x, y) => by
    simp only [inject, project, project_inject a x, project_inject b y]
    rfl
  | .option _, none => by simp [inject, project]
  | .option a, some x => by
    simp only [inject, project, project_inject a x, Option.map_some]
  | .result ok _, .inl x => by
    simp only [inject, project, project_inject ok x, Option.map_some]
  | .result _ err, .inr x => by
    simp only [inject, project, project_inject err x, Option.map_some]
  | .array elem n, v => by
    simp only [inject, project]
    have hlen : ((List.finRange n).map fun i => elem.inject v[i]).length = n := by simp
    rw [dif_pos hlen]
    -- Key: (finRange n).map (inject ∘ v[·]) = (ofFn v[·]).map inject
    have hmapeq : (List.finRange n).map (fun i => elem.inject v[i]) =
        (List.ofFn fun i : Fin n => v[i]).map elem.inject := by
      simp [List.ofFn_eq_map, List.map_map, Function.comp]
    -- Transport projectList across the equality (revert hlen to handle dependent proof)
    have hlen2 : ((List.ofFn fun i : Fin n => v[i]).map elem.inject).length = n := by simp
    have htransport : project.projectList elem
        ((List.finRange n).map fun i => elem.inject v[i]) n hlen =
        project.projectList elem
        ((List.ofFn fun i : Fin n => v[i]).map elem.inject) n hlen2 := by
      revert hlen; rw [hmapeq]; intro hlen; rfl
    rw [htransport, projectList_map_inject elem (project_inject elem) _ n _]
    congr 1; ext i
    simp [Vector.getElem_mk, Array.getElem_ofFn]

/-- `inject` is injective for each `τ`.
    Follows from `project_inject` (left-inverse implies injective). -/
theorem inject_injective (τ : CType) : Function.Injective τ.inject := by
  intro a b hab
  have := congrArg τ.project hab
  rw [project_inject, project_inject] at this
  exact Option.some_injective _ this

end CType

end CatCrypt.Hax
