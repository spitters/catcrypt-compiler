/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Hax.CType
public import CatCrypt.Hax.CType
public meta import CatCrypt.Hax.CTypeValue
public import CatCrypt.Hax.CTypeValue

/-!
# Vacuity Audit for Hax Bridge Infrastructure

Verifies that core CType operations are non-vacuous:
inject is injective, project roundtrips, types are nontrivial, etc.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.VacuityAudit

/-! ## 1. CType.inject is injective (proven in CTypeValue) -/

-- Re-export: inject_injective already proved in CTypeValue.lean
-- These examples demonstrate it works for specific types:
example : Function.Injective (CType.inject .u8) := CType.inject_injective .u8
example : Function.Injective (CType.inject .u32) := CType.inject_injective .u32
example : Function.Injective (CType.inject (.array .u8 16)) :=
  CType.inject_injective (.array .u8 16)
example : Function.Injective (CType.inject (.array .u8 32)) :=
  CType.inject_injective (.array .u8 32)

/-! ## 2. Project roundtrips (proven in CTypeValue) -/

example (v : UInt8) : CType.project .u8 (CType.inject .u8 v) = some v :=
  CType.project_inject .u8 v
example (v : Vector UInt8 16) :
    CType.project (.array .u8 16) (CType.inject (.array .u8 16) v) = some v :=
  CType.project_inject (.array .u8 16) v

/-! ## 3. Types are nontrivial (have distinct elements) -/

-- These use native_decide to check nontriviality at compile time
theorem u8_nontrivial : (0 : UInt8) ≠ (1 : UInt8) := by native_decide
theorem u32_nontrivial : (0 : UInt32) ≠ (1 : UInt32) := by native_decide
theorem u64_nontrivial : (0 : UInt64) ≠ (1 : UInt64) := by native_decide

/-! ## 4. Fintype cardinalities are correct -/

-- These verify the type universe is non-degenerate
theorem u8_card_pos : 0 < @Fintype.card UInt8 CType.fintypeUInt8 := by
  apply Fintype.card_pos

/-! ## 5. inject distinguishes distinct values -/

theorem inject_u8_distinct :
    CType.inject .u8 (0 : UInt8) ≠ CType.inject .u8 (1 : UInt8) := by
  intro h
  have := CType.inject_injective .u8 h
  exact absurd this (by native_decide)

theorem inject_u32_distinct :
    CType.inject .u32 (0 : UInt32) ≠ CType.inject .u32 (1 : UInt32) := by
  intro h
  have := CType.inject_injective .u32 h
  exact absurd this (by native_decide)

/-! ## 6. Array injection preserves distinctness -/

theorem inject_array_distinct :
    CType.inject (.array .u8 1) (#v[0] : Vector UInt8 1) ≠
    CType.inject (.array .u8 1) (#v[1] : Vector UInt8 1) := by
  intro h
  have := CType.inject_injective (.array .u8 1) h
  simp [Vector.ext_iff] at this

end CatCrypt.Hax.VacuityAudit
