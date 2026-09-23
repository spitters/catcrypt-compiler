/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived

/-!
# The memory footprint of the shipped point addition

The cells each canonical part of `ed25519_point_add` reads or writes lie in `paCells`.
The checks run against `paCellOK`, the predicate form of that cell list, and
`footOK_of_footOKP` carries each one to the list form the rest of the proof uses.

Each check evaluates `canonFromD` over its part, so the ten of them by `decide +kernel`
retain about a gigabyte each and exceed the memory of a 14 GB box; by `native_decide`
they cost seconds, at the price of `Lean.ofReduceBool` in the axioms of everything
downstream. The traversal is the same one the part checks of `Ed25519PointAddCut01` to
`Cut10` already perform, so folding the footprint into those checks would remove both
the second traversal and the axiom.

## Main results

* `paCellOK_mem`: the predicate implies membership in `paCells`.
* `pa_foot1` … `pa_foot10`: the footprint of each canonical part.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-- The cells the canonical block reads or writes: the sixteen output limbs at `%rdi`, the
    thirty-two input limbs at `%rsi`, and the stack cells at `-128` and `0, 8, …, 392`. -/
def paCells : List (String × Int) :=
  (List.range 16).map (fun i => ("%rdi", ((8 * i : Nat) : Int))) ++
  (List.range 32).map (fun i => ("%rsi", ((8 * i : Nat) : Int))) ++
  (("%rsp", -128) :: (List.range 50).map (fun i => ("%rsp", ((8 * i : Nat) : Int))))

/-- The cells of `paCells`, as a predicate on base and offset: the three groups are the
    ranges `%rdi + 8i` for `i < 16`, `%rsi + 8i` for `i < 32`, and `%rsp` at `-128` and at
    `8i` for `i < 50`. -/
def paCellOK (k : String × Int) : Bool :=
  (k.1 == "%rdi" && decide (0 ≤ k.2) && decide (k.2 < 128) && k.2 % 8 == 0) ||
  (k.1 == "%rsi" && decide (0 ≤ k.2) && decide (k.2 < 256) && k.2 % 8 == 0) ||
  (k.1 == "%rsp" &&
    ((k.2 == -128) || (decide (0 ≤ k.2) && decide (k.2 < 400) && k.2 % 8 == 0)))

theorem paCellOK_mem (k : String × Int) (h : paCellOK k = true) : k ∈ paCells := by
  obtain ⟨b, o⟩ := k
  simp only [paCellOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  simp only [paCells]
  rcases h with (⟨⟨⟨hb, h0⟩, h1⟩, h8⟩ | ⟨⟨⟨hb, h0⟩, h1⟩, h8⟩) | ⟨hb, h⟩
  · subst hb
    refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
      (List.mem_map.2 ⟨o.toNat / 8, List.mem_range.2 (by omega), ?_⟩))))
    simp only [Prod.mk.injEq]
    exact ⟨trivial, by omega⟩
  · subst hb
    refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (List.mem_map.2 ⟨o.toNat / 8, List.mem_range.2 (by omega), ?_⟩))))
    simp only [Prod.mk.injEq]
    exact ⟨trivial, by omega⟩
  · subst hb
    refine List.mem_append.2 (Or.inr ?_)
    rcases h with h | ⟨⟨h0, h1⟩, h8⟩
    · exact h ▸ List.mem_cons_self
    · refine List.mem_cons_of_mem _
        (List.mem_map.2 ⟨o.toNat / 8, List.mem_range.2 (by omega), ?_⟩)
      simp only [Prod.mk.injEq]
      exact ⟨trivial, by omega⟩

theorem pa_footP1 :
    footOKP paCellOK (canonFromD shippedBank {} ed25519PointAddShippedPart01) = true := by
  native_decide
theorem pa_footP2 :
    footOKP paCellOK (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02)
      = true := by native_decide
theorem pa_footP3 :
    footOKP paCellOK (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03)
      = true := by native_decide
theorem pa_footP4 :
    footOKP paCellOK (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04)
      = true := by native_decide
theorem pa_footP5 :
    footOKP paCellOK (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05)
      = true := by native_decide
theorem pa_footP6 :
    footOKP paCellOK (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06)
      = true := by native_decide
theorem pa_footP7 :
    footOKP paCellOK (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07)
      = true := by native_decide
theorem pa_footP8 :
    footOKP paCellOK (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08)
      = true := by native_decide
theorem pa_footP9 :
    footOKP paCellOK (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09)
      = true := by native_decide
theorem pa_footP10 :
    footOKP paCellOK (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10)
      = true := by native_decide


theorem pa_foot1 :
    footOK paCells (canonFromD shippedBank {} ed25519PointAddShippedPart01) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP1
theorem pa_foot2 :
    footOK paCells (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP2
theorem pa_foot3 :
    footOK paCells (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP3
theorem pa_foot4 :
    footOK paCells (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP4
theorem pa_foot5 :
    footOK paCells (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP5
theorem pa_foot6 :
    footOK paCells (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP6
theorem pa_foot7 :
    footOK paCells (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP7
theorem pa_foot8 :
    footOK paCells (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP8
theorem pa_foot9 :
    footOK paCells (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP9
theorem pa_foot10 :
    footOK paCells (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10) = true :=
  footOK_of_footOKP paCellOK_mem pa_footP10

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
