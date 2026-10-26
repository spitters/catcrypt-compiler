/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg

@[expose] public section

/-!
# Identity laws of argument transports and calls

`transArgs m tr` carries an argument vector along a type map `m` and a value transport `tr`.
Along the identity it returns the vector, up to the equality `ts.map id = ts`
(`transArgs_id_heq`). A call at a signature and an argument vector heterogeneously equal to
another signature and vector returns the same results (`call_eq_map_of_heq`). The dialect
category (`DialectCategoryBase`) and the legalisation passes of the region route
(`Haxc/LegalizeBy`) both use these two facts.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

namespace BlockLoweringExtend

variable {T : Type} [TyDenote T]

/-- The transport of an argument vector along the identity type map and the identity
    value transport is the vector. -/
theorem transArgs_id_heq : {ts : List T} → (x : HVector (fun t => ⟦t⟧) ts) →
    transArgs (fun t => t) (fun x => x) x ≍ x
  | [], .nil => HEq.rfl
  | _ :: ts, .cons x xs => by
      have ih := transArgs_id_heq xs
      change HVector.cons x (transArgs (fun t => t) (fun x => x) xs) ≍ HVector.cons x xs
      generalize transArgs (fun t => t) (fun x => x) xs = ys at ih
      have hts : ts.map (fun t => t) = ts := List.map_id' ts
      revert ys
      rw [hts]
      intro ys ih
      rw [eq_of_heq ih]

end BlockLoweringExtend

open Ctxt (Valuation)

/-- A call at a signature and an argument valuation equal to another signature and
    argument valuation returns the same results, read along the equality of the result
    types. -/
theorem call_eq_map_of_heq {d : Dialect.{0, 0}} [TyDenote d.Ty] (E : CallEnv d) (f : String)
    {as₁ as₂ rs₁ rs₂ : List d.Ty} (has : as₁ = as₂) (hrs : rs₁ = rs₂)
    {x₁ : Valuation as₁} {x₂ : Valuation as₂} (hx : x₁ ≍ x₂) {α : Type} (o : Option α)
    (T₁ : α → Valuation rs₁) (T₂ : α → Valuation rs₂) (hT : ∀ r, T₁ r ≍ T₂ r)
    (h : E.call f as₂ rs₂ x₂ = o.map T₂) : E.call f as₁ rs₁ x₁ = o.map T₁ := by
  subst has hrs
  obtain rfl := eq_of_heq hx
  obtain rfl : T₁ = T₂ := funext fun r => eq_of_heq (hT r)
  exact h

end CatCrypt.Crypto.SecureCompilation.VIR
