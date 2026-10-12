/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

@[expose] public section

set_option autoImplicit false

/-!
# Uniqueness of the ABI reading of a valuation

`AbiValOf σ sa V` reads every register variable and every array variable of `V` off the
entry state `sa`. On a context whose types are all registers or stack arrays it therefore
determines `V`: two valuations that `σ` reads off the same entry state are equal.

## Main results

* `JasminTy.regArrB`, `regArrCtxB`: the test that a type, and every type of a context, is a
  register or a stack array.
* `abiValOf_unique`: two valuations of a context of registers and stack arrays read off the
  same entry state are equal.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)

/-- The test that a type is a register or a stack array. -/
def JasminTy.regArrB : JasminTy → Bool
  | .reg _ => true
  | .stackArr _ _ => true
  | _ => false

/-- The test that every type of the context `Γ` is a register or a stack array. -/
def regArrCtxB (Γ : Ctxt jasminDialect) : Bool := Γ.all JasminTy.regArrB

/-- The type of a variable of a context of registers and stack arrays is a register or a
    stack array. -/
theorem regArrB_of_var : {Γ : Ctxt jasminDialect} → regArrCtxB Γ = true →
    {t : JasminTy} → Ctxt.Var Γ t → JasminTy.regArrB t = true
  | _ :: _, h, _, .here => by
      simp only [regArrCtxB, List.all_cons, Bool.and_eq_true] at h
      exact h.1
  | _ :: _, h, _, .there v => by
      simp only [regArrCtxB, List.all_cons, Bool.and_eq_true] at h
      exact regArrB_of_var h.2 v

/-- **The ABI reading determines the valuation** on a context of registers and stack
    arrays: two valuations that `σ` reads off the same entry state `sa` are equal. -/
theorem abiValOf_unique {σ : AbiLayout} {sa : AState} {Γ : Ctxt jasminDialect}
    (hΓ : regArrCtxB Γ = true) {V₁ V₂ : Ctxt.Valuation Γ}
    (h₁ : AbiValOf σ sa V₁) (h₂ : AbiValOf σ sa V₂) : V₁ = V₂ := by
  refine BlockLoweringCPS.valuation_ext V₁ V₂ fun {t} v => ?_
  cases t with
  | reg w =>
      obtain ⟨a, ha, -, hw, e₁⟩ := h₁.reg v
      obtain ⟨b, hb, -, hw', e₂⟩ := h₂.reg v
      rw [ha, Option.some.injEq] at hb
      subst hb hw
      exact e₁.trans e₂.symm
  | stackArr w n =>
      obtain ⟨a, ha, -, hw, e₁⟩ := h₁.arr v
      obtain ⟨b, hb, -, hw', e₂⟩ := h₂.arr v
      rw [ha, Option.some.injEq] at hb
      subst hb hw
      exact e₁.trans e₂.symm
  | inlineInt => exact absurd (regArrB_of_var hΓ v) (by decide)
  | bool => exact absurd (regArrB_of_var hΓ v) (by decide)

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
