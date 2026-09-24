/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative

/-!
# DR-collapse — the security layer over the unified crypto dialect

This is the **security layer over the `catCryptDialect` `SPComp`
interpretation**: security holds *over the crypto dialect's own `SPComp`
interpretation*. There is one security IR, and it is `catCryptDialect`.

The OTP and peephole dialect programs and their distribution-equality security
results are defined and proved **natively on `catCryptDialect`** in
`CryptoDialectSecurityNative.lean` (`otpReal_dialect`/`otpIdeal_dialect`, the
XOR-bijection and `bvAnd`-self peephole images, and the `*_dialect_secure_native`
distance-`0` theorems), computing the `SPComp` distance through `Com.denoteSP`
and the uniform-sample-XOR bijection. This module re-exports that native layer.

**0 axioms**; all goals closed.

## Observational equivalence and statistical distance on the dialect

This module also carries the dialect-side `comEquiv` / `comSdist` pseudometric
on `Com catCryptDialect` programs (computed through `Com.denoteSP`):
`comSdist_of_equiv`, `comSdist_symm` and `comSdist_triangle` give the
reflexivity-at-0, symmetry and triangle-inequality structure of a pseudometric
over the MLIR-aligned dialect's own `SPComp` interpretation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurity

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open scoped ENNReal

/-! ## Observational equivalence of dialect programs -/

/-- Observational equivalence of `catCryptDialect` programs: equal `SPComp`
    denotation for all valuations. -/
def comEquiv {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (p q : Com catCryptDialect Γ t) : Prop :=
  ∀ V : Ctxt.Valuation Γ, Com.denoteSP p V = Com.denoteSP q V

@[refl]
theorem comEquiv_refl {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (p : Com catCryptDialect Γ t) : comEquiv p p :=
  fun _ => rfl

@[symm]
theorem comEquiv_symm {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {p q : Com catCryptDialect Γ t} (h : comEquiv p q) : comEquiv q p :=
  fun V => (h V).symm

theorem comEquiv_trans {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {p q r : Com catCryptDialect Γ t}
    (h₁ : comEquiv p q) (h₂ : comEquiv q r) : comEquiv p r :=
  fun V => (h₁ V).trans (h₂ V)

/-! ## Statistical distance between dialect programs -/

/-- Statistical distance between `catCryptDialect` programs: supremum over all
    valuations of the `SPComp` `sdist`. -/
noncomputable def comSdist {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (p q : Com catCryptDialect Γ t) : ℝ≥0∞ :=
  ⨆ V : Ctxt.Valuation Γ,
    sdist (fun (_ : Unit) => Com.denoteSP p V) (fun (_ : Unit) => Com.denoteSP q V)

/-- `comEquiv` implies `comSdist = 0`. -/
theorem comSdist_of_equiv {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {p q : Com catCryptDialect Γ t} (h : comEquiv p q) :
    comSdist p q = 0 := by
  simp only [comSdist]
  apply le_antisymm
  · apply iSup_le; intro V
    have : (fun (_ : Unit) => Com.denoteSP p V) = (fun (_ : Unit) => Com.denoteSP q V) :=
      funext fun _ => h V
    rw [this, sdist_self]
  · exact zero_le

/-- `comSdist` is symmetric. -/
theorem comSdist_symm {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (p q : Com catCryptDialect Γ t) : comSdist p q = comSdist q p := by
  simp only [comSdist]
  congr 1; funext V; exact sdist_sym _ _

/-- `comSdist` satisfies the triangle inequality. -/
theorem comSdist_triangle {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (p q r : Com catCryptDialect Γ t) :
    comSdist p r ≤ comSdist p q + comSdist q r := by
  apply iSup_le; intro V
  calc sdist (fun _ => Com.denoteSP p V) (fun _ => Com.denoteSP r V)
      ≤ sdist (fun _ => Com.denoteSP p V) (fun _ => Com.denoteSP q V) +
        sdist (fun _ => Com.denoteSP q V) (fun _ => Com.denoteSP r V) :=
        sdist_triangle _ _ _
    _ ≤ comSdist p q + comSdist q r :=
        add_le_add (le_iSup_of_le V le_rfl) (le_iSup_of_le V le_rfl)

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurity
