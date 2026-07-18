/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps

/-!
# Field derived `double` / `square` on the HIGH FIELD DIALECT

The prime-field derived-arithmetic ops `field.double` (`a ↦ a + a`) and
`field.square` (`a ↦ a * a`) of fractalyze/prime-ir — factored as standalone
correspondence ops in `FieldDerivedOps` (`DerivedOp.fieldDouble`/`fieldSquare`) —
are here realised as **one-op `Com fieldDialect` schedules** over the primitive
`FieldOp` leaves, exactly mirroring `EcLineFieldEmit.ecLineProg` /
`EcPointAddFieldEmit.ecAddX3Prog`:

    fieldDoubleProg : Com fieldDialect [fp p] (fp p)   (one `fAdd a a`)
      --(fieldDouble_field_denote : denote = FieldDerivedOps.fieldDoubleF, rfl)-->
    fieldSquareProg : Com fieldDialect [fp p] (fp p)   (one `fMul a a`)
      --(fieldSquare_field_denote : denote = FieldDerivedOps.fieldSquareF, rfl)-->

Doubling is one `FieldOp.fAdd` of the input with itself, squaring is one
`FieldOp.fMul` of the input with itself; both denote (`rfl`) to the
`FieldDerivedOps` leaf functions, since the field-op denotations `fAddF`/`fMulF`
are `ZMod p`'s native `+`/`*`.

## What is proved here

* `fieldDoubleProg` / `fieldSquareProg` — the two one-op `Com fieldDialect`
  schedules over `Γ₀ = [fp p]`, built straight from `FieldOp.fAdd`/`FieldOp.fMul`.
* `fieldDouble_field_denote` / `fieldSquare_field_denote` — the field-dialect
  Coms denote EXACTLY the `FieldDerivedOps` leaf functions `fieldDoubleF` /
  `fieldSquareF` (`rfl`).

`field.powui` (the fixed-exponent power `a ↦ a ^ k`) is **not** lowered here: a
constant-exponent power is a multi-`fMul`/square chain (a static mul/square
schedule, cf. the `pow249Spec` Fermat chain), not a one-op schedule, so it is a
larger separate kernel — see `FieldDerivedOps.fieldPowF` for the op and its
Horner recursion.

## Honest classification (read `VIR/DIALECTS.md`)

This is a **denote-preserving `fieldDialect` schedule**, NOT an emit-wired
kernel.  Each schedule descends to jasmin/bytes through the certified
`FieldDescent.fieldComToJasmin_denote` (`Com fieldDialect → Com jasminDialect`,
Stage-2 word-realization carried as the explicit `hVarJ`/`hOpJ`/`hExtJ`
hypotheses, GMP-KAT-gated), exactly as `EcLineFieldEmit.ecLineJasmin_denote` —
we cite that descent here, we do not wire it (these derived forms factor through
the primitive `fAdd`/`fMul` emit kernels, `FieldEmitGoldenPath`).

**0 sorries.**
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedFieldEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps

variable {p : Nat}

/-! ## 1. The input context and the De Bruijn variable

`Γ₀ = [fp p]` holds the single prime-field operand `a` at index `0`. -/

/-- The starting context: the single prime-field operand `a`. -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect := [FieldTy.fp p]

/-- De Bruijn variable for `a` (index 0). -/
def va : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .here

/-- The valuation `⟨a⟩`. -/
def eval (a : ZMod p) : Ctxt.Valuation (Γ₀ p) := .cons a .nil

/-! ## 2. The `double` schedule `r = a + a` as a one-op `Com fieldDialect`

One `FieldOp.fAdd` of the input with itself. -/

/-- The field-doubling schedule `r = a + a` as a `Com fieldDialect` over `Γ₀`. -/
def fieldDoubleProg : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  -- r = a + a
  .var (.mk (.fAdd p) rfl (.cons va (.cons va .nil)))
  (.ret .here)

/-! ## 3. The `square` schedule `r = a * a` as a one-op `Com fieldDialect`

One `FieldOp.fMul` of the input with itself. -/

/-- The field-squaring schedule `r = a * a` as a `Com fieldDialect` over `Γ₀`. -/
def fieldSquareProg : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  -- r = a * a
  .var (.mk (.fMul p) rfl (.cons va (.cons va .nil)))
  (.ret .here)

/-! ## 4. The denotation ties — `denote = FieldDerivedOps.field{Double,Square}F`

Both are `rfl` (the field-op denotations `fAddF`/`fMulF` are `ZMod p`'s native
`+`/`*`), the same `rfl`-closed-form shape as `EcLineFieldEmit.ecLine_field_denote`. -/

/-- **`fieldDoubleProg` denotes exactly the derived-op leaf `a ↦ a + a`.** -/
theorem fieldDouble_field_denote (a : ZMod p) :
    (fieldDoubleProg (p := p)).denote (eval a) = fieldDoubleF p a := rfl

/-- **`fieldSquareProg` denotes exactly the derived-op leaf `a ↦ a * a`.** -/
theorem fieldSquare_field_denote (a : ZMod p) :
    (fieldSquareProg (p := p)).denote (eval a) = fieldSquareF p a := rfl

/-! ## 5. Tiny concrete smoke check (NOT a kernel KAT)

Over `ZMod 7`: doubling `3` gives `6`; squaring `3` gives `9 = 2 (mod 7)`. -/

example : (fieldDoubleProg (p := 7)).denote (eval 3) = (6 : ZMod 7) := rfl
example : (fieldSquareProg (p := 7)).denote (eval 3) = (2 : ZMod 7) := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedFieldEmit
