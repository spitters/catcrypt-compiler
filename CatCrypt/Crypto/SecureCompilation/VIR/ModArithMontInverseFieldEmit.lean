/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverse

/-!
# Montgomery-domain inverse on the HIGH FIELD DIALECT

The Montgomery-domain field inverse `mod_arith.mont_inverse` of
fractalyze/prime-ir — factored as the standalone correspondence op
`ModArithMontInverse.montInverseF rInv x = x⁻¹ · rInv⁻¹ · rInv⁻¹` (`= x⁻¹ · R²`,
since `rInv⁻¹ = R`) — is here realised as a **`Com fieldDialect` schedule** over
the primitive `FieldOp` leaves, exactly mirroring `EcLineFieldEmit.ecLineProg` /
`EcPointAddFieldEmit.ecAddX3Prog`:

    montInverseProg : Com fieldDialect [fp p, fp p] (fp p)   over (x, rInv)
        xi = fInv x        -- x⁻¹
        ri = fInv rInv     -- rInv⁻¹  (= R)
        t  = fMul xi ri    -- x⁻¹ · rInv⁻¹
        r  = fMul t  ri    -- x⁻¹ · rInv⁻¹ · rInv⁻¹  (= x⁻¹ · R²)
        ret r
      --(montInverse_field_denote : denote = ModArithMontInverse.montInverseF rInv x, rfl)-->

The schedule is two field inverses (`FieldOp.fInv`, denoting to `ZMod p`'s native
`⁻¹` = `byInverseF`) and two multiplies (`FieldOp.fMul`).  Because the field-op
denotations are `ZMod p`'s native operations and `*` is left-associative, the
schedule denotes (`rfl`) to `(x⁻¹ * rInv⁻¹) * rInv⁻¹` — definitionally the
`montInverseF` leaf.

## What is proved here

* `montInverseProg` — the four-op `Com fieldDialect` schedule over
  `Γ₀ = [fp p, fp p]` (the inputs `x, rInv`), built straight from
  `FieldOp.fInv`/`FieldOp.fMul`.
* `montInverse_field_denote` — the field-dialect Com denotes EXACTLY
  `x⁻¹ * rInv⁻¹ * rInv⁻¹` (`rfl`).
* `montInverse_eq_leaf` — and hence equals the `ModArithMontInverse` leaf
  `montInverseF rInv x` (`rfl`).

The op's downstream correctness — that its Montgomery product with `x̃` is the
unit `R = rInv⁻¹` — is `ModArithMontInverse.montInverse_spec` (over a prime
modulus); here we only tie the field schedule to that op's leaf.

## Classification (read `VIR/DIALECTS.md`)

This is a **denote-preserving `fieldDialect` schedule**, NOT an emit-wired
kernel.  It descends to jasmin/bytes through the certified
`FieldDescent.fieldComToJasmin_denote` (`Com fieldDialect → Com jasminDialect`,
the Montgomery base-field word realization carried as the explicit
`hVarJ`/`hOpJ`/`hExtJ` hypotheses, GMP-KAT-gated against the Fermat /
Bernstein–Yang reference), exactly as `EcLineFieldEmit.ecLineJasmin_denote` — we
cite that descent here, we do not wire it (the bytes-reaching field inverse still
flows through the existing Fermat / divstep emit kernels).

**All goals closed.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverseFieldEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverse

variable {p : Nat}

/-! ## 1. The input context and the De Bruijn variables

`Γ₀ = [fp p, fp p]` holds the residue `x` (index 0) and the Montgomery-radix
inverse `rInv` (index 1). -/

/-- The starting context: the residue `x` and the Montgomery-radix inverse
    `rInv`. -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect := [FieldTy.fp p, FieldTy.fp p]

/-- De Bruijn variable for `x` (index 0). -/
def vx : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .here
/-- `rInv` (index 1). -/
def vrInv : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .there .here

/-- The valuation `⟨x, rInv⟩`. -/
def eval (x rInv : ZMod p) : Ctxt.Valuation (Γ₀ p) :=
  .cons x (.cons rInv .nil)

/-! ## 2. The Montgomery-inverse schedule `r = x⁻¹ · rInv⁻¹ · rInv⁻¹`

Authored straight over `FieldOp.fInv`/`fMul`, threading the De Bruijn context
binding-by-binding (each `Com.var` prepends one entry, shifting the inputs). The
schedule (variable indices recorded per let):

    xi = fInv x         -- x⁻¹;            x → 1, rInv → 2
    ri = fInv rInv      -- rInv⁻¹;         xi → 1, x → 2, rInv → 3
    t  = fMul xi ri     -- x⁻¹·rInv⁻¹;     ri → 0, xi → 1
    r  = fMul t  ri     -- (x⁻¹·rInv⁻¹)·rInv⁻¹;  t → 0, ri → 1
    ret r
-/

/-- The Montgomery-domain inverse schedule `r = x⁻¹ · rInv⁻¹ · rInv⁻¹` as a
    `Com fieldDialect` over `Γ₀`, ending in `fp p`. -/
def montInverseProg : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  -- xi = x⁻¹             (x at idx 0)
  .var (.mk (.fInv p) rfl (.cons vx .nil))
  -- ri = rInv⁻¹          (rInv shifted once → idx 2)
  (.var (.mk (.fInv p) rfl (.cons (.there vrInv) .nil))
  -- t = xi * ri          (ri at idx 0, xi at idx 1)
  (.var (.mk (.fMul p) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r = t * ri           (t at idx 0, ri at idx 1)
  (.var (.mk (.fMul p) rfl (.cons .here (.cons (.there .here) .nil)))
  (.ret .here))))

/-! ## 3. The denotation ties — `denote = ModArithMontInverse.montInverseF`

`rfl` (the field-op denotations `fInvF`/`fMulF` are `ZMod p`'s native `⁻¹`/`*`,
and `*` is left-associative, so the schedule denotes definitionally to
`(x⁻¹ * rInv⁻¹) * rInv⁻¹`), the same `rfl`-closed-form shape as
`EcLineFieldEmit.ecLine_field_denote`. -/

/-- **`montInverseProg` denotes exactly `x⁻¹ · rInv⁻¹ · rInv⁻¹`.** -/
theorem montInverse_field_denote (x rInv : ZMod p) :
    (montInverseProg (p := p)).denote (eval x rInv)
      = x⁻¹ * rInv⁻¹ * rInv⁻¹ := rfl

/-- **`montInverseProg` denotes exactly the `ModArithMontInverse` leaf
    `montInverseF rInv x`.**  The field schedule REALISES prime-ir's
    `mod_arith.mont_inverse`. -/
theorem montInverse_eq_leaf (x rInv : ZMod p) :
    (montInverseProg (p := p)).denote (eval x rInv) = montInverseF rInv x := rfl

/-! ## 4. Tiny concrete smoke check (NOT a kernel KAT)

Over `ZMod 7` with `rInv = 1` (Montgomery radix `R = 1`, the plain field-inverse
specialisation): on `x = 3` (`3⁻¹ = 5`, since `3·5 = 15 = 1 mod 7`) the schedule
returns `5 · 1⁻¹ · 1⁻¹ = 5`. -/

example : (montInverseProg (p := 7)).denote (eval 3 1) = (5 : ZMod 7) := by with_unfolding_all rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverseFieldEmit
