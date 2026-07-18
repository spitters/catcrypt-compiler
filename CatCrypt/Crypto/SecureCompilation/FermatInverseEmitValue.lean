/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.BarrettReduceEmitValue
import CatCrypt.Crypto.Optimizer.Rewrite.FermatInverseGeneric

/-!
# The Fermat constant-time modular-inverse emit → VALUE bridge

This is the **modular-inverse** analogue of `BarrettReduceEmitValue.lean` — the
emit→value MIDDLE SEAM for the constant-time inverse primitive.  Where the
Barrett bridge ties an emitted UNARY reduce leaf to the abstract residue
`x mod q`, this module ties an emitted **CT-inverse leaf** (a unary named call)
to the abstract Fermat inverse `a ^ (p - 2)` — the data-independent
exponentiation that computes the modular inverse, used across ECC point
arithmetic and signature verification.

The carrier here is `ZMod p` — the Fermat inverse (`FermatInverseGeneric`) is
proved over `ZMod p` for prime `p`.  A `decode : RustVal .TFp → ZMod p` reads
the `.TFp` slot as a field element; the leaf is a one-input call
`leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]`.

This module composes:

1. the **structural emit** of a unary inverse leaf (= one named `leafSpec.call`
   with a 1-element argument list), with
2. a **leaf-realization hypothesis** (`FermatInvEmitRealizes`) — the localized
   residual that the emitted leaf decodes to `fermatInv p x`, and
3. the **correctness corollary** supplied by the proven Fermat theorem
   `fermatInv_eq_inv` (`fermatInv p a = a⁻¹` under `a ≠ 0`).

## What is genuinely closed here vs. localized

* **Closed (Lean theorem):** the **correctness corollary**
  `fermatInv_emit_correct`.  The Fermat theorem `fermatInv_eq_inv` rewrites
  `fermatInv p a = a⁻¹` for nonzero `a`, so a leaf realizing the **Fermat
  exponentiation value** (`FermatInvEmitRealizes`) automatically computes the
  **true modular inverse** `(decode xVal)⁻¹` on nonzero inputs.  The
  "`a ^ (p-2)` = inverse" content is discharged by the proven theorem.
* **Localized (named hypothesis `FermatInvKernelRealizes`):** that the opaque
  leaf-call value decodes to `fermatInv p (decode xVal)` — the bytes the
  emitted CT-inverse kernel actually computes.  Because `fermatInv` *is* the
  algorithm `a ^ (p-2)`, the kernel predicate coincides with the emit
  predicate: the emitted leaf and the abstract op agree definitionally; the
  meaningful value content is the correctness corollary that this equals `a⁻¹`.

## Non-vacuity

`fermatInvKernelRealizes_canonical` exhibits a concrete `LeafSpec` (built from a
`fermatInv`-returning realizer) under which `FermatInvKernelRealizes` — hence
`FermatInvEmitRealizes` — holds, so the hypotheses are satisfiable, not an
unsatisfiable over-constraint.  The genuine cross-prover content is the gap
between this canonical realizer and the emitted CT-inverse kernel's real byte
semantics, which lives outside Lean.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FermatInverseEmitValue

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.Rewrite.FermatInverseGeneric

variable (p : ℕ) [Fact p.Prime]

/-! ## §1  The Fermat-inverse leaf-realization predicates -/

set_option linter.unusedVariables false in
/-- **The localized Fermat-inverse leaf-realization predicate** (the value
    content).  For every operand `xVal` (and any prior dest value `oldDest`), the
    UNARY leaf-call value decodes to the Fermat inverse `fermatInv p (decode xVal)`
    — the value the constant-time inverse primitive computes.

    This is the unary analogue of `BarrettEmitRealizes`, with the abstract op
    fixed to `fermatInv p · = · ^ (p - 2)`.  It is **not** a Lean theorem: that
    `leafSpec.call`'s opaque value coincides with `a ^ (p - 2)` is the
    cross-prover edge, named here. -/
def FermatInvEmitRealizes (decode : RustVal .TFp → ZMod p)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (xVal oldDest : RustVal .TFp),
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = fermatInv p (decode xVal)

set_option linter.unusedVariables false in
/-- **The localized Fermat KERNEL-realization predicate.**  The residual the
    emitted kernel *actually* satisfies byte-wise: the leaf-call value decodes to
    `fermatInv p (decode xVal)` — the data-independent `a ^ (p - 2)`
    exponentiation the emitted CT-inverse kernel computes.

    Because `fermatInv` *is* the algorithm `a ^ (p - 2)`, this predicate
    coincides with `FermatInvEmitRealizes`: there is no separate "kernel = abstract
    op" square to discharge, unlike the Barrett seam (where `barrettCondsub`
    differs from `· % q`).  The meaningful value content is the correctness
    corollary `fermatInv_emit_correct`, lifting this to the true inverse `a⁻¹`. -/
def FermatInvKernelRealizes (decode : RustVal .TFp → ZMod p)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (xVal oldDest : RustVal .TFp),
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = fermatInv p (decode xVal)

/-! ## §2  The discharge (kernel ⇒ emit) and the correctness corollary

Unlike the Barrett seam — where the commuting square `barrettCondsub_eq_mod`
bridges the *distinct* kernel value `barrettCondsub q k x` and abstract op
`x % q` — here the kernel value `fermatInv p x` and the abstract op
`fermatInv p x` coincide (both are `x ^ (p - 2)`), so the discharge is the
identity.  The genuinely closed content is the **correctness corollary**: the
proven `fermatInv_eq_inv` lifts the Fermat exponentiation to the true field
inverse on nonzero inputs. -/

/-- **The discharge.**  Since the kernel value (`fermatInv p x`, the emitted
    `a ^ (p - 2)`) and the abstract op (`fermatInv p x`) coincide, the
    kernel-realization predicate IS the emit-realization predicate.  No commuting
    square is required (contrast `barrettEmitRealizes_of_kernel`). -/
theorem fermatInvEmitRealizes_of_kernel
    {decode : RustVal .TFp → ZMod p} {leaf : String} {leafSpec : LeafSpec}
    (hker : FermatInvKernelRealizes p decode leaf leafSpec) :
    FermatInvEmitRealizes p decode leaf leafSpec :=
  hker

/-- **The correctness corollary (the genuinely closed content).**  If the
    emitted leaf realizes the Fermat exponentiation (`FermatInvEmitRealizes`),
    then on any **nonzero** input the leaf-call value decodes to the **true field
    inverse** `(decode xVal)⁻¹`.  The "`a ^ (p - 2)` = inverse" step is the proven
    `fermatInv_eq_inv`; the emit-realization supplies the leaf↔`fermatInv` edge.

    This is the value of the seam: the data-independent constant-time inverse,
    emit-realized, proven equal to the true modular inverse for nonzero inputs. -/
theorem fermatInv_emit_correct
    {decode : RustVal .TFp → ZMod p} {leaf : String} {leafSpec : LeafSpec}
    (hreal : FermatInvEmitRealizes p decode leaf leafSpec)
    {xVal oldDest : RustVal .TFp} (hne : decode xVal ≠ 0) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (decode xVal)⁻¹ := by
  rw [hreal xVal oldDest, fermatInv_eq_inv p hne]

/-! ## §3  Non-vacuity: a canonical realizer satisfies `FermatInvKernelRealizes`

As in `BarrettReduceEmitValue.barrettKernelRealizes_canonical`, we exhibit a
concrete `LeafSpec` under which `FermatInvKernelRealizes` holds — confirming the
predicate is the right shape (an inhabited cross-prover claim).  Composed with
the §2 discharge it satisfies `FermatInvEmitRealizes`; composed with the
correctness corollary it computes `a⁻¹` on nonzero inputs. -/

/-- The canonical `CallSpec` realizing the Fermat inverse at leaf `leaf`: at the
    target name it decodes the single positional `.TFp` argument, computes
    `fermatInv p` of it, and re-encodes via a section `encode`; off-target it
    returns `oldDest`.  The unary analogue of `barrettKernelCallSpec`. -/
def fermatInvKernelCallSpec (decode : RustVal .TFp → ZMod p)
    (encode : ZMod p → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → ZMod p := fun a =>
        if ht : a.1 = TowerType.TFp then decode (ht ▸ a.2) else 0
      match args with
      | a :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encode (fermatInv p (pick a))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity witness for `FermatInvKernelRealizes`.**  For the canonical
    `LeafSpec` built from `fermatInvKernelCallSpec` with a decoder section `encode`
    (`decode ∘ encode = id`), the kernel-realization holds — so the localized
    hypothesis is satisfiable.  The genuine cross-prover content is precisely the
    gap between this canonical realizer and the emitted CT-inverse kernel's real
    byte semantics (the leaf-bytes KAT), which lives outside Lean. -/
theorem fermatInvKernelRealizes_canonical
    (decode : RustVal .TFp → ZMod p) (encode : ZMod p → RustVal .TFp)
    (hsection : ∀ n : ZMod p, decode (encode n) = n)
    (leaf : String) (limbStore : LimbStoreSpec) :
    FermatInvKernelRealizes p decode leaf
      { call := fermatInvKernelCallSpec p decode encode leaf,
        limbStore := limbStore } := by
  intro xVal oldDest
  show decode (fermatInvKernelCallSpec p decode encode leaf leaf .TFp [.TFp]
      oldDest [⟨.TFp, xVal⟩])
    = fermatInv p (decode xVal)
  simp only [fermatInvKernelCallSpec, ite_true, dite_true, hsection]

/-- **Non-vacuity witness for `FermatInvEmitRealizes`.**  Composing the canonical
    kernel realizer (§3) with the discharge (§2): the canonical `LeafSpec` also
    satisfies the Fermat-exponentiation realization. -/
theorem fermatInvEmitRealizes_canonical
    (decode : RustVal .TFp → ZMod p) (encode : ZMod p → RustVal .TFp)
    (hsection : ∀ n : ZMod p, decode (encode n) = n)
    (leaf : String) (limbStore : LimbStoreSpec) :
    FermatInvEmitRealizes p decode leaf
      { call := fermatInvKernelCallSpec p decode encode leaf,
        limbStore := limbStore } :=
  fermatInvEmitRealizes_of_kernel p
    (fermatInvKernelRealizes_canonical p decode encode hsection leaf limbStore)

end CatCrypt.Crypto.SecureCompilation.FermatInverseEmitValue
