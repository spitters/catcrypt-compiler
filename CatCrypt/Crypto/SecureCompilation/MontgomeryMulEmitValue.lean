/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
import CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryMulGeneric

/-!
# The Montgomery-multiply emit → field-VALUE bridge

This is the **Montgomery-multiplication** analogue of
`BarrettReduceEmitValue.lean` — the emit→value MIDDLE SEAM for the core
field/curve multiply used across ECC and pairing crypto.  Where the Barrett
bridge ties an emitted UNARY reduce leaf to the modular residue `x mod q`, this
module ties an emitted **BINARY Montgomery-multiply leaf** (a named call on two
`.TFp` operands) to the abstract **Montgomery product** value
`montMul N R N' a b` — the value the Montgomery multiplier computes.

The carrier here is `ℤ` — Montgomery reduction/multiplication
(`MontgomeryRedcGeneric` / `MontgomeryMulGeneric`) is proved over `ℤ`, where the
`Int.ModEq` (`[ZMOD N]`) algebra is cleanest.  A `decode : RustVal .TFp → ℤ`
reads the `.TFp` slot as an integer; the leaf is a two-input call
`leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]`,
matching the binary shape of `GenericNttEmitValue.NttEmitRealizes`.

This module composes:

1. the **structural emit** of a binary Montgomery-multiply leaf (= one named
   `leafSpec.call` with a 2-element argument list), with
2. a **leaf-realization hypothesis** (`MontMulEmitRealizes`) — the localized
   residual that the emitted leaf decodes to `montMul N R N' (decode aVal)
   (decode bVal)`, and
3. the **commuting square** supplied by the proven Montgomery-mul correctness
   theorem `montMul_mul_R_modEq` (`montMul N R N' a b * R ≡ a*b [ZMOD N]` under
   the Montgomery constant condition `N*N' ≡ -1 [ZMOD R]`).

## `montMul` IS the kernel algorithm — so the kernel residual coincides

Unlike the Barrett seam — where the kernel computes `barrettCondsub` and the
proven theorem rewrites it to `· % q` — here `montMul N R N' a b := redc N R N'
(a*b)` **is** the algorithm the Montgomery multiplier runs.  So the kernel
residual (`MontMulKernelRealizes`, the leaf-bytes KAT fact) and the value
residual (`MontMulEmitRealizes`) are literally the same proposition: the leaf
decodes to `montMul …`.  The discharge `montMulEmitRealizes_of_kernel` is thus
the identity on hypotheses.

The meaningful value-content theorem is the **downstream correctness corollary**
`montMul_emit_correct`: if the emitted leaf realizes `montMul`, then the decoded
output satisfies `decode(leaf …) * R ≡ (decode a)*(decode b) [ZMOD N]` — i.e.
the emitted leaf computes a *correct Montgomery product* (`≡ a*b*R⁻¹ mod N` in
the `R`-free `*R ≡ ab` form).  This is proved by reusing the source's keystone
`montMul_mul_R_modEq`.

## Non-vacuity

`montMulEmitRealizes_canonical` exhibits a concrete `LeafSpec` (built from a
`montMul`-returning realizer) under which `MontMulEmitRealizes` holds, so the
hypotheses are satisfiable, not an unsatisfiable over-constraint.  The genuine
cross-prover content is the gap between this canonical realizer and the emitted
Montgomery-multiply kernel's real byte semantics, which lives outside Lean.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MontgomeryMulEmitValue

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryMulGeneric

/-! ## §1  The Montgomery-multiply leaf-realization predicates -/

/-- **The localized Montgomery-multiply leaf-realization predicate** (the value
    content).  For every operand pair `aVal`, `bVal` (and any prior dest value
    `oldDest`), the BINARY leaf-call value decodes to the Montgomery product
    `montMul N R N' (decode aVal) (decode bVal)` — the value the Montgomery
    multiplier computes.

    This is the binary analogue of `BarrettEmitRealizes`/`NttEmitRealizes`, with
    the abstract op fixed to `montMul N R N'`.  It is **not** a Lean theorem:
    that `leafSpec.call`'s opaque value coincides with `montMul …` is the
    cross-prover edge, named here. -/
def MontMulEmitRealizes (N R N' : ℤ) (decode : RustVal .TFp → ℤ)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = montMul N R N' (decode aVal) (decode bVal)

/-- **The localized Montgomery KERNEL-realization predicate.**  The residual the
    emitted kernel *actually* satisfies byte-wise: the leaf-call value decodes to
    `montMul N R N' (decode aVal) (decode bVal)`.

    Because `montMul N R N' a b := redc N R N' (a*b)` **is** the algorithm the
    Montgomery multiplier runs (there is no separate "estimate then correct" step
    as in Barrett), the kernel residual and the value residual
    (`MontMulEmitRealizes`) are the *same* proposition.  The commuting square
    therefore degenerates to the identity (`montMulEmitRealizes_of_kernel`), and
    the genuine value content is exposed downstream by `montMul_emit_correct`. -/
def MontMulKernelRealizes (N R N' : ℤ) (decode : RustVal .TFp → ℤ)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = montMul N R N' (decode aVal) (decode bVal)

/-! ## §2  The commuting-square discharge (degenerate — `montMul` is the kernel)

For Barrett, the square is non-trivial: `barrettCondsub_eq_mod` rewrites the
kernel's condsub estimate to the true residue `· % q`.  Here the emitted kernel
computes `montMul` directly, so the kernel residual already *is* the value
residual; the discharge is the identity on hypotheses. -/

/-- **The commuting-square discharge.**  From the kernel-realization residual
    `MontMulKernelRealizes N R N' decode leaf leafSpec` (the leaf-bytes KAT fact),
    conclude the value realization `MontMulEmitRealizes N R N' decode leaf
    leafSpec`.  Since `montMul` is itself the kernel algorithm, the two predicates
    coincide and this is the identity. -/
theorem montMulEmitRealizes_of_kernel
    {N R N' : ℤ} {decode : RustVal .TFp → ℤ} {leaf : String} {leafSpec : LeafSpec}
    (hker : MontMulKernelRealizes N R N' decode leaf leafSpec) :
    MontMulEmitRealizes N R N' decode leaf leafSpec :=
  hker

/-! ## §3  The value content: the emitted Montgomery-multiply leaf is correct

The meaningful "the emitted Montgomery-multiply leaf is correct mod `N`"
statement.  Under the Montgomery constant condition `N*N' ≡ -1 [ZMOD R]`, the
proven keystone `montMul_mul_R_modEq` gives `montMul N R N' a b * R ≡ a*b [ZMOD
N]`.  Composed with a leaf realizing `montMul`, the decoded output of the
emitted leaf satisfies the same defining Montgomery congruence — i.e. the
emitted leaf computes a value `≡ a*b*R⁻¹ mod N`, a correct Montgomery product. -/

/-- **The emitted Montgomery-multiply leaf is correct mod `N`.**

    Given a leaf realizing the Montgomery product (`MontMulEmitRealizes`) and the
    Montgomery constant condition `N*N' ≡ -1 [ZMOD R]`, the decoded output of the
    emitted leaf satisfies the defining Montgomery property

    `decode(leaf …) * R ≡ (decode aVal) * (decode bVal) [ZMOD N]`,

    i.e. it is `≡ a*b*R⁻¹ mod N` — a correct Montgomery product of its inputs.

    Reuses the proven keystone `montMul_mul_R_modEq` from `MontgomeryMulGeneric`
    /`MontgomeryRedcGeneric` for the congruence; the rest is rewriting by the
    realization. -/
theorem montMul_emit_correct
    {N R N' : ℤ} {decode : RustVal .TFp → ℤ} {leaf : String} {leafSpec : LeafSpec}
    (hN' : N * N' ≡ -1 [ZMOD R])
    (hreal : MontMulEmitRealizes N R N' decode leaf leafSpec)
    (aVal bVal oldDest : RustVal .TFp) :
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) * R
      ≡ (decode aVal) * (decode bVal) [ZMOD N] := by
  rw [hreal aVal bVal oldDest]
  exact montMul_mul_R_modEq N R N' (decode aVal) (decode bVal) hN'

/-- **Corollary, from the kernel residual directly.**  Composing §2 and §3: a
    leaf satisfying the leaf-bytes KAT fact (`MontMulKernelRealizes`) computes a
    correct Montgomery product mod `N`. -/
theorem montMul_emit_correct_of_kernel
    {N R N' : ℤ} {decode : RustVal .TFp → ℤ} {leaf : String} {leafSpec : LeafSpec}
    (hN' : N * N' ≡ -1 [ZMOD R])
    (hker : MontMulKernelRealizes N R N' decode leaf leafSpec)
    (aVal bVal oldDest : RustVal .TFp) :
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) * R
      ≡ (decode aVal) * (decode bVal) [ZMOD N] :=
  montMul_emit_correct hN' (montMulEmitRealizes_of_kernel hker) aVal bVal oldDest

/-! ## §4  Non-vacuity: a canonical realizer satisfies `MontMulKernelRealizes`

As in `BarrettReduceEmitValue.barrettKernelRealizes_canonical`, we exhibit a
concrete `LeafSpec` under which `MontMulKernelRealizes` holds — confirming the
predicate is the right shape (an inhabited cross-prover claim).  Composed with
the §2 discharge it also satisfies `MontMulEmitRealizes`, and with §3 the
correctness congruence. -/

/-- The canonical `CallSpec` realizing the Montgomery-multiply kernel at leaf
    `leaf`: at the target name it decodes the two positional `.TFp` arguments,
    computes `montMul N R N'` of them, and re-encodes via a section `encode`;
    off-target it returns `oldDest`.  The binary analogue of
    `barrettKernelCallSpec` / `nttKernelCallSpec`. -/
def montMulKernelCallSpec (N R N' : ℤ) (decode : RustVal .TFp → ℤ)
    (encode : ℤ → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → ℤ := fun a =>
        if ht : a.1 = TowerType.TFp then decode (ht ▸ a.2) else 0
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encode (montMul N R N' (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity witness for `MontMulKernelRealizes`.**  For the canonical
    `LeafSpec` built from `montMulKernelCallSpec` with a decoder section `encode`
    (`decode ∘ encode = id`), the kernel-realization holds — so the localized
    hypothesis is satisfiable.  The genuine cross-prover content is precisely the
    gap between this canonical realizer and the emitted Montgomery kernel's real
    byte semantics (the leaf-bytes KAT), which lives outside Lean. -/
theorem montMulKernelRealizes_canonical
    (N R N' : ℤ) (decode : RustVal .TFp → ℤ) (encode : ℤ → RustVal .TFp)
    (hsection : ∀ z : ℤ, decode (encode z) = z)
    (leaf : String) (limbStore : LimbStoreSpec) :
    MontMulKernelRealizes N R N' decode leaf
      { call := montMulKernelCallSpec N R N' decode encode leaf,
        limbStore := limbStore } := by
  intro aVal bVal oldDest
  show decode (montMulKernelCallSpec N R N' decode encode leaf leaf .TFp
      [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = montMul N R N' (decode aVal) (decode bVal)
  simp only [montMulKernelCallSpec, ite_true, dite_true, hsection]

/-- **Non-vacuity witness for `MontMulEmitRealizes`.**  Composing the canonical
    kernel realizer (§4) with the degenerate commuting-square discharge (§2): the
    canonical `LeafSpec` also satisfies the value realization. -/
theorem montMulEmitRealizes_canonical
    (N R N' : ℤ) (decode : RustVal .TFp → ℤ) (encode : ℤ → RustVal .TFp)
    (hsection : ∀ z : ℤ, decode (encode z) = z)
    (leaf : String) (limbStore : LimbStoreSpec) :
    MontMulEmitRealizes N R N' decode leaf
      { call := montMulKernelCallSpec N R N' decode encode leaf,
        limbStore := limbStore } :=
  montMulEmitRealizes_of_kernel
    (montMulKernelRealizes_canonical N R N' decode encode hsection leaf limbStore)

/-- **Non-vacuity for the correctness corollary.**  Under the Montgomery constant
    condition, the canonical `LeafSpec` (§4) yields a correct Montgomery product
    mod `N` — the value content `montMul_emit_correct` is satisfiable, not
    vacuous. -/
theorem montMul_emit_correct_canonical
    (N R N' : ℤ) (decode : RustVal .TFp → ℤ) (encode : ℤ → RustVal .TFp)
    (hsection : ∀ z : ℤ, decode (encode z) = z)
    (hN' : N * N' ≡ -1 [ZMOD R])
    (leaf : String) (limbStore : LimbStoreSpec)
    (aVal bVal oldDest : RustVal .TFp) :
    decode
        ((montMulKernelCallSpec N R N' decode encode leaf) leaf .TFp [.TFp, .TFp]
          oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) * R
      ≡ (decode aVal) * (decode bVal) [ZMOD N] :=
  montMul_emit_correct hN'
    (montMulEmitRealizes_canonical N R N' decode encode hsection leaf limbStore)
    aVal bVal oldDest

end CatCrypt.Crypto.SecureCompilation.MontgomeryMulEmitValue
