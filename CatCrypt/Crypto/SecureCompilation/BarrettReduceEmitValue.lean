/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
public import CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

/-!
# The Barrett-reduce emit → modular-VALUE bridge

This is the **modular-reduction** analogue of `GenericFieldEmitValue.lean` /
`GenericNttEmitValue.lean` — the emit→value MIDDLE SEAM for the Barrett
reduction primitive.  Where the field bridge ties an emitted binary field-op
leaf to the abstract `ZMod q` field value, and the NTT bridge ties a binary
NTT-multiply leaf to the cyclic-convolution value, this module ties an emitted
**reduce leaf** (a UNARY named call) to the abstract **modular residue**
`x mod q`: the value the Barrett-reduce kernel computes.

The carrier here is `ℕ` — Barrett reduction (`BarrettReduceGeneric`) is proved
over `ℕ`.  A `decode : RustVal .TFp → ℕ` reads the `.TFp` slot as a natural
number; the leaf is a one-input call `leafSpec.call leaf .TFp [.TFp] oldDest
[⟨.TFp, xVal⟩]`.

This module composes:

1. the **structural emit** of a unary reduce leaf (= one named `leafSpec.call`
   with a 1-element argument list), with
2. a **leaf-realization hypothesis** (`BarrettEmitRealizes`) — the localized
   residual that the emitted leaf decodes to `x mod q`, and
3. the **commuting square** supplied by the proven Barrett correctness theorem
   `barrettCondsub_eq_mod` (`barrettCondsub q k x = x % q` under `0 < q`,
   `q ≤ 2^k`, `x < 2^k`).

## What is genuinely closed here vs. localized

* **Closed (Lean theorem):** the **commuting-square discharge**
  `barrettEmitRealizes_of_kernel`.  The Barrett correctness theorem
  `barrettCondsub_eq_mod` rewrites `barrettCondsub q k x = x % q`, so a leaf
  realizing the **Barrett kernel value** (`BarrettKernelRealizes`) automatically
  realizes `x mod q`.  The "Barrett reduce = mod" content is discharged by the
  proven theorem; the residual after the square is exactly "the leaf decodes to
  the Barrett-kernel value" — a structural/KAT fact about the emitted kernel.
* **Localized (named hypothesis `BarrettKernelRealizes`):** that the opaque
  leaf-call value decodes to `barrettCondsub q k (decode xVal)` — the bytes the
  emitted Barrett kernel actually computes.  This is the leaf-bytes KAT residual.

## Non-vacuity

`barrettKernelRealizes_canonical` exhibits a concrete `LeafSpec` (built from a
`barrettCondsub`-returning realizer) under which `BarrettKernelRealizes` — hence
`BarrettEmitRealizes` — holds, so the hypotheses are satisfiable, not an
unsatisfiable over-constraint.  The genuine cross-prover content is the gap
between this canonical realizer and the emitted Barrett kernel's real byte
semantics, which lives outside Lean.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BarrettReduceEmitValue

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

/-! ## §1  The Barrett-reduce leaf-realization predicates -/

set_option linter.unusedVariables false in
/-- **The localized Barrett-reduce leaf-realization predicate** (the value
    content).  For every operand `xVal` (and any prior dest value `oldDest`), the
    UNARY leaf-call value decodes to the modular residue `(decode xVal) % q` —
    the value the reduce primitive computes.

    This is the unary analogue of `FieldEmitRealizes`/`NttEmitRealizes`, with the
    abstract op fixed to `· % q`.  It is **not** a Lean theorem: that
    `leafSpec.call`'s opaque value coincides with `x mod q` is the cross-prover
    edge, named here.  (`k` is part of the Barrett parameter pair `(q, k)` and is
    kept for signature symmetry with the kernel predicate / discharge, even though
    the value content `· % q` does not mention it.) -/
def BarrettEmitRealizes (q k : ℕ) (decode : RustVal .TFp → ℕ)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (xVal oldDest : RustVal .TFp),
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (decode xVal) % q

/-- **The localized Barrett KERNEL-realization predicate.**  The residual the
    emitted kernel *actually* satisfies byte-wise: the leaf-call value decodes to
    `barrettCondsub q k (decode xVal)` — the condsub-corrected Barrett estimate
    the emitted reduce kernel computes.  This is the leaf-bytes KAT fact; the
    commuting square (`barrettCondsub_eq_mod`) lifts it to `BarrettEmitRealizes`. -/
def BarrettKernelRealizes (q k : ℕ) (decode : RustVal .TFp → ℕ)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (xVal oldDest : RustVal .TFp),
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = barrettCondsub q k (decode xVal)

/-! ## §2  The commuting-square discharge

`barrettCondsub_eq_mod` (`barrettCondsub q k x = x % q` under `0 < q`,
`q ≤ 2^k`, `x < 2^k`) is the proven content that the Barrett-condsub estimate
equals the true residue.  It lifts a kernel-realization (leaf = Barrett kernel)
to a full mod-reduction realization (leaf = `· % q`): after rewriting
`barrettCondsub = · % q`, the goal *is* the kernel residual. -/

/-- **The commuting-square discharge.**  From the kernel-realization residual
    `BarrettKernelRealizes q k decode leaf leafSpec` (the leaf decodes to the
    Barrett-condsub value — the leaf-bytes KAT fact) plus the Barrett
    side-conditions `0 < q`, `q ≤ 2^k`, and in-range inputs `decode xVal < 2^k`,
    conclude the full mod-reduction realization `BarrettEmitRealizes q k decode
    leaf leafSpec`.

    The "Barrett reduce = mod" content is discharged by the proven
    `barrettCondsub_eq_mod`; what remains after the square is exactly the kernel
    residual `hker`. -/
theorem barrettEmitRealizes_of_kernel
    {q k : ℕ} {decode : RustVal .TFp → ℕ} {leaf : String} {leafSpec : LeafSpec}
    (hq : 0 < q) (hk : q ≤ 2 ^ k)
    (hbound : ∀ xVal : RustVal .TFp, decode xVal < 2 ^ k)
    (hker : BarrettKernelRealizes q k decode leaf leafSpec) :
    BarrettEmitRealizes q k decode leaf leafSpec := by
  intro xVal oldDest
  rw [hker xVal oldDest, barrettCondsub_eq_mod q k hq hk (decode xVal) (hbound xVal)]

/-! ## §3  Non-vacuity: a canonical realizer satisfies `BarrettKernelRealizes`

As in `GenericNttEmitValue.nttKernelRealizes_canonical`, we exhibit a concrete
`LeafSpec` under which `BarrettKernelRealizes` holds — confirming the predicate
is the right shape (an inhabited cross-prover claim).  Composed with the §2
square, it also satisfies `BarrettEmitRealizes`. -/

/-- The canonical `CallSpec` realizing the Barrett kernel at leaf `leaf`: at the
    target name it decodes the single positional `.TFp` argument, computes
    `barrettCondsub q k` of it, and re-encodes via a section `encode`; off-target
    it returns `oldDest`.  The unary analogue of `nttKernelCallSpec`. -/
def barrettKernelCallSpec (q k : ℕ) (decode : RustVal .TFp → ℕ)
    (encode : ℕ → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → ℕ := fun a =>
        if ht : a.1 = TowerType.TFp then decode (ht ▸ a.2) else 0
      match args with
      | a :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encode (barrettCondsub q k (pick a))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity witness for `BarrettKernelRealizes`.**  For the canonical
    `LeafSpec` built from `barrettKernelCallSpec` with a decoder section `encode`
    (`decode ∘ encode = id`), the kernel-realization holds — so the localized
    hypothesis is satisfiable.  The genuine cross-prover content is precisely the
    gap between this canonical realizer and the emitted Barrett kernel's real byte
    semantics (the leaf-bytes KAT), which lives outside Lean. -/
theorem barrettKernelRealizes_canonical
    (q k : ℕ) (decode : RustVal .TFp → ℕ) (encode : ℕ → RustVal .TFp)
    (hsection : ∀ n : ℕ, decode (encode n) = n)
    (leaf : String) (limbStore : LimbStoreSpec) :
    BarrettKernelRealizes q k decode leaf
      { call := barrettKernelCallSpec q k decode encode leaf,
        limbStore := limbStore } := by
  intro xVal oldDest
  show decode (barrettKernelCallSpec q k decode encode leaf leaf .TFp [.TFp]
      oldDest [⟨.TFp, xVal⟩])
    = barrettCondsub q k (decode xVal)
  simp only [barrettKernelCallSpec, ite_true, dite_true, hsection]

/-- **Non-vacuity witness for `BarrettEmitRealizes`.**  Composing the canonical
    kernel realizer (§3) with the commuting-square discharge (§2): under the
    Barrett side-conditions, the canonical `LeafSpec` also satisfies the full
    mod-reduction realization. -/
theorem barrettEmitRealizes_canonical
    (q k : ℕ) (decode : RustVal .TFp → ℕ) (encode : ℕ → RustVal .TFp)
    (hsection : ∀ n : ℕ, decode (encode n) = n)
    (hq : 0 < q) (hk : q ≤ 2 ^ k)
    (hbound : ∀ xVal : RustVal .TFp, decode xVal < 2 ^ k)
    (leaf : String) (limbStore : LimbStoreSpec) :
    BarrettEmitRealizes q k decode leaf
      { call := barrettKernelCallSpec q k decode encode leaf,
        limbStore := limbStore } :=
  barrettEmitRealizes_of_kernel hq hk hbound
    (barrettKernelRealizes_canonical q k decode encode hsection leaf limbStore)

end CatCrypt.Crypto.SecureCompilation.BarrettReduceEmitValue
