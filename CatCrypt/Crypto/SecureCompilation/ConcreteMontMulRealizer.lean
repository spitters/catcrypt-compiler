/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.SecureCompilation.MontgomeryMulEmitValue
public import CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer
public import CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryMulGeneric

/-!
# Concrete realizer for the Montgomery-multiply kernel — KAT-free

`MontgomeryMulEmitValue.lean` reduces the Montgomery-multiply emit obligation to
a binary *leaf-realization* predicate — "the emitted Montgomery leaf's bytes
decode to `montMul N R N' (decode aVal) (decode bVal)`".  Its non-vacuity witness
(`montMulKernelRealizes_canonical`) exhibits a realizing `LeafSpec`, but only
**parametrically** over an abstract `encode`/`decode` pair with a *hypothesised*
section (`hsection : ∀ z : ℤ, decode (encode z) = z`).

This module makes that section **concrete and proved**, mirroring
`ConcreteBarrettRealizer.lean` (the unary Barrett-reduce concrete realizer).  The
Montgomery seam's carrier is `ℤ` (the `Int.ModEq` algebra of
`MontgomeryRedcGeneric`/`MontgomeryMulGeneric` is cleanest over `ℤ`).  Montgomery
operands are *residues* `0 ≤ a < N`, hence representable as a base-256 natural
number; we therefore reuse the Barrett file's proven base-256 `ℕ`↔bytes codec
(`encodeB`/`decodeB`, round-trip `decodeB_encodeB`) and lift it to `ℤ`:

* `decodeZ width a := (decodeB width a : ℤ)` reads the `.TFp` slot's first `width`
  base-256 bytes as a (non-negative) integer;
* `encodeZ width x := encodeB width x.toNat` lays the `width` base-256 digits of
  `x.toNat` into the carrier (for an in-range residue `0 ≤ x`, `x.toNat = x`).

We exhibit:

* a concrete `RustVal .TFp` (= `JArray 48`, the `.TBytes 48` byte carrier) base-256
  `ℤ` codec `encodeZ`/`decodeZ` — no constructor-wrapping of a function, no
  `axiom`;
* a **proved** round-trip `decodeZ_encodeZ : decodeZ width (encodeZ width x) = x`
  for **all** in-range non-negative inputs `0 ≤ x < 256 ^ width` — the byte-level
  fact a KAT would merely *assert*, here a theorem (it is `decodeB_encodeB`
  reused, the same `base256_digit_sum` engine as the field/Barrett codecs);
* a spec-computing realizer `LeafSpec` (`montMulLeafSpec N R N' width leaf …`)
  whose binary `.call` value at the leaf decodes to
  `montMul N R N' (decode aVal) (decode bVal)`;
* the realization `montMul_realizes_concrete`
  (`KernelRealizes2 (decodeZ width) (montMul N R N') leaf …`) — no KAT, no
  abstract section — proved from `decodeZ_encodeZ`, under the codec-fit
  side-condition that `montMul`'s output is an in-range residue
  (`0 ≤ montMul … < 256 ^ width`); and
* the `MontMulEmitRealizes` form via the `montMul_iff_kernel2` seam.

## What this proves and what it does NOT

* **Proved (unconditional Lean theorem modulo codec-fit):** there is a *concrete*,
  round-trip-verified base-256 byte codec and a *concrete*, spec-computing
  realizer `LeafSpec` under which the Montgomery-multiply leaf realization holds —
  strictly stronger than *assuming* a KAT, because the byte-level
  decode-equals-`montMul` fact is a theorem here, not a test vector.  The
  Montgomery-multiply *encoding* KAT (the `decode ∘ encode = id` assumption of
  `montMulKernelRealizes_canonical`) is discharged.
* **NOT proved (outside the scope):** that the *jasmin-emitted machine bytes*
  of the real Montgomery-multiply kernel equal this realizer.  That equality —
  emitted assembly ≡ the realizer `LeafSpec` — is the owned-machine-code route,
  outside this module.  This module removes the *encoding* KAT for the
  Montgomery-domain multiply family; it does **not** remove the *machine-code*
  obligation.

This covers the **Montgomery-domain multiply** primitive used across lattice/curve
crypto (ML-KEM/ML-DSA coefficient Montgomery multiply, RSA/EC field multiply).

## Side-conditions are codec-fit + Montgomery parameter conditions

The side hypotheses are of two distinct kinds, **neither** a hypothesis
on the realizer/kernel:

1. **Codec-fit** (`width ≤ 48`, and the per-call range
   `0 ≤ montMul N R N' (decodeZ width a) (decodeZ width b) < 256 ^ width`): these
   make the `width` base-256 digits fit the 48-byte carrier and the output a
   representable residue.  They are exactly the analogues of the Barrett file's
   `width ≤ 48`, `x < 256 ^ width`.  Since a real Montgomery multiplier returns a
   value reduced into `[0, N)` and `N ≤ 256 ^ width`, this is the residue-range
   fit, not a kernel assumption.
2. **Montgomery parameter condition** (`N * N' ≡ -1 [ZMOD R]`): this is the
   *defining precondition of the Montgomery algorithm itself* (it forces
   `gcd(R, N) = 1` and makes the reduction exact — see `MontgomeryRedcGeneric`),
   needed only for the downstream *correctness* corollary
   `montMul_realizes_correct`.  It is an algorithm precondition on the Montgomery
   constants `N`, `R`, `N'`, not a hypothesis on the emitted kernel.

## References
* P. L. Montgomery, "Modular multiplication without trial division",
  Math. Comp. 44 (1985), 519–521.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteMontMulRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.MontgomeryMulEmitValue
open CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryMulGeneric

/-! ## §1  A concrete base-256 `ℤ`↔bytes codec over `RustVal .TFp`

`RustVal .TFp = JArray 48 = Fin 48 → BitVec 8` is the `.TBytes 48` byte carrier.
A Montgomery operand is a *residue* `0 ≤ x < N`, hence a base-256 natural number;
we reuse the proven `ℕ` codec from `ConcreteBarrettRealizer` and lift to `ℤ`:
`decodeZ` reads it as a non-negative integer, `encodeZ` lays out `x.toNat`. -/

/-- Encode an integer into the first `width` carrier bytes as the little-endian
    base-256 digits of `x.toNat`; zero in the tail.  (`width ≤ 48` and
    `0 ≤ x < 256 ^ width` for the round-trip and fit.)  The carrier
    `RustVal .TFp` is the `.TBytes 48` byte array. -/
def encodeZ (width : ℕ) (x : ℤ) : RustVal .TFp :=
  encodeB width x.toNat

/-- Decode the first `width` carrier bytes as a base-256 little-endian
    (non-negative) integer. -/
def decodeZ (width : ℕ) (a : RustVal .TFp) : ℤ :=
  (decodeB width a : ℤ)

/-- **The verified Montgomery-codec round-trip (the crux).**  For `width ≤ 48` and
    an in-range non-negative input `0 ≤ x < 256 ^ width`, decoding the concrete
    base-256 byte encoding of an integer returns it unchanged — for **all**
    in-range non-negative inputs.  The byte-level fact a KAT would merely *assert*;
    here a theorem, reusing the proven `decodeB_encodeB` (engine
    `base256_digit_sum`). -/
theorem decodeZ_encodeZ (width : ℕ) (hw : width ≤ 48) (x : ℤ)
    (hx0 : 0 ≤ x) (hx : x < 256 ^ width) :
    decodeZ width (encodeZ width x) = x := by
  simp only [decodeZ, encodeZ]
  have hnat : x.toNat < 256 ^ width := by
    have hxz : (x.toNat : ℤ) < ((256 ^ width : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hx0]
      exact hx
    exact_mod_cast hxz
  rw [decodeB_encodeB width hw x.toNat hnat, Int.toNat_of_nonneg hx0]

/-! ## §2  The concrete Montgomery-multiply realizer `LeafSpec`

The realizer's `CallSpec`: at the Montgomery leaf it decodes the two `.TFp`
arguments, applies `montMul N R N'` in `ℤ`, and re-encodes via `encodeZ`;
off-leaf it returns `oldDest`.  The concrete instance of
`MontgomeryMulEmitValue.montMulKernelCallSpec` with the proven section. -/

/-- The concrete Montgomery-multiply realizer's `CallSpec`. -/
def montMulRealizerCallSpec (N R N' : ℤ) (width : ℕ) (leaf : String) : CallSpec :=
  montMulKernelCallSpec N R N' (decodeZ width) (encodeZ width) leaf

/-- The concrete Montgomery-multiply realizer `LeafSpec`. -/
def montMulLeafSpec (N R N' : ℤ) (width : ℕ) (leaf : String)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := montMulRealizerCallSpec N R N' width leaf, limbStore := limbStore }

/-! ## §3  The realization (no KAT, no abstract section) -/

/-- **Montgomery-multiply kernel realization (no KAT, no abstract section).**
    For `width ≤ 48`, the concrete realizer `montMulLeafSpec N R N' width …`
    decodes its binary leaf-call value to `montMul N R N'` of its two decoded
    inputs — proved by the round-trip `decodeZ_encodeZ`, not assumed via a test
    vector.

    The side hypothesis `hfit` is the **codec-fit residue-range** condition: the
    Montgomery product is a representable residue
    `0 ≤ montMul … < 256 ^ width` (a real Montgomery multiplier reduces into
    `[0, N)` with `N ≤ 256 ^ width`).  It is the binary analogue of the Barrett
    file's `x < 256 ^ width` codec-fit condition — **not** a kernel hypothesis
    (the realizer computes `montMul N R N'` unconditionally; `hfit` only certifies
    the byte window is wide enough to round-trip the output). -/
theorem montMul_realizes_concrete (N R N' : ℤ) (width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec)
    (hfit : ∀ aVal bVal : RustVal .TFp,
      0 ≤ montMul N R N' (decodeZ width aVal) (decodeZ width bVal) ∧
      montMul N R N' (decodeZ width aVal) (decodeZ width bVal) < 256 ^ width) :
    KernelRealizes2 (decodeZ width) (montMul N R N') leaf
      (montMulLeafSpec N R N' width leaf limbStore) := by
  intro aVal bVal oldDest
  show decodeZ width (montMulRealizerCallSpec N R N' width leaf leaf .TFp
      [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = montMul N R N' (decodeZ width aVal) (decodeZ width bVal)
  simp only [montMulRealizerCallSpec, montMulKernelCallSpec, ite_true, dite_true]
  obtain ⟨h0, hlt⟩ := hfit aVal bVal
  rw [decodeZ_encodeZ width hw _ h0 hlt]

/-- **The Montgomery realization as a `MontMulEmitRealizes` seam.**
    `montMul_realizes_concrete` *is* the localized
    `MontgomeryMulEmitValue.MontMulEmitRealizes` predicate — via the
    `montMul_iff_kernel2` seam (`Iff.rfl`) — with its abstract `encode`/`decode`
    section a *theorem* (`decodeZ_encodeZ`) rather than the assumed
    `hsection`. -/
theorem montMul_emit_realizes_concrete (N R N' : ℤ) (width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec)
    (hfit : ∀ aVal bVal : RustVal .TFp,
      0 ≤ montMul N R N' (decodeZ width aVal) (decodeZ width bVal) ∧
      montMul N R N' (decodeZ width aVal) (decodeZ width bVal) < 256 ^ width) :
    MontMulEmitRealizes N R N' (decodeZ width) leaf
      (montMulLeafSpec N R N' width leaf limbStore) :=
  (montMul_iff_kernel2 N R N' (decodeZ width) leaf
    (montMulLeafSpec N R N' width leaf limbStore)).mpr
    (montMul_realizes_concrete N R N' width hw leaf limbStore hfit)

/-! ## §4  The correctness corollary via the proven Montgomery lemma

Threading the Montgomery parameter condition `N * N' ≡ -1 [ZMOD R]` (the
defining precondition of the algorithm — it forces `gcd(R, N) = 1` and makes the
reduction exact) through the proven lemma `montMul_emit_correct`
(`MontgomeryMulEmitValue`, itself reusing `montMul_mul_R_modEq`) gives the full
correctness congruence: the decoded output of the concrete realizer satisfies
`decode(leaf …) * R ≡ (decode a) * (decode b) [ZMOD N]`, i.e. it is a correct
Montgomery product `≡ a*b*R⁻¹ mod N`.  The parameter condition is an algorithm
precondition on `N`, `R`, `N'`, **not** a hypothesis on the emitted kernel. -/

/-- **The concrete Montgomery-multiply realizer computes a correct Montgomery
    product mod `N`.**  Under the codec-fit `hfit` and the Montgomery parameter
    condition `N * N' ≡ -1 [ZMOD R]`, the decoded output of the concrete realizer
    satisfies the defining Montgomery property

    `decode(leaf …) * R ≡ (decode aVal) * (decode bVal) [ZMOD N]`,

    i.e. it is `≡ a*b*R⁻¹ mod N`.  The "decode = montMul" content is the proven
    `decodeZ_encodeZ`; the "montMul is a correct product" content is the proven
    key lemma `montMul_mul_R_modEq` (reused via `montMul_emit_correct`). -/
theorem montMul_realizes_correct (N R N' : ℤ) (width : ℕ) (hw : width ≤ 48)
    (hN' : N * N' ≡ -1 [ZMOD R])
    (leaf : String) (limbStore : LimbStoreSpec)
    (hfit : ∀ aVal bVal : RustVal .TFp,
      0 ≤ montMul N R N' (decodeZ width aVal) (decodeZ width bVal) ∧
      montMul N R N' (decodeZ width aVal) (decodeZ width bVal) < 256 ^ width)
    (aVal bVal oldDest : RustVal .TFp) :
    decodeZ width
        ((montMulLeafSpec N R N' width leaf limbStore).call leaf .TFp [.TFp, .TFp]
          oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) * R
      ≡ (decodeZ width aVal) * (decodeZ width bVal) [ZMOD N] :=
  montMul_emit_correct hN'
    (montMul_emit_realizes_concrete N R N' width hw leaf limbStore hfit)
    aVal bVal oldDest

end CatCrypt.Crypto.SecureCompilation.ConcreteMontMulRealizer
