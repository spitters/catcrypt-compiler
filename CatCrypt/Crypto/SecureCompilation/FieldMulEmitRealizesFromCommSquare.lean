/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Mul
import CatCrypt.Crypto.SecureCompilation.RelationalFrontCurveRegistry
import CatCrypt.Crypto.SecureCompilation.FieldEmitRealizesFromCommSquare

/-!
# Discharging `FieldEmitRealizes` from the relational MUL commuting square

This module is the **multiply** analogue of
`FieldEmitRealizesFromCommSquare.lean` (which discharged the *add* leaf). It
narrows the `FieldEmitRealizes q decode op leaf leafSpec` residual (from
`GenericFieldEmitValue.lean`) for `op = (· * ·)` using our *proven* relational
MUL value law.

`RelationalFrontBls377Mul.lean` proves the multi-limb MUL commuting square

```
  (a * b).val = bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b))
```

for every `KLimbPrimeMul Q` (`encMLK_mul_commutes`).  This is the genuine
multi-limb Barrett-reducing kernel for the *product* (`mulBignum` re-limbed +
`barrettReduce` at product width `2k`).  We use it to *discharge*
`FieldEmitRealizes` for `op = (· * ·)`, **conditioned only on the narrower "leaf
computes the limb kernel" fact** — i.e. that the leaf-call value, read as a limb
vector, is `mlMulMod` applied to the operand limb vectors.  Everything *above*
the limb kernel — the Barrett reduce of the product, the `ZMod`-value content —
is then supplied by `encMLK_mul_commutes`, which is a proved theorem, not an
assumption.

## The decode wiring (precisely what is tied vs. assumed)

A `RustVal .TFp` is a 48-byte array.  To read it as a `ZMod Q.q` residue we use
an abstract **limb-extraction** `readLimbs : RustVal .TFp → List (BitVec 64)`
(the byte-array → 64-bit-limb-vector projection; left abstract, as AUCurves keeps
`feval` a section variable) and decode via `bignumVal`, cast into `ZMod Q.q`.
This is the same `klimbDecode` used by the add discharge (and re-used here from
`FieldEmitRealizesFromCommSquare`):

```
  klimbDecode Q.toKLimbPrime readLimbs v := (bignumVal (readLimbs v) : ZMod Q.q)
```

The bridge `FieldEmitRealizes` is then discharged from **two narrow facts**:

* **(kernel-realization, the residual)** `readLimbs (leafSpec.call …) =`
  `mlMulMod Q.k Q.muTwo Q.ql (readLimbs aVal) (readLimbs bVal)` — the leaf, read
  at the limb level, *is* the emitted `mlMulMod` kernel.  This is a KAT /
  AUCurves fact about the limb kernel, **strictly narrower** than "leaf =
  abstract field value": it says nothing about the Barrett reduce of the
  product, only that the bytes are the kernel's bytes.
* **(operand-encoding agreement)** the operand byte-arrays are the `encMLK`
  serializations of their decoded residues: `readLimbs aVal = encMLK Q.q Q.k`
  `(klimbDecode … aVal)` (and likewise `bVal`).  This pins the *input* convention
  (canonical-representative limb form) — a well-formedness condition on the
  operand slots, not a value claim about the op.

Given these two, the field-op value content
`klimbDecode (leaf-call) = klimbDecode aVal * klimbDecode bVal` is **proved**,
*because* `encMLK_mul_commutes` proves the commuting square.  The residual that
survives is no longer "the leaf computes the abstract field value" but the much
narrower "the leaf's bytes are `mlMulMod`'s bytes" (kernel-realization) plus the
input convention — exactly the Tier-2 narrowing this module is for.

## What is genuinely closed here vs. localized

* **Closed (Lean theorem):** the `ZMod`-value content of `mul_realizes`.  Given
  the kernel-realization and operand-encoding hypotheses, the leaf-call value
  decodes to the field product — discharged by `encMLK_mul_commutes` (our proved
  commuting square), *not* assumed.  This is the genuine narrowing: the Barrett
  reduce of the product and the `(a*b).val` law come from a theorem.
* **Localized (narrowed residual):** `readLimbs (leafSpec.call …) = mlMulMod …`
  — that the leaf's emitted bytes are the limb kernel's bytes.  This is the KAT
  fact (AUCurves / owned-emit KAT), narrower than the original
  `FieldEmitRealizes` residual.

## Non-vacuity

`klimbMulKernelRealizes_canonical` exhibits a concrete `LeafSpec` (an
`mlMulMod`-on-`readLimbs` realizer) under which the kernel-realization holds, so
the narrowed hypothesis is satisfiable.  `fieldEmitRealizes_mul_canonical`
threads it through to a full `FieldEmitRealizes` witness, confirming the bridge
delivers an inhabitant of the `GenericFieldEmitValue` hypothesis from the
relational MUL law.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldMulEmitRealizesFromCommSquare

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit
open CatCrypt.Crypto.SecureCompilation.RelationalFront
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.FieldEmitRealizesFromCommSquare

/-! ## §1  The limb-vector decode for a `KLimbPrimeMul`

We reuse `klimbDecode` (from the add discharge) applied to the underlying
`KLimbPrime` (`Q.toKLimbPrime`): read the `.TFp` slot's limb vector via
`readLimbs`, then `bignumVal`-decode it into `ZMod Q.q`.  This is the `decode`
argument of `FieldEmitRealizes` specialized to the relational front's limb
representation — the same decoder the add side uses, so add and mul leaves of
the same field share one decode convention. -/

/-! ## §2  The narrowed residual: the leaf computes the limb kernel `mlMulMod`

`KLimbMulKernelRealizes Q readLimbs leaf leafSpec` is the *narrowed* residual the
relational MUL law lets us condition on: the leaf-call value, read as a limb
vector, is exactly `mlMulMod Q.k Q.muTwo Q.ql` applied to the operand limb
vectors.  This is a fact about the **bytes** of the emitted kernel — a KAT /
AUCurves statement — strictly weaker than the original `FieldEmitRealizes`
residual, which spoke about the abstract `ZMod` value. -/

/-- **The narrowed (kernel-level) residual for MUL.**  For every operand pair, the
    limb-vector read of the leaf-call value equals the emitted
    `mlMulMod Q.k Q.muTwo Q.ql` kernel run on the operand limb vectors.  This is
    the KAT fact "the leaf's bytes are the kernel's bytes" — it says nothing about
    the Barrett reduce of the product, only that the limb words coincide. -/
def KLimbMulKernelRealizes (Q : KLimbPrimeMul)
    (readLimbs : RustVal .TFp → List (BitVec 64)) (leaf : String)
    (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    readLimbs
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = mlMulMod Q.k Q.muTwo Q.ql (readLimbs aVal) (readLimbs bVal)

/-! ## §3  The discharge: the MUL commuting square turns the kernel residual into
`FieldEmitRealizes`

This is the payload.  Given the narrowed kernel-realization (§2) and the
operand-encoding agreement (the slots are `encMLK` serializations), the abstract
field-mul `FieldEmitRealizes` follows — *because* `encMLK_mul_commutes` proves
`(a * b).val = bignumVal (mlMulMod …)`.  The `ZMod`-value content is supplied by
the proved commuting square, so the residual that remains is just the kernel
fact. -/

/-- **The commuting square discharges `FieldEmitRealizes` for `op = (· * ·)`.**

    Suppose:
    * `hkernel` — the narrowed residual: the leaf-call's limb read is
      `mlMulMod Q.k Q.muTwo Q.ql` on the operand limb reads (§2, a KAT fact); and
    * `henc` — operand-encoding agreement: every `.TFp` slot's limb read is the
      `encMLK` serialization of its `klimbDecode` residue (the canonical-form
      input convention).

    Then `FieldEmitRealizes Q.q (klimbDecode Q.toKLimbPrime readLimbs) (· * ·)
    leaf leafSpec` holds.  The proof reads the leaf-call through `klimbDecode`,
    rewrites the limb read by `hkernel` to `mlMulMod`, and closes with
    `encMLK_mul_commutes` — our *proved* relational MUL commuting square —
    turning the limb-kernel fact into the abstract `ZMod Q.q` field-product.  No
    `ZMod`-value content is assumed; it is discharged by the theorem. -/
theorem fieldEmitRealizes_mul_of_kernel
    (Q : KLimbPrimeMul) (readLimbs : RustVal .TFp → List (BitVec 64))
    (leaf : String) (leafSpec : LeafSpec)
    (hkernel : KLimbMulKernelRealizes Q readLimbs leaf leafSpec)
    (henc : ∀ v : RustVal .TFp,
      readLimbs v = encMLK Q.q Q.k (klimbDecode Q.toKLimbPrime readLimbs v)) :
    FieldEmitRealizes Q.q (klimbDecode Q.toKLimbPrime readLimbs) (· * ·) leaf leafSpec := by
  intro aVal bVal oldDest
  -- Abbreviate the decoded residues of the two operands.
  set a := klimbDecode Q.toKLimbPrime readLimbs aVal with ha
  set b := klimbDecode Q.toKLimbPrime readLimbs bVal with hb
  -- The leaf-call value, decoded: read its limbs (hkernel) → `mlMulMod` of the
  -- operand limbs → (henc) `mlMulMod` of the `encMLK` serializations.
  show klimbDecode Q.toKLimbPrime readLimbs
      (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = a * b
  unfold klimbDecode
  rw [hkernel aVal bVal oldDest, henc aVal, henc bVal]
  -- Now the goal is
  -- `(bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK … a) (encMLK … b)) : ZMod Q.q) = a * b`.
  -- `encMLK_mul_commutes` gives `(a * b).val = bignumVal (mlMulMod …)`; cast both sides.
  rw [← ha, ← hb]
  rw [← encMLK_mul_commutes Q a b]
  exact (ZMod.natCast_zmod_val (a * b))

/-! ## §4  Non-vacuity: a canonical limb-kernel realizer

We exhibit a concrete `LeafSpec` under which the narrowed kernel-realization (§2)
holds, and thread it through `fieldEmitRealizes_mul_of_kernel` to a full
`FieldEmitRealizes` witness — confirming the bridge produces an inhabitant of the
`GenericFieldEmitValue` hypothesis from the relational MUL law, not an
over-constraint. -/

/-- The canonical `CallSpec` realizing the `mlMulMod` limb kernel at `leaf`:
    at the target name it reads the two positional `.TFp` operands' limb vectors,
    runs `mlMulMod Q.k Q.muTwo Q.ql`, and re-encodes the result limb vector into a
    `.TFp` slot via a section `writeLimbs` (`readLimbs ∘ writeLimbs = id`);
    off-target it returns `oldDest`.  The limb-level MUL analogue of
    `klimbAddCallSpec`. -/
def klimbMulCallSpec (Q : KLimbPrimeMul)
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → List (BitVec 64) := fun a =>
        if ht : a.1 = TowerType.TFp then readLimbs (ht ▸ a.2) else []
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ writeLimbs (mlMulMod Q.k Q.muTwo Q.ql (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity for the narrowed residual.**  For the canonical realizer built
    from `klimbMulCallSpec` with a limb-write section (`readLimbs ∘ writeLimbs =
    id`), the kernel-realization holds — the narrowed hypothesis is satisfiable. -/
theorem klimbMulKernelRealizes_canonical (Q : KLimbPrimeMul)
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp)
    (hsection : ∀ l : List (BitVec 64), readLimbs (writeLimbs l) = l)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KLimbMulKernelRealizes Q readLimbs leaf
      { call := klimbMulCallSpec Q readLimbs writeLimbs leaf, limbStore := limbStore } := by
  intro aVal bVal oldDest
  show readLimbs (klimbMulCallSpec Q readLimbs writeLimbs leaf leaf .TFp [.TFp, .TFp]
      oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) = _
  simp only [klimbMulCallSpec, ite_true, dite_true, hsection]

/-- **Non-vacuity for the full bridge.**  Threading the canonical limb-kernel
    realizer through `fieldEmitRealizes_mul_of_kernel` (under the operand-encoding
    convention) yields a genuine `FieldEmitRealizes` inhabitant — so the
    relational MUL commuting square does deliver the `GenericFieldEmitValue`
    hypothesis. -/
theorem fieldEmitRealizes_mul_canonical (Q : KLimbPrimeMul)
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp)
    (hsection : ∀ l : List (BitVec 64), readLimbs (writeLimbs l) = l)
    (henc : ∀ v : RustVal .TFp,
      readLimbs v = encMLK Q.q Q.k (klimbDecode Q.toKLimbPrime readLimbs v))
    (leaf : String) (limbStore : LimbStoreSpec) :
    FieldEmitRealizes Q.q (klimbDecode Q.toKLimbPrime readLimbs) (· * ·) leaf
      { call := klimbMulCallSpec Q readLimbs writeLimbs leaf, limbStore := limbStore } :=
  fieldEmitRealizes_mul_of_kernel Q readLimbs leaf _
    (klimbMulKernelRealizes_canonical Q readLimbs writeLimbs hsection leaf limbStore) henc

/-! ## §5  Composed payload: emit → field VALUE, residual = limb kernel

Composing §3 with `GenericFieldEmitValue.emitFieldBinop_realizes_value` gives the
end-to-end statement: *running* the emitted `emitFieldBinop` program writes into
`dest` a value that decodes to the field product
`klimbDecode aVal * klimbDecode bVal` — with the *only* cross-prover residual now
the narrowed limb-kernel fact (§2), the `ZMod`-value content supplied by
`encMLK_mul_commutes`. -/

/-- **The emit→field-VALUE bridge with the residual narrowed to the MUL limb
    kernel.**  Under the narrowed kernel-realization (§2) and the operand-encoding
    convention, running `emitFieldBinop leaf dest a b` writes into `dest` a value
    that decodes (via `klimbDecode`) to the abstract field product.  Compared to
    `emitFieldBinop_realizes_value`, the `FieldEmitRealizes` premise is
    *discharged here* from the MUL commuting square, so the surviving residual is
    the limb-kernel KAT fact, not "leaf = abstract field value". -/
theorem emitFieldBinop_mul_value_of_kernel
    (N : Nat) (Q : KLimbPrimeMul) (readLimbs : RustVal .TFp → List (BitVec 64))
    (leafSpec : LeafSpec) (leaf dest av bv : String)
    (aVal bVal oldDest : RustVal .TFp)
    (hda : dest ≠ av) (hdb : dest ≠ bv) (hab : av ≠ bv)
    (hkernel : KLimbMulKernelRealizes Q readLimbs leaf leafSpec)
    (henc : ∀ v : RustVal .TFp,
      readLimbs v = encMLK Q.q Q.k (klimbDecode Q.toKLimbPrime readLimbs v)) :
    ∃ rs',
      RustExec N leafSpec (emitFieldBinop leaf dest av bv)
          (operandState dest av bv aVal bVal oldDest) rs'
        ∧ (∀ v, locatedLookup rs' ⟨dest, .TFp⟩ = some v →
            klimbDecode Q.toKLimbPrime readLimbs v
              = klimbDecode Q.toKLimbPrime readLimbs aVal
                * klimbDecode Q.toKLimbPrime readLimbs bVal) :=
  emitFieldBinop_realizes_value N Q.q (klimbDecode Q.toKLimbPrime readLimbs) (· * ·) leafSpec
    leaf dest av bv aVal bVal oldDest hda hdb hab
    (fieldEmitRealizes_mul_of_kernel Q readLimbs leaf leafSpec hkernel henc)

end CatCrypt.Crypto.SecureCompilation.FieldMulEmitRealizesFromCommSquare
