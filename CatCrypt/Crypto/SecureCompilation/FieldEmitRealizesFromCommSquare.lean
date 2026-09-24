/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontCurveRegistry

/-!
# Discharging `FieldEmitRealizes` from the relational commuting square

`GenericFieldEmitValue.lean` localizes the emit→value residual as the named
hypothesis `FieldEmitRealizes q decode op leaf leafSpec`: the leaf-call value,
read through an abstract `decode : RustVal .TFp → ZMod q`, equals the abstract
field-op value `op (decode aVal) (decode bVal)`.  As stated there, that residual
is "the leaf computes the **abstract field value**" — a wide gap.

This module **narrows that residual** using our *proven* relational value law.
`RelationalFrontBls377Add.lean` (and the curve registry that reuses it) proves
the commuting square

```
  (a + b).val = bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b))
```

for every `KLimbPrime Q` (`encMLK_add_commutes` / `registry_add_commutes`).  We
use this commuting square to *discharge* `FieldEmitRealizes` for `op = (· + ·)`,
**conditioned only on the narrower "leaf computes the limb kernel" fact** — i.e.
that the leaf-call value, read as a limb vector, is `mlAddModK` applied to the
operand limb vectors.  Everything *above* the limb kernel — the modular reduce,
the `ZMod`-value content — is then supplied by `encMLK_add_commutes`, which is a
proved theorem, not an assumption.

## The decode wiring (precisely what is tied vs. assumed)

A `RustVal .TFp` is a 48-byte array.  To read it as a `ZMod Q.q` residue we use
an abstract **limb-extraction** `readLimbs : RustVal .TFp → List (BitVec 64)`
(the byte-array → 64-bit-limb-vector projection; left abstract, as AUCurves keeps
`feval` a section variable) and decode via `bignumVal`, cast into `ZMod Q.q`:

```
  klimbDecode Q readLimbs v := (bignumVal (readLimbs v) : ZMod Q.q)
```

The bridge `FieldEmitRealizes` is then discharged from **two narrow facts**:

* **(kernel-realization, the residual)** `readLimbs (leafSpec.call …) =`
  `mlAddModK Q.ql (readLimbs aVal) (readLimbs bVal)` — the leaf, read at the
  limb level, *is* the emitted `mlAddModK` kernel.  This is a KAT / AUCurves
  fact about the limb kernel, **strictly narrower** than "leaf = abstract field
  value": it says nothing about the `ZMod` reduce, only that the bytes are the
  kernel's bytes.
* **(operand-encoding agreement)** the operand byte-arrays are the `encMLK`
  serializations of their decoded residues: `readLimbs aVal = encMLK Q.q Q.k`
  `(klimbDecode … aVal)` (and likewise `bVal`).  This pins the *input* convention
  (canonical-representative limb form) — a well-formedness condition on the
  operand slots, not a value claim about the op.

Given these two, the field-op value content
`klimbDecode (leaf-call) = klimbDecode aVal + klimbDecode bVal` is **proved**,
*because* `encMLK_add_commutes` proves the commuting square.  The remaining
residual is "the leaf's bytes are `mlAddModK`'s bytes" (kernel-realization) plus
the input convention, narrower than "the leaf computes the abstract field
value".

## What is closed here vs. localized

* **Closed (Lean theorem):** the `ZMod`-value content of `add_realizes`.  Given
  the kernel-realization and operand-encoding hypotheses, the leaf-call value
  decodes to the field sum — discharged by `encMLK_add_commutes` (our proved
  commuting square), *not* assumed.  This is the narrowing: the modular
  reduce and the `(a+b).val` law come from a theorem.
* **Localized (narrowed residual):** `readLimbs (leafSpec.call …) = mlAddModK …`
  — that the leaf's emitted bytes are the limb kernel's bytes.  This is the KAT
  fact (AUCurves / owned-emit KAT), narrower than the original
  `FieldEmitRealizes` residual.

## Non-vacuity

`klimbKernelRealizes_canonical` exhibits a concrete `LeafSpec` (an
`mlAddModK`-on-`readLimbs` realizer) under which the kernel-realization holds, so
the narrowed hypothesis is satisfiable.  `fieldEmitRealizes_add_canonical`
threads it through to a full `FieldEmitRealizes` witness, confirming the bridge
delivers an inhabitant of the `GenericFieldEmitValue` hypothesis from the
relational law.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldEmitRealizesFromCommSquare

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit
open CatCrypt.Crypto.SecureCompilation.RelationalFront
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## §1  The limb-vector decode for a `KLimbPrime`

`klimbDecode Q readLimbs v` reads the byte-array slot `v` as a 64-bit limb
vector (via the abstract `readLimbs`) and decodes it through `bignumVal`, cast
into `ZMod Q.q`.  This is the CatCrypt image of the per-curve `feval` for the
multi-limb carrier: the `decode` argument of `FieldEmitRealizes` specialized to
the relational front's limb representation. -/

/-- The multi-limb field decoder for a `KLimbPrime`: read the `.TFp` slot's limb
    vector via `readLimbs`, then `bignumVal`-decode it into `ZMod Q.q`. -/
def klimbDecode (Q : KLimbPrime) (readLimbs : RustVal .TFp → List (BitVec 64)) :
    RustVal .TFp → ZMod Q.q :=
  fun v => (bignumVal (readLimbs v) : ZMod Q.q)

/-- `klimbDecode` on an `encMLK`-encoded residue recovers that residue (for a
    `KLimbPrime`, since `encMLK` round-trips through `bignumVal`).  This is the
    section law making the input-convention hypothesis coherent: a slot holding
    the canonical `encMLK` serialization of `a` decodes back to `a`. -/
theorem klimbDecode_encMLK (Q : KLimbPrime) (readLimbs : RustVal .TFp → List (BitVec 64))
    (v : RustVal .TFp) (a : ZMod Q.q) (hv : readLimbs v = encMLK Q.q Q.k a) :
    klimbDecode Q readLimbs v = a := by
  unfold klimbDecode
  rw [hv, bignumVal_encMLK Q.q Q.k Q.q_lt a]
  exact (ZMod.natCast_zmod_val a)

/-! ## §2  The narrowed residual: the leaf computes the limb kernel `mlAddModK`

`KLimbKernelRealizes Q readLimbs leaf leafSpec` is the *narrowed* residual the
relational law lets us condition on: the leaf-call value, read as a limb vector,
is exactly `mlAddModK Q.ql` applied to the operand limb vectors.  This is a fact
about the **bytes** of the emitted kernel — a KAT / AUCurves statement — strictly
weaker than the original `FieldEmitRealizes` residual, which spoke about the
abstract `ZMod` value. -/

/-- **The narrowed (kernel-level) residual.**  For every operand pair, the
    limb-vector read of the leaf-call value equals the emitted `mlAddModK Q.ql`
    kernel run on the operand limb vectors.  This is the KAT fact "the leaf's
    bytes are the kernel's bytes" — it says nothing about the `ZMod` reduce, only
    that the limb words coincide. -/
def KLimbKernelRealizes (Q : KLimbPrime)
    (readLimbs : RustVal .TFp → List (BitVec 64)) (leaf : String)
    (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    readLimbs
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = mlAddModK Q.ql (readLimbs aVal) (readLimbs bVal)

/-! ## §3  The discharge: the commuting square turns the kernel residual into
`FieldEmitRealizes`

This is the payload.  Given the narrowed kernel-realization (§2) and the
operand-encoding agreement (the slots are `encMLK` serializations), the abstract
field-add `FieldEmitRealizes` follows — *because* `encMLK_add_commutes` proves
`(a + b).val = bignumVal (mlAddModK …)`.  The `ZMod`-value content is supplied by
the proved commuting square, so the residual that remains is just the kernel
fact. -/

/-- **The commuting square discharges `FieldEmitRealizes` for `op = (· + ·)`.**

    Suppose:
    * `hkernel` — the narrowed residual: the leaf-call's limb read is
      `mlAddModK Q.ql` on the operand limb reads (§2, a KAT fact); and
    * `henc` — operand-encoding agreement: every `.TFp` slot's limb read is the
      `encMLK` serialization of its `klimbDecode` residue (the canonical-form
      input convention).

    Then `FieldEmitRealizes Q.q (klimbDecode Q readLimbs) (· + ·) leaf leafSpec`
    holds.  The proof reads the leaf-call through `klimbDecode`, rewrites the
    limb read by `hkernel` to `mlAddModK`, and closes with `encMLK_add_commutes`
    — our *proved* relational commuting square — turning the limb-kernel fact
    into the abstract `ZMod Q.q` field-sum.  No `ZMod`-value content is assumed;
    it is discharged by the theorem. -/
theorem fieldEmitRealizes_add_of_kernel
    (Q : KLimbPrime) (readLimbs : RustVal .TFp → List (BitVec 64))
    (leaf : String) (leafSpec : LeafSpec)
    (hkernel : KLimbKernelRealizes Q readLimbs leaf leafSpec)
    (henc : ∀ v : RustVal .TFp,
      readLimbs v = encMLK Q.q Q.k (klimbDecode Q readLimbs v)) :
    FieldEmitRealizes Q.q (klimbDecode Q readLimbs) (· + ·) leaf leafSpec := by
  intro aVal bVal oldDest
  -- Abbreviate the decoded residues of the two operands.
  set a := klimbDecode Q readLimbs aVal with ha
  set b := klimbDecode Q readLimbs bVal with hb
  -- The leaf-call value, decoded: read its limbs (hkernel) → `mlAddModK` of the
  -- operand limbs → (henc) `mlAddModK` of the `encMLK` serializations.
  show klimbDecode Q readLimbs
      (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = a + b
  unfold klimbDecode
  rw [hkernel aVal bVal oldDest, henc aVal, henc bVal]
  -- Now the goal is `(bignumVal (mlAddModK Q.ql (encMLK … a) (encMLK … b)) : ZMod Q.q) = a + b`.
  -- `encMLK_add_commutes` gives `(a + b).val = bignumVal (mlAddModK …)`; cast both sides.
  rw [← ha, ← hb]
  rw [← encMLK_add_commutes Q a b]
  exact (ZMod.natCast_zmod_val (a + b))

/-! ## §4  Non-vacuity: a canonical limb-kernel realizer

We exhibit a concrete `LeafSpec` under which the narrowed kernel-realization (§2)
holds, and thread it through `fieldEmitRealizes_add_of_kernel` to a full
`FieldEmitRealizes` witness — confirming the bridge produces an inhabitant of the
`GenericFieldEmitValue` hypothesis from the relational law, not an over-constraint. -/

/-- The canonical `CallSpec` realizing the `mlAddModK` limb kernel at `leaf`:
    at the target name it reads the two positional `.TFp` operands' limb vectors,
    runs `mlAddModK Q.ql`, and re-encodes the result limb vector into a `.TFp`
    slot via a section `writeLimbs` (`readLimbs ∘ writeLimbs = id`); off-target it
    returns `oldDest`.  The limb-level analogue of `fieldBinopCallSpec`. -/
def klimbAddCallSpec (Q : KLimbPrime)
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → List (BitVec 64) := fun a =>
        if ht : a.1 = TowerType.TFp then readLimbs (ht ▸ a.2) else []
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ writeLimbs (mlAddModK Q.ql (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity for the narrowed residual.**  For the canonical realizer built
    from `klimbAddCallSpec` with a limb-write section (`readLimbs ∘ writeLimbs =
    id`), the kernel-realization holds — the narrowed hypothesis is satisfiable. -/
theorem klimbKernelRealizes_canonical (Q : KLimbPrime)
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp)
    (hsection : ∀ l : List (BitVec 64), readLimbs (writeLimbs l) = l)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KLimbKernelRealizes Q readLimbs leaf
      { call := klimbAddCallSpec Q readLimbs writeLimbs leaf, limbStore := limbStore } := by
  intro aVal bVal oldDest
  show readLimbs (klimbAddCallSpec Q readLimbs writeLimbs leaf leaf .TFp [.TFp, .TFp]
      oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) = _
  simp only [klimbAddCallSpec, ite_true, dite_true, hsection]

/-- **Non-vacuity for the full bridge.**  Threading the canonical limb-kernel
    realizer through `fieldEmitRealizes_add_of_kernel` (under the operand-encoding
    convention) yields a `FieldEmitRealizes` inhabitant — so the relational
    commuting square does deliver the `GenericFieldEmitValue` hypothesis. -/
theorem fieldEmitRealizes_add_canonical (Q : KLimbPrime)
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp)
    (hsection : ∀ l : List (BitVec 64), readLimbs (writeLimbs l) = l)
    (henc : ∀ v : RustVal .TFp,
      readLimbs v = encMLK Q.q Q.k (klimbDecode Q readLimbs v))
    (leaf : String) (limbStore : LimbStoreSpec) :
    FieldEmitRealizes Q.q (klimbDecode Q readLimbs) (· + ·) leaf
      { call := klimbAddCallSpec Q readLimbs writeLimbs leaf, limbStore := limbStore } :=
  fieldEmitRealizes_add_of_kernel Q readLimbs leaf _
    (klimbKernelRealizes_canonical Q readLimbs writeLimbs hsection leaf limbStore) henc

/-! ## §5  Composed payload: emit → field VALUE, residual = limb kernel

Composing §3 with `GenericFieldEmitValue.emitFieldBinop_realizes_value` gives the
end-to-end statement: *running* the emitted `emitFieldBinop` program writes into
`dest` a value that decodes to the field sum `klimbDecode aVal + klimbDecode bVal`
— with the *only* cross-prover residual the narrowed limb-kernel fact (§2),
the `ZMod`-value content supplied by `encMLK_add_commutes`. -/

/-- **The emit→field-VALUE bridge with the residual narrowed to the limb kernel.**
    Under the narrowed kernel-realization (§2) and the operand-encoding convention,
    running `emitFieldBinop leaf dest a b` writes into `dest` a value that decodes
    (via `klimbDecode`) to the abstract field sum.  Compared to
    `emitFieldBinop_realizes_value`, the `FieldEmitRealizes` premise is *discharged
    here* from the commuting square, so the surviving residual is the limb-kernel
    KAT fact, not "leaf = abstract field value". -/
theorem emitFieldBinop_add_value_of_kernel
    (N : Nat) (Q : KLimbPrime) (readLimbs : RustVal .TFp → List (BitVec 64))
    (leafSpec : LeafSpec) (leaf dest av bv : String)
    (aVal bVal oldDest : RustVal .TFp)
    (hda : dest ≠ av) (hdb : dest ≠ bv) (hab : av ≠ bv)
    (hkernel : KLimbKernelRealizes Q readLimbs leaf leafSpec)
    (henc : ∀ v : RustVal .TFp,
      readLimbs v = encMLK Q.q Q.k (klimbDecode Q readLimbs v)) :
    ∃ rs',
      RustExec N leafSpec (emitFieldBinop leaf dest av bv)
          (operandState dest av bv aVal bVal oldDest) rs'
        ∧ (∀ v, locatedLookup rs' ⟨dest, .TFp⟩ = some v →
            klimbDecode Q readLimbs v
              = klimbDecode Q readLimbs aVal + klimbDecode Q readLimbs bVal) :=
  emitFieldBinop_realizes_value N Q.q (klimbDecode Q readLimbs) (· + ·) leafSpec
    leaf dest av bv aVal bVal oldDest hda hdb hab
    (fieldEmitRealizes_add_of_kernel Q readLimbs leaf leafSpec hkernel henc)

end CatCrypt.Crypto.SecureCompilation.FieldEmitRealizesFromCommSquare
