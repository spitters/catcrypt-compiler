/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer

/-!
# Concrete realizer for the Curve25519 base-field arithmetic step — KAT-free

The Montgomery ladder (X25519, RFC 7748 §5; Bernstein 2006) computes an x-only
scalar multiplication by iterating a *field-arithmetic* step over the base field

```
   Fp25519 = ℤ / (2^255 − 19) ℤ.
```

Each ladder iteration is built from base-field operations on the projective
coordinates `(X₂, Z₂, X₃, Z₃)` — additions, subtractions, multiplications, and
one scalar multiply by the curve constant `a24 = (A − 2)/4 = 121665`.  This
module makes the **base-field arithmetic** piece of that step a *concrete,
round-trip-verified* kernel realizer over the `RustVal .TFp` byte carrier,
mirroring `ConcreteBarrettRealizer.lean` and `ConcreteSymFieldRealizer.lean`.

We realize, over `Fp = ZMod p25519` (`p25519 = 2^255 − 19`):

* the **scalar multiply by the Curve25519 constant** `a24 = 121665`
  (`mul121665`, a *unary* field op — `x ↦ x · 121665` in `Fp`), the distinctive
  multiply-by-`(A−2)/4` of the ladder's doubling formula `xDBL`;
* the **field addition** `(· + ·)` and **field subtraction** `(· − ·)` of the
  ladder (the `add`/`sub` of the projective coordinates), and the general field
  **multiply** `(· * ·)` (the `mul` of two coordinates) — *binary* field ops.

For the unary `mul121665` we build a base-256 byte codec over `RustVal .TFp`,
**PROVE** `decode ∘ encode = id` for all inputs (reusing the field codec's
`base256_digit_sum` engine via `ConcreteSymFieldRealizer.decodeF_encodeF`), and
prove the `KernelRealizes` theorem with **no kernel hypotheses** — only the
codec-fit side-conditions `width ≤ 48`, `p25519 < 2^(8·width)`.  For the binary
ops we package the existing `fieldBinop_realizes_concrete` realizer at the
Curve25519 prime.

## HONEST scope — what IS realized and what is NOT

* **Realized (unconditional Lean theorem, codec a theorem not a KAT):** the
  *base-field arithmetic* step of the ladder — the constant-multiply
  `mul121665`, and field `add`/`sub`/`mul` — each as a concrete,
  round-trip-verified `LeafSpec` realizer over `ZMod p25519`.  These are exactly
  the `+`, `−`, `×` of one Montgomery-ladder iteration (the ladder uses *only*
  these field ops — no inversion until the final coordinate recovery).
* **NOT realized (the honest residual):** the **abstract elliptic-curve group
  law** — point addition on the Curve25519 group as a group operation — is **not**
  a base-field codec target and is **not** claimed here.  The `ladderStep` over
  the abstract group `G × G` (`MoreKernelRegistryEntries.LadderStepKernelRealizes`)
  is realized only *parametrically* over an abstract transport `decode`, with no
  concrete codec; this file does **not** close that.  What this file does is
  shrink the residual by grounding the *field-arithmetic* sub-steps of the ladder
  in a proved byte codec — it does **not** ground the group operation, and it
  does **not** assert "Schnorr EC point ops are now grounded".
* **NOT proved (the same residual as every realizer file):** that the
  *jasmin-emitted machine bytes* of the real field kernels equal these realizers
  (the owned-machine-code route — a separate follow-up).

## Side-conditions are NOT kernel hypotheses

Only the codec-fit side-conditions remain (`width ≤ 48`, `p25519 < 2^(8·width)`),
threaded exactly as the field codec threads them — **not** as hypotheses on the
realized field operation.  The realized spec (`· * 121665`, `+`, `−`, `*`) is
unconditional.

## References
* RFC 7748: Elliptic Curves for Security, §5 (X25519, Montgomery ladder)
* D. J. Bernstein, "Curve25519: new Diffie–Hellman speed records", PKC 2006
  (the `a24 = (A − 2)/4 = 121665` doubling constant).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteEcScalarRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer

/-! ## §0  The Curve25519 base field, axiom-free

`p25519 = 2^255 − 19`.  We work over `ZMod p25519` for the codec — the codec and
round-trip need only `NeZero p25519` (a decidable positivity fact), **not**
primality.  We therefore declare our own `NeZero` instance rather than importing
`Fp25519`'s `Fact (Nat.Prime _)` (which is an assumed axiom).  Keeping primality
out makes every theorem here axiom-clean. -/

/-- The Curve25519 modulus `p = 2^255 − 19`. -/
abbrev p25519 : ℕ := 2 ^ 255 - 19

/-- `p25519 ≠ 0` — a decidable positivity fact, no primality needed. -/
instance instNeZeroP25519 : NeZero p25519 := ⟨by decide⟩

/-- The Curve25519 doubling constant `a24 = (A − 2)/4 = 121665`, as a base-field
    element of `ZMod p25519`. -/
def a24 : ZMod p25519 := (121665 : ℕ)

/-! ## §1  The unary constant-multiply `mul121665` over `Fp`

`mul121665 x = x · 121665` in `ZMod p25519` — the distinctive scalar multiply of
the X25519 ladder doubling step `xDBL` (multiply-by-`(A−2)/4`).  A *unary* field
op, so a `KernelRealizes` row over the carrier `ZMod p25519`. -/

/-- The Curve25519 constant-multiply `x ↦ x · 121665` over the base field. -/
def mul121665 (x : ZMod p25519) : ZMod p25519 := x * a24

/-! ## §2  The unary realizer `CallSpec` / `LeafSpec`

At the leaf it decodes the sole `.TFp` argument via the base-256 field codec
`decodeF`, applies `mul121665`, and re-encodes via `encodeF`; off-leaf returns
`oldDest`.  The unary analogue of `ConcreteSymFieldRealizer.fieldBinopCallSpec`. -/

/-- The concrete `mul121665` realizer's `CallSpec`. -/
def mul121665CallSpec (width : ℕ) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → ZMod p25519 := fun a =>
        if ht : a.1 = TowerType.TFp then decodeF width (ht ▸ a.2) else 0
      match args with
      | a :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encodeF width (mul121665 (pick a))
          else oldDest
      | _ => oldDest
    else oldDest

/-- The concrete `mul121665` realizer `LeafSpec`. -/
def mul121665LeafSpec (width : ℕ) (leaf : String) (limbStore : LimbStoreSpec) :
    LeafSpec :=
  { call := mul121665CallSpec width leaf, limbStore := limbStore }

/-! ## §3  The unconditional realization of the constant-multiply (no KAT) -/

/-- **Unconditional Curve25519 constant-multiply realization (no KAT, no abstract
    section).**  For `width ≤ 48` and `p25519 < 2^(8·width)`, the concrete realizer
    `mul121665LeafSpec width …` decodes its leaf-call value to `mul121665` of its
    decoded input — i.e. `x · 121665` in `ZMod p25519` — for **every** input,
    proved by the field round-trip `decodeF_encodeF`, not assumed via a test
    vector.

    `width ≤ 48` and `p25519 < 2^(8·width)` are the *codec-fit* side-conditions
    (so the `width` base-256 digits lie inside the 48-byte carrier and the field
    element is in range); they are **not** kernel hypotheses — the realized op
    `mul121665` is unconditional.  This grounds the *field-arithmetic*
    constant-multiply of the X25519 ladder doubling step; it does **not** ground
    the abstract elliptic-curve group law. -/
theorem mul121665_realizes_concrete (width : ℕ) (hw : width ≤ 48)
    (hq : p25519 < 2 ^ (8 * width)) (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := p25519) width) mul121665 leaf
      (mul121665LeafSpec width leaf limbStore) := by
  intro xVal oldDest
  show decodeF width (mul121665CallSpec width leaf leaf .TFp [.TFp] oldDest
      [⟨.TFp, xVal⟩]) = mul121665 (decodeF width xVal)
  simp only [mul121665CallSpec, ite_true, dite_true]
  rw [decodeF_encodeF width hw hq]

/-! ## §4  The binary field ops of the ladder — add / sub / mul over `Fp`

The ladder's projective-coordinate arithmetic uses field `add`, `sub`, and `mul`
(binary ops over `ZMod p25519`).  Each is the existing
`ConcreteSymFieldRealizer.fieldBinop_realizes_concrete` at the Curve25519 prime —
the same proved byte codec, specialized to `p = p25519`.  We expose the three
ladder ops as named realizations. -/

/-- The Curve25519 field-ADD leaf spec. -/
def fieldAddLeafSpec25519 (width : ℕ) (leaf : String) (limbStore : LimbStoreSpec) :
    LeafSpec :=
  fieldAddLeafSpec p25519 width leaf limbStore

/-- The Curve25519 field-SUB leaf spec. -/
def fieldSubLeafSpec25519 (width : ℕ) (leaf : String) (limbStore : LimbStoreSpec) :
    LeafSpec :=
  fieldBinopLeafSpec width ((· - ·) : ZMod p25519 → ZMod p25519 → ZMod p25519)
    leaf limbStore

/-- The Curve25519 field-MUL leaf spec. -/
def fieldMulLeafSpec25519 (width : ℕ) (leaf : String) (limbStore : LimbStoreSpec) :
    LeafSpec :=
  fieldMulLeafSpec p25519 width leaf limbStore

/-- **Unconditional Curve25519 field-ADD realization** — the ladder's coordinate
    addition over `ZMod p25519`, a row of the proved field codec at `p = p25519`. -/
theorem fieldAdd25519_realizes_concrete (width : ℕ) (hw : width ≤ 48)
    (hq : p25519 < 2 ^ (8 * width)) (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := p25519) width)
      ((· + ·) : ZMod p25519 → ZMod p25519 → ZMod p25519) leaf
      (fieldAddLeafSpec25519 width leaf limbStore) :=
  fieldAdd_realizes_concrete p25519 width hw hq leaf limbStore

/-- **Unconditional Curve25519 field-SUB realization** — the ladder's coordinate
    subtraction over `ZMod p25519`. -/
theorem fieldSub25519_realizes_concrete (width : ℕ) (hw : width ≤ 48)
    (hq : p25519 < 2 ^ (8 * width)) (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := p25519) width)
      ((· - ·) : ZMod p25519 → ZMod p25519 → ZMod p25519) leaf
      (fieldSubLeafSpec25519 width leaf limbStore) :=
  fieldBinop_realizes_concrete width hw hq
    ((· - ·) : ZMod p25519 → ZMod p25519 → ZMod p25519) leaf limbStore

/-- **Unconditional Curve25519 field-MUL realization** — the ladder's coordinate
    multiplication over `ZMod p25519`. -/
theorem fieldMul25519_realizes_concrete (width : ℕ) (hw : width ≤ 48)
    (hq : p25519 < 2 ^ (8 * width)) (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := p25519) width)
      ((· * ·) : ZMod p25519 → ZMod p25519 → ZMod p25519) leaf
      (fieldMulLeafSpec25519 width leaf limbStore) :=
  fieldMul_realizes_concrete p25519 width hw hq leaf limbStore

end CatCrypt.Crypto.SecureCompilation.ConcreteEcScalarRealizer
