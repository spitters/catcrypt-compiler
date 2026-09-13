/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Bridges.ReprTransferInstancesCircleSTARK
public import CatCrypt.Crypto.Bridges.ReprTransferUnary
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Add

/-!
# CircleSTARK M31 field layer — add/reduce decode squares + the full connection

`Bridges/ReprTransferInstancesCircleSTARK.lean` hosts the Mersenne-31
(`p = 2³¹ − 1`, CircleSTARK / Stwo base field) **multiply** lane: the emitted,
Com-compiled `m31MulFold` as a proven `BinOpHomOn` along the residue decode
`m31Decode`, with an unconditional encode/decode field equation and a `@[csimp]`
install. This module completes the **field layer** with the two remaining
front-emitted M31 kernels (`SecureCompilation/CompileFromHaxMersenne31Add.lean`):

* `circlestarkM31AddHom : BinOpHomOn m31Decode (· < p) m31AddFold (· + ·)` —
  the emitted branch-free conditional-subtract **add** as a domain-restricted
  homomorphism, discharged directly by the proven field commuting square
  `m31AddFold_eq_field` (no hypothesis);
* `circlestarkM31ReduceHom : UnaryHomOn m31Decode (·.toNat < 2⁶²) m31ReduceFold id`
  — the emitted standalone Mersenne `2³¹ ≡ 1` double-fold **reduce** as a unary
  decode square on the product domain: it is the identity on residue classes,
  discharged by `m31ReduceFold_eq_field`;
* `m31FieldAdd` / `m31FieldAdd_eq` / `@[csimp] m31FieldAddSpec_csimp` — the add
  analogue of `m31FieldMul_eq`: through the canonical encode the field equation
  holds unconditionally, so the emitted kernel installs as the compiled runtime
  implementation of the M31 field add;
* `circlestark_field_layer_connected` — the capstone: **all three** emitted M31
  field kernels (multiply, add, reduce), decoded, compute exactly the
  `Zm31 = ZMod (2³¹ − 1)` field operations. This is the M31 analogue of the Baby
  Bear `STARKEmittedFieldRealization.stark_field_layer_connected`.

CircleSTARK's soundness/ZK bound (`ZK/CircleSTARK/Security.lean`) is stated over
an abstract field of size `2³¹ − 1` (its `CircleSTARKSecurityParams` carries
error terms, not field operations), so the field-layer target here is the
concrete field `Zm31` itself — the same target the multiply lane uses.

## Residual (HONEST)

The M31 base-field **multiply, add, and reduce** are each connected via proven,
front-emitted kernels (`m31MulFold_eq_field` / `m31AddFold_eq_field` /
`m31ReduceFold_eq_field`); no hypothesis. Axioms are the standard three plus
the `native_decide` primality certificate for `p` (`fact_prime_m31`, inherited
from the multiply lane — the same set as the existing multiply-only
connection). CircleSTARK's
circle-group point operations and the FRI low-degree-proximity soundness remain
separate edges, orthogonal to this base-field layer.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.ReprTransferInstancesCircleSTARKField

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.Bridges.ReprTransferUnary (UnaryHomOn)
open CatCrypt.Crypto.Bridges.ReprTransferInstancesCircleSTARK
  (m31Decode m31Encode m31Encode_lt m31Decode_m31Encode m31FieldMul_eq
    circlestarkM31MulHom)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Add

/-! ## The emitted M31 add as a proven `BinOpHomOn` -/

/-- **The emitted M31 add as a proven `BinOpHomOn`.** On the canonical residue
    domain `a, b < p = 2³¹ − 1`, the front-emitted branch-free
    conditional-subtract add `m31AddFold` pushes through the decode `m31Decode`
    to the `Zm31` field sum. Discharged directly by the proven field commuting
    square `m31AddFold_eq_field` — no hypothesis. The multiply twin is
    `ReprTransferInstancesCircleSTARK.circlestarkM31MulHom`; the Baby Bear
    analogue is `ReprTransferInstances.starkAddHom`. -/
def circlestarkM31AddHom :
    BinOpHomOn m31Decode (· < 2147483647#64) m31AddFold (· + ·) where
  app_eq a b ha hb := m31AddFold_eq_field a b ha hb

/-- **The M31 field-add commuting square (proven).** On the canonical residue
    domain `a, b < p`, decoding the emitted `m31AddFold` output equals the
    `Zm31` field sum of the decoded inputs — recovered through the generic
    transfer layer by `BinOpHomOn.realizes` on `circlestarkM31AddHom`. -/
theorem circlestark_m31_field_add_realized (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    m31Decode (m31AddFold a b) = m31Decode a + m31Decode b :=
  circlestarkM31AddHom.realizes ha hb

/-! ## The emitted M31 reduce as a proven `UnaryHomOn`

The standalone Mersenne reduce is a *unary, non-homomorphic* kernel — exactly
the shape `ReprTransferUnary.UnaryHomOn` packages. Its abstract counterpart is
the identity on `Zm31`: the reduce projects a word to its canonical residue
without changing the residue class. -/

/-- **The emitted M31 reduce as a proven `UnaryHomOn`.** On the product domain
    `x < 2⁶²` (where every `BitVec 64` product of canonical residues lives,
    since `(p−1)² < 2⁶²`), the front-emitted Mersenne `2³¹ ≡ 1` double-fold
    reduce `m31ReduceFold` pushes through the decode `m31Decode` to the identity
    on `Zm31`. Discharged directly by `m31ReduceFold_eq_field`. -/
def circlestarkM31ReduceHom :
    UnaryHomOn m31Decode (fun x => x.toNat < 2 ^ 62) m31ReduceFold
      (id : Zm31 → Zm31) where
  app_eq x hx := m31ReduceFold_eq_field x hx

/-- **The M31 reduce decode square (proven).** On the product domain `x < 2⁶²`,
    decoding the emitted `m31ReduceFold` output equals decoding the input: the
    reduce is the identity on residue classes — recovered through the generic
    transfer layer by `UnaryHomOn.realizes` on `circlestarkM31ReduceHom`. -/
theorem circlestark_m31_reduce_realized (x : BitVec 64)
    (hx : x.toNat < 2 ^ 62) :
    m31Decode (m31ReduceFold x) = m31Decode x :=
  circlestarkM31ReduceHom.realizes hx

/-! ## The unconditional encode/decode field add + `@[csimp]` install -/

/-- **M31 field add backed by the front-emitted kernel `m31AddFold`** (the add
    twin of `ReprTransferInstancesCircleSTARK.m31FieldMul`, the Baby Bear
    `bbFieldAdd` analogue). -/
def m31FieldAdd (a b : Zm31) : Zm31 :=
  m31Decode (m31AddFold (m31Encode a) (m31Encode b))

/-- The emitted M31 add, through encode/decode, computes the field sum
    **unconditionally** — the canonical encoding guarantees the residue range,
    so the domain-restricted square `circlestark_m31_field_add_realized`
    applies. The multiply twin is
    `ReprTransferInstancesCircleSTARK.m31FieldMul_eq`. -/
theorem m31FieldAdd_eq (a b : Zm31) : m31FieldAdd a b = a + b := by
  unfold m31FieldAdd
  rw [circlestarkM31AddHom.realizes (m31Encode_lt a) (m31Encode_lt b),
    m31Decode_m31Encode, m31Decode_m31Encode]

/-- Spec field add (the constant `@[csimp]` installs the emitted impl for). -/
def m31FieldAddSpec (a b : Zm31) : Zm31 := a + b

/-- **Verified native compute.** `@[csimp]` installs the front-emitted M31 add
    `m31AddFold` (via encode/decode) as the compiled runtime implementation of
    the M31 field add — proof-carrying, the add twin of
    `ReprTransferInstancesCircleSTARK.m31FieldMulSpec_csimp`. -/
@[csimp] theorem m31FieldAddSpec_csimp : m31FieldAddSpec = m31FieldAdd := by
  funext a b; rw [m31FieldAdd_eq]; rfl

/-! ## The capstone: the M31 field layer is connected across all three kernels -/

/-- **The CircleSTARK M31 field layer is CONNECTED.**

    All three front-emitted Mersenne-31 field kernels — the Mersenne-fold
    **multiply** `m31MulFold`, the branch-free conditional-subtract **add**
    `m31AddFold`, and the standalone double-fold **reduce** `m31ReduceFold` —
    compute, under the residue decode `m31Decode`, exactly the operations of
    the field `Zm31 = ZMod (2³¹ − 1)` standing under CircleSTARK's abstract
    `|F| = 2³¹ − 1` soundness/ZK statement (`ZK/CircleSTARK/Security.lean`):

    * multiply and add hold **unconditionally** on encoded field elements
      (the canonical encode lands in the residue range);
    * reduce is the identity on residue classes on its product domain
      `x < 2⁶²` (where every product of canonical residues lives).

    Each square is discharged by the proven field ties of the front-emitted
    kernels (`m31MulFold_eq_field` / `m31AddFold_eq_field` /
    `m31ReduceFold_eq_field`) — no hypothesis; the only non-standard axiom is
    the `native_decide` primality certificate for `p`. This is the M31
    analogue of the Baby Bear
    `STARKEmittedFieldRealization.stark_field_layer_connected`, extending the
    multiply-only
    `ReprTransferInstancesCircleSTARK.circlestark_field_layer_connected` to the
    full field layer. -/
theorem circlestark_field_layer_connected :
    (∀ a b : Zm31, m31Decode (m31MulFold (m31Encode a) (m31Encode b)) = a * b)
    ∧ (∀ a b : Zm31, m31Decode (m31AddFold (m31Encode a) (m31Encode b)) = a + b)
    ∧ (∀ x : BitVec 64, x.toNat < 2 ^ 62 →
        m31Decode (m31ReduceFold x) = m31Decode x) :=
  ⟨fun a b => m31FieldMul_eq a b,
   fun a b => m31FieldAdd_eq a b,
   fun x hx => circlestark_m31_reduce_realized x hx⟩

end CatCrypt.Crypto.Bridges.ReprTransferInstancesCircleSTARKField
