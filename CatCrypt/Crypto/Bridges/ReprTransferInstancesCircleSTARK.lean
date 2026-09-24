/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Bridges.ReprTransfer
public import CatCrypt.Crypto.Bridges.ReprTransfer
public meta import CatCrypt.Crypto.Bridges.ReprTransferExpr
public import CatCrypt.Crypto.Bridges.ReprTransferExpr
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum.Prime

/-!
# `ReprTransfer` instance — CircleSTARK's Mersenne-31 (M31) base field

This module ports the **field-arithmetic** byte↔field correspondence of the
CircleSTARK (StarkWare Stwo) proof system onto the reusable proof-transfer layer
`Bridges/ReprTransfer.lean` / `Bridges/ReprTransferExpr.lean`. CircleSTARK's
soundness/zero-knowledge bound (`ZK/CircleSTARK/Security.lean`,
`ZK/CircleSTARK/FullSecurity.lean`, `ZK/CircleSTARKBound.lean`) is stated over an
abstract field of size `|F| = 2³¹ − 1` — the **Mersenne-31** base field M31. Here
we name that field concretely (`M31 = ZMod (2³¹ − 1)`) and connect its `*` to the
emitted, Com-compiled M31 multiply `m31MulFold`, so the M31 field lane is realized
by a real verified kernel (the field analogue of the Baby Bear `bbFieldMul` lane
in `ReprTransferInstances.lean`).

## The M31 field layer is CONNECTED via a proven Com-compiled kernel

The base-field multiply has an emitted, Com-compiled, **proven** realization:
`m31MulFold` (`SecureCompilation/CompileFromHaxMersenne31.lean`) is the Mersenne
`2³¹ ≡ 1` double-fold whose `BitVec 64` denotation the verified compiler emits as
a jasmin `Com`, and `CompileFromHaxMersenne31Tie.m31MulFold_eq_field` proves the
**field commuting square** tying it to `ZMod 2147483647` multiplication — the M31
analogue of Baby Bear's `barrett_realizes_fmul`. We host that proven square on
the generic transfer layer:

* `circlestarkM31MulHom : BinOpHomOn m31Decode (· < 2³¹−1) m31MulFold (· * ·)` —
  the emitted M31 multiply as a domain-restricted homomorphism along the residue
  decode `m31Decode = fromNat ∘ toNat`, discharged **directly** by
  `m31MulFold_eq_field` (no hypothesis).
* `circlestark_m31_field_realized` — the field commuting square, on the canonical
  residue domain `a, b < p`.
* `circlestark_field_layer_connected` / `m31FieldMul_eq` — encoding `Zm31` into
  the canonical range, the emitted kernel computes the field product
  **unconditionally** (the Baby Bear `bbFieldMul_eq` analogue), so it installs as
  a `@[csimp]` verified runtime implementation of the M31 multiply.

The M31 base-field multiply is realized by the proven Com-compiled `m31MulFold`,
not a named hypothesis.

## The parametric realization

`M31FieldRealization` (a named byte↔field square over an abstract carrier `γ`,
with `add` included) is a **parametric** form — the field analogue of
the elliptic-curve group bridges (`ReprTransferInstancesBulletproofs`/`IVC`/
`Halo2IPA`). It is still useful for the field-add lane (`m31MulFold` realizes
only the multiply) and for callers wanting the equality-reflecting
`EndoOpRealization` / composite-`OpExpr` transfer. The headline is the proven
`circlestark_field_layer_connected`.

## Scope

The M31 **base-field multiply** layer is CONNECTED via the proven Com-compiled
`m31MulFold` (`m31MulFold_eq_field`); no hypothesis and no custom axiom is used
for it. CircleSTARK's circle-group structure and FRI low-degree-proximity
soundness remain **separate** edges (the circle-group law / the assumed
FRI-proximity axiom), orthogonal to this base-field transfer. See
`ZK/CircleSTARK/Security.lean` for the abstract soundness/ZK statement this field
lane sits beneath.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.ReprTransferInstancesCircleSTARK

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31

/-! ## 1. The Mersenne-31 base field -/

/-- The **Mersenne-31** prime `p = 2³¹ − 1 = 2147483647`, the CircleSTARK / Stwo
    base-field modulus over which the soundness/ZK bound is stated
    (`ZK/CircleSTARK/Security.lean`, `fieldSize = 2^31 - 1`). -/
def m31Prime : ℕ := 2147483647

instance : NeZero m31Prime := ⟨by decide⟩

instance : Fact (Nat.Prime m31Prime) := ⟨by native_decide⟩

/-- The **Mersenne-31** base field `M31 = ZMod (2³¹ − 1)`. A field, since
    `m31Prime` is prime. This is the concrete field standing under CircleSTARK's
    abstract `|F| = 2³¹ − 1` soundness statement. Definitionally the same field as
    `CompileFromHaxMersenne31Tie.Zm31`, the field the emitted kernel is tied to. -/
abbrev M31 : Type := ZMod m31Prime

/-! ## 2. The parametric realization (named byte↔field hypothesis)

The proven, headline connection is in §3 below. This parametric structure is
a reusable form for the field-add lane and for the
equality-reflecting `EndoOpRealization` / composite-`OpExpr` transfer (the
emitted `m31MulFold` realizes only the multiply). It is the field analogue of the
elliptic-curve group bridges, which carry their group law as a parametric square. -/

/-- The byte↔field realization for the M31 base field, against byte-level
    field-multiply `bmul` and field-add `badd` on an abstract carrier `γ`: a
    chosen encoding `enc`, its injectivity `enc_inj` (so a byte-level equality
    reflects a field-level equality), and the two commuting squares
    `mul_commutes`/`add_commutes`. This is the **parametric** form; the concrete
    proven multiply realization is `circlestarkM31MulHom` (§3). -/
structure M31FieldRealization (γ : Type) (bmul badd : γ → γ → γ) where
  /-- The chosen encoding of M31 field elements as byte-level carrier values. -/
  enc : M31 → γ
  /-- Distinct field elements encode distinctly (equality reflection): this lets
      a byte-level equality reflect a field-level equality. -/
  enc_inj : Function.Injective enc
  /-- **The field-multiply commuting square** (parametric byte↔field edge). -/
  mul_commutes : ∀ a b : M31, enc (a * b) = bmul (enc a) (enc b)
  /-- **The field-add commuting square** (parametric byte↔field edge). -/
  add_commutes : ∀ a b : M31, enc (a + b) = badd (enc a) (enc b)

variable {γ : Type} {bmul badd : γ → γ → γ}

/-- The realization **is** an `EndoOpRealization` of the M31 field multiply by
    the byte-level `bmul`: the M31 multiply lane becomes an instance of the
    generic representation-transfer layer (`Bridges/ReprTransferExpr.lean`). -/
def M31FieldRealization.toMulEndoRealization (R : M31FieldRealization γ bmul badd) :
    EndoOpRealization (· * · : M31 → M31 → M31) bmul where
  enc := R.enc
  enc_inj := R.enc_inj
  commutes := R.mul_commutes

/-- The realization **is** an `EndoOpRealization` of the M31 field add by the
    byte-level `badd`. -/
def M31FieldRealization.toAddEndoRealization (R : M31FieldRealization γ bmul badd) :
    EndoOpRealization (· + · : M31 → M31 → M31) badd where
  enc := R.enc
  enc_inj := R.enc_inj
  commutes := R.add_commutes

/-! ### Single-op field transfer -/

/-- The field-multiply commuting square, exposed as a lemma: encoding the
    abstract M31 product equals the byte-level multiply on the encoded operands. -/
theorem m31_mul_realized (R : M31FieldRealization γ bmul badd) (a b : M31) :
    R.enc (a * b) = bmul (R.enc a) (R.enc b) := R.mul_commutes a b

/-- The field-add commuting square, exposed as a lemma. -/
theorem m31_add_realized (R : M31FieldRealization γ bmul badd) (a b : M31) :
    R.enc (a + b) = badd (R.enc a) (R.enc b) := R.add_commutes a b

/-- **Single-op multiply transfer.** An equation between two M31 field products
    holds **iff** the byte-level multiplies agree on the encoded operands —
    obtained from the abstraction theorem at depth one. -/
theorem circlestark_field_mul_transfer (R : M31FieldRealization γ bmul badd)
    (a b a' b' : M31) :
    a * b = a' * b' ↔ bmul (R.enc a) (R.enc b) = bmul (R.enc a') (R.enc b') := by
  have h := OpExpr.expr_eq_transfer R.toMulEndoRealization
    (.node (.leaf a) (.leaf b)) (.node (.leaf a') (.leaf b'))
  simpa [OpExpr.denoteAbs, OpExpr.denoteComp, M31FieldRealization.toMulEndoRealization] using h

/-- **Single-op add transfer.** An equation between two M31 field sums holds
    **iff** the byte-level adds agree on the encoded operands. -/
theorem circlestark_field_add_transfer (R : M31FieldRealization γ bmul badd)
    (a b a' b' : M31) :
    a + b = a' + b' ↔ badd (R.enc a) (R.enc b) = badd (R.enc a') (R.enc b') := by
  have h := OpExpr.expr_eq_transfer R.toAddEndoRealization
    (.node (.leaf a) (.leaf b)) (.node (.leaf a') (.leaf b'))
  simpa [OpExpr.denoteAbs, OpExpr.denoteComp, M31FieldRealization.toAddEndoRealization] using h

/-! ### Composite field-expression transfer -/

/-- **Composite multiplicative-expression transfer.** An equation between two
    whole composite M31 multiplicative expressions holds **iff** their byte-level
    denotations agree — the entire expression transfers, for free, from the
    single field-multiply commuting square (`mul_commutes`) via the abstraction
    theorem `OpExpr.expr_eq_transfer`, with no bespoke composite proof. This is
    the shape CircleSTARK's AIR-constraint / polynomial evaluations fold over the
    M31 base field. -/
theorem circlestark_field_expr_transfer (R : M31FieldRealization γ bmul badd)
    (e₁ e₂ : OpExpr M31) :
    e₁.denoteAbs (· * ·) = e₂.denoteAbs (· * ·) ↔
      e₁.denoteComp R.toMulEndoRealization = e₂.denoteComp R.toMulEndoRealization :=
  OpExpr.expr_eq_transfer R.toMulEndoRealization e₁ e₂

/-! ## 3. The PROVEN realization via the emitted, Com-compiled `m31MulFold`

This is the headline. The emitted Mersenne-fold multiply
`m31MulFold` realizes the M31 base-field multiply, discharged directly by the
proven field commuting square `CompileFromHaxMersenne31Tie.m31MulFold_eq_field`
— no named hypothesis. This mirrors the Baby Bear `starkPoseidon2MulHom` /
`bbFieldMul` lane in `ReprTransferInstances.lean`. We work over
`Zm31 = ZMod 2147483647` (the field `m31MulFold_eq_field` is stated against,
definitionally equal to `M31`). -/

/-- The residue **decode** map: read the emitted kernel's `BitVec 64` output back
    as a `Zm31` field element via `fromNat ∘ toNat`. -/
def m31Decode (w : BitVec 64) : Zm31 := fromNat w.toNat

/-- **The emitted M31 multiply as a proven `BinOpHomOn`.** On the canonical
    residue domain `a, b < p = 2³¹ − 1`, the emitted, Com-compiled Mersenne-fold
    multiply `m31MulFold` pushes through the decode `m31Decode` to the `Zm31`
    field product. The homomorphism square is discharged **directly** by the
    proven field commuting square `m31MulFold_eq_field` — there is no hypothesis.
    The Baby Bear analogue is `ReprTransferInstances.starkPoseidon2MulHom`. -/
def circlestarkM31MulHom :
    BinOpHomOn m31Decode (· < 2147483647#64) m31MulFold (· * ·) where
  app_eq a b ha hb := m31MulFold_eq_field a b ha hb

/-- **The M31 field-multiply commuting square (proven).** On the canonical
    residue domain `a, b < p`, decoding the emitted `m31MulFold` output equals the
    `Zm31` field product of the decoded inputs — recovered through the generic
    transfer layer by `BinOpHomOn.realizes` on `circlestarkM31MulHom`. -/
theorem circlestark_m31_field_realized (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    m31Decode (m31MulFold a b) = m31Decode a * m31Decode b :=
  circlestarkM31MulHom.realizes ha hb

/-- Canonical **encode** `Zm31 → BitVec 64` (the field value as a machine word):
    always lands in the canonical residue range, so the realization holds
    unconditionally on encoded inputs. -/
def m31Encode (a : Zm31) : BitVec 64 := BitVec.ofNat 64 a.val

theorem m31Encode_toNat (a : Zm31) : (m31Encode a).toNat = a.val := by
  unfold m31Encode
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt a) (by norm_num))

theorem m31Decode_m31Encode (a : Zm31) : m31Decode (m31Encode a) = a := by
  unfold m31Decode fromNat; rw [m31Encode_toNat]; exact ZMod.natCast_rightInverse a

theorem m31Encode_lt (a : Zm31) : m31Encode a < 2147483647#64 := by
  rw [BitVec.lt_def, m31Encode_toNat]
  show a.val < (2147483647#64 : BitVec 64).toNat
  rw [show (2147483647#64 : BitVec 64).toNat = 2147483647 from by decide]
  exact ZMod.val_lt a

/-- **M31 field multiply backed by the emitted Com-compiled kernel `m31MulFold`**
    (the Baby Bear `bbFieldMul` analogue). -/
def m31FieldMul (a b : Zm31) : Zm31 :=
  m31Decode (m31MulFold (m31Encode a) (m31Encode b))

/-- The emitted M31 multiply, through encode/decode, computes the field product
    **unconditionally** — the canonical encoding guarantees the residue range, so
    the domain-restricted square `circlestark_m31_field_realized` applies. The
    Baby Bear analogue is `ReprTransferInstances.bbFieldMul_eq`. -/
theorem m31FieldMul_eq (a b : Zm31) : m31FieldMul a b = a * b := by
  unfold m31FieldMul
  rw [circlestarkM31MulHom.realizes (m31Encode_lt a) (m31Encode_lt b),
    m31Decode_m31Encode, m31Decode_m31Encode]

/-- **The M31 field layer is CONNECTED.** Encoding two `Zm31`
    field elements into the canonical range and running the emitted Com-compiled
    `m31MulFold`, the decoded output is exactly the `Zm31` field product. This is
    the proven field-layer connection, with no named hypothesis — discharged via
    `m31MulFold_eq_field`, the proven field commuting square of the emitted
    kernel. -/
theorem circlestark_field_layer_connected (a b : Zm31) :
    m31Decode (m31MulFold (m31Encode a) (m31Encode b)) = a * b :=
  m31FieldMul_eq a b

/-- Spec field multiply (the constant `@[csimp]` installs the emitted impl for). -/
def m31FieldMulSpec (a b : Zm31) : Zm31 := a * b

/-- **Verified native compute.** `@[csimp]` installs the emitted, Com-compiled
    Mersenne-31 multiply `m31MulFold` (via encode/decode) as the compiled runtime
    implementation of the M31 field multiply — proof-carrying, the Baby Bear
    `fieldMul_csimp` analogue. -/
@[csimp] theorem m31FieldMulSpec_csimp : m31FieldMulSpec = m31FieldMul := by
  funext a b; rw [m31FieldMul_eq]; rfl

end CatCrypt.Crypto.Bridges.ReprTransferInstancesCircleSTARK
