/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-!
# Applying `BinOpHomOn2` to the fixed-width multi-limb multiply

The Montgomery butterfly (`TransferButterflyJoint`) and the cross-lane combine
(`TransferLinCombTransport`) transported `BitVec 64`-lane binary kernels through a
decode map via the joint-domain homomorphism `BinOpHomOn2` — whose domain
`dom2 : α → α → Prop` is *binary*, so it can state a no-wrap precondition that
depends on **both** operands jointly and does NOT factor into two per-operand
bounds. This file applies the same engine object to the multi-limb bignum
**multiply** of `MultiLimbKernel.lean`.

The full schoolbook multiply `mulBignum : List (BitVec 64) → List (BitVec 64) →
List (BitVec 64)` is value-correct *unconditionally* — its output list simply
grows to fit the exact product (`mulBignum_val`). That makes it a binary op with a
*trivial* (`True`) domain, which carries no information. The interesting binary
condition appears when the product is stored at a **fixed limb width** `W` (the
size every real bignum field/register allocation actually uses): the truncation
`(mulBignum as bs).take W` is **lossless iff the product fits**, i.e.

```
bignumVal as * bignumVal bs < (2^64)^W .
```

This is a genuinely *joint* no-overflow bound on `(as, bs)`: a large `as` is
admissible exactly when `bs` is correspondingly small. It does NOT factor into two
per-operand bounds, so `ReprTransfer.BinOpHomOn`'s per-operand `dom` cannot state
it and the joint-domain `BinOpHomOn2` is required.

The pieces, mirroring `TransferLinCombTransport`:

1. `mulBignumW W` — the **fixed-`W`-width** machine multiply, the low `W` limbs of
   the schoolbook product `mulBignum`.
2. `mulBignumAbs` — the abstract product `(·) * (·)` of the decoded values.
3. `mulBignumDomJoint W` — the **genuine joint** no-overflow domain
   `bignumVal as * bignumVal bs < (2^64)^W`.
4. `decode_mulBignumW_joint` — the single `app_eq` commuting square on that domain,
   which **cites the existing value-correctness lemma** `mulBignum_val` (the
   schoolbook recombination, already proved) together with the lossless-truncation
   lemma `bignumVal_take_of_lt`. No schoolbook arithmetic is re-derived here.
5. `multiLimbHom2 W` — the transport, packaged as a `BinOpHomOn2`.
6. `mulBignumW_realizes_via_joint_transport` — the realization, read off
   `BinOpHomOn2.realizes` (NOT a fresh `simp`).
7. `mulBignumW_realizes_eq_handproof` — the engine-generated realization is
   `rfl`-equal to the directly-proved square (the Barrett-pilot tie): the transport
   adds the joint-domain *packaging*, not new mathematical content.

## Scope

`BinOpHomOn2` is map-level: the decode `bignumVal` is the Trocq map₁ transport
witness — no injectivity on the limb-list domain, **no univalence**, and no
`jasminc_preserves_ct`. The realization comes out of `BinOpHomOn2.realizes`. The
`app_eq` reuses `MultiLimbKernel.mulBignum_val` (the schoolbook value-correctness)
and `MultiLimbKernel.bignumVal_take_of_lt` (lossless fixed-width truncation) — the
recombination is *not* re-derived. As in the butterfly and the linear-combine
pilots, only the (exact, homomorphic) product is transported; any subsequent field
reduce (`condSubLimbs` / `barrettReduce`) is a separate unary stage.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TransferMultiLimbTransport

open CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## §1  The fixed-width machine op, the abstract product, and the joint domain -/

/-- The **fixed-`W`-width machine multiply**: the low `W` limbs of the schoolbook
    multi-limb product `mulBignum`. This is the multiply a real register/field
    allocation emits — a `W`-limb destination — and it agrees with the full product
    exactly when the product fits in `W` limbs (the joint domain below). -/
def mulBignumW (W : Nat) (as bs : List (BitVec 64)) : List (BitVec 64) :=
  (mulBignum as bs).take W

/-- The **abstract product** of the decoded limb-vectors: the value-level product
    over `ℕ`. (The decode map `bignumVal` carries each operand to its integer
    value; the abstract op is just multiplication.) -/
def mulBignumAbs (av bv : Nat) : Nat := av * bv

/-- The **genuine joint** no-overflow domain for the fixed-`W`-width multiply: the
    exact product of the two decoded values fits in `W` limbs,
    `bignumVal as * bignumVal bs < (2^64)^W`. This is a genuinely *binary* predicate
    on `(as, bs)` — it does NOT factor into two per-operand bounds (a large `as` is
    admissible iff `bs` is correspondingly small), which is exactly why
    `ReprTransfer.BinOpHomOn`'s per-operand `dom` cannot state it and the
    joint-domain `BinOpHomOn2` is required. -/
def mulBignumDomJoint (W : Nat) (as bs : List (BitVec 64)) : Prop :=
  bignumVal as * bignumVal bs < (2 ^ 64) ^ W

/-! ## §2  The homomorphism square on the joint domain -/

/-- The multi-limb homomorphism fact on the **joint** no-overflow domain: decoding
    the fixed-`W`-width product equals the abstract product on decoded operands. The
    per-pair hypothesis is the joint bound `bignumVal as * bignumVal bs < (2^64)^W`
    — no per-operand bound. The proof **cites the existing value-correctness lemma**
    `mulBignum_val` (the schoolbook recombination, already proved) plus the
    lossless-truncation lemma `bignumVal_take_of_lt`: the low `W` limbs lose nothing
    precisely under the joint bound. No schoolbook arithmetic is re-derived. -/
theorem decode_mulBignumW_joint (W : Nat) (as bs : List (BitVec 64))
    (hab : mulBignumDomJoint W as bs) :
    bignumVal (mulBignumW W as bs)
      = mulBignumAbs (bignumVal as) (bignumVal bs) := by
  simp only [mulBignumDomJoint] at hab
  simp only [mulBignumW, mulBignumAbs]
  -- The product list, truncated to its low `W` limbs, is lossless under the bound;
  -- its value is the schoolbook product `mulBignum_val`.
  rw [bignumVal_take_of_lt W (mulBignum as bs) (by rw [mulBignum_val]; exact hab),
    mulBignum_val]

/-- **The joint-domain transport, packaged as a `BinOpHomOn2`.** With the width `W`
    fixed, the fixed-width multiply `mulBignumW W` is a `BinOpHomOn2` along the
    decode map `bignumVal` on the **joint** sub-domain `mulBignumDomJoint W`, whose
    target is the abstract product `mulBignumAbs`. The commuting-square obligation is
    `decode_mulBignumW_joint` — joint hypothesis only. -/
def multiLimbHom2 (W : Nat) :
    BinOpHomOn2 (α := List (BitVec 64)) bignumVal (mulBignumDomJoint W)
      (mulBignumW W) mulBignumAbs where
  app_eq as bs hab := decode_mulBignumW_joint W as bs hab

/-- **The realization, GENERATED by the joint-domain transport.** The per-point
    realization equation for the fixed-width multi-limb multiply comes out of
    `BinOpHomOn2.realizes` applied to the `bignumVal` witness, with only the joint
    no-overflow hypothesis — NOT a fresh `simp`. -/
theorem mulBignumW_realizes_via_joint_transport (W : Nat) (as bs : List (BitVec 64))
    (hab : mulBignumDomJoint W as bs) :
    bignumVal (mulBignumW W as bs)
      = mulBignumAbs (bignumVal as) (bignumVal bs) :=
  (multiLimbHom2 W).realizes hab

/-! ## §3  The engine realization equals the hand proof (Barrett-pilot tie) -/

/-- **The engine-generated realization is `rfl`-equal to the hand proof.** Reading
    the realization off `(multiLimbHom2 W).realizes` is definitionally the same
    equation as calling `decode_mulBignumW_joint` directly: the `BinOpHomOn2`
    transport adds the joint-domain *packaging*, not new mathematical content. (Same
    relation as the cross-lane combine / the Barrett pilot.) -/
theorem mulBignumW_realizes_eq_handproof (W : Nat) (as bs : List (BitVec 64))
    (hab : mulBignumDomJoint W as bs) :
    mulBignumW_realizes_via_joint_transport W as bs hab
      = decode_mulBignumW_joint W as bs hab := rfl

/-! ## §4  The full (untruncated) product is the `W = ∞` limit -/

/-- **The untruncated product needs no joint bound.** Without a width cap the
    schoolbook list grows to fit, so `mulBignum`'s value is the abstract product on
    the *full* domain (`fun _ _ => True`) — exactly `mulBignum_val`, repackaged as a
    `BinOpHomOn2`. The fixed-width transport `multiLimbHom2 W` is the restriction of
    this to the no-overflow sub-domain, and recovers it as `W → ∞`. -/
def mulBignumHom2_full :
    BinOpHomOn2 (α := List (BitVec 64)) bignumVal (fun _ _ => True)
      mulBignum mulBignumAbs where
  app_eq as bs _ := mulBignum_val as bs

end CatCrypt.Crypto.SecureCompilation.TransferMultiLimbTransport
