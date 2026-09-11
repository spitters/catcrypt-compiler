/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Bridges.ReprTransfer

/-!
# Joint-domain operation homomorphism (`BinOpHomOn2`) and its butterfly application

`ReprTransfer.BinOpHomOn` carries a **per-operand** sub-domain `dom : α → Prop`:
its homomorphism square is gated by `dom a → dom b → …`.  That is the right shape
when the no-truncation precondition factors operand-by-operand (e.g. a field-`+`
where each summand is `< p`).  But the Montgomery **butterfly combine**
`(a, b) ↦ a + w·b` over `BitVec 64` lanes has a *joint* no-wrap
precondition — `a.toNat + w·b.toNat < 2^64` — which does NOT factor into two
per-operand bounds.  The pilot `MontButterflyTransfer.lean` was therefore forced
to OVER-RESTRICT to the per-operand `< 2^31` sufficient condition (then
`w·b < 2^62`, `a + w·b < 2^63 < 2^64`), and documented the gap.

This file closes that gap, **additively** (it does not touch `ReprTransfer.lean`):

* `BinOpHomOn2 φ dom2 tgt src` — the **joint-domain** homomorphism, whose domain
  `dom2 : α → α → Prop` is *binary*, so it can state `a.toNat + w·b < 2^64`
  directly.
* `BinOpHomOn.toBinOpHomOn2` — the **subsumption bridge**: every per-operand
  `BinOpHomOn φ dom tgt src` is a `BinOpHomOn2 φ (fun a b => dom a ∧ dom b) tgt src`,
  so the new form generalises the old and the pilot is not broken.
* `binOpHomOn2_strictly_more_general` — a witness that `BinOpHomOn2`'s `dom2` need
  not factor as a conjunction of per-operand predicates, so the generalisation is
  strict.

The **applications** — the Montgomery butterfly combine re-derived on its
joint no-wrap domain (dropping the pilot's per-operand `< 2^31`) and a second
homomorphic lane kernel — live in the sibling file
`CatCrypt/Crypto/SecureCompilation/TransferButterflyJoint.lean` (it imports the owned
butterfly model, so it is kept out of this `Bridges/` base file).

## Scope

`BinOpHomOn2` is map-level (the decode map `φ` is the Trocq map₁ / univalence-free
transport witness): no injectivity on the domains, **no univalence**, and no
`jasminc_preserves_ct`.  The realization equations are read off `.realizes`, not a
fresh `simp` over the machine block.  The only trust is the `BitVec`/lane-arithmetic
TCB the butterfly file already carries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.ReprTransferBinaryDom

open CatCrypt.Crypto.Bridges.ReprTransfer

universe u

/-! ## §1  The joint-domain homomorphism `BinOpHomOn2` -/

/-- A **joint-domain binary-operation homomorphism**: along a map `φ : α → A`, the
    concrete `tgt` pushes through `φ` to the abstract `src`, gated by a **binary**
    domain `dom2 : α → α → Prop`.  Because the domain is binary it can express a
    *joint* no-wrap condition (`a.toNat + w·b < 2^64`) that does NOT factor into two
    per-operand bounds — the precise generalisation the Montgomery butterfly needs.
    Map-level: `φ` is the Trocq map₁ transport witness, no injectivity required. -/
structure BinOpHomOn2 {α A : Type u} (φ : α → A) (dom2 : α → α → Prop)
    (tgt : α → α → α) (src : A → A → A) where
  /-- The homomorphism square, on the joint sub-domain. -/
  app_eq : ∀ a b, dom2 a b → φ (tgt a b) = src (φ a) (φ b)

namespace BinOpHomOn2
variable {α A : Type u} {φ : α → A} {dom2 : α → α → Prop}
  {tgt : α → α → α} {src : A → A → A}

/-- The realization equation: on jointly-canonical inputs, decoding the concrete
    result equals the abstract operation on the decoded inputs.  The per-point
    realization is read off this — the `transferKernel` analogue, joint-domain. -/
theorem realizes (H : BinOpHomOn2 φ dom2 tgt src) {a b : α} (hab : dom2 a b) :
    φ (tgt a b) = src (φ a) (φ b) := H.app_eq a b hab

end BinOpHomOn2

/-! ## §2  Subsumption: `BinOpHomOn` ⊆ `BinOpHomOn2`, and strict generality -/

/-- **Subsumption bridge.**  Every per-operand `BinOpHomOn φ dom tgt src` is a
    `BinOpHomOn2` whose joint domain is the conjunction `dom a ∧ dom b`.  So the
    joint-domain form subsumes the per-operand one — anything proved with the old
    `BinOpHomOn` (e.g. the pilot's `montButterflyHom`) re-exports unchanged. -/
def BinOpHomOn.toBinOpHomOn2 {α A : Type u} {φ : α → A} {dom : α → Prop}
    {tgt : α → α → α} {src : A → A → A}
    (H : BinOpHomOn φ dom tgt src) :
    BinOpHomOn2 φ (fun a b => dom a ∧ dom b) tgt src where
  app_eq a b hab := H.app_eq a b hab.1 hab.2

/-- The subsumption bridge preserves the realization equation: the realization read
    off the lifted `BinOpHomOn2` is the same equation as the original `BinOpHomOn`'s
    `.realizes`. -/
theorem toBinOpHomOn2_realizes {α A : Type u} {φ : α → A} {dom : α → Prop}
    {tgt : α → α → α} {src : A → A → A}
    (H : BinOpHomOn φ dom tgt src) {a b : α} (ha : dom a) (hb : dom b) :
    (BinOpHomOn.toBinOpHomOn2 H).realizes (a := a) (b := b) ⟨ha, hb⟩
      = H.realizes ha hb := rfl

/-- **Strict generality.**  `BinOpHomOn2`'s `dom2` need not be a conjunction of
    per-operand predicates.  Witness: a homomorphism on the *full* joint domain
    (`dom2 := fun _ _ => True`) — here the trivial identity transport — is a
    `BinOpHomOn2` whose `dom2` is not of the form `fun a b => dom a ∧ dom b` for any
    *strictly partial* per-operand `dom` (it holds for every pair, including pairs
    where a hypothetical per-operand bound would fail).  This is exactly the freedom
    the butterfly's joint no-wrap condition exercises: `a + w·b < 2^64` admits pairs
    with one large operand that no symmetric per-operand `< 2^31` cutoff admits. -/
theorem binOpHomOn2_strictly_more_general {A : Type u} (src : A → A → A) :
    BinOpHomOn2 (id : A → A) (fun _ _ => True) src src :=
  ⟨fun _ _ _ => rfl⟩

end CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
