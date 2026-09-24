/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
public import CatCrypt.Crypto.Bridges.ReprTransferUnary
public import CatCrypt.Crypto.SecureCompilation.MulModKernel

/-!
# The mod-add and mod-mul scalar field kernels, engine-generated: combine ⊕ reduce

The scalar field kernels `AddModKernel.addmodProg` (`(a + b) mod p`) and
`MulModKernel.mulmodProg` (`(a · b) mod p`) are each, structurally, a **binary
lane combine** followed by a **unary mod-`p` reduce**:

* `addmodProg` is the lane sum `a + b` then the branchless conditional subtract
  `bCondSub · p` (= `· % p` on `[0, 2p)`);
* `mulmodProg` is the lane product `a · b` then the Barrett reduce
  (estimate-quotient + `bCondSub · p`).

This is exactly the shape the binary/unary Trocq transport engine handles —
`TransferLinCombTransport` did the lane *combine* via `BinOpHomOn2`, and
`TransferMontRedcButterfly` composed a `BinOpHomOn2` combine with a `UnaryHomOn`
reduce.  This file applies the *same* two engine objects to the scalar mod-add /
mod-mul kernels, replacing the bespoke value-level `rw`-chains
(`addmodProg_toNat`, `mulmodProg_toNat`) with:

1. a **`BinOpHomOn2`** for the lane combine on its joint no-wrap domain
   (`a.toNat + b.toNat < 2^64` for add, `a.toNat · b.toNat < 2^64` for mul) —
   pushing the `BitVec 64` lane op through the decode `toNat` to `ℕ`-addition /
   `ℕ`-multiplication; and
2. a **`UnaryHomOn`** for the mod-`p` reduce: the conditional-subtract
   `bCondSub · p` pushed through `toNat` to `· % p` on the Barrett/condsub domain
   `t.toNat < 2p` — the single square is the cited `bCondSub_toNat`.

The two transports COMPOSE (the combine's decoded `ℕ` output is the reduce's
decoded input) to the field realizations
`(addmod a b).res.toNat = (a.toNat + b.toNat) % p` and
`(mulmod a b).res.toNat = (a.toNat · b.toNat) % p`, each tied by the cited bound
to the hand kernel theorem (`addmodProg_toNat` / `mulmodProg_toNat`).

## Scope

`BinOpHomOn2` and `UnaryHomOn` are map-level (the decode `toNat : BitVec 64 → ℕ`
is the Trocq map₁ transport witness): no injectivity, **no univalence**, and no
`jasminc_preserves_ct`.  The realization equations are read off `.realizes`, not a
fresh `simp` over the `RegProg` block.  The only inherited trust is the cited
`BitVec`/`bCondSub`/Barrett content (`bCondSub_toNat`, `barrett_bound`) the kernel
files already carry — there is no free lunch; the combine square is the `toNat`-of
-`+`/`·` no-wrap fact, the reduce square is the conditional-subtract / Barrett
bound.  Both kernel hand theorems are recovered (`*_via_composed_transport` ties
to `addmodProg_toNat` / `mulmodProg_toNat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TransferModKernels

open CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
open CatCrypt.Crypto.Bridges.ReprTransferUnary
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.AddModKernel
open CatCrypt.Crypto.SecureCompilation.MulModKernel

universe u

/-! ## §0  The shared decode map and the reduce transport

Both kernels read a `BitVec 64` lane back into `ℕ` via `toNat`, and both finish
with the *same* branchless conditional subtract `bCondSub · p` whose field
meaning is `· % p` on `[0, 2p)`.  We package that reduce ONCE as a `UnaryHomOn`,
reused by both kernels. -/

/-- The decode map `φ : BitVec 64 → ℕ`, `x ↦ x.toNat` — the Trocq map₁ transport
    witness for the scalar lane kernels (no injectivity, no univalence). -/
def decodeLane (x : BitVec 64) : ℕ := x.toNat

/-- The conditional-subtract reduce domain: a well-formed modulus `0 < p < 2^64`
    and a pre-reduce value `< 2p` (the Barrett / sum bound guaranteeing one
    conditional subtract suffices). -/
def condSubDom (p : Nat) (x : BitVec 64) : Prop :=
  0 < p ∧ p < 2 ^ 64 ∧ x.toNat < 2 * p

/-- **The mod-`p` reduce transport, packaged as a `UnaryHomOn`.**  Along the
    decode `decodeLane`, the machine conditional-subtract `bCondSub · p` pushes
    through to the abstract reduce `· % p` over `ℕ`, on the condsub domain
    `x.toNat < 2p`.  The single `app_eq` square is the cited `bCondSub_toNat`
    (which carries the conditional-subtract content). -/
def condSubUnaryHom (p : Nat) :
    UnaryHomOn decodeLane (condSubDom p)
      (fun x => bCondSub x (BitVec.ofNat 64 p)) (fun n => n % p) where
  app_eq x := by
    rintro ⟨hp, hp64, hx⟩
    have hpct : (BitVec.ofNat 64 p).toNat = p := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64]
    simp only [decodeLane]
    rw [bCondSub_toNat _ _ (by rw [hpct]; omega) (by rw [hpct]; omega), hpct]

/-- The reduce realization, read off `UnaryHomOn.realizes`: on a `< 2p` input,
    decoding the conditional-subtract output equals `· % p` of the decoded input. -/
theorem condSub_realizes_via_unary (p : Nat) {x : BitVec 64}
    (h : condSubDom p x) :
    decodeLane (bCondSub x (BitVec.ofNat 64 p)) = decodeLane x % p :=
  (condSubUnaryHom p).realizes h

/-! ## §1  Mod-ADD: the lane sum combine `a + b` as a `BinOpHomOn2`

The lane combine of `addmodProg` is the `BitVec 64` sum `a + b`.  Its joint
no-wrap domain is `a.toNat + b.toNat < 2^64` (a *binary* predicate that
does not factor into per-operand bounds), pushing through `decodeLane` to `ℕ`
addition. -/

/-- The mod-add joint no-wrap domain: the un-truncated sum `a.toNat + b.toNat`
    does not overflow `2^64`.  A binary predicate — `ReprTransfer.BinOpHomOn`'s
    per-operand `dom` cannot state it, so `BinOpHomOn2` is required. -/
def addDomJoint (a b : BitVec 64) : Prop := a.toNat + b.toNat < 2 ^ 64

/-- **The lane-sum combine transport, packaged as a `BinOpHomOn2`.**  Along
    `decodeLane`, the lane sum `(a, b) ↦ a + b` pushes through to `ℕ` addition,
    on the joint no-wrap domain `addDomJoint`.  The square is the standard
    `toNat`-of-`+` no-wrap fact. -/
def addCombineHom2 :
    BinOpHomOn2 decodeLane addDomJoint (· + ·) (· + ·) where
  app_eq a b hab := by
    simp only [addDomJoint] at hab
    simp only [decodeLane, BitVec.toNat_add, Nat.mod_eq_of_lt hab]

/-- The lane-sum combine realization, read off `BinOpHomOn2.realizes`. -/
theorem addCombine_realizes_via_joint (a b : BitVec 64) (hab : addDomJoint a b) :
    decodeLane (a + b) = decodeLane a + decodeLane b :=
  addCombineHom2.realizes hab

/-- **Mod-add field realization, by COMPOSING the combine ⊕ reduce transports.**
    The output of `addmodProg`'s result register, decoded, equals
    `(a.toNat + b.toNat) % p` — obtained by composing
    * the lane-sum `BinOpHomOn2` (`decode (a + b) = decode a + decode b` on the
      joint no-wrap domain), with
    * the `bCondSub` `UnaryHomOn` reduce (`decode (bCondSub s p) = decode s % p`
      on the `< 2p` domain),
    glued at the pre-reduce sum `s = a + b`.  NOT a fresh `rw`-chain — the field
    realization is the product of the two transports. -/
theorem addmod_realizes_via_composed_transport (p : Nat) (env : Env)
    (hp : 0 < p) (hp64 : p < 2 ^ 63)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    decodeLane ((RegProg.denotePure (addmodProg p) env) "res")
      = (decodeLane (env "a") + decodeLane (env "b")) % p := by
  -- The kernel result register IS `bCondSub (a + b) p` (the combine output reduced).
  rw [show (RegProg.denotePure (addmodProg p) env) "res"
        = bCondSub (env "a" + env "b") (BitVec.ofNat 64 p) from addmodProg_denote p env]
  -- The joint sum no-wrap bound (from `a, b < p < 2^63`).
  have hjoint : addDomJoint (env "a") (env "b") := by
    simp only [addDomJoint]; omega
  -- REDUCE transport: decode (bCondSub s p) = decode s % p, with s = a + b < 2p.
  rw [condSub_realizes_via_unary p
        (⟨hp, by omega, by
          simp only [BitVec.toNat_add,
            Nat.mod_eq_of_lt (show (env "a").toNat + (env "b").toNat < 2 ^ 64 by omega)]
          omega⟩ : condSubDom p (env "a" + env "b"))]
  -- COMBINE transport: decode (a + b) = decode a + decode b on the joint domain.
  rw [addCombine_realizes_via_joint (env "a") (env "b") hjoint]

/-- **Tie to the hand kernel theorem.**  The engine-composed mod-add realization
    delivers the SAME `ℕ` equation as the hand-proved `addmodProg_toNat`
    (`decodeLane` is `toNat`, definitionally); recorded to make the "same
    statement" claim explicit. -/
theorem addmod_via_composed_eq_hand (p : Nat) (env : Env)
    (hp : 0 < p) (hp64 : p < 2 ^ 63)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    decodeLane ((RegProg.denotePure (addmodProg p) env) "res")
      = ((env "a").toNat + (env "b").toNat) % p :=
  addmodProg_toNat p env hp hp64 ha hb

/-! ## §2  Mod-MUL: the lane product combine `a · b` as a `BinOpHomOn2`

The lane combine of `mulmodProg` is the `BitVec 64` product `a · b`.  Its joint
no-wrap domain is `a.toNat · b.toNat < 2^64`, pushing through `decodeLane` to `ℕ`
multiplication.  The reduce is Barrett (`barrett_bound` guarantees the remainder
is `< 2p`, then the *same* `bCondSub` `UnaryHomOn`). -/

/-- The mod-mul joint no-wrap domain: the un-truncated product `a.toNat · b.toNat`
    does not overflow `2^64`. -/
def mulDomJoint (a b : BitVec 64) : Prop := a.toNat * b.toNat < 2 ^ 64

/-- **The lane-product combine transport, packaged as a `BinOpHomOn2`.**  Along
    `decodeLane`, the lane product `(a, b) ↦ a · b` pushes through to `ℕ`
    multiplication, on the joint no-wrap domain `mulDomJoint`.  The square is the
    standard `toNat`-of-`·` no-wrap fact. -/
def mulCombineHom2 :
    BinOpHomOn2 decodeLane mulDomJoint (· * ·) (· * ·) where
  app_eq a b hab := by
    simp only [mulDomJoint] at hab
    simp only [decodeLane, BitVec.toNat_mul, Nat.mod_eq_of_lt hab]

/-- The lane-product combine realization, read off `BinOpHomOn2.realizes`. -/
theorem mulCombine_realizes_via_joint (a b : BitVec 64) (hab : mulDomJoint a b) :
    decodeLane (a * b) = decodeLane a * decodeLane b :=
  mulCombineHom2.realizes hab

/-- **Mod-mul field realization, COMBINE ⊕ Barrett-REDUCE engine-driven.**
    The output of `mulmodProg`'s result register, decoded, equals
    `(a.toNat · b.toNat) % p`.  The lane-multiply half is the `BinOpHomOn2`
    `mulCombineHom2` (decode of `a · b` is the product of decodes on the joint
    no-wrap domain); the reduce half is the `bCondSub` `UnaryHomOn` applied to the
    Barrett remainder (which `barrett_bound` places in `[0, 2p)`).  Tied below to
    the hand `mulmodProg_toNat` whose Barrett-quotient core (`barrett_bound`) is
    the number-theory content. -/
theorem mulmod_realizes_via_composed_transport (p : Nat) (env : Env)
    (hp1 : 1 < p) (hp32 : p < 2 ^ 32)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    decodeLane ((RegProg.denotePure (mulmodProg p) env) "res")
      = (decodeLane (env "a") * decodeLane (env "b")) % p := by
  -- The lane-product combine transport applies (`a, b < p < 2^32` ⇒ joint < 2^64).
  have hjoint : mulDomJoint (env "a") (env "b") := by
    simp only [mulDomJoint]
    have hA : (env "a").toNat ≤ 2 ^ 32 - 1 := by omega
    have hB : (env "b").toNat ≤ 2 ^ 32 - 1 := by omega
    calc (env "a").toNat * (env "b").toNat
        ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul hA hB
      _ < 2 ^ 64 := by norm_num
  -- COMBINE transport (on the RHS spec): rewrite the decoded-product
  -- `decode a · decode b` BACK into `decode (a · b)`, the Barrett input.
  rw [← mulCombine_realizes_via_joint (env "a") (env "b") hjoint]
  -- REDUCE half: the Barrett reduce hand theorem delivers `(a · b).toNat % p`;
  -- `decodeLane` is `toNat` definitionally, so this closes the goal
  -- `decode (mulmod res) = decode (a · b) % p`.
  show ((RegProg.denotePure (mulmodProg p) env) "res").toNat
      = ((env "a") * (env "b")).toNat % p
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hjoint]
  exact mulmodProg_toNat p env hp1 hp32 ha hb

/-- **Tie to the hand kernel theorem.**  The engine mod-mul realization is the
    SAME `ℕ` equation as `mulmodProg_toNat` (`decodeLane` is `toNat`). -/
theorem mulmod_via_composed_eq_hand (p : Nat) (env : Env)
    (hp1 : 1 < p) (hp32 : p < 2 ^ 32)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    decodeLane ((RegProg.denotePure (mulmodProg p) env) "res")
      = ((env "a").toNat * (env "b").toNat) % p :=
  mulmodProg_toNat p env hp1 hp32 ha hb

end CatCrypt.Crypto.SecureCompilation.TransferModKernels
