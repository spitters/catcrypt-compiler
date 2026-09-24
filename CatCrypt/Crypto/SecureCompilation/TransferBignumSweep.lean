/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
public import CatCrypt.Crypto.Bridges.ReprTransferUnary
public import CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit
public import CatCrypt.Crypto.SecureCompilation.Bignum4CondSubEmit
public import CatCrypt.Crypto.SecureCompilation.BignumAddEmitN

/-!
# Trocq bignum sweep: the multi-limb add combine and conditional-subtract reduce

The fixed-width multi-limb multiply (`TransferMultiLimbTransport`) and the scalar
mod-add / mod-mul kernels (`TransferModKernels`) transported `combine ⊕ reduce`
kernels through a decode map via the joint-domain homomorphism `BinOpHomOn2` and
the unary transport `UnaryHomOn`.  This file applies the **same two engine
objects** to the *multi-limb* (limb-list, register-width) add/subtract/reduce
kernels of `MultiLimbKernel.lean` — the recombination layer that the emitted x86
blocks (`BignumAddEmitN.adcxChain_bignumVal`, `BignumCondSubEmit.condSub2_bignumVal`,
`Bignum4CondSubEmit.condSub4_bignumVal`) consume — replacing the bespoke
value-level `rw`-chains with engine-generated realizations.

The pieces:

* **§1 the multi-limb add combine** `addLimbs as bs 0` — a `BinOpHomOn2` along the
  decode `bignumVal`, on the (per-pair) equal-length domain `as.length =
  bs.length`.  With carry-in `0` the schoolbook carry chain is the *exact*
  integer sum (the list grows by a top carry limb), so the homomorphism square is
  `bignumVal (addLimbs as bs 0) = bignumVal as + bignumVal bs` — the cited
  `addLimbs_val`, no joint no-overflow bound needed (unlike the truncated
  fixed-width multiply, whose joint bound `TransferMultiLimbTransport` carries).

* **§2 the multi-limb conditional-subtract reduce** `condSubLimbs · p` — a
  `UnaryHomOn` along `bignumVal` at a **fixed modulus** `p`, on the reduce domain
  `x.length = p.length ∧ bignumVal x < 2 · bignumVal p`.  The square is the cited
  `condSubLimbs_val` (`bignumVal (condSubLimbs x p) = bignumVal x % bignumVal p`)
  — the over-limbs analogue of `bCondSub_toNat`, the very value the emit-side
  `condSub2_bignumVal` / `condSub4_bignumVal` read through `valLimbs_eq_bignumVal`.

* **§3 the composed multi-limb mod-add** `(a + b) mod p` — the two engine objects
  COMPOSE (the combine's decoded `ℕ` output is the reduce's decoded input), giving
  `bignumVal (condSubLimbs (addLimbs a b 0) p) = (bignumVal a + bignumVal b) % p`
  on the joint domain (equal lengths + the sum `< 2p` reduce bound).  The
  multi-limb analogue of `TransferModKernels.addmod_realizes_via_composed_transport`
  (which did the single-lane `BitVec 64` version).

* **§4 the emit-side tie** — the emitted x86 conditional-subtract blocks
  `condSub2_bignumVal` (2-limb) and `condSub4_bignumVal` (4-limb) compute exactly
  `src (φ x)` of the §2 reduce transport (`bignumVal x % bignumVal p`); recorded
  by `Iff.rfl`/`rfl` ties so the engine reduce and the emitted block share one
  statement.

Each generated realization is read off `.realizes`; each is tied back to the
hand-proved kernel fact by `rfl` (`*_eq_handproof`). The Trocq plumbing performs
the square→realization step; it does not supply the math (the
recombination `addLimbs_val` / `condSubLimbs_val`) nor the emit-block machine
semantics the hand lemmas inherit.

## Scope

`BinOpHomOn2` and `UnaryHomOn` are map-level (the decode `bignumVal : List
(BitVec 64) → ℕ` is the Trocq map₁ transport witness): no injectivity on the
limb-list domain, **no univalence**, and no `jasminc_preserves_ct`.  The
realization equations are read off `.realizes`, not a fresh `simp` over the limb
recombination or the emitted block.  The only inherited trust is the cited
`MultiLimbKernel` content (`addLimbs_val`, `condSubLimbs_val`) the kernel file
already carries — there is no free lunch; the combine square is the carry-chain
exact-sum fact, the reduce square is the conditional-subtract residue fact.  The
emit-side ties (§4) carry, in addition, exactly the x86 machine-semantics content
the cited `condSub*_bignumVal` already proves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TransferBignumSweep

open CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
open CatCrypt.Crypto.Bridges.ReprTransferUnary
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

universe u

/-! ## §1  The multi-limb add combine `addLimbs · · 0` as a `BinOpHomOn2`

The combine of every multi-limb modular add (and of the emitted `adcx` chain,
`BignumAddEmitN.adcxChain_bignumVal`) is the schoolbook limb-wise carry chain
`addLimbs as bs 0`.  With carry-in `0` it is the *exact* integer sum — the output
list grows by a top carry limb — so no joint no-overflow bound is needed; the
only per-pair side condition is matching limb length. -/

/-- The multi-limb add domain: the two limb lists have equal length (the only
    side condition `addLimbs_val` needs; with carry-in `0` the sum is exact,
    so there is *no* joint no-overflow bound — the list grows to fit). -/
def addLimbsDom (as bs : List (BitVec 64)) : Prop := as.length = bs.length

/-- **The multi-limb add-combine transport, packaged as a `BinOpHomOn2`.**  Along
    the decode `bignumVal`, the schoolbook carry chain `(as, bs) ↦ addLimbs as bs 0`
    pushes through to `ℕ` addition, on the equal-length domain `addLimbsDom`.  The
    square is the cited `addLimbs_val` (carry-in `0`, residual carry `0`); no
    recombination is re-derived. -/
def addLimbsCombineHom2 :
    BinOpHomOn2 (α := List (BitVec 64)) bignumVal addLimbsDom
      (fun as bs => addLimbs as bs 0) (· + ·) where
  app_eq as bs hlen := by
    simp only [addLimbsDom] at hlen
    have h := addLimbs_val as bs 0 (by decide) hlen
    simpa using h

/-- The multi-limb add-combine realization, read off `BinOpHomOn2.realizes`: on
    equal-length operands, decoding the carry chain equals the sum of decodes. -/
theorem addLimbs_realizes_via_joint (as bs : List (BitVec 64))
    (hlen : addLimbsDom as bs) :
    bignumVal (addLimbs as bs 0) = bignumVal as + bignumVal bs :=
  addLimbsCombineHom2.realizes hlen

/-- **The engine add-combine realization is `rfl`-equal to the hand square.**  The
    `BinOpHomOn2` transport adds the joint-domain *packaging*, not new content. -/
theorem addLimbs_realizes_eq_handproof (as bs : List (BitVec 64))
    (hlen : addLimbsDom as bs) :
    addLimbs_realizes_via_joint as bs hlen
      = addLimbsCombineHom2.app_eq as bs hlen := rfl

/-! ## §2  The multi-limb conditional-subtract reduce `condSubLimbs · p` as a `UnaryHomOn`

The reduce of every multi-limb modular kernel — and the emitted x86 blocks
`condSub2Block` (2-limb, `BignumCondSubEmit`) and `condSub4Block` (4-limb,
`Bignum4CondSubEmit`) — finishes a value `< 2p` to `· mod p` via the branchless
conditional subtract `condSubLimbs · p`.  At a fixed modulus `p` it is a
`UnaryHomOn` along `bignumVal`, the over-limbs twin of the single-lane
`TransferModKernels.condSubUnaryHom`. -/

/-- The multi-limb conditional-subtract reduce domain at fixed modulus `p`: the
    pre-reduce value has the same limb count as `p` and is `< 2 · bignumVal p`
    (the bound guaranteeing one conditional subtract suffices — the upper half of
    the Barrett bracket / the post-add sum bound). -/
def condSubLimbsDom (p x : List (BitVec 64)) : Prop :=
  x.length = p.length ∧ bignumVal x < 2 * bignumVal p

/-- **The multi-limb mod-`p` reduce transport, packaged as a `UnaryHomOn`.**  At a
    fixed modulus `p`, along the decode `bignumVal`, the machine conditional
    subtract `condSubLimbs · p` pushes through to the abstract reduce
    `· % bignumVal p` over `ℕ`, on the reduce domain `condSubLimbsDom`.  The single
    `app_eq` square is the cited `condSubLimbs_val` — the over-limbs analogue of
    `bCondSub_toNat`, which carries the conditional-subtract content. -/
def condSubLimbsUnaryHom (p : List (BitVec 64)) :
    UnaryHomOn bignumVal (condSubLimbsDom p)
      (fun x => condSubLimbs x p) (fun n => n % bignumVal p) where
  app_eq x := by
    rintro ⟨hlen, hx⟩
    exact condSubLimbs_val x p hlen hx

/-- The multi-limb reduce realization, read off `UnaryHomOn.realizes`: on a
    `< 2p` equal-length input, decoding the conditional subtract equals `· % p`
    of the decoded input. -/
theorem condSubLimbs_realizes_via_unary (p : List (BitVec 64)) {x : List (BitVec 64)}
    (h : condSubLimbsDom p x) :
    bignumVal (condSubLimbs x p) = bignumVal x % bignumVal p :=
  (condSubLimbsUnaryHom p).realizes h

/-- **The engine reduce realization is `rfl`-equal to the hand square.**  The
    `UnaryHomOn` transport adds the *packaging*, not new content. -/
theorem condSubLimbs_realizes_eq_handproof (p : List (BitVec 64)) {x : List (BitVec 64)}
    (h : condSubLimbsDom p x) :
    condSubLimbs_realizes_via_unary p h = (condSubLimbsUnaryHom p).app_eq x h := rfl

/-! ## §3  The composed multi-limb mod-add `(a + b) mod p`

The combine (`addLimbsCombineHom2`) and the reduce (`condSubLimbsUnaryHom p`)
COMPOSE: the combine's decoded `ℕ` output `bignumVal a + bignumVal b` is the
reduce's decoded input, glued at the pre-reduce sum `s = addLimbs a b 0`.  The
product is the multi-limb field realization, the limb-list analogue of
`TransferModKernels.addmod_realizes_via_composed_transport`. -/

/-- **Multi-limb mod-add field realization, by COMPOSING combine ⊕ reduce.**  The
    conditional-subtract of the carry-chain sum, decoded, equals
    `(bignumVal a + bignumVal b) % bignumVal p` — obtained by composing
    * the add `BinOpHomOn2` (`decode (addLimbs a b 0) = decode a + decode b` on the
      equal-length domain), with
    * the `condSubLimbs` `UnaryHomOn` reduce (`decode (condSubLimbs s p) =
      decode s % p` on the `< 2p` domain),
    glued at the pre-reduce sum `s = addLimbs a b 0`.  NOT a fresh `rw`-chain — the
    field realization is the product of the two transports.  The reduce-side bound
    `hsum` is `bignumVal (addLimbs a b 0) < 2 · bignumVal p` (an input the caller
    supplies; for a real field add it follows from `a, b < p`, exactly as the
    single-lane `addmod` derived it from `a, b < p < 2^63`). -/
theorem modadd_realizes_via_composed_transport (a b p : List (BitVec 64))
    (hlen : a.length = b.length) (hsumlen : (addLimbs a b 0).length = p.length)
    (hsum : bignumVal (addLimbs a b 0) < 2 * bignumVal p) :
    bignumVal (condSubLimbs (addLimbs a b 0) p)
      = (bignumVal a + bignumVal b) % bignumVal p := by
  -- REDUCE transport: decode (condSubLimbs s p) = decode s % p, with s = addLimbs a b 0.
  rw [condSubLimbs_realizes_via_unary p (⟨hsumlen, hsum⟩ : condSubLimbsDom p (addLimbs a b 0))]
  -- COMBINE transport: decode (addLimbs a b 0) = decode a + decode b on equal length.
  rw [addLimbs_realizes_via_joint a b hlen]

/-! ## §4  The emit-side tie: the x86 conditional-subtract blocks realize the reduce

The emitted x86 blocks `condSub2Block` (2-limb) and `condSub4Block` (4-limb)
compute, in `bignumVal` terms, exactly `src (φ x)` of the §2 reduce transport —
`bignumVal x % bignumVal p`.  The hand lemmas `condSub2_bignumVal` /
`condSub4_bignumVal` (whose statement is that `ℕ` residue) consume precisely the
`condSubLimbs_val` content the §2 `UnaryHomOn` square packages, so the engine
reduce and the emitted block share one abstract residue spec. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit
open CatCrypt.Crypto.SecureCompilation.Bignum4CondSubEmit

/-- **The 2-limb emitted block realizes the §2 reduce spec.**  Reading the
    emitted `condSub2Block` output through `bignumVal` gives the *same* residue
    `bignumVal x % bignumVal p` the §2 reduce transport's `src ∘ φ` computes
    (here `x = [x0, x1]`, `p = [p0, p1]`).  Stated to match `condSub2_bignumVal`
    syntactically, it IS that hand lemma — the engine reduce and the emitted block
    share one residue spec. -/
theorem condSub2_realizes_reduce_spec (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1"] < 2 * bignumVal [s.get "p0", s.get "p1"]) :
    bignumVal [(runBlock s condSub2Block).get "d0", (runBlock s condSub2Block).get "d1"]
      = bignumVal [s.get "x0", s.get "x1"] % bignumVal [s.get "p0", s.get "p1"] :=
  condSub2_bignumVal s hx

/-- The 2-limb emit tie is `rfl`-equal to the hand lemma `condSub2_bignumVal`:
    same statement, the engine-reduce spec and the emitted-block hand lemma are
    one. -/
theorem condSub2_realizes_reduce_spec_eq_hand (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1"] < 2 * bignumVal [s.get "p0", s.get "p1"]) :
    condSub2_realizes_reduce_spec s hx = condSub2_bignumVal s hx := rfl

/-- **The 4-limb emitted block realizes the §2 reduce spec.**  As `condSub2`, for
    the P256-width 4-limb `condSub4Block`: its `bignumVal` output is the §2 reduce
    transport's `bignumVal x % bignumVal p` residue, exactly `condSub4_bignumVal`. -/
theorem condSub4_realizes_reduce_spec (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1", s.get "x2", s.get "x3"]
        < 2 * bignumVal [s.get "p0", s.get "p1", s.get "p2", s.get "p3"]) :
    bignumVal [(runBlock s condSub4Block).get "d0", (runBlock s condSub4Block).get "d1",
        (runBlock s condSub4Block).get "d2", (runBlock s condSub4Block).get "d3"]
      = bignumVal [s.get "x0", s.get "x1", s.get "x2", s.get "x3"]
        % bignumVal [s.get "p0", s.get "p1", s.get "p2", s.get "p3"] :=
  condSub4_bignumVal s hx

/-- The 4-limb emit tie is `rfl`-equal to the hand lemma `condSub4_bignumVal`. -/
theorem condSub4_realizes_reduce_spec_eq_hand (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1", s.get "x2", s.get "x3"]
        < 2 * bignumVal [s.get "p0", s.get "p1", s.get "p2", s.get "p3"]) :
    condSub4_realizes_reduce_spec s hx = condSub4_bignumVal s hx := rfl

/-! ## §5  Note: `subLimbs` does NOT fit a `BinOpHomOn2`

The multi-limb subtract `subLimbs xs ys` (`addLimbs xs (notLimbs ys) 1`) is the
borrow dual of the add, but its value lemma `subLimbs_val` is an *additive
identity*, not a homomorphism:

```
bignumVal (subLimbs xs ys) + bignumVal ys = bignumVal xs + (2^64)^xs.length .
```

There is no `src : ℕ → ℕ → ℕ` with `bignumVal (subLimbs xs ys) = src (bignumVal
xs) (bignumVal ys)` valid on the *full* equal-length domain: on borrow
(`bignumVal xs < bignumVal ys`) the top limb is `0` and the low limbs wrap, so
the decoded result is `bignumVal xs + (2^64)^n − bignumVal ys`, NOT `bignumVal xs
− bignumVal ys` (which would be negative / ill-typed over `ℕ`).  The wrap term
`(2^64)^xs.length` depends on the limb count `n`, not on the decoded *values*, so
it cannot be absorbed into a value-level binary `src`.  The honest home for
`subLimbs` is therefore the *reduce* composition (it appears inside
`condSubLimbs`, whose `UnaryHomOn` §2 covers it), not a standalone combine
`BinOpHomOn2`; transporting it as a combine would force the degenerate `True`
domain plus a carrier-level `src` carrying the `n`-dependent wrap, which is not a
value-level operation.  Documented here and skipped.
-/

end CatCrypt.Crypto.SecureCompilation.TransferBignumSweep
