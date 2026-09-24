/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import Mathlib.Data.ZMod.Basic

/-!
# The MULTI-LIMB field-carrier port for the relational EC realization

`RelationalFrontInstances`/`RelationalFrontECMul` carry the relational front over a
**single-word** `BitVec 64` carrier: an injective-not-surjective encoding
`encMod251 : ZMod 251 → BitVec 64` and a commuting square
`encMod251 (a ∘ b) = bop (encMod251 a) (encMod251 b)` for the GF(251) ADD and MUL,
with `bop` an emitted single-word reducing kernel. The unified EC group law is
realized over that single-word field; the `RelationalFrontEC` docstring flags the
last axis — the `bls12_377` **377-bit multi-limb** carrier (6×64-bit limbs) — as the
remaining carrier swap.

This module ports the relational tie to a **multi-limb carrier**. The transfer
structure ports *verbatim*: `EndoOpRealization` (`Bridges/ReprTransferExpr`) is
already parametric over the carrier type `α`, so the carrier swaps from `BitVec 64`
to the **represented natural value** `ℕ` (read off the limb-vector by
`MultiLimbKernel.bignumVal`) with **no change to the transfer machinery** — and the
whole-term abstraction theorem `OpExpr.expr_eq_transfer` is inherited for free. Only
the field carrier and the reducing kernel change.

## Scope: reuse, do NOT re-prove, the multi-limb arithmetic

Multi-limb modular reduction is heavy (`bv_decide` cannot bitblast a 128-bit
conditional subtract, let alone 384-bit). So we **reuse** the repo's already-proved
**value-level** multi-limb kernels, never re-deriving the arithmetic:

* `MultiLimbKernel.addLimbs_val` — the carry chain computes the **exact integer
  sum** `bignumVal (addLimbs x y c) = bignumVal x + bignumVal y + c` (proved by
  induction over limbs via `adc_toNat`/`adc_carry_le`, axiom-clean).
* `MultiLimbKernel.condSubLimbs_val` — the multi-limb conditional subtract is the
  **modular reduction**: for `V < 2·bignumVal p`,
  `bignumVal (condSubLimbs x p) = bignumVal x % bignumVal p` (the over-limbs analog
  of the single-word `bCondSub_toNat`; proved limb-wise, **no** 128-bit `bv_decide`).
* `MultiLimbKernel.bignumVal_dropLast` — `bignumVal l.dropLast = bignumVal l %
  (2^64)^W`, the limb-drop that turns the `n+1`-limb carry-extended sum back into an
  `n`-limb operand for the conditional subtract.

The composite `mlAddMod` (multi-limb add then conditional-subtract reduce) computes
`(bignumVal x + bignumVal y) % P`, **with the modular reduce**, from those
three proved value laws (`mlAddMod_val`). No new multi-limb arithmetic is proved
here.

## The op realized: multi-limb modular ADD over a 2-limb prime

The cleanest op with a proved value-level reduce is the **multi-limb modular add**.
We instantiate at **`k = 2` limbs** — a prime `p` with `2p ≤ 2^128` — the
`bls12_377` carrier exhibited at reduced scale: the encoding, the reducing kernel, and
the commuting square are pinned to `k = 2` where the `condSubLimbs`/`addLimbs` length
bookkeeping is concrete. Swapping to the full `377`-bit (`k = 6`) prime changes only
the limb count `k` and the modulus limbs `[p0,…,p5]`; the `EndoOpRealization` and the
commuting-square *structure* is exactly this one (`addLimbs_val`/`condSubLimbs_val`
are already stated for `n`-limb lists).

## What is demonstrated vs. deferred

* **Demonstrated (fully proved):** the multi-limb-carrier `EndoOpRealization`
  (`addModRealization`) and the commuting square `(a + b).val = bignumVal (mlAddMod
  pl (encML2 a) (encML2 b))` for `ZMod p` ADD over a 2-limb prime, **including the
  multi-limb modular reduce** — reusing `addLimbs_val` + `condSubLimbs_val` +
  `bignumVal_dropLast`, not re-proving them. A concrete worked example is closed by
  `decide`.
* **Deferred:** the full `377`-bit (`k = 6`) instance is a `k`-bump (the proved
  kernels are already `n`-limb); the multi-limb **MUL** modular reduce (Montgomery /
  Barrett over `k` limbs at the `ZMod` value level) is the larger remaining piece.
  Its integer-product leg **is** proved — `FieldMul2x1GoldenPath.field_mul_2x1`
  reconstructs the exact `(a0 + a1·2^64)·b` from the emitted single-word
  `MUL`/`UMULH` primitives — but the modular reduce *of that product* is the heavy
  Montgomery-`CIOS` value correctness, not closed here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The multi-limb carrier and the injective encoding `encML2`

The carrier read-off is `bignumVal : List (BitVec 64) → ℕ` (little-endian). A
`ZMod p` element (for a prime `p` with `2p ≤ 2^128`) encodes to its canonical `val`
split into two 64-bit limbs `[lo, hi]`, `lo = val % 2^64`, `hi = val / 2^64`. This is
the multi-limb analogue of `encMod251` (`val` into one word). -/

/-- The two-limb little-endian split of a natural number `< 2^128`. -/
def splitLimbs2 (v : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 (v % 2 ^ 64), BitVec.ofNat 64 (v / 2 ^ 64)]

@[simp] theorem splitLimbs2_length (v : Nat) : (splitLimbs2 v).length = 2 := rfl

/-- **`splitLimbs2` round-trips through `bignumVal`** for `v < 2^128`. The two-limb
    carrier faithfully represents any `< 2^128` natural — the multi-limb analogue of
    `encMod251`'s `(BitVec.ofNat 64 a.val).toNat = a.val`. -/
theorem bignumVal_splitLimbs2 (v : Nat) (hv : v < 2 ^ 128) :
    bignumVal (splitLimbs2 v) = v := by
  simp only [splitLimbs2, bignumVal]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : v % 2 ^ 64 % 2 ^ 64 = v % 2 ^ 64 := Nat.mod_mod_of_dvd v (dvd_refl _)
  have h2 : v / 2 ^ 64 % 2 ^ 64 = v / 2 ^ 64 := by
    apply Nat.mod_eq_of_lt; apply Nat.div_lt_of_lt_mul; rw [← pow_add]; exact hv
  rw [h1, h2]; omega

/-- The injective multi-limb encoding `ZMod p → List (BitVec 64)`: the canonical
    representative `val`, split into two limbs. The multi-limb sibling of
    `encMod251`. -/
def encML2 (p : Nat) (a : ZMod p) : List (BitVec 64) := splitLimbs2 a.val

@[simp] theorem encML2_length (p : Nat) (a : ZMod p) : (encML2 p a).length = 2 := rfl

/-- **`encML2` reads back `val`** (for a 2-limb prime `p < 2^128`). -/
theorem bignumVal_encML2 (p : Nat) [NeZero p] (hp128 : p < 2 ^ 128) (a : ZMod p) :
    bignumVal (encML2 p a) = a.val :=
  bignumVal_splitLimbs2 a.val (lt_trans (ZMod.val_lt a) hp128)

/-- **`encML2` is injective** (equality-reflecting): distinct residues have distinct
    `val < 2^128`, hence distinct limb-vectors of distinct `bignumVal`. The
    `map4`-level `enc_inj` the transport needs — note `encML2` is **not** surjective
    (most limb-vectors are `≥ p` or `≥ 2^128`). -/
theorem encML2_injective (p : Nat) [NeZero p] (hp128 : p < 2 ^ 128) :
    Function.Injective (encML2 p) := by
  intro a b hab
  have ha := bignumVal_encML2 p hp128 a
  have hb := bignumVal_encML2 p hp128 b
  rw [hab, hb] at ha
  exact (ZMod.val_injective p) ha.symm

/-! ## 2. The multi-limb reducing kernel `mlAddMod` and its value correctness

`mlAddMod pl x y` is the multi-limb field add: the carry-extended add `addLimbs x y 0`
(`n+1` limbs), drop the top carry limb (`0` since the sum is `< 2^128` for `2p ≤
2^128`), then the conditional-subtract reduce `condSubLimbs · pl`. Its value
correctness reuses the three proved kernels (no new arithmetic). -/

/-- Multi-limb modular add: carry-extended `addLimbs`, drop the top carry limb, then
    the `condSubLimbs` modular reduce against the modulus limb-vector `pl`. -/
def mlAddMod (pl : List (BitVec 64)) (x y : List (BitVec 64)) : List (BitVec 64) :=
  condSubLimbs ((addLimbs x y 0).dropLast) pl

/-- **`mlAddMod` value correctness — the multi-limb modular reduce.** For 2-limb
    operands `x, y` below the 2-limb modulus `pl` (with `2·P ≤ 2^128`, so the sum
    does not exceed the 2-limb range), the emitted composite computes the residue
    `(bignumVal x + bignumVal y) % bignumVal pl`. This is the multi-limb analogue of
    the single-word `AddModKernel.addmodProg_toNat`; it **reuses** `addLimbs_val`
    (exact sum), `bignumVal_dropLast` (drop the zero carry), and `condSubLimbs_val`
    (the reduce) — the heavy multi-limb arithmetic is not reproved. -/
theorem mlAddMod_val (pl x y : List (BitVec 64))
    (hxl : x.length = 2) (hyl : y.length = 2) (hpl : pl.length = 2)
    (hP0 : 0 < bignumVal pl) (h2P : 2 * bignumVal pl ≤ (2 ^ 64) ^ 2)
    (hx : bignumVal x < bignumVal pl) (hy : bignumVal y < bignumVal pl) :
    bignumVal (mlAddMod pl x y) = (bignumVal x + bignumVal y) % bignumVal pl := by
  unfold mlAddMod
  have hlen3 : (addLimbs x y 0).length = 3 := by
    rw [addLimbs_length x y 0 (by omega)]; omega
  have hsumval : bignumVal (addLimbs x y 0) = bignumVal x + bignumVal y := by
    rw [addLimbs_val x y 0 (by decide) (by omega)]; simp
  have hsumlt : bignumVal x + bignumVal y < (2 ^ 64) ^ 2 := by omega
  have hdrop : bignumVal (addLimbs x y 0).dropLast = bignumVal x + bignumVal y := by
    rw [bignumVal_dropLast 2 _ (by omega), hsumval, Nat.mod_eq_of_lt hsumlt]
  have hdroplen : ((addLimbs x y 0).dropLast).length = 2 := by
    rw [List.length_dropLast, hlen3]
  rw [condSubLimbs_val _ pl (by rw [hdroplen, hpl]) (by rw [hdrop]; omega), hdrop]

/-! ## 3. The `EndoOpRealization` for `ZMod p` ADD over the multi-limb value carrier

The carrier is the represented value `ℕ` (read by `bignumVal`); `enc = ZMod.val`,
`bop x y = (x + y) % p`. The single-op commuting square is `ZMod.val_add`. This is
the multi-limb sibling of `addMod251Realization` — same `EndoOpRealization` shape,
carrier swapped from `BitVec 64` to the multi-limb value `ℕ`. The whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) is inherited for free. -/

/-- **The `EndoOpRealization` for `F_p` add via the canonical representative**, over
    the multi-limb value carrier `ℕ`. `op = (· + ·)` on `ZMod p`; `bop = fun x y =>
    (x + y) % p` on `ℕ`; `enc = ZMod.val` (injective, not onto). The commuting square
    is `ZMod.val_add`. The multi-limb sibling of `addMod251Realization`. -/
def addModRealization (p : Nat) [NeZero p] :
    EndoOpRealization (fun a b : ZMod p => a + b) (fun x y : Nat => (x + y) % p) where
  enc := ZMod.val
  enc_inj := ZMod.val_injective p
  commutes := fun a b => by rw [ZMod.val_add]

/-! ## 4. The IR seam: the emitted multi-limb kernel realizes `bop`

`addModRealization`'s `bop x y = (x + y) % p` is realized by the emitted `mlAddMod`
kernel read through `bignumVal`: running `mlAddMod` on the *encoded* operands and
reading `bignumVal` gives exactly `(a.val + b.val) % p`. This is the multi-limb IR
seam — the analogue of `RealizedKernel.com_denotes_bop`, with `bignumVal ∘ mlAddMod`
in place of `Com.denote`. -/

/-- A 2-limb prime `p` whose `bignumVal`-readable modulus limb-vector is `pl`, with
    `2p ≤ 2^128` (so two reduced operands sum within the 2-limb range). The data the
    multi-limb seam needs — the multi-limb analogue of the single-word `p < 2^63`
    side condition in `AddModKernel`. -/
structure TwoLimbPrime where
  /-- The prime modulus. -/
  p : Nat
  /-- `p` is nonzero (so `ZMod p` is a nontrivial residue ring). -/
  nz : NeZero p
  /-- The modulus as a 2-limb little-endian vector. -/
  pl : List (BitVec 64)
  /-- `pl` has exactly two limbs. -/
  pl_len : pl.length = 2
  /-- `pl` reads back to `p`. -/
  pl_val : bignumVal pl = p
  /-- `2p` fits in the 2-limb range (no overflow on the sum of two reduced operands). -/
  two_p_le : 2 * p ≤ (2 ^ 64) ^ 2

attribute [instance] TwoLimbPrime.nz

/-- `p < 2^128` follows from `2p ≤ 2^128` (and `p > 0`). -/
theorem TwoLimbPrime.p_lt (P : TwoLimbPrime) : P.p < 2 ^ 128 := by
  have h : ((2 : Nat) ^ 64) ^ 2 = 2 ^ 128 := by norm_num
  have hpos : 0 < P.p := Nat.pos_of_ne_zero (NeZero.ne P.p)
  have := P.two_p_le; rw [h] at this; omega

/-- **The multi-limb IR seam.** The emitted `mlAddMod` kernel, run on the encoded
    operands and read through `bignumVal`, computes the realization's `bop` value
    `(a.val + b.val) % p`. The multi-limb analogue of `RealizedKernel.com_denotes_bop`
    — `bignumVal ∘ mlAddMod` plays the role of `Com.denote`. Reuses `mlAddMod_val`
    and `bignumVal_encML2`. -/
theorem mlAdd_seam (P : TwoLimbPrime) (a b : ZMod P.p) :
    bignumVal (mlAddMod P.pl (encML2 P.p a) (encML2 P.p b)) = (a.val + b.val) % P.p := by
  have hp128 := P.p_lt
  have hva : a.val < P.p := ZMod.val_lt a
  have hvb : b.val < P.p := ZMod.val_lt b
  have hea : bignumVal (encML2 P.p a) = a.val := bignumVal_encML2 P.p hp128 a
  have heb : bignumVal (encML2 P.p b) = b.val := bignumVal_encML2 P.p hp128 b
  rw [mlAddMod_val P.pl (encML2 P.p a) (encML2 P.p b) (encML2_length _ _) (encML2_length _ _)
      P.pl_len (by rw [P.pl_val]; exact Nat.pos_of_ne_zero (NeZero.ne P.p))
      (by rw [P.pl_val]; exact P.two_p_le)
      (by rw [hea, P.pl_val]; exact hva) (by rw [heb, P.pl_val]; exact hvb)]
  rw [hea, heb, P.pl_val]

/-! ## 5. The MULTI-LIMB commuting square (the heart, the carrier-port capstone)

The abstract `ZMod p` field add `a + b`, serialized by `encML2`, equals the emitted
multi-limb kernel `mlAddMod` (run on the serialized operands) read through
`bignumVal`. The multi-limb analogue of `encMod251_commutes` — same square, carrier
swapped to the multi-limb value. Composes `addModRealization.commutes` (`ZMod.val_add`)
with the IR seam (`mlAdd_seam`). -/

/-- **The multi-limb `F_p` ADD commuting square — the `bls12_377` carrier port at
    2-limb scale.** The abstract field add `a + b` (in `F_p`), serialized by the
    injective-not-surjective multi-limb encoding `encML2`, equals the emitted
    multi-limb reducing kernel `mlAddMod` on the serialized operands, read through
    `bignumVal`. This is the multi-limb analogue of `encMod251_commutes` — the
    relational tie carried over a multi-limb prime carrier, **with the
    multi-limb modular reduce** (`condSubLimbs`). -/
theorem encML2_add_commutes (P : TwoLimbPrime) (a b : ZMod P.p) :
    (a + b).val = bignumVal (mlAddMod P.pl (encML2 P.p a) (encML2 P.p b)) := by
  rw [mlAdd_seam P, ZMod.val_add]

/-- **The multi-limb transfer demonstration.** An abstract `F_p` equation `a + b =
    a' + b'` transfers to an equation between the emitted multi-limb kernel's
    `bignumVal`-read value on the encoded operands — through the injective-not-onto
    `encML2`. The multi-limb analogue of `addMod251_spec_transfers`; the relational
    front deciding an abstract field equation through a real multi-limb serialization
    and a multi-limb modular reduce. -/
theorem mlAdd_spec_transfers (P : TwoLimbPrime) (a a' b b' : ZMod P.p) :
    a + b = a' + b' ↔
      bignumVal (mlAddMod P.pl (encML2 P.p a) (encML2 P.p b))
        = bignumVal (mlAddMod P.pl (encML2 P.p a') (encML2 P.p b')) := by
  rw [← encML2_add_commutes P, ← encML2_add_commutes P]
  exact ⟨fun h => by rw [h], fun h => (addModRealization P.p).enc_inj h⟩

/-! ## 6. A worked example: a concrete 2-limb prime, the op, the limb-vector result

A concrete `TwoLimbPrime` instance at the small prime `p = 2^61 - 1` (a Mersenne
prime, `< 2^63`, so `2p ≤ 2^128` holds with room): its limb-vector is `[2^61 - 1, 0]`
(it fits in the low limb), and we exhibit the multi-limb add of two concrete field
elements decided by the emitted reducing kernel through `mlAdd_spec_transfers`. -/

/-- The concrete worked-example prime `p = 2^61 - 1` (Mersenne `M_61`), as a
    `TwoLimbPrime`. Its modulus limb-vector is `[2^61 - 1, 0]` (the prime fits the low
    limb). All side conditions discharge by `decide`/`norm_num`. -/
def m61TwoLimbPrime : TwoLimbPrime where
  p := 2 ^ 61 - 1
  nz := ⟨by decide⟩
  pl := [BitVec.ofNat 64 (2 ^ 61 - 1), 0]
  pl_len := rfl
  pl_val := by decide
  two_p_le := by norm_num

/-- **Worked example: a wrapping multi-limb field add decided by the emitted kernel.**
    In `F_{2^61-1}`, with `x = 2^61 - 2` and `y = 3`, the sum `x + y = 2^61 + 1`
    reduces to `2` (it exceeds `p = 2^61 - 1` by `2`). The abstract field equation
    `(2^61 - 2) + 3 = 2 + 0` in `F_{2^61-1}` transfers to the emitted multi-limb
    `mlAddMod` kernel agreeing (through `bignumVal`) on the serialized operands — the
    wrapping case the conditional-subtract reduce must get right. Closed by `decide`
    on the abstract field side via `mlAdd_spec_transfers`. -/
example :
    bignumVal (mlAddMod m61TwoLimbPrime.pl
        (encML2 m61TwoLimbPrime.p (2 ^ 61 - 2)) (encML2 m61TwoLimbPrime.p 3))
      = bignumVal (mlAddMod m61TwoLimbPrime.pl
          (encML2 m61TwoLimbPrime.p 2) (encML2 m61TwoLimbPrime.p 0)) :=
  (mlAdd_spec_transfers m61TwoLimbPrime (2 ^ 61 - 2) 2 3 0).mp (by decide)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
