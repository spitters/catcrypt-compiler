/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public meta import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import Mathlib.Data.ZMod.Basic

/-!
# The `bls12_377` base-field ADD, realized relationally over a 6×64-bit carrier

`RelationalFrontMultiLimb` carries the relational EC realization over a multi-limb
carrier at **2-limb scale** (`encML2`/`splitLimbs2`/`mlAddModK`/`encML2_add_commutes`),
with a worked example at the Mersenne prime `M_61`. That module's own docstring flags
the remaining axis: the full `377`-bit (`k = 6`) prime — *the user's literal target
field* — as a `k`-bump of the already-`n`-limb proved kernels.

This module **closes that bump**. It generalizes the 2-limb pieces to **`k` limbs**
and instantiates them at the `bls12_377` base-field prime `q` (377-bit, 6×64-bit
limbs). The abstract `ZMod q` field addition `a + b`, serialized by the `k = 6` encoding
`encMLK`, equals the emitted 6-limb reducing kernel `mlAddModK` (run on the serialized
operands) read through `bignumVal` — **with the 6-limb modular reduce**
(`condSubLimbs`). This is the `bls12_377` base-field ADD realized relationally.

## What generalizes (the `k`-limb pieces) and what is reused

The proved multi-limb kernels in `MultiLimbKernel` are already stated for `n`-limb
lists — `addLimbs_val` (exact integer sum), `condSubLimbs_val` (the `V < 2P` modular
reduce), `bignumVal_dropLast` (drop the zero carry limb). Only the *encoding* and the
*commuting-square scaffolding* were pinned to `k = 2`. We generalize exactly those:

* `splitLimbsK k v` — the `k`-limb little-endian split of any `v : ℕ` (recursive, no
  `k`-specific arithmetic). `bignumVal_splitLimbsK` proves it reads back `v % (2^64)^k`
  *unconditionally* (the `k`-limb analogue of `bignumVal_splitLimbs2`, via
  `Nat.mod_mul`), and `bignumVal_splitLimbsK_of_lt` gives `= v` for `v < (2^64)^k`.
* `encMLK q k` — the injective `ZMod q → List (BitVec 64)` encoding (`val`, `k`-split).
* `mlAddModK_val k …` — the `k`-limb modular-add value correctness, **reusing**
  `addLimbs_val` + `bignumVal_dropLast` + `condSubLimbs_val` verbatim (no new
  arithmetic; the only change from the 2-limb proof is `2 ↦ k`, `(2^64)^2 ↦ (2^64)^k`).
* `KLimbPrime` — a `k`-limb prime with `2q ≤ (2^64)^k`; `encMLK_add_commutes` is the
  `k`-limb commuting square. The `EndoOpRealization` (`Bridges/ReprTransferExpr`) is
  carrier-parametric and **unchanged**; the whole-term abstraction theorem
  (`OpExpr.expr_eq_transfer`) is inherited for free.

## The `bls12_377` instance (scope)

* **Demonstrated (sorry-free):** the `k`-limb generalization above, and its instance at
  the real `bls12_377` base-field prime
  `q = 0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001`
  (377-bit; `bls377Q`, with its 6×64 little-endian limb vector `bls377Limbs`). All three
  side conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^6` by `norm_num`
  (pure-`Nat`, no `decide`); `bignumVal bls377Limbs = q` by `simp [bignumVal,
  BitVec.toNat_ofNat] + norm_num`. The commuting square `(a + b).val = bignumVal (mlAddModK
  bls377Limbs (encMLK q 6 a) (encMLK q 6 b))` holds for `a b : ZMod q` — the
  `bls12_377` field add through the emitted 6-limb kernel, *including the wrapping reduce*.
* **The prime source.** The repo's `Vale/BLS12_377.lean` declares the field leaves as
  *opaque axioms* (Montgomery-form `Fp377`), not as a `Nat` modulus, so they supply no
  `Nat` literal; `bls377Q` is defined here directly (the canonical Zexe/Aleo BLS12-377
  base-field prime, `u = 0x8508c00000000001`).
* **Deferred (unchanged from `RelationalFrontMultiLimb`):** the multi-limb **MUL**
  modular reduce — Montgomery/Barrett *of the product* at the `ZMod` value level. Its
  integer-product leg is proved (`mulBignum_val`), and a generic Barrett reduce is proved
  (`barrettReduce_val`); wiring `barrettReduce` into a `ZMod q` MUL commuting square at
  `k = 6` is the larger remaining piece for the full `bls12_377` EC. The **ADD** — the
  simplest op, the user's target — is realized here in full.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The `k`-limb split and the injective encoding `encMLK` -/

/-- The `k`-limb little-endian split of a natural number: peel one 64-bit limb at a
    time. The `k`-generalization of `splitLimbs2` (no `k`-specific arithmetic in the
    definition). -/
def splitLimbsK : Nat → Nat → List (BitVec 64)
  | 0,     _ => []
  | k + 1, v => BitVec.ofNat 64 (v % 2 ^ 64) :: splitLimbsK k (v / 2 ^ 64)

@[simp] theorem splitLimbsK_length (k v : Nat) : (splitLimbsK k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [splitLimbsK, ih]

/-- **`splitLimbsK` reads back `v % (2^64)^k`** — *unconditionally*. The `k`-limb
    analogue of `bignumVal_splitLimbs2`, proved by induction via `Nat.mod_mul`. -/
theorem bignumVal_splitLimbsK (k v : Nat) :
    bignumVal (splitLimbsK k v) = v % (2 ^ 64) ^ k := by
  induction k generalizing v with
  | zero => simp [splitLimbsK, bignumVal, Nat.mod_one]
  | succ k ih =>
    simp only [splitLimbsK, bignumVal, ih]
    rw [BitVec.toNat_ofNat]
    have hmm : v % 2 ^ 64 % 2 ^ 64 = v % 2 ^ 64 := Nat.mod_mod_of_dvd v (dvd_refl _)
    have hpow : ((2 : Nat) ^ 64) ^ (k + 1) = 2 ^ 64 * (2 ^ 64) ^ k := by rw [pow_succ']
    rw [hmm, hpow, Nat.mod_mul]

/-- **`splitLimbsK` round-trips through `bignumVal`** for `v < (2^64)^k`. -/
theorem bignumVal_splitLimbsK_of_lt (k v : Nat) (hv : v < (2 ^ 64) ^ k) :
    bignumVal (splitLimbsK k v) = v := by
  rw [bignumVal_splitLimbsK, Nat.mod_eq_of_lt hv]

/-- The injective `k`-limb encoding `ZMod q → List (BitVec 64)`: the canonical
    representative `val`, split into `k` limbs. The `k`-generalization of `encML2`. -/
def encMLK (q k : Nat) (a : ZMod q) : List (BitVec 64) := splitLimbsK k a.val

@[simp] theorem encMLK_length (q k : Nat) (a : ZMod q) : (encMLK q k a).length = k := by
  simp [encMLK]

/-- **`encMLK` reads back `val`** (for a `k`-limb prime `q < (2^64)^k`). -/
theorem bignumVal_encMLK (q k : Nat) [NeZero q] (hqk : q < (2 ^ 64) ^ k) (a : ZMod q) :
    bignumVal (encMLK q k a) = a.val :=
  bignumVal_splitLimbsK_of_lt k a.val (lt_trans (ZMod.val_lt a) hqk)

/-- **`encMLK` is injective**: distinct residues have distinct `val < (2^64)^k`, hence
    distinct limb-vectors of distinct `bignumVal`. Not surjective. -/
theorem encMLK_injective (q k : Nat) [NeZero q] (hqk : q < (2 ^ 64) ^ k) :
    Function.Injective (encMLK q k) := by
  intro a b hab
  have ha := bignumVal_encMLK q k hqk a
  have hb := bignumVal_encMLK q k hqk b
  rw [hab, hb] at ha
  exact (ZMod.val_injective q) ha.symm

/-! ## 2. The `k`-limb reducing kernel `mlAddModK` and its value correctness -/

/-- Multi-limb modular add: carry-extended `addLimbs`, drop the top carry limb, then
    the `condSubLimbs` modular reduce against the modulus limb-vector `pl`. Identical to
    the 2-limb `mlAddModK`; the kernel is already `n`-limb. -/
def mlAddModK (pl x y : List (BitVec 64)) : List (BitVec 64) :=
  condSubLimbs ((addLimbs x y 0).dropLast) pl

/-- **`mlAddModK` value correctness at `k` limbs — the multi-limb modular
    reduce.** For `k`-limb operands `x, y` below the `k`-limb modulus `pl` (with `2P ≤
    (2^64)^k`, so the sum stays in the `k`-limb range), the emitted composite computes
    `(bignumVal x + bignumVal y) % bignumVal pl`. The only change from `mlAddModK_val`
    (`k = 2`) is `2 ↦ k`; it **reuses** `addLimbs_val`, `bignumVal_dropLast`, and
    `condSubLimbs_val` — the heavy multi-limb arithmetic is not reproved. -/
theorem mlAddModK_val (k : Nat) (pl x y : List (BitVec 64))
    (hxl : x.length = k) (hyl : y.length = k) (hpl : pl.length = k)
    (h2P : 2 * bignumVal pl ≤ (2 ^ 64) ^ k)
    (hx : bignumVal x < bignumVal pl) (hy : bignumVal y < bignumVal pl) :
    bignumVal (mlAddModK pl x y) = (bignumVal x + bignumVal y) % bignumVal pl := by
  unfold mlAddModK
  have hxy : x.length = y.length := by rw [hxl, hyl]
  have hlenk1 : (addLimbs x y 0).length = k + 1 := by
    rw [addLimbs_length x y 0 hxy, hxl]
  have hsumval : bignumVal (addLimbs x y 0) = bignumVal x + bignumVal y := by
    rw [addLimbs_val x y 0 (by decide) hxy]; simp
  have hsumlt : bignumVal x + bignumVal y < (2 ^ 64) ^ k := by omega
  have hdrop : bignumVal (addLimbs x y 0).dropLast = bignumVal x + bignumVal y := by
    rw [bignumVal_dropLast k _ hlenk1, hsumval, Nat.mod_eq_of_lt hsumlt]
  have hdroplen : ((addLimbs x y 0).dropLast).length = k := by
    rw [List.length_dropLast, hlenk1]; omega
  rw [condSubLimbs_val _ pl (by rw [hdroplen, hpl]) (by rw [hdrop]; omega), hdrop]

/-! ## 3. The `EndoOpRealization` for `ZMod q` ADD over the multi-limb value carrier

Carrier = represented value `ℕ` (read by `bignumVal`); `enc = ZMod.val`,
`bop x y = (x + y) % q`. The single-op commuting square is `ZMod.val_add`. The
`EndoOpRealization` is carrier-parametric — identical to `addModRealization`, reused
here for the `k`-limb instance. -/

/-- **The `EndoOpRealization` for `F_q` add via the canonical representative**, over the
    multi-limb value carrier `ℕ`. `op = (· + ·)`; `bop = fun x y => (x + y) % q`;
    `enc = ZMod.val`. The commuting square is `ZMod.val_add`. -/
def addModRealizationK (q : Nat) [NeZero q] :
    EndoOpRealization (fun a b : ZMod q => a + b) (fun x y : Nat => (x + y) % q) where
  enc := ZMod.val
  enc_inj := ZMod.val_injective q
  commutes := fun a b => by rw [ZMod.val_add]

/-! ## 4. The `k`-limb prime datum and the IR seam -/

/-- A `k`-limb prime `q` whose `bignumVal`-readable modulus limb-vector is `ql`, with
    `2q ≤ (2^64)^k` (so two reduced operands sum within the `k`-limb range). The
    `k`-generalization of `TwoLimbPrime`. -/
structure KLimbPrime where
  /-- The number of 64-bit limbs. -/
  k : Nat
  /-- The prime modulus. -/
  q : Nat
  /-- `q` is nonzero (so `ZMod q` is a residue ring). -/
  nz : NeZero q
  /-- The modulus as a `k`-limb little-endian vector. -/
  ql : List (BitVec 64)
  /-- `ql` has exactly `k` limbs. -/
  ql_len : ql.length = k
  /-- `ql` reads back to `q`. -/
  ql_val : bignumVal ql = q
  /-- `2q` fits in the `k`-limb range (no overflow on the sum of two reduced operands). -/
  two_q_le : 2 * q ≤ (2 ^ 64) ^ k

attribute [instance] KLimbPrime.nz

/-- `q < (2^64)^k` follows from `2q ≤ (2^64)^k` (and `q > 0`). -/
theorem KLimbPrime.q_lt (Q : KLimbPrime) : Q.q < (2 ^ 64) ^ Q.k := by
  have hpos : 0 < Q.q := Nat.pos_of_ne_zero (NeZero.ne Q.q)
  have := Q.two_q_le; omega

/-- **The multi-limb IR seam at `k` limbs.** The emitted `mlAddModK` kernel, run on the
    encoded operands and read through `bignumVal`, computes the realization's `bop`
    value `(a.val + b.val) % q`. Reuses `mlAddModK_val` and `bignumVal_encMLK`. -/
theorem mlAdd_seamK (Q : KLimbPrime) (a b : ZMod Q.q) :
    bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) = (a.val + b.val) % Q.q := by
  have hqk := Q.q_lt
  have hva : a.val < Q.q := ZMod.val_lt a
  have hvb : b.val < Q.q := ZMod.val_lt b
  have hea : bignumVal (encMLK Q.q Q.k a) = a.val := bignumVal_encMLK Q.q Q.k hqk a
  have heb : bignumVal (encMLK Q.q Q.k b) = b.val := bignumVal_encMLK Q.q Q.k hqk b
  rw [mlAddModK_val Q.k Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)
      (encMLK_length _ _ _) (encMLK_length _ _ _) Q.ql_len
      (by rw [Q.ql_val]; exact Q.two_q_le)
      (by rw [hea, Q.ql_val]; exact hva) (by rw [heb, Q.ql_val]; exact hvb)]
  rw [hea, heb, Q.ql_val]

/-! ## 5. The `k`-limb commuting square (the carrier-port capstone) -/

/-- **The `k`-limb `F_q` ADD commuting square.** The abstract field add `a + b` (in
    `F_q`), serialized by the injective-not-surjective `k`-limb encoding `encMLK`,
    equals the emitted multi-limb reducing kernel `mlAddModK` on the serialized operands,
    read through `bignumVal` — **with the multi-limb modular reduce**. The
    `k`-generalization of `encML2_add_commutes`. -/
theorem encMLK_add_commutes (Q : KLimbPrime) (a b : ZMod Q.q) :
    (a + b).val = bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) := by
  rw [mlAdd_seamK Q, ZMod.val_add]

/-- **The `k`-limb transfer demonstration.** An abstract `F_q` equation `a + b = a' + b'`
    transfers to an equation between the emitted multi-limb kernel's `bignumVal`-read
    value — through the injective-not-onto `encMLK`. The `k`-generalization of
    `mlAdd_spec_transfers`. -/
theorem mlAddK_spec_transfers (Q : KLimbPrime) (a a' b b' : ZMod Q.q) :
    a + b = a' + b' ↔
      bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b))
        = bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a') (encMLK Q.q Q.k b')) := by
  rw [← encMLK_add_commutes Q, ← encMLK_add_commutes Q]
  exact ⟨fun h => by rw [h], fun h => (addModRealizationK Q.q).enc_inj h⟩

/-! ## 6. The `bls12_377` instance: the 377-bit base-field prime, `k = 6`

The Zexe / SnarkVM / Aleo BLS12-377 base-field prime (`u = 0x8508c00000000001`,
377-bit). The repo's `Vale/BLS12_377.lean` declares the field leaves as opaque
Montgomery-form axioms (`Fp377`), not a `Nat` modulus, so `bls377Q` is defined here. -/

/-- The `bls12_377` base-field prime `q` (377-bit). -/
def bls377Q : Nat :=
  0x01ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001

/-- The `bls12_377` base-field prime as a 6×64-bit little-endian limb vector
    (`limb0` = low). Matches the `bench/bls12_377_compare` Montgomery-form modulus
    constant `q = Σ bls377Limbsᵢ · 2^(64·i)`. -/
def bls377Limbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0x8508c00000000001,
    BitVec.ofNat 64 0x170b5d4430000000,
    BitVec.ofNat 64 0x1ef3622fba094800,
    BitVec.ofNat 64 0x1a22d9f300f5138f,
    BitVec.ofNat 64 0xc63b05c06ca1493b,
    BitVec.ofNat 64 0x01ae3a4617c510ea ]

/-- `bls377Limbs` reads back to `bls377Q` — the 6-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). -/
theorem bignumVal_bls377Limbs : bignumVal bls377Limbs = bls377Q := by
  simp only [bls377Limbs, bls377Q, bignumVal, BitVec.toNat_ofNat]; norm_num

/-- **The `bls12_377` base-field prime as a `KLimbPrime` (`k = 6`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^6` by `norm_num`
    (pure-`Nat`); `bignumVal bls377Limbs = q` by `bignumVal_bls377Limbs`. -/
def bls377KLimbPrime : KLimbPrime where
  k        := 6
  q        := bls377Q
  nz       := ⟨by unfold bls377Q; norm_num⟩
  ql       := bls377Limbs
  ql_len   := rfl
  ql_val   := bignumVal_bls377Limbs
  two_q_le := by unfold bls377Q; norm_num

/-- **The `bls12_377` base-field ADD commuting square — the user's target field.** The
    abstract `bls12_377` base-field addition `a + b` (in `ZMod q` for the 377-bit
    prime `q`), serialized by the 6-limb encoding `encMLK q 6`, equals the emitted 6×64-bit
    reducing kernel `mlAddModK` on the serialized operands, read through `bignumVal` — with
    the 6-limb conditional-subtract modular reduce. -/
theorem bls377_add_commutes (a b : ZMod bls377Q) :
    (a + b).val
      = bignumVal (mlAddModK bls377Limbs (encMLK bls377Q 6 a) (encMLK bls377Q 6 b)) :=
  encMLK_add_commutes bls377KLimbPrime a b

/-! ## 7. A worked example: a `bls12_377` base-field add whose sum WRAPS

Two `bls12_377` base-field elements whose abstract sum exceeds `q` — so the 6-limb
conditional-subtract reduce *fires*. Take `a = q - 1` (the maximal residue) and `b = 5`:
in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the emitted kernel must reduce. We
exhibit the abstract field equation `(q - 1) + 5 = 4 + 0` transferring (through
`mlAddK_spec_transfers`) to the emitted 6-limb kernel agreeing on the serialized
operands. The abstract `ZMod q` equation closes by `decide` on the residues; the kernel
side is the wrapping reduce over `bls377Limbs`. -/

/-- **Worked wrapping example.** In the `bls12_377` base field, `(q - 1) + 5` wraps to
    `4` (the maximal residue plus `5` exceeds `q` by `4`). The abstract field equation
    `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the emitted 6-limb `mlAddModK` kernel
    agreeing (through `bignumVal`) on the serialized operands — the wrapping case the
    6-limb conditional-subtract reduce must get right. (`-1 = q - 1` is the maximal
    residue; `(-1) + 5 = 4` and `4 + 0 = 4` hold definitionally in `ZMod q`.) -/
theorem bls377_add_wrap_example :
    bignumVal (mlAddModK bls377Limbs
        (encMLK bls377Q 6 (-1)) (encMLK bls377Q 6 5))
      = bignumVal (mlAddModK bls377Limbs
          (encMLK bls377Q 6 4) (encMLK bls377Q 6 0)) :=
  (mlAddK_spec_transfers bls377KLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod bls377Q) + 5 = 4; ring_nf)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
