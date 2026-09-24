/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import Mathlib.Data.ZMod.Basic

/-!
# The `bls12_377` base-field SUBTRACTION, realized relationally over a 6×64-bit carrier

`RelationalFrontBls377Add` realizes the `bls12_377` base-field **ADD** relationally
(`encMLK_add_commutes` / `bls377_add_commutes`), and `RelationalFrontBls377Mul` the
**MUL**. This module closes the third field op — the **modular SUBTRACT** — completing
the `+`/`−`/`·` set over the 6-limb carrier needed for the inversion-free EC group law
(Jacobian add/double are straight-line `+`/`−`/`·`).

## The borrow-corrected subtract `(a + (p − b)) mod p`

`x − y` modulo a prime `p` (for `x, y < p`) is computed as the **borrow-corrected add**:
form `p − y` over limbs (the conditional-add-back the modulus performs), then add it to
`x` and reduce. Concretely, with `x, y < p`:

* `p − y ∈ (0, p]` (a `k`-limb value, since `y < p`), so `x + (p − y) < 2p`;
* a single `condSubLimbs` reduce against `p` therefore finishes, exactly as in
  `mlAddModK`. The result is `(x + (p − y)) mod p`, which **equals** `(x − y) mod p`
  in `ℤ/p` (`p − y ≡ −y`).

This reuses the verified `MultiLimbKernel` primitives verbatim: `subLimbs` (two's-complement
`p − y`, its top limb the not-borrow flag), `addLimbs` (the carry chain), and `condSubLimbs`
(the `V < 2p` modular reduce). No new multi-limb arithmetic is introduced — the only new
pieces are the composite `mlSubModK` and its value law, plus the `ZMod`-side bridge
`(a − b).val = (a.val + (q − b.val)) % q`.

## What is reused from `RelationalFrontBls377Add`

`bls377Q`, `bls377Limbs`, `bignumVal_bls377Limbs`, `KLimbPrime`, `bls377KLimbPrime`,
`encMLK`, `splitLimbsK`, `bignumVal_encMLK` are all reused. The `bls12_377` instance is
the same `KLimbPrime`; only the kernel (`mlSubModK`) and its commuting square are new.

## Scope

* **Demonstrated (fully proved):** the generic `k`-limb `mlSubModK` and its value law
  `mlSubModK_val` (composing `subLimbs_val` + `addLimbs_val` + `condSubLimbs_val`); the
  `ZMod q` bridge `ZMod.val_sub_borrow`; the SUB commuting square `encMLK_sub_commutes`;
  the `bls12_377` instance `bls377_sub_commutes` at the 377-bit prime; a
  `subModRealizationK` / `EndoOpRealization` for the field sub; and a worked wrapping
  example (a difference that borrows, so the conditional add-back fires).
* With **ADD** + **MUL** + **SUB** all realized over the 6-limb carrier, the `bls12_377`
  base-field op set is complete for the inversion-free EC group law.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The `ZMod`-side bridge: `(a − b).val` as a borrow-corrected add residue -/

/-- **The `ZMod q` subtract as a borrow-corrected add residue.** Unconditionally (no
    `b.val ≤ a.val` hypothesis, unlike `ZMod.val_sub`), the canonical representative of
    `a - b` is `(a.val + (q - b.val)) % q` — the value the limb kernel computes by adding
    the modulus complement `p − b` and reducing. Derived from `ZMod.val_add` (on
    `a - b = a + (-b)`) and `ZMod.neg_val`, splitting on whether `b = 0`. -/
theorem ZMod.val_sub_borrow {q : Nat} [NeZero q] (a b : ZMod q) :
    (a - b).val = (a.val + (q - b.val)) % q := by
  have hsub : a - b = a + (-b) := sub_eq_add_neg a b
  rw [hsub, ZMod.val_add]
  by_cases hb : b = 0
  · subst hb
    have ha : a.val < q := ZMod.val_lt a
    simp only [ZMod.neg_val, ZMod.val_zero, Nat.sub_zero, Nat.add_zero,
      Nat.mod_eq_of_lt ha, Nat.add_mod_right, if_true]
  · rw [ZMod.neg_val, if_neg hb]

/-! ## 2. The `k`-limb modular subtract kernel `mlSubModK` and its value law -/

/-- **Multi-limb modular subtract.** Compute the modulus complement `p − y` over limbs
    (`subLimbs pl y`, drop its not-borrow top limb), add it to `x` (carry-extended
    `addLimbs`, drop the top carry limb), then the `condSubLimbs` modular reduce against
    the modulus `pl`. The SUB analogue of `mlAddModK` (`x + y` ↦ `x + (p − y)`). -/
def mlSubModK (pl x y : List (BitVec 64)) : List (BitVec 64) :=
  condSubLimbs ((addLimbs x ((subLimbs pl y).dropLast) 0).dropLast) pl

/-- **`mlSubModK` value law at `k` limbs.** For `k`-limb operands `x, y` strictly below
    the `k`-limb modulus `pl` (with `2P ≤ (2^64)^k`), the emitted composite computes
    `(bignumVal x + (bignumVal pl − bignumVal y)) % bignumVal pl` — the borrow-corrected
    modular subtraction. Reuses `subLimbs_val`, `addLimbs_val`, `bignumVal_dropLast`, and
    `condSubLimbs_val`. -/
theorem mlSubModK_val (k : Nat) (pl x y : List (BitVec 64))
    (hxl : x.length = k) (hyl : y.length = k) (hpl : pl.length = k)
    (h2P : 2 * bignumVal pl ≤ (2 ^ 64) ^ k)
    (hx : bignumVal x < bignumVal pl) (hy : bignumVal y < bignumVal pl) :
    bignumVal (mlSubModK pl x y)
      = (bignumVal x + (bignumVal pl - bignumVal y)) % bignumVal pl := by
  unfold mlSubModK
  -- the modulus complement c = p - y, length k, value P - V_y
  have hcomp_len : (subLimbs pl y).length = k + 1 := by
    rw [subLimbs, addLimbs_length pl (notLimbs y) 1 (by simp [notLimbs, hpl, hyl]), hpl]
  have hcomp_val : bignumVal (subLimbs pl y) + bignumVal y
      = bignumVal pl + (2 ^ 64) ^ k := by
    have h := subLimbs_val pl y (by rw [hpl, hyl])
    rwa [hpl] at h
  set c := (subLimbs pl y).dropLast with hc
  have hclen : c.length = k := by rw [hc, List.length_dropLast, hcomp_len]; omega
  have hcval : bignumVal c = bignumVal pl - bignumVal y := by
    rw [hc, bignumVal_dropLast k _ hcomp_len]
    -- bignumVal (subLimbs pl y) = P - V_y + (2^64)^k, so mod (2^64)^k gives P - V_y
    have hsv : bignumVal (subLimbs pl y) = bignumVal pl - bignumVal y + (2 ^ 64) ^ k := by
      omega
    rw [hsv, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- now add x + c, drop carry limb, reduce
  set Pmy := bignumVal pl - bignumVal y with hPmy
  have hxy : x.length = c.length := by rw [hxl, hclen]
  have hlenk1 : (addLimbs x c 0).length = k + 1 := by
    rw [addLimbs_length x c 0 (by rw [hxl, hclen]), hxl]
  have hsumval : bignumVal (addLimbs x c 0) = bignumVal x + Pmy := by
    rw [addLimbs_val x c 0 (by decide) hxy, hcval]; simp
  have hsumlt : bignumVal x + Pmy < (2 ^ 64) ^ k := by
    have : Pmy ≤ bignumVal pl := by rw [hPmy]; omega
    omega
  have hdrop : bignumVal (addLimbs x c 0).dropLast = bignumVal x + Pmy := by
    rw [bignumVal_dropLast k _ hlenk1, hsumval, Nat.mod_eq_of_lt hsumlt]
  have hdroplen : ((addLimbs x c 0).dropLast).length = k := by
    rw [List.length_dropLast, hlenk1]; omega
  rw [condSubLimbs_val _ pl (by rw [hdroplen, hpl]) (by rw [hdrop]; omega), hdrop]

/-! ## 3. The `EndoOpRealization` for `ZMod q` SUB over the multi-limb value carrier

Carrier = represented value `ℕ` (read by `bignumVal`); `enc = ZMod.val`,
`bop x y = (x + (q − y)) % q`. The single-op commuting square is `ZMod.val_sub_borrow`.
The SUB sibling of `addModRealizationK` / `mulModRealizationK`. -/

/-- **The `EndoOpRealization` for `F_q` SUB via the canonical representative**, over the
    multi-limb value carrier `ℕ`. `op = (· - ·)`; `bop = fun x y => (x + (q - y)) % q`;
    `enc = ZMod.val`. The commuting square is `ZMod.val_sub_borrow`. -/
def subModRealizationK (q : Nat) [NeZero q] :
    EndoOpRealization (fun a b : ZMod q => a - b) (fun x y : Nat => (x + (q - y)) % q) where
  enc := ZMod.val
  enc_inj := ZMod.val_injective q
  commutes := fun a b => by rw [ZMod.val_sub_borrow]

/-! ## 4. The `k`-limb SUB IR seam and commuting square -/

/-- **The multi-limb SUB IR seam at `k` limbs.** The emitted `mlSubModK` kernel, run on
    the encoded operands and read through `bignumVal`, computes the realization's `bop`
    value `(a.val + (q − b.val)) % q`. Reuses `mlSubModK_val` and `bignumVal_encMLK`. -/
theorem mlSub_seamK (Q : KLimbPrime) (a b : ZMod Q.q) :
    bignumVal (mlSubModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b))
      = (a.val + (Q.q - b.val)) % Q.q := by
  have hqk := Q.q_lt
  have hva : a.val < Q.q := ZMod.val_lt a
  have hvb : b.val < Q.q := ZMod.val_lt b
  have hea : bignumVal (encMLK Q.q Q.k a) = a.val := bignumVal_encMLK Q.q Q.k hqk a
  have heb : bignumVal (encMLK Q.q Q.k b) = b.val := bignumVal_encMLK Q.q Q.k hqk b
  rw [mlSubModK_val Q.k Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)
      (encMLK_length _ _ _) (encMLK_length _ _ _) Q.ql_len
      (by rw [Q.ql_val]; exact Q.two_q_le)
      (by rw [hea, Q.ql_val]; exact hva) (by rw [heb, Q.ql_val]; exact hvb)]
  rw [hea, heb, Q.ql_val]

/-- **The `k`-limb `F_q` SUB commuting square.** The abstract field subtract `a - b` (in
    `F_q`), serialized by the injective-not-surjective `k`-limb encoding `encMLK`, equals
    the emitted multi-limb borrow-corrected kernel `mlSubModK` on the serialized operands,
    read through `bignumVal` — with the multi-limb conditional add-back and reduce.
    The SUB sibling of `encMLK_add_commutes`. -/
theorem encMLK_sub_commutes (Q : KLimbPrime) (a b : ZMod Q.q) :
    (a - b).val = bignumVal (mlSubModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) := by
  rw [mlSub_seamK Q, ZMod.val_sub_borrow]

/-- **The `k`-limb SUB transfer demonstration.** An abstract `F_q` equation `a - b = a' - b'`
    transfers to an equation between the emitted multi-limb kernel's `bignumVal`-read value
    — through the injective-not-onto `encMLK`. The SUB sibling of `mlAddK_spec_transfers`. -/
theorem mlSubK_spec_transfers (Q : KLimbPrime) (a a' b b' : ZMod Q.q) :
    a - b = a' - b' ↔
      bignumVal (mlSubModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b))
        = bignumVal (mlSubModK Q.ql (encMLK Q.q Q.k a') (encMLK Q.q Q.k b')) := by
  rw [← encMLK_sub_commutes Q, ← encMLK_sub_commutes Q]
  exact ⟨fun h => by rw [h], fun h => (subModRealizationK Q.q).enc_inj h⟩

/-! ## 5. The `bls12_377` instance: the 377-bit base-field prime, `k = 6`

Reuses `bls377KLimbPrime` from `RelationalFrontBls377Add` verbatim; only the kernel
(`mlSubModK`) and its commuting square are new for the SUB op. -/

/-- **The `bls12_377` base-field SUBTRACT commuting square — the user's target field.**
    The abstract `bls12_377` base-field subtraction `a - b` (in `ZMod q` for the
    377-bit prime `q = bls377Q`), serialized by the 6-limb encoding `encMLK q 6`, equals
    the emitted 6×64-bit borrow-corrected kernel `mlSubModK` on the serialized operands,
    read through `bignumVal` — with the 6-limb conditional add-back / reduce. The
    SUB sibling of `bls377_add_commutes`, completing the `bls12_377` field-op set. -/
theorem bls377_sub_commutes (a b : ZMod bls377Q) :
    (a - b).val
      = bignumVal (mlSubModK bls377Limbs (encMLK bls377Q 6 a) (encMLK bls377Q 6 b)) :=
  encMLK_sub_commutes bls377KLimbPrime a b

/-! ## 6. A worked example: a `bls12_377` base-field subtract that BORROWS

Two `bls12_377` base-field elements whose abstract difference borrows — `a < b`, so the
result wraps and the modulus add-back fires. Take `a = 0` and `b = 1`: in `ZMod q`,
`0 - 1 = -1 = q - 1`, which the kernel computes by adding `p - 1` to `0`. We exhibit the
abstract field equation `0 - 1 = (q-1) - 0` transferring (through `mlSubK_spec_transfers`)
to the emitted kernel agreeing on the serialized operands. -/

/-- **Worked borrowing example.** In the `bls12_377` base field, `0 - 1` borrows to
    `-1 = q - 1` (the maximal residue). The abstract field equation `0 - 1 = (-1) - 0` in
    `ZMod q` transfers to the emitted 6-limb `mlSubModK` kernel agreeing (through
    `bignumVal`) on the serialized operands — the borrowing case the conditional add-back
    must get right. (`-1 = q - 1` is the maximal residue; `0 - 1 = -1` and `(-1) - 0 = -1`
    hold definitionally in `ZMod q`.) -/
theorem bls377_sub_borrow_example :
    bignumVal (mlSubModK bls377Limbs
        (encMLK bls377Q 6 0) (encMLK bls377Q 6 1))
      = bignumVal (mlSubModK bls377Limbs
          (encMLK bls377Q 6 (-1)) (encMLK bls377Q 6 0)) :=
  (mlSubK_spec_transfers bls377KLimbPrime 0 (-1) 1 0).mp
    (by show (0 : ZMod bls377Q) - 1 = (-1) - 0; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
