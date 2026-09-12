/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Mul
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontEC
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# `bls12_377` base-field INVERSION via Fermat — the last field-op building block

`RelationalFrontBls377Add`/`RelationalFrontBls377Mul` realize the `bls12_377`
base-field **ADD** and **MUL** relationally over the 6×64-bit limb carrier: the
abstract `ZMod bls377Q` operation, serialized by `encMLK bls377Q 6` and read
through `bignumVal`, equals the emitted reducing kernel (`mlAddModK` /
`mlMulMod`). The `bls12_377` field-op set is complete for the inversion-free EC
group law except for **inversion** — the one operation the affine slope
`λ = num · denom⁻¹` needs that is a division.

This module realizes `bls12_377` base-field inversion **relationally via
Fermat's little theorem**: in a prime field `a⁻¹ = a^{q-2}` for `a ≠ 0`, and
`a^{q-2}` is a **square-and-multiply modular-exponentiation schedule** built from
the already-landed single-op MUL — a straight-line composition of `mlMulMod`, so
no division instruction is emitted.

The `bls12_377` base-field prime `q = bls377Q` is a 377-bit prime, so the
exponent `q - 2` is 377-bit and the GF(251) template's `ring`-closed 8-step
chain (`RelationalFrontECInv`, exponent `249`) does not port: `ring` cannot
expand `a^{q-2}`. The schedule here is stated **once, parametrically in the
exponent**, as the binary square-and-multiply function `powModSpec`, whose
correctness `powModSpec_val` is proved by strong induction on the exponent using
the single-op commuting square `ZMod.val_mul` at each node — the exponent is
never reduced, and the proof cost is independent of its 377-bit size.

The carrier is the **value carrier** `ℕ` (`enc = ZMod.val`, read from the limb
vector by `bignumVal`), matching `bls377_mul_commutes`
(`(a * b).val = bignumVal (mlMulMod …)`); each `(x * y) % q` node of `powModSpec`
is exactly the emitted MUL kernel's value (`bls377_inv_node_is_mlMulMod`, from
`mlMul_seamK`).

Primality of the 377-bit prime is a section hypothesis `[Fact (Nat.Prime
bls377Q)]` — the same convention as the rest of the `bls12_377` tower
(`RelationalFrontBls377Fp2Inv`, `…Fp6Inv`, `…Fp12Inv`), since 377-bit primality
does not go through `norm_num`.

## Main results

* `powModSpec` / `powModSpec_val` — binary square-and-multiply modular
  exponentiation on the value carrier `ℕ`, and its correctness
  `powModSpec q a.val e = (a ^ e).val` for any exponent `e`, proved parametrically
  by strong induction (no reduction of the literal exponent).
* `invFermatGen` — the Fermat identity `a^{q-2} = a⁻¹` for `a ≠ 0` in any prime
  field `ZMod q`.
* `powBls377Spec` — the `bls12_377` inverse schedule `powModSpec bls377Q x
  (bls377Q - 2)`.
* `bls377_pow_commutes` — `(a^{q-2}).val = powBls377Spec a.val`.
* `bls377_inv_commutes` — the deliverable: `(a⁻¹).val = powBls377Spec a.val` for
  `a ≠ 0`, the `bls12_377` inverse realized as the emitted square-and-multiply
  chain on the serialized coordinate, with no division instruction.
* `bls377_inv_node_is_mlMulMod` — each schedule node `(x * y) % q` is the emitted
  `mlMulMod` kernel's `bignumVal`.
* `bls377_inv_spec_transfers` — an abstract `F_q` inverse equation transfers to
  the emitted schedule through the injective `ZMod.val`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The parametric square-and-multiply schedule and its correctness

`powModSpec q base e` computes `base^e mod q` by binary square-and-multiply.
Its correctness `powModSpec q a.val e = (a^e).val` is proved by strong induction
on `e`, using `ZMod.val_mul` (`(x·y).val = x.val · y.val % q`) at each squaring
and each conditional multiply. The exponent is a parameter; nothing reduces it,
so the proof cost is independent of the 377-bit size of `bls377Q - 2`. -/

/-- **Binary square-and-multiply modular exponentiation** on the value carrier
    `ℕ`: `powModSpec q base e = base ^ e % q`. The `e/2` recursion is the standard
    square (`(h·h) % q`) and conditional multiply (`(· · base) % q` when the low
    bit is set); each node is one modular multiply, whose value is the emitted
    MUL kernel `mlMulMod`. -/
def powModSpec (q base : Nat) : Nat → Nat
  | 0 => 1 % q
  | (e + 1) =>
    let m := (e + 1) / 2
    let h := powModSpec q base m
    let h2 := (h * h) % q
    if (e + 1) % 2 = 1 then (h2 * base) % q else h2
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos e) (by decide)

/-- **`powModSpec` correctness.** For any exponent `e`, the binary
    square-and-multiply schedule on the serialized value `a.val` computes
    `(a ^ e).val`. Proved by strong induction on `e`: the square node folds by
    `ZMod.val_mul` + `pow_add`, the multiply node adds one to the exponent by
    `pow_succ`; the exponent bookkeeping is discharged by `omega` on `e/2` and
    `e % 2`. Parametric in `e` — the 377-bit exponent is never reduced. -/
theorem powModSpec_val {q : Nat} [NeZero q] (hq : 1 < q) (a : ZMod q) :
    ∀ e : Nat, powModSpec q a.val e = (a ^ e).val := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    match e with
    | 0 => simp [powModSpec, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hq]
    | (e + 1) =>
      have hm : (e + 1) / 2 < e + 1 := Nat.div_lt_self (Nat.succ_pos e) (by decide)
      have key : powModSpec q a.val ((e + 1) / 2) = (a ^ ((e + 1) / 2)).val := ih _ hm
      unfold powModSpec
      by_cases hbit : (e + 1) % 2 = 1
      · rw [if_pos hbit, key, ← ZMod.val_mul, ← ZMod.val_mul]
        congr 1
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      · rw [if_neg hbit, key, ← ZMod.val_mul]
        congr 1
        rw [← pow_add]
        congr 1
        omega

/-! ## 2. The Fermat identity — the relational meaning of `⁻¹`

In a prime field `a⁻¹ = a^{q-2}`: `ZMod.pow_card_sub_one_eq_one` gives
`a^{q-1} = 1`, so `a^{q-2} · a = a^{q-1} = 1`, and `a⁻¹ = a^{q-2}` by uniqueness
of the field inverse. -/

/-- **The Fermat identity for a prime field.** For `a ≠ 0` in `ZMod q` with `q`
    prime, `a^{q-2} = a⁻¹`. Via `ZMod.pow_card_sub_one_eq_one` (`a^{q-1} = 1`) and
    `ZMod.inv_eq_of_mul_eq_one`. This is the relational meaning of the inverse:
    the value the square-and-multiply chain `powModSpec … (q-2)` computes *is* the
    field inverse. -/
theorem invFermatGen {q : Nat} [Fact (Nat.Prime q)] (a : ZMod q) (ha : a ≠ 0) :
    a ^ (q - 2) = a⁻¹ := by
  have hqq : 2 ≤ q := (Fact.out (p := Nat.Prime q)).two_le
  have h : a ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hmul : a ^ (q - 2) * a = 1 := by
    rw [← pow_succ]
    have hqe : q - 2 + 1 = q - 1 := by omega
    rw [hqe]; exact h
  exact (ZMod.inv_eq_of_mul_eq_one q a (a ^ (q - 2)) (by rw [mul_comm]; exact hmul)).symm

/-! ## 3. The `bls12_377` inverse schedule and commuting square

`powBls377Spec` instantiates `powModSpec` at the 377-bit prime and the
exponent `bls377Q - 2`. `bls377_pow_commutes` is `powModSpec_val` specialized;
`bls377_inv_commutes` combines it with `invFermatGen` — the `bls12_377` inverse
realized as the emitted square-and-multiply chain on the serialized coordinate. -/

section Bls377
variable [Fact (Nat.Prime bls377Q)]

/-- The `bls12_377` base-field inverse schedule: `bls377Q`-modular
    square-and-multiply raising the serialized coordinate to `bls377Q - 2`
    (`= a⁻¹` by Fermat). A straight-line composition of the emitted MUL kernel's
    value; no division instruction. -/
def powBls377Spec (x : Nat) : Nat := powModSpec bls377Q x (bls377Q - 2)

/-- **The `bls12_377` power-chain commuting square.** The abstract field power
    `a^{q-2}` (in `ZMod bls377Q`), serialized by `ZMod.val`, equals the emitted
    square-and-multiply schedule `powBls377Spec` on the serialized coordinate.
    `powModSpec_val` specialized to the exponent `bls377Q - 2` — proved without
    reducing the 377-bit exponent. -/
theorem bls377_pow_commutes (a : ZMod bls377Q) :
    (a ^ (bls377Q - 2)).val = powBls377Spec a.val :=
  (powModSpec_val (Fact.out (p := Nat.Prime bls377Q)).one_lt a (bls377Q - 2)).symm

/-- **The `bls12_377` inverse commuting square — the deliverable.** For `a ≠ 0`,
    the abstract base-field inverse `a⁻¹` (in `ZMod bls377Q`), serialized by
    `ZMod.val`, equals the emitted square-and-multiply schedule `powBls377Spec` on
    the serialized coordinate. The inverse is realized **without any division
    instruction** — it is the Fermat power chain `a^{q-2}`. Combines
    `invFermatGen` (`a⁻¹ = a^{q-2}`) and `bls377_pow_commutes` (the chain). The
    `bls12_377` sibling of `invMod251_commutes`. -/
theorem bls377_inv_commutes (a : ZMod bls377Q) (ha : a ≠ 0) :
    (a⁻¹).val = powBls377Spec a.val := by
  rw [← invFermatGen a ha]
  exact bls377_pow_commutes a

set_option linter.unusedSectionVars false in
/-- **Each schedule node is the emitted MUL kernel.** The value-carrier multiply
    `(a.val * b.val) % bls377Q` — the single-op node of `powBls377Spec` — equals
    `bignumVal` of the emitted 12-limb Barrett-reducing kernel `mlMulMod` on the
    serialized operands. The `mlMul_seamK` seam, tying the abstract chain to the
    landed `bls12_377` MUL, so the schedule is a composition of the emitted MUL. -/
theorem bls377_inv_node_is_mlMulMod (a b : ZMod bls377Q) :
    (a.val * b.val) % bls377Q
      = bignumVal (mlMulMod 6 bls377MuLimbs bls377Limbs
          (encMLK bls377Q 6 a) (encMLK bls377Q 6 b)) :=
  (mlMul_seamK bls377KLimbPrimeMul a b).symm

/-- **The inverse transfer.** An abstract `bls12_377` base-field inverse equation
    `a⁻¹ = b⁻¹` (for nonzero `a, b`) is decided by the emitted square-and-multiply
    schedule on the serialized coordinates, through the injective `ZMod.val`. The
    inverse sibling of `mlMulK_spec_transfers`. -/
theorem bls377_inv_spec_transfers (a b : ZMod bls377Q) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ = b⁻¹ ↔ powBls377Spec a.val = powBls377Spec b.val := by
  rw [← bls377_inv_commutes a ha, ← bls377_inv_commutes b hb]
  exact ⟨fun h => by rw [h], fun h => ZMod.val_injective bls377Q h⟩

/-- **The `EndoUnaryRealization` for the `bls12_377` inverse power chain.** The op
    realized is `a ↦ a^{q-2}` (which equals `a⁻¹` for `a ≠ 0` by `invFermatGen`);
    `enc = ZMod.val` (injective); the commuting square is `bls377_pow_commutes`.
    The `bls12_377` sibling of `pow249UnaryRealization`. -/
def powBls377UnaryRealization :
    EndoUnaryRealization (fun a : ZMod bls377Q => a ^ (bls377Q - 2)) powBls377Spec where
  enc := ZMod.val
  enc_inj := ZMod.val_injective bls377Q
  commutes := bls377_pow_commutes

/-- **The Fermat power chain computes the inverse on the worked vector `a = 1`.**
    `1⁻¹ = 1` in `ZMod bls377Q`; the emitted schedule `powBls377Spec` on the
    serialized `1` therefore equals `(1 : ZMod bls377Q).val`. Ties the schedule to
    a concrete inverse without evaluating the 377-bit chain. -/
theorem bls377_inv_one :
    powBls377Spec (1 : ZMod bls377Q).val = (1 : ZMod bls377Q).val := by
  rw [← bls377_inv_commutes 1 one_ne_zero, inv_one]

end Bls377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
