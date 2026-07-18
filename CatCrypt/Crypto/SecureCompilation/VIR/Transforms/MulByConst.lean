/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import CatCrypt.Crypto.SecureCompilation.VIR.Grind

/-!
# Mul-by-constant strength reduction on `Com catCryptDialect`

Replace `bvMul x (bvConst (2^a - 1))` with the shift+subtract chain
`bvSub (bvShiftL x a) x`. This is the classic Curve25519-flavour
strength-reduction (e.g. `mul121665` could be expressed as a
shift-by-17 minus 1 — though the actual Curve25519 constant
`a24 = 121666` is *not* itself Mersenne; this pass targets the
Mersenne family `k = 2^a - 1` which is the cleanest case to verify
and the most common one in strength-reduction-by-hand bignum code).

## Concrete deliverable

* Two canonical program *builders* `progMulConst` /
  `progShiftSub` that produce the source and target 2-let chains.
* Correctness `progMulConst_ret_denote_eq_progShiftSub_ret`: the two
  chains evaluated with `body = .ret .here` (return the mul result)
  have equal denotations. The crucial BitVec identity
  `x * (2^a - 1) = (x <<< a) - x` is proved as a standalone lemma
  `bitvec_mul_mersenne_eq`.
* Smoke tests at `w = 64`, `a = 17`, `k = 2^17 − 1 = 131071`.

## Design choice — why a builder, not a Com walker

The fully-generic walker `Com d Γ t → Com d Γ t` that recognises the
2-let chain has to navigate three dependent-type indices (the constant
width, the multiplication width, and the `Var` payload type) plus a
non-trivial De-Bruijn alignment between the source and target shapes.
The verified-rewrites infrastructure for that is `lean-mlir`'s
`PeepholeRewrite`, which VIR does not yet ship. Until that lands,
this file provides:

1. The arithmetic identity (load-bearing for any verified version).
2. A pointwise rewrite that the user invokes when emitting the chain
   (e.g. inside `CryptoToVIR` or `compress` IR emission).

The existing `Peephole.lean` follows the same "narrow-shape rewrite"
philosophy (Group A operates only when the constants sit directly
above the consuming op).

## Stretch (task b) — DEFERRED

A `refreshMask` op + insertion pass to maintain the masking-safe
invariant under `bvAnd`/`bvMul`/etc. was scoped as a stretch goal.
**Deferred** because it requires either (i) extending `CatCryptOp` with
a new constructor (touching `CatCryptDialect.lean` / `CTPredicate.lean`
/ `MaskingPredicate.lean` / `Grind.lean`, which are explicitly off-limits
for this task), or (ii) inventing a Com-level "fresh randomness source"
that VIR currently does not have. Auto-fresh-random insertion is
documented as needing Phase-5 effectful-`Com`; see `MaskingPredicate.lean`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

set_option autoImplicit false

universe u v

namespace MulByConst

/-! ## 1. Core arithmetic identity

`x * (2^a - 1) = (x <<< a) - x` over `BitVec w`, for `a ≤ w`. -/

/-- Mersenne strength-reduction identity over `BitVec w`. -/
theorem bitvec_mul_mersenne_eq {w a : Nat} (ha : a ≤ w) (x : BitVec w) :
    x * (BitVec.ofNat w (2^a - 1)) = (x <<< a) - x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_sub,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  -- Step 1: `(2^a - 1) % 2^w = 2^a - 1` because `2^a ≤ 2^w`.
  have h2pow_le : 2^a ≤ 2^w := Nat.pow_le_pow_right (by decide) ha
  have h2pow_pos : 0 < 2^a := Nat.two_pow_pos a
  have hsub_lt : 2^a - 1 < 2^w := by omega
  rw [Nat.mod_eq_of_lt hsub_lt]
  -- Step 2: let `n := x.toNat`, `n < 2^w`.
  set n := x.toNat with hn_def
  have hn_lt : n < 2^w := BitVec.isLt x
  -- Step 3: distribute `n * (2^a - 1) = n * 2^a - n` (Nat sub OK because `2^a ≥ 1`).
  rw [Nat.mul_sub_one]
  -- Goal:
  -- (n * 2^a - n) % 2^w = (2^w - n + n * 2^a % 2^w) % 2^w
  have h_n_le_mul : n ≤ n * 2^a := Nat.le_mul_of_pos_right n h2pow_pos
  have h_n_le_2w : n ≤ 2^w := Nat.le_of_lt hn_lt
  -- Rewrite LHS: (n * 2^a - n) % 2^w = (n * 2^a - n + 2^w) % 2^w.
  rw [show (n * 2^a - n) % 2^w = (n * 2^a - n + 2^w) % 2^w from
        (Nat.add_mod_right (n * 2^a - n) (2^w)).symm]
  -- LHS arg: n * 2^a - n + 2^w = (n * 2^a) + (2^w - n).
  rw [show n * 2^a - n + 2^w = (n * 2^a) + (2^w - n) from by omega]
  -- Now collapse RHS via mod-add.
  rw [show (2^w - n + n * 2^a % 2^w) % 2^w = (n * 2^a + (2^w - n)) % 2^w by
        conv_rhs => rw [Nat.add_comm]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]]

/-! ## 2. Source / target chain builders

A canonical 2-let chain "let c = bvConst k; let r = bvMul x c; …body"
and its rewritten "let s = bvShiftL x a; let r = bvSub s x; …body"
counterpart. The two share their post-binding context
`(.sword w :: .sword w :: Γ)`, so any `body` in the source plugs into
the target as well. -/

/-- Source chain:  `let c = bvConst w k;  let r = bvMul w x c;  body`.

    Note `body` sees `c` at de-Bruijn `.there .here` and `r` at `.here`. -/
def progMulConst {Γ : Ctxt catCryptDialect} {s : CryptoTy} (w : Nat)
    (k : BitVec w) (x : Ctxt.Var (d := catCryptDialect) Γ (CryptoTy.sword w))
    (body : Com catCryptDialect
              (CryptoTy.sword w :: CryptoTy.sword w :: Γ) s) :
    Com catCryptDialect Γ s :=
  .var (t := CryptoTy.sword w)
      { op := .bvConst w k, retTy_eq := rfl, args := .nil }
    (.var (t := CryptoTy.sword w)
        { op := .bvMul w, retTy_eq := rfl,
          args := .cons (.there x) (.cons .here .nil) }
      body)

/-- Target chain:  `let s = bvShiftL x a;  let r = bvSub s x;  body`.

    The bottom binding sees `x : Var Γ (.sword w)` lifted by one
    binding to `Var (.sword w :: Γ) (.sword w)`. -/
def progShiftSub {Γ : Ctxt catCryptDialect} {s : CryptoTy} (w a : Nat)
    (x : Ctxt.Var (d := catCryptDialect) Γ (CryptoTy.sword w))
    (body : Com catCryptDialect
              (CryptoTy.sword w :: CryptoTy.sword w :: Γ) s) :
    Com catCryptDialect Γ s :=
  .var (t := CryptoTy.sword w)
      { op := .bvShiftL w a, retTy_eq := rfl, args := .cons x .nil }
    (.var (t := CryptoTy.sword w)
        { op := .bvSub w, retTy_eq := rfl,
          args := .cons .here (.cons (.there x) .nil) }
      body)

/-! ## 3. Pointwise (closed-body) correctness theorem

We prove the rewrite preserves denotation for `body = .ret .here`
(return the mul result). The fully-general "any body" version is **not**
true as stated: the source binds `c = bvConst k` at the middle slot,
while the target binds `s = (x <<< a)` there, and a body that reads
`.there .here` would observe the difference. A general rewrite that
also rebinds — or removes — the middle slot needs a substitution
mechanism that VIR does not yet ship (cf. `Peephole.lean`'s identical
"Group A" caveat for constant folding). The pointwise theorem below
is what every concrete strength-reduction call site needs. -/

/-- **Main correctness.** For `body = .ret .here` (the "return mul result"
    use case), the source and target chains have equal denotations. -/
theorem progMulConst_ret_denote_eq_progShiftSub_ret {Γ : Ctxt catCryptDialect}
    {w a : Nat} (ha : a ≤ w) (k : BitVec w)
    (hk : k = BitVec.ofNat w (2^a - 1))
    (x : Ctxt.Var (d := catCryptDialect) Γ (CryptoTy.sword w))
    (V : Ctxt.Valuation Γ) :
    (progMulConst w k x (.ret .here)).denote V =
      (progShiftSub w a x (.ret .here)).denote V := by
  -- Both sides definitionally reduce to a single BitVec expression in
  -- `x.lookup V`. After `unfold` they're `x.lookup V * k` (LHS) and
  -- `(x.lookup V <<< a) - x.lookup V` (RHS), equal by `hk` +
  -- `bitvec_mul_mersenne_eq`.
  -- After unfolding both chains, the goal is a BitVec equation in
  -- `x.lookup V`. Pose `xv := x.lookup V`; goal reduces to the
  -- arithmetic identity `xv * k = (xv <<< a) - xv`.
  set xv : BitVec w := x.lookup V
  -- Both sides definitionally reduce to a single BitVec expression.
  show xv * k = (xv <<< a) - xv
  rw [hk]
  exact bitvec_mul_mersenne_eq ha xv

/-! ## 4. Smoke tests at `w = 64, a = 17, k = 131071` -/

namespace SmokeTest

/-- The BitVec identity at the concrete width/shift. -/
example (x : BitVec 64) :
    x * (BitVec.ofNat 64 (2^17 - 1)) = (x <<< 17) - x :=
  bitvec_mul_mersenne_eq (by decide) x

/-- Numeric check: `2^17 - 1 = 131071`. -/
example : (2 ^ 17 - 1 : Nat) = 131071 := by decide

/-- Smoke test of the chain rewrite for `body = .ret .here` at the
    concrete Mersenne constant. -/
def Γ₀ : Ctxt catCryptDialect := [CryptoTy.sword 64]
def x₀ : Ctxt.Var (d := catCryptDialect) Γ₀ (CryptoTy.sword 64) := .here

example (x_val : BitVec 64) :
    (progMulConst 64 (BitVec.ofNat 64 131071) x₀ (.ret .here)).denote
        (.cons x_val .nil) =
      x_val * (BitVec.ofNat 64 131071) := by
  rfl

example (x_val : BitVec 64) :
    (progShiftSub 64 17 x₀ (.ret .here)).denote (.cons x_val .nil) =
      (x_val <<< 17) - x_val := by
  rfl

/-- The two chains agree at every input. -/
example (x_val : BitVec 64) :
    (progMulConst 64 (BitVec.ofNat 64 131071) x₀ (.ret .here)).denote
        (.cons x_val .nil) =
      (progShiftSub 64 17 x₀ (.ret .here)).denote (.cons x_val .nil) :=
  progMulConst_ret_denote_eq_progShiftSub_ret (Γ := Γ₀)
    (w := 64) (a := 17) (by decide)
    (BitVec.ofNat 64 131071) (by decide)
    x₀ (.cons x_val .nil)

end SmokeTest

end MulByConst

end CatCrypt.Crypto.SecureCompilation.VIR
