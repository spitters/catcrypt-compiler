/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Init.Data.BitVec.Lemmas

/-!
# `BitVecNatBridge`: bounded `Nat` ↔ `BitVec w` emit-correctness transfer

A tiny, dependency-light pair of lemmas that discharge a `BitVec w` emit-vs-abstract
equality from a `Nat`-domain fact, replacing the hand-written `.eq_of_toNat_eq` +
`.toNat`-push wrap-collapse boilerplate repeated across the emit-vs-abstract tie
family (`gf127MulFold_eq_mod`, the other `CompileFromHax{Gf*, SdithGf251,
Mersenne31}` ties, the ML-KEM Barrett-compress ties, …).

Given a `BitVec w` value bounded by `bound`, an emit form `f` and an abstract form
`g`, their two `.toNat`-computation lemmas (each valid on the bounded range), and
the `Nat`-domain payload, the equality follows. The structural `BitVec.eq_of_toNat_eq`
plumbing is done ONCE here; each tie supplies only the two `toNat` pushes and the
`Nat` fact. `bitvec_eq_of_nat_bridge` is the unary form; `bitvec_binop_eq_of_nat_bridge`
is the binary (two-operand) form used by the `*MulFold_eq_mod` fold ties.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation

/-- **Unary bounded `Nat` → `BitVec` transfer.** Given `x.toNat < bound`, the two
`.toNat`-computation lemmas `hf`, `hg` (valid on the bounded range), and the
`Nat`-domain payload `hnat`, conclude `f x = g x`. The `BitVec.eq_of_toNat_eq`
plumbing is done once here. -/
theorem bitvec_eq_of_nat_bridge {w : Nat} (x : BitVec w)
    (f g : BitVec w → BitVec w) (nf ng : Nat → Nat) (bound : Nat)
    (hx : x.toNat < bound)
    (hf : ∀ y : BitVec w, y.toNat < bound → (f y).toNat = nf y.toNat)
    (hg : ∀ y : BitVec w, y.toNat < bound → (g y).toNat = ng y.toNat)
    (hnat : ∀ n, n < bound → nf n = ng n) :
    f x = g x := by
  apply BitVec.eq_of_toNat_eq
  rw [hf x hx, hg x hx, hnat _ hx]

/-- **Binary bounded `Nat` → `BitVec` transfer.** The two-operand analogue of
`bitvec_eq_of_nat_bridge`, used by the `*MulFold_eq_mod` fold ties (`f a b = g a b`
with `a, b` bounded). `hf`/`hg` push each binop to `Nat` on the bounded range,
`hnat` is the pure-`Nat` payload. -/
theorem bitvec_binop_eq_of_nat_bridge {w : Nat} (a b : BitVec w)
    (f g : BitVec w → BitVec w → BitVec w) (nf ng : Nat → Nat → Nat) (bound : Nat)
    (ha : a.toNat < bound) (hb : b.toNat < bound)
    (hf : ∀ u v : BitVec w, u.toNat < bound → v.toNat < bound →
      (f u v).toNat = nf u.toNat v.toNat)
    (hg : ∀ u v : BitVec w, u.toNat < bound → v.toNat < bound →
      (g u v).toNat = ng u.toNat v.toNat)
    (hnat : ∀ m n, m < bound → n < bound → nf m n = ng m n) :
    f a b = g a b := by
  apply BitVec.eq_of_toNat_eq
  rw [hf a b ha hb, hg a b ha hb, hnat _ _ ha hb]

end CatCrypt.Crypto.SecureCompilation
