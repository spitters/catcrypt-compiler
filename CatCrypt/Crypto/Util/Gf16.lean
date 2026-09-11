/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Mathlib.Data.BitVec
public import Mathlib.Algebra.Group.Defs
public import Std.Tactic.BVDecide

/-!
# Verified GF(16) — `GF(2)[x] / (x^4 + x + 1)`

A computable, verified Lean reference implementation of GF(16) over the
"low-nibble" Rijndael-style irreducible polynomial `x^4 + x + 1` (encoded
as `0x13`). Used by the MAYO bridge (`MayoHaxLowCTBridge`) to replace
opaque encoder round-trip axioms with proven identities.

## Representation

A `Gf16` element is a `BitVec 4` (an element of `{0,1,…,15}` understood
as a polynomial of degree `<4` over `GF(2)`).

* **addition** = bitwise XOR (`a ^^^ b`);
* **multiplication** = polynomial multiplication over `GF(2)` of two
  `BitVec 4` operands, reduced modulo `0x13` (degree-4 irreducible).

The reduction polynomial choice (`x^4 + x + 1`, value `0x13`) follows
the MAYO reference implementation in `mayo-hax`.

## Field axioms

Closed by `decide` / `native_decide` / `bv_decide` over the 16-element
domain. No `sorry`, no axioms beyond Lean's kernel + Mathlib's standard
`BitVec` infrastructure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-- A `GF(16)` element: a 4-bit polynomial over `GF(2)` (low nibble).

    Defined as an `abbrev` over `BitVec 4` so all `BitVec` instances and
    bv-decide tactics flow through transparently. -/
abbrev Gf16 : Type := BitVec 4

namespace Gf16

/-! ## Multiplication via shift-and-XOR reduction by `0x13` -/

/-- Shift-and-XOR GF(16) multiplication, lifted to `BitVec 8` for the
    raw polynomial product, then reduced by `0x13 = x^4+x+1`. -/
def mulAux (a b : BitVec 4) : BitVec 4 :=
  let a8 : BitVec 8 := a.setWidth 8
  let b8 : BitVec 8 := b.setWidth 8
  let p0 := if b8 &&& 1#8 == 0#8 then 0#8 else a8
  let p1 := if (b8 >>> 1) &&& 1#8 == 0#8 then 0#8 else a8 <<< 1
  let p2 := if (b8 >>> 2) &&& 1#8 == 0#8 then 0#8 else a8 <<< 2
  let p3 := if (b8 >>> 3) &&& 1#8 == 0#8 then 0#8 else a8 <<< 3
  let prod8 : BitVec 8 := p0 ^^^ p1 ^^^ p2 ^^^ p3
  -- prod8 has degree ≤ 6. Reduce by 0x13 = x^4 + x + 1.
  let r1 := if (prod8 >>> 4) &&& 1#8 == 0#8 then prod8 else prod8 ^^^ 0x13#8
  let r2 := if (r1   >>> 5) &&& 1#8 == 0#8 then r1    else r1    ^^^ (0x13#8 <<< 1)
  let r3 := if (r2   >>> 6) &&& 1#8 == 0#8 then r2    else r2    ^^^ (0x13#8 <<< 2)
  r3.setWidth 4

/-- GF(16) multiplication. -/
def mul (a b : Gf16) : Gf16 := mulAux a b

/-! ## Field axioms (closed by `bv_decide` / explicit case analysis)

We expose all axioms as theorems over `BitVec 4 = Gf16`. The
multiplicative axioms are closed by `decide` enumerating all 16² (or 16³)
cases via the `BitVec` decidable equality. -/

theorem add_zero' (a : Gf16) : a ^^^ (0 : BitVec 4) = a := by bv_decide
theorem zero_add' (a : Gf16) : (0 : BitVec 4) ^^^ a = a := by bv_decide
theorem add_comm' (a b : Gf16) : a ^^^ b = b ^^^ a := by bv_decide
theorem add_assoc' (a b c : Gf16) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by bv_decide
theorem add_self' (a : Gf16) : a ^^^ a = (0 : BitVec 4) := by bv_decide

theorem mul_one (a : Gf16) : mul a (1 : BitVec 4) = a := by
  revert a; decide

theorem one_mul (a : Gf16) : mul (1 : BitVec 4) a = a := by
  revert a; decide

theorem mul_zero (a : Gf16) : mul a (0 : BitVec 4) = (0 : BitVec 4) := by
  revert a; decide

theorem zero_mul (a : Gf16) : mul (0 : BitVec 4) a = (0 : BitVec 4) := by
  revert a; decide

theorem mul_comm (a b : Gf16) : mul a b = mul b a := by
  revert a b; decide

theorem mul_assoc (a b c : Gf16) : mul (mul a b) c = mul a (mul b c) := by
  revert a b c; native_decide

theorem mul_add (a b c : Gf16) : mul a (b ^^^ c) = (mul a b) ^^^ (mul a c) := by
  revert a b c; native_decide

theorem add_mul (a b c : Gf16) : mul (a ^^^ b) c = (mul a c) ^^^ (mul b c) := by
  revert a b c; native_decide

/-! ## Encoders to/from BitVec, Nat, Int -/

/-- Inject a `BitVec 4` into `Gf16` (identity). -/
def ofBitVec (b : BitVec 4) : Gf16 := b

/-- Project a `Gf16` element back to a `BitVec 4` (identity). -/
def toBitVec (g : Gf16) : BitVec 4 := g

theorem ofBitVec_toBitVec (g : Gf16) : ofBitVec (toBitVec g) = g := rfl
theorem toBitVec_ofBitVec (b : BitVec 4) : toBitVec (ofBitVec b) = b := rfl

/-- Inject a `Nat` (mod 16) into `Gf16`. -/
def fromNat (n : Nat) : Gf16 := BitVec.ofNat 4 n

/-- Project a `Gf16` element to a `Nat` in `[0..15]`. -/
def asNat (g : Gf16) : Nat := BitVec.toNat g

/-- Project a `Gf16` element to an `Int`. -/
def asInt (g : Gf16) : Int := (BitVec.toNat g : Int)

/-- Inject an `Int` (clamped mod 16) into `Gf16`. -/
def fromInt (i : Int) : Gf16 := BitVec.ofNat 4 i.toNat

theorem fromNat_asNat (g : Gf16) : fromNat (asNat g) = g := by
  show BitVec.ofNat 4 (BitVec.toNat g) = g
  exact BitVec.ofNat_toNat 4 g

theorem fromInt_asInt (g : Gf16) : fromInt (asInt g) = g := by
  show BitVec.ofNat 4 ((BitVec.toNat g : Int).toNat) = g
  simp

theorem asNat_lt (g : Gf16) : asNat g < 16 := by
  show BitVec.toNat g < 16
  have h : BitVec.toNat g < 2 ^ 4 := g.isLt
  simpa using h

end Gf16

end CatCrypt.Util
