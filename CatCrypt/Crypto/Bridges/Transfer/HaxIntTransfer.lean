/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.BitScan
public import Transfer.Congruence.ParamAuto

/-!
# Bounded field models of hax integer limbs as ParamTransfer relations

A hax extraction computes on field elements represented as `Array Int` limb arrays
through the operations of a `*Deps` class. A bounded field model interprets those
operations as field operations along a valuation `val : Array Int → F`, on the
representations a predicate `Valid` admits. This file states that shape as one
structure, restricts it to the subtype of valid representations, and registers
the operations on that subtype as `Related` / `RelatedBinOp` squares of the
ParamTransfer engine along the encoding `val ∘ Subtype.val`.

## Main definitions

* `BoundedFieldModel` — the field operations on `Array Int` as function fields,
  with a valuation, a validity predicate, and value and validity laws.
* `BoundedFieldModel.Carrier` — the subtype of valid representations, with its
  closed `*`, `+`, `-`, negation, `1`, `0` and `BoundedFieldModel.csq`.
* `BoundedFieldModel.enc` — the encoding `val ∘ Subtype.val` into `F`.
* `BoundedFieldModel.Rep` — the representation relation `Valid a ∧ val a = m`.

## Main results

* `mulRelated`, `addRelated`, `subRelated` — `RelatedBinOp` squares along `enc`;
  `sqRelated`, `negRelated`, `oneRelated`, `zeroRelated` — their `Related`
  analogues for the unary operations and the constants.
* `edwardsAdd_related` — the four output coordinates of extended Edwards addition
  on the carrier are related to the same formula over `F`, by one `param_auto` call.
* `squareMultiply_rep` — the extracted square-and-multiply scan of `BitScan` over a
  bounded field model preserves `Rep`.
-/

@[expose] public section

set_option autoImplicit false

open Transfer

namespace CatCrypt.Crypto.Bridges.Transfer.HaxInt

/-! ## The bounded field model -/

/-- A field `F` realized on `Array Int` representations: the operations as function
fields, a valuation `val`, and a predicate `Valid` on which each operation computes
the corresponding field operation of the represented values and which each
operation preserves. -/
structure BoundedFieldModel (F : Type) [Field F] [DecidableEq F] where
  /-- The product of representations. -/
  mul : Array Int → Array Int → Array Int
  /-- The square of a representation. -/
  square : Array Int → Array Int
  /-- The sum of representations. -/
  add : Array Int → Array Int → Array Int
  /-- The difference of representations. -/
  sub : Array Int → Array Int → Array Int
  /-- The negation of a representation. -/
  neg : Array Int → Array Int
  /-- The inverse of a representation. -/
  inv : Array Int → Array Int
  /-- Selection of the first representation on the bit `1`, of the second on `0`. -/
  ct_select : Int → Array Int → Array Int → Array Int
  /-- The indicator of the zero element. -/
  is_zero : Array Int → Int
  /-- The representation of `1`. -/
  ONE : Array Int
  /-- The representation of `0`. -/
  ZERO : Array Int
  /-- The field element a representation stands for. -/
  val : Array Int → F
  /-- The representations on which the laws below hold. -/
  Valid : Array Int → Prop
  /-- `mul` is the field product. -/
  mul_eq : ∀ a b, Valid a → Valid b → val (mul a b) = val a * val b
  /-- `mul` preserves `Valid`. -/
  mul_valid : ∀ a b, Valid a → Valid b → Valid (mul a b)
  /-- `square` is the field square. -/
  square_eq : ∀ a, Valid a → val (square a) = val a ^ 2
  /-- `square` preserves `Valid`. -/
  square_valid : ∀ a, Valid a → Valid (square a)
  /-- `add` is the field sum. -/
  add_eq : ∀ a b, Valid a → Valid b → val (add a b) = val a + val b
  /-- `add` preserves `Valid`. -/
  add_valid : ∀ a b, Valid a → Valid b → Valid (add a b)
  /-- `sub` is the field difference. -/
  sub_eq : ∀ a b, Valid a → Valid b → val (sub a b) = val a - val b
  /-- `sub` preserves `Valid`. -/
  sub_valid : ∀ a b, Valid a → Valid b → Valid (sub a b)
  /-- `neg` is the field negation. -/
  neg_eq : ∀ a, Valid a → val (neg a) = - val a
  /-- `neg` preserves `Valid`. -/
  neg_valid : ∀ a, Valid a → Valid (neg a)
  /-- `inv` is the field inverse at a nonzero argument. -/
  inv_eq : ∀ a, Valid a → val a ≠ 0 → val (inv a) = (val a)⁻¹
  /-- `inv` preserves `Valid`. -/
  inv_valid : ∀ a, Valid a → Valid (inv a)
  /-- `ONE` represents `1`. -/
  one_eq : val ONE = 1
  /-- `ONE` is valid. -/
  one_valid : Valid ONE
  /-- `ZERO` represents `0`. -/
  zero_eq : val ZERO = 0
  /-- `ZERO` is valid. -/
  zero_valid : Valid ZERO
  /-- `is_zero` is the indicator of `0`. -/
  is_zero_eq : ∀ a, Valid a → is_zero a = if val a = 0 then 1 else 0
  /-- `ct_select` on a bit selects the first argument on `1`. -/
  ct_select_eq : ∀ (c : Int) (a b : Array Int), c = 0 ∨ c = 1 → Valid a → Valid b →
    val (ct_select c a b) = if c = 1 then val a else val b
  /-- `ct_select` preserves `Valid`. -/
  ct_select_valid : ∀ (c : Int) (a b : Array Int), c = 0 ∨ c = 1 → Valid a → Valid b →
    Valid (ct_select c a b)

/-! ## The carrier of valid representations and its encoding -/

namespace BoundedFieldModel

variable {F : Type} [Field F] [DecidableEq F] (M : BoundedFieldModel F)

/-- The valid representations of `M`. -/
def Carrier : Type := {a : Array Int // M.Valid a}

/-- The encoding of a valid representation as the field element it stands for. -/
def enc : M.Carrier → F := fun a => M.val a.1

/-- The representation relation: `a` is valid and stands for `m`. -/
def Rep (a : Array Int) (m : F) : Prop := M.Valid a ∧ M.val a = m

instance : Mul M.Carrier := ⟨fun a b => ⟨M.mul a.1 b.1, M.mul_valid _ _ a.2 b.2⟩⟩
instance : Add M.Carrier := ⟨fun a b => ⟨M.add a.1 b.1, M.add_valid _ _ a.2 b.2⟩⟩
instance : Sub M.Carrier := ⟨fun a b => ⟨M.sub a.1 b.1, M.sub_valid _ _ a.2 b.2⟩⟩
instance : Neg M.Carrier := ⟨fun a => ⟨M.neg a.1, M.neg_valid _ a.2⟩⟩
instance : One M.Carrier := ⟨⟨M.ONE, M.one_valid⟩⟩
instance : Zero M.Carrier := ⟨⟨M.ZERO, M.zero_valid⟩⟩

/-- The square on the carrier, computed by the `square` operation of `M`. -/
def csq (a : M.Carrier) : M.Carrier := ⟨M.square a.1, M.square_valid _ a.2⟩

/-- The product on the carrier is `mul` on the underlying representations. -/
@[simp] theorem mul_val (a b : M.Carrier) : (a * b).1 = M.mul a.1 b.1 := rfl
/-- The sum on the carrier is `add` on the underlying representations. -/
@[simp] theorem add_val (a b : M.Carrier) : (a + b).1 = M.add a.1 b.1 := rfl
/-- The difference on the carrier is `sub` on the underlying representations. -/
@[simp] theorem sub_val (a b : M.Carrier) : (a - b).1 = M.sub a.1 b.1 := rfl
/-- The negation on the carrier is `neg` on the underlying representation. -/
@[simp] theorem neg_val (a : M.Carrier) : (-a).1 = M.neg a.1 := rfl

/-- `mul` realizes the field product along `enc`. -/
instance mulRelated : RelatedBinOp M.enc (· * ·) (· * ·) where
  comm a b := M.mul_eq _ _ a.2 b.2

/-- `add` realizes the field sum along `enc`. -/
instance addRelated : RelatedBinOp M.enc (· + ·) (· + ·) where
  comm a b := M.add_eq _ _ a.2 b.2

/-- `sub` realizes the field difference along `enc`. -/
instance subRelated : RelatedBinOp M.enc (· - ·) (· - ·) where
  comm a b := M.sub_eq _ _ a.2 b.2

/-- `square` realizes the field square along `enc`. -/
instance sqRelated (a : M.Carrier) (a' : F) [ha : Related M.enc a a'] :
    Related M.enc (M.csq a) (a' ^ 2) where
  rel := (M.square_eq _ a.2).trans (by rw [← ha.rel]; rfl)

/-- `neg` realizes the field negation along `enc`. -/
instance negRelated (a : M.Carrier) (a' : F) [ha : Related M.enc a a'] :
    Related M.enc (-a) (-a') where
  rel := (M.neg_eq _ a.2).trans (by rw [← ha.rel]; rfl)

/-- `ONE` encodes `1`. -/
instance oneRelated : Related M.enc (1 : M.Carrier) (1 : F) where
  rel := M.one_eq

/-- `ZERO` encodes `0`. -/
instance zeroRelated : Related M.enc (0 : M.Carrier) (0 : F) where
  rel := M.zero_eq

/-! ## Extended Edwards addition by the engine -/

/-- The four output coordinates of extended Edwards addition, with leaves `x₁ y₁ t₁`,
`x₂ y₂ z₂ t₂`, `k` in place of `2d` and `z` in place of `2 z₁`, computed on the
carrier, encode the same formula over `F`. -/
theorem edwardsAdd_related (x₁ y₁ t₁ z x₂ y₂ z₂ t₂ k : M.Carrier) :
    let a := (y₁ - x₁) * (y₂ - x₂)
    let b := (y₁ + x₁) * (y₂ + x₂)
    let c := t₁ * k * t₂
    let dz := z * z₂
    let e := b - a
    let f := dz - c
    let g := dz + c
    let h := b + a
    let A := (M.enc y₁ - M.enc x₁) * (M.enc y₂ - M.enc x₂)
    let B := (M.enc y₁ + M.enc x₁) * (M.enc y₂ + M.enc x₂)
    let C := M.enc t₁ * M.enc k * M.enc t₂
    let DZ := M.enc z * M.enc z₂
    Related M.enc (e * f) ((B - A) * (DZ - C)) ∧
      Related M.enc (g * h) ((DZ + C) * (B + A)) ∧
      Related M.enc (f * g) ((DZ - C) * (DZ + C)) ∧
      Related M.enc (e * h) ((B - A) * (B + A)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> param_auto

end BoundedFieldModel

/-! ## The square-and-multiply scan -/

namespace BoundedFieldModel

variable {F : Type} [Field F] [DecidableEq F] (M : BoundedFieldModel F)

/-- The extracted square-and-multiply scan with `square` and multiplication by a
valid `s`, over `n` limbs of `w` bits, started from a representation of `val s ^ e`,
ends at a representation of `val s ^ (e * 2^(w n) + ∑_{k<n} limb_k 2^(w k))`. -/
theorem squareMultiply_rep {s : Array Int} (hs : M.Valid s) (w : Nat) (hw : 0 < w)
    (limbAt : Int → Int) (n : Nat)
    (hlimb : ∀ k : Nat, k < n → 0 ≤ limbAt k ∧ limbAt k < 2 ^ w)
    (a : Array Int) (e : Nat) (ha : M.Rep a (M.val s ^ e)) :
    M.Rep (Hax.whileFold ((n : Int), a) (fun _ => true)
        (CatCrypt.Hax.BitScan.outerBody w limbAt M.square (fun r => M.mul r s))).merge.2
      (M.val s ^ (e * 2 ^ (w * n)
        + ∑ k ∈ Finset.range n, (limbAt k).toNat * 2 ^ (w * k))) :=
  CatCrypt.Hax.BitScan.squareMultiply_rel M.Rep (M.val s)
    (fun b m ⟨hb, hm⟩ => ⟨M.square_valid b hb, by rw [M.square_eq b hb, hm, pow_two]⟩)
    (fun b m ⟨hb, hm⟩ => ⟨M.mul_valid b s hb hs, by rw [M.mul_eq b s hb hs, hm]⟩)
    w hw limbAt n hlimb a e ha

end BoundedFieldModel

end CatCrypt.Crypto.Bridges.Transfer.HaxInt
