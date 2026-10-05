/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Rust
public import HaxLean.Runtime
public import HaxAscent.RustSemantics.RCompOk

/-!
# Encoding of Aeneas values as values of the Hax runtime

The Aeneas `Std` model (`HaxLean.Rust`, namespace `Aeneas.Std`) represents a Rust
value by its machine type: `UScalar ty` and `IScalar ty` over `BitVec`, `Bool`,
`Option`, products, and the list-backed containers `Array α n`, `Slice α` and
`alloc.vec.Vec α`. The Hax runtime (`HaxLean.Runtime`, namespace `Hax`) represents
the same value by an unbounded `Int`, a `Bool`, an `Option`, a product, or an
`Array`. This module fixes the map between them.

## Main results

* `Encode`, `EncRel` — the encoding and its graph
* `ListRel`, `listRel_encRel_iff` — containers against runtime arrays
* `rcompOk_iff`, `not_rcompOk_of` — stating and refuting a square
* `iMinusOne` — the input of the counterexamples

## Encoding

| Aeneas type | runtime type | encoding |
|---|---|---|
| `UScalar ty` | `Int` | `x ↦ (x.val : Int)` (the unsigned value) |
| `IScalar ty` | `Int` | `x ↦ x.val` (the two's-complement value) |
| `Bool` | `Bool` | identity |
| `Option α` | `Option β` | `Option.map enc` |
| `α × α'` | `β × β'` | `Prod.map enc enc` |
| `Array α n`, `Slice α`, `Vec α` | `Array β` | the list, mapped by `enc`, as an array |

`Encode α β` carries the map `enc`; `EncRel` is its graph, the value relation
of the scalar squares. A container is related to a runtime array by
`ListRel R l arr := ArrayRel R l.toArray arr` for an arbitrary element relation
`R`; `listRel_encRel_iff` identifies `ListRel EncRel` with the encoding of the list.

## Squares

For an Aeneas operation `opA : … → RustM α` and a runtime operation `opC`, a square
is `RCompOk EncRel (opA args) (pure (opC (enc args)) : Id _)`: whenever `opA`
returns `ok r`, `opC` computes `enc r`. A pure Aeneas operation enters through
`lift`, as in extracted code. `rcompOk_iff` states an `RCompOk` goal against a
total `Id` computation as that implication; `not_rcompOk_of` refutes a square by
one input on which the Aeneas side returns a value whose encoding differs from the
runtime value.

## Inputs of the counterexamples

`iMinusOne ty` is the signed scalar `-1` of every signed type; the
counterexamples stated for all widths use it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Std.Do

/-- The encoding of an Aeneas value of type `α` as a runtime value of type `β`. -/
class Encode (α : Type) (β : outParam Type) where
  /-- The runtime value that represents an Aeneas value. -/
  enc : α → β

export Encode (enc)

/-- An unsigned scalar is encoded by its value. -/
instance instEncodeUScalar {ty : UScalarTy} : Encode (UScalar ty) Int :=
  ⟨fun x => (x.val : Int)⟩

/-- A signed scalar is encoded by its two's-complement value. -/
instance instEncodeIScalar {ty : IScalarTy} : Encode (IScalar ty) Int := ⟨fun x => x.val⟩

/-- A Boolean is encoded by itself. -/
instance instEncodeBool : Encode Bool Bool := ⟨id⟩

/-- An option is encoded componentwise. -/
instance instEncodeOption {α β : Type} [Encode α β] : Encode (Option α) (Option β) :=
  ⟨Option.map enc⟩

/-- A pair is encoded componentwise. -/
instance instEncodeProd {α α' β β' : Type} [Encode α β] [Encode α' β'] :
    Encode (α × α') (β × β') :=
  ⟨Prod.map enc enc⟩

/-- A fixed-length array is encoded as the array of its encoded entries. -/
instance instEncodeArray {α β : Type} [Encode α β] {n : Usize} :
    Encode (Aeneas.Std.Array α n) (_root_.Array β) :=
  ⟨fun v => (v.val.map enc).toArray⟩

/-- A slice is encoded as the array of its encoded entries. -/
instance instEncodeSlice {α β : Type} [Encode α β] : Encode (Slice α) (_root_.Array β) :=
  ⟨fun v => (v.val.map enc).toArray⟩

/-- A vector is encoded as the array of its encoded entries. -/
instance instEncodeVec {α β : Type} [Encode α β] :
    Encode (alloc.vec.Vec α) (_root_.Array β) :=
  ⟨fun v => (v.val.map enc).toArray⟩

@[simp] theorem enc_uscalar {ty : UScalarTy} (x : UScalar ty) : enc x = (x.val : Int) := rfl

@[simp] theorem enc_iscalar {ty : IScalarTy} (x : IScalar ty) : enc x = x.val := rfl

@[simp] theorem enc_bool (b : Bool) : enc b = b := rfl

@[simp] theorem enc_option {α β : Type} [Encode α β] (o : Option α) :
    enc o = o.map enc := rfl

@[simp] theorem enc_prod {α α' β β' : Type} [Encode α β] [Encode α' β'] (p : α × α') :
    enc p = (enc p.1, enc p.2) := rfl

/-- The encoding of unsigned scalars is injective. -/
theorem enc_uscalar_inj {ty : UScalarTy} {x y : UScalar ty} : enc x = enc y ↔ x = y := by
  cases x; cases y
  simp [UScalar.val, BitVec.toNat_inj, Int.natCast_inj]

/-- The encoding of signed scalars is injective. -/
theorem enc_iscalar_inj {ty : IScalarTy} {x y : IScalar ty} : enc x = enc y ↔ x = y := by
  cases x; cases y
  simp [IScalar.val, BitVec.toInt_inj]

/-- The value relation of the encoding: `c` is the encoding of `r`. -/
def EncRel {α β : Type} [Encode α β] (r : α) (c : β) : Prop := enc r = c

@[simp] theorem encRel_iff {α β : Type} [Encode α β] (r : α) (c : β) :
    EncRel r c ↔ enc r = c := Iff.rfl

/-- A list-backed Aeneas container (the `val` of an `Array`, `Slice` or `Vec`) and a
    runtime array are related pointwise by `R`. -/
def ListRel {α β : Type} (R : α → β → Prop) (l : List α) (arr : _root_.Array β) : Prop :=
  ArrayRel R l.toArray arr

theorem listRel_iff_forall₂ {α β : Type} {R : α → β → Prop} {l : List α}
    {arr : _root_.Array β} : ListRel R l arr ↔ List.Forall₂ R l arr.toList := Iff.rfl

/-- The pointwise encoding relation on a list is the encoding of the list. -/
theorem listRel_encRel_iff {α β : Type} [Encode α β] {l : List α} {arr : _root_.Array β} :
    ListRel EncRel l arr ↔ (l.map enc).toArray = arr := by
  have key : ∀ m : List β, List.Forall₂ EncRel l m ↔ l.map enc = m := by
    induction l with
    | nil => intro m; cases m <;> simp [forall₂_nil_cons_iff]
    | cons a l ih =>
      intro m
      cases m with
      | nil => simp [forall₂_cons_nil_iff]
      | cons b m =>
        rw [List.forall₂_cons, ih, List.map_cons, List.cons.injEq, encRel_iff]
  rw [listRel_iff_forall₂, key]
  constructor
  · intro h; rw [h]
  · rintro rfl; rfl

/-- An `RCompOk` relation between an Aeneas computation and a total runtime value:
    whenever `c` returns `ok a`, `R a c'` holds. -/
theorem rcompOk_iff {α β : Type} {R : α → β → Prop} {c : RustM α} {c' : β} :
    RCompOk R c (pure c' : Id β) ↔ ∀ a, c = .ok a → R a c' := by
  rw [RCompOk.id_iff]
  cases c <;> simp [wp, PredTrans.apply]

/-- A square whose Aeneas side is `lift v` (a pure library operation) holds exactly
    when `v` and `c'` are related. -/
theorem rcompOk_lift {α β : Type} {R : α → β → Prop} {v : α} {c' : β} :
    RCompOk R (lift v) (pure c' : Id β) ↔ R v c' := by
  rw [rcompOk_iff]
  constructor
  · intro h; exact h v rfl
  · intro h a ha; cases ha; exact h

/-- A square whose Aeneas side is `ok v` holds exactly when `v` and `c'` are related. -/
theorem rcompOk_ok {α β : Type} {R : α → β → Prop} {v : α} {c' : β} :
    RCompOk R (RustM.ok v) (pure c' : Id β) ↔ R v c' := rcompOk_lift

/-- A square fails when the Aeneas computation returns `ok a` for a value `a` that is
    not related to the runtime value. -/
theorem not_rcompOk_of {α β : Type} {R : α → β → Prop} {c : RustM α} {c' : β} (a : α)
    (hc : c = .ok a) (hR : ¬ R a c') : ¬ RCompOk R c (pure c' : Id β) := by
  rw [rcompOk_iff]
  intro h
  exact hR (h a hc)

/-- The signed scalar `-1` of type `ty`: every bit set. -/
def iMinusOne (ty : IScalarTy) : IScalar ty := ⟨BitVec.allOnes ty.numBits⟩

/-- The all-ones vector of a signed scalar width is `-1` as an integer. -/
theorem allOnes_toInt (ty : IScalarTy) : (BitVec.allOnes ty.numBits).toInt = -1 := by
  have := ty.numBits_nonzero
  simp only [BitVec.toInt_allOnes]
  rw [if_pos (by omega)]

@[simp] theorem iMinusOne_val (ty : IScalarTy) : (iMinusOne ty).val = -1 := allOnes_toInt ty

/-- `Int.bmod` depends on its argument only through its residue class: two
    integers congruent modulo `m` have the same balanced remainder. -/
theorem bmodCongr {a b : Int} {m : Nat} (h : a % m = b % m) : a.bmod m = b.bmod m := by
  rw [Int.bmod_eq_emod, Int.bmod_eq_emod, h]

/-- The residue of a signed scalar's value modulo its own width's modulus is the
    scalar's unsigned bit pattern: `Hax.cast_uw` applied to a signed scalar's own
    width recovers `x.bv.toNat`. -/
theorem iscalar_mod {ty : IScalarTy} (x : IScalar ty) :
    x.bv.toInt % ((2 ^ ty.numBits : Nat) : Int) = (x.bv.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]
  exact_mod_cast Nat.mod_eq_of_lt x.bv.isLt

theorem iscalar_cast_uw {ty : IScalarTy} (x : IScalar ty) :
    Hax.cast_uw ty.numBits x.val = (x.bv.toNat : Int) := by
  show (x.val % ((2 ^ ty.numBits : Nat) : Int)) = _
  rw [IScalar.val]
  exact iscalar_mod x

/-- A signed value's residue modulo `2^v` for `v` above its own width is itself:
    two's-complement reduction to a wider width is the identity. -/
theorem smod2w_eq_self_of_ge {w v : Nat} (hw : 1 ≤ w) (h : w ≤ v) (x : BitVec w) :
    Hax.smod2w v x.toInt = x.toInt := by
  have hlt := @BitVec.toInt_lt w x
  have hge := @BitVec.le_toInt w x
  show Int.bmod x.toInt (2 ^ v) = x.toInt
  obtain ⟨k, hk⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, w = j + 1 := ⟨w - 1, by omega⟩
  have hjk : j ≤ k := by omega
  have e2 : (2 : Nat) ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hjk
  have e2' : (2 : Int) ^ j ≤ 2 ^ k := by exact_mod_cast e2
  have epow : ((2 ^ v : Nat) : Int) = 2 ^ k * 2 := by push_cast; rw [hk]; exact Int.pow_succ 2 k
  apply Int.bmod_eq_of_le
  · have hd : ((2 ^ v : Nat) : Int) / 2 = 2 ^ k := by rw [epow]; omega
    rw [hd]; have hj' : w - 1 = j := by omega
    rw [hj'] at hge; omega
  · have hd : (((2 ^ v : Nat) : Int) + 1) / 2 = 2 ^ k := by rw [epow]; omega
    rw [hd]; have hj' : w - 1 = j := by omega
    rw [hj'] at hlt; omega

/-- A signed scalar's own residue at its own width is its value: two's-complement
    reduction of an already-canonical value is the identity. -/
theorem bmod_self_eq {w : Nat} (hw : 1 ≤ w) (x : BitVec w) : x.toInt.bmod (2 ^ w) = x.toInt := by
  have := smod2w_eq_self_of_ge hw (Nat.le_refl w) x
  rwa [Hax.smod2w] at this

/-- A signed scalar's value at its own width equals its residue modulo any
    natural-cast modulus, so `toInt_eq_toNat_bmod` inverts to give the scalar's
    unsigned bit pattern as the residue of its signed value. -/
theorem toNat_eq_toInt_emod {v : Nat} (y : BitVec v) :
    (y.toNat : Int) = y.toInt % ((2 ^ v : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]
  exact_mod_cast (Nat.mod_eq_of_lt y.isLt).symm

end CatCrypt.Hax.RustSemantics
