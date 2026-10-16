/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Contract
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Array
public import Transfer.Base.Related

/-!
# Representation assertions and transfer of contracts

`repAt n a enc x` says that the array of `n`-byte cells at `a` holds the encoding `enc x` of
the abstract value `x`; it is the array of some `r` with `Related enc x r` (`holds_repAt_iff`),
the relation of the `Related` registry of ParamTransfer.

`ContractSpec.binOp P Q bop W pub` is the contract of an operation that replaces the value `r`
held by `P` with `bop r s`, where `s` is the value held by `Q`. A contract of this shape over
representations, together with the commuting square `RelatedBinOp enc op bop`, gives the
contract over the abstract values, with `P ∘ enc` and `Q ∘ enc` as the location assertions and
`op` as the operation (`SContract.transfer`).

The instance is the one-limb modular addition `addModStep p a b` on the byte memory `MemW 64`:
its contract over `List (BitVec 64)` (`addMod_limbs_contract`) transfers along the one-limb
encoding `limb1 p` of `ZMod p`, whose square for `+` is `addModL_related`, to the contract
over `ZMod p` stated with `repAt` (`addMod_zmod_contract`).

## Main definitions

* `repAt`: a value represented as an array of cells.
* `ContractSpec.binOp`: the contract of an in-place binary operation.
* `limb1`, `addModL`, `addModStep`, `addModRun`: the one-limb encoding of `ZMod p`, modular
  addition of limbs, and its run on the byte memory.

## Main results

* `holds_repAt_iff`: `repAt` is the array of a related representation.
* `SContract.transfer`: a contract over representations and a commuting square give the
  contract over abstract values.
* `addModL_related`: the commuting square of `+` on `ZMod p` along `limb1 p`.
* `addMod_limbs_contract`, `addMod_zmod_contract`: the contract of `addModRun` over limbs, and
  the contract over `ZMod p` obtained from it by `SContract.transfer`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

universe u v w x

open Footprinted SAssert Transfer

/-! ## Representation assertions -/

section Rep

variable {A : Nat} {α : Type}

/-- The value `x` represented through the encoding `enc` as the array of `n`-byte cells at
    `a`. -/
abbrev repAt (n : Nat) (a : BitVec A) (enc : α → List (BitVec (8 * n))) (x : α) :
    SAssert (MemW A) (BitVec A) :=
  arrAt n a (enc x)

/-- `repAt n a enc x` holds exactly when the array at `a` holds a representation related to
    `x` by `enc`. -/
theorem holds_repAt_iff (n : Nat) (a : BitVec A) (enc : α → List (BitVec (8 * n))) (x : α)
    (m : MemW A) :
    (repAt n a enc x).holds m ↔ ∃ r, Related enc x r ∧ (arrAt n a r).holds m :=
  ⟨fun h => ⟨_, ⟨rfl⟩, h⟩, fun ⟨_, hr, h⟩ => by rw [repAt, hr.rel]; exact h⟩

end Rep

/-! ## Transfer of contracts -/

section Generic

variable {σ : Type u} {L : Type v} [Footprinted σ L] {T : Type w}

/-- The contract of an in-place binary operation: the location assertion `P` holds `r` and
    `Q` holds `s` before; `P` holds `bop r s` and `Q` holds `s` after. -/
def ContractSpec.binOp {β : Type x} (P Q : β → SAssert σ L) (bop : β → β → β)
    (W : β × β → σ → Set L) (pub : σ → σ → Prop) : ContractSpec σ L (β × β) where
  pre p := P p.1 ∗ Q p.2
  post p := P (bop p.1 p.2) ∗ Q p.2
  writes := W
  pub := pub

/-- **Transfer of a contract.** A contract of `bop` over representations and the commuting
    square `enc (op x y) = bop (enc x) (enc y)` give the contract of `op` over the abstract
    values, with the location assertions composed with the encoding. -/
theorem SContract.transfer {α β : Type x} {X : σ → T → σ → Prop} {P Q : β → SAssert σ L}
    {bop : β → β → β} {W : β × β → σ → Set L} {pub : σ → σ → Prop} {enc : α → β}
    {op : α → α → α} [hop : RelatedBinOp enc op bop]
    (h : SContract X (ContractSpec.binOp P Q bop W pub)) :
    SContract X (ContractSpec.binOp (fun x => P (enc x)) (fun x => Q (enc x)) op
      (fun p => W (enc p.1, enc p.2)) pub) :=
  h.adapt (fun p _ hs => ⟨(enc p.1, enc p.2), hs, fun s' h' => by
      show (P (enc (op p.1 p.2)) ∗ Q (enc p.2)).holds s'
      rw [hop.comm]
      exact h', subset_rfl⟩) fun _ _ hp => hp

end Generic

/-! ## The instance: one-limb modular addition -/

section AddMod

/-- The one-limb encoding of `ZMod p`: the canonical representative as a 64-bit word. -/
def limb1 (p : Nat) (x : ZMod p) : List (BitVec 64) := [BitVec.ofNat 64 x.val]

/-- Modular addition of the first limbs of two limb arrays. -/
def addModL (p : Nat) (r s : List (BitVec 64)) : List (BitVec 64) :=
  [BitVec.ofNat 64 (((r.headD 0).toNat + (s.headD 0).toNat) % p)]

/-- The commuting square of `+` on `ZMod p` and `addModL p` along `limb1 p`, for
    `p ≤ 2 ^ 64`. -/
theorem addModL_related (p : Nat) [NeZero p] (hp : p ≤ 2 ^ 64) :
    RelatedBinOp (limb1 p) (· + ·) (addModL p) where
  comm x y := by
    have hx := Nat.lt_of_lt_of_le (ZMod.val_lt x) hp
    have hy := Nat.lt_of_lt_of_le (ZMod.val_lt y) hp
    simp only [limb1, addModL, List.headD_cons, BitVec.toNat_ofNat, ZMod.val_add,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- The array of 64-bit limbs at `a` holds `r`, of length one. -/
def limbsAt (a : BitVec 64) (r : List (BitVec 64)) : SAssert (MemW 64) (BitVec 64) :=
  arrAt 8 a r ∗ ⌜r.length = 1⌝

/-- The memory with the limb at `a` replaced by the sum modulo `p` of the limbs at `a` and
    `b`. -/
def addModStep (p : Nat) (a b : BitVec 64) (m : MemW 64) : MemW 64 :=
  writeLE 8 m a (BitVec.ofNat 64 (((readLE 8 m a).toNat + (readLE 8 m b).toNat) % p))

/-- The run of `addModStep`, with the empty trace. -/
def addModRun (p : Nat) (a b : BitVec 64) : MemW 64 → Unit → MemW 64 → Prop :=
  detRun (addModStep p a b) fun _ => ()

/-- The contract of `addModRun` over limb arrays: the limb at `a` becomes `addModL p r s`,
    the limb at `b` is kept, and only the range of the limb at `a` is written. -/
theorem addMod_limbs_contract (p : Nat) (a b : BitVec 64) :
    SContract (addModRun p a b)
      (ContractSpec.binOp (limbsAt a) (limbsAt b) (addModL p)
        (fun _ _ => (⟨a, 8⟩ : Rng 64).toSet) fun _ _ => True) := by
  refine sContract_detRun_iff.2 ⟨?_, fun _ m _ => writesIn_writeLE 8 a _ m, fun _ _ _ _ _ _ _ => rfl⟩
  rintro ⟨r, s⟩ m ⟨hd, ⟨-, hr, hlr⟩, ⟨-, hs, hls⟩⟩
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hlr
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 hls
  have hrx : readLE 8 m a = x := by simpa using hr.2.1
  have hsy : readLE 8 m b = y := by simpa using hs.2.1
  have hab : (⟨b, 8⟩ : Rng 64).Disj ⟨a, 8⟩ := by
    refine Rng.disj_of_disjoint (Nat.succ_pos _) (Nat.succ_pos _) ?_
    have := hd.symm
    simpa [limbsAt, arrAt, emp] using this
  refine ⟨hd, ⟨Set.disjoint_empty _, ⟨Set.disjoint_empty _, ?_, trivial⟩, rfl⟩,
    ⟨Set.disjoint_empty _, ⟨Set.disjoint_empty _, ?_, trivial⟩, rfl⟩⟩
  · simp only [addModStep, hrx, hsy, List.headD_cons]
    simpa using readLE_writeLE_same 8 m a (BitVec.ofNat 64 ((x.toNat + y.toNat) % p))
      (Nat.le_of_ble_eq_true rfl)
  · show readLE 8 _ (b + BitVec.ofNat 64 (8 * 0)) = y
    simpa [addModStep, hsy] using readLE_writeLE_disj (n := 8) m (a := b) (b := a)
      (BitVec.ofNat 64 (((readLE 8 m a).toNat + (readLE 8 m b).toNat) % p)) hab

/-- **The contract of `addModRun` over `ZMod p`**, by `SContract.transfer` from
    `addMod_limbs_contract` along the square `addModL_related`: the representation at `a`
    of `x` becomes that of `x + y`, and the representation at `b` of `y` is kept. -/
theorem addMod_zmod_contract (p : Nat) [NeZero p] (hp : p ≤ 2 ^ 64) (a b : BitVec 64) :
    SContract (addModRun p a b)
      ⟨fun xy : ZMod p × ZMod p => repAt 8 a (limb1 p) xy.1 ∗ repAt 8 b (limb1 p) xy.2,
        fun xy => repAt 8 a (limb1 p) (xy.1 + xy.2) ∗ repAt 8 b (limb1 p) xy.2,
        fun _ _ => (⟨a, 8⟩ : Rng 64).toSet, fun _ _ => True⟩ := by
  have := addModL_related p hp
  refine (SContract.transfer (enc := limb1 p) (op := (· + ·))
    (addMod_limbs_contract p a b)).conseq (fun _ => ?_) (fun _ => ?_)
    (fun _ _ _ => subset_rfl) fun _ _ h => h
  · dsimp only [ContractSpec.binOp, limbsAt]
    sep_cancel
  · dsimp only [ContractSpec.binOp, limbsAt]
    sep_cancel

end AddMod

end CatCrypt.Crypto.SecureCompilation.SepLogic
