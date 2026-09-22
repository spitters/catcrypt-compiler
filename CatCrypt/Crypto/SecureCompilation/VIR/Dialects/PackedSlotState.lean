/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Fixed-width slot state packed into one natural number

A finite map from slot indices to natural numbers, carried as a single `Nat`
with slot `i` occupying bits `w * i`. A slot holds `x + 1` for a mapped index
and `0` for an unmapped one, so `0` is the empty state.

Reading a slot is a shift and a modulus; writing one is a shift, a subtraction,
a shift and an addition, independent of how many slots are live. An association
list keyed by slot pays a linear scan to read and rebuilds the whole list to
write.

The slot operations are stated with `>>>` and `<<<`, which the kernel reduces
on the accelerated `Nat` representation, and characterised immediately in terms
of `/` and `%`, in which the remaining proofs are ordinary arithmetic.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.PackedSlotState

set_option autoImplicit false

/-- Bits per slot. A slot holds a node index plus one, so the representable
    range is `2 ^ w - 1` indices. -/
def w : Nat := 32

/-- The slot radix. -/
def B : Nat := 2 ^ w

theorem B_pos : 0 < B := Nat.two_pow_pos w

/-- The raw content of slot `i`: the mapped value plus one, or zero. -/
def praw (σ i : Nat) : Nat := (σ >>> (w * i)) % B

/-- The value at slot `i`, or `none` when the slot is unmapped. -/
def pget (σ i : Nat) : Option Nat :=
  match praw σ i with
  | 0 => none
  | v + 1 => some v

/-- Replace slot `i` by `x`, leaving every other slot unchanged. -/
def pset (σ i x : Nat) : Nat :=
  σ - (praw σ i <<< (w * i)) + ((x + 1) <<< (w * i))

/-! ## The arithmetic characterisation -/

theorem praw_eq (σ i : Nat) : praw σ i = σ / 2 ^ (w * i) % B := by
  simp [praw, Nat.shiftRight_eq_div_pow]

theorem shiftLeft_eq (a s : Nat) : a <<< s = a * 2 ^ s := by
  simp [Nat.shiftLeft_eq]

theorem pset_eq (σ i x : Nat) :
    pset σ i x = σ - (σ / 2 ^ (w * i) % B) * 2 ^ (w * i) + (x + 1) * 2 ^ (w * i) := by
  simp [pset, praw_eq, shiftLeft_eq]

/-- The isolated slot never exceeds the state it came from, so the subtraction
    in `pset` does not truncate. -/
theorem slot_le (σ i : Nat) : (σ / 2 ^ (w * i) % B) * 2 ^ (w * i) ≤ σ := by
  calc (σ / 2 ^ (w * i) % B) * 2 ^ (w * i)
      ≤ (σ / 2 ^ (w * i)) * 2 ^ (w * i) :=
        Nat.mul_le_mul_right _ (Nat.mod_le _ _)
    _ ≤ σ := Nat.div_mul_le_self _ _

/-- A state written out around slot `i`: the slots above it, the slot itself,
    and the slots below it. -/
theorem split_at (σ i : Nat) :
    σ = (σ / 2 ^ (w * i) / B) * (B * 2 ^ (w * i))
      + (σ / 2 ^ (w * i) % B) * 2 ^ (w * i) + σ % 2 ^ (w * i) := by
  have h1 : σ / 2 ^ (w * i) = (σ / 2 ^ (w * i) / B) * B + σ / 2 ^ (w * i) % B :=
    (Nat.div_add_mod _ _).symm.trans (by rw [Nat.mul_comm])
  calc σ = σ / 2 ^ (w * i) * 2 ^ (w * i) + σ % 2 ^ (w * i) := by
            rw [Nat.div_add_mod']
    _ = ((σ / 2 ^ (w * i) / B) * B + σ / 2 ^ (w * i) % B) * 2 ^ (w * i)
          + σ % 2 ^ (w * i) := by rw [← h1]
    _ = _ := by ring

/-- `pset` with the unchanged parts of the state exposed. -/
theorem pset_split (σ i x : Nat) :
    pset σ i x = (σ / 2 ^ (w * i) / B) * (B * 2 ^ (w * i))
      + (x + 1) * 2 ^ (w * i) + σ % 2 ^ (w * i) := by
  have hs := split_at σ i
  have hle := slot_le σ i
  rw [pset_eq]
  omega

/-! ## Slot boundaries -/

theorem two_pow_succ_slot (i : Nat) : 2 ^ (w * (i + 1)) = B * 2 ^ (w * i) := by
  rw [B, Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]

/-- A slot content read as the low part above the slot boundary. -/
theorem praw_eq_mod (σ i : Nat) : praw σ i = σ % 2 ^ (w * (i + 1)) / 2 ^ (w * i) := by
  rw [praw_eq, two_pow_succ_slot, Nat.mul_comm B, Nat.mod_mul_right_div_self]

/-- The part of the state at and below slot `i` is smaller than the boundary
    above it. -/
theorem lowpart_lt (i e lo : Nat) (he : e < B) (hlo : lo < 2 ^ (w * i)) :
    e * 2 ^ (w * i) + lo < 2 ^ (w * (i + 1)) := by
  rw [two_pow_succ_slot]
  calc e * 2 ^ (w * i) + lo
      < e * 2 ^ (w * i) + 2 ^ (w * i) := by omega
    _ = (e + 1) * 2 ^ (w * i) := by ring
    _ ≤ B * 2 ^ (w * i) := Nat.mul_le_mul_right _ he

/-! ## `pset` leaves every other slot alone -/

/-- Below slot `i`, `pset` changes nothing. -/
theorem pset_mod (σ i x : Nat) : pset σ i x % 2 ^ (w * i) = σ % 2 ^ (w * i) := by
  have hL : pset σ i x % 2 ^ (w * i) = σ % 2 ^ (w * i) % 2 ^ (w * i) := by
    rw [pset_split]
    have h : (σ / 2 ^ (w * i) / B) * (B * 2 ^ (w * i)) + (x + 1) * 2 ^ (w * i)
          + σ % 2 ^ (w * i)
        = σ % 2 ^ (w * i) + ((σ / 2 ^ (w * i) / B) * B + (x + 1)) * 2 ^ (w * i) := by ring
    rw [h, Nat.add_mul_mod_self_right]
  rw [hL, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]

/-- Above slot `i`, `pset` changes nothing. -/
theorem pset_div (σ i x : Nat) (hx : x + 1 < B) :
    pset σ i x / 2 ^ (w * (i + 1)) = σ / 2 ^ (w * (i + 1)) := by
  have hlo : σ % 2 ^ (w * i) < 2 ^ (w * i) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hd : σ / 2 ^ (w * i) % B < B := Nat.mod_lt _ B_pos
  have e1 : pset σ i x
      = (x + 1) * 2 ^ (w * i) + σ % 2 ^ (w * i)
        + (σ / 2 ^ (w * i) / B) * 2 ^ (w * (i + 1)) := by
    rw [pset_split, two_pow_succ_slot]; ring
  have e2 : σ
      = (σ / 2 ^ (w * i) % B) * 2 ^ (w * i) + σ % 2 ^ (w * i)
        + (σ / 2 ^ (w * i) / B) * 2 ^ (w * (i + 1)) := by
    conv_lhs => rw [split_at σ i]
    rw [two_pow_succ_slot]; ring
  rw [e1, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (lowpart_lt i (x + 1) _ hx hlo)]
  conv_rhs => rw [e2]
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (lowpart_lt i _ _ hd hlo)]

/-! ## Reading back -/

/-- A state written out as slots above, the slot itself, and slots below reads
    back at that slot as the value it was written with. -/
theorem praw_of_split (A e lo i : Nat) (he : e < B) (hlo : lo < 2 ^ (w * i)) :
    praw (A * (B * 2 ^ (w * i)) + e * 2 ^ (w * i) + lo) i = e := by
  have hv : A * (B * 2 ^ (w * i)) + e * 2 ^ (w * i) + lo
      = lo + (A * B + e) * 2 ^ (w * i) := by ring
  have hm : (A * B + e) % B = e := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he]
  rw [praw_eq, hv, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlo, Nat.zero_add, hm]

theorem praw_pset_self (σ i x : Nat) (hx : x + 1 < B) : praw (pset σ i x) i = x + 1 := by
  rw [pset_split]
  exact praw_of_split _ _ _ _ hx (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem praw_pset_of_lt (σ i j x : Nat) (h : j < i) :
    praw (pset σ i x) j = praw σ j := by
  have hdvd : (2 : Nat) ^ (w * (j + 1)) ∣ 2 ^ (w * i) :=
    Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left w h)
  rw [praw_eq_mod, praw_eq_mod,
    ← Nat.mod_mod_of_dvd (pset σ i x) hdvd, ← Nat.mod_mod_of_dvd σ hdvd, pset_mod]

theorem praw_pset_of_gt (σ i j x : Nat) (h : i < j) (hx : x + 1 < B) :
    praw (pset σ i x) j = praw σ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
  have hpow : (2 : Nat) ^ (w * (i + 1 + k)) = 2 ^ (w * (i + 1)) * 2 ^ (w * k) := by
    rw [← Nat.pow_add, Nat.mul_add]
  rw [praw_eq, praw_eq, hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    pset_div σ i x hx]

theorem praw_pset_ne (σ i j x : Nat) (h : i ≠ j) (hx : x + 1 < B) :
    praw (pset σ i x) j = praw σ j := by
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact praw_pset_of_lt σ i j x hlt
  · exact praw_pset_of_gt σ i j x (by omega) hx

/-- Writing a slot and reading it back gives what was written. -/
theorem pget_pset_self (σ i x : Nat) (hx : x + 1 < B) : pget (pset σ i x) i = some x := by
  rw [pget, praw_pset_self σ i x hx]

/-- Writing one slot leaves every other slot readable as before. -/
theorem pget_pset_ne (σ i j x : Nat) (h : i ≠ j) (hx : x + 1 < B) :
    pget (pset σ i x) j = pget σ j := by
  rw [pget, pget, praw_pset_ne σ i j x h hx]

/-- The empty state maps nothing. -/
theorem pget_zero (i : Nat) : pget 0 i = none := by
  rw [pget, praw_eq, Nat.zero_div, Nat.zero_mod]

/-! ## Representing a finite map

A packed state stands for a map `α → Option Nat` through an enumeration
`idx : α → Nat` of the locations a program touches. Nothing here bounds `idx`:
the slot operations are total, so the enumeration's size does not enter, and
the only side condition is on the stored value.

The enumeration need be injective only on the locations in play, which is what
`InjOnP` says. An enumeration built from a duplicate-free list has that
property, by `injOnP_idxOf`.
-/

section Represents

variable {α : Type}

/-- `idx` is injective on the locations satisfying `P`. -/
def InjOnP (idx : α → Nat) (P : α → Prop) : Prop :=
  ∀ a b, P a → P b → idx a = idx b → a = b

/-- The packed state `σ` represents `f` at every location satisfying `P`. -/
def Represents (idx : α → Nat) (P : α → Prop) (σ : Nat) (f : α → Option Nat) : Prop :=
  ∀ d, P d → f d = pget σ (idx d)

/-- The empty state represents the everywhere-unmapped map. -/
theorem represents_zero (idx : α → Nat) (P : α → Prop) :
    Represents idx P 0 (fun _ => none) :=
  fun d _ => (pget_zero (idx d)).symm

/-- Writing one location through the enumeration represents updating the map at
    that location. -/
theorem Represents.set [DecidableEq α] {idx : α → Nat} {P : α → Prop}
    (hinj : InjOnP idx P) {σ : Nat} {f : α → Option Nat}
    (h : Represents idx P σ f) (d : α) (hd : P d) (x : Nat) (hx : x + 1 < B) :
    Represents idx P (pset σ (idx d) x) (fun e => if e = d then some x else f e) := by
  intro e he
  by_cases hed : e = d
  · subst hed
    rw [pget_pset_self _ _ _ hx]
    simp
  · simp only [if_neg hed]
    rw [pget_pset_ne σ (idx d) (idx e) x (fun hi => hed (hinj e d he hd hi.symm)) hx]
    exact h e he

/-- Reading a represented location. -/
theorem Represents.get {idx : α → Nat} {P : α → Prop} {σ : Nat} {f : α → Option Nat}
    (h : Represents idx P σ f) (d : α) (hd : P d) : pget σ (idx d) = f d :=
  (h d hd).symm

/-- A location's position in a list enumerates it injectively on that list's
    members. Duplicates do no harm: the position is that of the first
    occurrence. -/
theorem injOnP_idxOf [BEq α] [LawfulBEq α] (locs : List α) :
    InjOnP (fun a => locs.idxOf a) (fun a => a ∈ locs) :=
  fun _ _ ha _ hab => (List.idxOf_inj ha).mp hab

end Represents

end CatCrypt.Crypto.SecureCompilation.VIR.PackedSlotState
