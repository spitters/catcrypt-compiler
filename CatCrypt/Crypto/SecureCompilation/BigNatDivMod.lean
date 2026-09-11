/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigNatCompare
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivQrFrontEmit

/-!
# Euclidean division and modulo on the `BigNat` carrier

Carrier-level `div` and `mod` on the little-endian limb-list carrier
`bignumVal`, matching Lean's `Nat.div` (`÷0 → 0`) and `Nat.mod` (`%0 → x`).
The quotient and remainder are read out of the verified multi-limb Knuth
Algorithm D loop invariant (`MpnDivQrFrontEmit.kdFold_div_qr`): after all `qn`
digit steps the quotient window `Q` and remaining window `R` satisfy
`Q · D + R = X` with `R < D` and `D > 0`. Euclidean uniqueness turns that into
`Q = X / D` and `R = X % D`.

## Main results

* `div_of_euclid`, `mod_of_euclid` — Euclidean uniqueness at the `Nat` level:
  `Q · D + R = X` with `R < D` forces `X / D = Q` and `X % D = R`.
* `ofListMem`, `cells_ofListMem`, `cells_ofListMem_full`,
  `bignumVal_segCells_zeroBase` — a memref of a fixed width holding a carrier
  list in its low cells (rest zero), and how `cells` / `segCells` read it back.
* `carrier_div_of_kdFold` — the quotient window and remainder window of the
  Knuth-D fold, read through the memref adapter, are `bignumVal a / bignumVal b`
  and `bignumVal a % bignumVal b` when `0 < bignumVal b`.
* `div`, `mod` and `div_val`, `mod_val` — the carrier operations and their value
  specs `bignumVal (div a b) = bignumVal a / bignumVal b` and
  `bignumVal (mod a b) = bignumVal a % bignumVal b`, for arbitrary `b`
  (including `bignumVal b = 0`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatDivMod

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_lt)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells cells_length)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (segCells segCells_cons)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivQrFrontEmit
  (kdFold kdFold_div_qr setSeg setSeg_get_ge segCells_setSeg cells_add bignumVal_append)
open CatCrypt.Crypto.SecureCompilation.BigNatCompare (segCells_zero)

/-! ## 1. Euclidean uniqueness at the `Nat` level -/

/-- Uniqueness of the quotient: `Q · D + R = X` with `R < D` forces `X / D = Q`. -/
theorem div_of_euclid {X D Q R : Nat} (hD : 0 < D) (h : Q * D + R = X) (hR : R < D) :
    X / D = Q := by
  rw [← h, Nat.mul_comm Q D, Nat.add_comm (D * Q) R, Nat.add_mul_div_left R Q hD,
    Nat.div_eq_of_lt hR, Nat.zero_add]

/-- Uniqueness of the remainder: `Q · D + R = X` with `R < D` forces `X % D = R`. -/
theorem mod_of_euclid {X D Q R : Nat} (h : Q * D + R = X) (hR : R < D) :
    X % D = R := by
  rw [← h, Nat.mul_comm Q D, Nat.add_comm (D * Q) R, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hR]

/-! ## 2. A memref holding a carrier list in its low cells

`ofListMem N l` writes `l` into cells `0, …, l.length - 1` of an all-zero
width-`N` memref. `cells` / `segCells` read it back: the low prefix is `l`, and
any segment at or above `l.length` is zero. -/

/-- A width-`N` memref whose first `l.length` cells hold `l` and whose remaining
    cells are zero. -/
def ofListMem (N : Nat) (l : List (BitVec 64)) : Fin N → BitVec 64 :=
  setSeg (fun _ => 0) 0 l

/-- Reading a runtime index of an all-zero memref returns zero. -/
theorem memGetDyn_const_zero {N : Nat} (k : Nat) :
    memGetDyn (fun _ : Fin N => (0 : BitVec 64)) k = 0 := by
  cases N with
  | zero => rfl
  | succ m => rfl

/-- The first `k` cells (`k ≤ l.length ≤ N`) of `ofListMem N l` are `l.take k`. -/
theorem cells_ofListMem (N : Nat) (l : List (BitVec 64)) (k : Nat)
    (hk : k ≤ l.length) (hN : l.length ≤ N) :
    cells (ofListMem N l) k = l.take k := by
  rw [← segCells_zero (ofListMem N l) k]
  show segCells (setSeg (fun _ => (0 : BitVec 64)) 0 l) 0 k = l.take k
  exact segCells_setSeg (fun _ => (0 : BitVec 64)) 0 l k hk (by omega)

/-- The first `l.length` cells of `ofListMem N l` recover `l`. -/
theorem cells_ofListMem_full (N : Nat) (l : List (BitVec 64)) (hN : l.length ≤ N) :
    cells (ofListMem N l) l.length = l := by
  rw [cells_ofListMem N l l.length (Nat.le_refl _) hN, List.take_length]

/-- A segment of `ofListMem N l` at or above `l.length` is all zeros, so its
    value is `0`. -/
theorem bignumVal_segCells_zeroBase (N : Nat) (l : List (BitVec 64)) :
    ∀ lo k : Nat, l.length ≤ lo → lo + k ≤ N →
      bignumVal (segCells (ofListMem N l) lo k) = 0 := by
  intro lo k
  induction k generalizing lo with
  | zero => intro _ _; simp [segCells, bignumVal]
  | succ m ih =>
      intro hge hb
      have h0 : memGetDyn (ofListMem N l) lo = 0 := by
        show memGetDyn (setSeg (fun _ => (0 : BitVec 64)) 0 l) lo = 0
        rw [setSeg_get_ge (fun _ => (0 : BitVec 64)) 0 l lo (by omega) (by omega)]
        exact memGetDyn_const_zero lo
      have hrec := ih (lo + 1) (by omega) (by omega)
      rw [segCells_cons, h0]
      simp only [bignumVal]
      rw [hrec]
      simp

/-! ## 3. Reading the Knuth-D fold as carrier div / mod

With `vp` holding the divisor `b` and `acc` holding the dividend `a` in a window
wide enough that `X = bignumVal a` stays below `D · 2^(64·qn)`, the Euclidean
contract `kdFold_div_qr` gives `Q · D + R = X` and `R < D`; uniqueness rewrites
the quotient and remainder windows as `X / D` and `X % D`. -/

/-- The quotient window and remainder window of the Knuth-D fold, read through
    the memref adapter, are the carrier `div` and `mod` values. -/
theorem carrier_div_of_kdFold {NW NV : Nat} (vp : Fin NV → BitVec 64)
    (acc : Fin NW → BitVec 64) (a b : List (BitVec 64))
    (qn vn qbase : Nat)
    (hqn : qn = a.length)
    (hqb : qn + vn ≤ qbase) (hNW : qbase + qn ≤ NW)
    (hD : bignumVal (cells vp vn) = bignumVal b)
    (hX : bignumVal (cells acc (qn + vn)) = bignumVal a)
    (hbpos : 0 < bignumVal b) :
    bignumVal (segCells (kdFold vp vn qbase qn qn acc) qbase qn) = bignumVal a / bignumVal b
      ∧ bignumVal (cells (kdFold vp vn qbase qn qn acc) vn) = bignumVal a % bignumVal b := by
  have hDpos : 0 < bignumVal (cells vp vn) := by rw [hD]; exact hbpos
  have hR0 : bignumVal (cells acc (qn + vn)) < bignumVal (cells vp vn) * (2 ^ 64) ^ qn := by
    rw [hX, hD, hqn]
    calc bignumVal a < (2 ^ 64) ^ a.length := bignumVal_lt a
      _ ≤ bignumVal b * (2 ^ 64) ^ a.length := Nat.le_mul_of_pos_left _ hbpos
  obtain ⟨heq, hlt⟩ := kdFold_div_qr vp vn qbase qn acc hqb hNW hDpos hR0
  rw [hD, hX] at heq
  rw [hD] at hlt
  exact ⟨(div_of_euclid hbpos heq hlt).symm, (mod_of_euclid heq hlt).symm⟩

/-! ## 4. The carrier operations -/

/-- Carrier Euclidean division: `÷0 → []` (value `0`), else the Knuth-D quotient
    window of the dividend `a` by the divisor `b`. -/
def div (a b : List (BitVec 64)) : List (BitVec 64) :=
  if bignumVal b = 0 then []
  else
    segCells
      (kdFold (ofListMem b.length b) b.length (a.length + b.length) a.length a.length
        (ofListMem (2 * a.length + b.length) a))
      (a.length + b.length) a.length

/-- Carrier modulo: `%0 → a`, else the Knuth-D remainder window of the dividend
    `a` by the divisor `b`. -/
def mod (a b : List (BitVec 64)) : List (BitVec 64) :=
  if bignumVal b = 0 then a
  else
    cells
      (kdFold (ofListMem b.length b) b.length (a.length + b.length) a.length a.length
        (ofListMem (2 * a.length + b.length) a))
      b.length

/-- The value equations for `div` and `mod` on the `0 < bignumVal b` branch. -/
theorem carrier_div_mod (a b : List (BitVec 64)) (hb : 0 < bignumVal b) :
    bignumVal (div a b) = bignumVal a / bignumVal b
      ∧ bignumVal (mod a b) = bignumVal a % bignumVal b := by
  have hbne : ¬ bignumVal b = 0 := by omega
  have hD : bignumVal (cells (ofListMem b.length b) b.length) = bignumVal b := by
    rw [cells_ofListMem_full b.length b (Nat.le_refl _)]
  have hX : bignumVal (cells (ofListMem (2 * a.length + b.length) a) (a.length + b.length))
      = bignumVal a := by
    rw [cells_add, bignumVal_append, cells_ofListMem_full (2 * a.length + b.length) a (by omega),
      bignumVal_segCells_zeroBase (2 * a.length + b.length) a a.length b.length
        (Nat.le_refl _) (by omega)]
    simp
  unfold div mod
  rw [if_neg hbne, if_neg hbne]
  exact carrier_div_of_kdFold (ofListMem b.length b) (ofListMem (2 * a.length + b.length) a)
    a b a.length b.length (a.length + b.length) rfl (by omega) (by omega) hD hX hb

/-- **Division value spec.** `bignumVal (div a b) = bignumVal a / bignumVal b`
    for arbitrary `b`, including `bignumVal b = 0` (both sides `0`). -/
theorem div_val (a b : List (BitVec 64)) :
    bignumVal (div a b) = bignumVal a / bignumVal b := by
  rcases Nat.eq_zero_or_pos (bignumVal b) with h0 | hpos
  · unfold div
    rw [if_pos h0, h0, Nat.div_zero]
    simp [bignumVal]
  · exact (carrier_div_mod a b hpos).1

/-- **Modulo value spec.** `bignumVal (mod a b) = bignumVal a % bignumVal b`
    for arbitrary `b`, including `bignumVal b = 0` (`mod a b = a`). -/
theorem mod_val (a b : List (BitVec 64)) :
    bignumVal (mod a b) = bignumVal a % bignumVal b := by
  rcases Nat.eq_zero_or_pos (bignumVal b) with h0 | hpos
  · unfold mod
    rw [if_pos h0, h0, Nat.mod_zero]
  · exact (carrier_div_mod a b hpos).2

end CatCrypt.Crypto.SecureCompilation.BigNatDivMod
