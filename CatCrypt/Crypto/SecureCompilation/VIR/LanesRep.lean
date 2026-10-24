/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc

/-!
# Signed lanes and stack arrays

A signed `w`-bit word `x` represents `a : ZMod q` with bound `B` and factor `κ` when
`|x.toInt| ≤ B` and `x.toInt · κ = a` modulo `q` (`SRep`). The factor is `1` for a plain
signed reading and `2 ^ w` for the output of a Montgomery reduction. The lift to `n` lanes
(`LanesRep`) relates a valuation of the lane context `Ctxs w n` to a coefficient vector
`Fin n → ZMod q` cellwise, with a bound per lane; the lift to arrays (`ArrRep`) relates a
`stackArr w n` value to the same vector through its cells. A lanes valuation and an array
holding the same cells are related to the same coefficients (`lanesRep_iff_arrRep`).

The word theorems of `basemulProgW` and `accProgW` restate under `LanesRep`: input lanes
related to the operand rows at factor `1` give output lanes related to the ring-level
product at factor `2 ^ w`. `LanesRepFamily` packages the relation as a `RepFamily`.

## Main definitions

* `SRep`, `LanesRep`, `ArrRep`: the signed representation of a word, of a lanes valuation
  and of a stack array.
* `arrLanes`: the lanes valuation of the cells of a stack array.
* `row1`: a coefficient vector as a residue array with one modulus.
* `pairCoeffs`, `rowCoeffs`, `rowBound`: the coefficient vectors and input bounds of the
  lane layouts of `basemulProgW` and `accProgW`.

## Main results

* `SRep.mono`, `LanesRep.mono`: monotonicity in the bound.
* `lanesRep_iff_arrRep`, `lanesRep_arrLanes_iff`: a lanes valuation and a stack array with
  the same cells are related to the same coefficients.
* `basemulProgW_rel`: on input lanes representing the operand pair `(x, y)` with factor `1`
  and bound `inB`, the output lanes of `basemulProgW` represent `basemulF` of `x`, `y` with
  factor `2 ^ w` and bound `outB`.
* `accProgW_rel`: the same for `accProgW`, the input bound `inA` on the first row and `inB`
  on the second, the output `∑_j basemulF (x j) (y j)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SignedLanes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc
open CatCrypt.Crypto.SecureCompilation.VIR.RingDialect (Limbs basemulF)
open Finset (range)

/-! ## 1. Signed words, lanes and arrays -/

/-- **The signed representation.** The `w`-bit word `x` represents `a` with bound `B` and
factor `κ`: `|x.toInt| ≤ B` and `x.toInt · κ = a` modulo `q`. -/
def SRep (q w : ℕ) (κ : ZMod q) (B : ℕ) (a : ZMod q) (x : BitVec w) : Prop :=
  |x.toInt| ≤ B ∧ ((x.toInt : ℤ) : ZMod q) * κ = a

theorem SRep.mono {q w : ℕ} {κ : ZMod q} {B B' : ℕ} {a : ZMod q} {x : BitVec w}
    (h : SRep q w κ B a x) (hB : B ≤ B') : SRep q w κ B' a x :=
  ⟨h.1.trans (by exact_mod_cast hB), h.2⟩

/-- **The lanes representation.** Lane `i` of the valuation `W` of `Ctxs w n` represents
coefficient `i` with bound `B i` and factor `κ`. -/
def LanesRep (q w : ℕ) (κ : ZMod q) (B : ℕ → ℕ) {n : ℕ} (a : Fin n → ZMod q)
    (W : Valuation (Ctxs w n)) : Prop :=
  ∀ i : Fin n, SRep q w κ (B i) (a i) (hvGetG (Rw w) (0 : BitVec w) W i)

theorem LanesRep.mono {q w : ℕ} {κ : ZMod q} {B B' : ℕ → ℕ} {n : ℕ} {a : Fin n → ZMod q}
    {W : Valuation (Ctxs w n)} (h : LanesRep q w κ B a W) (hB : ∀ i, i < n → B i ≤ B' i) :
    LanesRep q w κ B' a W :=
  fun i => (h i).mono (hB i i.2)

/-- **The array representation.** Cell `i` of the stack array `A` represents coefficient `i`
with bound `B i` and factor `κ`. -/
def ArrRep (q w : ℕ) (κ : ZMod q) (B : ℕ → ℕ) {n : ℕ} (a : Fin n → ZMod q)
    (A : ⟦(JasminTy.stackArr w n : JasminTy)⟧) : Prop :=
  ∀ i : Fin n, SRep q w κ (B i) (a i) (A i)

/-- **Lanes and arrays.** A lanes valuation and a stack array holding the same cells are
related to the same coefficients. -/
theorem lanesRep_iff_arrRep {q w : ℕ} {κ : ZMod q} {B : ℕ → ℕ} {n : ℕ} {a : Fin n → ZMod q}
    {W : Valuation (Ctxs w n)} {A : ⟦(JasminTy.stackArr w n : JasminTy)⟧}
    (h : ∀ i : Fin n, hvGetG (Rw w) (0 : BitVec w) W i = A i) :
    LanesRep q w κ B a W ↔ ArrRep q w κ B a A := by
  refine forall_congr' fun i => ?_
  rw [h i]

/-- The lanes valuation of the cells of a stack array. -/
def arrLanes {w n : ℕ} (A : ⟦(JasminTy.stackArr w n : JasminTy)⟧) : Valuation (Ctxs w n) :=
  lanesVal (Rw w) (fun j => stackGet A j) n 0

theorem hvGetG_arrLanes {w n : ℕ} (A : ⟦(JasminTy.stackArr w n : JasminTy)⟧) (i : Fin n) :
    hvGetG (Rw w) (0 : BitVec w) (arrLanes A) i = A i := by
  rw [arrLanes, hvGetG_lanesVal _ _ _ n 0 i i.2, Nat.zero_add]
  exact stackGet_id A i

/-- A stack array is related to the coefficients its lanes valuation is related to. -/
theorem lanesRep_arrLanes_iff {q w : ℕ} {κ : ZMod q} {B : ℕ → ℕ} {n : ℕ}
    {a : Fin n → ZMod q} (A : ⟦(JasminTy.stackArr w n : JasminTy)⟧) :
    LanesRep q w κ B a (arrLanes A) ↔ ArrRep q w κ B a A :=
  lanesRep_iff_arrRep (hvGetG_arrLanes A)

/-- Every lanes valuation is the lanes valuation of its own cells. -/
theorem eq_lanesVal_self {w n : ℕ} (W : Valuation (Ctxs w n)) :
    W = lanesVal (Rw w) (fun j => hvGetG (Rw w) (0 : BitVec w) W j) n 0 :=
  eq_lanesVal (Rw w) (0 : BitVec w) _ n 0 W fun i _ => by rw [Nat.zero_add]

/-! ## 2. The lane layouts of the base multiplication and the accumulation -/

/-- A coefficient vector as the single row of a residue array with one modulus. -/
def row1 {q n : ℕ} (f : Fin n → ZMod q) : Limbs [q] n := fun r t =>
  match r with
  | ⟨0, _⟩ => f t

/-- The input coefficients of `basemulProgW`: the first operand on lanes `0, …, N − 1`, the
second on `N, …, 2 N − 1`. -/
def pairCoeffs {q N : ℕ} (x y : Limbs [q] N) : Fin (2 * N) → ZMod q := fun j =>
  if h : (j : ℕ) < N then x ⟨0, by simp⟩ ⟨j, h⟩ else y ⟨0, by simp⟩ ⟨j - N, by omega⟩

/-- The input coefficients of `accProgW` at `N = 2 ^ logN`: operand `j` of the first row on
lanes `j N, …, j N + N − 1`, operand `j` of the second row on lanes `k N + j N, …`. -/
def rowCoeffs {q : ℕ} (k logN : ℕ) (x y : ℕ → Limbs [q] (2 ^ logN)) :
    Fin (2 * k * 2 ^ logN) → ZMod q := fun m =>
  if (m : ℕ) < k * 2 ^ logN then
    x (m / 2 ^ logN) ⟨0, by simp⟩ ⟨m % 2 ^ logN, Nat.mod_lt _ (Nat.two_pow_pos logN)⟩
  else
    y ((m - k * 2 ^ logN) / 2 ^ logN) ⟨0, by simp⟩
      ⟨(m - k * 2 ^ logN) % 2 ^ logN, Nat.mod_lt _ (Nat.two_pow_pos logN)⟩

/-- The input bounds of `accProgW`: `A` on the first `k N` lanes, `B` on the rest. -/
def rowBound (k N A B : ℕ) (m : ℕ) : ℕ := if m < k * N then A else B

theorem idx_div_mod {N j t : ℕ} (hN : 0 < N) (ht : t < N) :
    (j * N + t) / N = j ∧ (j * N + t) % N = t := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

theorem rowCoeffs_fst {q : ℕ} (k logN : ℕ) (x y : ℕ → Limbs [q] (2 ^ logN)) {j t : ℕ}
    (hj : j < k) (ht : t < 2 ^ logN) (h : j * 2 ^ logN + t < 2 * k * 2 ^ logN) :
    rowCoeffs k logN x y ⟨j * 2 ^ logN + t, h⟩ = x j ⟨0, by simp⟩ ⟨t, ht⟩ := by
  obtain ⟨e1, e2⟩ := idx_div_mod (j := j) (Nat.two_pow_pos logN) ht
  simp only [rowCoeffs, ite_eq_left (idx_lt hj ht), e1, e2]

theorem rowCoeffs_snd {q : ℕ} (k logN : ℕ) (x y : ℕ → Limbs [q] (2 ^ logN)) {j t : ℕ}
    (ht : t < 2 ^ logN) (h : k * 2 ^ logN + j * 2 ^ logN + t < 2 * k * 2 ^ logN) :
    rowCoeffs k logN x y ⟨k * 2 ^ logN + j * 2 ^ logN + t, h⟩ = y j ⟨0, by simp⟩ ⟨t, ht⟩ := by
  obtain ⟨e1, e2⟩ := idx_div_mod (j := j) (Nat.two_pow_pos logN) ht
  have e0 : k * 2 ^ logN + j * 2 ^ logN + t - k * 2 ^ logN = j * 2 ^ logN + t := by omega
  simp only [rowCoeffs, ite_eq_right (show ¬ k * 2 ^ logN + j * 2 ^ logN + t < k * 2 ^ logN by omega),
    e0, e1, e2]

/-! ## 3. The lane theorems under the relation -/

/-- **The base multiplication under the lanes relation.** On input lanes representing the
operand pair `(x, y)` with factor `1` and bound `inB`, the output lanes of `basemulProgW`
represent `basemulF` of `x`, `y` at `L = logN − 1` with factor `2 ^ w` and bound `outB`. -/
theorem basemulProgW_rel (S : BasemulSched) (hS : S.Ok) (psi logN : ℕ) (hlog : 0 < logN)
    (x y : Limbs [S.q] (2 ^ logN)) (W : Valuation (Ctxs S.w (2 * 2 ^ logN)))
    (hW : LanesRep S.q S.w 1 (fun _ => S.inB) (pairCoeffs x y) W) :
    LanesRep S.q S.w ((2 ^ S.w : ℕ) : ZMod S.q) (fun _ => S.outB)
      (fun i => basemulF logN (logN - 1) [psi] x y ⟨0, by simp⟩ i)
      ((basemulProgW S psi logN).denote W) := by
  have hg : ∀ j, j < 2 * 2 ^ logN →
      |(hvGetG (Rw S.w) (0 : BitVec S.w) W j).toInt| ≤ S.inB :=
    fun j hj => (hW ⟨j, hj⟩).1
  have hx : ∀ j (hj : j < 2 ^ logN), x ⟨0, by simp⟩ ⟨j, hj⟩
      = ((hvGetG (Rw S.w) (0 : BitVec S.w) W j).toInt : ZMod S.q) := fun j hj => by
    have := (hW ⟨j, by omega⟩).2
    rw [mul_one] at this
    rw [this]
    simp [pairCoeffs, hj]
  have hy : ∀ j (hj : j < 2 ^ logN), y ⟨0, by simp⟩ ⟨j, hj⟩
      = ((hvGetG (Rw S.w) (0 : BitVec S.w) W (2 ^ logN + j)).toInt : ZMod S.q) := fun j hj => by
    have := (hW ⟨2 ^ logN + j, by omega⟩).2
    rw [mul_one] at this
    rw [this]
    simp [pairCoeffs]
  rw [eq_lanesVal_self W]
  intro i
  exact ⟨(basemulProgW_denote S hS psi logN hlog _ hg i i.2).1,
    basemulProgW_basemulF S hS psi logN hlog _ hg x y hx hy i i.2⟩

/-- **The row accumulation under the lanes relation.** On input lanes representing the rows
`x`, `y` with factor `1`, bound `inA` on the first row and `inB` on the second, the output
lanes of `accProgW` represent `∑_{j < k} basemulF (x j) (y j)` at `L = logN − 1` with
factor `2 ^ w` and bound `outB`. -/
theorem accProgW_rel (S : AccSched) (k : ℕ) (hS : S.Ok k) (psi logN : ℕ) (hlog : 0 < logN)
    (hk : 0 < k) (x y : ℕ → Limbs [S.q] (2 ^ logN))
    (W : Valuation (Ctxs S.w (2 * k * 2 ^ logN)))
    (hW : LanesRep S.q S.w 1 (rowBound k (2 ^ logN) S.inA S.inB) (rowCoeffs k logN x y) W) :
    LanesRep S.q S.w ((2 ^ S.w : ℕ) : ZMod S.q) (fun _ => S.outB)
      (fun i => ∑ j ∈ range k, basemulF logN (logN - 1) [psi] (x j) (y j) ⟨0, by simp⟩ i)
      ((accProgW S k psi logN).denote W) := by
  have hlt1 : ∀ j t, j < k → t < 2 ^ logN → j * 2 ^ logN + t < 2 * k * 2 ^ logN :=
    fun j t hj ht => by have := idx_lt hj ht; rw [Nat.mul_assoc]; omega
  have hlt2 : ∀ j t, j < k → t < 2 ^ logN →
      k * 2 ^ logN + j * 2 ^ logN + t < 2 * k * 2 ^ logN :=
    fun j t hj ht => by have := idx_lt hj ht; rw [Nat.mul_assoc]; omega
  have hA : ∀ j t, j < k → t < 2 ^ logN →
      |(hvGetG (Rw S.w) (0 : BitVec S.w) W (j * 2 ^ logN + t)).toInt| ≤ S.inA :=
    fun j t hj ht => by
      have := (hW ⟨_, hlt1 j t hj ht⟩).1
      simpa [rowBound, idx_lt hj ht] using this
  have hB : ∀ j t, j < k → t < 2 ^ logN →
      |(hvGetG (Rw S.w) (0 : BitVec S.w) W (k * 2 ^ logN + j * 2 ^ logN + t)).toInt|
        ≤ S.inB :=
    fun j t hj ht => by
      have := (hW ⟨_, hlt2 j t hj ht⟩).1
      have hn : ¬ k * 2 ^ logN + j * 2 ^ logN + t < k * 2 ^ logN := by omega
      simpa [rowBound, hn] using this
  have hx : ∀ j t (ht : t < 2 ^ logN), j < k → x j ⟨0, by simp⟩ ⟨t, ht⟩
      = ((hvGetG (Rw S.w) (0 : BitVec S.w) W (j * 2 ^ logN + t)).toInt : ZMod S.q) :=
    fun j t ht hj => by
      have := (hW ⟨_, hlt1 j t hj ht⟩).2
      rw [mul_one, rowCoeffs_fst k logN x y hj ht] at this
      exact this.symm
  have hy : ∀ j t (ht : t < 2 ^ logN), j < k → y j ⟨0, by simp⟩ ⟨t, ht⟩
      = ((hvGetG (Rw S.w) (0 : BitVec S.w) W (k * 2 ^ logN + j * 2 ^ logN + t)).toInt
        : ZMod S.q) :=
    fun j t ht hj => by
      have := (hW ⟨_, hlt2 j t hj ht⟩).2
      rw [mul_one, rowCoeffs_snd k logN x y ht] at this
      exact this.symm
  rw [eq_lanesVal_self W]
  intro i
  exact ⟨(accProgW_denote S k hS psi logN hlog hk _ hA hB i i.2).1,
    accProgW_basemulF S k hS psi logN hlog hk _ hA hB x y hx hy i i.2⟩

end CatCrypt.Crypto.SecureCompilation.VIR.SignedLanes
