/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Basis
public import CatCrypt.Quantum.TensorProduct

/-!
# Complex ball arithmetic in fixed-point dyadics

A `CBall` is a closed disc of the complex plane stored in fixed point: the centre is a pair of
integer mantissas and the radius a natural mantissa, all read at a scale `2^-e`. At the
working precision `prec = 64` (`Mem`, which is `MemAt prec`) the ball `⟨a, b, r⟩` is the disc
of centre `(a + b·i) / 2^64` and radius `r / 2^64`. No operation normalises a fraction: sums
are sums of integers, and the exact product `mulX` of balls at the scales `2^-e₁` and `2^-e₂`
is a ball at the scale `2^-(e₁+e₂)`, which `shift` brings back to the scale `2^-e` by floor
division of the centre by `2^64`, adding the remainders to the radius and rounding the radius
up. The operations are sound: if `z` lies in `A` and `w` in `B`, then `z + w`, `z - w`,
`z * w` lie in `add A B`, `sub A B`, `mul A B` (`mem_add`, `mem_sub`, `mem_mul`).

A `BMat k` is a `k × k` matrix of balls, stored as nested vectors so that it is data rather
than a closure; `MemM A B` says each entry of the complex matrix `A` lies in the ball of `B`
at the same place. An entry of a product is the sum of the exact products at the scale
`2^-128`, shifted once to the working scale.

The bound `bnorm B` is a rational upper bound on the `ℓ²` operator norm of every matrix with
entries in `B` (`norm_le_bnorm`): the operator norm is at most the sum of the moduli of the
entries, since every matrix unit has operator norm at most one.

## Main definitions

* `prec`, `CBall`, `CBall.MemAt`, `CBall.Mem`, `CBall.add`, `CBall.sub`, `CBall.neg`,
  `CBall.mulX`, `CBall.shift`, `CBall.mul`, `CBall.ofQ`, `CBall.widen`.
* `BMat`, `BMat.MemM`, `BMat.mul`, `BMat.sub`, `BMat.smul`, `BMat.kron`, `BMat.bnorm`.

## Main results

* `CBall.mem_add`, `CBall.mem_sub`, `CBall.mem_mulX`, `CBall.mem_shift`, `CBall.mem_mul`,
  `CBall.mem_ofQ`, `CBall.mem_widen` — soundness of the ball operations.
* `BMat.memM_mul`, `BMat.memM_sub`, `BMat.memM_smul`, `BMat.memM_kron` — soundness of the
  matrix operations.
* `BMat.norm_le_sum_norm` — the `ℓ²` operator norm of a square matrix is at most the sum of
  the moduli of its entries.
* `BMat.norm_le_bnorm` — `bnorm` bounds the operator norm of every matrix in the enclosure.
-/

@[expose] public section

set_option autoImplicit false

open Complex

namespace CatCrypt.Quantum.Synthesis.IntervalArith

/-- The working precision of the checkers: mantissas are read at the scale `2^-64`. -/
def prec : ℕ := 64

/-- A closed disc of `ℂ` in fixed point: centre mantissas `re`, `im` and radius mantissa
`rad`, read at a scale `2^-e` (`CBall.MemAt`). -/
structure CBall where
  /-- The mantissa of the real part of the centre. -/
  re : ℤ
  /-- The mantissa of the imaginary part of the centre. -/
  im : ℤ
  /-- The mantissa of the radius. -/
  rad : ℕ
  deriving Repr, Inhabited

namespace CBall

/-- The centre of a ball read at the scale `2^-e`. -/
noncomputable def centerAt (e : ℕ) (B : CBall) : ℂ := ((B.re : ℂ) + (B.im : ℂ) * I) / 2 ^ e

/-- `z` lies in the ball `B` read at the scale `2^-e`: its distance to the centre is at most
`rad / 2^e`. -/
def MemAt (e : ℕ) (z : ℂ) (B : CBall) : Prop := ‖z - B.centerAt e‖ ≤ (B.rad : ℝ) / 2 ^ e

/-- `z` lies in the ball `B` read at the working precision. -/
abbrev Mem (z : ℂ) (B : CBall) : Prop := MemAt prec z B

/-- An upper bound on the modulus of the centre mantissa: `|re| + |im|`. -/
def mag (B : CBall) : ℕ := B.re.natAbs + B.im.natAbs

theorem norm_centerAt_le (e : ℕ) (B : CBall) : ‖B.centerAt e‖ ≤ (B.mag : ℝ) / 2 ^ e := by
  have h := Complex.norm_le_abs_re_add_abs_im ((B.re : ℂ) + (B.im : ℂ) * I)
  have hre : ((B.re : ℂ) + (B.im : ℂ) * I).re = B.re := by simp
  have him : ((B.re : ℂ) + (B.im : ℂ) * I).im = B.im := by simp
  rw [hre, him] at h
  rw [centerAt, norm_div, norm_pow, Complex.norm_ofNat]
  have hm : (B.mag : ℝ) = |(B.re : ℝ)| + |(B.im : ℝ)| := by
    simp [mag, Nat.cast_natAbs]
  rw [hm]
  gcongr

theorem MemAt.norm_le {e : ℕ} {z : ℂ} {B : CBall} (h : MemAt e z B) :
    ‖z‖ ≤ ((B.mag + B.rad : ℕ) : ℝ) / 2 ^ e := by
  have h1 : ‖z‖ ≤ ‖z - B.centerAt e‖ + ‖B.centerAt e‖ := by
    simpa using norm_add_le (z - B.centerAt e) (B.centerAt e)
  have := norm_centerAt_le e B
  unfold MemAt at h
  push_cast
  rw [add_div]
  linarith

/-! ## Constants -/

/-- The exact ball at `0`. -/
def zero : CBall := ⟨0, 0, 0⟩

/-- The exact ball at `1`. -/
def one : CBall := ⟨2 ^ prec, 0, 0⟩

/-- The exact ball at `i`. -/
def iI : CBall := ⟨0, 2 ^ prec, 0⟩

/-- The unit disc. -/
def unit : CBall := ⟨0, 0, 2 ^ prec⟩

/-- The ball at the rational `q` rounded down to the grid `2^-64 ℤ`, of radius `2^-64`. -/
def ofQ (q : ℚ) : CBall := ⟨⌊q * 2 ^ prec⌋, 0, 1⟩

theorem mem_zero {e : ℕ} : MemAt e 0 zero := by simp [MemAt, zero, centerAt]

theorem mem_one : Mem 1 one := by
  simp [MemAt, one, centerAt]

theorem mem_iI : Mem I iI := by
  simp [MemAt, iI, centerAt]

theorem mem_unit {z : ℂ} (hz : ‖z‖ ≤ 1) : Mem z unit := by
  simpa [MemAt, unit, centerAt] using hz

theorem mem_ofQ (q : ℚ) : Mem (q : ℂ) (ofQ q) := by
  have h1 := Int.floor_le (q * 2 ^ prec)
  have h2 := Int.lt_floor_add_one (q * 2 ^ prec)
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  have hc : (q : ℂ) - (ofQ q).centerAt prec =
      (((q : ℝ) - (⌊q * 2 ^ prec⌋ : ℝ) / 2 ^ prec : ℝ) : ℂ) := by
    simp [ofQ, centerAt]
  rw [Mem, MemAt, hc, Complex.norm_real, Real.norm_eq_abs]
  have h1' : ((⌊q * 2 ^ prec⌋ : ℤ) : ℝ) ≤ (q : ℝ) * 2 ^ prec := by exact_mod_cast h1
  have h2' : (q : ℝ) * 2 ^ prec < ((⌊q * 2 ^ prec⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast h2
  have hk : (q : ℝ) - (⌊q * 2 ^ prec⌋ : ℝ) / 2 ^ prec =
      ((q : ℝ) * 2 ^ prec - (⌊q * 2 ^ prec⌋ : ℝ)) / 2 ^ prec := by
    field_simp
  have ha : |(q : ℝ) * 2 ^ prec - (⌊q * 2 ^ prec⌋ : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  rw [hk, abs_div, abs_of_pos hp]
  simp only [ofQ, Nat.cast_one]
  gcongr

/-! ## Arithmetic -/

/-- The ball of sums. -/
def add (A B : CBall) : CBall := ⟨A.re + B.re, A.im + B.im, A.rad + B.rad⟩

/-- The ball of negations. -/
def neg (A : CBall) : CBall := ⟨-A.re, -A.im, A.rad⟩

/-- The ball of differences. -/
def sub (A B : CBall) : CBall := ⟨A.re - B.re, A.im - B.im, A.rad + B.rad⟩

/-- The exact ball of products, read at the sum of the scales: the product of the centre
mantissas, with radius mantissa `mag A · rad B + rad A · mag B + rad A · rad B`. -/
def mulX (A B : CBall) : CBall :=
  ⟨A.re * B.re - A.im * B.im, A.re * B.im + A.im * B.re,
    A.mag * B.rad + A.rad * B.mag + A.rad * B.rad⟩

/-- `A` is the exact ball at `0`. -/
def isZero (A : CBall) : Bool := A.re == 0 && A.im == 0 && A.rad == 0

/-- The exact ball of products, `mulX`, computed without arithmetic when a factor is the exact
ball at `0`. -/
def mulW (A B : CBall) : CBall :=
  if A.isZero || B.isZero then ⟨0, 0, 0⟩
  else ⟨A.re * B.re - A.im * B.im, A.re * B.im + A.im * B.re,
    A.mag * B.rad + A.rad * B.mag + A.rad * B.rad⟩

theorem mulW_eq_mulX (A B : CBall) : mulW A B = mulX A B := by
  unfold mulW
  split
  · next h =>
    obtain ⟨a, b, r⟩ := A
    obtain ⟨a', b', r'⟩ := B
    simp only [isZero, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;> simp [mulX, mag]
  · rfl

/-- The compiled code of `mulX` is `mulW`: the zero shortcut runs, the proofs read `mulX`. -/
@[csimp] theorem mulX_eq_mulW : @mulX = @mulW := by
  funext A B
  exact (mulW_eq_mulX A B).symm

/-- The ball read at the scale `2^-(e + 64)` as a ball at the scale `2^-e`: the centre
mantissas are divided by `2^64` rounding down, and the radius mantissa plus the two
remainders is divided by `2^64` rounding up. -/
def shift (B : CBall) : CBall :=
  ⟨B.re / 2 ^ prec, B.im / 2 ^ prec,
    (B.rad + (B.re % 2 ^ prec).toNat + (B.im % 2 ^ prec).toNat + (2 ^ prec - 1)) / 2 ^ prec⟩

/-- The ball of products at the working scale: `mulX`, shifted. -/
def mul (A B : CBall) : CBall := shift (mulX A B)

theorem centerAt_add (e : ℕ) (A B : CBall) :
    (add A B).centerAt e = A.centerAt e + B.centerAt e := by
  simp only [centerAt, add]; push_cast; ring

theorem centerAt_neg (e : ℕ) (A : CBall) : (neg A).centerAt e = -A.centerAt e := by
  simp only [centerAt, neg]; push_cast; ring

theorem centerAt_sub (e : ℕ) (A B : CBall) :
    (sub A B).centerAt e = A.centerAt e - B.centerAt e := by
  simp only [centerAt, sub]; push_cast; ring

theorem centerAt_mulX (e₁ e₂ : ℕ) (A B : CBall) :
    (mulX A B).centerAt (e₁ + e₂) = A.centerAt e₁ * B.centerAt e₂ := by
  simp only [centerAt, mulX]
  push_cast
  rw [pow_add]
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem mem_add {e : ℕ} {z w : ℂ} {A B : CBall} (hz : MemAt e z A) (hw : MemAt e w B) :
    MemAt e (z + w) (add A B) := by
  unfold MemAt at *
  rw [centerAt_add, show z + w - (A.centerAt e + B.centerAt e) =
    (z - A.centerAt e) + (w - B.centerAt e) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [add]; push_cast; rw [add_div]; linarith

theorem mem_neg {e : ℕ} {z : ℂ} {A : CBall} (hz : MemAt e z A) : MemAt e (-z) (neg A) := by
  unfold MemAt at *
  rw [centerAt_neg, show -z - -A.centerAt e = -(z - A.centerAt e) by ring, norm_neg]
  simpa [neg] using hz

theorem mem_sub {e : ℕ} {z w : ℂ} {A B : CBall} (hz : MemAt e z A) (hw : MemAt e w B) :
    MemAt e (z - w) (sub A B) := by
  unfold MemAt at *
  rw [centerAt_sub, show z - w - (A.centerAt e - B.centerAt e) =
    (z - A.centerAt e) - (w - B.centerAt e) by ring]
  refine (norm_sub_le _ _).trans ?_
  simp only [sub]; push_cast; rw [add_div]; linarith

theorem mem_mulX {e₁ e₂ : ℕ} {z w : ℂ} {A B : CBall} (hz : MemAt e₁ z A) (hw : MemAt e₂ w B) :
    MemAt (e₁ + e₂) (z * w) (mulX A B) := by
  have hA := norm_centerAt_le e₁ A
  have hB := norm_centerAt_le e₂ B
  unfold MemAt at *
  rw [centerAt_mulX, show z * w - A.centerAt e₁ * B.centerAt e₂ =
    A.centerAt e₁ * (w - B.centerAt e₂) + (z - A.centerAt e₁) * B.centerAt e₂ +
      (z - A.centerAt e₁) * (w - B.centerAt e₂) by ring]
  refine (norm_add₃_le).trans ?_
  rw [norm_mul, norm_mul, norm_mul]
  have h1 := mul_le_mul hA hw (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul hz hB (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul hz hw (norm_nonneg _) (by positivity)
  have hr : ((mulX A B).rad : ℝ) / 2 ^ (e₁ + e₂) =
      A.mag / 2 ^ e₁ * (B.rad / 2 ^ e₂) + A.rad / 2 ^ e₁ * (B.mag / 2 ^ e₂) +
        A.rad / 2 ^ e₁ * (B.rad / 2 ^ e₂) := by
    simp only [mulX]
    push_cast
    rw [pow_add]
    field_simp
  rw [hr]
  linarith

/-- A natural `N` is at most `s` times its quotient by `s` rounded up. -/
theorem le_mul_ceil_div (N s : ℕ) (hs : 0 < s) : N ≤ s * ((N + (s - 1)) / s) := by
  have h1 := Nat.div_add_mod (N + (s - 1)) s
  have h2 := Nat.mod_lt (N + (s - 1)) hs
  generalize s * ((N + (s - 1)) / s) = t at *
  omega

theorem mem_shift {e : ℕ} {z : ℂ} {B : CBall} (hz : MemAt (e + prec) z B) :
    MemAt e z (shift B) := by
  set s : ℤ := 2 ^ prec with hs
  have hs0 : (0 : ℤ) < s := by positivity
  have hre := Int.emod_add_mul_ediv B.re s
  have him := Int.emod_add_mul_ediv B.im s
  have r1 := Int.emod_nonneg B.re hs0.ne'
  have r2 := Int.emod_nonneg B.im hs0.ne'
  set N : ℕ := B.rad + (B.re % s).toNat + (B.im % s).toNat with hN
  have hNs := le_mul_ceil_div N (2 ^ prec) (by positivity)
  have hNR : (N : ℝ) = B.rad + ((B.re % s : ℤ) : ℝ) + ((B.im % s : ℤ) : ℝ) := by
    have t1 : (((B.re % s).toNat : ℕ) : ℝ) = ((B.re % s : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg r1]
    have t2 : (((B.im % s).toNat : ℕ) : ℝ) = ((B.im % s : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg r2]
    rw [hN]; push_cast
    rw [t1, t2]
  have hNs' : (N : ℝ) ≤ 2 ^ prec * (((shift B).rad : ℕ) : ℝ) := by
    exact_mod_cast hNs
  have hc : B.centerAt (e + prec) - (shift B).centerAt e =
      (((B.re % s : ℤ) : ℂ) + ((B.im % s : ℤ) : ℂ) * I) / 2 ^ (e + prec) := by
    have hre' : (B.re : ℂ) = ((B.re % s : ℤ) : ℂ) + (s : ℂ) * ((B.re / s : ℤ) : ℂ) := by
      exact_mod_cast hre.symm
    have him' : (B.im : ℂ) = ((B.im % s : ℤ) : ℂ) + (s : ℂ) * ((B.im / s : ℤ) : ℂ) := by
      exact_mod_cast him.symm
    simp only [centerAt, shift]
    rw [hre', him', hs, pow_add]
    push_cast
    field_simp
    ring
  have hd : ‖B.centerAt (e + prec) - (shift B).centerAt e‖ ≤
      (((B.re % s : ℤ) : ℝ) + ((B.im % s : ℤ) : ℝ)) / 2 ^ (e + prec) := by
    rw [hc, norm_div, norm_pow, Complex.norm_ofNat]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast,
      abs_of_nonneg (by exact_mod_cast r1), abs_of_nonneg (by exact_mod_cast r2)]
  unfold MemAt at *
  rw [show z - (shift B).centerAt e =
    (z - B.centerAt (e + prec)) + (B.centerAt (e + prec) - (shift B).centerAt e) by ring]
  refine (norm_add_le _ _).trans ?_
  have hsum : (B.rad : ℝ) / 2 ^ (e + prec) +
      (((B.re % s : ℤ) : ℝ) + ((B.im % s : ℤ) : ℝ)) / 2 ^ (e + prec) =
      (N : ℝ) / 2 ^ (e + prec) := by
    rw [hNR, ← add_div]; ring_nf
  have hfin : (N : ℝ) / 2 ^ (e + prec) ≤ (((shift B).rad : ℕ) : ℝ) / 2 ^ e := by
    rw [pow_add, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (N : ℝ) * 2 ^ e ≤ 2 ^ prec * (((shift B).rad : ℕ) : ℝ) * 2 ^ e := by gcongr
      _ = _ := by ring
  linarith

theorem mem_mul {z w : ℂ} {A B : CBall} (hz : Mem z A) (hw : Mem w B) :
    Mem (z * w) (mul A B) :=
  mem_shift (mem_mulX hz hw)

/-- The ball with the radius increased by the rational `e`, rounded up to `2^-64 ℤ`. -/
def widen (e : ℚ) (A : CBall) : CBall := ⟨A.re, A.im, A.rad + ⌈e * 2 ^ prec⌉.toNat⟩

/-- A point within `e` of a point of `A` lies in `widen e A`. -/
theorem mem_widen {z w : ℂ} {A : CBall} {e : ℚ} (hw : Mem w A) (h : ‖z - w‖ ≤ (e : ℝ)) :
    Mem z (widen e A) := by
  unfold Mem MemAt at *
  have hc : (widen e A).centerAt prec = A.centerAt prec := rfl
  have h1 : e * 2 ^ prec ≤ (⌈e * 2 ^ prec⌉.toNat : ℚ) := by
    have := Int.le_ceil (e * 2 ^ prec)
    have h2 : (⌈e * 2 ^ prec⌉ : ℚ) ≤ ((⌈e * 2 ^ prec⌉.toNat : ℤ) : ℚ) := by
      exact_mod_cast Int.self_le_toNat _
    push_cast at h2
    linarith
  have h1' : (e : ℝ) ≤ ((⌈e * 2 ^ prec⌉.toNat : ℕ) : ℝ) / 2 ^ prec := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast h1
  rw [hc, show z - A.centerAt prec = (z - w) + (w - A.centerAt prec) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [widen]; push_cast; rw [add_div]; linarith

/-! ## Rounding of rationals -/

/-- `q` rounded up to the grid `2^-p ℤ`. -/
def ceilD (p : ℕ) (q : ℚ) : ℚ := (⌈q * 2 ^ p⌉ : ℚ) / 2 ^ p

theorem le_ceilD (p : ℕ) (q : ℚ) : q ≤ ceilD p q := by
  unfold ceilD
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-! ## Finite sums -/

/-- The ball of sums of a finite family, by recursion on the length. -/
def bsum : {k : ℕ} → (Fin k → CBall) → CBall
  | 0, _ => zero
  | _ + 1, f => add (f 0) (bsum fun i => f i.succ)

theorem mem_bsum {e : ℕ} : ∀ {k : ℕ} {z : Fin k → ℂ} {f : Fin k → CBall},
    (∀ i, MemAt e (z i) (f i)) → MemAt e (∑ i, z i) (bsum f)
  | 0, _, _, _ => by simpa [bsum] using mem_zero
  | _ + 1, _, _, h => by
    rw [Fin.sum_univ_succ]
    exact mem_add (h 0) (mem_bsum fun i => h i.succ)

end CBall

/-! ## Matrices of balls -/

open CBall

/-- A `k × k` matrix of balls, stored as nested vectors (rows first). -/
abbrev BMat (k : ℕ) := Vector (Vector CBall k) k

namespace BMat

variable {k : ℕ}

/-- The ball at row `i` and column `j`. -/
def get (B : BMat k) (i j : Fin k) : CBall := B[i][j]

/-- The matrix of balls with entries `f i j`. -/
def ofFn (f : Fin k → Fin k → CBall) : BMat k := Vector.ofFn fun i => Vector.ofFn (f i)

@[simp] theorem get_ofFn (f : Fin k → Fin k → CBall) (i j : Fin k) : (ofFn f).get i j = f i j := by
  simp [get, ofFn]

/-- Every entry of the complex matrix `A` lies in the ball of `B` at the same place. -/
def MemM (A : Matrix (Fin k) (Fin k) ℂ) (B : BMat k) : Prop := ∀ i j, Mem (A i j) (B.get i j)

/-- The product of matrices of balls: each entry is the sum of the exact products, shifted
once to the working scale. -/
def mul (A B : BMat k) : BMat k :=
  ofFn fun i j => shift (bsum fun l => mulX (A.get i l) (B.get l j))

/-- The difference of matrices of balls. -/
def sub (A B : BMat k) : BMat k := ofFn fun i j => CBall.sub (A.get i j) (B.get i j)

/-- The matrix of balls scaled by a ball. -/
def smul (c : CBall) (A : BMat k) : BMat k := ofFn fun i j => CBall.mul c (A.get i j)

/-- The identity matrix of exact balls. -/
def one : BMat k := ofFn fun i j => if i = j then CBall.one else CBall.zero

/-- The Kronecker product of matrices of balls, on the index order of `kronecker`. -/
def kron {a b : ℕ} (A : BMat a) (B : BMat b) : BMat (a * b) :=
  ofFn fun i j =>
    let i' := (TensorProduct.finProdEquiv a b).symm i
    let j' := (TensorProduct.finProdEquiv a b).symm j
    CBall.mul (A.get i'.1 j'.1) (B.get i'.2 j'.2)

theorem memM_mul {A B : Matrix (Fin k) (Fin k) ℂ} {A' B' : BMat k} (hA : MemM A A')
    (hB : MemM B B') : MemM (A * B) (mul A' B') := by
  intro i j
  rw [mul, get_ofFn, Matrix.mul_apply]
  exact mem_shift (mem_bsum fun l => mem_mulX (hA i l) (hB l j))

theorem memM_sub {A B : Matrix (Fin k) (Fin k) ℂ} {A' B' : BMat k} (hA : MemM A A')
    (hB : MemM B B') : MemM (A - B) (sub A' B') := by
  intro i j
  rw [sub, get_ofFn, Matrix.sub_apply]
  exact mem_sub (hA i j) (hB i j)

theorem memM_smul {c : ℂ} {A : Matrix (Fin k) (Fin k) ℂ} {c' : CBall} {A' : BMat k}
    (hc : Mem c c') (hA : MemM A A') : MemM (c • A) (smul c' A') := by
  intro i j
  rw [smul, get_ofFn, Matrix.smul_apply, smul_eq_mul]
  exact mem_mul hc (hA i j)

theorem memM_one : MemM (1 : Matrix (Fin k) (Fin k) ℂ) one := by
  intro i j
  rw [one, get_ofFn, Matrix.one_apply]
  split
  · exact mem_one
  · exact mem_zero

theorem memM_kron {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℂ} {B : Matrix (Fin b) (Fin b) ℂ}
    {A' : BMat a} {B' : BMat b} (hA : MemM A A') (hB : MemM B B') :
    MemM (TensorProduct.kronecker A B) (kron A' B') := by
  intro i j
  rw [kron, get_ofFn, TensorProduct.kronecker_apply]
  exact mem_mul (hA _ _) (hB _ _)

/-! ## The operator norm of an enclosure -/

open scoped Matrix.Norms.L2Operator

/-- A matrix unit with entry `c` has `ℓ²` operator norm at most `‖c‖`. -/
theorem norm_single_le (i j : Fin k) (c : ℂ) : ‖Matrix.single i j c‖ ≤ ‖c‖ := by
  have hE : ‖Matrix.single i j (1 : ℂ)‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (Matrix.single i j (1 : ℂ))
    rw [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul,
      ← Matrix.diagonal_single, Matrix.l2_opNorm_diagonal] at h
    have h1 : ‖(Pi.single j (1 : ℂ) : Fin k → ℂ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun l => ?_
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    nlinarith [norm_nonneg (Matrix.single i j (1 : ℂ))]
  have hs : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs]
  refine (norm_smul_le c _).trans ?_
  simpa using mul_le_mul_of_nonneg_left hE (norm_nonneg c)

/-- The `ℓ²` operator norm of a square matrix is at most the sum of the moduli of its
entries. -/
theorem norm_le_sum_norm (A : Matrix (Fin k) (Fin k) ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_single_le i j _)

/-- A rational upper bound on the `ℓ²` operator norm of every matrix with entries in `B`:
the sum over the entries of the mantissas `mag + rad`, divided by `2^64`. -/
def bnorm (B : BMat k) : ℚ := ((∑ i, ∑ j, ((B.get i j).mag + (B.get i j).rad) : ℕ) : ℚ) / 2 ^ prec

theorem norm_le_bnorm {A : Matrix (Fin k) (Fin k) ℂ} {B : BMat k} (h : MemM A B) :
    ‖A‖ ≤ (bnorm B : ℝ) := by
  refine (norm_le_sum_norm A).trans ?_
  rw [bnorm]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  have := (h i j).norm_le
  push_cast at this
  exact this

end BMat

end CatCrypt.Quantum.Synthesis.IntervalArith
