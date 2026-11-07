/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.PiLin

/-!
# Angles affine in circuit parameters

`AffAngle` is an angle `c + Σᵢ qᵢ·θᵢ`: an exact constant `c = a + b·π` (a `PiLin`) plus a
rational combination of the parameters `θᵢ` of a parameterised circuit. Its real value
under a valuation `ρ : ℕ → ℝ` of the parameters is `AffAngle.toReal ρ`. A circuit whose
angles are `AffAngle`s is compiled once, and its parameters are bound afterwards.

The coefficients are a list of pairs `(i, qᵢ)`. Addition merges two lists by index and drops
a coefficient that sums to zero, so on lists with strictly increasing indices and nonzero
coefficients (`AffAngle.Normal`) the representation is unique: two normal angles with the
same value under every valuation are equal (`AffAngle.eq_of_forall_toReal_eq`).

## Numerals and the coercion from `PiLin`

A numeral, a cast of a natural number or an integer, and the coercion `PiLin → AffAngle`
go through `AffAngle.ofLin`, the angle with no parameter part, so a numeral denotes the
multiple of `π` it denotes as a `PiLin`. Division `x / y` divides both parts of `x` by the
`π`-coefficient of the constant part of `y`; on a divisor `q·π` it divides the real angle
by `q` (`AffAngle.toReal_div_ofPi_at`).

## Main definitions

* `AffAngle`, `AffAngle.toReal`, `AffAngle.ofLin`, `AffAngle.param`.
* `AffAngle.const?` — the constant of an angle with no parameter part.
* `AffAngle.Normal` — indices strictly increasing, coefficients nonzero.

## Main results

* `AffAngle.toReal_add_at`, `AffAngle.toReal_neg_at`, `AffAngle.toReal_sub_at`,
  `AffAngle.toReal_div_ofPi_at` — the real angle at every valuation `ρ` of the parameters
  respects the operations; `AffAngle.toReal_ofLin`, `AffAngle.toReal_param`.
* `AffAngle.const?_spec`.
* `AffAngle.normal_ofLin`, `AffAngle.normal_param`, `AffAngle.Normal.add`,
  `AffAngle.Normal.neg`, `AffAngle.Normal.sub`, `AffAngle.Normal.div`.
* `AffAngle.eq_of_forall_toReal_eq`, from `irrational_pi`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum

/-- An angle `c + Σᵢ qᵢ·θᵢ` affine in the parameters `θᵢ` of a circuit. -/
structure AffAngle where
  /-- The constant part `a + b·π`. -/
  c : PiLin
  /-- The coefficients `(i, qᵢ)` of the parameters `θᵢ`. -/
  coef : List (ℕ × ℚ)
  deriving DecidableEq, Repr

namespace AffAngle

/-- The real angle under the valuation `ρ` of the parameters. -/
noncomputable def toReal (ρ : ℕ → ℝ) (x : AffAngle) : ℝ :=
  x.c.toReal + (x.coef.map fun e => (e.2 : ℝ) * ρ e.1).sum

/-- The constant of an angle with no parameter part. -/
def const? (x : AffAngle) : Option PiLin := if x.coef = [] then some x.c else none

/-- The angle with constant part `p` and no parameter part. -/
@[coe] def ofLin (p : PiLin) : AffAngle := ⟨p, []⟩

/-- A `PiLin` is the angle with no parameter part. -/
instance : Coe PiLin AffAngle := ⟨ofLin⟩

/-- The parameter `θᵢ`. -/
def param (i : ℕ) : AffAngle := ⟨0, [(i, 1)]⟩

/-- The sum of two coefficient lists sorted by index: the coefficients of an index present in
both lists add, and an index whose sum is zero is dropped. -/
def addCoef : List (ℕ × ℚ) → List (ℕ × ℚ) → List (ℕ × ℚ)
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | (i, a) :: xs, (j, b) :: ys =>
    if i < j then (i, a) :: addCoef xs ((j, b) :: ys)
    else if j < i then (j, b) :: addCoef ((i, a) :: xs) ys
    else if a + b = 0 then addCoef xs ys
    else (i, a + b) :: addCoef xs ys

/-- The negated coefficients. -/
def negCoef (l : List (ℕ × ℚ)) : List (ℕ × ℚ) := l.map fun e => (e.1, -e.2)

/-- The coefficients divided by `d`; division by zero leaves no coefficient. -/
def divCoef (d : ℚ) (l : List (ℕ × ℚ)) : List (ℕ × ℚ) :=
  if d = 0 then [] else l.map fun e => (e.1, e.2 / d)

instance : Zero AffAngle := ⟨ofLin 0⟩
instance : One AffAngle := ⟨ofLin 1⟩
instance : NatCast AffAngle := ⟨fun n => ofLin (n : PiLin)⟩
instance : IntCast AffAngle := ⟨fun k => ofLin (k : PiLin)⟩
instance (n : ℕ) [n.AtLeastTwo] : OfNat AffAngle n := ⟨ofLin (OfNat.ofNat n)⟩
instance : Add AffAngle := ⟨fun x y => ⟨x.c + y.c, addCoef x.coef y.coef⟩⟩
instance : Neg AffAngle := ⟨fun x => ⟨-x.c, negCoef x.coef⟩⟩
instance : Sub AffAngle := ⟨fun x y => ⟨x.c - y.c, addCoef x.coef (negCoef y.coef)⟩⟩
/-- Division by the `π`-coefficient of the constant part of the divisor. -/
instance : Div AffAngle := ⟨fun x y => ⟨x.c / y.c, divCoef y.c.b x.coef⟩⟩

@[simp] theorem ofLin_c (p : PiLin) : (ofLin p).c = p := rfl
@[simp] theorem ofLin_coef (p : PiLin) : (ofLin p).coef = [] := rfl
@[simp] theorem param_c (i : ℕ) : (param i).c = 0 := rfl
@[simp] theorem param_coef (i : ℕ) : (param i).coef = [(i, 1)] := rfl
@[simp] theorem add_c (x y : AffAngle) : (x + y).c = x.c + y.c := rfl
@[simp] theorem add_coef (x y : AffAngle) : (x + y).coef = addCoef x.coef y.coef := rfl
@[simp] theorem neg_c (x : AffAngle) : (-x).c = -x.c := rfl
@[simp] theorem neg_coef (x : AffAngle) : (-x).coef = negCoef x.coef := rfl
@[simp] theorem sub_c (x y : AffAngle) : (x - y).c = x.c - y.c := rfl
@[simp] theorem sub_coef (x y : AffAngle) :
    (x - y).coef = addCoef x.coef (negCoef y.coef) := rfl
@[simp] theorem div_c (x y : AffAngle) : (x / y).c = x.c / y.c := rfl
@[simp] theorem div_coef (x y : AffAngle) : (x / y).coef = divCoef y.c.b x.coef := rfl

/-! The simp lemmas below rewrite a numeral of `AffAngle` to `ofLin` of the `PiLin`
numeral, which `PiLin`'s simp lemmas rewrite to `ofPi q`. -/

/-- The numeral `0` is the angle `0` with no parameter part. -/
@[simp] theorem zero_eq_ofLin : (0 : AffAngle) = ofLin 0 := rfl

/-- The numeral `1` is the angle `π` with no parameter part. -/
@[simp] theorem one_eq_ofLin : (1 : AffAngle) = ofLin 1 := rfl

/-- A numeral `n ≥ 2` is the angle `n·π` with no parameter part. -/
@[simp] theorem ofNat_eq_ofLin (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : AffAngle) = ofLin (OfNat.ofNat n) := rfl

/-- The cast of a natural number `n` is the angle `n·π` with no parameter part. -/
@[simp] theorem natCast_eq_ofLin (n : ℕ) : (n : AffAngle) = ofLin (n : PiLin) := rfl

/-- The cast of an integer `k` is the angle `k·π` with no parameter part. -/
@[simp] theorem intCast_eq_ofLin (k : ℤ) : (k : AffAngle) = ofLin (k : PiLin) := rfl

/-! ## The real angle -/

/-- The parameter part of `toReal` of a merged list is the sum of the parts. -/
theorem sum_addCoef (ρ : ℕ → ℝ) (xs ys : List (ℕ × ℚ)) :
    ((addCoef xs ys).map fun e => (e.2 : ℝ) * ρ e.1).sum =
      (xs.map fun e => (e.2 : ℝ) * ρ e.1).sum + (ys.map fun e => (e.2 : ℝ) * ρ e.1).sum := by
  fun_induction addCoef xs ys with
  | case1 => simp
  | case2 => simp
  | case3 i a xs j b ys _ ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring
  | case4 i a xs j b ys _ _ ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring
  | case5 i a xs j b ys _ _ hab ih =>
    obtain rfl : i = j := by omega
    have hab' : (a : ℝ) + b = 0 := by exact_mod_cast hab
    simp only [List.map_cons, List.sum_cons, ih]
    linear_combination -(ρ i * hab')
  | case6 i a xs j b ys _ _ _ ih =>
    obtain rfl : i = j := by omega
    simp only [List.map_cons, List.sum_cons, ih]
    push_cast
    ring

/-- The parameter part of `toReal` of the negated coefficients is the negated part. -/
theorem sum_negCoef (ρ : ℕ → ℝ) (l : List (ℕ × ℚ)) :
    ((negCoef l).map fun e => (e.2 : ℝ) * ρ e.1).sum =
      -(l.map fun e => (e.2 : ℝ) * ρ e.1).sum := by
  induction l with
  | nil => simp [negCoef]
  | cons e l ih =>
    simp only [negCoef, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

/-- The parameter part of `toReal` of the coefficients divided by `d` is the part divided
by `d`. -/
theorem sum_divCoef (ρ : ℕ → ℝ) (d : ℚ) (l : List (ℕ × ℚ)) :
    ((divCoef d l).map fun e => (e.2 : ℝ) * ρ e.1).sum =
      (l.map fun e => (e.2 : ℝ) * ρ e.1).sum / d := by
  unfold divCoef
  split_ifs with hd
  · simp [hd]
  · induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      push_cast
      ring

/-- An angle with no parameter part has the value of its constant. -/
@[simp] theorem toReal_ofLin (ρ : ℕ → ℝ) (p : PiLin) : (ofLin p).toReal ρ = p.toReal := by
  simp [toReal]

/-- The parameter `θᵢ` has the value `ρ i`. -/
@[simp] theorem toReal_param (ρ : ℕ → ℝ) (i : ℕ) : (param i).toReal ρ = ρ i := by
  simp [toReal]

/-- Addition of angles is addition of their values. -/
@[simp] theorem toReal_add_at (ρ : ℕ → ℝ) (x y : AffAngle) :
    (x + y).toReal ρ = x.toReal ρ + y.toReal ρ := by
  simp only [toReal, add_c, add_coef, PiLin.toReal_add, sum_addCoef]; ring

/-- Negation of an angle is negation of its value. -/
@[simp] theorem toReal_neg_at (ρ : ℕ → ℝ) (x : AffAngle) : (-x).toReal ρ = -x.toReal ρ := by
  simp only [toReal, neg_c, neg_coef, PiLin.toReal_neg, sum_negCoef]; ring

/-- Subtraction of angles is subtraction of their values. -/
@[simp] theorem toReal_sub_at (ρ : ℕ → ℝ) (x y : AffAngle) :
    (x - y).toReal ρ = x.toReal ρ - y.toReal ρ := by
  simp only [toReal, sub_c, sub_coef, PiLin.toReal_sub, sum_addCoef, sum_negCoef]; ring

/-- Division by the angle `q·π` divides the real angle by `q`. -/
@[simp] theorem toReal_div_ofPi_at (ρ : ℕ → ℝ) (x : AffAngle) (q : QasmAngle) :
    (x / PiLin.ofPi q).toReal ρ = x.toReal ρ / q := by
  simp only [toReal, div_c, div_coef, ofLin_c, PiLin.ofPi_b, PiLin.toReal_div_ofPi,
    sum_divCoef]
  ring

/-- An angle whose constant `const?` returns has the real value of that constant under
every valuation. -/
theorem const?_spec {x : AffAngle} {p : PiLin} (h : x.const? = some p) (ρ : ℕ → ℝ) :
    x.toReal ρ = p.toReal := by
  unfold const? at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  simp [toReal, hc]

/-! ## Normal form -/

/-- Indices strictly increasing and coefficients nonzero. -/
def Normal (x : AffAngle) : Prop :=
  x.coef.Pairwise (fun e f => e.1 < f.1) ∧ ∀ e ∈ x.coef, e.2 ≠ 0

/-- `Normal` is decided on the coefficient list. -/
instance (x : AffAngle) : Decidable (Normal x) :=
  inferInstanceAs (Decidable (x.coef.Pairwise (fun e f => e.1 < f.1) ∧ ∀ e ∈ x.coef, e.2 ≠ 0))

/-- Every index of a merged list exceeds `k` when every index of both lists does. -/
theorem lt_of_mem_addCoef (k : ℕ) (xs ys : List (ℕ × ℚ))
    (hx : ∀ e ∈ xs, k < e.1) (hy : ∀ e ∈ ys, k < e.1) :
    ∀ e ∈ addCoef xs ys, k < e.1 := by
  fun_induction addCoef xs ys with
  | case1 => exact hy
  | case2 => exact hx
  | case3 i a xs j b ys _ ih =>
    rw [List.forall_mem_cons] at hx ⊢
    exact ⟨hx.1, ih hx.2 hy⟩
  | case4 i a xs j b ys _ _ ih =>
    rw [List.forall_mem_cons] at hy ⊢
    exact ⟨hy.1, ih hx hy.2⟩
  | case5 i a xs j b ys _ _ _ ih =>
    exact ih (List.forall_mem_cons.1 hx).2 (List.forall_mem_cons.1 hy).2
  | case6 i a xs j b ys _ _ _ ih =>
    rw [List.forall_mem_cons] at hx hy ⊢
    exact ⟨hx.1, ih hx.2 hy.2⟩

/-- Merging keeps indices strictly increasing. -/
theorem pairwise_addCoef (xs ys : List (ℕ × ℚ))
    (hx : xs.Pairwise (fun e f => e.1 < f.1)) (hy : ys.Pairwise (fun e f => e.1 < f.1)) :
    (addCoef xs ys).Pairwise (fun e f => e.1 < f.1) := by
  fun_induction addCoef xs ys with
  | case1 => exact hy
  | case2 => exact hx
  | case3 i a xs j b ys hij ih =>
    obtain ⟨hx₁, hx₂⟩ := List.pairwise_cons.1 hx
    obtain ⟨hy₁, -⟩ := List.pairwise_cons.1 hy
    exact List.pairwise_cons.2 ⟨lt_of_mem_addCoef i _ _ hx₁
      (List.forall_mem_cons.2 ⟨hij, fun e he => hij.trans (hy₁ e he)⟩), ih hx₂ hy⟩
  | case4 i a xs j b ys _ hji ih =>
    obtain ⟨hx₁, -⟩ := List.pairwise_cons.1 hx
    obtain ⟨hy₁, hy₂⟩ := List.pairwise_cons.1 hy
    exact List.pairwise_cons.2 ⟨lt_of_mem_addCoef j _ _
      (List.forall_mem_cons.2 ⟨hji, fun e he => hji.trans (hx₁ e he)⟩) hy₁, ih hx hy₂⟩
  | case5 i a xs j b ys _ _ _ ih =>
    exact ih (List.pairwise_cons.1 hx).2 (List.pairwise_cons.1 hy).2
  | case6 i a xs j b ys _ _ _ ih =>
    obtain rfl : i = j := by omega
    obtain ⟨hx₁, hx₂⟩ := List.pairwise_cons.1 hx
    obtain ⟨hy₁, hy₂⟩ := List.pairwise_cons.1 hy
    exact List.pairwise_cons.2 ⟨lt_of_mem_addCoef i _ _ hx₁ hy₁, ih hx₂ hy₂⟩

/-- Merging keeps coefficients nonzero. -/
theorem ne_zero_of_mem_addCoef (xs ys : List (ℕ × ℚ))
    (hx : ∀ e ∈ xs, e.2 ≠ 0) (hy : ∀ e ∈ ys, e.2 ≠ 0) :
    ∀ e ∈ addCoef xs ys, e.2 ≠ 0 := by
  fun_induction addCoef xs ys with
  | case1 => exact hy
  | case2 => exact hx
  | case3 i a xs j b ys _ ih =>
    rw [List.forall_mem_cons] at hx ⊢
    exact ⟨hx.1, ih hx.2 hy⟩
  | case4 i a xs j b ys _ _ ih =>
    rw [List.forall_mem_cons] at hy ⊢
    exact ⟨hy.1, ih hx hy.2⟩
  | case5 i a xs j b ys _ _ _ ih =>
    exact ih (List.forall_mem_cons.1 hx).2 (List.forall_mem_cons.1 hy).2
  | case6 i a xs j b ys _ _ hab ih =>
    rw [List.forall_mem_cons] at hx hy ⊢
    exact ⟨hab, ih hx.2 hy.2⟩

/-- An angle with no parameter part is normal. -/
theorem normal_ofLin (p : PiLin) : Normal (ofLin p) := by
  simp [Normal]

/-- A parameter is normal. -/
theorem normal_param (i : ℕ) : Normal (param i) := by
  simp [Normal]

/-- The sum of normal angles is normal. -/
theorem Normal.add {x y : AffAngle} (hx : Normal x) (hy : Normal y) : Normal (x + y) :=
  ⟨pairwise_addCoef _ _ hx.1 hy.1, ne_zero_of_mem_addCoef _ _ hx.2 hy.2⟩

/-- The negation of a normal angle is normal. -/
theorem Normal.neg {x : AffAngle} (hx : Normal x) : Normal (-x) := by
  refine ⟨by simpa [negCoef, List.pairwise_map] using hx.1, fun e he => ?_⟩
  simp only [neg_coef, negCoef] at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 he
  exact neg_ne_zero.2 (hx.2 f hf)

/-- The difference of normal angles is normal. -/
theorem Normal.sub {x y : AffAngle} (hx : Normal x) (hy : Normal y) : Normal (x - y) :=
  ⟨pairwise_addCoef _ _ hx.1 hy.neg.1, ne_zero_of_mem_addCoef _ _ hx.2 hy.neg.2⟩

/-- A normal angle divided by any angle is normal. -/
theorem Normal.div {x : AffAngle} (hx : Normal x) (y : AffAngle) : Normal (x / y) := by
  simp only [Normal, div_coef, divCoef]
  split_ifs with hd
  · simp
  · refine ⟨by simpa [List.pairwise_map] using hx.1, fun e he => ?_⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 he
    exact div_ne_zero (hx.2 f hf) hd

/-! ## Uniqueness of the normal form -/

/-- The indicator valuation of the parameter `i` reads off nothing from a list in which `i`
does not occur. -/
theorem sum_indicator_eq_zero (i : ℕ) (l : List (ℕ × ℚ)) (h : ∀ e ∈ l, e.1 ≠ i) :
    (l.map fun e => (e.2 : ℝ) * (if e.1 = i then 1 else 0)).sum = 0 := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.forall_mem_cons] at h
    rw [List.map_cons, List.sum_cons, ih h.2, ite_eq_right h.1, mul_zero, add_zero]

/-- Two normal coefficient lists with the same parameter part under every valuation are
equal. -/
theorem coef_eq_of_forall_sum_eq : ∀ (l₁ l₂ : List (ℕ × ℚ)),
    l₁.Pairwise (fun e f => e.1 < f.1) → (∀ e ∈ l₁, e.2 ≠ 0) →
    l₂.Pairwise (fun e f => e.1 < f.1) → (∀ e ∈ l₂, e.2 ≠ 0) →
    (∀ ρ : ℕ → ℝ, (l₁.map fun e => (e.2 : ℝ) * ρ e.1).sum =
      (l₂.map fun e => (e.2 : ℝ) * ρ e.1).sum) →
    l₁ = l₂
  | [], [], _, _, _, _, _ => rfl
  | [], (j, b) :: t, _, _, p₂, n₂, h => by
    have h' := h fun k => if k = j then 1 else 0
    rw [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
      sum_indicator_eq_zero j t fun e he => ((List.pairwise_cons.1 p₂).1 e he).ne',
      ite_eq_left rfl, mul_one, add_zero] at h'
    have hb : b = 0 := by exact_mod_cast h'.symm
    exact absurd hb (n₂ (j, b) List.mem_cons_self)
  | (i, a) :: t, [], p₁, n₁, _, _, h => by
    have h' := h fun k => if k = i then 1 else 0
    rw [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
      sum_indicator_eq_zero i t fun e he => ((List.pairwise_cons.1 p₁).1 e he).ne',
      ite_eq_left rfl, mul_one, add_zero] at h'
    have ha : a = 0 := by exact_mod_cast h'
    exact absurd ha (n₁ (i, a) List.mem_cons_self)
  | (i, a) :: t₁, (j, b) :: t₂, p₁, n₁, p₂, n₂, h => by
    obtain ⟨p₁₁, p₁₂⟩ := List.pairwise_cons.1 p₁
    obtain ⟨p₂₁, p₂₂⟩ := List.pairwise_cons.1 p₂
    have key : ∀ k, (∀ e ∈ t₁, e.1 ≠ k) → (∀ e ∈ t₂, e.1 ≠ k) →
        (a : ℝ) * (if i = k then 1 else 0) = (b : ℝ) * (if j = k then 1 else 0) := by
      intro k h₁ h₂
      have h' := h fun m => if m = k then 1 else 0
      rwa [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        sum_indicator_eq_zero k t₁ h₁, sum_indicator_eq_zero k t₂ h₂, add_zero, add_zero] at h'
    rcases lt_trichotomy i j with hij | rfl | hij
    · have := key i (fun e he => (p₁₁ e he).ne') fun e he => (hij.trans (p₂₁ e he)).ne'
      rw [ite_eq_left rfl, ite_eq_right hij.ne', mul_one, mul_zero] at this
      have ha : a = 0 := by exact_mod_cast this
      exact absurd ha (n₁ (i, a) List.mem_cons_self)
    · have := key i (fun e he => (p₁₁ e he).ne') fun e he => (p₂₁ e he).ne'
      rw [ite_eq_left rfl, mul_one, mul_one] at this
      obtain rfl : a = b := by exact_mod_cast this
      rw [coef_eq_of_forall_sum_eq t₁ t₂ p₁₂ (fun e he => n₁ e (List.mem_cons_of_mem _ he)) p₂₂
        (fun e he => n₂ e (List.mem_cons_of_mem _ he)) fun ρ => by
          have := h ρ
          rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons] at this
          linarith]
    · have := key j (fun e he => (hij.trans (p₁₁ e he)).ne') fun e he => (p₂₁ e he).ne'
      rw [ite_eq_left rfl, ite_eq_right hij.ne', mul_one, mul_zero] at this
      have hb : b = 0 := by exact_mod_cast this.symm
      exact absurd hb (n₂ (j, b) List.mem_cons_self)

/-- Two normal angles with the same real value under every valuation are equal. -/
theorem eq_of_forall_toReal_eq {x y : AffAngle} (hx : Normal x) (hy : Normal y)
    (h : ∀ ρ : ℕ → ℝ, x.toReal ρ = y.toReal ρ) : x = y := by
  have hc : x.c = y.c := PiLin.toReal_injective (by simpa [toReal] using h 0)
  have hl : x.coef = y.coef :=
    coef_eq_of_forall_sum_eq _ _ hx.1 hx.2 hy.1 hy.2 fun ρ => by
      have := h ρ
      simp only [toReal, hc] at this
      linarith
  cases x; cases y
  simp_all

end AffAngle

end CatCrypt.Quantum
