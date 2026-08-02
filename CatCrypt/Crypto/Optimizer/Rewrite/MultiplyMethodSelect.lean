/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodEquiv
import CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction

/-!
# Certified cost-minimizing selection over proven-equivalent multiply methods

Given a finite set of multiplication algorithms that are each proved equal to the
same ring product (`MultiplyMethodEquiv`: schoolbook / Karatsuba at two limbs,
schoolbook / Toom-3 at three limbs), this module picks the cheapest one and
carries two certificates:

* **denotation equality** — the chosen method computes the same value as every
  other candidate in the set. The proof is composed through the
  `ProofCarryingExtraction` witness API (`RewriteWitness.ofEq` /
  `RewriteWitness.validate`), so the equality is a kernel-checked certificate,
  not a test vector.
* **cost minimality** — the chosen method's cost is `≤` the cost of every
  candidate in the set, under a cost model that weights each ring multiplication
  by `Egraph.opCost` (the engine's "multiply is the expensive op" weight).

## Scope: finite-set cost-minimum with a certificate

This is the finite-candidate form of "choose the fastest implementation up to
proven equivalence": the candidate set is an explicit list, and selection is an
`argmin` over that list. `select_cost_min` proves the pick is minimal *within the
listed set*; `select_denote_eq` proves it agrees with each listed candidate.

A Level-2 e-graph adds three things this file does not: a union-find with
non-destructive sharing (so one saturated e-class stands in for the enumerated
list), congruence closure (so equivalences of subterms lift to parents without
re-enumeration), and global cost-minimum extraction over that class (rather than
`argmin` over a hand-listed finite set). The certificate machinery
(`RewriteWitness`) and the cost model (`Egraph.opCost`) are already the ones a
Level-2 extractor would reuse; what is missing is the saturated class in place of
the explicit candidate list.

## Cost metric

The multiplication count is the standard metric distinguishing these algorithms
(Karatsuba: 3 vs 4 sub-multiplies at two limbs; Toom-3: 5 vs 9 at three limbs).
Each count is weighted by `Egraph.opCost (.regArith .mul w)` so the model reuses
the engine's op cost rather than an ad-hoc constant.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodSelect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodEquiv
open CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction
open CatCrypt.Crypto.Optimizer.Rewrite

/-! ## 1. Generic minimum selection over a finite candidate list

`argmin cost best cs` folds over `best :: cs` returning an element of minimal
cost. The two lemmas establish it is `≤` every element and is itself a member. -/

section Argmin

variable {γ : Type*} (cost : γ → Nat)

/-- Return the minimum-cost element of `best :: cs`. -/
def argmin (best : γ) : List γ → γ
  | [] => best
  | c :: cs => if cost c < cost best then argmin c cs else argmin best cs

/-- `argmin` never exceeds the seed's cost. -/
theorem argmin_le_best : ∀ (cs : List γ) (best : γ),
    cost (argmin cost best cs) ≤ cost best := by
  intro cs
  induction cs with
  | nil => intro best; simp [argmin]
  | cons c cs ih =>
      intro best
      simp only [argmin]
      split
      · rename_i h; exact le_trans (ih c) (le_of_lt h)
      · exact ih best

/-- `argmin` is `≤` the cost of every element of the tail `cs`. -/
theorem argmin_le_mem : ∀ (cs : List γ) (best x : γ),
    x ∈ cs → cost (argmin cost best cs) ≤ cost x := by
  intro cs
  induction cs with
  | nil => intro best x hx; simp at hx
  | cons c cs ih =>
      intro best x hx
      simp only [argmin]
      rcases List.mem_cons.mp hx with rfl | hx'
      · split
        · exact argmin_le_best cost cs x
        · rename_i h; exact le_trans (argmin_le_best cost cs best) (Nat.le_of_not_lt h)
      · split
        · exact ih c x hx'
        · exact ih best x hx'

/-- `argmin` is `≤` the cost of every element of `best :: cs`. -/
theorem argmin_le (best : γ) (cs : List γ) :
    ∀ x ∈ best :: cs, cost (argmin cost best cs) ≤ cost x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact argmin_le_best cost cs x
  · exact argmin_le_mem cost cs best x hx'

/-- `argmin` returns an element of `best :: cs`. -/
theorem argmin_mem : ∀ (cs : List γ) (best : γ),
    argmin cost best cs ∈ best :: cs := by
  intro cs
  induction cs with
  | nil => intro best; simp [argmin]
  | cons c cs ih =>
      intro best
      simp only [argmin]
      split
      · exact List.mem_cons_of_mem best (ih c)
      · rcases List.mem_cons.mp (ih best) with h | h
        · exact List.mem_cons.mpr (Or.inl h)
        · exact List.mem_cons_of_mem best (List.mem_cons_of_mem c h)

end Argmin

/-! ## 2. Two-limb candidates: schoolbook vs Karatsuba

Each candidate pairs a method with its proof of equality to the two-limb product
`(a1·B + a0)·(b1·B + b0)`, taken from `evalMethod2_eq_product`. -/

section TwoLimb

variable {R : Type*} [CommRing R]

/-- Number of ring multiplications a two-limb method performs. -/
def mul2Count : Mul2Method → Nat
  | .schoolbook => 4
  | .karatsuba => 3

/-- Cost of a two-limb method: its multiply count weighted by the engine's
`mul` op cost (`Egraph.opCost (.regArith .mul 64) = 4`). -/
def mul2Cost (m : Mul2Method) : Nat :=
  mul2Count m * Egraph.opCost (.regArith .mul 64)

/-- A candidate: a two-limb method with its proof of equality to the product. -/
structure Mul2Candidate (B a1 a0 b1 b0 : R) where
  /-- The multiplication method. -/
  method : Mul2Method
  /-- Proof that the method computes the two-limb ring product. -/
  eqProduct : evalMethod2 method B a1 a0 b1 b0 = (a1 * B + a0) * (b1 * B + b0)

/-- The seed candidate (schoolbook). -/
def mul2Head (B a1 a0 b1 b0 : R) : Mul2Candidate B a1 a0 b1 b0 :=
  ⟨.schoolbook, evalMethod2_eq_product .schoolbook B a1 a0 b1 b0⟩

/-- The remaining candidates (Karatsuba). -/
def mul2Tail (B a1 a0 b1 b0 : R) : List (Mul2Candidate B a1 a0 b1 b0) :=
  [⟨.karatsuba, evalMethod2_eq_product .karatsuba B a1 a0 b1 b0⟩]

/-- The full two-limb candidate set. -/
def mul2Candidates (B a1 a0 b1 b0 : R) : List (Mul2Candidate B a1 a0 b1 b0) :=
  mul2Head B a1 a0 b1 b0 :: mul2Tail B a1 a0 b1 b0

/-- Denotation of a two-limb method at fixed operands, as a function of the
method. This is the `f` the `RewriteWitness` certificate is taken over. -/
def eval2F (B a1 a0 b1 b0 : R) : Mul2Method → R :=
  fun m => evalMethod2 m B a1 a0 b1 b0

/-- The certificate that any two methods agree, as a `RewriteWitness` over
`eval2F`. Validates to `evalMethod2 src … = evalMethod2 dst …`. -/
def mul2Witness (B a1 a0 b1 b0 : R) (src dst : Mul2Method) :
    RewriteWitness (eval2F B a1 a0 b1 b0) src dst :=
  RewriteWitness.ofEq (f := eval2F B a1 a0 b1 b0)
    (evalMethod2_agree src dst B a1 a0 b1 b0)

/-- The minimum-cost two-limb candidate. -/
def selectMul2 (B a1 a0 b1 b0 : R) : Mul2Candidate B a1 a0 b1 b0 :=
  argmin (fun cand => mul2Cost cand.method)
    (mul2Head B a1 a0 b1 b0) (mul2Tail B a1 a0 b1 b0)

/-- **Cost minimality.** The selected candidate's cost is `≤` that of every
candidate in the set. -/
theorem select_cost_min (B a1 a0 b1 b0 : R)
    (cand : Mul2Candidate B a1 a0 b1 b0)
    (hcand : cand ∈ mul2Candidates B a1 a0 b1 b0) :
    mul2Cost (selectMul2 B a1 a0 b1 b0).method ≤ mul2Cost cand.method :=
  argmin_le (fun cand => mul2Cost cand.method)
    (mul2Head B a1 a0 b1 b0) (mul2Tail B a1 a0 b1 b0) cand hcand

/-- **Denotation equality (certificate-carrying).** The selected candidate
computes the same value as every candidate in the set. The equality is produced
by validating the `RewriteWitness` from the candidate to the selection, so it is
a kernel-checked certificate. -/
theorem select_denote_eq (B a1 a0 b1 b0 : R)
    (cand : Mul2Candidate B a1 a0 b1 b0)
    (_hcand : cand ∈ mul2Candidates B a1 a0 b1 b0) :
    evalMethod2 (selectMul2 B a1 a0 b1 b0).method B a1 a0 b1 b0
      = evalMethod2 cand.method B a1 a0 b1 b0 :=
  (mul2Witness B a1 a0 b1 b0 (selectMul2 B a1 a0 b1 b0).method cand.method).validate

/-- The selected candidate computes the two-limb product (its own proof). -/
theorem select_eq_product (B a1 a0 b1 b0 : R) :
    evalMethod2 (selectMul2 B a1 a0 b1 b0).method B a1 a0 b1 b0
      = (a1 * B + a0) * (b1 * B + b0) :=
  (selectMul2 B a1 a0 b1 b0).eqProduct

/-- **The selection is Karatsuba** — its multiply count (3) is below schoolbook's
(4), so the cost model prefers it. -/
theorem selectMul2_method (B a1 a0 b1 b0 : R) :
    (selectMul2 B a1 a0 b1 b0).method = .karatsuba := rfl

/-- The selected candidate is a member of the set. -/
theorem selectMul2_mem (B a1 a0 b1 b0 : R) :
    selectMul2 B a1 a0 b1 b0 ∈ mul2Candidates B a1 a0 b1 b0 :=
  argmin_mem _ _ _

end TwoLimb

/-! ## 3. Three-limb candidates: schoolbook vs Toom-3

The field-form Toom-3 needs `6 ≠ 0`, so each three-limb candidate is built under
that hypothesis. The multiply counts are 9 (schoolbook) versus 5 (Toom-3). -/

section ThreeLimb

variable {R : Type*} [Field R]

/-- Number of ring multiplications a three-limb method performs. -/
def mul3Count : Mul3Method → Nat
  | .schoolbook => 9
  | .toom3 => 5

/-- Cost of a three-limb method: its multiply count weighted by the engine's
`mul` op cost. -/
def mul3Cost (m : Mul3Method) : Nat :=
  mul3Count m * Egraph.opCost (.regArith .mul 64)

/-- A candidate: a three-limb method with its proof of equality to the product. -/
structure Mul3Candidate (B a2 a1 a0 b2 b1 b0 : R) where
  /-- The multiplication method. -/
  method : Mul3Method
  /-- Proof that the method computes the three-limb ring product. -/
  eqProduct : evalMethod3 method B a2 a1 a0 b2 b1 b0
    = (a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0)

/-- The seed candidate (schoolbook). -/
def mul3Head (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    Mul3Candidate B a2 a1 a0 b2 b1 b0 :=
  ⟨.schoolbook, evalMethod3_eq_product h6 .schoolbook B a2 a1 a0 b2 b1 b0⟩

/-- The remaining candidates (Toom-3). -/
def mul3Tail (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    List (Mul3Candidate B a2 a1 a0 b2 b1 b0) :=
  [⟨.toom3, evalMethod3_eq_product h6 .toom3 B a2 a1 a0 b2 b1 b0⟩]

/-- The full three-limb candidate set. -/
def mul3Candidates (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    List (Mul3Candidate B a2 a1 a0 b2 b1 b0) :=
  mul3Head h6 B a2 a1 a0 b2 b1 b0 :: mul3Tail h6 B a2 a1 a0 b2 b1 b0

/-- Denotation of a three-limb method at fixed operands. -/
def eval3F (B a2 a1 a0 b2 b1 b0 : R) : Mul3Method → R :=
  fun m => evalMethod3 m B a2 a1 a0 b2 b1 b0

/-- The certificate that any two three-limb methods agree (given `6 ≠ 0`), as a
`RewriteWitness` over `eval3F`. -/
def mul3Witness (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) (src dst : Mul3Method) :
    RewriteWitness (eval3F B a2 a1 a0 b2 b1 b0) src dst :=
  RewriteWitness.ofEq (f := eval3F B a2 a1 a0 b2 b1 b0)
    (evalMethod3_agree h6 src dst B a2 a1 a0 b2 b1 b0)

/-- The minimum-cost three-limb candidate. -/
def selectMul3 (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    Mul3Candidate B a2 a1 a0 b2 b1 b0 :=
  argmin (fun cand => mul3Cost cand.method)
    (mul3Head h6 B a2 a1 a0 b2 b1 b0) (mul3Tail h6 B a2 a1 a0 b2 b1 b0)

/-- **Cost minimality** (three-limb). -/
theorem select3_cost_min (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R)
    (cand : Mul3Candidate B a2 a1 a0 b2 b1 b0)
    (hcand : cand ∈ mul3Candidates h6 B a2 a1 a0 b2 b1 b0) :
    mul3Cost (selectMul3 h6 B a2 a1 a0 b2 b1 b0).method ≤ mul3Cost cand.method :=
  argmin_le (fun cand => mul3Cost cand.method)
    (mul3Head h6 B a2 a1 a0 b2 b1 b0) (mul3Tail h6 B a2 a1 a0 b2 b1 b0) cand hcand

/-- **Denotation equality (certificate-carrying)** (three-limb). -/
theorem select3_denote_eq (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R)
    (cand : Mul3Candidate B a2 a1 a0 b2 b1 b0)
    (_hcand : cand ∈ mul3Candidates h6 B a2 a1 a0 b2 b1 b0) :
    evalMethod3 (selectMul3 h6 B a2 a1 a0 b2 b1 b0).method B a2 a1 a0 b2 b1 b0
      = evalMethod3 cand.method B a2 a1 a0 b2 b1 b0 :=
  (mul3Witness h6 B a2 a1 a0 b2 b1 b0
    (selectMul3 h6 B a2 a1 a0 b2 b1 b0).method cand.method).validate

/-- The selected candidate computes the three-limb product. -/
theorem select3_eq_product (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    evalMethod3 (selectMul3 h6 B a2 a1 a0 b2 b1 b0).method B a2 a1 a0 b2 b1 b0
      = (a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0) :=
  (selectMul3 h6 B a2 a1 a0 b2 b1 b0).eqProduct

/-- **The selection is Toom-3** — its multiply count (5) is below schoolbook's
(9). -/
theorem selectMul3_method (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    (selectMul3 h6 B a2 a1 a0 b2 b1 b0).method = .toom3 := rfl

end ThreeLimb

/-! ## 4. Worked instances over `ℤ` and `ℚ` -/

/-- The two-limb selector picks Karatsuba. -/
example : (selectMul2 (R := ℤ) 10 1 2 3 4).method = .karatsuba := rfl

/-- Over `ℤ` the selected two-limb value is `12·34 = 408` at base `10`. -/
example : evalMethod2 (selectMul2 (R := ℤ) 10 1 2 3 4).method 10 1 2 3 4 = (408 : ℤ) := by
  rw [select_eq_product]; norm_num

/-- The three-limb selector picks Toom-3 (`6 ≠ 0` in `ℚ`). -/
example : (selectMul3 (R := ℚ) (by norm_num) 10 1 2 3 4 5 6).method = .toom3 := rfl

/-- Over `ℚ` the selected three-limb value is `123·456 = 56088` at base `10`. -/
example :
    evalMethod3 (selectMul3 (R := ℚ) (by norm_num) 10 1 2 3 4 5 6).method
      10 1 2 3 4 5 6 = (56088 : ℚ) := by
  rw [select3_eq_product]; norm_num

end CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodSelect
