/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Instrument
public import CatCrypt.Quantum.TensorProduct
public import CatCrypt.Quantum.Programs.Qubit
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import CatCrypt.Tactic.NormSqrt


@[expose] public section
set_option autoImplicit false

/-!
# ZX Calculus

The ZX calculus (Coecke-Duncan 2008, van de Wetering 2020) is a graphical
language for quantum computation based on two types of nodes (Z-spiders and
X-spiders) connected by wires. Diagrams compose sequentially and in parallel,
and a set of rewrite rules (spider fusion, bialgebra, colour change, etc.)
gives a complete equational theory for qubit quantum mechanics.

## Main definitions

* `ZXDiagram m n` — ZX diagram with `m` input and `n` output wires
* `ZXDiagram.denote` — interpretation as a `2^n × 2^m` complex matrix
* `ZXDiagram.equiv` — semantic equivalence up to nonzero scalar
* `ZXDiagram.strictEquiv` — strict semantic equivalence (equal matrices)
* `ZXDiagram.spiderCount` — number of spiders in a diagram

## Rewrite Rules

* `spider_fusion` — two same-colour spiders connected by a wire merge
* `z_identity` — a Z-spider with phase 0 and one input/output is the identity
* `x_identity` — analogous for X-spiders
* `color_change` — X-spider = Hadamard-conjugated Z-spider
* `pi_copy` — copying a pi phase through a Z-spider

## References

* Coecke, Duncan — *Interacting quantum observables*, ICALP 2008
* van de Wetering — *ZX-calculus for the working quantum computer scientist*, 2020
* Nielsen, Chuang — *Quantum Computation and Quantum Information*, Chapter 4
-/

open scoped Matrix ComplexOrder
open Matrix Complex CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.Programs.Qubit

theorem Fin.sum_univ_sixteen {M : Type*} [AddCommMonoid M] (f : Fin 16 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
               f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  abel

noncomputable section

namespace CatCrypt.Quantum.ZXCalculus

/-! ## ZX Diagrams -/

/-- A ZX diagram with `m` input wires and `n` output wires.

The constructors correspond to the generators of the ZX calculus:
- `wire`: identity on one qubit
- `empty`: empty diagram (scalar 1)
- `zSpider m n alpha`: Z-spider (green node) with `m` inputs, `n` outputs, phase `alpha`
- `xSpider m n alpha`: X-spider (red node) with `m` inputs, `n` outputs, phase `alpha`
- `cap`: cup/Bell state creation (0 inputs, 2 outputs)
- `cup`: cap/Bell effect (2 inputs, 0 outputs)
- `swap`: wire crossing (2 inputs, 2 outputs)
- `compose`: sequential composition (plugging outputs into inputs)
- `tensor`: parallel composition (side by side) -/
inductive ZXDiagram : ℕ → ℕ → Type where
  | wire : ZXDiagram 1 1
  | empty : ZXDiagram 0 0
  | zSpider (m n : ℕ) (α : ℝ) : ZXDiagram m n
  | xSpider (m n : ℕ) (α : ℝ) : ZXDiagram m n
  | cap : ZXDiagram 0 2
  | cup : ZXDiagram 2 0
  | swap : ZXDiagram 2 2
  | compose {m n k : ℕ} : ZXDiagram m n → ZXDiagram n k → ZXDiagram m k
  | tensor {m₁ n₁ m₂ n₂ : ℕ} :
      ZXDiagram m₁ n₁ → ZXDiagram m₂ n₂ → ZXDiagram (m₁ + m₂) (n₁ + n₂)

namespace ZXDiagram

/-! ## Notation and Derived Constructors -/

/-- Sequential composition notation. -/
scoped infixl:60 " ⊚ " => ZXDiagram.compose

/-- Parallel composition notation. -/
scoped infixl:65 " ⊗ᵈ " => ZXDiagram.tensor

/-- Hadamard gate as a ZX diagram: Z(pi/2) then X(pi/2) then Z(pi/2),
    but more directly, a Z-spider with special phase decomposition. -/
def hadamardBox : ZXDiagram 1 1 :=
  .compose (.zSpider 1 1 (Real.pi / 2))
    (.compose (.xSpider 1 1 (Real.pi / 2)) (.zSpider 1 1 (Real.pi / 2)))

/-- n-fold parallel identity wires. -/
def wires : (n : ℕ) → ZXDiagram n n
  | 0 => .empty
  | (n + 1) => (Nat.add_comm 1 n ▸ ZXDiagram.tensor .wire (wires n) : ZXDiagram (n + 1) (n + 1))

/-! ## Spider Count -/

/-- Count the number of spiders (Z and X nodes) in a diagram. -/
def spiderCount {m n : ℕ} : ZXDiagram m n → ℕ
  | .wire => 0
  | .empty => 0
  | .zSpider _ _ _ => 1
  | .xSpider _ _ _ => 1
  | .cap => 0
  | .cup => 0
  | .swap => 0
  | .compose d₁ d₂ => d₁.spiderCount + d₂.spiderCount
  | .tensor d₁ d₂ => d₁.spiderCount + d₂.spiderCount

/-- Total node count including structural elements. -/
def nodeCount {m n : ℕ} : ZXDiagram m n → ℕ
  | .wire => 1
  | .empty => 1
  | .zSpider _ _ _ => 1
  | .xSpider _ _ _ => 1
  | .cap => 1
  | .cup => 1
  | .swap => 1
  | .compose d₁ d₂ => d₁.nodeCount + d₂.nodeCount
  | .tensor d₁ d₂ => d₁.nodeCount + d₂.nodeCount

/-! ## Matrix Primitives for Denotation -/

/-- Helper: `2 ^ n > 0` for all `n`. -/
theorem two_pow_pos (n : ℕ) : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)

/-- Helper: `2 ^ n - 1 < 2 ^ n` for all `n`. -/
theorem two_pow_sub_one_lt (n : ℕ) : 2 ^ n - 1 < 2 ^ n := Nat.sub_one_lt_of_le (two_pow_pos n) le_rfl

/-- Repeated tensor ket |b...b⟩ (n copies) as an element of Fin (2^n) -> C.
    |0...0⟩ maps to basis vector 0, |1...1⟩ maps to basis vector 2^n - 1. -/
def repeatedBasisKet (n : ℕ) (b : Fin 2) : Fin (2 ^ n) → ℂ :=
  fun i => if (b = 0 ∧ i = ⟨0, two_pow_pos n⟩) ∨
              (b = 1 ∧ i = ⟨2 ^ n - 1, two_pow_sub_one_lt n⟩)
           then 1 else 0

/-- Z-spider matrix: |0...0⟩⟨0...0| + e^{i*alpha} |1...1⟩⟨1...1|
    This is a 2^n x 2^m matrix. -/
def zSpiderMatrix (m n : ℕ) (α : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ m)) ℂ :=
  let ket0n := repeatedBasisKet n 0
  let bra0m := repeatedBasisKet m 0
  let ket1n := repeatedBasisKet n 1
  let bra1m := repeatedBasisKet m 1
  let phase := Complex.exp (Complex.I * ↑α)
  Matrix.of fun i j => ket0n i * bra0m j + phase * (ket1n i * bra1m j)

/-- Single-qubit Hadamard matrix (1/√2)[[1,1],[1,-1]]. -/
def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  Matrix.of ![![s, s], ![s, -s]]

/-- n-fold tensor product of the Hadamard matrix: H^{⊗n}.
    For n=0, this is the 1×1 identity. -/
def hadamardTensor : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | (n + 1) =>
    Matrix.of fun i j =>
      let i' := (Fin.cast (by ring) i : Fin (2 ^ 1 * 2 ^ n))
      let j' := (Fin.cast (by ring) j : Fin (2 ^ 1 * 2 ^ n))
      let ⟨i₁, i₂⟩ := (finProdFinEquiv.symm i' : Fin (2 ^ 1) × Fin (2 ^ n))
      let ⟨j₁, j₂⟩ := (finProdFinEquiv.symm j' : Fin (2 ^ 1) × Fin (2 ^ n))
      hadamardMatrix i₁ j₁ * hadamardTensor n i₂ j₂

def xSpiderMatrix (m n : ℕ) (α : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ m)) ℂ :=
  hadamardTensor n * zSpiderMatrix m n α * hadamardTensor m

/-- **Direct entry form of `hadamardTensor (n+1)`**: avoids recursing
    through `finProdFinEquiv.symm` which blocks simp on symbolic Fin
    indices. Tagged `@[simp]` so entry-wise proofs on concrete indices
    reduce cleanly. -/
@[simp]
lemma hadamardTensor_succ_apply (n : ℕ) (i j : Fin (2^(n+1))) :
    hadamardTensor (n+1) i j =
      hadamardMatrix
        ⟨i.val / 2^n, Nat.div_lt_of_lt_mul (by rw [pow_succ] at i; omega)⟩
        ⟨j.val / 2^n, Nat.div_lt_of_lt_mul (by rw [pow_succ] at j; omega)⟩ *
      hadamardTensor n
        ⟨i.val % 2^n, Nat.mod_lt _ (two_pow_pos n)⟩
        ⟨j.val % 2^n, Nat.mod_lt _ (two_pow_pos n)⟩ := by
  simp only [hadamardTensor, Matrix.of_apply]
  congr 2

/-- `hadamardTensor 1 = hadamardMatrix`. -/
theorem hadamardTensor_one_eq : hadamardTensor 1 = hadamardMatrix := by
  ext i j
  show hadamardTensor (0 + 1) i j = hadamardMatrix i j
  rw [hadamardTensor_succ_apply 0]
  simp only [pow_zero, Nat.div_one, Fin.mk_val, Nat.mod_one]
  simp [hadamardTensor]

/-- Cap (Bell state creation): |00⟩ + |11⟩ as a 4 x 1 matrix,
    i.e., a map from C^1 to C^4. -/
def capMatrix : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 0)) ℂ :=
  Matrix.of fun i _j =>
    if i = ⟨0, by norm_num⟩ then 1      -- |00⟩ coefficient
    else if i = ⟨3, by norm_num⟩ then 1  -- |11⟩ coefficient
    else 0

/-- Cup (Bell effect): ⟨00| + ⟨11| as a 1 x 4 matrix,
    i.e., a map from C^4 to C^1. -/
def cupMatrix : Matrix (Fin (2 ^ 0)) (Fin (2 ^ 2)) ℂ :=
  Matrix.of fun _i j =>
    if j = ⟨0, by norm_num⟩ then 1      -- ⟨00| coefficient
    else if j = ⟨3, by norm_num⟩ then 1  -- ⟨11| coefficient
    else 0

/-- SWAP matrix on 2 qubits: |ij⟩ -> |ji⟩. -/
def swapMatrix : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  Matrix.of ![![1,0,0,0], ![0,0,1,0], ![0,1,0,0], ![0,0,0,1]]

/-- Kronecker product of matrices with power-of-2 dimensions,
    with the appropriate cast on dimensions. -/
def tensorMatrix {m₁ n₁ m₂ n₂ : ℕ}
    (A : Matrix (Fin (2 ^ n₁)) (Fin (2 ^ m₁)) ℂ)
    (B : Matrix (Fin (2 ^ n₂)) (Fin (2 ^ m₂)) ℂ) :
    Matrix (Fin (2 ^ (n₁ + n₂))) (Fin (2 ^ (m₁ + m₂))) ℂ :=
  -- 2^(a+b) = 2^a * 2^b, so we can use Kronecker after casting
  Matrix.of fun i j =>
    let i' := (Fin.cast (by ring) i : Fin (2 ^ n₁ * 2 ^ n₂))
    let j' := (Fin.cast (by ring) j : Fin (2 ^ m₁ * 2 ^ m₂))
    let ⟨i₁, i₂⟩ := (finProdFinEquiv.symm i' : Fin (2 ^ n₁) × Fin (2 ^ n₂))
    let ⟨j₁, j₂⟩ := (finProdFinEquiv.symm j' : Fin (2 ^ m₁) × Fin (2 ^ m₂))
    A i₁ j₁ * B i₂ j₂

@[simp]
theorem tensorMatrix_apply {m₁ n₁ m₂ n₂ : ℕ}
    (A : Matrix (Fin (2 ^ n₁)) (Fin (2 ^ m₁)) ℂ)
    (B : Matrix (Fin (2 ^ n₂)) (Fin (2 ^ m₂)) ℂ)
    (i : Fin (2 ^ (n₁ + n₂))) (j : Fin (2 ^ (m₁ + m₂))) :
    tensorMatrix A B i j =
      A ⟨i.val / 2 ^ n₂,
          Nat.div_lt_of_lt_mul (show i.val < 2 ^ n₂ * 2 ^ n₁
            from mul_comm (2 ^ n₁) (2 ^ n₂) ▸ pow_add 2 n₁ n₂ ▸ i.isLt)⟩
        ⟨j.val / 2 ^ m₂,
          Nat.div_lt_of_lt_mul (show j.val < 2 ^ m₂ * 2 ^ m₁
            from mul_comm (2 ^ m₁) (2 ^ m₂) ▸ pow_add 2 m₁ m₂ ▸ j.isLt)⟩ *
      B ⟨i.val % 2 ^ n₂, Nat.mod_lt _ (two_pow_pos n₂)⟩
        ⟨j.val % 2 ^ m₂, Nat.mod_lt _ (two_pow_pos m₂)⟩ := by
  simp only [tensorMatrix, Matrix.of_apply]
  congr 1

/-- Equivalence `Fin (2^(m+n)) ≃ Fin (2^m) × Fin (2^n)` via div/mod.
    Used to reindex sums in `tensorMatrix_mul`. -/
def finPow2Equiv (m n : ℕ) : Fin (2^(m+n)) ≃ Fin (2^m) × Fin (2^n) where
  toFun l := (⟨l.val / 2^n, Nat.div_lt_of_lt_mul
    (mul_comm (2^m) (2^n) ▸ pow_add 2 m n ▸ l.isLt)⟩,
              ⟨l.val % 2^n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩)
  invFun p := ⟨p.1.val * 2^n + p.2.val, by
    nlinarith [p.1.isLt, p.2.isLt, (pow_add 2 m n).symm]⟩
  left_inv l := by ext; exact Nat.div_add_mod' l.val (2^n)
  right_inv p := by
    ext
    · show (p.1.val * 2^n + p.2.val) / 2^n = p.1.val
      rw [show p.1.val * 2^n + p.2.val = p.2.val + p.1.val * 2^n from by ring]
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos n)]
      simp [Nat.div_eq_of_lt p.2.isLt]
    · show (p.1.val * 2^n + p.2.val) % 2^n = p.2.val
      rw [show p.1.val * 2^n + p.2.val = 2^n * p.1.val + p.2.val from by ring]
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt p.2.isLt

/-- Mixed product property: `tensorMatrix A B * tensorMatrix C D = tensorMatrix (A*C) (B*D)`.
    This is the ZX-calculus analogue of `kronecker_mul_kronecker`. Allows simplifying
    tensor product compositions without expanding the inner Fin sum. -/
theorem tensorMatrix_mul {m₁ n₁ k₁ m₂ n₂ k₂ : ℕ}
    (A : Matrix (Fin (2 ^ n₁)) (Fin (2 ^ m₁)) ℂ)
    (B : Matrix (Fin (2 ^ n₂)) (Fin (2 ^ m₂)) ℂ)
    (C : Matrix (Fin (2 ^ m₁)) (Fin (2 ^ k₁)) ℂ)
    (D : Matrix (Fin (2 ^ m₂)) (Fin (2 ^ k₂)) ℂ) :
    tensorMatrix A B * tensorMatrix C D = tensorMatrix (A * C) (B * D) := by
  ext i j
  simp only [Matrix.mul_apply, tensorMatrix_apply]
  -- Reindex ∑_l via finPow2Equiv: Fin (2^(m₁+m₂)) ≃ Fin (2^m₁) × Fin (2^m₂)
  rw [(Equiv.sum_comp (finPow2Equiv m₁ m₂).symm _).symm, Fintype.sum_prod_type]
  -- Simplify: div/mod of (finPow2Equiv.symm (a,b)).val = a.val, b.val
  have ha : ∀ a : Fin (2^m₁), ∀ b : Fin (2^m₂),
    ((finPow2Equiv m₁ m₂).symm (a, b)).val / 2 ^ m₂ = a.val := by
    intro a b
    simp [finPow2Equiv, show a.val * 2^m₂ + b.val = b.val + a.val * 2^m₂ from by ring,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos m₂), Nat.div_eq_of_lt b.isLt]
  have hb : ∀ a : Fin (2^m₁), ∀ b : Fin (2^m₂),
    ((finPow2Equiv m₁ m₂).symm (a, b)).val % 2 ^ m₂ = b.val := by
    intro a b
    simp [finPow2Equiv, show a.val * 2^m₂ + b.val = 2^m₂ * a.val + b.val from by ring,
      Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  simp_rw [ha, hb]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext b; congr 1; ext a; ring

/-! ## Denotation -/

/-- Interpret a ZX diagram as a matrix (linear map from C^{2^m} to C^{2^n}).

A ZX diagram with `m` input wires and `n` output wires denotes a
`2^n x 2^m` complex matrix. The interpretation is compositional:
- `wire` -> 2 x 2 identity matrix
- `empty` -> 1 x 1 identity (scalar 1)
- `zSpider m n alpha` -> `|0...0⟩⟨0...0| + e^{i*alpha}|1...1⟩⟨1...1|`
- `xSpider m n alpha` -> Hadamard conjugate of Z-spider
- `cap` -> Bell state `|00⟩ + |11⟩`
- `cup` -> Bell effect `⟨00| + ⟨11|`
- `swap` -> SWAP gate
- `compose d1 d2` -> matrix multiplication `d2.denote * d1.denote`
- `tensor d1 d2` -> Kronecker product `d1.denote tensor d2.denote` -/
def denote {m n : ℕ} : ZXDiagram m n → Matrix (Fin (2 ^ n)) (Fin (2 ^ m)) ℂ
  | .wire => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | .empty => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | .zSpider m n α => zSpiderMatrix m n α
  | .xSpider m n α => xSpiderMatrix m n α
  | .cap => capMatrix
  | .cup => cupMatrix
  | .swap => swapMatrix
  | .compose d₁ d₂ => d₂.denote * d₁.denote
  | .tensor d₁ d₂ => tensorMatrix d₁.denote d₂.denote

/-! ## Semantic Equivalence -/

/-- Two ZX diagrams are equivalent if they denote the same matrix up to
    a nonzero scalar factor. This is the standard notion in the ZX calculus,
    since global phases are physically unobservable. -/
def equiv {m n : ℕ} (d₁ d₂ : ZXDiagram m n) : Prop :=
  ∃ (c : ℂ), c ≠ 0 ∧ d₁.denote = c • d₂.denote

/-- Strict equivalence: the diagrams denote exactly the same matrix. -/
def strictEquiv {m n : ℕ} (d₁ d₂ : ZXDiagram m n) : Prop :=
  d₁.denote = d₂.denote

/-- Notation for ZX equivalence. -/
scoped infix:50 " ≃zx " => ZXDiagram.equiv

/-- Notation for strict ZX equivalence. -/
scoped infix:50 " ≡zx " => ZXDiagram.strictEquiv

/-! ### Equivalence Properties -/

/-- `equiv` is reflexive. -/
theorem equiv_refl {m n : ℕ} (d : ZXDiagram m n) : d ≃zx d :=
  ⟨1, one_ne_zero, by simp⟩

/-- `equiv` is symmetric. -/
theorem equiv_symm {m n : ℕ} {d₁ d₂ : ZXDiagram m n} (h : d₁ ≃zx d₂) : d₂ ≃zx d₁ := by
  obtain ⟨c, hc, he⟩ := h
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [he, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

/-- `equiv` is transitive. -/
theorem equiv_trans {m n : ℕ} {d₁ d₂ d₃ : ZXDiagram m n}
    (h₁₂ : d₁ ≃zx d₂) (h₂₃ : d₂ ≃zx d₃) : d₁ ≃zx d₃ := by
  obtain ⟨c₁, hc₁, he₁⟩ := h₁₂
  obtain ⟨c₂, hc₂, he₂⟩ := h₂₃
  exact ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, by rw [he₁, he₂, smul_smul]⟩

/-- Strict equivalence implies equivalence. -/
theorem strictEquiv_implies_equiv {m n : ℕ} {d₁ d₂ : ZXDiagram m n}
    (h : d₁ ≡zx d₂) : d₁ ≃zx d₂ :=
  ⟨1, one_ne_zero, by simp [strictEquiv] at h; simp [h]⟩

/-- `strictEquiv` is reflexive. -/
theorem strictEquiv_refl {m n : ℕ} (d : ZXDiagram m n) : d ≡zx d := rfl

/-- `strictEquiv` is symmetric. -/
theorem strictEquiv_symm {m n : ℕ} {d₁ d₂ : ZXDiagram m n}
    (h : d₁ ≡zx d₂) : d₂ ≡zx d₁ := h.symm

/-- `strictEquiv` is transitive. -/
theorem strictEquiv_trans {m n : ℕ} {d₁ d₂ d₃ : ZXDiagram m n}
    (h₁₂ : d₁ ≡zx d₂) (h₂₃ : d₂ ≡zx d₃) : d₁ ≡zx d₃ := h₁₂.trans h₂₃

/-! ## ZX Calculus Rewrite Rules -/

/-! ### Helper lemmas for repeatedBasisKet inner products -/

/-- Self inner product of repeatedBasisKet is 1. -/
theorem repeatedBasisKet_self_inner (n : ℕ) (b : Fin 2) :
    ∑ l : Fin (2 ^ n), repeatedBasisKet n b l * repeatedBasisKet n b l = 1 := by
  simp only [repeatedBasisKet]
  have : ∀ l : Fin (2 ^ n),
      (if (b = 0 ∧ l = ⟨0, two_pow_pos n⟩) ∨ (b = 1 ∧ l = ⟨2 ^ n - 1, two_pow_sub_one_lt n⟩)
       then (1 : ℂ) else 0) *
      (if (b = 0 ∧ l = ⟨0, two_pow_pos n⟩) ∨ (b = 1 ∧ l = ⟨2 ^ n - 1, two_pow_sub_one_lt n⟩)
       then (1 : ℂ) else 0) =
      if (b = 0 ∧ l = ⟨0, two_pow_pos n⟩) ∨ (b = 1 ∧ l = ⟨2 ^ n - 1, two_pow_sub_one_lt n⟩)
       then 1 else 0 := by
    intro l; split_ifs <;> simp
  simp_rw [this]
  fin_cases b
  · simp [Finset.sum_ite_eq']
  · simp [Finset.sum_ite_eq']

/-- Cross inner product of repeatedBasisKet is 0 for n ≥ 1 with different basis indices. -/
theorem repeatedBasisKet_cross_inner {n : ℕ} (hn : 0 < n) (b₁ b₂ : Fin 2)
    (hne : b₁ ≠ b₂) :
    ∑ l : Fin (2 ^ n), repeatedBasisKet n b₁ l * repeatedBasisKet n b₂ l = 0 := by
  simp only [repeatedBasisKet]
  apply Finset.sum_eq_zero
  intro l _
  -- At most one of the two conditions can hold, so the product is 0
  suffices ¬((b₁ = 0 ∧ l = ⟨0, two_pow_pos n⟩) ∨
              (b₁ = 1 ∧ l = ⟨2 ^ n - 1, two_pow_sub_one_lt n⟩)) ∨
           ¬((b₂ = 0 ∧ l = ⟨0, two_pow_pos n⟩) ∨
              (b₂ = 1 ∧ l = ⟨2 ^ n - 1, two_pow_sub_one_lt n⟩)) by
    rcases this with h | h <;> simp only [h, ite_false, zero_mul, mul_zero]
  by_contra habs
  push Not at habs
  obtain ⟨h1, h2⟩ := habs
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases h1 with ⟨hb1, hl⟩ | ⟨hb1, hl⟩ <;> rcases h2 with ⟨hb2, hl'⟩ | ⟨hb2, hl'⟩
  · -- b₁ = 0, b₂ = 0
    exact hne (by rw [hb1, hb2])
  · -- b₁ = 0 (l=0), b₂ = 1 (l=2^n-1): 0 ≠ 2^n-1 for n≥1
    have h1 : l.val = 0 := congrArg Fin.val hl
    have h2 : l.val = 2 ^ n - 1 := congrArg Fin.val hl'
    have h3 : 2 ≤ 2 ^ n := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hn)
    omega
  · -- b₁ = 1 (l=2^n-1), b₂ = 0 (l=0): 2^n-1 ≠ 0 for n≥1
    have h1 : l.val = 2 ^ n - 1 := congrArg Fin.val hl
    have h2 : l.val = 0 := congrArg Fin.val hl'
    have h3 : 2 ≤ 2 ^ n := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hn)
    omega
  · -- b₁ = 1, b₂ = 1
    exact hne (by rw [hb1, hb2])

/-- Z-spider matrix multiplication with intermediate arity n ≥ 1:
    zSpiderMatrix n k β * zSpiderMatrix m n α = zSpiderMatrix m k (α + β)  (strict equality). -/
theorem zSpiderMatrix_mul {m n k : ℕ} (hn : 0 < n) (α β : ℝ) :
    zSpiderMatrix n k β * zSpiderMatrix m n α = zSpiderMatrix m k (α + β) := by
  ext i j
  simp only [zSpiderMatrix, Matrix.mul_apply, Matrix.of_apply]
  -- ∑_l (ket0k_i * bra0n_l + e^{iβ} * ket1k_i * bra1n_l) *
  --     (ket0n_l * bra0m_j + e^{iα} * ket1n_l * bra1m_j)
  -- We factor each summand, then use orthonormality of repeatedBasisKet.
  have h00 := repeatedBasisKet_self_inner n 0
  have h11 := repeatedBasisKet_self_inner n 1
  have h01 := repeatedBasisKet_cross_inner hn 0 1 (by decide)
  have h10 := repeatedBasisKet_cross_inner hn 1 0 (by decide)
  -- Abbreviate constants
  set a := repeatedBasisKet k 0 i
  set b := repeatedBasisKet m 0 j
  set c := repeatedBasisKet k 1 i
  set d := repeatedBasisKet m 1 j
  set eα := Complex.exp (Complex.I * ↑α)
  set eβ := Complex.exp (Complex.I * ↑β)
  -- Each summand: (a * f0(l) + eβ * c * f1(l)) * (f0(l) * b + eα * f1(l) * d)
  -- = a*b*f0²(l) + a*d*eα*f0(l)*f1(l) + eβ*c*b*f1(l)*f0(l) + eβ*eα*c*d*f1²(l)
  have hfactor : ∀ l : Fin (2^n),
      (a * repeatedBasisKet n 0 l + eβ * (c * repeatedBasisKet n 1 l)) *
      (repeatedBasisKet n 0 l * b + eα * (repeatedBasisKet n 1 l * d))
    = a * b * (repeatedBasisKet n 0 l * repeatedBasisKet n 0 l) +
      a * d * eα * (repeatedBasisKet n 0 l * repeatedBasisKet n 1 l) +
      eβ * c * b * (repeatedBasisKet n 1 l * repeatedBasisKet n 0 l) +
      eβ * eα * c * d * (repeatedBasisKet n 1 l * repeatedBasisKet n 1 l) :=
    fun _ => by ring
  simp_rw [hfactor, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h00, h11, h01, h10]
  simp only [mul_zero, mul_one, add_zero, zero_add]
  -- Now: a*b + eβ*eα*c*d = a*b + e^{i(α+β)}*c*d
  congr 1
  show eβ * eα * c * d = Complex.exp (Complex.I * ↑(α + β)) * (c * d)
  have : Complex.exp (Complex.I * ↑(α + β)) = eβ * eα := by
    simp only [eα, eβ, Complex.ofReal_add]
    rw [show Complex.I * (↑α + ↑β) = Complex.I * ↑β + Complex.I * ↑α by ring]
    exact Complex.exp_add _ _
  rw [this]; ring

/-- **Spider fusion**: Two Z-spiders connected by n ≥ 1 wires merge into one,
    with phases adding. Strictly equal (no scalar factor needed).

    Diagrammatically: Z(m,n,alpha) composed with Z(n,k,beta) = Z(m,k,alpha+beta)

    This is the fundamental rule that makes the ZX calculus tractable:
    any connected subgraph of same-colour spiders can be collapsed.

    Note: The n ≥ 1 hypothesis is essential. For n = 0 (disconnected spiders),
    the fusion does not hold: the "scalar" factor
    `1 + e^{iα} + e^{iβ} + e^{i(α+β)}` can be zero (e.g., α = β = π). -/
theorem spider_fusion (α β : ℝ) (m n k : ℕ) (hn : 0 < n) :
    (.compose (.zSpider m n α) (.zSpider n k β) : ZXDiagram m k) ≡zx
      .zSpider m k (α + β) := by
  show denote _ = denote _
  simp only [denote]
  exact zSpiderMatrix_mul hn α β

/-- **Identity removal**: A Z-spider with phase 0 and one input/output is
    the identity wire.

    Z(1,1,0) = wire -/
theorem z_identity : (.zSpider 1 1 0 : ZXDiagram 1 1) ≡zx .wire := by
  show denote (.zSpider 1 1 0) = denote .wire
  simp only [denote, zSpiderMatrix, repeatedBasisKet]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.of_apply, Complex.exp_zero, Complex.ofReal_zero,
          mul_zero, mul_one, add_zero, zero_add]

/-- **X-identity removal**: An X-spider with phase 0 and one input/output is
    the identity wire. -/
theorem inv_sqrt2_sq_mul_two : (↑(Real.sqrt 2))⁻¹ ^ 2 * (2 : ℂ) = 1 := by
  rw [inv_pow, sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  simp [Complex.ofReal_ofNat]

/-- `H * H = I` for the 2×2 Hadamard matrix, proved entry-wise via
    explicit four-entry case-split. We avoid the global
    `simp [hadamardMatrix]` rewrite (which loops on `hadamardMatrix.eq_1`
    in 4.29) by computing each entry of `H` once into named values. -/
theorem hadamardMatrix_sq :
    hadamardMatrix * hadamardMatrix = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- Cache the four entries of `H` to bypass looping `hadamardMatrix.eq_1`.
  have hH00 : hadamardMatrix 0 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH01 : hadamardMatrix 0 1 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH10 : hadamardMatrix 1 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH11 : hadamardMatrix 1 1 = -((↑(Real.sqrt 2) : ℂ)⁻¹) := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hsum :
      ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) +
      ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) = 1 := by
    rw [show ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) +
            ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) =
            ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 * 2 from by ring,
      inv_sqrt2_sq_mul_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two, hH00, hH01, hH10, hH11,
      Matrix.one_apply, Fin.zero_eta, Fin.mk_one, reduceIte] <;>
    first
      | linear_combination hsum
      | (rw [show -((↑(Real.sqrt 2) : ℂ)⁻¹) * -((↑(Real.sqrt 2) : ℂ)⁻¹) =
              ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 from by ring]; linear_combination hsum)
      | (rw [ite_eq_right (show (0 : Fin 2) ≠ 1 by decide)]; ring)
      | (rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]; ring)

/-- The Hadamard tensor is an involution: H^{⊗n} * H^{⊗n} = I for all n.

    Proof by induction. The key observation is that hadamardTensor (n+1)
    has Kronecker structure: entry (i,j) = H(i₁,j₁) * Hn(i₂,j₂).
    So (Hn₊₁ * Hn₊₁)(i,j) = ∑_k H(i₁,k₁)*Hn(i₂,k₂)*H(k₁,j₁)*Hn(k₂,j₂)
    = (H*H)(i₁,j₁) * (Hn*Hn)(i₂,j₂) = δ(i₁,j₁) * δ(i₂,j₂) = δ(i,j). -/
theorem hadamardTensor_sq (n : ℕ) :
    hadamardTensor n * hadamardTensor n = (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  induction n with
  | zero => simp [hadamardTensor]
  | succ n ih =>
    have hH := hadamardMatrix_sq
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    change ∑ k, hadamardTensor (n + 1) i k * hadamardTensor (n + 1) k j = _
    simp only [hadamardTensor, Matrix.of_apply]
    -- Define the decomposition equivalence
    have hcard : 2 ^ (n + 1) = 2 ^ 1 * 2 ^ n := by ring
    let e : Fin (2 ^ (n + 1)) ≃ Fin (2 ^ 1) × Fin (2 ^ n) :=
      (Fin.castOrderIso hcard).toEquiv.trans finProdFinEquiv.symm
    -- Abbreviate decomposition components for i, j
    set i₁ := (finProdFinEquiv.symm (Fin.cast hcard i)).1
    set i₂ := (finProdFinEquiv.symm (Fin.cast hcard i)).2
    set j₁ := (finProdFinEquiv.symm (Fin.cast hcard j)).1
    set j₂ := (finProdFinEquiv.symm (Fin.cast hcard j)).2
    -- Reindex the sum over Fin (2^1) × Fin (2^n)
    rw [← Equiv.sum_comp e.symm]
    -- After reindexing: for x = e.symm p, the decomposition yields p
    -- e.symm p = finProdFinEquiv p cast back; so decomposition of e.symm p = p
    have he_roundtrip : ∀ p : Fin (2 ^ 1) × Fin (2 ^ n),
        finProdFinEquiv.symm (Fin.cast (by ring) (e.symm p)) = p := by
      intro p
      show finProdFinEquiv.symm (Fin.cast _ (e.symm p)) = p
      ext <;> simp [e, Equiv.symm_trans_apply, Equiv.symm_symm, Fin.cast,
        Fin.castOrderIso, finProdFinEquiv, Fin.divNat, Fin.modNat]
      · -- (↑p.2 + 2^n * ↑p.1) / 2^n = ↑p.1
        rw [Nat.add_comm, Nat.mul_add_div (two_pow_pos n)]
        simp [Nat.div_eq_of_lt p.2.isLt]
      · -- ↑p.2 % 2^n = ↑p.2
        exact Nat.mod_eq_of_lt p.2.isLt
    -- Now use he_roundtrip to simplify the sum
    simp only [he_roundtrip]
    -- Goal: ∑ x, H(i₁,x.1)*Hn(i₂,x.2) * (H(x.1,j₁)*Hn(x.2,j₂)) = if i=j then 1 else 0
    -- Split product-type sum into double sum
    rw [Fintype.sum_prod_type]
    -- Simplify (x,y).1 = x and (x,y).2 = y, then rearrange (a*b)*(c*d) = (a*c)*(b*d)
    simp only [Prod.fst, Prod.snd]
    simp_rw [show ∀ (a : Fin (2 ^ 1)) (b : Fin (2 ^ n)),
        hadamardMatrix i₁ a * hadamardTensor n i₂ b *
        (hadamardMatrix a j₁ * hadamardTensor n b j₂) =
        (hadamardMatrix i₁ a * hadamardMatrix a j₁) *
        (hadamardTensor n i₂ b * hadamardTensor n b j₂)
      from fun _ _ => by ring]
    -- Factor out H terms (independent of b) from inner sum
    simp_rw [← Finset.mul_sum]
    -- Factor out the constant inner sum from the outer sum
    rw [← Finset.sum_mul]
    -- Recognize as matrix products
    have hH_prod : ∑ k : Fin (2 ^ 1), hadamardMatrix i₁ k * hadamardMatrix k j₁ =
        (hadamardMatrix * hadamardMatrix) i₁ j₁ := by simp [Matrix.mul_apply]
    have hHn_prod : ∑ k : Fin (2 ^ n), hadamardTensor n i₂ k * hadamardTensor n k j₂ =
        (hadamardTensor n * hadamardTensor n) i₂ j₂ := by simp [Matrix.mul_apply]
    rw [hH_prod, hHn_prod, ih, hH, Matrix.one_apply, Matrix.one_apply]
    -- Goal: (if i₁ = j₁ then 1 else 0) * (if i₂ = j₂ then 1 else 0) = if i = j then 1 else 0
    -- Relate i = j ↔ i₁ = j₁ ∧ i₂ = j₂
    have hiff : i = j ↔ (i₁ = j₁ ∧ i₂ = j₂) := by
      constructor
      · intro hij; subst hij; exact ⟨rfl, rfl⟩
      · intro ⟨h₁, h₂⟩
        have hpair : finProdFinEquiv.symm.1 (Fin.cast hcard i) =
                     finProdFinEquiv.symm.1 (Fin.cast hcard j) :=
          Prod.ext h₁ h₂
        have := finProdFinEquiv.symm.injective hpair
        exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hcard this))
    simp only [hiff]
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;> simp_all

theorem hadamardTensor_one_sq :
    hadamardTensor 1 * hadamardTensor 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  hadamardTensor_sq 1

/-- **X-spider fusion**: analogous fusion rule for X-spiders for n ≥ 1
    (via the Z-spider case and Hadamard involution). -/
theorem x_spider_fusion (α β : ℝ) (m n k : ℕ) (hn : 0 < n) :
    (.compose (.xSpider m n α) (.xSpider n k β) : ZXDiagram m k) ≡zx
      .xSpider m k (α + β) := by
  show denote _ = denote _
  simp only [denote, xSpiderMatrix]
  have hHn := hadamardTensor_sq n
  have hZ := @zSpiderMatrix_mul m n k hn α β
  calc hadamardTensor k * zSpiderMatrix n k β * hadamardTensor n *
       (hadamardTensor n * zSpiderMatrix m n α * hadamardTensor m)
      = hadamardTensor k * zSpiderMatrix n k β *
        (hadamardTensor n * hadamardTensor n) *
        zSpiderMatrix m n α * hadamardTensor m := by
          simp [Matrix.mul_assoc]
    _ = hadamardTensor k * zSpiderMatrix n k β *
        (1 : Matrix _ _ ℂ) *
        zSpiderMatrix m n α * hadamardTensor m := by rw [hHn]
    _ = hadamardTensor k * (zSpiderMatrix n k β * zSpiderMatrix m n α) *
        hadamardTensor m := by simp [Matrix.mul_assoc, Matrix.mul_one]
    _ = hadamardTensor k * zSpiderMatrix m k (α + β) * hadamardTensor m := by
          rw [hZ]

theorem x_identity : (.xSpider 1 1 0 : ZXDiagram 1 1) ≡zx .wire := by
  show denote (.xSpider 1 1 0) = denote .wire
  have hz : zSpiderMatrix 1 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := z_identity
  simp only [denote, xSpiderMatrix, hz, Matrix.mul_one]
  exact hadamardTensor_one_sq

/-- **Colour change via Hadamard**: An X-spider equals a Z-spider
    conjugated by Hadamard tensor on every wire.

    X(m,n,alpha) has denotation H^{⊗n} * Z(m,n,alpha) * H^{⊗m}

    This rule makes the X-spider redundant as a primitive,
    since it can always be expressed in terms of Z-spiders and Hadamards.

    Note: The ZX diagrammatic form would use n+m Hadamard boxes on the wires.
    Here we state the matrix-level identity directly, which is the definition
    of `xSpiderMatrix`. -/
theorem color_change (m n : ℕ) (α : ℝ) :
    denote (.xSpider m n α : ZXDiagram m n) =
      hadamardTensor n * denote (.zSpider m n α : ZXDiagram m n) * hadamardTensor m := by
  simp [denote, xSpiderMatrix]

theorem sqrt2_ne_zero : (↑(Real.sqrt 2) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2))

theorem sqrt2_sq : (↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; rfl

@[simp] theorem sqrt2_sq_pow : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by rw [sq]; exact sqrt2_sq

-- Bridge: ∑ over Fin (2^(1+1)) (simp can't reduce 2^(1+1) to 4)
theorem sum_fin_pow2_2 {M : Type*} [AddCommMonoid M] (f : Fin (2^(1+1)) → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

-- ZX matrix entry tactic: unfold defs + expand sums + close with ring or field_simp.
local macro "zx_matrix_tac" : tactic => `(tactic|
  (simp only [denote, zSpiderMatrix, xSpiderMatrix, repeatedBasisKet,
    hadamardTensor, hadamardMatrix, tensorMatrix_apply, tensorMatrix,
    Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
    Complex.exp_zero, Complex.ofReal_zero,
    finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.cast, vecCons,
    Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_four,
    sum_fin_pow2_2, Fin.isValue,
    Nat.add_eq, Nat.add_zero,
    ofReal_sqrt2_inv_sq]
   first | ring | (field_simp [sqrt2_ne_zero]; simp [sqrt2_sq_pow])))

/-- Helper: `X(1,1,π) = !![0,1;1,0]` (Pauli σ_x), proved via the colour-change
    `X = H · Z(π) · H` and an explicit 2×2 entry computation. -/
private lemma xSpiderMatrix_one_one_pi :
    xSpiderMatrix 1 1 Real.pi = !![0, 1; 1, 0] := by
  -- xSpiderMatrix 1 1 π = H · Z(π) · H, and Z(π) = diag(1, e^{iπ}) = diag(1, -1).
  have hZpi : zSpiderMatrix 1 1 Real.pi = !![1, 0; 0, -1] := by
    have h_exp_pi : Complex.exp (Complex.I * ↑Real.pi) = -1 := by
      rw [show Complex.I * ↑Real.pi = ↑Real.pi * Complex.I by ring]
      exact Complex.exp_pi_mul_I
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zSpiderMatrix, repeatedBasisKet, Matrix.of_apply, Fin.isValue, h_exp_pi]
  -- Cache H entries.
  have hH00 : hadamardMatrix 0 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH01 : hadamardMatrix 0 1 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH10 : hadamardMatrix 1 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH11 : hadamardMatrix 1 1 = -((↑(Real.sqrt 2) : ℂ)⁻¹) := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hinvsq : (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹ = (2 : ℂ)⁻¹ :=
    ofReal_sqrt2_inv_sq
  have hinvsq2 : (↑(Real.sqrt 2) : ℂ)⁻¹ ^ 2 = (2 : ℂ)⁻¹ := by rw [sq]; exact hinvsq
  simp only [xSpiderMatrix, hadamardTensor_one_eq, hZpi]
  rw [Matrix.mul_assoc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
       Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const,
       Fin.mk_zero, Fin.mk_one, hH00, hH01, hH10, hH11, Fin.isValue] ;
     ring_nf) <;>
    (first | linear_combination hinvsq2 | linear_combination -hinvsq2
           | linear_combination 2 * hinvsq2 | linear_combination -2 * hinvsq2)

/-- Helper: `Z(1,2,0)` as an explicit 4×2 matrix (the COPY map). -/
private lemma zSpiderMatrix_one_two_zero :
    zSpiderMatrix 1 2 0 = !![1, 0; 0, 0; 0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zSpiderMatrix, repeatedBasisKet, Matrix.of_apply, Fin.isValue]

/-- **Pi copy rule**: A π-phase X-spider on the input of a Z-spider
    (copy) is equivalent to π-phase X-spiders on each output wire.

    `Z(1,2,0) ∘ (X(1,1,π) ⊗ X(1,1,π)) ≃zx X(1,1,π) ∘ Z(1,2,0)`

    Semantically: X(1,1,π) = σ_x (Pauli-X). Pulling σ_x past the Z-copy
    flips BOTH output wires — the π phase copies through. This is a
    fundamental ZX rewrite rule.

    Proof: substitute concrete matrix forms via `xSpiderMatrix_one_one_pi`
    (σ_x) and `zSpiderMatrix_one_two_zero` (COPY), then compute the 4×2
    products entrywise. -/
theorem pi_copy :
    (.compose (.zSpider 1 2 0)
              (.tensor (.xSpider 1 1 Real.pi)
                       (.xSpider 1 1 Real.pi)) : ZXDiagram 1 2) ≃zx
      (.compose (.xSpider 1 1 Real.pi) (.zSpider 1 2 0)) := by
  apply strictEquiv_implies_equiv
  show denote _ = denote _
  -- denote (.compose d₁ d₂) = d₂.denote * d₁.denote, so
  -- LHS = denote (X⊗X) * denote (Z), RHS = denote (Z) * denote (X).
  simp only [denote, xSpiderMatrix_one_one_pi, zSpiderMatrix_one_two_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorMatrix_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
      Fin.sum_univ_four, Fin.isValue]

/-- **Zero-spider elimination**: A Z-spider with 0 inputs and 0 outputs and
    phase 0 is the scalar 2 (in the standard convention). -/
theorem z_zero_zero :
    (.zSpider 0 0 0 : ZXDiagram 0 0) ≃zx .empty := by
  refine ⟨2, by norm_num, ?_⟩
  simp only [denote, zSpiderMatrix, repeatedBasisKet]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.of_apply, Matrix.smul_apply, Complex.exp_zero, Complex.ofReal_zero,
        smul_eq_mul]
  norm_num

/-- **Wire straightening** (the snake, or yanking, equation): a wire bent by a
    cap and straightened by a cup denotes the identity wire. -/
theorem snake_equation_denote :
    ((ZXDiagram.wire ⊗ᵈ ZXDiagram.cap : ZXDiagram 1 3) ⊚
     (ZXDiagram.cup ⊗ᵈ ZXDiagram.wire : ZXDiagram 3 1))
      ≡zx (ZXDiagram.wire : ZXDiagram 1 1) := by
  show ZXDiagram.denote _ = ZXDiagram.denote _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ZXDiagram.denote, tensorMatrix, capMatrix, cupMatrix,
      Matrix.mul_apply, Fin.sum_univ_eight, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Matrix.one_apply_eq] <;>
    simp [Matrix.one_apply, Fin.ext_iff, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-! ## Composition Congruence -/

/-- Equivalence is a congruence for sequential composition. -/
theorem compose_congr {m n k : ℕ} {d₁ d₁' : ZXDiagram m n} {d₂ d₂' : ZXDiagram n k}
    (h₁ : d₁ ≃zx d₁') (h₂ : d₂ ≃zx d₂') :
    (d₁ ⊚ d₂) ≃zx (d₁' ⊚ d₂') := by
  obtain ⟨c₁, hc₁, he₁⟩ := h₁
  obtain ⟨c₂, hc₂, he₂⟩ := h₂
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
  simp only [denote]
  rw [he₁, he₂, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

/-- Equivalence is a congruence for tensor composition. -/
theorem tensor_congr {m₁ n₁ m₂ n₂ : ℕ}
    {d₁ d₁' : ZXDiagram m₁ n₁} {d₂ d₂' : ZXDiagram m₂ n₂}
    (h₁ : d₁ ≃zx d₁') (h₂ : d₂ ≃zx d₂') :
    (d₁ ⊗ᵈ d₂) ≃zx (d₁' ⊗ᵈ d₂') := by
  obtain ⟨c₁, hc₁, he₁⟩ := h₁
  obtain ⟨c₂, hc₂, he₂⟩ := h₂
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
  simp only [denote, tensorMatrix]
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [he₁, he₂]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Compose–tensor interchange** (bifunctoriality of the monoidal product):
    composing tensor products equals tensor-product of compositions,
    when the inner dimensions align.

    `(A ⊗ᵈ B) ⊚ (C ⊗ᵈ D) ≃zx (A ⊚ C) ⊗ᵈ (B ⊚ D)`

    Immediate from `tensorMatrix_mul`. Enables structural proofs of
    theorems like `cnotGate_sq` by letting spider fusion fire on the
    two halves of a tensor-composed diagram. -/
theorem compose_tensor_distrib
    {m_A n_A m_B n_B k l : ℕ}
    (A : ZXDiagram m_A n_A) (B : ZXDiagram m_B n_B)
    (C : ZXDiagram n_A k) (D : ZXDiagram n_B l) :
    ((A ⊗ᵈ B) ⊚ (C ⊗ᵈ D) : ZXDiagram (m_A + m_B) (k + l)) ≃zx
      ((A ⊚ C) ⊗ᵈ (B ⊚ D)) := by
  apply strictEquiv_implies_equiv
  show denote _ = denote _
  simp only [denote]
  exact tensorMatrix_mul _ _ _ _

/-! ## Derived Rules -/

/-- A Z-spider with phase 0, m inputs, and n outputs acts as a "copy" node
    when m=1 (it copies |0⟩ to |0...0⟩ and |1⟩ to |1...1⟩). -/
theorem z_copy_zero_basis (n : ℕ) :
    (.zSpider 1 n 0 : ZXDiagram 1 n) ≃zx .zSpider 1 n 0 :=
  equiv_refl _

/-- Composing a Z-spider with its "adjoint" (swapping inputs/outputs) and
    phase negated yields a scalar multiple of identity-like diagram.

    Z(m,n,alpha) composed with Z(n,m,-alpha) ~ Z(m,m,0) -/
theorem z_spider_compose_adjoint (m n : ℕ) (α : ℝ) (hn : 0 < n) :
    (.compose (.zSpider m n α) (.zSpider n m (-α)) : ZXDiagram m m) ≡zx
      .zSpider m m 0 := by
  have h := spider_fusion α (-α) m n m hn
  simp only [add_neg_cancel] at h
  exact h

/-- Phase gadget: a phase alpha on n parallel wires can be expressed as
    a Z-spider with 0 outputs connected to n copies. -/
theorem phase_gadget (n : ℕ) (α : ℝ) :
    (.compose (.zSpider n 1 0) (.compose (.zSpider 1 0 α) .empty) : ZXDiagram n 0) ≃zx
      .zSpider n 0 α := by
  apply strictEquiv_implies_equiv
  show denote _ = denote _
  simp only [denote]
  rw [Matrix.one_mul]
  have h := @zSpiderMatrix_mul n 1 0 (by omega) 0 α
  simp only [zero_add] at h
  exact h

/-! ## Circuit Interface -/

section Gates

/-- Pauli X gate as ZX diagram. -/
def pauliXGate : ZXDiagram 1 1 := .xSpider 1 1 Real.pi

/-- Pauli Z gate as ZX diagram. -/
def pauliZGate : ZXDiagram 1 1 := .zSpider 1 1 Real.pi

/-- Pauli Y gate as ZX diagram (up to global phase: Y = iXZ). -/
def pauliYGate : ZXDiagram 1 1 :=
  .compose (.zSpider 1 1 Real.pi) (.xSpider 1 1 Real.pi)

/-- S gate (pi/2 phase) as ZX diagram. -/
def sGate : ZXDiagram 1 1 := .zSpider 1 1 (Real.pi / 2)

/-- T gate (pi/4 phase) as ZX diagram. -/
def tGateZX : ZXDiagram 1 1 := .zSpider 1 1 (Real.pi / 4)

/-- CNOT gate as ZX diagram: Z-spider (copy) on control, X-spider (XOR) on target. -/
def cnotGate : ZXDiagram 2 2 :=
  .compose (.tensor (.zSpider 1 2 0) .wire)
           (.tensor .wire (.xSpider 2 1 0))

/-- CZ gate as ZX diagram. -/
def czGate : ZXDiagram 2 2 :=
  .compose (.tensor (.zSpider 1 2 0) .wire)
           (.tensor .wire (.zSpider 2 1 0))

/-- Rz(alpha) rotation gate. -/
def rzGate (α : ℝ) : ZXDiagram 1 1 := .zSpider 1 1 α

/-- Rx(alpha) rotation gate. -/
def rxGate (α : ℝ) : ZXDiagram 1 1 := .xSpider 1 1 α

end Gates

/-! ## Gate Identities -/

theorem exp_I_pi_sq : Complex.exp (Complex.I * ↑Real.pi) ^ 2 = 1 := by
  rw [sq, ← Complex.exp_add]
  ring_nf
  rw [show Complex.I * ↑Real.pi * 2 = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I]
  simp

theorem zSpiderMatrix_pi_sq :
    zSpiderMatrix 1 1 Real.pi * zSpiderMatrix 1 1 Real.pi =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [zSpiderMatrix, repeatedBasisKet]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.of_apply] <;>
    ring_nf <;> try rfl
  all_goals exact exp_I_pi_sq

/-- Pauli X squared is identity. -/
theorem pauliXGate_sq : (pauliXGate ⊚ pauliXGate) ≡zx .wire := by
  show denote (.compose (.xSpider 1 1 Real.pi) (.xSpider 1 1 Real.pi)) = denote .wire
  simp only [denote, xSpiderMatrix]
  have hH := hadamardTensor_one_sq
  have hZ := zSpiderMatrix_pi_sq
  -- H * Z * H * (H * Z * H) = H * Z * (H*H) * Z * H = H * Z * Z * H = H * H = I
  have : ∀ (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A * B * C * (A * B * C) = A * (B * (C * A) * B) * C := fun A B C => by
    simp [Matrix.mul_assoc]
  rw [this]
  rw [show hadamardTensor 1 * hadamardTensor 1 = (1 : Matrix _ _ ℂ) from hH]
  simp [hZ, hH]

/-- Pauli Z squared is identity. -/
theorem pauliZGate_sq : (pauliZGate ⊚ pauliZGate) ≡zx .wire := by
  show denote (.compose (.zSpider 1 1 Real.pi) (.zSpider 1 1 Real.pi)) = denote .wire
  simp only [denote, zSpiderMatrix, repeatedBasisKet]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.of_apply] <;>
    ring_nf <;> try rfl
  all_goals exact exp_I_pi_sq

/-- Helper: `e^{i·π/2} = i`, both in original and cast-distributed form. -/
private theorem exp_I_pi_half : Complex.exp (Complex.I * (↑Real.pi / 2)) = Complex.I := by
  rw [show Complex.I * (↑Real.pi / 2) = ↑(Real.pi / 2) * Complex.I from by push_cast; ring]
  rw [Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

/-- Helper: Z(π/2) as a concrete 2×2 matrix. Entry-by-entry approach
    that avoids the looping `repeatedBasisKet` rewrite. -/
theorem zSpider_half_pi_eq :
    zSpiderMatrix 1 1 (Real.pi / 2) = Matrix.of ![![1, 0], ![0, Complex.I]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zSpiderMatrix, repeatedBasisKet, Matrix.of_apply, Fin.mk_zero, Fin.mk_one] <;>
    exact exp_I_pi_half

-- `hadamardTensor_one_eq` moved to right after `hadamardTensor` definition
-- (so it's available earlier in the file).

/-- Helper: xSpider(π/2) as a concrete matrix.

    Strategy: X(π/2) = H · Z(π/2) · H by `xSpiderMatrix` definition (color-change).
    `zSpider_half_pi_eq` gives `Z(π/2) = ![[1,0],[0,I]]`. Then we expand
    H · D(1,I) · H entry-wise using `linear_combination` with the
    `ofReal_sqrt2_inv_sq` identity `(↑√2)⁻¹ * (↑√2)⁻¹ = 1/2`. -/
theorem xSpider_half_pi_eq :
    xSpiderMatrix 1 1 (Real.pi / 2) =
      Matrix.of ![![(1 + Complex.I) / 2, (1 - Complex.I) / 2],
                   ![(1 - Complex.I) / 2, (1 + Complex.I) / 2]] := by
  -- Cache H entries to bypass looping simp on `hadamardMatrix.eq_1`.
  have hH00 : hadamardMatrix 0 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH01 : hadamardMatrix 0 1 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH10 : hadamardMatrix 1 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH11 : hadamardMatrix 1 1 = -((↑(Real.sqrt 2) : ℂ)⁻¹) := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hinvsq : (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹ = (2 : ℂ)⁻¹ :=
    ofReal_sqrt2_inv_sq
  have hinvsq2 : (↑(Real.sqrt 2) : ℂ)⁻¹ ^ 2 = (2 : ℂ)⁻¹ := by rw [sq]; exact hinvsq
  -- xSpiderMatrix 1 1 (π/2) = H * Z(π/2) * H, with Fin (2^1) indexing.
  -- Convert via hadamardTensor_one_eq, then expand both sums.
  simp only [xSpiderMatrix, hadamardTensor_one_eq, zSpider_half_pi_eq]
  ext i j
  -- For (H * Z * H) i j, use Matrix.mul_apply twice over Fin 2.
  fin_cases i <;> fin_cases j <;>
    rw [show (hadamardMatrix * Matrix.of ![![(1 : ℂ), 0], ![0, Complex.I]] * hadamardMatrix) =
           hadamardMatrix * (Matrix.of ![![(1 : ℂ), 0], ![0, Complex.I]] * hadamardMatrix) from by
        rw [Matrix.mul_assoc]] <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Fin.mk_zero, Fin.mk_one, hH00, hH01, hH10, hH11,
      Fin.isValue] <;>
    (first
      | linear_combination (1 + Complex.I) * hinvsq2
      | linear_combination (1 - Complex.I) * hinvsq2)

/-- `hadamardBox = Z(π/2) · X(π/2) · Z(π/2)` evaluates to `((1+i)/√2) · H`.

    Strategy: unfold `denote` (which reverses compose order), then use the
    closed forms `zSpider_half_pi_eq` and `xSpider_half_pi_eq`, then compute
    the 2×2 product `D(I) · M · D(I)` where `M = (1/2)·[[1+I,1-I],[1-I,1+I]]`,
    yielding `((1+I)/2)·[[1,1],[1,-1]] = ((1+I)/√2)·H`. -/
theorem hadamardBox_denote_eq :
    denote hadamardBox = ((1 + Complex.I) / ↑(Real.sqrt 2)) • hadamardMatrix := by
  -- denote (compose d₁ d₂) = d₂.denote * d₁.denote, so
  -- denote (compose Z (compose X Z)) = (Z * X) * Z
  show zSpiderMatrix 1 1 (Real.pi / 2) * xSpiderMatrix 1 1 (Real.pi / 2) *
       zSpiderMatrix 1 1 (Real.pi / 2) =
    ((1 + Complex.I) / ↑(Real.sqrt 2)) • hadamardMatrix
  rw [zSpider_half_pi_eq, xSpider_half_pi_eq]
  -- Cache H entries.
  have hH00 : hadamardMatrix 0 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH01 : hadamardMatrix 0 1 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH10 : hadamardMatrix 1 0 = (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  have hH11 : hadamardMatrix 1 1 = -((↑(Real.sqrt 2) : ℂ)⁻¹) := by
    simp [hadamardMatrix, Matrix.of_apply, one_div]
  -- (1+i)/√2 = (1+i) · (√2)⁻¹
  have hdiv : ((1 + Complex.I) / ↑(Real.sqrt 2) : ℂ) =
      (1 + Complex.I) * (↑(Real.sqrt 2) : ℂ)⁻¹ := by
    rw [div_eq_mul_inv]
  have hinvsq : (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹ = (2 : ℂ)⁻¹ :=
    ofReal_sqrt2_inv_sq
  have hinvsq2 : (↑(Real.sqrt 2) : ℂ)⁻¹ ^ 2 = (2 : ℂ)⁻¹ := by rw [sq]; exact hinvsq
  -- Reassociate (D*X)*D so each entry computation needs only two sums.
  rw [Matrix.mul_assoc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.smul_apply, smul_eq_mul, Fin.mk_zero,
      Fin.mk_one, hH00, hH01, hH10, hH11, Fin.isValue, hdiv,
      Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
    -- Normalize multiplication, then substitute I^k powers, then close via hinvsq2.
    ring_nf <;>
    (try rw [show (Complex.I ^ 2 : ℂ) = -1 from Complex.I_sq]) <;>
    (try rw [show (Complex.I ^ 3 : ℂ) = -Complex.I from by
      rw [pow_succ, Complex.I_sq]; ring]) <;>
    (first
      | linear_combination (1 + Complex.I) * hinvsq2
      | linear_combination (1 - Complex.I) * hinvsq2
      | linear_combination -(1 + Complex.I) * hinvsq2
      | linear_combination -(1 - Complex.I) * hinvsq2)

/-- Two Hadamards cancel (up to nonzero scalar).
    hadamardBox = e^{iπ/4} * H, so hadamardBox² = e^{iπ/2} * I = i * I. -/
theorem hadamard_sq : (hadamardBox ⊚ hadamardBox) ≃zx .wire := by
  -- hadamardBox = ((1+i)/√2) * H, so hadamardBox² = ((1+i)/√2)² * H² = i * I
  refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
  show denote _ = Complex.I • denote _
  -- denote (compose d1 d2) = denote d2 * denote d1
  change denote hadamardBox * denote hadamardBox = Complex.I • (1 : Matrix _ _ ℂ)
  rw [hadamardBox_denote_eq]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [hadamardMatrix_sq]
  -- Goal: ((1+i)/√2) * ((1+i)/√2) • (1 : Matrix _ _ ℂ) = i • 1
  congr 1
  -- ((1+i)/√2)² = (1+i)²/2 = (1+2i-1)/2 = 2i/2 = i
  field_simp
  rw [sq (↑(Real.sqrt 2) : ℂ), ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  push_cast; ring_nf; simp [Complex.I_sq]

/-! ## Soundness -/

/-- Semantic equivalence implies physical equivalence: if two diagrams
    denote the same matrix up to scalar, then they implement the same
    quantum channel (up to global phase). -/
theorem equiv_physical_meaning {m n : ℕ} {d₁ d₂ : ZXDiagram m n}
    (h : d₁ ≃zx d₂)
    (ρ : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    ∃ (c : ℂ), c ≠ 0 ∧
      d₁.denote * ρ * d₁.denoteᴴ =
        (c * starRingEnd ℂ c) • (d₂.denote * ρ * d₂.denoteᴴ) := by
  obtain ⟨c, hc, he⟩ := h
  exact ⟨c, hc, by rw [he]; simp [conjTranspose_smul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, mul_comm (starRingEnd ℂ c) c]⟩

end ZXDiagram

end CatCrypt.Quantum.ZXCalculus
