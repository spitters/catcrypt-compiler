/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.ExpIBall
public import CatCrypt.Quantum.Synthesis.ZYZPass
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Enclosures of gate matrices and the residual checkers

The computable counterparts, in ball arithmetic, of the `2 × 2` matrix of a one-qubit gate,
of `KAKPass.pairMat` and of `KAKPass.blockMat`: `gate1B g`, `pairB i j g` and `blockB i j gs`
enclose the matrices of gates whose angles are exact (`Gate.RzQ`, and the fixed gates); a
real-valued `Gate.Rz` has no enclosure (`none`). `runB gs` encloses the `2 × 2` matrix
`runMat gs` of a list of one-qubit gates.

`embedGate2 n i j · hij` and `embedGate1 n q ·` are unital star-algebra homomorphisms
(`embed2Hom`, `embed1Hom`), so they do not increase the `ℓ²` operator norm (C⋆-algebra
homomorphisms are contractive, `NonUnitalStarAlgHom.norm_apply_le`). A bound on
`‖R - e^{iφ} G‖` for the `4 × 4` (or `2 × 2`) matrices of a block and of its replacement is
therefore a bound on the same difference of their `2^n × 2^n` matrices.

`checkPair i j gs rs φ` computes such a bound `ε` for a block `gs` and its replacement `rs` on
the pair `(i, j)` and the phase `φ`, after checking that both act on `(i, j)` only;
`checkRun q gs rs φ` does the same for one-qubit runs on `q`.

## Main definitions

* `gate1B`, `pairB`, `blockB`, `runB`, `runMat`.
* `embed2Hom`, `embed1Hom`.
* `checkPair`, `checkRun`.

## Main results

* `memM_pairB`, `memM_blockB`, `memM_gate1B`, `memM_runB` — soundness of the enclosures.
* `listMatrix_eq_embedGate1_runMat` — a run of one-qubit gates on `q` is `embedGate1` of its
  `2 × 2` matrix.
* `norm_embedGate2_le`, `norm_embedGate1_le` — the embeddings are contractive in the `ℓ²`
  operator norm.
* `norm_sub_le_checkPair`, `norm_sub_le_checkRun` — the checkers bound
  `‖listMatrix rs - e^{iφ} • listMatrix gs‖`.
-/

@[expose] public section

set_option autoImplicit false

open Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Synthesis.KAK CatCrypt.Quantum.Synthesis.KAKPass
open CatCrypt.Quantum.Synthesis.ZYZPass CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil)

namespace CatCrypt.Quantum.Synthesis.IntervalArith

open CBall BMat

variable {n : ℕ}

/-! ## Literal matrices -/

/-- The `2 × 2` matrix of balls with rows `(a, b)` and `(c, d)`. -/
def lit2 (a b c d : CBall) : BMat 2 := ofFn ![![a, b], ![c, d]]

theorem memM_lit2 {a b c d : ℂ} {A B C D : CBall} (ha : Mem a A) (hb : Mem b B) (hc : Mem c C)
    (hd : Mem d D) : MemM (Matrix.of ![![a, b], ![c, d]]) (lit2 A B C D) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa [lit2]

/-- The vector of four balls. -/
theorem mem_vec4 {a b c d : ℂ} {A B C D : CBall} (ha : Mem a A) (hb : Mem b B) (hc : Mem c C)
    (hd : Mem d D) : ∀ j, Mem (![a, b, c, d] j) (![A, B, C, D] j) := by
  intro j
  fin_cases j <;> simpa

/-- The `4 × 4` matrix of balls with the rows `r0`, `r1`, `r2`, `r3`. -/
def lit4 (r0 r1 r2 r3 : Fin 4 → CBall) : BMat 4 := ofFn ![r0, r1, r2, r3]

theorem memM_lit4 {r0 r1 r2 r3 : Fin 4 → ℂ} {R0 R1 R2 R3 : Fin 4 → CBall}
    (h0 : ∀ j, Mem (r0 j) (R0 j)) (h1 : ∀ j, Mem (r1 j) (R1 j)) (h2 : ∀ j, Mem (r2 j) (R2 j))
    (h3 : ∀ j, Mem (r3 j) (R3 j)) : MemM (Matrix.of ![r0, r1, r2, r3]) (lit4 R0 R1 R2 R3) := by
  intro i j
  fin_cases i
  · simpa [lit4] using h0 j
  · simpa [lit4] using h1 j
  · simpa [lit4] using h2 j
  · simpa [lit4] using h3 j

theorem mem_neg_one : Mem (-1) (neg CBall.one) := mem_neg mem_one

/-! ## One-qubit gates -/

/-- The Hadamard matrix. -/
def hadB : BMat 2 := lit2 invSqrt2 invSqrt2 invSqrt2 (neg invSqrt2)
/-- The Pauli `X` matrix. -/
def xB : BMat 2 := lit2 CBall.zero CBall.one CBall.one CBall.zero
/-- The Pauli `Y` matrix. -/
def yB : BMat 2 := lit2 CBall.zero (neg iI) iI CBall.zero
/-- The Pauli `Z` matrix. -/
def zB : BMat 2 := lit2 CBall.one CBall.zero CBall.zero (neg CBall.one)
/-- The phase gate `S`. -/
def sB : BMat 2 := lit2 CBall.one CBall.zero CBall.zero iI
/-- The rotation `diag(1, e^{iθ})` at the exact angle `θ`. -/
def rzB (p : PiLin) : BMat 2 := lit2 CBall.one CBall.zero CBall.zero (expIBall p)

theorem memM_hadB : MemM Programs.Qubit.hadamard hadB :=
  memM_lit2 mem_invSqrt2 mem_invSqrt2 mem_invSqrt2 (mem_neg mem_invSqrt2)

theorem memM_xB : MemM Programs.Qubit.pauliX xB := memM_lit2 mem_zero mem_one mem_one mem_zero

theorem memM_yB : MemM Programs.Qubit.pauliY yB :=
  memM_lit2 mem_zero (mem_neg mem_iI) mem_iI mem_zero

theorem memM_zB : MemM Programs.Qubit.pauliZ zB :=
  memM_lit2 mem_one mem_zero mem_zero mem_neg_one

theorem memM_sB : MemM Programs.Qubit.phaseS sB := memM_lit2 mem_one mem_zero mem_zero mem_iI

theorem memM_rzB (p : PiLin) : MemM (rzGate (PiLin.toReal p)) (rzB p) :=
  memM_lit2 mem_one mem_zero mem_zero (mem_expIBall p)

theorem memM_tB : MemM Programs.Qubit.tGate (rzB (PiLin.ofPi (1 / 4))) := by
  have h := memM_rzB (PiLin.ofPi (1 / 4))
  have ht : PiLin.toReal (PiLin.ofPi (1 / 4)) = Real.pi / 4 := by
    rw [PiLin.toReal_ofPi]; push_cast; ring
  rwa [ht] at h

theorem memM_tdgB : MemM tDaggerGate (rzB (PiLin.ofPi (-(1 / 4)))) := by
  have h := memM_rzB (PiLin.ofPi (-(1 / 4)))
  have ht : PiLin.toReal (PiLin.ofPi (-(1 / 4))) = -(Real.pi / 4) := by
    rw [PiLin.toReal_ofPi]; push_cast; ring
  rw [ht] at h
  have he : tDaggerGate = rzGate (-(Real.pi / 4)) := by
    simp only [tDaggerGate, rzGate]
    push_cast
    ring_nf
  rwa [he]

/-- The `2 × 2` matrix of a one-qubit gate with an exact angle; `none` for a real-valued
`Rz` and for the two-qubit gates. -/
def gate1B : Gate n → Option (BMat 2)
  | .H _ => some hadB
  | .X _ => some xB
  | .Y _ => some yB
  | .Z _ => some zB
  | .T _ => some (rzB (PiLin.ofPi (1 / 4)))
  | .Tdg _ => some (rzB (PiLin.ofPi (-(1 / 4))))
  | .S _ => some sB
  | .RzQ _ a => some (rzB a)
  | .Rz _ _ => none
  | .CNOT _ _ => none
  | .CZ _ _ => none

/-- The `2 × 2` matrix of a gate: `gateMatrix1`, and the identity for a two-qubit gate. -/
noncomputable def mat1 (g : Gate n) : Matrix (Fin 2) (Fin 2) ℂ := (gateMatrix1 g).getD 1

theorem memM_gate1B {g : Gate n} {B : BMat 2} (h : gate1B g = some B) : MemM (mat1 g) B := by
  cases g <;> simp only [gate1B, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [mat1, gateMatrix1, Option.getD_some]
  · exact memM_hadB
  · exact memM_xB
  · exact memM_yB
  · exact memM_zB
  · exact memM_tB
  · exact memM_tdgB
  · exact memM_sB
  · exact memM_rzB _

theorem gateEmbedding_eq_embedGate1_mat1 {g : Gate n} {q : Fin n} (h : oneQ? g = some q) :
    gateEmbedding g = embedGate1 n q (mat1 g) := by
  cases g <;> simp only [oneQ?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- The `2 × 2` matrix of a list of one-qubit gates; the head gate acts first. -/
noncomputable def runMat : List (Gate n) → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | g :: l => runMat l * mat1 g

theorem listMatrix_eq_embedGate1_runMat {q : Fin n} {l : List (Gate n)}
    (hl : ∀ g ∈ l, oneQ? g = some q) : listMatrix l = embedGate1 n q (runMat l) := by
  induction l with
  | nil => rw [listMatrix_nil, runMat, embedGate1_one]
  | cons g l ih =>
    rw [listMatrix_cons, ih (fun x hx => hl x (List.mem_cons_of_mem g hx)),
      gateEmbedding_eq_embedGate1_mat1 (hl g List.mem_cons_self), embedGate1_mul, runMat]

/-- The `2 × 2` matrix of balls of a list of one-qubit gates with exact angles. -/
def runB : List (Gate n) → Option (BMat 2)
  | [] => some BMat.one
  | g :: l => do
    let B ← runB l
    let G ← gate1B g
    pure (BMat.mul B G)

theorem memM_runB : ∀ {l : List (Gate n)} {B : BMat 2}, runB l = some B → MemM (runMat l) B
  | [], B, h => by
    simp only [runB, Option.some.injEq] at h
    subst h
    exact memM_one
  | g :: l, B, h => by
    simp only [runB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B', hB', G, hG, rfl⟩ := h
    exact memM_mul (memM_runB hB') (memM_gate1B hG)

/-! ## Gates on a pair -/

/-- The exact `4 × 4` matrix of `CNOT`. -/
def cnotB : BMat 4 :=
  lit4 ![CBall.one, CBall.zero, CBall.zero, CBall.zero]
    ![CBall.zero, CBall.one, CBall.zero, CBall.zero]
    ![CBall.zero, CBall.zero, CBall.zero, CBall.one]
    ![CBall.zero, CBall.zero, CBall.one, CBall.zero]

/-- The exact `4 × 4` matrix of `SWAP`. -/
def swapB : BMat 4 :=
  lit4 ![CBall.one, CBall.zero, CBall.zero, CBall.zero]
    ![CBall.zero, CBall.zero, CBall.one, CBall.zero]
    ![CBall.zero, CBall.one, CBall.zero, CBall.zero]
    ![CBall.zero, CBall.zero, CBall.zero, CBall.one]

/-- The exact `4 × 4` matrix of `CZ`. -/
def czB : BMat 4 :=
  lit4 ![CBall.one, CBall.zero, CBall.zero, CBall.zero]
    ![CBall.zero, CBall.one, CBall.zero, CBall.zero]
    ![CBall.zero, CBall.zero, CBall.one, CBall.zero]
    ![CBall.zero, CBall.zero, CBall.zero, neg CBall.one]

theorem memM_cnotB : MemM Programs.Qubit.cnot cnotB :=
  memM_lit4 (mem_vec4 mem_one mem_zero mem_zero mem_zero)
    (mem_vec4 mem_zero mem_one mem_zero mem_zero)
    (mem_vec4 mem_zero mem_zero mem_zero mem_one) (mem_vec4 mem_zero mem_zero mem_one mem_zero)

theorem memM_swapB : MemM Programs.Qubit.swap swapB :=
  memM_lit4 (mem_vec4 mem_one mem_zero mem_zero mem_zero)
    (mem_vec4 mem_zero mem_zero mem_one mem_zero)
    (mem_vec4 mem_zero mem_one mem_zero mem_zero) (mem_vec4 mem_zero mem_zero mem_zero mem_one)

theorem memM_czB : MemM czGate czB :=
  memM_lit4 (mem_vec4 mem_one mem_zero mem_zero mem_zero)
    (mem_vec4 mem_zero mem_one mem_zero mem_zero)
    (mem_vec4 mem_zero mem_zero mem_one mem_zero)
    (mem_vec4 mem_zero mem_zero mem_zero mem_neg_one)

/-- The matrix of balls of `side i q A`: `A ⊗ 1` on the high qubit `i`, `1 ⊗ A` otherwise. -/
def sideB (i q : Fin n) (A : BMat 2) : BMat 4 :=
  if q = i then BMat.kron (b := 2) A BMat.one else BMat.kron (a := 2) BMat.one A

theorem memM_sideB (i q : Fin n) {A : Matrix (Fin 2) (Fin 2) ℂ} {A' : BMat 2} (h : MemM A A') :
    MemM (side i q A) (sideB i q A') := by
  unfold side sideB
  split
  · exact memM_kron h memM_one
  · exact memM_kron memM_one h

/-- The matrix of balls of `pairMat i j g`; `none` for a real-valued `Rz`. -/
def pairB (i _j : Fin n) : Gate n → Option (BMat 4)
  | .H q => some (sideB i q hadB)
  | .X q => some (sideB i q xB)
  | .Y q => some (sideB i q yB)
  | .Z q => some (sideB i q zB)
  | .T q => some (sideB i q (rzB (PiLin.ofPi (1 / 4))))
  | .Tdg q => some (sideB i q (rzB (PiLin.ofPi (-(1 / 4)))))
  | .S q => some (sideB i q sB)
  | .Rz _ _ => none
  | .RzQ q a => some (sideB i q (rzB a))
  | .CNOT a b =>
    some (if a = b then BMat.one else if a = i then cnotB
      else BMat.mul (BMat.mul swapB cnotB) swapB)
  | .CZ a b =>
    some (if a = b then BMat.one else if a = i then czB else BMat.mul (BMat.mul swapB czB) swapB)

theorem memM_pairB {i j : Fin n} {g : Gate n} {B : BMat 4} (h : pairB i j g = some B) :
    MemM (pairMat i j g) B := by
  cases g <;> simp only [pairB, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [pairMat]
  · exact memM_sideB i _ memM_hadB
  · exact memM_sideB i _ memM_xB
  · exact memM_sideB i _ memM_yB
  · exact memM_sideB i _ memM_zB
  · exact memM_sideB i _ memM_tB
  · exact memM_sideB i _ memM_tdgB
  · exact memM_sideB i _ memM_sB
  · split
    · exact memM_one
    · split
      · exact memM_cnotB
      · exact memM_mul (memM_mul memM_swapB memM_cnotB) memM_swapB
  · split
    · exact memM_one
    · split
      · exact memM_czB
      · exact memM_mul (memM_mul memM_swapB memM_czB) memM_swapB
  · exact memM_sideB i _ (memM_rzB _)

/-- The matrix of balls of `blockMat i j l`; `none` when a gate has no enclosure. -/
def blockB (i j : Fin n) : List (Gate n) → Option (BMat 4)
  | [] => some BMat.one
  | g :: l => do
    let B ← blockB i j l
    let P ← pairB i j g
    pure (BMat.mul B P)

theorem memM_blockB {i j : Fin n} :
    ∀ {l : List (Gate n)} {B : BMat 4}, blockB i j l = some B → MemM (blockMat i j l) B
  | [], B, h => by
    simp only [blockB, Option.some.injEq] at h
    subst h
    exact memM_one
  | g :: l, B, h => by
    simp only [blockB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B', hB', P, hP, rfl⟩ := h
    exact memM_mul (memM_blockB hB') (memM_pairB hP)

/-! ## The embeddings are contractive -/

theorem embedGate2_add (i j : Fin n) (G H : Matrix (Fin 4) (Fin 4) ℂ) (hij : i ≠ j) :
    embedGate2 n i j (G + H) hij = embedGate2 n i j G hij + embedGate2 n i j H hij := by
  simp only [embedGate2]
  funext r c
  simp only [Matrix.of_apply, Matrix.add_apply]
  split <;> simp

/-- `embedGate2 n i j · hij` as a unital star-algebra homomorphism. -/
noncomputable def embed2Hom (i j : Fin n) (hij : i ≠ j) :
    Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ where
  toFun G := embedGate2 n i j G hij
  map_one' := embedGate2_one n i j hij
  map_mul' G H := (embedGate2_mul n i j G H hij).symm
  map_zero' := by simpa using embedGate2_smul i j 0 0 hij
  map_add' G H := embedGate2_add i j G H hij
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [embedGate2_smul, embedGate2_one]
  map_star' G := by
    simp only [Matrix.star_eq_conjTranspose]
    exact (embedGate2_conjTranspose n i j G hij).symm

/-- `embedGate1 n q ·` as a unital star-algebra homomorphism. -/
noncomputable def embed1Hom (q : Fin n) :
    Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ where
  toFun G := embedGate1 n q G
  map_one' := embedGate1_one n q
  map_mul' G H := (embedGate1_mul n q G H).symm
  map_zero' := embedGate1_map_zero q
  map_add' G H := embedGate1_map_add q G H
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [embedGate1_smul, embedGate1_one]
  map_star' G := by
    simp only [Matrix.star_eq_conjTranspose]
    exact (embedGate1_conjTranspose n q G).symm

open scoped Matrix.Norms.L2Operator

theorem norm_embedGate2_le (i j : Fin n) (hij : i ≠ j) (G : Matrix (Fin 4) (Fin 4) ℂ) :
    ‖embedGate2 n i j G hij‖ ≤ ‖G‖ :=
  NonUnitalStarAlgHom.norm_apply_le (embed2Hom i j hij) G

theorem norm_embedGate1_le (q : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖embedGate1 n q G‖ ≤ ‖G‖ :=
  NonUnitalStarAlgHom.norm_apply_le (embed1Hom q) G

/-! ## The checkers -/

/-- The residual checker of a block: for gate lists `gs` and `rs` on the distinct qubits
`(i, j)` with enclosed matrices, the bound `bnorm` of the enclosure of
`blockMat rs - e^{iφ} blockMat gs`; `none` otherwise. -/
def checkPair (i j : Fin n) (gs rs : List (Gate n)) (φ : PiLin) : Option ℚ :=
  if i ≠ j ∧ gs.all (onPair i j) = true ∧ rs.all (onPair i j) = true then do
    let G ← blockB i j gs
    let R ← blockB i j rs
    pure (bnorm (BMat.sub R (BMat.smul (expIBall φ) G)))
  else none

/-- **Soundness of the block checker.** If `checkPair i j gs rs φ = some ε`, the matrices of
`rs` and `gs` on `n` qubits satisfy `‖listMatrix rs - e^{iφ} • listMatrix gs‖ ≤ ε` in the
`ℓ²` operator norm. -/
theorem norm_sub_le_checkPair {i j : Fin n} {gs rs : List (Gate n)} {φ : PiLin} {ε : ℚ}
    (h : checkPair i j gs rs φ = some ε) :
    ‖listMatrix rs - exp (I * (PiLin.toReal φ : ℂ)) • listMatrix gs‖ ≤ (ε : ℝ) := by
  unfold checkPair at h
  split at h
  · next hc =>
    obtain ⟨hij, hgs, hrs⟩ := hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨G, hG, R, hR, rfl⟩ := h
    have hgs' : ∀ g ∈ gs, onPair i j g = true := List.all_eq_true.mp hgs
    have hrs' : ∀ g ∈ rs, onPair i j g = true := List.all_eq_true.mp hrs
    rw [listMatrix_eq_embedGate2 hij hgs', listMatrix_eq_embedGate2 hij hrs']
    have he : embedGate2 n i j (blockMat i j rs) hij -
        exp (I * (PiLin.toReal φ : ℂ)) • embedGate2 n i j (blockMat i j gs) hij =
        embed2Hom i j hij (blockMat i j rs - exp (I * (PiLin.toReal φ : ℂ)) • blockMat i j gs) := by
      rw [map_sub, map_smul]
      rfl
    rw [he]
    refine (NonUnitalStarAlgHom.norm_apply_le (embed2Hom i j hij) _).trans ?_
    exact norm_le_bnorm (memM_sub (memM_blockB hR) (memM_smul (mem_expIBall φ) (memM_blockB hG)))
  · exact absurd h (by simp)

/-- The residual checker of a one-qubit run: for gate lists `gs` and `rs` of one-qubit gates
on `q` with enclosed matrices, the bound `bnorm` of the enclosure of
`runMat rs - e^{iφ} runMat gs`; `none` otherwise. -/
def checkRun (q : Fin n) (gs rs : List (Gate n)) (φ : PiLin) : Option ℚ :=
  if gs.all (fun g => oneQ? g == some q) = true ∧ rs.all (fun g => oneQ? g == some q) = true then do
    let G ← runB gs
    let R ← runB rs
    pure (bnorm (BMat.sub R (BMat.smul (expIBall φ) G)))
  else none

/-- **Soundness of the run checker.** If `checkRun q gs rs φ = some ε`, the matrices of `rs`
and `gs` on `n` qubits satisfy `‖listMatrix rs - e^{iφ} • listMatrix gs‖ ≤ ε` in the `ℓ²`
operator norm. -/
theorem norm_sub_le_checkRun {q : Fin n} {gs rs : List (Gate n)} {φ : PiLin} {ε : ℚ}
    (h : checkRun q gs rs φ = some ε) :
    ‖listMatrix rs - exp (I * (PiLin.toReal φ : ℂ)) • listMatrix gs‖ ≤ (ε : ℝ) := by
  unfold checkRun at h
  split at h
  · next hc =>
    obtain ⟨hgs, hrs⟩ := hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨G, hG, R, hR, rfl⟩ := h
    have hgs' : ∀ g ∈ gs, oneQ? g = some q := fun g hg => by
      simpa using List.all_eq_true.mp hgs g hg
    have hrs' : ∀ g ∈ rs, oneQ? g = some q := fun g hg => by
      simpa using List.all_eq_true.mp hrs g hg
    rw [listMatrix_eq_embedGate1_runMat hgs', listMatrix_eq_embedGate1_runMat hrs']
    have he : embedGate1 n q (runMat rs) -
          exp (I * (PiLin.toReal φ : ℂ)) • embedGate1 n q (runMat gs) =
        embed1Hom q (runMat rs - exp (I * (PiLin.toReal φ : ℂ)) • runMat gs) := by
      rw [map_sub, map_smul]
      rfl
    rw [he]
    refine (NonUnitalStarAlgHom.norm_apply_le (embed1Hom q) _).trans ?_
    exact norm_le_bnorm (memM_sub (memM_runB hR) (memM_smul (mem_expIBall φ) (memM_runB hG)))
  · exact absurd h (by simp)

end CatCrypt.Quantum.Synthesis.IntervalArith
