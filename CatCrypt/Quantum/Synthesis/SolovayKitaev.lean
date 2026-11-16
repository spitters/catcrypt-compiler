/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QFT.Circuit
public import CatCryptCore.ForMathlib.SolovayKitaev.Recursion
public import CatCryptCore.ForMathlib.SolovayKitaev.HTDense

/-!
# Solovay–Kitaev synthesis over the gates `H`, `T`, `T†` of one qubit

Every single-qubit unitary `U` is within `ε` of a global phase times the matrix of a gate list
over `{H 0, T 0, Tdg 0}` of length `O (log ^ c (1 / ε))`, `c = log 5 / log (3/2)`.

The proof applies the Solovay–Kitaev theorem for `SU(2)` (`SolovayKitaev.solovay_kitaev`) to
the alphabet `hSU = i H`, `tSU = e^{-iπ/8} T` and their inverses, whose short words form a net
of `SU(2)` (`SolovayKitaev.exists_isCover_HT`). The unitary `U` is moved into `SU(2)` by the
phase `s⁻¹` with `s² = det U`. Each letter is a phase times the matrix of one gate:
`hSU⁻¹ = -i H` and `tSU⁻¹ = e^{iπ/8} T†`; the phases of a word multiply to the global phase.

## Main definitions

* `htGate`, `htPhase` — the gate and the phase of each letter of the alphabet.

## Main results

* `coe_htLetter` — each letter is its phase times the matrix of its gate.
* `coe_htWord` — a word is the product of its phases times the matrix of its gate list.
* `exists_htWord_approx` — **Solovay–Kitaev synthesis** over `H`, `T`, `T†`.

## References

* A. Yu. Kitaev, *Quantum computations: algorithms and error correction*, Russian Math.
  Surveys 52 (1997).
* C. M. Dawson, M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006);
  arXiv:quant-ph/0505030 (2005).
-/

@[expose] public section

set_option autoImplicit false

open Complex
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix listMatrix_append listMatrix_cons listMatrix_nil)
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CatCrypt.Quantum.Synthesis.SK

/-- On one qubit, the embedding of a gate matrix at qubit `0` is the matrix itself. -/
theorem embedGate1_one_zero (G : Matrix (Fin 2) (Fin 2) ℂ) : embedGate1 1 0 G = G := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The gate of each letter of the alphabet `hSU, tSU, hSU⁻¹, tSU⁻¹`. -/
def htGate : Fin 4 → Gate 1 := ![.H 0, .T 0, .H 0, .Tdg 0]

/-- The phase of each letter: `hSU = i H`, `tSU = e^{-iπ/8} T`, `hSU⁻¹ = -i H`,
`tSU⁻¹ = e^{iπ/8} T†`. -/
def htPhase : Fin 4 → ℂ :=
  ![I, exp (-(((Real.pi / 8 : ℝ) : ℂ) * I)), -I, exp (((Real.pi / 8 : ℝ) : ℂ) * I)]

/-- Each phase has norm one. -/
theorem norm_htPhase (i : Fin 4) : ‖htPhase i‖ = 1 := by
  fin_cases i <;> simp [htPhase, Complex.norm_exp]

/-- The product of the phases of a word has norm one. -/
theorem norm_prod_htPhase (v : List (Fin 4)) : ‖(v.map htPhase).prod‖ = 1 := by
  induction v with
  | nil => simp
  | cons a v ih => rw [List.map_cons, List.prod_cons, norm_mul, ih, norm_htPhase, mul_one]

/-- Each letter of the alphabet is its phase times the matrix of its gate. -/
theorem coe_htLetter (i : Fin 4) :
    (SolovayKitaev.htLetter i : Matrix (Fin 2) (Fin 2) ℂ) =
      htPhase i • listMatrix [htGate i] := by
  rw [listMatrix_cons, listMatrix_nil, one_mul]
  fin_cases i <;>
    simp only [htGate, htPhase, SolovayKitaev.htLetter, gateEmbedding, embedGate1_one_zero,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · rw [SolovayKitaev.coe_hSU]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SolovayKitaev.hadamard, Programs.Qubit.hadamard]
  · rw [SolovayKitaev.coe_tSU]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SolovayKitaev.tGate, Programs.Qubit.tGate, mul_comm]
  · change star (SolovayKitaev.hSU : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [SolovayKitaev.coe_hSU, star_smul]
    congr 1
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SolovayKitaev.hadamard, Programs.Qubit.hadamard, Matrix.star_apply]
  · change star (SolovayKitaev.tSU : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [SolovayKitaev.coe_tSU, star_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SolovayKitaev.tGate, tDaggerGate, Matrix.star_apply, ← Complex.exp_conj,
        ← Complex.exp_add, map_ofNat]
    ring_nf

/-- A word over the alphabet is the product of its phases times the matrix of its gate list;
the gate list is the word reversed, since the head of a gate list is applied first. -/
theorem coe_htWord (v : List (Fin 4)) :
    (SolovayKitaev.htWord v : Matrix (Fin 2) (Fin 2) ℂ) =
      (v.map htPhase).prod • listMatrix (v.map htGate).reverse := by
  induction v with
  | nil => simp [SolovayKitaev.htWord, listMatrix_nil]
  | cons a v ih =>
    rw [show SolovayKitaev.htWord (a :: v) =
        SolovayKitaev.htLetter a * SolovayKitaev.htWord v by simp [SolovayKitaev.htWord],
      MulMemClass.coe_mul, ih, coe_htLetter, List.map_cons, List.prod_cons, List.map_cons,
      List.reverse_cons, listMatrix_append, smul_mul_smul_comm]

/-- The arithmetic of the length bound: `M · max 1 (x / a) ^ p ≤ K L ^ p + K` for `x ≤ L` and
`K = M (1 + (a ^ p)⁻¹)`. -/
theorem mul_max_rpow_le {a L x p M : ℝ} (ha : 0 < a) (hL : 0 < L) (hp : 0 < p) (hx : x ≤ L)
    (hM : 0 ≤ M) :
    M * max 1 (x / a) ^ p ≤ M * (1 + (a ^ p)⁻¹) * L ^ p + M * (1 + (a ^ p)⁻¹) := by
  have hap : 0 < a ^ p := Real.rpow_pos_of_pos ha p
  have hLp : 0 ≤ L ^ p := Real.rpow_nonneg hL.le p
  have h1 : max 1 (x / a) ≤ max 1 (L / a) := by
    gcongr
  have h2 : max 1 (x / a) ^ p ≤ max 1 (L / a) ^ p :=
    Real.rpow_le_rpow (by positivity) h1 hp.le
  have h3 : max 1 (L / a) ^ p ≤ 1 + L ^ p * (a ^ p)⁻¹ := by
    rcases le_total 1 (L / a) with h | h
    · rw [max_eq_right h, Real.div_rpow hL.le ha.le, div_eq_mul_inv]
      linarith
    · rw [max_eq_left h, Real.one_rpow]
      have : 0 ≤ L ^ p * (a ^ p)⁻¹ := by positivity
      linarith
  have h4 : L ^ p * (a ^ p)⁻¹ ≤ (1 + (a ^ p)⁻¹) * L ^ p := by
    nlinarith
  have h5 : 0 ≤ (a ^ p)⁻¹ := by positivity
  calc M * max 1 (x / a) ^ p ≤ M * (1 + L ^ p * (a ^ p)⁻¹) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hM
    _ ≤ M * ((1 + (a ^ p)⁻¹) * L ^ p + (1 + (a ^ p)⁻¹)) :=
        mul_le_mul_of_nonneg_left (by linarith) hM
    _ = _ := by ring

/-- **Solovay–Kitaev synthesis over `H`, `T`, `T†`.** There is a constant `K` such that every
single-qubit unitary `U` is, for every `0 < ε < 1`, within `ε` in the operator norm of a phase
`c` times the matrix of a gate list over `{H 0, T 0, Tdg 0}` of length at most
`K · log (1 / ε) ^ (log 5 / log (3/2)) + K`. -/
theorem exists_htWord_approx :
    ∃ K : ℝ, ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (w : List (Gate 1)) (c : ℂ),
        (∀ g ∈ w, g = .H 0 ∨ g = .T 0 ∨ g = .Tdg 0) ∧ ‖c‖ = 1 ∧
        ‖U - c • listMatrix w‖ ≤ ε ∧
        (w.length : ℝ) ≤ K * Real.log (1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) + K := by
  set ε₀ : NNReal := 1 / 800 with hε₀
  have hε₀0 : 0 < ε₀ := by norm_num [hε₀]
  have hε₀1 : (ε₀ : ℝ) < 1 / SolovayKitaev.cSK ^ 2 := by
    norm_num [hε₀, SolovayKitaev.cSK, SolovayKitaev.cGC]
  obtain ⟨L₀, hcov⟩ := SolovayKitaev.exists_isCover_HT ε₀ hε₀0
  have hnet : Metric.IsCover ε₀ Set.univ
      (SolovayKitaev.wordEval SolovayKitaev.htLetter '' {w | w.length ≤ L₀}) := hcov
  have hinv : ∀ g, SolovayKitaev.htLetter (SolovayKitaev.htInvLetter g) =
      star (SolovayKitaev.htLetter g) := by
    intro g
    rw [SolovayKitaev.htLetter_inv]
    rfl
  set a : ℝ := Real.log (1 / (SolovayKitaev.cSK ^ 2 * ε₀)) with ha
  have ha0 : 0 < a := by
    rw [ha]
    apply Real.log_pos
    norm_num [hε₀, SolovayKitaev.cSK, SolovayKitaev.cGC]
  refine ⟨5 * L₀ * (1 + (a ^ SolovayKitaev.skExp)⁻¹), ?_⟩
  intro U hU ε hε hε1
  -- the phase `s` with `s ^ 2 = det U`
  set s : ℂ := exp (((Complex.arg U.det / 2 : ℝ) : ℂ) * I) with hs
  have hs1 : ‖s‖ = 1 := norm_exp_ofReal_mul_I (U.det.arg / 2)
  have hss : s * s = U.det := by
    have hd : ‖U.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
    have h2 := Complex.norm_mul_exp_arg_mul_I U.det
    rw [hd, Complex.ofReal_one, one_mul] at h2
    rw [← h2, hs, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hs0 : s ≠ 0 := by
    rintro h
    simp [h] at hs1
  have hV : s⁻¹ • U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · have hU' := hU
      rw [Matrix.mem_unitaryGroup_iff'] at hU' ⊢
      rw [star_smul, smul_mul_smul_comm, hU', Complex.star_def, Complex.conj_mul', norm_inv, hs1]
      simp
    · rw [Matrix.det_smul, Fintype.card_fin, ← hss]
      field_simp
  set V : SolovayKitaev.SU2 := ⟨s⁻¹ • U, hV⟩ with hVdef
  obtain ⟨v, hvd, hvl⟩ := SolovayKitaev.solovay_kitaev SolovayKitaev.htLetter
    SolovayKitaev.htInvLetter hinv hnet hε₀0 hε₀1 V hε
  refine ⟨(v.map htGate).reverse, s * (v.map htPhase).prod, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_reverse, List.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    fin_cases i <;> simp [htGate]
  · rw [norm_mul, hs1, one_mul, norm_prod_htPhase]
  · have hUV : U = s • (V : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hVdef, smul_smul, mul_inv_cancel₀ hs0, one_smul]
    have hw : (SolovayKitaev.wordEval SolovayKitaev.htLetter v : Matrix (Fin 2) (Fin 2) ℂ) =
        (v.map htPhase).prod • listMatrix (v.map htGate).reverse := coe_htWord v
    rw [hUV, mul_smul, ← smul_sub, norm_smul, hs1, one_mul, ← hw]
    exact hvd
  · rw [List.length_reverse, List.length_map]
    have hL : 0 < Real.log (1 / ε) := Real.log_pos (one_lt_one_div hε hε1)
    have hp : 0 < SolovayKitaev.skExp :=
      div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
    have hx : Real.log (1 / (SolovayKitaev.cSK ^ 2 * ε)) ≤ Real.log (1 / ε) := by
      apply Real.log_le_log
        (one_div_pos.2 (mul_pos (by norm_num [SolovayKitaev.cSK, SolovayKitaev.cGC]) hε))
      apply one_div_le_one_div_of_le hε
      apply le_mul_of_one_le_left hε.le
      norm_num [SolovayKitaev.cSK, SolovayKitaev.cGC]
    exact hvl.trans (mul_max_rpow_le ha0 hL hp hx (by positivity))

end CatCrypt.Quantum.Synthesis.SK
