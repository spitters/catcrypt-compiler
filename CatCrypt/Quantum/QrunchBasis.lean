/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Qelib
public import CatCrypt.Quantum.Synthesis.KAK

/-!
# Gate lists in the basis `{rx, ry, rz, cx, p}`

`toQelib` translates a list of `Gate`s into OpenQASM 2 statements over the basis
`{rx, ry, rz, cx, p}` of `qelib1.inc`, with the global phase of the translation as an
exact angle. The translation is gate by gate, with two peepholes on one qubit: the five
gates `Rz(−π/2) H Rz(γ) H S`, which `KAK.ryGatesA` builds for `Ry(γ)`, become the single
statement `ry(γ)`, and the three gates `H Rz(a) H` become `rx(a)`
(`H · P(a) · H = e^{ia/2} · Rx(a)`).

* `RzQ a`, `S`, `T`, `T†`, `Z` are `p` of `a`, `π/2`, `π/4`, `−π/4`, `π`, exactly;
* `H = ry(π/2) · p(π)`, exactly;
* `X = i · rx(π)` and `Y = i · ry(π)`;
* `CNOT` is `cx`, and `CZ(c, t)` is `ry(π/2)_t; cx(c, t); ry(−π/2)_t`, exactly.

`printQelib` prints a statement list as an OpenQASM 2 program, its angles as
`PiLin.toQASM` prints them (`num/den+k*pi/d`).

## Main results

* `toQelib` — the translation, and `qelibListMatrix_toQelib`: the matrix of the statements is
  `exp (i · phase) • listMatrix l` for a list without the real-angle `Rz`.
* `printQelib` — the OpenQASM 2 text of a statement list.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.OpenQASMImportGates
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.Qelib
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)

namespace CatCrypt.Quantum.QrunchBasis

variable {n : ℕ}

/-! ## Two-by-two identities -/

/-- `exp (−i π / 2) = −i`. -/
theorem exp_neg_pi_div_two_I :
    Complex.exp (Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ)) = -Complex.I := by
  rw [show Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ) = -(↑Real.pi / 2 * Complex.I) by
      push_cast; ring, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]

private theorem ofReal_sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow]; simp

private theorem half_quarter : Real.pi / 2 / 2 = Real.pi / 4 := by ring

private theorem neg_half_quarter : -(Real.pi / 2) / 2 = -(Real.pi / 4) := by ring

/-- `H = Ry(π/2) · P(π)`. -/
theorem ryMatrix_mul_rzGate_pi : ryMatrix (Real.pi / 2) * rzGate Real.pi = hadamard := by
  have he : Complex.exp (Complex.I * Real.pi) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ryMatrix, rzGate, hadamard, Matrix.mul_apply, Fin.sum_univ_two, half_quarter,
      Real.cos_pi_div_four, Real.sin_pi_div_four, he] <;>
    field_simp <;> ring_nf <;> simp [ofReal_sqrt_two_sq]

/-- `Rx(π) = −i X`. -/
theorem rxMatrix_pi : rxMatrix Real.pi = (-Complex.I) • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rxMatrix, pauliX]

/-- `Ry(π) = −i Y`. -/
theorem ryMatrix_pi : ryMatrix Real.pi = (-Complex.I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ryMatrix, pauliY]

/-- `Ry(−π/2) · X · Ry(π/2) = Z`. -/
theorem ryMatrix_pauliX_ryMatrix :
    ryMatrix (-(Real.pi / 2)) * pauliX * ryMatrix (Real.pi / 2) = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ryMatrix, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, half_quarter,
      neg_half_quarter, Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
    ring_nf <;> norm_num [ofReal_sqrt_two_sq]

/-- `Ry(−π/2) · Ry(π/2) = 1`. -/
theorem ryMatrix_neg_mul_ryMatrix : ryMatrix (-(Real.pi / 2)) * ryMatrix (Real.pi / 2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ryMatrix, Matrix.mul_apply, Fin.sum_univ_two, half_quarter,
      neg_half_quarter, Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
    ring_nf <;> simp [ofReal_sqrt_two_sq]

/-! ## Gate by gate -/

/-- A gate other than the real-angle `Rz`. -/
def NoRz : Gate n → Prop
  | .Rz _ _ => False
  | _ => True

/-- The statements of one gate over `{rx, ry, cx, p}` and their phase: the statements'
    matrix is `exp (i · phase) • gateEmbedding g` (`qelibListMatrix_gateQ`). -/
def gateQ : Gate n → List (QGate n) × PiLin
  | .H q => ([.p q (PiLin.ofPi 1), .ry q (PiLin.ofPi (1 / 2))], 0)
  | .X q => ([.rx q (PiLin.ofPi 1)], PiLin.ofPi (-(1 / 2)))
  | .Y q => ([.ry q (PiLin.ofPi 1)], PiLin.ofPi (-(1 / 2)))
  | .Z q => ([.p q (PiLin.ofPi 1)], 0)
  | .T q => ([.p q (PiLin.ofPi (1 / 4))], 0)
  | .Tdg q => ([.p q (PiLin.ofPi (-(1 / 4)))], 0)
  | .S q => ([.p q (PiLin.ofPi (1 / 2))], 0)
  | .CNOT c t => ([.cx c t], 0)
  | .CZ c t => if c = t then ([], 0) else
      ([.ry t (PiLin.ofPi (1 / 2)), .cx c t, .ry t (PiLin.ofPi (-(1 / 2)))], 0)
  | .RzQ q a => ([.p q a], 0)
  | .Rz _ _ => ([], 0)

/-- The matrix of a concatenation, head applied first. -/
theorem qelibListMatrix_append (l₁ l₂ : List (QGate n)) :
    qelibListMatrix (l₁ ++ l₂) = qelibListMatrix l₂ * qelibListMatrix l₁ := by
  induction l₁ with
  | nil => simp [qelibListMatrix]
  | cons g l ih => simp [qelibListMatrix, ih, mul_assoc]

/-- The statements of a gate realise it up to their phase. -/
theorem qelibListMatrix_gateQ (g : Gate n) (hg : NoRz g) :
    qelibListMatrix (gateQ g).1
      = Complex.exp (Complex.I * (gateQ g).2.toReal) • gateEmbedding g := by
  have h1 : (PiLin.ofPi 1).toReal = Real.pi := by simp
  have h12 : (PiLin.ofPi (1 / 2)).toReal = Real.pi / 2 := by
    rw [PiLin.toReal_ofPi]; push_cast; ring
  have hm12 : (PiLin.ofPi (-(1 / 2))).toReal = -(Real.pi / 2) := by
    rw [PiLin.toReal_ofPi]; push_cast; ring
  have h14 : (PiLin.ofPi (1 / 4)).toReal = Real.pi / 4 := by
    rw [PiLin.toReal_ofPi]; push_cast; ring
  have hm14 : (PiLin.ofPi (-(1 / 4))).toReal = -(Real.pi / 4) := by
    rw [PiLin.toReal_ofPi]; push_cast; ring
  cases g with
  | H q =>
    simp only [gateQ, qelibListMatrix, qelibMatrix, h1, h12, one_mul, gateEmbedding,
      embedGate1_mul, ryMatrix_mul_rzGate_pi, PiLin.toReal_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul]
  | X q =>
    simp only [gateQ, qelibListMatrix, qelibMatrix, h1, hm12, one_mul, gateEmbedding,
      rxMatrix_pi, embedGate1_smul, exp_neg_pi_div_two_I]
  | Y q =>
    simp only [gateQ, qelibListMatrix, qelibMatrix, h1, hm12, one_mul, gateEmbedding,
      ryMatrix_pi, embedGate1_smul, exp_neg_pi_div_two_I]
  | Z q =>
    simp only [gateQ, qelibListMatrix, qelibMatrix, h1, one_mul, gateEmbedding,
      ← pauliZ_eq_rzGate, PiLin.toReal_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      one_smul]
  | T q =>
    simp only [gateQ, qelibListMatrix, qelibMatrix, h14, one_mul, gateEmbedding,
      ← tGate_eq_rzGate, PiLin.toReal_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      one_smul]
  | Tdg q =>
    simp only [gateQ, qelibListMatrix, qelibMatrix, hm14, one_mul, gateEmbedding,
      ← tDaggerGate_eq_rzGate, PiLin.toReal_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul]
  | S q =>
    simp only [gateQ, qelibListMatrix, qelibMatrix, h12, one_mul, gateEmbedding,
      show Real.pi / 2 = 2 * (Real.pi / 4) by ring, ← phaseS_eq_rzGate, PiLin.toReal_zero,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
  | CNOT c t => simp [gateQ, qelibListMatrix, qelibMatrix]
  | CZ c t =>
    by_cases h : c = t
    · simp [gateQ, qelibListMatrix, gateEmbedding, h]
    · have hAB : embedGate1 n t (ryMatrix (-(Real.pi / 2))) *
          embedGate1 n t (ryMatrix (Real.pi / 2)) = 1 := by
        rw [embedGate1_mul, ryMatrix_neg_mul_ryMatrix, embedGate1_one]
      simp only [gateQ, ite_eq_right h, qelibListMatrix, qelibMatrix, h12, hm12, one_mul,
        gateEmbedding, dite_eq_right h, embedGate2_cnot h, PiLin.toReal_zero,
        Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
      rw [mul_ctrlMatrix_mul (commOn_embedGate1 (Ne.symm h) _) hAB, embedGate1_mul,
        embedGate1_mul, ryMatrix_pauliX_ryMatrix, embedGate2_czGate h]
  | RzQ q a => simp [gateQ, qelibListMatrix, qelibMatrix, gateEmbedding]
  | Rz q θ => exact hg.elim

/-! ## The translation -/

/-- The `Ry(γ)` pattern `Rz(−π/2) H Rz(γ) H S` is `exp (i γ / 2) • Ry(γ)`. -/
theorem listMatrix_ryPattern (q : Fin n) (γ : PiLin) :
    listMatrix [Gate.RzQ q (PiLin.ofPi (-(1 / 2))), .H q, .RzQ q γ, .H q, .S q]
      = Complex.exp (Complex.I * (γ.toReal / 2 : ℝ)) • embedGate1 n q (ryMatrix γ.toReal) := by
  have hm : (PiLin.ofPi (-(1 / 2))).toReal = -(Real.pi / 2) := by
    rw [PiLin.toReal_ofPi]; push_cast; ring
  simp only [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul, hm]
  rw [Synthesis.KAK.rzGate_neg_pi_div_two, phaseS_hadamard_rz_hadamard_sdg, embedGate1_smul]

/-- The `Rx(a)` pattern `H Rz(a) H` is `exp (i a / 2) • Rx(a)`. -/
theorem listMatrix_rxPattern (q : Fin n) (a : PiLin) :
    listMatrix [Gate.H q, .RzQ q a, .H q]
      = Complex.exp (Complex.I * (a.toReal / 2 : ℝ)) • embedGate1 n q (rxMatrix a.toReal) := by
  simp only [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul]
  rw [hadamard_rz_hadamard, embedGate1_smul]

/-- A list of gates as statements over `{rx, ry, cx, p}` and the global phase:
    `qelibListMatrix (toQelib l).1 = exp (i · (toQelib l).2) • listMatrix l`. -/
def toQelib : List (Gate n) → List (QGate n) × PiLin
  | [] => ([], 0)
  | .RzQ q a :: .H q₁ :: .RzQ q₂ γ :: .H q₃ :: .S q₄ :: rest =>
    if q₁ = q ∧ q₂ = q ∧ q₃ = q ∧ q₄ = q ∧ a = PiLin.ofPi (-(1 / 2)) then
      (.ry q γ :: (toQelib rest).1, -(γ / 2) + (toQelib rest).2)
    else
      ((gateQ (.RzQ q a)).1 ++ (toQelib (.H q₁ :: .RzQ q₂ γ :: .H q₃ :: .S q₄ :: rest)).1,
        (gateQ (.RzQ q a)).2 + (toQelib (.H q₁ :: .RzQ q₂ γ :: .H q₃ :: .S q₄ :: rest)).2)
  | .H q :: .RzQ q₁ a :: .H q₂ :: rest =>
    if q₁ = q ∧ q₂ = q then
      (.rx q a :: (toQelib rest).1, -(a / 2) + (toQelib rest).2)
    else
      ((gateQ (.H q)).1 ++ (toQelib (.RzQ q₁ a :: .H q₂ :: rest)).1,
        (gateQ (.H q)).2 + (toQelib (.RzQ q₁ a :: .H q₂ :: rest)).2)
  | g :: rest => ((gateQ g).1 ++ (toQelib rest).1, (gateQ g).2 + (toQelib rest).2)
termination_by l => l.length

/-- One gate in front of a translated list. -/
theorem qelibListMatrix_gateQ_append (g : Gate n) (hg : NoRz g) (r : List (QGate n) × PiLin)
    (l : List (Gate n))
    (hr : qelibListMatrix r.1 = Complex.exp (Complex.I * r.2.toReal) • listMatrix l) :
    qelibListMatrix ((gateQ g).1 ++ r.1)
      = Complex.exp (Complex.I * ((gateQ g).2 + r.2).toReal) • listMatrix (g :: l) := by
  rw [qelibListMatrix_append, hr, qelibListMatrix_gateQ g hg, smul_mul_smul, listMatrix_cons,
    ← Complex.exp_add]
  congr 1
  rw [PiLin.toReal_add]
  push_cast
  congr 1
  ring

/-- **The translation realises the list** up to its phase, for a list without the
    real-angle `Rz`. -/
theorem qelibListMatrix_toQelib (l : List (Gate n)) (hl : ∀ g ∈ l, NoRz g) :
    qelibListMatrix (toQelib l).1
      = Complex.exp (Complex.I * (toQelib l).2.toReal) • listMatrix l := by
  fun_induction toQelib l with
  | case1 => simp [qelibListMatrix, listMatrix_nil]
  | case2 q a q₁ q₂ γ q₃ q₄ rest hc ih =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hc
    have hr := ih (fun g hg => hl g (by simp [hg]))
    rw [show Gate.RzQ q₄ (PiLin.ofPi (-(1 / 2))) :: Gate.H q₄ :: Gate.RzQ q₄ γ :: Gate.H q₄ ::
        Gate.S q₄ :: rest = [Gate.RzQ q₄ (PiLin.ofPi (-(1 / 2))), .H q₄, .RzQ q₄ γ, .H q₄,
          .S q₄] ++ rest from rfl, listMatrix_append, listMatrix_ryPattern]
    simp only [qelibListMatrix, qelibMatrix, hr]
    rw [Matrix.mul_smul, smul_smul, Matrix.smul_mul, ← Complex.exp_add, PiLin.toReal_add,
      PiLin.toReal_neg, PiLin.ofNat_eq_ofPi, PiLin.toReal_div_ofPi]
    congr 2
    push_cast
    ring
  | case3 q a q₁ q₂ γ q₃ q₄ rest _ ih =>
    exact qelibListMatrix_gateQ_append _ (hl _ (by simp)) _ _
      (ih (fun g hg => hl g (List.mem_cons_of_mem _ hg)))
  | case4 q q₁ a q₂ rest hc ih =>
    obtain ⟨rfl, rfl⟩ := hc
    have hr := ih (fun g hg => hl g (by simp [hg]))
    rw [show Gate.H q₂ :: Gate.RzQ q₂ a :: Gate.H q₂ :: rest
        = [Gate.H q₂, .RzQ q₂ a, .H q₂] ++ rest from rfl, listMatrix_append,
      listMatrix_rxPattern]
    simp only [qelibListMatrix, qelibMatrix, hr]
    rw [Matrix.mul_smul, smul_smul, Matrix.smul_mul, ← Complex.exp_add, PiLin.toReal_add,
      PiLin.toReal_neg, PiLin.ofNat_eq_ofPi, PiLin.toReal_div_ofPi]
    congr 2
    push_cast
    ring
  | case5 q q₁ a q₂ rest _ ih =>
    exact qelibListMatrix_gateQ_append _ (hl _ (by simp)) _ _
      (ih (fun g hg => hl g (List.mem_cons_of_mem _ hg)))
  | case6 g rest _ _ ih =>
    exact qelibListMatrix_gateQ_append _ (hl _ (by simp)) _ _
      (ih (fun g hg => hl g (List.mem_cons_of_mem _ hg)))

/-! ## Printing -/

/-- A statement as an OpenQASM 2 line. -/
def QGate.toQASM : QGate n → String
  | .h q => s!"h q[{q.val}];"
  | .x q => s!"x q[{q.val}];"
  | .y q => s!"y q[{q.val}];"
  | .z q => s!"z q[{q.val}];"
  | .s q => s!"s q[{q.val}];"
  | .sdg q => s!"sdg q[{q.val}];"
  | .t q => s!"t q[{q.val}];"
  | .tdg q => s!"tdg q[{q.val}];"
  | .sx q => s!"sx q[{q.val}];"
  | .sxdg q => s!"sxdg q[{q.val}];"
  | .rx q a => s!"rx({a.toQASM}) q[{q.val}];"
  | .ry q a => s!"ry({a.toQASM}) q[{q.val}];"
  | .rz q a => s!"rz({a.toQASM}) q[{q.val}];"
  | .p q a => s!"p({a.toQASM}) q[{q.val}];"
  | .u q a b c => s!"u3({a.toQASM},{b.toQASM},{c.toQASM}) q[{q.val}];"
  | .u2 q a b => s!"u2({a.toQASM},{b.toQASM}) q[{q.val}];"
  | .cx c t => s!"cx q[{c.val}],q[{t.val}];"
  | .cz c t => s!"cz q[{c.val}],q[{t.val}];"
  | .swap a b => s!"swap q[{a.val}],q[{b.val}];"
  | .cp c t a => s!"cp({a.toQASM}) q[{c.val}],q[{t.val}];"
  | .ccx a b t => s!"ccx q[{a.val}],q[{b.val}],q[{t.val}];"
  | .ccz a b t => s!"ccz q[{a.val}],q[{b.val}],q[{t.val}];"

/-- A statement list as an OpenQASM 2 program on the register `q[n]`, one statement a
    line. -/
def printQelib (n : ℕ) (l : List (QGate n)) : String :=
  String.intercalate "\n"
    (["OPENQASM 2.0;", "include \"qelib1.inc\";", s!"qreg q[{n}];"] ++ l.map QGate.toQASM)
    ++ "\n"

end CatCrypt.Quantum.QrunchBasis
