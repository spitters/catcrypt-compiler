/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Representable rotation angles for QASM I/O

`Gate.Rz` stores a real angle `θ : ℝ`, which is noncomputable and cannot be
printed losslessly. The angle type of the QASM I/O boundary is a rational
multiple of `π`:

  `QasmAngle = ℚ`,  with  `toReal q = q · π`  (radians).

Every angle of the discrete (Clifford+T and rational-rotation) gate set has this
form (`T = rz(π/4)`, `S = rz(π/2)`, `rz(3π/8)`), and `toReal` connects it to the
real-valued semantics of `Gate.Rz`. The continuous angles of variational circuits
(`Programs/VQE`) stay on the real `Gate.Rz`.

`toQASM` prints OpenQASM 3.0 angle syntax, where `pi` is a built-in constant:
`0`, `pi`, `-pi`, `pi/4`, `-pi/2`, `3*pi/8`, `2*pi`. Its reader is
`DQASM.parseAngle` (`OpenQASMDiscrete`), with `DQASM.parseAngle_toQASM` the
round trip.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum

/-- A QASM-representable rotation angle: a rational multiple of `π` (radians). -/
abbrev QasmAngle : Type := ℚ

namespace QasmAngle

/-- Interpret a representable angle as a real number of radians, `q · π`. -/
noncomputable def toReal (q : QasmAngle) : ℝ := (q : ℝ) * Real.pi

@[simp] theorem toReal_zero : toReal 0 = 0 := by simp [toReal]

@[simp] theorem toReal_one : toReal 1 = Real.pi := by simp [toReal]

/-! ## Emit: representable angle → OpenQASM 3.0 literal -/

/-- Render the numerator part `k · π` of an angle (no denominator). -/
def numPiToString (k : ℤ) : String :=
  if k = 1 then "pi"
  else if k = -1 then "-pi"
  else s!"{k}*pi"

/-- Emit a representable angle as an OpenQASM 3.0 angle literal. -/
def toQASM (q : QasmAngle) : String :=
  if q.num = 0 then "0"
  else if q.den = 1 then numPiToString q.num
  else s!"{numPiToString q.num}/{q.den}"

end QasmAngle

end CatCrypt.Quantum
