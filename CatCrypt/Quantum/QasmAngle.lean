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

`Gate.Rz` stores a real angle `θ : ℝ`, which is noncomputable — it has no
`ToString` and no parser, so the OpenQASM backend currently drops it (emit prints
the literal word `theta`; parse substitutes `0`). A real angle also cannot be
inspected at runtime, so it can never be printed losslessly.

This module provides the **representable** angle type used at the QASM I/O
boundary. An angle is stored as a rational multiple of `π`:

  `QasmAngle = ℚ`,  with  `toReal q = q · π`  (radians).

Every angle in the discrete (Clifford+T and rational-rotation) gate set is of
this form — `T = rz(π/4)`, `S = rz(π/2)`, `rz(3π/8)`, … — so emit/parse over
`QasmAngle` is **lossless** and fully computable, while `toReal` connects it back
to the real-valued semantics of `Gate.Rz`. The continuous angles used by
variational circuits (`Programs/VQE`) stay on the real `Gate.Rz` and are simply
not in the representable image — consistent with the fact that an arbitrary real
cannot be emitted as a finite QASM literal.

The `toQASM` / `parse` pair targets OpenQASM 3.0 angle syntax, where `pi` is a
built-in constant: `0`, `pi`, `-pi`, `pi/4`, `-pi/2`, `3*pi/8`, `2*pi`.
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

theorem toReal_one : toReal 1 = Real.pi := by simp [toReal]

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

/-! ## Parse: OpenQASM 3.0 literal → representable angle -/

/-- Parse the numerator part `k*pi` / `pi` / `-pi` into its integer coefficient. -/
def parseNumPi (a : String) : Option ℤ :=
  let a := a.trim
  if a = "pi" then some 1
  else if a = "-pi" then some (-1)
  else if a.endsWith "*pi" then (a.dropRight 3).trim.toInt?
  else none

/-- Parse an OpenQASM 3.0 angle literal (`0`, `pi`, `-pi/2`, `3*pi/8`, …) into a
representable angle. Inverse of `toQASM` on its image. -/
def parse (s0 : String) : Option QasmAngle :=
  let s := s0.trim
  if s = "0" then some 0
  else
    match s.splitOn "/" with
    | [a] => (parseNumPi a).map (fun k => (k : ℚ))
    | [a, b] =>
      match parseNumPi a, b.trim.toNat? with
      | some k, some d => if d = 0 then none else some ((k : ℚ) / (d : ℚ))
      | _, _ => none
    | _ => none

/-! ## Round-trip on the representable image (lossless, computable) -/

example : parse (toQASM 0) = some 0 := by native_decide
example : parse (toQASM 1) = some 1 := by native_decide
example : parse (toQASM (1 / 4)) = some (1 / 4) := by native_decide          -- T
example : parse (toQASM (1 / 2)) = some (1 / 2) := by native_decide          -- S
example : parse (toQASM (-(1 / 4))) = some (-(1 / 4)) := by native_decide    -- T†
example : parse (toQASM (-(1 / 2))) = some (-(1 / 2)) := by native_decide    -- mergeTdgTdg
example : parse (toQASM (3 / 8)) = some (3 / 8) := by native_decide
example : parse (toQASM 2) = some 2 := by native_decide

end QasmAngle

end CatCrypt.Quantum
