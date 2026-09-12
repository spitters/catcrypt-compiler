/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontOps
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField
public import Mathlib.Data.ZMod.Basic

/-!
# Front recognizer: `primeir-hax` `ModArith::mont_mul` → `modArithMontDialect`

The `primeir-hax` `ModArith` trait (`primeir-hax/src/lib.rs`; extracted class
`Primeir_hax.ModArith`) exposes a **binary** Montgomery multiply
`mont_mul (a, b) ↦ a·b·R⁻¹ (mod p)`.  The unary domain-conversion methods
`to_mont`/`from_mont` and the fused unary `mont_square` are recognized in
`CompileFromHaxPrimeIrField.lean` (§4); this module recognizes the remaining
binary `mont_mul` slot, now that `modArithMontDialect` carries the two-operand
`ModArithMontOp.montMul` constructor (`VIR/ModArithMontOps.lean`).

## The recognition entry

| resolved method name            | `ModArithMontOp` (at `N R N'`) | denotes to           |
|---------------------------------|--------------------------------|----------------------|
| `Primeir_hax.ModArith.mont_mul` | `.montMul N R N'`              | `montMul N R N' a b` |

`(N, R, N')` are the Montgomery parameters (`N` the modulus, `R` the radix, `N'`
the constant with `N · N' ≡ -1 (mod R)`), supplied by the recognition context.
The recognizer is fail-closed (`Option`, `none` on any unrecognized head), and
both the fully-qualified `Primeir_hax.ModArith.mont_mul` and the bare
`ModArith.mont_mul` forms are accepted, mirroring the `mont_square` recognizer
in `CompileFromHaxPrimeIrField.recognizeModArithOp`.

## Value tie

`primeir_modarith_mont_mul_recognized_denote` proves the tie: the single-op
`Com modArithMontDialect` leaf carrying `.montMul N R N'` denotes on inputs
`(a, b)` to `montMul N R N' a b` — the two-operand Montgomery multiply the
dialect defines, routed through `ModArithMontOps.montMul_denote` (no fresh
Montgomery reduction, no new dialect op beyond the `montMul` constructor). The
diagonal `a = b` recovers the `mont_square` tie.

This closes the arity gap the `CompileFromHaxPrimeIrField.lean` §4 note recorded:
the crate's binary `mont_mul` now recognizes to a genuine binary op rather than
routing through the unary `mont_square` diagonal.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrMontMul

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontOps
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric (montMul)

/-! ## 1. The recognition entry

Keyed on the resolved `ModArith::mont_mul` trait-method name, returning the
binary `ModArithMontOp.montMul` at Montgomery parameters `(N, R, N')`. -/

/-- Recognize the resolved `primeir-hax` `ModArith::mont_mul` trait-method name
    as the binary `ModArithMontOp.montMul` at Montgomery parameters `(N, R, N')`.
    Fail-closed: any non-`mont_mul` head returns `none`. Both the
    fully-qualified `Primeir_hax.ModArith.mont_mul` and the bare
    `ModArith.mont_mul` forms are accepted. -/
def recognizeModArithMontMulOp (name : String) (N R N' : ℤ) :
    Option ModArithMontOp :=
  if name = "Primeir_hax.ModArith.mont_mul" ∨ name = "ModArith.mont_mul" then
    some (.montMul N R N')
  else none

@[simp] theorem recognize_mont_mul (N R N' : ℤ) :
    recognizeModArithMontMulOp "Primeir_hax.ModArith.mont_mul" N R N'
      = some (.montMul N R N') := rfl

@[simp] theorem recognize_mont_mul_bare (N R N' : ℤ) :
    recognizeModArithMontMulOp "ModArith.mont_mul" N R N'
      = some (.montMul N R N') := rfl

/-- An unrecognized head is rejected (fail-closed). The unary domain-conversion
    and fused-square names are keyed by
    `CompileFromHaxPrimeIrField.recognizeModArithOp`, not here. -/
theorem recognize_unknown (N R N' : ℤ) :
    recognizeModArithMontMulOp "Primeir_hax.ModArith.to_mont" N R N' = none := rfl

/-! ## 2. Emit: the recognized op as a single-op `Com modArithMontDialect` leaf

The binary `montMul` is `[residue N R N', residue N R N'] → residue N R N'`, so
the leaf takes two residues and returns one, mirroring the binary field leaves
(`fMulLeaf`) in `CompileFromHaxPrimeIrField.lean`. -/

/-- The `mont_mul` emit leaf: `let c = montMul a b; ret c` over two residues. -/
def montMulLeaf (N R N' : ℤ) :
    Com modArithMontDialect
      [ModArithMontTy.residue N R N', ModArithMontTy.residue N R N']
      (ModArithMontTy.residue N R N') :=
  .var (.mk (.montMul N R N') rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-! ## 3. The value tie

The emitted leaf denotes to the dialect's binary Montgomery multiply, reusing
`ModArithMontOps.montMul_denote`. -/

/-- **The recognized `ModArith::mont_mul` call ties to the dialect's binary
    Montgomery multiply.** The op that `recognizeModArithMontMulOp` returns
    (`.montMul N R N'`), emitted as `montMulLeaf`, denotes on inputs `(a, b)` to
    `montMul N R N' a b` — the two-operand Montgomery multiply the dialect
    defines, routed through `ModArithMontOps.montMul_denote` (no fresh Montgomery
    reduction). -/
theorem primeir_modarith_mont_mul_recognized_denote (N R N' a b : ℤ) :
    (montMulLeaf N R N').denote (.cons a (.cons b .nil)) = montMul N R N' a b := by
  show modArithMontDenote.denote (.montMul N R N') (.cons a (.cons b .nil))
    = montMul N R N' a b
  exact ModArithMontOps.montMul_denote N R N' a b

/-- **Recognition + emit + tie, end to end for the binary Montgomery multiply.**
    The recognizer accepts the `mont_mul` name (returning `.montMul N R N'`) and
    the leaf carrying that op denotes to `montMul N R N' a b`. Pins the
    recognizer entry and the value-tie together. -/
theorem primeir_modarith_mont_mul_recognized (N R N' a b : ℤ) :
    recognizeModArithMontMulOp "Primeir_hax.ModArith.mont_mul" N R N'
        = some (.montMul N R N') ∧
    (montMulLeaf N R N').denote (.cons a (.cons b .nil)) = montMul N R N' a b :=
  ⟨rfl, primeir_modarith_mont_mul_recognized_denote N R N' a b⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrMontMul
