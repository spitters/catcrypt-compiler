/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# `Com → AArch64`, step 1 (front): dialect faithfulness + a field-leaf compile

Two things on top of the proved `ComToArm` core:

1. **Dialect faithfulness** — the source effect `evalRegStmt` of each `RegStmt`
   *is* the `Com jasminDialect` op semantics (`JasminBinOp.apply` at width 64,
   `mulHiW`, the immediate-shift / move ops). So `RegStmt` is a faithful named-SSA
   view of the `regArith` fragment, not an ad-hoc reimplementation.

2. **A field-leaf compile (step 2 differential, in-Lean)** — the BabyBear Barrett
   `bbMul` field multiply, written as a `RegProg`, compiles through `regToBOp` to
   *exactly* the hand-written `BOp` block the owned ARM Poseidon2 leaf emits
   (`plonky3_perm16_a64_emit.bbMul`), by `rfl` (`bbMul_compiled_eq_hand`).
   `bbMul_machine_eq_denote` then states that the lowered `BInst` block, run on
   the `BState` model, computes `armTarget.denote (bbMulReg dst a b)`. Neither
   theorem mentions the encoded bytes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)

/-! ## 1. Dialect faithfulness

Each `evalRegStmt` arm equals the corresponding `Com jasminDialect` op effect:
the binary ALU ops are `JasminBinOp.apply` at width 64, `umulh` is `mulHiW`, and
the immediate shifts / move are the dialect's shift / move denotations. All by
definitional unfolding. -/

@[simp] theorem eval_add_faithful (s : BState) (d a b : String) :
    evalRegStmt s (.add d a b) = s.set d (JasminBinOp.apply (w := 64) .add (s.get a) (s.get b)) :=
  rfl

@[simp] theorem eval_sub_faithful (s : BState) (d a b : String) :
    evalRegStmt s (.sub d a b) = s.set d (JasminBinOp.apply (w := 64) .sub (s.get a) (s.get b)) :=
  rfl

@[simp] theorem eval_mul_faithful (s : BState) (d a b : String) :
    evalRegStmt s (.mul d a b) = s.set d (JasminBinOp.apply (w := 64) .mul (s.get a) (s.get b)) :=
  rfl

@[simp] theorem eval_and_faithful (s : BState) (d a b : String) :
    evalRegStmt s (.and d a b) = s.set d (JasminBinOp.apply (w := 64) .and (s.get a) (s.get b)) :=
  rfl

@[simp] theorem eval_orr_faithful (s : BState) (d a b : String) :
    evalRegStmt s (.orr d a b) = s.set d (JasminBinOp.apply (w := 64) .or (s.get a) (s.get b)) :=
  rfl

@[simp] theorem eval_eor_faithful (s : BState) (d a b : String) :
    evalRegStmt s (.eor d a b) = s.set d (JasminBinOp.apply (w := 64) .xor (s.get a) (s.get b)) :=
  rfl

@[simp] theorem eval_shrI_faithful (s : BState) (d a : String) (i : Nat) :
    evalRegStmt s (.shrI d a i) = s.set d (s.get a >>> i) :=
  rfl

/-! ## 2. The BabyBear Barrett `bbMul` field multiply, compiled

`bbMulReg dst a b` is `(a · b) mod p` over BabyBear (`p = 2013265921`,
`MU = 2290649223`): the schoolbook product, the Barrett reduce
`q = ((x >> 30)·MU >> 32)·P; x -= q`, and the branchless conditional subtract.
This is the BabyBear field multiply the owned ARM Poseidon2 permutation leaf
emits — written here over the `RegStmt` IR. -/

/-- `dst = (a · b) mod p` (BabyBear Barrett), as a straight-line `RegProg`. The
    scratch names `x`, `q` and the constant slots `MU`, `P`, `zero` match the
    owned leaf's allocation. -/
def bbMulReg (dst a b : String) : RegProg :=
  [ .mul "x" a b
  , .shrI "q" "x" 30, .mul "q" "q" "MU", .shrI "q" "q" 32, .mul "q" "q" "P"
  , .sub "x" "x" "q"
  , .sub dst "x" "P", .shrI "q" dst 63, .sub "q" "zero" "q", .and "q" "q" "P"
  , .add dst dst "q" ]

/-- The hand-written `BOp` block of the owned ARM Poseidon2 leaf for `bbMul`
    (the bench emitter `plonky3_perm16_a64_emit.bbMul`, which is not part of this
    package), reproduced for the equality below. -/
def bbMulHandBOp (dst a b : String) : List BOp :=
  [ .mul "x" a b
  , .lsr "q" "x" 30, .mul "q" "q" "MU", .lsr "q" "q" 32, .mul "q" "q" "P"
  , .sub "x" "x" "q"
  , .sub dst "x" "P", .lsr "q" dst 63, .sub "q" "zero" "q", .and "q" "q" "P"
  , .add dst dst "q" ]

/-- Compiling `bbMulReg` through the `regToBOp` instruction selection yields
    exactly the hand-written owned-leaf `BOp` block `bbMulHandBOp`. -/
theorem bbMul_compiled_eq_hand (dst a b : String) :
    regToBOp (bbMulReg dst a b) = bbMulHandBOp dst a b := by
  rfl

/-- The compiled-and-lowered `BInst` block, run on the `BState` model, computes
    the source `bbMulReg` denotation (`regToBOp_denote` at this program). -/
theorem bbMul_machine_eq_denote (dst a b : String) (s : BState) :
    runBBlock s (lowerBBlock (regToBOp (bbMulReg dst a b)))
      = armTarget.denote (bbMulReg dst a b) s :=
  regToBOp_denote _ _

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
