/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRelCompile

/-!
# DR-collapse — native dialect security

This file states and proves the dialect-level OTP and peephole security results
**directly on `catCryptDialect`**, computing the `SPComp` distance through
`Com.denoteSP` / `catCryptDenoteSP` and applying the uniform-sample-XOR
distribution fact (`SPComp.sample_bind_pure_equiv`).

The dialect OTP / peephole programs are defined natively as `Com catCryptDialect`
A-normal-form programs (their `Expr` ops, de-Bruijn arguments and return-type
witnesses written out directly). Their `Com.denoteSP` is then evaluated *by
reduction on the dialect itself* (`Com.denoteSP_var`/`Com.denoteSP_ret`,
`Expr.denoteSP`, `catCryptDenoteSP`), and the standard one-time-pad argument is
applied: `sample k; pure (inr (k ⊕ m))` is, in distribution, `sample c;
pure (inr c)`, because `(· ⊕ m)` is a bijection on `Bool`.

The security view therefore lives on `catCryptDialect` alone.

**0 axioms**, **0 sorries**.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRelCompile
open scoped ENNReal

/-! ## 0. Dialect programs (relationally compiled)

The OTP and peephole programs are built from the `CryptoDialectRelCompile`
combinators, so their `Com.denoteSP` reductions come from the bundled
`.spec`/`.correct` rather than a hand-written `Com.var` form. -/

/-- The OTP *real* program: `sample k; c = xor(k, m); ret (inr c)`. -/
noncomputable def otpRealCompiled : Compiled [CryptoTy.bit] (.sum .unit .bit) :=
  csampleBit (cxorBit Ctxt.Var.here (Ctxt.Var.there Ctxt.Var.here)
    (cinr .unit .bit Ctxt.Var.here (cret Ctxt.Var.here)))

noncomputable def otpReal_dialect : Com catCryptDialect [CryptoTy.bit] (.sum .unit .bit) :=
  otpRealCompiled.com

/-- The OTP *ideal* functionality: `sample c; ret (inr c)`. -/
noncomputable def otpIdealCompiled : Compiled [CryptoTy.bit] (.sum .unit .bit) :=
  csampleBit (cinr .unit .bit Ctxt.Var.here (cret Ctxt.Var.here))

noncomputable def otpIdeal_dialect : Com catCryptDialect [CryptoTy.bit] (.sum .unit .bit) :=
  otpIdealCompiled.com

/-- The XOR-bijection peephole LHS: `sample k; c = xor(k, m); ret c`. -/
noncomputable def xorSampleBijLhsCompiled : Compiled [CryptoTy.bit] CryptoTy.bit :=
  csampleBit (cxorBit Ctxt.Var.here (Ctxt.Var.there Ctxt.Var.here) (cret Ctxt.Var.here))

noncomputable def xorSampleBij_lhs_dialect : Com catCryptDialect [CryptoTy.bit] CryptoTy.bit :=
  xorSampleBijLhsCompiled.com

/-- The XOR-bijection peephole RHS: `sample c; ret c`. -/
noncomputable def xorSampleBijRhsCompiled : Compiled [CryptoTy.bit] CryptoTy.bit :=
  csampleBit (cret Ctxt.Var.here)

noncomputable def xorSampleBij_rhs_dialect : Com catCryptDialect [CryptoTy.bit] CryptoTy.bit :=
  xorSampleBijRhsCompiled.com

/-- The `bvAnd`-self peephole LHS: `y = bvAnd(x, x); ret y`. -/
noncomputable def bvAndSelfLhsCompiled : Compiled [CryptoTy.sword 8] (CryptoTy.sword 8) :=
  cbvAnd Ctxt.Var.here Ctxt.Var.here (cret Ctxt.Var.here)

noncomputable def bvAndSelf_lhs_dialect : Com catCryptDialect [CryptoTy.sword 8] (CryptoTy.sword 8) :=
  bvAndSelfLhsCompiled.com

/-- The `bvAnd`-self peephole RHS: `ret x`. -/
noncomputable def bvAndSelf_rhs_dialect : Com catCryptDialect [CryptoTy.sword 8] (CryptoTy.sword 8) :=
  Com.ret Ctxt.Var.here

/-! ## OTP: denotation of the dialect programs -/

/-- Real-OTP dialect denotation: sampling a key bit and XOR-ing it into the
    message bit, wrapped in `Sum.inr`. -/
theorem otpReal_dialect_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP otpReal_dialect V
      = SPComp.bind (SPComp.sample Bool)
          (fun k => SPComp.pure
            (Sum.inr (Bool.xor k (Ctxt.Var.here.lookup V)) : Unit ⊕ Bool)) :=
  otpRealCompiled.correct V

/-- Ideal-OTP dialect denotation: sampling a ciphertext bit directly, wrapped in
    `Sum.inr`. -/
theorem otpIdeal_dialect_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP otpIdeal_dialect V
      = SPComp.bind (SPComp.sample Bool)
          (fun c => SPComp.pure (Sum.inr c : Unit ⊕ Bool)) :=
  otpIdealCompiled.correct V

/-! ## OTP: native security (real = ideal in distribution) -/

/-- **Native OTP `real = ideal` over the crypto dialect.** The dialect OTP real
    and ideal `Com.denoteSP` images coincide at every valuation — the standard
    one-time-pad argument applied *directly* on `catCryptDialect`: with the two
    denotations evaluated natively (`otpReal_dialect_denoteSP` /
    `otpIdeal_dialect_denoteSP`) to `sample k; pure (inr (k ⊕ m))` and
    `sample c; pure (inr c)`, equality is `SPComp.sample_bind_pure_equiv` for the
    XOR bijection `xorBij m` (`(· ⊕ m)` is a bijection on `Bool`). -/
theorem otpReal_eq_otpIdeal_denoteSP
    (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP otpReal_dialect V = Com.denoteSP otpIdeal_dialect V := by
  rw [otpReal_dialect_denoteSP, otpIdeal_dialect_denoteSP]
  exact SPComp.sample_bind_pure_equiv (xorBij (Ctxt.Var.here.lookup V)) Sum.inr

/-- **Native dialect OTP security.** The dialect OTP real/ideal programs are at
    `SPComp` statistical distance `0` at every valuation — proved *directly on
    `catCryptDialect`* via `otpReal_eq_otpIdeal_denoteSP` (native `Com.denoteSP`
    evaluation + the uniform-sample-XOR bijection), with `sdist_self`.
    (composition plumbing) -/
theorem otp_dialect_secure_native :
    ∀ V : Ctxt.Valuation (d := catCryptDialect) [.bit],
      sdist (fun (_ : Unit) => Com.denoteSP otpReal_dialect V)
            (fun (_ : Unit) => Com.denoteSP otpIdeal_dialect V) = 0 := by
  intro V
  rw [funext fun (_ : Unit) => otpReal_eq_otpIdeal_denoteSP V, sdist_self]

/-! ## Peephole: native security of the XOR-bijection rewrite

`xor_sample_bij` is the OTP XOR-bijection peephole. Its two dialect images
(`xorSampleBij_lhs_dialect` = `sample k; c = xor(k, m); ret c`,
`xorSampleBij_rhs_dialect` = `sample c; ret c`) are proved distribution-equal
directly on `catCryptDialect`, the same native argument as OTP. -/

/-- Native denotation of the XOR-bijection peephole LHS on the crypto dialect:
    `sample k; pure (k ⊕ m)`. -/
theorem xorSampleBij_lhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP xorSampleBij_lhs_dialect V
      = SPComp.bind (SPComp.sample Bool)
          (fun k => SPComp.pure (Bool.xor k (Ctxt.Var.here.lookup V))) :=
  xorSampleBijLhsCompiled.correct V

/-- Denotation of the XOR-bijection peephole RHS on the crypto dialect:
    `sample c; pure c`. -/
theorem xorSampleBij_rhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP xorSampleBij_rhs_dialect V
      = SPComp.bind (SPComp.sample Bool) (fun c => SPComp.pure c) :=
  xorSampleBijRhsCompiled.correct V

/-- **Native XOR-bijection peephole security over the crypto dialect.** The two
    sides of `xor_sample_bij` are at `SPComp` distance `0` at every valuation —
    proved directly on `catCryptDialect`: native `Com.denoteSP` evaluation
    (`xorSampleBij_lhs_denoteSP`/`_rhs_denoteSP`) reduces both sides to
    `sample · ; pure ·`, equal by the XOR bijection `xorBij m`.
    (composition plumbing) -/
theorem xor_sample_bij_dialect_secure_native :
    ∀ V : Ctxt.Valuation (d := catCryptDialect) [.bit],
      sdist (fun (_ : Unit) => Com.denoteSP xorSampleBij_lhs_dialect V)
            (fun (_ : Unit) => Com.denoteSP xorSampleBij_rhs_dialect V) = 0 := by
  intro V
  have heq : Com.denoteSP xorSampleBij_lhs_dialect V
      = Com.denoteSP xorSampleBij_rhs_dialect V := by
    rw [xorSampleBij_lhs_denoteSP, xorSampleBij_rhs_denoteSP]
    exact SPComp.sample_bind_pure_equiv (xorBij (Ctxt.Var.here.lookup V)) id
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-! ## Peephole: native security of `bvAnd(x, x) = x`

`bvAnd_self_identity 8` rewrites `let y = bvAnd(x, x) in ret y` to `ret x`. On
the dialect both denote (purely) to `pure x`, so they are distance `0` — proved
directly on `catCryptDialect`. -/

/-- Native denotation of the `bvAnd`-self peephole LHS on the crypto dialect:
    `pure (x &&& x)`, which `BitVec.and_self` collapses to `pure x`. -/
theorem bvAndSelf_lhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.sword 8]) :
    Com.denoteSP bvAndSelf_lhs_dialect V
      = SPComp.pure (Ctxt.Var.here.lookup V) :=
  (bvAndSelfLhsCompiled.correct V).trans (congrArg SPComp.pure BitVec.and_self)

/-- Native denotation of the `bvAnd`-self peephole RHS on the crypto dialect:
    `pure x`. -/
theorem bvAndSelf_rhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.sword 8]) :
    Com.denoteSP bvAndSelf_rhs_dialect V
      = SPComp.pure (Ctxt.Var.here.lookup V) := by
  simp only [bvAndSelf_rhs_dialect, Com.denoteSP_ret]

/-- **Native `bvAnd(x, x) = x` peephole security over the crypto dialect.** Both
    sides denote to `pure x` (`bvAndSelf_lhs_denoteSP` reduces `x &&& x` to `x`
    via `BitVec.and_self`), so the `SPComp` distance is `0` at every valuation.
    Proved directly on `catCryptDialect`. (composition plumbing) -/
theorem bvAnd_self_dialect_secure_native :
    ∀ V : Ctxt.Valuation (d := catCryptDialect) [.sword 8],
      sdist (fun (_ : Unit) => Com.denoteSP bvAndSelf_lhs_dialect V)
            (fun (_ : Unit) => Com.denoteSP bvAndSelf_rhs_dialect V) = 0 := by
  intro V
  have heq : Com.denoteSP bvAndSelf_lhs_dialect V
      = Com.denoteSP bvAndSelf_rhs_dialect V := by
    rw [bvAndSelf_lhs_denoteSP, bvAndSelf_rhs_denoteSP]
  rw [funext fun (_ : Unit) => heq, sdist_self]

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative
