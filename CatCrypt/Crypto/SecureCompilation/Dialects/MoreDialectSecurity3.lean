/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative

/-!
# Lifted algebraic-rewrite security results, native on `Com catCryptDialect`

This module states and proves two algebraic peephole-security results
**directly on `catCryptDialect`**, computing the `SPComp` distance through
`Com.denoteSP` / `catCryptDenoteSP`. Alongside
`CryptoDialectSecurityNative.lean`, `MoreDialectSecurity.lean` and
`MoreDialectSecurity2.lean`, it covers the `BitVec n`
self-cancellation identities

* `bvXor(x, x) = 0` (the program form of `BitVec.xor_self`), and
* `bvSub(x, x) = 0` (the program form of `BitVec.sub_self`).

Each rewrite's two sides are built natively as `Com catCryptDialect` programs
through the `CryptoDialectRelCompile` combinators (`cxor` / `cbvSub` / `cbvConst`
/ `cret`), so their `Com.denoteSP` reductions come from the bundled
`.spec`/`.correct`. Both sides denote (purely) to `pure (0 : BitVec n)` — the
left through the relevant `BitVec` self-identity — so they are at `SPComp`
distance `0` at every valuation, by `sdist_self`.

The security view therefore lives on `catCryptDialect` alone.

## Anti-vacuity

Each theorem relates *distinct* programs (the `lhs` binds an
algebraic `bvXor`/`bvSub` op whose `rhs` binds a `bvConst 0` instead), so none
is `0 = 0`; none routes through a valuation-free constant-time predicate.

**0 axioms** beyond the standard `propext`/`Classical.choice`/`Quot.sound`;
all goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.MoreDialectSecurity3

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRelCompile
open scoped ENNReal

/-! ## 0. A `bvSub` combinator

`CryptoDialectRelCompile` ships `cxor` (`bvXor`) / `cbvAnd` / `cbvConst` but not
`bvSub`; we add the `Compiled` combinator here, mirroring `cbvAnd`. -/

/-- Bind `bvSub a b`. -/
noncomputable def cbvSub {Γ : Ctxt catCryptDialect} {s : CryptoTy} {n : Nat}
    (a b : Ctxt.Var Γ (CryptoTy.sword n))
    (body : Compiled (CryptoTy.sword n :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.bvSub n, rfl, .cons a (.cons b .nil)⟩) body.com
  spec := fun V => body.spec (V.extend (BitVec.sub (a.lookup V) (b.lookup V)))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-! ## 1. `BitVec n` XOR self-cancellation (`bvXor(x, x) = 0`) on the dialect -/

/-- The `BitVec n` XOR-self-cancel rewrite's *pre-rewrite* side
    (`let y = bvXor(x, x); ret y`). -/
noncomputable def bvXorSelfDemoLhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  cxor Ctxt.Var.here Ctxt.Var.here (cret Ctxt.Var.here)

noncomputable def bvXorSelfDemo_lhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvXorSelfDemoLhsCompiled n).com

/-- The `BitVec n` XOR-self-cancel rewrite's *post-rewrite* side
    (`let y = bvConst 0; ret y`). -/
noncomputable def bvXorSelfDemoRhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  cbvConst n 0 (cret Ctxt.Var.here)

noncomputable def bvXorSelfDemo_rhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvXorSelfDemoRhsCompiled n).com

/-- Native denotation of the XOR-self LHS: `pure (x ^^^ x)`, which
    `BitVec.xor_self` collapses to `pure 0`. -/
theorem bvXorSelfDemo_lhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvXorSelfDemo_lhs_dialect n) V = SPComp.pure (0 : BitVec n) :=
  ((bvXorSelfDemoLhsCompiled n).correct V).trans (congrArg SPComp.pure BitVec.xor_self)

/-- Native denotation of the XOR-self RHS: `pure 0`. -/
theorem bvXorSelfDemo_rhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvXorSelfDemo_rhs_dialect n) V = SPComp.pure (0 : BitVec n) :=
  (bvXorSelfDemoRhsCompiled n).correct V

/-- **Dialect-level `BitVec n` XOR-self-cancellation security.** The pre- and
    post-rewrite sides, as `Com catCryptDialect` programs, are at zero
    statistical distance at every valuation: `bvXor(x, x)` always equals the
    zero word. Proved directly on `catCryptDialect` (both denote to `pure 0`),
    with `sdist_self`. -/
theorem bvXorSelfDemo_dialect_security (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    sdist (fun (_ : Unit) => Com.denoteSP (bvXorSelfDemo_lhs_dialect n) V)
          (fun (_ : Unit) => Com.denoteSP (bvXorSelfDemo_rhs_dialect n) V) = 0 := by
  have heq : Com.denoteSP (bvXorSelfDemo_lhs_dialect n) V
      = Com.denoteSP (bvXorSelfDemo_rhs_dialect n) V := by
    rw [bvXorSelfDemo_lhs_denoteSP, bvXorSelfDemo_rhs_denoteSP]
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form, mirroring `progSdist`'s shape. -/
theorem bvXorSelfDemo_dialect_iSup_zero (n : Nat) :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.sword n],
        sdist (fun (_ : Unit) => Com.denoteSP (bvXorSelfDemo_lhs_dialect n) V)
              (fun (_ : Unit) => Com.denoteSP (bvXorSelfDemo_rhs_dialect n) V)) = 0 := by
  simp only [bvXorSelfDemo_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

/-! ## 2. `BitVec n` SUB self-cancellation (`bvSub(x, x) = 0`) on the dialect -/

/-- The SUB-self-cancel rewrite's *pre-rewrite* side
    (`let y = bvSub(x, x); ret y`). -/
noncomputable def bvSubSelfCancelLhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  cbvSub Ctxt.Var.here Ctxt.Var.here (cret Ctxt.Var.here)

noncomputable def bvSubSelfCancel_lhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvSubSelfCancelLhsCompiled n).com

/-- The SUB-self-cancel rewrite's *post-rewrite* side
    (`let y = bvConst 0; ret y`). -/
noncomputable def bvSubSelfCancelRhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  cbvConst n 0 (cret Ctxt.Var.here)

noncomputable def bvSubSelfCancel_rhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvSubSelfCancelRhsCompiled n).com

/-- Native denotation of the SUB-self LHS: `pure (x - x)`, which
    `BitVec.sub_self` collapses to `pure 0`. -/
theorem bvSubSelfCancel_lhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvSubSelfCancel_lhs_dialect n) V = SPComp.pure (0 : BitVec n) :=
  ((bvSubSelfCancelLhsCompiled n).correct V).trans (congrArg SPComp.pure (BitVec.sub_self _))

/-- Native denotation of the SUB-self RHS: `pure 0`. -/
theorem bvSubSelfCancel_rhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvSubSelfCancel_rhs_dialect n) V = SPComp.pure (0 : BitVec n) :=
  (bvSubSelfCancelRhsCompiled n).correct V

/-- **Dialect-level `BitVec n` SUB-self-cancellation security.** The pre- and
    post-rewrite sides, as `Com catCryptDialect` programs, are at zero
    statistical distance at every valuation: `bvSub(x, x)` always equals the
    zero word. Proved directly on `catCryptDialect` (both denote to `pure 0`),
    with `sdist_self`. -/
theorem bvSubSelfCancel_dialect_security (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    sdist (fun (_ : Unit) => Com.denoteSP (bvSubSelfCancel_lhs_dialect n) V)
          (fun (_ : Unit) => Com.denoteSP (bvSubSelfCancel_rhs_dialect n) V) = 0 := by
  have heq : Com.denoteSP (bvSubSelfCancel_lhs_dialect n) V
      = Com.denoteSP (bvSubSelfCancel_rhs_dialect n) V := by
    rw [bvSubSelfCancel_lhs_denoteSP, bvSubSelfCancel_rhs_denoteSP]
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form. -/
theorem bvSubSelfCancel_dialect_iSup_zero (n : Nat) :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.sword n],
        sdist (fun (_ : Unit) => Com.denoteSP (bvSubSelfCancel_lhs_dialect n) V)
              (fun (_ : Unit) => Com.denoteSP (bvSubSelfCancel_rhs_dialect n) V)) = 0 := by
  simp only [bvSubSelfCancel_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

end CatCrypt.Crypto.SecureCompilation.Dialects.MoreDialectSecurity3
