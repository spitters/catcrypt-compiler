/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative

/-!
# More peephole-security results, native on `Com catCryptDialect`

This file states and proves four further peephole-security results **directly on
`catCryptDialect`**, computing the `SPComp` distance through `Com.denoteSP` /
`catCryptDenoteSP`. It continues phase C.3 of the CProg-retirement plan, joining
`CryptoDialectSecurityNative.lean` and `MoreDialectSecurity.lean`:

* `xor_self_cancel` — XOR self-cancellation: `let y = xor(x, x); ret y ≡ ret false`.
* `bvAnd_self_identity n` — AND self-identity: `let y = bvAnd(x, x); ret y ≡ ret x`.
* `bvOr_self_identity n` — OR self-identity: `let y = bvOr(x, x); ret y ≡ ret x`.
* `sample_dce_bv n` — dead-`BitVec`-sample elimination: `let x = sampleBv n; ret v ≡ ret v`.

Each rewrite's two sides are built natively as `Com catCryptDialect` programs
through the `CryptoDialectRelCompile` combinators (`cxorBit` / `cbvAnd` / `cbvOr`
/ `cconstBit` / `csampleBv` / `cret`), so their `Com.denoteSP` reductions come
from the bundled `.spec`/`.correct`. The algebraic identities collapse both
sides to a common `pure ·` (via `Bool.xor_self` / `BitVec.and_self` /
`BitVec.or_self`); the dead-sample case uses that a uniform sample bound to an
unused variable is `pure`-absorbed (`SDistr.uniform_bind_const`). In every case
the `SPComp` distance is `0` at every valuation, by `sdist_self`.

The security view therefore lives on `catCryptDialect` alone.

## Anti-vacuity

Each ported theorem genuinely relates *distinct* programs (the `lhs` of each
rewrite binds an extra algebraic/sample op the `rhs` lacks), so none is
`0 = 0`; none routes through the valuation-free `Com.all_com_ct` shadow.

**0 axioms** beyond the standard `propext`/`Classical.choice`/`Quot.sound`,
**0 sorries**.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.MoreDialectSecurity2

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRelCompile
open scoped ENNReal

/-! ## 0. Extra combinators and the dead-sample fact

`CryptoDialectRelCompile` ships `cxorBit` / `cbvAnd` / `csampleBv` / `cret` but
not the `constBit` / `bvOr` binders; we add those `Compiled` combinators here,
mirroring `cbvAnd`. `sample_bind_const` is the dead-sample absorption fact
(a uniform sample bound to an unused variable is `pure`-absorbed). -/

/-- Bind a constant `b : Bool`. -/
noncomputable def cconstBit {Γ : Ctxt catCryptDialect} {s : CryptoTy} (b : Bool)
    (body : Compiled (CryptoTy.bit :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.constBit b, rfl, .nil⟩) body.com
  spec := fun V => body.spec (V.extend b)
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- Bind `bvOr a b`. -/
noncomputable def cbvOr {Γ : Ctxt catCryptDialect} {s : CryptoTy} {n : Nat}
    (a b : Ctxt.Var Γ (CryptoTy.sword n))
    (body : Compiled (CryptoTy.sword n :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.bvOr n, rfl, .cons a (.cons b .nil)⟩) body.com
  spec := fun V => body.spec (V.extend (BitVec.or (a.lookup V) (b.lookup V)))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- A uniform sample bound to an unused variable is `pure`-absorbed:
    `sample α >>= (fun _ => pure v) = pure v`. -/
private theorem sample_bind_const {α : Type} [Fintype α] [Nonempty α] {β : Type} (v : β) :
    SPComp.bind (SPComp.sample α) (fun _ => SPComp.pure v) = SPComp.pure v := by
  funext h
  simp only [SPComp.bind_def, SPComp.sample, SPComp.pure]
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_const (SDistr.pure (v, h))

/-! ## 1. XOR self-cancellation (`xor(x, x) = false`) on the dialect -/

/-- The XOR-self-cancel rewrite's *pre-rewrite* side (`let y = xor(x, x); ret y`). -/
noncomputable def xorSelfCancelLhsCompiled : Compiled [CryptoTy.bit] CryptoTy.bit :=
  cxorBit Ctxt.Var.here Ctxt.Var.here (cret Ctxt.Var.here)

noncomputable def xorSelfCancel_lhs_dialect : Com catCryptDialect [.bit] .bit :=
  xorSelfCancelLhsCompiled.com

/-- The XOR-self-cancel rewrite's *post-rewrite* side (`let y = constBit false; ret y`). -/
noncomputable def xorSelfCancelRhsCompiled : Compiled [CryptoTy.bit] CryptoTy.bit :=
  cconstBit false (cret Ctxt.Var.here)

noncomputable def xorSelfCancel_rhs_dialect : Com catCryptDialect [.bit] .bit :=
  xorSelfCancelRhsCompiled.com

/-- Native denotation of the XOR-self LHS: `pure (x ^^^ x)`, which
    `Bool.xor_self` collapses to `pure false`. -/
theorem xorSelfCancel_lhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP xorSelfCancel_lhs_dialect V = SPComp.pure false :=
  (xorSelfCancelLhsCompiled.correct V).trans (congrArg SPComp.pure (Bool.xor_self _))

/-- Native denotation of the XOR-self RHS: `pure false`. -/
theorem xorSelfCancel_rhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP xorSelfCancel_rhs_dialect V = SPComp.pure false :=
  xorSelfCancelRhsCompiled.correct V

/-- **Dialect-level XOR-self-cancellation perfect security.** The pre- and
    post-rewrite sides, as `Com catCryptDialect` programs, are at zero
    statistical distance at every valuation: `xor(x, x)` always equals `false`.
    Proved directly on `catCryptDialect` (both denote to `pure false`), with
    `sdist_self`. -/
theorem xorSelfCancel_dialect_security
    (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    sdist (fun (_ : Unit) => Com.denoteSP xorSelfCancel_lhs_dialect V)
          (fun (_ : Unit) => Com.denoteSP xorSelfCancel_rhs_dialect V) = 0 := by
  have heq : Com.denoteSP xorSelfCancel_lhs_dialect V
      = Com.denoteSP xorSelfCancel_rhs_dialect V := by
    rw [xorSelfCancel_lhs_denoteSP, xorSelfCancel_rhs_denoteSP]
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form, mirroring `progSdist`'s shape. -/
theorem xorSelfCancel_dialect_iSup_zero :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.bit],
        sdist (fun (_ : Unit) => Com.denoteSP xorSelfCancel_lhs_dialect V)
              (fun (_ : Unit) => Com.denoteSP xorSelfCancel_rhs_dialect V)) = 0 := by
  simp only [xorSelfCancel_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

/-! ## 2. `BitVec n` AND self-identity (`bvAnd(x, x) = x`) on the dialect -/

/-- The AND-self-identity rewrite's *pre-rewrite* side (`let y = bvAnd(x, x); ret y`). -/
noncomputable def bvAndSelfIdentityLhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  cbvAnd Ctxt.Var.here Ctxt.Var.here (cret Ctxt.Var.here)

noncomputable def bvAndSelfIdentity_lhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvAndSelfIdentityLhsCompiled n).com

/-- The AND-self-identity rewrite's *post-rewrite* side (`ret x`). -/
noncomputable def bvAndSelfIdentity_rhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  Com.ret Ctxt.Var.here

/-- Native denotation of the AND-self LHS: `pure (x &&& x)`, which
    `BitVec.and_self` collapses to `pure x`. -/
theorem bvAndSelfIdentity_lhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvAndSelfIdentity_lhs_dialect n) V = SPComp.pure (Ctxt.Var.here.lookup V) :=
  ((bvAndSelfIdentityLhsCompiled n).correct V).trans (congrArg SPComp.pure BitVec.and_self)

/-- Native denotation of the AND-self RHS: `pure x`. -/
theorem bvAndSelfIdentity_rhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvAndSelfIdentity_rhs_dialect n) V = SPComp.pure (Ctxt.Var.here.lookup V) := by
  simp only [bvAndSelfIdentity_rhs_dialect, Com.denoteSP_ret]

/-- **Dialect-level `BitVec n` AND-self-identity security.** The pre- and
    post-rewrite sides, as `Com catCryptDialect` programs, are at zero
    statistical distance at every valuation: `bvAnd(x, x)` always equals `x`.
    Proved directly on `catCryptDialect` (both denote to `pure x`), with
    `sdist_self`. -/
theorem bvAndSelfIdentity_dialect_security (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    sdist (fun (_ : Unit) => Com.denoteSP (bvAndSelfIdentity_lhs_dialect n) V)
          (fun (_ : Unit) => Com.denoteSP (bvAndSelfIdentity_rhs_dialect n) V) = 0 := by
  have heq : Com.denoteSP (bvAndSelfIdentity_lhs_dialect n) V
      = Com.denoteSP (bvAndSelfIdentity_rhs_dialect n) V := by
    rw [bvAndSelfIdentity_lhs_denoteSP, bvAndSelfIdentity_rhs_denoteSP]
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form. -/
theorem bvAndSelfIdentity_dialect_iSup_zero (n : Nat) :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.sword n],
        sdist (fun (_ : Unit) => Com.denoteSP (bvAndSelfIdentity_lhs_dialect n) V)
              (fun (_ : Unit) => Com.denoteSP (bvAndSelfIdentity_rhs_dialect n) V)) = 0 := by
  simp only [bvAndSelfIdentity_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

/-! ## 3. `BitVec n` OR self-identity (`bvOr(x, x) = x`) on the dialect -/

/-- The OR-self-identity rewrite's *pre-rewrite* side (`let y = bvOr(x, x); ret y`). -/
noncomputable def bvOrSelfIdentityLhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  cbvOr Ctxt.Var.here Ctxt.Var.here (cret Ctxt.Var.here)

noncomputable def bvOrSelfIdentity_lhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvOrSelfIdentityLhsCompiled n).com

/-- The OR-self-identity rewrite's *post-rewrite* side (`ret x`). -/
noncomputable def bvOrSelfIdentity_rhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  Com.ret Ctxt.Var.here

/-- Native denotation of the OR-self LHS: `pure (x ||| x)`, which
    `BitVec.or_self` collapses to `pure x`. -/
theorem bvOrSelfIdentity_lhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvOrSelfIdentity_lhs_dialect n) V = SPComp.pure (Ctxt.Var.here.lookup V) :=
  ((bvOrSelfIdentityLhsCompiled n).correct V).trans (congrArg SPComp.pure BitVec.or_self)

/-- Native denotation of the OR-self RHS: `pure x`. -/
theorem bvOrSelfIdentity_rhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvOrSelfIdentity_rhs_dialect n) V = SPComp.pure (Ctxt.Var.here.lookup V) := by
  simp only [bvOrSelfIdentity_rhs_dialect, Com.denoteSP_ret]

/-- **Dialect-level `BitVec n` OR-self-identity security.** The pre- and
    post-rewrite sides, as `Com catCryptDialect` programs, are at zero
    statistical distance at every valuation: `bvOr(x, x)` always equals `x`.
    Proved directly on `catCryptDialect` (both denote to `pure x`), with
    `sdist_self`. -/
theorem bvOrSelfIdentity_dialect_security (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    sdist (fun (_ : Unit) => Com.denoteSP (bvOrSelfIdentity_lhs_dialect n) V)
          (fun (_ : Unit) => Com.denoteSP (bvOrSelfIdentity_rhs_dialect n) V) = 0 := by
  have heq : Com.denoteSP (bvOrSelfIdentity_lhs_dialect n) V
      = Com.denoteSP (bvOrSelfIdentity_rhs_dialect n) V := by
    rw [bvOrSelfIdentity_lhs_denoteSP, bvOrSelfIdentity_rhs_denoteSP]
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form. -/
theorem bvOrSelfIdentity_dialect_iSup_zero (n : Nat) :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.sword n],
        sdist (fun (_ : Unit) => Com.denoteSP (bvOrSelfIdentity_lhs_dialect n) V)
              (fun (_ : Unit) => Com.denoteSP (bvOrSelfIdentity_rhs_dialect n) V)) = 0 := by
  simp only [bvOrSelfIdentity_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

/-! ## 4. Dead-`BitVec`-sample DCE (`sampleBv n` unused) on the dialect -/

/-- The dead-sample rewrite's *pre-DCE* side (`let x = sampleBv n; ret v`). -/
noncomputable def sampleDceBvLhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  csampleBv n (cret (Ctxt.Var.there Ctxt.Var.here))

noncomputable def sampleDceBv_lhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (sampleDceBvLhsCompiled n).com

/-- The dead-sample rewrite's *post-DCE* side (`ret v`). -/
noncomputable def sampleDceBv_rhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  Com.ret Ctxt.Var.here

/-- Native denotation of the dead-sample LHS: `sample (BitVec n) >>= (fun _ => pure v)`. -/
theorem sampleDceBv_lhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (sampleDceBv_lhs_dialect n) V
      = SPComp.bind (SPComp.sample (BitVec n))
          (fun _ => SPComp.pure (Ctxt.Var.here.lookup V)) :=
  (sampleDceBvLhsCompiled n).correct V

/-- Native denotation of the dead-sample RHS: `pure v`. -/
theorem sampleDceBv_rhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (sampleDceBv_rhs_dialect n) V = SPComp.pure (Ctxt.Var.here.lookup V) := by
  simp only [sampleDceBv_rhs_dialect, Com.denoteSP_ret]

/-- **Dialect-level dead-`BitVec`-sample DCE security.** The pre- and post-DCE
    sides, as `Com catCryptDialect` programs, are at zero statistical distance at
    every valuation: dropping an unused `BitVec n` sample is unobservable.
    Proved directly on `catCryptDialect` (the unused sample is `pure`-absorbed by
    `sample_bind_const`), with `sdist_self`. -/
theorem sampleDceBv_dialect_security (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    sdist (fun (_ : Unit) => Com.denoteSP (sampleDceBv_lhs_dialect n) V)
          (fun (_ : Unit) => Com.denoteSP (sampleDceBv_rhs_dialect n) V) = 0 := by
  have heq : Com.denoteSP (sampleDceBv_lhs_dialect n) V
      = Com.denoteSP (sampleDceBv_rhs_dialect n) V := by
    rw [sampleDceBv_lhs_denoteSP, sampleDceBv_rhs_denoteSP]
    exact sample_bind_const _
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form. -/
theorem sampleDceBv_dialect_iSup_zero (n : Nat) :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.sword n],
        sdist (fun (_ : Unit) => Com.denoteSP (sampleDceBv_lhs_dialect n) V)
              (fun (_ : Unit) => Com.denoteSP (sampleDceBv_rhs_dialect n) V)) = 0 := by
  simp only [sampleDceBv_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

end CatCrypt.Crypto.SecureCompilation.Dialects.MoreDialectSecurity2
