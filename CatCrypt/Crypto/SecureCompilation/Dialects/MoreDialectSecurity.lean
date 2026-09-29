/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative

/-!
# More peephole-security results, native on `Com catCryptDialect`

This module states and proves three peephole-security results **directly on
`catCryptDialect`**, computing the `SPComp` distance through `Com.denoteSP` /
`catCryptDenoteSP`, alongside the OTP/peephole results of
`CryptoDialectSecurityNative.lean`:

* `xor_sample_bij` — **THE OTP security argument as a peephole**:
  `let k = sampleBit; let c = xor(k, m); ret c  ≡  let c = sampleBit; ret c`.
  The XOR-with-`m` bijection makes the ciphertext distribution uniform. It is
  proved from the native `xor_sample_bij_dialect_secure_native`.
* `bvXor_sample_bij n` — the `BitVec n` analogue of the above (the BitVec OTP).
* `sample_dce_bit` — dead-code elimination of an unused sample:
  `let x = sampleBit; ret v  ≡  ret v`.

The `BitVec n` and dead-sample programs are built natively as `Com catCryptDialect`
programs through the `CryptoDialectRelCompile` combinators (`csampleBv` / `cxor`
/ `csampleBit` / `cret`), so their `Com.denoteSP` reductions come from the
bundled `.spec`/`.correct`. The XOR-bijection argument is
`SPComp.sample_bind_pure_equiv (bvXorBij m) id` (`(· ^^^ m)` is a bijection on
`BitVec n`); the dead-sample case uses that a uniform sample bound to an unused
variable is `pure`-absorbed (`SDistr.uniform_bind_const`). In every case the
`SPComp` distance is `0` at every valuation, by `sdist_self`.

The security view therefore lives on `catCryptDialect` alone.

## Anti-vacuity

Each theorem relates *distinct* programs (the `lhs` of each
rewrite binds an extra `xor`/`sample`, the `rhs` does not), so none is `0 = 0`;
none routes through a valuation-free constant-time predicate.

**0 axioms** beyond the standard `propext`/`Classical.choice`/`Quot.sound`;
all goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.MoreDialectSecurity

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRelCompile
open scoped ENNReal

/-! ## 0. The `BitVec n` XOR bijection and the dead-sample fact -/

/-- XOR with a fixed `BitVec n` is a bijection (key for the BitVec OTP). -/
def bvXorBij {n : Nat} (m : BitVec n) : BitVec n ≃ BitVec n where
  toFun k := k ^^^ m
  invFun c := c ^^^ m
  left_inv k := by simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv c := by simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- A uniform sample bound to an unused variable is `pure`-absorbed:
    `sample α >>= (fun _ => pure v) = pure v`. -/
theorem sample_bind_const {α : Type} [Fintype α] [Nonempty α] {β : Type} (v : β) :
    SPComp.bind (SPComp.sample α) (fun _ => SPComp.pure v) = SPComp.pure v := by
  funext h
  simp only [SPComp.bind_def, SPComp.sample, SPComp.pure]
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_const (SDistr.pure (v, h))

/-! ## 1. The XOR-bijection rewrite (`xor_sample_bij`) on the dialect

`xor_sample_bij` is the bit OTP security argument phrased as a peephole over
`[.bit]`: its `lhs` samples a key and XORs with the message, its `rhs` samples
the ciphertext directly. It is an alias of the native version proved in
`CryptoDialectSecurityNative.lean`. -/

/-- The XOR-bijection rewrite's *real* side
    (`let k = sampleBit; let c = xor(k, m); ret c`) as a `catCryptDialect`
    program (the native one). -/
noncomputable def xorSampleBij_lhs_dialect : Com catCryptDialect [.bit] .bit :=
  CryptoDialectSecurityNative.xorSampleBij_lhs_dialect

/-- The XOR-bijection rewrite's *ideal* side (`let c = sampleBit; ret c`) as a
    `catCryptDialect` program (the native one). -/
noncomputable def xorSampleBij_rhs_dialect : Com catCryptDialect [.bit] .bit :=
  CryptoDialectSecurityNative.xorSampleBij_rhs_dialect

/-- **Dialect-level XOR-bijection perfect security.** The two sides of the OTP
    XOR-bijection peephole, as `Com catCryptDialect` programs, are at zero
    statistical distance at every valuation: sampling a key and XORing it into
    the message is perfectly indistinguishable from sampling the ciphertext.
    Re-pointed at the native `xor_sample_bij_dialect_secure_native`. -/
theorem xorSampleBij_dialect_security
    (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    sdist (fun (_ : Unit) => Com.denoteSP xorSampleBij_lhs_dialect V)
          (fun (_ : Unit) => Com.denoteSP xorSampleBij_rhs_dialect V) = 0 :=
  CryptoDialectSecurityNative.xor_sample_bij_dialect_secure_native V

/-- Packaged supremum form, mirroring `progSdist`'s shape. -/
theorem xorSampleBij_dialect_iSup_zero :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.bit],
        sdist (fun (_ : Unit) => Com.denoteSP xorSampleBij_lhs_dialect V)
              (fun (_ : Unit) => Com.denoteSP xorSampleBij_rhs_dialect V)) = 0 := by
  simp only [xorSampleBij_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

/-! ## 2. The `BitVec n` XOR-bijection rewrite (`bvXor_sample_bij`) on the dialect -/

/-- The `BitVec n` XOR-bijection rewrite's *real* side
    (`let k = sampleBv n; let c = bvXor(k, m); ret c`). -/
noncomputable def bvXorSampleBijLhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  csampleBv n (cxor Ctxt.Var.here (Ctxt.Var.there Ctxt.Var.here) (cret Ctxt.Var.here))

noncomputable def bvXorSampleBij_lhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvXorSampleBijLhsCompiled n).com

/-- The `BitVec n` XOR-bijection rewrite's *ideal* side (`let c = sampleBv n; ret c`). -/
noncomputable def bvXorSampleBijRhsCompiled (n : Nat) :
    Compiled [CryptoTy.sword n] (CryptoTy.sword n) :=
  csampleBv n (cret Ctxt.Var.here)

noncomputable def bvXorSampleBij_rhs_dialect (n : Nat) :
    Com catCryptDialect [.sword n] (.sword n) :=
  (bvXorSampleBijRhsCompiled n).com

/-- Native denotation of the BitVec OTP real side: `sample k; pure (k ^^^ m)`. -/
theorem bvXorSampleBij_lhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvXorSampleBij_lhs_dialect n) V
      = SPComp.bind (SPComp.sample (BitVec n))
          (fun k => SPComp.pure (BitVec.xor k (Ctxt.Var.here.lookup V))) :=
  (bvXorSampleBijLhsCompiled n).correct V

/-- Native denotation of the BitVec OTP ideal side: `sample c; pure c`. -/
theorem bvXorSampleBij_rhs_denoteSP (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    Com.denoteSP (bvXorSampleBij_rhs_dialect n) V
      = SPComp.bind (SPComp.sample (BitVec n)) (fun c => SPComp.pure c) :=
  (bvXorSampleBijRhsCompiled n).correct V

/-- **Dialect-level `BitVec n` XOR-bijection perfect security.** The two sides
    of the `BitVec n` OTP peephole, as `Com catCryptDialect` programs, are at
    zero statistical distance at every valuation. Proved directly on
    `catCryptDialect`: native `Com.denoteSP` evaluation reduces both sides to
    `sample · ; pure ·`, equal by the XOR bijection `bvXorBij m`. -/
theorem bvXorSampleBij_dialect_security (n : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) [.sword n]) :
    sdist (fun (_ : Unit) => Com.denoteSP (bvXorSampleBij_lhs_dialect n) V)
          (fun (_ : Unit) => Com.denoteSP (bvXorSampleBij_rhs_dialect n) V) = 0 := by
  have heq : Com.denoteSP (bvXorSampleBij_lhs_dialect n) V
      = Com.denoteSP (bvXorSampleBij_rhs_dialect n) V := by
    rw [bvXorSampleBij_lhs_denoteSP, bvXorSampleBij_rhs_denoteSP]
    exact SPComp.sample_bind_pure_equiv (bvXorBij (Ctxt.Var.here.lookup V)) id
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form. -/
theorem bvXorSampleBij_dialect_iSup_zero (n : Nat) :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.sword n],
        sdist (fun (_ : Unit) => Com.denoteSP (bvXorSampleBij_lhs_dialect n) V)
              (fun (_ : Unit) => Com.denoteSP (bvXorSampleBij_rhs_dialect n) V)) = 0 := by
  simp only [bvXorSampleBij_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

/-! ## 3. Dead-sample DCE (`sample_dce_bit`) on the dialect -/

/-- The dead-sample rewrite's *pre-DCE* side (`let x = sampleBit; ret v`). -/
noncomputable def sampleDceBitLhsCompiled : Compiled [CryptoTy.bit] CryptoTy.bit :=
  csampleBit (cret (Ctxt.Var.there Ctxt.Var.here))

noncomputable def sampleDceBit_lhs_dialect : Com catCryptDialect [.bit] .bit :=
  sampleDceBitLhsCompiled.com

/-- The dead-sample rewrite's *post-DCE* side (`ret v`). -/
noncomputable def sampleDceBit_rhs_dialect : Com catCryptDialect [.bit] .bit :=
  Com.ret Ctxt.Var.here

/-- Native denotation of the dead-sample LHS: `sample Bool >>= (fun _ => pure v)`. -/
theorem sampleDceBit_lhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP sampleDceBit_lhs_dialect V
      = SPComp.bind (SPComp.sample Bool) (fun _ => SPComp.pure (Ctxt.Var.here.lookup V)) :=
  sampleDceBitLhsCompiled.correct V

/-- Native denotation of the dead-sample RHS: `pure v`. -/
theorem sampleDceBit_rhs_denoteSP (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    Com.denoteSP sampleDceBit_rhs_dialect V = SPComp.pure (Ctxt.Var.here.lookup V) := by
  simp only [sampleDceBit_rhs_dialect, Com.denoteSP_ret]

/-- **Dialect-level dead-sample DCE security.** The pre- and post-DCE sides, as
    `Com catCryptDialect` programs, are at zero statistical distance at every
    valuation: dropping an unused sample is unobservable. Proved directly on
    `catCryptDialect` (the unused sample is `pure`-absorbed by
    `sample_bind_const`), with `sdist_self`. -/
theorem sampleDceBit_dialect_security
    (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    sdist (fun (_ : Unit) => Com.denoteSP sampleDceBit_lhs_dialect V)
          (fun (_ : Unit) => Com.denoteSP sampleDceBit_rhs_dialect V) = 0 := by
  have heq : Com.denoteSP sampleDceBit_lhs_dialect V
      = Com.denoteSP sampleDceBit_rhs_dialect V := by
    rw [sampleDceBit_lhs_denoteSP, sampleDceBit_rhs_denoteSP]
    exact sample_bind_const _
  rw [funext fun (_ : Unit) => heq, sdist_self]

/-- Packaged supremum form. -/
theorem sampleDceBit_dialect_iSup_zero :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.bit],
        sdist (fun (_ : Unit) => Com.denoteSP sampleDceBit_lhs_dialect V)
              (fun (_ : Unit) => Com.denoteSP sampleDceBit_rhs_dialect V)) = 0 := by
  simp only [sampleDceBit_dialect_security]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

end CatCrypt.Crypto.SecureCompilation.Dialects.MoreDialectSecurity
