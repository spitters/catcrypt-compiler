/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# DR-collapse Phase 2 — the crypto dialect's `SPComp` security interpretation

`catCryptDialect` (in `VIR/CatCryptDialect.lean`) now carries the sample ops
(`sampleBit` / `sampleBv`) alongside the pure fragment, but its registered
`DialectDenote` (`catCryptDenote`) is the *pure compile* interpretation: a
sample denotes to its deterministic zero-entropy leaf (`false` / `0`). That is
the meaning the compile path needs.

The *security* meaning of a sample is probabilistic. Per the DR principle,
probability is an **interpretation**, not a compile-path op — so we give it
here as a second, `SPComp`-valued interpretation of the very same dialect:

* `catCryptDenoteSP` — the op-level interpretation. Every **pure** op denotes to
  `SPComp.pure` of its `catCryptDenote.denote` value; `sampleBit` denotes to
  `SPComp.sample Bool` and `sampleBv n` to `SPComp.sample (BitVec n)`.
* `Com.denoteSP` — the whole-program `SPComp` interpretation, mirroring the
  structure of `CryptoSSA.CProg.denote` (`.ret → SPComp.pure`, `.var → bind`).

The full agreement `CProg.denote ≅ Com.denoteSP` (sample ops included) lives in
`CryptoSSAToCryptoDialectFull.lean`; this file is the interpretation it targets.

**0 axioms**, **0 sorries**.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP

open CatCrypt.Core
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

/-! ## 1. The op-level `SPComp` interpretation -/

/-- Probabilistic / security interpretation of a `catCryptDialect` op:
    `sampleBit → SPComp.sample Bool`, `sampleBv n → SPComp.sample (BitVec n)`,
    and every pure op → `SPComp.pure` of its compile (`catCryptDenote`) value.

    This is the second interpretation of the dialect: the pure
    `catCryptDenote` is the compile meaning, this is the security meaning. -/
noncomputable def catCryptDenoteSP
    (op : CatCryptOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := catCryptDialect) op)) :
    SPComp ⟦DialectSignature.ret (d := catCryptDialect) op⟧ :=
  match op with
  | .sampleBit => SPComp.sample Bool
  | .sampleBv n => SPComp.sample (BitVec n)
  | op => SPComp.pure (catCryptDenote.denote op args)

/-! ## 2. Sanity: on a pure op the security interpretation is `SPComp.pure` -/

/-- On every **pure** op (everything except `sampleBit` / `sampleBv`),
    `catCryptDenoteSP` is `SPComp.pure` of the compile-path
    `catCryptDenote.denote` value. -/
theorem catCryptDenoteSP_pure
    (op : CatCryptOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := catCryptDialect) op))
    (h : op ≠ .sampleBit) (hb : ∀ n, op ≠ .sampleBv n) :
    catCryptDenoteSP op args = SPComp.pure (catCryptDenote.denote op args) := by
  cases op <;> simp_all [catCryptDenoteSP]

/-- `catCryptDenoteSP` on `sampleBit` is `SPComp.sample Bool`. -/
@[simp] theorem catCryptDenoteSP_sampleBit
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := catCryptDialect) .sampleBit)) :
    catCryptDenoteSP .sampleBit args = SPComp.sample Bool := rfl

/-- `catCryptDenoteSP` on `sampleBv n` is `SPComp.sample (BitVec n)`. -/
@[simp] theorem catCryptDenoteSP_sampleBv (n : Nat)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := catCryptDialect) (.sampleBv n))) :
    catCryptDenoteSP (.sampleBv n) args = SPComp.sample (BitVec n) := rfl

/-! ## 3. The whole-program `SPComp` interpretation `Com.denoteSP`

The `Com catCryptDialect` interpretation under `catCryptDenoteSP`. Mirrors
`CryptoSSA.CProg.denote`'s structure: `.ret v → SPComp.pure (v.lookup V)`,
`.var e body → SPComp.bind` of the expr's `SPComp` value into the body. -/

/-- `SPComp`-valued interpretation of an `Expr catCryptDialect`: resolve the
    arguments against the valuation, then apply `catCryptDenoteSP`. The
    `retTy_eq` witness re-indexes the result to the expression's type `t`. -/
noncomputable def Expr.denoteSP
    {Γ : Ctxt catCryptDialect} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (V : Ctxt.Valuation Γ) : SPComp ⟦t⟧ :=
  e.retTy_eq ▸ catCryptDenoteSP e.op (Expr.lookupArgs e.args V)

/-- `SPComp`-valued (security) interpretation of a whole `Com catCryptDialect`
    program. `.ret v` returns `v.lookup V` purely; `.var e body` binds the
    expression's `SPComp` value into the body, extending the valuation — exactly
    the structure of `CryptoSSA.CProg.denote`. -/
noncomputable def Com.denoteSP :
    {Γ : Ctxt catCryptDialect} → {t : CryptoTy} →
    Com catCryptDialect Γ t → Ctxt.Valuation Γ → SPComp ⟦t⟧
  | _, _, .ret v, V => SPComp.pure (v.lookup V)
  | _, _, .var e body, V =>
      SPComp.bind (Expr.denoteSP e V) (fun x => Com.denoteSP body (V.extend x))

/-- Unfold lemma for `Com.denoteSP` on `.ret`. -/
@[simp] theorem Com.denoteSP_ret
    {Γ : Ctxt catCryptDialect} {t : CryptoTy} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ) :
    Com.denoteSP (Com.ret v : Com catCryptDialect Γ t) V = SPComp.pure (v.lookup V) := rfl

/-- Unfold lemma for `Com.denoteSP` on `.var`. -/
@[simp] theorem Com.denoteSP_var
    {Γ : Ctxt catCryptDialect} {t s : CryptoTy}
    (e : Expr catCryptDialect Γ t) (body : Com catCryptDialect (t :: Γ) s)
    (V : Ctxt.Valuation Γ) :
    Com.denoteSP (Com.var e body : Com catCryptDialect Γ s) V =
      SPComp.bind (Expr.denoteSP e V) (fun x => Com.denoteSP body (V.extend x)) := rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
