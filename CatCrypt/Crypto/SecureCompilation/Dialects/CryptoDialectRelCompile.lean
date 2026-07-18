/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP

/-!
# Relational compilation for the probabilistic `catCryptDialect`

A Rupicola-style proof-producing layer for building `Com catCryptDialect`
security programs together with the `SPComp` distribution they denote. A
`Compiled Γ t` bundles a dialect program `com`, the spec `spec` it denotes via
`Com.denoteSP`, and the proof `correct` that the two agree at every valuation.

Programs are assembled from per-operation combinators (`csampleBv`, `cxor`,
`cmkPair`, `cinr`, `cbvConst`, `cret`); their `spec`/`correct` compose, so a
caller obtains the program, its `SPComp` denotation, and the denotes-spec proof
without writing de-Bruijn `Com.var` nodes or a per-program `Com.denoteSP`
reduction. This is the sampling-aware analogue of the deterministic
`RelationalCompile` layer (which targets `Com jasminDialect`).

Each combinator's `correct` field reduces `Com.denoteSP (Com.var ⟨op, rfl, args⟩ ·)`
through `Com.denoteSP_var` / `Expr.denoteSP` / `catCryptDenoteSP`: `sampleBv n`
contributes an `SPComp.sample (BitVec n)` bind; every pure op contributes a
`SPComp.pure` that `SPComp.pure_bind` collapses into the continuation's spec at
the op's value.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRelCompile

open CatCrypt.Core
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP

/-- A `Com catCryptDialect Γ t` paired with the `SPComp` spec it denotes via
    `Com.denoteSP` and the proof that they agree at every valuation. -/
structure Compiled (Γ : Ctxt catCryptDialect) (t : CryptoTy) where
  com : Com catCryptDialect Γ t
  spec : Ctxt.Valuation Γ → SPComp ⟦t⟧
  correct : ∀ V, Com.denoteSP com V = spec V

/-- Return a variable: `ret v`. -/
noncomputable def cret {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (v : Ctxt.Var Γ t) : Compiled Γ t where
  com := Com.ret v
  spec := fun V => SPComp.pure (v.lookup V)
  correct := fun _ => rfl

/-- Sample a `BitVec n` and continue with it bound at `.here`. -/
noncomputable def csampleBv {Γ : Ctxt catCryptDialect} {s : CryptoTy} (n : Nat)
    (body : Compiled (CryptoTy.sword n :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.sampleBv n, rfl, .nil⟩) body.com
  spec := fun V => SPComp.bind (SPComp.sample (BitVec n)) (fun x => body.spec (V.extend x))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP]
    exact congrArg (SPComp.bind (SPComp.sample (BitVec n)))
      (funext fun x => body.correct (V.extend x))

/-- Bind a constant `c : BitVec n`. -/
noncomputable def cbvConst {Γ : Ctxt catCryptDialect} {s : CryptoTy} (n : Nat) (c : BitVec n)
    (body : Compiled (CryptoTy.sword n :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.bvConst n c, rfl, .nil⟩) body.com
  spec := fun V => body.spec (V.extend c)
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- Bind `bvXor a b`. -/
noncomputable def cxor {Γ : Ctxt catCryptDialect} {s : CryptoTy} {n : Nat}
    (a b : Ctxt.Var Γ (CryptoTy.sword n))
    (body : Compiled (CryptoTy.sword n :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.bvXor n, rfl, .cons a (.cons b .nil)⟩) body.com
  spec := fun V => body.spec (V.extend (BitVec.xor (a.lookup V) (b.lookup V)))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- Bind `mkPair x y`. -/
noncomputable def cmkPair {Γ : Ctxt catCryptDialect} {s : CryptoTy} (a b : CryptoTy)
    (x : Ctxt.Var Γ a) (y : Ctxt.Var Γ b)
    (body : Compiled (CryptoTy.pair a b :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.mkPair a b, rfl, .cons x (.cons y .nil)⟩) body.com
  spec := fun V => body.spec (V.extend ((x.lookup V, y.lookup V) : ⟦CryptoTy.pair a b⟧))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- Bind `inr v` into `.sum a b`. -/
noncomputable def cinr {Γ : Ctxt catCryptDialect} {s : CryptoTy} (a b : CryptoTy)
    (v : Ctxt.Var Γ b) (body : Compiled (CryptoTy.sum a b :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.inr a b, rfl, .cons v .nil⟩) body.com
  spec := fun V => body.spec (V.extend (Sum.inr (v.lookup V) : ⟦CryptoTy.sum a b⟧))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- Bind `inl v` into `.sum a b`. -/
noncomputable def cinl {Γ : Ctxt catCryptDialect} {s : CryptoTy} (a b : CryptoTy)
    (v : Ctxt.Var Γ a) (body : Compiled (CryptoTy.sum a b :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.inl a b, rfl, .cons v .nil⟩) body.com
  spec := fun V => body.spec (V.extend (Sum.inl (v.lookup V) : ⟦CryptoTy.sum a b⟧))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- Sample a `Bool` and continue with it bound at `.here`. -/
noncomputable def csampleBit {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (body : Compiled (CryptoTy.bit :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.sampleBit, rfl, .nil⟩) body.com
  spec := fun V => SPComp.bind (SPComp.sample Bool) (fun x => body.spec (V.extend x))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP]
    exact congrArg (SPComp.bind (SPComp.sample Bool))
      (funext fun x => body.correct (V.extend x))

/-- Bind the `Bool` `xor a b`. -/
noncomputable def cxorBit {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (a b : Ctxt.Var Γ CryptoTy.bit) (body : Compiled (CryptoTy.bit :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.xor, rfl, .cons a (.cons b .nil)⟩) body.com
  spec := fun V => body.spec (V.extend (Bool.xor (a.lookup V) (b.lookup V)))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

/-- Bind `bvAnd a b`. -/
noncomputable def cbvAnd {Γ : Ctxt catCryptDialect} {s : CryptoTy} {n : Nat}
    (a b : Ctxt.Var Γ (CryptoTy.sword n))
    (body : Compiled (CryptoTy.sword n :: Γ) s) : Compiled Γ s where
  com := Com.var (e := ⟨CatCryptOp.bvAnd n, rfl, .cons a (.cons b .nil)⟩) body.com
  spec := fun V => body.spec (V.extend (BitVec.and (a.lookup V) (b.lookup V)))
  correct := fun V => by
    simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP, SPComp.pure_bind]
    exact body.correct _

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRelCompile
