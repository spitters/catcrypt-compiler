/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Resolved
import CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP

/-!
# ComITreeNBridge: `Com catCryptDialect` ↔ ITreeN bridge

Embeds a dialect program into `ITreeN n E` via the generic `embedSPComp`
(`comToITreeN`), so the ITreeN-level security results — `sdistITreeN = 0`
(`com_equiv_sdistITreeN_zero`) and security transfer (`com_security_transfer`,
`com_security_transfer_symm`) — follow from a denotation equivalence
`∀ V, Com.denoteSP p V = Com.denoteSP q V`. The proofs reduce through the generic
`flattenAll_embedSPComp`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ComITreeNBridge

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open scoped ENNReal

set_option autoImplicit true -- dialect IR: many context/type variables

/-! ## Section 1: Embedding `Com catCryptDialect` into ITreeN -/

/-- Embed a dialect program into `ITreeN n E` via `embedSPComp`, lifting its
    `SPComp` denotation `Com.denoteSP` to the ITreeN level (where UC security is
    conducted). The dialect-native analogue of `SSABridge.cProgToITreeN`. -/
noncomputable def comToITreeN {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (n : Nat) (E : EventSig) (c : Com catCryptDialect Γ t) (V : Ctxt.Valuation Γ) :
    ITreeN n E ⟦t⟧ :=
  embedSPComp n (Com.denoteSP c V)

/-- `flattenAll` of an embedded dialect program recovers its `SPComp`
    denotation. -/
theorem flattenAll_comToITreeN {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (c : Com catCryptDialect Γ t) (V : Ctxt.Valuation Γ) :
    ITreeN.flattenAll handler n (comToITreeN n E c V) = Com.denoteSP c V :=
  flattenAll_embedSPComp handler n (Com.denoteSP c V)

/-! ## Section 2: Compiler correctness from a `denoteSP` equivalence -/

/-- A dialect-level denotation equivalence (`∀ V, denoteSP p V = denoteSP q V`)
    gives `CompilerCorrectResolved` at the ITreeN level — the dialect analogue of
    `SSABridge.cprog_equiv_resolved`. -/
theorem com_denoteSP_resolved {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {p q : Com catCryptDialect Γ t}
    (h : ∀ V, Com.denoteSP p V = Com.denoteSP q V) (V : Ctxt.Valuation Γ) :
    CompilerCorrectResolved handler
      (fun (_ : Unit) => comToITreeN n E p V)
      (fun (_ : Unit) => comToITreeN n E q V) := by
  intro _
  simp only [comToITreeN]
  rw [flattenAll_embedSPComp, flattenAll_embedSPComp, h V]

/-- sdist between `denoteSP`-equivalent dialect programs is zero at the ITreeN
    level — the dialect analogue of `cprog_equiv_sdistITreeN_zero`. -/
theorem com_equiv_sdistITreeN_zero {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {p q : Com catCryptDialect Γ t}
    (h : ∀ V, Com.denoteSP p V = Com.denoteSP q V) (V : Ctxt.Valuation Γ) :
    sdistITreeN n E handler
      (fun (_ : Unit) => comToITreeN n E p V)
      (fun (_ : Unit) => comToITreeN n E q V) = 0 :=
  resolved_sdist_zero handler (com_denoteSP_resolved handler h V)

/-! ## Section 3: Security transfer -/

/-- Security transfer: if `p`'s ITreeN embedding is ε-close to `ideal` and
    `p`/`q` are `denoteSP`-equivalent, then `q`'s embedding is ε-close too — the
    dialect analogue of `ssa_security_transfer`. -/
theorem com_security_transfer {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {p q : Com catCryptDialect Γ t}
    (h : ∀ V, Com.denoteSP p V = Com.denoteSP q V)
    (V : Ctxt.Valuation Γ) {ideal : Unit → ITreeN n E ⟦t⟧} {ε : ℝ≥0∞}
    (hsec : sdistITreeN n E handler
      (fun _ => comToITreeN n E p V) ideal ≤ ε) :
    sdistITreeN n E handler
      (fun _ => comToITreeN n E q V) ideal ≤ ε := by
  calc sdistITreeN n E handler (fun _ => comToITreeN n E q V) ideal
      ≤ sdistITreeN n E handler (fun _ => comToITreeN n E q V)
          (fun _ => comToITreeN n E p V)
        + sdistITreeN n E handler (fun _ => comToITreeN n E p V) ideal :=
          sdistITreeN_triangle ..
    _ = 0 + sdistITreeN n E handler (fun _ => comToITreeN n E p V) ideal := by
        rw [sdistITreeN_sym, com_equiv_sdistITreeN_zero handler h V]
    _ ≤ ε := by simp; exact hsec

/-- Symmetric transfer: if `q`'s embedding has security, `p`'s inherits it. -/
theorem com_security_transfer_symm {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {p q : Com catCryptDialect Γ t}
    (h : ∀ V, Com.denoteSP p V = Com.denoteSP q V)
    (V : Ctxt.Valuation Γ) {ideal : Unit → ITreeN n E ⟦t⟧} {ε : ℝ≥0∞}
    (hsec : sdistITreeN n E handler
      (fun _ => comToITreeN n E q V) ideal ≤ ε) :
    sdistITreeN n E handler
      (fun _ => comToITreeN n E p V) ideal ≤ ε :=
  com_security_transfer handler (fun V => (h V).symm) V hsec

end CatCrypt.Crypto.SecureCompilation.Dialects.ComITreeNBridge
