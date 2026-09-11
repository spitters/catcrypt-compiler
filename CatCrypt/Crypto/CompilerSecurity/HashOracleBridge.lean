/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.CrossEventDemo
public import CatCrypt.Crypto.CompilerSecurity.TemplateCompilation

/-!
# Hash Oracle Cross-Event-Sig Compilation

Demonstrates cross-event-signature compilation for a protocol that uses
hash oracle calls as visible events. The source protocol has
`CryptoSig +ₑ HashOracleSig`, and the target has only `CryptoSig`
(hash oracle calls inlined).

This models the ROM (Random Oracle Model) to standard model compilation:
the source program makes explicit oracle queries; the compilation inlines
the hash function, removing the oracle interface.

## Pipeline

```
Source: CryptoSig +ₑ HashSig  --[inline hash]--> Target: CryptoSig only
  |                                                  |
  v                                                  v
flattenAll(sumHandler)         =           flattenAll(cryptoHandler)
```

## Main theorems

* `hash_cross_compiler_correct` -- CompilerCorrectCrossEvSig
* `hash_cross_sdist_zero` -- sdist = 0
* `hash_cross_security_transfer` -- UC security transfers
* `multi_hash_cross` -- multiple hash calls compiled away

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.HashOracleBridge

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open scoped ENNReal

/-! ## Event Signatures -/

/-- Abstract crypto events for the protocol. -/
inductive CryptoEvent where
  | setup
  | challenge
  | verify

/-- Crypto event signature. -/
def CryptoSig : EventSig where
  Event := CryptoEvent
  Resp := fun _ => Unit

/-- Hash oracle events. -/
inductive HashEvent where
  | query

/-- Hash oracle event signature. -/
def HashOracleSig : EventSig where
  Event := HashEvent
  Resp := fun _ => Unit

/-! ## Protocol Dependencies -/

/-- Abstract protocol dependencies. -/
structure HashProtocolDeps (W : Type) where
  /-- Core computation after setup + hash + challenge + verify. -/
  core : SPComp W
  /-- Hash oracle body. -/
  hash_body : SPComp Unit

variable {W : Type}

/-! ## Source Protocol (with hash oracle events) -/

/-- Source: setup → hash_query → challenge → verify → core.
    Uses `CryptoSig +ₑ HashOracleSig`. -/
noncomputable def hash_source (deps : HashProtocolDeps W) :
    Unit → ITreeN 5 (CryptoSig +ₑ HashOracleSig) W :=
  fun () =>
    ITreeN.vis 4 (Sum.inl CryptoEvent.setup) fun () =>
    ITreeN.vis 3 (Sum.inr HashEvent.query) fun () =>
    ITreeN.vis 2 (Sum.inl CryptoEvent.challenge) fun () =>
    ITreeN.vis 1 (Sum.inl CryptoEvent.verify) fun () =>
    embedSPComp 1 deps.core

/-! ## Target Protocol (hash inlined) -/

/-- Target: setup → [inline hash] → challenge → verify → core.
    Uses only `CryptoSig`. -/
noncomputable def hash_target (deps : HashProtocolDeps W)
    (crypto_handler : forall e : CryptoSig.Event, SPComp (CryptoSig.Resp e))
    (hash_body : SPComp Unit) :
    Unit → ITreeN 5 CryptoSig W :=
  fun () =>
    ITreeN.vis 4 CryptoEvent.setup fun () =>
    ITreeN.bind' crypto_handler 4
      (embedSPComp 4 hash_body) fun () =>
    ITreeN.vis 3 CryptoEvent.challenge fun () =>
    ITreeN.vis 2 CryptoEvent.verify fun () =>
    embedSPComp 2 deps.core

/-! ## Compiler Correctness -/

/-- Cross-event-sig compiler correctness: source (with hash oracle events) and
    target (hash inlined) produce the same SPComp after resolution. -/
theorem hash_cross_compiler_correct (deps : HashProtocolDeps W)
    (crypto_handler : forall e : CryptoSig.Event, SPComp (CryptoSig.Resp e))
    (hash_handler : forall e : HashOracleSig.Event, SPComp (HashOracleSig.Resp e)) :
    CompilerCorrectCrossEvSig
      (sumHandler crypto_handler hash_handler)
      crypto_handler
      (hash_source deps)
      (hash_target deps crypto_handler (hash_handler HashEvent.query)) := by
  intro ()
  simp only [hash_source, hash_target]
  -- LHS: flattenAll (sumHandler ...) 5 (vis 4 (.inl setup) ...)
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 4
    (Sum.inl CryptoEvent.setup)]
  -- RHS: flattenAll crypto_handler 5 (vis 4 setup ...)
  rw [flattenAll_vis crypto_handler 4 CryptoEvent.setup]
  simp only [sumHandler]
  congr 1; funext ()
  -- LHS: flattenAll 4 (vis 3 (.inr query) ...)
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 3
    (Sum.inr HashEvent.query)]
  -- RHS: flattenAll 4 (bind' 4 (embedSPComp 4 hash_body) ...)
  rw [flattenAll_bind, flattenAll_embedSPComp]
  simp only [sumHandler]
  congr 1; funext ()
  -- LHS: flattenAll 3 (vis 2 (.inl challenge) ...)
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 2
    (Sum.inl CryptoEvent.challenge)]
  rw [flattenAll_vis crypto_handler 3 CryptoEvent.challenge]
  simp only [sumHandler]
  congr 1; funext ()
  -- LHS: flattenAll 2 (vis 1 (.inl verify) ...)
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 1
    (Sum.inl CryptoEvent.verify)]
  rw [flattenAll_vis crypto_handler 2 CryptoEvent.verify]
  simp only [sumHandler]
  congr 1; funext ()
  rw [flattenAll_embedSPComp, flattenAll_embedSPComp]

/-! ## sdist = 0 -/

/-- Zero sdist follows from cross-event-sig correctness. -/
theorem hash_cross_sdist_zero (deps : HashProtocolDeps W)
    (crypto_handler : forall e : CryptoSig.Event, SPComp (CryptoSig.Resp e))
    (hash_handler : forall e : HashOracleSig.Event, SPComp (HashOracleSig.Resp e)) :
    sdist
      (fun a => ITreeN.flattenAll (sumHandler crypto_handler hash_handler) 5
        (hash_source deps a))
      (fun a => ITreeN.flattenAll crypto_handler 5
        (hash_target deps crypto_handler (hash_handler HashEvent.query) a)) = 0 :=
  cross_evsig_sdist_zero_source _ _
    (hash_cross_compiler_correct deps crypto_handler hash_handler)

/-! ## Security Transfer -/

/-- Source security transfers to the target. -/
theorem hash_cross_security_transfer (deps : HashProtocolDeps W)
    (crypto_handler : forall e : CryptoSig.Event, SPComp (CryptoSig.Resp e))
    (hash_handler : forall e : HashOracleSig.Event, SPComp (HashOracleSig.Resp e))
    (ideal : Unit → ITreeN 5 CryptoSig W)
    (ε : ℝ≥0∞)
    (hsec : sdist
      (fun a => ITreeN.flattenAll (sumHandler crypto_handler hash_handler) 5
        (hash_source deps a))
      (fun a => ITreeN.flattenAll crypto_handler 5 (ideal a)) ≤ ε) :
    sdist
      (fun a => ITreeN.flattenAll crypto_handler 5
        (hash_target deps crypto_handler (hash_handler HashEvent.query) a))
      (fun a => ITreeN.flattenAll crypto_handler 5 (ideal a)) ≤ ε := by
  have heq := hash_cross_compiler_correct deps crypto_handler hash_handler
  have : (fun a => ITreeN.flattenAll crypto_handler 5
      (hash_target deps crypto_handler (hash_handler HashEvent.query) a)) =
    (fun a => ITreeN.flattenAll (sumHandler crypto_handler hash_handler) 5
      (hash_source deps a)) := funext (fun x => (heq x).symm)
  rw [this]; exact hsec

/-! ## Multiple Hash Calls -/

/-- Source with two hash oracle calls. -/
noncomputable def multi_hash_source (deps : HashProtocolDeps W) :
    Unit → ITreeN 6 (CryptoSig +ₑ HashOracleSig) W :=
  fun () =>
    ITreeN.vis 5 (Sum.inl CryptoEvent.setup) fun () =>
    ITreeN.vis 4 (Sum.inr HashEvent.query) fun () =>
    ITreeN.vis 3 (Sum.inr HashEvent.query) fun () =>
    ITreeN.vis 2 (Sum.inl CryptoEvent.challenge) fun () =>
    ITreeN.vis 1 (Sum.inl CryptoEvent.verify) fun () =>
    embedSPComp 1 deps.core

/-- Target with both hash calls inlined.
    `bind'` does not consume a level, so both binds are at level 5. -/
noncomputable def multi_hash_target (deps : HashProtocolDeps W)
    (crypto_handler : forall e : CryptoSig.Event, SPComp (CryptoSig.Resp e))
    (hash_body : SPComp Unit) :
    Unit → ITreeN 6 CryptoSig W :=
  fun () =>
    ITreeN.vis 5 CryptoEvent.setup fun () =>
    ITreeN.bind' crypto_handler 5
      (embedSPComp 5 hash_body) fun () =>
    ITreeN.bind' crypto_handler 5
      (embedSPComp 5 hash_body) fun () =>
    ITreeN.vis 4 CryptoEvent.challenge fun () =>
    ITreeN.vis 3 CryptoEvent.verify fun () =>
    embedSPComp 3 deps.core

/-- Cross-event-sig correctness for two hash calls. -/
theorem multi_hash_cross_correct (deps : HashProtocolDeps W)
    (crypto_handler : forall e : CryptoSig.Event, SPComp (CryptoSig.Resp e))
    (hash_handler : forall e : HashOracleSig.Event, SPComp (HashOracleSig.Resp e)) :
    CompilerCorrectCrossEvSig
      (sumHandler crypto_handler hash_handler)
      crypto_handler
      (multi_hash_source deps)
      (multi_hash_target deps crypto_handler (hash_handler HashEvent.query)) := by
  intro ()
  simp only [multi_hash_source, multi_hash_target]
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 5
    (Sum.inl CryptoEvent.setup)]
  rw [flattenAll_vis crypto_handler 5 CryptoEvent.setup]
  simp only [sumHandler]
  congr 1; funext ()
  -- First hash call
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 4
    (Sum.inr HashEvent.query)]
  rw [flattenAll_bind, flattenAll_embedSPComp]
  simp only [sumHandler]
  congr 1; funext ()
  -- Second hash call (level 3 on LHS, bind' at level 5 on RHS)
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 3
    (Sum.inr HashEvent.query)]
  rw [flattenAll_bind, flattenAll_embedSPComp]
  simp only [sumHandler]
  congr 1; funext ()
  -- challenge (level 2 on LHS, level 4 on RHS)
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 2
    (Sum.inl CryptoEvent.challenge)]
  rw [flattenAll_vis crypto_handler 4 CryptoEvent.challenge]
  simp only [sumHandler]
  congr 1; funext ()
  -- verify (level 1 on LHS, level 3 on RHS)
  rw [flattenAll_vis (sumHandler crypto_handler hash_handler) 1
    (Sum.inl CryptoEvent.verify)]
  rw [flattenAll_vis crypto_handler 3 CryptoEvent.verify]
  simp only [sumHandler]
  congr 1; funext ()
  rw [flattenAll_embedSPComp, flattenAll_embedSPComp]

end CatCrypt.Crypto.SecureCompilation.HashOracleBridge
