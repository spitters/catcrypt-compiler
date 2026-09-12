/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.LowCTLeakTraceDef


@[expose] public section
set_option autoImplicit false

/-!
# Leakage observables for the adopted external leaves

`CatCrypt/Crypto/Vale/` adopts externally verified primitives as opaque
`extCall` leaves.  A leaf's body is not Lean code, so its side-channel
behaviour cannot be computed here; it is named by a leakage function and
constrained by an axiom citing the upstream proof.

## The observable

The leakage of one leaf call is a `LeakTrace` — the observable-event
sequence of `LowCTLeakTraceDef`, the same alphabet the enclosing program's
`LowCT.leakTrace` / `dynLeakTrace` are built from.  A leaf's leakage
function maps the leaf's arguments to the trace its execution emits, so
control-flow decisions and memory accesses that depend on an argument show
up as a difference between the traces at two argument values.

## The constant-time property

A leaf is constant-time in an argument when varying that argument alone
leaves the trace unchanged: `SecretIndependent (leak p)` for each fixed
public argument bundle `p`.  This is Goguen–Meseguer noninterference at the
leaf boundary, the same shape as `LowCTVartimeLeak.dynLeakTrace_noninterference`
carries for a `LowCT` program.

The predicate separates constant-time from variable-time leaves:
`secretIndependent_const` holds of a trace that ignores its argument, and
`not_secretIndependent_argBitLeak` refutes it for a trace that records one
bit of its argument.

## Scope

The leaf leakage functions are opaque.  What a `SecretIndependent` axiom
buys is the noninterference side condition that `LowCTCTAnalysis.cmdCT`
delegates to its `LeafCTTable` entry, stated so that a leaf whose trace does
vary with a secret argument contradicts it.  It is not a proof of the
upstream implementation; the citation for each is in `ValeCoqAxioms.lean`.

## Main results

* `LeafLeak` — the leakage trace of one external leaf call.
* `SecretIndependent` — a leaf leakage function does not vary with its
  argument.
* `secretIndependent_const` — an argument-ignoring trace is
  secret-independent.
* `not_secretIndependent_argBitLeak` — a trace recording one bit of its
  argument is not secret-independent.
-/

namespace CatCrypt.Crypto.Vale.LeafLeakage

open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-- The leakage of one external-leaf call: the sequence of observable
    events its execution emits, in the `LeakTrace` alphabet the enclosing
    `LowCT` program's leakage trace uses. -/
abbrev LeafLeak := LeakTrace

/-- `SecretIndependent leak`: the leakage trace `leak s` is the same at every
    `s`.  Applied to a leaf's leakage function partially applied to its public
    arguments, it says the leaf's observable behaviour is a function of those
    public arguments alone. -/
def SecretIndependent {S : Type} (leak : S → LeafLeak) : Prop :=
  ∀ s₁ s₂ : S, leak s₁ = leak s₂

/-- A leakage trace that ignores its argument is secret-independent. -/
theorem secretIndependent_const {S : Type} (t : LeafLeak) :
    SecretIndependent (fun _ : S => t) := fun _ _ => rfl

/-- A leakage trace recording one bit of its argument: the branch event of
    `LowCTVartimeLeak`, taken on the argument. -/
def argBitLeak (b : Bool) : LeafLeak :=
  [LeakEvent.pureOp (if b then "branch:1" else "branch:0")]

/-- `argBitLeak` is not secret-independent: its traces at `true` and at
    `false` differ.  A leaf whose control flow follows a secret bit has this
    leakage shape, so `SecretIndependent` separates constant-time leaves from
    variable-time ones. -/
theorem not_secretIndependent_argBitLeak : ¬ SecretIndependent argBitLeak := by
  intro h
  have hbit := h true false
  simp [argBitLeak] at hbit

end CatCrypt.Crypto.Vale.LeafLeakage
