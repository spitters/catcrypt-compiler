/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TracefulSpec
public import CatCrypt.Crypto.Symbolic.SigningDiscipline
public import CatCrypt.Crypto.Symbolic.TimedLabel

/-!
# Symbolic Automation Tactics

Macros for repetitive symbolic proof patterns used across TLS, EDHOC, MLS,
and Signal protocol verifications.

## Main definitions

* `symbolic_publishable` — close `bytesPublishable` goals from `sendMsg` steps
* `symbolic_timed_publishable` — close `bytesTimedPublishable` goals for public values
* `symbolic_coherence` — close structural equalities between `Traceful`-monad
  symbolic-protocol terms (the structural counterpart of `pkg_coherence` for the
  symbolic side; mirrors monadic-coherence laws via `funext` + monad-law `simp`)

## Usage

These macros replace recurring multi-line `simp` patterns in protocol
verification files.
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Tactic

/-- Close `bytesPublishable` goals where the message consists of public values
(DH public keys, signatures, MACs, literals, hashes). Replaces the pattern:
```
simp [bytesPublishable, labelOf, Label.isCorrupt]
```
used in `traceInvariant_sendMsg` steps of protocol verification. -/
macro "symbolic_publishable" : tactic =>
  `(tactic| simp only [bytesPublishable, labelOf, Label.isCorrupt,
    and_self, true_and, and_true])

/-- Close `bytesTimedPublishable` goals for messages consisting of public values.
Used in `hNetworkTimed` discharge for honest traces. -/
macro "symbolic_timed_publishable" : tactic =>
  `(tactic| simp only [bytesTimedPublishable, timedLabelOf, TimedLabel.isCorrupt,
    and_self, true_and, and_true])

/-- Close structural equalities between `Traceful`-monad symbolic protocol
terms. The symbolic counterpart of `pkg_coherence`: it discharges goals
arising from monad-law / handler simp on `Traceful` programs built from the
trace-event combinators (`sendMsg`, `mkRand`, `setStateT`, `getStateT`,
`triggerEvent`, `corruptPrincipal`, `recvMsg`).

Strategy:
1. Try `rfl` (definitional equality through monad reduction).
2. `funext _; rfl` — equality after unfolding the trace argument.
3. `simp only [...]` with the trace-combinator simp set — closes equalities
   that need monadic reduction. -/
macro "symbolic_coherence" : tactic =>
  `(tactic|
    first
    | rfl
    | (funext _; rfl)
    | (simp only [bind, pure, getTrace, sendMsg, mkRand, setStateT,
                  getStateT, triggerEvent, corruptPrincipal, recvMsg])
    | (funext _
       simp only [bind, pure, getTrace, sendMsg, mkRand, setStateT,
                  getStateT, triggerEvent, corruptPrincipal, recvMsg]))

end CatCrypt.Crypto.Symbolic.Tactic

/-! ## Smoke tests for `symbolic_coherence`

The structural counterpart of `pkg_coherence`: closes equalities between
`Traceful`-monad symbolic-protocol terms by combining `funext` with the
trace-combinator simp set. -/

section SymbolicCoherenceSmokeTest

open CatCrypt.Crypto.Symbolic
open CatCrypt.Crypto.Symbolic.Tactic

/-- Pure `Traceful` is the identity. -/
example {α : Type} (a : α) :
    (pure a : Traceful α) = fun tr => (a, tr) := by
  symbolic_coherence

/-- Right-identity monad law on `Traceful`. -/
example {α : Type} (m : Traceful α) :
    (do let a ← m; pure a) = m := by
  symbolic_coherence

end SymbolicCoherenceSmokeTest
