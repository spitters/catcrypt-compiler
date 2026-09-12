/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Attacker

/-!
# Security Property Types

Generic definitions for the two main classes of symbolic security properties:
secrecy and authentication (correspondence).

## Main definitions

* `Secrecy` — a secret value is not known to the attacker unless some owner
  is corrupted
* `Authentication` — an event triggered by a responder was preceded by a
  corresponding event by the initiator (or someone is corrupted)

## Design

These are parameterized over any `ProtocolInvariants` instance. The TLS-specific
instantiations provide concrete event tags and content.

The `Secrecy` property uses `attacker_only_knows_publishable` as its main
proof principle: if the attacker knows a secret, then the secret is publishable,
which by the label discipline means some owner must be corrupted.

The `Authentication` property uses trace event correspondence: if a responder
event exists at position `i`, then either an initiator event exists at some
`j < i`, or some principal is corrupted.

## References

* DY*-extrinsic: `DY.Lib.Crypto.Secrecy`, `DY.Lib.Event.Correspondence`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-! ## Secrecy -/

/-- A value `secret` with owners `owners` is secret in trace `tr`:
    if the attacker can derive it, then some owner must be corrupted.

This is the standard DY* secrecy property. The proof pattern is:
1. Assume `AttackerKnows tr secret`
2. Apply `attacker_only_knows_publishable` to get `bytesPublishable tr secret`
3. Unfold `hasLabel` to show the label must flow to `top`
4. The label is `meet` of owners' labels, so one must be corrupted -/
def Secrecy [ProtocolInvariants] (tr : Trace) (secret : Bytes) (owners : List String) : Prop :=
  traceInvariant tr →
  AttackerKnows tr secret →
  ∃ p, p ∈ owners ∧ tr.isCorruptAt p (tr.length - 1)

/-! ## Authentication (Correspondence) -/

/-- Authentication via event correspondence:
    if `responder` triggered event `(respTag, respContent)` at position `i`,
    then either:
    - `initiator` triggered `(initTag, initContent)` at some earlier position, OR
    - `responder` or `initiator` is corrupted at position `i`.

This models injective agreement when `respContent` contains a nonce. -/
def Authentication [ProtocolInvariants] (tr : Trace) (i : Nat)
    (responder initiator : String) (respTag initTag : String)
    (respContent initContent : Bytes) : Prop :=
  traceInvariant tr →
  tr.eventTriggeredAt i responder respTag respContent →
  (∃ j, j < i ∧ tr.eventTriggeredAt j initiator initTag initContent) ∨
  tr.isCorruptAt responder i ∨
  tr.isCorruptAt initiator i

/-! ## Derived Properties -/

/-- Forward secrecy: even if principal `p` is corrupted AFTER time `t`,
    the secret at time `t` remains protected. -/
def ForwardSecrecy [ProtocolInvariants] (tr : Trace) (secret : Bytes)
    (sessionTime : Nat) (owners : List String) : Prop :=
  traceInvariant tr →
  AttackerKnows tr secret →
  -- Either some owner was corrupted BEFORE OR AT the session time
  ∃ p, p ∈ owners ∧ tr.isCorruptAt p sessionTime

/-- Post-quantum secrecy: the secret is protected even against a quantum
    attacker, assuming the quantum-resistant primitive (KEM) is secure.
    The owners list includes both classical and PQ key holders. -/
def PQSecrecy [ProtocolInvariants] (tr : Trace) (secret : Bytes)
    (classicalOwners pqOwners : List String) : Prop :=
  traceInvariant tr →
  AttackerKnows tr secret →
  -- Either a classical owner AND a PQ owner are both corrupted,
  -- or a single owner holding both roles is corrupted
  (∃ p, p ∈ classicalOwners ∧ tr.isCorruptAt p (tr.length - 1)) ∧
  (∃ q, q ∈ pqOwners ∧ tr.isCorruptAt q (tr.length - 1))

end CatCrypt.Crypto.Symbolic
