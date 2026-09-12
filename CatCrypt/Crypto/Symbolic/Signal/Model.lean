/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Signal.Events

/-!
# Signal X3DH Protocol Model

The X3DH key agreement as `Traceful` programs. Models the initiator (Alice)
and responder (Bob) roles for an honest session.

## Main definitions

* `honestX3DH` — complete honest X3DH session (both roles)

## Design Notes

- We model one X3DH exchange between Alice and Bob
- Bob's identity key (ikB), signed prekey (spkB), and one-time prekey (opkB)
  are pre-existing DH keys
- Alice generates an ephemeral key (ek) and identity key (ikA)
- Both sides compute the same root key via `signalKeySchedule`
- We use server-computed key for both events (same trick as TLS Model.lean)
  because `Bytes.dh` is a free constructor (not commutative)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

/-! ## Honest X3DH Session -/

/-- A complete honest X3DH session.

Alice generates ephemeral and identity keys, computes the 4 DH operations,
derives the root key, triggers events for both sides, and sends the
initiator message.

Parameters:
- `alice`, `bob`: participant identities
- `ikB`: Bob's identity key (pre-existing)
- `spkB`: Bob's signed prekey (pre-existing)
- `opkB`: Bob's one-time prekey (pre-existing)

Returns the root key (same for both parties). -/
def honestX3DH (alice bob : String)
    (ikB spkB opkB : Bytes) : Traceful Bytes := do
  -- Alice generates ephemeral key
  let ek ← mkRand .dhKey (principalLabel alice) 32
  -- Alice generates identity key
  let ikA ← mkRand .dhKey (principalLabel alice) 32
  -- Compute 4 DH shared secrets (Alice's side)
  -- dh1 = dh(ikA, spkB): identity × signed prekey
  let dh1 := Bytes.dh ikA (Bytes.dhPub spkB)
  -- dh2 = dh(ek, ikB): ephemeral × identity
  let dh2 := Bytes.dh ek (Bytes.dhPub ikB)
  -- dh3 = dh(ek, spkB): ephemeral × signed prekey
  let dh3 := Bytes.dh ek (Bytes.dhPub spkB)
  -- dh4 = dh(ek, opkB): ephemeral × one-time prekey
  let dh4 := Bytes.dh ek (Bytes.dhPub opkB)
  -- Derive root key
  let rootKey := signalKeySchedule dh1 dh2 dh3 dh4
  -- Alice triggers X3DH initiator event
  triggerEvent alice x3dhInitTag (mkX3DHContent alice bob rootKey)
  -- Alice sends initiator message (public keys only)
  sendMsg (.concat (Bytes.dhPub ek) (Bytes.dhPub ikA))
  -- Bob triggers X3DH responder event (using same root key)
  triggerEvent bob x3dhRespTag (mkX3DHContent bob alice rootKey)
  return rootKey

end CatCrypt.Crypto.Symbolic.Signal
