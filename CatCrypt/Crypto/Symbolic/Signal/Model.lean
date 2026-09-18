/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Signal.Events

/-!
# Signal X3DH Protocol Model

One attacker-free X3DH run as a single `Traceful` program.

## Main definitions

* `honestX3DH` — Alice's steps of an X3DH exchange, followed by an `X3DHResp`
  event recorded in Bob's name

## Scope

- The model has no responder role. Bob generates no key, receives no message
  and computes nothing; `honestX3DH` records his `X3DHResp` event itself, with
  the root key that Alice computed.
- Bob's prekey bundle (`ikB`, `spkB`, `opkB`) is a parameter. The signature on
  the signed prekey is not modelled, and nothing constrains who chose the
  bundle, so the model says nothing about an attacker-supplied bundle.
- The initial ciphertext of X3DH is not sent. Under `labelOf` a ciphertext of
  a secret plaintext is not publishable, so a trace that sends one does not
  satisfy the invariant.
- The ratchet step `ratchetStep` of `Events.lean` is not used by this program.

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

/-- One attacker-free X3DH run.

Alice generates ephemeral and identity keys, computes the 4 DH operations,
derives the root key, records her `X3DHInit` event and sends the initiator
message. The program then records the `X3DHResp` event in Bob's name with the
same root key; Bob has no program of his own.

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
