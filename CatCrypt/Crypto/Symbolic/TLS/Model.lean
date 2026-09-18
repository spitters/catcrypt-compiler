/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TLS.Events

/-!
# TLS 1.3 Handshake Model

A simplified TLS 1.3 handshake as `Traceful` programs.

## Main definitions

* `clientHandshake` — client role of the TLS 1.3 handshake
* `serverHandshake` — server role of the TLS 1.3 handshake
* `honestSession` — both roles inlined into one attacker-free run

## Scope

* Only `honestSession` appears in a theorem: `honestSession_invariant` shows
  that its one output trace satisfies `tlsInvariants`. `clientHandshake` and
  `serverHandshake` appear in no theorem and are not verified.
* `clientHandshake` binds the result of `Bytes.signVerify` to `_verified` and
  does not branch on it; it records `ClientFinished` whatever the signature.
* `serverHandshake` sets the peer name to the literal `"client"` instead of
  parsing it from the ClientHello.
* The handshake flight is sent unencrypted. Under `labelOf` a ciphertext of a
  secret plaintext is not publishable, so a trace that sends one does not
  satisfy the invariant.
* `honestResumptionSession` and `honestSessionWithTicket` are definitions
  only; no theorem in this directory mentions them.

## Protocol Flow (1-RTT, no PSK)

```
Client                                           Server
──────                                           ──────
(1) x ←$ DH; gx := dhPub(x)
    → ClientHello(gx)

                                  (2) y ←$ DH; gy := dhPub(y)
                                      dhSS := dh(y, gx)
                                      appKey := keySchedule(dhSS)
                                      sig := sign(sk_s, ..., transcript)
                                      ← ServerHello(gy, sig)
                                      trigger ServerFinished(server, client, appKey)

(3) dhSS := dh(x, gy)
    appKey := keySchedule(dhSS)
    verify sig with vk_s
    trigger ClientFinished(client, server, appKey)
```

## Design Notes

- We model a simplified handshake without certificate chains, ALPN, etc.
- The server's long-term key is a signature key (EdDSA/ECDSA).
- We omit HelloRetryRequest and session resumption.
- The `recvMsg` function models the attacker delivering messages.
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-! ## Client Role -/

/-- Client's handshake computation.

Generates ephemeral DH key, sends ClientHello, receives ServerHello,
derives keys, computes `Bytes.signVerify` on the server signature without
using its result, and triggers the ClientFinished event. The program appears
in no theorem.

Parameters:
- `client`: client's identity (e.g., hostname)
- `server`: server's identity
- `serverVK`: server's verification key (known via certificate/trust store)
- `serverHelloMsg`: the message delivered by the network (attacker)

Returns the application traffic key. -/
def clientHandshake (client server : String) (serverVK : Bytes)
    (serverHelloMsg : Bytes) : Traceful Bytes := do
  -- Generate ephemeral DH key pair
  let x ← mkRand .dhKey (principalLabel client) 32
  let gx := Bytes.dhPub x
  -- Trigger ClientHello event
  triggerEvent client clientHelloTag (mkClientHelloContent client server gx)
  -- Send ClientHello
  sendMsg (mkClientHelloContent client server gx)
  -- Parse server response (in symbolic model, just destructure)
  let serverHello := recvMsg serverHelloMsg
  -- Extract gy and signature from serverHelloMsg
  -- In symbolic model: serverHelloMsg = concat(gy, sig)
  let gy := serverHelloMsg.splitL.getD Bytes.empty
  let serverSig := serverHelloMsg.splitR.getD Bytes.empty
  -- Compute DH shared secret
  let dhSS := Bytes.dh x gy
  -- Derive keys
  let appKey := keySchedule dhSS
  -- Verify server signature
  -- In symbolic model: signVerify checks structural equality
  let _verified := Bytes.signVerify serverVK serverSig
  -- Trigger ClientFinished event
  triggerEvent client clientFinishedTag (mkFinishedContent client server appKey)
  return appKey

/-! ## Server Role -/

/-- Server's handshake computation.

Receives ClientHello, generates ephemeral DH key, derives keys,
signs the transcript, and triggers ServerFinished event. The peer name in the
event is the literal `"client"`. The program appears in no theorem.

Parameters:
- `server`: server's identity
- `sigKey`: server's signing secret key
- `clientHelloMsg`: the ClientHello message from the network

Returns the application traffic key. -/
def serverHandshake (server : String) (sigKey : Bytes)
    (clientHelloMsg : Bytes) : Traceful Bytes := do
  -- Parse ClientHello (extract client identity and gx)
  let clientId := clientHelloMsg.splitL.getD Bytes.empty
  let gx := clientHelloMsg.splitR.bind Bytes.splitR |>.getD Bytes.empty
  -- Extract client name (in model, it's a literal)
  let client := "client" -- simplified: in real model, extracted from clientId
  -- Generate ephemeral DH key pair
  let y ← mkRand .dhKey (principalLabel server) 32
  let gy := Bytes.dhPub y
  -- Compute DH shared secret (commutativity: dh(y, gx) ≡ dh(x, gy))
  let dhSS := Bytes.dh y gx
  -- Derive keys
  let appKey := keySchedule dhSS
  -- Sign transcript with server's long-term key
  let nonce ← mkRand .nonce (principalLabel server) 32
  let transcript := Bytes.hash (Bytes.concat clientHelloMsg gy)
  let sig := Bytes.sign sigKey nonce transcript
  -- Trigger ServerFinished event
  triggerEvent server serverFinishedTag (mkFinishedContent server client appKey)
  -- Send ServerHello
  sendMsg (Bytes.concat gy sig)
  return appKey

/-! ## Protocol Session -/

/-- A complete TLS session between honest client and server.

The steps of both roles are inlined into one program with no attacker
interference: the client receives the server's actual message, and the client
event reuses the server-side key. The program does not call `clientHandshake`
or `serverHandshake`. -/
def honestSession (client server : String) (serverSigKey : Bytes) :
    Traceful (Bytes × Bytes) := do
  -- Server setup: generate long-term signing key
  let serverVK := Bytes.vk serverSigKey
  -- Client generates and sends ClientHello
  let x ← mkRand .dhKey (principalLabel client) 32
  let gx := Bytes.dhPub x
  triggerEvent client clientHelloTag (mkClientHelloContent client server gx)
  sendMsg (mkClientHelloContent client server gx)
  -- Server processes ClientHello and responds
  let y ← mkRand .dhKey (principalLabel server) 32
  let gy := Bytes.dhPub y
  let dhSS_server := Bytes.dh y gx
  let appKey_server := keySchedule dhSS_server
  let nonce ← mkRand .nonce (principalLabel server) 32
  let clientHelloContent := mkClientHelloContent client server gx
  let transcript := Bytes.hash (Bytes.concat clientHelloContent gy)
  let sig := Bytes.sign serverSigKey nonce transcript
  triggerEvent server serverFinishedTag (mkFinishedContent server client appKey_server)
  sendMsg (Bytes.concat gy sig)
  -- Client processes ServerHello
  -- Note: In an honest session, both sides derive the same key via DH commutativity
  -- (dh(x, gy) ≡ dh(y, gx)). We use the shared `appKey_server` for both events
  -- to enable trace invariant verification in the symbolic model, where
  -- Bytes.dh is a free constructor (not definitionally commutative).
  triggerEvent client clientFinishedTag (mkFinishedContent client server appKey_server)
  return (appKey_server, appKey_server)

/-! ## PSK Resumption Session

TLS 1.3 PSK-DHE resumption: the client presents a PSK derived from a
previous session, and both sides also contribute fresh ephemeral DH values.
This provides forward secrecy for the resumed session.

Protocol flow:
```
Client                                     Server
──────                                     ──────
(1) x ←$ DH; gx := dhPub(x)
    binder := pskBinder(psk, gx)
    → PSKClientHello(gx, binder)

                            (2) y ←$ DH; gy := dhPub(y)
                                dhSS := dh(y, gx)
                                appKey := pskKeySchedule(psk, dhSS)
                                trigger PSKServerFinished
                                ← PSKServerHello(gy)

(3) dhSS := dh(x, gy)
    appKey := pskKeySchedule(psk, dhSS)
    trigger PSKClientFinished
```
-/

/-- PSK-DHE resumption session between honest client and server.

    Requires a pre-shared key `psk` from a previous successful session
    (typically `resumptionSecret appKey` from a prior `honestSession`).

    Returns the new application traffic key (both sides agree). -/
def honestResumptionSession (client server : String) (psk : Bytes) :
    Traceful (Bytes × Bytes) := do
  -- Client generates ephemeral DH key pair
  let x ← mkRand .dhKey (principalLabel client) 32
  let gx := Bytes.dhPub x
  -- Client computes binder and sends PSKClientHello
  let binder := pskBinder psk gx
  triggerEvent client pskClientHelloTag
    (mkClientHelloContent client server gx)
  sendMsg (.concat (mkClientHelloContent client server gx) binder)
  -- Server generates ephemeral DH key pair
  let y ← mkRand .dhKey (principalLabel server) 32
  let gy := Bytes.dhPub y
  -- Server derives shared secret and application key
  let dhSS_server := Bytes.dh y gx
  let appKey := pskKeySchedule psk dhSS_server
  -- Server triggers PSKServerFinished
  triggerEvent server pskServerFinishedTag
    (mkPSKFinishedContent server client appKey)
  sendMsg gy
  -- Client processes response (honest session: uses same key)
  triggerEvent client pskClientFinishedTag
    (mkPSKFinishedContent client server appKey)
  return (appKey, appKey)

/-- Full session with ticket issuance: runs `honestSession` then derives
    a resumption secret for future PSK resumption. -/
def honestSessionWithTicket (client server : String) (serverSigKey : Bytes) :
    Traceful (Bytes × Bytes × Bytes) := do
  let (appKey_c, appKey_s) ← honestSession client server serverSigKey
  let resSecret := resumptionSecret appKey_s
  -- Server issues NewSessionTicket
  triggerEvent server newSessionTicketTag
    (mkTicketContent server client resSecret)
  return (appKey_c, appKey_s, resSecret)

end CatCrypt.Crypto.Symbolic.TLS
