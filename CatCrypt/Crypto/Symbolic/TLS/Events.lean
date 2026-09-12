/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Properties

/-!
# TLS 1.3 Events

TLS-specific event tags and content constructors for correspondence properties.

## Main definitions

* Event tag constants for TLS 1.3 handshake events
* Content serialization helpers for event payloads

## Design

We model the TLS 1.3 full handshake (1-RTT, no PSK, no 0-RTT) with
events at key points:
1. `ClientHello` — client sends (gx, offer)
2. `ServerHello` — server responds with (gy, mode)
3. `ServerFinished` — server completes its handshake
4. `ClientFinished` — client completes its handshake (agrees on key)

Event content includes both parties' identities and the derived key,
enabling correspondence assertions.
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-! ## Event Tags -/

/-- TLS handshake event tags -/
def clientHelloTag : String := "TLS.ClientHello"
def serverHelloTag : String := "TLS.ServerHello"
def serverFinishedTag : String := "TLS.ServerFinished"
def clientFinishedTag : String := "TLS.ClientFinished"

/-! ## Event Content -/

/-- Serialize ClientHello event content:
    records client identity, server identity, and DH public value -/
def mkClientHelloContent (client server : String) (gx : Bytes) : Bytes :=
  .concat (.literal client.toUTF8) (.concat (.literal server.toUTF8) gx)

/-- Serialize ServerHello event content -/
def mkServerHelloContent (server client : String) (gy : Bytes) : Bytes :=
  .concat (.literal server.toUTF8) (.concat (.literal client.toUTF8) gy)

/-- Serialize Finished event content: includes both parties and the derived key -/
def mkFinishedContent (self peer : String) (appKey : Bytes) : Bytes :=
  .concat (.literal self.toUTF8) (.concat (.literal peer.toUTF8) appKey)

/-! ## TLS Key Schedule (Simplified)

Model the TLS 1.3 key schedule as a chain of KDF operations.
This follows the HKDF-based key derivation from RFC 8446 §7.1. -/

/-- TLS 1.3 key schedule computation.
    Input: DH shared secret `dhSS` and optional PSK (we use zeros for no PSK).
    Output: application traffic secret. -/
def keySchedule (dhSS : Bytes) : Bytes :=
  let psk := Bytes.zeros 32
  -- Early secret: Extract(0, PSK)
  let earlySecret := Bytes.kdfExtract (Bytes.zeros 32) psk
  -- Derive-Secret(ES, "derived", "")
  let derivedES := Bytes.kdfExpand earlySecret (.literal "derived".toUTF8) 32
  -- Handshake secret: Extract(dES, DHE)
  let hsSecret := Bytes.kdfExtract derivedES dhSS
  -- Derive-Secret(HS, "derived", "")
  let derivedHS := Bytes.kdfExpand hsSecret (.literal "derived".toUTF8) 32
  -- Master secret: Extract(dHS, 0)
  let masterSecret := Bytes.kdfExtract derivedHS (Bytes.zeros 32)
  -- Application traffic secret
  Bytes.kdfExpand masterSecret (.literal "traffic".toUTF8) 32

/-- Handshake traffic keys (for Finished messages) -/
def handshakeKeys (dhSS : Bytes) : Bytes :=
  let psk := Bytes.zeros 32
  let earlySecret := Bytes.kdfExtract (Bytes.zeros 32) psk
  let derivedES := Bytes.kdfExpand earlySecret (.literal "derived".toUTF8) 32
  let hsSecret := Bytes.kdfExtract derivedES dhSS
  Bytes.kdfExpand hsSecret (.literal "hs_traffic".toUTF8) 32

/-! ## PSK Resumption Events

TLS 1.3 session resumption via PSK (RFC 8446 §4.2.11).
The server issues a NewSessionTicket after a successful handshake;
the client uses it to resume without a full DH exchange. -/

/-- Event tags for PSK resumption -/
def newSessionTicketTag : String := "TLS.NewSessionTicket"
def pskClientHelloTag : String := "TLS.PSKClientHello"
def pskServerHelloTag : String := "TLS.PSKServerHello"
def pskServerFinishedTag : String := "TLS.PSKServerFinished"
def pskClientFinishedTag : String := "TLS.PSKClientFinished"

/-- Content for NewSessionTicket event: identity of server + resumption secret -/
def mkTicketContent (server client : String) (resumptionSecret : Bytes) : Bytes :=
  .concat (.literal server.toUTF8) (.concat (.literal client.toUTF8) resumptionSecret)

/-- Content for PSK Finished events: includes binder + shared key -/
def mkPSKFinishedContent (self peer : String) (appKey : Bytes) : Bytes :=
  .concat (.literal self.toUTF8) (.concat (.literal peer.toUTF8) appKey)

/-- PSK key schedule: derives application traffic secret from PSK + fresh DHE.
    RFC 8446 §7.1: uses the PSK as the early secret input. -/
def pskKeySchedule (psk : Bytes) (dhSS : Bytes) : Bytes :=
  -- Early secret: Extract(0, PSK)
  let earlySecret := Bytes.kdfExtract (Bytes.zeros 32) psk
  -- Derive-Secret(ES, "derived", "")
  let derivedES := Bytes.kdfExpand earlySecret (.literal "derived".toUTF8) 32
  -- Handshake secret: Extract(dES, DHE)
  let hsSecret := Bytes.kdfExtract derivedES dhSS
  -- Derive-Secret(HS, "derived", "")
  let derivedHS := Bytes.kdfExpand hsSecret (.literal "derived".toUTF8) 32
  -- Master secret: Extract(dHS, 0)
  let masterSecret := Bytes.kdfExtract derivedHS (Bytes.zeros 32)
  -- Application traffic secret
  Bytes.kdfExpand masterSecret (.literal "traffic".toUTF8) 32

/-- PSK binder: HMAC of transcript using binder key derived from PSK.
    This authenticates the PSK holder to the server. -/
def pskBinder (psk : Bytes) (transcript : Bytes) : Bytes :=
  let earlySecret := Bytes.kdfExtract (Bytes.zeros 32) psk
  let binderKey := Bytes.kdfExpand earlySecret (.literal "binder".toUTF8) 32
  Bytes.mac binderKey transcript

/-- Resumption secret: derived from master secret after handshake completion.
    This becomes the PSK for future sessions. -/
def resumptionSecret (appKey : Bytes) : Bytes :=
  Bytes.kdfExpand appKey (.literal "resumption".toUTF8) 32

end CatCrypt.Crypto.Symbolic.TLS
