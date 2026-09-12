/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Properties

/-!
# EDHOC Events

EDHOC-specific event tags, content constructors, and key schedules for all
four authentication methods defined in RFC 9528.

## Main definitions

* Event tag constants for the EDHOC 3-message handshake
* Content serialization helpers for event payloads
* Key schedule functions for Methods 0–3

## Design

We model the EDHOC key exchange (RFC 9528) with events at key points:
1. `InitiatorMsg1` — initiator sends message_1 (g_x)
2. `ResponderMsg2` — responder sends message_2 (g_y, MAC/signature)
3. `InitiatorMsg3` — initiator sends message_3 (MAC/signature)
4. `ResponderVerified` — responder verifies message_3 (key confirmation)

EDHOC has 4 authentication methods:
- Method 0 (SIG-SIG): both parties authenticate via signatures
- Method 1 (SIG-STAT): initiator uses signature, responder uses static DH
- Method 2 (STAT-SIG): initiator uses static DH, responder uses signature
- Method 3 (STAT-STAT): both parties use static DH

The key schedule uses up to 3 DH operations and a 4-step HKDF chain.

## References

* RFC 9528 — EDHOC: A Lightweight Authenticated Key Exchange
* charlie-j/edhoc-formal-analysis — USENIX Security 2023
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-! ## Event Tags -/

/-- EDHOC handshake event tags -/
def initiatorMsg1Tag : String := "EDHOC.InitiatorMsg1"
def responderMsg2Tag : String := "EDHOC.ResponderMsg2"
def initiatorMsg3Tag : String := "EDHOC.InitiatorMsg3"
def responderVerifiedTag : String := "EDHOC.ResponderVerified"

/-! ## Event Content -/

/-- Serialize message_1 event content:
    records initiator identity, responder identity, and DH public value -/
def mkMsg1Content (initiator responder : String) (g_x : Bytes) : Bytes :=
  .concat (.literal initiator.toUTF8) (.concat (.literal responder.toUTF8) g_x)

/-- Serialize message_2 event content:
    records responder identity, initiator identity, DH public value, and derived key -/
def mkMsg2Content (responder initiator : String) (g_y prk_out : Bytes) : Bytes :=
  .concat (.literal responder.toUTF8)
    (.concat (.literal initiator.toUTF8)
      (.concat g_y prk_out))

/-- Serialize message_3 event content:
    records initiator identity, responder identity, and derived key -/
def mkMsg3Content (initiator responder : String) (prk_out : Bytes) : Bytes :=
  .concat (.literal initiator.toUTF8) (.concat (.literal responder.toUTF8) prk_out)

/-! ## EDHOC Key Schedules (Symbolic)

Model the EDHOC key schedule as chains of KDF operations.
Each method uses a different number of DH steps and KDF stages.

The key schedule follows RFC 9528 §4:
- prk_2e = Extract(TH_2, ECDH(x, g_y))                 — all methods
- prk_3e2m = Extract(Expand(prk_2e, ...), ECDH(r, g_x)) — Methods 1, 3
- prk_4e3m = Extract(Expand(prk_3e2m, ...), ECDH(i, g_y)) — Methods 2, 3
- prk_out = Expand(prk_Xe3m, ...)                        — all methods -/

/-- Method 0 (SIG-SIG) key schedule: 1 DH operation.
    Both parties authenticate via signatures, only ephemeral DH. -/
def edhocKeySchedule_m0 (dhXY : Bytes) : Bytes :=
  let prk_2e := Bytes.kdfExtract (Bytes.hash dhXY) dhXY
  Bytes.kdfExpand prk_2e (.literal "prk_out_m0".toUTF8) 32

/-- Method 1 (SIG-STAT) key schedule: 2 DH operations.
    Initiator uses signature, responder uses static DH.
    - dhXY: ECDH(x, g_y) — ephemeral-ephemeral
    - dhRX: ECDH(r, g_x) — responder static with initiator ephemeral -/
def edhocKeySchedule_m1 (dhXY dhRX : Bytes) : Bytes :=
  let prk_2e := Bytes.kdfExtract (Bytes.hash dhXY) dhXY
  let salt_3e2m := Bytes.kdfExpand prk_2e (.literal "salt_3e2m".toUTF8) 32
  let prk_3e2m := Bytes.kdfExtract salt_3e2m dhRX
  Bytes.kdfExpand prk_3e2m (.literal "prk_out_m1".toUTF8) 32

/-- Method 2 (STAT-SIG) key schedule: 2 DH operations.
    Initiator uses static DH, responder uses signature.
    - dhXY: ECDH(x, g_y) — ephemeral-ephemeral
    - dhIY: ECDH(i, g_y) — initiator static with responder ephemeral -/
def edhocKeySchedule_m2 (dhXY dhIY : Bytes) : Bytes :=
  let prk_2e := Bytes.kdfExtract (Bytes.hash dhXY) dhXY
  let salt_4e3m := Bytes.kdfExpand prk_2e (.literal "salt_4e3m".toUTF8) 32
  let prk_4e3m := Bytes.kdfExtract salt_4e3m dhIY
  Bytes.kdfExpand prk_4e3m (.literal "prk_out_m2".toUTF8) 32

/-- Method 3 (STAT-STAT) key schedule: 3 DH operations.
    Both parties use static DH (most complex method).
    - dhXY: ECDH(x, g_y) — ephemeral-ephemeral
    - dhRX: ECDH(r, g_x) — responder static with initiator ephemeral
    - dhIY: ECDH(i, g_y) — initiator static with responder ephemeral -/
def edhocKeySchedule_m3 (dhXY dhRX dhIY : Bytes) : Bytes :=
  let prk_2e := Bytes.kdfExtract (Bytes.hash dhXY) dhXY
  let salt_3e2m := Bytes.kdfExpand prk_2e (.literal "salt_3e2m".toUTF8) 32
  let prk_3e2m := Bytes.kdfExtract salt_3e2m dhRX
  let salt_4e3m := Bytes.kdfExpand prk_3e2m (.literal "salt_4e3m".toUTF8) 32
  let prk_4e3m := Bytes.kdfExtract salt_4e3m dhIY
  Bytes.kdfExpand prk_4e3m (.literal "prk_out_m3".toUTF8) 32

end CatCrypt.Crypto.Symbolic.EDHOC
