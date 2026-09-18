/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Events

/-!
# EDHOC Handshake Model

The EDHOC key exchange (RFC 9528) as `Traceful` programs, modeling initiator
and responder roles for all four authentication methods.

## Main definitions

* `initiatorHandshake_m3` / `responderHandshake_m3` — Method 3 (STAT-STAT)
* `initiatorHandshake_m0` / `responderHandshake_m0` — Method 0 (SIG-SIG)
* `initiatorHandshake_m1` / `responderHandshake_m1` — Method 1 (SIG-STAT)
* `initiatorHandshake_m2` / `responderHandshake_m2` — Method 2 (STAT-SIG)

## Protocol Flow (Method 3, STAT-STAT)

```
Initiator (I)                                   Responder (R)
─────────────                                   ─────────────
(1) x ←$ DH; g_x := dhPub(x)
    → message_1(I, R, g_x)

                                  (2) y ←$ DH; g_y := dhPub(y)
                                      dh_xy := dh(y, g_x)
                                      dh_rx := dh(sk_R, g_x)
                                      dh_iy := dh(y, pk_I)      -- view as dh(sk_I, g_y)
                                      prk_out := keySchedule_m3(dh_xy, dh_rx, dh_iy)
                                      mac_2 := mac(prk_out, hash(g_y))
                                      ← message_2(g_y, mac_2)
                                      trigger ResponderMsg2(R, I, g_y, prk_out)

(3) dh_xy := dh(x, g_y)
    dh_rx := dh(x, pk_R)          -- view as dh(sk_R, g_x)
    dh_iy := dh(sk_I, g_y)
    prk_out := keySchedule_m3(dh_xy, dh_rx, dh_iy)
    verify mac_2
    mac_3 := mac(prk_out, hash(g_x))
    → message_3(mac_3)
    trigger InitiatorMsg3(I, R, prk_out)

                                  (4) verify mac_3
                                      trigger ResponderVerified(R, I, prk_out)
```

## Scope

- None of the eight role programs appears in a theorem; none is verified
  against `edhocInvariants`. The honest run whose trace is analysed is
  `honestSession_m0` in `ProtocolVerification.lean`, which inlines the
  method-0 steps.
- The programs accept without checking the peer's authenticator. The
  method-0 and method-2 initiators and the method-0 and method-1 responders
  bind `Bytes.signVerify` to `_verified` and do not branch on it. The
  method-1 and method-3 initiators do not check `mac_2`, and the method-2 and
  method-3 responders do not check `mac_3`. The "verify" steps of the flow
  diagram above are absent from the programs.
- Messages 2 and 3 are sent unencrypted. Under `labelOf` a ciphertext of a
  secret plaintext is not publishable, so a trace that sends one does not
  satisfy the invariant.

## Design Notes

- EDHOC has MAC-based auth (Methods 1-3) and signature-based auth (Method 0)
- DH commutativity: `dh(x, dhPub(y))` and `dh(y, dhPub(x))` are
  structurally different terms. `Bytes.dhEquiv` relates them, but neither the
  attacker rules nor `labelOf` use it
- Each method's key schedule uses a different number of DH operations
- The `recvMsg` function models the attacker delivering messages
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-! ## Method 3 (STAT-STAT): Both parties use static DH -/

/-- Method 3 initiator role: generates ephemeral DH, sends message_1,
    processes message_2, computes 3 DH operations, sends message_3.

    Parameters:
    - `I`, `R`: initiator and responder identities
    - `sk_I`: initiator's static DH secret key
    - `pk_R`: responder's static DH public key
    - `msg2`: message_2 delivered by the network -/
def initiatorHandshake_m3 (I R : String) (sk_I pk_R : Bytes)
    (msg2 : Bytes) : Traceful Bytes := do
  -- Generate ephemeral DH key
  let x ← mkRand .dhKey (principalLabel I) 32
  let g_x := Bytes.dhPub x
  triggerEvent I initiatorMsg1Tag (mkMsg1Content I R g_x)
  sendMsg (mkMsg1Content I R g_x)
  -- Process message_2
  let _ := recvMsg msg2
  let g_y := msg2.splitL.getD Bytes.empty
  -- Three DH computations (initiator's view)
  let dh_xy := Bytes.dh x g_y             -- ephemeral-ephemeral
  let dh_rx := Bytes.dh x pk_R            -- initiator's ephemeral with responder's static
  let dh_iy := Bytes.dh sk_I g_y          -- initiator's static with responder's ephemeral
  let prk_out := edhocKeySchedule_m3 dh_xy dh_rx dh_iy
  -- Authenticate with MAC (STAT auth)
  let mac_3 := Bytes.mac prk_out (Bytes.hash g_x)
  triggerEvent I initiatorMsg3Tag (mkMsg3Content I R prk_out)
  sendMsg mac_3
  return prk_out

/-- Method 3 responder role: processes message_1, generates ephemeral DH,
    computes 3 DH operations, sends message_2, verifies message_3. -/
def responderHandshake_m3 (R I : String) (sk_R pk_I : Bytes)
    (msg1 msg3 : Bytes) : Traceful Bytes := do
  -- Parse message_1
  let g_x := msg1.splitR.bind Bytes.splitR |>.getD Bytes.empty
  -- Generate ephemeral DH key
  let y ← mkRand .dhKey (principalLabel R) 32
  let g_y := Bytes.dhPub y
  -- Three DH computations (responder's view)
  let dh_xy := Bytes.dh y g_x             -- ephemeral-ephemeral
  let dh_rx := Bytes.dh sk_R g_x          -- responder's static with initiator's ephemeral
  let dh_iy := Bytes.dh y pk_I            -- responder's ephemeral with initiator's static
  let prk_out := edhocKeySchedule_m3 dh_xy dh_rx dh_iy
  -- Send message_2 with MAC
  let mac_2 := Bytes.mac prk_out (Bytes.hash g_y)
  triggerEvent R responderMsg2Tag (mkMsg2Content R I g_y prk_out)
  sendMsg (Bytes.concat g_y mac_2)
  -- Verify message_3
  let _ := recvMsg msg3
  triggerEvent R responderVerifiedTag (mkMsg3Content I R prk_out)
  return prk_out

/-! ## Method 0 (SIG-SIG): Both parties use signatures -/

/-- Method 0 initiator role: signature-based authentication on both sides.
    Only 1 DH operation (ephemeral-ephemeral). -/
def initiatorHandshake_m0 (I R : String) (sigKey_I : Bytes) (vk_R : Bytes)
    (msg2 : Bytes) : Traceful Bytes := do
  let x ← mkRand .dhKey (principalLabel I) 32
  let g_x := Bytes.dhPub x
  triggerEvent I initiatorMsg1Tag (mkMsg1Content I R g_x)
  sendMsg (mkMsg1Content I R g_x)
  let _ := recvMsg msg2
  let g_y := msg2.splitL.getD Bytes.empty
  let sig_2 := msg2.splitR.getD Bytes.empty
  -- Single DH computation
  let dh_xy := Bytes.dh x g_y
  let prk_out := edhocKeySchedule_m0 dh_xy
  -- Verify responder's signature
  let _verified := Bytes.signVerify vk_R sig_2
  -- Sign for initiator authentication
  let nonce ← mkRand .nonce (principalLabel I) 32
  let sig_3 := Bytes.sign sigKey_I nonce (Bytes.hash g_x)
  triggerEvent I initiatorMsg3Tag (mkMsg3Content I R prk_out)
  sendMsg sig_3
  return prk_out

/-- Method 0 responder role: signature-based authentication. -/
def responderHandshake_m0 (R I : String) (sigKey_R : Bytes) (vk_I : Bytes)
    (msg1 msg3 : Bytes) : Traceful Bytes := do
  let g_x := msg1.splitR.bind Bytes.splitR |>.getD Bytes.empty
  let y ← mkRand .dhKey (principalLabel R) 32
  let g_y := Bytes.dhPub y
  let dh_xy := Bytes.dh y g_x
  let prk_out := edhocKeySchedule_m0 dh_xy
  -- Sign for responder authentication
  let nonce ← mkRand .nonce (principalLabel R) 32
  let sig_2 := Bytes.sign sigKey_R nonce (Bytes.hash g_y)
  triggerEvent R responderMsg2Tag (mkMsg2Content R I g_y prk_out)
  sendMsg (Bytes.concat g_y sig_2)
  -- Verify message_3 signature
  let _ := recvMsg msg3
  let _verified := Bytes.signVerify vk_I msg3
  triggerEvent R responderVerifiedTag (mkMsg3Content I R prk_out)
  return prk_out

/-! ## Method 1 (SIG-STAT): Initiator uses signature, responder uses static DH -/

/-- Method 1 initiator role: signs message_3, verifies responder via MAC. -/
def initiatorHandshake_m1 (I R : String) (sigKey_I : Bytes) (pk_R : Bytes)
    (msg2 : Bytes) : Traceful Bytes := do
  let x ← mkRand .dhKey (principalLabel I) 32
  let g_x := Bytes.dhPub x
  triggerEvent I initiatorMsg1Tag (mkMsg1Content I R g_x)
  sendMsg (mkMsg1Content I R g_x)
  let _ := recvMsg msg2
  let g_y := msg2.splitL.getD Bytes.empty
  -- Two DH computations
  let dh_xy := Bytes.dh x g_y
  let dh_rx := Bytes.dh x pk_R
  let prk_out := edhocKeySchedule_m1 dh_xy dh_rx
  -- Sign for initiator authentication (SIG)
  let nonce ← mkRand .nonce (principalLabel I) 32
  let sig_3 := Bytes.sign sigKey_I nonce (Bytes.hash g_x)
  triggerEvent I initiatorMsg3Tag (mkMsg3Content I R prk_out)
  sendMsg sig_3
  return prk_out

/-- Method 1 responder role: authenticates via static DH (STAT), verifies
    initiator signature. -/
def responderHandshake_m1 (R I : String) (sk_R : Bytes) (vk_I : Bytes)
    (msg1 msg3 : Bytes) : Traceful Bytes := do
  let g_x := msg1.splitR.bind Bytes.splitR |>.getD Bytes.empty
  let y ← mkRand .dhKey (principalLabel R) 32
  let g_y := Bytes.dhPub y
  let dh_xy := Bytes.dh y g_x
  let dh_rx := Bytes.dh sk_R g_x
  let prk_out := edhocKeySchedule_m1 dh_xy dh_rx
  -- MAC for responder authentication (STAT)
  let mac_2 := Bytes.mac prk_out (Bytes.hash g_y)
  triggerEvent R responderMsg2Tag (mkMsg2Content R I g_y prk_out)
  sendMsg (Bytes.concat g_y mac_2)
  -- Verify initiator's signature
  let _ := recvMsg msg3
  let _verified := Bytes.signVerify vk_I msg3
  triggerEvent R responderVerifiedTag (mkMsg3Content I R prk_out)
  return prk_out

/-! ## Method 2 (STAT-SIG): Initiator uses static DH, responder uses signature -/

/-- Method 2 initiator role: authenticates via static DH (STAT), verifies
    responder signature. -/
def initiatorHandshake_m2 (I R : String) (sk_I : Bytes) (vk_R : Bytes)
    (msg2 : Bytes) : Traceful Bytes := do
  let x ← mkRand .dhKey (principalLabel I) 32
  let g_x := Bytes.dhPub x
  triggerEvent I initiatorMsg1Tag (mkMsg1Content I R g_x)
  sendMsg (mkMsg1Content I R g_x)
  let _ := recvMsg msg2
  let g_y := msg2.splitL.getD Bytes.empty
  let sig_2 := msg2.splitR.getD Bytes.empty
  -- Two DH computations
  let dh_xy := Bytes.dh x g_y
  let dh_iy := Bytes.dh sk_I g_y
  let prk_out := edhocKeySchedule_m2 dh_xy dh_iy
  -- Verify responder's signature
  let _verified := Bytes.signVerify vk_R sig_2
  -- MAC for initiator authentication (STAT)
  let mac_3 := Bytes.mac prk_out (Bytes.hash g_x)
  triggerEvent I initiatorMsg3Tag (mkMsg3Content I R prk_out)
  sendMsg mac_3
  return prk_out

/-- Method 2 responder role: signs message_2, verifies initiator via MAC. -/
def responderHandshake_m2 (R I : String) (sigKey_R : Bytes) (pk_I : Bytes)
    (msg1 msg3 : Bytes) : Traceful Bytes := do
  let g_x := msg1.splitR.bind Bytes.splitR |>.getD Bytes.empty
  let y ← mkRand .dhKey (principalLabel R) 32
  let g_y := Bytes.dhPub y
  let dh_xy := Bytes.dh y g_x
  let dh_iy := Bytes.dh y pk_I
  let prk_out := edhocKeySchedule_m2 dh_xy dh_iy
  -- Sign for responder authentication (SIG)
  let nonce ← mkRand .nonce (principalLabel R) 32
  let sig_2 := Bytes.sign sigKey_R nonce (Bytes.hash g_y)
  triggerEvent R responderMsg2Tag (mkMsg2Content R I g_y prk_out)
  sendMsg (Bytes.concat g_y sig_2)
  -- Verify message_3 MAC
  let _ := recvMsg msg3
  triggerEvent R responderVerifiedTag (mkMsg3Content I R prk_out)
  return prk_out

end CatCrypt.Crypto.Symbolic.EDHOC
