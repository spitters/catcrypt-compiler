/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Symbolic.Properties

/-!
# Signal X3DH Events

Signal-specific event tags and content constructors for correspondence
properties. Models the X3DH initial key agreement and one ratchet step.

## Main definitions

* Event tags for X3DH initiator/responder and ratchet steps
* Content serialization helpers
* Signal key schedule (4-DH X3DH + ratchet step)

## Protocol Flow (X3DH)

```
Alice                                              Bob
──────                                             ───
(1) ek ←$ DH (ephemeral key)
    ikA ←$ DH (identity key, long-term)
    Compute:
      dh1 := dh(ikA, spkB)         -- identity × signed prekey
      dh2 := dh(ek, ikB)           -- ephemeral × identity
      dh3 := dh(ek, spkB)          -- ephemeral × signed prekey
      dh4 := dh(ek, opkB)          -- ephemeral × one-time prekey
    rootKey := signalKeySchedule(dh1, dh2, dh3, dh4)
    trigger X3DHInit(alice, bob, rootKey)
    → (dhPub(ek), dhPub(ikA))

                                    (2) Receive (gek, gikA)
                                        Compute same 4 DH operations
                                        rootKey := signalKeySchedule(...)
                                        trigger X3DHResp(bob, alice, rootKey)
```

## References

* Signal Protocol specification: X3DH key agreement
* DY* Signal formalization (Bhargavan et al.)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

/-! ## Event Tags -/

def x3dhInitTag : String := "Signal.X3DHInit"
def x3dhRespTag : String := "Signal.X3DHResp"
def ratchetStepTag : String := "Signal.RatchetStep"

/-! ## Event Content -/

/-- X3DH event content: identity of self, peer, and derived root key. -/
def mkX3DHContent (self peer : String) (rootKey : Bytes) : Bytes :=
  .concat (.literal self.toUTF8) (.concat (.literal peer.toUTF8) rootKey)

/-- Ratchet step event content. -/
def mkRatchetContent (self peer : String) (epoch : Nat) (chainKey : Bytes) : Bytes :=
  .concat (.literal self.toUTF8)
    (.concat (.literal peer.toUTF8)
      (.concat (.literal (toString epoch).toUTF8) chainKey))

/-! ## Signal Key Schedule -/

/-- X3DH key schedule: 4 DH shared secrets → root key.
    `KDF(0 || dh1 || dh2 || dh3 || dh4)` -/
def signalKeySchedule (dh1 dh2 dh3 dh4 : Bytes) : Bytes :=
  Bytes.kdfExtract (Bytes.zeros 32)
    (.concat (.concat dh1 dh2) (.concat dh3 dh4))

/-- Ratchet step: derive new root key from current root key and DH input. -/
def ratchetStep (rootKey dhInput : Bytes) : Bytes :=
  Bytes.kdfExtract rootKey dhInput

end CatCrypt.Crypto.Symbolic.Signal
