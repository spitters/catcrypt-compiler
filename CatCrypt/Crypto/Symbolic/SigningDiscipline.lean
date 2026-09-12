/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Attacker
public import CatCrypt.Crypto.Symbolic.TracefulSpec

/-!
# Signing Discipline — Authentication Primitives

In the DY model, if a cryptographic key has a principal label and the trace
invariant holds, then the attacker knowing the key implies the principal is
corrupt. This is the foundation for all authentication proofs.

## Main definitions

* `key_compromise` — knowing a principal-labeled key implies corruption
* `publishable_of_canFlow_corrupt` — values with sufficiently restricted
  labels are unpublishable without corruption

## Design

The authentication argument in the symbolic model is:
1. Protocol code triggers events when performing operations with keys
2. The `eventPred` records the correspondence property
3. `key_compromise` shows that an attacker producing operations with
   principal-labeled keys requires corruption

This file provides the generic key compromise lemma that all three
protocols (TLS, EDHOC, MLS) use.

## References

* DY*-extrinsic: `DY.Lib.Crypto.Sig.Lemma`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-! ## Key Compromise

The fundamental lemma: if the attacker knows a value with a principal label,
the principal must be corrupt. -/

/-- If the attacker knows a bytes value whose label is `principalLabel p`,
then `p` must be in the trace's corrupt set.

This is the core of all authentication proofs: signing keys, DH secret
keys, MAC keys, etc. that are labeled with a principal's identity cannot
be known to the attacker unless the principal is corrupted. -/
theorem key_compromise [inst : ProtocolInvariants]
    {tr : Trace} {b : Bytes} {p : String}
    (hInv : traceInvariant tr)
    (hLabel : hasLabel tr b (principalLabel p))
    (hKnows : AttackerKnows tr b) :
    tr.corruptSet p := by
  have hPub := attacker_only_knows_publishable hInv hKnows
  unfold bytesPublishable at hPub
  rw [hLabel] at hPub
  exact hPub

/-- More general: if the attacker knows a value whose label flows to
`principalLabel p`, the principal must be corrupt. -/
theorem key_compromise_flow [inst : ProtocolInvariants]
    {tr : Trace} {b : Bytes} {p : String}
    (hInv : traceInvariant tr)
    (hFlow : canFlow (labelOf tr b) (principalLabel p))
    (hKnows : AttackerKnows tr b) :
    tr.corruptSet p := by
  have hPub := attacker_only_knows_publishable hInv hKnows
  exact hFlow _ hPub

/-! ## DH Key Label Analysis

For DH-based protocols, the shared secret `dh(sk, dhPub(pk))` has label
`labelOf tr sk`. If `sk` has `principalLabel p`, then the DH shared
secret's label is also `principalLabel p`. -/

/-- Label of a DH shared secret is the label of the secret key. -/
theorem labelOf_dh (tr : Trace) (sk pk : Bytes) :
    labelOf tr (.dh sk pk) = labelOf tr sk := rfl

/-- Label of a KDF-derived key inherits from the inputs. -/
theorem labelOf_kdfExtract (tr : Trace) (salt ikm : Bytes) :
    labelOf tr (.kdfExtract salt ikm) =
    .meet (labelOf tr salt) (labelOf tr ikm) := rfl

/-- Label of a KDF-expanded key inherits from the PRK. -/
theorem labelOf_kdfExpand (tr : Trace) (prk info : Bytes) (len : Nat) :
    labelOf tr (.kdfExpand prk info len) = labelOf tr prk := rfl

/-! ## Publishability Lemmas -/

/-- Signatures are always publishable (label = top). -/
theorem signature_publishable (tr : Trace) (sk nonce msg : Bytes) :
    bytesPublishable tr (.sign sk nonce msg) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- MACs are always publishable (label = top). -/
theorem mac_publishable (tr : Trace) (key msg : Bytes) :
    bytesPublishable tr (.mac key msg) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- Hashes are always publishable (label = top). -/
theorem hash_publishable (tr : Trace) (msg : Bytes) :
    bytesPublishable tr (.hash msg) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- Public keys are always publishable (label = top). -/
theorem pk_publishable (tr : Trace) (sk : Bytes) :
    bytesPublishable tr (.pk sk) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- Verification keys are always publishable (label = top). -/
theorem vk_publishable (tr : Trace) (sk : Bytes) :
    bytesPublishable tr (.vk sk) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- DH public keys are always publishable (label = top). -/
theorem dhPub_publishable (tr : Trace) (sk : Bytes) :
    bytesPublishable tr (.dhPub sk) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- KEM public keys are always publishable (label = top). -/
theorem kemPub_publishable (tr : Trace) (sk : Bytes) :
    bytesPublishable tr (.kemPub sk) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- Literals are always publishable (label = top). -/
theorem literal_publishable (tr : Trace) (bs : ByteArray) :
    bytesPublishable tr (.literal bs) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]

/-- Concat is publishable if both components are. -/
theorem concat_publishable (tr : Trace) (b₁ b₂ : Bytes) :
    bytesPublishable tr b₁ → bytesPublishable tr b₂ →
    bytesPublishable tr (.concat b₁ b₂) := by
  simp [bytesPublishable, labelOf, Label.isCorrupt]
  exact And.intro

end CatCrypt.Crypto.Symbolic
