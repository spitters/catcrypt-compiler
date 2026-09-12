/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Symbolic.MLS.TreeTypes

/-!
# MLS Events

MLS-specific event tags, content constructors, and key schedule functions
for the TreeSync and TreeKEM sub-protocols.

## Main definitions

* Event tag constants for MLS commit operations
* Content serialization helpers for event payloads
* TreeKEM key schedule (symbolic)

## Design

We model MLS commit operations (RFC 9420 Section 12.4) with events at key points:
1. `MLS.Commit` — committer creates a commit and updates the tree
2. `MLS.CommitVerified` — receiver verifies and processes a commit
3. `MLS.GroupEstablished` — group state is established after commit
4. `MLS.PathSecret` — path secret is derived (for key secrecy)
5. `MLS.EpochKey` — epoch key is derived

## References

* RFC 9420 — The Messaging Layer Security (MLS) Protocol
* Wallez et al., USENIX Security 2023 — TreeSync
* Wallez et al., IEEE S&P 2025 — TreeKEM
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Event Tags -/

/-- MLS commit event: committer updates the group state. -/
def commitTag : String := "MLS.Commit"

/-- MLS commit verified: receiver processes and verifies a commit. -/
def commitVerifiedTag : String := "MLS.CommitVerified"

/-- MLS group established: group state is consistent after commit. -/
def groupEstablishedTag : String := "MLS.GroupEstablished"

/-- MLS path secret: a path secret was derived for key secrecy. -/
def pathSecretTag : String := "MLS.PathSecret"

/-- MLS epoch key: an epoch key was derived. -/
def epochKeyTag : String := "MLS.EpochKey"

/-! ## Event Content Constructors

Event content is serialized using `Bytes.concat` of `Bytes.literal` tags,
following the same pattern as EDHOC events. `String.toUTF8_injective`
enables extracting identities from content. -/

/-- Serialize commit event content:
    records committer identity, group id, epoch, and tree root hash. -/
def mkCommitContent (committer : String) (groupId : Bytes) (epoch : Nat)
    (rootHash : Bytes) : Bytes :=
  .concat (.literal committer.toUTF8)
    (.concat groupId
      (.concat (.literal (toString epoch).toUTF8) rootHash))

/-- Serialize commit-verified event content:
    records receiver identity, committer identity, group id, epoch, and
    tree root hash. -/
def mkCommitVerifiedContent (receiver committer : String) (groupId : Bytes)
    (epoch : Nat) (rootHash : Bytes) : Bytes :=
  .concat (.literal receiver.toUTF8)
    (.concat (.literal committer.toUTF8)
      (.concat groupId
        (.concat (.literal (toString epoch).toUTF8) rootHash)))

/-- Serialize group-established event content:
    records member identity, group id, epoch, and agreed tree root hash. -/
def mkGroupContent (member : String) (groupId : Bytes) (epoch : Nat)
    (rootHash : Bytes) : Bytes :=
  .concat (.literal member.toUTF8)
    (.concat groupId
      (.concat (.literal (toString epoch).toUTF8) rootHash))

/-- Serialize path-secret event content:
    records committer and the path secret (for secrecy tracking). -/
def mkPathSecretContent (committer : String) (pathSecret : Bytes) : Bytes :=
  .concat (.literal committer.toUTF8) pathSecret

/-- Serialize epoch-key event content:
    records member identity and the derived epoch key. -/
def mkEpochKeyContent (member : String) (epochKey : Bytes) : Bytes :=
  .concat (.literal member.toUTF8) epochKey

/-! ## TreeKEM Epoch Key Schedule (Symbolic)

The full epoch key derivation chain, from path secret to epoch key.
Models RFC 9420 Section 8 (Key Schedule). -/

/-- Derive the joiner secret from path secret and commit secret.

In the real protocol:
  `joiner_secret = KDF.Extract(commit_secret, path_secret)`

In the symbolic model, we use `kdfExtract`. -/
def deriveJoinerSecret (pathSecret commitSecret : Bytes) : Bytes :=
  Bytes.kdfExtract commitSecret pathSecret

/-- Derive the epoch secret from joiner secret and PSK.

In the real protocol:
  `epoch_secret = KDF.Extract(PSK_secret, joiner_secret)`

The PSK may be empty (in which case we use a zero salt). -/
def deriveMlsEpochSecret (joinerSecret psk : Bytes) : Bytes :=
  Bytes.kdfExtract psk joinerSecret

/-- Derive the application key from the epoch secret.

  `application_key = KDF.Expand(epoch_secret, "app", 32)` -/
def deriveApplicationKey (epochSecret : Bytes) : Bytes :=
  Bytes.kdfExpand epochSecret (.literal "MLS.app".toUTF8) 32

/-- Full MLS key schedule: path secret + commit secret + PSK → epoch key.

Chains:
1. `joiner_secret = Extract(commit_secret, path_secret)`
2. `epoch_secret = Extract(psk, joiner_secret)`
3. `application_key = Expand(epoch_secret, "app", 32)` -/
def mlsKeySchedule (pathSecret commitSecret psk : Bytes) : Bytes :=
  let joinerSecret := deriveJoinerSecret pathSecret commitSecret
  let epochSecret := deriveMlsEpochSecret joinerSecret psk
  deriveApplicationKey epochSecret

/-! ## Label of Key Schedule

The label analysis for the MLS key schedule, used in secrecy proofs. -/

/-- Label of the MLS key schedule output.

`labelOf(mlsKeySchedule ps cs psk)`
= `labelOf(kdfExpand(kdfExtract(psk, kdfExtract(cs, ps)), _, _))`
= `labelOf(kdfExtract(psk, kdfExtract(cs, ps)))`
= `meet(labelOf(psk), labelOf(kdfExtract(cs, ps)))`
= `meet(labelOf(psk), meet(labelOf(cs), labelOf(ps)))` -/
theorem labelOf_mlsKeySchedule (tr : Trace) (ps cs psk : Bytes) :
    labelOf tr (mlsKeySchedule ps cs psk) =
    .meet (labelOf tr psk) (.meet (labelOf tr cs) (labelOf tr ps)) := by
  rfl

end CatCrypt.Crypto.Symbolic.MLS
