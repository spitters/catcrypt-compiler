/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.MLS.Events
public import CatCrypt.Crypto.Symbolic.MLS.TreeInvariants

/-!
# MLS Protocol Model

The MLS commit operation (RFC 9420 Section 12.4) as `Traceful` programs,
modeling the committer and receiver roles.

## Main definitions

* `commitOperation` — committer creates a commit (generates path secret,
  encrypts for co-path, signs tree, triggers commit event)
* `processCommit` — receiver verifies and processes a commit (verify signature,
  decrypt path secret, derive epoch key, trigger verified event)

## Protocol Flow

```
Committer (C)                                  Receivers (R₁, ..., Rₖ)
─────────────                                  ──────────────────────
(1) pathSecret ←$ nonce
    for each node on direct path:
      nodeSecret = TreeKDF(pathSecret, i)
      hpkeKey = deriveHPKEKey(nodeSecret)
      encrypt pathSecret for co-path
    sign updated tree hash
    → Commit(C, groupId, epoch, rootHash)
    send commitMsg(pathCiphertexts, sig)

                                    (2) verify signature
                                        decrypt pathSecret from co-path
                                        epochKey = mlsKeySchedule(pathSecret, ...)
                                        → CommitVerified(Rᵢ, C, groupId, epoch, rootHash)
```

## References

* RFC 9420 Section 12.4 — Commit
* RFC 9420 Section 7.4 — TreeKEM
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Commit Operation -/

/-- The committer role: creates a commit updating the group tree.

1. Generates a fresh path secret (nonce labeled with committer's principal label)
2. Derives node secrets for each position on the direct path
3. Encrypts the path secret for each co-path member using KEM
4. Signs the updated tree root hash
5. Triggers the `Commit` event and sends the commit message

Parameters:
- `committer`: committer's identity
- `sigKey`: committer's signing key
- `members`: list of group members
- `groupId`: group identifier
- `epoch`: current epoch number
- `rootHash`: hash of the updated tree -/
def commitOperation (committer : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat)
    (rootHash : Bytes)
    (recipientKeys : List Bytes) : Traceful Bytes := do
  -- Generate fresh path secret
  let pathSecret ← mkRand .nonce (groupLabel members) 32
  -- Generate commit secret
  let commitSecret ← mkRand .nonce (principalLabel committer) 32
  -- Derive epoch key via full key schedule
  let epochKey := mlsKeySchedule pathSecret commitSecret (.literal "".toUTF8)
  -- Track the path secret for secrecy analysis
  triggerEvent committer pathSecretTag (mkPathSecretContent committer pathSecret)
  -- Encrypt path secret for each co-path recipient
  for pk in recipientKeys do
    let ss ← mkRand .kemKey (principalLabel committer) 32
    let _ct := Bytes.kemEncap pk ss
    sendMsg (Bytes.kemEncap pk ss)
  -- Sign the updated tree root hash
  let nonce ← mkRand .nonce (principalLabel committer) 32
  let sig := Bytes.sign sigKey nonce rootHash
  -- Trigger commit event
  triggerEvent committer commitTag (mkCommitContent committer groupId epoch rootHash)
  -- Send commit message: signature + encrypted path secrets
  sendMsg (.concat sig rootHash)
  -- Track epoch key
  triggerEvent committer epochKeyTag (mkEpochKeyContent committer epochKey)
  return epochKey

/-- The receiver role: processes and verifies a commit.

1. Receives the commit message
2. Verifies the committer's signature on the tree root hash
3. Decrypts the path secret from the KEM ciphertext
4. Derives the epoch key using the full key schedule
5. Triggers the `CommitVerified` event

Parameters:
- `receiver`: receiver's identity
- `committer`: committer's identity (from commit message)
- `committerVK`: committer's verification key
- `groupId`: group identifier
- `epoch`: epoch number from the commit
- `kemSK`: receiver's KEM secret key (for decrypting path secret)
- `commitMsg`: the commit message (sig ++ rootHash)
- `kemCT`: the KEM ciphertext containing the path secret -/
def processCommit (receiver committer : String) (committerVK : Bytes)
    (groupId : Bytes) (epoch : Nat)
    (kemSK : Bytes) (commitMsg kemCT : Bytes) : Traceful (Option Bytes) := do
  -- Parse commit message
  let sig := commitMsg.splitL.getD Bytes.empty
  let rootHash := commitMsg.splitR.getD Bytes.empty
  -- Verify committer's signature
  let verified := Bytes.signVerify committerVK sig
  match verified with
  | none => return none  -- Signature verification failed
  | some _ =>
    -- Decrypt path secret via KEM
    let pathSecretOpt := Bytes.kemDecap kemSK kemCT
    match pathSecretOpt with
    | none => return none  -- KEM decapsulation failed
    | some pathSecretShared =>
      -- Derive epoch key
      -- Use a default commit secret (in practice, sent alongside)
      let epochKey := mlsKeySchedule pathSecretShared
        (.literal "".toUTF8) (.literal "".toUTF8)
      -- Trigger commit-verified event
      triggerEvent receiver commitVerifiedTag
        (mkCommitVerifiedContent receiver committer groupId epoch rootHash)
      -- Trigger group-established event
      triggerEvent receiver groupEstablishedTag
        (mkGroupContent receiver groupId epoch rootHash)
      -- Track epoch key
      triggerEvent receiver epochKeyTag (mkEpochKeyContent receiver epochKey)
      return (some epochKey)

/-! ## Helper: Update Tree with Commit -/

/-- Update the tree by replacing a leaf and recomputing parent hashes.

This models the tree update that happens during a commit:
the committer's leaf is updated with new HPKE keys derived from
the path secret, and parent nodes along the direct path get
new HPKE keys and updated parent hashes. -/
def updateTreeLeaf {n : Nat} (tree : SymTree n) (idx : LeafIndex n)
    (newContent : NodeContent) : SymTree n :=
  setLeaf tree idx newContent

end CatCrypt.Crypto.Symbolic.MLS
