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

* `commitOperation` — committer creates a commit (generates the path secret
  and the commit secret, seals both to each co-path member with a KEM and an
  AEAD under the encapsulated secret, signs the tree root hash, triggers the
  commit event)
* `processCommit` — receiver verifies and processes a commit (verifies the
  signature, decapsulates and decrypts the path secret and the commit secret,
  derives the epoch key, triggers the verified event)
* `openPathSecret_sealPathSecret` — the receiver's opening inverts the
  committer's sealing at the matching KEM secret key

## Protocol Flow

```
Committer (C)                                  Receivers (R₁, ..., Rₖ)
─────────────                                  ──────────────────────
(1) pathSecret   ←$ kemKey (group label)
    commitSecret ←$ kemKey (committer label)
    epochKey = mlsKeySchedule(pathSecret, commitSecret, "")
    for each co-path member with HPKE key pkᵢ:
      ssᵢ ←$ kemKey
      send kemEncap(pkᵢ, ssᵢ) ‖ aeadEnc(kemSecretShared(ssᵢ), nonceᵢ,
                                        pathSecret ‖ commitSecret, "")
    sign updated tree root hash
    → Commit(C, groupId, epoch, rootHash)
    send sig ‖ rootHash

                                    (2) rootHash = signVerify(vk_C, sig)
                                        ssᵢ = kemDecap(skᵢ, kemCT)
                                        pathSecret ‖ commitSecret = aeadDec(ssᵢ, ct)
                                        epochKey = mlsKeySchedule(pathSecret, commitSecret, "")
                                        → CommitVerified(Rᵢ, C, groupId, epoch, rootHash)
```

The sealed path message is the symbolic form of the HPKE `EncryptWithLabel`
of RFC 9420 Section 7.6: a KEM encapsulation of a fresh secret followed by an
AEAD of the payload under the encapsulated secret. The receiver's epoch key is
built from the decrypted secrets, so it equals the committer's epoch key term
when the ciphertext is delivered unmodified.

## References

* RFC 9420 Section 12.4 — Commit
* RFC 9420 Section 7.4 — TreeKEM
* RFC 9420 Section 7.6 — Update Paths
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Structural Equality of Terms -/

/-- `Bytes.beqAux` is reflexive: every term is `BEq`-equal to itself. -/
theorem Bytes.beqAux_self (b : Bytes) : Bytes.beqAux b b = true := by
  induction b with
  | literal a =>
    simp only [Bytes.beqAux]
    show a.beq a = true
    simp [ByteArray.beq]
  | rand _ _ _ => simp [Bytes.beqAux]
  | concat _ _ ih₁ ih₂ => simp [Bytes.beqAux, ih₁, ih₂]
  | aeadEnc _ _ _ _ ihk ihn ihm iha => simp [Bytes.beqAux, ihk, ihn, ihm, iha]
  | pk _ ih => simp [Bytes.beqAux, ih]
  | pkeEnc _ _ _ ihp ihn ihm => simp [Bytes.beqAux, ihp, ihn, ihm]
  | vk _ ih => simp [Bytes.beqAux, ih]
  | sign _ _ _ ihs ihn ihm => simp [Bytes.beqAux, ihs, ihn, ihm]
  | hash _ ih => simp [Bytes.beqAux, ih]
  | dhPub _ ih => simp [Bytes.beqAux, ih]
  | dh _ _ ihs ihp => simp [Bytes.beqAux, ihs, ihp]
  | kdfExtract _ _ ihs ihi => simp [Bytes.beqAux, ihs, ihi]
  | kdfExpand _ _ _ ihp ihi => simp [Bytes.beqAux, ihp, ihi]
  | kemPub _ ih => simp [Bytes.beqAux, ih]
  | kemEncap _ _ ihp ihs => simp [Bytes.beqAux, ihp, ihs]
  | kemSecretShared _ ih => simp [Bytes.beqAux, ih]
  | mac _ _ ihk ihm => simp [Bytes.beqAux, ihk, ihm]

/-- `BEq` on `Bytes` is reflexive. -/
@[simp] theorem Bytes.beq_self (b : Bytes) : (b == b) = true :=
  Bytes.beqAux_self b

/-! ## Sealed Path Messages -/

/-- The path message sealed to one co-path member: the KEM encapsulation of
`ss` under `pk`, concatenated with the AEAD of `pathSecret ‖ commitSecret`
under the encapsulated secret `kemSecretShared ss` with nonce `nonce`. -/
def sealPathSecret (pk ss nonce pathSecret commitSecret : Bytes) : Bytes :=
  .concat (Bytes.kemEncap pk ss)
    (.aeadEnc (.kemSecretShared ss) nonce (.concat pathSecret commitSecret)
      (.literal "".toUTF8))

/-- The inverse of `sealPathSecret` at the receiver holding the KEM secret key
`kemSK`: decapsulates the left component and decrypts the right one under the
recovered secret, returning `pathSecret ‖ commitSecret`. -/
def openPathSecret (kemSK pathMsg : Bytes) : Option Bytes := do
  let kemCT ← pathMsg.splitL
  let ct ← pathMsg.splitR
  let ss ← Bytes.kemDecap kemSK kemCT
  Bytes.aeadDec ss ct

/-- `openPathSecret` inverts `sealPathSecret` at the matching KEM secret key. -/
theorem openPathSecret_sealPathSecret (kemSK ss nonce pathSecret commitSecret : Bytes) :
    openPathSecret kemSK (sealPathSecret (.kemPub kemSK) ss nonce pathSecret commitSecret) =
      some (.concat pathSecret commitSecret) := by
  simp [openPathSecret, sealPathSecret, Bytes.splitL, Bytes.splitR, Bytes.kemDecap,
    Bytes.aeadDec]

/-! ## Commit Operation -/

/-- The committer role: creates a commit updating the group tree.

1. Generates a fresh path secret (labeled with the group label) and a fresh
   commit secret (labeled with the committer's principal label), both as
   `kemKey` samples
2. Derives the epoch key from both through `mlsKeySchedule`
3. Seals the same path secret and commit secret to each co-path recipient
   with `sealPathSecret`
4. Signs the updated tree root hash
5. Triggers the `Commit` event and sends the commit message

Parameters:
- `committer`: committer's identity
- `sigKey`: committer's signing key
- `members`: list of group members
- `groupId`: group identifier
- `epoch`: current epoch number
- `rootHash`: hash of the updated tree
- `recipientKeys`: the KEM public keys of the co-path members -/
def commitOperation (committer : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat)
    (rootHash : Bytes)
    (recipientKeys : List Bytes) : Traceful Bytes := do
  -- Generate the path secret and the commit secret
  let pathSecret ← mkRand .kemKey (groupLabel members) 32
  let commitSecret ← mkRand .kemKey (principalLabel committer) 32
  -- Derive epoch key via full key schedule
  let epochKey := mlsKeySchedule pathSecret commitSecret (.literal "".toUTF8)
  -- Track the path secret for secrecy analysis
  triggerEvent committer pathSecretTag (mkPathSecretContent committer pathSecret)
  -- Seal the path secret and the commit secret to each co-path recipient
  for pk in recipientKeys do
    let ss ← mkRand .kemKey (principalLabel committer) 32
    let nonce ← mkRand .nonce (principalLabel committer) 32
    sendMsg (sealPathSecret pk ss nonce pathSecret commitSecret)
  -- Sign the updated tree root hash
  let nonce ← mkRand .nonce (principalLabel committer) 32
  let sig := Bytes.sign sigKey nonce rootHash
  -- Trigger commit event
  triggerEvent committer commitTag (mkCommitContent committer groupId epoch rootHash)
  -- Send commit message: signature and root hash
  sendMsg (.concat sig rootHash)
  -- Track epoch key
  triggerEvent committer epochKeyTag (mkEpochKeyContent committer epochKey)
  return epochKey

/-- The receiver role: processes and verifies a commit.

1. Verifies the committer's signature; the signed message is the root hash
2. Opens the sealed path message with `openPathSecret`, recovering the path
   secret and the commit secret
3. Derives the epoch key from the recovered secrets with `mlsKeySchedule`
4. Triggers the `CommitVerified`, `GroupEstablished` and `EpochKey` events

Returns `none` when signature verification or opening fails.

Parameters:
- `receiver`: receiver's identity
- `committer`: committer's identity (from commit message)
- `committerVK`: committer's verification key
- `groupId`: group identifier
- `epoch`: epoch number from the commit
- `kemSK`: receiver's KEM secret key
- `commitMsg`: the commit message (`sig ‖ rootHash`)
- `pathMsg`: the sealed path message addressed to the receiver -/
def processCommit (receiver committer : String) (committerVK : Bytes)
    (groupId : Bytes) (epoch : Nat)
    (kemSK : Bytes) (commitMsg pathMsg : Bytes) : Traceful (Option Bytes) := do
  -- Parse commit message
  let sig := commitMsg.splitL.getD Bytes.empty
  -- Verify the committer's signature; the signed message is the root hash
  match Bytes.signVerify committerVK sig with
  | none => return none
  | some rootHash =>
    -- Recover the path secret and the commit secret
    match openPathSecret kemSK pathMsg with
    | none => return none
    | some secrets =>
      let pathSecret := secrets.splitL.getD Bytes.empty
      let commitSecret := secrets.splitR.getD Bytes.empty
      -- Derive epoch key
      let epochKey := mlsKeySchedule pathSecret commitSecret (.literal "".toUTF8)
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
