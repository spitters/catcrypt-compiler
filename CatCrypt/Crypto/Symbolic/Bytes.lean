/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Symbolic Bytes — Message Term Algebra

Port of DY*'s `bytes` inductive: a symbolic term algebra for cryptographic
messages. This is the foundation of the Dolev-Yao model.

## Main definitions

* `Bytes` — 17-constructor inductive for all TLS 1.3 primitives
* `Usage` — single-purpose key restriction labels
* Destructor functions (`aeadDec`, `pkeDec`, `signVerify`, etc.)

## Design notes

DY*-extrinsic (F*) uses a flat `bytes` type with 17 constructors covering
AEAD, PKE, signatures, hashing, DH, KDF, KEM, and MAC. We port this directly.

Terms are symbolic: `aeadEnc key nonce msg ad` does not compute encryption,
it records that encryption was applied with those arguments. The attacker
knowledge closure (in `Attacker.lean`) determines what the adversary can derive.

## References

* Barthe et al., *DY*-extrinsic*, <https://github.com/REPROSEC/dolev-yao-star-extrinsic>
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-- Single-purpose key restriction labels.

In DY*, each random value is tagged with a `Usage` that restricts how it
may be used. This prevents key-reuse attacks in the symbolic model. -/
inductive Usage where
  /-- AEAD symmetric key -/
  | aeadKey : Usage
  /-- Public-key encryption secret key -/
  | pkeKey : Usage
  /-- Signature secret key -/
  | sigKey : Usage
  /-- Diffie-Hellman secret key -/
  | dhKey : Usage
  /-- KEM secret key -/
  | kemKey : Usage
  /-- MAC key -/
  | macKey : Usage
  /-- General-purpose nonce (no key operations) -/
  | nonce : Usage
  deriving DecidableEq, Repr, Inhabited

/-- Symbolic message term algebra.

This is the core of the Dolev-Yao model: messages are terms built from
constructors corresponding to cryptographic operations. The 17 constructors
cover all primitives needed for TLS 1.3:

- **Symmetric**: AEAD encryption, MAC, hashing
- **Asymmetric**: PKE, signatures
- **Key exchange**: Diffie-Hellman, KEM
- **Key derivation**: KDF extract and expand
- **Structural**: literals, nonces, concatenation -/
inductive Bytes where
  /-- A concrete byte string literal -/
  | literal : ByteArray → Bytes
  /-- A random nonce generated at trace position `time` with length `len` -/
  | rand : (usage : Usage) → (len : Nat) → (time : Nat) → Bytes
  /-- Concatenation of two messages -/
  | concat : Bytes → Bytes → Bytes
  /-- AEAD authenticated encryption -/
  | aeadEnc : (key nonce msg ad : Bytes) → Bytes
  /-- Public key derived from secret key -/
  | pk : (sk : Bytes) → Bytes
  /-- Public-key encryption -/
  | pkeEnc : (pk nonce msg : Bytes) → Bytes
  /-- Verification key derived from signing key -/
  | vk : (sk : Bytes) → Bytes
  /-- Digital signature -/
  | sign : (sk nonce msg : Bytes) → Bytes
  /-- Cryptographic hash -/
  | hash : (msg : Bytes) → Bytes
  /-- DH public value g^sk -/
  | dhPub : (sk : Bytes) → Bytes
  /-- DH shared secret g^(sk₁·sk₂) -/
  | dh : (sk pubKey : Bytes) → Bytes
  /-- KDF extract (salt, input keying material) -/
  | kdfExtract : (salt ikm : Bytes) → Bytes
  /-- KDF expand (pseudorandom key, info, length) -/
  | kdfExpand : (prk info : Bytes) → (len : Nat) → Bytes
  /-- KEM public key -/
  | kemPub : (sk : Bytes) → Bytes
  /-- KEM encapsulation (ciphertext component) -/
  | kemEncap : (pk ss : Bytes) → Bytes
  /-- KEM shared secret -/
  | kemSecretShared : (ss : Bytes) → Bytes
  /-- Message authentication code -/
  | mac : (key msg : Bytes) → Bytes
  deriving Inhabited

-- BEq for Bytes via structural comparison
mutual
  def Bytes.beqAux : Bytes → Bytes → Bool
    | .literal a, .literal b => a == b
    | .rand u₁ l₁ t₁, .rand u₂ l₂ t₂ => u₁ == u₂ && l₁ == l₂ && t₁ == t₂
    | .concat a₁ b₁, .concat a₂ b₂ => a₁.beqAux a₂ && b₁.beqAux b₂
    | .aeadEnc k₁ n₁ m₁ a₁, .aeadEnc k₂ n₂ m₂ a₂ =>
      k₁.beqAux k₂ && n₁.beqAux n₂ && m₁.beqAux m₂ && a₁.beqAux a₂
    | .pk s₁, .pk s₂ => s₁.beqAux s₂
    | .pkeEnc p₁ n₁ m₁, .pkeEnc p₂ n₂ m₂ =>
      p₁.beqAux p₂ && n₁.beqAux n₂ && m₁.beqAux m₂
    | .vk s₁, .vk s₂ => s₁.beqAux s₂
    | .sign s₁ n₁ m₁, .sign s₂ n₂ m₂ =>
      s₁.beqAux s₂ && n₁.beqAux n₂ && m₁.beqAux m₂
    | .hash m₁, .hash m₂ => m₁.beqAux m₂
    | .dhPub s₁, .dhPub s₂ => s₁.beqAux s₂
    | .dh s₁ p₁, .dh s₂ p₂ => s₁.beqAux s₂ && p₁.beqAux p₂
    | .kdfExtract s₁ i₁, .kdfExtract s₂ i₂ => s₁.beqAux s₂ && i₁.beqAux i₂
    | .kdfExpand p₁ i₁ l₁, .kdfExpand p₂ i₂ l₂ =>
      p₁.beqAux p₂ && i₁.beqAux i₂ && l₁ == l₂
    | .kemPub s₁, .kemPub s₂ => s₁.beqAux s₂
    | .kemEncap p₁ s₁, .kemEncap p₂ s₂ => p₁.beqAux p₂ && s₁.beqAux s₂
    | .kemSecretShared s₁, .kemSecretShared s₂ => s₁.beqAux s₂
    | .mac k₁ m₁, .mac k₂ m₂ => k₁.beqAux k₂ && m₁.beqAux m₂
    | _, _ => false
end

instance : BEq Bytes := ⟨Bytes.beqAux⟩

instance : Repr ByteArray where
  reprPrec ba _ :=
    -- Try to show as string if valid UTF8, otherwise show bytes
    let s := String.fromUTF8? ba
    match s with
    | some str => .text s!"ByteArray.ofUTF8 \"{str}\""
    | none => .text s!"ByteArray#{ba.size}"

deriving instance Repr for Bytes

/-- The empty byte string -/
def Bytes.empty : Bytes := .literal ⟨#[]⟩

/-- Zeros of a given length -/
def Bytes.zeros (n : Nat) : Bytes := .literal ⟨⟨List.replicate n 0⟩⟩

/-! ## Destructor Functions

These model the symbolic "inverse" operations. They return `Option Bytes`
because destruction only succeeds when the term has the right structure. -/

/-- AEAD decryption: succeeds only if the key matches -/
def Bytes.aeadDec (key ct : Bytes) : Option Bytes :=
  match ct with
  | .aeadEnc k _nonce msg _ad => if key == k then some msg else none
  | _ => none

/-- Public-key decryption: succeeds if sk matches the pk used for encryption -/
def Bytes.pkeDec (sk ct : Bytes) : Option Bytes :=
  match ct with
  | .pkeEnc (.pk sk') _nonce msg => if sk == sk' then some msg else none
  | _ => none

/-- Signature verification: returns the message if the vk matches the sk -/
def Bytes.signVerify (verKey sig : Bytes) : Option Bytes :=
  match sig with
  | .sign sk _nonce msg => if verKey == .vk sk then some msg else none
  | _ => none

/-- Split concatenation (left component) -/
def Bytes.splitL : Bytes → Option Bytes
  | .concat b₁ _b₂ => some b₁
  | _ => none

/-- Split concatenation (right component) -/
def Bytes.splitR : Bytes → Option Bytes
  | .concat _b₁ b₂ => some b₂
  | _ => none

/-- KEM decapsulation: extract shared secret -/
def Bytes.kemDecap (sk ct : Bytes) : Option Bytes :=
  match ct with
  | .kemEncap (.kemPub sk') ss => if sk == sk' then some (.kemSecretShared ss) else none
  | _ => none

/-- MAC verification: succeeds if the key matches -/
def Bytes.macVerify (key msg tag : Bytes) : Bool :=
  tag == .mac key msg

/-! ## DH Equational Theory

The key equation: `dh sk₁ (dhPub sk₂) = dh sk₂ (dhPub sk₁)` (commutativity
of the DH shared secret). We model this as a proposition rather than
definitional equality, since we want terms to be syntactically distinct
but semantically equal. -/

/-- Two DH shared secrets are equivalent if they use swapped keys -/
def Bytes.dhEquiv (b₁ b₂ : Bytes) : Prop :=
  ∃ sk₁ sk₂, b₁ = .dh sk₁ (.dhPub sk₂) ∧ b₂ = .dh sk₂ (.dhPub sk₁)

theorem Bytes.dhEquiv_symm {b₁ b₂ : Bytes} : Bytes.dhEquiv b₁ b₂ → Bytes.dhEquiv b₂ b₁ := by
  rintro ⟨sk₁, sk₂, h₁, h₂⟩; exact ⟨sk₂, sk₁, h₂, h₁⟩

/-! ## Subterm relation -/

/-- Direct subterm relation (one level deep) -/
inductive Bytes.isDirectSubterm : Bytes → Bytes → Prop where
  | concat_l {b₁ b₂} : isDirectSubterm b₁ (.concat b₁ b₂)
  | concat_r {b₁ b₂} : isDirectSubterm b₂ (.concat b₁ b₂)
  | aeadEnc_key {k n m a} : isDirectSubterm k (.aeadEnc k n m a)
  | aeadEnc_nonce {k n m a} : isDirectSubterm n (.aeadEnc k n m a)
  | aeadEnc_msg {k n m a} : isDirectSubterm m (.aeadEnc k n m a)
  | aeadEnc_ad {k n m a} : isDirectSubterm a (.aeadEnc k n m a)
  | pk_sk {s} : isDirectSubterm s (.pk s)
  | pkeEnc_pk {p n m} : isDirectSubterm p (.pkeEnc p n m)
  | pkeEnc_nonce {p n m} : isDirectSubterm n (.pkeEnc p n m)
  | pkeEnc_msg {p n m} : isDirectSubterm m (.pkeEnc p n m)
  | vk_sk {s} : isDirectSubterm s (.vk s)
  | sign_sk {s n m} : isDirectSubterm s (.sign s n m)
  | sign_nonce {s n m} : isDirectSubterm n (.sign s n m)
  | sign_msg {s n m} : isDirectSubterm m (.sign s n m)
  | hash_msg {m} : isDirectSubterm m (.hash m)
  | dhPub_sk {s} : isDirectSubterm s (.dhPub s)
  | dh_sk {s p} : isDirectSubterm s (.dh s p)
  | dh_pub {s p} : isDirectSubterm p (.dh s p)
  | kdfExtract_salt {s i} : isDirectSubterm s (.kdfExtract s i)
  | kdfExtract_ikm {s i} : isDirectSubterm i (.kdfExtract s i)
  | kdfExpand_prk {p i l} : isDirectSubterm p (.kdfExpand p i l)
  | kdfExpand_info {p i l} : isDirectSubterm i (.kdfExpand p i l)
  | kemPub_sk {s} : isDirectSubterm s (.kemPub s)
  | kemEncap_pk {p s} : isDirectSubterm p (.kemEncap p s)
  | kemEncap_ss {p s} : isDirectSubterm s (.kemEncap p s)
  | kemSecret_ss {s} : isDirectSubterm s (.kemSecretShared s)
  | mac_key {k m} : isDirectSubterm k (.mac k m)
  | mac_msg {k m} : isDirectSubterm m (.mac k m)

end CatCrypt.Crypto.Symbolic
