/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Invariant

/-!
# Attacker Knowledge — Dolev-Yao Closure

An attacker knowledge predicate in the style of DY*. The attacker can derive new
messages from known messages using the cryptographic constructors and
destructors. The main theorem shows that attacker knowledge respects
the label discipline.

## Main definitions

* `AttackerKnows` — inductive: messages the attacker can derive
* `attacker_only_knows_publishable` — main theorem: if the trace invariant
  holds, then everything the attacker knows is publishable

## Differences from DY*

* The rule for Diffie–Hellman builds `dh sk (dhPub pk')` from a known `sk`.
  There is no equation `dh x (dhPub y) = dh y (dhPub x)`, and `Bytes.dhEquiv`
  is not used here, so an attacker holding `y` does not derive the secret an
  uncompromised party computes as `dh x (dhPub y)`.
* The attacker does not generate randomness, and no rule recovers a message
  from its signature.

## References

* DY*-extrinsic: `DY.Core.Attacker.Knowledge`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-- Messages that the Dolev-Yao attacker can derive from a trace. -/
inductive AttackerKnows (tr : Trace) : Bytes → Prop where
  | network {msg : Bytes} {i : Nat} :
    tr.entryAt i = some (.msgSent msg) → AttackerKnows tr msg
  | corruptState {prin : String} {sessId : Nat} {content : Bytes} {i j : Nat} :
    tr.entryAt i = some (.corrupt prin) →
    tr.entryAt j = some (.setState prin sessId content) →
    AttackerKnows tr content
  | literal (bs : ByteArray) : AttackerKnows tr (.literal bs)
  | concat {b₁ b₂ : Bytes} :
    AttackerKnows tr b₁ → AttackerKnows tr b₂ →
    AttackerKnows tr (.concat b₁ b₂)
  | splitL {b₁ b₂ : Bytes} :
    AttackerKnows tr (.concat b₁ b₂) → AttackerKnows tr b₁
  | splitR {b₁ b₂ : Bytes} :
    AttackerKnows tr (.concat b₁ b₂) → AttackerKnows tr b₂
  | aeadEnc {key nonce msg ad : Bytes} :
    AttackerKnows tr key → AttackerKnows tr nonce →
    AttackerKnows tr msg → AttackerKnows tr ad →
    AttackerKnows tr (.aeadEnc key nonce msg ad)
  | aeadDec {key nonce msg ad : Bytes} :
    AttackerKnows tr key → AttackerKnows tr (.aeadEnc key nonce msg ad) →
    AttackerKnows tr msg
  | pk {sk : Bytes} :
    AttackerKnows tr sk → AttackerKnows tr (.pk sk)
  | pkeEnc {pk' nonce msg : Bytes} :
    AttackerKnows tr pk' → AttackerKnows tr nonce →
    AttackerKnows tr msg →
    AttackerKnows tr (.pkeEnc pk' nonce msg)
  | pkeDec {sk nonce msg : Bytes} :
    AttackerKnows tr sk → AttackerKnows tr (.pkeEnc (.pk sk) nonce msg) →
    AttackerKnows tr msg
  | vk {sk : Bytes} :
    AttackerKnows tr sk → AttackerKnows tr (.vk sk)
  | sign {sk nonce msg : Bytes} :
    AttackerKnows tr sk → AttackerKnows tr nonce →
    AttackerKnows tr msg →
    AttackerKnows tr (.sign sk nonce msg)
  | hash {msg : Bytes} :
    AttackerKnows tr msg → AttackerKnows tr (.hash msg)
  | dhPub {sk : Bytes} :
    AttackerKnows tr sk → AttackerKnows tr (.dhPub sk)
  | dh {sk pk' : Bytes} :
    AttackerKnows tr sk → AttackerKnows tr (.dhPub pk') →
    AttackerKnows tr (.dh sk (.dhPub pk'))
  | kdfExtract {salt ikm : Bytes} :
    AttackerKnows tr salt → AttackerKnows tr ikm →
    AttackerKnows tr (.kdfExtract salt ikm)
  | kdfExpand {prk info : Bytes} (len : Nat) :
    AttackerKnows tr prk → AttackerKnows tr info →
    AttackerKnows tr (.kdfExpand prk info len)
  | kemPub {sk : Bytes} :
    AttackerKnows tr sk → AttackerKnows tr (.kemPub sk)
  | kemEncap {pk' ss : Bytes} :
    AttackerKnows tr pk' → AttackerKnows tr ss →
    AttackerKnows tr (.kemEncap pk' ss)
  | kemDecap {sk ss : Bytes} :
    AttackerKnows tr sk →
    AttackerKnows tr (.kemEncap (.kemPub sk) ss) →
    AttackerKnows tr (.kemSecretShared ss)
  | mac {key msg : Bytes} :
    AttackerKnows tr key → AttackerKnows tr msg →
    AttackerKnows tr (.mac key msg)

/-! ## Main Theorem -/

/-- **Main theorem**: The Dolev-Yao attacker can only derive publishable values. -/
theorem attacker_only_knows_publishable [inst : ProtocolInvariants]
    {tr : Trace} {msg : Bytes}
    (hInv : traceInvariant tr)
    (hKnows : AttackerKnows tr msg) :
    bytesPublishable tr msg := by
  unfold bytesPublishable
  induction hKnows with
  | network hEntry =>
    have hi := Trace.entryAt_lt_length hEntry
    exact hInv _ hi _ hEntry
  | corruptState hCorrupt hState =>
    have hj := Trace.entryAt_lt_length hState
    have hStatePred := hInv _ hj _ hState
    have hCorruptSet := Trace.corruptSet_of_entryAt hCorrupt
    exact inst.statePred_label _ _ _ _ hStatePred _ hCorruptSet
  | literal _ =>
    simp [labelOf, Label.isCorrupt]
  | concat _ _ ih₁ ih₂ =>
    simp only [labelOf, Label.isCorrupt]
    exact ⟨ih₁, ih₂⟩
  | splitL _ ih =>
    simp only [labelOf, Label.isCorrupt] at ih
    exact ih.1
  | splitR _ ih =>
    simp only [labelOf, Label.isCorrupt] at ih
    exact ih.2
  | aeadEnc _ _ _ _ ihk _ ihm _ =>
    simp only [labelOf, Label.isCorrupt]
    exact ⟨ihk, ihm⟩
  | aeadDec _ _ _ ihct =>
    simp only [labelOf, Label.isCorrupt] at ihct
    exact ihct.2
  | pk _ =>
    simp [labelOf, Label.isCorrupt]
  | pkeEnc _ _ _ _ _ ihm =>
    simp only [labelOf]
    exact ihm
  | pkeDec _ _ _ ihct =>
    simp only [labelOf] at ihct
    exact ihct
  | vk _ =>
    simp [labelOf, Label.isCorrupt]
  | sign _ _ _ =>
    simp [labelOf, Label.isCorrupt]
  | hash _ =>
    simp [labelOf, Label.isCorrupt]
  | dhPub _ =>
    simp [labelOf, Label.isCorrupt]
  | dh _ _ ihsk _ =>
    simp only [labelOf]
    exact ihsk
  | kdfExtract _ _ ihs ihi =>
    simp only [labelOf, Label.isCorrupt]
    exact ⟨ihs, ihi⟩
  | kdfExpand _ _ _ ihprk _ =>
    simp only [labelOf]
    exact ihprk
  | kemPub _ =>
    simp [labelOf, Label.isCorrupt]
  | kemEncap _ _ _ ihss =>
    simp only [labelOf]
    exact ihss
  | kemDecap _ _ _ ihct =>
    simp only [labelOf] at ihct ⊢
    exact ihct
  | mac _ _ =>
    simp [labelOf, Label.isCorrupt]

end CatCrypt.Crypto.Symbolic
