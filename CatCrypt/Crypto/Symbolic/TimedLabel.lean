/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Attacker

/-!
# Time-Indexed Corruption Labels

Extends the label system with corruption timestamps. Instead of tracking
only WHICH principals must be corrupted (as `Label` does), `TimedLabel`
also tracks WHEN the associated cryptographic material was generated.

## Motivation

The standard `labelOf` + `attacker_only_knows_publishable` chain gives us
`corruptSet I`, meaning "I is corrupted at SOME point in the trace". For
forward secrecy, we need "I is corrupted at or before `sessionTime`". The
standard approach uses `hNoLateCorrupt` to bridge this gap, but
`TimedLabel` eliminates this hypothesis by carrying timestamps directly.

## Main definitions

* `TimedLabel` — corruption labels with generation-time annotations
* `Label.toTimedLabel` — map untimed labels to timed labels at a given time
* `timedLabelOf` — time-aware structural label assignment
* `TimedLabel.isCorrupt` — corruption semantics with temporal bounds
* `timedPublishable_implies_publishable` — bridge: timed ⟹ untimed
* `attacker_only_knows_timed_publishable` — the main theorem

## Design

For ephemeral DH keys generated at time `t`, corruption after `t` doesn't
help the attacker derive them. The timed label captures this directly:

- `TimedLabel.principalAt p t` means "requires corruption of `p` at or
  before time `t`"
- `TimedLabel.meet l₁ l₂` requires BOTH components to be corrupt
- `kdfExtract`: meet of timed labels (same as untimed)
- `kdfExpand`: inherits timed label of PRK
- `dh sk _`: inherits timed label of sk

## Correctness

The timed-label bridge axioms that previously connected `labelOf` to
`timedLabelOf` have been replaced by explicit hypotheses in the main
theorem. This makes the trust boundary explicit: the caller must show
that (1) sent messages are timed-publishable, and (2) corrupted state
is timed-publishable for the specific trace under consideration.

For honest protocol executions (TLS, EDHOC), sent messages have `.top`
timed labels (they consist of public values: DH public keys, signatures,
MACs), so hypothesis (1) is trivially satisfied. Hypothesis (2) requires
that corruption happens before key generation, which is a genuine forward
secrecy assumption about the trace.

## References

* Backes, Pfitzmann, Waidner: BPW model with corruption phases
* DY*-extrinsic: time-indexed labels (future work direction)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-! ## TimedLabel Type -/

/-- Corruption labels with generation-time annotations.

Like `Label`, but `principalAt p t` carries the trace position `t`
at which the protected value was generated. Corruption of `p`
must occur at or before `t` for the label to be considered corrupt. -/
inductive TimedLabel where
  /-- Bottom: never corrupt -/
  | bot : TimedLabel
  /-- Top: always known to the attacker -/
  | top : TimedLabel
  /-- Requires corruption of principal `p` at or before time `t` -/
  | principalAt : (p : String) → (time : Nat) → TimedLabel
  /-- Requires BOTH components corrupt -/
  | meet : TimedLabel → TimedLabel → TimedLabel
  /-- Requires EITHER component corrupt -/
  | join : TimedLabel → TimedLabel → TimedLabel
  deriving Inhabited

/-! ## Corruption Semantics -/

/-- Whether a timed label is corrupt given a trace.

Unlike `Label.isCorrupt` which uses a corruption *set*, this uses
`isCorruptAt` which checks both the principal AND the time. -/
def TimedLabel.isCorrupt (tr : Trace) : TimedLabel → Prop
  | .bot => False
  | .top => True
  | .principalAt p t => tr.isCorruptAt p t
  | .meet l₁ l₂ => l₁.isCorrupt tr ∧ l₂.isCorrupt tr
  | .join l₁ l₂ => l₁.isCorrupt tr ∨ l₂.isCorrupt tr

/-- Corruption is monotone: if `grows tr₁ tr₂` and a timed label is corrupt
in `tr₁`, it remains corrupt in `tr₂`. -/
theorem TimedLabel.isCorrupt_mono {tr₁ tr₂ : Trace}
    (hGrows : ∀ i p, tr₁.isCorruptAt p i → tr₂.isCorruptAt p i) :
    ∀ l : TimedLabel, l.isCorrupt tr₁ → l.isCorrupt tr₂ := by
  intro l
  induction l with
  | bot => exact id
  | top => exact id
  | principalAt p t => exact hGrows t p
  | meet _ _ ih₁ ih₂ => exact fun ⟨h₁, h₂⟩ => ⟨ih₁ h₁, ih₂ h₂⟩
  | join _ _ ih₁ ih₂ =>
    exact fun h => h.elim (fun h₁ => .inl (ih₁ h₁)) (fun h₂ => .inr (ih₂ h₂))

/-! ## Label to TimedLabel Mapping -/

/-- Map an untimed `Label` to a `TimedLabel` at a given generation time.

This is the canonical embedding: `principal p` becomes `principalAt p time`,
and compound labels are mapped structurally. -/
def Label.toTimedLabel (time : Nat) : Label → TimedLabel
  | .bot => .bot
  | .top => .top
  | .principal p => .principalAt p time
  | .meet l₁ l₂ => .meet (l₁.toTimedLabel time) (l₂.toTimedLabel time)
  | .join l₁ l₂ => .join (l₁.toTimedLabel time) (l₂.toTimedLabel time)

/-- Key bridge: if a timed label (from `toTimedLabel`) is corrupt, then
the original untimed label is corrupt under the trace's corruption set.

This holds because `isCorruptAt p t` implies `corruptSet p` whenever
`t` is a valid trace position (i.e., `t < tr.length`). -/
theorem Label.toTimedLabel_isCorrupt_implies (l : Label) (time : Nat) (tr : Trace)
    (hTime : time < tr.length) :
    (l.toTimedLabel time).isCorrupt tr → l.isCorrupt tr.corruptSet := by
  induction l with
  | bot => exact id
  | top => exact fun _ => trivial
  | principal p =>
    intro h
    show tr.corruptSet p
    obtain ⟨j, hj, hentry⟩ := h
    exact ⟨j, by omega, hentry⟩
  | meet _ _ ih₁ ih₂ =>
    intro ⟨h₁, h₂⟩
    exact ⟨ih₁ h₁, ih₂ h₂⟩
  | join _ _ ih₁ ih₂ =>
    intro h
    exact h.elim (fun h₁ => .inl (ih₁ h₁)) (fun h₂ => .inr (ih₂ h₂))

/-! ## Time-Aware Label Assignment -/

/-- Assign a timed corruption label to a bytes term.

The key difference from `labelOf`:
- `rand usage len time` uses `Label.toTimedLabel time` to map the label
  from the trace entry, embedding the generation time. This means
  `principal p` becomes `principalAt p time`, requiring corruption
  of `p` at or before `time`.
- For all other constructors, the structure mirrors `labelOf`.

Note: Unlike the previous version, this correctly handles all label
types (including `.bot` and compound labels) through `Label.toTimedLabel`. -/
def timedLabelOf (tr : Trace) : Bytes → TimedLabel
  | .literal _ => .top
  | .rand _ _ time =>
    match tr.randLabelAt time with
    | some l => l.toTimedLabel time
    | none => .bot
  | .concat b₁ b₂ => .meet (timedLabelOf tr b₁) (timedLabelOf tr b₂)
  | .aeadEnc key _nonce msg _ad => .meet (timedLabelOf tr key) (timedLabelOf tr msg)
  | .pk _ => .top
  | .pkeEnc _ _ msg => timedLabelOf tr msg
  | .vk _ => .top
  | .sign _ _ _ => .top
  | .hash _ => .top
  | .dhPub _ => .top
  | .dh sk _ => timedLabelOf tr sk
  | .kdfExtract salt ikm => .meet (timedLabelOf tr salt) (timedLabelOf tr ikm)
  | .kdfExpand prk _ _ => timedLabelOf tr prk
  | .kemPub _ => .top
  | .kemEncap _ ss => timedLabelOf tr ss
  | .kemSecretShared ss => timedLabelOf tr ss
  | .mac _ _ => .top

/-- A bytes value is timed-publishable if its timed label is corrupt. -/
def bytesTimedPublishable (tr : Trace) (b : Bytes) : Prop :=
  (timedLabelOf tr b).isCorrupt tr

/-! ## Bridge: Timed Publishability ⟹ Publishability

The timed version is strictly stronger than the untimed version: if a value
is timed-publishable, it is also (untimed-)publishable. This holds because
`isCorruptAt p t → corruptSet p` for valid trace positions. -/

/-- Helper: `randLabelAt` returning `some` implies the position is valid. -/
theorem Trace.randLabelAt_lt_length {tr : Trace} {time : Nat} {l : Label}
    (h : tr.randLabelAt time = some l) : time < tr.length := by
  unfold Trace.randLabelAt at h
  split at h <;> simp at h
  rename_i e he
  exact Trace.entryAt_lt_length he

/-- **Bridge lemma**: Timed publishability implies untimed publishability.

For every `Bytes` constructor, `timedLabelOf` and `labelOf` have the same
structure, differing only at `rand` where the label is mapped through
`Label.toTimedLabel`. Since `toTimedLabel_isCorrupt_implies` bridges the
timed corruption to untimed corruption, the result follows by structural
induction on `b`. -/
theorem timedPublishable_implies_publishable {tr : Trace} {b : Bytes} :
    bytesTimedPublishable tr b → bytesPublishable tr b := by
  unfold bytesTimedPublishable bytesPublishable
  induction b with
  | literal _ => exact fun _ => trivial
  | rand _usage _len time =>
    intro h
    show (labelOf tr (Bytes.rand _usage _len time)).isCorrupt tr.corruptSet
    simp only [labelOf, timedLabelOf] at h ⊢
    cases hrl : tr.randLabelAt time with
    | none =>
      rw [hrl] at h; exact absurd h id
    | some l =>
      rw [hrl] at h
      simp only [Option.getD]
      exact Label.toTimedLabel_isCorrupt_implies l time tr
        (Trace.randLabelAt_lt_length hrl) h
  | concat _ _ ih₁ ih₂ =>
    simp only [timedLabelOf, TimedLabel.isCorrupt, labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ih₁ h₁, ih₂ h₂⟩
  | aeadEnc _ _ _ _ ihk _ ihm _ =>
    simp only [timedLabelOf, TimedLabel.isCorrupt, labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ihk h₁, ihm h₂⟩
  | pk _ => exact fun _ => trivial
  | pkeEnc _ _ _ _ _ ihm => exact ihm
  | vk _ => exact fun _ => trivial
  | sign _ _ _ => exact fun _ => trivial
  | hash _ => exact fun _ => trivial
  | dhPub _ => exact fun _ => trivial
  | dh _ _ ihsk _ =>
    simp only [timedLabelOf, labelOf]; exact ihsk
  | kdfExtract _ _ ihs ihi =>
    simp only [timedLabelOf, TimedLabel.isCorrupt, labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ihs h₁, ihi h₂⟩
  | kdfExpand _ _ _ ihprk _ =>
    simp only [timedLabelOf, labelOf]; exact ihprk
  | kemPub _ => exact fun _ => trivial
  | kemEncap _ _ _ ihss =>
    simp only [timedLabelOf, labelOf]; exact ihss
  | kemSecretShared _ ihss =>
    simp only [timedLabelOf, labelOf]; exact ihss
  | mac _ _ => exact fun _ => trivial

/-! ## Helper Lemmas for Protocol Messages

These lemmas show that common protocol message constructors (DH public keys,
signatures, MACs, hashes) have `.top` timed labels, making them trivially
timed-publishable. -/

theorem bytesTimedPublishable_top {tr : Trace} {b : Bytes}
    (h : timedLabelOf tr b = .top) : bytesTimedPublishable tr b := by
  unfold bytesTimedPublishable; rw [h]; exact trivial

@[simp] theorem timedLabelOf_literal (tr : Trace) (bs : ByteArray) :
    timedLabelOf tr (.literal bs) = .top := rfl
@[simp] theorem timedLabelOf_pk (tr : Trace) (sk : Bytes) :
    timedLabelOf tr (.pk sk) = .top := rfl
@[simp] theorem timedLabelOf_vk (tr : Trace) (sk : Bytes) :
    timedLabelOf tr (.vk sk) = .top := rfl
@[simp] theorem timedLabelOf_sign (tr : Trace) (sk nonce msg : Bytes) :
    timedLabelOf tr (.sign sk nonce msg) = .top := rfl
@[simp] theorem timedLabelOf_hash (tr : Trace) (msg : Bytes) :
    timedLabelOf tr (.hash msg) = .top := rfl
@[simp] theorem timedLabelOf_dhPub (tr : Trace) (sk : Bytes) :
    timedLabelOf tr (.dhPub sk) = .top := rfl
@[simp] theorem timedLabelOf_kemPub (tr : Trace) (sk : Bytes) :
    timedLabelOf tr (.kemPub sk) = .top := rfl
@[simp] theorem timedLabelOf_mac (tr : Trace) (key msg : Bytes) :
    timedLabelOf tr (.mac key msg) = .top := rfl

/-- A `concat` of two timed-publishable values is timed-publishable. -/
theorem bytesTimedPublishable_concat {tr : Trace} {b₁ b₂ : Bytes}
    (h₁ : bytesTimedPublishable tr b₁) (h₂ : bytesTimedPublishable tr b₂) :
    bytesTimedPublishable tr (.concat b₁ b₂) :=
  ⟨h₁, h₂⟩

/-! ## Main Theorem -/

/-- **Main theorem**: The DY attacker can only derive timed-publishable values.

This is the timed analogue of `attacker_only_knows_publishable`. The proof
follows the same 21-case induction on `AttackerKnows`, but tracks
generation times through the timed label assignment.

The `network` and `corruptState` cases are handled by explicit hypotheses
rather than axioms. This makes the trust boundary clear:

* `hNetworkTimed`: sent messages must be timed-publishable. For honest
  protocol executions (TLS, EDHOC), this holds trivially because sent
  messages consist of public values (DH public keys, signatures, MACs).

* `hCorruptStateTimed`: corrupted state must be timed-publishable. This
  captures the forward secrecy assumption: corruption must have happened
  before the protected material was generated. -/
theorem attacker_only_knows_timed_publishable [ProtocolInvariants]
    {tr : Trace} {msg : Bytes}
    (_hInv : traceInvariant tr)
    (hNetworkTimed : ∀ msg' i,
      tr.entryAt i = some (.msgSent msg') →
      bytesTimedPublishable tr msg')
    (hCorruptStateTimed : ∀ (prin : String) (sessId : Nat) (content : Bytes) (i j : Nat),
      tr.entryAt i = some (.corrupt prin) →
      tr.entryAt j = some (.setState prin sessId content) →
      bytesTimedPublishable tr content)
    (hKnows : AttackerKnows tr msg) :
    bytesTimedPublishable tr msg := by
  unfold bytesTimedPublishable
  induction hKnows with
  | network hEntry =>
    exact hNetworkTimed _ _ hEntry
  | corruptState hCorrupt hState =>
    exact hCorruptStateTimed _ _ _ _ _ hCorrupt hState
  | literal _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]
  | concat _ _ ih₁ ih₂ =>
    simp only [timedLabelOf, TimedLabel.isCorrupt]
    exact ⟨ih₁, ih₂⟩
  | splitL _ ih =>
    simp only [timedLabelOf, TimedLabel.isCorrupt] at ih
    exact ih.1
  | splitR _ ih =>
    simp only [timedLabelOf, TimedLabel.isCorrupt] at ih
    exact ih.2
  | aeadEnc _ _ _ _ ihk _ ihm _ =>
    simp only [timedLabelOf, TimedLabel.isCorrupt]
    exact ⟨ihk, ihm⟩
  | aeadDec _ _ _ ihct =>
    simp only [timedLabelOf, TimedLabel.isCorrupt] at ihct
    exact ihct.2
  | pk _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]
  | pkeEnc _ _ _ _ _ ihm =>
    simp only [timedLabelOf]; exact ihm
  | pkeDec _ _ _ ihct =>
    simp only [timedLabelOf] at ihct; exact ihct
  | vk _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]
  | sign _ _ _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]
  | hash _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]
  | dhPub _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]
  | dh _ _ ihsk _ =>
    simp only [timedLabelOf]; exact ihsk
  | kdfExtract _ _ ihs ihi =>
    simp only [timedLabelOf, TimedLabel.isCorrupt]
    exact ⟨ihs, ihi⟩
  | kdfExpand _ _ _ ihprk _ =>
    simp only [timedLabelOf]; exact ihprk
  | kemPub _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]
  | kemEncap _ _ _ ihss =>
    simp only [timedLabelOf]; exact ihss
  | kemDecap _ _ _ ihct =>
    simp only [timedLabelOf] at ihct ⊢; exact ihct
  | mac _ _ =>
    simp [timedLabelOf, TimedLabel.isCorrupt]

end CatCrypt.Crypto.Symbolic
