/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.MLS.Invariants
public import CatCrypt.Crypto.Symbolic.TracefulSpec
public import CatCrypt.Crypto.Symbolic.SigningDiscipline

/-!
# MLS Protocol Verification

Proves that the MLS commit operation maintains `traceInvariant`,
starting from the empty trace. This closes the verification gap where
`traceInvariant` was assumed rather than derived.

## Main results

* `mlsEventPredMono` — MLS invariants are monotone under snoc
* `honestSession_mls_invariant` — MLS honest session maintains invariant from `.nil`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## EventPredMono Instance -/

instance mlsEventPredMono : EventPredMono where
  toProtocolInvariants := mlsInvariants
  eventPred_mono_snoc := by
    intro tr e i hi prin tag content
    show mlsEventPred tr i prin tag content → mlsEventPred (.snoc tr e) i prin tag content
    unfold mlsEventPred
    split
    · -- commitVerifiedTag
      rintro ⟨committer, groupId, epoch, rootHash, hcontent, hauth⟩
      exact ⟨committer, groupId, epoch, rootHash, hcontent, hauth.elim
        (fun ⟨j, hji, hevent⟩ => .inl ⟨j, hji, by
          show (Trace.snoc tr e).entryAt j = _
          rw [Trace.entryAt_snoc_ne tr e j (by omega)]
          exact hevent⟩)
        (fun ⟨k, hki, hentry⟩ => .inr ⟨k, hki, by
          rw [Trace.entryAt_snoc_ne tr e k (by omega)]
          exact hentry⟩)⟩
    · exact id  -- remaining cases have no trace references
  statePred_mono_snoc := by
    intro tr e prin _ content
    show mlsStatePred tr prin _ content → mlsStatePred (.snoc tr e) prin _ content
    exact canFlow_labelOf_mono_snoc tr e _ content

/-! ## Honest MLS Session

Define the trace produced by composing committer and receiver roles
in an honest execution (no KEM loop, shared key by construction). -/

/-- Honest MLS session: committer creates a commit, receiver verifies.
Both sides use the committer-computed epoch key (justified by honest
execution where path secret is correctly transmitted). -/
def honestSession_mls (C R : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat)
    (rootHash : Bytes) : Traceful Bytes := do
  -- Committer: generate path secret and commit secret
  let pathSecret ← mkRand .nonce (groupLabel members) 32
  let commitSecret ← mkRand .nonce (principalLabel C) 32
  let epochKey := mlsKeySchedule pathSecret commitSecret (.literal "".toUTF8)
  -- Committer: trigger pathSecret event
  triggerEvent C pathSecretTag (mkPathSecretContent C pathSecret)
  -- Committer: sign and create commit
  let nonce ← mkRand .nonce (principalLabel C) 32
  let sig := Bytes.sign sigKey nonce rootHash
  -- Committer: trigger commit event
  triggerEvent C commitTag (mkCommitContent C groupId epoch rootHash)
  -- Committer: send commit message
  sendMsg (.concat sig rootHash)
  -- Committer: trigger epoch key event
  triggerEvent C epochKeyTag (mkEpochKeyContent C epochKey)
  -- Receiver: verify and process commit
  -- (In honest execution, signature verification succeeds; we directly
  -- trigger the corresponding events)
  triggerEvent R commitVerifiedTag
    (mkCommitVerifiedContent R C groupId epoch rootHash)
  -- Receiver: trigger group established
  triggerEvent R groupEstablishedTag
    (mkGroupContent R groupId epoch rootHash)
  -- Receiver: trigger epoch key event (using shared key)
  triggerEvent R epochKeyTag (mkEpochKeyContent R epochKey)
  return epochKey

abbrev Inv := @traceInvariant mlsInvariants

/-! ### Named Intermediate Traces -/

noncomputable def tr₀ : Trace := .nil

noncomputable def ePS (_C : String) (_members : List String) :=
  Bytes.rand .nonce 32 0
noncomputable def tr₁ (_C : String) (members : List String) : Trace :=
  .snoc tr₀ (.randGen .nonce (groupLabel members) 32)

noncomputable def eCS (C : String) (members : List String) :=
  Bytes.rand .nonce 32 (tr₁ C members).length
noncomputable def tr₂ (C : String) (members : List String) : Trace :=
  .snoc (tr₁ C members) (.randGen .nonce (principalLabel C) 32)

noncomputable def pathSecret (_C : String) (members : List String) :=
  ePS _C members
noncomputable def commitSecret (C : String) (members : List String) :=
  eCS C members
noncomputable def epochKey (C : String) (members : List String) :=
  mlsKeySchedule (pathSecret C members) (commitSecret C members) (.literal "".toUTF8)

noncomputable def tr₃ (C : String) (members : List String) : Trace :=
  .snoc (tr₂ C members) (.event C pathSecretTag
    (mkPathSecretContent C (pathSecret C members)))

noncomputable def eNonce (C : String) (members : List String) :=
  Bytes.rand .nonce 32 (tr₃ C members).length
noncomputable def tr₄ (C : String) (members : List String) : Trace :=
  .snoc (tr₃ C members) (.randGen .nonce (principalLabel C) 32)

noncomputable def sig (C : String) (members : List String)
    (sigKey : Bytes) (rootHash : Bytes) :=
  Bytes.sign sigKey (eNonce C members) rootHash

noncomputable def tr₅ (C : String) (members : List String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) : Trace :=
  .snoc (tr₄ C members) (.event C commitTag
    (mkCommitContent C groupId epoch rootHash))

noncomputable def tr₆ (C : String) (members : List String)
    (sigKey : Bytes) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) : Trace :=
  .snoc (tr₅ C members groupId epoch rootHash) (.msgSent
    (.concat (sig C members sigKey rootHash) rootHash))

noncomputable def tr₇ (C : String) (members : List String)
    (sigKey : Bytes) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) : Trace :=
  .snoc (tr₆ C members sigKey groupId epoch rootHash) (.event C epochKeyTag
    (mkEpochKeyContent C (epochKey C members)))

noncomputable def tr₈ (C R : String) (members : List String)
    (sigKey : Bytes) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) : Trace :=
  .snoc (tr₇ C members sigKey groupId epoch rootHash) (.event R commitVerifiedTag
    (mkCommitVerifiedContent R C groupId epoch rootHash))

noncomputable def tr₉ (C R : String) (members : List String)
    (sigKey : Bytes) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) : Trace :=
  .snoc (tr₈ C R members sigKey groupId epoch rootHash) (.event R groupEstablishedTag
    (mkGroupContent R groupId epoch rootHash))

noncomputable def tr₁₀ (C R : String) (members : List String)
    (sigKey : Bytes) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) : Trace :=
  .snoc (tr₉ C R members sigKey groupId epoch rootHash) (.event R epochKeyTag
    (mkEpochKeyContent R (epochKey C members)))

/-- The output of `honestSession_mls` is `tr₁₀`. -/
theorem honestSession_mls_eq (C R : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) :
    (honestSession_mls C R sigKey members groupId epoch rootHash .nil).2 =
    tr₁₀ C R members sigKey groupId epoch rootHash := by
  unfold honestSession_mls tr₁₀ tr₉ tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀
  unfold epochKey commitSecret pathSecret sig eNonce eCS ePS
  simp only [bind, instMonadTraceful, mkRand, triggerEvent, sendMsg,
    Trace.length_nil, Trace.length_snoc]
  rfl

/-- The honest MLS session maintains trace invariant from the empty trace.

**No `traceInvariant` hypothesis** — derived from `traceInvariant .nil`. -/
theorem honestSession_mls_invariant (C R : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes)
    (hPubRH : ∀ tr : Trace, bytesPublishable tr rootHash) :
    Inv (honestSession_mls C R sigKey members groupId epoch rootHash .nil).2 := by
  rw [honestSession_mls_eq]
  unfold tr₁₀
  -- Chain of intermediate invariants
  have hInv₀ : Inv tr₀ := traceInvariant_nil
  have hInv₁ : Inv (tr₁ C members) := traceInvariant_randGen hInv₀ (Or.inl rfl)
  have hInv₂ : Inv (tr₂ C members) := traceInvariant_randGen hInv₁ (Or.inl rfl)
  have hInv₃ : Inv (tr₃ C members) := by
    unfold tr₃; apply traceInvariant_event hInv₂
    show mlsEventPred _ _ _ _ _; unfold mlsEventPred
    simp [pathSecretTag, commitVerifiedTag, groupEstablishedTag, commitTag]
    exact ⟨_, rfl⟩
  have hInv₄ : Inv (tr₄ C members) := traceInvariant_randGen hInv₃ (Or.inl rfl)
  have hInv₅ : Inv (tr₅ C members groupId epoch rootHash) := by
    unfold tr₅; apply traceInvariant_event hInv₄
    show mlsEventPred _ _ _ _ _; unfold mlsEventPred
    simp [commitTag, commitVerifiedTag, groupEstablishedTag]
    exact ⟨_, _, _, rfl⟩
  have hInv₆ : Inv (tr₆ C members sigKey groupId epoch rootHash) := by
    unfold tr₆; apply traceInvariant_sendMsg hInv₅
    unfold sig
    simp only [bytesPublishable, labelOf, Label.isCorrupt]
    exact ⟨trivial, hPubRH _⟩
  have hInv₇ : Inv (tr₇ C members sigKey groupId epoch rootHash) := by
    unfold tr₇; apply traceInvariant_event hInv₆
    show mlsEventPred _ _ _ _ _; unfold mlsEventPred
    simp [epochKeyTag, commitVerifiedTag, groupEstablishedTag, commitTag, pathSecretTag]
    exact ⟨_, rfl⟩
  have hInv₈ : Inv (tr₈ C R members sigKey groupId epoch rootHash) := by
    unfold tr₈; apply traceInvariant_event hInv₇
    show mlsEventPred _ _ _ _ _; unfold mlsEventPred
    simp only [commitVerifiedTag, BEq.beq]
    -- Need: ∃ committer groupId epoch rootHash, content = ... ∧ (∃ j < i, Commit at j ∨ corrupt)
    refine ⟨C, groupId, epoch, rootHash, rfl, .inl ⟨(tr₄ C members).length, ?_, ?_⟩⟩
    · unfold tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀; simp [Trace.length]
    · -- Commit event at position tr₄.length
      show (Trace.snoc (tr₇ C members sigKey groupId epoch rootHash) _).entryAt
        (tr₄ C members).length = _
      unfold tr₇ tr₆ tr₅
      simp [Trace.entryAt, Trace.length, tr₄, tr₃, tr₂, tr₁, tr₀]
  have hInv₉ : Inv (tr₉ C R members sigKey groupId epoch rootHash) := by
    unfold tr₉; apply traceInvariant_event hInv₈
    show mlsEventPred _ _ _ _ _; unfold mlsEventPred
    split
    · exfalso; unfold commitVerifiedTag groupEstablishedTag at *; simp_all
    · simp only [groupEstablishedTag, BEq.beq]
      exact ⟨_, _, _, rfl⟩
  -- Final step: receiver epoch key event
  apply traceInvariant_event hInv₉
  show mlsEventPred _ _ _ _ _; unfold mlsEventPred
  split
  · exfalso; unfold commitVerifiedTag epochKeyTag at *; simp_all
  · split
    · exfalso; unfold groupEstablishedTag epochKeyTag at *; simp_all
    · split
      · exfalso; unfold commitTag epochKeyTag at *; simp_all
      · split
        · exfalso; unfold pathSecretTag epochKeyTag at *; simp_all
        · simp only [epochKeyTag, BEq.beq]
          exact ⟨_, rfl⟩

/-- The honest MLS session triggers a `Commit` event. -/
theorem honestSession_mls_commit (C R : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) :
    ∃ j, (honestSession_mls C R sigKey members groupId epoch rootHash .nil).2.eventTriggeredAt
      j C commitTag (mkCommitContent C groupId epoch rootHash) := by
  rw [honestSession_mls_eq]
  exact ⟨(tr₄ C members).length, by
    unfold tr₁₀ tr₉ tr₈ tr₇ tr₆ tr₅ Trace.eventTriggeredAt
    simp [Trace.entryAt, Trace.length, tr₄, tr₃, tr₂, tr₁, tr₀]⟩

/-- The honest MLS session triggers a `CommitVerified` event. -/
theorem honestSession_mls_commitVerified (C R : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) :
    ∃ j, (honestSession_mls C R sigKey members groupId epoch rootHash .nil).2.eventTriggeredAt
      j R commitVerifiedTag
      (mkCommitVerifiedContent R C groupId epoch rootHash) := by
  rw [honestSession_mls_eq]
  exact ⟨(tr₇ C members sigKey groupId epoch rootHash).length, by
    unfold tr₁₀ tr₉ tr₈ Trace.eventTriggeredAt
    simp [Trace.entryAt, Trace.length, tr₇, tr₆, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]⟩

/-- The honest MLS session triggers a `GroupEstablished` event. -/
theorem honestSession_mls_groupEstablished (C R : String) (sigKey : Bytes)
    (members : List String) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) :
    ∃ j, (honestSession_mls C R sigKey members groupId epoch rootHash .nil).2.eventTriggeredAt
      j R groupEstablishedTag
      (mkGroupContent R groupId epoch rootHash) := by
  rw [honestSession_mls_eq]
  exact ⟨(tr₈ C R members sigKey groupId epoch rootHash).length, by
    unfold tr₁₀ tr₉ Trace.eventTriggeredAt
    simp [Trace.entryAt, Trace.length, tr₈, tr₇, tr₆, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]⟩

end CatCrypt.Crypto.Symbolic.MLS
