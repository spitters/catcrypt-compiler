/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Signal.Invariants
public import CatCrypt.Crypto.Symbolic.TracefulSpec
public import CatCrypt.Crypto.Symbolic.SigningDiscipline

/-!
# Signal Protocol Verification

Proves that `honestX3DH` maintains `traceInvariant` from the empty trace,
and establishes the `EventPredMono` instance for Signal.

## Main results

* `signalEventPredMono` — Signal invariants are monotone under snoc
* `honestX3DH_invariant` — honest X3DH session maintains invariant from `.nil`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

/-! ## EventPredMono Instance -/

instance signalEventPredMono : EventPredMono where
  toProtocolInvariants := signalInvariants
  eventPred_mono_snoc := by
    intro tr e i hi prin tag content
    show signalEventPred tr i prin tag content →
      signalEventPred (.snoc tr e) i prin tag content
    unfold signalEventPred
    split
    · rintro ⟨peer, rootKey, hcontent, hauth⟩
      exact ⟨peer, rootKey, hcontent, hauth.elim
        (fun ⟨j, hji, hevent⟩ => .inl ⟨j, hji, by
          show (Trace.snoc tr e).entryAt j = _
          rw [Trace.entryAt_snoc_ne tr e j (by omega)]
          exact hevent⟩)
        (fun ⟨k, hki, hentry⟩ => .inr ⟨k, hki, by
          rw [Trace.entryAt_snoc_ne tr e k (by omega)]
          exact hentry⟩)⟩
    · split <;> exact id
  statePred_mono_snoc := by
    intro tr e prin _ content
    show signalStatePred tr prin _ content →
      signalStatePred (.snoc tr e) prin _ content
    exact canFlow_labelOf_mono_snoc tr e _ content

/-! ## Honest Session: Step-by-Step Trace Construction -/

abbrev Inv := @traceInvariant signalInvariants

-- Named intermediate traces
noncomputable def tr₀ : Trace := .nil

noncomputable def ek (alice : String) := Bytes.rand .dhKey 32 0

noncomputable def tr₁ (alice : String) : Trace :=
  .snoc tr₀ (.randGen .dhKey (principalLabel alice) 32)

noncomputable def ikA (alice : String) := Bytes.rand .dhKey 32 (tr₁ alice).length

noncomputable def tr₂ (alice : String) : Trace :=
  .snoc (tr₁ alice) (.randGen .dhKey (principalLabel alice) 32)

noncomputable def rootKey_val (alice : String) (ikB spkB opkB : Bytes) :=
  signalKeySchedule
    (Bytes.dh (ikA alice) (Bytes.dhPub spkB))
    (Bytes.dh (ek alice) (Bytes.dhPub ikB))
    (Bytes.dh (ek alice) (Bytes.dhPub spkB))
    (Bytes.dh (ek alice) (Bytes.dhPub opkB))

noncomputable def initContent (alice bob : String) (ikB spkB opkB : Bytes) :=
  mkX3DHContent alice bob (rootKey_val alice ikB spkB opkB)

noncomputable def tr₃ (alice bob : String) (ikB spkB opkB : Bytes) : Trace :=
  .snoc (tr₂ alice) (.event alice x3dhInitTag (initContent alice bob ikB spkB opkB))

noncomputable def tr₄ (alice bob : String) (ikB spkB opkB : Bytes) : Trace :=
  .snoc (tr₃ alice bob ikB spkB opkB) (.msgSent (.concat (Bytes.dhPub (ek alice)) (Bytes.dhPub (ikA alice))))

noncomputable def respContent (alice bob : String) (ikB spkB opkB : Bytes) :=
  mkX3DHContent bob alice (rootKey_val alice ikB spkB opkB)

noncomputable def tr₅ (alice bob : String) (ikB spkB opkB : Bytes) : Trace :=
  .snoc (tr₄ alice bob ikB spkB opkB) (.event bob x3dhRespTag (respContent alice bob ikB spkB opkB))

/-- The output of `honestX3DH` is `tr₅`. -/
theorem honestX3DH_eq (alice bob : String) (ikB spkB opkB : Bytes) :
    (honestX3DH alice bob ikB spkB opkB .nil).2 =
      tr₅ alice bob ikB spkB opkB := by
  unfold honestX3DH tr₅ tr₄ tr₃ tr₂ tr₁ tr₀
  unfold respContent initContent rootKey_val ikA ek
  simp only [bind, instMonadTraceful, mkRand, triggerEvent, sendMsg,
    Trace.length_nil, Trace.length_snoc]
  rfl

/-- The honest Signal X3DH session maintains trace invariant from the empty trace.

**No `traceInvariant` hypothesis** — derived from `traceInvariant .nil`. -/
theorem honestX3DH_invariant (alice bob : String) (ikB spkB opkB : Bytes) :
    Inv (honestX3DH alice bob ikB spkB opkB .nil).2 := by
  rw [honestX3DH_eq]
  unfold tr₅
  -- Chain invariants
  have hInv₀ : Inv tr₀ := traceInvariant_nil
  have hInv₁ : Inv (tr₁ alice) :=
    Signal.traceInvariant_randGen hInv₀ (Or.inl rfl)
  have hInv₂ : Inv (tr₂ alice) :=
    Signal.traceInvariant_randGen hInv₁ (Or.inl rfl)
  have hInv₃ : Inv (tr₃ alice bob ikB spkB opkB) := by
    unfold tr₃
    apply Signal.traceInvariant_event hInv₂
    show signalEventPred _ _ _ _ _
    unfold signalEventPred
    simp [x3dhInitTag, x3dhRespTag]
    exact ⟨bob, _, rfl⟩
  have hInv₄ : Inv (tr₄ alice bob ikB spkB opkB) := by
    unfold tr₄
    apply Signal.traceInvariant_sendMsg hInv₃
    simp [bytesPublishable, labelOf, Label.isCorrupt]
  -- X3DHResp event: needs matching X3DHInit event
  apply Signal.traceInvariant_event hInv₄
  show signalEventPred _ _ _ _ _
  unfold signalEventPred
  simp only [x3dhRespTag, BEq.beq]
  refine ⟨alice, _, rfl, .inl ⟨(tr₂ alice).length, ?_, ?_⟩⟩
  · -- (tr₂ alice).length < (tr₄ ...).length
    unfold tr₄ tr₃ tr₂ tr₁ tr₀
    simp [Trace.length]
  · -- eventTriggeredAt at position (tr₂ alice).length
    show (Trace.snoc (tr₄ alice bob ikB spkB opkB)
        (.event bob x3dhRespTag (respContent alice bob ikB spkB opkB))).entryAt
      (tr₂ alice).length =
      some (.event alice x3dhInitTag (initContent alice bob ikB spkB opkB))
    unfold tr₄ tr₃
    simp [Trace.entryAt, Trace.length, tr₂, tr₁, tr₀]

/-- The honest X3DH session triggers an `X3DHInit` event. -/
theorem honestX3DH_initEvent (alice bob : String) (ikB spkB opkB : Bytes) :
    ∃ j, (honestX3DH alice bob ikB spkB opkB .nil).2.eventTriggeredAt
      j alice x3dhInitTag (initContent alice bob ikB spkB opkB) := by
  rw [honestX3DH_eq]
  exact ⟨(tr₂ alice).length, by
    unfold tr₅ tr₄ tr₃ Trace.eventTriggeredAt
    simp [Trace.entryAt, Trace.length, tr₂, tr₁, tr₀]⟩

/-- The honest X3DH session triggers an `X3DHResp` event. -/
theorem honestX3DH_respEvent (alice bob : String) (ikB spkB opkB : Bytes) :
    ∃ j, (honestX3DH alice bob ikB spkB opkB .nil).2.eventTriggeredAt
      j bob x3dhRespTag (respContent alice bob ikB spkB opkB) := by
  rw [honestX3DH_eq]
  exact ⟨(tr₄ alice bob ikB spkB opkB).length, by
    unfold tr₅ Trace.eventTriggeredAt
    rfl⟩

end CatCrypt.Crypto.Symbolic.Signal
