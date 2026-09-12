/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.Defs
public import CatCrypt.Crypto.Symbolic.Signal.Invariants

/-!
# Signal X3DH Authentication

Theorem: If Bob triggers an `X3DHResp` event, then either Alice triggered
a matching `X3DHInit` event, or Alice is corrupted.

## Main result

* `signal_x3dh_authentication` — X3DH responder authentication

## Proof

Follows the same pattern as `tls13_server_authentication`:
1. Extract the event entry from the trace
2. The trace invariant at the event position gives `signalEventPred`
3. Unfold to get the correspondence property directly

## References

* DY* Signal: X3DH authentication (Bhargavan et al.)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

theorem String.toUTF8_injective : Function.Injective String.toUTF8 := by
  intro ⟨b1, h1⟩ ⟨b2, h2⟩ (h : b1 = b2)
  cases h; rfl

/-- **X3DH Authentication**: If Bob completes X3DH (triggers `X3DHResp`),
then Alice initiated it (triggered `X3DHInit` with matching key), or
Alice is corrupted. -/
theorem signal_x3dh_authentication
    (tr : Trace) (i : Nat) (bob alice : String) (rootKey : Bytes) :
    @traceInvariant signalInvariants tr →
    tr.eventTriggeredAt i bob x3dhRespTag
      (mkX3DHContent bob alice rootKey) →
    (∃ j, j < i ∧ tr.eventTriggeredAt j alice x3dhInitTag
      (mkX3DHContent alice bob rootKey)) ∨
    tr.isCorruptAt alice i := by
  intro hInv hEvent
  have hi := Trace.entryAt_lt_length hEvent
  have hPred := hInv i hi _ hEvent
  change signalEventPred tr i bob x3dhRespTag (mkX3DHContent bob alice rootKey) at hPred
  unfold signalEventPred at hPred
  simp only [beq_self_eq_true, ↓reduceIte] at hPred
  obtain ⟨peer, rootKey', hcontent, hauth⟩ := hPred
  simp only [mkX3DHContent, Bytes.concat.injEq, Bytes.literal.injEq] at hcontent
  obtain ⟨_, hpeer_key⟩ := hcontent
  obtain ⟨hpeer, hrk⟩ := hpeer_key
  have hpeer' : peer = alice := String.toUTF8_injective hpeer.symm
  subst hpeer'; subst hrk
  exact hauth

end CatCrypt.Crypto.Symbolic.Signal
