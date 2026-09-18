/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.Defs
public import CatCrypt.Crypto.Symbolic.Signal.Invariants

/-!
# Signal X3DH: the X3DHResp / X3DHInit event correspondence

On a trace satisfying `signalInvariants`, an `X3DHResp` event is preceded by a
matching `X3DHInit` event unless the initiator is corrupt.

## Main result

* `signal_x3dh_authentication` — the correspondence, read back from
  `signalEventPred`

## Proof

Follows the same pattern as `tls13_server_authentication`:
1. Extract the event entry from the trace
2. The trace invariant at the event position gives `signalEventPred`
3. Unfold to get the correspondence property directly

## Scope

* The correspondence is postulated by `signalEventPred`. No signature or MAC
  predicate enters the proof.
* `traceInvariant` for `signalInvariants` is established only for the single
  honest trace `tr₅` (`honestX3DH_invariant`).
* The model has no responder role: `honestX3DH` records the `X3DHResp` event
  in Bob's name inside Alice's program. The theorem is therefore not a
  property of any responder program.

## References

* DY* Signal: X3DH authentication (Bhargavan et al.)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

theorem String.toUTF8_injective : Function.Injective String.toUTF8 := by
  intro ⟨b1, h1⟩ ⟨b2, h2⟩ (h : b1 = b2)
  cases h; rfl

/-- On a trace satisfying the invariant, an `X3DHResp` event at `i` is preceded
by an `X3DHInit` event with the same root key, or the initiator is corrupt at
`i`.

The conclusion is the clause of `signalEventPred` for `X3DHResp` events, which
the invariant hypothesis supplies. The invariant is established only for the
honest trace `tr₅`, in which the `X3DHResp` event is recorded by Alice's
program. -/
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
