/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Signal.Auth
public import CatCrypt.Crypto.Symbolic.Signal.ProtocolVerification

/-!
# Signal X3DH: the symbolic statements, conjoined

## Main result

* `signal_dual_security` — the event correspondence of
  `signal_x3dh_authentication` together with the trace invariant of the
  honest run `honestX3DH`.

## Scope

* The trace invariant is established for one trace, the output of
  `honestX3DH` from `.nil`. No theorem shows that a trace containing attacker
  sends, corruption or a second session satisfies it.
* The correspondence conjunct reads back `signalEventPred`, which requires a
  matching `X3DHInit` event or a corrupt initiator whenever an `X3DHResp`
  event is recorded. No signature or MAC check in a role program discharges
  that requirement.
* The model has no responder role. `honestX3DH` records Bob's `X3DHResp`
  event inside Alice's program, so no program of Bob is analysed.
* The file contains no secrecy statement for the X3DH root key.

The computational statement for X3DH is `x3dh_uc_secure` (`Signal/X3DH.lean`).

## References

* Signal Protocol specification: X3DH key agreement
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

/-- The two symbolic statements for X3DH, conjoined.

The first conjunct is `signal_x3dh_authentication`: on a trace satisfying
`signalInvariants`, an `X3DHResp` event at `i` is preceded by a matching
`X3DHInit` event unless the initiator is corrupt at `i`. It unpacks the
correspondence that `signalEventPred` postulates for `X3DHResp` events.

The second conjunct is `honestX3DH_invariant`: the single trace produced by
`honestX3DH` from `.nil` satisfies the invariant.

The statement takes no hypotheses: each conjunct is the statement of the
theorem that supplies it. -/
theorem signal_dual_security :
    /- Event correspondence -/
    (∀ (tr : Trace) (i : Nat) (bob alice : String) (rootKey : Bytes),
      @traceInvariant signalInvariants tr →
      tr.eventTriggeredAt i bob x3dhRespTag
        (mkX3DHContent bob alice rootKey) →
      (∃ j, j < i ∧ tr.eventTriggeredAt j alice x3dhInitTag
        (mkX3DHContent alice bob rootKey)) ∨
      tr.isCorruptAt alice i) ∧
    /- Invariant of the honest run -/
    (∀ (alice bob : String) (ikB spkB opkB : Bytes),
      @traceInvariant signalInvariants (honestX3DH alice bob ikB spkB opkB .nil).2) :=
  ⟨signal_x3dh_authentication, honestX3DH_invariant⟩

end CatCrypt.Crypto.Symbolic.Signal
