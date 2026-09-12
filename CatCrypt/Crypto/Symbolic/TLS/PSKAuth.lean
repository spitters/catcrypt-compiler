/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TLS.Invariants

/-!
# TLS 1.3 PSK Authentication

Proves that PSK resumption sessions satisfy authentication: every
`PSKClientFinished` event implies a matching `PSKServerFinished` event
(or the server is corrupted).

## Main Results

* `tls13_psk_authentication` — PSK client finished ⟹ server finished ∨ corrupt
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-- **PSK Authentication**: For any trace satisfying the TLS invariant,
    if a `PSKClientFinished` event occurs, then either a matching
    `PSKServerFinished` event occurred earlier, or the server is corrupted. -/
theorem tls13_psk_authentication
    (tr : Trace) (i : Nat) (client server : String) (appKey : Bytes) :
    @traceInvariant tlsInvariants tr →
    tr.eventTriggeredAt i client pskClientFinishedTag
      (mkPSKFinishedContent client server appKey) →
    (∃ j, j < i ∧ tr.eventTriggeredAt j server pskServerFinishedTag
      (mkPSKFinishedContent server client appKey)) ∨
    tr.isCorruptAt server i := by
  intro hInv hEvent
  have hi := Trace.entryAt_lt_length hEvent
  have hPred := hInv i hi _ hEvent
  change tlsEventPred tr i client pskClientFinishedTag
    (mkPSKFinishedContent client server appKey) at hPred
  unfold tlsEventPred at hPred
  have h1 : pskClientFinishedTag ≠ clientFinishedTag := by decide
  have h2 : pskClientFinishedTag ≠ serverFinishedTag := by decide
  simp only [beq_iff_eq, h1, h2, ite_false, ite_true] at hPred
  obtain ⟨peer, key, hcontent, hauth⟩ := hPred
  simp only [mkPSKFinishedContent, Bytes.concat.injEq, Bytes.literal.injEq] at hcontent
  obtain ⟨_, hpeer, hkey⟩ := hcontent
  have hpeer' : peer = server := String.toUTF8_injective hpeer.symm
  subst hpeer'; subst hkey
  exact hauth

end CatCrypt.Crypto.Symbolic.TLS
