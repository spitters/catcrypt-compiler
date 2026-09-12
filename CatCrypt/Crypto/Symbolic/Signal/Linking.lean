/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Signal.Auth
public import CatCrypt.Crypto.Symbolic.Signal.KeySecrecy
public import CatCrypt.Crypto.Symbolic.Signal.ProtocolVerification

/-!
# Dual Security for Signal: Symbolic

This file documents the dual security architecture for Signal X3DH.
The symbolic hypotheses provide trace-level guarantees.

## Main Result

* `signal_dual_security` — Symbolic auth + key secrecy for Signal X3DH

## Architecture

Signal X3DH has two independent security paths:

### Path 1: Symbolic (`signal_dual_security`, this file)
The symbolic results provide:
- X3DH authentication (event correspondence)
- Key secrecy (label analysis through key schedule)

### Path 2: Computational
Two independent computational arguments are wired up:
- **CLC-derived generic bound**: `x3dh_uc_secure_from_symbolic` in
  `CLCLinking.lean`, lifting `honestX3DH_invariant` to a
  `numKeys • total` UC bound via the CLC bridge.
- **Direct tight bound**: `x3dh_uc_secure` in `Signal/X3DH.lean`,
  giving `ε_gdh + ε_kdf` under GDH + PRF.
Both are packaged together in `Signal/X3DH/DualSecurity.lean`.

## References

* Signal Protocol specification: X3DH key agreement
* DY* Signal: dual security (Bhargavan et al.)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

/-- **Signal dual security**: the three symbolic guarantees for X3DH, conjoined.

The conjuncts are, in order: X3DH authentication — a completed `X3DHResp` at
`i` is preceded by a matching `X3DHInit` unless the peer is corrupt
(`signal_x3dh_authentication`); root-key secrecy — the attacker knows the
X3DH root key only if the initiator is corrupt (`signal_x3dh_key_secrecy`);
and the trace invariant for an honest session run from the empty trace
(`honestX3DH_invariant`).

The statement takes no hypotheses: each conjunct is the statement of the
theorem that supplies it. -/
theorem signal_dual_security :
    /- Authentication -/
    (∀ (tr : Trace) (i : Nat) (bob alice : String) (rootKey : Bytes),
      @traceInvariant signalInvariants tr →
      tr.eventTriggeredAt i bob x3dhRespTag
        (mkX3DHContent bob alice rootKey) →
      (∃ j, j < i ∧ tr.eventTriggeredAt j alice x3dhInitTag
        (mkX3DHContent alice bob rootKey)) ∨
      tr.isCorruptAt alice i) ∧
    /- Key secrecy -/
    (∀ (tr : Trace) (alice : String) (rootKey : Bytes)
      (ek ikA : Bytes) (ikB spkB opkB : Bytes),
      rootKey = signalKeySchedule
        (Bytes.dh ikA (Bytes.dhPub spkB))
        (Bytes.dh ek (Bytes.dhPub ikB))
        (Bytes.dh ek (Bytes.dhPub spkB))
        (Bytes.dh ek (Bytes.dhPub opkB)) →
      hasLabel tr ek (principalLabel alice) →
      hasLabel tr ikA (principalLabel alice) →
      @traceInvariant signalInvariants tr →
      AttackerKnows tr rootKey →
      tr.isCorruptAt alice (tr.length - 1)) ∧
    /- Protocol verification -/
    (∀ (alice bob : String) (ikB spkB opkB : Bytes),
      @traceInvariant signalInvariants (honestX3DH alice bob ikB spkB opkB .nil).2) :=
  ⟨signal_x3dh_authentication, signal_x3dh_key_secrecy, honestX3DH_invariant⟩

end CatCrypt.Crypto.Symbolic.Signal
