/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond

/-!
# Lattice → Jasmin lowering: import hub

This module declares nothing. It re-exports `JasminCTPredicate` and
`LatticeToJasminDenoteUncond` to its importers (`RobustSafetyContext`,
`JForProgCT`, `X86Backend.FramingReconcile`).

## Main results

None. Behaviour preservation of the lowering is
`LatticeToJasminDenoteUncond.lowerLatticeToJasmin_denote_eq_uncond`; constant time
of emitted code is `X86Backend.DecodedCT.bytesCTCheck_sound` at the bytes and
`Dialects.CryptoDialectCTLeak.catCT` at `Com`.
-/
