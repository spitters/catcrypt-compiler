/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.RelationalCompile

/-!
# Re-deriving the Keccak round emit-denotes-spec through the Rupicola framework

This file scales the denotational relational-compilation framework
(`RelationalCompile.lean`) from SHA-2 (`Sha2RoundRupicola.lean`) to the
**Keccak-p[1600,24] round** — the highest-payoff emit target in the
development (the XOF / hash leaf of ML-KEM, ML-DSA, SLH-DSA, FAEST, SHA-3).

## Ground truth and what the framework discharges

The bespoke #116/#118/#128/#132/#134/#135/#136 chain
(`KeccakEmitterReduction.lean` … `KeccakEmitterLanesReadout*.lean`) records the
~600-binding `emitRound` denotation reduction as a **residual `Prop`**
(`KeccakEmitterReduction.EmitRoundDenotesClosedForm`): the per-helper
`Com.denote` substrate lemmas (`emitOp_denote`, `emitMov_denote'`,
`emitRotL_denote_pos`) are proven once, but the full ~600-step composition
through `emitRound` (threading `bsAfterOp` extensions and pushing every read
back to the original `(bs, immVar, V)` through ~600 slot-disjointness side
conditions) is stated as a granted hypothesis, then bridged to FIPS 202 via
#113's `keccak_round_bitexact`.

The framework's Keccak instance (`RelationalCompile.lean` §7:
`KRefines`/`kArithStep`/`KRefines.arith`/`.seq`/`.consOp`/`.skip` and the
`scont_peel_keccak`/`rupicola_keccak` driver) **discharges exactly that
~600-step composition** structurally: it synthesizes the composite `KStateStep`
spec and proves `emitRound`'s `Com.denote` equals its continuation on a final
`(bsF, immVF, VF)` whose readout view is that spec — with *no* hand-written
`Com.denote` rewrite and *no* slot-disjointness inequality in the kernel proof.
Those live (once) inside `KRefines.arith` in `RelationalCompile.lean`.

## Op alphabet (FIPS 202 θρπχι) vs the framework

Keccak's round is xor-heavy with the χ AND-NOT and fixed rotations: `xor`,
`and`, `shl`, `shr`, `or` — all standard `JasminBinOp`, NOT being `xor` with
the all-ones mask immediate. So **no new operator** is needed; the framework's
single Keccak compilation lemma `KRefines.arith` (over `KeccakEmit.emitOp`)
covers every binding. The `emitMov` (idempotent-or copy) and `emitRotL`
(3-binding rotate, or skip at `n = 0`) wrappers are collapsed by the driver's
whnf to their bare `emitOp`s; the leaf-spec lemmas `KRefines.mov`/`.rotL_pos`/
`.rotL_zero` (in `RelationalCompile.lean`) document them.

## The re-derivation

Each `rupicola_keccak` invocation below states a `KRefines ?spec frag` goal
with the composite spec left as a metavariable, synthesized bottom-up by the
`SCont`-continuation splitter `scont_peel_keccak`. The proof body is the single
token `rupicola_keccak` — no `KRefines.seq`/`consOp` composition tree, no
`obtain`, no `Com.denote` rewrite, no slot inequality.

We re-derive the round bottom-up by sub-block (θ-C, θ-D, ρπ, χ, ι) and then the
**entire** `emitRound` — each in a single `rupicola_keccak` call.
-/

@[expose] public section

set_option autoImplicit false
-- The whole round is ~600 bindings; the splitter recurses once per binding.
set_option maxRecDepth 4000

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundRupicola

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.RelationalCompile
open CatCrypt.Crypto.SecureCompilation.RelationalCompile.Keccak

/-! ## 1. One θ column-parity chain, lowered by `rupicola_keccak`

`emitThetaCCol bs immV x` is four `xor`s into `C[x]`
(`C[x] = A[x,0] ⊕ … ⊕ A[x,4]`) — the simplest representative Keccak fragment.
The spec is synthesized; the proof is one token. -/

/-- **One θ column-parity chain, lowered by `rupicola_keccak` in one call.** -/
theorem emitThetaCCol_KRefines (x : Nat) :
    ∃ spec : KStateStep, KRefines (t := r64) spec
      (fun {Γ} (bs : BState Γ) immV k => emitThetaCCol bs immV x k) :=
  ⟨_, by rupicola_keccak⟩

/-! ## 2. The five θ column parities, lowered by `rupicola_keccak` -/

/-- **The full θ-C step (5 columns, 20 xors), one `rupicola_keccak` call.** -/
theorem emitTheta_C_KRefines :
    ∃ spec : KStateStep, KRefines (t := r64) spec
      (fun {Γ} (bs : BState Γ) immV k => emitTheta_C 5 0 bs immV k) :=
  ⟨_, by rupicola_keccak⟩

/-! ## 3. The θ-D step, lowered by `rupicola_keccak`

`emitTheta_D` exercises the `emitMov` (copy) and `emitRotL` (3-binding rotate)
wrappers in addition to the bare `xor`s — the driver collapses both via whnf. -/

/-- **The full θ-D step (5 columns; `mov`/`rotL`/`xor`s), one call.** -/
theorem emitTheta_D_KRefines :
    ∃ spec : KStateStep, KRefines (t := r64) spec
      (fun {Γ} (bs : BState Γ) immV k => emitTheta_D 5 0 bs immV k) :=
  ⟨_, by rupicola_keccak⟩

/-! ## 4. The ρ∘π step, lowered by `rupicola_keccak`

25 lanes, each a `mov` then a fixed `rotL` (the per-lane ρ offset). -/

/-- **The full ρ∘π step (25 lanes), one `rupicola_keccak` call.** -/
theorem emitRhoPi_KRefines :
    ∃ spec : KStateStep, KRefines (t := r64) spec
      (fun {Γ} (bs : BState Γ) immV k => emitRhoPi 25 0 bs immV k) :=
  ⟨_, by rupicola_keccak⟩

/-! ## 5. The χ nonlinear step, lowered by `rupicola_keccak`

25 lanes of `B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])` — the AND-NOT layer
(`mov ; xor mask ; and ; xor`). -/

/-- **The full χ step (25 lanes; the AND-NOT layer), one call.** -/
theorem emitChi_KRefines :
    ∃ spec : KStateStep, KRefines (t := r64) spec
      (fun {Γ} (bs : BState Γ) immV k => emitChi 25 0 bs immV k) :=
  ⟨_, by rupicola_keccak⟩

/-! ## 6. The ι step, lowered by `rupicola_keccak` -/

/-- **The ι step (`A[0,0] ⊕= RC[round]`), one call.** -/
theorem emitIota_KRefines (round : Nat) :
    ∃ spec : KStateStep, KRefines (t := r64) spec
      (fun {Γ} (bs : BState Γ) immV k => emitIota bs immV round k) :=
  ⟨_, by rupicola_keccak⟩

/-! ## 7. The full Keccak round, lowered by `rupicola_keccak` in one call

This is the payoff: the entire FIPS 202 round — θ (parities + D), ρ∘π, χ, ι;
the ~600-binding chain the bespoke #118/#128 residual records — is lowered to a
synthesized `KStateStep` spec by the `SCont` splitter in a single
`rupicola_keccak` invocation. The proof writes neither the spec, any
`KRefines.seq`/`consOp` composition, any `Com.denote` rewrite, nor any
slot-disjointness inequality. -/

/-- **The full Keccak-p round, lowered by `rupicola_keccak` in one call.** -/
theorem emitRound_KRefines (round : Nat) :
    ∃ spec : KStateStep, KRefines (t := r64) spec
      (fun {Γ} (bs : BState Γ) immV k => emitRound bs immV round k) :=
  ⟨_, by rupicola_keccak⟩

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundRupicola
