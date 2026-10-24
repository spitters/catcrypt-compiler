/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Word

/-!
# The BabyBear instance of `Width16` is the BabyBear Poseidon2 permutation

The permutation `Width16.permute bbParams`, at the parameter record `bbParams` of the word
program of `VIR.Poseidon2Word`, equals the standalone specification
`BabyBear.poseidon2BabyBearPermute`. The proof is by layers: the S-boxes agree as
`x ^ 7 = x ^ 4 · x ^ 2 · x`, the external and internal MDS layers agree lane by lane, the
round constants of `bbParams` are those of `BabyBear` by construction, and the round
iterations (`List.foldl` over `List.finRange` against `Nat.rec`) agree round by round.

## Main results

* `permute_bbParams_eq`: `Width16.permute bbParams = BabyBear.poseidon2BabyBearPermute`.
* `bbPermProg_spec'`: the BabyBear word program computes
  `BabyBear.poseidon2BabyBearPermute`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BabyBearTie

open CatCrypt.Crypto.Hash.Poseidon2
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Word
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate (Ctxs)

/-- The S-box of `bbParams` is the BabyBear S-box. -/
theorem sbox_bbParams (x : ZMod bbParams.p) : Width16.sbox bbParams x = BabyBear.sbox x := by
  show (x : ZMod BabyBear.babyBearPrime) ^ 7 = x * x * (x * x) * (x * x) * x
  ring

/-- The external MDS layer of `Width16` is the BabyBear external MDS layer. -/
theorem externalMDS_bbParams (x : Fin 16 → ZMod bbParams.p) :
    Width16.externalMDS x = BabyBear.externalMDS x := by
  funext i
  fin_cases i <;> rfl

/-- The internal MDS layer of `bbParams` is the BabyBear internal MDS layer. -/
theorem internalMDS_bbParams (x : Fin 16 → ZMod bbParams.p) :
    Width16.internalMDS bbParams x = BabyBear.internalMDS x := rfl

/-- An external round of `bbParams` is a BabyBear external round. -/
theorem externalRound_bbParams (x c : Fin 16 → ZMod bbParams.p) :
    Width16.externalRound bbParams x c = BabyBear.externalRound x c := by
  unfold Width16.externalRound BabyBear.externalRound
  rw [externalMDS_bbParams]
  simp only [sbox_bbParams]
  rfl

/-- An internal round of `bbParams` is a BabyBear internal round. -/
theorem internalRound_bbParams (x : Fin 16 → ZMod bbParams.p) (c : ZMod bbParams.p) :
    Width16.internalRound bbParams x c = BabyBear.internalRound x c := by
  simp only [Width16.internalRound, BabyBear.internalRound, internalMDS_bbParams]
  congr 1
  funext i
  by_cases h : i.val = 0
  · simp only [BabyBear.sboxLane0, h, ite_true, sbox_bbParams]
    rfl
  · simp [BabyBear.sboxLane0, h]

/-- **The tie.** The width-16 permutation at `bbParams` is the BabyBear Poseidon2
permutation. -/
theorem permute_bbParams_eq :
    Width16.permute bbParams = BabyBear.poseidon2BabyBearPermute := by
  funext x
  simp only [Width16.permute, BabyBear.poseidon2BabyBearPermute, externalMDS_bbParams,
    externalRound_bbParams, internalRound_bbParams, BabyBear.applyExternalPrefix,
    BabyBear.applyAllPartialRounds, BabyBear.applyExternalSuffix,
    show BabyBear.halfFullRounds = 0 + 1 + 1 + 1 + 1 from rfl,
    show BabyBear.partialRounds = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl,
    Nat.rec_zero]
  simp [bbParams, BabyBear.fullRounds, List.finRange_succ, Width16.rcInitial, Width16.rcFinal]

/-- **The BabyBear permutation against the standalone specification.** Input lanes at most
`p + 64` representing `x` with factor `−2 ^ 64` give output lanes at most `p + 64`
representing `BabyBear.poseidon2BabyBearPermute x`. -/
theorem bbPermProg_spec' (x : Fin 16 → ZMod bbParams.p) (W : Valuation (Ctxs 32 16))
    (hW : Rep16 bbParams.p (-2 ^ 64) 2013265985 x W) :
    Rep16 bbParams.p (-2 ^ 64) 2013265985 (BabyBear.poseidon2BabyBearPermute x)
      ((permProg bbParams bbPermChain [true, true] bbRc).denote W) := by
  rw [← permute_bbParams_eq]
  exact bbPermProg_spec x W hW

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BabyBearTie
