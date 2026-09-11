/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubSourceTower
public import CatCrypt.Crypto.SecureCompilation.Ascent.FeAddEndToEnd

/-!
# Demo: the closed source-to-bytes capstones at their concrete values

Route: for the closed kernels `r0 := a0 - b0` and `r0 := a0 + b0` with literal
inputs `av = 1634760805`, `bv = 857760878`, `feSub_source_to_bytes_tower` and
`feAdd_source_to_bytes_tower` state that the front-compiled jasmin program
denotes to the source program's output word, and that the word's `wEnc` reading
is the `ZMod 2^64` difference (sum) of the inputs. Each demo reads the
numeral the equation yields.

Theorems: `feSub_source_to_bytes_tower` (`Ascent/FeSubSourceTower.lean`),
`feAdd_source_to_bytes_tower` (`Ascent/FeAddEndToEnd.lean`).

## Main results

* `feSub_value`: the emitted subtraction denotes the source word, whose `wEnc`
  reading is `776999927`.
* `feAdd_value`: the emitted addition denotes the source word, whose `wEnc`
  reading is `2492521683`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT (LeafSpec)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

/-- The emitted `feSub` program denotes to the source word, and that word reads
    as `1634760805 - 857760878 = 776999927` in `ZMod 2^64`. -/
theorem feSub_value (N : Nat) (leafSpec : LeafSpec) :
    feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy feSubSourceWord
      ∧ wEnc feSubSourceWord = (776999927 : ZMod (2 ^ 64)) := by
  obtain ⟨h₁, h₂⟩ := feSub_source_to_bytes_tower N leafSpec
  refine ⟨h₁, ?_⟩
  rw [h₂]
  decide

/-- The emitted `feAdd` program denotes to the source word, and that word reads
    as `1634760805 + 857760878 = 2492521683` in `ZMod 2^64`. -/
theorem feAdd_value (N : Nat) (leafSpec : LeafSpec) :
    feAddJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy feAddSourceWord
      ∧ wEnc feAddSourceWord = (2492521683 : ZMod (2 ^ 64)) := by
  obtain ⟨h₁, h₂⟩ := feAdd_source_to_bytes_tower N leafSpec
  refine ⟨h₁, ?_⟩
  rw [h₂]
  decide

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.feSub_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feSub_value

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.feAdd_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feAdd_value

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
