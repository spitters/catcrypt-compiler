/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttWord

/-!
# The Falcon NTT at `q = 12289` as word templates

The negacyclic NTT templates of `VIR/NegacyclicNttTemplate.lean` and
`VIR/NegacyclicNttWord.lean` instantiated at the Falcon modulus `q = 12289`, with
full splitting to degree one: `n = 512` (nine layers, root `ψ = 49` of order
`1024`) and `n = 1024` (ten layers, root `ψ = 7` of order `2048`).

Two unsigned Montgomery schedules are given.  `falconLazy32` keeps lanes in 32-bit
words with radix `2 ^ 32` and reduces no layer.  On 16-bit words a lane bound plus
the offset `2 q` must fit `2 ^ 16`, so the bound is `q` or `3 q`, and the Barrett
reduction of `nttProgUW` (shift `29`, constant `43688`) is exact only below
`49164`, so a layer whose input bound is `3 q` cannot be reduced.  Hence every
layer but the last is reduced: `falconRed16 L` reduces after layers `0, …, L − 2`.

## Main results

* `falcon512Ntt_ok`, `falcon1024Ntt_ok` — the parameter records satisfy
  `NttParams.Ok`.
* `falcon512Ntt_denote`, `falcon1024Ntt_denote` — the field-level transform
  program computes `nttSpec`.
* `falconLazy32_ok512`, `falconLazy32_ok1024` — the 32-bit schedule satisfies
  `SchedOk` and `UWordOk`.
* `falconRed16_ok512`, `falconRed16_ok1024` — the 16-bit reduced schedules satisfy
  `SchedOk` and `UWordOk`.
* `falcon512UW32_denote`, `falcon1024UW32_denote`, `falcon512UW16_denote`,
  `falcon1024UW16_denote` — the unsigned word lowerings compute `nttSpec` with
  output bounds `19 q`, `21 q`, `3 q` and `3 q`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral (hvGetD)

/-! ## 1. Parameter records -/

/-- Falcon-512: `q = 12289`, 512 coefficients, nine layers, `ψ = 49`. -/
def falcon512Ntt : NttParams := ⟨12289, 9, 9, 49⟩

/-- Falcon-1024: `q = 12289`, 1024 coefficients, ten layers, `ψ = 7`. -/
def falcon1024Ntt : NttParams := ⟨12289, 10, 10, 7⟩

theorem falcon512Ntt_ok : falcon512Ntt.Ok := by decide +kernel

theorem falcon1024Ntt_ok : falcon1024Ntt.Ok := by decide +kernel

/-- The Falcon-512 transform program computes `nttSpec` at `ψ = 49`, `L = 9`. -/
theorem falcon512Ntt_denote (w : ℕ → ZMod 12289) (i : ℕ) (hi : i < 512) :
    hvGetD ((nttProg falcon512Ntt).denote (fnVal 12289 w 512 0)) i
      = nttSpec (49 : ZMod 12289) 9 9 w i :=
  nttProg_denote falcon512Ntt falcon512Ntt_ok w i hi

/-- The Falcon-1024 transform program computes `nttSpec` at `ψ = 7`, `L = 10`. -/
theorem falcon1024Ntt_denote (w : ℕ → ZMod 12289) (i : ℕ) (hi : i < 1024) :
    hvGetD ((nttProg falcon1024Ntt).denote (fnVal 12289 w 1024 0)) i
      = nttSpec (7 : ZMod 12289) 10 10 w i :=
  nttProg_denote falcon1024Ntt falcon1024Ntt_ok w i hi

/-! ## 2. The 32-bit unsigned schedule -/

/-- The Falcon schedule on 32-bit words: radix `2 ^ 32`, Montgomery constant
`4143984639 = −q⁻¹ mod 2 ^ 32`, offset `2 q`, no reduced layer. -/
def falconLazy32 : LazySched := ⟨2 ^ 32, 4143984639, 2, fun _ => false, 32⟩

theorem falconLazy32_ok512 :
    SchedOk falcon512Ntt falconLazy32 ∧ UWordOk falcon512Ntt falconLazy32 32 := by
  decide

theorem falconLazy32_ok1024 :
    SchedOk falcon1024Ntt falconLazy32 ∧ UWordOk falcon1024Ntt falconLazy32 32 := by
  decide

/-! ## 3. The 16-bit reduced schedules -/

/-- The Falcon schedule on 16-bit words for `L` layers: radix `2 ^ 16`, Montgomery
constant `12287 = −q⁻¹ mod 2 ^ 16`, offset `2 q`, and a Barrett reduction after
every layer `ℓ < L − 1`. -/
def falconRed16 (L : ℕ) : LazySched := ⟨2 ^ 16, 12287, 2, fun ℓ => decide (ℓ + 1 < L), 16⟩

theorem falconRed16_ok512 :
    SchedOk falcon512Ntt (falconRed16 9) ∧ UWordOk falcon512Ntt (falconRed16 9) 16 := by
  decide

theorem falconRed16_ok1024 :
    SchedOk falcon1024Ntt (falconRed16 10) ∧ UWordOk falcon1024Ntt (falconRed16 10) 16 := by
  decide

/-! ## 4. The word lowerings -/

/-- The Falcon-512 lowering on 32-bit words: from inputs below `q`, every output
word is below `19 q` and is `nttSpec` at `ψ = 49`, `L = 9` modulo `q`. -/
theorem falcon512UW32_denote (f : ℕ → ℕ) (hf : ∀ j, f j < 12289) (i : ℕ) (hi : i < 512) :
    (hvGetG (Rw 32) (0 : BitVec 32) ((nttProgUW falcon512Ntt falconLazy32 32).denote
        (lanesVal (Rw 32) (fun j => BitVec.ofNat 32 (f j)) 512 0)) i).toNat < 19 * 12289 ∧
    (((hvGetG (Rw 32) (0 : BitVec 32) ((nttProgUW falcon512Ntt falconLazy32 32).denote
        (lanesVal (Rw 32) (fun j => BitVec.ofNat 32 (f j)) 512 0)) i).toNat : ℕ)
        : ZMod 12289)
      = nttSpec (49 : ZMod 12289) 9 9 (fun j => (f j : ZMod 12289)) i :=
  nttProgUW_denote falcon512Ntt falconLazy32 32 falcon512Ntt_ok falconLazy32_ok512.1
    falconLazy32_ok512.2 f hf i hi

/-- The Falcon-1024 lowering on 32-bit words: from inputs below `q`, every output
word is below `21 q` and is `nttSpec` at `ψ = 7`, `L = 10` modulo `q`. -/
theorem falcon1024UW32_denote (f : ℕ → ℕ) (hf : ∀ j, f j < 12289) (i : ℕ) (hi : i < 1024) :
    (hvGetG (Rw 32) (0 : BitVec 32) ((nttProgUW falcon1024Ntt falconLazy32 32).denote
        (lanesVal (Rw 32) (fun j => BitVec.ofNat 32 (f j)) 1024 0)) i).toNat < 21 * 12289 ∧
    (((hvGetG (Rw 32) (0 : BitVec 32) ((nttProgUW falcon1024Ntt falconLazy32 32).denote
        (lanesVal (Rw 32) (fun j => BitVec.ofNat 32 (f j)) 1024 0)) i).toNat : ℕ)
        : ZMod 12289)
      = nttSpec (7 : ZMod 12289) 10 10 (fun j => (f j : ZMod 12289)) i :=
  nttProgUW_denote falcon1024Ntt falconLazy32 32 falcon1024Ntt_ok falconLazy32_ok1024.1
    falconLazy32_ok1024.2 f hf i hi

/-- The Falcon-512 lowering on 16-bit words: from inputs below `q`, every output
word is below `3 q` and is `nttSpec` at `ψ = 49`, `L = 9` modulo `q`. -/
theorem falcon512UW16_denote (f : ℕ → ℕ) (hf : ∀ j, f j < 12289) (i : ℕ) (hi : i < 512) :
    (hvGetG (Rw 16) (0 : BitVec 16) ((nttProgUW falcon512Ntt (falconRed16 9) 16).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofNat 16 (f j)) 512 0)) i).toNat < 3 * 12289 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((nttProgUW falcon512Ntt (falconRed16 9) 16).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofNat 16 (f j)) 512 0)) i).toNat : ℕ)
        : ZMod 12289)
      = nttSpec (49 : ZMod 12289) 9 9 (fun j => (f j : ZMod 12289)) i :=
  nttProgUW_denote falcon512Ntt (falconRed16 9) 16 falcon512Ntt_ok falconRed16_ok512.1
    falconRed16_ok512.2 f hf i hi

/-- The Falcon-1024 lowering on 16-bit words: from inputs below `q`, every output
word is below `3 q` and is `nttSpec` at `ψ = 7`, `L = 10` modulo `q`. -/
theorem falcon1024UW16_denote (f : ℕ → ℕ) (hf : ∀ j, f j < 12289) (i : ℕ) (hi : i < 1024) :
    (hvGetG (Rw 16) (0 : BitVec 16) ((nttProgUW falcon1024Ntt (falconRed16 10) 16).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofNat 16 (f j)) 1024 0)) i).toNat < 3 * 12289 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((nttProgUW falcon1024Ntt (falconRed16 10) 16).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofNat 16 (f j)) 1024 0)) i).toNat : ℕ)
        : ZMod 12289)
      = nttSpec (7 : ZMod 12289) 10 10 (fun j => (f j : ZMod 12289)) i :=
  nttProgUW_denote falcon1024Ntt (falconRed16 10) 16 falcon1024Ntt_ok falconRed16_ok1024.1
    falconRed16_ok1024.2 f hf i hi

end CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
