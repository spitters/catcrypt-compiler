/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Primitives.SHA256
public import CatCrypt.Crypto.Primitives.SHA256

/-!
# SHA-256 abstract round words (model-free)

The `UInt32` SHA-256 round components `t1Word` / `aPrimeWord` / `ePrimeWord` and
their faithfulness anchors to the sealed `Primitives.SHA256.compressRound`,
hoisted out of the bespoke `Sha256DwordRoundRealization` (which imports the
`Avx512DwordModel` machine) into this model-free module so the unified-dialect
abstract round tie (`Sha256DwordRoundAbstractCom`) can reuse them without a
machine-model dependency. These are pure `UInt32`/`Primitives.SHA256`
declarations — they never referenced `ZState32` or the dword lane model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordRoundWords

open CatCrypt.Crypto.Primitives.SHA256

/-- `T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ` at `UInt32` (FIPS-180-4 §6.2.2). -/
def t1Word (e f g h kt wt : UInt32) : UInt32 :=
  h + bigSigma1 e + ch e f g + kt + wt

/-- `a' = T₁ + T₂`, `T₂ = Σ₀(a) + Maj(a,b,c)`. -/
def aPrimeWord (a b c e f g h kt wt : UInt32) : UInt32 :=
  t1Word e f g h kt wt + (bigSigma0 a + maj a b c)

/-- `e' = d + T₁`. -/
def ePrimeWord (d e f g h kt wt : UInt32) : UInt32 :=
  d + t1Word e f g h kt wt

/-- The FIPS-180-4 initial state `H₀`, as a concrete `State256` for the anchor. -/
def h0State : State256 := fun (i : Fin 8) =>
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].getD i.val 0

/-- **`aPrimeWord` is `compressRound`'s `a'` (anchor).** On `H₀` and the round-0
    schedule/constant, the `UInt32` `aPrimeWord` equals `compressRound H₀ W₀ K₀ 0`
    — the sealed SHA-256 round's first output word `a' = T₁+T₂`. -/
theorem aPrimeWord_anchor :
    aPrimeWord (h0State 0) (h0State 1) (h0State 2) (h0State 4) (h0State 5)
      (h0State 6) (h0State 7) 0x71374491 0x428a2f98
      = compressRound h0State 0x428a2f98 0x71374491 0 := by
  native_decide

/-- **`ePrimeWord` is `compressRound`'s `e'` (anchor).** On `H₀` and the round-0
    schedule/constant, the `UInt32` `ePrimeWord` equals `compressRound H₀ W₀ K₀ 4`
    — the sealed SHA-256 round's fifth output word `e' = d+T₁`. -/
theorem ePrimeWord_anchor :
    ePrimeWord (h0State 3) (h0State 4) (h0State 5) (h0State 6) (h0State 7)
      0x71374491 0x428a2f98
      = compressRound h0State 0x428a2f98 0x71374491 4 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordRoundWords
