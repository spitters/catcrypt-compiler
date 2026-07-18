/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots
import CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveInverse

/-!
# The recursive butterfly NTT/INTT at the concrete ML-KEM/ML-DSA parameters

`NTTRecursiveFull.nttRec` is the concrete radix-2 butterfly forward NTT (proven
`= dft` by `nttRec_eq_dft`), and `NTTRecursiveInverse.nttRecInv` is the GS/DIF
inverse network (proven `= idft`, inverting `nttRec` by `nttRecInv_nttRec`). This
file instantiates those at the real lattice parameters using the concrete roots
from `ConcreteNttRoots`, tying the actual butterfly *algorithm* — not just the
abstract `dft`/`idft` — to ML-KEM (`ZMod 3329`, `2⁸ = 256`, root `17`) and ML-DSA
(`ZMod 8380417`, `2⁹ = 512`, root `1753`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.ConcreteRecursiveNtt

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveInverse
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots

/-! ## ML-KEM (`ZMod 3329`, `e = 8`, `2⁸ = 256`, `ω = 17`) -/

/-- The ML-KEM butterfly forward NTT computes the DFT. -/
theorem mlkem_nttRec_eq_dft (x : Fin (2 ^ 8) → ZMod 3329) (k : Fin (2 ^ 8)) :
    nttRec 8 (17 : ZMod 3329) x k = dft (2 ^ 8) (17 : ZMod 3329) x k :=
  nttRec_eq_dft 8 (17 : ZMod 3329) pow_256_17_eq_one x k

/-- The ML-KEM butterfly inverse NTT inverts the forward NTT: `intt ∘ ntt = id`. -/
theorem mlkem_nttRecInv_nttRec (x : Fin (2 ^ 8) → ZMod 3329) :
    nttRecInv 8 (17 : ZMod 3329) (nttRec 8 (17 : ZMod 3329) x) = x := by
  have hpr : IsPrimitiveRoot (17 : ZMod 3329) (2 ^ 8) := isPrimitiveRoot_17_256
  have hn : ((2 ^ 8 : ℕ) : ZMod 3329) ≠ 0 := by decide
  exact nttRecInv_nttRec 8 (17 : ZMod 3329) hpr hn x

/-! ## ML-DSA (`ZMod 8380417`, `e = 9`, `2⁹ = 512`, `ω = 1753`) -/

/-- The ML-DSA butterfly forward NTT computes the DFT. -/
theorem mldsa_nttRec_eq_dft (x : Fin (2 ^ 9) → ZMod 8380417) (k : Fin (2 ^ 9)) :
    nttRec 9 (1753 : ZMod 8380417) x k = dft (2 ^ 9) (1753 : ZMod 8380417) x k :=
  nttRec_eq_dft 9 (1753 : ZMod 8380417) pow_512_1753_eq_one x k

/-- The ML-DSA butterfly inverse NTT inverts the forward NTT: `intt ∘ ntt = id`. -/
theorem mldsa_nttRecInv_nttRec (x : Fin (2 ^ 9) → ZMod 8380417) :
    nttRecInv 9 (1753 : ZMod 8380417) (nttRec 9 (1753 : ZMod 8380417) x) = x := by
  have hpr : IsPrimitiveRoot (1753 : ZMod 8380417) (2 ^ 9) := isPrimitiveRoot_1753_512
  have hn : ((2 ^ 9 : ℕ) : ZMod 8380417) ≠ 0 := by decide
  exact nttRecInv_nttRec 9 (1753 : ZMod 8380417) hpr hn x

end CatCrypt.Crypto.Optimizer.Lattice.ConcreteRecursiveNtt
