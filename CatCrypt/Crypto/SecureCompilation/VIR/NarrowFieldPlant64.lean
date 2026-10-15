/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BabyBearTie

/-!
# The Plantard multiply with every product at `2 w` bits

`plantWrapBlk w p pinv` is the Plantard multiply of `NarrowField.plantBlk` with its low
product taken by wrapping multiplication at `2 w` bits. `plantBlk` forms
`a · b · pinv` at `4 w` bits and masks it to `2 w` bits, which keeps every binding in the
exact fragment of `ComRangeExact`. The block here casts the operands to `2 w` bits, where
`a · b < 2 ^ (2 w)` is exact, and multiplies by `pinv` modulo `2 ^ (2 w)`; the mask is the
wrap. The high step `(⌊c / 2 ^ w⌋ + 1) · p / 2 ^ w` is unchanged: for `p < 2 ^ w` its
product is below `2 ^ (2 w)`. No binding is wider than `2 w` bits, so at `w = 32` the block
is a 64-bit program.

The second product wraps, so the block lies outside the exact fragment and has no
`boundsOk` certificate. Its word function `plantW` is evaluated directly: `plantW_toNat`
gives its value as a natural number under `p < 2 ^ w` and `x · y < 2 ^ (2 w)`, and
`plantZ_eq_natCast` identifies that number with the integer semantics `plantZ` of
`plantBlk`. Under `F.plantOk` the two blocks therefore agree on words at most `F.inMax`.

## Main definitions

* `plantWrapBlk`: the block, twelve bindings at widths `w` and `2 w`.
* `plantBlk64`: its instance on 32-bit words.
* `plantW`: its word function.
* `WordField.mulPlantW`: the multiply of a `WordField` by this block.
* `plantWrapChain`: the block as a `Poseidon2Word.ChainMul`, with the bound and the factor
  `−2 ^ (2 w)` of `Poseidon2Word.plantChain`.
* `bbPermChain64`, `kbPermChain64`: the S-box chains of the BabyBear and KoalaBear
  permutations on this block.

## Main results

* `plantWrapBlk_denote`, `plantBlk64_denote`: the block computes `plantW`.
* `plantW_toNat`: the value of `plantW`.
* `WordField.mulPlantW_eq`: under `F.plantOk`, on words at most `F.inMax`,
  `F.mulPlantW x y = F.mulPlant x y`.
* `WordField.mulPlantW_rep`: the representation theorem of `WordField.mulPlant_rep` for
  this block.
* `bbPermProg64_spec'`: the BabyBear word program on `bbPermChain64` computes
  `BabyBear.poseidon2BabyBearPermute`.
* `kbPermProg64_spec`: the KoalaBear word program on `kbPermChain64` computes
  `KoalaBear.permute`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowFieldPlant64

open CatCrypt.Crypto.Hash.Poseidon2
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowField
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate (constE binE castE shrE Rw Ctxs)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Word

/-! ## 1. The block and its word function -/

/-- The Plantard multiply with every product at `2 w` bits:
`c = (a · b · pinv) mod 2 ^ (2 w)` by wrapping multiplication, result
`(⌊c / 2 ^ w⌋ + 1) · p / 2 ^ w`. -/
def plantWrapBlk (w p pinv : ℕ) : Com jasminDialect (C2 w) (.reg w) :=
  .var (castE w (2 * w) .here) <|
  .var (castE w (2 * w) (.there (.there .here))) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (constE (2 * w) pinv) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (shrE (2 * w) w .here) <|
  .var (constE (2 * w) 1) <|
  .var (binE .add (2 * w) (.there .here) .here) <|
  .var (constE (2 * w) p) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (shrE (2 * w) w .here) <|
  .var (castE (2 * w) w .here) <|
  .ret .here

/-- `plantWrapBlk` on 32-bit words: a program at 32 and 64 bits. -/
abbrev plantBlk64 (p pinv : ℕ) : Com jasminDialect (C2 32) (.reg 32) := plantWrapBlk 32 p pinv

/-- The word function of `plantWrapBlk`. -/
def plantW (w p pinv : ℕ) (x y : BitVec w) : BitVec w :=
  ((((x.zeroExtend (2 * w) * y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) pinv) >>> w
    + BitVec.ofNat (2 * w) 1) * BitVec.ofNat (2 * w) p) >>> w).zeroExtend w

theorem plantWrapBlk_denote (w p pinv : ℕ) (x y : BitVec w) :
    run2 (plantWrapBlk w p pinv) x y = plantW w p pinv x y := by
  show ((((x.zeroExtend (2 * w) * y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) pinv)
      >>> shiftMask (2 * w) w + BitVec.ofNat (2 * w) 1) * BitVec.ofNat (2 * w) p)
      >>> shiftMask (2 * w) w).zeroExtend w = _
  rw [NegacyclicNttTemplate.shiftMask_two_mul_self]
  rfl

theorem plantBlk64_denote (p pinv : ℕ) (x y : BitVec 32) :
    run2 (plantBlk64 p pinv) x y = plantW 32 p pinv x y := rfl

/-! ## 2. The value of the word function -/

/-- For `p < 2 ^ w` and `x · y < 2 ^ (2 w)` the word function is the Plantard value: the
operand product does not wrap, the product by `pinv` wraps to its residue modulo
`2 ^ (2 w)`, and the high step stays below `2 ^ (2 w)`. -/
theorem plantW_toNat (w p pinv : ℕ) (hw : 0 < w) (hp : p < 2 ^ w) (x y : BitVec w)
    (hxy : x.toNat * y.toNat < 2 ^ (2 * w)) :
    (plantW w p pinv x y).toNat
      = (x.toNat * y.toNat * pinv % 2 ^ (2 * w) / 2 ^ w + 1) * p / 2 ^ w := by
  have hRR : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  have hR : 0 < 2 ^ w := Nat.two_pow_pos w
  have hlt : 2 ^ w < 2 ^ (2 * w) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hx : x.toNat < 2 ^ (2 * w) := x.isLt.trans hlt
  have hy : y.toNat < 2 ^ (2 * w) := y.isLt.trans hlt
  set c := x.toNat * y.toNat * pinv % 2 ^ (2 * w) with hc
  have hc1 : c / 2 ^ w < 2 ^ w := by
    rw [Nat.div_lt_iff_lt_mul hR, ← hRR]; exact Nat.mod_lt _ (by positivity)
  have hm : (c / 2 ^ w + 1) * p < 2 ^ (2 * w) := by
    rw [hRR]
    calc (c / 2 ^ w + 1) * p ≤ 2 ^ w * p := Nat.mul_le_mul_right _ hc1
      _ < 2 ^ w * 2 ^ w := Nat.mul_lt_mul_of_pos_left hp hR
  have hq : (c / 2 ^ w + 1) * p / 2 ^ w < 2 ^ w := by
    rw [Nat.div_lt_iff_lt_mul hR, ← hRR]; exact hm
  simp only [plantW, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_mul,
    BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hxy, Nat.mul_mod_mod,
    Nat.mod_mul_mod, Nat.add_mod_mod]
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hq]

/-- The integer semantics of `plantBlk` on natural operands, as a natural number. -/
theorem plantZ_eq_natCast (w p pinv : ℕ) (hpl : pinv < 2 ^ (4 * w)) (hp : p < 2 ^ (2 * w))
    (hw : 0 < w) (a b : ℕ) :
    plantZ w p pinv a b = ((a * b * pinv % 2 ^ (2 * w) / 2 ^ w + 1) * p / 2 ^ w : ℕ) := by
  have hmask : 2 ^ (2 * w) - 1 < 2 ^ (4 * w) := by
    have : 2 ^ (2 * w) ≤ 2 ^ (4 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : 1 < 2 ^ (2 * w) := Nat.one_lt_two_pow (by omega)
  unfold plantZ
  rw [cW_mask hmask, cW_of_lt hpl, cW_of_lt hp, cW_of_lt h1, andZ_mask (by positivity)]
  push_cast
  rfl

/-! ## 3. Agreement with `plantBlk` -/

/-- The Plantard multiply of `F` on words by `plantWrapBlk`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.NarrowField.WordField.mulPlantW {w p : ℕ}
    (F : WordField w p) (x y : BitVec w) : BitVec w :=
  run2 (plantWrapBlk w p F.plantInv) x y

/-- **Agreement.** Under `F.plantOk`, on words at most `F.inMax`, the block with products
at `2 w` bits computes the word `plantBlk` computes. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.VIR.NarrowField.WordField.mulPlantW_eq
    {w p : ℕ} (F : WordField w p) (h : F.plantOk = true) {x y : BitVec w}
    (hx : x.toNat ≤ F.inMax) (hy : y.toNat ≤ F.inMax) :
    F.mulPlantW x y = F.mulPlant x y := by
  simp only [WordField.plantOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, h2, h3, h4, h5⟩, hb⟩ := h
  have hRR : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  have hpw : p < 2 ^ w := by
    have : 2 ^ w * p < 2 ^ w * 2 ^ w := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hxy : x.toNat * y.toNat < 2 ^ (2 * w) :=
    lt_of_le_of_lt (Nat.mul_le_mul hx hy) (by omega)
  obtain ⟨e, -⟩ := run2_eq_denoteZ hb x y hx hy
  rw [plantBlk_denoteZ, plantZ_eq_natCast w p F.plantInv h2 h3 h4] at e
  apply BitVec.eq_of_toNat_eq
  rw [WordField.mulPlantW, plantWrapBlk_denote, plantW_toNat w p F.plantInv h4 hpw x y hxy]
  exact (Int.ofNat_inj.mp e).symm

/-- **The Plantard block at `2 w` bits.** On words representing `u`, `v` with bound
`inMax`, the output represents an element `z` with `z · 2 ^ (2 w) = −(u · v)`, with bound
`p`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.VIR.NarrowField.WordField.mulPlantW_rep
    {w p : ℕ} (F : WordField w p) (h : F.plantOk = true) {x y : BitVec w} {u v : ZMod p}
    (hx : Rep p F.inMax x u) (hy : Rep p F.inMax y v) :
    Rep p p (F.mulPlantW x y) ((F.mulPlantW x y).toNat : ZMod p) ∧
      ((F.mulPlantW x y).toNat : ZMod p) * 2 ^ (2 * w) = -(u * v) := by
  rw [F.mulPlantW_eq h hx.1 hy.1]
  exact F.mulPlant_rep h hx hy

/-! ## 4. The chainable multiply and the permutations -/

/-- `plantWrapBlk` as a chainable multiply, with the bound `F.inMax` and the factor
`κ = −2 ^ (2 w)` of `plantChain`. -/
def plantWrapChain {w p : ℕ} (F : WordField w p) (h : F.plantOk = true)
    (hp : p ≤ F.inMax) : ChainMul w p where
  blk := plantWrapBlk w p F.plantInv
  bound := F.inMax
  κ := -2 ^ (2 * w)
  spec x y hx hy := by
    have e : run2 (plantWrapBlk w p F.plantInv) x y = run2 (plantBlk w p F.plantInv) x y :=
      F.mulPlantW_eq h hx hy
    rw [e]
    exact (plantChain F h hp).spec x y hx hy

/-- The S-box chain of the BabyBear permutation on the 64-bit Plantard block, inputs at
most `p + 64`. -/
def bbPermChain64 : ChainMul 32 2013265921 :=
  plantWrapChain bbFieldB bbFieldB_plantOk (by decide)

/-- The S-box chain of the KoalaBear permutation on the 64-bit Plantard block, inputs at
most `p + 64`. -/
def kbPermChain64 : ChainMul 32 2130706433 :=
  plantWrapChain kbFieldB kbFieldB_plantOk (by decide)

/-- The block of `bbPermChain64` is the 64-bit Plantard block at the BabyBear constants. -/
theorem bbPermChain64_blk :
    bbPermChain64.blk = plantBlk64 2013265921 4053239662620180481 := rfl

/-- **The BabyBear permutation on the 64-bit Plantard block.** Input lanes at most `p + 64`
representing `x` with factor `−2 ^ 64` give output lanes at most `p + 64` representing
`BabyBear.poseidon2BabyBearPermute x`. -/
theorem bbPermProg64_spec' (x : Fin 16 → ZMod bbParams.p) (W : Valuation (Ctxs 32 16))
    (hW : Rep16 bbParams.p (-2 ^ 64) 2013265985 x W) :
    Rep16 bbParams.p (-2 ^ 64) 2013265985 (BabyBear.poseidon2BabyBearPermute x)
      ((permProg bbParams bbPermChain64 [true, true] bbRc).denote W) := by
  rw [← Poseidon2BabyBearTie.permute_bbParams_eq]
  exact permProg_spec bbParams bbPermChain64 [true, true] rfl (κ' := 442368000)
    (by decide +kernel) bbRc bbRc_ok x W hW

/-- **The KoalaBear permutation on the 64-bit Plantard block.** Input lanes at most
`p + 64` representing `x` with factor `−2 ^ 64` give output lanes at most `p + 64`
representing `KoalaBear.permute x`. -/
theorem kbPermProg64_spec (x : Fin 16 → ZMod KoalaBear.P) (W : Valuation (Ctxs 32 16))
    (hW : Rep16 KoalaBear.P (-2 ^ 64) 2130706497 x W) :
    Rep16 KoalaBear.P (-2 ^ 64) 2130706497 (KoalaBear.permute x)
      ((permProg KoalaBear.params kbPermChain64 [true] kbRc).denote W) :=
  permProg_spec KoalaBear.params kbPermChain64 [true] rfl (κ' := 524386048)
    (by decide +kernel) kbRc kbRc_ok x W hW

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowFieldPlant64
