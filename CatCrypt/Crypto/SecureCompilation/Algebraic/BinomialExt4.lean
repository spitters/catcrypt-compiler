/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldExprCompile
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.KoalaBear
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.BabyBear
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Multiplication in the binomial extension `F[X]/(X⁴ − W)`

The degree-4 binomial extension of `ZMod p` by `X⁴ = W` (Plonky3's
`BinomialExtensionField<F, 4>`, with `W = 11` over BabyBear and `W = 3` over
KoalaBear), with elements written `c₀ + c₁X + c₂X² + c₃X³`. Coordinate `k` of the
product is the expression `mulExpr W k` in the eight coordinates of the factors:

```
c₀ = a₀b₀ + W(a₁b₃ + a₂b₂ + a₃b₁)
c₁ = a₀b₁ + a₁b₀ + W(a₂b₃ + a₃b₂)
c₂ = a₀b₂ + a₁b₁ + a₂b₀ + W a₃b₃
c₃ = a₀b₃ + a₁b₂ + a₂b₁ + a₃b₀
```

It is compiled by `FieldExprCompile.compile` to a `Com fieldDialect` program over
eight inputs and lowered through a single-word field.

## Main definitions

* `Ext W`: the ring `AdjoinRoot (X⁴ − C W)`; `toExt W c` is the element with
  coordinates `c`.
* `mulExpr W k`, `extMul W a b`: coordinate `k` of the product, as an expression and
  as a function of the coordinates.
* `mulJasmin W F k`: the lowered program of coordinate `k`.

## Main results

* `toExt_extMul`: `toExt W (extMul W a b) = toExt W a * toExt W b`.
* `mulJasmin_spec`: for every valuation of the eight inputs, the lowered program of
  coordinate `k` returns the encoding of coordinate `k` of the product of the two
  input elements.
* `koalaBear_mulJasmin_spec`, `babyBear_mulJasmin_spec`: the instances `W = 3`
  over KoalaBear and `W = 11` over BabyBear.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.BinomialExt4

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldExprCompile
open Polynomial

variable {p : Nat} (W : ZMod p)

/-! ## 1. The ring -/

/-- The ring `ZMod p [X] / (X⁴ − W)`. -/
abbrev Ext : Type := AdjoinRoot (X ^ 4 - C W : (ZMod p)[X])

/-- The element `c₀ + c₁X + c₂X² + c₃X³`. -/
noncomputable def toExt (c : Fin 4 → ZMod p) : Ext W :=
  AdjoinRoot.of _ (c 0) + AdjoinRoot.of _ (c 1) * AdjoinRoot.root _ +
    AdjoinRoot.of _ (c 2) * AdjoinRoot.root _ ^ 2 + AdjoinRoot.of _ (c 3) * AdjoinRoot.root _ ^ 3

theorem root_pow_four : (AdjoinRoot.root (X ^ 4 - C W)) ^ 4 = AdjoinRoot.of (X ^ 4 - C W) W := by
  have h := AdjoinRoot.eval₂_root (X ^ 4 - C W : (ZMod p)[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

/-! ## 2. The product coordinates -/

/-- Coordinate `i` of the first factor: input `i`. -/
def a (i : Fin 4) : FExpr p 8 := .inp ⟨i.val, by omega⟩

/-- Coordinate `i` of the second factor: input `4 + i`. -/
def b (i : Fin 4) : FExpr p 8 := .inp ⟨4 + i.val, by omega⟩

/-- Coordinate `k` of the product, as an expression in the eight input coordinates. -/
def mulExpr : Fin 4 → FExpr p 8
  | 0 => .add (.mul (a 0) (b 0))
      (.mul (.const W) (.add (.add (.mul (a 1) (b 3)) (.mul (a 2) (b 2))) (.mul (a 3) (b 1))))
  | 1 => .add (.add (.mul (a 0) (b 1)) (.mul (a 1) (b 0)))
      (.mul (.const W) (.add (.mul (a 2) (b 3)) (.mul (a 3) (b 2))))
  | 2 => .add (.add (.add (.mul (a 0) (b 2)) (.mul (a 1) (b 1))) (.mul (a 2) (b 0)))
      (.mul (.const W) (.mul (a 3) (b 3)))
  | 3 => .add (.add (.add (.mul (a 0) (b 3)) (.mul (a 1) (b 2))) (.mul (a 2) (b 1)))
      (.mul (a 3) (b 0))

/-- The eight inputs of the factors `x` and `y`. -/
def inputs8 (x y : Fin 4 → ZMod p) : Fin 8 → ZMod p := fun i =>
  if h : i.val < 4 then x ⟨i.val, h⟩ else y ⟨i.val - 4, by omega⟩

/-- The coordinates of the product of `x` and `y`. -/
def extMul (x y : Fin 4 → ZMod p) : Fin 4 → ZMod p
  | 0 => x 0 * y 0 + W * (x 1 * y 3 + x 2 * y 2 + x 3 * y 1)
  | 1 => x 0 * y 1 + x 1 * y 0 + W * (x 2 * y 3 + x 3 * y 2)
  | 2 => x 0 * y 2 + x 1 * y 1 + x 2 * y 0 + W * (x 3 * y 3)
  | 3 => x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0

theorem mulExpr_eval (x y : Fin 4 → ZMod p) (k : Fin 4) :
    (mulExpr W k).eval (inputs8 x y) = extMul W x y k := by
  fin_cases k <;> rfl

/-- **The coordinates compute the product in `F[X]/(X⁴ − W)`.** -/
theorem toExt_extMul (x y : Fin 4 → ZMod p) :
    toExt W (extMul W x y) = toExt W x * toExt W y := by
  have h := root_pow_four W
  simp only [toExt, extMul, map_add, map_mul]
  set r := AdjoinRoot.root (X ^ 4 - C W)
  set f := AdjoinRoot.of (X ^ 4 - C W)
  linear_combination (-(f (x 1) * f (y 3) + f (x 2) * f (y 2) + f (x 3) * f (y 1) +
    (f (x 2) * f (y 3) + f (x 3) * f (y 2)) * r + f (x 3) * f (y 3) * r ^ 2)) * h

theorem inputs8_split (z : Fin 8 → ZMod p) :
    inputs8 (fun i => z ⟨i.val, by omega⟩) (fun i => z ⟨4 + i.val, by omega⟩) = z := by
  funext i
  unfold inputs8
  split_ifs with h
  · rfl
  · exact congrArg z (Fin.ext (by simp only; omega))

/-! ## 3. The lowered programs -/

/-- The first factor of a valuation of the eight inputs: inputs `0 .. 3`. -/
def fst (V : Ctxt.Valuation (inCtxt p 8)) (i : Fin 4) : ZMod p := inputs V ⟨i.val, by omega⟩

/-- The second factor of a valuation of the eight inputs: inputs `4 .. 7`. -/
def snd (V : Ctxt.Valuation (inCtxt p 8)) (i : Fin 4) : ZMod p :=
  inputs V ⟨4 + i.val, by omega⟩

/-- The lowered program of coordinate `k` of the product, through `F`. -/
def mulJasmin (F : SingleWordField p) (k : Fin 4) :
    Com jasminDialect (mapCtxW (inCtxt p 8)) (mapTyW (.fp p)) :=
  compileJasmin F (mulExpr W k)

/-- **Correctness of the lowered multiplication.** On the encoding of any valuation
    `V` of the eight inputs, the lowered program of coordinate `k` returns the
    encoding of coordinate `k` of the product of `fst V` and `snd V`, whose
    coordinates `toExt_extMul` identifies with the product in `F[X]/(X⁴ − W)`. -/
theorem mulJasmin_spec (F : SingleWordField p) (V : Ctxt.Valuation (inCtxt p 8)) (k : Fin 4) :
    (mulJasmin W F k).denote (mapValW F V) = F.enc (extMul W (fst V) (snd V) k) := by
  rw [mulJasmin, compileJasmin_denote, ← mulExpr_eval]
  exact congrArg (fun z => F.enc ((mulExpr W k).eval z)) (inputs8_split (inputs V)).symm

/-! ## 4. KoalaBear and BabyBear -/

section Instances

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord

/-- KoalaBear's quartic extension, `X⁴ = 3`. -/
theorem koalaBear_mulJasmin_spec (V : Ctxt.Valuation (inCtxt KoalaBear.P 8)) (k : Fin 4) :
    (mulJasmin 3 KoalaBear.koalaBear k).denote (mapValW KoalaBear.koalaBear V) =
      KoalaBear.koalaBear.enc (extMul 3 (fst V) (snd V) k) :=
  mulJasmin_spec 3 KoalaBear.koalaBear V k

/-- BabyBear's quartic extension, `X⁴ = 11`. -/
theorem babyBear_mulJasmin_spec (V : Ctxt.Valuation (inCtxt BabyBear.P 8)) (k : Fin 4) :
    (mulJasmin 11 BabyBear.babyBear k).denote (mapValW BabyBear.babyBear V) =
      BabyBear.babyBear.enc (extMul 11 (fst V) (snd V) k) :=
  mulJasmin_spec 11 BabyBear.babyBear V k

end Instances

end CatCrypt.Crypto.SecureCompilation.Algebraic.BinomialExt4
