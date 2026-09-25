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

## The FRI fold over the extension

The arity-2 FRI fold step of the reference STARK (`fri_fold` in `plonky3-hax`,
`p_even + α · p_odd` with `p_even = (f(x) + f(−x)) · 2⁻¹` and
`p_odd = (f(x) − f(−x)) · (2x)⁻¹`), with `f(x)`, `f(−x)` and the challenge `β` in the
extension and the scalars `2⁻¹`, `(2x)⁻¹` in the base field:

```
fold = (f(x) + f(−x)) · inv2 + β · ((f(x) − f(−x)) · (2x)⁻¹)
```

* `foldExpr W inv2 k`: coordinate `k` of the fold over thirteen inputs (`f(x)` at
  `0 .. 3`, `f(−x)` at `4 .. 7`, `β` at `8 .. 11`, `(2x)⁻¹` at `12`); the difference
  `u − v` is compiled as `u + (−1) · v`.
* `extFold W inv2 lo hi β s`: its coordinates as a function.
* `toExt_extFold`: `toExt` of the coordinates is the fold in `F[X]/(X⁴ − W)`.
* `foldJasmin_spec`, `babyBear_foldJasmin_spec`: the lowered program of coordinate `k`
  returns the encoding of coordinate `k` of the fold.
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

/-! ## 5. The FRI fold over the extension -/

section Fold

/-- Coordinate `k` of the product of the elements with coordinate expressions `x`
    and `y`. -/
def mulOf {n : Nat} (x y : Fin 4 → FExpr p n) : Fin 4 → FExpr p n
  | 0 => .add (.mul (x 0) (y 0))
      (.mul (.const W) (.add (.add (.mul (x 1) (y 3)) (.mul (x 2) (y 2))) (.mul (x 3) (y 1))))
  | 1 => .add (.add (.mul (x 0) (y 1)) (.mul (x 1) (y 0)))
      (.mul (.const W) (.add (.mul (x 2) (y 3)) (.mul (x 3) (y 2))))
  | 2 => .add (.add (.add (.mul (x 0) (y 2)) (.mul (x 1) (y 1))) (.mul (x 2) (y 0)))
      (.mul (.const W) (.mul (x 3) (y 3)))
  | 3 => .add (.add (.add (.mul (x 0) (y 3)) (.mul (x 1) (y 2))) (.mul (x 2) (y 1)))
      (.mul (x 3) (y 0))

theorem mulExpr_eq_mulOf (k : Fin 4) : mulExpr W k = mulOf W a b k := by
  fin_cases k <;> rfl

theorem mulOf_eval {n : Nat} (x y : Fin 4 → FExpr p n) (z : Fin n → ZMod p) (k : Fin 4) :
    (mulOf W x y k).eval z = extMul W (fun i => (x i).eval z) (fun i => (y i).eval z) k := by
  fin_cases k <;> rfl

/-- Coordinate `i` of the evaluation `f(x)`: input `i`. -/
def foldLo (i : Fin 4) : FExpr p 13 := .inp ⟨i.val, by omega⟩

/-- Coordinate `i` of the evaluation `f(−x)`: input `4 + i`. -/
def foldHi (i : Fin 4) : FExpr p 13 := .inp ⟨4 + i.val, by omega⟩

/-- Coordinate `i` of the challenge `β`: input `8 + i`. -/
def foldBeta (i : Fin 4) : FExpr p 13 := .inp ⟨8 + i.val, by omega⟩

/-- The base-field scalar `(2x)⁻¹`: input `12`. -/
def foldHip : FExpr p 13 := .inp 12

/-- Coordinate `j` of `(f(x) − f(−x)) · (2x)⁻¹`. -/
def foldDiff (j : Fin 4) : FExpr p 13 :=
  .mul (.add (foldLo j) (.mul (.const (-1)) (foldHi j))) foldHip

/-- Coordinate `k` of the fold `(f(x) + f(−x)) · inv2 + β · ((f(x) − f(−x)) · (2x)⁻¹)`. -/
def foldExpr (inv2 : ZMod p) (k : Fin 4) : FExpr p 13 :=
  .add (.mul (.add (foldLo k) (foldHi k)) (.const inv2)) (mulOf W foldBeta foldDiff k)

/-- The coordinates of `(lo + hi) · inv2 + β · ((lo − hi) · s)`, for extension elements
    `lo`, `hi`, `β` and base-field scalars `inv2`, `s`. -/
def extFold (inv2 : ZMod p) (lo hi β : Fin 4 → ZMod p) (s : ZMod p) : Fin 4 → ZMod p :=
  fun k => (lo k + hi k) * inv2 + extMul W β (fun j => (lo j - hi j) * s) k

/-- The evaluation `f(x)` read from the thirteen inputs. -/
def loOf (z : Fin 13 → ZMod p) (i : Fin 4) : ZMod p := z ⟨i.val, by omega⟩

/-- The evaluation `f(−x)` read from the thirteen inputs. -/
def hiOf (z : Fin 13 → ZMod p) (i : Fin 4) : ZMod p := z ⟨4 + i.val, by omega⟩

/-- The challenge `β` read from the thirteen inputs. -/
def betaOf (z : Fin 13 → ZMod p) (i : Fin 4) : ZMod p := z ⟨8 + i.val, by omega⟩

theorem foldExpr_eval (inv2 : ZMod p) (z : Fin 13 → ZMod p) (k : Fin 4) :
    (foldExpr W inv2 k).eval z = extFold W inv2 (loOf z) (hiOf z) (betaOf z) (z 12) k := by
  simp only [foldExpr, FExpr.eval, mulOf_eval, extFold]
  congr 2
  funext j
  simp only [foldDiff, FExpr.eval, foldLo, foldHi, foldHip, loOf, hiOf]
  ring

theorem toExt_add (c d : Fin 4 → ZMod p) :
    toExt W (fun k => c k + d k) = toExt W c + toExt W d := by
  simp only [toExt, map_add]; ring

theorem toExt_sub (c d : Fin 4 → ZMod p) :
    toExt W (fun k => c k - d k) = toExt W c - toExt W d := by
  simp only [toExt, map_sub]; ring

theorem toExt_mul_of (c : Fin 4 → ZMod p) (s : ZMod p) :
    toExt W (fun k => c k * s) = toExt W c * AdjoinRoot.of _ s := by
  simp only [toExt, map_mul]; ring

/-- **The fold coordinates compute the fold in `F[X]/(X⁴ − W)`.** -/
theorem toExt_extFold (inv2 : ZMod p) (lo hi β : Fin 4 → ZMod p) (s : ZMod p) :
    toExt W (extFold W inv2 lo hi β s) =
      (toExt W lo + toExt W hi) * AdjoinRoot.of _ inv2 +
        toExt W β * ((toExt W lo - toExt W hi) * AdjoinRoot.of _ s) := by
  have h := toExt_add W (fun k => (lo k + hi k) * inv2)
    (extMul W β (fun j => (lo j - hi j) * s))
  rw [show (fun k => (lo k + hi k) * inv2 + extMul W β (fun j => (lo j - hi j) * s) k)
    = extFold W inv2 lo hi β s from rfl] at h
  rw [h, toExt_mul_of W (fun k => lo k + hi k), toExt_add, toExt_extMul,
    toExt_mul_of W (fun k => lo k - hi k), toExt_sub]

/-- The lowered program of coordinate `k` of the fold, through `F`. -/
def foldJasmin (F : SingleWordField p) (inv2 : ZMod p) (k : Fin 4) :
    Com jasminDialect (mapCtxW (inCtxt p 13)) (mapTyW (.fp p)) :=
  compileJasmin F (foldExpr W inv2 k)

/-- **Correctness of the lowered fold.** On the encoding of any valuation `V` of the
    thirteen inputs, the lowered program of coordinate `k` returns the encoding of
    coordinate `k` of the fold, which `toExt_extFold` identifies with the fold in
    `F[X]/(X⁴ − W)`. -/
theorem foldJasmin_spec (F : SingleWordField p) (inv2 : ZMod p)
    (V : Ctxt.Valuation (inCtxt p 13)) (k : Fin 4) :
    (foldJasmin W F inv2 k).denote (mapValW F V) =
      F.enc (extFold W inv2 (loOf (inputs V)) (hiOf (inputs V)) (betaOf (inputs V))
        (inputs V 12) k) := by
  rw [foldJasmin, compileJasmin_denote, foldExpr_eval]

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord in
/-- BabyBear's quartic extension fold, `X⁴ = 11`, with `inv2 = 2⁻¹`. -/
theorem babyBear_foldJasmin_spec (V : Ctxt.Valuation (inCtxt BabyBear.P 13)) (k : Fin 4) :
    (foldJasmin 11 BabyBear.babyBear 2⁻¹ k).denote (mapValW BabyBear.babyBear V) =
      BabyBear.babyBear.enc (extFold 11 2⁻¹ (loOf (inputs V)) (hiOf (inputs V))
        (betaOf (inputs V)) (inputs V 12) k) :=
  foldJasmin_spec 11 BabyBear.babyBear 2⁻¹ V k

end Fold

end CatCrypt.Crypto.SecureCompilation.Algebraic.BinomialExt4
