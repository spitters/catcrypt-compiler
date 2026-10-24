/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs

/-!
# The product of a binomial extension as `fieldDialect` code

For a degree `n`, a modulus `p` and an integer `ξ`, the product of
`F_p[v]/(vⁿ − ξ)` on coefficient vectors is
`(x * y) k = Σ_{i+j=k} x i * y j + ξ * Σ_{i+j=k+n} x i * y j`. The module defines that
product as a multi-result program of `fieldDialect` in two stages of expressions, as
the `Fp2` instructions of `TowerDialect` (`stepN`): the first stage binds the `n * n`
coefficient products `x i * y j`, each once; the second binds, for each `k`, the sum of
the products with `i + j = k` plus `ξ` times the sum of the products with
`i + j = k + n`. The program is identified with `ExtDesc.mul` of the descriptor
`ExtDesc.ext n (.prime p) [ξ]` for every `n`.

## Main results

* `sumE`, `sumE_eval`: the sum of a list of expressions and its value.
* `prodE`, `outE`: the expressions of the first and of the second stage.
* `descMul_eq`: coefficient `k` of `ExtDesc.mul` at `ExtDesc.ext n (.prime p) [ξ]` as two
  sums over ranges.
* `outE_eval`: the value of the second stage over the values of the first is
  `ExtDesc.mul`.
* `binomStep`, `binomStep_denote`, `binomStep_cov`: the program in continuation form over
  `n + n` coordinate variables, its denotation and its `ArithAt p`-coverage.
* `encVec`, `binomBlk`, `binomBlk_denote`, `binomBlk_cov`: the closed block over the
  `n` coordinates of each operand, with the coordinates of `ExtDesc.mul` as its value.
* `binomBlk_limbs`: over a block template of the base field at `p`, the lowered block maps
  the limbs of the coordinates of the operands to the limbs of the coordinates of the
  product.
* `binomBlk_two`: at `n = 2` the block and the `Fp2` multiply block of `towerToField` have
  the same denotation.
* `FExpr.ops`, `FExpr.muls`, `binomOps`, `binomMuls`: the numbers of bindings and of
  products; `quarticBabyBear_ops`, `quarticBabyBear_muls`: 34 bindings, 19 of them
  products, at `n = 4`, `p = 2013265921`, `ξ = 11`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ExtBinomial

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

variable {p : Nat}

/-! ## 1. Sums of expressions -/

/-- The sum of a list of expressions, with one `add` per element after the first; the
    constant `0` for the empty list. -/
def sumE {m : Nat} : List (FExpr p m) → FExpr p m
  | [] => .const 0
  | a :: l => l.foldl .add a

theorem foldl_add_eval {m : Nat} (v : Fin m → ZMod p) (l : List (FExpr p m)) (a : FExpr p m) :
    (l.foldl FExpr.add a).eval v = a.eval v + (l.map fun e => e.eval v).sum := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, FExpr.eval, add_assoc]

/-- The value of a sum of expressions. -/
theorem sumE_eval {m : Nat} (v : Fin m → ZMod p) (l : List (FExpr p m)) :
    (sumE l).eval v = (l.map fun e => e.eval v).sum := by
  cases l with
  | nil => rfl
  | cons a l => rw [sumE, foldl_add_eval, List.map_cons, List.sum_cons]

/-- The sum of a function over a list range is the sum over the finite range. -/
theorem sum_map_range (f : Nat → ZMod p) (m : Nat) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-! ## 2. The two stages -/

/-- Coefficient `i` of a vector of length `n`, zero for `i ≥ n`. -/
def rd {n : Nat} (x : Fin n → ZMod p) (i : Nat) : ZMod p :=
  if h : i < n then x ⟨i, h⟩ else 0

/-- First stage, over the coordinates of `x` then those of `y`: entry `(i, j)` is
    `x i * y j`. -/
def prodE (n : Nat) (q : Fin (n * n)) : FExpr p (n + n) :=
  .mul (.inp (Fin.castAdd n (finProdFinEquiv.symm q).1))
    (.inp (Fin.natAdd n (finProdFinEquiv.symm q).2))

/-- The values of the first stage at the operands `x` and `y`. -/
def prodVal (n : Nat) (x y : Fin n → ZMod p) (q : Fin (n * n)) : ZMod p :=
  (prodE n q).eval (Fin.append x y)

/-- The first-stage value `x i * y j`, the constant `0` out of range. -/
def prodAt (n i j : Nat) : FExpr p (n * n) :=
  if h : i < n ∧ j < n then .inp (finProdFinEquiv (⟨i, h.1⟩, ⟨j, h.2⟩)) else .const 0

theorem prodAt_eval (n : Nat) (x y : Fin n → ZMod p) (i j : Nat) :
    (prodAt n i j).eval (prodVal n x y) = rd x i * rd y j := by
  unfold prodAt
  split
  · next h =>
    simp only [FExpr.eval, prodVal, prodE, Equiv.symm_apply_apply, Fin.append_left,
      Fin.append_right, rd, dite_eq_left h.1, dite_eq_left h.2]
  · next h =>
    by_cases hi : i < n
    · have hj : ¬ j < n := fun hj => h ⟨hi, hj⟩
      simp only [FExpr.eval, rd, dite_eq_right hj, mul_zero]
    · simp only [FExpr.eval, rd, dite_eq_right hi, zero_mul]

/-- The products `x i * y j` with `i + j = k`, for `k < n`. -/
def lowTerms (n k : Nat) : List (FExpr p (n * n)) :=
  (List.range (k + 1)).map fun i => prodAt n i (k - i)

/-- The products `x i * y j` with `i + j = k + n`, for `k < n`. -/
def highTerms (n k : Nat) : List (FExpr p (n * n)) :=
  (List.range (n - 1 - k)).map fun t => prodAt n (k + 1 + t) (n - 1 - t)

/-- Second stage, over the values of the first: coefficient `k` of the product. The
    coefficient `n − 1` has no product with `i + j = k + n` and is the first sum alone. -/
def outE (n : Nat) (ξ : Int) (k : Fin n) : FExpr p (n * n) :=
  if k.val + 1 < n then FExpr.addSc ξ (sumE (lowTerms n k.val)) (sumE (highTerms n k.val))
  else sumE (lowTerms n k.val)

theorem lowTerms_eval (n k : Nat) (x y : Fin n → ZMod p) :
    (sumE (lowTerms n k)).eval (prodVal n x y)
      = ∑ i ∈ Finset.range (k + 1), rd x i * rd y (k - i) := by
  rw [sumE_eval, lowTerms, List.map_map, ← sum_map_range]
  exact congrArg List.sum (List.map_congr_left fun i _ => prodAt_eval n x y i (k - i))

theorem highTerms_eval (n k : Nat) (x y : Fin n → ZMod p) :
    (sumE (highTerms n k)).eval (prodVal n x y)
      = ∑ t ∈ Finset.range (n - 1 - k), rd x (k + 1 + t) * rd y (n - 1 - t) := by
  rw [sumE_eval, highTerms, List.map_map, ← sum_map_range]
  exact congrArg List.sum
    (List.map_congr_left fun t _ => prodAt_eval n x y (k + 1 + t) (n - 1 - t))

/-- The value of the second stage as two sums over ranges. -/
theorem outE_eval_sums (n : Nat) (ξ : Int) (x y : Fin n → ZMod p) (k : Fin n) :
    (outE n ξ k).eval (prodVal n x y)
      = (∑ i ∈ Finset.range (k.val + 1), rd x i * rd y (k.val - i))
        + (ξ : ZMod p)
          * ∑ t ∈ Finset.range (n - 1 - k.val), rd x (k.val + 1 + t) * rd y (n - 1 - t) := by
  unfold outE
  split
  · rw [FExpr.addSc_eval, lowTerms_eval, highTerms_eval]
  · next h =>
    have h0 : n - 1 - k.val = 0 := by omega
    rw [lowTerms_eval, h0, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]

/-! ## 3. The descriptor's product -/

/-- The descriptor's sum at a prime field is the sum over the finite range. -/
theorem descSum_eq (m : Nat) (f : Nat → ZMod p) :
    ExtDesc.sum (.prime p) m f = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem sum_range_split (f : Nat → ZMod p) (n k : Nat) (hk : k < n) :
    ∑ i ∈ Finset.range n, f i
      = (∑ i ∈ Finset.range (k + 1), f i) + ∑ t ∈ Finset.range (n - 1 - k), f (k + 1 + t) := by
  have h := Finset.sum_range_add f (k + 1) (n - 1 - k)
  rwa [show k + 1 + (n - 1 - k) = n by omega] at h

theorem sum_ite_low (a b : Nat → ZMod p) (n i k j₀ : Nat) (hj : j₀ < n) (h : i + j₀ = k) :
    (∑ j ∈ Finset.range n, if i + j = k then a j else if i + j = k + n then b j else 0)
      = a j₀ := by
  rw [Finset.sum_eq_single j₀]
  · rw [ite_eq_left h]
  · intro j hj' hne
    have hlt := Finset.mem_range.mp hj'
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro h'
    exact absurd (Finset.mem_range.mpr hj) h'

theorem sum_ite_high (a b : Nat → ZMod p) (n i k j₀ : Nat) (hj : j₀ < n)
    (h : i + j₀ = k + n) :
    (∑ j ∈ Finset.range n, if i + j = k then a j else if i + j = k + n then b j else 0)
      = b j₀ := by
  rw [Finset.sum_eq_single j₀]
  · rw [ite_eq_right (by omega), ite_eq_left h]
  · intro j hj' hne
    have hlt := Finset.mem_range.mp hj'
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro h'
    exact absurd (Finset.mem_range.mpr hj) h'

/-- **Coefficient `k` of the descriptor's product** at `F_p[v]/(vⁿ − ξ)`: the sum of
    `x i * y (k − i)` over `i ≤ k`, plus `ξ` times the sum of `x i * y (k + n − i)` over
    `k < i < n`. -/
theorem descMul_eq (n : Nat) (ξ : Int) (x y : Fin n → ZMod p) (k : Fin n) :
    (ExtDesc.ext n (.prime p) [ξ]).mul x y k
      = (∑ i ∈ Finset.range (k.val + 1), rd x i * rd y (k.val - i))
        + (ξ : ZMod p)
          * ∑ t ∈ Finset.range (n - 1 - k.val), rd x (k.val + 1 + t) * rd y (n - 1 - t) := by
  have hk := k.isLt
  show ExtDesc.sum (.prime p) n (fun i => ExtDesc.sum (.prime p) n fun j =>
      if i + j = k.val then rd x i * rd y j
      else if i + j = k.val + n then (ξ : ZMod p) * (rd x i * rd y j)
      else 0) = _
  simp only [descSum_eq]
  rw [sum_range_split _ n k.val hk, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_)
    (Finset.sum_congr rfl fun t ht => ?_)
  · have hi' := Finset.mem_range.mp hi
    exact sum_ite_low (fun j => rd x i * rd y j) (fun j => (ξ : ZMod p) * (rd x i * rd y j))
      n i k.val (k.val - i) (by omega) (by omega)
  · have ht' := Finset.mem_range.mp ht
    exact sum_ite_high (fun j => rd x (k.val + 1 + t) * rd y j)
      (fun j => (ξ : ZMod p) * (rd x (k.val + 1 + t) * rd y j))
      n (k.val + 1 + t) k.val (n - 1 - t) (by omega) (by omega)

/-- **The two stages compute the descriptor's product**, for every degree. -/
theorem outE_eval (n : Nat) (ξ : Int) (x y : Fin n → ZMod p) (k : Fin n) :
    (outE n ξ k).eval (prodVal n x y) = (ExtDesc.ext n (.prime p) [ξ]).mul x y k :=
  (outE_eval_sums n ξ x y k).trans (descMul_eq n ξ x y k).symm

/-! ## 4. The program in continuation form -/

/-- The product over the `n + n` coordinate variables `env` (those of `x`, then those of
    `y`): the first stage binds the `n * n` coefficient products, the second the `n`
    coordinates of the product, handed to the continuation. -/
def binomStep {ts : List FieldTy} (n : Nat) (ξ : Int) {Γ : Ctxt fieldDialect}
    (env : Fin (n + n) → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin n → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts) :
    MRC Γ ts :=
  emitVecT (n * n) (prodE n) env fun r₁ w =>
    emitVecT n (outE n ξ) w fun r₂ c => k (fun v => r₂ (r₁ v)) c

/-- **Denotation of `binomStep`.** If `env` holds the coordinates of `x` then those of `y`
    and the continuation denotes `R` whenever its renaming preserves values and its
    variables hold the coordinates of the descriptor's product, then the program denotes
    `R`. -/
theorem binomStep_denote {ts : List FieldTy} (n : Nat) (ξ : Int) (x y : Fin n → ZMod p)
    {Γ : Ctxt fieldDialect} (env : Fin (n + n) → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin n → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts)
    (V : Ctxt.Valuation Γ) (R : ListDenote ts)
    (hx : ∀ i, (env i).lookup V = Fin.append x y i)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ')
      (c : Fin n → Ctxt.Var Γ' (.fp p)), Preserves r V V' →
      (∀ j, (c j).lookup V' = (ExtDesc.ext n (.prime p) [ξ]).mul x y j) →
      (k r c).denote V' = R) :
    (binomStep n ξ env k).denote V = R := by
  refine emitVecT_denote (Fin.append x y) (n * n) (prodE n) env _ V R hx
    fun r₁ V₁ w h₁ hw => ?_
  refine emitVecT_denote (prodVal n x y) n (outE n ξ) w _ V₁ R hw fun r₂ V₂ c h₂ hc => ?_
  exact hk _ V₂ c (Preserves.comp h₁ h₂) fun j => (hc j).trans (outE_eval n ξ x y j)

/-- `binomStep` is `ArithAt p`-covered when its continuation is. -/
theorem binomStep_cov {ts : List FieldTy} (n : Nat) (ξ : Int) {Γ : Ctxt fieldDialect}
    (env : Fin (n + n) → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin n → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (c : Fin n → Ctxt.Var Γ' (.fp p)),
      CoveredM (ArithAt p) (k r c)) :
    CoveredM (ArithAt p) (binomStep n ξ env k) :=
  emitVecT_cov (n * n) (prodE n) env _ fun _ w =>
    emitVecT_cov n (outE n ξ) w _ fun _ _ => hk _ _

/-! ## 5. The closed block -/

variable (p) in
/-- The context of the block: the `n` coordinates of the first operand, then those of the
    second. -/
abbrev binomCtx (n : Nat) : Ctxt fieldDialect :=
  List.replicate n (FieldTy.fp p) ++ (List.replicate n (FieldTy.fp p) ++ [])

/-- The valuation of `n` coordinates. -/
def encVec : (n : Nat) → (Fin n → ZMod p) →
    Ctxt.Valuation (List.replicate n (FieldTy.fp p) : Ctxt fieldDialect)
  | 0, _ => .nil
  | n + 1, x => .cons (x 0) (encVec n fun j => x j.succ)

/-- The vector of `n` coordinate variables. -/
def coordVars {Γ : Ctxt fieldDialect} : (n : Nat) → (Fin n → Ctxt.Var Γ (.fp p)) →
    HVector (fun t => Ctxt.Var Γ t) (List.replicate n (FieldTy.fp p))
  | 0, _ => .nil
  | n + 1, c => .cons (c 0) (coordVars n fun j => c j.succ)

theorem lookupVars_coordVars {Γ : Ctxt fieldDialect} (V : Ctxt.Valuation Γ) :
    ∀ (n : Nat) (c : Fin n → Ctxt.Var Γ (.fp p)),
      MultiReturnCom.lookupVars (coordVars n c) V = encVec n (fun j => (c j).lookup V)
  | 0, _ => rfl
  | n + 1, c => by
    show HVector.cons _ (MultiReturnCom.lookupVars (coordVars n _) V) = _
    rw [lookupVars_coordVars V n]
    rfl

theorem lookup_regVar_encVec :
    ∀ (n : Nat) (x : Fin n → ZMod p) (i : Fin n),
      (regVar (τ := FieldTy.fp p) n i).lookup (encVec n x) = x i
  | _ + 1, _, ⟨0, _⟩ => rfl
  | n + 1, x, ⟨j + 1, h⟩ => lookup_regVar_encVec n (fun j => x j.succ) ⟨j, by omega⟩

variable (p) in
/-- The coordinate variables of the two operands in the context of the block. -/
def binomEnv (n : Nat) : Fin (n + n) → Ctxt.Var (binomCtx p n) (.fp p) :=
  Fin.append (fun i => inlHom _ (regVar n i))
    (fun i => inrHom (List.replicate n (FieldTy.fp p)) (inlHom [] (regVar n i)))

/-- The valuation of the block's context holding the coordinates of `x` and of `y`. -/
def encPair (n : Nat) (x y : Fin n → ZMod p) : Ctxt.Valuation (binomCtx p n) :=
  hvAppend (encVec n x) (hvAppend (encVec n y) .nil)

theorem lookup_binomEnv (n : Nat) (x y : Fin n → ZMod p) (i : Fin (n + n)) :
    (binomEnv p n i).lookup (encPair n x y) = Fin.append x y i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [binomEnv, Fin.append_left, Fin.append_left, encPair, lookup_inlHom,
      lookup_regVar_encVec]
  · rw [binomEnv, Fin.append_right, Fin.append_right, encPair, lookup_inrHom, lookup_inlHom,
      lookup_regVar_encVec]

variable (p) in
/-- **The block of the product of `F_p[v]/(vⁿ − ξ)`**, from the `n` coordinates of each
    operand to the `n` coordinates of the product. -/
def binomBlk (n : Nat) (ξ : Int) : MRC (binomCtx p n) (List.replicate n (FieldTy.fp p)) :=
  binomStep n ξ (binomEnv p n) fun _ c => .ret (coordVars n c)

/-- **Denotation of the block**: on the coordinates of `x` and `y` its value is the
    coordinates of the descriptor's product. -/
theorem binomBlk_denote (n : Nat) (ξ : Int) (x y : Fin n → ZMod p) :
    (binomBlk p n ξ).denote (encPair n x y)
      = encVec n ((ExtDesc.ext n (.prime p) [ξ]).mul x y) :=
  binomStep_denote n ξ x y _ _ _ _ (lookup_binomEnv n x y) fun _ V' c _ hc => by
    show MultiReturnCom.lookupVars (coordVars n c) V' = _
    rw [lookupVars_coordVars]
    exact congrArg (encVec n) (funext hc)

/-- The block is `ArithAt p`-covered. -/
theorem binomBlk_cov (n : Nat) (ξ : Int) : CoveredM (ArithAt p) (binomBlk p n ξ) :=
  binomStep_cov n ξ _ _ fun _ _ => trivial

/-- **The block over a template of the base field.** For a block template `B` at the
    modulus `p`, the limb lowering of the block maps the limbs of the coordinates of the
    operands to the limbs of the coordinates of the descriptor's product. -/
theorem binomBlk_limbs {m : Nat} (B : LimbBlockTemplate m) (hp : B.p = p) (n : Nat) (ξ : Int)
    (x y : Fin n → ZMod p) :
    ((loweringOf B.blocks).lowerMultiM (binomBlk p n ξ)).denote
        (flatVal B.enc (encPair n x y))
      = flatVal B.enc (encVec n ((ExtDesc.ext n (.prime p) [ξ]).mul x y)) := by
  subst hp
  rw [MultiBlockLoweringData.multiFundamentalM_on (loweringOf B.blocks) B.enc B.Good B.square
    (binomBlk B.p n ξ) (CoveredM.mono (fun _ he => B.arith he) _ (binomBlk_cov n ξ)),
    binomBlk_denote]

/-! ## 6. The quadratic instance -/

/-- **At `n = 2` the block agrees with the `Fp2` multiply block** of `towerToField`: the two
    programs have the same denotation. -/
theorem binomBlk_two (β ξ : Int) (V : Ctxt.Valuation (binomCtx p 2)) :
    (binomBlk p 2 β).denote V = (towerLowerOp (.mul .two p β ξ)).denote V := by
  rcases V with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩
  have hL := binomBlk_denote 2 β (Fp2Val.toDesc β ⟨a, b⟩) (Fp2Val.toDesc β ⟨c, d⟩)
  have hR := opSquare_mul2 p β ξ
    (HVector.cons (⟨a, b⟩ : Fp2Val p) (HVector.cons (⟨c, d⟩ : Fp2Val p) HVector.nil))
  have hm := Fp2Val.toDesc_mulBeta β (⟨a, b⟩ : Fp2Val p) ⟨c, d⟩
  exact (hL.trans (congrArg (encVec 2) hm.symm)).trans hR.symm

/-! ## 7. Operation counts -/

/-- The number of bindings `emitT` emits for an expression. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect.FExpr.ops {n : Nat} :
    FExpr p n → Nat
  | .inp _ => 0
  | .const _ => 1
  | .add a b => a.ops + b.ops + 1
  | .sub a b => a.ops + b.ops + 1
  | .neg a => a.ops + 1
  | .mul a b => a.ops + b.ops + 1

/-- The number of products among the bindings of an expression. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect.FExpr.muls {n : Nat} :
    FExpr p n → Nat
  | .inp _ => 0
  | .const _ => 0
  | .add a b => a.muls + b.muls
  | .sub a b => a.muls + b.muls
  | .neg a => a.muls
  | .mul a b => a.muls + b.muls + 1

variable (p) in
/-- The number of bindings of the block. -/
def binomOps (n : Nat) (ξ : Int) : Nat :=
  ((List.finRange (n * n)).map fun q => (prodE (p := p) n q).ops).sum
    + ((List.finRange n).map fun k => (outE (p := p) n ξ k).ops).sum

variable (p) in
/-- The number of products of the block. -/
def binomMuls (n : Nat) (ξ : Int) : Nat :=
  ((List.finRange (n * n)).map fun q => (prodE (p := p) n q).muls).sum
    + ((List.finRange n).map fun k => (outE (p := p) n ξ k).muls).sum

/-- The BabyBear quartic `F_p[v]/(v⁴ − 11)`, `p = 2013265921`: the block has 34 bindings
    (16 coefficient products, 12 sums, 3 constants `11` and 3 products with them). -/
theorem quarticBabyBear_ops : binomOps 2013265921 4 11 = 34 := by decide

/-- The BabyBear quartic: 19 of the bindings are products. -/
theorem quarticBabyBear_muls : binomMuls 2013265921 4 11 = 19 := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.ExtBinomial
