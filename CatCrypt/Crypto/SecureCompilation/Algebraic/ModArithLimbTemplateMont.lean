/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate

/-!
# The Montgomery limb template of a canonical limb template

`ofCanonMont T k hp hw hpw` is the limb template at the representation `mont k` built from
a limb template `T` at `canon`. It has the carrier, the encoding and the word casts of `T`.
Addition, subtraction, negation and doubling are the bodies of `T`. Montgomery
multiplication of `a` and `b` is the multiplication body of `T` on `a` and `b`, followed by
the multiplication body of `T` with the literal `(2 ^ k)⁻¹` of `ZMod p`; squaring is
Montgomery multiplication of the argument with itself. The literal is the cast block
`T.ofWords 64 T.limbs` applied to a stack array of the 64-bit words of the literal, so the
template requires that `T` has this cast block and that `p ≤ 2 ^ (64 * T.limbs)`.

## Main definitions

* `ModArithLimbTemplate.fillArr`, `ModArithLimbTemplate.litArr`: the stack array of the
  words of a natural number, built by stores at constant indices.
* `ModArithLimbTemplate.ofCanonMontMul`: Montgomery multiplication on two carriers at a
  literal of `ZMod p`.
* `ModArithLimbTemplate.ofCanonMont`: the template at `mont k`.

## Main results

* `ModArithLimbTemplate.ctLeak_spliceCom`: the events of a splice are the events of its two
  parts.
* `ModArithLimbTemplate.litArr_denote`: the array is the words of the number.
* `ModArithLimbTemplate.ofCanonMontMul_denote`: the value of Montgomery multiplication.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain (radixParams)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
  (spliceCom spliceCom_denote substHeadHom pullV pullV_substHeadHom pullV_lift_weakenOne)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (consHom)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open Ctxt (Var Valuation)
open _root_.Hax.FieldTag (FieldMethod)

namespace ModArithLimbTemplate

/-! ## 1. Events of a splice -/

/-- The events of `spliceCom c k` are the events of `c` followed by the events of `k` at
    the valuation extended by the value of `c`. -/
theorem ctLeak_spliceCom (M : LeakModel jasminDialect) : {Γ : Ctxt jasminDialect} →
    {t s : JasminTy} → (c : Com jasminDialect Γ t) → (k : Com jasminDialect (t :: Γ) s) →
    (V : Valuation Γ) →
    ComLevelCheck.Com.ctLeak M (spliceCom c k) V =
      ComLevelCheck.Com.ctLeak M c V ++
        ComLevelCheck.Com.ctLeak M k (V.extend (c.denote V))
  | _, _, _, .ret v, k, V => by
      simp [spliceCom, NFProg.Com.ctLeak_rename_pullV, pullV_substHeadHom,
        ComLevelCheck.Com.ctLeak]
      rfl
  | _, _, _, .var e body, k, V => by
      show ComLevelCheck.Expr.ctLeak M e V ++
          ComLevelCheck.Com.ctLeak M
            (spliceCom body (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ _)) k))
            (V.extend (e.denote V)) =
        (ComLevelCheck.Expr.ctLeak M e V ++
          ComLevelCheck.Com.ctLeak M body (V.extend (e.denote V))) ++
          ComLevelCheck.Com.ctLeak M k (V.extend (body.denote (V.extend (e.denote V))))
      rw [ctLeak_spliceCom M body, NFProg.Com.ctLeak_rename_pullV, List.append_assoc]
      exact congrArg _ (congrArg _ (congrArg _ (pullV_lift_weakenOne _ _ _)))

/-- A splice of two programs with fixed events has fixed events. -/
theorem leakFixed_spliceCom (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t s : JasminTy} {c : Com jasminDialect Γ t} {k : Com jasminDialect (t :: Γ) s}
    (hc : LeakFixed M c) (hk : LeakFixed M k) : LeakFixed M (spliceCom c k) := by
  intro V₁ V₂
  rw [ctLeak_spliceCom, ctLeak_spliceCom, hc V₁ V₂,
    hk (V₁.extend _) (V₂.extend (c.denote V₂))]

/-! ## 2. Literal arrays -/

/-- The renaming of the empty context. -/
def emptyCtxHom {Γ : Ctxt jasminDialect} : Ctxt.Hom [] Γ := fun v => nomatch v

/-- The stores of the words `0` to `m - 1` of `N` into the stack array `a`, at the indices
    `m - 1` down to `0`. -/
def fillArr (w n N : Nat) : (m : Nat) → {Γ : Ctxt jasminDialect} →
    Var Γ (.stackArr w n) → Com jasminDialect Γ (.stackArr w n)
  | 0, _, a => .ret a
  | m + 1, _, a =>
      .var ⟨.regConst w (N / 2 ^ (w * m)), rfl, .nil⟩ <|
        .var ⟨.stackStoreImm w n m, rfl, .cons a.there (.cons .here .nil)⟩ <|
          fillArr w n N m .here

/-- The stack array of the `n` words of `w` bits of `N`. -/
def litArr (w n N : Nat) {Γ : Ctxt jasminDialect} : Com jasminDialect Γ (.stackArr w n) :=
  .var ⟨.stackZero w n, rfl, .nil⟩ (fillArr w n N n .here)

/-- The stores of the words below `m ≤ n` set the entries below `m` to the words of `N`. -/
theorem fillArr_denote (w n N : Nat) : (m : Nat) → m ≤ n → {Γ : Ctxt jasminDialect} →
    (a : Var Γ (.stackArr w n)) → (V : Valuation Γ) →
    (fillArr w n N m a).denote V =
      fun i => if i.val < m then wordsOf w n N i else (a.lookup V : Fin n → BitVec w) i
  | 0, _, _, a, V => by
      funext i
      simp [fillArr, Com.denote]
  | m + 1, hm, _, a, V => by
      simp only [fillArr, Com.denote]
      rw [fillArr_denote w n N m (by omega)]
      funext i
      show (if i.val < m then wordsOf w n N i
        else stackSet (a.lookup V : Fin n → BitVec w) m (BitVec.ofNat w (N / 2 ^ (w * m))) i) = _
      have hs := stackSet_fin (a.lookup V : Fin n → BitVec w) ⟨m, by omega⟩
        (BitVec.ofNat w (N / 2 ^ (w * m)))
      simp only [] at hs
      rw [hs]
      by_cases h1 : i.val < m
      · simp [h1, Nat.lt_succ_of_lt h1]
      · by_cases h2 : i.val = m
        · have hi : i = ⟨m, by omega⟩ := Fin.ext h2
          simp [hi, wordsOf]
        · have hi : i ≠ ⟨m, by omega⟩ := fun h => h2 (congrArg Fin.val h)
          simp [h1, hi, show ¬ i.val < m + 1 by omega]

/-- The literal array is the words of `N`. -/
theorem litArr_denote (w n N : Nat) {Γ : Ctxt jasminDialect} (V : Valuation Γ) :
    (litArr w n N (Γ := Γ)).denote V = wordsOf w n N := by
  simp only [litArr, Com.denote]
  rw [fillArr_denote w n N n le_rfl]
  funext i
  simp [i.isLt]

/-- The stores of a literal array emit no events at leakage parameters with no
    variable-time operation. -/
theorem fillArr_ctLeak (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (w n N : Nat) :
    (m : Nat) → {Γ : Ctxt jasminDialect} → (a : Var Γ (.stackArr w n)) → (V : Valuation Γ) →
    ComLevelCheck.Com.ctLeak (jLeakModel Pj) (fillArr w n N m a) V = []
  | 0, _, a, V => rfl
  | m + 1, _, a, V => by
      simp only [fillArr, ComLevelCheck.Com.ctLeak, ComLevelCheck.Expr.ctLeak,
        ComLevelCheck.opLeak, jLeakModel, Dialects.JasminComLLeak.jKind, hV]
      simp only [List.nil_append]
      exact fillArr_ctLeak Pj hV w n N m .here _

/-- A literal array has fixed events at leakage parameters with no variable-time
    operation. -/
theorem litArr_fixed (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (w n N : Nat)
    {Γ : Ctxt jasminDialect} : LeakFixed (jLeakModel Pj) (litArr w n N (Γ := Γ)) := by
  intro V₁ V₂
  simp only [litArr, ComLevelCheck.Com.ctLeak, fillArr_ctLeak Pj hV]
  rfl

/-! ## 3. Montgomery multiplication on carriers -/

variable {p : Nat} (T : ModArithLimbTemplate p .canon) (k : Nat)
  (hw : (T.ofWords 64 T.limbs).isSome = true)

/-- Montgomery multiplication of the carriers `a` and `b` at the literal `c`: the
    multiplication body of `T` on `a` and `b`, then the multiplication body of `T` on the
    product and `c`, read by the cast block `T.ofWords 64 T.limbs` from its words. At
    `c = (2 ^ k)⁻¹` it is Montgomery multiplication at the radix `2 ^ k`. -/
def ofCanonMontMul (c : ZMod p) {Γ : Ctxt jasminDialect} (a b : Var Γ T.ty) :
    Com jasminDialect Γ T.ty :=
  spliceCom (Com.rename (consHom (consHom emptyCtxHom b) a) (T.body .mul)) <|
    spliceCom (litArr 64 T.limbs c.val) <|
      spliceCom (Com.rename (consHom emptyCtxHom .here) ((T.ofWords 64 T.limbs).get hw)) <|
        Com.rename (consHom (consHom emptyCtxHom .here) (.there (.there .here))) (T.body .mul)

/-- Montgomery multiplication at the literal `c` of the encodings of `x` and `y` is the
    encoding of `montMulF c x y`, when the words of `c` hold its value. -/
theorem ofCanonMontMul_denote [NeZero p] (hpw : p ≤ 2 ^ (64 * T.limbs)) (c : ZMod p)
    {Γ : Ctxt jasminDialect}
    (a b : Var Γ T.ty) (V : Valuation Γ) (x y : ZMod p) (ha : a.lookup V = T.enc x)
    (hb : b.lookup V = T.enc y) :
    (ofCanonMontMul T hw c a b).denote V = T.enc (montMulF c x y) := by
  have hr : fromWordsMF p 64 T.limbs (wordsOf 64 T.limbs c.val) = some c := by
    have hlt : c.val < 2 ^ (64 * T.limbs) :=
      lt_of_lt_of_le (ZMod.val_lt _) hpw
    simp only [fromWordsMF, wordsVal_wordsOf, Nat.mod_eq_of_lt hlt, ZMod.natCast_zmod_val,
      ZMod.val_lt, ite_true]
  have h1 : (Com.rename (consHom (consHom emptyCtxHom b) a) (T.body .mul)).denote V =
      T.enc (x * y) := by
    refine (FieldDialectBlockDescent.Com.denote_rename _ _ V).trans ?_
    have := T.body_denote .mul x y
    rw [← ha, ← hb] at this
    exact this
  unfold ofCanonMontMul
  refine (spliceCom_denote _ _ V).trans ?_
  rw [h1]
  refine (spliceCom_denote _ _ _).trans ?_
  rw [litArr_denote]
  refine (spliceCom_denote _ _ _).trans ?_
  have h3 : (Com.rename (consHom emptyCtxHom .here) ((T.ofWords 64 T.limbs).get hw)).denote
      (Ctxt.Valuation.extend (t := JasminTy.stackArr 64 T.limbs)
        (Ctxt.Valuation.extend (t := T.ty) V (T.enc (x * y)))
        (wordsOf 64 T.limbs c.val)) = T.enc c := by
    refine (FieldDialectBlockDescent.Com.denote_rename _ _ _).trans ?_
    exact T.ofWords_denote 64 T.limbs _ (Option.some_get hw).symm _ _ hr
  rw [h3]
  refine (FieldDialectBlockDescent.Com.denote_rename _ _ _).trans ?_
  exact T.body_denote .mul (x * y) _

/-- Montgomery multiplication has fixed events at leakage parameters with no variable-time
    operation. -/
theorem ofCanonMontMul_fixed (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none)
    (c : ZMod p) {Γ : Ctxt jasminDialect} (a b : Var Γ T.ty) :
    LeakFixed (jLeakModel Pj) (ofCanonMontMul T hw c a b) := by
  unfold ofCanonMontMul
  refine leakFixed_spliceCom _ (leakFixed_rename _ _ (T.body_fixed Pj hV .mul)) ?_
  refine leakFixed_spliceCom _ (litArr_fixed Pj hV _ _ _) ?_
  refine leakFixed_spliceCom _
    (leakFixed_rename _ _ (T.ofWords_fixed Pj hV 64 T.limbs _ (Option.some_get hw).symm)) ?_
  exact leakFixed_rename _ _ (T.body_fixed Pj hV .mul)

/-- The body of a method at `mont k`: the body of `T` for addition, subtraction, negation
    and doubling; Montgomery multiplication for multiplication and squaring. -/
def ofCanonMontBody : (m : FieldMethod) → Com jasminDialect (limbSig T.ty m) T.ty
  | .add => T.body .add
  | .sub => T.body .sub
  | .mul => ofCanonMontMul T hw ((radixParams k).rInv p) .here (.there .here)
  | .neg => T.body .neg
  | .square => ofCanonMontMul T hw ((radixParams k).rInv p) .here .here
  | .double => T.body .double

/-! ## 4. The template -/

/-- **The Montgomery template of a canonical template** `T` at an odd modulus `p`: the
    carrier, the encoding and the word casts of `T`, and the bodies `ofCanonMontBody`. The cast
    block `T.ofWords 64 T.limbs` exists and `p ≤ 2 ^ (64 * T.limbs)`. -/
@[instance_reducible] def ofCanonMont (hp : Odd p) (hpw : p ≤ 2 ^ (64 * T.limbs)) :
    ModArithLimbTemplate p (.mont k) where
  limbs := T.limbs
  ty := T.ty
  enc := T.enc
  body := ofCanonMontBody T k hw
  body_denote m x y := by
    have : NeZero p := NeZero.of_pos hp.pos
    cases m
    · exact T.body_denote .add x y
    · exact T.body_denote .sub x y
    · exact ofCanonMontMul_denote T hw hpw _ .here (.there .here) _ x y rfl rfl
    · exact T.body_denote .neg x y
    · exact ofCanonMontMul_denote T hw hpw _ .here .here _ x x rfl rfl
    · exact T.body_denote .double x y
  body_fixed Pj hV m := by
    cases m
    · exact T.body_fixed Pj hV .add
    · exact T.body_fixed Pj hV .sub
    · exact ofCanonMontMul_fixed T hw Pj hV _ _ _
    · exact T.body_fixed Pj hV .neg
    · exact ofCanonMontMul_fixed T hw Pj hV _ _ _
    · exact T.body_fixed Pj hV .double
  ofWords := T.ofWords
  ofWords_denote := T.ofWords_denote
  ofWords_fixed := T.ofWords_fixed
  toWords := T.toWords
  toWords_denote := T.toWords_denote
  toWords_fixed := T.toWords_fixed

end ModArithLimbTemplate

end CatCrypt.Crypto.SecureCompilation.Algebraic
