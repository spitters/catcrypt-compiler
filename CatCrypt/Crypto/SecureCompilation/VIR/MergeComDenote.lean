/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-!
# Denotation of the multi-output merge combinators

`VIR/MergeCom.lean` builds a `MultiReturnCom` out of single-return `Com`s:
`Com.foldVar` emits a program's bindings and hands its result variable to a
continuation, `Com.concat2` emits two programs one after the other, and
`Com.mergeTwo` peels a shared prefix of structurally equal bindings before
falling back on `Com.concat2`.  Each of the three has a denotation here.

`Com.foldVar`'s continuation is quantified over the context it is emitted
into, so its specification is quantified the same way: the continuation is
called at some extension `Γ'` of `Γ`, at a valuation whose pullback along the
accumulated renaming is the original valuation, and at a variable holding the
folded program's return value.  A continuation that produces one fixed result
under those two facts makes `Com.foldVar` produce it.

`Com.concat2` and `Com.mergeTwo` both denote to the pair of their arguments'
denotations, so the shared-prefix peel preserves semantics and a merged
program is reasoned about one output at a time.  The two-output butterfly at
the end of the file is the assembly that uses this: the two single-return
schedules of one Cooley–Tukey butterfly, which share a twiddle product, merge
into the two-output program that a stage of `VIR/NttStageFieldMultiReturn.lean`
writes by hand, with the same denotation.

## Main definitions

* `mulExpr` — the one-op `bvMul` expression builder, alongside the `bvAdd`,
  `bvSub` and `bvConst` builders of `MergeCom`'s `MergeSmoke`.
* `Gbf`, `bfVal` — the two-lane butterfly input context and its valuation.
* `comAddHalf`, `comSubHalf` — the two single-return schedules of one
  butterfly, sharing the constant and the twiddle product.
* `handHalf` — the same butterfly written by hand as one two-output program.

## Main results

* `pullV_weakenOne` — the pullback along `Ctxt.Hom.weakenOne` of an extended
  valuation is the valuation it extends.
* `pullV_tail` — a renaming out of `s :: Γ` whose pullback is `V.extend x`
  pulls back to `V` on the `.there`-shifted part.
* `Com.foldVar_denote` — the continuation-passing specification of
  `Com.foldVar`.
* `Com.concat2_denote` — `Com.concat2 c₁ c₂` denotes to the pair of the
  denotations of `c₁` and `c₂`.
* `Var.beq_eq_true`, `HVector.beqVars_eq_true` — the structural equality tests
  `Com.mergeTwo` branches on are sound.
* `Com.mergeTwo_denote` — `Com.mergeTwo c₁ c₂` denotes to the same pair,
  through both the lockstep peel and the fall-back concatenation.
* `handHalf_denote`, `merged_denote_handHalf`, `merged_denote_lanes` — the
  merge of the two butterfly schedules denotes as the hand-written two-output
  butterfly, and both give the butterfly's two lanes.

## Scope

The renaming layer these proofs stand on — `pullV`, `Var.lookup_rename`,
`Expr.denote_rename` and `Com.denote_rename` — is proved dialect-generically in
`VIR/FieldDialectBlockDescent.lean` and is used here rather than restated.  The
matching statement for `MultiReturnCom.rename` is
`MultiBlockLowering.multiReturnCom_denote_rename`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MergeComDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

universe u v

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-! ## 1. Pullback along a weakening -/

/-- The pullback of an extended valuation along `Ctxt.Hom.weakenOne` is the
valuation it extends. -/
theorem pullV_weakenOne {Γ : Ctxt d} {s : d.Ty} (x : ⟦s⟧)
    (V : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.weakenOne Γ s) (V.extend x) = V := by
  have h := pullV_there (d := d) (fun v => v) x V
  rw [pullV_id] at h
  exact h

omit [DialectSignature d] [DialectDenote d] in
/-- A renaming out of `s :: Γ` whose pullback is `V.extend x` pulls back to `V`
on the variables shifted past the head binding. -/
theorem pullV_tail {Γ Γ' : Ctxt d} {s : d.Ty} {x : ⟦s⟧}
    (h : Ctxt.Hom (s :: Γ) Γ') (V' : Ctxt.Valuation Γ')
    (V : Ctxt.Valuation Γ) (hV : pullV h V' = V.extend x) :
    pullV (fun {t} (w : Ctxt.Var Γ t) => h (Ctxt.Var.there w)) V' = V := by
  rw [pullV] at hV
  exact (HVector.cons.inj hV).2

/-! ## 2. The continuation-passing fold -/

/-- The continuation of `Com.foldVar c k` is called at an extension `Γ'` of
`Γ`, at a valuation `V'` pulling back to `V` along the accumulated renaming,
and at a variable holding `c.denote V`.  A continuation that produces `r`
under those two facts makes the fold produce `r`. -/
theorem Com.foldVar_denote {ts : List d.Ty} :
    ∀ {Γ : Ctxt d} {τ : d.Ty} (c : Com d Γ τ) (V : Ctxt.Valuation Γ)
      (k : ∀ {Γ' : Ctxt d}, Ctxt.Hom Γ Γ' → Ctxt.Var Γ' τ →
        MultiReturnCom d Γ' ts)
      (r : ListDenote ts),
      (∀ {Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') (v : Ctxt.Var Γ' τ)
          (V' : Ctxt.Valuation Γ'),
          pullV h V' = V → v.lookup V' = c.denote V →
          (k h v).denote V' = r) →
      (Com.foldVar c k).denote V = r
  | _, _, .ret v, V, k, r, hk => by
      simp only [Com.foldVar]
      exact hk (Ctxt.Hom.id _) v V (pullV_id V) rfl
  | _, _, .var e body, V, k, r, hk => by
      simp only [Com.foldVar, MultiReturnCom.denote]
      refine Com.foldVar_denote body (V.extend (e.denote V)) _ r ?_
      intro Γ' h v V' hV hv
      exact hk (Ctxt.Hom.comp h (Ctxt.Hom.weakenOne _ _)) v V'
        (pullV_tail h V' V hV) hv

/-! ## 3. Concatenation -/

/-- Emitting `c₁`'s bindings, then `c₂`'s renamed past them, returns the two
denotations. -/
theorem Com.concat2_denote {Γ : Ctxt d} {t1 t2 : d.Ty}
    (c1 : Com d Γ t1) (c2 : Com d Γ t2) (V : Ctxt.Valuation Γ) :
    (Com.concat2 c1 c2).denote V
      = .cons (c1.denote V) (.cons (c2.denote V) .nil) := by
  refine Com.foldVar_denote c1 V _ _ ?_
  intro Γ₁ h1 v1 V1 hV1 hv1
  refine Com.foldVar_denote (Com.rename h1 c2) V1 _ _ ?_
  intro Γ₂ h2 v2 V2 hV2 hv2
  rw [Com.denote_rename h1 c2 V1, hV1] at hv2
  simp only [MultiReturnCom.denote, MultiReturnCom.lookupVars]
  rw [Var.lookup_rename h2 v1 V2, hV2, hv1, hv2]

/-! ## 4. Soundness of the structural equality tests -/

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
/-- `Var.beq` decides variable equality. -/
theorem Var.beq_eq_true : ∀ {Γ : Ctxt d} {t : d.Ty} {v₁ v₂ : Ctxt.Var Γ t},
    Var.beq v₁ v₂ = true → v₁ = v₂
  | _, _, .here, .here, _ => rfl
  | _, _, .there w₁, .there w₂, h => by
      simp only [Var.beq] at h
      exact congrArg Ctxt.Var.there (Var.beq_eq_true h)

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
/-- `HVector.beqVars` decides equality of argument vectors. -/
theorem HVector.beqVars_eq_true {Γ : Ctxt d} :
    ∀ {ts : List d.Ty} {vs₁ vs₂ : HVector (fun ty => Ctxt.Var Γ ty) ts},
      HVector.beqVars vs₁ vs₂ = true → vs₁ = vs₂
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons v₁ r₁, .cons v₂ r₂, h => by
      simp only [HVector.beqVars, Bool.and_eq_true] at h
      rw [Var.beq_eq_true h.1, HVector.beqVars_eq_true h.2]

/-! ## 5. The lockstep merge -/

/-- The lockstep peel of a shared prefix and the fall-back concatenation both
return the two denotations. -/
theorem Com.mergeTwo_denote [DecidableEq d.Op] [DecidableEq d.Ty] :
    ∀ {Γ : Ctxt d} {t1 t2 : d.Ty} (c1 : Com d Γ t1) (c2 : Com d Γ t2)
      (V : Ctxt.Valuation Γ),
      (Com.mergeTwo c1 c2).denote V
        = .cons (c1.denote V) (.cons (c2.denote V) .nil)
  | _, _, _, .ret _, .ret _, _ => by
      simp only [Com.mergeTwo, MultiReturnCom.denote,
        MultiReturnCom.lookupVars, Com.denote]
  | _, _, _, .ret _, .var _ _, V => by
      simp only [Com.mergeTwo]
      exact Com.concat2_denote _ _ V
  | _, _, _, .var _ _, .ret _, V => by
      simp only [Com.mergeTwo]
      exact Com.concat2_denote _ _ V
  | _, _, _, .var (t := _) e1 body1, .var (t := _) e2 body2, V => by
      simp only [Com.mergeTwo]
      split
      · next h_s =>
        subst h_s
        split
        · next h_op =>
          split
          · next h_args =>
            simp only [MultiReturnCom.denote, Com.denote]
            have he : e1 = e2 := by
              obtain ⟨op1, rt1, args1⟩ := e1
              obtain ⟨op2, rt2, args2⟩ := e2
              simp only at h_op h_args
              cases h_op
              have h := HVector.beqVars_eq_true h_args
              simp only at h
              cases h
              rfl
            subst he
            exact Com.mergeTwo_denote body1 body2 _
          · exact Com.concat2_denote _ _ V
        · exact Com.concat2_denote _ _ V
      · exact Com.concat2_denote _ _ V

/-! ## 6. A two-output butterfly assembled from two single-output schedules

A Cooley–Tukey butterfly has two outputs, `x₀ + ω·x₂` and `x₀ − ω·x₂`, sharing
the twiddle product.  Written as two single-return `Com`s it binds that product
twice; `Com.mergeTwo` peels the shared constant and product and emits them once,
and `Com.mergeTwo_denote` identifies the result with the hand-written
two-output program lane by lane. -/

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MergeSmoke (W addExpr subExpr constExpr)

/-- The `bvMul 8` expression on two variables. -/
def mulExpr {Γ : Ctxt catCryptDialect}
    (a b : Ctxt.Var Γ W) : Expr catCryptDialect Γ W :=
  { op := .bvMul 8, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The butterfly input context: the two lanes `x₀` and `x₂`. -/
abbrev Gbf : Ctxt catCryptDialect := [W, W]

/-- The valuation `⟨x₀, x₂⟩` of `Gbf`. -/
def bfVal (x0 x2 : BitVec 8) : Ctxt.Valuation Gbf := .cons x0 (.cons x2 .nil)

/-- The additive output of the butterfly: the twiddle constant, the twiddle
product, then `x₀ + t`. -/
def comAddHalf : Com catCryptDialect Gbf W :=
  .var (constExpr 1)
    (.var (mulExpr .here (.there (.there .here)))
      (.var (addExpr (.there (.there .here)) .here)
        (.ret .here)))

/-- The subtractive output of the butterfly, on the same prefix: `x₀ − t`. -/
def comSubHalf : Com catCryptDialect Gbf W :=
  .var (constExpr 1)
    (.var (mulExpr .here (.there (.there .here)))
      (.var (subExpr (.there (.there .here)) .here)
        (.ret .here)))

/-- The butterfly as one two-output program: the constant and the twiddle
product bound once, then the two output lanes in order. -/
def handHalf : MultiReturnCom catCryptDialect Gbf [W, W] :=
  .var (constExpr 1)
    (.var (mulExpr .here (.there (.there .here)))
      (.var (addExpr (.there (.there .here)) .here)
        (.var (subExpr (.there (.there (.there .here))) (.there .here))
          (.ret (.cons (.there .here) (.cons .here .nil))))))

/-- The two lanes of the hand-written butterfly. -/
theorem handHalf_denote (x0 x2 : BitVec 8) :
    handHalf.denote (bfVal x0 x2)
      = .cons (x0 + 1 * x2) (.cons (x0 - 1 * x2) .nil) := rfl

/-- The merge of the two single-output schedules denotes as the hand-written
two-output butterfly. -/
theorem merged_denote_handHalf (x0 x2 : BitVec 8) :
    (Com.mergeTwo comAddHalf comSubHalf).denote (bfVal x0 x2)
      = handHalf.denote (bfVal x0 x2) := by
  rw [Com.mergeTwo_denote comAddHalf comSubHalf (bfVal x0 x2)]
  rfl

/-- The merged program's two lanes. -/
theorem merged_denote_lanes (x0 x2 : BitVec 8) :
    (Com.mergeTwo comAddHalf comSubHalf).denote (bfVal x0 x2)
      = .cons (x0 + 1 * x2) (.cons (x0 - 1 * x2) .nil) := by
  rw [merged_denote_handHalf, handHalf_denote]

end CatCrypt.Crypto.SecureCompilation.VIR.MergeComDenote
