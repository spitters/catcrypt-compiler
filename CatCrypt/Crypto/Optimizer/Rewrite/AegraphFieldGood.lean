/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphField
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

/-!
# The field e-graph preserves the coverage decision of the limb lowering

The limb lowering `FieldToJasminLimbs` accepts a field program when the decision
`GoodVB P` holds: every let-bound operation passes `opGoodB P`, that is, it is one of
`fAdd`, `fSub`, `fNeg`, `fMul`, `fCopy`, `fieldDouble`, `fieldSquare` or `fConst` at the
modulus `P.p`. The decision reads operations only, never argument shapes.

The acyclic e-graph `aegraphOptOf R` emits, for each binding, the binding itself hash-consed
(an existing variable or the renamed binding) or an alternative of a rule of `R`, itself
hash-consed. A predicate `g` on operations is therefore preserved whenever every rule maps
an expression whose operation satisfies `g` to alternatives whose bindings satisfy `g`
(`RulesOpsIn`). The field rules emit existing variables, the constant `fConst p 0` at the
modulus of a subtraction, and constant folds `fConst q x` at the result type `fp q` of the
folded operation, so they preserve `opGoodB P`.

With `aegraphOptField_goodVB` and the coverage of the Jacobian programs
(`EcRoute.goodVB_jacAdd`, `EcRoute.goodVB_jacDbl`), the Jacobian addition and doubling
programs after `aegraphOptField` satisfy `GoodVB P`, and `compileField P c'` is `some` when
`GoodVB P c' = true`.

## Main results

* `agGo_coveredCom`, `aegraphOptOf_coveredCom`: for a rule set satisfying
  `RulesOpsIn g`, the e-graph pass maps a program whose bindings all satisfy `g` to one
  whose bindings all satisfy `g`.
* `fieldRules_opsIn`: the field rules satisfy `RulesOpsIn` at `opGoodB P`.
* `goodVB_iff_coveredCom`: `GoodVB P` is coverage by `opGoodB P` of the operations.
* `aegraphOptOf_goodVB`, `aegraphOptField_goodVB`: the field e-graph pass preserves
  `GoodVB P`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphFieldGood

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-! ## 1. Preservation of an operation predicate by the e-graph -/

section Generic

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- Every binding an alternative emits has an operation satisfying `g`. -/
def AltOpsIn (g : d.Op → Prop) {Δ : Ctxt d} {s : d.Ty} : Alt Δ s → Prop
  | .var _ => True
  | .one e => g e.op
  | .two e1 e2 => g e1.op ∧ g e2.op

/-- Every rule of `R` maps an expression whose operation satisfies `g` to alternatives
    whose bindings satisfy `g`, under every definition table. -/
def RulesOpsIn (g : d.Op → Prop) (R : RuleSet d) : Prop :=
  ∀ (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s), g e.op →
    ∀ a ∈ R.alts D e, AltOpsIn g a

/-- A rule set satisfies `RulesOpsIn g` when each of its rules does. -/
theorem rulesOpsIn_of_forall {g : d.Op → Prop} {R : RuleSet d}
    (h : ∀ r ∈ R.rules, ∀ (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s), g e.op →
      ∀ a ∈ r.apply D e, AltOpsIn g a) : RulesOpsIn g R := by
  intro D Δ s e he a ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  exact h r hr D e he a ha

/-- The coverage predicate of the bindings of a program by an operation predicate. -/
abbrev OpsCovered (g : d.Op → Prop) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) : Prop :=
  CoveredCom (fun {_ _} e => g e.op) c

variable [DecidableEq d.Op] {g : d.Op → Prop}

omit [TyDenote d.Ty] [DialectDenote d] in
theorem reduceOne_opsIn (pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) (h : g e.op) : AltOpsIn g (reduceOne pure M e) := by
  unfold reduceOne
  split
  · trivial
  · exact h

omit [TyDenote d.Ty] [DialectDenote d] in
theorem reduceAlt_opsIn (pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty}
    (a : Alt Δ s) (ha : AltOpsIn g a) : AltOpsIn g (reduceAlt pure M a) := by
  cases a with
  | var v => trivial
  | one e => exact reduceOne_opsIn pure M e ha
  | two e1 e2 =>
      simp only [reduceAlt]
      split
      · exact reduceOne_opsIn pure M _ ha.2
      · exact ha

/-- The extracted alternative of an expression whose operation satisfies `g` has all its
    bindings satisfying `g`. -/
theorem choose_opsIn (R : RuleSet d) (hR : RulesOpsIn g R) (S : Tbl d × Defs d)
    {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) (h : g e.op) : AltOpsIn g (choose R S e) :=
  pick_prop R _ (fun a => AltOpsIn g a) _ _ (reduceOne_opsIn R.pure S.1 e h)
    (fun a ha _ => by
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      exact reduceAlt_opsIn R.pure S.1 a' (hR S.2 e h a' ha'))

/-- **Coverage of the traversal.** Under every renaming and state, `agGo R` maps a
    program whose bindings satisfy `g` to one whose bindings satisfy `g`. -/
theorem agGo_coveredCom (R : RuleSet d) (hR : RulesOpsIn g R) :
    ∀ {Γ Δ : Ctxt d} {t : d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d) (c : Com d Γ t),
      OpsCovered g c → OpsCovered g (agGo R ρ S c)
  | _, _, _, _, _, .ret _, _ => trivial
  | _, _, _, ρ, S, .var e body, h => by
      obtain ⟨he, hb⟩ : g e.op ∧ OpsCovered g body := h
      have hc := choose_opsIn R hR S (e.rename ρ) he
      simp only [agGo]
      split
      · exact agGo_coveredCom R hR _ _ body hb
      · rename_i e2 hce
        rw [hce] at hc
        exact (⟨hc, agGo_coveredCom R hR _ _ body hb⟩ : _ ∧ _)
      · rename_i s1 e1 e2 hce
        rw [hce] at hc
        exact (⟨hc.1, hc.2, agGo_coveredCom R hR _ _ body hb⟩ : _ ∧ _ ∧ _)

/-- **Coverage of the pass.** For a rule set satisfying `RulesOpsIn g`, if every binding of
    `c` has an operation satisfying `g`, so does every binding of `aegraphOptOf R c`. -/
theorem aegraphOptOf_coveredCom (R : RuleSet d) (hR : RulesOpsIn g R) {Γ : Ctxt d}
    {t : d.Ty} (c : Com d Γ t) (hc : OpsCovered g c) : OpsCovered g (aegraphOptOf R c) :=
  agGo_coveredCom R hR _ _ c hc

end Generic

/-! ## 2. The coverage decision of the limb lowering -/

section Field

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (opGoodB GoodVB)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphField
open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules

variable {n : Nat} (P : LimbParams n)

/-- `GoodVB P` holds exactly when every binding has an operation passing `opGoodB P`. -/
theorem goodVB_iff_coveredCom : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t), GoodVB P c = true ↔ OpsCovered (opGoodB P · = true) c
  | _, _, .ret _ => by simp [GoodVB, OpsCovered, CoveredCom]
  | _, _, .var e body => by
      simp only [GoodVB, Bool.and_eq_true, OpsCovered, CoveredCom]
      exact and_congr_right fun _ => goodVB_iff_coveredCom body

/-- An operation passing `opGoodB P` has the result type `fp P.p`. -/
theorem ret_of_opGoodB {op : FieldOp} (h : opGoodB P op = true) :
    DialectSignature.ret (d := fieldDialect) op = .fp P.p := by
  cases op <;> simp only [opGoodB, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;> rfl

/-- The constant `fieldReifyOp` produces at the type `fp P.p` passes `opGoodB P`. -/
theorem opGoodB_of_reify {s : FieldTy} {x : ⟦s⟧} {c : FieldOp} (hs : s = .fp P.p)
    (hc : fieldReifyOp s x = some c) : opGoodB P c = true := by
  subst hs
  simp only [fieldReifyOp, Option.some.injEq] at hc
  subst hc
  simp [opGoodB]

/-- **The field rules preserve `opGoodB P`.** The additive, multiplicative and involution
    rules emit existing variables; the subtraction rule emits `fConst p 0` at the modulus
    of the subtraction; constant folding emits `fConst q x` at the result type `fp q`. -/
theorem fieldRules_opsIn : RulesOpsIn (opGoodB P · = true) fieldRules := by
  refine rulesOpsIn_of_forall fun r hr => ?_
  simp only [fieldRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · intro D Δ s e _ alt ha
    rcases e with ⟨op, hop, args⟩
    cases op <;> simp only [addRule, addApply, List.not_mem_nil] at ha
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail, addAlts, List.mem_append] at ha
      rcases ha with h | h <;> split at h <;>
        simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial
  · intro D Δ s e _ alt ha
    rcases e with ⟨op, hop, args⟩
    cases op <;> simp only [mulRule, mulApply, List.not_mem_nil] at ha
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail, mulAlts, List.mem_append] at ha
      rcases ha with ((h | h) | h) | h <;> split at h <;>
        simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial
  · intro D Δ s e he alt ha
    rcases e with ⟨op, hop, args⟩
    cases op <;> simp only [subRule, subApply, List.not_mem_nil] at ha
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail, subAlts, List.mem_append] at ha
      rcases ha with h | h <;> split at h <;>
        simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
      · simpa [AltOpsIn, constE, opGoodB] using he
      · trivial
  · intro D Δ s e _ alt ha
    change alt ∈ invApply fieldInvolution D e at ha
    unfold invApply at ha
    split at ha
    · split at ha
      · split at ha
        · split at ha
          · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
            trivial
          · simp at ha
        · simp at ha
      · simp at ha
    · simp at ha
  · intro D Δ s e he alt ha
    change alt ∈ foldApply fieldReify (fun _ => true) D e at ha
    unfold foldApply at ha
    split at ha
    · split at ha
      · split at ha
        · split at ha
          · split at ha
            · rename_i c hc
              simp only [List.mem_singleton] at ha
              subst ha
              exact opGoodB_of_reify P (e.retTy_eq.symm.trans (ret_of_opGoodB P he)) hc
            · simp at ha
          · simp at ha
        · simp at ha
      · simp at ha
    · simp at ha

/-- **The e-graph pass at a rule set preserving `opGoodB P` preserves `GoodVB P`.** -/
theorem aegraphOptOf_goodVB (R : RuleSet fieldDialect) (hR : RulesOpsIn (opGoodB P · = true) R)
    {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t)
    (hc : GoodVB P c = true) : GoodVB P (aegraphOptOf R c) = true :=
  (goodVB_iff_coveredCom P _).2
    (aegraphOptOf_coveredCom R hR c ((goodVB_iff_coveredCom P c).1 hc))

/-- **The field e-graph pass preserves `GoodVB P`.** A program the limb lowering accepts is
    accepted after `aegraphOptField`. -/
theorem aegraphOptField_goodVB {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : GoodVB P c = true) :
    GoodVB P (aegraphOptField c) = true :=
  aegraphOptOf_goodVB P fieldRules (fieldRules_opsIn P) c hc

end Field

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphFieldGood
