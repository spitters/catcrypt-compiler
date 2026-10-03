/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
public import CatCrypt.Crypto.Optimizer.Rewrite.TraitRules
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldOpInfo

/-!
# The acyclic e-graph over `Com fieldDialect`

The instance of the acyclic e-graph `AegraphGeneric.aegraphOptOf` at `fieldDialect`, for
field-level programs before limb lowering. The rule set `fieldRules` holds ring identities
over the prime-field operations, for every modulus `p`, each proved against the denotation
of `fieldDialect` in `ZMod p`:

* `addRule`: `x + 0 = x`, `0 + x = x` (`addAlts_sound`);
* `mulRule`: `x * 1 = x`, `1 * x = x`, `x * 0 = 0`, `0 * x = 0` (`mulAlts_sound`);
* `subRule`: `x - x = 0`, `x - 0 = x` (`subAlts_sound`);
* `negRule`: `-(-x) = x`, the involution rule `TraitRules.involutionRule` at
  `fieldInvolution`;
* `constFoldRule fieldReify`: a pure operation on constant arguments is replaced by the
  constant `fConst` holding its value.

A constant operand is read from the definition table (`constOf`, a binding of `fConst`).
The node table merges every operation other than the designated-output copy `fCopy`.

## Main results

* `aegraphOptField`, `aegraphOptField_denote`: the pass denotes the same function as its
  input.
* `aegraphOptField_cost_le`: the pass does not increase `comCostOf fieldCost`.
* `aegraphOptField_constantTime`: the rules emit existing variables and a nullary
  constant, so the pass preserves constant time under every leakage model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-! ## 1. Reading the definition table -/

/-- The value of a variable of type `fp p`, read in `ZMod p`. -/
abbrev val {Δ : Ctxt fieldDialect} {p : Nat} (V : Ctxt.Valuation Δ)
    (a : Ctxt.Var Δ (.fp p)) : ZMod p :=
  a.lookup V

/-- The expression `fConst p c`. -/
def constE {Δ : Ctxt fieldDialect} (p : Nat) (c : ZMod p) : Expr fieldDialect Δ (.fp p) :=
  { op := .fConst p c, retTy_eq := rfl, args := .nil }

theorem constE_denote {Δ : Ctxt fieldDialect} (p : Nat) (c : ZMod p)
    (V : Ctxt.Valuation Δ) : (constE p c).denote V = c := rfl

/-- The constant a variable of type `fp p` holds, read from the definition table. -/
def constOf {Δ : Ctxt fieldDialect} {p : Nat} (D : Defs fieldDialect)
    (a : Ctxt.Var Δ (.fp p)) : Option (ZMod p) :=
  match D[varLvl a]? with
  | some (.fConst p' c, []) => if h : p' = p then some (h ▸ c) else none
  | _ => none

theorem constOf_sound {Δ : Ctxt fieldDialect} {p : Nat} {D : Defs fieldDialect}
    {V : Ctxt.Valuation Δ} (hD : DSound V D) {a : Ctxt.Var Δ (.fp p)} {c : ZMod p}
    (h : constOf D a = some c) : a.lookup V = c := by
  unfold constOf at h
  split at h
  · rename_i p' c' hl
    split at h
    · rename_i hp
      subst hp
      cases h
      obtain ⟨x, h1, h2⟩ := hD _ _ hl
      rw [getLvl_var] at h2
      have h1' : evalKey V (FieldOp.fConst p' c') [] = some ⟨.fp p', c'⟩ := rfl
      rw [h1'] at h1
      rw [← h1] at h2
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h2)).2
    · cases h
  · cases h

/-! ## 2. The ring identities -/

section Identities

variable {Δ : Ctxt fieldDialect} {p : Nat}

/-- `x + 0 = x` and `0 + x = x`. -/
def addAlts (D : Defs fieldDialect) (a b : Ctxt.Var Δ (.fp p)) : List (Alt Δ (.fp p)) :=
  (if constOf D b = some 0 then [.var a] else []) ++
    (if constOf D a = some 0 then [.var b] else [])

theorem addAlts_sound {D : Defs fieldDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.fp p)) :
    ∀ alt ∈ addAlts D a b, alt.denote V = val V a + val V b := by
  intro alt h
  simp only [addAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h
  · rename_i hb
    subst h
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    subst h
    simp [Alt.denote, constOf_sound hD ha]

/-- `x * 1 = x`, `1 * x = x`, `x * 0 = 0` and `0 * x = 0`; the zero is the operand that
    holds it. -/
def mulAlts (D : Defs fieldDialect) (a b : Ctxt.Var Δ (.fp p)) : List (Alt Δ (.fp p)) :=
  (if constOf D b = some 1 then [.var a] else []) ++
    (if constOf D a = some 1 then [.var b] else []) ++
    (if constOf D b = some 0 then [.var b] else []) ++
    (if constOf D a = some 0 then [.var a] else [])

theorem mulAlts_sound {D : Defs fieldDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.fp p)) :
    ∀ alt ∈ mulAlts D a b, alt.denote V = val V a * val V b := by
  intro alt h
  simp only [mulAlts, List.mem_append] at h
  rcases h with ((h | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h
  · rename_i hb
    subst h
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    subst h
    simp [Alt.denote, constOf_sound hD ha]
  · rename_i hb
    subst h
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    subst h
    simp [Alt.denote, constOf_sound hD ha]

/-- `x - x = 0` and `x - 0 = x`. -/
def subAlts (D : Defs fieldDialect) (a b : Ctxt.Var Δ (.fp p)) : List (Alt Δ (.fp p)) :=
  (if varEq a b then [.one (constE p 0)] else []) ++
    (if constOf D b = some 0 then [.var a] else [])

theorem subAlts_sound {D : Defs fieldDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.fp p)) :
    ∀ alt ∈ subAlts D a b, alt.denote V = val V a - val V b := by
  intro alt h
  simp only [subAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h
  · rename_i hab
    subst h
    rw [varEq_sound a b hab, sub_self]
    rfl
  · rename_i hb
    subst h
    simp [Alt.denote, constOf_sound hD hb]

end Identities

/-! ## 3. The rules -/

/-- The alternatives of `addAlts` on a prime-field addition. -/
def addApply (D : Defs fieldDialect) {Δ : Ctxt fieldDialect} {s : FieldTy}
    (e : Expr fieldDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.fAdd p, hop, args⟩ =>
      let a : Ctxt.Var Δ (.fp p) := args.head
      let b : Ctxt.Var Δ (.fp p) := args.tail.head
      hop ▸ addAlts D a b
  | _ => []

/-- The alternatives of `mulAlts` on a prime-field multiplication. -/
def mulApply (D : Defs fieldDialect) {Δ : Ctxt fieldDialect} {s : FieldTy}
    (e : Expr fieldDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.fMul p, hop, args⟩ =>
      let a : Ctxt.Var Δ (.fp p) := args.head
      let b : Ctxt.Var Δ (.fp p) := args.tail.head
      hop ▸ mulAlts D a b
  | _ => []

/-- The alternatives of `subAlts` on a prime-field subtraction. -/
def subApply (D : Defs fieldDialect) {Δ : Ctxt fieldDialect} {s : FieldTy}
    (e : Expr fieldDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.fSub p, hop, args⟩ =>
      let a : Ctxt.Var Δ (.fp p) := args.head
      let b : Ctxt.Var Δ (.fp p) := args.tail.head
      hop ▸ subAlts D a b
  | _ => []

theorem addApply_sound (D : Defs fieldDialect) {Δ : Ctxt fieldDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : FieldTy} (e : Expr fieldDialect Δ s) :
    ∀ alt ∈ addApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case fAdd p =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [addApply, HVector.head, HVector.tail] at halt
      exact addAlts_sound hD a b alt halt
  all_goals intro alt h; simp [addApply] at h

theorem mulApply_sound (D : Defs fieldDialect) {Δ : Ctxt fieldDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : FieldTy} (e : Expr fieldDialect Δ s) :
    ∀ alt ∈ mulApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case fMul p =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [mulApply, HVector.head, HVector.tail] at halt
      exact mulAlts_sound hD a b alt halt
  all_goals intro alt h; simp [mulApply] at h

theorem subApply_sound (D : Defs fieldDialect) {Δ : Ctxt fieldDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : FieldTy} (e : Expr fieldDialect Δ s) :
    ∀ alt ∈ subApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case fSub p =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [subApply, HVector.head, HVector.tail] at halt
      exact subAlts_sound hD a b alt halt
  all_goals intro alt h; simp [subApply] at h

/-- The additive identity: `x + 0 = x`, `0 + x = x`. -/
def addRule : Rule fieldDialect where
  apply D _ _ e := addApply D e
  sound D _ V hD _ e := addApply_sound D V hD e

/-- The multiplicative identity and annihilator: `x * 1 = x`, `1 * x = x`, `x * 0 = 0`,
    `0 * x = 0`. -/
def mulRule : Rule fieldDialect where
  apply D _ _ e := mulApply D e
  sound D _ V hD _ e := mulApply_sound D V hD e

/-- Subtraction: `x - x = 0`, `x - 0 = x`. -/
def subRule : Rule fieldDialect where
  apply D _ _ e := subApply D e
  sound D _ V hD _ e := subApply_sound D V hD e

/-! ## 3a. Instances of the trait rules -/

open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules

/-- The involutions of the field dialect: the negation `fNeg p`. -/
def fieldInvolution : Involution fieldDialect where
  isInv
    | .fNeg _ => true
    | _ => false
  ty
    | .fNeg p => .fp p
    | _ => .fp 0
  sig_eq op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  ret_eq op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  law op h x := by
    cases op <;> first
      | exact absurd h Bool.false_ne_true
      | exact neg_neg (G := ZMod _) x

/-- The constant operation holding a field value: `fConst` for a prime-field element. -/
def fieldReifyOp : (t : FieldTy) → ⟦t⟧ → Option FieldOp
  | .fp p, c => some (.fConst p c)
  | _, _ => none

/-- The reification of prime-field values as constants, under `fieldTraits`. -/
def fieldReify : ConstReify fieldDialect fieldTraits where
  reify := fieldReifyOp
  law := fieldTraits_constLaw
  const t x op h := by
    cases t <;> simp only [fieldReifyOp, Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl
  ret_eq t x op h := by
    cases t <;> simp only [fieldReifyOp, Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl
  denote_eq t x op h := by
    cases t <;> simp only [fieldReifyOp, Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl

/-- Double negation: `-(-x) = x`, the involution rule at `fieldInvolution`. -/
def negRule : Rule fieldDialect := involutionRule fieldInvolution

/-! ## 4. The field rule set and the pass

The cost `fieldCost` and the merge predicate `fieldPure` are defined in
`VIR/FieldOpInfo.lean`, as fields of `fieldTraits`. -/

/-- The extraction weight of a field operation: twice its cost, plus one unless it is a
    constant. -/
def fieldKey (op : FieldOp) : Nat :=
  2 * fieldCost op + (match op with | .fConst _ _ => 0 | _ => 1)

/-- The extraction weight `fieldKey` is the weight `OpTraits.key` derived from
    `fieldTraits`. -/
theorem fieldKey_eq : fieldKey = fieldTraits.key := by
  funext op
  cases op <;> rfl

/-- The field rule set: the four rule families above and constant folding at
    `fieldReify`, for every modulus, over the operation traits `fieldTraits`. -/
def fieldRules : RuleSet fieldDialect where
  toOpTraits := fieldTraits
  rules := [addRule, mulRule, subRule, negRule, constFoldRule fieldReify (fun _ => true)]

/-- **The aegraph pass on field programs**: the instance of `aegraphOptOf` at
    `fieldRules`. -/
def aegraphOptField {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    Com fieldDialect Γ t :=
  aegraphOptOf fieldRules c

/-- **Denotation of the field pass.** `aegraphOptField c` denotes the same function as
    `c`. -/
theorem aegraphOptField_denote {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : (aegraphOptField c).denote = c.denote :=
  aegraphOptOf_denote fieldRules c

/-- The field pass does not increase `comCostOf fieldCost`. -/
theorem aegraphOptField_cost_le {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) :
    comCostOf fieldCost (aegraphOptField c) ≤ comCostOf fieldCost c :=
  aegraphOptOf_cost_le fieldRules c

/-! ## 5. Constant time

The field rules emit existing variables and the nullary constant `fConst p 0`, whose events
do not depend on the valuation, so the field pass preserves constant time under every
leakage model. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)

variable {L : LeakModel fieldDialect}

section Alts

variable {Δ : Ctxt fieldDialect} {p : Nat} (D : Defs fieldDialect)

theorem addAlts_indep (a b : Ctxt.Var Δ (.fp p)) : ∀ alt ∈ addAlts D a b, alt.Indep L := by
  intro alt h
  simp only [addAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial

theorem mulAlts_indep (a b : Ctxt.Var Δ (.fp p)) : ∀ alt ∈ mulAlts D a b, alt.Indep L := by
  intro alt h
  simp only [mulAlts, List.mem_append] at h
  rcases h with ((h | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial

theorem subAlts_indep (a b : Ctxt.Var Δ (.fp p)) : ∀ alt ∈ subAlts D a b, alt.Indep L := by
  intro alt h
  simp only [subAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · exact fun _ _ => rfl
  · trivial

end Alts

/-- The events of every alternative of the field rule set do not depend on the
    valuation, for every leakage model. -/
theorem fieldRules_indep : RulesIndep L fieldRules := by
  refine rulesIndep_of_forall fun r hr => ?_
  simp only [fieldRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  rotate_left 3
  · exact involutionRule_indep L fieldInvolution
  · exact constFoldRule_indep L fieldReify _
  all_goals intro D Δ s e alt ha
  all_goals rcases e with ⟨op, hop, args⟩
  all_goals cases op <;>
    simp only [addRule, mulRule, subRule, addApply, mulApply, subApply,
      List.not_mem_nil] at ha <;> subst hop
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact addAlts_indep D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact mulAlts_indep D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact subAlts_indep D a b alt ha

/-- **Constant time of the field pass.** For every leakage model, if `c` is constant time
    for the relation `R`, so is `aegraphOptField c`. -/
theorem aegraphOptField_constantTime {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) :
    ConstantTime R (Com.ctLeak L (aegraphOptField c)) :=
  aegraphOptOf_constantTime fieldRules fieldRules_indep c R h

end Leak

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphField
