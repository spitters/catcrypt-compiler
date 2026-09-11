/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction
public import CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodEquiv
public import CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodSelect

/-!
# Global cost-minimum extraction over an explicit e-class

`MultiplyMethodSelect` chooses the cheapest of a *hand-listed* set of
proven-equivalent multiplication methods. This module lifts that to an
**e-class**: an equivalence class of terms, each carrying a `RewriteWitness`
proving its denotation equals a fixed representative, together with global
cost-minimum extraction over the class.

## The e-class representation

An `EClass f` over a denotation `f : α → β` is a representative `repr : α`
together with a list of `EClassMember`s. Each member is a term `term : α` plus a
certificate `cert : RewriteWitness f term repr` — the kernel-checkable
explanation that the member denotes the same value as the representative. The
class is closed under the registered rewrites by construction: adding a rewrite
means inserting a new member with its witness (`EClass.insertWitness` /
`EClass.insertEq`), and every member's denotation equality is recovered by
validating its stored certificate (`EClass.member_denote_eq`).

This is the explicit, eager form of an e-class: the members are enumerated and
their certificates stored directly, rather than materialised on demand from a
union-find. What a full congruence-closure engine would add over this is
described in the module report, not here.

## Extraction

`extractMin cost E` returns the class member of minimum cost, folding the
generic `argmin` (imported from `MultiplyMethodSelect`) over the full member
list `E.members'` (representative included). Two theorems certify it:

* `extractMin_cost_min` — its cost is `≤` the cost of every member of the class.
* `extractMin_denote_eq` — it denotes the same value as the representative, via
  `RewriteWitness.validate` (a checked certificate). `extractMin_denote_eq_member`
  lifts this to agreement with every member.

## Subsuming the finite selector

Section 3 instantiates the e-class on the multiply-method families
(schoolbook / Karatsuba at two limbs, schoolbook / Toom-3 at three limbs) and
recovers the same selection (`mul2Selected = .karatsuba`, `mul3Selected = .toom3`)
through the general `extractMin` rather than the finite `argmin` of
`MultiplyMethodSelect`. The recovered selection is proved to coincide with that
module's `selectMul2`/`selectMul3`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.EgraphGlobalMin

open CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction
open CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodEquiv
open CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodSelect

universe u v

/-! ## 1. The e-class and its members -/

section EClass

variable {α : Type u} {β : Type v}

/-- One member of an e-class over the denotation `f`, relative to a
representative `repr`: a term together with a `RewriteWitness` certifying that
the term denotes the same value as `repr`. -/
structure EClassMember (f : α → β) (repr : α) where
  /-- The member term. -/
  term : α
  /-- Certificate that `term` denotes the same value as the representative. -/
  cert : RewriteWitness f term repr

/-- An e-class over the denotation `f`: a representative together with a list of
members, each carrying its denotation-equality certificate to the
representative. The members need not be listed in any order and the
representative is not repeated in `members` (it is added by `members'`). -/
structure EClass (f : α → β) where
  /-- The representative term of the class. -/
  repr : α
  /-- The non-representative members, each with a certificate to `repr`. -/
  members : List (EClassMember f repr)

variable {f : α → β}

/-- The representative packaged as a member (with the reflexive certificate). -/
def EClass.reprMember (E : EClass f) : EClassMember f E.repr :=
  ⟨E.repr, RewriteWitness.refl f E.repr⟩

/-- The full member list of the class: the representative followed by the
recorded members. Extraction ranges over this list. -/
def EClass.members' (E : EClass f) : List (EClassMember f E.repr) :=
  E.reprMember :: E.members

/-- **Every member denotes the representative's value.** The certificate stored
in the member is validated by the transitivity fold of
`ProofCarryingExtraction`; the result is a kernel-checked equality, not a test
vector. -/
theorem EClass.member_denote_eq (E : EClass f) (mem : EClassMember f E.repr) :
    f mem.term = f E.repr :=
  mem.cert.validate

/-- Any two members of the class denote the same value. -/
theorem EClass.members_agree (E : EClass f)
    (m₁ m₂ : EClassMember f E.repr) : f m₁.term = f m₂.term :=
  (m₁.cert.validate).trans (m₂.cert.validate).symm

/-! ### Closure under the registered rewrites

Adding a rewrite to the class is inserting a member with its witness. The
membership invariant (every member carries a certificate to `repr`) is
structural, so closure holds by construction. -/

/-- Insert a term into the class from a witness `term → repr`. The result is an
e-class with the same representative and the new member prepended. -/
def EClass.insertWitness (E : EClass f) (t : α)
    (w : RewriteWitness f t E.repr) : EClass f :=
  { repr := E.repr, members := ⟨t, w⟩ :: E.members }

/-- Insert a term into the class from a bare denotation equality `f t = f repr`
(the single-step witness case). -/
def EClass.insertEq (E : EClass f) (t : α) (h : f t = f E.repr) : EClass f :=
  E.insertWitness t (RewriteWitness.ofEq h)

/-- Insertion preserves the representative. -/
@[simp] theorem EClass.insertWitness_repr (E : EClass f) (t : α)
    (w : RewriteWitness f t E.repr) : (E.insertWitness t w).repr = E.repr := rfl

/-- Build an e-class from a representative and a list of `(term, equality)`
pairs — the direct generalisation of a finite candidate list, where each entry
is a member proved denotation-equal to the representative. -/
def EClass.ofEqList (repr : α) (cs : List ((t : α) ×' (f t = f repr))) : EClass f :=
  { repr := repr, members := cs.map (fun c => ⟨c.1, RewriteWitness.ofEq c.2⟩) }

/-! ## 2. Global cost-minimum extraction -/

/-- The minimum-cost member of the class under `cost`, chosen by folding the
generic `argmin` over the full member list `members'`. -/
def extractMinMember (cost : α → Nat) (E : EClass f) : EClassMember f E.repr :=
  argmin (fun m : EClassMember f E.repr => cost m.term) E.reprMember E.members

/-- The minimum-cost *term* of the class under `cost`. -/
def extractMin (cost : α → Nat) (E : EClass f) : α :=
  (extractMinMember cost E).term

/-- The extracted member is a member of the class. -/
theorem extractMin_mem (cost : α → Nat) (E : EClass f) :
    extractMinMember cost E ∈ E.members' :=
  argmin_mem _ _ _

/-- **Cost minimality.** The extracted term's cost is `≤` the cost of every
member of the class (representative included). -/
theorem extractMin_cost_min (cost : α → Nat) (E : EClass f)
    (mem : EClassMember f E.repr) (hmem : mem ∈ E.members') :
    cost (extractMin cost E) ≤ cost mem.term :=
  argmin_le (fun m : EClassMember f E.repr => cost m.term)
    E.reprMember E.members mem hmem

/-- **Denotation equality (certificate-carrying).** The extracted term denotes
the same value as the representative, established by validating the extracted
member's `RewriteWitness`. -/
theorem extractMin_denote_eq (cost : α → Nat) (E : EClass f) :
    f (extractMin cost E) = f E.repr :=
  (extractMinMember cost E).cert.validate

/-- The extracted term denotes the same value as *every* member of the class. -/
theorem extractMin_denote_eq_member (cost : α → Nat) (E : EClass f)
    (mem : EClassMember f E.repr) :
    f (extractMin cost E) = f mem.term :=
  (extractMin_denote_eq cost E).trans (mem.cert.validate).symm

end EClass

/-! ## 3. Subsuming the finite multiply-method selector

The multiply-method families become e-classes: the representative is the
schoolbook method, the single non-representative member is Karatsuba (two limbs)
or Toom-3 (three limbs), each carrying the `mul2Witness`/`mul3Witness`
certificate from `MultiplyMethodSelect`. `extractMin` over the multiply cost
recovers the same choice the finite `argmin` selector made. -/

section MultiplyDemo

/-! ### Two-limb: schoolbook / Karatsuba -/

section TwoLimb

variable {R : Type*} [CommRing R]

/-- The two-limb multiply-method e-class at fixed operands: representative
schoolbook, member Karatsuba with its agreement certificate. The denotation is
`eval2F` (the method's assembled value). -/
def mul2EClass (B a1 a0 b1 b0 : R) : EClass (eval2F B a1 a0 b1 b0) :=
  { repr := .schoolbook
    members := [⟨.karatsuba, mul2Witness B a1 a0 b1 b0 .karatsuba .schoolbook⟩] }

/-- The method selected by global cost-minimum extraction over the two-limb
e-class, under the multiply cost model. -/
def mul2Selected (B a1 a0 b1 b0 : R) : Mul2Method :=
  extractMin (fun m => mul2Cost m) (mul2EClass B a1 a0 b1 b0)

/-- **The e-class extraction recovers Karatsuba** — the same method
`MultiplyMethodSelect.selectMul2` picks, now through the general `extractMin`
rather than the finite `argmin`. -/
theorem mul2Selected_eq_karatsuba (B a1 a0 b1 b0 : R) :
    mul2Selected B a1 a0 b1 b0 = .karatsuba := rfl

/-- The e-class selection coincides with the finite selector's choice. -/
theorem mul2Selected_eq_select (B a1 a0 b1 b0 : R) :
    mul2Selected B a1 a0 b1 b0 = (selectMul2 B a1 a0 b1 b0).method := rfl

/-- **Cost minimality of the e-class selection** (two-limb). -/
theorem mul2Selected_cost_min (B a1 a0 b1 b0 : R)
    (mem : EClassMember (eval2F B a1 a0 b1 b0) (mul2EClass B a1 a0 b1 b0).repr)
    (hmem : mem ∈ (mul2EClass B a1 a0 b1 b0).members') :
    mul2Cost (mul2Selected B a1 a0 b1 b0) ≤ mul2Cost mem.term :=
  extractMin_cost_min (fun m => mul2Cost m) (mul2EClass B a1 a0 b1 b0) mem hmem

/-- **Denotation equality of the e-class selection** (two-limb): the selected
method computes the same value as the representative, via the validated
certificate. -/
theorem mul2Selected_denote_eq (B a1 a0 b1 b0 : R) :
    evalMethod2 (mul2Selected B a1 a0 b1 b0) B a1 a0 b1 b0
      = evalMethod2 .schoolbook B a1 a0 b1 b0 :=
  extractMin_denote_eq (fun m => mul2Cost m) (mul2EClass B a1 a0 b1 b0)

end TwoLimb

/-! ### Three-limb: schoolbook / Toom-3 -/

section ThreeLimb

variable {R : Type*} [Field R]

/-- The three-limb multiply-method e-class at fixed operands (needs `6 ≠ 0` for
the field-form Toom-3 certificate): representative schoolbook, member Toom-3. -/
def mul3EClass (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    EClass (eval3F B a2 a1 a0 b2 b1 b0) :=
  { repr := .schoolbook
    members := [⟨.toom3, mul3Witness h6 B a2 a1 a0 b2 b1 b0 .toom3 .schoolbook⟩] }

/-- The method selected by global cost-minimum extraction over the three-limb
e-class. -/
def mul3Selected (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) : Mul3Method :=
  extractMin (fun m => mul3Cost m) (mul3EClass h6 B a2 a1 a0 b2 b1 b0)

/-- **The e-class extraction recovers Toom-3** — the same method
`MultiplyMethodSelect.selectMul3` picks, through the general `extractMin`. -/
theorem mul3Selected_eq_toom3 (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    mul3Selected h6 B a2 a1 a0 b2 b1 b0 = .toom3 := rfl

/-- The e-class selection coincides with the finite selector's choice. -/
theorem mul3Selected_eq_select (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    mul3Selected h6 B a2 a1 a0 b2 b1 b0 = (selectMul3 h6 B a2 a1 a0 b2 b1 b0).method := rfl

/-- **Cost minimality of the e-class selection** (three-limb). -/
theorem mul3Selected_cost_min (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R)
    (mem : EClassMember (eval3F B a2 a1 a0 b2 b1 b0)
      (mul3EClass h6 B a2 a1 a0 b2 b1 b0).repr)
    (hmem : mem ∈ (mul3EClass h6 B a2 a1 a0 b2 b1 b0).members') :
    mul3Cost (mul3Selected h6 B a2 a1 a0 b2 b1 b0) ≤ mul3Cost mem.term :=
  extractMin_cost_min (fun m => mul3Cost m) (mul3EClass h6 B a2 a1 a0 b2 b1 b0) mem hmem

/-- **Denotation equality of the e-class selection** (three-limb). -/
theorem mul3Selected_denote_eq (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    evalMethod3 (mul3Selected h6 B a2 a1 a0 b2 b1 b0) B a2 a1 a0 b2 b1 b0
      = evalMethod3 .schoolbook B a2 a1 a0 b2 b1 b0 :=
  extractMin_denote_eq (fun m => mul3Cost m) (mul3EClass h6 B a2 a1 a0 b2 b1 b0)

end ThreeLimb

end MultiplyDemo

/-! ## 4. Worked instances over `ℤ` and `ℚ` -/

/-- The two-limb e-class extraction picks Karatsuba over `ℤ`. -/
example : mul2Selected (R := ℤ) 10 1 2 3 4 = .karatsuba := rfl

/-- Over `ℤ` the extracted two-limb value is `12·34 = 408` at base `10`. -/
example :
    evalMethod2 (mul2Selected (R := ℤ) 10 1 2 3 4) 10 1 2 3 4 = (408 : ℤ) := by
  rw [mul2Selected_denote_eq, evalMethod2_eq_product]; norm_num

/-- The three-limb e-class extraction picks Toom-3 over `ℚ` (`6 ≠ 0`). -/
example : mul3Selected (R := ℚ) (by norm_num) 10 1 2 3 4 5 6 = .toom3 := rfl

/-- Over `ℚ` the extracted three-limb value is `123·456 = 56088` at base `10`. -/
example :
    evalMethod3 (mul3Selected (R := ℚ) (by norm_num) 10 1 2 3 4 5 6) 10 1 2 3 4 5 6
      = (56088 : ℚ) := by
  rw [mul3Selected_denote_eq, evalMethod3_eq_product (by norm_num : (6 : ℚ) ≠ 0)]
  norm_num

end CatCrypt.Crypto.Optimizer.Rewrite.EgraphGlobalMin
