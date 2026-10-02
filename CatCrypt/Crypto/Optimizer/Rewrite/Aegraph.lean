/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
public import CatCrypt.Crypto.Optimizer.Rewrite.ComGVN
public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-!
# An acyclic e-graph over `Com jasminDialect`

The instance at `jasminDialect` of the acyclic e-graph `AegraphGeneric.aegraphOptOf`, which
is stated for every dialect: `aegraphOpt` is `aegraphOptOf jasminRules`. This module gives
the jasmin rule set `jasminRules`: its rule (`binRule`), its cost `opCost`, its extraction
weight `opKey`, and its purity `ComGVN.gvnPure`.

## The rule set

The rules act on a binary `regArith` node `bop a b` over `reg w` other than a multiply,
for every width `w` (`binRules`). The operations of the instruction pairs of the x86
lowering (`ComGVN.pairedOp`: the multiply and the high multiply, the carry-chain add and its
carry-out) are kept: they have no alternative and the node table never merges them, so
every such binding is emitted unchanged. Each rule produces a `Term`: an existing variable, a
constant, one binary node, or two bindings. The rules, of which those naming a multiply
apply to no node, are

* constant folding of two constant operands;
* identities and annihilators with a constant operand: `x + 0`, `x - 0`, `x ^^^ 0`,
  `x ||| 0`, `x * 1`, `x &&& allOnes`, `x <<< 0`, `x >>> 0` are `x`; `x * 0`, `x &&& 0`,
  `~~~x &&& 0`, `x ||| allOnes` are the constant operand; `~~~0 &&& x` is `x`;
  `~~~allOnes &&& x` is `0`;
* shifts by at least the width are `0`, and `0 <<< x`, `0 >>> x` are `0`;
* strength reduction `x * 2^k ↦ x <<< k`;
* equal operands: `x - x`, `x ^^^ x`, `~~~x &&& x` are `0`; `x &&& x`, `x ||| x` are `x`;
* reassociation `(a ∘ b) ∘ c ↦ a ∘ (b ∘ c)` for the associative operations, with the
  inner node folded when `b` and `c` are constants;
* commutativity of the commutative operations, applied by running the rules on the
  swapped node as well.

## Main results

* `rule_sound`: every term of `binRules` denotes `bop.apply a b`, under a definition
  table sound for the valuation.
* `extract_denote`: the extracted alternative denotes the value of the expression;
  `choose_cost_le`: its cost is at most the cost of the expression.
* `aegraphOpt`, `aegraphOpt_denote`: the pass from the empty state; it denotes the same
  function as its input.
* `aegraphOpt_cost_le`: the pass does not increase `comCost`.
* `aegraphOpt_ctSafe`: the pass preserves `ctSafeComJ`.
* `aegraphOpt_ctLeak_eq`, `aegraphOpt_constantTime`: under a leakage model whose
  `regArith` operations are quiet, equal leakage of the input at two valuations gives
  equal leakage of the output, so the pass preserves constant time for every relation.
  The rules emit only `regArith` and `regConst` bindings; a `regConst` binding has no
  argument, so its events do not depend on the valuation (`jasminRules_indep`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.Aegraph

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
  (opCost comCost ctSafeComJ ctSafeComJ_true binE binE_denote asPow2 mul_pow2_eq_shl)
open CatCrypt.Crypto.Optimizer.Rewrite.ComGVN (Tbl comCost_eq_comCostOf pullV_eq_comap)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
  (varLvl getLvl_var varOfLvl? varOfLvl?_lookup castTo?_mk gatherArgs evalKey DSound Alt
    Rule RuleSet StSound aegraphOptOf)
open CatCrypt.Crypto.Optimizer.CopyProp (pullV)
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole (varEq varEq_sound)

/-! ## 1. Tables -/

/-- The expression `regConst w n`. -/
def constE {Δ : Ctxt jasminDialect} (w n : Nat) : Expr jasminDialect Δ (.reg w) :=
  { op := .regConst w n, retTy_eq := rfl, args := .nil }

theorem constE_denote {Δ : Ctxt jasminDialect} (w n : Nat) (V : Ctxt.Valuation Δ) :
    (constE w n).denote V = BitVec.ofNat w n := rfl

/-- The definition table at `jasminDialect`. -/
abbrev Defs := AegraphGeneric.Defs jasminDialect

/-- The constant a variable of type `reg w` holds, read from the definition table. -/
def constOf {Δ : Ctxt jasminDialect} {w : Nat} (D : Defs) (a : Ctxt.Var Δ (.reg w)) :
    Option Nat :=
  match D[varLvl a]? with
  | some (.regConst w' n, []) => if w' = w then some n else none
  | _ => none

theorem constOf_sound {Δ : Ctxt jasminDialect} {w : Nat} {D : Defs} {V : Ctxt.Valuation Δ}
    (hD : DSound V D) {a : Ctxt.Var Δ (.reg w)} {n : Nat} (h : constOf D a = some n) :
    a.lookup V = BitVec.ofNat w n := by
  unfold constOf at h
  split at h
  · rename_i w' n' hl
    split at h
    · rename_i hw
      subst hw
      cases h
      obtain ⟨x, h1, h2⟩ := hD _ _ hl
      rw [getLvl_var] at h2
      have h1' : evalKey V (.regConst w' n) [] = some ⟨.reg w', BitVec.ofNat w' n⟩ := rfl
      rw [h1'] at h1
      rw [← h1] at h2
      exact (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h2)).2)
    · cases h
  · cases h

/-- The binary node defining a variable of type `reg w`, read from the definition
    table. -/
def defOf {Δ : Ctxt jasminDialect} {w : Nat} (D : Defs) (a : Ctxt.Var Δ (.reg w)) :
    Option (JasminBinOp × Ctxt.Var Δ (.reg w) × Ctxt.Var Δ (.reg w)) :=
  match D[varLvl a]? with
  | some (.regArith bop w', [l1, l2]) =>
      if w' = w then
        match varOfLvl? Δ (.reg w) l1, varOfLvl? Δ (.reg w) l2 with
        | some a1, some a2 => some (bop, a1, a2)
        | _, _ => none
      else none
  | _ => none

theorem defOf_sound {Δ : Ctxt jasminDialect} {w : Nat} {D : Defs} {V : Ctxt.Valuation Δ}
    (hD : DSound V D) {a a1 a2 : Ctxt.Var Δ (.reg w)} {bop : JasminBinOp}
    (h : defOf D a = some (bop, a1, a2)) :
    a.lookup V = bop.apply (a1.lookup V) (a2.lookup V) := by
  unfold defOf at h
  split at h
  · rename_i bop' w' l1 l2 hl
    split at h
    · rename_i hw
      subst hw
      split at h
      · rename_i b1 b2 hb1 hb2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h0, h3, h4⟩ := h
        subst h0 h3 h4
        obtain ⟨x, h1, h2⟩ := hD _ _ hl
        rw [getLvl_var] at h2
        have e1 := varOfLvl?_lookup hb1 V
        have e2 := varOfLvl?_lookup hb2 V
        have h1' : evalKey V (.regArith bop' w') [l1, l2] =
            some ⟨.reg w', bop'.apply (b1.lookup V) (b2.lookup V)⟩ := by
          have hg : gatherArgs V [.reg w', .reg w'] [l1, l2] =
              some (.cons (b1.lookup V) (.cons (b2.lookup V) .nil)) := by
            simp [gatherArgs, e1, e2, castTo?_mk (d := jasminDialect)]
          unfold evalKey
          rw [show gatherArgs V (DialectSignature.sig (d := jasminDialect)
              (JasminOp.regArith bop' w')) [l1, l2] =
              some (.cons (b1.lookup V) (.cons (b2.lookup V) .nil)) from hg]
          rfl
        rw [h1'] at h1
        rw [← h1] at h2
        exact (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h2)).2)
      · cases h
    · cases h
  · cases h

/-! ## 2. Extraction weight -/

/-- The extraction weight of an operation: twice its cost, plus one unless it is a
    constant. A constant thus weighs less than any other operation of the same cost. -/
def opKey (op : JasminOp) : Nat :=
  2 * opCost op + (match op with | .regConst _ _ => 0 | _ => 1)

/-! ## 3. Rule terms and the BitVec identities -/

/-- The result of a rule on a node over `reg w`. -/
inductive Term (Δ : Ctxt jasminDialect) (w : Nat) : Type where
  /-- An existing variable. -/
  | var (v : Ctxt.Var Δ (.reg w))
  /-- The constant `n`. -/
  | const (n : Nat)
  /-- The node `bop a b`. -/
  | bin (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w))
  /-- The node `bop a (const n)`, with the constant bound first. -/
  | binK (bop : JasminBinOp) (a : Ctxt.Var Δ (.reg w)) (n : Nat)
  /-- The node `bop a (bop' b c)`, with the inner node bound first. -/
  | binB (bop : JasminBinOp) (a : Ctxt.Var Δ (.reg w)) (bop' : JasminBinOp)
      (b c : Ctxt.Var Δ (.reg w))

namespace Term

variable {Δ : Ctxt jasminDialect} {w : Nat}

/-- The value of a term. -/
def denote : Term Δ w → Ctxt.Valuation Δ → BitVec w
  | .var v, V => v.lookup V
  | .const n, _ => BitVec.ofNat w n
  | .bin bop a b, V => bop.apply (a.lookup V) (b.lookup V)
  | .binK bop a n, V => bop.apply (a.lookup V) (BitVec.ofNat w n)
  | .binB bop a bop' b c, V => bop.apply (a.lookup V) (bop'.apply (b.lookup V) (c.lookup V))

/-- The alternative a term emits. -/
def toAlt : Term Δ w → Alt Δ (.reg w)
  | .var v => .var v
  | .const n => .one (constE w n)
  | .bin bop a b => .one (binE bop a b)
  | .binK bop a n => .two (constE w n) (binE bop a.there .here)
  | .binB bop a bop' b c => .two (binE bop' b c) (binE bop a.there .here)

theorem toAlt_denote (t : Term Δ w) (V : Ctxt.Valuation Δ) :
    t.toAlt.denote V = t.denote V := by
  cases t <;> rfl

end Term

/-- The commutative and associative binary operations. -/
def acOp : JasminBinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

theorem apply_comm {bop : JasminBinOp} (h : acOp bop = true) {w : Nat} (x y : BitVec w) :
    bop.apply x y = bop.apply y x := by
  cases bop <;> simp [acOp] at h <;> simp only [JasminBinOp.apply]
  · exact BitVec.add_comm x y
  · exact BitVec.mul_comm x y
  · exact BitVec.and_comm x y
  · exact BitVec.or_comm x y
  · exact BitVec.xor_comm x y

theorem apply_assoc {bop : JasminBinOp} (h : acOp bop = true) {w : Nat} (x y z : BitVec w) :
    bop.apply (bop.apply x y) z = bop.apply x (bop.apply y z) := by
  cases bop <;> simp [acOp] at h <;> simp only [JasminBinOp.apply]
  · exact BitVec.add_assoc x y z
  · exact BitVec.mul_assoc x y z
  · exact BitVec.and_assoc x y z
  · exact BitVec.or_assoc x y z
  · exact BitVec.xor_assoc x y z

theorem asPow2_spec {w n k : Nat} (h : asPow2 w n = some k) : k < w ∧ 2 ^ k = n := by
  unfold asPow2 at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  exact ⟨List.mem_range.mp hm, by simpa using hp⟩

/-- Strength reduction: `x * c = x <<< k` when `c` reads as `2 ^ k` with `k < w`. -/
theorem mul_eq_shl_of_asPow2 {w k : Nat} (x c : BitVec w) (h : asPow2 w c.toNat = some k) :
    x * c = x <<< (BitVec.ofNat w k).toNat := by
  obtain ⟨hk, hc⟩ := asPow2_spec h
  have hkw : k < 2 ^ w := Nat.lt_trans hk (Nat.lt_two_pow_self)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw, ← mul_pow2_eq_shl x k, hc, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-! ## 4. The rules -/

section Rules

variable {Δ : Ctxt jasminDialect} {w : Nat}

theorem mem_ite {α : Type} {p : Prop} [Decidable p] {x t : α}
    (h : t ∈ (if p then [x] else [])) : p ∧ t = x := by
  split at h <;> simp_all

/-- Strength reduction of a multiplication by a constant power of two. -/
def pow2Rule (a : Ctxt.Var Δ (.reg w)) (c : BitVec w) : List (Term Δ w) :=
  match asPow2 w c.toNat with
  | some k => [.binK .shl a k]
  | none => []

/-- The rules for a node `bop a b` whose second operand holds the constant `c`. -/
def rightRules (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) (c : BitVec w) :
    List (Term Δ w) :=
  match bop with
  | .add | .sub | .xor => if c = 0 then [.var a] else []
  | .or => (if c = 0 then [.var a] else []) ++
      (if c = BitVec.allOnes w then [.var b] else [])
  | .and => (if c = 0 then [.var b] else []) ++
      (if c = BitVec.allOnes w then [.var a] else [])
  | .mul => (if c = 0 then [.var b] else []) ++ (if c = 1 then [.var a] else []) ++
      pow2Rule a c
  | .shl | .shr => (if c = 0 then [.var a] else []) ++
      (if w ≤ c.toNat then [.const 0] else [])
  | .andn => if c = 0 then [.var b] else []

/-- The rules for a node `bop a b` whose first operand holds the constant `c`, for the
    operations that are not commutative. -/
def leftRules (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) (c : BitVec w) :
    List (Term Δ w) :=
  match bop with
  | .shl | .shr => if c = 0 then [.var a] else []
  | .andn => (if c = 0 then [.var b] else []) ++
      (if c = BitVec.allOnes w then [.const 0] else [])
  | _ => []

/-- The rules for a node `bop a a`. -/
def selfRules (bop : JasminBinOp) (a : Ctxt.Var Δ (.reg w)) : List (Term Δ w) :=
  match bop with
  | .sub | .xor | .andn => [.const 0]
  | .and | .or => [.var a]
  | _ => []

/-- Constant folding of a node whose two operands are constants. -/
def foldRule (D : Defs) (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) : List (Term Δ w) :=
  match constOf D a, constOf D b with
  | some m, some n => [.const (bop.apply (BitVec.ofNat w m) (BitVec.ofNat w n)).toNat]
  | _, _ => []

/-- Reassociation `(a1 ∘ a2) ∘ b ↦ a1 ∘ (a2 ∘ b)` for an associative operation, with the
    inner node folded when `a2` and `b` are constants. -/
def assocRules (D : Defs) (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) :
    List (Term Δ w) :=
  if acOp bop then
    match defOf D a with
    | some (bop', a1, a2) =>
        if bop' = bop then
          (match constOf D a2, constOf D b with
            | some m, some n =>
                [.binK bop a1 (bop.apply (BitVec.ofNat w m) (BitVec.ofNat w n)).toNat]
            | _, _ => []) ++ [.binB bop a1 bop a2 b]
        else []
    | none => []
  else []

/-- The rules for the node `bop a b` in its given operand order. -/
def nodeRules (D : Defs) (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) : List (Term Δ w) :=
  foldRule D bop a b ++
  (match constOf D b with
    | some n => rightRules bop a b (BitVec.ofNat w n)
    | none => []) ++
  (match constOf D a with
    | some m => leftRules bop a b (BitVec.ofNat w m)
    | none => []) ++
  (if varEq a b then selfRules bop a else []) ++
  assocRules D bop a b

/-- The rule set on the node `bop a b`: the rules on the node and, for a commutative
    operation, the swapped node and the rules on it. A multiply has no rule: the x86
    lowering pairs its `MUL` with the high multiply on the same sources
    (`ComGVN.pairLowOp`). -/
def binRules (D : Defs) (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) : List (Term Δ w) :=
  if bop = .mul then [] else
  nodeRules D bop a b ++
    (if acOp bop then .bin bop b a :: nodeRules D bop b a else [])

theorem pow2Rule_sound (a : Ctxt.Var Δ (.reg w)) (c : BitVec w) (V : Ctxt.Valuation Δ)
    (t : Term Δ w) (ht : t ∈ pow2Rule a c) :
    t.denote V = JasminBinOp.mul.apply (a.lookup V) c := by
  unfold pow2Rule at ht
  split at ht
  · rename_i k hk
    simp only [List.mem_singleton] at ht
    subst ht
    exact (mul_eq_shl_of_asPow2 (a.lookup V) c hk).symm
  · simp at ht

theorem rightRules_sound (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w))
    (V : Ctxt.Valuation Δ) (t : Term Δ w) (ht : t ∈ rightRules bop a b (b.lookup V)) :
    t.denote V = bop.apply (a.lookup V) (b.lookup V) := by
  generalize hc : b.lookup V = c at ht ⊢
  have hb : Term.denote (.var b) V = c := hc
  have ha : Term.denote (.var a) V = a.lookup V := rfl
  have h0 : Term.denote (Δ := Δ) (.const 0) V = 0#w := rfl
  cases bop <;> simp only [rightRules, List.mem_append] at ht
  · obtain ⟨rfl, rfl⟩ := mem_ite ht
    simp [ha, JasminBinOp.apply]
  · obtain ⟨rfl, rfl⟩ := mem_ite ht
    simp [ha, JasminBinOp.apply]
  · rcases ht with (ht | ht) | ht
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [hb, JasminBinOp.apply]
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [ha, JasminBinOp.apply]
    · exact pow2Rule_sound a c V t ht
  · rcases ht with ht | ht
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [hb, JasminBinOp.apply]
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [ha, JasminBinOp.apply]
  · rcases ht with ht | ht
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [ha, JasminBinOp.apply]
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [hb, JasminBinOp.apply]
  · obtain ⟨rfl, rfl⟩ := mem_ite ht
    simp [ha, JasminBinOp.apply]
  · rcases ht with ht | ht
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [ha, JasminBinOp.apply]
    · obtain ⟨hw, rfl⟩ := mem_ite ht
      rw [h0]
      exact (BitVec.shiftLeft_eq_zero hw).symm
  · rcases ht with ht | ht
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [ha, JasminBinOp.apply]
    · obtain ⟨hw, rfl⟩ := mem_ite ht
      rw [h0]
      exact (BitVec.ushiftRight_eq_zero hw).symm
  · obtain ⟨rfl, rfl⟩ := mem_ite ht
    simp [hb, JasminBinOp.apply]

theorem leftRules_sound (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w))
    (V : Ctxt.Valuation Δ) (t : Term Δ w) (ht : t ∈ leftRules bop a b (a.lookup V)) :
    t.denote V = bop.apply (a.lookup V) (b.lookup V) := by
  generalize hc : a.lookup V = c at ht ⊢
  have ha : Term.denote (.var a) V = c := hc
  have hb : Term.denote (.var b) V = b.lookup V := rfl
  have h0 : Term.denote (Δ := Δ) (.const 0) V = 0#w := rfl
  cases bop <;> simp only [leftRules, List.mem_append, List.not_mem_nil] at ht
  · obtain ⟨rfl, rfl⟩ := mem_ite ht
    simp [ha, JasminBinOp.apply]
  · obtain ⟨rfl, rfl⟩ := mem_ite ht
    simp [ha, JasminBinOp.apply]
  · rcases ht with ht | ht
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [hb, JasminBinOp.apply]
    · obtain ⟨rfl, rfl⟩ := mem_ite ht
      simp [h0, JasminBinOp.apply]

theorem selfRules_sound (bop : JasminBinOp) (a : Ctxt.Var Δ (.reg w))
    (V : Ctxt.Valuation Δ) (t : Term Δ w) (ht : t ∈ selfRules bop a) :
    t.denote V = bop.apply (a.lookup V) (a.lookup V) := by
  cases bop <;> simp only [selfRules, List.mem_singleton, List.not_mem_nil] at ht <;>
    subst ht <;> simp [Term.denote, JasminBinOp.apply]

theorem foldRule_sound {D : Defs} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) (t : Term Δ w)
    (ht : t ∈ foldRule D bop a b) : t.denote V = bop.apply (a.lookup V) (b.lookup V) := by
  unfold foldRule at ht
  split at ht
  · rename_i m n hm hn
    simp only [List.mem_singleton] at ht
    subst ht
    simp only [Term.denote, BitVec.ofNat_toNat, BitVec.setWidth_eq, constOf_sound hD hm,
      constOf_sound hD hn]
  · simp at ht

theorem assocRules_sound {D : Defs} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) (t : Term Δ w)
    (ht : t ∈ assocRules D bop a b) : t.denote V = bop.apply (a.lookup V) (b.lookup V) := by
  unfold assocRules at ht
  split at ht
  · rename_i hac
    split at ht
    · rename_i bop' a1 a2 hdef
      split at ht
      · rename_i hb
        subst hb
        rw [defOf_sound hD hdef, apply_assoc hac]
        rw [List.mem_append] at ht
        rcases ht with ht | ht
        · split at ht
          · rename_i m n hm hn
            simp only [List.mem_singleton] at ht
            subst ht
            simp only [Term.denote, BitVec.ofNat_toNat, BitVec.setWidth_eq,
              constOf_sound hD hm, constOf_sound hD hn]
          · simp at ht
        · simp only [List.mem_singleton] at ht
          subst ht
          rfl
      · simp at ht
    · simp at ht
  · simp at ht

theorem nodeRules_sound {D : Defs} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) (t : Term Δ w)
    (ht : t ∈ nodeRules D bop a b) : t.denote V = bop.apply (a.lookup V) (b.lookup V) := by
  simp only [nodeRules, List.mem_append] at ht
  rcases ht with (((ht | ht) | ht) | ht) | ht
  · exact foldRule_sound hD bop a b t ht
  · split at ht
    · rename_i n hn
      rw [← constOf_sound hD hn] at ht
      exact rightRules_sound bop a b V t ht
    · simp at ht
  · split at ht
    · rename_i m hm
      rw [← constOf_sound hD hm] at ht
      exact leftRules_sound bop a b V t ht
    · simp at ht
  · split at ht
    · rename_i hab
      rw [varEq_sound a b hab] at ht ⊢
      exact selfRules_sound bop b V t ht
    · simp at ht
  · exact assocRules_sound hD bop a b t ht

/-- **Soundness of the rule set.** Under a definition table sound for `V`, every term the
    rules produce for the node `bop a b` denotes `bop.apply a b`, for every width and every
    pair of operands. -/
theorem rule_sound {D : Defs} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) (t : Term Δ w)
    (ht : t ∈ binRules D bop a b) : t.denote V = bop.apply (a.lookup V) (b.lookup V) := by
  unfold binRules at ht
  split at ht
  · simp at ht
  simp only [List.mem_append] at ht
  rcases ht with ht | ht
  · exact nodeRules_sound hD bop a b t ht
  · split at ht
    · rename_i hac
      rw [apply_comm hac]
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact nodeRules_sound hD bop b a t ht
    · simp at ht

end Rules

/-- The rule alternatives of an expression: for a binary `regArith` node, the terms of
    `binRules`; for every other operation, none. -/
def ruleAlts (D : Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.regArith bop w, hop, args⟩ =>
      let a : Ctxt.Var Δ (.reg w) := args.head
      let b : Ctxt.Var Δ (.reg w) := args.tail.head
      hop ▸ (binRules D bop a b).map Term.toAlt
  | _ => []

theorem ruleAlts_sound {D : Defs} {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) {V : Ctxt.Valuation Δ} (hD : DSound V D) :
    ∀ alt ∈ ruleAlts D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [ruleAlts, HVector.head, HVector.tail] at halt
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp halt
      rw [Term.toAlt_denote]
      exact rule_sound hD bop a b t ht
  all_goals intro alt h; simp [ruleAlts] at h

/-! ## 5. The jasmin rule set and the pass -/

/-- The rule of the jasmin rule set: the alternatives `ruleAlts` of a binary `regArith`
    node, sound by `ruleAlts_sound`. -/
def binRule : Rule jasminDialect where
  apply D _ _ e := ruleAlts D e
  sound _ _ _ hD _ e := ruleAlts_sound e hD

/-- The jasmin rule set: the rule `binRule`, the cost `opCost`, the extraction weight
    `opKey`, and the purity `ComGVN.gvnPure`, which keeps the operations of the instruction
    pairs of the x86 lowering out of the node table. -/
def jasminRules : RuleSet jasminDialect where
  rules := [binRule]
  cost := opCost
  key := opKey
  pure := ComGVN.gvnPure

/-- **Extraction** at the jasmin rule set. -/
def choose (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : Alt Δ s :=
  AegraphGeneric.choose jasminRules S e

/-- **Denotation of extraction.** Any alternative extraction chooses from the e-class of
    `e` denotes the value of `e`. -/
theorem extract_denote {S : Tbl × Defs} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr jasminDialect Δ s) :
    (choose S e).denote V = e.denote V :=
  AegraphGeneric.extract_denote jasminRules hS e

/-- **Cost of extraction.** The extracted alternative costs at most the expression. -/
theorem choose_cost_le (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : (choose S e).cost opCost ≤ opCost e.op :=
  AegraphGeneric.choose_cost_le jasminRules S e

/-- The aegraph traversal at the jasmin rule set. -/
def agGo {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (S : Tbl × Defs)
    (c : Com jasminDialect Γ t) : Com jasminDialect Δ t :=
  AegraphGeneric.agGo jasminRules ρ S c

/-- **Denotation of the traversal.** Under a state sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`. -/
theorem agGo_denote {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl × Defs) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Δ)
    (hS : StSound V S) : (agGo ρ S c).denote V = c.denote (pullV ρ V) := by
  rw [pullV_eq_comap]
  exact AegraphGeneric.agGo_denote jasminRules ρ S c V hS

/-- **The aegraph pass**: the instance of `AegraphGeneric.aegraphOptOf` at the jasmin rule
    set. -/
def aegraphOpt {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  aegraphOptOf jasminRules c

/-- **Denotation of the pass.** `aegraphOpt c` denotes the same function as `c`. -/
theorem aegraphOpt_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : (aegraphOpt c).denote = c.denote :=
  AegraphGeneric.aegraphOptOf_denote jasminRules c

/-! ## 6. Cost -/

theorem agGo_cost_le {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl × Defs) (c : Com jasminDialect Γ t) :
    comCost (agGo ρ S c) ≤ comCost c := by
  rw [comCost_eq_comCostOf, comCost_eq_comCostOf]
  exact AegraphGeneric.agGo_cost_le jasminRules ρ S c

/-- The pass does not increase `comCost`. -/
theorem aegraphOpt_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : comCost (aegraphOpt c) ≤ comCost c :=
  agGo_cost_le _ _ c

/-- The pass preserves the structural CT predicate `ctSafeComJ`. -/
theorem aegraphOpt_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : ctSafeComJ (aegraphOpt c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (aegraphOpt c), ctSafeComJ_true c]

/-! ## 7. Constant time under a leakage model

The bindings the rules emit are `regArith` and `regConst` bindings. Under a leakage model
whose `regArith` operations are quiet, the former emit no event, and a `regConst` binding
has no argument, so its events are the same at every valuation: the jasmin rule set
satisfies `AegraphGeneric.RulesIndep`, and the generic leakage theorems apply. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)

variable {L : LeakModel jasminDialect}

theorem binE_ctLeak (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {Δ : Ctxt jasminDialect} {w : Nat} (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w))
    (V : Ctxt.Valuation Δ) : Expr.ctLeak L (binE bop a b) V = [] := by
  show opLeak L (.regArith bop w) _ = []
  unfold opLeak
  rw [hq]

theorem toAlt_indep (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {Δ : Ctxt jasminDialect} {w : Nat} (t : Term Δ w) : t.toAlt.Indep L := by
  cases t with
  | var v => trivial
  | const n => exact fun _ _ => rfl
  | bin bop a b => exact fun V₁ V₂ => by rw [binE_ctLeak hq, binE_ctLeak hq]
  | binK bop a n =>
      exact ⟨fun _ _ => rfl, fun V₁ V₂ => by rw [binE_ctLeak hq, binE_ctLeak hq]⟩
  | binB bop a bop' b c =>
      exact ⟨fun V₁ V₂ => by rw [binE_ctLeak hq, binE_ctLeak hq],
        fun V₁ V₂ => by rw [binE_ctLeak hq, binE_ctLeak hq]⟩

theorem ruleAlts_indep (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (D : Defs)
    {Δ : Ctxt jasminDialect} {s : JasminTy} (e : Expr jasminDialect Δ s) :
    ∀ alt ∈ ruleAlts D e, alt.Indep L := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [ruleAlts, HVector.head, HVector.tail] at halt
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp halt
      exact toAlt_indep hq t
  all_goals intro alt h; simp [ruleAlts] at h

/-- Under a leakage model whose `regArith` operations are quiet, the events of every
    alternative of the jasmin rule set do not depend on the valuation. -/
theorem jasminRules_indep (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) :
    AegraphGeneric.RulesIndep L jasminRules := by
  intro D Δ s e alt h
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp h
  simp only [jasminRules, List.mem_singleton] at hr
  subst hr
  exact ruleAlts_indep hq D e alt ha

/-- **Leakage of the traversal.** Under states sound for `V₁` and `V₂`, equal leakage of
    the input at the pulled-back valuations gives equal leakage of the output. -/
theorem agGo_ctLeak (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (S : Tbl × Defs)
    (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Δ) (h₁ : StSound V₁ S)
    (h₂ : StSound V₂ S) (h : Com.ctLeak L c (pullV ρ V₁) = Com.ctLeak L c (pullV ρ V₂)) :
    Com.ctLeak L (agGo ρ S c) V₁ = Com.ctLeak L (agGo ρ S c) V₂ := by
  rw [pullV_eq_comap, pullV_eq_comap] at h
  exact AegraphGeneric.agGo_ctLeak jasminRules (jasminRules_indep hq) ρ S c V₁ V₂ h₁ h₂ h

/-- **Leakage of the pass.** Under a leakage model whose `regArith` operations are quiet,
    equal leakage of `c` at two valuations gives equal leakage of `aegraphOpt c` there. -/
theorem aegraphOpt_ctLeak_eq (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V₁ V₂ : Ctxt.Valuation Γ) (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (aegraphOpt c) V₁ = Com.ctLeak L (aegraphOpt c) V₂ :=
  AegraphGeneric.aegraphOptOf_ctLeak_eq jasminRules (jasminRules_indep hq) c V₁ V₂ h

/-- **Constant time of the pass.** Under a leakage model whose `regArith` operations are
    quiet, if `c` is constant time for the relation `R`, so is `aegraphOpt c`. -/
theorem aegraphOpt_constantTime (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (aegraphOpt c)) :=
  fun V₁ V₂ hR => aegraphOpt_ctLeak_eq hq c V₁ V₂ (h V₁ V₂ hR)

end Leak

end CatCrypt.Crypto.Optimizer.Rewrite.Aegraph
