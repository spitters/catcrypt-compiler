/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.ComGVN
public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-!
# An acyclic e-graph over `Com jasminDialect`

A `Com → Com` pass over the typed VIR `jasminDialect` in the style of the acyclic
e-graph (aegraph) of Cranelift. The pass walks the let-chain once, as global value
numbering does (`ComGVN.gvnGo`), and carries a state `St` of two tables keyed by levels
(positions counted from the bottom of the context, stable under extension):

* the node table `ComGVN.Tbl` of global value numbering, from argument levels to the
  pairs (operation, result level) of the recorded nodes; and
* a definition table `Defs`, from a result level to the operation and argument levels of
  one node defining it, read by the rules to find constants and nested operations.

At a binding `let x = e`, with `e` renamed into the output context, the pass forms the
e-class of `e`: `e` itself and the alternatives the rule set produces for it, each hash-
consed through the node table (`reduceAlt`). Each rule fires once, at the creation of the
node; there is no rebuild and no saturation loop. Extraction (`choose`) takes the
alternative of least `Alt.key` among those whose cost does not exceed the cost of `e`. The
class is a union node: the key of every one-binding alternative is entered in the node
table at the level of the chosen value (`insUnion`), so a later binding equal to any form
of the class is merged with it.

## The rule set

The rules act on a binary `regArith` node `bop a b` over `reg w`, for every width `w`
(`binRules`). Each produces a `Term`: an existing variable, a constant, one binary node,
or two bindings. The rules are

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
  argument, so its events do not depend on the valuation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.Aegraph

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
  (opCost comCost ctSafeComJ ctSafeComJ_true binE binE_denote asPow2 mul_pow2_eq_shl)
open CatCrypt.Crypto.Optimizer.Rewrite.ComGVN
  (Tbl Sound sound_empty sound_extend findVar findVar_sound insertT varLvl argLvls getLvl
    evalKey evalKey_expr evalKey_extend_some getLvl_extend_some getLvl_extend_top getLvl_var
    varOfLvl? varOfLvl?_lookup castTo?_mk gatherArgs)
open CatCrypt.Crypto.Optimizer.CopyProp
  (pullV consHom pullV_consHom pullV_lift pullV_id pullV_weaken Expr.denote_rename)
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole (varEq varEq_sound)

/-! ## 1. Tables -/

/-- The expression `regConst w n`. -/
def constE {Δ : Ctxt jasminDialect} (w n : Nat) : Expr jasminDialect Δ (.reg w) :=
  { op := .regConst w n, retTy_eq := rfl, args := .nil }

theorem constE_denote {Δ : Ctxt jasminDialect} (w n : Nat) (V : Ctxt.Valuation Δ) :
    (constE w n).denote V = BitVec.ofNat w n := rfl

/-- The definition table: for a result level, the operation and argument levels of one
    node defining it. -/
abbrev Defs := Std.HashMap Nat (JasminOp × List Nat)

/-- A definition table is sound for a valuation when every recorded node evaluates, at
    that valuation, to the value at its level. -/
def DSound {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (D : Defs) : Prop :=
  ∀ (l : Nat) (p : JasminOp × List Nat), D[l]? = some p →
    ∃ x, evalKey V p.1 p.2 = some x ∧ getLvl V l = some x

theorem dsound_empty {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    DSound V (∅ : Defs) := by
  intro l p h
  simp at h

theorem dsound_extend {Γ : Ctxt jasminDialect} {s : JasminTy} {V : Ctxt.Valuation Γ}
    (x : ⟦s⟧) {D : Defs} (hD : DSound V D) : DSound (Γ := s :: Γ) (V.extend x) D := by
  intro l p h
  obtain ⟨y, h1, h2⟩ := hD l p h
  exact ⟨y, evalKey_extend_some V x h1, getLvl_extend_some V x h2⟩

theorem dsound_insert {Γ : Ctxt jasminDialect} {V : Ctxt.Valuation Γ} {D : Defs}
    (hD : DSound V D) {op : JasminOp} {lv : List Nat} {l : Nat}
    {x : Σ t : JasminTy, ⟦t⟧} (h1 : evalKey V op lv = some x) (h2 : getLvl V l = some x) :
    DSound V (D.insert l (op, lv)) := by
  intro l' p h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i hk
    have hk' : l = l' := by simpa using hk
    subst hk'
    cases h
    exact ⟨x, h1, h2⟩
  · exact hD l' p h

/-- Entering a node whose value is the value at level `l` keeps a node table sound. -/
theorem sound_insertAt {Γ : Ctxt jasminDialect} {V : Ctxt.Valuation Γ} {M : Tbl}
    (hM : Sound V M) {op : JasminOp} {lv : List Nat} {l : Nat}
    {x : Σ t : JasminTy, ⟦t⟧} (h1 : evalKey V op lv = some x) (h2 : getLvl V l = some x) :
    Sound V (insertT M op lv l) := by
  unfold insertT
  split
  · intro lv' bucket h p hp
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      have hk' : lv = lv' := by simpa using hk
      subst hk'
      cases h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨x, h1, h2⟩
      · rw [Std.HashMap.getD_eq_getD_getElem?] at hp'
        rcases hb : M[lv]? with _ | b
        · simp [hb] at hp'
        · rw [hb] at hp'
          exact hM _ b hb p hp'
    · exact hM lv' bucket h p hp
  · exact hM

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
            simp [gatherArgs, e1, e2, castTo?_mk]
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

/-! ## 2. Alternatives -/

/-- An alternative form of a value of type `s` over the context `Δ`: an existing
    variable, one binding, or two bindings. -/
inductive Alt (Δ : Ctxt jasminDialect) (s : JasminTy) : Type where
  | var (v : Ctxt.Var Δ s)
  | one (e : Expr jasminDialect Δ s)
  | two {s1 : JasminTy} (e1 : Expr jasminDialect Δ s1) (e2 : Expr jasminDialect (s1 :: Δ) s)

namespace Alt

variable {Δ : Ctxt jasminDialect} {s : JasminTy}

/-- The value of an alternative. -/
def denote : Alt Δ s → Ctxt.Valuation Δ → ⟦s⟧
  | .var v, V => v.lookup V
  | .one e, V => e.denote V
  | .two e1 e2, V => e2.denote (V.extend (e1.denote V))

/-- The `comCost` of the bindings an alternative emits. -/
def cost : Alt Δ s → Nat
  | .var _ => 0
  | .one e => opCost e.op
  | .two e1 e2 => opCost e1.op + opCost e2.op

end Alt

/-- The extraction weight of an operation: twice its cost, plus one unless it is a
    constant. A constant thus weighs less than any other operation of the same cost. -/
def opKey (op : JasminOp) : Nat :=
  2 * opCost op + (match op with | .regConst _ _ => 0 | _ => 1)

/-- The extraction weight of an alternative. -/
def Alt.key {Δ : Ctxt jasminDialect} {s : JasminTy} : Alt Δ s → Nat
  | .var _ => 0
  | .one e => opKey e.op
  | .two e1 e2 => opKey e1.op + opKey e2.op

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
    operation, the swapped node and the rules on it. -/
def binRules (D : Defs) (bop : JasminBinOp) (a b : Ctxt.Var Δ (.reg w)) : List (Term Δ w) :=
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
  simp only [binRules, List.mem_append] at ht
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

/-! ## 5. Hash-consing of alternatives -/

/-- The output variable of a recorded node equal to `e` denotes the value of `e`. -/
theorem findVar_expr {Δ : Ctxt jasminDialect} {s : JasminTy} {M : Tbl}
    {V : Ctxt.Valuation Δ} (hM : Sound V M) {e : Expr jasminDialect Δ s}
    {w : Ctxt.Var Δ s} (h : findVar Δ s M e.op (argLvls e.args) = some w) :
    w.lookup V = e.denote V := by
  have h1 := findVar_sound hM h
  rw [evalKey_expr e V] at h1
  exact (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h1)).2).symm

/-- One binding, replaced by the variable of a recorded node equal to it. -/
def reduceOne (M : Tbl) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : Alt Δ s :=
  match findVar Δ s M e.op (argLvls e.args) with
  | some w => .var w
  | none => .one e

/-- An alternative with each binding replaced by the variable of a recorded node equal
    to it. -/
def reduceAlt (M : Tbl) {Δ : Ctxt jasminDialect} {s : JasminTy} : Alt Δ s → Alt Δ s
  | .var v => .var v
  | .one e => reduceOne M e
  | .two (s1 := s1) e1 e2 =>
      match findVar Δ s1 M e1.op (argLvls e1.args) with
      | some w1 => reduceOne M (e2.rename (consHom w1 (Ctxt.Hom.id Δ)))
      | none => .two e1 e2

theorem reduceOne_denote {M : Tbl} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hM : Sound V M) (e : Expr jasminDialect Δ s) :
    (reduceOne M e).denote V = e.denote V := by
  unfold reduceOne
  split
  · rename_i w hw
    exact findVar_expr hM hw
  · rfl

theorem reduceAlt_denote {M : Tbl} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hM : Sound V M) (a : Alt Δ s) :
    (reduceAlt M a).denote V = a.denote V := by
  cases a with
  | var v => rfl
  | one e => exact reduceOne_denote hM e
  | two e1 e2 =>
      simp only [reduceAlt]
      split
      · rename_i w1 hw1
        rw [reduceOne_denote hM, Expr.denote_rename, pullV_consHom, pullV_id,
          findVar_expr hM hw1]
        rfl
      · rfl

/-! ## 6. Extraction -/

/-- The alternative of least key among `best` and the members of the list whose cost is
    at most `bound`; on equal keys the earlier one. -/
def pick {Δ : Ctxt jasminDialect} {s : JasminTy} (bound : Nat) :
    Alt Δ s → List (Alt Δ s) → Alt Δ s
  | best, [] => best
  | best, a :: as => pick bound (if a.cost ≤ bound ∧ a.key < best.key then a else best) as

/-- A property of `best` and of every member of cost at most `bound` holds of the picked
    alternative. -/
theorem pick_prop {Δ : Ctxt jasminDialect} {s : JasminTy} (bound : Nat)
    (P : Alt Δ s → Prop) : ∀ (best : Alt Δ s) (as : List (Alt Δ s)), P best →
      (∀ a ∈ as, a.cost ≤ bound → P a) → P (pick bound best as)
  | _, [], hb, _ => hb
  | best, a :: as, hb, has => by
      simp only [pick]
      refine pick_prop bound P _ as ?_ (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))
      split
      · rename_i h
        exact has a List.mem_cons_self h.1
      · exact hb

/-- The e-class of `e`: the rule alternatives, each hash-consed through the node table. -/
def classAlts (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : List (Alt Δ s) :=
  (ruleAlts S.2 e).map (reduceAlt S.1)

/-- The forms of the union node of `e`: `e` itself, hash-consed, and its e-class. -/
def unionAlts (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : List (Alt Δ s) :=
  reduceOne S.1 e :: classAlts S e

/-- **Extraction**: the alternative of least key among `e` and its e-class, over the
    alternatives whose cost is at most the cost of `e`. -/
def choose (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : Alt Δ s :=
  pick (opCost e.op) (reduceOne S.1 e) (classAlts S e)

/-- A state of the pass is sound for a valuation when both tables are. -/
def StSound {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (S : Tbl × Defs) : Prop :=
  Sound V S.1 ∧ DSound V S.2

theorem unionAlts_denote {S : Tbl × Defs} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr jasminDialect Δ s) :
    ∀ a ∈ unionAlts S e, a.denote V = e.denote V := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact reduceOne_denote hS.1 e
  · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    rw [reduceAlt_denote hS.1]
    exact ruleAlts_sound e hS.2 a' ha'

/-- **Denotation of extraction.** Any alternative extraction chooses from the e-class of
    `e` denotes the value of `e`. -/
theorem extract_denote {S : Tbl × Defs} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr jasminDialect Δ s) :
    (choose S e).denote V = e.denote V :=
  pick_prop _ (fun a => a.denote V = e.denote V) _ _
    (unionAlts_denote hS e _ List.mem_cons_self)
    (fun a ha _ => unionAlts_denote hS e a (List.mem_cons_of_mem _ ha))

/-- **Cost of extraction.** The extracted alternative costs at most the expression. -/
theorem choose_cost_le (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : (choose S e).cost ≤ opCost e.op := by
  refine pick_prop _ (fun a => a.cost ≤ opCost e.op) _ _ ?_ (fun _ _ h => h)
  unfold reduceOne
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-! ## 7. State updates -/

/-- The node table with the key of every one-binding form of a union node entered at the
    level `l` of its value. -/
def insUnion (M : Tbl) (l : Nat) {Δ : Ctxt jasminDialect} {s : JasminTy} :
    List (Alt Δ s) → Tbl
  | [] => M
  | .one e :: U => insUnion (insertT M e.op (argLvls e.args) l) l U
  | _ :: U => insUnion M l U

theorem sound_insUnion {Δ' : Ctxt jasminDialect} {V' : Ctxt.Valuation Δ'} {l : Nat}
    {p : Σ t : JasminTy, ⟦t⟧} {Δ : Ctxt jasminDialect} {s : JasminTy}
    (hl : getLvl V' l = some p) :
    ∀ (U : List (Alt Δ s)) (M : Tbl), Sound V' M →
      (∀ e, Alt.one e ∈ U → evalKey V' e.op (argLvls e.args) = some p) →
      Sound V' (insUnion M l U)
  | [], _, hM, _ => hM
  | .one e :: U, _, hM, h =>
      sound_insUnion hl U _ (sound_insertAt hM (h e List.mem_cons_self) hl)
        (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
  | .var _ :: U, M, hM, h =>
      sound_insUnion hl U M hM (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
  | .two _ _ :: U, M, hM, h =>
      sound_insUnion hl U M hM (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- The state after a binding `e` whose extracted form is the existing variable `w`. -/
def stVar (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) (w : Ctxt.Var Δ s) : Tbl × Defs :=
  (insUnion S.1 (varLvl w) (unionAlts S e), S.2)

/-- The state after a binding `e` whose extracted form is the binding `e2`, bound at
    level `n`. -/
def stOne (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e e2 : Expr jasminDialect Δ s) (n : Nat) : Tbl × Defs :=
  (insUnion (insertT S.1 e2.op (argLvls e2.args) n) n (unionAlts S e),
    S.2.insert n (e2.op, argLvls e2.args))

/-- The state after a binding `e` whose extracted form is the bindings `e1` at level `n`
    and `e2` at level `n + 1`. -/
def stTwo (S : Tbl × Defs) {Δ : Ctxt jasminDialect} {s s1 : JasminTy}
    (e : Expr jasminDialect Δ s) (e1 : Expr jasminDialect Δ s1)
    (e2 : Expr jasminDialect (s1 :: Δ) s) (n : Nat) : Tbl × Defs :=
  (insUnion (insertT (insertT S.1 e1.op (argLvls e1.args) n) e2.op (argLvls e2.args) (n + 1))
      (n + 1) (unionAlts S e),
    (S.2.insert n (e1.op, argLvls e1.args)).insert (n + 1) (e2.op, argLvls e2.args))

theorem union_keys {S : Tbl × Defs} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr jasminDialect Δ s) :
    ∀ e3, Alt.one e3 ∈ unionAlts S e → evalKey V e3.op (argLvls e3.args) =
      some ⟨s, e.denote V⟩ := by
  intro e3 h3
  rw [evalKey_expr e3 V]
  have := unionAlts_denote hS e _ h3
  simp only [Alt.denote] at this
  rw [this]

theorem stVar_sound {S : Tbl × Defs} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr jasminDialect Δ s)
    {w : Ctxt.Var Δ s} (hc : choose S e = .var w) :
    StSound V (stVar S e w) ∧ w.lookup V = e.denote V := by
  have hw : w.lookup V = e.denote V := by
    have := extract_denote hS e
    rw [hc] at this
    exact this
  refine ⟨⟨?_, hS.2⟩, hw⟩
  refine sound_insUnion (getLvl_var w V) _ _ hS.1 ?_
  intro e3 h3
  rw [union_keys hS e e3 h3, hw]

theorem stOne_sound {S : Tbl × Defs} {Δ : Ctxt jasminDialect} {s : JasminTy}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr jasminDialect Δ s)
    {e2 : Expr jasminDialect Δ s} (hc : choose S e = .one e2) :
    StSound (Γ := s :: Δ) (V.extend (e2.denote V)) (stOne S e e2 Δ.length) ∧
      e2.denote V = e.denote V := by
  have hw : e2.denote V = e.denote V := by
    have := extract_denote hS e
    rw [hc] at this
    exact this
  have hk := evalKey_extend_some V (e2.denote V) (evalKey_expr e2 V)
  have hl := getLvl_extend_top V (e2.denote V)
  refine ⟨⟨?_, dsound_insert (dsound_extend _ hS.2) hk hl⟩, hw⟩
  refine sound_insUnion hl _ _ (sound_insertAt (sound_extend _ hS.1) hk hl) ?_
  intro e3 h3
  rw [hw]
  exact evalKey_extend_some V _ (union_keys hS e e3 h3)

theorem stTwo_sound {S : Tbl × Defs} {Δ : Ctxt jasminDialect} {s s1 : JasminTy}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr jasminDialect Δ s)
    {e1 : Expr jasminDialect Δ s1} {e2 : Expr jasminDialect (s1 :: Δ) s}
    (hc : choose S e = .two e1 e2) :
    StSound (Γ := s :: s1 :: Δ)
        ((V.extend (e1.denote V)).extend (e2.denote (V.extend (e1.denote V))))
        (stTwo S e e1 e2 Δ.length) ∧
      e2.denote (V.extend (e1.denote V)) = e.denote V := by
  have hw : e2.denote (V.extend (e1.denote V)) = e.denote V := by
    have := extract_denote hS e
    rw [hc] at this
    exact this
  set V1 := V.extend (e1.denote V) with hV1
  set x := e2.denote V1 with hx
  have hk1 := evalKey_extend_some V1 x (evalKey_extend_some V (e1.denote V) (evalKey_expr e1 V))
  have hl1 := getLvl_extend_some V1 x (getLvl_extend_top V (e1.denote V))
  have hk2 := evalKey_extend_some V1 x (evalKey_expr e2 V1)
  have hl2 : getLvl (Γ := s :: s1 :: Δ) (V1.extend x) (Δ.length + 1) = some ⟨s, x⟩ :=
    getLvl_extend_top V1 x
  refine ⟨⟨?_, ?_⟩, hw⟩
  · refine sound_insUnion hl2 _ _ (sound_insertAt (sound_insertAt
      (sound_extend _ (sound_extend _ hS.1)) hk1 hl1) hk2 hl2) ?_
    intro e3 h3
    rw [hw]
    exact evalKey_extend_some V1 _ (evalKey_extend_some V _ (union_keys hS e e3 h3))
  · exact dsound_insert (dsound_insert (dsound_extend _ (dsound_extend _ hS.2)) hk1 hl1) hk2 hl2

/-! ## 8. The pass -/

/-- The renaming that shifts past two fresh bindings. -/
def wk2 {Γ Δ : Ctxt jasminDialect} {s s1 : JasminTy} (ρ : Ctxt.Hom Γ Δ) :
    Ctxt.Hom Γ (s :: s1 :: Δ) :=
  fun v => (ρ v).there.there

theorem pullV_wk2 {Γ Δ : Ctxt jasminDialect} {s s1 : JasminTy} (ρ : Ctxt.Hom Γ Δ)
    (V : Ctxt.Valuation Δ) (x1 : ⟦s1⟧) (x : ⟦s⟧) :
    pullV (wk2 (s := s) (s1 := s1) ρ) ((V.extend x1).extend x) = pullV ρ V :=
  (pullV_weaken x (fun {_} v => Ctxt.Var.there (ρ v)) (V.extend x1)).trans
    (pullV_weaken x1 ρ V)

/-- The aegraph traversal under the renaming `ρ` and the state `S`: each binding is
    renamed, its e-class formed and hash-consed, and the extracted alternative emitted. -/
def agGo : {Γ Δ : Ctxt jasminDialect} → {t : JasminTy} → Ctxt.Hom Γ Δ → Tbl × Defs →
    Com jasminDialect Γ t → Com jasminDialect Δ t
  | _, _, _, ρ, _, .ret v => .ret (ρ v)
  | _, Δ, _, ρ, S, .var e body =>
      match choose S (e.rename ρ) with
      | .var w => agGo (consHom w ρ) (stVar S (e.rename ρ) w) body
      | .one e2 => .var e2 (agGo ρ.lift (stOne S (e.rename ρ) e2 Δ.length) body)
      | .two e1 e2 =>
          .var e1 (.var e2
            (agGo (consHom .here (wk2 ρ)) (stTwo S (e.rename ρ) e1 e2 Δ.length) body))

/-- **Denotation of the traversal.** Under a state sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`. -/
theorem agGo_denote : ∀ {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl × Defs) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Δ),
    StSound V S → (agGo ρ S c).denote V = c.denote (pullV ρ V)
  | _, _, _, ρ, _, .ret v, V, _ => CopyProp.Ctxt.Var.lookup_rename ρ v V
  | _, Δ, _, ρ, S, .var (t := s) e body, V, hS => by
      simp only [agGo]
      split
      · rename_i w hc
        obtain ⟨hS', hw⟩ := stVar_sound hS _ hc
        rw [agGo_denote _ _ body V hS', pullV_consHom, hw, Expr.denote_rename]
        rfl
      · rename_i e2 hc
        obtain ⟨hS', hw⟩ := stOne_sound hS _ hc
        simp only [Com.denote]
        rw [agGo_denote _ _ body _ hS', pullV_lift, hw, Expr.denote_rename]
      · rename_i s1 e1 e2 hc
        obtain ⟨hS', hw⟩ := stTwo_sound hS _ hc
        simp only [Com.denote]
        rw [agGo_denote _ _ body _ hS', pullV_consHom, pullV_wk2, Expr.denote_rename] at *
        show body.denote ((pullV ρ V).extend (e2.denote _)) = _
        rw [hw]

/-- **The aegraph pass**: the traversal from the identity renaming and the empty state. -/
def aegraphOpt {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  agGo (Ctxt.Hom.id Γ) (∅, ∅) c

theorem stSound_empty {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    StSound V ((∅, ∅) : Tbl × Defs) :=
  ⟨sound_empty V, dsound_empty V⟩

/-- **Denotation of the pass.** `aegraphOpt c` denotes the same function as `c`. -/
theorem aegraphOpt_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : (aegraphOpt c).denote = c.denote :=
  funext fun V => by rw [aegraphOpt, agGo_denote _ _ c V (stSound_empty V), pullV_id]

/-! ## 9. Cost -/

theorem agGo_cost_le : ∀ {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl × Defs) (c : Com jasminDialect Γ t),
    comCost (agGo ρ S c) ≤ comCost c
  | _, _, _, ρ, _, .ret v => Nat.le_refl _
  | _, Δ, _, ρ, S, .var (t := s) e body => by
      have hch := choose_cost_le S (e.rename ρ)
      simp only [agGo]
      split
      · rename_i w hc
        simp only [comCost]
        exact Nat.le_trans (agGo_cost_le _ _ body) (Nat.le_add_left _ _)
      · rename_i e2 hc
        rw [hc] at hch
        simp only [comCost]
        exact Nat.add_le_add hch (agGo_cost_le _ _ body)
      · rename_i s1 e1 e2 hc
        rw [hc] at hch
        simp only [comCost, Alt.cost] at hch ⊢
        have := agGo_cost_le (consHom .here (wk2 (s1 := s1) ρ))
          (stTwo S (e.rename ρ) e1 e2 Δ.length) body
        rw [← Nat.add_assoc]
        exact Nat.add_le_add hch this

/-- The pass does not increase `comCost`. -/
theorem aegraphOpt_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : comCost (aegraphOpt c) ≤ comCost c :=
  agGo_cost_le _ _ c

/-- The pass preserves the structural CT predicate `ctSafeComJ`. -/
theorem aegraphOpt_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : ctSafeComJ (aegraphOpt c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (aegraphOpt c), ctSafeComJ_true c]

/-! ## 10. Constant time under a leakage model

The bindings the rules emit are `regArith` and `regConst` bindings. Under a leakage model
whose `regArith` operations are quiet, the former emit no event, and a `regConst` binding
has no argument, so its events are the same at every valuation. The extracted alternative
of a binding is therefore the binding itself, hash-consed, or an alternative whose events
do not depend on the valuation. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)
open CatCrypt.Crypto.Optimizer.Rewrite.ComGVN (opLeak_length Expr.ctLeak_rename)

variable (L : LeakModel jasminDialect)

/-- The events of every binding an alternative emits are the same at every valuation. -/
def Alt.Indep {Δ : Ctxt jasminDialect} {s : JasminTy} : Alt Δ s → Prop
  | .var _ => True
  | .one e => ∀ V₁ V₂, Expr.ctLeak L e V₁ = Expr.ctLeak L e V₂
  | .two e1 e2 => (∀ V₁ V₂, Expr.ctLeak L e1 V₁ = Expr.ctLeak L e1 V₂) ∧
      (∀ V₁ V₂, Expr.ctLeak L e2 V₁ = Expr.ctLeak L e2 V₂)

variable {L}

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

theorem reduceOne_cases (M : Tbl) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : reduceOne M e = .one e ∨ (reduceOne M e).Indep L := by
  unfold reduceOne
  split
  · exact Or.inr trivial
  · exact Or.inl rfl

theorem reduceAlt_indep (M : Tbl) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (a : Alt Δ s) (ha : a.Indep L) : (reduceAlt M a).Indep L := by
  cases a with
  | var v => trivial
  | one e =>
      rcases reduceOne_cases (L := L) M e with h | h
      · show (reduceOne M e).Indep L
        rw [h]
        exact ha
      · exact h
  | two e1 e2 =>
      simp only [reduceAlt]
      split
      · rename_i w1 _
        rcases reduceOne_cases (L := L) M (e2.rename (consHom w1 (Ctxt.Hom.id Δ))) with h | h
        · rw [h]
          intro V₁ V₂
          rw [Expr.ctLeak_rename, Expr.ctLeak_rename]
          exact ha.2 _ _
        · exact h
      · exact ha

/-- The extracted alternative of `e` is `e` itself or has events independent of the
    valuation. -/
theorem choose_leak (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (S : Tbl × Defs)
    {Δ : Ctxt jasminDialect} {s : JasminTy} (e : Expr jasminDialect Δ s) :
    choose S e = .one e ∨ (choose S e).Indep L :=
  pick_prop _ (fun a => a = .one e ∨ a.Indep L) _ _ (reduceOne_cases S.1 e)
    (fun a ha _ => by
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      exact Or.inr (reduceAlt_indep S.1 a' (ruleAlts_indep hq S.2 e a' ha')))

/-- **Leakage of the traversal.** Under states sound for `V₁` and `V₂`, equal leakage of
    the input at the pulled-back valuations gives equal leakage of the output. -/
theorem agGo_ctLeak (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) :
    ∀ {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (S : Tbl × Defs)
      (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Δ), StSound V₁ S → StSound V₂ S →
      Com.ctLeak L c (pullV ρ V₁) = Com.ctLeak L c (pullV ρ V₂) →
      Com.ctLeak L (agGo ρ S c) V₁ = Com.ctLeak L (agGo ρ S c) V₂
  | _, _, _, ρ, _, .ret v, _, _, _, _, _ => rfl
  | _, Δ, _, ρ, S, .var e body, V₁, V₂, h₁, h₂, h => by
      simp only [Com.ctLeak] at h
      obtain ⟨hE, hB⟩ := List.append_inj h (opLeak_length L e.op _ _)
      rw [← Expr.ctLeak_rename, ← Expr.ctLeak_rename] at hE
      have hP := choose_leak hq S (e.rename ρ)
      simp only [agGo]
      split
      · rename_i w hc
        obtain ⟨hS₁, hw₁⟩ := stVar_sound h₁ _ hc
        obtain ⟨hS₂, hw₂⟩ := stVar_sound h₂ _ hc
        refine agGo_ctLeak hq _ _ body V₁ V₂ hS₁ hS₂ ?_
        rw [pullV_consHom, pullV_consHom, hw₁, hw₂, Expr.denote_rename, Expr.denote_rename]
        exact hB
      · rename_i e2 hc
        obtain ⟨hS₁, hw₁⟩ := stOne_sound h₁ _ hc
        obtain ⟨hS₂, hw₂⟩ := stOne_sound h₂ _ hc
        have hE2 : Expr.ctLeak L e2 V₁ = Expr.ctLeak L e2 V₂ := by
          rw [hc] at hP
          rcases hP with h' | h'
          · injection h' with h''
            subst h''
            exact hE
          · exact h' V₁ V₂
        simp only [Com.ctLeak]
        rw [hE2]
        congr 1
        refine agGo_ctLeak hq _ _ body _ _ hS₁ hS₂ ?_
        rw [pullV_lift, pullV_lift, hw₁, hw₂, Expr.denote_rename, Expr.denote_rename]
        exact hB
      · rename_i s1 e1 e2 hc
        obtain ⟨hS₁, hw₁⟩ := stTwo_sound h₁ _ hc
        obtain ⟨hS₂, hw₂⟩ := stTwo_sound h₂ _ hc
        have hI : (Alt.two e1 e2).Indep L := by
          rw [hc] at hP
          rcases hP with h' | h'
          · cases h'
          · exact h'
        simp only [Com.ctLeak]
        rw [hI.1 V₁ V₂, hI.2 _ (V₂.extend (e1.denote V₂))]
        congr 2
        refine agGo_ctLeak hq _ _ body _ _ hS₁ hS₂ ?_
        rw [pullV_consHom, pullV_consHom, pullV_wk2, pullV_wk2]
        show Com.ctLeak L body ((pullV ρ V₁).extend (e2.denote _)) =
          Com.ctLeak L body ((pullV ρ V₂).extend (e2.denote _))
        rw [hw₁, hw₂, Expr.denote_rename, Expr.denote_rename]
        exact hB

/-- **Leakage of the pass.** Under a leakage model whose `regArith` operations are quiet,
    equal leakage of `c` at two valuations gives equal leakage of `aegraphOpt c` there. -/
theorem aegraphOpt_ctLeak_eq (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V₁ V₂ : Ctxt.Valuation Γ) (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (aegraphOpt c) V₁ = Com.ctLeak L (aegraphOpt c) V₂ :=
  agGo_ctLeak hq _ _ c V₁ V₂ (stSound_empty V₁) (stSound_empty V₂)
    (by rw [pullV_id, pullV_id]; exact h)

/-- **Constant time of the pass.** Under a leakage model whose `regArith` operations are
    quiet, if `c` is constant time for the relation `R`, so is `aegraphOpt c`. -/
theorem aegraphOpt_constantTime (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (aegraphOpt c)) :=
  fun V₁ V₂ hR => aegraphOpt_ctLeak_eq hq c V₁ V₂ (h V₁ V₂ hR)

end Leak

end CatCrypt.Crypto.Optimizer.Rewrite.Aegraph
