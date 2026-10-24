/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole
public import CatCrypt.Crypto.SecureCompilation.Ascent.EgraphBlockEquality
public import CatCrypt.Crypto.Optimizer.Rewrite.ComGVN
public import CatCrypt.Crypto.Optimizer.Rewrite.Aegraph
public import CatCrypt.Crypto.Optimizer.ComRangeFold

/-!
# `Com jasminDialect` rewrite pipeline: peephole then equality-saturation

The two verified algebraic `Com → Com` passes over the typed VIR
`jasminDialect` —

* the bounded equality-saturation engine `Egraph.saturateCom` (algebraic
  identity/annihilator collapses under a known-constant environment), and
* the local syntactic peephole `Peephole.peepCom` (`sub a a ↦ xor a a`
  zeroing idiom, `and a a ↦ or a a` idempotent canonicalisation) —

are composed here into the canonical `Com`-level optimisation sequence.

## Ordering

The pipeline runs **peephole first, then equality-saturation**:

1. `peepCom` canonicalises the local two-address / zeroing idioms (it is
   purely syntactic — no constant analysis), exposing more `or a a` /
   `and a a` idempotent shapes;
2. `saturateCom` then fires the algebraic identity/annihilator rules
   (`x + 0 ↦ x`, `x * 0 ↦ 0`, `x * 1 ↦ x`, …) under the known-constant
   environment, to a fuel-bounded fixed point.

This is the *algebraic-canonicalisation* stage of the dual-IR optimiser.
The complementary *instruction-scheduling* stage runs one IR down, on the
`LowCT` block representation (`Optimizer.Pipeline.scheduleThenPipeline`,
which wires in the ILP list scheduler): the VIR `Com jasminDialect`
is canonicalised here, and the lowered `LowCT` block is scheduled there.

## What is proved

* `comAlgebraicPipeline_denote` — end-to-end denotation preservation of
  the composed (peephole then saturate) `Com → Com` transform, under a
  known-constant environment consistent with the valuation.  Chains
  `Peephole.peepCom_denote` with `Egraph.saturateCom_denote`.  **Not**
  `rfl` — the peephole and the saturation engine rewrite the
  `Com` term.
* `comAlgebraicPipeline_cost_le` — the composed transform is
  cost-non-increasing (the "extraction is no worse than the input" half of
  the equality-saturation contract, composed with the peephole's own
  cost-non-increase).
* `comRangeOpt`, `comRangeOpt_denote`, `comRangeOpt_cost_le` — the range stage: the
  bindings that the range analysis `ComRange` bounds to one point become constants, masks
  of operands already in range are dropped, selects on a decided condition are narrowed,
  a multiply by `1` becomes a copy and a carry-chain add at carry-in `0` becomes an add; the
  low half of an instruction pair of the x86 lowering (`ComGVN.pairLowOp`) is rewritten
  only when the high half of its pair is a constant of the stage (`pairHighFolds`); its
  denotation equality holds at every valuation.
* `optCom`, `optCom_denote` — the `Com` optimisation stage, the range stage followed by the
  acyclic e-graph pass `Aegraph.aegraphOpt` (rules at node creation, hash-consing,
  extraction), whose denotation equality holds at every valuation; `optCom_cost_le`
  carries the cost bound.
* `comAlgebraicPipeline_ctLeak` — under a leakage model whose `regArith` operations are
  quiet, the composed transform keeps the leakage of a program at every valuation;
  `comRangeOpt_constantTime`, `optCom_ctLeak_eq`, `optCom_constantTime` — under the same
  hypothesis the range stage and the stage map equal leakage to equal leakage and keep
  constant time for every relation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## §1  The composed algebraic-canonicalisation transform

Peephole first (syntactic local cleanups), then the fuel-bounded
equality-saturation engine (algebraic identity/annihilator collapses). -/

/-- The composed `Com → Com` algebraic-canonicalisation transform:
    peephole, then `fuel`-bounded equality saturation under the
    known-constant environment `k`. -/
def comAlgebraicPipeline {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    Com jasminDialect Γ t :=
  saturateCom fuel (peepCom c) k

/-! ## §2  End-to-end denotation preservation -/

/-- **Composed denotation preservation.**  Running the peephole then the
    equality-saturation engine preserves the denotation of the `Com`, for
    any known-constant environment `k` consistent with the valuation `V`.
    Chains `peepCom_denote` with `saturateCom_denote`.  This is exactly
    `Peephole.peep_then_saturate_denote`, re-exported as the headline
    pipeline theorem. -/
theorem comAlgebraicPipeline_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (comAlgebraicPipeline fuel c k).denote V = c.denote V := by
  unfold comAlgebraicPipeline
  rw [saturateCom_denote fuel (peepCom c) k V hk, peepCom_denote c V]

/-! ## §4  Cost non-increase -/

/-- **The composed transform is cost-non-increasing.**  The peephole is
    cost-non-increasing (`peepCom_cost_le`) and so is the saturation engine
    (`saturate_cost_le`); transitivity gives the composed bound. -/
theorem comAlgebraicPipeline_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    comCost (comAlgebraicPipeline fuel c k) ≤ comCost c := by
  unfold comAlgebraicPipeline
  exact Nat.le_trans (saturate_cost_le fuel (peepCom c) k) (peepCom_cost_le c)

/-! ## §5  The range stage

`comRangeOpt` rewrites each binding with the abstract values of the range analysis
`ComRange.exprAbs`, run from the full lane range of every input and refined at the
comparisons, the carry-chain add and the select (`stageOpAbs`). Its rules are identities of
the operations for all operands within their intervals:

* a register binding whose interval is one point `n` becomes `regConst w n`
  (`ComRangeFold.pointExpr`). This folds a comparison that the intervals of its operands
  decide, a carry-out bit that they exclude or force, a high multiply whose operands bound
  it to one point, and every other operation whose interval is one point;
* `a &&& b` with `b` the constant `2^k - 1` and `a < 2^k` becomes the copy `a ||| a`, and
  symmetrically in the operands;
* `select c a b` with `c` one point becomes the copy of `a` or of `b`;
* `a * b` with `b` the constant `1` becomes the copy `a ||| a`, and symmetrically in the
  operands (`mulPair_of_one`: the high word of the pair is then `0`);
* `addCarryLo w a b c` with `c` the constant `0` becomes `a + b` (`carryPair_of_zero`: the
  carry-out of the pair is then the bit the intervals decide).

The x86 lowering pairs the `MUL` of a multiply with the `MULXHI` of the high multiply on the
same sources, and reads the carry-out of `addCarryHi` by `setc` from the flags of the `ADCX`
of the `addCarryLo` before it. A multiply or a carry-chain add (`ComGVN.pairLowOp`) is
therefore rewritten only when the intervals of its operands make the high half of its pair a
point (`pairHighFolds`): the high multiply of the same operands, and the carry-out of the same
operands at every carry-in, are then constants of the stage (`pairHighFolds_mulhi`,
`pairHighFolds_addCarryHi`), and no pair is separated. The input intervals hold at every
valuation, so the stage needs no hypothesis on it. Each rewritten binding is a `regConst`
binding, of cost 1 and without arguments, or a `regArith` binding of cost 1 that is not a
multiply. -/

section Range

open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.Optimizer.ComRangeFold (pointExpr pointExpr_denote)

/-- The truth value of `x < y` for `x.toNat` in `a` and `y.toNat` in `b`, when the
    intervals decide it. -/
def ltDecide? (a b : Iv) : Option Bool :=
  if a.2 < b.1 then some true else if b.2 ≤ a.1 then some false else none

/-- The truth value of `x ≤ y` for `x.toNat` in `a` and `y.toNat` in `b`, when the
    intervals decide it. -/
def leDecide? (a b : Iv) : Option Bool :=
  if a.2 ≤ b.1 then some true else if b.2 < a.1 then some false else none

/-- The truth value of `x = y` for `x.toNat` in `a` and `y.toNat` in `b`, when the
    intervals decide it. -/
def eqDecide? (a b : Iv) : Option Bool :=
  if a.2 < b.1 ∨ b.2 < a.1 then some false
  else if a.1 = a.2 ∧ b.1 = b.2 ∧ a.1 = b.1 then some true else none

/-- The truth value of the relation `c` on `x` and `y` for `x.toNat` in `a` and `y.toNat`
    in `b`, when the intervals decide it. -/
def cmpDecide? : JasminCmp → Iv → Iv → Option Bool
  | .eq, a, b => eqDecide? a b
  | .ne, a, b => (eqDecide? a b).map (!·)
  | .ult, a, b => ltDecide? a b
  | .ule, a, b => leDecide? a b
  | .ugt, a, b => ltDecide? b a
  | .uge, a, b => leDecide? b a

/-- The carry-out bit of `x + y + cin` for `x.toNat` in `a`, `y.toNat` in `b` and a one-bit
    `cin`, when the intervals decide it. -/
def carryDecide? (w : Nat) (a b : Iv) : Option Bool :=
  if a.2 + b.2 + 1 < 2 ^ w then some false
  else if (2 : Int) ^ w ≤ a.1 + b.1 then some true else none

/-- The one-bit word of a truth value. -/
def bitOf (r : Bool) : BitVec 1 := if r then 1#1 else 0#1

/-- The one-point interval of a truth value. -/
def bitIv (r : Bool) : Iv := if r then (1, 1) else (0, 0)

/-- `a &&& b = a` for `a` in the interval `ia` and `b` in `ib`: the lane interval of `ib` is
    one point `2^k - 1` and the lane interval of `ia` lies below `2^k`. -/
def maskDrops (w : Nat) (ia ib : Iv) : Bool :=
  match ivSingle? (ivLane w ib) with
  | some n => decide (n + 1 = 2 ^ Nat.log2 (n + 1)) &&
      decide ((ivLane w ia).2 < 2 ^ Nat.log2 (n + 1))
  | none => false

section Facts

variable {w : Nat}

theorem ltDecide?_sound {a b : Iv} {x y : Nat} (ha : a.1 ≤ (x : Int) ∧ (x : Int) ≤ a.2)
    (hb : b.1 ≤ (y : Int) ∧ (y : Int) ≤ b.2) {r : Bool} (h : ltDecide? a b = some r) :
    decide (x < y) = r := by
  unfold ltDecide? at h
  split_ifs at h <;> cases h <;> simp <;> omega

theorem leDecide?_sound {a b : Iv} {x y : Nat} (ha : a.1 ≤ (x : Int) ∧ (x : Int) ≤ a.2)
    (hb : b.1 ≤ (y : Int) ∧ (y : Int) ≤ b.2) {r : Bool} (h : leDecide? a b = some r) :
    decide (x ≤ y) = r := by
  unfold leDecide? at h
  split_ifs at h <;> cases h <;> simp <;> omega

theorem eqDecide?_sound {a b : Iv} {x y : Nat} (ha : a.1 ≤ (x : Int) ∧ (x : Int) ≤ a.2)
    (hb : b.1 ≤ (y : Int) ∧ (y : Int) ≤ b.2) {r : Bool} (h : eqDecide? a b = some r) :
    decide (x = y) = r := by
  unfold eqDecide? at h
  split_ifs at h <;> cases h <;> simp <;> omega

/-- A decided relation holds exactly when the decision says so. -/
theorem cmpDecide?_sound (c : JasminCmp) {a b : Iv} {x y : BitVec w}
    (ha : a.1 ≤ (x.toNat : Int) ∧ (x.toNat : Int) ≤ a.2)
    (hb : b.1 ≤ (y.toNat : Int) ∧ (y.toNat : Int) ≤ b.2) {r : Bool}
    (h : cmpDecide? c a b = some r) : c.holds x y = r := by
  have heq : (x == y) = decide (x.toNat = y.toNat) := by
    rw [Bool.eq_iff_iff]; simp [BitVec.toNat_eq]
  cases c with
  | eq => show (x == y) = r; rw [heq]; exact eqDecide?_sound ha hb h
  | ne =>
    simp only [cmpDecide?, Option.map_eq_some_iff] at h
    obtain ⟨r', h', rfl⟩ := h
    show (x != y) = !r'
    rw [bne, heq, eqDecide?_sound ha hb h']
  | ult => simpa [JasminCmp.holds, BitVec.ult] using ltDecide?_sound ha hb h
  | ule => simpa [JasminCmp.holds, BitVec.ule] using leDecide?_sound ha hb h
  | ugt => simpa [JasminCmp.holds, BitVec.ult] using ltDecide?_sound hb ha h
  | uge => simpa [JasminCmp.holds, BitVec.ule] using leDecide?_sound hb ha h

/-- A decided carry-out bit is the bit of the decision. -/
theorem carryDecide?_sound {a b : Iv} {x y : BitVec w} (cin : BitVec 1)
    (ha : a.1 ≤ (x.toNat : Int) ∧ (x.toNat : Int) ≤ a.2)
    (hb : b.1 ≤ (y.toNat : Int) ∧ (y.toNat : Int) ≤ b.2) {r : Bool}
    (h : carryDecide? w a b = some r) : carryOutBit x y cin = bitOf r := by
  have hc : cin.toNat < 2 := cin.isLt
  have hp : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by norm_num
  unfold carryDecide? at h
  unfold carryOutBit bitOf
  by_cases hs : x.toNat + y.toNat + cin.toNat ≥ 2 ^ w
  · have hs' : (2 : Int) ^ w ≤ x.toNat + y.toNat + cin.toNat := by
      rw [← hp]; exact_mod_cast hs
    rw [ite_eq_left hs]
    split_ifs at h <;> cases h
    · omega
    · rfl
  · have hs' : (x.toNat : Int) + y.toNat + cin.toNat < 2 ^ w := by
      rw [← hp]; exact_mod_cast Nat.lt_of_not_le hs
    rw [ite_eq_right hs]
    split_ifs at h <;> cases h
    · rfl
    · omega

theorem mem_bitIv (r : Bool) : (bitIv r).Mem 1 (bitOf r) := by
  cases r <;> exact Iv.mem_of_bounds (by decide) (by decide)

/-- `x &&& y = x` when `maskDrops` holds of the intervals of `x` and `y`. -/
theorem and_eq_of_maskDrops {ia ib : Iv} {x y : BitVec w} (hx : ia.Mem w x) (hy : ib.Mem w y)
    (h : maskDrops w ia ib = true) : x &&& y = x := by
  unfold maskDrops at h
  split at h
  · rename_i n hn
    have hyn : y.toNat = n := Iv.toNat_eq_of_single hy hn
    have hxb := (Iv.mem_lane hx).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hxk : x.toNat < 2 ^ Nat.log2 (n + 1) := by
      have : ((x.toNat : Nat) : Int) < ((2 ^ Nat.log2 (n + 1) : Nat) : Int) := by
        push_cast; omega
      exact_mod_cast this
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hyn, show n = 2 ^ Nat.log2 (n + 1) - 1 by omega,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hxk]
  · cases h

/-- The multiply pair at an operand equal to `1`: the low word `x * y` is `x` and the high
    word `mulHiW x y` is `0`. -/
theorem mulPair_of_one {x y : BitVec w} (hy : y.toNat = 1) : x * y = x ∧ mulHiW x y = 0 := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, hy, Nat.mul_one, Nat.mod_eq_of_lt x.isLt]
  · unfold mulHiW
    rw [hy, Nat.mul_one, Nat.div_eq_of_lt x.isLt]
    rfl

/-- The carry-chain add pair at carry-in `0`, for `x.toNat` in `a` and `y.toNat` in `b` when
    the intervals decide the carry-out: the data word is `x + y` and the carry-out bit is the
    bit of the decision. -/
theorem carryPair_of_zero {a b : Iv} {x y : BitVec w} {ci : BitVec 1} (hci : ci.toNat = 0)
    (ha : a.1 ≤ (x.toNat : Int) ∧ (x.toNat : Int) ≤ a.2)
    (hb : b.1 ≤ (y.toNat : Int) ∧ (y.toNat : Int) ≤ b.2) {r : Bool}
    (h : carryDecide? w a b = some r) :
    addCarryWord x y ci = x + y ∧ carryOutBit x y ci = bitOf r :=
  ⟨by unfold addCarryWord; rw [hci]; simp, carryDecide?_sound ci ha hb h⟩

end Facts

variable {Γ : JCtxt}

/-- The abstract value of an operation on the variables `args`: `ComRange.opAbs`, refined at
    a comparison and a carry-out bit that the operand intervals decide, at the carry-chain
    add with carry-in `0`, and at the select on a one-point condition. -/
def stageOpAbs (A : AEnv Γ) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    (len : Nat := Γ.length) : AVal :=
  match op, args with
  | .cmp c w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    match cmpDecide? c (ivLane w (hget A a).1) (ivLane w (hget A b).1) with
    | some r => (bitIv r, .none)
    | none => (ivTop 1, .none)
  | .cmpImm c w n, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    match cmpDecide? c (ivLane w (hget A a).1) (ivConst w n) with
    | some r => (bitIv r, .none)
    | none => (ivTop 1, .none)
  | .addCarryHi w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    match carryDecide? w (ivLane w (hget A a).1) (ivLane w (hget A b).1) with
    | some r => (bitIv r, .none)
    | none => (ivTop 1, .none)
  | .addCarryLo w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    let ci : Ctxt.Var Γ (.reg 1) := args.tail.tail.head
    match ivSingle? (ivLane 1 (hget A ci).1) with
    | some 0 => (ivAdd w (hget A a).1 (hget A b).1, .none)
    | _ => (ivTop w, .none)
  | .select w, args =>
    let ci : Ctxt.Var Γ (.reg 1) := args.head
    let a : Ctxt.Var Γ (.reg w) := args.tail.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.tail.head
    match ivSingle? (ivLane 1 (hget A ci).1) with
    | some 1 => hget A a
    | some 0 => hget A b
    | _ => (ivTop w, .none)
  | op, args => opAbs A op args len

/-- The abstract value of an expression for the range stage. -/
def stageAbs (A : AEnv Γ) {t : JasminTy} (e : Expr jasminDialect Γ t)
    (len : Nat := Γ.length) : AVal :=
  stageOpAbs A e.op e.args len

/-- A one-bit word whose `toNat` is `0` is `0#1`, and one whose `toNat` is `1` is `1#1`. -/
theorem bit_eq_of_toNat {x : BitVec 1} {k : Nat} (h : x.toNat = k) :
    (k = 0 → x = 0#1) ∧ (k = 1 → x = 1#1) :=
  ⟨fun hk => BitVec.eq_of_toNat_eq (by simp [h, hk]),
    fun hk => BitVec.eq_of_toNat_eq (by simp [h, hk])⟩

theorem stageOpAbs_sound {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    {len : Nat} (hlen : len = Γ.length) :
    ValOK V (DialectSignature.ret (d := jasminDialect) op) (stageOpAbs A op args len)
      (DialectDenote.denote op (Expr.lookupArgs args V)) := by
  subst hlen
  cases op
  case cmp c w =>
    match args with
    | .cons a (.cons b .nil) =>
    simp only [stageOpAbs, HVector.head, HVector.tail]
    split
    · rename_i r hr
      have hh := cmpDecide?_sound c (Iv.mem_lane (hA.reg a).1) (Iv.mem_lane (hA.reg b).1) hr
      refine ⟨?_, SymOK.none _ _ _⟩
      show (bitIv r).Mem 1 (cmpBit c (regVal V a) (regVal V b))
      rw [show cmpBit c (regVal V a) (regVal V b) = bitOf r by
        unfold cmpBit bitOf; rw [hh]]
      exact mem_bitIv r
    · exact ⟨Iv.mem_top _, SymOK.none _ _ _⟩
  case cmpImm c w n =>
    match args with
    | .cons a .nil =>
    simp only [stageOpAbs, HVector.head]
    split
    · rename_i r hr
      have hk : (ivConst w n).1 ≤ ((BitVec.ofNat w n).toNat : Int) ∧
          ((BitVec.ofNat w n).toNat : Int) ≤ (ivConst w n).2 := by
        simp [ivConst]
      have hh := cmpDecide?_sound c (Iv.mem_lane (hA.reg a).1) hk hr
      refine ⟨?_, SymOK.none _ _ _⟩
      show (bitIv r).Mem 1 (cmpBit c (regVal V a) (BitVec.ofNat w n))
      rw [show cmpBit c (regVal V a) (BitVec.ofNat w n) = bitOf r by
        unfold cmpBit bitOf; rw [hh]]
      exact mem_bitIv r
    · exact ⟨Iv.mem_top _, SymOK.none _ _ _⟩
  case addCarryHi w =>
    match args with
    | .cons a (.cons b (.cons ci .nil)) =>
    simp only [stageOpAbs, HVector.head, HVector.tail]
    split
    · rename_i r hr
      refine ⟨?_, SymOK.none _ _ _⟩
      show (bitIv r).Mem 1 (carryOutBit (regVal V a) (regVal V b) (regVal V ci))
      rw [carryDecide?_sound _ (Iv.mem_lane (hA.reg a).1) (Iv.mem_lane (hA.reg b).1) hr]
      exact mem_bitIv r
    · exact ⟨Iv.mem_top _, SymOK.none _ _ _⟩
  case addCarryLo w =>
    match args with
    | .cons a (.cons b (.cons ci .nil)) =>
    simp only [stageOpAbs, HVector.head, HVector.tail]
    split
    · rename_i hc
      have h0 := (bit_eq_of_toNat (Iv.toNat_eq_of_single (hA.reg ci).1 hc)).1 rfl
      refine ⟨?_, SymOK.none _ _ _⟩
      show (ivAdd w (hget A a).1 (hget A b).1).Mem w
        (addCarryWord (regVal V a) (regVal V b) (regVal V ci))
      rw [show addCarryWord (regVal V a) (regVal V b) (regVal V ci) = regVal V a + regVal V b by
        unfold addCarryWord; rw [h0]; simp]
      exact Iv.mem_add (hA.reg a).1 (hA.reg b).1
    · exact ⟨Iv.mem_top _, SymOK.none _ _ _⟩
  case select w =>
    match args with
    | .cons ci (.cons a (.cons b .nil)) =>
    simp only [stageOpAbs, HVector.head, HVector.tail]
    split
    · rename_i hc
      have h1 := (bit_eq_of_toNat (Iv.toNat_eq_of_single (hA.reg ci).1 hc)).2 rfl
      show ValOK V (.reg w) (hget A a) (selectW (regVal V ci) (regVal V a) (regVal V b))
      rw [show selectW (regVal V ci) (regVal V a) (regVal V b) = regVal V a by
        unfold selectW; rw [ite_eq_left h1]]
      exact hA (.reg w) a
    · rename_i hc
      have h0 := (bit_eq_of_toNat (Iv.toNat_eq_of_single (hA.reg ci).1 hc)).1 rfl
      show ValOK V (.reg w) (hget A b) (selectW (regVal V ci) (regVal V a) (regVal V b))
      rw [show selectW (regVal V ci) (regVal V a) (regVal V b) = regVal V b by
        unfold selectW; rw [ite_eq_right (by rw [h0]; decide)]]
      exact hA (.reg w) b
    · exact ⟨Iv.mem_top _, SymOK.none _ _ _⟩
  all_goals exact opAbs_sound hA _ _

/-- The abstract value of an expression for the range stage holds of its value. -/
theorem stageAbs_sound {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V) {len : Nat}
    (hlen : len = Γ.length) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    ValOK V t (stageAbs A e len) (e.denote V) := by
  rcases e with ⟨op, rfl, args⟩
  exact stageOpAbs_sound hA op args hlen

/-- The rewrites of the range stage other than the point rule: the dropped mask, the
    multiply by `1`, the carry-chain add at carry-in `0` and the select on a one-point
    condition. -/
def ruleOp (A : AEnv Γ) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    Option (Expr jasminDialect Γ (DialectSignature.ret (d := jasminDialect) op)) :=
  match op, args with
  | .regArith .and w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    if maskDrops w (hget A a).1 (hget A b).1 then some (binE .or a a)
    else if maskDrops w (hget A b).1 (hget A a).1 then some (binE .or b b)
    else none
  | .regArith .mul w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    if ivSingle? (ivLane w (hget A b).1) = some 1 then some (binE .or a a)
    else if ivSingle? (ivLane w (hget A a).1) = some 1 then some (binE .or b b)
    else none
  | .addCarryLo w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    let ci : Ctxt.Var Γ (.reg 1) := args.tail.tail.head
    match ivSingle? (ivLane 1 (hget A ci).1) with
    | some 0 => some (binE .add a b)
    | _ => none
  | .select w, args =>
    let ci : Ctxt.Var Γ (.reg 1) := args.head
    let a : Ctxt.Var Γ (.reg w) := args.tail.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.tail.head
    match ivSingle? (ivLane 1 (hget A ci).1) with
    | some 1 => some (binE .or a a)
    | some 0 => some (binE .or b b)
    | _ => none
  | _, _ => none

/-- A rewrite of `ruleOp` is a `regArith` operation other than a multiply. -/
theorem ruleOp_op (A : AEnv Γ) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    {e' : Expr jasminDialect Γ (DialectSignature.ret (d := jasminDialect) op)}
    (h : ruleOp A op args = some e') : ∃ bop w, e'.op = .regArith bop w ∧ bop ≠ .mul := by
  cases op
  case regArith bop w =>
    cases bop
    case and =>
      simp only [ruleOp] at h
      split_ifs at h <;> cases h <;> exact ⟨_, _, rfl, by decide⟩
    case mul =>
      simp only [ruleOp] at h
      split_ifs at h <;> cases h <;> exact ⟨_, _, rfl, by decide⟩
    all_goals simp [ruleOp] at h
  case addCarryLo w =>
    simp only [ruleOp] at h
    split at h <;> cases h
    exact ⟨_, _, rfl, by decide⟩
  case select w =>
    simp only [ruleOp] at h
    split at h <;> cases h <;> exact ⟨_, _, rfl, by decide⟩
  all_goals simp [ruleOp] at h

/-- A rewrite of `ruleOp` denotes the value of the operation. -/
theorem ruleOp_sound {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    {e' : Expr jasminDialect Γ (DialectSignature.ret (d := jasminDialect) op)}
    (h : ruleOp A op args = some e') :
    e'.denote V = DialectDenote.denote op (Expr.lookupArgs args V) := by
  cases op
  case regArith bop w =>
    cases bop
    case and =>
      match args with
      | .cons a (.cons b .nil) =>
      simp only [ruleOp, HVector.head, HVector.tail] at h
      split_ifs at h with h1 h2
      · cases h
        show regVal V a ||| regVal V a = regVal V a &&& regVal V b
        rw [and_eq_of_maskDrops (hA.reg a).1 (hA.reg b).1 h1, BitVec.or_self]
      · cases h
        show regVal V b ||| regVal V b = regVal V a &&& regVal V b
        rw [BitVec.and_comm, and_eq_of_maskDrops (hA.reg b).1 (hA.reg a).1 h2, BitVec.or_self]
    case mul =>
      match args with
      | .cons a (.cons b .nil) =>
      simp only [ruleOp, HVector.head, HVector.tail] at h
      split_ifs at h with h1 h2
      · cases h
        show regVal V a ||| regVal V a = regVal V a * regVal V b
        rw [BitVec.or_self, (mulPair_of_one (Iv.toNat_eq_of_single (hA.reg b).1 h1)).1]
      · cases h
        show regVal V b ||| regVal V b = regVal V a * regVal V b
        rw [BitVec.or_self, BitVec.mul_comm,
          (mulPair_of_one (Iv.toNat_eq_of_single (hA.reg a).1 h2)).1]
    all_goals simp [ruleOp] at h
  case addCarryLo w =>
    match args with
    | .cons a (.cons b (.cons ci .nil)) =>
    simp only [ruleOp, HVector.head, HVector.tail] at h
    split at h
    · rename_i hc
      cases h
      show regVal V a + regVal V b = addCarryWord (regVal V a) (regVal V b) (regVal V ci)
      unfold addCarryWord
      rw [Iv.toNat_eq_of_single (hA.reg ci).1 hc]
      simp
    · cases h
  case select w =>
    match args with
    | .cons ci (.cons a (.cons b .nil)) =>
    simp only [ruleOp, HVector.head, HVector.tail] at h
    split at h
    · rename_i hc
      cases h
      have h1 := (bit_eq_of_toNat (Iv.toNat_eq_of_single (hA.reg ci).1 hc)).2 rfl
      show regVal V a ||| regVal V a = selectW (regVal V ci) (regVal V a) (regVal V b)
      rw [BitVec.or_self]; unfold selectW; rw [ite_eq_left h1]
    · rename_i hc
      cases h
      have h0 := (bit_eq_of_toNat (Iv.toNat_eq_of_single (hA.reg ci).1 hc)).1 rfl
      show regVal V b ||| regVal V b = selectW (regVal V ci) (regVal V a) (regVal V b)
      rw [BitVec.or_self]; unfold selectW; rw [ite_eq_right (by rw [h0]; decide)]
    · cases h
  all_goals simp [ruleOp] at h

/-- The rewrites of the range stage other than the point rule (`ruleOp`). -/
def rangeRule (A : AEnv Γ) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Expr jasminDialect Γ t :=
  match ruleOp A e.op e.args with
  | some e' => e.retTy_eq ▸ e'
  | none => e

/-- The high half of the instruction pair whose low half is `op args` is one point of the
    range stage: `mulhi w a b` for the multiply `a * b`, and `addCarryHi w a b c` for the
    carry-chain add `addCarryLo w a b ci`, at every carry-in `c`. The stage replaces such a
    high half by a constant (`pairHighFolds_mulhi`, `pairHighFolds_addCarryHi`). The value
    is `true` at every other operation. -/
def pairHighFolds (A : AEnv Γ) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    Bool :=
  match op, args with
  | .regArith .mul w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    (ivSingle? (ivLane w (ivMulhi w (hget A a).1 (hget A b).1))).isSome
  | .addCarryLo w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    (carryDecide? w (ivLane w (hget A a).1) (ivLane w (hget A b).1)).isSome
  | _, _ => true

/-- When `pairHighFolds` holds of the multiply `a * b`, the range stage binds the high
    multiply of `a` and `b`, in either order, to a constant. -/
theorem pairHighFolds_mulhi (A : AEnv Γ) {w : Nat} (a b : Ctxt.Var Γ (.reg w)) (len : Nat)
    (h : pairHighFolds A (.regArith .mul w) (.cons a (.cons b .nil)) = true) :
    (pointExpr (Γ := Γ) (.reg w)
        (stageOpAbs A (.mulhi w) (.cons a (.cons b .nil)) len).1).isSome = true ∧
      (pointExpr (Γ := Γ) (.reg w)
        (stageOpAbs A (.mulhi w) (.cons b (.cons a .nil)) len).1).isSome = true := by
  have hc : ivMulhi w (hget A b).1 (hget A a).1 = ivMulhi w (hget A a).1 (hget A b).1 := by
    simp only [ivMulhi, Int.mul_comm]
  simp only [pairHighFolds, HVector.head, HVector.tail] at h
  have e1 : stageOpAbs A (.mulhi w) (.cons a (.cons b .nil)) len =
      (ivMulhi w (hget A a).1 (hget A b).1, .none) := rfl
  have e2 : stageOpAbs A (.mulhi w) (.cons b (.cons a .nil)) len =
      (ivMulhi w (hget A b).1 (hget A a).1, .none) := rfl
  rw [e1, e2, hc]
  simp only [pointExpr, Option.isSome_map]
  exact ⟨h, h⟩

/-- When `pairHighFolds` holds of the carry-chain add `addCarryLo w a b ci`, the range stage
    binds the carry-out `addCarryHi w a b c` to a constant at every carry-in `c`. -/
theorem pairHighFolds_addCarryHi (A : AEnv Γ) {w : Nat} (a b : Ctxt.Var Γ (.reg w))
    (ci c : Ctxt.Var Γ (.reg 1)) (len : Nat)
    (h : pairHighFolds A (.addCarryLo w) (.cons a (.cons b (.cons ci .nil))) = true) :
    (pointExpr (Γ := Γ) (.reg 1)
        (stageOpAbs A (.addCarryHi w) (.cons a (.cons b (.cons c .nil))) len).1).isSome
      = true := by
  simp only [pairHighFolds, HVector.head, HVector.tail, Option.isSome_iff_exists] at h
  obtain ⟨r, hr⟩ := h
  simp only [stageOpAbs, HVector.head, HVector.tail, hr, pointExpr, Option.isSome_map]
  cases r <;> rfl

/-- The rewrite of one binding by the range stage, in a context of length `len`. A low half
    of an instruction pair of the x86 lowering (`ComGVN.pairLowOp`) is kept unless the stage
    binds the high half of the pair to a constant (`pairHighFolds`), so that no pair is
    separated. -/
def rangeExpr (A : AEnv Γ) (len : Nat) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Expr jasminDialect Γ t :=
  if ComGVN.pairLowOp e.op && !pairHighFolds A e.op e.args then e else
  match pointExpr t (stageAbs A e len).1 with
  | some e' => e'
  | none => rangeRule A e

theorem rangeRule_denote {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : (rangeRule A e).denote V = e.denote V := by
  rcases e with ⟨op, rfl, args⟩
  unfold rangeRule
  split
  · rename_i e' he
    exact ruleOp_sound hA op args he
  · rfl

theorem rangeExpr_denote {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V) {len : Nat}
    (hlen : len = Γ.length) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    (rangeExpr A len e).denote V = e.denote V := by
  unfold rangeExpr
  split
  · rfl
  split
  · rename_i e' he
    exact pointExpr_denote (stageAbs_sound hA hlen e) he
  · exact rangeRule_denote hA e

/-- Every operation costs at least 1. -/
theorem one_le_opCost (op : JasminOp) : 1 ≤ opCost op := by
  unfold opCost; split <;> omega

theorem rangeRule_cost_le (A : AEnv Γ) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    opCost (rangeRule A e).op ≤ opCost e.op := by
  rcases e with ⟨op, rfl, args⟩
  unfold rangeRule
  split
  · rename_i e' he
    obtain ⟨bop, w, hop, hne⟩ := ruleOp_op A op args he
    show opCost e'.op ≤ opCost op
    rw [hop]
    cases bop <;> first | exact absurd rfl hne | exact one_le_opCost op
  · exact Nat.le_refl _

theorem rangeExpr_cost_le (A : AEnv Γ) (len : Nat) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : opCost (rangeExpr A len e).op ≤ opCost e.op := by
  unfold rangeExpr
  split
  · exact Nat.le_refl _
  split
  · rename_i e' he
    cases t with
    | reg w =>
      simp only [pointExpr, Option.map_eq_some_iff] at he
      obtain ⟨n, -, rfl⟩ := he
      exact one_le_opCost _
    | _ => simp [pointExpr] at he
  · exact rangeRule_cost_le A e

/-- The range stage from the abstract environment `A` of a context of length `len`. -/
def rangeCom : {Γ : JCtxt} → {t : JasminTy} → AEnv Γ → Nat →
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | _, _, _, _, .ret v => .ret v
  | _, _, A, len, .var e body =>
    .var (rangeExpr A len e)
      (rangeCom (HVector.cons (f := fun _ => AVal) (stageAbs A e len) A) (len + 1) body)

theorem rangeCom_denote : ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ) (len : Nat)
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ), len = Γ.length → EnvOK A V →
    (rangeCom A len c).denote V = c.denote V
  | _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, A, len, .var e body, V, hlen, hA => by
    simp only [rangeCom, Com.denote]
    rw [rangeExpr_denote hA hlen e]
    exact rangeCom_denote _ (len + 1) body _ (by simp [hlen])
      (hA.cons (stageAbs_sound hA hlen e))

theorem rangeCom_cost_le : ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ) (len : Nat)
    (c : Com jasminDialect Γ t), comCost (rangeCom A len c) ≤ comCost c
  | _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, A, len, .var e body => by
    simp only [rangeCom, comCost]
    exact Nat.add_le_add (rangeExpr_cost_le A len e) (rangeCom_cost_le _ _ body)

/-- The abstract environment of the full lane range of every variable, with no facts. -/
def topEnv : (Γ : JCtxt) → AEnv Γ
  | [] => .nil
  | t :: Γ => HVector.cons (f := fun _ => AVal) (tyTop t, .none) (topEnv Γ)

theorem hget_topEnv : ∀ {Γ : JCtxt} {t : JasminTy} (v : Ctxt.Var Γ t),
    hget (topEnv Γ) v = (tyTop t, .none)
  | _ :: _, _, .here => rfl
  | _ :: _, _, .there v => hget_topEnv v

theorem envOK_topEnv {Γ : JCtxt} (V : Ctxt.Valuation Γ) : EnvOK (topEnv Γ) V := by
  intro t v
  rw [hget_topEnv]
  exact valOK_top V t _

/-- **The range stage**: the range rewrites from the full lane range of every input. -/
def comRangeOpt {t : JasminTy} (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  rangeCom (topEnv Γ) Γ.length c

/-- **Denotation of the range stage.** `comRangeOpt c` denotes the same function as `c`. -/
theorem comRangeOpt_denote {t : JasminTy} (c : Com jasminDialect Γ t) :
    (comRangeOpt c).denote = c.denote :=
  funext fun V => rangeCom_denote _ _ c V rfl (envOK_topEnv V)

/-- The range stage does not increase `comCost`. -/
theorem comRangeOpt_cost_le {t : JasminTy} (c : Com jasminDialect Γ t) :
    comCost (comRangeOpt c) ≤ comCost c :=
  rangeCom_cost_le _ _ c

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)
open CatCrypt.Crypto.Optimizer.Rewrite.ComGVN (opLeak_length)

variable {L : LeakModel jasminDialect}

/-- Under a leakage model whose `regArith` operations are quiet, a binding that `rangeRule`
    rewrites emits no event: its rewrite is a `regArith` binding. -/
theorem rangeRule_leak (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (A : AEnv Γ)
    {t : JasminTy} (e : Expr jasminDialect Γ t) :
    rangeRule A e = e ∨
      ∀ V₁ V₂, Expr.ctLeak L (rangeRule A e) V₁ = Expr.ctLeak L (rangeRule A e) V₂ := by
  rcases e with ⟨op, rfl, args⟩
  unfold rangeRule
  split
  · rename_i e' he
    obtain ⟨bop, w, hop, -⟩ := ruleOp_op A op args he
    exact Or.inr fun V₁ V₂ => by
      show Expr.ctLeak L e' V₁ = Expr.ctLeak L e' V₂
      rw [expr_ctLeak_regArith L hq e' hop, expr_ctLeak_regArith L hq e' hop]
  · exact Or.inl rfl

theorem rangeExpr_leak (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (A : AEnv Γ)
    (len : Nat) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    rangeExpr A len e = e ∨
      ∀ V₁ V₂, Expr.ctLeak L (rangeExpr A len e) V₁ = Expr.ctLeak L (rangeExpr A len e) V₂ := by
  unfold rangeExpr
  split
  · exact Or.inl rfl
  split
  · rename_i e' he
    cases t with
    | reg w =>
      simp only [pointExpr, Option.map_eq_some_iff] at he
      obtain ⟨n, -, rfl⟩ := he
      exact Or.inr fun _ _ => rfl
    | _ => simp [pointExpr] at he
  · exact rangeRule_leak hq A e

/-- **Leakage of the range traversal.** Under environments that hold of `V₁` and `V₂`, equal
    leakage of the input there gives equal leakage of the output. -/
theorem rangeCom_ctLeak (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) :
    ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ) (len : Nat) (c : Com jasminDialect Γ t)
      (V₁ V₂ : Ctxt.Valuation Γ), len = Γ.length → EnvOK A V₁ → EnvOK A V₂ →
      Com.ctLeak L c V₁ = Com.ctLeak L c V₂ →
      Com.ctLeak L (rangeCom A len c) V₁ = Com.ctLeak L (rangeCom A len c) V₂
  | _, _, _, _, .ret _, _, _, _, _, _, _ => rfl
  | _, _, A, len, .var e body, V₁, V₂, hlen, h₁, h₂, h => by
    simp only [Com.ctLeak] at h
    obtain ⟨hE, hB⟩ := List.append_inj h (opLeak_length L e.op _ _)
    simp only [rangeCom, Com.ctLeak]
    rw [rangeExpr_denote h₁ hlen e, rangeExpr_denote h₂ hlen e]
    congr 1
    · rcases rangeExpr_leak hq A len e with h' | h'
      · rw [h']; exact hE
      · exact h' _ _
    · exact rangeCom_ctLeak hq _ (len + 1) body _ _ (by simp [hlen])
        (h₁.cons (stageAbs_sound h₁ hlen e)) (h₂.cons (stageAbs_sound h₂ hlen e)) hB

/-- **Leakage of the range stage.** Under a leakage model whose `regArith` operations are
    quiet, equal leakage of `c` at two valuations gives equal leakage of `comRangeOpt c`
    there. A comparison, carry-out or select that the stage folds may leak under such a
    model; its replacement, a `regConst` or `regArith` binding, emits the same events at
    both valuations. -/
theorem comRangeOpt_ctLeak_eq (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {t : JasminTy} (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (comRangeOpt c) V₁ = Com.ctLeak L (comRangeOpt c) V₂ :=
  rangeCom_ctLeak hq _ _ c V₁ V₂ rfl (envOK_topEnv V₁) (envOK_topEnv V₂) h

/-- **Constant time of the range stage.** Under a leakage model whose `regArith` operations
    are quiet, if `c` is constant time for the relation `R`, so is `comRangeOpt c`. -/
theorem comRangeOpt_constantTime (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet)
    {t : JasminTy} (c : Com jasminDialect Γ t)
    (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (comRangeOpt c)) :=
  fun V₁ V₂ hR => comRangeOpt_ctLeak_eq hq c V₁ V₂ (h V₁ V₂ hR)

end Leak

end Range

/-! ## §5a  The `Com` optimisation stage

The stage runs the range stage `comRangeOpt`, then the acyclic e-graph pass
`Aegraph.aegraphOpt`. The rule set of the e-graph pass contains the identities of the
saturation engine (with the constant tested as a value, at every width) and of the peephole,
and its node table performs global value numbering over every form of each e-class. The
range stage runs first because its output is input to the e-graph rules: the constants it
binds feed their constant folding and identities, its copies `x ||| x` are collapsed by the
rule for `bop a a`, and duplicate constants are merged by value numbering. Neither pass needs
a hypothesis on the valuation. -/

/-- **The `Com` optimisation stage**: the range stage, then the acyclic e-graph pass. -/
def optCom {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  Aegraph.aegraphOpt (comRangeOpt c)

/-- **Denotation of the stage.** `optCom c` denotes the same function as `c`, at every
    valuation. -/
theorem optCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : (optCom c).denote = c.denote := by
  rw [optCom, Aegraph.aegraphOpt_denote, comRangeOpt_denote]

/-- The stage does not increase `comCost`. -/
theorem optCom_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : comCost (optCom c) ≤ comCost c :=
  Nat.le_trans (Aegraph.aegraphOpt_cost_le _) (comRangeOpt_cost_le c)

/-! ## §5b  Leakage of the stage

The peephole and the saturation engine replace a binary `regArith` binding by another binary
`regArith` binding over the same width and leave every other binding unchanged. Under a
leakage model whose `regArith` operations emit no event, both passes keep the leakage of a
program at every valuation. Without that hypothesis the statement fails: a model for which
`add` is quiet and `or` is not distinguishes `x + 0` from its rewrite `x ||| x`. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)

/-- A result of `binE` is a `regArith` expression. -/
theorem binE_op {Γ : Ctxt jasminDialect} {w : Nat} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg w)) : (binE op a b).op = .regArith op w := rfl

/-- Leakage of one rewritten expression of the saturation engine. -/
theorem rewriteExpr_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ) :
    Expr.ctLeak L (rewriteExpr e k) V = Expr.ctLeak L e V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [rewriteExpr, HVector.head, HVector.tail]
      rw [expr_ctLeak_regArith L hq ⟨.regArith bop w, rfl, .cons a (.cons b .nil)⟩ rfl V]
      rcases hr : rewriteBin bop a b (KEnv.lookup b k) with _ | e'
      · exact expr_ctLeak_regArith L hq _ rfl V
      · have hop' : ∃ bop', e'.op = .regArith bop' w := by
          unfold rewriteBin at hr
          split at hr <;> first | (cases hr; exact ⟨_, binE_op _ _ _⟩) | cases hr
        obtain ⟨bop', hop'⟩ := hop'
        exact expr_ctLeak_regArith L hq e' hop' V
  all_goals rfl

/-- Leakage of one pass of the saturation engine, from an environment consistent with the
    valuation. -/
theorem rewriteCom_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ),
      KEnv.Consistent k V → Com.ctLeak L (rewriteCom c k) V = Com.ctLeak L c V
  | .ret _, _, _, _ => rfl
  | .var e body, k, V, hk => by
      simp only [rewriteCom, Com.ctLeak]
      rw [rewriteExpr_ctLeak L hq e k V, rewriteExpr_denote e k V hk,
        rewriteCom_ctLeak L hq body (extendK e k) (V.extend (e.denote V))
          (extendK_consistent e k V hk)]

/-- Leakage of the bounded saturation engine, from an environment consistent with the
    valuation. -/
theorem saturateCom_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} :
    ∀ (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ),
      KEnv.Consistent k V → Com.ctLeak L (saturateCom fuel c k) V = Com.ctLeak L c V
  | 0, _, _, _, _ => rfl
  | fuel + 1, c, k, V, hk => by
      simp only [saturateCom]
      rw [saturateCom_ctLeak L hq fuel (rewriteCom c k) k V hk, rewriteCom_ctLeak L hq c k V hk]

/-- **Leakage of the composed transform.** Under a leakage model whose `regArith`
    operations are quiet, `comAlgebraicPipeline fuel c k` has the leakage of `c` at every
    valuation consistent with `k`. -/
theorem comAlgebraicPipeline_ctLeak (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    Com.ctLeak L (comAlgebraicPipeline fuel c k) V = Com.ctLeak L c V := by
  unfold comAlgebraicPipeline
  rw [saturateCom_ctLeak L hq fuel (peepCom c) k V hk, peepCom_ctLeak L hq c V]

/-- **Leakage of the stage.** Under a leakage model whose `regArith` operations are quiet,
    equal leakage of `c` at two valuations gives equal leakage of `optCom c` there. -/
theorem optCom_ctLeak_eq (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (optCom c) V₁ = Com.ctLeak L (optCom c) V₂ :=
  Aegraph.aegraphOpt_ctLeak_eq hq _ V₁ V₂ (comRangeOpt_ctLeak_eq hq c V₁ V₂ h)

/-- **Constant time of the stage.** Under a leakage model whose `regArith` operations are
    quiet, if `c` is constant time for the relation `R`, so is `optCom c`. -/
theorem optCom_constantTime (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (optCom c)) :=
  Aegraph.aegraphOpt_constantTime hq _ R (comRangeOpt_constantTime hq c R h)

end Leak

/-! ## §6  Self-contained validation

`Egraph.demoMulZero` is `x ↦ x * 0` via an explicit `regConst 0` binder.
The composed pipeline (peephole then saturation) preserves its denotation
(both map `x` to `0`) and is cost-non-increasing.  The peephole half does
not fire on this kernel (no `sub a a` / `and a a`), and the saturation
half collapses the `mul`-by-zero to `b &&& b`; the composition therefore
realises the same denotation-preserving rewrite as the saturation engine
alone, through the canonical two-pass entry point. -/

/-- The composed pipeline (fuel 4) preserves the demo's denotation. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoMulZero demoK).denote V = demoMulZero.denote V :=
  comAlgebraicPipeline_denote 4 demoMulZero demoK V (demoK_consistent V)

/-- The composed pipeline is cost-non-increasing on the demo. -/
example : comCost (comAlgebraicPipeline 4 demoMulZero demoK) ≤ comCost demoMulZero :=
  comAlgebraicPipeline_cost_le 4 demoMulZero demoK

/-- The composed pipeline on the peephole demo (`x ↦ x - x`): the peephole
    half fires (`sub x x ↦ xor x x`), the saturation half leaves it
    (no known constant), and denotation is preserved (both map `x` to `0`). -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoSelfSub demoK).denote V = demoSelfSub.denote V :=
  comAlgebraicPipeline_denote 4 demoSelfSub demoK V (demoK_consistent V)

end CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
