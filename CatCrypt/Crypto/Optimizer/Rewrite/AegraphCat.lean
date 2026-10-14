/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
public import CatCrypt.Crypto.Optimizer.Rewrite.TraitRules
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptOpInfo

/-!
# The acyclic e-graph over `Com catCryptDialect`

The instance of the acyclic e-graph `AegraphGeneric.aegraphOptOf` at `catCryptDialect`. The
rule set `catRules` holds bit-vector identities valid for every width `w` and every operand,
each proved against the denotation `catCryptDenote`:

* `xorRule`: `x ^ 0 = x`, `0 ^ x = x`, `x ^ x = 0` (`xorAlts_sound`);
* `andRule`: `x & 0 = 0`, `0 & x = 0`, `x & x = x`, `x & ~0 = x`, `~0 & x = x`
  (`andAlts_sound`);
* `orRule`: `x | 0 = x`, `0 | x = x`, `x | x = x`, `x | ~0 = ~0`, `~0 | x = ~0`
  (`orAlts_sound`);
* `addRule`: `x + 0 = x`, `0 + x = x` (`addAlts_sound`);
* `subRule`: `x - 0 = x`, `x - x = 0` (`subAlts_sound`);
* `mulRule`: `x * 1 = x`, `1 * x = x`, `x * 0 = 0`, `0 * x = 0` (`mulAlts_sound`);
* `shiftZeroRule`: a shift or rotation by the constant amount zero is the identity
  (`bvShiftL`, `bvShiftR`, `bvShiftRA`, `bvRol`, `bvRor`; `zeroAmtAlts_sound`);
* `notRule`: `~~x = x` and `!!b = b`, the involution rule `TraitRules.involutionRule` at
  `catInvolution`;
* `idempotentRule catIdempotent`: `b && b = b`, `b || b = b` on bits;
* `selfCancelRule catSelfCancel`: `b ^^ b = false`, `eqBit b b = true`, `bvEq x x = true`;
* `constFoldRule catReify`: a pure operation on constant arguments is replaced by the
  constant `bvConst`, `constBit` or `constUnit` holding its value.

A constant operand is read from the definition table (`constOf`, a binding of `bvConst`).
The node table merges every operation other than the sampling leaves `sampleBit`, `sampleBv` and the external call `extCall`.

## Main results

* `aegraphOptCat`, `aegraphOptCat_denote`: the pass denotes the same function as its input.
* `aegraphOptCat_cost_le`: the pass does not increase `comCostOf catCost`.
* `catRules_indep`, `aegraphOptCat_constantTime`: the rules emit existing variables and the
  nullary constant `bvConst w 0`, so the pass preserves constant time under every leakage
  model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-! ## 1. Reading the definition table -/

/-- The value of a variable of type `sword w`. -/
abbrev val {Δ : Ctxt catCryptDialect} {w : Nat} (V : Ctxt.Valuation Δ)
    (a : Ctxt.Var Δ (.sword w)) : BitVec w :=
  a.lookup V

/-- The expression `bvConst w c`. -/
def constE {Δ : Ctxt catCryptDialect} (w : Nat) (c : BitVec w) :
    Expr catCryptDialect Δ (.sword w) :=
  { op := .bvConst w c, retTy_eq := rfl, args := .nil }

theorem constE_denote {Δ : Ctxt catCryptDialect} (w : Nat) (c : BitVec w)
    (V : Ctxt.Valuation Δ) : (constE w c).denote V = c := rfl

/-- The constant a variable of type `sword w` holds, read from the definition table. -/
def constOf {Δ : Ctxt catCryptDialect} {w : Nat} (D : Defs catCryptDialect)
    (a : Ctxt.Var Δ (.sword w)) : Option (BitVec w) :=
  match D[varLvl a]? with
  | some (.bvConst w' c, []) => if h : w' = w then some (h ▸ c) else none
  | _ => none

theorem constOf_sound {Δ : Ctxt catCryptDialect} {w : Nat} {D : Defs catCryptDialect}
    {V : Ctxt.Valuation Δ} (hD : DSound V D) {a : Ctxt.Var Δ (.sword w)} {c : BitVec w}
    (h : constOf D a = some c) : val V a = c := by
  unfold constOf at h
  split at h
  · rename_i w' c' hl
    split at h
    · rename_i hw
      subst hw
      cases h
      obtain ⟨x, h1, h2⟩ := hD _ _ hl
      rw [getLvl_var] at h2
      have h1' : evalKey V (CatCryptOp.bvConst w' c') [] = some ⟨.sword w', c'⟩ := rfl
      rw [h1'] at h1
      rw [← h1] at h2
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h2)).2
    · cases h
  · cases h

/-! ## 2. The bit-vector identities -/

section Identities

variable {Δ : Ctxt catCryptDialect} {w : Nat}

/-- `x ^ 0 = x`, `0 ^ x = x` and `x ^ x = 0`. -/
def xorAlts (D : Defs catCryptDialect) (a b : Ctxt.Var Δ (.sword w)) :
    List (Alt Δ (.sword w)) :=
  (if constOf D b = some 0 then [.var a] else []) ++
    (if constOf D a = some 0 then [.var b] else []) ++
    (if varEq a b then [.one (constE w 0)] else [])

theorem xorAlts_sound {D : Defs catCryptDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ xorAlts D a b, alt.denote V = val V a ^^^ val V b := by
  intro alt h
  simp only [xorAlts, List.mem_append] at h
  rcases h with (h | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]
  · rename_i hab
    rw [varEq_sound a b hab, BitVec.xor_self]
    rfl

/-- `x & 0 = 0`, `0 & x = 0`, `x & x = x`, `x & ~0 = x` and `~0 & x = x`; the zero is the
    operand that holds it. -/
def andAlts (D : Defs catCryptDialect) (a b : Ctxt.Var Δ (.sword w)) :
    List (Alt Δ (.sword w)) :=
  (if constOf D b = some 0 then [.var b] else []) ++
    (if constOf D a = some 0 then [.var a] else []) ++
    (if varEq a b then [.var a] else []) ++
    (if constOf D b = some (BitVec.allOnes w) then [.var a] else []) ++
    (if constOf D a = some (BitVec.allOnes w) then [.var b] else [])

theorem andAlts_sound {D : Defs catCryptDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ andAlts D a b, alt.denote V = val V a &&& val V b := by
  intro alt h
  simp only [andAlts, List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]
  · rename_i hab
    rw [varEq_sound a b hab]
    simp [Alt.denote]
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]

/-- `x | 0 = x`, `0 | x = x`, `x | x = x`, `x | ~0 = ~0` and `~0 | x = ~0`; the all-ones
    value is the operand that holds it. -/
def orAlts (D : Defs catCryptDialect) (a b : Ctxt.Var Δ (.sword w)) :
    List (Alt Δ (.sword w)) :=
  (if constOf D b = some 0 then [.var a] else []) ++
    (if constOf D a = some 0 then [.var b] else []) ++
    (if varEq a b then [.var a] else []) ++
    (if constOf D b = some (BitVec.allOnes w) then [.var b] else []) ++
    (if constOf D a = some (BitVec.allOnes w) then [.var a] else [])

theorem orAlts_sound {D : Defs catCryptDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ orAlts D a b, alt.denote V = val V a ||| val V b := by
  intro alt h
  simp only [orAlts, List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]
  · rename_i hab
    rw [varEq_sound a b hab]
    simp [Alt.denote]
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]

/-- `x + 0 = x` and `0 + x = x`. -/
def addAlts (D : Defs catCryptDialect) (a b : Ctxt.Var Δ (.sword w)) :
    List (Alt Δ (.sword w)) :=
  (if constOf D b = some 0 then [.var a] else []) ++
    (if constOf D a = some 0 then [.var b] else [])

theorem addAlts_sound {D : Defs catCryptDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ addAlts D a b, alt.denote V = val V a + val V b := by
  intro alt h
  simp only [addAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]

/-- `x - 0 = x` and `x - x = 0`. -/
def subAlts (D : Defs catCryptDialect) (a b : Ctxt.Var Δ (.sword w)) :
    List (Alt Δ (.sword w)) :=
  (if constOf D b = some 0 then [.var a] else []) ++
    (if varEq a b then [.one (constE w 0)] else [])

theorem subAlts_sound {D : Defs catCryptDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ subAlts D a b, alt.denote V = val V a - val V b := by
  intro alt h
  simp only [subAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i hab
    rw [varEq_sound a b hab, BitVec.sub_self]
    rfl

/-- `x * 1 = x`, `1 * x = x`, `x * 0 = 0` and `0 * x = 0`; the zero is the operand that
    holds it. -/
def mulAlts (D : Defs catCryptDialect) (a b : Ctxt.Var Δ (.sword w)) :
    List (Alt Δ (.sword w)) :=
  (if constOf D b = some 1 then [.var a] else []) ++
    (if constOf D a = some 1 then [.var b] else []) ++
    (if constOf D b = some 0 then [.var b] else []) ++
    (if constOf D a = some 0 then [.var a] else [])

theorem mulAlts_sound {D : Defs catCryptDialect} {V : Ctxt.Valuation Δ} (hD : DSound V D)
    (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ mulAlts D a b, alt.denote V = val V a * val V b := by
  intro alt h
  simp only [mulAlts, List.mem_append] at h
  rcases h with ((h | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]
  · rename_i hb
    simp [Alt.denote, constOf_sound hD hb]
  · rename_i ha
    simp [Alt.denote, constOf_sound hD ha]

theorem rotateLeft_zero' (x : BitVec w) : x.rotateLeft 0 = x := by
  ext i
  simp [BitVec.getElem_rotateLeft]

theorem rotateRight_zero' (x : BitVec w) : x.rotateRight 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateRight, hi]

/-- A unary operation `f · k` with the constant amount `k`, whose amount zero is the
    identity: the operand itself when `k = 0`. -/
def zeroAmtAlts (k : Nat) (a : Ctxt.Var Δ (.sword w)) : List (Alt Δ (.sword w)) :=
  if k = 0 then [.var a] else []

theorem zeroAmtAlts_sound (f : BitVec w → Nat → BitVec w) (hf : ∀ x, f x 0 = x)
    (V : Ctxt.Valuation Δ) (k : Nat) (a : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ zeroAmtAlts k a, alt.denote V = f (val V a) k := by
  intro alt h
  unfold zeroAmtAlts at h
  split at h
  · rename_i hk
    subst hk
    simp only [List.mem_singleton] at h
    subst h
    exact (hf _).symm
  · simp at h

end Identities

/-! ## 3. The rules -/

/-- The alternatives of `xorAlts` on a bit-vector exclusive or. -/
def xorApply (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    (e : Expr catCryptDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.bvXor w, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      let b : Ctxt.Var Δ (.sword w) := args.tail.head
      hop ▸ xorAlts D a b
  | _ => []

/-- The alternatives of `andAlts` on a bit-vector conjunction. -/
def andApply (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    (e : Expr catCryptDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.bvAnd w, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      let b : Ctxt.Var Δ (.sword w) := args.tail.head
      hop ▸ andAlts D a b
  | _ => []

/-- The alternatives of `orAlts` on a bit-vector disjunction. -/
def orApply (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    (e : Expr catCryptDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.bvOr w, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      let b : Ctxt.Var Δ (.sword w) := args.tail.head
      hop ▸ orAlts D a b
  | _ => []

/-- The alternatives of `addAlts` on a bit-vector addition. -/
def addApply (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    (e : Expr catCryptDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.bvAdd w, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      let b : Ctxt.Var Δ (.sword w) := args.tail.head
      hop ▸ addAlts D a b
  | _ => []

/-- The alternatives of `subAlts` on a bit-vector subtraction. -/
def subApply (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    (e : Expr catCryptDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.bvSub w, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      let b : Ctxt.Var Δ (.sword w) := args.tail.head
      hop ▸ subAlts D a b
  | _ => []

/-- The alternatives of `mulAlts` on a bit-vector multiplication. -/
def mulApply (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    (e : Expr catCryptDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.bvMul w, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      let b : Ctxt.Var Δ (.sword w) := args.tail.head
      hop ▸ mulAlts D a b
  | _ => []

/-- The alternatives of `zeroAmtAlts` on a shift or rotation by a constant amount. -/
def shiftZeroApply {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    (e : Expr catCryptDialect Δ s) : List (Alt Δ s) :=
  match e with
  | ⟨.bvShiftL w k, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      hop ▸ zeroAmtAlts k a
  | ⟨.bvShiftR w k, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      hop ▸ zeroAmtAlts k a
  | ⟨.bvShiftRA w k, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      hop ▸ zeroAmtAlts k a
  | ⟨.bvRol w k, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      hop ▸ zeroAmtAlts k a
  | ⟨.bvRor w k, hop, args⟩ =>
      let a : Ctxt.Var Δ (.sword w) := args.head
      hop ▸ zeroAmtAlts k a
  | _ => []

theorem xorApply_sound (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ xorApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case bvXor w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [xorApply, HVector.head, HVector.tail] at halt
      exact xorAlts_sound hD a b alt halt
  all_goals intro alt h; simp [xorApply] at h

theorem andApply_sound (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ andApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case bvAnd w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [andApply, HVector.head, HVector.tail] at halt
      exact andAlts_sound hD a b alt halt
  all_goals intro alt h; simp [andApply] at h

theorem orApply_sound (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ orApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case bvOr w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [orApply, HVector.head, HVector.tail] at halt
      exact orAlts_sound hD a b alt halt
  all_goals intro alt h; simp [orApply] at h

theorem addApply_sound (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ addApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case bvAdd w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [addApply, HVector.head, HVector.tail] at halt
      exact addAlts_sound hD a b alt halt
  all_goals intro alt h; simp [addApply] at h

theorem subApply_sound (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ subApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case bvSub w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [subApply, HVector.head, HVector.tail] at halt
      exact subAlts_sound hD a b alt halt
  all_goals intro alt h; simp [subApply] at h

theorem mulApply_sound (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect}
    (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ mulApply D e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case bvMul w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [mulApply, HVector.head, HVector.tail] at halt
      exact mulAlts_sound hD a b alt halt
  all_goals intro alt h; simp [mulApply] at h

theorem shiftZeroApply_sound {Δ : Ctxt catCryptDialect} (V : Ctxt.Valuation Δ)
    {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ shiftZeroApply e, alt.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case bvShiftL w k =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a .nil, _ =>
      intro alt halt
      simp only [shiftZeroApply, HVector.head] at halt
      exact zeroAmtAlts_sound (fun x n => x <<< shiftMask w n)
        (fun x => by simp only [shiftMask_zero, BitVec.shiftLeft_zero]) V k a alt halt
  case bvShiftR w k =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a .nil, _ =>
      intro alt halt
      simp only [shiftZeroApply, HVector.head] at halt
      exact zeroAmtAlts_sound (fun x n => BitVec.ushiftRight x (shiftMask w n))
        (fun x => by rw [shiftMask_zero]; exact BitVec.ushiftRight_zero x) V k a alt halt
  case bvShiftRA w k =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a .nil, _ =>
      intro alt halt
      simp only [shiftZeroApply, HVector.head] at halt
      exact zeroAmtAlts_sound (fun x n => BitVec.sshiftRight x n)
        (fun _ => BitVec.sshiftRight_zero)
        V k a alt halt
  case bvRol w k =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a .nil, _ =>
      intro alt halt
      simp only [shiftZeroApply, HVector.head] at halt
      exact zeroAmtAlts_sound (fun x n => x.rotateLeft n) rotateLeft_zero'
        V k a alt halt
  case bvRor w k =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a .nil, _ =>
      intro alt halt
      simp only [shiftZeroApply, HVector.head] at halt
      exact zeroAmtAlts_sound (fun x n => x.rotateRight n) rotateRight_zero'
        V k a alt halt
  all_goals intro alt h; simp [shiftZeroApply] at h

/-- Exclusive or: `x ^ 0 = x`, `0 ^ x = x`, `x ^ x = 0`. -/
def xorRule : Rule catCryptDialect where
  apply D _ _ e := xorApply D e
  sound D _ V hD _ e := xorApply_sound D V hD e

/-- Conjunction: `x & 0 = 0`, `0 & x = 0`, `x & x = x`, `x & ~0 = x`, `~0 & x = x`. -/
def andRule : Rule catCryptDialect where
  apply D _ _ e := andApply D e
  sound D _ V hD _ e := andApply_sound D V hD e

/-- Disjunction: `x | 0 = x`, `0 | x = x`, `x | x = x`, `x | ~0 = ~0`, `~0 | x = ~0`. -/
def orRule : Rule catCryptDialect where
  apply D _ _ e := orApply D e
  sound D _ V hD _ e := orApply_sound D V hD e

/-- The additive identity: `x + 0 = x`, `0 + x = x`. -/
def addRule : Rule catCryptDialect where
  apply D _ _ e := addApply D e
  sound D _ V hD _ e := addApply_sound D V hD e

/-- Subtraction: `x - 0 = x`, `x - x = 0`. -/
def subRule : Rule catCryptDialect where
  apply D _ _ e := subApply D e
  sound D _ V hD _ e := subApply_sound D V hD e

/-- The multiplicative identity and annihilator: `x * 1 = x`, `1 * x = x`, `x * 0 = 0`,
    `0 * x = 0`. -/
def mulRule : Rule catCryptDialect where
  apply D _ _ e := mulApply D e
  sound D _ V hD _ e := mulApply_sound D V hD e

/-- A shift or rotation by the constant amount zero is the identity. -/
def shiftZeroRule : Rule catCryptDialect where
  apply _ _ _ e := shiftZeroApply e
  sound _ _ V _ _ e := shiftZeroApply_sound V e

/-! ## 3a. Instances of the trait rules -/

open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules

/-- The involutions of catCrypt: the bit-vector complement `bvNot w` and the bit negation
    `not`. -/
def catInvolution : Involution catCryptDialect where
  isInv
    | .bvNot _ | .not => true
    | _ => false
  ty
    | .bvNot w => .sword w
    | _ => .bit
  sig_eq op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  ret_eq op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  law op h x := by
    cases op <;> first
      | exact absurd h Bool.false_ne_true
      | exact Bool.not_not x
      | exact BitVec.not_not (b := (x : BitVec _))

/-- The idempotent catCrypt operations not covered by `andRule` and `orRule`: the bit
    conjunction `and` and disjunction `or`. -/
def catIdempotent : Idempotent catCryptDialect where
  isIdem
    | .and | .or => true
    | _ => false
  ty _ := .bit
  sig_eq op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  ret_eq op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  law op h x := by
    cases op <;> first
      | exact Bool.and_self x
      | exact Bool.or_self x
      | exact absurd h Bool.false_ne_true

/-- The self-cancelling catCrypt operations not covered by `xorRule` and `subRule`: the bit
    exclusive or (`b ^^ b = false`), the bit equality and the bit-vector equality
    (`x = x` is `true`). -/
def catSelfCancel : SelfCancel catCryptDialect where
  isCancel
    | .xor | .eqBit | .bvEq _ => true
    | _ => false
  ty
    | .bvEq w => .sword w
    | _ => .bit
  sig_eq op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  zero
    | .xor => .constBit false
    | _ => .constBit true
  zero_sig op _ := by cases op <;> rfl
  zero_ret op h := by cases op <;> first | rfl | exact absurd h Bool.false_ne_true
  law op h x := by
    cases op <;> first
      | exact absurd h Bool.false_ne_true
      | exact Sigma.ext rfl (heq_of_eq (by simp [app2, app0, DialectDenote.denote,
          HVector.head, HVector.tail]))

/-- The constant operation holding a catCrypt value: `bvConst` for a word, `constBit` for a
    bit, `constUnit` for the unit. -/
def catReifyOp : (t : CryptoTy) → ⟦t⟧ → Option CatCryptOp
  | .sword w, x => some (.bvConst w x)
  | .bit, b => some (.constBit b)
  | .unit, _ => some .constUnit
  | _, _ => none

/-- The reification of catCrypt values as constants, under `catTraits`. -/
def catReify : ConstReify catCryptDialect catTraits where
  reify := catReifyOp
  law := catTraits_constLaw
  const t x op h := by
    cases t <;> simp only [catReifyOp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      rfl
  ret_eq t x op h := by
    cases t <;> simp only [catReifyOp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      rfl
  denote_eq t x op h := by
    cases t <;> simp only [catReifyOp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      rfl

/-- Double complement: `~~x = x` and `!!b = b`, the involution rule at `catInvolution`. -/
def notRule : Rule catCryptDialect := involutionRule catInvolution

/-! ## 4. The catCrypt rule set and the pass

The cost `catCost` and the merge predicate `catPure` are defined in
`VIR/CatCryptOpInfo.lean`, as fields of `catTraits`. -/

/-- The extraction weight of a catCrypt operation: twice its cost, plus one unless it is a
    constant. -/
def catKey (op : CatCryptOp) : Nat :=
  2 * catCost op + (match op with | .bvConst _ _ | .constBit _ | .constUnit => 0 | _ => 1)

/-- The extraction weight `catKey` is the weight `OpTraits.key` derived from
    `catTraits`. -/
theorem catKey_eq : catKey = catTraits.key := by
  funext op
  cases op <;> rfl

/-- The catCrypt rule set: the eight rule families above, for every width, and the trait
    rules at `catIdempotent`, `catSelfCancel` and `catReify`, over the operation traits
    `catTraits`. -/
def catRules : RuleSet catCryptDialect where
  toOpTraits := catTraits
  rules := [xorRule, andRule, orRule, addRule, subRule, mulRule, shiftZeroRule, notRule,
    idempotentRule catIdempotent, selfCancelRule catSelfCancel,
    constFoldRule catReify (fun _ => true)]

/-- **The aegraph pass on catCrypt programs**: the instance of `aegraphOptOf` at
    `catRules`. -/
def aegraphOptCat {Γ : Ctxt catCryptDialect} {t : CryptoTy} (c : Com catCryptDialect Γ t) :
    Com catCryptDialect Γ t :=
  aegraphOptOf catRules c

/-- **Denotation of the catCrypt pass.** `aegraphOptCat c` denotes the same function as
    `c`. -/
theorem aegraphOptCat_denote {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) : (aegraphOptCat c).denote = c.denote :=
  aegraphOptOf_denote catRules c

/-- The catCrypt pass does not increase `comCostOf catCost`. -/
theorem aegraphOptCat_cost_le {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) :
    comCostOf catCost (aegraphOptCat c) ≤ comCostOf catCost c :=
  aegraphOptOf_cost_le catRules c

/-! ## 5. Constant time

The catCrypt rules emit existing variables and the nullary constant `bvConst w 0`, whose
events do not depend on the valuation, so the pass preserves constant time under every
leakage model. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)

variable {L : LeakModel catCryptDialect}

section Alts

variable {Δ : Ctxt catCryptDialect} {w : Nat} (D : Defs catCryptDialect)

theorem xorAlts_indep (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ xorAlts D a b, alt.Indep L := by
  intro alt h
  simp only [xorAlts, List.mem_append] at h
  rcases h with (h | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · trivial
  · trivial
  · exact fun _ _ => rfl

theorem andAlts_indep (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ andAlts D a b, alt.Indep L := by
  intro alt h
  simp only [andAlts, List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial

theorem orAlts_indep (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ orAlts D a b, alt.Indep L := by
  intro alt h
  simp only [orAlts, List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial

theorem addAlts_indep (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ addAlts D a b, alt.Indep L := by
  intro alt h
  simp only [addAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial

theorem subAlts_indep (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ subAlts D a b, alt.Indep L := by
  intro alt h
  simp only [subAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h
  · trivial
  · exact fun _ _ => rfl

theorem mulAlts_indep (a b : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ mulAlts D a b, alt.Indep L := by
  intro alt h
  simp only [mulAlts, List.mem_append] at h
  rcases h with ((h | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> trivial

theorem zeroAmtAlts_indep (k : Nat) (a : Ctxt.Var Δ (.sword w)) :
    ∀ alt ∈ zeroAmtAlts k a, alt.Indep L := by
  intro alt h
  unfold zeroAmtAlts at h
  split at h
  · simp only [List.mem_singleton] at h
    subst h
    trivial
  · simp at h

end Alts

/-- The events of every alternative of the catCrypt rule set do not depend on the
    valuation, for every leakage model. -/
theorem catRules_indep : RulesIndep L catRules := by
  refine rulesIndep_of_forall fun r hr => ?_
  simp only [catRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_left 7
  · exact involutionRule_indep L catInvolution
  · exact idempotentRule_indep L catIdempotent
  · exact selfCancelRule_indep L catSelfCancel
  · exact constFoldRule_indep L catReify _
  all_goals intro D Δ s e alt ha
  all_goals rcases e with ⟨op, hop, args⟩
  all_goals cases op <;>
    simp only [xorRule, andRule, orRule, addRule, subRule, mulRule, shiftZeroRule,
      xorApply, andApply, orApply, addApply, subApply, mulApply, shiftZeroApply,
      List.not_mem_nil] at ha <;> subst hop
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact xorAlts_indep D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact andAlts_indep D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact orAlts_indep D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact addAlts_indep D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact subAlts_indep D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact mulAlts_indep D a b alt ha
  all_goals
    match args, (rfl : args = args) with
    | .cons a .nil, _ =>
      simp only [HVector.head] at ha
      exact zeroAmtAlts_indep _ a alt ha

/-- **Constant time of the catCrypt pass.** For every leakage model, if `c` is constant
    time for the relation `R`, so is `aegraphOptCat c`. -/
theorem aegraphOptCat_constantTime {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) :
    ConstantTime R (Com.ctLeak L (aegraphOptCat c)) :=
  aegraphOptOf_constantTime catRules catRules_indep c R h

end Leak

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat
