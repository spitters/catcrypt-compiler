/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The extension-tower dialect and its lowering to `fieldDialect`

`towerDialect` is the dialect of the pairing extension tower
`Fp2 = Fp[u]/(u² − β)`, `Fp6 = Fp2[v]/(v³ − ξ)` with `ξ = ξ₀ + u`, and
`Fp12 = Fp6[w]/(w² − v)`, with the non-residues `β` and `ξ₀` carried in the types.
Its types denote the carriers `Fp2Val`, `Fp6Val`, `Fp12Val` of `FieldDialect`, and its
multiplications denote `Fp2Val.mulBeta β`, `Fp6Val.mulBeta β ξ₀` and
`Fp12Val.mulBeta β ξ₀`. The types `word` and `bit` give the `HasWord64` and
`HasBoolBit` instances that `NFProg` needs.

`towerToField` is a multi-value block lowering to `fieldDialect`: an `Fp2` value is
represented by its two base coordinates, an `Fp6` value by six and an `Fp12` value by
twelve. Every block is a closed `MultiReturnCom fieldDialect` over the flattened
argument registers, generated from a straight-line program:

* `TExpr`, `emitT`, `emitVecT`: expressions over `ZMod p` with sums, differences,
  negations and products, compiled to `fAdd`, `fSub`, `fNeg`, `fMul` and `fConst`
  bindings; an input binds nothing.
* `I2`, `I2.emit`: the `Fp2` instructions, each two stages of expressions over the
  coordinates of its operands. The product is Karatsuba (three `fMul`), the square is
  the complex method (two `fMul`).
* `SLP`: straight-line programs over a register file, with `SLP.eval` and the emitter
  `SLP.emit`, generic in the register bundle and the instruction set.
  `SLP.emit_denote` reduces the correctness of every program to the soundness of its
  instructions (`EmitSound`).
* `I6`, `I6.emit`: the `Fp6` instructions, each an `Fp2` program (`mul6P`: six `Fp2`
  products and two non-residue products; `sq6P`: the Chung–Hasan squaring).
* The `Fp12` multiply (`mul12P`, Karatsuba over `Fp6`, three `Fp6` products) and
  square (`sq12P`, complex method) are `Fp6` programs; the sparse product with a line
  in the `0-1-4` pattern (`sparse014P`, thirteen `Fp2` products) is an `Fp2` program.

## Main definitions

* `TowerTy`, `TowerOp`, `towerDialect`: the dialect.
* `towerMapTys`, `towerEnc`, `towerToField`: the lowering and its encoding.

## Main results

* `SLP.emit_denote`: an emitted program computes `SLP.eval` under sound instructions.
* `I2.emit_sound`, `I6.emit_sound`: the `Fp2` and the `Fp6` instructions are sound.
* `blk2_denote`, `blk6_denote`: a block generated from an `Fp2` or an `Fp6` program
  returns the encoding of the program's value.
* `mul6P_eval`, `sq6P_eval`, `mul12P_eval`, `sq12P_eval`, `sparse014P_eval`: the
  programs compute `Fp6Val.mulBeta`, `Fp12Val.mulBeta` and the product with
  `line014`.
* `towerToField_blockSquare`: the block square of `towerToField` at every op.
* `towerToField_fundamental`: every program of the tower dialect lowers to a
  `fieldDialect` program that maps the flattened encoding of the inputs to the encoding
  of the value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

/-! ## 1. Carrier operations -/

section Carriers

variable {p : Nat}

/-- Negation of an `Fp6` value. -/
def neg6 (x : Fp6Val p) : Fp6Val p := ⟨-x.a0, -x.a1, -x.a2⟩

/-- Negation of an `Fp12` value. -/
def neg12 (x : Fp12Val p) : Fp12Val p := ⟨neg6 x.c0, neg6 x.c1⟩

/-- The zero `Fp6` value. -/
def zero6 : Fp6Val p := ⟨0, 0, 0⟩

/-- Multiplication of an `Fp12` value by `w`: `(a + b·w)·w = v·b + a·w`. -/
def mulW12 (β ξ0 : ZMod p) (x : Fp12Val p) : Fp12Val p :=
  ⟨Fp12Val.mulByVBeta β ξ0 x.c1, x.c0⟩

/-- The `Fp12` value of a line with coefficients `c0`, `c1`, `c4` in the `0-1-4`
    pattern: `(c0 + c1·v) + (c4·v)·w`. -/
def line014 (c0 c1 c4 : Fp2Val p) : Fp12Val p := ⟨⟨c0, c1, 0⟩, ⟨0, c4, 0⟩⟩

end Carriers

/-! ## 2. Types -/

/-- The value types of the tower dialect. The non-residues are part of the type:
    `fp2 p β` is `Fp[u]/(u² − β)`, `fp6 p β ξ` is `Fp2[v]/(v³ − (ξ + u))` and
    `fp12 p β ξ` is `Fp6[w]/(w² − v)`. -/
inductive TowerTy where
  /-- The prime field `F_p`. -/
  | fp (p : Nat)
  /-- The quadratic extension with `u² = β`. -/
  | fp2 (p : Nat) (β : Int)
  /-- The cubic extension with `v³ = ξ + u`. -/
  | fp6 (p : Nat) (β ξ : Int)
  /-- The quadratic extension of `fp6` with `w² = v`. -/
  | fp12 (p : Nat) (β ξ : Int)
  /-- A 64-bit word. -/
  | word
  /-- A bit. -/
  | bit
  deriving DecidableEq

/-- The denotation of the tower types: the carriers of `FieldDialect`, 64-bit words and
    booleans. -/
@[reducible] instance : TyDenote TowerTy where
  denote
    | .fp p => ZMod p
    | .fp2 p _ => Fp2Val p
    | .fp6 p _ _ => Fp6Val p
    | .fp12 p _ _ => Fp12Val p
    | .word => BitVec 64
    | .bit => Bool

/-- The three extension levels. -/
inductive Lvl where
  /-- `Fp2`. -/
  | two
  /-- `Fp6`. -/
  | six
  /-- `Fp12`. -/
  | twelve
  deriving DecidableEq

/-- The type of a level. -/
@[reducible] def Lvl.ty : Lvl → Nat → Int → Int → TowerTy
  | .two, p, β, _ => .fp2 p β
  | .six, p, β, ξ => .fp6 p β ξ
  | .twelve, p, β, ξ => .fp12 p β ξ

/-- The type of the level below. -/
@[reducible] def Lvl.base : Lvl → Nat → Int → Int → TowerTy
  | .two, p, _, _ => .fp p
  | .six, p, β, _ => .fp2 p β
  | .twelve, p, β, ξ => .fp6 p β ξ

/-! ## 3. Ops -/

/-- The ops of the tower dialect. The level ops carry the level, the prime and the
    non-residues. -/
inductive TowerOp where
  /-- Addition. -/
  | add (l : Lvl) (p : Nat) (β ξ : Int)
  /-- Subtraction. -/
  | sub (l : Lvl) (p : Nat) (β ξ : Int)
  /-- Negation. -/
  | neg (l : Lvl) (p : Nat) (β ξ : Int)
  /-- Multiplication. -/
  | mul (l : Lvl) (p : Nat) (β ξ : Int)
  /-- Squaring. -/
  | square (l : Lvl) (p : Nat) (β ξ : Int)
  /-- Multiplication by the generator of the next level: by `ξ + u` at `Fp2`, by `v` at
      `Fp6`, by `w` at `Fp12`. -/
  | mulByNonResidue (l : Lvl) (p : Nat) (β ξ : Int)
  /-- The `Fp2` Frobenius, the conjugation `a + b·u ↦ a − b·u`. -/
  | frobenius2 (p : Nat) (β : Int)
  /-- The product of an `Fp12` value with a line `(c0, c1, c4)` in the `0-1-4`
      pattern. -/
  | sparseMul (p : Nat) (β ξ : Int)
  /-- The embedding of the level below. -/
  | lift (l : Lvl) (p : Nat) (β ξ : Int)
  /-- Coordinate `i` of an `Fp2` value. -/
  | proj2 (p : Nat) (β : Int) (i : Fin 2)
  /-- Coordinate `i` of an `Fp6` value. -/
  | proj6 (p : Nat) (β ξ : Int) (i : Fin 3)
  /-- Coordinate `i` of an `Fp12` value. -/
  | proj12 (p : Nat) (β ξ : Int) (i : Fin 2)
  /-- A prime-field constant. -/
  | constFp (p : Nat) (c : ZMod p)
  deriving DecidableEq

/-- The tower dialect. -/
@[reducible] def towerDialect : Dialect := { Op := TowerOp, Ty := TowerTy }

instance : DialectSignature towerDialect where
  sig
    | .add l p β ξ | .sub l p β ξ | .mul l p β ξ => [l.ty p β ξ, l.ty p β ξ]
    | .neg l p β ξ | .square l p β ξ | .mulByNonResidue l p β ξ => [l.ty p β ξ]
    | .frobenius2 p β => [.fp2 p β]
    | .sparseMul p β ξ => [.fp12 p β ξ, .fp2 p β, .fp2 p β, .fp2 p β]
    | .lift l p β ξ => [l.base p β ξ]
    | .proj2 p β _ => [.fp2 p β]
    | .proj6 p β ξ _ => [.fp6 p β ξ]
    | .proj12 p β ξ _ => [.fp12 p β ξ]
    | .constFp _ _ => []
  ret
    | .add l p β ξ | .sub l p β ξ | .mul l p β ξ => l.ty p β ξ
    | .neg l p β ξ | .square l p β ξ | .mulByNonResidue l p β ξ => l.ty p β ξ
    | .frobenius2 p β => .fp2 p β
    | .sparseMul p β ξ => .fp12 p β ξ
    | .lift l p β ξ => l.ty p β ξ
    | .proj2 p _ _ => .fp p
    | .proj6 p β _ _ => .fp2 p β
    | .proj12 p β ξ _ => .fp6 p β ξ
    | .constFp p _ => .fp p

/-! ## 4. Denotation -/

section Denote

/-- Addition at a level. -/
def addL : (l : Lvl) → (p : Nat) → (β ξ : Int) →
    ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧
  | .two, p, _, _ => fun (x y : Fp2Val p) => x + y
  | .six, _, _, _ => Fp6Val.add
  | .twelve, _, _, _ => Fp12Val.add

/-- Subtraction at a level. -/
def subL : (l : Lvl) → (p : Nat) → (β ξ : Int) →
    ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧
  | .two, p, _, _ => fun (x y : Fp2Val p) => x - y
  | .six, _, _, _ => Fp6Val.sub
  | .twelve, _, _, _ => Fp12Val.sub

/-- Negation at a level. -/
def negL : (l : Lvl) → (p : Nat) → (β ξ : Int) → ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧
  | .two, p, _, _ => fun (x : Fp2Val p) => -x
  | .six, _, _, _ => neg6
  | .twelve, _, _, _ => neg12

/-- Multiplication at a level. -/
def mulL : (l : Lvl) → (p : Nat) → (β ξ : Int) →
    ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧
  | .two, p, β, _ => Fp2Val.mulBeta (β : ZMod p)
  | .six, p, β, ξ => Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p)
  | .twelve, p, β, ξ => Fp12Val.mulBeta (β : ZMod p) (ξ : ZMod p)

/-- Multiplication by the generator of the next level. -/
def mulNRL : (l : Lvl) → (p : Nat) → (β ξ : Int) → ⟦l.ty p β ξ⟧ → ⟦l.ty p β ξ⟧
  | .two, p, β, ξ => Fp6Val.mulXiBeta (β : ZMod p) (ξ : ZMod p)
  | .six, p, β, ξ => Fp12Val.mulByVBeta (β : ZMod p) (ξ : ZMod p)
  | .twelve, p, β, ξ => mulW12 (β : ZMod p) (ξ : ZMod p)

/-- The embedding of the level below. -/
def liftL : (l : Lvl) → (p : Nat) → (β ξ : Int) → ⟦l.base p β ξ⟧ → ⟦l.ty p β ξ⟧
  | .two, _, _, _ => fun a => (⟨a, 0⟩ : Fp2Val _)
  | .six, _, _, _ => fun a => (⟨a, 0, 0⟩ : Fp6Val _)
  | .twelve, _, _, _ => fun a => (⟨a, zero6⟩ : Fp12Val _)

instance : DialectDenote towerDialect where
  denote
    | .add l p β ξ => fun a => addL l p β ξ a.head a.tail.head
    | .sub l p β ξ => fun a => subL l p β ξ a.head a.tail.head
    | .neg l p β ξ => fun a => negL l p β ξ a.head
    | .mul l p β ξ => fun a => mulL l p β ξ a.head a.tail.head
    | .square l p β ξ => fun a => mulL l p β ξ a.head a.head
    | .mulByNonResidue l p β ξ => fun a => mulNRL l p β ξ a.head
    | .frobenius2 _ _ => fun a => Fp2Val.frobenius a.head
    | .sparseMul p β ξ => fun a =>
        Fp12Val.mulBeta (β : ZMod p) (ξ : ZMod p) a.head
          (line014 a.tail.head a.tail.tail.head a.tail.tail.tail.head)
    | .lift l p β ξ => fun a => liftL l p β ξ a.head
    | .proj2 _ _ i => fun a => match i with
        | 0 => a.head.c0
        | 1 => a.head.c1
    | .proj6 _ _ _ i => fun a => match i with
        | 0 => a.head.a0
        | 1 => a.head.a1
        | 2 => a.head.a2
    | .proj12 _ _ _ i => fun a => match i with
        | 0 => a.head.c0
        | 1 => a.head.c1
    | .constFp _ c => fun _ => c

end Denote

/-- The trip counter of `towerDialect` is its `word` type. -/
instance : HasWord64 towerDialect where
  word := TowerTy.word
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- The bit type of `towerDialect`. -/
instance : HasBitType towerDialect where
  bit := TowerTy.bit

/-- The bit of `towerDialect` denotes a `Bool`. -/
instance : HasBoolBit towerDialect where
  toBool := id

/-! ## 5. Expressions over `ZMod p` and their emission -/

section Emit

variable {p : Nat}

/-- A program of `fieldDialect` with results `ts`. -/
abbrev MRC (Γ : Ctxt fieldDialect) (ts : List FieldTy) : Type :=
  MultiReturnCom fieldDialect Γ ts

/-- A renaming of variables from `Γ` to `Γ'`. -/
abbrev Ren (Γ Γ' : Ctxt fieldDialect) : Type :=
  ∀ {t : FieldTy}, Ctxt.Var Γ t → Ctxt.Var Γ' t

/-- A renaming preserves values from `V` to `V'`. -/
def Preserves {Γ Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V : Ctxt.Valuation Γ)
    (V' : Ctxt.Valuation Γ') : Prop :=
  ∀ {t : FieldTy} (v : Ctxt.Var Γ t), (r v).lookup V' = v.lookup V

theorem Preserves.comp {Γ₁ Γ₂ Γ₃ : Ctxt fieldDialect} {r₁ : Ren Γ₁ Γ₂} {r₂ : Ren Γ₂ Γ₃}
    {V₁ : Ctxt.Valuation Γ₁} {V₂ : Ctxt.Valuation Γ₂} {V₃ : Ctxt.Valuation Γ₃}
    (h₁ : Preserves r₁ V₁ V₂) (h₂ : Preserves r₂ V₂ V₃) :
    Preserves (fun v => r₂ (r₁ v)) V₁ V₃ :=
  fun v => (h₂ (r₁ v)).trans (h₁ v)

variable (p) in
/-- An expression over `ZMod p` in `n` inputs. -/
inductive TExpr (n : Nat) where
  /-- Input `i`. -/
  | inp (i : Fin n)
  /-- The constant `c`. -/
  | const (c : ZMod p)
  /-- A sum. -/
  | add (a b : TExpr n)
  /-- A difference. -/
  | sub (a b : TExpr n)
  /-- A negation. -/
  | neg (a : TExpr n)
  /-- A product. -/
  | mul (a b : TExpr n)

/-- The value of an expression at the inputs `x`. -/
def TExpr.eval {n : Nat} (x : Fin n → ZMod p) : TExpr p n → ZMod p
  | .inp i => x i
  | .const c => c
  | .add a b => a.eval x + b.eval x
  | .sub a b => a.eval x - b.eval x
  | .neg a => -a.eval x
  | .mul a b => a.eval x * b.eval x

/-- `c · e`, with no binding for `c = 1` and a negation for `c = −1`. -/
def TExpr.mulSc {n : Nat} (c : Int) (e : TExpr p n) : TExpr p n :=
  if c = 1 then e else if c = -1 then .neg e else .mul (.const (c : ZMod p)) e

/-- `x + c · y`, with no binding for `c = 0`, a sum for `c = 1` and a difference for
    `c = −1`. -/
def TExpr.addSc {n : Nat} (c : Int) (x y : TExpr p n) : TExpr p n :=
  if c = 0 then x else if c = 1 then .add x y else if c = -1 then .sub x y
  else .add x (.mul (.const (c : ZMod p)) y)

@[simp] theorem TExpr.mulSc_eval {n : Nat} (c : Int) (e : TExpr p n) (x : Fin n → ZMod p) :
    (TExpr.mulSc c e).eval x = (c : ZMod p) * e.eval x := by
  unfold TExpr.mulSc
  split_ifs with h1 h2
  · subst h1; simp
  · subst h2; simp [TExpr.eval]
  · rfl

@[simp] theorem TExpr.addSc_eval {n : Nat} (c : Int) (a b : TExpr p n)
    (x : Fin n → ZMod p) :
    (TExpr.addSc c a b).eval x = a.eval x + (c : ZMod p) * b.eval x := by
  unfold TExpr.addSc
  split_ifs with h0 h1 h2
  · subst h0; simp
  · subst h1; simp [TExpr.eval]
  · subst h2; simp [TExpr.eval, sub_eq_add_neg]
  · rfl

/-- The program of an expression: one binding per constant, sum, difference, negation
    and product, then the continuation on the renaming into its context and the
    variable holding the value. -/
def emitT {ts : List FieldTy} {n : Nat} : TExpr p n → {Γ : Ctxt fieldDialect} →
    (Fin n → Ctxt.Var Γ (.fp p)) →
    ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → MRC Γ' ts) → MRC Γ ts
  | .inp i, _, env, k => k (fun v => v) (env i)
  | .const c, _, _, k => .var ⟨.fConst p c, rfl, .nil⟩ (k (fun v => v.there) .here)
  | .add a b, _, env, k =>
    emitT a env fun r₁ va => emitT b (fun i => r₁ (env i)) fun r₂ vb =>
      .var ⟨.fAdd p, rfl, .cons (r₂ va) (.cons vb .nil)⟩ (k (fun v => (r₂ (r₁ v)).there) .here)
  | .sub a b, _, env, k =>
    emitT a env fun r₁ va => emitT b (fun i => r₁ (env i)) fun r₂ vb =>
      .var ⟨.fSub p, rfl, .cons (r₂ va) (.cons vb .nil)⟩ (k (fun v => (r₂ (r₁ v)).there) .here)
  | .neg a, _, env, k =>
    emitT a env fun r₁ va =>
      .var ⟨.fNeg p, rfl, .cons va .nil⟩ (k (fun v => (r₁ v).there) .here)
  | .mul a b, _, env, k =>
    emitT a env fun r₁ va => emitT b (fun i => r₁ (env i)) fun r₂ vb =>
      .var ⟨.fMul p, rfl, .cons (r₂ va) (.cons vb .nil)⟩ (k (fun v => (r₂ (r₁ v)).there) .here)

/-- **Denotation of `emitT`.** If `env` holds `x` under `V` and the continuation
    denotes `R` whenever its renaming preserves values and its variable holds the value
    of `e`, then `emitT e env k` denotes `R`. -/
theorem emitT_denote {ts : List FieldTy} {n : Nat} (x : Fin n → ZMod p) (e : TExpr p n)
    {Γ : Ctxt fieldDialect} (env : Fin n → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → MRC Γ' ts)
    (V : Ctxt.Valuation Γ) (R : ListDenote ts) (hx : ∀ i, (env i).lookup V = x i)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ')
      (w : Ctxt.Var Γ' (.fp p)), Preserves r V V' → w.lookup V' = e.eval x →
      (k r w).denote V' = R) :
    (emitT e env k).denote V = R := by
  induction e generalizing Γ R with
  | inp i => exact hk _ V (env i) (fun _ => rfl) (hx i)
  | const c => exact hk _ _ .here (fun _ => rfl) rfl
  | add a b iha ihb =>
    refine iha env _ V R hx fun r₁ V₁ va h₁ hva => ?_
    refine ihb (fun i => r₁ (env i)) _ V₁ R (fun i => (h₁ (env i)).trans (hx i))
      fun r₂ V₂ vb h₂ hvb => ?_
    refine hk _ _ .here (fun v => (h₂ (r₁ v)).trans (h₁ v)) ?_
    exact congrArg₂ (fun u w : ZMod p => u + w) ((h₂ va).trans hva) hvb
  | sub a b iha ihb =>
    refine iha env _ V R hx fun r₁ V₁ va h₁ hva => ?_
    refine ihb (fun i => r₁ (env i)) _ V₁ R (fun i => (h₁ (env i)).trans (hx i))
      fun r₂ V₂ vb h₂ hvb => ?_
    refine hk _ _ .here (fun v => (h₂ (r₁ v)).trans (h₁ v)) ?_
    exact congrArg₂ (fun u w : ZMod p => u - w) ((h₂ va).trans hva) hvb
  | neg a iha =>
    refine iha env _ V R hx fun r₁ V₁ va h₁ hva => ?_
    refine hk _ _ .here (fun v => h₁ v) ?_
    exact congrArg (fun u : ZMod p => -u) hva
  | mul a b iha ihb =>
    refine iha env _ V R hx fun r₁ V₁ va h₁ hva => ?_
    refine ihb (fun i => r₁ (env i)) _ V₁ R (fun i => (h₁ (env i)).trans (hx i))
      fun r₂ V₂ vb h₂ hvb => ?_
    refine hk _ _ .here (fun v => (h₂ (r₁ v)).trans (h₁ v)) ?_
    exact congrArg₂ (fun u w : ZMod p => u * w) ((h₂ va).trans hva) hvb

/-- The program of `m` expressions over `n` inputs, emitted in order, then the
    continuation on the renaming into its context and the `m` variables holding the
    values. -/
def emitVecT {ts : List FieldTy} {n : Nat} : (m : Nat) → (Fin m → TExpr p n) →
    {Γ : Ctxt fieldDialect} → (Fin n → Ctxt.Var Γ (.fp p)) →
    ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts) →
    MRC Γ ts
  | 0, _, _, _, k => k (fun v => v) Fin.elim0
  | m + 1, es, _, env, k =>
    emitT (es 0) env fun r₁ v =>
      emitVecT m (fun j => es j.succ) (fun i => r₁ (env i)) fun r₂ vs =>
        k (fun w => r₂ (r₁ w)) (Fin.cons (r₂ v) vs)

/-- **Denotation of `emitVecT`.** -/
theorem emitVecT_denote {ts : List FieldTy} {n : Nat} (x : Fin n → ZMod p) :
    ∀ (m : Nat) (es : Fin m → TExpr p n) {Γ : Ctxt fieldDialect}
      (env : Fin n → Ctxt.Var Γ (.fp p))
      (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts)
      (V : Ctxt.Valuation Γ) (R : ListDenote ts), (∀ i, (env i).lookup V = x i) →
      (∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ')
        (ws : Fin m → Ctxt.Var Γ' (.fp p)), Preserves r V V' →
        (∀ j, (ws j).lookup V' = (es j).eval x) → (k r ws).denote V' = R) →
      (emitVecT m es env k).denote V = R
  | 0, _, _, _, _, V, _, _, hk => hk _ V Fin.elim0 (fun _ => rfl) (fun j => j.elim0)
  | m + 1, es, _, env, k, V, R, hx, hk => by
    refine emitT_denote x (es 0) env _ V R hx fun r₁ V₁ v h₁ hv => ?_
    refine emitVecT_denote x m (fun j => es j.succ) (fun i => r₁ (env i)) _ V₁ R
      (fun i => (h₁ (env i)).trans (hx i)) fun r₂ V₂ vs h₂ hvs => ?_
    refine hk _ V₂ _ (Preserves.comp h₁ h₂) fun j => ?_
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (h₂ v).trans hv
    · exact hvs j

end Emit

/-! ## 6. Straight-line programs over a register file -/

section SLP

/-- A straight-line program over `k` registers with `m` results, in the instruction
    set `I`: each step appends the value of one instruction to the register file. -/
inductive SLP (I : Nat → Type) : Nat → Nat → Type where
  /-- Return the registers `outs`. -/
  | ret {k m : Nat} (outs : Fin m → Fin k) : SLP I k m
  /-- Append the value of `ins` and continue. -/
  | step {k m : Nat} (ins : I k) (rest : SLP I (k + 1) m) : SLP I k m

variable {I : Nat → Type} {A : Type} {B : Ctxt fieldDialect → Type}

/-- The values of a program's results. -/
def SLP.eval (ev : ∀ {k : Nat}, I k → (Fin k → A) → A) :
    {k m : Nat} → SLP I k m → (Fin k → A) → Fin m → A
  | _, _, .ret outs, xs => fun j => xs (outs j)
  | _, _, .step ins rest, xs => rest.eval ev (Fin.snoc (α := fun _ => A) xs (ev ins xs))

/-- The emission of a program: each instruction is emitted by `em`, and its result
    bundle is appended to the register file. -/
def SLP.emit (ren : ∀ {Γ Γ' : Ctxt fieldDialect}, Ren Γ Γ' → B Γ → B Γ')
    (em : ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy}, I k → (Fin k → B Γ) →
      ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → B Γ' → MRC Γ' ts) → MRC Γ ts)
    {ts : List FieldTy} :
    {k m : Nat} → SLP I k m → {Γ : Ctxt fieldDialect} → (Fin k → B Γ) →
    ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → B Γ') → MRC Γ' ts) → MRC Γ ts
  | _, _, .ret outs, _, env, kk => kk (fun v => v) (fun j => env (outs j))
  | _, _, .step ins rest, _, env, kk =>
    em ins env fun r z =>
      rest.emit ren em (Fin.snoc (α := fun _ => B _) (fun i => ren r (env i)) z)
        fun r' zs => kk (fun v => r' (r v)) zs

/-- An emitter is sound for the values `val` and the semantics `ev`: the emitted code
    of an instruction hands the continuation a bundle holding the instruction's
    value. -/
def EmitSound (val : ∀ {Γ : Ctxt fieldDialect}, B Γ → Ctxt.Valuation Γ → A)
    (ev : ∀ {k : Nat}, I k → (Fin k → A) → A)
    (em : ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy}, I k → (Fin k → B Γ) →
      ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → B Γ' → MRC Γ' ts) → MRC Γ ts) : Prop :=
  ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy} (ins : I k) (env : Fin k → B Γ)
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → B Γ' → MRC Γ' ts)
    (V : Ctxt.Valuation Γ) (R : ListDenote ts),
    (∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ') (z : B Γ'),
      Preserves r V V' → val z V' = ev ins (fun i => val (env i) V) → (kk r z).denote V' = R) →
    (em ins env kk).denote V = R

/-- **Correctness of an emitted program.** Under a sound emitter whose renaming of
    bundles preserves values, the emitted program hands the continuation bundles
    holding the values of the program's results. -/
theorem SLP.emit_denote (val : ∀ {Γ : Ctxt fieldDialect}, B Γ → Ctxt.Valuation Γ → A)
    (ren : ∀ {Γ Γ' : Ctxt fieldDialect}, Ren Γ Γ' → B Γ → B Γ')
    (ev : ∀ {k : Nat}, I k → (Fin k → A) → A)
    (em : ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy}, I k → (Fin k → B Γ) →
      ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → B Γ' → MRC Γ' ts) → MRC Γ ts)
    (hren : ∀ {Γ Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V : Ctxt.Valuation Γ)
      (V' : Ctxt.Valuation Γ') (b : B Γ), Preserves r V V' → val (ren r b) V' = val b V)
    (hs : EmitSound val ev em) {ts : List FieldTy} :
    ∀ {k m : Nat} (P : SLP I k m) {Γ : Ctxt fieldDialect} (env : Fin k → B Γ)
      (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → B Γ') → MRC Γ' ts)
      (V : Ctxt.Valuation Γ) (R : ListDenote ts),
      (∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ') (zs : Fin m → B Γ'),
        Preserves r V V' → (∀ j, val (zs j) V' = P.eval ev (fun i => val (env i) V) j) →
        (kk r zs).denote V' = R) →
      (P.emit ren em env kk).denote V = R
  | _, _, .ret outs, _, env, kk, V, R, hk => hk _ V _ (fun _ => rfl) (fun _ => rfl)
  | _, _, .step ins rest, _, env, kk, V, R, hk => by
    refine hs ins env _ V R fun r V' z hr hz => ?_
    refine SLP.emit_denote val ren ev em hren hs rest _ _ V' R fun r' V'' zs hr' hzs => ?_
    refine hk _ V'' zs (Preserves.comp hr hr') fun j => (hzs j).trans ?_
    show rest.eval ev _ j = rest.eval ev _ j
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]; exact hz
    · simp only [Fin.snoc_castSucc]; exact hren r V V' (env i) hr

end SLP

/-! ## 7. Register bundles -/

section Bundles

variable {p : Nat}

variable (p) in
/-- The two coordinate variables of an `Fp2` value. -/
structure F2 (Γ : Ctxt fieldDialect) where
  /-- The `1`-coordinate. -/
  c0 : Ctxt.Var Γ (.fp p)
  /-- The `u`-coordinate. -/
  c1 : Ctxt.Var Γ (.fp p)

/-- The value of an `Fp2` bundle. -/
def F2.val {Γ : Ctxt fieldDialect} (x : F2 p Γ) (V : Ctxt.Valuation Γ) : Fp2Val p :=
  ⟨x.c0.lookup V, x.c1.lookup V⟩

/-- The renaming of an `Fp2` bundle. -/
def F2.ren {Γ Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (x : F2 p Γ) : F2 p Γ' := ⟨r x.c0, r x.c1⟩

theorem F2.val_ren {Γ Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V : Ctxt.Valuation Γ)
    (V' : Ctxt.Valuation Γ') (x : F2 p Γ) (h : Preserves r V V') :
    (x.ren r).val V' = x.val V :=
  Fp2Val.ext (h x.c0) (h x.c1)

variable (p) in
/-- The three `Fp2` bundles of an `Fp6` value. -/
structure F6 (Γ : Ctxt fieldDialect) where
  /-- The `1`-coordinate. -/
  a0 : F2 p Γ
  /-- The `v`-coordinate. -/
  a1 : F2 p Γ
  /-- The `v²`-coordinate. -/
  a2 : F2 p Γ

/-- The value of an `Fp6` bundle. -/
def F6.val {Γ : Ctxt fieldDialect} (x : F6 p Γ) (V : Ctxt.Valuation Γ) : Fp6Val p :=
  ⟨x.a0.val V, x.a1.val V, x.a2.val V⟩

/-- The renaming of an `Fp6` bundle. -/
def F6.ren {Γ Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (x : F6 p Γ) : F6 p Γ' :=
  ⟨x.a0.ren r, x.a1.ren r, x.a2.ren r⟩

theorem F6.val_ren {Γ Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V : Ctxt.Valuation Γ)
    (V' : Ctxt.Valuation Γ') (x : F6 p Γ) (h : Preserves r V V') :
    (x.ren r).val V' = x.val V := by
  simp only [F6.val, F6.ren, F2.val_ren r V V' _ h]

end Bundles

/-! ## 8. `Fp2` instructions -/

section Fp2

variable {p : Nat}

/-- Two stages of expressions over the `n` coordinate variables `env`: the first stage
    binds `m₁` values, the second the two coordinates of the result. -/
def stepN {ts : List FieldTy} {n m₁ : Nat} (es₁ : Fin m₁ → TExpr p n) (es₂ : Fin 2 → TExpr p m₁)
    {Γ : Ctxt fieldDialect} (env : Fin n → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F2 p Γ' → MRC Γ' ts) : MRC Γ ts :=
  emitVecT m₁ es₁ env fun r₁ w => emitVecT 2 es₂ w fun r₂ c => k (fun v => r₂ (r₁ v)) ⟨c 0, c 1⟩

/-- The value of `stepN es₁ es₂` at the coordinate values `x`. -/
def stepVal {n m₁ : Nat} (es₁ : Fin m₁ → TExpr p n) (es₂ : Fin 2 → TExpr p m₁)
    (x : Fin n → ZMod p) : Fp2Val p :=
  ⟨(es₂ 0).eval (fun i => (es₁ i).eval x), (es₂ 1).eval (fun i => (es₁ i).eval x)⟩

theorem stepN_denote {ts : List FieldTy} {n m₁ : Nat} (es₁ : Fin m₁ → TExpr p n)
    (es₂ : Fin 2 → TExpr p m₁) {Γ : Ctxt fieldDialect} (env : Fin n → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F2 p Γ' → MRC Γ' ts)
    (V : Ctxt.Valuation Γ) (R : ListDenote ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ') (z : F2 p Γ'),
      Preserves r V V' → z.val V' = stepVal es₁ es₂ (fun i => (env i).lookup V) →
      (k r z).denote V' = R) :
    (stepN es₁ es₂ env k).denote V = R := by
  refine emitVecT_denote _ m₁ es₁ env _ V R (fun _ => rfl) fun r₁ V₁ w h₁ hw => ?_
  refine emitVecT_denote _ 2 es₂ w _ V₁ R hw fun r₂ V₂ c h₂ hc => ?_
  refine hk _ V₂ _ (Preserves.comp h₁ h₂) ?_
  show (⟨(c 0).lookup V₂, (c 1).lookup V₂⟩ : Fp2Val p) = _
  rw [hc 0, hc 1]
  rfl

/-- The four coordinate variables of two `Fp2` bundles. -/
def env4 {Γ : Ctxt fieldDialect} (x y : F2 p Γ) : Fin 4 → Ctxt.Var Γ (.fp p) :=
  ![x.c0, x.c1, y.c0, y.c1]

/-- The two coordinate variables of an `Fp2` bundle. -/
def env2 {Γ : Ctxt fieldDialect} (x : F2 p Γ) : Fin 2 → Ctxt.Var Γ (.fp p) :=
  ![x.c0, x.c1]

/-- The `Fp2` instructions over `k` registers. -/
inductive I2 (k : Nat) where
  /-- Sum of two registers. -/
  | add (i j : Fin k)
  /-- Difference of two registers. -/
  | sub (i j : Fin k)
  /-- Negation of a register. -/
  | neg (i : Fin k)
  /-- Product of two registers. -/
  | mul (i j : Fin k)
  /-- Square of a register. -/
  | sq (i : Fin k)
  /-- Product of a register with `ξ + u`. -/
  | mulXi (i : Fin k)
  /-- Conjugate of a register. -/
  | conj (i : Fin k)
  /-- The zero value. -/
  | zero

/-- The value of an `Fp2` instruction. -/
def I2.eval (β ξ : Int) {k : Nat} : I2 k → (Fin k → Fp2Val p) → Fp2Val p
  | .add i j, xs => xs i + xs j
  | .sub i j, xs => xs i - xs j
  | .neg i, xs => -xs i
  | .mul i j, xs => Fp2Val.mulBeta (β : ZMod p) (xs i) (xs j)
  | .sq i, xs => Fp2Val.mulBeta (β : ZMod p) (xs i) (xs i)
  | .mulXi i, xs => Fp6Val.mulXiBeta (β : ZMod p) (ξ : ZMod p) (xs i)
  | .conj i, xs => Fp2Val.frobenius (xs i)
  | .zero, _ => 0

/-- The pass-through stage. -/
def idE {n : Nat} : Fin n → TExpr p n := TExpr.inp

/-- Second stage of the sum, over `x0, x1, y0, y1`. -/
def addE₂ : Fin 2 → TExpr p 4 := ![.add (.inp 0) (.inp 2), .add (.inp 1) (.inp 3)]

/-- Second stage of the difference. -/
def subE₂ : Fin 2 → TExpr p 4 := ![.sub (.inp 0) (.inp 2), .sub (.inp 1) (.inp 3)]

/-- Second stage of the negation, over `x0, x1`. -/
def negE₂ : Fin 2 → TExpr p 2 := ![.neg (.inp 0), .neg (.inp 1)]

/-- First stage of the Karatsuba product: `x0·y0`, `x1·y1`, `(x0 + x1)·(y0 + y1)`. -/
def mulE₁ : Fin 3 → TExpr p 4 :=
  ![.mul (.inp 0) (.inp 2), .mul (.inp 1) (.inp 3),
    .mul (.add (.inp 0) (.inp 1)) (.add (.inp 2) (.inp 3))]

/-- Second stage of the Karatsuba product: `v0 + β·v1` and `s − v0 − v1`. -/
def mulE₂ (β : Int) : Fin 2 → TExpr p 3 :=
  ![TExpr.addSc β (.inp 0) (.inp 1), .sub (.sub (.inp 2) (.inp 0)) (.inp 1)]

/-- First stage of the complex-method square: `x0·x1` and `(x0 + x1)·(x0 + β·x1)`. -/
def sqE₁ (β : Int) : Fin 2 → TExpr p 2 :=
  ![.mul (.inp 0) (.inp 1), .mul (.add (.inp 0) (.inp 1)) (TExpr.addSc β (.inp 0) (.inp 1))]

/-- Second stage of the complex-method square: `m − (1 + β)·v` and `v + v`. -/
def sqE₂ (β : Int) : Fin 2 → TExpr p 2 :=
  ![TExpr.addSc (-(1 + β)) (.inp 1) (.inp 0), .add (.inp 0) (.inp 0)]

/-- Second stage of the product with `ξ + u`: `ξ·x0 + β·x1` and `x0 + ξ·x1`. -/
def mulXiE₂ (β ξ : Int) : Fin 2 → TExpr p 2 :=
  ![TExpr.addSc β (TExpr.mulSc ξ (.inp 0)) (.inp 1), TExpr.addSc ξ (.inp 0) (.inp 1)]

/-- Second stage of the conjugation. -/
def conjE₂ : Fin 2 → TExpr p 2 := ![.inp 0, .neg (.inp 1)]

/-- The zero value. -/
def zeroE₂ : Fin 2 → TExpr p 0 := ![.const 0, .const 0]

/-- The emission of an `Fp2` instruction. -/
def I2.emit (p : Nat) (β ξ : Int) {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy} :
    I2 k → (Fin k → F2 p Γ) →
    ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F2 p Γ' → MRC Γ' ts) → MRC Γ ts
  | .add i j, env, kk => stepN idE addE₂ (env4 (env i) (env j)) kk
  | .sub i j, env, kk => stepN idE subE₂ (env4 (env i) (env j)) kk
  | .neg i, env, kk => stepN idE negE₂ (env2 (env i)) kk
  | .mul i j, env, kk => stepN mulE₁ (mulE₂ β) (env4 (env i) (env j)) kk
  | .sq i, env, kk => stepN (sqE₁ β) (sqE₂ β) (env2 (env i)) kk
  | .mulXi i, env, kk => stepN idE (mulXiE₂ β ξ) (env2 (env i)) kk
  | .conj i, env, kk => stepN idE conjE₂ (env2 (env i)) kk
  | .zero, _, kk => stepN idE zeroE₂ Fin.elim0 kk

/-- **The `Fp2` instructions are sound**: the emitted code of each instruction
    computes its value. -/
theorem I2.emit_sound (β ξ : Int) :
    EmitSound (fun {Γ} (x : F2 p Γ) V => x.val V) (fun {k} (ins : I2 k) xs => ins.eval β ξ xs)
      (fun {k Γ ts} ins env kk => I2.emit p β ξ (k := k) (Γ := Γ) (ts := ts) ins env kk) := by
  intro k Γ ts ins env kk V R hk
  cases ins with
  | add i j =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    ext <;> simp [stepVal, addE₂, idE, env4, TExpr.eval, I2.eval, F2.val]
  | sub i j =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    ext <;> simp [stepVal, subE₂, idE, env4, TExpr.eval, I2.eval, F2.val]
  | neg i =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    ext <;> simp [stepVal, negE₂, idE, env2, TExpr.eval, I2.eval, F2.val]
  | mul i j =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    ext <;> simp [stepVal, mulE₁, mulE₂, env4, TExpr.eval, I2.eval, F2.val]; ring
  | sq i =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    ext <;> simp [stepVal, sqE₁, sqE₂, env2, TExpr.eval, I2.eval, F2.val] <;> ring
  | mulXi i =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    ext <;> simp [stepVal, mulXiE₂, idE, env2, TExpr.eval, I2.eval, F2.val,
      Fp6Val.mulXiBeta] <;> ring
  | conj i =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    ext <;> simp [stepVal, conjE₂, idE, env2, TExpr.eval, I2.eval, F2.val]
  | zero =>
    refine stepN_denote _ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    rfl

/-- The emitter of the `Fp2` instructions. -/
abbrev em2 (p : Nat) (β ξ : Int) : ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy},
    I2 k → (Fin k → F2 p Γ) → ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F2 p Γ' → MRC Γ' ts) →
    MRC Γ ts :=
  fun ins env kk => I2.emit p β ξ ins env kk

/-- The semantics of the `Fp2` instructions. -/
abbrev ev2 (p : Nat) (β ξ : Int) : ∀ {k : Nat}, I2 k → (Fin k → Fp2Val p) → Fp2Val p :=
  fun ins xs => ins.eval β ξ xs

end Fp2

/-! ## 9. Blocks over the flattened registers -/

section Blocks

variable {p : Nat}

/-- Variable `i` of `List.replicate n τ`, with index `0` the head. -/
def regVar {τ : FieldTy} : (n : Nat) → Fin n → @Ctxt.Var fieldDialect (List.replicate n τ) τ
  | _ + 1, ⟨0, _⟩ => .here
  | n + 1, ⟨j + 1, h⟩ => (regVar n ⟨j, by omega⟩).there

variable (p) in
/-- Register `i` of `k` flattened `Fp2` values: the variables `2i` and `2i + 1`. -/
def inEnv2 (k : Nat) (i : Fin k) : F2 p (List.replicate (2 * k) (FieldTy.fp p)) :=
  ⟨regVar (2 * k) ⟨2 * i.val, by omega⟩, regVar (2 * k) ⟨2 * i.val + 1, by omega⟩⟩

/-- The coordinate variables of `m` bundles, in order. -/
def outVars2 {Γ : Ctxt fieldDialect} : (m : Nat) → (Fin m → F2 p Γ) →
    HVector (fun t => Ctxt.Var Γ t) (List.replicate (2 * m) (FieldTy.fp p))
  | 0, _ => .nil
  | m + 1, zs => .cons (zs 0).c0 (.cons (zs 0).c1 (outVars2 m (fun j => zs j.succ)))

variable (p) in
/-- The flattened coordinates of `m` values of `Fp2`. -/
def encRegs : (m : Nat) → (Fin m → Fp2Val p) →
    Ctxt.Valuation (List.replicate (2 * m) (FieldTy.fp p) : Ctxt fieldDialect)
  | 0, _ => .nil
  | m + 1, xs => .cons (xs 0).c0 (.cons (xs 0).c1 (encRegs m (fun j => xs j.succ)))

theorem lookupVars_outVars2 {Γ : Ctxt fieldDialect} (V : Ctxt.Valuation Γ) :
    ∀ (m : Nat) (zs : Fin m → F2 p Γ),
      MultiReturnCom.lookupVars (outVars2 m zs) V = encRegs p m (fun j => (zs j).val V)
  | 0, _ => rfl
  | m + 1, zs => by
    show HVector.cons _ (HVector.cons _ (MultiReturnCom.lookupVars (outVars2 m _) V)) = _
    rw [lookupVars_outVars2 V m]
    rfl

variable (p) in
/-- The block of an `Fp2` program over `k` flattened `Fp2` arguments. -/
def blk2 (β ξ : Int) {k m : Nat} (P : SLP I2 k m) :
    MRC (List.replicate (2 * k) (FieldTy.fp p)) (List.replicate (2 * m) (FieldTy.fp p)) :=
  P.emit (B := F2 p) (fun r x => x.ren r) (em2 p β ξ) (fun i => inEnv2 p k i)
    fun _ zs => .ret (outVars2 m zs)

/-- **Correctness of a block generated from an `Fp2` program.** -/
theorem blk2_denote (β ξ : Int) {k m : Nat} (P : SLP I2 k m)
    (V : Ctxt.Valuation (List.replicate (2 * k) (FieldTy.fp p) : Ctxt fieldDialect)) :
    (blk2 p β ξ P).denote V = encRegs p m (P.eval (ev2 p β ξ) (fun i => (inEnv2 p k i).val V)) :=
  SLP.emit_denote (B := F2 p) (fun x V => x.val V) (fun r x => x.ren r) (ev2 p β ξ) (em2 p β ξ)
    (fun r V V' b h => F2.val_ren r V V' b h) (I2.emit_sound β ξ) P _ _ V _
    fun _ V' zs _ hzs => by
      show MultiReturnCom.lookupVars (outVars2 m zs) V' = _
      rw [lookupVars_outVars2]
      exact congrArg (encRegs p m) (funext hzs)

end Blocks

/-! ## 10. `Fp6` instructions -/

section Fp6

variable {p : Nat}

/-- Sum of two `Fp6` values: registers `0, 1, 2` and `3, 4, 5`. -/
def add6P : SLP I2 6 3 :=
  .step (.add 0 3) <| .step (.add 1 4) <| .step (.add 2 5) <| .ret ![6, 7, 8]

/-- Difference of two `Fp6` values. -/
def sub6P : SLP I2 6 3 :=
  .step (.sub 0 3) <| .step (.sub 1 4) <| .step (.sub 2 5) <| .ret ![6, 7, 8]

/-- Negation of an `Fp6` value. -/
def neg6P : SLP I2 3 3 :=
  .step (.neg 0) <| .step (.neg 1) <| .step (.neg 2) <| .ret ![3, 4, 5]

/-- Product of two `Fp6` values with six `Fp2` products and two products with `ξ + u`:
    `v_i = a_i·b_i`, `c0 = v0 + ξ·((a1 + a2)(b1 + b2) − v1 − v2)`,
    `c1 = (a0 + a1)(b0 + b1) − v0 − v1 + ξ·v2`, `c2 = (a0 + a2)(b0 + b2) − v0 + v1 − v2`. -/
def mul6P : SLP I2 6 3 :=
  .step (.mul 0 3) <| .step (.mul 1 4) <| .step (.mul 2 5) <|
  .step (.add 1 2) <| .step (.add 4 5) <| .step (.mul 9 10) <|
  .step (.sub 11 7) <| .step (.sub 12 8) <| .step (.mulXi 13) <| .step (.add 14 6) <|
  .step (.add 0 1) <| .step (.add 3 4) <| .step (.mul 16 17) <|
  .step (.sub 18 6) <| .step (.sub 19 7) <| .step (.mulXi 8) <| .step (.add 20 21) <|
  .step (.add 0 2) <| .step (.add 3 5) <| .step (.mul 23 24) <|
  .step (.sub 25 6) <| .step (.add 26 7) <| .step (.sub 27 8) <|
  .ret ![15, 22, 28]

/-- Chung–Hasan squaring of an `Fp6` value: `s0 = a0²`, `s1 = 2·a0·a1`,
    `s2 = (a0 − a1 + a2)²`, `s3 = 2·a1·a2`, `s4 = a2²`; `c0 = s0 + ξ·s3`,
    `c1 = s1 + ξ·s4`, `c2 = s1 + s2 + s3 − s0 − s4`. -/
def sq6P : SLP I2 3 3 :=
  .step (.sq 0) <| .step (.mul 0 1) <| .step (.add 4 4) <|
  .step (.sub 0 1) <| .step (.add 6 2) <| .step (.sq 7) <|
  .step (.mul 1 2) <| .step (.add 9 9) <| .step (.sq 2) <|
  .step (.mulXi 10) <| .step (.add 3 12) <| .step (.mulXi 11) <| .step (.add 5 14) <|
  .step (.add 5 8) <| .step (.add 16 10) <| .step (.sub 17 3) <| .step (.sub 18 11) <|
  .ret ![13, 15, 19]

/-- Product of an `Fp6` value with `v`: `(ξ·a2, a0, a1)`. -/
def mulV6P : SLP I2 3 3 := .step (.mulXi 2) <| .ret ![3, 0, 1]

/-- The `Fp6` instructions over `k` registers. -/
inductive I6 (k : Nat) where
  /-- Sum of two registers. -/
  | add (i j : Fin k)
  /-- Difference of two registers. -/
  | sub (i j : Fin k)
  /-- Negation of a register. -/
  | neg (i : Fin k)
  /-- Product of two registers. -/
  | mul (i j : Fin k)
  /-- Square of a register. -/
  | sq (i : Fin k)
  /-- Product of a register with `v`. -/
  | mulV (i : Fin k)

/-- The value of an `Fp6` instruction. -/
def I6.eval (β ξ : Int) {k : Nat} : I6 k → (Fin k → Fp6Val p) → Fp6Val p
  | .add i j, xs => Fp6Val.add (xs i) (xs j)
  | .sub i j, xs => Fp6Val.sub (xs i) (xs j)
  | .neg i, xs => neg6 (xs i)
  | .mul i j, xs => Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs i) (xs j)
  | .sq i, xs => Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs i) (xs i)
  | .mulV i, xs => Fp12Val.mulByVBeta (β : ZMod p) (ξ : ZMod p) (xs i)

/-- The `Fp2` registers of two `Fp6` bundles. -/
def env6 {Γ : Ctxt fieldDialect} (x y : F6 p Γ) : Fin 6 → F2 p Γ :=
  ![x.a0, x.a1, x.a2, y.a0, y.a1, y.a2]

/-- The `Fp2` registers of an `Fp6` bundle. -/
def env3 {Γ : Ctxt fieldDialect} (x : F6 p Γ) : Fin 3 → F2 p Γ := ![x.a0, x.a1, x.a2]

/-- The emission of an `Fp2` program with three results as an `Fp6` bundle. -/
def run6 (β ξ : Int) {n : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy} (P : SLP I2 n 3)
    (e : Fin n → F2 p Γ) (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F6 p Γ' → MRC Γ' ts) :
    MRC Γ ts :=
  P.emit (B := F2 p) (fun r x => x.ren r) (em2 p β ξ) e fun r zs => kk r ⟨zs 0, zs 1, zs 2⟩

/-- The emission of an `Fp6` instruction. -/
def I6.emit (p : Nat) (β ξ : Int) {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy} :
    I6 k → (Fin k → F6 p Γ) →
    ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F6 p Γ' → MRC Γ' ts) → MRC Γ ts
  | .add i j, env, kk => run6 β ξ add6P (env6 (env i) (env j)) kk
  | .sub i j, env, kk => run6 β ξ sub6P (env6 (env i) (env j)) kk
  | .neg i, env, kk => run6 β ξ neg6P (env3 (env i)) kk
  | .mul i j, env, kk => run6 β ξ mul6P (env6 (env i) (env j)) kk
  | .sq i, env, kk => run6 β ξ sq6P (env3 (env i)) kk
  | .mulV i, env, kk => run6 β ξ mulV6P (env3 (env i)) kk

/-- The emitter of the `Fp6` instructions. -/
abbrev em6 (p : Nat) (β ξ : Int) : ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy},
    I6 k → (Fin k → F6 p Γ) → ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F6 p Γ' → MRC Γ' ts) →
    MRC Γ ts :=
  fun ins env kk => I6.emit p β ξ ins env kk

/-- The semantics of the `Fp6` instructions. -/
abbrev ev6 (p : Nat) (β ξ : Int) : ∀ {k : Nat}, I6 k → (Fin k → Fp6Val p) → Fp6Val p :=
  fun ins xs => ins.eval β ξ xs

variable (p) in
/-- Soundness of the `Fp6` instructions at `β`, `ξ`. -/
def I6Sound (β ξ : Int) : Prop :=
  EmitSound (B := F6 p) (fun x V => x.val V) (ev6 p β ξ) (em6 p β ξ)

/-- Coordinate `r` of an `Fp6` bundle. -/
def F6.get {Γ : Ctxt fieldDialect} (x : F6 p Γ) : Fin 3 → F2 p Γ := ![x.a0, x.a1, x.a2]

/-- Coordinate `r` of an `Fp6` value. -/
def get6 (x : Fp6Val p) : Fin 3 → Fp2Val p := ![x.a0, x.a1, x.a2]

theorem F6.val_get {Γ : Ctxt fieldDialect} (x : F6 p Γ) (V : Ctxt.Valuation Γ) (r : Fin 3) :
    (x.get r).val V = get6 (x.val V) r := by
  fin_cases r <;> rfl

variable (p) in
/-- Register `i` of `k` flattened `Fp6` values. -/
def inEnv6 (k : Nat) (i : Fin k) : F6 p (List.replicate (2 * (3 * k)) (FieldTy.fp p)) :=
  ⟨inEnv2 p (3 * k) ⟨3 * i.val, by omega⟩, inEnv2 p (3 * k) ⟨3 * i.val + 1, by omega⟩,
    inEnv2 p (3 * k) ⟨3 * i.val + 2, by omega⟩⟩

/-- The six `Fp2` coordinates of two `Fp6` bundles, in order. -/
def flat12 {Γ : Ctxt fieldDialect} (zs : Fin 2 → F6 p Γ) : Fin 6 → F2 p Γ :=
  ![(zs 0).a0, (zs 0).a1, (zs 0).a2, (zs 1).a0, (zs 1).a1, (zs 1).a2]

/-- The six `Fp2` coordinates of two `Fp6` values, in order. -/
def flat12v (ys : Fin 2 → Fp6Val p) : Fin 6 → Fp2Val p :=
  ![(ys 0).a0, (ys 0).a1, (ys 0).a2, (ys 1).a0, (ys 1).a1, (ys 1).a2]

theorem flat12_val {Γ : Ctxt fieldDialect} (zs : Fin 2 → F6 p Γ) (V : Ctxt.Valuation Γ)
    (j : Fin 6) : (flat12 zs j).val V = flat12v (fun i => (zs i).val V) j := by
  fin_cases j <;> rfl

variable (p) in
/-- The block of an `Fp6` program with two results (an `Fp12` value) over `k` flattened
    `Fp6` arguments. -/
def blk6 (β ξ : Int) {k : Nat} (P : SLP I6 k 2) :
    MRC (List.replicate (2 * (3 * k)) (FieldTy.fp p)) (List.replicate (2 * 6) (FieldTy.fp p)) :=
  P.emit (B := F6 p) (fun r x => x.ren r) (em6 p β ξ) (fun i => inEnv6 p k i)
    fun _ zs => .ret (outVars2 6 (flat12 zs))

/-- **Correctness of a block generated from an `Fp6` program**, under the soundness of
    the `Fp6` instructions. -/
theorem blk6_denote (β ξ : Int) (hs : I6Sound p β ξ) {k : Nat} (P : SLP I6 k 2)
    (V : Ctxt.Valuation (List.replicate (2 * (3 * k)) (FieldTy.fp p) : Ctxt fieldDialect)) :
    (blk6 p β ξ P).denote V =
      encRegs p 6 (flat12v (P.eval (ev6 p β ξ) (fun i => (inEnv6 p k i).val V))) :=
  SLP.emit_denote (B := F6 p) (fun x V => x.val V) (fun r x => x.ren r) (ev6 p β ξ) (em6 p β ξ)
    (fun r V V' b h => F6.val_ren r V V' b h) hs P _ _ V _
    fun _ V' zs _ hzs => by
      show MultiReturnCom.lookupVars (outVars2 6 (flat12 zs)) V' = _
      rw [lookupVars_outVars2]
      refine congrArg (encRegs p 6) (funext fun j => ?_)
      rw [flat12_val]
      exact congrArg (fun ys => flat12v ys j) (funext hzs)

end Fp6

/-! ## 11. `Fp12` programs -/

section Fp12

/-- Sum of two `Fp12` values: registers `0, 1` and `2, 3`. -/
def add12P : SLP I6 4 2 := .step (.add 0 2) <| .step (.add 1 3) <| .ret ![4, 5]

/-- Difference of two `Fp12` values. -/
def sub12P : SLP I6 4 2 := .step (.sub 0 2) <| .step (.sub 1 3) <| .ret ![4, 5]

/-- Negation of an `Fp12` value. -/
def neg12P : SLP I6 2 2 := .step (.neg 0) <| .step (.neg 1) <| .ret ![2, 3]

/-- Karatsuba product of two `Fp12` values with three `Fp6` products:
    `c0 = a·c + v·(b·d)`, `c1 = (a + b)(c + d) − a·c − b·d`. -/
def mul12P : SLP I6 4 2 :=
  .step (.mul 0 2) <| .step (.mul 1 3) <| .step (.add 0 1) <| .step (.add 2 3) <|
  .step (.mul 6 7) <| .step (.sub 8 4) <| .step (.sub 9 5) <| .step (.mulV 5) <|
  .step (.add 4 11) <| .ret ![12, 10]

/-- Complex-method square of an `Fp12` value with two `Fp6` products:
    `c0 = (a + b)(a + v·b) − a·b − v·(a·b)`, `c1 = 2·a·b`. -/
def sq12P : SLP I6 2 2 :=
  .step (.mul 0 1) <| .step (.add 0 1) <| .step (.mulV 1) <| .step (.add 0 4) <|
  .step (.mul 3 5) <| .step (.mulV 2) <| .step (.sub 6 2) <| .step (.sub 8 7) <|
  .step (.add 2 2) <| .ret ![9, 10]

/-- Product of an `Fp12` value with `w`: `(v·b) + a·w`, over the `Fp2` registers. -/
def mulW12P : SLP I2 6 6 := .step (.mulXi 5) <| .ret ![6, 3, 4, 0, 1, 2]

/-- The product of an `Fp12` value (registers `0 .. 5`) with the line `(c0, c1, c4)`
    (registers `6, 7, 8`) in the `0-1-4` pattern, with thirteen `Fp2` products:
    `aa = x.c0·(c0 + c1·v)`, `bb = x.c1·(c4·v)`,
    `c1' = (x.c0 + x.c1)·(c0 + (c1 + c4)·v) − aa − bb`, `c0' = aa + v·bb`. -/
def sparse014P : SLP I2 9 6 :=
  .step (.mul 0 6) <| .step (.mul 1 7) <| .step (.mul 2 7) <| .step (.mulXi 11) <|
  .step (.add 12 9) <| .step (.add 6 7) <| .step (.add 0 1) <| .step (.mul 14 15) <|
  .step (.sub 16 9) <| .step (.sub 17 10) <| .step (.mul 2 6) <| .step (.add 19 10) <|
  .step (.mul 5 8) <| .step (.mulXi 21) <| .step (.mul 3 8) <| .step (.mul 4 8) <|
  .step (.add 7 8) <| .step (.add 3 0) <| .step (.add 4 1) <| .step (.add 5 2) <|
  .step (.mul 26 6) <| .step (.mul 27 25) <| .step (.mul 28 25) <| .step (.mulXi 31) <|
  .step (.add 32 29) <| .step (.add 6 25) <| .step (.add 26 27) <| .step (.mul 34 35) <|
  .step (.sub 36 29) <| .step (.sub 37 30) <| .step (.mul 28 6) <| .step (.add 39 30) <|
  .step (.sub 33 13) <| .step (.sub 41 22) <| .step (.sub 38 18) <| .step (.sub 43 23) <|
  .step (.sub 40 20) <| .step (.sub 45 24) <|
  .step (.mulXi 24) <| .step (.add 47 13) <| .step (.add 22 18) <| .step (.add 23 20) <|
  .ret ![48, 49, 50, 42, 44, 46]

/-- The embedding of `Fp2` into `Fp6`. -/
def lift6P : SLP I2 1 3 := .step .zero <| .ret ![0, 1, 1]

/-- The embedding of `Fp6` into `Fp12`. -/
def lift12P : SLP I2 3 6 := .step .zero <| .ret ![0, 1, 2, 3, 3, 3]

/-- Coordinate `i` of an `Fp6` value. -/
def proj6P (i : Fin 3) : SLP I2 3 1 := .ret ![i]

/-- Coordinate `i` of an `Fp12` value. -/
def proj12P (i : Fin 2) : SLP I2 6 3 := .ret fun j => ⟨3 * i.val + j.val, by omega⟩

/-- An `Fp2` program of one binary instruction. -/
def bin2P (f : Fin 2 → Fin 2 → I2 2) : SLP I2 2 1 := .step (f 0 1) <| .ret ![2]

/-- An `Fp2` program of one unary instruction. -/
def un2P (f : Fin 1 → I2 1) : SLP I2 1 1 := .step (f 0) <| .ret ![1]

end Fp12

/-! ## 12. The lowering -/

section Lowering

/-- The `fieldDialect` types representing a tower type: one, two, six or twelve
    coordinates in `F_p`. -/
def towerMapTys : TowerTy → List FieldTy
  | .fp p => [.fp p]
  | .fp2 p _ => List.replicate 2 (.fp p)
  | .fp6 p _ _ => List.replicate 6 (.fp p)
  | .fp12 p _ _ => List.replicate 12 (.fp p)
  | .word => []
  | .bit => []

/-- The encoding of a tower value by its coordinates. -/
def towerEnc : {t : TowerTy} → ⟦t⟧ → @Ctxt.Valuation fieldDialect _ (towerMapTys t)
  | .fp _, x => .cons x .nil
  | .fp2 p _, x => encRegs p 1 ![x]
  | .fp6 p _ _, x => encRegs p 3 ![x.a0, x.a1, x.a2]
  | .fp12 p _ _, x => encRegs p 6 ![x.c0.a0, x.c0.a1, x.c0.a2, x.c1.a0, x.c1.a1, x.c1.a2]
  | .word, _ => .nil
  | .bit, _ => .nil

/-- The block lifting a prime-field value to `Fp2`. -/
def liftFpBlk (p : Nat) : MRC [FieldTy.fp p] (List.replicate 2 (FieldTy.fp p)) :=
  emitVecT 2 ![.inp 0, .const 0] ![Ctxt.Var.here] fun _ w => .ret (.cons (w 0) (.cons (w 1) .nil))

/-- The block of coordinate `i` of an `Fp2` value. -/
def proj2Blk (p : Nat) (i : Fin 2) : MRC (List.replicate 2 (FieldTy.fp p)) [FieldTy.fp p] :=
  .ret (.cons (env2 (inEnv2 p 1 0) i) .nil)

/-- The blocks of the tower ops. -/
def towerLowerOp : (op : TowerOp) →
    MRC (ctxFlat towerMapTys (DialectSignature.sig (d := towerDialect) op))
      (towerMapTys (DialectSignature.ret (d := towerDialect) op))
  | .add .two p β ξ => blk2 p β ξ (bin2P I2.add)
  | .add .six p β ξ => blk2 p β ξ add6P
  | .add .twelve p β ξ => blk6 p β ξ add12P
  | .sub .two p β ξ => blk2 p β ξ (bin2P I2.sub)
  | .sub .six p β ξ => blk2 p β ξ sub6P
  | .sub .twelve p β ξ => blk6 p β ξ sub12P
  | .neg .two p β ξ => blk2 p β ξ (un2P I2.neg)
  | .neg .six p β ξ => blk2 p β ξ neg6P
  | .neg .twelve p β ξ => blk6 p β ξ neg12P
  | .mul .two p β ξ => blk2 p β ξ (bin2P I2.mul)
  | .mul .six p β ξ => blk2 p β ξ mul6P
  | .mul .twelve p β ξ => blk6 p β ξ mul12P
  | .square .two p β ξ => blk2 p β ξ (un2P I2.sq)
  | .square .six p β ξ => blk2 p β ξ sq6P
  | .square .twelve p β ξ => blk6 p β ξ sq12P
  | .mulByNonResidue .two p β ξ => blk2 p β ξ (un2P I2.mulXi)
  | .mulByNonResidue .six p β ξ => blk2 p β ξ mulV6P
  | .mulByNonResidue .twelve p β ξ => blk2 p β ξ mulW12P
  | .frobenius2 p β => blk2 p β 0 (un2P I2.conj)
  | .sparseMul p β ξ => blk2 p β ξ sparse014P
  | .lift .two p _ _ => liftFpBlk p
  | .lift .six p β ξ => blk2 p β ξ lift6P
  | .lift .twelve p β ξ => blk2 p β ξ lift12P
  | .proj2 p _ i => proj2Blk p i
  | .proj6 p β ξ i => blk2 p β ξ (proj6P i)
  | .proj12 p β ξ i => blk2 p β ξ (proj12P i)
  | .constFp p c => .var ⟨.fConst p c, rfl, .nil⟩ (.ret (.cons .here .nil))

/-- **The lowering of the tower dialect to `fieldDialect`.** -/
def towerToField : MultiBlockLoweringData towerDialect fieldDialect where
  mapTys := towerMapTys
  lowerOp := towerLowerOp

end Lowering

/-! ## 13. Block squares at the base ops -/

section Squares

/-- The block square of `towerToField` at one op. -/
def OpSquare (op : TowerOp) : Prop :=
  ∀ vals : Ctxt.Valuation (DialectSignature.sig (d := towerDialect) op),
    (towerToField.lowerOp op).denote (flatVal towerEnc vals)
      = towerEnc (DialectDenote.denote (d := towerDialect) op vals)

theorem opSquare_add2 (p : Nat) (β ξ : Int) : OpSquare (.add .two p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_sub2 (p : Nat) (β ξ : Int) : OpSquare (.sub .two p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_mul2 (p : Nat) (β ξ : Int) : OpSquare (.mul .two p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_neg2 (p : Nat) (β ξ : Int) : OpSquare (.neg .two p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_square2 (p : Nat) (β ξ : Int) : OpSquare (.square .two p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_mulByNonResidue2 (p : Nat) (β ξ : Int) :
    OpSquare (.mulByNonResidue .two p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_frobenius2 (p : Nat) (β : Int) : OpSquare (.frobenius2 p β) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β 0 _ _).trans rfl

theorem opSquare_lift2 (p : Nat) (β ξ : Int) : OpSquare (.lift .two p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  show (liftFpBlk p).denote (HVector.cons x HVector.nil) = _
  refine emitVecT_denote ![x] 2 _ _ _ _ _ (fun i => by fin_cases i; rfl) ?_
  intro _ _ V' ws _ hws
  show HVector.cons ((ws 0).lookup V') (HVector.cons ((ws 1).lookup V') HVector.nil) = _
  rw [hws 0, hws 1]
  rfl

theorem opSquare_proj2 (p : Nat) (β : Int) (i : Fin 2) : OpSquare (.proj2 p β i) := by
  rintro (_ | ⟨x, _ | _⟩)
  fin_cases i <;> rfl

theorem opSquare_constFp (p : Nat) (c : ZMod p) : OpSquare (.constFp p c) := by
  rintro (_ | _)
  rfl

theorem mul6P_eval {p : Nat} (β ξ : Int) (xs : Fin 6 → Fp2Val p) :
    mul6P.eval (ev2 p β ξ) xs = get6 (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p)
      ⟨xs 0, xs 1, xs 2⟩ ⟨xs 3, xs 4, xs 5⟩) := by
  have h : mul6P.eval (ev2 p β ξ) xs =
      ![Fp6Val.mulXiBeta (β : ZMod p) (ξ : ZMod p)
            (Fp2Val.mulBeta (β : ZMod p) (xs 1 + xs 2) (xs 4 + xs 5)
              - Fp2Val.mulBeta (β : ZMod p) (xs 1) (xs 4)
              - Fp2Val.mulBeta (β : ZMod p) (xs 2) (xs 5))
          + Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 3),
        Fp2Val.mulBeta (β : ZMod p) (xs 0 + xs 1) (xs 3 + xs 4)
            - Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 3)
            - Fp2Val.mulBeta (β : ZMod p) (xs 1) (xs 4)
          + Fp6Val.mulXiBeta (β : ZMod p) (ξ : ZMod p) (Fp2Val.mulBeta (β : ZMod p) (xs 2) (xs 5)),
        Fp2Val.mulBeta (β : ZMod p) (xs 0 + xs 2) (xs 3 + xs 5)
            - Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 3)
            + Fp2Val.mulBeta (β : ZMod p) (xs 1) (xs 4)
          - Fp2Val.mulBeta (β : ZMod p) (xs 2) (xs 5)] := by
    funext j; fin_cases j <;> rfl
  rw [h]
  funext j
  fin_cases j <;> ext <;>
    simp [get6, Fp6Val.mulBeta, Fp6Val.mulXiBeta, Fp2Val.mulBeta] <;> ring

theorem opSquare_mul6 (p : Nat) (β ξ : Int) : OpSquare (.mul .six p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  refine (blk2_denote β ξ _ _).trans ?_
  rw [mul6P_eval]
  rfl

theorem sq6P_eval {p : Nat} (β ξ : Int) (xs : Fin 3 → Fp2Val p) :
    sq6P.eval (ev2 p β ξ) xs = get6 (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p)
      ⟨xs 0, xs 1, xs 2⟩ ⟨xs 0, xs 1, xs 2⟩) := by
  have h : sq6P.eval (ev2 p β ξ) xs =
      ![Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 0)
          + Fp6Val.mulXiBeta (β : ZMod p) (ξ : ZMod p)
            (Fp2Val.mulBeta (β : ZMod p) (xs 1) (xs 2) + Fp2Val.mulBeta (β : ZMod p) (xs 1) (xs 2)),
        (Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 1) + Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 1))
          + Fp6Val.mulXiBeta (β : ZMod p) (ξ : ZMod p) (Fp2Val.mulBeta (β : ZMod p) (xs 2) (xs 2)),
        (Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 1) + Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 1))
            + Fp2Val.mulBeta (β : ZMod p) (xs 0 - xs 1 + xs 2) (xs 0 - xs 1 + xs 2)
            + (Fp2Val.mulBeta (β : ZMod p) (xs 1) (xs 2) + Fp2Val.mulBeta (β : ZMod p) (xs 1) (xs 2))
            - Fp2Val.mulBeta (β : ZMod p) (xs 0) (xs 0)
          - Fp2Val.mulBeta (β : ZMod p) (xs 2) (xs 2)] := by
    funext j; fin_cases j <;> rfl
  rw [h]
  funext j
  fin_cases j <;> ext <;>
    simp [get6, Fp6Val.mulBeta, Fp6Val.mulXiBeta, Fp2Val.mulBeta] <;> ring

theorem run6_denote {p : Nat} (β ξ : Int) {n : Nat} {Γ : Ctxt fieldDialect}
    {ts : List FieldTy} (P : SLP I2 n 3) (e : Fin n → F2 p Γ)
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F6 p Γ' → MRC Γ' ts)
    (V : Ctxt.Valuation Γ) (R : ListDenote ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ') (z : F6 p Γ'),
      Preserves r V V' →
      z.val V' = (let ys := P.eval (ev2 p β ξ) (fun i => (e i).val V); ⟨ys 0, ys 1, ys 2⟩) →
      (kk r z).denote V' = R) :
    (run6 β ξ P e kk).denote V = R :=
  SLP.emit_denote (B := F2 p) (fun x V => x.val V) (fun r x => x.ren r) (ev2 p β ξ) (em2 p β ξ)
    (fun r V V' b h => F2.val_ren r V V' b h) (I2.emit_sound β ξ) P e _ V R
    fun r V' zs hr hzs => hk r V' _ hr (by
      show (⟨(zs 0).val V', (zs 1).val V', (zs 2).val V'⟩ : Fp6Val p) = _
      rw [hzs 0, hzs 1, hzs 2])

/-- **The `Fp6` instructions are sound.** -/
theorem I6.emit_sound {p : Nat} (β ξ : Int) : I6Sound p β ξ := by
  intro k Γ ts ins env kk V R hk
  cases ins with
  | add i j => exact run6_denote β ξ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans rfl)
  | sub i j => exact run6_denote β ξ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans rfl)
  | neg i => exact run6_denote β ξ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans rfl)
  | mulV i => exact run6_denote β ξ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans rfl)
  | mul i j =>
    refine run6_denote β ξ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    simp only [mul6P_eval]
    rfl
  | sq i =>
    refine run6_denote β ξ _ _ kk V R fun r V' z hr hz => hk r V' z hr (hz.trans ?_)
    simp only [sq6P_eval]
    rfl

/-- The Karatsuba identity for `Fp6Val.mulBeta`. -/
theorem Fp6Val.mulBeta_karatsuba {p : Nat} (β ξ0 : ZMod p) (a b c d : Fp6Val p) :
    Fp6Val.sub (Fp6Val.sub (Fp6Val.mulBeta β ξ0 (Fp6Val.add a b) (Fp6Val.add c d))
        (Fp6Val.mulBeta β ξ0 a c)) (Fp6Val.mulBeta β ξ0 b d)
      = Fp6Val.add (Fp6Val.mulBeta β ξ0 a d) (Fp6Val.mulBeta β ξ0 b c) := by
  ext <;> simp [Fp6Val.mulBeta, Fp6Val.add, Fp6Val.sub, Fp6Val.mulXiBeta, Fp2Val.mulBeta] <;>
    ring

theorem mul12P_eval {p : Nat} (β ξ : Int) (xs : Fin 4 → Fp6Val p) :
    mul12P.eval (ev6 p β ξ) xs = ![
      (Fp12Val.mulBeta (β : ZMod p) (ξ : ZMod p) ⟨xs 0, xs 1⟩ ⟨xs 2, xs 3⟩).c0,
      (Fp12Val.mulBeta (β : ZMod p) (ξ : ZMod p) ⟨xs 0, xs 1⟩ ⟨xs 2, xs 3⟩).c1] := by
  have h : mul12P.eval (ev6 p β ξ) xs = ![
      Fp6Val.add (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 0) (xs 2))
        (Fp12Val.mulByVBeta (β : ZMod p) (ξ : ZMod p)
          (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 1) (xs 3))),
      Fp6Val.sub (Fp6Val.sub (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p)
          (Fp6Val.add (xs 0) (xs 1)) (Fp6Val.add (xs 2) (xs 3)))
          (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 0) (xs 2)))
        (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 1) (xs 3))] := by
    funext j; fin_cases j <;> rfl
  rw [h]
  funext j
  fin_cases j
  · rfl
  · exact Fp6Val.mulBeta_karatsuba _ _ _ _ _ _

theorem sq12P_eval {p : Nat} (β ξ : Int) (xs : Fin 2 → Fp6Val p) :
    sq12P.eval (ev6 p β ξ) xs = ![
      (Fp12Val.mulBeta (β : ZMod p) (ξ : ZMod p) ⟨xs 0, xs 1⟩ ⟨xs 0, xs 1⟩).c0,
      (Fp12Val.mulBeta (β : ZMod p) (ξ : ZMod p) ⟨xs 0, xs 1⟩ ⟨xs 0, xs 1⟩).c1] := by
  have h : sq12P.eval (ev6 p β ξ) xs = ![
      Fp6Val.sub (Fp6Val.sub (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (Fp6Val.add (xs 0) (xs 1))
            (Fp6Val.add (xs 0) (Fp12Val.mulByVBeta (β : ZMod p) (ξ : ZMod p) (xs 1))))
          (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 0) (xs 1)))
        (Fp12Val.mulByVBeta (β : ZMod p) (ξ : ZMod p)
          (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 0) (xs 1))),
      Fp6Val.add (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 0) (xs 1))
        (Fp6Val.mulBeta (β : ZMod p) (ξ : ZMod p) (xs 0) (xs 1))] := by
    funext j; fin_cases j <;> rfl
  rw [h]
  funext j
  fin_cases j <;> ext <;>
    simp [Fp12Val.mulBeta, Fp12Val.mulByVBeta, Fp6Val.mulBeta, Fp6Val.add, Fp6Val.sub,
      Fp6Val.mulXiBeta, Fp2Val.mulBeta] <;> ring

theorem add12P_eval {p : Nat} (β ξ : Int) (xs : Fin 4 → Fp6Val p) :
    add12P.eval (ev6 p β ξ) xs = ![(Fp12Val.add ⟨xs 0, xs 1⟩ ⟨xs 2, xs 3⟩).c0,
      (Fp12Val.add ⟨xs 0, xs 1⟩ ⟨xs 2, xs 3⟩).c1] := by
  funext j; fin_cases j <;> rfl

theorem sub12P_eval {p : Nat} (β ξ : Int) (xs : Fin 4 → Fp6Val p) :
    sub12P.eval (ev6 p β ξ) xs = ![(Fp12Val.sub ⟨xs 0, xs 1⟩ ⟨xs 2, xs 3⟩).c0,
      (Fp12Val.sub ⟨xs 0, xs 1⟩ ⟨xs 2, xs 3⟩).c1] := by
  funext j; fin_cases j <;> rfl

theorem neg12P_eval {p : Nat} (β ξ : Int) (xs : Fin 2 → Fp6Val p) :
    neg12P.eval (ev6 p β ξ) xs = ![(neg12 ⟨xs 0, xs 1⟩).c0, (neg12 ⟨xs 0, xs 1⟩).c1] := by
  funext j; fin_cases j <;> rfl

theorem opSquare_add12 (p : Nat) (β ξ : Int) : OpSquare (.add .twelve p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  refine (blk6_denote β ξ (I6.emit_sound β ξ) _ _).trans ?_
  rw [add12P_eval]
  rfl

theorem opSquare_sub12 (p : Nat) (β ξ : Int) : OpSquare (.sub .twelve p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  refine (blk6_denote β ξ (I6.emit_sound β ξ) _ _).trans ?_
  rw [sub12P_eval]
  rfl

theorem opSquare_neg12 (p : Nat) (β ξ : Int) : OpSquare (.neg .twelve p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  refine (blk6_denote β ξ (I6.emit_sound β ξ) _ _).trans ?_
  rw [neg12P_eval]
  rfl

/-- `blk6_denote` at given register values. -/
theorem blk6_denote_of {p : Nat} (β ξ : Int) {k : Nat} (P : SLP I6 k 2)
    (V : Ctxt.Valuation (List.replicate (2 * (3 * k)) (FieldTy.fp p) : Ctxt fieldDialect))
    (xs : Fin k → Fp6Val p) (hV : ∀ i, (inEnv6 p k i).val V = xs i) :
    (blk6 p β ξ P).denote V = encRegs p 6 (flat12v (P.eval (ev6 p β ξ) xs)) := by
  rw [blk6_denote β ξ (I6.emit_sound β ξ), funext hV]

theorem opSquare_mul12 (p : Nat) (β ξ : Int) : OpSquare (.mul .twelve p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  refine (blk6_denote_of β ξ _ _ ![x.c0, x.c1, y.c0, y.c1]
    fun i => by fin_cases i <;> rfl).trans ?_
  rw [mul12P_eval]
  rfl

theorem opSquare_square12 (p : Nat) (β ξ : Int) : OpSquare (.square .twelve p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  refine (blk6_denote_of β ξ _ _ ![x.c0, x.c1] fun i => by fin_cases i <;> rfl).trans ?_
  rw [sq12P_eval]
  rfl

@[simp] theorem fp2Val_zero_c0 {p : Nat} : (0 : Fp2Val p).c0 = 0 := rfl
@[simp] theorem fp2Val_zero_c1 {p : Nat} : (0 : Fp2Val p).c1 = 0 := rfl

theorem sparse014P_eval {p : Nat} (β ξ : Int) (xs : Fin 9 → Fp2Val p) :
    sparse014P.eval (ev2 p β ξ) xs =
      let R := Fp12Val.mulBeta (β : ZMod p) (ξ : ZMod p) ⟨⟨xs 0, xs 1, xs 2⟩, ⟨xs 3, xs 4, xs 5⟩⟩
        (line014 (xs 6) (xs 7) (xs 8))
      ![R.c0.a0, R.c0.a1, R.c0.a2, R.c1.a0, R.c1.a1, R.c1.a2] := by
  have h : sparse014P.eval (ev2 p β ξ) xs =
      let M := Fp2Val.mulBeta (p := p) (β : ZMod p)
      let Xi := Fp6Val.mulXiBeta (p := p) (β : ZMod p) (ξ : ZMod p)
      let r9 := M (xs 0) (xs 6)
      let r10 := M (xs 1) (xs 7)
      let aa0 := Xi (M (xs 2) (xs 7)) + r9
      let aa1 := M (xs 6 + xs 7) (xs 0 + xs 1) - r9 - r10
      let aa2 := M (xs 2) (xs 6) + r10
      let bb0 := Xi (M (xs 5) (xs 8))
      let bb1 := M (xs 3) (xs 8)
      let bb2 := M (xs 4) (xs 8)
      let o := xs 7 + xs 8
      let y0 := xs 3 + xs 0
      let y1 := xs 4 + xs 1
      let y2 := xs 5 + xs 2
      let r29 := M y0 (xs 6)
      let r30 := M y1 o
      let z0 := Xi (M y2 o) + r29
      let z1 := M (xs 6 + o) (y0 + y1) - r29 - r30
      let z2 := M y2 (xs 6) + r30
      ![Xi bb2 + aa0, bb0 + aa1, bb1 + aa2, z0 - aa0 - bb0, z1 - aa1 - bb1, z2 - aa2 - bb2] := by
    funext j; fin_cases j <;> rfl
  rw [h]
  funext j
  fin_cases j <;> ext <;>
    simp [Fp12Val.mulBeta, Fp12Val.mulByVBeta, Fp6Val.mulBeta, Fp6Val.add, Fp6Val.mulXiBeta,
      Fp2Val.mulBeta, line014] <;> ring

/-- `blk2_denote` at given register values. -/
theorem blk2_denote_of {p : Nat} (β ξ : Int) {k m : Nat} (P : SLP I2 k m)
    (V : Ctxt.Valuation (List.replicate (2 * k) (FieldTy.fp p) : Ctxt fieldDialect))
    (xs : Fin k → Fp2Val p) (hV : ∀ i, (inEnv2 p k i).val V = xs i) :
    (blk2 p β ξ P).denote V = encRegs p m (P.eval (ev2 p β ξ) xs) := by
  rw [blk2_denote, funext hV]

theorem opSquare_sparseMul (p : Nat) (β ξ : Int) : OpSquare (.sparseMul p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨c0, _ | ⟨c1, _ | ⟨c4, _ | _⟩⟩⟩⟩)
  refine (blk2_denote_of β ξ _ _
    ![x.c0.a0, x.c0.a1, x.c0.a2, x.c1.a0, x.c1.a1, x.c1.a2, c0, c1, c4]
    fun i => by fin_cases i <;> rfl).trans ?_
  rw [sparse014P_eval]
  rfl

theorem opSquare_square6 (p : Nat) (β ξ : Int) : OpSquare (.square .six p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  refine (blk2_denote β ξ _ _).trans ?_
  rw [sq6P_eval]
  rfl

theorem opSquare_add6 (p : Nat) (β ξ : Int) : OpSquare (.add .six p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_sub6 (p : Nat) (β ξ : Int) : OpSquare (.sub .six p β ξ) := by
  rintro (_ | ⟨x, _ | ⟨y, _ | _⟩⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_neg6 (p : Nat) (β ξ : Int) : OpSquare (.neg .six p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_mulByNonResidue6 (p : Nat) (β ξ : Int) :
    OpSquare (.mulByNonResidue .six p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_mulByNonResidue12 (p : Nat) (β ξ : Int) :
    OpSquare (.mulByNonResidue .twelve p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_lift6 (p : Nat) (β ξ : Int) : OpSquare (.lift .six p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_lift12 (p : Nat) (β ξ : Int) : OpSquare (.lift .twelve p β ξ) := by
  rintro (_ | ⟨x, _ | _⟩)
  exact (blk2_denote β ξ _ _).trans rfl

theorem opSquare_proj6 (p : Nat) (β ξ : Int) (i : Fin 3) : OpSquare (.proj6 p β ξ i) := by
  rintro (_ | ⟨x, _ | _⟩)
  refine (blk2_denote β ξ _ _).trans ?_
  fin_cases i <;> rfl

theorem opSquare_proj12 (p : Nat) (β ξ : Int) (i : Fin 2) : OpSquare (.proj12 p β ξ i) := by
  rintro (_ | ⟨x, _ | _⟩)
  refine (blk2_denote β ξ _ _).trans ?_
  fin_cases i <;> rfl

/-- The block square holds at every op. -/
theorem opSquare_all : ∀ op : TowerOp, OpSquare op
  | .add .two p β ξ => opSquare_add2 p β ξ
  | .add .six p β ξ => opSquare_add6 p β ξ
  | .add .twelve p β ξ => opSquare_add12 p β ξ
  | .sub .two p β ξ => opSquare_sub2 p β ξ
  | .sub .six p β ξ => opSquare_sub6 p β ξ
  | .sub .twelve p β ξ => opSquare_sub12 p β ξ
  | .neg .two p β ξ => opSquare_neg2 p β ξ
  | .neg .six p β ξ => opSquare_neg6 p β ξ
  | .neg .twelve p β ξ => opSquare_neg12 p β ξ
  | .mul .two p β ξ => opSquare_mul2 p β ξ
  | .mul .six p β ξ => opSquare_mul6 p β ξ
  | .mul .twelve p β ξ => opSquare_mul12 p β ξ
  | .square .two p β ξ => opSquare_square2 p β ξ
  | .square .six p β ξ => opSquare_square6 p β ξ
  | .square .twelve p β ξ => opSquare_square12 p β ξ
  | .mulByNonResidue .two p β ξ => opSquare_mulByNonResidue2 p β ξ
  | .mulByNonResidue .six p β ξ => opSquare_mulByNonResidue6 p β ξ
  | .mulByNonResidue .twelve p β ξ => opSquare_mulByNonResidue12 p β ξ
  | .frobenius2 p β => opSquare_frobenius2 p β
  | .sparseMul p β ξ => opSquare_sparseMul p β ξ
  | .lift .two p β ξ => opSquare_lift2 p β ξ
  | .lift .six p β ξ => opSquare_lift6 p β ξ
  | .lift .twelve p β ξ => opSquare_lift12 p β ξ
  | .proj2 p β i => opSquare_proj2 p β i
  | .proj6 p β ξ i => opSquare_proj6 p β ξ i
  | .proj12 p β ξ i => opSquare_proj12 p β ξ i
  | .constFp p c => opSquare_constFp p c

/-- **Block square of `towerToField`** at every op. -/
theorem towerToField_blockSquare : towerToField.BlockSquare towerEnc (fun _ => True) :=
  fun e _ vals => opSquare_all e.op vals

/-- **Fundamental theorem of `towerToField`.** Every program of the tower dialect lowers
    to a `fieldDialect` program that maps the flattened encoding of the inputs to the
    encoding of the value. -/
theorem towerToField_fundamental {Γ : Ctxt towerDialect} {t : TowerTy}
    (c : Com towerDialect Γ t) (V : Ctxt.Valuation Γ) :
    (towerToField.lowerMulti c).denote (flatVal towerEnc V) = towerEnc (c.denote V) :=
  towerToField.multiFundamental_on towerEnc _ towerToField_blockSquare c
    (coveredCom_of_forall _ (fun _ => trivial) c) V

end Squares

end CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect
