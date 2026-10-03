/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

/-!
# `fieldDialect → jasminDialect` over four 64-bit limbs in Montgomery form

For a modulus record `P : FieldLimbs.Mont4.Mont4Prime`, the multi-value block
lowering from `fieldDialect` to `jasminDialect` that represents every field type by
four 64-bit registers. A value of `fp P.p` is carried by the limbs of its
Montgomery form (`FieldLimbs.Mont4.enc`); values of other types are carried by zero
limbs.

| source op at `P.p` | target block |
|---|---|
| `fAdd` | `addBlk x y` |
| `fSub` | `subBlk x y` |
| `fNeg` | `negBlk x` |
| `fMul` | `mulBlk x y` |
| `fInv` | `invBlk x`, the Montgomery power `x^(p-2)` |
| `fieldDouble` | `addBlk x x` |
| `fieldSquare` | `mulBlk x x` |
| `fConst c` | `constBlk (c · 2^256).val` |
| `fCopy` | `Curve25519.copyBlk x` |

Every other operation, and every operation at another modulus, lowers to the zero
limbs; the coverage predicate `GoodV` excludes them, and admits `fInv` only at a prime
modulus.

## Main definitions

* `mapTysL`, `encL`: the type map and the encoding.
* `lowerOpL`: the per-operation blocks; `loweringL`: the lowering
  `FieldToJasminLimbs.loweringOf (lowerOpL P)` at four limbs.
* `GoodM`: addition, multiplication, constants and copies at `P.p`.
* `GoodV`: `GoodM`, subtraction, negation, doubling, squaring, and inversion at a
  prime `P.p`.

## Main results

* `nv_encX`, `nv_encY`: the operand limb variables of a flattened valuation carry the
  Montgomery forms.
* `blockSquareV`, `blockSquareL`: the block square of `loweringL` for `GoodV` and
  `GoodM` expressions.
* `fieldToJasminLimbsMont4_denoteV`: for every `GoodV`-covered program `c`,
  `(loweringL.lowerMulti c).denote (flatVal encL V) = encL (c.denote V)`;
  `fieldToJasminLimbsMont4_denote` is its restriction to `GoodM`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 MC nv nv_cons nv_nil R4 limbsOf copyBlk)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (loweringOf)

variable (P : Mont4Prime)

/-! ## 1. Operand variables -/

/-- The context `Γ` preceded by the four limbs of an operand. -/
abbrev C4 (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := R4 ++ Γ

/-- Limb `0` of the first operand. -/
abbrev xv₀ {Γ : Ctxt jasminDialect} : Var (C4 Γ) w64 := .here
/-- Limb `1` of the first operand. -/
abbrev xv₁ {Γ : Ctxt jasminDialect} : Var (C4 Γ) w64 := .there .here
/-- Limb `2` of the first operand. -/
abbrev xv₂ {Γ : Ctxt jasminDialect} : Var (C4 Γ) w64 := .there (.there .here)
/-- Limb `3` of the first operand. -/
abbrev xv₃ {Γ : Ctxt jasminDialect} : Var (C4 Γ) w64 := .there (.there (.there .here))

/-- Shift a variable past the four limbs of the first operand. -/
abbrev past4 {Γ : Ctxt jasminDialect} (v : Var Γ w64) : Var (C4 Γ) w64 :=
  .there (.there (.there (.there v)))

theorem nv_limbsOf {Γ : Ctxt jasminDialect} (n : Nat) (hn : n < 2 ^ 256)
    (B : Valuation Γ) : nv (hvAppend (limbsOf n) B) [xv₀, xv₁, xv₂, xv₃] = n := by
  show (BitVec.ofNat 64 n).toNat + 2 ^ 64 * ((BitVec.ofNat 64 (n / 2 ^ 64)).toNat
    + 2 ^ 64 * ((BitVec.ofNat 64 (n / 2 ^ 128)).toNat
    + 2 ^ 64 * ((BitVec.ofNat 64 (n / 2 ^ 192)).toNat + 2 ^ 64 * 0))) = n
  simp only [BitVec.toNat_ofNat]
  omega

theorem nv_encX {Γ : Ctxt jasminDialect} (x : ZMod P.p) (B : Valuation Γ) :
    nv (hvAppend (enc P x) B) [xv₀, xv₁, xv₂, xv₃] = (x * R P).val :=
  nv_limbsOf _ (val_lt_two_pow P _) B

theorem nv_encY {Γ : Ctxt jasminDialect} (A : ListDenote R4) (y : ZMod P.p)
    (B : Valuation Γ) :
    nv (hvAppend A (hvAppend (enc P y) B))
      [past4 xv₀, past4 xv₁, past4 xv₂, past4 xv₃] = (y * R P).val := by
  rcases A with _ | ⟨a₀, _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | _⟩⟩⟩⟩
  exact nv_encX P y B

/-! ## 2. The lowering -/

/-- Every field type is carried by four 64-bit registers. -/
@[reducible] def mapTysL : fieldDialect.Ty → List jasminDialect.Ty := fun _ => R4

/-- The encoding: `enc P` on `fp P.p`, and zero limbs on every other type. -/
def encL : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL t)
  | .fp q, x => if h : q = P.p then enc P (cast (congrArg ZMod h) x) else limbsOf 0
  | .fp2 _, _ => limbsOf 0
  | .fp6 _, _ => limbsOf 0
  | .fp12 _, _ => limbsOf 0

theorem encL_fp (x : ZMod P.p) : encL P (t := .fp P.p) x = enc P x := by
  simp only [encL, dite_true]
  rfl

/-- The block of each field operation at `P.p`: addition, subtraction, negation,
    multiplication, inversion, doubling, squaring, constants and copies; the zero limbs
    otherwise. -/
def lowerOpL : (op : fieldDialect.Op) →
    MultiReturnCom jasminDialect (ctxFlat mapTysL (DialectSignature.sig op))
      (mapTysL (DialectSignature.ret op))
  | .fAdd q => if q = P.p then
      addBlk P xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .fSub q => if q = P.p then
      subBlk P xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .fNeg q => if q = P.p then negBlk P xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .fMul q => if q = P.p then
      mulBlk P xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .fInv q => if q = P.p then invBlk P xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .fConst q c => if h : q = P.p then constBlk ((cast (congrArg ZMod h) c * R P).val)
    else constBlk 0
  | .fCopy q => if q = P.p then copyBlk xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .fieldDouble q => if q = P.p then addBlk P xv₀ xv₁ xv₂ xv₃ xv₀ xv₁ xv₂ xv₃
    else constBlk 0
  | .fieldSquare q => if q = P.p then mulBlk P xv₀ xv₁ xv₂ xv₃ xv₀ xv₁ xv₂ xv₃
    else constBlk 0
  | .ext2Mul _ | .ext2Add _ | .ext2Sub _ | .frobenius2 _ | .ext6Mul _ _ | .ext6Add _
  | .ext6Sub _ | .ext12Mul _ _ | .ext12Add _ | .ext12Sub _ => constBlk 0

/-- The multi-value lowering `fieldDialect → jasminDialect` over four limbs in
    Montgomery form: the generic limb lowering with the blocks `lowerOpL P`. -/
def loweringL : MultiBlockLoweringData fieldDialect jasminDialect :=
  loweringOf (n := 4) (lowerOpL P)

/-- The operations covered at `P.p`: addition, multiplication, constants and copies. -/
def GoodM {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) : Prop :=
  e.op = .fAdd P.p ∨ e.op = .fMul P.p ∨ (∃ c : ZMod P.p, e.op = .fConst P.p c) ∨
    e.op = .fCopy P.p

/-- The operations covered at `P.p`: those of `GoodM`, subtraction, negation, doubling,
    squaring, and inversion when `P.p` is prime. -/
def GoodV {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) : Prop :=
  GoodM P e ∨ e.op = .fSub P.p ∨ e.op = .fNeg P.p ∨ e.op = .fieldDouble P.p ∨
    e.op = .fieldSquare P.p ∨ (P.p.Prime ∧ e.op = .fInv P.p)

/-! ## 3. The block square and the fundamental theorem -/

/-- **The block square of `loweringL` on `GoodV`.** -/
theorem blockSquareV : (loweringL P).BlockSquare (fun {t} x => encL P (t := t) x) (GoodV P) := by
  intro Γ t e hg vals
  obtain ⟨op, h, args⟩ := e
  rcases hg with (hop | hop | ⟨c, hop⟩ | hop) | hop | hop | hop | hop | ⟨hp, hop⟩ <;> subst hop
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fAdd P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fAddF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact addBlk_denote P _ _ _ _ _ _ _ _ _ a b (nv_encX P a _) (nv_encY P _ b _)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fMul P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fMulF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact mulBlk_denote P _ _ _ _ _ _ _ _ _ a b (nv_encX P a _) (nv_encY P _ b _)
  · obtain ⟨⟩ := vals
    show (lowerOpL P (.fConst P.p c)).denote .nil = encL P (t := .fp P.p) (fConstF c)
    rw [encL_fp, lowerOpL, dif_pos rfl]
    exact constBlk_denote _ _
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fCopy P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fCopyF a)
    rw [encL_fp, lowerOpL, if_pos rfl, copyBlk_denote, nv_encX]
    rfl
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fSub P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fSubF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact subBlk_denote_enc P _ _ _ _ _ _ _ _ _ a b (nv_encX P a _) (nv_encY P _ b _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fNeg P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fNegF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact negBlk_denote_enc P _ _ _ _ _ a (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fieldDouble P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fDoubleF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact addBlk_denote P _ _ _ _ _ _ _ _ _ a a (nv_encX P a _) (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fieldSquare P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fSquareF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact mulBlk_denote P _ _ _ _ _ _ _ _ _ a a (nv_encX P a _) (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fInv P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fInvF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact invBlk_denote_inv P hp _ _ _ _ _ a (nv_encX P a _)

/-- **The block square of `loweringL` on `GoodM`.** -/
theorem blockSquareL : (loweringL P).BlockSquare (fun {t} x => encL P (t := t) x) (GoodM P) := by
  intro Γ t e hg
  exact blockSquareV P e (Or.inl hg)

/-- **Denotation preservation of `fieldDialect → jasminDialect` over four limbs in
    Montgomery form.** A `GoodV`-covered field program lowers to a multi-result
    jasmin program that maps the limbs of its inputs to the limbs of its result. -/
theorem fieldToJasminLimbsMont4_denoteV {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ) :
    ((loweringL P).lowerMulti c).denote (flatVal (fun {t} x => encL P (t := t) x) V)
      = encL P (c.denote V) :=
  (loweringL P).multiFundamental_on (fun {t} x => encL P (t := t) x) (GoodV P)
    (blockSquareV P) c hc V

/-- Denotation preservation on a `GoodM`-covered field program. -/
theorem fieldToJasminLimbsMont4_denote {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodM P) c) (V : Valuation Γ) :
    ((loweringL P).lowerMulti c).denote (flatVal (fun {t} x => encL P (t := t) x) V)
      = encL P (c.denote V) :=
  (loweringL P).multiFundamental_on (fun {t} x => encL P (t := t) x) (GoodM P)
    (blockSquareL P) c hc V

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4
