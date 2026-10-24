/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

/-!
# `fieldDialect → jasminDialect` over four 64-bit limbs at `p = 2^255 - 19`

The multi-value block lowering from `fieldDialect` to `jasminDialect` that
represents every field type by four 64-bit registers. A value of `fp p` with
`p = 2^255 - 19` is carried by the limbs of its canonical representative
(`FieldLimbs.Curve25519.enc`); values of other types are carried by zero limbs.

| source op at `p` | target block |
|---|---|
| `fAdd`, `fieldDouble` | `addBlk x y`, `addBlk x x` |
| `fSub` | `subBlk x y` |
| `fNeg` | `negBlk x` |
| `fMul`, `fieldSquare` | `mulBlk x y`, `sqrBlk x` |
| `fConst p c` | `constBlk c` |
| `fCopy` | `copyBlk x` |

Every other operation, and every operation at a modulus other than `p`, lowers to
the zero limbs; the coverage predicate `GoodL` excludes them.

## Main definitions

* `mapTysL`, `encL`: the type map and the encoding.
* `lowerOpL`: the per-operation blocks; `loweringL`: the lowering
  `FieldToJasminLimbs.loweringOf lowerOpL` at four limbs.
* `GoodL`: the operations covered at `p`.
* `mulAddProg`: the covered source program `x * y + z`.

## Main results

* `nv_encX`, `nv_encY`: the operand limb variables of a flattened valuation carry the
  canonical representatives.
* `blockSquareL`: the block square of `loweringL` for `GoodL` expressions.
* `fieldToJasminLimbs_denote`: for every `GoodL`-covered program `c`,
  `(loweringL.lowerMulti c).denote (flatVal encL V) = encL (c.denote V)`.
* `mulAddProg_lowered`: the lowered `x * y + z` maps the limbs of `x`, `y`, `z` to the
  limbs of `x * y + z`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs25519

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (loweringOf)

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

theorem nv_encX {Γ : Ctxt jasminDialect} (x : ZMod p25519) (B : Valuation Γ) :
    nv (hvAppend (enc x) B) [xv₀, xv₁, xv₂, xv₃] = x.val := by
  have hx : x.val < 2 ^ 255 - 19 := ZMod.val_lt x
  show (BitVec.ofNat 64 x.val).toNat + 2 ^ 64 * ((BitVec.ofNat 64 (x.val / 2 ^ 64)).toNat
    + 2 ^ 64 * ((BitVec.ofNat 64 (x.val / 2 ^ 128)).toNat
    + 2 ^ 64 * ((BitVec.ofNat 64 (x.val / 2 ^ 192)).toNat + 2 ^ 64 * 0))) = x.val
  simp only [BitVec.toNat_ofNat]
  omega

theorem nv_encY {Γ : Ctxt jasminDialect} (A : ListDenote R4) (y : ZMod p25519)
    (B : Valuation Γ) :
    nv (hvAppend A (hvAppend (enc y) B))
      [past4 xv₀, past4 xv₁, past4 xv₂, past4 xv₃] = y.val := by
  rcases A with _ | ⟨a₀, _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | _⟩⟩⟩⟩
  exact nv_encX y B

/-! ## 2. The lowering -/

/-- Every field type is carried by four 64-bit registers. -/
@[reducible] def mapTysL : fieldDialect.Ty → List jasminDialect.Ty := fun _ => R4

/-- The encoding: `enc` on `fp (2^255 - 19)`, and zero limbs on every other type. -/
def encL : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL t)
  | .fp q, x => if h : q = p25519 then enc (cast (congrArg ZMod h) x) else limbsOf 0
  | .fp2 _, _ => limbsOf 0
  | .fp6 _, _ => limbsOf 0
  | .fp12 _, _ => limbsOf 0

theorem encL_fp (x : ZMod p25519) : encL (t := .fp p25519) x = enc x := by
  simp only [encL, dite_true]
  rfl

/-- The block of each field operation. -/
def lowerOpL : (op : fieldDialect.Op) →
    MultiReturnCom jasminDialect (ctxFlat mapTysL (DialectSignature.sig op))
      (mapTysL (DialectSignature.ret op))
  | .fAdd q => if q = p25519 then
      addBlk xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .fSub q => if q = p25519 then
      subBlk xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .fNeg q => if q = p25519 then negBlk xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .fMul q => if q = p25519 then
      mulBlk xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .fConst q c => if h : q = p25519 then constBlk (cast (congrArg ZMod h) c) else constBlk 0
  | .fCopy q => if q = p25519 then copyBlk xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .fieldDouble q => if q = p25519 then addBlk xv₀ xv₁ xv₂ xv₃ xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .fieldSquare q => if q = p25519 then sqrBlk xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .fInv _ => constBlk 0

/-- The multi-value lowering `fieldDialect → jasminDialect` over four limbs: the generic
    limb lowering with the blocks `lowerOpL`. -/
def loweringL : MultiBlockLoweringData fieldDialect jasminDialect :=
  loweringOf (n := 4) lowerOpL

/-- The operations covered at `2^255 - 19`: add, sub, neg, mul, constants, copy,
    doubling and squaring. -/
def GoodL {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) : Prop :=
  e.op = .fAdd p25519 ∨ e.op = .fSub p25519 ∨ e.op = .fNeg p25519 ∨ e.op = .fMul p25519 ∨
    (∃ c : ZMod p25519, e.op = .fConst p25519 c) ∨ e.op = .fCopy p25519 ∨
    e.op = .fieldDouble p25519 ∨ e.op = .fieldSquare p25519

/-! ## 3. The block square and the fundamental theorem -/

/-- **The block square of `loweringL`.** -/
theorem blockSquareL : loweringL.BlockSquare (fun {t} x => encL (t := t) x) GoodL := by
  intro Γ t e hg vals
  obtain ⟨op, h, args⟩ := e
  rcases hg with hop | hop | hop | hop | ⟨c, hop⟩ | hop | hop | hop <;> subst hop
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL (.fAdd p25519)).denote (hvAppend (encL a) (hvAppend (encL b) .nil))
      = encL (t := .fp p25519) (fAddF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact addBlk_denote _ _ _ _ _ _ _ _ _ a b (nv_encX a _) (nv_encY _ b _)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL (.fSub p25519)).denote (hvAppend (encL a) (hvAppend (encL b) .nil))
      = encL (t := .fp p25519) (fSubF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact subBlk_denote _ _ _ _ _ _ _ _ _ a b (nv_encX a _) (nv_encY _ b _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL (.fNeg p25519)).denote (hvAppend (encL a) .nil)
      = encL (t := .fp p25519) (fNegF a)
    rw [encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact negBlk_denote _ _ _ _ _ a (nv_encX a _)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL (.fMul p25519)).denote (hvAppend (encL a) (hvAppend (encL b) .nil))
      = encL (t := .fp p25519) (fMulF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact mulBlk_denote _ _ _ _ _ _ _ _ _ a b (nv_encX a _) (nv_encY _ b _)
  · obtain ⟨⟩ := vals
    show (lowerOpL (.fConst p25519 c)).denote .nil = encL (t := .fp p25519) (fConstF c)
    rw [encL_fp, lowerOpL, dite_eq_left rfl]
    exact constBlk_denote _ c
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL (.fCopy p25519)).denote (hvAppend (encL a) .nil)
      = encL (t := .fp p25519) (fCopyF a)
    rw [encL_fp, lowerOpL, ite_eq_left rfl]
    exact copyBlk_denote _ _ _ _ _ a (nv_encX a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL (.fieldDouble p25519)).denote (hvAppend (encL a) .nil)
      = encL (t := .fp p25519) (fDoubleF a)
    rw [encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact addBlk_denote _ _ _ _ _ _ _ _ _ a a (nv_encX a _) (nv_encX a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL (.fieldSquare p25519)).denote (hvAppend (encL a) .nil)
      = encL (t := .fp p25519) (fSquareF a)
    rw [encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact sqrBlk_denote _ _ _ _ _ a (nv_encX a _)

/-- **Denotation preservation of `fieldDialect → jasminDialect` over four limbs.** A
    `GoodL`-covered field program lowers to a multi-result jasmin program that maps
    the limbs of its inputs to the limbs of its result. -/
theorem fieldToJasminLimbs_denote {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom GoodL c) (V : Valuation Γ) :
    (loweringL.lowerMulti c).denote (flatVal (fun {t} x => encL (t := t) x) V)
      = encL (c.denote V) :=
  loweringL.multiFundamental_on (fun {t} x => encL (t := t) x) GoodL blockSquareL c hc V

/-! ## 4. The program `x * y + z` -/

/-- The field type `fp (2^255 - 19)`. -/
abbrev F25519 : FieldTy := .fp p25519

/-- The source program `let m = x * y; let s = m + z; ret s`. -/
def mulAddProg : Com fieldDialect [F25519, F25519, F25519] F25519 :=
  .var ⟨.fMul p25519, rfl, .cons .here (.cons (.there .here) .nil)⟩ <|
  .var ⟨.fAdd p25519, rfl, .cons .here (.cons (.there (.there (.there .here))) .nil)⟩ <|
  .ret .here

theorem mulAddProg_covered : CoveredCom GoodL mulAddProg :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inl rfl, trivial⟩

theorem mulAddProg_denote (x y z : ZMod p25519) :
    (mulAddProg.denote (.cons x (.cons y (.cons z .nil))) : ZMod p25519) = x * y + z :=
  rfl

/-- **The lowered `x * y + z`** maps the limbs of `x`, `y`, `z` to the limbs of
    `x * y + z`. -/
theorem mulAddProg_lowered (x y z : ZMod p25519) :
    (loweringL.lowerMulti mulAddProg).denote
      (hvAppend (enc x) (hvAppend (enc y) (hvAppend (enc z) .nil))) = enc (x * y + z) := by
  have h := fieldToJasminLimbs_denote mulAddProg mulAddProg_covered
    (.cons x (.cons y (.cons z .nil)))
  rw [mulAddProg_denote] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs25519
