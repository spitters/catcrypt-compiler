/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

/-!
# `fieldDialect → jasminDialect` over `n` 64-bit limbs at a Solinas modulus

For a record `S : FieldLimbs.Solinas.SolinasParams n`, the multi-value block lowering
from `fieldDialect` to `jasminDialect` that represents every field type by `n` 64-bit
registers. A value of `fp p` with `p = 2^k - c` is carried by the limbs of its
canonical representative (`Solinas.enc`); values of other types are carried by zero
limbs.

| source op at `p` | target block |
|---|---|
| `fAdd`, `fieldDouble` | `addBlk x y`, `addBlk x x` |
| `fSub` | `subBlk x y` |
| `fNeg` | `negBlk x` |
| `fMul`, `fieldSquare` | `mulBlk x y`, `sqrBlk x` |
| `fConst p c` | `constBlk c` |

Every other operation, and every operation at a modulus other than `p`, lowers to the
zero limbs; the coverage predicate `GoodL` excludes them.

## Main definitions

* `CN`, `opVars`, `pastN`: the operand contexts and variables.
* `encL`: the encoding, over the type map `FieldToJasminLimbs.mapTysL n`.
* `lowerOpL`: the per-operation blocks; `loweringL`: the lowering
  `FieldToJasminLimbs.loweringOf (lowerOpL S)`.
* `GoodL`: the operations covered at `p`.
* `opGoodLB`, `GoodLB`: the decision of coverage.

## Main results

* `nv_opVars`, `nv_encX`, `nv_encY`: the operand limb variables of a flattened
  valuation carry the canonical representatives.
* `blockSquareL`: the block square of `loweringL` for `GoodL` expressions.
* `GoodLB_sound`: a program accepted by `GoodLB` is `GoodL`-covered.
* `fieldToJasminLimbs_denote`: for every `GoodL`-covered program `c`,
  `(loweringL S).lowerMulti c` denotes `encL S (c.denote V)` on `flatVal (encL S) V`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsSolinas

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 nv nv_nil nv_cons nv_map)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn limbsN two_pow_succ)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (mapTysL loweringOf)

/-! ## 1. Operand variables -/

/-- The context `Γ` preceded by `k` limbs. -/
abbrev CN (k : Nat) (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := Rn k ++ Γ

/-- The first `k` variables of `CN k Γ`, in order. -/
def opVars {Γ : Ctxt jasminDialect} : (k : Nat) → List (Var (CN k Γ) w64)
  | 0 => []
  | k + 1 => (Var.here : Var (w64 :: CN k Γ) w64) :: (opVars k).map (fun v => v.there)

/-- A variable of `Γ` shifted past `k` limbs. -/
def pastN {Γ : Ctxt jasminDialect} {t : JasminTy} : (k : Nat) → Var Γ t → Var (CN k Γ) t
  | 0, v => v
  | k + 1, v => (pastN k v).there

theorem opVars_length {Γ : Ctxt jasminDialect} : ∀ k, (opVars (Γ := Γ) k).length = k
  | 0 => rfl
  | k + 1 => by simp [opVars, opVars_length k]

theorem lookup_pastN {Γ : Ctxt jasminDialect} {t : JasminTy} (B : Valuation Γ) :
    ∀ (k : Nat) (A : ListDenote (Rn k)) (v : Var Γ t),
      (pastN k v).lookup (hvAppend A B) = v.lookup B
  | 0, .nil, _ => rfl
  | k + 1, .cons _ A, v => lookup_pastN B k A v

theorem nv_opVars {Γ : Ctxt jasminDialect} (B : Valuation Γ) :
    ∀ (k v : Nat), nv (hvAppend (limbsN k v) B) (opVars k) = v % 2 ^ (64 * k)
  | 0, v => by simp [opVars, nv_nil, Nat.mod_one]
  | k + 1, v => by
      have ih := nv_opVars B k (v / 2 ^ 64)
      have hm := nv_map (r := fun {_} w => Var.there w)
        (W := (hvAppend (limbsN k (v / 2 ^ 64)) B : Valuation (CN k Γ)))
        (W' := (HVector.cons (BitVec.ofNat 64 v) (hvAppend (limbsN k (v / 2 ^ 64)) B) :
          Valuation (w64 :: CN k Γ)))
        (fun _ => rfl) (opVars k)
      show nv (HVector.cons (BitVec.ofNat 64 v) (hvAppend (limbsN k (v / 2 ^ 64)) B) :
          Valuation (w64 :: CN k Γ))
        ((Var.here : Var (w64 :: CN k Γ) w64) :: (opVars k).map (fun v => v.there)) = _
      rw [nv_cons, hm, ih, two_pow_succ, Nat.mul_comm (2 ^ (64 * k)), Nat.mod_mul]
      rfl

variable {n : Nat} (S : SolinasParams n)

theorem nv_encX {Γ : Ctxt jasminDialect} (x : ZMod (p S)) (B : Valuation Γ) :
    nv (hvAppend (enc S x) B : Valuation (CN n Γ)) (opVars n) = x.val := by
  rw [enc, nv_opVars, Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt x) (p_lt S))]

theorem nv_encY {Γ : Ctxt jasminDialect} (A : ListDenote (Rn n)) (y : ZMod (p S))
    (B : Valuation Γ) :
    nv (hvAppend A (hvAppend (enc S y) B) : Valuation (CN n (CN n Γ)))
      ((opVars n).map (fun v => pastN n v)) = y.val := by
  rw [nv_map (r := fun {_} w => pastN n w) (W := (hvAppend (enc S y) B : Valuation (CN n Γ)))
    (fun v => lookup_pastN _ n A v), nv_encX]

/-! ## 2. The lowering -/

/-- The encoding: `enc` on `fp p`, and zero limbs on every other type. -/
def encL : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t)
  | .fp q, x => if h : q = p S then enc S (cast (congrArg ZMod h) x) else limbsN n 0
  | .fp2 _, _ => limbsN n 0
  | .fp6 _, _ => limbsN n 0
  | .fp12 _, _ => limbsN n 0

theorem encL_fp (x : ZMod (p S)) : encL S (t := .fp (p S)) x = enc S x := by
  simp only [encL, dite_true]
  rfl

/-- The zero limbs. -/
abbrev zeroBlk {Γ : Ctxt jasminDialect} : MultiReturnCom jasminDialect Γ (Rn n) :=
  FieldLimbs.Mont.constBlk n 0

/-- The block of each field operation. -/
def lowerOpL : (op : fieldDialect.Op) →
    MultiReturnCom jasminDialect (ctxFlat (mapTysL n) (DialectSignature.sig op))
      (mapTysL n (DialectSignature.ret op))
  | .fAdd q => if q = p S then addBlk S (opVars n) ((opVars n).map (fun v => pastN n v))
    else zeroBlk
  | .fSub q => if q = p S then subBlk S (opVars n) ((opVars n).map (fun v => pastN n v))
    else zeroBlk
  | .fNeg q => if q = p S then negBlk S (opVars n) else zeroBlk
  | .fMul q => if q = p S then mulBlk S (opVars n) ((opVars n).map (fun v => pastN n v))
    else zeroBlk
  | .fConst q c => if h : q = p S then constBlk S (cast (congrArg ZMod h) c) else zeroBlk
  | .fCopy _ => zeroBlk
  | .fieldDouble q => if q = p S then addBlk S (opVars n) (opVars n) else zeroBlk
  | .fieldSquare q => if q = p S then sqrBlk S (opVars n) else zeroBlk
  | .fInv _ => zeroBlk

/-- The multi-value lowering `fieldDialect → jasminDialect` over `n` limbs: the generic
    limb lowering with the blocks `lowerOpL S`. -/
def loweringL : MultiBlockLoweringData fieldDialect jasminDialect :=
  loweringOf (lowerOpL S)

/-- The operations covered at `p`: add, sub, neg, mul, constants, doubling and
    squaring. -/
def GoodL {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) : Prop :=
  e.op = .fAdd (p S) ∨ e.op = .fSub (p S) ∨ e.op = .fNeg (p S) ∨ e.op = .fMul (p S) ∨
    (∃ c : ZMod (p S), e.op = .fConst (p S) c) ∨ e.op = .fieldDouble (p S) ∨
    e.op = .fieldSquare (p S)

/-! ## 3. The block square and the fundamental theorem -/

/-- The block square of `loweringL`. -/
theorem blockSquareL : (loweringL S).BlockSquare (fun {t} x => encL S (t := t) x)
    (GoodL S) := by
  intro Γ t e hg vals
  obtain ⟨op, h, args⟩ := e
  rcases hg with hop | hop | hop | hop | ⟨c, hop⟩ | hop | hop <;> subst hop
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL S (.fAdd (p S))).denote (hvAppend (encL S a) (hvAppend (encL S b) .nil))
      = encL S (t := .fp (p S)) (fAddF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact addBlk_denote S _ _ _ (opVars_length n) (by rw [List.length_map]; exact opVars_length n)
      a b (nv_encX S a _) (nv_encY S _ b _)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL S (.fSub (p S))).denote (hvAppend (encL S a) (hvAppend (encL S b) .nil))
      = encL S (t := .fp (p S)) (fSubF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact subBlk_denote S _ _ _ (opVars_length n) (by rw [List.length_map]; exact opVars_length n)
      a b (nv_encX S a _) (nv_encY S _ b _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL S (.fNeg (p S))).denote (hvAppend (encL S a) .nil)
      = encL S (t := .fp (p S)) (fNegF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact negBlk_denote S _ _ (opVars_length n) a (nv_encX S a _)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL S (.fMul (p S))).denote (hvAppend (encL S a) (hvAppend (encL S b) .nil))
      = encL S (t := .fp (p S)) (fMulF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact mulBlk_denote S _ _ _ (opVars_length n) (by rw [List.length_map]; exact opVars_length n)
      a b (nv_encX S a _) (nv_encY S _ b _)
  · obtain ⟨⟩ := vals
    show (lowerOpL S (.fConst (p S) c)).denote .nil = encL S (t := .fp (p S)) (fConstF c)
    rw [encL_fp, lowerOpL, dif_pos rfl]
    exact constBlk_denote S _ c
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL S (.fieldDouble (p S))).denote (hvAppend (encL S a) .nil)
      = encL S (t := .fp (p S)) (fDoubleF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact addBlk_denote S _ _ _ (opVars_length n) (opVars_length n) a a (nv_encX S a _)
      (nv_encX S a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL S (.fieldSquare (p S))).denote (hvAppend (encL S a) .nil)
      = encL S (t := .fp (p S)) (fSquareF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact sqrBlk_denote S _ _ (opVars_length n) a (nv_encX S a _)

/-- Denotation preservation of `fieldDialect → jasminDialect` over `n` limbs: a
    `GoodL`-covered field program lowers to a multi-result jasmin program that maps the
    limbs of its inputs to the limbs of its result. -/
theorem fieldToJasminLimbs_denote {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodL S) c) (V : Valuation Γ) :
    ((loweringL S).lowerMulti c).denote (flatVal (fun {t} x => encL S (t := t) x) V)
      = encL S (c.denote V) :=
  (loweringL S).multiFundamental_on (fun {t} x => encL S (t := t) x) (GoodL S)
    (blockSquareL S) c hc V

/-! ## 4. The decision of coverage -/

/-- The operations `GoodLB` accepts: those of `GoodL`. -/
def opGoodLB : fieldDialect.Op → Bool
  | .fAdd q | .fSub q | .fNeg q | .fMul q | .fieldDouble q | .fieldSquare q => q == p S
  | .fConst q _ => q == p S
  | _ => false

/-- The coverage decision: every let-bound operation passes `opGoodLB`. -/
def GoodLB : {Γ : Ctxt fieldDialect} → {t : FieldTy} → Com fieldDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opGoodLB S e.op && GoodLB body

theorem opGoodLB_sound {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t)
    (h : opGoodLB S e.op = true) : GoodL S e := by
  obtain ⟨op, _, _⟩ := e
  cases op <;> simp only [opGoodLB, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;>
    simp [GoodL]

/-- A program accepted by `GoodLB` is `GoodL`-covered. -/
theorem GoodLB_sound : {Γ : Ctxt fieldDialect} → {t : FieldTy} →
    (c : Com fieldDialect Γ t) → GoodLB S c = true → CoveredCom (GoodL S) c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, h => by
      simp only [GoodLB, Bool.and_eq_true] at h
      exact ⟨opGoodLB_sound S e h.1, GoodLB_sound body h.2⟩

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsSolinas
