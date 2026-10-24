/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverse
public import Mathlib.Tactic.LinearCombination

/-!
# `fieldDialect → modArithDialect` with a Montgomery representation

The counterpart of prime-ir's `field-to-mod-arith` pass. Montgomery parameters
`M : MontParams` fix, for each modulus `q`, whether `fp q` is carried in Montgomery
form and the radix `R q` with its inverse `rInv q`. A field value `x : ZMod q` is
represented by `M.toRep x`, which is `x · R q` in Montgomery form and `x` otherwise.
The lowering is a representation-changing `Com` transport: on the lowered program,
multiplication and squaring are `montMul` and inversion is `montInverse` where the
Montgomery flag is set, a constant `c` becomes the constant `toRep c`, and addition,
subtraction, negation, doubling and copies keep their `mod_arith` twin.

The lowering is a `FieldDialectBlockDescent.BlockLoweringData`; `CoveredCom Good`
excludes an inversion at a Montgomery modulus that is not prime. The extension types,
which carry no `fieldDialect` operation, map to `fp q` and are transported to zero.

## Main definitions

* `MontParams`, `MontParams.toRep`, `MontParams.ofRep`: the representation.
* `lowering M`: the lowering; `transTy M`, `mapVal M`: the value and valuation
  transports.
* `GoodOp M`, `Good M`: the covered operations.
* `MontParams.withRepr`, `MontParams.reprOut`, `loweringAt`: the lowering of a
  program of `fieldDialectAt ρ`, whose Montgomery flags are those `ρ` fixes and
  `M.isMont` elsewhere, into `modArithDialectAt` of the flags it used.

## Main results

* `blockSquare`: the block of a covered expression maps the transported valuation
  to the transport of the expression's value.
* `fieldToModArithMont_denote`: for every covered program `c`,
  `((lowering M).blockLowerCom c).denote (mapVal M V) = transTy M (c.denote V)`.
* `fieldToModArithMont_readBack`: reading the lowered value of an `fp q` program
  back through `ofRep` gives the field value.
* `loweringAt_denote`: the transport for `loweringAt`.

The second stage, `modArithDialect → jasminDialect` over four 64-bit limbs, and the
agreement of the two stages with `FieldToJasminLimbsMont4` are in
`Algebraic/ModArithToJasminLimbsMont4.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithMont

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

/-! ## 1. The representation -/

/-- Montgomery parameters per modulus: whether `fp q` is carried in Montgomery form,
    the radix `R q` and its inverse `rInv q`, which multiply to one wherever the
    Montgomery flag is set. -/
structure MontParams where
  /-- The Montgomery flag of `fp q`. -/
  isMont : Nat → Bool
  /-- The Montgomery radix in `ZMod q`. -/
  R : (q : Nat) → ZMod q
  /-- The inverse of the radix in `ZMod q`. -/
  rInv : (q : Nat) → ZMod q
  /-- The radix and its inverse multiply to one where the Montgomery flag is set. -/
  R_mul_rInv : ∀ q, isMont q = true → R q * rInv q = 1

namespace MontParams

variable (M : MontParams)

/-- The representation of `x : ZMod q`: `x · R` in Montgomery form, `x` otherwise. -/
def toRep {q : Nat} (x : ZMod q) : ZMod q := if M.isMont q then x * M.R q else x

/-- The read-back of a representative: `y · R⁻¹` in Montgomery form, `y` otherwise. -/
def ofRep {q : Nat} (y : ZMod q) : ZMod q := if M.isMont q then y * M.rInv q else y

theorem montOfRep_toRep {q : Nat} (x : ZMod q) : M.ofRep (M.toRep x) = x := by
  unfold ofRep toRep
  cases h : M.isMont q
  · rfl
  · simp only [ite_true]
    linear_combination x * M.R_mul_rInv q h

end MontParams

/-! ## 2. The lowering -/

/-- The type map: `fp q ↦ fp q`; the extension types, which the lowering does not
    cover, go to `fp q`. -/
@[reducible] def mapTy : FieldTy → ModArithTy
  | .fp q => .fp q
  | .fp2 q => .fp q
  | .fp6 q => .fp q
  | .fp12 q => .fp q

/-- The context map: pointwise `mapTy`. -/
@[reducible] def mapCtx (Γ : Ctxt fieldDialect) : Ctxt modArithDialect := Γ.map mapTy

/-- The variable map: the same de Bruijn position over the mapped context. -/
@[reducible] def mapVar : {Γ : Ctxt fieldDialect} → {t : FieldTy} → Var Γ t →
    Var (mapCtx Γ) (mapTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVar v)

/-- The argument variables of an expression over the mapped context. -/
@[reducible] def mapArgs {Γ : Ctxt fieldDialect} :
    {tys : List FieldTy} → HVector (fun ty => Var Γ ty) tys →
      HVector (fun ty => Var (mapCtx Γ) ty) (tys.map mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (mapVar v) (mapArgs rest)

/-- The one-binding block applying `op` to `args`. -/
@[reducible] def opCom {Δ : Ctxt modArithDialect} (op : ModArithOp)
    (args : HVector (fun t => Var Δ t) (DialectSignature.sig (d := modArithDialect) op)) :
    Com modArithDialect Δ (DialectSignature.ret (d := modArithDialect) op) :=
  .var ⟨op, rfl, args⟩ (.ret .here)

/-- The block of an operation the lowering does not cover: the constant zero. -/
@[reducible] def zeroCom {Δ : Ctxt modArithDialect} : (t : FieldTy) →
    Com modArithDialect Δ (mapTy t)
  | .fp q => opCom (.modConst q 0) .nil
  | .fp2 q => opCom (.modConst q 0) .nil
  | .fp6 q => opCom (.modConst q 0) .nil
  | .fp12 q => opCom (.modConst q 0) .nil

/-- The block of each field operation. Addition, subtraction, negation, copies and
    doubling keep their `mod_arith` twin; multiplication and squaring become
    `montMul` and inversion becomes `montInverse` where the Montgomery flag is set;
    a constant `c` becomes the constant `toRep c`. -/
def lowerOpBlock (M : MontParams) {Δ : Ctxt modArithDialect} : (op : FieldOp) →
    HVector (fun t => Var Δ t) ((DialectSignature.sig (d := fieldDialect) op).map mapTy) →
      Com modArithDialect Δ (mapTy (DialectSignature.ret (d := fieldDialect) op))
  | .fAdd q, args => opCom (.modAdd q) args
  | .fSub q, args => opCom (.modSub q) args
  | .fNeg q, args => opCom (.modNeg q) args
  | .fMul q, args =>
      if M.isMont q then opCom (.montMul q (M.rInv q)) args else opCom (.modMul q) args
  | .fInv q, args =>
      if M.isMont q then opCom (.montInverse q (M.rInv q)) args
      else opCom (.byInverse q) args
  | .fConst q c, _ => opCom (.modConst q (M.toRep c)) .nil
  | .fCopy q, args => opCom (.modCopy q) args
  | .fieldDouble q, args => opCom (.modAdd q) (.cons args.head (.cons args.head .nil))
  | .fieldSquare q, args =>
      if M.isMont q then opCom (.montMul q (M.rInv q)) (.cons args.head (.cons args.head .nil))
      else opCom (.modMul q) (.cons args.head (.cons args.head .nil))

/-- The block of an expression. -/
def lowerExprBlock (M : MontParams) {Γ : Ctxt fieldDialect} {t : FieldTy} :
    Expr fieldDialect Γ t → Com modArithDialect (mapCtx Γ) (mapTy t)
  | ⟨op, h, args⟩ => h ▸ lowerOpBlock M op (mapArgs args)

/-- The lowering `fieldDialect → modArithDialect` with Montgomery parameters `M`. -/
def lowering (M : MontParams) : BlockLoweringData fieldDialect modArithDialect where
  mapTy := mapTy
  mapCtx := mapCtx
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVar
  lowerExprBlock := lowerExprBlock M

/-! ## 3. Transports and the leaf squares -/

/-- The value transport: `toRep` on `fp q`, zero on the extension types. -/
def transTy (M : MontParams) : TransTy (lowering M) := fun {t} x =>
  match t, x with
  | .fp _, x => M.toRep x
  | .fp2 q, _ => (0 : ZMod q)
  | .fp6 q, _ => (0 : ZMod q)
  | .fp12 q, _ => (0 : ZMod q)

/-- The valuation transport: `transTy` at every position. -/
def mapVal (M : MontParams) : MapVal (lowering M) := fun {Γ} V =>
  match Γ, V with
  | [], .nil => .nil
  | _ :: _, .cons x V => .cons (transTy M x) (mapVal M V)

theorem mapVar_lookup (M : MontParams) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (v : Var Γ t) (V : Valuation Γ) :
    (mapVar v).lookup (mapVal M V) = transTy M (v.lookup V) := by
  induction v with
  | here => cases V with | cons x V => rfl
  | there v ih => cases V with | cons x V => exact ih V

theorem montVarTransports (M : MontParams) : VarTransports (lowering M) (transTy M) (mapVal M) :=
  fun v V => mapVar_lookup M v V

theorem montMapValExtends (M : MontParams) :
    MapValExtends (lowering M) (transTy M) (mapVal M) := by
  intro Γ t V x
  rfl

/-- The operations the lowering covers: prime-field addition, subtraction,
    negation, multiplication, constants, copies, doubling and squaring, and
    inversion at a prime modulus where the Montgomery flag is set. -/
def GoodOp (M : MontParams) : FieldOp → Prop
  | .fAdd _ => True
  | .fSub _ => True
  | .fNeg _ => True
  | .fMul _ => True
  | .fInv q => M.isMont q = true → q.Prime
  | .fConst _ _ => True
  | .fCopy _ => True
  | .fieldDouble _ => True
  | .fieldSquare _ => True

/-- An expression is covered when its operation is. -/
def Good (M : MontParams) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) : Prop :=
  GoodOp M e.op

theorem montToRep_add (M : MontParams) {q : Nat} (a b : ZMod q) :
    M.toRep a + M.toRep b = M.toRep (a + b) := by
  unfold MontParams.toRep; split <;> ring

theorem montToRep_sub (M : MontParams) {q : Nat} (a b : ZMod q) :
    M.toRep a - M.toRep b = M.toRep (a - b) := by
  unfold MontParams.toRep; split <;> ring

theorem montToRep_neg (M : MontParams) {q : Nat} (a : ZMod q) :
    -M.toRep a = M.toRep (-a) := by
  unfold MontParams.toRep; split <;> ring

theorem toRep_montMul (M : MontParams) {q : Nat} (h : M.isMont q = true) (a b : ZMod q) :
    M.toRep a * M.toRep b * M.rInv q = M.toRep (a * b) := by
  simp only [MontParams.toRep, h, ite_true]
  linear_combination (a * b * M.R q) * M.R_mul_rInv q h

theorem toRep_mul (M : MontParams) {q : Nat} (h : M.isMont q = false) (a b : ZMod q) :
    M.toRep a * M.toRep b = M.toRep (a * b) := by
  simp only [MontParams.toRep, h]
  rfl

/-- In `ZMod n`, a right inverse is the inverse. -/
theorem zmod_inv_eq_of_mul_eq_one {n : Nat} {x y : ZMod n} (h : x * y = 1) : x⁻¹ = y := by
  have hu : x⁻¹ * x = 1 := ZMod.inv_mul_of_unit x (IsUnit.of_mul_eq_one y h)
  calc x⁻¹ = x⁻¹ * (x * y) := by rw [h, mul_one]
    _ = (x⁻¹ * x) * y := by ring
    _ = y := by rw [hu, one_mul]

theorem toRep_montInverse (M : MontParams) {q : Nat} (h : M.isMont q = true)
    (hq : q.Prime) (a : ZMod q) :
    (M.toRep a)⁻¹ * (M.rInv q)⁻¹ * (M.rInv q)⁻¹ = M.toRep a⁻¹ := by
  have : Fact q.Prime := ⟨hq⟩
  have hR := M.R_mul_rInv q h
  have hinv : (M.rInv q)⁻¹ = M.R q :=
    zmod_inv_eq_of_mul_eq_one (by rw [mul_comm]; exact hR)
  simp only [MontParams.toRep, h, ite_true, hinv]
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, ZMod.inv_zero]
  · have hau : a * a⁻¹ = 1 :=
      ZMod.mul_inv_of_unit a (ModArithMontInverse.isUnit_of_ne_zero ha)
    have e : (a * M.R q)⁻¹ = a⁻¹ * M.rInv q :=
      zmod_inv_eq_of_mul_eq_one (by linear_combination (M.R q * M.rInv q) * hau + hR)
    rw [e]
    linear_combination (a⁻¹ * M.R q) * hR

theorem toRep_inv (M : MontParams) {q : Nat} (h : M.isMont q = false) (a : ZMod q) :
    (M.toRep a)⁻¹ = M.toRep a⁻¹ := by
  simp only [MontParams.toRep, h]
  rfl

/-- **The block square.** The block of a covered expression maps the transported
    valuation to the transport of the expression's value. -/
theorem blockSquare (M : MontParams) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) (hg : Good M e) (V : Valuation Γ) :
    ((lowering M).lowerExprBlock e).denote (mapVal M V) = transTy M (e.denote V) := by
  rcases e with ⟨op, h, args⟩
  subst h
  cases op with
  | fAdd q =>
      match args with
      | .cons a (.cons b .nil) =>
          show modAddF ((mapVar a).lookup (mapVal M V)) ((mapVar b).lookup (mapVal M V))
            = M.toRep (fAddF (a.lookup V) (b.lookup V))
          rw [mapVar_lookup, mapVar_lookup]
          exact montToRep_add M _ _
  | fSub q =>
      match args with
      | .cons a (.cons b .nil) =>
          show modSubF ((mapVar a).lookup (mapVal M V)) ((mapVar b).lookup (mapVal M V))
            = M.toRep (fSubF (a.lookup V) (b.lookup V))
          rw [mapVar_lookup, mapVar_lookup]
          exact montToRep_sub M _ _
  | fNeg q =>
      match args with
      | .cons a .nil =>
          show modNegF ((mapVar a).lookup (mapVal M V)) = M.toRep (fNegF (a.lookup V))
          rw [mapVar_lookup]
          exact montToRep_neg M _
  | fCopy q =>
      match args with
      | .cons a .nil =>
          show modCopyF ((mapVar a).lookup (mapVal M V)) = M.toRep (fCopyF (a.lookup V))
          rw [mapVar_lookup]
          rfl
  | fConst q c =>
      match args with
      | .nil => rfl
  | fieldDouble q =>
      match args with
      | .cons a .nil =>
          show modAddF ((mapVar a).lookup (mapVal M V)) ((mapVar a).lookup (mapVal M V))
            = M.toRep (fDoubleF (a.lookup V))
          rw [mapVar_lookup]
          exact montToRep_add M _ _
  | fMul q =>
      match args with
      | .cons a (.cons b .nil) =>
          cases hm : M.isMont q
          · simp only [lowering, lowerExprBlock, lowerOpBlock, hm, Bool.false_eq_true, ite_false]
            show modMulF ((mapVar a).lookup (mapVal M V)) ((mapVar b).lookup (mapVal M V))
              = M.toRep (fMulF (a.lookup V) (b.lookup V))
            rw [mapVar_lookup, mapVar_lookup]
            exact toRep_mul M hm _ _
          · simp only [lowering, lowerExprBlock, lowerOpBlock, hm, ite_true]
            show montMulF (M.rInv q) ((mapVar a).lookup (mapVal M V))
                ((mapVar b).lookup (mapVal M V))
              = M.toRep (fMulF (a.lookup V) (b.lookup V))
            rw [mapVar_lookup, mapVar_lookup]
            exact toRep_montMul M hm _ _
  | fieldSquare q =>
      match args with
      | .cons a .nil =>
          cases hm : M.isMont q
          · simp only [lowering, lowerExprBlock, lowerOpBlock, hm, Bool.false_eq_true, ite_false]
            show modMulF ((mapVar a).lookup (mapVal M V)) ((mapVar a).lookup (mapVal M V))
              = M.toRep (fSquareF (a.lookup V))
            rw [mapVar_lookup]
            exact toRep_mul M hm _ _
          · simp only [lowering, lowerExprBlock, lowerOpBlock, hm, ite_true]
            show montMulF (M.rInv q) ((mapVar a).lookup (mapVal M V))
                ((mapVar a).lookup (mapVal M V))
              = M.toRep (fSquareF (a.lookup V))
            rw [mapVar_lookup]
            exact toRep_montMul M hm _ _
  | fInv q =>
      match args with
      | .cons a .nil =>
          cases hm : M.isMont q
          · simp only [lowering, lowerExprBlock, lowerOpBlock, hm, Bool.false_eq_true, ite_false]
            show byInverseF ((mapVar a).lookup (mapVal M V)) = M.toRep (fInvF (a.lookup V))
            rw [mapVar_lookup]
            exact toRep_inv M hm _
          · simp only [lowering, lowerExprBlock, lowerOpBlock, hm, ite_true]
            show montInverseF (M.rInv q) ((mapVar a).lookup (mapVal M V))
              = M.toRep (fInvF (a.lookup V))
            rw [mapVar_lookup]
            exact toRep_montInverse M hm (hg hm) _

/-! ## 4. The whole-program transport -/

/-- **Stage 1 transport.** For every covered field program `c`, the lowered
    `mod_arith` program maps the transported inputs to the transport of `c`'s
    value: `toRep` on `fp q`. -/
theorem fieldToModArithMont_denote (M : MontParams) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (Good M) c) (V : Valuation Γ) :
    ((lowering M).blockLowerCom c).denote (mapVal M V) = transTy M (c.denote V) :=
  blockFundamental_on (lowering M) (transTy M) (mapVal M) (Good M) (montVarTransports M)
    (fun e hg V => blockSquare M e hg V) (montMapValExtends M) c hc V

/-- **Stage 1 read back.** For a covered program returning `fp q`, reading the
    lowered program's value back through the representation gives the field
    value. -/
theorem fieldToModArithMont_readBack (M : MontParams) {Γ : Ctxt fieldDialect} {q : Nat}
    (c : Com fieldDialect Γ (.fp q)) (hc : CoveredCom (Good M) c) (V : Valuation Γ) :
    M.ofRep (q := q) (((lowering M).blockLowerCom c).denote (mapVal M V)) = c.denote V := by
  rw [fieldToModArithMont_denote M c hc V]
  exact M.montOfRep_toRep _

/-! ## 5. Montgomery flags read from the types -/

/-- `M` with the Montgomery flag of `q` taken from `(ρ q).mont` where `ρ` fixes it and
    from `M.isMont q` elsewhere; `h` gives the radix identity where `ρ` sets the flag. -/
def MontParams.withRepr (M : MontParams) (ρ : ModArithReprMap)
    (h : ∀ q, (ρ q).mont = some true → M.R q * M.rInv q = 1) : MontParams where
  isMont q := (ρ q).mont.getD (M.isMont q)
  R := M.R
  rInv := M.rInv
  R_mul_rInv q hq := by
    cases hm : (ρ q).mont with
    | none => rw [hm] at hq; exact M.R_mul_rInv q hq
    | some b => rw [hm] at hq; cases hq; exact h q hm

/-- Under the map that fixes nothing, the flags are those of `M`. -/
theorem MontParams.withRepr_unfixed (M : MontParams)
    (h : ∀ q, (ModArithReprMap.unfixed q).mont = some true → M.R q * M.rInv q = 1) :
    M.withRepr .unfixed h = M := rfl

/-- The representation map of the lowered program: the widths of `ρ`, and the
    Montgomery flag of every modulus fixed to `M.isMont`. -/
def MontParams.reprOut (M : MontParams) (ρ : ModArithReprMap) : ModArithReprMap :=
  fun q => { ρ q with mont := some (M.isMont q) }

/-- The lowering of a program of `fieldDialectAt ρ` with the Montgomery flags of
    `M.withRepr ρ h`, into `modArithDialectAt` of the flags it used. -/
def loweringAt (M : MontParams) (ρ : ModArithReprMap)
    (h : ∀ q, (ρ q).mont = some true → M.R q * M.rInv q = 1)
    {Γ : Ctxt (fieldDialectAt ρ)} {t : FieldTyAt ρ} (c : Com (fieldDialectAt ρ) Γ t) :
    Com (modArithDialectAt ((M.withRepr ρ h).reprOut ρ)) (mapCtx Γ) (mapTy t) :=
  annotateCom _ ((lowering (M.withRepr ρ h)).blockLowerCom (unannotateFieldCom c))

/-- **Stage 1 transport, flags from the types.** For every covered program `c` of
    `fieldDialectAt ρ`, the lowered program maps the transported inputs to the
    transport of `c`'s value under `M.withRepr ρ h`. -/
theorem loweringAt_denote (M : MontParams) (ρ : ModArithReprMap)
    (h : ∀ q, (ρ q).mont = some true → M.R q * M.rInv q = 1)
    {Γ : Ctxt (fieldDialectAt ρ)} {t : FieldTyAt ρ} (c : Com (fieldDialectAt ρ) Γ t)
    (hc : CoveredCom (Good (M.withRepr ρ h)) (unannotateFieldCom c))
    (V : Ctxt.Valuation Γ) :
    (loweringAt M ρ h c).denote (mapVal (M.withRepr ρ h) V)
      = transTy (M.withRepr ρ h) (c.denote V) :=
  fieldToModArithMont_denote (M.withRepr ρ h) (unannotateFieldCom c) hc V

end CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithMont
