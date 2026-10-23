/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithMont

/-!
# `modArithDialect → jasminDialect` over four 64-bit limbs, and the two-stage descent

The counterpart of prime-ir's `mod-arith-to-arith` pass at a modulus record
`P : FieldLimbs.Mont4.Mont4Prime`. Every `mod_arith` type is carried by four 64-bit
registers; a value `y : ZMod P.p` is carried by the limbs of its canonical
representative `y.val`, whatever representation the value is in. The blocks at `P.p`:

| source op | target block |
|---|---|
| `modAdd` | `addBlk x y` |
| `modSub` | `subBlk x y`, the borrow chain with `p` added back on a borrow |
| `modNeg` | `negBlk x`, the subtraction from the zero limbs |
| `montMul _` | `mulBlk x y` |
| `montReduce _` | `reduceBlk x`, the Montgomery product with `1` |
| `montInverse _` | `invBlk x`, the Montgomery power `x^(p-2)` by square-and-multiply |
| `modConst c` | `constBlk c.val` |
| `modCopy` | `Curve25519.copyBlk x` |

The coverage predicate `GoodA` fixes the radix inverse of `montMul`, `montReduce` and
`montInverse` to `rInv P = (2^256)⁻¹`, and covers `montInverse` only at a prime
modulus. Every other operation, including the plain `modMul` and `byInverse`, lowers
to the zero limbs; stage 1 at `montOf P` emits neither at `P.p`.

Composed with `FieldToModArithMont.lowering (montOf P)`, which puts `fp P.p` in
Montgomery form with radix `2^256`, the two stages lower every program that `GoodV`
covers (addition, subtraction, negation, multiplication, doubling, squaring,
constants, copies, and inversion at a prime modulus) to a jasmin program with the
one-step lowering's encoding `encL P`. On the fragment that
`FieldToJasminLimbsMont4.GoodV` covers, the result agrees with that of
`FieldToJasminLimbsMont4.loweringL`. The blocks `subBlk`, `negBlk` and `invBlk` are
those of `FieldLimbs.Mont4`, shared with the one-step lowering.

## Main definitions

* `rInv P`, `reduceBlk`: the radix inverse and the Montgomery reduction block.
* `encA`, `lowerOpA`, `loweringA`, `GoodA`: the stage-2 encoding, blocks, lowering
  and coverage.
* `montOf P`: the Montgomery parameters of `P` for stage 1.

## Main results

* `invBlk_denote`: the inversion block computes `montInverse` with radix inverse
  `rInv P` at a prime modulus.
* `modArithToJasminLimbsMont4_denote`: for every `GoodA`-covered program `c`,
  `((loweringA P).lowerMulti c).denote (flatVal encA V) = encA (c.denote V)`.
* `coveredCom_blockLowerCom`: a block lowering whose blocks are covered by an
  operation predicate maps covered programs to covered programs.
* `encA_transTy`: `encA ∘ transTy (montOf P) = encL P`.
* `fieldToJasminViaModArith_denote`: the composite maps the encoded inputs of a
  `GoodV`-covered field program to `encL P` of its value.
* `fieldToJasminViaModArith_agreesV`: on a `GoodV`-covered program the composite and
  `loweringL` produce the same limbs; `fieldToJasminViaModArith_agrees` is its
  restriction to `GoodM`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithToJasminLimbsMont4

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk1 eConst eBit eBit_denote Pres Pres.id Pres.comp bindK bindK_denote nv nv_nil
    nv_cons nv_map nv_lt selR selR_denote constsK constsK_denote addK addK_denote adcR
    adcR_denote xorR xorR_denote R4 limbsOf ret4 ret4_denote copyBlk)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4
  (C4 xv₀ xv₁ xv₂ xv₃ past4 nv_limbsOf)

variable (P : Mont4Prime)

/-! ## 1. The radix inverse and the plain encoding -/

/-- The inverse of the Montgomery radix `2^256` in `ZMod p`. -/
def rInv : ZMod P.p := (R P)⁻¹

theorem R_mul_rInv : R P * rInv P = 1 := ZMod.mul_inv_of_unit _ (isUnit_R P)

/-- A residue `y` is the Montgomery form of `y · R⁻¹`. -/
theorem enc_mul_rInv (y : ZMod P.p) : enc P (y * rInv P) = limbsOf y.val := by
  rw [enc, mul_assoc, mul_comm (rInv P), R_mul_rInv, mul_one]

theorem val_mul_rInv_mul_R (y : ZMod P.p) : (y * rInv P * R P).val = y.val := by
  rw [mul_assoc, mul_comm (rInv P), R_mul_rInv, mul_one]

theorem nv_limbsY {Γ : Ctxt jasminDialect} (A : ListDenote R4) (n : Nat) (hn : n < 2 ^ 256)
    (B : Valuation Γ) :
    nv (hvAppend A (hvAppend (limbsOf n) B))
      [past4 xv₀, past4 xv₁, past4 xv₂, past4 xv₃] = n := by
  rcases A with _ | ⟨a₀, _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | _⟩⟩⟩⟩
  exact nv_limbsOf n hn B

/-! ## 2. The Montgomery reduction block -/

section Reduce

variable {Γ : Ctxt jasminDialect}

/-- The Montgomery reduction block: the Montgomery product of `x₀ … x₃` with the
    constant `1`. -/
def reduceBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  .var (eConst 1) <| .var (eConst 0) <| .var (eConst 0) <| .var (eConst 0) <|
    mulBlk P (.there (.there (.there (.there x₀)))) (.there (.there (.there (.there x₁))))
      (.there (.there (.there (.there x₂)))) (.there (.there (.there (.there x₃))))
      (.there (.there (.there .here))) (.there (.there .here)) (.there .here) .here

theorem reduceBlk_denote (W : Valuation Γ) (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) :
    (reduceBlk P x₀ x₁ x₂ x₃).denote W = enc P (x * rInv P) := by
  refine mulBlk_denote P _ _ _ _ _ _ _ _ _ x (rInv P) hx ?_
  rw [mul_comm, R_mul_rInv, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt P.one_lt]
  rfl

end Reduce

/-! ## 3. The Montgomery inversion -/

/-- The Montgomery inverse of a Montgomery form `a` is the Montgomery form of
    `(a · R⁻¹)^(p-2)`. -/
theorem montInverse_eq (hp : P.p.Prime) (a : ZMod P.p) :
    montInverseF (rInv P) a = (a * rInv P) ^ (P.p - 2) * R P := by
  have hR : (rInv P)⁻¹ = R P :=
    ZMod.inv_eq_of_mul_eq_one _ _ _ (by rw [mul_comm]; exact R_mul_rInv P)
  rw [pow_sub_two_eq_inv P hp, montInverseF, hR]
  by_cases ha : a = 0
  · subst ha
    rw [zero_mul, ZMod.inv_zero, zero_mul, zero_mul]
  · have hinv := pow_sub_two_eq_inv P hp a
    have hu : a * a⁻¹ = 1 := by
      have := Fact.mk hp
      rw [← hinv, ← pow_succ', show P.p - 2 + 1 = P.p - 1 by
        have := hp.two_le; omega]
      exact ZMod.pow_card_sub_one_eq_one ha
    rw [ZMod.inv_eq_of_mul_eq_one _ (a * rInv P) (a⁻¹ * R P) (by
      rw [show a * rInv P * (a⁻¹ * R P) = (a * a⁻¹) * (R P * rInv P) by ring, hu,
        R_mul_rInv, one_mul])]

/-- The inversion block on the limbs of `a` returns the limbs of the Montgomery inverse
    of `a` with radix inverse `rInv P`. -/
theorem invBlk_denote {Γ : Ctxt jasminDialect} (hp : P.p.Prime) (W : Valuation Γ)
    (x₀ x₁ x₂ x₃ : Var Γ w64) (a : ZMod P.p) (hx : nv W [x₀, x₁, x₂, x₃] = a.val) :
    (invBlk P x₀ x₁ x₂ x₃).denote W = limbsOf (montInverseF (rInv P) a).val := by
  rw [invBlk_denote_pow P W x₀ x₁ x₂ x₃ (a * rInv P) (by rw [hx, val_mul_rInv_mul_R]), enc,
    montInverse_eq P hp]

/-! ## 4. The lowering -/

/-- Every `mod_arith` type is carried by four 64-bit registers. -/
@[reducible] def mapTysA : modArithDialect.Ty → List jasminDialect.Ty := fun _ => R4

/-- The encoding: the limbs of the canonical representative on `fp P.p`, zero limbs
    on every other type. A value of `fp P.p` is taken as it stands, so a value in
    Montgomery form is carried by the limbs of that form. -/
def encA : ∀ {t : modArithDialect.Ty}, ⟦t⟧ → Valuation (mapTysA t)
  | .fp q, x => if h : q = P.p then limbsOf (cast (congrArg ZMod h) x).val else limbsOf 0
  | .fpVec _ _, _ => limbsOf 0
  | .word _, _ => limbsOf 0
  | .carry, _ => limbsOf 0

theorem encA_fp (x : ZMod P.p) : encA P (t := .fp P.p) x = limbsOf x.val := by
  simp only [encA, dite_true]
  rfl

/-- The block of each `mod_arith` operation at `P.p`: `modAdd` and `modSub` are the
    limb addition and subtraction, `modNeg` the negation, `montMul` the Montgomery
    multiplication, `montReduce` the Montgomery reduction, `montInverse` the Montgomery
    inversion, `modConst c` the limbs of `c` and `modCopy` the limb copy; every other
    operation lowers to the zero limbs. -/
def lowerOpA : (op : modArithDialect.Op) →
    MultiReturnCom jasminDialect (ctxFlat mapTysA (DialectSignature.sig op))
      (mapTysA (DialectSignature.ret op))
  | .modAdd q => if q = P.p then
      addBlk P xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .modSub q => if q = P.p then
      subBlk P xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .modNeg q => if q = P.p then negBlk P xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .montMul q _ => if q = P.p then
      mulBlk P xv₀ xv₁ xv₂ xv₃ (past4 xv₀) (past4 xv₁) (past4 xv₂) (past4 xv₃)
    else constBlk 0
  | .montReduce q _ => if q = P.p then reduceBlk P xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .montInverse q _ => if q = P.p then invBlk P xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | .modConst q c => if h : q = P.p then constBlk (cast (congrArg ZMod h) c).val
    else constBlk 0
  | .modCopy q => if q = P.p then copyBlk xv₀ xv₁ xv₂ xv₃ else constBlk 0
  | _ => constBlk 0

/-- The multi-value lowering `modArithDialect → jasminDialect` over four limbs. -/
def loweringA : MultiBlockLoweringData modArithDialect jasminDialect where
  mapTys := mapTysA
  lowerOp := lowerOpA P

/-- The operations covered at `P.p`: addition, Montgomery multiplication and
    reduction with the radix inverse `rInv P`, constants, copies, subtraction,
    negation, and the Montgomery inverse with `rInv P` when `P.p` is prime. -/
def GoodOpA (op : modArithDialect.Op) : Prop :=
  op = .modAdd P.p ∨ op = .montMul P.p (rInv P) ∨ op = .montReduce P.p (rInv P) ∨
    (∃ c : ZMod P.p, op = .modConst P.p c) ∨ op = .modCopy P.p ∨ op = .modSub P.p ∨
    op = .modNeg P.p ∨ (P.p.Prime ∧ op = .montInverse P.p (rInv P))

/-- An expression is covered when its operation is. -/
def GoodA {Γ : Ctxt modArithDialect} {t : ModArithTy} (e : Expr modArithDialect Γ t) : Prop :=
  GoodOpA P e.op

/-! ## 5. The block square and the stage-2 theorem -/

theorem blockSquareA :
    (loweringA P).BlockSquare (fun {t} x => encA P (t := t) x) (GoodA P) := by
  intro Γ t e hg vals
  obtain ⟨op, h, args⟩ := e
  rcases hg with hop | hop | hop | ⟨c, hop⟩ | hop | hop | hop | ⟨hp, hop⟩ <;> subst hop
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpA P (.modAdd P.p)).denote (hvAppend (encA P a) (hvAppend (encA P b) .nil))
      = encA P (t := .fp P.p) (modAddF a b)
    change ZMod P.p at a b
    rw [encA_fp, encA_fp, encA_fp, lowerOpA, if_pos rfl, ← enc_mul_rInv P (modAddF a b),
      show modAddF a b * rInv P = a * rInv P + b * rInv P by simp only [modAddF]; ring]
    exact addBlk_denote P _ _ _ _ _ _ _ _ _ (a * rInv P) (b * rInv P)
      ((nv_limbsOf _ (val_lt_two_pow P a) _).trans (val_mul_rInv_mul_R P a).symm)
      ((nv_limbsY _ _ (val_lt_two_pow P b) _).trans (val_mul_rInv_mul_R P b).symm)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpA P (.montMul P.p (rInv P))).denote
        (hvAppend (encA P a) (hvAppend (encA P b) .nil))
      = encA P (t := .fp P.p) (montMulF (rInv P) a b)
    change ZMod P.p at a b
    rw [encA_fp, encA_fp, encA_fp, lowerOpA, if_pos rfl,
      ← enc_mul_rInv P (montMulF (rInv P) a b),
      show montMulF (rInv P) a b * rInv P = a * rInv P * (b * rInv P) by
        simp only [montMulF]; ring]
    exact mulBlk_denote P _ _ _ _ _ _ _ _ _ (a * rInv P) (b * rInv P)
      ((nv_limbsOf _ (val_lt_two_pow P a) _).trans (val_mul_rInv_mul_R P a).symm)
      ((nv_limbsY _ _ (val_lt_two_pow P b) _).trans (val_mul_rInv_mul_R P b).symm)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpA P (.montReduce P.p (rInv P))).denote (hvAppend (encA P a) .nil)
      = encA P (t := .fp P.p) (montReduceF (rInv P) a)
    change ZMod P.p at a
    rw [encA_fp, encA_fp, lowerOpA, if_pos rfl, ← enc_mul_rInv P (montReduceF (rInv P) a),
      show montReduceF (rInv P) a * rInv P = a * rInv P * rInv P by rfl]
    exact reduceBlk_denote P _ _ _ _ _ (a * rInv P)
      ((nv_limbsOf _ (val_lt_two_pow P a) _).trans (val_mul_rInv_mul_R P a).symm)
  · obtain ⟨⟩ := vals
    show (lowerOpA P (.modConst P.p c)).denote .nil = encA P (t := .fp P.p) (modConstF c)
    rw [encA_fp, lowerOpA, dif_pos rfl]
    exact constBlk_denote _ _
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpA P (.modCopy P.p)).denote (hvAppend (encA P a) .nil)
      = encA P (t := .fp P.p) (modCopyF a)
    rw [encA_fp, lowerOpA, if_pos rfl, copyBlk_denote,
      nv_limbsOf _ (val_lt_two_pow P a)]
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpA P (.modSub P.p)).denote (hvAppend (encA P a) (hvAppend (encA P b) .nil))
      = encA P (t := .fp P.p) (modSubF a b)
    change ZMod P.p at a b
    rw [encA_fp, encA_fp, encA_fp, lowerOpA, if_pos rfl]
    exact subBlk_denote P _ _ _ _ _ _ _ _ _ a b (nv_limbsOf _ (val_lt_two_pow P a) _)
      (nv_limbsY _ _ (val_lt_two_pow P b) _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpA P (.modNeg P.p)).denote (hvAppend (encA P a) .nil)
      = encA P (t := .fp P.p) (modNegF a)
    change ZMod P.p at a
    rw [encA_fp, encA_fp, lowerOpA, if_pos rfl]
    exact negBlk_denote P _ _ _ _ _ a (nv_limbsOf _ (val_lt_two_pow P a) _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpA P (.montInverse P.p (rInv P))).denote (hvAppend (encA P a) .nil)
      = encA P (t := .fp P.p) (montInverseF (rInv P) a)
    change ZMod P.p at a
    rw [encA_fp, encA_fp, lowerOpA, if_pos rfl]
    exact invBlk_denote P hp _ _ _ _ _ a (nv_limbsOf _ (val_lt_two_pow P a) _)

/-- **Stage 2 transport.** A `GoodA`-covered `mod_arith` program lowers to a
    multi-result jasmin program that maps the limbs of its inputs to the limbs of its
    result. -/
theorem modArithToJasminLimbsMont4_denote {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (c : Com modArithDialect Γ t) (hc : CoveredCom (GoodA P) c) (V : Valuation Γ) :
    ((loweringA P).lowerMulti c).denote (flatVal (fun {t} x => encA P (t := t) x) V)
      = encA P (c.denote V) :=
  (loweringA P).multiFundamental_on (fun {t} x => encA P (t := t) x) (GoodA P)
    (blockSquareA P) c hc V

/-! ## 6. Coverage through a block lowering -/

section Coverage

variable {d : Dialect} [DialectSignature d]

/-- The expression predicate of an operation predicate. -/
abbrev OpGood (Q : d.Op → Prop) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) : Prop := Q e.op

theorem coveredCom_mono (G G' : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hG : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), G e → G' e) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t), CoveredCom G c → CoveredCom G' c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, hc => ⟨hG e hc.1, coveredCom_mono G G' hG body hc.2⟩

/-- A renaming keeps the coverage of a program by the expression predicate of an operation
    predicate. -/
theorem coveredCom_rename_opGood (Q : d.Op → Prop) :
    ∀ {Γ Γ' : Ctxt d} {t : d.Ty} (h : Ctxt.Hom Γ Γ') (c : Com d Γ t),
      CoveredCom (OpGood Q) c → CoveredCom (OpGood Q) (Com.rename h c)
  | _, _, _, _, .ret _, _ => trivial
  | _, _, _, h, .var _ body, hc => ⟨hc.1, coveredCom_rename_opGood Q h.lift body hc.2⟩

/-- A splice of two programs covered by the expression predicate of an operation predicate is
    covered by it. -/
theorem coveredCom_spliceCom_opGood (Q : d.Op → Prop) :
    ∀ {Γ : Ctxt d} {t s : d.Ty} (c : Com d Γ t) (k : Com d (t :: Γ) s),
      CoveredCom (OpGood Q) c → CoveredCom (OpGood Q) k →
        CoveredCom (OpGood Q) (FieldDialectBlockDescent.spliceCom c k)
  | _, _, _, .ret _, k, _, hk => coveredCom_rename_opGood Q _ k hk
  | _, _, _, .var _ body, k, hc, hk =>
      ⟨hc.1, coveredCom_spliceCom_opGood Q body _ hc.2 (coveredCom_rename_opGood Q _ k hk)⟩

/-- A block lowering whose block of every `G`-expression is covered by an operation
    predicate `Q` lowers every `G`-covered program to a `Q`-covered program. -/
theorem coveredCom_blockLowerCom {d' : Dialect} [DialectSignature d']
    (L : FieldDialectBlockDescent.BlockLoweringData d d') (Q : d'.Op → Prop)
    (G : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hL : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), G e →
      CoveredCom (OpGood Q) (L.lowerExprBlock e)) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t), CoveredCom G c →
      CoveredCom (OpGood Q) (L.blockLowerCom c)
  | _, _, .ret _, _ => trivial
  | Γ, _, .var (t := bs) e body, hc => by
      have ih := coveredCom_blockLowerCom L Q G hL body hc.2
      refine coveredCom_spliceCom_opGood Q _ _ (hL e hc.1) ?_
      generalize L.blockLowerCom body = x at ih ⊢
      generalize L.mapCtx_cons bs Γ = hh
      revert x hh
      generalize L.mapCtx (bs :: Γ) = Z
      intro x ih hh
      subst hh
      exact ih

end Coverage

/-! ## 7. The composite and the one-step lowering -/

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4 (encL loweringL GoodM
  GoodV encL_fp fieldToJasminLimbsMont4_denoteV)

/-- The Montgomery parameters of `P`: `fp P.p` in Montgomery form with radix `2^256`,
    every other modulus in plain form. -/
def montOf : FieldToModArithMont.MontParams where
  isMont q := decide (q = P.p)
  R q := if h : q = P.p then cast (congrArg ZMod h.symm) (R P) else 1
  rInv q := if h : q = P.p then cast (congrArg ZMod h.symm) (rInv P) else 1
  R_mul_rInv q hq := by
    have h : q = P.p := of_decide_eq_true hq
    subst h
    simp only [dite_true, cast_eq]
    exact R_mul_rInv P

theorem montOf_isMont : (montOf P).isMont P.p = true := decide_eq_true rfl

theorem montOf_R : (montOf P).R P.p = R P := by
  simp only [montOf, dite_true, cast_eq]

theorem montOf_rInv : (montOf P).rInv P.p = rInv P := by
  simp only [montOf, dite_true, cast_eq]

/-- The stage-1 block of a `GoodV`-expression is `GoodA`-covered. -/
theorem lowerExprBlock_covered {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) (hg : GoodV P e) :
    CoveredCom (OpGood (d := modArithDialect) (GoodOpA P))
      ((FieldToModArithMont.lowering (montOf P)).lowerExprBlock e) := by
  have key : ∀ {α : Type} (b : Bool) (x y : α) (Pr : α → Prop), b = true → Pr x →
      Pr (if b = true then x else y) := by
    intro α b x y Pr hb hx
    subst hb
    exact hx
  obtain ⟨op, h, args⟩ := e
  rcases hg with (hop | hop | ⟨c, hop⟩ | hop) | hop | hop | hop | hop | ⟨hp, hop⟩ <;>
    subst hop <;> subst h
  · exact ⟨Or.inl rfl, trivial⟩
  · exact key _ _ _ (CoveredCom (OpGood (d := modArithDialect) (GoodOpA P)))
      (montOf_isMont P) ⟨Or.inr (Or.inl (by rw [montOf_rInv])), trivial⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))), trivial⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), trivial⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), trivial⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), trivial⟩
  · exact ⟨Or.inl rfl, trivial⟩
  · exact key _ _ _ (CoveredCom (OpGood (d := modArithDialect) (GoodOpA P)))
      (montOf_isMont P) ⟨Or.inr (Or.inl (by rw [montOf_rInv])), trivial⟩
  · exact key _ _ _ (CoveredCom (OpGood (d := modArithDialect) (GoodOpA P)))
      (montOf_isMont P)
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, by rw [montOf_rInv]⟩)))))),
        trivial⟩

/-- The composite encoding is the one-step encoding: `encA ∘ transTy = encL`. -/
theorem encA_transTy {t : FieldTy} (x : ⟦t⟧) :
    encA P (FieldToModArithMont.transTy (montOf P) x) = encL P x := by
  have zero : ∀ q : Nat, encA P (t := .fp q) (0 : ZMod q) = limbsOf 0 := by
    intro q
    by_cases h : q = P.p
    · subst h
      rw [encA_fp, ZMod.val_zero]
    · simp only [encA, dif_neg h]
  cases t with
  | fp q =>
      by_cases h : q = P.p
      · subst h
        show encA P (t := .fp P.p) ((montOf P).toRep x) = encL P (t := .fp P.p) x
        rw [encA_fp, encL_fp, FieldToModArithMont.MontParams.toRep, if_pos (montOf_isMont P),
          montOf_R]
        rfl
      · show encA P (t := .fp q) ((montOf P).toRep x) = encL P (t := .fp q) x
        simp only [encA, encL, dif_neg h]
  | fp2 q => exact zero q
  | fp6 q => exact zero q
  | fp12 q => exact zero q

/-- **The composite transport.** For every `GoodV`-covered field program `c`, lowering
    it by stage 1 at `montOf P` and then by stage 2 gives a jasmin program that maps
    the limbs of its inputs to `encL P` of `c`'s value, the encoding of the one-step
    lowering `FieldToJasminLimbsMont4`. -/
theorem fieldToJasminViaModArith_denote {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ) :
    ((loweringA P).lowerMulti
        ((FieldToModArithMont.lowering (montOf P)).blockLowerCom c)).denote
        (flatVal (fun {t} x => encA P (t := t) x) (FieldToModArithMont.mapVal (montOf P) V))
      = encL P (c.denote V) := by
  have hc1 : CoveredCom (FieldToModArithMont.Good (montOf P)) c :=
    coveredCom_mono _ _ (fun e hg => by
      rcases hg with (hop | hop | ⟨_, hop⟩ | hop) | hop | hop | hop | hop | ⟨hp, hop⟩ <;>
        simp only [FieldToModArithMont.Good, hop, FieldToModArithMont.GoodOp]
      exact fun _ => hp) c hc
  have hc2 : CoveredCom (GoodA P)
      ((FieldToModArithMont.lowering (montOf P)).blockLowerCom c) :=
    coveredCom_blockLowerCom _ (GoodOpA P) (GoodV P) (lowerExprBlock_covered P) c hc
  rw [modArithToJasminLimbsMont4_denote P _ hc2,
    FieldToModArithMont.fieldToModArithMont_denote _ c hc1 V]
  exact encA_transTy P _

/-- **Agreement with the one-step lowering.** On a `GoodV`-covered field program, the
    two-stage lowering and `FieldToJasminLimbsMont4.loweringL` produce the same limbs
    from the encoded inputs. -/
theorem fieldToJasminViaModArith_agreesV {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ) :
    ((loweringA P).lowerMulti
        ((FieldToModArithMont.lowering (montOf P)).blockLowerCom c)).denote
        (flatVal (fun {t} x => encA P (t := t) x) (FieldToModArithMont.mapVal (montOf P) V))
      = ((loweringL P).lowerMulti c).denote (flatVal (fun {t} x => encL P (t := t) x) V) :=
  (fieldToJasminViaModArith_denote P c hc V).trans
    (fieldToJasminLimbsMont4_denoteV P c hc V).symm

/-- Agreement with the one-step lowering on a `GoodM`-covered field program. -/
theorem fieldToJasminViaModArith_agrees {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodM P) c) (V : Valuation Γ) :
    ((loweringA P).lowerMulti
        ((FieldToModArithMont.lowering (montOf P)).blockLowerCom c)).denote
        (flatVal (fun {t} x => encA P (t := t) x) (FieldToModArithMont.mapVal (montOf P) V))
      = ((loweringL P).lowerMulti c).denote (flatVal (fun {t} x => encL P (t := t) x) V) :=
  fieldToJasminViaModArith_agreesV P c (coveredCom_mono _ _ (fun _ hg => Or.inl hg) c hc) V

end CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithToJasminLimbsMont4
