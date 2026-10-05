/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontInstances
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances

/-!
# The tower dialect lowered to 64-bit limbs in Montgomery form

`towerToLimbs P` is the composite multi-value lowering
`towerToField.comp (loweringL P)` from `towerDialect` to `jasminDialect`: a tower value at
the modulus `P.p` is represented by its `1`, `2`, `6` or `12` coordinates in `F_p`, each
carried by the `n` limbs of its Montgomery form. The block of a tower op is the limb
lowering of its `fieldDialect` block.

The composite's correctness is `MultiBlockLoweringData.comp_fundamental` from the block
square of `towerToField`, the block square of `loweringL P` on `GoodV P`, and the coverage
of every tower block at `P.p` by `GoodV P`. Coverage holds because every tower block binds
only `fAdd`, `fSub`, `fNeg`, `fMul` and `fConst` at the modulus of its op (`ArithAt`): the
emitters `emitT`, `emitVecT`, `stepN`, `I2.emit`, `SLP.emit`, `run6`, `I6.emit` hand on the
coverage of their continuations (`emitT_cov`, …, `I6.emit_cov`), and `blk2`, `blk6`,
`liftFpBlk`, `proj2Blk` and the constant block are covered (`towerLowerOp_cov`).

## Main definitions

* `ArithAt p`: the `fieldDialect` expressions binding `fAdd`, `fSub`, `fNeg`, `fMul` or
  `fConst` at `p`.
* `towerPrime`, `TowerAt q`: the modulus of a tower op, and the tower expressions at
  modulus `q`; `towerAtB` decides `TowerAt`-coverage of a program.
* `towerToLimbs P`, `towerLimbEnc P`: the composite lowering and its encoding.
* `bls12381Tower`, `bn254Tower`: the composite at the BLS12-381 base prime over six limbs
  (`MontInstances.bls12381`) and at the BN254 base prime over four limbs
  (`Mont4Instances.bn254`, a `LimbParams 4`).
* `tArrCtx N`, `arrCoords`, `tArrFlat`: the context of word arrays of `N` words, one per
  tower variable, and the coordinate limbs an array holds (coordinate `i` from word `i * n`).
* `towerBody P N`, `towerCom P N`: the tower program over word arrays: the loads of the
  coordinates of the input arrays (`loadT`), the composite lowering, and the stores of the
  coordinates of the result into the output array (`storeCoords`).
* `towerGoodB P N`: the decision of the side conditions of `towerCom_denote`.

## Main results

* `CoveredM.mono`: coverage is monotone in the predicate.
* `towerLowerOp_cov`: every tower block is `ArithAt`-covered at the modulus of its op.
* `towerToLimbs_blockSquare`: the block square of the composite at `P.p`.
* `towerToLimbs_fundamental`: every tower program at `P.p` lowers to a `jasminDialect`
  program mapping the limbs of the coordinates of its inputs to the limbs of the
  coordinates of its value; `bls12381Tower_fundamental` and `bn254Tower_fundamental` are
  its instances.
* `towerCom_denote`, `towerCom_denoteB`: for input arrays holding the Montgomery limbs of the
  coordinates of the inputs, the output array of `towerCom P N c` holds the Montgomery limbs
  of the coordinates of the value of `c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

/-! ## 1. Coverage -/

section Coverage

/-- Coverage of a multi-result program is monotone in the predicate. -/
theorem CoveredM.mono {d : Dialect} [DialectSignature d]
    {G G' : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop}
    (h : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), G e → G' e) :
    ∀ {Γ : Ctxt d} {ts : List d.Ty} (m : MultiReturnCom d Γ ts), CoveredM G m → CoveredM G' m
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, hc => ⟨h e hc.1, CoveredM.mono h body hc.2⟩

/-- The `fieldDialect` expressions that the tower blocks at `p` bind: `fAdd`, `fSub`,
    `fNeg`, `fMul` and `fConst` at `p`. -/
def ArithAt (p : Nat) {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) :
    Prop :=
  e.op = .fAdd p ∨ e.op = .fSub p ∨ e.op = .fNeg p ∨ e.op = .fMul p ∨
    ∃ c : ZMod p, e.op = .fConst p c

/-- An `ArithAt P.p` expression is `GoodV P`. -/
theorem goodV_of_arithAt {n : Nat} (P : LimbParams n) {Γ : Ctxt fieldDialect}
    {t : FieldTy} {e : Expr fieldDialect Γ t} (h : ArithAt P.p e) : GoodV P e := by
  rcases h with h | h | h | h | ⟨c, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨c, h⟩))

variable {p : Nat}

/-- `emitT` is `ArithAt p`-covered when its continuation is. -/
theorem emitT_cov {ts : List FieldTy} {n : Nat} (e : FExpr p n) :
    ∀ {Γ : Ctxt fieldDialect} (env : Fin n → Ctxt.Var Γ (.fp p))
      (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → MRC Γ' ts),
      (∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (w : Ctxt.Var Γ' (.fp p)),
        CoveredM (ArithAt p) (k r w)) →
      CoveredM (ArithAt p) (emitT e env k) := by
  induction e with
  | inp i => intro Γ env k hk; exact hk _ _
  | const c => intro Γ env k hk; exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rfl⟩))), hk _ _⟩
  | add a b iha ihb =>
    intro Γ env k hk
    exact iha env _ fun r₁ va => ihb _ _ fun r₂ vb => ⟨Or.inl rfl, hk _ _⟩
  | sub a b iha ihb =>
    intro Γ env k hk
    exact iha env _ fun r₁ va => ihb _ _ fun r₂ vb => ⟨Or.inr (Or.inl rfl), hk _ _⟩
  | neg a iha =>
    intro Γ env k hk
    exact iha env _ fun r₁ va => ⟨Or.inr (Or.inr (Or.inl rfl)), hk _ _⟩
  | mul a b iha ihb =>
    intro Γ env k hk
    exact iha env _ fun r₁ va => ihb _ _ fun r₂ vb => ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), hk _ _⟩

/-- `emitVecT` is `ArithAt p`-covered when its continuation is. -/
theorem emitVecT_cov {ts : List FieldTy} {n : Nat} :
    ∀ (m : Nat) (es : Fin m → FExpr p n) {Γ : Ctxt fieldDialect}
      (env : Fin n → Ctxt.Var Γ (.fp p))
      (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts),
      (∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (ws : Fin m → Ctxt.Var Γ' (.fp p)),
        CoveredM (ArithAt p) (k r ws)) →
      CoveredM (ArithAt p) (emitVecT m es env k)
  | 0, _, _, _, _, hk => hk _ _
  | m + 1, es, _, env, _, hk =>
    emitT_cov (es 0) env _ fun _ _ =>
      emitVecT_cov m (fun j => es j.succ) _ _ fun _ _ => hk _ _

/-- `stepN` is `ArithAt p`-covered when its continuation is. -/
theorem stepN_cov {ts : List FieldTy} {n m₁ : Nat} (es₁ : Fin m₁ → FExpr p n)
    (es₂ : Fin 2 → FExpr p m₁) {Γ : Ctxt fieldDialect} (env : Fin n → Ctxt.Var Γ (.fp p))
    (k : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F2 p Γ' → MRC Γ' ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (z : F2 p Γ'),
      CoveredM (ArithAt p) (k r z)) :
    CoveredM (ArithAt p) (stepN es₁ es₂ env k) :=
  emitVecT_cov m₁ es₁ env _ fun _ w => emitVecT_cov 2 es₂ w _ fun _ _ => hk _ _

/-- The `Fp2` emitter is `ArithAt p`-covered when its continuation is. -/
theorem I2.emit_cov (β ξ : Int) {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy}
    (ins : I2 k) (env : Fin k → F2 p Γ)
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F2 p Γ' → MRC Γ' ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (z : F2 p Γ'),
      CoveredM (ArithAt p) (kk r z)) :
    CoveredM (ArithAt p) (I2.emit p β ξ ins env kk) := by
  cases ins <;> exact stepN_cov _ _ _ kk hk

/-- An emitted straight-line program is `G`-covered when the instruction emitter and the
    continuation are. -/
theorem SLP.emit_cov {I : Nat → Type} {B : Ctxt fieldDialect → Type}
    (G : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
    (ren : ∀ {Γ Γ' : Ctxt fieldDialect}, Ren Γ Γ' → B Γ → B Γ')
    (em : ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy}, I k → (Fin k → B Γ) →
      ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → B Γ' → MRC Γ' ts) → MRC Γ ts)
    (hem : ∀ {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy} (ins : I k)
      (env : Fin k → B Γ) (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → B Γ' → MRC Γ' ts),
      (∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (z : B Γ'), CoveredM G (kk r z)) →
      CoveredM G (em ins env kk))
    {ts : List FieldTy} :
    ∀ {k m : Nat} (P : SLP I k m) {Γ : Ctxt fieldDialect} (env : Fin k → B Γ)
      (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → B Γ') → MRC Γ' ts),
      (∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (zs : Fin m → B Γ'), CoveredM G (kk r zs)) →
      CoveredM G (P.emit ren em env kk)
  | _, _, .ret _, _, _, _, hk => hk _ _
  | _, _, .step ins rest, _, env, _, hk =>
    hem ins env _ fun _ _ => SLP.emit_cov G ren em hem rest _ _ fun _ _ => hk _ _

/-- `run6` is `ArithAt p`-covered when its continuation is. -/
theorem run6_cov (β ξ : Int) {n : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy}
    (P : SLP I2 n 3) (e : Fin n → F2 p Γ)
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F6 p Γ' → MRC Γ' ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (z : F6 p Γ'),
      CoveredM (ArithAt p) (kk r z)) :
    CoveredM (ArithAt p) (run6 β ξ P e kk) :=
  SLP.emit_cov (B := F2 p) (ArithAt p) (fun r x => x.ren r) (em2 p β ξ)
    (fun ins env kk hk => I2.emit_cov β ξ ins env kk hk) P e _ fun _ _ => hk _ _

/-- The `Fp6` emitter is `ArithAt p`-covered when its continuation is. -/
theorem I6.emit_cov (β ξ : Int) {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy}
    (ins : I6 k) (env : Fin k → F6 p Γ)
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → F6 p Γ' → MRC Γ' ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (z : F6 p Γ'),
      CoveredM (ArithAt p) (kk r z)) :
    CoveredM (ArithAt p) (I6.emit p β ξ ins env kk) := by
  cases ins <;> exact run6_cov β ξ _ _ kk hk

/-- A block generated from an `Fp2` program is `ArithAt p`-covered. -/
theorem blk2_cov (β ξ : Int) {k m : Nat} (P : SLP I2 k m) :
    CoveredM (ArithAt p) (blk2 p β ξ P) :=
  SLP.emit_cov (B := F2 p) (ArithAt p) (fun r x => x.ren r) (em2 p β ξ)
    (fun ins env kk hk => I2.emit_cov β ξ ins env kk hk) P _ _ fun _ _ => trivial

/-- A block generated from an `Fp6` program is `ArithAt p`-covered. -/
theorem blk6_cov (β ξ : Int) {k : Nat} (P : SLP I6 k 2) :
    CoveredM (ArithAt p) (blk6 p β ξ P) :=
  SLP.emit_cov (B := F6 p) (ArithAt p) (fun r x => x.ren r) (em6 p β ξ)
    (fun ins env kk hk => I6.emit_cov β ξ ins env kk hk) P _ _ fun _ _ => trivial

/-- The lifting block is `ArithAt p`-covered. -/
theorem liftFpBlk_cov (p : Nat) : CoveredM (ArithAt p) (liftFpBlk p) :=
  emitVecT_cov 2 _ _ _ fun _ _ => trivial

end Coverage

/-! ## 2. The tower blocks at their modulus -/

section Ops

/-- The modulus of a tower op. -/
def towerPrime : TowerOp → Nat
  | .add _ p _ _ | .sub _ p _ _ | .neg _ p _ _ | .mul _ p _ _ | .square _ p _ _
  | .mulByNonResidue _ p _ _ | .lift _ p _ _ => p
  | .frobenius2 p _ | .sparseMul p _ _ | .proj2 p _ _ | .proj6 p _ _ _ | .proj12 p _ _ _
  | .constFp p _ => p

/-- **Every tower block is `ArithAt`-covered at the modulus of its op.** -/
theorem towerLowerOp_cov : ∀ op : TowerOp, CoveredM (ArithAt (towerPrime op)) (towerLowerOp op)
  | .add .two _ _ _ | .add .six _ _ _ | .sub .two _ _ _ | .sub .six _ _ _
  | .neg .two _ _ _ | .neg .six _ _ _ | .mul .two _ _ _ | .mul .six _ _ _
  | .square .two _ _ _ | .square .six _ _ _ | .mulByNonResidue .two _ _ _
  | .mulByNonResidue .six _ _ _ | .mulByNonResidue .twelve _ _ _ | .frobenius2 _ _
  | .sparseMul _ _ _ | .lift .six _ _ _ | .lift .twelve _ _ _ | .proj6 _ _ _ _
  | .proj12 _ _ _ _ => blk2_cov _ _ _
  | .add .twelve _ _ _ | .sub .twelve _ _ _ | .neg .twelve _ _ _ | .mul .twelve _ _ _
  | .square .twelve _ _ _ => blk6_cov _ _ _
  | .lift .two p _ _ => liftFpBlk_cov p
  | .proj2 _ _ _ => trivial
  | .constFp _ c => ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rfl⟩))), trivial⟩

/-- The tower expressions at modulus `q`. -/
def TowerAt (q : Nat) {Γ : Ctxt towerDialect} {t : TowerTy} (e : Expr towerDialect Γ t) :
    Prop :=
  towerPrime e.op = q

/-- The decision of `TowerAt q`-coverage. -/
def towerAtB (q : Nat) : {Γ : Ctxt towerDialect} → {t : TowerTy} → Com towerDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => (towerPrime e.op == q) && towerAtB q body

/-- A program accepted by `towerAtB q` is `TowerAt q`-covered. -/
theorem towerAtB_sound (q : Nat) :
    ∀ {Γ : Ctxt towerDialect} {t : TowerTy} (c : Com towerDialect Γ t),
      towerAtB q c = true → CoveredCom (TowerAt q) c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, h => by
    simp only [towerAtB, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, towerAtB_sound q body h.2⟩

end Ops

/-! ## 3. The composite lowering -/

section Composite

variable {n : Nat} (P : LimbParams n)

/-- **The tower dialect lowered to `n` limbs in Montgomery form**:
    `towerToField` followed by `loweringL P`. -/
@[reducible] def towerToLimbs : MultiBlockLoweringData towerDialect jasminDialect :=
  towerToField.comp (loweringL P)

/-- The encoding of the composite: the limbs of the Montgomery forms of the coordinates. -/
def towerLimbEnc : (towerToLimbs P).Enc :=
  MultiBlockLoweringData.compEnc towerToField (loweringL P) towerEnc
    (fun {t} x => encL P (t := t) x)

/-- Every tower block at `P.p` is `GoodV P`-covered. -/
theorem towerLowerOp_covGoodV {Γ : Ctxt towerDialect} {t : TowerTy}
    (e : Expr towerDialect Γ t) (h : TowerAt P.p e) :
    CoveredM (GoodV P) (towerToField.lowerOp e.op) :=
  CoveredM.mono (fun _ he => goodV_of_arithAt P (h ▸ he)) _ (towerLowerOp_cov e.op)

/-- **Block square of the composite** at every tower op at `P.p`. -/
theorem towerToLimbs_blockSquare : (towerToLimbs P).BlockSquare (towerLimbEnc P) (TowerAt P.p) :=
  MultiBlockLoweringData.comp_blockSquare towerToField (loweringL P) towerEnc
    (fun {t} x => encL P (t := t) x) (TowerAt P.p) (GoodV P)
    (fun e _ vals => opSquare_all e.op vals) (blockSquareV P) (towerLowerOp_covGoodV P)

/-- **Fundamental theorem of the tower-to-limbs lowering.** Every tower program whose ops
    are at `P.p` lowers to a `jasminDialect` program that maps the limbs of the Montgomery
    forms of the coordinates of the inputs to those of the coordinates of the value. -/
theorem towerToLimbs_fundamental {Γ : Ctxt towerDialect} {t : TowerTy}
    (c : Com towerDialect Γ t) (hc : CoveredCom (TowerAt P.p) c) (V : Ctxt.Valuation Γ) :
    ((towerToLimbs P).lowerMulti c).denote (flatVal (towerLimbEnc P) V)
      = flatVal (fun {t} x => encL P (t := t) x) (towerEnc (c.denote V)) :=
  MultiBlockLoweringData.comp_fundamental towerToField (loweringL P) towerEnc
    (fun {t} x => encL P (t := t) x) (TowerAt P.p) (GoodV P)
    (fun e _ vals => opSquare_all e.op vals) (blockSquareV P) (towerLowerOp_covGoodV P) c hc V

end Composite

/-! ## 4. BLS12-381 and BN254 -/

section Instances

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs

/-- The tower lowering at the BLS12-381 base prime over six limbs. -/
abbrev bls12381Tower : MultiBlockLoweringData towerDialect jasminDialect :=
  towerToLimbs MontInstances.bls12381

/-- The tower lowering at the BN254 base prime over four limbs. -/
abbrev bn254Tower : MultiBlockLoweringData towerDialect jasminDialect :=
  towerToLimbs Mont4Instances.bn254

/-- **Fundamental theorem of the BLS12-381 tower lowering.** -/
theorem bls12381Tower_fundamental {Γ : Ctxt towerDialect} {t : TowerTy}
    (c : Com towerDialect Γ t) (hc : CoveredCom (TowerAt MontInstances.bls12381.p) c)
    (V : Ctxt.Valuation Γ) :
    (bls12381Tower.lowerMulti c).denote (flatVal (towerLimbEnc MontInstances.bls12381) V)
      = flatVal (fun {t} x => encL MontInstances.bls12381 (t := t) x)
          (towerEnc (c.denote V)) :=
  towerToLimbs_fundamental MontInstances.bls12381 c hc V

/-- **Fundamental theorem of the BN254 tower lowering.** -/
theorem bn254Tower_fundamental {Γ : Ctxt towerDialect} {t : TowerTy}
    (c : Com towerDialect Γ t) (hc : CoveredCom (TowerAt Mont4Instances.bn254.p) c)
    (V : Ctxt.Valuation Γ) :
    (bn254Tower.lowerMulti c).denote (flatVal (towerLimbEnc Mont4Instances.bn254) V)
      = flatVal (fun {t} x => encL Mont4Instances.bn254 (t := t) x)
          (towerEnc (c.denote V)) :=
  towerToLimbs_fundamental Mont4Instances.bn254 c hc V

end Instances

/-! ## 5. The tower program over word arrays -/

section Arrays

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 MC bindK bindK_denote
  eConst Pres Pres.id Pres.comp)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)

variable {N : Nat}

/-- The context of word arrays of `N` words, one for each variable of a tower context. -/
@[reducible] def tArrCtx (N : Nat) : Ctxt towerDialect → Ctxt jasminDialect
  | [] => []
  | _ :: Γ => arrTy N :: tArrCtx N Γ

/-- The coordinates held by the array `a`: `n` limbs for each variable of `Δ`, from
    index `j` on. -/
def arrCoords (n : Nat) (a : Fin N → BitVec 64) : (Δ : Ctxt fieldDialect) → Nat →
    Ctxt.Valuation (ctxFlat (mapTysL n) Δ)
  | [], _ => .nil
  | _ :: Δ, j => hvAppend (arrLimbs a n j) (arrCoords n a Δ (j + n))

/-- The coordinate limbs of every array of a valuation of `tArrCtx N Γ`, appended: an array
    of a variable of type `t` holds the coordinates `towerMapTys t` from index `0` on. -/
def tArrFlat (n : Nat) : {Γ : Ctxt towerDialect} → Ctxt.Valuation (tArrCtx N Γ) →
    Ctxt.Valuation (ctxFlat (fun t => ctxFlat (mapTysL n) (towerMapTys t)) Γ)
  | [], .nil => .nil
  | t :: _, .cons a A => hvAppend (arrCoords n a (towerMapTys t) 0) (tArrFlat n A)

/-- The loads of the coordinates `Δf` of the array `a` from index `j`, `n` limbs each; the
    continuation receives the renaming of the context and the renaming of the coordinate
    limbs onto the loaded words. -/
def loadCoords (n : Nat) {bs : List JasminTy} : {Δ : Ctxt jasminDialect} →
    (Δf : Ctxt fieldDialect) → Nat → Ctxt.Var Δ (arrTy N) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (ctxFlat (mapTysL n) Δf) Δ' →
      MC Δ' bs) → MC Δ bs
  | _, [], _, _, k => k (fun v => v) (fun v => nomatch v)
  | _, _ :: Δf, j, a, k =>
      loadLimbs n j a fun r₁ hx =>
      loadCoords n Δf (j + n) (r₁ a) fun r₂ hr =>
        k (fun v => r₂ (r₁ v)) (appendHom (fun w => r₂ (hx w)) hr)

theorem loadCoords_denote (n : Nat) {bs : List JasminTy} (hN : N < 2 ^ 64) :
    ∀ {Δ : Ctxt jasminDialect} (Δf : Ctxt fieldDialect) (j : Nat) (a : Ctxt.Var Δ (arrTy N))
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (ctxFlat (mapTysL n) Δf) Δ' → MC Δ' bs)
      (W : Ctxt.Valuation Δ) (G : ListDenote bs), j + Δf.length * n ≤ N →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ')
          (h : Ctxt.Hom (ctxFlat (mapTysL n) Δf) Δ') (W' : Ctxt.Valuation Δ'), Pres r W W' →
          pullV h W' = arrCoords n (a.lookup W) Δf j → (k r h).denote W' = G) →
      (loadCoords n Δf j a k).denote W = G
  | _, [], _, _, _, W, _, _, hk => hk (fun v => v) _ W (Pres.id W) rfl
  | _, u :: Δf, j, a, k, W, G, hj, hk => by
      have hl : (u :: Δf).length * n = Δf.length * n + n := by
        rw [List.length_cons, Nat.succ_mul]
      refine loadLimbs_denote n j a _ W G (by omega) fun r₁ hx W₁ h₁ hhx => ?_
      refine loadCoords_denote n hN Δf (j + n) _ _ W₁ G (by omega)
        fun r₂ hr W₂ h₂ hhr => ?_
      refine hk _ _ W₂ (Pres.comp h₁ h₂) ?_
      rw [pullV_appendHom, hhr, pullV_comp_pres h₂ hx, hhx, h₁ a]
      rfl

/-- The loads of the coordinates of every array of `tArrCtx N Γ`, through the renaming
    `src`; the continuation receives the renaming of the context and the renaming of the
    flattened coordinate limbs onto the loaded words. -/
def loadT (n : Nat) {bs : List JasminTy} : (Γ : Ctxt towerDialect) → {Δ : Ctxt jasminDialect} →
    Ctxt.Hom (tArrCtx N Γ) Δ →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
      Ctxt.Hom (ctxFlat (fun t => ctxFlat (mapTysL n) (towerMapTys t)) Γ) Δ' → MC Δ' bs) →
    MC Δ bs
  | [], _, _, k => k (fun v => v) (fun v => nomatch v)
  | t :: Γ, _, src, k =>
      loadCoords n (towerMapTys t) 0 (src .here) fun r₁ hx =>
      loadT n Γ (fun v => r₁ (src (.there v))) fun r₂ hr =>
        k (fun v => r₂ (r₁ v)) (appendHom (fun w => r₂ (hx w)) hr)

theorem loadT_denote (n : Nat) {bs : List JasminTy} (hN : N < 2 ^ 64) :
    ∀ (Γ : Ctxt towerDialect) {Δ : Ctxt jasminDialect} (src : Ctxt.Hom (tArrCtx N Γ) Δ)
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (ctxFlat (fun t => ctxFlat (mapTysL n) (towerMapTys t)) Γ) Δ' → MC Δ' bs)
      (W : Ctxt.Valuation Δ) (G : ListDenote bs),
      (∀ s ∈ Γ, (towerMapTys s).length * n ≤ N) →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ')
          (h : Ctxt.Hom (ctxFlat (fun t => ctxFlat (mapTysL n) (towerMapTys t)) Γ) Δ')
          (W' : Ctxt.Valuation Δ'), Pres r W W' → pullV h W' = tArrFlat n (pullV src W) →
          (k r h).denote W' = G) →
      (loadT n Γ src k).denote W = G
  | [], _, _, _, W, _, _, hk => hk (fun v => v) _ W (Pres.id W) rfl
  | t :: Γ, _, src, k, W, G, hfit, hk => by
      refine loadCoords_denote n hN (towerMapTys t) 0 _ _ W G
        (by have := hfit t (by simp); omega) fun r₁ hx W₁ h₁ hhx => ?_
      refine loadT_denote n hN Γ _ _ W₁ G (fun s hs => hfit s (List.mem_cons_of_mem t hs))
        fun r₂ hr W₂ h₂ hhr => ?_
      refine hk _ _ W₂ (Pres.comp h₁ h₂) ?_
      rw [pullV_appendHom, hhr, pullV_comp_pres h₂ hx, hhx,
        pullV_comp_pres h₁ (fun v => src (.there v))]
      rfl

/-- The stores of the limbs `h` into the array `o` from index `j`; the continuation receives
    the renaming of the context and the last stored array. -/
def storeLimbsK {bs : List JasminTy} : {Δ : Ctxt jasminDialect} → (m j : Nat) →
    Ctxt.Var Δ (arrTy N) → Ctxt.Hom (Rn m) Δ →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Var Δ' (arrTy N) → MC Δ' bs) → MC Δ bs
  | _, 0, _, o, _, k => k (fun v => v) o
  | _, m + 1, j, o, h, k =>
      bindK (eConst j) fun r₁ i =>
      bindK (eStore (r₁ o) i (r₁ (h .here))) fun r₂ o' =>
      storeLimbsK m (j + 1) o' (fun w => r₂ (r₁ (h (.there w)))) fun r₃ o'' =>
        k (fun v => r₃ (r₂ (r₁ v))) o''

theorem storeLimbsK_denote {bs : List JasminTy} (hN : N < 2 ^ 64) :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (o : Ctxt.Var Δ (arrTy N)) (h : Ctxt.Hom (Rn m) Δ)
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Var Δ' (arrTy N) → MC Δ' bs)
      (W : Ctxt.Valuation Δ) (G : ListDenote bs), j + m ≤ N →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (o' : Ctxt.Var Δ' (arrTy N))
          (W' : Ctxt.Valuation Δ'), Pres r W W' →
          o'.lookup W' = storeVal (o.lookup W) j (pullV h W) → (k r o').denote W' = G) →
      (storeLimbsK m j o h k).denote W = G
  | _, 0, _, o, _, _, W, _, _, hk => hk (fun v => v) o W (Pres.id W) rfl
  | _, m + 1, j, o, h, k, W, G, hjm, hk => by
      refine bindK_denote _ _ W G fun r₁ i W₁ h₁ hi => ?_
      refine bindK_denote _ _ W₁ G fun r₂ o' W₂ h₂ ho => ?_
      refine storeLimbsK_denote hN m (j + 1) o' _ _ W₂ G (by omega)
        fun r₃ o'' W₃ h₃ ho'' => ?_
      refine hk _ o'' W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) ?_
      have e : (eStore (r₁ o) i (r₁ (h .here))).denote W₁
          = stackSet ((r₁ o).lookup W₁) (i.lookup W₁).toNat ((r₁ (h .here)).lookup W₁) := rfl
      have e₀ : (i.lookup W₁).toNat = j := by
        rw [hi]
        exact (BitVec.toNat_ofNat j 64).trans (Nat.mod_eq_of_lt (by omega))
      rw [ho'', ho, e, e₀, h₁ o, h₁ (h .here),
        pullV_comp_pres h₂ (fun w => r₁ (h (.there w))),
        pullV_comp_pres h₁ (fun w => h (.there w))]
      rfl

/-- The stores of the coordinates `Δf` into the array `o` from index `j`, `n` limbs each,
    returning the last stored array. -/
def storeCoords (n : Nat) : {Δ : Ctxt jasminDialect} → (Δf : Ctxt fieldDialect) → Nat →
    Ctxt.Var Δ (arrTy N) → Ctxt.Hom (ctxFlat (mapTysL n) Δf) Δ → MC Δ [arrTy N]
  | _, [], _, o, _ => .ret (.cons o .nil)
  | _, _ :: Δf, j, o, h =>
      storeLimbsK n j o (fun w => h (inlHom (ctxFlat (mapTysL n) Δf) w)) fun r o' =>
        storeCoords n Δf (j + n) o' (fun w => r (h (inrHom (Rn n) w)))

/-- The array `o` with the coordinate limbs `L` of `Δf` written from index `j`. -/
def storeCoordsVal (n : Nat) (o : Fin N → BitVec 64) : (Δf : Ctxt fieldDialect) → Nat →
    Ctxt.Valuation (ctxFlat (mapTysL n) Δf) → Fin N → BitVec 64
  | [], _, _ => o
  | _ :: Δf, j, L =>
      storeCoordsVal n
        (storeVal o j (pullV (fun w => inlHom (ctxFlat (mapTysL n) Δf) w) L)) Δf (j + n)
        (pullV (fun w => inrHom (Rn n) w) L)

theorem storeCoords_denote (n : Nat) (hN : N < 2 ^ 64) :
    ∀ {Δ : Ctxt jasminDialect} (Δf : Ctxt fieldDialect) (j : Nat) (o : Ctxt.Var Δ (arrTy N))
      (h : Ctxt.Hom (ctxFlat (mapTysL n) Δf) Δ) (W : Ctxt.Valuation Δ),
      j + Δf.length * n ≤ N →
      (storeCoords n Δf j o h).denote W
        = .cons (storeCoordsVal n (o.lookup W) Δf j (pullV h W)) .nil
  | _, [], _, _, _, _, _ => rfl
  | _, u :: Δf, j, o, h, W, hj => by
      have hl : (u :: Δf).length * n = Δf.length * n + n := by
        rw [List.length_cons, Nat.succ_mul]
      refine storeLimbsK_denote hN n j o _ _ W _ (by omega) fun r o' W' hr ho' => ?_
      rw [storeCoords_denote n hN Δf (j + n) o' _ W' (by omega), ho',
        pullV_comp_pres hr (fun w => h (inrHom (Rn n) w))]
      simp only [storeCoordsVal, ← pullV_comp]

theorem arrLimbs_congr {a b : Fin N → BitVec 64} :
    ∀ (m j : Nat), (∀ i, j ≤ i → i < j + m → stackGet a i = stackGet b i) →
      arrLimbs a m j = arrLimbs b m j
  | 0, _, _ => rfl
  | m + 1, j, h => by
      simp only [arrLimbs, h j (Nat.le_refl j) (by omega),
        arrLimbs_congr m (j + 1) fun i h1 h2 => h i (by omega) (by omega)]

theorem storeCoordsVal_get_lt (n i : Nat) :
    ∀ (o : Fin N → BitVec 64) (Δf : Ctxt fieldDialect) (j : Nat)
      (L : Ctxt.Valuation (ctxFlat (mapTysL n) Δf)), i < j → j + Δf.length * n ≤ N →
      stackGet (storeCoordsVal n o Δf j L) i = stackGet o i
  | _, [], _, _, _, _ => rfl
  | o, u :: Δf, j, L, hij, hj => by
      have hl : (u :: Δf).length * n = Δf.length * n + n := by
        rw [List.length_cons, Nat.succ_mul]
      simp only [storeCoordsVal]
      rw [storeCoordsVal_get_lt n i _ Δf (j + n) _ (by omega) (by omega),
        storeVal_get_lt o i j _ hij (by omega)]

/-- A valuation of an appended context is an appended valuation. -/
theorem valuation_append_split {d : Dialect} [TyDenote d.Ty] :
    ∀ (xs : Ctxt d) {ys : Ctxt d} (L : Ctxt.Valuation (xs ++ ys)),
      ∃ (A : Ctxt.Valuation xs) (B : Ctxt.Valuation ys), L = hvAppend A B
  | [], _, L => ⟨.nil, L, rfl⟩
  | _ :: xs, _, .cons a L => by
      obtain ⟨A, B, rfl⟩ := valuation_append_split xs L
      exact ⟨.cons a A, B, rfl⟩

/-- The coordinates written by `storeCoordsVal` are read back by `arrCoords`. -/
theorem arrCoords_storeCoordsVal (n : Nat) :
    ∀ (o : Fin N → BitVec 64) (Δf : Ctxt fieldDialect) (j : Nat)
      (L : Ctxt.Valuation (ctxFlat (mapTysL n) Δf)), j + Δf.length * n ≤ N →
      arrCoords n (storeCoordsVal n o Δf j L) Δf j = L
  | _, [], _, .nil, _ => rfl
  | o, u :: Δf, j, L, hj => by
      have hl : (u :: Δf).length * n = Δf.length * n + n := by
        rw [List.length_cons, Nat.succ_mul]
      obtain ⟨A, B, rfl⟩ := valuation_append_split (Rn n) (ys := ctxFlat (mapTysL n) Δf) L
      simp only [storeCoordsVal, arrCoords, pullV_inlHom, pullV_inrHom]
      rw [arrCoords_storeCoordsVal n _ Δf (j + n) B (by omega),
        arrLimbs_congr n j (fun i h1 _ =>
          storeCoordsVal_get_lt n i _ Δf (j + n) B (by omega) (by omega)),
        arrLimbs_storeVal o j A (by omega)]

variable {n : Nat} (P : LimbParams n)

/-- **The lowered tower program over word arrays, as a multi-result program.** Over the
    context `tArrCtx N Γ ++ [arrTy N]` (an array of `N` words for each source variable, then
    the output array): the loads of the coordinates of every input array, the composite
    lowering `(towerToLimbs P).lowerR` of `c` on the loaded limbs, and the stores of the
    coordinate limbs of the result into the output array; the program returns the last
    stored array. -/
def towerBody (N : Nat) {Γ : Ctxt towerDialect} {t : TowerTy} (c : Com towerDialect Γ t) :
    MC (tArrCtx N Γ ++ [arrTy N]) [arrTy N] :=
  loadT n Γ (fun v => inlHom [arrTy N] v) fun r h =>
    (towerToLimbs P).lowerR h c fun r₂ vs =>
      storeCoords n (towerMapTys t) 0 (r₂ (r (inrHom (tArrCtx N Γ) .here))) (hvToHom vs)

/-- **The lowered tower program over word arrays.** -/
def towerCom (N : Nat) {Γ : Ctxt towerDialect} {t : TowerTy} (c : Com towerDialect Γ t) :
    Com jasminDialect (tArrCtx N Γ ++ [arrTy N]) (arrTy N) :=
  (towerBody P N c).toComHead

theorem towerBody_denote (N : Nat) (hN : N < 2 ^ 64) {Γ : Ctxt towerDialect} {t : TowerTy}
    (hfit : ∀ s ∈ Γ, (towerMapTys s).length * n ≤ N) (c : Com towerDialect Γ t)
    (hc : CoveredCom (TowerAt P.p) c) (V : Ctxt.Valuation Γ)
    (A : Ctxt.Valuation (tArrCtx N Γ)) (o : Fin N → BitVec 64)
    (ht : (towerMapTys t).length * n ≤ N)
    (hA : tArrFlat n A = flatVal (towerLimbEnc P) V) :
    (towerBody P N c).denote (hvAppend A (.cons o .nil))
      = .cons (storeCoordsVal n o (towerMapTys t) 0 (towerLimbEnc P (c.denote V))) .nil := by
  refine loadT_denote n hN Γ _ _ _ _ hfit fun r h W' hr hh => ?_
  refine (towerToLimbs P).lowerR_denote_on (towerLimbEnc P) (TowerAt P.p)
    (towerToLimbs_blockSquare P) h c _ W' V _ hc ?_ fun r₂ vs W'' h₂ hvs => ?_
  · refine hh.trans ?_
    rw [pullV_inlHom]
    exact hA
  · have e₁ : pullV (fun w => hvToHom vs w) W'' = towerLimbEnc P (c.denote V) :=
      (pullV_hvToHom W'' vs).trans hvs
    have e₂ : (r₂ (r (inrHom (tArrCtx N Γ) .here))).lookup W'' = o := by
      rw [h₂, hr, lookup_inrHom]
      rfl
    refine (storeCoords_denote n hN _ 0 _ _ W'' (by omega)).trans ?_
    rw [e₂]
    exact congrArg (fun x => (HVector.cons (storeCoordsVal n o (towerMapTys t) 0 x) HVector.nil
      : ListDenote [arrTy N])) e₁

/-- **Denotation of the lowered tower program over word arrays.** For a tower program `c`
    whose ops are at `P.p`, with every coordinate block inside the arrays of `N < 2 ^ 64`
    words, and input arrays holding the Montgomery limbs of the coordinates of the values of
    `V`, the output array of `towerCom P N c` holds the Montgomery limbs of the coordinates of
    `c.denote V`, whatever it held on entry. -/
theorem towerCom_denote (N : Nat) (hN : N < 2 ^ 64) {Γ : Ctxt towerDialect} {t : TowerTy}
    (hfit : ∀ s ∈ Γ, (towerMapTys s).length * n ≤ N) (ht : (towerMapTys t).length * n ≤ N)
    (c : Com towerDialect Γ t) (hc : CoveredCom (TowerAt P.p) c) (V : Ctxt.Valuation Γ)
    (A : Ctxt.Valuation (tArrCtx N Γ)) (o : Fin N → BitVec 64)
    (hA : tArrFlat n A = flatVal (towerLimbEnc P) V) :
    arrCoords n ((towerCom P N c).denote (hvAppend A (.cons o .nil))) (towerMapTys t) 0
      = towerLimbEnc P (c.denote V) := by
  rw [towerCom, MultiReturnCom.toComHead_denote, towerBody_denote P N hN hfit c hc V A o ht hA]
  exact arrCoords_storeCoordsVal n o _ 0 _ (by omega)

/-- The decision of the side conditions of `towerCom_denote`: the ops of `c` are at `P.p`,
    `N < 2 ^ 64`, and the coordinates of every source variable and of the result fit in
    `N` words. -/
def towerGoodB (N : Nat) {Γ : Ctxt towerDialect} {t : TowerTy} (c : Com towerDialect Γ t) :
    Bool :=
  towerAtB P.p c && decide (N < 2 ^ 64)
    && Γ.all (fun s => decide ((towerMapTys s).length * n ≤ N))
    && decide ((towerMapTys t).length * n ≤ N)

theorem towerGoodB_sound (N : Nat) {Γ : Ctxt towerDialect} {t : TowerTy}
    (c : Com towerDialect Γ t) (h : towerGoodB P N c = true) :
    CoveredCom (TowerAt P.p) c ∧ N < 2 ^ 64 ∧ (∀ s ∈ Γ, (towerMapTys s).length * n ≤ N)
      ∧ (towerMapTys t).length * n ≤ N := by
  simp only [towerGoodB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨towerAtB_sound P.p c h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **Denotation of the lowered tower program on a program accepted by `towerGoodB`.** -/
theorem towerCom_denoteB (N : Nat) {Γ : Ctxt towerDialect} {t : TowerTy}
    (c : Com towerDialect Γ t) (hc : towerGoodB P N c = true) (V : Ctxt.Valuation Γ)
    (A : Ctxt.Valuation (tArrCtx N Γ)) (o : Fin N → BitVec 64)
    (hA : tArrFlat n A = flatVal (towerLimbEnc P) V) :
    arrCoords n ((towerCom P N c).denote (hvAppend A (.cons o .nil))) (towerMapTys t) 0
      = towerLimbEnc P (c.denote V) :=
  have h := towerGoodB_sound P N c hc
  towerCom_denote P N h.2.1 h.2.2.1 h.2.2.2 c h.1 V A o hA

end Arrays

end CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs
