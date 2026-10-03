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

## Main results

* `CoveredM.mono`: coverage is monotone in the predicate.
* `towerLowerOp_cov`: every tower block is `ArithAt`-covered at the modulus of its op.
* `towerToLimbs_blockSquare`: the block square of the composite at `P.p`.
* `towerToLimbs_fundamental`: every tower program at `P.p` lowers to a `jasminDialect`
  program mapping the limbs of the coordinates of its inputs to the limbs of the
  coordinates of its value; `bls12381Tower_fundamental` and `bn254Tower_fundamental` are
  its instances.
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
theorem emitT_cov {ts : List FieldTy} {n : Nat} (e : TExpr p n) :
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
    ∀ (m : Nat) (es : Fin m → TExpr p n) {Γ : Ctxt fieldDialect}
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
theorem stepN_cov {ts : List FieldTy} {n m₁ : Nat} (es₁ : Fin m₁ → TExpr p n)
    (es₂ : Fin 2 → TExpr p m₁) {Γ : Ctxt fieldDialect} (env : Fin n → Ctxt.Var Γ (.fp p))
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

end CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs
