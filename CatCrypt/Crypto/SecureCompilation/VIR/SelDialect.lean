/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecEmbed

/-!
# Unsigned minimum and half-width multiply beside the scalar dialect

`selOps` is an operation set over the type alphabet `JasminTy` with two operations on
`w`-bit registers: `umin w`, the unsigned minimum `RangeDomain.umin`, and `mulu w`, the
product `halfProd` of the two operands with their upper halves cleared. At `w = 64` the
second is the product of the zero-extended low dwords, the lane function of `vpmuludq`.
Under the range fact that both operands are below `2 ^ (w / 2)` it is the full product.

`jasminSel` is the operation sum `Dialect.opSum jasminDialect selOps`. Its leakage model
`jasminSelLeak M` gives a scalar operation the class of the model `M` of `jasminDialect`
and makes the two operations quiet. `ofScalar` is the inclusion of a program of
`jasminDialect`, an instance of `X86VecEmbed.relabel`.

`selTile d` is the lane-wise form of the two operations over the type alphabet
`d.Ty ⊕ TileTy` of `scalarTile d`: `tileMinu n w` and `tileMulu n w` on tiles of `n` lanes of
`w` bits. `tileSel d` is the operation sum `Dialect.opSum (scalarTile d) (selTile d)`, with
the trip counter, the branch bit and the call environment of `scalarTile d`; its leakage
model `tileSelLeak M` extends `scalarTileLeak d M` with the two operations quiet.
`ofScalarTile` is the inclusion of a program of `scalarTile d`.

## Main definitions

* `halfProd`: the product of two words with their upper halves cleared.
* `SelOp`, `selOps`, `selDenote`: the operation set and its denotation.
* `jasminSel`, `jasminSelDenote`, `jasminSelLeak`: the operation sum with `jasminDialect`,
  its denotation on programs and its leakage model.
* `uminE`, `muluE`: the two expressions of `jasminSel`.
* `ofScalarExpr`, `ofScalar`: an expression and a program of `jasminDialect` in `jasminSel`.
* `SelTileOp`, `selTile`, `tileMinuApply`, `tileMuluApply`: the lane-wise operation set.
* `tileSel`, `tileSelDenote`, `tileSelLeak`: the operation sum with `scalarTile d`, its
  denotation and its leakage model.
* `ofScalarTileExpr`, `ofScalarTile`: an expression and a program of `scalarTile d` in
  `tileSel d`.
* `jasminTileSel`, `jasminTileSelDenote`: the instance of `tileSel` at `jasminDialect`.

## Main results

* `halfProd_eq_mul`: below `2 ^ (w / 2)` the half-width product is the product.
* `mul_eq_halfProd`: the 64-bit instance, from `RangeDomain.mul_eq_mul_setWidth32`.
* `halfProd_eq_muludq`: at 64 bits the half-width product is the lane function of
  `LOp.muludq`.
* `uminE_denote`, `muluE_denote`: the values of the two expressions.
* `jasminSel_opLeak_inr`, `jasminSel_opLeak_inl`: the two operations emit no event, a scalar
  operation the events of the scalar model.
* `jasminSel_nfCTRel_of_levelCheck'`: a program the level checker accepts is constant time
  relative to its runs.
* `ofScalar_denote`, `ofScalar_leakRun`, `ofScalar_levelCheck'`, `ofScalar_nfCTRel`: the
  inclusion preserves the denotation, the leakage run and the result of the level checker.
* `tileMinu_lane`, `tileMulu_lane`: lane `j` of a tile operation is the scalar operation on
  lane `j` of the operands.
* `tileSel_opLeak_inr`, `tileSel_opLeak_inl`, `tileSel_nfCTRel_of_levelCheck'`: the events
  of `tileSel d` and the soundness of its level checker.
* `ofScalarTile_denote`, `ofScalarTile_leakRunM`, `ofScalarTile_levelCheck'`: the inclusion
  of `scalarTile d` preserves the denotation, the leakage run and the result of the level
  checker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SelDialect

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecEmbed
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (LOp)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (umin mul_eq_mul_setWidth32)
open Ctxt (Var Valuation)

/-! ## 1. The half-width product -/

/-- The product of two `w`-bit words with their upper halves cleared: the product of the low
    `w / 2` bits of each, zero-extended to `w` bits. -/
def halfProd {w : Nat} (a b : BitVec w) : BitVec w :=
  (a.setWidth (w / 2)).setWidth w * (b.setWidth (w / 2)).setWidth w

/-- **The half-width product of operands below `2 ^ (w / 2)` is their product.** -/
theorem halfProd_eq_mul {w : Nat} (a b : BitVec w) (ha : a.toNat < 2 ^ (w / 2))
    (hb : b.toNat < 2 ^ (w / 2)) : halfProd a b = a * b := by
  have key : ∀ x : BitVec w, x.toNat < 2 ^ (w / 2) → (x.setWidth (w / 2)).setWidth w = x := by
    intro x hx
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt x.isLt]
  unfold halfProd
  rw [key a ha, key b hb]

/-- At 64 bits the half-width product is the product of the zero-extended low dwords. -/
theorem halfProd_word64 (a b : BitVec 64) :
    halfProd a b = (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 := rfl

/-- **A 64-bit product of operands below `2 ^ 32` is the half-width product.** -/
theorem mul_eq_halfProd (a b : BitVec 64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    a * b = halfProd a b :=
  mul_eq_mul_setWidth32 a b ha hb

/-- At 64 bits the half-width product is the lane function of `LOp.muludq`. -/
theorem halfProd_eq_muludq (x y : BitVec 64) : halfProd x y = LOp.muludq.apply x y := rfl

/-- The unsigned minimum is the lane function of `LOp.minu`. -/
theorem umin_eq_minu {L : Nat} (x y : BitVec L) : umin x y = LOp.minu.apply x y := rfl

/-! ## 2. The operation set -/

/-- The unsigned minimum and the half-width multiply on `w`-bit registers. -/
inductive SelOp where
  /-- The unsigned minimum of two `w`-bit registers. -/
  | umin (w : Nat)
  /-- The product of the low halves of two `w`-bit registers; `w` is even. -/
  | mulu (w : Nat)
  deriving DecidableEq

/-- The operation set of the unsigned minimum and the half-width multiply over the type
    alphabet `JasminTy`. -/
@[reducible] def selOps : Dialect := { Op := SelOp, Ty := JasminTy }

/-- The signature of the two operations: two `w`-bit registers to a `w`-bit register. -/
instance instDialectSignatureSelOps : DialectSignature selOps where
  sig
    | .umin w => [.reg w, .reg w]
    | .mulu w => [.reg w, .reg w]
  ret
    | .umin w => .reg w
    | .mulu w => .reg w

/-- The value of the two operations: `RangeDomain.umin` and `halfProd`. -/
instance selDenote : DialectDenote selOps where
  denote
    | .umin w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        (umin a b : BitVec w)
    | .mulu w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        (halfProd a b : BitVec w)

/-- The value of `umin w`. -/
@[simp] theorem selDenote_umin (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := selOps) (.umin w) (.cons a (.cons b .nil)) = umin a b := rfl

/-- The value of `mulu w`. -/
@[simp] theorem selDenote_mulu (w : Nat) (a b : BitVec w) :
    DialectDenote.denote (d := selOps) (.mulu w) (.cons a (.cons b .nil)) = halfProd a b := rfl

/-! ## 3. The operation sum with `jasminDialect` -/

/-- The operation sum of `jasminDialect` and `selOps` over `JasminTy`. -/
abbrev jasminSel : Dialect.{0, 0} := Dialect.opSum jasminDialect selOps

/-- The signature of `jasminSel`: the signature of the summand. -/
instance instDialectSignatureJasminSel : DialectSignature jasminSel where
  sig
    | .inl o => DialectSignature.sig (d := jasminDialect) o
    | .inr o => DialectSignature.sig (d := selOps) o
  ret
    | .inl o => DialectSignature.ret (d := jasminDialect) o
    | .inr o => DialectSignature.ret (d := selOps) o

/-- The value of an operation of `jasminSel`: the value in its summand. -/
instance instDialectDenoteJasminSel : DialectDenote jasminSel where
  denote
    | .inl o => fun args => DialectDenote.denote (d := jasminDialect) o args
    | .inr o => fun args => DialectDenote.denote (d := selOps) o args

/-- The trip counter of `jasminSel` is the 64-bit register. -/
instance instHasWord64JasminSel : HasWord64 jasminSel where
  word := HasWord64.word (d := jasminDialect)
  toNat := HasWord64.toNat (d := jasminDialect)
  ofNat := HasWord64.ofNat (d := jasminDialect)

/-- The bit of `jasminSel` is the 1-bit register. -/
instance instHasBoolBitJasminSel : HasBoolBit jasminSel where
  bit := HasBitType.bit (d := jasminDialect)
  toBool := HasBoolBit.toBool (d := jasminDialect)

/-- `jasminSel` denotes calls in the empty environment. -/
instance instCallDenoteJasminSel : CallDenote jasminSel := ⟨.empty⟩

/-- The denotation of `jasminSel` on programs: both summands are total. -/
@[instance_reducible] def jasminSelDenote : DialectDenoteM jasminSel Option :=
  instDialectDenoteMOptionOfPure jasminSel

/-- A scalar operation has in `jasminSel` its value in `jasminDialect`. -/
@[simp] theorem jasminSel_denote_inl (o : JasminOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) o)) :
    DialectDenote.denote (d := jasminSel) (.inl o) args =
      DialectDenote.denote (d := jasminDialect) o args := rfl

/-- An operation of `selOps` has in `jasminSel` its value in `selOps`. -/
@[simp] theorem jasminSel_denote_inr (o : SelOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := selOps) o)) :
    DialectDenote.denote (d := jasminSel) (.inr o) args =
      DialectDenote.denote (d := selOps) o args := rfl

/-! ## 4. The leakage model -/

/-- The leakage model of `jasminSel` over a model `M` of `jasminDialect`: a scalar
    operation has its class in `M`, the unsigned minimum and the half-width multiply are
    quiet, and a value has the reading of `M`. -/
def jasminSelLeak (M : LeakModel jasminDialect) : LeakModel jasminSel where
  kind := Sum.elim M.kind (fun _ => .quiet)
  valNat := M.valNat

/-- A scalar operation has the class `M` gives it. -/
@[simp] theorem jasminSelLeak_kind_inl (M : LeakModel jasminDialect) (op : JasminOp) :
    (jasminSelLeak M).kind (.inl op) = M.kind op := rfl

/-- An operation of `selOps` is quiet. -/
@[simp] theorem jasminSelLeak_kind_inr (M : LeakModel jasminDialect) (op : SelOp) :
    (jasminSelLeak M).kind (.inr op) = .quiet := rfl

/-- The readings of a list of values are those of `M`. -/
theorem jasminSel_valsNat (M : LeakModel jasminDialect) :
    ∀ {ts : List JasminTy} (vals : HVector (fun t => ⟦t⟧) ts),
      valsNat (jasminSelLeak M) vals = valsNat M vals
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show M.valNat _ x :: valsNat (jasminSelLeak M) xs = M.valNat _ x :: valsNat M xs
      rw [jasminSel_valsNat M xs]

/-- **A scalar operation emits in `jasminSel` the events it emits in `jasminDialect`.** -/
theorem jasminSel_opLeak_inl (M : LeakModel jasminDialect) (op : JasminOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    opLeak (jasminSelLeak M) (.inl op) vals = opLeak M op vals := by
  unfold opLeak
  rw [jasminSelLeak_kind_inl, jasminSel_valsNat M vals]

/-- **The unsigned minimum and the half-width multiply emit no event.** -/
theorem jasminSel_opLeak_inr (M : LeakModel jasminDialect) (op : SelOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := selOps) op)) :
    opLeak (jasminSelLeak M) (.inr op) vals = [] := rfl

/-- The constraint of a scalar operation is its constraint in `M`. -/
@[simp] theorem jasminSel_opAccepts_inl (M : LeakModel jasminDialect) (op : JasminOp)
    (ls : List SecretLevel) :
    opAccepts (jasminSelLeak M) (.inl op) ls = opAccepts M op ls := rfl

/-- The level checker places no constraint on an operation of `selOps`. -/
@[simp] theorem jasminSel_opAccepts_inr (M : LeakModel jasminDialect) (op : SelOp)
    (ls : List SecretLevel) : opAccepts (jasminSelLeak M) (.inr op) ls = true := rfl

/-! ## 5. Programs of `jasminSel` -/

/-- The denotation of a program of `jasminSel`. -/
abbrev jasminSelDenP (fuel : Nat) {Γ : Ctxt jasminSel} {ts : List jasminSel.Ty}
    (p : NFProg jasminSel Γ ts) (V : Valuation Γ) : Option (Valuation ts) :=
  p.denote fuel V

/-- The leakage run of a program of `jasminSel` over the model `M` of `jasminDialect`. -/
abbrev jasminSelLeakRun (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminSel}
    {ts : List jasminSel.Ty} (p : NFProg jasminSel Γ ts) (V : Valuation Γ) :
    Option (Valuation ts × List CTLeak) :=
  NFProg.leakRun (jasminSelLeak M) fuel p V

/-- **The level checker on `jasminSel`.** A program the checker `levelCheck'` accepts at
    `jasminSelLeak M` for the entry labels `L` is constant time for `L` relative to the runs
    that succeed. -/
theorem jasminSel_nfCTRel_of_levelCheck' (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminSel} {ts : List jasminSel.Ty} (p : NFProg jasminSel Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' (jasminSelLeak M) p L).isSome) :
    NFCTRel (jasminSelLeak M) L fuel p :=
  NFProg.nfCTRel_of_levelCheck' (jasminSelLeak M) fuel p L h

/-! ## 6. The two expressions -/

section Exprs

variable {Γ : Ctxt jasminSel}

/-- The unsigned minimum of `a` and `b`. -/
def uminE (w : Nat) (a b : Var Γ (JasminTy.reg w)) : Expr jasminSel Γ (JasminTy.reg w) :=
  ⟨.inr (.umin w), rfl, .cons a (.cons b .nil)⟩

/-- The half-width product of `a` and `b`. -/
def muluE (w : Nat) (a b : Var Γ (JasminTy.reg w)) : Expr jasminSel Γ (JasminTy.reg w) :=
  ⟨.inr (.mulu w), rfl, .cons a (.cons b .nil)⟩

/-- The value of `uminE`. -/
@[simp] theorem uminE_denote (w : Nat) (a b : Var Γ (JasminTy.reg w)) (V : Valuation Γ) :
    (uminE w a b).denote V = umin (a.lookup V) (b.lookup V) := by
  unfold Expr.denote; rfl

/-- The value of `muluE`. -/
@[simp] theorem muluE_denote (w : Nat) (a b : Var Γ (JasminTy.reg w)) (V : Valuation Γ) :
    (muluE w a b).denote V = halfProd (a.lookup V) (b.lookup V) := by
  unfold Expr.denote; rfl

/-- **The half-width product of operands below `2 ^ (w / 2)` is the product.** -/
theorem muluE_denote_of_lt (w : Nat) (a b : Var Γ (JasminTy.reg w)) (V : Valuation Γ)
    (ha : BitVec.toNat (w := w) (a.lookup V) < 2 ^ (w / 2))
    (hb : BitVec.toNat (w := w) (b.lookup V) < 2 ^ (w / 2)) :
    (muluE w a b).denote V
      = (show BitVec w from a.lookup V) * (show BitVec w from b.lookup V) :=
  (muluE_denote w a b V).trans (halfProd_eq_mul _ _ ha hb)

end Exprs

/-! ## 7. Programs of `jasminDialect` in `jasminSel` -/

/-- An expression of `jasminDialect` as an expression of `jasminSel`: the operation tagged
    `.inl`, the arguments unchanged. -/
def ofScalarExpr {Γ : List JasminTy} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Expr jasminSel Γ t where
  op := .inl e.op
  retTy_eq := e.retTy_eq
  args := castArgs e.args

/-- A scalar expression denotes in `jasminSel` what it denotes in `jasminDialect`. -/
theorem ofScalarExpr_denoteM {Γ : List JasminTy} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Valuation (d := jasminDialect) Γ) :
    @Expr.denoteM jasminSel Option _ _ jasminSelDenote Γ t (ofScalarExpr e) V
      = e.denoteM (M := Option) V := by
  obtain ⟨op, rfl, args⟩ := e
  show some (DialectDenote.denote (d := jasminDialect) op
      (Expr.lookupArgs (d := jasminSel) (castArgs args) V)) = _
  rw [lookupArgs_castArgs args V]
  rfl

/-- A scalar expression emits in `jasminSel` the events it emits in `jasminDialect`. -/
theorem ofScalarExpr_ctLeak (M : LeakModel jasminDialect) {Γ : List JasminTy} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Valuation (d := jasminDialect) Γ) :
    Expr.ctLeak (jasminSelLeak M) (ofScalarExpr e) V = Expr.ctLeak M e V := by
  show opLeak (jasminSelLeak M) (.inl e.op)
      (Expr.lookupArgs (d := jasminSel) (castArgs e.args) V) = _
  rw [lookupArgs_castArgs e.args V, jasminSel_opLeak_inl]
  rfl

/-- A program of `jasminDialect` as a program of `jasminSel`: every let-bound operation
    tagged as a scalar operation, the regions kept. -/
def ofScalar {Γ : Ctxt jasminSel} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    NFProg jasminSel Γ ts :=
  relabel (O₁ := JasminOp) (O₂ := JasminOp ⊕ SelOp) (T := JasminTy) ofScalarExpr p

/-- **A scalar program denotes in `jasminSel` what it denotes in `jasminDialect`**, at
    every fuel and valuation. -/
theorem ofScalar_denote (fuel : Nat) {Γ : Ctxt jasminSel} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    jasminSelDenP fuel (ofScalar p) V = p.denote fuel V :=
  relabel_denote (O₁ := JasminOp) (O₂ := JasminOp ⊕ SelOp) (T := JasminTy) ofScalarExpr
    (DS := jasminSelDenote) (CS := instCallDenoteJasminSel) ofScalarExpr_denoteM
    (fun _ _ _ _ => rfl) fuel p V

/-- **A scalar program runs in `jasminSel` to the results and the events of its run in
    `jasminDialect`.** -/
theorem ofScalar_leakRun (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminSel}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    jasminSelLeakRun M fuel (ofScalar p) V = NFProg.leakRun M fuel p V := by
  rw [← NFProg.leakRunM_eq_leakRun M fuel p V]
  exact (NFProg.leakRunM_eq_leakRun (jasminSelLeak M) fuel (ofScalar p) V).symm.trans
    (relabel_leakRunM (O₁ := JasminOp) (O₂ := JasminOp ⊕ SelOp) (T := JasminTy) ofScalarExpr
      M (jasminSelLeak M) (DS := jasminSelDenote) ofScalarExpr_denoteM (ofScalarExpr_ctLeak M)
      fuel p V)

/-- **The level checker returns on a scalar program in `jasminSel` what it returns in
    `jasminDialect`.** -/
theorem ofScalar_levelCheck' (M : LeakModel jasminDialect) {Γ : Ctxt jasminSel}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (L : Labels Γ) :
    NFProg.levelCheck' (jasminSelLeak M) (ofScalar p) L = NFProg.levelCheck' M p L :=
  relabel_levelCheck' (O₁ := JasminOp) (O₂ := JasminOp ⊕ SelOp) (T := JasminTy) ofScalarExpr
    M (jasminSelLeak M) (fun _ _ => rfl) (fun e L => argLvls_cast L e.args) p L

/-- A scalar program the level checker accepts in `jasminDialect` is constant time in
    `jasminSel` relative to its runs. -/
theorem ofScalar_nfCTRel (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminSel}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' M p L).isSome) :
    NFCTRel (jasminSelLeak M) L fuel (ofScalar p) :=
  jasminSel_nfCTRel_of_levelCheck' M fuel _ L ((ofScalar_levelCheck' M p L).symm ▸ h)

/-! ## 8. The lane-wise operation set -/

/-- The lane-wise unsigned minimum and half-width multiply on tiles. -/
inductive SelTileOp where
  /-- The unsigned minimum in each of the `n` lanes of `w` bits. -/
  | tileMinu (n w : Nat)
  /-- The half-width product in each of the `n` lanes of `w` bits. -/
  | tileMulu (n w : Nat)
  deriving DecidableEq

/-- The data effect of `tileMinu`: the unsigned minimum in each lane. -/
def tileMinuApply {n w : Nat} (a b : Fin n → BitVec w) : Fin n → BitVec w :=
  fun i => umin (a i) (b i)

/-- The data effect of `tileMulu`: the half-width product in each lane. -/
def tileMuluApply {n w : Nat} (a b : Fin n → BitVec w) : Fin n → BitVec w :=
  fun i => halfProd (a i) (b i)

section Tile

variable (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]

/-- The dialect of the lane-wise operation set over the type alphabet of `scalarTile d`. -/
abbrev selTile : Dialect.{0, 0} where
  Op := SelTileOp
  Ty := d.Ty ⊕ TileTy

/-- The signature of the lane-wise operations: two tiles to a tile of the same shape. -/
instance instDialectSignatureSelTile : DialectSignature (selTile d) where
  sig
    | .tileMinu n w => [.inr (.tile n w), .inr (.tile n w)]
    | .tileMulu n w => [.inr (.tile n w), .inr (.tile n w)]
  ret
    | .tileMinu n w => .inr (.tile n w)
    | .tileMulu n w => .inr (.tile n w)

/-- The value of the lane-wise operations: `tileMinuApply` and `tileMuluApply`. -/
instance instDialectDenoteSelTile : DialectDenote (selTile d) where
  denote
    | .tileMinu n w => fun args =>
        let a : Fin n → BitVec w := args.head
        let b : Fin n → BitVec w := args.tail.head
        (tileMinuApply a b : Fin n → BitVec w)
    | .tileMulu n w => fun args =>
        let a : Fin n → BitVec w := args.head
        let b : Fin n → BitVec w := args.tail.head
        (tileMuluApply a b : Fin n → BitVec w)

omit [DialectSignature d] in
/-- **Lane `j` of `tileMinu` is `umin` on lane `j` of the operands.** -/
theorem tileMinu_lane (n w : Nat) (a b : Fin n → BitVec w) (j : Fin n) :
    (DialectDenote.denote (d := selTile d) (.tileMinu n w) (.cons a (.cons b .nil)) :
        Fin n → BitVec w) j
      = DialectDenote.denote (d := selOps) (.umin w) (.cons (a j) (.cons (b j) .nil)) := rfl

omit [DialectSignature d] in
/-- **Lane `j` of `tileMulu` is `mulu` on lane `j` of the operands.** -/
theorem tileMulu_lane (n w : Nat) (a b : Fin n → BitVec w) (j : Fin n) :
    (DialectDenote.denote (d := selTile d) (.tileMulu n w) (.cons a (.cons b .nil)) :
        Fin n → BitVec w) j
      = DialectDenote.denote (d := selOps) (.mulu w) (.cons (a j) (.cons (b j) .nil)) := rfl

/-! ## 9. The operation sum with `scalarTile d` -/

/-- The operation sum of `scalarTile d` and the lane-wise operation set. -/
abbrev tileSel : Dialect.{0, 0} := Dialect.opSum (scalarTile d) (selTile d)

/-- The signature of `tileSel d`: the signature of the summand. -/
instance instDialectSignatureTileSel : DialectSignature (tileSel d) where
  sig
    | .inl o => DialectSignature.sig (d := scalarTile d) o
    | .inr o => DialectSignature.sig (d := selTile d) o
  ret
    | .inl o => DialectSignature.ret (d := scalarTile d) o
    | .inr o => DialectSignature.ret (d := selTile d) o

/-- The trip counter of `tileSel d` is the counter of `d`. -/
instance instHasWord64TileSel [HasWord64 d] : HasWord64 (tileSel d) where
  word := .inl (HasWord64.word (d := d))
  toNat := HasWord64.toNat (d := d)
  ofNat := HasWord64.ofNat (d := d)

/-- The bit of `tileSel d` is the bit of `d`. -/
instance instHasBoolBitTileSel [HasBoolBit d] : HasBoolBit (tileSel d) where
  bit := .inl (HasBitType.bit (d := d))
  toBool := HasBoolBit.toBool (d := d)

/-- `tileSel d` denotes calls in the empty environment. -/
instance instCallDenoteTileSel : CallDenote (tileSel d) := ⟨.empty⟩

/-- The denotation of `tileSel d` over the denotation `D` of `d`: an operation of
    `scalarTile d` by `scalarTileDenote d D`, a lane-wise operation by its total
    denotation. -/
@[instance_reducible] def tileSelDenote (D : DialectDenoteM d Option) :
    DialectDenoteM (tileSel d) Option where
  denoteM
    | .inl o, args => (scalarTileDenote d D).denoteM o args
    | .inr o, args => some (DialectDenote.denote (d := selTile d) o args)

/-- An operation of `scalarTile d` denotes in `tileSel d` as in `scalarTile d`. -/
@[simp] theorem tileSelDenote_inl (D : DialectDenoteM d Option) (o : (scalarTile d).Op)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := scalarTile d) o)) :
    (tileSelDenote d D).denoteM (.inl o) args = (scalarTileDenote d D).denoteM o args := rfl

/-- `tileMinu` returns the tile of the lane-wise unsigned minimum. -/
@[simp] theorem tileSelDenote_tileMinu (D : DialectDenoteM d Option) (n w : Nat)
    (a b : Fin n → BitVec w) :
    (tileSelDenote d D).denoteM (.inr (.tileMinu n w)) (.cons a (.cons b .nil))
      = some (tileMinuApply a b) := rfl

/-- `tileMulu` returns the tile of the lane-wise half-width product. -/
@[simp] theorem tileSelDenote_tileMulu (D : DialectDenoteM d Option) (n w : Nat)
    (a b : Fin n → BitVec w) :
    (tileSelDenote d D).denoteM (.inr (.tileMulu n w)) (.cons a (.cons b .nil))
      = some (tileMuluApply a b) := rfl

/-- The leakage model of `tileSel d` over a model `M` of `d`: an operation of
    `scalarTile d` has its class in `scalarTileLeak d M`, a lane-wise operation is quiet,
    and a value has the reading of `scalarTileLeak d M`. -/
def tileSelLeak (M : LeakModel d) : LeakModel (tileSel d) where
  kind := Sum.elim (scalarTileLeak d M).kind (fun _ => .quiet)
  valNat := (scalarTileLeak d M).valNat

/-- An operation of `scalarTile d` has the class `scalarTileLeak d M` gives it. -/
@[simp] theorem tileSelLeak_kind_inl (M : LeakModel d) (op : (scalarTile d).Op) :
    (tileSelLeak d M).kind (.inl op) = (scalarTileLeak d M).kind op := rfl

/-- A lane-wise operation is quiet. -/
@[simp] theorem tileSelLeak_kind_inr (M : LeakModel d) (op : SelTileOp) :
    (tileSelLeak d M).kind (.inr op) = .quiet := rfl

/-- The readings of a list of values are those of `scalarTileLeak d M`. -/
theorem tileSel_valsNat (M : LeakModel d) :
    ∀ {ts : List (d.Ty ⊕ TileTy)} (vals : HVector (fun t => ⟦t⟧) ts),
      valsNat (tileSelLeak d M) vals = valsNat (scalarTileLeak d M) vals
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show (scalarTileLeak d M).valNat _ x :: valsNat (tileSelLeak d M) xs
        = (scalarTileLeak d M).valNat _ x :: valsNat (scalarTileLeak d M) xs
      rw [tileSel_valsNat M xs]

/-- **The events of an operation of `scalarTile d`** in `tileSel d` are its events in
    `scalarTile d`. -/
theorem tileSel_opLeak_inl (M : LeakModel d) (op : (scalarTile d).Op)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := scalarTile d) op)) :
    opLeak (tileSelLeak d M) (.inl op) vals = opLeak (scalarTileLeak d M) op vals := by
  unfold opLeak
  rw [tileSelLeak_kind_inl, tileSel_valsNat d M vals]

/-- **A lane-wise operation emits no event.** -/
theorem tileSel_opLeak_inr (M : LeakModel d) (op : SelTileOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := selTile d) op)) :
    opLeak (tileSelLeak d M) (.inr op) vals = [] := rfl

/-- The constraint of an operation of `scalarTile d` is its constraint in `scalarTile d`. -/
@[simp] theorem tileSel_opAccepts_inl (M : LeakModel d) (op : (scalarTile d).Op)
    (ls : List SecretLevel) :
    opAccepts (tileSelLeak d M) (.inl op) ls = opAccepts (scalarTileLeak d M) op ls := rfl

/-- The level checker places no constraint on a lane-wise operation. -/
@[simp] theorem tileSel_opAccepts_inr (M : LeakModel d) (op : SelTileOp)
    (ls : List SecretLevel) : opAccepts (tileSelLeak d M) (.inr op) ls = true := rfl

variable [HasWord64 d] [HasBoolBit d]

/-- The denotation of a program of `tileSel d` over the denotation `D` of `d`. -/
abbrev tileSelDenP (D : DialectDenoteM d Option) (fuel : Nat) {Γ : Ctxt (tileSel d)}
    {ts : List (tileSel d).Ty} (p : NFProg (tileSel d) Γ ts) (V : Valuation Γ) :
    Option (Valuation ts) :=
  @NFProg.denote (tileSel d) _ _ _ _ (tileSelDenote d D) _ fuel Γ ts p V

/-- The leakage run of a program of `tileSel d` over the denotation `D` and the leakage
    model `M` of `d`. -/
abbrev tileSelLeakRun (D : DialectDenoteM d Option) (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt (tileSel d)} {ts : List (tileSel d).Ty} (p : NFProg (tileSel d) Γ ts)
    (V : Valuation Γ) : Option (Valuation ts × List CTLeak) :=
  @NFProg.leakRunM (tileSel d) _ _ _ _ (tileSelDenote d D) (tileSelLeak d M) fuel _ _ p V

/-- **The level checker on `tileSel d`.** A program the checker `levelCheck'` accepts at
    `tileSelLeak d M` for the entry labels `L` is constant time for `L` relative to the runs
    that succeed, over every denotation of `d`. -/
theorem tileSel_nfCTRel_of_levelCheck' (D : DialectDenoteM d Option) (M : LeakModel d)
    (fuel : Nat) {Γ : Ctxt (tileSel d)} {ts : List (tileSel d).Ty}
    (p : NFProg (tileSel d) Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' (tileSelLeak d M) p L).isSome) :
    @NFCTRel (tileSel d) _ _ _ _ (tileSelDenote d D) (tileSelLeak d M) Γ ts L fuel p :=
  @NFProg.nfCTRel_of_levelCheck' (tileSel d) _ _ _ _ (tileSelDenote d D)
    (tileSelLeak d M) fuel Γ ts p L h

/-! ## 10. Programs of `scalarTile d` in `tileSel d` -/

/-- An expression of `scalarTile d` as an expression of `tileSel d`: the operation tagged
    `.inl`, the arguments unchanged. -/
def ofScalarTileExpr {Γ : List (d.Ty ⊕ TileTy)} {t : d.Ty ⊕ TileTy}
    (e : Expr (scalarTile d) Γ t) : Expr (tileSel d) Γ t where
  op := .inl e.op
  retTy_eq := e.retTy_eq
  args := castArgs e.args

omit [HasWord64 d] [HasBoolBit d] in
/-- An included expression denotes as the expression. -/
theorem ofScalarTileExpr_denoteM (D : DialectDenoteM d Option) {Γ : List (d.Ty ⊕ TileTy)}
    {t : d.Ty ⊕ TileTy} (e : Expr (scalarTile d) Γ t)
    (V : Valuation (d := scalarTile d) Γ) :
    @Expr.denoteM (tileSel d) Option _ _ (tileSelDenote d D) Γ t (ofScalarTileExpr d e) V
      = @Expr.denoteM (scalarTile d) Option _ _ (scalarTileDenote d D) Γ t e V := by
  obtain ⟨op, rfl, args⟩ := e
  show (scalarTileDenote d D).denoteM op
      (Expr.lookupArgs (d := tileSel d) (castArgs args) V) = _
  rw [lookupArgs_castArgs args V]
  rfl

omit [HasWord64 d] [HasBoolBit d] in
/-- An included expression emits the events of the expression. -/
theorem ofScalarTileExpr_ctLeak (M : LeakModel d) {Γ : List (d.Ty ⊕ TileTy)}
    {t : d.Ty ⊕ TileTy} (e : Expr (scalarTile d) Γ t)
    (V : Valuation (d := scalarTile d) Γ) :
    Expr.ctLeak (tileSelLeak d M) (ofScalarTileExpr d e) V
      = Expr.ctLeak (scalarTileLeak d M) e V := by
  show opLeak (tileSelLeak d M) (.inl e.op)
      (Expr.lookupArgs (d := tileSel d) (castArgs e.args) V) = _
  rw [lookupArgs_castArgs e.args V, tileSel_opLeak_inl]
  rfl

/-- A program of `scalarTile d` as a program of `tileSel d`: every let-bound operation
    tagged `.inl`, the regions kept. -/
def ofScalarTile {Γ : Ctxt (scalarTile d)} {ts : List (d.Ty ⊕ TileTy)}
    (p : NFProg (scalarTile d) Γ ts) : NFProg (tileSel d) Γ ts :=
  relabel (O₁ := (scalarTile d).Op) (O₂ := (tileSel d).Op) (T := d.Ty ⊕ TileTy)
    (ofScalarTileExpr d) p

/-- **An included program denotes in `tileSel d` what it denotes in `scalarTile d`**, at
    every fuel and valuation. -/
theorem ofScalarTile_denote (D : DialectDenoteM d Option) (fuel : Nat)
    {Γ : Ctxt (scalarTile d)} {ts : List (d.Ty ⊕ TileTy)} (p : NFProg (scalarTile d) Γ ts)
    (V : Valuation Γ) :
    tileSelDenP d D fuel (ofScalarTile d p) V = scalarTileDenP d D fuel p V :=
  relabel_denote (O₁ := (scalarTile d).Op) (O₂ := (tileSel d).Op) (T := d.Ty ⊕ TileTy)
    (ofScalarTileExpr d) (DL := scalarTileDenote d D) (DS := tileSelDenote d D)
    (CL := instCallDenoteScalarTile d) (CS := instCallDenoteTileSel d)
    (ofScalarTileExpr_denoteM d D) (fun _ _ _ _ => rfl) fuel p V

/-- **An included program runs in `tileSel d` to the results and the events of its run in
    `scalarTile d`.** -/
theorem ofScalarTile_leakRunM (D : DialectDenoteM d Option) (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt (scalarTile d)} {ts : List (d.Ty ⊕ TileTy)} (p : NFProg (scalarTile d) Γ ts)
    (V : Valuation Γ) :
    tileSelLeakRun d D M fuel (ofScalarTile d p) V = scalarTileLeakRun d D M fuel p V :=
  relabel_leakRunM (O₁ := (scalarTile d).Op) (O₂ := (tileSel d).Op) (T := d.Ty ⊕ TileTy)
    (ofScalarTileExpr d) (scalarTileLeak d M) (tileSelLeak d M) (DL := scalarTileDenote d D)
    (DS := tileSelDenote d D) (ofScalarTileExpr_denoteM d D) (ofScalarTileExpr_ctLeak d M)
    fuel p V

/-- **The level checker returns on an included program what it returns in
    `scalarTile d`.** -/
theorem ofScalarTile_levelCheck' (M : LeakModel d) {Γ : Ctxt (scalarTile d)}
    {ts : List (d.Ty ⊕ TileTy)} (p : NFProg (scalarTile d) Γ ts) (L : Labels Γ) :
    NFProg.levelCheck' (tileSelLeak d M) (ofScalarTile d p) L
      = NFProg.levelCheck' (scalarTileLeak d M) p L :=
  relabel_levelCheck' (O₁ := (scalarTile d).Op) (O₂ := (tileSel d).Op) (T := d.Ty ⊕ TileTy)
    (ofScalarTileExpr d) (scalarTileLeak d M) (tileSelLeak d M) (fun _ _ => rfl)
    (fun e L => argLvls_cast L e.args) p L

end Tile

/-! ## 11. The instance at `jasminDialect` -/

/-- The operation sum of `scalarTile jasminDialect` and the lane-wise operation set. -/
abbrev jasminTileSel : Dialect := tileSel jasminDialect

instance : DialectSignature jasminTileSel := instDialectSignatureTileSel jasminDialect
instance : HasWord64 jasminTileSel := instHasWord64TileSel jasminDialect
instance : HasBoolBit jasminTileSel := instHasBoolBitTileSel jasminDialect
instance : CallDenote jasminTileSel := instCallDenoteTileSel jasminDialect

/-- The denotation of `jasminTileSel`: every summand is total. -/
@[instance_reducible] def jasminTileSelDenote : DialectDenoteM jasminTileSel Option :=
  tileSelDenote jasminDialect (instDialectDenoteMOptionOfPure jasminDialect)

end CatCrypt.Crypto.SecureCompilation.VIR.SelDialect
