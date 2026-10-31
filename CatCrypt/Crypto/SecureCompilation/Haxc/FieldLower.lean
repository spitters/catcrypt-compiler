/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
public import CatCrypt.Crypto.Hax.NFFieldSum
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
public import CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs

/-!
# Field operations lowered to limb blocks inside `NFProg`

`lowerF P` translates a program of `NFProg nfFieldDialect`, where
`nfFieldDialect = Dialect.sum nfDialect fieldDialect`, to a program of `NFProg jasminDialect`
for a field template `P` (`FieldLowerTemplate`). A field element is carried by a word array
of `n` limbs holding its encoding `FieldLowerTemplate.enc P`; a word, an unsigned integer
and an integer are carried by a 64-bit register (`jTy`, `JRel`). The templates are a
Montgomery record `P : LimbParams n` (`montTemplate`: the Montgomery form `encL P` and the
block `fieldCom P`) and a block-level template `T : LimbBlockTemplate n` (`limbTemplate`:
the encoding `T.enc` and the block `fieldComOf T.blocks`), which covers `solinasBlocks` with
canonical representatives and `montBlocks`.

Each variable of the source has a reading `Rd`: a carrier variable, an integer literal, or
nothing. A binding of an operation of `fieldDialect` that the template accepts becomes the
straight block `FieldLowerTemplate.block P op` on the arrays of its arguments: the loads of
the limbs, the block of the operation, and the stores of the result into the array of the
first argument. A binding of
an operation of `nfDialect` is one of the loop operations of the front `impToNF`: an integer
literal (no target binding), the unit value, and, with a lower bound read as the literal
`0`, the counter `ctr` (the trip index) and the trip count `trip` (the reading of its upper
bound). A counted loop is kept as a counted loop of `NFProg jasminDialect`, so that the
export of `NFProg jasminDialect` handles it; branches, exit-flag loops and call nodes are
refused.

## Main definitions

* `FieldLowerTemplate`, `montTemplate`, `limbTemplate` — the field templates of `lowerF`.
* `jTy`, `JRel`, `JRelV` — the carrier types and the relation of values and carriers.
* `Rd`, `JRen`, `JAgree` — readings, renamings to readings and their agreement.
* `leftArm`, `fieldArm`, `bindF` — the translation of a binding; `rightArm` is `fieldArm`
  at a Montgomery record, unfolded (`fieldArm_mont`).
* `lowerF` — the translation.
* `sumStep`, `fieldLowerStep` — `nfToSum` and `lowerF` as chain steps (`PassChain.Step`);
  `sumCert`, `fieldLowerCert` their certificates.
* `kindRen`, `idRen` — the entry renamings of a context carried at given kinds.

## Main results

* `fieldArm_sound` — the array of the block of a field operation holds the encoding of its
  value; `rightArm_sound` its Montgomery instance.
* `lowerF_sound` — the lowered program computes carriers related to the values of the
  source, at every leaf table and every fuel.
* `kindRen_agree`, `idRen_agree` — the entry renamings agree with related valuations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend hvToHom pullV_hvToHom
  flatVal ctxFlat)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (eConst)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs (LimbBlockTemplate ArithAt)
open CatCrypt.Crypto.Hax.NFFieldSum (nfFieldDialect nfFieldDenote)
open Ctxt (Var Valuation)

/-! ## 1. Carrier types, relations and readings -/

/-- The jasmin type that carries a type of `nfFieldDialect` over `n` limbs: a 64-bit register
    for a type of `nfDialect`, a word array of `n` limbs for a field type. -/
@[reducible] def jTy (n : Nat) : nfFieldDialect.Ty → jasminDialect.Ty
  | .inl _ => .reg 64
  | .inr _ => arrTy n

/-- The variables of a context, in order. -/
def allVars {d : Dialect} [DialectSignature d] :
    (Γ : Ctxt d) → HVector (fun t => Var Γ t) Γ
  | [] => .nil
  | _ :: Γ => .cons .here (shiftVars (allVars Γ))
where
  /-- A vector of variables under one more binding. -/
  shiftVars {Γ : Ctxt d} {s : d.Ty} :
      {ts : List d.Ty} → HVector (fun t => Var Γ t) ts → HVector (fun t => Var (s :: Γ) t) ts
    | [], .nil => .nil
    | _ :: _, .cons v vs => .cons (.there v) (shiftVars vs)

/-- The field program of one operation on its arguments. -/
def opCom (op : fieldDialect.Op) :
    Com fieldDialect (DialectSignature.sig op) (DialectSignature.ret op) :=
  .var ⟨op, rfl, allVars _⟩ (.ret .here)

theorem lookupArgs_allVars {d : Dialect} [DialectSignature d] [TyDenote d.Ty] :
    ∀ (Γ : Ctxt d) (V : Valuation Γ), Expr.lookupArgs (allVars Γ) V = V
  | [], .nil => rfl
  | _ :: Γ, .cons x V => by
      have hs : ∀ {ts : List d.Ty} (vs : HVector (fun t => Var Γ t) ts),
          Expr.lookupArgs (allVars.shiftVars (s := _) vs) (HVector.cons x V) =
            Expr.lookupArgs vs V := by
        intro ts vs
        induction vs with
        | nil => rfl
        | cons v vs ih =>
            show HVector.cons _ _ = HVector.cons _ _
            rw [ih]
            rfl
      show HVector.cons x _ = HVector.cons x V
      rw [hs, lookupArgs_allVars Γ V]

theorem opCom_denote (op : fieldDialect.Op) (V : Valuation (DialectSignature.sig op)) :
    (opCom op).denote V = DialectDenote.denote op V := by
  show DialectDenote.denote op (Expr.lookupArgs (allVars _) V) = _
  rw [lookupArgs_allVars]

/-! ## 1a. The field template -/

/-- **A field template of `lowerF` over `n` limbs**, carried by the values of `α`: the
    modulus `p`; the element encoding `enc`, the limbs of the word array that carries a field
    element (its Montgomery form for a Montgomery record, its canonical representative for a
    Solinas template); the acceptance `accepts` of an operation of `fieldDialect`; the block
    `block P op` of an operation over the arrays of its arguments and an output array; and
    the denotation of an accepted block: on input arrays holding the encodings of the
    arguments, its output array holds the encoding of the value of the operation. -/
class FieldLowerTemplate (α : Type) (n : outParam Nat) where
  /-- The modulus. -/
  p : α → Nat
  /-- The element encoding: the limbs carrying a field element. -/
  enc : α → ∀ {t : FieldTy}, ⟦t⟧ → Valuation (mapTysL n t)
  /-- The operations of `fieldDialect` the template lowers. -/
  accepts : α → fieldDialect.Op → Bool
  /-- The block of an operation over the arrays of its arguments and an output array. -/
  block : α → (op : fieldDialect.Op) →
    Com jasminDialect (arrCtx n (DialectSignature.sig op) ++ [arrTy n]) (arrTy n)
  /-- The output array of an accepted block holds the encoding of the value. -/
  block_denote : ∀ (P : α) (op : fieldDialect.Op), accepts P op = true → n < 2 ^ 64 →
    ∀ (V : Valuation (DialectSignature.sig op))
      (A : Valuation (arrCtx n (DialectSignature.sig op))) (o : Fin n → BitVec 64),
      arrFlat A = flatVal (fun {t} x => enc P (t := t) x) V →
      arrLimbs ((block P op).denote (hvAppend A (.cons o .nil))) n 0
        = enc P (DialectDenote.denote op V)

/-- **The Montgomery template** of a record `P`: the modulus `P.p`, the Montgomery limbs
    `encL P`, the operations `opGoodB P` accepts and the block `fieldCom P (opCom op)`. -/
instance montTemplate {n : Nat} : FieldLowerTemplate (LimbParams n) n where
  p P := P.p
  enc P := fun {t} x => encL P (t := t) x
  accepts P := opGoodB P
  block P op := fieldCom P (opCom op)
  block_denote P op hg hn V A o hA := by
    rw [fieldCom_denote P hn (opCom op)
      (GoodVB_sound P (opCom op) (by simp [GoodVB, opCom, hg])) V A o hA, opCom_denote]

/-- The operations of `ArithAt p`: `fAdd`, `fSub`, `fNeg`, `fMul` and `fConst` at `p`. -/
def arithOpB (p : Nat) : fieldDialect.Op → Bool
  | .fAdd q | .fSub q | .fNeg q | .fMul q => q == p
  | .fConst q _ => q == p
  | _ => false

/-- The program of an operation that `arithOpB p` accepts is covered by every predicate that
    holds on `ArithAt p`. -/
theorem coveredCom_opCom {p : Nat}
    {Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop}
    (h : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} {e : Expr fieldDialect Γ t},
      ArithAt p e → Good e)
    (op : fieldDialect.Op) (hg : arithOpB p op = true) : CoveredCom Good (opCom op) := by
  refine ⟨h ?_, trivial⟩
  cases op <;> simp only [arithOpB, beq_iff_eq, Bool.false_eq_true] at hg <;> subst hg <;>
    simp [ArithAt]

/-- **The template of a block-level template** `T` (`montBlocks`, `solinasBlocks`, ...):
    the modulus `T.p`, the encoding `T.enc`, the operations of `ArithAt T.p`, and the block
    `fieldComOf T.blocks (opCom op)`. -/
instance limbTemplate {n : Nat} : FieldLowerTemplate (LimbBlockTemplate n) n where
  p T := T.p
  enc T := fun {t} x => T.enc (t := t) x
  accepts T := arithOpB T.p
  block T op := fieldComOf T.blocks (opCom op)
  block_denote T op hg hn V A o hA := by
    rw [fieldComOf_denote T.blocks T.enc T.Good T.square hn (opCom op)
      (coveredCom_opCom T.arith op hg) V A o hA, opCom_denote]

variable {n : Nat} {α : Type} (P : α) [FieldLowerTemplate α n]

/-- The relation of a value of `nfFieldDialect` and its carrier: a word, an unsigned integer
    and an integer by the natural number of the register, a field element by the limbs
    `FieldLowerTemplate.enc P` of the array; every other type of `nfDialect` by the true
    relation. -/
def JRel : (t : nfFieldDialect.Ty) → ⟦t⟧ → ⟦jTy n t⟧ → Prop
  | .inl (.word _), x, y => BitVec.toNat (w := 64) y = BitVec.toNat x
  | .inl .int, x, y => (BitVec.toNat (w := 64) y : Int) = x
  | .inl (.uint _), x, y => BitVec.toNat (w := 64) y = BitVec.toNat x
  | .inl _, _, _ => True
  | .inr t, x, y => arrLimbs y n 0 = FieldLowerTemplate.enc P (t := t) x

/-- The relations of a tuple of values and a tuple of carriers. -/
def JRelV : {ts : List nfFieldDialect.Ty} → Valuation ts → Valuation (ts.map (jTy n)) → Prop
  | [], _, _ => True
  | t :: _, .cons x xs, .cons y ys => JRel P t x y ∧ JRelV xs ys

variable (n) in
/-- **A reading** of a variable of type `t`: a carrier variable, an integer literal (bound
    by no target binding), or nothing (for a value no operation reads). -/
inductive Rd (Θ : Ctxt jasminDialect) (t : nfFieldDialect.Ty) : Type where
  | var (v : Var Θ (jTy n t))
  | lit (z : Int)
  | none

/-- The relation of a literal reading: the integer itself at the integer type, and the
    natural number of the word at a word type. -/
def litRel : (t : nfFieldDialect.Ty) → Int → ⟦t⟧ → Prop
  | .inl .int, z, x => x = z
  | .inl (.word _), z, x => (BitVec.toNat x : Int) = z
  | _, _, _ => False

/-- The relation of a reading at a valuation of the carriers and a source value. -/
def Rd.rel {Θ : Ctxt jasminDialect} (W : Valuation Θ) {t : nfFieldDialect.Ty} :
    Rd n Θ t → ⟦t⟧ → Prop
  | .var v, x => JRel P t x (v.lookup W)
  | .lit z, x => litRel t z x
  | .none, _ => True

/-- A reading renamed along a renaming of the carrier context. -/
def Rd.rename {Θ Θ' : Ctxt jasminDialect} (h : Ctxt.Hom Θ Θ') {t : nfFieldDialect.Ty} :
    Rd n Θ t → Rd n Θ' t
  | .var v => .var (h v)
  | .lit z => .lit z
  | .none => .none

/-- A renaming `h` from `W` to `W'` keeps every lookup. -/
def Pres {Θ Θ' : Ctxt jasminDialect} (h : Ctxt.Hom Θ Θ') (W : Valuation Θ)
    (W' : Valuation Θ') : Prop :=
  ∀ {s : JasminTy} (v : Var Θ s), (h v).lookup W' = v.lookup W

theorem Rd.rel_rename {Θ Θ' : Ctxt jasminDialect} {h : Ctxt.Hom Θ Θ'} {W : Valuation Θ}
    {W' : Valuation Θ'} (hp : Pres h W W') {t : nfFieldDialect.Ty} (r : Rd n Θ t)
    (x : ⟦t⟧) (hr : r.rel P W x) : (r.rename h).rel P W' x := by
  cases r with
  | var v => exact (show JRel P t x ((h v).lookup W') by rw [hp v]; exact hr)
  | lit z => exact hr
  | none => trivial

variable (n) in
/-- A renaming of the variables of `nfFieldDialect` to readings. -/
abbrev JRen (Δ : Ctxt nfFieldDialect) (Θ : Ctxt jasminDialect) : Type :=
  ∀ {t : nfFieldDialect.Ty}, Var Δ t → Rd n Θ t

/-- Every variable is related to its reading. -/
def JAgree {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    (X : Valuation Δ) (W : Valuation Θ) : Prop :=
  ∀ (t : nfFieldDialect.Ty) (v : Var Δ t), (ρ v).rel P W (v.lookup X)

/-- A renaming under one more binding read by `r`, the others renamed along `h`. -/
def JRen.lift {Δ : Ctxt nfFieldDialect} {Θ Θ' : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    (h : Ctxt.Hom Θ Θ') {s : nfFieldDialect.Ty} (r : Rd n Θ' s) : JRen n (s :: Δ) Θ'
  | _, .here => r
  | _, .there v => (ρ v).rename h

theorem JAgree.lift {Δ : Ctxt nfFieldDialect} {Θ Θ' : Ctxt jasminDialect} {ρ : JRen n Δ Θ}
    {X : Valuation Δ} {W : Valuation Θ} (hA : JAgree P ρ X W) {h : Ctxt.Hom Θ Θ'}
    {W' : Valuation Θ'} (hp : Pres h W W') {s : nfFieldDialect.Ty} (r : Rd n Θ' s)
    (x : ⟦s⟧) (hr : r.rel P W' x) : JAgree P (ρ.lift h r) (X.extend x) W' := by
  intro t v
  cases v with
  | here => exact hr
  | there v => exact Rd.rel_rename P hp (ρ v) _ (hA t v)

/-- A renaming under a carried tuple `cs`, read by the first carrier variables. -/
def JRen.app {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) :
    (cs : List nfFieldDialect.Ty) → JRen n (cs ++ Δ) (cs.map (jTy n) ++ Θ)
  | [] => ρ
  | _ :: cs => JRen.lift (JRen.app ρ cs) (fun v => .there v) (.var .here)

theorem JAgree.app {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ}
    {X : Valuation Δ} {W : Valuation Θ} (hA : JAgree P ρ X W) :
    ∀ (cs : List nfFieldDialect.Ty) (A : Valuation cs) (B : Valuation (cs.map (jTy n))),
      JRelV P A B → JAgree P (JRen.app ρ cs) (hvAppend A X) (hvAppend B W)
  | [], .nil, .nil, _ => hA
  | _ :: cs, .cons x A, .cons _ B, hAB =>
      (JAgree.app hA cs A B hAB.2).lift P (h := fun v => .there v) (fun _ => rfl) (.var .here)
        x hAB.1

/-- The carrier variable of a reading that is a variable. -/
def Rd.var? {Θ : Ctxt jasminDialect} {t : nfFieldDialect.Ty} : Rd n Θ t → Option (Var Θ (jTy n t))
  | .var v => some v
  | _ => Option.none

/-- The integer of a reading that is a literal. -/
def Rd.lit? {Θ : Ctxt jasminDialect} {t : nfFieldDialect.Ty} : Rd n Θ t → Option Int
  | .lit z => some z
  | _ => Option.none

theorem Rd.eq_of_var? {Θ : Ctxt jasminDialect} {t : nfFieldDialect.Ty} {r : Rd n Θ t}
    {w : Var Θ (jTy n t)} (h : r.var? = some w) : r = .var w := by
  cases r <;> simp_all [Rd.var?]

theorem Rd.eq_of_lit? {Θ : Ctxt jasminDialect} {t : nfFieldDialect.Ty} {r : Rd n Θ t} {z : Int}
    (h : r.lit? = some z) : r = .lit z := by
  cases r <;> simp_all [Rd.lit?]

/-- The carrier variables of a vector of variables, when every reading is a variable. -/
def retVars {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) :
    {ts : List nfFieldDialect.Ty} → HVector (fun t => Var Δ t) ts →
      Option (HVector (fun t => Var Θ t) (ts.map (jTy n)))
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (ρ v).var?.bind fun w => (retVars ρ vs).map (.cons w)

theorem retVars_rel {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ}
    {X : Valuation Δ} {W : Valuation Θ} (hA : JAgree P ρ X W) :
    ∀ {ts : List nfFieldDialect.Ty} (vs : HVector (fun t => Var Δ t) ts) ws,
      retVars ρ vs = some ws → JRelV P (Expr.lookupArgs vs X) (Expr.lookupArgs ws W)
  | [], .nil, _, _ => trivial
  | _ :: _, .cons v vs, ws, h => by
      obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ws', hws', rfl⟩ := Option.map_eq_some_iff.mp h
      have hv : (ρ v).rel P W (v.lookup X) := hA _ v
      have e : ρ v = .var w := Rd.eq_of_var? hw
      rw [e] at hv
      exact ⟨hv, retVars_rel hA vs ws' hws'⟩

/-! ## 2. The bindings -/

/-- The continuation of a binding of type `t`: a renaming of the carrier context and the
    reading of the bound value. -/
abbrev BindK (n : Nat) (Θ : Ctxt jasminDialect) (t : nfFieldDialect.Ty)
    (us : List JasminTy) : Type :=
  ∀ {Θ' : Ctxt jasminDialect}, Ctxt.Hom Θ Θ' → Rd n Θ' t → Option (NFProg jasminDialect Θ' us)

/-- The loop counter from the lower bound `lo` and the trip index `i`: with `lo` read as the
    literal `0`, the reading of `i`. -/
def ctrArm {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} (lo : Var Δ (.inl .int)) (i : Var Δ (.inl (.word 64)))
    (k : BindK n Θ (.inl (.word 64)) us) : Option (NFProg jasminDialect Θ us) :=
  if (ρ lo).lit? = some 0 then (ρ i).var?.bind fun w => k (fun v => v) (.var w) else none

/-- The trip count from the lower bound `lo` and the upper bound `hi`: with `lo` read as
    the literal `0`, the reading of `hi`, or a binding of the constant of a literal `hi`. -/
def tripArm {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} {t : NfTy} (lo : Var Δ (.inl .int)) (hi : Var Δ (.inl t))
    (k : BindK n Θ (.inl (.word 64)) us) : Option (NFProg jasminDialect Θ us) :=
  if (ρ lo).lit? = some 0 then
    match ρ hi with
    | .var w => k (fun v => v) (.var w)
    | .lit z => (k (fun v => .there v) (.var .here)).map (.var (eConst z.toNat))
    | .none => none
  else none

/-- **The left arm**: an operation of `nfDialect` on readings. An integer literal is read
    as a literal and the unit value as nothing, with no target binding; with the lower bound
    read as the literal `0`, the loop counter `ctr` is read as the trip index (`ctrArm`), and
    the trip count `trip` as its upper bound, or as a binding of the constant when the upper
    bound is a literal (`tripArm`). Every other operation is refused. -/
def leftArm {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} :
    (op : NfOp) → HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inl) →
      BindK n Θ (.inl (DialectSignature.ret op)) us → Option (NFProg jasminDialect Θ us)
  | .named _ op, args, k => leftArm ρ op args k
  | .ilit .int z, _, k => k (fun v => v) (.lit z)
  | .ilit (.word _) z, _, k => k (fun v => v) (.lit z)
  | .constUnit, _, k => k (fun v => v) .none
  | .ctr, args, k => ctrArm ρ args.head args.tail.head k
  | .trip _, args, k => tripArm ρ args.head args.tail.head k
  | _, _, _ => none

/-- The array variables carrying a vector of field variables, when every reading is a
    variable. -/
def fldArrs {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) :
    {ts : List FieldTy} → HVector (fun t => Var Δ t) (ts.map Sum.inr) →
      Option (HVector (fun t => Var Θ t) (arrCtx n ts))
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (ρ v).var?.bind fun w => (fldArrs ρ vs).map (.cons w)

/-- The first array of a vector of arrays. -/
def headArr {Θ : Ctxt jasminDialect} :
    {ts : List FieldTy} → HVector (fun t => Var Θ t) (arrCtx n ts) → Option (Var Θ (arrTy n))
  | [], _ => none
  | _ :: _, .cons a _ => some a

/-- **The right arm**: an operation of `fieldDialect` that the template accepts and that
    has an argument, on array readings, as the block `FieldLowerTemplate.block P op` over
    the arrays of its arguments, writing into the array of its first argument. -/
def fieldArm {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} (op : fieldDialect.Op)
    (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inr))
    (k : BindK n Θ (.inr (DialectSignature.ret op)) us) : Option (NFProg jasminDialect Θ us) :=
  if FieldLowerTemplate.accepts P op then
    (fldArrs ρ args).bind fun as =>
      (headArr as).bind fun o =>
        NFProg.spliceNF?
          (Com.rename (hvToHom (hvAppend as (.cons o .nil))) (FieldLowerTemplate.block P op))
          (fun {_} h res => k h (.var res))
  else none

/-- **The right arm at a Montgomery record**, `fieldArm` with the template unfolded: an
    operation at `P.p` that `opGoodB` accepts and that has an argument, as the block
    `fieldCom P (opCom op)` over the arrays of its arguments. -/
def rightArm {n : Nat} (P : LimbParams n) {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) {us : List JasminTy} (op : fieldDialect.Op)
    (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inr))
    (k : BindK n Θ (.inr (DialectSignature.ret op)) us) : Option (NFProg jasminDialect Θ us) :=
  if opGoodB P op then
    (fldArrs ρ args).bind fun as =>
      (headArr as).bind fun o =>
        NFProg.spliceNF?
          (Com.rename (hvToHom (hvAppend as (.cons o .nil))) (fieldCom P (opCom op)))
          (fun {_} h res => k h (.var res))
  else none

/-- The template right arm at a Montgomery record is `rightArm`. -/
theorem fieldArm_mont {n : Nat} (P : LimbParams n) {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) {us : List JasminTy} (op : fieldDialect.Op)
    (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inr))
    (k : BindK n Θ (.inr (DialectSignature.ret op)) us) :
    fieldArm P ρ op args k = rightArm P ρ op args k := rfl

/-- **The binding of an expression**: the left arm on an operation of `nfDialect`, the
    right arm on an operation of `fieldDialect`. -/
def bindF {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} : {t : nfFieldDialect.Ty} → Expr nfFieldDialect Δ t →
      BindK n Θ t us → Option (NFProg jasminDialect Θ us)
  | _, ⟨.inl op, rfl, args⟩, k => leftArm ρ op args k
  | _, ⟨.inr op, rfl, args⟩, k => fieldArm P ρ op args k

/-! ## 3. The translation -/

/-- **The lowering of field operations** from the renaming `ρ`: each binding by `bindF`, the
    result vector at the carrier variables of its readings, and a counted loop whose count
    and initial values are read by carrier variables, with the counter read by the target
    counter and the carried tuple by the target tuple. Branches, exit-flag loops and call
    nodes are refused. -/
def lowerF : {Δ : Ctxt nfFieldDialect} → {ts : List nfFieldDialect.Ty} →
    NFProg nfFieldDialect Δ ts → {Θ : Ctxt jasminDialect} → JRen n Δ Θ →
      Option (NFProg jasminDialect Θ (ts.map (jTy n)))
  | _, _, .ret vs, _, ρ => (retVars ρ vs).map .ret
  | _, _, .var e k, _, ρ => bindF P ρ e fun h r => lowerF k (ρ.lift h r)
  | _, _, .forLoop (cs := cs) count inits body k, _, ρ =>
      match ρ count with
      | .var c => (retVars ρ inits).bind fun ivs =>
          (lowerF body (JRen.app (ρ.lift (fun v => .there v) (.var .here)) cs)).bind
            fun body' => (lowerF k (JRen.app ρ cs)).map fun k' => .forLoop c ivs body' k'
      | _ => none
  | _, _, _, _, _ => none

/-! ## 4. Soundness -/

/-- The denotation of a program of `nfFieldDialect` at the leaf table `L`. -/
abbrev SDenL (L : NfLeafTable) (fuel : Nat) {Δ : Ctxt nfFieldDialect}
    {ts : List nfFieldDialect.Ty} (p : NFProg nfFieldDialect Δ ts) (X : Valuation Δ) :
    Option (Valuation ts) :=
  @NFProg.denote nfFieldDialect _ _ _ _ (nfFieldDenote L) _ fuel Δ ts p X

/-- **A block followed by a partial continuation, forward.** A program `spliceNF? blk k`
    returns denotes what the continuation's program denotes at an extension of the
    valuation that keeps every lookup and holds the value of the block at its result. -/
theorem spliceNF?_fwd (fuel : Nat) {us : List JasminTy} :
    ∀ {Θ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Θ a)
      (k : {Θ' : Ctxt jasminDialect} → Ctxt.Hom Θ Θ' → Var Θ' a →
        Option (NFProg jasminDialect Θ' us))
      (W : Valuation Θ) (q : NFProg jasminDialect Θ us), NFProg.spliceNF? blk k = some q →
      ∃ (Θ' : Ctxt jasminDialect) (h : Ctxt.Hom Θ Θ') (res : Var Θ' a) (W' : Valuation Θ')
        (q' : NFProg jasminDialect Θ' us), Pres h W W' ∧ res.lookup W' = blk.denote W ∧
          k h res = some q' ∧ q.denote fuel W = q'.denote fuel W'
  | _, _, .ret v, _, W, q, hq => ⟨_, fun x => x, v, W, q, fun _ => rfl, rfl, hq, rfl⟩
  | _, _, .var e blk, k, W, q, hq => by
      simp only [NFProg.spliceNF?] at hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨Θ', h, res, W', q'', hp, hres, hk, hden⟩ :=
        spliceNF?_fwd fuel blk _ (W.extend (e.denote W)) q' hq'
      refine ⟨Θ', fun x => h (.there x), res, W', q'', fun v => hp (.there v), hres, hk, ?_⟩
      rw [← hden]
      simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]

/-- The looked-up variables of an appended vector are the appended lookups. -/
theorem lookupVars_hvAppend {Θ : Ctxt jasminDialect} (W : Valuation Θ) :
    ∀ {xs ys : List JasminTy} (as : HVector (fun t => Var Θ t) xs)
      (bs : HVector (fun t => Var Θ t) ys),
      MultiReturnCom.lookupVars (hvAppend as bs) W =
        hvAppend (MultiReturnCom.lookupVars as W) (MultiReturnCom.lookupVars bs W)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons a as, bs => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupVars_hvAppend W as bs]

theorem fldArrs_rel {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ}
    {X : Valuation Δ} {W : Valuation Θ} (hA : JAgree P ρ X W) :
    ∀ {ts : List FieldTy} (vs : HVector (fun t => Var Δ t) (ts.map Sum.inr)) as,
      fldArrs ρ vs = some as →
        arrFlat (n := n) (MultiReturnCom.lookupVars as W) =
          flatVal (fun {t} x => FieldLowerTemplate.enc P (t := t) x)
            (unmapInr (Expr.lookupArgs vs X))
  | [], .nil, _, h => by
      cases h
      rfl
  | _ :: _, .cons v vs, as, h => by
      obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.mp h
      have hv : (ρ v).rel P W (v.lookup X) := hA _ v
      have e : ρ v = .var w := Rd.eq_of_var? hw
      rw [e] at hv
      show hvAppend (arrLimbs (w.lookup W) n 0) _
        = hvAppend (FieldLowerTemplate.enc P (v.lookup X)) _
      rw [show arrLimbs (w.lookup W) n 0 = FieldLowerTemplate.enc P (v.lookup X) from hv,
        fldArrs_rel hA vs as' has']

/-- The conclusion of the soundness of a binding: an extension of the carrier valuation
    that keeps every lookup, a reading of the bound value related to it, and a program of
    the continuation denoting what the translated program denotes. -/
def BindOk {Θ : Ctxt jasminDialect} {t : nfFieldDialect.Ty} {us : List JasminTy}
    (fuel : Nat) (W : Valuation Θ) (x : ⟦t⟧) (k : BindK n Θ t us)
    (q : NFProg jasminDialect Θ us) : Prop :=
  ∃ (Θ' : Ctxt jasminDialect) (h : Ctxt.Hom Θ Θ') (r : Rd n Θ' t) (W' : Valuation Θ')
    (q' : NFProg jasminDialect Θ' us), Pres h W W' ∧ r.rel P W' x ∧ k h r = some q' ∧
      q.denote fuel W = q'.denote fuel W'

theorem bindOk_id {Θ : Ctxt jasminDialect} {t : nfFieldDialect.Ty} {us : List JasminTy}
    (fuel : Nat) (W : Valuation Θ) (x : ⟦t⟧) (k : BindK n Θ t us)
    (q : NFProg jasminDialect Θ us) (r : Rd n Θ t) (hr : r.rel P W x)
    (hq : k (fun v => v) r = some q) : BindOk P fuel W x k q :=
  ⟨_, fun v => v, r, W, q, fun _ => rfl, hr, hq, rfl⟩

theorem lit_zero {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ}
    {X : Valuation Δ} {W : Valuation Θ} (hA : JAgree P ρ X W) (lo : Var Δ (.inl .int))
    (h : (ρ lo).lit? = some 0) : lo.lookup X = (0 : Int) := by
  have h1 : (ρ lo).rel P W (lo.lookup X) := hA _ lo
  rw [Rd.eq_of_lit? h] at h1
  exact h1

/-- The loop counter keeps the value. -/
theorem ctrArm_sound (fuel : Nat) {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    {ρ : JRen n Δ Θ} {X : Valuation Δ} {W : Valuation Θ} (hA : JAgree P ρ X W)
    {us : List JasminTy} (lo : Var Δ (.inl .int)) (i : Var Δ (.inl (.word 64)))
    (k : BindK n Θ (.inl (.word 64)) us) (q : NFProg jasminDialect Θ us)
    (hq : ctrArm ρ lo i k = some q) (x : BitVec 64)
    (hx : (fun (a : Int) (b : BitVec 64) =>
      if 0 ≤ a ∧ a + (b.toNat : Int) < 2 ^ 64 then
        some (BitVec.ofNat 64 (a + (b.toNat : Int)).toNat)
      else none) (lo.lookup X) (i.lookup X) = some x) :
    BindOk P fuel W (t := .inl (.word 64)) x k q := by
  unfold ctrArm at hq
  split at hq
  · rename_i hlo
    obtain ⟨w, hw, hq⟩ := Option.bind_eq_some_iff.mp hq
    refine bindOk_id P fuel W (t := .inl (.word 64)) x k q (.var w) ?_ hq
    have h2 : (ρ i).rel P W (i.lookup X) := hA _ i
    have e : ρ i = .var w := Rd.eq_of_var? hw
    rw [e] at h2
    change BitVec.toNat (w.lookup W) = BitVec.toNat (i.lookup X) at h2
    change BitVec.toNat (w.lookup W) = BitVec.toNat x
    rw [lit_zero P hA lo hlo] at hx
    beta_reduce at hx
    rw [zero_add] at hx
    split at hx
    · obtain rfl := Option.some.inj hx
      rw [h2, Int.toNat_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
    · cases hx
  · cases hq

/-- The trip count keeps the value. -/
theorem tripArm_sound (fuel : Nat) {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    {ρ : JRen n Δ Θ} {X : Valuation Δ} {W : Valuation Θ} (hA : JAgree P ρ X W)
    {us : List JasminTy} {t : NfTy} (lo : Var Δ (.inl .int)) (hi : Var Δ (.inl t))
    (k : BindK n Θ (.inl (.word 64)) us) (q : NFProg jasminDialect Θ us)
    (hq : tripArm ρ lo hi k = some q) (x : BitVec 64)
    (hx : (NfTy.toInt? t (hi.lookup X)).map
      (fun h => BitVec.ofNat 64 (h - (lo.lookup X : Int)).toNat) = some x) :
    BindOk P fuel W (t := .inl (.word 64)) x k q := by
  unfold tripArm at hq
  split at hq
  · rename_i hlo
    rw [lit_zero P hA lo hlo] at hx
    have h2 : (ρ hi).rel P W (hi.lookup X) := hA _ hi
    split at hq
    · rename_i w hhi
      refine bindOk_id P fuel W (t := .inl (.word 64)) x k q (.var w) ?_ hq
      have e : ρ hi = .var w := hhi
      rw [e] at h2
      change BitVec.toNat (w.lookup W) = BitVec.toNat x
      change JRel P (.inl t) (hi.lookup X) (w.lookup W) at h2
      have hw := (w.lookup W).isLt
      cases t <;> simp only [NfTy.toInt?, Option.map_none, Option.map_some,
        reduceCtorEq, Option.some.injEq] at hx <;> subst hx <;> simp only [JRel] at h2 <;>
        simp only [BitVec.toNat_ofNat] <;> omega
    · rename_i z hhi
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      refine ⟨_, fun v => .there v, .var .here, (W.extend (BitVec.ofNat 64 z.toNat)), q',
        fun _ => rfl, ?_, hq', ?_⟩
      · have e : ρ hi = .lit z := hhi
        rw [e] at h2
        change BitVec.toNat (BitVec.ofNat 64 z.toNat) = BitVec.toNat x
        cases t <;> (simp only [Rd.rel, litRel] at h2; try exact h2.elim) <;>
          (simp only [NfTy.toInt?, Option.map_some, Option.some.injEq] at hx
           subst hx
           rw [h2, Int.sub_zero])
      · simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
          Option.bind_some]
        rfl
    · cases hq
  · cases hq

/-- **The left arm keeps the value.** -/
theorem leftArm_sound (L : NfLeafTable) (fuel : Nat) {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ} {X : Valuation Δ} {W : Valuation Θ}
    (hA : JAgree P ρ X W) {us : List JasminTy} :
    ∀ (op : NfOp) (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inl))
      (k : BindK n Θ (.inl (DialectSignature.ret op)) us) (q : NFProg jasminDialect Θ us),
      leftArm ρ op args k = some q → ∀ x, nfDenoteOp L op (unmapInl (Expr.lookupArgs args X)) =
        some x → BindOk P fuel W (t := .inl (DialectSignature.ret op)) x k q
  | .named _ op, args, k, q, hq, x, hx => leftArm_sound L fuel hA op args k q hq x hx
  | .ilit t z, _, k, q, hq, x, hx => by
      cases t <;> simp only [leftArm, reduceCtorEq] at hq
      · rename_i w _
        refine bindOk_id P fuel W (t := .inl (.word w)) x k q (.lit z) ?_ hq
        change NfTy.ofLit? (.word w) z = some x at hx
        simp only [NfTy.ofLit?] at hx
        split at hx
        · rename_i hr
          obtain rfl := Option.some.inj hx
          have h0 : (z.toNat : Int) = z := Int.toNat_of_nonneg hr.1
          have h1 : z.toNat < 2 ^ w := by
            have h2 := hr.2
            rw [← h0] at h2
            exact_mod_cast h2
          show ((BitVec.ofNat w z.toNat).toNat : Int) = z
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, h0]
        · cases hx
      · refine bindOk_id P fuel W (t := .inl .int) x k q (.lit z) ?_ hq
        exact (Option.some.inj hx).symm
  | .constUnit, _, k, q, hq, x, _ =>
      bindOk_id P fuel W (t := .inl .unit) x k q .none trivial hq
  | .ctr, .cons lo (.cons i .nil), k, q, hq, x, hx =>
      ctrArm_sound P fuel hA lo i k q hq x hx
  | .trip _, .cons lo (.cons hi .nil), k, q, hq, x, hx => tripArm_sound P fuel hA lo hi k q hq x hx
  | .const _ _, _, _, _, hq, _, _ | .constBit _, _, _, _, hq, _, _
  | .bin _ _, _, _, _, hq, _, _ | .un _ _, _, _, _, hq, _, _ | .cast _ _, _, _, _, hq, _, _
  | .scast _ _, _, _, _, hq, _, _ | .cmp _ _, _, _, _, hq, _, _ | .andB, _, _, _, hq, _, _
  | .orB, _, _, _, hq, _, _ | .xorB, _, _, _, hq, _, _ | .eqB, _, _, _, hq, _, _
  | .notB, _, _, _, hq, _, _ | .index _ _, _, _, _, hq, _, _ | .update _ _, _, _, _, hq, _, _
  | .arrLit _ _, _, _, _, hq, _, _ | .arrRepeat _ _, _, _, _, hq, _, _
  | .mkPair _ _, _, _, _, hq, _, _ | .fst _ _, _, _, _, hq, _, _ | .snd _ _, _, _, _, hq, _, _
  | .call _ _ _, _, _, _, hq, _, _ | .tnilV, _, _, _, hq, _, _
  | .tconsV _ _, _, _, _, hq, _, _ | .thead _ _, _, _, _, hq, _, _
  | .ttail _ _, _, _, _, hq, _, _ | .boundInt _, _, _, _, hq, _, _ => by simp [leftArm] at hq

/-- **The right arm keeps the value**: the array of the block holds the encoding of the
    value of the operation. -/
theorem fieldArm_sound (hn : n < 2 ^ 64) (fuel : Nat) {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ} {X : Valuation Δ} {W : Valuation Θ}
    (hA : JAgree P ρ X W) {us : List JasminTy} (op : fieldDialect.Op)
    (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inr))
    (k : BindK n Θ (.inr (DialectSignature.ret op)) us) (q : NFProg jasminDialect Θ us)
    (hq : fieldArm P ρ op args k = some q) :
    BindOk P fuel W (t := .inr (DialectSignature.ret op))
      (DialectDenote.denote op (unmapInr (Expr.lookupArgs args X))) k q := by
  unfold fieldArm at hq
  split at hq
  · rename_i hg
    obtain ⟨as, has, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨o, -, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨Θ', h, res, W', q', hp, hres, hk, hden⟩ := spliceNF?_fwd fuel _ _ W q hq
    refine ⟨Θ', h, .var res, W', q', hp, ?_, hk, hden⟩
    change arrLimbs (res.lookup W') n 0 = FieldLowerTemplate.enc P _
    rw [hres, FieldDialectBlockDescent.Com.denote_rename, pullV_hvToHom, lookupVars_hvAppend,
      show MultiReturnCom.lookupVars (HVector.cons o HVector.nil) W =
        HVector.cons (o.lookup W) .nil from rfl,
      FieldLowerTemplate.block_denote P op hg hn (unmapInr (Expr.lookupArgs args X)) _ _
        (fldArrs_rel P hA args as has)]
  · cases hq

/-- **The right arm at a Montgomery record keeps the value**: the array of the block holds
    the Montgomery limbs of the value of the operation. -/
theorem rightArm_sound {n : Nat} (P : LimbParams n) (hn : n < 2 ^ 64) (fuel : Nat)
    {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ} {X : Valuation Δ}
    {W : Valuation Θ} (hA : JAgree P ρ X W) {us : List JasminTy} (op : fieldDialect.Op)
    (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inr))
    (k : BindK n Θ (.inr (DialectSignature.ret op)) us) (q : NFProg jasminDialect Θ us)
    (hq : rightArm P ρ op args k = some q) :
    BindOk P fuel W (t := .inr (DialectSignature.ret op))
      (DialectDenote.denote op (unmapInr (Expr.lookupArgs args X))) k q :=
  fieldArm_sound P hn fuel hA op args k q hq

/-- **A translated binding keeps the value.** -/
theorem bindF_sound (L : NfLeafTable) (hn : n < 2 ^ 64) (fuel : Nat) {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} {ρ : JRen n Δ Θ} {X : Valuation Δ} {W : Valuation Θ}
    (hA : JAgree P ρ X W) {us : List JasminTy} :
    ∀ {t : nfFieldDialect.Ty} (e : Expr nfFieldDialect Δ t) (k : BindK n Θ t us)
      (q : NFProg jasminDialect Θ us), bindF P ρ e k = some q → ∀ x,
        @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote L) Δ t e X = some x →
          BindOk P fuel W x k q
  | _, ⟨.inl op, rfl, args⟩, k, q, hq, x, hx => leftArm_sound P L fuel hA op args k q hq x hx
  | _, ⟨.inr op, rfl, args⟩, k, q, hq, x, hx => by
      have hx' : some (DialectDenote.denote op (unmapInr (Expr.lookupArgs args X))) = some x :=
        hx
      cases Option.some.inj hx'
      exact fieldArm_sound P hn fuel hA op args k q hq

/-- **The lowering keeps the values at the carriers.** For a program `prog` lowered from the
    renaming `ρ`, valuations `X`, `W` related along `ρ` and every leaf table `L`: a run of
    `prog` to the result `R` is matched, at every fuel, by a run of the lowered program to a
    result related to `R` by `JRelV`. -/
theorem lowerF_sound (L : NfLeafTable) (hn : n < 2 ^ 64) (fuel fuel' : Nat) :
    ∀ {Δ : Ctxt nfFieldDialect} {ts : List nfFieldDialect.Ty}
      (prog : NFProg nfFieldDialect Δ ts) {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
      (q : NFProg jasminDialect Θ (ts.map (jTy n))), lowerF P prog ρ = some q →
      ∀ (X : Valuation Δ) (W : Valuation Θ), JAgree P ρ X W →
        ∀ R, SDenL L fuel prog X = some R → ∃ R', q.denote fuel' W = some R' ∧ JRelV P R R'
  | _, _, .ret vs, _, ρ, q, h, X, W, hA, R, hR => by
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
      cases hR
      exact ⟨_, rfl, retVars_rel P hA vs ws hws⟩
  | _, _, .var e k, _, ρ, q, h, X, W, hA, R, hR => by
      obtain ⟨x, hx, hR⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨Θ', g, r, W', q', hp, hr, hk, hden⟩ := bindF_sound P L hn fuel' hA e _ q h x hx
      obtain ⟨R', hR', hrel⟩ :=
        lowerF_sound L hn fuel fuel' k (ρ.lift g r) q' hk _ _ (hA.lift P hp r x hr) R hR
      exact ⟨R', hden.trans hR', hrel⟩
  | _, _, .forLoop (cs := cs) count inits body k, _, ρ, q, h, X, W, hA, R, hR => by
      simp only [lowerF] at h
      split at h
      · rename_i c hc
        obtain ⟨ivs, hivs, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨accF, hfold, hkout⟩ := Option.bind_eq_some_iff.mp hR
        have hcnt : BitVec.toNat (c.lookup W) = BitVec.toNat (count.lookup X) := by
          have h0 : (ρ count).rel P W (count.lookup X) := hA _ count
          rw [hc] at h0
          exact h0
        obtain ⟨accF', hfold', hrF⟩ := NFProg.foldlM_rel_fwd (R := JRelV P (ts := cs)) _
          (fun j _ acc acc' a1 hr ha1 =>
            lowerF_sound L hn fuel fuel' body _ b hb _ _
              (JAgree.app P (hA.lift P (h := fun v => .there v)
                (W' := W.extend (BitVec.ofNat 64 j)) (fun _ => rfl) (.var .here)
                (BitVec.ofNat 64 j) (by exact rfl)) cs acc acc' hr) a1 ha1)
          _ _ accF (retVars_rel P hA inits ivs hivs) hfold
        obtain ⟨R', hR', hrel⟩ := lowerF_sound L hn fuel fuel' k _ k' hk _ _
          (JAgree.app P hA cs accF accF' hrF) R hkout
        refine ⟨R', ?_, hrel⟩
        change ((List.range (BitVec.toNat (c.lookup W))).foldlM
            (fun acc j => b.denote fuel'
              (hvAppend acc (HVector.cons (t := JasminTy.reg 64) (BitVec.ofNat 64 j) W)))
            (Expr.lookupArgs ivs W)).bind (fun acc => k'.denote fuel' (hvAppend acc W)) =
          some R'
        rw [hcnt]
        erw [hfold']
        exact hR'
      · cases h
  | _, _, .ifThenElse _ _ _ _, _, _, _, h, _, _, _, _, _ => by simp [lowerF] at h
  | _, _, .whileLoop _ _ _, _, _, _, h, _, _, _, _, _ => by simp [lowerF] at h
  | _, _, .call _ _ _, _, _, _, h, _, _, _, _, _ => by simp [lowerF] at h

/-! ## 5. The steps and the chain -/

open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.Hax.NFFieldSum (Kind KRelV SRen SAgree CallsAgree nfToSum nfToSum_sound)
open CatCrypt.Hax.PrimeirNames (OpTable)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf)
open _root_.Hax (Builtins)

/-- The renaming of a context carried at the kinds `ks`: each variable at its kind, by the
    variable of its position. -/
def kindRen {p : Nat} : {Γ : Ctxt nfDialect} → (ks : HVector (Kind p) Γ) →
    SRen p Γ (Hax.NFFieldSum.kTys ks)
  | [], .nil => fun v => nomatch v
  | _ :: _, .cons k ks => SRen.lift (kindRen ks) k

theorem kindRen_agree {p : Nat} : ∀ {Γ : Ctxt nfDialect} (ks : HVector (Kind p) Γ)
    (V : Valuation Γ) (X : Valuation (Hax.NFFieldSum.kTys ks)), KRelV ks V X →
      SAgree (kindRen ks) V X
  | [], .nil, _, _, _ => fun _ v => nomatch v
  | _ :: _, .cons k ks, .cons x V, X, h => by
      change Valuation (d := nfFieldDialect) (k.ty :: Hax.NFFieldSum.kTys ks) at X
      cases X with
      | cons y X => exact (kindRen_agree ks V X h.2).lift k x y h.1

variable (n) in
/-- The renaming of a context to the readings by the carrier variable of each position. -/
def idRen : (Δ : Ctxt nfFieldDialect) → JRen n Δ (Δ.map (jTy n))
  | [] => fun v => nomatch v
  | _ :: Δ => JRen.lift (idRen Δ) (fun v => .there v) (.var .here)

theorem idRen_agree : ∀ (Δ : Ctxt nfFieldDialect) (X : Valuation Δ)
    (W : Valuation (d := jasminDialect) (Δ.map (jTy n))), JRelV P X W → JAgree P (idRen n Δ) X W
  | [], _, _, _ => fun _ v => nomatch v
  | _ :: Δ, .cons x X, .cons _ W, h =>
      (idRen_agree Δ X W h.2).lift P (h := fun v => .there v) (fun _ => rfl) (.var .here) x h.1

/-- The semantics of programs of `nfFieldDialect` at the builtin table `bi` and the fuel
    `tf`. -/
abbrev nfFieldSemB (bi : Builtins) (tf : Nat) (Δ : Ctxt nfFieldDialect)
    (ts : List nfFieldDialect.Ty) : Sem (NFProg nfFieldDialect Δ ts) :=
  @nfSem tf nfFieldDialect _ _ _ _ (nfFieldDenote (tableOf bi)) _ Δ ts

/-- The program of a result of `nfToSum` whose one integer result is carried as a field
    element. -/
def fldOnly {p : Nat} {Δ : Ctxt nfFieldDialect} :
    (Σ ks : HVector (Kind p) [NfTy.int], NFProg nfFieldDialect Δ (Hax.NFFieldSum.kTys ks)) →
      Option (NFProg nfFieldDialect Δ [.inr (.fp p)])
  | ⟨.cons .fld .nil, q⟩ => some q
  | ⟨.cons (.nf _) .nil, _⟩ => none

theorem fldOnly_some {p : Nat} {Δ : Ctxt nfFieldDialect} :
    ∀ (r : Σ ks : HVector (Kind p) [NfTy.int], NFProg nfFieldDialect Δ (Hax.NFFieldSum.kTys ks))
      (q : NFProg nfFieldDialect Δ [.inr (.fp p)]), fldOnly r = some q →
        r = ⟨.cons .fld .nil, q⟩
  | ⟨.cons .fld .nil, _⟩, _, h => by cases h; rfl
  | ⟨.cons (.nf _) .nil, _⟩, _, h => by cases h

/-- The translation `nfToSum T p` at the modulus `p` of the template, from the renaming `σ`,
    as a chain step on a program with one integer result carried as a field element. -/
def sumStep (T : OpTable) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    (σ : SRen (FieldLowerTemplate.p P) Γ Δ) :
    Step (NFProg nfDialect Γ [.int])
      (NFProg nfFieldDialect Δ [.inr (.fp (FieldLowerTemplate.p P))]) :=
  ⟨"nfToSum", fun prog => (nfToSum T (FieldLowerTemplate.p P) prog σ).bind fldOnly⟩

/-- **The certificate of `sumStep`**, from `nfToSum_sound`: the input relation is the
    agreement along `σ`, and the output relation relates the integer result to its residue. -/
def sumCert (T : OpTable) (hT : T.ok = true) {bi : Builtins}
    (hbi : CallsAgree T (FieldLowerTemplate.p P) bi) (tf : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} (σ : SRen (FieldLowerTemplate.p P) Γ Δ) :
    StepCert (sumStep P T σ).run
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ Γ [.int])
      (nfFieldSemB bi tf Δ _) where
  relIn V X := SAgree σ V X
  relOut R R' := KRelV (HVector.cons (Kind.fld (p := FieldLowerTemplate.p P)) .nil)
    (show Valuation (d := nfDialect) [NfTy.int] from R)
    (show Valuation (Hax.NFFieldSum.kTys (HVector.cons (Kind.fld (p := FieldLowerTemplate.p P))
      .nil)) from R')
  sound := by
    intro prog q V X o hf hA hd
    obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hf
    cases fldOnly_some r q hf
    exact nfToSum_sound T hT hbi prog σ
      (HVector.cons (Kind.fld (p := FieldLowerTemplate.p P)) .nil) q hr V X hA tf o hd

/-- **The field lowering step** `fieldLowerStep`: `lowerF P` from the renaming `ρ`. -/
def fieldLowerStep {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    (ts : List nfFieldDialect.Ty) :
    Step (NFProg nfFieldDialect Δ ts) (NFProg jasminDialect Θ (ts.map (jTy n))) :=
  ⟨"fieldLower", fun prog => lowerF P prog ρ⟩

/-- **The certificate of the field lowering**, from `lowerF_sound`: the input relation is
    the agreement along `ρ`, the output relation `JRelV`, at every pair of fuels. -/
def fieldLowerCert (hn : n < 2 ^ 64) (bi : Builtins) (tf cf : Nat) {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) (ts : List nfFieldDialect.Ty) :
    StepCert (fieldLowerStep P ρ ts).run (nfFieldSemB bi tf Δ ts)
      (nfSem cf jasminDialect Θ (ts.map (jTy n))) where
  relIn X W := JAgree P ρ X W
  relOut R R' := JRelV P R R'
  sound := by
    intro prog q X W o hf hA hd
    exact lowerF_sound P (tableOf bi) hn tf cf prog ρ q hf X W hA o hd

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
