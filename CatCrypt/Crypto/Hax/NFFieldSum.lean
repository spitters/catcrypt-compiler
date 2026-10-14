/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.PrimeirNames
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel

/-!
# Field calls as the field summand of `nfDialect ⊕ fieldDialect`

The front `impToNF` carries a library call of the `primeir-hax` name table as the leaf call
`NfOp.call f as .int` of `nfDialect`. `nfToSum T p` translates a program of
`NFProg nfDialect` to a program of `NFProg nfFieldDialect`, where
`nfFieldDialect = Dialect.sum nfDialect fieldDialect`: a binding whose operation is a call of
a field entry of the name table `T`, on variables already carried as field elements, becomes
the operation of `fieldDialect` given by `T.toOp p` in the right summand; every other binding
stays an operation of `nfDialect` in the left summand. A counted loop carries its tuple at the
kinds of its initial values, and its body must return the tuple at the same kinds; branches,
exit-flag loops and call nodes are refused.

Each source variable is carried by a target variable of a kind (`Kind`): a variable of
`nfDialect` at its own type (`Kind.nf`), or, for an integer, a variable of `fieldDialect` at
the field `ZMod p` holding its residue (`Kind.fld`). `nfToSum_sound` states that the
translated program computes the values of the source at the `nf` kinds and their residues at
the `fld` kinds, for every builtin table that agrees with `T.builtins p` on the field entries
(`CallsAgree`).

`sumToField` reads a program of `NFProg nfFieldDialect` whose context and bindings all lie
in the right summand, straight-line with one result, as a program `Com fieldDialect`
(`sumToField_sound`).

## Main definitions

* `nfFieldDialect`, `nfFieldDenote`, `SDenP` — the summed dialect, its denotation at a leaf
  table, and the denotation of its programs at a builtin table.
* `Kind`, `SVar`, `SRen`, `SAgree` — the kinds, carried variables, renamings and their
  agreement with valuations.
* `CallsAgree` — a builtin table agrees with the builtins of a name table on its field
  entries.
* `nfToSum` — the translation to `NFProg nfFieldDialect`.
* `sumToField` — the reading of a field-only program as `Com fieldDialect`.
* `primeirFieldTable` — the six bare heads of the `primeir_hax::Field` methods.

## Main results

* `nfToSum_sound` — the translation keeps the values at the `nf` kinds and the residues at
  the `fld` kinds.
* `sumToField_sound` — the reading keeps the value.
* `primeirFieldTable_agrees` — `primeirBuiltins p` agrees with the table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFFieldSum

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.Hax.ImpToNF (tableOf enc dec encAll PDenP)
open CatCrypt.Hax.PrimeirNames
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)
open _root_.Hax (Value)

/-! ## 1. The summed dialect -/

/-- The coproduct of `nfDialect` and `fieldDialect`. -/
abbrev nfFieldDialect : Dialect := Dialect.sum nfDialect fieldDialect

instance : DialectSignature nfFieldDialect :=
  instDialectSignatureSum (d := nfDialect) (e := fieldDialect)

/-- The trip counter of `nfFieldDialect` is the counter of `nfDialect`. -/
instance : HasWord64 nfFieldDialect where
  word := .inl (NfTy.word 64)
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- The bit of `nfFieldDialect` is the bit of `nfDialect`. -/
instance : HasBoolBit nfFieldDialect where
  bit := .inl NfTy.bit
  toBool := id

/-- `nfFieldDialect` denotes calls in the empty environment. -/
instance : CallDenote nfFieldDialect := ⟨.empty⟩

/-- The denotation of `nfFieldDialect` at the leaf table `T`: an operation of the left
    summand by `nfDenoteOp T`, an operation of the right summand by its total denotation. -/
@[instance_reducible] def nfFieldDenote (T : NfLeafTable) :
    DialectDenoteM nfFieldDialect Option where
  denoteM
    | .inl o, args => nfDenoteOp T o (unmapInl args)
    | .inr o, args => some (DialectDenote.denote o (unmapInr args))

/-- The denotation of a program of `nfFieldDialect` at the builtin table `bi`. -/
abbrev SDenP (bi : _root_.Hax.Builtins) (fuel : Nat) {Γ : Ctxt nfFieldDialect}
    {ts : List nfFieldDialect.Ty} (p : NFProg nfFieldDialect Γ ts) (V : Valuation Γ) :
    Option (Valuation ts) :=
  @NFProg.denote nfFieldDialect _ _ _ _ (nfFieldDenote (tableOf bi)) _ fuel Γ ts p V

/-! ## 2. Kinds and carried variables -/

/-- The kind of a carried variable of the source type `t`: a variable of `nfDialect` at `t`,
    or, for an integer, a variable of the field `ZMod p` holding its residue. -/
inductive Kind (p : Nat) : NfTy → Type
  | nf (t : NfTy) : Kind p t
  | fld : Kind p .int

/-- The target type of a kind. -/
def Kind.ty {p : Nat} : {t : NfTy} → Kind p t → nfFieldDialect.Ty
  | t, .nf _ => .inl t
  | _, .fld => .inr (.fp p)

/-- The relation of a source value and a target value at a kind: equality at `nf`, the
    residue at `fld`. -/
def Kind.rel {p : Nat} : {t : NfTy} → (k : Kind p t) → t.denote → ⟦k.ty⟧ → Prop
  | _, .nf _, x, y => y = x
  | _, .fld, x, y => ((x : Int) : ZMod p) = y

/-- The target types of a vector of kinds. -/
def kTys {p : Nat} : {ts : List NfTy} → HVector (Kind p) ts → List nfFieldDialect.Ty
  | [], .nil => []
  | _ :: _, .cons k ks => k.ty :: kTys ks

/-- The relation of source and target valuations along a vector of kinds. -/
def KRelV {p : Nat} : {ts : List NfTy} → (ks : HVector (Kind p) ts) →
    Valuation (d := nfDialect) ts → Valuation (kTys ks) → Prop
  | [], .nil, _, _ => True
  | _ :: _, .cons k ks, .cons x xs, ys =>
      k.rel x (HVector.head (ys : Valuation (k.ty :: kTys ks))) ∧
        KRelV ks xs (HVector.tail (ys : Valuation (k.ty :: kTys ks)))

/-- A carried variable: a kind and a target variable of its type. -/
structure SVar (p : Nat) (Δ : Ctxt nfFieldDialect) (t : NfTy) where
  /-- The kind. -/
  k : Kind p t
  /-- The target variable. -/
  v : Var Δ k.ty

/-- A renaming sending every source variable to a carried variable. -/
abbrev SRen (p : Nat) (Γ : Ctxt nfDialect) (Δ : Ctxt nfFieldDialect) : Type :=
  ∀ {t : NfTy}, Var Γ t → SVar p Δ t

variable {p : Nat}

/-- A renaming under one more binding of the kind `k`. -/
def SRen.lift {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {s : NfTy} (σ : SRen p Γ Δ)
    (k : Kind p s) : SRen p (s :: Γ) (k.ty :: Δ)
  | _, .here => ⟨k, .here⟩
  | _, .there v => ⟨(σ v).k, .there (σ v).v⟩

/-- Every source variable is related to its carried variable. -/
def SAgree {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ)
    (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ (t : NfTy) (v : Var Γ t), (σ v).k.rel (v.lookup V) ((σ v).v.lookup W)

theorem SAgree.lift {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {σ : SRen p Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : SAgree σ V W) {s : NfTy} (k : Kind p s)
    (x : s.denote) (y : ⟦k.ty⟧) (hxy : k.rel x y) :
    SAgree (σ.lift k) (V.extend x) (W.extend y) := by
  intro t v
  cases v with
  | here => exact hxy
  | there v => exact h t v

/-- The carried variables of a vector of source variables. -/
def retArgs {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts →
      Σ ks : HVector (Kind p) ts, HVector (fun t => Var Δ t) (kTys ks)
  | [], .nil => ⟨.nil, .nil⟩
  | _ :: _, .cons v vs => ⟨.cons (σ v).k (retArgs σ vs).1, .cons (σ v).v (retArgs σ vs).2⟩

theorem retArgs_rel {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {σ : SRen p Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : SAgree σ V W) :
    ∀ {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts),
      KRelV (retArgs σ vs).1 (Expr.lookupArgs vs V) (Expr.lookupArgs (retArgs σ vs).2 W)
  | [], .nil => trivial
  | _ :: _, .cons v vs => ⟨h _ v, retArgs_rel h vs⟩

/-- The target variable of an `nf` carried variable. -/
def SVar.nf? {Δ : Ctxt nfFieldDialect} : {t : NfTy} → SVar p Δ t → Option (Var Δ (.inl t))
  | _, ⟨.nf _, w⟩ => some w
  | _, ⟨.fld, _⟩ => none

theorem SVar.nf?_lookup {Δ : Ctxt nfFieldDialect} {W : Valuation Δ} {t : NfTy} (s : SVar p Δ t)
    {w : Var Δ (.inl t)} (hw : s.nf? = some w) {x : t.denote}
    (hx : s.k.rel x (s.v.lookup W)) : w.lookup W = x := by
  rcases s with ⟨k, y⟩
  cases k with
  | nf _ => cases hw; exact hx
  | fld => cases hw

/-- The target variables of `nf` carried variables. -/
def nfArgs {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts →
      Option (HVector (fun t => Var Δ t) (ts.map Sum.inl))
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (σ v).nf?.bind fun w => (nfArgs σ vs).map (.cons w)

theorem nfArgs_lookup {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {σ : SRen p Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : SAgree σ V W) :
    ∀ {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts)
      (ws : HVector (fun t => Var Δ t) (ts.map Sum.inl)), nfArgs σ vs = some ws →
      unmapInl (e := fieldDialect) (Expr.lookupArgs ws W) = Expr.lookupArgs vs V
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons v vs, .cons w ws, hw => by
      obtain ⟨w', hw', hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨ws', hws', hc⟩ := Option.map_eq_some_iff.mp hw
      cases hc
      change HVector.cons _ _ = HVector.cons _ _
      rw [nfArgs_lookup h vs ws hws', SVar.nf?_lookup _ hw' (h _ v)]

/-- The target variable of a `fld` carried variable. -/
def SVar.fld? {Δ : Ctxt nfFieldDialect} : {t : NfTy} → SVar p Δ t →
    Option (Var Δ (.inr (.fp p)))
  | _, ⟨.fld, w⟩ => some w
  | _, ⟨.nf _, _⟩ => none

theorem SVar.fld?_lookup {Δ : Ctxt nfFieldDialect} {W : Valuation Δ} {t : NfTy}
    (s : SVar p Δ t) {w : Var Δ (.inr (.fp p))} (hw : s.fld? = some w) {x : t.denote}
    (hx : s.k.rel x (s.v.lookup W)) :
    ∃ h : t = .int, ((cast (congrArg NfTy.denote h) x : Int) : ZMod p) = w.lookup W := by
  rcases s with ⟨k, y⟩
  cases k with
  | nf _ => cases hw
  | fld => cases hw; exact ⟨rfl, hx⟩

/-- The target variables of `fld` carried variables. -/
def fldArgs {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts → Option (List (Var Δ (.inr (.fp p))))
  | [], .nil => some []
  | _ :: _, .cons v vs => (σ v).fld?.bind fun w => (fldArgs σ vs).map (w :: ·)

theorem fldArgs_lookup {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {σ : SRen p Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : SAgree σ V W) :
    ∀ {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts)
      (ws : List (Var Δ (.inr (.fp p)))), fldArgs σ vs = some ws →
      ∃ zs : List Int, encAll ts (Expr.lookupArgs vs V) = zs.map Value.int ∧
        zs.map (Int.cast : Int → ZMod p) = ws.map (fun w => w.lookup W)
  | [], .nil, ws, hw => by
      cases hw
      exact ⟨[], rfl, rfl⟩
  | _ :: _, .cons v vs, ws, hw => by
      obtain ⟨w', hw', hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨ws', hws', rfl⟩ := Option.map_eq_some_iff.mp hw
      obtain ⟨zs, hzs, hz⟩ := fldArgs_lookup h vs ws' hws'
      obtain ⟨ht, hv⟩ := SVar.fld?_lookup _ hw' (h _ v)
      subst ht
      refine ⟨v.lookup V :: zs, ?_, ?_⟩
      · change enc .int (v.lookup V) :: encAll _ (Expr.lookupArgs vs V) = _
        rw [hzs]
        rfl
      · simp only [List.map_cons, hz]
        exact congrArg (· :: _) hv

/-! ## 3. The field arm -/

/-- The context of one field variable at the modulus `p` for each entry of `ws`. -/
def locCtx (p : Nat) {α : Type} : List α → Ctxt fieldDialect
  | [] => []
  | _ :: ws => FieldTy.fp p :: locCtx p ws

/-- The variables of `locCtx p ws`, in order. -/
def locVars (p : Nat) {α : Type} : (ws : List α) → List (Var (locCtx p ws) (FieldTy.fp p))
  | [] => []
  | _ :: ws => .here :: (locVars p ws).map .there

/-- The variable of the summed context that a variable of `locCtx p ws` stands for. -/
def locMap {Δ : Ctxt nfFieldDialect} : (ws : List (Var Δ (.inr (.fp p)))) → {t : FieldTy} →
    Var (locCtx p ws) t → Var Δ (.inr t)
  | w :: _, _, .here => w
  | _ :: ws, _, .there v => locMap ws v

/-- The valuation of `locCtx p ws` read from the variables `ws` at `W`. -/
def locVal {Δ : Ctxt nfFieldDialect} (W : Valuation Δ) :
    (ws : List (Var Δ (.inr (.fp p)))) → Valuation (locCtx p ws)
  | [] => .nil
  | w :: ws => .cons (w.lookup W) (locVal W ws)

theorem locMap_lookup {Δ : Ctxt nfFieldDialect} (W : Valuation Δ) :
    ∀ (ws : List (Var Δ (.inr (.fp p)))) {t : FieldTy} (v : Var (locCtx p ws) t),
      (locMap ws v).lookup W = v.lookup (locVal W ws)
  | _ :: _, _, .here => rfl
  | _ :: ws, _, .there v => locMap_lookup W ws v

theorem locVars_lookup {Δ : Ctxt nfFieldDialect} (W : Valuation Δ) :
    ∀ ws : List (Var Δ (.inr (.fp p))),
      (locVars p ws).map (fun v => v.lookup (locVal W ws)) = ws.map (fun w => w.lookup W)
  | [] => rfl
  | w :: ws => by
      change w.lookup W :: ((locVars p ws).map (Var.there (s := FieldTy.fp p))).map
          (fun v => v.lookup (HVector.cons (w.lookup W) (locVal W ws))) = _
      rw [List.map_map]
      exact congrArg (_ :: ·) (locVars_lookup W ws)

/-- The arguments of an expression of `fieldDialect` carried into the summed context. -/
def liftInrArgs {Δf : Ctxt fieldDialect} {Δ : Ctxt nfFieldDialect}
    (ι : ∀ {t : FieldTy}, Var Δf t → Var Δ (.inr t)) :
    {ts : List FieldTy} → HVector (fun t => Var Δf t) ts →
      HVector (fun t => Var Δ t) (ts.map Sum.inr)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (ι v) (liftInrArgs ι vs)

/-- An expression of `fieldDialect` as an expression of the right summand. -/
def liftInr {Δf : Ctxt fieldDialect} {Δ : Ctxt nfFieldDialect}
    (ι : ∀ {t : FieldTy}, Var Δf t → Var Δ (.inr t)) {t : FieldTy}
    (e : Expr fieldDialect Δf t) : Expr nfFieldDialect Δ (.inr t) :=
  ⟨.inr e.op, congrArg Sum.inr e.retTy_eq, liftInrArgs ι e.args⟩

theorem liftInrArgs_lookup {Δf : Ctxt fieldDialect} {Δ : Ctxt nfFieldDialect}
    {ι : ∀ {t : FieldTy}, Var Δf t → Var Δ (.inr t)} {Wf : Valuation Δf} {W : Valuation Δ}
    (hι : ∀ (t : FieldTy) (v : Var Δf t), (ι v).lookup W = v.lookup Wf) :
    ∀ {ts : List FieldTy} (vs : HVector (fun t => Var Δf t) ts),
      unmapInr (d := nfDialect) (Expr.lookupArgs (liftInrArgs ι vs) W) = Expr.lookupArgs vs Wf
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      change HVector.cons _ _ = HVector.cons _ _
      rw [liftInrArgs_lookup hι vs, hι _ v]

/-- **A lifted expression denotes as its source**, at a valuation agreeing on the lifted
    variables. -/
theorem liftInr_denote (L : NfLeafTable) {Δf : Ctxt fieldDialect} {Δ : Ctxt nfFieldDialect}
    {ι : ∀ {t : FieldTy}, Var Δf t → Var Δ (.inr t)} {Wf : Valuation Δf} {W : Valuation Δ}
    (hι : ∀ (t : FieldTy) (v : Var Δf t), (ι v).lookup W = v.lookup Wf) {t : FieldTy}
    (e : Expr fieldDialect Δf t) :
    @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote L) Δ _ (liftInr ι e) W =
      some (e.denote Wf) := by
  obtain ⟨op, rfl, args⟩ := e
  change some (DialectDenote.denote op (unmapInr (Expr.lookupArgs (liftInrArgs ι args) W))) = _
  rw [liftInrArgs_lookup hι]
  rfl

/-- A builtin table agrees with the builtins of the name table `T` at the modulus `p` on the
    calls of the names of `T`, on integers. -/
def CallsAgree (T : OpTable) (p : Nat) (bi : _root_.Hax.Builtins) : Prop :=
  ∀ (f : String) (zs : List Int), (T.entry? f).isSome = true →
    bi f (zs.map Value.int) = T.builtins p f (zs.map Value.int)

/-- The field arm of a call: the op of `T.toOp p` on the field variables carrying its
    arguments. -/
def fieldArm (T : OpTable) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ)
    (f : String) {as : List NfTy} (args : HVector (fun t => Var Γ t) as) :
    Option (Expr nfFieldDialect Δ (.inr (.fp p))) :=
  (fldArgs σ args).bind fun ws =>
    (T.toOp p (Δ := locCtx p ws) f (locVars p ws)).map (liftInr (locMap ws))

/-- The field arm of an operation of `nfDialect`: a call, under its source name or none. -/
def opArm (T : OpTable) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ) :
    (op : NfOp) → HVector (fun t => Var Γ t) (DialectSignature.sig (d := nfDialect) op) →
      Option (Expr nfFieldDialect Δ (.inr (.fp p)))
  | .named _ op, args => opArm T σ op args
  | .call f _ _, args => fieldArm T σ f args
  | _, _ => none

/-- **The field arm computes the residue.** -/
theorem opArm_sound (T : OpTable) (hT : T.ok = true) {bi : _root_.Hax.Builtins}
    (hbi : CallsAgree T p bi) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {σ : SRen p Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hA : SAgree σ V W) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := nfDialect) op))
      (e' : Expr nfFieldDialect Δ (.inr (.fp p))), opArm T σ op args = some e' →
      ∀ x, nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some x →
        ∃ z : Int, enc op.ret x = .int z ∧
          ∃ y, @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote (tableOf bi)) Δ _ e' W =
            some y ∧ (z : ZMod p) = y
  | .named _ op, args, e', h, x, hx => opArm_sound T hT hbi hA op args e' h x hx
  | .call f as r, args, e', h, x, hx => by
      change (bi f (encAll as (Expr.lookupArgs args V))).bind (dec r) = some x at hx
      change fieldArm T σ f args = some e' at h
      obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e'', he'', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨zs, hzs, hz⟩ := fldArgs_lookup hA args ws hws
      obtain ⟨z, hb, hzv⟩ := T.toOp_sound p hT f (locVars p ws) e'' he'' (locVal W ws) zs
        (by rw [hz, locVars_lookup W ws])
      have hsome : (T.entry? f).isSome = true := by
        unfold OpTable.toOp at he''
        cases hE : T.entry? f with
        | none => rw [hE] at he''; cases he''
        | some _ => rfl
      have hzs' : encAll as (Expr.lookupArgs args V) = zs.map Value.int := hzs
      rw [hzs', hbi f zs hsome, hb] at hx
      refine ⟨z, ?_, _, liftInr_denote _ (fun _ v => locMap_lookup W ws v) e'', hzv⟩
      have hx' : dec r (.int z) = some x := by
        simpa using hx
      exact (ImpToNF.dec_sound r _ x hx').symm
  | .const _ _, _, _, h, _, _ | .constBit _, _, _, h, _, _ | .constUnit, _, _, h, _, _
  | .bin _ _, _, _, h, _, _ | .un _ _, _, _, h, _, _ | .cast _ _, _, _, h, _, _
  | .scast _ _, _, _, h, _, _ | .cmp _ _, _, _, h, _, _ | .andB, _, _, h, _, _
  | .orB, _, _, h, _, _ | .xorB, _, _, h, _, _ | .eqB, _, _, h, _, _
  | .notB, _, _, h, _, _ | .index _ _, _, _, h, _, _ | .update _ _, _, _, h, _, _
  | .arrLit _ _, _, _, h, _, _ | .arrRepeat _ _, _, _, h, _, _
  | .mkPair _ _, _, _, h, _, _ | .fst _ _, _, _, h, _, _ | .snd _ _, _, _, h, _, _
  | .ilit _ _, _, _, h, _, _ | .ctr, _, _, h, _, _ | .trip _, _, _, h, _, _
  | .tnilV, _, _, h, _, _ | .tconsV _ _, _, _, h, _, _ | .thead _ _, _, _, h, _, _
  | .ttail _ _, _, _, h, _, _ | .boundInt _, _, _, h, _, _ => nomatch h

/-! ## 4. The translation -/

/-- A renaming under a carried tuple of the kinds `ks`. -/
def SRen.app {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ) :
    {cs : List NfTy} → (ks : HVector (Kind p) cs) → SRen p (cs ++ Γ) (kTys ks ++ Δ)
  | [], .nil => σ
  | _ :: _, .cons k ks => SRen.lift (SRen.app σ ks) k

theorem SAgree.app {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {σ : SRen p Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : SAgree σ V W) :
    ∀ {cs : List NfTy} (ks : HVector (Kind p) cs) (A : Valuation (d := nfDialect) cs)
      (B : Valuation (kTys ks)), KRelV ks A B →
      SAgree (SRen.app σ ks) (hvAppend A V) (hvAppend B W)
  | [], .nil, .nil, B, _ => by
      change Valuation (d := nfFieldDialect) [] at B
      cases B
      exact h
  | _ :: _, .cons k ks, .cons x A, B, hAB => by
      change Valuation (d := nfFieldDialect) (k.ty :: kTys ks) at B
      cases B with
      | cons y B => exact (SAgree.app h ks A B hAB.2).lift k x y hAB.1

/-- Whether a kind is `fld`. -/
def Kind.isFld {p : Nat} : {t : NfTy} → Kind p t → Bool
  | _, .nf _ => false
  | _, .fld => true

/-- The `fld` flags of a vector of kinds. -/
def kFlags {p : Nat} : {ts : List NfTy} → HVector (Kind p) ts → List Bool
  | [], .nil => []
  | _ :: _, .cons k ks => k.isFld :: kFlags ks

theorem Kind.eq_of_isFld {t : NfTy} : ∀ (k k' : Kind p t), k.isFld = k'.isFld → k = k'
  | .nf _, .nf _, _ => rfl
  | .fld, k', h => by cases k' <;> first | rfl | cases h
  | .nf _, .fld, h => by cases h

theorem kFlags_inj : ∀ {ts : List NfTy} (ks ks' : HVector (Kind p) ts),
    kFlags ks = kFlags ks' → ks = ks'
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons k ks, .cons k' ks', h => by
      simp only [kFlags, List.cons.injEq] at h
      rw [Kind.eq_of_isFld k k' h.1, kFlags_inj ks ks' h.2]

/-- A field expression as the binding of a source integer at the kind `fld`. -/
def fieldBind {Δ : Ctxt nfFieldDialect} : (t : NfTy) →
    Option (Expr nfFieldDialect Δ (.inr (.fp p))) →
      Option (Σ k : Kind p t, Expr nfFieldDialect Δ k.ty)
  | .int, some e => some ⟨.fld, e⟩
  | _, _ => none

/-- An expression of `nfDialect` on `nf` carried variables, in the left summand. -/
def nfBind {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ) {t : NfTy}
    (e : Expr nfDialect Γ t) : Option (Σ k : Kind p t, Expr nfFieldDialect Δ k.ty) :=
  (nfArgs σ e.args).map fun args' =>
    ⟨.nf t, ⟨.inl e.op, congrArg Sum.inl e.retTy_eq, args'⟩⟩

/-- The binding of an expression: the field arm of a call of a field entry of `T` on `fld`
    carried variables, else the expression of `nfDialect` on `nf` carried variables. -/
def bindOf (T : OpTable) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen p Γ Δ)
    {t : NfTy} (e : Expr nfDialect Γ t) : Option (Σ k : Kind p t, Expr nfFieldDialect Δ k.ty) :=
  fieldBind t (opArm T σ e.op e.args) <|> nfBind σ e

theorem fieldBind_rel (L : NfLeafTable) {Δ : Ctxt nfFieldDialect} {W : Valuation Δ} {t : NfTy}
    {e₁ : Expr nfFieldDialect Δ (.inr (.fp p))} {k : Kind p t} {e' : Expr nfFieldDialect Δ k.ty}
    (h : fieldBind t (some e₁) = some ⟨k, e'⟩) {x : t.denote} {z : Int} {y : ZMod p}
    (hz : enc t x = .int z)
    (hy : @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote L) Δ _ e₁ W = some y)
    (hzy : (z : ZMod p) = y) :
    ∃ y', @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote L) Δ _ e' W = some y' ∧
      k.rel x y' := by
  cases t <;> try cases h
  cases Value.int.inj hz
  exact ⟨y, hy, hzy⟩

theorem nfBind_sound {bi : _root_.Hax.Builtins} {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {σ : SRen p Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hA : SAgree σ V W) {op : NfOp}
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := nfDialect) op))
    (k : Kind p op.ret) (e' : Expr nfFieldDialect Δ k.ty)
    (he : nfBind σ (⟨op, rfl, args⟩ : Expr nfDialect Γ op.ret) = some ⟨k, e'⟩)
    (x : op.ret.denote) (hx : nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some x) :
    ∃ y, @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote (tableOf bi)) Δ _ e' W =
      some y ∧ k.rel x y := by
  obtain ⟨args', ha, he⟩ := Option.map_eq_some_iff.mp he
  cases he
  refine ⟨x, ?_, rfl⟩
  change nfDenoteOp (tableOf bi) op (unmapInl (Expr.lookupArgs args' W)) = some x
  rw [nfArgs_lookup hA args args' ha]
  exact hx

/-- **A translated binding keeps the value at its kind.** -/
theorem bindOf_sound (T : OpTable) (hT : T.ok = true) {bi : _root_.Hax.Builtins}
    (hbi : CallsAgree T p bi) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {σ : SRen p Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hA : SAgree σ V W) {t : NfTy}
    (e : Expr nfDialect Γ t) (k : Kind p t) (e' : Expr nfFieldDialect Δ k.ty)
    (he : bindOf T σ e = some ⟨k, e'⟩) (x : t.denote)
    (hx : @Expr.denoteM nfDialect Option _ _ (nfDenote (tableOf bi)) Γ t e V = some x) :
    ∃ y, @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote (tableOf bi)) Δ _ e' W =
      some y ∧ k.rel x y := by
  obtain ⟨op, rfl, args⟩ := e
  change nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some x at hx
  change (fieldBind op.ret (opArm T σ op args) <|> nfBind σ ⟨op, rfl, args⟩) = _ at he
  cases hF : opArm T σ op args with
  | some e₁ =>
      obtain ⟨z, hz, y, hy, hzy⟩ := opArm_sound T hT hbi hA op args e₁ hF x hx
      rw [hF] at he
      cases hB : fieldBind (p := p) (Δ := Δ) op.ret (some e₁) with
      | some b =>
          rw [hB] at he
          cases he
          exact fieldBind_rel _ hB hz hy hzy
      | none =>
          rw [hB] at he
          exact nfBind_sound hA args k e' he x hx
  | none =>
      rw [hF] at he
      have h0 : fieldBind (p := p) (Δ := Δ) op.ret none = none := by
        cases op.ret <;> rfl
      rw [h0] at he
      exact nfBind_sound hA args k e' he x hx

/-- A program at the result kinds `ks` as a program at equal result kinds `ks'`. -/
def castKinds {Δ : Ctxt nfFieldDialect} {ts : List NfTy} {ks ks' : HVector (Kind p) ts}
    (h : ks = ks') (q : NFProg nfFieldDialect Δ (kTys ks)) : NFProg nfFieldDialect Δ (kTys ks') :=
  Eq.rec (motive := fun ks' _ => NFProg nfFieldDialect Δ (kTys ks')) q h

/-- **The translation to `NFProg nfFieldDialect`** from the renaming `σ`: each binding by
    `bindOf`, the result vector at the kinds of its carried variables, and a counted loop
    with its counter at `nf` and its tuple at the kinds of its initial values, when the body
    returns the tuple at these kinds. Branches, exit-flag loops and call nodes are refused. -/
def nfToSum (T : OpTable) (p : Nat) : {Γ : Ctxt nfDialect} → {Δ : Ctxt nfFieldDialect} →
    {ts : List NfTy} → NFProg nfDialect Γ ts → SRen p Γ Δ →
      Option (Σ ks : HVector (Kind p) ts, NFProg nfFieldDialect Δ (kTys ks))
  | _, _, _, .ret vs, σ => some ⟨(retArgs σ vs).1, .ret (retArgs σ vs).2⟩
  | _, _, _, .var e k, σ => (bindOf T σ e).bind fun b =>
      (nfToSum T p k (SRen.lift σ b.1)).map fun r => ⟨r.1, .var b.2 r.2⟩
  | _, Δ, _, .forLoop count inits body k, σ =>
      (σ count).nf?.bind fun c =>
        (nfToSum T p body
            (SRen.app (SRen.lift σ (.nf (NfTy.word 64))) (retArgs σ inits).1)).bind fun b =>
          if h : kFlags b.1 = kFlags (retArgs σ inits).1 then
            (nfToSum T p k (SRen.app σ (retArgs σ inits).1)).map fun r =>
              ⟨r.1, .forLoop (c : Var Δ (HasWord64.word (d := nfFieldDialect)))
                (retArgs σ inits).2 (castKinds (kFlags_inj _ _ h) b.2) r.2⟩
          else none
  | _, _, _, _, _ => none

/-- **The translation keeps the values at the kinds.** For a program `prog` translated from
    the renaming `σ` with the result kinds `ks`, valuations `V`, `W` agreeing along `σ`, and a
    builtin table `bi` agreeing with `T.builtins p` on the names of `T`: a run of `prog` with
    the leaves of `bi` to the result `R` is matched by a run of the translated program to a
    result related to `R` along `ks`. -/
theorem nfToSum_sound (T : OpTable) (hT : T.ok = true) {bi : _root_.Hax.Builtins}
    (hbi : CallsAgree T p bi) :
    ∀ {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {ts : List NfTy}
      (prog : NFProg nfDialect Γ ts) (σ : SRen p Γ Δ) (ks : HVector (Kind p) ts)
      (q : NFProg nfFieldDialect Δ (kTys ks)), nfToSum T p prog σ = some ⟨ks, q⟩ →
      ∀ (V : Valuation Γ) (W : Valuation Δ), SAgree σ V W →
        ∀ (fuel : Nat) (R : Valuation (d := nfDialect) ts), PDenP bi fuel prog V = some R →
          ∃ R', SDenP bi fuel q W = some R' ∧ KRelV ks R R'
  | _, _, _, .ret vs, σ, ks, q, h, V, W, hA, fuel, R, hR => by
      cases h
      cases hR
      exact ⟨_, rfl, retArgs_rel hA vs⟩
  | _, _, _, .var e k, σ, ks, q, h, V, W, hA, fuel, R, hR => by
      obtain ⟨⟨kd, e'⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨ks', q'⟩, hq, h⟩ := Option.map_eq_some_iff.mp h
      cases h
      obtain ⟨x, hx, hR⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨y, hy, hxy⟩ := bindOf_sound T hT hbi hA e kd e' hb x hx
      obtain ⟨R', hR', hrel⟩ :=
        nfToSum_sound T hT hbi k _ ks' q' hq _ _ (hA.lift kd x y hxy) fuel R hR
      refine ⟨R', ?_, hrel⟩
      change (@Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote (tableOf bi)) _ _ e' W).bind
        (fun y => SDenP bi fuel q' (W.extend y)) = some R'
      rw [hy]
      exact hR'
  | _, _, _, .forLoop count inits body k, σ, ks, q, h, V, W, hA, fuel, R, hR => by
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨kb, b⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hfl
        obtain ⟨⟨kk, k'⟩, hk, h⟩ := Option.map_eq_some_iff.mp h
        cases h
        have heq := kFlags_inj _ _ hfl
        subst heq
        obtain ⟨accF, hfold, hkout⟩ := Option.bind_eq_some_iff.mp hR
        have hcnt : c.lookup W = count.lookup V := SVar.nf?_lookup _ hc (hA _ count)
        obtain ⟨accF', hfold', hrF⟩ := NFProg.foldlM_rel_fwd
          (R := KRelV (retArgs σ inits).1) _
          (fun j _ acc acc' a1 hr ha1 =>
            nfToSum_sound T hT hbi body _ _ b hb _ _
              (SAgree.app (hA.lift (.nf (NfTy.word 64)) (BitVec.ofNat 64 j)
                (BitVec.ofNat 64 j) rfl) _ acc acc' hr) fuel a1 ha1)
          _ _ accF (retArgs_rel hA inits) hfold
        obtain ⟨R', hR', hrel⟩ := nfToSum_sound T hT hbi k _ kk k' hk _ _
          (SAgree.app hA _ accF accF' hrF) fuel R hkout
        refine ⟨R', ?_, hrel⟩
        change ((List.range (BitVec.toNat (c.lookup W))).foldlM
            (fun acc j => SDenP bi fuel b
              (hvAppend acc (HVector.cons (t := Sum.inl (NfTy.word 64)) (BitVec.ofNat 64 j) W)))
            (Expr.lookupArgs (retArgs σ inits).2 W)).bind
          (fun acc => SDenP bi fuel k' (hvAppend acc W)) = some R'
        rw [hcnt]
        erw [hfold']
        exact hR'
      · cases h
  | _, _, _, .ifThenElse _ _ _ _, _, _, _, h, _, _, _, _, _, _ => nomatch h
  | _, _, _, .whileLoop _ _ _, _, _, _, h, _, _, _, _, _, _ => nomatch h
  | _, _, _, .call _ _ _, _, _, _, h, _, _, _, _, _, _ => nomatch h

/-! ## 5. The field summand as `Com fieldDialect` -/

/-- A context of `fieldDialect` in the right summand. -/
def inrCtx : Ctxt fieldDialect → Ctxt nfFieldDialect
  | [] => []
  | t :: Δ => .inr t :: inrCtx Δ

/-- A valuation of a context of `fieldDialect` as a valuation of its right-summand image. -/
def inrVal : {Δf : Ctxt fieldDialect} → Valuation Δf → Valuation (inrCtx Δf)
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons x (inrVal xs)

/-- A renaming of the right-summand variables of `Δ` into `Δf`. -/
abbrev IRen (Δ : Ctxt nfFieldDialect) (Δf : Ctxt fieldDialect) : Type :=
  ∀ {t : FieldTy}, Var Δ (.inr t) → Var Δf t

/-- The renaming under one more right-summand binding. -/
def IRen.lift {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect} {s : FieldTy}
    (ρ : IRen Δ Δf) : IRen (.inr s :: Δ) (s :: Δf)
  | _, .here => .here
  | _, .there v => .there (ρ v)

/-- The renaming of `inrCtx Δf` into `Δf`. -/
def IRen.inr : {Δf : Ctxt fieldDialect} → IRen (inrCtx Δf) Δf
  | _ :: _, _, .here => .here
  | _ :: _, _, .there v => .there (IRen.inr v)

/-- The right-summand variables agree with their images. -/
def IAgree {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect} (ρ : IRen Δ Δf)
    (W : Valuation Δ) (Wf : Valuation Δf) : Prop :=
  ∀ (t : FieldTy) (v : Var Δ (.inr t)), v.lookup W = (ρ v).lookup Wf

theorem IAgree.lift {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect} {ρ : IRen Δ Δf}
    {W : Valuation Δ} {Wf : Valuation Δf} (h : IAgree ρ W Wf) {s : FieldTy} (y : ⟦s⟧) :
    IAgree (IRen.lift (s := s) ρ) (W.extend (t := Sum.inr s) y) (Wf.extend y) := by
  intro t v
  cases v with
  | here => rfl
  | there v => exact h t v

theorem IAgree.inr : ∀ {Δf : Ctxt fieldDialect} (Wf : Valuation Δf),
    IAgree (IRen.inr (Δf := Δf)) (inrVal Wf) Wf
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ Wf, t, .there v => IAgree.inr Wf t v

/-- The arguments of a right-summand operation, renamed into `Δf`. -/
def unInrArgs {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect} (ρ : IRen Δ Δf) :
    {ts : List FieldTy} → HVector (fun t => Var Δ t) (ts.map Sum.inr) →
      HVector (fun t => Var Δf t) ts
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (ρ v) (unInrArgs ρ vs)

theorem unInrArgs_lookup {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect} {ρ : IRen Δ Δf}
    {W : Valuation Δ} {Wf : Valuation Δf} (h : IAgree ρ W Wf) :
    ∀ {ts : List FieldTy} (vs : HVector (fun t => Var Δ t) (ts.map Sum.inr)),
      unmapInr (d := nfDialect) (Expr.lookupArgs vs W) = Expr.lookupArgs (unInrArgs ρ vs) Wf
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      change HVector.cons _ _ = HVector.cons _ _
      rw [unInrArgs_lookup h vs, h _ v]

/-- A right-summand expression as an expression of `fieldDialect`. -/
def inrExpr? {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect} (ρ : IRen Δ Δf) {s : FieldTy} :
    Expr nfFieldDialect Δ (.inr s) → Option (Expr fieldDialect Δf s)
  | ⟨.inr o, h, args⟩ => some ⟨o, Sum.inr.inj h, unInrArgs ρ args⟩
  | ⟨.inl _, _, _⟩ => none

theorem inrExpr?_denote (L : NfLeafTable) {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect}
    {ρ : IRen Δ Δf} {W : Valuation Δ} {Wf : Valuation Δf} (h : IAgree ρ W Wf) {s : FieldTy}
    (e : Expr nfFieldDialect Δ (.inr s)) (e' : Expr fieldDialect Δf s)
    (he : inrExpr? ρ e = some e') :
    @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote L) Δ _ e W = some (e'.denote Wf) := by
  obtain ⟨o | o, hr, args⟩ := e
  · cases he
  · cases he
    have hr' : DialectSignature.ret o = s := Sum.inr.inj hr
    subst hr'
    change some (DialectDenote.denote o (unmapInr (Expr.lookupArgs args W))) = _
    rw [unInrArgs_lookup h args]
    rfl

/-- **The reading of a field-only program** as `Com fieldDialect`: a straight-line program
    of `nfFieldDialect` with one right-summand result, whose bindings are right-summand
    operations, renamed into `Δf` by `ρ`. -/
def sumToField {t : FieldTy} : {Δ : Ctxt nfFieldDialect} → {Δf : Ctxt fieldDialect} →
    {us : List nfFieldDialect.Ty} → NFProg nfFieldDialect Δ us → us = [.inr t] → IRen Δ Δf →
      Option (Com fieldDialect Δf t)
  | _, _, _, .ret vs, h, ρ => some (.ret (ρ (h ▸ vs).head))
  | _, _, _, .var (t := Sum.inr _) e k, h, ρ =>
      (inrExpr? ρ e).bind fun e' => (sumToField k h (IRen.lift ρ)).map (.var e')
  | _, _, _, _, _, _ => none

/-- **The reading keeps the value.** -/
theorem sumToField_sound (bi : _root_.Hax.Builtins) (fuel : Nat) {t : FieldTy} :
    ∀ {Δ : Ctxt nfFieldDialect} {Δf : Ctxt fieldDialect} {us : List nfFieldDialect.Ty}
      (q : NFProg nfFieldDialect Δ us) (hus : us = [.inr t]) (ρ : IRen Δ Δf)
      (c : Com fieldDialect Δf t), sumToField q hus ρ = some c →
      ∀ (W : Valuation Δ) (Wf : Valuation Δf), IAgree ρ W Wf →
        SDenP bi fuel q W = some (hus ▸ .cons (c.denote Wf) .nil)
  | _, _, _, .ret vs, hus, ρ, c, h, W, Wf, hA => by
      subst hus
      cases h
      rcases vs with _ | ⟨v, _ | _⟩
      change some (HVector.cons (v.lookup W) .nil) = _
      rw [hA _ v]
      rfl
  | _, _, _, .var (t := Sum.inr _) e k, hus, ρ, c, h, W, Wf, hA => by
      obtain ⟨e', he', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
      subst hus
      change (@Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote (tableOf bi)) _ _ e W).bind
        (fun y => SDenP bi fuel k (W.extend y)) = _
      rw [inrExpr?_denote _ hA e e' he']
      exact sumToField_sound bi fuel k rfl _ c' hc' _ _ (hA.lift _)
  | _, _, _, .var (t := Sum.inl _) _ _, _, _, _, h, _, _, _ => nomatch h
  | _, _, _, .forLoop _ _ _ _, _, _, _, h, _, _, _ => nomatch h
  | _, _, _, .ifThenElse _ _ _ _, _, _, _, h, _, _, _ => nomatch h
  | _, _, _, .whileLoop _ _ _, _, _, _, h, _, _, _ => nomatch h
  | _, _, _, .call _ _ _, _, _, _, h, _, _, _ => nomatch h

/-! ## 6. The field route of a program with one integer result -/

/-- **The field program of a program of `nfDialect`** with one integer result, from a
    renaming into the right-summand image of `Δf`: the translation `nfToSum T p`, whose
    result must be carried at the kind `fld`, read as `Com fieldDialect` by `sumToField`. -/
def fieldOfNF (T : OpTable) (p : Nat) {Γ : Ctxt nfDialect} {Δf : Ctxt fieldDialect}
    {t : NfTy} (prog : NFProg nfDialect Γ [t]) (σ : SRen p Γ (inrCtx Δf)) :
    Option (Com fieldDialect Δf (.fp p)) :=
  (nfToSum T p prog σ).bind fun r => fldResults r.1 r.2
where
  /-- The field program of a translated program whose result is carried at `fld`. -/
  fldResult : {t : NfTy} → (k : Kind p t) → NFProg nfFieldDialect (inrCtx Δf) [k.ty] →
      Option (Com fieldDialect Δf (.fp p))
    | _, .fld, q => sumToField q rfl IRen.inr
    | _, .nf _, _ => none
  /-- `fldResult` at the kind of the one result. -/
  fldResults : {t : NfTy} → (ks : HVector (Kind p) [t]) →
      NFProg nfFieldDialect (inrCtx Δf) (kTys ks) → Option (Com fieldDialect Δf (.fp p))
    | _, .cons k .nil, q => fldResult k q

/-- **The field program computes the residue of the source result.** -/
theorem fieldOfNF_sound (T : OpTable) (hT : T.ok = true) {bi : _root_.Hax.Builtins}
    (hbi : CallsAgree T p bi) {Γ : Ctxt nfDialect} {Δf : Ctxt fieldDialect} {t : NfTy}
    (prog : NFProg nfDialect Γ [t]) (σ : SRen p Γ (inrCtx Δf))
    (c : Com fieldDialect Δf (.fp p)) (h : fieldOfNF T p prog σ = some c)
    (V : Valuation Γ) (Wf : Valuation Δf) (hA : SAgree σ V (inrVal Wf)) (fuel : Nat)
    (x : t.denote) (hR : PDenP bi fuel prog V = some (.cons x .nil)) :
    ∃ z : Int, enc t x = .int z ∧ (z : ZMod p) = c.denote Wf := by
  obtain ⟨⟨ks, q⟩, hq, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨R', hR', hrel⟩ := nfToSum_sound T hT hbi prog σ ks q hq V (inrVal Wf) hA fuel _ hR
  rcases ks with _ | ⟨k, _ | _⟩
  cases k with
  | nf _ => cases h
  | fld =>
      have hs := sumToField_sound bi fuel q rfl IRen.inr c h (inrVal Wf) Wf (IAgree.inr Wf)
      rw [hR'] at hs
      cases hs
      exact ⟨x, rfl, hrel.1⟩

/-! ## 7. The table of the bare method heads -/

/-- The field entries of the six bare method heads `add`, `sub`, `mul`, `neg`, `square`,
    `double`, the heads `primeirBuiltins` reads. -/
def primeirFieldTable : OpTable :=
  ⟨[fieldEntry "add" .add, fieldEntry "sub" .sub, fieldEntry "mul" .mul,
    fieldEntry "neg" .neg, fieldEntry "square" .square, fieldEntry "double" .double]⟩

theorem primeirFieldTable_ok : primeirFieldTable.ok = true := by
  simp [OpTable.ok, primeirFieldTable, fieldEntry_ok]

/-- **`primeirBuiltins p` agrees with the bare-head table** on its names. -/
theorem primeirFieldTable_agrees (p : Nat) :
    CallsAgree primeirFieldTable p (CatCrypt.Hax.primeirBuiltins p) := by
  intro f zs hf
  have hmem : f ∈ ["add", "sub", "mul", "neg", "square", "double"] := by
    simp only [OpTable.entry?, primeirFieldTable, fieldEntry, List.find?] at hf
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
    rw [beq_false_of_ne (Ne.symm h1), beq_false_of_ne (Ne.symm h2),
      beq_false_of_ne (Ne.symm h3), beq_false_of_ne (Ne.symm h4),
      beq_false_of_ne (Ne.symm h5), beq_false_of_ne (Ne.symm h6)] at hf
    exact Bool.false_ne_true hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, zs⟩⟩⟩ <;> rfl

end CatCrypt.Crypto.Hax.NFFieldSum
