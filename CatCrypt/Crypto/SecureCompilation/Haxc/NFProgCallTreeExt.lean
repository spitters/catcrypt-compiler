/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
public import CatCrypt.Crypto.Hax.NFToCatCall

/-!
# The call trees of the translation with declarations

In `nfDialect` a call of a leaf is an operation `NfOp.call f as r`, denoted by a leaf table
`NfLeafTable`. This module reads such an operation as one event of the signature `leafSig`
(`opTree`, `linkReader`); interpreting the call tree `treeAt linkReader` of a program under the
handler `leafHandler T` of a leaf table is the denotation at `nfDenote T`
(`interp_treeAt_linkReader`).

The translation `nfToCatExt D` turns a leaf call that `D` declares into the node `NFProg.call`
of `catCryptDialect`, and a leaf call that `catOp` accepts into operations of
`catCryptDialect`. At the tree level the first is an event of the source related to an event
of the target (`ExtRE`, `ExtRA`), the second a source event that the target skips, answered by
the leaf table of the builtin table (`nfToCatExt_ruttS`).

## Main definitions

* `LeafCall`, `leafSig`, `leafHandler`: the event of a leaf call and the handler of a table.
* `opTree`, `linkReader`: the tree of an operation and the expression reader of `nfDialect`.
* `ExtRE`, `ExtRA`, `OutRel`: the relations of events, answers and leaves of the translation.
* `NFExtTree`: the stage statement of the translation at the tree level.

## Main results

* `interp_opTree`, `interp_linkReader`, `interp_treeAt_linkReader`: adequacy of the readings.
* `linkReader_renameInv`: the reader is invariant under renaming, so `ruttS_treeAt_dce` applies
  to it.
* `ruttS_obind`, `ruttS_ofoldl`, `ruttS_owhileIter`, `RuttS.mono`: congruences of `RuttS` at
  a failed leaf `none`.
* `emitRes_elim`, `pinAll_elimQ`: the bindings of the translation preserve a property closed
  under let-bindings.
* `nfToCatExt_ruttS`: the stage lemma of `extCallStep` at the tree level.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## Leaf calls as events -/

/-- A call of a leaf of `nfDialect`: the name, the argument types, the result type and the
    argument values. -/
structure LeafCall where
  /-- The name of the leaf. -/
  name : String
  /-- The argument types. -/
  argTys : List NfTy
  /-- The result type. -/
  ret : NfTy
  /-- The argument values. -/
  args : HVector NfTy.denote argTys

/-- The event signature of leaf calls: a call is answered by a value of the result type, or by
    `none`. -/
abbrev leafSig : EventSig where
  Event := LeafCall
  Resp := fun c => Option c.ret.denote

/-- The handler of the leaf table `T`. -/
def leafHandler (T : NfLeafTable) : ∀ e : leafSig.Event, leafSig.Resp e :=
  fun c => T.call c.name c.argTys c.ret c.args

/-- The tree of an operation of `nfDialect` on its arguments: a leaf call is one event, under
    the source names of `named`; every other operation is the leaf of its denotation. -/
def opTree : (op : NfOp) → HVector NfTy.denote op.sig → CallTree leafSig (Option op.ret.denote)
  | .named _ op, a => opTree op a
  | .call f as r, a => .vis (⟨f, as, r, a⟩ : LeafCall) fun y => .ret y
  | op, a => .ret (nfDenoteOp NfLeafTable.empty op a)

/-- Under the handler of `T`, the tree of an operation interprets to its denotation. -/
theorem interp_opTree (T : NfLeafTable) :
    ∀ (op : NfOp) (a : HVector NfTy.denote op.sig),
      interp (leafHandler T) (opTree op a) = nfDenoteOp T op a := by
  intro op
  induction op with
  | named n op ih => exact ih
  | call f as r => intro a; rfl
  | _ => intro a; rfl

/-- The expression reader of `nfDialect` in which a leaf call is one event. -/
def linkReader : ExprReader leafSig nfDialect := fun e V =>
  match e with
  | ⟨op, h, args⟩ => h ▸ opTree op (Expr.lookupArgs args V)

/-- **Adequacy of the reader**: under the handler of `T`, the tree of an expression interprets
    to its denotation at `nfDenote T`. -/
theorem interp_linkReader (T : NfLeafTable) {Γ : Ctxt nfDialect} {t : NfTy}
    (e : Expr nfDialect Γ t) (V : Valuation Γ) :
    interp (leafHandler T) (linkReader e V) =
      @Expr.denoteM nfDialect Option _ _ (nfDenote T) Γ t e V := by
  obtain ⟨op, rfl, args⟩ := e
  exact interp_opTree T op _

/-- **Adequacy of the call tree of `nfDialect`**: under the handler of `T`, the tree at
    `linkReader` interprets to the denotation at `nfDenote T` and the call environment the
    handler induces from `tE`. -/
theorem interp_treeAt_linkReader (T : NfLeafTable) (tE : TreeCallEnv leafSig nfDialect)
    (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (V : Valuation Γ) :
    interp (leafHandler T) (treeAt linkReader tE fuel p V) =
      @NFProg.denoteAt nfDialect _ _ _ _ (nfDenote T) (tE.interpEnv (leafHandler T)) fuel
        Γ ts p V :=
  @interp_treeAt leafSig nfDialect _ _ _ _ (nfDenote T) (leafHandler T) linkReader
    (fun e V => interp_linkReader T e V) tE fuel Γ ts p V

/-- The reader of `nfDialect` is invariant under renaming, the hypothesis of the stage lemma
    of dead-binding elimination `ruttS_treeAt_dce`. -/
theorem linkReader_renameInv :
    ExprReader.RenameInv (E := leafSig) (d := nfDialect) linkReader := by
  intro Γ Δ t f V W e e' h he
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  obtain ⟨op, rfl, eargs⟩ := e
  simp only [linkReader, PRen.lookupArgs_vars? h eargs hargs]

/-! ## Congruences of `RuttS` at the failed leaf `none` -/

/-- The relation of optional leaves: a source value is matched by a related target value. -/
def OutRel {α β : Type} (R : α → β → Prop) (o₁ : Option α) (o₂ : Option β) : Prop :=
  ∀ a, o₁ = some a → ∃ b, o₂ = some b ∧ R a b

section Congr

variable {E₁ E₂ : EventSig} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
  {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}

/-- `RuttS` is monotone in the relation of the leaves. -/
theorem RuttS.mono {R₁ R₂ : Type} {RR RR' : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (hR : ∀ a b, RR a b → RR' a b) {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : RuttS h₁ RE RA RR Fail t₁ t₂) : RuttS h₁ RE RA RR' Fail t₁ t₂ := by
  induction h with
  | ret h => exact .ret (hR _ _ h)
  | fail h => exact .fail h
  | vis he _ ih => exact .vis he ih
  | skip _ ih => exact .skip ih

/-- **Sequencing at the failed leaf `none`**: related prefixes and continuations related at
    related values give related `obind`. -/
theorem ruttS_obind {α₁ α₂ β₁ β₂ : Type} {R : α₁ → α₂ → Prop} {R' : β₁ → β₂ → Prop}
    {t₁ : CallTree E₁ (Option α₁)} {t₂ : CallTree E₂ (Option α₂)}
    {k₁ : α₁ → CallTree E₁ (Option β₁)} {k₂ : α₂ → CallTree E₂ (Option β₂)}
    (h : RuttS h₁ RE RA (OutRel R) (fun o => o = none) t₁ t₂)
    (hk : ∀ a b, R a b → RuttS h₁ RE RA (OutRel R') (fun o => o = none) (k₁ a) (k₂ b)) :
    RuttS h₁ RE RA (OutRel R') (fun o => o = none) (obind t₁ k₁) (obind t₂ k₂) := by
  refine RuttS.bind h ?_ ?_
  · intro s₁ s₂ hs
    cases s₁ with
    | none => exact .fail rfl
    | some a =>
      obtain ⟨b, rfl, hab⟩ := hs a rfl
      exact hk a b hab
  · rintro s₁ rfl t
    exact .fail rfl

/-- Related steps give related folds. -/
theorem ruttS_ofoldl {α β₁ β₂ : Type} {R : β₁ → β₂ → Prop}
    {f₁ : β₁ → α → CallTree E₁ (Option β₁)} {f₂ : β₂ → α → CallTree E₂ (Option β₂)}
    (hf : ∀ b b' i, R b b' →
      RuttS h₁ RE RA (OutRel R) (fun o => o = none) (f₁ b i) (f₂ b' i)) :
    ∀ (l : List α) (b : β₁) (b' : β₂), R b b' →
      RuttS h₁ RE RA (OutRel R) (fun o => o = none) (ofoldl f₁ l b) (ofoldl f₂ l b') := by
  intro l
  induction l with
  | nil =>
    intro b b' hb
    exact .ret fun a ha => by cases ha; exact ⟨b', rfl, hb⟩
  | cons i l ih =>
    intro b b' hb
    exact ruttS_obind (hf b b' i hb) fun a a' ha => ih a a' ha

/-- Related steps that agree on the exit bit give related exit-flag iterations, at every
    target fuel at least the source fuel. -/
theorem ruttS_owhileIter {d₁ d₂ : Dialect.{0, 0}} [TyDenote d₁.Ty] [HasBoolBit d₁]
    [TyDenote d₂.Ty] [HasBoolBit d₂] {cs₁ : List d₁.Ty} {cs₂ : List d₂.Ty}
    {R : Valuation cs₁ → Valuation cs₂ → Prop}
    {s₁ : Valuation cs₁ → CallTree E₁ (Option (Valuation (HasBitType.bit (d := d₁) :: cs₁)))}
    {s₂ : Valuation cs₂ → CallTree E₂ (Option (Valuation (HasBitType.bit (d := d₂) :: cs₂)))}
    (hs : ∀ a a', R a a' → RuttS h₁ RE RA
      (OutRel fun r r' => R r.tail r'.tail ∧
        HasBoolBit.toBool (d := d₁) r.head = HasBoolBit.toBool (d := d₂) r'.head)
      (fun o => o = none) (s₁ a) (s₂ a')) :
    ∀ (n m : Nat), n ≤ m → ∀ a a', R a a' →
      RuttS h₁ RE RA (OutRel R) (fun o => o = none) (owhileIter s₁ n a) (owhileIter s₂ m a') := by
  intro n
  induction n with
  | zero => intro m _ a a' _; exact .fail rfl
  | succ n ih =>
    intro m hm a a' ha
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ruttS_obind (hs a a' ha) fun r r' hr => ?_
    rw [← hr.2]
    split
    · exact ih m (by omega) _ _ hr.1
    · exact .ret fun x hx => by cases hx; exact ⟨_, rfl, hr.1⟩

end Congr

/-! ## The bindings of the translation -/

/-- A let-binding of `catCryptDialect` has the call tree of its continuation at the extended
    valuation. -/
theorem nfProgTree_var (fuel : Nat) {Δ : Ctxt catCryptDialect} {c : CryptoTy}
    {us : List CryptoTy} (e : Expr catCryptDialect Δ c) (k : NFProg catCryptDialect (c :: Δ) us)
    (W : Valuation Δ) :
    nfProgTree fuel (.var e k) W = nfProgTree fuel k (W.extend (e.denote W)) := by
  simp only [nfProgTree, treeAt, pureReader, Expr.denoteM_option_eq_some]
  rfl

/-- **The bindings of `pinAll` preserve a property closed under let-bindings**, from every
    valuation the readings relate to `V` at which the readings `rs` relate `xs`. -/
theorem pinAll_elimQ {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    (Q : ∀ {Δ : Ctxt catCryptDialect}, NFProg catCryptDialect Δ us → Valuation Δ → Prop)
    (hQ : ∀ {Δ : Ctxt catCryptDialect} {c : CryptoTy} (e : Expr catCryptDialect Δ c)
      (k : NFProg catCryptDialect (c :: Δ) us) (W : Valuation Δ),
      Q k (W.extend (e.denote W)) → Q (.var e k) W)
    (k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us))
    (V : Valuation Γ) (xs : Valuation (d := nfDialect) ts)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy))
      (p' : NFProg catCryptDialect Δ' us) (W' : Valuation Δ'),
      k σ' ws = some p' → σ'.Agree V W' → VRelL ts xs (Expr.lookupArgs ws W') → Q p' W')
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (p' : NFProg catCryptDialect Δ us) (W : Valuation Δ)
    (h : pinAll k σ rs = some p') (hag : σ.Agree V W) (hx : RdRelL W ts xs rs) : Q p' W := by
  refine pinAll_elim
    (M := fun {Δ} σ rs p' => ∀ W : Valuation Δ, σ.Agree V W → RdRelL W ts xs rs → Q p' W)
    ?_ ?_ σ rs p' h W hag hx
  · intro Δ σ rs ws p hws hk W hag hx
    exact HK σ ws p W hk hag (pinVars_rel xs rs ws hws hx)
  · intro Δ σ rs c p hc ih W hag hx
    exact hQ _ p W (ih (W.extend (BitVec.ofNat 64 c))
      (TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 c))
      (bindLit_rel (firstLit_lt xs rs hc hx) xs rs hx))

/-- **The bindings of a translated operation preserve a property closed under let-bindings**,
    when the continuation has it from every reading that relates `V.extend y`. -/
theorem emitRes_elim {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (Q : ∀ {Δ : Ctxt catCryptDialect}, NFProg catCryptDialect Δ (ts.map catTy) →
      Valuation Δ → Prop)
    (hQ : ∀ {Δ : Ctxt catCryptDialect} {c : CryptoTy} (e : Expr catCryptDialect Δ c)
      (k : NFProg catCryptDialect (c :: Δ) (ts.map catTy)) (W : Valuation Δ),
      Q k (W.extend (e.denote W)) → Q (.var e k) W)
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    (V : Valuation Γ) (y : s.denote)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (p' : NFProg catCryptDialect Δ' (ts.map catTy)) (W' : Valuation Δ'),
      cont σ' = some p' → σ'.Agree (V.extend y) W' → Q p' W') :
    ∀ {Δ : Ctxt catCryptDialect} (res : OpRes Δ s) (σ : TRd Γ Δ) (W : Valuation Δ)
      (p' : NFProg catCryptDialect Δ (ts.map catTy)),
      emitRes cont rfl res σ = some p' → σ.Agree V W → OpResRel W s y res → Q p' W := by
  intro Δ res
  induction res with
  | rd r =>
    intro σ W p' h hag hrel
    exact HK _ p' W h (TRd.agree_cons hag hrel)
  | expr e' =>
    intro σ W p' h hag hrel
    obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
    exact hQ _ k' W (HK σ.lift k' _ hk' (TRd.agree_lift hag hrel))
  | expr1 c e' =>
    intro σ W p' h hag hrel
    obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
    have hW1 := TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 c)
    exact hQ _ _ W (hQ _ k' _ (HK (TRd.lift (TRd.wk σ)) k' _ hk' (TRd.agree_lift hW1 hrel)))
  | bind c e rest ih =>
    intro σ W p' h hag hrel
    obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
    exact hQ e k' W (ih cont y HK σ.wk (W.extend (e.denote W)) k' hk'
      (TRd.agree_wk hag _) hrel)

/-! ## The stage lemma of the translation with declarations -/

/-- **The event relation of the translation**: a leaf call and a call of `catCryptDialect` of
    the same name, at the mapped signature, on argument values related by `VRelL`. -/
def ExtRE (e₁ : leafSig.Event) (e₂ : (nfCallSig catCryptDialect).Event) : Prop :=
  e₂.name = e₁.name ∧ ∃ h : e₂.argTys = e₁.argTys.map catTy, e₂.resTys = [catTy e₁.ret] ∧
    VRelL e₁.argTys e₁.args (h ▸ e₂.args : Valuation (d := catCryptDialect) _)

/-- **The answer relation of the translation**: a value of the leaf is answered by the target
    with one value related to it by `VRel`. -/
def ExtRA (e₁ : leafSig.Event) (e₂ : (nfCallSig catCryptDialect).Event)
    (a₁ : leafSig.Resp e₁) (a₂ : (nfCallSig catCryptDialect).Resp e₂) : Prop :=
  ∀ y, a₁ = some y → ∃ y' : (catTy e₁.ret).denote,
    a₂ ≍ (some (HVector.cons y' .nil) : Option (Valuation (d := catCryptDialect)
      [catTy e₁.ret])) ∧ VRel e₁.ret y y'

/-- **The stage statement of the translation with declarations at the tree level**, for the
    program `p`: when `nfToCatExt D p σ = some p'` and `σ` relates `V` to `W`, the tree of `p`
    at `linkReader`, the source fuel `tf` and the source handler of `T` is related by `RuttS`
    to the tree of `p'` with call events at every fuel at least `tf`, at the relations
    `ExtRE`, `ExtRA`, the leaves related by `VRelL`, and the failed source leaf `none`. -/
def NFExtTree (T : NfLeafTable) (D : List ExtDecl) (tE : TreeCallEnv leafSig nfDialect)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (p' : NFProg catCryptDialect Δ (ts.map catTy)),
    nfToCatExt D p σ = some p' → ∀ (V : Valuation Γ) (W : Valuation Δ), σ.Agree V W →
    ∀ tf fuel, tf ≤ fuel →
      RuttS (leafHandler T) ExtRE ExtRA (OutRel (VRelL ts)) (fun o => o = none)
        (treeAt linkReader tE tf p V) (nfProgTree fuel p' W)

/-- The tree of a declared leaf call: the tree of an operation that `extArgs` reads as a call
    of `f` on the readings `rs` is related to `t₂` when the event of the call is, at every
    argument vector the readings relate. -/
theorem ruttS_opTree_extArgs {D : List ExtDecl} {Γ : Ctxt nfDialect}
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) {V : Valuation Γ} {W : Valuation Δ}
    (hag : σ.Agree V W) {R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    {h₁ : ∀ e : leafSig.Event, leafSig.Resp e} {E₂ : EventSig}
    {RE : leafSig.Event → E₂.Event → Prop}
    {RA : (e₁ : leafSig.Event) → (e₂ : E₂.Event) → leafSig.Resp e₁ → E₂.Resp e₂ → Prop}
    (op : NfOp) :
    ∀ (args : HVector (fun t => Var Γ t) op.sig) (f : String) (as : List NfTy)
      (rs : HVector (fun t => Rd Δ t) as), extArgs D σ op args = some (f, ⟨as, rs⟩) →
      ∀ (K : Option op.ret.denote → CallTree leafSig R₁) (t₂ : CallTree E₂ R₂),
      (∀ xs : HVector NfTy.denote as, RdRelL W as xs rs →
        RuttS h₁ RE RA RR Fail
          (.vis (⟨f, as, op.ret, xs⟩ : LeafCall) fun y => (CallTree.ret y).bind K) t₂) →
      RuttS h₁ RE RA RR Fail ((opTree op (Expr.lookupArgs args V)).bind K) t₂ := by
  induction op with
  | named n op ih => exact ih
  | call g bs r =>
    intro args f as rs h K t₂ H
    unfold extArgs at h
    split at h
    · cases h
      exact H _ (TRd.rdRelL_rds hag args)
    · cases h
  | _ =>
    intro args f as rs h
    cases h

/-- The relation of a source tree `t₁` to the tree with call events of a program of
    `catCryptDialect` at a valuation, the property the bindings of the translation carry. -/
def TQ (T : NfLeafTable) {ts : List NfTy}
    (t₁ : CallTree leafSig (Option (Valuation (d := nfDialect) ts))) (fuel : Nat)
    {Δ : Ctxt catCryptDialect} (p' : NFProg catCryptDialect Δ (ts.map catTy))
    (W : Valuation Δ) : Prop :=
  RuttS (leafHandler T) ExtRE ExtRA (OutRel (VRelL ts)) (fun o => o = none) t₁
    (nfProgTree fuel p' W)

/-- `TQ` is closed under let-bindings of the target. -/
theorem TQ_var (T : NfLeafTable) {ts : List NfTy}
    (t₁ : CallTree leafSig (Option (Valuation (d := nfDialect) ts))) (fuel : Nat)
    {Δ : Ctxt catCryptDialect} {c : CryptoTy} (e : Expr catCryptDialect Δ c)
    (k : NFProg catCryptDialect (c :: Δ) (ts.map catTy)) (W : Valuation Δ)
    (h : TQ T t₁ fuel k (W.extend (e.denote W))) : TQ T t₁ fuel (.var e k) W := by
  unfold TQ at h ⊢
  rwa [nfProgTree_var]

/-- **The stage lemma of `extCallStep` at the tree level.** Under `SubTable bi`, the
    translation with declarations satisfies `NFExtTree` at the leaf table of `bi`: a declared
    leaf call is an event related by `ExtRE` and `ExtRA` to the call node of the target, a
    leaf call that `catOp` translates is a skipped source event, and every other operation is
    no event. -/
theorem nfToCatExt_ruttS {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (D : List ExtDecl)
    (tE : TreeCallEnv leafSig nfDialect) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : NFExtTree (ImpToNF.tableOf bi) D tE p := by
  induction p with
  | ret vs =>
    intro Δ σ p' h V W hag tf fuel _
    refine pinAll_elimQ (Q := fun p' W => TQ (ImpToNF.tableOf bi)
        (treeAt linkReader tE tf (.ret vs) V) fuel p' W)
      (fun e k W hk => TQ_var _ _ _ e k W hk) _ V (Expr.lookupArgs vs V) ?_ σ _ p' W h hag
      (TRd.rdRelL_rds hag vs)
    intro Δ' σ' ws p'' W' hk _ hrel
    cases hk
    exact .ret fun a ha => by cases ha; exact ⟨_, rfl, hrel⟩
  | var e k ih =>
    intro Δ σ p' h V W hag tf fuel hle
    obtain ⟨op, rfl, args⟩ := e
    change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some p' at h
    unfold emitOp at h
    change RuttS _ _ _ _ _ (obind (opTree op (Expr.lookupArgs args V))
      fun x => treeAt linkReader tE tf k (V.extend x)) _
    unfold obind
    split at h
    · rename_i res hres
      refine RuttS.skip_bind _ ?_
      rw [interp_opTree]
      cases hy : nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V) with
      | none => exact .fail rfl
      | some y =>
        exact emitRes_elim (fun p' W => TQ (ImpToNF.tableOf bi)
            (treeAt linkReader tE tf k (V.extend y)) fuel p' W)
          (fun e k W hk => TQ_var _ _ _ e k W hk) _ V y
          (fun σ' p'' W' hk hag' => ih σ' p'' hk _ W' hag' tf fuel hle) res σ W p' h hag
          (catOp_sound hbi σ hag op args res y hres hy)
    · obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f, as, rs⟩ := c
      refine ruttS_opTree_extArgs σ hag op args f as rs hc _ _ fun xs hxs => ?_
      refine pinAll_elimQ (Q := fun p' W => TQ (ImpToNF.tableOf bi) _ fuel p' W)
        (fun e k W hk => TQ_var _ _ _ e k W hk) _ V xs ?_ σ rs p' W h hag hxs
      intro Δ' σ' ws p'' W' hk hag' hws
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
      refine .vis ⟨rfl, rfl, rfl, hws⟩ fun a₁ a₂ ha => ?_
      cases a₁ with
      | none => exact .fail rfl
      | some y =>
        obtain ⟨y', hy', hrel⟩ := ha y rfl
        cases eq_of_heq hy'
        exact ih σ'.lift k' hk' (V.extend y) (W'.extend y') (TRd.agree_lift hag' hrel) tf
          fuel hle
  | @forLoop Γ₀ cs ts₀ count inits body k ihb ihk =>
    intro Δ σ p' h V W hag tf fuel hle
    refine pinAll_elimQ (ts := .word 64 :: cs) (Q := fun p' W => TQ (ImpToNF.tableOf bi)
        (treeAt linkReader tE tf (.forLoop count inits body k) V) fuel p' W)
      (fun e k W hk => TQ_var _ _ _ e k W hk) _ V
      (Expr.lookupArgs (HVector.cons count inits) V) ?_ σ _ p' W h hag
      (TRd.rdRelL_rds hag (HVector.cons count inits))
    intro Δ' σ' ws p'' W' hk hag' hrel
    rcases ws with _ | ⟨c, is⟩
    obtain ⟨body', hb', hk⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
    have hc2 : HasWord64.toNat (d := catCryptDialect) ((HVector.cons c is).head.lookup W') =
        HasWord64.toNat (d := nfDialect) (count.lookup V) := by
      rw [hrel.1]
      rfl
    simp only [TQ, nfProgTree, treeAt]
    rw [hc2]
    refine ruttS_obind (ruttS_ofoldl (fun acc acc' i hacc => ?_) _ _ _ hrel.2)
      fun a b hab => ihk (TRd.liftApp cs σ') k' hk' _ _ (TRd.agree_liftApp hag' cs a b hab)
        tf fuel hle
    exact ihb (TRd.liftApp cs (TRd.lift σ')) body' hb' _ _
      (TRd.agree_liftApp (TRd.agree_lift (s := NfTy.word 64) hag'
        (x := BitVec.ofNat 64 i) (y := BitVec.ofNat 64 i) rfl) cs acc acc' hacc) tf fuel hle
  | @ifThenElse Γ₀ rs ts₀ cond thn els k iht ihe ihk =>
    intro Δ σ p' h V W hag tf fuel hle
    have hcond := hag _ cond
    simp only [nfToCatExt] at h
    split at h
    · rename_i c hc
      rw [hc] at hcond
      obtain ⟨thn', ht', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨els', he', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have hcb : HasBoolBit.toBool (d := catCryptDialect) (c.lookup W) =
          HasBoolBit.toBool (d := nfDialect) (cond.lookup V) := hcond.symm
      simp only [nfProgTree, treeAt]
      rw [hcb]
      refine ruttS_obind ?_ fun r r' hr =>
        ihk (TRd.liftApp rs σ) k' hk' _ _ (TRd.agree_liftApp hag rs r r' hr) tf fuel hle
      cases HasBoolBit.toBool (d := nfDialect) (cond.lookup V)
      · exact ihe σ els' he' V W hag tf fuel hle
      · exact iht σ thn' ht' V W hag tf fuel hle
    · cases h
  | @whileLoop Γ₀ cs ts₀ inits body k ihb ihk =>
    intro Δ σ p' h V W hag tf fuel hle
    refine pinAll_elimQ (ts := cs) (Q := fun p' W => TQ (ImpToNF.tableOf bi)
        (treeAt linkReader tE tf (.whileLoop inits body k) V) fuel p' W)
      (fun e k W hk => TQ_var _ _ _ e k W hk) _ V (Expr.lookupArgs inits V) ?_ σ _ p' W h hag
      (TRd.rdRelL_rds hag inits)
    intro Δ' σ' ws p'' W' hk hag' hrel
    obtain ⟨body', hb', hk⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
    simp only [TQ, nfProgTree, treeAt]
    refine ruttS_obind (ruttS_owhileIter (R := VRelL cs) (fun a a' ha => ?_) tf fuel hle _ _
      hrel) fun a b hab => ihk (TRd.liftApp cs σ') k' hk' _ _
        (TRd.agree_liftApp hag' cs a b hab) tf fuel hle
    refine RuttS.mono ?_ (ihb (TRd.liftApp cs σ') body' hb' _ _
      (TRd.agree_liftApp hag' cs a a' ha) tf fuel hle)
    intro o o' ho r hr
    obtain ⟨r', hr', hR⟩ := ho r hr
    refine ⟨r', hr', ?_⟩
    rcases r with _ | ⟨b, r⟩
    rcases r' with _ | ⟨b', r'⟩
    exact ⟨hR.2, hR.1⟩
  | call f args k _ =>
    intro Δ σ p' h
    cases h

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
