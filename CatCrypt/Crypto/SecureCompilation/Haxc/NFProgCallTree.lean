/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgDCE

/-!
# The call tree of a structured program and dead-binding elimination

The stages of the chain of `compileA` are stated on the denotation `NFProg.denoteAt` of a
structured program at a call environment, which answers a call by a partial function. This
module reads a structured program as a finite call tree over an event signature (`treeAt`): a
`call` node runs the tree of a *tree call environment*, and a let-binding runs the tree an
*expression reader* gives for its expression, so that an operation of the dialect may perform
events as well. Interpreting the tree under a handler is `denoteAt` at the call environment
the handler induces, when the reader interprets to the denotation of the expressions
(`interp_treeAt`). At the event call environment, in which each call is one event carrying the
symbol, the signature and the argument values, the handler of a call environment `Ec`
interprets the tree to `denoteAt Ec` (`interp_nfProgTree`).

Dead-binding elimination `NFProg.dce` removes a let-binding whose value is unread, and with it
the events its expression performs. The tree of `dce p` is related to the tree of `p` by
`RuttS` at equal events and answers, equal leaves and the failed source leaf `none`
(`ruttS_treeAt_dce`): a removed binding is a sequence of skipped source events.

## Main definitions

* `obind`, `ofoldl`, `owhileIter`: sequencing, folds and exit-flag iteration of trees of
  optional results.
* `TreeCallEnv`, `ExprReader`, `treeAt`: a call environment answering by trees, a reader of
  expressions as trees, and the call tree of a structured program.
* `NFCall`, `nfCallSig`, `eventEnv`, `callHandler`, `nfProgTree`: the event of a call, the
  call tree in which every call is an event, and the handler of a call environment.
* `RefinesT`: the relation `RuttS` at equal events, answers and leaves, with `none` as the
  failed source leaf.

## Main results

* `interp_treeAt`: interpreting the tree is `denoteAt` at the induced call environment.
* `interp_nfProgTree`: under the handler of `Ec`, the call tree with call events interprets
  to `denoteAt Ec`.
* `RuttS.bind`, `RuttS.refl`, `RuttS.skip_bind`: sequencing, reflexivity and the skip of a
  whole source prefix for `RuttS`.
* `RefinesT.trans`, `RefinesT.obind`, `RefinesT.ofoldl`, `RefinesT.owhileIter`: refinement up
  to skipped events composes and is a congruence of the tree combinators.
* `treeAt_rename?`: a renamed program has the tree of the source at related valuations.
* `ruttS_treeAt_dce`: the stage lemma of dead-binding elimination at the tree level.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## Trees of optional results -/

section OTree

variable {E : EventSig}

/-- Sequencing of trees of optional results: a leaf `none` ends with `none`, a leaf `some a`
    continues with `k a`. -/
def obind {α β : Type} (t : CallTree E (Option α)) (k : α → CallTree E (Option β)) :
    CallTree E (Option β) :=
  t.bind fun o => match o with
    | none => .ret none
    | some a => k a

/-- Interpretation of `obind` is the bind of `Option`. -/
theorem interp_obind {α β : Type} (h : ∀ e : E.Event, E.Resp e) (t : CallTree E (Option α))
    (k : α → CallTree E (Option β)) :
    interp h (obind t k) = (interp h t).bind fun a => interp h (k a) := by
  unfold obind
  rw [interp_bind]
  cases interp h t <;> rfl

/-- The left fold of trees of optional results. -/
def ofoldl {α β : Type} (f : β → α → CallTree E (Option β)) : List α → β → CallTree E (Option β)
  | [], b => .ret (some b)
  | a :: l, b => obind (f b a) fun b' => ofoldl f l b'

/-- Interpretation of `ofoldl` is the fold `List.foldlM` of `Option`. -/
theorem interp_ofoldl {α β : Type} (h : ∀ e : E.Event, E.Resp e)
    (f : β → α → CallTree E (Option β)) (l : List α) (b : β) :
    interp h (ofoldl f l b) = l.foldlM (fun b a => interp h (f b a)) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [ofoldl, interp_obind, List.foldlM_cons, ih]
    rfl

end OTree

/-! ## The call tree of a structured program -/

section Tree

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- The fuel-bounded exit-flag iteration of a tree body `step`, the tree form of
    `NFProg.whileIter`. -/
def owhileIter {cs : List d.Ty}
    (step : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))) :
    Nat → Valuation cs → CallTree E (Option (Valuation cs))
  | 0, _ => .ret none
  | n + 1, acc => obind (step acc) fun r =>
      if HasBoolBit.toBool (d := d) r.head then owhileIter step n r.tail else .ret (some r.tail)

omit [DialectSignature d] [HasWord64 d] in
/-- Interpretation of `owhileIter` is `NFProg.whileIter` at the interpreted body. -/
theorem interp_owhileIter (h : ∀ e : E.Event, E.Resp e) {cs : List d.Ty}
    (step : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))) :
    ∀ (n : Nat) (acc : Valuation cs),
      interp h (owhileIter step n acc) = NFProg.whileIter (fun a => interp h (step a)) n acc := by
  intro n
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
    intro acc
    simp only [owhileIter, NFProg.whileIter, interp_obind]
    congr 1; funext r; split <;> simp [ih]

/-- A call environment answering a call of the symbol `f` at the signature `as → rs` by a tree
    of optional result valuations. -/
structure TreeCallEnv (E : EventSig) (d : Dialect.{0, 0}) [TyDenote d.Ty] where
  /-- The tree of the callee of the symbol `f` at the signature `as → rs`. -/
  call : (f : String) → (as rs : List d.Ty) → Valuation as → CallTree E (Option (Valuation rs))

/-- The call environment a handler induces from a tree call environment. -/
def TreeCallEnv.interpEnv (h : ∀ e : E.Event, E.Resp e) (tE : TreeCallEnv E d) : CallEnv d :=
  ⟨fun f as rs a => interp h (tE.call f as rs a)⟩

/-- A reader of expressions as trees of optional values. -/
abbrev ExprReader (E : EventSig) (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] :
    Type :=
  ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Valuation Γ → CallTree E (Option ⟦t⟧)

/-- **The call tree of a structured program** at the expression reader `ex`, the tree call
    environment `tE` and the fuel `fuel`: clause by clause the denotation `NFProg.denote`, with
    a let-binding running the tree of `ex` and a `call` the tree of `tE`. -/
def treeAt (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Valuation Γ →
      CallTree E (Option (Valuation ts))
  | _, _, .ret vs, V => .ret (some (Expr.lookupArgs vs V))
  | _, _, .var e k, V => obind (ex e V) fun x => treeAt ex tE fuel k (V.extend x)
  | _, _, .forLoop count inits body k, V =>
      obind (ofoldl (fun acc i => treeAt ex tE fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V))) (Expr.lookupArgs inits V))
        fun acc => treeAt ex tE fuel k (hvAppend acc V)
  | _, _, .ifThenElse cond thn els k, V =>
      obind (if HasBoolBit.toBool (d := d) (cond.lookup V) then treeAt ex tE fuel thn V
          else treeAt ex tE fuel els V)
        fun r => treeAt ex tE fuel k (hvAppend r V)
  | _, _, .whileLoop inits body k, V =>
      obind (owhileIter (fun acc => treeAt ex tE fuel body (hvAppend acc V)) fuel
          (Expr.lookupArgs inits V))
        fun acc => treeAt ex tE fuel k (hvAppend acc V)
  | _, _, .call (as := as) (rs := rs) f args k, V =>
      obind (tE.call f as rs (Expr.lookupArgs args V)) fun r =>
        treeAt ex tE fuel k (hvAppend r V)

variable [DialectDenoteM d Option]

/-- **Adequacy of the call tree**: when the reader `ex` interprets under `h` to the denotation
    of each expression, the tree of `p` interprets under `h` to `denoteAt` at the call
    environment `h` induces from `tE`. -/
theorem interp_treeAt (h : ∀ e : E.Event, E.Resp e) (ex : ExprReader E d)
    (hex : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      interp h (ex e V) = e.denoteM V)
    (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ V : Valuation Γ, interp h (treeAt ex tE fuel p V) = p.denoteAt (tE.interpEnv h) fuel V := by
  induction p with
  | ret vs => intro V; rfl
  | var e k ih =>
    intro V
    simp only [treeAt, interp_obind, hex, ih]
    rfl
  | forLoop count inits body k ihb ihk =>
    intro V
    simp only [treeAt, interp_obind, interp_ofoldl, ihb, ihk]
    rfl
  | ifThenElse cond thn els k iht ihe ihk =>
    intro V
    simp only [treeAt, interp_obind, ihk]
    rw [apply_ite (interp h), iht, ihe]
    rfl
  | whileLoop inits body k ihb ihk =>
    intro V
    simp only [treeAt, interp_obind, interp_owhileIter, ihb, ihk]
    rfl
  | call f args k ih =>
    intro V
    simp only [treeAt, interp_obind, ih]
    rfl

/-- The reader of an expression as the leaf of its denotation, without event. -/
def pureReader : ExprReader E d := fun e V => .ret (e.denoteM (M := Option) V)

end Tree

/-! ## The call tree with call events -/

section Events

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A call of a structured program: the symbol, the signature and the argument values. -/
structure NFCall (d : Dialect.{0, 0}) [TyDenote d.Ty] where
  /-- The symbol of the callee. -/
  name : String
  /-- The argument types. -/
  argTys : List d.Ty
  /-- The result types. -/
  resTys : List d.Ty
  /-- The argument values. -/
  args : Valuation argTys

/-- The event signature of the calls of a dialect: a call is answered by a valuation of its
    result types, or by `none` when the callee refuses. -/
def nfCallSig (d : Dialect.{0, 0}) [TyDenote d.Ty] : EventSig where
  Event := NFCall d
  Resp := fun c => Option (Valuation c.resTys)

/-- The tree call environment in which each call is one event. -/
def eventEnv : TreeCallEnv (nfCallSig d) d :=
  ⟨fun f as rs a => .vis (⟨f, as, rs, a⟩ : NFCall d) fun r => .ret r⟩

/-- The handler of the call environment `Ec`: a call is answered by the callee of `Ec`. -/
def callHandler (Ec : CallEnv d) : ∀ e : (nfCallSig d).Event, (nfCallSig d).Resp e :=
  fun c => Ec.call c.name c.argTys c.resTys c.args

/-- **The call tree of a structured program with call events**, at the fuel `fuel`. -/
def nfProgTree (fuel : Nat) [DialectDenoteM d Option] {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V : Valuation Γ) : CallTree (nfCallSig d) (Option (Valuation ts)) :=
  treeAt pureReader eventEnv fuel p V

/-- **Adequacy of the call tree with call events**: under the handler of the call environment
    `Ec`, the call tree of `p` interprets to `denoteAt Ec`. -/
theorem interp_nfProgTree [DialectDenoteM d Option] (Ec : CallEnv d) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) :
    interp (callHandler Ec) (nfProgTree fuel p V) = p.denoteAt Ec fuel V := by
  rw [nfProgTree, interp_treeAt _ _ (fun _ _ => rfl)]
  rfl

end Events

/-! ## Lemmas on `RuttS` -/

section RuttSLemmas

variable {E₁ E₂ : EventSig} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
  {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}

/-- **Sequencing of related trees**: related prefixes and continuations related at related
    leaves, each failed leaf continuing to a tree related to every target tree. -/
theorem RuttS.bind {S₁ S₂ R₁ R₂ : Type} {RR' : S₁ → S₂ → Prop} {Fail' : S₁ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ S₁} {t₂ : CallTree E₂ S₂}
    {k₁ : S₁ → CallTree E₁ R₁} {k₂ : S₂ → CallTree E₂ R₂}
    (h : RuttS h₁ RE RA RR' Fail' t₁ t₂)
    (hk : ∀ s₁ s₂, RR' s₁ s₂ → RuttS h₁ RE RA RR Fail (k₁ s₁) (k₂ s₂))
    (hf : ∀ s₁, Fail' s₁ → ∀ t, RuttS h₁ RE RA RR Fail (k₁ s₁) t) :
    RuttS h₁ RE RA RR Fail (t₁.bind k₁) (t₂.bind k₂) := by
  induction h with
  | ret h => exact hk _ _ h
  | fail h => exact hf _ h _
  | vis he _ ih => exact .vis he ih
  | skip _ ih => exact .skip ih

/-- **Skip of a source prefix**: a source tree `t.bind k₁` is related to `t₂` when the
    continuation at the interpretation of `t` under the source handler is. -/
theorem RuttS.skip_bind {S R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (t : CallTree E₁ S) {k₁ : S → CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : RuttS h₁ RE RA RR Fail (k₁ (interp h₁ t)) t₂) :
    RuttS h₁ RE RA RR Fail (t.bind k₁) t₂ := by
  induction t with
  | ret s => exact h
  | vis e c ih => exact .skip (ih (h₁ e) h)

end RuttSLemmas

section Refines

variable {E : EventSig} {h₁ : ∀ e : E.Event, E.Resp e}

/-- **Refinement of trees up to skipped events**: `RuttS` at the source handler `h₁`, equal
    events and answers, equal leaves, and the source leaf `none` as the failed run. -/
def RefinesT (h₁ : ∀ e : E.Event, E.Resp e) {α : Type} (t₁ t₂ : CallTree E (Option α)) :
    Prop :=
  RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) (fun r₁ r₂ => r₁ = r₂)
    (fun r₁ => r₁ = none) t₁ t₂

/-- **Reflexivity**: a tree is related to itself at equal events and answers, at every
    reflexive relation of the leaves. -/
theorem RuttS.refl {R : Type} {RR : R → R → Prop} {Fail : R → Prop} (hR : ∀ r, RR r r)
    (t : CallTree E R) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail t t := by
  induction t with
  | ret r => exact .ret (hR r)
  | vis e c ih =>
    refine .vis rfl fun a₁ a₂ ha => ?_
    cases ha
    exact ih a₁

/-- A tree refines itself. -/
theorem RefinesT.refl {α : Type} (t : CallTree E (Option α)) : RefinesT h₁ t t :=
  RuttS.refl (fun _ => rfl) t

/-- **Sequencing of refinements**: refined prefixes and refined continuations give a refined
    `obind`. -/
theorem RefinesT.obind {α β : Type} {t₁ t₂ : CallTree E (Option α)}
    {k₁ k₂ : α → CallTree E (Option β)} (h : RefinesT h₁ t₁ t₂)
    (hk : ∀ a, RefinesT h₁ (k₁ a) (k₂ a)) :
    RefinesT h₁ (NFProgCallTree.obind t₁ k₁) (NFProgCallTree.obind t₂ k₂) := by
  refine RuttS.bind h ?_ ?_
  · rintro s₁ s₂ rfl
    cases s₁ with
    | none => exact .ret rfl
    | some a => exact hk a
  · rintro s₁ rfl t
    exact .fail rfl

/-- **Transitivity**: refinement up to skipped events composes, so the stage lemmas of a chain
    compose to a refinement of the whole chain. -/
theorem RefinesT.trans {α : Type} {t₁ t₂ t₃ : CallTree E (Option α)}
    (h12 : RefinesT h₁ t₁ t₂) (h23 : RefinesT h₁ t₂ t₃) : RefinesT h₁ t₁ t₃ := by
  induction h12 generalizing t₃ with
  | ret h => subst h; exact h23
  | fail h => exact .fail h
  | vis he _ ih =>
    subst he
    cases h23 with
    | vis he' hk' => exact .vis he' fun a₁ a₂ ha => ih a₁ a₁ HEq.rfl (hk' a₁ a₂ ha)
    | skip hk' => exact .skip (ih _ _ HEq.rfl hk')
  | skip _ ih => exact .skip (ih h23)

/-- Refined steps give a refined fold. -/
theorem RefinesT.ofoldl {α β : Type} {f₁ f₂ : β → α → CallTree E (Option β)}
    (hf : ∀ b a, RefinesT h₁ (f₁ b a) (f₂ b a)) (l : List α) (b : β) :
    RefinesT h₁ (ofoldl f₁ l b) (ofoldl f₂ l b) := by
  induction l generalizing b with
  | nil => exact RefinesT.refl _
  | cons a l ih => exact RefinesT.obind (hf b a) fun b' => ih b'

end Refines

/-! ## Renaming and dead-binding elimination at the tree level -/

section Dce

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A reader of expressions is invariant under renaming: a renamed expression at related
    valuations has the tree of the source expression. -/
def ExprReader.RenameInv (ex : ExprReader E d) : Prop :=
  ∀ {Γ Δ : Ctxt d} {t : d.Ty} {f : PRen Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (e : Expr d Γ t) {e' : Expr d Δ t}, PRen.Agrees f V W → Expr.rename? f e = some e' →
    ex e' W = ex e V

omit [HasWord64 d] [HasBoolBit d] in
/-- The pure reader is invariant under renaming. -/
theorem pureReader_renameInv [DialectDenoteM d Option] :
    ExprReader.RenameInv (E := E) (d := d) pureReader := by
  intro Γ Δ t f V W e e' h he
  simp only [pureReader, Expr.denoteM_rename? h e he]

/-- **A renamed program has the tree of the source**: when `rename? f p = some p'` and `f`
    relates `V` to `W`, the tree of `p'` at `W` is the tree of `p` at `V`. -/
theorem treeAt_rename? {ex : ExprReader E d} (hex : ex.RenameInv) (tE : TreeCallEnv E d)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {p' : NFProg d Δ ts} {V : Valuation Γ}
      {W : Valuation Δ}, NFProg.rename? f p = some p' → PRen.Agrees f V W →
      treeAt ex tE fuel p' W = treeAt ex tE fuel p V := by
  induction p with
  | ret vs =>
    intro Δ f p' V W hp h
    simp only [NFProg.rename?, Option.map_eq_some_iff] at hp
    obtain ⟨ws, hws, rfl⟩ := hp
    simp only [treeAt, PRen.lookupArgs_vars? h vs hws]
  | var e k ih =>
    intro Δ f p' V W hp h
    simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨e', he, k', hk, rfl⟩ := hp
    simp only [treeAt, hex e h he]
    congr 1
    funext x
    exact ih hk (PRen.agrees_lift h x)
  | forLoop count inits body k ihb ihk =>
    intro Δ f p' V W hp h
    simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨c', hc, i', hi, b', hb, k', hk, rfl⟩ := hp
    simp only [treeAt, h count c' hc, PRen.lookupArgs_vars? h inits hi]
    have hbody : (fun acc i => treeAt ex tE fuel b'
          (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) W))) =
        (fun acc i => treeAt ex tE fuel body
          (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) V))) := by
      funext acc i
      exact ihb hb (PRen.agrees_liftApp (PRen.agrees_lift h _) _ acc)
    rw [hbody]
    congr 1
    funext acc
    exact ihk hk (PRen.agrees_liftApp h _ acc)
  | ifThenElse cond thn els k iht ihe ihk =>
    intro Δ f p' V W hp h
    simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨c', hc, t', ht, e', he, k', hk, rfl⟩ := hp
    simp only [treeAt, h cond c' hc, iht ht h, ihe he h]
    congr 1
    funext r
    exact ihk hk (PRen.agrees_liftApp h _ r)
  | whileLoop inits body k ihb ihk =>
    intro Δ f p' V W hp h
    simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨i', hi, b', hb, k', hk, rfl⟩ := hp
    simp only [treeAt, PRen.lookupArgs_vars? h inits hi]
    have hbody : (fun acc => treeAt ex tE fuel b' (hvAppend acc W)) =
        (fun acc => treeAt ex tE fuel body (hvAppend acc V)) := by
      funext acc
      exact ihb hb (PRen.agrees_liftApp h _ acc)
    rw [hbody]
    congr 1
    funext acc
    exact ihk hk (PRen.agrees_liftApp h _ acc)
  | call fn args k ih =>
    intro Δ f p' V W hp h
    simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨a', ha, k', hk, rfl⟩ := hp
    simp only [treeAt, PRen.lookupArgs_vars? h args ha]
    congr 1
    funext r
    exact ih hk (PRen.agrees_liftApp h _ r)

omit [DialectSignature d] [HasWord64 d] in
/-- Refined bodies give a refined exit-flag iteration. -/
theorem RefinesT.owhileIter {h₁ : ∀ e : E.Event, E.Resp e} {cs : List d.Ty}
    {s₁ s₂ : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))}
    (hs : ∀ a, RefinesT h₁ (s₁ a) (s₂ a)) :
    ∀ (n : Nat) (a : Valuation cs),
      RefinesT h₁ (NFProgCallTree.owhileIter s₁ n a) (NFProgCallTree.owhileIter s₂ n a) := by
  intro n
  induction n with
  | zero => intro a; exact RefinesT.refl _
  | succ n ih =>
    intro a
    refine RefinesT.obind (hs a) fun r => ?_
    split
    · exact ih _
    · exact RefinesT.refl _

/-- **The stage lemma of dead-binding elimination at the tree level**: at a reader invariant
    under renaming, the tree of `NFProg.dce p` refines the tree of `p` up to skipped source
    events, at every source handler. A removed let-binding is the skip of the events of its
    expression; a source run that fails there is the failed source leaf. -/
theorem ruttS_treeAt_dce (h₁ : ∀ e : E.Event, E.Resp e) {ex : ExprReader E d}
    (hex : ex.RenameInv) (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) :
    ∀ V : Valuation Γ,
      RefinesT h₁ (treeAt ex tE fuel p V) (treeAt ex tE fuel (NFProg.dce p) V) := by
  induction p with
  | ret vs => intro V; exact RefinesT.refl _
  | var e k ih =>
    intro V
    simp only [NFProg.dce]
    split
    · rename_i k' hr
      refine RuttS.skip_bind (ex e V) ?_
      cases hx : interp h₁ (ex e V) with
      | none => exact .fail rfl
      | some x =>
        rw [treeAt_rename? hex tE fuel (NFProg.dce k) hr (PRen.agrees_drop V x)]
        exact ih _
    · exact RefinesT.obind (RefinesT.refl _) fun x => ih _
  | forLoop count inits body k ihb ihk =>
    intro V
    exact RefinesT.obind (RefinesT.ofoldl (fun _ _ => ihb _) _ _) fun _ => ihk _
  | ifThenElse cond thn els k iht ihe ihk =>
    intro V
    refine RefinesT.obind ?_ fun _ => ihk _
    split
    · exact iht V
    · exact ihe V
  | whileLoop inits body k ihb ihk =>
    intro V
    exact RefinesT.obind (RefinesT.owhileIter (fun _ => ihb _) _ _) fun _ => ihk _
  | call f args k ih =>
    intro V
    exact RefinesT.obind (RefinesT.refl _) fun _ => ih _

end Dce

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
