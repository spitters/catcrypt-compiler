/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontProg
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInline
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeConsts

/-!
# The front of a module at the level of call trees

The source call tree of the entry of a module at its tree table (`moduleTreeTable`) is the
substitution of the table into the call tree at `evTable` (`nfTree_eq_substT`). The target call
tree of the program of `haxToNF`, with the calls other than the calls of linked functions answered
(`answerOut`), is a substitution into the call tree of the program before the inlining of the
calls of the functions of the module: a round of inlining substitutes the tree of the body of each
inlined call (`treeAt_inline_crate`), and the answering of the other calls is a substitution
(`answerOut_eq_substT`).

Substitution keeps a relation of trees (`RuttS.substK`) when the substituted trees of related
events are related, with a failed source answer allowed wherever the target tree stops at the
failed target answer (`KillsT`): the source call of a function of the module that fails is related
to every target tree, since the target program stops at the failed answer of the call.

## Main results

* `RuttS.substK`: substitution keeps `RuttS`, with failed answers.
* `answerOut_eq_substT`, `treeAt_inlineIter_crate`: the target tree as a substitution.
* `moduleEv_relT`: the relation of the substituted trees of a call, by induction on the depth.
* `front_relT`: the relation `FrontRET` of the front between the source call tree of the entry of
  a module and the call tree of the program of `haxToNF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv treeAt obind ofoldl
  owhileIter ExprReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst (substT substT_ret substT_vis)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubstTable (substT_bind)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent (AllEvT)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_ret bind_assoc)

/-! ## Substitutions -/

section Subst

variable {E E' E'' : EventSig}

/-- Substituting every event by itself is the identity. -/
theorem substT_id {R : Type} (t : CallTree E R) :
    substT (fun e => .vis e CallTree.ret) t = t := by
  induction t with
  | ret r => rfl
  | vis e k ih =>
    rw [substT_vis]
    show CallTree.vis e (fun a => (CallTree.ret a).bind fun a => substT _ (k a)) = _
    exact congrArg _ (funext ih)

/-- **Substitutions compose.** -/
theorem substT_substT {R : Type} (σ : ∀ e : E'.Event, CallTree E'' (E'.Resp e))
    (τ : ∀ e : E.Event, CallTree E' (E.Resp e)) (t : CallTree E R) :
    substT σ (substT τ t) = substT (fun e => substT σ (τ e)) t := by
  induction t with
  | ret r => rfl
  | vis e k ih =>
    rw [substT_vis, substT_vis, substT_bind]
    exact congrArg _ (funext ih)

/-- **Answering the events outside a predicate is a substitution**: an event kept stays an
    event, every other event is replaced by the leaf of its answer. -/
theorem answerOut_eq_substT {R : Type} (keep : E.Event → Bool) (h : ∀ e : E.Event, E.Resp e)
    (t : CallTree E R) :
    NFProgCallTreeCompose.answerOut keep h t =
      substT (fun e => if keep e then .vis e CallTree.ret else .ret (h e)) t := by
  induction t with
  | ret r => rfl
  | vis e k ih =>
    rw [substT_vis]
    by_cases hk : keep e = true
    · simp only [NFProgCallTreeCompose.answerOut, hk, ite_true]
      show _ = CallTree.vis e (fun a => (CallTree.ret a).bind fun a => substT _ (k a))
      exact congrArg _ (funext ih)
    · simp only [NFProgCallTreeCompose.answerOut, hk, Bool.false_eq_true, ite_false]
      exact ih _

end Subst

/-! ## Substitution with failed answers -/

section Kill

variable {E₁ E₂ : EventSig}

/-- **Every event of a tree satisfies `G`, and the tree stops at the answer `kill`**: at every
    event `e` the continuation at `kill e` is a leaf `o` at which every related source leaf
    failed. -/
def KillsT {R₁ R₂ : Type} (kill : ∀ e : E₂.Event, E₂.Resp e) (G : E₂.Event → Prop)
    (RR : R₁ → R₂ → Prop) (Fail : R₁ → Prop) : CallTree E₂ R₂ → Prop
  | .ret _ => True
  | .vis e k => G e ∧ (∃ o, k (kill e) = .ret o ∧ ∀ r, RR r o → Fail r)
      ∧ ∀ a, KillsT kill G RR Fail (k a)

/-- A source tree related to a target leaf at which every related source leaf failed is related
    to every target tree. -/
theorem RuttS.of_ret_fail {E₁' E₂' : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁'.Event, E₁'.Resp e}
    {RE : E₁'.Event → E₂'.Event → Prop}
    {RA : (e₁ : E₁'.Event) → (e₂ : E₂'.Event) → E₁'.Resp e₁ → E₂'.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {o : R₂} (ho : ∀ r, RR r o → Fail r)
    {s : CallTree E₁' R₁} (h : RuttS h₁ RE RA RR Fail s (.ret o)) :
    ∀ t, RuttS h₁ RE RA RR Fail s t := by
  generalize ht : (CallTree.ret o : CallTree E₂' R₂) = t₂ at h
  induction h with
  | ret hr =>
    cases ht
    exact fun _ => .fail (ho _ hr)
  | fail hf => exact fun _ => .fail hf
  | vis => cases ht
  | skip _ ih => exact fun t => .skip (ih ht t)

/-- **Substitution keeps `RuttS`, with failed answers.** Let `t₁` and `t₂` be related by `RuttS`
    at the source handler `h₁`, every event of `t₂` satisfy `G`, and `t₂` stop at the answers
    `kill` (`KillsT`). Substitute `σ₁` in `t₁` and `σ₂` in `t₂`. When the substituted trees of
    related events, the target event satisfying `G`, are related at the new relations, a source
    leaf related by the answer relation to the target leaf or to the answer `kill`, and a source
    leaf failed when the answer relation relates it to `kill`, and when the interpretation of the
    substituted tree of every source event under the new source handler `h₁'` is the answer of
    `h₁`, the substituted trees are related. -/
theorem RuttS.substK {E₁' E₂' : EventSig} {R₁ R₂ : Type}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e} {h₁' : ∀ e : E₁'.Event, E₁'.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RE' : E₁'.Event → E₂'.Event → Prop}
    {RA' : (e₁ : E₁'.Event) → (e₂ : E₂'.Event) → E₁'.Resp e₁ → E₂'.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    {σ₁ : ∀ e : E₁.Event, CallTree E₁' (E₁.Resp e)} {σ₂ : ∀ e : E₂.Event, CallTree E₂' (E₂.Resp e)}
    (kill : ∀ e : E₂.Event, E₂.Resp e) {G : E₂.Event → Prop}
    (hσ : ∀ e₁ e₂, RE e₁ e₂ → G e₂ →
      RuttS h₁' RE' RA' (fun a₁ a₂ => RA e₁ e₂ a₁ a₂ ∨ RA e₁ e₂ a₁ (kill e₂))
        (fun a₁ => RA e₁ e₂ a₁ (kill e₂)) (σ₁ e₁) (σ₂ e₂))
    (hh : ∀ e₁, interp h₁' (σ₁ e₁) = h₁ e₁)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttS h₁ RE RA RR Fail t₁ t₂) :
    KillsT kill G RR Fail t₂ → RuttS h₁' RE' RA' RR Fail (substT σ₁ t₁) (substT σ₂ t₂) := by
  induction h with
  | ret h => exact fun _ => .ret h
  | fail h => exact fun _ => .fail h
  | @vis e₁ e₂ k₁ k₂ he _ ih =>
    rintro ⟨hG, ⟨o, hko, ho⟩, hK⟩
    rw [substT_vis, substT_vis]
    refine NFProgCallTree.RuttS.bind (hσ _ _ he hG) (fun a₁ a₂ ha => ?_) (fun a₁ ha t => ?_)
    · rcases ha with ha | ha
      · exact ih a₁ a₂ ha (hK a₂)
      · have H := ih a₁ (kill e₂) ha (hK _)
        rw [hko, substT_ret] at H
        exact RuttS.of_ret_fail ho H _
    · have H := ih a₁ (kill e₂) ha (hK _)
      rw [hko, substT_ret] at H
      exact RuttS.of_ret_fail ho H _
  | @skip e₁ k₁ t₂ _ ih =>
    intro hK
    rw [substT_vis]
    refine NFProgCallTree.RuttS.skip_bind (σ₁ e₁) ?_
    rw [hh]
    exact ih hK

end Kill

/-! ## The events of the tree of a program -/

section Good

open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig linkReader opTree)
open Ctxt (Valuation)
open MultiBlockLowering (hvAppend)

/-- **A tree of leaf calls with good events that stops at the failed answer**: every event is
    the call of a name, argument types and a result type satisfying `Gc`, and the continuation at
    the answer `none` is the leaf `none`. -/
def GoodT (Gc : String → List NfTy → NfTy → Prop) {α : Type} :
    CallTree leafSig (Option α) → Prop
  | .ret _ => True
  | .vis e k => Gc e.name e.argTys e.ret ∧ k none = .ret none ∧ ∀ a, GoodT Gc (k a)

/-- An operation whose leaf calls satisfy `Gc`, under any number of names. -/
def OpOk (Gc : String → List NfTy → NfTy → Prop) : NfOp → Prop
  | .named _ o => OpOk Gc o
  | .call f as r => Gc f as r
  | _ => True

variable {Gc : String → List NfTy → NfTy → Prop}

/-- `GoodT` of a sequence of trees. -/
theorem goodT_obind {α β : Type} {t : CallTree leafSig (Option α)}
    {k : α → CallTree leafSig (Option β)} (ht : GoodT Gc t) (hk : ∀ a, GoodT Gc (k a)) :
    GoodT Gc (obind t k) := by
  induction t with
  | ret o =>
    cases o with
    | none => trivial
    | some a => exact hk a
  | vis e c ih =>
    obtain ⟨hG, hn, hc⟩ := ht
    refine ⟨hG, ?_, fun a => ih a (hc a)⟩
    show obind (c none) k = _
    rw [hn]
    rfl

/-- `GoodT` of a left fold of trees. -/
theorem goodT_ofoldl {α β : Type} {f : β → α → CallTree leafSig (Option β)}
    (hf : ∀ b a, GoodT Gc (f b a)) : ∀ (l : List α) (b : β), GoodT Gc (ofoldl f l b)
  | [], _ => trivial
  | a :: l, b => goodT_obind (hf b a) fun b' => goodT_ofoldl hf l b'

/-- `GoodT` of the iteration of a loop body. -/
theorem goodT_owhileIter {cs : Ctxt nfDialect}
    {step : Valuation cs →
      CallTree leafSig (Option (Valuation (HasBitType.bit (d := nfDialect) :: cs)))}
    (hs : ∀ a, GoodT Gc (step a)) :
    ∀ (n : Nat) (acc : Valuation cs), GoodT Gc (owhileIter (E := leafSig) (d := nfDialect)
      (cs := cs) step n acc)
  | 0, _ => trivial
  | n + 1, acc => goodT_obind (hs acc) fun r => by
      dsimp only
      split
      · exact goodT_owhileIter hs n _
      · trivial

/-- The tree of an operation whose leaf calls satisfy `Gc`. -/
theorem goodT_opTree : ∀ (o : NfOp), OpOk Gc o → ∀ a : HVector NfTy.denote o.sig,
    GoodT Gc (opTree o a) := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r => intro h a; exact ⟨h, rfl, fun _ => trivial⟩
  | _ => intro _ _; trivial

/-- **The tree of a program whose leaf calls satisfy `Gc`**, at the reader `linkReader` and a
    call environment whose trees satisfy `GoodT`. -/
theorem goodT_treeAt {tE : TreeCallEnv leafSig nfDialect}
    (htE : ∀ f as rs a, GoodT Gc (tE.call f as rs a)) (fuel : Nat) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    (∀ o, p.HasOp o → OpOk Gc o) → ∀ V : Valuation Γ, GoodT Gc (treeAt linkReader tE fuel p V) := by
  induction p with
  | ret vs => intro _ _; trivial
  | var e k ih =>
    intro hp V
    obtain ⟨o, rfl, args⟩ := e
    exact goodT_obind (goodT_opTree o (hp o (Or.inl rfl)) _)
      fun x => ih (fun o' ho => hp o' (Or.inr ho)) _
  | forLoop count inits body k ihb ihk =>
    intro hp V
    exact goodT_obind (goodT_ofoldl (fun _ _ => ihb (fun o ho => hp o (Or.inl ho)) _) _ _)
      fun _ => ihk (fun o ho => hp o (Or.inr ho)) _
  | ifThenElse cond thn els k iht ihe ihk =>
    intro hp V
    refine goodT_obind ?_ fun _ => ihk (fun o ho => hp o (Or.inr (Or.inr ho))) _
    split
    · exact iht (fun o ho => hp o (Or.inl ho)) V
    · exact ihe (fun o ho => hp o (Or.inr (Or.inl ho))) V
  | whileLoop inits body k ihb ihk =>
    intro hp V
    exact goodT_obind (goodT_owhileIter (fun _ => ihb (fun o ho => hp o (Or.inl ho)) _) _ _)
      fun _ => ihk (fun o ho => hp o (Or.inr ho)) _
  | call f args k ih =>
    intro hp V
    exact goodT_obind (htE _ _ _ _) fun _ => ih hp _

/-- A tree of `GoodT` has the events of `Gc` and stops at the answer `none`, at a leaf at which
    every source leaf related to `none` failed. -/
theorem killsT_of_goodT {R₁ α : Type} {RR : R₁ → Option α → Prop} {Fail : R₁ → Prop}
    (hF : ∀ r, RR r none → Fail r) :
    ∀ {t : CallTree leafSig (Option α)}, GoodT Gc t →
      KillsT (fun _ => none) (fun e : LeafCall => Gc e.name e.argTys e.ret) RR Fail t
  | .ret _, _ => trivial
  | .vis _ _, ⟨hG, hn, hk⟩ => ⟨hG, ⟨none, hn, hF⟩, fun a => killsT_of_goodT hF (hk a)⟩

end Good

/-! ## The inlining of the calls of the functions of a crate as a substitution -/

section Inline

open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig linkReader opTree)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateLib)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn)
open Ctxt (Valuation)

variable (fs : List CrateFn) (base : String → List NfTy → Option NfTy)

/-- The substitution of one round of inlining at the library of the functions `fs`: a leaf call
    the library has a body for runs the tree of the body at the argument values, read at its
    single result; every other leaf call is kept as its event. -/
def inlSub (tE : TreeCallEnv leafSig nfDialect) (fuel : Nat) :
    ∀ e : leafSig.Event, CallTree leafSig (leafSig.Resp e) := fun e =>
  match crateOp fs (.call e.name e.argTys e.ret) base with
  | some b => obind (treeAt linkReader tE fuel b e.args) fun r => .ret (some r.head)
  | none => .vis e CallTree.ret

/-- At an operation without a body in the library of a crate, the substitution `inlSub` keeps the
    tree of the operation. -/
theorem substT_opTree_none (tE : TreeCallEnv leafSig nfDialect) (fuel : Nat) :
    ∀ (o : NfOp), crateOp fs o base = none → ∀ a : HVector NfTy.denote o.sig,
      substT (inlSub fs base tE fuel) (opTree o a) = opTree o a := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r =>
    intro h a
    show (inlSub fs base tE fuel ⟨f, as, r, a⟩).bind CallTree.ret = _
    rw [bind_ret]
    simp only [inlSub, h]
    rfl
  | _ => intro _ _; rfl

/-- At an operation with a body `b` in the library of a crate, the substitution `inlSub` of the
    tree of the operation is the tree of the body, read at its single result. -/
theorem substT_opTree_some (tE : TreeCallEnv leafSig nfDialect) (fuel : Nat) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), crateOp fs o base = some b →
      ∀ a : HVector NfTy.denote o.sig,
        substT (inlSub fs base tE fuel) (opTree o a) =
          obind (treeAt linkReader tE fuel b a) fun r => .ret (some r.head) := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r =>
    intro b h a
    show (inlSub fs base tE fuel ⟨f, as, r, a⟩).bind CallTree.ret = _
    rw [bind_ret]
    simp only [inlSub, h]
  | _ => intro _ h; cases h

/-- The reader of the library of a crate is the substitution `inlSub` in the reader
    `linkReader`. -/
theorem inlineReader_crate (tE : TreeCallEnv leafSig nfDialect) (fuel : Nat) {Γ : Ctxt nfDialect}
    {t : NfTy} (e : Expr nfDialect Γ t) (V : Valuation Γ) :
    NFCallTreeInline.inlineReader (crateLib fs base) linkReader tE fuel e V =
      substT (inlSub fs base tE fuel) (linkReader e V) := by
  obtain ⟨o, rfl, args⟩ := e
  simp only [NFCallTreeInline.inlineReader, linkReader]
  generalize Expr.lookupArgs args V = a
  clear args
  split
  · rename_i b hb
    exact (substT_opTree_some fs base tE fuel o b hb a).symm
  · rename_i hb
    exact (substT_opTree_none fs base tE fuel o hb a).symm

/-- **A round of inlining at the library of a crate is the substitution `inlSub`**, at a call
    environment whose trees are the failed leaf. -/
theorem treeAt_inline_crate {tE : TreeCallEnv leafSig nfDialect}
    (htE : ∀ f as rs a, tE.call f as rs a = .ret none) (fuel : Nat) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) {p' : NFProg nfDialect Γ ts}
    (hq : NFProg.inline? (crateLib fs base) p = some p') (V : Valuation Γ) :
    treeAt linkReader tE fuel p' V =
      substT (inlSub fs base tE fuel) (treeAt linkReader tE fuel p V) := by
  rw [NFCallTreeInline.treeAt_inline? NFProgCallTreeExt.linkReader_renameInv tE fuel p hq,
    NFCallTreeInline.substT_treeAt]
  refine NFCallTreeInline.treeAt_ext ?_ ?_ fuel p V
  · intro Γ t e V
    exact inlineReader_crate fs base tE fuel e V
  · intro f as rs a
    show tE.call f as rs a = substT _ (tE.call f as rs a)
    rw [htE]
    rfl

/-- The substitution of `n` rounds of inlining at the library of a crate. -/
def inlSubN (tE : TreeCallEnv leafSig nfDialect) (fuel : Nat) :
    Nat → ∀ e : leafSig.Event, CallTree leafSig (leafSig.Resp e)
  | 0 => fun e => .vis e CallTree.ret
  | n + 1 => fun e => substT (inlSubN tE fuel n) (inlSub fs base tE fuel e)

/-- **Rounds of inlining at the library of a crate are the substitution `inlSubN`**, on a
    program whose rounds do not refuse. -/
theorem treeAt_inlineIter_crate {tE : TreeCallEnv leafSig nfDialect}
    (htE : ∀ f as rs a, tE.call f as rs a = .ret none) (fuel : Nat) (P : NfOp → Bool)
    {Γ : Ctxt nfDialect} {ts : List NfTy} :
    ∀ (n : Nat) (p : NFProg nfDialect Γ ts), p.inlineIterOk (crateLib fs base) P n = true →
      ∀ V : Valuation Γ, treeAt linkReader tE fuel (p.inlineIter (crateLib fs base) n) V =
        substT (inlSubN fs base tE fuel n) (treeAt linkReader tE fuel p V)
  | 0, p, _, V => (substT_id _).symm
  | n + 1, p, hok, V => by
    simp only [NFProg.inlineIterOk, Bool.and_eq_true] at hok
    obtain ⟨-, hok⟩ := hok
    simp only [NFProg.inlineIter]
    split at hok
    · rename_i q hq
      rw [treeAt_inlineIter_crate htE fuel P n q hok V, treeAt_inline_crate fs base htE fuel p hq,
        substT_substT]
      rfl
    · cases hok

end Inline

/-! ## The body of a function of a module -/

section Callee

open _root_.Hax (ImpExpr Value Env Outcome TExpr)
open CatCrypt.Crypto.Hax (HaxModule ModFn)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn EntryVals encAll paramsEnv entryCtx RepeatCalls)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateLib crateBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig linkReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF (evTable ImpRE ImpRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontProg (ProgOut)
open Ctxt (Valuation)

/-- **The extraction of a function of a module and the tree of its body at `evTable`.** Let
    `crateBody` return the body `b` of the preparation of the function `f` by `nfBody` at the
    argument types `as` and the result type `r`, the extraction of `f` pass `haxFrontShapeOk`
    and have call-free arguments at the calls of its inlined closures (`spineArgsOk`), and the
    source handler answer `repeat` as the table of `repeat` calls. From the environment binding
    the names of the parameters to the encodings of the arguments `a`, at a target fuel at least
    the source fuel, the call tree of the extraction at `evTable` and the tree of `b` at `a` are
    related by `RuttS` at `ImpRE`, `ImpRA` and `ProgOut r`, the source leaves that are not values
    failed. -/
theorem callee_relT (fs : List CrateFn) (base : String → List NfTy → Option NfTy) (f : ModFn)
    (hok : CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr = true)
    (hs : NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (h₁ : ∀ e : linkSig.Event, linkSig.Resp e) (hR : RepeatCalls fun g vals => h₁ ⟨g, vals⟩)
    (tE : TreeCallEnv leafSig nfDialect) {as : Ctxt nfDialect} {r : NfTy}
    {b : NFProg nfDialect as [r]} (hb : crateBody fs (f.prep nfBody) as r base = some b)
    (fuel tf : Nat) (hft : fuel ≤ tf) (a : Valuation as) :
    RuttS h₁ ImpRE ImpRA (ProgOut r) (fun x => ¬ ∃ v, x.1 = .val v)
      (nfTree evTable fuel f.texpr.erase (paramsEnv (f.params.map (·.1)) (encAll as a)))
      (treeAt linkReader tE tf b a) := by
  unfold crateBody at hb
  split at hb
  · obtain ⟨o, ho, hb⟩ := Option.bind_eq_some_iff.mp hb
    split at hb
    · rename_i hty
      obtain ⟨h1, h2⟩ := hty
      cases hb
      subst h1 h2
      simp only [cast_eq]
      have hB := NFCallTreeFrontBody.nfBody_relT h₁ evTable fuel f.texpr hok hs
        (paramsEnv (f.params.map (·.1)) (encAll (entryCtx f.params) a))
      have hI := NFCallTreeImpToNF.impToNF_relT _ h₁ hR tE (nfBody f.texpr) none _ ho fuel tf hft
        _ a (CatCrypt.Crypto.Hax.NFInline.entryEnv_rel_paramsEnv f.params a)
      have hI' : RuttS h₁ ImpRE ImpRA (ProgOut o.t) NFCallTreeImpToNF.SrcFail
          (denoteT evTable fuel (nfBody f.texpr)
            (paramsEnv (f.params.map (·.1)) (encAll (entryCtx f.params) a)))
          (treeAt linkReader tE tf o.prog a) := by
        rw [CatCrypt.Crypto.Hax.ImpToNF.Out.prog, NFCallTreeImpToNF.treeAt_plug,
          ← bind_ret (denoteT evTable fuel (nfBody f.texpr) _)]
        refine NFCallTreeImpToNF.ruttS_obindK hI (fun r W hr => .ret ?_) ?_
          (fun r hf _ => .fail hf)
        · obtain ⟨v, W', hv, hW, -, henc⟩ := hr
          cases hW
          intro v' hv' _
          rw [hv] at hv'
          cases hv'
          exact ⟨_, rfl, henc⟩
        · rintro r w ⟨v, W, -, hW, -⟩
          exact ⟨W, hW⟩
      refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans ?_ hB hI')
      · rintro r₀ o' ⟨r₁, h01, h12⟩ v hv hcf
        rcases h01 with h | ⟨w, -, h, -⟩
        · exact h12 v (h.trans hv) hcf
        · rw [hv] at h
          cases h
          simp at hcf
      · intro r₀ r₁ h01 hf ⟨v, hv⟩
        rcases h01 with h | ⟨w, -, -, h'⟩
        · exact hf v (h.trans hv)
        · exact hf w h'
    · cases hb
  · cases hb

end Callee

/-! ## The calls of a module, by induction on the depth -/

section Module

open _root_.Hax (ImpExpr Value Env Outcome TExpr Builtins)
open CatCrypt.Crypto.Hax (HaxModule ModFn LinkedFn linkBi linkBi_of_find_none find?_prep
  dec_controlFlow refBi_repeatCalls)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn encAll paramsEnv RepeatCalls TypedCalls tableOf dec enc
  hax64SigOf)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateLib crateBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig linkReader
  leafHandler)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF (evTable ImpRE ImpRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontProg (ProgOut nfTree_eq_substT)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (FrontRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped (FrontRET)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3 (keepL)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (srcFail)

/-- The substitution answering the leaf calls other than the calls of the linked functions of
    `m` by the leaf table of the table of the linked functions over `bi`. -/
def answerSub (m : HaxModule) (bi : Builtins) :
    ∀ e : leafSig.Event, CallTree leafSig (leafSig.Resp e) := fun e =>
  if keepL m e then .vis e CallTree.ret else .ret (leafHandler (tableOf (m.linkTable bi)) e)

/-- **A leaf call the front relates to a call of the module**: a call of a function of `m` with
    a body in the library of the prepared functions, at the result type of the function; a call
    of a linked function at its parameter types and its result type; another call typed by
    `hax64SigOf`. -/
def GoodCall (m : HaxModule) (g : String) (as : List NfTy) (r : NfTy) : Prop :=
  match m.fns.find? (·.name == g) with
  | some f => (crateOp (m.prepared nfBody) (.call g as r) m.linkSig).isSome = true ∧ r = f.res
  | none =>
    match m.linked.find? (·.name == g) with
    | some l => as = l.params.map (·.2) ∧ r = l.res
    | none => hax64SigOf g as = some r

/-- The answer of a call of a function of a module from the leaf of its run: the value of the
    leaf when `dec` decodes it at the result type `t`, and the failed answer otherwise. -/
def decRes (t : NfTy) (x : Outcome × Env) : Option Value :=
  match x.1 with
  | .val v => if (dec t v).isSome then some v else none
  | _ => none

variable {E : EventSig}

/-- `refBiT` at a name of a function at a positive depth. -/
theorem refBiT_succ_some (fs : List ModFn) (bt : TreeTable E) (fuel n : Nat) {g : String}
    {f : ModFn} (hg : fs.find? (·.name == g) = some f) (vals : List Value) :
    refBiT fs bt fuel (n + 1) g vals =
      (nfTree (refBiT fs bt fuel n) fuel f.texpr.erase (paramsEnv (f.params.map (·.1)) vals)).bind
        fun x => .ret (decRes f.res x) := by
  simp only [refBiT, hg]
  rfl

/-- `refBiT` at a name of a function at depth `0`. -/
theorem refBiT_zero_some (fs : List ModFn) (bt : TreeTable E) (fuel : Nat) {g : String}
    {f : ModFn} (hg : fs.find? (·.name == g) = some f) (vals : List Value) :
    refBiT fs bt fuel 0 g vals = .ret none := by
  simp only [refBiT, hg]

/-- `refBiT` at a name of no function. -/
theorem refBiT_none (fs : List ModFn) (bt : TreeTable E) (fuel n : Nat) {g : String}
    (hg : fs.find? (·.name == g) = none) (vals : List Value) :
    refBiT fs bt fuel n g vals = bt g vals := by
  cases n <;> simp only [refBiT, hg]

/-- The substitution of an event by itself followed by its answers. -/
theorem substT_vis_ret {E' : EventSig} (σ : ∀ e : E.Event, CallTree E' (E.Resp e))
    (e : E.Event) : substT σ (.vis e CallTree.ret) = σ e :=
  bind_ret _

/-- A leaf call without a body is kept by every number of rounds of inlining. -/
theorem inlSubN_none (fs : List CrateFn) (base : String → List NfTy → Option NfTy)
    (tE : TreeCallEnv leafSig nfDialect) (fuel : Nat) {e : leafSig.Event}
    (h : crateOp fs (.call e.name e.argTys e.ret) base = none) :
    ∀ n, inlSubN fs base tE fuel n e = .vis e CallTree.ret
  | 0 => rfl
  | n + 1 => by
    have he : inlSub fs base tE fuel e = .vis e CallTree.ret := by simp only [inlSub, h]
    show substT _ (inlSub fs base tE fuel e) = _
    rw [he, substT_vis_ret, inlSubN_none fs base tE fuel h n]

/-- A name of no function of a module has no body in the library of its prepared functions. -/
theorem crateOp_prepared_none {m : HaxModule} {g : String}
    (hg : m.fns.find? (·.name == g) = none) (as : List NfTy) (r : NfTy) :
    crateOp (m.prepared nfBody) (.call g as r) m.linkSig = none := by
  simp only [crateOp, HaxModule.prepared, find?_prep, hg, Option.map_none, Option.bind_none]

/-- The body of a call of a function of a module in the library of its prepared functions. -/
theorem crateOp_prepared_some {m : HaxModule} {g : String} {f : ModFn}
    (hg : m.fns.find? (·.name == g) = some f) (as : List NfTy) (r : NfTy) :
    crateOp (m.prepared nfBody) (.call g as r) m.linkSig =
      crateBody (m.prepared nfBody) (f.prep nfBody) as r m.linkSig := by
  simp only [crateOp, HaxModule.prepared, find?_prep, hg, Option.map_some, Option.bind_some]

/-- A failed source leaf decodes to the failed answer. -/
theorem decRes_of_srcFail (t : NfTy) {x : Outcome × Env} (h : srcFail x) : decRes t x = none := by
  unfold decRes
  split
  · rename_i v hv
    obtain ⟨b, w, rfl⟩ : ∃ b w, v = .controlFlow b w := by
      have hc := h v hv
      cases v <;> simp_all [Value.isControlFlow]
    simp [dec_controlFlow]
  · rfl

/-- A source leaf related to the failed target leaf by `ProgOut` is failed. -/
theorem srcFail_of_progOut_none {t : NfTy} {x : Outcome × Env} (h : ProgOut t x none) :
    srcFail x := by
  intro v hv
  cases hc : v.isControlFlow
  · obtain ⟨y, hy, -⟩ := h v hv hc
    cases hy
  · rfl

/-- A source leaf related to a target leaf by `ProgOut` decodes to the encoding of the target
    value or to the failed answer. -/
theorem decRes_of_progOut {t t' : NfTy} {x : Outcome × Env} {w : HVector NfTy.denote [t]}
    (h : ProgOut t x (some w)) : decRes t' x = some (enc t w.head) ∨ decRes t' x = none := by
  unfold decRes
  split
  · rename_i v hv
    split
    · rename_i hs
      left
      cases hc : v.isControlFlow
      · obtain ⟨y, hy, rfl⟩ := h v hv hc
        cases hy
        rfl
      · obtain ⟨b, w', rfl⟩ : ∃ b w', v = .controlFlow b w' := by
          cases v <;> simp_all [Value.isControlFlow]
        rw [dec_controlFlow] at hs
        cases hs
    · exact Or.inr rfl
  · exact Or.inr rfl

/-- A source leaf that is not a value is a failed source leaf. -/
theorem srcFail_of_not_val {x : Outcome × Env} (h : ¬ ∃ v, x.1 = .val v) : srcFail x :=
  fun v hv => (h ⟨v, hv⟩).elim

/-- **A call of no function of a module.** At a leaf call related by `ImpRE` to a source call of
    a name of no function of `m`, typed by `GoodCall`, the source tree of the linked tree table
    and the answered target event are related: a call of a linked function is an event of both,
    related by `FrontRET`; another call is answered on both sides, by `bi` and by the leaf table,
    at the typing `hax64SigOf` of `bi`. -/
theorem linkEv_relT (m : HaxModule) (bi : Builtins) (hT : TypedCalls bi hax64SigOf)
    {e₀ : linkSig.Event} {e₁ : leafSig.Event} (hE : ImpRE e₀ e₁)
    (hf : m.fns.find? (·.name == e₁.name) = none) (hG : GoodCall m e₁.name e₁.argTys e₁.ret) :
    RuttS (linkHandler m) (FrontRET m) FrontRA
      (fun a₀ a₁ => ImpRA e₀ e₁ a₀ a₁ ∨ ImpRA e₀ e₁ a₀ none) (fun a₀ => ImpRA e₀ e₁ a₀ none)
      (linkTreeTable m bi (LinkCall.name e₀) (LinkCall.args e₀)) (answerSub m bi e₁) := by
  obtain ⟨g, vals⟩ := e₀
  obtain ⟨g', as, r, a⟩ := e₁
  obtain ⟨hn, hv⟩ := hE
  dsimp only at hn hv hf hG ⊢
  subst hn hv
  unfold GoodCall at hG
  rw [hf] at hG
  cases hl : m.linked.find? (·.name == g') with
  | some l =>
    rw [hl] at hG
    obtain ⟨has, hr⟩ := hG
    have hk : keepL m ⟨g', as, r, a⟩ = true :=
      List.any_eq_true.mpr ⟨l, List.mem_of_find?_eq_some hl, by
        have h := List.find?_some hl
        exact h⟩
    simp only [linkTreeTable, hl, answerSub, hk, ite_true]
    refine .vis ⟨⟨rfl, rfl, l, hl, hr⟩, fun l' hl' => ?_⟩ fun a₀ a₁ ha => .ret (Or.inl ha)
    rw [hl] at hl'
    cases hl'
    exact has
  | none =>
    rw [hl] at hG
    have hk : keepL m ⟨g', as, r, a⟩ = false := by
      unfold keepL
      rw [List.any_eq_false]
      intro l hlm hle
      exact List.find?_eq_none.mp hl l hlm hle
    simp only [linkTreeTable, hl, answerSub, hk, Bool.false_eq_true, ite_false]
    refine .ret (Or.inl ?_)
    show bi g' (encAll as a) = ((linkBi m.linked bi g' (encAll as a)).bind (dec r)).map (enc r)
    rw [linkBi_of_find_none _ _ hl]
    cases hb : bi g' (encAll as a) with
    | none => rfl
    | some v =>
      obtain ⟨y, hy, rfl⟩ := hT g' as r hG a v hb
      simp [hy]

/-- **The calls of a module, by induction on the depth.** Let the functions of the module `m`
    pass `haxFrontShapeOk` and `spineArgsOk`, none be named `repeat`, the table of the linked
    functions over `bi` satisfy `RepeatCalls`, `bi` be typed by `hax64SigOf`, and the leaf calls of
    every body of the library of the prepared functions satisfy `GoodCall`. At a leaf call
    related by `ImpRE` to a source call and satisfying `GoodCall`, at a target fuel at least the
    fuel `fuelC` of the functions, the tree of `refBiT` at the depth `k` and the tree of the leaf
    call after `k` rounds of inlining and the answering of the calls other than the calls of the
    linked functions are related by `RuttS` at `FrontRET` and `FrontRA`, a source answer related
    by `ImpRA` to the target answer or to the failed answer, a source answer related to the
    failed answer failed. A call of a function at depth `0` is the failed source answer; at a
    positive depth the run of the extraction is related to the inlined body by `callee_relT` and
    the relation at the smaller depth (`RuttS.substK`). -/
theorem moduleEv_relT (m : HaxModule) (bi : Builtins) (hT : TypedCalls bi hax64SigOf)
    (hR : RepeatCalls (m.linkTable bi)) (hfR : m.fns.find? (·.name == "repeat") = none)
    (hfs : ∀ f ∈ m.fns, CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr = true
      ∧ NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hgood : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk (GoodCall m) o)
    {tE : TreeCallEnv leafSig nfDialect} (htE : ∀ f as rs a, tE.call f as rs a = .ret none)
    (fuelC tf : Nat) (hft : fuelC ≤ tf) :
    ∀ (k : Nat) (e₀ : linkSig.Event) (e₁ : leafSig.Event), ImpRE e₀ e₁ →
      GoodCall m e₁.name e₁.argTys e₁.ret →
      RuttS (linkHandler m) (FrontRET m) FrontRA
        (fun a₀ a₁ => ImpRA e₀ e₁ a₀ a₁ ∨ ImpRA e₀ e₁ a₀ none) (fun a₀ => ImpRA e₀ e₁ a₀ none)
        (refBiT m.fns (linkTreeTable m bi) fuelC k (LinkCall.name e₀) (LinkCall.args e₀))
        (substT (answerSub m bi) (inlSubN (m.prepared nfBody) m.linkSig tE tf k e₁)) := by
  intro k
  induction k with
  | zero =>
    intro e₀ e₁ hE hG
    cases hf : m.fns.find? (·.name == e₁.name) with
    | none =>
      have hg : m.fns.find? (·.name == LinkCall.name e₀) = none := by rw [← hE.1]; exact hf
      rw [refBiT_none _ _ _ _ hg, inlSubN_none _ _ _ _ (crateOp_prepared_none hf _ _) 0,
        substT_vis_ret]
      exact linkEv_relT m bi hT hE hf hG
    | some f =>
      have hg : m.fns.find? (·.name == LinkCall.name e₀) = some f := by rw [← hE.1]; exact hf
      rw [refBiT_zero_some _ _ _ hg]
      exact .fail rfl
  | succ k ih =>
    intro e₀ e₁ hE hG
    cases hf : m.fns.find? (·.name == e₁.name) with
    | none =>
      have hg : m.fns.find? (·.name == LinkCall.name e₀) = none := by rw [← hE.1]; exact hf
      rw [refBiT_none _ _ _ _ hg, inlSubN_none _ _ _ _ (crateOp_prepared_none hf _ _) _,
        substT_vis_ret]
      exact linkEv_relT m bi hT hE hf hG
    | some f =>
      have hg : m.fns.find? (·.name == LinkCall.name e₀) = some f := by rw [← hE.1]; exact hf
      have hfm : f ∈ m.fns := List.mem_of_find?_eq_some hf
      unfold GoodCall at hG
      rw [hf] at hG
      obtain ⟨hb, hr⟩ := hG
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hb
      have hb' := hb
      rw [crateOp_prepared_some hf] at hb'
      have hinl : inlSub (m.prepared nfBody) m.linkSig tE tf e₁ =
          obind (treeAt linkReader tE tf b e₁.args) fun r => .ret (some r.head) := by
        simp only [inlSub, hb]
      have hRk : RepeatCalls fun g vals =>
          interp (linkHandler m) (refBiT m.fns (linkTreeTable m bi) fuelC k g vals) := by
        change RepeatCalls (interpTable (linkHandler m) (refBiT m.fns (linkTreeTable m bi) fuelC k))
        rw [interpTable_refBiT, interpTable_linkTreeTable]
        exact refBi_repeatCalls m.fns hR hfR fuelC k
      have hC := callee_relT (m.prepared nfBody) m.linkSig f (hfs f hfm).1 (hfs f hfm).2
        (fun e => interp (linkHandler m) (refBiT m.fns (linkTreeTable m bi) fuelC k e.name e.args))
        hRk tE hb' fuelC tf hft e₁.args
      have hS := RuttS.substK (fun _ => none)
        (G := fun e : LeafCall => GoodCall m e.name e.argTys e.ret)
        (σ₁ := fun e : LinkCall => refBiT m.fns (linkTreeTable m bi) fuelC k e.name e.args)
        (σ₂ := fun e => substT (answerSub m bi) (inlSubN (m.prepared nfBody) m.linkSig tE tf k e))
        (fun e₀' e₁' hE' hG' => ih e₀' e₁' hE' hG') (fun _ => rfl)
        (NFCallTreeFrontBody.RuttS.mono_fail (fun x hx => srcFail_of_not_val hx) hC)
        (killsT_of_goodT (fun x hx => srcFail_of_progOut_none hx)
          (goodT_treeAt (fun f as rs a => by rw [htE]; trivial) tf b (hgood _ _ _ b hb) e₁.args))
      rw [refBiT_succ_some _ _ _ _ hg, hE.2,
        nfTree_eq_substT (refBiT m.fns (linkTreeTable m bi) fuelC k)]
      change RuttS _ _ _ _ _ _ (substT (answerSub m bi)
        (substT (inlSubN (m.prepared nfBody) m.linkSig tE tf k)
          (inlSub (m.prepared nfBody) m.linkSig tE tf e₁)))
      rw [hinl, substT_substT, NFCallTreeInline.substT_obind]
      refine NFProgCallTree.RuttS.bind hS (fun x o hx => ?_) (fun x hx t => ?_)
      · cases o with
        | none => exact .ret (Or.inr (decRes_of_srcFail f.res (srcFail_of_progOut_none hx)))
        | some w =>
          refine .ret ?_
          rcases decRes_of_progOut (t' := f.res) hx with h | h
          · exact Or.inl h
          · exact Or.inr h
      · rw [decRes_of_srcFail f.res hx]
        exact .fail rfl

end Module

/-! ## The front of a module -/

section Front

open _root_.Hax (ImpExpr Value Env Outcome TExpr Builtins)
open CatCrypt.Crypto.Hax (HaxModule ModFn find?_prep hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn EntryVals RepeatCalls tableOf entryCtx)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateLib crateInline?_eq_some)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig linkReader
  leafHandler)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontProg (nfTree_eq_substT)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (answerOut FrontRA FrontRR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped (FrontRET)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3 (keepL)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (srcFail)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)

/-- `spineArgsOk` of an extraction with the constants of a layout bound is `spineArgsOk` of the
    extraction. -/
theorem spineArgsOk_bindConsts (te : TExpr) :
    ∀ cs : List (String × Value), NFCallTreeInlineSpine.spineArgsOk (bindConsts cs te).erase =
      NFCallTreeInlineSpine.spineArgsOk te.erase
  | [] => rfl
  | (k, v) :: cs => by
    simp only [bindConsts]
    split
    · rw [TExpr.erase, TExpr.erase]
      exact spineArgsOk_bindConsts te cs
    · exact spineArgsOk_bindConsts te cs

/-- **The front of a module at the level of call trees.** Let the entry and the functions of the
    module `m` have call-free arguments at the calls of their inlined closures (`spineArgsOk`; the
    inlining of closures duplicates the calls in the arguments otherwise), the leaf calls of the
    source program of the entry and of every body of the library of the prepared functions
    satisfy `GoodCall` (a call of a function of `m` has a body in the library: the rounds of
    inlining refuse a call without one only in the rounds they make, and at the result type of
    the function; a call of a linked function is at the parameter types of the function, which
    `FrontRET` asks for and the call typing `crateSigOf` does not give, since it lets an integer
    argument fit a word parameter), and the call environment `tE` answer every call by the failed
    leaf. When `haxToNF` returns `q` on `m`, from a source environment the layout reads off an
    entry state, at every fuel of the functions and of the entry, there are a valuation of the
    entry related to the environment and a target fuel at which the source call tree of the
    entry at the tree table of the module and the call tree of `q` at `linkReader`, with the calls
    other than the calls of the linked functions answered by the leaf table, are related by
    `RuttS` at `FrontRET`, `FrontRA`, `FrontRR` and `srcFail`. This is the hypothesis `hfront` of
    `NFProgCallTreeModule.r3FG_of_front`. -/
theorem front_relT {m : HaxModule} {σ : AbiLayout} (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ f as rs a, tE.call f as rs a = .ret none)
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hgoodE : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o → OpOk (GoodCall m) o)
    (hgood : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk (GoodCall m) o) :
    ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
      haxToNF σ m = some q → ∀ (sa : Ascent.AddrMem.AState), σ.Regions sa → ∀ (env : Env),
      σ.EnvOf sa env → ∀ (fuelC fuel : Nat), ∃ (V : Ctxt.Valuation (entryCtx (abiEntry σ)))
        (tf : Nat), EntryVals env (abiEntry σ) V
        ∧ RuttS (linkHandler m) (FrontRET m) FrontRA (FrontRR q.1) srcFail
          (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) := by
  intro q hq sa _ env henv fuelC fuel
  obtain ⟨hfs0, hshape, hlk, p, hp, hinl⟩ := haxToNF_eq_some hq
  obtain ⟨V, hV⟩ := CatCrypt.Crypto.Hax.ImpToNF.entryVals_of_typed (entryTyped_abiEntry henv)
  refine ⟨V, max fuel fuelC, hV, ?_⟩
  have hfR : m.fns.find? (·.name == "repeat") = none := by
    have h := crateArrOk_find_repeat hfs0
    rw [HaxModule.prepared, find?_prep] at h
    exact Option.map_eq_none_iff.mp h
  have hR : RepeatCalls (m.linkTable hax64WExit) := linkTable_repeatCalls hlk
  have hinl' : CatCrypt.Crypto.Hax.NFInline.crateInline? (m.prepared nfBody) m.depth p m.linkSig
      = some q.2 := hinl
  obtain ⟨hok, hq2⟩ := crateInline?_eq_some hinl'
  have hiter := (Bool.and_eq_true_iff.mp hok).1
  rw [← NFCallTreeConsts.nfTree_bindConsts_of_envOf _ fuel m.entry henv,
    nfTree_eq_substT (moduleTreeTable m hax64WExit fuelC), hq2, answerOut_eq_substT,
    treeAt_inlineIter_crate _ _ htE _ _ m.depth p hiter V, substT_substT]
  have hR1 : RepeatCalls fun g vals =>
      interp (linkHandler m) (moduleTreeTable m hax64WExit fuelC g vals) := by
    change RepeatCalls (interpTable (linkHandler m) (moduleTreeTable m hax64WExit fuelC))
    rw [interpTable_moduleTreeTable]
    exact CatCrypt.Crypto.Hax.refBi_repeatCalls m.fns hR hfR fuelC m.depth
  have hsrc := NFCallTreeFrontProg.srcProg_relT (m.prepared nfBody ++ m.linkedFns) σ
    (bindConsts σ.consts m.entry) hp (by rw [spineArgsOk_bindConsts]; exact hspine)
    (fun e => interp (linkHandler m) (moduleTreeTable m hax64WExit fuelC e.name e.args)) hR1 tE
    fuel (max fuel fuelC) (le_max_left _ _) env V hV
  have hS := RuttS.substK (fun _ => none)
    (G := fun e : LeafCall => GoodCall m e.name e.argTys e.ret)
    (σ₁ := fun e : LinkCall => moduleTreeTable m hax64WExit fuelC e.name e.args)
    (σ₂ := fun e => substT (answerSub m hax64WExit)
      (inlSubN (m.prepared nfBody) m.linkSig tE (max fuel fuelC) m.depth e))
    (fun e₀ e₁ hE hG => moduleEv_relT m hax64WExit CatCrypt.Crypto.Hax.hax64WExit_typedCalls hR
      hfR (fun f hf => ⟨hshape f hf, hfs f hf⟩) hgood htE fuelC (max fuel fuelC)
      (le_max_right _ _) m.depth e₀ e₁ hE hG) (fun _ => rfl)
    (NFCallTreeFrontBody.RuttS.mono_fail (fun x hx => srcFail_of_not_val hx) hsrc)
    (killsT_of_goodT (fun x hx => srcFail_of_progOut_none hx)
      (goodT_treeAt (fun f as rs a => by rw [htE]; trivial) (max fuel fuelC) p
        (hgoodE q p hq hp) V))
  exact NFProgCallTreeExt.RuttS.mono (fun _ _ h => h) hS

end Front

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule
