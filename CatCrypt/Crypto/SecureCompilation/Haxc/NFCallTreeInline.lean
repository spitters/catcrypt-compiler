/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFInline
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubstTable

/-!
# Inlining of calls at the level of call trees

The inlining `NFProg.inline? L p` replaces a let-binding of an operation and a `call` node the
library `L` has a body for by the body, followed by the continuation. In the call tree `treeAt`
a let-binding runs the tree of the expression reader and a `call` node the tree of the tree call
environment. The tree of `inline? L p` at the reader `ex` and the call environment `tE` is the
tree of `p` at the reader `inlineReader L ex tE fuel` and the call environment
`inlineEnv L ex tE fuel`, which run the tree of the body at `ex` and `tE` where the library has
one (`treeAt_inline?`): an equality of trees, with no hypothesis on the library.

Two consequences follow.

* At the call events (`nfProgTree`) and a library without bodies of operations, the tree of
  `inline? L p` is the substitution `substT (inlineSubst L fuel)` of the tree of `p`: each call
  the library inlines is replaced by the tree of its body, every other call is kept as its
  event (`nfProgTree_inline?`). `RuttS.substT` then transfers a relation of the trees of `p`.
* The soundness of a library becomes a relation of trees (`InlineLib.TreeSound`): the tree of
  the body of a call refines the tree of the call, and the tree of the body of an operation the
  tree of the reader. Under it the tree of `p` is refined by the tree of `inline? L p`
  (`refinesT_treeAt_inline?`) and of `inlineIter L n p` (`refinesT_treeAt_inlineIter`).

## Main definitions

* `inlineReader`, `inlineEnv`: the reader and the call environment running the trees of the
  bodies of a library.
* `inlineSubst`: the substitution of the trees of the bodies for the call events.
* `InlineLib.TreeSound`: soundness of a library as a refinement of trees.

## Main results

* `treeAt_seq?`: the tree of a splice is the tree of the body followed by the continuation.
* `treeAt_inline?`: the tree of the inlined program is the tree of the program at the reader
  and the call environment of the library.
* `substT_treeAt`, `nfProgTree_inline?`: substitution in the tree of a program, and the inlined
  call tree as a substitution.
* `interp_inlineSubst`: the substituted tree of a call interprets to the run of the body.
* `RefinesT.treeAt`, `refinesT_treeAt_inline?`, `refinesT_treeAt_inlineIter`: refinement of the
  tree under refined readers and call environments, and of inlining under a sound library.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst (substT substT_vis)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubstTable (substT_bind)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## Sequencing of trees of optional results -/

section OBind

variable {E : EventSig}

/-- `obind` is associative. -/
theorem obind_assoc {α β γ : Type} (t : CallTree E (Option α))
    (f : α → CallTree E (Option β)) (g : β → CallTree E (Option γ)) :
    obind (obind t f) g = obind t fun a => obind (f a) g := by
  unfold obind
  rw [NFCallTreeAnfPick.bind_assoc]
  congr 1
  funext o
  cases o <;> rfl

/-- Substitution commutes with `obind`. -/
theorem substT_obind {E' : EventSig} (σ : ∀ e : E.Event, CallTree E' (E.Resp e)) {α β : Type}
    (t : CallTree E (Option α)) (k : α → CallTree E (Option β)) :
    substT σ (obind t k) = obind (substT σ t) fun a => substT σ (k a) := by
  unfold obind
  rw [substT_bind]
  congr 1
  funext o
  cases o <;> rfl

/-- Substitution commutes with `ofoldl`. -/
theorem substT_ofoldl {E' : EventSig} (σ : ∀ e : E.Event, CallTree E' (E.Resp e)) {α β : Type}
    (f : β → α → CallTree E (Option β)) (l : List α) (b : β) :
    substT σ (ofoldl f l b) = ofoldl (fun b a => substT σ (f b a)) l b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [ofoldl, substT_obind, ih]

end OBind

section Tree

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

omit [DialectSignature d] [HasWord64 d] in
/-- Substitution commutes with `owhileIter`. -/
theorem substT_owhileIter {E' : EventSig} (σ : ∀ e : E.Event, CallTree E' (E.Resp e))
    {cs : List d.Ty}
    (step : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))) :
    ∀ (n : Nat) (acc : Valuation cs),
      substT σ (owhileIter step n acc) = owhileIter (fun a => substT σ (step a)) n acc := by
  intro n
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
    intro acc
    simp only [owhileIter, substT_obind]
    congr 1
    funext r
    split
    · exact ih _
    · rfl

/-- **The tree of a program depends on the reader and the call environment pointwise.** -/
theorem treeAt_ext {ex ex' : ExprReader E d} {tE tE' : TreeCallEnv E d}
    (hex : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ), ex e V = ex' e V)
    (htE : ∀ f as rs a, tE.call f as rs a = tE'.call f as rs a) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ V : Valuation Γ, treeAt ex tE fuel p V = treeAt ex' tE' fuel p V := by
  induction p with
  | ret vs => intro V; rfl
  | var e k ih => intro V; simp only [treeAt, hex, ih]
  | forLoop count inits body k ihb ihk => intro V; simp only [treeAt, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk => intro V; simp only [treeAt, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk => intro V; simp only [treeAt, ihb, ihk]
  | call f args k ih => intro V; simp only [treeAt, htE, ih]

/-- **Substitution in the tree of a program** is the tree at the substituted reader and call
    environment. -/
theorem substT_treeAt {E' : EventSig} (σ : ∀ e : E.Event, CallTree E' (E.Resp e))
    (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) :
    ∀ V : Valuation Γ, substT σ (treeAt ex tE fuel p V) =
      treeAt (fun e V => substT σ (ex e V)) ⟨fun f as rs a => substT σ (tE.call f as rs a)⟩
        fuel p V := by
  induction p with
  | ret vs => intro V; rfl
  | var e k ih => intro V; simp only [treeAt, substT_obind, ih]
  | forLoop count inits body k ihb ihk =>
    intro V; simp only [treeAt, substT_obind, substT_ofoldl, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
    intro V
    simp only [treeAt, substT_obind, ihk]
    congr 1
    split
    · exact iht V
    · exact ihe V
  | whileLoop inits body k ihb ihk =>
    intro V; simp only [treeAt, substT_obind, substT_owhileIter, ihb, ihk]
  | call f args k ih => intro V; simp only [treeAt, substT_obind, ih]

/-! ## The splice at the tree level -/

/-- **The tree of a splice**: when `seq? k b ρ θ = some q`, `ρ` relates `U` to `W` and `θ`
    relates `V₀` to `W`, the tree of `q` at `W` is the tree of `b` at `U` followed by the tree
    of `k` at its results and `V₀`. -/
theorem treeAt_seq? {ex : ExprReader E d} (hex : ex.RenameInv) (tE : TreeCallEnv E d)
    (fuel : Nat) {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts} {U : Valuation Δ}
      {V₀ : Valuation Γ₀} {W : Valuation Γ}, NFProg.seq? k b ρ θ = some q →
      PRen.Agrees ρ U W → PRen.Agrees θ V₀ W →
      treeAt ex tE fuel q W =
        obind (treeAt ex tE fuel b U) fun r => treeAt ex tE fuel k (hvAppend r V₀) := by
  induction b with
  | ret vs =>
    intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ
    simp only [NFProg.seq?, Option.bind_eq_some_iff] at hq
    obtain ⟨ws, hws, hq⟩ := hq
    rw [treeAt_rename? hex tE fuel k hq (PRen.agrees_appendVars hθ ws),
      PRen.lookupArgs_vars? hρ vs hws]
    rfl
  | var e b ih =>
    intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ
    simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨e', he, b', hb, rfl⟩ := hq
    simp only [treeAt, hex e hρ he, obind_assoc]
    congr 1
    funext x
    exact ih k hb (PRen.agrees_lift hρ x) (PRen.agrees_shift hθ _ (.cons x .nil))
  | forLoop count inits body b _ ih =>
    intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ
    simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨c', hc, i', hi, body', hbody', b', hb, rfl⟩ := hq
    simp only [treeAt, hρ count c' hc, PRen.lookupArgs_vars? hρ inits hi, obind_assoc]
    have hfold : (fun acc i => treeAt ex tE fuel body'
          (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) W))) =
        (fun acc i => treeAt ex tE fuel body
          (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) U))) := by
      funext acc i
      exact treeAt_rename? hex tE fuel body hbody'
        (PRen.agrees_liftApp (PRen.agrees_lift hρ _) _ acc)
    rw [hfold]
    congr 1
    funext acc
    exact ih k hb (PRen.agrees_liftApp hρ _ acc) (PRen.agrees_shift hθ _ acc)
  | ifThenElse cond thn els b _ _ ih =>
    intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ
    simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨c', hc, t', ht, e', he, b', hb, rfl⟩ := hq
    simp only [treeAt, hρ cond c' hc, treeAt_rename? hex tE fuel thn ht hρ,
      treeAt_rename? hex tE fuel els he hρ, obind_assoc]
    congr 1
    funext r
    exact ih k hb (PRen.agrees_liftApp hρ _ r) (PRen.agrees_shift hθ _ r)
  | whileLoop inits body b _ ih =>
    intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ
    simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨i', hi, body', hbody', b', hb, rfl⟩ := hq
    simp only [treeAt, PRen.lookupArgs_vars? hρ inits hi, obind_assoc]
    have hstep : (fun acc => treeAt ex tE fuel body' (hvAppend acc W)) =
        (fun acc => treeAt ex tE fuel body (hvAppend acc U)) := by
      funext acc
      exact treeAt_rename? hex tE fuel body hbody' (PRen.agrees_liftApp hρ _ acc)
    rw [hstep]
    congr 1
    funext acc
    exact ih k hb (PRen.agrees_liftApp hρ _ acc) (PRen.agrees_shift hθ _ acc)
  | call f args b ih =>
    intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ
    simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨a', ha, b', hb, rfl⟩ := hq
    simp only [treeAt, PRen.lookupArgs_vars? hρ args ha, obind_assoc]
    congr 1
    funext r
    exact ih k hb (PRen.agrees_liftApp hρ _ r) (PRen.agrees_shift hθ _ r)

/-! ## The reader and the call environment of a library -/

/-- The tree of an expression at the library `L`: the tree of the body of its operation at its
    argument values, read at its single result, where `L` has a body; the tree of `ex`
    otherwise. -/
def inlineReader (L : InlineLib d) (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat) :
    {Γ : Ctxt d} → {t : d.Ty} → Expr d Γ t → Valuation Γ → CallTree E (Option ⟦t⟧)
  | _, _, ⟨o, rfl, args⟩, V =>
    match L.op o with
    | some b => obind (treeAt ex tE fuel b (Expr.lookupArgs args V)) fun r => .ret (some r.head)
    | none => ex ⟨o, rfl, args⟩ V

/-- The call environment of the library `L`: a call runs the tree of its body where `L` has
    one, and the tree of `tE` otherwise. -/
def inlineEnv (L : InlineLib d) (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat) :
    TreeCallEnv E d :=
  ⟨fun f as rs a =>
    match L.call f as rs with
    | some b => treeAt ex tE fuel b a
    | none => tE.call f as rs a⟩

/-- **The tree of an inlined program.** At a reader invariant under renaming, when
    `inline? L p = some p'`, the tree of `p'` at `ex` and `tE` is the tree of `p` at the reader
    and the call environment of `L`, which run the trees of the bodies at `ex` and `tE`. The
    statement is an equality and needs no soundness of `L`: inlining is exactly the
    substitution of the trees of the bodies for the inlined calls and operations. -/
theorem treeAt_inline? {L : InlineLib d} {ex : ExprReader E d} (hex : ex.RenameInv)
    (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts}, NFProg.inline? L p = some p' → ∀ V : Valuation Γ,
      treeAt ex tE fuel p' V =
        treeAt (inlineReader L ex tE fuel) (inlineEnv L ex tE fuel) fuel p V := by
  induction p with
  | ret vs =>
    intro p' hq V
    cases hq
    rfl
  | var e k ih =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff] at hq
    obtain ⟨k', hk', hq⟩ := hq
    obtain ⟨o, rfl, args⟩ := e
    simp only [NFProg.inlineVar] at hq
    split at hq
    · rename_i b hb
      rw [treeAt_seq? hex tE fuel b k' hq (PRen.agrees_ofArgs V args) (PRen.agrees_id V)]
      simp only [treeAt, inlineReader, hb, obind_assoc]
      congr 1
      funext r
      cases r with
      | cons x r =>
        cases r
        exact ih hk' _
    · cases hq
      simp only [treeAt, inlineReader, ‹L.op o = none›]
      congr 1
      funext x
      exact ih hk' _
  | forLoop count inits body k ihb ihk =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨b', hb', k', hk', rfl⟩ := hq
    simp only [treeAt, ihb hb', ihk hk']
  | ifThenElse cond thn els k iht ihe ihk =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨t', ht', e', he', k', hk', rfl⟩ := hq
    simp only [treeAt, iht ht', ihe he', ihk hk']
  | whileLoop inits body k ihb ihk =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨b', hb', k', hk', rfl⟩ := hq
    simp only [treeAt, ihb hb', ihk hk']
  | call f args k ih =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff] at hq
    obtain ⟨k', hk', hq⟩ := hq
    split at hq
    · rename_i b hb
      rw [treeAt_seq? hex tE fuel b k' hq (PRen.agrees_ofArgs V args) (PRen.agrees_id V)]
      simp only [treeAt, inlineEnv, hb]
      congr 1
      funext r
      exact ih hk' _
    · cases hq
      simp only [treeAt, inlineEnv, ‹L.call f _ _ = none›]
      congr 1
      funext r
      exact ih hk' _

/-! ## Refinement under a sound library -/

/-- **Refined readers and call environments give a refined tree**: when every tree of `ex` is
    refined by the tree of `ex'` and every call tree of `tE` by the one of `tE'`, the tree of a
    program at `ex` and `tE` is refined by its tree at `ex'` and `tE'`. -/
theorem RefinesT.treeAt (h₁ : ∀ e : E.Event, E.Resp e) {ex ex' : ExprReader E d}
    {tE tE' : TreeCallEnv E d}
    (hex : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      RefinesT h₁ (ex e V) (ex' e V))
    (htE : ∀ f as rs a, RefinesT h₁ (tE.call f as rs a) (tE'.call f as rs a)) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ V : Valuation Γ, RefinesT h₁ (NFProgCallTree.treeAt ex tE fuel p V)
      (NFProgCallTree.treeAt ex' tE' fuel p V) := by
  induction p with
  | ret vs => intro V; exact RefinesT.refl _
  | var e k ih => intro V; exact RefinesT.obind (hex e V) fun _ => ih _
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
  | call f args k ih => intro V; exact RefinesT.obind (htE _ _ _ _) fun _ => ih _

/-- **A library is sound for trees** at the source handler `h₁`, the reader `ex`, the call
    environment `tE` and the fuel `fuel`: the tree of an expression of an operation the library
    has a body for is refined by the tree of the body at its argument values, read at its
    result, and the tree of a call the library has a body for is refined by the tree of the
    body at the argument values. The trees of the bodies are taken at `ex` and `tE` because
    `inline?` keeps the inlined bodies as they are. This is the tree form of
    `InlineLib.Sound`: a successful source run of the call is a run of the body with the same
    events and result. -/
structure _root_.CatCrypt.Crypto.SecureCompilation.VIR.InlineLib.TreeSound
    (h₁ : ∀ e : E.Event, E.Resp e) (L : InlineLib d) (ex : ExprReader E d)
    (tE : TreeCallEnv E d) (fuel : Nat) : Prop where
  /-- The tree of the body of an operation refines the tree of its expression. -/
  op : ∀ (o : d.Op) b, L.op o = some b → ∀ {Γ : Ctxt d}
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig o)) (V : Valuation Γ),
    RefinesT h₁ (ex ⟨o, rfl, args⟩ V)
      (obind (NFProgCallTree.treeAt ex tE fuel b (Expr.lookupArgs args V))
        fun r => .ret (some r.head))
  /-- The tree of the body of a symbol refines the tree of its call. -/
  call : ∀ f as rs b, L.call f as rs = some b → ∀ a,
    RefinesT h₁ (tE.call f as rs a) (NFProgCallTree.treeAt ex tE fuel b a)

/-- **Inlining refines the tree** under a library sound for trees: the tree of `p` is refined
    by the tree of `inline? L p`, up to skipped source events. -/
theorem refinesT_treeAt_inline? {h₁ : ∀ e : E.Event, E.Resp e} {L : InlineLib d}
    {ex : ExprReader E d} (hex : ex.RenameInv) {tE : TreeCallEnv E d} {fuel : Nat}
    (hL : L.TreeSound h₁ ex tE fuel) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    {p' : NFProg d Γ ts} (hq : NFProg.inline? L p = some p') (V : Valuation Γ) :
    RefinesT h₁ (NFProgCallTree.treeAt ex tE fuel p V)
      (NFProgCallTree.treeAt ex tE fuel p' V) := by
  rw [treeAt_inline? hex tE fuel p hq]
  refine RefinesT.treeAt h₁ ?_ ?_ fuel p V
  · intro Γ t e V
    obtain ⟨o, rfl, args⟩ := e
    simp only [inlineReader]
    split
    · exact hL.op o _ ‹_› args V
    · exact RefinesT.refl _
  · intro f as rs a
    simp only [inlineEnv]
    split
    · exact hL.call f as rs _ ‹_› a
    · exact RefinesT.refl _

/-- **Repeated inlining refines the tree** under a library sound for trees. -/
theorem refinesT_treeAt_inlineIter {h₁ : ∀ e : E.Event, E.Resp e} {L : InlineLib d}
    {ex : ExprReader E d} (hex : ex.RenameInv) {tE : TreeCallEnv E d} {fuel : Nat}
    (hL : L.TreeSound h₁ ex tE fuel) {Γ : Ctxt d} {ts : List d.Ty} :
    ∀ (n : Nat) (p : NFProg d Γ ts) (V : Valuation Γ),
      RefinesT h₁ (NFProgCallTree.treeAt ex tE fuel p V)
        (NFProgCallTree.treeAt ex tE fuel (NFProg.inlineIter L n p) V)
  | 0, p, V => RefinesT.refl _
  | n + 1, p, V => by
    simp only [NFProg.inlineIter]
    split
    · rename_i q hq
      exact (refinesT_treeAt_inline? hex hL p hq V).trans
        (refinesT_treeAt_inlineIter hex hL n q V)
    · exact RefinesT.refl _

/-! ## The inlined call tree as a substitution -/

variable [DialectDenoteM d Option]

/-- The substitution of the trees of the bodies of the library `L` for the call events: a call
    the library has a body for runs the call tree of the body at its argument values, every
    other call is kept as its event. -/
def inlineSubst (L : InlineLib d) (fuel : Nat) :
    ∀ c : (nfCallSig d).Event, CallTree (nfCallSig d) ((nfCallSig d).Resp c) :=
  fun c => (inlineEnv L pureReader eventEnv fuel).call c.name c.argTys c.resTys c.args

/-- **The inlined call tree is a substitution of the call tree**: for a library without bodies
    of operations, the call tree of `inline? L p` is the call tree of `p` in which every call
    the library has a body for is replaced by the call tree of the body. With `RuttS.substT`,
    a relation of the call trees of `p` transfers to the inlined program. -/
theorem nfProgTree_inline? {L : InlineLib d} (hL : ∀ o, L.op o = none) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) {p' : NFProg d Γ ts}
    (hq : NFProg.inline? L p = some p') (V : Valuation Γ) :
    nfProgTree fuel p' V = substT (inlineSubst L fuel) (nfProgTree fuel p V) := by
  unfold nfProgTree
  rw [treeAt_inline? pureReader_renameInv eventEnv fuel p hq, substT_treeAt]
  refine treeAt_ext ?_ ?_ fuel p V
  · intro Γ t e V
    obtain ⟨o, rfl, args⟩ := e
    simp only [inlineReader, hL]
    rfl
  · intro f as rs a
    exact (NFCallTreeAnfPick.bind_ret _).symm

/-- The substituted tree of a call interprets under the handler of `Ec` to the run of the body
    at `Ec` where the library has one, and to the callee of `Ec` otherwise. This is the
    consistency hypothesis of `RuttS.substT` for `inlineSubst`. -/
theorem interp_inlineSubst (Ec : CallEnv d) (L : InlineLib d) (fuel : Nat)
    (c : (nfCallSig d).Event) :
    interp (callHandler Ec) (inlineSubst L fuel c) =
      match L.call c.name c.argTys c.resTys with
      | some b => b.denoteAt Ec fuel c.args
      | none => callHandler Ec c := by
  simp only [inlineSubst, inlineEnv]
  cases L.call c.name c.argTys c.resTys with
  | none => rfl
  | some b => exact interp_nfProgTree Ec fuel b c.args

end Tree

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInline
