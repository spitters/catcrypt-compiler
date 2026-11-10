/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFMontifyHint
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep

/-!
# The Montgomery rewriter at the level of call trees

From the step `montifyStep` on, a call of a field head (`fieldHeadB`) or of a reduce-multiply
head (`NFMontify.montTag?`) is no call of a linked function: the chain inlines it as a block of
let-bindings. The rewriter `NFMontify.montify` replaces a field multiplication by a call of a
reduce-multiply head on other arguments and adds reduce-multiply calls that convert a word
between degrees. In the call tree `nfProgTree`, in which every call is an event, these are
target events without a source event, which `RuttS` does not relate. This module reads such a
call inside the tree: the tree call environment `mfEnv` answers a field head or a
reduce-multiply head by the leaf of its value at `montEnv (fieldEnv E)`, and makes every other
call one event. Under the handler of `E` the tree interprets to `denoteAt` at
`montEnv (fieldEnv E)` (`interp_mfTree`), and the tree with every call an event refines it at a
source handler that answers the inner heads by their values (`refinesT_nfProgTree_mfTree`).

At `mfEnv` the rewriter keeps the events, their arguments and the returned values: the call
tree of the rewritten program refines the call tree of the source program
(`refinesT_montify`). The proof follows `NFMontify.montifyAux_leakSound` clause by clause, with
equalities of trees in place of equalities of leakage runs. The inlining of the
reduce-multiply heads keeps the tree (`treeAt_inline?`), so the montify step refines the tree at
`mfEnv` (`refinesT_montifyStep`). The field dialect step inlines each field call by a body
without `call`, whose tree at `mfEnv` is the leaf of the value of the call whenever the call
answers; it refines the tree at `mfEnv` as well (`refinesT_fieldDialectStep`).

## Main definitions

* `innerHead`, `mfEnv`, `mfTree`: the heads answered inside the tree, the tree call
  environment, and the call tree of a program of `jasminDialect` at it.

## Main results

* `interp_mfTree`: adequacy of `mfTree` for `denoteAt` at `montEnv (fieldEnv E)`.
* `refinesT_nfProgTree_mfTree`: the tree with every call an event refines `mfTree`.
* `obind_assoc`, `treeAt_seq?`, `treeAt_inline?`, `treeAt_ofCom`: associativity of `obind`, the
  tree of a splice, inlining at a library whose bodies have the trees of their calls, and the
  tree of a straight-line program.
* `convProg_mfTree`: a conversion has the tree of its continuation.
* `montifyAux_refinesT`, `entryConv_refinesT`, `refinesT_montify`: the stage lemma of the
  rewriter at the tree level.
* `refinesT_montifyAt`, `refinesT_montifyStep`, `refinesT_nfProgTree_montifyStep`: the stage
  lemma of `montifyStep` at `mfEnv`, and from the tree with every call an event.
* `refinesT_inline?`, `treeAt_ret_of_callFree`: inlining at a library whose bodies refine the
  trees of their calls refines the tree; a program without `call` has a leaf as its tree.
* `refinesT_fieldBodyD`, `refinesT_fieldDialectStep`: the stage lemma of `fieldDialectStep` at
  `mfEnv`: a field call is a leaf there, and its lowered body a leaf with the same value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (canonEnc w64)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32 (mont32Cert)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.MontDeg (encK redcMulW)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (eConst)
open _root_.Hax.FieldTag (fieldTag? fieldHeadB)
open Ctxt (Var Valuation)

/-! ## The tree with the field and reduce-multiply heads answered inside -/

/-- A head answered inside the call tree: a reduce-multiply head or a field head. -/
def innerHead (f : String) : Bool := (montTag? f).isSome || fieldHeadB f

/-- **The tree call environment of the field and reduce-multiply heads**: an inner head is the
    leaf of its value at `montEnv (fieldEnv CallEnv.empty)`, every other call one event. -/
def mfEnv : TreeCallEnv (nfCallSig jasminDialect) jasminDialect :=
  ⟨fun f as rs a =>
    if innerHead f then .ret ((montEnv (fieldEnv CallEnv.empty)).call f as rs a)
    else .vis (⟨f, as, rs, a⟩ : NFCall jasminDialect) fun r => .ret r⟩

/-- The call tree of a program of `jasminDialect` at `mfEnv`. -/
def mfTree (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    CallTree (nfCallSig jasminDialect) (Option (Valuation (d := jasminDialect) ts)) :=
  treeAt pureReader mfEnv fuel p V

/-- At an inner head, `montEnv (fieldEnv E)` does not depend on `E`. -/
theorem montEnv_fieldEnv_inner {f : String} (hf : innerHead f = true)
    (E E' : CallEnv jasminDialect) (as rs : List JasminTy)
    (x : Valuation (d := jasminDialect) as) :
    (montEnv (fieldEnv E)).call f as rs x = (montEnv (fieldEnv E')).call f as rs x := by
  cases hm : montTag? f with
  | some q => simp only [montEnv, hm]
  | none =>
    have hb : fieldHeadB f = true := by simpa [innerHead, hm] using hf
    simp only [montEnv, hm, fieldEnv_of_fieldHeadB _ hb]

/-- At a head that is not inner, `montEnv (fieldEnv E)` is `E`. -/
theorem montEnv_fieldEnv_outer {f : String} (hf : innerHead f = false)
    (E : CallEnv jasminDialect) (as rs : List JasminTy)
    (x : Valuation (d := jasminDialect) as) :
    (montEnv (fieldEnv E)).call f as rs x = E.call f as rs x := by
  simp only [innerHead, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hf
  rw [montEnv_of_none _ hf.1, fieldEnv_of_none _ hf.2]

/-- **Adequacy of `mfTree`**: under the handler of `E`, the tree interprets to `denoteAt` at
    `montEnv (fieldEnv E)`. -/
theorem interp_mfTree (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    interp (callHandler E) (mfTree fuel p V) = p.denoteAt (montEnv (fieldEnv E)) fuel V := by
  have hE : mfEnv.interpEnv (callHandler E) = montEnv (fieldEnv E) := by
    change (⟨_⟩ : CallEnv jasminDialect) = ⟨(montEnv (fieldEnv E)).call⟩
    congr 1
    funext f as rs x
    by_cases hf : innerHead f = true
    · simp only [mfEnv, hf, ite_true]
      exact montEnv_fieldEnv_inner hf _ _ as rs x
    · simp only [mfEnv, hf]
      exact (montEnv_fieldEnv_outer (by simpa using hf) E as rs x).symm
  rw [mfTree, interp_treeAt _ _ (fun _ _ => rfl), hE]

/-- **The tree with every call an event refines `mfTree`**, at a source handler that answers
    each inner head by its value: an event of an inner head is skipped. -/
theorem refinesT_nfProgTree_mfTree (h₁ : ∀ e : (nfCallSig jasminDialect).Event,
      (nfCallSig jasminDialect).Resp e)
    (hh : ∀ (f : String) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₁ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ V : Valuation Γ, RefinesT h₁ (nfProgTree fuel p V) (mfTree fuel p V) := by
  induction p with
  | ret vs => intro V; exact RefinesT.refl _
  | var e k ih => intro V; exact RefinesT.obind (RefinesT.refl _) fun _ => ih _
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
    by_cases hf : innerHead f = true
    · simp only [nfProgTree, mfTree, treeAt, eventEnv, mfEnv, hf, ite_true]
      unfold obind
      refine RuttS.skip_bind _ ?_
      simp only [interp, hh f _ _ _ hf]
      cases (montEnv (fieldEnv CallEnv.empty)).call f _ _ (Expr.lookupArgs args V) with
      | none => exact .ret rfl
      | some r => exact ih _
    · simp only [nfProgTree, mfTree, treeAt, eventEnv, mfEnv, hf, Bool.false_eq_true,
        ite_false]
      exact RefinesT.obind (RefinesT.refl _) fun _ => ih _

/-- A `call` of an inner head has the tree of its continuation at the value of the head. -/
theorem mfTree_call_inner (fuel : Nat) {Γ : Ctxt jasminDialect} {as rs ts : List JasminTy}
    {g : String} (hg : innerHead g = true) (args : HVector (fun t => Var Γ t) as)
    (k : NFProg jasminDialect (rs ++ Γ) ts) (W : Valuation Γ) :
    mfTree fuel (NFProg.call g args k) W =
      obind (.ret ((montEnv (fieldEnv CallEnv.empty)).call g as rs (Expr.lookupArgs args W)))
        fun r => mfTree fuel k (hvAppend r W) := by
  simp only [mfTree, treeAt, mfEnv, hg, ite_true]

/-! ## Splicing and inlining at the tree level -/

section Inline

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- Sequencing of trees of optional results is associative. -/
theorem obind_assoc {α β γ : Type} (t : CallTree E (Option α))
    (k₁ : α → CallTree E (Option β)) (k₂ : β → CallTree E (Option γ)) :
    obind (obind t k₁) k₂ = obind t fun a => obind (k₁ a) k₂ := by
  induction t with
  | ret o => cases o <;> rfl
  | vis e c ih => exact congrArg (CallTree.vis e) (funext ih)

/-- **The tree of a splice**: when `ρ` relates `U` to `W` and `θ` relates `V₀` to `W`, the
    splice `seq? k b ρ θ` has at `W` the tree of `b` at `U` followed by the tree of `k` at its
    results and `V₀`. -/
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

/-- **Inlining keeps the tree**: at a library without operation bodies whose body of each
    symbol has the tree of its call in `tE`, the inlined program has the tree of the source
    program, at every valuation. -/
theorem treeAt_inline? {ex : ExprReader E d} (hex : ex.RenameInv) (tE : TreeCallEnv E d)
    (fuel : Nat) {L : InlineLib d} (hop : ∀ o, L.op o = none)
    (hcall : ∀ f as rs b, L.call f as rs = some b →
      ∀ x, treeAt ex tE fuel b x = tE.call f as rs x)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts}, NFProg.inline? L p = some p' →
      ∀ V, treeAt ex tE fuel p' V = treeAt ex tE fuel p V := by
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
    simp only [NFProg.inlineVar, hop, Option.some.injEq] at hq
    subst hq
    simp only [treeAt, ih hk']
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
      rw [treeAt_seq? hex tE fuel b k' hq (PRen.agrees_ofArgs V args) (PRen.agrees_id V),
        hcall f _ _ b hb]
      simp only [treeAt, ih hk']
    · cases hq
      simp only [treeAt, ih hk']

/-- The tree of a straight-line program at the pure reader is the leaf of its value. -/
theorem treeAt_ofCom [DialectDenote d] (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d}
    {t : d.Ty} (c : Com d Γ t) (V : Valuation Γ) :
    treeAt pureReader tE fuel (NFProg.ofCom c) V = .ret (some (.cons (c.denote V) .nil)) := by
  induction c with
  | ret v => rfl
  | var e k ih =>
    simp only [NFProg.ofCom, treeAt, pureReader, Expr.denoteM_option_eq_some]
    exact ih _

/-- **Inlining refines the tree**: at a library without operation bodies whose body of each
    symbol refines the tree of its call in `tE`, the tree of the inlined program refines the
    tree of the source program, at every valuation. -/
theorem refinesT_inline? {ex : ExprReader E d} (hex : ex.RenameInv) (tE : TreeCallEnv E d)
    (fuel : Nat) (h₁ : ∀ e : E.Event, E.Resp e) {L : InlineLib d} (hop : ∀ o, L.op o = none)
    (hcall : ∀ f as rs b, L.call f as rs = some b →
      ∀ x, RefinesT h₁ (tE.call f as rs x) (treeAt ex tE fuel b x))
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts}, NFProg.inline? L p = some p' →
      ∀ V, RefinesT h₁ (treeAt ex tE fuel p V) (treeAt ex tE fuel p' V) := by
  induction p with
  | ret vs =>
    intro p' hq V
    cases hq
    exact RefinesT.refl _
  | var e k ih =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff] at hq
    obtain ⟨k', hk', hq⟩ := hq
    obtain ⟨o, rfl, args⟩ := e
    simp only [NFProg.inlineVar, hop, Option.some.injEq] at hq
    subst hq
    exact RefinesT.obind (RefinesT.refl _) fun _ => ih hk' _
  | forLoop count inits body k ihb ihk =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨b', hb', k', hk', rfl⟩ := hq
    exact RefinesT.obind (RefinesT.ofoldl (fun _ _ => ihb hb' _) _ _) fun _ => ihk hk' _
  | ifThenElse cond thn els k iht ihe ihk =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨t', ht', e', he', k', hk', rfl⟩ := hq
    refine RefinesT.obind ?_ fun _ => ihk hk' _
    split
    · exact iht ht' V
    · exact ihe he' V
  | whileLoop inits body k ihb ihk =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨b', hb', k', hk', rfl⟩ := hq
    exact RefinesT.obind (RefinesT.owhileIter (fun _ => ihb hb' _) _ _) fun _ => ihk hk' _
  | call f args k ih =>
    intro p' hq V
    simp only [NFProg.inline?, Option.bind_eq_some_iff] at hq
    obtain ⟨k', hk', hq⟩ := hq
    split at hq
    · rename_i b hb
      rw [treeAt_seq? hex tE fuel b k' hq (PRen.agrees_ofArgs V args) (PRen.agrees_id V)]
      exact RefinesT.obind (hcall f _ _ b hb _) fun _ => ih hk' _
    · cases hq
      exact RefinesT.obind (RefinesT.refl _) fun _ => ih hk' _

/-- A program without `call` calls no symbol. -/
theorem not_calls_of_callFree {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.callFree = true) {f : String} {as rs : List d.Ty} (hc : p.Calls f as rs) : False := by
  induction p with
  | ret => exact hc.elim
  | var e k ih => exact ih hp hc
  | forLoop _ _ _ _ ihb ihk =>
    simp only [NFProg.callFree, Bool.and_eq_true] at hp
    rcases hc with h | h
    exacts [ihb hp.1 h, ihk hp.2 h]
  | ifThenElse _ _ _ _ iht ihe ihk =>
    simp only [NFProg.callFree, Bool.and_eq_true] at hp
    rcases hc with h | h | h
    exacts [iht hp.1.1 h, ihe hp.1.2 h, ihk hp.2 h]
  | whileLoop _ _ _ ihb ihk =>
    simp only [NFProg.callFree, Bool.and_eq_true] at hp
    rcases hc with h | h
    exacts [ihb hp.1 h, ihk hp.2 h]
  | call _ _ _ _ => simp [NFProg.callFree] at hp

/-- `obind` of a leaf and continuations that are leaves is a leaf. -/
theorem obind_ret_of {α β : Type} {t : CallTree E (Option α)} {k : α → CallTree E (Option β)}
    (ht : ∃ o, t = .ret o) (hk : ∀ a, ∃ o, k a = .ret o) : ∃ o, obind t k = .ret o := by
  obtain ⟨o, rfl⟩ := ht
  cases o with
  | none => exact ⟨none, rfl⟩
  | some a => exact hk a

/-- A fold of steps that are leaves is a leaf. -/
theorem ofoldl_ret_of {α β : Type} {f : β → α → CallTree E (Option β)}
    (hf : ∀ b a, ∃ o, f b a = .ret o) : ∀ (l : List α) (b : β), ∃ o, ofoldl f l b = .ret o
  | [], _ => ⟨_, rfl⟩
  | a :: l, b => obind_ret_of (hf b a) fun b' => ofoldl_ret_of hf l b'

omit [DialectSignature d] [HasWord64 d] in
/-- An exit-flag iteration of a body that is a leaf is a leaf. -/
theorem owhileIter_ret_of {cs : List d.Ty}
    {s : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))}
    (hs : ∀ a, ∃ o, s a = .ret o) : ∀ (n : Nat) (a : Valuation cs),
      ∃ o, NFProgCallTree.owhileIter s n a = .ret o
  | 0, _ => ⟨_, rfl⟩
  | n + 1, a => obind_ret_of (hs a) fun r => by
      split
      · exact owhileIter_ret_of hs n _
      · exact ⟨_, rfl⟩

/-- **The tree of a program without `call` is a leaf** at the pure reader. -/
theorem treeAt_ret_of_callFree [DialectDenoteM d Option] (tE : TreeCallEnv E d) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.callFree = true) :
    ∀ V, ∃ o, treeAt pureReader tE fuel p V = .ret o := by
  induction p with
  | ret vs => exact fun _ => ⟨_, rfl⟩
  | var e k ih => exact fun V => obind_ret_of ⟨_, rfl⟩ fun _ => ih hp _
  | forLoop _ _ _ _ ihb ihk =>
    simp only [NFProg.callFree, Bool.and_eq_true] at hp
    exact fun V => obind_ret_of (ofoldl_ret_of (fun _ _ => ihb hp.1 _) _ _) fun _ => ihk hp.2 _
  | ifThenElse _ _ _ _ iht ihe ihk =>
    simp only [NFProg.callFree, Bool.and_eq_true] at hp
    intro V
    refine obind_ret_of ?_ fun _ => ihk hp.2 _
    split
    · exact iht hp.1.1 V
    · exact ihe hp.1.2 V
  | whileLoop _ _ _ ihb ihk =>
    simp only [NFProg.callFree, Bool.and_eq_true] at hp
    exact fun V => obind_ret_of (owhileIter_ret_of (fun _ => ihb hp.1 _) _ _) fun _ => ihk hp.2 _
  | call _ _ _ _ => simp [NFProg.callFree] at hp

end Inline

/-! ## The rewriter -/

section Montify

variable {p : Nat} (h : mont32Cert p = true) (hm : montTag? (montHead p) = some p) (fuel : Nat)

include hm in
/-- **A conversion has the tree of its continuation** at the converted word and the
    constant. -/
theorem convProg_mfTree {Θ : Ctxt jasminDialect} (x : Var Θ w64) (j : ℤ) {us : List JasminTy}
    (k : NFProg jasminDialect (w64 :: w64 :: Θ) us) (W : Valuation Θ) :
    mfTree fuel (convProg h x j k) W =
      mfTree fuel k (.cons (redcMulW p (x.lookup W) (BitVec.ofNat 64 (convC h j)))
        (.cons (BitVec.ofNat 64 (convC h j)) W)) := by
  have hi : innerHead (montHead p) = true := by simp [innerHead, hm]
  unfold convProg
  simp only [mfTree, treeAt, pureReader, Expr.denoteM_option_eq_some, mfEnv, hi, ite_true]
  change obind (.ret ((montEnv (fieldEnv CallEnv.empty)).call (montHead p) [w64, w64] [w64]
      (.cons (x.lookup W) (.cons (BitVec.ofNat 64 (convC h j)) .nil))))
    (fun r => mfTree fuel k (hvAppend r (.cons (BitVec.ofNat 64 (convC h j)) W))) = _
  rw [montEnv_montHead _ hm]
  rfl

/-- The conclusion of the tree lemma of a binding: an extension of the rewritten valuation that
    keeps every lookup, a reading of the bound value related to it, and a program of the
    continuation with the tree of the rewritten program. -/
def BindOkT {Θ : Ctxt jasminDialect} {t : JasminTy} {us : List JasminTy} (W : Valuation Θ)
    (x : ⟦t⟧) (kk : BindK Θ t us) (q : NFProg jasminDialect Θ us) : Prop :=
  ∃ (Θ' : Ctxt jasminDialect) (g : Ctxt.Hom Θ Θ') (r : Rd Θ' t) (W' : Valuation Θ')
    (q' : NFProg jasminDialect Θ' us), Pres g W W' ∧ r.rel h W' x ∧ kk g r = some q' ∧
      mfTree fuel q W = mfTree fuel q' W'

include hm in
/-- The result of a field call at the degree `k`, continued at the degree `d`, keeps the tree
    and is read in relation to the canonical representative of its value. -/
theorem resConv_mfTree {Θ : Ctxt jasminDialect} {us : List JasminTy} (v : Var Θ w64)
    (k d : ℤ) (kk : BindK Θ w64 us) (q : NFProg jasminDialect Θ us)
    (hq : resConv h v k d kk = some q) (W : Valuation Θ) (z : ZMod p)
    (hv : v.lookup W = encK h k z) :
    BindOkT h fuel W (canonEnc p z) kk q := by
  unfold resConv at hq
  split at hq
  · exact ⟨_, fun w => w, rdOf v k, W, q, fun _ => rfl, rdOf_rel h v k z hv, hq, rfl⟩
  · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    refine ⟨_, fun w => .there (.there w), rdOf .here d,
      .cons (redcMulW p (v.lookup W) (BitVec.ofNat 64 (convC h (d - k + 1))))
        (.cons (BitVec.ofNat 64 (convC h (d - k + 1))) W), q', fun _ => rfl, ?_, hq',
      convProg_mfTree h hm fuel v _ q' W⟩
    apply rdOf_rel
    change redcMulW p (v.lookup W) _ = encK h d z
    rw [hv, redcMulW_conv]
    congr 1
    ring

include hm in
/-- A binding continued at the degree `d` keeps the tree and is read in relation to its
    value. -/
theorem varConv_mfTree {Θ : Ctxt jasminDialect} {us : List JasminTy} {t : JasminTy} (d : ℤ)
    (kk : BindK (t :: Θ) t us) (q : NFProg jasminDialect (t :: Θ) us)
    (hq : varConv h d kk = some q) (W : Valuation (t :: Θ)) :
    BindOkT h fuel W (Var.here.lookup W) kk q := by
  unfold varConv at hq
  split at hq
  · exact ⟨_, fun w => w, .same .here, W, q, fun _ => rfl, rfl, hq, rfl⟩
  · cases t with
    | reg w =>
      by_cases hw : w = 64
      · subst hw
        obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
        refine ⟨_, fun w => .there (.there w), .mont .here d,
          .cons (redcMulW p (Var.here.lookup W) (BitVec.ofNat 64 (convC h (d + 1))))
            (.cons (BitVec.ofNat 64 (convC h (d + 1))) W), q', fun _ => rfl, ?_, hq',
          convProg_mfTree h hm fuel .here _ q' W⟩
        intro hx
        have e := redcMulW_conv h 0 (d + 1)
          (((Var.here.lookup W : BitVec 64).toNat : Nat) : ZMod p)
        rw [← word_eq_encK_zero h _ hx, show (0 : ℤ) + (d + 1) - 1 = d by ring] at e
        exact e
      · simp [wordConv, hw] at hq
    | _ => simp [wordConv] at hq

/-- The conclusion of the tree lemma of a call of an inner head with the results `r`: a
    renaming of the source context after the call, agreeing with the extended valuations, at
    which the continuation has a rewritten program with the tree of the rewritten call. -/
def CallOkT {Γ Θ : Ctxt jasminDialect} {rs us : List JasminTy} (X : Valuation Γ)
    (W : Valuation Θ) (r : Valuation (d := jasminDialect) rs) (kk : CallK Γ rs us)
    (q : NFProg jasminDialect Θ us) : Prop :=
  ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen (rs ++ Γ) Θ') (W' : Valuation Θ')
    (q' : NFProg jasminDialect Θ' us), kk ρ' = some q' ∧ MAgree h ρ' (hvAppend r X) W' ∧
      mfTree fuel q W = mfTree fuel q' W'

/-- A program `opaqueArm` returns is the call on the read arguments before a program the
    continuation returns. -/
theorem opaqueArm_some {Γ Θ : Ctxt jasminDialect} {f : String} {as rs us : List JasminTy}
    {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ} {kk : CallK Γ rs us}
    {q : NFProg jasminDialect Θ us} (hq : opaqueArm f args ρ kk = some q) :
    ∃ args' k', sameVars ρ args = some args' ∧ kk (MRen.app ρ rs) = some k' ∧
      q = .call f args' k' := by
  obtain ⟨args', hargs, hq⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
  exact ⟨args', k', hargs, hk', rfl⟩

/-- **A call of a head that is no field head is kept**: `callArm` returns the call on the read
    arguments before a program the continuation returns. -/
theorem callArm_outer {Γ Θ : Ctxt jasminDialect} {f : String} (hi : fieldHeadB f = false)
    {us as rs : List JasminTy} (args : HVector (fun t => Var Γ t) as) (ρ : MRen Γ Θ) (d : ℤ)
    (kk : CallK Γ rs us) (q : NFProg jasminDialect Θ us)
    (hq : callArm h f args ρ d kk = some q) :
    ∃ args' k', sameVars ρ args = some args' ∧ kk (MRen.app ρ rs) = some k' ∧
      q = .call f args' k' := by
  have hft : fieldTag? f = none := (_root_.Hax.FieldTag.fieldHeadB_eq_false_iff.mp hi).1
  unfold callArm at hq
  split at hq
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    simp only [binArm, hft] at hq
    exact opaqueArm_some hq
  · split at hq
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      rcases args with _ | ⟨a, _ | _⟩
      simp only [unArm, hft] at hq
      exact opaqueArm_some hq
    · exact opaqueArm_some hq

/-- A call of a field head that is kept has the tree of its continuation. -/
theorem opaqueArm_mfTree {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    (hi : fieldHeadB f = true) {as rs us : List JasminTy}
    (args : HVector (fun t => Var Γ t) as) {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) (kk : CallK Γ rs us)
    (q : NFProg jasminDialect Θ us) (hq : opaqueArm f args ρ kk = some q)
    (r : Valuation (d := jasminDialect) rs)
    (hr : (fieldEnv CallEnv.empty).call f as rs (Expr.lookupArgs args X) = some r) :
    CallOkT h fuel X W r kk q := by
  obtain ⟨args', k', hargs, hk', rfl⟩ := opaqueArm_some hq
  refine ⟨_, MRen.app ρ rs, hvAppend r W, k', hk', MAgree.app h hA rs r, ?_⟩
  rw [mfTree_call_inner fuel (by simp [innerHead, hi]), montEnv_of_none _ hf,
    sameVars_lookup h hA args args' hargs, hr]
  rfl

include hm in
/-- A field call rewritten to the inner head `g`, whose value is a word at the degree `k`, has
    the tree of its continuation. -/
theorem fieldRes_mfTree {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) (g : String) (hgi : innerHead g = true)
    {as us : List JasminTy} (args : HVector (fun t => Var Θ t) as) (k d : ℤ)
    (kk : CallK Γ [w64] us) (q : NFProg jasminDialect Θ us)
    (hq : fieldRes h ρ g args k d kk = some q) (z : ZMod p)
    (hg : (montEnv (fieldEnv CallEnv.empty)).call g as [w64] (Expr.lookupArgs args W) =
      some (.cons (encK h k z) .nil)) :
    CallOkT h fuel X W (.cons (canonEnc p z) .nil) kk q := by
  obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  obtain ⟨Θ', g', r, W', q', hp, hr, hk, hden⟩ :=
    resConv_mfTree h hm fuel .here k d (resK ρ kk) q0 hq0 (.cons (encK h k z) W) z rfl
  refine ⟨Θ', MRen.lift ρ (fun w => g' (.there w)) r, W', q', hk,
    hA.lift h (g := fun w => g' (.there w)) (fun v => hp (.there v)) r _ hr, ?_⟩
  rw [mfTree_call_inner fuel hgi, hg]
  exact hden

include hm in
/-- A call of a field head with two word arguments has the tree of its continuation. -/
theorem binArm_mfTree {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    (hi : fieldHeadB f = true) (a b : Var Γ w64) {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) (d : ℤ) {us : List JasminTy}
    (kk : CallK Γ [w64] us) (q : NFProg jasminDialect Θ us) (hq : binArm h f a b ρ d kk = some q)
    (r : Valuation (d := jasminDialect) [w64])
    (hr : (fieldEnv CallEnv.empty).call f [w64, w64] [w64]
      (.cons (a.lookup X) (.cons (b.lookup X) .nil)) = some r) :
    CallOkT h fuel X W r kk q := by
  unfold binArm at hq
  split at hq
  · rename_i m q' ht
    split at hq
    · rename_i hc
      obtain ⟨rfl, hbin⟩ := hc
      obtain ⟨ha, hb, rfl⟩ := fieldCall_bin h CallEnv.empty ht hbin _ _ r hr
      have hva := Rd.rel_canon h (ρ a) _ (hA _ a) ha
      have hvb := Rd.rel_canon h (ρ b) _ (hA _ b) hb
      split at hq
      · rename_i hmul
        obtain ⟨rfl, -⟩ := hmul
        refine fieldRes_mfTree h hm fuel hA _ (by simp [innerHead, hm]) _ _ _ kk q hq _ ?_
        change (montEnv (fieldEnv CallEnv.empty)).call (montHead q') [w64, w64] [w64]
          (.cons ((ρ a).var.lookup W) (.cons ((ρ b).var.lookup W) .nil)) = _
        rw [hva, hvb, redcCall h hm]
        rfl
      · split at hq
        · rename_i hkeep
          obtain ⟨hdeg, hlin⟩ := hkeep
          refine fieldRes_mfTree h hm fuel hA _ (by simp [innerHead, hi]) _ _ _ kk q hq _ ?_
          change (montEnv (fieldEnv CallEnv.empty)).call f [w64, w64] [w64]
            (.cons ((ρ a).var.lookup W) (.cons ((ρ b).var.lookup W) .nil)) = _
          rw [hva, hvb, ← hdeg]
          exact keepCall_bin h CallEnv.empty hf ht hbin _ hlin _ _
        · cases hq
    · exact opaqueArm_mfTree h fuel hf hi _ hA kk q hq r hr
  · exact opaqueArm_mfTree h fuel hf hi _ hA kk q hq r hr

include hm in
/-- A call of a field head with one word argument has the tree of its continuation. -/
theorem unArm_mfTree {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    (hi : fieldHeadB f = true) (a : Var Γ w64) {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) (d : ℤ) {us : List JasminTy}
    (kk : CallK Γ [w64] us) (q : NFProg jasminDialect Θ us) (hq : unArm h f a ρ d kk = some q)
    (r : Valuation (d := jasminDialect) [w64])
    (hr : (fieldEnv CallEnv.empty).call f [w64] [w64] (.cons (a.lookup X) .nil) = some r) :
    CallOkT h fuel X W r kk q := by
  unfold unArm at hq
  split at hq
  · rename_i m q' ht
    split at hq
    · rename_i hc
      obtain ⟨rfl, hun⟩ := hc
      obtain ⟨ha, rfl⟩ := fieldCall_un h CallEnv.empty ht hun _ r hr
      have hva := Rd.rel_canon h (ρ a) _ (hA _ a) ha
      split at hq
      · rename_i hsq
        obtain ⟨rfl, -⟩ := hsq
        refine fieldRes_mfTree h hm fuel hA _ (by simp [innerHead, hm]) _ _ _ kk q hq _ ?_
        change (montEnv (fieldEnv CallEnv.empty)).call (montHead q') [w64, w64] [w64]
          (.cons ((ρ a).var.lookup W) (.cons ((ρ a).var.lookup W) .nil)) = _
        rw [hva, redcCall h hm]
        rfl
      · split at hq
        · rename_i hlin
          refine fieldRes_mfTree h hm fuel hA _ (by simp [innerHead, hi]) _ _ _ kk q hq _ ?_
          change (montEnv (fieldEnv CallEnv.empty)).call f [w64] [w64]
            (.cons ((ρ a).var.lookup W) .nil) = _
          rw [hva]
          exact keepCall_un h CallEnv.empty hf ht hun _ hlin _
        · cases hq
    · exact opaqueArm_mfTree h fuel hf hi _ hA kk q hq r hr
  · exact opaqueArm_mfTree h fuel hf hi _ hA kk q hq r hr

include hm in
/-- **A call of a field head has the tree of its continuation**: the rewriter of the call
    returns a program with the tree of the rewritten continuation at a renaming that agrees
    with the results of the source call. -/
theorem callArm_mfTree {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    (hi : fieldHeadB f = true) {us as rs : List JasminTy} (args : HVector (fun t => Var Γ t) as)
    {ρ : MRen Γ Θ} {X : Valuation Γ} {W : Valuation Θ} (hA : MAgree h ρ X W) (d : ℤ)
    (kk : CallK Γ rs us) (q : NFProg jasminDialect Θ us) (hq : callArm h f args ρ d kk = some q)
    (r : Valuation (d := jasminDialect) rs)
    (hr : (fieldEnv CallEnv.empty).call f as rs (Expr.lookupArgs args X) = some r) :
    CallOkT h fuel X W r kk q := by
  unfold callArm at hq
  split at hq
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact binArm_mfTree h hm fuel hf hi a b hA _ kk q hq r hr
  · split at hq
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      rcases args with _ | ⟨a, _ | _⟩
      exact unArm_mfTree h hm fuel hf hi a hA _ kk q hq r hr
    · exact opaqueArm_mfTree h fuel hf hi _ hA kk q hq r hr

variable (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)

include hm in
/-- **The rewriter keeps the call tree up to refinement.** For a program `prog` rewritten from
    the renaming `ρ` and valuations `X`, `W` that agree along `ρ`, the tree of the rewritten
    program at `W` refines the tree of `prog` at `X`, at every source handler: each event is
    the source event with the same arguments, and each returned value the source value. -/
theorem montifyAux_refinesT :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
      (H : DegHint) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) (q : NFProg jasminDialect Θ ts),
      montifyAux h prog H ρ = some q → ∀ (X : Valuation Γ) (W : Valuation Θ),
        MAgree h ρ X W → RefinesT h₁ (mfTree fuel prog X) (mfTree fuel q W)
  | _, _, .ret vs, _, _, ρ, q, hq, X, W, hA => by
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [mfTree, treeAt]
      rw [sameVars_lookup h hA vs ws hws]
      exact RefinesT.refl _
  | _, _, .var e k, H, _, ρ, q, hq, X, W, hA => by
      obtain ⟨e', he, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [mfTree, treeAt, pureReader]
      rw [renExpr_denoteM h hA e e' he]
      cases e.denoteM (M := Option) X with
      | none => exact .ret rfl
      | some x =>
        obtain ⟨Θ', g, r, W', q', hp, hr, hk, hden⟩ :=
          varConv_mfTree h hm fuel H.deg _ q0 hq0 (W.extend x)
        change RefinesT h₁ (mfTree fuel k (X.extend x)) (mfTree fuel q0 (W.extend x))
        rw [hden]
        exact montifyAux_refinesT k H.next _ q' hk (X.extend x) W'
          (hA.lift h (g := fun w => g (.there w)) (fun v => hp (.there v)) r x hr)
  | _, _, .forLoop (cs := cs) count inits body k, H, _, ρ, q, hq, X, W, hA => by
      obtain ⟨c, hc, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨ivs, hivs, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      have hcnt : c.lookup W = count.lookup X := by
        have h0 : (ρ count).rel h W (count.lookup X) := hA _ count
        have e : ρ count = .same c := Rd.eq_of_same? hc
        rw [e] at h0
        exact h0
      simp only [mfTree, treeAt]
      rw [hcnt, sameVars_lookup h hA inits ivs hivs]
      refine RefinesT.obind (RefinesT.ofoldl (fun a i => ?_) _ _) fun acc =>
        montifyAux_refinesT k H.next _ k' hk' _ _ (MAgree.app h hA cs acc)
      exact montifyAux_refinesT body H.sub1 _ b' hb' _ _
        (MAgree.app h (hA.lift h (g := fun w => .there w)
          (W' := HVector.cons (HasWord64.ofNat (d := jasminDialect) i) W) (fun _ => rfl)
          (.same .here) (HasWord64.ofNat (d := jasminDialect) i) rfl) cs a)
  | _, _, .ifThenElse (rs := rs) cond thn els k, H, _, ρ, q, hq, X, W, hA => by
      obtain ⟨c, hc, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨t', ht', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨e', he', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      have hcond : c.lookup W = cond.lookup X := by
        have h0 : (ρ cond).rel h W (cond.lookup X) := hA _ cond
        have e : ρ cond = .same c := Rd.eq_of_same? hc
        rw [e] at h0
        exact h0
      simp only [mfTree, treeAt]
      rw [hcond]
      refine RefinesT.obind ?_ fun r =>
        montifyAux_refinesT k H.next _ k' hk' _ _ (MAgree.app h hA rs r)
      split
      · exact montifyAux_refinesT thn H.sub1 ρ t' ht' X W hA
      · exact montifyAux_refinesT els H.sub2 ρ e' he' X W hA
  | _, _, .whileLoop (cs := cs) inits body k, H, _, ρ, q, hq, X, W, hA => by
      obtain ⟨ivs, hivs, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [mfTree, treeAt]
      rw [sameVars_lookup h hA inits ivs hivs]
      exact RefinesT.obind (RefinesT.owhileIter (fun a =>
          montifyAux_refinesT body H.sub1 _ b' hb' _ _ (MAgree.app h hA cs a)) _ _) fun acc =>
        montifyAux_refinesT k H.next _ k' hk' _ _ (MAgree.app h hA cs acc)
  | _, _, .call f args k, H, _, ρ, q, hq, X, W, hA => by
      unfold montifyAux at hq
      split at hq
      · cases hq
      · rename_i hf
        have hf' : montTag? f = none := Option.not_isSome_iff_eq_none.mp hf
        cases hi : fieldHeadB f with
        | false =>
          obtain ⟨args', k', hargs, hk', rfl⟩ := callArm_outer h hi args ρ H.deg _ q hq
          have hio : innerHead f = false := by simp [innerHead, hf', hi]
          simp only [mfTree, treeAt, mfEnv, hio, Bool.false_eq_true, ite_false]
          rw [sameVars_lookup h hA args args' hargs]
          exact RefinesT.obind (RefinesT.refl _) fun r =>
            montifyAux_refinesT k H.next _ k' hk' _ _ (MAgree.app h hA _ r)
        | true =>
          rw [mfTree_call_inner fuel (by simp [innerHead, hi])]
          cases hr : (montEnv (fieldEnv CallEnv.empty)).call f _ _ (Expr.lookupArgs args X) with
          | none => exact .fail rfl
          | some r =>
            rw [montEnv_of_none _ hf'] at hr
            obtain ⟨Θ', ρ', W', q', hk, hA', hden⟩ :=
              callArm_mfTree h hm fuel hf' hi args hA _ _ q hq r hr
            change RefinesT h₁ (mfTree fuel k (hvAppend r X)) (mfTree fuel q W)
            rw [hden]
            exact montifyAux_refinesT k H.next ρ' q' hk _ W' hA'

include hm in
/-- **The entry conversions keep the refinement.** When `entryConv` returns `q` from a renaming
    that agrees with `X` and `W`, and the tree of every program the continuation returns, from
    a renaming that agrees with `X` and a valuation `W'`, refines `t` at `W'`, the tree of `q`
    at `W` refines `t`. -/
theorem entryConv_refinesT {Γ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us))
    (X : Valuation Γ) (t : CallTree (nfCallSig jasminDialect) (Option (Valuation us)))
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen Γ Θ') (q' : NFProg jasminDialect Θ' us)
      (W' : Valuation Θ'), kk ρ' = some q' → MAgree h ρ' X W' →
        RefinesT h₁ t (mfTree fuel q' W')) :
    ∀ (vs : List (Var Γ w64 × ℤ)) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ)
      (q : NFProg jasminDialect Θ us) (W : Valuation Θ), entryConv h kk vs ρ = some q →
      MAgree h ρ X W → RefinesT h₁ t (mfTree fuel q W)
  | [], _, ρ, q, W, hq, hA => hk ρ q W hq hA
  | (v, d) :: vs, _, ρ, q, W, hq, hA => by
      obtain ⟨x, hx, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q1, hq1, rfl⟩ := Option.map_eq_some_iff.mp hq
      have hxv : x.lookup W = v.lookup X := by
        have h0 : (ρ v).rel h W (v.lookup X) := hA _ v
        have e : ρ v = .same x := Rd.eq_of_same? hx
        rw [e] at h0
        exact h0
      rw [convProg_mfTree h hm fuel x (d + 1) q1 W]
      refine entryConv_refinesT kk X t hk vs _ q1 _ hq1 ?_
      refine MAgree.set h (MAgree.comp h hA (g := fun y => .there (.there y))
        (W' := .cons (t := w64) (redcMulW p (x.lookup W) (BitVec.ofNat 64 (convC h (d + 1))))
          (.cons (t := w64) (BitVec.ofNat 64 (convC h (d + 1))) W)) ?_) v _ ?_
      · intro _ _
        rfl
      intro hlt
      have e := redcMulW_conv h 0 (d + 1) (((v.lookup X : BitVec 64).toNat : Nat) : ZMod p)
      rw [← word_eq_encK_zero h _ hlt, show (0 : ℤ) + (d + 1) - 1 = d by ring] at e
      change redcMulW p (x.lookup W) (BitVec.ofNat 64 (convC h (d + 1))) = _
      rw [hxv]
      exact e

/-- **The stage lemma of the rewriter `montify` at the tree level**: when `montify` accepts the
    parameter degrees `pd` and the degree assignment `H` and returns `q`, the tree of `q` at
    `mfEnv` refines the tree of `prog`, at every valuation and every source handler. -/
theorem refinesT_montify (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) (q : NFProg jasminDialect Γ ts)
    (hq : montify h pd H prog = some q) (X : Valuation Γ) :
    RefinesT h₁ (mfTree fuel prog X) (mfTree fuel q X) := by
  unfold montify at hq
  split at hq
  · rename_i hm'
    exact entryConv_refinesT h hm' fuel h₁ (fun ρ => montifyAux h prog H ρ) X _
      (fun ρ' q' W' hk hA' => montifyAux_refinesT h hm' fuel h₁ prog H ρ' q' hk X W' hA')
      (paramDegs Γ pd) (idRen Γ) q X hq (idRen_agree h X)
  · cases hq

end Montify

/-! ## The montify step -/

/-- **The body of a reduce-multiply head has the tree of its call** at `mfEnv`: the leaf of
    `montCall`. -/
theorem mfTree_montBody (fuel : Nat) (f : String) (as rs : List JasminTy)
    (b : NFProg jasminDialect as rs) (hb : montLibJ.call f as rs = some b)
    (x : Valuation (d := jasminDialect) as) : mfTree fuel b x = mfEnv.call f as rs x := by
  change montBody f as rs = some b at hb
  unfold montBody at hb
  split at hb
  · rename_i q hq
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      have hi : innerHead f = true := by simp [innerHead, hq]
      rcases x with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
      simp only [mfEnv, hi, ite_true, montEnv, hq]
      rw [mfTree, redcMulProg, treeAt_ofCom,
        Algebraic.FieldWord.MontDeg.redcMulBlk_value]
      rfl
    · cases hb
  · cases hb

variable (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
  (fuel : Nat)

/-- **A montify round refines the tree** at `mfEnv`: the rewriter refines it
    (`refinesT_montify`) and the inlining of the reduce-multiply heads keeps it. -/
theorem refinesT_montifyAt {p : Nat} (h : mont32Cert p = true) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) (X : Valuation Γ) :
    RefinesT h₁ (mfTree fuel prog X) (mfTree fuel (montifyAt h prog) X) := by
  unfold montifyAt
  split
  · rename_i q hq
    split
    · rename_i q' hq'
      split
      · refine RefinesT.trans (refinesT_montify h fuel h₁ _ _ prog q hq X) ?_
        rw [mfTree, mfTree, treeAt_inline? pureReader_renameInv mfEnv fuel (fun _ => rfl)
          (fun f as rs b hb x => mfTree_montBody fuel f as rs b hb x) q hq' X]
        exact RefinesT.refl _
      · exact RefinesT.refl _
    · exact RefinesT.refl _
  · exact RefinesT.refl _

/-- The montify rounds at a list of moduli refine the tree. -/
theorem refinesT_montifyMods {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    ∀ (ps : List Nat) (prog : NFProg jasminDialect Γ ts) (X : Valuation Γ),
      RefinesT h₁ (mfTree fuel prog X) (mfTree fuel (montifyMods ps prog) X)
  | [], _, _ => RefinesT.refl _
  | p :: ps, prog, X => by
      refine RefinesT.trans ?_ (refinesT_montifyMods ps _ X)
      split
      · rename_i h
        exact refinesT_montifyAt h₁ fuel h prog X
      · exact RefinesT.refl _

/-- **The stage lemma of `montifyStep` at the tree level**: the tree at `mfEnv` of the output
    of the montify step refines the tree of its input, at every source handler. -/
theorem refinesT_montifyStep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hf : (montifyStep Γ ts).run p = some q)
    (X : Valuation Γ) : RefinesT h₁ (mfTree fuel p X) (mfTree fuel q X) := by
  obtain rfl : montifyPass p = q := Option.some.inj hf
  exact refinesT_montifyMods h₁ fuel _ p X

/-- **The montify step from the tree with every call an event**: at a source handler that
    answers each inner head by its value, the tree at `mfEnv` of the output of the montify
    step refines the tree `nfProgTree` of its input. -/
theorem refinesT_nfProgTree_montifyStep
    (hh : ∀ (f : String) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₁ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p q : NFProg jasminDialect Γ ts}
    (hf : (montifyStep Γ ts).run p = some q) (X : Valuation Γ) :
    RefinesT h₁ (nfProgTree fuel p X) (mfTree fuel q X) :=
  RefinesT.trans (refinesT_nfProgTree_mfTree h₁ hh fuel p X) (refinesT_montifyStep h₁ fuel hf X)

/-! ## The field dialect step -/

open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldBodyD fieldLibD fieldBodyD_some
  fieldBodyD_callFree fieldLibD_sound fieldDialectStep)

/-- A head with a raised body is a field head. -/
theorem fieldHeadB_of_raiseBody {f : String} {as rs : List JasminTy}
    {b : NFProg FieldChainDialect.jasField (as.map Sum.inl) (rs.map Sum.inl)}
    (h : FieldRaise.raiseBody f (as.map Sum.inl) (rs.map Sum.inl) = some b) :
    fieldHeadB f = true := by
  unfold FieldRaise.raiseBody at h
  cases ht : fieldTag? f with
  | some mp => simp [fieldHeadB, ht]
  | none =>
    rw [ht] at h
    cases hm : _root_.Hax.FieldTag.fieldTagM? f with
    | none => simp [hm] at h
    | some mpk => exact _root_.Hax.FieldTag.fieldHeadB_of_fieldTagM? hm

/-- **The lowered body of a field head refines its call** at `mfEnv`: the call is the leaf of
    the value of the `u64` table, and the body, which has no `call`, is the leaf of its
    denotation, which is that value whenever the table answers. -/
theorem refinesT_fieldBodyD (h₁ : ∀ e : (nfCallSig jasminDialect).Event,
      (nfCallSig jasminDialect).Resp e) (fuel : Nat) (f : String) (as rs : List JasminTy)
    (b : NFProg jasminDialect as rs) (hb : fieldLibD.call f as rs = some b)
    (x : Valuation (d := jasminDialect) as) :
    RefinesT h₁ (mfEnv.call f as rs x) (mfTree fuel b x) := by
  change fieldBodyD f as rs = some b at hb
  obtain ⟨-, r₁, hr₁, -⟩ := fieldBodyD_some hb
  have hfb : fieldHeadB f = true := fieldHeadB_of_raiseBody hr₁
  have hmt : montTag? f = none := by
    cases hq : montTag? f with
    | none => rfl
    | some q =>
      rw [fieldHeadB_of_montTag? hq] at hfb
      cases hfb
  have hi : innerHead f = true := by simp [innerHead, hfb]
  have hbf := fieldBodyD_callFree hb
  obtain ⟨o, ho⟩ := treeAt_ret_of_callFree mfEnv fuel b hbf x
  have hoe : o = b.denoteAt (fieldEnv CallEnv.empty) fuel x := by
    have e := interp_mfTree CallEnv.empty fuel b x
    rw [mfTree, ho] at e
    refine e.trans ?_
    exact NFProg.denoteAt_congr b _ _
      (fun _ _ _ _ hc => (not_calls_of_callFree b hbf hc).elim) fuel x
  simp only [mfEnv, hi, ite_true]
  rw [mfTree, ho, montEnv_of_none _ hmt]
  cases hy : (fieldEnv CallEnv.empty).call f as rs x with
  | none => exact .fail rfl
  | some y =>
    have hd := @InlineLib.Sound.call jasminDialect _ _ _ _ _ ⟨fieldEnv CallEnv.empty⟩
      fieldLibD fuel (fieldLibD_sound CallEnv.empty fuel) f as rs b hb x y hy
    refine .ret ?_
    rw [hoe]
    exact hd.symm

/-- **The stage lemma of `fieldDialectStep` at the tree level**: the tree at `mfEnv` of the
    output of the field dialect step refines the tree of its input, at every source handler.
    A field call is a leaf of `mfEnv`, and its lowered body is a leaf with the same value. -/
theorem refinesT_fieldDialectStep (h₁ : ∀ e : (nfCallSig jasminDialect).Event,
      (nfCallSig jasminDialect).Resp e) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p q : NFProg jasminDialect Γ ts}
    (hf : (fieldDialectStep Γ ts).run p = some q) (X : Valuation Γ) :
    RefinesT h₁ (mfTree fuel p X) (mfTree fuel q X) := by
  change (if fieldFree p then some p else _) = some q at hf
  split at hf
  · cases hf
    exact RefinesT.refl _
  · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · cases hif
      exact refinesT_inline? pureReader_renameInv mfEnv fuel h₁ (fun _ => rfl)
        (fun f as rs b hb x => refinesT_fieldBodyD h₁ fuel f as rs b hb x) p hq0 X
    · cases hif

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont
