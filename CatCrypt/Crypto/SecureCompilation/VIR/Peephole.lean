/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom

/-!
# Verified peephole rewriting for `Com`

A `PeepholeRewrite` is a pair of programs over a common context together with a
proof that they denote the same function and a proof that they emit the same
observations. `rewritePeepholeAt` applies one at a given position of a target
program; it is total, returning the target unchanged when the pattern does not
match, so its soundness theorems are unconditional.

A position inside a program is named by a `Zipper`: the bindings before the
position, as a `Lets`, and the program continuing from it.
`Zipper.insertPureCom` splices a program in at that position and substitutes one
variable of the suffix at the spliced program's result. The matcher `matchVar`
walks the pattern's bindings backwards against the target's, unifying pattern
variables with target variables in a `Mapping`; `denote_matchVar` states what a
successful match guarantees.

Leakage is carried alongside the denotation. A dialect supplies a `DialectLeak`
instance giving the observations each operation emits on its argument values,
and `Com.leakEvents` collects them in evaluation order. A `PeepholeRewrite`
whose pattern emits no observation leaves the target's observation trace
unchanged.

## Main results

* `Ctxt.Valuation.ofFun`, `comap`, `ext` — the function view of a valuation, and
  renaming of valuations along a `Ctxt.Hom`.
* `Lets`, `Lets.denote`, `Lets.getExpr`; `Com.outContext`, `Com.toLets`,
  `Com.denoteLets`, `Com.returnVar`.
* `Zipper`, `Zipper.toCom`, `Zipper.insertPureCom`,
  `Zipper.denote_insertPureCom_eq_of`.
* `DialectLeak`, `Com.leakEvents`, `Lets.leakEvents`,
  `Zipper.leakEvents_insertPureCom`.
* `Mapping`, `matchVar`, `matchArgWith`, `denote_matchVar`.
* `Lets.vars`, `Com.vars`, `Ctxt.allVars`, and the `Decidable` instance for
  "every variable of the pattern's context occurs in the pattern".
* `splitProgramAt`, `rewriteAt`, `rewritePeepholeAt`, `rewritePeephole`,
  `multiRewritePeephole`, with `denote_rewritePeepholeAt`,
  `denote_rewritePeephole`, `denote_multiRewritePeephole`,
  `leak_rewritePeepholeAt`, `leak_rewritePeephole`.
* `PeepholeDemo` — `bvSub a a ↦ bvXor a a` as a `PeepholeRewrite` over
  `catCryptDialect`.

## References

* opencompl/lean-mlir, `LeanMLIR/Framework/Zipper.lean` and
  `LeanMLIR/Transforms/Rewrite/{Mapping,Match,Rewrite}.lean`: the source of the
  `Zipper` / `Mapping` / `matchVar` / `PeepholeRewrite` design.
* *Verifying Peephole Rewriting In SSA Compiler IRs*, arXiv:2407.03685.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

open Ctxt (Var)

/-! ## 1. Valuations as functions on variables -/

namespace Ctxt.Valuation

/-- Build a valuation from a function assigning a value to every variable. -/
def ofFun {d : Dialect} [TyDenote d.Ty] :
    {Γ : Ctxt d} → (∀ t : d.Ty, Var Γ t → ⟦t⟧) → Ctxt.Valuation Γ
  | [], _ => .nil
  | _ :: _, f => .cons (f _ .here) (ofFun (fun t v => f t (.there v)))

@[simp] theorem lookup_ofFun {d : Dialect} [TyDenote d.Ty] :
    {Γ : Ctxt d} → {t : d.Ty} → (v : Var Γ t) → (f : ∀ t : d.Ty, Var Γ t → ⟦t⟧) →
      v.lookup (ofFun f) = f t v
  | _ :: _, _, .here, _ => rfl
  | _ :: _, _, .there v, f => lookup_ofFun v (fun t v => f t (.there v))

/-- Two valuations of the same context that agree on every variable are equal. -/
theorem ext {d : Dialect} [TyDenote d.Ty] :
    {Γ : Ctxt d} → (V W : Ctxt.Valuation Γ) →
      (∀ (t : d.Ty) (v : Var Γ t), v.lookup V = v.lookup W) → V = W
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons x V, .cons y W, h => by
      have hx : x = y := h _ .here
      have hV : V = W := ext V W (fun t v => h t (.there v))
      subst hx; subst hV; rfl

/-- Rename a valuation along a context homomorphism. -/
def comap {d : Dialect} [TyDenote d.Ty] {Γ Γ' : Ctxt d}
    (h : Ctxt.Hom Γ Γ') (V : Ctxt.Valuation Γ') : Ctxt.Valuation Γ :=
  ofFun (fun _ v => (h v).lookup V)

@[simp] theorem lookup_comap {d : Dialect} [TyDenote d.Ty] {Γ Γ' : Ctxt d} {t : d.Ty}
    (h : Ctxt.Hom Γ Γ') (V : Ctxt.Valuation Γ') (v : Var Γ t) :
    v.lookup (V.comap h) = (h v).lookup V :=
  lookup_ofFun v _

@[simp] theorem comap_id {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d}
    (V : Ctxt.Valuation Γ) : V.comap (Ctxt.Hom.id Γ) = V :=
  ext _ _ (fun _ _ => by simp [Ctxt.Hom.id])

theorem extend_comap_lift {d : Dialect} [TyDenote d.Ty] {Γ Γ' : Ctxt d} {s : d.Ty}
    (h : Ctxt.Hom Γ Γ') (V : Ctxt.Valuation Γ') (x : ⟦s⟧) :
    (V.extend x).comap (Ctxt.Hom.lift h) = (V.comap h).extend x :=
  ext _ _ (fun _ v => by
    cases v <;> simp [Ctxt.Valuation.extend, Ctxt.Hom.lift, Var.lookup])

@[simp] theorem comap_weakenOne {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d} {s : d.Ty}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) :
    (V.extend x).comap (Ctxt.Hom.weakenOne Γ s) = V :=
  ext _ _ (fun _ _ => by
    simp [Ctxt.Valuation.extend, Ctxt.Hom.weakenOne, Var.lookup])

@[simp] theorem comap_comp {d : Dialect} [TyDenote d.Ty] {Γ₁ Γ₂ Γ₃ : Ctxt d}
    (h₂ : Ctxt.Hom Γ₂ Γ₃) (h₁ : Ctxt.Hom Γ₁ Γ₂) (V : Ctxt.Valuation Γ₃) :
    V.comap (Ctxt.Hom.comp h₂ h₁) = (V.comap h₂).comap h₁ :=
  ext _ _ (fun _ _ => by simp [Ctxt.Hom.comp])

end Ctxt.Valuation

/-! ## 2. Renaming commutes with denotation -/

@[simp] theorem Expr.op_rename {d : Dialect} [DialectSignature d] {Γ Γ' : Ctxt d}
    {τ : d.Ty} (h : Ctxt.Hom Γ Γ') (e : Expr d Γ τ) : (e.rename h).op = e.op := rfl

@[simp] theorem Expr.args_rename {d : Dialect} [DialectSignature d] {Γ Γ' : Ctxt d}
    {τ : d.Ty} (h : Ctxt.Hom Γ Γ') (e : Expr d Γ τ) :
    (e.rename h).args = HVector.renameVars h e.args := rfl

theorem Expr.lookupArgs_renameVars {d : Dialect} [TyDenote d.Ty] {Γ Γ' : Ctxt d}
    (h : Ctxt.Hom Γ Γ') (V : Ctxt.Valuation Γ') :
    ∀ {tys : List d.Ty} (args : HVector (fun ty => Var Γ ty) tys),
      Expr.lookupArgs (HVector.renameVars h args) V = Expr.lookupArgs args (V.comap h)
  | [], .nil => rfl
  | _ :: _, .cons a as => by
      simp only [HVector.renameVars, Expr.lookupArgs, Ctxt.Valuation.lookup_comap,
        lookupArgs_renameVars h V as]

@[simp] theorem Expr.denote_rename {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {Γ Γ' : Ctxt d} {τ : d.Ty}
    (h : Ctxt.Hom Γ Γ') (e : Expr d Γ τ) (V : Ctxt.Valuation Γ') :
    (e.rename h).denote V = e.denote (V.comap h) := by
  show e.retTy_eq ▸ DialectDenote.denote e.op
      (Expr.lookupArgs (HVector.renameVars h e.args) V) = _
  rw [Expr.lookupArgs_renameVars]
  rfl

@[simp] theorem Com.denote_rename {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] :
    {Γ Γ' : Ctxt d} → {τ : d.Ty} → (h : Ctxt.Hom Γ Γ') → (c : Com d Γ τ) →
      (V : Ctxt.Valuation Γ') → (c.rename h).denote V = c.denote (V.comap h)
  | _, _, _, _, .ret _, _ => by simp [Com.rename, Com.denote]
  | _, _, _, h, .var e body, _ => by
      simp only [Com.rename, Com.denote, Expr.denote_rename,
        Com.denote_rename (Ctxt.Hom.lift h) body,
        Ctxt.Valuation.extend_comap_lift]

/-- Two expressions with the same operation whose arguments evaluate alike
denote the same value. -/
theorem Expr.denote_eq_of_lookupArgs {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {Γ Γ' : Ctxt d} {τ : d.Ty} {op : d.Op}
    (hty : DialectSignature.ret op = τ)
    (args : HVector (fun ty => Var Γ ty) (DialectSignature.sig op))
    (args' : HVector (fun ty => Var Γ' ty) (DialectSignature.sig op))
    (V : Ctxt.Valuation Γ) (V' : Ctxt.Valuation Γ')
    (h : Expr.lookupArgs args V = Expr.lookupArgs args' V') :
    (Expr.mk op hty args).denote V = (Expr.mk op hty args').denote V' := by
  simp only [Expr.denote, h]

/-! ## 3. `Lets`: a straight-line sequence of bindings -/

/-- A straight-line sequence of bindings taking a valuation of `Γ_in` to a
valuation of the output context. The head of the output context is the most
recent binding. -/
inductive Lets (d : Dialect) [DialectSignature d] (Γ_in : Ctxt d) :
    Ctxt d → Type _ where
  /-- The empty sequence. -/
  | nil : Lets d Γ_in Γ_in
  /-- Extend a sequence with one more binding. -/
  | var {Γ_out : Ctxt d} {t : d.Ty} (body : Lets d Γ_in Γ_out)
      (e : Expr d Γ_out t) : Lets d Γ_in (t :: Γ_out)

namespace Lets

variable {d : Dialect} [DialectSignature d]

/-- Denotation of a binding sequence: extend the input valuation one binding at
a time. -/
def denote [TyDenote d.Ty] [DialectDenote d] {Γ_in : Ctxt d} :
    {Γ_out : Ctxt d} → Lets d Γ_in Γ_out → Ctxt.Valuation Γ_in → Ctxt.Valuation Γ_out
  | _, .nil, V => V
  | _, .var body e, V => (body.denote V).extend (e.denote (body.denote V))

/-- The expression binding a variable, weakened into the output context.
`none` when the variable is free in the input context. -/
def getExpr {Γ_in : Ctxt d} :
    {Γ_out : Ctxt d} → Lets d Γ_in Γ_out → {t : d.Ty} → Var Γ_out t →
      Option (Expr d Γ_out t)
  | _, .nil, _, _ => none
  | _, .var _ e, _, .here => some (e.rename (Ctxt.Hom.weakenOne _ _))
  | _, .var body _, _, .there v =>
      (body.getExpr v).map (Expr.rename (Ctxt.Hom.weakenOne _ _))

/-- The expression returned by `getExpr` denotes the value the variable is bound
to. -/
theorem getExpr_denote [TyDenote d.Ty] [DialectDenote d] {Γ_in : Ctxt d}
    (V : Ctxt.Valuation Γ_in) :
    {Γ_out : Ctxt d} → (lets : Lets d Γ_in Γ_out) → {t : d.Ty} → (v : Var Γ_out t) →
      (e : Expr d Γ_out t) → lets.getExpr v = some e →
      e.denote (lets.denote V) = v.lookup (lets.denote V)
  | _, .nil, _, _, _, h => by simp [getExpr] at h
  | _, .var _ _, _, .here, e, h => by
      simp only [getExpr, Option.some.injEq] at h
      subst h
      simp only [denote, Expr.denote_rename, Ctxt.Valuation.comap_weakenOne]
      rfl
  | _, .var body _, _, .there v, e, h => by
      simp only [getExpr, Option.map_eq_some_iff] at h
      obtain ⟨e', he', rfl⟩ := h
      simp only [denote, Expr.denote_rename, Ctxt.Valuation.comap_weakenOne]
      exact getExpr_denote V body v e' he'

end Lets

/-! ## 4. A `Com` as a binding sequence plus a result variable -/

namespace Com

variable {d : Dialect} [DialectSignature d]

/-- The context in scope after all of a program's bindings. -/
def outContext : {Γ : Ctxt d} → {τ : d.Ty} → Com d Γ τ → Ctxt d
  | Γ, _, .ret _ => Γ
  | _, _, .var _ body => body.outContext

/-- The program's result, as a variable of its output context. -/
def returnVar : {Γ : Ctxt d} → {τ : d.Ty} → (c : Com d Γ τ) → Var c.outContext τ
  | _, _, .ret v => v
  | _, _, .var _ body => body.returnVar

/-- The weakening from a program's input context into its output context. -/
def outContextHom : {Γ : Ctxt d} → {τ : d.Ty} → (c : Com d Γ τ) →
    Ctxt.Hom Γ c.outContext
  | _, _, .ret _ => Ctxt.Hom.id _
  | _, _, .var _ body => Ctxt.Hom.comp body.outContextHom (Ctxt.Hom.weakenOne _ _)

/-- The valuation of a program's output context reached from an input
valuation. -/
def denoteLets [TyDenote d.Ty] [DialectDenote d] :
    {Γ : Ctxt d} → {τ : d.Ty} → (c : Com d Γ τ) → Ctxt.Valuation Γ →
      Ctxt.Valuation c.outContext
  | _, _, .ret _, V => V
  | _, _, .var e body, V => body.denoteLets (V.extend (e.denote V))

@[simp] theorem denoteLets_returnVar [TyDenote d.Ty] [DialectDenote d] :
    {Γ : Ctxt d} → {τ : d.Ty} → (c : Com d Γ τ) → (V : Ctxt.Valuation Γ) →
      c.returnVar.lookup (c.denoteLets V) = c.denote V
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V => denoteLets_returnVar body (V.extend (e.denote V))

@[simp] theorem lookup_outContextHom_denoteLets [TyDenote d.Ty] [DialectDenote d] :
    {Γ : Ctxt d} → {τ : d.Ty} → (c : Com d Γ τ) → (V : Ctxt.Valuation Γ) →
      {t : d.Ty} → (v : Var Γ t) →
      (c.outContextHom v).lookup (c.denoteLets V) = v.lookup V
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .var e body, V, _, v => by
      simp only [outContextHom, denoteLets, Ctxt.Hom.comp, Ctxt.Hom.weakenOne]
      exact lookup_outContextHom_denoteLets body (V.extend (e.denote V)) (.there v)

theorem comap_outContextHom_denoteLets [TyDenote d.Ty] [DialectDenote d]
    {Γ : Ctxt d} {τ : d.Ty} (c : Com d Γ τ) (V : Ctxt.Valuation Γ) :
    (c.denoteLets V).comap c.outContextHom = V :=
  Ctxt.Valuation.ext _ _ (fun _ _ => by simp)

end Com

/-! ## 5. Appending a program to a binding sequence -/

/-- Append the bindings of a `Com` to the end of a binding sequence. -/
def Lets.addComToEnd {d : Dialect} [DialectSignature d] {Γ_in : Ctxt d} :
    {Γ_mid : Ctxt d} → Lets d Γ_in Γ_mid → {τ : d.Ty} → (c : Com d Γ_mid τ) →
      Lets d Γ_in c.outContext
  | _, lets, _, .ret _ => lets
  | _, lets, _, .var e body => (Lets.var lets e).addComToEnd body

/-- A program's bindings, as a `Lets`. -/
def Com.toLets {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {τ : d.Ty}
    (c : Com d Γ τ) : Lets d Γ c.outContext :=
  Lets.nil.addComToEnd c

theorem Lets.denote_addComToEnd {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ_in : Ctxt d} (V : Ctxt.Valuation Γ_in) :
    {Γ_mid : Ctxt d} → (lets : Lets d Γ_in Γ_mid) → {τ : d.Ty} → (c : Com d Γ_mid τ) →
      (lets.addComToEnd c).denote V = c.denoteLets (lets.denote V)
  | _, _, _, .ret _ => rfl
  | _, lets, _, .var e body => Lets.denote_addComToEnd V (Lets.var lets e) body

@[simp] theorem Com.denote_toLets {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ : Ctxt d} {τ : d.Ty} (c : Com d Γ τ) (V : Ctxt.Valuation Γ) :
    c.toLets.denote V = c.denoteLets V :=
  Lets.denote_addComToEnd V Lets.nil c

/-! ## 6. Substituting one variable in a context homomorphism -/

/-- Decidable equality on De Bruijn variables of the same context and type. -/
instance Ctxt.Var.instDecidableEq {d : Dialect} {Γ : Ctxt d} {t : d.Ty} :
    DecidableEq (Var Γ t) := fun a b =>
  match a, b with
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun h => by cases h)
  | .there _, .here => isFalse (fun h => by cases h)
  | .there a, .there b =>
      match Ctxt.Var.instDecidableEq a b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (fun heq => h (by cases heq; rfl))

/-- Transport a variable along an equality of its type. -/
def Ctxt.Var.castTy {d : Dialect} {Γ : Ctxt d} {s t : d.Ty} (h : s = t)
    (v : Var Γ s) : Var Γ t := h ▸ v

@[simp] theorem Ctxt.Var.castTy_rfl {d : Dialect} {Γ : Ctxt d} {s : d.Ty}
    (v : Var Γ s) : Ctxt.Var.castTy rfl v = v := rfl

/-- A context homomorphism overridden at one variable. -/
def Ctxt.Hom.subst {d : Dialect} [DecidableEq d.Ty] {Γ Γ' : Ctxt d} {nt : d.Ty}
    (h : Ctxt.Hom Γ Γ') (v : Var Γ nt) (w : Var Γ' nt) : Ctxt.Hom Γ Γ' :=
  fun {s} x =>
    if hs : s = nt then
      (if Ctxt.Var.castTy hs x = v then Ctxt.Var.castTy hs.symm w else h x)
    else h x

@[simp] theorem Ctxt.Hom.subst_self {d : Dialect} [DecidableEq d.Ty] {Γ Γ' : Ctxt d}
    {nt : d.Ty} (h : Ctxt.Hom Γ Γ') (v : Var Γ nt) (w : Var Γ' nt) :
    Ctxt.Hom.subst h v w v = w := by
  simp [Ctxt.Hom.subst]

theorem Ctxt.Hom.subst_of_ne {d : Dialect} [DecidableEq d.Ty] {Γ Γ' : Ctxt d}
    {nt s : d.Ty} (h : Ctxt.Hom Γ Γ') (v : Var Γ nt) (w : Var Γ' nt) (x : Var Γ s)
    (hx : ∀ hs : s = nt, Ctxt.Var.castTy hs x ≠ v) :
    Ctxt.Hom.subst h v w x = h x := by
  simp only [Ctxt.Hom.subst]
  split
  · rename_i hs
    simp [hx hs]
  · rfl

/-! ## 7. Zippers -/

/-- A position inside a program: the bindings before the position, and the
program that continues from it. -/
structure Zipper (d : Dialect) [DialectSignature d] (Γ_in : Ctxt d) (τ : d.Ty) where
  /-- The context in scope at the position. -/
  {Γ_mid : Ctxt d}
  /-- The bindings before the position. -/
  top : Lets d Γ_in Γ_mid
  /-- The program continuing from the position. -/
  bot : Com d Γ_mid τ

namespace Zipper

variable {d : Dialect} [DialectSignature d]

/-- Denotation of a zipper: run the prefix, then the suffix. -/
def denote [TyDenote d.Ty] [DialectDenote d] {Γ_in : Ctxt d} {τ : d.Ty}
    (zip : Zipper d Γ_in τ) (V : Ctxt.Valuation Γ_in) : ⟦τ⟧ :=
  zip.bot.denote (zip.top.denote V)

/-- Fold a prefix of bindings back onto the front of a program. -/
def toComGo {Γ_in : Ctxt d} {τ : d.Ty} :
    {Γ_mid : Ctxt d} → Lets d Γ_in Γ_mid → Com d Γ_mid τ → Com d Γ_in τ
  | _, .nil, com => com
  | _, .var body e, com => toComGo body (.var e com)

/-- Recombine a zipper into a single program. -/
def toCom {Γ_in : Ctxt d} {τ : d.Ty} (zip : Zipper d Γ_in τ) : Com d Γ_in τ :=
  toComGo zip.top zip.bot

@[simp] theorem denote_toComGo [TyDenote d.Ty] [DialectDenote d] {Γ_in : Ctxt d}
    {τ : d.Ty} (V : Ctxt.Valuation Γ_in) :
    {Γ_mid : Ctxt d} → (lets : Lets d Γ_in Γ_mid) → (com : Com d Γ_mid τ) →
      (toComGo lets com).denote V = com.denote (lets.denote V)
  | _, .nil, _ => rfl
  | _, .var body e, com => by
      rw [show toComGo (Lets.var body e) com = toComGo body (Com.var e com) from rfl,
        denote_toComGo V body (Com.var e com)]
      rfl

@[simp] theorem denote_toCom [TyDenote d.Ty] [DialectDenote d] {Γ_in : Ctxt d}
    {τ : d.Ty} (zip : Zipper d Γ_in τ) (V : Ctxt.Valuation Γ_in) :
    zip.toCom.denote V = zip.denote V :=
  denote_toComGo V zip.top zip.bot

/-- Splice a program in at the zipper's position, substituting every use of `v`
in the suffix at the spliced program's result. -/
def insertPureCom [DecidableEq d.Ty] {Γ_in : Ctxt d} {τ nt : d.Ty}
    (zip : Zipper d Γ_in τ) (v : Var zip.Γ_mid nt)
    (newCom : Com d zip.Γ_mid nt) : Zipper d Γ_in τ :=
  { top := zip.top.addComToEnd newCom
    bot := zip.bot.rename (Ctxt.Hom.subst newCom.outContextHom v newCom.returnVar) }

/-- The spliced program's valuation, read back through the substitution
homomorphism, is the original valuation — provided the spliced program computes
the value the substituted variable already held. -/
theorem comap_subst_denoteLets [TyDenote d.Ty] [DialectDenote d] [DecidableEq d.Ty]
    {Γ_mid : Ctxt d} {nt : d.Ty} (v : Var Γ_mid nt) (newCom : Com d Γ_mid nt)
    (V : Ctxt.Valuation Γ_mid) (h : newCom.denote V = v.lookup V) :
    (newCom.denoteLets V).comap
        (Ctxt.Hom.subst newCom.outContextHom v newCom.returnVar) = V := by
  refine Ctxt.Valuation.ext _ _ (fun t x => ?_)
  simp only [Ctxt.Valuation.lookup_comap]
  by_cases hs : t = nt
  · subst hs
    by_cases hx : x = v
    · subst hx
      rw [Ctxt.Hom.subst_self, Com.denoteLets_returnVar, h]
    · rw [Ctxt.Hom.subst_of_ne _ _ _ _ (fun _ => by simpa using hx)]
      simp
  · rw [Ctxt.Hom.subst_of_ne _ _ _ _ (fun he => absurd he hs)]
    simp

/-- Splicing a program in preserves the denotation, provided the spliced program
computes the value the substituted variable already held. -/
theorem denote_insertPureCom_eq_of [TyDenote d.Ty] [DialectDenote d] [DecidableEq d.Ty]
    {Γ_in : Ctxt d} {τ nt : d.Ty} {zip : Zipper d Γ_in τ} {v : Var zip.Γ_mid nt}
    {newCom : Com d zip.Γ_mid nt} (V_in : Ctxt.Valuation Γ_in)
    (h : newCom.denote (zip.top.denote V_in) = v.lookup (zip.top.denote V_in)) :
    (zip.insertPureCom v newCom).denote V_in = zip.denote V_in := by
  unfold denote insertPureCom
  simp only []
  rw [Com.denote_rename, Lets.denote_addComToEnd, comap_subst_denoteLets _ _ _ h]

end Zipper

/-! ## 8. Leakage traces -/

/-- The observations a dialect's operations emit. `leakOf op args` is the list
of events evaluating `op` on `args` produces; an operation with no observable
side channel emits `[]`. -/
class DialectLeak (d : Dialect) [TyDenote d.Ty] [DialectSignature d] where
  /-- The alphabet of observations. -/
  Event : Type
  /-- The observations an operation emits on the given argument values. -/
  leakOf : (op : d.Op) → HVector (fun t => ⟦t⟧) (DialectSignature.sig op) →
    List Event

namespace Com

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [DialectLeak d]

/-- The observations a program emits on a given input, in evaluation order. -/
def leakEvents : {Γ : Ctxt d} → {τ : d.Ty} → Com d Γ τ → Ctxt.Valuation Γ →
    List (DialectLeak.Event d)
  | _, _, .ret _, _ => []
  | _, _, .var e body, V =>
      DialectLeak.leakOf e.op (Expr.lookupArgs e.args V) ++
        body.leakEvents (V.extend (e.denote V))

@[simp] theorem leakEvents_rename :
    {Γ Γ' : Ctxt d} → {τ : d.Ty} → (h : Ctxt.Hom Γ Γ') → (c : Com d Γ τ) →
      (V : Ctxt.Valuation Γ') → (c.rename h).leakEvents V = c.leakEvents (V.comap h)
  | _, _, _, _, .ret _, _ => rfl
  | _, _, _, h, .var e body, _ => by
      simp only [Com.rename, leakEvents, Expr.op_rename, Expr.args_rename,
        Expr.lookupArgs_renameVars, Expr.denote_rename,
        leakEvents_rename (Ctxt.Hom.lift h) body, Ctxt.Valuation.extend_comap_lift]

end Com

namespace Lets

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [DialectLeak d]

/-- The observations a binding sequence emits on a given input. -/
def leakEvents {Γ_in : Ctxt d} :
    {Γ_out : Ctxt d} → Lets d Γ_in Γ_out → Ctxt.Valuation Γ_in →
      List (DialectLeak.Event d)
  | _, .nil, _ => []
  | _, .var body e, V =>
      body.leakEvents V ++
        DialectLeak.leakOf e.op (Expr.lookupArgs e.args (body.denote V))

theorem leakEvents_addComToEnd {Γ_in : Ctxt d} (V : Ctxt.Valuation Γ_in) :
    {Γ_mid : Ctxt d} → (lets : Lets d Γ_in Γ_mid) → {τ : d.Ty} → (c : Com d Γ_mid τ) →
      (lets.addComToEnd c).leakEvents V
        = lets.leakEvents V ++ c.leakEvents (lets.denote V)
  | _, lets, _, .ret _ => (List.append_nil (lets.leakEvents V)).symm
  | _, lets, _, .var e body => by
      have ih := leakEvents_addComToEnd V (Lets.var lets e) body
      show ((Lets.var lets e).addComToEnd body).leakEvents V
        = lets.leakEvents V ++ (Com.var e body).leakEvents (lets.denote V)
      rw [ih]
      simp [leakEvents, Com.leakEvents, denote, List.append_assoc]

end Lets

namespace Zipper

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [DialectLeak d]

/-- The observations a zipper emits: the prefix's, then the suffix's. -/
def leakEvents {Γ_in : Ctxt d} {τ : d.Ty} (zip : Zipper d Γ_in τ)
    (V : Ctxt.Valuation Γ_in) : List (DialectLeak.Event d) :=
  zip.top.leakEvents V ++ zip.bot.leakEvents (zip.top.denote V)

@[simp] theorem leakEvents_toComGo {Γ_in : Ctxt d} {τ : d.Ty}
    (V : Ctxt.Valuation Γ_in) :
    {Γ_mid : Ctxt d} → (lets : Lets d Γ_in Γ_mid) → (com : Com d Γ_mid τ) →
      (toComGo lets com).leakEvents V
        = lets.leakEvents V ++ com.leakEvents (lets.denote V)
  | _, .nil, _ => by simp [toComGo, Lets.leakEvents, Lets.denote]
  | _, .var body e, com => by
      rw [show toComGo (Lets.var body e) com = toComGo body (Com.var e com) from rfl,
        leakEvents_toComGo V body (Com.var e com)]
      simp [Lets.leakEvents, Lets.denote, Com.leakEvents, List.append_assoc]

@[simp] theorem leakEvents_toCom {Γ_in : Ctxt d} {τ : d.Ty} (zip : Zipper d Γ_in τ)
    (V : Ctxt.Valuation Γ_in) : zip.toCom.leakEvents V = zip.leakEvents V :=
  leakEvents_toComGo V zip.top zip.bot

/-- Splicing a program in inserts exactly that program's observations at the
zipper's position. -/
theorem leakEvents_insertPureCom [DecidableEq d.Ty] {Γ_in : Ctxt d} {τ nt : d.Ty}
    {zip : Zipper d Γ_in τ} {v : Var zip.Γ_mid nt} {newCom : Com d zip.Γ_mid nt}
    (V_in : Ctxt.Valuation Γ_in)
    (h : newCom.denote (zip.top.denote V_in) = v.lookup (zip.top.denote V_in)) :
    (zip.insertPureCom v newCom).leakEvents V_in
      = zip.top.leakEvents V_in ++ newCom.leakEvents (zip.top.denote V_in)
          ++ zip.bot.leakEvents (zip.top.denote V_in) := by
  unfold leakEvents insertPureCom
  simp only []
  rw [Lets.leakEvents_addComToEnd, Com.leakEvents_rename, Lets.denote_addComToEnd,
    comap_subst_denoteLets _ _ _ h]

/-- Splicing in an observation-free program leaves the observations
unchanged. -/
theorem leakEvents_insertPureCom_eq_of [DecidableEq d.Ty] {Γ_in : Ctxt d}
    {τ nt : d.Ty} {zip : Zipper d Γ_in τ} {v : Var zip.Γ_mid nt}
    {newCom : Com d zip.Γ_mid nt} (V_in : Ctxt.Valuation Γ_in)
    (h : newCom.denote (zip.top.denote V_in) = v.lookup (zip.top.denote V_in))
    (hleak : newCom.leakEvents (zip.top.denote V_in) = []) :
    (zip.insertPureCom v newCom).leakEvents V_in = zip.leakEvents V_in := by
  rw [leakEvents_insertPureCom V_in h, hleak]
  simp [leakEvents]

end Zipper

/-! ## 9. Enumerating the variables of a context -/

/-- Every variable of a context, paired with its type. -/
def Ctxt.allVars {d : Dialect} : (Γ : Ctxt d) → List ((t : d.Ty) × Var Γ t)
  | [] => []
  | t :: Γ => ⟨t, .here⟩ :: (Ctxt.allVars Γ).map (fun p => ⟨p.1, .there p.2⟩)

theorem Ctxt.mem_allVars {d : Dialect} :
    {Γ : Ctxt d} → {t : d.Ty} → (v : Var Γ t) →
      (⟨t, v⟩ : (t : d.Ty) × Var Γ t) ∈ Ctxt.allVars Γ
  | _ :: _, _, .here => List.mem_cons_self ..
  | _ :: _, _, .there v =>
      List.mem_cons_of_mem _ (List.mem_map_of_mem (Ctxt.mem_allVars v))

instance Ctxt.decidableForallVarMem {d : Dialect} [DecidableEq d.Ty] {Γ : Ctxt d}
    (L : List ((t : d.Ty) × Var Γ t)) :
    Decidable (∀ (t : d.Ty) (v : Var Γ t), (⟨t, v⟩ : (t : d.Ty) × Var Γ t) ∈ L) :=
  decidable_of_iff (∀ p ∈ Ctxt.allVars Γ, p ∈ L)
    ⟨fun h t v => h ⟨t, v⟩ (Ctxt.mem_allVars v), fun h p _ => by
      obtain ⟨t, v⟩ := p; exact h t v⟩

/-! ## 10. Mappings from pattern variables to target variables -/

/-- A pattern variable, paired with its type. -/
abbrev MapKey {d : Dialect} (Δ : Ctxt d) : Type _ := (t : d.Ty) × Var Δ t

/-- A partial assignment of target variables to the variables of a pattern's
input context, as an association list. -/
abbrev Mapping {d : Dialect} (Δ Γ : Ctxt d) : Type _ :=
  List ((k : MapKey Δ) × Var Γ k.1)

namespace Mapping

variable {d : Dialect} [DecidableEq d.Ty] {Δ Γ : Ctxt d}

/-- The variable assigned to a pattern variable, if any. -/
def lookup : Mapping Δ Γ → (k : MapKey Δ) → Option (Var Γ k.1)
  | [], _ => none
  | ⟨k', w⟩ :: m, k => if h : k' = k then some (h ▸ w) else lookup m k

@[simp] theorem lookup_cons_self (m : Mapping Δ Γ) (k : MapKey Δ) (w : Var Γ k.1) :
    lookup (⟨k, w⟩ :: m) k = some w := by simp [lookup]

theorem lookup_cons_of_ne (m : Mapping Δ Γ) {k k' : MapKey Δ} (w : Var Γ k'.1)
    (h : k' ≠ k) : lookup (⟨k', w⟩ :: m) k = lookup m k := by simp [lookup, h]

/-- Extension order: `Le m₁ m₂` when every assignment of `m₁` is also an
assignment of `m₂`. -/
def Le (m₁ m₂ : Mapping Δ Γ) : Prop :=
  ∀ (k : MapKey Δ) (w : Var Γ k.1), m₁.lookup k = some w → m₂.lookup k = some w

theorem Le.rfl (m : Mapping Δ Γ) : Le m m := fun _ _ h => h

theorem Le.trans {m₁ m₂ m₃ : Mapping Δ Γ} (h₁ : Le m₁ m₂) (h₂ : Le m₂ m₃) :
    Le m₁ m₃ := fun k w h => h₂ k w (h₁ k w h)

theorem Le.isSome {m₁ m₂ : Mapping Δ Γ} (h : Le m₁ m₂) {k : MapKey Δ}
    (hk : (m₁.lookup k).isSome) : (m₂.lookup k).isSome := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hk
  simp [h k w hw]

/-- The assignment is defined on every variable of the pattern's context. -/
def IsTotal (m : Mapping Δ Γ) : Prop := ∀ k : MapKey Δ, (m.lookup k).isSome

/-- A total assignment, read as a context homomorphism. -/
def toHom (m : Mapping Δ Γ) (h : m.IsTotal) : Ctxt.Hom Δ Γ :=
  fun {t} v => (m.lookup ⟨t, v⟩).get (h ⟨t, v⟩)

theorem lookup_eq_some_toHom (m : Mapping Δ Γ) (h : m.IsTotal) {t : d.Ty}
    (v : Var Δ t) : m.lookup ⟨t, v⟩ = some (m.toHom h v) :=
  (Option.some_get (h ⟨t, v⟩)).symm

/-- Read a valuation of the target context back along a partial assignment.
Unassigned pattern variables take the default value. -/
def mapValuation [TyDenote d.Ty] [∀ t : d.Ty, Inhabited ⟦t⟧] (m : Mapping Δ Γ)
    (V : Ctxt.Valuation Γ) : Ctxt.Valuation Δ :=
  Ctxt.Valuation.ofFun (fun t v =>
    match m.lookup ⟨t, v⟩ with
    | some w => w.lookup V
    | none => default)

theorem lookup_mapValuation_of [TyDenote d.Ty] [∀ t : d.Ty, Inhabited ⟦t⟧]
    {m : Mapping Δ Γ} {V : Ctxt.Valuation Γ} {t : d.Ty} {v : Var Δ t} {w : Var Γ t}
    (h : m.lookup ⟨t, v⟩ = some w) :
    v.lookup (m.mapValuation V) = w.lookup V := by
  simp [mapValuation, h]

theorem comap_toHom_eq_mapValuation [TyDenote d.Ty] [∀ t : d.Ty, Inhabited ⟦t⟧]
    (m : Mapping Δ Γ) (h : m.IsTotal) (V : Ctxt.Valuation Γ) :
    V.comap (m.toHom h) = m.mapValuation V :=
  Ctxt.Valuation.ext _ _ (fun _ v => by
    rw [Ctxt.Valuation.lookup_comap,
      lookup_mapValuation_of (lookup_eq_some_toHom m h v)])

end Mapping

/-! ## 11. Unification of a single variable -/

/-- Record that the pattern variable `w` stands for the target variable `v`, or
fail if `w` is already assigned to a different variable. -/
def unifyVars {d : Dialect} [DecidableEq d.Ty] {Δ Γ : Ctxt d} {t : d.Ty}
    (w : Var Δ t) (v : Var Γ t) (m : Mapping Δ Γ) : Option (Mapping Δ Γ) :=
  match m.lookup ⟨t, w⟩ with
  | some v' => if v' = v then some m else none
  | none => some (⟨⟨t, w⟩, v⟩ :: m)

theorem unifyVars_le {d : Dialect} [DecidableEq d.Ty] {Δ Γ : Ctxt d} {t : d.Ty}
    {w : Var Δ t} {v : Var Γ t} {m m' : Mapping Δ Γ}
    (h : unifyVars w v m = some m') : Mapping.Le m m' := by
  unfold unifyVars at h
  split at h
  · split at h
    · cases h; exact Mapping.Le.rfl _
    · exact absurd h (by simp)
  · rename_i hnone
    cases h
    intro k x hx
    by_cases hk : (⟨t, w⟩ : MapKey Δ) = k
    · subst hk; rw [hnone] at hx; exact absurd hx (by simp)
    · rwa [Mapping.lookup_cons_of_ne _ _ hk]

theorem unifyVars_lookup {d : Dialect} [DecidableEq d.Ty] {Δ Γ : Ctxt d} {t : d.Ty}
    {w : Var Δ t} {v : Var Γ t} {m m' : Mapping Δ Γ}
    (h : unifyVars w v m = some m') : m'.lookup ⟨t, w⟩ = some v := by
  unfold unifyVars at h
  split at h
  · rename_i v' hv'
    split at h
    · cases h; rename_i heq; rw [hv', heq]
    · exact absurd h (by simp)
  · cases h; simp

/-! ## 12. The matcher -/

/-- Transport an argument vector along an equality of its type list. -/
def HVector.castTys {d : Dialect} {Γ : Ctxt d} {l l' : List d.Ty} (h : l = l')
    (vs : HVector (fun ty => Var Γ ty) l) : HVector (fun ty => Var Γ ty) l' :=
  h ▸ vs

@[simp] theorem HVector.castTys_rfl {d : Dialect} {Γ : Ctxt d} {l : List d.Ty}
    (vs : HVector (fun ty => Var Γ ty) l) : HVector.castTys rfl vs = vs := rfl

/-- Run a variable matcher over corresponding entries of two argument vectors,
threading the assignment. -/
def matchArgWith {d : Dialect} [DecidableEq d.Ty] {Δ_in Γ_out Δ_mid : Ctxt d}
    (f : ∀ {t : d.Ty}, Var Γ_out t → Var Δ_mid t → Mapping Δ_in Γ_out →
      Option (Mapping Δ_in Γ_out)) :
    {l : List d.Ty} → HVector (fun ty => Var Γ_out ty) l →
      HVector (fun ty => Var Δ_mid ty) l → Mapping Δ_in Γ_out →
      Option (Mapping Δ_in Γ_out)
  | [], .nil, .nil, m => some m
  | _ :: _, .cons a as, .cons b bs, m => (f a b m).bind (matchArgWith f as bs)

/-- Extend the assignment so that the expression tree the pattern variable `w`
denotes in `matchLets` is unified with the expression tree the target variable
`v` denotes in `lets`. `none` on a conflicting assignment or a structural
mismatch. -/
def matchVar {d : Dialect} [DialectSignature d] [DecidableEq d.Ty] [DecidableEq d.Op]
    {Γ_in Γ_out Δ_in : Ctxt d} (lets : Lets d Γ_in Γ_out) :
    {Δ_out : Ctxt d} → (matchLets : Lets d Δ_in Δ_out) → {t : d.Ty} →
      Var Γ_out t → Var Δ_out t → Mapping Δ_in Γ_out → Option (Mapping Δ_in Γ_out)
  | _, .nil, _, v, w, m => unifyVars w v m
  | _, .var mlets me, _, v, .here, m =>
      match lets.getExpr v with
      | none => none
      | some ie =>
          if h : me.op = ie.op then
            matchArgWith (matchVar lets mlets) ie.args
              (HVector.castTys (congrArg DialectSignature.sig h) me.args) m
          else none
  | _, .var mlets _, _, v, .there w, m => matchVar lets mlets v w m

/-! ## 13. The matcher only extends the assignment -/

theorem matchArgWith_le {d : Dialect} [DecidableEq d.Ty] {Δ_in Γ_out Δ_mid : Ctxt d}
    {f : ∀ {t : d.Ty}, Var Γ_out t → Var Δ_mid t → Mapping Δ_in Γ_out →
      Option (Mapping Δ_in Γ_out)}
    (hf : ∀ {t : d.Ty} (a : Var Γ_out t) (b : Var Δ_mid t) (m m' : Mapping Δ_in Γ_out),
      f a b m = some m' → Mapping.Le m m') :
    ∀ {l : List d.Ty} (as : HVector (fun ty => Var Γ_out ty) l)
      (bs : HVector (fun ty => Var Δ_mid ty) l) (m m' : Mapping Δ_in Γ_out),
      matchArgWith f as bs m = some m' → Mapping.Le m m'
  | [], .nil, .nil, _, _, h => by
      simp only [matchArgWith, Option.some.injEq] at h
      cases h; exact Mapping.Le.rfl _
  | _ :: _, .cons a as, .cons b bs, m, m', h => by
      simp only [matchArgWith, Option.bind_eq_some_iff] at h
      obtain ⟨m₁, h₁, h₂⟩ := h
      exact Mapping.Le.trans (hf a b m m₁ h₁) (matchArgWith_le hf as bs m₁ m' h₂)

theorem matchVar_le {d : Dialect} [DialectSignature d] [DecidableEq d.Ty]
    [DecidableEq d.Op] {Γ_in Γ_out Δ_in : Ctxt d} (lets : Lets d Γ_in Γ_out) :
    ∀ {Δ_out : Ctxt d} (matchLets : Lets d Δ_in Δ_out) {t : d.Ty}
      (v : Var Γ_out t) (w : Var Δ_out t) (m m' : Mapping Δ_in Γ_out),
      matchVar lets matchLets v w m = some m' → Mapping.Le m m'
  | _, .nil, _, _, _, _, _, h => unifyVars_le h
  | _, .var mlets _, _, v, .here, m, m', h => by
      rcases hie : lets.getExpr v with _ | ie
      · simp [matchVar, hie] at h
      · simp only [matchVar, hie] at h
        split at h
        · exact matchArgWith_le
            (fun a b m₁ m₂ hh => matchVar_le lets mlets a b m₁ m₂ hh) _ _ _ _ h
        · exact absurd h (by simp)
  | _, .var mlets _, _, v, .there w, m, m', h => by
      simp only [matchVar] at h
      exact matchVar_le lets mlets v w m m' h

/-! ## 14. What a successful match guarantees -/

theorem lookupArgs_eq_of_matchArgWith {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty]
    {Δ_in Γ_out Δ_mid : Ctxt d}
    {f : ∀ {t : d.Ty}, Var Γ_out t → Var Δ_mid t → Mapping Δ_in Γ_out →
      Option (Mapping Δ_in Γ_out)}
    {Y : Mapping Δ_in Γ_out → Ctxt.Valuation Δ_mid} {Vout : Ctxt.Valuation Γ_out}
    (hmono : ∀ {t : d.Ty} (a : Var Γ_out t) (b : Var Δ_mid t) (m m' : Mapping Δ_in Γ_out),
      f a b m = some m' → Mapping.Le m m')
    (hf : ∀ {t : d.Ty} (a : Var Γ_out t) (b : Var Δ_mid t) (m m' : Mapping Δ_in Γ_out),
      f a b m = some m' → ∀ mf : Mapping Δ_in Γ_out, Mapping.Le m' mf →
        b.lookup (Y mf) = a.lookup Vout) :
    ∀ {l : List d.Ty} (as : HVector (fun ty => Var Γ_out ty) l)
      (bs : HVector (fun ty => Var Δ_mid ty) l) (m m' : Mapping Δ_in Γ_out),
      matchArgWith f as bs m = some m' → ∀ mf : Mapping Δ_in Γ_out, Mapping.Le m' mf →
      Expr.lookupArgs bs (Y mf) = Expr.lookupArgs as Vout
  | [], .nil, .nil, _, _, _, _, _ => rfl
  | _ :: _, .cons a as, .cons b bs, m, m', h, mf, hle => by
      simp only [matchArgWith, Option.bind_eq_some_iff] at h
      obtain ⟨m₁, h₁, h₂⟩ := h
      have hle₁ : Mapping.Le m₁ mf :=
        Mapping.Le.trans (matchArgWith_le hmono as bs m₁ m' h₂) hle
      simp only [Expr.lookupArgs]
      rw [hf a b m m₁ h₁ mf hle₁,
        lookupArgs_eq_of_matchArgWith hmono hf as bs m₁ m' h₂ mf hle]

theorem denote_matchVar {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] [DecidableEq d.Ty] [DecidableEq d.Op]
    [∀ t : d.Ty, Inhabited ⟦t⟧] {Γ_in Γ_out Δ_in : Ctxt d}
    (lets : Lets d Γ_in Γ_out) (V : Ctxt.Valuation Γ_in) :
    ∀ {Δ_out : Ctxt d} (matchLets : Lets d Δ_in Δ_out) {t : d.Ty}
      (v : Var Γ_out t) (w : Var Δ_out t) (m m' : Mapping Δ_in Γ_out),
      matchVar lets matchLets v w m = some m' →
      ∀ mf : Mapping Δ_in Γ_out, Mapping.Le m' mf →
      w.lookup (matchLets.denote (mf.mapValuation (lets.denote V)))
        = v.lookup (lets.denote V)
  | _, .nil, _, _, w, _, _, h, mf, hle => by
      have hw := hle _ _ (unifyVars_lookup h)
      simpa [Lets.denote] using Mapping.lookup_mapValuation_of hw
  | _, .var mlets me, _, v, .here, m, m', h, mf, hle => by
      rcases hie : lets.getExpr v with _ | ie
      · simp [matchVar, hie] at h
      · simp only [matchVar, hie] at h
        split at h
        · rename_i hop
          have hargs :
              Expr.lookupArgs
                  (HVector.castTys (congrArg DialectSignature.sig hop) me.args)
                  (mlets.denote (mf.mapValuation (lets.denote V)))
                = Expr.lookupArgs ie.args (lets.denote V) :=
            lookupArgs_eq_of_matchArgWith
              (fun a b m₁ m₂ hh => matchVar_le lets mlets a b m₁ m₂ hh)
              (fun a b m₁ m₂ hh mg hg =>
                denote_matchVar lets V mlets a b m₁ m₂ hh mg hg)
              _ _ _ _ h mf hle
          rw [← Lets.getExpr_denote V lets v ie hie]
          simp only [Lets.denote, Ctxt.Valuation.extend, Var.lookup]
          clear h hie hle
          revert hargs
          obtain ⟨mop, mty, margs⟩ := me
          obtain ⟨iop, ity, iargs⟩ := ie
          change mop = iop at hop
          subst hop
          intro hargs
          have hargs' :
              Expr.lookupArgs margs (mlets.denote (mf.mapValuation (lets.denote V)))
                = Expr.lookupArgs iargs (lets.denote V) := hargs
          exact Expr.denote_eq_of_lookupArgs mty margs iargs _ _ hargs'
        · exact absurd h (by simp)
  | _, .var mlets _, _, v, .there w, m, m', h, mf, hle => by
      simp only [matchVar] at h
      simpa [Lets.denote, Ctxt.Valuation.extend, Var.lookup] using
        denote_matchVar lets V mlets v w m m' h mf hle

/-! ## 15. Which variables a pattern constrains -/

/-- The pattern variables reached from each entry of an argument vector. -/
def Lets.varsOfVec {d : Dialect} {Δ_in Δ_mid : Ctxt d}
    (g : ∀ {t : d.Ty}, Var Δ_mid t → List (MapKey Δ_in)) :
    {l : List d.Ty} → HVector (fun ty => Var Δ_mid ty) l → List (MapKey Δ_in)
  | [], .nil => []
  | _ :: _, .cons a as => g a ++ Lets.varsOfVec g as

/-- The input-context variables the expression tree rooted at `w` reads. -/
def Lets.vars {d : Dialect} [DialectSignature d] {Δ_in : Ctxt d} :
    {Δ_out : Ctxt d} → Lets d Δ_in Δ_out → {t : d.Ty} → Var Δ_out t →
      List (MapKey Δ_in)
  | _, .nil, t, w => [⟨t, w⟩]
  | _, .var mlets me, _, .here => Lets.varsOfVec (Lets.vars mlets) me.args
  | _, .var mlets _, _, .there w => Lets.vars mlets w

/-- The input-context variables a program reads. -/
def Com.vars {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {τ : d.Ty}
    (c : Com d Γ τ) : List (MapKey Γ) :=
  c.toLets.vars c.returnVar

theorem Lets.varsOfVec_castTys {d : Dialect} {Δ_in Δ_mid : Ctxt d}
    (g : ∀ {t : d.Ty}, Var Δ_mid t → List (MapKey Δ_in)) {l l' : List d.Ty}
    (h : l = l') (vs : HVector (fun ty => Var Δ_mid ty) l) :
    Lets.varsOfVec g (HVector.castTys h vs) = Lets.varsOfVec g vs := by
  cases h; rfl

theorem mem_matchArgWith {d : Dialect} [DecidableEq d.Ty] {Δ_in Γ_out Δ_mid : Ctxt d}
    {f : ∀ {t : d.Ty}, Var Γ_out t → Var Δ_mid t → Mapping Δ_in Γ_out →
      Option (Mapping Δ_in Γ_out)}
    {g : ∀ {t : d.Ty}, Var Δ_mid t → List (MapKey Δ_in)}
    (hmono : ∀ {t : d.Ty} (a : Var Γ_out t) (b : Var Δ_mid t) (m m' : Mapping Δ_in Γ_out),
      f a b m = some m' → Mapping.Le m m')
    (hg : ∀ {t : d.Ty} (a : Var Γ_out t) (b : Var Δ_mid t) (m m' : Mapping Δ_in Γ_out),
      f a b m = some m' → ∀ u ∈ g b, (m'.lookup u).isSome) :
    ∀ {l : List d.Ty} (as : HVector (fun ty => Var Γ_out ty) l)
      (bs : HVector (fun ty => Var Δ_mid ty) l) (m m' : Mapping Δ_in Γ_out),
      matchArgWith f as bs m = some m' →
      ∀ u ∈ Lets.varsOfVec g bs, (m'.lookup u).isSome
  | [], .nil, .nil, _, _, _, _, hu => by simp [Lets.varsOfVec] at hu
  | _ :: _, .cons a as, .cons b bs, m, m', h, u, hu => by
      simp only [matchArgWith, Option.bind_eq_some_iff] at h
      obtain ⟨m₁, h₁, h₂⟩ := h
      simp only [Lets.varsOfVec, List.mem_append] at hu
      rcases hu with hu | hu
      · exact (matchArgWith_le hmono as bs m₁ m' h₂).isSome (hg a b m m₁ h₁ u hu)
      · exact mem_matchArgWith hmono hg as bs m₁ m' h₂ u hu

theorem mem_matchVar {d : Dialect} [DialectSignature d] [DecidableEq d.Ty]
    [DecidableEq d.Op] {Γ_in Γ_out Δ_in : Ctxt d} (lets : Lets d Γ_in Γ_out) :
    ∀ {Δ_out : Ctxt d} (matchLets : Lets d Δ_in Δ_out) {t : d.Ty}
      (v : Var Γ_out t) (w : Var Δ_out t) (m m' : Mapping Δ_in Γ_out),
      matchVar lets matchLets v w m = some m' →
      ∀ u ∈ matchLets.vars w, (m'.lookup u).isSome
  | _, .nil, _, _, _, _, _, h, u, hu => by
      simp only [Lets.vars, List.mem_singleton] at hu
      subst hu
      simp [unifyVars_lookup h]
  | _, .var mlets me, _, v, .here, m, m', h, u, hu => by
      rcases hie : lets.getExpr v with _ | ie
      · simp [matchVar, hie] at h
      · simp only [matchVar, hie] at h
        split at h
        · simp only [Lets.vars] at hu
          refine mem_matchArgWith
            (fun a b m₁ m₂ hh => matchVar_le lets mlets a b m₁ m₂ hh)
            (fun a b m₁ m₂ hh => mem_matchVar lets mlets a b m₁ m₂ hh)
            _ _ _ _ h u ?_
          rw [Lets.varsOfVec_castTys]
          exact hu
        · exact absurd h (by simp)
  | _, .var mlets _, _, v, .there w, m, m', h, u, hu => by
      simp only [matchVar] at h
      simp only [Lets.vars] at hu
      exact mem_matchVar lets mlets v w m m' h u hu

theorem Mapping.isTotal_of_matchVar {d : Dialect} [DialectSignature d]
    [DecidableEq d.Ty] [DecidableEq d.Op] {Γ_in Γ_out Δ_in Δ_out : Ctxt d}
    {lets : Lets d Γ_in Γ_out} {matchLets : Lets d Δ_in Δ_out} {t : d.Ty}
    {v : Var Γ_out t} {w : Var Δ_out t} {m : Mapping Δ_in Γ_out}
    (hm : matchVar lets matchLets v w [] = some m)
    (hvars : ∀ (s : d.Ty) (u : Var Δ_in s),
      (⟨s, u⟩ : MapKey Δ_in) ∈ matchLets.vars w) :
    m.IsTotal :=
  fun k => mem_matchVar lets matchLets v w [] m hm k (hvars k.1 k.2)

/-! ## 16. Splitting a program at a position -/

/-- A program split at a position: the bindings up to it, the program after it,
and the variable it binds. -/
structure SplitResult (d : Dialect) [DialectSignature d] (Γ_in : Ctxt d)
    (τ : d.Ty) where
  /-- The context in scope at the position. -/
  {Γ_mid : Ctxt d}
  /-- The type bound at the position. -/
  {midTy : d.Ty}
  /-- The bindings up to and including the position. -/
  top : Lets d Γ_in Γ_mid
  /-- The program continuing after the position. -/
  bot : Com d Γ_mid τ
  /-- The variable bound at the position. -/
  midVar : Var Γ_mid midTy

/-- The split, read as a zipper. -/
def SplitResult.toZipper {d : Dialect} [DialectSignature d] {Γ_in : Ctxt d}
    {τ : d.Ty} (r : SplitResult d Γ_in τ) : Zipper d Γ_in τ :=
  { top := r.top, bot := r.bot }

/-- Walk `pos` bindings of a program into a `Lets` prefix. -/
def splitProgramAtAux {d : Dialect} [DialectSignature d] {Γ₁ : Ctxt d} {τ : d.Ty} :
    (pos : Nat) → {Γ₂ : Ctxt d} → Lets d Γ₁ Γ₂ → Com d Γ₂ τ →
      Option (SplitResult d Γ₁ τ)
  | 0, _, lets, .var e body => some { top := .var lets e, bot := body, midVar := .here }
  | _, _, _, .ret _ => none
  | n + 1, _, lets, .var e body => splitProgramAtAux n (.var lets e) body

/-- Split a program at the `pos`-th binding. -/
def splitProgramAt {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {τ : d.Ty}
    (pos : Nat) (prog : Com d Γ τ) : Option (SplitResult d Γ τ) :=
  splitProgramAtAux pos Lets.nil prog

theorem denote_splitProgramAtAux {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ₁ : Ctxt d} {τ : d.Ty} (V : Ctxt.Valuation Γ₁) :
    ∀ (pos : Nat) {Γ₂ : Ctxt d} (lets : Lets d Γ₁ Γ₂) (prog : Com d Γ₂ τ)
      (res : SplitResult d Γ₁ τ), splitProgramAtAux pos lets prog = some res →
      res.toZipper.denote V = prog.denote (lets.denote V)
  | 0, _, _, .var _ _, res, h => by
      simp only [splitProgramAtAux, Option.some.injEq] at h
      subst h
      rfl
  | 0, _, _, .ret _, _, h => by simp [splitProgramAtAux] at h
  | _ + 1, _, _, .ret _, _, h => by simp [splitProgramAtAux] at h
  | n + 1, _, lets, .var e body, res, h => by
      simp only [splitProgramAtAux] at h
      exact denote_splitProgramAtAux V n (.var lets e) body res h

theorem denote_splitProgramAt {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ : Ctxt d} {τ : d.Ty} (V : Ctxt.Valuation Γ) (pos : Nat)
    (prog : Com d Γ τ) (res : SplitResult d Γ τ)
    (h : splitProgramAt pos prog = some res) :
    res.toZipper.denote V = prog.denote V :=
  denote_splitProgramAtAux V pos Lets.nil prog res h

theorem leakEvents_splitProgramAtAux {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] [DialectLeak d] {Γ₁ : Ctxt d} {τ : d.Ty}
    (V : Ctxt.Valuation Γ₁) :
    ∀ (pos : Nat) {Γ₂ : Ctxt d} (lets : Lets d Γ₁ Γ₂) (prog : Com d Γ₂ τ)
      (res : SplitResult d Γ₁ τ), splitProgramAtAux pos lets prog = some res →
      res.toZipper.leakEvents V = lets.leakEvents V ++ prog.leakEvents (lets.denote V)
  | 0, _, _, .var _ _, res, h => by
      simp only [splitProgramAtAux, Option.some.injEq] at h
      subst h
      simp [SplitResult.toZipper, Zipper.leakEvents, Lets.leakEvents, Lets.denote,
        Com.leakEvents, List.append_assoc]
  | 0, _, _, .ret _, _, h => by simp [splitProgramAtAux] at h
  | _ + 1, _, _, .ret _, _, h => by simp [splitProgramAtAux] at h
  | n + 1, _, lets, .var e body, res, h => by
      simp only [splitProgramAtAux] at h
      rw [leakEvents_splitProgramAtAux V n (.var lets e) body res h]
      simp [Lets.leakEvents, Lets.denote, Com.leakEvents, List.append_assoc]

theorem leakEvents_splitProgramAt {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] [DialectLeak d] {Γ : Ctxt d} {τ : d.Ty} (V : Ctxt.Valuation Γ)
    (pos : Nat) (prog : Com d Γ τ) (res : SplitResult d Γ τ)
    (h : splitProgramAt pos prog = some res) :
    res.toZipper.leakEvents V = prog.leakEvents V :=
  leakEvents_splitProgramAtAux V pos Lets.nil prog res h

/-! ## 17. Rewriting at a position -/

variable {d : Dialect} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d]
  [DecidableEq d.Ty] [DecidableEq d.Op] [∀ t : d.Ty, Inhabited ⟦t⟧]

/-- Search for `lhs` at position `pos` of `target`; on a match, splice `rhs` in
under the matched variable assignment and redirect the matched position to its
result. -/
def rewriteAt {Γ₁ Γ₂ : Ctxt d} {t₁ t₂ : d.Ty} (lhs rhs : Com d Γ₁ t₁)
    (hlhs : ∀ (s : d.Ty) (v : Var Γ₁ s), (⟨s, v⟩ : MapKey Γ₁) ∈ lhs.vars)
    (pos : Nat) (target : Com d Γ₂ t₂) : Option (Com d Γ₂ t₂) :=
  match splitProgramAt pos target with
  | none => none
  | some res =>
      if h : res.midTy = t₁ then
        match hm : matchVar res.top lhs.toLets (Ctxt.Var.castTy h res.midVar)
            lhs.returnVar [] with
        | none => none
        | some m =>
            some (res.toZipper.insertPureCom (Ctxt.Var.castTy h res.midVar)
              (rhs.rename (m.toHom (Mapping.isTotal_of_matchVar hm hlhs)))).toCom
      else none

/-- On a match, the spliced program computes the value the matched position
already held. -/
theorem denote_matched {Γ₁ Γ₂ : Ctxt d} {t₁ t₂ : d.Ty} {lhs rhs : Com d Γ₁ t₁}
    (hcorrect : ∀ V : Ctxt.Valuation Γ₁, lhs.denote V = rhs.denote V)
    {res : SplitResult d Γ₂ t₂} {mv : Var res.Γ_mid t₁} {m : Mapping Γ₁ res.Γ_mid}
    (hm : matchVar res.top lhs.toLets mv lhs.returnVar [] = some m)
    (ht : m.IsTotal) (V : Ctxt.Valuation Γ₂) :
    (rhs.rename (m.toHom ht)).denote (res.top.denote V)
      = mv.lookup (res.top.denote V) := by
  rw [Com.denote_rename, Mapping.comap_toHom_eq_mapValuation, ← hcorrect]
  simpa using
    denote_matchVar res.top V lhs.toLets mv lhs.returnVar [] m hm m (Mapping.Le.rfl m)

omit [DecidableEq d.Op] [∀ t : d.Ty, Inhabited ⟦t⟧] in
/-- On a match with a silent pattern, the spliced program emits no
observation. -/
theorem leakEvents_matched [DialectLeak d] {Γ₁ Γ₂ : Ctxt d} {t₁ t₂ : d.Ty}
    {lhs rhs : Com d Γ₁ t₁}
    (hleak : ∀ V : Ctxt.Valuation Γ₁, rhs.leakEvents V = lhs.leakEvents V)
    (hsilent : ∀ V : Ctxt.Valuation Γ₁, lhs.leakEvents V = [])
    {res : SplitResult d Γ₂ t₂} {m : Mapping Γ₁ res.Γ_mid} (ht : m.IsTotal)
    (V : Ctxt.Valuation Γ₂) :
    (rhs.rename (m.toHom ht)).leakEvents (res.top.denote V) = [] := by
  rw [Com.leakEvents_rename, hleak, hsilent]

theorem denote_rewriteAt {Γ₁ Γ₂ : Ctxt d} {t₁ t₂ : d.Ty} {lhs rhs : Com d Γ₁ t₁}
    (hcorrect : ∀ V : Ctxt.Valuation Γ₁, lhs.denote V = rhs.denote V)
    {hlhs : ∀ (s : d.Ty) (v : Var Γ₁ s), (⟨s, v⟩ : MapKey Γ₁) ∈ lhs.vars}
    {pos : Nat} {target : Com d Γ₂ t₂} {rew : Com d Γ₂ t₂}
    (hrew : rewriteAt lhs rhs hlhs pos target = some rew) (V : Ctxt.Valuation Γ₂) :
    rew.denote V = target.denote V := by
  unfold rewriteAt at hrew
  split at hrew
  · exact absurd hrew (by simp)
  · rename_i res hsp
    split at hrew
    · split at hrew
      · exact absurd hrew (by simp)
      · rename_i m hm
        simp only [Option.some.injEq] at hrew
        subst hrew
        rw [Zipper.denote_toCom,
          Zipper.denote_insertPureCom_eq_of V (denote_matched hcorrect hm _ V)]
        exact denote_splitProgramAt V pos target res hsp
    · exact absurd hrew (by simp)

theorem leakEvents_rewriteAt [DialectLeak d] {Γ₁ Γ₂ : Ctxt d} {t₁ t₂ : d.Ty}
    {lhs rhs : Com d Γ₁ t₁}
    (hcorrect : ∀ V : Ctxt.Valuation Γ₁, lhs.denote V = rhs.denote V)
    (hleak : ∀ V : Ctxt.Valuation Γ₁, rhs.leakEvents V = lhs.leakEvents V)
    (hsilent : ∀ V : Ctxt.Valuation Γ₁, lhs.leakEvents V = [])
    {hlhs : ∀ (s : d.Ty) (v : Var Γ₁ s), (⟨s, v⟩ : MapKey Γ₁) ∈ lhs.vars}
    {pos : Nat} {target : Com d Γ₂ t₂} {rew : Com d Γ₂ t₂}
    (hrew : rewriteAt lhs rhs hlhs pos target = some rew) (V : Ctxt.Valuation Γ₂) :
    rew.leakEvents V = target.leakEvents V := by
  unfold rewriteAt at hrew
  split at hrew
  · exact absurd hrew (by simp)
  · rename_i res hsp
    split at hrew
    · split at hrew
      · exact absurd hrew (by simp)
      · rename_i m hm
        simp only [Option.some.injEq] at hrew
        subst hrew
        rw [Zipper.leakEvents_toCom,
          Zipper.leakEvents_insertPureCom_eq_of V (denote_matched hcorrect hm _ V)
            (leakEvents_matched hleak hsilent _ V)]
        exact leakEvents_splitProgramAt V pos target res hsp
    · exact absurd hrew (by simp)

/-! ## 18. Peephole rewrites -/

/-- A rewrite rule: two programs over a common context that denote the same
function and emit the same observations. -/
structure PeepholeRewrite (d : Dialect) [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] [DialectLeak d] (Γ : Ctxt d) (τ : d.Ty) where
  /-- The pattern to search for. -/
  lhs : Com d Γ τ
  /-- The program to substitute. -/
  rhs : Com d Γ τ
  /-- The two sides denote the same function. -/
  correct : ∀ V : Ctxt.Valuation Γ, lhs.denote V = rhs.denote V
  /-- The two sides emit the same observations. -/
  leak : ∀ V : Ctxt.Valuation Γ, rhs.leakEvents V = lhs.leakEvents V

/-- A rewrite whose pattern emits no observation. -/
def PeepholeRewrite.Silent [DialectLeak d] {Γ : Ctxt d} {τ : d.Ty}
    (pr : PeepholeRewrite d Γ τ) : Prop :=
  ∀ V : Ctxt.Valuation Γ, pr.lhs.leakEvents V = []

/-- Apply a rewrite at a position, leaving the target unchanged when the pattern
does not match or does not constrain every variable of its context. -/
def rewritePeepholeAt [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty}
    (pr : PeepholeRewrite d Γ τ) (pos : Nat) (target : Com d Γ₂ t₂) : Com d Γ₂ t₂ :=
  if hlhs : ∀ (s : d.Ty) (v : Var Γ s), (⟨s, v⟩ : MapKey Γ) ∈ pr.lhs.vars
  then (rewriteAt pr.lhs pr.rhs hlhs pos target).getD target
  else target

theorem denote_rewritePeepholeAt [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty}
    (pr : PeepholeRewrite d Γ τ) (pos : Nat) (target : Com d Γ₂ t₂)
    (V : Ctxt.Valuation Γ₂) :
    (rewritePeepholeAt pr pos target).denote V = target.denote V := by
  unfold rewritePeepholeAt
  split
  · rename_i hlhs
    rcases hr : rewriteAt pr.lhs pr.rhs hlhs pos target with _ | rew
    · simp
    · simpa [hr] using denote_rewriteAt pr.correct hr V
  · rfl

theorem leak_rewritePeepholeAt [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty}
    (pr : PeepholeRewrite d Γ τ) (hs : pr.Silent) (pos : Nat)
    (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂) :
    (rewritePeepholeAt pr pos target).leakEvents V = target.leakEvents V := by
  unfold rewritePeepholeAt
  split
  · rename_i hlhs
    rcases hr : rewriteAt pr.lhs pr.rhs hlhs pos target with _ | rew
    · simp
    · simpa [hr] using leakEvents_rewriteAt pr.correct pr.leak hs hr V
  · rfl

/-! ## 19. Iterating a rewrite -/

/-- Apply a rewrite at position `ix` and later, for at most `fuel` steps. -/
def rewritePeepholeGo [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty} (fuel : Nat)
    (pr : PeepholeRewrite d Γ τ) (ix : Nat) (target : Com d Γ₂ t₂) : Com d Γ₂ t₂ :=
  match fuel with
  | 0 => target
  | fuel + 1 => rewritePeepholeGo fuel pr (ix + 1) (rewritePeepholeAt pr ix target)

/-- Apply a rewrite from position `0`, for at most `fuel` steps. -/
def rewritePeephole [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty} (fuel : Nat)
    (pr : PeepholeRewrite d Γ τ) (target : Com d Γ₂ t₂) : Com d Γ₂ t₂ :=
  rewritePeepholeGo fuel pr 0 target

theorem denote_rewritePeepholeGo [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty} :
    ∀ (fuel : Nat) (pr : PeepholeRewrite d Γ τ) (ix : Nat) (target : Com d Γ₂ t₂)
      (V : Ctxt.Valuation Γ₂),
      (rewritePeepholeGo fuel pr ix target).denote V = target.denote V
  | 0, _, _, _, _ => rfl
  | fuel + 1, pr, ix, target, V => by
      rw [rewritePeepholeGo, denote_rewritePeepholeGo fuel pr (ix + 1) _ V,
        denote_rewritePeepholeAt]

theorem denote_rewritePeephole [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty}
    (fuel : Nat) (pr : PeepholeRewrite d Γ τ) (target : Com d Γ₂ t₂)
    (V : Ctxt.Valuation Γ₂) :
    (rewritePeephole fuel pr target).denote V = target.denote V :=
  denote_rewritePeepholeGo fuel pr 0 target V

theorem leak_rewritePeepholeGo [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty}
    (pr : PeepholeRewrite d Γ τ) (hs : pr.Silent) :
    ∀ (fuel : Nat) (ix : Nat) (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂),
      (rewritePeepholeGo fuel pr ix target).leakEvents V = target.leakEvents V
  | 0, _, _, _ => rfl
  | fuel + 1, ix, target, V => by
      rw [rewritePeepholeGo, leak_rewritePeepholeGo pr hs fuel (ix + 1) _ V,
        leak_rewritePeepholeAt pr hs]

theorem leak_rewritePeephole [DialectLeak d] {Γ Γ₂ : Ctxt d} {τ t₂ : d.Ty}
    (fuel : Nat) (pr : PeepholeRewrite d Γ τ) (hs : pr.Silent)
    (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂) :
    (rewritePeephole fuel pr target).leakEvents V = target.leakEvents V :=
  leak_rewritePeepholeGo pr hs fuel 0 target V

/-! ## 20. Iterating a list of rewrites -/

/-- Apply every rewrite of a list at position `ix` and later, for at most `fuel`
steps. -/
def multiRewritePeepholeAt [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty} (fuel : Nat)
    (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ)) (ix : Nat)
    (target : Com d Γ₂ t₂) : Com d Γ₂ t₂ :=
  match fuel with
  | 0 => target
  | fuel + 1 =>
      multiRewritePeepholeAt fuel prs (ix + 1)
        (prs.foldl (fun acc p => rewritePeepholeAt p.2.2 ix acc) target)

/-- Apply every rewrite of a list from position `0`, for at most `fuel`
steps. -/
def multiRewritePeephole [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty} (fuel : Nat)
    (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ))
    (target : Com d Γ₂ t₂) : Com d Γ₂ t₂ :=
  multiRewritePeepholeAt fuel prs 0 target

theorem denote_foldl_rewritePeepholeAt [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty} :
    ∀ (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ)) (ix : Nat)
      (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂),
      (prs.foldl (fun acc p => rewritePeepholeAt p.2.2 ix acc) target).denote V
        = target.denote V
  | [], _, _, _ => rfl
  | _ :: prs, ix, target, V => by
      simp only [List.foldl_cons]
      rw [denote_foldl_rewritePeepholeAt prs ix _ V, denote_rewritePeepholeAt]

theorem denote_multiRewritePeepholeAt [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty} :
    ∀ (fuel : Nat) (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ))
      (ix : Nat) (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂),
      (multiRewritePeepholeAt fuel prs ix target).denote V = target.denote V
  | 0, _, _, _, _ => rfl
  | fuel + 1, prs, ix, target, V => by
      rw [multiRewritePeepholeAt, denote_multiRewritePeepholeAt fuel prs (ix + 1) _ V,
        denote_foldl_rewritePeepholeAt]

theorem denote_multiRewritePeephole [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty}
    (fuel : Nat) (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ))
    (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂) :
    (multiRewritePeephole fuel prs target).denote V = target.denote V :=
  denote_multiRewritePeepholeAt fuel prs 0 target V

theorem leak_foldl_rewritePeepholeAt [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty} :
    ∀ (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ))
      (_ : ∀ p ∈ prs, PeepholeRewrite.Silent p.2.2) (ix : Nat)
      (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂),
      (prs.foldl (fun acc p => rewritePeepholeAt p.2.2 ix acc) target).leakEvents V
        = target.leakEvents V
  | [], _, _, _, _ => rfl
  | p :: prs, hs, ix, target, V => by
      simp only [List.foldl_cons]
      rw [leak_foldl_rewritePeepholeAt prs
          (fun q hq => hs q (List.mem_cons_of_mem _ hq)) ix _ V,
        leak_rewritePeepholeAt _ (hs p (List.mem_cons_self ..))]

theorem leak_multiRewritePeepholeAt [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty} :
    ∀ (fuel : Nat) (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ))
      (_ : ∀ p ∈ prs, PeepholeRewrite.Silent p.2.2) (ix : Nat)
      (target : Com d Γ₂ t₂) (V : Ctxt.Valuation Γ₂),
      (multiRewritePeepholeAt fuel prs ix target).leakEvents V = target.leakEvents V
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, prs, hs, ix, target, V => by
      rw [multiRewritePeepholeAt,
        leak_multiRewritePeepholeAt fuel prs hs (ix + 1) _ V,
        leak_foldl_rewritePeepholeAt prs hs]

theorem leak_multiRewritePeephole [DialectLeak d] {Γ₂ : Ctxt d} {t₂ : d.Ty}
    (fuel : Nat) (prs : List ((Γ : Ctxt d) × (τ : d.Ty) × PeepholeRewrite d Γ τ))
    (hs : ∀ p ∈ prs, PeepholeRewrite.Silent p.2.2) (target : Com d Γ₂ t₂)
    (V : Ctxt.Valuation Γ₂) :
    (multiRewritePeephole fuel prs target).leakEvents V = target.leakEvents V :=
  leak_multiRewritePeepholeAt fuel prs hs 0 target V


/-! ## 21. A worked rewrite over `catCryptDialect` -/

namespace PeepholeDemo

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)

/-- A default value for each of the dialect's runtime types. -/
instance instInhabitedCryptoDenote : ∀ t : CryptoTy, Inhabited ⟦t⟧
  | .bit => ⟨false⟩
  | .unit => ⟨()⟩
  | .pair a b =>
      ⟨((instInhabitedCryptoDenote a).default, (instInhabitedCryptoDenote b).default)⟩
  | .sum a _ => ⟨.inl (instInhabitedCryptoDenote a).default⟩
  | .sword n => ⟨(0 : BitVec n)⟩
  | .memref n => ⟨((fun _ => 0) : Fin n → BitVec 64)⟩
  | .memrefW w n => ⟨((fun _ => 0) : Fin n → BitVec w)⟩

/-- Observations for `catCryptDialect`: an operation is observable exactly when
it reads a `memref`, so register arithmetic emits nothing. -/
instance instDialectLeak : DialectLeak catCryptDialect where
  Event := CryptoTy
  leakOf op _ :=
    (DialectSignature.sig op).filter
      (fun t => match t with | .memref _ => true | _ => false)

/-- The 64-bit word type. -/
abbrev W : CryptoTy := .sword 64

/-- A context holding one 64-bit word. -/
abbrev G : Ctxt catCryptDialect := [W]

/-- `let z = a - a; ret z`. -/
def subSelf : Com catCryptDialect G W :=
  .var { op := .bvSub 64, retTy_eq := rfl, args := .cons .here (.cons .here .nil) }
    (.ret .here)

/-- `let z = a ^^^ a; ret z`. -/
def xorSelf : Com catCryptDialect G W :=
  .var { op := .bvXor 64, retTy_eq := rfl, args := .cons .here (.cons .here .nil) }
    (.ret .here)

/-- The zeroing idiom `a - a ↦ a ^^^ a`, as a `PeepholeRewrite`. -/
def subSelfToXorSelf : PeepholeRewrite catCryptDialect G W where
  lhs := subSelf
  rhs := xorSelf
  correct := by
    intro V
    cases V
    rename_i x V'
    cases V'
    have hbv : ∀ y : BitVec 64, y - y = y ^^^ y := by intro y; simp
    exact hbv x
  leak := fun _ => rfl

/-- Neither side of the rewrite reads a `memref`, so the pattern is silent. -/
theorem subSelfToXorSelf_silent : subSelfToXorSelf.Silent := fun _ => rfl

/-- Every variable of the pattern's context occurs in the pattern, which is the
side condition `rewritePeepholeAt` checks. -/
example : ∀ (s : CryptoTy) (v : Ctxt.Var G s),
    (⟨s, v⟩ : MapKey G) ∈ subSelfToXorSelf.lhs.vars := by
  intro s v
  cases v with
  | here => exact List.Mem.head _
  | there v' => cases v'

/-- A target program containing the self-subtract. -/
def demoTarget : Com catCryptDialect G W :=
  .var { op := .bvSub 64, retTy_eq := rfl, args := .cons .here (.cons .here .nil) }
    (.ret .here)

example (V : Ctxt.Valuation G) :
    (rewritePeepholeAt subSelfToXorSelf 0 demoTarget).denote V = demoTarget.denote V :=
  denote_rewritePeepholeAt subSelfToXorSelf 0 demoTarget V

example (V : Ctxt.Valuation G) :
    (rewritePeepholeAt subSelfToXorSelf 0 demoTarget).leakEvents V
      = demoTarget.leakEvents V :=
  leak_rewritePeepholeAt subSelfToXorSelf subSelfToXorSelf_silent 0 demoTarget V

example (V : Ctxt.Valuation G) :
    (rewritePeephole 4 subSelfToXorSelf demoTarget).denote V = demoTarget.denote V :=
  denote_rewritePeephole 4 subSelfToXorSelf demoTarget V

end PeepholeDemo

end CatCrypt.Crypto.SecureCompilation.VIR
