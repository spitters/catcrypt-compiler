/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

/-!
# Verified translation validation for the `Com jasminDialect` optimiser

A **verified translation-validation (TV) checker** for the typed VIR
`jasminDialect`. The intended use is an *untrusted* optimizer oracle — an
external rewrite engine, or a `gcc`/LLVM-`O3`-class optimizer that is reflected
back into a candidate `Com jasminDialect Γ t` — proposes an optimized program,
and this checker either *certifies* that the candidate denotes the same function
as the input, or *rejects*. Soundness of the optimizer itself is never trusted:
only the checker is in the TCB, and the checker is verified here.

## What is checked

`tvCheck c c'` is a decidable Boolean test that returns `true` only on a
relation we prove implies full denotational equivalence. It accepts the
candidate `c'` when *either*

* `c'` is structurally the input `c` (the optimizer returned the program
  unchanged — vacuously equivalent), or
* `c'` is structurally the output of the already-verified local peephole pass
  `Peephole.peepCom c` (the candidate matches the canonicalisation that the
  in-tree verified pass would produce).

Structural equality is decided by `comEqB`, a homogeneous Boolean equality on
`Com jasminDialect Γ t` (both sides already share the context `Γ` and return
type `t`, since that is the `tvCheck` signature). The only dependent subtlety is
the existential intermediate type at each `var` binder, handled by deciding
`JasminTy` equality (which has `DecidableEq`) and casting.

## What is proved

* `comEqB_sound` — `comEqB c c' = true → ∀ V, c'.denote V = c.denote V`. An
  induction over the `Com` let-chain; **not** `rfl`.
* `tvCheck_sound` — the headline soundness theorem:
  `tvCheck c c' = true → ∀ V, c'.denote V = c.denote V`. Composes
  `comEqB_sound` with the verified `Peephole.peepCom_denote`. The checker is
  *incomplete* (it certifies only this conservative relation), but it is
  **sound**: it never certifies a candidate that changes the denotation.

This is the base verified-TV checker: a global-minimum optimisation path in which
the search/rewrite is delegated to an untrusted oracle and only the equivalence
check is trusted. Widening the accepted relation (more verified rewrites, an
equality-saturation witness, observational refinement) extends the checker
without enlarging the TCB, as long as each extension carries its own soundness
lemma.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.TranslationValidation

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## §1  Decidable structural equality of expressions

An `Expr jasminDialect Γ t` is an op (with `DecidableEq`), a proof that its
return type is `t` (proof-irrelevant — ignored), and an `HVector` of argument
variables. We compare the op and the arguments. -/

/-- Boolean equality of two argument `HVector`s of the *same* type list. The
`Ctxt.Var` entries are compared with the verified `varEq`. -/
def argsEqB {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} →
    HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var Γ ty) tys → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons a as, .cons b bs => varEq a b && argsEqB as bs

/-- `argsEqB` is sound: equal-by-`argsEqB` arg vectors look up to the same
denotation under any valuation. -/
theorem argsEqB_sound {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy}
      (as bs : HVector (fun ty => Ctxt.Var Γ ty) tys),
      argsEqB as bs = true →
      ∀ V : Ctxt.Valuation Γ, Expr.lookupArgs as V = Expr.lookupArgs bs V := by
  intro tys
  induction tys with
  | nil => intro as bs _ V; cases as; cases bs; rfl
  | cons ty rest ih =>
      intro as bs
      cases as with
      | cons a as =>
        cases bs with
        | cons b bs =>
          intro h V
          rw [show argsEqB (HVector.cons a as) (HVector.cons b bs)
                = (varEq a b && argsEqB as bs) from rfl, Bool.and_eq_true] at h
          obtain ⟨ha, has⟩ := h
          have hab : a = b := varEq_sound a b ha
          subst hab
          rw [show Expr.lookupArgs (HVector.cons a as) V
                = HVector.cons (Ctxt.Var.lookup a V) (Expr.lookupArgs as V) from rfl,
              show Expr.lookupArgs (HVector.cons a bs) V
                = HVector.cons (Ctxt.Var.lookup a V) (Expr.lookupArgs bs V) from rfl,
              ih as bs has V]

/-- Boolean equality of two expressions of the same context and return type:
same op, same arguments. The `retTy_eq` proof fields are irrelevant. -/
def exprEqB {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e e' : Expr jasminDialect Γ t) : Bool :=
  if h : e.op = e'.op then
    argsEqB e.args (h ▸ e'.args)
  else false

/-- `exprEqB` is sound: equal-by-`exprEqB` expressions denote the same value. -/
theorem exprEqB_sound {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e e' : Expr jasminDialect Γ t) (h : exprEqB e e' = true)
    (V : Ctxt.Valuation Γ) :
    e'.denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  rcases e' with ⟨op', hop', args'⟩
  simp only [exprEqB] at h
  by_cases hoo : op = op'
  · subst hoo
    simp only [dif_pos] at h
    have hargs : Expr.lookupArgs args V = Expr.lookupArgs args' V :=
      argsEqB_sound args args' h V
    subst hop
    cases hop'
    simp only [Expr.denote, hargs]
  · simp only [dif_neg hoo] at h
    exact (Bool.false_ne_true h).elim

/-! ## §2  Decidable structural equality of `Com`

Homogeneous in the outer context and return type (the `tvCheck` signature pins
them); the only dependent step is the existential intermediate type at each
`var`, handled by `decEq` on `JasminTy` and a cast. -/

/-- Boolean structural equality of two programs with the same context and return
type. At a `var` binder we first decide equality of the existential intermediate
type, then compare the bound expression and recurse into the body. -/
def comEqB {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Com jasminDialect Γ t → Bool
  | .ret v, .ret v' => varEq v v'
  | .var (t := a) e body, .var (t := a') e' body' =>
      if h : a = a' then
        exprEqB e (h ▸ e') && comEqB body (h ▸ body')
      else false
  | _, _ => false

/-- **Soundness of `comEqB`.** If `comEqB c c' = true` then `c'` denotes the
same function as `c`, for every valuation. An induction over the let
chain — **not** `rfl`. -/
theorem comEqB_sound {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c c' : Com jasminDialect Γ t),
      comEqB c c' = true → ∀ V : Ctxt.Valuation Γ, c'.denote V = c.denote V := by
  intro c
  induction c with
  | ret v =>
      intro c' h V
      cases c' with
      | ret v' => simp only [comEqB] at h; rw [varEq_sound v v' h]
      | var e' body' => simp [comEqB] at h
  | var e body ih =>
      intro c' h V
      cases c' with
      | ret v' => simp [comEqB] at h
      | var e' body' =>
          simp only [comEqB] at h
          split at h
          · rename_i hty
            subst hty
            rw [Bool.and_eq_true] at h
            obtain ⟨he, hb⟩ := h
            simp only [Com.denote]
            rw [exprEqB_sound e e' he V]
            exact ih body' hb (V.extend (e.denote V))
          · exact (Bool.false_ne_true h).elim

/-! ## §3  The translation-validation checker -/

/-- **The verified TV checker.** Accepts the candidate `c'` (output of an
untrusted optimizer oracle) against the input `c` when `c'` is structurally
either `c` itself or the verified peephole canonicalisation `peepCom c`. Returns
`true` only on a relation that `tvCheck_sound` proves implies denotational
equivalence. Decidable, hence executable as a checker. -/
def tvCheck {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c c' : Com jasminDialect Γ t) : Bool :=
  comEqB c c' || comEqB (peepCom c) c'

/-- **Soundness of the TV checker.** If `tvCheck c c' = true`, the
candidate `c'` denotes the same function as the input `c`, for every valuation.
The optimizer that produced `c'` is *not* trusted: this theorem certifies the
candidate purely from the checker's `true` result, by composing `comEqB_sound`
with the verified `Peephole.peepCom_denote`. Incomplete (only the conservative
relation is accepted) but never unsound. -/
theorem tvCheck_sound {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c c' : Com jasminDialect Γ t) (h : tvCheck c c' = true) :
    ∀ V : Ctxt.Valuation Γ, c'.denote V = c.denote V := by
  intro V
  simp only [tvCheck, Bool.or_eq_true] at h
  rcases h with h | h
  · exact comEqB_sound c c' h V
  · rw [comEqB_sound (peepCom c) c' h V, peepCom_denote c V]

/-! ## §4  Self-contained validation

Two demos exercising both arms of the checker, reusing `Peephole.demoSelfSub`
(`x ↦ x - x`, whose peephole canonicalisation is the `xor x x` zeroing idiom). -/

/-- **Accept (identity arm).** The optimizer that returns its input unchanged is
certified equivalent. -/
example : tvCheck demoSelfSub demoSelfSub = true := by decide

/-- **Accept (peephole arm).** A candidate equal to the verified peephole
output (`x - x ↦ xor x x`) is certified equivalent. -/
example :
    tvCheck demoSelfSub
      (Com.var (binE .xor (Ctxt.Var.here) (Ctxt.Var.here)) (.ret .here)) = true := by
  decide

/-- The accepted peephole candidate denotes the same function as the
input (both map `x` to `0`) — the soundness theorem applied to the demo. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (Com.var (binE .xor (Ctxt.Var.here) (Ctxt.Var.here)) (.ret .here)).denote V
      = demoSelfSub.denote V :=
  tvCheck_sound demoSelfSub _ (by decide) V

end CatCrypt.Crypto.Optimizer.TranslationValidation
