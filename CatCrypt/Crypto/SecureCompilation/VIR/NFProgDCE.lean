/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg

/-!
# Partial renaming and dead-binding elimination on `NFProg`

A partial renaming `PRen Γ Δ` sends each variable of `Γ` to a variable of `Δ` or to
`none`. `NFProg.rename?` applies one to a program and is `none` when the program reads
a variable the renaming drops. The strengthening `PRen.drop` drops the newest
binding, so `NFProg.rename? PRen.drop k` is the continuation `k` without its bound
variable, when `k` does not read it.

`NFProg.dce` removes every let-binding whose continuation, after the removal inside
it, does not read the bound variable. The denotation is in `Option`, so a removed
binding may be one that fails; the pass refines the denotation: a run of the source
to `some out` is a run of the result to `some out` (`NFProg.denote_dce`).

Removing the frame of a loop, dropping a zero initialisation and binding a literal at
its use are choices of the lowering of `NFProg` to `LowCT`, not passes on `NFProg`.
`NFProg.dce` is the pass on `NFProg` between the front `impToNF` and the readback
`nfToImp`; the rewritings `fuseMulHiT` and `stripArrTailT` act on the typed body before
the front.

## Main definitions

* `PRen`, `PRen.lift`, `PRen.liftApp`, `PRen.drop` — partial renamings.
* `PRen.Agrees` — a partial renaming relates two valuations.
* `NFProg.rename?` — a partial renaming applied to a program.
* `NFProg.dce` — dead-binding elimination.

## Main results

* `PRen.agrees_lift`, `PRen.agrees_liftApp`, `PRen.agrees_drop` — the relation
  under the liftings and at the strengthening.
* `NFProg.denote_rename?` — a renamed program denotes as the source at related
  valuations.
* `NFProg.foldlM_some_mono`, `NFProg.whileIter_some_mono` — an `Option` fold and an
  exit-flag iteration keep a `some` result under a step that refines.
* `NFProg.denote_dce` — dead-binding elimination refines the denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## 1. Partial renamings -/

/-- A partial renaming from `Γ` to `Δ`: each variable to a variable of the same type,
    or `none`. -/
abbrev PRen {d : Dialect} (Γ Δ : Ctxt d) : Type _ := ∀ {t : d.Ty}, Var Γ t → Option (Var Δ t)

namespace PRen

variable {d : Dialect}

/-- A partial renaming under one more binding, sending the new variable to itself. -/
def lift {Γ Δ : Ctxt d} {s : d.Ty} (f : PRen Γ Δ) : PRen (s :: Γ) (s :: Δ)
  | _, .here => some .here
  | _, .there v => (f v).map .there

/-- A partial renaming under the bindings `cs`, sending each of them to itself. -/
def liftApp {Γ Δ : Ctxt d} : (cs : List d.Ty) → PRen Γ Δ → PRen (cs ++ Γ) (cs ++ Δ)
  | [], f => f
  | _ :: cs, f => lift (liftApp cs f)

/-- The strengthening: the newest binding dropped, every other variable shifted. -/
def drop {Γ : Ctxt d} {s : d.Ty} : PRen (s :: Γ) Γ
  | _, .here => none
  | _, .there v => some v

variable [TyDenote d.Ty]

/-- The partial renaming `f` relates the valuations `V` and `W`: a variable `f` keeps
    reads in `W` what it reads in `V`. -/
def Agrees {Γ Δ : Ctxt d} (f : PRen Γ Δ) (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ {t : d.Ty} (v : Var Γ t) (v' : Var Δ t), f v = some v' → v'.lookup W = v.lookup V

/-- The lifted renaming relates the valuations extended by one value. -/
theorem agrees_lift {Γ Δ : Ctxt d} {s : d.Ty} {f : PRen Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : Agrees f V W) (x : ⟦s⟧) :
    Agrees (lift (s := s) f) (V.extend x) (W.extend x) := by
  intro t v v' hv
  cases v with
  | here =>
      simp only [lift, Option.some.injEq] at hv
      subst hv
      rfl
  | there v =>
      simp only [lift, Option.map_eq_some_iff] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact h v w hw

/-- The renaming lifted under `cs` relates the valuations extended by one tuple. -/
theorem agrees_liftApp {Γ Δ : Ctxt d} {f : PRen Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : Agrees f V W) :
    (cs : List d.Ty) → (A : Valuation cs) →
    Agrees (liftApp cs f) (hvAppend A V) (hvAppend A W)
  | [], .nil => h
  | _ :: cs, .cons a A => agrees_lift (agrees_liftApp h cs A) a

/-- The strengthening relates a valuation extended by one value to the valuation. -/
theorem agrees_drop {Γ : Ctxt d} {s : d.Ty} (V : Valuation Γ) (x : ⟦s⟧) :
    Agrees (drop (s := s)) (V.extend x) V := by
  intro t v v' hv
  cases v with
  | here => simp [drop] at hv
  | there v =>
      simp only [drop, Option.some.injEq] at hv
      subst hv
      rfl

end PRen

/-! ## 2. Renaming variables, expressions and programs -/

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]

/-- A partial renaming applied to a vector of variables. -/
def PRen.vars? {Γ Δ : Ctxt d} (f : PRen Γ Δ) : {ts : List d.Ty} →
    HVector (fun t => Var Γ t) ts → Option (HVector (fun t => Var Δ t) ts)
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (f v).bind fun v' => (PRen.vars? f vs).map (.cons v')

omit [DialectSignature d] in
/-- Renamed variables read in `W` what the source variables read in `V`. -/
theorem PRen.lookupArgs_vars? {Γ Δ : Ctxt d} {f : PRen Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : PRen.Agrees f V W) : {ts : List d.Ty} →
    (vs : HVector (fun t => Var Γ t) ts) → {ws : HVector (fun t => Var Δ t) ts} →
    PRen.vars? f vs = some ws → Expr.lookupArgs ws W = Expr.lookupArgs vs V
  | [], .nil, _, hw => by
      simp only [PRen.vars?, Option.some.injEq] at hw
      subst hw
      rfl
  | _ :: _, .cons v vs, _, hw => by
      simp only [PRen.vars?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hw
      obtain ⟨v', hv, ws', hws, rfl⟩ := hw
      show HVector.cons (v'.lookup W) (Expr.lookupArgs ws' W) = _
      rw [h v v' hv, PRen.lookupArgs_vars? h vs hws]
      rfl

/-- A partial renaming applied to an expression. -/
def Expr.rename? {Γ Δ : Ctxt d} {t : d.Ty} (f : PRen Γ Δ) (e : Expr d Γ t) :
    Option (Expr d Δ t) :=
  (PRen.vars? f e.args).map fun args => { op := e.op, retTy_eq := e.retTy_eq, args }

/-- A renamed expression denotes in `W` as the source in `V`. -/
theorem Expr.denoteM_rename? {M : Type → Type} [DialectDenoteM d M] {Γ Δ : Ctxt d}
    {t : d.Ty} {f : PRen Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (h : PRen.Agrees f V W) (e : Expr d Γ t) {e' : Expr d Δ t}
    (he : Expr.rename? f e = some e') : e'.denoteM (M := M) W = e.denoteM V := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  obtain ⟨op, rfl, eargs⟩ := e
  simp only [Expr.denoteM]
  rw [PRen.lookupArgs_vars? h eargs hargs]

variable [HasWord64 d] [HasBoolBit d]

namespace NFProg

/-- A partial renaming applied to a program: `none` when the program reads a variable
    the renaming drops. -/
def rename? : {Γ Δ : Ctxt d} → {ts : List d.Ty} → PRen Γ Δ → NFProg d Γ ts →
    Option (NFProg d Δ ts)
  | _, _, _, f, .ret vs => (PRen.vars? f vs).map .ret
  | _, _, _, f, .var e k =>
      (Expr.rename? f e).bind fun e' => (rename? (PRen.lift f) k).map (.var e')
  | _, _, _, f, .forLoop (cs := cs) count inits body k =>
      (f count).bind fun c' => (PRen.vars? f inits).bind fun i' =>
        (rename? (PRen.liftApp cs (PRen.lift f)) body).bind fun b' =>
          (rename? (PRen.liftApp cs f) k).map fun k' => .forLoop c' i' b' k'
  | _, _, _, f, .ifThenElse (rs := rs) cond thn els k =>
      (f cond).bind fun c' => (rename? f thn).bind fun t' => (rename? f els).bind fun e' =>
        (rename? (PRen.liftApp rs f) k).map fun k' => .ifThenElse c' t' e' k'
  | _, _, _, f, .whileLoop (cs := cs) inits body k =>
      (PRen.vars? f inits).bind fun i' => (rename? (PRen.liftApp cs f) body).bind fun b' =>
        (rename? (PRen.liftApp cs f) k).map fun k' => .whileLoop i' b' k'

variable [DialectDenoteM d Option]

/-- **A renamed program denotes as the source.** When `rename? f p = some p'` and `f`
    relates `V` to `W`, `p'` denotes at `W` what `p` denotes at `V`. -/
theorem denote_rename? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {p' : NFProg d Δ ts} {V : Valuation Γ}
      {W : Valuation Δ}, rename? f p = some p' → PRen.Agrees f V W →
      ∀ fuel, p'.denote fuel W = p.denote fuel V := by
  induction p with
  | ret vs =>
      intro Δ f p' V W hp h fuel
      simp only [rename?, Option.map_eq_some_iff] at hp
      obtain ⟨ws, hws, rfl⟩ := hp
      simp only [denote, PRen.lookupArgs_vars? h vs hws]
  | var e k ih =>
      intro Δ f p' V W hp h fuel
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨e', he, k', hk, rfl⟩ := hp
      simp only [denote, Expr.denoteM_rename? h e he]
      congr 1
      funext x
      exact ih hk (PRen.agrees_lift h x) fuel
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' V W hp h fuel
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨c', hc, i', hi, b', hb, k', hk, rfl⟩ := hp
      simp only [denote, h count c' hc, PRen.lookupArgs_vars? h inits hi]
      have hbody : (fun acc i => b'.denote fuel
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) W))) =
          (fun acc i => body.denote fuel
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) V))) := by
        funext acc i
        exact ihb hb (PRen.agrees_liftApp (PRen.agrees_lift h _) _ acc) fuel
      rw [hbody]
      congr 1
      funext acc
      exact ihk hk (PRen.agrees_liftApp h _ acc) fuel
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' V W hp h fuel
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨c', hc, t', ht, e', he, k', hk, rfl⟩ := hp
      simp only [denote, h cond c' hc, iht ht h fuel, ihe he h fuel]
      congr 1
      funext r
      exact ihk hk (PRen.agrees_liftApp h _ r) fuel
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' V W hp h fuel
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨i', hi, b', hb, k', hk, rfl⟩ := hp
      simp only [denote, PRen.lookupArgs_vars? h inits hi]
      have hbody : (fun acc => b'.denote fuel (hvAppend acc W)) =
          (fun acc => body.denote fuel (hvAppend acc V)) := by
        funext acc
        exact ihb hb (PRen.agrees_liftApp h _ acc) fuel
      rw [hbody]
      congr 1
      funext acc
      exact ihk hk (PRen.agrees_liftApp h _ acc) fuel

/-! ## 3. Dead-binding elimination -/

/-- **Dead-binding elimination.** A let-binding whose continuation, after the removal
    inside it, does not read the bound variable is removed; the pass descends into
    every region. -/
def dce : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → NFProg d Γ ts
  | _, _, .ret vs => .ret vs
  | _, _, .var e k =>
      match rename? PRen.drop (dce k) with
      | some k' => k'
      | none => .var e (dce k)
  | _, _, .forLoop count inits body k => .forLoop count inits (dce body) (dce k)
  | _, _, .ifThenElse cond thn els k => .ifThenElse cond (dce thn) (dce els) (dce k)
  | _, _, .whileLoop inits body k => .whileLoop inits (dce body) (dce k)

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] in
/-- An `Option` fold keeps a `some` result when each step `g` refines the step `f`. -/
theorem foldlM_some_mono {α β : Type} {f g : β → α → Option β}
    (hfg : ∀ b i b', f b i = some b' → g b i = some b') :
    ∀ (l : List α) (b r : β), l.foldlM f b = some r → l.foldlM g b = some r
  | [], _, _, h => h
  | i :: l, b, r, h => by
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨b', hb', hr⟩ := h
      exact ⟨b', hfg b i b' hb', foldlM_some_mono hfg l b' r hr⟩

omit [DialectSignature d] [HasWord64 d] [DialectDenoteM d Option] in
/-- An exit-flag iteration keeps a `some` result when the step `g` refines the step
    `f`. -/
theorem whileIter_some_mono {cs : List d.Ty}
    {f g : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs))}
    (hfg : ∀ a r, f a = some r → g a = some r) :
    ∀ (n : Nat) (a r : Valuation cs), whileIter f n a = some r → whileIter g n a = some r
  | 0, _, _, h => by simp [whileIter] at h
  | n + 1, a, r, h => by
      simp only [whileIter, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨s, hs, hr⟩ := h
      refine ⟨s, hfg a s hs, ?_⟩
      split at hr
      · rw [if_pos ‹_›]; exact whileIter_some_mono hfg n _ _ hr
      · rw [if_neg ‹_›]; exact hr

/-- **Dead-binding elimination refines the denotation.** A run of `p` to `some out` at
    any fuel is a run of `dce p` to `some out` at that fuel. -/
theorem denote_dce {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {fuel : Nat} {V : Valuation Γ} {out : Valuation ts},
      p.denote fuel V = some out → (dce p).denote fuel V = some out := by
  induction p with
  | ret vs => intro fuel V out h; exact h
  | var e k ih =>
      intro fuel V out h
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, hk⟩ := h
      have hk' := ih hk
      simp only [dce]
      split
      · rename_i k' hr
        rw [denote_rename? (dce k) hr (PRen.agrees_drop V x) fuel]
        exact hk'
      · simp only [denote, hx, Option.bind_eq_bind, Option.bind_some]
        exact hk'
  | forLoop count inits body k ihb ihk =>
      intro fuel V out h
      simp only [dce, denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨acc, hacc, hk⟩ := h
      exact ⟨acc, foldlM_some_mono (fun _ _ _ hb => ihb hb) _ _ _ hacc, ihk hk⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro fuel V out h
      simp only [dce, denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨r, hr, hk⟩ := h
      refine ⟨r, ?_, ihk hk⟩
      split at hr
      · rw [if_pos ‹_›]; exact iht hr
      · rw [if_neg ‹_›]; exact ihe hr
  | whileLoop inits body k ihb ihk =>
      intro fuel V out h
      simp only [dce, denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨acc, hacc, hk⟩ := h
      exact ⟨acc, whileIter_some_mono (fun _ _ hb => ihb hb) _ _ _ hacc, ihk hk⟩

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
