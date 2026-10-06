/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Category.KleisliCat
public import CatCrypt.Crypto.Hax.NFInline

/-!
# The category of regions of a dialect, at denotations

For a dialect `d` the objects of `Region d` are the type lists of `d`. A morphism from `Γ` to
`ts` is a class of structured programs `NFProg d Γ ts` under `Region.DenoteEq`: two programs
are identified when they denote the same partial function on valuations at every fuel.

Composition is the splice `NFProg.seq?` of `Hax/NFInline.lean`. For `p : NFProg d Γ ts` and
`q : NFProg d ts us`, the continuation is `q` weakened to the context `ts ++ Γ` along
`PRen.inl`, and the splice is taken at the identity renaming of `Γ` for the body and for the
continuation's enclosing context. A renaming is total (`PRen.Total`) when it keeps every
variable; `NFProg.rename?` and `NFProg.seq?` succeed at total renamings, so `NFProg.seq` is a
total operation. The identity is the return `ret (allVars Γ)` of every variable.

`NFProg.denote_seq?` states the denotation of a splice at one fuel shared by the body, the
continuation and the result. Composition therefore respects `Region.DenoteEq` in both
arguments, and the unit and associativity laws are the monad laws of `Option` at each fuel.

The denotation at a fuel is a functor into the Kleisli category of `Option`
(`Region.denoteFunctor`), and the family of these functors over all fuels is jointly faithful
(`Region.hom_ext_denoteFunctor`).

## Main definitions

* `PRen.Total` — the renamings that keep every variable.
* `PRen.inl` — the renaming of `Γ` into `Γ ++ Δ`.
* `NFProg.weaken` — a program over `ts` as a program over `ts ++ Γ`.
* `NFProg.seq` — the composition of two programs, by the splice at identity renamings.
* `Region`, `Region.DenoteEq`, `Region.Hom`, `Region.Hom.mk`, `Region.Hom.comp` — the objects,
  the denotational equality, the morphisms, the class of a program and the composition.
* `Region.instCategory` — the category of regions.
* `Region.denoteFunctor` — the denotation at a fuel, into `KleisliCat Option`.

## Main results

* `PRen.vars?_isSome_of_total`, `Expr.rename?_isSome_of_total`,
  `NFProg.rename?_isSome_of_total`, `NFProg.seq?_isSome_of_total` — renaming and the splice
  succeed at total renamings.
* `NFProg.denote_weaken`, `NFProg.denote_seq` — the denotations of a weakened program and of a
  composition.
* `NFProg.denote_ret_seq`, `NFProg.denote_seq_ret`, `NFProg.denote_seq_assoc` — the unit and
  associativity laws of the composition, at denotations.
* `Region.mk_comp_mk`, `Region.id_eq_mk` — composition and identity on classes of programs.
* `Region.denoteFunctor_map_mk` — the functor on the class of a program.
* `Region.hom_ext_denoteFunctor` — two morphisms with the same image at every fuel are equal.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend inlHom lookup_inlHom)

/-! ## 1. Total renamings -/

namespace PRen

variable {d : Dialect}

/-- A partial renaming is total when it keeps every variable. -/
def Total {Γ Δ : Ctxt d} (f : PRen Γ Δ) : Prop := ∀ {t : d.Ty} (v : Var Γ t), (f v).isSome

/-- The renaming of `Γ` into `Γ ++ Δ`. -/
def inl {Γ : Ctxt d} (Δ : Ctxt d) : PRen Γ (Γ ++ Δ) := fun v => some (inlHom Δ v)

/-- The identity renaming is total. -/
theorem total_id {Γ : Ctxt d} : Total (PRen.id (Γ := Γ)) := fun _ => rfl

/-- The renaming of `Γ` into `Γ ++ Δ` is total. -/
theorem total_inl {Γ : Ctxt d} (Δ : Ctxt d) : Total (inl (Γ := Γ) Δ) := fun _ => rfl

/-- A total renaming is total under one more binding. -/
theorem total_lift {Γ Δ : Ctxt d} {s : d.Ty} {f : PRen Γ Δ} (h : Total f) :
    Total (lift (s := s) f) := by
  intro t v
  cases v with
  | here => rfl
  | there v => simp only [lift, Option.isSome_map, h v]

/-- A total renaming is total under the bindings `cs`. -/
theorem total_liftApp {Γ Δ : Ctxt d} {f : PRen Γ Δ} (h : Total f) :
    (cs : List d.Ty) → Total (liftApp cs f)
  | [] => h
  | _ :: cs => total_lift (total_liftApp h cs)

/-- A total renaming followed by a shift is total. -/
theorem total_shift {Γ₀ Γ : Ctxt d} {θ : PRen Γ₀ Γ} (cs : List d.Ty) (h : Total θ) :
    Total (shift cs θ) := by
  intro t v
  simp only [shift, Option.isSome_map, h v]

/-- The renaming to returned variables, followed by a total renaming, is total. -/
theorem total_appendVars {Γ₀ Γ : Ctxt d} {θ : PRen Γ₀ Γ} (h : Total θ) : {rs : List d.Ty} →
    (ws : HVector (fun t => Var Γ t) rs) → Total (appendVars θ ws)
  | [], .nil => h
  | _ :: _, .cons _ ws => by
      intro v
      cases v with
      | here => rfl
      | there v => exact total_appendVars h ws v

/-- A total renaming renames every vector of variables. -/
theorem vars?_isSome_of_total {Γ Δ : Ctxt d} {f : PRen Γ Δ} (h : Total f) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) → (PRen.vars? f vs).isSome
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      obtain ⟨v', hv⟩ := Option.isSome_iff_exists.mp (h v)
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (vars?_isSome_of_total h vs)
      simp only [PRen.vars?, hv, hws, Option.bind_some, Option.map_some, Option.isSome_some]

variable [TyDenote d.Ty]

/-- The renaming of `Γ` into `Γ ++ Δ` relates a valuation to its extension by a valuation of
    `Δ`. -/
theorem agrees_inl {Γ Δ : Ctxt d} (A : Valuation Γ) (B : Valuation Δ) :
    Agrees (inl (Γ := Γ) Δ) A (hvAppend A B) := by
  intro t v v' hv
  simp only [inl, Option.some.injEq] at hv
  subst hv
  exact lookup_inlHom B v A

end PRen

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]

omit [TyDenote d.Ty] in
/-- A total renaming renames every expression. -/
theorem Expr.rename?_isSome_of_total {Γ Δ : Ctxt d} {t : d.Ty} {f : PRen Γ Δ}
    (h : PRen.Total f) (e : Expr d Γ t) : (Expr.rename? f e).isSome := by
  simp only [Expr.rename?, Option.isSome_map]
  exact PRen.vars?_isSome_of_total h e.args

variable [HasWord64 d] [HasBoolBit d]

/-! ## 2. Renaming and the splice at total renamings -/

namespace NFProg

/-- **A total renaming renames every program.** -/
theorem rename?_isSome_of_total {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ}, PRen.Total f → (rename? f p).isSome := by
  induction p with
  | ret vs =>
      intro Δ f h
      simp only [rename?, Option.isSome_map]
      exact PRen.vars?_isSome_of_total h vs
  | var e k ih =>
      intro Δ f h
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp (Expr.rename?_isSome_of_total h e)
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ih (PRen.total_lift h))
      simp only [rename?, he, hk, Option.bind_some, Option.map_some, Option.isSome_some]
  | forLoop count inits body k ihb ihk =>
      intro Δ f h
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (h count)
      obtain ⟨i', hi⟩ := Option.isSome_iff_exists.mp (PRen.vars?_isSome_of_total h inits)
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ihb (PRen.total_liftApp (PRen.total_lift h) _))
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk (PRen.total_liftApp h _))
      simp only [rename?, hc, hi, hb, hk, Option.bind_some, Option.map_some,
        Option.isSome_some]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f h
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (h cond)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (iht h)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp (ihe h)
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk (PRen.total_liftApp h _))
      simp only [rename?, hc, ht, he, hk, Option.bind_some, Option.map_some,
        Option.isSome_some]
  | whileLoop inits body k ihb ihk =>
      intro Δ f h
      obtain ⟨i', hi⟩ := Option.isSome_iff_exists.mp (PRen.vars?_isSome_of_total h inits)
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp (ihb (PRen.total_liftApp h _))
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk (PRen.total_liftApp h _))
      simp only [rename?, hi, hb, hk, Option.bind_some, Option.map_some, Option.isSome_some]
  | call fn args k ih =>
      intro Δ f h
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp (PRen.vars?_isSome_of_total h args)
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ih (PRen.total_liftApp h _))
      simp only [rename?, ha, hk, Option.bind_some, Option.map_some, Option.isSome_some]

/-- **The splice succeeds at total renamings.** -/
theorem seq?_isSome_of_total {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ}, PRen.Total ρ → PRen.Total θ →
      (seq? k b ρ θ).isSome := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ hρ hθ
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (PRen.vars?_isSome_of_total hρ vs)
      simp only [seq?, hws, Option.bind_some]
      exact rename?_isSome_of_total k (PRen.total_appendVars hθ ws)
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ hρ hθ
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp (Expr.rename?_isSome_of_total hρ e)
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ih k (PRen.total_lift hρ) (PRen.total_shift [_] hθ))
      simp only [seq?, he, hb, Option.bind_some, Option.map_some, Option.isSome_some]
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ hρ hθ
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (hρ count)
      obtain ⟨i', hi⟩ := Option.isSome_iff_exists.mp (PRen.vars?_isSome_of_total hρ inits)
      obtain ⟨body', hbody⟩ := Option.isSome_iff_exists.mp
        (rename?_isSome_of_total body (PRen.total_liftApp (PRen.total_lift hρ) _))
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ih k (PRen.total_liftApp hρ _) (PRen.total_shift _ hθ))
      simp only [seq?, hc, hi, hbody, hb, Option.bind_some, Option.map_some,
        Option.isSome_some]
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ hρ hθ
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (hρ cond)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (rename?_isSome_of_total thn hρ)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp (rename?_isSome_of_total els hρ)
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ih k (PRen.total_liftApp hρ _) (PRen.total_shift _ hθ))
      simp only [seq?, hc, ht, he, hb, Option.bind_some, Option.map_some,
        Option.isSome_some]
  | whileLoop inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ hρ hθ
      obtain ⟨i', hi⟩ := Option.isSome_iff_exists.mp (PRen.vars?_isSome_of_total hρ inits)
      obtain ⟨body', hbody⟩ := Option.isSome_iff_exists.mp
        (rename?_isSome_of_total body (PRen.total_liftApp hρ _))
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ih k (PRen.total_liftApp hρ _) (PRen.total_shift _ hθ))
      simp only [seq?, hi, hbody, hb, Option.bind_some, Option.map_some, Option.isSome_some]
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ hρ hθ
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp (PRen.vars?_isSome_of_total hρ args)
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ih k (PRen.total_liftApp hρ _) (PRen.total_shift _ hθ))
      simp only [seq?, ha, hb, Option.bind_some, Option.map_some, Option.isSome_some]

/-! ## 3. The composition of programs -/

/-- The program `q` over `ts` as a program over `ts ++ Γ`: the renaming along `PRen.inl`. -/
def weaken {ts us : List d.Ty} (Γ : Ctxt d) (q : NFProg d ts us) : NFProg d (ts ++ Γ) us :=
  (rename? (PRen.inl Γ) q).get (rename?_isSome_of_total q (PRen.total_inl Γ))

/-- **The composition** of `p` from `Γ` to `ts` and `q` from `ts` to `us`: the splice of the
    body `p` and the continuation `q` weakened to `ts ++ Γ`, at the identity renaming of `Γ`
    for the body and for the enclosing context of the continuation. -/
def seq {Γ : Ctxt d} {ts us : List d.Ty} (p : NFProg d Γ ts) (q : NFProg d ts us) :
    NFProg d Γ us :=
  (seq? (q.weaken Γ) p PRen.id PRen.id).get
    (seq?_isSome_of_total p (q.weaken Γ) PRen.total_id PRen.total_id)

variable [DialectDenoteM d Option] [CallDenote d]

/-- A weakened program denotes at an extended valuation what the program denotes at the
    valuation. -/
theorem denote_weaken {ts us : List d.Ty} (Γ : Ctxt d) (q : NFProg d ts us) (fuel : Nat)
    (r : Valuation ts) (V : Valuation Γ) :
    (q.weaken Γ).denote fuel (hvAppend r V) = q.denote fuel r :=
  denote_rename? q (Option.some_get _).symm (PRen.agrees_inl r V) fuel

/-- **The composition denotes the Kleisli composite**, at one fuel for both programs. -/
theorem denote_seq {Γ : Ctxt d} {ts us : List d.Ty} (p : NFProg d Γ ts) (q : NFProg d ts us)
    (fuel : Nat) (V : Valuation Γ) :
    (p.seq q).denote fuel V = p.denote fuel V >>= fun r => q.denote fuel r :=
  (denote_seq? p (q.weaken Γ) (q := p.seq q) (Option.some_get _).symm (PRen.agrees_id V)
    (PRen.agrees_id V) fuel).trans
    (congrArg (p.denote fuel V >>= ·) (funext fun r => denote_weaken Γ q fuel r V))

/-- The return of every variable is a left unit of the composition, at denotations. -/
theorem denote_ret_seq {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (fuel : Nat)
    (V : Valuation Γ) : ((NFProg.ret (allVars Γ)).seq p).denote fuel V = p.denote fuel V := by
  rw [denote_seq, denote_ret, lookupArgs_allVars]
  rfl

/-- The return of every variable is a right unit of the composition, at denotations. -/
theorem denote_seq_ret {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (fuel : Nat)
    (V : Valuation Γ) : (p.seq (.ret (allVars ts))).denote fuel V = p.denote fuel V := by
  rw [denote_seq]
  simp only [denote_ret, lookupArgs_allVars]
  exact bind_pure _

/-- The composition is associative, at denotations. -/
theorem denote_seq_assoc {Γ : Ctxt d} {ts us ws : List d.Ty} (p : NFProg d Γ ts)
    (q : NFProg d ts us) (r : NFProg d us ws) (fuel : Nat) (V : Valuation Γ) :
    ((p.seq q).seq r).denote fuel V = (p.seq (q.seq r)).denote fuel V := by
  simp only [denote_seq, bind_assoc]

end NFProg

/-! ## 4. The category of regions -/

/-- The type lists of a dialect, as the objects of the category of regions. -/
def Region (d : Dialect.{0, 0}) : Type := Ctxt d

namespace Region

open CategoryTheory

variable [DialectDenoteM d Option] [CallDenote d]

/-- **Denotational equality** of two programs: the same partial function on valuations at
    every fuel. -/
def DenoteEq {Γ : Ctxt d} {ts : List d.Ty} (p q : NFProg d Γ ts) : Prop :=
  ∀ (fuel : Nat) (V : Valuation Γ), p.denote fuel V = q.denote fuel V

/-- The composition of programs respects denotational equality in both arguments. -/
theorem DenoteEq.seq {Γ : Ctxt d} {ts us : List d.Ty} {p p' : NFProg d Γ ts}
    {q q' : NFProg d ts us} (hp : DenoteEq p p') (hq : DenoteEq q q') :
    DenoteEq (p.seq q) (p'.seq q') := by
  intro fuel V
  rw [NFProg.denote_seq, NFProg.denote_seq, hp fuel V]
  congr 1
  funext r
  exact hq fuel r

/-- The morphisms of regions from `Γ` to `ts`: programs up to denotational equality. -/
def Hom (Γ ts : Region d) : Type := Quot (DenoteEq (d := d) (Γ := Γ) (ts := ts))

/-- The class of a program. -/
def Hom.mk {Γ ts : Region d} (p : NFProg d Γ ts) : Hom Γ ts := Quot.mk _ p

/-- The composition of morphisms: the composition of programs on classes. -/
def Hom.comp {Γ ts us : Region d} (f : Hom Γ ts) (g : Hom ts us) : Hom Γ us :=
  Quot.map₂ (fun (p : NFProg d Γ ts) (q : NFProg d ts us) => p.seq q)
    (fun _ _ _ hq => DenoteEq.seq (fun _ _ => rfl) hq)
    (fun _ _ _ hp => DenoteEq.seq hp (fun _ _ => rfl)) f g

/-- **The category of regions of a dialect**: type lists, programs up to denotational
    equality, the return of every variable as identity and the splice as composition. -/
instance instCategory : Category (Region d) where
  Hom Γ ts := Hom Γ ts
  id Γ := Hom.mk (.ret (allVars Γ))
  comp f g := Hom.comp f g
  id_comp := by
    rintro Γ ts ⟨p⟩
    exact Quot.sound fun fuel V => NFProg.denote_ret_seq p fuel V
  comp_id := by
    rintro Γ ts ⟨p⟩
    exact Quot.sound fun fuel V => NFProg.denote_seq_ret p fuel V
  assoc := by
    rintro Γ ts us ws ⟨p⟩ ⟨q⟩ ⟨r⟩
    exact Quot.sound fun fuel V => NFProg.denote_seq_assoc p q r fuel V

/-- The identity of `Γ` is the class of the return of every variable. -/
theorem id_eq_mk (Γ : Region d) : 𝟙 Γ = Hom.mk (.ret (allVars (Γ : Ctxt d))) := rfl

/-- The composition of two classes is the class of the composition. -/
theorem mk_comp_mk {Γ ts us : Region d} (p : NFProg d Γ ts) (q : NFProg d ts us) :
    CategoryStruct.comp (X := Γ) (Y := ts) (Z := us) (Hom.mk p) (Hom.mk q) =
      Hom.mk (p.seq q) := rfl

/-- Two denotationally equal programs have the same class. -/
theorem mk_eq_mk {Γ ts : Region d} {p q : NFProg d Γ ts} (h : DenoteEq p q) :
    Hom.mk p = Hom.mk q := Quot.sound h

/-! ## 5. The denotation functor -/

/-- **The denotation of regions at the fuel `fuel`**, as a functor into the Kleisli category
    of `Option`: a type list goes to its valuations and the class of a program to the
    denotation of the program at `fuel`. -/
def denoteFunctor (fuel : Nat) : Region d ⥤ KleisliCat Option where
  obj Γ := KleisliCat.mk Option (Valuation (Γ : Ctxt d))
  map {Γ ts} f := Quot.lift (fun (p : NFProg d Γ ts) => p.denote fuel)
    (fun _ _ h => funext (h fuel)) f
  map_id Γ := funext fun V => congrArg some (lookupArgs_allVars V)
  map_comp := by
    rintro Γ ts us ⟨p⟩ ⟨q⟩
    exact funext fun V => NFProg.denote_seq p q fuel V

/-- The denotation functor on the class of a program. -/
theorem denoteFunctor_map_mk (fuel : Nat) {Γ ts : Region d} (p : NFProg d Γ ts) :
    (denoteFunctor fuel).map (Hom.mk p : Γ ⟶ ts) = p.denote fuel := rfl

/-- **The denotation functors are jointly faithful**: two morphisms with the same image at
    every fuel are equal. -/
theorem hom_ext_denoteFunctor {Γ ts : Region d} {f g : Γ ⟶ ts}
    (h : ∀ fuel : Nat, (denoteFunctor fuel).map f = (denoteFunctor fuel).map g) : f = g := by
  induction f using Quot.inductionOn with
  | _ p =>
    induction g using Quot.inductionOn with
    | _ q => exact Quot.sound fun fuel V => congrFun (h fuel) V

end Region

end CatCrypt.Crypto.SecureCompilation.VIR
