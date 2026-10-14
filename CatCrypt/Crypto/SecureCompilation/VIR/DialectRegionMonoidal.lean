/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectRegionCategory

/-!
# The symmetric monoidal structure on the regions of a dialect

The category `Region d` of `VIR/DialectRegionCategory.lean` is symmetric monoidal. The tensor of
two type lists is their append, the unit is the empty list, and the tensor of a program `p` from
`Γ` to `ts` and a program `q` from `Δ` to `us` runs `p` on the `Γ` part and `q` on the `Δ` part
of a valuation of `Γ ++ Δ` and returns the append of the results.

The whiskers are programs. The right whisker `p ▷ Δ` is `p` weakened to `Γ ++ Δ`, followed by the
return of its results and of the variables of `Δ`; the left whisker `Γ ◁ q` is `q` renamed into
`Γ ++ Δ` along `PRen.inr`, followed by the return of the variables of `Γ` and of its results.
Both are splices `NFProg.seqKeep`, whose continuation reads the results and the whole context of
the body. A renaming `f` of `ts` into `Γ` is the morphism `Region.ren f` from `Γ` to `ts`, the
return of the variables of `f`; it denotes the pullback of valuations along `f`.

The associator, the right unitor and the braiding are renaming isomorphisms; the left unitor is
the identity, since `[] ++ Γ` reduces to `Γ`. Every law is an equality of morphisms, which by
`Region.hom_ext_den` is an equality of denotations at each fuel and valuation. A valuation of an
append is an append of valuations (`Region.exists_hvAppend`), and the denotation of each
structure map at an appended valuation is stated in `Option` (`Region.den_tensorHom` and the
lemmas beside it); the laws then follow from the monad laws of `Option`. The interchange law
`tensorHom_comp_tensorHom` uses in addition that `Option` is a commutative monad
(`Option.bind_comm`); this is the case of a commutative monad of Power and Robinson
("Premonoidal categories and notions of computation", 1997), whose Kleisli category is
symmetric monoidal.

## Main definitions

* `PRen.inr` — the renaming of `Δ` into `Γ ++ Δ`.
* `NFProg.seqKeep` — the splice of a body and a continuation over its results and its context.
* `NFProg.whiskerRight`, `NFProg.whiskerLeft` — the whiskers, as programs.
* `Region.den` — the denotation of a morphism at a fuel, as a partial function on valuations.
* `Region.ren`, `Region.renIso` — renamings as morphisms and as isomorphisms.
* `Region.instMonoidalCategory`, `Region.instBraidedCategory`, `Region.instSymmetricCategory` —
  the symmetric monoidal structure.

## Main results

* `NFProg.denote_seqKeep`, `NFProg.denote_whiskerRight`, `NFProg.denote_whiskerLeft` — the
  denotations of the splice and of the whiskers.
* `Region.hom_ext_den` — two morphisms with the same denotations are equal.
* `Region.den_ren` — a renaming denotes the pullback along it.
* `Region.den_tensorHom` — the tensor of two morphisms denotes the pair of their denotations on
  the two parts of a valuation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend inlHom inrHom appendHom homToHV lookup_inlHom lookup_inrHom
  lookupVars_homToHV lookupVars_eq_lookupArgs)
open FieldDialectBlockDescent (pullV)
open BlockLoweringCPS (valuation_ext)

/-! ## 1. The renaming into the right part of an append -/

namespace PRen

variable {d : Dialect}

/-- The renaming of `Δ` into `Γ ++ Δ`. -/
def inr (Γ : Ctxt d) {Δ : Ctxt d} : PRen Δ (Γ ++ Δ) := fun v => some (inrHom Γ v)

/-- The renaming of `Δ` into `Γ ++ Δ` is total. -/
theorem total_inr (Γ : Ctxt d) {Δ : Ctxt d} : Total (inr Γ (Δ := Δ)) := fun _ => rfl

variable [TyDenote d.Ty]

/-- The renaming of `Δ` into `Γ ++ Δ` relates a valuation to its extension on the left by a
    valuation of `Γ`. -/
theorem agrees_inr {Γ Δ : Ctxt d} (A : Valuation Γ) (B : Valuation Δ) :
    Agrees (inr Γ (Δ := Δ)) B (hvAppend A B) := by
  intro t v v' hv
  simp only [inr, Option.some.injEq] at hv
  subst hv
  exact lookup_inrHom B A v

end PRen

/-! ## 2. Pullbacks of appended valuations -/

namespace Region

variable {d : Dialect.{0, 0}} [TyDenote d.Ty]

/-- Every valuation of an append is an append of valuations. -/
theorem exists_hvAppend : ∀ {xs ys : Ctxt d} (V : Valuation (xs ++ ys)),
    ∃ (A : Valuation xs) (B : Valuation ys), V = hvAppend A B
  | [], _, V => ⟨.nil, V, rfl⟩
  | _ :: _, _, .cons x V => by
      obtain ⟨A, B, rfl⟩ := exists_hvAppend V
      exact ⟨.cons x A, B, rfl⟩

/-- Looking up `v` in the pullback along `f` is looking up `f v`. -/
theorem lookup_pullV {Γ Γ' : Ctxt d} (f : Ctxt.Hom Γ Γ') {t : d.Ty} (v : Var Γ t)
    (V : Valuation Γ') : v.lookup (pullV f V) = (f v).lookup V := by
  induction v with
  | here => rfl
  | there w ih => simp only [pullV]; exact ih (fun v => f (.there v))

/-- Pulling back along a composite renaming is the composite of the pullbacks. -/
theorem pullV_comp {Γ₁ Γ₂ Γ₃ : Ctxt d} (f : Ctxt.Hom Γ₁ Γ₂) (g : Ctxt.Hom Γ₂ Γ₃)
    (W : Valuation Γ₃) : pullV (fun v => g (f v)) W = pullV f (pullV g W) :=
  valuation_ext _ _ fun v => by rw [lookup_pullV, lookup_pullV, lookup_pullV]

/-- Pulling back along the identity is the identity. -/
theorem pullV_id {Γ : Ctxt d} (V : Valuation Γ) : pullV (fun v => v) V = V :=
  valuation_ext _ _ fun v => lookup_pullV _ v V

/-- The pullback along `inlHom` of an appended valuation is its left part. -/
theorem pullV_inlHom {xs ys : Ctxt d} (A : Valuation xs) (B : Valuation ys) :
    pullV (inlHom ys) (hvAppend A B) = A :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact lookup_inlHom B v A

/-- The pullback along `inrHom` of an appended valuation is its right part. -/
theorem pullV_inrHom {xs ys : Ctxt d} (A : Valuation xs) (B : Valuation ys) :
    pullV (inrHom xs) (hvAppend A B) = B :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact lookup_inrHom B A v

/-- The pullback along a renaming followed by `inlHom` of an appended valuation is the pullback
    of its left part. -/
theorem pullV_comp_inlHom {Γ xs ys : Ctxt d} (f : Ctxt.Hom Γ xs) (A : Valuation xs)
    (B : Valuation ys) : pullV (fun v => inlHom ys (f v)) (hvAppend A B) = pullV f A := by
  rw [pullV_comp, pullV_inlHom]

/-- The pullback along a renaming followed by `inrHom` of an appended valuation is the pullback
    of its right part. -/
theorem pullV_comp_inrHom {Γ xs ys : Ctxt d} (f : Ctxt.Hom Γ ys) (A : Valuation xs)
    (B : Valuation ys) : pullV (fun v => inrHom xs (f v)) (hvAppend A B) = pullV f B := by
  rw [pullV_comp, pullV_inrHom]

/-- Looking up an `appendHom` variable. -/
theorem lookup_appendHom {ys Δ : Ctxt d} (g : Ctxt.Hom ys Δ) (W : Valuation Δ) :
    ∀ {xs : Ctxt d} (f : Ctxt.Hom xs Δ) {t : d.Ty} (v : Var (xs ++ ys) t),
      (appendHom f g v).lookup W = v.lookup (hvAppend (pullV f W) (pullV g W))
  | [], _, _, v => (lookup_pullV g v W).symm
  | _ :: _, _, _, .here => rfl
  | _ :: _, f, _, .there v => lookup_appendHom g W (fun w => f (.there w)) v

/-- The pullback along `appendHom f g` appends the pullbacks along `f` and `g`. -/
theorem pullV_appendHom {xs ys Δ : Ctxt d} (f : Ctxt.Hom xs Δ) (g : Ctxt.Hom ys Δ)
    (W : Valuation Δ) : pullV (appendHom f g) W = hvAppend (pullV f W) (pullV g W) :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact lookup_appendHom g W f v

/-- An appended valuation is the append of its pullbacks along `inlHom` and `inrHom`. -/
theorem hvAppend_split {xs ys : Ctxt d} (V : Valuation (xs ++ ys)) :
    hvAppend (pullV (inlHom ys) V) (pullV (inrHom xs) V) = V := by
  obtain ⟨A, B, rfl⟩ := exists_hvAppend V
  rw [pullV_inlHom, pullV_inrHom]

/-- The append of the empty valuation and a valuation is the valuation. -/
theorem hvAppend_nil {ys : Ctxt d} (B : Valuation ys) :
    hvAppend (HVector.nil : Valuation ([] : Ctxt d)) B = B := rfl

/-- The two valuations of the empty list are equal. -/
theorem valuation_nil_eq (A B : Valuation ([] : Ctxt d)) : A = B := by
  cases A; cases B; rfl

/-! ### The renamings of the structure maps -/

/-- The renaming of `Γ ++ (Δ ++ Ε)` into `(Γ ++ Δ) ++ Ε`. -/
def assocRen (Γ Δ Ε : Ctxt d) : Ctxt.Hom (Γ ++ (Δ ++ Ε)) ((Γ ++ Δ) ++ Ε) :=
  appendHom (fun v => inlHom Ε (inlHom Δ v))
    (appendHom (fun v => inlHom Ε (inrHom Γ v)) (inrHom (Γ ++ Δ)))

/-- The renaming of `(Γ ++ Δ) ++ Ε` into `Γ ++ (Δ ++ Ε)`. -/
def assocInvRen (Γ Δ Ε : Ctxt d) : Ctxt.Hom ((Γ ++ Δ) ++ Ε) (Γ ++ (Δ ++ Ε)) :=
  appendHom (appendHom (inlHom (Δ ++ Ε)) (fun v => inrHom Γ (inlHom Ε v)))
    (fun v => inrHom Γ (inrHom Δ v))

/-- The renaming of `Γ` into `Γ ++ []`. -/
def unitRen (Γ : Ctxt d) : Ctxt.Hom Γ (Γ ++ []) := inlHom []

/-- The renaming of `Γ ++ []` into `Γ`. -/
def unitInvRen (Γ : Ctxt d) : Ctxt.Hom (Γ ++ []) Γ :=
  appendHom (fun v => v) (fun {t} (v : Var ([] : Ctxt d) t) => nomatch v)

/-- The renaming of `Δ ++ Γ` into `Γ ++ Δ`. -/
def swapRen (Γ Δ : Ctxt d) : Ctxt.Hom (Δ ++ Γ) (Γ ++ Δ) := appendHom (inrHom Γ) (inlHom Δ)

theorem pullV_assocRen {Γ Δ Ε : Ctxt d} (A : Valuation Γ) (B : Valuation Δ)
    (C : Valuation Ε) :
    pullV (assocRen Γ Δ Ε) (hvAppend (hvAppend A B) C) = hvAppend A (hvAppend B C) := by
  simp only [assocRen, pullV_appendHom, pullV_comp_inlHom, pullV_inlHom, pullV_inrHom]

theorem pullV_assocInvRen {Γ Δ Ε : Ctxt d} (A : Valuation Γ) (B : Valuation Δ)
    (C : Valuation Ε) :
    pullV (assocInvRen Γ Δ Ε) (hvAppend A (hvAppend B C)) = hvAppend (hvAppend A B) C := by
  simp only [assocInvRen, pullV_appendHom, pullV_comp_inrHom, pullV_inlHom, pullV_inrHom]

theorem pullV_unitRen {Γ : Ctxt d} (A : Valuation Γ) (B : Valuation ([] : Ctxt d)) :
    pullV (unitRen Γ) (hvAppend A B) = A :=
  pullV_inlHom A B

theorem pullV_unitInvRen {Γ : Ctxt d} (A : Valuation Γ) (B : Valuation ([] : Ctxt d)) :
    pullV (unitInvRen Γ) A = hvAppend A B := by
  simp only [unitInvRen, pullV_appendHom, pullV_id]
  exact congrArg _ (valuation_nil_eq _ B)

theorem pullV_swapRen {Γ Δ : Ctxt d} (A : Valuation Γ) (B : Valuation Δ) :
    pullV (swapRen Γ Δ) (hvAppend A B) = hvAppend B A := by
  simp only [swapRen, pullV_appendHom, pullV_inrHom, pullV_inlHom]

end Region

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]

/-! ## 3. The splice over the results and the context, and the whiskers -/

namespace NFProg

/-- **The splice keeping the context**: the body `p` from `Γ` to `ts` followed by the
    continuation `k`, which reads the results of `p` and the variables of `Γ`; the splice of
    `Hax/NFInline.lean` at the identity renamings. -/
def seqKeep {Γ : Ctxt d} {ts us : List d.Ty} (p : NFProg d Γ ts) (k : NFProg d (ts ++ Γ) us) :
    NFProg d Γ us :=
  (seq? k p PRen.id PRen.id).get (seq?_isSome_of_total p k PRen.total_id PRen.total_id)

/-- The composition is the splice keeping the context, at the weakened continuation. -/
theorem seq_eq_seqKeep {Γ : Ctxt d} {ts us : List d.Ty} (p : NFProg d Γ ts)
    (q : NFProg d ts us) : p.seq q = p.seqKeep (q.weaken Γ) := rfl

/-- The right whisker of `p` from `Γ` to `ts` by `Δ`: `p` weakened to `Γ ++ Δ`, followed by
    the return of its results and of the variables of `Δ`. -/
def whiskerRight {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (Δ : Ctxt d) :
    NFProg d (Γ ++ Δ) (ts ++ Δ) :=
  (p.weaken Δ).seqKeep
    (.ret (homToHV (ts ++ Δ) (appendHom (inlHom (Γ ++ Δ)) (fun v => inrHom ts (inrHom Γ v)))))

/-- The left whisker of `q` from `Δ` to `us` by `Γ`: `q` renamed into `Γ ++ Δ` along
    `PRen.inr`, followed by the return of the variables of `Γ` and of its results. -/
def whiskerLeft (Γ : Ctxt d) {Δ : Ctxt d} {us : List d.Ty} (q : NFProg d Δ us) :
    NFProg d (Γ ++ Δ) (Γ ++ us) :=
  ((rename? (PRen.inr Γ) q).get (rename?_isSome_of_total q (PRen.total_inr Γ))).seqKeep
    (.ret (homToHV (Γ ++ us) (appendHom (fun v => inrHom us (inlHom Δ v)) (inlHom (Γ ++ Δ)))))

variable [DialectDenoteM d Option] [CallDenote d]

/-- **The splice keeping the context denotes the body followed by the continuation** at the
    results and the valuation, at one fuel for both programs. -/
theorem denote_seqKeep {Γ : Ctxt d} {ts us : List d.Ty} (p : NFProg d Γ ts)
    (k : NFProg d (ts ++ Γ) us) (fuel : Nat) (V : Valuation Γ) :
    (p.seqKeep k).denote fuel V = p.denote fuel V >>= fun r => k.denote fuel (hvAppend r V) :=
  denote_seq? p k (Option.some_get _).symm (PRen.agrees_id V) (PRen.agrees_id V) fuel

/-- A return of the variables of a renaming denotes the pullback along it. -/
theorem denote_ret_homToHV {Γ : Ctxt d} (ts : List d.Ty) (f : Ctxt.Hom ts Γ) (fuel : Nat)
    (V : Valuation Γ) : (NFProg.ret (homToHV ts f)).denote fuel V = some (pullV f V) := by
  rw [denote_ret, ← lookupVars_eq_lookupArgs, lookupVars_homToHV]

/-- The right whisker runs the program on the left part of a valuation and keeps the right
    part. -/
theorem denote_whiskerRight {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (Δ : Ctxt d)
    (fuel : Nat) (A : Valuation Γ) (B : Valuation Δ) :
    (p.whiskerRight Δ).denote fuel (hvAppend A B) =
      p.denote fuel A >>= fun r => some (hvAppend r B) := by
  rw [whiskerRight, denote_seqKeep, denote_weaken]
  congr 1
  funext r
  rw [denote_ret_homToHV, Region.pullV_appendHom, Region.pullV_inlHom,
    Region.pullV_comp_inrHom, Region.pullV_inrHom]

/-- The left whisker keeps the left part of a valuation and runs the program on the right
    part. -/
theorem denote_whiskerLeft (Γ : Ctxt d) {Δ : Ctxt d} {us : List d.Ty} (q : NFProg d Δ us)
    (fuel : Nat) (A : Valuation Γ) (B : Valuation Δ) :
    (q.whiskerLeft Γ).denote fuel (hvAppend A B) =
      q.denote fuel B >>= fun r => some (hvAppend A r) := by
  rw [whiskerLeft, denote_seqKeep,
    denote_rename? q (Option.some_get _).symm (PRen.agrees_inr A B) fuel]
  congr 1
  funext r
  rw [denote_ret_homToHV, Region.pullV_appendHom, Region.pullV_comp_inrHom,
    Region.pullV_inlHom, Region.pullV_inlHom]

end NFProg

/-! ## 4. Denotations, renamings and whiskers of morphisms -/

namespace Region

open CategoryTheory

variable [DialectDenoteM d Option] [CallDenote d]

/-- **The denotation of a morphism** at the fuel `fuel`: the denotation of any program of the
    class, a partial function on valuations. -/
def den (fuel : Nat) {Γ ts : Region d} (f : Γ ⟶ ts) :
    Valuation (Γ : Ctxt d) → Option (Valuation (ts : Ctxt d)) :=
  Quot.lift (fun (p : NFProg d Γ ts) => p.denote fuel) (fun _ _ h => funext (h fuel)) f

/-- The denotation of a morphism is the denotation functor on it. -/
theorem den_eq_map (fuel : Nat) {Γ ts : Region d} (f : Γ ⟶ ts) :
    den fuel f = (denoteFunctor fuel).map f := rfl

/-- **Two morphisms with the same denotations are equal.** -/
theorem hom_ext_den {Γ ts : Region d} {f g : Γ ⟶ ts}
    (h : ∀ (fuel : Nat) (V : Valuation (Γ : Ctxt d)), den fuel f V = den fuel g V) : f = g :=
  hom_ext_denoteFunctor fun fuel => funext fun V => h fuel V

/-- The denotation of a composite is the Kleisli composite of the denotations. -/
theorem den_comp (fuel : Nat) {Γ ts us : Region d} (f : Γ ⟶ ts) (g : ts ⟶ us)
    (V : Valuation (Γ : Ctxt d)) : den fuel (f ≫ g) V = den fuel f V >>= den fuel g :=
  congrFun ((denoteFunctor fuel).map_comp f g) V

/-- The denotation of an identity is the unit of `Option`. -/
theorem den_id (fuel : Nat) (Γ : Region d) (V : Valuation (Γ : Ctxt d)) :
    den fuel (𝟙 Γ) V = some V :=
  congrFun ((denoteFunctor fuel).map_id Γ) V

/-- **A renaming as a morphism**: for a renaming `f` of `ts` into `Γ`, the class of the return
    of the variables of `f`. -/
def ren {Γ ts : Region d} (f : Ctxt.Hom (ts : Ctxt d) (Γ : Ctxt d)) : Γ ⟶ ts :=
  Hom.mk (.ret (homToHV ts f))

/-- **A renaming denotes the pullback along it.** -/
theorem den_ren (fuel : Nat) {Γ ts : Region d} (f : Ctxt.Hom (ts : Ctxt d) (Γ : Ctxt d))
    (V : Valuation (Γ : Ctxt d)) : den fuel (ren f) V = some (pullV f V) :=
  NFProg.denote_ret_homToHV _ f fuel V

/-- The composite of two renamings is the renaming along the composite. -/
theorem ren_comp_ren {Γ ts us : Region d} (f : Ctxt.Hom (ts : Ctxt d) (Γ : Ctxt d))
    (g : Ctxt.Hom (us : Ctxt d) (ts : Ctxt d)) : ren f ≫ ren g = ren (fun v => f (g v)) :=
  hom_ext_den fun fuel V => by
    refine (den_comp fuel _ _ V).trans ?_
    refine (congrArg (· >>= den fuel (ren g)) (den_ren fuel f V)).trans ?_
    refine (den_ren fuel g _).trans ?_
    exact (congrArg some (pullV_comp _ _ V).symm).trans (den_ren fuel _ V).symm

/-- The renaming along the identity is the identity. -/
theorem ren_id (Γ : Region d) : ren (Γ := Γ) (ts := Γ) (fun v => v) = 𝟙 Γ :=
  hom_ext_den fun fuel V =>
    (den_ren fuel _ V).trans ((congrArg some (pullV_id V)).trans (den_id fuel Γ V).symm)

/-- **A renaming isomorphism**: two renamings whose pullbacks are mutually inverse. -/
def renIso {Γ ts : Region d} (f : Ctxt.Hom (ts : Ctxt d) (Γ : Ctxt d))
    (g : Ctxt.Hom (Γ : Ctxt d) (ts : Ctxt d))
    (hgf : ∀ V : Valuation (Γ : Ctxt d), pullV g (pullV f V) = V)
    (hfg : ∀ W : Valuation (ts : Ctxt d), pullV f (pullV g W) = W) : Γ ≅ ts where
  hom := ren f
  inv := ren g
  hom_inv_id := hom_ext_den fun fuel V => by
    rw [den_comp, den_ren, den_id]
    exact (den_ren fuel g _).trans (congrArg some (hgf V))
  inv_hom_id := hom_ext_den fun fuel W => by
    rw [den_comp, den_ren, den_id]
    exact (den_ren fuel f _).trans (congrArg some (hfg W))

/-- Programs with the same denotations have right whiskers with the same denotations. -/
theorem DenoteEq.whiskerRight {Γ : Ctxt d} {ts : List d.Ty} {p p' : NFProg d Γ ts}
    (h : DenoteEq p p') (Δ : Ctxt d) : DenoteEq (p.whiskerRight Δ) (p'.whiskerRight Δ) := by
  intro fuel V
  obtain ⟨A, B, rfl⟩ := exists_hvAppend V
  rw [NFProg.denote_whiskerRight, NFProg.denote_whiskerRight, h fuel A]

/-- Programs with the same denotations have left whiskers with the same denotations. -/
theorem DenoteEq.whiskerLeft (Γ : Ctxt d) {Δ : Ctxt d} {us : List d.Ty} {q q' : NFProg d Δ us}
    (h : DenoteEq q q') : DenoteEq (q.whiskerLeft Γ) (q'.whiskerLeft Γ) := by
  intro fuel V
  obtain ⟨A, B, rfl⟩ := exists_hvAppend V
  rw [NFProg.denote_whiskerLeft, NFProg.denote_whiskerLeft, h fuel B]

/-- The right whisker of a morphism: the right whisker of programs on classes. -/
def Hom.whiskerRight {Γ ts : Ctxt d} (f : Hom Γ ts) (Δ : Ctxt d) : Hom (Γ ++ Δ) (ts ++ Δ) :=
  Quot.map (fun p => NFProg.whiskerRight p Δ) (fun _ _ h => DenoteEq.whiskerRight h Δ) f

/-- The left whisker of a morphism: the left whisker of programs on classes. -/
def Hom.whiskerLeft (Γ : Ctxt d) {Δ us : Ctxt d} (g : Hom Δ us) : Hom (Γ ++ Δ) (Γ ++ us) :=
  Quot.map (fun q => NFProg.whiskerLeft Γ q) (fun _ _ h => DenoteEq.whiskerLeft Γ h) g

/-! ## 5. The structure maps -/

/-- The associator: the renaming isomorphism of `(Γ ++ Δ) ++ Ε` and `Γ ++ (Δ ++ Ε)`. -/
def associatorIso (Γ Δ Ε : Ctxt d) : Iso (C := Region d) ((Γ ++ Δ) ++ Ε) (Γ ++ (Δ ++ Ε)) :=
  renIso (assocRen Γ Δ Ε) (assocInvRen Γ Δ Ε)
    (fun V => by
      obtain ⟨AB, C, rfl⟩ := exists_hvAppend V
      obtain ⟨A, B, rfl⟩ := exists_hvAppend AB
      rw [pullV_assocRen, pullV_assocInvRen])
    (fun W => by
      obtain ⟨A, BC, rfl⟩ := exists_hvAppend W
      obtain ⟨B, C, rfl⟩ := exists_hvAppend BC
      rw [pullV_assocInvRen, pullV_assocRen])

/-- The right unitor: the renaming isomorphism of `Γ ++ []` and `Γ`. -/
def rightUnitorIso (Γ : Ctxt d) : Iso (C := Region d) (Γ ++ []) Γ :=
  renIso (unitRen Γ) (unitInvRen Γ)
    (fun V => by
      obtain ⟨A, B, rfl⟩ := exists_hvAppend V
      rw [pullV_unitRen, pullV_unitInvRen A B])
    (fun W => by rw [pullV_unitInvRen W .nil, pullV_unitRen])

/-- The braiding: the renaming isomorphism of `Γ ++ Δ` and `Δ ++ Γ`. -/
def braidingIso (Γ Δ : Ctxt d) : Iso (C := Region d) (Γ ++ Δ) (Δ ++ Γ) :=
  renIso (swapRen Γ Δ) (swapRen Δ Γ)
    (fun V => by
      obtain ⟨A, B, rfl⟩ := exists_hvAppend V
      rw [pullV_swapRen, pullV_swapRen])
    (fun W => by
      obtain ⟨B, A, rfl⟩ := exists_hvAppend W
      rw [pullV_swapRen, pullV_swapRen])

/-- **The monoidal data of regions**: append as tensor, the empty list as unit, the whiskers
    of programs, and the renaming isomorphisms as associator and right unitor. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Region d) where
  tensorObj Γ Δ := @HAppend.hAppend (Ctxt d) (Ctxt d) (Ctxt d) _ Γ Δ
  whiskerLeft Γ _ _ g := Hom.whiskerLeft Γ g
  whiskerRight f Δ := Hom.whiskerRight f Δ
  tensorUnit := ([] : Ctxt d)
  associator Γ Δ Ε := associatorIso Γ Δ Ε
  leftUnitor Γ := Iso.refl Γ
  rightUnitor Γ := rightUnitorIso Γ

open MonoidalCategory

/-! ## 6. The denotations of the structure maps -/

/-- The right whisker of a morphism runs it on the left part of a valuation. -/
theorem den_whiskerRight (fuel : Nat) {Γ ts : Region d} (f : Γ ⟶ ts) (Δ : Region d)
    (A : Valuation (Γ : Ctxt d)) (B : Valuation (Δ : Ctxt d)) :
    den fuel (f ▷ Δ) (hvAppend A B) = den fuel f A >>= fun r => some (hvAppend r B) := by
  induction f using Quot.inductionOn with
  | _ p => exact NFProg.denote_whiskerRight p Δ fuel A B

/-- The left whisker of a morphism runs it on the right part of a valuation. -/
theorem den_whiskerLeft (fuel : Nat) (Γ : Region d) {Δ us : Region d} (g : Δ ⟶ us)
    (A : Valuation (Γ : Ctxt d)) (B : Valuation (Δ : Ctxt d)) :
    den fuel (Γ ◁ g) (hvAppend A B) = den fuel g B >>= fun r => some (hvAppend A r) := by
  induction g using Quot.inductionOn with
  | _ q => exact NFProg.denote_whiskerLeft Γ q fuel A B

/-- **The tensor of two morphisms denotes the pair of their denotations** on the two parts of
    a valuation. -/
theorem den_tensorHom (fuel : Nat) {Γ ts Δ us : Region d} (f : Γ ⟶ ts) (g : Δ ⟶ us)
    (A : Valuation (Γ : Ctxt d)) (B : Valuation (Δ : Ctxt d)) :
    den fuel (f ⊗ₘ g) (hvAppend A B) =
      den fuel f A >>= fun a => den fuel g B >>= fun b => some (hvAppend a b) := by
  show den fuel (f ▷ Δ ≫ ts ◁ g) (hvAppend A B) = _
  rw [den_comp, den_whiskerRight]
  simp only [Option.bind_eq_bind, Option.bind_assoc, Option.bind_some, den_whiskerLeft]

theorem den_associator_hom (fuel : Nat) (Γ Δ Ε : Region d) (A : Valuation (Γ : Ctxt d))
    (B : Valuation (Δ : Ctxt d)) (C : Valuation (Ε : Ctxt d)) :
    den fuel (α_ Γ Δ Ε).hom (hvAppend (hvAppend A B) C) = some (hvAppend A (hvAppend B C)) :=
  (den_ren fuel _ _).trans (congrArg some (pullV_assocRen A B C))

theorem den_associator_inv (fuel : Nat) (Γ Δ Ε : Region d) (A : Valuation (Γ : Ctxt d))
    (B : Valuation (Δ : Ctxt d)) (C : Valuation (Ε : Ctxt d)) :
    den fuel (α_ Γ Δ Ε).inv (hvAppend A (hvAppend B C)) = some (hvAppend (hvAppend A B) C) :=
  (den_ren fuel _ _).trans (congrArg some (pullV_assocInvRen A B C))

theorem den_leftUnitor_hom (fuel : Nat) (Γ : Region d) (V : Valuation (Γ : Ctxt d)) :
    den fuel (λ_ Γ).hom V = some V :=
  den_id fuel Γ V

theorem den_rightUnitor_hom (fuel : Nat) (Γ : Region d) (A : Valuation (Γ : Ctxt d))
    (B : Valuation ([] : Ctxt d)) : den fuel (ρ_ Γ).hom (hvAppend A B) = some A :=
  (den_ren fuel _ _).trans (congrArg some (pullV_unitRen A B))

/-! ## 7. The monoidal category of regions -/

/-- **The monoidal category of regions.** -/
instance instMonoidalCategory : MonoidalCategory (Region d) where
  tensorHom_def _ _ := rfl
  id_tensorHom_id Γ Δ := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (Γ : Ctxt d)) (ys := (Δ : Ctxt d)) V
    simp only [den_tensorHom, den_id, Option.bind_eq_bind, Option.bind_some]
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X₁ : Ctxt d)) (ys := (X₂ : Ctxt d)) V
    simp only [den_comp, den_tensorHom, Option.bind_eq_bind, Option.bind_assoc,
      Option.bind_some]
    congr 1
    funext a
    exact Option.bind_comm _ _
  whiskerLeft_id Γ Δ := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (Γ : Ctxt d)) (ys := (Δ : Ctxt d)) V
    simp only [den_whiskerLeft, den_id, Option.bind_eq_bind, Option.bind_some]
  id_whiskerRight Γ Δ := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (Γ : Ctxt d)) (ys := (Δ : Ctxt d)) V
    simp only [den_whiskerRight, den_id, Option.bind_eq_bind, Option.bind_some]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := hom_ext_den fun fuel V => by
    obtain ⟨AB, C, rfl⟩ :=
      exists_hvAppend (xs := (X₁ ⊗ X₂ : Region d)) (ys := (X₃ : Ctxt d)) V
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X₁ : Ctxt d)) (ys := (X₂ : Ctxt d)) AB
    simp only [den_comp, den_tensorHom, den_associator_hom, Option.bind_eq_bind,
      Option.bind_assoc, Option.bind_some]
  leftUnitor_naturality {X Y} f := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := ([] : Ctxt d)) (ys := (X : Ctxt d)) V
    cases A
    simp only [den_comp, den_whiskerLeft, den_leftUnitor_hom, Option.bind_eq_bind,
      Option.bind_assoc, Option.bind_some]
    exact Option.bind_fun_some _
  rightUnitor_naturality {X Y} f := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X : Ctxt d)) (ys := ([] : Ctxt d)) V
    simp only [den_comp, den_whiskerRight, den_rightUnitor_hom, Option.bind_eq_bind,
      Option.bind_assoc, Option.bind_some, Option.bind_fun_some]
  pentagon W X Y Z := hom_ext_den fun fuel V => by
    obtain ⟨ABC, D, rfl⟩ := exists_hvAppend
      (xs := ((W ⊗ X) ⊗ Y : Region d)) (ys := (Z : Ctxt d)) V
    obtain ⟨AB, C, rfl⟩ := exists_hvAppend (xs := (W ⊗ X : Region d)) (ys := (Y : Ctxt d)) ABC
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (W : Ctxt d)) (ys := (X : Ctxt d)) AB
    simp only [den_comp, den_whiskerRight, den_whiskerLeft, den_associator_hom,
      Option.bind_eq_bind, Option.bind_some]
  triangle X Y := hom_ext_den fun fuel V => by
    obtain ⟨AB, C, rfl⟩ :=
      exists_hvAppend (xs := (X ⊗ 𝟙_ (Region d) : Region d)) (ys := (Y : Ctxt d)) V
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X : Ctxt d)) (ys := ([] : Ctxt d)) AB
    cases B
    simp only [den_comp, den_whiskerRight, den_whiskerLeft, den_associator_hom,
      den_rightUnitor_hom, den_leftUnitor_hom, Option.bind_eq_bind, Option.bind_some]
    rfl

/-! ## 8. The braiding and the symmetry -/

theorem den_braidingIso_hom (fuel : Nat) (Γ Δ : Region d) (A : Valuation (Γ : Ctxt d))
    (B : Valuation (Δ : Ctxt d)) :
    den fuel (braidingIso Γ Δ).hom (hvAppend A B) = some (hvAppend B A) :=
  (den_ren fuel _ _).trans (congrArg some (pullV_swapRen A B))

/-- **The braided monoidal category of regions**: the braiding swaps the two parts of a
    valuation. -/
instance instBraidedCategory : BraidedCategory (Region d) where
  braiding Γ Δ := braidingIso Γ Δ
  braiding_naturality_right X {Y Z} f := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X : Ctxt d)) (ys := (Y : Ctxt d)) V
    simp only [den_comp, den_whiskerLeft, den_whiskerRight, den_braidingIso_hom,
      Option.bind_eq_bind, Option.bind_assoc, Option.bind_some]
  braiding_naturality_left {X Y} f Z := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X : Ctxt d)) (ys := (Z : Ctxt d)) V
    simp only [den_comp, den_whiskerLeft, den_whiskerRight, den_braidingIso_hom,
      Option.bind_eq_bind, Option.bind_assoc, Option.bind_some]
  hexagon_forward X Y Z := hom_ext_den fun fuel V => by
    obtain ⟨AB, C, rfl⟩ :=
      exists_hvAppend (xs := (X ⊗ Y : Region d)) (ys := (Z : Ctxt d)) V
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X : Ctxt d)) (ys := (Y : Ctxt d)) AB
    simp only [den_comp, den_whiskerLeft, den_whiskerRight, den_braidingIso_hom,
      den_associator_hom, Option.bind_eq_bind, Option.bind_some]
  hexagon_reverse X Y Z := hom_ext_den fun fuel V => by
    obtain ⟨A, BC, rfl⟩ :=
      exists_hvAppend (xs := (X : Ctxt d)) (ys := (Y ⊗ Z : Region d)) V
    obtain ⟨B, C, rfl⟩ := exists_hvAppend (xs := (Y : Ctxt d)) (ys := (Z : Ctxt d)) BC
    simp only [den_comp, den_whiskerLeft, den_whiskerRight, den_braidingIso_hom,
      den_associator_inv, Option.bind_eq_bind, Option.bind_some]

/-- The braiding denotes the swap of the two parts of a valuation. -/
theorem den_braiding_hom (fuel : Nat) (Γ Δ : Region d) (A : Valuation (Γ : Ctxt d))
    (B : Valuation (Δ : Ctxt d)) : den fuel (β_ Γ Δ).hom (hvAppend A B) = some (hvAppend B A) :=
  den_braidingIso_hom fuel Γ Δ A B

/-- **The symmetric monoidal category of regions.** -/
instance instSymmetricCategory : SymmetricCategory (Region d) where
  symmetry X Y := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := (X : Ctxt d)) (ys := (Y : Ctxt d)) V
    simp only [den_comp, den_braiding_hom, den_id, Option.bind_eq_bind, Option.bind_some]

end Region

end CatCrypt.Crypto.SecureCompilation.VIR
