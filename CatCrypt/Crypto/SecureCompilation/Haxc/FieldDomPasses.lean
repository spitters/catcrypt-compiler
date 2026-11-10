/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomWriteKills

/-!
# The store-chain shape through the passes after the splice of the wide blocks

The shape `LoadsChain` (loads and memory-free bindings, then one chain of stores, each reading
the result of the previous one, ending in the return of the last stored array) is kept by the
passes that run between the splice of the body of a wide tagged call and the export.

A partial renaming that keeps the current version of a chain keeps the chain, and a renaming
that drops it fails on the chain. Dead-binding elimination therefore never removes a store of a
chain (the next store or the return reads its result), and removes a load or a memory-free
binding only through a renaming that keeps every name the rest reads. The forwarding of loads,
the select lowering, mask elimination and the carry pairs rename stores and keep them; the
range stage rewrites a binding to itself, a constant or an arithmetic operation, and keeps a
store; extraction from the e-graph at the jasmin rules keeps a store, since no rule rewrites one
and a store is never merged, and turns every other binding into a variable, itself, or
memory-free bindings. The widening maps a memory-free binding to a block of memory-free
bindings and a load or a store to one load or store.

## Main definitions

* `AltFree`: an alternative of extraction binds memory-free operations only.
* `ComFree`: a straight-line block binds memory-free operations only.

## Main results

* `chainTail_rename?`, `loadsChain_rename?`: a partial renaming keeps the shapes.
* `rename?_chainTail_none`: a renaming that drops the current version fails on a chain tail.
* `chainTail_dce`, `loadsChain_dce`: dead-binding elimination keeps the shapes.
* `loadsChain_fwdLoad1`, `loadsChain_castNF`: the forwarding of loads from one-word arrays and
  the carried form keep `LoadsChain`.
* `chainTail_seq?`, `loadsChain_seq?`: the splice of a body of the shape before a continuation
  that continues the chain of its result has the shape.
* `loadsChain_lowerSelects`: the select lowering keeps `LoadsChain`.
* `rangeExpr_eq_or_memFree`, `loadsChain_loopRange`: the range stage keeps a binding or makes
  it memory-free, and keeps `LoadsChain`.
* `loadsChain_maskElimGo`, `loadsChain_carryPairGo`, `loadsChain_legalizeRegion`: mask
  elimination, the carry pairs and the region legalisation keep `LoadsChain`.
* `jasminRules_alts_free`, `jasminRules_alts_store`, `choose_store`, `choose_cases`: the jasmin
  rules produce memory-free alternatives and none for a store; extraction keeps a store.
* `loadsChain_aegraphOptNF`: the e-graph pass at the jasmin rules keeps `LoadsChain`.
* `comFree_wideOpBlock?`, `chainTail_widen`, `loadsChain_widen`: the widened block of a
  memory-free operation is memory-free, and the widening keeps the shapes.
* `loadsChain_narrowPrep`: the narrow-word stages keep `LoadsChain`.
* `loadsChain_lowerBodyTail`: the end of the lowering of a raised body keeps `LoadsChain`.
* `loadsChain_afterSplice`: the select, range and e-graph steps, the narrow-word stages and the
  legalisation take a program of the shape `LoadsChain` to the program the export receives, of
  the same shape.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)
open Ctxt (Var)

/-! ## 1. Partial renamings -/

/-- A partial renaming of a vector of variables, at its head (unfolding lemma). -/
theorem vars?_cons {Γ Δ : Ctxt jasminDialect} (f : PRen Γ Δ) {t : JasminTy} {ts : List JasminTy}
    (v : Var Γ t) (vs : HVector (fun t => Var Γ t) ts) :
    PRen.vars? f (.cons v vs) = (f v).bind fun v' => (PRen.vars? f vs).map (.cons v') := rfl

/-- A partial renaming of the empty vector (unfolding lemma). -/
theorem vars?_nil {Γ Δ : Ctxt jasminDialect} (f : PRen Γ Δ) :
    PRen.vars? f (.nil : HVector (fun t => Var Γ t) []) = some .nil := rfl

/-- A partial renaming of a store binding renames its three arguments. -/
theorem rename?_store {Γ Δ : Ctxt jasminDialect} {w m : Nat} (f : PRen Γ Δ)
    (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w))
    {e' : Expr jasminDialect Δ (.stackArr w m)}
    (he : Expr.rename? f (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
      Expr jasminDialect Γ (.stackArr w m)) = some e') :
    ∃ v' i' x', f v = some v' ∧
      e' = ⟨.stackStore w m, rfl, .cons v' (.cons i' (.cons x' .nil))⟩ := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  change ((f v).bind fun v' => ((f i).bind fun i' => ((f x).bind fun x' =>
    (some HVector.nil).map (HVector.cons x')).map (HVector.cons i')).map (HVector.cons v')) =
      some args at hargs
  cases hv : f v <;> cases hi : f i <;> cases hx : f x <;>
    simp only [hv, hi, hx, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hargs
  subst hargs
  exact ⟨_, _, _, rfl, rfl⟩

/-- A partial renaming of a load binding renames its two arguments. -/
theorem rename?_load {Γ Δ : Ctxt jasminDialect} {w m : Nat} (f : PRen Γ Δ)
    (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64))
    {e' : Expr jasminDialect Δ (.reg w)}
    (he : Expr.rename? f (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
      Expr jasminDialect Γ (.reg w)) = some e') :
    ∃ a' i', e' = ⟨.stackLoad w m, rfl, .cons a' (.cons i' .nil)⟩ := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  change ((f a).bind fun a' => ((f i).bind fun i' =>
    (some HVector.nil).map (HVector.cons i')).map (HVector.cons a')) = some args at hargs
  cases ha : f a <;> cases hi : f i <;>
    simp only [ha, hi, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hargs
  subst hargs
  exact ⟨_, _, rfl⟩

/-- A partial renaming of an expression keeps its operation. -/
theorem rename?_op {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {f : PRen Γ Δ}
    {e : Expr jasminDialect Γ t} {e' : Expr jasminDialect Δ t}
    (he : Expr.rename? f e = some e') : e'.op = e.op := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨_, -, rfl⟩ := he
  rfl

/-- **A partial renaming keeps a chain tail**, at the image of its current version. -/
theorem chainTail_rename? {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ {Δ : Ctxt jasminDialect} {f : PRen Γ Δ} {v' : Var Δ (.stackArr w m)}
      {k' : NFProg jasminDialect Δ ts}, f v = some v' → NFProg.rename? f k = some k' →
      ChainTail v' k' := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro Δ f v' k' hv hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k'', hk', rfl⟩ := hr
      refine .free _ _ _ ((rename?_op he').symm ▸ he) (ih ?_ hk')
      simp [PRen.lift, hv]
  | @store Γ w m ts v i x k hk ih =>
      intro Δ f v' k' hv hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k'', hk', rfl⟩ := hr
      obtain ⟨v'', i', x', hv', rfl⟩ := rename?_store f v i x he'
      rw [hv] at hv'
      cases hv'
      exact .store _ _ _ _ (ih rfl hk')
  | @ret Γ w m v =>
      intro Δ f v' k' hv hr
      change Option.map NFProg.ret ((f v).bind fun v' =>
        (some HVector.nil).map (HVector.cons v')) = some k' at hr
      simp only [hv, Option.bind_some, Option.map_some, Option.some.injEq] at hr
      subst hr
      exact .ret _

/-- **A renaming that drops the current version fails on a chain tail**: the store or the
    return that reads it has no image. -/
theorem rename?_chainTail_none {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ {Δ : Ctxt jasminDialect} {f : PRen Γ Δ}, f v = none → NFProg.rename? f k = none := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro Δ f hv
      simp only [NFProg.rename?, Option.bind_eq_none_iff, Option.map_eq_none_iff]
      intro e' _
      exact ih (by simp [PRen.lift, hv])
  | @store Γ w m ts v i x k hk ih =>
      intro Δ f hv
      change ((Expr.rename? f _).bind fun e' => _) = none
      rw [show Expr.rename? f (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
          Expr jasminDialect Γ (.stackArr w m)) = none from by
        change Option.map _ ((f v).bind fun v' => _) = none
        rw [hv]
        rfl]
      rfl
  | @ret Γ w m v =>
      intro Δ f hv
      change Option.map NFProg.ret ((f v).bind fun v' => _) = none
      rw [hv]
      rfl

/-- **A partial renaming keeps the shape `LoadsChain`.** -/
theorem loadsChain_rename? {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ {Δ : Ctxt jasminDialect} {f : PRen Γ Δ} {p' : NFProg jasminDialect Δ ts},
      NFProg.rename? f p = some p' → LoadsChain p' := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ f p' hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      exact .free _ _ ((rename?_op he').symm ▸ he) (ih hk')
  | @load Γ w m ts a i k hk ih =>
      intro Δ f p' hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      obtain ⟨a', i', rfl⟩ := rename?_load f a i he'
      exact .load _ _ _ (ih hk')
  | @store Γ w m ts v i x k hk =>
      intro Δ f p' hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      obtain ⟨v', i', x', -, rfl⟩ := rename?_store f v i x he'
      exact .store _ _ _ _ (chainTail_rename? hk rfl hk')
  | @ret Γ ts vs =>
      intro Δ f p' hr
      simp only [NFProg.rename?, Option.map_eq_some_iff] at hr
      obtain ⟨ws, -, rfl⟩ := hr
      exact .ret _

/-! ## 2. Dead-binding elimination -/

/-- **Dead-binding elimination keeps a chain tail**: it removes no store of the chain, since
    the next store or the return reads its result. -/
theorem chainTail_dce {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ChainTail v (NFProg.dce k) := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact chainTail_rename? ih (by simp [PRen.drop]) hr
      · exact .free _ _ _ he ih
  | @store Γ w m ts v i x k hk ih =>
      have hn : NFProg.rename? PRen.drop (NFProg.dce k) = none :=
        rename?_chainTail_none ih (by simp [PRen.drop])
      simp only [NFProg.dce, hn]
      exact .store _ _ _ _ ih
  | @ret Γ w m v => exact .ret _

/-- **Dead-binding elimination keeps the shape `LoadsChain`.** -/
theorem loadsChain_dce {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) : LoadsChain (NFProg.dce p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact loadsChain_rename? ih hr
      · exact .free _ _ he ih
  | @load Γ w m ts a i k hk ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact loadsChain_rename? ih hr
      · exact .load _ _ _ ih
  | @store Γ w m ts v i x k hk =>
      have hk' := chainTail_dce hk
      have hn : NFProg.rename? PRen.drop (NFProg.dce k) = none :=
        rename?_chainTail_none hk' (by simp [PRen.drop])
      simp only [NFProg.dce, hn]
      exact .store _ _ _ _ hk'
  | @ret Γ ts vs => exact .ret _

/-! ## 3. Forwarding of loads from one-word arrays, and the carried form -/

/-- A memory-free binding is no load from a one-word array. -/
theorem loadArr1?_of_memFree {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : jMemFree e.op = true) : NFFwdLoad1.loadArr1? e = none := by
  rcases e with ⟨op, rfl, args⟩
  cases op <;> first | rfl | simp [jMemFree] at he

/-- **The forwarding of loads keeps a chain tail**, at every facts and renaming, at the image
    of the current version. -/
theorem chainTail_fwdLoad1Go {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ {Δ : Ctxt jasminDialect} (K : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ),
      ChainTail (ren v) (NFFwdLoad1.fwdLoad1Go k K ren) := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, loadArr1?_of_memFree e he]
      exact .free _ _ _ he (ih _ (Ctxt.Hom.lift ren))
  | @store Γ w m ts v i x k hk ih =>
      intro Δ K ren
      exact .store _ _ _ _ (ih _ (Ctxt.Hom.lift ren))
  | @ret Γ w m v =>
      intro Δ K ren
      exact .ret _

/-- **The forwarding of loads keeps the shape `LoadsChain`**, at every facts and renaming. -/
theorem loadsChain_fwdLoad1Go {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ {Δ : Ctxt jasminDialect} (K : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ),
      LoadsChain (NFFwdLoad1.fwdLoad1Go p K ren) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _
        · exact .free _ _ he (ih _ _)
      · exact .free _ _ he (ih _ _)
  | @load Γ w m ts a i k hk ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _
        · exact .load _ _ _ (ih _ _)
      · exact .load _ _ _ (ih _ _)
  | @store Γ w m ts v i x k hk =>
      intro Δ K ren
      exact .store _ _ _ _ (chainTail_fwdLoad1Go hk _ (Ctxt.Hom.lift ren))
  | @ret Γ ts vs =>
      intro Δ K ren
      exact .ret _

/-- **The forwarding of loads keeps the shape `LoadsChain`.** -/
theorem loadsChain_fwdLoad1 {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) : LoadsChain (NFFwdLoad1.fwdLoad1 p) :=
  loadsChain_fwdLoad1Go h _ _

/-- **A carried program has the shape `LoadsChain` when the program has it.** -/
theorem loadsChain_castNF {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ')
    (hts : ts = ts') {q : NFProg jasminDialect Γ ts} (h : LoadsChain q) :
    LoadsChain (FieldDialectStep.castNF hΓ hts q) := by
  subst hΓ hts
  exact h

/-! ## 4. The splice of a body before a continuation -/

/-- A chain tail is a program of the shape `LoadsChain`. -/
theorem loadsChain_of_chainTail {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    LoadsChain k := by
  induction h with
  | free v e k he hk ih => exact .free _ _ he ih
  | store v i x k hk _ => exact .store _ _ _ _ hk
  | ret v => exact .ret _

/-- **The splice of a chain tail before a continuation that continues the chain** is a chain
    tail: at the return of the body, the continuation reads the last version. -/
theorem chainTail_seq? : ∀ {Δ : Ctxt jasminDialect} {w m w' m' : Nat}
    {v : Var Δ (.stackArr w' m')} {b : NFProg jasminDialect Δ [.stackArr w m]}, ChainTail v b →
    ∀ {Γ₀ : Ctxt jasminDialect} {ts : List JasminTy}
      {k : NFProg jasminDialect (.stackArr w m :: Γ₀) ts}, ChainTail .here k →
    ∀ {Γ : Ctxt jasminDialect} {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {v' : Var Γ (.stackArr w' m')}
      {q : NFProg jasminDialect Γ ts}, ρ v = some v' → NFProg.seq? k b ρ θ = some q →
      ChainTail v' q
  | _, _, _, _, _, _, _, .free v e b he hb, _, _, k, hk, _, ρ, θ, v', q, hv, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      exact .free _ _ _ ((rename?_op he').symm ▸ he)
        (chainTail_seq? hb hk (show (ρ v).map Var.there = _ by rw [hv]; rfl) hq')
  | _, _, _, _, _, _, _, .store v i x b hb, _, _, k, hk, _, ρ, θ, v', q, hv, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨v'', i', x', hv', rfl⟩ := rename?_store ρ v i x he'
      rw [hv] at hv'
      cases hv'
      exact .store _ _ _ _ (chainTail_seq? hb hk rfl hq')
  | _, _, _, _, _, _, _, .ret v, _, _, k, hk, _, ρ, θ, v', q, hv, hq => by
      change ((ρ v).bind fun v' => (some HVector.nil).map (HVector.cons v')).bind
        (fun ws => NFProg.rename? (PRen.appendVars θ ws) k) = some q at hq
      simp only [hv, Option.bind_some, Option.map_some] at hq
      exact chainTail_rename? hk rfl hq

/-- **The splice of a body of the shape `LoadsChain` before a continuation that continues the
    chain of its result** has the shape `LoadsChain`. -/
theorem loadsChain_seq? : ∀ {Δ : Ctxt jasminDialect} {w m : Nat}
    {b : NFProg jasminDialect Δ [.stackArr w m]}, LoadsChain b →
    ∀ {Γ₀ : Ctxt jasminDialect} {ts : List JasminTy}
      {k : NFProg jasminDialect (.stackArr w m :: Γ₀) ts}, ChainTail .here k →
    ∀ {Γ : Ctxt jasminDialect} {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg jasminDialect Γ ts},
      NFProg.seq? k b ρ θ = some q → LoadsChain q
  | _, _, _, _, .free e b he hb, _, _, k, hk, _, ρ, θ, q, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      exact .free _ _ ((rename?_op he').symm ▸ he) (loadsChain_seq? hb hk hq')
  | _, _, _, _, .load a i b hb, _, _, k, hk, _, ρ, θ, q, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨a', i', rfl⟩ := rename?_load ρ a i he'
      exact .load _ _ _ (loadsChain_seq? hb hk hq')
  | _, _, _, _, .store v i x b hb, _, _, k, hk, _, ρ, θ, q, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨v', i', x', -, rfl⟩ := rename?_store ρ v i x he'
      exact .store _ _ _ _ (chainTail_seq? (v' := .here) hb hk rfl hq')
  | _, _, _, _, .ret vs, _, _, k, hk, _, ρ, θ, q, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at hq
      obtain ⟨ws, -, hq⟩ := hq
      exact loadsChain_rename? (loadsChain_of_chainTail hk) hq

/-! ## 5. The select lowering -/

/-- **The select lowering keeps a chain tail**, along every renaming. -/
theorem chainTail_lowerSel {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ),
      ChainTail (ren v) (NFProg.lowerSel k ren) := by
  induction h with
  | free v e k he hk ih => intro Δ ren; exact .free _ _ _ he (ih (Ctxt.Hom.lift ren))
  | store v i x k hk ih => intro Δ ren; exact .store _ _ _ _ (ih (Ctxt.Hom.lift ren))
  | ret v => intro Δ ren; exact .ret _

/-- **The select lowering keeps the shape `LoadsChain`**, along every renaming. -/
theorem loadsChain_lowerSel {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ), LoadsChain (NFProg.lowerSel p ren) := by
  induction h with
  | free e k he hk ih => intro Δ ren; exact .free _ _ he (ih _)
  | load a i k hk ih => intro Δ ren; exact .load _ _ _ (ih _)
  | store v i x k hk =>
      intro Δ ren
      exact .store _ _ _ _ (chainTail_lowerSel hk (Ctxt.Hom.lift ren))
  | ret vs => intro Δ ren; exact .ret _

/-- **The select lowering keeps the shape `LoadsChain`.** -/
theorem loadsChain_lowerSelects {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) : LoadsChain (NFProg.lowerSelects p) :=
  loadsChain_lowerSel h _

/-! ## 6. The range stage -/

section Range

open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (rangeExpr rangeRule ruleOp ruleOp_op)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop (carriedGo loopRange)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (AEnv)

/-- **The range stage keeps a binding or makes it memory-free**: the rewrite of a binding is
    the binding, a constant, or a rewrite of `ruleOp` (an arithmetic operation). -/
theorem rangeExpr_eq_or_memFree {Γ : Ctxt jasminDialect} (A : AEnv Γ) (len : Nat)
    {t : JasminTy} (e : Expr jasminDialect Γ t) :
    rangeExpr A len e = e ∨ jMemFree (rangeExpr A len e).op = true := by
  unfold rangeExpr
  split
  · exact .inl rfl
  split
  · rename_i e' he
    right
    cases t with
    | reg w =>
        simp only [CatCrypt.Crypto.Optimizer.ComRangeFold.pointExpr, Option.map_eq_some_iff] at he
        obtain ⟨_, -, rfl⟩ := he
        rfl
    | _ => simp [CatCrypt.Crypto.Optimizer.ComRangeFold.pointExpr] at he
  · rcases e with ⟨op, rfl, args⟩
    unfold rangeRule
    split
    · rename_i e' he
      right
      obtain ⟨bop, w, hop, -⟩ := ruleOp_op A op args he
      simp only
      rw [hop]
      rfl
    · exact .inl rfl

/-- **The range stage keeps a store.** -/
theorem rangeExpr_store {Γ : Ctxt jasminDialect} (A : AEnv Γ) (len : Nat) {w m : Nat}
    (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w)) :
    rangeExpr A len (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
      Expr jasminDialect Γ (.stackArr w m)) =
      ⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :=
  rfl

/-- **The traversal of the range stage keeps a chain tail**, at every annotation. -/
theorem chainTail_carriedGo {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ (A : AEnv Γ) (len : Nat) (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn),
      ChainTail v (carriedGo A len a k) := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro A len a
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len e with h | h
      · rw [h]
        exact .free _ _ _ he (ih _ _ _)
      · exact .free _ _ _ h (ih _ _ _)
  | @store Γ w m ts v i x k hk ih =>
      intro A len a
      simp only [carriedGo]
      exact .store _ _ _ _ (ih _ _ _)
  | ret v => intro A len a; exact .ret _

/-- **The traversal of the range stage keeps the shape `LoadsChain`**, at every
    annotation. -/
theorem loadsChain_carriedGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ (A : AEnv Γ) (len : Nat) (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn),
      LoadsChain (carriedGo A len a p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro A len a
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len e with h | h
      · rw [h]
        exact .free _ _ he (ih _ _ _)
      · exact .free _ _ h (ih _ _ _)
  | @load Γ w m ts a i k hk ih =>
      intro A len an
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len
        (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) with h | h
      · rw [h]
        exact .load _ _ _ (ih _ _ _)
      · exact .free _ _ h (ih _ _ _)
  | @store Γ w m ts v i x k hk =>
      intro A len a
      simp only [carriedGo]
      exact .store _ _ _ _ (chainTail_carriedGo hk _ _ _)
  | ret vs => intro A len a; exact .ret _

/-- **The range stage keeps the shape `LoadsChain`**, at every annotation. -/
theorem loadsChain_loopRange {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p)
    (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn) :
    LoadsChain (loopRange a p) :=
  loadsChain_carriedGo h _ _ _

end Range

/-! ## 7. Mask elimination, the carry pairs and the legalisation -/

section Narrow

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

/-- **Mask elimination keeps a chain tail**, at every facts and renaming. -/
theorem chainTail_maskElimGo {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ) (u : Var Δ (.stackArr w m)),
      ren v = u → ChainTail u (maskElimGo k A ren) := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro Δ A ren u hu
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _ _ hu
        · exact .free _ _ _ he (ih _ _ _ (congrArg Var.there hu))
      · exact .free _ _ _ he (ih _ _ _ (congrArg Var.there hu))
  | @store Γ w m ts v i x k hk ih =>
      intro Δ A ren u hu
      subst hu
      exact .store _ _ _ _ (ih _ _ _ rfl)
  | ret v => intro Δ A ren u hu; subst hu; exact .ret _

/-- **Mask elimination keeps the shape `LoadsChain`**, at every facts and renaming. -/
theorem loadsChain_maskElimGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ),
      LoadsChain (maskElimGo p A ren) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ A ren
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _
        · exact .free _ _ he (ih _ _)
      · exact .free _ _ he (ih _ _)
  | @load Γ w m ts a i k hk ih =>
      intro Δ A ren
      exact .load _ _ _ (ih _ _)
  | @store Γ w m ts v i x k hk =>
      intro Δ A ren
      exact .store _ _ _ _ (chainTail_maskElimGo hk _ (Ctxt.Hom.lift ren) _ rfl)
  | ret vs => intro Δ A ren; exact .ret _

/-- **The insertion of a data binding before a carry-out keeps a chain tail.** -/
theorem chainTail_carryInsert {Γ : Ctxt jasminDialect} {w' m : Nat} {ts : List JasminTy}
    {t : JasminTy} (w : Nat) (h : DialectSignature.ret (d := jasminDialect) (.addCarryHi w) = t)
    (args : HVector (fun t => Var Γ t)
      (DialectSignature.sig (d := jasminDialect) (.addCarryHi w)))
    {v : Var Γ (.stackArr w' m)} {k : NFProg jasminDialect (t :: Γ) ts}
    (hk : ChainTail v.there k) : ChainTail v (carryInsert w h args k) := by
  unfold carryInsert
  split
  · rename_i e' k' he hk'
    exact .free _ _ _ rfl (.free _ _ _ ((rename?_op he).symm ▸ rfl)
      (chainTail_rename? hk (by simp [PRen.lift, wk1]) hk'))
  · exact .free _ _ _ (by subst h; rfl) hk

/-- **The insertion of a data binding before a carry-out keeps the shape `LoadsChain`.** -/
theorem loadsChain_carryInsert {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {t : JasminTy} (w : Nat) (h : DialectSignature.ret (d := jasminDialect) (.addCarryHi w) = t)
    (args : HVector (fun t => Var Γ t)
      (DialectSignature.sig (d := jasminDialect) (.addCarryHi w)))
    {k : NFProg jasminDialect (t :: Γ) ts} (hk : LoadsChain k) :
    LoadsChain (carryInsert w h args k) := by
  unfold carryInsert
  split
  · rename_i e' k' he hk'
    exact .free _ _ rfl (.free _ _ ((rename?_op he).symm ▸ rfl) (loadsChain_rename? hk hk'))
  · exact .free _ _ (by subst h; rfl) hk

/-- **The carry pairs keep a chain tail**, at every key of the binding before. -/
theorem chainTail_carryPairGo {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ prev : Option (Nat × List Nat), ChainTail v (carryPairGo prev k) := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro prev
      unfold carryPairGo
      split
      · split
        · exact .free _ _ _ he (ih _)
        · exact chainTail_carryInsert _ _ _ (ih _)
      · exact .free _ _ _ he (ih _)
  | @store Γ w m ts v i x k hk ih =>
      intro prev
      exact .store _ _ _ _ (ih _)
  | ret v => intro prev; exact .ret _

/-- **The carry pairs keep the shape `LoadsChain`**, at every key of the binding before. -/
theorem loadsChain_carryPairGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ prev : Option (Nat × List Nat), LoadsChain (carryPairGo prev p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro prev
      unfold carryPairGo
      split
      · split
        · exact .free _ _ he (ih _)
        · exact loadsChain_carryInsert _ _ _ (ih _)
      · exact .free _ _ he (ih _)
  | @load Γ w m ts a i k hk ih =>
      intro prev
      exact .load _ _ _ (ih _)
  | @store Γ w m ts v i x k hk =>
      intro prev
      exact .store _ _ _ _ (chainTail_carryPairGo hk _)
  | ret vs => intro prev; exact .ret _

end Narrow

/-- **The region legalisation keeps the shape `LoadsChain`.** -/
theorem loadsChain_legalizeRegion {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : LoadsChain p) : LoadsChain (legalizeRegion p) := h

/-! ## 8. The e-graph pass at the jasmin rules -/

section Aegraph

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (Alt RuleSet pick pick_prop reduceOne
  reduceAlt classAlts)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (nfGo aegraphOptNF)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)

/-- An alternative of extraction binds memory-free operations only. -/
def AltFree {Δ : Ctxt jasminDialect} {s : JasminTy} : Alt Δ s → Prop
  | .var _ => True
  | .one e => jMemFree e.op = true
  | .two e1 e2 => jMemFree e1.op = true ∧ jMemFree e2.op = true

/-- A hash-consed binding is a variable or the binding itself. -/
theorem reduceOne_cases {Δ : Ctxt jasminDialect} {s : JasminTy} (pure : JasminOp → Bool)
    (M : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.Tbl jasminDialect)
    (e : Expr jasminDialect Δ s) :
    (∃ w, reduceOne pure M e = .var w) ∨ reduceOne pure M e = .one e := by
  unfold reduceOne
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

/-- A hash-consed binding of an operation that is not merged is the binding itself. -/
theorem reduceOne_of_not_pure {Δ : Ctxt jasminDialect} {s : JasminTy} {pure : JasminOp → Bool}
    (M : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.Tbl jasminDialect)
    {e : Expr jasminDialect Δ s} (h : pure e.op = false) : reduceOne pure M e = .one e := by
  simp [reduceOne, CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.findVar, h]

/-- **Hash-consing keeps a memory-free alternative memory-free.** -/
theorem reduceAlt_free {Δ : Ctxt jasminDialect} {s : JasminTy} (pure : JasminOp → Bool)
    (M : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.Tbl jasminDialect) (a : Alt Δ s)
    (h : AltFree a) : AltFree (reduceAlt pure M a) := by
  cases a with
  | var v => trivial
  | one e =>
      rcases reduceOne_cases pure M e with ⟨w, hw⟩ | hw <;>
        simp only [reduceAlt, hw, AltFree]
      exact h
  | two e1 e2 =>
      simp only [reduceAlt]
      split
      · rcases reduceOne_cases pure M (e2.rename _) with ⟨w, hw⟩ | hw <;> rw [hw]
        · trivial
        · exact h.2
      · exact h

/-- **The jasmin rules produce memory-free alternatives.** -/
theorem jasminRules_alts_free (D : CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.Defs)
    {Δ : Ctxt jasminDialect} {s : JasminTy} (e : Expr jasminDialect Δ s) :
    ∀ a ∈ jasminRules.alts D e, AltFree a := by
  intro a ha
  simp only [RuleSet.alts, List.mem_flatMap, jasminRules, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  obtain ⟨r, hr, ha⟩ := ha
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · change a ∈ CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.ruleAlts D e at ha
    unfold CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.ruleAlts at ha
    split at ha
    · rename_i bop w' hop args
      subst hop
      simp only [List.mem_map] at ha
      obtain ⟨t, -, rfl⟩ := ha
      cases t <;> simp only [CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.Term.toAlt, AltFree] <;>
        trivial
    · simp at ha
  · change a ∈ CatCrypt.Crypto.Optimizer.Rewrite.TraitRules.foldApply _ _ D e at ha
    unfold CatCrypt.Crypto.Optimizer.Rewrite.TraitRules.foldApply at ha
    repeat' split at ha
    all_goals try (simp at ha; done)
    rename_i c hc
    simp only [List.mem_singleton] at ha
    subst ha
    change CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.jasminReifyOp s _ = some c at hc
    cases s <;> simp only [CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.jasminReifyOp,
      Option.some.injEq, reduceCtorEq] at hc
    subst hc
    rfl
  · change a ∈ CatCrypt.Crypto.Optimizer.Rewrite.TraitRules.copyApply _ e at ha
    unfold CatCrypt.Crypto.Optimizer.Rewrite.TraitRules.copyApply at ha
    repeat' split at ha
    all_goals try (simp at ha; done)
    simp only [Option.mem_toList, Option.map_eq_some_iff] at ha
    obtain ⟨_, -, rfl⟩ := ha
    trivial
  · change a ∈ CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.cmpOneAlts D e at ha
    unfold CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.cmpOneAlts at ha
    split at ha
    · rename_i hop args
      subst hop
      simp only at ha
      split at ha
      · simp only [List.mem_singleton] at ha
        subst ha
        trivial
      · simp at ha
    · simp at ha
  · change a ∈ CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.mersenneAlts D e at ha
    unfold CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.mersenneAlts at ha
    split at ha
    · rename_i w' hop args
      subst hop
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.mersenneTerms, List.mem_append] at ha
      rcases ha with ha | ha <;> split at ha <;>
        first
        | (simp at ha)
        | (unfold CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.mersenneAlt at ha
           repeat' split at ha
           all_goals try (simp at ha; done)
           simp only [List.mem_singleton] at ha
           subst ha
           exact ⟨rfl, rfl⟩)
    · simp at ha

/-- **The jasmin rules produce no alternative for a store.** -/
theorem jasminRules_alts_store (D : CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.Defs)
    {Δ : Ctxt jasminDialect} {w m : Nat} (v : Var Δ (.stackArr w m)) (i : Var Δ (.reg 64))
    (x : Var Δ (.reg w)) :
    jasminRules.alts D (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
      Expr jasminDialect Δ (.stackArr w m)) = [] :=
  rfl

/-- **Extraction keeps a store.** -/
theorem choose_store (S : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.Tbl jasminDialect ×
      CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.Defs)
    {Δ : Ctxt jasminDialect} {w m : Nat} (v : Var Δ (.stackArr w m)) (i : Var Δ (.reg 64))
    (x : Var Δ (.reg w)) :
    CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.choose jasminRules S
      (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
        Expr jasminDialect Δ (.stackArr w m)) =
      .one ⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ := by
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.choose
  rw [show classAlts jasminRules S _ = [] from
    congrArg (List.map _) (jasminRules_alts_store _ _ _ _)]
  exact reduceOne_of_not_pure _ rfl

/-- **Extraction of a binding** is a variable, the binding, or a memory-free alternative. -/
theorem choose_cases (S : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.Tbl jasminDialect ×
      CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.Defs)
    {Δ : Ctxt jasminDialect} {s : JasminTy} (e : Expr jasminDialect Δ s) :
    (∃ w, CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.choose jasminRules S e = .var w)
      ∨ CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.choose jasminRules S e = .one e
      ∨ AltFree (CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.choose jasminRules S e) := by
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.choose
  refine pick_prop jasminRules _
    (fun a => (∃ w, a = .var w) ∨ a = .one e ∨ AltFree a) _ _ ?_ ?_
  · rcases reduceOne_cases jasminRules.pure S.1 e with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · intro a ha _
    simp only [classAlts, List.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact .inr (.inr (reduceAlt_free _ _ a' (jasminRules_alts_free S.2 e a' ha')))

/-- **The e-graph traversal keeps a chain tail**, along every renaming and state. -/
theorem chainTail_nfGo {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ {Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom Γ Δ) S (u : Var Δ (.stackArr w m)), ρ v = u →
      ChainTail u (nfGo jasminRules ρ S k) := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro Δ ρ S u hu
      simp only [nfGo]
      have hc := choose_cases S (e.rename ρ)
      split
      · exact ih _ _ _ hu
      · rename_i e2 he2
        rw [he2] at hc
        rcases hc with ⟨_, hc⟩ | hc | hc
        · cases hc
        · cases hc
          exact .free _ _ _ he (ih _ _ _ (congrArg Var.there hu))
        · exact .free _ _ _ hc (ih _ _ _ (congrArg Var.there hu))
      · rename_i e1 e2 he2
        rw [he2] at hc
        rcases hc with ⟨_, hc⟩ | hc | hc
        · cases hc
        · cases hc
        · exact .free _ _ _ hc.1 (.free _ _ _ hc.2
            (ih _ _ _ (congrArg (fun x => Var.there (Var.there x)) hu)))
  | @store Γ w m ts v i x k hk ih =>
      intro Δ ρ S u hu
      subst hu
      simp only [nfGo]
      rw [show Expr.rename ρ (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
          Expr jasminDialect Γ (.stackArr w m)) =
          ⟨.stackStore w m, rfl, .cons (ρ v) (.cons (ρ i) (.cons (ρ x) .nil))⟩ from rfl,
        choose_store]
      exact .store _ _ _ _ (ih _ _ _ rfl)
  | ret v => intro Δ ρ S u hu; subst hu; exact .ret _

/-- The free and load cases of `loadsChain_nfGo`: a binding that is memory-free or that the
    shape `LoadsChain` admits stays so, or becomes a variable or memory-free alternatives. -/
theorem loadsChain_nfGo_var {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom (t :: Γ) Δ) S,
      LoadsChain (nfGo jasminRules ρ S k))
    (he : ∀ {Θ : Ctxt jasminDialect} (k' : NFProg jasminDialect (t :: Θ) ts) (ρ : Ctxt.Hom Γ Θ),
      LoadsChain k' → LoadsChain (.var (e.rename ρ) k'))
    (ρ : Ctxt.Hom Γ Δ) (S : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.Tbl jasminDialect ×
      CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.Defs) :
    LoadsChain (nfGo jasminRules ρ S (.var e k)) := by
  simp only [nfGo]
  have hc := choose_cases S (e.rename ρ)
  split
  · exact hk _ _
  · rename_i e2 he2
    rw [he2] at hc
    rcases hc with ⟨_, hc⟩ | hc | hc
    · cases hc
    · cases hc
      exact he _ _ (hk _ _)
    · exact .free _ _ hc (hk _ _)
  · rename_i e1 e2 he2
    rw [he2] at hc
    rcases hc with ⟨_, hc⟩ | hc | hc
    · cases hc
    · cases hc
    · exact .free _ _ hc.1 (.free _ _ hc.2 (hk _ _))

/-- **The e-graph traversal keeps the shape `LoadsChain`**, along every renaming and state. -/
theorem loadsChain_nfGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ {Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom Γ Δ) S, LoadsChain (nfGo jasminRules ρ S p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ ρ S
      exact loadsChain_nfGo_var e k ih (fun _ _ hk' => .free _ _ he hk') ρ S
  | @load Γ w m ts a i k hk ih =>
      intro Δ ρ S
      exact loadsChain_nfGo_var ⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ k ih
        (fun _ ρ' hk' => .load (ρ' a) (ρ' i) _ hk') ρ S
  | @store Γ w m ts v i x k hk =>
      intro Δ ρ S
      simp only [nfGo]
      rw [show Expr.rename ρ (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
          Expr jasminDialect Γ (.stackArr w m)) =
          ⟨.stackStore w m, rfl, .cons (ρ v) (.cons (ρ i) (.cons (ρ x) .nil))⟩ from rfl,
        choose_store]
      exact .store _ _ _ _ (chainTail_nfGo hk (Ctxt.Hom.lift ρ) _ _ rfl)
  | ret vs => intro Δ ρ S; exact .ret _

/-- **The e-graph pass at the jasmin rules keeps the shape `LoadsChain`.** -/
theorem loadsChain_aegraphOptNF {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    LoadsChain (aegraphOptNF jasminRules p) :=
  loadsChain_nfGo h _ _

end Aegraph

/-! ## 9. The widening of narrow words -/

section Widen

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

/-- A straight-line block binds memory-free operations only. -/
inductive ComFree : {Δ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Δ t → Prop
  /-- The return. -/
  | ret {Δ : Ctxt jasminDialect} {t : JasminTy} (v : Var Δ t) : ComFree (.ret v)
  /-- A memory-free binding in front. -/
  | var {Δ : Ctxt jasminDialect} {t u : JasminTy} (e : Expr jasminDialect Δ u)
      (c : Com jasminDialect (u :: Δ) t) : jMemFree e.op = true → ComFree c → ComFree (.var e c)

/-- A renamed block of memory-free operations binds memory-free operations only. -/
theorem comFree_rename {Δ : Ctxt jasminDialect} {t : JasminTy} {c : Com jasminDialect Δ t}
    (h : ComFree c) : ∀ {Δ' : Ctxt jasminDialect} (f : Ctxt.Hom Δ Δ'),
      ComFree (Com.rename f c) := by
  induction h with
  | ret v => intro Δ' f; exact .ret _
  | var e c he _ ih => intro Δ' f; exact .var _ _ he (ih _)

theorem comFree_withMask {Δ : Ctxt jasminDialect} (W : Nat) (m : Option Nat)
    (e : Expr jasminDialect Δ (.reg W)) (he : jMemFree e.op = true) :
    ComFree (withMask W m e) := by
  cases m with
  | none => exact .var _ _ he (.ret _)
  | some w => exact .var _ _ he (.var _ _ rfl (.var _ _ rfl (.ret _)))

/-- **The widened block of a memory-free operation binds memory-free operations only.** -/
theorem comFree_wideOpBlock? {Γ : Ctxt jasminDialect} (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op))
    {blk : Com jasminDialect (Γ.map wideTy)
      (wideTy (DialectSignature.ret (d := jasminDialect) op))}
    (hop : jMemFree op = true) (h : wideOpBlock? op args = some blk) : ComFree blk := by
  cases op <;> simp only [jMemFree, Bool.false_eq_true] at hop <;>
    simp only [wideOpBlock?, reduceCtorEq] at h <;> cases h
  · unfold arithBlock
    split
    · split
      · exact comFree_withMask _ _ _ rfl
      · exact comFree_withMask _ _ _ rfl
      · exact comFree_withMask _ _ _ rfl
      · exact .var _ _ rfl (.var _ _ rfl (comFree_withMask _ _ _ rfl))
      · exact .var _ _ rfl (.var _ _ rfl (comFree_withMask _ _ _ rfl))
      all_goals exact .var _ _ rfl (.ret _)
    · exact .var _ _ rfl (.ret _)
  · exact comFree_withMask _ _ _ rfl
  · exact .var _ _ rfl (.ret _)
  · unfold mulhiBlock
    split
    · exact .var _ _ rfl (.var _ _ rfl (.ret _))
    · exact .var _ _ rfl (.ret _)
  · unfold addLoBlock
    split
    · exact .var _ _ rfl (.var _ _ rfl (comFree_withMask _ _ _ rfl))
    · exact .var _ _ rfl (.ret _)
  · unfold addHiBlock
    split
    · exact .var _ _ rfl (.var _ _ rfl (.var _ _ rfl (.var _ _ rfl (.var _ _ rfl (.ret _)))))
    · exact .var _ _ rfl (.ret _)
  · unfold wideRorBlock
    split
    · exact .var _ _ rfl (.var _ _ rfl (comFree_withMask _ _ _ rfl))
    · exact .var _ _ rfl (.ret _)
  · exact .var _ _ rfl (.ret _)
  · unfold sarBlock
    split
    · exact .var _ _ rfl (comFree_withMask _ _ _ rfl)
    · exact .var _ _ rfl (.ret _)
  · unfold wideShlBlock
    split
    · exact comFree_withMask _ _ _ rfl
    · exact .var _ _ rfl (.ret _)
  all_goals exact .var _ _ rfl (.ret _)

/-- **The splice of a block of memory-free operations before continuations that continue a
    chain** is a chain tail. -/
theorem chainTail_spliceNF? {w m : Nat} {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (K : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)) (u : Var Δ (.stackArr w m)),
      ComFree blk →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (u' : Var Δ' (.stackArr w m)) (q' : NFProg jasminDialect Δ' ts), ren' u = u' →
        K ren' res = some q' → ChainTail u' q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk K = some q → ChainTail u q
  | _, _, .ret v, K, u, _, hK, _, h => hK _ v u _ rfl h
  | _, _, .var e blk, K, u, .var _ _ he hb, hK, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .free _ _ _ he (chainTail_spliceNF? blk _ u.there hb
        (fun ren' res u' q'' hu hq => hK _ res u' q'' hu hq) hq')

/-- **The splice of a block of memory-free operations before continuations of the shape
    `LoadsChain`** has the shape. -/
theorem loadsChain_spliceNF? {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (K : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)),
      ComFree blk →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), K ren' res = some q' → LoadsChain q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk K = some q → LoadsChain q
  | _, _, .ret v, K, _, hK, _, h => hK _ v _ h
  | _, _, .var e blk, K, .var _ _ he hb, hK, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .free _ _ he (loadsChain_spliceNF? blk _ hb
        (fun ren' res q'' hq => hK _ res q'' hq) hq')

/-- The splice of a renamed one-binding block (unfolding lemma). -/
theorem spliceNF?_rename_one {Δ Δ' : Ctxt jasminDialect} {a : JasminTy} {ts : List JasminTy}
    (ren : Ctxt.Hom Δ Δ') (e : Expr jasminDialect Δ a)
    (K : {Δ'' : Ctxt jasminDialect} → Ctxt.Hom Δ' Δ'' → Var Δ'' a →
      Option (NFProg jasminDialect Δ'' ts)) :
    NFProg.spliceNF? (Com.rename ren (one e)) K =
      (K (fun x => x.there) .here).map (.var (e.rename ren)) := rfl

/-- **The widening keeps a chain tail**, along every renaming, at the image of the widened
    current version. -/
theorem chainTail_widen {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (widenP.mapCtx Γ) Δ)
      (u : Var Δ (.stackArr (wideW w) m)) {q : NFProg jasminDialect Δ (ts.map widenP.mapTy)},
      ren (mapVar v) = u → NFProg.map? widenP widenP_regionTypes k ren = some q →
      ChainTail u q := by
  induction h with
  | @free Γ w m t ts v e k he hk ih =>
      intro Δ ren u q hu hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      rcases e with ⟨op, rfl, args⟩
      exact chainTail_spliceNF? _ _ u (comFree_rename (comFree_wideOpBlock? op args he hblk) ren)
        (fun ren' res u' q' hu' hq' => ih _ u' (by subst hu; exact hu') hq') hq
  | @store Γ w m ts v i x k hk ih =>
      intro Δ ren u q hu hq
      subst hu
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackStore (wideW w) m, rfl,
          .cons (mapVar v) (.cons (mapVar i) (.cons (mapVar x) .nil))⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .store _ _ _ _ (ih _ .here rfl hq')
  | @ret Γ w m v =>
      intro Δ ren u q hu hq
      subst hu
      rw [NFProg.map?] at hq
      cases hq
      exact .ret _

/-- **The widening keeps the shape `LoadsChain`**, along every renaming. -/
theorem loadsChain_widen {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (widenP.mapCtx Γ) Δ)
      {q : NFProg jasminDialect Δ (ts.map widenP.mapTy)},
      NFProg.map? widenP widenP_regionTypes p ren = some q → LoadsChain q := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ ren q hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      rcases e with ⟨op, rfl, args⟩
      exact loadsChain_spliceNF? _ _ (comFree_rename (comFree_wideOpBlock? op args he hblk) ren)
        (fun ren' res q' hq' => ih _ hq') hq
  | @load Γ w m ts a i k hk ih =>
      intro Δ ren q hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackLoad (wideW w) m, rfl,
          .cons (mapVar a) (.cons (mapVar i) .nil)⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .load _ _ _ (ih _ hq')
  | @store Γ w m ts v i x k hk =>
      intro Δ ren q hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackStore (wideW w) m, rfl,
          .cons (mapVar v) (.cons (mapVar i) (.cons (mapVar x) .nil))⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .store _ _ _ _ (chainTail_widen hk _ .here rfl hq')
  | @ret Γ ts vs =>
      intro Δ ren q hq
      rw [NFProg.map?] at hq
      cases hq
      exact .ret _

/-- **The narrow-word stages keep the shape `LoadsChain`.** -/
theorem loadsChain_narrowPrep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (h : LoadsChain p) (hq : narrowPrep p = some q) : LoadsChain q := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  exact loadsChain_carryPairGo (loadsChain_dce (loadsChain_maskElimGo
    (loadsChain_widen h _ h₀) _ _)) _

end Widen

/-! ## 10. The steps after the splice -/

section Steps

open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (lowerSelectsStep aegraphStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)

/-- **The end of the lowering of a raised body keeps the shape `LoadsChain`**: the carried
    form, the forwarding of loads from one-word arrays and dead-binding elimination. -/
theorem loadsChain_lowerBodyTail {as rs : List JasminTy} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (hΓ : Γ = as) (hts : ts = rs) {r : NFProg jasminDialect Γ ts}
    (h : LoadsChain r) :
    LoadsChain (NFProg.dce (NFFwdLoad1.fwdLoad1 (FieldDialectStep.castNF hΓ hts r))) :=
  loadsChain_dce (loadsChain_fwdLoad1 (loadsChain_castNF hΓ hts h))

/-- **The select lowering step keeps the shape `LoadsChain`.** -/
theorem loadsChain_lowerSelectsStep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (h : LoadsChain p)
    (hq : (lowerSelectsStep Γ ts).run p = some q) : LoadsChain q := by
  cases hq
  exact loadsChain_lowerSelects h

/-- **The range step keeps the shape `LoadsChain`.** -/
theorem loadsChain_synRangeStep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (h : LoadsChain p)
    (hq : (synRangeStep Γ ts).run p = some q) : LoadsChain q := by
  cases hq
  exact loadsChain_loopRange h _

/-- **The e-graph step at the jasmin rules keeps the shape `LoadsChain`.** -/
theorem loadsChain_aegraphStep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (h : LoadsChain p)
    (hq : (aegraphStep jasminRules Γ ts).run p = some q) : LoadsChain q := by
  cases hq
  exact loadsChain_aegraphOptNF h

/-- **The steps after the field dialect step, the narrow-word stages and the legalisation keep
    the shape `LoadsChain`**: from a program of the shape after the splice of the wide blocks,
    the program that the export receives has the shape. -/
theorem loadsChain_afterSplice {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p p₁ p₂ p₃ : NFProg jasminDialect Γ [t]}
    {q : NFProg jasminDialect (Γ.map NarrowWords.wideTy) [NarrowWords.wideTy t]}
    (h : LoadsChain p) (h₁ : (lowerSelectsStep Γ [t]).run p = some p₁)
    (h₂ : (synRangeStep Γ [t]).run p₁ = some p₂)
    (h₃ : (aegraphStep jasminRules Γ [t]).run p₂ = some p₃)
    (hq : NarrowWords.narrowPrep p₃ = some q) : LoadsChain (legalizeRegion q) :=
  loadsChain_legalizeRegion (loadsChain_narrowPrep (loadsChain_aegraphStep
    (loadsChain_synRangeStep (loadsChain_lowerSelectsStep h h₁) h₂) h₃) hq)

end Steps

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
