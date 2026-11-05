/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap

/-!
# The calls of a structured program

`callsAll C p` states that every `call` node of the structured program `p` satisfies the
predicate `C` at its symbol and its signature. A conversion `map?` along a partial block
lowering transports it, with the signatures mapped by the type map of the lowering.

## Main definitions

* `callsAll` — every `call` node satisfies a predicate at its symbol and signature.

## Main results

* `callsAll_spliceNF?`, `callsAll_castRetHead` — the splice of a block and the cast of the
  first result type keep `callsAll`.
* `callsAll_map?` — the conversion `map?` transports `callsAll`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal

open CatCrypt.Crypto.SecureCompilation.VIR
open Ctxt (Var Valuation)

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **Every `call` node of the program satisfies `C`** at its symbol and its signature. -/
def callsAll (C : String → List d.Ty → List d.Ty → Bool) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => callsAll C k
  | _, _, .forLoop _ _ body k => callsAll C body && callsAll C k
  | _, _, .ifThenElse _ thn els k => callsAll C thn && callsAll C els && callsAll C k
  | _, _, .whileLoop _ body k => callsAll C body && callsAll C k
  | _, _, .call (as := as) (rs := rs) f _ k => C f as rs && callsAll C k

end Generic

section MapCalls

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- A block spliced before continuations that return programs of `callsAll C` gives a
    program of `callsAll C`. -/
theorem callsAll_spliceNF? (C : String → List d'.Ty → List d'.Ty → Bool) {ts : List d'.Ty} :
    {Δ : Ctxt d'} → {a : d'.Ty} → (blk : Com d' Δ a) →
    (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d' Δ' ts)) →
    (∀ {Δ' : Ctxt d'} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (q : NFProg d' Δ' ts),
      k ren res = some q → callsAll C q = true) →
    ∀ {q : NFProg d' Δ ts}, NFProg.spliceNF? blk k = some q → callsAll C q = true
  | _, _, .ret v, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact callsAll_spliceNF? C blk _ (fun ren res q hq => hk _ res q hq) hq'

/-- Carrying the first result type keeps `callsAll C`. -/
theorem callsAll_castRetHead (C : String → List d.Ty → List d.Ty → Bool) {Δ : Ctxt d}
    {a b : d.Ty} {ts : List d.Ty} (h : a = b) (p : NFProg d Δ (a :: ts)) :
    callsAll C (NFProg.castRetHead h p) = callsAll C p := by
  subst h
  rfl

/-- **The conversion `map?` transports `callsAll`**: a call of the result is a call of the
    source with its signature mapped by `P.mapTy`. -/
theorem callsAll_map? (P : PartialBlockLowering d d') (hT : P.RegionTypes)
    (C : String → List d'.Ty → List d'.Ty → Bool) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts)
    (hp : callsAll (fun f as rs => C f (as.map P.mapTy) (rs.map P.mapTy)) p = true) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) {q : NFProg d' Δ (ts.map P.mapTy)},
      NFProg.map? P hT p ren = some q → callsAll C q = true := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      rfl
  | var e k ih =>
      intro Δ ren q h
      obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact callsAll_spliceNF? C _ _ (fun ren' res q' hq' => ih hp _ hq') h
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q h
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsAll, ihb hp.1 _ hb, ihk hp.2 _ hk, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q h
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsAll, iht hp.1.1 _ ht, ihe hp.1.2 _ he, ihk hp.2 _ hk, Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q h
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsAll, callsAll_castRetHead, ihb hp.1 _ hb, ihk hp.2 _ hk, Bool.and_self]
  | call f args k ih =>
      intro Δ ren q h
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsAll, hp.1, ih hp.2 _ hk, Bool.and_self]

end MapCalls

end CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal
