/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAbort
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCall

/-!
# Tuple flattening at the level of call trees

The second step of the chain `extChain` is tuple flattening `flatSame`, which replaces each
value of a tuple type by its components. At the reader `linkReader` of `nfDialect` a tuple
operation is a leaf of its value and a leaf call keeps its event, at argument values the
flattening does not change. The tree of a flattened program at a valuation related to the
flattened source valuation therefore has the events of the source tree, with equal answers,
and its leaves are the flattened source leaves (`ruttS_treeAt_flatProg`), at a tree call
environment in which every call of a procedure fails (the programs of the front have no
procedure call). At a context and result types without tuple types the leaves are equal
(`ruttS_treeAt_flatSame`).

## Main results

* `opTree_of_tupleHom?`: the tree of a tuple operation is the leaf of its value.
* `ruttS_eqTrans`: a relation at equal events and answers followed by a relation composes, at
  the relations of the second.
* `ruttS_treeAt_flatProg`: the stage lemma of `flatProg` at `linkReader`.
* `ruttS_treeAt_flatSame`: the stage lemma of `flatSame` at `linkReader`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeFlat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig linkReader opTree OutRel
  ruttS_obind ruttS_ofoldl ruttS_owhileIter)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## Composition after a relation at equal events -/

section EqTrans

variable {E₁ E₂ : EventSig} {h₁ : ∀ e : E₁.Event, E₁.Resp e}

/-- **A relation at equal events and answers followed by a relation composes**, at the
    relations of events and answers of the second, the composition of the relations of the
    leaves, and the failed leaves of the first, when a leaf related to a failed leaf of the
    middle tree is failed. -/
theorem ruttS_eqTrans {R₀ R₁ R₂ : Type} {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR₁ : R₀ → R₁ → Prop} {RR : R₁ → R₂ → Prop} {F₀ : R₀ → Prop} {F₁ : R₁ → Prop}
    (hF : ∀ r₀ r₁, RR₁ r₀ r₁ → F₁ r₁ → F₀ r₀)
    {t₀ : CallTree E₁ R₀} {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h01 : RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR₁ F₀ t₀ t₁)
    (h12 : RuttS h₁ RE RA RR F₁ t₁ t₂) :
    RuttS h₁ RE RA (Relation.Comp RR₁ RR) F₀ t₀ t₂ := by
  induction h01 generalizing t₂ with
  | ret h =>
    cases h12 with
    | ret h' => exact .ret ⟨_, h, h'⟩
    | fail h' => exact .fail (hF _ _ h h')
  | fail h => exact .fail h
  | vis he _ ih =>
    subst he
    cases h12 with
    | vis he' hk' => exact .vis he' fun a₁ a₂ ha => ih a₁ a₁ HEq.rfl (hk' a₁ a₂ ha)
    | skip hk' => exact .skip (ih _ _ HEq.rfl hk')
  | skip _ ih => exact .skip (ih h12)

end EqTrans

/-! ## The tree of a tuple operation -/

/-- **The tree of a tuple operation is the leaf of its value**: an operation that `tupleHom?`
    reads as a renaming of components is no leaf call, and its tree is the leaf of its
    denotation at the empty leaf table. -/
theorem opTree_of_tupleHom? {Γ Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
      (R : Ctxt.Hom (flatTy op.ret) Δ), tupleHom? ren op args = some @R →
      ∀ a : HVector NfTy.denote op.sig,
        opTree op a = .ret (nfDenoteOp NfLeafTable.empty op a) := by
  intro op
  induction op with
  | named n op ih => intro args R h a; exact ih args R h a
  | tnilV => intro _ _ _ _; rfl
  | constUnit => intro _ _ _ _; rfl
  | tconsV _ _ => intro _ _ _ _; rfl
  | thead _ _ => intro _ _ _ _; rfl
  | ttail _ _ => intro _ _ _ _; rfl
  | _ => intro args R h _; simp [tupleHom?] at h

/-! ## The stage lemma of `flatProg` -/

/-- **The stage lemma of tuple flattening at the tree level.** At a tree call environment in
    which every call of a procedure fails, a program `q` that `flatProg` returns on `p` at a
    renaming `ren` relating `W` to the flattened `V` has at `W` the events of the tree of `p` at
    `V`, with equal answers, and the flattened leaves of that tree, at every source handler. -/
theorem ruttS_treeAt_flatProg (h₁ : ∀ e : leafSig.Event, leafSig.Resp e)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (a : Valuation (d := nfDialect) as),
      tE.call f as rs a = .ret none)
    (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ)
      (q : NFProg nfDialect Δ (flatCtx ts)), flatProg p ren = some q →
      ∀ (V : Valuation Γ) (W : Valuation Δ), pullV ren W = flatV V →
      RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
        (OutRel fun x y => y = flatV x) (fun o => o = none)
        (treeAt linkReader tE fuel p V) (treeAt linkReader tE fuel q W) := by
  induction p with
  | ret vs =>
    intro Δ ren q hq V W hW
    rw [flatProg] at hq
    have h2 := Option.some.inj hq
    subst h2
    refine .ret fun a ha => ?_
    cases ha
    exact ⟨_, rfl, lookupArgs_flatArgs ren V W hW vs⟩
  | var e k ih =>
    obtain ⟨op, rfl, args⟩ := e
    intro Δ ren q hq V W hW
    rw [flatProg] at hq
    cases hT : tupleHom? ren op args with
    | some R =>
      simp only [hT] at hq
      obtain ⟨x, hx, hR⟩ := tupleHom?_spec ren V W hW NfLeafTable.empty op args R hT
      have hl : linkReader (⟨op, rfl, args⟩ : Expr nfDialect _ op.ret) V = .ret (some x) := by
        change opTree op (Expr.lookupArgs args V) = _
        rw [opTree_of_tupleHom? ren op args R hT, hx]
      show RuttS h₁ _ _ _ _ (obind (linkReader (⟨op, rfl, args⟩ : Expr nfDialect _ op.ret) V)
        fun x => treeAt linkReader tE fuel k (V.extend x)) _
      rw [hl]
      exact ih (appendHom R ren) q hq (V.extend x) W
        (pullV_appendHom_flat ren V W hW R x hR)
    | none =>
      simp only [hT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨args', ha, R, hR, k', hk, rfl⟩ := hq
      have he : linkReader (⟨op, rfl, args'⟩ : Expr nfDialect _ op.ret) W
          = linkReader (⟨op, rfl, args⟩ : Expr nfDialect _ op.ret) V := by
        change opTree op (Expr.lookupArgs args' W) = opTree op (Expr.lookupArgs args V)
        rw [atomArgs?_spec ren V W hW args args' ha]
      show RuttS h₁ _ _ _ _ (obind (linkReader (⟨op, rfl, args⟩ : Expr nfDialect _ op.ret) V)
        fun x => treeAt linkReader tE fuel k (V.extend x))
        (obind (linkReader (⟨op, rfl, args'⟩ : Expr nfDialect _ op.ret) W)
          fun x => treeAt linkReader tE fuel k' (W.extend x))
      rw [he]
      refine ruttS_obind (R := fun x y => x = y) (RuttS.refl (fun o a ha => ⟨a, ha, rfl⟩) _)
        fun x y hxy => ?_
      subst hxy
      exact ih _ k' hk (V.extend x) (W.extend x)
        (pullV_appendHom_flat _ V _ (pullV_there_flat ren V W hW x) R x
          (atomRet?_spec op.ret R hR x W))
  | forLoop count inits body k ihb ihk =>
    intro Δ ren q hq V W hW
    rw [flatProg] at hq
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨body', hb, k', hk, rfl⟩ := hq
    have hc : (ren (varHom flatTy count .here)).lookup W = count.lookup V :=
      (lookup_varRen ren V W hW count .here).trans rfl
    show RuttS h₁ _ _ _ _ (obind (ofoldl _ _ _) _) (obind (ofoldl _ _ _) _)
    rw [hc, lookupArgs_flatArgs ren V W hW inits]
    refine ruttS_obind (R := fun x y => y = flatV x) (ruttS_ofoldl (fun acc acc' i hacc => ?_)
      _ _ _ rfl) fun acc acc' hacc => ?_
    · subst hacc
      exact ihb _ body' hb
        (hvAppend acc (.cons (HasWord64.ofNat (d := nfDialect) i) V))
        (hvAppend (flatV acc) (.cons (HasWord64.ofNat (d := nfDialect) i) W))
        (pullV_appRen _ (.cons (HasWord64.ofNat (d := nfDialect) i) V)
          (.cons (HasWord64.ofNat (d := nfDialect) i) W)
          (pullV_appendHom_flat (t := NfTy.word 64) (Δ := NfTy.word 64 :: Δ) _ V _
            (pullV_there_flat ren V W hW _)
            (fun w => inlHom (d := nfDialect) (xs := [NfTy.word 64]) Δ w) _ rfl)
          _ acc)
    · subst hacc
      exact ihk _ k' hk (hvAppend acc V) (hvAppend (flatV acc) W) (pullV_appRen ren V W hW _ acc)
  | ifThenElse cond thn els k iht ihe ihk =>
    intro Δ ren q hq V W hW
    rw [flatProg] at hq
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨thn', ht, els', he, k', hk, rfl⟩ := hq
    have hc : (ren (varHom flatTy cond .here)).lookup W = cond.lookup V :=
      (lookup_varRen ren V W hW cond .here).trans rfl
    show RuttS h₁ _ _ _ _ (obind (if _ then _ else _) _) (obind (if _ then _ else _) _)
    rw [hc]
    refine ruttS_obind (R := fun x y => y = flatV x) ?_ fun r r' hr => ?_
    · split
      · exact iht ren thn' ht V W hW
      · exact ihe ren els' he V W hW
    · subst hr
      exact ihk _ k' hk (hvAppend r V) (hvAppend (flatV r) W) (pullV_appRen ren V W hW _ r)
  | whileLoop inits body k ihb ihk =>
    intro Δ ren q hq V W hW
    rw [flatProg] at hq
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨body', hb, k', hk, rfl⟩ := hq
    show RuttS h₁ _ _ _ _ (obind (owhileIter _ _ _) _) (obind (owhileIter _ _ _) _)
    rw [lookupArgs_flatArgs ren V W hW inits]
    refine ruttS_obind (R := fun x y => y = flatV x) (ruttS_owhileIter (fun acc acc' hacc => ?_)
      fuel fuel le_rfl _ _ rfl) fun acc acc' hacc => ?_
    · subst hacc
      refine NFProgCallTreeExt.RuttS.mono (RR := OutRel fun x y => y = flatV x)
        (fun o o' h a ha => ?_)
        (ihb _ body' hb (hvAppend acc V) (hvAppend (flatV acc) W)
          (pullV_appRen ren V W hW _ acc))
      obtain ⟨b, hb', rfl⟩ := h a ha
      exact ⟨_, hb', by cases a; exact ⟨rfl, rfl⟩⟩
    · subst hacc
      exact ihk _ k' hk (hvAppend acc V) (hvAppend (flatV acc) W) (pullV_appRen ren V W hW _ acc)
  | call f args k _ =>
    intro Δ ren q hq V W hW
    rw [flatProg] at hq
    simp only [Option.map_eq_some_iff] at hq
    obtain ⟨k', _, rfl⟩ := hq
    show RuttS h₁ _ _ _ _ (obind (tE.call _ _ _ _) _) (obind (tE.call _ _ _ _) _)
    rw [htE, htE]
    exact .fail rfl

/-! ## The stage lemma of `flatSame` -/

/-- A relation whose target is heterogeneously equal to a tree over equal leaf types holds at
    the cast of its relation of leaves. -/
theorem ruttS_heq_target {E₁ E₂ : EventSig} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {R₁ A B : Type} (hAB : A = B) {RR : R₁ → A → Prop} {Fail : R₁ → Prop}
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ A} {t₂' : CallTree E₂ B} (ht : t₂' ≍ t₂)
    (h : RuttS h₁ RE RA RR Fail t₁ t₂) :
    RuttS h₁ RE RA (fun r b => ∀ a, b ≍ a → RR r a) Fail t₁ t₂' := by
  subst hAB
  cases ht
  exact NFProgCallTreeExt.RuttS.mono (fun r a h' a' ha => by cases ha; exact h') h

/-- **The stage lemma of `flatSame` at the tree level.** At a tree call environment in which
    every call of a procedure fails, a program `flatSame` returns on `p` has at `V` the events
    of the tree of `p` at `V`, with equal answers and equal leaves. -/
theorem ruttS_treeAt_flatSame (h₁ : ∀ e : leafSig.Event, leafSig.Resp e)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (a : Valuation (d := nfDialect) as),
      tE.call f as rs a = .ret none)
    (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} {p q : NFProg nfDialect Γ ts}
    (hq : flatSame p = some q) (V : Valuation Γ) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (OutRel fun x y => y = x) (fun o => o = none)
      (treeAt linkReader tE fuel p V) (treeAt linkReader tE fuel q V) := by
  obtain ⟨-, hts, q0, hq0, hF⟩ := flatSame_heq
    (β := fun _ ts => CallTree leafSig (Option (Valuation (d := nfDialect) ts)))
    (fun q V => treeAt linkReader tE fuel q V) hq V
  have h := ruttS_treeAt_flatProg h₁ tE htE fuel p _ q0 hq0 V (flatV V) (pullV_id_flat V)
  have hT : Option (Valuation (d := nfDialect) (flatCtx ts))
      = Option (Valuation (d := nfDialect) ts) := by
    rw [flatCtx_of_noTuple hts]
  refine NFProgCallTreeExt.RuttS.mono (fun o o' h' x hx => ?_) (ruttS_heq_target hT hF h)
  obtain ⟨b, hb, rfl⟩ := h' (cast hT.symm o') (cast_heq _ _).symm x hx
  refine ⟨x, ?_, rfl⟩
  have h1 : o' ≍ (some (flatV x) : Option (Valuation (d := nfDialect) (flatCtx ts))) :=
    (cast_heq _ _).symm.trans (heq_of_eq hb)
  have h2 : (some (flatV x) : Option (Valuation (d := nfDialect) (flatCtx ts)))
      ≍ (some x : Option (Valuation (d := nfDialect) ts)) :=
    option_map_heq (congrArg (Valuation (d := nfDialect)) (flatCtx_of_noTuple hts)) flatV
      (flatV_heq hts) (some x)
  exact eq_of_heq (h1.trans h2)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeFlat
