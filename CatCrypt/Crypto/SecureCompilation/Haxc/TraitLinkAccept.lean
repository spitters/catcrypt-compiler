/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
public import CatCrypt.Crypto.Hax.TraitLink
public import CatCrypt.Crypto.Hax.FrontTyping

/-!
# The front accepts the callees of trait links

`HaxModule.withTraitLinks` adds to a module, for each declared trait head, the callee
`TraitLink.wrapper`: the extraction `ByteWords.traitWrapperTExpr`, which packs byte arguments
into words, calls the linked leaf and unpacks or flags its result. This module proves that the
front of compileA (`haxToNF`) accepts these callees: the side conditions `haxFrontShapeOk`, the
absence of integer slices (`modFnIntSlice`), the array-operation names (`crateArrOk`), and the
body of the callee in the inlining library (`NFInline.crateBody`, the check of the callees of
`HaxModule.inline?`).

The body the front prepares from the callee is the A-normal form of its extraction with the
counts of `repeat` read in (`repeatCountInline`). The proof types it in three steps.

1. `NTy` types the nested call trees of the extraction (variables, literals, calls, and
   `repeat` of two literals). The A-normal form of a tree with an `NTy` derivation is a list
   of bindings with a `BindsTy` derivation (`anf_nty`): each binding is typed by the typing
   judgement `FrontTy` of the front, except the pair of a literal count and the call of
   `repeat` that reads it.
2. `repeatCountInline` turns such a list of bindings, ending in a variable, into a chain with
   a `ChainTy` derivation (`rci_chain`): `FrontTy` bindings and calls of `repeat` with a
   literal count.
3. A chain with a `ChainTy` derivation is translated by `impToNF`
   (`impToNF_out_of_chainTy`), so the callee has a body (`crateBody_isSome_of_chainTy`).

The premises on a link are decidable and hold of the links the printer declares: the
parameter names are distinct and none is a fresh name of the A-normaliser (`anormName j`),
the leaf is not `repeat`, the call typing types the leaf at the converted argument types, and
it agrees with `hax64SigOf` on the builtin heads of the callee.

## Main definitions

* `NTy`, `NTyArgs` — nested call trees and their types.
* `BindsTy` — lists of bindings typed one after the other.
* `ChainTy` — chains of bindings typed by `FrontTy` or as a call of `repeat` with a literal
  count.
* `leafArgTy`, `leafResTy` — the types of the leaf's arguments and result.
* `WrapperSig` — a call typing that agrees with `hax64SigOf` on the builtin heads of the
  callee.

## Main results

* `impToNF_out_of_chainTy`, `crateBody_isSome_of_chainTy` — a chain with a derivation is
  translated, and a callee whose body has one has a body in the library.
* `anf_nty` — the A-normal form of a typed tree is a typed list of bindings.
* `rci_chain` — `repeatCountInline` of a typed list of bindings is a typed chain.
* `chain_wrapper` — the body the front prepares from the callee is a typed chain.
* `haxFrontShapeOk_wrapper` — the extraction of the callee passes `haxFrontShapeOk`.
* `crateBody_wrapper_isSome` — the callee has a body in the inlining library.
* `withTraitLinks_frontOk` — the callees of a module with links added pass the checks
  `haxToNF` makes of its callees.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.TraitLinkAccept

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.FrontTyping
open CatCrypt.Crypto.Hax.ImpToNF (impToNF NfEnv Out CrateFn crateSigOf hax64SigOf entryCtx
  entryEnv repeatArgs? repeatOut atomOut)
open _root_.Hax (ImpExpr ImpLit TExpr)
open _root_.Hax.ByteWords
open _root_.Hax.InlineLocalClosures (frameOk inlineSpine)

/-! ## 1. Chains of bindings and their translation -/

/-- **A chain of bindings**: an expression with a `FrontTy` derivation, or a binding of a
    value with a `FrontTy` derivation, or of a call of `repeat` on a variable of `64`-bit
    words and a literal count, before a chain. -/
inductive ChainTy (S : String → List NfTy → Option NfTy) :
    TyEnv → ImpExpr → NfTy → TyEnv → Prop
  | base {Γ Γ' : TyEnv} {e : ImpExpr} {t : NfTy} : FrontTy S Γ e t Γ' → ChainTy S Γ e t Γ'
  | letBind {Γ Γv Γ' : TyEnv} {x : String} {v b : ImpExpr} {tv t : NfTy} :
      FrontTy S Γ v tv Γv → ChainTy S ((x, tv) :: Γv) b t Γ' →
      ChainTy S Γ (.letBind x v b) t Γ'
  | letRepeat {Γ Γ' : TyEnv} {x y : String} {n : Nat} {b : ImpExpr} {t : NfTy} :
      Γ.lookup y = some (.word 64) → n < 2 ^ 64 →
      ChainTy S ((x, .arr n (.word 64)) :: Γ) b t Γ' →
      ChainTy S Γ (.letBind x (.app "repeat" [.var y, .lit (.int (n : Int))]) b) t Γ'

/-- The call of `repeat` on a variable of `64`-bit words and a literal count below `2 ^ 64` is
    translated to an array of the count of words, leaving the environment of types. -/
theorem impToNF_repeat_out (S : String → List NfTy → Option NfTy) (tgt : Option String)
    {Δ : Ctxt nfDialect} (σ : NfEnv Δ) {y : String} {n : Nat}
    (hy : (tysOf σ).lookup y = some (.word 64)) (hn : n < 2 ^ 64) :
    ∃ o, impToNF S tgt σ (.app "repeat" [.var y, .lit (.int (n : Int))]) = some o ∧
      o.t = .arr n (.word 64) ∧ tysOf o.σ = tysOf σ := by
  rw [lookup_tysOf] at hy
  obtain ⟨⟨tp, v⟩, hp, hpt⟩ := Option.map_eq_some_iff.mp hy
  simp only at hpt
  subst hpt
  have h0 : (0 : Int) ≤ n := by omega
  have h1 : (n : Int) < 2 ^ 64 := by exact_mod_cast hn
  have hr : repeatArgs? "repeat" [.var y, .lit (.int (n : Int))] = some (.var y, (n : Int)) := by
    simp [repeatArgs?, h0]
    omega
  have ha : atomOut σ (.var y) = some ⟨Δ, .word 64, .nil, σ, v⟩ := by
    simp [atomOut, hp]
  have he : impToNF S tgt σ (.app "repeat" [.var y, .lit (.int (n : Int))]) =
      repeatOut tgt σ (.var y) n := by
    rw [impToNF, ite_eq_left rfl, hr, Option.bind_some]
  rw [he, repeatOut, ha, Option.bind_some, dite_eq_left rfl]
  exact ⟨_, rfl, by simp [Out.comp, ImpToNF.bind1N], by simp [Out.comp, ImpToNF.bind1N]⟩

/-- **A chain with a derivation is translated**: from an environment of names erasing to `Γ`,
    `impToNF` returns an output of the derived type whose environment erases to the derived
    one. -/
theorem impToNF_out_of_chainTy {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {e : ImpExpr} {t : NfTy} (h : ChainTy S Γ e t Γ') :
    ∀ (tgt : Option String) {Δ : Ctxt nfDialect} (σ : NfEnv Δ), tysOf σ = Γ →
      ∃ o, impToNF S tgt σ e = some o ∧ o.t = t ∧ tysOf o.σ = Γ' := by
  induction h with
  | base h => exact impToNF_out_of_frontTy h
  | @letBind _ _ _ x _ _ _ _ hv _ ih =>
    intro tgt Δ σ hσ
    obtain ⟨ov, hov, htv, hσv⟩ := impToNF_out_of_frontTy hv (some x) σ hσ
    obtain ⟨ob, hob, htb, hσb⟩ := ih tgt ((x, ⟨ov.t, ov.res⟩) :: ov.σ) (by simp [htv, hσv])
    refine ⟨ov.comp ob, ?_, htb, hσb⟩
    show (impToNF S (some x) σ _).bind _ = _
    rw [hov, Option.bind_some, hob]
    rfl
  | @letRepeat _ _ x _ _ _ _ hy hn _ ih =>
    intro tgt Δ σ hσ
    obtain ⟨ov, hov, htv, hσv⟩ := impToNF_repeat_out S (some x) σ (hσ ▸ hy) hn
    obtain ⟨ob, hob, htb, hσb⟩ := ih tgt ((x, ⟨ov.t, ov.res⟩) :: ov.σ)
      (by simp [htv, hσv, hσ])
    refine ⟨ov.comp ob, ?_, htb, hσb⟩
    show (impToNF S (some x) σ _).bind _ = _
    rw [hov, Option.bind_some, hob]
    rfl

/-- A chain of bindings has no `whileFold`. -/
theorem whileFoldFree_of_chainTy {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {e : ImpExpr} {t : NfTy} (h : ChainTy S Γ e t Γ') : ImpToNF.whileFoldFree e = true := by
  induction h with
  | base h => exact whileFoldFree_of_frontTy h
  | letBind hv _ ih => simp [ImpToNF.whileFoldFree, whileFoldFree_of_frontTy hv, ih]
  | letRepeat _ _ _ ih =>
    simp [ImpToNF.whileFoldFree, ImpToNF.whileFoldFree.freeList, ih]

/-- **A callee body with a chain derivation has a body**: when the body of `c` has a `ChainTy`
    derivation from its parameters at the type `r`, at the call typing `crateSigOf fs base`,
    `crateBody` returns a program at the parameter types and `r`. -/
theorem crateBody_isSome_of_chainTy (fs : List CrateFn) (c : CrateFn) {as : List NfTy}
    {r : NfTy} (base : String → List NfTy → Option NfTy) {Γ' : TyEnv}
    (has : entryCtx c.params = as) (h : ChainTy (crateSigOf fs base) c.params c.body r Γ') :
    (NFInline.crateBody fs c as r base).isSome := by
  obtain ⟨o, ho, hot, -⟩ := impToNF_out_of_chainTy h none (entryEnv c.params)
    (tysOf_entryEnv _)
  simp only [NFInline.crateBody, whileFoldFree_of_chainTy h, ite_true, ho, Option.bind_some]
  rw [dite_eq_left ⟨has, hot⟩]
  rfl

/-! ## 2. Nested call trees and their A-normal form -/

mutual
/-- **A nested call tree of the type `t`** over the environment of types `Γ`: a variable of
    `Γ`, a literal, a call of a name other than `repeat` on trees whose types the call typing
    `S` accepts, or `repeat` of a literal of the type of `64`-bit words and a literal count
    below `2 ^ 64`. -/
inductive NTy (S : String → List NfTy → Option NfTy) (Γ : TyEnv) : ImpExpr → NfTy → Prop
  | var {x : String} {t : NfTy} : Γ.lookup x = some t → NTy S Γ (.var x) t
  | lit {l : ImpLit} {t : NfTy} : litTy l = some t → NTy S Γ (.lit l) t
  | app {f : String} {args : List ImpExpr} {as : List NfTy} {r : NfTy} :
      f ≠ "repeat" → NTyArgs S Γ args as → S f as = some r → NTy S Γ (.app f args) r
  | rep {l : ImpLit} {n : Nat} : litTy l = some (.word 64) → n < 2 ^ 64 →
      NTy S Γ (.app "repeat" [.lit l, .lit (.int (n : Int))]) (.arr n (.word 64))

/-- The arguments of a nested call, each a nested call tree. -/
inductive NTyArgs (S : String → List NfTy → Option NfTy) (Γ : TyEnv) :
    List ImpExpr → List NfTy → Prop
  | nil : NTyArgs S Γ [] []
  | cons {e : ImpExpr} {es : List ImpExpr} {a : NfTy} {as : List NfTy} :
      NTy S Γ e a → NTyArgs S Γ es as → NTyArgs S Γ (e :: es) (a :: as)
end

/-- **A list of bindings typed one after the other**: each binding of a value with a
    `FrontTy` derivation from the environment the bindings before it leave, or the pair of a
    binding of a literal count and a binding of the call of `repeat` on a variable of `64`-bit
    words and that count. -/
inductive BindsTy (S : String → List NfTy → Option NfTy) :
    TyEnv → List (String × ImpExpr) → TyEnv → Prop
  | nil {Γ : TyEnv} : BindsTy S Γ [] Γ
  | cons {Γ Γv Γ' : TyEnv} {x : String} {v : ImpExpr} {tv : NfTy}
      {bs : List (String × ImpExpr)} :
      FrontTy S Γ v tv Γv → BindsTy S ((x, tv) :: Γv) bs Γ' → BindsTy S Γ ((x, v) :: bs) Γ'
  | rep {Γ Γ' : TyEnv} {c m y : String} {n : Nat} {bs : List (String × ImpExpr)} :
      Γ.lookup y = some (.word 64) → n < 2 ^ 64 →
      BindsTy S ((m, .arr n (.word 64)) :: (c, .word 64) :: Γ) bs Γ' →
      BindsTy S Γ ((c, .lit (.int (n : Int))) :: (m, .app "repeat" [.var y, .var c]) :: bs) Γ'

theorem BindsTy.append {S : String → List NfTy → Option NfTy} {Γ Γ₁ Γ₂ : TyEnv}
    {bs₁ bs₂ : List (String × ImpExpr)} (h₁ : BindsTy S Γ bs₁ Γ₁) (h₂ : BindsTy S Γ₁ bs₂ Γ₂) :
    BindsTy S Γ (bs₁ ++ bs₂) Γ₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hv _ ih => exact .cons hv (ih h₂)
  | rep hy hn _ ih => exact .rep hy hn (ih h₂)

/-- An integer literal below `2 ^ 64` has the type of `64`-bit words. -/
theorem litTy_int {n : Nat} (hn : n < 2 ^ 64) : litTy (.int (n : Int)) = some (.word 64) := by
  have h0 : (0 : Int) ≤ n := by omega
  have h1 : (n : Int) < 2 ^ 64 := by exact_mod_cast hn
  have hl : ImpToNF.litInt (.int (n : Int)) = some (.word 64, (n : Int)) := by
    rw [ImpToNF.litInt, ite_eq_left ⟨h0, h1⟩]
  have ho : (NfTy.ofLit? (.word 64) (n : Int)).isSome = true := by
    rw [NfTy.ofLit?, ite_eq_left ⟨h0, h1⟩]
    rfl
  rw [litTy]
  · rw [hl, Option.bind_some]
    dsimp only
    rw [ite_eq_left ho]
  · intro b h
    cases h
  · intro h
    cases h

/-- No fresh name of the A-normaliser from the index `k` on is bound in `Γ`. -/
def AnfFresh (k : Nat) (Γ : TyEnv) : Prop := ∀ j, k ≤ j → Γ.lookup (anormName j) = none

/-- Every name `Γ` binds is bound in `Γ'` at the same type. -/
def TyExt (Γ Γ' : TyEnv) : Prop := ∀ x t, Γ.lookup x = some t → Γ'.lookup x = some t

theorem TyExt.refl (Γ : TyEnv) : TyExt Γ Γ := fun _ _ h => h

theorem TyExt.trans {Γ₁ Γ₂ Γ₃ : TyEnv} (h₁ : TyExt Γ₁ Γ₂) (h₂ : TyExt Γ₂ Γ₃) : TyExt Γ₁ Γ₃ :=
  fun x t h => h₂ x t (h₁ x t h)

theorem TyExt.cons {Γ : TyEnv} {y : String} (hy : Γ.lookup y = none) (t : NfTy) :
    TyExt Γ ((y, t) :: Γ) := by
  intro x t' hx
  have hxy : x ≠ y := by
    rintro rfl
    rw [hy] at hx
    cases hx
  have hb : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
  simp [List.lookup, hb, hx]

theorem AnfFresh.mono {k k' : Nat} {Γ : TyEnv} (h : AnfFresh k Γ) (hk : k ≤ k') :
    AnfFresh k' Γ :=
  fun j hj => h j (Nat.le_trans hk hj)

theorem AnfFresh.cons {k : Nat} {Γ : TyEnv} (h : AnfFresh k Γ) (t : NfTy) :
    AnfFresh (k + 1) ((anormName k, t) :: Γ) := by
  intro j hj
  have hne : anormName j ≠ anormName k := fun he => by
    have := anormName_inj he
    omega
  have hb : (anormName j == anormName k) = false := beq_eq_false_iff_ne.mpr hne
  simp [List.lookup, hb, h j (by omega)]

/-- Splitting the leading bindings of `prependBindings bs c` returns `bs` and `c` when `c` is
    not a binding. -/
theorem splitLetBinds_prependBindings_of_core (bs : List (String × ImpExpr)) {c : ImpExpr}
    (hc : splitLetBinds c = ([], c)) : splitLetBinds (prependBindings bs c) = (bs, c) := by
  induction bs with
  | nil => exact hc
  | cons p bs ih =>
    obtain ⟨n, v⟩ := p
    rw [prependBindings_cons, splitLetBinds_letBind, ih]

mutual
/-- **The A-normal form of a typed tree is a typed list of bindings.** From a counter `k`
    whose fresh names `Γ` does not bind, and an environment `Γ` extending the environment `Γ₀`
    of the tree, the normal form is a list of bindings `bs` before an atom or a call on atoms
    `c`; the bindings are typed from `Γ` to an extension `Γ'` of `Γ`, the bindings followed by
    a binding of `c` to any name are typed, and the next counter is fresh for `Γ'`. -/
theorem anf_nty {S : String → List NfTy → Option NfTy} {Γ₀ : TyEnv} {e : ImpExpr} {t : NfTy}
    (h : NTy S Γ₀ e t) : ∀ (k : Nat) (Γ : TyEnv), TyExt Γ₀ Γ → AnfFresh k Γ →
      ∃ bs c k' Γ', aNormTBody e k = (prependBindings bs c, k') ∧
        splitLetBinds c = ([], c) ∧ (∀ x b, bindRhs x c b = .letBind x c b) ∧
        (∀ f args, e = .app f args → ∃ vs, c = .app f vs) ∧
        k ≤ k' ∧ AnfFresh k' Γ' ∧ TyExt Γ Γ' ∧ BindsTy S Γ bs Γ' ∧
        ∀ x, BindsTy S Γ (bs ++ [(x, c)]) ((x, t) :: Γ') := by
  intro k Γ hext hfr
  match h with
  | .var hx =>
    refine ⟨[], .var _, k, Γ, rfl, rfl, fun _ _ => rfl, ?_, le_rfl, hfr, TyExt.refl _,
      BindsTy.nil, fun _ => BindsTy.cons (.var (hext _ _ hx)) BindsTy.nil⟩
    intro _ _ he
    cases he
  | .lit hl =>
    refine ⟨[], .lit _, k, Γ, rfl, rfl, fun _ _ => rfl, ?_, le_rfl, hfr, TyExt.refl _,
      BindsTy.nil, fun _ => BindsTy.cons (.lit hl) BindsTy.nil⟩
    intro _ _ he
    cases he
  | .app (f := f) hf hargs hS =>
    obtain ⟨bs, vs, k', Γ', ha, hk, hfr', hext', hbs, hvs⟩ := anf_ntyArgs hargs k Γ hext hfr
    refine ⟨bs, .app f vs, k', Γ', ?_, rfl, fun _ _ => rfl, fun g as' he => ?_, hk, hfr', hext',
      hbs, fun x => hbs.append (.cons (.app hf hvs hS) .nil)⟩
    · simp only [aNormTBody, ha]
    · cases he
      exact ⟨vs, rfl⟩
  | .rep (l := l) (n := n) hl hn =>
    have hy : ((anormName k, NfTy.word 64) :: Γ).lookup (anormName k) = some (.word 64) := by
      simp [List.lookup]
    refine ⟨[(anormName k, .lit l), (anormName (k + 1), .lit (.int (n : Int)))],
      .app "repeat" [.var (anormName k), .var (anormName (k + 1))], k + 2,
      (anormName (k + 1), .word 64) :: (anormName k, .word 64) :: Γ, ?_, rfl, fun _ _ => rfl,
      fun g as' he => ?_, by omega, (hfr.cons _).cons _,
      (TyExt.cons (hfr k le_rfl) _).trans (TyExt.cons ((hfr.cons _) (k + 1) le_rfl) _),
      .cons (.lit hl) (.cons (.lit (litTy_int hn)) .nil), fun x => ?_⟩
    · simp [aNormTBody, aNormTArgs, isVar, hoistAt, splitLetBinds, prependBindings]
    · cases he
      exact ⟨_, rfl⟩
    · exact .cons (.lit hl) (.rep hy hn .nil)

/-- **The A-normal form of typed arguments**: the hoisted bindings are typed from `Γ` to an
    extension `Γ'`, the arguments become variables typed in `Γ'`, and the next counter is
    fresh for `Γ'`. -/
theorem anf_ntyArgs {S : String → List NfTy → Option NfTy} {Γ₀ : TyEnv} {args : List ImpExpr}
    {as : List NfTy} (h : NTyArgs S Γ₀ args as) : ∀ (k : Nat) (Γ : TyEnv), TyExt Γ₀ Γ →
      AnfFresh k Γ →
      ∃ bs vs k' Γ', aNormTArgs args k = (bs, vs, k') ∧ k ≤ k' ∧ AnfFresh k' Γ' ∧
        TyExt Γ Γ' ∧ BindsTy S Γ bs Γ' ∧ FrontTyArgs S Γ' vs as Γ' := by
  intro k Γ hext hfr
  match h with
  | .nil => exact ⟨[], [], k, Γ, rfl, le_rfl, hfr, TyExt.refl _, .nil, .nil⟩
  | .cons (e := e) (a := a) he hes =>
    by_cases hv : isVar e = true
    · obtain ⟨y, rfl⟩ := isVar_eq_true hv
      obtain ⟨bs, vs, k', Γ', ha, hk, hfr', hext', hbs, hvs⟩ := anf_ntyArgs hes k Γ hext hfr
      have hy : Γ'.lookup y = some a := by
        cases he with
        | var hx => exact hext' _ _ (hext _ _ hx)
      refine ⟨bs, .var y :: vs, k', Γ', ?_, hk, hfr', hext', hbs, .cons (.var hy) hvs⟩
      simp [aNormTArgs, isVar, ha]
    · obtain ⟨B, c, k1, Γa, hb, hc, -, -, hk1, hfra, hexta, -, hB⟩ := anf_nty he k Γ hext hfr
      have hcons := TyExt.cons (hfra k1 le_rfl) a
      obtain ⟨bs, vs, k', Γ', ha, hk, hfr', hext', hbs, hvs⟩ :=
        anf_ntyArgs hes (k1 + 1) ((anormName k1, a) :: Γa) (hext.trans (hexta.trans hcons))
          (hfra.cons _)
      have hy : Γ'.lookup (anormName k1) = some a := hext' _ _ (by simp [List.lookup])
      refine ⟨B ++ [(anormName k1, c)] ++ bs, .var (anormName k1) :: vs, k', Γ', ?_, by omega,
        hfr', hexta.trans (hcons.trans hext'), (hB _).append hbs, .cons (.var hy) hvs⟩
      simp [aNormTArgs, hv, hb, hoistAt, splitLetBinds_prependBindings_of_core _ hc, ha]
end

/-! ## 3. Reading the counts of `repeat` -/

/-- The expression is a binding of a call of `repeat` on two variables. -/
def repHead : ImpExpr → Bool
  | .letBind _ (.app "repeat" [.var _, .var _]) _ => true
  | _ => false

/-- A value with a `FrontTy` derivation is no call of `repeat`. -/
theorem frontTy_ne_repeat {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv} {e : ImpExpr}
    {t : NfTy} (h : FrontTy S Γ e t Γ') (args : List ImpExpr) : e ≠ .app "repeat" args := by
  rintro rfl
  cases h with
  | app hf _ _ => exact hf rfl

theorem repeatCountBind_of_repHead {c : String} {v b : ImpExpr} (h : repHead b = false) :
    repeatCountBind c v b = .letBind c v b := by
  unfold repeatCountBind
  split
  · simp [repHead] at h
  · rfl

theorem repeatCountBind_ne_var (c : String) (v b : ImpExpr) (y : String) :
    repeatCountBind c v b ≠ .var y := by
  unfold repeatCountBind
  split
  · split <;> simp
  · simp

theorem isSomeRet_eq_true {x : String} {v b : ImpExpr} (h : isSomeRet x v b = true) :
    ∃ a, v = .app "Some" [a] ∧ b = .var x := by
  unfold isSomeRet at h
  split at h
  · rename_i a r
    exact ⟨a, rfl, by simp at h; rw [h]⟩
  · cases h

theorem getLast?_cons_of_eq_some {α : Type} {a b : α} {l : List α} (h : l.getLast? = some b) :
    (a :: l).getLast? = some b := by
  cases l with
  | nil => simp at h
  | cons c l => rw [List.getLast?_cons_cons, h]

/-- **`repeatCountInline` of a typed list of bindings ending in a variable is a typed chain**
    of the shape of the front. When the bindings are typed from `Γ` to `Γ'`, `z` has the type
    `t` in `Γ'`, and the last binding, when it binds `z`, is no `Some` call, the rewritten
    chain has a `ChainTy` derivation, passes `prepShapeB` and does not start with a call of
    `repeat` on two variables. -/
theorem rci_chain {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {bs : List (String × ImpExpr)} (h : BindsTy S Γ bs Γ') {z : String} {t : NfTy}
    (hz : Γ'.lookup z = some t) :
    (∀ x v, bs.getLast? = some (x, v) → x = z → ∀ a, v ≠ .app "Some" [a]) →
      ChainTy S Γ (repeatCountInline (prependBindings bs (.var z))) t Γ' ∧
        prepShapeB (repeatCountInline (prependBindings bs (.var z))) = true ∧
        repHead (repeatCountInline (prependBindings bs (.var z))) = false := by
  induction h with
  | nil =>
    intro _
    exact ⟨.base (.var hz), rfl, rfl⟩
  | @cons Γ₁ Γv Γ₂ x v tv bs hv hbs ih =>
    intro hlast
    obtain ⟨hc, hs, hr⟩ := ih hz (fun x' v' hl => hlast x' v' (getLast?_cons_of_eq_some hl))
    have he : repeatCountInline (prependBindings ((x, v) :: bs) (.var z)) =
        .letBind x v (repeatCountInline (prependBindings bs (.var z))) := by
      rw [prependBindings_cons, repeatCountInline, repeatCountBind_of_repHead hr]
    rw [he]
    refine ⟨.letBind hv hc, ?_, ?_⟩
    · have hns : isSomeRet x v (repeatCountInline (prependBindings bs (.var z))) = false := by
        cases hsr : isSomeRet x v (repeatCountInline (prependBindings bs (.var z))) with
        | false => rfl
        | true =>
          obtain ⟨a, rfl, hb⟩ := isSomeRet_eq_true hsr
          cases bs with
          | nil =>
            have hxz : z = x := by simpa [prependBindings, repeatCountInline] using hb
            exact absurd rfl (hlast x _ (by simp) hxz.symm a)
          | cons q bs =>
            obtain ⟨n, w⟩ := q
            rw [prependBindings_cons, repeatCountInline] at hb
            exact absurd hb (repeatCountBind_ne_var _ _ _ _)
      simp [prepShapeB, hns, hs]
    · unfold repHead
      split
      · rename_i heq
        injection heq with _ hv'
        exact absurd hv' (frontTy_ne_repeat hv _)
      · rfl
  | @rep Γ₁ Γ₂ c m y n bs hy hn hbs ih =>
    intro hlast
    obtain ⟨hc, hs, hr⟩ := ih hz (fun x' v' hl => hlast x' v'
      (getLast?_cons_of_eq_some (getLast?_cons_of_eq_some hl)))
    have he : repeatCountInline (prependBindings ((c, .lit (.int (n : Int))) ::
        (m, .app "repeat" [.var y, .var c]) :: bs) (.var z)) =
        .letBind c (.lit (.int (n : Int))) (.letBind m (.app "repeat" [.var y, .lit (.int n)])
          (repeatCountInline (prependBindings bs (.var z)))) := by
      rw [prependBindings_cons, prependBindings_cons, repeatCountInline, repeatCountInline,
        repeatCountBind_of_repHead hr]
      simp [repeatCountBind]
    rw [he]
    have hy' : ((c, NfTy.word 64) :: Γ₁).lookup y = some (.word 64) := by
      by_cases hyc : y = c
      · subst hyc
        simp [List.lookup]
      · have hb : (y == c) = false := beq_eq_false_iff_ne.mpr hyc
        simp [List.lookup, hb, hy]
    refine ⟨.letBind (.lit (litTy_int hn)) (.letRepeat hy' hn hc), ?_, rfl⟩
    simp [prepShapeB, isSomeRet, hs]

/-! ## 4. The callee of a link -/

/-- The call typing agrees with `hax64SigOf` on the builtin heads of the callee. -/
def WrapperSig (S : String → List NfTy → Option NfTy) : Prop :=
  ∀ g ∈ wrapperHeads, S g = hax64SigOf g

/-- The masked byte of a byte-word array is a word. -/
theorem nty_byteE {S : String → List NfTy → Option NfTy} (hS : WrapperSig S) {Γ : TyEnv}
    {p : String} (hp : Γ.lookup p = some (.arr 32 (.word 64))) {k : Nat} (hk : k < 2 ^ 64) :
    NTy S Γ (byteE p k).erase (.word 64) := by
  show NTy S Γ (.app "BitAnd#64" [.app "index" [.var p, .lit (.int (k : Int))],
    .lit (.int ((255 : Nat) : Int))]) _
  refine .app (by decide) (.cons (.app (r := .word 64) (by decide) (.cons (.var hp) (.cons
    (.lit (litTy_int hk)) .nil)) ?_) (.cons (.lit (litTy_int (by norm_num))) .nil)) ?_
  · rw [hS "index" (by simp [wrapperHeads])]
    rfl
  · rw [hS "BitAnd#64" (by simp [wrapperHeads])]
    rfl

theorem nty_wordE {S : String → List NfTy → Option NfTy} (hS : WrapperSig S) {Γ : TyEnv}
    {p : String} (hp : Γ.lookup p = some (.arr 32 (.word 64))) (base : Nat) :
    ∀ n, base + n < 2 ^ 64 → 8 * n < 2 ^ 64 → NTy S Γ (wordE p base n).erase (.word 64) := by
  intro n
  induction n with
  | zero => intro _ _; exact .lit (litTy_int (by norm_num))
  | succ n ih =>
    intro h1 h2
    show NTy S Γ (.app "BitOr#64" [(wordE p base n).erase,
      .app "Shl#64" [(byteE p (base + n)).erase, .lit (.int ((8 * n : Nat) : Int))]]) _
    refine .app (by decide) (.cons (ih (by omega) (by omega)) (.cons (.app (r := .word 64)
      (by decide) (.cons (nty_byteE hS hp (by omega)) (.cons (.lit (litTy_int (by omega)))
        .nil)) ?_) .nil)) ?_
    · rw [hS "Shl#64" (by simp [wrapperHeads])]
      rfl
    · rw [hS "BitOr#64" (by simp [wrapperHeads])]
      rfl

theorem nty_packE {S : String → List NfTy → Option NfTy} (hS : WrapperSig S) {Γ : TyEnv}
    {p : String} (hp : Γ.lookup p = some (.arr 32 (.word 64))) :
    ∀ j, j ≤ 4 → NTy S Γ (packE p j).erase (.arr 4 (.word 64)) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact .rep (n := 4) (litTy_int (by norm_num)) (by norm_num)
  | succ j ih =>
    intro hj
    show NTy S Γ (.app "array_update" [(packE p j).erase, .lit (.int (j : Int)),
      (wordE p (8 * j) 8).erase]) _
    refine .app (by decide) (.cons (ih (by omega)) (.cons (.lit (litTy_int (by omega)))
      (.cons (nty_wordE hS hp (8 * j) 8 (by omega) (by norm_num)) .nil))) ?_
    rw [hS "array_update" (by simp [wrapperHeads])]
    rfl

theorem nty_byteOfWordE {S : String → List NfTy → Option NfTy} (hS : WrapperSig S)
    {Γ : TyEnv} {r : String} (hr : Γ.lookup r = some (.arr 4 (.word 64))) {k : Nat}
    (hk : k < 2 ^ 64) : NTy S Γ (byteOfWordE r k).erase (.word 64) := by
  show NTy S Γ (.app "BitAnd#64" [.app "Shr#64" [.app "index" [.var r,
    .lit (.int ((k / 8 : Nat) : Int))], .lit (.int ((8 * (k % 8) : Nat) : Int))],
    .lit (.int ((255 : Nat) : Int))]) _
  have h8 : 8 * (k % 8) < 2 ^ 64 := by omega
  refine .app (by decide) (.cons (.app (r := .word 64) (by decide)
    (.cons (.app (r := .word 64) (by decide) (.cons (.var hr)
      (.cons (.lit (litTy_int (by omega))) .nil)) ?_)
    (.cons (.lit (litTy_int h8)) .nil)) ?_) (.cons (.lit (litTy_int (by norm_num))) .nil)) ?_
  · rw [hS "index" (by simp [wrapperHeads])]
    rfl
  · rw [hS "Shr#64" (by simp [wrapperHeads])]
    rfl
  · rw [hS "BitAnd#64" (by simp [wrapperHeads])]
    rfl

theorem nty_unpackE {S : String → List NfTy → Option NfTy} (hS : WrapperSig S) {Γ : TyEnv}
    {r : String} (hr : Γ.lookup r = some (.arr 4 (.word 64))) :
    ∀ k, k < 2 ^ 64 → NTy S Γ (unpackE r k).erase (.arr 32 (.word 64)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact .rep (n := 32) (litTy_int (by norm_num)) (by norm_num)
  | succ k ih =>
    intro hk
    show NTy S Γ (.app "array_update" [(unpackE r k).erase, .lit (.int (k : Int)),
      (byteOfWordE r k).erase]) _
    refine .app (by decide) (.cons (ih (by omega)) (.cons (.lit (litTy_int (by omega)))
      (.cons (nty_byteOfWordE hS hr (by omega)) .nil))) ?_
    rw [hS "array_update" (by simp [wrapperHeads])]
    rfl

/-- The type of the leaf's argument under a conversion: 4 words for `bytes`, a word for
    `keep`. -/
def leafArgTy : ArgConv → NfTy
  | .bytes => .arr 4 (.word 64)
  | .keep => .word 64

/-- The type of the leaf's result under a conversion: 4 words for `bytes`, a word for
    `flag`. -/
def leafResTy : ResConv → NfTy
  | .bytes => .arr 4 (.word 64)
  | .flag => .word 64

/-- The environment of types of the parameters of a callee. -/
def paramTys (ps : List (String × ArgConv)) : TyEnv :=
  ps.map fun p => (p.1, TraitLink.argTy p.2)

theorem lookup_paramTys {ps : List (String × ArgConv)} (hnd : (ps.map (·.1)).Nodup)
    {p : String × ArgConv} (hp : p ∈ ps) :
    (paramTys ps).lookup p.1 = some (TraitLink.argTy p.2) := by
  induction ps with
  | nil => cases hp
  | cons q ps ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp [paramTys]
    · have hne : p.1 ≠ q.1 := fun he => hnd.1 (he ▸ List.mem_map_of_mem hp')
      have hb : (p.1 == q.1) = false := beq_eq_false_iff_ne.mpr hne
      have := ih hnd.2 hp'
      simp only [paramTys, List.map_cons, List.lookup, hb] at this ⊢
      exact this

theorem lookup_paramTys_none {ps : List (String × ArgConv)} {x : String}
    (h : ∀ p ∈ ps, p.1 ≠ x) : (paramTys ps).lookup x = none := by
  induction ps with
  | nil => rfl
  | cons q ps ih =>
    have hb : (x == q.1) = false := beq_eq_false_iff_ne.mpr (h q (by simp)).symm
    have := ih (fun p hp => h p (by simp [hp]))
    simp only [paramTys, List.map_cons, List.lookup, hb] at this ⊢
    exact this

/-- The arguments of the call of the leaf are typed at the converted argument types. -/
theorem nty_leafArgs {S : String → List NfTy → Option NfTy} (hS : WrapperSig S) {Γ : TyEnv} :
    ∀ ps : List (String × ArgConv), (∀ p ∈ ps, Γ.lookup p.1 = some (TraitLink.argTy p.2)) →
      NTyArgs S Γ ((ps.map argE).map TExpr.erase) (ps.map fun p => leafArgTy p.2) := by
  intro ps hps
  induction ps with
  | nil => exact .nil
  | cons q ps ih =>
    obtain ⟨p, c⟩ := q
    refine .cons ?_ (ih fun r hr => hps r (by simp [hr]))
    have hp := hps (p, c) (by simp)
    cases c
    · exact nty_packE hS hp 4 le_rfl
    · exact .var hp

/-- The result expression of the callee is typed at the result type, from the leaf's result
    bound to `resVar`. -/
theorem nty_resE {S : String → List NfTy → Option NfTy} (hS : WrapperSig S) (res : ResConv) :
    NTy S [(resVar, leafResTy res)] (resE res).erase (TraitLink.resTy res) := by
  cases res
  · exact nty_unpackE hS (by simp [List.lookup, leafResTy]) 32 (by norm_num)
  · show NTy S _ (.app "Ne" [.var resVar, .lit (.int ((0 : Nat) : Int))]) _
    refine .app (by decide) (.cons (.var (t := .word 64) (by simp [List.lookup, leafResTy]))
      (.cons (.lit (litTy_int (by norm_num))) .nil)) ?_
    rw [hS "Ne" (by simp [wrapperHeads])]
    rfl

theorem traitWrapperTExpr_erase (leaf : String) (params : List (String × ArgConv))
    (res : ResConv) : (traitWrapperTExpr leaf params res).erase =
      .letBind resVar (.app leaf ((params.map argE).map TExpr.erase)) (resE res).erase := by
  simp [traitWrapperTExpr, TExpr.erase]

/-- The result expression of the callee is a call of `array_update` or `Ne`. -/
theorem resE_erase_app (res : ResConv) :
    ∃ g args, (resE res).erase = .app g args ∧ g ≠ "Some" ∧ g ≠ "collect" := by
  cases res <;> exact ⟨_, _, rfl, by decide, by decide⟩

theorem argE_erase_ne_map (q : String × ArgConv) (xs : List ImpExpr) :
    (argE q).erase ≠ .app "map" xs := by
  obtain ⟨p, c⟩ := q
  cases c <;> simp [argE, packE, TExpr.erase]

theorem mapSrc?_app {f : String} {as : List ImpExpr} (h : ∀ a ∈ as, ∀ xs, a ≠ .app "map" xs) :
    _root_.Hax.InlineMap.mapSrc? (.app f as) = none := by
  rcases as with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp [_root_.Hax.InlineMap.mapSrc?]
  · have := h a (by simp)
    unfold _root_.Hax.InlineMap.mapSrc?
    split <;> simp_all
  · simp [_root_.Hax.InlineMap.mapSrc?]

theorem mapSite?_app {f : String} {as : List ImpExpr} (h : ∀ a ∈ as, ∀ xs, a ≠ .app "map" xs) :
    _root_.Hax.InlineMap.mapSite? (.app f as) = none := by
  rcases as with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp [_root_.Hax.InlineMap.mapSite?]
  · have := h a (by simp)
    unfold _root_.Hax.InlineMap.mapSite?
    split <;> simp_all
  · simp [_root_.Hax.InlineMap.mapSite?]

/-- The preparation steps of the front leave the extraction of the callee unchanged. -/
theorem haxFrontPrep_wrapper (leaf : String) (params : List (String × ArgConv))
    (res : ResConv) : haxFrontPrep (traitWrapperTExpr leaf params res).erase =
      (traitWrapperTExpr leaf params res).erase := by
  obtain ⟨g, gargs, hR, -, -⟩ := resE_erase_app res
  have hA : ∀ a ∈ (params.map argE).map TExpr.erase, ∀ xs, a ≠ .app "map" xs := by
    intro a ha xs
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp (List.map_map ▸ ha)
    exact argE_erase_ne_map q xs
  rw [traitWrapperTExpr_erase, hR]
  generalize (params.map argE).map TExpr.erase = As at hA
  simp [haxFrontPrep, inlineSpine, _root_.Hax.LetIntoBranches.letsInto,
    _root_.Hax.LetIntoBranches.bindInto, _root_.Hax.InlineMap.inlineMapClosures,
    _root_.Hax.InlineMap.nameMapSources, _root_.Hax.InlineMap.inlineMaps, mapSrc?_app hA,
    mapSite?_app hA]

/-- A name whose second character is not `_` is no fresh name of the A-normaliser. -/
theorem ne_anormName_of_second {s : String} (hs : s.toList[1]? ≠ some '_')
    (j : Nat) : s ≠ anormName j := by
  intro h
  have h8 : (toString "__anorm_").toList = ['_', '_', 'a', 'n', 'o', 'r', 'm', '_'] := rfl
  have := congrArg (fun s : String => (s.toList.drop 1).head?) h
  simp [anormName, h8] at this
  exact hs this

theorem resVar_ne_anormName (j : Nat) : resVar ≠ anormName j :=
  ne_anormName_of_second (by decide) j

theorem retName_ne_anormName (j : Nat) : retName ≠ anormName j :=
  ne_anormName_of_second (by decide) j

/-- **The body the front prepares from the callee is a typed chain of the shape of the
    front.** At a call typing that agrees with `hax64SigOf` on the builtin heads of the callee
    and types the leaf at the converted argument types, for distinct parameter names none of
    which is a fresh name of the A-normaliser and a leaf other than `repeat`. -/
theorem chain_wrapper {S : String → List NfTy → Option NfTy} (hS : WrapperSig S)
    (leaf : String) (params : List (String × ArgConv)) (res : ResConv)
    (hnd : (params.map (·.1)).Nodup) (hanorm : ∀ p ∈ params, ∀ j, p.1 ≠ anormName j)
    (hrep : leaf ≠ "repeat")
    (hleaf : S leaf (params.map fun p => leafArgTy p.2) = some (leafResTy res)) :
    ∃ Γ', ChainTy S (paramTys params)
        (repeatCountInline (haxFrontAnf (traitWrapperTExpr leaf params res).erase))
        (TraitLink.resTy res) Γ' ∧
      prepShapeB (repeatCountInline (haxFrontAnf (traitWrapperTExpr leaf params res).erase)) =
        true := by
  obtain ⟨g, gargs, hR, hgS, -⟩ := resE_erase_app res
  have hV : NTy S (paramTys params) (.app leaf ((params.map argE).map TExpr.erase))
      (leafResTy res) :=
    .app hrep (nty_leafArgs hS params fun p hp => lookup_paramTys hnd hp) hleaf
  have hRt : NTy S [(resVar, leafResTy res)] (.app g gargs) (TraitLink.resTy res) :=
    hR ▸ nty_resE hS res
  have hfr0 : AnfFresh 0 (paramTys params) :=
    fun j _ => lookup_paramTys_none fun p hp => hanorm p hp j
  obtain ⟨bs1, c1, k1, Γ1, ha1, hs1, hbr1, -, -, hfr1, -, -, hB1⟩ :=
    anf_nty hV 0 (paramTys params) (TyExt.refl _) hfr0
  have hfrr : AnfFresh k1 ((resVar, leafResTy res) :: Γ1) := by
    intro j hj
    have hb : (anormName j == resVar) = false :=
      beq_eq_false_iff_ne.mpr (resVar_ne_anormName j).symm
    simp [List.lookup, hb, hfr1 j hj]
  have hextr : TyExt [(resVar, leafResTy res)] ((resVar, leafResTy res) :: Γ1) := by
    intro x t hx
    by_cases hxr : x = resVar
    · subst hxr
      simpa [List.lookup] using hx
    · have hb : (x == resVar) = false := beq_eq_false_iff_ne.mpr hxr
      simp [List.lookup, hb] at hx
  obtain ⟨bs2, c2, k2, Γ2, ha2, hs2, hbr2, happ2, -, -, -, -, hB2⟩ :=
    anf_nty hRt k1 _ hextr hfrr
  obtain ⟨vs, rfl⟩ := happ2 g gargs rfl
  have hform : haxFrontAnf (traitWrapperTExpr leaf params res).erase =
      prependBindings ((bs1 ++ [(resVar, c1)]) ++ (bs2 ++ [(retName, .app g vs)]))
        (.var retName) := by
    unfold haxFrontAnf aNormalizeTotal
    rw [haxFrontPrep_wrapper, traitWrapperTExpr_erase, hR]
    simp only [bindTails, isTailBindable, ite_true]
    rw [aNormTBody, ha1]
    simp only [splitLetBinds_prependBindings_of_core _ hs1, hbr1]
    rw [aNormTBody, ha2]
    simp only [splitLetBinds_prependBindings_of_core _ hs2, hbr2, aNormTBody]
    simp [prependBindings_append, prependBindings_cons, prependBindings_nil]
  rw [hform]
  obtain ⟨hc, hs, -⟩ := rci_chain ((hB1 resVar).append (hB2 retName)) (z := retName)
    (t := TraitLink.resTy res)
    (by simp [List.lookup]) (by
      intro x v hl _ a hv
      rw [← List.append_assoc, List.getLast?_concat] at hl
      cases hl
      cases hv
      exact hgS rfl)
  exact ⟨_, hc, hs⟩

mutual
/-- A typed tree whose variables satisfy `ok` passes the source condition `ANormDOk ok` of the
    A-normaliser and binds no name. -/
theorem nty_anormDOk {S : String → List NfTy → Option NfTy} {Γ : TyEnv} {e : ImpExpr}
    {t : NfTy} (h : NTy S Γ e t) (ok : String → Bool)
    (hok : ∀ x t, Γ.lookup x = some t → ok x = true) :
    ANormDOk ok e = true ∧ ∀ bd, frameOk (fun _ => true) bd (fun _ => true) e = true := by
  match h with
  | .var hx => exact ⟨by simp [ANormDOk, hok _ _ hx], fun _ => by simp [frameOk]⟩
  | .lit _ => exact ⟨by simp [ANormDOk], fun _ => by simp [frameOk]⟩
  | .app _ hargs _ =>
    obtain ⟨h1, h2, h3⟩ := ntyArgs_anormDOk hargs ok hok
    exact ⟨by simp [ANormDOk, h1, h2], fun bd => by simp [frameOk, frameOk.okList_eq, h3 bd]⟩
  | .rep _ _ =>
    exact ⟨by simp [ANormDOk, argsOrderOk, varKept, ANormDOkList],
      fun _ => by simp [frameOk, frameOk.okList]⟩

/-- Typed arguments whose variables satisfy `ok` pass `ANormDOkList ok` and `argsOrderOk`,
    and bind no name. -/
theorem ntyArgs_anormDOk {S : String → List NfTy → Option NfTy} {Γ : TyEnv}
    {args : List ImpExpr} {as : List NfTy} (h : NTyArgs S Γ args as) (ok : String → Bool)
    (hok : ∀ x t, Γ.lookup x = some t → ok x = true) :
    ANormDOkList ok args = true ∧ argsOrderOk args = true ∧
      ∀ bd, args.all (frameOk (fun _ => true) bd (fun _ => true)) = true := by
  match h with
  | .nil => exact ⟨rfl, rfl, fun _ => rfl⟩
  | .cons (e := e) (es := es) he hes =>
    obtain ⟨a1, a2⟩ := nty_anormDOk he ok hok
    obtain ⟨b1, b2, b3⟩ := ntyArgs_anormDOk hes ok hok
    have hk : es.all (varKept e) = true := by
      rw [List.all_eq_true]
      intro a ha
      unfold varKept
      split
      · exact List.all_eq_true.mp (b3 _) a ha
      · rfl
    exact ⟨by simp [ANormDOkList, a1, b1], by simp [argsOrderOk, hk, b2],
      fun bd => by simp [a2 bd, b3 bd]⟩
end

/-- The extraction of the callee passes the source condition of the A-normaliser. -/
theorem aNormTDenoteOk_wrapper {S : String → List NfTy → Option NfTy} (hS : WrapperSig S)
    (leaf : String) (params : List (String × ArgConv)) (res : ResConv)
    (hanorm : ∀ p ∈ params, ∀ j, p.1 ≠ anormName j) (hrep : leaf ≠ "repeat")
    (hnd : (params.map (·.1)).Nodup)
    (hleaf : S leaf (params.map fun p => leafArgTy p.2) = some (leafResTy res)) :
    aNormTDenoteOk (haxFrontPrep (traitWrapperTExpr leaf params res).erase) = true := by
  have key : ∀ ok : String → Bool, ok resVar = true → ok retName = true →
      (∀ p ∈ params, ok p.1 = true) →
      ANormDOk ok (bindTails (traitWrapperTExpr leaf params res).erase) = true := by
    intro ok h1 h2 h3
    obtain ⟨g, gargs, hR, -, -⟩ := resE_erase_app res
    have hV : NTy S (paramTys params) (.app leaf ((params.map argE).map TExpr.erase))
        (leafResTy res) :=
      .app hrep (nty_leafArgs hS params fun p hp => lookup_paramTys hnd hp) hleaf
    have hRt : NTy S [(resVar, leafResTy res)] (.app g gargs) (TraitLink.resTy res) :=
      hR ▸ nty_resE hS res
    have hokV : ∀ x t, (paramTys params).lookup x = some t → ok x = true := by
      intro x t hx
      by_contra hne
      have hn : (paramTys params).lookup x = none :=
        lookup_paramTys_none fun p hp he => hne (he ▸ h3 p hp)
      rw [hn] at hx
      cases hx
    have hokR : ∀ x t, [(resVar, leafResTy res)].lookup x = some t → ok x = true := by
      intro x t hx
      by_cases hxr : x = resVar
      · exact hxr ▸ h1
      · have hb : (x == resVar) = false := beq_eq_false_iff_ne.mpr hxr
        simp [List.lookup, hb] at hx
    have hVd := (nty_anormDOk hV ok hokV).1
    have hRd := (nty_anormDOk hRt ok hokR).1
    simp only [ANormDOk, Bool.and_eq_true] at hVd hRd
    rw [traitWrapperTExpr_erase, hR]
    simp only [bindTails, isTailBindable, ite_true, ANormDOk, h1, h2, hVd.1, hVd.2, hRd.1,
      hRd.2, Bool.and_self]
  rw [haxFrontPrep_wrapper]
  refine key _ ?_ ?_ ?_
  · simpa [List.all_eq_true] using fun j _ => resVar_ne_anormName j
  · simpa [List.all_eq_true] using fun j _ => retName_ne_anormName j
  · intro p hp
    simpa [List.all_eq_true] using fun j _ => hanorm p hp j

/-- The body the front prepares from the extraction of the callee is the chain of
    `chain_wrapper`. -/
theorem haxFrontBodyP_wrapper {S : String → List NfTy → Option NfTy} (hS : WrapperSig S)
    (leaf : String) (params : List (String × ArgConv)) (res : ResConv)
    (hnd : (params.map (·.1)).Nodup) (hanorm : ∀ p ∈ params, ∀ j, p.1 ≠ anormName j)
    (hrep : leaf ≠ "repeat")
    (hleaf : S leaf (params.map fun p => leafArgTy p.2) = some (leafResTy res)) :
    haxFrontBodyP shapeAccepts (traitWrapperTExpr leaf params res).erase =
      repeatCountInline (haxFrontAnf (traitWrapperTExpr leaf params res).erase) := by
  obtain ⟨-, -, hs⟩ := chain_wrapper hS leaf params res hnd hanorm hrep hleaf
  have hroute : haxFrontRouteOkP shapeAccepts
      (repeatCountInline (haxFrontAnf (traitWrapperTExpr leaf params res).erase)) = true := by
    simp [haxFrontRouteOkP, shapeAccepts, hs]
  have hEP : haxFrontAnfEP shapeAccepts (traitWrapperTExpr leaf params res).erase =
      repeatCountInline (haxFrontAnf (traitWrapperTExpr leaf params res).erase) := by
    unfold haxFrontAnfEP
    exact anfEPick_of_ok _ _ hroute
  unfold haxFrontBodyP
  simp only [hEP]
  rw [ite_eq_left (show shapeAccepts.plain _ = true from hs)]

/-- **The extraction of the callee of a link passes the side conditions of the front.** -/
theorem haxFrontShapeOk_wrapper {S : String → List NfTy → Option NfTy} (hS : WrapperSig S)
    (leaf : String) (params : List (String × ArgConv)) (res : ResConv)
    (hnd : (params.map (·.1)).Nodup) (hanorm : ∀ p ∈ params, ∀ j, p.1 ≠ anormName j)
    (hrep : leaf ≠ "repeat")
    (hleaf : S leaf (params.map fun p => leafArgTy p.2) = some (leafResTy res)) :
    haxFrontShapeOk (traitWrapperTExpr leaf params res) = true := by
  obtain ⟨_, _, hs⟩ := chain_wrapper hS leaf params res hnd hanorm hrep hleaf
  have hroute : haxFrontRouteOkP shapeAccepts
      (repeatCountInline (haxFrontAnf (traitWrapperTExpr leaf params res).erase)) = true := by
    simp [haxFrontRouteOkP, shapeAccepts, hs]
  have hEP : haxFrontAnfEP shapeAccepts (traitWrapperTExpr leaf params res).erase =
      repeatCountInline (haxFrontAnf (traitWrapperTExpr leaf params res).erase) := by
    unfold haxFrontAnfEP
    exact anfEPick_of_ok _ _ hroute
  unfold haxFrontShapeOk haxFrontOkP
  rw [hEP, aNormTDenoteOk_wrapper hS leaf params res hanorm hrep hnd hleaf, hroute]
  rfl

/-- **The callee of a link has a body in the inlining library** (`NFInline.crateBody`, the
    check `HaxModule.inline?` makes of its callees), at the call typing `crateSigOf fs base`,
    when no callee of `fs` has a builtin head of the callee, `base` agrees with `hax64SigOf`
    on those heads, and the link meets the premises of `chain_wrapper`. -/
theorem crateBody_wrapper_isSome (t : TraitLink) (fs : List CrateFn)
    (base : String → List NfTy → Option NfTy)
    (hW : ∀ g ∈ wrapperHeads, fs.find? (·.name == g) = none)
    (hbase : ∀ g ∈ wrapperHeads, base g = hax64SigOf g)
    (hnd : (t.params.map (·.1)).Nodup) (hanorm : ∀ p ∈ t.params, ∀ j, p.1 ≠ anormName j)
    (hrep : t.leaf ≠ "repeat")
    (hleaf : crateSigOf fs base t.leaf (t.params.map fun p => leafArgTy p.2) =
      some (leafResTy t.res)) :
    (NFInline.crateBody fs (t.wrapper.prep nfBody) (entryCtx t.wrapper.params)
      (TraitLink.resTy t.res) base).isSome = true := by
  have hS : WrapperSig (crateSigOf fs base) := fun g hg => by
    funext as
    simp [crateSigOf, hW g hg, hbase g hg]
  obtain ⟨Γ', hc, -⟩ := chain_wrapper hS t.leaf t.params t.res hnd hanorm hrep hleaf
  refine crateBody_isSome_of_chainTy fs _ base rfl (Γ' := Γ') ?_
  dsimp only [ModFn.prep, TraitLink.wrapper]
  rw [nfBody, haxFrontBodyP_wrapper hS t.leaf t.params t.res hnd hanorm hrep hleaf]
  exact hc

/-- No prepared callee of the functions `fs` followed by the callees of the links `ls` has the
    name `g` when no function of `fs` and no head of `ls` has it. -/
theorem find?_map_prep_none {fs : List ModFn} {g : String} :
    (fs.map (ModFn.prep nfBody)).find? (·.name == g) = none ↔
      fs.find? (·.name == g) = none := by
  simp [List.find?_map, Function.comp_def, ModFn.prep]

theorem find?_prepared_wrappers_none {fs : List ModFn} {ls : List TraitLink} {g : String}
    (hf : fs.find? (·.name == g) = none) (hl : ∀ t ∈ ls, t.head ≠ g) :
    ((fs ++ ls.map TraitLink.wrapper).map (ModFn.prep nfBody)).find? (·.name == g) = none := by
  rw [find?_map_prep_none, List.find?_append, hf, Option.none_or, List.find?_eq_none]
  intro f hf'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf'
  simpa [TraitLink.wrapper] using hl t ht

/-- **The callees of a module with trait links added pass the checks `haxToNF` makes of its
    callees, other than the integer slices.** Let the module `m` pass `crateArrOk` of its
    prepared callees and `haxFrontShapeOk` of each extraction, have no function with a builtin
    head of the callees of the links, and let its call typing of linked functions agree with
    `hax64SigOf` on those heads. For links whose head is not `len`, whose leaf is not
    `repeat`, whose parameter names are no fresh names of the A-normaliser, and whose leaf
    the call typing of linked functions types at the converted argument types, the module
    `withTraitLinks ls m` passes the same checks, and each callee of a link has a body in the
    inlining library of the module. -/
theorem withTraitLinks_frontOk_core {ls : List TraitLink} {m m' : HaxModule}
    (h : HaxModule.withTraitLinks ls m = some m')
    (harr : crateArrOk (m.prepared nfBody) = true)
    (hshape : (m.fns.all fun f => haxFrontShapeOk f.texpr) = true)
    (hWf : ∀ g ∈ wrapperHeads, m.fns.find? (·.name == g) = none)
    (hWl : ∀ g ∈ wrapperHeads, m.linkSig g = hax64SigOf g)
    (hlinks : ∀ t ∈ ls, t.head ≠ "len" ∧ t.leaf ≠ "repeat" ∧
      (∀ p ∈ t.params, ∀ j, p.1 ≠ anormName j) ∧
      m.linkSig t.leaf (t.params.map fun p => leafArgTy p.2) = some (leafResTy t.res)) :
    crateArrOk (m'.prepared nfBody) = true ∧
      (m'.fns.all fun f => haxFrontShapeOk f.texpr) = true ∧
      ∀ t ∈ ls, (NFInline.crateBody (m'.prepared nfBody) (t.wrapper.prep nfBody)
        (entryCtx t.wrapper.params) (TraitLink.resTy t.res) m'.linkSig).isSome = true := by
  unfold HaxModule.withTraitLinks at h
  split at h
  · rename_i hls
    cases h
    obtain rfl := List.isEmpty_iff.mp hls
    exact ⟨harr, hshape, by simp⟩
  · split at h
    · rename_i _ hok
      cases h
      have hmem := fun t (ht : t ∈ ls) => HaxModule.traitLinksOk_mem hok ht
      have hheads : ∀ g ∈ wrapperHeads, ∀ t ∈ ls, t.head ≠ g :=
        fun g hg t ht he => (hmem t ht).2.2.2.1 (he ▸ hg)
      have hfW : ∀ g ∈ wrapperHeads,
          ((m.fns ++ ls.map TraitLink.wrapper).map (ModFn.prep nfBody)).find?
            (·.name == g) = none :=
        fun g hg => find?_prepared_wrappers_none (hWf g hg) (hheads g hg)
      have hS : WrapperSig (crateSigOf ((m.fns ++ ls.map TraitLink.wrapper).map
          (ModFn.prep nfBody)) m.linkSig) := fun g hg => by
        funext as
        simp only [crateSigOf, hfW g hg, hWl g hg]
      have hleaf : ∀ t ∈ ls, crateSigOf ((m.fns ++ ls.map TraitLink.wrapper).map
          (ModFn.prep nfBody)) m.linkSig t.leaf (t.params.map fun p => leafArgTy p.2) =
            some (leafResTy t.res) := by
        intro t ht
        have hl : ∀ t' ∈ ls, t'.head ≠ t.leaf := by
          intro t' ht' he
          have := List.find?_eq_none.mp (hmem t ht).2.2.2.2.2 t' ht'
          simp [he] at this
        simp only [crateSigOf, find?_prepared_wrappers_none (hmem t ht).2.2.2.2.1 hl]
        exact (hlinks t ht).2.2.2
      refine ⟨?_, ?_, ?_⟩
      · have harr' := harr
        simp only [crateArrOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          Option.isNone_iff_eq_none] at harr' ⊢
        obtain ⟨h1, h2, h3, h4⟩ := harr'
        have hW1 : "index" ∈ wrapperHeads := by simp [wrapperHeads]
        have hW2 : "array_update" ∈ wrapperHeads := by simp [wrapperHeads]
        have hW3 : "repeat" ∈ wrapperHeads := by simp [wrapperHeads]
        exact ⟨find?_prepared_wrappers_none (find?_map_prep_none.mp h1)
            fun t ht => (hlinks t ht).1,
          find?_prepared_wrappers_none (find?_map_prep_none.mp h2) (hheads _ hW1),
          find?_prepared_wrappers_none (find?_map_prep_none.mp h3) (hheads _ hW2),
          find?_prepared_wrappers_none (find?_map_prep_none.mp h4) (hheads _ hW3)⟩
      · rw [List.all_append, hshape, Bool.true_and, List.all_eq_true]
        intro f hf
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
        exact haxFrontShapeOk_wrapper hS t.leaf t.params t.res (hmem t ht).1
          (hlinks t ht).2.2.1 (hlinks t ht).2.1 (hleaf t ht)
      · intro t ht
        exact crateBody_wrapper_isSome t _ m.linkSig hfW hWl (hmem t ht).1 (hlinks t ht).2.2.1
          (hlinks t ht).2.1 (hleaf t ht)
    · cases h

/-- No integer slice is in the types of the callee of a link. -/
theorem modFnIntSlice_wrapper (t : TraitLink) : modFnIntSlice t.wrapper = false := by
  have ha : ∀ c, intSliceTy (TraitLink.argTy c) = false := by
    intro c
    cases c <;> rfl
  have hr : intSliceTy (TraitLink.resTy t.res) = false := by
    cases t.res <;> rfl
  simp [modFnIntSlice, TraitLink.wrapper, ha, hr]

/-- The functions of a module with trait links added have no integer slice when those of the
    module have none. -/
theorem withTraitLinks_noIntSlice {ls : List TraitLink} {m m' : HaxModule}
    (h : HaxModule.withTraitLinks ls m = some m')
    (hslice : (m.fns.all fun f => !modFnIntSlice f) = true) :
    (m'.fns.all fun f => !modFnIntSlice f) = true := by
  unfold HaxModule.withTraitLinks at h
  split at h
  · cases h
    exact hslice
  · split at h
    · cases h
      rw [List.all_append, hslice, Bool.true_and, List.all_eq_true]
      intro f hf
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hf
      simp [modFnIntSlice_wrapper]
    · cases h

/-- **The callees of a module with trait links added pass the checks `haxToNF` makes of its
    callees.** Under the premises of `withTraitLinks_frontOk_core` and no integer slice in the
    functions of `m`, the module `withTraitLinks ls m` passes `crateArrOk`, `haxFrontShapeOk`
    and the absence of integer slices (`modFnIntSlice`), and each callee of a link has a body
    in the inlining library of the module. -/
theorem withTraitLinks_frontOk {ls : List TraitLink} {m m' : HaxModule}
    (h : HaxModule.withTraitLinks ls m = some m')
    (harr : crateArrOk (m.prepared nfBody) = true)
    (hshape : (m.fns.all fun f => haxFrontShapeOk f.texpr) = true)
    (hslice : (m.fns.all fun f => !modFnIntSlice f) = true)
    (hWf : ∀ g ∈ wrapperHeads, m.fns.find? (·.name == g) = none)
    (hWl : ∀ g ∈ wrapperHeads, m.linkSig g = hax64SigOf g)
    (hlinks : ∀ t ∈ ls, t.head ≠ "len" ∧ t.leaf ≠ "repeat" ∧
      (∀ p ∈ t.params, ∀ j, p.1 ≠ anormName j) ∧
      m.linkSig t.leaf (t.params.map fun p => leafArgTy p.2) = some (leafResTy t.res)) :
    crateArrOk (m'.prepared nfBody) = true ∧
      (m'.fns.all fun f => haxFrontShapeOk f.texpr) = true ∧
      (m'.fns.all fun f => !modFnIntSlice f) = true ∧
      ∀ t ∈ ls, (NFInline.crateBody (m'.prepared nfBody) (t.wrapper.prep nfBody)
        (entryCtx t.wrapper.params) (TraitLink.resTy t.res) m'.linkSig).isSome = true := by
  obtain ⟨h1, h2, h3⟩ := withTraitLinks_frontOk_core h harr hshape hWf hWl hlinks
  exact ⟨h1, h2, withTraitLinks_noIntSlice h hslice, h3⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.TraitLinkAccept
