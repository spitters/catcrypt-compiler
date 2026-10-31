/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps

/-!
# The output of the hax front has types of positive width

The front `haxToNF` of a module, followed by tuple flattening `flatSameStep`, returns
programs of `JasminImageOps.NFTysPos`: every let-binding, carried, branch-result and call type
is a word of positive width or a type other than a word. The check `outTyStep` returns its
input, and dead-binding elimination `NFProg.dce` keeps `NFTysPos`, so the program the chain
`extChain` hands to `nfToCatExt` satisfies `NFTysPos`.

The proof follows `FrontComplete.haxToNF_imp_NBD`: every operation of the flattened output
satisfies `FrontComplete.outOp m`, and over a context of `tyU` types (no word other than the
`64`-bit word, no slice) an operation of `outOp m` has a `tyU` result
(`FrontComplete.dom_of_outOp`), so every type bound in the program is a `tyU` type, and a
`tyU` type has positive width.

## Main results

* `nfWidthPos_of_tyU` — a `tyU` type has positive width.
* `NFTysPos_rename?`, `NFTysPos_dce` — renaming and dead-binding elimination keep `NFTysPos`.
* `NFTysPos_of_opsNB` — a program over a context of `tyU` types whose operations have `tyU`
  results on `tyU` arguments satisfies `NFTysPos`.
* `haxToNF_flatSame_NFTysPos` — the flattened output of the front, and its dead-code
  elimination, satisfy `NFTysPos`.
* `HaxModule.refusal?_eq_none_imp_NFTysPos` — on a module `refusal?` accepts, the flattened
  output of the front, and its dead-code elimination, satisfy `NFTysPos`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FrontTysPos

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (nfWidthPos NFTysPos)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (tyU tyU_vars opsNB outOp)
open Ctxt (Var)

/-- A `tyU` type has positive width. -/
theorem nfWidthPos_of_tyU {t : NfTy} (h : tyU t = true) : nfWidthPos t = true := by
  cases t with
  | word w =>
      simp only [tyU, decide_eq_true_eq] at h
      subst h
      rfl
  | _ => rfl

/-- A list of `tyU` types has positive widths. -/
theorem all_nfWidthPos_of_tyU {ts : List NfTy} (h : ∀ t ∈ ts, tyU t = true) :
    ts.all nfWidthPos = true :=
  List.all_eq_true.mpr fun t ht => nfWidthPos_of_tyU (h t ht)

/-- **Renaming keeps `NFTysPos`.** -/
theorem NFTysPos_rename? {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt nfDialect} {f : PRen Γ Δ} {p' : NFProg nfDialect Δ ts},
      NFProg.rename? f p = some p' → NFTysPos p → NFTysPos p' := by
  induction p with
  | ret vs =>
      intro Δ f p' h _
      simp only [NFProg.rename?, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      trivial
  | var e k ih =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', -, k', hk, rfl⟩ := h
      exact ⟨hp.1, ih hk hp.2⟩
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, b', hb, k', hk, rfl⟩ := h
      exact ⟨hp.1, ihb hb hp.2.1, ihk hk hp.2.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, t', ht, e', he, k', hk, rfl⟩ := h
      exact ⟨hp.1, iht ht hp.2.1, ihe he hp.2.2.1, ihk hk hp.2.2.2⟩
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, b', hb, k', hk, rfl⟩ := h
      exact ⟨hp.1, ihb hb hp.2.1, ihk hk hp.2.2⟩
  | call fn args k ih =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, k', hk, rfl⟩ := h
      exact ⟨hp.1, hp.2.1, ih hk hp.2.2⟩

/-- **Dead-binding elimination keeps `NFTysPos`.** -/
theorem NFTysPos_dce {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (hp : NFTysPos p) : NFTysPos (NFProg.dce p) := by
  induction p with
  | ret => trivial
  | var e k ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        exact NFTysPos_rename? _ hk' (ih hp.2)
      · exact ⟨hp.1, ih hp.2⟩
  | forLoop _ _ body k ihb ihk =>
      exact ⟨hp.1, ihb hp.2.1, ihk hp.2.2⟩
  | ifThenElse _ thn els k iht ihe ihk =>
      exact ⟨hp.1, iht hp.2.1, ihe hp.2.2.1, ihk hp.2.2.2⟩
  | whileLoop _ body k ihb ihk =>
      exact ⟨hp.1, ihb hp.2.1, ihk hp.2.2⟩
  | call _ _ k ih =>
      exact ⟨hp.1, hp.2.1, ih hp.2.2⟩

/-- **A program over `tyU` types with `tyU`-result operations has types of positive
    width.** When every operation that satisfies `P` has a `tyU` result on `tyU` arguments,
    a program of `opsNB P` over a context of `tyU` types satisfies `NFTysPos`, and its result
    types are `tyU` types, at every loop test `W`. -/
theorem NFTysPos_of_opsNB {P : NfOp → Bool}
    (hP : ∀ o, P o = true → (∀ t ∈ o.sig, tyU t = true) → tyU o.ret = true)
    {W : List NfTy → Bool} {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    (∀ t ∈ Γ, tyU t = true) → opsNB P p W = true → NFTysPos p ∧ ∀ t ∈ ts, tyU t = true := by
  induction p with
  | ret vs => intro hΓ _; exact ⟨trivial, tyU_vars hΓ vs⟩
  | var e k ih =>
      obtain ⟨o, rfl, args⟩ := e
      intro hΓ hp
      simp only [opsNB, Bool.and_eq_true] at hp
      have hret := hP o hp.1 (tyU_vars hΓ args)
      obtain ⟨hk, hts⟩ := ih (fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        exacts [hret, hΓ t ht]) hp.2
      exact ⟨⟨nfWidthPos_of_tyU hret, hk⟩, hts⟩
  | @forLoop Γ cs ts count inits body k ihb ihk =>
      intro hΓ hp
      simp only [opsNB, Bool.and_eq_true] at hp
      have hcs := tyU_vars hΓ inits
      obtain ⟨hb, -⟩ := ihb (fun t ht => by
          rcases List.mem_append.mp ht with ht | ht
          · exact hcs t ht
          · rcases List.mem_cons.mp ht with rfl | ht
            exacts [rfl, hΓ t ht]) hp.1
      obtain ⟨hk, hts⟩ := ihk (fun t ht => by
          rcases List.mem_append.mp ht with ht | ht
          exacts [hcs t ht, hΓ t ht]) hp.2
      exact ⟨⟨all_nfWidthPos_of_tyU hcs, hb, hk⟩, hts⟩
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      intro hΓ hp
      simp only [opsNB, Bool.and_eq_true] at hp
      obtain ⟨ht, hrs⟩ := iht hΓ hp.1.1
      obtain ⟨he, -⟩ := ihe hΓ hp.1.2
      obtain ⟨hk, hts⟩ := ihk (fun t ht => by
          rcases List.mem_append.mp ht with ht | ht
          exacts [hrs t ht, hΓ t ht]) hp.2
      exact ⟨⟨all_nfWidthPos_of_tyU hrs, ht, he, hk⟩, hts⟩
  | @whileLoop Γ cs ts inits body k ihb ihk =>
      intro hΓ hp
      simp only [opsNB, Bool.and_eq_true] at hp
      have hcs := tyU_vars hΓ inits
      have hΓ' : ∀ t ∈ cs ++ Γ, tyU t = true := fun t ht => by
        rcases List.mem_append.mp ht with ht | ht
        exacts [hcs t ht, hΓ t ht]
      obtain ⟨hb, -⟩ := ihb hΓ' hp.1.2
      obtain ⟨hk, hts⟩ := ihk hΓ' hp.2
      exact ⟨⟨all_nfWidthPos_of_tyU hcs, hb, hk⟩, hts⟩
  | call => intro _ hp; simp [opsNB] at hp

open CatCrypt.Crypto.Hax.ImpToNF (entryCtx crateSigOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (haxToNF_flatSame_opsNBLoop
  dom_of_outOp tyU_entryCtx)

/-- **The flattened output of the front has types of positive width.** When `haxToNF σ m`
    returns the program `p` and the tuple flattening `flatSameStep` returns `q` on it, the
    programs `q` and `dce q` satisfy `NFTysPos`. -/
theorem haxToNF_flatSame_NFTysPos {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule}
    {t : NfTy} {p : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hh : haxToNF σ m = some ⟨t, p⟩) {q : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hq : (flatSameStep (entryCtx (NFToRoute.abiEntry σ)) [t]).run p = some q) :
    NFTysPos q ∧ NFTysPos (NFProg.dce q) := by
  obtain ⟨-, -, hlk, -, -, -⟩ := haxToNF_eq_some hh
  obtain ⟨hls, -⟩ := haxToNF_eq_some_sig hh
  have h3 := haxToNF_flatSame_opsNBLoop hh hq
  have hP : ∀ o, outOp m o = true → (∀ t ∈ o.sig, tyU t = true) → tyU o.ret = true :=
    fun o ho hs => (dom_of_outOp hlk hls (fun _ _ => none)
      (D := ((linkedDecls m (fun _ _ => none)).filter
        (fun d => !_root_.Hax.FieldTag.fieldHeadB d.name)) ++
        opFieldDecls o)
      (fun d hd => List.mem_append_left _ hd) o ho hs
      (fun d hd => List.mem_append_right _ hd)).2
  have hpos := (NFTysPos_of_opsNB hP q (tyU_entryCtx σ) h3).1
  exact ⟨hpos, NFTysPos_dce q hpos⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.FrontTysPos

/-- **A module the front accepts has a flattened output of types of positive width.** When
    `m.refusal? σ` is `none`, `haxToNF σ m` returns a program `p`, and on every program `q`
    the tuple flattening `flatSameStep` returns on `p`, the programs `q` and `dce q` satisfy
    `NFTysPos`: every let-binding, carried, branch-result and call type is a word of positive
    width or a type other than a word. -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_NFTysPos
    {σ : CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule}
    (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), CatCrypt.Crypto.SecureCompilation.Haxc.haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ q, (CatCrypt.Crypto.SecureCompilation.Haxc.flatSameStep _ [t]).run p = some q →
        CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps.NFTysPos q ∧
          CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps.NFTysPos
            (CatCrypt.Crypto.SecureCompilation.VIR.NFProg.dce q) := by
  obtain ⟨⟨t, p⟩, hp⟩ := Option.isSome_iff_exists.mp
    ((CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_iff σ m).mp hr)
  exact ⟨t, p, hp, fun q hq =>
    CatCrypt.Crypto.SecureCompilation.Haxc.FrontTysPos.haxToNF_flatSame_NFTysPos hp hq⟩
