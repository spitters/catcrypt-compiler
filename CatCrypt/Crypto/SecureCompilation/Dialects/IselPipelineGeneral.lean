/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect

/-!
# D3 — the UNCONDITIONAL recursive ISel pass (refactored to generate equation lemmas)

This file delivers the *unconditional* `∀ c V, (walker c).denote V = c.denote V`
denote-preservation theorem for the ROR (and ANDN) native-op instruction-selection
pass — with **no fixed-point-body hypothesis** and **no operand side condition** —
that `RorImmSelect.lean` / `IselPipelineRec.lean` could only state in a *conditioned*
form (`iselPipeline_denote_of`, conditioned on a per-pass body fixed point).

## Why the landed pass could not reach `∀ c`

`RorImmSelect.rorImmSelect` (and `AndnSelect.andnSelect`) pattern-matches a
**three-binding** chain `.var e1 (.var e2 (.var e3 body))` *and* nests a dependent
op-constructor `match` inside that chain. That three-binding arm overlaps the
catch-all `.var e body` arm, and the nested dependent match prevents Lean from
generating clean equation lemmas / a `.induct` principle. Structural induction on
`c` therefore cannot push the recursion through the descent: the catch-all arm is
not definitionally `.var e (rorImmSelect body)` on an abstract `body` without first
doing WHNF on the head op — which is exactly what the dependent match blocks. (This
is documented as the obstruction in `IselPipelineRec.lean` §"On the unconditional
`∀ c` form".)

## The refactor (this file)

We split the pass into two total functions:

* a **decidable recognizer** `rorRecognize : Com Γ s → Option (RorSite Γ s)` that does
  the three-binding lookahead and the *full* operand check (operand-sound, exactly as
  the landed matcher), and returns a plain `Option` carrying the matched parameters
  `(w, n, src, deepBody)` **together with a proof** `c = mkRotrSubtree w n src deepBody`.
  The nested dependent op-`match` lives **here**, inside a function returning a plain
  `Option` — *not* inside the `Com` recursion.

* a **structurally-recursive walker** `rorWalk : Com Γ s → Com Γ s` that matches only
  `.ret v` and `.var e body` (a clean single-binding `Com` recursion). At a `.var`
  node it calls `rorRecognize`; on `some site` it emits the native `mkRorOp` over the
  *recursively-walked* matched subtree body (`site.deepBody`, a strict subterm — the
  recursion decreases by `sizeOf`); on `none` it descends into `body`.

Because the `Com` recursion in `rorWalk` is a clean `.ret`/`.var e body` split (the
op-match is isolated in `rorRecognize`'s `Option`), Lean **does** generate the
equation lemmas — so the unconditional `∀ c V, (rorWalk c).denote V = c.denote V`
goes through by well-founded recursion / structural case analysis, splitting on the
recognizer's `Option` (a plain `Option.rec`, no dependent-match block), closing the
fire case by the value lemma `RorImmSelect.mkRorOp_denote`.

The recognizer is operand-sound: `rorRecognize c = some site` carries
`c = mkRotrSubtree site.w site.n site.src site.deepBody`, so a fired site is always
the canonical rotate subtree — no miscompile (`IselPipelineRec.rorCex` is not matched).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.IselPipelineGeneral

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness

/-! ## 1. The recognizer result: a matched canonical rotate site -/

/-- A recognized canonical rotate subtree at the head of some `c : Com Γ s`: the
    width `w`, the in-range immediate `n < w`, the source variable `src`, the
    continuation `deepBody` after the three bindings, **and** a proof that `c` is
    literally `mkRotrSubtree w n src deepBody`. The equality field is the operand-soundness
    certificate: a recognized site is always the canonical `shr; shl; or` rotate
    emulation, so the rewrite to `mkRorOp` is value-preserving with no side condition,
    and `deepBody`'s `sizeOf` decrease (for the walker's termination) follows from it. -/
structure RorSite {Γ : Ctxt jasminDialect} {s : JasminTy} (c : Com jasminDialect Γ s) where
  w : Nat
  n : Nat
  src : Ctxt.Var Γ (.reg w)
  hlt : n < w
  deepBody : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s
  horig : mkRotrSubtree w n src deepBody = c

/-- `varBeq` reflects equality: a `true` operand guard yields the `Var` equality used
    to certify the recognized subtree is canonical. -/
theorem eq_of_varBeq {d : Dialect} {Γ : Ctxt d} {t : d.Ty} {a b : Ctxt.Var Γ t}
    (h : varBeq a b = true) : a = b := by
  have h' : @decide (a = b) (varDecEq a b) = true := by simpa [varBeq] using h
  exact of_decide_eq_true (inst := varDecEq a b) h'

/-! ## 2. The recognizer (the nested op-match is isolated HERE, returns `Option`)

`rorRecognize c` does the three-binding lookahead with the **full** canonical
operand check (operand-sound, exactly as `RorImmSelect.rorImmSelect`'s tightened
matcher), and returns `Option (RorSite c)`. The nested dependent op-`match` and the
`▸` operand-cast bookkeeping live entirely inside this function, which returns a
plain `Option` — so the `Com` recursion in `rorWalk` (§3) stays clean and its
equation lemmas generate. -/

/-- Decide whether `c`'s head is the canonical `shr; shl; or` rotate emulation with
    `n < w`, the `shl` reading the same `src` by `w - n`, and the `or` combining exactly
    the two preceding results. On a match, return the site (with the equality
    certificate); else `none`. -/
def rorRecognize {Γ : Ctxt jasminDialect} {s : JasminTy} :
    (c : Com jasminDialect Γ s) → Option (RorSite c)
  | .var (t := JasminTy.reg w) (.mk op1 hr1 args1)
      (.var (t := JasminTy.reg w2) (.mk op2 hr2 args2)
        (.var (t := JasminTy.reg w3) (.mk op3 hr3 args3) body)) =>
      match op1, args1, op2, args2, op3, args3 with
      | .shrImm we n, .cons src .nil, .shlImm wsh m, .cons shlSrc .nil,
          .regArith JasminBinOp.or wor, .cons orHi (.cons orLo .nil) =>
          if hcond : we = w ∧ w2 = w ∧ w3 = w ∧ n < w ∧ wsh = w ∧ wor = w2 ∧ m = w - n then
            let src' : Ctxt.Var Γ (.reg w) := hcond.1 ▸ src
            let shlSrcW : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w) :=
              hcond.2.2.2.2.1 ▸ shlSrc
            let orHiW : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w) :=
              (hcond.2.2.2.2.2.1.trans hcond.2.1) ▸ orHi
            let orLoW : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w2) :=
              hcond.2.2.2.2.2.1 ▸ orLo
            if hop : varBeq shlSrcW (Ctxt.Var.there src')
                && varBeq orHiW (Ctxt.Var.there Ctxt.Var.here)
                && varBeq orLoW Ctxt.Var.here then
              let deepBody : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s :=
                (by rw [hcond.2.1, hcond.2.2.1] : Com jasminDialect (.reg w3 :: .reg w2 :: .reg w :: Γ) s
                      = Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) ▸ body
              some { w := w, n := n, src := src', hlt := hcond.2.2.2.1,
                     deepBody := deepBody, horig := by
                       obtain ⟨hwe, hw2, hw3, hn, hwsh, hwor, hm⟩ := hcond
                       subst hwe; subst hw2; subst hw3; subst hwsh; subst hwor; subst hm
                       rw [Bool.and_eq_true, Bool.and_eq_true] at hop
                       obtain ⟨⟨h1, h2⟩, h3⟩ := hop
                       have q1 : shlSrc = src.there := eq_of_varBeq h1
                       have q2 : orHi = Ctxt.Var.here.there := eq_of_varBeq h2
                       have q3 : orLo = Ctxt.Var.here := eq_of_varBeq h3
                       show mkRotrSubtree _ _ src body = _
                       clear h1 h2 h3 src' shlSrcW orHiW orLoW deepBody
                       subst q1; subst q2; subst q3
                       rfl }
            else none
          else none
      | _, _, _, _, _, _ => none
  | _ => none

/-! ## 3. The structural walker (clean `.ret`/`.var e body` `Com` recursion)

`rorWalk` is the refactored pass. Its `Com` recursion is the clean two-arm
`.ret v` / `.var e body` split — the op-`match` lives in `rorRecognize`, which
returns a plain `Option`. At each `.var` node, `rorRecognize` decides whether the
head is a canonical rotate subtree; on `some site` we emit the native `mkRorOp`
over the **recursively-walked** matched body (`site.deepBody`, a strict subterm by
`site.horig`), on `none` we descend into `body`. Because the recursion is clean,
Lean generates the equation lemmas and the `.induct` principle (§4 uses them). -/

/-- The matched body is a strict subterm of `c`, so the walker's recursion on it
    decreases `sizeOf`. Read off `site.horig`. -/
theorem RorSite.deepBody_lt {Γ : Ctxt jasminDialect} {s : JasminTy}
    {c : Com jasminDialect Γ s} (site : RorSite c) :
    sizeOf site.deepBody < sizeOf c := by
  have key : sizeOf site.deepBody
      < sizeOf (mkRotrSubtree site.w site.n site.src site.deepBody) := by
    simp only [mkRotrSubtree, Com.var.sizeOf_spec]; omega
  rw [site.horig] at key
  exact key

/-- **The refactored ROR ISel pass.** A clean structurally-recursive walk over
    `Com jasminDialect`: at each `.var` node, fire the native `rorImm` (via `mkRorOp`)
    on a recognized canonical rotate subtree, else descend. The op-match is isolated
    in `rorRecognize` (returns `Option`), so the `Com` recursion is clean and the
    equation lemmas generate — enabling the UNCONDITIONAL `∀ c` soundness (§4). -/
def rorWalk {Γ : Ctxt jasminDialect} {s : JasminTy} :
    Com jasminDialect Γ s → Com jasminDialect Γ s
  | .ret v => .ret v
  | .var e body =>
      match rorRecognize (.var e body) with
      | some site => mkRorOp site.w site.n site.src (rorWalk site.deepBody)
      | none => .var e (rorWalk body)
  termination_by c => sizeOf c
  decreasing_by
    · exact site.deepBody_lt
    · simp_wf; omega

/-- `rorWalk` is the identity on `.ret`. -/
theorem rorWalk_ret {Γ : Ctxt jasminDialect} {s : JasminTy} (v : Ctxt.Var Γ s) :
    rorWalk (.ret v) = .ret v := by
  rw [rorWalk.eq_def]

/-- `rorWalk`'s defining equation on a fired `.var` node: when `rorRecognize` returns
    `some site`, the walk is the native `mkRorOp` over the walked deep body. -/
theorem rorWalk_var_some {Γ : Ctxt jasminDialect} {s : JasminTy} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s)
    (site : RorSite (Com.var e body)) (hrec : rorRecognize (.var e body) = some site) :
    rorWalk (.var e body)
      = mkRorOp site.w site.n site.src (rorWalk site.deepBody) := by
  rw [rorWalk.eq_def]; dsimp only; rw [hrec]

/-- `rorWalk`'s defining equation on a non-fired `.var` node: when `rorRecognize`
    returns `none`, the walk descends into the body. -/
theorem rorWalk_var_none {Γ : Ctxt jasminDialect} {s : JasminTy} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s)
    (hrec : rorRecognize (.var e body) = none) :
    rorWalk (.var e body) = .var e (rorWalk body) := by
  rw [rorWalk.eq_def]; dsimp only; rw [hrec]

/-- **`rorWalk` fires on the canonical rotate subtree** — the analogue of
    `RorImmSelect.rorImmSelect_fires` for the refactored walker. For `n < w`, walking
    `mkRotrSubtree w n src body` (the `shr; shl; or` emulation) yields the native
    `mkRorOp w n src` over the walked body. The recognizer's width/operand decisions on
    the canonical subtree are discharged by `dif_pos` / `varBeq_self`. -/
theorem rorWalk_fires {Γ : Ctxt jasminDialect} {s : JasminTy} (w n : Nat) (hlt : n < w)
    (src : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    rorWalk (mkRotrSubtree w n src body) = mkRorOp w n src (rorWalk body) := by
  -- the recognizer fires on the canonical subtree, returning a site with parameters
  -- `w, n, src, body` (its `horig` is some proof — irrelevant to the projections).
  have hrec : rorRecognize (mkRotrSubtree w n src body)
      = some { w := w, n := n, src := src, hlt := hlt, deepBody := body,
               horig := rfl } := by
    show (if _ : w = w ∧ w = w ∧ w = w ∧ n < w ∧ w = w ∧ w = w ∧ (w - n) = w - n
          then _ else _) = _
    erw [dif_pos (show w = w ∧ w = w ∧ w = w ∧ n < w ∧ w = w ∧ w = w ∧ (w - n) = w - n from
      ⟨rfl, rfl, rfl, hlt, rfl, rfl, rfl⟩)]
    simp only [varBeq_self, Bool.and_self, dite_true]; rfl
  rw [show mkRotrSubtree w n src body
        = Com.var (Expr.mk (JasminOp.shrImm w n) rfl (.cons src .nil))
            (.var (Expr.mk (JasminOp.shlImm w (w - n)) rfl (.cons (.there src) .nil))
              (.var (Expr.mk (JasminOp.regArith .or w) rfl
                  (.cons (.there .here) (.cons .here .nil)))
                body)) from rfl]
  rw [rorWalk_var_some _ _ _ hrec]

/-! ## 4. The UNCONDITIONAL soundness theorem (`∀ c`, no body fixed-point hypothesis)

This is the deliverable the conditioned `IselPipeline.iselPipeline_denote_of` /
`IselPipelineRec.iselPipeline_denote_conditioned` could not reach. Structural
induction via the **generated** `rorWalk.induct` (the refactor's payoff) pushes the
preservation through the descent; the fire case is closed by the value
lemma `mkRorOp_denote` plus body-congruence; the descend case by `Com.denote`'s
own structure. No fixed-point-body hypothesis, no operand side condition, no
`sorry`. -/

/-- **Body-congruence for `mkRotrSubtree`.** Its denotation depends on its body only
    through the body's denotation on the three-extended valuation, so bodies that
    denote equally everywhere give equal `mkRotrSubtree` denotations. (No width-`w`
    `BitVec` value is forced — the extended valuation stays abstract.) -/
theorem mkRotrSubtree_body_congr {Γ : Ctxt jasminDialect} {s : JasminTy} (w n : Nat)
    (src : Ctxt.Var Γ (.reg w))
    (b1 b2 : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s)
    (V : Ctxt.Valuation Γ) (h : ∀ V', b1.denote V' = b2.denote V') :
    (mkRotrSubtree w n src b1).denote V = (mkRotrSubtree w n src b2).denote V := by
  simp only [mkRotrSubtree, Com.denote]; apply h

/-- **THE UNCONDITIONAL ISEL SOUNDNESS.** For **every** program `c` and valuation `V`,
    the refactored ROR pass `rorWalk` preserves the denotation:
    `(rorWalk c).denote V = c.denote V`. No fixed-point-body hypothesis, no operand
    side condition (the recognizer is operand-sound via `RorSite.horig`), no `sorry`.

    Proof: structural induction via the generated `rorWalk.induct`. The fire case
    rewrites `c = mkRotrSubtree …` (the recognizer certificate `site.horig`), collapses
    the native `mkRorOp` to the emulation by the value lemma `mkRorOp_denote`,
    and discharges the walked body by the IH through `mkRotrSubtree_body_congr`. The
    descend case threads `Com.denote` through `body`'s IH. The ROR `n < w` guard never
    surfaces as a side condition because `site.hlt` carries it on every fired site. -/
theorem rorWalk_denote {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) (V : Ctxt.Valuation Γ) :
    (rorWalk c).denote V = c.denote V := by
  -- Generalize over the valuation: the fire case runs the body on a 3-extended
  -- valuation, so the IH must hold for *every* `V'`. Induct via the GENERATED
  -- `rorWalk.induct` with the `∀ V` motive.
  refine rorWalk.induct
    (motive := fun Γ c => ∀ V : Ctxt.Valuation Γ, (rorWalk c).denote V = c.denote V)
    ?_ ?_ ?_ Γ c V
  · -- `.ret v`: the walk is the identity.
    intro Γ v V; rw [rorWalk_ret]
  · -- fire: `rorRecognize (.var e body) = some site`, with `site.horig` certifying
    -- `.var e body = mkRotrSubtree site.w site.n site.src site.deepBody`.
    intro Γ t e body site hrec ih V
    rw [rorWalk_var_some e body site hrec]
    -- bring the source `(Com.var e body).denote V` to the canonical emulation's
    -- denotation via the recognizer certificate (congrArg avoids the dependent-motive
    -- rewrite, since `site`'s type mentions `Com.var e body`).
    rw [← congrArg (fun c => Com.denote c V) site.horig]
    -- collapse native `mkRorOp` to `mkRotrSubtree` (n < w from `site.hlt`)
    rw [mkRorOp_denote site.w site.n site.hlt]
    -- discharge the walked body against the original body via the IH (∀ V').
    exact mkRotrSubtree_body_congr site.w site.n site.src _ site.deepBody V ih
  · -- descend: no fire; thread `Com.denote` through the body's IH.
    intro Γ t e body hrec ih V
    rw [rorWalk_var_none e body hrec]
    simp only [Com.denote]
    rw [ih]

/-! ## 5. Worked example: a body with MULTIPLE rotate sites — ALL selected

The thing the conditioned pass could not express: a `Com` with **two** independent
rotate subtrees stacked (the inner one in the body of the outer one). `rorWalk`
selects **both** native `rorImm`s, and `rorWalk_denote` (unconditional, no per-site
`hbody` hypothesis) certifies the denotation is preserved — at concrete values. -/

/-- Two stacked rotate subtrees over `[reg 64]`: an outer rotate-by-8 whose body is an
    inner rotate-by-24, returning the inner result. Both are canonical `shr; shl; or`
    emulations, so `rorWalk` fires on **both**. -/
def twoRotates : Com jasminDialect [.reg 64] (.reg 64) :=
  mkRotrSubtree 64 8 .here
    (mkRotrSubtree 64 24 (.there (.there .here)) (.ret .here))

/-- **`rorWalk` selects BOTH native rotates** — by `rorWalk_denote`, the multi-site
    walk preserves the denotation on every input, with NO per-site fixed-point
    hypothesis (the thing the conditioned pipeline could not do). -/
theorem twoRotates_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 64]) :
    (rorWalk twoRotates).denote V = twoRotates.denote V :=
  rorWalk_denote twoRotates V

/-- **Both sites fire to native `rorImm`.** The walked program is the doubly-native
    image: `rorImm 64 8` over `rorImm 64 24` over `ret`. Both selections fire by
    `rorWalk_fires` (each `8 < 64`, `24 < 64`), exhibiting the multi-site selection the
    conditioned pass could not express in one uniform pass. -/
theorem twoRotates_selected :
    rorWalk twoRotates
      = mkRorOp 64 8 .here
          (mkRorOp 64 24 (.there (.there .here)) (.ret .here)) := by
  -- outer rotate fires (8 < 64); its body is the inner rotate subtree, which `rorWalk`
  -- then fires on (24 < 64); the innermost body is `ret`, a `rorWalk` fixed point.
  rw [twoRotates, rorWalk_fires 64 8 (by decide),
      rorWalk_fires 64 24 (by decide), rorWalk_ret]

/-! ## 6. Operand-soundness preserved: the non-canonical `or` is NOT walked

The refactored walker is operand-sound by construction (`RorSite.horig`): the
`IselPipelineRec.rorCex` defect (an `or` combining `lo ||| lo`, not `hi ||| lo`) is
not recognized, so `rorWalk` is the identity there and the denotation is preserved —
no miscompile survives the refactor either. -/

/-- The non-canonical witness (same shape as `RorImmSelect.rorCex`): an `or` combining
    `lo ||| lo`. -/
def rorCex : Com jasminDialect [.reg 8] (.reg 8) :=
  .var (.mk (.shrImm 8 1) rfl (.cons .here .nil))
    (.var (.mk (.shlImm 8 1) rfl (.cons (.there .here) .nil))
      (.var (.mk (.regArith .or 8) rfl (.cons .here (.cons .here .nil)))
        (.ret .here)))

/-- **`rorWalk` does NOT fire on the non-canonical `or`** — by `rfl`, the recognizer
    declines (its operand check fails), so `rorWalk` is the identity on `rorCex`. The
    refactored pass is operand-sound, exactly as the landed matcher. -/
theorem rorWalk_rorCex_not_fired : rorWalk rorCex = rorCex := by
  -- The recognizer declines at the top (`or` is `lo ||| lo`, not `hi ||| lo`), so the
  -- walk descends; each deeper level also fails to recognize (too short), down to `ret`.
  rw [show rorCex = Com.var _ _ from rfl, rorWalk_var_none _ _ (by rfl)]
  rw [rorWalk_var_none _ _ (by rfl)]
  rw [rorWalk_var_none _ _ (by rfl)]
  rw [rorWalk_ret]

/-- Denotation preserved on the former counterexample (corollary of the unconditional
    theorem — no special-casing needed). -/
theorem rorWalk_rorCex_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 8]) :
    (rorWalk rorCex).denote V = rorCex.denote V :=
  rorWalk_denote rorCex V

end CatCrypt.Crypto.SecureCompilation.Dialects.IselPipelineGeneral
