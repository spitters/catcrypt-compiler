/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.IselPipelineGeneral
public import CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect

/-!
# D3 — the GENERAL ISel pass: ROR + ANDN, both UNCONDITIONAL

This file completes the general (`#1`) instruction-selection pass. It mirrors the
ROR refactor in `IselPipelineGeneral.lean` for the BMI1 ANDN op, then **composes**
the two unconditional native-op selectors into one general `Com → Com` pass with a
single unconditional `∀ c V, (iselGeneral c).denote V = c.denote V`.

## What lands here

* `andnRecognize : Com Γ s → Option (AndnSite c)` — the decidable recognizer for the
  canonical `const; xor; and` and-not subtree, carrying the operand-soundness
  certificate `horig : mkAndnotSubtree w a b deepBody = c`. The nested op-`match`
  (and the `▸` operand-cast bookkeeping) is isolated **here**, inside a function
  returning a plain `Option` — exactly as `rorRecognize`.
* `andnWalk : Com Γ s → Com Γ s` — the clean structurally-recursive walker
  (`.ret`/`.var e body` only), so Lean generates `andnWalk.eq_def` / `andnWalk.induct`.
* `andnWalk_denote : ∀ c V, (andnWalk c).denote V = c.denote V` — **UNCONDITIONAL**,
  via the generated `andnWalk.induct`, reusing `AndnSelect.mkAndnOp_denote` (whose
  collapse is unconditional — ANDN has no `n < w` range guard, so this is even
  simpler than ROR: `AndnSite` carries no `hlt` field).
* `iselGeneral := andnWalk ∘ rorWalk` — the composed general pass, with
  `iselGeneral_denote : ∀ c V, (iselGeneral c).denote V = c.denote V` UNCONDITIONAL
  (a trivial chain of the two unconditional preservations — contrast the old
  conditioned `IselPipeline.iselPipeline_denote_of` / `andnSelect_denote`, which both
  carried a per-pass body-fixed-point hypothesis).

## Why this is fully general (no conditions)

The landed `AndnSelect.andnSelect_denote` is conditioned on `hbody : andnSelect body
= body` (a body fixed point), exactly as `RorImmSelect`'s was. The refactor isolates
the op-match in the `Option`-returning recognizer, so the `Com` recursion in
`andnWalk` is the clean two-arm `.ret`/`.var e body` split, Lean generates the
`.induct` principle, and structural induction pushes the preservation through the
descent with **no** body hypothesis. The ANDN value collapse (`mkAndnOp_denote`) is
unconditional, so unlike ROR there is not even a width-range side condition to thread.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.IselGeneralAndn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.IselPipelineGeneral
open CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness

/-! ## 1. The recognizer result: a matched canonical and-not site -/

/-- A recognized canonical and-not subtree at the head of some `c : Com Γ s`: the
    width `w`, the two live source variables `a b : Var Γ (.reg w)`, the continuation
    `deepBody` after the three bindings, **and** a proof that `c` is literally
    `mkAndnotSubtree w a b deepBody`. The equality field is the operand-soundness
    certificate: a recognized site is always the canonical `const; xor; and` and-not
    emulation, so the rewrite to `mkAndnOp` is value-preserving with no side condition
    (the ANDN collapse is *unconditional* — there is no `n < w` analogue here), and
    `deepBody`'s `sizeOf` decrease (for the walker's termination) follows from it. -/
structure AndnSite {Γ : Ctxt jasminDialect} {s : JasminTy} (c : Com jasminDialect Γ s) where
  w : Nat
  a : Ctxt.Var Γ (.reg w)
  b : Ctxt.Var Γ (.reg w)
  deepBody : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s
  horig : mkAndnotSubtree w a b deepBody = c

/-- `AndnSelect.varBeq` reflects equality: a `true` operand guard yields the `Var`
    equality used to certify the recognized subtree is canonical. (Local analogue of
    `IselPipelineGeneral.eq_of_varBeq`, keyed to `AndnSelect.varBeq`/`varDecEq`.) -/
theorem eq_of_varBeq {d : Dialect} {Γ : Ctxt d} {t : d.Ty} {a b : Ctxt.Var Γ t}
    (h : AndnSelect.varBeq a b = true) : a = b := by
  have h' : @decide (a = b) (AndnSelect.varDecEq a b) = true := by
    simpa [AndnSelect.varBeq] using h
  exact of_decide_eq_true (inst := AndnSelect.varDecEq a b) h'

/-! ## 2. The recognizer (the nested op-match is isolated HERE, returns `Option`)

`andnRecognize c` does the three-binding lookahead with the **full** canonical
operand check (operand-sound, exactly as `AndnSelect.andnSelect`'s tightened
matcher): the `regConst` is `allOnes = 2^w-1`, the `xor`'s mask operand is the
just-bound const (`.here`) over a context input `.there b`, and the `and`'s second
operand is the `xor` result (`.here`) over a context input `.there (.there a)`. It
returns `Option (AndnSite c)`. The nested dependent op-`match` and the `▸`
operand-cast bookkeeping live entirely inside this function, which returns a plain
`Option` — so the `Com` recursion in `andnWalk` (§3) stays clean and its equation
lemmas generate. -/

/-- Decide whether `c`'s head is the canonical `const; xor; and` and-not emulation
    with matching widths, the `regConst` being `allOnes`, the `xor` reading the live
    `b` against the mask, and the `and` combining `a` with the materialised `~~~ b`.
    On a match, return the site (with the equality certificate); else `none`. -/
def andnRecognize {Γ : Ctxt jasminDialect} {s : JasminTy} :
    (c : Com jasminDialect Γ s) → Option (AndnSite c)
  | .var (t := JasminTy.reg w) (.mk op1 hr1 args1)
      (.var (t := JasminTy.reg w2) (.mk op2 hr2 args2)
        (.var (t := JasminTy.reg w3) (.mk op3 hr3 args3) body)) =>
      match op1, args1, op2, args2, op3, args3 with
      | .regConst we cval, .nil, .regArith JasminBinOp.xor wx, .cons (.there bRaw) (.cons xMask .nil),
          .regArith JasminBinOp.and wa, .cons (.there (.there aRaw)) (.cons aNb .nil) =>
          if hcond : we = w ∧ w2 = w ∧ w3 = w ∧ wx = w ∧ wa = w ∧ cval = 2 ^ w - 1 then
            let bV : Ctxt.Var Γ (.reg w) := hcond.2.2.2.1 ▸ bRaw
            let aV : Ctxt.Var Γ (.reg w) := hcond.2.2.2.2.1 ▸ aRaw
            let xMaskW : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w) := hcond.2.2.2.1 ▸ xMask
            let aNbW : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w2) :=
              (hcond.2.2.2.2.1.trans hcond.2.1.symm) ▸ aNb
            if hop : AndnSelect.varBeq xMaskW Ctxt.Var.here
                && AndnSelect.varBeq aNbW Ctxt.Var.here then
              let deepBody : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s :=
                (by rw [hcond.2.1, hcond.2.2.1] : Com jasminDialect (.reg w3 :: .reg w2 :: .reg w :: Γ) s
                      = Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) ▸ body
              some { w := w, a := aV, b := bV, deepBody := deepBody, horig := by
                       obtain ⟨hwe, hw2, hw3, hwx, hwa, hcv⟩ := hcond
                       subst hwe; subst hw2; subst hw3; subst hwx; subst hwa; subst hcv
                       rw [Bool.and_eq_true] at hop
                       obtain ⟨hm, hn⟩ := hop
                       have q1 : xMask = Ctxt.Var.here := eq_of_varBeq hm
                       have q2 : aNb = Ctxt.Var.here := eq_of_varBeq hn
                       show mkAndnotSubtree _ aRaw bRaw body = _
                       clear hm hn bV aV xMaskW aNbW deepBody
                       subst q1; subst q2
                       rfl }
            else none
          else none
      | _, _, _, _, _, _ => none
  | _ => none

/-! ## 3. The structural walker (clean `.ret`/`.var e body` `Com` recursion)

`andnWalk` is the refactored pass. Its `Com` recursion is the clean two-arm
`.ret v` / `.var e body` split — the op-`match` lives in `andnRecognize`, which
returns a plain `Option`. At each `.var` node, `andnRecognize` decides whether the
head is a canonical and-not subtree; on `some site` we emit the native `mkAndnOp`
over the **recursively-walked** matched body (`site.deepBody`, a strict subterm by
`site.horig`), on `none` we descend into `body`. Because the recursion is clean,
Lean generates the equation lemmas and the `.induct` principle (§4 uses them). -/

/-- The matched body is a strict subterm of `c`, so the walker's recursion on it
    decreases `sizeOf`. Read off `site.horig`. -/
theorem AndnSite.deepBody_lt {Γ : Ctxt jasminDialect} {s : JasminTy}
    {c : Com jasminDialect Γ s} (site : AndnSite c) :
    sizeOf site.deepBody < sizeOf c := by
  have key : sizeOf site.deepBody
      < sizeOf (mkAndnotSubtree site.w site.a site.b site.deepBody) := by
    simp only [mkAndnotSubtree, Com.var.sizeOf_spec]; omega
  rw [site.horig] at key
  exact key

/-- **The refactored ANDN ISel pass.** A clean structurally-recursive walk over
    `Com jasminDialect`: at each `.var` node, fire the native `andn` (via `mkAndnOp`)
    on a recognized canonical and-not subtree, else descend. The op-match is isolated
    in `andnRecognize` (returns `Option`), so the `Com` recursion is clean and the
    equation lemmas generate — enabling the UNCONDITIONAL `∀ c` soundness (§4). -/
def andnWalk {Γ : Ctxt jasminDialect} {s : JasminTy} :
    Com jasminDialect Γ s → Com jasminDialect Γ s
  | .ret v => .ret v
  | .var e body =>
      match andnRecognize (.var e body) with
      | some site => mkAndnOp site.w site.a site.b (andnWalk site.deepBody)
      | none => .var e (andnWalk body)
  termination_by c => sizeOf c
  decreasing_by
    · exact site.deepBody_lt
    · simp_wf; omega

/-- `andnWalk` is the identity on `.ret`. -/
theorem andnWalk_ret {Γ : Ctxt jasminDialect} {s : JasminTy} (v : Ctxt.Var Γ s) :
    andnWalk (.ret v) = .ret v := by
  rw [andnWalk.eq_def]

/-- `andnWalk`'s defining equation on a fired `.var` node: when `andnRecognize` returns
    `some site`, the walk is the native `mkAndnOp` over the walked deep body. -/
theorem andnWalk_var_some {Γ : Ctxt jasminDialect} {s : JasminTy} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s)
    (site : AndnSite (Com.var e body)) (hrec : andnRecognize (.var e body) = some site) :
    andnWalk (.var e body)
      = mkAndnOp site.w site.a site.b (andnWalk site.deepBody) := by
  rw [andnWalk.eq_def]; dsimp only; rw [hrec]

/-- `andnWalk`'s defining equation on a non-fired `.var` node: when `andnRecognize`
    returns `none`, the walk descends into the body. -/
theorem andnWalk_var_none {Γ : Ctxt jasminDialect} {s : JasminTy} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s)
    (hrec : andnRecognize (.var e body) = none) :
    andnWalk (.var e body) = .var e (andnWalk body) := by
  rw [andnWalk.eq_def]; dsimp only; rw [hrec]

/-- **`andnWalk` fires on the canonical and-not subtree** — the analogue of
    `AndnSelect.andnSelect_fires` for the refactored walker. Walking
    `mkAndnotSubtree w a b body` (the `const; xor; and` emulation) yields the native
    `mkAndnOp w a b` over the walked body. The recognizer's width/value/operand
    decisions on the canonical subtree are discharged by `dite_eq_left` / `varBeq_self`. -/
theorem andnWalk_fires {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (a b : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    andnWalk (mkAndnotSubtree w a b body) = mkAndnOp w a b (andnWalk body) := by
  -- the recognizer fires on the canonical subtree, returning a site with parameters
  -- `w, a, b, body` (its `horig` is some proof — irrelevant to the projections).
  have hrec : andnRecognize (mkAndnotSubtree w a b body)
      = some { w := w, a := a, b := b, deepBody := body, horig := rfl } := by
    show (if _ : w = w ∧ w = w ∧ w = w ∧ w = w ∧ w = w ∧ (2 ^ w - 1) = 2 ^ w - 1
          then _ else _) = _
    simp only [and_self, ↓reduceDIte, AndnSelect.varBeq_self, Bool.and_self]; rfl
  rw [show mkAndnotSubtree w a b body
        = Com.var (Expr.mk (JasminOp.regConst w (2 ^ w - 1)) rfl .nil)
            (.var (Expr.mk (JasminOp.regArith .xor w) rfl
                (.cons (.there b) (.cons .here .nil)))
              (.var (Expr.mk (JasminOp.regArith .and w) rfl
                  (.cons (.there (.there a)) (.cons .here .nil)))
                body)) from rfl]
  rw [andnWalk_var_some _ _ _ hrec]

/-! ## 4. The UNCONDITIONAL ANDN soundness theorem (`∀ c`, no body fixed-point hypothesis)

This is the deliverable the conditioned `AndnSelect.andnSelect_denote` (carrying the
`hbody : andnSelect body = body` per-pass body fixed point) could not reach.
Structural induction via the **generated** `andnWalk.induct` (the refactor's payoff)
pushes the preservation through the descent; the fire case is closed by the
value lemma `mkAndnOp_denote` (UNCONDITIONAL — no in-range guard) plus
body-congruence; the descend case by `Com.denote`'s own structure. No fixed-point
hypothesis and no side condition. -/

/-- **Body-congruence for `mkAndnotSubtree`.** Its denotation depends on its body only
    through the body's denotation on the three-extended valuation, so bodies that
    denote equally everywhere give equal `mkAndnotSubtree` denotations. -/
theorem mkAndnotSubtree_body_congr {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (a b : Ctxt.Var Γ (.reg w))
    (b1 b2 : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s)
    (V : Ctxt.Valuation Γ) (h : ∀ V', b1.denote V' = b2.denote V') :
    (mkAndnotSubtree w a b b1).denote V = (mkAndnotSubtree w a b b2).denote V := by
  simp only [mkAndnotSubtree, Com.denote]; apply h

/-- **THE UNCONDITIONAL ANDN ISEL SOUNDNESS.** For **every** program `c` and valuation
    `V`, the refactored ANDN pass `andnWalk` preserves the denotation:
    `(andnWalk c).denote V = c.denote V`. No fixed-point-body hypothesis, no side
    condition (the recognizer is operand-sound via `AndnSite.horig`; the ANDN collapse
    is unconditional).

    Proof: structural induction via the generated `andnWalk.induct`. The fire case
    rewrites `c = mkAndnotSubtree …` (the recognizer certificate `site.horig`),
    collapses the native `mkAndnOp` to the emulation by the value lemma
    `mkAndnOp_denote`, and discharges the walked body by the IH through
    `mkAndnotSubtree_body_congr`. The descend case threads `Com.denote` through
    `body`'s IH. -/
theorem andnWalk_denote {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) (V : Ctxt.Valuation Γ) :
    (andnWalk c).denote V = c.denote V := by
  -- Generalize over the valuation: the fire case runs the body on a 3-extended
  -- valuation, so the IH must hold for *every* `V'`. Induct via the GENERATED
  -- `andnWalk.induct` with the `∀ V` motive.
  refine andnWalk.induct
    (motive := fun Γ c => ∀ V : Ctxt.Valuation Γ, (andnWalk c).denote V = c.denote V)
    ?_ ?_ ?_ Γ c V
  · -- `.ret v`: the walk is the identity.
    intro Γ v V; rw [andnWalk_ret]
  · -- fire: `andnRecognize (.var e body) = some site`, with `site.horig` certifying
    -- `.var e body = mkAndnotSubtree site.w site.a site.b site.deepBody`.
    intro Γ t e body site hrec ih V
    rw [andnWalk_var_some e body site hrec]
    -- bring the source `(Com.var e body).denote V` to the canonical emulation's
    -- denotation via the recognizer certificate (congrArg avoids the dependent-motive
    -- rewrite, since `site`'s type mentions `Com.var e body`).
    rw [← congrArg (fun c => Com.denote c V) site.horig]
    -- collapse native `mkAndnOp` to `mkAndnotSubtree` (unconditional — no guard)
    rw [mkAndnOp_denote site.w]
    -- discharge the walked body against the original body via the IH (∀ V').
    exact mkAndnotSubtree_body_congr site.w site.a site.b _ site.deepBody V ih
  · -- descend: no fire; thread `Com.denote` through the body's IH.
    intro Γ t e body hrec ih V
    rw [andnWalk_var_none e body hrec]
    simp only [Com.denote]
    rw [ih]

/-! ## 5. The COMPOSED general ISel pass: ROR + ANDN, one pass, UNCONDITIONAL

`iselGeneral` runs the ROR selector (`rorWalk`) then the ANDN selector (`andnWalk`)
on the result — one general `Com → Com` instruction-selection pass selecting *both*
native ops. Its denote-preservation is the **trivial chain** of the two unconditional
preservations `andnWalk_denote` and `rorWalk_denote`: NO fixed-point hypothesis, NO
operand or width side condition — contrast the old conditioned forms
(`IselPipeline.iselPipeline_denote_of` and `AndnSelect.andnSelect_denote`, both of
which carried a per-pass body-fixed-point premise). -/

/-- **The composed general ISel pass.** Select ROR native rotates first, then ANDN
    native and-nots on the result. -/
def iselGeneral {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) : Com jasminDialect Γ s :=
  andnWalk (rorWalk c)

/-- **THE UNCONDITIONAL GENERAL ISEL SOUNDNESS.** For **every** program `c` and
    valuation `V`, the composed general pass `iselGeneral = andnWalk ∘ rorWalk`
    preserves the denotation: `(iselGeneral c).denote V = c.denote V`. A trivial chain
    of the two unconditional denote-preservations — no fixed-point/operand/width
    condition whatsoever (contrast the old conditioned `iselPipeline_denote_of`). -/
theorem iselGeneral_denote {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) (V : Ctxt.Valuation Γ) :
    (iselGeneral c).denote V = c.denote V := by
  rw [iselGeneral, andnWalk_denote, rorWalk_denote]

/-! ## 6. Worked example: a body with BOTH a rotate AND an and-not — both selected

The capstone the conditioned pipeline could not express in one uniform pass: a `Com`
with a rotate subtree whose body is an and-not subtree. `iselGeneral` selects the
native `rorImm` AND the native `andn`, and `iselGeneral_denote` (unconditional, no
per-site hypothesis) certifies the denotation is preserved on every input. -/

/-- A rotate-by-8 over `[reg 64, reg 64]` whose body is an and-not of the two register
    inputs (visible after the rotate's three bindings as `.there (.there (.there .here))`
    and the next), returning the and-not result. The outer subtree is the canonical
    `shr; shl; or` rotate emulation; its body is the canonical `const; xor; and`
    and-not emulation. So `iselGeneral` fires ROR on the outer and ANDN on the inner. -/
def rotThenAndn : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  mkRotrSubtree 64 8 .here
    (mkAndnotSubtree 64 (.there (.there (.there .here)))
      (.there (.there (.there (.there .here)))) (.ret .here))

/-- **`iselGeneral` selects BOTH native ops** — by `iselGeneral_denote`, the
    combined walk preserves the denotation on every input, with NO per-site
    fixed-point hypothesis (the thing the conditioned pipeline could not do). -/
theorem rotThenAndn_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 64, .reg 64]) :
    (iselGeneral rotThenAndn).denote V = rotThenAndn.denote V :=
  iselGeneral_denote rotThenAndn V

/-- **Both sites fire to native ops.** The general-walked program is the doubly-native
    image: the native `rorImm 64 8` (from `rorWalk`) over the native `andn 64`
    (from `andnWalk`) over `ret`. The ROR pass fires the outer rotate (8 < 64) and
    leaves the inner and-not subtree as a `rorWalk` fixed point; the ANDN pass then
    fires the inner and-not and is the identity on the now-native outer `rorImm`. -/
theorem rotThenAndn_selected :
    iselGeneral rotThenAndn
      = mkRorOp 64 8 .here
          (mkAndnOp 64 (.there (.there (.there .here)))
            (.there (.there (.there (.there .here)))) (.ret .here)) := by
  rw [iselGeneral]
  -- ROR fires the outer rotate; its body (the and-not subtree) is a rorWalk fixed point.
  rw [rotThenAndn, rorWalk_fires 64 8 (by decide)]
  rw [show rorWalk (mkAndnotSubtree 64 (.there (.there (.there .here)))
            (.there (.there (.there (.there .here)))) (.ret .here))
        = mkAndnotSubtree 64 (.there (.there (.there .here)))
            (.there (.there (.there (.there .here)))) (.ret .here) from by
        rw [mkAndnotSubtree]
        rw [rorWalk_var_none _ _ (by rfl)]
        rw [rorWalk_var_none _ _ (by rfl)]
        rw [rorWalk_var_none _ _ (by rfl)]
        rw [rorWalk_ret]]
  -- ANDN walks the native rorImm subtree: the rorImm bindings are not an and-not, so
  -- ANDN descends to the inner and-not subtree and fires there. Unfold `mkRorOp` on
  -- BOTH sides (`simp only`), descend through its three bindings, fire ANDN on the
  -- inner and-not, then `andnWalk_ret`; the residual is `rfl`.
  simp only [mkRorOp]
  rw [andnWalk_var_none _ _ (by rfl)]
  rw [andnWalk_var_none _ _ (by rfl)]
  rw [andnWalk_var_none _ _ (by rfl)]
  rw [andnWalk_fires 64, andnWalk_ret]

end CatCrypt.Crypto.SecureCompilation.Dialects.IselGeneralAndn
