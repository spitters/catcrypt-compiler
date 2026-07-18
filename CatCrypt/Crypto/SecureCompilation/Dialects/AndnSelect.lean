/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass

/-!
# D3 — the `andn` peephole: a subtree-collapsing ISel pass on `Com jasminDialect`

This is keystone #1's **second** native-op selection (after `RorImmSelect.lean`'s
`rorImm`): the BMI1 `ANDN dst, a, b ⇒ dst := (~a) & b` instruction, which collapses
the and-not idiom `a &&& (~~~ b)` from a `NOT; AND` pair to a single op. It is the
exact shape `Sha2/KeccakChiSelect` hand-applies at the value level for the Keccak χ
step `B[x] ^^^ ((¬B[x+1]) ∧ B[x+2])`; this pass generalizes it to a structural
`Com`-level rewrite.

## The emulation subtree it matches

On `Com jasminDialect` the and-not idiom is the three-binding chain (reading
`a : Var Γ (.reg w)` and `b : Var Γ (.reg w)` from context `Γ`):

    let mask = regConst w (2^w-1)         -- allOnes               → reg w :: Γ
    let nb   = regArith .xor a' b';       -- nb = b ^^^ allOnes = ~~~ b
    let out  = regArith .and a'' nb;      -- out = a &&& nb = a &&& (~~~ b)
    <body>

(The materialised `~~~ b` is the standard `b ^^^ allOnes` form; the live data inputs
are `a` and `b`, the `mask` / `nb` are intermediate carriers.)

## The rewrite (same-context-shape, no de-Bruijn re-threading)

The native `andn` is a *single* `regArith .andn` op, so — exactly as `RorImmSelect`
keeps the two dead `shr`/`shl` carriers — this pass keeps the `mask`/`nb` bindings
in place (they become dead, the next pass's DCE removes them) and rewrites **only
the third op** from `regArith .and [a, nb]` to `regArith .andn [b, a]` (the operand
**transpose** ANDN needs: ANDN complements its *first* source, so to compute
`a &&& (~~~ b)` we feed `b` first and `a` second). The original `a`, `b` are
reachable at the `and` binding two binders deep. The output context is unchanged,
so `<body>` needs no adaptation. The bound `out` changes from
`a &&& (b ^^^ allOnes)` to `(~~~ b) &&& a`, equal by
`ArithIselSoundness.andn_eq_andnot`. That is the whole soundness content — a 2→1
collapse plus an operand transpose.

## Coverage (honest)

The collapse is **unconditional** at the value level (`andn_eq_andnot` holds for all
`a, b`, no in-range guard — unlike ROR's `n < w`). The only fragment condition is
the structural one the headline carries: the body must be a pass fixed point
(`hbody`), exactly as in `RorImmSelect_denote`. On a matched subtree the pass
rewrites to `andn` and the denotation is preserved; on every non-matching shape it
is the identity.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness

/-! ## 1. The canonical and-not emulation subtree (the match target) -/

/-- The canonical `const; xor; and` and-not emulation subtree over `Com
    jasminDialect`, reading `a b : Var Γ (.reg w)`, binding
    `out = a &&& (b ^^^ allOnes) = a &&& (~~~ b)` at de-Bruijn 0, then `body`. -/
def mkAndnotSubtree {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (a b : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    Com jasminDialect Γ s :=
  -- mask := allOnes                                  ctx Γ → reg w :: Γ
  .var (.mk (.regConst w (2 ^ w - 1)) rfl .nil)
    -- nb := b ^^^ mask;  b = .there b, mask = .here   → reg w :: reg w :: Γ
    (.var (.mk (.regArith .xor w) rfl (.cons (.there b) (.cons .here .nil)))
      -- out := a &&& nb;  a = .there (.there a), nb = .here
      (.var (.mk (.regArith .and w) rfl (.cons (.there (.there a)) (.cons .here .nil)))
        body))

/-- The native single-`andn` image of `mkAndnotSubtree`, with the **same** output
    context: the `mask`/`nb` carriers are kept dead so `body`'s de-Bruijn indices
    are unchanged; only the third op is the native `andn`, reading `b` then `a`
    (the ANDN operand transpose, since `andn` complements its first source). At the
    third binding `a`/`b` are two binders deep. -/
def mkAndnOp {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (a b : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    Com jasminDialect Γ s :=
  -- mask := allOnes   (dead, kept for context-shape parity)
  .var (.mk (.regConst w (2 ^ w - 1)) rfl .nil)
    -- nb := b ^^^ mask   (dead)
    (.var (.mk (.regArith .xor w) rfl (.cons (.there b) (.cons .here .nil)))
      -- out := andn b a = (~~~ b) &&& a;  b = .there (.there b), a = .there (.there a)
      (.var (.mk (.regArith .andn w) rfl
          (.cons (.there (.there b)) (.cons (.there (.there a)) .nil)))
        body))

/-! ## 2. Value-level keystone: the two subtrees denote equally (unconditional) -/

/-- **Subtree denotation agreement.** `mkAndnOp` (native `andn b a`) and
    `mkAndnotSubtree` (the `const; xor; and` emulation) denote the **same value** on
    every valuation: the bound `out` changes from `a &&& (b ^^^ allOnes)` to
    `(~~~ b) &&& a`, equal by `andn_eq_andnot` after rewriting `b ^^^ allOnes` to
    `~~~ b`; the `mask`/`nb` carriers and `body` are identical. -/
theorem mkAndnOp_denote {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (a b : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s)
    (V : Ctxt.Valuation Γ) :
    (mkAndnOp w a b body).denote V = (mkAndnotSubtree w a b body).denote V := by
  -- Both run `body` on a 3-extended valuation; only the head `out` differs:
  -- `andn`'s `(~~~ B) &&& A` vs `and`'s `A &&& (B ^^^ allOnes)`. State the body
  -- equality over generic `A B : BitVec w` so the notation lands on `BitVec`,
  -- close by `andn_eq_andnot` (and `ofNat_allOnes`/`xor_allOnes`), then instantiate.
  have h : ∀ A B : BitVec w,
      body.denote
          (.cons (JasminBinOp.andn.apply B A)
            (.cons (B ^^^ BitVec.ofNat w (2 ^ w - 1)) (.cons (BitVec.ofNat w (2 ^ w - 1)) V)))
        = body.denote
          (.cons (A &&& (B ^^^ BitVec.ofNat w (2 ^ w - 1)))
            (.cons (B ^^^ BitVec.ofNat w (2 ^ w - 1)) (.cons (BitVec.ofNat w (2 ^ w - 1)) V))) := by
    intro A B
    rw [andn_eq_andnot]
    rw [ArithEmulations.ofNat_allOnes, BitVec.xor_allOnes]
  exact h (a.lookup V) (b.lookup V)

/-! ## 3. The peephole pass `andnSelect`

Total `Com jasminDialect → Com jasminDialect` that, at any binding whose next three
ops are the canonical and-not emulation `regConst w (2^w-1); regArith .xor w;
regArith .and w` (with matching widths), rewrites the third op to the native
`regArith .andn w` with the operands transposed (ANDN's first source is the one
complemented). The two now-dead carriers stay in place (no de-Bruijn re-threading).
Every non-matching shape passes through; the recursion descends into the
continuation. Mirrors `RorImmSelect.rorImmSelect`'s structural skeleton.

**Operand-soundness (the matcher checks the *full* canonical subtree).** Keying the
fire on the three op *tags* alone and rewriting the `and` to `andn bRaw aDeep`
miscompiles any `const; xor; and` chain that is not the canonical and-not: e.g. a
`regConst 0` makes the `xor` the identity (`b ^^^ 0 = b`, not `~~~ b`), yet the native
`andn` still computes `(~~~ b) &&& a` — a different value (see
`IselPipelineRec.andnCex`). The recognizer therefore pins, in addition to the op
tags and the width guards:

* the `regConst` value is exactly `allOnes = 2^w - 1` (so the `xor` materialises
  `~~~ b`);
* the `xor`'s second operand is the constant just bound (`mask = .here`) and its
  first operand is a context input `.there b` — recovering the live `b`;
* the `and`'s second operand is the `xor` result (`nb = .here`) and its first
  operand is a context input `.there (.there a)` — recovering the live `a`.

With those pinned, firing implies the matched subtree is literally
`mkAndnotSubtree w a b body`, so the rewrite to `mkAndnOp` (native `andn b a`, the
ANDN operand transpose) is denotation-preserving by `mkAndnOp_denote` with **no
operand side condition**. As in `RorImmSelect`, `Ctxt.Var` carries no `DecidableEq`,
so we supply the structural `varDecEq`/`varBeq` below for the operand checks. -/

/-- Structural decidable equality for De Bruijn variables (see
    `RorImmSelect.varDecEq`; redeclared locally to avoid a cross-pass import). -/
def varDecEq {d : Dialect} : {Γ : Ctxt d} → {t : d.Ty} →
    (a b : Ctxt.Var Γ t) → Decidable (a = b)
  | _, _, .here, .here => isTrue rfl
  | _, _, .there a, .there b =>
      match varDecEq a b with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro hh; cases hh; exact h rfl)
  | _, _, .here, .there _ => isFalse (by intro h; cases h)
  | _, _, .there _, .here => isFalse (by intro h; cases h)

/-- Boolean operand-equality for the recognizer guards (routed through `varDecEq`
    so no `Decidable` instance metavariable is left under the dependent casts). -/
def varBeq {d : Dialect} {Γ : Ctxt d} {t : d.Ty} (a b : Ctxt.Var Γ t) : Bool :=
  decide (a = b) (h := varDecEq a b)

/-- `varBeq` is reflexive — discharges the operand guards on a canonical subtree. -/
theorem varBeq_self {d : Dialect} {Γ : Ctxt d} {t : d.Ty} (a : Ctxt.Var Γ t) :
    varBeq a a = true := by simp [varBeq]

/-- The `andn` peephole. Fires on the canonical `const; xor; and` and-not subtree
    with equal widths, the `regConst` being `allOnes`, and the `xor`/`and` second
    operands being the mask / materialised `~~~ b` — collapsing the `and` op to a
    native `andn` (operands transposed); identity elsewhere. Total and structurally
    recursive. -/
def andnSelect {Γ : Ctxt jasminDialect} {s : JasminTy} :
    Com jasminDialect Γ s → Com jasminDialect Γ s
  | .var (t := JasminTy.reg w) e1
      (.var (t := JasminTy.reg w2) e2
        (.var (t := JasminTy.reg w3) e3 body)) =>
      match e1.op, e2.op, e2.args, e3.op, e3.args with
      | .regConst _ cval, .regArith JasminBinOp.xor wx, .cons (.there bRaw) (.cons xMask .nil),
          .regArith JasminBinOp.and wa, .cons (.there (.there aRaw)) (.cons aNb .nil) =>
          if hcond : w2 = w ∧ w3 = w ∧ wx = w ∧ wa = w ∧ cval = 2 ^ w - 1 then
            -- recover the live `b` (from the `xor`'s `.there b`) and `a` (from the
            -- `and`'s `.there (.there a)`); the `regConst` is `allOnes` by `hcond`.
            let bV : Ctxt.Var Γ (.reg w) := hcond.2.2.1 ▸ bRaw
            let aV : Ctxt.Var Γ (.reg w) := hcond.2.2.2.1 ▸ aRaw
            -- the `xor` mask operand must be the just-bound const (`.here`) ...
            let xMaskW : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w) := hcond.2.2.1 ▸ xMask
            -- ... and the `and`'s second operand must be the `xor` result (`.here`).
            let aNbW : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w2) :=
              (hcond.2.2.2.1.trans hcond.1.symm) ▸ aNb
            if varBeq xMaskW Ctxt.Var.here && varBeq aNbW Ctxt.Var.here then
              -- full canonical and-not: collapse the `and` to native `andn b a`
              -- (`(~~~ b) &&& a`), reading `b`, `a` two binders deep, transposed.
              let bThere : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w3) :=
                hcond.2.1.symm ▸ (Ctxt.Var.there (Ctxt.Var.there bV))
              let aThere : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w3) :=
                hcond.2.1.symm ▸ (Ctxt.Var.there (Ctxt.Var.there aV))
              let newE3 : Expr jasminDialect (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w3) :=
                { op := .regArith .andn w3
                  retTy_eq := rfl
                  args := .cons bThere (.cons aThere .nil) }
              .var e1 (.var e2 (.var newE3 (andnSelect body)))
            else .var e1 (.var e2 (.var e3 (andnSelect body)))
          else .var e1 (.var e2 (.var e3 (andnSelect body)))
      | _, _, _, _, _ => .var e1 (.var e2 (.var e3 (andnSelect body)))
  | .var e body => .var e (andnSelect body)
  | .ret v => .ret v

/-- **The pass fires on the canonical and-not subtree.** `andnSelect` rewrites
    `mkAndnotSubtree` (the `const; xor; and` emulation) to `mkAndnOp` (the native
    `andn`), recursing into the body. This is the statement that the pass subsumes
    the hand-done Keccak-χ `andn` selection. -/
theorem andnSelect_fires {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (a b : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    andnSelect (mkAndnotSubtree w a b body) = mkAndnOp w a b (andnSelect body) := by
  show (if _ : w = w ∧ w = w ∧ w = w ∧ w = w ∧ (2 ^ w - 1) = 2 ^ w - 1 then _ else _) = _
  rw [dif_pos ⟨rfl, rfl, rfl, rfl, rfl⟩]
  simp only [varBeq_self, Bool.and_self, if_true]
  rfl

/-- The pass is the identity on a bare `ret`. -/
theorem andnSelect_ret {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    andnSelect (Com.ret v) = Com.ret v := rfl

/-! ## 4. Headline: denotation preservation on the matched fragment -/

/-- **`andnSelect` is denotation-preserving on the and-not subtree.** For a body the
    pass leaves fixed (`hbody : andnSelect body = body`), running the pass on the
    canonical `const; xor; and` and-not emulation computes the **same value** as the
    emulation on every input: the fired native `andn` denotes equally by
    `mkAndnOp_denote` (no in-range guard — the ANDN collapse is unconditional). So
    this native-op ISel selection is a perf-only transform. -/
theorem andnSelect_denote {Γ : Ctxt jasminDialect} (w : Nat)
    (a b : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) (.reg w))
    (hbody : andnSelect body = body)
    (V : Ctxt.Valuation Γ) :
    (andnSelect (mkAndnotSubtree w a b body)).denote V
      = (mkAndnotSubtree w a b body).denote V := by
  rw [andnSelect_fires w a b, hbody, mkAndnOp_denote w]

/-! ## 5. Worked example

A self-contained and-not at width 64 over `[reg 64, reg 64]` with the trivial body
`ret out`. We exhibit that the pass produces the `andn` op (the worked program
equals `mkAndnOp …` by `rfl`) and that the denotation is preserved on every input. -/

/-- Worked source: the canonical `const; xor; and` and-not subtree over
    `[reg 64, reg 64]`, body `ret out`, computing `a &&& (~~~ b)` for inputs
    `a = .here`, `b = .there .here`. -/
def exampleAndnot : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  mkAndnotSubtree 64 .here (.there .here) (.ret .here)

/-- Its native image: the same program with the `and` collapsed to native `andn`. -/
def exampleAndn : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  mkAndnOp 64 .here (.there .here) (.ret .here)

/-- **The pass produces the `andn` op on the worked example** — by `rfl`, the
    transformed program is exactly the native `andn` form. -/
example : andnSelect exampleAndnot = exampleAndn := rfl

/-- **Denotation preserved on the worked example**, on every input valuation. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 64, .reg 64]) :
    (andnSelect exampleAndnot).denote V = exampleAndnot.denote V :=
  andnSelect_denote 64 .here (.there .here) (.ret .here) rfl V

/-! ## 6. Operand-soundness regression: a non-`allOnes` mask is NOT rewritten

The defect the tightened matcher closes: a `regConst 8 _; regArith .xor 8;
regArith .and 8` chain (op tags + widths match) whose `regConst` is `0`, so the `xor`
materialises `b ^^^ 0 = b` rather than `~~~ b`. The old tag-only matcher fired and
rewrote the `and` to `andn b a = (~~~ b) &&& a`, changing the value (source `5`,
pass `0` on `a = 3, b = 5`). The tightened matcher checks the `regConst` value, so it
does **not** fire — the chain passes through and the denotation is preserved. -/

/-- The witness program: a `const; xor; and` chain with `regConst 0` (not `allOnes`).
    (Same term as `IselPipelineRec.andnCex`.) -/
def andnCex : Com jasminDialect [.reg 8, .reg 8] (.reg 8) :=
  .var (.mk (.regConst 8 0) rfl .nil)
    (.var (.mk (.regArith .xor 8) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
      (.var (.mk (.regArith .and 8) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
        (.ret .here)))

/-- **The tightened matcher does NOT fire on the non-`allOnes` mask.** The pass is
    the identity on `andnCex` — by `rfl`, the `cval = 2^w - 1` guard fails on the
    `regConst 0`, so no `andn` is selected. This is the closed counterexample: the
    old matcher miscompiled `andnCex`; the new one cannot. -/
theorem andnSelect_andnCex_not_fired : andnSelect andnCex = andnCex := rfl

/-- **Denotation preserved on the former counterexample**, on every input — a direct
    corollary of the pass being the identity there (no miscompile survives). -/
theorem andnSelect_andnCex_denote
    (V : Ctxt.Valuation (d := jasminDialect) [.reg 8, .reg 8]) :
    (andnSelect andnCex).denote V = andnCex.denote V := by
  rw [andnSelect_andnCex_not_fired]

end CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect
