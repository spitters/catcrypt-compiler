/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass

/-!
# D3 — the `rorImm` peephole: a subtree-collapsing ISel pass on `Com jasminDialect`

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`ArithIselPass.lean` builds the denotation-preserving ISel *framework* on the
cleanest **same-shape** case (commutative operand canonicalization), and its
docstring §"What needs a multi-op rewrite" flags the next deliverable:

> **ROR** (`rorImm_eq_shiftOr`): the rotate emulation `(a >>> n) ||| (a <<< (w-n))`
> is a three-op `shr; shl; or` subtree collapsing to one `rorImm` — node-count
> change.

This file delivers exactly that peephole as a `Com jasminDialect → Com jasminDialect`
pass. It opens the ISel-as-a-pass line: the first *real native-op selection*
that **matches an emulation subtree and rewrites it to the native op**, with a
machine-checked denotation-preservation proof.

## The emulation subtree it matches

On `Com jasminDialect` the SHA-2 Σ/σ and Keccak ρ rotate idiom is the three-binding
chain (reading `src` from context `Γ`):

    let hi  = shrImm w n   src;          -- ctx Γ            → reg w :: Γ
    let lo  = shlImm w (w-n) src;        -- ctx reg w :: Γ   → reg w :: reg w :: Γ
    let out = regArith .or [hi, lo];     -- out = hi ||| lo  → reg w :: reg w :: reg w :: Γ
    <body>

`Sha2RotateSelect`/`KeccakRotateSelect` hand-apply this exact selection at the
**value** level on the bespoke emit substrate (`Env`/`BState`); this pass
generalizes it to a structural `Com`-level rewrite that any producer's output can
be run through.

## The rewrite (same-context-shape, no de-Bruijn re-threading)

The native `rorImm` is a *single* op, so the naïve rewrite would drop the context
from `reg w :: reg w :: reg w :: Γ` to `reg w :: Γ` and force re-threading every
de-Bruijn index in `<body>`. We avoid that: the pass keeps the first two bindings
(`hi`, `lo`) in place — they become dead, the next pass's DCE removes them — and
rewrites **only the third op** from `regArith .or [hi, lo]` to `rorImm w n [src]`,
reading the original `src` (reachable at the `or` binding as `.there (.there src)`).
The output context is therefore *unchanged* (`reg w :: reg w :: reg w :: Γ`), so
`<body>` needs no adaptation. The value bound at `<body>`'s de-Bruijn 0 changes
from `(src >>> n) ||| (src <<< (w-n))` to `src.rotateRight n` — equal by
`ArithIselSoundness.rorImm_eq_shiftOr` for an in-range `n < w`. That is the whole
soundness content.

## Coverage (honest)

The collapse is licensed only for an **in-range immediate** `n < w` (every SHA-512
Σ/σ and Keccak ρ rotate is in range). The pass carries that as the `n < w` conjunct
of `rorImmSelect`'s match guard, and the theorems as the `hlt : n < w` hypothesis of
`rorImmSelect_fires` / `rorImmSelect_denote`, rather than firing on an out-of-range `n`
(where
`rotateRight` and the shift-or form differ) — the same discipline as
`MLIR/VectorDialect/LoweringAVX512.lean`, whose `lowerAVX512` returns `none`
outside its supported op fragment. On a matched, in-range subtree the pass
rewrites to `rorImm` and the denotation is preserved (`rorImmSelect_denote`, the
headline). On every non-matching or out-of-range shape the pass is the identity
(so it is total and never changes a denotation it cannot prove equal).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness

/-! ## 1. The canonical rotate emulation subtree (the match target)

We give the three-binding `shr; shl; or` emulation a named smart constructor so
the matcher has a precise shape to recognize and the soundness has a precise term
to rewrite. `mkRotrSubtree w n src body` is the subtree above; `mkRorOp w n src body`
is its single-`rorImm` image with the **same output context** (the two dead
`shr`/`shl` bindings are kept so `body`'s de-Bruijn indices are unchanged). -/

/-- The canonical `shr; shl; or` rotate-right emulation subtree over `Com
    jasminDialect`, reading `src : Var Γ (.reg w)`, binding `out = (src >>> n) |||
    (src <<< (w-n))` at de-Bruijn 0, then continuing with `body`. -/
def mkRotrSubtree {Γ : Ctxt jasminDialect} {s : JasminTy} (w n : Nat)
    (src : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    Com jasminDialect Γ s :=
  -- hi := src >>> n
  .var (.mk (.shrImm w n) rfl (.cons src .nil))
    -- lo := src <<< (w - n);  src = .there .here
    (.var (.mk (.shlImm w (w - n)) rfl (.cons (.there src) .nil))
      -- out := hi ||| lo;  hi = .there .here, lo = .here
      (.var (.mk (.regArith .or w) rfl (.cons (.there .here) (.cons .here .nil)))
        body))

/-- The native single-`rorImm` image of `mkRotrSubtree`, with the **same** output
    context: the two emulation bindings (`shr`, `shl`) are kept as dead carriers so
    `body`'s de-Bruijn indices are unchanged; only the third op is the native
    `rorImm w n src`. The selected op reads the original `src`, which at the third
    binding is `.there (.there src)`. -/
def mkRorOp {Γ : Ctxt jasminDialect} {s : JasminTy} (w n : Nat)
    (src : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    Com jasminDialect Γ s :=
  -- hi := src >>> n   (dead, kept for context-shape parity)
  .var (.mk (.shrImm w n) rfl (.cons src .nil))
    -- lo := src <<< (w - n)   (dead)
    (.var (.mk (.shlImm w (w - n)) rfl (.cons (.there src) .nil))
      -- out := rorImm w n src;  src here is .there (.there src)
      (.var (.mk (.rorImm w n) rfl (.cons (.there (.there src)) .nil))
        body))

/-! ## 2. Value-level equality: the two subtrees denote equally (for `n < w`)

This is the whole soundness content, reduced to the `BitVec` identity
`rorImm_eq_shiftOr`. -/

/-- **Subtree denotation agreement.** For an in-range immediate `n < w`,
    `mkRorOp` (native `rorImm`) and `mkRotrSubtree` (the `shr; shl; or` emulation)
    denote the **same value** on every valuation: the bound `out` changes from the
    shift-or form to `rotateRight n`, equal by `rorImm_eq_shiftOr`, and the kept
    `hi`/`lo` carriers plus `body` are identical. -/
theorem mkRorOp_denote {Γ : Ctxt jasminDialect} {s : JasminTy} (w n : Nat)
    (hlt : n < w) (src : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s)
    (V : Ctxt.Valuation Γ) :
    (mkRorOp w n src body).denote V = (mkRotrSubtree w n src body).denote V := by
  -- Both `Com`s run `body` on a 3-extended valuation; the `hi := src >>> n` and
  -- `lo := src <<< (w-n)` carriers are identical, and only the head (`out`)
  -- differs: `rorImm`'s `rotateRight n` vs `or`'s `(src >>> n) ||| (src <<< (w-n))`.
  -- State that body equality over a generic `a : BitVec w` (so the shift/rotate
  -- notation lands on `BitVec`), close it by `rorImm_eq_shiftOr`, then instantiate
  -- at `a := src.lookup V`; the `Com.denote` reduction to the 3-extended form is
  -- definitional.
  have h : ∀ a : BitVec w,
      body.denote
          (.cons (a.rotateRight n) (.cons (a <<< (w - n)) (.cons (a >>> n) V)))
        = body.denote
          (.cons ((a >>> n) ||| (a <<< (w - n)))
            (.cons (a <<< (w - n)) (.cons (a >>> n) V))) := by
    intro a
    rw [rorImm_eq_shiftOr w n hlt]
  exact h (src.lookup V)

/-! ## 3. The peephole pass `rorImmSelect`

A total `Com jasminDialect → Com jasminDialect` that walks the program and, at any
binding whose next three ops are the canonical rotate emulation `shrImm w n;
shlImm w (w-n); regArith .or w`, rewrites the third op to the native `rorImm w n`,
leaving the two now-dead shift carriers in place (so `body`'s de-Bruijn indices are
unchanged — no re-threading). Every non-matching or out-of-range shape passes
through; the recursion descends into the continuation. Mirrors
`ArithIselPass.iselCom`'s structural-recursion skeleton, extended from a same-shape
`Expr` swap to this subtree collapse.

**Operand-soundness (the matcher checks the *full* canonical subtree).** It is not
enough to key the fire on the three op *tags* and rewrite the `or` to
`rorImm w n [src]` regardless of what the `or` actually combined — that miscompiles
any `shr; shl; or` whose `or` is not the canonical `hi ||| lo` over a single shared
`src` (see `IselPipelineRec.rorCex`). The recognizer therefore pins, in addition to
the op tags and the widths/`n < w` guard:

* the `shl` source is the **same** `src` the `shr` reads, one binder deeper
  (`shlSrc = .there src`), and the `shl` amount is exactly `w - n`;
* the `or` combines **exactly** the two immediately preceding bindings —
  `hi = .there .here` (the `shr` result) and `lo = .here` (the `shl` result).

With those pinned, firing implies the matched subtree is literally
`mkRotrSubtree w n src body`, so the rewrite to `mkRorOp` is denotation-preserving
by `mkRorOp_denote` with **no operand side condition** — the local fire-site is
operand-unconditional. `Ctxt.Var` has no `DecidableEq` instance, so we supply the
structural `varDecEq` below to decide the `Var`-equality operand checks (this lives
in the pass file, touching no shared substrate).

The `n < w` guard is the honest fragment condition: out of range, `rotateRight`
and the shift-or form differ, so the pass declines to fire (cf.
`MLIR/VectorDialect/LoweringAVX512.lean`, whose `lowerAVX512` likewise returns
`none` outside its supported op fragment). -/

/-- Structural decidable equality for intrinsically-typed De Bruijn variables.
    `Ctxt.Var` is an inductive (`here`/`there`) but carries no derived
    `DecidableEq`; the matcher needs to decide operand identity, so we provide it
    here without modifying the shared `Core.lean` substrate. -/
def varDecEq {d : Dialect} : {Γ : Ctxt d} → {t : d.Ty} →
    (a b : Ctxt.Var Γ t) → Decidable (a = b)
  | _, _, .here, .here => isTrue rfl
  | _, _, .there a, .there b =>
      match varDecEq a b with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro hh; cases hh; exact h rfl)
  | _, _, .here, .there _ => isFalse (by intro h; cases h)
  | _, _, .there _, .here => isFalse (by intro h; cases h)

/-- Boolean operand-equality used in the recognizer guards. We route through the
    explicit `varDecEq` (rather than a `Decidable` instance) so the guard never
    leaves an unresolved instance metavariable under the dependent `▸` casts. -/
def varBeq {d : Dialect} {Γ : Ctxt d} {t : d.Ty} (a b : Ctxt.Var Γ t) : Bool :=
  decide (a = b) (h := varDecEq a b)

/-- `varBeq` is reflexive — used to discharge the recognizer's operand guards on a
    canonical subtree. -/
theorem varBeq_self {d : Dialect} {Γ : Ctxt d} {t : d.Ty} (a : Ctxt.Var Γ t) :
    varBeq a a = true := by simp [varBeq]

/-- The `rorImm` peephole. Fires on the canonical `shr; shl; or` rotate subtree
    with equal widths, `n < w`, the `shl` reading the same `src` by `w - n`, and the
    `or` combining exactly the `shr`/`shl` results — collapsing the `or` op to a
    native `rorImm`; identity elsewhere. Total and structurally recursive. -/
def rorImmSelect {Γ : Ctxt jasminDialect} {s : JasminTy} :
    Com jasminDialect Γ s → Com jasminDialect Γ s
  | .var (t := JasminTy.reg w) e1
      (.var (t := JasminTy.reg w2) e2
        (.var (t := JasminTy.reg w3) e3 body)) =>
      match e1.op, e1.args, e2.op, e2.args, e3.op, e3.args with
      | .shrImm we n, .cons src .nil, .shlImm wsh m, .cons shlSrc .nil,
          .regArith JasminBinOp.or wor, .cons orHi (.cons orLo .nil) =>
          if hcond : we = w ∧ w2 = w ∧ w3 = w ∧ n < w ∧ wsh = w ∧ wor = w2 ∧ m = w - n then
            -- widths agree and `n < w`; pin the operands canonical.
            let src' : Ctxt.Var Γ (.reg w) := hcond.1 ▸ src
            let shlSrcW : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w) :=
              hcond.2.2.2.2.1 ▸ shlSrc
            let orHiW : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w) :=
              (hcond.2.2.2.2.2.1.trans hcond.2.1) ▸ orHi
            let orLoW : Ctxt.Var (JasminTy.reg w2 :: JasminTy.reg w :: Γ) (JasminTy.reg w2) :=
              hcond.2.2.2.2.2.1 ▸ orLo
            if varBeq shlSrcW (Ctxt.Var.there src')
                && varBeq orHiW (Ctxt.Var.there Ctxt.Var.here)
                && varBeq orLoW Ctxt.Var.here then
              -- the full canonical rotate subtree: collapse to native `rorImm`.
              let newE3 : Expr jasminDialect (.reg w2 :: .reg w :: Γ) (.reg w3) :=
                { op := .rorImm w n
                  retTy_eq := hcond.2.2.1 ▸ rfl
                  args := .cons (.there (.there src')) .nil }
              .var e1 (.var e2 (.var newE3 (rorImmSelect body)))
            else .var e1 (.var e2 (.var e3 (rorImmSelect body)))
          else .var e1 (.var e2 (.var e3 (rorImmSelect body)))
      | _, _, _, _, _, _ => .var e1 (.var e2 (.var e3 (rorImmSelect body)))
  | .var e body => .var e (rorImmSelect body)
  | .ret v => .ret v

/-- **The pass fires on the canonical rotate subtree.** For an in-range immediate
    `n < w`, `rorImmSelect` rewrites `mkRotrSubtree` (the `shr; shl; or` emulation)
    to `mkRorOp` (the native `rorImm`), recursing into the body. This is the
    statement that the pass *subsumes* the hand-done `Sha2/KeccakRotateSelect`
    rotate selection: those modules pick `rorImm` for one rotate site; this pass
    picks it for every canonical rotate subtree in a `Com`. -/
theorem rorImmSelect_fires {Γ : Ctxt jasminDialect} {s : JasminTy} (w n : Nat)
    (hlt : n < w) (src : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s) :
    rorImmSelect (mkRotrSubtree w n src body) = mkRorOp w n src (rorImmSelect body) := by
  show (if _ : w = w ∧ w = w ∧ w = w ∧ n < w ∧ w = w ∧ w = w ∧ (w - n) = w - n
        then _ else _) = _
  rw [dif_pos ⟨rfl, rfl, rfl, hlt, rfl, rfl, rfl⟩]
  simp only [varBeq_self, Bool.and_self, if_true]
  rfl

/-- The pass is the identity on a bare `ret`. -/
theorem rorImmSelect_ret {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    rorImmSelect (Com.ret v) = Com.ret v := rfl

/-! ## 4. Headline: denotation preservation on the matched fragment -/

/-- **`rorImmSelect` is denotation-preserving on the rotate subtree.** For an
    in-range immediate `n < w` and a body that the pass leaves fixed
    (`hbody : rorImmSelect body = body` — e.g. a `ret`, or any body with no further
    rotate subtree), running the pass on the canonical `shr; shl; or` rotate
    emulation computes the **same value** as the emulation on every input: the
    fired native `rorImm` denotes equally by `mkRorOp_denote`. So this first
    native-op ISel selection is a perf-only transform, never correctness-critical.

    The `n < w` and `hbody` hypotheses scope the theorem to the supported fragment
    (an in-range rotate with a pass-fixed body); out of range the pass declines to
    fire, and on a body it would re-transform the preservation chains through the
    body's own `rorImmSelect` equation. -/
theorem rorImmSelect_denote {Γ : Ctxt jasminDialect} (w n : Nat) (hlt : n < w)
    (src : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) (.reg w))
    (hbody : rorImmSelect body = body)
    (V : Ctxt.Valuation Γ) :
    (rorImmSelect (mkRotrSubtree w n src body)).denote V
      = (mkRotrSubtree w n src body).denote V := by
  rw [rorImmSelect_fires w n hlt, hbody, mkRorOp_denote w n hlt]

/-! ## 5. Worked example

A self-contained rotate-right-by-8 at width 64 (a SHA-512 `Σ`/Keccak `ρ` amount),
over `[reg 64]` with the trivial body `ret out`. We exhibit that the pass produces
the `rorImm` op (the worked program equals `mkRorOp …` by `rfl`) and that the
denotation is preserved on every input — proving the pass subsumes the hand-done
rotate selection on a concrete program. -/

/-- Worked source: the canonical `shr; shl; or` rotate-by-8 subtree over `[reg 64]`,
    body `ret out`. -/
def exampleRotr : Com jasminDialect [.reg 64] (.reg 64) :=
  mkRotrSubtree 64 8 .here (.ret .here)

/-- Its native image: the same program with the `or` collapsed to `rorImm 64 8`. -/
def exampleRor : Com jasminDialect [.reg 64] (.reg 64) :=
  mkRorOp 64 8 .here (.ret .here)

/-- **The pass produces the `rorImm` op on the worked example** — by `rfl`, the
    transformed program is exactly the native `rorImm` form. -/
example : rorImmSelect exampleRotr = exampleRor := rfl

/-- **Denotation preserved on the worked example**, on every input valuation. The
    `64 - 8 = 56`-bit shift-or rotate and the native `rorImm 64 8` compute the same
    value. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 64]) :
    (rorImmSelect exampleRotr).denote V = exampleRotr.denote V :=
  rorImmSelect_denote 64 8 (by decide) .here (.ret .here) rfl V

/-! ## 6. Operand-soundness regression: the non-canonical `or` is NOT rewritten

The defect the tightened matcher closes: a `shrImm 8 1; shlImm 8 1; regArith .or 8`
chain (op tags + widths + `1 < 8` all match) whose `or` combines `lo ||| lo`
(`.here, .here`) instead of the canonical `hi ||| lo`. The old tag-only matcher fired
and rewrote it to `rorImm 8 1 [src]`, changing the value (source `2`, pass `128`).
The tightened matcher checks the `or`'s operands, so it does **not** fire — the chain
passes through as the identity and the denotation is trivially preserved. -/

/-- The witness program: a `shr; shl; or` chain whose `or` is `lo ||| lo`, **not**
    the canonical `hi ||| lo`. (Same term as `IselPipelineRec.rorCex`.) -/
def rorCex : Com jasminDialect [.reg 8] (.reg 8) :=
  .var (.mk (.shrImm 8 1) rfl (.cons .here .nil))
    (.var (.mk (.shlImm 8 1) rfl (.cons (.there .here) .nil))
      (.var (.mk (.regArith .or 8) rfl (.cons .here (.cons .here .nil)))
        (.ret .here)))

/-- **The tightened matcher does NOT fire on the non-canonical `or`.** The pass is
    the identity on `rorCex` — by `rfl`, the operand check (`orHi = .there .here`)
    fails on the `lo ||| lo` `or`, so no `rorImm` is selected. This is the closed
    counterexample: the old matcher miscompiled `rorCex`; the new one cannot. -/
theorem rorImmSelect_rorCex_not_fired : rorImmSelect rorCex = rorCex := rfl

/-- **Denotation preserved on the former counterexample**, on every input — a direct
    corollary of the pass being the identity there (no miscompile survives). -/
theorem rorImmSelect_rorCex_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 8]) :
    (rorImmSelect rorCex).denote V = rorCex.denote V := by
  rw [rorImmSelect_rorCex_not_fired]

end CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
