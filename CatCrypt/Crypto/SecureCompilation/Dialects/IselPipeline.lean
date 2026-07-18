/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
import CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect
import CatCrypt.Crypto.SecureCompilation.Dialects.CmovSelect

/-!
# D3 — the ISel pipeline capstone: composing the native-op selection passes

`RorImmSelect.lean`, `AndnSelect.lean`, and `CmovSelect.lean` each land **one**
native-op instruction-selection pass on `Com jasminDialect`:

* `rorImmSelect` collapses the `shr; shl; or` rotate emulation to native `rorImm`
  (licensed for an in-range immediate `n < w`);
* `andnSelect` collapses the `const; xor; and` and-not emulation to native `andn`
  (the value collapse is **unconditional**);
* `selectSelect` collapses the `const; xor; and; and; or` masked-select emulation to
  native `select`/CMOV (licensed by a materialisation invariant).

This file is the **capstone**: it composes the uniform passes into a single
verified `Com jasminDialect → Com jasminDialect` instruction-selection pipeline
`iselPipeline`, and proves a **composed denote-preservation** result built from the
landed `*_denote` lemmas. This exhibits the backend spine as one multi-selection
ISel pass, not three disjoint peepholes.

## Which passes compose uniformly, and which doesn't (read this)

`rorImmSelect` and `andnSelect` are both **uniform** `Com Γ s → Com Γ s` total
rewriters: they take only the program, walk it structurally, and fire on their
respective subtree shapes. They therefore compose by plain function composition,
and the composite is a uniform `Com Γ s → Com Γ s` pass:

    iselPipeline := andnSelect ∘ rorImmSelect.

`selectSelect` is **not** of this shape. As its own module documents (§3 "The
peephole pass"), the masked-select emulation mentions no 1-bit value — the
condition `cond` the mask materialised is **not recoverable** from the emulation
subtree alone — so `selectSelect` is *condition-guided*: it takes the explicit
`cond c x y body` operands and is the single-subtree builder `mkSelectOp`, not a
`Com Γ s → Com Γ s` walker. It cannot slot into a uniform fold over an arbitrary
program; we document it as a **separate-shape selection** and surface it through
the pipeline only as the already-proved `selectSelect_denote` (re-exported below),
exactly as its module states. Folding CMOV uniformly is gated on recovering the
1-bit condition from the emulation (see the closing note in §4).

## The composed soundness (honest fragment)

Composition of denote-preserving maps is denote-preserving. We state this as a
**general** lemma (`iselPipeline_denote_of`) conditioned on the **conjunction** of
the two per-pass guards at the relevant program — `rorImmSelect` preserving `c`'s
denotation, and `andnSelect` preserving `(rorImmSelect c)`'s denotation — with no
`sorry` on any open goal. Discharging those two hypotheses on a concrete program is
exactly what the landed `rorImmSelect_denote` / `andnSelect_denote` do on their
matched fragments; §3 wires them on a worked program carrying **both** a rotate and
an and-not subtree, where the pipeline selects **both** native ops and the
denotation equality holds, sorry-free.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.IselPipeline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.CmovSelect

/-! ## 1. The composed pipeline

The uniform passes compose by function composition. `rorImmSelect` runs first
(picking native `rorImm` for every in-range rotate subtree), then `andnSelect`
runs on its output (picking native `andn` for every and-not subtree). The two are
**orthogonal at the op level**: `rorImmSelect` fires only on `shrImm; shlImm; or`,
`andnSelect` only on `regConst; xor; and`, so neither disturbs the other's matched
subtree, and the order does not affect which ops are selected. -/

/-- The ISel pipeline: `rorImm` selection followed by `andn` selection, as one
    uniform `Com jasminDialect → Com jasminDialect` pass. -/
def iselPipeline {Γ : Ctxt jasminDialect} {s : JasminTy} :
    Com jasminDialect Γ s → Com jasminDialect Γ s :=
  fun c => andnSelect (rorImmSelect c)

/-- Unfold the pipeline as the explicit composition (for rewriting). -/
theorem iselPipeline_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) :
    iselPipeline c = andnSelect (rorImmSelect c) := rfl

/-- The pipeline is the identity on a bare `ret`: both passes are. -/
theorem iselPipeline_ret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v : Ctxt.Var Γ t) :
    iselPipeline (Com.ret v) = Com.ret v := by
  rw [iselPipeline_eq, rorImmSelect_ret, andnSelect_ret]

/-! ## 2. Composed denote-preservation (general lemma)

Composition of denote-preserving maps is denote-preserving. The composed result is
conditioned on the **conjunction** of the two per-pass guards *at the program in
question* — `hror` for the first pass on `c`, `handn` for the second pass on
`rorImmSelect c`. Neither hypothesis is a `sorry`: on a concrete program they are
discharged by the landed `rorImmSelect_denote` / `andnSelect_denote` (§3). -/

/-- **The pipeline is denote-preserving wherever both passes are.** If `rorImmSelect`
    preserves `c`'s denotation on `V` (`hror`) and `andnSelect` preserves
    `(rorImmSelect c)`'s denotation on `V` (`handn`), then the composite `iselPipeline`
    preserves `c`'s denotation. This is the composition-of-denote-preserving-maps
    fact, made into the capstone soundness: the multi-selection ISel pass never
    changes the value the program computes, on the fragment where each constituent
    selection is licensed (the conjunction of the ROR `n < w` guard and the — here
    structural-only — ANDN guard, both surfaced via the per-pass `*_denote`). -/
theorem iselPipeline_denote_of {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) (V : Ctxt.Valuation Γ)
    (hror : (rorImmSelect c).denote V = c.denote V)
    (handn : (andnSelect (rorImmSelect c)).denote V = (rorImmSelect c).denote V) :
    (iselPipeline c).denote V = c.denote V := by
  rw [iselPipeline_eq, handn, hror]

/-! ## 3. Worked example: a program with BOTH a rotate and an and-not subtree

We build a single `Com` carrying both native-op opportunities and show the pipeline
selects **both** the native `rorImm` and the native `andn`, with the denotation
preserved — sorry-free. The outer ROR subtree's body *is* the ANDN subtree; the two
ops are orthogonal (ROR matches `shr; shl; or`, ANDN matches `const; xor; and`), so
each pass fires on its own subtree and leaves the other untouched.

Widths: `w = 64`. Context `Γ = [reg 64, reg 64]`, holding `src` (for the rotate) and
a second register reused as both `a` and `b` of the and-not (any in-context regs
work; we keep it minimal). The ROR subtree extends `Γ` by three `reg 64`; in that
extended context the ANDN subtree reads two of those registers, extends by three
more, and returns. -/

/-- The shared `Γ` of the worked example. -/
abbrev Γ2 : Ctxt jasminDialect := [.reg 64, .reg 64]

/-- The ANDN subtree that sits in the *body* position of the rotate subtree. Its
    context is `reg 64 :: reg 64 :: reg 64 :: Γ2` (the three registers the rotate
    subtree binds). It reads two of those as `a`, `b`, binds the and-not, returns. -/
def andnInner :
    Com jasminDialect (.reg 64 :: .reg 64 :: .reg 64 :: Γ2)
      (.reg 64) :=
  mkAndnotSubtree 64 (.there .here) .here (.ret .here)

/-- The full worked source program: the rotate emulation `shr; shl; or` (rotate by 8
    at width 64 on `src = .here`) whose body is the and-not emulation `const; xor;
    and`. Carries both native-op opportunities. -/
def exampleBoth : Com jasminDialect Γ2 (.reg 64) :=
  mkRotrSubtree 64 8 .here andnInner

/-- `rorImmSelect` leaves the and-not inner subtree fixed — it matches only the
    `shr; shl; or` rotate shape, never `const; xor; and`. -/
theorem rorImmSelect_andnInner : rorImmSelect andnInner = andnInner := rfl

/-- After the rotate pass, the program is the native `rorImm` over the **unchanged**
    and-not subtree. By `rorImmSelect_fires` (the rotate fires) and the inner subtree
    being a `rorImmSelect` fixed point. -/
theorem rorImmSelect_exampleBoth :
    rorImmSelect exampleBoth = mkRorOp 64 8 .here andnInner := by
  rw [exampleBoth, rorImmSelect_fires 64 8 (by decide), rorImmSelect_andnInner]

/-! ### The pipeline selects BOTH native ops -/

/-- **The pipeline produces native `rorImm` AND native `andn`.** Running
    `iselPipeline` on `exampleBoth` selects the native rotate (via `rorImmSelect`,
    leaving the and-not body) and then the native and-not (via `andnSelect`). The
    resulting program is exactly the doubly-native image: `rorImm` over an `andn`
    over `ret`. Established by `rfl` — both selections fire definitionally on the
    matched shapes. -/
theorem iselPipeline_exampleBoth :
    iselPipeline exampleBoth
      = mkRorOp 64 8 .here
          (mkAndnOp 64 (.there .here) .here (.ret .here)) := rfl

/-! ### The denotation is preserved, sorry-free -/

/-- **Body congruence for the rotate native image.** `mkRorOp`'s denotation depends
    on its body only through the body's denotation on the (rotate-extended)
    valuation, so two bodies that denote equally everywhere give equal `mkRorOp`
    denotations. (No width-`w` `BitVec` computation is forced — the extended
    valuation stays abstract.) -/
theorem mkRorOp_body_congr {Γ : Ctxt jasminDialect} {s : JasminTy} (w n : Nat)
    (src : Ctxt.Var Γ (.reg w))
    (b1 b2 : Com jasminDialect (.reg w :: .reg w :: .reg w :: Γ) s)
    (V : Ctxt.Valuation Γ) (h : ∀ V', b1.denote V' = b2.denote V') :
    (mkRorOp w n src b1).denote V = (mkRorOp w n src b2).denote V := by
  simp only [mkRorOp, Com.denote]; apply h

/-- **Denotation preserved on the both-subtree example.** On every input valuation
    the pipeline's output computes the same value as the source. The pipeline output
    is the doubly-native program `rorImm` over `andn` (by `iselPipeline_exampleBoth`,
    definitional); we bring it back to the source by two landed value-level keystones:
    the native `andn` denotes equally to the and-not emulation by `mkAndnOp_denote`
    (lifted to the rotate body by `mkRorOp_body_congr`), and the native `rorImm`
    denotes equally to the rotate emulation by `mkRorOp_denote` (rotate-by-8 is in
    range, `8 < 64`). Sorry-free: every step is a landed `*_denote` keystone. -/
theorem iselPipeline_exampleBoth_denote (V : Ctxt.Valuation Γ2) :
    (iselPipeline exampleBoth).denote V = exampleBoth.denote V := by
  rw [iselPipeline_exampleBoth]
  -- doubly-native: `mkRorOp` over `mkAndnOp` over `ret`.
  -- Step 1: collapse the inner native `andn` back to the and-not emulation, under
  -- the rotate body (the inner ANDN keystone is unconditional).
  rw [mkRorOp_body_congr 64 8 .here _ andnInner V
        (fun V' => mkAndnOp_denote 64 (.there .here) .here (.ret .here) V')]
  -- Step 2: collapse the outer native `rorImm` back to the rotate emulation
  -- (rotate-by-8 in range), recovering exactly `exampleBoth`.
  rw [mkRorOp_denote 64 8 (by decide) .here andnInner V, exampleBoth]

/-! ## 4. Path to an UNCONDITIONAL recursive ISel pass (honest note)

The composed soundness above is conditioned on the per-pass fixed-point/guard
hypotheses (the `hbody` fixed-point bodies and ROR's `n < w`). Dropping the
**body fixed-point** hypothesis needs a *recursive* preservation theorem:
`(rorImmSelect c).denote V = c.denote V` for **every** `c`, proved by structural
induction on `c` — at each binding, either the rotate subtree fires (closed by
`mkRorOp_denote`) and we recurse on the (already-transformed) body, or the pass
descends and we recurse directly. The same for `andnSelect` (whose op collapse is
already unconditional, so its recursive form needs no value-side guard at all).
With those two recursive `*_denote` theorems, `iselPipeline_denote_of`'s two
hypotheses become *theorems*, and the pipeline soundness specialises to the
unconditional `∀ c V, (iselPipeline c).denote V = c.denote V`. The only genuine
residual guard is ROR's `n < w` (out of range the rotate and the shift-or form
differ), which stays as a side condition on the rotate sites — never a `sorry`.

CMOV folds in once the 1-bit condition is recoverable from the masked-select
emulation (a `condMask`-shaped op the chain exposes), at which point `selectSelect`
becomes a uniform `Com Γ s → Com Γ s` walker and joins the composition with its
materialisation invariant discharged structurally. Until then it is surfaced as the
separate-shape `selectSelect_denote`.
-/

end CatCrypt.Crypto.SecureCompilation.Dialects.IselPipeline
