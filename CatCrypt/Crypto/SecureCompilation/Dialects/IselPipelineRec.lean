/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.IselPipeline

/-!
# ISel operand-soundness: regression checks on non-canonical inputs

This module pins down the **operand-soundness** of the ISel matchers.
`rorImmSelect` / `andnSelect` (`RorImmSelect.lean` / `AndnSelect.lean` §3) require
the full canonical subtree, and this module checks two non-canonical programs on
which a matcher keyed on the op *tags* alone would miscompile: the passes do **not**
fire on them, so they pass through as the identity and the denotation is preserved.

## The two non-canonical inputs

A `rorImmSelect` keyed on `e1.op, e1.args, e2.op, e3.op` alone would rewrite the `or`
to `rorImm w n [src]` (value `src.rotateRight n`) *regardless* of what the `or`
combines, since it would not constrain the `shl`'s source/amount or the `or`'s two
operands. A `shrImm; shlImm; regArith .or` chain at matching widths whose `or` is,
say, `lo ||| lo` would then be miscompiled. An `andnSelect` of the same shape, not
checking that the `regConst` is `allOnes` nor the `xor`/`and` second operands, would
miscompile a `regConst 0` chain (where the `xor` is the identity, `b ^^^ 0 = b`).

The matchers pin the **full** canonical subtree (see the
operand-soundness notes in the two pass files): firing implies the matched subtree is
literally `mkRotrSubtree` / `mkAndnotSubtree`, so the local fire-site is
operand-unconditional (`mkRorOp_denote` / `mkAndnOp_denote` apply with no operand side
condition). The regression theorems below witness that `rorCex` / `andnCex` pass
through unchanged.

## On the unconditional `∀ c` form

The fully-general `∀ c V, (rorImmSelect c).denote V = c.denote V` by structural
induction stays mechanically blocked: the passes nest an op-**constructor** `match`
inside a three-binding `Com` match, which defeats Lean's equation-lemma /
functional-induction generation (the catch-all `.var` arm overlaps the three-binding
arm, so the descent is not `rfl` on an abstract body without WHNF). The pipeline
soundness therefore stays the conditioned `IselPipeline.iselPipeline_denote_of`
(re-exported in §3), conditioned on a body fixed-point only, **not** on
any operand canonicity at the fire site, because the matcher is operand-sound. Crucially,
**no miscompile counterexample survives** (§1–§2): the conditioning is on the descent,
not on correctness of a fired site.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.IselPipelineRec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.IselPipeline

/-! ## 1. `rorImmSelect` does NOT fire on the non-canonical `or` (regression) -/

/-- A non-canonical program: a `shrImm 8 1; shlImm 8 1; regArith .or 8` chain
    (op tags + widths + `1 < 8` all match) whose `or` combines `lo` with `lo`
    (de-Bruijn `[.here, .here]`) — **not** the canonical `hi ||| lo`. A tag-only
    matcher would rewrite it to `rorImm 8 1 [src]`, changing the value
    (source `2`, pass `128`); `rorImmSelect` checks the `or`'s operands. -/
def rorCex : Com jasminDialect [.reg 8] (.reg 8) :=
  .var (.mk (.shrImm 8 1) rfl (.cons .here .nil))
    (.var (.mk (.shlImm 8 1) rfl (.cons (.there .here) .nil))
      (.var (.mk (.regArith .or 8) rfl (.cons .here (.cons .here .nil)))
        (.ret .here)))

/-- The input on which a tag-only rewrite of `rorCex` diverges: `src = 1 : BitVec 8`. -/
def rorCexV : Ctxt.Valuation (d := jasminDialect) [.reg 8] := .cons (1 : BitVec 8) .nil

/-- **`rorImmSelect` does NOT fire on `rorCex`.** By `rfl`: the operand
    guard (`orHi = .there .here`) fails on the `lo ||| lo` `or`, so the pass is the
    identity here — no `rorImm` is selected. -/
theorem rorImmSelect_rorCex_not_fired : rorImmSelect rorCex = rorCex := rfl

/-- **`rorImmSelect` preserves `rorCex`'s denotation** (it is the identity there), on
    every input — in particular on `rorCexV`: the matcher does not fire on a
    non-canonical `or`. -/
theorem rorImmSelect_rorCex_denote_preserved (V : Ctxt.Valuation (d := jasminDialect) [.reg 8]) :
    (rorImmSelect rorCex).denote V = rorCex.denote V := by
  rw [rorImmSelect_rorCex_not_fired]

/-! ## 2. `andnSelect` does NOT fire on the non-`allOnes` mask (regression) -/

/-- A non-canonical program: a `regConst 8 _; xor 8; and 8` chain (op tags +
    widths match) whose `regConst` is `0` rather than `allOnes`, so the `xor`
    materialises `b ^^^ 0 = b`, not `~~~ b`. A tag-only matcher would rewrite the
    `and` to `andn b a = (~~~ b) &&& a`, changing the value (source `5`, pass `0` on
    `a = 3, b = 5`); `andnSelect` checks the `regConst` value. -/
def andnCex : Com jasminDialect [.reg 8, .reg 8] (.reg 8) :=
  .var (.mk (.regConst 8 0) rfl .nil)
    (.var (.mk (.regArith .xor 8) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
      (.var (.mk (.regArith .and 8) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
        (.ret .here)))

/-- The input on which a tag-only rewrite of `andnCex` diverges: `a = 3`, `b = 5`. -/
def andnCexV : Ctxt.Valuation (d := jasminDialect) [.reg 8, .reg 8] :=
  .cons (3 : BitVec 8) (.cons (5 : BitVec 8) .nil)

/-- **`andnSelect` does NOT fire on `andnCex`.** By `rfl`: the
    `cval = 2^w - 1` guard fails on the `regConst 0`, so the pass is the identity
    here — no `andn` is selected. -/
theorem andnSelect_andnCex_not_fired : andnSelect andnCex = andnCex := rfl

/-- **`andnSelect` preserves `andnCex`'s denotation** (it is the identity there), on
    every input: the matcher does not fire on a non-`allOnes` mask. -/
theorem andnSelect_andnCex_denote_preserved
    (V : Ctxt.Valuation (d := jasminDialect) [.reg 8, .reg 8]) :
    (andnSelect andnCex).denote V = andnCex.denote V := by
  rw [andnSelect_andnCex_not_fired]

/-! ## 3. The pipeline: conditioned preservation (re-export)

The matchers are operand-sound (§1–§2), and the fully-general `∀ c` preservation is
mechanically blocked on the descent (see the module docstring). So the pipeline
soundness is `IselPipeline.iselPipeline_denote_of`, conditioned on the per-pass body fixed points
only: on any program where `rorImmSelect` preserves `c`'s denotation and `andnSelect`
preserves `(rorImmSelect c)`'s denotation, the composite preserves `c`'s. Those two
hypotheses are discharged on a canonical site by `rorImmSelect_denote` /
`andnSelect_denote` (the worked `IselPipeline.iselPipeline_exampleBoth_denote`). The
conditioning is on the descent, not on operand canonicity at a fired site — a fired
site is always canonical. -/

/-- **Pipeline preservation, conditioned on the per-pass body fixed points.** Identical
    to `IselPipeline.iselPipeline_denote_of`; surfaced here as the pipeline
    result. The matcher is operand-sound (§1–§2), so the conditioning is on the
    recursive descent only — no miscompile counterexample survives. -/
theorem iselPipeline_denote_conditioned {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) (V : Ctxt.Valuation Γ)
    (hror : (rorImmSelect c).denote V = c.denote V)
    (handn : (andnSelect (rorImmSelect c)).denote V = (rorImmSelect c).denote V) :
    (iselPipeline c).denote V = c.denote V :=
  iselPipeline_denote_of c V hror handn

end CatCrypt.Crypto.SecureCompilation.Dialects.IselPipelineRec
