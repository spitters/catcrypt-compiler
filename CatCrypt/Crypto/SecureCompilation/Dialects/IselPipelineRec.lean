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
# D3 — ISel operand-soundness: the former miscompiles are closed (a regression record)

This file pins down the **operand-soundness** of the ISel matchers. An earlier
version of `rorImmSelect` / `andnSelect` keyed its fire decision on the op *tags*
only and under-checked the operands, so it miscompiled non-canonical inputs. Those
matchers are now **tightened** (`RorImmSelect.lean` / `AndnSelect.lean` §3) to require
the full canonical subtree, and this file records the machine-checked regression: on
the two former counterexamples the tightened passes do **not** fire, so they pass
through as the identity and the denotation is preserved.

## What was wrong, and what fixes it

The old `rorImmSelect` keyed on `e1.op, e1.args, e2.op, e3.op` and rewrote the `or` to
`rorImm w n [src]` (value `src.rotateRight n`) *regardless* of what the `or` actually
combined — it did not constrain the `shl`'s source/amount or the `or`'s two operands.
So a `shrImm; shlImm; regArith .or` chain at matching widths whose `or` is, say,
`lo ||| lo` was miscompiled. The old `andnSelect` was the same shape: it did not check
the `regConst` was `allOnes` nor the `xor`/`and` second operands, so a `regConst 0`
chain (where the `xor` is the identity, `b ^^^ 0 = b`) was miscompiled.

The tightened matchers now pin the **full** canonical subtree (see the
operand-soundness notes in the two pass files): firing implies the matched subtree is
literally `mkRotrSubtree` / `mkAndnotSubtree`, so the local fire-site is
operand-unconditional (`mkRorOp_denote` / `mkAndnOp_denote` apply with no operand side
condition). The regression theorems below witness that the formerly-miscompiled
`rorCex` / `andnCex` now pass through unchanged.

## On the unconditional `∀ c` form

The fully-general `∀ c V, (rorImmSelect c).denote V = c.denote V` by structural
induction stays mechanically blocked: the passes nest an op-**constructor** `match`
inside a three-binding `Com` match, which defeats Lean's equation-lemma /
functional-induction generation (the catch-all `.var` arm overlaps the three-binding
arm, so the descent is not `rfl` on an abstract body without WHNF). The pipeline
soundness therefore stays the conditioned `IselPipeline.iselPipeline_denote_of`
(re-exported in §3) — but it is now conditioned on a body fixed-point only, **not** on
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

/-- The formerly-miscompiled program: a `shrImm 8 1; shlImm 8 1; regArith .or 8` chain
    (op tags + widths + `1 < 8` all match) whose `or` combines `lo` with `lo`
    (de-Bruijn `[.here, .here]`) — **not** the canonical `hi ||| lo`. The old
    tag-only matcher fired and rewrote it to `rorImm 8 1 [src]`, changing the value
    (source `2`, pass `128`); the tightened matcher checks the `or`'s operands. -/
def rorCex : Com jasminDialect [.reg 8] (.reg 8) :=
  .var (.mk (.shrImm 8 1) rfl (.cons .here .nil))
    (.var (.mk (.shlImm 8 1) rfl (.cons (.there .here) .nil))
      (.var (.mk (.regArith .or 8) rfl (.cons .here (.cons .here .nil)))
        (.ret .here)))

/-- The input the old miscompile diverged on: `src = 1 : BitVec 8`. -/
def rorCexV : Ctxt.Valuation (d := jasminDialect) [.reg 8] := .cons (1 : BitVec 8) .nil

/-- **The tightened `rorImmSelect` does NOT fire on `rorCex`.** By `rfl`: the operand
    guard (`orHi = .there .here`) fails on the `lo ||| lo` `or`, so the pass is the
    identity here — no `rorImm` is selected. This is the closed counterexample. -/
theorem rorImmSelect_rorCex_not_fired : rorImmSelect rorCex = rorCex := rfl

/-- **`rorImmSelect` preserves `rorCex`'s denotation** (it is the identity there), on
    every input — in particular on the input the old miscompile diverged on. The
    former `rorImmSelect_not_denote_preserving` is therefore no longer derivable: the
    matcher does not fire on a non-canonical `or`. -/
theorem rorImmSelect_rorCex_denote_preserved (V : Ctxt.Valuation (d := jasminDialect) [.reg 8]) :
    (rorImmSelect rorCex).denote V = rorCex.denote V := by
  rw [rorImmSelect_rorCex_not_fired]

/-! ## 2. `andnSelect` does NOT fire on the non-`allOnes` mask (regression) -/

/-- The formerly-miscompiled program: a `regConst 8 _; xor 8; and 8` chain (op tags +
    widths match) whose `regConst` is `0` rather than `allOnes`, so the `xor`
    materialises `b ^^^ 0 = b`, not `~~~ b`. The old matcher fired and rewrote the
    `and` to `andn b a = (~~~ b) &&& a`, changing the value (source `5`, pass `0` on
    `a = 3, b = 5`); the tightened matcher checks the `regConst` value. -/
def andnCex : Com jasminDialect [.reg 8, .reg 8] (.reg 8) :=
  .var (.mk (.regConst 8 0) rfl .nil)
    (.var (.mk (.regArith .xor 8) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
      (.var (.mk (.regArith .and 8) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
        (.ret .here)))

/-- The input the old miscompile diverged on: `a = 3`, `b = 5 : BitVec 8`. -/
def andnCexV : Ctxt.Valuation (d := jasminDialect) [.reg 8, .reg 8] :=
  .cons (3 : BitVec 8) (.cons (5 : BitVec 8) .nil)

/-- **The tightened `andnSelect` does NOT fire on `andnCex`.** By `rfl`: the
    `cval = 2^w - 1` guard fails on the `regConst 0`, so the pass is the identity
    here — no `andn` is selected. This is the closed counterexample. -/
theorem andnSelect_andnCex_not_fired : andnSelect andnCex = andnCex := rfl

/-- **`andnSelect` preserves `andnCex`'s denotation** (it is the identity there), on
    every input. The former `andnSelect_not_denote_preserving` is therefore no longer
    derivable: the matcher does not fire on a non-`allOnes` mask. -/
theorem andnSelect_andnCex_denote_preserved
    (V : Ctxt.Valuation (d := jasminDialect) [.reg 8, .reg 8]) :
    (andnSelect andnCex).denote V = andnCex.denote V := by
  rw [andnSelect_andnCex_not_fired]

/-! ## 3. The pipeline, honestly: conditioned preservation (re-export)

The matchers are now operand-sound (§1–§2: no miscompile counterexample survives), but
the fully-general `∀ c` preservation stays mechanically blocked on the descent (see the
module docstring). So the pipeline soundness is the landed
`IselPipeline.iselPipeline_denote_of`, conditioned on the per-pass body fixed points
only: on any program where `rorImmSelect` preserves `c`'s denotation and `andnSelect`
preserves `(rorImmSelect c)`'s denotation, the composite preserves `c`'s. Those two
hypotheses are discharged on a canonical site by `rorImmSelect_denote` /
`andnSelect_denote` (the worked `IselPipeline.iselPipeline_exampleBoth_denote`). The
conditioning is on the descent, not on operand canonicity at a fired site — a fired
site is always canonical now. -/

/-- **Pipeline preservation, conditioned on the per-pass body fixed points.** Identical
    to `IselPipeline.iselPipeline_denote_of`; surfaced here as the honest pipeline
    result. The matcher is operand-sound (§1–§2), so the conditioning is on the
    recursive descent only — no miscompile counterexample survives. -/
theorem iselPipeline_denote_conditioned {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Com jasminDialect Γ s) (V : Ctxt.Valuation Γ)
    (hror : (rorImmSelect c).denote V = c.denote V)
    (handn : (andnSelect (rorImmSelect c)).denote V = (rorImmSelect c).denote V) :
    (iselPipeline c).denote V = c.denote V :=
  iselPipeline_denote_of c V hror handn

end CatCrypt.Crypto.SecureCompilation.Dialects.IselPipelineRec
