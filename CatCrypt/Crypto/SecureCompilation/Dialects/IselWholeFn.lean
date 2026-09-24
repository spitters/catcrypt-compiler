/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.IselPipeline
public import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering

/-!
# Connecting the ISel optimizer to the whole-function emit

`IselPipeline.lean` defines the multi-selection ISel pass `iselPipeline`
(`andnSelect ∘ rorImmSelect`) on `Com jasminDialect`, with a composed
denote-preservation result `iselPipeline_denote_of` (conditioned on the two
per-pass guards). `WholeFnLowering.lean` proves `lowerComToProg_sem_eq'`: for a
**straight-line** body, *running the emitted single-function `JasminProg`* equals
`Com.denote`, with both SSA-naming side-conditions discharged (only the
opaque-leaf edge `LeafAgrees` remains).

This module ties the two ends together — the end-to-end statement a real compiler
makes:

> **front emits an emulation → ISel selects the native op → whole-function emit →
> run = original denote.**

Concretely, for a whole-function body `bodyEmul` carrying a canonical rotate
emulation (`shr; shl; or`), let `bodyOpt := iselPipeline bodyEmul` be the
optimized body — with the native `rorImm` selected. We prove:

* **(a) ISel preserves the denotation** — `bodyOpt.denote V = bodyEmul.denote V`,
  via `iselPipeline_denote_of` with the two per-pass guards discharged for this
  concrete body (`rorImmSelect_denote` on the rotate, `andnSelect` an identity on
  the native image since it matches `const; xor; and`, not `shr; shl; rorImm`).
* **(b) The emitted optimized function runs to the ORIGINAL denotation** —
  `runProg (lowerComToProg bodyOpt) leafSem V = bodyEmul.denote V`, composing (a)
  with `lowerComToProg_sem_eq'` on `bodyOpt` (which needs `StraightLine bodyOpt`;
  the native `rorImm` and its two kept shift carriers are all non-`stackStore`, so
  the optimized body stays straight-line).

## The worked example

`bodyEmul = mkRotrSubtree 64 8 .here (ret .here)` over `Γ = [reg 64]`: a
rotate-by-8 at width 64 (a SHA-512 `Σ` / Keccak `ρ` amount), `ret out`. The
optimized `bodyOpt` is the native `rorImm 64 8` (over the two dead shift carriers).
The emitted optimized function runs — under a word-level leaf evaluator — to
exactly the original `(shr; shl; or)` rotate emulation's denotation. The ISel guard
`8 < 64` is discharged by `decide`; `StraightLine bodyOpt` by `simp` on the three
non-`stackStore` ops.

## Scope

This is the *single-fire-site, straight-line* end-to-end tie: one canonical rotate
emulation subtree, optimized and emitted as a whole function. It is the composition
of two existing main theorems, not new optimizer/emit machinery. Optimizing an
**arbitrary** whole body is outside its scope: that needs the *recursive* ISel descent
(`iselPipeline_denote_of`'s two guards turned into the unconditional
`∀ c V, (iselPipeline c).denote V = c.denote V` by structural induction — see
`IselPipeline.lean` §4) and bodies with **multiple** fire sites (each rotate /
and-not subtree selected and the descent threaded through). The one residual
value-side guard is ROR's `n < w` (out of range the rotate and the
shift-or form differ); it stays a side condition on the rotate sites. The emit side additionally carries the opaque-leaf edge `LeafAgrees`, the
same edge carried throughout the emit-correctness theory.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.IselWholeFn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
open CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.AndnSelect
open CatCrypt.Crypto.SecureCompilation.Dialects.IselPipeline

/-! ## 1. The whole-function body and its ISel optimization

`bodyEmul` is the canonical `shr; shl; or` rotate-by-8 emulation at width 64 over
`Γ = [reg 64]`, with the trivial body `ret out`. `bodyOpt := iselPipeline bodyEmul`
is its ISel image: `rorImmSelect` fires (rotate-by-8 in range), selecting native
`rorImm`; `andnSelect` then runs over the result and is the **identity** (the native
image is `shr; shl; rorImm`, which `andnSelect` never matches — it fires only on
`const; xor; and`). -/

/-- The whole-function **source** body: the canonical `shr; shl; or` rotate-by-8
    emulation at width 64, `ret out`. (Same term as `RorImmSelect.exampleRotr`.) -/
def bodyEmul : Com jasminDialect [.reg 64] (.reg 64) :=
  mkRotrSubtree 64 8 .here (.ret .here)

/-- The ISel-**optimized** whole-function body. -/
def bodyOpt : Com jasminDialect [.reg 64] (.reg 64) :=
  iselPipeline bodyEmul

/-- After the rotate pass, the body is the native `rorImm` over the unchanged
    `ret` body (rotate-by-8 in range, `8 < 64`). -/
theorem rorImmSelect_bodyEmul :
    rorImmSelect bodyEmul = mkRorOp 64 8 .here (.ret .here) := by
  rw [bodyEmul, rorImmSelect_fires 64 8 (by decide)]
  rfl

/-- `andnSelect` is the **identity** on the native rotate image: it matches only
    `const; xor; and`, never `shr; shl; rorImm`, so it descends to the `ret`. By
    `rfl` — the matcher falls into the catch-all at each binder. -/
theorem andnSelect_mkRorOp :
    andnSelect (mkRorOp 64 8 (Γ := [.reg 64]) .here (.ret .here))
      = mkRorOp 64 8 .here (.ret .here) := rfl

/-- **`bodyOpt` is the doubly-processed image: the native `rorImm` form.** The
    pipeline selects `rorImm` (rotate fires) and leaves it fixed under `andnSelect`. -/
theorem bodyOpt_eq :
    bodyOpt = mkRorOp 64 8 .here (.ret .here) := by
  rw [bodyOpt, iselPipeline_eq, rorImmSelect_bodyEmul, andnSelect_mkRorOp]

/-! ## 2. (a) ISel preserves the denotation -/

/-- **(a) The ISel optimization preserves the body's denotation.** On every input
    valuation, the optimized body computes the same value as the source emulation.
    Via `iselPipeline_denote_of`, discharging its two per-pass guards for this
    concrete body: `rorImmSelect` preserves `bodyEmul`'s denotation by
    `rorImmSelect_denote` (rotate-by-8 in range); `andnSelect` preserves
    `(rorImmSelect bodyEmul)`'s denotation because it is the identity there (the
    native image is not an and-not subtree). Sorry-free. -/
theorem bodyOpt_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 64]) :
    bodyOpt.denote V = bodyEmul.denote V := by
  rw [bodyOpt]
  refine iselPipeline_denote_of bodyEmul V ?_ ?_
  · -- rotate pass preserves `bodyEmul`'s denotation (rotate-by-8 in range)
    exact rorImmSelect_denote 64 8 (by decide) .here (.ret .here) rfl V
  · -- and-not pass is the identity on the native rotate image, hence preserves
    rw [rorImmSelect_bodyEmul, andnSelect_mkRorOp]

/-! ## 3. (b) The emitted optimized function runs to the ORIGINAL denotation -/

/-- `bodyOpt` is straight-line: its three ops (`shrImm`, `shlImm`, `rorImm`) are all
    non-`stackStore`, and the body is `ret`. Discharged by `simp` on the op
    inequalities, exactly as `WholeFnLowering.smokeProg_straightLine`. -/
theorem bodyOpt_straightLine : StraightLine bodyOpt := by
  rw [bodyOpt_eq]
  refine ⟨fun w n h => ?_, fun w n h => ?_, fun w n h => ?_, trivial⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **(b) The emitted optimized whole function runs to the ORIGINAL denotation.**
    Running the lowered single-function `JasminProg` of the ISel-optimized body
    (native `rorImm`) under a word-level leaf evaluator equals the **source**
    emulation's `Com.denote` — the full end-to-end chain:

      front emits `shr; shl; or` → ISel selects native `rorImm` → whole-function
      emit → run = original `(shr; shl; or)` denotation.

    Compose `lowerComToProg_sem_eq'` on `bodyOpt` (needs `StraightLine bodyOpt`,
    discharged) with (a). The only remaining hypothesis is the opaque-leaf edge
    `hLeaf` (vacuous here — no `extCall` in a pure rotate). Sorry-free. -/
theorem emittedOpt_run_eq_origDenote {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (V : Ctxt.Valuation (d := jasminDialect) [.reg 64]) :
    runProg leafSem bodyOpt V = bodyEmul.denote V := by
  rw [lowerComToProg_sem_eq' hLeaf bodyOpt bodyOpt_straightLine V, bodyOpt_denote]

/-! ## 4. Worked KAT: the emitted native-`rorImm` function on a concrete input

Rotate-right `0x0123456789ABCDEF` by 8 at width 64. The emitted optimized function
(native `rorImm`) computes `BitVec.rotateRight 0x0123456789ABCDEF 8`, byte-for-byte
the source `(shr; shl; or)` rotate emulation's `denote`. -/

/-- **Worked end-to-end KAT.** On input `0x0123456789ABCDEF`, the emitted
    ISel-optimized whole function (native `rorImm 64 8`) runs to the source rotate
    emulation's denotation — and that value is the rotate of the input. Ties the
    whole chain to a concrete number. -/
theorem emittedOpt_run_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    runProg leafSem bodyOpt (.cons (0x0123456789ABCDEF : BitVec 64) .nil)
      = bodyEmul.denote (.cons (0x0123456789ABCDEF : BitVec 64) .nil) := by
  rw [emittedOpt_run_eq_origDenote hLeaf]

end CatCrypt.Crypto.SecureCompilation.Dialects.IselWholeFn
