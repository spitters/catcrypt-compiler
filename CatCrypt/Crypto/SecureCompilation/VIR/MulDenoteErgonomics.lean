/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Ergonomic `Com.denote = field spec` for `mul`-based kernels

`MontMulFragmentDemo` (#477) and `FieldEmitGoldenPath` discharge each
`Com.denote = <BitVec spec>` step with a bare `rfl`. That works — the Jasmin
dialect's denotation is fully structural — but a bare `rfl` forces the kernel
*defeq* through the entire `Com.denote / Expr.denote / lookupArgs / Var.lookup`
recursion plus the `jasminDenote` instance match at the kernel's reducibility
setting. For a wide kernel (a full CIOS Montgomery limb chain) that single
`isDefEq` is what heartbeat-outs: `mul`/`mulhi` kernels lower golden but their
value step has no cheap `rfl` — that is a property of the bare `rfl` over the
whole body, not of any one op.

This file factors the denotation machinery out as a one-line tactic
(`com_denote`) built on a small reusable `simp` set. Instead of one monolithic
`isDefEq` over the whole kernel, the recipe is two phases:

* a `simp only` over the denotation *skeleton* (`Com.denote`, `Expr.denote`,
  `Expr.lookupArgs`, `Ctxt.Valuation.extend` — the recursive `Com`/`Expr` defs).
  This rewrites the binder chain open one `.var` at a time (linear in kernel
  size), turning the nested `Com.denote` recursion into a flat tree of
  `DialectDenote.denote …` applied to `lookupArgs …` argument vectors. Each
  step is a rewrite, not a whnf search, so it avoids the exponential `isDefEq`
  a bare `rfl` over the whole body risks;
* a trailing `rfl` that settles the residue: the per-op `match` on the
  now-concrete `HVector.cons` argument vectors plus the dialect op semantics
  (`regArith → JasminBinOp.apply`, `mulhi → mulHiW`, `shrImm → >>>`,
  `regConst → ofNat`). This residual `rfl` is shallow and local — one
  constructor `match` per binder, with `mulHiW a b` / `a * b` left symbolic
  (the `a.toNat * b.toNat / 2 ^ w` arithmetic is never forced) — not one deep
  defeq over the entire denotation recursion.

The win over the bare `rfl` of `MontMulFragmentDemo` / `FieldEmitGoldenPath` is
*where the work happens*: the `simp only` does the structural, size-linear part
by rewriting, and the kernel `rfl` only discharges an already-unfolded shallow
residue. For the small kernels below a bare `rfl` still works at default
heartbeats; the two-phase form is the shape that scales to a wide CIOS limb
chain, where a single `rfl` over the whole body is the step that has no cheap
discharge.

## What the set contains

The skeleton (`Com.denote`, `Expr.denote`, `Expr.lookupArgs`,
`Ctxt.Valuation.extend`) is dialect-agnostic (`Core.lean`); `com_denote` also
lists `Ctxt.Var.lookup`, the two `HVector` projections, and the Jasmin op
semantics (`jasminDenote` instance + `JasminBinOp.apply`) so the bundle is
robust across kernels (any of those that are needed as rewrites fire; the rest
are settled by the trailing `rfl`). A different dialect reuses the skeleton and
swaps the last two op-semantics entries.

## Worked demo: the GF(251) Solinas single fold

`(x >>> 8) * 5 + (x &&& 255)` — the `mul`-by-constant-5 Solinas reduction step
(GF(251), `2 ^ 8 ≡ 5`), the `mul`-based sibling of `FieldEmitGoldenPath`'s
all-ALU `fieldCondSub251Com`. It exercises a `regArith .mul` (against a
`regConst 5`), a `shrImm 8`, an `and` (against a `regConst 255`), and an `add` —
a real `mul` binding, not just `mulhi`. We prove `Com.denote = the BitVec spec`
by the method, NOT `native_decide`, NOT a heartbeat-bumped `rfl`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MulDenoteErgonomics

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The reusable denotation tactic

`com_denote` is the packaged two-phase recipe: `simp only` over the denotation
skeleton (rewriting the binder chain open, linear in kernel size) then a shallow
`rfl` to settle the per-op `match` residue with the BitVec op-results left
symbolic. -/

/-- One-line tactic: discharge a `Com jasminDialect` `denote = spec` goal by
    rewriting the denotation skeleton open with the reusable `simp` set, then
    `rfl` to settle the (now shallow, per-binder) `match` residue.

    The `simp only` list is the recursive denotation skeleton (`Com.denote`,
    `Expr.denote`, `Expr.lookupArgs`, `Ctxt.Valuation.extend`) plus the
    per-element pieces (`Ctxt.Var.lookup`, `HVector.head`/`tail`) and the Jasmin
    op semantics (`jasminDenote` instance + `JasminBinOp.apply`) — bundled so the
    tactic is robust across kernels: whichever of these are needed as rewrites
    fire, the rest are settled by the trailing `rfl`. The first group is
    dialect-agnostic; a different dialect swaps the op-semantics tail. -/
macro "com_denote" : tactic =>
  `(tactic|
    (simp only [Com.denote, Expr.denote, Expr.lookupArgs, Ctxt.Var.lookup,
      Ctxt.Valuation.extend, HVector.head, HVector.tail,
      jasminDenote, JasminBinOp.apply]; rfl))

/-! ## 2. Argument context and references for the GF(251) Solinas fold

One input `x : reg 64`. `vx = .here`. -/

abbrev Γ : Ctxt jasminDialect := [.reg 64]

/-- The sole input `x`. -/ def vx : Ctxt.Var Γ (.reg 64) := .here

/-! ## 3. The intended pure function (over `BitVec 64`)

The GF(251) Solinas single fold `(x >>> 8) * 5 + (x &&& 255)`: split `x` into a
low byte `x &&& 255` and a high part `x >>> 8`, and fold the high part back in
weighted by `2^8 ≡ 5 (mod 251)`. -/

/-- The GF(251) Solinas single-fold spec: `(x >>> 8) * 5 + (x &&& 255)`. -/
def solinas251Fold (x : BitVec 64) : BitVec 64 :=
  ((x >>> 8) * (5 : BitVec 64)) + (x &&& (255 : BitVec 64))

/-! ## 4. The `Com` program

`c5 := 5 ; hi := x >>> 8 ; prod := hi * c5 ; c255 := 255 ; lo := x &&& c255 ;
 r := prod + lo ; ret r` — over arg `[x]`. The `prod := hi * c5` is a genuine
`regArith .mul` binding (the demo's reason to exist), `hi := x >>> 8` a `shrImm`,
`lo := x &&& c255` an `and`, and the constants are `regConst`s. -/
def solinas251FoldCom : Com jasminDialect Γ (.reg 64) :=
  -- d0 := c5 = 5
  .var (.mk (.regConst 64 5) rfl .nil)
  -- d1 := hi = x >>> 8        (x = vx shifted by one binder)
  (.var (.mk (.shrImm 64 8) rfl (.cons (.there vx) .nil))
  -- d2 := prod = hi * c5      (hi = .here, c5 = .there .here)
  (.var (.mk (.regArith .mul 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- d3 := c255 = 255
  (.var (.mk (.regConst 64 255) rfl .nil)
  -- d4 := lo = x &&& c255     (x = .there.there.there.there.here, c255 = .here)
  (.var (.mk (.regArith .and 64) rfl
            (.cons (.there (.there (.there (.there .here))))
              (.cons .here .nil)))
  -- d5 := r = prod + lo       (prod = .there.there.here, lo = .here)
  (.var (.mk (.regArith .add 64) rfl
            (.cons (.there (.there .here)) (.cons .here .nil)))
    (.ret .here))))))

/-! ## 5. The value proof — `Com.denote = spec`, via the reusable method

NOT `native_decide`, NOT a heartbeat-bumped brute `rfl`: the `com_denote` tactic
rewrites the denotation skeleton open, after which a shallow `rfl` settles the
per-op residue with the BitVec op-results left symbolic. -/

/-- The input valuation `⟨x⟩`. -/
def val (x : BitVec 64) : Ctxt.Valuation Γ := .cons x .nil

/-- **The GF(251) Solinas-fold value proof, spelled out.** The source
    `Com.denote` is exactly `(x >>> 8) * 5 + (x &&& 255)`. The `simp only`
    rewrites the binder chain open over the denotation skeleton (the consumed
    lemmas: `Com.denote`/`Expr.denote`/`Expr.lookupArgs`/`Ctxt.Valuation.extend`,
    plus the kernel/spec defs), then `rfl` settles the shallow per-op `match`
    residue — the `mul` binding to a symbolic `BitVec` `*`, the `shrImm` to
    `>>>`, the `and` to `&&&`, the `regConst`s to `BitVec.ofNat`, with no defeq
    blow-up and no `native_decide`. -/
@[simp] theorem solinas251FoldCom_denote (x : BitVec 64) :
    solinas251FoldCom.denote (val x) = solinas251Fold x := by
  simp only [solinas251FoldCom, val, solinas251Fold, Com.denote, Expr.denote,
    Expr.lookupArgs, Ctxt.Valuation.extend]
  rfl

/-- Same statement via the packaged one-line `com_denote` tactic (the canonical
    entry point for reuse): identical proof obligation, one token. -/
theorem solinas251FoldCom_denote' (x : BitVec 64) :
    solinas251FoldCom.denote (val x) = solinas251Fold x := by
  com_denote

/-! ## 6. Reusing the set on a `mulhi` binding (the CIOS building block)

To show the set is not specific to the low-word `mul`: the high word `mulHiW`
binding reduces the same way. This is the `mulhi` arm a full CIOS Montgomery
limb uses (the `MULX` hi output). The point is that `com_denote` leaves
`mulHiW a b` **symbolic** — the `a.toNat * b.toNat / 2^64` arithmetic is not
forced, so the same proof scales to a wide limb chain without the defeq blow-up
that a monolithic `rfl` over the whole body would hit. -/

/-- A single `mulhi` binding `hi := mulhi x y` over `[x, y]`, denoting `mulHiW`,
    proved by the same set — `mulHiW x y` is left symbolic. -/
def mulHiCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var (.mk (.mulhi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

theorem mulHiCom_denote (x y : BitVec 64) :
    mulHiCom.denote (.cons x (.cons y .nil)) = mulHiW y x := by
  com_denote

end CatCrypt.Crypto.SecureCompilation.VIR.MulDenoteErgonomics
