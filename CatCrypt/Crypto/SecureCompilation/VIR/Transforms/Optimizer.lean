/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.Peephole
import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.IfToCmov

/-!
# `Optimizer` — composed optimization driver for VIR

This file is the single entry point that composes the existing VIR
optimization passes into a callable pipeline:

* `Peephole.peephole` — algebraic peephole on `Com catCryptDialect`
  (currently `bvXor v v → 0`, `bvSub v v → 0`).
* `Transforms.ifToCmov` — `Secret`-tagged value-shaped `ifBit` to
  branch-free `cmov` chain on `ComR catCryptDialect`.

Each pass already ships with its own denotation/correctness theorem.
This file's job is to:

1. Provide composable entry points (`optimize`, `optimizeR`).
2. Prove their correctness as a one-line composition of the per-pass
   theorems (`optimize_denote_eq`, `optimizeR_denote_eq`).
3. Prove that `optimizeR` never decreases CT-safety
   (`optimizeR_ctSafe_or_unchanged`).

## v1 scope (single-pass)

For v1 we compose the passes **without** fixed-point iteration:

* `optimize := peephole` on `Com` (one application).
* `optimizeR c := ifToCmov c` on `ComR`. (Lifting the inner `Com`-level
  peephole through `ComR` requires walking under `ifBit`, which is
  follow-up work; the `ifToCmov` pass produces `ComR` whose result is
  region-free, so a follow-up can compose `peephole ∘ toCom?` on the
  region-free output.)

Fuel-based fixed-point iteration is documented as v2 — both passes are
idempotent in practice on the patterns they recognise (re-applying
`peephole` to `bvConst 0` is a no-op; re-applying `ifToCmov` to a
`cmov`-chain is a no-op since the chain has no `ifBit`), so a single
pass discharges all currently-recognised patterns in one go.

## Compress emission wiring

`CompressJazzEmit.lean` operates on `LowCT`, not on `Com catCryptDialect`,
so there is no `compressVIR : Com catCryptDialect _ _` value to plug
the optimizer into. The wiring is documented here as **deferred** until
`CompressJazzEmit` (or a sibling file) exposes a `Com`-level
representation. Once it does, an `optimizedCompressVIR := optimize
compressVIR` definition with a `_denote_eq` corollary is a two-line
addition.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
  (CatCryptOp catCryptDialect)

set_option autoImplicit false

namespace Optimizer

/-! ## 1. One-pass optimization entry points -/

/-- One-pass optimization on `Com catCryptDialect`. v1 applies the
    algebraic peephole. `IfToCmov` operates on `ComR`, so it appears in
    `optimizeR` rather than here. -/
def optimize {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    Com catCryptDialect Γ t → Com catCryptDialect Γ t :=
  Peephole.peephole

/-- One-pass optimization on `ComR catCryptDialect`. v1 applies
    `ifToCmov` to the top of the region tree. A future revision should
    walk under `ifBit` arms and lift `Com`-level peephole through them;
    see the file docstring for the fuel-based fixed-point follow-up. -/
def optimizeR {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    ComR catCryptDialect Γ t → ComR catCryptDialect Γ t :=
  Transforms.ifToCmov

/-! ## 2. Composed denotational correctness

Each underlying pass preserves denotation; the composition therefore
preserves denotation. Each theorem is a one-liner via the per-pass
correctness theorems (`peephole_denote_eq`, `ifToCmov_denote_eq`). -/

/-- **Main correctness theorem (Com)**: `optimize` preserves denotation. -/
theorem optimize_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (V : Ctxt.Valuation Γ) :
    (optimize c).denote V = c.denote V := by
  simp [optimize, Peephole.peephole_denote_eq]

/-- **Main correctness theorem (ComR)**: `optimizeR` preserves denotation. -/
theorem optimizeR_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : ComR catCryptDialect Γ t) (V : Ctxt.Valuation Γ) :
    (optimizeR c).denote V = c.denote V := by
  simp [optimizeR, Transforms.ifToCmov_denote_eq]

/-! ## 3. CT-safety: optimization never decreases CT-safety -/

/-- **CT-escalation theorem**: optimization either makes the program
    outright CT-safe (when it discharged a `Secret`-tagged `ifBit`) or
    leaves CT-safety unchanged. This is the composed analogue of
    `ifToCmov_ctSafe_or_unchanged`. -/
theorem optimizeR_ctSafe_or_unchanged {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : ComR catCryptDialect Γ t) :
    ctSafeComR (optimizeR c) = true ∨
      ctSafeComR (optimizeR c) = ctSafeComR c := by
  -- v1: `optimizeR = ifToCmov`, so this follows immediately.
  exact Transforms.ifToCmov_ctSafe_or_unchanged c

/-! ## 4. Smoke test

A small program demonstrating `optimize` on the algebraic peephole:
`let x = K; let y = bvXor x x; ret y` — after optimization the inner
`bvXor x x` is folded to `bvConst 0`, and the denotation is `0`. -/

namespace SmokeTest

/-- The "obvious" CT-safety win program: `let x = K; let y = bvXor x x;
    ret y`. The unoptimized denotation is `K ^^^ K = 0`; the
    optimizer replaces the `bvXor` with a `bvConst 0`, and the result
    still denotes to `0`. -/
def progSelfXor : Com catCryptDialect [] (CryptoTy.sword 8) :=
  .var (t := CryptoTy.sword 8)
      { op := .bvConst 8 (0x42 : BitVec 8), retTy_eq := rfl, args := .nil }
    (.var (t := CryptoTy.sword 8)
        { op := .bvXor 8, retTy_eq := rfl,
          args := .cons .here (.cons .here .nil) }
      (.ret .here))

/-- Smoke test 1: the optimized program still denotes to `0`. -/
example : (optimize progSelfXor).denote .nil = (0 : BitVec 8) := by
  rw [optimize_denote_eq]; rfl

/-- Smoke test 2: pre/post optimization denotations agree (regression
    check for `optimize_denote_eq`). -/
example : (optimize progSelfXor).denote .nil = progSelfXor.denote .nil :=
  optimize_denote_eq progSelfXor .nil

/-- Smoke test 3 (ComR-side): the optimizer turns a value-shaped
    `Secret`-tagged bit `ifBit` into a CT-safe program. -/
example {Γ : Ctxt catCryptDialect} (c a b : Ctxt.Var Γ .bit) :
    ctSafeComR (optimizeR (ComR.ifBit (d := catCryptDialect) (t := .bit)
        c .Secret (.ret a) (.ret b))) = true := by
  exact Transforms.ifToCmov_makes_bit_secret_ifBits_ctSafe c a b

end SmokeTest

end Optimizer

end CatCrypt.Crypto.SecureCompilation.VIR
