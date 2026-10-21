/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ImpExprToThir
public import CatCrypt.Crypto.SecureCompilation.ImpExprToThir

/-!
# C3: the single compile-from-hax correctness meta-theorem

This module is the **C3** step of the verified-compiler plan: it assembles the
*single* end-to-end compile-correctness statement for compile-from-hax, by
composing the two value-preservation pieces that are already proven:

* **C2** (`ImpExprToThir.lean`): `impExprToThir_denoteScalar` — the hax
  extraction AST `ImpExpr` translates value-preservingly into the verified
  `Thir` front IR (`ImpExpr.denoteScalar = Thir.denote`).
* **C1** (`ThirToComFront.lean`): `thirToJasmin_denote` — the `Thir` front IR
  lowers value-preservingly into a `Com jasminDialect` (the emitted owned-x86
  IR) (`Thir.denote = Com.denote`).

## What it adds

`ImpExprToThir.sigma0Src_to_jasmin` already threaded these two theorems for the
single concrete σ₀ leaf. This file lifts that one-off into the **universal**
statement, packaged as a single compiler `compileFromHax` and a single
correctness theorem `compileFromHax_denote`:

> for every hax `ImpExpr` `e` and input vector `I`, if `compileFromHax` succeeds
> producing the jasmin `Com` `c`, then the *source* denotation of `e` equals the
> denotation of `c`.

That is the whole compile-from-hax pipeline (`ImpExpr → Thir → Com jasminDialect`)
proven value-preserving in one statement, no per-primitive compiler reasoning.

## The per-primitive obligation framing

`compileFromHax_meets_spec` packages the *consequence* a per-primitive proof
discharges: a primitive author supplies the extracted `ImpExpr` `e` and proves
its **source** denotation equals the FIPS / NIST / reference spec value; the
meta-theorem then guarantees the **compiled** jasmin `Com` computes that exact
value. The compiler correctness is proved once, here; per-primitive work reduces
to a source-level spec-agreement obligation.

## σ₀ as a corollary

`sigma0_compiles` re-derives the SHA-256 message-schedule σ₀ end-to-end result
*through* the meta-theorem (`compileFromHax_meets_spec`), not as a fresh proof —
demonstrating that the universal statement composes on the concrete leaf.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHax

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  The single compile entry point

`compileFromHax` is the whole front pipeline as one function: translate the hax
`ImpExpr` into the `Thir` front IR (C2), then lower that into a
`Com jasminDialect` at the empty local scope (C1). Either stage may fail
(`none`), so the composition is `Option.bind`; whatever it *does* produce is
value-preserving by `compileFromHax_denote`. -/

set_option linter.deprecated false in
/-- Compile a hax `ImpExpr` to a `Com jasminDialect`, in one step:
    `ImpExpr → Thir` (the C2 translator) then `Thir → Com` (the C1 front),
    lowered at the empty local scope (`initFState w nIn`). Retired with the
    THIR generator since 2026-10-18: new kernels compile through `compileA`
    (`haxToNF`), and the kernel families built here move to the other kernel
    producers. -/
def compileFromHax {w nIn : Nat} (params : List String) (e : ImpExpr) :
    Option (Com jasminDialect (frontCtxt w nIn []) (rW w)) :=
  (impExprToThir params e).bind fun t => thirToJasmin [] (initFState w nIn) t

/-! ## §2  The compile-from-hax correctness meta-theorem

The single C3 deliverable: compile-from-hax is value-preserving end to end, with
the *source* semantics (`ImpExpr.denoteScalar`) on the left and the *target*
(`Com.denote` of the emitted jasmin IR) on the right. The proof recovers the
intermediate `Thir` from the `Option.bind` success, then chains C2's
`impExprToThir_denoteScalar` with C1's `thirToJasmin_denote` (via `initAgree`). -/

/-- **Compile-from-hax correctness (the C3 meta-theorem).** Whenever
    `compileFromHax params e = some c`, the hax source's scalar denotation equals
    the compiled `Com jasminDialect`'s denotation under the canonical input
    valuation. The whole `ImpExpr → Thir → Com` pipeline, value-preserving in one
    statement: C2 (`impExprToThir_denoteScalar`) composed with C1
    (`thirToJasmin_denote`). -/
theorem compileFromHax_denote {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (e : ImpExpr)
    {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (hc : compileFromHax params e = some c) :
    ImpExpr.denoteScalar params I e (LEnv.empty w)
      = some (c.denote (inputValuation w nIn I)) := by
  -- Recover the intermediate `Thir` from the `Option.bind` success.
  simp only [compileFromHax, Option.bind_eq_some_iff] at hc
  obtain ⟨t, ht, hct⟩ := hc
  -- C2 (`ImpExprToThir`) : source `denoteScalar` = front `Thir.denote`.
  have hsrc := impExprToThir_denoteScalar (w := w) (nIn := nIn) params I e
    (LEnv.empty w) ht
  -- C1 (the front) : `Thir.denote` = `Com.denote`, via `initAgree`.
  have hfront := thirToJasmin_denote (w := w) (nIn := nIn) [] I t (LEnv.empty w)
    (initFState w nIn) (inputValuation w nIn I) c (initAgree I) hct
  rw [hsrc, hfront]

/-! ## §3  The per-primitive obligation framing

`compileFromHax_meets_spec` is the clean corollary capturing what a per-primitive
correctness proof must discharge: *give the extracted `ImpExpr`, show its source
denotation is the spec value, and the compiled jasmin `Com` computes that value*
— one source-level obligation, with all compiler reasoning factored into
`compileFromHax_denote`. -/

/-- **Per-primitive spec obligation.** If `compileFromHax` succeeds and the hax
    source's scalar denotation equals a `spec` value, then the compiled
    `Com jasminDialect` denotes to exactly that `spec`. The statement a
    per-primitive proof discharges: supply the extracted `e`, prove its
    source-denotation is the FIPS / reference value, and get target correctness
    of the emitted jasmin for free. Immediate from `compileFromHax_denote`. -/
theorem compileFromHax_meets_spec {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (e : ImpExpr) (spec : BitVec w)
    {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (hc : compileFromHax params e = some c)
    (hspec : ImpExpr.denoteScalar params I e (LEnv.empty w) = some spec) :
    c.denote (inputValuation w nIn I) = spec := by
  have h := compileFromHax_denote params I e hc
  rw [hspec] at h
  exact (Option.some.injEq _ _ ▸ h).symm

/-! ## §4  σ₀ as a corollary of the meta-theorem

The SHA-256 message-schedule σ₀ result re-derived *through* the C3 meta-theorem
(`compileFromHax_meets_spec`), demonstrating that the universal statement
composes on a concrete leaf. The compilation success is computed; the value
equation routes the FIPS σ₀ source-spec (`sigma0Src_denoteScalar`) through the
single obligation — no re-proof of the compiler. -/

/-- The compile-from-hax pipeline succeeds on σ₀ (`w = 32`, one parameter). -/
theorem sigma0_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"] sigma0Src).isSome := by
  native_decide

/-- **σ₀ via the C3 meta-theorem.** There is a compiled `Com jasminDialect` `c`
    with `compileFromHax ["x"] sigma0Src = some c`, and for every input `x`, `c`'s
    `BitVec 32` denotation is exactly the FIPS 180-4 σ₀ formula
    `(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)`. Proved by routing the FIPS source-spec
    (`sigma0Src_denoteScalar`) through `compileFromHax_meets_spec` — the σ₀
    correctness goes *through* the universal meta-theorem, not a fresh proof. -/
theorem sigma0_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["x"] sigma0Src = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  -- The concrete compiled Com (computed; `sigma0_compileFromHax_isSome` proves
  -- the lowering returns `some`).
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"] sigma0Src).get
    sigma0_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"] sigma0Src = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  -- The FIPS σ₀ source-spec at input `x` (`(fun _ => x) 0 = x` reduced inside).
  have hspec := sigma0Src_denoteScalar (fun _ => x)
  -- `LEnv.empty 32 = fun _ => none` definitionally; route the spec through the
  -- per-primitive obligation corollary of the C3 meta-theorem.
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    sigma0Src _ hc hspec

attribute [deprecated "The THIR generator is retired: new kernels compile through compileA (haxToNF); existing compileFromHax kernel families move to the other kernel producers." (since := "2026-10-18")] compileFromHax

end CatCrypt.Crypto.SecureCompilation.CompileFromHax
