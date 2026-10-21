/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ImpExprToThir
public import CatCrypt.Crypto.SecureCompilation.ImpExprToThir

/-!
# Front ingestion composition: `ImpExpr → Com jasminDialect` in one entry point

This module supplies the **single front entry point** the `catcrypt-emit` CLI
calls on `cargo hax into lean` output: a width-parameterized composition

```text
ImpExpr  --(impExprToThir params)-->  Thir  --(thirToJasmin)-->  Com jasminDialect
```

that consumes the hax-extracted source AST (`Hax.ImpExpr`) and produces
an emittable `Com jasminDialect`, so the CLI can run *from source IR* rather than
from a hand-written `Com`/`Thir` driver.

## The two pieces it chains (both pre-existing, both proved)

* `ImpExprToThir.impExprToThir : List String → ImpExpr → Option Thir` — the C2
  source→front translator (let-normalized scalar ARX subset; `none` outside it),
  with value-preservation `impExprToThir_denoteScalar`.
* `ThirToComFront.thirToJasmin : (locals) → FState → Thir → Option (Com
  jasminDialect …)` — the C1 front→jasmin lowering (ANF, bounded loops unrolled),
  with value-preservation `thirToJasmin_denote`.

Here `Thir` is the **standalone ANF statement IR**
(`ThirToComFront.Thir`, an `inductive`) — *not* `Com thirDialect`. The two share a
name fragment but are different objects:

| object | what it is | who produces / consumes it |
|---|---|---|
| `ThirToComFront.Thir` | standalone ANF stmt `inductive` | `impExprToThir` produces; `thirToJasmin` lowers it to `Com jasminDialect` |
| `Com thirDialect` | MLIR-style `Com` over `thirDialect` | hand-written (`montMulThir`); `lowerThir : Com thirDialect → Com jasminDialect` op-expands it |

So there are **two** verified lowering lanes into `Com jasminDialect`: the ANF
lane `Thir → thirToJasmin → Com jasminDialect` (the one driven by `ImpExpr`, used
here) and the dialect lane `Com thirDialect → lowerThir → Com jasminDialect`
(driven by hand-written `Com thirDialect` like `montMulThir`). There is **no**
`ImpExpr → Com thirDialect` translator; the source-ingestion front is the ANF
lane, which is what this file composes.

## What this file adds

`ImpExprToThir.lean` already proves the whole chain end-to-end for one fixed
program (`sigma0Src_to_jasmin`, an existential). What was missing is a *named,
reusable* front entry — a function the CLI can call on arbitrary `ImpExpr` — and a
clean worked example that exhibits `impToJasmin e = some …`. This file supplies
both.

### Signature scoping

`thirToJasmin` produces `Com jasminDialect (frontCtxt w nIn []) (rW w)`: a single
`rW w`-typed result over an `nIn`-word input file, both fixed before lowering. So
the front entry is parameterized over `(w nIn : Nat)` (the register width and the
number of bundled input words) and a parameter-name list `params` — the standard
front signature class that `montMulThir` (`w = 64`, two inputs) and `sigma0`
(`w = 32`, one input) already inhabit. Within that class the composition is total
over `ImpExpr`, returning `none` exactly when `impExprToThir` rejects (the source
falls outside the supported subset) or when `thirToJasmin` cannot resolve an atom.

The fully general dependent shape (`Σ Γ t, Com jasminDialect Γ t`, with `Γ`/`t`
varying per program) is not needed: the front always targets the
`frontCtxt w nIn [] → rW w` signature, so fixing `(w, nIn)` is the natural class
and keeps the return type a plain `Option (Com …)`.

## What is covered vs rejected

Covered: the let-normalized scalar ARX subset `impExprToThir` accepts (literals,
parameter / array-element reads, binary ALU ops, immediate shifts/rotates,
bitwise NOT; bounded Horner / array recurrences via the §7–§8 unrollers in
`ImpExprToThir.lean`). Rejected (→ `none`): everything else — `tuple`/`proj`/
`match_`/`ifThenElse`, refs, general loops, nested non-atom app arguments.

The actual `cargo hax into lean` JSON → `ImpExpr` parse is the hax frontend's job
(out of scope here); this is the **Lean-side** composition that consumes the
already-parsed `ImpExpr`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HaxToThirFront

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  The front entry point -/

set_option linter.deprecated false in
/-- The THIR front entry point. Compose the source→`Thir`
    translator with the `Thir`→`Com jasminDialect` lowering, at register width `w`
    over an `nIn`-word bundled input file with parameter names `params`. Returns
    the emittable `Com jasminDialect (frontCtxt w nIn []) (rW w)`, or `none` when
    either stage rejects (the source is outside the supported subset, or an atom
    fails to resolve).

    Retired with the THIR generator since 2026-10-18: new kernels compile
    through `compileA` (`haxToNF`). -/
def impToJasmin (w nIn : Nat) (params : List String) (e : ImpExpr) :
    Option (Com jasminDialect (frontCtxt w nIn []) (rW w)) :=
  (impExprToThir params e).bind fun t =>
    thirToJasmin [] (initFState w nIn) t

/-- The front entry returns `none` on a source outside the translatable subset:
    the rejection comes from `impExprToThir` returning `none`, so the whole bind
    short-circuits. -/
theorem impToJasmin_none {w nIn : Nat} {params : List String} {e : ImpExpr}
    (h : impExprToThir params e = none) : impToJasmin w nIn params e = none := by
  simp [impToJasmin, h]

/-! ## §2  Front-entry value preservation (the chain in one statement)

When `impToJasmin` succeeds, the source `denoteScalar` of the input `ImpExpr`
equals the emitted `Com`'s denotation under the canonical input valuation. This
is the two preservation theorems (`impExprToThir_denoteScalar`,
`thirToJasmin_denote`) threaded through the bind. -/

/-- **Front-entry preservation.** Whenever the front entry succeeds
    (`impToJasmin w nIn params e = some c`), the source-level `denoteScalar` of the
    hax `ImpExpr` equals the emitted `Com jasminDialect`'s denotation, under the
    canonical input valuation built from any input vector `I`. The single
    end-to-end value-preservation statement for the ingestion front: it threads
    `impExprToThir_denoteScalar` (C2) into `thirToJasmin_denote` (C1). -/
theorem impToJasmin_denote {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (e : ImpExpr)
    {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (h : impToJasmin w nIn params e = some c) :
    ImpExpr.denoteScalar params I e (fun _ => none)
      = some (c.denote (inputValuation w nIn I)) := by
  simp only [impToJasmin] at h
  -- Peel the bind: a `Thir` must have been produced, and lowered to `c`.
  rcases ht : impExprToThir params e with _ | t
  · rw [ht] at h; simp at h
  · rw [ht] at h
    simp only [Option.bind_some] at h
    -- C2: source `denoteScalar` = front `Thir.denote`.
    have hsrc := impExprToThir_denoteScalar (w := w) (nIn := nIn) params I e
      (fun _ => none) ht
    -- C1: front `Thir.denote` = emitted `Com.denote`.
    have hfront := thirToJasmin_denote (w := w) (nIn := nIn) [] I t
      (LEnv.empty w) (initFState w nIn) (inputValuation w nIn I) c
      (initAgree I) h
    -- `LEnv.empty w = fun _ => none` definitionally, so the env in `hfront`
    -- matches `hsrc`'s `(fun _ => none)`; chain the two equalities.
    rw [hsrc]; exact hfront

/-! ## §3  Worked example: a Montgomery-flavoured multiply-add leaf

A small two-input arithmetic body over an array parameter `"w"`, in the
let-normalized ARX shape the front accepts:

```text
let p = w[0] * w[1];        // t = a * b
let r = p + w[0];           // r = t + a    (a stand-in MAC tail)
r
```

This mirrors the *opening* of `montMulThir`'s REDC (`t = a*b`, then a chained
add), expressed as a hax `ImpExpr` and pushed through `impToJasmin`. It exercises
exactly the array-read + binary-op surface (`index[w,k]`, `wrapping_mul`,
`wrapping_add`) that real ANF hax bodies emit, at width `w = 64` with `nIn = 2`
input words. -/

/-- The worked-example source as a hax `ImpExpr`: `(w[0] * w[1]) + w[0]`, fully
    let-normalized over the single array parameter `"w"`. -/
def maddSrc : ImpExpr :=
  .letBind "p"
      (.app "wrapping_mul"
        [ .app "index" [.var "w", .lit (.int 0)]
        , .app "index" [.var "w", .lit (.int 1)] ])
    (.letBind "r"
        (.app "wrapping_add"
          [ .var "p", .app "index" [.var "w", .lit (.int 0)] ])
      (.var "r"))

/-- The front entry **succeeds** on the worked-example `ImpExpr`: ingesting it at
    `w = 64`, `nIn = 2`, parameter `["w"]` produces a concrete `Com jasminDialect`.
    The single demonstration that the composed front turns hax source into an
    emittable `Com`. -/
theorem maddSrc_compiles : (impToJasmin 64 2 ["w"] maddSrc).isSome := by
  native_decide

/-- **Worked example, end-to-end (`ImpExpr → Com jasminDialect`, with the value
    tie).** There is a `Com jasminDialect` `c` such that the hax `ImpExpr`
    `(w[0] * w[1]) + w[0]` ingests through the front entry to `c`, and `c`'s
    `BitVec 64` denotation is exactly `(I 0 * I 1) + I 0` for every two-word input
    `I`. Threads `impToJasmin_denote` through the source semantics of `maddSrc`. -/
theorem maddSrc_front_e2e (I : Fin 2 → BitVec 64) :
    ∃ c : Com jasminDialect (frontCtxt 64 2 []) (rW 64),
      impToJasmin 64 2 ["w"] maddSrc = some c ∧
      c.denote (inputValuation 64 2 I)
        = (inpGet I 0 * inpGet I 1) + inpGet I 0 := by
  set c := (impToJasmin 64 2 ["w"] maddSrc).get maddSrc_compiles with hc_def
  have hc : impToJasmin 64 2 ["w"] maddSrc = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  -- Front preservation: source `denoteScalar` = emitted `Com.denote`.
  have hpre := impToJasmin_denote (w := 64) (nIn := 2) ["w"] I maddSrc hc
  -- The source value of `maddSrc` is `(w[0]*w[1]) + w[0]`.
  have hspec : ImpExpr.denoteScalar ["w"] I maddSrc (fun _ => none)
      = some ((inpGet I 0 * inpGet I 1) + inpGet I 0) := by
    simp only [maddSrc, ImpExpr.denoteScalar, denoteAtomExpr, indexAtom?,
      recogBin, recogShift, litNat?, ShiftKind.apply, JasminBinOp.apply,
      List.mem_cons, List.not_mem_nil, reduceIte, String.reduceEq, Int.toNat]
    rfl
  -- Chain: spec = denoteScalar (hspec) = Com.denote (hpre), peel the `some`.
  rw [hspec] at hpre
  exact (Option.some_inj.1 hpre).symm

/-! ## §4  Sanity `#check`s of the front entry's type -/

/-- The front entry has the advertised type: `ImpExpr → Option (Com jasminDialect …)`. -/
example : ImpExpr → Option (Com jasminDialect (frontCtxt 64 2 []) (rW 64)) :=
  impToJasmin 64 2 ["w"]

attribute [deprecated "The THIR generator is retired: new kernels compile through compileA (haxToNF); existing THIR kernel families move to the other kernel producers. impToJasmin is the same composition as CompileFromHax.compileFromHax." (since := "2026-10-18")] impToJasmin

end CatCrypt.Crypto.SecureCompilation.HaxToThirFront
