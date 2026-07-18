/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax
import CatCrypt.Crypto.SHA256.Extraction.Sha256_haxpipe

/-!
# Compiling a CALL IN LET-RHS position (SHA-256 σ₀ via let-flatten)

`CompileFromHaxCall` compiled a helper call in **tail/return** position
(`small_sigma0(x)`). It documented the orthogonal gap this file closes:

> Inlining `let r = small_sigma0(x); r` would land the callee's let-chain as the
> RHS of `let r = …`, which the §3 `rhsOf` rejects (a `letBind` is not a flat
> `Rhs`).

That is exactly the non-tail-position shape whole-function verbatim compress
needs — calls sit in `let`-RHS / `array_update`-arg positions, not just at the
return. This file is the bounded demo for the §12 `letFlatten` pre-pass that
closes it.

## The pipeline

The caller body is the let-RHS call

```text
letCallSrc = let r = small_sigma0(x); r
```

The three front pre-passes compose (the order verified by the `rfl`-probe below):

```text
letCallPipe = letFlatten 100 (anfLift (callInline shaReg 100 letCallSrc))
```

* `callInline` (§11) inlines `small_sigma0`'s verbatim extracted body into the
  RHS of `let r = …`, producing `let r = (let x = x; …σ₀-body…); r` — the very
  `letBind`-as-RHS form `rhsOf` rejects.
* `anfLift` (§10) head-normalizes (`#32` tags dropped) and flattens the nested
  `BitXor`/`rotate_right`/`Shr` tree into fresh `_anf<n>` binders.
* `letFlatten` (§12) hoists the inner `let x = x; _anf… ` chain **out** of the
  `let r = …` RHS, re-associating into one flat let-chain.

The result lands in the §3 flat let-normalized atom-arg subset, so the unchanged
`compileFromHax` (C2 ∘ C1) compiles it — value-preserving against the FIPS 180-4
σ₀ formula `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`.

## On the pass order

`letFlatten` runs **last** (after `anfLift`), not before it: `anfLift`'s
`letBind` arm re-introduces nested-`let` RHSes when it flattens the `app` tree
sitting in `let r = …`'s RHS, so `letFlatten` must run afterward to hoist those
out. (Running `anfLift` after `letFlatten` re-creates the nested-let RHS and
`compileFromHax` fails — confirmed by diagnostics.) Both `letFlatten` and the
hoisted binders are fresh/distinct names (`_anf<n>`, the callee's `x`), so the
§12 hygiene assumption holds and the plain re-association is sound.

## On the preservation statement

As in `CompileFromHaxCall`/`CompileFromHaxVerbatim`, the inlined body is
`#32`-tagged with nested-app arguments, so its *own* `ImpExpr.denoteScalar` is
`none` until `anfLift`. The honest whole-pass preservation is therefore the
demo-specific `letCall_denoteScalar`: the let-flattened inlined call denotes to
the FIPS σ₀ value, proved by reducing `letCallPipe` to the explicit flat
`letCallNorm` (rfl-probe) then `denoteScalar`-reduction. Routed through
`compileFromHax_meets_spec`, this yields `letCall_compiles` — a CALL IN LET-RHS
position compiled correctly, via let-flatten composed with call-inline + ANF.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxLetFlatten

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminBinOp)

/-- The σ₀ callee definition: one formal parameter `"x"`, body the *verbatim*
    extracted `Sha256.small_sigma0_impExpr` (`#32`-tagged, nested-app args). -/
def sigma0Callee : List String × ImpExpr := (["x"], Sha256.small_sigma0_impExpr)

/-- The callee registry: `small_sigma0` resolves to `sigma0Callee`; every other
    head is `none`. -/
def shaReg : CallRegistry := fun f => if f = "small_sigma0" then some sigma0Callee else none

/-- The caller body: the call `small_sigma0(x)` in **let-RHS** position — the exact
    `let r = small_sigma0(x); r` form `CompileFromHaxCall` documented as rejected by
    `rhsOf` (the inlined callee let-chain would sit as `let r = …`'s RHS). -/
def letCallSrc : ImpExpr := .letBind "r" (.app "small_sigma0" [.var "x"]) (.var "r")

/-- The fully-normalized caller body. The three passes compose: `callInline`
    inlines the verbatim σ₀ body into the `let r = …` RHS; `anfLift` flattens its
    `#32`-tagged nested-app tree; `letFlatten` (run last) hoists the resulting
    inner let-chain out of the `let r = …` RHS into one flat let-chain. -/
def letCallPipe : ImpExpr := letFlatten 100 (anfLift (callInline shaReg 100 letCallSrc))

/-- The explicit flat normal form of `letCallPipe`: the callee's leading
    `let x = x`, then the `anfLift`-hoisted `_anf<n>` ARX chain, then the caller's
    own `let r = (_anf3 ⊕ _anf0); r` — and crucially **no** `letBind` sits as
    another `letBind`'s RHS (that is exactly what `letFlatten` achieved; before it,
    the `_anf…` chain was the RHS of `let r = …`). In the §3 atom-arg subset. -/
def letCallNorm : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "_anf2" (.app "rotate_right" [.var "x", .lit (.int 7)])
    (.letBind "_anf1" (.app "rotate_right" [.var "x", .lit (.int 18)])
     (.letBind "_anf3" (.app "BitXor" [.var "_anf2", .var "_anf1"])
      (.letBind "_anf0" (.app "shr" [.var "x", .lit (.int 3)])
       (.letBind "r" (.app "BitXor" [.var "_anf3", .var "_anf0"])
        (.var "r"))))))

/-- `letFlatten 100 (anfLift (callInline shaReg 100 letCallSrc))` reduces
    (definitionally) to the explicit flat `letCallNorm`. Closed-term computation:
    `rfl`. This is the demo's rfl-probe pin — it confirms the pass-composition
    *order* (`letFlatten` last) lands a flat atom-arg let-chain with no
    `letBind`-as-RHS. -/
theorem letCallPipe_eq : letCallPipe = letCallNorm := rfl

/-- **The let-flattened inlined-call body is value-preserving.** Its `denoteScalar`
    (the §2 source semantics, parameter `"x"`, single input `I 0 = x`) is exactly
    the FIPS 180-4 σ₀ value `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`. The honest
    whole-pass preservation: the `#32`-tagged inlined callee body has no denotation
    of its own; `callInline` + `anfLift` + `letFlatten` together make it denote — to
    the σ₀ spec of the call argument. Proved by `denoteScalar`-reduction of
    `letCallNorm`, mirroring `caller_callInline_denoteScalar`'s simp set. -/
theorem letCall_denoteScalar (x : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 1) ["x"] (fun _ => x) letCallPipe (fun _ => none)
      = some (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat)) := by
  rw [letCallPipe_eq]
  simp only [letCallNorm, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the let-flattened inlined call. -/
theorem letCall_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"] letCallPipe).isSome := by native_decide

/-- **A CALL IN LET-RHS position compiles correctly (via let-flatten).** There is a
    compiled `Com jasminDialect` `c` such that the caller `let r = small_sigma0(x); r`
    — the exact non-tail-position form `CompileFromHaxCall` showed `rhsOf` rejects —
    `callInline`-inlines the helper's verbatim body, `anfLift`-flattens the ARX tree,
    `letFlatten`-hoists the inner let-chain out of the `let r = …` RHS, compiles to
    `c`, and for every input `x`, `c`'s `BitVec 32` denotation is exactly the FIPS
    180-4 σ₀ formula `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`. The last front primitive
    whole-function verbatim compress needs: routes `letCall_denoteScalar` through the
    C3 meta-theorem `compileFromHax_meets_spec` (no fresh compiler proof). -/
theorem letCall_compiles :
    ∃ c, compileFromHax (w := 32) (nIn := 1) ["x"] letCallPipe = some c ∧
         ∀ (x : BitVec 32),
           c.denote (inputValuation 32 1 (fun _ => x))
             = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"] letCallPipe).get letCall_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"] letCallPipe = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    letCallPipe _ hc (letCall_denoteScalar x)

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxLetFlatten
