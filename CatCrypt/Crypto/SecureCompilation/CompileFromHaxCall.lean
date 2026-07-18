/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax
import CatCrypt.Crypto.SHA256.Extraction.Sha256_haxpipe

/-!
# Compiling a body that CALLS a helper (SHA-256 σ₀ via inlining)

`CompileFromHaxVerbatim` compiled the *self-contained* verbatim leaf
`Sha256.small_sigma0_impExpr` (its own body). A whole-function hax extraction —
e.g. `sha256_compress` — instead **calls** that leaf: its schedule loop contains
`small_sigma0(index[w, Sub[i,15]])`. The front must inline `small_sigma0`'s
extracted body (formal `x` substituted by the argument) *before* the §10 `anfLift`
and §3 translator see it.

This file is the bounded **call-handling** demo for the §11 `callInline`
pre-pass. The caller is the bare call

```text
callerSrc = small_sigma0(x)
```

over the single input atom `x`. The `callInline` pre-pass (registry `shaReg`,
mapping `small_sigma0 ↦ (["x"], small_sigma0_impExpr)`) replaces it by
`small_sigma0`'s *verbatim* extracted body (still `#32`-tagged, nested-app args),
with the callee's formal `x` substituted by the caller's argument `x`. `anfLift`
(§10) then head-normalizes and flattens it, and the unchanged `compileFromHax`
(C2 ∘ C1) compiles it — value-preserving against the FIPS 180-4 σ₀ formula
`(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`.

## On the caller shape

`callerSrc` is the call in **tail/return position** (`small_sigma0(x)`), not a
`let r = small_sigma0(x); r`. Inlining the latter would land the callee's
let-chain as the RHS of `let r = …`, which the §3 `rhsOf` rejects (a `letBind` is
not a flat `Rhs`) — that is the orthogonal "no nested-let RHS" front limitation,
not a `callInline` gap. The tail-position call inlines to a flat let-chain that
compiles directly, exactly mirroring how `CompileFromHaxVerbatim` feeds the bare
σ₀ body under `["x"]` / `fun _ => x`.

## On the preservation statement

As in `CompileFromHaxVerbatim`, the inlined body is `#32`-tagged with nested-app
arguments, so its *own* `ImpExpr.denoteScalar` is `none`; `anfLift` is what gives
it a denotation. The honest preservation is therefore the demo-specific
`caller_callInline_denoteScalar`: the `anfLift`-ed inlined call denotes to the
FIPS σ₀ value. Routed through `compileFromHax_meets_spec`, this yields
`caller_callInline_compiles` — a body that CALLS a helper compiled correctly by
inlining the callee's verbatim extracted body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxCall

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
    head (e.g. the recognised ALU/shift primitives) is `none`. -/
def shaReg : CallRegistry := fun f => if f = "small_sigma0" then some sigma0Callee else none

/-- The caller body: the bare call `small_sigma0(x)` on the single input atom `x`
    (tail/return position — see the module note on the `let r = …` alternative). -/
def callerSrc : ImpExpr := .app "small_sigma0" [.var "x"]

/-- The inlined-then-ANF-lifted caller body. `callInline` replaces `small_sigma0(x)`
    by the σ₀ verbatim body (formal `x` ↦ argument `x`); `anfLift` then normalizes
    it to the §3 let-normalized atom-arg form. -/
def callerNorm : ImpExpr := anfLift (callInline shaReg 100 callerSrc)

/-- The explicit normal form of `callerNorm`: head-normalized (`#32` tags dropped,
    `Shr → shr`) and flattened — every operator application now has only atom
    arguments, hoisted through fresh `_anf<n>` binders. Identical in shape to
    `CompileFromHaxVerbatim.sigma0Norm` (the call was inlined to the same σ₀ body),
    keeping the callee's leading `let x = x` self-binding. -/
def callerXNorm : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "_anf2" (.app "rotate_right" [.var "x", .lit (.int 7)])
    (.letBind "_anf1" (.app "rotate_right" [.var "x", .lit (.int 18)])
     (.letBind "_anf3" (.app "BitXor" [.var "_anf2", .var "_anf1"])
      (.letBind "_anf0" (.app "shr" [.var "x", .lit (.int 3)])
       (.app "BitXor" [.var "_anf3", .var "_anf0"])))))

/-- `anfLift (callInline shaReg 100 callerSrc)` reduces (definitionally) to the
    explicit `callerXNorm`. Closed-term computation: `rfl`. This is the demo's
    rfl-probe pin — `callInline` inlines the verbatim σ₀ body and `anfLift`
    normalizes it. -/
theorem callerNorm_eq : anfLift (callInline shaReg 100 callerSrc) = callerXNorm := rfl

/-- **The inlined-call body is value-preserving.** Its `denoteScalar` (the §2
    source semantics, parameter `"x"`, single input `I 0 = x`) is exactly the FIPS
    180-4 σ₀ value `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`. The honest preservation
    result for the call: the verbatim callee body inlined into the caller has no
    denotation of its own (it is `#32`-tagged with nested-app args), and `anfLift`
    is what makes it denote — to the σ₀ spec of the call argument. Proved by
    `denoteScalar`-reduction of `callerXNorm`, mirroring
    `anfLift_small_sigma0_denoteScalar`'s simp set. -/
theorem caller_callInline_denoteScalar (x : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 1) ["x"] (fun _ => x)
        (anfLift (callInline shaReg 100 callerSrc)) (fun _ => none)
      = some (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat)) := by
  rw [callerNorm_eq]
  simp only [callerXNorm, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The compile-from-hax pipeline succeeds on the inlined-then-ANF-lifted call. -/
theorem caller_callInline_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift (callInline shaReg 100 callerSrc))).isSome := by native_decide

/-- **A body that CALLS a helper compiles correctly (by inlining the callee).**
    There is a compiled `Com jasminDialect` `c` such that the caller
    `small_sigma0(x)` — a *call* to the σ₀ helper — `callInline`-inlines the
    helper's verbatim extracted body, `anfLift`-compiles to `c`, and for every
    input `x`, `c`'s `BitVec 32` denotation is exactly the FIPS 180-4 σ₀ formula
    `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3)`. The call-handling primitive whole-function
    verbatim compress needs: routes `caller_callInline_denoteScalar` through the
    C3 meta-theorem `compileFromHax_meets_spec` (no fresh compiler proof). -/
theorem caller_callInline_compiles :
    ∃ c, compileFromHax (w := 32) (nIn := 1) ["x"]
           (anfLift (callInline shaReg 100 callerSrc)) = some c ∧
         ∀ (x : BitVec 32),
           c.denote (inputValuation 32 1 (fun _ => x))
             = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  set c := (compileFromHax (w := 32) (nIn := 1) ["x"]
    (anfLift (callInline shaReg 100 callerSrc))).get caller_callInline_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["x"]
      (anfLift (callInline shaReg 100 callerSrc)) = some c := (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["x"] (fun _ => x)
    (anfLift (callInline shaReg 100 callerSrc)) _ hc (caller_callInline_denoteScalar x)

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxCall
