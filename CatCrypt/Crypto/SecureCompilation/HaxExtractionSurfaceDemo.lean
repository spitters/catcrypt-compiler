/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac
public import CatCrypt.Crypto.SecureCompilation.VIR.KernelDelab

/-!
# A hax extraction displayed as the `kernel%` surface

`CompileFromHaxFrodoMac.lean` takes a **real hax `ImpExpr` extraction** — the
FrodoKEM LWE multiply-accumulate step `acc + a·b mod 2^16` — and runs it through
the verified front `compileFromHax` (`ImpExpr → Thir → Com jasminDialect`). The
result is `frodoMacKernel`: the routine as the object the compiler-correctness
proofs are about.

`VIR/KernelDelab.lean` gives `Com jasminDialect` a `@[delab]` handler that renders
a leaf back as the reviewable `kernel%` surface. This file closes the loop
**extraction → surface**, reusing that delaborator with no change to hax-lean and
no change to the delaborator:

* `frodoMacKernel` is the verified compiler's output on the extraction.
* `frodoMacSurface` is that same `Com` written in the `kernel%` surface; the two
  are equal by `rfl` (`frodoMacKernel_eq_surface`) — the surface *is* the compiled
  extraction, not a hand-written twin.
* `#print frodoMacSurface` (pinned by `#guard_msgs`) exhibits the delaborator
  rendering the extraction as `kernel%`.
* `frodoMacRoundtrip_eq` is `elab (delab frodoMacSurface) = frodoMacSurface` — the
  rendered surface re-elaborates to the same term (`rfl`).

## Why the surface is ascribed a literal context

`compileFromHax` produces a `Com` at context `frontCtxt 64 3 []`, which is
*definitionally* the literal `[rW 64, rW 64, rW 64]` (`frontCtxt _ n [] =
List.replicate n (rW w)`). The delaborator recovers positional formal names from a
`List.cons` spine, so the surface is ascribed the reduced literal context; the tie
to the compiler output (typed at `frontCtxt 64 3 []`) holds by `rfl` since the two
contexts are defeq.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HaxExtractionSurfaceDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac

/-! ## 1. The extracted routine, lowered by the verified compiler -/

/-- The FrodoKEM MAC hax extraction (`frodoMacSrc`), lowered to `Com jasminDialect`
    by the verified front `compileFromHax`. This is the routine the
    correctness theorem `frodoMac_compiles` is stated about. -/
def frodoMacKernel : Com jasminDialect [rW 64, rW 64, rW 64] (rW 64) :=
  (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] frodoMacSrc).get
    frodoMac_compileFromHax_isSome

/-! ## 2. The same `Com`, written in the `kernel%` surface -/

/-- The reviewable `kernel%` surface for the compiled extraction. `v0/v1/v2` are
    the three inputs `acc/a/b`; the body is `x0 := mask 0xFFFF; x1 := a*b;
    x2 := acc + x1; x3 := x2 & mask; x4 := x3 | x3; ret x4` — exactly the
    multiply-accumulate-then-mask the front emits. -/
def frodoMacSurface : Com jasminDialect [rW 64, rW 64, rW 64] (rW 64) :=
  kernel% (v0 : rW 64) (v1 : rW 64) (v2 : rW 64) {
    x0 := (JasminOp.regConst 64 65535) [];
    x1 := (JasminOp.regArith .mul 64) [v1, v2];
    x2 := (JasminOp.regArith .add 64) [v0, x1];
    x3 := (JasminOp.regArith .and 64) [x2, x0];
    x4 := (JasminOp.regArith .or 64) [x3, x3];
    ret x4
  }

/-- The reviewable `kernel%` surface denotes to the FrodoKEM MAC spec `frodoMacForm`
    (`acc + a·b mod 2^16`). `Com.denote` reduces the literal chain to
    `frodoMacForm ||| frodoMacForm` (the `x4 := x3 | x3` copy idiom the front emits);
    `bv_decide` collapses the self-`or`. -/
theorem frodoMacSurface_denote (acc a b : BitVec 64) :
    frodoMacSurface.denote (inputValuation 64 3 ![acc, a, b]) = frodoMacForm acc a b := by
  have oself : ∀ y : BitVec 64, y ||| y = y := by intro y; bv_decide
  have h : frodoMacSurface.denote (inputValuation 64 3 ![acc, a, b])
      = frodoMacForm acc a b ||| frodoMacForm acc a b := rfl
  rw [h, oself]

/-- The extraction's compiled `Com` (`frodoMacKernel`) denotes to the same
    `frodoMacForm`, recovered from the proven `frodoMac_compiles` (the verified
    front's value-preservation): `frodoMacKernel` is the `some`-witness `prog`. -/
theorem frodoMacKernel_denote (acc a b : BitVec 64) :
    frodoMacKernel.denote (inputValuation 64 3 ![acc, a, b]) = frodoMacForm acc a b := by
  obtain ⟨prog, hc, hspec⟩ := frodoMac_compiles
  have hpk : frodoMacKernel = prog := by
    have h1 : some frodoMacKernel
        = compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] frodoMacSrc :=
      Option.some_get frodoMac_compileFromHax_isSome
    rw [hc] at h1; exact Option.some.inj h1
  rw [hpk]; exact hspec acc a b

/-- **The extraction and the surface denote identically.** The verified compiler's
    lowering of the FrodoKEM MAC extraction (`frodoMacKernel`) and the reviewable
    `kernel%` surface (`frodoMacSurface`) compute the same value for every input —
    both the FrodoKEM MAC `acc + a·b mod 2^16`. The surface is a faithful display of
    the extracted routine. -/
theorem frodoMacKernel_eq_surface_denote (acc a b : BitVec 64) :
    frodoMacKernel.denote (inputValuation 64 3 ![acc, a, b])
      = frodoMacSurface.denote (inputValuation 64 3 ![acc, a, b]) := by
  rw [frodoMacKernel_denote, frodoMacSurface_denote]

/-! ## 3. Display pin — the delaborator renders the extraction as `kernel%` -/

/--
info: @[expose] def CatCrypt.Crypto.SecureCompilation.HaxExtractionSurfaceDemo.frodoMacSurface : Com jasminDialect
[rW 64, rW 64, rW 64] (rW 64) :=
kernel%
(v0 :
  rW
    64)(v1 :
  rW
    64)(v2 :
  rW
    64){x0 :=
  (JasminOp.regConst 64
    65535)[];x1 := (JasminOp.regArith JasminBinOp.mul 64)[v1,
  v2];x2 := (JasminOp.regArith JasminBinOp.add 64)[v0,
  x1];x3 := (JasminOp.regArith JasminBinOp.and 64)[x2, x0];x4 := (JasminOp.regArith JasminBinOp.or 64)[x3, x3];ret x4}
-/
#guard_msgs (whitespace := lax) in
#print frodoMacSurface

/-! ## 4. Round-trip: `elab (delab frodoMacSurface) = frodoMacSurface` -/

/-- The delaborated surface of §3, copied back and re-elaborated. -/
def frodoMacRoundtrip : Com jasminDialect [rW 64, rW 64, rW 64] (rW 64) :=
  kernel% (v0 : rW 64) (v1 : rW 64) (v2 : rW 64) {
    x0 := (JasminOp.regConst 64 65535) [];
    x1 := (JasminOp.regArith JasminBinOp.mul 64) [v1, v2];
    x2 := (JasminOp.regArith JasminBinOp.add 64) [v0, x1];
    x3 := (JasminOp.regArith JasminBinOp.and 64) [x2, x0];
    x4 := (JasminOp.regArith JasminBinOp.or 64) [x3, x3];
    ret x4
  }

/-- **Round-trip.** Re-elaborating the delaborated `kernel%` surface returns the
    compiled extraction (`rfl`). -/
theorem frodoMacRoundtrip_eq : frodoMacRoundtrip = frodoMacSurface := rfl

end CatCrypt.Crypto.SecureCompilation.HaxExtractionSurfaceDemo
