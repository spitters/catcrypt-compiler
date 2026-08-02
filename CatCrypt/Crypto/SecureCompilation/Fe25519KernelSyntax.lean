/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax
import CatCrypt.Crypto.SecureCompilation.Fe25519MulLeafGoldenPath
import CatCrypt.Crypto.SecureCompilation.Fe25519AddLeafGoldenPath

/-!
# `kernel%` against the deployed fe25519 golden-path leaves

The `kernel%` surface — a named-variable concrete syntax for a straight-line
`Com` leaf — is declared in `VIR/KernelSyntax.lean`, together with its grammar
(`kformal`, `kstmt`) and its dialect-generic elaborator. This module instantiates
that surface at the two **deployed** fe25519 leaves and pins the elaboration by
`rfl`.

A `Com` leaf reads its inputs as typed de-Bruijn `Ctxt.Var`s — `.there (.there
.here)` — a raw index that also carries the proof its slot has the right
`JasminTy`. `kernel%` lets the author name the formals and every let-binding, so
the fe25519 multiply-accumulate column low word reads

```text
  kernel% (acc_lo : .reg 64) (acc_hi : .reg 64) (a : .reg 64) (b : .reg 64) {
    p_lo := (JasminOp.regArith .mul 64) [a, b];
    s    := (JasminOp.regArith .add 64) [acc_lo, p_lo];
    ret s
  }
```

## How the resolution works (the typed symbol table)

The `Com` framework binds each `.var` result at the **front** of the context:
`Com.var (e : Expr d Γ t) (body : Com d (t :: Γ) s)`. So de-Bruijn index `0`
(`Ctxt.Var.here`) is always the most-recently-bound name, and every prior name
shifts one step deeper (`Ctxt.Var.there`). The elaborator mirrors this with a
compile-time **scope** — an `Array Name` whose position `i` is exactly the
de-Bruijn index of that name:

* a formal list seeds the scope in declaration order;
* a let-binding prepends its name (the new binding is de-Bruijn index `0`, every
  existing name shifts up by one);
* a named use resolves to `Ctxt.Var.there^i Ctxt.Var.here` where `i` is the
  name's position in the current scope.

The emitted indices are then checked against the ascribed context `Γ`, so the
intrinsic typing of `Com` supplies exactly the typing proof each `Ctxt.Var`
demands — a wrong index that lands on a wrong-typed slot is a type error, not a
silent bug. The elaborator never manufactures a proof term; it only computes
indices, and the kernel discharges the `JasminTy` obligation.

## What is proved

* `macColKernel_eq_leaf` — the named multiply-accumulate column low word
  elaborates to **exactly** `Fe25519MulLeaf.fe25519MacColLoCom`, by `rfl`.
* `addLimbKernel_eq_leaf` — the named per-limb field add elaborates to **exactly**
  `Fe25519AddLeaf.fe25519Add51LimbCom`, by `rfl`. This one exercises a second op
  (`stackLoad`) and a mixed context (`stackArr` + `reg`), so the resolution is
  shown faithful across ops and types, not just for one shape.

Both are `rfl` against the deployed golden-path leaves — the named notation adds
readability and index-safety with **no new trust**: the elaborated term is
definitionally the hand-authored one.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519KernelSyntax

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## The named notation elaborates to the deployed leaves, by `rfl` -/

/-- The fe25519 multiply-accumulate column low word, in named form. Compare
    `Fe25519MulLeaf.fe25519MacColLoCom`, whose body spells the same wiring as
    `.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)`. -/
def macColKernel : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  kernel% (acc_lo : .reg 64) (acc_hi : .reg 64) (a : .reg 64) (b : .reg 64) {
    p_lo := (JasminOp.regArith .mul 64) [a, b];
    s    := (JasminOp.regArith .add 64) [acc_lo, p_lo];
    ret s
  }

/-- **The elaborator is faithful — `rfl`.** The named multiply-accumulate column
    low word elaborates to **exactly** the hand-authored golden-path leaf; the
    symbol table resolved `a`, `b`, `acc_lo`, `p_lo`, `s` to precisely the
    de-Bruijn indices the hand-written `Com` spells out. -/
theorem macColKernel_eq_leaf :
    macColKernel = Fe25519MulLeaf.fe25519MacColLoCom := rfl

/-- The fe25519 per-limb field add, in named form. Two `stackLoad`s over a mixed
    `stackArr`/`reg` context plus a `regArith .add` — exercises the resolution
    across a second op and heterogeneous slot types. Compare
    `Fe25519AddLeaf.fe25519Add51LimbCom`. -/
def addLimbKernel : Com jasminDialect [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64) :=
  kernel% (A : .stackArr 64 5) (B : .stackArr 64 5) (i : .reg 64) {
    ai := (JasminOp.stackLoad 64 5) [A, i];
    bi := (JasminOp.stackLoad 64 5) [B, i];
    s  := (JasminOp.regArith .add 64) [ai, bi];
    ret s
  }

/-- **The elaborator is faithful across ops and mixed types — `rfl`.** The named
    per-limb field add elaborates to **exactly** `fe25519Add51LimbCom`. `A`, `B`,
    `i` resolve to their `stackArr`/`reg` slots and `ai`, `bi`, `s` to their
    binding indices, matching the hand-written de-Bruijn leaf. -/
theorem addLimbKernel_eq_leaf :
    addLimbKernel = Fe25519AddLeaf.fe25519Add51LimbCom := rfl

end CatCrypt.Crypto.SecureCompilation.Fe25519KernelSyntax
