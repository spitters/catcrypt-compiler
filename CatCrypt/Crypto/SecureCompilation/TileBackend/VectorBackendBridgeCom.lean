/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The AVX2 128-bit packed-ALU bridge on the UNIFIED `Com jasminDialect`

`VectorBackendBridge.lean` consolidates the bespoke 128-bit x86 vector machine
(`Vec128Model`'s `VInst` / `VState`) onto the shape-generic `Tile 4 32` lane
model. This module is the SIMD-dialect-unification companion for the **x86 leg**:
it re-expresses the bridge's packed two-operand 4×u32 arithmetic core directly as
`Com jasminDialect` programs over `reg 128` XMM registers, off the bespoke
`Vec128Model` machine, using the verified dialect's `JasminOp.vsimd (.packed bop
32)` op (denote `v128PackLanesW 32 bop`, the carry-free 4×u32 packed-lane op).
This mirrors `ZmmArithBridgeCom.lean` (the `Tile 8 64` ZMM companion), which
routes the same packed ops through the `Com jasminDialect` denote chain.

## Which `VInst` ops migrate

`VectorBackendBridge.lean`'s `vinstToReg` maps the cleanly-corresponding
two-operand packed arithmetic onto the `regArith` binop alphabet. Each is a
carry-free 4×u32 packed-lane op, so it maps EXACTLY onto a `vsimd (.packed bop
32)`:

| `VInst`   | lane op (`Vec128Model`) | `JasminBinOp` | denote                  |
|-----------|-------------------------|---------------|-------------------------|
| `vpaddd`  | `a + b` (per lane)      | `.add`        | `v128PackLanesW 32 .add` |
| `vpxor`   | `a ^^^ b` (per lane)    | `.xor`        | `v128PackLanesW 32 .xor` |
| `vpor`    | `a ||| b` (per lane)    | `.or`         | `v128PackLanesW 32 .or`  |

These three are exactly the `vinstToReg`-mapped subset of the x86 bridge. They
migrate in full to `Com jasminDialect` here. (`vpxor`/`vpor` could equally route
through `.bitwise .xor`/`.or` — the whole-128-bit bitwise op — since xor/or
distribute over the lane split; the bridge ties to the tile `.xorr`/`.orr` arm
either way. We use the uniform `packed` op so all three share one builder and one
round-trip lemma.)

## What is proved here

For each migrated op a `Com jasminDialect` program over the input context
`[a, b]` (two `reg 128`) whose single binding is the matching `vsimd (.packed bop
32)`, plus a `rfl`-denote lemma pinning its denotation to `v128PackLanesW 32 bop
a b` — the verified-dialect packed-lane op the bespoke `VInst` computes
lane-by-lane. The denote lemmas elaborate by `rfl`: `Com.denote` of a one-binding
straight-line program unfolds definitionally through the `vsimd (.packed …)`
denote arm to the `v128PackLanesW` call.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridgeCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridgeCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Register type and the two-input context

A single `reg 128` (one XMM 4×u32 lane-vector) is the working type. Each packed
two-operand op consumes two of them, in de-Bruijn order `[a, b]`:

* `a` — first source (de Bruijn `0`, `.here`);
* `b` — second source (de Bruijn `1`, `.there .here`). -/

/-- The `reg 128` dialect type (one XMM 4×u32 lane-vector), abbreviated. -/
abbrev r128 : JasminTy := .reg 128

/-- The two-input context of a packed XMM binop: `[a, b]`, each `reg 128`. -/
abbrev binCtx : Ctxt jasminDialect := [r128, r128]

/-! ## 2. The dialect-native packed-arithmetic programs `Com jasminDialect`

```
let r = vsimd (.packed bop 32) a b      -- r := bop-packed(a, b)
ret r
```

The single binding (`vsimd (.packed bop 32)`) consumes `a` (`.here` in `binCtx`)
and `b` (`.there .here`), producing `r` at the front; the program returns it
(`.here` in the extended context `[r, a, b]`). One generic builder instantiates
all three two-operand ops. -/

/-- Generic one-op packed AVX2 program: `r := (packed bop 32)(a, b); ret r`, over
    the two-input context `[a, b]`. The dialect-native equivalent of one bespoke
    `VInst` packed-arithmetic op. -/
def packAvx2Com (bop : JasminBinOp) : Com jasminDialect binCtx r128 :=
  -- r := vsimd (.packed bop 32) a b   (a = .here, b = .there .here)
  .var (.mk (.vsimd (.packed bop 32)) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The migrated `vpaddd` op as a `Com jasminDialect`: packed 4×u32 add. -/
def vpadddCom : Com jasminDialect binCtx r128 := packAvx2Com .add

/-- The migrated `vpxor` op as a `Com jasminDialect`: packed 4×u32 bitwise xor. -/
def vpxorCom : Com jasminDialect binCtx r128 := packAvx2Com .xor

/-- The migrated `vpor` op as a `Com jasminDialect`: packed 4×u32 bitwise or. -/
def vporCom : Com jasminDialect binCtx r128 := packAvx2Com .or

/-! ## 3. Denotation characterization

Each program computes the verified-dialect packed-lane op `v128PackLanesW 32 bop`,
the 4×u32 packed-lane semantics. The proofs are `rfl`: `Com.denote` of the
one-binding program unfolds definitionally through the `vsimd (.packed …)` denote
arm to the `v128PackLanesW` call. -/

/-- **Generic packed-binop denotation pin.** On any input valuation `⟨a, b⟩`,
    `packAvx2Com bop` denotes to `v128PackLanesW 32 bop a b` — the
    verified-dialect packed 4×u32 op the matching bespoke `VInst` computes
    lane-by-lane. -/
theorem packAvx2Com_denote (bop : JasminBinOp) (a b : BitVec 128) :
    (packAvx2Com bop).denote (.cons a (.cons b .nil)) = v128PackLanesW 32 bop a b :=
  rfl

/-- `vpadddCom` denotes to `v128PackLanesW 32 .add a b` — packed 4×u32 add. -/
theorem vpadddCom_denote (a b : BitVec 128) :
    vpadddCom.denote (.cons a (.cons b .nil)) = v128PackLanesW 32 .add a b := rfl

/-- `vpxorCom` denotes to `v128PackLanesW 32 .xor a b` — packed 4×u32 bitwise xor. -/
theorem vpxorCom_denote (a b : BitVec 128) :
    vpxorCom.denote (.cons a (.cons b .nil)) = v128PackLanesW 32 .xor a b := rfl

/-- `vporCom` denotes to `v128PackLanesW 32 .or a b` — packed 4×u32 bitwise or. -/
theorem vporCom_denote (a b : BitVec 128) :
    vporCom.denote (.cons a (.cons b .nil)) = v128PackLanesW 32 .or a b := rfl

/-! ## 4. The migrated arithmetic core, packaged

All three `vinstToReg`-mapped packed ops of `VectorBackendBridge.lean`'s x86 leg
realized as `Com jasminDialect` programs whose denotations are the
verified-dialect `v128PackLanesW 32` packed-lane ops — the dialect-native form of
the bridge's two-operand x86 arithmetic core. -/

/-- **The migrated AVX2 arithmetic core.** The three bridge-mapped packed ops are
    each realized as a `Com jasminDialect` whose denotation is the corresponding
    verified-dialect `v128PackLanesW 32` op — the SIMD-dialect-unification image
    of `VectorBackendBridge.lean`'s x86 two-operand arithmetic subset. -/
theorem avx2ArithCore_realized (a b : BitVec 128) :
    vpadddCom.denote (.cons a (.cons b .nil)) = v128PackLanesW 32 .add a b ∧
    vpxorCom.denote  (.cons a (.cons b .nil)) = v128PackLanesW 32 .xor a b ∧
    vporCom.denote   (.cons a (.cons b .nil)) = v128PackLanesW 32 .or  a b :=
  ⟨rfl, rfl, rfl⟩

end CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridgeCom
