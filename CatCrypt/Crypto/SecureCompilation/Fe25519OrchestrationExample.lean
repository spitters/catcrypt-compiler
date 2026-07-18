/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT
import CatCrypt.Crypto.SecureCompilation.Fe25519AddLeafGoldenPath
import CatCrypt.Crypto.SecureCompilation.Fe25519MulLeafGoldenPath

/-!
# Worked example: Rust orchestrating jasmin-like fe25519 leaves

This file demonstrates the two-layer split that the CatCrypt compiler embodies:

* an **orchestration layer** — a `LowCT` program (the *covered* constant-time
  fragment: bounded loops, leaf calls, scalar index arithmetic) that stitches
  together field-op leaves. This is the "Rust" side: control flow the borrow
  checker certifies, no register scheduling.
* a **leaf layer** — the fe25519 field operations as word-level
  `Com jasminDialect` kernels (`Fe25519AddLeafGoldenPath.fe25519Add51LimbCom`,
  `Fe25519MulLeafGoldenPath.fe25519MacColLoCom`). This is the "jasmin-like"
  side: the `MULX`/`ADCX`/`ADOX` schedule, generated through the verified front,
  never hand-authored.

The `LowCT` leaf calls name their leaves by string (`"fe25519_mul"`,
`"fe25519_add"`); at the dialect level each name becomes a
`JasminOp.extCall name argTys retTy` node, which the MLIR lowering maps to
`func.call`. §3 makes that correspondence concrete and proves the `extCall` node
denotes exactly the real add leaf.

## What is built (0 sorries, no `native_decide`, no new axioms)

* `macAccumulate` — a `mac_accumulate`-style orchestration: an `RFor` loop whose
  body multiplies two field elements (`RCallN "fe25519_mul"`) then adds the
  product into an accumulator (`RCall "fe25519_add"`). The canonical
  "Rust orchestrates jasmin leaves" shape, over the *real* fe25519 leaves.
* `fe25519AddExtCallCom` + `fe25519AddExtCall_denote_opaque` — the `"fe25519_add"`
  leaf name realised as a `JasminOp.extCall` node, opaque at the dialect level
  (`jasminExtSem` default); the tie to the golden-path leaf `fe25519Add51LimbCom`
  routes through the `FuncRegistryN` inlining registry, not `jasminExtSem` (the
  leaf-call ↔ `func.call` correspondence).
* `macAccumulate_shape` — a structural read-back of the loop body, witnessing
  the mul-then-add orchestration shape as a definitional identity.

The concrete-syntax prototype (the ergonomic layer over this AST) lives in the
companion `Fe25519OrchestrationSyntax.lean`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Fe25519AddLeaf (fe25519Add51LimbCom)

/-! ## 1. The orchestration-layer slots

Every slot the orchestration threads is a Curve25519 base-field element
(`TowerType.TFp25519`, the radix-2⁵¹ representation the leaves compute over).
`fieldLoc name` is the `Located` for a field-typed slot named `name`. -/

/-- A field-element slot named `name` (Curve25519 base field, radix 2⁵¹). -/
def fieldLoc (name : String) : Located := ⟨name, .TFp25519⟩

/-- The accumulator slot. -/
def accLoc : Located := fieldLoc "acc"

/-- The per-iteration product scratch slot. -/
def prodLoc : Located := fieldLoc "p"

/-- The `i`-th multiplicand input slots (bound by the surrounding harness). -/
def aiLoc : Located := fieldLoc "a_i"
def biLoc : Located := fieldLoc "b_i"

/-! ## 2. The `mac_accumulate` orchestration over the real leaves

`macAccumulate n` runs, for `i = 0 … n-1`:

```text
  p   := fe25519_mul(a_i, b_i)    -- RCallN: multi-dest leaf call, one dest `p`
  acc := fe25519_add(p)           -- RCall:  acc += p (dst-accumulating add)
```

`RCallN "fe25519_mul" [p] [a_i, b_i]` is the multiply leaf call (`Phase G`
N-output call shape — one destination here); `RCall "fe25519_add" acc [p]`
accumulates the product into `acc`. Both leaf names resolve to `extCall`
nodes at the dialect level (§3). The loop is a structurally-terminating `RFor`,
so no fuel/termination side condition is needed — the covered fragment. -/

/-- One loop-body: `p := fe25519_mul(a_i, b_i) ; acc := fe25519_add(p)`. -/
def macBody : LowCT :=
  .RSeq
    (.RCallN "fe25519_mul" [prodLoc] [aiLoc, biLoc])
    (.RCall "fe25519_add" accLoc [prodLoc])

/-- The `mac_accumulate` orchestration: `for i in 0..n { <macBody> }`. -/
def macAccumulate (n : Nat) : LowCT :=
  .RFor "i" n macBody

/-- **The orchestration shape, definitionally.** `macAccumulate n` is exactly an
    `RFor` over the mul-then-add body — the Rust-orchestration + jasmin-leaf
    shape, read back as a `rfl` identity. -/
theorem macAccumulate_shape (n : Nat) :
    macAccumulate n =
      .RFor "i" n
        (.RSeq
          (.RCallN "fe25519_mul" [⟨"p", .TFp25519⟩] [⟨"a_i", .TFp25519⟩, ⟨"b_i", .TFp25519⟩])
          (.RCall "fe25519_add" ⟨"acc", .TFp25519⟩ [⟨"p", .TFp25519⟩])) := rfl

/-! ## 3. The leaf-call ↔ `extCall` (`func.call`) correspondence

At the dialect level the leaf name `"fe25519_add"` in the `LowCT` call becomes a
`JasminOp.extCall "fe25519_add" [stackArr 64 5, stackArr 64 5, reg 64] (reg 64)`
node — the signature of the radix-2⁵¹ per-limb add leaf `(A, B, i) ↦ A[i] + B[i]`.
`jasminExtSem` treats every non-lattice leaf as OPAQUE (`JasminTy.default`) — the
invariant that keeps dialect correctness (`DialectToJasminComCorrect`, `JasminValTransport`)
clean; only the width-16 `stackArr` lattice leaves are non-default. The tie between the
`extCall` node and the front-generated golden-path leaf `fe25519Add51LimbCom` therefore does
NOT live in `jasminExtSem`; it routes through `ComInlineCall`'s `FuncRegistryN`/
`RegistryConsistentN` registry — the named-call inlining path — which supplies the leaf `Com`
for `"fe25519_add"` at a call site. -/

/-- The `"fe25519_add"` leaf realised as a single `extCall` node over
    `[A : stackArr 64 5, B : stackArr 64 5, i : reg 64]`: the dialect image of
    the `LowCT` `RCall "fe25519_add" …`. Args in de Bruijn order `A, B, i`. -/
def fe25519AddExtCallCom :
    Com jasminDialect [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64) :=
  .var { op := .extCall "fe25519_add" [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64),
         retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)) }
    (.ret .here)

/-- **The `extCall` node is opaque at the dialect level** — `rfl`. `jasminExtSem` returns the
    default for `"fe25519_add"` (a non-lattice leaf), so the node denotes `JasminTy.default`.
    The node's real semantics — that it computes the front-generated leaf
    `fe25519Add51LimbCom`'s `A[i] + B[i]` — are supplied when the named call is INLINED against
    that leaf `Com` via the `FuncRegistryN` registry. That is the load-bearing tie, kept out of
    `jasminExtSem` so the dialect-correctness invariants (`jasminExtSem_reg`/`_stackArr64`) hold. -/
theorem fe25519AddExtCall_denote_opaque (a b : Fin 5 → BitVec 64) (i : BitVec 64) :
    Com.denote fe25519AddExtCallCom (.cons a (.cons b (.cons i .nil)))
      = JasminTy.default (.reg 64) := rfl

end CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample
