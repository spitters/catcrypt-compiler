/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering

/-!
# VectorDialect consumer demo — ChaCha 4-way packed `add`

A worked example showing that one *kernel step* of the existing ChaCha
4-way primitive (the lane-parallel `#VPADD_4u32` that adds four 32-bit
state words in parallel) is expressible in the new VectorDialect *and*
proven equivalent to the abstract vector denotation.

This **validates that the dialect is expressive enough** for SIMD kernels
that today are hand-emitted as inline jasmin mnemonics in
`VIR/ChaChaEmit.lean` (cf. `chacha4way_has_packed_add` —
`strContains "#VPADD_4u32("`). We do *not* rewrite the emit; we only show
the equivalence to anchor the claim that a future Phase-2 rewrite will be
denotation-preserving.

The consumer-side specification of the ChaCha 4-way `add` step is the
**lane-map of scalar `BitVec 32 ·+·`**: at each of 4 lanes, add the two
input words. We show this is `VectorOp.add` applied to two
`VectorTy (BitVec 32) 4` operands, and that both the abstract denotation
and the lowered `ScalarExpansion` agree with the lane-map.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ConsumerDemo

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## The kernel step

A ChaCha state word is `BitVec 32`. Four lanes (= one AVX `__m128i`,
emitted as `#VPADD_4u32` in `ChaChaEmit.lean`) is `VectorTy (BitVec 32) 4`. -/

/-- The element type of a ChaCha lane. -/
abbrev W32 := BitVec 32

/-- AVX 4-way carrier: 4 parallel 32-bit words. -/
abbrev W32x4 := VectorTy W32 4

/-- The consumer's spec for the kernel step: lane-wise `+` on two
    4-lane state-word vectors. This is the meaning of `#VPADD_4u32(a, b)`
    in jasmin and the matching `laneMap (· + ·) a b` in the existing
    ChaCha 4-way proof. -/
def vpadd4u32_spec (a b : W32x4) : W32x4 := fun i => a i + b i

/-! ## The VectorDialect rendering

The same step rendered as a single `VectorOp.add` (the carrier-polymorphic
abstract op from `Ops.lean`), with the per-lane operator instantiated as
`HAdd.hAdd` on `BitVec 32`. -/

/-- The kernel step as a `VectorOp`. -/
def vpadd4u32_vectorOp (a b : W32x4) : VectorOp W32 4 :=
  .add (fun x y => x + y) a b

/-! ## Equivalence — abstract denotation -/

/-- **Abstract = consumer spec.** The VectorDialect abstract denotation of
    `vpadd4u32_vectorOp a b` is the consumer's `vpadd4u32_spec a b`. -/
theorem vpadd4u32_abstract_eq (a b : W32x4) :
    denoteVectorOp (vpadd4u32_vectorOp a b)
      = VectorOp.Result.vec (vpadd4u32_spec a b) := by
  show VectorOp.Result.vec (VectorTy.map₂ (fun x y => x + y) a b)
       = VectorOp.Result.vec _
  rfl

/-! ## Equivalence — lowered IR -/

/-- The default lane initialiser the lowering uses (any value works because
    every lane is overwritten by the per-lane stores). -/
def initW32 : W32 := 0

/-- **Lowered = abstract = consumer spec.** The VectorDialect *lowered*
    expansion of `vpadd4u32_vectorOp a b` denotes to `vpadd4u32_spec a b`.

    This is the keystone for the rewrite "rewrite the ChaCha 4-way kernel
    step to a VectorDialect op". Combined with `vpadd4u32_abstract_eq`, the
    rewrite is denotation-preserving on both sides. -/
theorem vpadd4u32_lowered_eq (a b : W32x4) :
    VectorOp.Result.vec (loweredAdd initW32 (fun x y => x + y) a b).denote
      = VectorOp.Result.vec (vpadd4u32_spec a b) := by
  rw [← denoteVectorOp_eq_lower_add initW32 (fun x y => x + y) a b]
  exact vpadd4u32_abstract_eq a b

/-! ## Conclusion — the dialect is expressive enough for the kernel

If a Phase-2 rewrite replaces

```
chacha20_4way_block { … #VPADD_4u32(a, b) … }
```

in `ChaChaEmit.lean` with

```
chacha20_4way_block_vectorDialect { … VectorOp.add (· + ·) a b … }
```

then `vpadd4u32_abstract_eq` (abstract denotation = spec) and
`vpadd4u32_lowered_eq` (lowered IR = spec) prove the step preserves
meaning. The existing `chacha4way_denotation_preserves` theorem in
`ChaChaEmit.lean` then carries through unchanged.

This is exactly the "vector op = elementwise scalar op" justification a
correct progressive SIMD lowering needs — discharged here for the
ChaCha-shaped step, but with no element-type or lane-count assumptions
beyond what `BitVec`-bearing `Add` already provides.
-/

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ConsumerDemo
