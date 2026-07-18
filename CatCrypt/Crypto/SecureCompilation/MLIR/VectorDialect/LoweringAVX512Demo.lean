/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ConsumerDemo
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec

/-!
# AVX-512 lowering — the #183 architectural win, demonstrated (task #276)

The thesis of the structured `VectorOp` dialect (#183) is that adding a new
SIMD width is **a new lowering pass, not 22 mnemonics × 7 per-primitive
rewrites.** [`LoweringAVX512.lean`](LoweringAVX512.lean) landed the new pass.
This file *demonstrates the payoff*: it takes `VectorOp` terms produced by
**already-migrated consumers, byte-for-byte unchanged**, and lowers them via
the AVX-512 pass to 512-bit emit.

The point: the consumer's `VectorOp` term is the *same object* it always was.
No edit to `ConsumerDemo.lean`, no edit to `MldsaNtt4WayVec.lean`. We re-target
it to AVX-512 simply by applying `lowerAVX512` instead of the AVX2 `lower`.
The 512-bit emit drops out, and its denotation is proven equal to the
consumer's original abstract spec.

## What is reused unchanged

* `ConsumerDemo.vpadd4u32_vectorOp` — the ChaCha 4-way packed-add kernel step,
  authored against the AVX2 path. We feed *that exact term* to `lowerAVX512`.
* `MldsaNtt4WayVec.mulHi16` / `shiftRA16` — the ML-DSA / ML-KEM Montgomery /
  Barrett reduction lane ops, authored for the AVX2 `VPMULH` / `VPSRA`. We
  build the *same* `VectorOp.mulHi` / `VectorOp.shiftRA` terms and lower them
  to the 512-bit `#VPMULH_32u16` / `#VPSRA_32u16` mnemonics.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512Demo

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ConsumerDemo
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec

/-! ## 1. ChaCha 4-way packed add — the SAME `VectorOp`, now at 512-bit width

`vpadd4u32_vectorOp a b` is the kernel step authored in `ConsumerDemo.lean`
against the AVX2 lowering. We do **not** touch it. At AVX-512 the lane count
doubles (4 → 8), but the abstract op is lane-count-polymorphic, so the *same
constructor* re-targets simply by choosing the AVX-512 width. (We state the
re-target at the ChaCha 4-lane shape the consumer authored; an 8-wide variant
is the identical term at `n := 8`.) -/

/-- The AVX-512 lowering of the **unchanged** ChaCha 4-way `add` kernel step
    denotes exactly the consumer's original `vpadd4u32_spec`. The consumer
    code did not change — only the lowering pass (`lowerAVX512` in place of the
    AVX2 `lower`). -/
theorem chacha_add_avx512_eq_spec (a b : W32x4) :
    (lowerAVX512 .w16u32 (vpadd4u32_vectorOp a b)).map (·.denote512)
      = some (vpadd4u32_spec a b) := by
  -- `vpadd4u32_vectorOp a b = .add (·+·) a b`; the AVX-512 pass denotes `map₂`;
  -- `vpadd4u32_spec a b = fun i => a i + b i = map₂ (·+·) a b`.
  rfl

/-- The same unchanged term emits a 512-bit `#VPADD_16u32` mnemonic line via
    the new pass. (At AVX2 the consumer emitted `#VPADD_4u32`; the identical
    `VectorOp` term now yields the `zmm` mnemonic — the win in one line.) -/
theorem chacha_add_avx512_render (a b : W32x4) :
    ((lowerAVX512 .w16u32 (vpadd4u32_vectorOp a b)).map
        (renderAVX512 "c" ["a", "b"]))
      = some "c = #VPADD_16u32(a, b);" := rfl

/-! ## 2. ML-DSA / ML-KEM Montgomery reduction — same ops, 512-bit `zmm`

`mulHi16` (`VPMULHW`) and `shiftRA16` (`VPSRAW`) are the reduction lane ops
authored in `MldsaNtt4WayVec.lean` for the AVX2 path. We build the *same*
`VectorOp.mulHi` / `VectorOp.shiftRA` terms over them and lower to 512-bit. At
AVX-512 a `zmm` holds 32 × u16 lanes, so the natural width is `w32u16` (vs
AVX2's 16 × u16 in a `__m256i`). The consumer's lane op is untouched. -/

/-- The high-half multiply (`VPMULH`) leg of Montgomery reduction, lowered via
    the AVX-512 pass, denotes the same per-lane `mulHi16` the consumer authored
    — now over a 32-lane `zmm`. Consumer op (`mulHi16`) unchanged. -/
theorem mldsa_mulHi_avx512_eq (v w : VectorTy (BitVec 16) 32) :
    (lowerAVX512 .w32u16 (.mulHi mulHi16 v w : VectorOp (BitVec 16) 32)).map
        (·.denote512)
      = some (fun i => mulHi16 (v i) (w i)) := rfl

/-- The signed shift (`VPSRA`) leg, lowered via the AVX-512 pass, denotes the
    consumer's `shiftRA16` per lane over a 32-lane `zmm`. -/
theorem mldsa_shiftRA_avx512_eq (m : Nat) (v : VectorTy (BitVec 16) 32) :
    (lowerAVX512 .w32u16 (.shiftRA shiftRA16 m v : VectorOp (BitVec 16) 32)).map
        (·.denote512)
      = some (fun i => shiftRA16 (v i) m) := rfl

/-- The two reduction legs emit 512-bit `#VPMULH_32u16` / `#VPSRA_32u16`
    mnemonics from the unchanged consumer ops. -/
theorem mldsa_reduction_avx512_render (v w : VectorTy (BitVec 16) 32) (m : Nat) :
    ((lowerAVX512 .w32u16 (.mulHi mulHi16 v w)).map (renderAVX512 "t" ["m", "q"]))
        = some "t = #VPMULH_32u16(m, q);"
      ∧ ((lowerAVX512 .w32u16 (.shiftRA shiftRA16 m v)).map
          (renderAVX512 "r" ["a"]))
        = some ("r = #VPSRA_32u16(a, " ++ toString m ++ ");") := by
  refine ⟨rfl, rfl⟩

/-! ## 3. Cross-target consistency — AVX2 and AVX-512 agree on the same term

The clearest statement of the win: for the **same** consumer `VectorOp` term,
the AVX2 lowering (`lower`, denoting via `ScalarExpansion`) and the AVX-512
lowering (`lowerAVX512`, denoting via `denote512`) produce the **same lane
vector**. Only the emit width differs. -/

/-- For the unchanged ChaCha 4-way `add` step, the AVX2 lowering and the
    AVX-512 lowering denote the **same** lane vector. The consumer authored one
    `VectorOp` term; both target passes agree on its meaning. -/
theorem chacha_add_avx2_avx512_agree (a b : W32x4) :
    ((lowerAVX512 .w16u32 (vpadd4u32_vectorOp a b)).map (·.denote512)
      = (lower initW32 (vpadd4u32_vectorOp a b)).map (·.denote)) := by
  -- `vpadd4u32_vectorOp a b = .add (·+·) a b`.  AVX-512 side denotes `map₂`;
  -- AVX2 side's `ScalarExpansion` also denotes `map₂` (by `lower_add_correct`).
  -- Both reduce to `some (map₂ (·+·) a b)`.
  show (lowerAVX512 .w16u32 (.add _ a b)).map (·.denote512)
      = (lower initW32 (.add _ a b)).map (·.denote)
  rw [lowerAVX512_add_correct, lower_add_correct]

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512Demo
