/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptOpProperties

/-!
# VEIR-shaped `propertiesOf` for `CatCryptOp`

Mirrors VEIR's `Veir/IR/OpInfo.lean` + per-dialect `Veir/Dialects/<X>/OpInfo.lean`
shape so the eventual port to upstream VEIR (post-toolchain-stabilization)
is mechanical.

## Three-layer shape (matches VEIR's)

1. `HasDialectOpInfo` typeclass with a `propertiesOf : Op → Type` slot
   (VEIR-DIFF: stripped down — we drop the `Hashable`/`Repr` plumbing for
   now; add back if the optimizer needs hash-consing).
2. `propertiesOf : CatCryptOp → Type` mapping each op to its property type
   from `CatCryptOpProperties`.
3. `instance : HasDialectOpInfo CatCryptOp` binding the dialect.

## VEIR-DIFF (auditable)

* No `Hashable opCode` / `Repr opCode` extensions on the class.
* No `propertiesHash`/`propertiesRepr`/`propertiesDecideEq` defaulting
  tactics — added when first consumer needs them.
* No `@[properties_of]` attribute (VEIR uses it to drive a defaulting
  `simp only [properties_of]` tactic; we use plain pattern match).

These divergences are intentional: keep VIR small until VEIR upstream
is on a stable toolchain we can `require`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCryptDialect
open CatCryptOpProperties

/-! ## 1. Typeclass -/

/-- VEIR-shaped op-info: assigns each op in `opCode` a property type.
    Stripped down vs upstream — see file docstring for VEIR-DIFF. -/
class HasDialectOpInfo (opCode : Type) where
  propertiesOf : opCode → Type

/-! ## 2. `propertiesOf` for `CatCryptOp`

Each op gets a tuple of the property structures it cares about. Ops
without informative properties default to `Unit`.

For now the buckets are: bit ops (CT + Pure + Linear), BitVec arithmetic
(CT + Pure + Overflow), memory ops (Pure only), extCall (none — semantics
is supplied externally). -/

/-- Property type per `CatCryptOp`. Each row is `(ConstantTime, Pure,
    [Linear|Overflow|Unit])`. -/
def CatCryptOp.propertiesOf : CatCryptOp → Type
  -- Constants: trivially CT + Pure
  | .constBit _ | .constUnit | .bvConst _ _ =>
      ConstantTimeProperties × PureProperties
  -- Bit ops: CT + Pure + Linear (XOR-share commuting where applicable)
  | .xor | .and | .or | .not | .eqBit =>
      ConstantTimeProperties × PureProperties × LinearProperties
  -- BitVec ops: CT + Pure + Overflow (wrap semantics)
  | .bvXor _ | .bvAnd _ | .bvOr _ | .bvNot _
  | .bvAdd _ | .bvSub _ | .bvMul _ | .bvEq _
  | .bvShiftL _ _ | .bvShiftR _ _
  | .bvRor _ _ | .bvRol _ _ | .bvShiftRA _ _ | .andn _
  | .bvShiftLV _ | .bvShiftRV _
  | .bvAdd64 _ | .bvAdc _
  | .bvMulHi _ | .bvAddCarryLo _ | .bvAddCarryHi _ =>
      ConstantTimeProperties × PureProperties × OverflowProperties
  -- Pair/sum constructors and destructors: CT + Pure (no overflow, no linear)
  | .mkPair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _ =>
      ConstantTimeProperties × PureProperties
  -- `ite` is CT iff its condition is a public bit (caller-asserted) — flag CT only.
  | .ite _ => ConstantTimeProperties × PureProperties
  -- `bitToSword n`: CT + Pure + Linear over `BitVec n` GF(2)-sharing
  -- (it's a sign-extension, which is bit-additive). This is the "mask
  -- source" op used by branch-free cmov.
  | .bitToSword _ =>
      ConstantTimeProperties × PureProperties × LinearProperties
  -- Memory ops: Pure (functional store/load semantics) + CT iff index is static
  | .memrefZero _ | .memrefSet _ _ | .memrefGet _ _
  | .memrefSetDyn _ | .memrefGetDyn _ | .memrefGetDyn128 _ =>
      ConstantTimeProperties × PureProperties
  -- External call: properties are external; opaque here.
  | .extCall _ _ _ => Unit
  -- Sampling ops: no representable static property (probabilistic, not pure);
  -- opaque here like `extCall`.
  | .sampleBit | .sampleBv _ => Unit
  -- 128-bit SIMD ops: data-oblivious (fixed lane pattern, no secret-dependent
  -- index or branch), so CT + Pure. Not marked Linear — the GF(2^8) field
  -- multiply / affine / shuffle arms are non-linear over the sharing structure.
  | .vsimd _ | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _ | .vpslldqC _
  | .vconst128 _
  | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2 =>
      ConstantTimeProperties × PureProperties

/-! ## 3. `HasDialectOpInfo` instance for `catCryptDialect` -/

instance : HasDialectOpInfo CatCryptOp where
  propertiesOf := CatCryptOp.propertiesOf

end CatCrypt.Crypto.SecureCompilation.VIR
