/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.RustSemantics.Encode

/-!
# Width-tagged casts: runtime against Aeneas

The cast names of the leaf audit's section 2.3, now three width-and-sign-tagged
families rather than one: the printer emits `cast#w` (bare digits) for a cast to
an unsigned type from an unsigned or non-integer source, `cast#u<w>` for a cast
to an unsigned type from a *signed* source, and `cast#i<w>` for any cast to a
signed type (`HaxAdapter`'s `castTag?`), rendered `Hax.castVal_w w`,
`Hax.cast_uw w` and `Hax.cast_iw w` respectively.

## Main results

| runtime name | Aeneas operation | class | theorem |
|---|---|---|---|
| `cast#w` | `UScalar.cast` (unsigned to unsigned) | 1 | `cast_u_square` |
| `cast#u<w>` | `IScalar.hcast` (signed to unsigned) | 1 | `cast_iu_square` |
| `cast#i<w>` | `IScalar.cast` (signed to signed) | 1 | `cast_ii_square` |
| `cast#i<w>` | `UScalar.hcast` (unsigned to signed) | 1 | `cast_ui_square` |

`cast_ii_square` and `cast_ui_square` both target `Hax.cast_iw`, the runtime
operation for every cast to a signed type regardless of the source's sign.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Transfer.Param

/-- A cast between unsigned types agrees with the runtime `Hax.castVal_w` at the
    target width. -/
theorem cast_u_square {src : UScalarTy} (tgt : UScalarTy) (x : UScalar src) :
    RCompOk EncRel (lift (UScalar.cast tgt x))
      (pure (Hax.castVal_w tgt.numBits (enc x)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv.zeroExtend tgt.numBits).toNat : Int) = Hax.castVal_w _ (x.bv.toNat : Int)
  simp [Hax.castVal_w, Hax.mod2w]

/-- A signed-to-unsigned cast agrees with `Hax.cast_uw` at the target width: the
    residue of the source's signed value modulo `2^w` is its unsigned bit
    pattern under sign extension. -/
theorem cast_iu_square {src : IScalarTy} (tgt : UScalarTy) (x : IScalar src) :
    RCompOk EncRel (lift (IScalar.hcast tgt x))
      (pure (Hax.cast_uw tgt.numBits (enc x)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv.signExtend tgt.numBits).toNat : Int) = Hax.cast_uw tgt.numBits x.val
  show ((x.bv.signExtend tgt.numBits).toNat : Int) = x.bv.toInt % ((2 ^ tgt.numBits : Nat) : Int)
  rw [toNat_eq_toInt_emod, BitVec.toInt_signExtend]
  rcases Nat.le_total tgt.numBits src.numBits with hle | hle
  · rw [Nat.min_eq_left hle, Int.bmod_emod]
  · rw [Nat.min_eq_right hle,
      bmod_self_eq (Nat.one_le_iff_ne_zero.mpr src.numBits_nonzero) x.bv]

/-- A cast between signed types agrees with `Hax.cast_iw` at the target width:
    sign extension truncates to the target width's two's-complement range,
    which is exactly what `Hax.cast_iw` computes on the source's value. -/
theorem cast_ii_square {src tgt : IScalarTy} (x : IScalar src) :
    RCompOk EncRel (lift (IScalar.cast tgt x))
      (pure (Hax.cast_iw tgt.numBits (enc x)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv.signExtend tgt.numBits).toInt = Hax.cast_iw tgt.numBits x.val
  show (x.bv.signExtend tgt.numBits).toInt = Hax.smod2w tgt.numBits x.bv.toInt
  rw [BitVec.toInt_signExtend]
  rcases Nat.le_total tgt.numBits src.numBits with hle | hle
  · rw [Nat.min_eq_left hle, Hax.smod2w]
  · rw [Nat.min_eq_right hle,
      smod2w_eq_self_of_ge (Nat.one_le_iff_ne_zero.mpr src.numBits_nonzero) hle]
    have h2 := smod2w_eq_self_of_ge (Nat.one_le_iff_ne_zero.mpr src.numBits_nonzero)
      (Nat.le_refl src.numBits) x.bv
    rwa [Hax.smod2w] at h2

/-- An unsigned-to-signed cast agrees with `Hax.cast_iw` at the target width:
    zero extension followed by the two's-complement reading is exactly the
    residue `Hax.cast_iw` computes on the source's (nonnegative) value. -/
theorem cast_ui_square {src : UScalarTy} (tgt : IScalarTy) (x : UScalar src) :
    RCompOk EncRel (lift (UScalar.hcast tgt x))
      (pure (Hax.cast_iw tgt.numBits (enc x)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv.zeroExtend tgt.numBits).toInt = Hax.cast_iw tgt.numBits x.val
  show (x.bv.zeroExtend tgt.numBits).toInt = Hax.smod2w tgt.numBits x.bv.toNat
  rw [Hax.smod2w]
  show (BitVec.setWidth tgt.numBits x.bv).toInt = _
  rw [BitVec.toInt_setWidth]

end CatCrypt.Hax.RustSemantics
