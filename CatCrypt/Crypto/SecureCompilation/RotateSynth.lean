/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Init.Data.BitVec.Lemmas

set_option autoImplicit false

/-!
# Rotate synthesis identity for the ARX emit kernels

The supported `Com` alphabet has no rotate `SupportedOp`, so a left-rotate by `n` is
synthesised from `shlImm`/`shrImm`/`or` as `(x <<< n) ||| (x >>> (w - n))`. The value
specs of every ARX kernel (Threefish MIX, SipHash, Speck, variable-shift ChaCha/BLAKE)
must certify that this shift-or form equals `BitVec.rotateLeft`.

Rather than re-derive that identity with a per-kernel `bv_decide` (one SAT call each,
several seconds apiece), factor it once here. `BitVec.rotateLeft_def` already states
`x.rotateLeft r = (x <<< (r % w)) ||| (x >>> (w - r % w))`; for a rotation amount below
the width the `r % w` collapses, so the identity is pure rewriting — no `bv_decide`. -/

namespace CatCrypt.Crypto.SecureCompilation.RotateSynth

set_option linter.unusedVariables false in
/-- **Rotate-left synthesis (width 64).** For `0 < n < 64`, the shift-or form emitted from
    the `shlImm`/`shrImm`/`or` alphabet equals `BitVec.rotateLeft`. Certified by rewriting
    with `BitVec.rotateLeft_def` (no `bv_decide`); reused by every u64 ARX kernel. The
    `0 < n` hypothesis is carried for the caller's rotation-constant discharge; only
    `n < 64` is needed for the `n % 64` collapse. -/
theorem rotl_synth (x : BitVec 64) (n : Nat) (hn : 0 < n) (hn' : n < 64) :
    (x <<< n) ||| (x >>> (64 - n)) = x.rotateLeft n := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn']

set_option linter.unusedVariables false in
/-- **Rotate-right synthesis (width 64).** For `0 < n < 64`, the shift-or form emitted from
    the `shrImm`/`shlImm`/`or` alphabet equals `BitVec.rotateRight`. Certified by rewriting
    with `BitVec.rotateRight_def` (no `bv_decide`); reused by the SPECK right-rotate. Same
    shape as `rotl_synth` with the shift directions swapped. -/
theorem rotr_synth (x : BitVec 64) (n : Nat) (hn : 0 < n) (hn' : n < 64) :
    (x >>> n) ||| (x <<< (64 - n)) = x.rotateRight n := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn']

end CatCrypt.Crypto.SecureCompilation.RotateSynth
