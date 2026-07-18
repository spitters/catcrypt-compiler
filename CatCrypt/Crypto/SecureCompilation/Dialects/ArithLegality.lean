/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.Arith
import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

set_option autoImplicit false

/-!
# D0: the `SupportedOp` firewall is exactly the lowered `arith` dialect

The MLIR dialect-alignment restructure (D0)
re-points the `ScalarLinDeBruijn.SupportedOp` firewall — the neutral jasmin
fragment the flattening front accepts — onto the new upstream-aligned `arith`
dialect (`Dialects/Arith.lean`). This file discharges the bridge obligation that
makes that re-pointing sound: the `SupportedOp` predicate carves out *precisely*
the width-64 image of `arith` under `ArithOp.toJasmin`.

The headline `supportedOp_iff_arith_image` proves the two op-sets coincide. Its
backward direction gives the corollary `arith_toJasmin_supported`: every `arith`
op at width 64 lowers into the supported jasmin fragment, which is the direction
the firewall actually consumes when it accepts an `arith → jasmin` lowering.

Together with `Arith.toJasmin_sig` / `Arith.toJasmin_ret` (the signature-image
lemmas already in `Dialects/Arith.lean`), this is the op-level half of the D0
legalization contract.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Arith

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn (SupportedOp)

/-! ## The width field of an `arith` op -/

/-- The bit-width `w` carried by every `arith` op. (`SupportedOp` is hard-coded to
    width 64, so this is what the bridge theorem pins down on the `arith` side.) -/
def ArithOp.width : ArithOp → Nat
  | .addi w => w
  | .subi w => w
  | .muli w => w
  | .andi w => w
  | .ori  w => w
  | .xori w => w
  | .mului_extended_hi w => w
  | .shrui_imm w _ => w
  | .shli_imm w _ => w
  | .constant w _ => w

/-! ## The bridge theorem -/

/-- **D0 firewall bridge.** The neutral `SupportedOp` jasmin fragment is *exactly*
    the width-64 image of the `arith` dialect under `ArithOp.toJasmin`: every
    supported jasmin op is the lowering of some width-64 `arith` op, and conversely
    every width-64 `arith` op lowers into the supported fragment. -/
theorem supportedOp_iff_arith_image (op : JasminOp) :
    SupportedOp op ↔ ∃ aop : ArithOp, aop.toJasmin = op ∧ aop.width = 64 := by
  constructor
  · rintro (⟨bop, rfl, hbop⟩ | rfl | ⟨k, (rfl | rfl)⟩ | ⟨k, rfl⟩)
    · rcases hbop with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨.addi 64, rfl, rfl⟩
      · exact ⟨.subi 64, rfl, rfl⟩
      · exact ⟨.muli 64, rfl, rfl⟩
      · exact ⟨.andi 64, rfl, rfl⟩
      · exact ⟨.ori 64, rfl, rfl⟩
      · exact ⟨.xori 64, rfl, rfl⟩
    · exact ⟨.mului_extended_hi 64, rfl, rfl⟩
    · exact ⟨.shrui_imm 64 k, rfl, rfl⟩
    · exact ⟨.shli_imm 64 k, rfl, rfl⟩
    · exact ⟨.constant 64 k, rfl, rfl⟩
  · rintro ⟨aop, rfl, hw⟩
    cases aop with
    | addi w => subst hw; exact SupportedOp.regAdd
    | subi w => subst hw; exact SupportedOp.regSub
    | muli w => subst hw; exact SupportedOp.regMul
    | andi w => subst hw; exact SupportedOp.regAnd
    | ori w => subst hw; exact SupportedOp.regOr
    | xori w => subst hw; exact SupportedOp.regXor
    | mului_extended_hi w => subst hw; exact SupportedOp.mulhi
    | shrui_imm w n => subst hw; exact SupportedOp.shrImm n
    | shli_imm w n => subst hw; exact SupportedOp.shlImm n
    | constant w n => subst hw; exact SupportedOp.regConst n

/-- **The direction the firewall consumes.** Every `arith` op at width 64 lowers
    into the supported jasmin fragment. -/
theorem arith_toJasmin_supported (aop : ArithOp) (hw : aop.width = 64) :
    SupportedOp aop.toJasmin :=
  (supportedOp_iff_arith_image _).2 ⟨aop, rfl, hw⟩

end CatCrypt.Crypto.SecureCompilation.Dialects.Arith
