/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Lowering

/-!
# Semantics preservation for the representative scalar subset

For each modeled two-address arithmetic/logical op, the x86 `step` result in
the destination register equals the source `lprog` op's denotation
`JasminBinOp.apply`, evaluated at the destination (source 0) and the source
operand (source 1). This is the framework-establishing core of the POC:
the lowering preserves the data semantics of the source IR op.

## What is proved here (run `lean_verify` for the axiom set)

* `mov_preserves`        — `MOV`   : result is `src`.
* `add_preserves`        — `ADD`   : `JasminBinOp.add`.
* `sub_preserves`        — `SUB`   : `JasminBinOp.sub`.
* `mul_preserves`        — `MUL`   : `JasminBinOp.mul` (low word).
* `and_preserves`        — `AND`   : `JasminBinOp.and`.
* `or_preserves`         — `OR`    : `JasminBinOp.or`.
* `xor_preserves`        — `XOR`   : `JasminBinOp.xor`.
* `shl_preserves`        — `SHL`   : `JasminBinOp.shl`.
* `shr_preserves`        — `SHR`   : `JasminBinOp.shr`.
* `cmov_preserves`       — `CMOV`  : `if cc then src else dst`.

The five representatives requested by the task (`MOV`, `ADD`, `IMUL`, a shift,
`CMOV`) are covered by `mov_preserves`, `add_preserves`, `mul_preserves`,
`shl_preserves`/`shr_preserves`, `cmov_preserves`; the rest of the modeled ALU
subset is proved for free with the same shape.

`SAR` is **modeled but not proved**: the source `JasminBinOp` carries only the
*logical* right shift `shr`, so there is no `lprog`-level source op for the
arithmetic right shift to be preserved against. Stated explicitly here rather
than hidden.

The ADX/BMI2 trio `MULX`/`ADCX`/`ADOX` likewise has **no `JasminBinOp` source
op** (it is emitted as Jasmin `Copn` intrinsics, not arithmetic `lprog` ops),
so it is not preserved against `JasminBinOp.apply` here. Its data and
flag-routing effects are pinned differentially against Jasmin's `x86_MULX_lo_hi`
/ `x86_ADCX` and stated as all-inputs effect theorems in
`TranslationValidation.lean`, the same way `ADC`/`SBB` are.

## End-to-end form

`lower_then_step_preserves` packages this through the lowering: for any modeled
two-address `Lopn`, `step` of the lowered instruction reads back the
`JasminBinOp.apply` of the source op. The bridge from these per-instruction
facts to a whole-`lcmd` simulation against jasmin's `lsem` is the
`ComLsemExportFaithful[MC]` predicate (`LsemPortAll`), proved over the lsem port
for the modeled straight-line fragments.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

variable {w : Nat} (s : State w) (dst : Reg) (src : Operand)

/-! ## Per-instruction preservation -/

/-- `MOV dst, src` writes `src.eval` into `dst`. -/
theorem mov_preserves : (step s (.mov dst src)).get dst = src.eval s := by
  simp [step, State.get, State.set]

/-- `ADD` realises `JasminBinOp.add` in the destination register (the carry
    flag side effect is separate; see `add_setsCF`). -/
theorem add_preserves :
    (step s (.add dst src)).get dst
      = JasminBinOp.apply .add (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.setALU, State.set]

/-- `SUB` realises `JasminBinOp.sub` in the destination register. -/
theorem sub_preserves :
    (step s (.sub dst src)).get dst
      = JasminBinOp.apply .sub (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.setALU, State.set]

/-- `MUL`/`IMUL` (low word) realises `JasminBinOp.mul`. The low `w` bits of the
    signed and unsigned products agree, so a single arm covers both. -/
theorem mul_preserves :
    (step s (.mul dst src)).get dst
      = JasminBinOp.apply .mul (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.set]

/-- `AND` realises `JasminBinOp.and`. -/
theorem and_preserves :
    (step s (.and_ dst src)).get dst
      = JasminBinOp.apply .and (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.set]

/-- `OR` realises `JasminBinOp.or`. -/
theorem or_preserves :
    (step s (.or_ dst src)).get dst
      = JasminBinOp.apply .or (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.set]

/-- `XOR` realises `JasminBinOp.xor`. -/
theorem xor_preserves :
    (step s (.xor_ dst src)).get dst
      = JasminBinOp.apply .xor (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.set]

/-- `SHL` realises `JasminBinOp.shl` (logical left shift by `src.toNat`). -/
theorem shl_preserves :
    (step s (.shl dst src)).get dst
      = JasminBinOp.apply .shl (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.set]

/-- `SHR` realises `JasminBinOp.shr` (logical right shift by `src.toNat`). -/
theorem shr_preserves :
    (step s (.shr dst src)).get dst
      = JasminBinOp.apply .shr (s.get dst) (src.eval s) := by
  simp [step, JasminBinOp.apply, State.get, State.set]

/-- `CMOVcc dst, src` writes `src` when the condition holds and leaves `dst`
    otherwise — the canonical conditional-move denotation. -/
theorem cmov_preserves (cc : Cond) :
    (step s (.cmov cc dst src)).get dst
      = (if cc.eval s.flags then src.eval s else s.get dst) := by
  simp [step, State.get, State.set]

/-! ## End-to-end through the lowering

For a modeled two-address `Lopn [reg dst] opn [src]`, lowering then stepping
reads back `JasminBinOp.apply` of the source op (for the arithmetic opcodes) or
`src` (for `MOV`). We state the arithmetic case generically over the opcode. -/

/-- The lowering of an arithmetic two-address `Lopn`, stepped, equals the source
    op's `JasminBinOp.apply`. Quantifies over the arithmetic/logical opcodes via
    `binOpName`. The BMI1 `andn` (`binOpName .andn = "ANDN"`) is the
    non-destructive 3-operand VEX form, NOT a single-source two-address `Lopn`,
    so `lowerLinstrR "ANDN" = none` and its `hlow : … = some i` premise is
    vacuous (discharged by `simp at hlow`). -/
theorem lower_arith_step_preserves (bop : JasminBinOp)
    (srcOp : LOperand) (i : Instr w)
    (hsrc : lowerOperand srcOp = src)
    (hlow : lowerLinstrR w (.Lopn [.reg dst] (binOpName bop) [srcOp]) = some i) :
    (step s i).get dst = JasminBinOp.apply bop (s.get dst) (src.eval s) := by
  subst hsrc
  cases bop <;>
    simp only [binOpName, lowerLinstrR, Option.some.injEq] at hlow <;>
    first
      | (subst hlow; simp [step, JasminBinOp.apply, State.get, State.setALU, State.set])
      | simp at hlow

end CatCrypt.Crypto.SecureCompilation.X86Backend
