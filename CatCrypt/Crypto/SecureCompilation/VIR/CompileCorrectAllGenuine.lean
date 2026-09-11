/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectBaseAlu

/-!
# `compile_correct_all_genuine`: cross-arch correctness over a genuine `exec`

One `GenuineModelChoice`-parametric compiler-correctness keystone whose machine
`exec` is the per-arch block executor for every choice — `runRBlock64` for
RISC-V, `runBBlock` for ARM — over the shared scalar register route
(`comToRegProg`). For a base-ALU all-`reg 64` `Com`, reading the result register
out of the model's execution of the compiled-and-lowered block on the encoded
input state equals the source `Com.denote`.

## Scope

* The choices are the ISAs with a block executor over the shared `comToRegProg`
  route: RISC-V (`runRBlock64`) and ARM (`runBBlock`). x86 has no base-ALU
  register-block executor over that route (`X86Backend.runXBlock` is the SIMD
  `XInst` executor); x86 whole-function execution is `runProg` on the lattice
  route (`compile_correct_all`).
* Fragment: base-ALU (ADD/SUB/AND/OR/XOR), the fragment the underlying keystones
  `compile_correct_riscv` / `compile_correct_arm` cover. Grounding depths:
  RISC-V value-level Sail `execute_RTYPE`; ARM decode-round-trip + differential
  (no in-tree `sail-arm` execute). Dispatches to those keystones
  (`CompileCorrectBaseAlu`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectAllGenuine

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLsem
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Compiler (MachineModel)
open CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectBaseAlu

/-! ## 1. The genuine-exec model choices and selector

The cross-arch choices that carry a genuine block executor over the shared
`comToRegProg` route. Unlike `Compiler.ModelChoice`, every constructor here
maps to a model whose `exec` is non-`id`. -/

/-- The ISAs with a genuine base-ALU block executor over the shared scalar
    register route (`comToRegProg`): RISC-V and ARM. -/
inductive GenuineModelChoice where
  /-- RISC-V — `exec = runRBlock64`, value-level Sail `execute_RTYPE` grounding. -/
  | riscv : GenuineModelChoice
  /-- ARM (AArch64) — `exec = runBBlock`, decode-round-trip grounding. -/
  | arm : GenuineModelChoice

/-- The `MachineModel` for a genuine choice — `riscvBaseAluModel` /
    `armBaseAluModel`, each with a **non-`id`** `exec` (`runRBlock64` /
    `runBBlock`), unlike `Compiler.chosenModel` which is `latticeModel`
    (`exec = id`) for every choice. -/
def genuineModel : GenuineModelChoice → MachineModel
  | .riscv => riscvBaseAluModel
  | .arm => armBaseAluModel

/-- The compiled-and-lowered base-ALU block for a choice (the model `Code`):
    `lowerRBlock64 ∘ regToROp ∘ comToRegProg` for RISC-V,
    `armBlockOf ∘ comToRegProg` for ARM. -/
def genuineCode {Γ : Ctxt jasminDialect} (com : Com jasminDialect Γ (.reg 64)) :
    (choice : GenuineModelChoice) → (genuineModel choice).Code
  | .riscv => lowerRBlock64 (regToROp (comToRegProg com Γ.length))
  | .arm => armBlockOf (comToRegProg com Γ.length)

/-- The encoded input state for a choice (`encodeIn` is `id`, so the value
    carrier *is* the input state): the register file is the reflected
    valuation `envOf Γ.length V`. -/
def genuineEncode {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    (choice : GenuineModelChoice) → (genuineModel choice).Value
  | .riscv => encodeRiscvState V
  | .arm => encodeArmState V

/-- Read the result register out of a final state (the `regs` read-back the
    keystones use). -/
def genuineReadReg :
    (choice : GenuineModelChoice) → (genuineModel choice).Value → String → BitVec 64
  | .riscv, s, n => s.regs n
  | .arm, s, n => s.regs n

/-! ## 2. The cross-arch keystone over a genuine `exec` -/

/-- **`compile_correct_all_genuine` — one cross-arch compiler-correctness
    keystone whose `exec` is genuine (non-`id`) for *every* choice.**

    For a base-ALU all-`reg 64` `Com` and any `choice : GenuineModelChoice`,
    reading the result register out of the model's **execution** of the
    compiled-and-lowered block on the encoded input state —
    `genuineReadReg choice (M.decodeOut (M.exec (genuineCode com) (M.encodeIn (genuineEncode V))))` —
    equals the source `Com.denote com V`, where `M.exec` is the genuine
    `runRBlock64` (RISC-V) / `runBBlock` (ARM) block fold, **not** the
    `latticeModel` identity.

    This is the cross-arch genuine-`exec` statement `compile_correct_all` lacks
    (there `exec = id` for every arm and the RISC-V/ARM arms reuse the x86
    run-output). Proved by dispatching to the per-arch keystones
    `compile_correct_riscv` / `compile_correct_arm`. -/
theorem compile_correct_all_genuine {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (choice : GenuineModelChoice) :
    genuineReadReg choice
        ((genuineModel choice).decodeOut
          ((genuineModel choice).exec (genuineCode com choice)
            ((genuineModel choice).encodeIn (genuineEncode V choice))))
        (comRetName com Γ.length)
      = Com.denote com V := by
  cases choice with
  | riscv => exact (compile_correct_riscv hba hΓ V).1
  | arm => exact (compile_correct_arm hba hΓ V).1

/-! ## 3. The `exec` is genuinely non-`id` for every choice (load-bearing) -/

/-- The RISC-V arm's `exec` is the genuine `runRBlock64` fold — NOT
    `latticeModel`'s `fun _ s => s`. -/
theorem genuineModel_exec_riscv_nonid (code : List RInst64) (s : RState64) :
    (genuineModel .riscv).exec code s = runRBlock64 s code := rfl

/-- The ARM arm's `exec` is the genuine `runBBlock` fold — NOT
    `latticeModel`'s `fun _ s => s`. -/
theorem genuineModel_exec_arm_nonid (code : List BInst) (s : BState) :
    (genuineModel .arm).exec code s = runBBlock s code := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectAllGenuine
