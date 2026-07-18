/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLin
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64

/-!
# `Com → RISC-V (RV64)`: the RV64 `ScalarTarget` instance

The RV64 instance of the shared `ScalarLin` waist — the SAME source IR the
AArch64 backend consumes, with its own instruction selection `RegStmt → ROp64`.
The whole-program keystone (`regToROp_denote`) comes from the generic
`ScalarTarget.compile_denote`, exactly as for AArch64: *one keystone, instantiated
per ISA*, not copy-pasted.

## Selectable subset

`RvOk` marks the `RegStmt`s the RV64 backend selects: the binary ALU ops, `umulh`,
`mov`, `movz`, the immediate logical shifts (`shrI`/`shlI`, lowered to `srli`/`slli`),
and the backend-neutral `loadImm` (lowered to RV64's full-width `li`). The one
non-selectable `RegStmt` is the ARM-specific `movk` (the front emits `loadImm`
instead), on which `evalRegStmtRV` is the identity.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-- The RV64-selectable subset of `RegStmt`. -/
def RvOk : RegStmt → Bool
  | .movk .. => false
  | _ => true

/-- Instruction selection `RegStmt → ROp64`. ALU ops map 1:1 (`orr→or`,
    `eor→xor`, `umulh→mulhu`); `movz`/`loadImm` become a `li`, the immediate shifts
    become `srli`/`slli`. Only the ARM-specific `movk` has no expansion (empty,
    unreachable under `RvOk` — the front emits `loadImm`). -/
def regStmtToROp : RegStmt → List ROp64
  | .add d a b => [.add d a b]
  | .sub d a b => [.sub d a b]
  | .mul d a b => [.mul d a b]
  | .and d a b => [.and d a b]
  | .orr d a b => [.or d a b]
  | .eor d a b => [.xor d a b]
  | .umulh d a b => [.mulhu d a b]
  | .mov d a => [.mov d a]
  | .movz d i => [.li d (i % 0x10000)]
  | .loadImm d n => [.li d n]
  | .shrI d a i => [.srli d a i]
  | .shlI d a i => [.slli d a i]
  | .movk .. => []

/-- The RV64 source effect of a statement (matching `evalRInst64` arm-for-arm;
    identity on the one unselectable arm, the ARM-specific `movk`). -/
def evalRegStmtRV (s : RState64) : RegStmt → RState64
  | .add d a b => s.set d (opAdd64 (s.get a) (s.get b))
  | .sub d a b => s.set d (opSub64 (s.get a) (s.get b))
  | .mul d a b => s.set d (opMul64 (s.get a) (s.get b))
  | .and d a b => s.set d (opAnd64 (s.get a) (s.get b))
  | .orr d a b => s.set d (opOr64 (s.get a) (s.get b))
  | .eor d a b => s.set d (opXor64 (s.get a) (s.get b))
  | .umulh d a b => s.set d (opMulhu (s.get a) (s.get b))
  | .mov d a => s.set d (s.get a)
  | .movz d i => s.set d (BitVec.ofNat 64 (i % 0x10000))
  | .loadImm d n => s.set d (BitVec.ofNat 64 n)
  | .shrI d a i => s.set d (s.get a >>> i)
  | .shlI d a i => s.set d (s.get a <<< i)
  | .movk .. => s

/-- Per-statement selection correctness (all arms, by definitional unfolding). -/
theorem regStmtToROp_denote (s : RState64) (stmt : RegStmt) :
    (regStmtToROp stmt).foldl (fun st op => runRBlock64 st (toRInst64 op)) s
      = evalRegStmtRV s stmt := by
  cases stmt <;> rfl

/-- The RV64 backend as a `ScalarTarget`. -/
def rvTarget : ScalarTarget where
  Op := ROp64
  St := RState64
  runOps s ops := ops.foldl (fun st op => runRBlock64 st (toRInst64 op)) s
  runOps_nil _ := rfl
  runOps_append xs ys s := by simp only [List.foldl_append]
  step := evalRegStmtRV
  toOps := regStmtToROp
  select_correct s stmt := regStmtToROp_denote s stmt

/-- Compile a program to an `ROp64` block. -/
def regToROp (p : RegProg) : List ROp64 := rvTarget.compile p

/-- **RV64 keystone** (the RV64 instance of `ScalarTarget.compile_denote`). -/
theorem regToROp_denote (p : RegProg) (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp p)) = rvTarget.denote p s := by
  rw [riscvBlock64_lowering_denote]
  exact rvTarget.compile_denote p s

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
