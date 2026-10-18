/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLsem

/-!
# `compile_correct_baseAlu`: compiler correctness over a block-execution `exec`

This module states the CompCert-shape equation
`decode (model.exec code (encode V)) = source value` for models whose `exec` is a
block-execution semantics: `runRBlock64` for RISC-V and `runBBlock` for ARM.

## Main results

* `compile_correct_baseAlu` — the equation for a `MachineModel` whose value
  carrier is its state.
* `compile_correct_riscv`, `compile_correct_arm` — the equation for
  `riscvBaseAluModel` and `armBaseAluModel` on the base-ALU fragment.

## Carrier

* The model is `riscvBaseAluModel` / `armBaseAluModel`
  (`RISCVBackend/ComToRiscvLsem.lean`, `ARMBackend/ComToArmLsem.lean`), whose
  `exec` is `runRBlock64` / `runBBlock`. Its `validated` field is
  `RiscvBaseAluGrounded` (per-op agreement with a Sail `execute_RTYPE` excerpt)
  for RISC-V and `ArmBaseAluGrounded` (value preservation and GP-ALU coverage)
  for ARM.
* `Code` is the compiled-and-lowered base-ALU block
  `lowerRBlock64 (regToROp (comToRegProg com Γ.length))` (RISC-V) /
  `armBlockOf (comToRegProg com Γ.length)` (ARM).
* `Value`/`State` is the register state `RState64` / `BState`. The model's
  `encodeIn` and `decodeOut` are `id`; the source valuation is encoded by
  `encodeRiscvState` / `encodeArmState`, which build a state with
  `regs = envOf Γ.length V`, and the output is read at the result register
  `comRetName com Γ.length`.

In the conclusion, `model.decodeOut (model.exec code (model.encodeIn V))` read at
`comRetName com Γ.length` equals `Com.denote com V`; the term `model.exec` is the
`runRBlock64`/`runBBlock` fold applied to the encoded input state, so the source
denotation is read from the executed state. The theorems
`comToRiscvLsem_correct` / `comToArmLsem_correct` prove it.

## Scope

The statements assume `ComBaseAlu com` and `AllReg64 Γ`: base-ALU only
(ADD/SUB/AND/OR/XOR on RISC-V, ADD/SUB/AND/ORR/EOR on ARM), the fragment of
`comToRiscvLsem_correct`/`comToArmLsem_correct` and of
`riscvBaseAluModel`/`armBaseAluModel`. The RISC-V model's `validated` field is a
value-level refinement against a Sail `execute_RTYPE` excerpt under register
hypotheses; ARM's is value preservation with GP-ALU coverage, supported outside
the statement by the decode round-trip and differential/qemu testing, with no
in-tree `sail-arm` execute model (see `ComToArmLsem.lean`). This module restates
those two theorems in the `decode∘exec∘encode` shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectBaseAlu

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

/-! ## 1. Encoding a source valuation into the model's input state

`comToRiscvLsem_correct`/`comToArmLsem_correct` run from a state `s` whose
register file is the reflected valuation `envOf Γ.length V`. The models
`riscvBaseAluModel`/`armBaseAluModel` have `encodeIn := id`, so the value carrier
is the input state; the functions below build that state from the valuation. -/

/-- Encode a source valuation `V` into the RISC-V model's input `RState64`:
    the register file is the reflected env `envOf Γ.length V`. By construction
    `(encodeRiscvState V).regs = envOf Γ.length V`, the input hypothesis `hs` of
    `comToRiscvLsem_correct`. -/
def encodeRiscvState {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) : RState64 :=
  { regs := envOf Γ.length V }

@[simp] theorem encodeRiscvState_regs {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) : (encodeRiscvState V).regs = envOf Γ.length V := rfl

/-- Encode a source valuation `V` into the ARM model's input `BState`: the `X`
    register file is the reflected env `envOf Γ.length V` (the carry flag is
    irrelevant to the GP-ALU fragment, taken `false`). By construction
    `(encodeArmState V).regs = envOf Γ.length V`. -/
def encodeArmState {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) : BState :=
  { regs := envOf Γ.length V, cf := false }

@[simp] theorem encodeArmState_regs {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) : (encodeArmState V).regs = envOf Γ.length V := rfl

/-! ## 2. RISC-V: `compile_correct` over `riscvBaseAluModel.exec = runRBlock64`

The CompCert-shape equation with `exec = runRBlock64`. `decodeOut` is `id`; the
output is read at the result register `comRetName`. -/

/-- **`compile_correct_riscv` — compiler correctness for `riscvBaseAluModel`.**
    For a `Com` with `ComBaseAlu com` over a context with `AllReg64 Γ`, the
    model's execution of the compiled-and-lowered block on the encoded input
    state, `model.decodeOut (model.exec code (model.encodeIn V))`, read at the
    result register `comRetName com Γ.length`, equals `Com.denote com V`, and
    every executed `RInst64` is base-ALU (`riscvBlock_all_baseAlu`). For
    base-ALU instructions, `riscvStep64_sail_grounded` relates each step to the
    Sail `execute_RTYPE` excerpt under its register hypotheses; that relation is
    not part of this statement.

    The conclusion runs `model.exec`, which is `runRBlock64` (the `evalRInst64`
    fold). Proved by instantiating
    `comToRiscvLsem_correct`. -/
theorem compile_correct_riscv {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) :
    (riscvBaseAluModel.decodeOut
        (riscvBaseAluModel.exec
          (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))
          (riscvBaseAluModel.encodeIn (encodeRiscvState V)))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsBaseAlu i) := by
  -- `decodeOut`/`encodeIn` are `id`; `exec` is `runRBlock64`.
  show (runRBlock64 (encodeRiscvState V)
          (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsBaseAlu i)
  exact comToRiscvLsem_correct hba hΓ V (encodeRiscvState V) rfl

/-! ## 3. ARM: `compile_correct` over `armBaseAluModel.exec = runBBlock` -/

/-- **`compile_correct_arm` — compiler correctness for `armBaseAluModel`.** The
    AArch64 counterpart of `compile_correct_riscv`: for a `Com` with
    `ComBaseAlu com` over a context with `AllReg64 Γ`, the model's execution
    (`runBBlock`) of the compiled-and-lowered AArch64 block on the encoded input
    state, read at the result register, equals `Com.denote com V`, and every
    executed `BInst` is GP-ALU (`armBlock_all_gpAlu`). Proved by instantiating
    `comToArmLsem_correct`.

    **Trust scope:** the GP-ALU conjunct states membership only. For those
    instructions the package has decode round-trip theorems and external
    differential/qemu testing, and no Sail-execute refinement; ARM has no in-tree
    `sail-arm` execute model (see `ComToArmLsem.lean`). -/
theorem compile_correct_arm {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) :
    (armBaseAluModel.decodeOut
        (armBaseAluModel.exec
          (armBlockOf (comToRegProg com Γ.length))
          (armBaseAluModel.encodeIn (encodeArmState V)))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ armBlockOf (comToRegProg com Γ.length), IsGpAlu i) := by
  -- `decodeOut`/`encodeIn` are `id`; `exec` is `runBBlock`.
  show (runBBlock (encodeArmState V)
          (armBlockOf (comToRegProg com Γ.length))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ armBlockOf (comToRegProg com Γ.length), IsGpAlu i)
  exact comToArmLsem_correct hba hΓ V (encodeArmState V) rfl

/-! ## 4. The parametric `MachineModel`-level statement

Both per-architecture results above are instances of one `MachineModel`-level
CompCert shape: given a model `M` whose `State = Value` (the register state) with
`decodeOut`/`encodeIn` reducing to `id` on the carrier, an input state, and a
value fact about `M.exec` on that state, the equation
`(M.decodeOut (M.exec code (M.encodeIn (enc V)))) read at comRetName = denote`
holds, and its left-hand side runs `M.exec`. `compile_correct_baseAlu` states
this generically; it is instantiated at `riscvBaseAluModel`/`armBaseAluModel`
below, where `M.exec` is `runRBlock64`/`runBBlock`. -/

/-- **`compile_correct_baseAlu` — the `MachineModel`-parametric CompCert shape.**
    Stated for a `MachineModel M` whose value carrier is its state
    (`hVal : Value = State`, as in the base-ALU models, where
    `encodeIn = decodeOut = id`). Given the carrier-identity facts
    (`hEnc`/`hDec`), a register read-back `readReg`, the compiled block `code`,
    an input state `encV`, and the value fact `hKey` (the read-back of
    `M.exec code encV` at `ret` equals `denote`), the CompCert-shape equation
    `readReg (decodeOut (exec code (encodeIn encV))) ret = denote` holds. The
    left-hand side runs `M.exec code (M.encodeIn encV)`; `encodeIn`/`decodeOut`
    only transport along `hVal`. The theorem itself is a rewriting by
    `hEnc`/`hDec`; its content is the hypothesis `hKey`.

    Instantiated at `riscvBaseAluModel` (`M.exec = runRBlock64`, `hKey` from
    `comToRiscvLsem_correct`) and `armBaseAluModel` (`M.exec = runBBlock`, `hKey`
    from `comToArmLsem_correct`); see `compile_correct_baseAlu_riscv`/`_arm`. -/
theorem compile_correct_baseAlu
    (M : MachineModel) (hVal : M.Value = M.State)
    (hEnc : ∀ s : M.State, M.encodeIn (hVal ▸ s) = s)
    (hDec : ∀ s : M.State, (hVal ▸ M.decodeOut s : M.State) = s)
    (readReg : M.State → String → BitVec 64)
    (code : M.Code) (encV : M.State) (ret : String) (denote : BitVec 64)
    (hKey : readReg (M.exec code encV) ret = denote) :
    readReg (hVal ▸ M.decodeOut (M.exec code (M.encodeIn (hVal ▸ encV)))) ret
      = denote := by
  -- `decodeOut`/`encodeIn` are the carrier identities (`hEnc`/`hDec`), so the
  -- CompCert round-trip reduces to `M.exec` of the encoded state.
  rw [hEnc, hDec]
  exact hKey

/-- `compile_correct_baseAlu` at `riscvBaseAluModel`, for `ComBaseAlu com` and
    `AllReg64 Γ`: `M.exec` is `runRBlock64` and the value fact is the first
    conjunct of `compile_correct_riscv` (from `comToRiscvLsem_correct`). -/
theorem compile_correct_baseAlu_riscv {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) :
    (riscvBaseAluModel.decodeOut
        (riscvBaseAluModel.exec
          (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))
          (riscvBaseAluModel.encodeIn (encodeRiscvState V)))).regs
        (comRetName com Γ.length)
      = Com.denote com V :=
  compile_correct_baseAlu riscvBaseAluModel rfl (fun _ => rfl) (fun _ => rfl)
    (fun s => s.regs) _ (encodeRiscvState V) (comRetName com Γ.length) _
    (compile_correct_riscv hba hΓ V).1

/-- `compile_correct_baseAlu` at `armBaseAluModel`, for `ComBaseAlu com` and
    `AllReg64 Γ`: `M.exec` is `runBBlock` and the value fact is the first
    conjunct of `compile_correct_arm` (from `comToArmLsem_correct`). -/
theorem compile_correct_baseAlu_arm {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) :
    (armBaseAluModel.decodeOut
        (armBaseAluModel.exec
          (armBlockOf (comToRegProg com Γ.length))
          (armBaseAluModel.encodeIn (encodeArmState V)))).regs
        (comRetName com Γ.length)
      = Com.denote com V :=
  compile_correct_baseAlu armBaseAluModel rfl (fun _ => rfl) (fun _ => rfl)
    (fun s => s.regs) _ (encodeArmState V) (comRetName com Γ.length) _
    (compile_correct_arm hba hΓ V).1

/-! ## 5. The `exec` of each model -/

/-- The RISC-V model's `exec` used in `compile_correct_riscv` is the
    `runRBlock64` block fold. -/
theorem compile_correct_riscv_exec_nonid
    (code : List RInst64) (s : RState64) :
    riscvBaseAluModel.exec code s = runRBlock64 s code := rfl

/-- The ARM model's `exec` used in `compile_correct_arm` is the `runBBlock` block
    fold. -/
theorem compile_correct_arm_exec_nonid
    (code : List BInst) (s : BState) :
    armBaseAluModel.exec code s = runBBlock s code := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectBaseAlu
