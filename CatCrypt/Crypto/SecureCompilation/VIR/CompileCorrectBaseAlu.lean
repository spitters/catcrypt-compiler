/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLsem
import CatCrypt.Crypto.SecureCompilation.VIR.Compiler

/-!
# `compile_correct_baseAlu`: compiler correctness over a *genuine* non-`id` `exec`

`VIR/Compiler.lean`'s `compile_correct_all` is parametric over a `MachineModel`
`choice`, but for every `choice` it instantiates the **lattice carrier**
`latticeModel`, whose `exec := fun _ s => s` is the identity — the RISC-V/ARM
arms of `compile_correct_all` differ *only* in the `validated` field (the
`decode∘encode` round-trip pilots), never in `exec`. So `compile_correct_all`'s
CompCert-shape equation `decodeOut (exec m (encodeIn …)) = denote` reduces, for
RISC-V/ARM, through `exec := id` — the model's execution semantics does **no
work**.

This module states the missing **`compile_correct` over a non-`id` `exec`**: the
CompCert-shape equation `decode (model.exec code (encode V)) = source value`
where `model.exec` is the **genuine** block-execution semantics — `runRBlock64`
for RISC-V, `runBBlock` for ARM — *not* the identity. It is additive (a NEW file,
the way `ComToRiscvLsem`/`ComToArmLsem` added their base-ALU models without
touching `VIR/Compiler.lean`), and it does **not** edit `compile_correct_all` /
`latticeModel` in place.

## Carrier

* The model is `riscvBaseAluModel` / `armBaseAluModel`
  (`RISCVBackend/ComToRiscvLsem.lean`, `ARMBackend/ComToArmLsem.lean`), whose
  `exec` is `runRBlock64` / `runBBlock` and whose `validated` is the
  value-level (RISC-V: Sail) grounding each backend carries (NOT `True`, NOT
  `id`).
* `Code` is the compiled-and-lowered base-ALU block
  `lowerRBlock64 (regToROp (comToRegProg com Γ.length))` (RISC-V) /
  `armBlockOf (comToRegProg com Γ.length)` (ARM).
* `Value`/`State` is the register state `RState64` / `BState`; `encodeIn` is the
  register-name encoding of the source valuation (`encodeRiscvState` /
  `encodeArmState`, building a state whose `regs = envOf Γ.length V`); `decodeOut`
  is `id` and the abstract output is read back at the result register
  `comRetName com Γ.length`.

The conclusion `model.decodeOut (model.exec code (model.encodeIn V)) read at
comRetName = Com.denote com V` makes `model.exec` **load-bearing**: it is the
`runRBlock64`/`runBBlock` fold, applied to the encoded input state, and the
source denotation is recovered from the *executed* state. The keystones
`comToRiscvLsem_correct` / `comToArmLsem_correct` discharge it.

## Scope

Base-ALU only (ADD/SUB/AND/OR/XOR ↔ ADD/SUB/AND/ORR/EOR), exactly the fragment
the keystones cover — the same fragment `riscvBaseAluModel`/`armBaseAluModel`
carry. The RISC-V model's grounding is a value-level Sail-`execute_RTYPE`
refinement; ARM's is a decode-round-trip + differential/qemu grounding (no
in-tree `sail-arm` execute model) — the residual called out in
`ComToArmLsem.lean`. This module does not change those depths; it only exposes
the keystones in the CompCert `decode∘exec∘encode` shape over the genuine `exec`.
-/

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
open CatCrypt.Crypto.SecureCompilation.VIR.Compiler (MachineModel)

/-! ## 1. Encoding a source valuation into the genuine model's input state

The keystones (`comToRiscvLsem_correct`/`comToArmLsem_correct`) run from a state
`s` whose register file is the reflected valuation `envOf Γ.length V`. These are
the `MachineModel.encodeIn` maps of `riscvBaseAluModel`/`armBaseAluModel`
(`encodeIn := id`, so the value carrier IS the input state): we build the
register-state input from the valuation. -/

/-- Encode a source valuation `V` into the RISC-V model's input `RState64`:
    the register file is the reflected env `envOf Γ.length V`. By construction
    `(encodeRiscvState V).regs = envOf Γ.length V`, the keystone's input
    hypothesis. -/
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

The CompCert-shape equation over the genuine non-`id` `exec`. `decodeOut` is the
model `id`; we read the abstract output at the result register `comRetName`. -/

/-- **`compile_correct_riscv` — compiler correctness over the genuine RISC-V
    `exec`.** For a base-ALU all-`reg 64` `Com`, decoding the
    `riscvBaseAluModel`'s **execution** of the compiled-and-lowered block on the
    encoded input state — `model.decodeOut (model.exec code (model.encodeIn V))`,
    read at the result register `comRetName com Γ.length` — equals the source
    `Com.denote com V`, **and** every executed `RInst64` is base-ALU (so each
    step is Sail-`execute_RTYPE`-grounded, `riscvBlock_all_baseAlu`).

    `model.exec` is **load-bearing**: it is `runRBlock64` (the `evalRInst64`
    fold), NOT the `latticeModel` identity `fun _ s => s`. This is the genuine
    "compile_correct over a non-`id` exec" that `compile_correct_all` lacks for
    RISC-V — proved by instantiating the keystone `comToRiscvLsem_correct`. -/
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
  -- `decodeOut`/`encodeIn` are `id`; `exec` is the genuine `runRBlock64`.
  show (runRBlock64 (encodeRiscvState V)
          (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ lowerRBlock64 (regToROp (comToRegProg com Γ.length)), IsBaseAlu i)
  exact comToRiscvLsem_correct hba hΓ V (encodeRiscvState V) rfl

/-! ## 3. ARM: `compile_correct` over `armBaseAluModel.exec = runBBlock` -/

/-- **`compile_correct_arm` — compiler correctness over the genuine AArch64
    `exec`.** The mirror of `compile_correct_riscv`: decoding the
    `armBaseAluModel`'s **execution** (`runBBlock`, NOT `id`) of the
    compiled-and-lowered AArch64 block on the encoded input state, read at the
    result register, equals `Com.denote com V`, and every executed `BInst` is
    GP-ALU (decode-round-trip-grounded, `armBlock_all_gpAlu`). Proved by
    instantiating the keystone `comToArmLsem_correct`.

    **Trust scope (residual vs RISC-V):** the GP-ALU conjunct is a *decode*
    round-trip + differential/qemu grounding, not a Sail-execute refinement — ARM
    has no in-tree `sail-arm` execute model (see `ComToArmLsem.lean`). -/
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
  -- `decodeOut`/`encodeIn` are `id`; `exec` is the genuine `runBBlock`.
  show (runBBlock (encodeArmState V)
          (armBlockOf (comToRegProg com Γ.length))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ armBlockOf (comToRegProg com Γ.length), IsGpAlu i)
  exact comToArmLsem_correct hba hΓ V (encodeArmState V) rfl

/-! ## 4. The parametric `MachineModel`-level statement

Both per-arch results above are instances of one `MachineModel`-level CompCert
shape: given a model `M` whose `State = Value` (the register state) with
`decodeOut`/`encodeIn` reducing to `id` on the carrier, an encoder building the
keystone input state, and the keystone value-fact, the equation
`(M.decodeOut (M.exec code (M.encodeIn (enc V)))) read at comRetName = denote`
holds **with `M.exec` load-bearing**. `compile_correct_baseAlu` packages this so
the keystone (`runRBlock64`/`runBBlock`) is the model's `exec`, instantiated at
`riscvBaseAluModel`/`armBaseAluModel` below. -/

/-- **`compile_correct_baseAlu` — the `MachineModel`-parametric CompCert shape
    over a genuine non-`id` `exec`.** Stated for a `MachineModel M` whose value
    carrier *is* its state (`Value = State`, the case the genuine base-ALU models
    are in — `encodeIn = decodeOut = id`). Given the carrier-identity facts
    (`hEnc`/`hDec`), a `regs` read-back `readReg`, the compiled block `code`, the
    encoded input state `encV`, and the keystone value-fact `hKey` (the
    executed-state read-back equals `denote`), the CompCert-shape equation
    `readReg (decodeOut (exec code (encodeIn encV))) ret = denote` holds — with
    `M.exec` **load-bearing**: `M.exec code (M.encodeIn encV)` is the genuine model
    run, and the identity `encodeIn`/`decodeOut` only un/re-wrap the carrier.

    Instantiated at `riscvBaseAluModel` (`M.exec = runRBlock64`,
    `hKey := comToRiscvLsem_correct`) and `armBaseAluModel` (`M.exec = runBBlock`,
    `hKey := comToArmLsem_correct`) — see `compile_correct_baseAlu_riscv`/`_arm`. -/
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
  -- CompCert round-trip collapses to the genuine `M.exec` of the encoded state.
  rw [hEnc, hDec]
  exact hKey

/-- `compile_correct_baseAlu` at `riscvBaseAluModel`: the keystone `M.exec`
    instantiates to the genuine `runRBlock64` and the value-fact to
    `comToRiscvLsem_correct` — confirming the parametric shape's `exec` is the
    non-`id` RISC-V block fold. -/
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

/-- `compile_correct_baseAlu` at `armBaseAluModel`: `M.exec` is the genuine
    `runBBlock` and the value-fact is `comToArmLsem_correct`. -/
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

/-! ## 5. The `exec` is genuinely non-`id` (load-bearing), recorded explicitly -/

/-- The RISC-V model's `exec` used in `compile_correct_riscv` is the genuine
    `runRBlock64` block fold — NOT the `latticeModel` identity `fun _ s => s`. -/
theorem compile_correct_riscv_exec_nonid
    (code : List RInst64) (s : RState64) :
    riscvBaseAluModel.exec code s = runRBlock64 s code := rfl

/-- The ARM model's `exec` used in `compile_correct_arm` is the genuine
    `runBBlock` block fold — NOT the `latticeModel` identity `fun _ s => s`. -/
theorem compile_correct_arm_exec_nonid
    (code : List BInst) (s : BState) :
    armBaseAluModel.exec code s = runBBlock s code := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectBaseAlu
