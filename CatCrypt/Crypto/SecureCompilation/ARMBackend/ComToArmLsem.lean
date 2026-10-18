/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder

/-!
# `Com → AArch64`: a block-execution `MachineModel` and value preservation

This module is the AArch64 counterpart of `RISCVBackend/ComToRiscvLsem.lean`,
which defines the structure `MachineModel`. This module defines a
`MachineModel` whose `exec` is the `ArmModel.runBBlock` block fold and whose
`validated` field is the value-preservation statement for the base-ALU (GP-ALU)
fragment of `Com → AArch64`.

## Dependencies

* **The block model** — `ARMBackend.runBBlock` (the `evalBInst` fold over the
  64-bit `X`-register `BState`) and `runBBlock_cons`/`bignumBlock_lowering_denote`
  (`ArmModel.lean`, `ArmLowering.lean`).
* **The whole-`Com` value chain** — `ScalarLinNeutralDemo.com_arm_e2e`: for a
  `Com` satisfying `ComOK` over an `AllReg64` context, run from a state whose
  registers are `envOf Γ.length V`, the AArch64 machine run computes `Com.denote`.
  It composes `comToReg_faithful` (the de-Bruijn front), the neutral-semantics
  theorem `com_machine_faithful`, and the AArch64 `ScalarTarget` theorem
  `ComToArm.regToBOp_denote`. It is stated over `armTarget.runOps`/
  `armTarget.compile`, which `bignumBlock_lowering_denote` identifies with the
  model run `runBBlock ∘ lowerBBlock`.
* **The `Com`-level base-ALU restriction** — `ComBaseAlu`, `BaseAluOp`,
  `RegBaseAlu`, `comToRegProg_RegBaseAlu` are defined over `RegStmt` /
  `opToStmts` / `Com` and do not mention RISC-V lowering; they are imported from
  `RISCVBackend.ComToRiscvLsem` and used for the ARM coverage proof.
* **The decode round-trip** — `SailArmDecoder.roundtrip_binst_add`, `_sub`,
  `_and`, `_orr`, `_eor` (the five GP-ALU ops this module's fragment executes),
  alongside the rest of the `roundtrip_binst_*` family and the 32-bit
  `roundtrip_ainst_*`: `decode (encode i) = i` against field splits hand
  transcribed from the public `rems-project/sail-arm` `aarch_decode.sail`.
  No sail-arm checkout is vendored in this repository, so the transcription is a
  trusted step. `roundtrip_binst_orr` carries the side condition `Rn ≠ XZR`,
  which separates `ORR` from the `MOV` alias.

## Main results

1. **`comToArmLsem_correct`** (main theorem) — for `ComBaseAlu com`,
   `AllReg64 Γ` and a start state with `s.regs = envOf Γ.length V`, the AArch64
   `runBBlock` execution of the compiled-and-lowered block, read at the result
   register, equals `Com.denote com V`, and every executed `BInst` is in the
   GP-ALU subset (`armBlock_all_gpAlu`).
2. **`armBaseAluModel`** — a `MachineModel` with
   `exec := fun code s => runBBlock s code` and `validated := ArmBaseAluGrounded`,
   the proposition stated by `comToArmLsem_correct`; the AArch64 counterpart of
   `riscvBaseAluModel`.

## Trust scope: decode round-trip, no Sail-execute refinement

The RISC-V model's `validated` (`RiscvBaseAluGrounded`) is a value-level
Sail-execute refinement: under a register-name alignment, the value each base-ALU
`evalRInst64` step writes is proved equal to the value the sail-riscv
`execute_RTYPE` clause writes, where that clause is an in-file excerpt of the
sail-riscv-lean generated output (commit `9eba3f07`; upstream not vendored)
(`SailRiscv64Refinement`). ARM has an in-tree hand-transcribed execute-clause
file, `SailArm64Refinement.lean`, which renders two Arm ARM pseudocode clauses and
proves that their per-op value matches `ArmModel`'s `opAnd64`/`opOrr64`/`opEor64`
(and raw `BitVec` `+`/`-`). No theorem links it to `runBBlock`: the file does not
mention `evalBInst`, `BState` or `runBBlock`, no module in the package imports it,
its clauses were not read from a checkout vendored in this repository, and the
provenance of the transcription is not recorded. It therefore does not ground
this model. The ARM model rests on:

* the **`SailArmDecoder` decode round-trip** — `decode (encode i) = i` against the
  transcribed `sail-arm` `aarch_decode.sail` parse clauses (which operand bits
  each instruction names), for the full emitted GP-ALU subset;
* **differential testing** against the GNU assembler / objdump / LLVM and a qemu
  execute KAT — 704/704 encode-decode, 237/237 execute, a tally from an untracked
  local harness, not vendored in this repository and not reproducible from this
  tree;
* the **hand-written `ArmModel` semantics**, checked against the Arm ARM by
  reading.

No machine-checked equality relates `runBBlock`'s per-op effect to a `sail-arm`
execute clause; the machine-checked relation is between the encoder output and the
transcribed decode parse. A Sail-execute grounding for ARM requires a vendored
`sail-arm` execute-semantics model and a theorem carrying the value-level lemmas of
`SailArm64Refinement` to `evalBInst`/`runBBlock`. The `validated` field of
`armBaseAluModel` is value preservation plus GP-ALU coverage, not a Sail-execute
refinement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLsem

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
  (RegBaseAlu BaseAluOp ComBaseAlu comToRegProg_RegBaseAlu MachineModel)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The GP-ALU fragment of the machine `BInst` set

The base-ALU AArch64 instructions a base-ALU `Com` lowers to: the five binary
GP-ALU ops `ADD`/`SUB`/`AND`/`ORR`/`EOR` over the 64-bit `X` registers (the
flag-setting forms, the multiplies, the conditional-selects, the constant loads
and the shifts are *not* GP-ALU here). The AArch64 analogue of RISC-V's
`IsBaseAlu : RInst64 → Prop`. -/

/-- A GP-ALU `BInst`: `ADD`/`SUB`/`AND`/`ORR`/`EOR` (64-bit, no flags). -/
def IsGpAlu : BInst → Prop
  | .add .. | .sub .. | .and .. | .orr .. | .eor .. => True
  | _ => False

/-! ### The lowered AArch64 block of a `RegProg`

`ComToArm.regToBOp p` is `armTarget.compile p = p.flatMap regStmtToBOp`. We
spell the pipeline as `p.flatMap regStmtToBOp` rather than via `regToBOp`,
because `regToBOp` is *definitionally* `armTarget.compile` and `armTarget` is a
structure literal that bundles its `select_correct` proof field — whose `loadImm`
case (`ComToArm.regStmtToBOp_denote`→`loadImm_lower`→`mk_recon`) is closed by
`bv_decide`, pulling SAT-certificate axioms into the term. The `instSel`
abbreviation below is the same op-selection (`regToBOp_eq` proves they are
equal) and does not depend on the `bv_decide` axioms, so `comToArmLsem_correct`
can be stated over it without them. -/

/-- The op-selection of a `RegProg` (= `ComToArm.regToBOp`, spelled without the
    axiom-entangled `armTarget` structure literal). -/
def instSel (p : RegProg) : List BOp := p.flatMap regStmtToBOp

/-- `instSel` is exactly `ComToArm.regToBOp` — definitionally equal, but stated as
    a propositional bridge so the equality (and `regToBOp`'s `mk_recon`
    `bv_decide` axioms) is not a dependency of `comToArmLsem_correct`. -/
theorem regToBOp_eq (p : RegProg) : regToBOp p = instSel p := rfl

/-- The lowered AArch64 machine block of a `RegProg`: select ops, lower to
    `BInst`. Equal to `lowerBBlock (regToBOp p)` (via `regToBOp_eq`). -/
def armBlockOf (p : RegProg) : List BInst := lowerBBlock (instSel p)

/-! ## 2. The compiled-and-lowered block is entirely GP-ALU

The lowered block of a base-ALU `Com` contains only GP-ALU `BInst`s, the five
instruction forms covered by the `SailArmDecoder` decode round-trip theorems. The
`Com`/`RegStmt`-level base-ALU restriction (`ComBaseAlu`, `RegBaseAlu`,
`comToRegProg_RegBaseAlu`) is imported from the RISC-V module; the lemmas below
concern the ARM lowering `regStmtToBOp` / `toBInst`. -/

/-- One base-ALU `RegStmt` lowers (`regStmtToBOp` then `toBInst`) to all GP-ALU
    `BInst`s — the ARM analogue of RISC-V's `stmt_lower_base`. -/
theorem stmt_lower_gpAlu (stmt : RegStmt) (h : RegBaseAlu stmt) :
    ∀ i ∈ (regStmtToBOp stmt).map toBInst, IsGpAlu i := by
  cases stmt <;> simp_all [RegBaseAlu, regStmtToBOp, toBInst, IsGpAlu]

/-- A whole base-ALU `RegProg` lowers (`instSel` then `lowerBBlock`) to an
    all-GP-ALU `BInst` block. `instSel p = p.flatMap regStmtToBOp` and
    `lowerBBlock = List.map toBInst`. -/
theorem regprog_lower_gpAlu (p : RegProg) (hp : ∀ stmt ∈ p, RegBaseAlu stmt) :
    ∀ i ∈ armBlockOf p, IsGpAlu i := by
  intro i hi
  rw [armBlockOf, instSel, show lowerBBlock (p.flatMap regStmtToBOp)
        = (p.flatMap regStmtToBOp).map toBInst from rfl,
      List.map_flatMap, List.mem_flatMap] at hi
  obtain ⟨stmt, hstmt, hi'⟩ := hi
  exact stmt_lower_gpAlu stmt (hp stmt hstmt) i hi'

/-- **The compiled-and-lowered AArch64 block of a base-ALU `Com` is all GP-ALU.**
    Every `BInst` the model executes is `ADD`/`SUB`/`AND`/`ORR`/`EOR`, the forms
    covered by the `SailArmDecoder` round-trip theorems (for `ORR` under
    `Rn ≠ XZR`); those theorems are separate and not part of this statement. The
    ARM counterpart of `riscvBlock_all_baseAlu`. -/
theorem armBlock_all_gpAlu {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) :
    ∀ i ∈ armBlockOf (comToRegProg com Γ.length), IsGpAlu i :=
  regprog_lower_gpAlu (comToRegProg com Γ.length) (comToRegProg_RegBaseAlu hba Γ.length)

/-! ## 3. The value bridge, restricted to the base-ALU fragment

`com_arm_e2e` routes the value through the *full* `armTarget`, whose
`select_correct` covers `loadImm` (a `bv_decide` `movz`/`movk` reconstruction,
`ComToArm.mk_recon`, that pulls SAT-certificate axioms into the term). The
base-ALU fragment never emits `loadImm`, so we build the value bridge directly
over the GP-ALU statements — for which `runBBlock ∘ lowerBBlock ∘ regStmtToBOp`
realises `evalRegStmt` by `rfl`. The proof of `comToArmLsem_correct` therefore
does not pass through `mk_recon` and its `bv_decide` SAT-certificate axioms. The
de-Bruijn front (`comToReg_faithful`) and the neutral projection (`hstep_arm`) do
not use `bv_decide`. -/

/-- For a base-ALU `RegStmt`, the lowered machine run of its selected `BOp`(s)
    realises the source effect `evalRegStmt` — `rfl` on each of the five GP-ALU
    cases (no `loadImm`, hence no `mk_recon`/`bv_decide` axioms). -/
theorem runBBlock_regStmtToBOp_base (s : BState) (stmt : RegStmt)
    (h : RegBaseAlu stmt) :
    runBBlock s (lowerBBlock (regStmtToBOp stmt)) = evalRegStmt s stmt := by
  cases stmt <;> first | rfl | exact absurd h (by simp [RegBaseAlu])

/-- `runBBlock` is additive over block concatenation (the `BInst` analogue of
    `runABlock_append`; not provided in `ArmModel.lean`). -/
theorem runBBlock_append (s : BState) (xs ys : List BInst) :
    runBBlock s (xs ++ ys) = runBBlock (runBBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBBlock_cons, ih]

/-- A whole base-ALU `RegProg`'s lowered machine run is the `evalRegStmt` fold —
    induction over the program, using `runBBlock`/`lowerBBlock` additivity and the
    per-statement base-ALU fact (no `armTarget.compile_denote`, so no `loadImm`
    leak). -/
theorem runBBlock_regToBOp_base (p : RegProg) (hp : ∀ stmt ∈ p, RegBaseAlu stmt)
    (s : BState) :
    runBBlock s (armBlockOf p) = p.foldl evalRegStmt s := by
  induction p generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hx : RegBaseAlu x := hp x (List.mem_cons.mpr (Or.inl rfl))
      have hxs : ∀ stmt ∈ xs, RegBaseAlu stmt :=
        fun stmt h => hp stmt (List.mem_cons.mpr (Or.inr h))
      rw [show armBlockOf (x :: xs)
            = lowerBBlock (regStmtToBOp x) ++ armBlockOf xs from by
            simp only [armBlockOf, instSel, List.flatMap_cons, lowerBBlock, List.map_append],
          runBBlock_append, runBBlock_regStmtToBOp_base s x hx, List.foldl_cons]
      exact ih hxs (evalRegStmt s x)

/-- **The base-ALU value bridge.** For a base-ALU `RegProg`, the projected machine
    run computes the canonical neutral denotation `RegProg.denotePure` — the
    `loadImm`-free analogue of `ScalarTarget.compile_denote_pure_on`, using the
    AArch64 projection agreement `hstep_arm`. -/
theorem runBBlock_regToBOp_base_pure (p : RegProg)
    (hp : ∀ stmt ∈ p, RegBaseAlu stmt) (s : BState) :
    (runBBlock s (armBlockOf p)).regs
      = RegProg.denotePure p s.regs := by
  rw [runBBlock_regToBOp_base p hp]
  show (p.foldl evalRegStmt s).regs = p.foldl evalRegStmtPure s.regs
  induction p generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← hstep_arm s x]
      exact ih (fun stmt h => hp stmt (List.mem_cons.mpr (Or.inr h))) (evalRegStmt s x)

/-! ## 4. `Com → AArch64` value preservation -/

/-- **Whole-`Com` value preservation for AArch64.** For a `Com` with
    `ComBaseAlu com` over a context with `AllReg64 Γ`, and a start state `s` with
    `s.regs = envOf Γ.length V`, executing the compiled-and-lowered AArch64 block
    with `runBBlock`:

    1. yields a state whose register `comRetName com Γ.length` holds
       `Com.denote com V` (proof: the de-Bruijn front `comToReg_faithful`, the
       per-statement base-ALU machine fact `runBBlock_regStmtToBOp_base`, and the
       neutral projection `hstep_arm`, restricted to the `loadImm`-free GP-ALU
       subset), and
    2. executes only GP-ALU instructions (`armBlock_all_gpAlu`: every executed
       `BInst` is `ADD`/`SUB`/`AND`/`ORR`/`EOR`).

    The block `armBlockOf (comToRegProg com Γ.length)` is definitionally
    `lowerBBlock (regToBOp (comToRegProg com Γ.length))`, the `ComToArm` pipeline
    (`regToBOp_eq`). It is spelled via `armBlockOf` because the
    `regToBOp`/`armTarget` spelling depends on `mk_recon`'s `bv_decide` axioms
    through the `loadImm` selection, which the base-ALU fragment does not use.

    This is the AArch64 counterpart of `comToRiscvLsem_correct`, with `runBBlock`
    as the execution semantics.

    **Trust scope:** conjunct (2) states only membership in the GP-ALU subset. For
    that subset the package has the `SailArmDecoder` decode round-trip theorems and
    external differential/qemu testing; it has no Sail-execute refinement. The
    in-tree `SailArm64Refinement` transcribes execute clauses, but no theorem links
    it to `runBBlock`, so it is not a counterpart of `SailRiscv64Refinement`. -/
theorem comToArmLsem_correct {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (hba : ComBaseAlu com) (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (s : BState) (hs : s.regs = envOf Γ.length V) :
    (runBBlock s (armBlockOf (comToRegProg com Γ.length))).regs
        (comRetName com Γ.length)
      = Com.denote com V
    ∧ (∀ i ∈ armBlockOf (comToRegProg com Γ.length), IsGpAlu i) := by
  refine ⟨?_, armBlock_all_gpAlu hba⟩
  rw [runBBlock_regToBOp_base_pure _ (comToRegProg_RegBaseAlu hba Γ.length), hs,
      ← comToReg_faithful (ComBaseAlu.toComOK hba) hΓ V]

/-! ## 5. An AArch64 `MachineModel` with `exec := runBBlock` -/

/-- The statement of `comToArmLsem_correct` as a proposition, used as the
    `MachineModel.validated` field. The AArch64 counterpart of RISC-V's
    `RiscvBaseAluGrounded`, at the value-preservation level: for every `Com` with
    `ComBaseAlu com` over an `AllReg64` context, run from a state with
    `s.regs = envOf Γ.length V`, the `runBBlock` execution holds `Com.denote com V`
    at the result register and executes only GP-ALU instructions.

    It is not a Sail-execute refinement. `RiscvBaseAluGrounded` equates each model
    step with the `execute_RTYPE` Sail clause held as an in-file excerpt of the
    sail-riscv-lean generated output (commit `9eba3f07`; upstream not vendored);
    no theorem here connects `runBBlock` to an execute-clause model. The in-tree
    `SailArm64Refinement.lean` transcribes two Arm ARM execute clauses by hand, but
    no module imports it and it does not mention `evalBInst`/`runBBlock`. The
    GP-ALU instructions are covered by the `SailArmDecoder` decode round-trip,
    differential/qemu testing and the hand-written `ArmModel`. A Sail-execute
    refinement would require a vendored `sail-arm` execute model and a theorem
    relating it to `runBBlock`. -/
def ArmBaseAluGrounded : Prop :=
  ∀ {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)},
    ComBaseAlu com → AllReg64 Γ → ∀ (V : Ctxt.Valuation Γ) (s : BState),
      s.regs = envOf Γ.length V →
      (runBBlock s (armBlockOf (comToRegProg com Γ.length))).regs
          (comRetName com Γ.length)
        = Com.denote com V
      ∧ (∀ i ∈ armBlockOf (comToRegProg com Γ.length), IsGpAlu i)

/-- `ArmBaseAluGrounded` holds, by `comToArmLsem_correct`. -/
theorem armBaseAluGrounded_proof : ArmBaseAluGrounded :=
  fun hba hΓ V s hs => comToArmLsem_correct hba hΓ V s hs

/-- **The AArch64 base-ALU `MachineModel`.** Its `exec` is the `runBBlock` block
    fold over `BState`, and its `validated` field is `ArmBaseAluGrounded`
    (proved by `armBaseAluGrounded_proof`). `Code` is the executed `BInst` list;
    `State` and `Value` are `BState`; `encodeIn` and `decodeOut` are `id`. The
    AArch64 counterpart of `riscvBaseAluModel`.

    **Scope:** `validated` states value preservation and GP-ALU coverage, not a
    Sail-execute refinement. RISC-V has such a refinement against an in-file
    excerpt of the sail-riscv-lean generated output; ARM's `SailArm64Refinement`
    is a hand transcription and no theorem relates it to `runBBlock`. -/
def armBaseAluModel : MachineModel where
  Code := List BInst
  State := BState
  Value := BState
  encodeIn := id
  decodeOut := id
  exec := fun code s => runBBlock s code
  validated := ArmBaseAluGrounded

/-- The model's `exec` is the `runBBlock` block fold. -/
theorem armBaseAluModel_exec (code : List BInst) (s : BState) :
    armBaseAluModel.exec code s = runBBlock s code := rfl

/-- The model's `validated` field, `ArmBaseAluGrounded`, holds by
    `armBaseAluGrounded_proof`. -/
theorem armBaseAluModel_validated : armBaseAluModel.validated :=
  armBaseAluGrounded_proof

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLsem
