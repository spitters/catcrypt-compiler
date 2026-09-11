/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.ComToRiscvLsem
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
public import CatCrypt.Crypto.SecureCompilation.VIR.Compiler

/-!
# `Com → AArch64`: a block-execution `MachineModel` + value-preservation keystone

This module mirrors the RISC-V cross-arch result
(`RISCVBackend/ComToRiscvLsem.lean`) on the AArch64 side: it replaces the
`MachineModel.exec := fun _ s => s` validation shell of `VIR/Compiler.lean`'s
`latticeModel`/`armModel` with a `MachineModel` whose `exec` is the **real**
`ArmModel.runBBlock` block fold, carrying a genuine value-level `validated`
field — the whole-`Com → AArch64` value-preservation keystone for the base-ALU
(GP-ALU) fragment.

## What was already in the tree (reused verbatim, not re-derived)

* **The block model** — `ARMBackend.runBBlock` (the `evalBInst` fold over the
  64-bit `X`-register `BState`) and `runBBlock_cons`/`bignumBlock_lowering_denote`,
  already proved (`ArmModel.lean`, `ArmLowering.lean`).
* **The whole-`Com` value chain** — `ScalarLinNeutralDemo.com_arm_e2e`: for a
  supported all-`reg 64` `Com`, the AArch64 machine run computes `Com.denote`.
  This chains `comToReg_faithful` (the de-Bruijn front), the neutral-semantics
  master `com_machine_faithful`, and the AArch64 `ScalarTarget` keystone
  (`ComToArm.regToBOp_denote`). It terminates at `armTarget.runOps`/
  `armTarget.compile`, which `bignumBlock_lowering_denote` identifies with the
  model run `runBBlock ∘ lowerBBlock`.
* **The `Com`-level base-ALU restriction** — `ComBaseAlu`, `BaseAluOp`,
  `RegBaseAlu`, `comToRegProg_RegBaseAlu` are **front-only** (over `RegStmt` /
  `opToStmts` / `Com`, not RISC-V lowering), so they are imported verbatim from
  `RISCVBackend.ComToRiscvLsem` and reused for the ARM coverage proof.
* **The decode round-trip** — `SailArmDecoder.roundtrip_binst_add`, `_sub`,
  `_and`, `_orr`, `_eor` (the five GP-ALU ops this module's fragment executes),
  alongside the rest of the `roundtrip_binst_*` family and the 32-bit
  `roundtrip_ainst_*`: `decode (encode i) = i` against field splits **hand
  transcribed** from the public `rems-project/sail-arm` `aarch_decode.sail`
  (no sail-arm checkout is vendored in this repo, so that transcription is a
  trusted step). `roundtrip_binst_orr` carries the `Rn ≠ XZR` side condition
  that separates a real `ORR` from the `MOV` alias.

## What this module adds (the missing completion)

1. **`comToArmLsem_correct`** (the ARM keystone) — the whole-`Com` value-
   preservation fact: the AArch64 `runBBlock` execution of the compiled-and-
   lowered base-ALU `Com` computes `Com.denote` (via `com_arm_e2e` bridged
   through `bignumBlock_lowering_denote`) **and** every executed `BInst` is in
   the GP-ALU subset (`armBlock_all_gpAlu`).
2. **`armBaseAluModel`** — a genuine `MachineModel` with
   `exec := fun code s => runBBlock s code` (a non-`id` execution semantics) and
   a `validated` field carrying the value-level keystone, analogous to
   `riscvBaseAluModel`.

## HONEST trust scope: decode round-trip, NOT a Sail-execute refinement

**This is the residual that separates ARM from RISC-V.** The RISC-V model's
`validated` (`RiscvBaseAluGrounded`) is a *value-level Sail-execute refinement*:
each base-ALU step of `runRBlock64` is proved equal to the value the sail-riscv
`execute_RTYPE` clause writes, where that clause is an in-file excerpt of the
sail-riscv-lean generated output (commit `9eba3f07`; upstream not vendored)
(`SailRiscv64Refinement`). ARM has an
in-tree *hand-transcribed* execute-clause file — `SailArm64Refinement.lean`,
which renders two Arm ARM pseudocode clauses and proves their per-op value
matches `ArmModel`'s `opAnd64`/`opOrr64`/`opEor64` (and raw `BitVec` `+`/`-`) —
but **no theorem links it to `runBBlock`**: nothing in it mentions `evalBInst`,
`BState`, or `runBBlock`, nothing in the package imports it, and its clauses were
not read from a checkout vendored in this repo; the transcription's provenance is
not recorded. So it does not ground this model. What grounds the ARM model is:

* the **`SailArmDecoder` decode round-trip** — `decode (encode i) = i` against the
  transcribed `sail-arm` `aarch_decode.sail` *parse* clauses (which operand bits
  each instruction names), for the full emitted GP-ALU subset;
* **differential testing** against the GNU assembler / objdump / LLVM and a qemu
  execute KAT — 704/704 encode-decode, 237/237 execute, a tally from an untracked
  local harness, not vendored in this repo and not reproducible from this tree;
* the **hand-written `ArmModel` semantics**, auditable against the Arm ARM by eye.

There is **no machine-checked equality between `runBBlock`'s per-op effect and an
authoritative `sail-arm` *execute* clause** — only between the encoder bytes and
the transcribed *decode* parse. Bringing ARM to RISC-V's depth needs a vendored
`sail-arm` execute-semantics model and a theorem carrying `SailArm64Refinement`'s
value-level lemmas across to `evalBInst`/`runBBlock`; that is the explicit
residual, called out here so the `validated` field is not read as a Sail-execute
grounding it is not.
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
  (RegBaseAlu BaseAluOp ComBaseAlu comToRegProg_RegBaseAlu)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Compiler (MachineModel)

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
abbreviation below is the *same* op-selection (`regToBOp_eq` proves they are
equal), kept axiom-entanglement-free for the keystone. -/

/-- The op-selection of a `RegProg` (= `ComToArm.regToBOp`, spelled without the
    axiom-entangled `armTarget` structure literal). -/
def instSel (p : RegProg) : List BOp := p.flatMap regStmtToBOp

/-- `instSel` is exactly `ComToArm.regToBOp` — definitionally equal, but stated as
    a propositional bridge so the equality (and `regToBOp`'s `mk_recon`
    `bv_decide` axioms) stays *outside* the keystone's axiom budget. -/
theorem regToBOp_eq (p : RegProg) : regToBOp p = instSel p := rfl

/-- The lowered AArch64 machine block of a `RegProg`: select ops, lower to
    `BInst`. Equal to `lowerBBlock (regToBOp p)` (via `regToBOp_eq`). -/
def armBlockOf (p : RegProg) : List BInst := lowerBBlock (instSel p)

/-! ## 2. The compiled-and-lowered block is entirely GP-ALU

So every step the `runBBlock` execution takes is a decode-round-trip-grounded
GP-ALU instruction, we show the lowered block of a base-ALU `Com` contains only
GP-ALU `BInst`s. The `Com`/`RegStmt`-level base-ALU restriction (`ComBaseAlu`,
`RegBaseAlu`, `comToRegProg_RegBaseAlu`) is front-only and imported from the
RISC-V module; only the ARM-local lowering `regStmtToBOp` / `toBInst` is new. -/

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

/-- **The compiled-and-lowered AArch64 block of a base-ALU `Com` is all GP-ALU** —
    so every `BInst` the model executes is decode-round-trip-grounded (the ARM
    analogue of `riscvBlock_all_baseAlu`). -/
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
realises `evalRegStmt` by `rfl` — keeping the keystone's axiom set
`{propext, Classical.choice, Quot.sound}` (matching `comToRiscvLsem_correct`).
The de-Bruijn front (`comToReg_faithful`) and the neutral projection
(`hstep_arm`) are themselves axiom-clean. -/

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

/-! ## 4. The `Com → AArch64` value-preservation keystone -/

/-- **The whole-`Com` value-preservation keystone (the ARM completion).** For a
    base-ALU all-`reg 64` `Com`, executing the compiled-and-lowered AArch64 block
    on the model:

    1. **computes the source `Com.denote`** (the value chain: the de-Bruijn front
       `comToReg_faithful`, the per-statement base-ALU machine fact
       `runBBlock_regStmtToBOp_base`, and the neutral projection `hstep_arm` — all
       reusing the existing AArch64 `ArmModel`/`ComToArm` pieces, restricted to the
       `loadImm`-free GP-ALU subset so the axiom set matches
       `comToRiscvLsem_correct`), and
    2. **runs only GP-ALU instructions** (`armBlock_all_gpAlu` — every executed
       `BInst` is `ADD`/`SUB`/`AND`/`ORR`/`EOR`, each grounded by the
       `SailArmDecoder` decode round-trip).

    The block `armBlockOf (comToRegProg com Γ.length)` is definitionally
    `lowerBBlock (regToBOp (comToRegProg com Γ.length))` — the `ComToArm` pipeline
    (`regToBOp_eq`); it is spelled via `armBlockOf` so the keystone's axiom set
    stays `{propext, Classical.choice, Quot.sound}` (the `regToBOp`/`armTarget`
    spelling drags in `mk_recon`'s `bv_decide` axioms via the `loadImm` selection
    the base-ALU fragment never uses).

    The `MachineModel.exec := fun _ s => s` shell of `latticeModel`/`armModel` is
    thereby replaced, on the base-ALU fragment, by the genuine `runBBlock`
    functional semantics — the AArch64 mirror of `comToRiscvLsem_correct`.

    **Trust scope (the residual vs RISC-V):** conjunct (2) is a *decode* round-trip
    + differential/qemu grounding, **not** a Sail-execute refinement. The in-tree
    `SailArm64Refinement` hand-transcribes execute clauses but no theorem links it
    to `runBBlock`, so it is not a `SailRiscv64Refinement` analogue. -/
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

/-! ## 5. A genuine non-`id` `exec` for the AArch64 model -/

/-- The proposition recording the value-level keystone (and its GP-ALU coverage),
    to inhabit the `MachineModel.validated` field — the AArch64 analogue of
    RISC-V's `RiscvBaseAluGrounded`, but at the **value-preservation** depth this
    backend supports. For every base-ALU all-`reg 64` `Com`, run from a matching
    state, the `runBBlock` execution reads back the source `Com.denote` and runs
    only GP-ALU instructions.

    **It is NOT a Sail-execute refinement.** Unlike `RiscvBaseAluGrounded` (which
    equates each model step with the `execute_RTYPE` Sail clause held as an
    in-file excerpt of the sail-riscv-lean generated output — commit `9eba3f07`;
    upstream not vendored), no
    theorem here connects `runBBlock` to an execute-clause model. The in-tree
    `SailArm64Refinement.lean` hand-transcribes two Arm ARM execute clauses, but
    it is import-orphaned and never mentions `evalBInst`/`runBBlock`, so it does
    not close that gap. The GP-ALU coverage is grounded by the `SailArmDecoder`
    decode round-trip + differential/qemu testing + the hand-written `ArmModel`.
    The residual to RISC-V depth is a vendored `sail-arm` execute port plus a
    theorem bridging it to `runBBlock`. -/
def ArmBaseAluGrounded : Prop :=
  ∀ {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)},
    ComBaseAlu com → AllReg64 Γ → ∀ (V : Ctxt.Valuation Γ) (s : BState),
      s.regs = envOf Γ.length V →
      (runBBlock s (armBlockOf (comToRegProg com Γ.length))).regs
          (comRetName com Γ.length)
        = Com.denote com V
      ∧ (∀ i ∈ armBlockOf (comToRegProg com Γ.length), IsGpAlu i)

/-- `ArmBaseAluGrounded` is inhabited by the proved keystone (not `True`). -/
theorem armBaseAluGrounded_proof : ArmBaseAluGrounded :=
  fun hba hΓ V s hs => comToArmLsem_correct hba hΓ V s hs

/-- **The AArch64 base-ALU `MachineModel`, with a genuine `exec`.** Unlike
    `VIR/Compiler.lean`'s `latticeModel`/`armModel` (whose `exec := fun _ s => s`
    is a validation shell that does not run the code), this model's `exec` is the
    real `runBBlock` block fold over `BState`, and its `validated` field is the
    value-level keystone `ArmBaseAluGrounded` (inhabited by
    `armBaseAluGrounded_proof`). `Code` is the executed `BInst` list;
    `State`/`Value` is `BState`. This is the non-`id` execution model the AArch64
    path was missing for the base-ALU fragment — the mirror of `riscvBaseAluModel`.

    **Honest depth:** `validated` is value-preservation + GP-ALU decode-round-trip
    grounding, NOT a Sail-execute refinement — RISC-V has one against an in-file
    excerpt of the sail-riscv-lean generated output; ARM's `SailArm64Refinement`
    is a hand transcription with no theorem reaching `runBBlock`. -/
def armBaseAluModel : MachineModel where
  Code := List BInst
  State := BState
  Value := BState
  encodeIn := id
  decodeOut := id
  exec := fun code s => runBBlock s code
  validated := ArmBaseAluGrounded

/-- The model's `exec` genuinely runs the code: it is `runBBlock`, not the
    `latticeModel` identity `fun _ s => s`. -/
theorem armBaseAluModel_exec (code : List BInst) (s : BState) :
    armBaseAluModel.exec code s = runBBlock s code := rfl

/-- The model's `validated` field is the genuine value-level keystone, discharged
    by `armBaseAluGrounded_proof` (never `True`-by-fiat). -/
theorem armBaseAluModel_validated : armBaseAluModel.validated :=
  armBaseAluGrounded_proof

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLsem
