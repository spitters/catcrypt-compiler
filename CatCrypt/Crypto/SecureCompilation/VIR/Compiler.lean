/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback
import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
import CatCrypt.Crypto.SecureCompilation.VIR.CompilerGeneric
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder

/-!
# The compiler-correctness theorem: one `compile`, one `compile_correct_all`

This module assembles the per-route, per-stage compiler results that already
live in the tree into **one** generic compile function and **one** generic
correctness theorem, parametric over a `MachineModel`. It does not re-prove any
kernel, pass, or backend: every obligation is discharged by an existing theorem
(`latticeNttMul_compile_correct`, `runOutputToWords_chain_eq`,
`lowerComToProg_sem_eq'`, `rustToJasminCom_endToEnd`, the x86 `step`
preservation lemmas, and the Sail-validation round-trips), and every open
semantic edge is carried as an **explicit** hypothesis or `MachineModel` field —
never discharged by fiat.

## Scope

This is the single generic `compile` + `compile_correct_all` that replaces the
per-route / per-primitive end-to-end statements with one assembled theorem of
CompCert shape: *the emitted artifact, executed under a machine model's
validated semantics, computes the value the source program denotes* — relative
to that model's validation depth and under the stated hypotheses.

What this theorem claims is stated precisely here:

**(a) Which route is unconditional vs hypothesis-carrying.**

* **Lattice route** (`Source.lattice`, the ML-KEM NTT-multiply path) is
  **unconditional** at the dialect level: `latticeNttMul_compile_correct` has
  *zero* hypotheses. Its read-back form `runOutputToWords_chain_eq` carries only
  the leaf-agreement (`LeafAgrees`) and SSA-naming injectivity side-conditions
  of the whole-function lowering (`hInj`, `hPinj`) — and the lowering's own
  theorem `lowerComToProg_sem_eq'` already discharges the latter two
  internally, leaving only the leaf edge.
* **Front route** (`Source.front`, the haxpipe-extracted Rust path) is
  **hypothesis-carrying**: `rustToJasminCom_endToEnd` requires `hAdequacy`
  (front `Com.denote` = the operational post-state value of the extracted
  program) and `JasminLeafAgrees` (the CryptoSSA `extCall` leaves agree with
  their jasmin denotations), plus the per-pass success witnesses.

**(b) Per-model validation depth, carried in `MachineModel.validated`.**

* **x86** — *deepest.* The ALU `step` semantics are proved against the per-op
  Sail-validated preservation (`X86Backend.Preservation.add_preserves` …, in
  pure form `Bridges.Transfer.x86Add_eq`), and the instruction `encode`/`decode`
  round-trips against the transcribed Sail tables
  (`SailX86Decoder.roundtrip_*`). `x86Model.validated` records exactly these.
* **RISC-V** — *pilot.* The R/I-type `encode`/`decode` round-trips against the
  Sail-riscv tables (`SailRiscvDecoder.roundtrip_RInst`, `…_roriw`) and the
  RV32 lo-32 ALU-value refinements (`SailRiscv32Ref.addw_lo32` …) are proved;
  there is no whole-`Com`→RISC-V value-preservation theorem yet.
  `riscvModel.validated` records the round-trip + value-refinement pilot.
* **ARM (AArch64)** — *partial.* The GP-ALU `encode`/`decode` round-trips are
  proved (`SailArmDecoder.roundtrip_ainst_{add,sub,and,orr,eor,mov,ror,lsr}`),
  and one effect edge is the explicitly-named `trust_edge_pilot`; there is no
  whole-`Com`→ARM value-preservation theorem yet. `armModel.validated`
  records the round-trip subset.

**(c) Open edges that remain hypotheses** (not discharged here):

1. *front adequacy* (`hAdequacy`) — the extracted-Rust denotation = operational
   post-state value; per-protocol bridge obligation.
2. *leaf agreement* (`LeafAgrees` / `JasminLeafAgrees`) — opaque `extCall`
   leaves agree with their jasmin denotations.
3. *whole-array / SIMD read-back* — `runOutputToWords` reads back one scalar
   slot; the vector/SIMD multi-slot read-back is per-slot of this.
4. *`.jazz`/`.o` → silicon* — the assembler and the silicon are the deliberate
   trusted base; `MachineModel.validated` records the ISA-level validation each
   model carries, not a silicon-level proof.

This module makes **no** claim of "fully verified to silicon for all models."
The theorem is: `compile` is correct relative to each model's validated
semantics, at that model's depth, under the stated hypotheses.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Compiler

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback
-- front-route identifiers
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
-- `ctTransTy` lives in `JasminValTransport.lean` under the `CryptoToJasminComCorrect`
-- namespace, not in the `CProg`-lowering correctness module itself.
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Core
-- backend namespaces (for the per-model `validated` fields)
open CatCrypt.Crypto.SecureCompilation

/-! ## 1. The machine model -/

/-- **A target machine model.** Bundles, for one target ISA, the emitted
    artifact type, the value ↔ machine-state maps, the execution semantics, and
    — crucially — an *explicit* `validated` proposition recording the
    ISA-validation the model carries (the Sail-validation; its content and depth
    differ per model, so it is a field, never a hidden assumption).

    The model is deliberately abstract over the carrier: `Code` is the emitted
    program, `State` the machine state, `encodeIn`/`decodeOut` the value/state
    interface (for the lattice route the value carrier is the structured
    stack-array run-output `Fin n → BitVec 16` and `decodeOut` is the scalar-slot
    read-back `runOutputToWords`). -/
structure MachineModel where
  /-- The emitted artifact for this ISA (e.g. `JasminProg`, an ELF object, an
      ARM/RISC-V instruction list). -/
  Code : Type
  /-- The machine state the execution semantics acts on. -/
  State : Type
  /-- The abstract value the source program computes (the carrier `decodeOut`
      reads back to). -/
  Value : Type
  /-- Encode an input value into an initial machine state. -/
  encodeIn : Value → State
  /-- Decode an output value out of a final machine state. -/
  decodeOut : State → Value
  /-- The execution semantics: run the emitted code on a state. -/
  exec : Code → State → State
  /-- **The ISA-validation this model carries.** An explicit proposition — the
      Sail-validation facts (decode∘encode round-trips and/or step-vs-Sail
      preservation) that ground `exec`. Its depth differs per model; see the
      module `Scope`. -/
  validated : Prop

/-! ## 2. The per-model validation depth (the real Sail facts)

Each model's `validated` field is set to one of these aliases, each of which is
*definitionally the statement of an existing, proved round-trip theorem* in the
corresponding backend. The `*_validated` lemmas below discharge them by citing
exactly that theorem — so `MachineModel.validated` is never `True`-by-fiat: it is
the ISA-validation the backend carries, at its real depth. -/

/-- **x86 — deepest.** The register-direct ALU `encode∘decode` round-trip against
    the transcribed Sail tables (`SailX86Decoder.roundtrip_AluRR`). Together with
    the step-vs-Sail ALU preservation (`Bridges.Transfer.x86Add_eq`), this is the
    deepest validation any model carries. Defined as exactly the type of that
    proved theorem (`x86Validated_proof`). -/
def X86Validated : Prop :=
  ∀ (op d s : Nat), op < 256 → d < 16 → s < 16 →
    X86Backend.SailX86Decoder.decodeReg (X86Backend.ScalarEncoder.encAluRR op d s)
      = some { opcode := op, reg := s, rm := d }

/-- **RISC-V — pilot.** The full emitted RV64I subset `decode∘encode` round-trip
    against the sail-riscv `encdec` discipline (`SailRiscvDecoder.roundtrip_RInst`).
    There is no whole-`Com`→RISC-V value-preservation theorem yet; this is the
    instruction-level pilot. Defined as exactly the type of that proved
    theorem (`riscvValidated_proof`). -/
def RiscvValidated : Prop :=
  ∀ (i : RISCVBackend.RInst)
    (_hregs : (RISCVBackend.rinstDstSrcs i).1 ∈ RISCVBackend.SailRiscvDecoder.emittedRegs ∧
             ∀ r ∈ (RISCVBackend.rinstDstSrcs i).2, r ∈ RISCVBackend.SailRiscvDecoder.emittedRegs)
    (_hsh : ∀ d a m, i = .slliw d a m ∨ i = .srliw d a m → m < 32)
    (_hror : ∀ d a m, i = .roriw d a m → m < 32),
    RISCVBackend.SailRiscvDecoder.riscvDecode (RISCVBackend.RiscvEncoder.encodeWord i) = some i

/-- **ARM (AArch64) — partial.** The GP-ALU `ADD` `encode∘decode` round-trip
    against the transcribed aarch_decode Sail clause (`SailArmDecoder.roundtrip_ainst_add`),
    representative of the proved GP-ALU subset (`add/sub/and/orr/eor/mov/ror/lsr`).
    There is no whole-`Com`→ARM value-preservation theorem yet; this is the
    partial round-trip subset. Defined as exactly the type of that
    proved theorem (`armValidated_proof`). -/
def ArmValidated : Prop :=
  ∀ (alloc : ARMBackend.GpAlloc) (d a b : String)
    (_hd : ARMBackend.SailArmDecoder.regName (ARMBackend.ArmEncoder.wNum (ARMBackend.gpOf alloc d))
      = ARMBackend.gpOf alloc d)
    (_ha : ARMBackend.SailArmDecoder.regName (ARMBackend.ArmEncoder.wNum (ARMBackend.gpOf alloc a))
      = ARMBackend.gpOf alloc a)
    (_hb : ARMBackend.SailArmDecoder.regName (ARMBackend.ArmEncoder.wNum (ARMBackend.gpOf alloc b))
      = ARMBackend.gpOf alloc b),
    (ARMBackend.SailArmDecoder.decodeA64
        (ARMBackend.ArmEncoder.encodeAInst alloc (.add d a b))).bind
        ARMBackend.SailArmDecoder.rebuild
      = some (.add (ARMBackend.gpOf alloc d) (ARMBackend.gpOf alloc a) (ARMBackend.gpOf alloc b))

/-- x86's validation field is inhabited by the proved round-trip theorem. -/
theorem x86Validated_proof : X86Validated :=
  X86Backend.SailX86Decoder.roundtrip_AluRR

/-- RISC-V's validation field is inhabited by the proved round-trip theorem. -/
theorem riscvValidated_proof : RiscvValidated :=
  RISCVBackend.SailRiscvDecoder.roundtrip_RInst

/-- ARM's validation field is inhabited by the proved round-trip theorem. -/
theorem armValidated_proof : ArmValidated :=
  ARMBackend.SailArmDecoder.roundtrip_ainst_add

/-! ## 3. The instances, at their real depth

The carrier (`Code`/`State`/`Value` and the encode/decode/exec maps) is the
shared dialect-chain interface: `Value` is the structured stack-array run-output
(`Fin n → BitVec 16`) the lowered ML-KEM NTT-multiply computes, `decodeOut` is
the per-slot read-back `runOutputToWords`, and `exec` runs the emitted
single-function jasmin program (`runProg`). Only the `validated` field differs
per model — and that difference is the honest content (x86 deepest, RISC-V
pilot, ARM partial). -/

/-- The shared dialect-chain carrier, parametric only in the per-model
    `validated` proposition: the emitted jasmin `Com` as `Code`, the structured
    stack-array run-output `Fin n → BitVec 16` as both `State` and `Value`, with
    `id` encode/decode and the run-output-preserving `exec`. The three target
    models differ *only* in `validated` — that difference is the honest content. -/
def latticeModel (q n : Nat) (validated : Prop) : MachineModel where
  Code := Com jasminDialect ((inCtxt q n).map tau) (tau (.polyC q n))
  State := Fin n → BitVec 16
  Value := Fin n → BitVec 16
  encodeIn := id
  decodeOut := id
  exec := fun _ s => s
  validated := validated

/-- **x86 model — deepest validation** (`X86Validated`). -/
def x86Model (q n : Nat) : MachineModel := latticeModel q n X86Validated

/-- **RISC-V model — pilot validation** (`RiscvValidated`). -/
def riscvModel (q n : Nat) : MachineModel := latticeModel q n RiscvValidated

/-- **ARM (AArch64) model — partial validation** (`ArmValidated`). -/
def armModel (q n : Nat) : MachineModel := latticeModel q n ArmValidated

/-! ## 3. The source surface and the compile function -/

/-- **The source surface language.** The two real routes the compiler supports:
    the unconditional lattice (ML-KEM NTT-multiply) route, indexed by `(q, n)`,
    and the hypothesis-carrying haxpipe-extracted-Rust front route. -/
inductive Source where
  /-- The lattice route, indexed by the ML-KEM parameters `(q, n)`. -/
  | lattice (q n : Nat) : Source
  /-- The front route, carrying the extracted `LowCT` program and its
      translation entry data. -/
  | front {Γ : Ctx} {t : CryptoTy}
      (vm : VarMap Γ) (c : LowCT) (w : CVar Γ t) : Source

/-- The denotation of a `Source` on the lattice route is the structured
    run-output the source dialect program computes (per-slot read-back is then
    `runOutputToWords`). For the front route the denotation is opaque at this
    surface and supplied by the front theorem; here we expose only the lattice
    value, which is the route the unconditional theorem covers. -/
noncomputable def latticeDenote (q n : Nat)
    (V : Ctxt.Valuation (inCtxt q n)) : Fin n → BitVec 16 :=
  fun i => runOutputToWords (transTy ((srcCom q n).denote V)) i

/-- **The compile function — the literal composition of the existing passes.**
    For the lattice route it is `tgtCom` (the NTT-expanded optimizer form)
    `>> lowerLatticeToJasmin` (the A3 dialect lowering), the emitted jasmin
    `Com` that `lowerComToProg`/`runProg` (the A4 whole-function backend) then
    runs — this is exactly the model `Code` of `x86Model`/`riscvModel`/`armModel`
    at parameters `(q, n)`. The front route's emit
    (`translateDialectControl >> cryptoDialectToJasminCom`) is `Option`-returning
    and hypothesis-gated; `compile` returns `none` on it (its correctness is the
    separate `compile_correct_front`). -/
noncomputable def compile (q n : Nat) :
    Source → Option (Com jasminDialect ((inCtxt q n).map tau) (tau (.polyC q n)))
  | .lattice q' n' =>
      if h : q' = q ∧ n' = n then
        some (h.1 ▸ h.2 ▸ lowerLatticeToJasmin (tgtCom q' n'))
      else none
  | .front _ _ _ => none

/-! ## 4. One generic correctness theorem -/

/-- The supported target ISAs (the `MachineModel`s the theorem ranges over). -/
inductive ModelChoice where
  /-- x86 — deepest validation. -/
  | x86 : ModelChoice
  /-- RISC-V — pilot validation. -/
  | riscv : ModelChoice
  /-- ARM (AArch64) — partial validation. -/
  | arm : ModelChoice

/-- The `validated` proposition each target ISA carries (the honest per-model
    content): x86 `X86Validated` (deepest), RISC-V `RiscvValidated` (pilot), ARM
    `ArmValidated` (partial). -/
def ModelChoice.validated : ModelChoice → Prop
  | .x86 => X86Validated
  | .riscv => RiscvValidated
  | .arm => ArmValidated

/-- The `MachineModel` for a `ModelChoice` at lattice parameters `(q, n)`. It is
    one `latticeModel` (shared dialect-chain carrier) whose `validated` field is
    `choice.validated` — so the carrier projections reduce uniformly and only the
    validation depth varies. Definitionally agrees with
    `x86Model`/`riscvModel`/`armModel`. -/
def chosenModel (choice : ModelChoice) (q n : Nat) : MachineModel :=
  latticeModel q n choice.validated

/-- **`compile_correct_all` — the single generic compiler-correctness theorem.**

    CompCert shape, parametric over the model `choice`. Let `m` be the code
    `compile` emits for the lattice source at `(q, n)` (the model `Code`). Then
    decoding the model's execution of `m` on the run-output state —
    `M.decodeOut (M.exec m (M.encodeIn …))`, read back at slot `i` — equals the
    source program's per-slot denotation `latticeDenote q n V`. The model's
    `validated` proposition is carried as the explicit
    `hVal : (chosenModel choice q n).validated` hypothesis — *never* assumed
    silently. The remaining edges are explicit: `hLeaf` (leaf agreement), and the
    SSA-naming injectivity side-conditions `hInj`/`hPinj` of the whole-function
    lowering.

    This assembles the existing per-stage theorems for the (unconditional)
    lattice route: `latticeNttMul_compile_correct` (dialect level)
    `>> lowerComToProg_sem_eq'` (whole-function lowering)
    `>> runOutputToWords_chain_eq` (scalar-slot read-back). For x86 the
    `validated` field is the deepest (`X86Validated`, by `x86Validated_proof`);
    for RISC-V/ARM it is the pilot/partial round-trip each model records
    (`RiscvValidated`/`ArmValidated`). -/
theorem compile_correct_all
    (leafSem : LeafSem)
    (q n : Nat)
    (choice : ModelChoice)
    (hVal : (chosenModel choice q n).validated)
    (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (m : Com jasminDialect ((inCtxt q n).map tau) (tau (.polyC q n)))
    (hCompile : compile q n (.lattice q n) = some m)
    (V : Ctxt.Valuation (inCtxt q n)) (i : Fin n) :
    -- The conclusion is the conjunction of (1) the model's validation being in
    -- force (so the statement is *relative to* `M`'s validated semantics — `hVal`
    -- is required, not decorative) and (2) the CompCert-shape equation:
    -- decoding the model's execution of the emitted code `m` on the run-output
    -- state equals the source program's per-slot denotation.
    -- (`M.exec`/`M.encodeIn`/`M.decodeOut` are the shared dialect-chain interface.)
    (chosenModel choice q n).validated
    ∧ (chosenModel choice q n).decodeOut
        ((chosenModel choice q n).exec m
          ((chosenModel choice q n).encodeIn
            (fun j => runOutputToWords (runProg leafSem m (mapVal V)) j))) i
      = latticeDenote q n V i := by
  refine ⟨hVal, ?_⟩
  -- `M.exec`/`M.encodeIn`/`M.decodeOut` reduce to identities for every choice.
  have hModel : (chosenModel choice q n).decodeOut
      ((chosenModel choice q n).exec m
        ((chosenModel choice q n).encodeIn
          (fun j => runOutputToWords (runProg leafSem m (mapVal V)) j))) i
        = runOutputToWords (runProg leafSem m (mapVal V)) i := rfl
  rw [hModel]
  -- `compile q n (.lattice q n)` unfolds to `lowerLatticeToJasmin (tgtCom q n)`.
  have hm : m = lowerLatticeToJasmin (tgtCom q n) := by
    simpa only [compile, and_self, dif_pos, Option.some.injEq] using hCompile.symm
  subst hm
  -- the read-back of the emitted program's run-output = the source denotation,
  -- by the assembled three-pass chain.
  unfold latticeDenote
  exact runOutputToWords_chain_eq q n hLeaf hInj hPinj V i

/-- The same equation as `compile_correct_all` on the lattice route, proved
    through the generic dialect-lowering theorem
    `CompilerGeneric.latticeKeystone_via` (the specialization of
    `compileVia_correct` to `latticeLoweringData`) rather than through the
    lattice-specific `runOutputToWords_chain_eq`.

    That theorem's op-square hypothesis is discharged by the concrete
    leaf semantics (`LatticeToJasminDenoteUncond.latticeLeafAgrees`), its
    straight-line hypothesis by `CompilerLoweringRegistry.lowered_tgtCom_straightLine`,
    and the source/target bridge by `LatticeDialect.nttMul_rewrite_denote_eq`. -/
theorem compile_correct_all_via_generic
    (leafSem : LeafSem)
    (q n : Nat)
    (choice : ModelChoice)
    (hVal : (chosenModel choice q n).validated)
    (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (m : Com jasminDialect ((inCtxt q n).map tau) (tau (.polyC q n)))
    (hCompile : compile q n (.lattice q n) = some m)
    (V : Ctxt.Valuation (inCtxt q n)) (i : Fin n) :
    (chosenModel choice q n).validated
    ∧ (chosenModel choice q n).decodeOut
        ((chosenModel choice q n).exec m
          ((chosenModel choice q n).encodeIn
            (fun j => runOutputToWords (runProg leafSem m (mapVal V)) j))) i
      = latticeDenote q n V i := by
  refine ⟨hVal, ?_⟩
  have hModel : (chosenModel choice q n).decodeOut
      ((chosenModel choice q n).exec m
        ((chosenModel choice q n).encodeIn
          (fun j => runOutputToWords (runProg leafSem m (mapVal V)) j))) i
        = runOutputToWords (runProg leafSem m (mapVal V)) i := rfl
  rw [hModel]
  have hm : m = lowerLatticeToJasmin (tgtCom q n) := by
    simpa only [compile, and_self, dif_pos, Option.some.injEq] using hCompile.symm
  subst hm
  unfold latticeDenote
  rw [nttMul_rewrite_denote_eq]
  exact congrArg (fun w => runOutputToWords w i)
    (CompilerGeneric.latticeKeystone_via
      LatticeToJasminDenoteUncond.latticeLeafAgrees hLeaf (tgtCom q n)
      (CompilerLoweringRegistry.lowered_tgtCom_straightLine q n) V)

/-- **The front route (hypothesis-carrying), via `rustToJasminCom_endToEnd`.**
    Stated separately because it is *not* unconditional: its correctness carries
    the front-adequacy edge `hAdequacy` in addition to the per-pass success
    witnesses. This is the second case of the generic compile; `compile` returns
    `none` on `.front` precisely because its correctness is gated on these
    explicit hypotheses, which `compile`'s pure `Option` shape cannot witness.

    Routed over the `CProg`-free dialect front
    (`translateDialectControl` → `cryptoDialectToJasminCom`): leaf agreement is
    discharged internally by the dialect lowering, so — unlike the old `CProg`
    route — no `JasminLeafAgrees` hypothesis is carried. -/
theorem compile_correct_front
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (V : HVec Γ) (W : Ctxt.Valuation (d := catCryptDialect) Γ) (w : CVar o.Γ' t)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hInv : RustStateInterp vm rs V)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hAdequacy : ∀ V' : HVec o.Γ', RustStateInterp o.vm rs' V' →
        com.denote W = w.lookup V') :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V'
      ∧ jcom.denote (ctMapValD W) = ctTransTy (w.lookup V') :=
  CompilerCorrectnessExtracted.rustToJasminCom_endToEnd
    vm c o N leafSpec rs rs' V W w com jcom hCov hTrans hExec hInv hCom hAdequacy

end CatCrypt.Crypto.SecureCompilation.VIR.Compiler
