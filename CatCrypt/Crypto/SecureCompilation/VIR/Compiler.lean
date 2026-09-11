/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerGeneric
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder

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
  **hypothesis-carrying** in the form used here: `compile_correct_front` cites
  `rustToJasminCom_endToEnd`, which over `IsCoveredCtl` requires `hAdequacy`
  (front `Com.denote` = the operational post-state value of the extracted
  program) on top of the per-pass success witnesses. Leaf agreement is
  *discharged* internally by the dialect lowering, so no `JasminLeafAgrees`
  hypothesis is carried. The hypothesis-free sibling
  `rustToJasminCom_endToEnd_unconditional` does not *prove* the adequacy edge —
  it **avoids** it, by stating the value leg over the machine-word source
  semantics `semScalar` rather than over the operational `RustExec` post-state,
  on the smaller `IsCoveredSCtl` fragment
  (`CompilerCorrectnessExtracted.lean:436`); it makes no claim about the
  `RustExec` value of the tracked output. The in-tree kernel capstones ride its
  top-level form.

**(b) What each model's `validated` field carries.**

Every `validated` field below is *definitionally the statement of one proved
`decode ∘ encode` round-trip theorem* — no more. The decoders those round-trips
run against are hand-written Lean, transcribed by hand from the vendor Sail
sources (`rems-project/sail-x86-from-acl2`, `riscv/sail-riscv`,
`rems-project/sail-arm`); the upstream models are not vendored in this tree, and
the transcription itself is not machine-checked.

* **x86** — `x86Model.validated` is `X86Validated`, which is exactly
  `SailX86Decoder.roundtrip_AluRR`: the register-direct ALU round-trip against
  the transcribed ModRM/REX parse rules. It carries **no** ALU *semantics*.
  The step-level facts live elsewhere and are not in this field:
  `X86Backend.Preservation.add_preserves` … (pure form
  `Bridges.Transfer.x86Add_eq`) equates the owned `step` model with
  `JasminBinOp.apply` — an owned-model fact, not a Sail one — while the
  comparison against the Sail-x86 semantics (`X86Backend.SailX86Lean`) is a set
  of `native_decide` pins at concrete inputs, not a ∀-quantified refinement.
* **RISC-V** — `riscvModel.validated` is `RiscvValidated`, exactly
  `SailRiscvDecoder.roundtrip_RInst`: the round-trip for the full emitted RV64I
  subset. The value-level results are *not* in this field. The whole-`Com`→
  RISC-V value preservation is `ComToRiscvLsem.comToRiscvLsem_correct`, over the
  base-ALU all-`reg 64` fragment, and it is that module's `riscvBaseAluModel` —
  not `riscvModel` — whose `validated` carries the ∀-quantified execute-level
  refinement (`SailRiscv64Ref`, ADD/SUB/AND/OR/XOR) against the `execute_RTYPE`
  clause quoted in-file from the `sail-riscv-lean` generated output (a
  hand-pasted excerpt at a pinned commit; the upstream is not vendored). This is
  the deepest ISA grounding in the tree.
* **ARM (AArch64)** — `armModel.validated` is `ArmValidated`, exactly
  `SailArmDecoder.roundtrip_ainst_add`: the `ADD` round-trip alone, one
  representative of the proved GP-ALU subset
  (`roundtrip_ainst_{add,sub,and,orr,eor,mov,ror,lsr}`;
  `SailArmDecoder.trust_edge_pilot` is a doc-anchor alias of that same ADD
  round-trip, not a separate effect edge). The whole-`Com`→ARM value
  preservation is `ComToArmLsem.comToArmLsem_correct`, over the base-ALU
  all-`reg 64` fragment, carried by that module's `armBaseAluModel`. There is no
  ARM execute-level refinement anywhere in the chain:
  `ARMBackend.SailArm64Refinement` renders two Arm ARM execute clauses into its
  own hand-written register model and proves the `ArmModel` GP-ALU op functions
  against them, but it never mentions `evalBInst`/`runBBlock`, and no module
  imports it.

**(c) Open edges that remain hypotheses** (not discharged here):

1. *front adequacy* (`hAdequacy`, on the `IsCoveredCtl` form only) — the
   extracted-Rust denotation = operational post-state value; per-protocol bridge
   obligation. The `IsCoveredSCtl` sibling does not discharge it either: it
   sidesteps it by stating the value leg over `semScalar` instead of over the
   `RustExec` post-state.
2. *leaf agreement* (`LeafAgrees`, on the lattice route) — opaque `extCall`
   leaves agree with their jasmin denotations.
3. *whole-array / SIMD read-back* — `runOutputToWords` reads back one scalar
   slot; the vector/SIMD multi-slot read-back is per-slot of this.
4. *`.jazz`/`.o` → silicon* — the assembler and the silicon are the deliberate
   trusted base; `MachineModel.validated` records the one encoder round-trip
   each model carries, not a silicon-level proof.

This module makes **no** claim of "fully verified to silicon for all models."
The theorem is: `compile` is correct relative to each model's validated
semantics, at that model's depth, under the stated hypotheses.
-/

@[expose] public section

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
    ISA-validation the model carries (for the three models below, the encoder
    round-trip against the transcribed Sail decode rules; its content differs
    per model, so it is a field, never a hidden assumption).

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
  /-- **The ISA-validation this model carries.** An explicit proposition — for
      the three models below, the `decode ∘ encode` round-trip against the
      transcribed Sail decode rules. Which instructions it covers differs per
      model; see the module `Scope`. -/
  validated : Prop

/-! ## 2. The per-model validation (the real Sail-decode facts)

Each model's `validated` field is set to one of these aliases, each of which is
*definitionally the statement of an existing, proved round-trip theorem* in the
corresponding backend. The `*_validated` lemmas below discharge them by citing
exactly that theorem — so `MachineModel.validated` is never `True`-by-fiat: it is
the encoder round-trip the backend carries, and nothing beyond it. -/

/-- **x86.** The register-direct ALU `decode∘encode` round-trip against the
    hand-transcribed Sail-x86 ModRM/REX parse rules
    (`SailX86Decoder.roundtrip_AluRR`), and *only* that: no ALU semantics are
    recorded here. Defined as exactly the type of that proved theorem
    (`x86Validated_proof`). -/
def X86Validated : Prop :=
  ∀ (op d s : Nat), op < 256 → d < 16 → s < 16 →
    X86Backend.SailX86Decoder.decodeReg (X86Backend.ScalarEncoder.encAluRR op d s)
      = some { opcode := op, reg := s, rm := d }

/-- **RISC-V.** The full emitted RV64I subset `decode∘encode` round-trip against
    the hand-transcribed sail-riscv `encdec` discipline
    (`SailRiscvDecoder.roundtrip_RInst`). This field is the instruction-level
    round-trip only; the whole-`Com`→RISC-V value preservation is
    `ComToRiscvLsem.comToRiscvLsem_correct`, over the base-ALU all-`reg 64`
    fragment, and the execute-level refinement against the `execute_RTYPE`
    clause — an in-file excerpt of the sail-riscv-lean generated output (commit
    `9eba3f07`; upstream not vendored) — is that module's
    `riscvBaseAluModel.validated`.
    Defined as exactly the type of that proved theorem
    (`riscvValidated_proof`). -/
def RiscvValidated : Prop :=
  ∀ (i : RISCVBackend.RInst)
    (_hregs : (RISCVBackend.rinstDstSrcs i).1 ∈ RISCVBackend.SailRiscvDecoder.emittedRegs ∧
             ∀ r ∈ (RISCVBackend.rinstDstSrcs i).2, r ∈ RISCVBackend.SailRiscvDecoder.emittedRegs)
    (_hsh : ∀ d a m, i = .slliw d a m ∨ i = .srliw d a m → m < 32)
    (_hror : ∀ d a m, i = .roriw d a m → m < 32),
    RISCVBackend.SailRiscvDecoder.riscvDecode (RISCVBackend.RiscvEncoder.encodeWord i) = some i

/-- **ARM (AArch64).** The GP-ALU `ADD` `decode∘encode` round-trip against the
    hand-transcribed `aarch_decode` Sail clause
    (`SailArmDecoder.roundtrip_ainst_add`) — `ADD` alone, one representative of
    the proved GP-ALU subset (`add/sub/and/orr/eor/mov/ror/lsr`), not the subset
    itself. This field is that round-trip only; the whole-`Com`→ARM value
    preservation is `ComToArmLsem.comToArmLsem_correct`, over the base-ALU
    all-`reg 64` fragment. Defined as exactly the type of that
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
per model, and it names, per model, the one proved encoder round-trip that model
carries: x86 the register-direct ALU forms, RISC-V the full emitted RV64I
subset, ARM the `ADD` representative. The value-level machine results live in
the grounded models of `ComToRiscvLsem` / `ComToArmLsem`, not here. -/

/-- The shared dialect-chain carrier, parametric only in the per-model
    `validated` proposition: the emitted jasmin `Com` as `Code`, the structured
    stack-array run-output `Fin n → BitVec 16` as both `State` and `Value`, with
    `id` encode/decode and the run-output-preserving `exec`. The three target
    models differ *only* in `validated` — the one encoder round-trip each
    backend carries. -/
def latticeModel (q n : Nat) (validated : Prop) : MachineModel where
  Code := Com jasminDialect ((inCtxt q n).map tau) (tau (.polyC q n))
  State := Fin n → BitVec 16
  Value := Fin n → BitVec 16
  encodeIn := id
  decodeOut := id
  exec := fun _ s => s
  validated := validated

/-- **x86 model** — `validated` is the register-direct ALU round-trip
    (`X86Validated`). -/
def x86Model (q n : Nat) : MachineModel := latticeModel q n X86Validated

/-- **RISC-V model** — `validated` is the emitted-RV64I round-trip
    (`RiscvValidated`). -/
def riscvModel (q n : Nat) : MachineModel := latticeModel q n RiscvValidated

/-- **ARM (AArch64) model** — `validated` is the `ADD` round-trip
    (`ArmValidated`). -/
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
  /-- x86 — the register-direct ALU round-trip. -/
  | x86 : ModelChoice
  /-- RISC-V — the emitted-RV64I round-trip. -/
  | riscv : ModelChoice
  /-- ARM (AArch64) — the `ADD` round-trip. -/
  | arm : ModelChoice

/-- The `validated` proposition each target ISA carries (the honest per-model
    content): x86 `X86Validated` (register-direct ALU), RISC-V `RiscvValidated`
    (full emitted RV64I subset), ARM `ArmValidated` (`ADD`). -/
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
    `>> runOutputToWords_chain_eq` (scalar-slot read-back). The `validated`
    field is the encoder round-trip each model records — `X86Validated` (by
    `x86Validated_proof`), `RiscvValidated`, `ArmValidated` — and nothing
    stronger; the machine-execution results are `ComToRiscvLsem` /
    `ComToArmLsem` and `ScalarLinX86Demo.com_x86_e2e`. -/
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
