# Demo

The compiler is a Lean library rather than a command-line tool. A program enters
through a front (as a hax-lean AST, a LowCT term, the `Thir` input of the scalar
front, or a Lean specification), and compiling it means applying Lean functions to
it and building the module. This page states what is proved about two example
routes; [GETTING_STARTED.md](GETTING_STARTED.md) has the setup and the first run.
Theorem names are relative to the namespace `CatCrypt.Crypto.SecureCompilation`.

## Compiling a program to assembly

`CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo` writes the routine

```rust
fn f(a: u64, b: u64) -> u64 { let t = a.wrapping_mul(b); t.wrapping_add(a) }
```

by hand as a term `srcThir` of the front's input type `ThirToComFront.Thir`; the
package contains no Rust source for it, and the module does not run hax. The front
`thirToJasmin` lowers it to the `Com` program `srcCom`, and the backend compiles that
to the AArch64 block `srcArm`. [GETTING_STARTED.md](GETTING_STARTED.md) runs the
module and shows the three instructions it prints.

Two theorems cover the route the value takes; the module instantiates neither for
this program. `ThirToComFront.thirToJasmin_denote`: when the front succeeds on a
`Thir` term and the input valuation agrees with the front's initial state (`Agree`),
the `Thir` denotation equals the denotation of the output `Com`.
`ScalarLinNeutralDemo.com_arm_e2e`: for a straight-line `Com` over the supported
operations (`ComOK`) in a context of 64-bit registers, the block that the scalar
selection `ARMBackend.ComToArm.armTarget` compiles, run from a state whose registers
hold the inputs, leaves `Com.denote` in the result register. `srcCom` binds only the
64-bit multiply, add and or operations (the front copies a variable with `or`), all
of which `SupportedOp` lists, and `ARMBackend.ComToArm.regToBOp_denote` together
with `ScalarLin.ScalarTarget.compile_denote` equates running `srcArm` with the
`armTarget` run of the same program. No theorem in the package states
`ComOK srcCom`. The printed text is outside both theorems: it names the 32-bit views
`w0`, `w1`, … of the registers, and the printer carries no theorem.

`ARMBackend.ComToArmLsem.comToArmLsem_correct` restates the AArch64 result over the
`runBBlock` machine model on the base arithmetic-logic subset (`ADD`, `SUB`, `AND`,
`ORR`, `EOR`) and adds that every instruction of the block lies in that subset. The
demo's multiply is outside that subset. No theorem relates `runBBlock` to a Sail
execute clause; `ARMBackend/SailArmDecoder.lean` proves that the encoder's words
decode back to the encoded instructions under decode field splits transcribed by
hand from `sail-arm`, and that round trip is not part of `comToArmLsem_correct`.
`RISCVBackend.ComToRiscvLsem.comToRiscvLsem_correct` is the RISC-V counterpart. There
`RISCVBackend.ComToRiscvLsem.riscvStep64_sail_grounded` proves that, for each base
instruction, the model `evalRInst64` writes the value that an `execute_RTYPE` clause
writes, under an alignment of register names with register numbers; that clause
is copied by hand from the generated `sail-riscv-lean` model into
`RISCVBackend/SailRiscv64Refinement.lean`. The package vendors no Sail source.

## The relational front

The relational front starts from a Lean specification. An operation `op : A → A → A`
is given an injective encoding `enc` into 64-bit words and a commuting square
`enc (op a b) = bop (enc a) (enc b)` (`CatCrypt.Crypto.Bridges.ReprTransfer.EndoOpRealization`).
A `RelationalFront.RealizedKernel` pairs `bop` with a `Com jasminDialect` in the
`ComOK` fragment whose denotation is `bop` with its two arguments in reverse order,
and the backend theorems above apply to that `Com`. `CatCrypt.Crypto.SecureCompilation.RelationalFrontMachine` composes the
three steps. For addition in `ZMod 251`:

```lean
theorem addMod251_source_eq_arm (a b : ZMod 251)
    (s : BState) (hs : s.regs = envOf 2
      ((.cons (addMod251RealizedKernel.realization.enc b)
        (.cons (addMod251RealizedKernel.realization.enc a) .nil) :
          Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)))) :
    addMod251RealizedKernel.realization.enc ((fun x y : ZMod 251 => x + y) a b)
      = ((ComToArm.armTarget.runOps s
          (ComToArm.armTarget.compile (comToRegProg fieldAddMod251Com 2))).regs)
          (comRetName fieldAddMod251Com 2)
```

The encoded `ZMod 251` sum equals the result register of the AArch64 block that the
scalar selection compiles from `fieldAddMod251Com`, run from a state whose registers
hold the encoded operands. `addMod251_source_eq_riscv` is the RISC-V counterpart, and
`gf256Mul_source_eq_arm` and `gf256Mul_source_eq_riscv` state the same for the
GF(2⁸) multiply. `fieldAddMod251Com` is a `Com` written by hand and proved to denote
`bop` (`FieldEmitGoldenAddMod.fieldAddMod251Com_denote`); the relational front does
not generate it. Build with:

```bash
lake build CatCrypt.Crypto.SecureCompilation.RelationalFrontMachine
```

`CatCrypt.Crypto.SecureCompilation.RelationalFrontCurve25519` works at the value
level. `RelationalFront.c25519_add_commutes` and `RelationalFront.c25519_mul_commutes`
prove that addition and multiplication in `ZMod (2²⁵⁵ − 19)`, encoded as four 64-bit
limbs (`encMLK`), agree with the Lean list functions `mlAddModK` and `mlMulMod`. The
module builds no `Com` and no machine code, and the 255-bit field has no
`RealizedKernel`, whose carrier is a single 64-bit word.

## Headline theorems

Each theorem below is stated at the level named. [README.md](README.md#the-guarantees)
gives the fragments and hypotheses in full.

- [`VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd`](CatCrypt/Crypto/SecureCompilation/VIR/CompilerCorrectnessExtracted.lean):
  LowCT to the Jasmin `Com` denotation. For a LowCT source in `IsCoveredCtl` (no
  data-dependent `while`), given the front's value adequacy as the hypothesis
  `hAdequacy`, a `RustExec` run, a related entry state and the success of each pass,
  the Jasmin `Com` denotes the value that a valuation related to the post-state holds
  in the tracked output. The sibling
  `rustToJasminCom_endToEnd_unconditional` has no adequacy hypothesis and states that
  value over the machine-word semantics `semScalar`, in which an opaque leaf call
  returns a default value.
- [`VIR.RobustCompilationPipeline.robustCompilation_source_to_x86`](CatCrypt/Crypto/SecureCompilation/VIR/RobustCompilationPipeline.lean):
  the lattice dialect, whose NTT model is the identity, lowered to Jasmin and composed
  with an abstract x86 side. The x86 observable, behaviour and constant-time predicate
  are parameters, and both conjuncts of the conclusion are the `semRefine` and
  `ctPreserve` fields of the hypothesis `JasminVerifiedCompiler`, applied to the
  evaluator-level result and the `Com`-level constant-time result. The statement
  contains no x86 instruction semantics; the package's one instance,
  `VIR.OwnedX86RobustInstance.ownedJasminVerifiedCompiler`, uses the evaluator result
  and `True`. Leaf agreement and SSA-naming injectivity are further hypotheses.
- [`VIR.LoweringDataComp.compileVia_comp_correct`](CatCrypt/Crypto/SecureCompilation/VIR/LoweringDataComp.lean):
  the Jasmin-IR evaluator. For a program lowered through two dialect lowerings to
  Jasmin (`d → d' → jasmin`), `runProg` on the lowered program computes the composite
  transport of the source denotation, given the per-operation transport hypotheses of
  each lowering, leaf agreement, and a straight-line lowered program. The
  single-lowering case is `VIR.CompilerGeneric.compileVia_correct`.
  `VIR.Compiler.compile_correct_all` states the lattice route over the `MachineModel`
  interface; for the lattice model `exec`, `encodeIn` and `decodeOut` are identities,
  so its equation is at the evaluator level.
- [`ScalarLinX86Demo.com_x86_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinX86Demo.lean):
  machine code. For a straight-line `Com` over `ComOK` in a context of 64-bit
  registers, with shift amounts in range (`ShiftAmtOK`), running the ops of the
  scalar selection `x86Target` (`x86Target.runOps ∘ x86Target.compile`) leaves the
  source `Com`'s denotation in the result register. The x86 assembly that the owned
  exporters write comes from other routes, ending in AT&T text printers, that this
  theorem does not cover ([README.md](README.md#limitations)). `comToArmLsem_correct` and
  `comToRiscvLsem_correct` are the AArch64 and RISC-V statements on the base
  arithmetic-logic subset.

[README.md](README.md#limitations) lists the hypotheses the pipeline carries, the
predicates that are the constant `True`, and the package's declared axioms;
`lake env lean AxiomAudit.lean` prints the axioms of the theorems that file lists, and
[BUILDING.md](BUILDING.md#check-axioms) explains how to check another theorem.

## The manual

```bash
cd docs && lake update && lake build CompilerManual && lake exe compiler-manual --output _out
```
