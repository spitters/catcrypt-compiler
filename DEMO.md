# Demo

The compiler is a Lean library. A program enters through a front (a hax-lean AST, a
LowCT term, the `Thir` input of the scalar front, or a Lean specification), and
compiling it means applying Lean functions to it and building the module. This page
states the theorems behind two routes; [GETTING_STARTED.md](GETTING_STARTED.md) has
the setup and the first run. The hax compiler `compileA`, which compiles a hax module
to x86-64 bytes, is described in [PIPELINE.md](PIPELINE.md), and
[BUILDING.md](BUILDING.md#run-the-hax-compiler) runs its executable `haxc`. Theorem
names are relative to the namespace `CatCrypt.Crypto.SecureCompilation`.

## Compiling a program to assembly

`CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo` writes the routine

```rust
fn f(a: u64, b: u64) -> u64 { let t = a.wrapping_mul(b); t.wrapping_add(a) }
```

as a term `srcThir` of the front's input type `ThirToComFront.Thir`. The front
`thirToJasmin` lowers it to the Jasmin-dialect program `srcCom`, and the AArch64
backend compiles that to the block `srcArm`. [GETTING_STARTED.md](GETTING_STARTED.md)
runs the module and shows the instructions it prints (`mul x2, x1, x0`,
`add x3, x2, x1`, `orr x4, x3, x3`).

`CompilerHelloDemo.srcArm_correct` states, for every input valuation `V` and machine
state whose virtual registers `v0 … v(n-1)` hold `V`, that running `srcArm` under
`runBBlock` leaves `Com.denote srcCom V` in the virtual result register. It instantiates `com_arm_e2e` with
`srcCom_ok : ComOK srcCom`.

The front and the backend carry these general theorems:

- `ThirToComFront.thirToJasmin_denote`: when the front succeeds on a `Thir` term and
  the input valuation agrees with the front's initial state (`Agree`), the `Thir`
  denotation equals the denotation of the output `Com`.
- `ScalarLinNeutralDemo.com_arm_e2e`: for a straight-line `Com` over the supported
  operations (`ComOK`) in a context of 64-bit registers, the block that the scalar
  selection `ARMBackend.ComToArm.armTarget` compiles, run in a register model whose
  registers are named by strings from virtual registers holding the inputs, leaves
  `Com.denote` in the virtual result register; no register is allocated.
- `ARMBackend.ComToArmLsem.comToArmLsem_correct` restates the AArch64 result over the
  `runBBlock` machine model on the base arithmetic-logic subset (`ADD`, `SUB`, `AND`,
  `ORR`, `EOR`). `RISCVBackend.ComToRiscvLsem.comToRiscvLsem_correct` is the RISC-V
  counterpart, and `RISCVBackend.ComToRiscvLsem.riscvStep64_sail_grounded` equates the
  destination value of each base instruction step with that of an `execute_RTYPE` clause
  copied from the `sail-riscv-lean` model, under an alignment of the string-named
  register file with the 32 Sail registers.

## The relational front

The relational front starts from a Lean specification. An operation `op : A → A → A`
receives an injective encoding `enc` into 64-bit words and a commuting square
`enc (op a b) = bop (enc a) (enc b)` (`CatCrypt.Crypto.Bridges.ReprTransfer.EndoOpRealization`).
A `RelationalFront.RealizedKernel` pairs `bop` with a `Com jasminDialect` in the
`ComOK` fragment whose denotation is `bop` with its two arguments in reverse order,
and the backend theorems above apply to that `Com`.
`CatCrypt.Crypto.SecureCompilation.RelationalFrontMachine` composes the three steps.
For addition in `ZMod 251`:

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
scalar selection compiles from `fieldAddMod251Com`, run from registers holding the
encoded operands. `addMod251_source_eq_riscv` is the RISC-V counterpart, and
`gf256Mul_source_eq_arm` and `gf256Mul_source_eq_riscv` state the same for the
GF(2⁸) multiply. `fieldAddMod251Com` is a `Com` written in Lean and proved to denote
`bop` (`FieldEmitGoldenAddMod.fieldAddMod251Com_denote`). The module is listed in
[EXAMPLES.md](EXAMPLES.md), which gives the build command.

`CatCrypt.Crypto.SecureCompilation.RelationalFrontCurve25519` states the value-level
squares for a multi-limb field: `RelationalFront.c25519_add_commutes` and
`RelationalFront.c25519_mul_commutes` prove that addition and multiplication in
`ZMod (2²⁵⁵ − 19)`, encoded as four 64-bit limbs (`encMLK`), agree with the Lean list
functions `mlAddModK` and `mlMulMod`.

## Headline theorems

[README.md](README.md#the-guarantees) tabulates the headline theorems with their
level and fragment, and [HEADLINES.md](HEADLINES.md) states each with its
hypotheses. [BUILDING.md](BUILDING.md#check-axioms) prints the axioms of a theorem, and
[BUILDING.md](BUILDING.md#generate-the-documentation) builds the
[manual](docs/CompilerManual.lean).
