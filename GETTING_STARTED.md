# Getting started

## Build and run a first example

This needs the toolchain and the first-time setup from [BUILDING.md](BUILDING.md)
(section "First-time setup"). From the package root:

```bash
lake build CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo   # the demo and its import closure
lake env lean CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean
```

`lake build <module>` builds that module's import closure and nothing else; the full
`lake build` is not needed for the demo. `lake env lean` runs Lean in the workspace
environment and builds nothing, so the second command needs the first. It elaborates
the module and prints AArch64 assembly for the routine
`fn f(a: u64, b: u64) -> u64 { let t = a.wrapping_mul(b); t.wrapping_add(a) }`:

```
	mul x2, x1, x0
	add x3, x2, x1
	orr x4, x3, x3
```

## What just happened

- The source is `srcThir`, written by hand in the module as a term of the front's
  input type `ThirToComFront.Thir`, the type that the translators from hax-lean's
  ASTs produce (`TExprToThir.texprToThir` from `Hax.TExpr`,
  `ImpExprToThir.impExprToThir` from `Hax.ImpExpr`). The demo does not run hax.
- The front `thirToJasmin` lowers it at width 64 to the Jasmin-dialect program
  `srcCom`; `srcThir_lowers` checks that the lowering succeeds.
- The backend compiles `srcCom` to the AArch64 block `srcArm`, and
  `renderBBlockBody` prints it through the register map `demoAlloc` (`x0`, `x1`, …).
- `srcArm_correct`, an instance of `com_arm_e2e` through `srcCom_ok : ComOK srcCom`,
  proves that running `srcArm` from registers holding the inputs leaves the
  denotation of `srcCom` in the result register.
- [DEMO.md](DEMO.md) states the theorems behind this route.

## Next

- [DEMO.md](DEMO.md): the theorems behind this run, and the relational front (a
  Lean specification related to compiled code).
- [PIPELINE.md](PIPELINE.md): the hax compiler `compileA` from a hax module to x86-64
  bytes, and [BUILDING.md](BUILDING.md#run-the-hax-compiler) to run it on a Rust crate.
- [EXAMPLES.md](EXAMPLES.md): a set of buildable example modules.
- [NAVIGATION.md](NAVIGATION.md): where each subsystem lives and its main theorem.
- [bench.md](bench.md): performance ratios against production implementations.
- The [manual](docs/CompilerManual.lean); [BUILDING.md](BUILDING.md#generate-the-documentation)
  builds it.
- [AxiomAudit.lean](AxiomAudit.lean): prints the axioms of the theorems it lists;
  [BUILDING.md](BUILDING.md#check-axioms) runs it and explains how to check another
  theorem.
