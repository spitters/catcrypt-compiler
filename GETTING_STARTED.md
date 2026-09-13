# Getting started

## Build and run a first example

This needs the toolchain, read access to the private Veir dependency, and the
first-time setup from [BUILDING.md](BUILDING.md) (sections "Access to the Veir
dependency" and "First-time setup"). From the package root:

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
	mul w2, w1, w0
	add w3, w2, w1
	orr w4, w3, w3
```

## What just happened

- The source is `srcThir`, written by hand in the module as a term of the front's
  input type `ThirToComFront.Thir`. That is the type the package's translators from
  hax-lean's ASTs produce (`TExprToThir.texprToThir` from `Hax.TExpr`,
  `ImpExprToThir.impExprToThir` from `Hax.ImpExpr`). The package contains no Rust
  source for the routine, and the demo does not run hax.
- The front `thirToJasmin` lowers it at width 64 to the IR program `srcCom`; the
  module checks that the lowering succeeds with `native_decide` (`srcThir_lowers`).
- The backend compiles `srcCom` to the 64-bit AArch64 block `srcArm`, and
  `renderBBlockBody` prints it through the register map `demoAlloc`, which names
  the 32-bit views `w0`, `w1`, … of the registers. The printer carries no theorem.
- [DEMO.md](DEMO.md) states which theorems apply to this program.

## Next

- [DEMO.md](DEMO.md): the theorems behind this run, and the relational front (a
  Lean specification related to compiled code).
- [EXAMPLES.md](EXAMPLES.md): a set of buildable example modules.
- [bench.md](bench.md): measured performance of the emitted assembly against the
  deployed reference for each primitive.
- The manual, with the narrative:
  `cd docs && lake update && lake build CompilerManual && lake exe compiler-manual --output _out`.
- [AxiomAudit.lean](AxiomAudit.lean): prints the axioms of the theorems it lists,
  with `lake env lean AxiomAudit.lean`; [BUILDING.md](BUILDING.md#check-axioms)
  explains how to check another theorem.
