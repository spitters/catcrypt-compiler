# Getting started

## Compile a program in one command

From the package root:

```bash
lake env lean CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean
```

This compiles a Rust routine — `fn f(a, b) { let t = a * b; t + a }`, extracted by
hax and lowered through the front — to AArch64, and prints the emitted assembly:

```
	mul w2, w1, w0
	add w3, w2, w1
	orr w4, w3, w3
```

The first run builds the dependencies (mathlib and the CatCrypt libraries); after
that it is fast. See [BUILDING.md](BUILDING.md) for the toolchain and dependencies.

## What just happened

- **The source** is a Rust function; hax extracts it and the front (`thirToJasmin`)
  produces the compiler's IR — programs enter through a front, never as hand-written
  IR.
- **The output** is the AArch64 block held by `srcArm` in the module, rendered to
  text by the assembly printer.
- **The certificates** are the theorems [DEMO.md](DEMO.md) walks through.

## Next

- [DEMO.md](DEMO.md) — what this run proves, plus the relational front (a Lean
  specification compiled by relational compilation).
- [EXAMPLES.md](EXAMPLES.md) — a curated set of buildable example modules.
- [bench.md](bench.md) — measured performance of the emitted assembly against the
  deployed reference for each primitive.
- The manual — narrative and the headline theorems:
  `cd docs && lake build CompilerManual && lake exe compiler-manual --output _out`.
- [AxiomAudit.lean](AxiomAudit.lean) — the axioms the headline theorems rest on:
  `lake env lean AxiomAudit.lean`.
