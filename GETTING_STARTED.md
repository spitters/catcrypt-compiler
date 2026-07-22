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
- **The certificate** is in the same file: `thirToJasmin_denote` proves the compiled
  IR denotes the source, and `com_riscv_e2e` proves the machine block computes that
  denotation for every supported program.

## Next

- [DEMO.md](DEMO.md) — the same routine plus the relational front (a Lean
  specification compiled by relational compilation), and the axiom audit.
- [EXAMPLES.md](EXAMPLES.md) — a curated set of buildable example modules.
- [FAQ.md](FAQ.md) — no CLI? how do I compile my own program? what is trusted?
- The manual — narrative and the headline theorems:
  `cd docs && lake build CompilerManual && lake exe compiler-manual --output _out`.
- [AxiomAudit.lean](AxiomAudit.lean) — the axioms the headline theorems rest on:
  `lake env lean AxiomAudit.lean`.
