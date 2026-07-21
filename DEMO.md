# Demo

Concrete commands, run from the package root. The first `lake build` compiles the
dependencies; see [BUILDING.md](BUILDING.md) for setup. The headline theorems these
touch are described in the manual's "Headline theorems" section.

## The correctness capstones and their trusted base

```bash
lake env lean AxiomAudit.lean
```

Prints the axiom set behind the three headline theorems — the generic compiler
correctness, the Rust front's source-to-Jasmin end-to-end result, and the robust
source-to-x86 compilation.

## Emit one kernel to three backends

```bash
lake build CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
```

One `Com` front lowered to x86-64, AArch64, and RISC-V; the module's theorems state
the emitted code agrees with the source on each backend.

## Emit machine bytes

```bash
lake build CatCrypt.Crypto.SecureCompilation.X86Backend.GoldenPathByteIdentityDemo
```

Emits a kernel through the golden path and inspects its byte encoding.

## Import a hand-written Jasmin leaf

```bash
lake build CatCrypt.Crypto.Jasmin.Examples.JincParserDemo
```

Parses a `.jinc` leaf into the IR and inspects it — the import-from-Jasmin direction.

## Orchestration over emitted arithmetic leaves

```bash
lake build CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample
```

A Curve25519 accumulation orchestrated over emitted field leaves.

## Build the manual

```bash
cd docs && lake build CompilerManual && lake exe compiler-manual --output _out
```

Open `docs/_out/html-single/index.html`.
