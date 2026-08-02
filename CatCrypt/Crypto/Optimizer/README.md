# Optimizer — verified Com optimizer + register allocator

Role: the compiler's optimization and register-allocation passes over the `Com`
IR — each a Lean function proved to preserve denotation, so optimizing is one
more use of the same denotation-preserving relation that drives compilation.
Part of the `CatCryptCompiler` build target (with `SecureCompilation` + `Jasmin`).

## What lives here
- **Com rewrites:** `ComCSE`, `ComDCE`, `ConstFold`, `CopyProp`, `ComCanonical`,
  `BarrettReduce`, composed in `ComOptPipeline` / `ComFullOpt` / `ComCleanupPipeline`.
- **Register allocation:** `GenericRegAlloc(Validated/Sim)`, `GraphColoringRegAlloc`,
  `GraphColoringCoalesce`, `JInstrRegAllocScoped`, with `FootprintSpill` +
  `InOrderCostModel`.
- **E-graph / equality-saturation:** `EgraphOracle`, `EgraphSelectDemo`, and the
  `Rewrite/` subtree — a proof-carrying `saturateCom` over `Com`, a cost model, and
  a library of verified algebraic-equivalence rewrites (multiply methods,
  Montgomery/Barrett reduction, inverse, scalar-mul). See `Rewrite/AGENTS.md` for
  the index, the two levels (greedy descent vs global-min extraction), and the
  optimize-up-to-equivalence targets.

See `ARCHITECTURE.md` and `sec:techniques` in the compiler paper for how these
passes compose; the denotation-preservation obligation is the invariant every
pass discharges.
