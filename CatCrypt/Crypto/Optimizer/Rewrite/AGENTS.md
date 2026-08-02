# Rewrite — verified equality-saturation + algebraic rewrite library

Index for the "optimize a `Com` up to proven equivalence" subsystem. Grep here
before adding a rewrite pass, a program-search heuristic, or a "pick the fastest
implementation" selector — the substrate below already exists over the compiler
IR, not just as a quantum-diagram demo.

## Engine (proof-carrying)

- `Egraph.lean` — `saturateCom fuel c k` over `Com jasminDialect`.
  `saturateCom_denote` proves the output denotes the same function as the input.
  `comCost`/`opCost` is the cost model (`mul` expensive, shift cheap);
  `saturate_cost_le` proves each step is cost-non-increasing. This is a
  rewrite-saturation engine: greedy cost descent, no union-find, no e-classes, so
  it does **not** extract a global cost minimum (see "Two levels").
- `ProofCarryingExtraction.lean` — generic over any `f : α → β`
  (`RewriteStep`/`RewriteChain`/`RewriteWitness`/`optimizeChecked`). An untrusted
  extractor emits a witness (its explanation); `optimizeChecked_denote` checks it
  against the kernel. The untrusted-search / checked-result boundary.
  `ComWitness`/`saturateWitness` instantiate it for `Com`.
- `RegistryEgraphBridge.lean`, `EgraphGrindIntegration.lean` — bridges to the
  `Related` registry and to `grind`.
- `../../Bridges/Quantum/ZXEgraph.lean` instantiates the same `Related`/
  `RelatedBinOp` machinery for ZX diagrams — the framework is term-language-agnostic.

## Cost models

`../X86CostModel.lean`, `../InOrderCostModel.lean` (cycle-level),
`../RandomizedScheduleSearch.lean`, `../JointScheduleRegAlloc.lean`.

## Rewrite library (leaf equivalences, proved as equations — not KAT)

Each is an algebraic identity proved as an equation, usable as a saturation rule:

- Multiply: `MultiplyMethodEquiv` (schoolbook / Karatsuba / Toom-3 = product),
  `KaratsubaGenericPass`, `Toom3GenericPass`.
- Reduction: `MontgomeryMulGeneric`, `MontgomeryRedcGeneric`, `MontDomainElimPass`,
  `BarrettMulGeneric`, `BarrettReduceGeneric`, `CrtGeneric`, `RadixDecompGeneric`.
- Inverse: `ModInverseGeneric`, `FermatInverseGeneric`, `BatchInverseGeneric`.
- Exponent / scalar-mul: `ModPowGeneric`, `MonoidPowLadderPass`,
  `WindowedScalarMulGeneric`.
- Field peephole: `FieldConstFoldPass`, `FieldCsePass`, `FieldHornerPass`,
  `FieldStrengthReducePass`, `FieldLetDcePass`, `NegElimPass`, `Peephole`.
- NTT algebra: `../Lattice/NTTConvolutionTheorem.lean` (DFT = multi-point
  polynomial evaluation; convolution theorem).

## Two levels

- **Level 1 (present):** rewrite-saturation with monotone cost descent and a
  per-step denotation proof — apply verified rewrites, never get slower, carry the
  proof.
- **Level 2 (not built):** a union-find e-graph with non-destructive sharing and
  global cost-minimum extraction — required to consider all equivalent
  implementations and select the globally fastest. `Egraph.lean` records this as
  the delta. It reuses the cost models above and `ProofCarryingExtraction` for the
  certificate.

## Targets for "choose the fastest up to equivalence"

- **Field multiply / reduction** is the readiest: the equivalences
  (`MultiplyMethodEquiv`, the Montgomery/Barrett generics) and a manual selector
  (`../../SecureCompilation/RelationalFrontCiosSelect.lean`, `preferCios`) already
  exist, so Level-2 extraction generalizes a selection that is currently hand-written.
- **Modular inverse, scalar-mul, exponentiation** — the generics above.
- **NTT** emit correctness currently rests on a byte-KAT (the emit carries an `id`
  denotation placeholder in `../../SecureCompilation/VIR/LatticeNttEmit.lean`).
  Bridging the emit to `NTTConvolutionTheorem` replaces the KAT with a proof; this
  is the one arithmetic primitive still test-gated rather than equation-backed.
