# Rewrite: rewrite saturation and the algebraic rewrite library

Index for optimizing a `Com` up to proven equivalence. Search here before adding a
rewrite pass, a program-search heuristic, or a selector that picks the fastest of
several equivalent implementations.

## Engine

- `Egraph.lean`: `saturateCom fuel c k` over `Com jasminDialect`.
  `saturateCom_denote` states that the output denotes the same function as the
  input for a known-constant environment consistent with the valuation.
  `comCost`/`opCost` is the cost model (multiply expensive, shift cheap), and
  `saturate_cost_le` states that the rewritten `Com` costs no more than the input.
  The engine applies rewrite rules up to a fuel bound and stops at a local fixpoint;
  it has no union-find and no e-classes, and it does not find a global cost minimum.
- `ComPipeline.lean`: `comAlgebraicPipeline` runs `Peephole.peepCom` and then
  `saturateCom`; `comAlgebraicPipeline_denote` composes the two preservation
  theorems.
- `ProofCarryingExtraction.lean`: generic over any `f : α → β` (`RewriteStep`,
  `RewriteChain`, `RewriteWitness`, `optimizeChecked`). An untrusted extractor
  returns a witness, and `optimizeChecked_denote` checks it. `ComWitness` and
  `saturateWitness` instantiate it for `Com`.
- `MultiplyMethodSelect.lean`: cost-minimum choice over a listed set of multiply
  methods proved equal (`select_cost_min`, `select_denote_eq`).
- `EgraphGlobalMin.lean`: an explicit e-class `EClass f`, a representative plus
  members, each member carrying a `RewriteWitness` to the representative.
  `extractMin` returns the cheapest member; `extractMin_cost_min` states its cost is
  at most that of every member, and `extractMin_denote_eq` that it denotes the
  representative. On the multiply-method families, `mul2Selected` and `mul3Selected`
  recover the choices of `selectMul2` and `selectMul3`.
- `RegistryEgraphBridge.lean`: bridge to the `Related` registry
  (`Transfer.Base.Related`, from ParamTransfer).
- `../TranslationValidationEgraph.lean` accepts a candidate structurally equal to the
  output of `comAlgebraicPipeline` (`tvCheckCanon_sound`).

## Cost models

`../X86CostModel.lean`, `../InOrderCostModel.lean` (cycle-level),
`../RandomizedScheduleSearch.lean`, `../JointScheduleRegAlloc.lean`.

## Rewrite library

Each module proves algebraic identities as equations, usable as rewrite rules:

- Multiply: `MultiplyMethodEquiv` (schoolbook, Karatsuba and Toom-3 equal the
  product), `KaratsubaGenericPass`, `Toom3GenericPass`.
- Reduction: `MontgomeryMulGeneric`, `MontgomeryRedcGeneric`, `MontDomainElimPass`,
  `MontgomeryTransport` (Montgomery-domain transport for NTT arithmetic),
  `BarrettMulGeneric`, `BarrettReduceGeneric`, `CrtGeneric`, `RadixDecompGeneric`.
- Inverse: `ModInverseGeneric`, `FermatInverseGeneric`, `BatchInverseGeneric`.
- Exponent and scalar multiplication: `ModPowGeneric`, `MonoidPowLadderPass`,
  `WindowedScalarMulGeneric`.
- Field structure: `FieldSqrtGeneric` (modular square roots), `LegendreSymbolGeneric`
  (quadratic-residue test), `FrobeniusGeneric` (the Frobenius endomorphism).
- Evaluation and sums: `LagrangeInterpGeneric` (Lagrange interpolation),
  `LinearCombGeneric` (linear-combination and inner-product evaluation).
- Field peephole: `FieldHornerPass`, `FieldStrengthReducePass`, `NegElimPass`,
  `Peephole`. Constant folding, common subexpressions and dead bindings of field code
  are rules and stages of the generic e-graph (`AegraphField`, `TraitRules`) and
  `NFProg.dce`.
- Canonicalization: `AbsentRewrites` (`neg (neg x) = x` on `BitVec`,
  `fromMont ∘ toMont = id` over `ZMod p`, `reverse ∘ reverse = id` for bit
  reversal).
- NTT algebra: `../Lattice/NTTConvolutionTheorem.lean` (the DFT is multi-point
  polynomial evaluation; convolution theorem).

## Levels

- Rewrite saturation, present: `Egraph.lean`, `ComPipeline.lean`. Monotone cost
  descent with a denotation proof per step.
- Minimum extraction over an explicit class, present: `EgraphGlobalMin.lean` for an
  e-class whose members are listed with their certificates, and
  `MultiplyMethodSelect.lean` for a finite list.
- Union-find saturation, not present: non-destructive sharing and congruence closure
  that would fill an e-class from the rewrite rules instead of an enumerated list.
  The section "Scope: finite-set cost-minimum with a certificate" of
  `MultiplyMethodSelect.lean` lists what it adds.

## Selection targets

- Field multiply and reduction: the equivalences (`MultiplyMethodEquiv`, the
  Montgomery and Barrett generics) exist. `EgraphGlobalMin` derives the
  multiply-method choice through `extractMin`; the CIOS/Barrett choice `preferCios`
  (`../../SecureCompilation/RelationalFrontCiosSelect.lean`) is a hand-written cost
  comparison.
- Modular inverse, scalar multiplication, exponentiation: the generics above.
- NTT: `../Lattice/NttEmitDenotationBridge.lean` proves that the ML-KEM
  butterfly-stage sequence, as a value model, equals `nttIter`
  (`nttIter_succ_eq_ctMergeStage`), `dft` (`IterativeNttEqRec.mlkem_nttIter_eq_dft`)
  and polynomial evaluation. No theorem relates the `.jazz` text that
  `../../SecureCompilation/VIR/LatticeNttEmit.lean` renders
  (`emitMlkemNttFull16wayJazz`) to the value model; that module's lane-independence
  theorems are instantiated at the per-lane block `id`.
