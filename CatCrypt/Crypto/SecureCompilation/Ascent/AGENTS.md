# Ascent: contributor guide

The ascent proves that a program at one of the compiler's low levels (a `LowCT`
command, an x86 or RV64 instruction list, x86 bytes) computes a Lean specification.
[ASCENT.md](../../../../ASCENT.md) explains the calculus and traces a capstone. This
file gives the names, the entry modules, the choice of tactic and the rules for
editing here. Modules are in the namespace `CatCrypt.Crypto.SecureCompilation.Ascent`,
demonstrations in `…Ascent.Demos`.

## Names

The vocabulary follows [sgraf812/ascent](https://github.com/sgraf812/ascent) and
AutoCorres.

- `Corres` is the correspondence relation over `semScalar`. Variants carry a suffix
  for the machine or shape: `CorresU` (`semU`), `CorresWhile`, `CorresJ` (`runBlock`
  over `JState 64`), `CorresR` (`runRBlock64`), `CorresM` (any step function),
  `CorresMPost`, `CorresH`, `CorresE`, `CorresUE`. Lemmas take the matching prefix
  (`corres_`, `corresU_`, `corresJ_`, `corresR_`, `corresM_`, `corresH_`).
- State relations start with `SR` (`SRword`, `SRwordNT`, `SRwordBV`, `SRarr`,
  `SRcarry`, `SRx`, `SRr`, the generic `SRof`); abstract states start with `A`.
- A leaf is named after what it refines: `corres_setExpr`, `corres_arrStore`,
  `corresJ_sbb`, `corresJ_addX`, `corresR_add`.
- Decidable fragments: `IsAscendable`, `IsAscendableExpr`, `IsAscendableBitwise`,
  with specifications `asemW`, `asemWExpr`, `asemWBV`. A `Bool` checker ends in `B`
  and has a `*B_sound` lemma.
- Welds to the emit leg: `corres_emit_weld` and the `keystone_*` family (called emit
  welds in prose). Capstones end in `_endToEnd`, `_source_to_bytes` or `_capstone`;
  their "bytes" is a `Com jasminDialect` denotation.
- Hypothesis names: `hCorres`, `hSR`, `hP`, `hAgree`, `hEmit` (an emit equation),
  `hBridge` (a source word identified with the kernel's word).

## Entry modules

| Area | Modules |
|---|---|
| Relations | [`Corres`](Corres.lean), [`CorresGeneric`](CorresGeneric.lean), [`RunBlockCorres`](RunBlockCorres.lean), [`CorresRiscv`](CorresRiscv.lean), [`While`](While.lean), [`WhileTop`](WhileTop.lean), [`HeapAbs`](HeapAbs.lean), [`Phases`](Phases.lean) |
| `LowCT` leaves and control | [`ExprLeaf`](ExprLeaf.lean), [`CorresScalar`](CorresScalar.lean), [`SelectLeaf`](SelectLeaf.lean), [`ArrLoadLeaf`](ArrLoadLeaf.lean), [`ArrStoreLeaf`](ArrStoreLeaf.lean), [`Control`](Control.lean), [`Exit`](Exit.lean) |
| Automation | [`Ascend`](Ascend.lean), [`AscendDecide`](AscendDecide.lean), [`AscendMeta`](AscendMeta.lean), [`Guards`](Guards.lean), [`GuardsLeaf`](GuardsLeaf.lean), [`Strengthen`](Strengthen.lean), [`CorresSymEngine`](CorresSymEngine.lean), [`CorresSolver`](CorresSolver.lean), [`CorresX86Solver`](CorresX86Solver.lean), [`CorresRiscvSolver`](CorresRiscvSolver.lean), [`CorresSymScalar`](CorresSymScalar.lean), [`MontBounds`](MontBounds.lean) |
| Multi-limb and field results | [`EcMultiLimbCapstone`](EcMultiLimbCapstone.lean), [`EcMultiLimbMul`](EcMultiLimbMul.lean), [`MpnAdxCorres`](MpnAdxCorres.lean), [`FieldReduce`](FieldReduce.lean), [`CapstoneField`](CapstoneField.lean) |
| Ties between machines | [`CorresMachineTie`](CorresMachineTie.lean), [`JasminComRunBlockTie`](JasminComRunBlockTie.lean), [`XrunRunBlockTie`](XrunRunBlockTie.lean), [`CorresHoare`](CorresHoare.lean), [`RunBlockMvcgen`](RunBlockMvcgen.lean), [`JStateSepLogic`](JStateSepLogic.lean) |
| Descent contracts | [`CorresDescentX86`](CorresDescentX86.lean), [`CorresDescentRiscv`](CorresDescentRiscv.lean) |
| Welds and capstones | [`EmitBridge`](EmitBridge.lean), [`LegWeld`](LegWeld.lean), [`LegWeldDemo`](LegWeldDemo.lean), [`FeSubEndToEnd`](FeSubEndToEnd.lean), [`FeAddEndToEnd`](FeAddEndToEnd.lean), [`KeystoneControl`](KeystoneControl.lean), [`PipelineWeld`](PipelineWeld.lean), [`SourceBridge`](SourceBridge.lean) |
| Loops as functions | [`WhileFun`](WhileFun.lean), [`WhileFunEmit`](WhileFunEmit.lean), [`Demos/WhileFunSum`](Demos/WhileFunSum.lean) |
| Imported blocks | [`AddrMem`](AddrMem.lean), [`Demos/Ed25519PointAddBytes`](Demos/Ed25519PointAddBytes.lean), [`Demos/S2nMontmulP384Proof`](Demos/S2nMontmulP384Proof.lean) |
| Demonstrations | [`Demos/Decide`](Demos/Decide.lean), [`Demos/Scalar`](Demos/Scalar.lean), [`Demos/X86StraightLine`](Demos/X86StraightLine.lean), [`Demos/Riscv`](Demos/Riscv.lean), [`Demos/EarlyExit`](Demos/EarlyExit.lean) |

Every module docstring lists its results under `## Main results`. The modules
`GradedWP`, `GradedMvcgenProbe`, `WriterTMvcgen`, `LeakageExceptT`, the
`Relational*Mvcgen` pair, `UCLeakageDecomp` and the `X*` framework (`XMvcgen`,
`XDijkstraAll` and siblings) study program-logic variants and are outside the import
graph of the calculus.

## Choosing a tactic

| Goal | Tactic |
|---|---|
| `Corres` at `asemW c`, `asemWExpr c` or `asemWBV c`, small concrete kernel | `ascend!`, `ascend_expr!`, `ascend_bitwise!`, `ascend_unified!` |
| the same goal, large or generated kernel | `ascend_meta` (walks the term; `decide` only on names and literals) |
| straight-line `RSeq`/`RScalarSetExpr` kernel mixing arithmetic and bitwise nodes | `corres_sym_scalar`, or the macro `corres_solve_scalar` |
| loops, conditionals, range side conditions | `ascendG_sound`, `ascendG_sound_scalar`, `tsLowCT_sound`; inspect `(ascendG fuel c).1` first |
| array loads and stores | `ascendGL_sound_scalar`, `tsLowCTL_sound_scalar` over the array layout |
| `CorresJ SR` over a `JInstr` block | `corres_sym` (the `SymM` engine over the `@[corres]` leaves) |
| `CorresR SRr` over an `RInst64` block | `corres_sym_rv`, or the macro `corres_solve_rv` |
| carry-out and Montgomery range goals | `mont_bound` |

A solver closes the goal when the stated abstract transition is definitionally equal
to the synthesised fold; state the transition as that fold, or let the solver
synthesise it and rewrite afterwards.

## Adding a kernel

- A closed straight-line word kernel with a source: copy
  [`LegWeldDemo`](LegWeldDemo.lean). Supply the source `src : RustSrc`, the front's
  term with `LitNorm (lower src) c`, an `AdeqRun` witness, `readsOK` and `afterB`,
  the five front success facts for `FrontOut.ofSome`, and `Corres SRwordNT P fa c`;
  `legWeld_lower` gives the equation for the kernel's `Com jasminDialect` program.
- An x86 or RV64 block: state `CorresJ SR (fun _ => True) fold block` and close it
  with `corres_sym`. A new instruction needs one `@[corres]` lemma (`@[corresR]` for
  RV64) in a module that imports `CorresAttr`; `corresJ_of_regs` and `corresR_of_set`
  state a single-write leaf once. A new machine judgment gets the engine through a
  `CorresSymEngine.Machine` value, as `CorresRiscvSolver` does.
- A block from the descent: `corres_of_refines_x86_runBlock` or `corresR_of_refines`.
- Source coverage: `RustSubsetToLowCT.lowerRefines` for `if`-free `RustSrc`;
  `haxToLowCT_simulates_program`, `haxToLowCT_simulates_programT`,
  `haxToLowCT_simulates_programL` and `haxToLowCTFn_simulates` for hax programs
  ([CatCrypt/Crypto/Hax/AGENTS.md](../../Hax/AGENTS.md)); hax-lean's
  `pipeline_correct` family, used in `PipelineWeld` and `Exit`.

## Editing in this directory

- Docstrings state what a declaration is, name the semantics a result is stated over
  (`semScalar`, `semU`, `runBlock`, `runRBlock64`, `Com catCryptDialect`,
  `Com jasminDialect`) and the hypotheses that remain. Run
  `bash scripts/lint-lean-prose.sh <files>` on changed files.
- After adding or removing a module, run `bash scripts/gen-module-globs.sh` and
  `ROT_GUARD_WRITE_MANIFEST=1 bash scripts/rot-guard-build.sh --check`.
- Pin the axioms of a headline theorem with `#guard_msgs in #print axioms`.
- For a large kernel use `ascend_meta` rather than `decide` or `rfl` over the whole
  term.
- `ExprLeaf`, `EcMultiLimbMul`, `EcMultiLimbEmit` and `FieldReduce` have importers in
  `X86Backend/` and `Secp256k1FeMulBrickProduct`; a statement change there reaches
  them.
- Keep exploratory modules out of the import graph of the calculus.
