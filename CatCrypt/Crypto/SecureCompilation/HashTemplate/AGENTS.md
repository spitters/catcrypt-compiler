# `HashTemplate/` — hash compressions as straight-line templates

A template generates a hash compression as a straight-line `jasminDialect` program from a
parameter record, and proves once, for every parameter value, that the program denotes the
reference compression (`*_value`) and that its events do not depend on the inputs
(`*_events`). Proofs go by an invariant per round, so their cost does not grow with the
round count.

| Module | Content |
|---|---|
| `StraightLine` | the generic compiler: `WExp` (variables, constants, `JasminBinOp`, rotate right, shift right), `genLets`/`genLetsR`, `genLoad`/`genLoads`, `genStores`/`genStoresIdx`, with value and fixed-event lemmas |
| `Sha2` | the SHA-2 family (`Sha2FamilyParams`; SHA-224/256/384/512/512-224/512-256) |
| `Blake2` | BLAKE2b and BLAKE2s (`Blake2Params`) |
| `Keccak` | Keccak-f[1600] |

The parameter tables are checked against the standards outside Lean, in the development
checkout SSProve-lean: `bench/sha2_template_h0`, `bench/blake2_template_params`,
`bench/keccak_template_params`.

## Compiling a template with `compileRegion`

A template becomes a linked callee of `compileA` through `LinkedFn.ofRegion` over
`NFProg.ofCom` of the program. `compileRegion` accepts a program only in the following form:

- **Outputs by register-index stores.** Write the result with `genStoresIdx`
  (`regConst` then `stackStore`). The cell fold of the region back half has no case for
  the immediate-index store of `genStores`, and the wide address gate refuses it.
- **No fresh output array.** `.stackZero` prints as `ZEROARR`, which the printed-body gate
  refuses. Store into an argument array.
- **One read-only array.** A linked kernel admits at most one read-only array argument, so
  pack the inputs into one array (`sha2InCtxtP`, `blake2InCtxtP`: chaining words at 0-7,
  message words at 8-23). The output array is separate and is not read. Scalars
  (BLAKE2's counter and flag words) are register arguments.
- **Rotations and `andn`** (SHA-2's `Ch`, Keccak's `χ`) are compiled natively (`ROR` and the
  BMI1 `ANDN` of the encoder); the region legalisation `legalizeRegion` is the identity
  (`Haxc/AndnLegal`).
- **Size.** In a module `compileRegion` is evaluated by the interpreter (the modules are not
  precompiled, so `native_decide` is no faster than `#eval`), and its cost grows faster than
  linearly in the number of lets: the 12-round BLAKE2b compression does not finish within the
  language-server limit, and the executable `linked-kernel-emit` (`LinkedKernelEmitMain`)
  compiles it.

The leakage obligation of `calleeSpec_of_compileRegion` follows from a template's
`*_events` theorem by `Dialects.NFLeak.nfct_ofCom_of_fixed` (module
`Dialects/NFLeakOfCom`).

Before writing proofs over a compiled template, evaluate each stage of `compileRegion` on it
(`regionExportableB`, `exportR`, `regionCallee`, `regionLprogC`, the printed body,
`encodableLinstrR` per instruction, the conjuncts of `regionCoB` and `regionCtB`). A
`native_decide` over the result of a refused compile crashes the language-server worker.
