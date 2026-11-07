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
| `TemplateKernel` | region kernels and template kernels (`ProgKernelData`, `TemplateKernelData`): the linked function of the bytes of `compileRegion`, its contract (`meets`) and its linked-kernel structure (`linked`), and the check at the frame of the code (`frameCheck`) |
| `TemplateKernelAbi` | the same kernels at the System V convention (`abiKernel`, `meets_abi`, `linked_abi`): the clobber set `abiClob` without the callee-saved registers, which the code saves and restores (`regionBack_restores`) |
| `Sha2Linked`, `Blake2Linked`, `KeccakLinked`, `LinkedAbi` | the SHA-512, BLAKE2b and Keccak-f kernels (`sha512Kernel`, `blake2bKernel`, `keccakFKernel`) and their System V forms (`*KernelAbi`), the objects of `bench/hash_linked_compare/gen/` |

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
  (`Haxc/AndnLegal`), and the and-not and rotate legalisations `legalizeAndn` and
  `legalizeRor` are proved and not applied.
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

## Whole hashes over the linked templates

The orchestration of a whole hash is Rust of the dev checkout, compiled by `compileA` with
the template kernel linked at its System V contract (`LinkedAbi`): `sha3_256_words`,
`shake128_256_words`, `shake256_512_words` (`sponge-hax`, module `words`) call
`keccak_f(dst, src)` (`keccakFKernelAbi`); `blake2b_512_words` (`blake2b-hax`) calls
`blake2b_compress(h, f0, t1, t0, hm)` (`blake2bKernelAbi`); `sha512_words` (`sha512-hax`) calls
`sha512_compress(h, hm)` (`sha512KernelAbi`). Each crate function of these names has a reference
body; the module lists the kernel in `linked` and not in `fns`. Every entry takes the message as
2048 words (`%rdi`) with the memory layout of the byte buffer, the byte length at most 16384
(`%rsi`, a bound of the layout), two storage arrays (`%rdx`, `%rcx`) and the output array
(`%r8`), and keeps to the front's domain: storage arrays are parameters, message indices are
masked into the buffer (the index check reads the mask), and the division by a Keccak rate is a
product and a shift. SHA-512 reverses the bytes of its words with `swap_bytes#64`, translated by
`NFToCat.bswapChain`. The known-answer harness is `bench/hash_whole_compare`.

Not done: the extraction of the three crates (`cargo hax json --use-ids`, then
`scripts/reextract.sh` of the dev checkout), the modules stating `compileA` acceptance and the
instances of `haxc_correct_auto_one` and `haxc_ct_proved_all` (the pattern of
`FAEST/FaestV3Compile`), the rows of `EmitRegistry` and `scripts/acceptance-registry.tsv`, and
the objects in `bench/hash_whole_compare/gen/`. A `BSWAP` or `MOVBE` lowering of the byte
reversal needs a `jasminDialect` operation, its `Lprog` op, the encoder and decoder entries and
its `aMachine` semantics.
