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

The three crates are extracted into `Sponge_haxpipe`, `Blake2b_haxpipe` and `Sha512_haxpipe`
of the dev checkout (`scripts/reextract.sh`). On the module of an entry with its kernel linked,
under the layout of the harness (`msg` at `%rdi` as 2048 words, `len` at `%rsi` bounded by
16384, the storage arrays at `%rdx` and `%rcx`, the output at `%r8`, the constant
`MSG_MASK = 2047`), `compileA` refuses as follows; no module states acceptance and no object
exists in `bench/hash_whole_compare/gen/`.

- **The System V kernels are refused as callees.** The callee checks of a calling body
  (`calleeBodyBT`) decode the code of a kernel and run the keep check
  `Callee.keepCheckAtB` at its clobber set. `keepCheckSWB` refuses a body that writes a
  register outside the clobber set, and the `*KernelAbi` code writes the callee-saved
  registers it saves and restores (`regionBack_restores`), so at `abiClob` the conjuncts
  `codeOk`, `dead` and `calleeSeg` fail; `verify_chall2` is accepted with `keccakFKernel`
  and refused with `keccakFKernelAbi`. Accepting them needs a keep check that admits a
  register saved to a frame slot and restored before the return (the provenance facts
  `KFact` of `kstepS` already track register-to-slot and slot-to-register moves), with its
  soundness beside `keepCheck_soundBy`. The kernels at the full clobber set (`keccakFKernel`,
  `blake2bKernel`, `sha512Kernel`) are usable from C: a calling body saves every
  callee-saved register (`unwrittenSaved` is empty on a body with a call).
- **The sponge entries are refused by the class of a calling body.** With `keccakFKernel`,
  every callee check passes and the image check `calleeImgBT` fails at
  `printedAddrCWB`: the carry-out `ADCXHI` of the checked product `len * 30841` (the
  division by the rate, `(len * m) >> s`) is not directly after its add in the printed
  body (`carryPrevB` and `instrOKWB` at position 205 of 330).
- **BLAKE2b and SHA-512 are not evaluated in a module.** The bytes of `blake2bKernel` and
  `sha512Kernel` are `compileRegion` on the template, which the interpreter (`lean --run`,
  `#eval`) does not finish in 40 minutes; only an executable (`linked-kernel-emit`) evaluates
  them, so `compileA` on these modules is decided only there.

The stages of `compileA` on a calling body are those of `regionBack` at the table
`regionCallee` finds: `regionExportableB`, `narrowPrep`, `exportR`, `regionCallee`,
`regionLprogC`, `calleeBytes`, then the gate `regionCoB` (whose callee conjuncts are
`calleeBodyBT` and the image check `renImageB`, with `calleeImgBT` = `regionImgCB` at the frame
of the table) and the constant-time decision `calleeCtB`. `RegionDiag` explains the stages of a
body without a call only. A `BSWAP` or `MOVBE` lowering of the byte reversal needs a
`jasminDialect` operation, its `Lprog` op, the encoder and decoder entries and its `aMachine`
semantics.
