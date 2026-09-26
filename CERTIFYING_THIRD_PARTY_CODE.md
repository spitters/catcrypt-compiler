# Certifying existing machine code against a hax reference

The compiler's forward direction proves that the code it emits computes its source. This
document describes the other direction: given machine code that the compiler did not produce
(or whose production is not trusted), establish what it computes. The intended pipeline has
three steps.

1. Extract a reference for the function from the Rust crate with hax. Its meaning is hax-lean's
   reference semantics `denote'` over a builtin table.
2. Run a differential oracle between the reference semantics and a machine run of the given
   bytes on a battery of inputs. A disagreement is reported with the first pair of
   semantic levels that differ, before any proof is attempted.
3. On agreement, prove by the ascent that the bytes, run on the x86 machine model, compute the
   specification.

The components of each step exist. They have been joined end to end for no third-party kernel
yet; the [Status](#status) section lists what is closed and what is planned.

Module paths below are relative to `CatCrypt/Crypto/SecureCompilation/` in this package unless
another package is named. The dev tree is the CatCrypt development workspace that depends on
this package.

## The pipeline

### The reference: hax extraction and its word table

hax translates a Rust function to an `ImpExpr` program, and hax-lean gives it the evaluator
`denote'` parameterised by a builtin table. For `u64` code the table is `hax64Builtins`
(hax-lean `HaxLean/Semantics.lean`): `hax64WordOps` gives each width-tagged operation its Rust
meaning on integers in `[0, 2^64)` (`wrapping_add#64`, `wrapping_sub#64`, `wrapping_mul#64`,
`mulhi#64`, the bitwise operations, shifts that are undefined for an amount of 64 or more,
`Add` that is undefined on overflow, and the steps of the widening multiply through `u128`),
and `widthArrayOps` supplies `index`, `array_update` and `array_lit`. An operation outside the
table, or on an argument outside its domain, evaluates to `none`, where Rust would panic or
the program is outside the table.

### The oracle

`CatCrypt/Crypto/Hax/HaxOracle.lean` in the dev tree runs one kernel, `mpn_mul_1`, through
every executable semantics on its compiler route and reads back the output cells
`rp[0], …, rp[n]` as natural numbers. `oracleRun` lists eight levels:

| Level | Semantics |
|---|---|
| `hax-raw` | `denote'` of `Mpn.mpn_mul_1_impExpr` under `rawWordTable` |
| `hax-fused` | `denote'` of the fused, A-normalised program under `mul1WordTable` |
| `front-pipeline` | the front's scalar semantics `semScalar` of the lowered loop body |
| `front-pinned` | the same fold at the pinned body `mul1BodyLow NR` |
| `coml` | the denotation of the front-compiled `ComL` loop |
| `node-raw` | the flag machine `lsemFuelMemF` on the exported loop node |
| `node-renamed` | the same node under the renaming `nodeRen` |
| `machine` | `run aMachine` on `decodeLprog (encodeLfundefBytes mul1PhysBody)` |

`diff` names the first two levels whose cells disagree. The front, node and machine levels
model an output array of nine words, so they run for `n ≤ 8` and report larger inputs as out
of model. `HaxOracleMain.lean` runs the fixed `battery` (edge cases at `n = 0`, `1`, `4`, and
pseudo-random inputs at `n = 1`, `4`, `8`) and exits with status `1` at the first
disagreement:

```
lake exe hax-oracle
```

The executable needs about 2.75 GB of memory at start-up, for the initialisation of the
emitter's closed terms. The oracle's `machine` level runs the bytes of this compiler's own
exporter; the byte blob is fixed in the module.

The machine level uses the decoded-machine layer of this package.
`X86Backend/DecodedLsemStep.lean` relates `aMachine` (`Ascent/RInstrAddrMem.lean`), which runs
the `RInstr` list that `decodeLprog` returns on the address-memory state, to the flag machine
`lsemFuelMemF`, one straight segment at a time (`DecSim`, with instances per instruction
family, `decSim_mulx` for the `MUL:64`/`MULXHI:64` pair, and the loads and stores through a
frame-held base). `X86Backend/DecodedLsemLoop.lean` adds the counted loop with its zero-trip
guard (`decLoop_guarded`) and a whole node (`decNode_halts`).

### The ascent

The ascent (see [ASCENT.md](ASCENT.md)) relates a program to an abstract function through
correspondence squares in the style of AutoCorres. For x86 the program is a `JInstr 64`
block run by `runBlock` (Jasmin's x86 semantics transcribed in Lean, with memory keyed by base
register) or by `runBlockA` (`Ascent/AddrMem.lean`, the same instruction semantics over a
byte memory addressed by value). `runBlockA_simD_on` (`Ascent/AddrMemDerived.lean`) carries a
result on `runBlock` to `runBlockA` for a block that respects a memory discipline, under the
hypothesis `Separated` that the cells the block uses occupy pairwise disjoint eight-byte
ranges.

Foreign assembly enters as a `JInstr 64` list through an importer that is not trusted. Each
file under `Ascent/Imported/` records the source file, its commit and SHA-256, and the
importer script (`bench/s2n_import/import_owned.sh`); `bench/s2n_import/compare_owned.sh`
prints the list back with `AsmPrinter.renderBlockBody` and checks it against the source's
instruction sequence. The proof is about the list, so an importer error would make the
theorem about different code, which the comparison script is there to detect.

## What a certificate states

The closed examples fall into two forms.

### Blocks on the address machine

`scReduceShipped_correct_addr` (`Ascent/Demos/Ed25519ScReduceShippedProof.lean`): for every
address state `sa` with `Separated shippedBank sa.regs scrCells`, the block
`ed25519ScReduceShippedBlock` run by `runBlockA` stores at `%rdi + 8i`, `i < 4`, limbs whose
value is `x mod L` and below `L`, where `x` is the eight-limb value at `%rsi` and
`L = 2^252 + 27742317777372353535851937790883648493`.

`scMuladdShipped_correct_addr` (`Ascent/Demos/Ed25519ScMuladdShippedProof.lean`): under
`Separated shippedBank sa.regs scmCells`, `ed25519ScMuladdShippedBlock` stores at `%rdi` the
four limbs of `(a · b + c) mod L`, with `a`, `b`, `c` the four-limb values at `%rsi`, `%rdx`,
`%rcx`, and the result below `L`.

`shippedBank` (`Ascent/AddrMemDerived.lean`) takes the SysV argument registers and `%rsp` as
memory bases. The cell lists `scrCells` and `scmCells` are the input and output limbs and the
stack cells the block uses. The hypothesis is the only one on the entry state; it excludes
overlapping input and output buffers.

### Bytes that decode to a block

`paShippedBytes_correct` (`Ascent/Demos/Ed25519PointAddBytes.lean`): for every `sa` with
`Separated shippedBank sa.regs paCells` and eight input coordinates `paInValA sa k` below
`2^255 - 19`, the byte string `encodeJBlock s2nAlloc ed25519PointAddShippedBlock` decodes by
`decodeJStream` to a block `c` whose output coordinates `outValOf c sa k` (the four words at
`%rdi + 32k`) are the components of `paSpec`, the extended-coordinates Edwards addition
formula over the natural values of the inputs modulo `2^255 - 19`. The bytes in the statement
are this package's encoding of the imported instruction list; the bytes of the original
object file do not appear.

### A loop node on the flag machine

`binAnd_export_machine_shipped` (`VIR/JasminLsemExportShippedAnd.lean`): the export node of
the shipped `mpn_and_n_loop_owned` limb body, renamed by a node renaming `ρ`, run on the flag
machine `lsemFuelMemF` from program counter `0`, halts, and the array at `argName 0` decodes
to `JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0`, the source fold of the limb body over `m`
trips. The hypotheses fix the renaming on the store slot, require the seed state to agree
with the loop's entry valuation, the invariant base registers to be readable, and the trip
count register to hold `m < 2^64`. This result is stated at the linear Jasmin level, before
encoding.

### The referent of each certificate

Three of the four blocks were printed by this package's owned backend
(`crates/catcrypt-ed25519/asm/*_x86_from_lean.s` in the dev tree) and are treated as foreign
code: the proofs do not use the compiler's correctness theorems. The specifications are Lean
functions written for the proof (`paSpec`, `x mod L`, `(a · b + c) mod L`) and the source fold
of the limb body; none of the four is stated against a hax reference. The ascent has also been
applied to code from other projects: s2n-bignum's `bignum_montmul_p384`
(`s2nMontmulP384_correct_addr`, `Ascent/Demos/S2nMontmulP384Addr.lean`) and the CryptOpt
Curve25519 kernels `solinas_square` and `carry_mul` (`solinasSquare_correct_addr`,
`carryMul_correct_addr`, `Ascent/CryptOptAddr.lean`), each against a specification written in
Lean.

## Trusted base

A certificate of this kind relies on the following, beyond Lean's kernel.

- The x86 machine model. `runBlock`, `runBlockA` and `aMachine` define what an instruction
  does; a certificate says nothing about a processor that behaves differently.
- The decoder and the byte encoding, where the certificate is stated over bytes.
  `paShippedBytes_correct` includes the decode in its conclusion; the correspondence between the decoder's reading and the processor's reading
  of the same bytes is trusted.
- The assembler and loader. A certificate over a `JInstr` list or over this package's encoding
  of it does not cover the object file the linker consumes, the placement of the code, or the
  calling convention beyond the entry-state hypotheses.
- The entry-state hypotheses: separation of the cells (`Separated`), input ranges where the
  algorithm needs them, and for the loop node the seed and trip-count conditions.
- For the planned hax-referenced certificates: hax's extraction of the Rust function, and
  hax-lean's `denote'` with `hax64Builtins` as the meaning of the Rust source.

The following are checked by testing only.

- The importer, by `bench/s2n_import/compare_owned.sh`.
- The oracle. Agreement on its battery shows that the levels agree on those inputs and
  does not enter a certificate.
- The reference semantics against rustc. The D1 runner `lake exe hax-run`
  (`CatCrypt/Crypto/Hax/HaxRunMain.lean` in the dev tree) runs an extracted program under
  `denote'`; `bench/hax_diff/diff_sha256.sh` feeds the same inputs to a rustc build of the
  `sha256-hax` crate and diffs the outputs over its ten public functions. A mismatch is
  treated as a bug in the extraction, the semantics or the builtin table.

## Cost levers

The Ed25519 proofs are sized by two devices documented in their modules.

- Part checks. `partCheck` (`Ascent/Demos/Ed25519SymExec.lean`) runs a symbolic executor over
  a part of the block from a map of machine locations to word expressions, interns the
  results in a hash-consed value table, and compares them with the expected map;
  `partCheck_sound` turns a passing check into the implication across `runBlock`, and each
  table operation is proved sound once (`symStep_sound`, `internE_spec`, `Tb.add_spec`). The
  scalar reduction is checked over eight parts, the multiply-add over nine, and the part
  results are chained. The checks run by `decide +kernel` and cost gigabytes of kernel memory,
  so they live in modules separate from the executor.
- Cut certificates. Each part check is split into two halves at a boundary certificate, the
  symbolic state at the cut, generated outside the kernel by the same executor
  (`scripts/cutgen/Ed25519ScReduceCutAll.lean`); `Ed25519ScReduceCut01` … `Cut07` and
  `Ed25519ScMuladdCut01` … `Cut09` check the halves, which `mapHolds_cat` joins. The last
  scalar-reduction part, a ten-instruction segment, is checked whole. The footprint checks
  run by `native_decide`.

[ASCENT.md](ASCENT.md) records the effect: with the blocks cut at boundary certificates and
each part checked in its own module, every module elaborates within a few gigabytes.

## Status

Closed:

- the four certificates `paShippedBytes_correct`, `scReduceShipped_correct_addr`,
  `scMuladdShipped_correct_addr` and `binAnd_export_machine_shipped`, stated above;
- the decoded-machine layer `DecodedLsemStep`, `DecodedLsemLoop` relating `aMachine` on
  decoded bytes to the flag machine;
- the oracle `hax-oracle`, wired for `mpn_mul_1` only, over bytes of this package's own
  exporter;
- the D1 differential runner against rustc for `sha256-hax`.

Planned:

- Generalise the oracle to take an extracted `ImpExpr`, a builtin table such as
  `hax64Builtins`, a byte blob and an ABI and layout description, and to run the decoded bytes
  on `aMachine` against `denote'`.
- Add a hardware leg: run the same bytes natively in a subprocess, with the runner used by the
  verified-evaluation tactic `verified_decide_hw`, and compare with `aMachine`. This tests the
  machine model, which the certificates trust.
- Apply the pipeline to one libcrux field kernel: the hax reference from the extraction
  corpus, the bytes from the shipped object, and a proof by ascent against the same hax
  reference, attempted only after the oracle agrees.
- Write the cost levers above as a recipe for a new kernel.
