# Certifying existing machine code against a hax reference

The compiler's forward direction proves that the code it emits computes its source. This
document describes the other direction: given machine code that the compiler did not produce
(or whose production is not trusted), establish what it computes. The method has two parts.

1. A reference for the function, extracted from the Rust crate with hax. Its meaning is
   hax-lean's reference semantics `denote'` over a builtin table, and the ascent on `ImpExpr`
   relates it to a Lean function.
2. A proof by the ascent on x86 that the given code, run on the x86 machine model, computes a
   Lean function, which is then equated with the specification.

The certificates of [What a certificate states](#what-a-certificate-states) are proved by the
second part against specifications written in Lean.

Module paths below are relative to `CatCrypt/Crypto/SecureCompilation/` in this package unless
another package is named.

## The pipeline

### The reference: hax extraction and its word table

hax translates a Rust function to an `ImpExpr` program, and hax-lean gives it the evaluator
`denote'` parameterised by a builtin table. For `u64` code the table is `hax64Builtins`
(hax-lean module
[`HaxLean.Semantics`](https://github.com/spitters/hax-lean/blob/9c1a46530b44fd27dba98deb7df724d3db52ad15/HaxLean/Semantics.lean)): `hax64WordOps` gives each width-tagged operation its Rust
meaning on integers in `[0, 2^64)` (`wrapping_add#64`, `wrapping_sub#64`, `wrapping_mul#64`,
`mulhi#64`, the bitwise operations, shifts that are undefined for an amount of 64 or more,
`Add` that is undefined on overflow, and the steps of the widening multiply through `u128`),
and `widthArrayOps` supplies `index`, `array_update` and `array_lit`. An operation outside the
table, or on an argument outside its domain, evaluates to `none`, where Rust would panic or
the program is outside the table.

### Decoded bytes and the flag machine

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

### The ascent against a hax reference

The reference side of the ascent lives in `HaxAscent/Ascent/`. `Corres bi P G e V Q`
(`Corres.lean`) relates an `ImpExpr` program `e`, run by `denote'` under the builtin table
`bi`, to a shallow Lean description: from an entry environment related to the abstract
state and under the guard `G`, the run returns the value `V` from some fuel on.
`FnCorres bi e entry G f` is its top-level form for a function `f`, and
`fnCorres_refinesO` reads it as an `Option`-level refinement.

These judgements are produced without hand-written loop specifications by the surface
generator.

- `GenRules.lean` states the rules over explicit binding lists (`CorresB`, `CorresG` for
  early return and break), with one loop rule per loop form of the extraction
  (`corresB_forFoldP`, `corresB_forFoldRevP`, `corresB_forFoldG`, `corresB_whileFoldG`,
  `corresG_forFoldReturnG`) and `fnCorres_of_corresB`, `fnCorresX_of_corresG` for whole
  functions.
- `Generate.lean` defines `Hax.Ascent.Gen.ascendFn`, which evaluates a literal
  symbolically, applies one rule per step, closes every side condition (lookups, leaf
  lemmas of the table, loop termination from a measure) and returns the shallow function
  with its `FnCorres` (or `FnCorresX` for an early return). A step without a rule fails
  with a message naming its cause (`construct:`, `leaf:`, `type:`, `unbound:`, `loop:`,
  `side:`); the generator returns no open goal.
- `Coverage.lean` runs the generator over a whole haxpipeT extraction: `hax_ascend Ns`
  assembles the builtin table from the extraction's dependency class and declares, per
  function `f`, the generated surface `Ns.HaxGen.f.gen`, its correspondence
  `Ns.HaxGen.f.corres_full` and a call lemma `Ns.HaxCall.f` for later callers;
  `#hax_coverage Ns` reports per function `proved`, `failed`, `timeout` or `excluded`.

These results relate a hax reference to a Lean function, and the x86 ascent relates machine
code to a Lean function. A certificate that ties given bytes to a hax reference composes the
two at a common Lean function; `fnCorres_enc_unique` (`HaxAscent/Ascent/FnCorresUnique.lean`)
states that two correspondences of the same extracted body, entry and guard have equal
encoded results at every argument satisfying the guard.

### Machine code as input

Foreign assembly enters as a `JInstr 64` list through an importer that is not trusted. Each
file under `Ascent/Imported/` records the source file, its commit and SHA-256, and the
importer script (`bench/s2n_import/import_owned.sh`); `bench/s2n_import/compare_owned.sh`
prints the list back with `AsmPrinter.renderBlockBody` and checks it against the source's
instruction sequence. The proof is about the list, so an importer error would make the
theorem about different code, which the comparison script is there to detect.

## What a certificate states

The closed examples fall into three forms.

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
are this package's encoding of the imported instruction list, a Lean transcription of the
text that the project's backend printed; the bytes that an assembler produces for that
text do not appear.

### A loop node on the flag machine

`binAnd_export_machine_shipped` (`VIR/JasminLsemExportShippedAnd.lean`): the export node of
the shipped `mpn_and_n_loop_owned` limb body, renamed by a node renaming `ρ`, run on the flag
machine `lsemFuelMemF` from program counter `0`, halts, and the array at `argName 0` decodes
to `JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0`, the source fold of the limb body over `m`
trips. The hypotheses fix the renaming on the store slot, require the seed state to agree
with the loop's entry valuation, the invariant base registers to be readable, and the trip
count register to hold `m < 2^64`. This result is stated at the linear Jasmin level, before
encoding, and its specification is the denotation of the emitted body itself; the
identification of that fold with elementwise conjunction is not part of it.

### The referent of each certificate

Three of the four blocks were printed by this package's owned backend and are treated as
foreign code: the proofs do not use the compiler's correctness theorems. The specifications are Lean
functions written for the proof (`paSpec`, `x mod L`, `(a · b + c) mod L`) and the source fold
of the limb body; none of the four is stated against a hax reference. The ascent has also been
applied to code from other projects: s2n-bignum's `bignum_montmul_p384`
(`s2nMontmulP384_correct_addr`, `Ascent/Demos/S2nMontmulP384Addr.lean`) and the CryptOpt
Curve25519 kernels `solinas_square` and `carry_mul` (`solinasSquare_correct_addr`,
`carryMul_correct_addr`, `Ascent/CryptOptAddr.lean`), each against a specification written in
Lean.

## Worked example: s2n-bignum's `bignum_montmul_p384`

`Ascent/Demos/CertifyThirdPartyDemo.lean` states a certificate for a kernel from another
project in the form its caller uses. The code is `s2nMontmulP384Block`, the body of
s2n-bignum's hand-written x86-64 Montgomery multiplication modulo
`p384 = 2^384 - 2^128 - 2^96 + 2^32 - 1`, imported as a `JInstr 64` list
(`Ascent/Demos/S2nMontmulP384.lean` records the source file, commit and SHA-256).

The proof is in three layers, each an existing module.

1. `S2nMontmulP384Proof.lean` proves `s2nMontmulP384_correct` over `runBlock`, the machine
   whose memory is keyed by base-register names.
2. `S2nMontmulP384Addr.lean` restates it over the byte-addressed machine `runBlockA`:
   `s2nMontmulP384_correct_addr` holds for any overlap of the input and output buffers,
   because the block's memory reads precede its writes
   (`s2nMontmulP384Block_readsPrecedeWrites`) and every access follows the pointer map
   `montBank` (`s2nMontmulP384Block_disciplined`).
3. `S2nMontmulP384Bytes.lean` carries the result to bytes: `s2nMontmulP384_decode` states
   that this package's encoding of the block decodes back to the block, and
   `s2nMontmulP384Bytes_correct` that the decoded instructions compute the product under
   `runBlock`.

The demo adds the caller's form. `s2nMontmulP384_correct_reduced`: for every address state
whose entry registers `%rsi`, `%rdx`, `%rdi` hold `px`, `py`, `pz`, and whose six-word
values `x` at `px` and `y` at `py` are below `p384`, the block run by `runBlockA` stores at
`pz` a value `z < p384` with `z = x · y · (2^384)⁻¹` in `ZMod p384`. It derives
s2n-bignum's precondition `x · y ≤ 2^384 · p384` from the reduced inputs.
`s2nMontmulP384_bytes_decode` restates the decoding theorem.

The certificate assumes the machine model `runBlockA` as a description of the processor, the
correspondence of the imported list with the object code s2n-bignum ships (checked by the
importer's comparison script, not proved), and the entry-state hypotheses above. The
specification is a Lean statement written for the proof; s2n-bignum has no hax extraction,
so the hax leg of the pipeline does not apply to this kernel.

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
- For a certificate against a hax reference: hax's extraction of the Rust function, and
  hax-lean's `denote'` with `hax64Builtins` as the meaning of the Rust source.

The importer is checked by testing, by `bench/s2n_import/compare_owned.sh`.

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
  scalar-reduction part, a ten-instruction segment, is checked whole.

With the blocks cut at boundary certificates and each part checked in its own module, every
module elaborates within a few gigabytes ([ASCENT.md](ASCENT.md)).

## Summary of results

- The certificates `paShippedBytes_correct`, `scReduceShipped_correct_addr`,
  `scMuladdShipped_correct_addr` and `binAnd_export_machine_shipped`, stated above.
- The decoded-machine layer `DecodedLsemStep`, `DecodedLsemLoop`, relating `aMachine` on
  decoded bytes to the flag machine.
- The surface generator `hax_ascend` with its rules, relating every function of an
  extraction that it proves to a generated Lean function.
- The worked example `Ascent/Demos/CertifyThirdPartyDemo.lean` on s2n-bignum's
  `bignum_montmul_p384`.
- The certificates `solinasSquare_correct_addr` and `carryMul_correct_addr` of the CryptOpt
  kernels `solinas_square` and `carry_mul` at the address machine.
