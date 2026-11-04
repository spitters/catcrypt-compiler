# The Aeneas front

The Aeneas front compiles a Rust function, as the Aeneas Lean backend prints it into the
result monad of the vendored Aeneas standard library (`HaxLean.Rust`), through the same
compiler as the hax front: `reifyAeneas%` reads the Lean function into an NF program, the
entry [`aeneasEntry`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Entry.lean)
hands it to `extChain` and `compileRegion`, and the compiler theorems of `NFEntry` hold at it.
There is no second pipeline: the hax entry `haxEntry` and `aeneasEntry` are two instances of
`NFEntry`, and `NFEntry.compileR_correct` and `NFEntry.compileR_ct` are stated once for both.

## What is proved

**Compiler correctness at an Aeneas function.** When `aeneasEntry.compileR` returns bytes for
a source, every run of the bytes from an entry state that the layout reads as the arguments
of the Lean function ends in the state the Lean function's value prescribes
([`NFEntry.compileR_correct`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/Haxc/ComposeV1.lean)).
Constant time of the same bytes is
[`aeneasEntry_compileR_ct`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/EntryCT.lean),
under the decided level check of the NF program.

**The reading is correct by construction.** `reifyAeneas%` builds the NF program together
with a proof that its denotation is the Lean function's value. Each construct of the printed
Lean has one congruence lemma in
[`Reify`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Reify.lean)
(binds, literals, conditionals, loops over a range and `loop`, guards); the elaborator
unfolds only the defining equation of the function and applies these lemmas. No reified
program is checked by `rfl` or `decide` on the whole term.

**Guards.** One lemma, `Reify.guardS`, reads every panic guard: `massert P`,
`if c then k else fail e` and `if c then fail e else k` are its instances. The passing
condition is read by `ReadCond`: a comparison `<`, `<=`, `>`, `>=`, `=`, `!=` at every width
of at most 64 bits and its negation, a Boolean variable in either polarity, `&&` and `||` of
two Boolean variables, a decided proposition. The guard compiles to the abort of `nfDialect`,
which the first pass of `extChain` (`abortElim`) removes with a value and a constant-time
certificate.

**Words of every width, through ParamTransfer.** The operations on Aeneas scalars and arrays
are related to the table `hax64WExit` of the compiler by squares stated once for every width
of at most 64 bits, as ParamTransfer `Related`, `RelatedBinOp` and `RelatedUnOp` instances
([`Scalars`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Scalars.lean),
[`Arrays`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Arrays.lean),
over [`TableReads`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/TableReads.lean)).
Unsigned division and remainder go through the chain's `divChain` with no machine `DIV`.

**The converse reading.** `nfToRustM` reads an NF program back into the Aeneas monad, and
[`nfToRustM_sim`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Loops.lean)
shows that it simulates the compiler's semantics for every NF program, loops included
(`loop_whileIter`, by fixpoint induction).

**Bytes of Aeneas test functions.** Two functions of the Aeneas test suite (commit b08bf81,
copied unchanged in `Demo/Test*.lean`) are compiled with both theorems instantiated:
`arrays.incr_array` (120 bytes,
[`incrArray_compileR_correct`, `incrArray_compileR_ct`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/Compiled.lean))
and `joins.opt_add_1_or_panic`, with a Boolean argument and a panic guard (104 bytes,
[`optAdd_compileR_correct`, `optAdd_compileR_ct`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/CompiledOptAdd.lean)).
The bytes are written by the rows `aeneas_incr_array` and `aeneas_opt_add` of the dev
executable `linked-kernel-emit`. `Demo/Reified` and `Demo/Guards` read further test
functions (`iter_loop`, `sum`, the assertions of `assert_cfg`).

## Types the entry accepts

`AeTy`: unsigned scalars of at most 64 bits (a word of 64 bits, zero-extended), Booleans (the
word 0 or 1 in a public register), and arrays of `n` such values.

## Adding an Aeneas function

Copy the printed definitions unchanged into a `Demo/Test*.lean` module with the provenance
header used there, apply `reifyAeneas%` to the function, and state its `AeSrc` and layout as
in `Demo/CompiledOptAdd.lean`. A construct the reader refuses names the congruence lemma
that is missing; add that lemma to `Reify` once, for every instance of the construct.

## Related documents

The Aeneas standard-library names the front relies on, with their vendored definitions, are
listed in [`docs/aeneas-std-names.md`](https://github.com/spitters/hax-lean/blob/work/aeneas-entry/docs/aeneas-std-names.md)
of hax-lean. The compiler's correctness methods are in [CORRECTNESS.md](../../../../CORRECTNESS.md).
