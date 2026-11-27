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
(binds, literals, conditionals, loops over a range and over iterator adapters, `loop`, guards); the elaborator
unfolds only the defining equation of the function and applies these lemmas. No reified
program is checked by `rfl` or `decide` on the whole term.

**Guards.** One lemma, `Reify.guardP`, reads every panic guard: `massert P`,
`if c then k else fail e` and `if c then fail e else k` are its instances (through
`Reify.guardS`). The passing condition is read as a prefix of bindings and a bit: a
comparison `<`, `<=`, `>`, `>=`, `=`, `!=` at every width of at most 64 bits and its negation,
a Boolean variable in either polarity, a negation, `&&` and `||` of compound operands, a
decided proposition, each by one instance of `ReadBit`. The guard compiles to the abort of
`nfDialect`, which the first pass of `extChain` (`abortElim`) removes with a value and a
constant-time certificate.

**Words of every width, through ParamTransfer.** The operations on Aeneas scalars and arrays
are related to the table `hax64WExit` of the compiler by squares stated once for every width
of at most 64 bits, as ParamTransfer `Related`, `RelatedBinOp` and `RelatedUnOp` instances
([`Scalars`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Scalars.lean),
[`Arrays`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Arrays.lean),
over [`AeneasTableReads`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/Hax/AeneasTableReads.lean)).
Unsigned division and remainder go through the chain's `divChain` with no machine `DIV`.

**Signed scalars.** An `IScalar` of `i8` to `i64` is the word of its bit pattern, zero-extended
to 64 bits; a signed comparison is the unsigned comparison of the patterns offset by the sign
bit (`slt_iff_flip`, `sle_iff_flip`, `seq_iff_flip`), and the squares against `hax64WExit` are
`iadd_square`, `isub_square`, `slt_square`
([`Signed`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Signed.lean)).
The checked `+`, `-`, `*` of Aeneas fail exactly when the exact result leaves the range of the
width, and the reader reads them under that guard. At `i8`, `i16` and `i32` the guard compares
the 64-bit wrapping operation of the sign extensions with the bounds `lo64`, `hi64`
(`iadd_guarded`, `isub_guarded`, `imul_guarded`,
[`SignedGuard`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/SignedGuard.lean)).
At `i64` the guard is the absence of signed overflow of the wrapping operation: the sign bits of
`x ^^^ z` and `y ^^^ z` for a sum, of `x ^^^ y` and `x ^^^ z` for a difference, and for a
product the bound on the product of the absolute values (`add_guard_iff`, `sub_guard_iff`,
`mul_guard_iff`; `iadd64_guarded`, `isub64_guarded`, `imul64_guarded`,
[`SignedGuard64`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/SignedGuard64.lean)).
The guard is the abort of `nfDialect` and compiles as above. `signed.abs_diff` at `i32` has the
compiler theorem `absDiff_compileR_correct`
([`Demo/CompiledSigned`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/CompiledSigned.lean)).

**Structures of scalars.** A structure argument is bound field by field, so that a projection
`S.f s` in the body is a variable; a structure result is the array of its field words, written
into an out-region by `storeFields` (`Reify.okStruct`, `nfToRustM_storeFields`,
[`Structs`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Structs.lean)).
The compiler theorems are `incrX_compileR_correct` and `pairSum_compileR_correct`
([`Demo/CompiledStructs`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/CompiledStructs.lean)).

**Iterator adapters.** A `for` loop over `(0..n).enumerate()`, `(0..n).step_by(k)`,
`a.iter().enumerate()` or `a.iter().zip(b.iter())` is read as a counted loop. Each adapter has
an `IndexedIter` whose item at the trip index `j` is what the adapter's `next` yields in the
Aeneas model (`enumRangeIter`, `stepByRangeIter`, `enumArrayIter`, `zipArrayIter`,
[`Iterators`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Iterators.lean)),
and `Reify.indexedForLoop` reads the loop over such a state. The compiler theorems are
`enumRangeSum_compileR_correct`, `enumArraySum_compileR_correct`,
`zipArraySum_compileR_correct`
([`Demo/CompiledIterAdapters`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/CompiledIterAdapters.lean))
and `stepByRangeSum_compileR_correct`
([`Demo/CompiledStepBy`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/CompiledStepBy.lean)).

**Absence of panics on an input range.** `aeneasRange% f [I₁, …]` proves
`∀ xs, lo₁ ≤ x₁ ∧ x₁ ≤ hi₁ → … → ∃ y, f xs = .ok y` for the intervals `Iᵢ = (loᵢ, hiᵢ)`, or `_`
for an argument without hypothesis
([`RangeEntry`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/RangeEntry.lean)).
The interval checker `NFRange.check` runs on the program `R.prog` of `reifyAeneas% f` with the
leaf table `aeTable` (`NFRange.check_sound'`, `aeSpec_sound`); a range it refuses is bisected
within `coverBudget` checks (`noPanic_of_cover`). The denotation gives a value of the reading
(`nfToRustM_of_denote`), and the converse of the reading below gives a value of `f`
(`noPanic_of_complete`, `aeneas_noPanic`). A signed argument is read through its bit pattern:
an interval of nonnegative values is the interval of the patterns, one of negative values is
shifted by `2 ^ n`, and one with both signs is split into the two (`memI`, `memI_neg`,
`memI_cases`). The theorems include `i64` with a negative lower bound (`incr64Signed_noPanic`,
`incr64Neg_noPanic`, `dec64Signed_noPanic` in
[`Demo/RangeTests`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/RangeTests.lean)).
A refusal names the failing call.

**The converse of the reading.** `completeAeneas% R`, for `R := reifyAeneas% f`, proves
`∀ xs, CompleteG E (f xs) V R.prog`: a value of the reading of the program is the image of a
value of `f`. Each congruence lemma of `Reify` outside the `while` loop has a complete twin, and
the elaborator replaces each node of `R.sound` by its twin
([`ReifyComplete`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/ReifyComplete.lean)).
`nfToRustM` reads an NF program back into the Aeneas monad (`aeCallV_sound`,
[`NFToRustM`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/NFToRustM.lean)),
and
[`nfToRustM_sim`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Loops.lean)
shows that a value of this reading is a value of the compiler's denotation `PDenP hax64WExit`
from some fuel on, for every NF program, loops included (`loop_whileIter`, by fixpoint
induction).

**Agreement with the hax front.** `xcheck σ m s` reads a hax module `m` without linked
functions and an Aeneas source `s` into NF programs, brings both to a canonical form (aborting
branches and tuple structure removed, dead code eliminated, source names stripped) and compares
their erasures to untyped trees, which decides alpha-equivalence. `xcheck_sound` states that
when the check accepts, a hax run and an Aeneas run from one entry state return the same value
([`XCheck`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/XCheck.lean)).
[`Demo/XCheckTest`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/XCheckTest.lean)
pairs the hax extractions of six test functions (`xor_u32`, `shift_u32`,
`u32_use_wrapping_add`, `u32_use_wrapping_sub`, `add_and`, `u32_use_rotate_left`) with their
Aeneas translations.

**The interaction-tree monad of upstream Aeneas.** Upstream types generated code against
`Result α := ITree RustEffect α`; the certificate of this front, `fn a = .ok y`, is in the flat
`RustM`. The map `toUp` of the package catcrypt-aeneas (`CatCryptAeneas.Agree`) from the flat
`RustM` to upstream `RustM` is a monad morphism (`toUp_bind`, `toUp_pure`) and injective, with
`toUp x = ok y ↔ x = .ok y` (`toUp_eq_ok_iff`), and the flat and upstream `loop` agree on
agreeing bodies, divergence included (`AgreesUp.loop`). A value of the Aeneas front is thus the
result `ok y` of the upstream computation.

**Bytes of Aeneas test functions.** Three functions of the Aeneas test suite (commit b08bf81,
copied unchanged in `Demo/Test*.lean`) are compiled with both theorems instantiated:
`bitwise.and_bool`, with two Boolean arguments and a Boolean result (246 bytes, no branch,
[`andBool_compileR_correct`, `andBool_compileR_ct`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/CompiledAndBool.lean)),
`arrays.incr_array` (120 bytes,
[`incrArray_compileR_correct`, `incrArray_compileR_ct`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/Compiled.lean))
and `joins.opt_add_1_or_panic`, with a Boolean argument and a panic guard (104 bytes,
[`optAdd_compileR_correct`, `optAdd_compileR_ct`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/CompiledOptAdd.lean)).
The bytes are written by the rows `aeneas_and_bool`, `aeneas_incr_array` and
`aeneas_opt_add` of the dev executable `linked-kernel-emit`. `Demo/Reified`, `Demo/Guards` and
`Demo/CompoundGuards` read further test functions (`iter_loop`, `sum`, the assertions of
`assert_cfg`).

## Types the entry accepts

`AeTy`: unsigned scalars (`u`) and signed scalars (`i`) of at most 64 bits (the bit pattern as
a word of 64 bits, zero-extended), Booleans (the word 0 or 1 in a register, as argument or
result), and arrays of `n` such values. Structures of scalars enter through the field-wise
reading of `Structs`.

## Adding an Aeneas function

Copy the printed definitions unchanged into a `Demo/Test*.lean` module with the provenance
header used there, apply `reifyAeneas%` to the function, and state its `AeSrc` and layout as
in `Demo/CompiledOptAdd.lean`. A construct the reader refuses names the congruence lemma
that is missing; add that lemma to `Reify` once, for every instance of the construct.

## Related documents

The Aeneas standard-library names the front relies on, with their vendored definitions, are
listed in the [Aeneas names table](https://github.com/spitters/hax-lean/blob/81fca54fb84838fdcef7a52f4dd63d7230f08e7b/docs/aeneas-std-names.md)
of hax-lean. The compiler's correctness methods are in [CORRECTNESS.md](../../../../CORRECTNESS.md).
