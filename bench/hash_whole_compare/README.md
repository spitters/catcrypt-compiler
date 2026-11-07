# Whole hash functions: compiled orchestration with a linked kernel

`whole.c` checks and times whole hash functions: the compiler's entries, whose
orchestration (padding, block loop, finalisation) is Rust compiled by `compileA` and whose
compression or permutation is a region-compiled template kernel linked under its System V
contract (`HashTemplate/LinkedAbi.lean`), against HACL* full hashes, OpenSSL EVP and
libsodium.

| Hash | Entry (crate) | Linked kernel | Peers |
|---|---|---|---|
| SHA3-256 | `sha3_256_words` (sponge-hax) | `keccak_f` = `keccakFKernelAbi` | OpenSSL `SHA3-256`, HACL* `Hacl_Hash_SHA3_sha3_256` |
| SHAKE128, 32 bytes | `shake128_256_words` (sponge-hax) | `keccak_f` | OpenSSL `SHAKE128`, HACL* `Hacl_Hash_SHA3_shake128` |
| SHAKE256, 64 bytes | `shake256_512_words` (sponge-hax) | `keccak_f` | OpenSSL `SHAKE256`, HACL* `Hacl_Hash_SHA3_shake256` |
| BLAKE2b-512 | `blake2b_512_words` (blake2b-hax) | `blake2b_compress` = `blake2bKernelAbi` | OpenSSL `BLAKE2B512`, libsodium `crypto_generichash`, HACL* `Hacl_Hash_Blake2b_hash_with_key` |
| SHA-512 | `sha512_words` (sha512-hax) | `sha512_compress` = `sha512KernelAbi` | OpenSSL `SHA512`, HACL* `Hacl_Hash_SHA2_hash_512` |

## The interface of our entries

Every entry takes the message as an array of 2048 64-bit words (`%rdi`) with the memory
layout of the byte buffer padded to whole words, the byte length at most 16384 (`%rsi`),
two storage arrays (`%rdx`, `%rcx`: the sponge states of 25 words, or the output array of 8
words and the input array of 24 words of the compression), and the output array (`%r8`),
which receives the digest bytes as words. BLAKE2b and Keccak read their words
little-endian; SHA-512 reverses the bytes of each message and digest word
(`u64::swap_bytes`). The harness fills the buffer beyond the length with `0xa5`, so an
entry that reads those bytes into a block fails the known-answer check.

## Use

    make kat                      # build `whole`, run the known-answer checks
    make bench-build DEV=<dev>    # build `whole-bench` (needs bench/measurement_lib of the dev checkout)
    make run LABEL="..."          # reference host: known answers, then the timing runs

`kat` checks every arm at the message lengths 0, 1, 64, 127, 128, 1000, 1024 and 16384
bytes (byte `i` is `31 i + 7` mod 256) against `kat_table.h`, which `gen_kat.py` writes from
Python `hashlib`, and calls our objects once more through `abi_check_call`, which checks that
the System V callee-saved registers are kept. An arm is built in when its parts exist: HACL*
when `$(LIBCRUX)/sys/hacl/c/src` has the sources (`HACL=0` leaves it out), ours when `gen/`
holds `sha3_256_words.o`, `shake128_256_words.o`, `shake256_512_words.o`,
`blake2b_512_words.o` and `sha512_words.o` with the symbols `catcrypt_<entry>`
(`OURS=0` leaves them out). The summary line names the arms that were not built.

`bench` (in `whole-bench` only) prints, per hash, length and arm, the median and minimum TSC
cycles per call over `SAMPLES` samples of `INNER` calls, each call depending on the previous
one through the first message byte. It runs the known-answer checks first and stops when an
arm fails. Read `bench/AGENTS.md` of the dev checkout before quoting a number.
