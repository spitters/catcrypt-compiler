# Region-compiled hash kernels against OpenSSL, HACL\* and XKCP

This directory measures three ELF objects in `gen/` written by `lake exe linked-kernel-emit`
(root `CatCrypt/Crypto/SecureCompilation/HashTemplate/LinkedKernelEmitMain.lean`). Each row
evaluates `frameCompile`, the region back half `compileRegion` at the frame of the code, on a
straight-line template under the layout of its linked function, and writes the bytes as an
object with one global symbol.

| object | symbol | template | linked function (Lean) |
|---|---|---|---|
| `gen/sha512_compress.o` | `catcrypt_sha512_compress` | `sha2CompressBodyP sha512P` | `HashTemplate.Sha2Linked.sha512Kernel` |
| `gen/blake2b_compress.o` | `catcrypt_blake2b_compress` | `blake2CompressBodyP blake2bP` (12 rounds) | `HashTemplate.Blake2Linked.blake2bKernel` |
| `gen/keccak_f1600.o` | `catcrypt_keccak_f1600` | `KeccakLinked.keccakFLayoutBody` (24 rounds) | `HashTemplate.KeccakLinked.keccakFKernel` |

The bytes are those of the linked functions: `frameCompile_spec` gives `compileRegion` at
`redLayout σ F` (the kernel's layout at the frame `F` of its code) the same bytes. The
meaning of each linked function is the template's reference (`sha2CompressRef`,
`blake2CompressRef`, `Primitives.Keccak.keccakF`), proved in Lean; this directory adds
test evidence and timings, not proof.

## Arms

| kernel | arm | source | side |
|---|---|---|---|
| all | ours | `gen/*.o`, linked as is, behind the trampoline of `tramp.c` | verified compiler output |
| SHA-512 compression | openssl | `SHA512_Transform`, system libcrypto (OpenSSL 3.0.13, its x86_64 assembly with run-time CPU dispatch) | peer |
| SHA-512 compression | hacl | `Hacl_Hash_SHA2_sha512_update_nblocks` (one block), HACL\* C from libcrux `sys/hacl/c` | peer, verified C |
| BLAKE2b compression | hacl | `update_block` of `Hacl_Hash_Blake2b.c` (included by `refs.c` to reach the static function) | peer, verified C |
| Keccak-f[1600] | xkcp | `KeccakP1600_Permute_24rounds`, XKCP `opt64` (generic 64-bit, all rounds unrolled, no lane complementing) as vendored in faest-ref v3.0.2 `sha3/opt64` | peer |
| Keccak-f[1600] | hacl | `Hacl_Hash_SHA3_state_permute` | peer, verified C |

libb2 is not installed on this host, and OpenSSL exports no single-block BLAKE2b or
Keccak-f entry point; BLAKE2b has the HACL\* arm only. `make provenance` prints the
versions and the hashes of our objects.

## Adapters

Calling conventions (from the layouts `sha512Abi`, `blake2bKAbi`, `keccakFAbi`):

* SHA-512: `h[8]` out at `%rdi`, `hm[24]` in at `%rsi` (chaining words, then the 16 message
  words as big-endian loads of the block).
* BLAKE2b: `h[8]` out at `%rdi`, `f0` at `%rsi`, `t1` at `%rdx`, `t0` at `%rcx`, `hm[24]` at
  `%r8` (message words little-endian); the second flag word is 0.
* Keccak-f[1600]: `dst[25]` out at `%rdi`, `src[25]` in at `%rsi`, lane `(x, y)` at `5y + x`.

The kernels may change every general-purpose register but `%rsp` (`sha512Clob`,
`blake2bKClob`, `keccakFClob`), including the System V callee-saved ones, and use a red zone
below their frame. `tramp.c` therefore calls each object through a trampoline that saves and
restores `%rbx`, `%rbp`, `%r12`-`%r15`; the trampoline is harness code, and its cost is in
every "ours" figure.

## Conformance (`make conform`)

1. Official vectors computed through our objects alone: SHA-512("abc") (FIPS 180-4) by one
   compression of the padded block from the IV; BLAKE2b-512("abc") (RFC 7693 Appendix A) by
   one final compression from the parameter-adjusted IV; SHA3-256("abc") (FIPS 202) by one
   permutation of the absorbed padded block; lane 0 of Keccak-f[1600] of the zero state.
   Each literal vector is also compared with OpenSSL's EVP one-shot digest.
2. `NRAND` random inputs per kernel (xorshift64\*, fixed seed), compared word for word with
   every peer: SHA-512 against OpenSSL and HACL\*; BLAKE2b at random counters `t0`, `t1` and a
   random final flag against HACL\*; Keccak-f against XKCP and HACL\*.

## Timing (`make run`)

`compare bench` prints, per kernel and arm, the median and minimum over `SAMPLES` samples of
TSC cycles per call (`SSProve-lean/bench/measurement_lib/tscbench.h`, CPUID/RDTSC/RDTSCP fences, pinned to
`CPU`). Each sample runs `INNER` calls, chained: a peer updates its state in place; ours
alternates two input arrays, each call writing its output into the chaining words (or the
lanes) of the other, so every call depends on the previous one. The peers' state stays
resident; ours reads 24 or 25 input words and writes 8 or 25 output words per call.
TSC cycles are reference-clock cycles, not core cycles.

## Ratios

`SSProve-lean/bench/framework/geomean_ratios.tsv` carries one row per kernel and peer; the ratio is
ours/peer of the median of the three per-run medians.

## Results

Run of 2026-11-01 (label `2026-11-01 night, load ~3.5, pinned core`), AMD Ryzen 7 PRO 7840U
(`/proc/cpuinfo`), one pinned core, three runs, each a separate process, after `make conform` passed (`SSProve-lean/bench/hash_linked_compare/results/conform.txt`: the four official
vectors and 10000 random inputs per kernel, ours equal to every peer). The host carried a
load average of about 3.5 from other jobs; all arms of a kernel were measured in one process
on the same pinned core, so the ratios compare like with like, while the absolute figures may
sit above those of an idle host. Objects written by `lake exe linked-kernel-emit` on
2026-11-01. Each row runs in 11 to 31 s of wall time, almost all of it the compile; the
executable imports the layouts and bodies from the `*LinkedData` modules, so its start-up
evaluates none of the closed checks of the `*Linked` modules. TSC
cycles per call, median of the three per-run medians (`SSProve-lean/bench/hash_linked_compare/results/run{1,2,3}.tsv`; the results files stay in the development checkout):

| kernel | ours | peer | peer cyc | ours / peer |
|---|---|---|---|---|
| SHA-512 compression | 1143.9 | OpenSSL 3.0.13 `SHA512_Transform` | 421.5 | 2.71 |
| SHA-512 compression | 1143.9 | HACL\* `sha512_update_nblocks` | 632.7 | 1.81 |
| BLAKE2b compression | 610.7 | HACL\* `update_block` | 359.4 | 1.70 |
| Keccak-f[1600] | 2823.8 | XKCP opt64 | 685.5 | 4.12 |
| Keccak-f[1600] | 2823.8 | HACL\* `state_permute` | 1918.4 | 1.47 |

Our figures include the trampoline of `tramp.c`. The objects' `.text` sections are 25987
(SHA-512), 13432 (BLAKE2b) and 62474 (Keccak-f) bytes, of 6954, 3417 and 13890 instructions:
each template is straight-line code.
