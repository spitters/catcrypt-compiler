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

`OPTFLAGS` is `-O3 -march=native` unless overridden; `SIMDFLAGS` is `-mavx2
-DHACL_CAN_COMPILE_VEC128 -DHACL_CAN_COMPILE_VEC256`, the flags libcrux's `build.rs` sets for
HACL\*'s vector code on x86-64. `compare` prints the compiler and both flag sets in the header
of its output, and `make provenance` prints the versions and commits of every peer and the
hashes of our objects.

| kernel | arm | source | flags | verified | vectorised |
|---|---|---|---|---|---|
| all | ours | `gen/*.o`, linked as is, behind the trampoline of `tramp.c`; SHA-512 and BLAKE2b through the block wrappers `ours_sha512_block`, `ours_blake2b_block` of `tramp.c` | objects as emitted; wrappers `OPTFLAGS` | yes: compiler output whose meaning is the reference, proved in Lean | no |
| SHA-512 compression | openssl | `SHA512_Transform`, system libcrypto (OpenSSL 3.0.13), x86_64 assembly with run-time CPU dispatch | prebuilt | no | message schedule in the AVX and AVX2 paths |
| SHA-512 compression | hacl | `Hacl_Hash_SHA2_sha512_update_nblocks` (one block), HACL\* C from libcrux `sys/hacl/c` | `OPTFLAGS` | yes (HACL\*) | no (portable C) |
| SHA-512 compression, 4 lanes | hacl_vec256 | static `sha512_update4` of `Hacl_SHA2_Vec256.c` (included by `refs_hacl_vec256.c`) | `OPTFLAGS SIMDFLAGS` | yes (HACL\*) | AVX2, four independent lanes |
| BLAKE2b compression | hacl | static `update_block` of `Hacl_Hash_Blake2b.c` (included by `refs.c`) | `OPTFLAGS` | yes (HACL\*) | no (portable C) |
| BLAKE2b compression | hacl_simd256 | static `update_block` of `Hacl_Hash_Blake2b_Simd256.c` (included by `refs_hacl_blake2b_simd256.c`) | `OPTFLAGS SIMDFLAGS` | yes (HACL\*) | AVX2, one state as four rows of four words |
| Keccak-f[1600] | xkcp | `KeccakP1600_Permute_24rounds`, XKCP `opt64` (generic 64-bit, all rounds unrolled, no lane complementing) as vendored in faest-ref v3.0.2 `sha3/opt64` | `OPTFLAGS` | no | no |
| Keccak-f[1600] | xkcp_avx2 | `KeccakP1600_AVX2_Permute_24rounds`, XKCP `lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s` (CRYPTOGAMS assembly), the XKCP submodule of formosa-keccak | assembly | no | AVX2, one state |
| Keccak-f[1600] | xkcp_avx512 | `KeccakP1600_AVX512_Permute_24rounds`, XKCP `lib/low/KeccakP-1600/AVX512/KeccakP-1600-AVX512.s` (CRYPTOGAMS assembly), same checkout | assembly | no | AVX-512, one state |
| Keccak-f[1600] | hacl | `Hacl_Hash_SHA3_state_permute` | `OPTFLAGS` | yes (HACL\*) | no (portable C) |
| Keccak-f[1600], 4 states | hacl_simd256_absorb | `Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks` over one 168-byte block of zeros per state (`Hacl_Hash_SHA3_Simd256.c`) | `OPTFLAGS SIMDFLAGS` | yes (HACL\*) | AVX2, four states |

Interface: every arm is timed one block (one permutation) per call, in chained calls. The
SHA-512 and BLAKE2b arms all take the 128-byte block and load its message words inside the
call: the peers in their compression functions, ours in the block wrappers, which load the 16
words into the kernel's input array (with a byte swap for SHA-512, as a copy for BLAKE2b on
little-endian x86-64) and then call the kernel. The Keccak-f arms take the 25-lane state. The
4-lane rows (`sha512_compress_x4`, `keccak_f1600_x4`) process four independent states per
call and report cycles per call divided by 4, that is per block per lane and per state; ours
has no 4-lane arm, so these rows give the throughput of HACL\*'s multi-buffer code and are not
ratios against ours. HACL\* exports neither a single-state vector Keccak-f nor a 4-way
permutation alone, so the `keccak_f1600_x4` arm includes the copy, transposition and XOR of
the zero block into the four states. With `-march=native` on an AVX-512 host the C compiler
may also vectorise the portable C peers and the block wrappers.

Not added: libb2 is not installed on this host; libsodium is installed as the runtime library
only (no headers), and its `crypto_generichash_blake2b` interface buffers input and exposes
no block compression; OpenSSL exports no single-block BLAKE2b or Keccak-f entry point.

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
every "ours" figure. The block wrappers `ours_sha512_block` and `ours_blake2b_block` of
`tramp.c` sit above the trampoline; their message loads are also in every "ours" figure for
SHA-512 and BLAKE2b.

The XKCP AVX2 state holds the lanes in a permuted order, so both XKCP assembly arms are read
and written through their `AddBytes` and `ExtractBytes` in the conformance check and permute
a resident state in the timing. HACL\*'s 4-lane states are arrays of 256-bit vectors in which
word (or lane) `i` of lane (or state) `j` is 64-bit word `4i + j`.

## Conformance (`make conform`)

1. Official vectors computed by every arm on its own (ours through the block wrappers that
   the timing calls; a 4-lane arm with the vector in all four lanes, the lanes checked
   equal): SHA-512("abc") (FIPS 180-4) by one compression of the padded block from the IV;
   BLAKE2b-512("abc") (RFC 7693 Appendix A) by one final compression from the
   parameter-adjusted IV; SHA3-256("abc") (FIPS 202) by one permutation of the absorbed
   padded block; lane 0 of Keccak-f[1600] of the zero state. Each literal vector is also
   compared with OpenSSL's EVP one-shot digest.
2. `NRAND` random inputs per kernel (xorshift64\*, fixed seed), compared word for word between
   ours and every peer: SHA-512 against OpenSSL, HACL\* and each lane of HACL\* Vec256 (four
   independent random blocks and chaining values); BLAKE2b at random counters `t0`, `t1` and a
   random final flag against HACL\* and HACL\* Simd256; Keccak-f against XKCP opt64, XKCP AVX2,
   XKCP AVX-512, HACL\* and each state of HACL\* Simd256 (four independent random states).

## Timing (`make run`)

`compare bench` prints, per kernel and arm, the median and minimum over `SAMPLES` samples of
TSC cycles per call (`SSProve-lean/bench/measurement_lib/tscbench.h`, CPUID/RDTSC/RDTSCP fences, pinned to
`CPU`). Each sample runs `INNER` calls, chained: a peer updates its state in place; ours
alternates two input arrays, each call writing its output into the chaining words (or the
lanes) of the other, so every call depends on the previous one. The peers' state stays
resident; ours reads 8 chaining words and the 128-byte block (SHA-512, BLAKE2b) or 25 lanes
(Keccak-f) and writes 8 or 25 output words per call. The 4-lane rows divide by 4 as stated
under Arms. TSC cycles are reference-clock cycles, not core cycles.

## Ratios

`SSProve-lean/bench/framework/geomean_ratios.tsv` carries one row per kernel and peer; the ratio is
ours/peer of the median of the three per-run medians.

## Results

The figures below were measured with the previous adapter, which converted the SHA-512
message words outside the timed loop and copied the BLAKE2b block once before it, and without
the vector arms. Run of 2026-11-01 (label `2026-11-01 night, load ~3.5, pinned core`), AMD Ryzen 7 PRO 7840U
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
