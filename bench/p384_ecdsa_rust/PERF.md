# P-384 ECDSA and DHKEM: measurements

kind: measurement record · authority: canonical for the figures of
`bench/p384_ecdsa_rust` · freshness: each section is a dated run and goes stale
with the machine, the toolchain and the contents of `gen/`

This file holds the measured figures of the crate described in
[README.md](README.md). The design, the tiering of each opponent, the
signing-fairness reconstructions and the test suites are described there; where
the text below refers to a section "above" that is not in this file, it is the
section of that name in README.md.

**Host.** AMD Ryzen 7 PRO 7840U (Zen 4, 8 cores / 16 threads), Linux
7.0.0-31-generic, rustc 1.93.0, `--release`, every process pinned to core 15
with `taskset`. The load average differs between runs and is stated in each
section.

**Units and ratios.** Whole-operation and micro-benchmark figures are the median
of the per-repetition wall-clock ns/op (µs/op where a table says so), with every
arm of a process interleaved round-robin. The field-multiply table is in
invariant-TSC reference cycles. A ratio is ours over theirs, measured in the
same process; below 1.00 our side is faster. Absolute figures compare only
within one process, because the machine load differs between runs.

**How to run.** From this directory, with `S2N_BIGNUM_DIR` naming a built
s2n-bignum checkout (see README.md, [§ Paths](README.md#paths)):

| command | what it runs |
|---|---|
| `make bench` | ECDSA and DHKEM, `--features s2n`, CryptOpt and pure-Rust AUCurves field, one process each |
| `make bench-production` | the same with the OpenSSL, BoringSSL and (when present) AWS-LC and SymCrypt columns, `--features s2n,production` |
| `make bench-dhkem` | DHKEM only, three AUCurves field configurations: pure Rust, CryptOpt, s2n-bignum (`P384_S2N_FIELD`) |
| `make field` | the P-384 field multiply, `fieldbench`, `--features s2n,emit-field` |

| variable | meaning | default |
|---|---|---|
| `BENCH_REPS`, `BENCH_ITERS` | repetitions, iterations per repetition | 15, 300 in the Makefile; 11, 200 in the binary |
| `BENCH_MICRO_ITERS` | iterations for the scalar-inverse and two-term-multiply micro-benchmarks | 4000 |
| `BENCH_SECTIONS` | `ecdsa`, `dhkem` or both | `ecdsa,dhkem` |
| `BENCH_CPU` (Makefile) | the core `taskset` pins to | 15 |
| `P384_NO_CRYPTOPT=1` | AUCurves field in fiat-crypto Rust instead of CryptOpt assembly (build time) | unset |
| `P384_S2N_FIELD` | AUCurves field from an s2n-bignum archive or an emitted `.s` file (build time) | unset |
| `P384_OPENSSL36_LIBCRYPTO` | the OpenSSL 3.2+ library of the native DHKEM rows | `/opt/microsoft/mdatp/lib/libcrypto.so.3` |
| `P384_AWSLC_LIBCRYPTO` | the AWS-LC library; its rows are skipped when absent | `../../../bench_refs/aws-lc-build/crypto/libcrypto.so` |
| `P384_SYMCRYPT_LIB` | the SymCrypt module; its rows are skipped when absent or not version 103.13 | `../../../bench_refs/symcrypt/build/cmake/Linux_AMD64_GCC_Release/module/libsymcrypt.so.103` |
| `KAT_RANDOM`, `FIELD_SAMPLES`, `FIELD_INNER` | `fieldbench`: random known-answer pairs, samples, multiplies per sample | 100000, 301, 2000 |

The AUCurves field configuration is fixed at build time, so a benchmark binary
is rebuilt with the same variables before each run.

## Measured, the AUCurves backends

2026-09-16, AMD Ryzen 7 PRO 7840U (Zen 4, 8 cores / 16 threads), Linux
7.0.0-31-generic, rustc 1.93.0, `--release`, pinned to core 15, load average
1.1 to 1.9 during the run — one Rocq worker was saturating another core. The
figure is the median of the per-repetition ns/op. Our side, RustCrypto and
Graviola, and the two arms of each micro-benchmark, are interleaved
round-robin within each process, because on this machine the clock drifts by
more over a sequential sweep than the variants differ from each other
(the script `p384-safe-rust/build.sh` of the AUCurves tree records that
measurement).

Whether the CryptOpt assembly is linked is a compile-time choice of
`p384-safe-rust`, so the two configurations cannot be interleaved against
each other; they are separate processes and separate rows. Against
RustCrypto only the pure-Rust row is a same-tier comparison: the assembly row
has a hand-superoptimized field multiply on our side and Rust on
RustCrypto's. Against Graviola it is the assembly row that is same-tier and
the pure-Rust row that is not.

The Graviola figures are a later run on the same machine, core and pinning;
the RustCrypto columns were re-measured inside the same two processes, so the
three columns of a row are directly comparable. Against the earlier
`### Whole operation` table the RustCrypto column sits 7 to 10% lower, which
bounds the drift between the two runs; the four ratios reproduce to two
decimals across them.

### The scalar inverse

15 repetitions of 4000 iterations, one fixed scalar, pure-Rust field. The
scalar field is fiat-crypto in both configurations and the divstep inverter
calls neither `fp_mul` nor `fp_square`, so the assembly configuration
reproduces these three rows to within 1%.

| inverse | ns/op | vs Fermat |
|---|---|---|
| Fermat `a^(n-2)`, 383 squarings + 287 multiplications | 33 016 | 1.00 |
| divstep, 15 × 59, `safegcd_p384_order` | 2 228 | 0.07 |
| base-field `fp_inv`, `safegcd_p384`, for scale | 2 256 | — |

The two divstep inverses cost the same, as they should: identical limb
count, identical iteration count, and a modulus that enters only as data.
The development repository's `bench/p384_safegcd_compare` recorded `fp_inv` at 2333 ns/op on this box,
which is the same figure to 3%.

Both are the half-delta variant. The safegcd core starts `zeta = -1`, the
δ₀ = 1/2 encoding, and `ModInfo::outer_iters` documents the requirement
`outer_iters ≥ ⌈(9437·b + 1)/(4096·59)⌉`, which is fifteen at `b = 384` and
gives 885 divsteps; the classic δ₀ = 1 bound at that width is 1110, which
needs nineteen outer iterations. Running the same step over the same modulus
at each count, and asserting the two agree on 256 inputs first:

| bound | divsteps | ns/op | ratio |
|---|---|---|---|
| classic δ₀ = 1, 19 × 59 | 1121 | 2718 | 1.00 |
| half δ₀ = 1/2, 15 × 59 | 885 | 2145 | 0.79 |

The ratio is the iteration ratio, 885/1121, to two decimals — the per-step
cost is the same and only the count differs. At the whole-operation level it
is worth about 570 ns, under one percent of a signature, because the inverse
is now a few percent of the operation rather than the quarter of it that the
Fermat chain was.

### The two-term multiply

15 repetitions of 200 iterations, on the `u1`, `u2` and `Q` of the verify
row below.

| configuration | route | ns/op | ratio |
|---|---|---|---|
| fiat-crypto field, pure Rust | `mul_base` + `mul` + `add`, 3 leaves | 480 031 | 1.00 |
| fiat-crypto field, pure Rust | `p384_lincomb`, interleaved, w = 5 | 445 379 | 0.93 |
| CryptOpt assembly field | `mul_base` + `mul` + `add`, 3 leaves | 353 576 | 1.00 |
| CryptOpt assembly field | `p384_lincomb`, interleaved, w = 5 | 329 233 | 0.93 |

### Whole operation

15 repetitions of 300 iterations.

| configuration | op | ours ns/op | RustCrypto ns/op | ratio | same tier |
|---|---|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 80 490 | 505 369 | 0.16 | yes |
| fiat-crypto field, pure Rust | verify | 455 950 | 927 494 | 0.49 | yes |
| CryptOpt assembly field | sign | 62 281 | 505 166 | 0.12 | no |
| CryptOpt assembly field | verify | 339 054 | 951 083 | 0.36 | no |

Ratio is ours / RustCrypto; below 1.00 means our side is faster. A repeat of
the whole measurement gave the same four ratios to two decimals (ours:
80 767 / 458 594 pure, 62 486 / 339 050 assembly; RustCrypto: 506 812 /
931 008 and 506 800 / 933 626). The RustCrypto column differs by 2.5%
between the two processes of a run, which bounds the drift between them.

### Whole operation, all three implementations

15 repetitions of 300 iterations, one process per field configuration, the
three sides interleaved round-robin inside each. Same machine, core and
pinning as the two-column table above, but a separate run: read the ratios
across the two tables and the absolutes only within one.

| configuration | op | ours ns/op | RustCrypto | vs RC | Graviola | vs GV |
|---|---|---|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 73 061 | 461 528 | 0.16 | 108 205 | 0.68 |
| fiat-crypto field, pure Rust | verify | 414 759 | 851 848 | 0.49 | 206 189 | **2.01** |
| CryptOpt assembly field | sign | 57 460 | 468 695 | 0.12 | 112 181 | 0.51 |
| CryptOpt assembly field | verify | 310 122 | 857 869 | 0.36 | 201 581 | **1.54** |

A repeat of the whole measurement gave the same ratios against RustCrypto to
two decimals and against Graviola to within 4%: ours 73 891 / 417 078 pure
and 57 019 / 305 075 assembly, Graviola 109 703 / 199 535 and 108 776 /
197 638, so 0.67 and 2.09 pure, 0.52 and 1.54 assembly. The Graviola verify
column is the noisiest of the six, moving 1.3% between the two runs.

Tier per row, and what each column includes:

| row | vs RustCrypto | vs Graviola |
|---|---|---|
| pure Rust, sign | same tier; both prehashed and both given `k` | not same tier (Rust against assembly), *and* not like for like (their column is the whole `sign` API) |
| pure Rust, verify | same tier | not same tier; like for like up to a 0.1% message hash |
| assembly, sign | not same tier | same tier, but not like for like |
| assembly, verify | not same tier | **same tier and like for like — the headline Graviola row** |

The RustCrypto ratios are unchanged from the previous measurement: 0.16 and
0.49 against 0.16 and 0.50 pure Rust, 0.12 and 0.36 against 0.12 and 0.36
with the assembly field.

**Where we lose.** Verification, against Graviola, in both configurations.
The headline row — same tier, like for like — is 310 µs against 202 µs, a
factor of 1.54 slower. The pure-Rust row is 2.01, which is the tier gap and
is reported as such. Both are the two-term multiply: our `p384_lincomb` is
Shamir with a 5-bit window over the AUCurves group law, and Graviola runs two
5-bit-window Booth multiplications in s2n-bignum assembly and still finishes
first. The 1.54 is the figure to move, and it is not a compiler-emit figure:
the orchestration above the leaves is a handful of calls either way.

**Where we win, and by how much once the caveat is paid.** Signing, in both
configurations, but the column is not like for like: Graviola's `sign` does
SHA-384, a system-RNG read and an RFC 6979 nonce derivation that our kernel
does not. Timing those three separately bounds the part that can be
subtracted:

| configuration | component | ns/op | of `sign` |
|---|---|---|---|
| pure Rust | SHA-384 of the 25-byte message | 193 | 0.2% |
| pure Rust | system RNG, 16 bytes | 426 | 0.4% |
| pure Rust | RFC 6979 HMAC_DRBG, 7 × HMAC-SHA-384 | 5 422 | 5.0% |
| pure Rust | subtotal | 6 041 | 5.6% |
| pure Rust | `sign`, measured | 108 205 | 100% |
| pure Rust | arithmetic only, upper bound | 102 164 | — |
| CryptOpt assembly | subtotal of the same three | 6 022 | 5.4% |
| CryptOpt assembly | `sign`, measured | 112 181 | 100% |
| CryptOpt assembly | arithmetic only, upper bound | 106 159 | — |

Against that upper bound the sign ratio is at most 0.72 pure Rust and 0.54
with the assembly field, so the signing win survives the caveat in both
configurations. It comes from the fixed-base comb: Graviola's README states
that its P-384 base-point multiplication uses the same 5-bit window as its
variable-point one, "leaving some P384 base point performance on the table".

The subtraction is bounded and not exact. The three components are timed
outside `sign`, because `rfc6979_sign_with_random` is private and the `Hash`
parameter cannot be instantiated downstream; the DRBG figure is the
reconstruction described above, over Graviola's own `Hmac<Sha384>`. Whatever
else `sign` does — the private-key encode, the zeroise, the rejection test —
is unaccounted, so the arithmetic-only row is an upper bound and the ratio
against it is an upper bound too. **What could not be isolated:** Graviola's
arithmetic-only signing cost exactly, and its internal HMAC_DRBG object,
which is `pub(crate)`.

On the verify side the hash is 193 ns of a 206 189 ns row, 0.09%, so removing
it moves the pure-Rust ratio from 2.011 to 2.013 and the assembly ratio from
1.538 to 1.540. The message is 25 bytes, one SHA-384 block; a longer message
would raise Graviola's column and flatter ours, which is why a short one is
used.

### Against the previous kernel

The previous kernel used the Fermat scalar inverse and reached `u1*G + u2*Q`
through `p384_scalar_mul_base`, `p384_scalar_mul` and `p384_point_add`. Only
the ratio columns compare across the two dates: the RustCrypto baseline was
457 677 – 458 128 ns/op for sign and 838 679 – 839 781 for verify on the
earlier run and 505 166 – 506 812 and 927 494 – 951 083 here, on the same
machine, binary and pinning, with a Rocq worker on the box this time.

| configuration | op | ratio, previous | ratio, now |
|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 0.22 | 0.16 |
| fiat-crypto field, pure Rust | verify | 0.56 | 0.49 |
| CryptOpt assembly field | sign | 0.18 | 0.12 |
| CryptOpt assembly field | verify | 0.42 | 0.36 |

Nothing got slower. The movement is attributable to the two changes
separately, and the two micro-benchmarks account for it within 2%. Scaling
the previous absolute figures by the RustCrypto baseline's own movement puts
the previous kernel at 111.4 µs and 520.9 µs (pure Rust) and 93.3 µs and
401.2 µs (assembly) under this run's conditions. Signing calls the inverse
once and not the two-term multiply, so it should drop by the inverse's
30.8 µs; verification calls both, so it should drop by 30.8 µs plus the
34.7 µs (pure Rust) or 24.3 µs (assembly) of the multiply:

| configuration | op | previous, rescaled | predicted | measured |
|---|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 111.4 µs | 80.6 µs | 80.5 µs |
| fiat-crypto field, pure Rust | verify | 520.9 µs | 455.4 µs | 456.0 µs |
| CryptOpt assembly field | sign | 93.3 µs | 62.5 µs | 62.3 µs |
| CryptOpt assembly field | verify | 401.2 µs | 346.0 µs | 339.1 µs |

The rescaling is an estimate, not a measurement: it assumes our side and
RustCrypto's were slowed by the same factor between the two dates. The
micro-benchmarks are direct, and they are what the attribution rests on.

These are whole-operation numbers for an orchestration the compiler emitted
over our own verified leaves. They say nothing about the correctness of the emit;
that is the Lean equivalence proof, and a passing KAT is not a substitute for
it (the development repository's `bench/AGENTS.md`, "KAT vs correctness proof").

## Measured, the s2n-bignum backend

2026-09-16, same machine as the tables above (AMD Ryzen 7 PRO 7840U, Zen 4,
8 cores / 16 threads, Linux 7.0.0-31-generic, rustc 1.93.0, `--release`,
pinned to core 15). **The box was busier than during the run recorded above:
load average 2.4 to 4.9, with Lean workers on other cores throughout.** Every
absolute figure in this section is inflated by that — RustCrypto's sign
column reads 582 to 705 µs here against 462 to 469 µs there — so read the
ratios, which the round-robin interleaving protects, and not the absolutes.
Four processes were run, two per AUCurves field configuration, and the spread
between them is quoted on every row.

### The P-384 field multiply, which decides what could be built

Before any configuration was built on our own field kernels, the two emitted
P-384 field kernels in the tree were measured against s2n-bignum's. Neither
had been measured against anything recorded: the development repository's `bench/framework/geomean_ratios.tsv`
has no P-384 row, and the bench section of the development repository's `bench/p384_fieldmul_compare/README.md`
is deferred.

`src/bin/fieldbench.rs`, `--features s2n,emit-field`. Known-answer gate
first, 100 361 operand pairs per arm — all pairs of corner operands plus
100 000 random pairs below `p` — every output byte-identical to a reference
built from `bignum_montmul_p384` itself, and every output below `p`. No
timing is printed unless every arm passes. Then a serial dependent chain,
301 samples of 2000 multiplies, arms interleaved in rotating order within
each sample. The figure is invariant-TSC reference cycles, minimum and
median.

| arm | computes | min cyc | med cyc | min ns | ratio to s2n |
|---|---|---|---|---|---|
| `p384_montmul_proven`, CatCrypt emit | `x y R⁻¹ mod p`, `R = 2^384` | 330.1 | 343.7 | 100.1 | **2.58** |
| `bignum_montmul_p384`, s2n-bignum | `x y R⁻¹ mod p`, `R = 2^384` | 127.9 | 132.1 | 38.8 | 1.00 |
| `p384::fp_mul`, fiat-crypto Rust | `x y R⁻¹ mod p` | 210.2 | 219.8 | 63.8 | 1.64 |
| `p384::fp_mul`, CryptOpt assembly | `x y R⁻¹ mod p` | 144.6 | 150.3 | 43.9 | 1.23 |
| `p384_mul_x86_from_lean`, CatCrypt emit | `x y mod p`, ordinary domain | 299.5 | 311.1 | 90.9 | 2.34 |

The two CryptOpt and fiat rows come from two processes (the field is a
compile-time choice); the other three rows are from the pure-Rust process and
reproduce in the assembly process to within 3%.

**The first row is the answer, and it is a loss.** Our emitted P-384
Montgomery multiply is **2.58× slower** than s2n-bignum's on the minima and
2.60× on the medians, on the same function, the same Montgomery domain, the
same six-limb layout and the same calling convention. Three runs gave 2.573,
2.575 and 2.581 on the minima, so the figure is not noise. It is also slower
than the fiat-crypto Rust it would replace, by a factor of 1.57.

This is consistent with what the development repository's `bench/p384_fieldmul_compare/README.md` already
says of the other kernel: correctness-first, unscheduled emit, with no
register-residence or scheduling pass applied. Nothing about the result is
surprising and nothing about it is hidden.

The Solinas row is a different shape of comparison and not a like-for-like
one: it computes `x y mod p` in the ordinary domain through a 6×6 MULX/ADCX
schoolbook and a derived signed eleven-term Solinas reduction, where the
montmul rows compute `x y R⁻¹ mod p`. It does more of one kind of work and
none of another. It is timed as the other emitted P-384 field kernel; it does not substitute
for the montmul.

**Consequence for the backends.** A fourth configuration with our emitted
field kernels under the group law was not built. On these numbers it would be
slower than all three existing ones and would answer no question the others
do not. The field layer is where the work is, and until the emitted montmul
is within reach of 127 cycles there is nothing to compose it into. Note also
that a mixed configuration would have to be internally consistent about the
Montgomery domain: `p384_montmul_proven` and `bignum_montmul_p384` agree on
`R = 2^384`, but `p384_mul_x86_from_lean` is in the ordinary domain and
cannot be dropped in beside either.

At the group layer there is nothing to compose at all. The six-limb emitted
point-operation stack has uninhabited realizer bundles and a ladder that
cannot read its scalar, so the group law in every configuration here comes
from AUCurves or from s2n-bignum.

### The base-point multiply, the first orchestration lever

The comb against the archive's own windowed multiplication, on identical
s2n-bignum arithmetic. 15 repetitions of 200 iterations, round-robin. The
second row is the route Graviola takes for its base point.

| route | ns/op, pure process | ns/op, assembly process | ratio |
|---|---|---|---|
| `p384_montjscalarmul` on `G` (as Graviola) | 151 409 | 128 834 | 1.00 |
| fixed-base comb, `w = 5`, `p384_montjmixadd` | 29 261 | 25 433 | **0.19 – 0.20** |
| AUCurves fixed-base comb, `w = 5`, for scale | 102 404 | 64 091 | 0.68 / 0.50 |

The first two rows run the same field operations and the same point
operations. They differ only in how the multiplication is organised, so the
ratio is the comb's alone: **5.1× on the base-point multiply**, from trading
three hundred and eighty-four doublings for a 229 KB table. The repeat
process gave 0.19 and 0.19.

### The two-term multiply, the second lever

| backend | route | ns/op, pure | ns/op, assembly | ratio |
|---|---|---|---|---|
| `aucurves` | `mul_base` + `mul` + `add`, 3 leaves | 1 114 346 | 733 373 | 1.00 |
| `aucurves` | interleaved, `w = 5` | 648 330 | 422 349 | 0.58 |
| `s2n` | `mul_base` + `mul` + `add`, 3 leaves | 302 991 | 279 040 | 1.00 |
| `s2n` | interleaved, `w = 5` | 185 161 | 169 004 | **0.61** |

The `s2n` split route, 303 µs and 279 µs, is within a few percent of
Graviola's whole verify row measured in the same processes (298 µs and 286
µs), which is the expected reading of a verification that performs two
separate window multiplications and one addition.

### The scalar inverse

15 repetitions of 4000 iterations, round-robin, pure-Rust process.

| inverse | ns/op | vs Fermat |
|---|---|---|
| Fermat `a^(n-2)`, 383 squarings + 287 multiplications | 45 742 | 1.00 |
| divstep, 15 × 59, `safegcd_p384_order` | 3 045 | 0.07 |
| base-field `fp_inv`, for scale | 3 371 | 0.07 |
| s2n-bignum generic `bignum_modinv` at the group order | 3 119 | 0.07 |

s2n-bignum has **no** group-order inverse for P-384: `bignum_inv_p384` and
`bignum_montinv_p384` are both modulo the field prime. What it has is the
generic `bignum_modinv` for an arbitrary odd modulus, and that is the last
row. It computes the same function as the divstep inverse
(`tests/s2n.rs::generic_modinv_matches_the_divstep_inverse`, sixteen random
scalars) and runs within 3% of it across all four processes, sometimes above
and sometimes below. On that showing there is no reason to swap, and the
`s2n` backend keeps the crate's divstep inverse, as every other backend does.

### Whole operation, three backends

15 repetitions of 300 iterations, one process per AUCurves field
configuration, every side interleaved round-robin inside each. The `s2n`
rows appear in both processes and should agree; the spread between them
bounds the run-to-run drift.

Pure-Rust process, first run:

| op | backend | ours ns/op | RustCrypto | vs RC | Graviola | vs GV |
|---|---|---|---|---|---|---|
| sign | `aucurves` | 108 486 | 704 823 | 0.15 | 176 435 | 0.61 |
| sign | `s2n` | 34 459 | 704 823 | 0.05 | 176 435 | **0.20** |
| verify | `aucurves` | 649 971 | 1 294 174 | 0.50 | 297 669 | 2.18 |
| verify | `s2n` | 193 854 | 1 294 174 | 0.15 | 297 669 | **0.65** |

CryptOpt-assembly process, first run:

| op | backend | ours ns/op | RustCrypto | vs RC | Graviola | vs GV |
|---|---|---|---|---|---|---|
| sign | `aucurves` | 79 333 | 626 086 | 0.13 | 153 930 | 0.52 |
| sign | `s2n` | 32 005 | 626 086 | 0.05 | 153 930 | **0.21** |
| verify | `aucurves` | 431 953 | 1 162 307 | 0.37 | 286 174 | 1.51 |
| verify | `s2n` | 167 488 | 1 162 307 | 0.14 | 286 174 | **0.59** |

Four processes, the ratios that matter:

| ratio | pure #1 | pure #2 | asm #1 | asm #2 |
|---|---|---|---|---|
| `s2n` sign / Graviola | 0.20 | 0.20 | 0.21 | 0.21 |
| `s2n` verify / Graviola | 0.65 | 0.59 | 0.59 | 0.62 |
| `s2n` sign / RustCrypto | 0.05 | 0.05 | 0.05 | 0.05 |
| `s2n` verify / RustCrypto | 0.15 | 0.14 | 0.15 | 0.14 |
| `aucurves` verify / Graviola | 2.18 | 2.04 | 1.51 | 1.51 |

The `aucurves` ratios reproduce the run recorded in the section above — 0.15
to 0.16 and 0.50 for sign and verify against RustCrypto pure-Rust, 0.13 and
0.37 with the assembly field, 1.51 against Graviola — which is the check that
the harness change did not move them.

**On identical s2n-bignum arithmetic, our orchestration beats Graviola on
both operations: sign at 0.20 to 0.21, verify at 0.59 to 0.65.** Graviola's
sign column is its whole API and not like for like; subtracting the three
components it performs and our kernel does not (SHA-384, the system-RNG read
and the RFC 6979 HMAC_DRBG nonce, 5.1% and 5.4% of the row) puts the bound at
0.21 pure and 0.22 assembly, so the signing win survives the caveat with room
to spare. The verify row needs no caveat beyond the 0.09% message hash.

Where the two wins come from, in the same processes: the base-point multiply
at 0.19 of the route Graviola takes, and the two-term multiply at 0.61 of the
two-separate-multiplications route its verification takes. Those two
micro-benchmarks account for the two whole-operation rows.

**The `aucurves` verify row against Graviola is still a loss**, 1.51 with the
assembly field, unchanged from the earlier run. That row compares our group
law on a CryptOpt field against s2n-bignum assembly, which is a different
question from the one the `s2n` row answers, and both are kept for that
reason. What the `s2n` row shows is that the 1.51 is not an orchestration
deficit: with the arithmetic held fixed the same orchestration wins by a
factor of 1.6 on the same operation.

## Measured, OpenSSL and BoringSSL

2026-09-16, the same machine as the sections above (AMD Ryzen 7 PRO 7840U,
Linux 7.0.0-31-generic, rustc 1.93.0, `--release`, pinned to core 15), 15
repetitions of 300 iterations, every column interleaved round-robin in one
process. **The box was loaded: load average 3.8 to 9.6 across the runs, with
Lean workers and another field benchmark on other cores**, so the
absolute figures are inflated and vary by up to a factor of two between
processes; the
ratios, which the interleaving protects, are what is reported. Eight
processes were run: four of the committed binary (load 7.2 to 9.6) and,
before it, four of a binary identical in every timed arm except that it
lacked the BoringSSL nonce-derivation arm (load 3.8 to 7.0).

Absolute figures, committed binary, the lower-load process of each pair:

| configuration | op | backend | ours | RustCrypto | Graviola | OpenSSL | BoringSSL |
|---|---|---|---|---|---|---|---|
| pure Rust | sign | `aucurves` | 110 695 | 678 005 | 164 552 | 891 753 | 536 049 |
| pure Rust | sign | `s2n` | 33 877 | 678 005 | 164 552 | 891 753 | 536 049 |
| pure Rust | verify | `aucurves` | 621 089 | 1 240 531 | 296 337 | 700 770 | 557 621 |
| pure Rust | verify | `s2n` | 187 960 | 1 240 531 | 296 337 | 700 770 | 557 621 |
| CryptOpt | sign | `aucurves` | 97 202 | 815 286 | 198 086 | 914 053 | 594 536 |
| CryptOpt | sign | `s2n` | 37 623 | 815 286 | 198 086 | 914 053 | 594 536 |
| CryptOpt | verify | `aucurves` | 508 338 | 1 418 192 | 333 705 | 790 534 | 610 648 |
| CryptOpt | verify | `s2n` | 197 543 | 1 418 192 | 333 705 | 790 534 | 610 648 |

ns/op, median of the per-repetition figures. The OpenSSL and BoringSSL sign
columns are the nonce-supplied ones.

Ratios, ours over theirs, range over the four processes of each field
configuration (eight for the `s2n` rows, which do not depend on it):

| op | our row | vs OpenSSL | vs BoringSSL | tier against both |
|---|---|---|---|---|
| sign | `aucurves`, pure Rust | 0.11 – 0.13 | 0.19 – 0.21 | not same tier, against us |
| sign | `aucurves`, CryptOpt | 0.10 – 0.11 | 0.14 – 0.16 | same tier on the field |
| sign | `s2n` | 0.03 – 0.04 | 0.05 – 0.06 | not same tier, in our favour |
| verify | `aucurves`, pure Rust | 0.83 – 0.89 | **1.11 – 1.28** | not same tier, against us |
| verify | `aucurves`, CryptOpt | 0.61 – 0.68 | 0.74 – 0.85 | same tier on the field |
| verify | `s2n` | 0.24 – 0.27 | 0.31 – 0.37 | not same tier, in our favour |

The sign rows against BoringSSL are like for like; against OpenSSL they are
against the reconstruction described above. The verify rows are like for
like on both.

**Where we lose.** Verification in the pure-Rust `aucurves` configuration
against BoringSSL, 1.11 in three of the four processes and 1.28 in the most
loaded one:
our group law and orchestration over the fiat-crypto Rust field are slower
than BoringSSL's C group law over its generic assembly Montgomery loop. The
same row is a win against OpenSSL (0.83 to 0.89), and with the CryptOpt field
it is a win against both (0.61 to 0.68 and 0.74 to 0.85). Against Graviola
the losses recorded above stand, unchanged in these runs: 1.88 to 2.10 pure
Rust and 1.46 to 1.61 with the CryptOpt field. Every other row is a win.

Signing, full API against the nonce-supplied column:

| process | BoringSSL, nonce supplied | BoringSSL, `ECDSA_do_sign` | its nonce derivation | OpenSSL, nonce supplied | OpenSSL, `ECDSA_do_sign` | `BN_generate_dsa_nonce` |
|---|---|---|---|---|---|---|
| pure Rust | 536 049 | 540 872 | 893 | 891 753 | 862 858 | 2 577 |
| CryptOpt | 594 536 | 641 323 | 1 023 | 914 053 | 945 265 | 2 885 |

The nonce derivation is 0.2% of BoringSSL's signature and 0.3% of OpenSSL's
(0.9 to 1.4 µs and 2.1 to 3.5 µs over all processes). The full-API minus
nonce-supplied difference moves between −85 µs and +115 µs across processes,
two orders of magnitude above the component it would measure, so it does not
resolve the derivation, and on this box it cannot distinguish the OpenSSL
reconstruction from the production entry point either. Against the full API
the sign ratios are 0.14 to 0.20 (`aucurves`) and 0.05 to 0.06 (`s2n`) for
BoringSSL, 0.10 to 0.13 and 0.03 to 0.04 for OpenSSL; they are not like for
like, and differ from the nonce-supplied ratios by less than the spread.

`openssl speed -seconds 3 ecdsap384` on core 15 in the same window gives
977.6 signs/s and 1363.1 verifies/s, 1.02 ms and 734 µs, through the EVP
provider path; the harness's `ECDSA_do_sign` and `ECDSA_do_verify` figures
over the eight processes, 0.72 to 1.24 ms and 0.58 to 0.97 ms, are the same
magnitude.

**What could not be isolated or verified.** OpenSSL's nonce-supplied signing
cost through its own `ecdsa_sign_setup`: no exported entry point takes `k`,
so the column is the public-API reconstruction. BoringSSL's nonce derivation
inside `ECDSA_do_sign`: `BCM_rand_bytes_with_additional_data` is not
exported, so the component is `BN_rand_range_ex` with zero additional data.
The OpenSSL 3.0.13 source was read from the upstream tag, not from Ubuntu's
patched source package, which is not on this machine; the build options
`openssl version -a` prints do not change the method selection it describes.

## Measured, AWS-LC

2026-09-16, the machine of [§ Measured, the AUCurves backends](#measured-the-aucurves-backends), pinned to core 15, one
process of the pure-Rust AUCurves build (`P384_NO_CRYPTOPT=1`),
`BENCH_SECTIONS=dhkem,ecdsa BENCH_REPS=15 BENCH_ITERS=300`, every column
interleaved round-robin. **Load average 4.0 before the run and 6.7 after**,
with Lean and C compiler processes on other cores, so absolute figures are
from a loaded machine. `gen/` held the emitted ECDSA sources and no DHKEM
source, so the ECDSA rows are emitted kernels and the DHKEM rows the
transcription.

| op | ours `aucurves` | ours `s2n` | AWS-LC | `aucurves` / AWS-LC | `s2n` / AWS-LC |
|---|---|---|---|---|---|
| sign, nonce supplied | 97 407 | 30 356 | 74 443 | **1.31** | 0.41 |
| verify | 532 002 | 155 941 | 176 936 | **3.01** | 0.88 |
| sign, AWS-LC full API | | | 81 541 | 1.19 | 0.37 |

ns/op, median of the per-repetition figures. AWS-LC's nonce-derivation arm
is 603 ns. In the same process: OpenSSL 3.0.13 sign 762 421 and verify
622 992, BoringSSL 491 900 and 483 369, Graviola 145 965 and 269 249.

**Where we lose.** Both `aucurves` rows. In the pure-Rust configuration our
group law over the fiat-crypto Rust field is slower than AWS-LC's comb and
wNAF over s2n-bignum assembly: 1.31 on signing and 3.01 on verification. The
same arithmetic tier is the `s2n` row, which is faster on both, 0.41 and
0.88. Two differences on the signing path are known from the sources and
were not isolated inside AWS-LC: its scalar inverse is Fermat over the
generic `bn_mul_mont_nohw`, where the `s2n` backend calls the divstep
inverse (in this process our own Fermat chain took 38.7 µs and the divstep
2.6 µs), and its comb is `ec_nistp_scalar_mul_base` in C with a C point
addition, where ours is `src/comb_s2n.rs`. Both sides verify with a width-5 two-term pass over
the same field, and the verification margin is the narrower one.

The CryptOpt and s2n-montmul AUCurves field configurations were not run
against AWS-LC.

## Measured, DHKEM(P-384, HKDF-SHA384)

2026-09-16, the machine of [§ Measured, the AUCurves backends](#measured-the-aucurves-backends), rustc 1.93.0,
`--release`, pinned to core 15, `BENCH_SECTIONS=dhkem BENCH_REPS=15
BENCH_ITERS=300`, one process per AUCurves field configuration, every arm
interleaved round-robin within the process. **The load average was 6.6 to
8.7 throughout** — two C compiler processes, Lean and Python were running on
other cores — so these are figures from a loaded machine. The `s2n` rows
appear in all three processes and differ by up to 7% (encap 188.7 to 195.4
µs, decap 149.8 to 161.0 µs), which bounds the run-to-run drift. Both DHKEM
kernels were the transcription (`gen/` held no DHKEM file).

Median µs per operation. `pure`, `asm` and `s2n-f` are the processes with the
AUCurves field in fiat-crypto Rust, the CryptOpt assembly, and s2n-bignum's
`bignum_montmul_p384`/`bignum_montsqr_p384` (`P384_S2N_FIELD`); only the
`ours/aucurves` row runs a different field in each, the others show the drift.

| op | implementation | kind | arithmetic | pure | asm | s2n-f |
|---|---|---|---|---|---|---|
| encap | ours, `aucurves` | transcription | AUCurves RCB over the column's field | 692.5 | 484.4 | 413.2 |
| encap | ours, `s2n` | transcription | s2n-bignum asm | 195.4 | 188.7 | 192.0 |
| encap | reference | reconstruction | RustCrypto `p384` 0.13.1, fiat Rust | 1303.7 | 1312.4 | 1223.7 |
| encap | hpke-rs `setup_sender` | native, + DeriveKeyPair + key schedule | RustCrypto `p384` 0.13.1 | 1411.8 | 1303.1 | 1237.8 |
| encap | hpke-rs provider | reconstruction | RustCrypto `p384` 0.13.1 | 1337.4 | 1282.5 | 1240.7 |
| encap | Graviola 0.4.1 | reconstruction | s2n-bignum asm | 348.0 | 320.3 | 320.6 |
| encap | BoringSSL | reconstruction | generic Montgomery C, `bn_mul_mont_nohw` | 1132.9 | 1064.1 | 1006.5 |
| encap | OpenSSL 3.0.13 | reconstruction | `EC_GFp_mont`, `x86_64-mont` | 2346.8 | 2280.3 | 2191.7 |
| encap | OpenSSL 3.6.0 | reconstruction | `EC_GFp_mont`, `x86_64-mont` (inferred) | 1854.6 | 1787.7 | 1720.3 |
| encap | OpenSSL 3.6.0 DHKEM | native, + DeriveKeyPair | as above | 1780.1 | 1730.3 | 1666.1 |
| decap | ours, `aucurves` | transcription | AUCurves RCB over the column's field | 591.7 | 415.5 | 341.0 |
| decap | ours, `s2n` | transcription | s2n-bignum asm | 161.0 | 150.6 | 149.8 |
| decap | reference | reconstruction | RustCrypto `p384` 0.13.1 | 671.9 | 657.9 | 608.4 |
| decap | hpke-rs `setup_receiver` | native, + pk(skR) + key schedule | RustCrypto `p384` 0.13.1 | 1333.8 | 1319.1 | 1256.7 |
| decap | hpke-rs provider | reconstruction | RustCrypto `p384` 0.13.1 | 663.6 | 631.8 | 622.7 |
| decap | Graviola 0.4.1 | reconstruction | s2n-bignum asm | 176.7 | 170.0 | 164.0 |
| decap | BoringSSL | reconstruction | generic Montgomery C | 546.7 | 517.8 | 495.6 |
| decap | OpenSSL 3.0.13 | reconstruction | `EC_GFp_mont` | 1462.1 | 1440.7 | 1412.8 |
| decap | OpenSSL 3.6.0 | reconstruction | `EC_GFp_mont` (inferred) | 914.5 | 957.5 | 909.3 |
| decap | OpenSSL 3.6.0 DHKEM | native | as above | 896.8 | 875.1 | 864.2 |

The ratios that decide the comparison, ours / theirs:

| ratio | pure | asm | s2n-f |
|---|---|---|---|
| `s2n` encap / Graviola | 0.56 | 0.59 | 0.60 |
| `s2n` decap / Graviola | 0.91 | 0.89 | 0.91 |
| `aucurves` encap / Graviola | 1.99 | 1.51 | 1.29 |
| `aucurves` decap / Graviola | 3.35 | 2.44 | 2.08 |
| `aucurves` encap / hpke-rs, adjusted | 0.50 | 0.38 | 0.34 |
| `aucurves` decap / hpke-rs, adjusted | 0.89 | 0.61 | 0.55 |
| `s2n` encap / hpke-rs, adjusted | 0.14 | 0.15 | 0.16 |
| `s2n` decap / hpke-rs, adjusted | 0.24 | 0.22 | 0.24 |
| `aucurves` decap / BoringSSL | 1.08 | 0.80 | 0.69 |
| `s2n` encap / OpenSSL 3.6 DHKEM | 0.11 | 0.11 | 0.12 |
| `s2n` decap / OpenSSL 3.6 DHKEM | 0.18 | 0.17 | 0.17 |

"Adjusted" subtracts from hpke-rs's native row the separately timed parts
our kernel does not perform: the base-mode key schedule (10.0 to 11.2 µs)
from both, the KDF part of `DeriveKeyPair` (2.7 to 2.9 µs, timed over `hkdf`
0.12 as an estimate) from encap, and `pk(skR)` (621 to 657 µs) from decap.
hpke-rs's `setup_receiver` recomputes `pkR` from `skR` on every call
(`dh_kem::decaps`), which roughly doubles its decapsulation cost. The
OpenSSL 3.6 DHKEM encap row still includes `DeriveKeyPair`, whose KDF part
is under 5 µs of its 1.7 ms.

**The HKDF share is small.** `ExtractAndExpand` alone, µs: ours 3.0 to 3.8,
the reference 3.0 to 3.1, hpke-rs's provider 2.9 to 3.7, Graviola's HMAC 2.5
to 2.9, BoringSSL 2.4 to 2.6, OpenSSL 3.0 4.3 to 5.0, OpenSSL 3.6 4.0 to 4.7.
It is 0.5 to 1.0% of our `aucurves` rows and 1.9 to 2.3% of our `s2n` rows;
the rest is the two scalar multiplications (encap) or one (decap).

**Where we lose.**

* **`aucurves` against Graviola, in every field configuration**: encap 1.29
  to 1.99, decap 2.08 to 3.35. This is our group law and variable-base
  multiply over fiat-crypto, CryptOpt or s2n-bignum field code against
  s2n-bignum's Jacobian point operations; with the arithmetic held equal
  (the `s2n` row) the same orchestration wins on both operations, so the
  loss is in the arithmetic under the leaves, not in the emitted sequence.
  Decap loses by more because it has no fixed-base multiply, where the comb
  recovers ground.
* **`aucurves` pure-Rust decap against the BoringSSL reconstruction**: 1.08.
  BoringSSL runs C with an assembly Montgomery loop, so this is not
  same-tier; with an assembly field under AUCurves the row is 0.80 or 0.69.
* **The `s2n` decap margin over Graviola is narrow**: 0.89 to 0.91, within
  the order of the drift between processes. Both run a width-5 window over
  the same point operations; our decap has no comb to spend.
* **Our KDF leaves take 1.3 to 1.5 times as long as BoringSSL's HKDF**, the
  fastest here, about 1 µs per operation; against the reference and
  hpke-rs's provider the difference is within the noise.

Against the same-tier production opponent, hpke-rs over RustCrypto
(`aucurves` pure-Rust row), ours is faster: 0.50 encap and 0.89 decap
adjusted, 0.49 and 0.44 unadjusted. Against the C libraries in these three
processes every row of ours is faster except the BoringSSL decap above.

**AWS-LC and OpenSSL 4.1.0-dev**, a later single process: pure-Rust
AUCurves build, `BENCH_SECTIONS=dhkem,ecdsa BENCH_REPS=15 BENCH_ITERS=300`,
core 15, `P384_OPENSSL36_LIBCRYPTO` set to the 4.1.0-dev build, load average
4.0 before and 6.7 after (the run whose ECDSA rows are in
[§ Measured, AWS-LC](#measured-aws-lc)). Median µs per operation,
and ours over theirs:

| op | implementation | kind | µs | `aucurves` / this | `s2n` / this |
|---|---|---|---|---|---|
| encap | ours, `aucurves` | transcription | 627.6 | 1.00 | 0.27 |
| encap | ours, `s2n` | transcription | 170.3 | 3.68 | 1.00 |
| encap | Graviola 0.4.1 | reconstruction | 301.2 | 2.08 | 0.57 |
| encap | BoringSSL | reconstruction | 974.9 | 0.64 | 0.17 |
| encap | AWS-LC 5.9.0 | reconstruction | 200.8 | **3.13** | 0.85 |
| encap | OpenSSL 4.1.0-dev | reconstruction | 2261.1 | 0.28 | 0.08 |
| encap | OpenSSL 4.1.0-dev DHKEM | native, + DeriveKeyPair | 1548.0 | 0.41 | 0.11 |
| decap | ours, `aucurves` | transcription | 517.6 | 1.00 | 0.27 |
| decap | ours, `s2n` | transcription | 138.1 | 3.75 | 1.00 |
| decap | Graviola 0.4.1 | reconstruction | 151.3 | 3.42 | 0.91 |
| decap | BoringSSL | reconstruction | 477.6 | **1.08** | 0.29 |
| decap | AWS-LC 5.9.0 | reconstruction | 138.3 | **3.74** | **1.00** |
| decap | OpenSSL 4.1.0-dev | reconstruction | 1539.7 | 0.34 | 0.09 |
| decap | OpenSSL 4.1.0-dev DHKEM | native | 789.3 | 0.66 | 0.17 |

AWS-LC's `ExtractAndExpand` alone took 2.6 µs, OpenSSL 4.1.0-dev's 3.1 µs.

* **`s2n` decap against AWS-LC is a tie**: 138.1 against 138.3 µs, a ratio
  of 1.00. Both run the same s2n-bignum field and the same assembly
  variable-base multiply by name (`p384_montjscalarmul`), plus the SEC1
  decoding and validation and the KDF; AWS-LC's figure also includes the
  per-call `EC_KEY` copy and `EC_KEY_check_fips`. `s2n` encap is 0.85;
  encap adds a fixed-base multiply, which is AWS-LC's C comb on one side and
  `src/comb_s2n.rs` on the other, and the split of the difference was not
  measured.
* **`aucurves` pure Rust loses to AWS-LC** by 3.13 (encap) and 3.74
  (decap), the same shape as the Graviola loss above: Rust group law over
  the fiat-crypto Rust field against s2n-bignum assembly.
* The OpenSSL 4.1.0-dev reconstruction is slower than its own native DHKEM
  (2261 against 1548 µs encap, 1540 against 789 µs decap). The
  reconstruction builds its `EVP_PKEY` objects and KDF contexts on every
  call; its cost was not decomposed.

### Emitted kernels

`lake exe emit-p384-rust` wrote `gen/p384_dhkem_encap.rs` and
`gen/p384_dhkem_decap.rs` on 2026-09-17; the build reports both as emitted.
`P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n,production`
passes 116 tests on them. Bench: pure-Rust AUCurves build,
`BENCH_SECTIONS=dhkem BENCH_REPS=15 BENCH_ITERS=300`, core 15,
`P384_OPENSSL36_LIBCRYPTO` set to the 4.1.0-dev build, load average 1.7 before
and 2.5 after. Median µs per operation, and ours over theirs:

| op | implementation | kind | µs | `aucurves` / this | `s2n` / this |
|---|---|---|---|---|---|
| encap | ours, `aucurves` | emitted | 523.2 | 1.00 | 0.27 |
| encap | ours, `s2n` | emitted | 140.2 | 3.73 | 1.00 |
| encap | Graviola 0.4.1 | reconstruction | 240.7 | 2.17 | 0.58 |
| encap | AWS-LC 5.9.0 | reconstruction | 163.0 | 3.21 | 0.86 |
| encap | hpke-rs 0.7.0 | native, + DeriveKeyPair, + key schedule | 1007.1 | 0.52 | 0.14 |
| encap | BoringSSL | reconstruction | 852.3 | 0.61 | 0.16 |
| encap | OpenSSL 4.1.0-dev DHKEM | native, + DeriveKeyPair | 1327.5 | 0.39 | 0.11 |
| decap | ours, `aucurves` | emitted | 440.1 | 1.00 | 0.27 |
| decap | ours, `s2n` | emitted | 116.7 | 3.77 | 1.00 |
| decap | Graviola 0.4.1 | reconstruction | 123.0 | 3.58 | 0.95 |
| decap | AWS-LC 5.9.0 | reconstruction | 118.7 | 3.71 | 0.98 |
| decap | hpke-rs 0.7.0 | native, + pk(skR), + key schedule | 998.5 | 0.44 | 0.12 |
| decap | BoringSSL | reconstruction | 427.8 | 1.03 | 0.27 |
| decap | OpenSSL 4.1.0-dev DHKEM | native | 664.8 | 0.66 | 0.18 |

The emitted `s2n` rows are 0.86 (encap) and 0.98 (decap) of AWS-LC and 0.58
and 0.95 of Graviola; the decap margins are within the run-to-run drift
recorded above. The `aucurves` pure-Rust rows lose to Graviola and AWS-LC by
2.2–3.7 and to BoringSSL decap by 1.03. All rows of this run are faster than
the earlier runs, including the opponents, because the machine was less
loaded; compare within a run only.

## Measured, all field configurations (2026-09-17)

One process per AUCurves field configuration, run one after another, each with
`BENCH_SECTIONS=ecdsa,dhkem BENCH_REPS=15 BENCH_ITERS=300
BENCH_MICRO_ITERS=4000`, `--features s2n,production`, core 15, OpenSSL 4.1.0-dev
for the native DHKEM row. The load average was 2.8–3.8 in the first three
processes. The last two processes, with `P384_S2N_FIELD` set to
the encoded montmul of `bench/s2n_import` (`make encode-montmul`) and to the framed file with
its symbol renamed, ran later on a quieter machine, and their opponent columns
are 5–10 % lower than in the first three. Compare rows within one process only.
Median µs per operation; the `aucurves` rows change with the field, the `s2n`
rows are the s2n-bignum backend in the same process.

| field under `aucurves` | sign `aucurves` | sign `s2n` | verify `aucurves` | verify `s2n` | encap `aucurves` | decap `aucurves` | base-point comb `aucurves` |
|---|---|---|---|---|---|---|---|
| fiat-crypto Rust | 94.9 | 29.3 | 543.7 | 161.0 | 560.6 | 454.8 | 82.0 |
| CryptOpt assembly | 68.7 | 28.0 | 380.4 | 151.7 | 386.3 | 328.0 | 59.2 |
| s2n-bignum montmul and montsqr | 56.2 | 26.5 | 293.0 | 141.9 | 310.6 | 262.9 | 49.8 |
| our encoded montmul (square as montmul) | 53.1 | 25.0 | 272.8 | 132.3 | 288.4 | 241.6 | 44.3 |
| our framed montmul (square as montmul) | 53.1 | 25.0 | 278.0 | 132.6 | 287.7 | 240.5 | 44.6 |

Ratios, ours over the opponent in the same process, for the pure-Rust process
(`aucurves` / `s2n`):

| op | RustCrypto | Graviola | OpenSSL 3.0 | BoringSSL | AWS-LC |
|---|---|---|---|---|---|
| sign | 0.16 / 0.05 | 0.65 / 0.20 | 0.13 / 0.04 | 0.20 / 0.06 | 1.26 / 0.39 |
| verify | 0.51 / 0.15 | 2.16 / 0.64 | 0.91 / 0.27 | 1.12 / 0.33 | 3.12 / 0.92 |

and for the process with our encoded montmul:

| op | RustCrypto | Graviola | OpenSSL 3.0 | BoringSSL | AWS-LC |
|---|---|---|---|---|---|
| sign | 0.10 / 0.05 | 0.45 / 0.21 | 0.08 / 0.04 | 0.13 / 0.06 | 0.80 / 0.38 |
| verify | 0.29 / 0.14 | 1.27 / 0.61 | 0.52 / 0.25 | 0.65 / 0.31 | 1.80 / 0.87 |

The Graviola sign column is its whole API (hash, RNG and RFC 6979 nonce
included) and is not like for like; the verify column is. The two montmul files
differ only in the frame (red-zone moves or `push`/`pop`), and their rows agree
within the run-to-run spread.

## Measured, SymCrypt

2026-09-17, the machine of
[§ Measured, the AUCurves backends](#measured-the-aucurves-backends), rustc
1.93.0, `--features s2n,production`, core 15, `BENCH_SECTIONS=ecdsa,dhkem
BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000`, `P384_OPENSSL36_LIBCRYPTO`
set to the OpenSSL 4.1.0-dev build, `gen/` holding the emitted ECDSA and DHKEM
sources. Two processes, one after the other: `pure`, the AUCurves field in
fiat-crypto Rust (`P384_NO_CRYPTOPT=1`), and `enc`, the AUCurves field over the
encoded s2n-bignum montmul of `bench/s2n_import` (`P384_S2N_FIELD` naming the
file `make encode-montmul` writes there; README.md,
[§ DHKEM, Commands](README.md#commands-1), gives the path). **Load average** (1, 5, 15 min): `pure`
3.42, 3.56, 4.39 before and 2.28, 3.10, 4.12 after; `enc` 2.00, 2.98, 4.06
before and 3.03, 2.95, 3.91 after. SymCrypt is 103.13.0, the shared module
described in README.md, [§ SymCrypt](README.md#symcrypt-the-fourth-production-opponent).

Median µs per operation, and ours over SymCrypt in the same process. The
`s2n` backend does not depend on the AUCurves field; its two columns show the
drift between the processes.

| op | ours `aucurves`, pure | ours `aucurves`, enc | ours `s2n`, pure / enc | SymCrypt, pure / enc | `aucurves` / SymCrypt, pure / enc | `s2n` / SymCrypt, pure / enc |
|---|---|---|---|---|---|---|
| ECDSA sign (SymCrypt: full API, own nonce) | 84.1 | 55.3 | 26.6 / 26.2 | 165.6 / 165.6 | 0.51 / 0.33 | 0.16 / 0.16 |
| ECDSA verify | 475.9 | 286.8 | 140.1 / 137.9 | 184.8 / 184.7 | **2.58 / 1.55** | 0.76 / 0.75 |
| DHKEM encap (SymCrypt: reconstruction) | 507.4 | 314.5 | 138.3 / 144.0 | 309.4 / 320.1 | **1.64** / 0.98 | 0.45 / 0.45 |
| DHKEM decap (SymCrypt: reconstruction) | 429.6 | 266.9 | 114.9 / 118.7 | 160.8 / 165.9 | **2.67 / 1.61** | 0.71 / 0.72 |

Both of our DHKEM rows are the emitted kernels, and the ECDSA rows the
emitted orchestration.

**Signing.** SymCrypt's module exports no nonce-supplied entry point, so its
sign figure is `SymCryptEcDsaSign` with its own RNG nonce. The full-API table
of the same processes times the call again (165.4 µs pure, 165.5 µs enc) and
one 48-byte `SymCryptRandom` draw alone (0.39 µs, 0.38 µs); the difference,
165.0 µs and 165.1 µs, estimates SymCrypt's cost with the nonce supplied, and
the ratios against it are 0.51 and 0.16 (pure) and 0.33 and 0.16 (enc), equal
to two decimals to those above. The second draw inside the call, the blinding
factor of the `k` inversion, is in all of these figures on SymCrypt's side.

**Where we lose.**

* **`aucurves` verification and decapsulation, in both field
  configurations**: 2.58 and 2.67 with the fiat-crypto Rust field, 1.55 and
  1.61 with the encoded montmul. The pure-Rust rows are not same-tier
  (Rust field against SymCrypt's MULX assembly). The `enc` rows are same-tier
  on the field multiply, so the remaining loss is above it: our group law in
  Rust (complete RCB formulas, projective coordinates) over a field whose
  square is a multiply in this configuration, against SymCrypt's C Jacobian
  formulas over a dedicated square. The split was not measured. With the arithmetic replaced by s2n-bignum's (the `s2n` row) the
  same orchestration is faster than SymCrypt on both, 0.76 and 0.71, so the
  loss is under the leaves, not in the emitted sequence.
* **`aucurves` pure-Rust encapsulation**: 1.64. With the encoded montmul the
  row is 0.98, a tie within the drift between the processes (the `s2n`
  encap row moved by 4 % between them).

Every other row of ours is faster than SymCrypt: all four `s2n` rows (0.16 to
0.76) and both `aucurves` sign rows, though the sign rows compare a
nonce-supplied kernel with SymCrypt's full API.

**SymCrypt against the other opponents in the same processes** (pure): its
verification is 1.18 times AWS-LC's (184.8 against 156.9 µs) and 0.43 times
BoringSSL's; its full-API signature is 2.39 times AWS-LC's nonce-supplied one
(69.4 µs). Its encapsulation takes 1.92 times its decapsulation (309.4 against
160.8 µs): `Encap` computes `skE*G` at key import, a fixed-window multiply
with no comb, which is also the bulk of its signing cost. The reasons read
from the source (a fixed window of width 6 with about 380 doublings for
`k*G`, a group order handled by a MULX product and a division per multiply, a
blinded binary-GCD inverse, a heap allocation per call) were not isolated.
`SymCryptHkdf` took 1.8 µs (pure) and 1.9 µs (enc) for `ExtractAndExpand`,
the fastest KDF of the processes; ours took 2.4 and 2.6 µs.

**What could not be isolated or verified.** SymCrypt's nonce-supplied
signing cost: the entry point that takes `k` is not exported by the shared
module. The attribution of the `enc` verification and decapsulation loss to
the group law rather than to the square-as-multiply field configuration: no
run with a dedicated square under AUCurves was made against SymCrypt. The
CryptOpt configuration was not run against SymCrypt.
