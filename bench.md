# Benchmarks

The compiler emits assembly inside Lean. These benchmarks compare that emitted
assembly against deployed references, cycle-for-cycle on one host (AMD Ryzen 7 PRO
7840U, RDTSC, `taskset`-pinned). Ratios are ours / reference — below 1.0 is faster,
above 1.0 is slower. The emitted `.s` artifacts for the rows below ship under
`bench/`, each with a provenance header naming which symbols are owned-emit versus
`call <leaf>`. The timing harness is part of the wider CatCrypt development and is
not shipped here, so each ratio is cited to the development scoreboard rather than
re-run from this repository.

Comparisons are made only at matching scope — an emitted kernel against an emitted
or verified-scalar kernel, an adopted leaf against an adopted leaf — and each row is
one of:

- **like-for-like** — both sides at the same optimisation tier;
- **adopted leaf** — the emit rides a verified external leaf, so the ratio is near
  1.0 by construction;
- **partial** — a kernel whose whole-primitive assembly is not yet linked in a
  single binary, or a tier the owned register allocator has not yet closed; the
  ratio is a target, not a verdict.

## Field and bignum

The emitted arithmetic is the strongest tier: at parity with s2n-bignum's scalar
kernels, and ahead of libgmp at practical sizes.

| kernel | reference (same tier) | ratio |
|---|---|---|
| Curve25519 `fe25519_mul` (4×64) | s2n-bignum `bignum_mul_p25519` (scalar ADX) | 0.98× |
| 4-limb `bignum_mul_4_8` | s2n-bignum (scalar) | 1.05× (parity) |
| `mpn_mul_basecase` (cwhile4, n ≥ 16) | libgmp (scalar) | 0.79–0.90× |
| owned vs jasminc, 9 both-emit kernels | jasmin | 0.749× geomean |

## Symmetric

Stated at matching tier against the verified-C scalar references, the emitted
symmetric compression kernels are behind: this is where the owned register
allocator has the most headroom, and the rows are a partial target rather than a
result.

| primitive | reference (same tier) | ratio |
|---|---|---|
| SHA-256 compress | HACL\* scalar | ~6.6× (slower) |
| SHA-512 compress | HACL\* scalar | ~5.1–5.7× (slower) |
| HMAC-SHA256 (amortised) | HACL\* scalar | 1.06× |
| Keccak-f1600 | HACL\* | no same-tier win (~1.01×) |

## Elliptic curve

| operation | reference (same tier) | ratio |
|---|---|---|
| X25519 scalar-mul ladder (in-Lean, unadopted) | s2n-bignum | 1.857× (slower) |

The X25519 ladder is the modularity floor: where the compiler emits an unadopted
in-Lean kernel rather than riding a verified leaf, a scheduling factor remains.

## Pairing

| primitive | status |
|---|---|
| BLS12-377 | adopted leaf — the orchestration is owned-emit; the field and pairing arithmetic are `call`ed into the AUCurves verified bedrock2 tower, not emitted here. No committed ratio. |
| BN254 field multiply | uncurated — an auto-parsed 0.493× vs libgmp (scalar) whose tier is unconfirmed and which is not on the vetted scoreboard. |

## Artifacts

Each emitted row above ships its `.s` under `bench/<comparison>/` with a one-line
provenance header. Owned-emit (verified-compiler output, self-contained): SHA-256
and SHA-512 compress, Keccak-f1600, `fe25519_mul`, BN254 mont-mul. Adopted-leaf
(owned glue over a linked verified leaf): HMAC over the resident owned compress, and
the BLS12-377 orchestration over the AUCurves tower.
