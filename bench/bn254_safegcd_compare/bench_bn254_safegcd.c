/* BN254 (alt_bn128) Fp field-inversion bench: AUCurves BY-divstep leaf
 * (safegcd_bn254) — verified-CT Bernstein-Yang inverter.
 *
 * Headline path: the AUCurves-verified Bernstein-Yang inverter from
 * `src/safegcd_bn254.rs` of the AUCurves crate `curve25519-jasmin-rs` (a checkout at
 * `BLS/AUCurves/` beside this repository)
 * (`bn254_invert_divstep_sat`), re-exported via the staticlib shim in
 * `shim/src/lib.rs` under the C symbol `safegcd_bn254_invert`.
 *
 * Adopted as a verified-CT leaf via the verified-front extCall pattern
 * (CatCrypt/Crypto/Vale/SafegcdBN254.lean; verified-front emit driver in
 * bn254_safegcd_emit.lean).  #489 flipped the BN254 Fp inverse off the
 * prior Fermat a^(p-2) chain onto this divstep leaf.
 *
 * KAT: for each AUCurves in-tree test input (incl. p-1), verify
 *   x · BY^-1(x) ≡ 1 (mod p_{BN254})
 * using a schoolbook N-limb mul-mod REFERENCE computed here in C — the
 * same x·x^-1≡1 identity AUCurves' own `safegcd_bn254.rs::tests` checks.
 * No fabricated answer vectors: the KAT is a mathematical identity
 * verified against a schoolbook mul-mod.
 *
 * Methodology: MIN-of-SAMPLES, rdtsc cyc + clock_gettime ns, pin_to_cpu(3).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include <gmp.h>

#include "bn254_safegcd_ref.h"
#include "tscbench.h"
#include "affinity.h"

#define N 4  /* limbs */

/* BN254 base prime, 4×u64 LE (= AUCurves BN254_P_4X64). */
static const uint64_t P[N] = {
    0x3C208C16D87CFD47ULL,
    0x97816A916871CA8DULL,
    0xB85045B68181585DULL,
    0x30644E72E131A029ULL
};

/* AUCurves' own deterministic test inputs (safegcd_bn254.rs::tests),
 * including p-1.  Not fabricated outputs — the KAT checks the identity
 * x·x^-1 ≡ 1, so any nonzero input is a valid test. */
#define NTESTS 4
static uint64_t TESTS[NTESTS][N] = {
    {1, 0, 0, 0},
    {2, 0, 0, 0},
    {0x0123456789abcdefULL, 0xfedcba9876543210ULL, 0xdeadbeefULL, 0x1ULL},
    {0,0,0,0}  /* p-1, filled at runtime */
};

/* Schoolbook (a*b mod p) over N×u64 LE saturated limbs — bit-serial long
 * division reference (mirrors AUCurves' in-tree mul_mod_p). */
static void mul_mod_p(uint64_t out[N], const uint64_t a[N], const uint64_t b[N]) {
    uint64_t prod[2*N];
    memset(prod, 0, sizeof(prod));
    for (int i = 0; i < N; i++) {
        unsigned __int128 carry = 0;
        for (int j = 0; j < N; j++) {
            unsigned __int128 v =
                (unsigned __int128)a[i] * b[j] + prod[i+j] + carry;
            prod[i+j] = (uint64_t)v;
            carry = v >> 64;
        }
        prod[i+N] = (uint64_t)carry;
    }
    uint64_t p_ext[2*N], rem[2*N];
    memset(p_ext, 0, sizeof(p_ext));
    memset(rem, 0, sizeof(rem));
    for (int k = 0; k < N; k++) p_ext[k] = P[k];
    for (int bit = 2*N*64 - 1; bit >= 0; bit--) {
        uint64_t carry = 0;
        for (int k = 0; k < 2*N; k++) {
            uint64_t nc = rem[k] >> 63;
            rem[k] = (rem[k] << 1) | carry;
            carry = nc;
        }
        int limb = bit / 64, lbit = bit % 64;
        rem[0] |= (prod[limb] >> lbit) & 1;
        int ge = 1;
        for (int k = 2*N - 1; k >= 0; k--) {
            if (rem[k] > p_ext[k]) { ge = 1; break; }
            if (rem[k] < p_ext[k]) { ge = 0; break; }
        }
        if (ge) {
            __int128 borrow = 0;
            for (int k = 0; k < 2*N; k++) {
                __int128 v = (__int128)rem[k] - p_ext[k] - borrow;
                rem[k] = (uint64_t)v;
                borrow = (v < 0) ? 1 : 0;
            }
        }
    }
    for (int k = 0; k < N; k++) out[k] = rem[k];
}

static int is_zero(const uint64_t x[N]) {
    for (int k = 0; k < N; k++) if (x[k]) return 0;
    return 1;
}

/* GMP Fermat reference: out = x^(p-2) mod p — the prior BN254 inverse path
 * (bn254_inv, Vale/BN254.lean) computed this addition chain.  GMP's mpz_powm
 * is windowed (faster than a hand a^(p-2) addition chain), so the divstep/
 * fermat ratio below is CONSERVATIVE w.r.t. the chain it replaces. */
static mpz_t g_p, g_pm2, g_x, g_r;
static void gmp_setup(void) {
    mpz_inits(g_p, g_pm2, g_x, g_r, NULL);
    mpz_import(g_p, N, -1, sizeof(uint64_t), 0, 0, P);  /* LE limbs */
    mpz_sub_ui(g_pm2, g_p, 2);
}
static void fermat_inv(uint64_t out[N], const uint64_t x[N]) {
    mpz_import(g_x, N, -1, sizeof(uint64_t), 0, 0, x);
    mpz_powm(g_r, g_x, g_pm2, g_p);
    for (int k = 0; k < N; k++) out[k] = 0;
    size_t cnt = 0;
    mpz_export(out, &cnt, -1, sizeof(uint64_t), 0, 0, g_r);
}

static int kat_check(void) {
    /* fill p-1 */
    for (int k = 0; k < N; k++) TESTS[NTESTS-1][k] = P[k];
    TESTS[NTESTS-1][0] -= 1;

    uint64_t one[N]; memset(one, 0, sizeof(one)); one[0] = 1;
    for (int t = 0; t < NTESTS; t++) {
        uint64_t xi[N], prod[N];
        safegcd_bn254_invert(xi, TESTS[t]);
        if (is_zero(xi)) {
            fprintf(stderr, "KAT FAIL: BY^-1 = 0 for input %d\n", t);
            return 1;
        }
        mul_mod_p(prod, TESTS[t], xi);
        if (memcmp(prod, one, sizeof(one)) != 0) {
            fprintf(stderr, "KAT FAIL: x · BY^-1(x) != 1 (mod p_BN254) input %d\n", t);
            return 1;
        }
        /* cross-check: divstep inverse == GMP Fermat a^(p-2) inverse */
        uint64_t xf[N];
        fermat_inv(xf, TESTS[t]);
        if (memcmp(xi, xf, sizeof(xf)) != 0) {
            fprintf(stderr, "KAT FAIL: safegcd != fermat a^(p-2) for input %d\n", t);
            return 1;
        }
    }
    return 0;
}

static long REPS = 5000;
#define SAMPLES 3
static volatile uint64_t g_sink = 0;

static inline double ns_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    if (argc > 1) REPS = atol(argv[1]);
    if (REPS < 1) REPS = 1;
    pin_to_cpu(3);
    gmp_setup();

    if (kat_check() != 0) {
        fprintf(stderr, "ABORT: KAT failed; bench results would be meaningless\n");
        return 2;
    }
    printf("# KAT: OK — x · BY^-1(x) == 1 (mod p_BN254) for all %d AUCurves inputs\n", NTESTS);
    printf("#      (schoolbook mul-mod reference; inputs incl. p-1)\n");

    uint64_t x[N]; memcpy(x, TESTS[2], sizeof(x));
    uint64_t out[N];
    safegcd_bn254_invert(out, x); g_sink += out[0];

    printf("# BN254 Fp inversion bench (AUCurves BY-divstep, u64x%d)\n", N);
    printf("# REPS=%ld, SAMPLES=%d, MIN-of-SAMPLES, pin_to_cpu(3)\n\n", REPS, SAMPLES);

    double ns_min = 1e30; uint64_t cyc_min = ~0ULL;
    for (int s = 0; s < SAMPLES; s++) {
        uint64_t c0 = rdtsc_start();
        double t0 = ns_now();
        for (long r = 0; r < REPS; r++) { safegcd_bn254_invert(out, x); g_sink += out[0]; }
        double t1 = ns_now();
        uint64_t c1 = rdtsc_end();
        double v_ns = (t1 - t0) / (double)REPS;
        uint64_t v_cyc = (c1 - c0) / (uint64_t)REPS;
        if (v_ns < ns_min) ns_min = v_ns;
        if (v_cyc < cyc_min) cyc_min = v_cyc;
    }
    /* GMP Fermat a^(p-2) baseline (the prior bn254_inv path). */
    double f_ns_min = 1e30; uint64_t f_cyc_min = ~0ULL;
    for (int s = 0; s < SAMPLES; s++) {
        uint64_t c0 = rdtsc_start();
        double t0 = ns_now();
        for (long r = 0; r < REPS; r++) { fermat_inv(out, x); g_sink += out[0]; }
        double t1 = ns_now();
        uint64_t c1 = rdtsc_end();
        double v_ns = (t1 - t0) / (double)REPS;
        uint64_t v_cyc = (c1 - c0) / (uint64_t)REPS;
        if (v_ns < f_ns_min) f_ns_min = v_ns;
        if (v_cyc < f_cyc_min) f_cyc_min = v_cyc;
    }

    printf("%-40s %12s %12s\n", "impl", "ns/op", "cyc/op");
    printf("%-40s %12.1f %12llu\n",
           "AUCurves safegcd_bn254 (BY u64x4, CT)", ns_min, (unsigned long long)cyc_min);
    printf("%-40s %12.1f %12llu\n",
           "gmp fermat a^(p-2) (windowed, prior)", f_ns_min, (unsigned long long)f_cyc_min);
    printf("\n# ratio safegcd/fermat = %.3fx  (divstep vs GMP windowed Fermat;\n",
           (double)cyc_min / (double)f_cyc_min);
    printf("#   conservative — gmp powm is faster than a hand a^(p-2) chain)\n");
    return 0;
}
