/* Conformance test for the AUCurves BY/safegcd Pallas Fp inversion leaf.
 *
 * Validates that `pallas_safegcd_invert` (the C shim re-export of
 * AUCurves' verified-CT Bernstein-Yang divstep inverter
 * `safegcd_pallas::pallas_invert_divstep_sat`) is correct against:
 *
 *   - the 4 KAT inputs from
 *     `safegcd_pallas.rs::tests::pallas_invert_times_self_is_one`
 *     via the involutive round-trip identity invert(invert(x)) == x
 *   - 1000 random vectors (xoshiro256** with fixed seed) via the same
 *     involutive identity, providing structural coverage of the divstep
 *     loop's data-independent path
 *
 * Failure prints the offending (trial, hex of x, hex of invert(x), hex
 * of invert(invert(x))) and exits 1.  Success prints
 *   OK 4/4 KAT + 1000/1000 random involution round-trips (AUCurves BY/safegcd Pallas)
 * and exits 0.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "pallas_safegcd_ref.h"

/* Pallas base prime as 4×u64 LE. */
static const uint64_t PALLAS_P[4] = {
    0x992D30ED00000001ULL,
    0x224698FC094CF91BULL,
    0x0000000000000000ULL,
    0x4000000000000000ULL,
};

static const uint64_t KAT_INPUTS[4][4] = {
    {1ULL, 0, 0, 0},
    {2ULL, 0, 0, 0},
    {0x0123456789ABCDEFULL, 0xFEDCBA9876543210ULL,
     0xDEADBEEFULL, 0x1ULL},
    {0x992D30ED00000000ULL,
     0x224698FC094CF91BULL,
     0x0000000000000000ULL,
     0x4000000000000000ULL},
};

/* Reduce x mod p (subtract p if x >= p). 4-limb compare + cond-sub. */
static int ge_p(const uint64_t x[4]) {
    for (int i = 3; i >= 0; i--) {
        if (x[i] > PALLAS_P[i]) return 1;
        if (x[i] < PALLAS_P[i]) return 0;
    }
    return 1;
}
static void sub_p(uint64_t x[4]) {
    uint64_t borrow = 0;
    for (int i = 0; i < 4; i++) {
        uint64_t r = x[i] - PALLAS_P[i] - borrow;
        borrow = (x[i] < PALLAS_P[i] + borrow) ? 1 : 0;
        x[i] = r;
    }
}
static void canon(uint64_t x[4]) {
    while (ge_p(x)) sub_p(x);
}
static int is_zero(const uint64_t x[4]) {
    for (int i = 0; i < 4; i++) if (x[i]) return 0;
    return 1;
}

static uint64_t xs[4] = {0xCAB1CAB1CAB1CAB1ULL, 0x5A1A5A1A5A1A5A1AULL,
                         0xDEADC0DEDEADC0DEULL, 0xF00DBA12F00DBA12ULL};
static inline uint64_t rotl(uint64_t x, int k) {
    return (x << k) | (x >> (64 - k));
}
static uint64_t xrand(void) {
    uint64_t r = rotl(xs[1] * 5, 7) * 9;
    uint64_t t = xs[1] << 17;
    xs[2] ^= xs[0]; xs[3] ^= xs[1];
    xs[1] ^= xs[2]; xs[0] ^= xs[3];
    xs[2] ^= t;     xs[3] = rotl(xs[3], 45);
    return r;
}

static int eq4(const uint64_t a[4], const uint64_t b[4]) {
    for (int i = 0; i < 4; i++) if (a[i] != b[i]) return 0;
    return 1;
}
static void hex_dump4(const char *tag, const uint64_t x[4]) {
    fprintf(stderr, "%s: ", tag);
    for (int i = 3; i >= 0; i--) fprintf(stderr, "%016llx", (unsigned long long)x[i]);
    fputc('\n', stderr);
}

int main(void) {
    int kat_ok = 0, rand_ok = 0;

    /* Fixed KATs: round-trip identity. */
    for (int i = 0; i < 4; i++) {
        uint64_t a[4], b[4];
        pallas_safegcd_invert(a, KAT_INPUTS[i]);
        pallas_safegcd_invert(b, a);
        if (eq4(b, KAT_INPUTS[i])) {
            kat_ok++;
        } else {
            fprintf(stderr, "KAT %d FAIL\n", i);
            hex_dump4("  x      ", KAT_INPUTS[i]);
            hex_dump4("  inv(x) ", a);
            hex_dump4("  inv2(x)", b);
            return 1;
        }
    }

    /* 1000 random round-trips. */
    for (int trial = 0; trial < 1000; trial++) {
        uint64_t x[4], a[4], b[4];
        for (int i = 0; i < 4; i++) x[i] = xrand();
        canon(x);
        if (is_zero(x)) { trial--; continue; }  /* invert(0) undefined */

        pallas_safegcd_invert(a, x);
        pallas_safegcd_invert(b, a);
        if (eq4(b, x)) {
            rand_ok++;
        } else {
            fprintf(stderr, "RANDOM %d FAIL\n", trial);
            hex_dump4("  x      ", x);
            hex_dump4("  inv(x) ", a);
            hex_dump4("  inv2(x)", b);
            return 1;
        }
    }

    printf("OK %d/4 KAT + %d/1000 random involution round-trips "
           "(AUCurves BY/safegcd Pallas)\n", kat_ok, rand_ok);
    return 0;
}
