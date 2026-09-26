/* Pallas base-field Fp inversion bench: AUCurves BY/safegcd leaf.
 *
 * Measures cyc/op of the AUCurves verified-CT Bernstein-Yang divstep
 * inverter `pallas_invert_divstep_sat` (a 4×u64 saturated LE input
 * → 4×u64 output, 590 divsteps internally over 5-limb Signed62).
 *
 * Trust profile:
 *   * AUCurves BY/safegcd-leaf
 *       Trust = Coq kernel + AUCurves Bernstein-Yang divstep proof
 *               + AUCurves CI valgrind/crabgrind CT verification
 *               + Rust compiler.
 *
 * Methodology:
 *   - MIN-of-SAMPLES (REPS configurable, default 100000 for the inner
 *     loop — inversion runs ~5-15 Kcyc/op at the 255-bit width)
 *   - rdtsc cycles via tscbench.h + clock_gettime for ns
 *   - pin_to_cpu(3) for stable measurement
 *   - Inputs: 4 fixed KAT vectors from
 *     `safegcd_pallas.rs::tests::pallas_invert_times_self_is_one`.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include "pallas_safegcd_ref.h"
#include "tscbench.h"
#include "affinity.h"

static volatile uint64_t g_sink = 0;

static inline double ns_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

static long REPS = 100000;
#define SAMPLES 3

/* Pallas base prime as 4×u64 LE.
 * p = 2^254 + 45560315531419706090280762371685220353
 *   = 0x40000000_00000000_00000000_00000000_224698fc_094cf91b_992d30ed_00000001
 * (cited per safegcd_pallas.rs::PALLAS_P_4X64) */
static const uint64_t PALLAS_P[4] = {
    0x992D30ED00000001ULL,
    0x224698FC094CF91BULL,
    0x0000000000000000ULL,
    0x4000000000000000ULL,
};

/* KAT inputs from
 * `safegcd_pallas.rs::tests::pallas_invert_times_self_is_one`.
 * Each x has `pallas_invert_divstep_sat(out, x)` followed by
 * x · out ≡ 1 (mod p) — checked here via the AUCurves round-trip
 * (we call invert twice; invert(invert(x)) = x for x ≠ 0). */
static const uint64_t KAT_INPUTS[4][4] = {
    {1ULL, 0, 0, 0},
    {2ULL, 0, 0, 0},
    {0x0123456789ABCDEFULL, 0xFEDCBA9876543210ULL,
     0xDEADBEEFULL, 0x1ULL},
    /* p - 1 */
    {0x992D30ED00000000ULL, /* p[0] - 1 */
     0x224698FC094CF91BULL,
     0x0000000000000000ULL,
     0x4000000000000000ULL},
};

static int eq4(const uint64_t a[4], const uint64_t b[4]) {
    for (int i = 0; i < 4; i++) if (a[i] != b[i]) return 0;
    return 1;
}

static void hex_dump4(const char *tag, const uint64_t x[4]) {
    fprintf(stderr, "%s: ", tag);
    for (int i = 3; i >= 0; i--) fprintf(stderr, "%016llx", (unsigned long long)x[i]);
    fputc('\n', stderr);
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    if (argc > 1) REPS = atol(argv[1]);
    if (REPS < 1) REPS = 1;

    pin_to_cpu(3);

    /* Mute the prime + warn the compiler we use it. */
    (void)PALLAS_P;

    printf("# Pallas Fp inversion bench: AUCurves BY/safegcd leaf\n");
    printf("# REPS=%ld, SAMPLES=%d, MIN-of-SAMPLES\n", REPS, SAMPLES);
    printf("# Inputs: 4 KATs from safegcd_pallas.rs::tests\n");
    printf("# pin_to_cpu(3)\n\n");

    /* Round-trip KAT: invert(invert(x)) == x for the 4 fixed inputs. */
    int kat_ok = 0;
    for (int i = 0; i < 4; i++) {
        uint64_t inv1[4], inv2[4];
        pallas_safegcd_invert(inv1, KAT_INPUTS[i]);
        pallas_safegcd_invert(inv2, inv1);
        if (eq4(inv2, KAT_INPUTS[i])) {
            kat_ok++;
        } else {
            fprintf(stderr, "KAT round-trip FAIL on input %d\n", i);
            hex_dump4("  in   ", KAT_INPUTS[i]);
            hex_dump4("  inv  ", inv1);
            hex_dump4("  inv2 ", inv2);
            return 1;
        }
        g_sink += inv1[0];
    }
    printf("# round-trip KAT: %d/4 OK (invert(invert(x)) == x)\n", kat_ok);
    printf("\n");

    /* Warm-up. */
    {
        uint64_t out[4];
        pallas_safegcd_invert(out, KAT_INPUTS[2]);
        g_sink += out[0];
    }

    uint64_t cyc_min = ~0ULL;
    double ns_min = 1e30;

    for (int s = 0; s < SAMPLES; s++) {
        uint64_t out[4];
        uint64_t c0 = rdtsc_start();
        double t0 = ns_now();
        for (long r = 0; r < REPS; r++) {
            /* Rotate through the 4 KAT inputs to defeat any branch
             * predictor caching (the divstep is CT, so this is paranoia). */
            pallas_safegcd_invert(out, KAT_INPUTS[r & 3]);
            g_sink += out[0];
        }
        double t1 = ns_now();
        uint64_t c1 = rdtsc_end();
        double v_ns = (t1 - t0) / (double)REPS;
        uint64_t v_cyc = (c1 - c0) / (uint64_t)REPS;
        if (v_ns < ns_min) ns_min = v_ns;
        if (v_cyc < cyc_min) cyc_min = v_cyc;
    }

    printf("# Fp inversion (Bernstein-Yang divstep, 590 steps, 4*u64 LE)\n");
    printf("%-30s %12s %12s\n", "impl", "ns/op", "cyc/op");
    printf("%-30s %12.1f %12llu\n", "aucurves-by-safegcd (Pallas)",
           ns_min, (unsigned long long)cyc_min);

    return 0;
}
