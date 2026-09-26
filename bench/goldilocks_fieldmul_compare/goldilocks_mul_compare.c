/* KAT + head-to-head microbench: the Goldilocks field multiply
 *   goldilocks_mul(x, y) = (x * y) mod (2^64 - 2^32 + 1),
 *   single 64-bit field element, emitted by the IN-LEAN x86 backend (no jasminc,
 *   MULX + two c-folds + a 2-word double conditional subtract — the multi-term
 *   Solinas reduce of #403, realising multiSolinasReduce multiGoldilocks) vs:
 *
 *   1. a portable C reference: the Plonky3 / winterfell GoldilocksField
 *      reduce128 (the canonical reduce used by the Plonky3 prover);
 *   2. GMP mpz, (x*y) mod p, the canonical-arithmetic oracle.
 *
 * KAT gates the bench: each trial cross-checks lean == ref == GMP (all canonical
 * mod p). The bench runs only if all KATs pass. No fabricated vectors: fixed
 * corner cases + xorshift-random, all checked against GMP.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <gmp.h>

/* in-Lean x86-backend emit (gen_com/goldilocks_mul_x86_from_lean.s) */
extern uint64_t goldilocks_mul_x86_from_lean(uint64_t x, uint64_t y);

static const uint64_t GP  = 0xFFFFFFFF00000001ULL; /* 2^64 - 2^32 + 1 */
static const uint64_t EPS = 0x00000000FFFFFFFFULL; /* 2^32 - 1        */

/* Portable reference: Plonky3 / winterfell Goldilocks reduce128. */
static inline uint64_t ref_reduce128(uint64_t lo, uint64_t hi) {
  uint32_t n_hi_hi = (uint32_t)(hi >> 32);
  uint32_t n_hi_lo = (uint32_t)hi;
  uint64_t t0;
  unsigned char b = __builtin_sub_overflow(lo, (uint64_t)n_hi_hi, &t0);
  if (b) t0 -= EPS;                       /* wrap correction */
  uint64_t t1 = (uint64_t)n_hi_lo * EPS;
  uint64_t t2;
  unsigned char c = __builtin_add_overflow(t0, t1, &t2);
  if (c) t2 += EPS;                       /* wrap correction */
  return t2;
}
static inline uint64_t ref_mul(uint64_t x, uint64_t y) {
  unsigned __int128 p = (unsigned __int128)x * (unsigned __int128)y;
  uint64_t r = ref_reduce128((uint64_t)p, (uint64_t)(p >> 64));
  /* Plonky3's reduce128 leaves a value in [0, 2^64) that is reduced but not
     necessarily canonical (< p); canonicalize for the byte-equality KAT, which
     the lean kernel already does via its two conditional subtracts. */
  if (r >= GP) r -= GP;
  return r;
}

/* GMP oracle: (x*y) mod p */
static mpz_t P;
static void init_p(void) {
  mpz_init(P);
  mpz_ui_pow_ui(P, 2, 64);
  mpz_sub(P, P, P); /* zero, rebuild below */
  mpz_ui_pow_ui(P, 2, 64);
  mpz_t e; mpz_init(e); mpz_ui_pow_ui(e, 2, 32);
  mpz_sub(P, P, e);
  mpz_add_ui(P, P, 1);
  mpz_clear(e);
}
static uint64_t gmp_mul(uint64_t x, uint64_t y) {
  mpz_t X, Y, Z; mpz_inits(X, Y, Z, NULL);
  mpz_set_ui(X, x); mpz_set_ui(Y, y);
  mpz_mul(Z, X, Y); mpz_mod(Z, Z, P);
  uint64_t r = mpz_get_ui(Z);
  mpz_clears(X, Y, Z, NULL);
  return r;
}

static uint64_t rng = 0x243F6A8885A308D3ULL;
static inline uint64_t xrand(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
  return rng * 0x2545F4914F6CDD1DULL;
}

static int kat(void) {
  uint64_t corners[] = {
    0, 1, 2, EPS, EPS + 1, (uint64_t)1 << 32, GP - 1, GP, GP + 1,
    0xFFFFFFFFFFFFFFFFULL, 0x8000000000000000ULL, 0xFFFFFFFF00000000ULL
  };
  int nc = (int)(sizeof(corners) / sizeof(corners[0]));
  int fails = 0;
  for (int i = 0; i < nc; i++)
    for (int j = 0; j < nc; j++) {
      uint64_t x = corners[i], y = corners[j];
      uint64_t L = goldilocks_mul_x86_from_lean(x, y);
      uint64_t R = ref_mul(x, y);
      uint64_t G = gmp_mul(x, y);
      if (!(L == G && R == G)) {
        fails++;
        fprintf(stderr, "KAT FAIL corner x=%016llx y=%016llx  lean=%016llx ref=%016llx gmp=%016llx\n",
                (unsigned long long)x, (unsigned long long)y,
                (unsigned long long)L, (unsigned long long)R, (unsigned long long)G);
      }
    }
  for (long t = 0; t < 200000; t++) {
    uint64_t x = xrand(), y = xrand();
    uint64_t L = goldilocks_mul_x86_from_lean(x, y);
    uint64_t R = ref_mul(x, y);
    uint64_t G = gmp_mul(x, y);
    if (!(L == G && R == G)) {
      fails++;
      if (fails < 10)
        fprintf(stderr, "KAT FAIL rand x=%016llx y=%016llx  lean=%016llx ref=%016llx gmp=%016llx\n",
                (unsigned long long)x, (unsigned long long)y,
                (unsigned long long)L, (unsigned long long)R, (unsigned long long)G);
    }
  }
  return fails;
}

static uint64_t now_ns(void) {
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

int main(int argc, char **argv) {
  long trials = (argc > 1) ? atol(argv[1]) : 2000000;
  init_p();

  int f = kat();
  if (f) { fprintf(stderr, "KAT failed (%d) — not benching.\n", f); return 1; }
  printf("KAT OK (lean == Plonky3-ref == GMP mod p)\n");
  if (trials <= 1) return 0;

  /* warm + data-dependent chains to defeat the optimizer */
  uint64_t a = 0x1234567, bx = 0x89abcdef;
  uint64_t best_lean = ~0ULL, best_ref = ~0ULL;
  for (int rep = 0; rep < 5; rep++) {
    uint64_t s = now_ns();
    uint64_t acc = a;
    for (long t = 0; t < trials; t++) acc = goldilocks_mul_x86_from_lean(acc, bx);
    uint64_t e = now_ns();
    if (acc == 0xdeadbeef) printf(" ");
    uint64_t d = e - s; if (d < best_lean) best_lean = d;
  }
  for (int rep = 0; rep < 5; rep++) {
    uint64_t s = now_ns();
    uint64_t acc = a;
    for (long t = 0; t < trials; t++) acc = ref_mul(acc, bx);
    uint64_t e = now_ns();
    if (acc == 0xdeadbeef) printf(" ");
    uint64_t d = e - s; if (d < best_ref) best_ref = d;
  }
  double cyc_lean = (double)best_lean / (double)trials * 3.5; /* ~3.5 GHz est */
  double cyc_ref  = (double)best_ref  / (double)trials * 3.5;
  printf("lean  : %.3f ns/op  (~%.2f cyc/op @3.5GHz)\n",
         (double)best_lean / trials, cyc_lean);
  printf("ref   : %.3f ns/op  (~%.2f cyc/op @3.5GHz)\n",
         (double)best_ref / trials, cyc_ref);
  printf("ratio lean/ref : %.3fx\n", (double)best_lean / (double)best_ref);
  return 0;
}
