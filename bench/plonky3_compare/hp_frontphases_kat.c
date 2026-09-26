/* KAT for the FRONT-COMPILED honest_prove FRI fold-chain phase
 * (gen_com/honest_prove_frontphases.s, emitted by
 * CatCrypt/Crypto/SecureCompilation/VIR/Plonky3HonestProveFrontEmit.lean —
 * owned render, no jasminc, no hand Com/Lcmd).
 *
 * ORACLE: the REAL jasminc whole-prover artifact plonky3_honest_prove.s is
 * linked and run on the KAT Fibonacci trace; its proof words are the ground
 * truth (out[16..17] = final degree-1 polynomial, out[18] = beta).
 *
 * The fragment
 *   hp_fri_fold_chain(buf[17], lde[96], n16, n8, n4, n2)
 * folds the column-0 LDE rows through hp_prove's fold phases
 * (32->16->8->4->2, beta riding in buf[16]).  The LDE input is recomputed
 * here by the field-only coset-NTT replica (honest_prove_reroute.c recipe —
 * no permutation involved).
 *
 * Gate: buf[0] == out[16], buf[1] == out[17] — the fragment reproduces the
 * jasminc artifact's final-poly words exactly.
 *
 * Build: make plonky3-hp-frontphases-kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern uint64_t *hp_prove(uint64_t *out, const uint64_t *p0);
extern void hp_fri_fold_chain(uint64_t *buf, const uint64_t *lde,
                              uint64_t n16, uint64_t n8, uint64_t n4, uint64_t n2);

#define BB_P 2013265921ULL
#define BB_G 31ULL

/* ---------- field-only coset-NTT LDE replica (honest_prove_reroute.c) ------ */
static inline uint64_t pr_reduce(uint64_t x) {
  uint64_t t = x - BB_P;
  return ((int64_t)t < 0) ? x : t;
}
static inline uint64_t pr_add(uint64_t a, uint64_t b) { return pr_reduce(pr_reduce(a) + pr_reduce(b)); }
static inline uint64_t pr_sub(uint64_t a, uint64_t b) { return pr_reduce((BB_P + pr_reduce(a)) - pr_reduce(b)); }
static inline uint64_t pr_mul(uint64_t a, uint64_t b) { return (pr_reduce(a) * pr_reduce(b)) % BB_P; }
static uint64_t pr_pow(uint64_t base, uint64_t exp) {
  uint64_t r = 1, c = base % BB_P;
  for (int it = 0; it < 64; it++) { if (exp & 1) r = pr_mul(r, c); c = pr_mul(c, c); exp >>= 1; }
  return r;
}
static uint64_t pr_inv(uint64_t a) { return a == 0 ? 0 : pr_pow(a, BB_P - 2); }
static uint64_t pr_bitrev(uint64_t i, int logN) {
  uint64_t r = 0;
  for (int b = 0; b < logN; b++) { r = (r << 1) | (i & 1); i >>= 1; }
  return r;
}
static void pr_ntt(uint64_t *io, int n, uint64_t omega) {
  int logN = 0; while ((1 << logN) < n) logN++;
  uint64_t a[32];
  for (int i = 0; i < n; i++) a[i] = io[pr_bitrev((uint64_t)i, logN)];
  for (int layer = 0; layer < logN; layer++) {
    int size = 1 << (layer + 1), half = size >> 1;
    uint64_t wsize = pr_pow(omega, (uint64_t)(n / size));
    for (int blk = 0; blk < n; blk += size) {
      uint64_t wpow = 1;
      for (int pos = 0; pos < half; pos++) {
        uint64_t lo = a[blk + pos], hi = a[blk + pos + half];
        uint64_t t = pr_mul(wpow, hi);
        a[blk + pos] = pr_add(lo, t);
        a[blk + pos + half] = pr_sub(lo, t);
        wpow = pr_mul(wpow, wsize);
      }
    }
  }
  memcpy(io, a, sizeof(uint64_t) * n);
}
static void pr_intt(uint64_t *io, int n, uint64_t omega) {
  pr_ntt(io, n, pr_inv(omega));
  uint64_t ni = pr_inv((uint64_t)n);
  for (int i = 0; i < n; i++) io[i] = pr_mul(io[i], ni);
}
static void trace_lde(uint64_t o[96], const uint64_t s[24]) {
  uint64_t omegaTrace = pr_pow(BB_G, (BB_P - 1) >> 3);
  uint64_t omegaN = pr_pow(BB_G, (BB_P - 1) >> 5);
  for (int col = 0; col < 3; col++) {
    uint64_t colbuf[8], lde_col[32];
    for (int row = 0; row < 8; row++) colbuf[row] = pr_reduce(s[3*row + col]);
    pr_intt(colbuf, 8, omegaTrace);
    for (int row = 0; row < 8; row++)  lde_col[row] = colbuf[row];
    for (int row = 8; row < 32; row++) lde_col[row] = 0;
    uint64_t w = 1;
    for (int row = 0; row < 32; row++) { lde_col[row] = pr_mul(lde_col[row], w); w = pr_mul(w, BB_G); }
    pr_ntt(lde_col, 32, omegaN);
    for (int row = 0; row < 32; row++) o[row*3 + col] = lde_col[row];
  }
}

int main(void) {
  /* KAT Fibonacci trace (height 8, width 3, a0=0, b0=1) */
  uint64_t trace[24];
  { uint64_t a = 0, b = 1;
    for (int row = 0; row < 8; row++) {
      trace[3*row + 0] = a; trace[3*row + 1] = b;
      uint64_t c = a + b; trace[3*row + 2] = c; a = b; b = c;
    } }

  /* oracle: the jasminc whole-prover artifact */
  uint64_t out_ref[980];
  memset(out_ref, 0, sizeof out_ref);
  hp_prove(out_ref, trace);

  /* fragment input: field-only LDE replica + the oracle's beta in buf[16] */
  uint64_t lde[96];
  trace_lde(lde, trace);
  uint64_t buf[17];
  memset(buf, 0, sizeof buf);
  buf[16] = out_ref[18];
  hp_fri_fold_chain(buf, lde, 16, 8, 4, 2);

  int fails = 0;
  if (buf[0] != out_ref[16]) {
    printf("FAIL finalpoly[0]: got %llu want %llu\n",
           (unsigned long long)buf[0], (unsigned long long)out_ref[16]);
    fails++;
  }
  if (buf[1] != out_ref[17]) {
    printf("FAIL finalpoly[1]: got %llu want %llu\n",
           (unsigned long long)buf[1], (unsigned long long)out_ref[17]);
    fails++;
  }
  if (fails == 0) {
    printf("hp_frontphases KAT: PASS (fold chain == jasminc artifact final poly)\n");
    printf("  finalpoly = %llu, %llu  beta = %llu  nonce = %llu\n",
           (unsigned long long)buf[0], (unsigned long long)buf[1],
           (unsigned long long)out_ref[18], (unsigned long long)out_ref[19]);
    return 0;
  }
  printf("hp_frontphases KAT: FAIL (%d mismatches)\n", fails);
  return 1;
}
