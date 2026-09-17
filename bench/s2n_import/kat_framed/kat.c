/* Known-answer test: bignum_montmul_p384_framed against s2n-bignum's
   bignum_montmul_p384 on random inputs below p384, disjoint and in-place,
   and callee-saved register preservation through check_saved. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void bignum_montmul_p384(uint64_t *z, const uint64_t *x, const uint64_t *y);
extern void bignum_montmul_p384_framed(uint64_t *z, const uint64_t *x, const uint64_t *y);
extern int check_saved(uint64_t *z, const uint64_t *x, const uint64_t *y);

static const uint64_t P[6] = {0x00000000ffffffffULL, 0xffffffff00000000ULL,
                              0xfffffffffffffffeULL, 0xffffffffffffffffULL,
                              0xffffffffffffffffULL, 0xffffffffffffffffULL};

static uint64_t st = 0x9e3779b97f4a7c15ULL;
static uint64_t rnd(void) {
  st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st;
}
static int lt_p(const uint64_t *a) {
  for (int i = 5; i >= 0; i--) {
    if (a[i] < P[i]) return 1;
    if (a[i] > P[i]) return 0;
  }
  return 0;
}
static void rand_below_p(uint64_t *a) {
  do { for (int i = 0; i < 6; i++) a[i] = rnd(); } while (!lt_p(a));
}

int main(void) {
  long bad = 0, n = 200000;
  uint64_t x[6], y[6], z1[6], z2[6], t[6];
  /* edge values */
  uint64_t edges[4][6];
  memset(edges, 0, sizeof edges);
  edges[1][0] = 1;
  memcpy(edges[2], P, sizeof P); edges[2][0] -= 1;          /* p - 1 */
  for (int i = 0; i < 6; i++) edges[3][i] = P[i] >> 1;     /* ~p/2 */
  for (int a = 0; a < 4; a++)
    for (int b = 0; b < 4; b++) {
      bignum_montmul_p384(z1, edges[a], edges[b]);
      bignum_montmul_p384_framed(z2, edges[a], edges[b]);
      if (memcmp(z1, z2, sizeof z1)) bad++;
    }
  for (long k = 0; k < n; k++) {
    rand_below_p(x); rand_below_p(y);
    bignum_montmul_p384(z1, x, y);
    bignum_montmul_p384_framed(z2, x, y);
    if (memcmp(z1, z2, sizeof z1)) bad++;
    /* in place: z = x, and x = y */
    memcpy(t, x, sizeof t);
    bignum_montmul_p384_framed(t, t, y);
    if (memcmp(t, z1, sizeof t)) bad++;
    bignum_montmul_p384(z1, x, x);
    memcpy(t, x, sizeof t);
    bignum_montmul_p384_framed(t, t, t);
    if (memcmp(t, z1, sizeof t)) bad++;
  }
  int saved = check_saved(z2, x, y);
  printf("vectors: %ld random x3 + 16 edge, mismatches: %ld, callee-saved mask: %d\n",
         n, bad, saved);
  return (bad != 0 || saved != 0);
}
