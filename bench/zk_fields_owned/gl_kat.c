/* Known-answer test of the owned Goldilocks kernels gl_add, gl_sub, gl_mul, gl_neg
 * against unsigned __int128 arithmetic modulo p = 2^64 - 2^32 + 1.
 *
 * ABI: void f(uint64_t *out, const uint64_t *in); in[0] = x, in[1] = y, both
 * canonical (< p); out[0] = the canonical result. gl_neg reads in[0] only.
 */
#include <stdint.h>
#include <stdio.h>

extern void gl_add(uint64_t *out, const uint64_t *in);
extern void gl_sub(uint64_t *out, const uint64_t *in);
extern void gl_mul(uint64_t *out, const uint64_t *in);
extern void gl_neg(uint64_t *out, const uint64_t *in);

typedef unsigned __int128 u128;
static const uint64_t P = 0xFFFFFFFF00000001ULL;

static uint64_t ref_add(uint64_t x, uint64_t y) { return (uint64_t)(((u128)x + y) % P); }
static uint64_t ref_sub(uint64_t x, uint64_t y) { return (uint64_t)(((u128)x + P - y) % P); }
static uint64_t ref_mul(uint64_t x, uint64_t y) { return (uint64_t)(((u128)x * y) % P); }
static uint64_t ref_neg(uint64_t x) { return (uint64_t)(((u128)P - x) % P); }

static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;
static uint64_t rng(void) {
  uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}
/* A canonical element: rejection sampling on 64-bit words. */
static uint64_t rng_elt(void) {
  for (;;) {
    uint64_t v = rng();
    if (v < P) return v;
  }
}

static long failures = 0, checks = 0;

static void check(const char *op, uint64_t x, uint64_t y, uint64_t got, uint64_t want) {
  checks++;
  if (got != want) {
    if (failures < 20)
      fprintf(stderr, "FAIL %s(0x%016llx, 0x%016llx): got 0x%016llx want 0x%016llx\n", op,
              (unsigned long long)x, (unsigned long long)y, (unsigned long long)got,
              (unsigned long long)want);
    failures++;
  }
}

static void check_pair(uint64_t x, uint64_t y) {
  uint64_t in[2] = {x, y}, out[1];
  gl_add(out, in); check("add", x, y, out[0], ref_add(x, y));
  gl_sub(out, in); check("sub", x, y, out[0], ref_sub(x, y));
  gl_mul(out, in); check("mul", x, y, out[0], ref_mul(x, y));
  gl_neg(out, in); check("neg", x, 0, out[0], ref_neg(x));
}

int main(void) {
  static const uint64_t edge[] = {
      0, 1, 2, 3,
      0x00000000FFFFFFFFULL, 0x0000000100000000ULL, 0x0000000100000001ULL,
      0x00000000FFFFFFFEULL, 0x7FFFFFFFFFFFFFFFULL, 0x8000000000000000ULL,
      0x8000000000000001ULL, 0xFFFFFFFE00000000ULL, 0xFFFFFFFEFFFFFFFFULL,
      0xFFFFFFFF00000000ULL, /* p - 1 */
      0xFFFFFFFEFFFFFFFFULL, /* p - 2 */
      0x00000001FFFFFFFFULL, 0x8000000080000000ULL, 0x7FFFFFFF80000001ULL,
  };
  const int ne = (int)(sizeof edge / sizeof edge[0]);
  for (int i = 0; i < ne; i++)
    for (int j = 0; j < ne; j++) check_pair(edge[i], edge[j]);
  for (int i = 0; i < ne; i++)
    for (int k = 0; k < 64; k++) {
      uint64_t r = rng_elt();
      check_pair(edge[i], r);
      check_pair(r, edge[i]);
    }
  for (long k = 0; k < 1000000; k++) check_pair(rng_elt(), rng_elt());
  if (failures) {
    fprintf(stderr, "gl_kat: %ld of %ld checks FAILED\n", failures, checks);
    return 1;
  }
  printf("gl_kat: all %ld checks passed (add, sub, mul, neg)\n", checks);
  return 0;
}
