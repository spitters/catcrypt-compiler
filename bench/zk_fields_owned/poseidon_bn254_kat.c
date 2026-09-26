/* Known-answer test of the owned circomlib Poseidon permutation (width 3, BN254
 * scalar field r) against circomlib / Poseidon-reference vectors.
 *
 * ABI: void poseidon_bn254_t3(uint64_t *out, const uint64_t *in);
 *   in[4k .. 4k+3]  = lane k (k = 0, 1, 2) as the Montgomery form x * 2^256 mod r,
 *                     four little-endian 64-bit limbs;
 *   out[4k .. 4k+3] = the permuted lane k in the same form.
 *
 * The harness converts to and from Montgomery form with its own shift-and-reduce
 * arithmetic (256 modular doublings in, 256 modular halvings out), independent of
 * the kernel's Montgomery reduction.
 *
 * Vectors:
 *   perm(0, 1, 2)  all three lanes: the Poseidon reference test vector
 *                  poseidonperm_x5_254_3; lane 0 is circomlibjs poseidon([1, 2]).
 *   perm(0, 3, 4)  lane 0: circomlibjs poseidon([3, 4]).
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void poseidon_bn254_t3(uint64_t *out, const uint64_t *in);

typedef unsigned __int128 u128;
typedef struct { uint64_t l[4]; } fe;

/* r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001 */
static const fe R = {{0x43e1f593f0000001ULL, 0x2833e84879b97091ULL, 0xb85045b68181585dULL,
                      0x30644e72e131a029ULL}};

static int ge(const fe *a, const fe *b) {
  for (int i = 3; i >= 0; i--) {
    if (a->l[i] != b->l[i]) return a->l[i] > b->l[i];
  }
  return 1;
}
static void add(fe *a, const fe *b) {
  u128 c = 0;
  for (int i = 0; i < 4; i++) {
    c += (u128)a->l[i] + b->l[i];
    a->l[i] = (uint64_t)c;
    c >>= 64;
  }
}
static void sub(fe *a, const fe *b) {
  uint64_t borrow = 0;
  for (int i = 0; i < 4; i++) {
    u128 d = (u128)a->l[i] - b->l[i] - borrow;
    a->l[i] = (uint64_t)d;
    borrow = (uint64_t)(d >> 127);
  }
}
/* x * 2^256 mod r, for x < r. Values stay below 2r < 2^255. */
static fe to_mont(fe x) {
  for (int k = 0; k < 256; k++) {
    add(&x, &x);
    if (ge(&x, &R)) sub(&x, &R);
  }
  return x;
}
/* y * 2^-256 mod r, for y < r. y + r < 2^255, so the sum fits four limbs. */
static fe from_mont(fe y) {
  for (int k = 0; k < 256; k++) {
    if (y.l[0] & 1) add(&y, &R);
    for (int i = 0; i < 4; i++) y.l[i] = (y.l[i] >> 1) | (i < 3 ? y.l[i + 1] << 63 : 0);
  }
  return y;
}
static fe from_u64(uint64_t v) {
  fe x = {{v, 0, 0, 0}};
  return x;
}
static fe from_hex(const char *s) {
  fe x = {{0, 0, 0, 0}};
  size_t n = strlen(s);
  for (size_t i = 0; i < n; i++) {
    char c = s[i];
    uint64_t d = (c >= '0' && c <= '9') ? (uint64_t)(c - '0')
               : (c >= 'a' && c <= 'f') ? (uint64_t)(c - 'a' + 10)
                                        : (uint64_t)(c - 'A' + 10);
    for (int j = 3; j > 0; j--) x.l[j] = (x.l[j] << 4) | (x.l[j - 1] >> 60);
    x.l[0] = (x.l[0] << 4) | d;
  }
  return x;
}
static void print_fe(const char *tag, const fe *x) {
  fprintf(stderr, "%s0x%016llx%016llx%016llx%016llx\n", tag, (unsigned long long)x->l[3],
          (unsigned long long)x->l[2], (unsigned long long)x->l[1], (unsigned long long)x->l[0]);
}

static int failures = 0;

/* Run the kernel on lanes (a, b, c); compare the lanes whose expected hex is non-NULL. */
static void run(const char *name, fe a, fe b, fe c, const char *e0, const char *e1,
                const char *e2) {
  fe lanes[3] = {a, b, c};
  uint64_t in[12], out[12];
  for (int k = 0; k < 3; k++) {
    fe m = to_mont(lanes[k]);
    memcpy(&in[4 * k], m.l, sizeof m.l);
  }
  poseidon_bn254_t3(out, in);
  const char *exp[3] = {e0, e1, e2};
  for (int k = 0; k < 3; k++) {
    fe m;
    memcpy(m.l, &out[4 * k], sizeof m.l);
    if (ge(&m, &R)) {
      fprintf(stderr, "FAIL %s lane %d: output limbs not below r\n", name, k);
      print_fe("  got (Montgomery) ", &m);
      failures++;
      continue;
    }
    if (!exp[k]) continue;
    fe got = from_mont(m), want = from_hex(exp[k]);
    if (memcmp(got.l, want.l, sizeof got.l) != 0) {
      fprintf(stderr, "FAIL %s lane %d\n", name, k);
      print_fe("  got  ", &got);
      print_fe("  want ", &want);
      failures++;
    }
  }
}

int main(void) {
  /* The conversion helpers are inverse to each other on a few values. */
  static const char *probe[] = {"0", "1", "2",
      "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000"};
  for (int i = 0; i < 4; i++) {
    fe x = from_hex(probe[i]), y = from_mont(to_mont(x));
    if (memcmp(x.l, y.l, sizeof x.l) != 0) {
      fprintf(stderr, "harness: Montgomery conversion round trip failed on %s\n", probe[i]);
      return 2;
    }
  }
  run("perm(0,1,2)", from_u64(0), from_u64(1), from_u64(2),
      "115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a",
      "0fca49b798923ab0239de1c9e7a4a9a2210312b6a2f616d18b5a87f9b628ae29",
      "0e7ae82e40091e63cbd4f16a6d16310b3729d4b6e138fcf54110e2867045a30c");
  run("perm(0,3,4)", from_u64(0), from_u64(3), from_u64(4),
      "20a3af0435914ccd84b806164531b0cd36e37d4efb93efab76913a93e1f30996", NULL, NULL);
  if (failures) {
    fprintf(stderr, "poseidon_bn254_t3: %d lane checks FAILED\n", failures);
    return 1;
  }
  printf("poseidon_bn254_t3: poseidon([1,2]), poseidon([3,4]) and perm(0,1,2) passed\n");
  return 0;
}
