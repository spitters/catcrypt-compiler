/* compare.c -- conformance and timing of the compiler's SHA-512, BLAKE2b and
 * Keccak-f[1600] objects against OpenSSL, HACL* and XKCP.
 *
 *   compare conform [NRAND]   official vectors, then NRAND random inputs per
 *                             kernel compared word for word with every peer;
 *                             exit 1 on any mismatch.
 *   compare bench [--cpu C] [--samples S] [--inner I] [--run R] [--label L]
 *                             TSV: kernel, arm, median and minimum TSC cycles
 *                             per call over S samples of I chained calls; for the
 *                             4-lane rows (kernel *_x4), cycles per call / 4.
 *
 * Chaining: every arm's call depends on the previous call's output, so no arm
 * overlaps independent calls.  The peers update their state in place; ours
 * alternates two input arrays, writing each call's output words into the
 * chaining words (or lanes) of the other array.  The SHA-512 and BLAKE2b arms all
 * take the 128-byte block: ours through the block wrappers of tramp.c, which load
 * the message words on every call.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "affinity.h"
#include "arms.h"
#include "tscbench.h"

/* ---- inputs ---------------------------------------------------------------- */

static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd64(void) {
  uint64_t x = rng_state;
  x ^= x >> 12;
  x ^= x << 25;
  x ^= x >> 27;
  rng_state = x;
  return x * 0x2545F4914F6CDD1DULL;
}
static void rnd_bytes(uint8_t *p, int n) {
  for (int i = 0; i < n; i++) p[i] = (uint8_t)rnd64();
}

static uint64_t load_le64(const uint8_t *p) {
  uint64_t w = 0;
  for (int i = 7; i >= 0; i--) w = (w << 8) | p[i];
  return w;
}
static void store_be64(uint8_t *p, uint64_t w) {
  for (int i = 7; i >= 0; i--) { p[i] = (uint8_t)w; w >>= 8; }
}
static void store_le64(uint8_t *p, uint64_t w) {
  for (int i = 0; i < 8; i++) { p[i] = (uint8_t)w; w >>= 8; }
}

static const uint64_t SHA512_IV[8] = {
  0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL, 0x3c6ef372fe94f82bULL,
  0xa54ff53a5f1d36f1ULL, 0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL,
  0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL};

/* ---- the three kernels as functions of (state, block) ------------------------ */

/* Ours through the block wrappers that the timing calls. */
static void ours_sha512(uint64_t h[8], const uint8_t blk[128]) {
  uint64_t src[24], dst[8];
  memcpy(src, h, 8 * sizeof(uint64_t));
  ours_sha512_block(dst, src, blk);
  memcpy(h, dst, sizeof dst);
}

static void ours_blake2b(uint64_t h[8], const uint8_t blk[128], uint64_t t0, uint64_t t1,
                         int last) {
  uint64_t src[24], dst[8];
  memcpy(src, h, 8 * sizeof(uint64_t));
  ours_blake2b_block(dst, src, blk, t0, t1, last ? ~0ULL : 0ULL);
  memcpy(h, dst, sizeof dst);
}

static void hacl_blake2b(uint64_t h[8], const uint8_t blk[128], uint64_t t0, uint64_t t1,
                         int last) {
  uint64_t hash16[16], wv[16];
  peer_hacl_blake2b_init_rows(hash16, h);
  peer_hacl_blake2b(hash16, wv, blk, t0, t1, last);
  memcpy(h, hash16, 8 * sizeof(uint64_t));
}

static void hacl_blake2b_simd256(uint64_t h[8], const uint8_t blk[128], uint64_t t0,
                                 uint64_t t1, int last) {
  _Alignas(32) uint64_t hash16[16];
  _Alignas(32) uint64_t wv[16];
  peer_hacl_blake2b_init_rows(hash16, h);
  peer_hacl_blake2b_simd256(hash16, wv, blk, t0, t1, last);
  memcpy(h, hash16, 8 * sizeof(uint64_t));
}

/* 4-lane states: word i of lane j at st[4i + j]. */
static void x4_set(uint64_t *st, int words, int j, const uint64_t *w) {
  for (int i = 0; i < words; i++) st[4 * i + j] = w[i];
}
static void x4_get(const uint64_t *st, int words, int j, uint64_t *w) {
  for (int i = 0; i < words; i++) w[i] = st[4 * i + j];
}

static void ours_keccak(uint64_t s[25]) {
  uint64_t out[25];
  ours_keccak_f1600(out, s);
  memcpy(s, out, sizeof out);
}

/* ---- conformance --------------------------------------------------------- */

static int failures = 0;

static void check_words(const char *what, const uint64_t *a, const uint64_t *b, int n) {
  for (int i = 0; i < n; i++)
    if (a[i] != b[i]) {
      printf("MISMATCH %s word %d: %016llx != %016llx\n", what, i, (unsigned long long)a[i],
             (unsigned long long)b[i]);
      failures++;
      return;
    }
}

static void check_bytes(const char *what, const uint8_t *a, const uint8_t *b, int n) {
  if (memcmp(a, b, (size_t)n) != 0) {
    printf("MISMATCH %s\n", what);
    failures++;
  } else {
    printf("ok       %s\n", what);
  }
}

static void hex_to_bytes(const char *hex, uint8_t *out, int n) {
  for (int i = 0; i < n; i++) {
    unsigned v;
    sscanf(hex + 2 * i, "%2x", &v);
    out[i] = (uint8_t)v;
  }
}

/* The 4-lane arms on one input: the input in all four lanes, the lanes checked
 * equal, lane 0 returned. */
static void hacl_sha512_x4_all(uint64_t h[8], const uint8_t blk[128]) {
  _Alignas(32) uint64_t st[32];
  uint64_t w[8];
  for (int j = 0; j < 4; j++) x4_set(st, 8, j, h);
  peer_hacl_sha512_x4(st, blk, blk, blk, blk);
  x4_get(st, 8, 0, h);
  for (int j = 1; j < 4; j++) {
    x4_get(st, 8, j, w);
    check_words("sha512 hacl_vec256_x4 lane j vs lane 0", w, h, 8);
  }
}

static void hacl_keccak_x4_all(uint64_t s[25]) {
  _Alignas(32) uint64_t st[100];
  uint64_t w[25];
  for (int j = 0; j < 4; j++) x4_set(st, 25, j, s);
  peer_hacl_keccak_x4_absorb0(st);
  x4_get(st, 25, 0, s);
  for (int j = 1; j < 4; j++) {
    x4_get(st, 25, j, w);
    check_words("keccak hacl_simd256_x4 state j vs state 0", w, s, 25);
  }
}

typedef void (*sha512_fn)(uint64_t h[8], const uint8_t blk[128]);
typedef void (*blake2b_fn)(uint64_t h[8], const uint8_t blk[128], uint64_t t0, uint64_t t1,
                           int last);
typedef void (*keccak_fn)(uint64_t s[25]);

static const struct { const char *arm; sha512_fn f; } SHA512_ARMS[] = {
    {"ours", ours_sha512},
    {"openssl", peer_openssl_sha512},
    {"hacl", peer_hacl_sha512},
    {"hacl_vec256_x4", hacl_sha512_x4_all}};
static const struct { const char *arm; blake2b_fn f; } BLAKE2B_ARMS[] = {
    {"ours", ours_blake2b},
    {"hacl", hacl_blake2b},
    {"hacl_simd256", hacl_blake2b_simd256}};
static const struct { const char *arm; keccak_fn f; } KECCAK_ARMS[] = {
    {"ours", ours_keccak},
    {"xkcp", peer_xkcp_keccak_f1600},
    {"xkcp_avx2", peer_xkcp_avx2_keccak_f1600},
    {"xkcp_avx512", peer_xkcp_avx512_keccak_f1600},
    {"hacl", peer_hacl_keccak_f1600},
    {"hacl_simd256_x4", hacl_keccak_x4_all}};
#define NARMS(a) ((int)(sizeof(a) / sizeof((a)[0])))

/* FIPS 180-4 / FIPS 202 / RFC 7693 vectors for the message "abc". */
static const char *SHA512_ABC =
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f";
static const char *BLAKE2B512_ABC =
    "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
    "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923";
static const char *SHA3_256_ABC =
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532";

/* Every arm, ours and each peer, computes each vector on its own. */
static void vectors(void) {
  const uint8_t abc[3] = {'a', 'b', 'c'};
  uint8_t want[64], evp[64];
  unsigned evplen = 0;
  char what[160];

  /* SHA-512("abc"): one compression from the IV over the padded block. */
  {
    uint8_t blk[128] = {0}, got[64];
    memcpy(blk, abc, 3);
    blk[3] = 0x80;
    blk[127] = 24;
    hex_to_bytes(SHA512_ABC, want, 64);
    if (evp_digest("SHA512", abc, 3, evp, &evplen)) check_bytes("vector literal SHA-512(abc) = OpenSSL EVP", want, evp, 64);
    for (int a = 0; a < NARMS(SHA512_ARMS); a++) {
      uint64_t h[8];
      memcpy(h, SHA512_IV, sizeof h);
      SHA512_ARMS[a].f(h, blk);
      for (int i = 0; i < 8; i++) store_be64(got + 8 * i, h[i]);
      snprintf(what, sizeof what, "%s sha512_compress: SHA-512(abc) (FIPS 180-4)", SHA512_ARMS[a].arm);
      check_bytes(what, got, want, 64);
    }
  }

  /* BLAKE2b-512("abc"): h = IV ^ P (digest 64, no key), t = 3, final flag. */
  {
    uint8_t blk[128] = {0}, got[64];
    memcpy(blk, abc, 3);
    hex_to_bytes(BLAKE2B512_ABC, want, 64);
    if (evp_digest("BLAKE2B-512", abc, 3, evp, &evplen)) check_bytes("vector literal BLAKE2b-512(abc) = OpenSSL EVP", want, evp, 64);
    for (int a = 0; a < NARMS(BLAKE2B_ARMS); a++) {
      uint64_t h[8];
      memcpy(h, SHA512_IV, sizeof h);
      h[0] ^= 0x01010040ULL;
      BLAKE2B_ARMS[a].f(h, blk, 3, 0, 1);
      for (int i = 0; i < 8; i++) store_le64(got + 8 * i, h[i]);
      snprintf(what, sizeof what, "%s blake2b_compress: BLAKE2b-512(abc) (RFC 7693 App. A)", BLAKE2B_ARMS[a].arm);
      check_bytes(what, got, want, 64);
    }
  }

  /* SHA3-256("abc"): one permutation of the absorbed padded block (rate 136). */
  {
    uint8_t blk[200] = {0}, got[32];
    memcpy(blk, abc, 3);
    blk[3] ^= 0x06;
    blk[135] ^= 0x80;
    hex_to_bytes(SHA3_256_ABC, want, 32);
    if (evp_digest("SHA3-256", abc, 3, evp, &evplen)) check_bytes("vector literal SHA3-256(abc) = OpenSSL EVP", want, evp, 32);
    for (int a = 0; a < NARMS(KECCAK_ARMS); a++) {
      uint64_t s[25];
      for (int i = 0; i < 25; i++) s[i] = load_le64(blk + 8 * i);
      KECCAK_ARMS[a].f(s);
      for (int i = 0; i < 4; i++) store_le64(got + 8 * i, s[i]);
      snprintf(what, sizeof what, "%s keccak_f1600: SHA3-256(abc) (FIPS 202)", KECCAK_ARMS[a].arm);
      check_bytes(what, got, want, 32);
    }
  }

  /* Keccak-f[1600] of the zero state: lane 0 (Keccak team intermediate values). */
  for (int a = 0; a < NARMS(KECCAK_ARMS); a++) {
    uint64_t s[25] = {0};
    KECCAK_ARMS[a].f(s);
    uint64_t want0 = 0xF1258F7940E1DDE7ULL;
    snprintf(what, sizeof what, "%s keccak_f1600: lane 0 of keccak_f(0)", KECCAK_ARMS[a].arm);
    check_words(what, s, &want0, 1);
    if (s[0] == want0) printf("ok       %s\n", what);
  }
}

static void random_batch(long nrand) {
  long n0 = failures;
  for (long r = 0; r < nrand; r++) {
    uint8_t blk[128];
    uint64_t h0[8];
    rnd_bytes(blk, 128);
    for (int i = 0; i < 8; i++) h0[i] = rnd64();

    uint64_t a[8], b[8], c[8];
    memcpy(a, h0, sizeof a); memcpy(b, h0, sizeof b); memcpy(c, h0, sizeof c);
    ours_sha512(a, blk);
    peer_openssl_sha512(b, blk);
    peer_hacl_sha512(c, blk);
    check_words("sha512 ours vs OpenSSL", a, b, 8);
    check_words("sha512 ours vs HACL*", a, c, 8);

    uint64_t t0 = rnd64(), t1 = rnd64();
    int last = (int)(rnd64() & 1);
    memcpy(a, h0, sizeof a); memcpy(b, h0, sizeof b); memcpy(c, h0, sizeof c);
    ours_blake2b(a, blk, t0, t1, last);
    hacl_blake2b(b, blk, t0, t1, last);
    hacl_blake2b_simd256(c, blk, t0, t1, last);
    check_words("blake2b ours vs HACL*", a, b, 8);
    check_words("blake2b ours vs HACL* Simd256", a, c, 8);

    uint64_t s[25], x[25], y[25], v2[25], v5[25];
    for (int i = 0; i < 25; i++) s[i] = x[i] = y[i] = v2[i] = v5[i] = rnd64();
    ours_keccak(s);
    peer_xkcp_keccak_f1600(x);
    peer_hacl_keccak_f1600(y);
    peer_xkcp_avx2_keccak_f1600(v2);
    peer_xkcp_avx512_keccak_f1600(v5);
    check_words("keccak_f1600 ours vs XKCP", s, x, 25);
    check_words("keccak_f1600 ours vs HACL*", s, y, 25);
    check_words("keccak_f1600 ours vs XKCP AVX2", s, v2, 25);
    check_words("keccak_f1600 ours vs XKCP AVX-512", s, v5, 25);

    /* 4-lane arms: four independent random inputs, each lane against ours. */
    {
      uint8_t blks[4][128];
      uint64_t hs[4][8], ks[4][25], w[25];
      _Alignas(32) uint64_t st[32];
      _Alignas(32) uint64_t ks4[100];
      for (int j = 0; j < 4; j++) {
        rnd_bytes(blks[j], 128);
        for (int i = 0; i < 8; i++) hs[j][i] = rnd64();
        for (int i = 0; i < 25; i++) ks[j][i] = rnd64();
        x4_set(st, 8, j, hs[j]);
        x4_set(ks4, 25, j, ks[j]);
      }
      peer_hacl_sha512_x4(st, blks[0], blks[1], blks[2], blks[3]);
      peer_hacl_keccak_x4_absorb0(ks4);
      for (int j = 0; j < 4; j++) {
        ours_sha512(hs[j], blks[j]);
        x4_get(st, 8, j, w);
        check_words("sha512 ours vs HACL* Vec256 x4 (one lane)", hs[j], w, 8);
        ours_keccak(ks[j]);
        x4_get(ks4, 25, j, w);
        check_words("keccak_f1600 ours vs HACL* Simd256 x4 (one state)", ks[j], w, 25);
      }
    }
    if (failures - n0 > 10) break;
  }
  if (failures == n0)
    printf("ok       random batch: %ld inputs per kernel, ours = every peer\n", nrand);
}

/* ---- timing -------------------------------------------------------------- */

typedef struct {
  long samples, inner;
} Cfg;

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

/* PER is the number of independent states one call processes (1, or 4 for the
 * 4-lane rows); the figure is cycles per call / PER. */
#define TIME_ARM_N(kernel, arm, PER, BODY)                                        \
  do {                                                                            \
    uint64_t *d_ = malloc(sizeof(uint64_t) * (size_t)cfg.samples);                \
    double div_ = 2.0 * (double)cfg.inner * (double)(PER);                        \
    for (long w_ = 0; w_ < cfg.inner; w_++) { BODY; }                             \
    for (long s_ = 0; s_ < cfg.samples; s_++) {                                   \
      uint64_t t0_ = rdtsc_start();                                               \
      for (long i_ = 0; i_ < cfg.inner; i_++) { BODY; }                           \
      uint64_t t1_ = rdtsc_end();                                                 \
      d_[s_] = t1_ - t0_;                                                         \
    }                                                                             \
    qsort(d_, (size_t)cfg.samples, sizeof *d_, cmp_u64);                          \
    printf("%s\t%s\t%.1f\t%.1f\t%s\t%d\n", kernel, arm,                           \
           (double)d_[cfg.samples / 2] / div_, (double)d_[0] / div_, label, run); \
    free(d_);                                                                     \
  } while (0)
#define TIME_ARM(kernel, arm, BODY) TIME_ARM_N(kernel, arm, 1, BODY)

static void bench(Cfg cfg, const char *label, int run) {
  uint8_t blk[128];
  rnd_bytes(blk, 128);
  printf("# kernel\tarm\tmedian_cyc\tmin_cyc\tlabel\trun\n");

  /* SHA-512: every arm takes the 128-byte block; ours loads the message words
   * big-endian inside ours_sha512_block, on every call. */
  {
    uint64_t A[24], B[24];
    memcpy(A, SHA512_IV, 64); memcpy(B, SHA512_IV, 64);
    TIME_ARM("sha512_compress", "ours", { ours_sha512_block(B, A, blk); ours_sha512_block(A, B, blk); });
    void *ctx = peer_openssl_sha512_ctx();
    TIME_ARM("sha512_compress", "openssl", { peer_openssl_sha512_ctx_step(ctx, blk); peer_openssl_sha512_ctx_step(ctx, blk); });
    free(ctx);
    uint64_t st[8];
    memcpy(st, SHA512_IV, 64);
    TIME_ARM("sha512_compress", "hacl", { peer_hacl_sha512(st, blk); peer_hacl_sha512(st, blk); });
  }

  /* SHA-512, four lanes per call (HACL* Vec256): cycles per block per lane. */
  {
    uint8_t blks[4][128];
    for (int j = 0; j < 4; j++) rnd_bytes(blks[j], 128);
    _Alignas(32) uint64_t st[32];
    for (int j = 0; j < 4; j++) x4_set(st, 8, j, SHA512_IV);
    TIME_ARM_N("sha512_compress_x4", "hacl_vec256", 4,
               { peer_hacl_sha512_x4(st, blks[0], blks[1], blks[2], blks[3]);
                 peer_hacl_sha512_x4(st, blks[0], blks[1], blks[2], blks[3]); });
  }

  /* BLAKE2b: every arm takes the 128-byte block; ours copies it into the kernel's
   * input array inside ours_blake2b_block, on every call. */
  {
    uint64_t A[24], B[24];
    memcpy(A, SHA512_IV, 64); memcpy(B, SHA512_IV, 64);
    TIME_ARM("blake2b_compress", "ours", { ours_blake2b_block(B, A, blk, 128, 0, 0); ours_blake2b_block(A, B, blk, 128, 0, 0); });
    _Alignas(32) uint64_t hash16[16];
    _Alignas(32) uint64_t wv[16];
    peer_hacl_blake2b_init_rows(hash16, SHA512_IV);
    TIME_ARM("blake2b_compress", "hacl", { peer_hacl_blake2b(hash16, wv, blk, 128, 0, 0); peer_hacl_blake2b(hash16, wv, blk, 128, 0, 0); });
    peer_hacl_blake2b_init_rows(hash16, SHA512_IV);
    TIME_ARM("blake2b_compress", "hacl_simd256", { peer_hacl_blake2b_simd256(hash16, wv, blk, 128, 0, 0); peer_hacl_blake2b_simd256(hash16, wv, blk, 128, 0, 0); });
  }

  /* Keccak-f[1600] */
  {
    uint64_t A[25], B[25];
    for (int i = 0; i < 25; i++) A[i] = rnd64();
    TIME_ARM("keccak_f1600", "ours", { ours_keccak_f1600(B, A); ours_keccak_f1600(A, B); });
    void *st = peer_xkcp_state();
    TIME_ARM("keccak_f1600", "xkcp", { peer_xkcp_state_step(st); peer_xkcp_state_step(st); });
    free(st);
    st = peer_xkcp_avx2_state();
    TIME_ARM("keccak_f1600", "xkcp_avx2", { peer_xkcp_avx2_state_step(st); peer_xkcp_avx2_state_step(st); });
    free(st);
    st = peer_xkcp_avx512_state();
    TIME_ARM("keccak_f1600", "xkcp_avx512", { peer_xkcp_avx512_state_step(st); peer_xkcp_avx512_state_step(st); });
    free(st);
    uint64_t s[25];
    for (int i = 0; i < 25; i++) s[i] = rnd64();
    TIME_ARM("keccak_f1600", "hacl", { peer_hacl_keccak_f1600(s); peer_hacl_keccak_f1600(s); });
  }

  /* Keccak-f[1600], four states per call (HACL* Simd256, absorb of a zero block
   * included): cycles per state. */
  {
    _Alignas(32) uint64_t s4[100];
    for (int i = 0; i < 100; i++) s4[i] = rnd64();
    TIME_ARM_N("keccak_f1600_x4", "hacl_simd256_absorb", 4,
               { peer_hacl_keccak_x4_absorb0(s4); peer_hacl_keccak_x4_absorb0(s4); });
  }
}

/* Compiler and flags, set by the Makefile. */
#ifndef HARNESS_CC
#define HARNESS_CC "unknown"
#endif
#ifndef HARNESS_CFLAGS
#define HARNESS_CFLAGS "unknown"
#endif
#ifndef HARNESS_SIMDFLAGS
#define HARNESS_SIMDFLAGS "unknown"
#endif

static void print_build_header(void) {
  printf("# compiler: %s\n", HARNESS_CC);
  printf("# C peers, adapters, block wrappers, harness: %s\n", HARNESS_CFLAGS);
  printf("# HACL* Simd256/Vec256 peers: %s\n", HARNESS_SIMDFLAGS);
  printf("# XKCP AVX2/AVX-512 peers: assembly (.s), assembled by the compiler above\n");
  printf("# OpenSSL peer: system libcrypto, prebuilt (%s)\n", peer_openssl_version());
  printf("# ours: gen/*.o as emitted, behind the register-saving trampoline of tramp.c\n");
}

/* Every TIME_ARM body makes two calls; TIME_ARM divides by 2 * inner. */
int main(int argc, char **argv) {
  if (argc >= 2 && strcmp(argv[1], "conform") == 0) {
    long nrand = argc >= 3 ? atol(argv[2]) : 10000;
    print_build_header();
    vectors();
    random_batch(nrand);
    printf("%s: %d mismatch(es)\n", failures ? "FAIL" : "PASS", failures);
    return failures ? 1 : 0;
  }
  if (argc >= 2 && strcmp(argv[1], "bench") == 0) {
    Cfg cfg = {501, 500};
    int cpu = -1, run = 0;
    const char *label = "unlabelled";
    for (int i = 2; i + 1 < argc; i += 2) {
      if (!strcmp(argv[i], "--cpu")) cpu = atoi(argv[i + 1]);
      else if (!strcmp(argv[i], "--samples")) cfg.samples = atol(argv[i + 1]);
      else if (!strcmp(argv[i], "--inner")) cfg.inner = atol(argv[i + 1]);
      else if (!strcmp(argv[i], "--run")) run = atoi(argv[i + 1]);
      else if (!strcmp(argv[i], "--label")) label = argv[i + 1];
      else { fprintf(stderr, "unknown argument %s\n", argv[i]); return 2; }
    }
    if (cpu >= 0 && pin_to_cpu(cpu) != 0) fprintf(stderr, "warning: could not pin to cpu %d\n", cpu);
    /* --inner counts calls; the loop runs inner / 2 steps of two calls. */
    cfg.inner = cfg.inner > 1 ? cfg.inner / 2 : 1;
    printf("# hash_linked_compare: TSC cycles per call (two chained calls per inner step);"
           " *_x4 rows: cycles per call / 4 (per block per lane, per state)\n");
    print_build_header();
    bench(cfg, label, run);
    return 0;
  }
  fprintf(stderr, "usage: %s conform [NRAND] | bench [--cpu C] [--samples S] [--inner I] "
                  "[--run R] [--label L]\n", argv[0]);
  return 2;
}
